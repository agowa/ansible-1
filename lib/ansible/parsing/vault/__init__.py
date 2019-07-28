# (c) 2014, James Tanner <tanner.jc@gmail.com>
# (c) 2016, Adrian Likins <alikins@redhat.com>
# (c) 2016 Toshio Kuratomi <tkuratomi@ansible.com>
#
# Ansible is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# Ansible is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with Ansible.  If not, see <http://www.gnu.org/licenses/>.

# Make coding more python3-ish
from __future__ import (absolute_import, division, print_function)
__metaclass__ = type

import os
import random
import shlex
import shutil
import subprocess
import sys
import tempfile
import warnings
from abc import ABC, abstractmethod
from binascii import hexlify
from binascii import unhexlify
from binascii import Error as BinasciiError

HAS_CRYPTOGRAPHY = False
CRYPTOGRAPHY_BACKEND = None
try:
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", DeprecationWarning)
        from cryptography.exceptions import InvalidSignature
    from cryptography.hazmat.backends import default_backend
    from cryptography.hazmat.primitives import hashes, padding
    from cryptography.hazmat.primitives.hmac import HMAC
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    from cryptography.hazmat.primitives.ciphers import (
        Cipher as C_Cipher, algorithms, modes
    )
    CRYPTOGRAPHY_BACKEND = default_backend()
    HAS_CRYPTOGRAPHY = True
except ImportError:
    pass

from ansible.errors import AnsibleError, AnsibleAssertionError
from ansible import constants as C
from ansible.module_utils.six import PY3, binary_type
# Note: on py2, this zip is izip not the list based zip() builtin
from ansible.module_utils.six.moves import zip
from ansible.module_utils._text import to_bytes, to_text, to_native
from ansible.utils.display import Display
from ansible.utils.path import makedirs_safe

display = Display()


b_HEADER = b'$ANSIBLE_VAULT'
CIPHER_WHITELIST = frozenset((
    (u'AES256', u'CTR'),
))
KDF_WHITELIST = frozenset((
    u'PBKDF2',
))
CIPHER_WRITE_WHITELIST = frozenset((
    (u'AES256', u'CTR'),
))
KDF_WRITE_WHITELIST = frozenset((
    u'PBKDF2',
))
# See also CIPHER_MAPPING at the bottom of the file which maps cipher strings
# (used in VaultFile header) to a cipher class

NEED_CRYPTO_LIBRARY = ("ansible-vault requires the cryptography library " +
                        "in order to function.")


class AnsibleVaultError(AnsibleError):
    pass


class AnsibleVaultPasswordError(AnsibleVaultError):
    pass


class AnsibleVaultFormatError(AnsibleError):
    pass

# TODO: Move these functions into the correct classes
# many of these are dependent on either the algorithm
# or the secret provider.

def is_encrypted(data):
    """ Test if this is vault encrypted data blob

    :arg data: a byte or text string to test whether it is recognized as vault
        encrypted data
    :returns: True if it is recognized.  Otherwise, False.
    """
    try:
        # Make sure we have a byte string and that it only contains ascii
        # bytes.
        b_data = to_bytes(to_text(data, encoding='ascii', errors='strict', nonstring='strict'), encoding='ascii', errors='strict')
    except (UnicodeError, TypeError):
        # The vault format is pure ascii so if we failed to encode to bytes
        # via ascii we know that this is not vault data.
        # Similarly, if it's not a string, it's not vault data
        return False

    # TODO: Should we also try to parse the envelope data here?
    if b_data.startswith(b_HEADER):

        return True
    return False


def is_encrypted_file(file_obj, start_pos=0, count=-1):
    """Test if the contents of a file obj are a vault encrypted data blob.

    :arg file_obj: A file object that will be read from.
    :kwarg start_pos: A byte offset in the file to start reading the header
        from.  Defaults to 0, the beginning of the file.
    :kwarg count: Read up to this number of bytes from the file to determine
        if it looks like encrypted vault data.  The default is -1, read to the
        end of file.
    :returns: True if the file looks like a vault file. Otherwise, False.
    """
    # read the header and reset the file stream to where it started
    current_position = file_obj.tell()
    try:
        file_obj.seek(start_pos)
        return is_encrypted(file_obj.read(count))

    finally:
        file_obj.seek(current_position)


def _parse_vaulttext_envelope(b_vaulttext_envelope, default_vault_id=None):

    b_tmpdata = b_vaulttext_envelope.splitlines()
    b_tmpheader = b_tmpdata[0].strip().split(b';')

    # 1.1
    b_version = b_tmpheader[1].strip()
    cipher_name = to_text(b_tmpheader[2].strip())
    # 1.2
    vault_id = default_vault_id
    if b_version >= b'1.2':
        if len(b_tmpheader) >= 4:
            vault_id = b_tmpheader[3].strip()
    # 1.3
    cipher_mode = u'CTR'
    kdf_name = u'PBKDF2'
    if b_version >= b'1.3':
        if len(b_tmpheader) >= 6:
            cipher_mode = to_text(b_tmpheader[4].strip())
            kdf_name = to_text(b_tmpheader[5].strip())

    b_ciphertext = b''.join(b_tmpdata[1:])

    return b_ciphertext, b_version, cipher_name, vault_id, cipher_mode, kdf_name


def parse_vaulttext_envelope(b_vaulttext_envelope, default_vault_id=None, filename=None):
    """Parse the vaulttext envelope

    When data is saved, it has a header prepended and is formatted into 80
    character lines.  This method extracts the information from the header
    and then removes the header and the inserted newlines.  The string returned
    is suitable for processing by the Cipher classes.

    :arg b_vaulttext: byte str containing the data from a save file
    :kwarg default_vault_id: The vault_id name to use if the vaulttext does not provide one.
    :kwarg filename: The filename that the data came from.  This is only
        used to make better error messages in case the data cannot be
        decrypted. This is optional.
    :returns: A tuple of byte str of the vaulttext suitable to pass to parse_vaultext,
        a byte str of the vault format version,
        the name of the cipher used, the vault_id, cipher mode and the kdf used.
    :raises: AnsibleVaultFormatError: if the vaulttext_envelope format is invalid
    """
    # used by decrypt
    default_vault_id = default_vault_id or C.DEFAULT_VAULT_IDENTITY

    try:
        return _parse_vaulttext_envelope(b_vaulttext_envelope, default_vault_id)
    except Exception as exc:
        msg = "Vault envelope format error"
        if filename:
            msg += ' in %s' % (filename)
        msg += ': %s' % exc
        raise AnsibleVaultFormatError(msg)

def _get_vault_header_parts_format_helper(cipher_name, version=None, vault_id=None, cipher_mode=None, kdf_name=None):
    """ Generate the most backwards compatible header format.

        :arg cipher_name: unicode cipher name (e.g. u'AES256')
        :arg version: unicode vault version (e.g '1.2').
            Optional, by default lowest possible version will be used.
        :arg vault_id: unicode vault identifier (e.g. u'default').
            If provided, the version will be bumped to 1.2.
        :arg cipher_mode: unicode cipher mode (e.g. u'CTR').
            If provided, the version will be bumped to 1.3.
        :arg kdf_name: unicode kdf name (e.g. u'PBKDF2').
            If provided, the version will be bumped to 1.3
        :returns: An ordered list with the bytestrings to write
            into the header.

        ╔════════════════╦═══════════════════════════════════════════════╦════════════╦════════════════════════════╗
        ║ Version        ║                      1.1                      ║     1.2    ║             1.3            ║
        ╠════════════════╬═══════════════════╦═══════════╦═══════════════╬════════════╬═══════════════╦════════════╣
        ║ Meaning        ║ b_HEADER          ║ b_version ║ b_cipher_name ║ b_vault_id ║ b_cipher_mode ║ b_kdf_name ║
        ╠════════════════╬═══════════════════╬═══════════╬═══════════════╬════════════╬═══════════════╬════════════╣
        ║ Default values ║ b'$ANSIBLE_VAULT' ║ b'1.1'    ║ b'AES256'     ║ b'default' ║ b'CTR'        ║ b'PBKDF2'  ║
        ╚════════════════╩═══════════════════╩═══════════╩═══════════════╩════════════╩═══════════════╩════════════╝
    """
    # Provide default value for lowest possible version
    # The default should be the behaviour of the previous
    # version before it was implemented
    version = version or '1.1'
    cipher_name = cipher_name or 'AES256'
    vault_id = vault_id or u'default'
    cipher_mode = cipher_mode.upper() or u'CTR'
    kdf_name = kdf_name.upper() or u'PBKDF2'

    # Bump version if newer parameters are necessary,
    # e.g. specified value is not backwards compatible
    if vault_id != u'default':
        # If vault_id is specified, use at least version 1.2.
        if version in ['1.1']:
            version = '1.2'
    if cipher_mode != u'CTR' or kdf_name != u'PBKDF2':
        # If cipher_mode or kdf_name is specified,
        # use at least version 1.3.
        if version in ['1.1', '1.2']:
            version = '1.3'

    # 1.1
    b_version = to_bytes(version, 'utf-8', errors='strict')
    b_cipher_name = to_bytes(cipher_name, 'utf-8', errors='strict')
    # 1.2
    b_vault_id = to_bytes(vault_id, 'utf-8', errors='strict')
    # 1.3
    b_cipher_mode = to_bytes(cipher_mode, 'utf-8', errors='strict')
    b_kdf_name = to_bytes(kdf_name, 'utf-8', errors='strict')

    header_parts = [b_HEADER,
                    b_version,
                    b_cipher_name]

    # Conditionally add header depending on requested/required header version
    if b_version >= b'1.2':
        header_parts.append(b_vault_id)
    if b_version >= b'1.3':
        header_parts.append(b_cipher_mode)
        header_parts.append(b_kdf_name)

    return header_parts


def format_vaulttext_envelope(b_ciphertext, cipher_name, version=None, vault_id=None,
                                cipher_mode=None, kdf_name=None):
    """ Add header and format to 80 columns

        :arg b_ciphertext: the encrypted and hexlified data as a byte string
        :arg cipher_name: unicode cipher name (e.g. u'AES256')
        :arg version: unicode vault version (e.g '1.2').
            Optional, by default lowest possible version will be used.
        :arg vault_id: unicode vault identifier (e.g. u'default').
            If provided, the version will be bumped to 1.2.
        :arg cipher_mode: unicode cipher mode (e.g. u'CTR').
            If provided, the version will be bumped to 1.3.
        :arg kdf_name: unicode kdf name (e.g. u'PBKDF2').
            If provided, the version will be bumped to 1.3
        :returns: a byte str that should be dumped into a file.  It's
            formatted to 80 char columns and has the header prepended
    """

    if not cipher_name:
        raise AnsibleError("the cipher must be set before adding a header")

    header_parts = _get_vault_header_parts_format_helper(
        cipher_name=cipher_name,
        version=version,
        vault_id=vault_id,
        cipher_mode=cipher_mode,
        kdf_name=kdf_name
    )


    header = b';'.join(header_parts)

    # TODO: Also wrap header when longer than 80 characters.
    b_vaulttext = [header]
    b_vaulttext += [b_ciphertext[i:i + 80] for i in range(0, len(b_ciphertext), 80)]
    b_vaulttext += [b'']
    b_vaulttext = b'\n'.join(b_vaulttext)

    return b_vaulttext


def _unhexlify(b_data):
    try:
        return unhexlify(b_data)
    except (BinasciiError, TypeError) as exc:
        raise AnsibleVaultFormatError('Vault format unhexlify error: %s' % exc)


def _parse_vaulttext(b_vaulttext):
    b_vaulttext = _unhexlify(b_vaulttext)
    b_salt, b_crypted_hmac, b_ciphertext = b_vaulttext.split(b"\n", 2)
    b_salt = _unhexlify(b_salt)
    b_ciphertext = _unhexlify(b_ciphertext)

    return b_ciphertext, b_salt, b_crypted_hmac


def parse_vaulttext(b_vaulttext):
    """Parse the vaulttext

    :arg b_vaulttext: byte str containing the vaulttext (ciphertext, salt, crypted_hmac)
    :returns: A tuple of byte str of the ciphertext suitable for passing to a
        Cipher class's decrypt() function, a byte str of the salt,
        and a byte str of the crypted_hmac
    :raises: AnsibleVaultFormatError: if the vaulttext format is invalid
    """
    # SPLIT SALT, DIGEST, AND DATA
    try:
        return _parse_vaulttext(b_vaulttext)
    except AnsibleVaultFormatError:
        raise
    except Exception as exc:
        msg = "Vault vaulttext format error: %s" % exc
        raise AnsibleVaultFormatError(msg)


def verify_secret_is_not_empty(secret, msg='Invalid vault password was provided'):
    '''Check the secret against minimal requirements.

    Raises: AnsibleVaultPasswordError if the password does not meet requirements.

    Currently, only requirement is that the password is not None or an empty string.
    '''
    if not secret:
        raise AnsibleVaultPasswordError(msg)


def script_is_client(filename):
    '''Determine if a vault secret script is a client script that can be given --vault-id args'''

    # if password script is 'something-client' or 'something-client.[sh|py|rb|etc]'
    # script_name can still have '.' or could be entire filename if there is no ext
    script_name, dummy = os.path.splitext(filename)

    # TODO: for now, this is entirely based on filename
    if script_name.endswith('-client'):
        return True

    return False


def get_file_vault_secret(filename=None, vault_id=None, encoding=None, loader=None):
    this_path = os.path.realpath(os.path.expanduser(filename))

    if not os.path.exists(this_path):
        raise AnsibleError("The vault password file %s was not found" % this_path)

    if loader.is_executable(this_path):
        if script_is_client(filename):
            display.vvvv(u'The vault password file %s is a client script.' % to_text(filename))
            # TODO: pass vault_id_name to script via cli
            return ClientScriptVaultSecret(filename=this_path, vault_id=vault_id,
                                           encoding=encoding, loader=loader)
        # just a plain vault password script. No args, returns a byte array
        return ScriptVaultSecret(filename=this_path, encoding=encoding, loader=loader)

    return PlainTextFileVaultSecret(filename=this_path, encoding=encoding, loader=loader)


def match_secrets(secrets, target_vault_ids):
    '''Find all VaultSecret objects that are mapped to any of the target_vault_ids in secrets'''
    if not secrets:
        return []

    matches = [(vault_id, secret) for vault_id, secret in secrets if vault_id in target_vault_ids]
    return matches


def match_best_secret(secrets, target_vault_ids):
    '''Find the best secret from secrets that matches target_vault_ids

    Since secrets should be ordered so the early secrets are 'better' than later ones, this
    just finds all the matches, then returns the first secret'''
    matches = match_secrets(secrets, target_vault_ids)
    if matches:
        return matches[0]
    # raise exception?
    return None


def match_encrypt_vault_id_secret(secrets, encrypt_vault_id=None):
    # See if the --encrypt-vault-id matches a vault-id
    display.vvvv(u'encrypt_vault_id=%s' % to_text(encrypt_vault_id))

    if encrypt_vault_id is None:
        raise AnsibleError('match_encrypt_vault_id_secret requires a non None encrypt_vault_id')

    encrypt_vault_id_matchers = [encrypt_vault_id]
    encrypt_secret = match_best_secret(secrets, encrypt_vault_id_matchers)

    # return the best match for --encrypt-vault-id
    if encrypt_secret:
        return encrypt_secret

    # If we specified a encrypt_vault_id and we couldn't find it, dont
    # fallback to using the first/best secret
    raise AnsibleVaultError('Did not find a match for --encrypt-vault-id=%s in the known vault-ids %s' % (encrypt_vault_id,
                                                                                                          [_v for _v, _vs in secrets]))


def match_encrypt_secret(secrets, encrypt_vault_id=None):
    '''Find the best/first/only secret in secrets to use for encrypting'''

    display.vvvv(u'encrypt_vault_id=%s' % to_text(encrypt_vault_id))
    # See if the --encrypt-vault-id matches a vault-id
    if encrypt_vault_id:
        return match_encrypt_vault_id_secret(secrets,
                                             encrypt_vault_id=encrypt_vault_id)

    # Find the best/first secret from secrets since we didnt specify otherwise
    # ie, consider all of the available secrets as matches
    _vault_id_matchers = [_vault_id for _vault_id, dummy in secrets]
    best_secret = match_best_secret(secrets, _vault_id_matchers)

    # can be empty list sans any tuple
    return best_secret

@staticmethod
def _is_equal(b_a, b_b):
    """
    Comparing 2 byte arrrays in constant time
    to avoid timing attacks.

    It would be nice if there was a library for this but
    hey.
    """
    if not (isinstance(b_a, binary_type) and isinstance(b_b, binary_type)):
        raise TypeError('_is_equal can only be used to compare two byte strings')

    # http://codahale.com/a-lesson-in-timing-attacks/
    if len(b_a) != len(b_b):
        return False

    result = 0
    for b_x, b_y in zip(b_a, b_b):
        if PY3:
            result |= b_x ^ b_y
        else:
            result |= ord(b_x) ^ ord(b_y)
    return result == 0


class VaultEditor:

    def __init__(self, vault=None):
        # TODO: it may be more useful to just make VaultSecrets and index of VaultLib objects...
        self.vault = vault or VaultLib()

    # TODO: mv shred file stuff to it's own class
    def _shred_file_custom(self, tmp_path):
        """"Destroy a file, when shred (core-utils) is not available

        Unix `shred' destroys files "so that they can be recovered only with great difficulty with
        specialised hardware, if at all". It is based on the method from the paper
        "Secure Deletion of Data from Magnetic and Solid-State Memory",
        Proceedings of the Sixth USENIX Security Symposium (San Jose, California, July 22-25, 1996).

        We do not go to that length to re-implement shred in Python; instead, overwriting with a block
        of random data should suffice.

        See https://github.com/ansible/ansible/pull/13700 .
        """

        file_len = os.path.getsize(tmp_path)

        if file_len > 0:  # avoid work when file was empty
            max_chunk_len = min(1024 * 1024 * 2, file_len)

            passes = 3
            with open(tmp_path, "wb") as fh:
                for _ in range(passes):
                    fh.seek(0, 0)
                    # get a random chunk of data, each pass with other length
                    chunk_len = random.randint(max_chunk_len // 2, max_chunk_len)
                    data = os.urandom(chunk_len)

                    for _ in range(0, file_len // chunk_len):
                        fh.write(data)
                    fh.write(data[:file_len % chunk_len])

                    # FIXME remove this assert once we have unittests to check its accuracy
                    if fh.tell() != file_len:
                        raise AnsibleAssertionError()

                    os.fsync(fh)

    def _shred_file(self, tmp_path):
        """Securely destroy a decrypted file

        Note standard limitations of GNU shred apply (For flash, overwriting would have no effect
        due to wear leveling; for other storage systems, the async kernel->filesystem->disk calls never
        guarantee data hits the disk; etc). Furthermore, if your tmp dirs is on tmpfs (ramdisks),
        it is a non-issue.

        Nevertheless, some form of overwriting the data (instead of just removing the fs index entry) is
        a good idea. If shred is not available (e.g. on windows, or no core-utils installed), fall back on
        a custom shredding method.
        """

        if not os.path.isfile(tmp_path):
            # file is already gone
            return

        try:
            r = subprocess.call(['shred', tmp_path])
        except (OSError, ValueError):
            # shred is not available on this system, or some other error occurred.
            # ValueError caught because macOS El Capitan is raising an
            # exception big enough to hit a limit in python2-2.7.11 and below.
            # Symptom is ValueError: insecure pickle when shred is not
            # installed there.
            r = 1

        if r != 0:
            # we could not successfully execute unix shred; therefore, do custom shred.
            self._shred_file_custom(tmp_path)

        os.remove(tmp_path)

    def _edit_file_helper(self, filename, secret,
                          existing_data=None, force_save=False, vault_id=None):

        # Create a tempfile
        root, ext = os.path.splitext(os.path.realpath(filename))
        fd, tmp_path = tempfile.mkstemp(suffix=ext)
        os.close(fd)

        cmd = self._editor_shell_command(tmp_path)
        try:
            if existing_data:
                self.write_data(existing_data, tmp_path, shred=False)

            # drop the user into an editor on the tmp file
            subprocess.call(cmd)
        except Exception as e:
            # whatever happens, destroy the decrypted file
            self._shred_file(tmp_path)
            raise AnsibleError('Unable to execute the command "%s": %s' % (' '.join(cmd), to_native(e)))

        b_tmpdata = self.read_data(tmp_path)

        # Do nothing if the content has not changed
        # except shreading our temporary file
        if existing_data == b_tmpdata and not force_save:
            self._shred_file(tmp_path)
            return

        # encrypt new data and write out to tmp
        # An existing vaultfile will always be UTF-8,
        # so decode to unicode here
        b_ciphertext = self.vault.encrypt(b_tmpdata, secret, vault_id=vault_id)
        self.write_data(b_ciphertext, tmp_path)

        # shuffle tmp file into place
        self.shuffle_files(tmp_path, filename)
        display.vvvvv(u'Saved edited file "%s" encrypted using %s and  vault id "%s"' % (to_text(filename), to_text(secret), to_text(vault_id)))

    def _real_path(self, filename):
        # '-' is special to VaultEditor, dont expand it.
        if filename == '-':
            return filename

        real_path = os.path.realpath(filename)
        return real_path

    def encrypt_bytes(self, b_plaintext, secret, vault_id=None):

        b_ciphertext = self.vault.encrypt(b_plaintext, secret, vault_id=vault_id)

        return b_ciphertext

    def encrypt_file(self, filename, secret, vault_id=None, output_file=None):

        # A file to be encrypted into a vaultfile could be any encoding
        # so treat the contents as a byte string.

        # follow the symlink
        filename = self._real_path(filename)

        b_plaintext = self.read_data(filename)
        b_ciphertext = self.vault.encrypt(b_plaintext, secret, vault_id=vault_id)
        self.write_data(b_ciphertext, output_file or filename)

    def decrypt_file(self, filename, output_file=None):

        # follow the symlink
        filename = self._real_path(filename)

        ciphertext = self.read_data(filename)

        try:
            plaintext = self.vault.decrypt(ciphertext, filename=filename)
        except AnsibleError as e:
            raise AnsibleError("%s for %s" % (to_native(e), to_native(filename)))
        self.write_data(plaintext, output_file or filename, shred=False)

    def create_file(self, filename, secret, vault_id=None):
        """ create a new encrypted file """

        dirname = os.path.dirname(filename)
        if dirname and not os.path.exists(dirname):
            display.warning(u"%s does not exist, creating..." % to_text(dirname))
            makedirs_safe(dirname)

        # FIXME: If we can raise an error here, we can probably just make it
        # behave like edit instead.
        if os.path.isfile(filename):
            raise AnsibleError("%s exists, please use 'edit' instead" % filename)

        self._edit_file_helper(filename, secret, vault_id=vault_id)

    def edit_file(self, filename):
        vault_id_used = None
        vault_secret_used = None
        # follow the symlink
        filename = self._real_path(filename)

        b_vaulttext = self.read_data(filename)

        # vault or yaml files are always utf8
        vaulttext = to_text(b_vaulttext)

        try:
            # vaulttext gets converted back to bytes, but alas
            # TODO: return the vault_id that worked?
            plaintext, vault_id_used, vault_secret_used = self.vault.decrypt_and_get_vault_id(vaulttext)
        except AnsibleError as e:
            raise AnsibleError("%s for %s" % (to_native(e), to_native(filename)))

        # Figure out the vault id from the file, to select the right secret to re-encrypt it
        # (duplicates parts of decrypt, but alas...)
        # TODO: Don't duplicate code here, instead reference decrypt
        dummy, dummy, cipher_name, vault_id, cipher_mode, kdf_name = \
            parse_vaulttext_envelope(
                b_vaulttext,
                filename=filename
            )

        # vault id here may not be the vault id actually used for decrypting
        # as when the edited file has no vault-id but is decrypted by non-default id in secrets
        # (vault_id=default, while a different vault-id decrypted)

        # Keep the same vault-id (and version) as in the header
        # TODO: Make sure the same cipher_name, cipher_mode and kdf_name are used
        if cipher_name not in CIPHER_WRITE_WHITELIST:
            # we want to get rid of files encrypted with the AES cipher
            self._edit_file_helper(filename, vault_secret_used, existing_data=plaintext,
                                   force_save=True, vault_id=vault_id)
        else:
            self._edit_file_helper(filename, vault_secret_used, existing_data=plaintext,
                                   force_save=False, vault_id=vault_id)

    def plaintext(self, filename):

        b_vaulttext = self.read_data(filename)
        vaulttext = to_text(b_vaulttext)

        try:
            plaintext = self.vault.decrypt(vaulttext, filename=filename)
            return plaintext
        except AnsibleError as e:
            raise AnsibleVaultError("%s for %s" % (to_native(e), to_native(filename)))

    # FIXME/TODO: make this use VaultSecret
    def rekey_file(self, filename, new_vault_secret, new_vault_id=None):

        # follow the symlink
        filename = self._real_path(filename)

        prev = os.stat(filename)
        b_vaulttext = self.read_data(filename)
        vaulttext = to_text(b_vaulttext)

        display.vvvvv(u'Rekeying file "%s" to with new vault-id "%s" and vault secret %s' %
                      (to_text(filename), to_text(new_vault_id), to_text(new_vault_secret)))
        try:
            plaintext, vault_id_used, _dummy = self.vault.decrypt_and_get_vault_id(vaulttext)
        except AnsibleError as e:
            raise AnsibleError("%s for %s" % (to_native(e), to_native(filename)))

        # This is more or less an assert, see #18247
        if new_vault_secret is None:
            raise AnsibleError('The value for the new_password to rekey %s with is not valid' % filename)

        # FIXME: VaultContext...?  could rekey to a different vault_id in the same VaultSecrets

        # Need a new VaultLib because the new vault data can be a different
        # vault lib format or cipher (for ex, when we migrate 1.0 style vault data to
        # 1.1 style data we change the version and the cipher). This is where a VaultContext might help

        # the new vault will only be used for encrypting, so it doesn't need the vault secrets
        # (we will pass one in directly to encrypt)
        new_vault = VaultLib(secrets={})
        b_new_vaulttext = new_vault.encrypt(plaintext, new_vault_secret, vault_id=new_vault_id)

        self.write_data(b_new_vaulttext, filename)

        # preserve permissions
        os.chmod(filename, prev.st_mode)
        os.chown(filename, prev.st_uid, prev.st_gid)

        display.vvvvv(u'Rekeyed file "%s" (decrypted with vault id "%s") was encrypted with new vault-id "%s" and vault secret %s' %
                      (to_text(filename), to_text(vault_id_used), to_text(new_vault_id), to_text(new_vault_secret)))

    def read_data(self, filename):

        try:
            if filename == '-':
                data = sys.stdin.read()
            else:
                with open(filename, "rb") as fh:
                    data = fh.read()
        except Exception as e:
            msg = to_native(e)
            if not msg:
                msg = repr(e)
            raise AnsibleError('Unable to read source file (%s): %s' % (to_native(filename), msg))

        return data

    # TODO: add docstrings for arg types since this code is picky about that
    def write_data(self, data, filename, shred=True):
        """Write the data bytes to given path

        This is used to write a byte string to a file or stdout. It is used for
        writing the results of vault encryption or decryption. It is used for
        saving the ciphertext after encryption and it is also used for saving the
        plaintext after decrypting a vault. The type of the 'data' arg should be bytes,
        since in the plaintext case, the original contents can be of any text encoding
        or arbitrary binary data.

        When used to write the result of vault encryption, the val of the 'data' arg
        should be a utf-8 encoded byte string and not a text typ and not a text type..

        When used to write the result of vault decryption, the val of the 'data' arg
        should be a byte string and not a text type.

        :arg data: the byte string (bytes) data
        :arg filename: filename to save 'data' to.
        :arg shred: if shred==True, make sure that the original data is first shredded so that is cannot be recovered.
        :returns: None
        """
        # FIXME: do we need this now? data_bytes should always be a utf-8 byte string
        b_file_data = to_bytes(data, errors='strict')

        # get a ref to either sys.stdout.buffer for py3 or plain old sys.stdout for py2
        # We need sys.stdout.buffer on py3 so we can write bytes to it since the plaintext
        # of the vaulted object could be anything/binary/etc
        output = getattr(sys.stdout, 'buffer', sys.stdout)

        if filename == '-':
            output.write(b_file_data)
        else:
            if os.path.isfile(filename):
                if shred:
                    self._shred_file(filename)
                else:
                    os.remove(filename)
            with open(filename, "wb") as fh:
                fh.write(b_file_data)

    def shuffle_files(self, src, dest):
        prev = None
        # overwrite dest with src
        if os.path.isfile(dest):
            prev = os.stat(dest)
            # old file 'dest' was encrypted, no need to _shred_file
            os.remove(dest)
        shutil.move(src, dest)

        # reset permissions if needed
        if prev is not None:
            # TODO: selinux, ACLs, xattr?
            os.chmod(dest, prev.st_mode)
            os.chown(dest, prev.st_uid, prev.st_gid)

    def _editor_shell_command(self, filename):
        env_editor = os.environ.get('EDITOR', 'vi')
        editor = shlex.split(env_editor)
        editor.append(filename)

        return editor


class VaultLib:
    # TODO: Also allow cipher_name, cipher_mode and kdf_name to be passed from cli
    def __init__(self, secrets=None):
        self.secrets = secrets or []
        self.cipher_name = None
        self.cipher_mode = None
        self.kdf_name = None

    def encrypt(self, plaintext, secret=None, vault_id=None):
        """Vault encrypt a piece of data.

        :arg plaintext: a text or byte string to encrypt.
        :returns: a utf-8 encoded byte str of encrypted data.  The string
            contains a header identifying this as vault encrypted data and
            formatted to newline terminated lines of 80 characters.  This is
            suitable for dumping as is to a vault file.

        If the string passed in is a text string, it will be encoded to UTF-8
        before encryption.
        """

        if secret is None:
            if self.secrets:
                dummy, secret = match_encrypt_secret(self.secrets)
            else:
                raise AnsibleVaultError("A vault password must be specified to encrypt data")

        b_plaintext = to_bytes(plaintext, errors='surrogate_or_strict')

        if is_encrypted(b_plaintext):
            raise AnsibleError("input is already encrypted")

        # Backwards compatible e.g. old defaults:
        if not self.cipher_name or (self.cipher_name not in [i[0] for i in CIPHER_WRITE_WHITELIST]):
            display.v(u'Unknown cipher "{0}" assume AES256'.format(to_text(self.cipher_name)))
            self.cipher_name = u"AES256"
        if not self.cipher_mode or (
            self.cipher_mode not in [i[1] for i in CIPHER_WRITE_WHITELIST if i[0]==self.cipher_name]
        ):
            if self.cipher_name == u'AES256':
                display.v(u'Unknown cipher mode "{0}" assume CTR mode'.format(to_text(self.cipher_mode)))
                self.cipher_mode = u'CTR'
            else:
                raise AnsibleVaultError(u'Unknown cipher mode "{0}" for "{1}"'.format(
                                        to_text(self.cipher_mode), to_text(self.cipher_name)))
        if not self.kdf_name or self.kdf_name not in KDF_WRITE_WHITELIST:
            if self.cipher_name == u'AES256' and self.cipher_mode == u'CTR':
                display.v(u'Unknown key derivation function "{0}" assume PBKDF2'.format(
                            to_text(self.cipher_mode)))
                self.kdf_name = u'PBKDF2'
            else:
                raise AnsibleVaultError(u'Unknown key derivation function "{0}"'.format(to_text(
                                        self.kdf_name)))

        try:
            this_cipher = CIPHER_MAPPING[(self.cipher_name, self.cipher_mode)]()
        except KeyError:
            raise AnsibleError(u"{0}-{1} cipher could not be found".format(self.cipher_name, self.cipher_mode))

        # encrypt data
        if vault_id:
            display.vvvvv(u'Encrypting with vault_id "%s" and vault secret %s' % (to_text(vault_id), to_text(secret)))
        else:
            display.vvvvv(u'Encrypting without a vault_id using vault secret %s' % to_text(secret))

        b_ciphertext = this_cipher.encrypt(b_plaintext, secret, self.kdf_name)

        # format the data for output to the file
        b_vaulttext = format_vaulttext_envelope(
            b_ciphertext,
            self.cipher_name,
            vault_id=vault_id,
            cipher_mode=self.cipher_mode,
            kdf_name=self.kdf_name
        )
        return b_vaulttext

    def decrypt(self, vaulttext, filename=None):
        '''Decrypt a piece of vault encrypted data.

        :arg vaulttext: a string to decrypt.  Since vault encrypted data is an
            ascii text format this can be either a byte str or unicode string.
        :kwarg filename: a filename that the data came from.  This is only
            used to make better error messages in case the data cannot be
            decrypted.
        :returns: a byte string containing the decrypted data and the vault-id that was used

        '''
        plaintext, vault_id, vault_secret = self.decrypt_and_get_vault_id(vaulttext, filename=filename)
        return plaintext

    def decrypt_and_get_vault_id(self, vaulttext, filename=None):
        """Decrypt a piece of vault encrypted data.

        :arg vaulttext: a string to decrypt.  Since vault encrypted data is an
            ascii text format this can be either a byte str or unicode string.
        :kwarg filename: a filename that the data came from.  This is only
            used to make better error messages in case the data cannot be
            decrypted.
        :returns: a byte string containing the decrypted data and the vault-id vault-secret that was used

        """
        b_vaulttext = to_bytes(vaulttext, errors='strict', encoding='utf-8')

        if self.secrets is None:
            raise AnsibleVaultError("A vault password must be specified to decrypt data")

        if not is_encrypted(b_vaulttext):
            msg = "input is not vault encrypted data"
            if filename:
                msg += "%s is not a vault encrypted file" % to_native(filename)
            raise AnsibleError(msg)

        (
            b_vaulttext, dummy, cipher_name,
            vault_id, cipher_mode, kdf_name
        ) = parse_vaulttext_envelope(
            b_vaulttext,
            filename=filename
        )

        # create the cipher object, note that the cipher used for decrypt can
        # be different than the cipher used for encrypt
        if cipher_name in CIPHER_WHITELIST:
            this_cipher = CIPHER_MAPPING[cipher_name]()
        else:
            raise AnsibleVaultError("{0} cipher could not be found".format(cipher_name))
        if cipher_mode in this_cipher.MODE_WHITELIST:
            this_cipher_mode = this_cipher.MODE_MAPPING[cipher_mode]
        else:
            raise AnsibleVaultError("{0} cipher mode could not be found".format(cipher_mode))
        if kdf_name in KDF_WHITELIST:
            this_kdf = KDF_MAPPING[kdf_name]
        else:
            raise AnsibleVaultError("{0} kdf could not be found".format(kdf_name))

        b_plaintext = None

        if not self.secrets:
            raise AnsibleError('Attempting to decrypt but no vault secrets found')

        # WARNING: Currently, the vault id is not required to match the vault id in the vault blob to
        #          decrypt a vault properly. The vault id in the vault blob is not part of the encrypted
        #          or signed vault payload. There is no cryptographic checking/verification/validation of the
        #          vault blobs vault id. It can be tampered with and changed. The vault id is just a nick
        #          name to use to pick the best secret and provide some ux/ui info.

        # iterate over all the applicable secrets (all of them by default) until one works...
        # if we specify a vault_id, only the corresponding vault secret is checked and
        # we check it first.

        vault_id_matchers = []
        vault_id_used = None
        vault_secret_used = None

        if vault_id:
            display.vvvvv(u'Found a vault_id (%s) in the vaulttext' % to_text(vault_id))
            vault_id_matchers.append(vault_id)
            _matches = match_secrets(self.secrets, vault_id_matchers)
            if _matches:
                display.vvvvv(u'We have a secret associated with vault id (%s), will try to use to decrypt %s' % (to_text(vault_id), to_text(filename)))
            else:
                display.vvvvv(u'Found a vault_id (%s) in the vault text, but we do not have a associated secret (--vault-id)' % to_text(vault_id))

        # Not adding the other secrets to vault_secret_ids enforces a match between the vault_id from the vault_text and
        # the known vault secrets.
        if not C.DEFAULT_VAULT_ID_MATCH:
            # Add all of the known vault_ids as candidates for decrypting a vault.
            vault_id_matchers.extend([_vault_id for _vault_id, _dummy in self.secrets if _vault_id != vault_id])

        matched_secrets = match_secrets(self.secrets, vault_id_matchers)

        # for vault_secret_id in vault_secret_ids:
        for vault_secret_id, vault_secret in matched_secrets:
            display.vvvvv(u'Trying to use vault secret=(%s) id=%s to decrypt %s' % (to_text(vault_secret), to_text(vault_secret_id), to_text(filename)))

            try:
                # secret = self.secrets[vault_secret_id]
                display.vvvv(u'Trying secret %s for vault_id=%s' % (to_text(vault_secret), to_text(vault_secret_id)))
                b_plaintext = this_cipher.decrypt(b_vaulttext, vault_secret)
                if b_plaintext is not None:
                    vault_id_used = vault_secret_id
                    vault_secret_used = vault_secret
                    file_slug = ''
                    if filename:
                        file_slug = ' of "%s"' % filename
                    display.vvvvv(
                        u'Decrypt%s successful with secret=%s and vault_id=%s' % (to_text(file_slug), to_text(vault_secret), to_text(vault_secret_id))
                    )
                    break
            except AnsibleVaultFormatError as exc:
                msg = u"There was a vault format error"
                if filename:
                    msg += u' in %s' % (to_text(filename))
                msg += u': %s' % exc
                display.warning(msg)
                raise
            except AnsibleVaultError as e:
                display.vvvv(u'Tried to use the vault secret (%s) to decrypt (%s) but it failed. Error: %s' %
                             (to_text(vault_secret_id), to_text(filename), e))
                continue
        else:
            msg = "Decryption failed (no vault secrets were found that could decrypt)"
            if filename:
                msg += " on %s" % to_native(filename)
            raise AnsibleVaultError(msg)

        if b_plaintext is None:
            msg = "Decryption failed"
            if filename:
                msg += " on %s" % to_native(filename)
            raise AnsibleVaultError(msg)

        return b_plaintext, vault_id_used, vault_secret_used


########################################
#              Interfaces              #
########################################

class VaultSecret(ABC):
    '''
    Opaque/abstract objects for a single vault secret. ie, a password or a key.
    This is the interface for all secret retrievers.

    :param _bytes: Directly provide a secret bytestring, used for testing only.
    :param engine: function to get bytestring from.
    '''

    def __init__(self, _bytes=None):
        super(VaultSecret, self).__init__()
        self._bytes = _bytes

    @property
    def bytes(self):
        '''The secret as a bytestring.

        Sub classes that store text types will need to override to encode the text to bytes.
        '''
        assert self._bytes is not None
        return self._bytes

    def load(self):
        '''
        Populate self._bytes with the secret bytestring.
        E.g. Ask for password.
        '''
        self._bytes = self._engine()
        assert self._bytes is not None

    @abstractmethod
    def _engine(self):
        pass


class FileVaultSecret(VaultSecret):
    '''
    Load Vault Secret using a file (abstract class)
    '''

    def __init__(self, filename, encoding=None, loader=None):
        super(FileVaultSecret, self).__init__()
        self.encoding = encoding or 'utf8'
        self.filename = filename
        self.loader = loader
        self._text = None

    @property
    def bytes(self):
        if self._text and not self._bytes:
            self._bytes == self._text.encode(self.encoding)
        return super(FileVaultSecret, self).bytes()

    def load(self):
        self._bytes = self._engine(self.filename)
        assert self._bytes is not None

    @abstractmethod
    def _engine(self, filename):
        pass


class VaultKDF(ABC):
    @abstractmethod
    def run(self, b_password, b_salt, key_length, iv_length):
        pass


class VaultMAC(ABC):
    def __init__(self):
        super(VaultMAC, self).__init__()
        self.algorithm = None

    @abstractmethod
    def run(self, b_ciphertext, b_key):
        pass

    @abstractmethod
    def is_valid(self, b_ciphertext, b_key, b_valid_hmac):
        pass


# TODO: Move everything underneath here into separate files.

########################################
#           Secret Providers           #
########################################

class PromptVaultSecret(VaultSecret):
    '''
    Prompt for Vault Secret through stdin/terminal
    '''
    default_prompt_formats = ["Vault password (%s): "]

    def __init__(self, _bytes=None , vault_id=None, prompt_formats=None):
        super(PromptVaultSecret, self).__init__(_bytes=_bytes)
        assert 0 <= len(prompt_formats) <= 2
        self.prompt_formats = prompt_formats or self.default_prompt_formats
        self.vault_id = vault_id

    def _engine(self):
        b_vault_passwords = []
        # TODO: Validate assumption:
        # A list with either one or two arguments,
        # either one to ask for an unlock password
        # or two to ask for a new one for changing/setting
        # the password initially.

        # FIXME: This does not look right.
        # It looks like this should enable something like keyslots in luks,
        # but they only ever check the password against the first entry.
        # Also the check function throws an exception if the first
        # element of the for loop is not already a match.
        for prompt_format in self.prompt_formats:
            prompt = prompt_format % {'vault_id': self.vault_id}
            try:
                vault_pass = display.prompt(prompt, private=True)
            except EOFError:
                raise AnsibleVaultError('EOFError (ctrl-d) on prompt for (%s)' % self.vault_id)

            verify_secret_is_not_empty(vault_pass)

            b_vault_pass = to_bytes(vault_pass, errors='strict', nonstring='simplerepr').strip()
            b_vault_passwords.append(b_vault_pass)

        # Make sure the passwords match by comparing them all to the first password
        for b_vault_password in b_vault_passwords[1:]:
            if self._confirm(b_vault_passwords[0], b_vault_password):
                return b_vault_password
        else:
            if len(b_vault_passwords) == 1:
                return b_vault_passwords[0]
            else:
                return None

    def _confirm(self, b_vault_pass_good, b_vault_pass_to_check):
        # enforce no newline chars at the end of passwords

        if b_vault_pass_good == str(b_vault_pass_to_check):
            return True
        else:
            return False


# TODO: mv these classes to a separate file so we don't pollute vault with 'subprocess' etc
class PlainTextFileVaultSecret(FileVaultSecret):
    '''
    Load Vault Secret from textfile
    '''

    def _engine(self, filename):
        """
        Read a vault password from a file or if executable, execute the script and
        retrieve password from STDOUT
        """

        # TODO: replace with use of self.loader
        try:
            f = open(filename, "rb")
            vault_pass = f.read().strip()
            f.close()
        except (OSError, IOError) as e:
            raise AnsibleError("Could not read vault password file %s: %s" % (filename, e))

        b_vault_data, dummy = self.loader._decrypt_if_vault_data(vault_pass, filename)

        vault_pass = b_vault_data.strip(b'\r\n')

        verify_secret_is_not_empty(vault_pass,
                                   msg='Invalid vault password was provided from file (%s)' % filename)

        return vault_pass

    def __repr__(self):
        if self.filename:
            return "%s(filename='%s')" % (self.__class__.__name__, self.filename)
        return "%s()" % (self.__class__.__name__)


class ScriptVaultSecret(FileVaultSecret):

    class VAULT_ID_RC:
        '''
        script returncode mapping
        '''
        UNKNOWN = 2
        SUCCESS = 0

    def _engine(self, filename):
        if not self.loader.is_executable(filename):
            raise AnsibleVaultError("The vault password script %s was not executable" % filename)

        command = self._build_command()

        stdout, stderr, p = self._run(command)

        self._check_results(stdout, stderr, p)

        vault_pass = stdout.strip(b'\r\n')

        empty_password_msg = 'Invalid vault password was provided from script (%s)' % filename
        verify_secret_is_not_empty(vault_pass,
                                   msg=empty_password_msg)

        return vault_pass

    def _run(self, command):
        try:
            # STDERR not captured to make it easier for users to prompt for input in their scripts
            p = subprocess.Popen(command, stdout=subprocess.PIPE)
        except OSError as e:
            msg_format = "Problem running vault password script %s (%s)." \
                " If this is not a script, remove the executable bit from the file."
            msg = msg_format % (self.filename, e)

            raise AnsibleError(msg)

        stdout, stderr = p.communicate()
        return stdout, stderr, p

    def _check_results(self, stdout, stderr, popen):
        if popen.returncode != self.VAULT_ID_RC.SUCCESS:
            raise AnsibleError("Vault password script %s returned non-zero (%s): %s" %
                               (self.filename, popen.returncode, stderr))

    def _build_command(self):
        return [self.filename]


class ClientScriptVaultSecret(ScriptVaultSecret):

    def __init__(self, filename, encoding=None, loader=None, vault_id=None):
        super(ClientScriptVaultSecret, self).__init__(filename=filename,
                                                      encoding=encoding,
                                                      loader=loader)
        self._vault_id = vault_id
        display.vvvv(u'Executing vault password client script: %s --vault-id %s' % (to_text(filename), to_text(vault_id)))

    def _run(self, command):
        try:
            p = subprocess.Popen(command,
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE)
        except OSError as e:
            msg_format = "Problem running vault password client script %s (%s)." \
                " If this is not a script, remove the executable bit from the file."
            msg = msg_format % (self.filename, e)

            raise AnsibleError(msg)

        stdout, stderr = p.communicate()
        return stdout, stderr, p

    def _check_results(self, stdout, stderr, popen):
        if popen.returncode == self.VAULT_ID_RC.UNKNOWN:
            raise AnsibleError('Vault password client script %s did not find a secret for vault-id=%s: %s' %
                               (self.filename, self._vault_id, stderr))

        if popen.returncode != self.VAULT_ID_RC.SUCCESS:
            raise AnsibleError("Vault password client script %s returned non-zero (%s) when getting secret for vault-id=%s: %s" %
                               (self.filename, popen.returncode, self._vault_id, stderr))

    def _build_command(self):
        command = [self.filename]
        if self._vault_id:
            command.extend(['--vault-id', self._vault_id])

        return command

    def __repr__(self):
        if self.filename:
            return "%s(filename='%s', vault_id='%s')" % \
                (self.__class__.__name__, self.filename, self._vault_id)
        return "%s()" % (self.__class__.__name__)


########################################
#               CIPHERS                #
########################################

class VaultAES256:
    """
    Vault implementation using AES-CTR with an HMAC-SHA256 authentication code.
    Keys are derived using PBKDF2
    """
    # http://www.daemonology.net/blog/2009-06-11-cryptographic-right-answers.html
    # Note: strings in this class should be byte strings by default.

    def __init__(self, cipher_mode, kdf, mac):
        if not HAS_CRYPTOGRAPHY:
            raise AnsibleError(NEED_CRYPTO_LIBRARY)
        self.cipher_mode = cipher_mode
        self._kdf = kdf
        self._mac = mac

    def _gen_keys(self, b_password, b_salt):
        # Number of bytes required for the key, for AES this is also where the name
        # originates from.
        # This number in bits is than divided by 8 to get the byte count.
        # AES128: 128/8 = 16
        # AES192: 192/8 = 24
        # AES256: 256/8 = 32
        key_length = 32

        # The iv lenght depends on the AES mode being used.
        # For most modes the iv match the lenght of a single block.
        # e. g. AES.block_size (bit) == iv_length (byte) * 8 (bit/byte)
        # AES is a 128-bit block cipher, so for
        # CTR: IVs and counter nonces are 16 bytes
        iv_length = algorithms.AES.block_size // 8

        # As we only have one password to derive our secrets from,
        # we instruct the kdf do provide us with a key that we than
        # can split into three parts as required by the CTR mode.
        # key1 and key2 with a size of key_lenght each
        # and an iv with a size of iv_length.
        kdf_key_length = 2 * key_length + iv_length
        b_derivedkey = self._kdf.run(b_password, b_salt, kdf_key_length)
        # Now split the derived key into the parts we need.
        b_key1 = b_derivedkey[:key_length]
        b_key2 = b_derivedkey[key_length:(key_length * 2)]
        b_iv = b_derivedkey[(key_length * 2):(key_length * 2) + iv_length]
        return b_key1, b_key2, b_iv

    def _encrypt(self, b_plaintext, b_key, b_iv):
        cipher = C_Cipher(algorithms.AES(b_key), self.cipher_mode(b_iv), CRYPTOGRAPHY_BACKEND)
        encryptor = cipher.encryptor()
        padder = padding.PKCS7(algorithms.AES.block_size).padder()
        b_ciphertext = encryptor.update(padder.update(b_plaintext) + padder.finalize())
        b_ciphertext += encryptor.finalize()
        return hexlify(b_ciphertext)

    def encrypt(self, b_plaintext, secret, b_salt=None):
        '''
        args: b_plaintext: The bytestring that should be encrypted
        args: secret: The secret that is used for encryption
        args: b_salt: The salt to be used (optional).
                    If None, os.urandom(32) is used instead.
        '''
        if secret is None:
            raise AnsibleVaultError('The secret passed to encrypt() was None')
        b_salt = b_salt or os.urandom(32)
        b_password = secret.bytes
        b_key1, b_key2, b_iv = self._gen_keys(b_password, b_salt)

        b_ciphertext = self._encrypt(b_plaintext, b_key1, b_iv)
        b_mac = self._mac.run(b_ciphertext, b_key2)

        b_vaulttext = b'\n'.join([hexlify(b_salt), b_mac, b_ciphertext])
        # Unnecessary but getting rid of it is a backwards incompatible vault
        # format change
        b_vaulttext = hexlify(b_vaulttext)
        return b_vaulttext

    def _decrypt(self, b_ciphertext, b_key, b_iv):
        cipher = C_Cipher(algorithms.AES(b_key), self.cipher_mode(b_iv), CRYPTOGRAPHY_BACKEND)
        decryptor = cipher.decryptor()
        unpadder = padding.PKCS7(128).unpadder()
        b_plaintext = unpadder.update(
            decryptor.update(b_ciphertext) + decryptor.finalize()
        ) + unpadder.finalize()
        return b_plaintext

    def decrypt(self, b_vaulttext, secret):
        '''
        Validate MAC and only than decrypt the
        vaulttext (binary string) using the secret.
        '''
        b_ciphertext, b_salt, b_crypted_mac = parse_vaulttext(b_vaulttext)
        b_password = secret.bytes
        b_key1, b_key2, b_iv = self._gen_keys(b_password, b_salt)

        if self._mac.is_valid(b_ciphertext, b_key2, b_crypted_mac):
            b_plaintext = self._decrypt(b_ciphertext, b_key1, b_iv)
        else:
            raise AnsibleVaultError('MAC verification failed.')
        return b_plaintext


########################################
#                 KDF                  #
########################################

class VaultPBKDF2(VaultKDF):
    def __init__(self, algorithm):
        super(VaultPBKDF2, self).__init__()
        self.algorithm = algorithm

    def run(self, b_secret, b_salt, key_length, iterations=10000):
        '''
        :arg b_secret: The secret as a binary string. e.g. b'TestSecretDoNOTUseInProducti0n'
        :arg b_salt: A binary representation of the salt that should be used.
                        For most cryptoigraphic operations the salt must be guaranteed to be unique.
                        If you use the same salt with different passphrases on the same file,
                        it can be broken. This also applies to using the same iv on two different
                        files. Further details to this attack vecktor can be found within the
                        documentation of the cypher you're implementing.
        :arg key_length: The requested key matherial size to derive from the secret.
        :kwarg algorithm: A reference to the hash function that should be used (default sha256).
        :kwarg iterations: The iteration count that should be used (default 100000).
        :returns: a byte string containing the derived key.
        '''
        kdf = PBKDF2HMAC(
            algorithm=self.algorithm(),
            length=key_length,
            salt=b_salt,
            iterations=iterations,
            backend=CRYPTOGRAPHY_BACKEND)
        b_derivedkey = kdf.derive(b_secret)
        return b_derivedkey


########################################
#                 MAC                  #
########################################

# Currently we only have this one HMAC function
# CMACs are nowadays faster because of hardware
# acceleration. So there should also be one of
# them
# TODO: Add one CMAC function
# And for example AES-GCM and AES-EAX
# dont need a MAC function as they have
# authentication capability build in.
# So one of them should
# be implemented too.
# TODO: Implemente AES-GCM and/or AES-EAX
class VaultHMAC(VaultMAC):
    def __init__(self, hash_function):
        super(VaultHMAC, self).__init__()
        self.algorithm = hash_function

    @staticmethod
    def run(self, b_ciphertext, b_key):
        hmac = HMAC(b_key, self.algorithm(), CRYPTOGRAPHY_BACKEND)
        hmac.update(b_ciphertext)
        b_hmac = hmac.finalize()
        return to_bytes(hexlify(b_hmac), errors='surrogate_or_strict')

    @staticmethod
    def is_valid(self, b_ciphertext, b_key, b_valid_hmac):
        hmac = HMAC(b_key, self.algorithm(), CRYPTOGRAPHY_BACKEND)
        hmac.update(b_ciphertext)
        try:
            hmac.verify(_unhexlify(b_valid_hmac))
            return True
        except InvalidSignature:
            return False
        return False


########################################
#    Map crypto operations to there    #
#   corresponding library functions,   #
#      so that we can use multiple     #
# libraries without dupplicating code. #
#   We're also going to unify there    #
#         parameters if needed         #
########################################

if HAS_CRYPTOGRAPHY:
    HASHING_ALGORITHM = {
        u'SHA256': hashes.SHA256,
        u'SHA384': hashes.SHA384,
        u'SHA512': hashes.SHA512,
    }
    MAC_ALGORITHM = {
        u'HMAC-SHA256': lambda: VaultHMAC(HASHING_ALGORITHM['SHA256']),
        u'HMAC-SHA384': lambda: VaultHMAC(HASHING_ALGORITHM['SHA384']),
        u'HMAC-SHA512': lambda: VaultHMAC(HASHING_ALGORITHM['SHA512']),
    }
    KDF_MAPPING = {
        u'PBKDF2': lambda: VaultPBKDF2(HASHING_ALGORITHM['SHA256']),
    }
    CIPHER_MAPPING = {
        (u'AES256', u'CTR', u'HMAC-SHA256'): lambda kdf: VaultAES256(modes.CTR, kdf, MAC_ALGORITHM['HMAC-SHA256']),
        (u'AES256', u'CBC', u'HMAC-SHA256'): lambda kdf: VaultAES256(modes.CBC, kdf, MAC_ALGORITHM['HMAC-SHA256']),
    }
else:
    # if we do not have any cryptolibrary, initialize our function mapping
    # as empty, just to be save.
    HASHING_ALGORITHM = {
    }
    MAC_ALGORITHM = {
    }
    KDF_MAPPING = {
    }
    CIPHER_MAPPING = {
    }
    raise AnsibleError(NEED_CRYPTO_LIBRARY + '(Detected in encrypt)')

