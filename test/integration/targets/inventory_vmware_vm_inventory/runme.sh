#!/usr/bin/env bash

[[ -n "$DEBUG" || -n "$ANSIBLE_DEBUG" ]] && set -x

set -euo pipefail

# Required to differentiate between Python 2 and 3 environ
PYTHON=${ANSIBLE_TEST_PYTHON_INTERPRETER:-python}

export ANSIBLE_CONFIG=ansible.cfg
export VMWARE_SERVER="${VCENTER_HOST}"
export VMWARE_USERNAME="${VMWARE_USERNAME:-user}"
export VMWARE_PASSWORD="${VMWARE_PASSWORD:-pass}"
VMWARE_CONFIG=test-config.vmware.yaml

cat > "$VMWARE_CONFIG" <<VMWARE_YAML
plugin: vmware_vm_inventory
strict: False
validate_certs: False
with_tags: False
VMWARE_YAML

cleanup() {
    echo "Cleanup"
    if [ -f "${VMWARE_CONFIG}" ]; then
        rm -f "${VMWARE_CONFIG}"
    fi
    if [ -d "$(pwd)/inventory_cache" ]; then
        echo "Removing $(pwd)/inventory_cache"
        rm -rf "$(pwd)/inventory_cache"
    fi
    echo "Done"
    exit 0
}

trap cleanup INT TERM EXIT

echo "DEBUG: Using ${VCENTER_HOST} with username ${VMWARE_USERNAME} and password ${VMWARE_PASSWORD}"

echo "Kill all previous instances"
curl "http://${VCENTER_HOST}:5000/killall" > /dev/null 2>&1

echo "Start new VCSIM server"
curl "http://${VCENTER_HOST}:5000/spawn?dc=2&cluster=1&folder=0" > /dev/null 2>&1

echo "Debugging new instances"
curl "http://${VCENTER_HOST}:5000/govc_find"

# Creates folder structure to test inventory folder support
ansible-playbook -i 'localhost,' test_vmware_prep_folders.yml

# Get inventory
ansible-inventory -i ${VMWARE_CONFIG} --list

# Get inventory using YAML
ansible-inventory -i ${VMWARE_CONFIG} --list --yaml

# Install TOML for --toml
${PYTHON} -m pip install toml

# Get inventory using TOML
ansible-inventory -i ${VMWARE_CONFIG} --list --toml

echo "Check if cache is working for inventory plugin"
ls "$(pwd)/inventory_cache/vmware_vm_"* > /dev/null 2>&1
if [ $? -ne 0 ]; then
    echo "Cache directory not found. Please debug"
    exit 1
fi
echo "Cache is working"

# Test playbook with given inventory
ansible-playbook -i ${VMWARE_CONFIG} test_vmware_vm_inventory.yml --connection=local "$@"
