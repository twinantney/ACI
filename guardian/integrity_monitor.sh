#!/bin/bash

RUNTIME_CONFIG="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/core/runtime_config.conf"

if [ -f "$RUNTIME_CONFIG" ]; then
    source "$RUNTIME_CONFIG"
else
    echo "RUNTIME CONFIGURATION MISSING"
    exit 1
fi

HASH_FILE="$GUARDIAN_PATH/vault_integrity.hash"

generate_hash() {
    find "$VAULT_PATH" -type f ! -name "*.hash" \
    -exec sha256sum {} \; > "$HASH_FILE"
    echo "BASELINE CREATED"
}

check_hash() {
    CURRENT=$(mktemp)
    find "$VAULT_PATH" -type f ! -name "*.hash" \
    -exec sha256sum {} \; > "$CURRENT"

    if cmp -s "$HASH_FILE" "$CURRENT"; then
        echo "INTEGRITY VERIFIED"
    else
        echo "INTEGRITY FAILURE"
        echo "$(date): SECURITY_EVENT :: TAMPER_DETECTED" >> "$AUDIT_LOG"
        "$GUARDIAN_PATH/tamper_response.sh" tamper
    fi

    rm "$CURRENT"
}

case "$1" in
create) generate_hash ;;
check) check_hash ;;
*)
    echo "Usage:"
    echo "./integrity_monitor.sh create"
    echo "./integrity_monitor.sh check"
    ;;
esac
