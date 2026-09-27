#!/bin/bash

RUNTIME_CONFIG="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/core/runtime_config.conf"

if [ -f "$RUNTIME_CONFIG" ]; then
    source "$RUNTIME_CONFIG"
else
    echo "RUNTIME CONFIGURATION MISSING"
    exit 1
fi

echo "CONFIGURATION VALIDATOR ONLINE"

FILES=(
"system_state.conf"
"policy.conf"
"security_metadata.conf"
)

for FILE in "${FILES[@]}"
do
    if [ -f "$CONFIG_PATH/$FILE" ]; then
        echo "$FILE : PRESENT"
    else
        echo "$FILE : MISSING"
        echo "$(date): SECURITY_EVENT :: CONFIG_MISSING_$FILE" >> "$AUDIT_LOG"
        exit 1
    fi
done

echo "$(date): SECURITY_EVENT :: CONFIG_VALIDATION_SUCCESS" >> "$AUDIT_LOG"

echo "CONFIGURATION STATUS: VALID"
