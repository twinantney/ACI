#!/bin/bash

RUNTIME_CONFIG="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/core/runtime_config.conf"

if [ -f "$RUNTIME_CONFIG" ]; then
    source "$RUNTIME_CONFIG"
else
    echo "RUNTIME CONFIGURATION MISSING"
    exit 1
fi

echo "SSI OBSERVER ONLINE"

echo "--- SYSTEM STATE ---"

if [ -f "$STATE_FILE" ]; then
    grep SYSTEM_STATE "$STATE_FILE"
else
    echo "STATE FILE MISSING"
fi

echo "--- CONFIGURATION ---"

for FILE in system_state.conf policy.conf security_metadata.conf
do
    if [ -f "$CONFIG_PATH/$FILE" ]; then
        echo "$FILE : PRESENT"
    else
        echo "$FILE : MISSING"
    fi
done

echo "--- RECENT SECURITY EVENTS ---"

tail -5 "$AUDIT_LOG"

echo "SSI OBSERVATION COMPLETE"
