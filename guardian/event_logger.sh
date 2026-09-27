#!/bin/bash

RUNTIME_CONFIG="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/core/runtime_config.conf"

if [ -f "$RUNTIME_CONFIG" ]; then
    source "$RUNTIME_CONFIG"
else
    echo "RUNTIME CONFIGURATION MISSING"
    exit 1
fi

EVENT="$1"

echo "$(date) :: SECURITY_EVENT :: $EVENT" >> "$AUDIT_LOG"

echo "EVENT RECORDED: $EVENT"
