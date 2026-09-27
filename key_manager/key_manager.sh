#!/bin/bash

############################################
# OPTIMUS7 KEY MANAGEMENT ENGINE
# Runtime Bound Key Controller
############################################

RUNTIME_CONFIG="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/core/runtime_config.conf"

if [ -f "$RUNTIME_CONFIG" ]; then
    source "$RUNTIME_CONFIG"
else
    echo "RUNTIME CONFIGURATION MISSING"
    exit 1
fi

echo "KEY MANAGEMENT ENGINE ONLINE"

if [ -f "$KEY_MANAGER_PATH/key_policy.conf" ]; then

    echo "KEY POLICY LOADED"

else

    echo "KEY POLICY MISSING"
    exit 1

fi

echo "$(date): SECURITY_EVENT :: KEY_MANAGER_STARTED" >> "$AUDIT_LOG"

echo "KEY MANAGEMENT READY"
