#!/bin/bash

############################################
# OPTIMUS VAULT SECURITY GATE
# Runtime Bound Access Controller
############################################


RUNTIME_CONFIG="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/core/runtime_config.conf"


if [ -f "$RUNTIME_CONFIG" ]; then
    source "$RUNTIME_CONFIG"
else
    echo "RUNTIME CONFIGURATION MISSING"
    exit 1
fi


POLICY="$POLICY_PATH/policy_engine.sh"


if [ ! -f "$POLICY" ]; then
    echo "POLICY ENGINE MISSING"
    exit 1
fi


echo "OPTIMUS VAULT SECURITY GATE ONLINE"

RESULT=$("$POLICY")


echo "$RESULT"


if echo "$RESULT" | grep -q "ACCESS ALLOWED"; then

    echo "$(date): SECURITY_EVENT :: VAULT_ACCESS_GRANTED" >> "$AUDIT_LOG"

    echo "VAULT ACCESS GRANTED"

    ls -la "$(dirname "${BASH_SOURCE[0]}")"


else

    echo "$(date): SECURITY_EVENT :: VAULT_ACCESS_DENIED" >> "$AUDIT_LOG"

    echo "VAULT ACCESS DENIED"

fi
