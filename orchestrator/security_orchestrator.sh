#!/bin/bash

############################################
# OPTIMUS7 SECURITY ORCHESTRATOR
# Unified Runtime Coordination Layer
############################################


RUNTIME_CONFIG="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/core/runtime_config.conf"


if [ -f "$RUNTIME_CONFIG" ]; then
    source "$RUNTIME_CONFIG"
else
    echo "RUNTIME CONFIG MISSING"
    exit 1
fi


echo "OPTIMUS7 SECURITY ORCHESTRATOR ONLINE"

echo "SYSTEM: $SYSTEM_NAME"


if [ -f "$STATE_FILE" ]; then

    CURRENT=$(grep "^SYSTEM_STATE=" "$STATE_FILE" | cut -d'=' -f2)

else

    CURRENT="UNKNOWN"

fi


echo "SYSTEM STATE: $CURRENT"


echo
echo "--- COMPONENT BIND CHECK ---"


[ -d "$SSI_PATH" ] && echo "SSI PATH OK" || echo "SSI PATH MISSING"

[ -d "$ASI_PATH" ] && echo "ASI PATH OK" || echo "ASI PATH MISSING"

[ -d "$AUTH_PATH" ] && echo "AUTH PATH OK" || echo "AUTH PATH MISSING"

[ -d "$POLICY_PATH" ] && echo "POLICY PATH OK" || echo "POLICY PATH MISSING"

[ -d "$VAULT_PATH" ] && echo "VAULT PATH OK" || echo "VAULT PATH MISSING"


echo


case "$CURRENT" in


UNLOCKED)

    echo "SECURITY STATUS: READY"

    echo "$(date): SECURITY_EVENT :: ORCHESTRATOR_READY" >> "$AUDIT_LOG"

;;


LOCKED)

    echo "SECURITY STATUS: LOCKED"

    echo "$(date): SECURITY_EVENT :: ORCHESTRATOR_LOCKED" >> "$AUDIT_LOG"

;;


EMERGENCY_LOCK)

    echo "SECURITY STATUS: EMERGENCY"

    echo "$(date): SECURITY_EVENT :: ORCHESTRATOR_EMERGENCY" >> "$AUDIT_LOG"

;;


*)

    echo "SECURITY STATUS: UNKNOWN"

    echo "$(date): SECURITY_EVENT :: ORCHESTRATOR_UNKNOWN_STATE" >> "$AUDIT_LOG"

;;

esac


echo "ORCHESTRATOR COMPLETE"

