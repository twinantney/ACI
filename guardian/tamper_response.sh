#!/bin/bash

RUNTIME_CONFIG="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/core/runtime_config.conf"

if [ -f "$RUNTIME_CONFIG" ]; then
    source "$RUNTIME_CONFIG"
else
    echo "RUNTIME CONFIGURATION MISSING"
    exit 1
fi

set_emergency_lock() {
    sed -i "s/^SYSTEM_STATE=.*/SYSTEM_STATE=EMERGENCY_LOCK/" "$STATE_FILE"
}

record_event() {
    echo "$(date) :: SECURITY_EVENT :: $1" >> "$AUDIT_LOG"
}

case "$1" in

tamper)
    echo "TAMPER CONDITION DETECTED"
    record_event "TAMPER_DETECTED"
    set_emergency_lock
    record_event "SYSTEM_EMERGENCY_LOCK_TRIGGERED"
    echo "SYSTEM MOVED TO EMERGENCY_LOCK"
    ;;

*)
    echo "Usage:"
    echo "./tamper_response.sh tamper"
    ;;

esac
