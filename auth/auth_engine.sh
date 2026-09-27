#!/bin/bash

############################################
# OPTIMUS7 AUTHENTICATION ENGINE
# Runtime Bound Authentication Controller
############################################

RUNTIME_CONFIG="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/core/runtime_config.conf"

if [ -f "$RUNTIME_CONFIG" ]; then
    source "$RUNTIME_CONFIG"
else
    echo "RUNTIME CONFIGURATION MISSING"
    exit 1
fi

echo "OPTIMUS7 AUTH ENGINE ONLINE"

############################################
# RUNTIME VALIDATION
############################################

if [ ! -f "$STATE_FILE" ]; then
    echo "STATE FILE MISSING"
    exit 1
fi

if [ ! -f "$AUDIT_LOG" ]; then
    touch "$AUDIT_LOG"
fi

if [ ! -f "$AUTH_CONFIG" ]; then
    echo "AUTH CONFIGURATION MISSING"
    exit 1
fi

############################################
# AUTH CONFIGURATION
############################################

CONFIG="$AUTH_CONFIG"

PRIMARY_KEY=$(grep "^PRIMARY_KEY=" "$CONFIG" | cut -d'=' -f2)
EMERGENCY_KEY=$(grep "^EMERGENCY_KEY=" "$CONFIG" | cut -d'=' -f2)
FAILED=$(grep "^FAILED_ATTEMPTS=" "$CONFIG" | cut -d'=' -f2)
MAX=$(grep "^MAX_ATTEMPTS=" "$CONFIG" | cut -d'=' -f2)

############################################
# STATE CONTROL
############################################

set_state() {
    NEW_STATE="$1"
    sed -i "s/^SYSTEM_STATE=.*/SYSTEM_STATE=$NEW_STATE/" "$STATE_FILE"
    echo "$(date): AUTH_STATE_CHANGED_TO_$NEW_STATE" >> "$AUDIT_LOG"
}

get_state() {
    grep "^SYSTEM_STATE=" "$STATE_FILE" | cut -d'=' -f2
}

############################################
# ATTEMPT CONTROL
############################################

reset_attempts() {
    sed -i "s/^FAILED_ATTEMPTS=.*/FAILED_ATTEMPTS=0/" "$CONFIG"
}

increment_attempts() {
    FAILED=$((FAILED+1))
    sed -i "s/^FAILED_ATTEMPTS=.*/FAILED_ATTEMPTS=$FAILED/" "$CONFIG"
}

############################################
# AUDIT
############################################

log_event() {
    echo "$(date): AUTH_EVENT :: $1" >> "$AUDIT_LOG"
}

############################################
# AUTH OPERATIONS
############################################

authenticate_primary() {
    read -s -p "Primary Key: " INPUT
    echo

    if [ "$INPUT" = "$PRIMARY_KEY" ]; then
        reset_attempts
        set_state "UNLOCKED"
        log_event "PRIMARY_AUTH_SUCCESS"
        echo "ACCESS GRANTED"
    else
        increment_attempts
        log_event "PRIMARY_AUTH_FAILED"
        echo "ACCESS DENIED"

        if [ "$FAILED" -ge "$MAX" ]; then
            set_state "EMERGENCY_LOCK"
            log_event "EMERGENCY_LOCK_TRIGGERED"
            echo "EMERGENCY LOCK ACTIVE"
        fi
    fi
}

authenticate_emergency() {
    read -s -p "Emergency Key: " INPUT
    echo

    if [ "$INPUT" = "$EMERGENCY_KEY" ]; then
        reset_attempts
        set_state "LOCKED"
        log_event "EMERGENCY_RECOVERY_SUCCESS"
        echo "RECOVERY SUCCESS"
    else
        log_event "EMERGENCY_RECOVERY_FAILED"
        echo "RECOVERY FAILED"
    fi
}

############################################
# STATUS
############################################

status() {
    echo "SYSTEM: $SYSTEM_NAME"
    echo "RUNTIME: $RUNTIME_VERSION"
    echo "CURRENT STATE: $(get_state)"
    echo "AUTH CONFIG: READY"
    echo "STATE BINDING: READY"
    echo "AUDIT BINDING: READY"
}

############################################
# COMMAND ROUTER
############################################

case "$1" in

unlock)
    authenticate_primary
    ;;

emergency)
    authenticate_emergency
    ;;

status)
    status
    ;;

*)
    echo "Usage:"
    echo "./auth_engine.sh unlock"
    echo "./auth_engine.sh emergency"
    echo "./auth_engine.sh status"
    ;;

esac
