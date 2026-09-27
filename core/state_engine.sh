#!/bin/bash

############################################
# OPTIMUS⁷ CORE STATE ENGINE
# Unified Runtime State Controller
############################################


############################################
# LOAD RUNTIME AUTHORITY
############################################

RUNTIME_CONFIG="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/core/runtime_config.conf"


if [ -f "$RUNTIME_CONFIG" ]; then
    source "$RUNTIME_CONFIG"
else
    echo "RUNTIME CONFIGURATION MISSING"
    exit 1
fi


############################################
# STATE INITIALIZATION
############################################

ensure_files() {

    if [ ! -f "$STATE_FILE" ]; then

        echo "SYSTEM_STATE=UNKNOWN" > "$STATE_FILE"
        echo "FAILED_ATTEMPTS=0" >> "$STATE_FILE"
        echo "MAX_FAILED_ATTEMPTS=3" >> "$STATE_FILE"

    fi


    if [ ! -f "$AUDIT_LOG" ]; then

        touch "$AUDIT_LOG"

    fi

}


############################################
# STATE ACCESS
############################################

get_state() {

    grep "^SYSTEM_STATE=" "$STATE_FILE" | cut -d'=' -f2

}


set_state() {

    NEW_STATE="$1"

    sed -i "s/^SYSTEM_STATE=.*/SYSTEM_STATE=$NEW_STATE/" "$STATE_FILE"

    echo "$(date): STATE_CHANGED_TO_$NEW_STATE" >> "$AUDIT_LOG"

}


############################################
# STATE DISPLAY
############################################

show_state() {

    CURRENT="$(get_state)"

    echo "CURRENT SECURITY STATE: $CURRENT"

}


############################################
# STATE OPERATIONS
############################################

lock_system() {

    set_state "LOCKED"

    echo "SYSTEM LOCKED"

}


unlock_system() {

    set_state "UNLOCKED"

    echo "SYSTEM UNLOCKED"

}


emergency_lock() {

    set_state "EMERGENCY_LOCK"

    echo "$(date): EMERGENCY_LOCK_TRIGGERED" >> "$AUDIT_LOG"

    echo "EMERGENCY LOCK ACTIVE"

}


############################################
# SYSTEM STATUS
############################################

system_status() {

    echo "OPTIMUS7 CORE STATE ENGINE ONLINE"

    echo "SYSTEM: $SYSTEM_NAME"

    echo "RUNTIME: $RUNTIME_VERSION"

    echo "STATE FILE: $STATE_FILE"

    echo "AUDIT LOG: $AUDIT_LOG"

    show_state

}


############################################
# STARTUP
############################################

ensure_files


case "$1" in


status)

    system_status

    ;;


lock)

    lock_system

    ;;


unlock)

    unlock_system

    ;;


emergency)

    emergency_lock

    ;;


*)

    echo "Usage:"
    echo "./state_engine.sh status"
    echo "./state_engine.sh lock"
    echo "./state_engine.sh unlock"
    echo "./state_engine.sh emergency"

    ;;


esac
