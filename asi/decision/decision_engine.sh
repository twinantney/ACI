#!/bin/bash

BASE="$HOME/SECURITY_SYSTEM_TEST"

STATE="$BASE/core/security_state.conf"

echo "ASI DECISION ENGINE ONLINE"

if [ -f "$STATE" ]; then

    CURRENT=$(grep SYSTEM_STATE "$STATE" | cut -d'=' -f2)

else

    CURRENT="UNKNOWN"

fi


case "$CURRENT" in

UNLOCKED)
    echo "DECISION: NORMAL"
    ;;

LOCKED)
    echo "DECISION: WARNING"
    ;;

EMERGENCY_LOCK)
    echo "DECISION: EMERGENCY CONDITION"
    ;;

*)
    echo "DECISION: UNKNOWN"
    ;;

esac

echo "ASI DECISION COMPLETE"
