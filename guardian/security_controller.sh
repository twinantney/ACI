#!/bin/bash

RUNTIME_CONFIG="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/core/runtime_config.conf"

if [ -f "$RUNTIME_CONFIG" ]; then
    source "$RUNTIME_CONFIG"
else
    echo "RUNTIME CONFIGURATION MISSING"
    exit 1
fi

CURRENT=$(grep "^SYSTEM_STATE=" "$STATE_FILE" | cut -d'=' -f2)

case "$CURRENT" in

UNLOCKED)
    echo "SECURITY CLEAR"
    echo "AUTHORIZED OPERATIONS ENABLED"
    ;;

LOCKED)
    echo "SECURITY RESTRICTION ACTIVE"
    echo "OPERATIONS BLOCKED"
    ;;

EMERGENCY_LOCK)
    echo "CRITICAL SECURITY STATE"
    echo "ALL OPERATIONS BLOCKED"
    ;;

*)
    echo "UNKNOWN STATE"
    ;;

esac
