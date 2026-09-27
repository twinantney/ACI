#!/bin/bash

BASE="$HOME/SECURITY_SYSTEM_TEST"

REGISTRY="$BASE/ssi/registry/system_registry.conf"
STATE="$BASE/core/security_state.conf"
LOG="$BASE/audit/security.log"

echo "=============================="
echo "SSI SYSTEM INTELLIGENCE ONLINE"
echo "=============================="

echo

echo "--- SYSTEM STATE ---"

if [ -f "$STATE" ]; then
    grep SYSTEM_STATE "$STATE"
else
    echo "STATE FILE MISSING"
fi

echo

echo "--- REGISTERED COMPONENTS ---"

if [ -f "$REGISTRY" ]; then
    grep "=" "$REGISTRY"
else
    echo "REGISTRY MISSING"
fi

echo

echo "--- RECENT EVENTS ---"

if [ -f "$LOG" ]; then
    tail -5 "$LOG"
else
    echo "AUDIT LOG MISSING"
fi

echo

echo "SSI SYSTEM ASSESSMENT COMPLETE"
