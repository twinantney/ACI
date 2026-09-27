#!/bin/bash

BASE="$HOME/SECURITY_SYSTEM_TEST"

MEMORY="$BASE/asi/memory"
STATE="$BASE/core/security_state.conf"

echo "ASI COGNITION ENGINE ONLINE"

echo "--- SYSTEM ASSESSMENT ---"

if [ -f "$STATE" ]; then
    echo "STATE:"
    grep SYSTEM_STATE "$STATE"
else
    echo "STATE UNAVAILABLE"
fi

echo "--- MEMORY SUMMARY ---"

if [ -f "$MEMORY/event_memory.log" ]; then
    tail -5 "$MEMORY/event_memory.log"
else
    echo "EVENT MEMORY EMPTY"
fi

echo "ASI ASSESSMENT COMPLETE"
