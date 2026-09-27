#!/bin/bash

BASE="$HOME/SECURITY_SYSTEM_TEST"

EVENT_LOG="$BASE/asi/memory/event_memory.log"
INTELLIGENCE_LOG="$BASE/asi/memory/intelligence_memory.log"

echo "ASI MEMORY INTELLIGENCE ONLINE"

echo "===== MEMORY ANALYSIS $(date) =====" >> "$INTELLIGENCE_LOG"

if [ ! -f "$EVENT_LOG" ]; then
    echo "NO EVENT MEMORY AVAILABLE"
    exit 1
fi

TOTAL=$(wc -l < "$EVENT_LOG")

echo "TOTAL_EVENTS=$TOTAL" | tee -a "$INTELLIGENCE_LOG"

echo "--- EVENT CATEGORIES ---" | tee -a "$INTELLIGENCE_LOG"

if grep -q "VAULT_ACCESS_DENIED" "$EVENT_LOG"; then
    echo "CATEGORY=ACCESS_SECURITY" | tee -a "$INTELLIGENCE_LOG"
fi

if grep -q "EMERGENCY" "$EVENT_LOG"; then
    echo "CATEGORY=EMERGENCY_ACTIVITY" | tee -a "$INTELLIGENCE_LOG"
fi

if grep -q "KEY_MANAGER" "$EVENT_LOG"; then
    echo "CATEGORY=KEY_MANAGEMENT" | tee -a "$INTELLIGENCE_LOG"
fi

echo "MEMORY INTELLIGENCE COMPLETE"
