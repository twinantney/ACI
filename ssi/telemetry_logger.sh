#!/bin/bash

BASE="$HOME/SECURITY_SYSTEM_TEST"

STATE="$BASE/core/security_state.conf"
AUDIT="$BASE/audit/security.log"
LOG="$BASE/ssi/telemetry/ssi_assessment.log"

echo "==============================" >> "$LOG"
echo "SSI TELEMETRY SNAPSHOT" >> "$LOG"
echo "TIME: $(date)" >> "$LOG"

echo "--- SYSTEM STATE ---" >> "$LOG"

if [ -f "$STATE" ]; then
    grep SYSTEM_STATE "$STATE" >> "$LOG"
else
    echo "STATE UNAVAILABLE" >> "$LOG"
fi

echo "--- RECENT EVENTS ---" >> "$LOG"

if [ -f "$AUDIT" ]; then
    tail -5 "$AUDIT" >> "$LOG"
else
    echo "AUDIT UNAVAILABLE" >> "$LOG"
fi

echo "--- ASI STATUS ---" >> "$LOG"

if [ -f "$BASE/asi/core/asi_core.sh" ]; then
    echo "ASI_CORE=AVAILABLE" >> "$LOG"
else
    echo "ASI_CORE=MISSING" >> "$LOG"
fi

if [ -f "$BASE/asi/action_reaction/action_engine.sh" ]; then
    echo "ASI_ACTION_REACTION=AVAILABLE" >> "$LOG"
else
    echo "ASI_ACTION_REACTION=MISSING" >> "$LOG"
fi

echo "SSI TELEMETRY COMPLETE" >> "$LOG"
