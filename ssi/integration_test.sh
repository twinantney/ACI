#!/bin/bash

BASE="$HOME/SECURITY_SYSTEM_TEST"

AUDIT="$BASE/audit/security.log"

echo "=============================="
echo "SSI END-TO-END INTEGRATION TEST"
echo "=============================="

echo

echo "[1] GENERATING TEST EVENT"

echo "$(date): SECURITY_EVENT :: SSI_INTEGRATION_TEST_EVENT" >> "$AUDIT"

echo "TEST EVENT WRITTEN"

echo

echo "[2] CHECKING AUDIT INGESTION"

tail -5 "$AUDIT"

echo

echo "[3] RUNNING ASI MEMORY UPDATE"

"$BASE/asi/memory/memory_engine.sh"

echo

echo "[4] RUNNING ASI KNOWLEDGE CONTEXT"

"$BASE/asi/knowledge/context_engine.sh"

echo

echo "[5] RUNNING ASI COGNITION"

"$BASE/asi/cognition/cognition_engine.sh"

echo

echo "[6] RUNNING ASI DECISION"

"$BASE/asi/decision/decision_engine.sh"

echo

echo "[7] RUNNING ASI ACTION/REACTION"

"$BASE/asi/action_reaction/action_engine.sh"

echo

echo "[8] RUNNING SSI REPORT"

"$BASE/ssi/ssi_full_report.sh"

echo

echo "=============================="
echo "SSI INTEGRATION TEST COMPLETE"
echo "=============================="
