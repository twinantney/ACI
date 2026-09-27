#!/bin/bash

BASE="$HOME/SECURITY_SYSTEM_TEST"

STATE="$BASE/core/security_state.conf"
LOG="$BASE/audit/security.log"

echo "=============================="
echo "SSI FULL SYSTEM REPORT"
echo "=============================="

echo

echo "--- SECURITY COMPONENTS ---"

check() {
    if [ -f "$1" ]; then
        echo "$2 ........ ONLINE"
    else
        echo "$2 ........ MISSING"
    fi
}

check "$BASE/core/state_engine.sh" "CORE"
check "$BASE/auth/auth_engine.sh" "AUTH"
check "$BASE/guardian/security_controller.sh" "GUARDIAN"
check "$BASE/policy/policy_engine.sh" "POLICY"
check "$BASE/vault/vault_gate.sh" "VAULT"
check "$BASE/orchestrator/security_orchestrator.sh" "ORCHESTRATOR"
check "$BASE/key_manager/key_manager.sh" "KEY_MANAGER"

echo

echo "--- ASI INTELLIGENCE ---"

check "$BASE/asi/core/asi_core.sh" "ASI_CORE"
check "$BASE/asi/memory/memory_engine.sh" "ASI_MEMORY"
check "$BASE/asi/knowledge/context_engine.sh" "ASI_KNOWLEDGE"
check "$BASE/asi/cognition/cognition_engine.sh" "ASI_COGNITION"
check "$BASE/asi/decision/decision_engine.sh" "ASI_DECISION"
check "$BASE/asi/action_reaction/action_engine.sh" "ASI_ACTION"

echo

echo "--- CURRENT STATE ---"

if [ -f "$STATE" ]; then
    grep SYSTEM_STATE "$STATE"
else
    echo "STATE UNAVAILABLE"
fi

echo

echo "--- RECENT EVENTS ---"

if [ -f "$LOG" ]; then
    tail -5 "$LOG"
else
    echo "AUDIT UNAVAILABLE"
fi

echo

echo "--- TELEMETRY ---"

if [ -f "$BASE/ssi/telemetry/ssi_assessment.log" ]; then
    echo "LAST SNAPSHOT: AVAILABLE"
else
    echo "LAST SNAPSHOT: MISSING"
fi

echo

echo "SSI FULL REPORT COMPLETE"
