#!/bin/bash

BASE="$HOME/SECURITY_SYSTEM_TEST/asi"

echo "=============================="
echo "ASI INTEGRATION ENGINE ONLINE"
echo "=============================="

echo

echo "[1] CORE INITIALIZATION"
"$BASE/core/asi_core.sh"

echo

echo "[2] MEMORY UPDATE"
"$BASE/memory/memory_engine.sh"

echo

echo "[3] KNOWLEDGE CONTEXT"
"$BASE/knowledge/context_engine.sh"

echo

echo "[4] COGNITION ANALYSIS"
"$BASE/cognition/cognition_engine.sh"

echo

echo "[5] DECISION ANALYSIS"
"$BASE/decision/decision_engine.sh"

echo

echo "[6] ACTION / REACTION"
"$BASE/action_reaction/action_engine.sh"

echo

echo "=============================="
echo "ASI KNOWLEDGE INTEGRATION COMPLETE"
echo "=============================="
