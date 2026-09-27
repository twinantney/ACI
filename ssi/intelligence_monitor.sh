#!/bin/bash

BASE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

REGISTRY="$BASE/ssi/registry/system_registry.conf"

echo "=============================="
echo "SSI INTELLIGENCE MONITOR ONLINE"
echo "=============================="

echo

if [ ! -f "$REGISTRY" ]; then
    echo "REGISTRY MISSING"
    exit 1
fi

source "$REGISTRY"

resolve_path() {
    TARGET="$1"
    if [[ "$TARGET" == ../* ]]; then
        TARGET="${TARGET#../}"
    fi
    realpath "$BASE/$TARGET" 2>/dev/null
}

check_component() {
    COMPONENT_PATH="$1"
    COMPONENT_NAME="$2"
    if [ -f "$COMPONENT_PATH" ]; then
        if [ -x "$COMPONENT_PATH" ]; then
            echo "$COMPONENT_NAME ........ PRESENT + EXECUTABLE"
        else
            echo "$COMPONENT_NAME ........ PRESENT + NOT EXECUTABLE"
        fi
    else
        echo "$COMPONENT_NAME ........ MISSING"
    fi
}

echo "--- SECURITY COMPONENTS ---"

check_component "$(resolve_path "$CORE")" "CORE"
check_component "$(resolve_path "$AUTH")" "AUTH"
check_component "$(resolve_path "$GUARDIAN")" "GUARDIAN"
check_component "$(resolve_path "$POLICY")" "POLICY"
check_component "$(resolve_path "$VAULT")" "VAULT"
check_component "$(resolve_path "$ORCHESTRATOR")" "ORCHESTRATOR"
check_component "$(resolve_path "$KEY_MANAGER")" "KEY_MANAGER"
check_component "$(resolve_path "$CONFIG_VALIDATOR")" "CONFIG_VALIDATOR"

echo

echo "--- ASI INTELLIGENCE COMPONENTS ---"

check_component "$(resolve_path "$ASI_CORE")" "ASI_CORE"
check_component "$(resolve_path "$ASI_MEMORY")" "ASI_MEMORY"
check_component "$(resolve_path "$ASI_KNOWLEDGE")" "ASI_KNOWLEDGE"
check_component "$(resolve_path "$ASI_COGNITION")" "ASI_COGNITION"
check_component "$(resolve_path "$ASI_DECISION")" "ASI_DECISION"
check_component "$(resolve_path "$ASI_ACTION_REACTION")" "ASI_ACTION_REACTION"

echo

echo "--- SYSTEM BIND STATUS ---"

TOTAL=0
MISSING=0

for COMPONENT in \
"$CORE" "$AUTH" "$GUARDIAN" "$POLICY" "$VAULT" "$ORCHESTRATOR" "$KEY_MANAGER" "$CONFIG_VALIDATOR" \
"$ASI_CORE" "$ASI_MEMORY" "$ASI_KNOWLEDGE" "$ASI_COGNITION" "$ASI_DECISION" "$ASI_ACTION_REACTION"
do
    TOTAL=$((TOTAL+1))
    if [ ! -f "$(resolve_path "$COMPONENT")" ]; then
        MISSING=$((MISSING+1))
    fi
done

echo "REGISTERED COMPONENTS : $TOTAL"
echo "MISSING COMPONENTS    : $MISSING"

if [ "$MISSING" -eq 0 ]; then
    echo "SYSTEM BIND CHECK     : READY"
else
    echo "SYSTEM BIND CHECK     : INCOMPLETE"
fi

echo

echo "SSI INTELLIGENCE MONITOR COMPLETE"
