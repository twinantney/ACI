#!/bin/bash

BASE="$HOME/SECURITY_SYSTEM_TEST"

KNOWLEDGE="$BASE/asi/knowledge/knowledge_base.conf"
MEMORY="$BASE/asi/memory/event_memory.log"

echo "ASI CONTEXT ENGINE ONLINE"

if [ -f "$KNOWLEDGE" ]; then
    echo "KNOWLEDGE BASE LOADED"
else
    echo "KNOWLEDGE BASE MISSING"
    exit 1
fi

echo "--- CONTEXT ANALYSIS ---"

if [ -f "$MEMORY" ]; then

    SORTED_KEYS=$(while IFS='=' read -r KEY VALUE
    do
        LOOKUP="${KEY#EVENT_}"
        LOOKUP="${LOOKUP#STATE_}"
        echo "${#LOOKUP} $LOOKUP=$VALUE"
    done < "$KNOWLEDGE" | sort -rn -k1,1)

    while read -r EVENT
    do
        MATCHED="NO_MATCH"

        while read -r LEN PAIR
        do
            LOOKUP="${PAIR%%=*}"
            VALUE="${PAIR#*=}"

            case "$EVENT" in
                *"$LOOKUP"*)
                    MATCHED="$VALUE"
                    break
                    ;;
            esac
        done <<< "$SORTED_KEYS"

        echo "OBSERVED: $EVENT :: CONTEXT=$MATCHED"

    done < "$MEMORY"

else

    echo "NO MEMORY AVAILABLE"

fi

echo "ASI CONTEXT COMPLETE"
