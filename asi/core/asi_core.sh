#!/bin/bash

BASE="$HOME/SECURITY_SYSTEM_TEST/asi"

MEMORY="$BASE/memory"

echo "ASI CORE ONLINE"

if [ -d "$MEMORY" ]; then
    echo "MEMORY SYSTEM AVAILABLE"
else
    echo "MEMORY SYSTEM MISSING"
    exit 1
fi

echo "$(date): ASI_CORE_STARTED" >> "$MEMORY/system_memory.log"

echo "ASI STATUS: INITIALIZED"
