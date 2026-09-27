#!/bin/bash

BASE="$HOME/SECURITY_SYSTEM_TEST"

MEMORY="$BASE/asi/memory"
AUDIT="$BASE/audit/security.log"

echo "ASI MEMORY ENGINE ONLINE"

echo "$(date): MEMORY_ENGINE_STARTED" >> "$MEMORY/system_memory.log"

echo "--- RECENT SECURITY EVENTS ---"

tail -5 "$AUDIT" >> "$MEMORY/event_memory.log"

echo "--- CURRENT MEMORY STATE ---"

echo "LAST_UPDATE=$(date)" >> "$MEMORY/state_memory.log"

echo "ASI MEMORY UPDATED"
