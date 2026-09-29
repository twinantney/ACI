import json
import sys

def audit_json_receipt():
    print("📋 OPENING APEX INTEGRATION RECEIPT...\n")
    try:
        with open("at5_closure_log.json", "r") as f:
            data = json.load(f)
            
        print("--- ARTIFACT STRUCTURE ---")
        print(json.dumps(data, indent=4))
        print("--------------------------")
        
        if data.get("apex_status") == "CERTIFIED" and data.get("closure_check_passed"):
            print("\n🟢 VERIFICATION: Artifact structure is structurally valid and fully certified.")
        else:
            print("\n⚠️ WARNING: Status fields do not indicate clear apex certification.")
            
    except FileNotFoundError:
        print("❌ ERROR: at5_closure_log.json not found in the current directory.")
        sys.exit(1)
    except json.JSONDecodeError:
        print("❌ CRITICAL: at5_closure_log.json contains corrupted/malformed syntax.")
        sys.exit(1)

if __name__ == "__main__":
    audit_json_receipt()

