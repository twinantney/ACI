import json
import os
import sys

def isolate_initial_veto_node(file_path="production_intelligence_metrics.json"):
    print("==========================================================================")
    print("      INITIALIZING MULTI-DOMAIN TELEMETRY CRITICAL VETO PARSER            ")
    print("==========================================================================")

    if not os.path.exists(file_path):
        print(f"[ERROR] Telemetry dataset '{file_path}' absent from local directory.")
        sys.exit(1)

    with open(file_path, "r") as f:
        try:
            data = json.load(f)
        except json.JSONDecodeError:
            print("[ERROR] Corrupted JSON matrix format detected inside metrics log.")
            sys.exit(1)

    history = data.get("evolution_history", [])
    if not history:
        print("[ERROR] Evolution history array empty or unpopulated.")
        sys.exit(1)

    # Chronologically loop step-by-step through the 10,000 evolutionary processing cycles
    for record in history:
        step = record.get("iteration", 0)
        slices = record.get("node_telemetry_slices", [])

        for slice_data in slices:
            node_id = slice_data.get("node_id", -1)
            margin = float(slice_data.get("local_margin", 1.0))

            # Isolate the exact instant a node margin breaches the formal safety floor threshold
            if margin < 0.05:
                print(f"[BREACH DETECTED] Processing Cycle Milestone: {step:05d}")
                print(f" -> Failed Bottleneck Domain ID : Node [{node_id}]")
                print(f" -> Localized Margin Value      : {margin:.6f}")
                print("--------------------------------------------------------------------------")
                print("[SUCCESS] ABSOLUTE THREAT INTERCEPT POINT IDENTIFIED.")
                print("==========================================================================")
                return

    print("[INFO] Review complete: No discrete node local margin breached the safety floor.")
    print("==========================================================================")

if __name__ == "__main__":
    isolate_initial_veto_node()

