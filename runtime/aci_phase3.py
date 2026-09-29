import os
import json
import datetime
import subprocess

class ApexIntelligenceEngine:
    def __init__(self, state_file="aci_knowledge_state.json", project_dir="."):
        self.state_file = state_file
        self.project_dir = project_dir
        self.knowledge_state = self.load_knowledge_state()

    def load_knowledge_state(self):
        """Loads or initializes the tracking state configuration."""
        if os.path.exists(self.state_file):
            try:
                with open(self.state_file, 'r') as f:
                    return json.load(f)
            except json.JSONDecodeError:
                print("[!] Error reading state file. Corrupted JSON.")
                return self.get_default_state()
        else:
            return self.get_default_state()

    def get_default_state(self):
        """Generates fallback environment telemetry data metadata."""
        return {
            "system_status": "INITIALIZED",
            "phase": "PHASE_3_INTEGRATION",
            "last_updated": str(datetime.datetime.now()),
            "verified_proofs": [],
            "pending_verification": []
        }

    def save_knowledge_state(self):
        """Persists the tracking matrix back to disk."""
        self.knowledge_state["last_updated"] = str(datetime.datetime.now())
        with open(self.state_file, 'w') as f:
            json.dump(self.knowledge_state, f, indent=4)
        print("[+] Knowledge state successfully committed.")

    def run_lean_verification(self):
        """Runs full lake build against the entire ACI system."""
        print("[*] Running full lake build...")
        try:
            result = subprocess.run(
                ["lake", "build"],
                capture_output=True, text=True, check=False,
                cwd=self.project_dir
            )
            if result.returncode == 0:
                print("[+] Full system build successful.")
                return True
            else:
                print("[-] Build failed:")
                print(result.stderr if result.stderr else result.stdout)
                return False
        except FileNotFoundError:
            print("[!] lake toolchain not found.")
            return False

    def execute_intelligence_loop(self):
        """Executes main architectural processing steps."""
        print("==============================================")
        print("    ACI APEX INTELLIGENCE SYSTEM - PHASE 3   ")
        print("==============================================")
        print(f"Current Phase Status: {self.knowledge_state['system_status']}")
        # Verify active math environment assets
        verified = self.run_lean_verification()
        if verified:
            self.knowledge_state["system_status"] = "VERIFIED_OPERATIONAL"
        else:
            self.knowledge_state["system_status"] = "SYNTAX_DEGRADATION"
        self.save_knowledge_state()
        print("==============================================")

if __name__ == "__main__":
    # Launch system core target engine inside active execution block
    engine = ApexIntelligenceEngine()
    engine.execute_intelligence_loop()
