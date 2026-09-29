import json
import sys
import numpy as np
from lean_bounds import LeanBounds
from PrimeRuntimeV4_backup import PrimeRuntimeV4
import json

class VerifyBridge:
    def __init__(self):
        self.rt = PrimeRuntimeV4()
        self.lean_module = "VerifyState"
        self.obligations = []
        self.results = {}

    def export_obligation(self, name: str, claim: str) -> dict:
        obligation = {
            "name": name,
            "claim": claim,
            "runtime_state": self.rt.manifold_state,
            "integrity": self.rt.verify_all()
        }
        self.obligations.append(obligation)
        return obligation

    def export_to_json(self, path: str = "obligations.json"):
        with open(path, "w") as f:
            json.dump(self.obligations, f, indent=2)
        return f"EXPORTED:{len(self.obligations)}_OBLIGATIONS->{path}"

    def read_lean_result(self, path: str = "all_verified_runs.json") -> dict:
        try:
            with open(path) as f:
                self.results = json.load(f)
            return self.results
        except FileNotFoundError:
            return {"status": "LEAN_RESULTS_NOT_FOUND"}

    def verify_state(self) -> str:
        report_str = self.rt.verify_all()
        if "STATUS:HALT" in report_str:
            return "BRIDGE:RUNTIME_FAULT"
        return "BRIDGE:RUNTIME_VERIFIED_AWAITING_LEAN"

    def full_report(self) -> dict:
        report_str = self.rt.verify_all()
        return {
            "runtime": report_str,
            "manifold": self.rt.manifold_state,
            "obligations": len(self.obligations),
            "lean_results": self.results
        }

    def talk(self, user_input: str) -> str:
        thought_process = self.rt.run_recursive_thought(complexity_depth=3)
        response = self.rt.run_inference(user_input)
        return f"SYSTEM_THOUGHT: {thought_process}\nSYSTEM_RESPONSE: {response}"

    def verified_step(self, dt):
        margin = self.rt.step(dt)
        validation = LeanBounds.validate_margin(margin)

        if validation['status'] == 'BREACH':
            return {
                "status": "HALT",
                "reason": "breach_implies_halt",
                "module": "MoruzinLaw.lean",
                "margin": margin
            }

        if validation['status'] == 'DEGRADED':
            return {
                "status": "DEGRADED",
                "lean_build": "CI_ONLY",
                "margin": margin
            }

        return {
            "status": "STABLE",
            "margin": margin
        }

