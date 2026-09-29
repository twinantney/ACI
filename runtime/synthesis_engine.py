import subprocess
import os

def run_lean_proof(module_name):
    """
    Verifies a Lean module directly from the project root,
    using the existing lake build cache (lake-manifest.json,
    .lake build artifacts) instead of an isolated copy.
    This avoids redundant Mathlib re-elaboration and the
    associated memory spike of checking a file outside the
    project's build graph.
    """
    file_path = f"{module_name}.lean"
    full_path = os.path.join("/root/my_project", file_path)

    if not os.path.exists(full_path):
        return False, f"Module not found: {full_path}"

    # lake env lean uses the project's existing environment
    # (Mathlib cache, lake-manifest) instead of cold-starting
    cmd = ["lake", "env", "lean", file_path]

    try:
        result = subprocess.run(
            cmd,
            cwd="/root/my_project",
            capture_output=True,
            text=True,
            check=True,
            timeout=300,
        )
        return True, result.stdout
    except subprocess.CalledProcessError as e:
        return False, e.stderr
    except subprocess.TimeoutExpired:
        return False, "Verification timed out after 300s"

def execute_apex_synthesis(payload):
    proof_target = payload.get("proof_module")
    success, output = run_lean_proof(proof_target)

    if success:
        return f"LEAN_VERIFIED: {proof_target} compiled successfully."
    else:
        return f"LEAN_REJECTED: {output}"
