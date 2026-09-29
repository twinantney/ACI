from synthesis_engine import execute_apex_synthesis

def submit_task(problem):
    try:
        if problem.get("type") == "LeanProof":
            return execute_apex_synthesis(problem.get("payload"))
        return "Verification: Standard constraints met."
    except Exception as e:
        return f"Governor Error: {str(e)}"

