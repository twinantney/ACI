from Governor import submit_task

task = {
    "type": "LeanProof",
    "payload": {"proof_module": "MainTheorem"}
}

print(f"Result: {submit_task(task)}")

