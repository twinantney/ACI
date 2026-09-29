def diagnose_spring_timescale(spring_k=0.1, mass=1.0, dt=0.05, steps=200,
                                initial_displacement=15.0):
    """Diagnostic only — no runtime behavior changes. Directly computes
    whether the given spring_k/dt/steps combination is even
    mathematically capable of closing the adversarial test's initial
    displacement, using the same linearized spring-mass update the
    actual Dynamics.step performs (ignoring policy/noise/coupling terms,
    which are secondary to this specific question). This answers
    definitively whether the last two rounds' failure to recover was a
    tuning problem (spring_k too small for this dt/steps budget) or
    something structurally deeper, before writing any further fix."""
    x = initial_displacement
    p = 0.0
    trajectory = [x]
    for _ in range(steps):
        spring_force = -spring_k * x
        p = p + dt * spring_force
        x = x + dt * (p / mass)
        trajectory.append(x)
    return {
        "spring_k": spring_k,
        "dt": dt,
        "steps": steps,
        "initial_displacement": initial_displacement,
        "final_displacement": trajectory[-1],
        "closed_the_gap": abs(trajectory[-1]) < 1.0,
        "trajectory_sample": [round(v, 4) for v in trajectory[::20]],
    }


if __name__ == "__main__":
    print("=== SPRING TIMESCALE DIAGNOSTIC (isolated, before any runtime change) ===")
    current_config = diagnose_spring_timescale()
    print(f"Current config (spring_k=0.1): {current_config}")

    print("\n=== SAME DIAGNOSTIC WITH STRONGER SPRING_K CANDIDATES ===")
    for candidate_k in [0.5, 1.0, 2.0, 5.0]:
        result = diagnose_spring_timescale(spring_k=candidate_k)
        print(f"spring_k={candidate_k}: closed_the_gap={result['closed_the_gap']}, "
              f"final_displacement={result['final_displacement']:.4f}")
