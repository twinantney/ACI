import time
import numpy as np
from VerifyBridge import VerifyBridge
from lean_bounds import LeanBounds

def compute_lyapunov(nodes):
    """
    Computes Lyapunov value from node states.
    Corresponds to lyapunov_zero_iff, lyapunov_strict_decrease
    in PrimeMasterEngine.lean — Section 33.
    tau_sq = mean sigma, E_post = mean energy, mu = mean perturbation
    """
    tau_sq = float(np.mean([n.state.sigma**2 for n in nodes]))
    E_post = float(np.mean([np.linalg.norm(n.state.x)**2 for n in nodes]))
    mu = float(np.mean([np.linalg.norm(n.state.u)**2 for n in nodes]))
    return 0.4 * tau_sq + 0.3 * E_post + 0.3 * mu

def run_aci(steps=100, dt=0.05, delay=0.0):
    vb = VerifyBridge()
    prev_lyapunov = None

    print("==============================================")
    print("       ACI SOVEREIGN RUNTIME — ACTIVE        ")
    print("==============================================")

    for step in range(steps):
        result = vb.verified_step(dt)
        status = result['status']
        margin = float(result['margin'])

        # Domain-level margin tracking
        node_margins = [
            min(1.0 - n.state.sigma * 0.05,
                1.0 - np.linalg.norm(n.state.u),
                1.0 - np.linalg.norm(n.state.x) * 0.1)
            for n in vb.rt.nodes
        ]
        closure = LeanBounds.domain_closure_check(node_margins)
        bottleneck = closure.get('bottleneck_domain', -1)
        M_N7 = float(closure.get('M_N7', 0.0))

        # Lyapunov tracking
        lyap = compute_lyapunov(vb.rt.nodes)
        lyap_status = "DECREASING" if prev_lyapunov is None else \
                      "DECREASING" if lyap < prev_lyapunov else "INCREASING"
        prev_lyapunov = lyap

        print(f"[{step:04d}] STATUS:{status} MARGIN:{margin:.6f} "
              f"M_N7:{M_N7:.6f} BOTTLENECK:D{bottleneck} "
              f"LYAPUNOV:{lyap:.6f} L_TREND:{lyap_status}")

        if status == 'HALT':
            print(f"[HALT] breach_implies_halt — MoruzinLaw.lean")
            print(f"[HALT] System stopped at step {step}")
            break

        if delay > 0:
            time.sleep(delay)

    print("==============================================")
    print(f"FINAL: {vb.full_report()}")
    print("==============================================")

if __name__ == "__main__":
    run_aci(steps=50, dt=0.05)
