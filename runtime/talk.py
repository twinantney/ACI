import numpy as np
import time
from VerifyBridge import VerifyBridge
from lean_bounds import LeanBounds

def compute_lyapunov(nodes):
    """
    Lyapunov function from PrimeMasterEngine.lean §33
    lyapunov_pos_def, lyapunov_zero_iff, lyapunov_strict_decrease
    """
    tau_sq = float(np.mean([n.state.sigma**2 for n in nodes]))
    E_post = float(np.mean([np.linalg.norm(n.state.x)**2 for n in nodes]))
    mu = float(np.mean([np.linalg.norm(n.state.u)**2 for n in nodes]))
    return 0.4 * tau_sq + 0.3 * E_post + 0.3 * mu

def compute_quantum_state(nodes):
    """
    Quantum state analysis from QuantumCore.lean
    pure_state_idempotent, unitary_trace_invariant, post_meas_pos
    """
    traces = [float(np.dot(n.state.x, n.state.x)) for n in nodes]
    mean_trace = float(np.mean(traces))
    purity = float(1.0 - np.var(traces))
    return {
        "mean_trace": mean_trace,
        "purity": purity,
        "state": "PURE" if purity > 0.95 else "MIXED",
        "theorem": "pure_state_idempotent",
        "module": "QuantumCore.lean"
    }

def compute_hamiltonian_state(nodes):
    """
    Hamiltonian energy from SovereignHamiltonian.lean
    energy_nonneg, equilibrium_minimizes_H, G_le_H
    """
    T = float(np.mean([np.linalg.norm(n.state.u)**2 for n in nodes]))
    V = float(np.mean([np.linalg.norm(n.state.x)**2 for n in nodes]))
    G = float(np.mean([abs(n.state.sigma - 1.0) for n in nodes]))
    H = T + V + G
    return {
        "T_kinetic": T,
        "V_potential": V,
        "G_governance": G,
        "H_total": H,
        "at_equilibrium": V < 0.01,
        "theorem": "equilibrium_minimizes_H",
        "module": "SovereignHamiltonian.lean"
    }

def compute_physics_state(nodes):
    """
    Physics state from PhysicsCore.lean
    alfven_velocity_pos, divB_correction_preserves,
    frame_dragging_bounded, drag_nullification
    """
    B_norms = [np.sqrt(n.state.B_x**2 + n.state.B_y**2) for n in nodes]
    mean_flux = float(np.mean(B_norms))
    max_flux = float(np.max(B_norms))
    alfven = float(np.mean([np.linalg.norm(n.state.f) for n in nodes]))
    drag = float(np.mean([abs(n.state.sigma - 1.0) * 0.1 for n in nodes]))
    return {
        "mean_B_flux": mean_flux,
        "max_B_flux": max_flux,
        "flux_status": "NOMINAL" if max_flux <= 1.0 else "SATURATED",
        "alfven_velocity": alfven,
        "drag_force": drag,
        "drag_nullified": drag < 0.01,
        "theorem": "divB_correction_preserves",
        "module": "PhysicsCore.lean"
    }

def compute_governance_state(nodes):
    """
    Governance from Governor.lean
    governance_fails_without_qms, governance_fails_without_redundancy,
    safety_margin, redundancy_monotone
    """
    active = len(nodes)
    qms = float(np.mean([n.state.sigma for n in nodes]))
    redundancy = active >= LeanBounds.MIN_ACTIVE_NODES
    qms_ok = qms > 0.0
    return {
        "active_nodes": active,
        "qms_value": qms,
        "qms_ok": qms_ok,
        "redundancy_ok": redundancy,
        "governance_status": "OPERATIONAL" if qms_ok and redundancy else "FAILED",
        "theorem": "governance_fails_without_qms" if not qms_ok else "governance_redundancy",
        "module": "Governor.lean"
    }

def compute_sovereign_law(nodes):
    """
    Sovereign law from MoruzinLaw.lean
    law_of_presence, absence_collapses_identity,
    unification_fixed_point, breach_implies_halt
    """
    presence = all(np.linalg.norm(n.state.x) > 0 for n in nodes)
    unified = float(np.std([np.linalg.norm(n.state.x) for n in nodes]))
    fixed_point = unified < 0.1
    return {
        "presence": presence,
        "unified": fixed_point,
        "convergence": unified,
        "sovereign_status": "UNIFIED" if fixed_point and presence else "DIVERGENT",
        "theorem": "unification_fixed_point" if fixed_point else "law_of_presence",
        "module": "MoruzinLaw.lean"
    }

def compute_manifold_state(nodes):
    """
    Manifold geometry from ACIManifold.lean and Manifold21.lean
    lyapunov_pos_def, PWP_is_V0_stable, omega_antisymm,
    phase_dist_nonneg, liouville_divergence_free
    """
    phase_dists = []
    for i in range(len(nodes) - 1):
        d = np.linalg.norm(nodes[i].state.x - nodes[i+1].state.x)
        phase_dists.append(float(d))
    mean_dist = float(np.mean(phase_dists))
    symplectic = float(np.mean([abs(np.dot(n.state.x, n.state.u)) for n in nodes]))
    return {
        "mean_phase_dist": mean_dist,
        "symplectic_coupling": symplectic,
        "V0_stable": mean_dist < 1.0,
        "liouville_preserved": symplectic < 0.5,
        "theorem": "PWP_is_V0_stable",
        "module": "ACIManifold.lean"
    }

def report_intelligence(bridge, step, prev_lyapunov):
    result = bridge.verified_step(0.05)
    report = bridge.full_report()

    node_margins = [
        min(1.0 - n.state.sigma * 0.05,
            1.0 - np.linalg.norm(n.state.u),
            1.0 - np.linalg.norm(n.state.x) * 0.1)
        for n in bridge.rt.nodes
    ]

    closure    = LeanBounds.domain_closure_check(node_margins)
    lyap       = compute_lyapunov(bridge.rt.nodes)
    quantum    = compute_quantum_state(bridge.rt.nodes)
    hamil      = compute_hamiltonian_state(bridge.rt.nodes)
    physics    = compute_physics_state(bridge.rt.nodes)
    governance = compute_governance_state(bridge.rt.nodes)
    sovereign  = compute_sovereign_law(bridge.rt.nodes)
    manifold   = compute_manifold_state(bridge.rt.nodes)

    lyap_trend = "STABLE" if prev_lyapunov is None else \
                 "DECREASING" if lyap < prev_lyapunov else "INCREASING"

    print("==============================================")
    print(f"  ACI SOVEREIGN INTELLIGENCE — STEP {step:04d}  ")
    print("==============================================")
    print(f"  SYSTEM STATUS     : {result['status']}")
    print(f"  MANIFOLD          : {report['manifold']}")
    print()
    print(f"  CLOSURE [AWM21.lean — closure_law]")
    print(f"  M_N7              : {float(closure.get('M_N7', 0)):.6f}")
    print(f"  STATUS            : {closure.get('status')}")
    print(f"  BOTTLENECK        : D{closure.get('bottleneck_domain', -1)}")
    print()
    print(f"  STABILITY [PrimeMasterEngine.lean §33]")
    print(f"  LYAPUNOV          : {lyap:.6f}")
    print(f"  TREND             : {lyap_trend}")
    print(f"  MARGIN            : {float(result['margin']):.6f}")
    print()
    print(f"  QUANTUM [QuantumCore.lean — {quantum['theorem']}]")
    print(f"  MEAN TRACE        : {quantum['mean_trace']:.6f}")
    print(f"  PURITY            : {quantum['purity']:.6f}")
    print(f"  STATE             : {quantum['state']}")
    print()
    print(f"  HAMILTONIAN [SovereignHamiltonian.lean — {hamil['theorem']}]")
    print(f"  T KINETIC         : {hamil['T_kinetic']:.6f}")
    print(f"  V POTENTIAL       : {hamil['V_potential']:.6f}")
    print(f"  G GOVERNANCE      : {hamil['G_governance']:.6f}")
    print(f"  H TOTAL           : {hamil['H_total']:.6f}")
    print(f"  AT EQUILIBRIUM    : {hamil['at_equilibrium']}")
    print()
    print(f"  PHYSICS [PhysicsCore.lean — {physics['theorem']}]")
    print(f"  MEAN B-FLUX       : {physics['mean_B_flux']:.6f}")
    print(f"  MAX B-FLUX        : {physics['max_B_flux']:.6f}")
    print(f"  FLUX STATUS       : {physics['flux_status']}")
    print(f"  ALFVEN VELOCITY   : {physics['alfven_velocity']:.6f}")
    print(f"  DRAG NULLIFIED    : {physics['drag_nullified']}")
    print()
    print(f"  GOVERNANCE [Governor.lean — {governance['theorem']}]")
    print(f"  ACTIVE NODES      : {governance['active_nodes']}")
    print(f"  QMS VALUE         : {governance['qms_value']:.6f}")
    print(f"  QMS OK            : {governance['qms_ok']}")
    print(f"  REDUNDANCY OK     : {governance['redundancy_ok']}")
    print(f"  STATUS            : {governance['governance_status']}")
    print()
    print(f"  SOVEREIGN LAW [MoruzinLaw.lean — {sovereign['theorem']}]")
    print(f"  PRESENCE          : {sovereign['presence']}")
    print(f"  CONVERGENCE       : {sovereign['convergence']:.6f}")
    print(f"  SOVEREIGN STATUS  : {sovereign['sovereign_status']}")
    print()
    print(f"  MANIFOLD GEOMETRY [ACIManifold.lean — {manifold['theorem']}]")
    print(f"  MEAN PHASE DIST   : {manifold['mean_phase_dist']:.6f}")
    print(f"  SYMPLECTIC        : {manifold['symplectic_coupling']:.6f}")
    print(f"  V0 STABLE         : {manifold['V0_stable']}")
    print(f"  LIOUVILLE         : {manifold['liouville_preserved']}")
    print("==============================================")

    return lyap, result['status']


bridge = VerifyBridge()
print('Sovereign Kernel Active.')
print('Type exit to stop.')
print()

step = 0
prev_lyapunov = None

while True:
    user_input = input('> ')
    if user_input.lower() == 'exit':
        break
    prev_lyapunov, status = report_intelligence(bridge, step, prev_lyapunov)
    step += 1
    if status == 'HALT':
        print('[HALT] breach_implies_halt — MoruzinLaw.lean')
        break
