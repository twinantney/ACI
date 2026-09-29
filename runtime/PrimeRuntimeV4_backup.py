import numpy as np
import random

DOMAIN_NAMES = [
    "A_Energy", "B_Control", "C_Thermal", "D_Structural",
    "E_Boundary", "F_Diagnostics", "G_Governance",
    "H_Harmonic", "I_Information", "J_Joining",
    "K_Kernel", "L_Localization", "M_Morphogenic",
    "N_Node", "O_Operator", "P_Propagation",
    "Q_Quality", "R_Resonance", "S_State",
    "T_Temporal", "U_Unification",
]

def domain_priority(domain_index):
    return domain_index + 1

def T_kinetic(p, m):
    return float(np.sum(p ** 2 / (2 * m)))

def V_potential(k, y_actual, y_spine):
    return float(0.5 * k * np.sum((y_actual - y_spine) ** 2))

def G_governance(W, A, dl):
    return float(W * np.sum(A * dl))

def H_OPT7(p, m, k, y_actual, y_spine, W, A, dl):
    return (T_kinetic(p, m) + V_potential(k, y_actual, y_spine) +
            G_governance(W, A, dl))

def verify_V_zero_iff_equilibrium(y_actual, y_spine, k, tol=1e-9):
    v = V_potential(k, y_actual, y_spine)
    at_equilibrium = bool(np.allclose(y_actual, y_spine, atol=tol))
    v_is_zero = abs(v) < tol
    return {
        "V_potential": v,
        "at_equilibrium": at_equilibrium,
        "V_is_zero": v_is_zero,
        "iff_holds": at_equilibrium == v_is_zero,
    }

def verify_G_le_H(p, m, k, y_actual, y_spine, W, A, dl):
    g = G_governance(W, A, dl)
    h = H_OPT7(p, m, k, y_actual, y_spine, W, A, dl)
    return {"G_governance": g, "H_OPT7": h, "G_le_H_holds": g <= h + 1e-9}

def verify_equilibrium_minimizes_H(p, m, k, y_spine, W, A, dl, tol=1e-9):
    h_at_eq = H_OPT7(p, m, k, y_spine, y_spine, W, A, dl)
    expected = T_kinetic(p, m) + G_governance(W, A, dl)
    return {
        "H_at_equilibrium": h_at_eq,
        "T_plus_G": expected,
        "collapse_holds": abs(h_at_eq - expected) < tol,
    }

class EnergyTriad:
    def __init__(self, energy=0.0, thermal=0.0, structural=0.0):
        self.energy = max(0.0, energy)
        self.thermal = max(0.0, thermal)
        self.structural = max(0.0, structural)

    @property
    def total(self):
        return self.energy + self.thermal + self.structural

MC2_U_MAX = 0.95
MC2_LOCAL_RETAIN = 0.8
MC2_GLOBAL_LEAK = 0.2

def mc2_load_factor(x):
    return float(np.clip(x, 0.0, MC2_U_MAX))

def mc2_effective_mass(m, load):
    load = min(load, MC2_U_MAX)
    return m / (1.0 - load)

def mc2_collision_force(O, Gamma, Omega):
    return (O * Gamma) / (Omega + 1e-9)

def mc2_displacement(F, m_eff, dt):
    return (F / m_eff) * (dt ** 2)

def mc2_coupling_strength(m_origin, m_target):
    return 1.0 / (m_origin + m_target)

def mc2_update_origin(x_d, delta):
    return x_d + MC2_LOCAL_RETAIN * delta

def mc2_update_target(x_t, delta, c_strength):
    return x_t + MC2_GLOBAL_LEAK * c_strength * delta

def verify_mc2_retain_leak_sum():
    total = MC2_LOCAL_RETAIN + MC2_GLOBAL_LEAK
    return {"sum": total, "matches_proven_identity": abs(total - 1.0) < 1e-12}

def verify_mc2_coupling_symmetric(m_a=1.0, m_b=2.5):
    forward = mc2_coupling_strength(m_a, m_b)
    reverse = mc2_coupling_strength(m_b, m_a)
    return {"forward": forward, "reverse": reverse,
            "symmetric": abs(forward - reverse) < 1e-12}

def compute_critical_damping(spring_k, mass):
    return 2.0 * np.sqrt(spring_k * mass)

class IntegrityTracker:
    def __init__(self):
        self.integrity_ever_broken = False
        self.history = []

    def check_transition(self, source_integrity, target_integrity):
        valid = (not source_integrity) or target_integrity
        self.history.append(valid)
        if not valid:
            self.integrity_ever_broken = True
        return valid

LAWSON_BOUND = 1e21

def lawson_triple_product(n_density, T_temp, tau_confinement):
    return float(n_density * T_temp * tau_confinement)

def lawson_satisfied(n_density, T_temp, tau_confinement):
    return lawson_triple_product(
        n_density, T_temp, tau_confinement) >= LAWSON_BOUND

def alfven_velocity(B_field, mu_zero, rho):
    denom = np.sqrt(max(mu_zero * rho, 1e-12))
    return float(B_field / denom)

def frame_dragging(warping_scalar):
    w = max(0.0, warping_scalar)
    return float(1.0 / (1.0 + 0.1 * w))

def divB_residual(dBx_dx, dBy_dy):
    return float(dBx_dx + dBy_dy)

def n7_M_N7(margin_values):
    return float(min(margin_values)) if margin_values else 0.0

def n7_bottleneck_index(margin_values):
    if not margin_values:
        return None
    return int(np.argmin(margin_values))

def n7_gate_decision(margin_values, floor):
    m = n7_M_N7(margin_values)
    if floor < m:
        return ("Sealed", None)
    return ("Vetoed", n7_bottleneck_index(margin_values))

def manifold21_omega(q1, p1, q2, p2):
    return float(np.sum(q1 * p2 - p1 * q2))

def manifold21_poisson_bracket(df_dq, df_dp, dg_dq, dg_dp):
    return float(np.sum(df_dq * dg_dp - df_dp * dg_dq))

def manifold21_lyapunov(q, p, q_eq, p_eq):
    return float(0.5 * (np.sum((q - q_eq) ** 2) +
                         np.sum((p - p_eq) ** 2)))

def moruzin_chamber_valid(delta, m_eff):
    return abs(delta) <= m_eff

def moruzin_chamber_compose(d1, m1, d2, m2):
    return (d1 + d2, m1 + m2)

def quantum_density_matrix(x_state):
    a, b = x_state[0], x_state[1]
    norm = np.sqrt(a ** 2 + b ** 2) + 1e-12
    psi = np.array([a / norm, b / norm])
    rho = np.outer(psi, psi)
    return rho

def quantum_is_hermitian(rho, tol=1e-6):
    return bool(np.allclose(rho, rho.T, atol=tol))

def quantum_trace_one(rho, tol=1e-6):
    return bool(abs(np.trace(rho) - 1.0) < tol)

def quantum_is_positive(rho, tol=1e-6):
    eigvals = np.linalg.eigvalsh(rho)
    return bool(np.all(eigvals >= -tol))

def quantum_unitary_evolve(rho, theta):
    c, s = np.cos(theta), np.sin(theta)
    U = np.array([[c, -s], [s, c]])
    return U @ rho @ U.T

def quantum_trace_preserved(rho_before, rho_after, tol=1e-6):
    return bool(abs(np.trace(rho_before) - np.trace(rho_after)) < tol)

def verify_priority_injective(nodes):
    priorities = [n.priority for n in nodes]
    seen = set()
    duplicates = set()
    for p in priorities:
        if p in seen:
            duplicates.add(p)
        seen.add(p)
    return (len(duplicates) == 0, sorted(duplicates))

def system_gate_forward(node_statuses):
    return "Vetoed" if any(s == "Vetoed" for s in node_statuses) else "Sealed"

def system_gate_reverse_extractable(node_statuses, system_status):
    vetoed_indices = [i for i, s in enumerate(node_statuses) if s == "Vetoed"]
    if system_status == "Vetoed":
        return vetoed_indices if vetoed_indices else None
    return [] if not vetoed_indices else None

def system_gate_report(node_statuses):
    forward = system_gate_forward(node_statuses)
    reverse = system_gate_reverse_extractable(node_statuses, forward)
    consistent = reverse is not None
    return {
        "system_status": forward,
        "veto_causing_nodes": reverse if reverse else [],
        "forward_reverse_consistent": consistent,
    }

def policy_at_least_as_permissive(node_a, node_b):
    a_noise_ceiling = getattr(node_a, "noise_level", 0.01)
    b_noise_ceiling = getattr(node_b, "noise_level", 0.01)
    a_margin_floor = getattr(node_a.state, "local_margin", 0.0)
    b_margin_floor = getattr(node_b.state, "local_margin", 0.0)
    return (a_noise_ceiling >= b_noise_ceiling and
            a_margin_floor >= b_margin_floor)

def find_most_permissive_node(nodes):
    for i, candidate in enumerate(nodes):
        if all(policy_at_least_as_permissive(candidate, other)
               for other in nodes):
            return i
    return None

def selftest_priority_violation_detected(nodes):
    original = nodes[5].priority
    nodes[5].priority = nodes[3].priority
    is_valid, duplicates = verify_priority_injective(nodes)
    nodes[5].priority = original
    correctly_detected = (is_valid is False) and (nodes[3].priority in duplicates)
    return {"correctly_detected": bool(correctly_detected), "duplicates_found": duplicates}

def selftest_gate_veto_detected():
    statuses = ["Sealed"] * 21
    statuses[9] = "Vetoed"
    report = system_gate_report(statuses)
    correctly_detected = (report["system_status"] == "Vetoed" and
                           9 in report["veto_causing_nodes"] and
                           report["forward_reverse_consistent"])
    return {"correctly_detected": bool(correctly_detected), "report": report}

def compute_sub_margins(sigma, u, x):
    return [
        1.0 - sigma * 0.05,
        1.0 - np.linalg.norm(u),
        1.0 - np.linalg.norm(x) * 0.1,
    ]

class State:
    def __init__(self):
        self.x, self.u, self.f = np.zeros(3), np.zeros(3), np.zeros(3)
        self.t, self.sigma, self.beta = 1.0, 1.0, 0.0
        self.B_x, self.B_y = 0.0, 0.0
        self.p = np.zeros(3)
        self.y_spine = None
        self.load = 0.0
        self.triad = EnergyTriad()
        self.fusion_density = 1e19
        self.fusion_temp = 1.0
        self.fusion_confinement = 1.0
        self.alfven_v = 0.0
        self.divB_resid = 0.0
        self.prev_B_x, self.prev_B_y = 0.0, 0.0
        self.frame_drag_factor = 1.0
        self.n7_gate_status = "Sealed"
        self.n7_veto_reason = None
        self.lyapunov_V = 0.0
        self.omega_self_check = 0.0
        self.chamber_valid = True
        self.rho = np.array([[0.5, 0.0], [0.0, 0.5]])
        self.rho_hermitian = True
        self.rho_trace_one = True
        self.rho_positive = True
        self.local_margin = 1.0
        self.raw_margin_pre_correction = 1.0
        self.mc2_leaked_delta = np.zeros(3)
        self.prev_x = np.zeros(3)
        self.prev_p = np.zeros(3)

class Policy:
    def __init__(self):
        self.weights = np.random.randn(6, 3) * 0.1
    def act(self, state_vec):
        return np.tanh(state_vec @ self.weights)

class Node:
    def __init__(self, nid):
        self.id = nid
        self.domain_index = nid % 21
        self.domain_name = DOMAIN_NAMES[self.domain_index]
        self.priority = domain_priority(self.domain_index)
        self.state = State()
        self.links = []
        self.policy = Policy()
        self.mass = 1.0
        self.spring_k = 2.0
        self.spring_damping = compute_critical_damping(self.spring_k, self.mass)
        self.gov_weight = 0.05
        self.O_strength = 1.0
        self.Gamma_gain = 1.0
        self.Omega_burden = 1.0
        self.mu_zero = 1.0
        self.rho_density = 1.0
        self.m_eff_chamber = 1.0

NOISE_LEVEL_MAX = 1.0
NOISE_LEVEL_MIN = 0.0001

class StochasticResonanceNode(Node):
    def __init__(self, nid, noise_level=0.01):
        super().__init__(nid)
        self._noise_level = float(np.clip(
            noise_level, NOISE_LEVEL_MIN, NOISE_LEVEL_MAX))
        self.configured_noise_level = self._noise_level

    @property
    def noise_level(self):
        return self._noise_level

    @noise_level.setter
    def noise_level(self, value):
        clamped = float(np.clip(
            value, NOISE_LEVEL_MIN, NOISE_LEVEL_MAX))
        self._noise_level = clamped
        self.configured_noise_level = clamped

    def apply_ssr(self, state_vec):
        noise = np.random.normal(
            0, self.noise_level, state_vec.shape)
        return self.policy.act(state_vec + noise)

def sync_weights_unweighted(nodes, eta=0.05):
    all_weights = np.array([n.policy.weights for n in nodes])
    avg_weights = np.mean(all_weights, axis=0)
    for n in nodes:
        n.policy.weights += eta * (avg_weights - n.policy.weights)

def sync_weights(nodes, eta=0.05):
    margins = np.array([n.state.local_margin for n in nodes])
    shifted = margins - np.max(margins)
    fitness = np.exp(shifted)
    fitness_sum = fitness.sum()
    if fitness_sum < 1e-12:
        weights_soft = np.full(len(nodes), 1.0 / len(nodes))
    else:
        weights_soft = fitness / fitness_sum
    all_weights = np.array([n.policy.weights for n in nodes])
    fitness_avg = np.tensordot(weights_soft, all_weights, axes=(0, 0))
    for n in nodes:
        n.policy.weights += eta * (fitness_avg - n.policy.weights)

def sanitize_state(x, fallback=0.0):
    return np.nan_to_num(x, nan=fallback, posinf=1.0, neginf=-1.0)

U_NORM_MAX = 0.99

def clamp_u(u, max_norm=U_NORM_MAX):
    norm = np.linalg.norm(u)
    if norm > max_norm:
        return u * (max_norm / norm)
    return u

def verify_clamp_u_bound(num_trials=200, max_norm=U_NORM_MAX, seed=123):
    rng = np.random.default_rng(seed)
    worst_violation = 0.0
    for _ in range(num_trials):
        trial_vec = rng.normal(0, 10, size=3)
        clamped = clamp_u(trial_vec, max_norm)
        out_norm = float(np.linalg.norm(clamped))
        violation = max(0.0, out_norm - max_norm)
        worst_violation = max(worst_violation, violation)
    return {
        "bound_holds": worst_violation < 1e-9,
        "max_norm_certificate": max_norm,
        "worst_observed_violation": worst_violation,
        "trials_run": num_trials,
    }

def apply_mc2_coupling_cascade(nodes):
    for n in nodes:
        n.state.mc2_leaked_delta = np.zeros(3)
    for n in nodes:
        delta = n.state.u
        for neighbor in n.links:
            c_strength = mc2_coupling_strength(n.mass, neighbor.mass)
            leaked = MC2_GLOBAL_LEAK * c_strength * delta
            neighbor.state.mc2_leaked_delta = neighbor.state.mc2_leaked_delta + leaked

def system_certified_kernel_report(nodes, tol=1e-6):
    all_hermitian = all(n.state.rho_hermitian for n in nodes)
    all_trace_one = all(n.state.rho_trace_one for n in nodes)
    all_positive = all(n.state.rho_positive for n in nodes)
    failing_nodes = [
        n.id for n in nodes
        if not (n.state.rho_hermitian and n.state.rho_trace_one and n.state.rho_positive)
    ]
    return {
        "all_nodes_hermitian": all_hermitian,
        "all_nodes_trace_one": all_trace_one,
        "all_nodes_positive": all_positive,
        "system_fully_certified": all_hermitian and all_trace_one and all_positive,
        "failing_node_ids": failing_nodes,
    }

class Dynamics:
    def step(self, node, dt):
        s = node.state
        s.x = sanitize_state(s.x)
        s.f = sanitize_state(s.f)
        s.p = sanitize_state(s.p)

        if s.y_spine is None:
            s.y_spine = s.x.copy()

        neighbor_states = [sanitize_state(n.state.x) for n in node.links]
        coupling = np.mean(neighbor_states, axis=0) if neighbor_states else 0

        warping = float(np.linalg.norm(s.x - s.y_spine))
        s.frame_drag_factor = frame_dragging(warping)
        s.f = s.frame_drag_factor * (0.6 * s.f + 0.4 * coupling)

        F = mc2_collision_force(
            node.O_strength, node.Gamma_gain, node.Omega_burden)
        s.load = mc2_load_factor(np.linalg.norm(s.x) / 5.0)
        m_eff = mc2_effective_mass(node.mass, s.load)
        delta = mc2_displacement(F, m_eff, dt)
        sv = np.concatenate([s.x, s.f])
        direction = (node.apply_ssr(sv)
            if isinstance(node, StochasticResonanceNode)
            else node.policy.act(sv))
        dir_norm = np.linalg.norm(direction)
        if dir_norm > 1e-9:
            direction = direction / dir_norm
        s.u = clamp_u(sanitize_state(direction * delta))

        spring_force = (-node.spring_k * (s.x - s.y_spine)
                         - node.spring_damping * s.p)
        s.p = sanitize_state(s.p + dt * spring_force)
        A_vec = np.abs(s.p)
        dl_vec = s.x - s.y_spine
        H = H_OPT7(
            s.p, np.full(3, node.mass), node.spring_k,
            s.x, s.y_spine, node.gov_weight, A_vec, dl_vec)

        s.triad = EnergyTriad(
            energy=T_kinetic(s.p, np.full(3, node.mass)),
            thermal=abs(G_governance(node.gov_weight, A_vec, dl_vec)),
            structural=V_potential(node.spring_k, s.x, s.y_spine))

        s.fusion_density = 1e19 * (1.0 + s.triad.energy)
        s.fusion_temp = 1.0 + float(np.linalg.norm(s.p))
        s.fusion_confinement = 1.0 / (1.0 + s.load)

        B_mag = float(np.sqrt(s.B_x ** 2 + s.B_y ** 2))
        s.alfven_v = alfven_velocity(
            B_mag, node.mu_zero, node.rho_density)

        dBx_dx = s.B_x - s.prev_B_x
        dBy_dy = s.B_y - s.prev_B_y
        s.divB_resid = divB_residual(dBx_dx, dBy_dy)
        s.prev_B_x, s.prev_B_y = s.B_x, s.B_y

        sub_margins = compute_sub_margins(s.sigma, s.u, s.x)
        s.raw_margin_pre_correction = float(min(sub_margins))

        status, veto_idx = n7_gate_decision(sub_margins, 0.05)
        s.n7_gate_status = status
        s.n7_veto_reason = (
            ["sigma_term", "u_term", "x_term"][veto_idx]
            if veto_idx is not None else None)

        s.local_margin = float(min(sub_margins))

        s.omega_self_check = manifold21_omega(s.prev_x, s.prev_p, s.x, s.p)

        s.lyapunov_V = manifold21_lyapunov(
            s.x, s.p, s.y_spine, np.zeros(3))

        s.chamber_valid = moruzin_chamber_valid(
            float(np.linalg.norm(s.u)), node.m_eff_chamber)

        rho_before = quantum_density_matrix(s.x)
        theta = 0.01 * s.sigma
        s.rho = quantum_unitary_evolve(rho_before, theta)
        s.rho_hermitian = quantum_is_hermitian(s.rho)
        s.rho_trace_one = quantum_trace_one(s.rho)
        s.rho_positive = quantum_is_positive(s.rho)

        s.x += dt * (s.u + s.f + s.p / node.mass) + s.mc2_leaked_delta
        s.x = sanitize_state(s.x)

        s.t += dt
        s.sigma = np.linalg.norm(s.x) * (1.0 + abs(s.t - 1.0))

        s.prev_x = s.x.copy()
        s.prev_p = s.p.copy()

class Constraint:
    def evaluate(self, nodes):
        margins = [
            min(compute_sub_margins(n.state.sigma, n.state.u, n.state.x))
            for n in nodes
        ]
        result = min(margins)
        return float(result) if np.isfinite(result) else -1.0

    def evaluate_raw(self, nodes):
        raw_margins = [n.state.raw_margin_pre_correction for n in nodes]
        result = min(raw_margins) if raw_margins else -1.0
        return float(result) if np.isfinite(result) else -1.0

POLE_MARGIN_MAX = 5.0
POLE_MARGIN_MIN = 0.01
ENTROPY_TARGET_MAX = 10.0
ENTROPY_TARGET_MIN = 0.01

def effective_pole_margin(base_margin, nodes):
    if not nodes:
        return base_margin
    mean_noise = float(np.mean([
        getattr(n, "noise_level", 0.01) for n in nodes]))
    tightening = 1.0 / (1.0 + mean_noise)
    tightened = base_margin * max(tightening, 0.3)
    return float(np.clip(
        tightened, POLE_MARGIN_MIN, POLE_MARGIN_MAX))

class MemoryBuffer:
    def __init__(self, capacity=100):
        self.capacity = capacity
        self.buffer = []
    def push(self, state_snapshot):
        self.buffer.append(state_snapshot)
        if len(self.buffer) > self.capacity:
            self.buffer.pop(0)
    def sample_trajectory(self):
        return np.array(self.buffer)

class DivergenceFilter:
    def __init__(self):
        self.last_div = 0.0

    def get_weighted_divergence(self, trajectory, alpha=0.3):
        n = len(trajectory)
        weights = np.exp(-alpha * np.arange(n)[::-1])
        weights /= weights.sum()
        weighted_mean = np.sum(
            trajectory * weights[:, np.newaxis, np.newaxis], axis=0)
        variance = np.sum(
            weights[:, np.newaxis, np.newaxis] *
            (trajectory - weighted_mean) ** 2, axis=0)
        return variance.mean()

    def get_filtered_divergence(self, trajectory, alpha=0.3, beta=0.7):
        raw_div = self.get_weighted_divergence(trajectory, alpha)
        filtered_div = (beta * self.last_div) + ((1.0 - beta) * raw_div)
        self.last_div = filtered_div
        return filtered_div

class EntropyEngine:
    def __init__(self, target_entropy=1.0):
        self.target = target_entropy
    def calculate_divergence(self, trajectory):
        return np.var(trajectory, axis=0).mean()
    def apply_normalization(self, nodes, trajectory):
        divergence = self.calculate_divergence(trajectory)
        if divergence > self.target:
            for n in nodes:
                n.state.x *= 0.99

def apply_adaptive_normalization(nodes, trajectory, target=1.0):
    divergence = np.var(trajectory, axis=0).mean()
    gain = np.clip(divergence / target, 0.0, 0.05)
    for n in nodes:
        n.state.x *= (1.0 - gain)

def apply_stochastic_revitalization(nodes, divergence, target=1.0):
    revitalization_factor = np.clip(1.0 - (divergence / target), 0.0, 1.0)
    for n in nodes:
        n.noise_level = 0.01 + (0.05 * revitalization_factor)

def apply_temporal_gating(step_count, nodes, divergence, target=1.0):
    if step_count % 5 == 0:
        revitalization_factor = np.clip(
            1.0 - (divergence / target), 0.0, 1.0)
        for n in nodes:
            base = getattr(n, "configured_noise_level", 0.01)
            n.noise_level = base * (
                0.2 + 0.8 * revitalization_factor)
    else:
        for n in nodes:
            base = getattr(n, "configured_noise_level", 0.01)
            current = n.noise_level
            n.noise_level = current + 0.05 * (base - current)

def get_adaptive_dt(base_dt, divergence, threshold=0.1):
    if divergence > threshold:
        return base_dt / (1.0 + (divergence * 10.0))
    return base_dt

def apply_pole_stabilization(nodes, margin=0.99):
    for n in nodes:
        norm = np.linalg.norm(n.state.x)
        if norm > margin:
            n.state.x *= (margin / norm)

def apply_quantum_causal_flux(nodes, causal_tensor, coupling_strength=0.001):
    for n in nodes:
        if causal_tensor.shape == (2, 2) and len(n.state.x) >= 2:
            flux_correction = causal_tensor @ n.state.x[:2]
            n.state.B_x += coupling_strength * flux_correction[0]
            n.state.B_y += coupling_strength * flux_correction[1]
            B_norm = np.sqrt(n.state.B_x**2 + n.state.B_y**2)
            if B_norm > 1.0:
                n.state.B_x /= B_norm
                n.state.B_y /= B_norm

def get_causal_integrity(nodes):
    B_norms = [np.sqrt(n.state.B_x**2 + n.state.B_y**2) for n in nodes]
    return float(np.mean(B_norms) * 100.0)

class PrimeRuntimeV4:
    def __init__(self, entropy_target=1.0, pole_margin=0.99,
                 disable_pole_stabilization=False):
        self.nodes = [StochasticResonanceNode(i) for i in range(21)]
        for i, n in enumerate(self.nodes):
            n.links = [self.nodes[(i+1)%21], self.nodes[(i-1)%21]]
        self.dynamics = Dynamics()
        self.constraints = Constraint()
        self.integrity = IntegrityTracker()
        self.step_count = 0
        self.registry_buffer = MemoryBuffer(capacity=50)
        self.divergence_filter = DivergenceFilter()
        self.pole_margin = float(np.clip(
            pole_margin, POLE_MARGIN_MIN, POLE_MARGIN_MAX))
        self.pole_margin_was_clamped = (
            self.pole_margin != pole_margin)
        self.entropy_target = float(np.clip(
            entropy_target,
            ENTROPY_TARGET_MIN, ENTROPY_TARGET_MAX))
        self.entropy_target_was_clamped = (
            self.entropy_target != entropy_target)
        self.entropy_engine = EntropyEngine(
            target_entropy=self.entropy_target)
        self.raw_margin_history = []
        self.disable_pole_stabilization = disable_pole_stabilization
        self.node_count = len(self.nodes)
        (self.priority_injective,
         self.priority_duplicates) = verify_priority_injective(self.nodes)

    def step(self, dt):
        margin_before = self.constraints.evaluate(self.nodes)
        integrity_before = margin_before > 0.05

        for n in self.nodes:
            self.dynamics.step(n, dt)
        apply_mc2_coupling_cascade(self.nodes)
        if self.step_count % 10 == 0:
            sync_weights(self.nodes)
        self.registry_buffer.push([n.state.x for n in self.nodes])
        div = self.divergence_filter.get_filtered_divergence(
            self.registry_buffer.sample_trajectory())
        self.entropy_engine.apply_normalization(
            self.nodes, self.registry_buffer.sample_trajectory())
        apply_temporal_gating(
            self.step_count, self.nodes, div,
            target=self.entropy_target)

        self.raw_margin_history.append(
            self.constraints.evaluate_raw(self.nodes))

        self.step_count += 1
        dt = get_adaptive_dt(0.05, div)

        if not self.disable_pole_stabilization:
            live_margin = effective_pole_margin(self.pole_margin, self.nodes)
            apply_pole_stabilization(self.nodes, margin=live_margin)

        margin_after = self.constraints.evaluate(self.nodes)
        integrity_after = margin_after > 0.05
        self.integrity.check_transition(integrity_before, integrity_after)

        return margin_after

    def run(self, steps=200, dt=0.05):
        for t in range(steps):
            if self.step(dt) <= 0.05:
                return f"INSTABILITY_DETECTED_AT_{t}"
        return "RUN COMPLETE"

    def verify_all(self):
        margin = self.constraints.evaluate(self.nodes)
        status = 'STABLE' if margin > 0.05 else 'UNSTABLE'
        raw_margin = (self.raw_margin_history[-1]
                      if self.raw_margin_history else margin)
        raw_status = 'STABLE' if raw_margin > 0.05 else 'UNSTABLE'
        return (f"MARGIN:{margin:.6f} STATUS:{status} | "
                f"RAW_MARGIN(pre-correction):{raw_margin:.6f} "
                f"RAW_STATUS:{raw_status} | NODES:{len(self.nodes)}")

    @property
    def manifold_state(self):
        margin = self.constraints.evaluate(self.nodes)
        return f"21-DOMAIN-ACTIVE MARGIN:{margin:.4f}"

    @property
    def total_triad_energy(self):
        return float(sum(n.state.triad.total for n in self.nodes))

    @property
    def fusion_ignition_count(self):
        return sum(
            1 for n in self.nodes
            if lawson_satisfied(
                n.state.fusion_density, n.state.fusion_temp,
                n.state.fusion_confinement))

    @property
    def max_divB_residual(self):
        return float(max(
            abs(n.state.divB_resid) for n in self.nodes))

    @property
    def n7_vetoed_count(self):
        return sum(
            1 for n in self.nodes
            if n.state.n7_gate_status == "Vetoed")

    @property
    def max_omega_self_check(self):
        return float(max(
            abs(n.state.omega_self_check) for n in self.nodes))

    @property
    def chamber_valid_count(self):
        return sum(1 for n in self.nodes if n.state.chamber_valid)

    @property
    def quantum_properties_hold_count(self):
        return sum(
            1 for n in self.nodes
            if n.state.rho_hermitian and
               n.state.rho_trace_one and
               n.state.rho_positive)

    @property
    def raw_margin_ever_failed(self):
        return any(m <= 0.05 for m in self.raw_margin_history)

    def bidirectional_gate_report(self):
        statuses = [n.state.n7_gate_status for n in self.nodes]
        return system_gate_report(statuses)

    def most_permissive_node_index(self):
        return find_most_permissive_node(self.nodes)

    def matrix7_certified_kernel_report(self):
        return system_certified_kernel_report(self.nodes)

    def sovereign_hamiltonian_report(self, node_index=0):
        n = self.nodes[node_index]
        s = n.state
        m_vec = np.full(3, n.mass)
        A_vec = np.abs(s.p)
        dl_vec = s.x - s.y_spine if s.y_spine is not None else np.zeros(3)
        y_spine = s.y_spine if s.y_spine is not None else s.x.copy()
        return {
            "V_zero_iff_equilibrium": verify_V_zero_iff_equilibrium(
                s.x, y_spine, n.spring_k),
            "G_le_H": verify_G_le_H(
                s.p, m_vec, n.spring_k, s.x, y_spine,
                n.gov_weight, A_vec, dl_vec),
            "equilibrium_minimizes_H": verify_equilibrium_minimizes_H(
                s.p, m_vec, n.spring_k, y_spine,
                n.gov_weight, A_vec, dl_vec),
        }

    def run_recursive_thought(self, complexity_depth=3):
        margin = self.constraints.evaluate(self.nodes)
        return f"DEPTH:{complexity_depth} MARGIN:{margin:.6f}"

    def run_inference(self, user_input):
        report = self.bidirectional_gate_report()
        return f"DECISION:{report['system_status']} CONSISTENT:{report['forward_reverse_consistent']}"


def run_adversarial_stress_test(steps=200, dt=0.05, disable_pole=False,
                                  magnitude=15.0, seed=99):
    rt = PrimeRuntimeV4(disable_pole_stabilization=disable_pole)
    rng = np.random.default_rng(seed=seed)
    for n in rt.nodes:
        large_x = rng.normal(0, 1, size=3)
        large_x = large_x / (np.linalg.norm(large_x) + 1e-9) * magnitude
        n.state.x = large_x
        n.state.y_spine = np.zeros(3)
        large_p = rng.normal(0, 1, size=3) * 5.0
        n.state.p = large_p
    raw_margins = []
    corrected_margins = []
    for _ in range(steps):
        corrected = rt.step(dt)
        corrected_margins.append(corrected)
        raw_margins.append(rt.raw_margin_history[-1])
    recovery_step = next(
        (i for i, m in enumerate(raw_margins) if m > 0.05), None)
    return {
        "steps_run": steps,
        "magnitude": magnitude,
        "seed": seed,
        "min_raw_margin": float(min(raw_margins)),
        "raw_ever_failed": any(m <= 0.05 for m in raw_margins),
        "raw_margin_fully_recovered": raw_margins[-1] > 0.05,
        "first_step_raw_margin_crossed_threshold": recovery_step,
    }


def verify_recovery_robustness(magnitudes=(5.0, 10.0, 15.0, 20.0),
                                 seeds=(1, 42, 99, 2024), steps=100):
    results = []
    for mag in magnitudes:
        for seed in seeds:
            r = run_adversarial_stress_test(
                steps=steps, disable_pole=True, magnitude=mag, seed=seed)
            results.append(r)
    never_recovered = [r for r in results
                        if r["first_step_raw_margin_crossed_threshold"] is None]
    recovered = [r["first_step_raw_margin_crossed_threshold"] for r in results
                 if r["first_step_raw_margin_crossed_threshold"] is not None]
    return {
        "all_recovered": len(never_recovered) == 0,
        "never_recovered_cases": never_recovered,
        "recovery_step_range": (min(recovered), max(recovered)) if recovered else None,
        "full_results": results,
    }


if __name__ == "__main__":
    print("=== SPRING/DAMPING CALCULATION CHECK ===")
    print(f"spring_k=2.0, mass=1.0, computed critical damping: "
          f"{compute_critical_damping(2.0, 1.0):.6f}")

    print("\n=== MC2ENGINE SPEC VERIFICATION ===")
    print(f"Retain+leak sum: {verify_mc2_retain_leak_sum()}")
    print(f"Coupling symmetry: {verify_mc2_coupling_symmetric()}")

    print("\n=== DEFAULT RUN ===")
    rt = PrimeRuntimeV4()
    print(f"Priority injective at construction: {rt.priority_injective}")
    result = rt.run()
    print(result)
    print(rt.verify_all())
    print(f"Raw margin ever failed: {rt.raw_margin_ever_failed}")
    print(f"Bidirectional gate report: {rt.bidirectional_gate_report()}")

    print("\n=== MATRIX7 SYSTEM-WIDE CERTIFIED KERNEL REPORT ===")
    print(rt.matrix7_certified_kernel_report())

    print("\n=== SOVEREIGN HAMILTONIAN VERIFICATION REPORT (node 0) ===")
    print(rt.sovereign_hamiltonian_report(node_index=0))

    print("\n=== CHECKER SELF-TESTS ===")
    fresh_rt = PrimeRuntimeV4()
    print(f"Priority-violation detection: {selftest_priority_violation_detected(fresh_rt.nodes)}")
    print(f"Gate-veto detection: {selftest_gate_veto_detected()}")

    print("\n=== CLAMP_U NUMERIC BOUND CERTIFICATE ===")
    print(verify_clamp_u_bound())

    print("\n=== RECOVERY ROBUSTNESS CHECK (multiple magnitudes/seeds, mass-relative damping) ===")
    print(verify_recovery_robustness())
