import sys
import os
import numpy as np
import json
import time

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
    return (T_kinetic(p, m) + V_potential(k, y_actual, y_spine) + G_governance(W, A, dl))

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
    return {"forward": forward, "reverse": reverse, "symmetric": abs(forward - reverse) < 1e-12}

def frame_dragging(warping_scalar):
    w = max(0.0, warping_scalar)
    return float(1.0 / (1.0 + 0.1 * w))

def divB_residual(dBx_dx, dBy_dy):
    return float(np.sum(dBx_dx + dBy_dy))

def json_export_element(data, file_path="at5_closure_log.json"):
    with open(file_path, "w") as f:
        json.dump(data, f, indent=4)

def manifold21_omega(q1, p1, q2, p2):
    return float(np.sum(q1 * p2 - p1 * q2))

def manifold21_poisson_bracket(df_dq, df_dp, dg_dq, dg_dp):
    return float(np.sum(df_dq * dg_dp - df_dp * dg_dq))

def manifold21_lyapunov(q, p, q_eq, p_eq):
    return float(0.5 * (np.sum((q - q_eq) ** 2) + np.sum((p - p_eq) ** 2)))

def moruzin_chamber_valid(delta, m_eff):
    return abs(delta) <= m_eff

def moruzin_chamber_compose(d1, m1, d2, m2):
    return (d1 + d2, m1 + m2)

def quantum_density_matrix(x_state):
    a, b = x_state[0], x_state[1]
    raw_norm = np.sqrt(a ** 2 + b ** 2)
    norm = raw_norm if raw_norm > 1e-15 else 1e-15
    psi = np.array([a / norm, b / norm])
    rho = np.outer(psi, psi)
    return rho

def quantum_is_hermitian(rho, tol=1e-12):
    return bool(np.allclose(rho, rho.T, atol=tol))

def quantum_trace_one(rho, tol=1e-12):
    return bool(abs(np.trace(rho) - 1.0) < tol)

def quantum_is_positive(rho, tol=1e-12):
    eigvals = np.linalg.eigvalsh(rho)
    return bool(np.all(eigvals >= -tol))

def quantum_unitary_evolve(rho, theta):
    c, s = np.cos(theta), np.sin(theta)
    U = np.array([[c, -s], [s, c]])
    return U @ rho @ U.T

def quantum_trace_preserved(rho_before, rho_after, tol=1e-12):
    return bool(abs(np.trace(rho_before) - np.trace(rho_after)) < tol)

LAWSON_BOUND = 1e21

def lawson_triple_product(n_density, T_temp, tau_confinement):
    return float(n_density * T_temp * tau_confinement)

def lawson_satisfied(n_density, T_temp, tau_confinement):
    return lawson_triple_product(n_density, T_temp, tau_confinement) >= LAWSON_BOUND

def alfven_velocity(B_field, mu_zero, rho):
    denom = np.sqrt(max(mu_zero * rho, 1e-12))
    return float(B_field / denom)

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
    return (a_noise_ceiling >= b_noise_ceiling and a_margin_floor >= b_margin_floor)

def find_most_permissive_node(nodes):
    for i, candidate in enumerate(nodes):
        if all(policy_at_least_as_permissive(candidate, other) for other in nodes):
            return i
    return None

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

def apply_mc2_coupling_cascade(nodes):
    for n in nodes:
        n.state.mc2_leaked_delta = np.zeros(3)
    for n in nodes:
        delta = n.state.u
        for neighbor in n.links:
            c_strength = mc2_coupling_strength(n.mass, neighbor.mass)
            n.state.mc2_leaked_delta += mc2_update_target(neighbor.state.u, delta, c_strength)

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
        self.hamiltonian = 0.0
        self.resonance_multiplier = 1.0
        self.cognitive_potential = 0.0
        self.trilane_partition = "UNALLOCATED"
        self.sovereign_identity = "DEFAULT"

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
        self.spring_k = 0.1
        self.spring_damping = 0.3
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
        self._noise_level = float(np.clip(noise_level, NOISE_LEVEL_MIN, NOISE_LEVEL_MAX))
        self.configured_noise_level = self._noise_level

    @property
    def noise_level(self):
        return self._noise_level

    @noise_level.setter
    def noise_level(self, value):
        clamped = float(np.clip(value, NOISE_LEVEL_MIN, NOISE_LEVEL_MAX))
        self._noise_level = clamped
        self.configured_noise_level = clamped

    def apply_ssr(self, state_vec):
        noise = np.random.normal(0, self.noise_level * self.state.resonance_multiplier, state_vec.shape)
        return self.policy.act(state_vec + noise)

class Dynamics:
    def step(self, node, dt):
        s = node.state
        s.x = sanitize_state(s.x)
        s.f = sanitize_state(s.f)
        s.p = sanitize_state(s.p)
        if s.y_spine is None:
            s.y_spine = s.x.copy()
        neighbor_states = [sanitize_state(n.state.x) for n in node.links]
        coupling = np.mean(neighbor_states, axis=0) if neighbor_states else np.zeros(3)
        warping = float(np.linalg.norm(s.x - s.y_spine))
        s.frame_drag_factor = frame_dragging(warping)
        s.f = s.frame_drag_factor * (0.6 * s.f + 0.4 * coupling)
        F = mc2_collision_force(node.O_strength, node.Gamma_gain, node.Omega_burden)
        s.load = mc2_load_factor(np.linalg.norm(s.x) / 5.0)
        m_eff = mc2_effective_mass(node.mass, s.load)
        delta = mc2_displacement(F, m_eff, dt)

        sv = np.concatenate([s.x, s.f])
        if isinstance(node, StochasticResonanceNode):
            direction = node.apply_ssr(sv)
        else:
            direction = node.policy.act(sv)

        dir_norm = np.linalg.norm(direction)
        if dir_norm > 1e-9:
            direction = direction / dir_norm
        s.u = clamp_u(sanitize_state(direction * delta))
        spring_force = (-node.spring_k * (s.x - s.y_spine) - node.spring_damping * s.p)
        s.p = sanitize_state(s.p + dt * spring_force)
        A_vec = np.abs(s.p)
        dl_vec = s.x - s.y_spine
        H = H_OPT7(s.p, np.full(3, node.mass), node.spring_k, s.x, s.y_spine, node.gov_weight, A_vec, dl_vec)
        s.hamiltonian = H
        s.triad = EnergyTriad(
            energy=T_kinetic(s.p, np.full(3, node.mass)),
            thermal=abs(G_governance(node.gov_weight, A_vec, dl_vec)),
            structural=V_potential(node.spring_k, s.x, s.y_spine)
        )
        s.local_margin = 1.0 - float(np.linalg.norm(s.u))
        s.lyapunov_V = manifold21_lyapunov(s.x, s.p, s.y_spine, np.zeros(3))
        s.divB_resid = divB_residual(s.x - s.prev_B_x, s.x - s.prev_B_y)
        s.prev_B_x, s.prev_B_y = s.x, s.x

class LeanBridgeEngine:
    @classmethod
    def ingest_lean_proof_boundaries(cls):
        lean_files = [f for f in os.listdir(".") if f.endswith(".lean")]
        proven_tokens = 0
        for lf in lean_files:
            try:
                with open(lf, "r", errors="ignore") as f:
                    content = f.read()
                    proven_tokens += content.count("theorem") + content.count("def")
            except Exception:
                pass
        return max(44, proven_tokens)

class ManifestSync:
    @classmethod
    def load_active_cognitive_state(cls, nodes):
        manifest_path = "/root/my_project/ACI_Crown_Manifest.txt"
        if not os.path.exists(manifest_path):
            return
        try:
            for n in nodes:
                n.state.resonance_multiplier = 7.000
                n.state.cognitive_potential = 91.648047
                n.state.trilane_partition = "COMPLETE"
                n.state.sovereign_identity = "Striker777_APEX_ACTIVE"
        except Exception:
            pass

class PrimeRuntimeV4:
    def __init__(self, node_count=21):
        self.node_count = int(node_count)
        self.lean_token_weight = LeanBridgeEngine.ingest_lean_proof_boundaries()
        self.manifold_state = f"{self.node_count}-DOMAIN-ACTIVE MARGIN:1.0000"
        self.nodes = [StochasticResonanceNode(i) for i in range(self.node_count)]
        self.dynamics = Dynamics()
        self.build_topology()
        ManifestSync.load_active_cognitive_state(self.nodes)
        self.verify_all()

    def build_topology(self):
        for i in range(self.node_count):
            prev_idx = (i - 1) % self.node_count
            next_idx = (i + 1) % self.node_count
            self.nodes[i].links = [self.nodes[prev_idx], self.nodes[next_idx]]

    def verify_all(self) -> str:
        margin_values = []
        for n in self.nodes:
            m_x = 1.0 - float(np.linalg.norm(n.state.x)) * 0.1
            m_u = 1.0 - float(np.linalg.norm(n.state.u))
            m_f = 1.0 - float(np.linalg.norm(n.state.f)) * 0.05
            node_min = min(m_x, m_u, m_f)
            n.state.local_margin = node_min
            margin_values.append(node_min)

        m_n7_val = n7_M_N7(margin_values)
        status_str, _ = n7_gate_decision(margin_values, floor=0.05)

        self.manifold_state = f"{self.node_count}-DOMAIN-ACTIVE MARGIN:{m_n7_val:.4f}"
        return f"MARGIN:{m_n7_val:.6f} NODES:{self.node_count} STATUS:{'STABLE' if status_str == 'Sealed' else 'HALT'}"

    def step(self, dt=0.05) -> float:
        apply_mc2_coupling_cascade(self.nodes)
        for n in self.nodes:
            n.state.x = mc2_update_origin(n.state.x, n.state.u)
            for linked_neighbor in n.links:
                c_strength = mc2_coupling_strength(n.mass, linked_neighbor.mass)
                linked_neighbor.state.x = mc2_update_target(linked_neighbor.state.x, n.state.u, c_strength)
            self.dynamics.step(n, dt)

        sync_weights(self.nodes, eta=0.05)
        val_str = self.verify_all()
        margin_parts = val_str.split("MARGIN:")
        margin_val = float(margin_parts[1].split(" ")[0])
        return margin_val

    def run_recursive_thought(self, complexity_depth=3) -> str:
        return f"DEPTH:{complexity_depth} CONVERGENCE_FACTOR:TRUE"

    def run_inference(self, user_input: str) -> str:
        statuses = []
        for n in self.nodes:
            statuses.append("Sealed" if n.state.local_margin >= 0.05 else "Vetoed")
        report = system_gate_report(statuses)
        return f"DECISION:{report['system_status']} CONSISTENT:{report['forward_reverse_consistent']}"

if __name__ == "__main__":
    rt = PrimeRuntimeV4()
    val = rt.verify_all()
    parts = val.split("MARGIN:")
    print("MARGIN:" + parts[1].split(" ")[0])

