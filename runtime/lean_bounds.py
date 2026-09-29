# lean_bounds.py
# Connects Python runtime to formally verified constants from ACI Lean modules
# All bounds correspond to proven theorems — zero sorries, CI green

class LeanBounds:
    """
    Formally verified bounds from ACI Lean modules.
    Each constant corresponds to a machine-checked theorem.
    """

    # From AWMCore.lean — awm_energy_bounded, energy_nonneg
    AWM_ENERGY_MAX = 1.0
    AWM_ENERGY_MIN = 0.0

    # From Governor.lean — safety_margin, safety_exceeds_limit
    SAFETY_MARGIN_MIN = 0.05
    SAFETY_MARGIN_TARGET = 0.95

    # From MoruzinLaw.lean — breach_implies_halt
    BREACH_THRESHOLD = 0.05

    # From AWMCore.lean — tanh_abs_lt_one
    TANH_BOUND = 1.0

    # From AWMCore.lean — perturbation_bound
    PERTURBATION_MAX = 0.99

    # From N7Spine.lean — spine_closure_margin
    SPINE_CLOSURE_MIN = 0.0

    # From SovereignHamiltonian.lean — energy_nonneg, G_le_H
    HAMILTONIAN_MIN = 0.0

    # From Manifold21.lean — phase_dist_nonneg
    PHASE_DIST_MIN = 0.0

    # From Governor.lean — redundancy_monotone
    MIN_ACTIVE_NODES = 2

    # From AWM21.lean — all_domains_count
    DOMAIN_COUNT = 21

    @classmethod
    def validate_margin(cls, margin: float) -> dict:
        """
        Validates a runtime margin against formally verified bounds.
        Returns status and which Lean theorem governs the bound.
        """
        if margin <= cls.BREACH_THRESHOLD:
            return {
                "status": "BREACH",
                "action": "HALT",
                "lean_theorem": "breach_implies_halt",
                "lean_module": "MoruzinLaw.lean",
                "margin": margin
            }
        elif margin < cls.SAFETY_MARGIN_TARGET:
            return {
                "status": "DEGRADED",
                "action": "NORMALIZE",
                "lean_theorem": "safety_margin",
                "lean_module": "Governor.lean",
                "margin": margin
            }
        else:
            return {
                "status": "STABLE",
                "action": "CONTINUE",
                "lean_theorem": "closure_law",
                "lean_module": "AWM21.lean",
                "margin": margin
            }

    @classmethod
    def validate_node_count(cls, active_nodes: int) -> bool:
        """
        From Governor.lean — governance_fails_without_redundancy
        System requires minimum node count to maintain governance.
        """
        return active_nodes >= cls.MIN_ACTIVE_NODES

    @classmethod
    def validate_energy(cls, energy: float) -> bool:
        """
        From SovereignHamiltonian.lean — energy_nonneg
        Energy must be nonnegative.
        """
        return energy >= cls.HAMILTONIAN_MIN

    @classmethod
    def validate_perturbation(cls, norm: float) -> bool:
        """
        From AWMCore.lean — perturbation_bound
        State vector norm must stay within pole stabilization bound.
        """
        return norm <= cls.PERTURBATION_MAX

    @classmethod
    def domain_closure_check(cls, margins: list) -> dict:
        """
        From AWM21.lean — closure_law, bottleneck_exists_iff
        M_N7 > 0 iff all domain margins > 0.
        Single failure collapses the system.
        """
        if len(margins) != cls.DOMAIN_COUNT:
            return {
                "status": "DOMAIN_COUNT_MISMATCH",
                "expected": cls.DOMAIN_COUNT,
                "received": len(margins)
            }
        min_margin = min(margins)
        bottleneck = margins.index(min_margin)
        if min_margin <= 0:
            return {
                "status": "CLOSURE_FAILED",
                "lean_theorem": "single_failure_collapses",
                "lean_module": "AWM21.lean",
                "bottleneck_domain": bottleneck,
                "M_N7": min_margin
            }
        return {
            "status": "CLOSED",
            "lean_theorem": "closure_law",
            "lean_module": "AWM21.lean",
            "bottleneck_domain": bottleneck,
            "M_N7": min_margin
        }
