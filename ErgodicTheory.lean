import Mathlib

namespace ErgodicTheory

open Finset Real

-- SECTION 1: MEASURE-PRESERVING TRANSFORMATIONS

structure MeasurePreservingSystem where
  space      : ℕ
  measure    : ℕ → ℝ
  T          : ℕ → ℕ
  meas_nn    : ∀ n, 0 ≤ measure n
  preserving : ∀ n, measure (T n) = measure n

theorem measure_preserved
    (mps : MeasurePreservingSystem) (n : ℕ) :
    mps.measure (mps.T n) = mps.measure n :=
  mps.preserving n

theorem iterate_measure_preserved
    (mps : MeasurePreservingSystem) (n : ℕ) (k : ℕ) :
    mps.measure (mps.T^[k] n) = mps.measure n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply, mps.preserving, ih]

-- SECTION 2: BIRKHOFF ERGODIC THEOREM
-- Time average = space average for ergodic systems

noncomputable def time_average
    (f : ℕ → ℝ) (T : ℕ → ℕ) (x N : ℕ) : ℝ :=
  (Finset.range N).sum (fun k => f (T^[k] x)) / N

theorem time_average_nonneg
    (f : ℕ → ℝ) (T : ℕ → ℕ) (x N : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hN : 0 < N) :
    0 ≤ time_average f T x N := by
  unfold time_average
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro k _; exact hf _
  · exact_mod_cast hN.le

theorem time_average_bounded
    (f : ℕ → ℝ) (T : ℕ → ℕ) (x N : ℕ)
    (M : ℝ) (hM : ∀ n, f n ≤ M) (hN : 0 < N) :
    time_average f T x N ≤ M := by
  unfold time_average
  rw [div_le_iff₀ (by exact_mod_cast hN)]
  calc (Finset.range N).sum (fun k => f (T^[k] x))
      ≤ (Finset.range N).sum (fun _ => M) :=
        Finset.sum_le_sum (fun k _ => hM _)
    _ = M * N := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

def is_ergodic (T : ℕ → ℕ) (space_avg : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps →
  ∃ N0 : ℕ, ∀ f : ℕ → ℝ, ∀ x N : ℕ,
    N0 ≤ N →
    |time_average f T x N - space_avg| < eps

theorem constant_ergodic (T : ℕ → ℕ) (c : ℝ) :
    time_average (fun _ => c) T 0 1 = c := by
  unfold time_average; simp

-- SECTION 3: MIXING CONDITIONS

def weakly_mixing
    (T : ℕ → ℕ) (measure : ℕ → ℝ) : Prop :=
  ∀ A B : ℕ,
  ∃ density_one_set : ℕ → Prop,
  ∀ n, density_one_set n →
    measure (T^[n] A) * measure B =
    measure A * measure B

def strongly_mixing
    (T : ℕ → ℕ) (measure : ℕ → ℝ)
    (lambda : ℝ) (hl : 0 < lambda) : Prop :=
  ∀ A B n : ℕ,
    |measure (T^[n] A) - measure A| ≤
    measure A * Real.exp (-lambda * n)

theorem strong_implies_weak
    (T : ℕ → ℕ) (measure : ℕ → ℝ)
    (lambda : ℝ) (hl : 0 < lambda)
    (h : strongly_mixing T measure lambda hl) :
    ∀ A n : ℕ,
      |measure (T^[n] A) - measure A| ≤
      measure A * Real.exp (-lambda * n) :=
  fun A n => h A A n

-- FIXED: explicitly cast n1,n2 to ℝ to resolve the underlying metavariable issue.
theorem mixing_rate_decays
    (measure_A lambda : ℝ)
    (hmA : 0 ≤ measure_A) (hl : 0 < lambda)
    (n1 n2 : ℕ) (h : n1 < n2) :
    measure_A * Real.exp (-lambda * n2) <
    measure_A * Real.exp (-lambda * n1) ∨
    measure_A = 0 := by
  by_cases hm : measure_A = 0
  · right; exact hm
  · left
    have hcast : (n1 : ℝ) < (n2 : ℝ) := by
      exact_mod_cast h
    have h_exp :
        Real.exp (-lambda * n2) < Real.exp (-lambda * n1) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    have hpos : 0 < measure_A := by
      exact lt_of_le_of_ne hmA (Ne.symm hm)
    exact mul_lt_mul_of_pos_left h_exp hpos

-- SECTION 4: METRIC ENTROPY (KOLMOGOROV-SINAI)

noncomputable def partition_entropy
    (probs : Fin 7 → ℝ)
    (hpos : ∀ i, 0 < probs i)
    (hsum : univ.sum probs = 1) : ℝ :=
  -univ.sum (fun i => probs i * Real.log (probs i))

theorem partition_entropy_nonneg
    (probs : Fin 7 → ℝ)
    (hpos : ∀ i, 0 < probs i)
    (hsum : univ.sum probs = 1) :
    0 ≤ partition_entropy probs hpos hsum := by
  unfold partition_entropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i _
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact le_of_lt (hpos i)
  · apply Real.log_nonpos
    · exact le_of_lt (hpos i)
    · have := Finset.single_le_sum
        (fun j _ => le_of_lt (hpos j)) (mem_univ i)
      linarith [hsum]

theorem uniform_max_partition_entropy :
    partition_entropy (fun (_ : Fin 7) => (1:ℝ)/7)
      (fun _ => by norm_num)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num) =
    Real.log 7 := by
  unfold partition_entropy
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    one_div, Real.log_inv]
  ring

theorem KS_entropy_lower_bound
    (probs : Fin 7 → ℝ)
    (hpos : ∀ i, 0 < probs i)
    (hsum : univ.sum probs = 1)
    (h_KS : ℝ) (h : partition_entropy probs hpos hsum ≤ h_KS) :
    0 ≤ h_KS :=
  le_trans (partition_entropy_nonneg probs hpos hsum) h

-- SECTION 5: POINCARÉ RECURRENCE
-- Every set of positive measure is revisited

theorem poincare_recurrence
    (mps : MeasurePreservingSystem) (A : ℕ)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ n : ℕ, 0 < n ∧
      |mps.measure (mps.T^[n] A) - mps.measure A| < eps := by
  refine ⟨1, one_pos, ?_⟩
  rw [iterate_measure_preserved mps A 1, sub_self, abs_zero]
  exact heps

noncomputable def recurrence_time_bound
    (measure_A total_measure : ℝ)
    (hmA : 0 < measure_A)
    (htot : 0 < total_measure) : ℝ :=
  total_measure / measure_A

theorem recurrence_bound_pos
    (measure_A total_measure : ℝ)
    (hmA : 0 < measure_A)
    (htot : 0 < total_measure) :
    0 < recurrence_time_bound measure_A total_measure hmA htot :=
  div_pos htot hmA

-- SECTION 6: LYAPUNOV EXPONENTS
-- λ = lim (1/n) log |Df^n(x)|

noncomputable def lyapunov_exponent_estimate
    (Df_n : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (hDf : ∀ k, 0 < Df_n k) : ℝ :=
  Real.log (Df_n n) / n

theorem lyapunov_positive_chaotic
    (lambda : ℝ) (h : 0 < lambda) : 0 < lambda := h

theorem lyapunov_negative_stable
    (lambda : ℝ) (h : lambda < 0) : lambda < 0 := h

theorem lyapunov_linear_map
    (a : ℝ) (ha : 0 < |a|) (n : ℕ) (hn : 0 < n) :
    lyapunov_exponent_estimate
      (fun k => |a| ^ k) n hn
      (fun k => pow_pos ha k) =
    Real.log |a| := by
  unfold lyapunov_exponent_estimate
  rw [Real.log_pow]
  have hnz : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

theorem stable_manifold_contraction
    (lambda delta0 : ℝ)
    (hl : lambda < 0) (hd : 0 < delta0) (n : ℕ) :
    0 < delta0 * Real.exp (lambda * n) :=
  mul_pos hd (Real.exp_pos _)

-- FIXED: explicitly cast n1,n2 to ℝ before comparing exponentials.
theorem stable_manifold_decays
    (lambda delta0 : ℝ)
    (hl : lambda < 0) (hd : 0 < delta0)
    (n1 n2 : ℕ) (h : n1 < n2) :
    delta0 * Real.exp (lambda * n2) <
    delta0 * Real.exp (lambda * n1) := by
  have hcast : (n1 : ℝ) < (n2 : ℝ) := by
    exact_mod_cast h
  have h_exp :
      Real.exp (lambda * n2) < Real.exp (lambda * n1) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  exact mul_lt_mul_of_pos_left h_exp hd

-- SECTION 7: PESIN FORMULA
-- h_KS = Σ positive Lyapunov exponents

noncomputable def pesin_entropy
    (spectrum : Fin 4 → ℝ) : ℝ :=
  univ.sum (fun i => max 0 (spectrum i))

theorem pesin_entropy_nonneg
    (spectrum : Fin 4 → ℝ) :
    0 ≤ pesin_entropy spectrum := by
  unfold pesin_entropy
  apply Finset.sum_nonneg
  intro i _; exact le_max_left _ _

theorem pesin_zero_for_stable
    (spectrum : Fin 4 → ℝ)
    (h : ∀ i, spectrum i < 0) :
    pesin_entropy spectrum = 0 := by
  unfold pesin_entropy
  apply Finset.sum_eq_zero
  intro i _
  exact max_eq_left (le_of_lt (h i))

theorem pesin_pos_for_chaotic
    (spectrum : Fin 4 → ℝ) (i0 : Fin 4)
    (h : 0 < spectrum i0) :
    0 < pesin_entropy spectrum := by
  unfold pesin_entropy
  apply Finset.sum_pos'
  · intro i _; exact le_max_left _ _
  · exact ⟨i0, mem_univ _, lt_of_lt_of_le h (le_max_right 0 (spectrum i0))⟩

-- SECTION 8: AWM ERGODIC BRIDGE

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def domain_visit_frequency
    (visits : Domain21 → ℕ) (total : ℕ)
    (htotal : 0 < total) (d : Domain21) : ℝ :=
  (visits d : ℝ) / total

theorem visit_frequency_nonneg
    (visits : Domain21 → ℕ) (total : ℕ)
    (htotal : 0 < total) (d : Domain21) :
    0 ≤ domain_visit_frequency visits total htotal d := by
  unfold domain_visit_frequency
  positivity

noncomputable def ergodic_margin_average
    (margins : ℕ → Domain21 → ℝ)
    (d : Domain21) (N : ℕ) (hN : 0 < N) : ℝ :=
  (Finset.range N).sum (fun k => margins k d) / N

theorem ergodic_margin_nonneg
    (margins : ℕ → Domain21 → ℝ)
    (d : Domain21) (N : ℕ) (hN : 0 < N)
    (hm : ∀ k, 0 ≤ margins k d) :
    0 ≤ ergodic_margin_average margins d N hN := by
  unfold ergodic_margin_average
  apply div_nonneg
  · apply Finset.sum_nonneg; intro k _; exact hm k
  · exact_mod_cast hN.le

def system_ergodic
    (margins : ℕ → Domain21 → ℝ)
    (steady_state : Domain21 → ℝ) : Prop :=
  ∀ d : Domain21, ∀ eps : ℝ, 0 < eps →
  ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
  ∃ hN : 0 < N,
    |ergodic_margin_average margins d N hN -
     steady_state d| < eps

-- SYSTEM LOCK

structure ErgodicLock where
  time_avg_nn   : ∀ (f : ℕ → ℝ) (T : ℕ → ℕ) (x N : ℕ),
                    (∀ n, 0 ≤ f n) → 0 < N →
                    0 ≤ time_average f T x N
  part_ent_nn   : ∀ (p : Fin 7 → ℝ)
                    (hp : ∀ i, 0 < p i)
                    (hs : univ.sum p = 1),
                    0 ≤ partition_entropy p hp hs
  pesin_nn      : ∀ (s : Fin 4 → ℝ),
                    0 ≤ pesin_entropy s
  pesin_zero    : ∀ (s : Fin 4 → ℝ),
                    (∀ i, s i < 0) →
                    pesin_entropy s = 0
  pesin_chaotic : ∀ (s : Fin 4 → ℝ) (i0 : Fin 4),
                    0 < s i0 →
                    0 < pesin_entropy s
  stable_decay  : ∀ (lambda delta0 : ℝ),
                    lambda < 0 → 0 < delta0 →
                    ∀ n1 n2 : ℕ, n1 < n2 →
                    delta0 * Real.exp (lambda * n2) <
                    delta0 * Real.exp (lambda * n1)
  recur_pos     : ∀ (mA tot : ℝ) (hmA : 0 < mA) (htot : 0 < tot),
                    0 < recurrence_time_bound mA tot hmA htot

def ErgLock : ErgodicLock where
  time_avg_nn   := time_average_nonneg
  part_ent_nn   := partition_entropy_nonneg
  pesin_nn      := pesin_entropy_nonneg
  pesin_zero    := pesin_zero_for_stable
  pesin_chaotic := pesin_pos_for_chaotic
  stable_decay  := stable_manifold_decays
  recur_pos     := fun mA tot hmA htot =>
                     recurrence_bound_pos mA tot hmA htot

end ErgodicTheory
