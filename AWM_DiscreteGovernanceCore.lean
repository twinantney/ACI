import Mathlib

namespace AWM_DiscreteGovernanceCore

def intMin (a b : Int) : Int := if a ≤ b then a else b

theorem intMin_le_left (a b : Int) : intMin a b ≤ a := by
  unfold intMin
  split_ifs <;> omega

theorem intMin_le_right (a b : Int) : intMin a b ≤ b := by
  unfold intMin
  split_ifs <;> omega

theorem intMin_comm (a b : Int) : intMin a b = intMin b a := by
  unfold intMin
  split_ifs <;> omega

theorem intMin_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ intMin a b := by
  unfold intMin
  split_ifs <;> omega

theorem intMin_glb (a b c : Int) (hca : c ≤ a) (hcb : c ≤ b) : c ≤ intMin a b := by
  unfold intMin
  split_ifs <;> omega

theorem intMin_self (a : Int) : intMin a a = a := by
  unfold intMin
  split_ifs <;> omega

theorem intMin_assoc (a b c : Int) : intMin (intMin a b) c = intMin a (intMin b c) := by
  unfold intMin
  split_ifs <;> omega

def listMinNE : Int → List Int → Int
  | x, [] => x
  | x, (y :: ys) => intMin x (listMinNE y ys)

theorem listMinNE_le_head (x : Int) (xs : List Int) : listMinNE x xs ≤ x := by
  cases xs with
  | nil => simp [listMinNE]
  | cons y ys => simp only [listMinNE]; exact intMin_le_left x (listMinNE y ys)

theorem listMinNE_le_mem : ∀ (xs : List Int) (x y : Int),
    y ∈ (x :: xs) → listMinNE x xs ≤ y := by
  intro xs
  induction xs with
  | nil =>
      intro x y hy
      simp at hy
      subst hy
      simp [listMinNE]
  | cons z zs ih =>
      intro x y hy
      simp only [listMinNE]
      simp at hy
      rcases hy with hy | hy
      · subst hy
        exact intMin_le_left x (listMinNE z zs)
      · have h1 := intMin_le_right x (listMinNE z zs)
        have h2 := ih z y hy
        omega

theorem listMinNE_nonneg : ∀ (xs : List Int) (x : Int),
    0 ≤ x → (∀ y ∈ xs, 0 ≤ y) → 0 ≤ listMinNE x xs := by
  intro xs
  induction xs with
  | nil =>
      intro x hx _
      simpa [listMinNE] using hx
  | cons z zs ih =>
      intro x hx hall
      simp only [listMinNE]
      have hz : 0 ≤ z := hall z (by simp)
      have hzs : ∀ y ∈ zs, 0 ≤ y := fun y hy => hall y (by simp [hy])
      have hrec := ih z hz hzs
      exact intMin_nonneg x (listMinNE z zs) hx hrec

theorem listMinNE_glb : ∀ (xs : List Int) (x c : Int),
    c ≤ x → (∀ y ∈ xs, c ≤ y) → c ≤ listMinNE x xs := by
  intro xs
  induction xs with
  | nil =>
      intro x c hx _
      simpa [listMinNE] using hx
  | cons z zs ih =>
      intro x c hx hall
      simp only [listMinNE]
      have hz : c ≤ z := hall z (by simp)
      have hzs : ∀ y ∈ zs, c ≤ y := fun y hy => hall y (by simp [hy])
      have hrec := ih z c hz hzs
      exact intMin_glb x (listMinNE z zs) c hx hrec

theorem listMinNE_eq_of_all_eq (c : Int) (xs : List Int) :
    ∀ x : Int, x = c → (∀ y ∈ xs, y = c) → listMinNE x xs = c := by
  induction xs with
  | nil => intro x hx _; simpa [listMinNE] using hx
  | cons z zs ih =>
      intro x hx hall
      have hz : z = c := hall z (by simp)
      have hzs : ∀ y ∈ zs, y = c := fun y hy => hall y (by simp [hy])
      have hrec := ih z hz hzs
      simp only [listMinNE, hrec, hx, intMin_self]

structure MarginVec where
  head : Int
  tail : List Int
  h_floor_head : 0 ≤ head
  h_floor_tail : ∀ y ∈ tail, 0 ≤ y

def MarginVec.M (mv : MarginVec) : Int := listMinNE mv.head mv.tail

theorem MarginVec.M_le_head (mv : MarginVec) : mv.M ≤ mv.head :=
  listMinNE_le_head mv.head mv.tail

theorem MarginVec.M_le_mem (mv : MarginVec) (y : Int) (hy : y ∈ (mv.head :: mv.tail)) :
    mv.M ≤ y :=
  listMinNE_le_mem mv.tail mv.head y hy

theorem MarginVec.M_nonneg (mv : MarginVec) : 0 ≤ mv.M :=
  listMinNE_nonneg mv.tail mv.head mv.h_floor_head mv.h_floor_tail

def MarginVec.rescale (mv : MarginVec) (c : Int) (hc : 0 ≤ c) : MarginVec where
  head := c * mv.head
  tail := mv.tail.map (fun y => c * y)
  h_floor_head := Int.mul_nonneg hc mv.h_floor_head
  h_floor_tail := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨y0, hy0, rfl⟩ := hy
    exact Int.mul_nonneg hc (mv.h_floor_tail y0 hy0)

structure ConstraintSet where
  checks : List Bool

def ConstraintSet.satisfied (cs : ConstraintSet) : Bool := cs.checks.all id

theorem ConstraintSet.satisfied_nil : (ConstraintSet.mk []).satisfied = true := by
  simp [ConstraintSet.satisfied]

theorem ConstraintSet.satisfied_cons (b : Bool) (bs : List Bool) :
    (ConstraintSet.mk (b :: bs)).satisfied = (b && (ConstraintSet.mk bs).satisfied) := by
  simp [ConstraintSet.satisfied]

theorem ConstraintSet.satisfied_append (cs1 cs2 : List Bool) :
    (ConstraintSet.mk (cs1 ++ cs2)).satisfied =
      ((ConstraintSet.mk cs1).satisfied && (ConstraintSet.mk cs2).satisfied) := by
  induction cs1 with
  | nil => simp [ConstraintSet.satisfied]
  | cons b bs ih =>
      simp only [List.cons_append, ConstraintSet.satisfied_cons, ih]
      cases b <;> simp

theorem ConstraintSet.satisfied_iff_all_true (cs : ConstraintSet) :
    cs.satisfied = true ↔ ∀ b ∈ cs.checks, b = true := by
  unfold ConstraintSet.satisfied
  constructor
  · intro h b hb
    exact List.all_eq_true.mp h b hb
  · intro h
    exact List.all_eq_true.mpr h

def stateChain (n : Nat) : Int := (n : Int) - 1

theorem stateChain_succ (n : Nat) : stateChain (n + 1) = stateChain n + 1 := by
  unfold stateChain
  omega

theorem stateChain_strictMono (m n : Nat) (h : m < n) : stateChain m < stateChain n := by
  unfold stateChain
  omega

theorem stateChain_injective (m n : Nat) (h : stateChain m = stateChain n) : m = n := by
  unfold stateChain at h
  omega

def reachN : Nat → (Nat → Nat → Bool) → Nat → Nat → Bool
  | 0, adj, i, j => (i == j) || adj i j
  | (k + 1), adj, i, j => reachN k adj i j || (List.range (k + 2)).any (fun m => reachN k adj i m && adj m j)

theorem reach0_refl (adj : Nat → Nat → Bool) (i : Nat) : reachN 0 adj i i = true := by
  unfold reachN
  simp

theorem reachN_mono (k : Nat) (adj : Nat → Nat → Bool) (i j : Nat) (h : reachN k adj i j = true) :
    reachN (k + 1) adj i j = true := by
  unfold reachN
  simp [h]

theorem reachN_step (adj : Nat → Nat → Bool) (i j : Nat) (h : adj i j = true) :
    reachN 0 adj i j = true := by
  unfold reachN
  simp [h]

structure ValidityCheck where
  domainOk : Bool
  constraintOk : Bool
  marginOk : Bool
  nodeOk : Bool

def ValidityCheck.valid (v : ValidityCheck) : Bool :=
  v.domainOk && v.constraintOk && v.marginOk && v.nodeOk

theorem ValidityCheck.valid_iff (v : ValidityCheck) :
    v.valid = true ↔ v.domainOk = true ∧ v.constraintOk = true ∧ v.marginOk = true ∧ v.nodeOk = true := by
  unfold ValidityCheck.valid
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    tauto
  · intro ⟨h1, h2, h3, h4⟩
    simp [h1, h2, h3, h4]

theorem ValidityCheck.valid_of_all_true (v : ValidityCheck)
    (h1 : v.domainOk = true) (h2 : v.constraintOk = true)
    (h3 : v.marginOk = true) (h4 : v.nodeOk = true) : v.valid = true := by
  rw [ValidityCheck.valid_iff]
  exact ⟨h1, h2, h3, h4⟩

theorem ValidityCheck.invalid_of_domain_false (v : ValidityCheck) (h : v.domainOk = false) :
    v.valid = false := by
  unfold ValidityCheck.valid
  simp [h]

theorem ValidityCheck.invalid_of_constraint_false (v : ValidityCheck) (h : v.constraintOk = false) :
    v.valid = false := by
  unfold ValidityCheck.valid
  simp [h]

theorem ValidityCheck.invalid_of_margin_false (v : ValidityCheck) (h : v.marginOk = false) :
    v.valid = false := by
  unfold ValidityCheck.valid
  simp [h]

theorem ValidityCheck.invalid_of_node_false (v : ValidityCheck) (h : v.nodeOk = false) :
    v.valid = false := by
  unfold ValidityCheck.valid
  simp [h]

def marginFromValidity (v : ValidityCheck) (baseMargin : Int) (hbase : 0 ≤ baseMargin) : Int :=
  if v.valid then baseMargin else 0

theorem marginFromValidity_nonneg (v : ValidityCheck) (baseMargin : Int) (hbase : 0 ≤ baseMargin) :
    0 ≤ marginFromValidity v baseMargin hbase := by
  unfold marginFromValidity
  split_ifs <;> omega

theorem marginFromValidity_eq_base_of_valid (v : ValidityCheck) (baseMargin : Int) (hbase : 0 ≤ baseMargin)
    (h : v.valid = true) : marginFromValidity v baseMargin hbase = baseMargin := by
  unfold marginFromValidity
  simp [h]

theorem marginFromValidity_eq_zero_of_invalid (v : ValidityCheck) (baseMargin : Int) (hbase : 0 ≤ baseMargin)
    (h : v.valid = false) : marginFromValidity v baseMargin hbase = 0 := by
  unfold marginFromValidity
  simp [h]

def marginVecFromChecks (base : Int) (hbase : 0 ≤ base) (v0 : ValidityCheck) (vs : List ValidityCheck) :
    MarginVec where
  head := marginFromValidity v0 base hbase
  tail := vs.map (fun v => marginFromValidity v base hbase)
  h_floor_head := marginFromValidity_nonneg v0 base hbase
  h_floor_tail := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨v, _, rfl⟩ := hy
    exact marginFromValidity_nonneg v base hbase

theorem marginVecFromChecks_eq_base_of_all_valid (base : Int) (hbase : 0 ≤ base)
    (v0 : ValidityCheck) (vs : List ValidityCheck)
    (h0 : v0.valid = true) (hall : ∀ v ∈ vs, v.valid = true) :
    (marginVecFromChecks base hbase v0 vs).M = base := by
  have hhead : marginFromValidity v0 base hbase = base :=
    marginFromValidity_eq_base_of_valid v0 base hbase h0
  have htail : ∀ y ∈ vs.map (fun v => marginFromValidity v base hbase), y = base := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact marginFromValidity_eq_base_of_valid v base hbase (hall v hv)
  unfold MarginVec.M marginVecFromChecks
  exact listMinNE_eq_of_all_eq base _ (marginFromValidity v0 base hbase) hhead htail

theorem marginVecFromChecks_eq_zero_of_exists_invalid (base : Int) (hbase : 0 ≤ base)
    (v0 : ValidityCheck) (vs : List ValidityCheck)
    (hinvalid : v0.valid = false ∨ ∃ v ∈ vs, v.valid = false) :
    (marginVecFromChecks base hbase v0 vs).M = 0 := by
  have hmem : (0 : Int) ∈
      ((marginVecFromChecks base hbase v0 vs).head :: (marginVecFromChecks base hbase v0 vs).tail) := by
    rcases hinvalid with h0 | ⟨v, hv, hvfalse⟩
    · left
      exact marginFromValidity_eq_zero_of_invalid v0 base hbase h0
    · right
      refine List.mem_map.mpr ⟨v, hv, ?_⟩
      exact marginFromValidity_eq_zero_of_invalid v base hbase hvfalse
  have hle := MarginVec.M_le_mem (marginVecFromChecks base hbase v0 vs) 0 hmem
  have hge := MarginVec.M_nonneg (marginVecFromChecks base hbase v0 vs)
  omega

end AWM_DiscreteGovernanceCore
