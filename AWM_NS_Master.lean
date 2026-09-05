-- 
import Mathlib

namespace AWM_NS_Master

open Finset Real

structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Vec3

def zero : Vec3 := ⟨0, 0, 0⟩
def add (a b : Vec3) : Vec3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def neg (a : Vec3) : Vec3 := ⟨-a.x, -a.y, -a.z⟩
def sub (a b : Vec3) : Vec3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
def smul (c : ℝ) (a : Vec3) : Vec3 := ⟨c * a.x, c * a.y, c * a.z⟩
def dot (a b : Vec3) : ℝ := a.x * b.x + a.y * b.y + a.z * b.z
def cross (a b : Vec3) : Vec3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩
def normSq (a : Vec3) : ℝ := dot a a

theorem ext {a b : Vec3} (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a; cases b; simp_all

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by unfold dot; ring
theorem cross_self (a : Vec3) : cross a a = zero := by apply ext <;> simp [cross, zero]
theorem dot_cross_self (a b : Vec3) : dot a (cross a b) = 0 := by unfold dot cross; ring
theorem cross_dot_self (a b : Vec3) : dot (cross a b) a = 0 := by rw [dot_comm]; exact dot_cross_self a b
theorem smul_dot (c : ℝ) (a b : Vec3) : dot (smul c a) b = c * dot a b := by unfold smul dot; ring

theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  unfold normSq dot; nlinarith [sq_nonneg a.x, sq_nonneg a.y, sq_nonneg a.z]

theorem normSq_eq_zero_iff (a : Vec3) : normSq a = 0 ↔ a = zero := by
  unfold normSq dot
  constructor
  · intro h; apply ext <;> nlinarith [sq_nonneg a.x, sq_nonneg a.y, sq_nonneg a.z]
  · intro h; rw [h]; simp [zero]

theorem dot_self_eq_normSq (a : Vec3) : dot a a = normSq a := rfl
theorem smul_normSq (c : ℝ) (a : Vec3) : normSq (smul c a) = c ^ 2 * normSq a := by
  unfold normSq smul dot; ring
theorem add_comm (a b : Vec3) : add a b = add b a := by apply ext <;> simp [add] <;> ring
theorem normSq_zero : normSq zero = 0 := by unfold normSq dot zero
theorem cross_anticomm (a b : Vec3) : cross a b = neg (cross b a) := by
  apply ext <;> simp [cross, neg] <;> ring
theorem dot_add_left (a b c : Vec3) : dot (add a b) c = dot a c + dot b c := by unfold dot add; ring

theorem cauchy_schwarz (a b : Vec3) : (dot a b) ^ 2 ≤ normSq a * normSq b := by
  unfold dot normSq dot
  nlinarith [sq_nonneg (a.x * b.y - a.y * b.x), sq_nonneg (a.y * b.z - a.z * b.y),
             sq_nonneg (a.x * b.z - a.z * b.x)]

theorem add_normSq_le (a b : Vec3) : normSq (add a b) ≤ 2 * (normSq a + normSq b) := by
  unfold normSq dot add
  nlinarith [sq_nonneg (a.x - b.x), sq_nonneg (a.y - b.y), sq_nonneg (a.z - b.z)]

theorem dot_le_sqrt_mul_sqrt (a b : Vec3) :
    dot a b ≤ Real.sqrt (normSq a) * Real.sqrt (normSq b) := by
  have hcs := cauchy_schwarz a b
  have hna := normSq_nonneg a
  have hnb := normSq_nonneg b
  have hprod : Real.sqrt (normSq a) * Real.sqrt (normSq b) = Real.sqrt (normSq a * normSq b) := by
    rw [Real.sqrt_mul hna]
  rw [hprod]
  have habs : dot a b ≤ |dot a b| := le_abs_self _
  refine le_trans habs ?_
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hcs

theorem triangle_ineq (a b : Vec3) :
    Real.sqrt (normSq (add a b)) ≤ Real.sqrt (normSq a) + Real.sqrt (normSq b) := by
  have hsq : normSq (add a b) ≤ (Real.sqrt (normSq a) + Real.sqrt (normSq b)) ^ 2 := by
    have hna := normSq_nonneg a
    have hnb := normSq_nonneg b
    have hexp : normSq (add a b) = normSq a + 2 * dot a b + normSq b := by
      unfold normSq dot add; ring
    have hsa : Real.sqrt (normSq a) ^ 2 = normSq a := Real.sq_sqrt hna
    have hsb : Real.sqrt (normSq b) ^ 2 = normSq b := Real.sq_sqrt hnb
    have hab := dot_le_sqrt_mul_sqrt a b
    nlinarith [hexp, hsa, hsb, hab]
  have hrhs : 0 ≤ Real.sqrt (normSq a) + Real.sqrt (normSq b) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc Real.sqrt (normSq (add a b))
      ≤ Real.sqrt ((Real.sqrt (normSq a) + Real.sqrt (normSq b)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (normSq a) + Real.sqrt (normSq b) := Real.sqrt_sq hrhs

end Vec3

structure Mat3 where
  a11 : ℝ; a12 : ℝ; a13 : ℝ
  a21 : ℝ; a22 : ℝ; a23 : ℝ
  a31 : ℝ; a32 : ℝ; a33 : ℝ

namespace Mat3

def zero : Mat3 := ⟨0,0,0,0,0,0,0,0,0⟩
def transpose (A : Mat3) : Mat3 :=
  ⟨A.a11, A.a21, A.a31, A.a12, A.a22, A.a32, A.a13, A.a23, A.a33⟩
def add (A B : Mat3) : Mat3 :=
  ⟨A.a11+B.a11, A.a12+B.a12, A.a13+B.a13, A.a21+B.a21, A.a22+B.a22, A.a23+B.a23,
   A.a31+B.a31, A.a32+B.a32, A.a33+B.a33⟩
def sub (A B : Mat3) : Mat3 :=
  ⟨A.a11-B.a11, A.a12-B.a12, A.a13-B.a13, A.a21-B.a21, A.a22-B.a22, A.a23-B.a23,
   A.a31-B.a31, A.a32-B.a32, A.a33-B.a33⟩
def smul (c : ℝ) (A : Mat3) : Mat3 :=
  ⟨c*A.a11, c*A.a12, c*A.a13, c*A.a21, c*A.a22, c*A.a23, c*A.a31, c*A.a32, c*A.a33⟩
def mulVec (A : Mat3) (v : Vec3) : Vec3 :=
  ⟨A.a11*v.x+A.a12*v.y+A.a13*v.z, A.a21*v.x+A.a22*v.y+A.a23*v.z, A.a31*v.x+A.a32*v.y+A.a33*v.z⟩
def mul (A B : Mat3) : Mat3 :=
  ⟨A.a11*B.a11+A.a12*B.a21+A.a13*B.a31, A.a11*B.a12+A.a12*B.a22+A.a13*B.a32,
   A.a11*B.a13+A.a12*B.a23+A.a13*B.a33, A.a21*B.a11+A.a22*B.a21+A.a23*B.a31,
   A.a21*B.a12+A.a22*B.a22+A.a23*B.a32, A.a21*B.a13+A.a22*B.a23+A.a23*B.a33,
   A.a31*B.a11+A.a32*B.a21+A.a33*B.a31, A.a31*B.a12+A.a32*B.a22+A.a33*B.a32,
   A.a31*B.a13+A.a32*B.a23+A.a33*B.a33⟩
def trace (A : Mat3) : ℝ := A.a11 + A.a22 + A.a33
def frobeniusSq (A : Mat3) : ℝ :=
  A.a11^2+A.a12^2+A.a13^2+A.a21^2+A.a22^2+A.a23^2+A.a31^2+A.a32^2+A.a33^2
def symmetricPart (A : Mat3) : Mat3 := smul (1/2) (add A (transpose A))
def antisymmetricPart (A : Mat3) : Mat3 := smul (1/2) (sub A (transpose A))

theorem frobeniusSq_nonneg (A : Mat3) : 0 ≤ frobeniusSq A := by unfold frobeniusSq; positivity
theorem trace_symmetricPart (A : Mat3) : trace (symmetricPart A) = trace A := by
  unfold trace symmetricPart smul add transpose; ring
theorem trace_antisymmetricPart (A : Mat3) : trace (antisymmetricPart A) = 0 := by
  unfold trace antisymmetricPart smul sub transpose; ring
theorem add_symmetric_antisymmetric (A : Mat3) :
    add (symmetricPart A) (antisymmetricPart A) = A := by
  unfold add symmetricPart antisymmetricPart smul sub transpose
  cases A; simp; constructor <;> ring
theorem transpose_transpose (A : Mat3) : transpose (transpose A) = A := by
  unfold transpose; cases A; rfl
theorem trace_add (A B : Mat3) : trace (add A B) = trace A + trace B := by unfold trace add; ring
theorem trace_smul (c : ℝ) (A : Mat3) : trace (smul c A) = c * trace A := by unfold trace smul; ring
theorem transpose_symmetricPart (A : Mat3) : transpose (symmetricPart A) = symmetricPart A := by
  unfold symmetricPart transpose smul add; cases A; simp; constructor <;> ring
theorem transpose_add (A B : Mat3) : transpose (add A B) = add (transpose A) (transpose B) := by
  unfold transpose add; cases A; cases B; rfl

theorem frobeniusSq_add_le (A B : Mat3) :
    frobeniusSq (add A B) ≤ 2 * (frobeniusSq A + frobeniusSq B) := by
  unfold frobeniusSq add
  nlinarith [sq_nonneg (A.a11-B.a11), sq_nonneg (A.a12-B.a12), sq_nonneg (A.a13-B.a13),
             sq_nonneg (A.a21-B.a21), sq_nonneg (A.a22-B.a22), sq_nonneg (A.a23-B.a23),
             sq_nonneg (A.a31-B.a31), sq_nonneg (A.a32-B.a32), sq_nonneg (A.a33-B.a33)]

theorem mulVec_normSq_le (A : Mat3) (v : Vec3) :
    Vec3.normSq (mulVec A v) ≤ frobeniusSq A * Vec3.normSq v := by
  have h1 : (A.a11*v.x+A.a12*v.y+A.a13*v.z)^2 ≤
      (A.a11^2+A.a12^2+A.a13^2)*(v.x^2+v.y^2+v.z^2) := by
    nlinarith [sq_nonneg (A.a11*v.y-A.a12*v.x), sq_nonneg (A.a12*v.z-A.a13*v.y),
               sq_nonneg (A.a11*v.z-A.a13*v.x)]
  have h2 : (A.a21*v.x+A.a22*v.y+A.a23*v.z)^2 ≤
      (A.a21^2+A.a22^2+A.a23^2)*(v.x^2+v.y^2+v.z^2) := by
    nlinarith [sq_nonneg (A.a21*v.y-A.a22*v.x), sq_nonneg (A.a22*v.z-A.a23*v.y),
               sq_nonneg (A.a21*v.z-A.a23*v.x)]
  have h3 : (A.a31*v.x+A.a32*v.y+A.a33*v.z)^2 ≤
      (A.a31^2+A.a32^2+A.a33^2)*(v.x^2+v.y^2+v.z^2) := by
    nlinarith [sq_nonneg (A.a31*v.y-A.a32*v.x), sq_nonneg (A.a32*v.z-A.a33*v.y),
               sq_nonneg (A.a31*v.z-A.a33*v.x)]
  unfold mulVec Vec3.normSq Vec3.dot frobeniusSq
  nlinarith [h1, h2, h3]

theorem trace_le_sqrt_three_mul_frobenius (A : Mat3) :
    trace A ≤ Real.sqrt 3 * Real.sqrt (frobeniusSq A) := by
  have hcs : (trace A) ^ 2 ≤ 3 * frobeniusSq A := by
    unfold trace frobeniusSq
    nlinarith [sq_nonneg (A.a11-A.a22), sq_nonneg (A.a22-A.a33), sq_nonneg (A.a11-A.a33),
               sq_nonneg A.a12, sq_nonneg A.a13, sq_nonneg A.a21, sq_nonneg A.a23,
               sq_nonneg A.a31, sq_nonneg A.a32]
  have hfrob := frobeniusSq_nonneg A
  have hrw : Real.sqrt 3 * Real.sqrt (frobeniusSq A) = Real.sqrt (3 * frobeniusSq A) := by
    rw [Real.sqrt_mul (by norm_num)]
  rw [hrw]
  have habs : trace A ≤ |trace A| := le_abs_self _
  refine le_trans habs ?_
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hcs

theorem trace_mul_comm (A B : Mat3) : trace (mul A B) = trace (mul B A) := by unfold trace mul; ring
theorem mul_mulVec (A B : Mat3) (v : Vec3) : mulVec (mul A B) v = mulVec A (mulVec B v) := by
  apply Vec3.ext <;> (unfold mul mulVec; ring)
theorem mul_add (A B C : Mat3) : mul A (add B C) = add (mul A B) (mul A C) := by
  unfold mul add; cases A; cases B; cases C; simp; refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> ring

end Mat3

abbrev Point3 := Vec3
abbrev Time := ℝ
abbrev VelocityField := Time → Point3 → Vec3
abbrev ScalarField := Time → Point3 → ℝ
abbrev PressureField := ScalarField
abbrev GradientField := Time → Point3 → Mat3
abbrev VorticityField := Time → Point3 → Vec3

structure SpatialDerivative where
  dx : (Point3 → ℝ) → Point3 → ℝ
  dy : (Point3 → ℝ) → Point3 → ℝ
  dz : (Point3 → ℝ) → Point3 → ℝ

structure SpatialSecondDerivative where
  dxx : (Point3 → ℝ) → Point3 → ℝ
  dyy : (Point3 → ℝ) → Point3 → ℝ
  dzz : (Point3 → ℝ) → Point3 → ℝ

def gradient (D : SpatialDerivative) (f : Point3 → ℝ) (p : Point3) : Vec3 :=
  ⟨D.dx f p, D.dy f p, D.dz f p⟩
def laplacian (D : SpatialSecondDerivative) (f : Point3 → ℝ) (p : Point3) : ℝ :=
  D.dxx f p + D.dyy f p + D.dzz f p
def divergence (G : Mat3) : ℝ := Mat3.trace G
def incompressible (G : GradientField) : Prop := ∀ t p, divergence (G t p) = 0

theorem incompressible_zero : incompressible (fun _ _ => Mat3.zero) := by
  intro t p; simp [divergence, Mat3.trace, Mat3.zero]

def curl (D : SpatialDerivative) (u : Point3 → Vec3) (p : Point3) : Vec3 :=
  ⟨D.dy (fun q => (u q).z) p - D.dz (fun q => (u q).y) p,
   D.dz (fun q => (u q).x) p - D.dx (fun q => (u q).z) p,
   D.dx (fun q => (u q).y) p - D.dy (fun q => (u q).x) p⟩

def vorticity (D : SpatialDerivative) (u : VelocityField) : VorticityField := fun t p => curl D (u t) p
def strain (G : GradientField) : GradientField := fun t p => Mat3.symmetricPart (G t p)
def rotation (G : GradientField) : GradientField := fun t p => Mat3.antisymmetricPart (G t p)
def convective (G : GradientField) (u : VelocityField) : VelocityField :=
  fun t p => Mat3.mulVec (G t p) (u t p)

theorem strain_add_rotation (G : GradientField) (t : Time) (p : Point3) :
    Mat3.add (strain G t p) (rotation G t p) = G t p := Mat3.add_symmetric_antisymmetric (G t p)

theorem convective_normSq_bound (G : GradientField) (u : VelocityField) (t : Time) (p : Point3) :
    Vec3.normSq (convective G u t p) ≤ Mat3.frobeniusSq (G t p) * Vec3.normSq (u t p) :=
  Mat3.mulVec_normSq_le (G t p) (u t p)

structure NavierStokes where
  viscosity : ℝ
  velocity : VelocityField
  pressure : PressureField
  velocityGradient : GradientField
  timeDerivative : VelocityField
  pressureGradient : Time → Point3 → Vec3
  laplacianVelocity : Time → Point3 → Vec3
  equation : ∀ t p,
    Vec3.add (timeDerivative t p) (convective velocityGradient velocity t p) =
    Vec3.add (Vec3.smul (-viscosity) (laplacianVelocity t p)) (Vec3.smul (-1) (pressureGradient t p))
  viscosity_pos : 0 < viscosity

structure NSIncompressibility (NS : NavierStokes) where
  proof : incompressible NS.velocityGradient

structure VorticityEvolution where
  viscosity : ℝ
  omega : VorticityField
  timeDerivative : Time → Point3 → Vec3
  convection : Time → Point3 → Vec3
  stretching : Time → Point3 → Vec3
  diffusion : Time → Point3 → Vec3
  equation : ∀ t p,
    Vec3.add (timeDerivative t p) (convection t p) =
    Vec3.add (stretching t p) (Vec3.smul viscosity (diffusion t p))

structure VorticityEnergyBalance where
  energy : Time → ℝ
  dissipation : Time → ℝ
  stretching : Time → ℝ
  viscosity : ℝ
  derivative : Time → ℝ
  identity : ∀ t, (1/2) * derivative t + viscosity * dissipation t = stretching t
  energy_nonneg : ∀ t, 0 ≤ energy t
  dissipation_nonneg : ∀ t, 0 ≤ dissipation t
  viscosity_pos : 0 < viscosity

theorem energy_balance_stretching_lower_bound (B : VorticityEnergyBalance) (t : Time)
    (hderiv : 0 ≤ B.derivative t) : 0 ≤ B.stretching t := by
  have h := B.identity t; nlinarith [B.dissipation_nonneg t, B.viscosity_pos]

theorem energy_balance_derivative_upper_bound (B : VorticityEnergyBalance) (t : Time)
    (hstretch : B.stretching t ≤ 0) : B.derivative t ≤ 0 := by
  have h := B.identity t; nlinarith [B.dissipation_nonneg t, B.viscosity_pos]

theorem energy_balance_dissipation_bound (B : VorticityEnergyBalance) (t : Time) :
    B.viscosity * B.dissipation t ≤ B.stretching t + |((1:ℝ)/2) * B.derivative t| := by
  have h := B.identity t
  have habs : ((1:ℝ)/2) * B.derivative t ≤ |((1:ℝ)/2) * B.derivative t| := le_abs_self _
  linarith

def expDecay (k t : ℝ) : ℝ := Real.exp (-k * t)
theorem expDecay_pos (k t : ℝ) : 0 < expDecay k t := Real.exp_pos _
theorem expDecay_deriv (k t : ℝ) : HasDerivAt (expDecay k) (-k * expDecay k t) t := by
  unfold expDecay
  have h1 : HasDerivAt (fun s => -k * s) (-k) t := (hasDerivAt_id t).const_mul (-k)
  simpa [mul_comm] using h1.exp

def energyDecay (E0 ν t : ℝ) : ℝ := E0 * expDecay (2*ν) t
theorem energyDecay_deriv (E0 ν t : ℝ) :
    HasDerivAt (energyDecay E0 ν) (-2*ν * energyDecay E0 ν t) t := by
  unfold energyDecay
  have h := (expDecay_deriv (2*ν) t).const_mul E0
  have heq : E0 * (-(2*ν) * expDecay (2*ν) t) = -2*ν * (E0 * expDecay (2*ν) t) := by ring
  rwa [heq] at h

theorem energyDecay_nonincreasing (E0 ν t : ℝ) (hE0 : 0 ≤ E0) (hν : 0 ≤ ν) :
    -2*ν * energyDecay E0 ν t ≤ 0 := by
  have hpos : 0 ≤ energyDecay E0 ν t := mul_nonneg hE0 (Real.exp_pos _).le
  nlinarith

def harmonicPosition (k t : ℝ) : ℝ := Real.cos (Real.sqrt k * t)
theorem harmonicPosition_deriv (k t : ℝ) :
    HasDerivAt (harmonicPosition k) (-(Real.sqrt k) * Real.sin (Real.sqrt k * t)) t := by
  unfold harmonicPosition
  have h1 : HasDerivAt (fun s => Real.sqrt k * s) (Real.sqrt k) t := (hasDerivAt_id t).const_mul (Real.sqrt k)
  simpa [mul_comm] using h1.cos

def harmonicVelocity (k t : ℝ) : ℝ := -(Real.sqrt k) * Real.sin (Real.sqrt k * t)
theorem harmonicVelocity_deriv (k t : ℝ) (hk : 0 ≤ k) :
    HasDerivAt (harmonicVelocity k) (-k * harmonicPosition k t) t := by
  unfold harmonicVelocity harmonicPosition
  have h1 : HasDerivAt (fun s => Real.sqrt k * s) (Real.sqrt k) t := (hasDerivAt_id t).const_mul (Real.sqrt k)
  have h3 := (h1.sin).const_mul (-(Real.sqrt k))
  have hsq : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk
  have heq : -(Real.sqrt k) * (Real.cos (Real.sqrt k * t) * Real.sqrt k) = -k * Real.cos (Real.sqrt k * t) := by
    nlinarith [hsq]
  rwa [heq] at h3

theorem harmonic_energy_conserved (k t : ℝ) (hk : 0 ≤ k) :
    HasDerivAt (fun s => (harmonicVelocity k s)^2 + k * (harmonicPosition k s)^2) 0 t := by
  have hp := harmonicPosition_deriv k t
  have hv := harmonicVelocity_deriv k t hk
  have h1 : HasDerivAt (fun s => (harmonicVelocity k s)^2)
      (2 * harmonicVelocity k t * (-k * harmonicPosition k t)) t := by
    simpa using hv.pow 2
  have h2 : HasDerivAt (fun s => k * (harmonicPosition k s)^2)
      (k * (2 * harmonicPosition k t * (-(Real.sqrt k) * Real.sin (Real.sqrt k * t)))) t :=
    (hp.pow 2).const_mul k
  have hsum := h1.add h2
  have hzero : 2 * harmonicVelocity k t * (-k * harmonicPosition k t) +
      k * (2 * harmonicPosition k t * (-(Real.sqrt k) * Real.sin (Real.sqrt k * t))) = 0 := by
    unfold harmonicVelocity; ring
  rwa [hzero] at hsum

-- AWM MARGIN LATTICE: seven-domain bottleneck structure with rescale invariance

inductive Domain7 | Energy | Control | Thermal | Structural | Boundary | Diagnostics | Governance
  deriving DecidableEq, Repr, Fintype

structure MarginVector where
  m : Domain7 → ℝ
  h_floor : ∀ d, 0 ≤ m d

noncomputable def M7 (mv : MarginVector) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty mv.m

theorem M7_le_all (mv : MarginVector) (d : Domain7) : M7 mv ≤ mv.m d :=
  Finset.inf'_le mv.m (Finset.mem_univ d)

theorem M7_nonneg (mv : MarginVector) : 0 ≤ M7 mv := by
  obtain ⟨d, hd⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty mv.m
  unfold M7; rw [hd]; exact mv.h_floor d

noncomputable def rescaleMV (mv : MarginVector) (c : ℝ) (hc : 0 ≤ c) : MarginVector where
  m := fun d => c * mv.m d
  h_floor := fun d => mul_nonneg hc (mv.h_floor d)

theorem rescaleMV_M7 (mv : MarginVector) (c : ℝ) (hc : 0 ≤ c) :
    M7 (rescaleMV mv c hc) = c * M7 mv := by
  obtain ⟨d0, hd0⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty mv.m
  obtain ⟨d1, hd1⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (rescaleMV mv c hc).m
  apply le_antisymm
  · calc M7 (rescaleMV mv c hc) ≤ (rescaleMV mv c hc).m d0 := M7_le_all (rescaleMV mv c hc) d0
      _ = c * mv.m d0 := rfl
      _ = c * M7 mv := by unfold M7; rw [hd0]
  · calc c * M7 mv ≤ c * mv.m d1 := by
          apply mul_le_mul_of_nonneg_left (M7_le_all mv d1) hc
      _ = (rescaleMV mv c hc).m d1 := rfl
      _ = M7 (rescaleMV mv c hc) := by unfold M7; rw [hd1]

theorem rescaleMV_preserves_floor (mv : MarginVector) (c floor : ℝ) (hc : 0 ≤ c)
    (h_floor_lt : floor < M7 mv) (hc_pos : 0 < c) (hc1 : 1 ≤ c) :
    floor < M7 (rescaleMV mv c hc) := by
  rw [rescaleMV_M7]
  have hM7 := M7_nonneg mv
  nlinarith

def bottleneck (mv : MarginVector) : Domain7 :=
  (Finset.exists_mem_eq_inf' Finset.univ_nonempty mv.m).choose

theorem bottleneck_spec (mv : MarginVector) : mv.m (bottleneck mv) = M7 mv :=
  (Finset.exists_mem_eq_inf' Finset.univ_nonempty mv.m).choose_spec.symm

noncomputable def correctBottleneck (mv : MarginVector) (target : ℝ) (h : 0 ≤ target) :
    MarginVector where
  m := fun d => if d = bottleneck mv then target else mv.m d
  h_floor := fun d => by split_ifs with hd; · exact h; · exact mv.h_floor d

theorem correctBottleneck_others_unchanged (mv : MarginVector) (target : ℝ) (h : 0 ≤ target)
    (d : Domain7) (hd : d ≠ bottleneck mv) :
    (correctBottleneck mv target h).m d = mv.m d := by unfold correctBottleneck; simp [hd]

theorem correctBottleneck_at_target (mv : MarginVector) (target : ℝ) (h : 0 ≤ target) :
    (correctBottleneck mv target h).m (bottleneck mv) = target := by unfold correctBottleneck; simp

theorem correctBottleneck_M7 (mv : MarginVector) (target : ℝ) (h : 0 ≤ target)
    (h_dom : ∀ d, d ≠ bottleneck mv → target ≤ mv.m d) :
    M7 (correctBottleneck mv target h) = target := by
  apply le_antisymm
  · have hle := M7_le_all (correctBottleneck mv target h) (bottleneck mv)
    rwa [correctBottleneck_at_target] at hle
  · apply Finset.le_inf'
    intro d _
    by_cases hd : d = bottleneck mv
    · rw [hd, correctBottleneck_at_target]
    · rw [correctBottleneck_others_unchanged mv target h d hd]; exact h_dom d hd

-- AWM ENERGY TRIAD: dissipation / stretching / margin, nonnegative-sum aggregate

structure AWMTriad where
  dissip : ℝ
  stretch : ℝ
  margin : ℝ
  h_dissip : 0 ≤ dissip
  h_stretch : 0 ≤ stretch
  h_margin : 0 ≤ margin

def AWMTriad.total (T : AWMTriad) : ℝ := T.dissip + T.stretch + T.margin

theorem AWMTriad.total_nonneg (T : AWMTriad) : 0 ≤ T.total :=
  add_nonneg (add_nonneg T.h_dissip T.h_stretch) T.h_margin

theorem AWMTriad.total_mono_dissip (T : AWMTriad) (d' : ℝ) (hd' : 0 ≤ d') (h : T.dissip ≤ d') :
    T.total ≤ d' + T.stretch + T.margin := by unfold AWMTriad.total; linarith

structure AWMParameters where
  viscosity : ℝ
  theta : ℝ
  feedback : Time → ℝ
  viscosity_pos : 0 < viscosity
  theta_nonneg : 0 ≤ theta
  theta_lt_one : theta < 1

def dissipationMargin (p : AWMParameters) (D : ℝ) : ℝ := (1 - p.theta) * p.viscosity * D

theorem dissipationMargin_pos (p : AWMParameters) (D : ℝ) (hD : 0 < D) :
    0 < dissipationMargin p D := by
  unfold dissipationMargin
  have h1 : 0 < 1 - p.theta := by linarith [p.theta_lt_one]
  positivity

theorem dissipationMargin_mono (p : AWMParameters) (D1 D2 : ℝ) (h : D1 ≤ D2) :
    dissipationMargin p D1 ≤ dissipationMargin p D2 := by
  unfold dissipationMargin
  have h1 : 0 ≤ 1 - p.theta := by linarith [p.theta_lt_one]
  nlinarith [p.viscosity_pos.le]

theorem dissipationMargin_zero (p : AWMParameters) : dissipationMargin p 0 = 0 := by
  unfold dissipationMargin; ring

theorem dissipationMargin_additive (p : AWMParameters) (D1 D2 : ℝ) :
    dissipationMargin p (D1 + D2) = dissipationMargin p D1 + dissipationMargin p D2 := by
  unfold dissipationMargin; ring

theorem dissipationMargin_triple_product_mono (p1 p2 : AWMParameters) (D : ℝ) (hD : 0 ≤ D)
    (hv : p1.viscosity ≤ p2.viscosity) (hθ : p2.theta ≤ p1.theta) :
    dissipationMargin p1 D ≤ dissipationMargin p2 D := by
  unfold dissipationMargin
  have h1 : 0 ≤ 1 - p1.theta := by linarith [p1.theta_lt_one]
  have h2 : 1 - p1.theta ≤ 1 - p2.theta := by linarith
  nlinarith [p1.viscosity_pos.le, p2.viscosity_pos.le]

inductive EvidenceStatus | proved | derived | interface | open_

structure AnalyticEvidence where
  name : String
  status : EvidenceStatus
  statement : String

def RealFoundationObligation : AnalyticEvidence :=
  {name := "Real foundation", status := EvidenceStatus.open_,
   statement := "Construct genuine real-number completeness and continuous-analysis foundations."}
def LebesgueFoundationObligation : AnalyticEvidence :=
  {name := "Lebesgue integration", status := EvidenceStatus.open_,
   statement := "Construct continuous R3 measure and integration."}
def LpFoundationObligation : AnalyticEvidence :=
  {name := "Lp spaces", status := EvidenceStatus.open_,
   statement := "Construct genuine continuous Lp spaces and norms on R3."}
def HolderObligation : AnalyticEvidence :=
  {name := "Holder inequality", status := EvidenceStatus.open_,
   statement := "Prove continuous Holder inequality."}
def SobolevObligation : AnalyticEvidence :=
  {name := "Sobolev embedding", status := EvidenceStatus.open_,
   statement := "Prove the required three-dimensional Sobolev embedding/interpolation."}
def BiotSavartObligation : AnalyticEvidence :=
  {name := "Biot-Savart", status := EvidenceStatus.open_,
   statement := "Derive velocity-vorticity reconstruction and differentiation."}
def SingularIntegralObligation : AnalyticEvidence :=
  {name := "Calderon-Zygmund", status := EvidenceStatus.open_,
   statement := "Prove required Lp singular-integral bounds."}
def CriticalStretchingObligation : AnalyticEvidence :=
  {name := "Critical vortex stretching", status := EvidenceStatus.open_,
   statement := "Prove |int omega^T S omega| <= theta*nu*||grad omega||_2^2 + G(t)*||omega||_2^2 with theta<1 and G locally integrable."}
def ContinuationObligation : AnalyticEvidence :=
  {name := "Global continuation", status := EvidenceStatus.open_,
   statement := "Prove critical control excludes finite-time loss of smoothness."}

structure FeedbackIntegrability where
  coefficient : Time → ℝ
  finite : Prop
  measurable : Prop
  integrable : Prop

structure CriticalVortexStretchingClosure where
  viscosity : ℝ
  theta : ℝ
  feedback : Time → ℝ
  thetaCondition : theta < 1
  stretchingBound : Prop
  feedbackIntegrable : FeedbackIntegrability

structure ClosedEnergyInequality where
  balance : VorticityEnergyBalance
  closure : CriticalVortexStretchingClosure
  inequality : Prop
  positiveReserve : Prop

structure GronwallCertificate where
  inequality : ClosedEnergyInequality
  integralCoefficient : Prop
  finiteBound : Prop

structure ContinuationCertificate where
  finiteVorticityControl : Prop
  regularityCriterion : Prop
  continuation : Prop

structure GlobalRegularityCertificate where
  localExistence : Prop
  closedEnergy : Prop
  continuation : ContinuationCertificate
  globalRegularity : Prop

structure SingularIntegralOperator where
  kernel : Point3 → Point3 → ℝ
  cancellation : Prop
  homogeneity : Prop
  principalValue : Prop

structure HolderTriple where
  p : ℝ; q : ℝ; r : ℝ
  reciprocal : 1/p + 1/q = 1/r

def stdHolderTriple : HolderTriple := {p := 2, q := 2, r := 1, reciprocal := by norm_num}

structure HolderEstimate where
  triple : HolderTriple
  estimate : Prop

structure InterpolationEstimate where
  lower : ℝ; upper : ℝ; target : ℝ; parameter : ℝ
  estimate : Prop

structure SobolevEmbedding where
  sourceExponent : ℝ
  targetExponent : ℝ
  derivativeOrder : ℕ
  dimension : ℕ
  embedding : Prop

structure BiotSavartThreeDimensional where
  omega : VorticityField
  velocity : VelocityField
  kernel : Point3 → Point3 → Vec3
  singularity : Prop
  divergenceFree : Prop
  curlRecovery : Prop
  decay : Prop

structure GradientBiotSavart where
  velocity : VelocityField
  vorticity : VorticityField
  gradient : GradientField
  singularOperator : Prop
  CalderonZygmundRepresentation : Prop

structure StretchingEstimate where
  constant : ℝ
  constant_pos : 0 < constant
  estimate : Prop

structure CriticalScalingData where
  lambda : ℝ
  lambda_pos : 0 < lambda
  velocityExponent : ℝ
  vorticityExponent : ℝ
  timeExponent : ℝ
  spatialExponent : ℝ
  scalingInvariant : Prop

def CriticalVorticityExponent : ℝ := 3/2

structure CriticalClosurePipeline where
  scaling : CriticalScalingData
  BiotSavart : BiotSavartThreeDimensional
  gradient : GradientBiotSavart
  holder : HolderEstimate
  interpolation : InterpolationEstimate
  Sobolev : SobolevEmbedding
  stretching : StretchingEstimate
  closure : CriticalVortexStretchingClosure
  Gronwall : GronwallCertificate
  continuation : ContinuationCertificate

structure AWMCoreTarget where
  PDE : NavierStokes
  vorticity : VorticityEvolution
  energy : VorticityEnergyBalance
  critical : CriticalClosurePipeline
  global : GlobalRegularityCertificate

def AWMCoreCompletionTarget : Prop := Nonempty AWMCoreTarget

structure AWMStatus where
  algebra : EvidenceStatus
  PDE : EvidenceStatus
  continuousAnalysis : EvidenceStatus
  BiotSavart : EvidenceStatus
  singularIntegrals : EvidenceStatus
  criticalInterpolation : EvidenceStatus
  vortexStretching : EvidenceStatus
  continuation : EvidenceStatus

def CurrentAWMStatus : AWMStatus :=
  {algebra := EvidenceStatus.derived, PDE := EvidenceStatus.interface,
   continuousAnalysis := EvidenceStatus.open_, BiotSavart := EvidenceStatus.open_,
   singularIntegrals := EvidenceStatus.open_, criticalInterpolation := EvidenceStatus.open_,
   vortexStretching := EvidenceStatus.open_, continuation := EvidenceStatus.open_}

structure AWMLock where
  normSq_nn : ∀ a : Vec3, 0 ≤ Vec3.normSq a
  cauchy_schwarz : ∀ a b : Vec3, (Vec3.dot a b) ^ 2 ≤ Vec3.normSq a * Vec3.normSq b
  triangle_ineq : ∀ a b : Vec3,
    Real.sqrt (Vec3.normSq (Vec3.add a b)) ≤ Real.sqrt (Vec3.normSq a) + Real.sqrt (Vec3.normSq b)
  frobeniusSq_nn : ∀ A : Mat3, 0 ≤ Mat3.frobeniusSq A
  mulVec_bound : ∀ (A : Mat3) (v : Vec3), Vec3.normSq (Mat3.mulVec A v) ≤ Mat3.frobeniusSq A * Vec3.normSq v
  mul_mulVec_assoc : ∀ (A B : Mat3) (v : Vec3), Mat3.mulVec (Mat3.mul A B) v = Mat3.mulVec A (Mat3.mulVec B v)
  trace_mul_comm : ∀ A B : Mat3, Mat3.trace (Mat3.mul A B) = Mat3.trace (Mat3.mul B A)
  trace_split : ∀ A : Mat3, Mat3.add (Mat3.symmetricPart A) (Mat3.antisymmetricPart A) = A
  transpose_involutive : ∀ A : Mat3, Mat3.transpose (Mat3.transpose A) = A
  margin_pos : ∀ (p : AWMParameters) (D : ℝ), 0 < D → 0 < dissipationMargin p D
  margin_additive : ∀ (p : AWMParameters) (D1 D2 : ℝ),
    dissipationMargin p (D1 + D2) = dissipationMargin p D1 + dissipationMargin p D2
  margin_triple_mono : ∀ (p1 p2 : AWMParameters) (D : ℝ), 0 ≤ D → p1.viscosity ≤ p2.viscosity →
    p2.theta ≤ p1.theta → dissipationMargin p1 D ≤ dissipationMargin p2 D
  energy_stretch_lb : ∀ (B : VorticityEnergyBalance) (t : Time), 0 ≤ B.derivative t → 0 ≤ B.stretching t
  strain_rotation_split : ∀ (G : GradientField) (t : Time) (p : Point3),
    Mat3.add (strain G t p) (rotation G t p) = G t p
  convective_bound : ∀ (G : GradientField) (u : VelocityField) (t : Time) (p : Point3),
    Vec3.normSq (convective G u t p) ≤ Mat3.frobeniusSq (G t p) * Vec3.normSq (u t p)
  incompressible_zero_field : incompressible (fun _ _ => Mat3.zero)
  energyDecay_eq : ∀ (E0 ν t : ℝ), HasDerivAt (energyDecay E0 ν) (-2*ν * energyDecay E0 ν t) t
  energyDecay_decreasing : ∀ (E0 ν t : ℝ), 0 ≤ E0 → 0 ≤ ν → -2*ν * energyDecay E0 ν t ≤ 0
  harmonicPosition_eq : ∀ (k t : ℝ),
    HasDerivAt (harmonicPosition k) (-(Real.sqrt k) * Real.sin (Real.sqrt k * t)) t
  harmonicVelocity_eq : ∀ (k t : ℝ), 0 ≤ k → HasDerivAt (harmonicVelocity k) (-k * harmonicPosition k t) t
  harmonic_energy_conserved : ∀ (k t : ℝ), 0 ≤ k →
    HasDerivAt (fun s => (harmonicVelocity k s)^2 + k * (harmonicPosition k s)^2) 0 t
  M7_nonneg : ∀ mv : MarginVector, 0 ≤ M7 mv
  M7_le_all : ∀ (mv : MarginVector) (d : Domain7), M7 mv ≤ mv.m d
  rescaleMV_M7 : ∀ (mv : MarginVector) (c : ℝ) (hc : 0 ≤ c), M7 (rescaleMV mv c hc) = c * M7 mv
  correctBottleneck_M7 : ∀ (mv : MarginVector) (target : ℝ) (h : 0 ≤ target),
    (∀ d, d ≠ bottleneck mv → target ≤ mv.m d) → M7 (correctBottleneck mv target h) = target
  triad_total_nn : ∀ T : AWMTriad, 0 ≤ T.total

def AWMLockCert : AWMLock where
  normSq_nn := Vec3.normSq_nonneg
  cauchy_schwarz := Vec3.cauchy_schwarz
  triangle_ineq := Vec3.triangle_ineq
  frobeniusSq_nn := Mat3.frobeniusSq_nonneg
  mulVec_bound := Mat3.mulVec_normSq_le
  mul_mulVec_assoc := Mat3.mul_mulVec
  trace_mul_comm := Mat3.trace_mul_comm
  trace_split := Mat3.add_symmetric_antisymmetric
  transpose_involutive := Mat3.transpose_transpose
  margin_pos := dissipationMargin_pos
  margin_additive := dissipationMargin_additive
  margin_triple_mono := dissipationMargin_triple_product_mono
  energy_stretch_lb := energy_balance_stretching_lower_bound
  strain_rotation_split := strain_add_rotation
  convective_bound := convective_normSq_bound
  incompressible_zero_field := incompressible_zero
  energyDecay_eq := energyDecay_deriv
  energyDecay_decreasing := energyDecay_nonincreasing
  harmonicPosition_eq := harmonicPosition_deriv
  harmonicVelocity_eq := harmonicVelocity_deriv
  harmonic_energy_conserved := harmonic_energy_conserved
  M7_nonneg := M7_nonneg
  M7_le_all := M7_le_all
  rescaleMV_M7 := rescaleMV_M7
  correctBottleneck_M7 := correctBottleneck_M7
  triad_total_nn := AWMTriad.total_nonneg

end AWM_NS_Master
