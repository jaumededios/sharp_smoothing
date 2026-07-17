import JoseSmoothest.SpecialFunctions.PellAbel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Polynomial

/-!
# Real phases for polynomial Pell--Abel solutions

This file turns a supplied real Pell--Abel solution into a cosine of a
strictly increasing phase.  Endpoint integrability is kept as explicit input,
so the result is independent of any particular factorization of the Pell
weight at the endpoints.
-/

noncomputable section

namespace Polynomial

open Real Set MeasureTheory intervalIntegral

/-- Sign, positivity, and endpoint-integrability data for a real branch of a
polynomial Pell equation. -/
structure RealPellPhaseInterval (D A : ℝ[X]) where
  /-- The left endpoint, which is a branch point of `D`. -/
  left : ℝ
  /-- The right endpoint of the real phase interval. -/
  right : ℝ
  left_lt_right : left < right
  eval_D_left : D.eval left = 0
  neg_D : ∀ x ∈ Ioo left right, D.eval x < 0
  /-- The sign which makes the differential numerator positive. -/
  orientation : ℝ
  orientation_sq : orientation ^ 2 = 1
  numerator_pos : ∀ x ∈ Ioo left right, 0 < orientation * A.eval x
  density_intervalIntegrable :
    IntervalIntegrable
      (fun x ↦ orientation * A.eval x / √(-D.eval x))
      volume left right

namespace RealPellPhaseInterval

variable {D A : ℝ[X]} (I : RealPellPhaseInterval D A)

/-- The positive real phase density on the open interval. -/
def density (x : ℝ) : ℝ :=
  I.orientation * A.eval x / √(-D.eval x)

/-- The phase, anchored to be zero at the left endpoint. -/
def phase (x : ℝ) : ℝ :=
  ∫ t in I.left..x, I.density t

/-- The real companion coordinate on the cut. -/
def companion (_I : RealPellPhaseInterval D A)
    (s : PellAbelSolution D) (x : ℝ) : ℝ :=
  √(-D.eval x) * s.Q.eval x

theorem orientation_ne_zero : I.orientation ≠ 0 := by
  intro h
  have hsquare := I.orientation_sq
  rw [h] at hsquare
  norm_num at hsquare

theorem orientation_eq_one_or_neg_one :
    I.orientation = 1 ∨ I.orientation = -1 :=
  sq_eq_one_iff.mp I.orientation_sq

private theorem continuousAt_density {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    ContinuousAt I.density x := by
  apply ContinuousAt.div
  · exact continuousAt_const.mul A.continuous.continuousAt
  · exact D.continuous.continuousAt.neg.sqrt
  · exact (sqrt_pos.2 (by linarith [I.neg_D x hx])).ne'

theorem continuousOn_phase :
    ContinuousOn I.phase (Icc I.left I.right) := by
  change ContinuousOn (fun x ↦ ∫ t in I.left..x, I.density t)
    (Icc I.left I.right)
  simpa only [phase, density, uIcc_of_le I.left_lt_right.le] using
    intervalIntegral.continuousOn_primitive_interval'
      I.density_intervalIntegrable (show I.left ∈ uIcc I.left I.right by simp)

@[simp] theorem phase_left : I.phase I.left = 0 := by
  simp [phase]

theorem hasDerivAt_phase {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    HasDerivAt I.phase (I.density x) x := by
  have hint : IntervalIntegrable I.density volume I.left x := by
    apply I.density_intervalIntegrable.mono_set
    rw [uIcc_of_le hx.1.le, uIcc_of_le I.left_lt_right.le]
    exact Icc_subset_Icc_right hx.2.le
  have hmeas : StronglyMeasurable I.density := by
    apply Measurable.stronglyMeasurable
    exact (measurable_const.mul A.continuous.measurable).div
      D.continuous.measurable.neg.sqrt
  exact intervalIntegral.integral_hasDerivAt_right hint
    hmeas.stronglyMeasurableAtFilter (I.continuousAt_density hx)

theorem density_pos {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    0 < I.density x := by
  exact div_pos (I.numerator_pos x hx) (sqrt_pos.2 (by linarith [I.neg_D x hx]))

theorem strictMonoOn_phase :
    StrictMonoOn I.phase (Icc I.left I.right) := by
  apply strictMonoOn_of_deriv_pos (D := Icc I.left I.right) (convex_Icc _ _)
    I.continuousOn_phase
  intro x hx
  rw [interior_Icc] at hx
  exact (I.hasDerivAt_phase hx).deriv ▸ I.density_pos hx

theorem phaseSign_sq (s : PellAbelSolution D) :
    (s.P.eval I.left) ^ 2 = 1 := by
  have h := congrArg (eval I.left) s.equation
  simp only [eval_sub, eval_pow, eval_mul, eval_one, I.eval_D_left, zero_mul,
    sub_zero] at h
  exact h

theorem phaseSign_eq_one_or_neg_one (s : PellAbelSolution D) :
    s.P.eval I.left = 1 ∨ s.P.eval I.left = -1 :=
  sq_eq_one_iff.mp (I.phaseSign_sq s)

/-- The second differential identity obtained by differentiating and
cancelling the nonzero Pell denominator. -/
private theorem companionPolynomialIdentity
    {N : ℕ} (s : PellAbelSolution D) (hQ : s.Q ≠ 0)
    (hderiv : derivative s.P = C (N : ℝ) * A * s.Q) :
    derivative D * s.Q + C (2 : ℝ) * D * derivative s.Q =
      C ((2 : ℝ) * N) * A * s.P := by
  have heq := congrArg derivative s.equation
  simp only [derivative_sub, derivative_pow, derivative_mul, derivative_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one] at heq
  apply mul_right_cancel₀ hQ
  calc
    (derivative D * s.Q + C (2 : ℝ) * D * derivative s.Q) * s.Q =
        derivative D * s.Q ^ 2 + D * (C 2 * s.Q * derivative s.Q) := by ring
    _ = C 2 * s.P * derivative s.P := (sub_eq_zero.mp heq).symm
    _ = (C ((2 : ℝ) * N) * A * s.P) * s.Q := by
      rw [hderiv, map_mul]
      ring

private theorem hasDerivAt_eval_P
    {N : ℕ} (s : PellAbelSolution D)
    (hderiv : derivative s.P = C (N : ℝ) * A * s.Q) (x : ℝ) :
    HasDerivAt (fun y ↦ s.P.eval y) ((N : ℝ) * A.eval x * s.Q.eval x) x := by
  simpa only [hderiv, eval_mul, eval_C] using s.P.hasDerivAt x

private theorem deriv_companion
    {N : ℕ} (s : PellAbelSolution D) (hQ : s.Q ≠ 0)
    (hderiv : derivative s.P = C (N : ℝ) * A * s.Q)
    {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    deriv (fun y ↦ √(-D.eval y) * s.Q.eval y) x =
      -((N : ℝ) * A.eval x / √(-D.eval x) * s.P.eval x) := by
  have hD : D.eval x < 0 := I.neg_D x hx
  have hroot : √(-D.eval x) ≠ 0 := (sqrt_pos.2 (by linarith)).ne'
  have hsq : √(-D.eval x) ^ 2 = -D.eval x := Real.sq_sqrt (by linarith)
  have hsqrt := (D.hasDerivAt x).neg.sqrt (neg_ne_zero.mpr (ne_of_lt hD))
  have hprod := hsqrt.mul (s.Q.hasDerivAt x)
  have hcomp := companionPolynomialIdentity s hQ hderiv
  have hev := congrArg (eval x) hcomp
  simp only [eval_add, eval_mul, eval_C] at hev
  have hcoeff :
      (-(derivative D).eval x / (2 * √(-D.eval x))) * s.Q.eval x +
          √(-D.eval x) * (derivative s.Q).eval x =
        -((N : ℝ) * A.eval x / √(-D.eval x) * s.P.eval x) := by
    field_simp [hroot]
    rw [hsq]
    linear_combination -hev
  exact hprod.deriv.trans hcoeff

private def angle (N : ℕ) (x : ℝ) : ℝ :=
  (N : ℝ) * I.phase x

private def cosInvariant (N : ℕ) (s : PellAbelSolution D) (x : ℝ) : ℝ :=
  s.P.eval x * Real.cos (I.angle N x) -
    I.orientation * I.companion s x * Real.sin (I.angle N x)

private def sinInvariant (N : ℕ) (s : PellAbelSolution D) (x : ℝ) : ℝ :=
  s.P.eval x * Real.sin (I.angle N x) +
    I.orientation * I.companion s x * Real.cos (I.angle N x)

private theorem continuousOn_angle (N : ℕ) :
    ContinuousOn (I.angle N) (Icc I.left I.right) :=
  continuousOn_const.mul I.continuousOn_phase

private theorem continuous_companion (s : PellAbelSolution D) :
    Continuous (I.companion s) := by
  exact D.continuous.neg.sqrt.mul s.Q.continuous

private theorem continuousOn_cosInvariant (N : ℕ) (s : PellAbelSolution D) :
    ContinuousOn (I.cosInvariant N s) (Icc I.left I.right) := by
  have hcos : ContinuousOn (fun x ↦ Real.cos (I.angle N x))
      (Icc I.left I.right) := Real.continuous_cos.comp_continuousOn (I.continuousOn_angle N)
  have hsin : ContinuousOn (fun x ↦ Real.sin (I.angle N x))
      (Icc I.left I.right) := Real.continuous_sin.comp_continuousOn (I.continuousOn_angle N)
  exact (s.P.continuous.continuousOn.mul hcos).sub
    ((continuousOn_const.mul (I.continuous_companion s).continuousOn).mul hsin)

private theorem continuousOn_sinInvariant (N : ℕ) (s : PellAbelSolution D) :
    ContinuousOn (I.sinInvariant N s) (Icc I.left I.right) := by
  have hcos : ContinuousOn (fun x ↦ Real.cos (I.angle N x))
      (Icc I.left I.right) := Real.continuous_cos.comp_continuousOn (I.continuousOn_angle N)
  have hsin : ContinuousOn (fun x ↦ Real.sin (I.angle N x))
      (Icc I.left I.right) := Real.continuous_sin.comp_continuousOn (I.continuousOn_angle N)
  exact (s.P.continuous.continuousOn.mul hsin).add
    ((continuousOn_const.mul (I.continuous_companion s).continuousOn).mul hcos)

private theorem hasDerivAt_angle
    (N : ℕ) {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    HasDerivAt (I.angle N) ((N : ℝ) * I.density x) x := by
  change HasDerivAt (fun y ↦ (N : ℝ) * I.phase y) ((N : ℝ) * I.density x) x
  exact (I.hasDerivAt_phase hx).const_mul (N : ℝ)

private theorem differentiableAt_companion
    (s : PellAbelSolution D) {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    DifferentiableAt ℝ (I.companion s) x := by
  have hD : D.eval x < 0 := I.neg_D x hx
  have hsqrt := (D.hasDerivAt x).neg.sqrt (neg_ne_zero.mpr (ne_of_lt hD))
  change DifferentiableAt ℝ (fun y ↦ √(-D.eval y) * s.Q.eval y) x
  exact hsqrt.differentiableAt.mul (s.Q.hasDerivAt x).differentiableAt

private theorem differentiableAt_cosInvariant
    (N : ℕ) (s : PellAbelSolution D) {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    DifferentiableAt ℝ (I.cosInvariant N s) x := by
  have hP := (s.P.hasDerivAt x).differentiableAt
  have hangle := (I.hasDerivAt_angle N hx).differentiableAt
  exact (hP.mul hangle.cos).sub
    ((differentiableAt_const (c := I.orientation).mul (I.differentiableAt_companion s hx)).mul
      hangle.sin)

private theorem differentiableAt_sinInvariant
    (N : ℕ) (s : PellAbelSolution D) {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    DifferentiableAt ℝ (I.sinInvariant N s) x := by
  have hP := (s.P.hasDerivAt x).differentiableAt
  have hangle := (I.hasDerivAt_angle N hx).differentiableAt
  exact (hP.mul hangle.sin).add
    ((differentiableAt_const (c := I.orientation).mul (I.differentiableAt_companion s hx)).mul
      hangle.cos)

private theorem deriv_cosInvariant_eq_zero
    {N : ℕ} (s : PellAbelSolution D) (hQ : s.Q ≠ 0)
    (hderiv : derivative s.P = C (N : ℝ) * A * s.Q)
    {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    deriv (I.cosInvariant N s) x = 0 := by
  have hP := hasDerivAt_eval_P s hderiv x
  have hangle := I.hasDerivAt_angle N hx
  have hR := (I.differentiableAt_companion s hx).hasDerivAt
  have hRderiv : deriv (I.companion s) x =
      -((N : ℝ) * A.eval x / √(-D.eval x) * s.P.eval x) := by
    change deriv (fun y ↦ √(-D.eval y) * s.Q.eval y) x = _
    exact I.deriv_companion s hQ hderiv hx
  rw [hRderiv] at hR
  have hF := (hP.mul hangle.cos).sub ((hR.const_mul I.orientation).mul hangle.sin)
  have hroot : √(-D.eval x) ≠ 0 :=
    (sqrt_pos.2 (by linarith [I.neg_D x hx])).ne'
  have hsquare : I.orientation * I.orientation = 1 := by
    simpa only [pow_two] using I.orientation_sq
  change HasDerivAt (I.cosInvariant N s) _ x at hF
  rw [hF.deriv]
  simp only [density, angle, companion]
  field_simp [hroot]
  ring_nf at hsquare ⊢
  rw [hsquare]
  ring

private theorem deriv_sinInvariant_eq_zero
    {N : ℕ} (s : PellAbelSolution D) (hQ : s.Q ≠ 0)
    (hderiv : derivative s.P = C (N : ℝ) * A * s.Q)
    {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    deriv (I.sinInvariant N s) x = 0 := by
  have hP := hasDerivAt_eval_P s hderiv x
  have hangle := I.hasDerivAt_angle N hx
  have hR := (I.differentiableAt_companion s hx).hasDerivAt
  have hRderiv : deriv (I.companion s) x =
      -((N : ℝ) * A.eval x / √(-D.eval x) * s.P.eval x) := by
    change deriv (fun y ↦ √(-D.eval y) * s.Q.eval y) x = _
    exact I.deriv_companion s hQ hderiv hx
  rw [hRderiv] at hR
  have hG := (hP.mul hangle.sin).add ((hR.const_mul I.orientation).mul hangle.cos)
  have hroot : √(-D.eval x) ≠ 0 :=
    (sqrt_pos.2 (by linarith [I.neg_D x hx])).ne'
  have hsquare : I.orientation * I.orientation = 1 := by
    simpa only [pow_two] using I.orientation_sq
  change HasDerivAt (I.sinInvariant N s) _ x at hG
  rw [hG.deriv]
  simp only [density, angle, companion]
  field_simp [hroot]
  ring_nf at hsquare ⊢
  rw [hsquare]
  ring

private theorem cosInvariant_eq_phaseSign
    {N : ℕ} (s : PellAbelSolution D) (hQ : s.Q ≠ 0)
    (hderiv : derivative s.P = C (N : ℝ) * A * s.Q)
    {x : ℝ} (hx : x ∈ Icc I.left I.right) :
    I.cosInvariant N s x = s.P.eval I.left := by
  let c : ℝ := (I.left + I.right) / 2
  have hc : c ∈ Ioo I.left I.right := by
    dsimp only [c]
    constructor <;> linarith [I.left_lt_right]
  have hdiff : DifferentiableOn ℝ (I.cosInvariant N s) (Ioo I.left I.right) :=
    fun _ hy ↦ (I.differentiableAt_cosInvariant N s hy).differentiableWithinAt
  have hzero : EqOn (deriv (I.cosInvariant N s)) 0 (Ioo I.left I.right) :=
    fun _ hy ↦ I.deriv_cosInvariant_eq_zero s hQ hderiv hy
  have hopen : EqOn (I.cosInvariant N s)
      (fun _ ↦ I.cosInvariant N s c) (Ioo I.left I.right) := by
    intro y hy
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero hy hc
  have hclosed : EqOn (I.cosInvariant N s)
      (fun _ ↦ I.cosInvariant N s c) (Icc I.left I.right) := by
    apply hopen.of_subset_closure (I.continuousOn_cosInvariant N s) continuousOn_const
      Ioo_subset_Icc_self
    rw [closure_Ioo (ne_of_lt I.left_lt_right)]
  have hleft : I.left ∈ Icc I.left I.right := ⟨le_rfl, I.left_lt_right.le⟩
  calc
    I.cosInvariant N s x = I.cosInvariant N s c := hclosed hx
    _ = I.cosInvariant N s I.left := (hclosed hleft).symm
    _ = s.P.eval I.left := by
      simp [cosInvariant, angle, companion, I.eval_D_left]

private theorem sinInvariant_eq_zero
    {N : ℕ} (s : PellAbelSolution D) (hQ : s.Q ≠ 0)
    (hderiv : derivative s.P = C (N : ℝ) * A * s.Q)
    {x : ℝ} (hx : x ∈ Icc I.left I.right) :
    I.sinInvariant N s x = 0 := by
  let c : ℝ := (I.left + I.right) / 2
  have hc : c ∈ Ioo I.left I.right := by
    dsimp only [c]
    constructor <;> linarith [I.left_lt_right]
  have hdiff : DifferentiableOn ℝ (I.sinInvariant N s) (Ioo I.left I.right) :=
    fun _ hy ↦ (I.differentiableAt_sinInvariant N s hy).differentiableWithinAt
  have hzero : EqOn (deriv (I.sinInvariant N s)) 0 (Ioo I.left I.right) :=
    fun _ hy ↦ I.deriv_sinInvariant_eq_zero s hQ hderiv hy
  have hopen : EqOn (I.sinInvariant N s)
      (fun _ ↦ I.sinInvariant N s c) (Ioo I.left I.right) := by
    intro y hy
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero hy hc
  have hclosed : EqOn (I.sinInvariant N s)
      (fun _ ↦ I.sinInvariant N s c) (Icc I.left I.right) := by
    apply hopen.of_subset_closure (I.continuousOn_sinInvariant N s) continuousOn_const
      Ioo_subset_Icc_self
    rw [closure_Ioo (ne_of_lt I.left_lt_right)]
  have hleft : I.left ∈ Icc I.left I.right := ⟨le_rfl, I.left_lt_right.le⟩
  calc
    I.sinInvariant N s x = I.sinInvariant N s c := hclosed hx
    _ = I.sinInvariant N s I.left := (hclosed hleft).symm
    _ = 0 := by simp [sinInvariant, angle, companion, I.eval_D_left]

theorem pell_eval_eq_cos_phase
    {N : ℕ} (s : PellAbelSolution D)
    (hQ : s.Q ≠ 0)
    (hderiv : derivative s.P = C (N : ℝ) * A * s.Q)
    {x : ℝ} (hx : x ∈ Icc I.left I.right) :
    s.P.eval x =
      s.P.eval I.left * Real.cos ((N : ℝ) * I.phase x) := by
  have hF := I.cosInvariant_eq_phaseSign s hQ hderiv hx
  have hG := I.sinInvariant_eq_zero s hQ hderiv hx
  rw [cosInvariant, angle] at hF
  rw [sinInvariant, angle] at hG
  calc
    s.P.eval x = s.P.eval x *
        (Real.sin ((N : ℝ) * I.phase x) ^ 2 +
          Real.cos ((N : ℝ) * I.phase x) ^ 2) := by
      rw [Real.sin_sq_add_cos_sq]
      ring
    _ = (s.P.eval x * Real.cos ((N : ℝ) * I.phase x) -
          I.orientation * I.companion s x * Real.sin ((N : ℝ) * I.phase x)) *
            Real.cos ((N : ℝ) * I.phase x) +
        (s.P.eval x * Real.sin ((N : ℝ) * I.phase x) +
          I.orientation * I.companion s x * Real.cos ((N : ℝ) * I.phase x)) *
            Real.sin ((N : ℝ) * I.phase x) := by ring
    _ = s.P.eval I.left * Real.cos ((N : ℝ) * I.phase x) := by
      rw [hF, hG]
      ring

theorem pell_companion_eq_sin_phase
    {N : ℕ} (s : PellAbelSolution D)
    (hQ : s.Q ≠ 0)
    (hderiv : derivative s.P = C (N : ℝ) * A * s.Q)
    {x : ℝ} (hx : x ∈ Icc I.left I.right) :
    I.companion s x =
      -I.orientation * s.P.eval I.left *
        Real.sin ((N : ℝ) * I.phase x) := by
  have hF := I.cosInvariant_eq_phaseSign s hQ hderiv hx
  have hG := I.sinInvariant_eq_zero s hQ hderiv hx
  rw [cosInvariant, angle] at hF
  rw [sinInvariant, angle] at hG
  calc
    I.companion s x = I.orientation ^ 2 * I.companion s x *
        (Real.sin ((N : ℝ) * I.phase x) ^ 2 +
          Real.cos ((N : ℝ) * I.phase x) ^ 2) := by
      rw [I.orientation_sq, Real.sin_sq_add_cos_sq]
      ring
    _ = -I.orientation *
          (s.P.eval x * Real.cos ((N : ℝ) * I.phase x) -
            I.orientation * I.companion s x * Real.sin ((N : ℝ) * I.phase x)) *
            Real.sin ((N : ℝ) * I.phase x) +
        I.orientation *
          (s.P.eval x * Real.sin ((N : ℝ) * I.phase x) +
            I.orientation * I.companion s x * Real.cos ((N : ℝ) * I.phase x)) *
            Real.cos ((N : ℝ) * I.phase x) := by ring
    _ = -I.orientation * s.P.eval I.left *
        Real.sin ((N : ℝ) * I.phase x) := by
      rw [hF, hG]
      ring

end RealPellPhaseInterval

end Polynomial
