import JoseSmoothest.Kernel
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.Count

/-!
# Fourier representation of finite convolution

This file builds a Fourier equivalence between complex `L²` for counting measure on `ℤ`
and complex `L²` on the circle. It then identifies every iterated-difference convolution
norm with its scalar multiplier norm.

## Main definitions

* `JoseSmoothest.kernelFourierTransform`: the real Fourier symbol of a finite kernel.
* `JoseSmoothest.IsAdmissibleKernel`: the hypotheses on kernels in Theorem 1.4.
* `JoseSmoothest.differenceSmoothness`: the norm of an iterated difference after averaging.
* `JoseSmoothest.differenceMultiplierNorm`: the corresponding multiplier supremum.
* `JoseSmoothest.fourthOrderSmoothness`: the norm of fourth difference after averaging.
* `JoseSmoothest.fourthOrderMultiplierNorm`: the supremum of the scalar multiplier.

## Main results

* `JoseSmoothest.differenceSmoothness_eq_multiplierNorm`: the general multiplier identity.
* `JoseSmoothest.differenceMultiplier_le_smoothness`: the general pointwise multiplier bound.
* `JoseSmoothest.fourthOrderSmoothness_eq_multiplierNorm`: equation (3.3) of the paper.
* `JoseSmoothest.fourthOrderMultiplier_le_smoothness`: the pointwise multiplier bound.

## Proof outline

Singleton indicators give a Hilbert basis of complex counting-measure `L²`. Matching this
basis with Mathlib's Fourier basis produces an isometric equivalence to circle `L²`.
Translations become multiplication by characters, so finite convolution and every iterated
difference become multiplication by a continuous symbol. The operator norm of that
multiplication map is its uniform norm. Finally, complexification preserves the norm of
the real operator, and symmetry identifies the complex kernel symbol with its real cosine
transform.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JoseSmoothest

/-- The real Fourier transform (symbol) of a symmetric finite kernel. -/
def kernelFourierTransform (u : Kernel) (ξ : ℝ) : ℝ :=
  u.sum fun k a ↦ a * Real.cos ((k : ℝ) * ξ)

/-- The four assumptions imposed on kernels in Theorem 1.4. -/
def IsAdmissibleKernel (n : ℕ) (u : Kernel) : Prop :=
  (∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0) ∧
  (∀ k : ℤ, u (-k) = u k) ∧
  u.sum (fun _ a ↦ a) = 1 ∧
  ∀ ξ : ℝ, 0 ≤ kernelFourierTransform u ξ

namespace IsAdmissibleKernel

/-- An admissible kernel vanishes outside `[-n, n]`. -/
theorem support {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0 :=
  h.1

/-- An admissible kernel is symmetric. -/
theorem symmetric {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    ∀ k : ℤ, u (-k) = u k :=
  h.2.1

/-- The coefficients of an admissible kernel sum to one. -/
theorem sum_eq_one {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    u.sum (fun _ a ↦ a) = 1 :=
  h.2.2.1

/-- The Fourier transform of an admissible kernel is nonnegative. -/
theorem fourier_nonnegative {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    ∀ ξ : ℝ, 0 ≤ kernelFourierTransform u ξ :=
  h.2.2.2

end IsAdmissibleKernel

/-- The operator norm of the `r`-fold forward difference after convolution by `u`. -/
def differenceSmoothness (r : ℕ) (u : Kernel) : ℝ :=
  ‖differenceAfterAveraging r u‖

/-- The modulus of the `r`-fold difference multiplier at frequency `ξ`. -/
def differenceMultiplier (r : ℕ) (u : Kernel) (ξ : ℝ) : ℝ :=
  Real.sqrt (2 * (1 - Real.cos ξ)) ^ r * |kernelFourierTransform u ξ|

/-- The supremum of the `r`-fold difference multiplier over all real frequencies. -/
def differenceMultiplierNorm (r : ℕ) (u : Kernel) : ℝ :=
  sSup {a : ℝ | ∃ ξ : ℝ, a = differenceMultiplier r u ξ}

/-- The operator norm of `∇⁴` after convolution by `u`. -/
def fourthOrderSmoothness (u : Kernel) : ℝ :=
  ‖(differenceOperator ^ 4).comp (averagingOperator u)‖

/-- The modulus of the fourth-order Fourier multiplier at frequency `ξ`. -/
def fourthOrderMultiplier (u : Kernel) (ξ : ℝ) : ℝ :=
  4 * (1 - Real.cos ξ) ^ 2 * |kernelFourierTransform u ξ|

/-- The supremum of the fourth-order multiplier over all real frequencies. -/
def fourthOrderMultiplierNorm (u : Kernel) : ℝ :=
  sSup {r : ℝ | ∃ ξ : ℝ, r = fourthOrderMultiplier u ξ}

/-! ## Fourier series on counting-measure `L²` -/

private abbrev ComplexSequence := Lp ℂ 2 (Measure.count : Measure ℤ)

/-- The singleton indicator at `i`, used privately to build the Fourier basis
of counting-measure `L²`. -/
private def countDelta (i : ℤ) : ComplexSequence :=
  indicatorConstLp 2 (measurableSet_singleton i) (by simp) 1

private theorem countDelta_orthonormal : Orthonormal ℂ countDelta := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [countDelta, L2.inner_indicatorConstLp_one_indicatorConstLp_one]
  by_cases h : i = j
  · simp [h]
  · simp [h]

private theorem countDelta_span_orthogonal :
    (Submodule.span ℂ (Set.range countDelta))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  apply Lp.ext
  refine Measure.ae_count_iff.mpr ?_
  intro i
  have hi := ((Submodule.span ℂ (Set.range countDelta)).mem_orthogonal f).mp hf
    (countDelta i) (Submodule.subset_span ⟨i, rfl⟩)
  unfold countDelta at hi
  rw [L2.inner_indicatorConstLp_one] at hi
  simpa [integral_singleton] using hi

/-- A Hilbert basis of complex counting-measure `L²`, built from singleton
indicators.  This stays private because it only repairs a missing library
bridge between two representations of sequence `ℓ²`. -/
private def countHilbertBasis : HilbertBasis ℤ ℂ ComplexSequence :=
  HilbertBasis.mkOfOrthogonalEqBot countDelta_orthonormal countDelta_span_orthogonal

private local instance circlePeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

private abbrev CircleL2 :=
  Lp ℂ 2 (@AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive)

/-- The Fourier-series equivalence from complex sequences to circle `L²`. -/
private def sequenceFourierEquiv : ComplexSequence ≃ₗᵢ[ℂ] CircleL2 :=
  countHilbertBasis.repr.trans fourierBasis.repr.symm

private def circleMultiplierLp (m : C(AddCircle (2 * Real.pi), ℂ)) :
    Lp ℂ ∞ (@AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive) :=
  ContinuousMap.toLp ∞ (@AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive) ℂ m

private def circleMultiplyLinear (m : C(AddCircle (2 * Real.pi), ℂ)) :
    CircleL2 →ₗ[ℂ] CircleL2 where
  toFun f := (circleMultiplierLp m • f : CircleL2)
  map_add' f g := Lp.add_smul (r := 2) (circleMultiplierLp m) f g
  map_smul' c f := by
    change (circleMultiplierLp m • (c • f) : CircleL2) =
      c • (circleMultiplierLp m • f : CircleL2)
    exact (Lp.smul_comm (r := 2) c (circleMultiplierLp m) f).symm

private def circleMultiply (m : C(AddCircle (2 * Real.pi), ℂ)) :
    CircleL2 →L[ℂ] CircleL2 :=
  LinearMap.mkContinuous (circleMultiplyLinear m) ‖circleMultiplierLp m‖ (fun f => by
    change ‖(circleMultiplierLp m • f : CircleL2)‖ ≤ ‖circleMultiplierLp m‖ * ‖f‖
    exact Lp.norm_smul_le (r := 2) (circleMultiplierLp m) f)

private theorem circleMultiply_coeFn (m : C(AddCircle (2 * Real.pi), ℂ)) (f : CircleL2) :
    circleMultiply m f =ᵐ[@AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive]
      fun x ↦ m x * f x := by
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (circleMultiplierLp m) f,
    ContinuousMap.coeFn_toLp (p := ∞)
      (𝕜 := ℂ)
      (μ := @AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive) m] with x hx hm
  change (circleMultiplierLp m • f : CircleL2) x = m x * f x
  rw [hx]
  change circleMultiplierLp m x * f x = m x * f x
  change circleMultiplierLp m x = m x at hm
  rw [hm]

private theorem circleMultiply_norm_le (m : C(AddCircle (2 * Real.pi), ℂ)) :
    ‖circleMultiply m‖ ≤ ‖m‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg m)
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [circleMultiply_coeFn m f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (m.norm_coe_le_norm x) (norm_nonneg _)

/-
The reverse norm inequality is obtained by testing on the indicator of an open set on
which `‖m x‖` is larger than a fixed number strictly between the two candidate norms.
Every nonempty open set has positive Haar measure, so this test function is nonzero.
-/
private theorem circleMultiply_norm (m : C(AddCircle (2 * Real.pi), ℂ)) :
    ‖circleMultiply m‖ = ‖m‖ := by
  apply le_antisymm (circleMultiply_norm_le m)
  rw [ContinuousMap.norm_eq_iSup_norm]
  apply ciSup_le
  intro x
  by_contra hx
  have hlt : ‖circleMultiply m‖ < ‖m x‖ := lt_of_not_ge hx
  let c : ℝ := (‖circleMultiply m‖ + ‖m x‖) / 2
  have hMc : ‖circleMultiply m‖ < c := by
    dsimp [c]
    linarith
  have hcx : c < ‖m x‖ := by
    dsimp [c]
    linarith
  have hcpos : 0 < c := lt_of_le_of_lt (norm_nonneg _) hMc
  let U : Set (AddCircle (2 * Real.pi)) := {y | c < ‖m y‖}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const m.continuous.norm
  have hxU : x ∈ U := hcx
  have hUne : U.Nonempty := ⟨x, hxU⟩
  let μ : Measure (AddCircle (2 * Real.pi)) :=
    @AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive
  have hμU : 0 < μ U := hUopen.measure_pos μ hUne
  have hμUtop : μ U ≠ ∞ := measure_ne_top μ U
  let f : CircleL2 := indicatorConstLp 2 hUopen.measurableSet hμUtop 1
  have hfnormpos : 0 < ‖f‖ := by
    dsimp [f]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    have hreal : 0 < μ.real U :=
      ENNReal.toReal_pos (ne_of_gt hμU) hμUtop
    simp only [norm_one, one_mul]
    positivity
  have hcf : ‖(c : ℂ) • f‖ ≤ ‖circleMultiply m f‖ := by
    suffices ∀ᵐ y ∂μ, ‖((c : ℂ) • f) y‖ ≤ 1 * ‖circleMultiply m f y‖ by
      simpa only [one_mul] using
        (Lp.norm_le_mul_norm_of_ae_le_mul
          (f := (c : ℂ) • f) (g := circleMultiply m f) (c := 1) this)
    filter_upwards [Lp.coeFn_smul (c : ℂ) f,
      @indicatorConstLp_coeFn (AddCircle (2 * Real.pi)) ℂ _ 2 μ _
        U hUopen.measurableSet hμUtop 1,
      circleMultiply_coeFn m f] with y hsm hf hmul
    rw [hsm, Pi.smul_apply, hmul, hf]
    by_cases hy : y ∈ U
    · rw [Set.indicator_of_mem hy]
      simp only [smul_eq_mul, mul_one, Complex.norm_real, Real.norm_eq_abs,
        one_mul, abs_of_pos hcpos]
      exact (show c ≤ ‖m y‖ from (show c < ‖m y‖ from hy).le)
    · rw [Set.indicator_of_notMem hy]
      simp
  have hcancel : c * ‖f‖ ≤ ‖circleMultiply m‖ * ‖f‖ := by
    calc
      c * ‖f‖ = ‖(c : ℂ) • f‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
      _ ≤ ‖circleMultiply m f‖ := hcf
      _ ≤ ‖circleMultiply m‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
  have : c ≤ ‖circleMultiply m‖ := le_of_mul_le_mul_right hcancel hfnormpos
  exact (not_lt_of_ge this) hMc

private theorem circleMultiply_fourier (k i : ℤ) :
    circleMultiply (fourier k) (fourierLp 2 i) = fourierLp 2 (i + k) := by
  apply Lp.ext
  filter_upwards [circleMultiply_coeFn (fourier k) (fourierLp 2 i),
    coeFn_fourierLp 2 i, coeFn_fourierLp 2 (i + k)] with x hmul hi hik
  rw [hmul, hi, hik, add_comm, fourier_add]

private theorem circleMultiply_zero :
    circleMultiply (0 : C(AddCircle (2 * Real.pi), ℂ)) = 0 := by
  ext f
  filter_upwards [circleMultiply_coeFn (0 : C(AddCircle (2 * Real.pi), ℂ)) f,
    Lp.coeFn_zero ℂ 2
      (@AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive)] with x hzero hz
  change circleMultiply (0 : C(AddCircle (2 * Real.pi), ℂ)) f x = (0 : CircleL2) x
  rw [hzero, hz]
  simp

private theorem circleMultiply_one :
    circleMultiply (1 : C(AddCircle (2 * Real.pi), ℂ)) =
      ContinuousLinearMap.id ℂ CircleL2 := by
  ext f
  filter_upwards [circleMultiply_coeFn (1 : C(AddCircle (2 * Real.pi), ℂ)) f] with x h
  change circleMultiply (1 : C(AddCircle (2 * Real.pi), ℂ)) f x = f x
  rw [h]
  simp

private theorem circleMultiply_add (m n : C(AddCircle (2 * Real.pi), ℂ)) :
    circleMultiply (m + n) = circleMultiply m + circleMultiply n := by
  ext f
  filter_upwards [circleMultiply_coeFn (m + n) f, circleMultiply_coeFn m f,
    circleMultiply_coeFn n f, Lp.coeFn_add (circleMultiply m f) (circleMultiply n f)]
      with x hmn hm hn hadd
  change circleMultiply (m + n) f x = (circleMultiply m f + circleMultiply n f) x
  rw [hmn, hadd, Pi.add_apply, hm, hn]
  simp [add_mul]

private theorem circleMultiply_neg (m : C(AddCircle (2 * Real.pi), ℂ)) :
    circleMultiply (-m) = -circleMultiply m := by
  ext f
  filter_upwards [circleMultiply_coeFn (-m) f, circleMultiply_coeFn m f,
    Lp.coeFn_neg (circleMultiply m f)] with x hneg hm hout
  change circleMultiply (-m) f x = (-(circleMultiply m f)) x
  rw [hneg]
  rw [ContinuousMap.neg_apply, hout, Pi.neg_apply, hm]
  simp

private theorem circleMultiply_smul (c : ℂ) (m : C(AddCircle (2 * Real.pi), ℂ)) :
    circleMultiply (c • m) = c • circleMultiply m := by
  ext f
  filter_upwards [circleMultiply_coeFn (c • m) f, circleMultiply_coeFn m f,
    Lp.coeFn_smul c (circleMultiply m f)] with x hcm hm hout
  rw [hcm, ContinuousMap.smul_apply, smul_eq_mul]
  change (c * m x) * f x = (c • circleMultiply m f) x
  rw [hout, Pi.smul_apply, hm]
  simp [mul_assoc]

private theorem circleMultiply_sub (m n : C(AddCircle (2 * Real.pi), ℂ)) :
    circleMultiply (m - n) = circleMultiply m - circleMultiply n := by
  rw [sub_eq_add_neg, circleMultiply_add, circleMultiply_neg, sub_eq_add_neg]

private theorem circleMultiply_mul (m n : C(AddCircle (2 * Real.pi), ℂ)) :
    circleMultiply (m * n) = (circleMultiply m).comp (circleMultiply n) := by
  ext f
  filter_upwards [circleMultiply_coeFn (m * n) f,
    circleMultiply_coeFn m (circleMultiply n f), circleMultiply_coeFn n f]
      with x hmul hm hn
  change circleMultiply (m * n) f x = circleMultiply m (circleMultiply n f) x
  rw [hmul, hm, hn]
  simp [mul_assoc]

private theorem circleMultiply_pow (m : C(AddCircle (2 * Real.pi), ℂ)) (r : ℕ) :
    circleMultiply (m ^ r) = circleMultiply m ^ r := by
  induction r with
  | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using circleMultiply_one
  | succ r ih =>
      rw [pow_succ, circleMultiply_mul, ih, pow_succ, ContinuousLinearMap.mul_def]

private def complexTranslation (k : ℤ) : ComplexSequence →ₗᵢ[ℂ] ComplexSequence :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun j : ℤ ↦ -k + j)
    (measurePreserving_vadd (-k) (Measure.count : Measure ℤ))

private theorem complexTranslation_countDelta (k i : ℤ) :
    complexTranslation k (countDelta i) = countDelta (i + k) := by
  apply Lp.ext
  apply Measure.ae_count_iff.mpr
  intro j
  have ht := Measure.ae_count_iff.mp
    (Lp.coeFn_compMeasurePreserving (countDelta i)
      (measurePreserving_vadd (-k) (Measure.count : Measure ℤ))) j
  change ((Lp.compMeasurePreserving (fun j : ℤ => (-k) +ᵥ j)
    (measurePreserving_vadd (-k) (Measure.count : Measure ℤ))) (countDelta i)) j =
      (countDelta (i + k)) j
  rw [ht]
  change (countDelta i) ((-k) +ᵥ j) = (countDelta (i + k)) j
  have hi := Measure.ae_count_iff.mp
    (@indicatorConstLp_coeFn ℤ ℂ _ 2 (Measure.count : Measure ℤ) _
      {i} (measurableSet_singleton i) (by simp) 1) ((-k) +ᵥ j)
  have hij := Measure.ae_count_iff.mp
    (@indicatorConstLp_coeFn ℤ ℂ _ 2 (Measure.count : Measure ℤ) _
      {i + k} (measurableSet_singleton (i + k)) (by simp) 1) j
  change (countDelta i) ((-k) +ᵥ j) =
    ({i} : Set ℤ).indicator (fun _ => (1 : ℂ)) ((-k) +ᵥ j) at hi
  change (countDelta (i + k)) j =
    ({i + k} : Set ℤ).indicator (fun _ => (1 : ℂ)) j at hij
  rw [hi, hij]
  by_cases h : j = i + k
  · have h' : (-k) +ᵥ j = i := by
      change -k + j = i
      omega
    rw [Set.indicator_of_mem (by simpa using h'), Set.indicator_of_mem (by simpa using h)]
  · have h' : (-k) +ᵥ j ≠ i := by
      change -k + j ≠ i
      omega
    rw [Set.indicator_of_notMem (by simpa using h'),
      Set.indicator_of_notMem (by simpa using h)]

private theorem sequenceFourierEquiv_countDelta (i : ℤ) :
    sequenceFourierEquiv (countDelta i) = fourierLp 2 i := by
  unfold sequenceFourierEquiv
  rw [LinearIsometryEquiv.trans_apply]
  change fourierBasis.repr.symm (countHilbertBasis.repr (countDelta i)) = _
  have hcount : countHilbertBasis i = countDelta i :=
    congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
      countDelta_orthonormal countDelta_span_orthogonal) i
  rw [← hcount, countHilbertBasis.repr_self, fourierBasis.repr_symm_single]
  exact congrFun coe_fourierBasis i

private theorem sequenceFourierEquiv_complexTranslation (k : ℤ) (f : ComplexSequence) :
    sequenceFourierEquiv (complexTranslation k f) =
      circleMultiply (fourier k) (sequenceFourierEquiv f) := by
  let lhs : ComplexSequence →L[ℂ] CircleL2 :=
    sequenceFourierEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (complexTranslation k).toContinuousLinearMap
  let rhs : ComplexSequence →L[ℂ] CircleL2 :=
    (circleMultiply (fourier k)).comp
      sequenceFourierEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hdense : Dense (Submodule.span ℂ (Set.range countHilbertBasis) : Set ComplexSequence) := by
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr countHilbertBasis.dense_span
  have heq : lhs = rhs := ContinuousLinearMap.ext_on hdense (by
    rintro x ⟨i, rfl⟩
    have hcount : countHilbertBasis i = countDelta i :=
      congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
        countDelta_orthonormal countDelta_span_orthogonal) i
    change sequenceFourierEquiv (complexTranslation k (countHilbertBasis i)) =
      circleMultiply (fourier k) (sequenceFourierEquiv (countHilbertBasis i))
    rw [hcount, complexTranslation_countDelta, sequenceFourierEquiv_countDelta,
      sequenceFourierEquiv_countDelta, circleMultiply_fourier])
  exact DFunLike.congr_fun heq f

private def complexDifferenceOperator : ComplexSequence →L[ℂ] ComplexSequence :=
  (complexTranslation (-1)).toContinuousLinearMap -
    ContinuousLinearMap.id ℂ ComplexSequence

private def complexAveragingOperator (u : Kernel) : ComplexSequence →L[ℂ] ComplexSequence :=
  u.sum fun k a ↦ (a : ℂ) • (complexTranslation k).toContinuousLinearMap

private def kernelCircleSymbol (u : Kernel) : C(AddCircle (2 * Real.pi), ℂ) :=
  u.sum fun k a ↦ (a : ℂ) • fourier k

private def orderCircleSymbol (r : ℕ) (u : Kernel) : C(AddCircle (2 * Real.pi), ℂ) :=
  (fourier (-1) - 1) ^ r * kernelCircleSymbol u

private theorem sequenceFourierEquiv_complexDifference (f : ComplexSequence) :
    sequenceFourierEquiv (complexDifferenceOperator f) =
      circleMultiply (fourier (-1) - 1) (sequenceFourierEquiv f) := by
  change sequenceFourierEquiv (complexTranslation (-1) f - f) = _
  rw [map_sub, sequenceFourierEquiv_complexTranslation, circleMultiply_sub,
    circleMultiply_one]
  rfl

private theorem sequenceFourierEquiv_complexAveraging (u : Kernel) (f : ComplexSequence) :
    sequenceFourierEquiv (complexAveragingOperator u f) =
      circleMultiply (kernelCircleSymbol u) (sequenceFourierEquiv f) := by
  classical
  induction u using Finsupp.induction with
  | zero => simp [complexAveragingOperator, kernelCircleSymbol, circleMultiply_zero]
  | single_add k a u hk ha ih =>
      have havg : complexAveragingOperator (Finsupp.single k a + u) =
          (a : ℂ) • (complexTranslation k).toContinuousLinearMap +
            complexAveragingOperator u := by
        unfold complexAveragingOperator
        rw [Finsupp.sum_add_index' (by simp) (by simp [add_smul]),
          Finsupp.sum_single_index (by simp)]
      have hsymbol : kernelCircleSymbol (Finsupp.single k a + u) =
          (a : ℂ) • fourier k + kernelCircleSymbol u := by
        unfold kernelCircleSymbol
        rw [Finsupp.sum_add_index' (by simp) (by simp [add_smul]),
          Finsupp.sum_single_index (by simp)]
      rw [havg, hsymbol]
      change sequenceFourierEquiv ((a : ℂ) • complexTranslation k f +
          complexAveragingOperator u f) =
        circleMultiply ((a : ℂ) • fourier k + kernelCircleSymbol u)
          (sequenceFourierEquiv f)
      rw [map_add, map_smul, sequenceFourierEquiv_complexTranslation, ih,
        circleMultiply_add, circleMultiply_smul]
      rfl

private theorem sequenceFourierEquiv_complexDifference_pow (r : ℕ) (f : ComplexSequence) :
    sequenceFourierEquiv ((complexDifferenceOperator ^ r) f) =
      circleMultiply ((fourier (-1) - 1) ^ r) (sequenceFourierEquiv f) := by
  induction r generalizing f with
  | zero =>
      rw [pow_zero, one_apply_eq_self, pow_zero, circleMultiply_one]
      rfl
  | succ r ih =>
      rw [pow_succ, mul_apply_eq_comp, ih, sequenceFourierEquiv_complexDifference]
      change ((circleMultiply ((fourier (-1) - 1) ^ r)).comp
          (circleMultiply (fourier (-1) - 1))) (sequenceFourierEquiv f) = _
      rw [← circleMultiply_mul, ← pow_succ]

private def complexOrderOperator (r : ℕ) (u : Kernel) :
    ComplexSequence →L[ℂ] ComplexSequence :=
  (complexDifferenceOperator ^ r).comp (complexAveragingOperator u)

private theorem sequenceFourierEquiv_complexOrder
    (r : ℕ) (u : Kernel) (f : ComplexSequence) :
    sequenceFourierEquiv (complexOrderOperator r u f) =
      circleMultiply (orderCircleSymbol r u) (sequenceFourierEquiv f) := by
  unfold complexOrderOperator
  rw [ContinuousLinearMap.comp_apply]
  rw [sequenceFourierEquiv_complexDifference_pow,
    sequenceFourierEquiv_complexAveraging]
  change ((circleMultiply ((fourier (-1) - 1) ^ r)).comp
      (circleMultiply (kernelCircleSymbol u))) (sequenceFourierEquiv f) = _
  rw [← circleMultiply_mul]
  rfl

private theorem complexOrderOperator_norm (r : ℕ) (u : Kernel) :
    ‖complexOrderOperator r u‖ = ‖orderCircleSymbol r u‖ := by
  have hforward :
      ‖complexOrderOperator r u‖ ≤ ‖circleMultiply (orderCircleSymbol r u)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    calc
      ‖complexOrderOperator r u f‖ =
          ‖sequenceFourierEquiv (complexOrderOperator r u f)‖ :=
        (sequenceFourierEquiv.norm_map _).symm
      _ = ‖circleMultiply (orderCircleSymbol r u) (sequenceFourierEquiv f)‖ := by
        rw [sequenceFourierEquiv_complexOrder]
      _ ≤ ‖circleMultiply (orderCircleSymbol r u)‖ * ‖sequenceFourierEquiv f‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖circleMultiply (orderCircleSymbol r u)‖ * ‖f‖ := by
        rw [sequenceFourierEquiv.norm_map]
  have hbackward : ‖circleMultiply (orderCircleSymbol r u)‖ ≤
      ‖complexOrderOperator r u‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro g
    let f : ComplexSequence := sequenceFourierEquiv.symm g
    have hFg : sequenceFourierEquiv f = g := sequenceFourierEquiv.apply_symm_apply g
    calc
      ‖circleMultiply (orderCircleSymbol r u) g‖ =
          ‖circleMultiply (orderCircleSymbol r u) (sequenceFourierEquiv f)‖ := by rw [hFg]
      _ = ‖sequenceFourierEquiv (complexOrderOperator r u f)‖ := by
        rw [sequenceFourierEquiv_complexOrder]
      _ = ‖complexOrderOperator r u f‖ := sequenceFourierEquiv.norm_map _
      _ ≤ ‖complexOrderOperator r u‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖complexOrderOperator r u‖ * ‖g‖ := by
        rw [show ‖f‖ = ‖g‖ from sequenceFourierEquiv.symm.norm_map g]
  rw [← circleMultiply_norm (orderCircleSymbol r u)]
  exact le_antisymm hforward hbackward

/-! ## Comparison with real `L²`

The following maps compare real and complex `L²`. They are kept private:
the public API only needs the resulting equality of operator norms. -/

private def complexOfReal : Sequence →L[ℝ] ComplexSequence :=
  Complex.ofRealCLM.compLpL 2 (Measure.count : Measure ℤ)

private def complexRe : ComplexSequence →L[ℝ] Sequence :=
  Complex.reCLM.compLpL 2 (Measure.count : Measure ℤ)

private def complexIm : ComplexSequence →L[ℝ] Sequence :=
  Complex.imCLM.compLpL 2 (Measure.count : Measure ℤ)

private theorem complexOfReal_coeFn (f : Sequence) :
    complexOfReal f =ᵐ[Measure.count] fun i ↦ (f i : ℂ) :=
  ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM f

private theorem complexRe_coeFn (f : ComplexSequence) :
    complexRe f =ᵐ[Measure.count] fun i ↦ (f i).re :=
  ContinuousLinearMap.coeFn_compLpL Complex.reCLM f

private theorem complexIm_coeFn (f : ComplexSequence) :
    complexIm f =ᵐ[Measure.count] fun i ↦ (f i).im :=
  ContinuousLinearMap.coeFn_compLpL Complex.imCLM f

private theorem complexOfReal_norm (f : Sequence) : ‖complexOfReal f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [complexOfReal_coeFn f] with x hx
  rw [hx, Complex.norm_real]

private theorem complex_norm_sq_eq_re_add_im (f : ComplexSequence) :
    ‖f‖ ^ 2 = ‖complexRe f‖ ^ 2 + ‖complexIm f‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℝ),
    norm_sq_eq_re_inner (𝕜 := ℝ), L2.inner_def, L2.inner_def, L2.inner_def]
  rw [← integral_re (L2.integrable_inner f f)]
  simp only [RCLike.re_to_real]
  rw [← integral_add (L2.integrable_inner (complexRe f) (complexRe f))
    (L2.integrable_inner (complexIm f) (complexIm f))]
  apply integral_congr_ae
  filter_upwards [complexRe_coeFn f, complexIm_coeFn f] with x hre him
  rw [hre, him]
  simp only [inner_self_eq_norm_sq_to_K]
  norm_cast
  simpa [Real.norm_eq_abs, sq_abs, pow_two] using
    (RCLike.norm_sq_eq_def (z := f x))

private theorem complexTranslation_ofReal (k : ℤ) (f : Sequence) :
    complexTranslation k (complexOfReal f) = complexOfReal (translation k f) := by
  apply Lp.ext
  apply Measure.ae_count_iff.mpr
  intro i
  have hct := Measure.ae_count_iff.mp
    (Lp.coeFn_compMeasurePreserving (complexOfReal f)
      (measurePreserving_vadd (-k) (Measure.count : Measure ℤ))) i
  have hrt := Measure.ae_count_iff.mp
    (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_vadd (-k) (Measure.count : Measure ℤ))) i
  have he := Measure.ae_count_iff.mp (complexOfReal_coeFn f) ((-k) +ᵥ i)
  have het := Measure.ae_count_iff.mp (complexOfReal_coeFn (translation k f)) i
  change ((Lp.compMeasurePreserving (fun j : ℤ => (-k) +ᵥ j)
      (measurePreserving_vadd (-k) (Measure.count : Measure ℤ))) (complexOfReal f)) i =
    complexOfReal (translation k f) i
  rw [hct, Function.comp_apply, het]
  change complexOfReal f ((-k) +ᵥ i) =
    (((Lp.compMeasurePreserving (fun j : ℤ => (-k) +ᵥ j)
      (measurePreserving_vadd (-k) (Measure.count : Measure ℤ))) f) i : ℂ)
  rw [he, hrt, Function.comp_apply]

private theorem complexDifference_ofReal (f : Sequence) :
    complexDifferenceOperator (complexOfReal f) =
      complexOfReal (differenceOperator f) := by
  change complexTranslation (-1) (complexOfReal f) - complexOfReal f =
    complexOfReal (translation (-1) f - f)
  rw [complexTranslation_ofReal, map_sub]

private theorem complexAveraging_ofReal (u : Kernel) (f : Sequence) :
    complexAveragingOperator u (complexOfReal f) =
      complexOfReal (averagingOperator u f) := by
  classical
  induction u using Finsupp.induction with
  | zero => simp [complexAveragingOperator, averagingOperator]
  | single_add k a u hk ha ih =>
      have hcavg : complexAveragingOperator (Finsupp.single k a + u) =
          (a : ℂ) • (complexTranslation k).toContinuousLinearMap +
            complexAveragingOperator u := by
        unfold complexAveragingOperator
        rw [Finsupp.sum_add_index' (by simp) (by simp [add_smul]),
          Finsupp.sum_single_index (by simp)]
      have hravg : averagingOperator (Finsupp.single k a + u) =
          a • (translation k).toContinuousLinearMap + averagingOperator u := by
        unfold averagingOperator
        rw [Finsupp.sum_add_index' (by simp) (by simp [add_smul]),
          Finsupp.sum_single_index (by simp)]
      rw [hcavg, hravg]
      change (a : ℂ) • complexTranslation k (complexOfReal f) +
          complexAveragingOperator u (complexOfReal f) =
        complexOfReal (a • translation k f + averagingOperator u f)
      rw [complexTranslation_ofReal, ih, map_add, map_smul]
      exact congrArg (fun g : ComplexSequence ↦ g + complexOfReal (averagingOperator u f))
        (RCLike.real_smul_eq_coe_smul a (complexOfReal (translation k f))).symm

private theorem complexDifference_pow_ofReal (r : ℕ) (f : Sequence) :
    (complexDifferenceOperator ^ r) (complexOfReal f) =
      complexOfReal ((differenceOperator ^ r) f) := by
  induction r generalizing f with
  | zero => simp
  | succ r ih =>
      rw [pow_succ, mul_apply_eq_comp, complexDifference_ofReal, ih,
        pow_succ, mul_apply_eq_comp]

private theorem complexOrder_ofReal (r : ℕ) (u : Kernel) (f : Sequence) :
    complexOrderOperator r u (complexOfReal f) =
      complexOfReal (differenceAfterAveraging r u f) := by
  rw [complexOrderOperator, differenceAfterAveraging, ContinuousLinearMap.comp_apply,
    complexAveraging_ofReal, complexDifference_pow_ofReal,
    ContinuousLinearMap.comp_apply]

private theorem complexRe_ofReal (f : Sequence) :
    complexRe (complexOfReal f) = f := by
  apply Lp.ext
  filter_upwards [complexRe_coeFn (complexOfReal f), complexOfReal_coeFn f]
    with x hre he
  rw [hre, he]
  simp

private theorem complexIm_ofReal (f : Sequence) :
    complexIm (complexOfReal f) = 0 := by
  apply Lp.ext
  filter_upwards [complexIm_coeFn (complexOfReal f), complexOfReal_coeFn f,
    Lp.coeFn_zero ℝ 2 (Measure.count : Measure ℤ)] with x him he hz
  rw [him, he, hz]
  simp

private theorem complexRe_I_smul_ofReal (f : Sequence) :
    complexRe (Complex.I • complexOfReal f) = 0 := by
  apply Lp.ext
  filter_upwards [complexRe_coeFn (Complex.I • complexOfReal f),
    Lp.coeFn_smul Complex.I (complexOfReal f), complexOfReal_coeFn f,
    Lp.coeFn_zero ℝ 2 (Measure.count : Measure ℤ)] with x hre hI he hz
  rw [hre, hI, Pi.smul_apply, he, hz]
  simp [smul_eq_mul]

private theorem complexIm_I_smul_ofReal (f : Sequence) :
    complexIm (Complex.I • complexOfReal f) = f := by
  apply Lp.ext
  filter_upwards [complexIm_coeFn (Complex.I • complexOfReal f),
    Lp.coeFn_smul Complex.I (complexOfReal f), complexOfReal_coeFn f]
      with x him hI he
  rw [him, hI, Pi.smul_apply, he]
  simp [smul_eq_mul]

private theorem complex_reconstruction (f : ComplexSequence) :
    f = complexOfReal (complexRe f) + Complex.I • complexOfReal (complexIm f) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (complexOfReal (complexRe f))
      (Complex.I • complexOfReal (complexIm f)),
    complexOfReal_coeFn (complexRe f), complexRe_coeFn f,
    Lp.coeFn_smul Complex.I (complexOfReal (complexIm f)),
    complexOfReal_coeFn (complexIm f), complexIm_coeFn f] with x hadd hre hfre hI him hfim
  rw [hadd, Pi.add_apply, hre, hfre, hI, Pi.smul_apply, him, hfim]
  change f x = (f x).re + Complex.I * (f x).im
  rw [mul_comm]
  exact (Complex.re_add_im (f x)).symm

/-
For one inequality, embed real sequences isometrically into complex sequences. For the
other, decompose a complex sequence into real and imaginary parts. The Pythagorean norm
identity then bounds both components by the norm of the real operator.
-/
private theorem order_real_complex_norm (r : ℕ) (u : Kernel) :
    ‖differenceAfterAveraging r u‖ = ‖complexOrderOperator r u‖ := by
  let R : Sequence →L[ℝ] Sequence :=
    differenceAfterAveraging r u
  let C : ComplexSequence →L[ℂ] ComplexSequence := complexOrderOperator r u
  have hreal_le : ‖R‖ ≤ ‖C‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    calc
      ‖R f‖ = ‖complexOfReal (R f)‖ := (complexOfReal_norm (R f)).symm
      _ = ‖C (complexOfReal f)‖ := by
        rw [show C (complexOfReal f) = complexOfReal (R f) by
          simpa [C, R] using complexOrder_ofReal r u f]
      _ ≤ ‖C‖ * ‖complexOfReal f‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖C‖ * ‖f‖ := by rw [complexOfReal_norm]
  have hcomplex_le : ‖C‖ ≤ ‖R‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    let a : Sequence := R (complexRe f)
    let b : Sequence := R (complexIm f)
    have hout : C f = complexOfReal a + Complex.I • complexOfReal b := by
      rw [complex_reconstruction f, map_add, map_smul]
      change complexOrderOperator r u (complexOfReal (complexRe f)) +
          Complex.I • complexOrderOperator r u (complexOfReal (complexIm f)) = _
      rw [complexOrder_ofReal, complexOrder_ofReal]
    have hout_re : complexRe (C f) = a := by
      rw [hout, map_add, complexRe_ofReal, complexRe_I_smul_ofReal, add_zero]
    have hout_im : complexIm (C f) = b := by
      rw [hout, map_add, complexIm_ofReal, complexIm_I_smul_ofReal, zero_add]
    have hinput : ‖f‖ ^ 2 = ‖complexRe f‖ ^ 2 + ‖complexIm f‖ ^ 2 :=
      complex_norm_sq_eq_re_add_im f
    have houtput : ‖C f‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
      rw [complex_norm_sq_eq_re_add_im, hout_re, hout_im]
    have ha : ‖a‖ ≤ ‖R‖ * ‖complexRe f‖ := ContinuousLinearMap.le_opNorm _ _
    have hb : ‖b‖ ≤ ‖R‖ * ‖complexIm f‖ := ContinuousLinearMap.le_opNorm _ _
    have ha2 : ‖a‖ ^ 2 ≤ (‖R‖ * ‖complexRe f‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 ha
    have hb2 : ‖b‖ ^ 2 ≤ (‖R‖ * ‖complexIm f‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hb
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1
    calc
      ‖C f‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := houtput
      _ ≤ (‖R‖ * ‖complexRe f‖) ^ 2 + (‖R‖ * ‖complexIm f‖) ^ 2 :=
        add_le_add ha2 hb2
      _ = ‖R‖ ^ 2 * (‖complexRe f‖ ^ 2 + ‖complexIm f‖ ^ 2) := by ring
      _ = ‖R‖ ^ 2 * ‖f‖ ^ 2 := by rw [← hinput]
      _ = (‖R‖ * ‖f‖) ^ 2 := by ring
  change ‖R‖ = ‖C‖
  exact le_antisymm hreal_le hcomplex_le

/-! ## Evaluation of the circle symbol -/

private theorem fourier_coe_two_pi (k : ℤ) (ξ : ℝ) :
    fourier k (ξ : AddCircle (2 * Real.pi)) =
      Complex.exp (Complex.I * (k : ℝ) * ξ) := by
  rw [fourier_coe_apply]
  congr 1
  field_simp [Real.pi_ne_zero]
  push_cast
  ring

private theorem fourier_coe_two_pi_re (k : ℤ) (ξ : ℝ) :
    (fourier k (ξ : AddCircle (2 * Real.pi))).re =
      Real.cos ((k : ℝ) * ξ) := by
  rw [fourier_coe_two_pi, Complex.exp_re]
  simp

private theorem kernelCircleSymbol_apply (u : Kernel) (x : AddCircle (2 * Real.pi)) :
    kernelCircleSymbol u x = u.sum (fun k a ↦ (a : ℂ) * fourier k x) := by
  classical
  simp [kernelCircleSymbol, Finsupp.sum]

private theorem kernelCircleSymbol_re (u : Kernel) (ξ : ℝ) :
    (kernelCircleSymbol u (ξ : AddCircle (2 * Real.pi))).re =
      kernelFourierTransform u ξ := by
  classical
  induction u using Finsupp.induction with
  | zero => simp [kernelCircleSymbol, kernelFourierTransform]
  | single_add k a u hk ha ih =>
      unfold kernelCircleSymbol kernelFourierTransform at ih ⊢
      rw [Finsupp.sum_add_index'
          (by intro j; simp only [Complex.ofReal_zero, zero_smul])
          (by intro j b c; rw [Complex.ofReal_add, add_smul]),
        Finsupp.sum_single_index (by simp only [Complex.ofReal_zero, zero_smul]),
        Finsupp.sum_add_index'
          (by intro j; exact zero_mul _)
          (by intro j b c; exact add_mul b c _),
        Finsupp.sum_single_index (by exact zero_mul _)]
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
        Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [fourier_coe_two_pi_re, ih]

private theorem kernelCircleSymbol_sum_neg
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (x : AddCircle (2 * Real.pi)) :
    u.sum (fun k a ↦ (a : ℂ) * fourier (-k) x) =
      u.sum (fun k a ↦ (a : ℂ) * fourier k x) := by
  classical
  change (∑ k ∈ u.support, (u k : ℂ) * fourier (-k) x) =
    ∑ k ∈ u.support, (u k : ℂ) * fourier k x
  refine Finset.sum_bij (fun k _ ↦ -k) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro hzero
    apply hk
    rw [← symmetric k]
    exact hzero
  · intro a ha b hb hab
    omega
  · intro b hb
    refine ⟨-b, ?_, by omega⟩
    rw [Finsupp.mem_support_iff] at hb ⊢
    rwa [symmetric b]
  · intro k hk
    rw [symmetric k]

private theorem kernelCircleSymbol_conj
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (x : AddCircle (2 * Real.pi)) :
    starRingEnd ℂ (kernelCircleSymbol u x) = kernelCircleSymbol u x := by
  classical
  have hc : starRingEnd ℂ (kernelCircleSymbol u x) =
      u.sum (fun k a ↦ (a : ℂ) * fourier (-k) x) := by
    rw [kernelCircleSymbol_apply]
    change starRingEnd ℂ (∑ k ∈ u.support, (u k : ℂ) * fourier k x) =
      ∑ k ∈ u.support, (u k : ℂ) * fourier (-k) x
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_mul, Complex.conj_ofReal, fourier_neg]
  rw [hc, kernelCircleSymbol_sum_neg u symmetric, ← kernelCircleSymbol_apply]

private theorem kernelCircleSymbol_eq_real
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (ξ : ℝ) :
    kernelCircleSymbol u (ξ : AddCircle (2 * Real.pi)) =
      (kernelFourierTransform u ξ : ℂ) := by
  calc
    kernelCircleSymbol u (ξ : AddCircle (2 * Real.pi)) =
        ((kernelCircleSymbol u (ξ : AddCircle (2 * Real.pi))).re : ℂ) :=
      (Complex.conj_eq_iff_re.mp
        (kernelCircleSymbol_conj u symmetric (ξ : AddCircle (2 * Real.pi)))).symm
    _ = (kernelFourierTransform u ξ : ℂ) := by rw [kernelCircleSymbol_re]

private theorem fourier_sub_one_norm_sq (ξ : ℝ) :
    ‖fourier (-1) (ξ : AddCircle (2 * Real.pi)) - 1‖ ^ 2 =
      2 * (1 - Real.cos ξ) := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  simp only [RCLike.inner_apply', mul_one]
  change ‖fourier (-1) (ξ : AddCircle (2 * Real.pi))‖ ^ 2 -
      2 * (fourier (-1) (ξ : AddCircle (2 * Real.pi))).re + ‖(1 : ℂ)‖ ^ 2 =
        2 * (1 - Real.cos ξ)
  rw [fourier_coe_two_pi_re]
  rw [show ‖fourier (-1) (ξ : AddCircle (2 * Real.pi))‖ = 1 from Circle.norm_coe _]
  simp [Real.cos_neg]
  ring

private theorem fourier_sub_one_norm (ξ : ℝ) :
    ‖fourier (-1) (ξ : AddCircle (2 * Real.pi)) - 1‖ =
      Real.sqrt (2 * (1 - Real.cos ξ)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), fourier_sub_one_norm_sq]

/-- The generic smoothness at order four is the original fourth-order quantity. -/
@[simp]
theorem differenceSmoothness_four (u : Kernel) :
    differenceSmoothness 4 u = fourthOrderSmoothness u :=
  rfl

/-- At even order `2 * m`, the difference weight is a polynomial in `cos ξ`. -/
theorem differenceMultiplier_two_mul (m : ℕ) (u : Kernel) (ξ : ℝ) :
    differenceMultiplier (2 * m) u ξ =
      (2 * (1 - Real.cos ξ)) ^ m * |kernelFourierTransform u ξ| := by
  have hnonneg : 0 ≤ 2 * (1 - Real.cos ξ) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.cos_le_one ξ))
  unfold differenceMultiplier
  rw [pow_mul, Real.sq_sqrt hnonneg]

/-- The generic multiplier at order four is the original fourth-order multiplier. -/
@[simp]
theorem differenceMultiplier_four (u : Kernel) (ξ : ℝ) :
    differenceMultiplier 4 u ξ = fourthOrderMultiplier u ξ := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, differenceMultiplier_two_mul]
  unfold fourthOrderMultiplier
  ring

/-- At order six, the difference weight is `8 * (1 - cos ξ) ^ 3`. -/
@[simp]
theorem differenceMultiplier_six (u : Kernel) (ξ : ℝ) :
    differenceMultiplier 6 u ξ =
      8 * (1 - Real.cos ξ) ^ 3 * |kernelFourierTransform u ξ| := by
  calc
    differenceMultiplier 6 u ξ =
        (2 * (1 - Real.cos ξ)) ^ 3 * |kernelFourierTransform u ξ| := by
      simpa using differenceMultiplier_two_mul 3 u ξ
    _ = 8 * (1 - Real.cos ξ) ^ 3 * |kernelFourierTransform u ξ| := by ring

/-- The generic multiplier supremum at order four is the original one. -/
@[simp]
theorem differenceMultiplierNorm_four (u : Kernel) :
    differenceMultiplierNorm 4 u = fourthOrderMultiplierNorm u := by
  unfold differenceMultiplierNorm fourthOrderMultiplierNorm
  simp only [differenceMultiplier_four]

private theorem orderCircleSymbol_norm_coe
    (r : ℕ)
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (ξ : ℝ) :
    ‖orderCircleSymbol r u (ξ : AddCircle (2 * Real.pi))‖ =
      differenceMultiplier r u ξ := by
  unfold orderCircleSymbol differenceMultiplier
  simp only [ContinuousMap.mul_apply, ContinuousMap.pow_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, norm_mul, norm_pow]
  rw [fourier_sub_one_norm, kernelCircleSymbol_eq_real u symmetric,
    Complex.norm_real, Real.norm_eq_abs]

private theorem orderCircleSymbol_norm_eq_multiplierNorm
    (r : ℕ)
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    ‖orderCircleSymbol r u‖ = differenceMultiplierNorm r u := by
  unfold differenceMultiplierNorm
  let S : Set ℝ := {a : ℝ | ∃ ξ : ℝ, a = differenceMultiplier r u ξ}
  have hS_nonempty : S.Nonempty := ⟨differenceMultiplier r u 0, 0, rfl⟩
  have hS_bdd : BddAbove S := by
    refine ⟨‖orderCircleSymbol r u‖, ?_⟩
    rintro a ⟨ξ, rfl⟩
    rw [← orderCircleSymbol_norm_coe r u symmetric ξ]
    exact (orderCircleSymbol r u).norm_coe_le_norm (ξ : AddCircle (2 * Real.pi))
  change ‖orderCircleSymbol r u‖ = sSup S
  apply le_antisymm
  · rw [ContinuousMap.norm_eq_iSup_norm]
    apply ciSup_le
    intro x
    refine QuotientAddGroup.induction_on x ?_
    intro ξ
    rw [orderCircleSymbol_norm_coe r u symmetric ξ]
    exact le_csSup hS_bdd ⟨ξ, rfl⟩
  · apply csSup_le hS_nonempty
    rintro a ⟨ξ, rfl⟩
    rw [← orderCircleSymbol_norm_coe r u symmetric ξ]
    exact (orderCircleSymbol r u).norm_coe_le_norm (ξ : AddCircle (2 * Real.pi))

/-! ## Operator norm identities -/

/-- The norm of the `r`-fold difference after averaging equals its multiplier supremum. -/
theorem differenceSmoothness_eq_multiplierNorm
    (r : ℕ)
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    differenceSmoothness r u = differenceMultiplierNorm r u := by
  unfold differenceSmoothness
  rw [order_real_complex_norm, complexOrderOperator_norm,
    orderCircleSymbol_norm_eq_multiplierNorm r u symmetric]

/-- Every frequency supplies a lower bound for the iterated-difference operator norm. -/
theorem differenceMultiplier_le_smoothness
    (r : ℕ)
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (ξ : ℝ) :
    differenceMultiplier r u ξ ≤ differenceSmoothness r u := by
  rw [← orderCircleSymbol_norm_coe r u symmetric ξ]
  unfold differenceSmoothness
  rw [order_real_complex_norm, complexOrderOperator_norm]
  exact (orderCircleSymbol r u).norm_coe_le_norm (ξ : AddCircle (2 * Real.pi))

/-- Equation (3.3): the operator norm equals the multiplier supremum. -/
theorem fourthOrderSmoothness_eq_multiplierNorm
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    fourthOrderSmoothness u = fourthOrderMultiplierNorm u := by
  rw [← differenceSmoothness_four, ← differenceMultiplierNorm_four]
  exact differenceSmoothness_eq_multiplierNorm 4 u symmetric

/-- Every frequency supplies a lower bound for the operator norm. -/
theorem fourthOrderMultiplier_le_smoothness
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (ξ : ℝ) :
    fourthOrderMultiplier u ξ ≤ fourthOrderSmoothness u := by
  rw [← differenceMultiplier_four, ← differenceSmoothness_four]
  exact differenceMultiplier_le_smoothness 4 u symmetric ξ

end JoseSmoothest
