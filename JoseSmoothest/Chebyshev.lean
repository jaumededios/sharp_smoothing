import JoseSmoothest.Fourier
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# The Chebyshev-polynomial model of an admissible kernel

This file passes from a symmetric kernel supported on `[-n,n]` to its
polynomial symbol on `[-1,1]`.  It also records the weighted norm and the
Chebyshev coefficient normalization used in the extremal problem.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial
open MeasureTheory Module

/-- The Chebyshev polynomial `T_m`, evaluated at `x`. -/
def chebyshevT (m : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ m).eval x

/-- The Chebyshev polynomial associated to a kernel supported in `[-n,n]`. -/
def kernelPolynomial (n : ℕ) (u : Kernel) : ℝ[X] :=
  C (u 0) +
    ∑ k ∈ Finset.Icc 1 n,
      C (2 * u (k : ℤ)) * Polynomial.Chebyshev.T ℝ k

/-- The polynomial associated to a kernel supported in `[-n, n]` has degree at most `n`. -/
theorem kernelPolynomial_natDegree_le (n : ℕ) (u : Kernel) :
    (kernelPolynomial n u).natDegree ≤ n := by
  unfold kernelPolynomial
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · apply natDegree_sum_le_of_forall_le
    intro k hk
    apply (natDegree_mul_le).trans
    rw [natDegree_C, Polynomial.Chebyshev.natDegree_T]
    simpa using (Finset.mem_Icc.mp hk).2

private theorem sum_Icc_one_eq_sum_range (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 n, f k = ∑ j ∈ Finset.range n, f (j + 1) := by
  symm
  refine Finset.sum_bij (fun j _ ↦ j + 1) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    omega
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    refine ⟨b - 1, ?_, by omega⟩
    simp only [Finset.mem_range]
    omega
  · intro j hj
    rfl

/-- Evaluating the kernel polynomial at `cos ξ` gives the Fourier transform of the kernel. -/
theorem kernelPolynomial_eval_cos
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (ξ : ℝ) :
    (kernelPolynomial n u).eval (Real.cos ξ) = kernelFourierTransform u ξ := by
  classical
  -- Pair the terms at opposite indices using symmetry of the kernel and cosine.
  let f : ℤ → ℝ := fun k ↦ u k * Real.cos ((k : ℝ) * ξ)
  have hf_even : Function.Even f := by
    intro k
    simp only [f]
    rw [symmetric k]
    simp
  have hsupp : u.support ⊆ Finset.Icc (-(n : ℤ)) n := by
    intro k hk
    by_contra hki
    exact (Finsupp.mem_support_iff.mp hk) (support k hki)
  have hfourier : kernelFourierTransform u ξ =
      ∑ k ∈ Finset.Icc (-(n : ℤ)) n, f k := by
    unfold kernelFourierTransform
    rw [Finsupp.sum_of_support_subset u hsupp]
    simp
  rw [hfourier]
  unfold kernelPolynomial
  simp only [eval_add, eval_C, eval_finsetSum, eval_mul,
    Polynomial.Chebyshev.T_real_cos, f, Int.cast_natCast]
  rw [sum_Icc_one_eq_sum_range, Finset.sum_Icc_of_even_eq_range hf_even n,
    Finset.sum_range_succ']
  simp [f, add_mul]
  simp [add_comm, mul_comm]
  ring_nf
  rw [Finset.sum_mul]

/-- A normalized kernel gives a kernel polynomial whose value at `1` is `1`. -/
theorem kernelPolynomial_eval_one
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (normalized : u.sum (fun _ a ↦ a) = 1) :
    (kernelPolynomial n u).eval 1 = 1 := by
  have hcos := kernelPolynomial_eval_cos n u support symmetric 0
  rw [Real.cos_zero] at hcos
  rw [hcos]
  unfold kernelFourierTransform
  simpa using normalized

/-- A kernel with nonnegative Fourier transform gives a polynomial nonnegative on `[-1, 1]`. -/
theorem kernelPolynomial_nonnegative_on_Icc
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (fourier_nonnegative : ∀ ξ : ℝ, 0 ≤ kernelFourierTransform u ξ) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ (kernelPolynomial n u).eval x := by
  intro x hx
  rw [← Real.cos_arccos hx.1 hx.2]
  rw [kernelPolynomial_eval_cos n u support symmetric]
  exact fourier_nonnegative _

/-- The weighted norm appearing in Proposition 1.6. -/
def weightedPolynomialNorm (p : ℝ[X]) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    r = |(1 - x) ^ 2 * p.eval x|}

private theorem weightedPolynomialRange_nonempty (p : ℝ[X]) :
    {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      r = |(1 - x) ^ 2 * p.eval x|}.Nonempty := by
  refine ⟨|(1 - 0) ^ 2 * p.eval 0|, 0, ?_, rfl⟩
  constructor <;> norm_num

private theorem weightedPolynomialRange_bddAbove (p : ℝ[X]) :
    BddAbove {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      r = |(1 - x) ^ 2 * p.eval x|} := by
  let g : ℝ → ℝ := fun x ↦ |(1 - x) ^ 2 * p.eval x|
  have hg : Continuous g := by
    unfold g
    fun_prop
  have hset : {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      r = |(1 - x) ^ 2 * p.eval x|} = g '' Set.Icc (-1 : ℝ) 1 := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hset]
  exact (isCompact_Icc.image hg).bddAbove

/-- Equation (3.3) after the substitution `x=cos ξ`. -/
theorem fourthOrderMultiplierNorm_eq_four_mul_weightedPolynomialNorm
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    fourthOrderMultiplierNorm u =
      4 * weightedPolynomialNorm (kernelPolynomial n u) := by
  let p := kernelPolynomial n u
  let A : Set ℝ := {r : ℝ | ∃ ξ : ℝ, r = fourthOrderMultiplier u ξ}
  let B : Set ℝ := {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    r = |(1 - x) ^ 2 * p.eval x|}
  -- First express every multiplier value through the polynomial symbol.
  have hvalue (ξ : ℝ) : fourthOrderMultiplier u ξ =
      4 * |(1 - Real.cos ξ) ^ 2 * p.eval (Real.cos ξ)| := by
    unfold fourthOrderMultiplier p
    rw [kernelPolynomial_eval_cos n u support symmetric]
    have hs : 0 ≤ (1 - Real.cos ξ) ^ 2 := sq_nonneg _
    simp only [abs_mul, abs_of_nonneg hs]
    ring
  have hB_nonempty : B.Nonempty := by
    simpa [B, p] using weightedPolynomialRange_nonempty (kernelPolynomial n u)
  have hB_bdd : BddAbove B := by
    simpa [B, p] using weightedPolynomialRange_bddAbove (kernelPolynomial n u)
  have hA_nonempty : A.Nonempty :=
    ⟨fourthOrderMultiplier u 0, 0, rfl⟩
  -- The pointwise identity transfers boundedness from the polynomial range.
  have hA_bdd : BddAbove A := by
    obtain ⟨M, hM⟩ := hB_bdd
    refine ⟨4 * M, ?_⟩
    rintro r ⟨ξ, rfl⟩
    rw [hvalue]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply hM
    exact ⟨Real.cos ξ, ⟨Real.neg_one_le_cos ξ, Real.cos_le_one ξ⟩, rfl⟩
  -- Compare the two suprema in each direction, using `arccos` for the reverse inequality.
  change sSup A = 4 * sSup B
  apply le_antisymm
  · apply csSup_le hA_nonempty
    rintro r ⟨ξ, rfl⟩
    rw [hvalue]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply le_csSup hB_bdd
    exact ⟨Real.cos ξ, ⟨Real.neg_one_le_cos ξ, Real.cos_le_one ξ⟩, rfl⟩
  · have hsup : sSup B ≤ sSup A / 4 := by
      apply csSup_le hB_nonempty
      rintro r ⟨x, hx, rfl⟩
      have hle := le_csSup hA_bdd
        (⟨Real.arccos x, rfl⟩ : fourthOrderMultiplier u (Real.arccos x) ∈ A)
      rw [hvalue, Real.cos_arccos hx.1 hx.2] at hle
      linarith
    linarith

/-- The `m`-th Chebyshev coefficient in the normalization of (1.6). -/
def chebyshevCoefficient (p : ℝ[X]) (m : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in (-1 : ℝ)..1,
      p.eval x * chebyshevT m x / Real.sqrt (1 - x ^ 2)

private def chebyshevBasis : Basis ℕ ℝ ℝ[X] :=
  (Polynomial.Chebyshev.chebyshevTsequence ℝ).basis (by simp)

private theorem chebyshevBasis_apply (i : ℕ) :
    chebyshevBasis i = Polynomial.Chebyshev.T ℝ i := by
  simp [chebyshevBasis, Polynomial.Chebyshev.chebyshevTsequence]

private def chebyshevInner (m : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x, p.eval x * (Polynomial.Chebyshev.T ℝ m).eval x
      ∂Polynomial.Chebyshev.measureT
  map_add' p q := by
    simp only [eval_add, add_mul]
    rw [MeasureTheory.integral_add]
    · apply Polynomial.Chebyshev.integrable_measureT
      fun_prop
    · apply Polynomial.Chebyshev.integrable_measureT
      fun_prop
  map_smul' c p := by
    simp only [eval_smul, smul_eq_mul]
    rw [← MeasureTheory.integral_const_mul]
    congr with x
    simp only [RingHom.id_apply]
    ring

private theorem chebyshevInner_basis (m i : ℕ) :
    chebyshevInner m (chebyshevBasis i) =
      if i = m then (if m = 0 then Real.pi else Real.pi / 2) else 0 := by
  rw [chebyshevBasis_apply]
  unfold chebyshevInner
  by_cases him : i = m
  · subst i
    simp only [if_pos]
    by_cases hm : m = 0
    · subst m
      simpa using
        Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero
    · simp only [hm, if_false]
      exact Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hm
  · simp only [him, if_false]
    exact Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne him

private theorem chebyshevInner_eq_coord (p : ℝ[X]) (m : ℕ) :
    chebyshevInner m p =
      (if m = 0 then Real.pi else Real.pi / 2) * chebyshevBasis.coord m p := by
  -- Orthogonality determines both linear maps on every element of the basis.
  have hmaps : chebyshevInner m =
      (if m = 0 then Real.pi else Real.pi / 2) • chebyshevBasis.coord m := by
    apply chebyshevBasis.ext
    intro i
    rw [chebyshevInner_basis]
    simp only [LinearMap.smul_apply, smul_eq_mul, Basis.coord_apply,
      Basis.repr_self_apply]
    by_cases him : i = m
    · simp [him]
    · simp [him]
  exact LinearMap.congr_fun hmaps p

private theorem chebyshevCoefficient_eq_coord (p : ℝ[X]) (m : ℕ) :
    chebyshevCoefficient p m =
      if m = 0 then chebyshevBasis.coord m p else chebyshevBasis.coord m p / 2 := by
  -- Rewrite the weighted interval integral using the Chebyshev measure.
  have hint :
      (∫ x in (-1 : ℝ)..1,
          p.eval x * chebyshevT m x / Real.sqrt (1 - x ^ 2)) =
        chebyshevInner m p := by
    change (∫ x in (-1 : ℝ)..1,
          p.eval x * (Polynomial.Chebyshev.T ℝ m).eval x /
            Real.sqrt (1 - x ^ 2)) =
      ∫ x, p.eval x * (Polynomial.Chebyshev.T ℝ m).eval x
        ∂Polynomial.Chebyshev.measureT
    rw [Polynomial.Chebyshev.integral_measureT]
    simp only [div_eq_mul_inv, Real.sqrt_inv]
  unfold chebyshevCoefficient
  rw [hint, chebyshevInner_eq_coord]
  by_cases hm : m = 0
  · simp only [hm, if_pos]
    field_simp [Real.pi_ne_zero]
  · simp only [hm, if_false]
    field_simp [Real.pi_ne_zero]

/-- The `m`-th Chebyshev coefficient of a kernel polynomial is its kernel coefficient. -/
theorem chebyshevCoefficient_kernelPolynomial
    (n m : ℕ)
    (hm : m ≤ n)
    (u : Kernel) :
    chebyshevCoefficient (kernelPolynomial n u) m = u m := by
  -- Write the kernel polynomial explicitly in the Chebyshev basis.
  have hkpoly : kernelPolynomial n u =
      (u 0) • chebyshevBasis 0 +
        ∑ k ∈ Finset.Icc 1 n, (2 * u (k : ℤ)) • chebyshevBasis k := by
    simp [kernelPolynomial, chebyshevBasis_apply, Algebra.smul_def]
  rw [chebyshevCoefficient_eq_coord, hkpoly]
  by_cases hm0 : m = 0
  · subst m
    simp only [↓reduceIte, Basis.coord_apply, map_add, map_smul, Basis.repr_self,
      smul_eq_mul, mul_one, map_sum, Finsupp.single_eq_same, CharP.cast_eq_zero,
      add_eq_left]
    apply Finset.sum_eq_zero
    intro c hc
    rw [Finsupp.single_apply]
    simp only [Finset.mem_Icc] at hc
    simp [show c ≠ 0 by omega]
  · have hmmem : m ∈ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc]
      omega
    simp only [hm0, if_false, map_add, map_smul, map_sum, Basis.coord_apply,
      Basis.repr_self_apply, smul_eq_mul]
    simp [hmmem, Ne.symm hm0]

private theorem chebyshevCoord_eq_zero_of_natDegree_lt
    {p : ℝ[X]} {n m : ℕ}
    (hp : p.natDegree ≤ n)
    (hnm : n < m) :
    chebyshevBasis.coord m p = 0 := by
  let S := Polynomial.Chebyshev.chebyshevTsequence ℝ
  have hp_degreeLE : p ∈ Polynomial.degreeLE ℝ n := by
    rw [Polynomial.mem_degreeLE]
    exact degree_le_natDegree.trans (by exact_mod_cast hp)
  have hp_span_sequence : p ∈ Submodule.span ℝ (S '' Set.Iic n) := by
    rw [S.span_degreeLE (by simp)]
    exact hp_degreeLE
  have hp_span_basis : p ∈ Submodule.span ℝ (chebyshevBasis '' Set.Iic n) := by
    simpa [S, chebyshevBasis_apply,
      Polynomial.Chebyshev.chebyshevTsequence] using hp_span_sequence
  have hsupp := chebyshevBasis.repr_support_subset_of_mem_span
    (Set.Iic n) hp_span_basis
  change chebyshevBasis.repr p m = 0
  by_contra hm
  have hm_support : m ∈ (chebyshevBasis.repr p).support :=
    Finsupp.mem_support_iff.mpr hm
  have hm_le : m ≤ n := hsupp hm_support
  omega

/-- Two polynomials of degree at most `n` are equal when their first `n + 1`
Chebyshev coefficients agree. -/
theorem polynomial_eq_of_chebyshevCoefficient_eq
    {n : ℕ}
    {p q : ℝ[X]}
    (hp : p.natDegree ≤ n)
    (hq : q.natDegree ≤ n)
    (hcoeff : ∀ m ≤ n,
      chebyshevCoefficient p m = chebyshevCoefficient q m) :
    p = q := by
  apply chebyshevBasis.ext_elem
  intro m
  change chebyshevBasis.coord m p = chebyshevBasis.coord m q
  by_cases hm : m ≤ n
  · have h := hcoeff m hm
    rw [chebyshevCoefficient_eq_coord, chebyshevCoefficient_eq_coord] at h
    by_cases hm0 : m = 0
    · simpa [hm0] using h
    · simpa [hm0] using h
  · rw [chebyshevCoord_eq_zero_of_natDegree_lt hp (by omega),
      chebyshevCoord_eq_zero_of_natDegree_lt hq (by omega)]

end JoseSmoothest
