import JoseSmoothest.EvenOrder.WeightedMinimax

/-!
# Fourier reduction for an arbitrary even difference

This file identifies the norm of a difference of order `2 * m` with `2 ^ m`
times the corresponding weighted polynomial norm.
-/

noncomputable section

namespace JoseSmoothest

/-- An admissible kernel gives an admissible polynomial for the weighted
problem at every half-order `m`. -/
theorem IsAdmissibleKernel.evenWeightedKernelPolynomial
    {m n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    IsAdmissibleEvenWeightedPolynomial m (n + m) (kernelPolynomial n u) where
  degree_le := by
    simpa using kernelPolynomial_natDegree_le n u
  nonnegative :=
    kernelPolynomial_nonnegative_on_Icc n u h.support h.symmetric
      h.fourier_nonnegative
  eval_one :=
    kernelPolynomial_eval_one n u h.support h.symmetric h.sum_eq_one

/-- The norm of an even difference is `2 ^ m` times the weighted norm of the
kernel polynomial. -/
theorem differenceSmoothness_two_mul_eq_pow_mul_evenWeightedPolynomialNorm
    (m n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    differenceSmoothness (2 * m) u =
      (2 : ℝ) ^ m * evenWeightedPolynomialNorm m (kernelPolynomial n u) := by
  let p := kernelPolynomial n u
  let A : Set ℝ := {a : ℝ | ∃ ξ : ℝ, a = differenceMultiplier (2 * m) u ξ}
  let B : Set ℝ := {b : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    b = |(1 - x) ^ m * p.eval x|}
  let c : ℝ := (2 : ℝ) ^ m
  have hcpos : 0 < c := by positivity
  have hvalue (ξ : ℝ) : differenceMultiplier (2 * m) u ξ =
      c * |(1 - Real.cos ξ) ^ m * p.eval (Real.cos ξ)| := by
    rw [differenceMultiplier_two_mul]
    rw [kernelPolynomial_eval_cos n u support symmetric]
    have hnonneg : 0 ≤ (1 - Real.cos ξ) ^ m :=
      pow_nonneg (sub_nonneg.mpr (Real.cos_le_one ξ)) m
    rw [mul_pow, abs_mul, abs_of_nonneg hnonneg]
    simp only [c]
    ring
  have hB_nonempty : B.Nonempty := by
    refine ⟨|(1 - 0) ^ m * p.eval 0|, 0, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hB_bdd : BddAbove B := by
    let g : ℝ → ℝ := fun x ↦ |(1 - x) ^ m * p.eval x|
    have hg : Continuous g := by
      unfold g
      fun_prop
    have hB : B = g '' Set.Icc (-1 : ℝ) 1 := by
      ext b
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [hB]
    exact (isCompact_Icc.image hg).bddAbove
  have hA_nonempty : A.Nonempty :=
    ⟨differenceMultiplier (2 * m) u 0, 0, rfl⟩
  have hA_bdd : BddAbove A := by
    obtain ⟨K, hK⟩ := hB_bdd
    refine ⟨c * K, ?_⟩
    rintro a ⟨ξ, rfl⟩
    rw [hvalue]
    exact mul_le_mul_of_nonneg_left
      (hK ⟨Real.cos ξ, ⟨Real.neg_one_le_cos ξ, Real.cos_le_one ξ⟩, rfl⟩)
      hcpos.le
  rw [differenceSmoothness_eq_multiplierNorm (2 * m) u symmetric]
  change sSup A = c * sSup B
  apply le_antisymm
  · apply csSup_le hA_nonempty
    rintro a ⟨ξ, rfl⟩
    rw [hvalue]
    exact mul_le_mul_of_nonneg_left
      (le_csSup hB_bdd
        ⟨Real.cos ξ, ⟨Real.neg_one_le_cos ξ, Real.cos_le_one ξ⟩, rfl⟩)
      hcpos.le
  · rw [mul_comm]
    apply (le_div_iff₀ hcpos).mp
    apply csSup_le hB_nonempty
    rintro b ⟨x, hx, rfl⟩
    apply (le_div_iff₀ hcpos).mpr
    have hle := le_csSup hA_bdd
      (⟨Real.arccos x, rfl⟩ : differenceMultiplier (2 * m) u (Real.arccos x) ∈ A)
    rw [hvalue, Real.cos_arccos hx.1 hx.2] at hle
    simpa [mul_comm] using hle

end JoseSmoothest
