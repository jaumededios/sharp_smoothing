import JoseSmoothest.WeightedExtremal

/-!
# The smoothest-average theorem

This file assembles the Fourier reduction and the weighted Chebyshev extremal
problem into Theorem 1.4 of Gaitán--Garzón--Madrid, including the coefficient
description of the unique equality case.
-/

noncomputable section

namespace JoseSmoothest

/-- The explicit coefficient formula for the unique equality-case kernel. -/
def IsExtremalKernel (n : ℕ) (u : Kernel) : Prop :=
  ∀ m : ℕ, m ≤ n →
    let coefficient :=
      1 / Real.pi *
        ∫ x in (-1 : ℝ)..1,
          extremalPolynomial n x * chebyshevT m x /
            Real.sqrt (1 - x ^ 2)
    u m = coefficient ∧ u (-(m : ℤ)) = coefficient

theorem isExtremalKernel_iff_kernelPolynomial_eq
    (n : ℕ)
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    IsExtremalKernel n u ↔
      kernelPolynomial n u = weightedExtremalPolynomial (n + 2) := by
  have hcoefficient (m : ℕ) :
      chebyshevCoefficient (weightedExtremalPolynomial (n + 2)) m =
        1 / Real.pi *
          ∫ x in (-1 : ℝ)..1,
            extremalPolynomial n x * chebyshevT m x /
              Real.sqrt (1 - x ^ 2) := by
    unfold chebyshevCoefficient
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    simp only
    rw [weightedExtremalPolynomial_eval]
  constructor
  · intro hextremal
    apply polynomial_eq_of_chebyshevCoefficient_eq
    · exact kernelPolynomial_natDegree_le n u
    · simpa using weightedExtremalPolynomial_natDegree_le (n + 2) (by omega)
    · intro m hm
      rw [chebyshevCoefficient_kernelPolynomial n m hm u,
        hcoefficient m]
      exact (hextremal m hm).1
  · intro hpolynomial m hm
    have hpositive :
        u m = 1 / Real.pi *
          ∫ x in (-1 : ℝ)..1,
            extremalPolynomial n x * chebyshevT m x /
              Real.sqrt (1 - x ^ 2) := by
      rw [← hcoefficient m, ← hpolynomial,
        chebyshevCoefficient_kernelPolynomial n m hm u]
    exact ⟨hpositive, (symmetric (m : ℤ)).trans hpositive⟩

/-- Theorem 1.4, sharp inequality. -/
theorem smoothestAverage_inequality
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    sharpConstant n ≤ fourthOrderSmoothness u := by
  rcases admissible with ⟨support, symmetric, normalized, fourier_nonnegative⟩
  have hdeg : (kernelPolynomial n u).natDegree ≤ (n + 2) - 2 := by
    simpa using kernelPolynomial_natDegree_le n u
  have hnonnegative : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ (kernelPolynomial n u).eval x :=
    kernelPolynomial_nonnegative_on_Icc n u support symmetric
      fourier_nonnegative
  have hone : (kernelPolynomial n u).eval 1 = 1 :=
    kernelPolynomial_eval_one n u support symmetric normalized
  calc
    sharpConstant n =
        4 * weightedChebyshevConstant (n + 2) :=
      sharpConstant_eq_four_mul_weightedChebyshevConstant n
    _ ≤ 4 * weightedPolynomialNorm (kernelPolynomial n u) := by
      gcongr
      exact weightedPolynomialNorm_ge (n + 2) (by omega)
        (kernelPolynomial n u) hdeg hnonnegative hone
    _ = fourthOrderMultiplierNorm u :=
      (fourthOrderMultiplierNorm_eq_four_mul_weightedPolynomialNorm
        n u support symmetric).symm
    _ = fourthOrderSmoothness u :=
      (fourthOrderSmoothness_eq_multiplierNorm u symmetric).symm

/-- Theorem 1.4, equality characterization. -/
theorem smoothestAverage_eq_iff
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    fourthOrderSmoothness u = sharpConstant n ↔
      IsExtremalKernel n u := by
  rcases admissible with ⟨support, symmetric, normalized, fourier_nonnegative⟩
  have hdeg : (kernelPolynomial n u).natDegree ≤ (n + 2) - 2 := by
    simpa using kernelPolynomial_natDegree_le n u
  have hnonnegative : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ (kernelPolynomial n u).eval x :=
    kernelPolynomial_nonnegative_on_Icc n u support symmetric
      fourier_nonnegative
  have hone : (kernelPolynomial n u).eval 1 = 1 :=
    kernelPolynomial_eval_one n u support symmetric normalized
  rw [fourthOrderSmoothness_eq_multiplierNorm u symmetric,
    fourthOrderMultiplierNorm_eq_four_mul_weightedPolynomialNorm
      n u support symmetric,
    sharpConstant_eq_four_mul_weightedChebyshevConstant]
  constructor
  · intro hequality
    apply (isExtremalKernel_iff_kernelPolynomial_eq n u symmetric).2
    apply (weightedPolynomialNorm_eq_iff (n + 2) (by omega)
      (kernelPolynomial n u) hdeg hnonnegative hone).1
    linarith
  · intro hextremal
    have hpolynomial :=
      (isExtremalKernel_iff_kernelPolynomial_eq n u symmetric).1 hextremal
    have hnorm := (weightedPolynomialNorm_eq_iff (n + 2) (by omega)
      (kernelPolynomial n u) hdeg hnonnegative hone).2 hpolynomial
    linarith

end JoseSmoothest
