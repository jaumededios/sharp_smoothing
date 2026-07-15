import JoseSmoothest.WeightedExtremal

/-!
# The smoothest-average theorem

This file assembles the Fourier reduction and the weighted Chebyshev extremal
problem into Theorem 1.4 of Gaitán--Garzón--Madrid, including the coefficient
characterization of equality among admissible kernels.
-/

noncomputable section

namespace JoseSmoothest

/-- An admissible kernel gives a feasible polynomial for the weighted
extremal problem after the substitution `x = cos ξ`. -/
theorem IsAdmissibleKernel.kernelPolynomial
    {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    IsAdmissibleWeightedPolynomial (n + 2) (kernelPolynomial n u) where
  degree_le := by
    simpa using kernelPolynomial_natDegree_le n u
  nonnegative :=
    kernelPolynomial_nonnegative_on_Icc n u h.support h.symmetric
      h.fourier_nonnegative
  eval_one :=
    kernelPolynomial_eval_one n u h.support h.symmetric h.sum_eq_one

/-- The kernel obtained from the Chebyshev coefficients of the extremal
polynomial in Proposition 1.6. -/
def extremalKernel (n : ℕ) : Kernel :=
  kernelOfPolynomial n (weightedExtremalPolynomial (n + 2))

/-- The polynomial symbol of `extremalKernel` is the extremal polynomial. -/
theorem kernelPolynomial_extremalKernel (n : ℕ) :
    kernelPolynomial n (extremalKernel n) =
      weightedExtremalPolynomial (n + 2) := by
  apply kernelPolynomial_kernelOfPolynomial
  simpa using weightedExtremalPolynomial_natDegree_le (n + 2) (by omega)

/-- The coefficient-defined extremal kernel satisfies all four hypotheses of
Theorem 1.4. -/
theorem extremalKernel_isAdmissible (n : ℕ) :
    IsAdmissibleKernel n (extremalKernel n) := by
  apply kernelOfPolynomial_isAdmissible
  · simpa using weightedExtremalPolynomial_natDegree_le (n + 2) (by omega)
  · exact weightedExtremalPolynomial_nonnegative (n + 2) (by omega)
  · exact weightedExtremalPolynomial_eval_one (n + 2) (by omega)

/-- The explicit coefficient formula characterizing an equality case. -/
def IsExtremalKernel (n : ℕ) (u : Kernel) : Prop :=
  ∀ m : ℕ, m ≤ n →
    let coefficient :=
      1 / Real.pi *
        ∫ x in (-1 : ℝ)..1,
          extremalPolynomial n x * chebyshevT m x /
            Real.sqrt (1 - x ^ 2)
    u m = coefficient ∧ u (-(m : ℤ)) = coefficient

/-- For a symmetric kernel, the coefficient formula is equivalent to the
corresponding identity between its kernel polynomial and the extremizer of the
weighted polynomial problem. -/
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

/-- Theorem 1.4, lower bound with the paper's stated constant. -/
theorem smoothestAverage_inequality
    (n : ℕ)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    sharpConstant n ≤ fourthOrderSmoothness u := by
  calc
    sharpConstant n =
        4 * weightedChebyshevConstant (n + 2) :=
      sharpConstant_eq_four_mul_weightedChebyshevConstant n
    _ ≤ 4 * weightedPolynomialNorm (kernelPolynomial n u) := by
      gcongr
      exact admissible.kernelPolynomial.norm_ge (by omega)
    _ = fourthOrderMultiplierNorm u :=
      (fourthOrderMultiplierNorm_eq_four_mul_weightedPolynomialNorm
        n u admissible.support admissible.symmetric).symm
    _ = fourthOrderSmoothness u :=
      (fourthOrderSmoothness_eq_multiplierNorm u admissible.symmetric).symm

/-- Theorem 1.4, equality characterization. -/
theorem smoothestAverage_eq_iff
    (n : ℕ)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    fourthOrderSmoothness u = sharpConstant n ↔
      IsExtremalKernel n u := by
  rw [fourthOrderSmoothness_eq_multiplierNorm u admissible.symmetric,
    fourthOrderMultiplierNorm_eq_four_mul_weightedPolynomialNorm
      n u admissible.support admissible.symmetric,
    sharpConstant_eq_four_mul_weightedChebyshevConstant]
  constructor
  · intro hequality
    apply (isExtremalKernel_iff_kernelPolynomial_eq n u admissible.symmetric).2
    apply (admissible.kernelPolynomial.norm_eq_iff (by omega)).1
    linarith
  · intro hextremal
    have hpolynomial :=
      (isExtremalKernel_iff_kernelPolynomial_eq n u admissible.symmetric).1 hextremal
    have hnorm :=
      (admissible.kernelPolynomial.norm_eq_iff (by omega)).2 hpolynomial
    linarith

/-- The explicit coefficient-defined kernel satisfies the equality formula
from Theorem 1.4. -/
theorem extremalKernel_isExtremal (n : ℕ) :
    IsExtremalKernel n (extremalKernel n) := by
  apply (isExtremalKernel_iff_kernelPolynomial_eq n (extremalKernel n)
    (extremalKernel_isAdmissible n).symmetric).2
  exact kernelPolynomial_extremalKernel n

/-- The coefficient-defined admissible kernel attains the sharp constant. -/
theorem extremalKernel_attains (n : ℕ) :
    fourthOrderSmoothness (extremalKernel n) = sharpConstant n := by
  exact (smoothestAverage_eq_iff n (extremalKernel n)
    (extremalKernel_isAdmissible n)).2 (extremalKernel_isExtremal n)

/-- The sharp fourth-order constant is attained by an admissible kernel. -/
theorem exists_extremalKernel (n : ℕ) :
    ∃ u : Kernel,
      IsAdmissibleKernel n u ∧
        fourthOrderSmoothness u = sharpConstant n :=
  ⟨extremalKernel n, extremalKernel_isAdmissible n,
    extremalKernel_attains n⟩

/-- Every admissible kernel attaining the sharp constant is the explicit
coefficient-defined kernel. -/
theorem eq_extremalKernel_of_attains
    (n : ℕ)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u)
    (attains : fourthOrderSmoothness u = sharpConstant n) :
    u = extremalKernel n := by
  apply kernel_eq_of_kernelPolynomial_eq n admissible.support
    admissible.symmetric (extremalKernel_isAdmissible n).support
    (extremalKernel_isAdmissible n).symmetric
  have hextremal := (smoothestAverage_eq_iff n u admissible).1 attains
  exact ((isExtremalKernel_iff_kernelPolynomial_eq n u
    admissible.symmetric).1 hextremal).trans
      (kernelPolynomial_extremalKernel n).symm

/-- There is a unique admissible kernel attaining the sharp fourth-order
constant. -/
theorem existsUnique_extremalKernel (n : ℕ) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧
        fourthOrderSmoothness u = sharpConstant n := by
  refine ⟨extremalKernel n,
    ⟨extremalKernel_isAdmissible n, extremalKernel_attains n⟩, ?_⟩
  intro u hu
  exact eq_extremalKernel_of_attains n u hu.1 hu.2

end JoseSmoothest
