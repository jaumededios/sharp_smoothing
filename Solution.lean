import JoseSmoothest.Challenge
import JoseSmoothest.SixthOrder

/-!
# Comparator solution for sharp smoothing

The declarations in this file repeat the comparator statement API.  Their
proofs bridge to the complete formalization under `JoseSmoothest/`.
-/

noncomputable section

namespace JoseSmoothestComparator

open JoseSmoothest

/-- The `r`-fold forward-difference operator on square-summable sequences. -/
def iteratedDifferenceOperator (r : ℕ) : Sequence →L[ℝ] Sequence :=
  differenceOperator ^ r

/-- The norm of the `r`-fold difference after convolution by `u`. -/
def iteratedDifferenceSmoothness (r : ℕ) (u : Kernel) : ℝ :=
  ‖(iteratedDifferenceOperator r).comp (averagingOperator u)‖

/-- The explicit coefficient formula characterizing an equality case. -/
def IsExtremalKernel (n : ℕ) (u : Kernel) : Prop :=
  ∀ m : ℕ, m ≤ n →
    let coefficient :=
      1 / Real.pi *
        ∫ x in (-1 : ℝ)..1,
          extremalPolynomial n x * chebyshevT m x /
            Real.sqrt (1 - x ^ 2)
    u m = coefficient ∧ u (-(m : ℤ)) = coefficient

/-- Theorem 1.4: the claimed constant is a lower bound for every admissible
kernel of order `n`. -/
theorem smoothestAverage_inequality
    (n : ℕ)
    (_n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    sharpConstant n ≤ iteratedDifferenceSmoothness 4 u := by
  simpa [iteratedDifferenceSmoothness, iteratedDifferenceOperator,
    fourthOrderSmoothness] using
      JoseSmoothest.smoothestAverage_inequality n u admissible

/-- Theorem 1.4: for an admissible kernel, equality is equivalent to the
displayed Chebyshev coefficient formula. -/
theorem smoothestAverage_eq_iff
    (n : ℕ)
    (_n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    iteratedDifferenceSmoothness 4 u = sharpConstant n ↔
      IsExtremalKernel n u := by
  simpa only [iteratedDifferenceSmoothness, iteratedDifferenceOperator,
    fourthOrderSmoothness, IsExtremalKernel,
    JoseSmoothest.IsExtremalKernel] using
    JoseSmoothest.smoothestAverage_eq_iff n u admissible

/-- The sharp fourth-order constant is attained by a unique admissible kernel. -/
theorem smoothestAverage_existsUnique_optimizer
    (n : ℕ)
    (_n_positive : 0 < n) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧
        iteratedDifferenceSmoothness 4 u = sharpConstant n := by
  simpa only [iteratedDifferenceSmoothness, iteratedDifferenceOperator,
    fourthOrderSmoothness] using
      JoseSmoothest.existsUnique_extremalKernel n

/-- The sixth-difference norm is eight times the cubic weighted norm of the
kernel polynomial.  This is the operator-to-polynomial reduction used in
Theorem 1.7. -/
theorem sixthDifference_eq_cubicWeightedNorm
    (n : ℕ)
    (_n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    iteratedDifferenceSmoothness 6 u =
      8 * cubicWeightedPolynomialNorm (kernelPolynomial n u) := by
  simpa only [iteratedDifferenceSmoothness, iteratedDifferenceOperator,
    differenceSmoothness, differenceAfterAveraging] using
      differenceSmoothness_six_eq_eight_mul_cubicWeightedPolynomialNorm
        n u admissible.support admissible.symmetric

end JoseSmoothestComparator
