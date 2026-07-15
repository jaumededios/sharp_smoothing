import JoseSmoothest.SixthOrder
import JoseSmoothest.WeightedExtremal

/-!
# Comparator statement showcase for sharp smoothing

This file is the statement side of the `leanprover/comparator` boundary.  It
contains the paper-facing fourth-order claims and the exact sixth-order
reduction whose fidelity a reviewer must inspect.  The candidate declarations
in `Solution.lean` must have definitionally identical types and must pass the
configured axiom check.
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
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    sharpConstant n ≤ iteratedDifferenceSmoothness 4 u := by
  sorry

/-- Theorem 1.4: for an admissible kernel, equality is equivalent to the
displayed Chebyshev coefficient formula. -/
theorem smoothestAverage_eq_iff
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    iteratedDifferenceSmoothness 4 u = sharpConstant n ↔
      IsExtremalKernel n u := by
  sorry

/-- The sharp fourth-order constant is attained by a unique admissible kernel. -/
theorem smoothestAverage_existsUnique_optimizer
    (n : ℕ)
    (n_positive : 0 < n) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧
        iteratedDifferenceSmoothness 4 u = sharpConstant n := by
  sorry

/-- The sixth-difference norm is eight times the cubic weighted norm of the
kernel polynomial.  This is the operator-to-polynomial reduction used in
Theorem 1.7. -/
theorem sixthDifference_eq_cubicWeightedNorm
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    iteratedDifferenceSmoothness 6 u =
      8 * cubicWeightedPolynomialNorm (kernelPolynomial n u) := by
  sorry

end JoseSmoothestComparator
