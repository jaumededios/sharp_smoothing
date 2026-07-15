import JoseSmoothest.WeightedExtremal

/-!
# Comparator statement showcase for the smoothest-average theorem

This file is the statement side of the `leanprover/comparator` boundary.  It
contains the paper-facing claims whose fidelity a reviewer must inspect.  The
candidate declarations in `Solution.lean` must have definitionally identical
types and must pass the configured axiom check.
-/

noncomputable section

namespace JoseSmoothestComparator

open JoseSmoothest

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
    sharpConstant n ≤ fourthOrderSmoothness u := by
  sorry

/-- Theorem 1.4: for an admissible kernel, equality is equivalent to the
displayed Chebyshev coefficient formula. -/
theorem smoothestAverage_eq_iff
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    fourthOrderSmoothness u = sharpConstant n ↔
      IsExtremalKernel n u := by
  sorry

end JoseSmoothestComparator
