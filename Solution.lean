import JoseSmoothest.Challenge

/-!
# Comparator solution for the smoothest-average theorem

The declarations in this file repeat the trusted challenge API.  Their proofs
bridge to the complete formalization under `JoseSmoothest/`.
-/

noncomputable section

namespace JoseSmoothestComparator

open JoseSmoothest

/-- The explicit coefficient formula for the unique equality-case kernel. -/
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
  exact JoseSmoothest.smoothestAverage_inequality n n_positive u admissible

/-- Theorem 1.4: equality holds exactly for the kernel with the displayed
Chebyshev coefficient formula. -/
theorem smoothestAverage_eq_iff
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    fourthOrderSmoothness u = sharpConstant n ↔
      IsExtremalKernel n u := by
  simpa only [IsExtremalKernel, JoseSmoothest.IsExtremalKernel] using
    JoseSmoothest.smoothestAverage_eq_iff n n_positive u admissible

end JoseSmoothestComparator
