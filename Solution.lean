import JoseSmoothest.Challenge

/-!
# Comparator solution for the smoothest-average theorem

The declarations in this file repeat the comparator statement API.  Their
proofs bridge to the complete formalization under `JoseSmoothest/`.
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
    (_n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    sharpConstant n ≤ fourthOrderSmoothness u := by
  exact JoseSmoothest.smoothestAverage_inequality n u admissible

/-- Theorem 1.4: for an admissible kernel, equality is equivalent to the
displayed Chebyshev coefficient formula. -/
theorem smoothestAverage_eq_iff
    (n : ℕ)
    (_n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    fourthOrderSmoothness u = sharpConstant n ↔
      IsExtremalKernel n u := by
  simpa only [IsExtremalKernel, JoseSmoothest.IsExtremalKernel] using
    JoseSmoothest.smoothestAverage_eq_iff n u admissible

end JoseSmoothestComparator
