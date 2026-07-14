# Blueprint for `JoseSmoothest/Challenge.lean`

## Purpose

This module contains the complete paper-facing Theorem 1.4: both the sharp
inequality and the characterization of equality by the coefficient formula
(1.6).  All analytic and approximation-theoretic work is imported; this file
only assembles the established equivalences.

## Imports

```lean
import JoseSmoothest.WeightedExtremal
```

## Public declarations

```lean
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
      kernelPolynomial n u = weightedExtremalPolynomial (n + 2)

/-- Theorem 1.4, sharp inequality. -/
theorem smoothestAverage_inequality
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    sharpConstant n ≤ fourthOrderSmoothness u

/-- Theorem 1.4, equality characterization. -/
theorem smoothestAverage_eq_iff
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    fourthOrderSmoothness u = sharpConstant n ↔
      IsExtremalKernel n u

end JoseSmoothest
```

## Detailed proof blueprint

### Kernel coefficient characterization

Use `weightedExtremalPolynomial_eval` to rewrite the integral in
`IsExtremalKernel` as
`chebyshevCoefficient (weightedExtremalPolynomial (n+2)) m`.

For the forward direction, `chebyshevCoefficient_kernelPolynomial` rewrites
the coefficient of `kernelPolynomial n u` as `u m`.  Thus the two polynomials
have equal Chebyshev coefficients through degree `n`.  Their degree bounds
come from `kernelPolynomial_natDegree_le` and
`weightedExtremalPolynomial_natDegree_le`; apply
`polynomial_eq_of_chebyshevCoefficient_eq`.

Conversely, polynomial equality and coefficient extraction give the positive
coefficient formula.  The hypothesis `symmetric` gives the formula at `-m`.
This proves `isExtremalKernel_iff_kernelPolynomial_eq`.

### Common reduction for both main statements

Decompose `admissible` into support, symmetry, mass normalization, and Fourier
nonnegativity.  Put `p=kernelPolynomial n u` and `N=n+2`.  Then:

1. `kernelPolynomial_natDegree_le` gives `p.natDegree≤N-2`;
2. `kernelPolynomial_eval_one` gives `p(1)=1`;
3. `kernelPolynomial_nonnegative_on_Icc` gives `p≥0` on `[-1,1]`;
4. the Fourier and cosine bridge gives the exact chain

   `fourthOrderSmoothness u`
   `= fourthOrderMultiplierNorm u`
   `= 4 * weightedPolynomialNorm p`;

5. `sharpConstant_eq_four_mul_weightedChebyshevConstant` rewrites the target
   constant with the same factor four.

### `smoothestAverage_inequality`

Apply `weightedPolynomialNorm_ge N` to `p`, multiply its inequality by four,
and rewrite both sides with the identities above.  Positivity of four lets
`gcongr` discharge the order step.  `n_positive` is stronger than needed for
the inequality but is retained because it is part of the authoritative
Theorem 1.4 statement.

### `smoothestAverage_eq_iff`

Use the exact norm identities to transform

`fourthOrderSmoothness u = sharpConstant n`

into

`weightedPolynomialNorm p = weightedChebyshevConstant (n+2)`.

The positive factor four cancels.  Apply
`weightedPolynomialNorm_eq_iff` to turn this into
`p=weightedExtremalPolynomial (n+2)`, then apply
`isExtremalKernel_iff_kernelPolynomial_eq` in reverse.  Every arrow is an
equivalence, so this proves both directions and uniqueness simultaneously.

