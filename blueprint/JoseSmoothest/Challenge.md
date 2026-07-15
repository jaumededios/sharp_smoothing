# Blueprint for `JoseSmoothest/Challenge.lean`

## Purpose

This module contains the formalized part of paper-facing Theorem 1.4: the
lower bound and, for an already-admissible kernel, the characterization of
equality by the coefficient formula (1.6). All analytic and
approximation-theoretic work is imported; this file only assembles the
established equivalences. It does not construct the coefficient-defined
kernel or prove it admissible.

## Imports

```lean
import JoseSmoothest.WeightedExtremal
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

/-- An admissible kernel gives a feasible polynomial for the weighted
extremal problem after the substitution `x = cos ξ`. -/
theorem IsAdmissibleKernel.kernelPolynomial
    {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    IsAdmissibleWeightedPolynomial (n + 2) (kernelPolynomial n u)

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
      kernelPolynomial n u = weightedExtremalPolynomial (n + 2)

/-- Theorem 1.4, lower bound with the paper's stated constant. -/
theorem smoothestAverage_inequality
    (n : ℕ)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    sharpConstant n ≤ fourthOrderSmoothness u

/-- Theorem 1.4, equality characterization. -/
theorem smoothestAverage_eq_iff
    (n : ℕ)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    fourthOrderSmoothness u = sharpConstant n ↔
      IsExtremalKernel n u

end JoseSmoothest
```

## Detailed proof blueprint

### Polynomial feasibility

For `h : IsAdmissibleKernel n u`, construct
`h.kernelPolynomial : IsAdmissibleWeightedPolynomial (n+2)
(kernelPolynomial n u)`. The required fields are exactly the three bridge
theorems from `Chebyshev.lean`: `kernelPolynomial_natDegree_le` supplies the
degree bound (after simplifying `(n+2)-2`),
`kernelPolynomial_nonnegative_on_Icc` uses `h.support`, `h.symmetric`, and
`h.fourier_nonnegative`, and `kernelPolynomial_eval_one` uses the support,
symmetry, and `h.sum_eq_one` projections.

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

Use the four stable dot-notation projections of `admissible`. Put
`p=kernelPolynomial n u` and `N=n+2`. Then:

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

Apply `admissible.kernelPolynomial.norm_ge` to the packaged feasible
polynomial, multiply its inequality by four, and rewrite both sides with the
identities above. Positivity of four lets `gcongr` discharge the order step.
The proof actually works at `n = 0`, so the reusable library theorem omits
the paper's stronger `0 < n` assumption. The `Showcase.lean` comparator
boundary retains that assumption verbatim.

### `smoothestAverage_eq_iff`

Use the exact norm identities to transform

`fourthOrderSmoothness u = sharpConstant n`

into

`weightedPolynomialNorm p = weightedChebyshevConstant (n+2)`.

The positive factor four cancels. Apply
`admissible.kernelPolynomial.norm_eq_iff` to turn this into
`p=weightedExtremalPolynomial (n+2)`, then apply
`isExtremalKernel_iff_kernelPolynomial_eq` in reverse.  Every arrow is an
equivalence, so this proves both directions and uniqueness simultaneously.
