# Blueprint for `JoseSmoothest/Challenge.lean`

## Purpose

This module completes paper-facing Theorem 1.4. It proves the lower bound and
the coefficient characterization of equality, constructs the kernel from the
Chebyshev coefficients of the extremal polynomial, proves that this kernel is
admissible and attains the sharp constant, and proves that it is the unique
admissible optimizer. All analytic and approximation-theoretic work is
imported; this file assembles those results at the kernel level.

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

/-- The kernel obtained from the Chebyshev coefficients of the extremal
polynomial in Proposition 1.6. -/
def extremalKernel (n : ℕ) : Kernel :=
  kernelOfPolynomial n (weightedExtremalPolynomial (n + 2))

/-- The polynomial symbol of `extremalKernel` is the extremal polynomial. -/
theorem kernelPolynomial_extremalKernel (n : ℕ) :
    kernelPolynomial n (extremalKernel n) =
      weightedExtremalPolynomial (n + 2)

/-- The coefficient-defined extremal kernel satisfies all four hypotheses of
Theorem 1.4. -/
theorem extremalKernel_isAdmissible (n : ℕ) :
    IsAdmissibleKernel n (extremalKernel n)

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

/-- The explicit coefficient-defined kernel satisfies the equality formula
from Theorem 1.4. -/
theorem extremalKernel_isExtremal (n : ℕ) :
    IsExtremalKernel n (extremalKernel n)

/-- The coefficient-defined admissible kernel attains the sharp constant. -/
theorem extremalKernel_attains (n : ℕ) :
    fourthOrderSmoothness (extremalKernel n) = sharpConstant n

/-- The sharp fourth-order constant is attained by an admissible kernel. -/
theorem exists_extremalKernel (n : ℕ) :
    ∃ u : Kernel,
      IsAdmissibleKernel n u ∧
        fourthOrderSmoothness u = sharpConstant n

/-- Every admissible kernel attaining the sharp constant is the explicit
coefficient-defined kernel. -/
theorem eq_extremalKernel_of_attains
    (n : ℕ)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u)
    (attains : fourthOrderSmoothness u = sharpConstant n) :
    u = extremalKernel n

/-- There is a unique admissible kernel attaining the sharp fourth-order
constant. -/
theorem existsUnique_extremalKernel (n : ℕ) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧
        fourthOrderSmoothness u = sharpConstant n

end JoseSmoothest
```

## Detailed proof blueprint

### `IsAdmissibleKernel.kernelPolynomial`

For `h : IsAdmissibleKernel n u`, construct
`h.kernelPolynomial : IsAdmissibleWeightedPolynomial (n+2)
(kernelPolynomial n u)`. The required fields are exactly the three bridge
theorems from `Chebyshev.lean`: `kernelPolynomial_natDegree_le` supplies the
degree bound (after simplifying `(n+2)-2`),
`kernelPolynomial_nonnegative_on_Icc` uses `h.support`, `h.symmetric`, and
`h.fourier_nonnegative`, and `kernelPolynomial_eval_one` uses the support,
symmetry, and `h.sum_eq_one` projections.

### `extremalKernel`

Apply `kernelOfPolynomial` to the unique weighted extremal polynomial at the
shifted degree `N=n+2`. The result is, by definition, the finitely supported
symmetric kernel whose entries are the Chebyshev coefficients appearing in
formula (1.6).

### `kernelPolynomial_extremalKernel`

Use `kernelPolynomial_kernelOfPolynomial`. The only obligation is that the
weighted extremal polynomial has degree at most `n`; this follows from
`weightedExtremalPolynomial_natDegree_le` at `N=n+2`, whose bound `N-2`
simplifies to `n`.

### `extremalKernel_isAdmissible`

Apply `kernelOfPolynomial_isAdmissible` to the weighted extremal polynomial.
Its degree bound is the one used above. Its nonnegativity on `[-1,1]` and its
value one at the right endpoint are exactly
`weightedExtremalPolynomial_nonnegative` and
`weightedExtremalPolynomial_eval_one`. The generic polynomial-to-kernel
theorem then supplies support, symmetry, normalization, and Fourier
nonnegativity together.

### `IsExtremalKernel`

This predicate records formula (1.6) directly at every index `0 ≤ m ≤ n`.
The same integral is required at `m` and `-m`, so the definition contains
both the Chebyshev coefficient formula and the symmetry of the proposed
optimizer on its supported indices.

### `isExtremalKernel_iff_kernelPolynomial_eq`

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
equivalence, so this proves both directions of the equality characterization.

### `extremalKernel_isExtremal`

Apply `isExtremalKernel_iff_kernelPolynomial_eq` using the symmetry field of
`extremalKernel_isAdmissible`. The resulting polynomial equality is precisely
`kernelPolynomial_extremalKernel`.

### `extremalKernel_attains`

Use the reverse implication of `smoothestAverage_eq_iff` for the explicit
kernel. Its admissibility comes from `extremalKernel_isAdmissible`, and the
coefficient condition comes from `extremalKernel_isExtremal`. This gives the
sharp norm equality.

### `exists_extremalKernel`

Take `extremalKernel n` as the witness and package its admissibility and
attainment theorems into the required conjunction.

### `eq_extremalKernel_of_attains`

Suppose an admissible kernel `u` attains the sharp constant. The forward
implication of `smoothestAverage_eq_iff` shows that `u` satisfies the
coefficient formula. Convert this with
`isExtremalKernel_iff_kernelPolynomial_eq` into equality of its kernel
polynomial with the weighted optimizer. The explicit kernel has the same
polynomial by `kernelPolynomial_extremalKernel`. Finally apply
`kernel_eq_of_kernelPolynomial_eq` to these polynomial identities and the
support and symmetry fields of the two admissibility proofs, obtaining
`u = extremalKernel n`.

### `existsUnique_extremalKernel`

Use `extremalKernel n` as the existence witness, with
`extremalKernel_isAdmissible` and `extremalKernel_attains` proving the target
property. For uniqueness, any other witness satisfies the hypotheses of
`eq_extremalKernel_of_attains`, so it equals the explicit kernel. This
packages construction, attainment, and uniqueness into a single `∃!`
statement.
