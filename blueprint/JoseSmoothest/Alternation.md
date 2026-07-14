# Blueprint for `JoseSmoothest/Alternation.lean`

## Purpose

This module isolates the root-counting form of the alternation principle.  It
is the only genuinely reusable approximation-theory lemma needed for the
weighted Chebyshev argument.  Weak inequalities are essential: at an
alternation node the competing polynomial may also vanish, in which case the
proof must count the resulting root with its correct multiplicity.

## Imports

```lean
import Mathlib
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

/-- A polynomial of degree `< m` cannot have weakly alternating signs at
`m + 1` strictly ordered points unless it is zero. -/
theorem polynomial_eq_zero_of_alternating_signs
    {m : ℕ}
    (hm : 0 < m)
    {p : ℝ[X]}
    (hdeg : p.natDegree < m)
    {x : Fin (m + 1) → ℝ}
    (hx : StrictMono x)
    (halt : ∀ i : Fin (m + 1),
      0 ≤ (-1 : ℝ) ^ (i : ℕ) * p.eval (x i)) :
    p = 0

end JoseSmoothest
```

## Detailed proof blueprint

The formal proof uses Lagrange interpolation instead of root-multiplicity
bookkeeping.  This is both shorter and better aligned with Mathlib's existing
approximation-theory API.

Assume `p ≠ 0` and interpolate it at the `m+1` nodes `x i`.  Since
`p.natDegree < m`, the coefficient of `X^m` is zero.  Mathlib's
`Lagrange.coeff_eq_sum` therefore gives

```text
Σ i, p(x i) / Π j≠i (x i - x j) = 0.
```

For each `i`, split the denominator product into the indices below and above
`i`.  Strict monotonicity makes every factor below `i` positive and every
factor above `i` negative.  There are exactly `m-i` factors above `i`, using
`Fin.card_Ioi`; hence

```text
0 < (-1)^(m-i) * Π j≠i (x i - x j).
```

The same sign statement holds for the inverse denominator.  Multiplying the
`i`-th Lagrange summand by the common sign `(-1)^m` rewrites it as the product

```text
((-1)^i * p(x i)) *
  ((-1)^(m-i) * (Π j≠i (x i-x j))⁻¹).
```

The first factor is nonnegative by `halt`, while the second is strictly
positive.  Thus every term of the signed Lagrange sum is nonnegative.  Their
sum is zero, so `Fintype.sum_eq_zero_iff_of_nonneg` forces every term to be
zero, and the nonzero sign and denominator factors give `p.eval (x i)=0` for
all `i`.

Finally apply
`Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero` to the injective node
map (injectivity follows from `hx.injective`) and the same degree bound.  This
concludes `p=0` without any analytic intermediate-value or multiplicity
argument.
