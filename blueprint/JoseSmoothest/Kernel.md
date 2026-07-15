# Blueprint for `JoseSmoothest/Kernel.lean`

## Purpose

This module builds the bounded forward-difference and finite-convolution
operators used verbatim in Theorem 1.4.

## Imports

```lean
import JoseSmoothest.Basic
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

/-- The forward difference `f(j + 1) - f(j)`, as a bounded operator on `ℓ²(ℤ)`. -/
def differenceOperator : Sequence →L[ℝ] Sequence :=
  (translation (-1)).toContinuousLinearMap - ContinuousLinearMap.id ℝ Sequence

/-- Convolution by `u`, viewed as a bounded operator on `ℓ²(ℤ)`. -/
def averagingOperator (u : Kernel) : Sequence →L[ℝ] Sequence :=
  u.sum fun k a ↦ a • (translation k).toContinuousLinearMap

end JoseSmoothest
```

## Detailed proof blueprint

### `differenceOperator`

By the definition in the preceding module, `translation (-1)` sends the
coefficient at `j` to the coefficient at `-(-1) + j = j + 1`.  Coercing this
linear isometry to a continuous linear map and subtracting the identity map
therefore sends `f(j)` to `f(j + 1) - f(j)`.  Continuous linear maps are closed
under subtraction, so the result is automatically a bounded operator.

### `averagingOperator`

A kernel `u` is a `Finsupp`, so `u.sum` forms the finite sum of the continuous
linear maps `u(k) • translation(k)`.  Applying the sum to a sequence `f` gives
the finite convolution `∑ k, u(k) f(j - k)` at coefficient `j`.  Finite sums
and scalar multiples of continuous linear maps remain continuous, hence this
definition also packages boundedness without a separate analytic argument.

In the Fourier module, unfold the linear-isometry application and use
`Lp.coeFn_compMeasurePreserving` together with extensionality by
almost-everywhere equality to verify these pointwise descriptions.  Those
representative-level lemmas stay private because the public operators do not
depend on a choice of `Lp` representative.
