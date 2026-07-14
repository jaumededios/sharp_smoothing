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

/-- The forward difference `f(j+1)-f(j)` as a bounded operator on `L²(ℤ)`. -/
def differenceOperator : Sequence →L[ℝ] Sequence :=
  (translation (-1)).toContinuousLinearMap - ContinuousLinearMap.id ℝ Sequence

/-- Convolution by `u`, viewed as a bounded operator on `L²(ℤ)`. -/
def averagingOperator (u : Kernel) : Sequence →L[ℝ] Sequence :=
  u.sum fun k a ↦ a • (translation k).toContinuousLinearMap

end JoseSmoothest
```

## Detailed proof blueprint

`translation (-1)` composes with `j↦1+j`, so subtracting the identity gives
the forward difference.  A kernel is a `Finsupp`; its `sum` of the operators
`u(k)•translation(k)` is therefore a finite sum of continuous linear maps and
is exactly convolution by `u`.

In the Fourier module, unfold the linear-isometry application and use
`Lp.coeFn_compMeasurePreserving` (and equality in `Lp` via almost-everywhere
equality) to prove privately that these operators have the expected formulas
on representatives.  Keeping those lemmas private avoids exposing arbitrary
representative choices in the public API.
