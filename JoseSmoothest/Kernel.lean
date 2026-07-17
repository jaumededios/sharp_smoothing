import JoseSmoothest.Basic

/-!
# Difference and averaging operators

This file bundles the forward difference and finite convolution as continuous
linear operators on `L²(ℤ)`.

## Main definitions

* `JoseSmoothest.differenceOperator`: the forward-difference operator.
* `JoseSmoothest.averagingOperator`: convolution by a finitely supported kernel.
* `JoseSmoothest.differenceAfterAveraging`: an arbitrary iterated difference after convolution.
-/

noncomputable section

namespace JoseSmoothest

/-- The forward difference `f(j + 1) - f(j)`, as a bounded operator on `ℓ²(ℤ)`. -/
def differenceOperator : Sequence →L[ℝ] Sequence :=
  (translation (-1)).toContinuousLinearMap - ContinuousLinearMap.id ℝ Sequence

/-- Convolution by `u`, viewed as a bounded operator on `ℓ²(ℤ)`. -/
def averagingOperator (u : Kernel) : Sequence →L[ℝ] Sequence :=
  u.sum fun k a ↦ a • (translation k).toContinuousLinearMap

/-- The `r`-fold forward difference after convolution by `u`. -/
def differenceAfterAveraging (r : ℕ) (u : Kernel) : Sequence →L[ℝ] Sequence :=
  (differenceOperator ^ r).comp (averagingOperator u)

end JoseSmoothest
