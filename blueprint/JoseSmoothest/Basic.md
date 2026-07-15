# Blueprint for `JoseSmoothest/Basic.lean`

## Purpose

This module fixes the two bundled types in the authoritative challenge: real
`L²(ℤ)` for counting measure and finitely supported real kernels.  Translation
is obtained directly from Mathlib's action of measure-preserving maps on
`Lp`, so norm preservation requires no project-specific summability theory.

## Imports

```lean
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
```

## Public declarations

```lean
noncomputable section

open MeasureTheory

namespace JoseSmoothest

/-- The real Hilbert space `L²(ℤ)` for counting measure on the integers. -/
abbrev Sequence := Lp ℝ 2 (Measure.count : Measure ℤ)

/-- A real-valued kernel with finite support on `ℤ`. -/
abbrev Kernel := ℤ →₀ ℝ

/-- Translation by `k`, sending `f(j)` to `f(j-k)`, as an isometry of `L²(ℤ)`. -/
def translation (k : ℤ) : Sequence →ₗᵢ[ℝ] Sequence :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun j : ℤ ↦ -k + j)
    (measurePreserving_vadd (-k) (Measure.count : Measure ℤ))

end JoseSmoothest
```

## Detailed proof blueprint

### `Sequence`

This is a type abbreviation, so there is no proposition to prove.  Instantiate
Mathlib's bundled `Lp` space with scalar field `ℝ`, exponent `2`, underlying
space `ℤ`, and counting measure.  The resulting type carries the real Hilbert
space and normed-space structure needed by every later operator.

### `Kernel`

Again this is a type abbreviation rather than a theorem.  A finitely supported
function `ℤ →₀ ℝ` records the coefficients of a convolution kernel and makes
every coefficient sum definitionally finite.  No separate summability
hypothesis is therefore required.

### `translation`

Counting measure is invariant under addition by any integer.  Mathlib's
`measurePreserving_vadd` supplies the corresponding `MeasurePreserving` proof
for `j ↦ -k + j`, and `Lp.compMeasurePreservingₗᵢ` turns composition with that
map into a linear isometry on `L²`.  Since `-k + j = j - k`, this is precisely
the translation used in convolution.  All later pointwise formulas are
established as almost-everywhere equalities through the
`Lp.compMeasurePreservingₗᵢ` API and remain private to the Fourier proof.
