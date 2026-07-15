# Blueprint for `JoseSmoothest/SpecialFunctions/ThirdKindDifferential.lean`

## Purpose

For an even-degree hyperelliptic curve `y²=D(x)`, this module constructs the
unique differential

```text
η = A(x) dx / y
```

with residues `-1,+1` at the two infinities and purely imaginary periods.
This is the distinguished differential of the third kind used in the
Pell--Abel criterion.  The endpoint extremal problem will later impose the
additional, highly restrictive identity `A=(X-1)^g`.

## Imports

```lean
import JoseSmoothest.SpecialFunctions.RiemannBilinear
import Mathlib.LinearAlgebra.Matrix.PosDef
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest.Hyperelliptic

open Polynomial Complex
open scoped ComplexConjugate

namespace Curve

variable {g : ℕ} (C : Curve g)

def IsNormalizedThirdKind (A : ℝ[X]) : Prop :=
  A.natDegree ≤ g ∧ A.coeff g = 1 ∧
    ∀ cyc : C.ClosedLiftedPath,
      (cyc.integral (A.map (algebraMap ℝ ℂ))).re = 0

theorem isNormalizedThirdKind_iff_cutPeriods
    (S : C.CutSystem) (A : ℝ[X]) :
    C.IsNormalizedThirdKind A ↔
      A.natDegree ≤ g ∧ A.coeff g = 1 ∧
      (∀ j, (S.aPeriod (A.map (algebraMap ℝ ℂ)) j).re = 0) ∧
      (∀ j, (S.bPeriod (A.map (algebraMap ℝ ℂ)) j).re = 0)

theorem existsUnique_normalizedThirdKind :
    ∃! A : ℝ[X], C.IsNormalizedThirdKind A

def thirdKindNumerator : ℝ[X] :=
  Classical.choose C.existsUnique_normalizedThirdKind

theorem thirdKindNumerator_spec :
    C.IsNormalizedThirdKind C.thirdKindNumerator

theorem thirdKindNumerator_unique {A : ℝ[X]}
    (hA : C.IsNormalizedThirdKind A) :
    A = C.thirdKindNumerator

theorem natDegree_thirdKindNumerator_le :
    C.thirdKindNumerator.natDegree ≤ g

theorem coeff_thirdKindNumerator :
    C.thirdKindNumerator.coeff g = 1

theorem thirdKindPeriod_re (cyc : C.ClosedLiftedPath) :
    (cyc.integral
      (C.thirdKindNumerator.map (algebraMap ℝ ℂ))).re = 0

theorem thirdKindPeriod_conj (cyc : C.ClosedLiftedPath) :
    conj (cyc.integral
      (C.thirdKindNumerator.map (algebraMap ℝ ℂ))) =
      -(cyc.integral
        (C.thirdKindNumerator.map (algebraMap ℝ ℂ)))

def endpointNumerator : ℝ[X] := (X - Polynomial.C 1) ^ g

@[simp] theorem endpointNumerator_monic :
    C.endpointNumerator.Monic

@[simp] theorem natDegree_endpointNumerator :
    C.endpointNumerator.natDegree = g

theorem endpointNumerator_eq_thirdKind_iff
    (S : C.CutSystem) :
    C.endpointNumerator = C.thirdKindNumerator ↔
      (∀ j, (S.aPeriod
        (C.endpointNumerator.map (algebraMap ℝ ℂ)) j).re = 0) ∧
      (∀ j, (S.bPeriod
        (C.endpointNumerator.map (algebraMap ℝ ℂ)) j).re = 0)

def HasDegreeNPeriods (N : ℕ) : Prop :=
  ∀ cyc : C.ClosedLiftedPath,
    ∃ k : ℤ,
      (N : ℂ) * cyc.integral
        (C.thirdKindNumerator.map (algebraMap ℝ ℂ)) =
        2 * π * I * k

theorem hasDegreeNPeriods_iff_cutSystem
    (S : C.CutSystem) (N : ℕ) :
    C.HasDegreeNPeriods N ↔
      ∀ j : Fin (2 * g), ∃ k : ℤ,
        (N : ℂ) * S.periods
          (C.thirdKindNumerator.map (algebraMap ℝ ℂ)) j =
          2 * π * I * k

theorem hasDegreeNPeriods_mul {M N : ℕ}
    (hN : C.HasDegreeNPeriods N) :
    C.HasDegreeNPeriods (M * N)

end Curve

end JoseSmoothest.Hyperelliptic
```

## Detailed natural-language proof blueprint

### Residue normalization

The previous module computes the residues of `A(x)dx/y` at the two
infinities as minus and plus the leading degree-`g` coefficient.  Therefore
`deg A≤g` and `coeff A g=1` are exactly the residue conditions `-1,+1`.
No local analytic argument is repeated in this file.

### Reducing all periods to a cut basis

The cut system expresses the integral around every closed lifted path as an
integer combination of its `2g` standard periods.  A complex number is purely
imaginary exactly when its real part is zero, and integer combinations
preserve that condition.  This proves
`isNormalizedThirdKind_iff_cutPeriods` in both directions.

### Existence and uniqueness

Begin with the monic differential `x^g dx/y`.  Over the complex numbers,
every other differential with the same residues differs from it by a
holomorphic differential

```text
(c₀ + c₁x + ⋯ + c_{g-1}x^(g-1)) dx/y.
```

Thus the unknown correction has `g` complex coefficients, or `2g` real
unknowns.  Vanishing of the real parts of the `2g` periods is a square real
linear system.  `RiemannBilinear.realPeriodMap_bijective` gives existence and
uniqueness.  Only after solving that complex problem apply conjugation:
reality of `D` preserves the normalization conditions, so uniqueness fixes
the solution and proves that all numerator coefficients are real.

This is the analytically deepest proof in the module.  Rather than formalize
the general Riemann bilinear relations, prove the required positivity by
cutting the surface into its fundamental polygon, applying Stokes/Green to a
primitive on that polygon, and summing paired boundary edges.  The result is
a positive-definite `g×g` real Gram matrix.  This proof is reusable for the
period matrix later but does not require defining a Jacobian.

### Canonical choice

`thirdKindNumerator` is the unique polynomial selected by the preceding
theorem.  Its specification, degree, leading coefficient, and period facts
are direct projections.  A complex number of real part zero satisfies
`conj z=-z`, which gives `thirdKindPeriod_conj`.

### Endpoint numerator test

`(X-1)^g` is monic of degree `g`, so its differential already has the correct
residues.  By uniqueness it equals the distinguished numerator precisely when
all of its standard periods have zero real part.  This equivalence is the
finite system of transcendental equations imposed on the curve by the
endpoint-confluent smoothing problem.  It is not true for an arbitrary
hyperelliptic curve and must never be installed as a simp lemma or an
existence theorem.

### Quantized periods

The cut-system decomposition writes every closed period as an integer
combination of the `2g` basis periods plus an integer residue multiple of
`2πi`.  The normalized leading coefficient is one, so the residue term is
automatically quantized after multiplication by the natural number `N`.
This proves the finite-basis characterization.  Replacing `N` by `M*N`
multiplies every integer label by `M`.
