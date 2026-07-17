# Blueprint for `JoseSmoothest/SpecialFunctions/RiemannBilinear.lean`

## Purpose

This core module proves the one specialized Riemann-bilinear/energy identity
needed twice later: to normalize the third-kind differential and to prove
that a normalized hyperelliptic period matrix lies in Siegel upper
half-space.  Isolating it prevents two independent, sign-sensitive polygon
arguments.

## Imports

```lean
import JoseSmoothest.SpecialFunctions.HyperellipticCurve
import Mathlib.LinearAlgebra.Matrix.PosDef
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest.Hyperelliptic

open Complex Matrix Polynomial

namespace Curve

variable {g : ℕ} (C : Curve g)

def IsHolomorphicNumerator (A : ℂ[X]) : Prop := A.natDegree < g

def differentialEnergy (A : ℂ[X]) : ℝ

def periodEnergy (S : C.CutSystem) (A : ℂ[X]) : ℝ

def realPeriodMap (S : C.CutSystem) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin (2 * g) → ℝ)

theorem differentialEnergy_nonneg (A : ℂ[X]) :
    0 ≤ C.differentialEnergy A

theorem differentialEnergy_eq_zero_iff {A : ℂ[X]}
    (hA : C.IsHolomorphicNumerator A) :
    C.differentialEnergy A = 0 ↔ A = 0

theorem riemann_bilinear_energy
    (S : C.CutSystem) {A : ℂ[X]}
    (hA : C.IsHolomorphicNumerator A) :
    C.differentialEnergy A =
      C.periodEnergy S A

theorem holomorphic_eq_zero_of_aPeriods_eq_zero
    (S : C.CutSystem) {A : ℂ[X]}
    (hA : C.IsHolomorphicNumerator A)
    (ha : ∀ j, S.aPeriod A j = 0) :
    A = 0

theorem realPeriodMap_bijective (S : C.CutSystem) :
    Function.Bijective (C.realPeriodMap S)

end Curve

end JoseSmoothest.Hyperelliptic
```

`periodEnergy` is the explicit Hermitian pairing of the `a`- and `b`-period
vectors.  `realPeriodMap` sends the real and imaginary parts of the `g`
holomorphic coefficients to the real parts of all `2g` periods.  Both
definitions are public because downstream normalization proofs use their
linearity, but their coordinate formulas live in this module only.

## Detailed natural-language proof blueprint

Cut the compact curve along the symplectic cycles to obtain a polygon on
which the holomorphic differential has a single-valued primitive.  Apply
Stokes/Green to the squared norm of that primitive.  Paired boundary edges
cancel after translating by their periods; the uncancelled terms are exactly
the Hermitian `periodEnergy`.  The surface integral is the nonnegative
`L²` energy of `A(x)dx/y`.

Zero energy makes the differential zero pointwise.  Since `dx/y` is not the
zero differential, polynomial identity on a nonempty chart gives `A=0`.
This proves injectivity of the `a`-period map and, after applying the same
identity to the real-part normalization system, injectivity of
`realPeriodMap`.  Domain and codomain both have real dimension `2g`, so it is
bijective.

The signs of the symplectic intersection form are fixed in
`CutSystem.CyclesFormSymplecticBasis`.  Reversing a `b`-cycle without also
changing this orientation is therefore rejected, which is essential for
positive rather than negative definite imaginary period matrices.
