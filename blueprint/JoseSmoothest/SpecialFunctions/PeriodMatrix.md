# Blueprint for `JoseSmoothest/SpecialFunctions/PeriodMatrix.lean`

## Purpose and priority

This optional bridge constructs the normalized period matrix of the
hyperelliptic cut model and packages the Siegel upper half-space condition.
Neither the abstract Pell--Abel criterion nor the real-phase proof needs a
period matrix.  It becomes necessary only when a recovered curve is evaluated
through genus-`g` Riemann theta functions.

## Imports

```lean
import JoseSmoothest.SpecialFunctions.RiemannBilinear
import Mathlib.LinearAlgebra.Matrix.PosDef
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Complex Matrix Polynomial
open scoped ComplexConjugate

structure SiegelUpperHalfSpace (g : ℕ) where
  periodMatrix : Matrix (Fin g) (Fin g) ℂ
  symmetric : periodMatrix.transpose = periodMatrix
  im_posDef : Matrix.PosDef (periodMatrix.map Complex.im)

namespace SiegelUpperHalfSpace

variable {g : ℕ}

def conjugateNeg (S : SiegelUpperHalfSpace g) :
    SiegelUpperHalfSpace g

@[simp] theorem periodMatrix_conjugateNeg
    (S : SiegelUpperHalfSpace g) :
    S.conjugateNeg.periodMatrix = -S.periodMatrix.map conj

end SiegelUpperHalfSpace

namespace Hyperelliptic.Curve

variable {g : ℕ} (C : Hyperelliptic.Curve g)

def holomorphicNumerator (j : Fin g) : ℂ[X] := X ^ (j : ℕ)

def aPeriodMatrix (S : C.CutSystem) : Matrix (Fin g) (Fin g) ℂ :=
  fun i j ↦ S.aPeriod (C.holomorphicNumerator i) j

def bPeriodMatrix (S : C.CutSystem) : Matrix (Fin g) (Fin g) ℂ :=
  fun i j ↦ S.bPeriod (C.holomorphicNumerator i) j

theorem isUnit_det_aPeriodMatrix (S : C.CutSystem) :
    IsUnit (C.aPeriodMatrix S).det

def normalizedPeriodMatrix (S : C.CutSystem) :
    Matrix (Fin g) (Fin g) ℂ :=
  (C.aPeriodMatrix S)⁻¹ * C.bPeriodMatrix S

theorem normalizedPeriodMatrix_symmetric (S : C.CutSystem) :
    (C.normalizedPeriodMatrix S).transpose =
      C.normalizedPeriodMatrix S

theorem normalizedPeriodMatrix_im_posDef (S : C.CutSystem) :
    Matrix.PosDef ((C.normalizedPeriodMatrix S).map Complex.im)

def siegelPeriodMatrix (S : C.CutSystem) :
    SiegelUpperHalfSpace g where
  periodMatrix := C.normalizedPeriodMatrix S
  symmetric := C.normalizedPeriodMatrix_symmetric S
  im_posDef := C.normalizedPeriodMatrix_im_posDef S

end Hyperelliptic.Curve

end JoseSmoothest
```

## Detailed natural-language proof blueprint

The differentials `x^j dx/y`, `0≤j<g`, form the standard holomorphic basis:
the local branch coordinate removes the apparent finite singularities, and
the degree bound makes them regular at both infinities.  If a linear
combination has all `a`-periods zero, the specialized Riemann bilinear energy
identity forces it to vanish.  Therefore the `a`-period matrix is invertible.

Multiplying the differential basis by its inverse `a`-period matrix produces
a normalized basis with identity `a`-periods.  The first Riemann bilinear
relation makes its `b`-period matrix symmetric; the second identifies the
quadratic form of its imaginary part with the positive `L²` energy of a
nonzero holomorphic differential.  Hence the imaginary part is positive
definite and the matrix lies in Siegel upper half-space.

The proof should reuse the polygonal energy calculation already needed for
existence of the distinguished third-kind differential.  This module should
not independently formalize general homology, wedge products, or the full
Riemann bilinear theorem.
