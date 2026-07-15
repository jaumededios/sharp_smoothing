# Blueprint for `JoseSmoothest/SpecialFunctions/HyperellipticCurve.lean`

## Purpose and scope

This module builds the specialized cut model of an even-degree real
hyperelliptic curve

```text
y² = D(x),       deg D = 2g+2.
```

It exposes affine points, the two points at infinity, the involution, lifted
paths, and integration of `A(x) dx/y`.  It does not develop arbitrary compact
Riemann surfaces, divisors, or sheaf cohomology.  The internal construction
may use charts and quotients, but downstream files see only the concrete API
below.

## Imports

```lean
import JoseSmoothest.SpecialFunctions.ComplexPathIntegral
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest.Hyperelliptic

open Polynomial Complex

structure Curve (g : ℕ) where
  D : ℝ[X]
  monic_D : D.Monic
  squarefree_D : Squarefree D
  natDegree_D : D.natDegree = 2 * g + 2

namespace Curve

variable {g : ℕ} (C : Curve g)

def complexPolynomial : ℂ[X] := C.D.map (algebraMap ℝ ℂ)

def AffinePoint :=
  {p : ℂ × ℂ // p.2 ^ 2 = C.complexPolynomial.eval p.1}

namespace AffinePoint

def x (p : C.AffinePoint) : ℂ := p.1.1

def y (p : C.AffinePoint) : ℂ := p.1.2

def involution (p : C.AffinePoint) : C.AffinePoint

@[simp] theorem x_involution (p : C.AffinePoint) :
    (p.involution).x = p.x

@[simp] theorem y_involution (p : C.AffinePoint) :
    (p.involution).y = -p.y

@[simp] theorem involution_involution (p : C.AffinePoint) :
    p.involution.involution = p

end AffinePoint

structure RealBranchPoint where
  x : ℝ
  isRoot : C.D.eval x = 0

def RealBranchPoint.affinePoint (e : C.RealBranchPoint) : C.AffinePoint :=
  ⟨(e.x, 0), by simp [e.isRoot, complexPolynomial]⟩

-- The implementation is the two-point compactification of `AffinePoint`.
def Point : Type

def affine : C.AffinePoint → C.Point

def infinityPlus : C.Point

def infinityMinus : C.Point

def involution : C.Point → C.Point

theorem involutive_involution : Function.Involutive C.involution

instance : TopologicalSpace C.Point
instance : T2Space C.Point
instance : CompactSpace C.Point

theorem infinityPlus_ne_infinityMinus :
    C.infinityPlus ≠ C.infinityMinus

@[simp] theorem involution_infinityPlus :
    C.involution C.infinityPlus = C.infinityMinus

@[simp] theorem involution_infinityMinus :
    C.involution C.infinityMinus = C.infinityPlus

@[simp] theorem involution_affine (p : C.AffinePoint) :
    C.involution (C.affine p) = C.affine p.involution

theorem affine_injective : Function.Injective C.affine

theorem point_eq_affine_or_infinity (p : C.Point) :
    (∃ q, p = C.affine q) ∨
      p = C.infinityPlus ∨ p = C.infinityMinus

structure LiftedPath (p q : C.AffinePoint) where
  xPath : Complex.PiecewiseC1Path p.x q.x
  y : ℝ → ℂ
  y_sq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    y t ^ 2 = C.complexPolynomial.eval (xPath t)
  y_zero : y 0 = p.y
  y_one : y 1 = q.y
  continuous_y : ContinuousOn y (Set.Icc (0 : ℝ) 1)
  y_ne_zero : ∀ t ∈ Set.Ioo (0 : ℝ) 1, y t ≠ 0

namespace LiftedPath

def involution {p q : C.AffinePoint}
    (γ : C.LiftedPath p q) :
    C.LiftedPath p.involution q.involution

def reverse {p q : C.AffinePoint}
    (γ : C.LiftedPath p q) : C.LiftedPath q p

def trans {p q r : C.AffinePoint}
    (γ : C.LiftedPath p q) (hq : q.y ≠ 0)
    (δ : C.LiftedPath q r) :
    C.LiftedPath p r

def integral {p q : C.AffinePoint}
    (γ : C.LiftedPath p q) (A : ℂ[X]) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    A.eval (γ.xPath t) / γ.y t * γ.xPath.velocity t

@[simp] theorem integral_involution {p q : C.AffinePoint}
    (γ : C.LiftedPath p q) (A : ℂ[X]) :
    γ.involution.integral A = -γ.integral A

theorem integral_reverse {p q : C.AffinePoint}
    (γ : C.LiftedPath p q) (A : ℂ[X]) :
    γ.reverse.integral A = -γ.integral A

theorem integral_trans {p q r : C.AffinePoint}
    (γ : C.LiftedPath p q) (hq : q.y ≠ 0)
    (δ : C.LiftedPath q r)
    (A : ℂ[X]) :
    (γ.trans hq δ).integral A = γ.integral A + δ.integral A

end LiftedPath

def ClosedLiftedPath := Σ p : C.AffinePoint, C.LiftedPath p p

namespace ClosedLiftedPath

def integral (cyc : C.ClosedLiftedPath) (A : ℂ[X]) : ℂ :=
  cyc.2.integral A

end ClosedLiftedPath

def PathsAvoidBranchPoints
    (cycles : Fin g → Σ p : C.AffinePoint, C.LiftedPath p p) : Prop

def CyclesFormSymplecticBasis
    (aCycle bCycle :
      Fin g → Σ p : C.AffinePoint, C.LiftedPath p p) : Prop

structure CutSystem where
  aCycle : Fin g → Σ p : C.AffinePoint, C.LiftedPath p p
  bCycle : Fin g → Σ p : C.AffinePoint, C.LiftedPath p p
  avoids_branchPoints_a : C.PathsAvoidBranchPoints aCycle
  avoids_branchPoints_b : C.PathsAvoidBranchPoints bCycle
  symplectic_basis : C.CyclesFormSymplecticBasis aCycle bCycle

namespace CutSystem

def aPeriod (S : C.CutSystem) (A : ℂ[X]) (j : Fin g) : ℂ :=
  (S.aCycle j).2.integral A

def bPeriod (S : C.CutSystem) (A : ℂ[X]) (j : Fin g) : ℂ :=
  (S.bCycle j).2.integral A

def periods (S : C.CutSystem) (A : ℂ[X]) : Fin (2 * g) → ℂ

theorem closedIntegral_eq_integerCombination
    (S : C.CutSystem) (A : ℂ[X])
    (hA : A.natDegree ≤ g)
    (cyc : C.ClosedLiftedPath) :
    ∃ (z : Fin (2 * g) → ℤ) (k : ℤ),
      cyc.integral A =
        ∑ j, (z j : ℂ) * S.periods A j +
          2 * π * I * (k : ℂ) * A.coeff g

end CutSystem

theorem exists_cutSystem : Nonempty C.CutSystem

def residueAtInfinityPlus (A : ℂ[X]) : ℂ

def residueAtInfinityMinus (A : ℂ[X]) : ℂ

theorem residueAtInfinityPlus {A : ℂ[X]}
    (hA : A.natDegree ≤ g) :
    C.residueAtInfinityPlus A =
      -A.coeff g

theorem residueAtInfinityMinus {A : ℂ[X]}
    (hA : A.natDegree ≤ g) :
    C.residueAtInfinityMinus A =
      A.coeff g

end Curve

end JoseSmoothest.Hyperelliptic
```

`Genus`, `ClosedLiftedPath`, and the residue definitions are implemented in
this module and exposed only through the displayed theorems.  The two `Prop`
fields in `CutSystem` abbreviate concrete intersection-number and coverage
conditions; their definitions must be public in Lean even though clients
should rarely unfold them.

## Detailed natural-language proof blueprint

### Affine curve and involution

An affine point is a pair `(x,y)` satisfying `y²=D(x)`.  Replacing `y` by
`-y` preserves the equation, fixes `x`, negates `y`, and is visibly an
involution.  These proofs are elementary ring normalization.

### Two-point compactification

Because `D` is monic of even degree `2g+2`, set `u=1/x` and
`v=y/x^(g+1)` near infinity.  The equation becomes

```text
v² = u^(2g+2) D(1/u),
```

whose right side tends to one.  It therefore has two local branches with
`v→1` and `v→-1`; these are `infinityPlus` and `infinityMinus`.  The
squarefree hypothesis makes every finite branch point nonsingular.  Use
`x-e` as a local coordinate away from branch points and `y` as a local
coordinate at a simple branch point.  These charts prove Hausdorffness and
compactness of the glued two-sheet cut model.  The involution exchanges the
two infinity charts.

Riemann--Hurwitz for the degree-two projection with `2g+2` simple branch
points gives genus `g`.  Since Mathlib lacks Riemann--Hurwitz for analytic
surfaces, this module must prove the specialized Euler-characteristic count
directly from the polygonal cut construction.

### Lifted paths and differential integrals

A lifted path records an `x`-path and a continuous choice of `y` satisfying
`y²=D(x)`.  This is exactly the data required to integrate
`A(x)dx/y`.  Applying the involution negates `y`, so it negates the integral.
Reversal and concatenation away from branch points reduce to their plane-path
analogues from `ComplexPathIntegral`.  The explicit `q.y≠0` hypothesis on
concatenation is necessary because the bundled path requires `y` to stay
nonzero at every interior parameter.  A branch point may be an endpoint, but
concatenating there would move it into the interior and is instead handled by
the removable-singularity limiting construction below.

Near a branch point both `dx` and `y` vanish to first order in the local
coordinate `y`; their quotient is regular.  Thus the apparent division by
zero in the parametrized formula is removable.  The implementation should
prove independence from a small detour and then define a path crossing a
branch point by a limit, rather than relying on Lean's totalized division.

### Cut system and periods

Pair the `2g+2` branch points by disjoint arcs, cut both copies of the sphere
along those arcs, and glue opposite banks.  Standard loops around `g` cuts
and between adjacent cuts give `aⱼ,bⱼ` cycles.  Polygon reduction shows that
every closed lifted path is homologous to an integer combination of these
`2g` cycles plus small loops around the two deleted infinity points and the
finite branch points.  The finite loops have zero integral because the
differential is regular there.  The infinity loops contribute integer
multiples of `2πi * coeff A g` by the residue calculation below.  Homotopy
invariance and additivity then give the stated
`closedIntegral_eq_integerCombination` without building general singular
homology.

### Residues at infinity

In the coordinate `u=1/x`, monicity gives

```text
y = ± u^(-g-1) (1 + O(u)).
```

If `A` has degree at most `g`, then

```text
A(x) dx/y = ∓ A_g du/u + a holomorphic term.
```

Reading off the coefficient of `du/u` yields residues `-A_g` on the plus
sheet and `A_g` on the minus sheet.  In particular, a monic degree-`g`
numerator produces residues `-1,+1`, the normalization required later.
