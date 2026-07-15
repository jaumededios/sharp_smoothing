# Blueprint for `JoseSmoothest/SpecialFunctions/MeromorphicDescent.lean`

## Purpose

The period criterion needs more than path integration: it constructs a
meromorphic unit on the compact two-sheeted curve, controls its orders at the
two infinities, and descends invariant/anti-invariant combinations to
polynomials in `x`.  Mathlib has no compact-curve meromorphic API that can do
this.  This module supplies precisely that specialized layer.

## Imports

```lean
import JoseSmoothest.SpecialFunctions.ThirdKindDifferential
import Mathlib.Analysis.Meromorphic.Order
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest.Hyperelliptic

open Complex Polynomial

namespace Curve

variable {g : ℕ} (C : Curve g)

def MeromorphicFunction : Type

def MeromorphicDifferential : Type

def pullbackX (R : RatFunc ℂ) : C.MeromorphicFunction

def pullbackPolynomial (P : ℂ[X]) : C.MeromorphicFunction

def yFunction : C.MeromorphicFunction

def IsLocallyDivisibleByY (f : C.MeromorphicFunction) : Prop

def logarithmicDerivative
    (f : C.MeromorphicFunction) : C.MeromorphicDifferential

def thirdKindDifferential : C.MeromorphicDifferential

namespace MeromorphicFunction

instance : CommField C.MeromorphicFunction

def evalAffine (f : C.MeromorphicFunction) (p : C.AffinePoint) : WithTop ℂ

def compInvolution (f : C.MeromorphicFunction) : C.MeromorphicFunction

def orderAtInfinityPlus (f : C.MeromorphicFunction) : ℤ

def orderAtInfinityMinus (f : C.MeromorphicFunction) : ℤ

def HasNoFinitePoles (f : C.MeromorphicFunction) : Prop

def IsInvariant (f : C.MeromorphicFunction) : Prop :=
  f.compInvolution = f

def IsAntiInvariant (f : C.MeromorphicFunction) : Prop :=
  f.compInvolution = -f

theorem invariant_eq_rationalInX {f : C.MeromorphicFunction}
    (hf : f.IsInvariant) :
    ∃ R : RatFunc ℂ, f = C.pullbackX R

theorem invariant_noFinitePoles_eq_polynomial
    {f : C.MeromorphicFunction} (hinv : f.IsInvariant)
    (hfinite : f.HasNoFinitePoles) :
    ∃ P : ℂ[X], f = C.pullbackPolynomial P

theorem antiInvariant_div_y_noFinitePoles_eq_polynomial
    {f : C.MeromorphicFunction} (hanti : f.IsAntiInvariant)
    (hbranch : C.IsLocallyDivisibleByY f)
    (hfinite : (f / C.yFunction).HasNoFinitePoles) :
    ∃ Q : ℂ[X], f / C.yFunction = C.pullbackPolynomial Q

end MeromorphicFunction

def ExponentialIntegralUnit (N : ℕ) : Type

namespace ExponentialIntegralUnit

def toMeromorphicFunction {N : ℕ}
    (F : C.ExponentialIntegralUnit N) : C.MeromorphicFunction

theorem exists_of_periods {N : ℕ} (hN : 0 < N)
    (hper : C.HasDegreeNPeriods N) :
    Nonempty (C.ExponentialIntegralUnit N)

theorem orderAtInfinityPlus {N : ℕ}
    (F : C.ExponentialIntegralUnit N) :
    F.toMeromorphicFunction.orderAtInfinityPlus = -N

theorem orderAtInfinityMinus {N : ℕ}
    (F : C.ExponentialIntegralUnit N) :
    F.toMeromorphicFunction.orderAtInfinityMinus = N

theorem involution {N : ℕ} (F : C.ExponentialIntegralUnit N) :
    F.toMeromorphicFunction.compInvolution =
      F.toMeromorphicFunction⁻¹

theorem logarithmicDerivative {N : ℕ}
    (F : C.ExponentialIntegralUnit N) :
    C.logarithmicDerivative F.toMeromorphicFunction =
      N • C.thirdKindDifferential

end ExponentialIntegralUnit

end Curve

end JoseSmoothest.Hyperelliptic
```

`MeromorphicDifferential` is the chartwise one-form type defined alongside
`MeromorphicFunction`.  No general compact-curve divisor API is being
promised.

## Detailed natural-language proof blueprint

Represent a meromorphic function by compatible meromorphic expressions in
the explicit affine, branch, and infinity charts from `HyperellipticCurve`.
Local meromorphic orders are Mathlib's plane orders transported through those
charts.  Field operations and the involution act chartwise.

An invariant meromorphic function belongs to the fixed field of the quadratic
extension `ℂ(x,y)/ℂ(x)`, hence is rational in `x`.  Prove this concretely by
writing a chart expression as `R(x)+yS(x)` and comparing it with its
involute.  No finite poles means the denominator of `R` is constant, so `R`
is a polynomial.  For an anti-invariant function, the invariant quotient by
`y` is meromorphic precisely when the numerator vanishes in the branch local
coordinate; this proves the companion descent theorem.

Under period quantization, exponentiating `N` times a local primitive of the
third-kind differential gives compatible chart functions: transition
constants are exponentials of `2πik` and hence one.  The residue calculation
gives orders `-N,+N` at infinity.  Oddness of the differential under the
hyperelliptic involution gives `F∘ι=F⁻¹` after normalization at a branch
point.  Differentiating the exponential proves the logarithmic-derivative
identity.
