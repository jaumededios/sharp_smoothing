# Blueprint for `JoseSmoothest/SpecialFunctions/PellAbelPeriod.lean`

## Purpose

This module proves the Abel--Pell period criterion.  A degree-`N` polynomial
solution of

```text
P² - D Q² = 1
```

exists exactly when every period of the distinguished third-kind differential
belongs to `(2πi/N) · ℤ`.  It also recovers `P` as the cosine of an Abelian
integral and proves the derivative identity.  This is the central reusable
special-function theorem.

## Imports

```lean
import JoseSmoothest.SpecialFunctions.PellAbel
import JoseSmoothest.SpecialFunctions.MeromorphicDescent
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest.Hyperelliptic

open Polynomial Complex

namespace Curve

variable {g : ℕ} (C : Curve g)

theorem pellAbelSolution_of_periods {N : ℕ}
    (e : C.RealBranchPoint)
    (hN : 0 < N) (hper : C.HasDegreeNPeriods N) :
    ∃ s : Polynomial.PellAbelSolution C.D,
      s.P.leadingCoeff = s.Q.leadingCoeff ∧
      s.P.natDegree = N ∧
      s.Q.natDegree = N - g - 1 ∧
      derivative s.P =
        Polynomial.C (N : ℝ) * C.thirdKindNumerator * s.Q

theorem periods_of_pellAbelSolution {N : ℕ}
    (hN : 0 < N)
    (s : Polynomial.PellAbelSolution C.D)
    (hlead : s.P.leadingCoeff = s.Q.leadingCoeff)
    (hdeg : s.P.natDegree = N) :
    C.HasDegreeNPeriods N

theorem derivative_eq_thirdKind_of_pellAbelSolution {N : ℕ}
    (hN : 0 < N)
    (s : Polynomial.PellAbelSolution C.D)
    (hlead : s.P.leadingCoeff = s.Q.leadingCoeff)
    (hdeg : s.P.natDegree = N) :
    derivative s.P =
      Polynomial.C (N : ℝ) * C.thirdKindNumerator * s.Q

theorem pellAbelSolution_iff_periods
    (e : C.RealBranchPoint) {N : ℕ} (hN : 0 < N) :
    (∃ s : Polynomial.PellAbelSolution C.D,
      s.P.leadingCoeff = s.Q.leadingCoeff ∧
      s.P.natDegree = N) ↔
      C.HasDegreeNPeriods N

def recoveredSolution {N : ℕ}
    (e : C.RealBranchPoint)
    (hN : 0 < N) (hper : C.HasDegreeNPeriods N) :
    Polynomial.PellAbelSolution C.D :=
  Classical.choose (C.pellAbelSolution_of_periods e hN hper)

theorem recoveredSolution_leadingCoeff_eq {N : ℕ}
    (e : C.RealBranchPoint)
    (hN : 0 < N) (hper : C.HasDegreeNPeriods N) :
    (C.recoveredSolution e hN hper).P.leadingCoeff =
      (C.recoveredSolution e hN hper).Q.leadingCoeff

theorem natDegree_recoveredSolution_P {N : ℕ}
    (e : C.RealBranchPoint)
    (hN : 0 < N) (hper : C.HasDegreeNPeriods N) :
    (C.recoveredSolution e hN hper).P.natDegree = N

theorem recoveredSolution_derivative {N : ℕ}
    (e : C.RealBranchPoint)
    (hN : 0 < N) (hper : C.HasDegreeNPeriods N) :
    derivative (C.recoveredSolution e hN hper).P =
      Polynomial.C (N : ℝ) * C.thirdKindNumerator *
        (C.recoveredSolution e hN hper).Q

theorem recoveredSolution_P_eq_cos_integral {N : ℕ}
    (e : C.RealBranchPoint)
    (hN : 0 < N) (hper : C.HasDegreeNPeriods N)
    {p : C.AffinePoint}
    (γ : C.LiftedPath e.affinePoint p) :
    ((C.recoveredSolution e hN hper).P.map
      (algebraMap ℝ ℂ)).eval p.x =
      (C.recoveredSolution e hN hper).P.eval e.x *
      cos ((N : ℂ) * I *
        γ.integral
          (C.thirdKindNumerator.map (algebraMap ℝ ℂ)))

theorem recoveredSolution_Q_eq_sin_integral {N : ℕ}
    (e : C.RealBranchPoint)
    (hN : 0 < N) (hper : C.HasDegreeNPeriods N)
    {p : C.AffinePoint} (hp : p.y ≠ 0)
    (γ : C.LiftedPath e.affinePoint p) :
    ((C.recoveredSolution e hN hper).Q.map
      (algebraMap ℝ ℂ)).eval p.x =
      -(C.recoveredSolution e hN hper).P.eval e.x * I / p.y *
      sin ((N : ℂ) * I *
        γ.integral
          (C.thirdKindNumerator.map (algebraMap ℝ ℂ)))

end Curve

end JoseSmoothest.Hyperelliptic
```

The real base branch point `e` both proves descent from complex to real
coefficients and fixes the harmless simultaneous sign of `P,Q`.  The chosen
leading-coefficient orientation and the displayed cosine convention must be
tested against genus zero and the existing cubic Zolotarev sign convention
before this public surface is frozen.

## Detailed natural-language proof blueprint

### Checking periods on a basis

Every closed lifted path has period equal to an integer combination of the
cut-system periods plus an integer multiple of the small-loop residue
`2πi * coeff A g`.  For the normalized third-kind numerator that coefficient
is one.  Hence quantization of the `2g` basis periods implies quantization of
every period; the residue contribution is automatically quantized because
`N` is an integer.  The reverse implication is immediate by choosing the
basis cycles.  Multiplying the degree by `M` multiplies every integer period
label by `M`, proving `hasDegreeNPeriods_mul`.

### From periods to a meromorphic unit

Fix a base point and define locally

```text
F(p) = exp(N ∫ⁿ η).
```

Changing the path adds a closed period.  Under `HasDegreeNPeriods`, multiplying
that period by `N` gives `2πik`, so the exponential is unchanged.  Thus `F`
is single-valued.  The residues `-1,+1` imply

```text
div(F) = N(∞₋ - ∞₊)
```

with the sign dictated by the chosen infinity charts.  The involution negates
`η`; normalization at a branch point therefore gives
`F(ιp)=F(p)⁻¹`.

Set

```text
P = (F + F⁻¹)/2,
Q = (F - F⁻¹)/(2y).
```

The first expression is invariant under the involution.  The numerator in
the second is odd, as is `y`, so the quotient is invariant as well.  Both
therefore descend to rational functions of `x`.  They have no finite poles:
at a branch point the apparent singularity of `Q` is removable by oddness in
the local coordinate `y`.  Their growth at infinity is at most `N` and
`N-g-1`.  A rational function of `x` with no finite pole is a polynomial, so
`P,Q` have the claimed degrees.  The chosen infinity sheet makes their
leading coefficients equal.  Their common value is generally not one:
`D=X²-1` gives `P=T_N`, `Q=U_{N-1}`, whose leading coefficient is a power of
two.

Because `D` and the distinguished numerator are real and the exponential is
normalized at the real branch point `e`, complex conjugation fixes the
descended rational functions on the real structure.  Uniqueness of polynomial
coefficients therefore shows that `P,Q` lie in `ℝ[X]`.  Without such a real
base point the period theorem would only produce complex polynomials (for
example `D=X²+1`), so this hypothesis is essential rather than cosmetic.

Algebra gives `P²-DQ²=1`.  Differentiating `log F=Nη` and substituting the
two symmetric expressions yields

```text
P' = N A Q,
```

where `A=thirdKindNumerator`.

### From a Pell solution to periods

Given an oriented solution whose two leading coefficients agree, form the
meromorphic unit `F=P+yQ`.  The Pell identity
gives `F⁻¹=P-yQ`.  The degree calculation shows that `F` has divisor
`N(∞₋-∞₊)`.  Its logarithmic derivative divided by `N` has the
correct residues and purely imaginary periods, so uniqueness identifies it
with the distinguished differential `η`.

Analytic continuation of `log F` around a closed path changes it by an
integer multiple of `2πi`.  Hence `N∮η∈2πiℤ`, proving period
quantization.  Moreover

```text
(1/N) d log F = (P'/(NQ)) dx/y.
```

Equal leading coefficients give residues `-1,+1` at the two infinities,
and the logarithmic periods have zero real part.  Uniqueness of the
normalized third-kind differential identifies `P'/(NQ)` with
`thirdKindNumerator`.  Clearing the nonzero factors proves
`derivative_eq_thirdKind_of_pellAbelSolution`.  This public reverse-direction
identity is essential for curve extraction: it identifies the differential
belonging to the *supplied* minimizer solution, rather than a solution chosen
by classical choice.  The period result, derivative identity, reverse
implication, and `iff` all follow from the same logarithmic calculation.

### Cosine and sine recovery formulas

Normalize the exponential integral by its value at the base branch point.
There `y=0`, so `F(e)=P(e)=±1`; this supplies the explicit factor `P(e)` in
both formulas.  From `F/P(e)=exp(N∫η)` and its inverse, use the exponential
definitions of complex cosine and sine.  With the convention
`cos(i z)=(exp(-z)+exp(z))/2`, the symmetric part is exactly the displayed
cosine; the antisymmetric part divided by `y` gives the sine formula.  Period
quantization makes both right sides independent of the chosen lifted path.
