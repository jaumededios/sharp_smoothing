# Blueprint for `JoseSmoothest/SpecialFunctions/RealPellPhase.lean`

## Purpose

This module proves the real-variable phase theorem needed for the direct
classification of a supplied polynomial Pell--Abel solution.  It deliberately
does not construct a solution from periods: the caller supplies

```text
P² - D Q² = 1,              P' = N A Q,
```

together with the sign and integrability data on a real interval.  The result
is a strictly increasing phase and exact cosine/sine formulae for `P` and
`sqrt(-D) Q`.  The proof is elementary one-variable calculus and is reusable
outside the smoothing problem.

## Imports

```lean
import JoseSmoothest.SpecialFunctions.PellAbel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
```

## Public declarations

```lean
noncomputable section

namespace Polynomial

open Real Set MeasureTheory intervalIntegral

/-- Sign, positivity, and endpoint-integrability data for a real branch of a
polynomial Pell equation. -/
structure RealPellPhaseInterval (D A : ℝ[X]) where
  /-- The left endpoint, which is a branch point of `D`. -/
  left : ℝ
  /-- The right endpoint of the real phase interval. -/
  right : ℝ
  left_lt_right : left < right
  eval_D_left : D.eval left = 0
  neg_D : ∀ x ∈ Set.Ioo left right, D.eval x < 0
  /-- The sign which makes the differential numerator positive. -/
  orientation : ℝ
  orientation_sq : orientation ^ 2 = 1
  numerator_pos :
    ∀ x ∈ Set.Ioo left right, 0 < orientation * A.eval x
  density_intervalIntegrable :
    IntervalIntegrable
      (fun x ↦ orientation * A.eval x / √(-D.eval x))
      volume left right

namespace RealPellPhaseInterval

variable {D A : ℝ[X]} (I : RealPellPhaseInterval D A)

/-- The positive real phase density on the open interval. -/
def density (x : ℝ) : ℝ :=
  I.orientation * A.eval x / √(-D.eval x)

/-- The phase, anchored to be zero at the left endpoint. -/
def phase (x : ℝ) : ℝ :=
  ∫ t in I.left..x, I.density t

/-- The real companion coordinate on the cut. -/
def companion (s : PellAbelSolution D) (x : ℝ) : ℝ :=
  √(-D.eval x) * s.Q.eval x

theorem orientation_ne_zero : I.orientation ≠ 0

theorem orientation_eq_one_or_neg_one :
    I.orientation = 1 ∨ I.orientation = -1

theorem continuousOn_phase :
    ContinuousOn I.phase (Set.Icc I.left I.right)

@[simp] theorem phase_left : I.phase I.left = 0

theorem hasDerivAt_phase {x : ℝ}
    (hx : x ∈ Set.Ioo I.left I.right) :
    HasDerivAt I.phase (I.density x) x

theorem density_pos {x : ℝ}
    (hx : x ∈ Set.Ioo I.left I.right) :
    0 < I.density x

theorem strictMonoOn_phase :
    StrictMonoOn I.phase (Set.Icc I.left I.right)

theorem phaseSign_sq (s : PellAbelSolution D) :
    (s.P.eval I.left) ^ 2 = 1

theorem phaseSign_eq_one_or_neg_one (s : PellAbelSolution D) :
    s.P.eval I.left = 1 ∨ s.P.eval I.left = -1

theorem pell_eval_eq_cos_phase
    {N : ℕ} (s : PellAbelSolution D)
    (hQ : s.Q ≠ 0)
    (hderiv : derivative s.P = C (N : ℝ) * A * s.Q)
    {x : ℝ} (hx : x ∈ Set.Icc I.left I.right) :
    s.P.eval x =
      s.P.eval I.left * Real.cos ((N : ℝ) * I.phase x)

theorem pell_companion_eq_sin_phase
    {N : ℕ} (s : PellAbelSolution D)
    (hQ : s.Q ≠ 0)
    (hderiv : derivative s.P = C (N : ℝ) * A * s.Q)
    {x : ℝ} (hx : x ∈ Set.Icc I.left I.right) :
    I.companion s x =
      -I.orientation * s.P.eval I.left *
        Real.sin ((N : ℝ) * I.phase x)

end RealPellPhaseInterval

end Polynomial
```

The generic theorem does not need to carry a separate `0 < N` hypothesis.
The endpoint specialization has `0 < N` because `1 ≤ m ≤ N`; with a
nonempty negative-`D` interval and `Q ≠ 0`, the remaining hypotheses in fact
exclude the degenerate `N = 0` case.

## Detailed natural-language proof blueprint

### Phase calculus

The density is interval-integrable by a structure field.  The standard
continuity theorem for indefinite interval integrals therefore makes `phase`
continuous on the closed interval, and the integral over a degenerate
interval gives `phase left = 0`.  At an interior point, `D(x)<0`, so
`sqrt(-D(x))` is nonzero.  Polynomial evaluation, negation, square root on the
positive reals, multiplication, and division show that the density is
continuous there.  The fundamental theorem of calculus gives
`phase' = density`.

The numerator is positive by assumption and the square-root denominator is
positive because `D<0`; hence `density>0`.  Apply the mean-value theorem to
the phase on every closed subinterval `[x,y]` contained in the open interval.
For endpoints, approximate from the interior and use continuity.  This proves
strict monotonicity on the entire closed interval.

The equation evaluated at the left endpoint has `D(left)=0`, so
`P(left)^2=1`.  Over the reals this is equivalent to `P(left)=1` or `-1`.

### Polynomial cancellation and the rotation system

Differentiate `P²-DQ²=1` as a polynomial identity and substitute
`P'=N A Q`.  The resulting identity is

```text
Q * (2 N A P - D' Q - 2 D Q') = 0.
```

Since `Q≠0` and `ℝ[X]` is an integral domain, cancel `Q`.  On the open
interval put

```text
R(x) = sqrt(-D(x)) Q(x),
ρ(x) = orientation A(x) / sqrt(-D(x)).
```

The chain rule for `sqrt`, the cancelled polynomial identity, and
`orientation²=1` give

```text
P' = orientation * N * ρ * R,
R' = -orientation * N * ρ * P.
```

This avoids dividing by `Q(x)`, so zeros of `Q` cause no analytic problem.

### Conserved quantities and endpoint extension

Let `θ=N phase`.  Differentiate

```text
F = P cos θ - orientation R sin θ,
G = P sin θ + orientation R cos θ.
```

The rotation system and `θ'=Nρ` make both derivatives zero on the open
interval.  Each function is continuous on the closed interval: polynomial
evaluation, real square root, multiplication, and the phase are continuous.
The zero-derivative
constancy theorem on compact subintervals, followed by endpoint continuity,
shows that `F` and `G` are constant on the whole interval.

At the left endpoint, `phase=0` and `R=0`, so `F=P(left)` and `G=0`.
Solving the two rotation equations gives

```text
P(x) = P(left) cos(N phase(x)),
R(x) = -orientation P(left) sin(N phase(x)).
```

No complex logarithm, argument branch, or period theory is used.
