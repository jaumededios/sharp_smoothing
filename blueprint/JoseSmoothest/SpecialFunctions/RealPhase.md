# Blueprint for `JoseSmoothest/SpecialFunctions/RealPhase.lean`

## Purpose

The complex period criterion produces polynomials, but the extremal theorem
also needs a real statement: on a distinguished interval the recovered
polynomial is a cosine of a strictly monotone real phase.  This module turns
the sign of `D` and the phase length into bounds and ordered alternating
nodes.  It contains no smoothing-specific weighted norm.

## Imports

```lean
import JoseSmoothest.SpecialFunctions.PellAbelPeriod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest.Hyperelliptic

open Polynomial Real

namespace Curve

variable {g : ℕ} (C : Curve g)

structure RealPhaseInterval (A : ℝ[X]) where
  left : ℝ
  right : ℝ
  left_lt_right : left < right
  eval_D_left : C.D.eval left = 0
  nonpos_D : ∀ x ∈ Set.Icc left right, C.D.eval x ≤ 0
  neg_D : ∀ x ∈ Set.Ioo left right, C.D.eval x < 0
  orientation : ℝ
  orientation_eq : orientation = 1 ∨ orientation = -1
  numerator_positive :
    ∀ x ∈ Set.Ioo left right, 0 < orientation * A.eval x

namespace RealPhaseInterval

variable {C : Curve g} {A : ℝ[X]} (I : C.RealPhaseInterval A)

def density (x : ℝ) : ℝ :=
  I.orientation * A.eval x / √(-C.D.eval x)

def phase (x : ℝ) : ℝ :=
  ∫ t in I.left..x, I.density t

theorem intervalIntegrable_density :
    IntervalIntegrable I.density volume I.left I.right

theorem continuous_phase : ContinuousOn I.phase (Set.Icc I.left I.right)

theorem phase_left : I.phase I.left = 0

theorem hasDerivAt_phase {x : ℝ} (hx : x ∈ Set.Ioo I.left I.right) :
    HasDerivAt I.phase (I.density x) x

theorem density_pos {x : ℝ} (hx : x ∈ Set.Ioo I.left I.right) :
    0 < I.density x

theorem strictMonoOn_phase :
    StrictMonoOn I.phase (Set.Icc I.left I.right)

def leftBranchPoint : C.RealBranchPoint where
  x := I.left
  isRoot := I.eval_D_left

def solution (N : ℕ) (hN : 0 < N)
    (hper : C.HasDegreeNPeriods N) :
    Polynomial.PellAbelSolution C.D :=
  C.recoveredSolution I.leftBranchPoint hN hper

def phaseSign (N : ℕ) (hN : 0 < N)
    (hper : C.HasDegreeNPeriods N) : ℝ :=
  (I.solution N hN hper).P.eval I.left

theorem phaseSign_eq_one_or_neg_one (N : ℕ) (hN : 0 < N)
    (hper : C.HasDegreeNPeriods N) :
    I.phaseSign N hN hper = 1 ∨ I.phaseSign N hN hper = -1

def HasLength (N K : ℕ) : Prop :=
  (N : ℝ) * I.phase I.right = K * π

def node (N K : ℕ) (hN : 0 < N)
    (hK : I.HasLength N K) (j : Fin (K + 1)) : ℝ :=
  Classical.choose (I.exists_unique_phase_value hN hK j)

theorem node_mem_Icc (N K : ℕ) (hN : 0 < N)
    (hK : I.HasLength N K) (j : Fin (K + 1)) :
    I.node N K hN hK j ∈ Set.Icc I.left I.right

theorem phase_node (N K : ℕ) (hN : 0 < N)
    (hK : I.HasLength N K) (j : Fin (K + 1)) :
    (N : ℝ) * I.phase (I.node N K hN hK j) = (j : ℕ) * π

theorem strictMono_node (N K : ℕ) (hN : 0 < N)
    (hK : I.HasLength N K) :
    StrictMono (I.node N K hN hK)

theorem node_zero (N K : ℕ) (hN : 0 < N)
    (hK : I.HasLength N K) :
    I.node N K hN hK 0 = I.left

theorem node_last (N K : ℕ) (hN : 0 < N)
    (hK : I.HasLength N K) :
    I.node N K hN hK (Fin.last K) = I.right

theorem pellAbelSolution_eval_eq_cos_phase
    {N : ℕ} (hN : 0 < N)
    (s : Polynomial.PellAbelSolution C.D)
    (hQ0 : s.Q ≠ 0)
    (hderiv : derivative s.P =
      Polynomial.C (N : ℝ) * A * s.Q)
    {x : ℝ} (hx : x ∈ Set.Icc I.left I.right) :
    s.P.eval x =
      s.P.eval I.left * Real.cos ((N : ℝ) * I.phase x)

theorem abs_pellAbelSolution_eval_le_one
    (s : Polynomial.PellAbelSolution C.D)
    {x : ℝ} (hx : x ∈ Set.Icc I.left I.right) :
    |s.P.eval x| ≤ 1

theorem recoveredSolution_eval_eq_cos_phase
    {N : ℕ} (hN : 0 < N) (hper : C.HasDegreeNPeriods N)
    (hA : A = C.thirdKindNumerator) {x : ℝ}
    (hx : x ∈ Set.Icc I.left I.right) :
    (I.solution N hN hper).P.eval x =
      I.phaseSign N hN hper *
        Real.cos ((N : ℝ) * I.phase x)

theorem abs_recoveredSolution_eval_le_one
    {N : ℕ} (hN : 0 < N) (hper : C.HasDegreeNPeriods N)
    (hA : A = C.thirdKindNumerator) {x : ℝ}
    (hx : x ∈ Set.Icc I.left I.right) :
    |(I.solution N hN hper).P.eval x| ≤ 1

theorem recoveredSolution_eval_node
    {N K : ℕ} (hN : 0 < N) (hper : C.HasDegreeNPeriods N)
    (hA : A = C.thirdKindNumerator) (hK : I.HasLength N K)
    (j : Fin (K + 1)) :
    (I.solution N hN hper).P.eval (I.node N K hN hK j) =
      I.phaseSign N hN hper * (-1 : ℝ) ^ (j : ℕ)

end RealPhaseInterval

end Curve

end JoseSmoothest.Hyperelliptic
```

The factor `phaseSign` is the recovered polynomial's value at the left branch
point and is always `±1`.  It is not the density orientation: the genus-zero
Chebyshev test has positive density but left value `(-1)^N`.

## Detailed natural-language proof blueprint

### Integrability at branch endpoints

Inside the open interval, `D<0`, so the square root in the denominator is
strictly positive and the density is continuous.  At a simple zero of the
squarefree polynomial `D`, the denominator behaves like a nonzero constant
times `√|x-a|`; its reciprocal is locally integrable.  At an endpoint where
`D` does not vanish, continuity is immediate.  Factor `D` by `(X-C a)` at
each branch endpoint, bound the remaining factor above and below on a small
compact interval, and compare with the standard integrable function
`t ↦ 1/√t`.  This proves `intervalIntegrable_density` without assigning
mathematical meaning to totalized division at the endpoint itself.

### Continuity, derivative, and monotonicity

The indefinite interval integral of an interval-integrable function is
continuous.  At every interior point the density is continuous, so the
fundamental theorem gives its derivative.  The orientation assumption makes
the numerator positive and `D<0` makes the denominator positive; hence the
derivative is strictly positive.  The mean-value theorem, or positivity of
the integral over each nontrivial subinterval, proves strict monotonicity on
the closed interval.

### Phase nodes

Assume `N phase(right)=Kπ`.  For `j=0,…,K`, the target `jπ/N` lies between
the phase values at the two endpoints.  Continuity gives a preimage and strict
monotonicity makes it unique.  Choosing that point defines `node`.  Comparing
target phase values proves strict ordering.  Targets zero and `Kπ/N`
identify the first and last nodes with the interval endpoints.

### Real cosine representation for a supplied solution

The primary theorem accepts the actual Pell solution used by its caller and
requires `Q≠0`.  This hypothesis is essential: the unit solution has
`P=1,Q=0` and satisfies the derivative identity vacuously, but cannot follow
a nonconstant phase.  Curve extraction obtains `Q≠0` from its nonzero
leading coefficient; a recovered positive-degree solution obtains it from
its degree and leading-coefficient orientation.
On the upper bank of the cut take

```text
y = i √(-D(x)).
```

Then, for `F=P+yQ`, logarithmic differentiation of the Pell identity and the
assumed derivative formula give

```text
d log F = N A(x) dx/y
          = -i N A(x) dx/√(-D(x)).
```

up to the chosen orientation sign.  Solve this first-order complex ODE on
the open interval and extend to the endpoints by continuity.  At the left
branch point `y=0`, so `F(left)=P(left)` and the Pell identity gives
`P(left)²=1`.  Taking the symmetric part of
`F(x)=P(left) exp(±iN phase(x))` proves the displayed cosine formula;
cosine is even, so the orientation sign disappears.

The elementary interval bound also follows directly from
`P²=1+DQ²` and `D≤0`, without periods or the derivative formula.
Applying the supplied-solution cosine theorem to `recoveredSolution` and its
known derivative identity gives the older recovery theorem as a corollary.
At a phase node the angle is `jπ`, so cosine is `(-1)^j`, proving exact
equioscillation.
