# Blueprint for `JoseSmoothest/EvenOrder/EndpointPhase.lean`

## Purpose

This module specializes the generic real Pell phase theorem to the
squarefree Pell factor extracted from an endpoint alternant.  It proves the
endpoint reciprocal-square-root integrability, the exact cosine
classification, and the exact winding

```text
N * phase(1) = (N - m + 1) * π.
```

The proof uses the already established derivative/root exhaustion.  It is a
direct classification of the supplied extremizer, not a forward construction
from Abelian periods.

## Imports

```lean
import JoseSmoothest.EvenOrder.PellExtraction
import JoseSmoothest.SpecialFunctions.RealPellPhase
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial Real Set MeasureTheory intervalIntegral

namespace EndpointAlternant

variable {m N : ℕ} {Z : ℝ[X]} (a : EndpointAlternant m N Z)

/-- The endpoint factors removed from the extracted squarefree Pell weight. -/
def phaseEndpointFactor (_a : EndpointAlternant m N Z) : ℝ[X] :=
  (X + C 1) * (X - C 1) ^ (m % 2)

/-- The factor of `D` which has no zero on `[-1,1]`. -/
def phaseCore : ℝ[X] :=
  a.D /ₘ a.phaseEndpointFactor

theorem phaseEndpointFactor_dvd :
    a.phaseEndpointFactor ∣ a.D

theorem endpoint_D_core_factorization :
    a.phaseEndpointFactor * a.phaseCore = a.D

theorem eval_phaseCore_ne_zero
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    a.phaseCore.eval x ≠ 0

theorem phaseCore_sign_odd (hm : Odd m)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 < a.phaseCore.eval x

theorem phaseCore_sign_even (hm : Even m)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    a.phaseCore.eval x < 0

/-- The orientation which makes `(X-1)^g` positive on the open interval. -/
def phaseOrientation (_a : EndpointAlternant m N Z) : ℝ :=
  (-1 : ℝ) ^ endpointGenus m

/-- The direct real phase data of the extracted Pell solution. -/
def realPhaseInterval : Polynomial.RealPellPhaseInterval
    a.D ((X - C 1) ^ endpointGenus m)

/-- The canonical real phase of the endpoint alternant. -/
def phase (x : ℝ) : ℝ :=
  a.realPhaseInterval.phase x

theorem phase_density_eq {x : ℝ} :
    a.realPhaseInterval.density x =
      (1 - x) ^ endpointGenus m / √(-a.D.eval x)

theorem continuousOn_phase :
    ContinuousOn a.phase (Set.Icc (-1 : ℝ) 1)

@[simp] theorem phase_neg_one : a.phase (-1) = 0

theorem phase_density_pos {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < a.realPhaseInterval.density x

theorem strictMonoOn_phase :
    StrictMonoOn a.phase (Set.Icc (-1 : ℝ) 1)

theorem eval_eq_cos_phase {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Z.eval x =
      a.orientation * Real.cos ((N : ℝ) * a.phase x)

theorem companion_eq_sin_phase {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    √(-a.D.eval x) * a.Q.eval x =
      -a.phaseOrientation * a.orientation *
        Real.sin ((N : ℝ) * a.phase x)

theorem phase_node (j : Fin (N - m + 2)) :
    (N : ℝ) * a.phase (a.nodes j) = (j : ℕ) * Real.pi

theorem phaseLength :
    (N : ℝ) * a.phase 1 = ((N - m + 1 : ℕ) : ℝ) * Real.pi

end EndpointAlternant

end JoseSmoothest
```

## Detailed natural-language proof blueprint

### Removing the endpoint singularities

The extraction theorem gives a monic squarefree polynomial `D`, a simple
root at `-1`, root multiplicity `m % 2` at `1`, and no root in the open
interval.  The two endpoint factors are coprime, so their product divides
`D`.  Exact division defines `phaseCore`, and the factorization follows by
cancellation.  If the core vanished anywhere in `[-1,1]`, the corresponding
root multiplicity of `D` would exceed the already known endpoint
multiplicity or would give an interior root, contradiction.

Write `g=endpointGenus m` and `ε=m%2`.  On the open interval the sign
`D<0` determines the sign of the nonvanishing core, and continuity extends
it to the endpoints:

- if `m` is odd, `ε=1` and
  `-D(x)=(1-x²) phaseCore(x)`, so the core is positive;
- if `m` is even, `ε=0` and
  `-D(x)=(1+x)(-phaseCore(x))`, so the core is negative.

### Endpoint integrability

The density orientation is `(-1)^g`, hence
`orientation*(x-1)^g=(1-x)^g` on the open interval.  In the odd case rewrite
the density as a continuous multiplier of Mathlib's Chebyshev weight; in the
even case use the translated power weight at the only branch endpoint:

```text
odd m:  [(1-x)^g / sqrt(phaseCore(x))] / sqrt(1-x²),
even m: [(1-x)^g / sqrt(-phaseCore(x))] / sqrt(x+1).
```

The bracketed functions extend continuously to `[-1,1]`, since the core has
constant strict sign there.  Mathlib proves interval integrability of the
Chebyshev weight and of `x ↦ x^r` for `r>-1`; translation gives the even
weight `1/sqrt(x+1)`.  Multiplication by a continuous function preserves
interval integrability.  Endpoint discrepancies are harmless in the
interval-integrability congruence.  These facts populate
`realPhaseInterval`.

The generic phase theorem now supplies continuity, strict monotonicity, and
the cosine/sine formulae.  The left polynomial value is the alternant's
orientation by `node_zero` and `node_value`.

### Exact winding between alternating nodes

Put `K=N-m+1`; the endpoint alternant has `K+1` ordered nodes.  At node `j`,
`Z=±1`.  The Pell equation and `D<0` in the interior show that the real
companion is zero; the endpoint cases are immediate from `D=0` or the known
endpoint value.  The sine formula therefore says

```text
sin(N phase(node j)) = 0.
```

Thus the angle is `k_j π` for an integer `k_j`.  At the left endpoint the
angle is zero, so `k_0=0`.  Since `phase` is strictly increasing and `N>0`,
the integers `k_j` are strictly increasing.

They cannot skip an integer.  If `k_{j+1}≥k_j+2`, continuity and strict
monotonicity give a point strictly between consecutive nodes whose angle is
`(k_j+1)π`.  The sine formula makes the companion zero there.  Since
`D<0`, this forces `Q=0`.  But the explicit formula for `Q` has precisely the
interior alternation nodes as its roots; strict ordering shows there is no
root between consecutive nodes.  This contradiction proves
`k_{j+1}=k_j+1`, hence `k_j=j`.  The last node is `1`, giving the exact phase
length `(N-m+1)π`.
