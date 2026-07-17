# Blueprint for `JoseSmoothest/EvenOrder/CurveExtraction.lean`

## Purpose

This analytic continuation of `PellExtraction` equips the extracted
squarefree polynomial with its hyperelliptic curve, identifies the retained
solution's differential and periods, proves the exact real phase length, and
packages `EndpointAbelianData`.  It never switches to a noncanonical chosen
solution.

## Imports

```lean
import JoseSmoothest.EvenOrder.PellExtraction
import JoseSmoothest.EvenOrder.AbelianCertificate
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial Real
open Hyperelliptic

namespace EndpointAlternant

variable {m N : ℕ} {Z : ℝ[X]} (a : EndpointAlternant m N Z)

def curve : Hyperelliptic.Curve (endpointGenus m) where
  D := a.D
  monic_D := a.monic_D
  squarefree_D := a.squarefree_D
  natDegree_D := a.natDegree_D

theorem endpointNumerator_eq_thirdKind :
    a.curve.endpointNumerator = a.curve.thirdKindNumerator

theorem hasDegreeNPeriods :
    a.curve.HasDegreeNPeriods N

def phaseInterval :
    a.curve.RealPhaseInterval a.curve.endpointNumerator where
  left := -1
  right := 1
  left_lt_right := by norm_num
  eval_D_left := a.eval_D_neg_one
  nonpos_D := a.nonpos_D
  neg_D := by simpa [curve] using a.neg_D
  orientation := (-1 : ℝ) ^ endpointGenus m
  orientation_eq := by
    rcases Even.or_Odd (endpointGenus m) with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  numerator_positive := by
    intro x hx
    simp [Curve.endpointNumerator]
    positivity

theorem phaseLength :
    a.phaseInterval.HasLength N (N - m + 1)

def endpointAbelianData : EndpointAbelianData m N where
  contact := a.contactData
  rootMultiplicity_D_neg_one := a.rootMultiplicity_D_neg_one
  neg_D := a.neg_D
  endpoint_thirdKind := a.endpointNumerator_eq_thirdKind
  phaseInterval := a.phaseInterval
  phase_left := rfl
  phase_right := rfl
  phase_length := a.phaseLength

end EndpointAlternant

namespace EvenWeightedExtremalData

variable {m N : ℕ} (E : EvenWeightedExtremalData m N)

def extractedEndpointAbelianData
    (hm : 1 ≤ m) (hN : m ≤ N) : EndpointAbelianData m N :=
  (E.endpointAlternant hm hN).endpointAbelianData

theorem extractedEndpointAbelianData_peak_eq
    (hm : 1 ≤ m) (hN : m ≤ N) :
    (E.extractedEndpointAbelianData hm hN).peak = E.M

end EvenWeightedExtremalData

end JoseSmoothest
```

## Detailed natural-language proof blueprint

### Distinguished differential and periods

The algebraic extraction gives a genuine curve and retains a solution with
`Q≠0`, since `Q` has the nonzero leading coefficient of the degree-`N`
polynomial `Z`.  The reverse Pell--Abel theorem gives

```text
Z' = N thirdKindNumerator Q
```

and quantized degree-`N` periods.  Compare this with the algebraic identity

```text
Z' = N (X-1)^endpointGenus(m) Q.
```

Cancel the nonzero factors to identify the distinguished numerator with the
endpoint numerator.  This is noncircular: the minimizer first constructs the
curve, and logarithmic differentiation of that same supplied solution then
identifies its normalized differential.

### Real phase and exact length

Choose phase orientation `(-1)^g`, so
`orientation*(x-1)^g=(1-x)^g>0`.  The supplied-solution cosine theorem gives

```text
Z(x)=Z(-1) cos(N phase(x)).
```

Let `K=N-m+1`.  Alternation at the `K+1` endpoint-inclusive nodes forces the
right phase to reach at least `Kπ/N` and to equal `ℓπ/N` for an integer
`ℓ`.  Every intermediate multiple of `π/N` gives a distinct interior root
of `Z'`.  Endpoint contact already accounts for multiplicity `m-1`, so
`deg Z'=N-1` permits at most `N-m` interior roots.  Hence `ℓ-1≤N-m` and
`ℓ≥K`, proving `ℓ=K`.

### Recovering the intrinsic peak

The original extremal quotient and the quotient reconstructed from endpoint
contact both have value one at the right endpoint.  Comparing their common
numerator shows the extracted scale is `M/2`; its peak is therefore exactly
the original `E.M`.  This connects the unconditional intrinsic constant to
the endpoint-curve formula in `Classification`.
