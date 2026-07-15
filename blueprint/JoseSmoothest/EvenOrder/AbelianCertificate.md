# Blueprint for `JoseSmoothest/EvenOrder/AbelianCertificate.lean`

## Purpose and status

This file is the sole bridge from explicit endpoint Pell--Abel data to the
generic smoothing certificate.  Unlike the earlier draft, its structure
retains the supplied `EndpointContactData.solution`; it never replaces that
solution by a noncanonical `recoveredSolution`.  Period quantization is a
theorem derived from the retained solution.

Every implication in this module is unconditional.  Existence of the data
will be supplied in `CurveExtraction` by the finite-dimensional minimizer.

## Imports

```lean
import JoseSmoothest.EvenOrder.EndpointContact
import JoseSmoothest.EvenOrder.WeightedMinimax
import JoseSmoothest.SpecialFunctions.RealPhase
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial Real
open Hyperelliptic

namespace EndpointContactData

variable {m N : ℕ} (d : EndpointContactData m N)

def curve : Hyperelliptic.Curve (endpointGenus m) where
  D := d.D
  monic_D := d.monic_D
  squarefree_D := d.squarefree_D
  natDegree_D := d.natDegree_D

end EndpointContactData

structure EndpointAbelianData (m N : ℕ) where
  contact : EndpointContactData m N
  rootMultiplicity_D_neg_one :
    rootMultiplicity (-1) contact.D = 1
  neg_D : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, contact.D.eval x < 0
  endpoint_thirdKind :
    contact.curve.endpointNumerator = contact.curve.thirdKindNumerator
  phaseInterval :
    contact.curve.RealPhaseInterval contact.curve.endpointNumerator
  phase_left : phaseInterval.left = -1
  phase_right : phaseInterval.right = 1
  phase_length : phaseInterval.HasLength N (N - m + 1)

namespace EndpointAbelianData

variable {m N : ℕ} (d : EndpointAbelianData m N)

theorem N_pos : 0 < N := by omega

theorem hasDegreeNPeriods :
    d.contact.curve.HasDegreeNPeriods N

theorem solution_derivative :
    derivative d.contact.solution.P =
      Polynomial.C (N : ℝ) *
        d.contact.curve.endpointNumerator * d.contact.solution.Q

theorem endpointScale_pos : 0 < d.contact.endpointScale

def Z : ℝ[X] := d.contact.solution.P

def scale : ℝ := d.contact.endpointScale

def peak : ℝ := 2 * d.scale

def numerator : ℝ[X] :=
  Polynomial.C d.scale * (1 - d.Z)

def endpointQuotient : ℝ[X] := d.contact.endpointQuotient

def orientation : ℝ := d.Z.eval (-1)

def nodes : Fin (N - m + 1) → ℝ :=
  fun j ↦ d.phaseInterval.node N (N - m + 1)
    d.N_pos d.phase_length j.castSucc

theorem orientation_eq : d.orientation = 1 ∨ d.orientation = -1

theorem strictMono_nodes : StrictMono d.nodes

theorem nodes_mem_Ico (j : Fin (N - m + 1)) :
    d.nodes j ∈ Set.Ico (-1 : ℝ) 1

theorem node_value (j : Fin (N - m + 1)) :
    d.Z.eval (d.nodes j) =
      d.orientation * (-1 : ℝ) ^ (j : ℕ)

theorem Z_bounds {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    -1 ≤ d.Z.eval x ∧ d.Z.eval x ≤ 1

theorem exists_Z_eq_neg_one :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, d.Z.eval x = -1

theorem numerator_bounds {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ d.numerator.eval x ∧ d.numerator.eval x ≤ d.peak

theorem exists_numerator_eq_peak :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      d.numerator.eval x = d.peak

theorem endpoint_factorization :
    (Polynomial.C 1 - X) ^ m * d.endpointQuotient = d.numerator

theorem endpointQuotient_eval_one :
    d.endpointQuotient.eval 1 = 1

theorem endpointQuotient_nonnegative {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ d.endpointQuotient.eval x

theorem natDegree_endpointQuotient_le :
    d.endpointQuotient.natDegree ≤ N - m

def zeroPeakCertificate :
    EvenZeroPeakCertificate m N d.numerator d.peak

def extremalData : EvenWeightedExtremalData m N where
  S := d.endpointQuotient
  q := d.numerator
  M := d.peak
  admissible := {
    degree_le := d.natDegree_endpointQuotient_le
    nonnegative := d.endpointQuotient_nonnegative
    eval_one := d.endpointQuotient_eval_one }
  factorization := d.endpoint_factorization
  certificate := d.zeroPeakCertificate

theorem peak_formula :
    d.peak =
      (-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 *
        d.contact.endpointDValue / (N : ℝ) ^ 2

theorem predictedDifferenceConstant :
    2 ^ m * d.peak =
      2 ^ m * (-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 *
        d.contact.endpointDValue / (N : ℝ) ^ 2

end EndpointAbelianData

end JoseSmoothest
```

## Detailed natural-language proof blueprint

### The retained solution and its periods

`EndpointContactData` already contains the exact degree-`N` Pell solution,
equal leading coefficients, value one at the right endpoint, and exact
`m`-fold contact.  Its monic squarefree polynomial of degree `2g+2` defines
the curve directly.

The reverse Pell--Abel theorem applied to this solution proves both degree-`N`
period quantization and

```text
Z' = N thirdKindNumerator Q.
```

The `endpoint_thirdKind` field changes this to the endpoint differential
identity.  There is no classical-choice comparison and no sign
normalization: `Z(1)=1` is already part of `contact`.
The solution's `Q` is nonzero because its leading coefficient equals the
nonzero leading coefficient of the positive-degree `P`; this supplies the
nontriviality hypothesis of the real cosine theorem.

### Positivity of the scale

If `m` is even, `D` does not vanish at one and continuity from the negative
open interval gives `d=D(1)<0`; the sign factor `(-1)^(m+1)` is negative.  If
`m` is odd, `D` has a simple root at one.  Since it is negative immediately
to the left, `D'(1)>0`; now the sign factor is positive.  In both cases

```text
(-1)^(m+1) endpointDValue > 0,
```

so the endpoint scale is positive.

### Phase, nodes, and bounds

Apply the supplied-solution cosine theorem from `RealPhase` to the retained
Pell solution and `solution_derivative`.  The phase interval begins at `-1`,
so the base sign is exactly `Z(-1)=orientation`; the Pell identity at this
branch point makes it `±1`.  The phase length gives `N-m+2` nodes including
both endpoints.  Dropping the final endpoint leaves the `N-m+1` certificate
nodes in `[-1,1)`, with strict ordering and alternating values.

The real Pell bound, or the cosine formula, gives `-1≤Z≤1` throughout the
interval.  Since `N≥m`, the phase makes at least one half-turn, so one of its
node values is `-1`.

### Numerator, quotient, and certificate

Positive `scale` and the bound on `Z` imply

```text
0 ≤ scale(1-Z) ≤ 2 scale = peak.
```

A point with `Z=-1` attains the peak.  The endpoint factorization, quotient
normalization, and degree come from `EndpointContactData`.  On `[-1,1)`, the
factor `(1-x)^m` is positive, so numerator nonnegativity passes to the
quotient; at one use its proved value one.  These fields define both the
generic zero--peak certificate and a complete `EvenWeightedExtremalData`
package.

### Constant

Substituting `peak=2*endpointScale` gives

```text
peak = (-1)^(m+1) m² endpointDValue / N².
```

The Fourier reduction for a `2m`-fold difference contributes `2^m`.  For
`m=3`, `D=(X²-1)H` and `endpointDValue=D'(1)=2H(1)=2r²`, recovering
`144r²/N²`.  This remains a required regression theorem.
