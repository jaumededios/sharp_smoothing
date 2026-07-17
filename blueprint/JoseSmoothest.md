# Blueprint for `JoseSmoothest.lean`

## Purpose

This is the umbrella module for the complete formalization of Theorem 1.4,
including construction and uniqueness of its extremal kernel.  It also
exports the order-independent iterated-difference Fourier theory, the
certificate-conditional sixth-order argument, the theta expressions needed
for the paper's analytic construction, and the complete algebraic passage
from Lebedev's Pell--Abel data to the sixth-order optimizer.

The target is the paper's **first main result**, Theorem 1.4: the sharp
fourth-difference estimate for normalized symmetric kernels supported on
`[-n,n]` whose Fourier transform is nonnegative, together with existence and
uniqueness of the equality case.  For the sixth derivative, the formalization
proves the exact operator-to-cubic-weighted-polynomial reduction and the full
extremal argument from an abstract zero--peak certificate.  It now also proves
that the polynomial Pell equation, differential identity, and equioscillation
data asserted for the Zolotarev polynomial produce that certificate, including
the exact endpoint normalization and the paper-shaped constant in terms of an
abstract endpoint parameter.  What remains is
the genuinely analytic existence theorem constructing those data from a
modulus `k_N`; neither Mathlib nor the paper proves that theorem.

## Blueprint/formalization correspondence

The blueprint directory records the implemented Lean module tree together
with a one-to-one target tree for the optional modules still planned:

| Blueprint | Lean file |
|---|---|
| `blueprint/JoseSmoothest/Basic.md` | `JoseSmoothest/Basic.lean` |
| `blueprint/JoseSmoothest/Kernel.md` | `JoseSmoothest/Kernel.lean` |
| `blueprint/JoseSmoothest/Fourier.md` | `JoseSmoothest/Fourier.lean` |
| `blueprint/JoseSmoothest/Chebyshev.md` | `JoseSmoothest/Chebyshev.lean` |
| `blueprint/JoseSmoothest/Alternation.md` | `JoseSmoothest/Alternation.lean` |
| `blueprint/JoseSmoothest/WeightedExtremal.md` | `JoseSmoothest/WeightedExtremal.lean` |
| `blueprint/JoseSmoothest/Challenge.md` | `JoseSmoothest/Challenge.lean` |
| `blueprint/JoseSmoothest/SixthOrder.md` | `JoseSmoothest/SixthOrder.lean` |
| `blueprint/JoseSmoothest/JacobiTheta.md` | `JoseSmoothest/JacobiTheta.lean` |
| `blueprint/JoseSmoothest/Zolotarev.md` | `JoseSmoothest/Zolotarev.lean` |
| `blueprint/JoseSmoothest.md` | `JoseSmoothest.lean` |

The table above is the original implemented tree.  The arbitrary-even-order
project now also has a statement-first blueprint whose rows are in one-to-one
correspondence with its Lean modules.  `SpecialFunctions/PellAbel`,
`TwoSetAlternation`, `EvenOrder/WeightedMinimax`,
`EvenOrder/FourierReduction`, `EvenOrder/Equioscillation`, the final
`EvenOrder` kernel theorem, `EvenOrder/EndpointAlternation`,
`EvenOrder/EndpointContact`, `EvenOrder/PellExtraction`,
`SpecialFunctions/RealPellPhase`, `EvenOrder/EndpointPhase`, and
`EvenOrder/DirectClassification` have already crossed from plan to proof;
the other rows remain the exact target file structure:

| Blueprint | Target Lean file |
|---|---|
| `blueprint/JoseSmoothest/SpecialFunctions/ComplexPathIntegral.md` | `JoseSmoothest/SpecialFunctions/ComplexPathIntegral.lean` |
| `blueprint/JoseSmoothest/SpecialFunctions/PellAbel.md` | `JoseSmoothest/SpecialFunctions/PellAbel.lean` |
| `blueprint/JoseSmoothest/SpecialFunctions/RealPellPhase.md` | `JoseSmoothest/SpecialFunctions/RealPellPhase.lean` |
| `blueprint/JoseSmoothest/SpecialFunctions/HyperellipticCurve.md` | `JoseSmoothest/SpecialFunctions/HyperellipticCurve.lean` |
| `blueprint/JoseSmoothest/SpecialFunctions/RiemannBilinear.md` | `JoseSmoothest/SpecialFunctions/RiemannBilinear.lean` |
| `blueprint/JoseSmoothest/SpecialFunctions/ThirdKindDifferential.md` | `JoseSmoothest/SpecialFunctions/ThirdKindDifferential.lean` |
| `blueprint/JoseSmoothest/SpecialFunctions/MeromorphicDescent.md` | `JoseSmoothest/SpecialFunctions/MeromorphicDescent.lean` |
| `blueprint/JoseSmoothest/SpecialFunctions/PellAbelPeriod.md` | `JoseSmoothest/SpecialFunctions/PellAbelPeriod.lean` |
| `blueprint/JoseSmoothest/SpecialFunctions/RealPhase.md` | `JoseSmoothest/SpecialFunctions/RealPhase.lean` |
| `blueprint/JoseSmoothest/SpecialFunctions/PeriodMatrix.md` | `JoseSmoothest/SpecialFunctions/PeriodMatrix.lean` |
| `blueprint/JoseSmoothest/SpecialFunctions/RiemannTheta.md` | `JoseSmoothest/SpecialFunctions/RiemannTheta.lean` |
| `blueprint/JoseSmoothest/SpecialFunctions.md` | `JoseSmoothest/SpecialFunctions.lean` |
| `blueprint/JoseSmoothest/TwoSetAlternation.md` | `JoseSmoothest/TwoSetAlternation.lean` |
| `blueprint/JoseSmoothest/EvenOrder/WeightedMinimax.md` | `JoseSmoothest/EvenOrder/WeightedMinimax.lean` |
| `blueprint/JoseSmoothest/EvenOrder/FourierReduction.md` | `JoseSmoothest/EvenOrder/FourierReduction.lean` |
| `blueprint/JoseSmoothest/EvenOrder/ActiveSetPerturbation.md` | `JoseSmoothest/EvenOrder/ActiveSetPerturbation.lean` |
| `blueprint/JoseSmoothest/EvenOrder/Equioscillation.md` | `JoseSmoothest/EvenOrder/Equioscillation.lean` |
| `blueprint/JoseSmoothest/EvenOrder/EndpointAlternation.md` | `JoseSmoothest/EvenOrder/EndpointAlternation.lean` |
| `blueprint/JoseSmoothest/EvenOrder/EndpointContact.md` | `JoseSmoothest/EvenOrder/EndpointContact.lean` |
| `blueprint/JoseSmoothest/EvenOrder/PellExtraction.md` | `JoseSmoothest/EvenOrder/PellExtraction.lean` |
| `blueprint/JoseSmoothest/EvenOrder/EndpointPhase.md` | `JoseSmoothest/EvenOrder/EndpointPhase.lean` |
| `blueprint/JoseSmoothest/EvenOrder/DirectClassification.md` | `JoseSmoothest/EvenOrder/DirectClassification.lean` |
| `blueprint/JoseSmoothest/EvenOrder/AbelianCertificate.md` | `JoseSmoothest/EvenOrder/AbelianCertificate.lean` |
| `blueprint/JoseSmoothest/EvenOrder/CurveExtraction.md` | `JoseSmoothest/EvenOrder/CurveExtraction.lean` |
| `blueprint/JoseSmoothest/EvenOrder.md` | `JoseSmoothest/EvenOrder.lean` |
| `blueprint/JoseSmoothest/EvenOrder/Classification.md` | `JoseSmoothest/EvenOrder/Classification.lean` |

These are deliberately not empty Lean stubs: the blueprint is being reviewed
as mathematics before any new formal code is committed to that API.  Private
proof-engineering lemmas will stay in the file that uses them.

## Dependency and implementation order

1. `Basic`: bundled real `ℓ²(ℤ)`, finitely supported kernels, translations.
2. `Kernel`: bounded forward difference, its iterates, and convolution.
3. `Fourier`: exact iterated-difference norm = multiplier supremum.
4. `Chebyshev`: kernel polynomial, weighted norm, arcsine coefficient formula.
5. `Alternation`: the weak-sign root-counting theorem absent from Mathlib.
6. `WeightedExtremal`: Proposition 1.6 with equality uniqueness.
7. `Challenge`: Theorem 1.4, including unique kernel attainment.
8. `SixthOrder`: cubic weighted reduction and the certificate-conditional
   sixth-order theorem.
9. `JacobiTheta`: normalized theta expressions and the analytic formulae used
   to state Lebedev's construction without making unsupported claims.
10. `Zolotarev`: derives the cubic endpoint quotient, certificate, sharp
    constant, equality case, and unique kernel from the Pell--Abel and
    equioscillation package.
11. This root module: one-import entry point and final verification target.

For arbitrary even order, the planned continuation is:

12. `SpecialFunctions/PellAbel`: pure polynomial algebra and endpoint
    valuations.  This module is now implemented and checked.
13. `TwoSetAlternation`, `EvenOrder/WeightedMinimax`, and
    `EvenOrder/Equioscillation`: unconditional finite-dimensional minimizer
    and full alternation; `EvenOrder` now completes the unconditional sharp
    kernel theorem.
14. `EvenOrder/EndpointContact` and `EvenOrder/PellExtraction`:
    endpoint valuations, critical-point exhaustion, explicit squarefree Pell
    factor, and minimal genus.  These algebraic modules are now implemented.
15. `SpecialFunctions/RealPellPhase`, `EvenOrder/EndpointPhase`, and
    `EvenOrder/DirectClassification`: the direct real-variable classification
    of the extracted solution.  This is the current route and does not depend
    on compact curves, periods, or theta functions.  These modules are now
    implemented and checked.
16. Optionally, `SpecialFunctions/ComplexPathIntegral`, `HyperellipticCurve`,
    and `RiemannBilinear`: a future forward-construction route through a
    specialized analytic cut model and energy theorem.
17. Optionally, `ThirdKindDifferential`, `MeromorphicDescent`,
    `PellAbelPeriod`, and the curve-based `RealPhase`, followed by
    `AbelianCertificate`, `CurveExtraction`, and `Classification`.
18. `RiemannTheta`, only if explicit higher-genus evaluation is later needed.

See [the special-function umbrella blueprint](JoseSmoothest/SpecialFunctions.md)
for the corrected genus formula, dependency gates, and missing-Mathlib audit.

## Prerequisite audit against Mathlib `v4.32.0`

The following infrastructure is already in Mathlib and is reused:

- `MeasureTheory.Lp` over counting measure, composition with
  measure-preserving maps, continuous linear maps, and operator norms;
- the circle Fourier Hilbert basis `fourierBasis`, Fourier coefficients,
  Parseval, and Haar measure on `AddCircle`;
- `Finsupp` finite sums and polynomial degree/divisibility/root-multiplicity
  APIs;
- Chebyshev `T` and `U`, evaluation at cosine, degree, extrema/nodes,
  derivative and differential identities;
- the arcsine measure `Polynomial.Chebyshev.measureT` and the exact
  orthogonality integrals for Chebyshev `T`;
- compactness of `[-1,1]`, extrema of continuous functions, interval
  integrals, and the intermediate value theorem.

The following prerequisites are **not** present in Mathlib in the form needed
by the theorem and are implemented in this project:

1. **Counting-measure Fourier equivalence.**  Mathlib has the circle Fourier
   basis, but `Analysis.Normed.Lp.LpEquiv` explicitly lists the equivalence
   between sequence `lp` and `MeasureTheory.Lp` for counting measure as a
   TODO.  `Fourier.lean` constructs a Hilbert basis of `Lp ℂ 2 count`
   from singleton indicators and compose its representation map with
   `fourierBasis.repr.symm`.
2. **Exact convolution-multiplier norm identity.**  We need the precise
   operator norm of any finite iterate of the difference operator after
   convolution, not merely Plancherel or a Holder upper bound.  This includes
   Fourier conjugacy,
   multiplication on circle `L²`, the lower bound from localized indicator
   functions, and comparison of the real and complex operator norms.
3. **Kernel-to-Chebyshev bridge.**  No library theorem packages the passage
   from a symmetric `Finsupp ℤ ℝ` supported on `[-n,n]` to
   `u(0)+2∑u(k)T_k`, or transports its multiplier supremum through
   `x=cos ξ`.
4. **Weak alternation/root-counting lemma.**  The equality proof needs an
   alternation theorem with weak signs and correct multiplicity accounting
   when two adjacent sign intervals share a zero.  Mathlib supplies the root
   and multiplicity machinery, but not this theorem.
5. **Proposition 1.6 in formal form.**  The transformed Chebyshev optimizer
   must be constructed as an actual polynomial after proving a double
   factor at `x=1`; its degree, positivity, normalization, sharp weighted
   norm, and unique equality case all require project proofs.
6. **Coefficient reconstruction glue.**  Mathlib proves the necessary
   Chebyshev orthogonality integrals, but we must expand the kernel polynomial,
   normalize the zero and positive modes correctly, and derive the exact
   arcsine integral formula for the unique kernel.  The project also proves
   the inverse construction from a bounded-degree polynomial to a supported
   symmetric kernel.
7. **Certificate-based cubic weighted minimax theorem.**  The sixth-order
   module proves that the required zero--peak alternation data forces the
   sharp cubic weighted norm, uniqueness, and unique kernel attainment.
8. **Zolotarev endpoint algebra.**  From the correctly signed Pell equation
   and Lebedev differential identity, the project derives the triple endpoint
   zero, the exact third derivative, polynomial quotient, normalization,
   positivity, certificate, and the factor `144 r² / N²`.

The remaining prerequisite for the paper's explicit sixth-order formula is an analytic
existence theorem: construct a solution `k_N` of the displayed elliptic
equation, prove the theta quotient descends to real polynomials `Z_N,V_N`,
establish the Pell/differential identities and the unwrapped-phase
equioscillation.  Mathlib has only the underlying two-variable theta series,
and the paper cites the polynomial theory to Lebedev while not proving
existence or uniqueness of `k_N`.  Fejer--Riesz and Erdos--Lax are not needed
for the present fourth-order proof or this algebraic sixth-order layer.

## Imports

```lean
import JoseSmoothest.Challenge
import JoseSmoothest.EvenOrder
import JoseSmoothest.EvenOrder.ActiveSetPerturbation
import JoseSmoothest.EvenOrder.DirectClassification
import JoseSmoothest.EvenOrder.Equioscillation
import JoseSmoothest.EvenOrder.EndpointAlternation
import JoseSmoothest.EvenOrder.EndpointContact
import JoseSmoothest.EvenOrder.EndpointPhase
import JoseSmoothest.EvenOrder.FourierReduction
import JoseSmoothest.EvenOrder.PellExtraction
import JoseSmoothest.EvenOrder.WeightedMinimax
import JoseSmoothest.JacobiTheta
import JoseSmoothest.SpecialFunctions.PellAbel
import JoseSmoothest.SpecialFunctions.RealPellPhase
import JoseSmoothest.TwoSetAlternation
import JoseSmoothest.Zolotarev
```

## Public declarations

There are no declarations in this file.  Its transitive imports expose the
fourth-order theorem, unique optimizer, generic iterated-difference theory,
theta foundations, and the Zolotarev-data-conditional sixth-order results.

## Verification blueprint

Build `JoseSmoothest.lean`, scan every mathematical project source for
`sorry`/`admit`, and run `#print axioms` on the fourth-order attainment theorem
and the sixth-order certificate theorem.  Only the standard Mathlib axioms
may remain.
