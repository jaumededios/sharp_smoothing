# Blueprint for `JoseSmoothest.lean`

## Purpose

This is the umbrella module for the complete formalization of Theorem 1.4,
including its sharp inequality and equality characterization.

The target is the paper's **first main result**, Theorem 1.4: the sharp
fourth-difference estimate for normalized symmetric kernels supported on
`[-n,n]` whose Fourier transform is nonnegative, together with the unique
equality case.  The sixth-order Zolotarev theorem and the other results in the
paper are deliberately outside this formalization.

## Blueprint/formalization correspondence

The blueprint directory is a literal mirror of the Lean module tree:

| Blueprint | Lean file |
|---|---|
| `blueprint/JoseSmoothest/Basic.md` | `JoseSmoothest/Basic.lean` |
| `blueprint/JoseSmoothest/Kernel.md` | `JoseSmoothest/Kernel.lean` |
| `blueprint/JoseSmoothest/Fourier.md` | `JoseSmoothest/Fourier.lean` |
| `blueprint/JoseSmoothest/Chebyshev.md` | `JoseSmoothest/Chebyshev.lean` |
| `blueprint/JoseSmoothest/Alternation.md` | `JoseSmoothest/Alternation.lean` |
| `blueprint/JoseSmoothest/WeightedExtremal.md` | `JoseSmoothest/WeightedExtremal.lean` |
| `blueprint/JoseSmoothest/Challenge.md` | `JoseSmoothest/Challenge.lean` |
| `blueprint/JoseSmoothest.md` | `JoseSmoothest.lean` |

There is no additional Lean module.  Private proof-engineering lemmas stay
in the file that uses them.

## Dependency and implementation order

1. `Basic`: bundled real `ℓ²(ℤ)`, finitely supported kernels, translations.
2. `Kernel`: bounded forward difference and convolution operators.
3. `Fourier`: exact operator norm = Fourier multiplier supremum.
4. `Chebyshev`: kernel polynomial, weighted norm, arcsine coefficient formula.
5. `Alternation`: the weak-sign root-counting theorem absent from Mathlib.
6. `WeightedExtremal`: Proposition 1.6 with equality uniqueness.
7. `Challenge`: both parts of Theorem 1.4.
8. This root module: one-import entry point and final verification target.

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
   operator norm of four differences after finite convolution, not merely
   Plancherel or a Holder upper bound.  This includes Fourier conjugacy,
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
   arcsine integral formula for the unique kernel.

We do **not** need to implement Fejer--Riesz, Erdos--Lax, Jacobi elliptic
functions, or Zolotarev polynomials: those belong to other results or proofs
in the paper and are not used by its proof of Theorem 1.4.

## Imports

```lean
import JoseSmoothest.Challenge
```

## Public declarations

There are no declarations in this file.  Its transitive imports expose all
definitions and the two final theorems.

## Verification blueprint

Build `JoseSmoothest.lean`, scan every project source for `sorry`/`admit`, and
run `#print axioms` on both `JoseSmoothest.smoothestAverage_inequality` and
`JoseSmoothest.smoothestAverage_eq_iff`.  Only the standard Mathlib axioms may
remain.
