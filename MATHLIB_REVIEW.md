# Mathlib-Quality Review

This is an engineering review of the current formalization against Mathlib's
published contribution and review standards. It distinguishes improvements
that belong in this repository from code that could become a Mathlib
contribution after further generalization and human review.

## Review standard

The review used Mathlib's current official guidance:

- [Contributing to Mathlib](https://leanprover-community.github.io/contribute/index.html)
- [Mathlib's values](https://leanprover-community.github.io/contribute/values.html)
- [Library style](https://leanprover-community.github.io/contribute/style.html)
- [Naming conventions](https://leanprover-community.github.io/contribute/naming.html)
- [Documentation style](https://leanprover-community.github.io/contribute/doc.html)
- [Pull-request review guide](https://leanprover-community.github.io/contribute/pr-review.html)

The resulting rubric was: correctness and trust boundary first; weak
hypotheses and reusable statements; a stable API around definitions; focused
imports and sensible file placement; documented declarations and long proofs;
then proof simplification where it improves readability and robustness.
Shorter source was not treated as a goal by itself.

Mathlib's contribution guide also requires disclosure of AI use and active
supervision by a Lean subject expert. The files here should therefore not be
submitted upstream verbatim or as an unattended AI-generated pull request.

## Refactor performed

- `Basic`: expanded the module map and retained the minimal foundational API.
- `Kernel`: documented the operators, kept their implementation small, and
  exposed the order-generic difference-after-averaging operator used by both
  the fourth- and sixth-order developments.
- `Fourier`: parameterized the complex symbol, Fourier intertwining, and
  real/complex norm comparison by the number of differences; added even-order
  and fourth-/sixth-order rewrites; and retained named projections for all
  four admissibility hypotheses.
- `Chebyshev`: narrowed an import, replaced a deprecated theorem name,
  removed flexible `simp`, documented every public declaration, and added the
  inverse polynomial-to-kernel construction and injectivity theorem.
- `Alternation`: replaced the broad import, documented proof phases, and
  removed the unnecessary hypothesis `0 < m`.
- `WeightedExtremal`: narrowed imports, removed lint warnings, and introduced
  `IsAdmissibleWeightedPolynomial` with theorem methods for the sharp bound
  and equality case.
- `Challenge`: removed the unused internal hypothesis `0 < n`, packaged the
  kernel-to-polynomial feasibility bridge, constructed the unique attaining
  kernel, and eliminated duplicated hypothesis plumbing.
- `SixthOrder`: isolates the order-six operator reduction and the reusable
  property-first zero--peak alternation argument from the analytic
  Zolotarev/elliptic construction, then transfers a supplied certificate back
  to conditional kernel attainment and uniqueness.
- `JacobiTheta`: fixes the period-one theta normalization used by Mathlib,
  defines the translated theta expressions and Lebedev ratio, and deliberately
  limits its theorems to the derivative and symmetry facts currently supported
  by the library.
- `Zolotarev`: derives the endpoint cube, exact normalization, degree,
  nonnegativity, zero--peak certificate, `144 r² / N²` constant, and unique
  kernel from the Pell--Abel/differential/equioscillation package. It also
  records the elementary Jacobi endpoint-scale calculation.
- `Showcase` / `Solution`: define iterated differences at the public boundary,
  preserve the paper's `n > 0` hypothesis, and check the fourth-order bound,
  equality, unique attainment, and sixth-order norm reduction.

The new local API has several useful paths:

```text
admissible.support / symmetric / sum_eq_one / fourier_nonnegative
admissible.kernelPolynomial.norm_ge / norm_eq_iff
kernelOfPolynomial / kernelPolynomial_kernelOfPolynomial
kernelOfPolynomial_isAdmissible / kernel_eq_of_kernelPolynomial_eq
extremalKernel / extremalKernel_attains / existsUnique_extremalKernel
```

Thus downstream proofs no longer know the nesting of the admissibility
conjunction or repeatedly pass the same degree, nonnegativity, and endpoint
normalization arguments.

## Automated checks

The following checks pass on Mathlib `v4.32.0`:

- `lake build` completes;
- `#lint` reports no declaration-linter errors in the audited modules;
- the official `lint-style` executable reports no source-style findings;
- LSP diagnostics contain no mathematical-source warnings other than the
  unresolved copyright-header warning described below;
- every mathematical Lean line is at most 100 columns;
- `git diff --check` passes;
- LSP axiom verification finds exactly `propext`, `Classical.choice`, and
  `Quot.sound` for each main theorem, with no suspicious source patterns;
- the real `leanprover/comparator` check validates all four public theorems.

The four `sorry` declarations in `Showcase.lean` are intentional comparator
specifications. `Solution.lean` and the mathematical library are sorry-free.

## Good candidates for Mathlib

These should be proposed separately, in small dependency-ordered pull
requests. Searches against the pinned library found useful ingredients but no
existing theorem with the same complete API.

### 1. Weak polynomial alternation

`polynomial_eq_zero_of_alternating_signs` is already isolated in
`Alternation.lean` and is independent of the paper. Before upstreaming, it
should be generalized from `ℝ` to a suitable linear ordered field and moved
to the polynomial/Lagrange-interpolation area. Its barycentric proof is a
natural complement to the existing root-counting and interpolation API.

This is the smallest and strongest first contribution candidate.

### 2. Chebyshev basis and coefficient extensionality

The private Chebyshev basis machinery supports reusable facts:

- weighted orthogonality computes a Chebyshev basis coordinate;
- the normalized interval integral computes the corresponding coefficient;
- coordinates above the degree vanish;
- bounded-degree polynomials are equal when their initial Chebyshev
  coefficients agree.

The new finite reconstruction results also show that taking these
coefficients and rebuilding a bounded-degree Chebyshev expansion is a genuine
inverse. The kernel wrapper itself is problem-specific, but the underlying
finite Chebyshev-series reconstruction is a plausible addition to the same
upstream API.

These should be extracted from the kernel-specific file into the
`Polynomial.Chebyshev` namespace, probably adjacent to Mathlib's
`Chebyshev.Orthogonality` module. The basis definition and normalization need
community review before their names become permanent API.

### 3. Counting-measure `L²` Fourier bridge

`Fourier.lean` privately constructs the singleton-indicator Hilbert basis of
counting-measure `L²`, then identifies it with the circle Fourier basis. A
Mathlib contribution should first expose the generic singleton basis for
counting measure; the specialized equivalence for `ℤ` can be a second change.
This would remove a large project-local compatibility layer between
`MeasureTheory.Lp` and the sequence-space representation used by
`HilbertBasis.repr`.

### 4. Exact norm of an `L²` multiplication operator

The current proof shows that multiplication by a continuous function on the
circle has operator norm equal to its uniform norm, using full support of Haar
measure. The upstream theorem should be formulated for a compact space with a
finite full-support measure, and preferably for the widest useful range of
`Lp` exponents. Mathlib already provides the upper bound; the localized open
set argument supplies the missing reverse inequality.

### 5. Real/complex operator-norm transfer

The real-to-complex comparison in `Fourier.lean` is reusable in principle,
but the current statement is specialized to counting-measure `L²`. It should
only be extracted after choosing a canonical Mathlib complexification API;
otherwise a project-specific public theorem would create the wrong long-term
abstraction.

## Parts that should remain project-local

The affine Chebyshev scaling, transformed peak nodes, double-root division,
specific weighted constants, kernel polynomial, polynomial-to-kernel wrapper,
and equality coefficient formula encode this paper's problem. The sixth-order
cubic factorization, `CubicZeroPeakCertificate`, and `CubicZolotarevData` are
also deliberately property-first local interfaces: their alternation and
endpoint algebra are reusable, but the packages are tailored to the
Zolotarev application. The theta-one through theta-four wrappers could become
an upstream contribution only together with the expected nonvanishing,
addition, and classical-identification API; definitions alone would be too
thin. These pieces
are well factored inside this repository but are not presently broad enough
to justify Mathlib's maintenance burden. `IsAdmissibleWeightedPolynomial`
and `IsAdmissibleCubicWeightedPolynomial` are useful local APIs, not upstream
candidates by themselves.

## Remaining gates before an upstream contribution

1. Discuss each proposed statement, generality, name, and destination on the
   Lean Zulip before opening a pull request.
2. Have a human expert understand and referee every proof, including the
   mathematical statement and its interaction with existing Mathlib APIs.
3. Add Mathlib's standard copyright and Apache-2.0 header only when the
   contributor has authorized that licensing. This repository is currently
   marked `UNLICENSED`, so this review deliberately does not invent a license;
   that is the source of the remaining header-linter warning.
4. Add the paper to Mathlib's bibliography for any paper-dependent material,
   and split contributions into the small units listed above.
5. Rebase each candidate on current Mathlib master and run its full lint,
   import, documentation, and CI suite there.
