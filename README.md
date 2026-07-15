# The Smoothest Average

This repository contains a Lean 4 formalization of Theorem 1.4 from the
preprint [*The smoothest average and some extremal problems for
polynomials*](https://arxiv.org/abs/2604.25074) by José Gaitán, Carlos Garzón,
and José Madrid.

**Theorem.** Let `n > 0`. Every normalized symmetric kernel supported on
`[-n,n]` with nonnegative Fourier transform satisfies

```text
‖∇⁴ after convolution by u‖ ≥
  2⁶ / (n + 2)² · tan²(π / (2n + 4)).
```

For an admissible kernel, equality is equivalent to its coefficients being
given by the Chebyshev integral formula (1.6) in the paper. Lean constructs
this coefficient-defined kernel, proves that it is admissible and attains the
sharp constant, and proves that it is the unique admissible optimizer.

The sixth-order extension now has two layers. `SixthOrder` proves the cubic
weighted minimax theorem from a zero--peak certificate. `Zolotarev` then
derives that certificate, its normalized degree-`N-3` quotient, the exact
constant `144 r² / N²` as a function of its supplied endpoint parameter,
attainment, and the unique kernel from the
Pell--Abel, differential, and equioscillation data of the first Zolotarev
polynomial. `JacobiTheta` fixes the theta conventions needed to state the
remaining analytic construction. The result is still conditional on the
existence of those analytic data: Mathlib lacks the Jacobi elliptic/Zolotarev
theory, and the paper itself neither proves existence nor uniqueness of the
modulus `k_N` used in its statement. In particular, Lean has not yet
identified the abstract endpoint parameter `r` with the paper's Jacobi
elliptic ratio.

The reusable theory now also proves an unconditional theorem at every even
difference order.  For each `m ≥ 1` and support radius `n`, `EvenOrder`
constructs the unique admissible kernel minimizing the `2m`-th difference
norm, proves its sharp lower bound, and characterizes equality.  Its sharp
constant is defined intrinsically by the unique finite-dimensional weighted
minimizer.  Lean also extracts its monic squarefree minimal-genus Pell weight,
constructs a strictly increasing real phase, proves the exact cosine
classification and scaled phase winding, and expresses the sharp constant by the
Pell weight's endpoint coefficient.  Compact hyperelliptic surfaces and
periods are needed only for a future forward special-function construction,
not for this direct classification.

For a reader-facing account of what this statement means in Lean, how the
formal proof follows the mathematics, and what the comparator and Lean kernel
verify, see [Formalization Explanation](FORMALIZATION_EXPLANATION.md).
For the engineering audit, refactor summary, and proposed upstream
contributions, see [Mathlib-Quality Review](MATHLIB_REVIEW.md).

## Lean Entry Points

The public files separate the statement surface from its proof.

- [Showcase.lean](Showcase.lean): the four public statements used as the
  comparator specification: the fourth-order lower bound, equality
  characterization, unique optimizer, and sixth-order norm reduction. Its
  four proof bodies are intentional `sorry` placeholders.
- [Solution.lean](Solution.lean): the sorry-free companion with exactly the
  same theorem surface, bridged to the internal proof library.
- [JoseSmoothest.lean](JoseSmoothest.lean): the umbrella import for the full
  mathematical formalization.
- [JoseSmoothest/EvenOrder.lean](JoseSmoothest/EvenOrder.lean): the
  unconditional sharp theorem and unique optimizer at every even order.
- [JoseSmoothest/EvenOrder/DirectClassification.lean](JoseSmoothest/EvenOrder/DirectClassification.lean):
  the unconditional minimal-genus Pell/real-phase classification and endpoint
  formula for the sharp constant.

## Repository Layout

- `JoseSmoothest/`: the internal Lean proof library.
- `blueprint/`: the implemented Markdown files mirror the current Lean
  modules; the arbitrary-even workstream maps each additional blueprint to
  one planned Lean module.  Every file records the public declarations and
  detailed natural-language proofs before implementation.
- `JoseSmoothest/JacobiTheta.lean`: normalized theta expressions for the
  remaining analytic construction.
- `JoseSmoothest/Zolotarev.lean`: the checked Pell--Abel-to-certificate and
  sixth-order kernel layer.
- `Comparator/`: configuration for `leanprover/comparator`.
- `scripts/`: pinned local comparator setup and execution helpers.
- `FORMALIZATION_EXPLANATION.md`: a non-technical guide to the statement,
  proof architecture, and trust boundary.
- `MATHLIB_REVIEW.md`: the code-quality audit and Mathlib extraction plan.
- `formalization.yaml`: provenance, scope, automation, fidelity, and
  source-to-Lean alignment metadata.

See [JoseSmoothest/README.md](JoseSmoothest/README.md) for a module-by-module
map and [blueprint/JoseSmoothest.md](blueprint/JoseSmoothest.md) for the proof
blueprint.  The natural-language-first plan for arbitrary even order begins
at the [final even-order blueprint](blueprint/JoseSmoothest/EvenOrder.md);
its direct Pell phase and optional hyperelliptic forward-construction library
are mapped in the
[special-function blueprint](blueprint/JoseSmoothest/SpecialFunctions.md).

## Build

The project is pinned to Lean and Mathlib `v4.32.0`.

```bash
lake exe cache get
lake build Showcase
lake build Solution
lake build JoseSmoothest
lake build
```

The default targets are `JoseSmoothest`, `Showcase`, and `Solution`.

## Comparator Check

The comparator checks all four public theorems, requires definitionally
identical statement environments, permits only `propext`, `Quot.sound`, and
`Classical.choice`, and replays the solution in the Lean kernel.

```bash
./scripts/setup_local_comparator_linux.sh
./scripts/run_local_comparator.sh
```

Equivalently, with compatible tools already on `PATH`:

```bash
lake test
```

See [Comparator.md](Comparator.md) for the immutable tool pins and security
notes. The pinned GitHub Actions workflow runs the same comparator check on
every push and pull request.

## Formalization Metadata

[formalization.yaml](formalization.yaml) follows the
[`mathlib-initiative/formalization.yaml`](https://github.com/mathlib-initiative/formalization.yaml)
v0.3 self-reporting format. The project is currently marked `UNLICENSED`:
publishing the source does not silently choose a software license on behalf of
the copyright holder.
