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
given by the Chebyshev integral formula (1.6) in the paper. The present Lean
development does not separately construct that kernel and prove it
admissible, so attainment of the bound is not yet formalized.

For a reader-facing account of what this statement means in Lean, how the
formal proof follows the mathematics, and what the comparator and Lean kernel
verify, see [Formalization Explanation](FORMALIZATION_EXPLANATION.md).
For the engineering audit, refactor summary, and proposed upstream
contributions, see [Mathlib-Quality Review](MATHLIB_REVIEW.md).

## Lean Entry Points

The public files separate the statement surface from its proof.

- [Showcase.lean](Showcase.lean): the two paper-facing statements used as
  the comparator specification. Its two proof bodies are intentional
  `sorry` placeholders.
- [Solution.lean](Solution.lean): the sorry-free companion with exactly the
  same theorem surface, bridged to the internal proof library.
- [JoseSmoothest.lean](JoseSmoothest.lean): the umbrella import for the full
  mathematical formalization.

## Repository Layout

- `JoseSmoothest/`: the internal Lean proof library.
- `blueprint/`: eight Markdown files in one-to-one correspondence with the
  eight mathematical Lean modules; each records the public declarations and
  detailed natural-language proofs.
- `Comparator/`: configuration for `leanprover/comparator`.
- `scripts/`: pinned local comparator setup and execution helpers.
- `FORMALIZATION_EXPLANATION.md`: a non-technical guide to the statement,
  proof architecture, and trust boundary.
- `MATHLIB_REVIEW.md`: the code-quality audit and Mathlib extraction plan.
- `formalization.yaml`: provenance, scope, automation, fidelity, and
  source-to-Lean alignment metadata.

See [JoseSmoothest/README.md](JoseSmoothest/README.md) for a module-by-module
map and [blueprint/JoseSmoothest.md](blueprint/JoseSmoothest.md) for the proof
blueprint.

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

The comparator checks both parts of Theorem 1.4, requires definitionally
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
