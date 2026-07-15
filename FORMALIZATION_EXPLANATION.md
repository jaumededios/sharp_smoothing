# Formalization Explanation

This note explains what the Lean formalization checks and how its pieces
correspond to the mathematics in [*The smoothest average and some extremal
problems for polynomials*](https://arxiv.org/abs/2604.25074). It is written for
readers who are comfortable with mathematical arguments but do not know Lean.
The low-level proof scripts are not explained line by line; the aim is to make
the statement, mathematical strategy, and trust boundary understandable.

## What has been formalized

The project formalizes Theorem 1.4, the paper's first main result, together
with Proposition 1.6, the polynomial extremal theorem on which its proof
depends. There are two conclusions:

1. every admissible averaging kernel satisfies the paper's
   fourth-difference lower bound;
2. for an already-admissible kernel, equality is equivalent to the Chebyshev
   integral formula (1.6) in the paper.

The formalization does not separately construct the coefficient-defined
kernel and prove that it is admissible. It therefore proves the lower bound
and a conditional, at-most-one equality characterization, but not attainment
of the bound in the original kernel problem. At the supporting polynomial
level, the extremal polynomial is constructed and its sharpness is proved.

The results about other derivative orders, including the sixth-order
Zolotarev problem, are not part of this formalization.

## The mathematical statement in ordinary language

Fix a positive integer `n`. A kernel is a finite list of real weights

```text
u(-n), ..., u(-1), u(0), u(1), ..., u(n).
```

It acts on a square-summable sequence `f : ℤ → ℝ` by averaging translated
copies of `f`:

```text
(Aᵤ f)(j) = ∑ₖ u(k) f(j-k).
```

The kernel is *admissible* when it has four properties:

- it is supported on the integers from `-n` to `n`;
- it is symmetric: `u(-k) = u(k)`;
- its weights sum to one;
- its Fourier transform is nonnegative at every frequency.

Let the forward difference be `∇f(j) = f(j+1) - f(j)`. The quantity being
minimized is the operator norm of taking the average and then four forward
differences:

```text
Cᵤ = ‖∇⁴ Aᵤ‖.
```

Theorem 1.4 says

```text
Cᵤ ≥ 2⁶ / (n + 2)² · tan²(π / (2n + 4)).
```

For an admissible `u`, equality is equivalent to the following condition: for
every `0 ≤ m ≤ n`, the symmetric coefficients of `u` are

```text
u(m) = u(-m)
     = 1/π ∫₋₁¹ Sₙ(x) Tₘ(x) / √(1-x²) dx,
```

where `Tₘ` is the degree-`m` Chebyshev polynomial and `Sₙ` is the transformed
Chebyshev extremal polynomial from the paper.

## A 90-second Lean primer

A Lean theorem has typed variables, named hypotheses, and a conclusion. For
example, the beginning of the formal inequality is:

```lean
theorem smoothestAverage_inequality
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    sharpConstant n ≤ fourthOrderSmoothness u := by
  -- proof
```

Here `n : ℕ` says that `n` is a natural number. The expression
`n_positive : 0 < n` is a hypothesis, as is the statement that `u` is
admissible. The colon before the last line separates the assumptions from the
conclusion. The words `:= by` begin the proof.

Lean checks that every proof step has the required type. At the end it
constructs a proof term, and Lean's small kernel checks that term. This is
stronger than testing examples: the result is verified for every `n`, `u`,
and admissibility proof allowed by the statement.

## The exact Lean results

The two main declarations at the paper-facing comparator boundary are:

```lean
theorem smoothestAverage_inequality
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    sharpConstant n ≤ fourthOrderSmoothness u

theorem smoothestAverage_eq_iff
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    fourthOrderSmoothness u = sharpConstant n ↔
      IsExtremalKernel n u
```

The symbol `↔` means “if and only if.” Thus, for an already-admissible `u`,
the coefficient formula implies equality and equality implies the coefficient
formula. This declaration does not by itself produce such a kernel or prove
that the coefficient formula satisfies all four admissibility conditions.
Internally, Lean proves a slightly stronger reusable result: its proof does
not need `n_positive`, and therefore also covers `n = 0`. The paper-facing
statement keeps the hypothesis exactly as stated in the theorem.

## Translating the objects into Lean

Most background objects come from
[Mathlib](https://github.com/leanprover-community/mathlib4), Lean's standard
mathematical library. The project supplies the definitions specific to this
problem.

### Sequences and kernels

The paper works with the Hilbert space `ℓ²(ℤ)`. Mathlib represents this as an
`L²` space over the integers with counting measure:

```lean
abbrev Sequence := Lp ℝ 2 (Measure.count : Measure ℤ)
```

A kernel is represented by a finitely supported function on all integers:

```lean
abbrev Kernel := ℤ →₀ ℝ
```

This differs slightly from presenting `u` as a function whose domain is
exactly `{-n, ..., n}`. The support condition in `IsAdmissibleKernel` makes
the two descriptions equivalent for this theorem.

### Translation, averaging, and differences

Integer translation preserves counting measure, so Mathlib turns it into a
linear isometry of `L²`. The forward difference is translation by one minus
the identity. Averaging by `u` is the finite operator sum

```text
Aᵤ = ∑ₖ u(k) τₖ.
```

The formal smoothness quantity is then defined literally as the norm of the
composite operator:

```lean
def fourthOrderSmoothness (u : Kernel) : ℝ :=
  ‖(differenceOperator ^ 4).comp (averagingOperator u)‖
```

### Admissible kernels

For a symmetric real kernel, its Fourier transform is the real cosine sum

```text
û(ξ) = ∑ₖ u(k) cos(kξ).
```

The Lean predicate packages the four hypotheses of the theorem:

```lean
def IsAdmissibleKernel (n : ℕ) (u : Kernel) : Prop :=
  (∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0) ∧
  (∀ k : ℤ, u (-k) = u k) ∧
  u.sum (fun _ a ↦ a) = 1 ∧
  ∀ ξ : ℝ, 0 ≤ kernelFourierTransform u ξ
```

The notation `Finset.Icc (-n) n` means the finite integer interval from `-n`
to `n`. A chain of `∧` symbols means that all four conditions must hold.

### The equality case

`IsExtremalKernel n u` says directly that every coefficient of `u` agrees
with formula (1.6):

```lean
def IsExtremalKernel (n : ℕ) (u : Kernel) : Prop :=
  ∀ m : ℕ, m ≤ n →
    let coefficient :=
      1 / Real.pi *
        ∫ x in (-1 : ℝ)..1,
          extremalPolynomial n x * chebyshevT m x /
            Real.sqrt (1 - x ^ 2)
    u m = coefficient ∧ u (-(m : ℤ)) = coefficient
```

The integral has an apparent singularity at the endpoints, but it is the
standard integrable Chebyshev weight. Mathlib already contains the relevant
Chebyshev weight/measure and orthogonality theorems.

## The proof architecture

The formal proof follows the paper's conceptual reduction rather than
searching directly over kernels.

```mermaid
flowchart LR
  A["Admissible kernel u"] --> B["Operator on ℓ²(ℤ)"]
  B --> C["Fourier multiplier norm"]
  C --> D["Polynomial p on [-1,1]"]
  D --> E["Sharp weighted Chebyshev problem"]
  E --> F["Lower bound and unique optimizer"]
  F --> G["Chebyshev coefficient formula for u"]
```

### 1. Package the analytic operators

`Basic.lean` and `Kernel.lean` construct translations, convolution, and the
forward difference as bounded linear operators on real `ℓ²(ℤ)`. This makes
the norm in the theorem an ordinary Mathlib operator norm.

### 2. Diagonalize by the Fourier transform

On the Fourier side, translation becomes multiplication by a complex
exponential. Consequently, four differences after averaging become
multiplication by a scalar function of the frequency `ξ`. Its absolute value
is

```text
4 (1 - cos ξ)² |û(ξ)|.
```

`Fourier.lean` proves the exact identity between the operator norm and the
supremum of this multiplier. The upper bound follows from multiplication on
`L²`; the reverse bound uses functions concentrated on a small arc near a
chosen frequency. Exact equality here is essential for identifying every
case of equality later.

Mathlib provides the Fourier basis on the circle, but not the exact
equivalence from its sequence representation to `L²(ℤ)` with counting
measure needed by this statement. The project constructs that missing bridge
from the singleton basis of `L²(ℤ)`.

### 3. Replace the Fourier sum by a polynomial

Symmetry converts the Fourier transform into a cosine polynomial. Since
`Tₖ(cos ξ) = cos(kξ)`, `Chebyshev.lean` associates to `u` the polynomial

```text
p(x) = u(0) + 2 ∑ₖ₌₁ⁿ u(k) Tₖ(x).
```

The four kernel hypotheses become transparent polynomial facts:

- `degree p ≤ n`;
- `p(1) = 1`;
- `p(x) ≥ 0` on `[-1,1]`.

The change of variables `x = cos ξ` turns the operator norm into

```text
4 · sup{|(1-x)² p(x)| : -1 ≤ x ≤ 1}.
```

Thus the infinite-dimensional operator problem has become a finite-degree
extremal problem for nonnegative polynomials.

### 4. Solve the weighted polynomial problem

`WeightedExtremal.lean` formalizes Proposition 1.6. It constructs the
candidate optimizer by applying an affine change of variables to a
Chebyshev polynomial `T_N`. Its numerator has a double zero at `x = 1`, so
division by `(1-x)²` produces a genuine polynomial of degree `N-2`, not a
rational function. The proof then establishes its normalization,
nonnegativity, degree, and exact weighted norm.

For uniqueness, compare any competing polynomial `p` with the candidate
`S`. Since both equal one at `x = 1`, their difference factors as

```text
p - S = (1-X) r.
```

At transformed Chebyshev nodes, the norm bound forces `r` to have alternating
weak signs. `Alternation.lean` proves that a polynomial of such low degree
cannot alternate at that many ordered points unless it is zero. Therefore
`r = 0`, so `p = S`. This proves both sharpness and uniqueness.

### 5. Recover the kernel coefficients

Chebyshev orthogonality recovers each coefficient of `p` through the weighted
integral

```text
1/π ∫₋₁¹ p(x) Tₘ(x) / √(1-x²) dx.
```

`Chebyshev.lean` proves this coefficient formula with the correct separate
normalizations for the zeroth and positive modes. Once the polynomial is
known to be the unique optimizer, this formula gives exactly the coefficients
in `IsExtremalKernel`. This proves the conditional equality characterization;
constructing the resulting kernel and verifying its admissibility remains
outside the current development.

Finally, `JoseSmoothest/Challenge.lean` combines the exact Fourier norm, the
weighted polynomial theorem, and coefficient reconstruction to prove both
parts of Theorem 1.4.

## Where the proof lives

- [`JoseSmoothest/Basic.lean`](JoseSmoothest/Basic.lean): `ℓ²(ℤ)`, finite
  kernels, and translation.
- [`JoseSmoothest/Kernel.lean`](JoseSmoothest/Kernel.lean): difference and
  averaging operators.
- [`JoseSmoothest/Fourier.lean`](JoseSmoothest/Fourier.lean): the exact
  Fourier multiplier/operator-norm identity.
- [`JoseSmoothest/Chebyshev.lean`](JoseSmoothest/Chebyshev.lean): the kernel
  polynomial and coefficient reconstruction.
- [`JoseSmoothest/Alternation.lean`](JoseSmoothest/Alternation.lean): the
  alternating-sign polynomial uniqueness lemma.
- [`JoseSmoothest/WeightedExtremal.lean`](JoseSmoothest/WeightedExtremal.lean):
  Proposition 1.6 and its unique optimizer.
- [`JoseSmoothest/Challenge.lean`](JoseSmoothest/Challenge.lean): the
  sorry-free assembly of Theorem 1.4.
- [`Showcase.lean`](Showcase.lean): the statement-only comparator interface.
- [`Solution.lean`](Solution.lean): the comparator solution linked to the
  full proof.

For declaration-by-declaration natural-language proofs, see the
[`blueprint/`](blueprint/) directory.

## What is trusted, and what the comparator adds

The public statement file and the internal theorem file have different jobs:

- the root [`Showcase.lean`](Showcase.lean) fixes the public statements to
  be checked. Its two theorem bodies are intentional `sorry` placeholders;
  this file is a specification, not the evidence for the result;
- [`JoseSmoothest/Challenge.lean`](JoseSmoothest/Challenge.lean) belongs to
  the mathematical library and contains complete proofs. It and the root
  [`Solution.lean`](Solution.lean) are sorry-free.

The [Lean comparator](https://github.com/leanprover/comparator) checks that
the challenge and solution expose definitionally identical theorem
statements. It then exports and kernel-checks the solution while allowing
only the standard axioms

```text
propext, Quot.sound, Classical.choice.
```

In particular, `sorryAx` is not permitted in the checked solution. The
comparator makes it harder for an alleged solution to change a definition,
weaken a hypothesis, or hide an extra axiom while retaining a theorem with a
similar-looking name.

There is still an important semantic trust boundary. Lean proves the theorem
that was encoded; readers must still check that definitions such as
`IsAdmissibleKernel`, `fourthOrderSmoothness`, and `IsExtremalKernel` faithfully
express the paper's mathematics. The public statements and this explanation
are intended to make that review possible.

The formalization was produced with substantial OpenAI Codex assistance and
has passed Lean builds and comparator checking, but it has not yet received
independent human peer review or author verification. The current provenance
and review status are recorded in [`formalization.yaml`](formalization.yaml).

## Reproducing the checks

Build the mathematical development with:

```bash
lake exe cache get
lake build
```

On Linux, install the pinned audit tools and run the comparator with:

```bash
./scripts/setup_local_comparator_linux.sh
./scripts/run_local_comparator.sh
```

The immutable tool revisions and the role of the landrun sandbox are
documented in [`Comparator.md`](Comparator.md).

## Further reading

- [The source paper](https://arxiv.org/abs/2604.25074).
- [The detailed proof blueprint](blueprint/JoseSmoothest.md).
- [The module-by-module library map](JoseSmoothest/README.md).
- [Appendix: Lean formalization](https://arxiv.org/abs/2607.08656), whose
  reader-facing presentation inspired the organization of this note.
