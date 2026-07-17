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
depends. The fourth-order development proves four conclusions:

1. every admissible averaging kernel satisfies the paper's
   fourth-difference lower bound;
2. for an admissible kernel, equality is equivalent to the Chebyshev integral
   formula (1.6) in the paper;
3. the kernel defined by that coefficient formula is admissible and attains
   the sharp bound;
4. this kernel is the unique admissible optimizer.

At the supporting polynomial level, the extremal polynomial is constructed
and its sharpness and uniqueness are proved. Lean then reconstructs a finite
symmetric kernel from its Chebyshev coefficients and transports all the
polynomial properties back to the kernel problem.

There is also a sixth-order development. It reduces the sixth-difference
operator norm to a cubic weighted polynomial norm and proves sharpness and
uniqueness from an abstract zero--peak certificate. A second module proves
that Lebedev's polynomial Pell equation, differential identity, and
equioscillation data produce that certificate and the same algebraic constant
as in the paper, in terms of a supplied endpoint parameter `r`. The remaining
gap is analytic existence: constructing those
polynomial data from an elliptic modulus `k_N`. Mathlib does not contain that
theory, and the paper calls `k_N` “the solution” without proving that such a
solution exists or is unique.

Beyond the paper's stated fourth- and sixth-order results, the reusable
development now proves the underlying minimization theorem for every even
difference order.  Given `m ≥ 1` and a support radius `n`, Lean constructs an
admissible kernel minimizing the norm of `2m` forward differences, proves the
sharp lower bound, and proves that this kernel is unique.  The sharp constant
is defined by the unique weighted-polynomial minimizer.  Lean now also gives
a direct Pell--Abel classification of that minimizer: it extracts a monic
squarefree polynomial `D`, defines a strictly increasing real phase by an
explicit integral, proves that the normalized extremizer is a cosine of that
phase, and proves the exact number of half-turns.  The sharp constant is an
explicit endpoint coefficient of `D`.  What remains separate is a *forward*
closed theta/period formula constructing `D` without first constructing the
minimizer; that is not needed for existence, optimality, or the direct
classification.

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

The formalization also defines the finite symmetric kernel with exactly
these coefficients, proves all four admissibility conditions, proves that it
has norm equal to the displayed constant, and proves that any other
admissible kernel with that norm is equal to it.

## A 90-second Lean primer

A Lean theorem has typed variables, named hypotheses, and a conclusion. For
example, the beginning of the formal inequality is:

```lean
theorem smoothestAverage_inequality
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    sharpConstant n ≤ iteratedDifferenceSmoothness 4 u := by
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

The four declarations at the paper-facing comparator boundary are:

```lean
theorem smoothestAverage_inequality
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    sharpConstant n ≤ iteratedDifferenceSmoothness 4 u

theorem smoothestAverage_eq_iff
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    iteratedDifferenceSmoothness 4 u = sharpConstant n ↔
      IsExtremalKernel n u

theorem smoothestAverage_existsUnique_optimizer
    (n : ℕ)
    (n_positive : 0 < n) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧
        iteratedDifferenceSmoothness 4 u = sharpConstant n

theorem sixthDifference_eq_cubicWeightedNorm
    (n : ℕ)
    (n_positive : 0 < n)
    (u : Kernel)
    (admissible : IsAdmissibleKernel n u) :
    iteratedDifferenceSmoothness 6 u =
      8 * cubicWeightedPolynomialNorm (kernelPolynomial n u)
```

The symbol `↔` means “if and only if.” Thus, for an already-admissible `u`,
the coefficient formula implies equality and equality implies the coefficient
formula. The symbol `∃!` means “there exists exactly one.” The third theorem
makes attainment and uniqueness part of the checked interface, while the
fourth checks the exact operator-to-polynomial reduction that starts the
sixth-order development. The internal fourth-order library exposes the
explicit optimizer as well:

```lean
def extremalKernel (n : ℕ) : Kernel

theorem extremalKernel_isAdmissible (n : ℕ) :
    IsAdmissibleKernel n (extremalKernel n)

theorem extremalKernel_attains (n : ℕ) :
    fourthOrderSmoothness (extremalKernel n) = sharpConstant n

theorem existsUnique_extremalKernel (n : ℕ) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧
        fourthOrderSmoothness u = sharpConstant n
```

The arbitrary-even-order theorem has the analogous internal interface:

```lean
theorem existsUnique_smoothestEvenOrderKernel
    (m n : ℕ) (hm : 1 ≤ m) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧
        differenceSmoothness (2 * m) u =
          sharpEvenDifferenceConstant m n hm
```

Companion theorems prove the lower bound for every admissible kernel and show
that equality is equivalent first to equality of kernel polynomials and then
to equality with this canonical kernel.

Internally, Lean proves slightly stronger reusable fourth-order results: none
of those proofs needs `n_positive`, and they therefore also cover `n = 0`.
The paper-facing comparator statements keep the positive-order hypothesis
explicit.

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
  G --> H["Construct an admissible extremal kernel"]
  H --> I["Attainment and uniqueness"]
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

The same file proves the inverse construction needed after solving the
polynomial problem. Given a polynomial of degree at most `n`, take its first
`n+1` Chebyshev coefficients and place them symmetrically at the integer
indices from `-n` to `n`. Reconstructing the polynomial from this kernel gives
the original polynomial. If the polynomial is normalized and nonnegative on
`[-1,1]`, the reconstructed kernel is admissible.

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
in `IsExtremalKernel`.

The formal proof then applies the inverse polynomial-to-kernel construction
to the weighted optimizer. Polynomial reconstruction proves that its symbol
is the optimizer, and the optimizer's degree, nonnegativity, and normalization
prove that the kernel is admissible. The equality characterization proves
attainment. Finally, supported symmetric kernels are determined by their
kernel polynomials, so any admissible kernel attaining the bound equals this
explicit kernel.

Finally, `JoseSmoothest/Challenge.lean` combines the exact Fourier norm, the
weighted polynomial theorem, coefficient reconstruction, and the inverse
kernel construction to prove the lower bound, equality characterization,
attainment, and uniqueness in Theorem 1.4.

## The sixth-order property-first extension

For six differences, the Fourier symbol contributes a cubic factor after the
same substitution `x = cos ξ`. The module `SixthOrder.lean` defines

```text
sup{|(1-x)³ p(x)| : -1 ≤ x ≤ 1}
```

and proves that the sixth-difference operator norm is eight times this cubic
weighted norm. It packages the expected optimizer properties into a
`CubicZeroPeakCertificate`: a global bound, an attained peak, and enough
strictly ordered nodes alternating between zero and the peak. From an exact
cubic factorization and this certificate, Lean proves the candidate's norm,
the sharp lower bound for every admissible polynomial, and uniqueness of the
equality case.

It also takes the Chebyshev coefficients of any such certified polynomial to
construct an admissible finite kernel. The exact factor-eight identity then
gives a conditional sixth-order lower bound, proves that this kernel attains
it, and proves that it is the unique admissible attaining kernel.

`Zolotarev.lean` performs the next layer rigorously. Its input is the actual
mathematical package asserted by Lebedev: real polynomials `Z` and `V`, the
correctly signed Pell--Abel identity, the differential equation
`Z' = N (X-1) V`, a nonzero endpoint scale, and the interval
equioscillation. Lean differentiates the Pell equation to prove `V(1)=0`,
proves the double criticality of `Z`, computes the third derivative, divides
`1-Z` by `(1-X)³`, and proves that the quotient has degree at most `N-3`, is
nonnegative, and equals one at the endpoint. It then constructs the literal
`CubicZeroPeakCertificate`. The resulting sixth-order constant is

```text
144 r² / N²,
```

Here `r` is an abstract input satisfying `H(1)=r²`. It is intended to be the
ratio `(1-cn(2a))/dn(2a)` from Theorem 1.7, but proving that identification is
part of the still-missing analytic construction.

This still does not manufacture the input polynomials. `JacobiTheta.lean`
fixes the theta-function normalization and defines the expressions appearing
in Lebedev's formula, while carefully making no unsupported claims about
their zeros, reality, or polynomiality. Completing the unconditional theorem
requires a new analytic library proving that the theta quotient descends to
the real polynomials `Z,V`, proving its Pell/differential identities and
unwrapped-phase equioscillation, and proving existence of `k_N`.

## Where the proof lives

- [`JoseSmoothest/Basic.lean`](JoseSmoothest/Basic.lean): `ℓ²(ℤ)`, finite
  kernels, and translation.
- [`JoseSmoothest/Kernel.lean`](JoseSmoothest/Kernel.lean): difference and
  averaging operators.
- [`JoseSmoothest/Fourier.lean`](JoseSmoothest/Fourier.lean): the exact
  Fourier multiplier/operator-norm identity.
- [`JoseSmoothest/Chebyshev.lean`](JoseSmoothest/Chebyshev.lean): the kernel
  polynomial, coefficient extraction, and inverse polynomial-to-kernel
  construction.
- [`JoseSmoothest/Alternation.lean`](JoseSmoothest/Alternation.lean): the
  alternating-sign polynomial uniqueness lemma.
- [`JoseSmoothest/WeightedExtremal.lean`](JoseSmoothest/WeightedExtremal.lean):
  Proposition 1.6 and its unique optimizer.
- [`JoseSmoothest/Challenge.lean`](JoseSmoothest/Challenge.lean): the
  sorry-free assembly of Theorem 1.4, including the unique attaining kernel.
- [`JoseSmoothest/SixthOrder.lean`](JoseSmoothest/SixthOrder.lean): the exact
  sixth-order norm reduction and property-first cubic extremal theorem.
- [`JoseSmoothest/JacobiTheta.lean`](JoseSmoothest/JacobiTheta.lean): the
  normalized theta expressions used by Lebedev's construction.
- [`JoseSmoothest/Zolotarev.lean`](JoseSmoothest/Zolotarev.lean): the
  Pell--Abel endpoint calculation, concrete certificate, paper constant, and
  conditional unique sixth-order optimizer.
- [`Showcase.lean`](Showcase.lean): the statement-only comparator interface.
- [`Solution.lean`](Solution.lean): the comparator solution linked to the
  full proof.

For declaration-by-declaration natural-language proofs, see the
[`blueprint/`](blueprint/) directory.

## What is trusted, and what the comparator adds

The public statement file and the internal theorem file have different jobs:

- the root [`Showcase.lean`](Showcase.lean) fixes the public statements to
  be checked. Its four theorem bodies are intentional `sorry` placeholders;
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
`IsAdmissibleKernel`, `iteratedDifferenceSmoothness`, and `IsExtremalKernel`
faithfully express the paper's mathematics. The public statements and this
explanation are intended to make that review possible.

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
