# Blueprint for `JoseSmoothest/Fourier.lean`

## Purpose

This module formalizes the exact Fourier-analytic identity used in equation
(3.3) of the paper.  It identifies the operator norm of four forward
differences after convolution with the supremum of the corresponding scalar
multiplier.  Exact equality, rather than only a pointwise lower bound, is
needed for the equality characterization in Theorem 1.4.

## Imports

```lean
import JoseSmoothest.Kernel
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.Count
```

## Public declarations

```lean
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace JoseSmoothest

/-- The real Fourier transform (symbol) of a symmetric finite kernel. -/
def kernelFourierTransform (u : Kernel) (ξ : ℝ) : ℝ :=
  u.sum fun k a ↦ a * Real.cos ((k : ℝ) * ξ)

/-- The four assumptions imposed on kernels in Theorem 1.4. -/
def IsAdmissibleKernel (n : ℕ) (u : Kernel) : Prop :=
  (∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0) ∧
  (∀ k : ℤ, u (-k) = u k) ∧
  u.sum (fun _ a ↦ a) = 1 ∧
  ∀ ξ : ℝ, 0 ≤ kernelFourierTransform u ξ

namespace IsAdmissibleKernel

/-- An admissible kernel vanishes outside `[-n, n]`. -/
theorem support {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0

/-- An admissible kernel is symmetric. -/
theorem symmetric {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    ∀ k : ℤ, u (-k) = u k

/-- The coefficients of an admissible kernel sum to one. -/
theorem sum_eq_one {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    u.sum (fun _ a ↦ a) = 1

/-- The Fourier transform of an admissible kernel is nonnegative. -/
theorem fourier_nonnegative {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    ∀ ξ : ℝ, 0 ≤ kernelFourierTransform u ξ

end IsAdmissibleKernel

/-- The operator norm of `∇⁴` after convolution by `u`. -/
def fourthOrderSmoothness (u : Kernel) : ℝ :=
  ‖(differenceOperator ^ 4).comp (averagingOperator u)‖

/-- The modulus of the fourth-order Fourier multiplier at frequency `ξ`. -/
def fourthOrderMultiplier (u : Kernel) (ξ : ℝ) : ℝ :=
  4 * (1 - Real.cos ξ) ^ 2 * |kernelFourierTransform u ξ|

/-- The supremum of the fourth-order multiplier over all real frequencies. -/
def fourthOrderMultiplierNorm (u : Kernel) : ℝ :=
  sSup {r : ℝ | ∃ ξ : ℝ, r = fourthOrderMultiplier u ξ}

/-- Equation (3.3): the operator norm equals the multiplier supremum. -/
theorem fourthOrderSmoothness_eq_multiplierNorm
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    fourthOrderSmoothness u = fourthOrderMultiplierNorm u

/-- Every frequency supplies a lower bound for the operator norm. -/
theorem fourthOrderMultiplier_le_smoothness
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (ξ : ℝ) :
    fourthOrderMultiplier u ξ ≤ fourthOrderSmoothness u

end JoseSmoothest
```

## Detailed proof blueprint

Write `Aᵤ = (differenceOperator ^ 4).comp (averagingOperator u)` for the real
fourth-order convolution operator.

### `kernelFourierTransform`

Because `u` is a `Finsupp`, `u.sum` is the finite sum over its support.  Give
the coefficient at `k` the cosine character `cos(kξ)` and add the terms.  The
result is real-valued.  Symmetry is not needed to define the expression; it
is the hypothesis that later identifies it with the full complex Fourier
symbol.

### `IsAdmissibleKernel`

Package the paper's four assumptions as a right-associated conjunction.  The
first conjunct is support in the integer interval `[-n, n]`; the second is
symmetry under `k ↦ -k`; the third normalizes the finite coefficient sum to
one; and the last requires the real Fourier transform to be nonnegative at
every real frequency.  This definition is a proposition and therefore
contains no additional computational data.

### The four `IsAdmissibleKernel` projections

The defining conjunction is nested as `support ∧ symmetry ∧ normalization ∧
nonnegativity`.  Therefore the four conclusions are respectively `h.1`,
`h.2.1`, `h.2.2.1`, and `h.2.2.2`.  These theorems expose stable dot notation,
so downstream proofs do not depend on the conjunction's internal nesting.

### `fourthOrderSmoothness`

Take the fourth power of the bounded forward-difference operator, compose it
with convolution by `u`, and take the continuous-linear-map operator norm.
This is exactly the left-hand quantity in equation (3.3); all boundedness is
already carried by the bundled operators.

### `fourthOrderMultiplier`

The Fourier multiplier of one forward difference has squared modulus
`2(1 - cos ξ)`.  Four differences therefore contribute
`4(1 - cos ξ)^2`.  Multiply this nonnegative factor by the absolute value of
the real kernel symbol.  The later symbol calculation proves that this
formula is precisely the modulus of the complex multiplier.

### `fourthOrderMultiplierNorm`

Form the set of all values `fourthOrderMultiplier u ξ` and take its real
supremum.  Using a range set rather than a function-space norm makes this
definition independent of periodicity.  Later, continuity on the compact
circle proves that the set is nonempty and bounded above and identifies this
supremum with the norm of a continuous circle symbol.

### Build the counting-measure Fourier equivalence

Mathlib's `fourierBasis` is a Hilbert basis of complex `L²` on a circle, but
the challenge uses `MeasureTheory.Lp ℂ 2 Measure.count` for sequences.  Build
the missing bridge privately.

Define `countDelta i` as the `L²` indicator of the singleton `{i}`.  The inner
product formula for singleton indicators proves orthonormality.  If `f` is
orthogonal to their span, testing against `countDelta i` and evaluating the
singleton integral gives `f i = 0` for every `i`.  Counting-measure
almost-everywhere extensionality then gives `f = 0`, so the orthogonal
complement is bottom.  Apply `HilbertBasis.mkOfOrthogonalEqBot` to obtain
`countHilbertBasis`.

At period `2π`, compose the representation map for this basis with the inverse
representation map for Mathlib's circle Fourier basis:

`sequenceFourierEquiv = countHilbertBasis.repr.trans fourierBasis.repr.symm`.

Both factors are linear isometries, hence their composite is a linear
isometric equivalence between complex sequence `L²` and circle `L²`.

### Prove the exact norm of circle multiplication

For a continuous circle function `m`, convert `m` to `L∞` and use Mathlib's
`Lp` scalar multiplication to define `circleMultiply m` on circle `L²`.
Hölder's estimate and the pointwise bound `‖m x‖ ≤ ‖m‖` give
`‖circleMultiply m‖ ≤ ‖m‖`.

For the reverse inequality, fix `x` and suppose the operator norm were
strictly smaller than `‖m x‖`.  Let `c` be the midpoint of these two numbers.
The set `U = {y | c < ‖m y‖}` is nonempty and open by continuity.  Haar measure
has full support, so `U` has positive measure; compactness makes its measure
finite.  Test multiplication on the `L²` indicator `f` of `U`.  Pointwise on
`U`, multiplication expands `f` by at least `c`, so
`c ‖f‖ ≤ ‖circleMultiply m‖ ‖f‖`.  Positivity of the measure gives
`0 < ‖f‖`, allowing cancellation and contradicting the choice of `c`.  Thus
`‖m x‖ ≤ ‖circleMultiply m‖` for every `x`; taking the supremum yields
equality.

### Intertwine translations and the circle symbol

Define complex translations, differences, and convolution exactly as in the
real setting.  Direct calculation on singleton indicators shows that
translation by `k` sends `countDelta i` to `countDelta (i + k)`.  The Fourier
equivalence sends those two basis vectors to `fourierLp 2 i` and
`fourierLp 2 (i + k)`, while circle multiplication by `fourier k` has the same
effect.  The span of the Hilbert basis is dense, so extensionality of
continuous linear maps extends the intertwining identity to every sequence.

Linearity and `Finsupp` induction then show that complex convolution by `u`
becomes multiplication by

`kernelCircleSymbol u = Σ k, u(k) • fourier k`.

Similarly, one difference becomes multiplication by `fourier (-1) - 1`, and
induction on the power makes four differences multiplication by its fourth
power.  Hence the complex version of `Aᵤ` is conjugate through
`sequenceFourierEquiv` to multiplication by

`fourthCircleSymbol u = (fourier (-1) - 1)^4 * kernelCircleSymbol u`.

Since the equivalence and its inverse preserve norms, applying the operator
norm bound in both directions proves that the complex operator norm is the
norm of this circle symbol.  The exact multiplication theorem changes no
constant in this identification.

### Return from complex to real sequences

Pointwise `Complex.ofReal` defines a norm-preserving real-linear embedding of
real counting-measure `L²` into complex `L²`.  Almost-everywhere pointwise
calculations show that it intertwines translations, differences, finite
convolution, and therefore the fourth-order operators.  Testing the complex
operator on embedded real inputs proves that the real operator norm is at
most the complex norm.

Conversely, decompose a complex input into the embedded real and imaginary
parts.  The operator has real coefficients, so it acts on the two components
separately.  The identity

`‖f‖² = ‖Re f‖² + ‖Im f‖²`

holds for both input and output.  Bound each output component by the real
operator norm, add the squared inequalities, and take square roots.  This
proves that the complex norm is at most the real norm, hence the two norms
are equal.

### Evaluate the circle symbol

At the real representative `ξ` of the circle,
`fourier k ξ = exp(I k ξ)`.  Reindex the finite kernel sum by `k ↦ -k` and
use symmetry to prove that complex conjugation fixes `kernelCircleSymbol u`.
It is therefore real, and its real part is the cosine sum
`kernelFourierTransform u ξ`.

The elementary complex-norm identity

`‖fourier (-1) ξ - 1‖² = 2(1 - cos ξ)`

then gives
`‖fourthCircleSymbol u ξ‖ = fourthOrderMultiplier u ξ`.  The multiplier
range is nonempty, using `ξ = 0`, and is bounded above by the continuous-map
norm.  For one inequality between that norm and the range supremum, lift an
arbitrary circle point to a real representative and use `le_csSup`; for the
other, use `csSup_le` and the pointwise continuous-map norm bound.  Thus
`‖fourthCircleSymbol u‖ = fourthOrderMultiplierNorm u`.

### `fourthOrderSmoothness_eq_multiplierNorm`

Unfold `fourthOrderSmoothness`.  The real/complex comparison replaces the
norm of `Aᵤ` by the norm of the complex fourth-order operator.  Fourier
intertwining and the exact multiplication norm replace that by
`‖fourthCircleSymbol u‖`.  Finally, the symbol evaluation identifies this with
`fourthOrderMultiplierNorm u`.  Chaining these three equalities proves
equation (3.3).

### `fourthOrderMultiplier_le_smoothness`

Rewrite the multiplier value as the pointwise norm of
`fourthCircleSymbol u` using symmetry.  It is at most the continuous-map norm
of that symbol.  The complex Fourier intertwining identifies this norm with
the complex fourth-order operator norm, and the real/complex comparison
identifies the latter with `fourthOrderSmoothness u`.  These rewrites followed
by the standard pointwise bound `m.norm_coe_le_norm` prove the result.
