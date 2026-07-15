# Blueprint for `JoseSmoothest/Fourier.lean`

## Purpose

This module proves the exact Fourier-analytic identity for every number of
forward differences after convolution.  The fourth-order specialization is
equation (3.3) of the paper, while the generic API also supplies the Fourier
reduction for the sixth-order theorem.  Exact equality, rather than only a
pointwise lower bound, is needed for the equality characterization in
Theorem 1.4.

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

/-- The operator norm of the `r`-fold forward difference after convolution by `u`. -/
def differenceSmoothness (r : ℕ) (u : Kernel) : ℝ :=
  ‖differenceAfterAveraging r u‖

/-- The modulus of the `r`-fold difference multiplier at frequency `ξ`. -/
def differenceMultiplier (r : ℕ) (u : Kernel) (ξ : ℝ) : ℝ :=
  Real.sqrt (2 * (1 - Real.cos ξ)) ^ r * |kernelFourierTransform u ξ|

/-- The supremum of the `r`-fold difference multiplier over all real frequencies. -/
def differenceMultiplierNorm (r : ℕ) (u : Kernel) : ℝ :=
  sSup {a : ℝ | ∃ ξ : ℝ, a = differenceMultiplier r u ξ}

/-- The operator norm of `∇⁴` after convolution by `u`. -/
def fourthOrderSmoothness (u : Kernel) : ℝ :=
  ‖(differenceOperator ^ 4).comp (averagingOperator u)‖

/-- The modulus of the fourth-order Fourier multiplier at frequency `ξ`. -/
def fourthOrderMultiplier (u : Kernel) (ξ : ℝ) : ℝ :=
  4 * (1 - Real.cos ξ) ^ 2 * |kernelFourierTransform u ξ|

/-- The supremum of the fourth-order multiplier over all real frequencies. -/
def fourthOrderMultiplierNorm (u : Kernel) : ℝ :=
  sSup {r : ℝ | ∃ ξ : ℝ, r = fourthOrderMultiplier u ξ}

/-- The generic smoothness at order four is the original fourth-order quantity. -/
@[simp]
theorem differenceSmoothness_four (u : Kernel) :
    differenceSmoothness 4 u = fourthOrderSmoothness u

/-- At even order `2 * m`, the difference weight is a polynomial in `cos ξ`. -/
theorem differenceMultiplier_two_mul (m : ℕ) (u : Kernel) (ξ : ℝ) :
    differenceMultiplier (2 * m) u ξ =
      (2 * (1 - Real.cos ξ)) ^ m * |kernelFourierTransform u ξ|

/-- The generic multiplier at order four is the original fourth-order multiplier. -/
@[simp]
theorem differenceMultiplier_four (u : Kernel) (ξ : ℝ) :
    differenceMultiplier 4 u ξ = fourthOrderMultiplier u ξ

/-- At order six, the difference weight is `8 * (1 - cos ξ) ^ 3`. -/
@[simp]
theorem differenceMultiplier_six (u : Kernel) (ξ : ℝ) :
    differenceMultiplier 6 u ξ =
      8 * (1 - Real.cos ξ) ^ 3 * |kernelFourierTransform u ξ|

/-- The generic multiplier supremum at order four is the original one. -/
@[simp]
theorem differenceMultiplierNorm_four (u : Kernel) :
    differenceMultiplierNorm 4 u = fourthOrderMultiplierNorm u

/-- The norm of the `r`-fold difference after averaging equals its multiplier supremum. -/
theorem differenceSmoothness_eq_multiplierNorm
    (r : ℕ)
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    differenceSmoothness r u = differenceMultiplierNorm r u

/-- Every frequency supplies a lower bound for the iterated-difference operator norm. -/
theorem differenceMultiplier_le_smoothness
    (r : ℕ)
    (u : Kernel)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (ξ : ℝ) :
    differenceMultiplier r u ξ ≤ differenceSmoothness r u

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

Write `Aᵣ,ᵤ = differenceAfterAveraging r u` for the real order-`r`
convolution-difference operator.

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

### `differenceSmoothness`

The preceding module bundles `Aᵣ,ᵤ` as a continuous linear map.  Its operator
norm is therefore already a real number, and this definition simply records
that norm.  No positivity or symmetry assumption on the kernel is needed to
form it.

### `differenceMultiplier`

One forward difference has complex Fourier symbol `exp(-Iξ) - 1`.  The square
of its modulus is `2(1 - cos ξ)`, so its modulus is the nonnegative square
root `sqrt(2(1 - cos ξ))`.  Raising this modulus to `r` accounts for the
`r`-fold difference.  For a symmetric real kernel, the modulus of its complex
symbol is `|kernelFourierTransform u ξ|`; multiplying the two factors gives
the scalar multiplier modulus.

The square-root formulation is valid for odd and even `r`.  In particular,
it avoids the incorrect use of natural-number division in an expression such
as `(2(1 - cos ξ))^(r / 2)`.

### `differenceMultiplierNorm`

Take the real supremum of the range of `differenceMultiplier r u`.  The range
is later shown to be nonempty and bounded by identifying it pointwise with
the norm of a continuous function on the compact circle.

### `fourthOrderSmoothness`

Take the fourth power of the bounded forward-difference operator, compose it
with convolution by `u`, and take the continuous-linear-map operator norm.
This is exactly the left-hand quantity in equation (3.3).  The theorem
`differenceSmoothness_four` later proves that it is the `r = 4`
specialization of the generic definition.

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

Similarly, one difference becomes multiplication by `fourier (-1) - 1`.
Induction on `r` shows that the `r`-fold difference becomes multiplication by
its `r`th power.  Hence the complex version of `Aᵣ,ᵤ` is conjugate through
`sequenceFourierEquiv` to multiplication by

`orderCircleSymbol r u = (fourier (-1) - 1)^r * kernelCircleSymbol u`.

Since the equivalence and its inverse preserve norms, applying the operator
norm bound in both directions proves that the complex operator norm is the
norm of this circle symbol.  The exact multiplication theorem changes no
constant in this identification.

### Return from complex to real sequences

Pointwise `Complex.ofReal` defines a norm-preserving real-linear embedding of
real counting-measure `L²` into complex `L²`.  Almost-everywhere pointwise
calculations show that it intertwines translations, differences, every
power of the difference operator, and finite convolution.  Testing the
complex order-`r` operator on embedded real inputs proves that the real
operator norm is at most the complex norm.

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

and nonnegativity of a norm give

`‖fourier (-1) ξ - 1‖ = sqrt(2(1 - cos ξ))`

through `Real.sqrt_sq`.  Taking the `r`th power and multiplying by the kernel
symbol norm proves

`‖orderCircleSymbol r u ξ‖ = differenceMultiplier r u ξ`.

The multiplier range is nonempty, using `ξ = 0`, and is bounded above by the
continuous-map norm.  For one inequality between that norm and the range
supremum, lift an arbitrary circle point to a real representative and use
`le_csSup`; for the other, use `csSup_le` and the pointwise continuous-map
norm bound.  Thus

`‖orderCircleSymbol r u‖ = differenceMultiplierNorm r u`.

### `differenceSmoothness_four`

Unfold `differenceSmoothness`, `differenceAfterAveraging`, and
`fourthOrderSmoothness`.  Both sides reduce definitionally to the norm of
`(differenceOperator ^ 4).comp (averagingOperator u)`, so reflexivity proves
the equality.  The `[simp]` attribute makes the legacy fourth-order API a
convenient normal form.

### `differenceMultiplier_two_mul`

Set `x = 2(1 - cos ξ)`.  Since `cos ξ ≤ 1`, one has `0 ≤ x`.  Use
`pow_mul` to rewrite `(sqrt x)^(2m)` as `((sqrt x)^2)^m`, then use
`Real.sq_sqrt` to replace `(sqrt x)^2` by `x`.  The kernel-symbol absolute
value is unchanged, giving the stated polynomial formula for every even
order.

### `differenceMultiplier_four`

Specialize `differenceMultiplier_two_mul` to `m = 2`.  Ring normalization
changes `(2(1 - cos ξ))^2` into `4(1 - cos ξ)^2`, exactly the defining
formula for `fourthOrderMultiplier`.  Mark the result as a simplification
lemma for backward compatibility.

### `differenceMultiplier_six`

Specialize `differenceMultiplier_two_mul` to `m = 3`.  Expanding the scalar
power of two gives `2^3 = 8`, hence the order-six weight is
`8(1 - cos ξ)^3`.  This is the Fourier weight needed to reduce the paper's
sixth-order theorem to its cubic weighted-polynomial problem.

### `differenceMultiplierNorm_four`

Unfold both supremum definitions.  The preceding pointwise order-four
identity rewrites every witness in the generic range to the corresponding
`fourthOrderMultiplier` value.  The two sets are therefore definitionally
equal after simplification, and their suprema agree.

### `differenceSmoothness_eq_multiplierNorm`

Unfold `differenceSmoothness`.  The real/complex comparison replaces
`‖Aᵣ,ᵤ‖` by the norm of `complexOrderOperator r u`.  Fourier intertwining and
the exact multiplication norm replace this with `‖orderCircleSymbol r u‖`.
The circle-symbol supremum calculation then gives
`differenceMultiplierNorm r u`.  Chaining these three equalities proves the
generic norm identity.

### `differenceMultiplier_le_smoothness`

Rewrite the multiplier value as the pointwise norm of
`orderCircleSymbol r u` using symmetry.  A continuous function's pointwise
norm is at most its uniform norm.  Fourier intertwining identifies that norm
with the complex order-`r` operator norm, and the real/complex comparison
identifies the latter with `differenceSmoothness r u`.

### `fourthOrderSmoothness_eq_multiplierNorm`

Rewrite the left side backwards with `differenceSmoothness_four` and the
right side backwards with `differenceMultiplierNorm_four`.  Apply
`differenceSmoothness_eq_multiplierNorm` at `r = 4`.  This recovers equation
(3.3) entirely from the generic theorem while preserving its original public
statement.

### `fourthOrderMultiplier_le_smoothness`

Rewrite both sides backwards with `differenceMultiplier_four` and
`differenceSmoothness_four`.  The generic pointwise theorem at `r = 4` then
proves the legacy fourth-order inequality directly.
