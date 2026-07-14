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

Write `A = (differenceOperator ^ 4).comp (averagingOperator u)`.

### 1. Build the missing counting-measure Fourier equivalence

Mathlib's `fourierBasis` is a Hilbert basis of complex `L²` on a circle, and
its representation space is sequence `lp`.  The challenge's sequence type is
instead `MeasureTheory.Lp ℂ 2 Measure.count`; Mathlib deliberately has no
equivalence between these two sequence presentations.

Privately define

`countDelta i = indicatorConstLp 2 {i} 1 : Lp ℂ 2 Measure.count`.

Use `L2.inner_indicatorConstLp_one_indicatorConstLp_one` to prove that these
vectors are orthonormal.  To prove completeness, let `f` be orthogonal to
every `countDelta i`; the inner-product formula and `integral_singleton` give
`f i=0` for every integer.  `Measure.ae_count_iff` and `Lp.ext` then give
`f=0`.  Construct `countHilbertBasis` with
`HilbertBasis.mkOfOrthogonalEqBot`.

At circle period `2π`, define the private linear isometric equivalence

`sequenceFourierEquiv = countHilbertBasis.repr.trans fourierBasis.repr.symm`.

This construction has already been checked against Mathlib v4.32.0: the
singleton family, its orthogonal-complement proof, the Hilbert basis, and the
composition of representation maps all elaborate.

### 2. Identify the complex Fourier symbol

Define complex translations and the complex analogues of convolution and
`A`.  Under the convention supplied by `sequenceFourierEquiv`, translation
by `k` becomes multiplication by `exp(I*k*ξ)`.  Hence the complex multiplier
is

`λ(ξ) = (exp(-I*ξ)-1)^4 * Σ_k u(k) exp(I*k*ξ)`.

Prove this first for the singleton basis.  Linearity gives it on finite
linear combinations, and density of the Hilbert-basis span plus continuity
extends it to all of complex counting-measure `L²`.

Pair `k` with `-k` using `symmetric`.  Euler's identity cancels the imaginary
parts and identifies the finite sum with `kernelFourierTransform u ξ`.  The
identity

`‖exp(-I*ξ)-1‖² = 2(1-cos ξ)`

then yields `‖λ(ξ)‖ = fourthOrderMultiplier u ξ`.

### 3. Exact norm of multiplication on circle `L²`

The multiplier is a continuous `2π`-periodic function.  Use its lift to
`AddCircle (2π)` and define multiplication on `L²`; Mathlib's Holder estimate
gives the upper bound by `fourthOrderMultiplierNorm u`.

For the reverse bound at a fixed frequency `ξ`, continuity gives a small open
arc on which the modulus is within `ε` of `‖λ(ξ)‖`.  Haar measure assigns this
arc positive finite measure.  Apply the multiplication operator to the
normalized `L²` indicator of the arc.  The lower pointwise bound integrates
to an operator amplification of at least `‖λ(ξ)‖-ε`; let `ε↓0`.  This is the
formal version of the localized Fourier test functions used in the paper.

The range defining `fourthOrderMultiplierNorm` is nonempty and bounded: its
function is continuous and periodic, and it also has a direct finite-sum
bound.  These facts justify `le_csSup`, `csSup_le`, and passage from the
pointwise lower bounds to equality of norms.

### 4. Return from complex to real sequences

Pointwise `Complex.ofReal` gives a norm-preserving embedding of real
counting-measure `L²` into complex `L²` and intertwines every translation,
difference, and real-kernel convolution.  This immediately bounds the real
operator norm by the complex one.

Conversely, split an arbitrary complex input into its real and imaginary
parts.  The operator has real coefficients, so it acts componentwise, while
both the input and output squared norms are sums of the corresponding real
and imaginary squared norms.  Bounding each component by the real operator
norm proves that the complex norm is no larger.  Thus the real and complex
operator norms coincide.

Combining this equality with the exact multiplication norm proves
`fourthOrderSmoothness_eq_multiplierNorm`.  The fixed-frequency part of the
localized-indicator argument also directly gives
`fourthOrderMultiplier_le_smoothness`.

### `fourthOrderMultiplier_le_smoothness`

Rewrite the right-hand side with the norm identity.  The multiplier value is
in the range used to define `fourthOrderMultiplierNorm`, so `le_csSup` gives
the result using the boundedness established above.
