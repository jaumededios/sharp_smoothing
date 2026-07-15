# Blueprint for `JoseSmoothest/Chebyshev.lean`

## Purpose

This module converts a symmetric finite kernel into a polynomial on
`[-1,1]`, transports the Fourier multiplier norm to the weighted polynomial
norm, and formalizes Chebyshev coefficient extraction with the arcsine weight.
The coefficient theorem is the bridge from equality of extremal polynomials
to the integral formula (1.6) for the unique kernel.

## Imports

```lean
import JoseSmoothest.Fourier
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial
open MeasureTheory Module

/-- The Chebyshev polynomial `T_m`, evaluated at `x`. -/
def chebyshevT (m : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ m).eval x

/-- The Chebyshev polynomial associated to a kernel supported in `[-n,n]`. -/
def kernelPolynomial (n : ℕ) (u : Kernel) : ℝ[X] :=
  C (u 0) +
    ∑ k ∈ Finset.Icc 1 n,
      C (2 * u (k : ℤ)) * Polynomial.Chebyshev.T ℝ k

/-- The polynomial associated to a kernel supported in `[-n, n]` has degree at most `n`. -/
theorem kernelPolynomial_natDegree_le (n : ℕ) (u : Kernel) :
    (kernelPolynomial n u).natDegree ≤ n

/-- Evaluating the kernel polynomial at `cos ξ` gives the Fourier transform of the kernel. -/
theorem kernelPolynomial_eval_cos
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (ξ : ℝ) :
    (kernelPolynomial n u).eval (Real.cos ξ) = kernelFourierTransform u ξ

/-- A normalized kernel gives a kernel polynomial whose value at `1` is `1`. -/
theorem kernelPolynomial_eval_one
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (normalized : u.sum (fun _ a ↦ a) = 1) :
    (kernelPolynomial n u).eval 1 = 1

/-- A kernel with nonnegative Fourier transform gives a polynomial nonnegative on `[-1, 1]`. -/
theorem kernelPolynomial_nonnegative_on_Icc
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (fourier_nonnegative : ∀ ξ : ℝ, 0 ≤ kernelFourierTransform u ξ) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ (kernelPolynomial n u).eval x

/-- The weighted norm appearing in Proposition 1.6. -/
def weightedPolynomialNorm (p : ℝ[X]) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    r = |(1 - x) ^ 2 * p.eval x|}

/-- Equation (3.3) after the substitution `x=cos ξ`. -/
theorem fourthOrderMultiplierNorm_eq_four_mul_weightedPolynomialNorm
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    fourthOrderMultiplierNorm u =
      4 * weightedPolynomialNorm (kernelPolynomial n u)

/-- The `m`-th Chebyshev coefficient in the normalization of (1.6). -/
def chebyshevCoefficient (p : ℝ[X]) (m : ℕ) : ℝ :=
  1 / Real.pi *
    ∫ x in (-1 : ℝ)..1,
      p.eval x * chebyshevT m x / Real.sqrt (1 - x ^ 2)

/-- The `m`-th Chebyshev coefficient of a kernel polynomial is its kernel coefficient. -/
theorem chebyshevCoefficient_kernelPolynomial
    (n m : ℕ)
    (hm : m ≤ n)
    (u : Kernel) :
    chebyshevCoefficient (kernelPolynomial n u) m = u m

/-- Two polynomials of degree at most `n` are equal when their first `n + 1`
Chebyshev coefficients agree. -/
theorem polynomial_eq_of_chebyshevCoefficient_eq
    {n : ℕ}
    {p q : ℝ[X]}
    (hp : p.natDegree ≤ n)
    (hq : q.natDegree ≤ n)
    (hcoeff : ∀ m ≤ n,
      chebyshevCoefficient p m = chebyshevCoefficient q m) :
    p = q

end JoseSmoothest
```

## Detailed proof blueprint

### `chebyshevT`

This definition is the evaluation map for Mathlib's first-kind Chebyshev
polynomial `Polynomial.Chebyshev.T ℝ m`.  It introduces no new mathematical
content; the wrapper keeps later integral formulas readable while retaining
access to Mathlib's recurrence, degree, and trigonometric evaluation lemmas.

### `kernelPolynomial`

The constant coefficient is the central kernel value `u 0`.  For each
positive index `k` in `1, …, n`, symmetry combines the coefficients at `k`
and `-k`, producing the factor `2 * u k` multiplying `T_k`.  The finite
`Finset.Icc` sum therefore gives exactly the polynomial symbol of a symmetric
kernel supported on `[-n, n]`.

### `kernelPolynomial_natDegree_le`

Unfold `kernelPolynomial` and bound the natural degree of an addition by the
maximum of the degrees of its two terms.  The constant term has degree zero,
so it is bounded by `n`.  Apply `natDegree_sum_le_of_forall_le` to the finite
sum.  For an index `k` in `Finset.Icc 1 n`, use `natDegree_mul_le`,
`natDegree_C`, and `Polynomial.Chebyshev.natDegree_T` to bound the summand's
degree by `k`; interval membership supplies `k ≤ n`.  Transitivity gives the
required bound for every summand and hence for the whole polynomial.

### `kernelPolynomial_eval_cos`

Set `f k = u k * cos(kξ)`.  Kernel symmetry and cosine evenness prove that
`f` is even.  The support hypothesis implies that the `Finsupp` support of
`u` is contained in the integer interval `[-n, n]`, so
`Finsupp.sum_of_support_subset` rewrites `kernelFourierTransform u ξ` as the
sum of `f` over that interval.

Evaluate `kernelPolynomial` at `cos ξ`, distribute evaluation through the
finite sum with `eval_finsetSum`, and rewrite each Chebyshev value using
`Polynomial.Chebyshev.T_real_cos`.  A private reindexing lemma identifies
the positive interval `1, …, n` with `Finset.range n` shifted by one.
`Finset.sum_Icc_of_even_eq_range` then pairs `k` with `-k`, while
`Finset.sum_range_succ'` separates the zero term.  Ring normalization and
`Finset.sum_mul` show that the paired terms are precisely the coefficients
`2 * u k` in the evaluated kernel polynomial.

### `kernelPolynomial_eval_one`

Specialize `kernelPolynomial_eval_cos` to `ξ = 0` and rewrite
`Real.cos_zero`.  Unfold `kernelFourierTransform`; each argument
`(k : ℝ) * 0` becomes zero and every cosine factor becomes one, leaving exactly
`u.sum (fun _ a ↦ a)`.  The normalization hypothesis identifies this sum
with `1`.

### `kernelPolynomial_nonnegative_on_Icc`

Fix `x ∈ [-1, 1]` and take `ξ = Real.arccos x`.  The endpoint inequalities
from membership in the interval give `Real.cos (Real.arccos x) = x`.
Rewrite the polynomial evaluation with this identity and then apply
`kernelPolynomial_eval_cos`.  The goal becomes nonnegativity of
`kernelFourierTransform u (Real.arccos x)`, which is exactly the supplied
Fourier nonnegativity hypothesis.

### `weightedPolynomialNorm`

This definition takes the supremum of the image of the compact interval
`[-1, 1]` under `x ↦ |(1 - x)^2 p(x)|`.  Private supporting lemmas show that
the range is nonempty by evaluating at zero and is bounded above because the
displayed function is continuous and a continuous image of a compact set is
bounded.

### `fourthOrderMultiplierNorm_eq_four_mul_weightedPolynomialNorm`

Let `p = kernelPolynomial n u`, let `A` be the range of
`fourthOrderMultiplier u`, and let `B` be the weighted polynomial range in
the definition of `weightedPolynomialNorm p`.  First use
`kernelPolynomial_eval_cos` and nonnegativity of a square to prove the
pointwise identity

```text
fourthOrderMultiplier u ξ = 4 * |(1 - cos ξ)^2 * p(cos ξ)|.
```

The range `B` is nonempty and bounded by the private compactness lemmas.  Its
upper bound, multiplied by four, bounds `A` because `cos ξ ∈ [-1, 1]`; `A` is
also nonempty by taking `ξ = 0`.

For `sSup A ≤ 4 * sSup B`, apply `csSup_le` to `A`, rewrite each element with
the pointwise identity, and bound its polynomial value by `le_csSup` in `B`.
For the reverse inequality, apply `csSup_le` to `B`.  Given
`x ∈ [-1, 1]`, the frequency `Real.arccos x` lies in `A`, and
`Real.cos_arccos` converts the resulting `le_csSup` inequality into
`4 * |(1 - x)^2 p(x)| ≤ sSup A`.  Division by the positive scalar four and
linear arithmetic finish the two-sided comparison.

### `chebyshevCoefficient`

This definition uses the classical first-kind Chebyshev weight
`1 / sqrt (1 - x^2)` on `[-1, 1]` and the paper's common prefactor `1 / π`.
Consequently the coefficient of `T_0` is its usual basis coordinate, whereas
the coefficient of `T_m` for positive `m` is half its basis coordinate.  The
next theorem proves and uses this normalization through private basis lemmas.

### `chebyshevCoefficient_kernelPolynomial`

Privately turn Mathlib's Chebyshev polynomial sequence into the basis
`chebyshevBasis`.  For each `m`, define the linear functional

```text
p ↦ ∫ p(x) T_m(x) ∂measureT.
```

The Chebyshev orthogonality theorems compute this functional on every basis
element: its value is zero away from `m`, is `π` at `m = 0`, and is `π / 2`
at a positive `m`.  Polynomial evaluation is continuous, so
`integrable_measureT` supplies the integrability obligations needed for the
linear map.  Linearity and `Basis.ext` identify it on an arbitrary polynomial
with `π` times the `m`-th basis coordinate at zero and `π / 2` times that
coordinate otherwise.  The theorem `integral_measureT` rewrites the
functional as the weighted interval integral, giving

```text
chebyshevCoefficient p m =
  if m=0 then coord_m(p) else coord_m(p)/2.
```

Rewrite `kernelPolynomial` in this basis.  If `m = 0`, the zeroth basis
coordinate of every summand indexed by `1, …, n` vanishes, leaving `u 0`.
If `m ≠ 0`, the bound `m ≤ n` puts `m` in `Finset.Icc 1 n`; basis-coordinate
evaluation selects its unique summand and returns `2 * u m`.  Substitution
into the coordinate formula returns `u m` in both cases.

### `polynomial_eq_of_chebyshevCoefficient_eq`

Apply extensionality for `chebyshevBasis`.  At an index `m ≤ n`, the coefficient
hypothesis and the displayed coefficient-to-coordinate formula imply that
the `m`-th basis coordinates of `p` and `q` agree (separating `m=0` from the
positive case).  At an index `m > n`, use
`Polynomial.Chebyshev.chebyshevTsequence.span_degreeLE`: each polynomial of
degree at most `n` lies in the span of the basis elements indexed by
`Set.Iic n`.  `Basis.repr_support_subset_of_mem_span` then says that its
`m`-th coordinate vanishes.  Thus every coordinate of `p` and `q` agrees,
and basis extensionality gives `p = q`.
