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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

/-- The Chebyshev polynomial `Tₘ`, evaluated at `x`. -/
def chebyshevT (m : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ m).eval x

/-- The Chebyshev polynomial associated to a kernel supported in `[-n,n]`. -/
def kernelPolynomial (n : ℕ) (u : Kernel) : ℝ[X] :=
  C (u 0) +
    ∑ k ∈ Finset.Icc 1 n,
      C (2 * u (k : ℤ)) * Polynomial.Chebyshev.T ℝ k

theorem kernelPolynomial_natDegree_le (n : ℕ) (u : Kernel) :
    (kernelPolynomial n u).natDegree ≤ n

theorem kernelPolynomial_eval_cos
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (ξ : ℝ) :
    (kernelPolynomial n u).eval (Real.cos ξ) = kernelFourierTransform u ξ

theorem kernelPolynomial_eval_one
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k)
    (normalized : u.sum (fun _ a ↦ a) = 1) :
    (kernelPolynomial n u).eval 1 = 1

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

theorem chebyshevCoefficient_kernelPolynomial
    (n m : ℕ)
    (hm : m ≤ n)
    (u : Kernel) :
    chebyshevCoefficient (kernelPolynomial n u) m = u m

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

### `kernelPolynomial_natDegree_le`

Each summand is a scalar multiple of `T_k`.  Use
`Polynomial.Chebyshev.natDegree_T`, `natDegree_C_mul_le`, and
`natDegree_sum_le_of_forall_le`; membership in `Icc 1 n` supplies `k≤n`.
The constant term also has degree at most `n`.

### `kernelPolynomial_eval_cos`

Evaluate the finite polynomial sum and rewrite
`Polynomial.Chebyshev.T_real_cos`.  Express the `Finsupp.sum` defining the
kernel symbol as a sum over `u.support`, discard indices outside `[-n,n]`
using `support`, split the interval into zero/positive/negative parts, and
reindex the negative part by `k↦-k`.  Symmetry and cosine evenness combine the
two nonzero terms into `2*u(k)*cos(kξ)`, exactly the evaluated kernel
polynomial.

### Normalization and nonnegativity

For `kernelPolynomial_eval_one`, specialize the cosine identity at `ξ=0` and
rewrite the Fourier sum using `normalized`.

For nonnegativity, take `ξ=arccos x`.  Membership of `x` in `[-1,1]` gives
`cos(arccos x)=x`; the evaluation identity and `fourier_nonnegative ξ` finish.

### Multiplier norm versus weighted polynomial norm

After `kernelPolynomial_eval_cos`, the multiplier is

`4 * |(1-cos ξ)^2 * p(cos ξ)|`.

Show equality of the two `sSup` values by proving equality of their underlying
ranges up to multiplication by four.  One direction maps `ξ` to `cos ξ`.
The other maps `x∈[-1,1]` to `arccos x`.  Both sets are nonempty and bounded
because polynomial evaluation is continuous on the compact interval; apply
the order lemmas for `csSup` and commute the positive scalar four with the
supremum.

### `chebyshevCoefficient_kernelPolynomial`

Privately turn Mathlib's Chebyshev polynomial sequence into the basis
`chebyshevBasis`.  For each `m`, define the linear functional

```text
p ↦ ∫ p(x) T_m(x) ∂measureT.
```

The Chebyshev orthogonality theorems compute this functional on every basis
element: its value is zero away from `m`, is `π` at `m=0`, and is `π/2` at
a positive `m`.  Linearity and `Basis.ext` therefore identify it on an
arbitrary polynomial with `π` times the `m`-th basis coordinate at zero and
`π/2` times that coordinate otherwise.  The theorem `integral_measureT`
then rewrites the functional as the interval integral divided by
`sqrt(1-x²)`, giving

```text
chebyshevCoefficient p m =
  if m=0 then coord_m(p) else coord_m(p)/2.
```

Rewrite `kernelPolynomial` in this basis.  Its zeroth coordinate is `u(0)`,
and for `1≤m≤n` its `m`-th coordinate is `2u(m)`.  Substitution into the
coordinate formula returns `u(m)` in both cases.  Integrability of the
auxiliary functional follows from `integrable_measureT`, since polynomial
evaluation is continuous.

### `polynomial_eq_of_chebyshevCoefficient_eq`

Apply extensionality for `chebyshevBasis`.  At an index `m≤n`, the coefficient
hypothesis and the displayed coefficient-to-coordinate formula imply that
the `m`-th basis coordinates of `p` and `q` agree (separating `m=0` from the
positive case).  At an index `m>n`, use
`Polynomial.Chebyshev.chebyshevTsequence.span_degreeLE`: each polynomial of
degree at most `n` lies in the span of the basis elements indexed by
`Set.Iic n`.  `Basis.repr_support_subset_of_mem_span` then says that its
`m`-th coordinate vanishes.  Thus every coordinate of `p` and `q` agrees,
and basis extensionality gives `p=q`.
