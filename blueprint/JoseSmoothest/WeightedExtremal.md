# Blueprint for `JoseSmoothest/WeightedExtremal.lean`

## Purpose

This module formalizes Proposition 1.6, including its equality
characterization.  It constructs the transformed Chebyshev optimizer as an
actual polynomial, proves the sharp weighted norm bound, and connects its
evaluation formula and constant to the notation in Theorem 1.4.

## Imports

```lean
import JoseSmoothest.Alternation
import JoseSmoothest.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

/-- The sharp constant in Proposition 1.6. -/
def weightedChebyshevConstant (N : ℕ) : ℝ :=
  16 / (N : ℝ) ^ 2 * Real.tan (Real.pi / (2 * (N : ℝ))) ^ 2

/-- The affine argument used to transform `T_N`. -/
def affineChebyshevArgument (N : ℕ) : ℝ[X] :=
  C ((1 + Real.cos (Real.pi / (N : ℝ))) / 2) * (X + 1) - 1

/-- The numerator `(8/N²)tan²(π/2N) * (1 + T_N(L(X)))`. -/
def transformedChebyshevPolynomial (N : ℕ) : ℝ[X] :=
  C (8 / (N : ℝ) ^ 2 * Real.tan (Real.pi / (2 * (N : ℝ))) ^ 2) *
    (1 + (Polynomial.Chebyshev.T ℝ N).comp
      (affineChebyshevArgument N))

/-- The polynomial optimizer `S_{N-2}` from equation (1.8). -/
def weightedExtremalPolynomial (N : ℕ) : ℝ[X] :=
  transformedChebyshevPolynomial N / (C 1 - X) ^ 2

theorem weightedChebyshevConstant_nonneg (N : ℕ) :
    0 ≤ weightedChebyshevConstant N

theorem weightedExtremalPolynomial_eval_one
    (N : ℕ) (hN : 2 ≤ N) :
    (weightedExtremalPolynomial N).eval 1 = 1

theorem weightedExtremalPolynomial_natDegree_le
    (N : ℕ) (hN : 2 ≤ N) :
    (weightedExtremalPolynomial N).natDegree ≤ N - 2

theorem weightedExtremalPolynomial_nonnegative
    (N : ℕ) (hN : 2 ≤ N) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ (weightedExtremalPolynomial N).eval x

theorem weightedExtremalPolynomial_norm
    (N : ℕ) (hN : 2 ≤ N) :
    weightedPolynomialNorm (weightedExtremalPolynomial N) =
      weightedChebyshevConstant N

/-- The sharp constant in Theorem 1.4. -/
def sharpConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 6 / ((n : ℝ) + 2) ^ 2 *
    Real.tan (Real.pi / (2 * (n : ℝ) + 4)) ^ 2

/-- The pointwise formula for `S_n`, with its removable singularity filled. -/
def extremalPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  if x = 1 then
    1
  else
    8 / ((n : ℝ) + 2) ^ 2 *
      Real.tan (Real.pi / (2 * (n : ℝ) + 4)) ^ 2 /
      (1 - x) ^ 2 *
      (1 + chebyshevT (n + 2)
        (((1 + Real.cos (Real.pi / ((n : ℝ) + 2))) / 2) *
          (x + 1) - 1))

theorem sharpConstant_eq_four_mul_weightedChebyshevConstant (n : ℕ) :
    sharpConstant n = 4 * weightedChebyshevConstant (n + 2)

theorem weightedExtremalPolynomial_eval (n : ℕ) (x : ℝ) :
    (weightedExtremalPolynomial (n + 2)).eval x =
      extremalPolynomial n x

/-- Proposition 1.6, sharp inequality. -/
theorem weightedPolynomialNorm_ge
    (N : ℕ)
    (hN : 2 ≤ N)
    (p : ℝ[X])
    (hdeg : p.natDegree ≤ N - 2)
    (hnonneg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x)
    (hone : p.eval 1 = 1) :
    weightedChebyshevConstant N ≤ weightedPolynomialNorm p

/-- Proposition 1.6, uniqueness of the equality case. -/
theorem weightedPolynomialNorm_eq_iff
    (N : ℕ)
    (hN : 2 ≤ N)
    (p : ℝ[X])
    (hdeg : p.natDegree ≤ N - 2)
    (hnonneg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x)
    (hone : p.eval 1 = 1) :
    weightedPolynomialNorm p = weightedChebyshevConstant N ↔
      p = weightedExtremalPolynomial N

end JoseSmoothest
```

## Detailed proof blueprint

### The transformed polynomial and its double zero

Fix `N≥2`, put `c=cos(π/N)`, and let `L` be the polynomial represented by
`affineChebyshevArgument N`.  Its evaluation maps `[-1,1]` onto `[-1,c]`.
Mathlib's `abs_eval_T_real_le_one` therefore shows
`0 ≤ 1+T_N(L(x)) ≤ 2` on the interval.

Let `q=transformedChebyshevPolynomial N`.  At `x=1`, `L(1)=c` and
`T_N(c)=cos π=-1`.  Moreover `T'_N(c)=0`, using
`T_derivative_eq_U` and `U_real_cos`.  Hence `q(1)=q'(1)=0`, so
`(C 1-X)^2 ∣ q`.  Polynomial division by this monic-up-to-a-unit factor is
therefore exact; this proves the defining quotient really is a polynomial
`S_{N-2}` and gives the degree bound.

Evaluate Mathlib's Chebyshev differential equation
`one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T` at `c`.  Since
`T_N(c)=-1` and `T'_N(c)=0`, it gives
`T''_N(c)=N²/sin²(π/N)`.  The chain rule and the half-angle identity imply
`q''(1)=2`.  Since `q=(1-X)^2 S`, the product rule gives `S(1)=1`.

For `x≠1`, exact division yields

`S(x) = (8/N²)tan²(π/2N) * (1+T_N(L(x))) / (1-x)²`.

This proves nonnegativity.  It also proves
`weightedExtremalPolynomial_eval`; at `x=1` use the normalization, and away
from one simplify the quotient and casts with `field_simp` and `ring`.

### Norm of the optimizer

Multiplying the displayed formula by `(1-x)²` recovers `q(x)`.  The Chebyshev
bound gives `|q(x)|≤2α`, where
`α=(8/N²)tan²(π/2N)`.  At the inverse image of the node
`cos(2π/N)` (or at `x=-1` when `N=2`) the value is `2α`.  Compactness and the
`csSup` characterization of `weightedPolynomialNorm` then give equality with
`2α = weightedChebyshevConstant N`.

### Alternation and uniqueness

Handle `N=2` separately: the degree condition forces `p` to be the constant
one polynomial, which is the optimizer.

Assume now `3≤N` and suppose `p` satisfies all hypotheses and has weighted
norm at most the sharp constant.  Since `p(1)=S(1)=1`, factor

`p-S = (1-X)r`, with `r.natDegree≤N-3`.

At the `N-1` transformed Chebyshev nodes corresponding to indices
`N,N-1,…,2`, the numerator `q=(1-X)²S` alternates between zero and `2α`.
Nonnegativity of `(1-x)²p(x)` gives one weak sign for `r` at the zero nodes;
the assumed upper bound gives the opposite weak sign at the `2α` nodes.  The
nodes are strictly increasing by `Polynomial.Chebyshev.strictAntiOn_node`
after reversing their indices.  Apply
`polynomial_eq_zero_of_alternating_signs` with `m=N-2`; its degree hypothesis
is exactly the bound on `r`.  Therefore `r=0` and `p=S`.

This uniqueness lemma proves both public statements:

- if the weighted norm were smaller than the constant, uniqueness would give
  `p=S`, contradicting the already computed norm of `S`;
- equality implies `p=S`, while the reverse implication follows directly
  from `weightedExtremalPolynomial_norm`.

### Constant conversion

Unfold both constants, push the cast through `n+2`, and use
`2*(n+2)=2n+4` and `4*16=2^6`.  `norm_num`, `push_cast`, and `ring` prove
`sharpConstant_eq_four_mul_weightedChebyshevConstant`; no trigonometric
identity is needed.
