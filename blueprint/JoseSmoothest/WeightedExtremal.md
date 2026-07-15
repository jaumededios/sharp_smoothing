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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
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

/-- A polynomial feasible for the weighted extremal problem of order `N`. -/
structure IsAdmissibleWeightedPolynomial (N : ℕ) (p : ℝ[X]) : Prop where
  /-- The degree bound in the weighted extremal problem. -/
  degree_le : p.natDegree ≤ N - 2
  /-- Nonnegativity on the approximation interval. -/
  nonnegative : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x
  /-- Normalization at the right endpoint. -/
  eval_one : p.eval 1 = 1

/-- The sharp weighted Chebyshev constant is nonnegative. -/
theorem weightedChebyshevConstant_nonneg (N : ℕ) :
    0 ≤ weightedChebyshevConstant N

/-- The weighted extremal polynomial has the prescribed value at `1`. -/
theorem weightedExtremalPolynomial_eval_one
    (N : ℕ) (hN : 2 ≤ N) :
    (weightedExtremalPolynomial N).eval 1 = 1

/-- The optimizer has the degree required in Proposition 1.6. -/
theorem weightedExtremalPolynomial_natDegree_le
    (N : ℕ) (_hN : 2 ≤ N) :
    (weightedExtremalPolynomial N).natDegree ≤ N - 2

/-- The weighted extremal polynomial is nonnegative on `[-1, 1]`. -/
theorem weightedExtremalPolynomial_nonnegative
    (N : ℕ) (hN : 2 ≤ N) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ (weightedExtremalPolynomial N).eval x

/-- The explicit optimizer is feasible for the weighted extremal problem. -/
theorem weightedExtremalPolynomial_isAdmissible
    (N : ℕ) (hN : 2 ≤ N) :
    IsAdmissibleWeightedPolynomial N (weightedExtremalPolynomial N)

/-- The optimizer attains the sharp weighted Chebyshev constant. -/
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

/-- The paper's final constant is four times the weighted Chebyshev constant. -/
theorem sharpConstant_eq_four_mul_weightedChebyshevConstant (n : ℕ) :
    sharpConstant n = 4 * weightedChebyshevConstant (n + 2)

/-- The polynomial quotient agrees with the paper's pointwise formula. -/
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

namespace IsAdmissibleWeightedPolynomial

/-- The sharp lower bound, packaged for an admissible weighted polynomial. -/
theorem norm_ge
    {N : ℕ} {p : ℝ[X]}
    (hp : IsAdmissibleWeightedPolynomial N p)
    (hN : 2 ≤ N) :
    weightedChebyshevConstant N ≤ weightedPolynomialNorm p

/-- The equality characterization, packaged for an admissible weighted polynomial. -/
theorem norm_eq_iff
    {N : ℕ} {p : ℝ[X]}
    (hp : IsAdmissibleWeightedPolynomial N p)
    (hN : 2 ≤ N) :
    weightedPolynomialNorm p = weightedChebyshevConstant N ↔
      p = weightedExtremalPolynomial N

end IsAdmissibleWeightedPolynomial

end JoseSmoothest
```

## Detailed proof blueprint

### The four polynomial data definitions

`weightedChebyshevConstant N` is the closed form predicted by Proposition
1.6.  Its factors are kept separate so that the later proof can identify it
with twice the scale of the transformed Chebyshev numerator.

`affineChebyshevArgument N` is the polynomial

```text
L(X) = ((1 + cos(π/N)) / 2) (X + 1) - 1.
```

Thus `L(-1)=-1` and `L(1)=cos(π/N)`.  The positive slope maps the interval
`[-1,1]` into the interval on which the standard Chebyshev bound applies.

`transformedChebyshevPolynomial N` is the scaled numerator

```text
q(X) = (8/N²) tan²(π/(2N)) (1 + T_N(L(X))).
```

It is represented by `C`, polynomial addition, multiplication, and `comp`,
so its definition is an actual element of `ℝ[X]`, not merely a pointwise
function.

`weightedExtremalPolynomial N` divides `q` by `(1-X)²` in `ℝ[X]`.  The later
double-root argument proves that this division is exact for `N≥2`; hence the
definition represents the optimizer `S_{N-2}` without a singularity at one.

### `IsAdmissibleWeightedPolynomial`

The structure packages exactly the feasible set of Proposition 1.6.  Its
three fields record the degree bound, pointwise nonnegativity on `[-1,1]`,
and normalization at `1`.  No positivity hypothesis is included: the
alternation proof needs only weak nonnegativity, and the endpoint condition
already rules out the zero polynomial.

### `weightedChebyshevConstant_nonneg`

Unfold the constant.  The denominator `(N : ℝ)²` is nonnegative, as is the
square of the tangent.  The numerator is positive, and Lean's `positivity`
tactic combines these facts to prove the product is nonnegative.  This also
covers `N=0`, where real division uses the field convention for division by
zero.

### The double zero and `weightedExtremalPolynomial_eval_one`

Fix `N≥2`, put `c=cos(π/N)`, and write `L` and `q` for the two definitions
above.  At `x=1`, `L(1)=c` and

```text
T_N(c) = cos(N · π/N) = cos π = -1.
```

The derivative also vanishes there.  Mathlib's identity
`T_derivative_eq_U`, followed by `U_real_cos`, rewrites it as a multiple of
`sin π`; the denominator `sin(π/N)` is nonzero because `0<π/N<π`.
Consequently `q(1)=q'(1)=0`, so the root-multiplicity API gives
`(C 1-X)² ∣ q`.

Evaluate the Chebyshev differential equation
`one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T` at `c`.  Using
`T_N(c)=-1` and `T'_N(c)=0` gives the required value of `T''_N(c)`.  The
chain rule and the half-angle identity then simplify the scaled second
derivative to `q''(1)=2`.

Exact monic division gives

```text
q = (1-X)² S.
```

Differentiate this identity twice and evaluate at one.  All terms except
`2*S(1)` vanish, so comparison with `q''(1)=2` yields `S(1)=1`, which is the
statement of `weightedExtremalPolynomial_eval_one`.

### `weightedExtremalPolynomial_natDegree_le`

First bound the affine polynomial's natural degree by one.  The composition
degree estimate and `natDegree_T` then give `natDegree q≤N`.  Rewrite
polynomial `/` as `divByMonic` by the monicity of `(C 1-X)²`, whose degree is
two.  Mathlib's formula for the degree of a monic quotient reduces the goal
to `N-2≤N-2`.  The argument does not use `_hN`; that assumption is retained
so the theorem has the same interface as the other optimizer facts.

### `weightedExtremalPolynomial_nonnegative`

For `x∈[-1,1]`, positivity of the affine scale shows `L(x)∈[-1,1]`.
Mathlib's bound `abs_eval_T_real_le_one` therefore implies

```text
0 ≤ q(x) ≤ 2 * (8/N²) tan²(π/(2N)).
```

If `x=1`, use `weightedExtremalPolynomial_eval_one`.  Otherwise `(1-x)²`
is strictly positive.  Evaluating the exact factorization
`q=(1-X)²S` and dividing its nonnegative left-hand side by that factor proves
`0≤S(x)`.

### `weightedExtremalPolynomial_isAdmissible`

Construct the structure directly.  Fill `degree_le` with
`weightedExtremalPolynomial_natDegree_le`, `nonnegative` with the preceding
interval theorem, and `eval_one` with the endpoint normalization.  This is
the canonical bundled witness that the explicit polynomial is feasible.

### `weightedExtremalPolynomial_norm`

Evaluating `q=(1-X)²S` identifies every value in the range defining
`weightedPolynomialNorm S` with `|q(x)|`.  The Chebyshev estimate above gives
the pointwise upper bound `|q(x)|≤weightedChebyshevConstant N`.

For the reverse inequality, take the inverse image under `L` of
`cos(2π/N)`.  This point lies in `[-1,1]`, and `T_N(cos(2π/N))=1`, so `q`
equals twice its scale there, exactly `weightedChebyshevConstant N`.  The
range is nonempty (for example, use `x=0`) and the pointwise estimate supplies
an upper bound.  The two `csSup` inequalities, using that bound and the peak
witness, prove equality.

### `sharpConstant` and `extremalPolynomial`

`sharpConstant n` records the constant in Theorem 1.4 after substituting
`N=n+2` and incorporating the factor four introduced by the Fourier
reduction.

`extremalPolynomial n x` is the paper's pointwise expression for `S_n`.  At
`x=1` it explicitly returns the removable value `1`.  Away from one it is
the transformed Chebyshev numerator divided by `(1-x)²`, with every
occurrence of `N` replaced by `n+2`.

### `sharpConstant_eq_four_mul_weightedChebyshevConstant`

Unfold both constants and push the cast through `n+2`.  The identities
`2*(n+2)=2n+4` and `4*16=2^6` make the two expressions syntactically equal;
`ring_nf` completes the proof.  No trigonometric identity is needed.

### `weightedExtremalPolynomial_eval`

Split on `x=1`.  At one, use the optimizer normalization and the first branch
of `extremalPolynomial`.  If `x≠1`, evaluate the exact polynomial
factorization at `x`; the square `(1-x)²` is nonzero, so `field_simp` cancels
it.  Unfold the two scale definitions, `chebyshevT`, and the affine map, push
casts through `n+2`, and normalize the remaining ring expressions.  The
result is exactly the second branch of `extremalPolynomial`.

### Alternation and the two Proposition 1.6 theorems

The common core used by `weightedPolynomialNorm_ge` and
`weightedPolynomialNorm_eq_iff` first handles `N=2`: the degree condition
forces `p` to be the constant-one polynomial, as it does for the optimizer.

For `N≥3`, assume `p` is feasible and its weighted norm is at most the sharp
constant.  Since `p(1)=S(1)=1`, factor

```text
p - S = (X-1) r,
```

where `r.natDegree<N-2`.  At the `N-1` increasing, transformed Chebyshev
nodes corresponding to indices `N,N-1,…,2`, the numerator
`q=(1-X)²S` alternates between zero and twice its scale.  Nonnegativity of
`p` controls the sign of `r` at the zero nodes.  The assumed norm upper bound
controls the opposite sign at the peak nodes.  Multiplying `r` by the common
sign `(-1)^N` converts these statements into the hypotheses of
`polynomial_eq_zero_of_alternating_signs` with `m=N-2`.  Thus `r=0`, and
therefore `p=S`.

For `weightedPolynomialNorm_ge`, suppose instead that the norm is strictly
below the constant.  The core uniqueness result gives `p=S`, contradicting
`weightedExtremalPolynomial_norm`.  Hence the constant is a lower bound.

For `weightedPolynomialNorm_eq_iff`, equality supplies the upper bound needed
by uniqueness and hence implies `p=S`.  Conversely, substituting `p=S`
reduces the claim directly to `weightedExtremalPolynomial_norm`.

### The bundled wrappers `norm_ge` and `norm_eq_iff`

Both namespace theorems simply unpack an
`IsAdmissibleWeightedPolynomial N p`.  The fields `degree_le`, `nonnegative`,
and `eval_one` are passed, in that order, to `weightedPolynomialNorm_ge` or
`weightedPolynomialNorm_eq_iff`; `hN` supplies the remaining order
assumption.  These wrappers expose the same sharp bound and equality theorem
through the reusable bundled admissibility API.
