# Blueprint for `JoseSmoothest/Zolotarev.lean`

## Purpose and status

This module formalizes the **algebraic half** of the cubic Zolotarev
construction used for sixth differences.  Its input, `CubicZolotarevData`,
records exactly the polynomial identities and real-interval information that
the Jacobi-elliptic construction must supply.  From those data the module
derives the endpoint normalization, constructs the cubic weighted optimizer,
builds its zero--peak certificate, and transfers the result to the unique
sharp kernel.

Thus every implication in this file is unconditional Lean mathematics.  The
existence of `CubicZolotarevData N` is deliberately not asserted here; the
analytic work still needed to construct such data is listed honestly at the
end of this blueprint.

## Imports

```lean
import JoseSmoothest.SixthOrder
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

def zolotarevPellWeight (H : ℝ[X]) : ℝ[X] :=
  (X ^ 2 - 1) * H

structure CubicZolotarevData (N : ℕ) where
  Z : ℝ[X]
  V : ℝ[X]
  H : ℝ[X]
  r : ℝ
  three_le : 3 ≤ N
  natDegree_Z_le : Z.natDegree ≤ N
  eval_one : Z.eval 1 = 1
  pell : Z ^ 2 - zolotarevPellWeight H * V ^ 2 = 1
  differential : derivative Z = C (N : ℝ) * (X - C 1) * V
  eval_H_one : H.eval 1 = r ^ 2
  r_ne_zero : r ≠ 0
  derivative_V_eval_one_ne_zero : (derivative V).eval 1 ≠ 0
  bounds : ∀ x ∈ Set.Icc (-1 : ℝ) 1, -1 ≤ Z.eval x ∧ Z.eval x ≤ 1
  orientation : ℝ
  orientation_eq : orientation = 1 ∨ orientation = -1
  nodes : Fin (N - 3 + 1) → ℝ
  strictMono_nodes : StrictMono nodes
  nodes_mem_Ico : ∀ i, nodes i ∈ Set.Ico (-1 : ℝ) 1
  node_value : ∀ i, Z.eval (nodes i) = orientation * (-1 : ℝ) ^ (i : ℕ)
  exists_negative : ∃ x ∈ Set.Icc (-1 : ℝ) 1, Z.eval x = -1

def CubicZolotarevData.scale {N : ℕ}
    (d : CubicZolotarevData N) : ℝ :=
  9 * d.r ^ 2 / (N : ℝ) ^ 2

def CubicZolotarevData.peak {N : ℕ}
    (d : CubicZolotarevData N) : ℝ :=
  18 * d.r ^ 2 / (N : ℝ) ^ 2

def CubicZolotarevData.numerator {N : ℕ}
    (d : CubicZolotarevData N) : ℝ[X] :=
  C d.scale * (1 - d.Z)

def CubicZolotarevData.endpointQuotient {N : ℕ}
    (d : CubicZolotarevData N) : ℝ[X] :=
  -(d.numerator /ₘ ((X - C 1) ^ 3))

@[simp] theorem zolotarevPellWeight_eval_one (H : ℝ[X]) :
    (zolotarevPellWeight H).eval 1 = 0

theorem zolotarevPellWeight_derivative_eval_one (H : ℝ[X]) :
    (derivative (zolotarevPellWeight H)).eval 1 = 2 * H.eval 1

theorem zolotarevEllipticEndpointScale_identity
    (k kComplement sn cn dn : ℝ)
    (hsn_dn : k ^ 2 * sn ^ 2 + dn ^ 2 = 1)
    (hsn_cn : kComplement ^ 2 * sn ^ 2 + cn ^ 2 = dn ^ 2)
    (hdn : dn ≠ 0) :
    (1 - cn / dn ^ 2) ^ 2 +
        (k * kComplement * sn ^ 2 / dn ^ 2) ^ 2 =
      ((1 - cn) / dn) ^ 2

theorem CubicZolotarevData.derivative_Z_eval_one {N : ℕ}
    (d : CubicZolotarevData N) :
    (derivative d.Z).eval 1 = 0

theorem CubicZolotarevData.eval_V_one {N : ℕ}
    (d : CubicZolotarevData N) :
    d.V.eval 1 = 0

theorem CubicZolotarevData.secondDerivative_Z_eval_one {N : ℕ}
    (d : CubicZolotarevData N) :
    (derivative (derivative d.Z)).eval 1 = 0

theorem CubicZolotarevData.derivative_V_eval_one {N : ℕ}
    (d : CubicZolotarevData N) :
    (derivative d.V).eval 1 = (N : ℝ) / (3 * d.r ^ 2)

theorem CubicZolotarevData.thirdDerivative_Z_eval_one {N : ℕ}
    (d : CubicZolotarevData N) :
    (derivative (derivative (derivative d.Z))).eval 1 =
      2 * (N : ℝ) ^ 2 / (3 * d.r ^ 2)

theorem CubicZolotarevData.cubic_dvd_one_sub_Z {N : ℕ}
    (d : CubicZolotarevData N) :
    (X - C 1) ^ 3 ∣ 1 - d.Z

theorem CubicZolotarevData.cubic_dvd_numerator {N : ℕ}
    (d : CubicZolotarevData N) :
    (X - C 1) ^ 3 ∣ d.numerator

theorem CubicZolotarevData.endpoint_factorization {N : ℕ}
    (d : CubicZolotarevData N) :
    (C 1 - X) ^ 3 * d.endpointQuotient = d.numerator

theorem CubicZolotarevData.natDegree_numerator_le {N : ℕ}
    (d : CubicZolotarevData N) :
    d.numerator.natDegree ≤ N

theorem CubicZolotarevData.natDegree_endpointQuotient_le {N : ℕ}
    (d : CubicZolotarevData N) :
    d.endpointQuotient.natDegree ≤ N - 3

theorem CubicZolotarevData.endpointQuotient_eval_one {N : ℕ}
    (d : CubicZolotarevData N) :
    d.endpointQuotient.eval 1 = 1

theorem CubicZolotarevData.scale_pos {N : ℕ}
    (d : CubicZolotarevData N) :
    0 < d.scale

theorem CubicZolotarevData.peak_eq_two_mul_scale {N : ℕ}
    (d : CubicZolotarevData N) :
    d.peak = 2 * d.scale

theorem CubicZolotarevData.numerator_bounds {N : ℕ}
    (d : CubicZolotarevData N) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ d.numerator.eval x ∧ d.numerator.eval x ≤ d.peak

theorem CubicZolotarevData.endpointQuotient_nonnegative {N : ℕ}
    (d : CubicZolotarevData N) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ d.endpointQuotient.eval x

theorem CubicZolotarevData.endpointQuotient_isAdmissible {N : ℕ}
    (d : CubicZolotarevData N) :
    IsAdmissibleCubicWeightedPolynomial N d.endpointQuotient

def CubicZolotarevData.zeroPeakCertificate {N : ℕ}
    (d : CubicZolotarevData N) :
    CubicZeroPeakCertificate N d.numerator d.peak

def CubicZolotarevData.sixthOrderKernel {n : ℕ}
    (d : CubicZolotarevData (n + 3)) : Kernel :=
  certifiedSixthOrderKernel n d.endpointQuotient

theorem CubicZolotarevData.cubicWeightedPolynomialNorm_endpointQuotient
    {N : ℕ} (d : CubicZolotarevData N) :
    cubicWeightedPolynomialNorm d.endpointQuotient = d.peak

theorem CubicZolotarevData.sixthOrderKernel_attains {n : ℕ}
    (d : CubicZolotarevData (n + 3)) :
    differenceSmoothness 6 d.sixthOrderKernel = 8 * d.peak

theorem CubicZolotarevData.sixthOrderKernel_attains_explicit {n : ℕ}
    (d : CubicZolotarevData (n + 3)) :
    differenceSmoothness 6 d.sixthOrderKernel =
      8 * (18 * d.r ^ 2 / ((n + 3 : ℕ) : ℝ) ^ 2)

theorem CubicZolotarevData.sixthOrderKernel_attains_paperConstant {n : ℕ}
    (d : CubicZolotarevData (n + 3)) :
    differenceSmoothness 6 d.sixthOrderKernel =
      144 * d.r ^ 2 / ((n + 3 : ℕ) : ℝ) ^ 2

theorem CubicZolotarevData.sixthOrderSmoothness_ge {n : ℕ}
    (d : CubicZolotarevData (n + 3))
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    8 * d.peak ≤ differenceSmoothness 6 u

theorem CubicZolotarevData.sixthOrderSmoothness_ge_paperConstant {n : ℕ}
    (d : CubicZolotarevData (n + 3))
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    144 * d.r ^ 2 / ((n + 3 : ℕ) : ℝ) ^ 2 ≤
      differenceSmoothness 6 u

theorem CubicZolotarevData.sixthOrderSmoothness_eq_iff {n : ℕ}
    (d : CubicZolotarevData (n + 3))
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    differenceSmoothness 6 u = 8 * d.peak ↔ u = d.sixthOrderKernel

theorem CubicZolotarevData.existsUnique_sixthOrderKernel {n : ℕ}
    (d : CubicZolotarevData (n + 3)) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧ differenceSmoothness 6 u = 8 * d.peak

end JoseSmoothest
```

## Detailed proof blueprint

### The Pell input and endpoint criticality

The Zolotarev Pell weight is

`W(X) = (X² - 1) H(X)`.

Evaluation at `X=1` immediately gives `W(1)=0`.  Differentiating by the
product rule gives

`W'(X) = 2X H(X) + (X²-1)H'(X)`,

and therefore `W'(1)=2H(1)`.  These calculations prove
`zolotarevPellWeight_eval_one` and
`zolotarevPellWeight_derivative_eval_one`.

The auxiliary theorem `zolotarevEllipticEndpointScale_identity` records the
elementary algebra needed to identify the endpoint value of the quadratic
Pell factor with the paper's elliptic ratio.  Clear the nonzero denominator
`dn`, use the Jacobi identities

`k² sn² + dn² = 1`,

`kComplement² sn² + cn² = dn²`,

and expand both squares.  Substitution of the two identities reduces the
difference of the two sides to zero.  Equivalently, the sum of the squared
parameters

`(1-cn/dn²)² + (k kComplement sn²/dn²)²`

is `((1-cn)/dn)²`.  This is precisely the algebraic calculation that turns
the value of `H(1)` in Lebedev's parametrization into `r²`; no analytic
Jacobi-function fact beyond the two displayed identities is used here.

The differential identity in the structure is

`Z' = N (X-1) V`.

Its right-hand side vanishes at one, proving `derivative_Z_eval_one`.  To
obtain `eval_V_one`, differentiate the Pell identity

`Z² - W V² = 1`

once and evaluate at one.  The already known values `Z(1)=1`, `Z'(1)=0`,
and `W(1)=0` reduce the identity to

`W'(1) V(1)² = 0`.

Here `W'(1)=2r²`; since `r≠0`, this forces `V(1)=0`.  Differentiating
`Z'=N(X-1)V` once and evaluating at one then gives `Z''(1)=N V(1)=0`,
which is `secondDerivative_Z_eval_one`.

### Determining the first nonzero endpoint coefficient

Differentiate the differential identity twice.  At one, all terms carrying
`X-1` or `V(1)` disappear, leaving

`Z'''(1) = 2N V'(1)`.                                                     (1)

Differentiate the Pell identity three times and evaluate at one.  Using
`Z(1)=1`, `Z'(1)=Z''(1)=0`, `W(1)=0`, `W'(1)=2r²`, and `V(1)=0`, the
surviving terms give

`Z'''(1) = 6r² V'(1)²`.                                                   (2)

Equating (1) and (2) gives

`V'(1) (2N - 6r² V'(1)) = 0`.

The `derivative_V_eval_one_ne_zero` field selects the nondegenerate branch,
so division by `3r²` proves

`V'(1)=N/(3r²)`.

Substitution back into (1) proves

`Z'''(1)=2N²/(3r²)`.

These are `derivative_V_eval_one` and `thirdDerivative_Z_eval_one`.  Notice
that the simple-zero assumption on `V` is used at exactly one point: it rules
out the unwanted zero branch of the quadratic endpoint identity.

### The cubic endpoint factor and exact quotient

Put `p=1-Z`.  The endpoint data say

`p(1)=p'(1)=p''(1)=0`.

The root-multiplicity/iterated-derivative criterion therefore implies that
`X-1` has multiplicity at least three in `p`.  The zero-polynomial case is
handled separately.  This proves `cubic_dvd_one_sub_Z`.  Multiplying the
resulting factorization by the constant polynomial `C scale` proves
`cubic_dvd_numerator`.

The definition of `endpointQuotient` divides the numerator by the monic
polynomial `(X-1)³` and then negates the quotient.  Exact division is valid
because of the preceding divisibility theorem.  Since

`(1-X)³ = -(X-1)³`,

the signs cancel and yield

`(1-X)³ endpointQuotient = numerator`.

This is `endpoint_factorization`.

### Degree bookkeeping

The numerator is a constant polynomial times `1-Z`, so its natural degree is
at most the degree of `Z`, hence at most `N`.  This proves
`natDegree_numerator_le`, including harmless zero-polynomial edge cases via
the standard `natDegree` inequalities.

Division by the monic cubic lowers natural degree by three.  Applying the
exact `natDegree_divByMonic` formula to `(X-1)³`, and then subtracting three
from the numerator bound, proves
`natDegree_endpointQuotient_le : natDegree endpointQuotient ≤ N-3`.

### Normalization at the distinguished endpoint

Differentiate the exact factorization

`(1-X)³ S = numerator`

three times and evaluate at one.  Direct expansion of the product rule gives

`((1-X)³ S)'''(1) = -6S(1)`.

On the other hand, because `numerator = scale(1-Z)`, its third derivative at
one is `-scale·Z'''(1)`.  Insert

`scale = 9r²/N²`, `Z'''(1)=2N²/(3r²)`,

and use `N≥3` and `r≠0` to cancel the nonzero denominators.  The result is
`-6S(1)=-6`, so `S(1)=1`.  This proves
`endpointQuotient_eval_one`.

### Positivity and interval bounds

Because `N≥3`, the real number `N` is positive; because `r≠0`, `r²` is
positive.  Hence `scale=9r²/N²` is positive, proving `scale_pos`.  Unfolding
the two definitions and simplifying proves

`peak = 18r²/N² = 2 scale`,

which is `peak_eq_two_mul_scale`.

For `x∈[-1,1]`, the input bound `-1≤Z(x)≤1` says
`0≤1-Z(x)≤2`.  Multiplication by the positive scale therefore gives

`0 ≤ numerator(x) ≤ 2 scale = peak`.

This is `numerator_bounds`.

To prove `endpointQuotient_nonnegative`, first handle `x=1` using its
normalization.  If `x<1`, evaluate the endpoint factorization:

`(1-x)³ endpointQuotient(x) = numerator(x)`.

The factor `(1-x)³` is strictly positive and the numerator is nonnegative,
so the quotient is nonnegative.  The degree bound, this pointwise
nonnegativity, and the value one at the endpoint are precisely the three
fields of `IsAdmissibleCubicWeightedPolynomial`; together they prove
`endpointQuotient_isAdmissible`.

### The zero--peak certificate

The definition `zeroPeakCertificate` reuses the orientation, ordered nodes,
node locations, and interval bounds from `CubicZolotarevData`.  The input
`exists_negative` supplies a point where `Z=-1`; there the numerator equals

`scale(1-(-1)) = 2 scale = peak`,

so a peak is genuinely attained.  At an alternation node,

`Z(nodes i)=orientation·(-1)^i`.

Consequently

`numerator(nodes i)
 = scale(1-orientation·(-1)^i)
 = peak/2·(1-orientation·(-1)^i)`,

which is exactly the zero--peak node formula expected by
`CubicZeroPeakCertificate`.

### Passage to the sixth-difference kernel

The definition `sixthOrderKernel` applies the inverse polynomial-to-kernel
construction from `SixthOrder.lean` to `endpointQuotient`.  The theorem
`cubicWeightedPolynomialNorm_endpointQuotient` feeds the endpoint
factorization and the zero--peak certificate into the generic certified-norm
theorem, obtaining exactly `peak`.

The theorem `sixthOrderKernel_attains` then applies the generic sixth-order
kernel transfer theorem.  It uses the admissibility proved above and the
same factorization and certificate to obtain

`differenceSmoothness 6 sixthOrderKernel = 8·peak`.

Unfolding the definition of `peak` gives

`8 · (18r²/(n+3)²)`,

which is `sixthOrderKernel_attains_explicit` and is the elliptic-ratio form of
the paper's constant.  Ring normalization rewrites the leading product
`8·18` as `144=2⁴·3²`, proving
`sixthOrderKernel_attains_paperConstant` in the exact layout of Theorem 1.7.

For an arbitrary admissible kernel, the generic certified lower-bound
theorem yields `8·peak ≤ differenceSmoothness 6 u`; this is
`sixthOrderSmoothness_ge`.  Unfolding `peak` and applying the same ring
normalization converts its left side to `144r²/(n+3)²`, proving
`sixthOrderSmoothness_ge_paperConstant`.  Its equality theorem says equality
holds exactly when the kernel equals the reconstructed candidate, proving
`sixthOrderSmoothness_eq_iff`.  Finally, the generic existence-and-uniqueness
theorem packages admissibility, attainment, and that equality
characterization into `existsUnique_sixthOrderKernel`.

## Remaining analytic existence input

The completed algebra above reduces the unconditional sixth-order theorem to
constructing a term of type `CubicZolotarevData N`.  This is substantial
analytic mathematics, and the paper itself delegates central parts of it to
Lebedev's theory rather than proving them.  A faithful Lean development must
still establish all of the following.

1. **Existence of the distinguished modulus `k_N`.**  For `a=K(k)/N`, the
   paper chooses `k_N∈(0,1)` satisfying

   `cn(2a) + 2 sn(2a) Zeta(a) = 1`.

   Lean needs continuous real versions of the complete elliptic integral,
   Jacobi elliptic functions, and Jacobi zeta, followed by a genuine
   existence proof for a root of this equation (and any uniqueness or range
   information used later).  Merely defining `k_N` by choice would leave the
   required existence theorem unproved.

2. **Theta-quotient descent to a polynomial.**  Lebedev's formula initially
   defines the first Zolotarev function through a theta quotient in an
   auxiliary variable `u`, while the real polynomial variable is a rational
   expression in `cn(2u)`.  One must prove that the quotient is invariant
   under all changes of `u` representing the same `x`, has no unwanted
   poles, and descends to a real polynomial `Z` of degree at most `N`.
   Mathlib's modular Jacobi-theta material does not currently provide this
   real-variable descent theorem.

3. **Lebedev's Pell and differential identities.**  The descended
   polynomials `Z`, `V`, and the quadratic factor `H` must satisfy

   `Z² - (X²-1)H V² = 1`,

   `Z' = N(X-1)V`, and `H(1)=r²`, with
   `r=(1-cn(2a))/dn(2a)`.  These are not in Mathlib.  Formalizing the cited
   Lebedev result requires developing the relevant theta/Jacobi addition,
   derivative, and zero/pole formulas rather than treating the citation as an
   axiom.

4. **The simple endpoint zero of `V`.**  This file assumes `V'(1)≠0` and then
   derives the paper's endpoint normalization.  Pell plus the differential
   equation alone only gives the product alternative
   `V'(1)=0` or `V'(1)=N/(3r²)`; it does not rule out the degenerate branch.
   The elliptic construction must prove the zero of `V` at one is simple (or
   prove the desired nonzero third derivative by an equivalent argument).

5. **Real interval bounds and equioscillation.**  One must prove
   `|Z(x)|≤1` on `[-1,1]`, produce the required strictly ordered nodes in
   `[-1,1)`, prove the alternating values there, and exhibit a point where
   `Z=-1`.  In the theta parametrization this requires tracking the real
   path and the phase of the quotient.  Statements modulo periods are not
   enough: an **unwrapped phase** (or a direct monotonic parametrization) is
   needed to count and order every alternation point without losing integer
   winding information.

These five items are the exact boundary between the present formalization and
an unconditional construction of the paper's Zolotarev certificate.  In
particular, the Lean structure is not an extra mathematical conjecture: its
fields are the explicit conclusions that must be extracted from the
elliptic/Lebedev construction, while every subsequent optimization and kernel
argument has already been checked by Lean.
