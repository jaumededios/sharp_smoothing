# Blueprint for `JoseSmoothest/JacobiTheta.lean`

## Purpose and normalization

This module fixes the theta-function conventions needed for the analytic
Zolotarev construction.  Mathlib's `jacobiTheta₂ z τ` uses the normalized
theta coordinate `z`, with period one.  The paper instead writes its capital
theta functions as functions of the elliptic argument `u`.  The two arguments
are related by

```text
z = u / (2 K).
```

Keeping that conversion explicit is essential: it accounts both for the
argument in Lebedev's quotient and for the factor `1/(2K)` in the theta formula
for Jacobi zeta.

Every quotient below is a total complex-valued Lean function.  Thus division
by zero has Lean's usual value zero.  This module does **not** claim that the
theta constants are nonzero, that the resulting expressions are real on a
real interval, or that the symmetric theta expression is a polynomial.  Those
are precisely some of the analytic results still needed for the Zolotarev
certificate.

## Imports

```lean
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Complex Real

def thetaThree (z τ : ℂ) : ℂ :=
  jacobiTheta₂ z τ

def thetaFour (z τ : ℂ) : ℂ :=
  jacobiTheta₂ (z + 1 / 2) τ

def thetaTwo (z τ : ℂ) : ℂ :=
  cexp (π * I * (τ / 4 + z)) * jacobiTheta₂ (z + τ / 2) τ

def thetaOne (z τ : ℂ) : ℂ :=
  -I * cexp (π * I * (τ / 4 + z)) *
    jacobiTheta₂ (z + (1 + τ) / 2) τ

def thetaThreePrime (z τ : ℂ) : ℂ :=
  jacobiTheta₂' z τ

def thetaFourPrime (z τ : ℂ) : ℂ :=
  jacobiTheta₂' (z + 1 / 2) τ

theorem hasDerivAt_thetaThree (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (thetaThree · τ) (thetaThreePrime z τ) z

theorem hasDerivAt_thetaFour (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (thetaFour · τ) (thetaFourPrime z τ) z

theorem thetaThree_add_one (z τ : ℂ) :
    thetaThree (z + 1) τ = thetaThree z τ

theorem thetaFour_add_one (z τ : ℂ) :
    thetaFour (z + 1) τ = thetaFour z τ

theorem thetaThree_neg (z τ : ℂ) :
    thetaThree (-z) τ = thetaThree z τ

theorem thetaFour_neg (z τ : ℂ) :
    thetaFour (-z) τ = thetaFour z τ

theorem thetaThreePrime_add_one (z τ : ℂ) :
    thetaThreePrime (z + 1) τ = thetaThreePrime z τ

theorem thetaFourPrime_add_one (z τ : ℂ) :
    thetaFourPrime (z + 1) τ = thetaFourPrime z τ

theorem thetaThreePrime_neg (z τ : ℂ) :
    thetaThreePrime (-z) τ = -thetaThreePrime z τ

theorem thetaFourPrime_neg (z τ : ℂ) :
    thetaFourPrime (-z) τ = -thetaFourPrime z τ

def ellipticModulusThetaExpression (τ : ℂ) : ℂ :=
  (thetaTwo 0 τ / thetaThree 0 τ) ^ 2

def completeKThetaExpression (τ : ℂ) : ℂ :=
  π / 2 * thetaThree 0 τ ^ 2

def normalizedThetaArgument (u τ : ℂ) : ℂ :=
  u / (2 * completeKThetaExpression τ)

def thetaOneEllipticArgument (u τ : ℂ) : ℂ :=
  thetaOne (normalizedThetaArgument u τ) τ

def thetaThreeEllipticArgument (u τ : ℂ) : ℂ :=
  thetaThree (normalizedThetaArgument u τ) τ

def ellipticThetaOneThreeProduct (u τ : ℂ) : ℂ :=
  thetaOneEllipticArgument u τ * thetaThreeEllipticArgument u τ

def lebedevThetaRatio (a u τ : ℂ) : ℂ :=
  ellipticThetaOneThreeProduct (a + u) τ /
    ellipticThetaOneThreeProduct (a - u) τ

theorem lebedevThetaRatio_neg (a u τ : ℂ) :
    lebedevThetaRatio a (-u) τ = (lebedevThetaRatio a u τ)⁻¹

def lebedevSymmetricThetaPower (N : ℕ) (a u τ : ℂ) : ℂ :=
  ((lebedevThetaRatio a u τ) ^ N +
      ((lebedevThetaRatio a u τ)⁻¹) ^ N) / 2

theorem lebedevSymmetricThetaPower_neg (N : ℕ) (a u τ : ℂ) :
    lebedevSymmetricThetaPower N a (-u) τ =
      lebedevSymmetricThetaPower N a u τ

def jacobiSnThetaExpression (u τ : ℂ) : ℂ :=
  thetaThree 0 τ / thetaTwo 0 τ *
    (thetaOne (normalizedThetaArgument u τ) τ /
      thetaFour (normalizedThetaArgument u τ) τ)

def jacobiCnThetaExpression (u τ : ℂ) : ℂ :=
  thetaFour 0 τ / thetaTwo 0 τ *
    (thetaTwo (normalizedThetaArgument u τ) τ /
      thetaFour (normalizedThetaArgument u τ) τ)

def jacobiDnThetaExpression (u τ : ℂ) : ℂ :=
  thetaFour 0 τ / thetaThree 0 τ *
    (thetaThree (normalizedThetaArgument u τ) τ /
      thetaFour (normalizedThetaArgument u τ) τ)

def jacobiZetaThetaExpression (u τ : ℂ) : ℂ :=
  thetaFourPrime (normalizedThetaArgument u τ) τ /
    (2 * completeKThetaExpression τ *
      thetaFour (normalizedThetaArgument u τ) τ)

end JoseSmoothest
```

## Detailed natural-language proof blueprint

### The four normalized theta functions

Mathlib defines

```text
θ₃(z,τ) = ∑ n : ℤ, exp(2πinz + πin²τ).
```

Accordingly, `thetaThree` is a direct alias.  Translating `z` by `1/2`
multiplies the `n`-th summand by `(-1)^n`, which is the standard normalized
`θ₄`; this gives `thetaFour`.

For `thetaTwo`, translate by `τ/2` and multiply by
`exp(πi(τ/4+z))`.  In the exponent, the three terms involving `τ` combine as

```text
n²τ + nτ + τ/4 = (n + 1/2)² τ,
```

and the terms involving `z` become `2πi(n+1/2)z`.  This is exactly the
normalized `θ₂` series.  Translating once more by `1/2` inserts `(-1)^n`;
the prefactor `-i` produces the standard `θ₁` convention.  These calculations
explain the definitions of `thetaTwo` and `thetaOne`; no theorem about their
series is needed later in this file.

`thetaThreePrime` is Mathlib's termwise first-variable derivative
`jacobiTheta₂'`.  Since `thetaFour` is just `thetaThree` translated by a
constant, its derivative is the same derivative series evaluated at
`z + 1/2`; this defines `thetaFourPrime`.

### `hasDerivAt_thetaThree`

Assume `0 < τ.im`.  Mathlib's theorem `hasDerivAt_jacobiTheta₂_fst` says that
the first-variable derivative of `jacobiTheta₂` is `jacobiTheta₂'` throughout
the upper half-plane.  Unfolding `thetaThree` and `thetaThreePrime` turns that
theorem into the desired statement verbatim.

### `hasDerivAt_thetaFour`

Again assume `0 < τ.im`.  Apply Mathlib's derivative theorem at
`z + 1/2`.  Compose it with the affine map `z ↦ z + 1/2`, whose derivative is
one.  After unfolding `thetaFour` and `thetaFourPrime`, the chain rule gives
the statement.

### Periodicity of `thetaThree` and `thetaFour`

Mathlib proves `jacobiTheta₂ (z+1) τ = jacobiTheta₂ z τ`, which directly gives
`thetaThree_add_one`.  For `thetaFour_add_one`, unfold the shifted definition.
Its left-hand theta argument is `(z+1)+1/2`, which is
`(z+1/2)+1`; the same Mathlib periodicity theorem finishes the proof.

### Evenness of `thetaThree` and `thetaFour`

Mathlib proves that `jacobiTheta₂` is even in `z`, giving `thetaThree_neg`
directly.  For theta four, rewrite

```text
-z + 1/2 = -(z + 1/2) + 1.
```

Remove the added one by periodicity and then remove the minus sign by
Mathlib's evenness theorem.  This proves `thetaFour_neg`.

### Periodicity and oddness of the derivatives

Mathlib separately proves that `jacobiTheta₂'` has period one and is odd.
Those statements immediately imply `thetaThreePrime_add_one` and
`thetaThreePrime_neg`.  The theta-four derivative has the translated argument
`z+1/2`.  The same two rewrites used for theta four itself therefore prove
`thetaFourPrime_add_one` and `thetaFourPrime_neg`, using derivative
periodicity and derivative oddness in place of their function counterparts.

### Theta expressions for the elliptic parameters

The classical theta-constant formulas are

```text
k = (θ₂(0)/θ₃(0))²,
K = (π/2) θ₃(0)².
```

`ellipticModulusThetaExpression` and `completeKThetaExpression` merely record
these expressions.  They do not yet assert that a chosen `τ` corresponds to a
real modulus or that the denominator is nonzero.  The normalized theta
coordinate associated with an elliptic argument is `u/(2K)`, which is exactly
`normalizedThetaArgument`.

The paper's capital theta functions take elliptic arguments.  Therefore
`thetaOneEllipticArgument u τ` and `thetaThreeEllipticArgument u τ` first
convert `u` to `u/(2K)` and only then apply the normalized theta function.
Their product is named `ellipticThetaOneThreeProduct`.

### Lebedev's quotient and `lebedevThetaRatio_neg`

The basic quotient in Lebedev's formula is

```text
A(a,u) = Θ₁(a+u)Θ₃(a+u) / (Θ₁(a-u)Θ₃(a-u)).
```

This is `lebedevThetaRatio`.  On replacing `u` by `-u`, its numerator becomes
the old denominator and its denominator becomes the old numerator.  Hence the
new quotient is the inverse of the old one.  Lean's inversion on `ℂ` is
involutive and division is totalized at zero, so `inv_div` proves the identity
without nonvanishing assumptions.

### Symmetric power and `lebedevSymmetricThetaPower_neg`

The analytic expression used to parametrize the Zolotarev polynomial is

```text
(A(a,u)^N + A(a,u)^(-N)) / 2.
```

`lebedevSymmetricThetaPower` records this expression without claiming it is a
polynomial in the paper's real coordinate `x`.  Under `u ↦ -u`, the preceding
theorem replaces `A` by `A⁻¹`.  The two summands are consequently exchanged.
Commutativity of addition proves `lebedevSymmetricThetaPower_neg`.

### The `sn`, `cn`, and `dn` theta expressions

With normalized theta argument `z=u/(2K)`, the standard formulas are

```text
sn(u) = θ₃(0)/θ₂(0) · θ₁(z)/θ₄(z),
cn(u) = θ₄(0)/θ₂(0) · θ₂(z)/θ₄(z),
dn(u) = θ₄(0)/θ₃(0) · θ₃(z)/θ₄(z).
```

The three definitions transcribe these formulas exactly.  Their names end in
`ThetaExpression` because the identification with a separately developed
theory of Jacobi elliptic functions, together with all required denominator
facts, has not yet been proved in Lean.

### The Jacobi-zeta theta expression

For normalized coordinate `z=u/(2K)`, differentiating with respect to the
elliptic argument `u` contributes the chain-rule factor `1/(2K)`.  Thus the
classical logarithmic-derivative expression is

```text
Z(u) = θ₄'(z) / (2K θ₄(z)).
```

This is precisely `jacobiZetaThetaExpression`.  As with the other elliptic
expressions, the definition makes no nonvanishing or identification claim.

## What remains beyond this module

To turn these expressions into the paper's Zolotarev certificate, later files
must still establish at least:

1. an upper-half-plane parameter corresponding to each real modulus;
2. nonvanishing and reality of the theta quotients on the relevant path;
3. the Jacobi elliptic identities and the existence of the special parameter
   solving Lebedev's equation;
4. polynomiality in the rationally parametrized real coordinate;
5. the Pell identity, derivative identity, and equioscillation data.

This file intentionally isolates a small part which is already supported by
Mathlib and is fully proved without axioms or placeholders.
