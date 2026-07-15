import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Theta-function expressions used by the Zolotarev construction

This file fixes the theta-function conventions needed to state the analytic
part of Lebedev's Zolotarev construction.  Mathlib's `jacobiTheta₂` is the
normalized two-variable series

`∑' n : ℤ, exp (2 π i n z + π i n² τ)`.

The definitions below are total functions, as usual in Lean.  In particular,
quotients evaluate to zero when a denominator is zero.  Theorems which identify
these expressions with classical Jacobi elliptic functions will therefore need
upper-half-plane and nonvanishing hypotheses; no such identification is claimed
in this foundational file.
-/

noncomputable section

namespace JoseSmoothest

open Complex Real

/-- The normalized theta-three function `θ₃(z, τ)`, in Mathlib's convention. -/
def thetaThree (z τ : ℂ) : ℂ :=
  jacobiTheta₂ z τ

/-- The normalized theta-four function `θ₄(z, τ) = θ₃(z + 1/2, τ)`. -/
def thetaFour (z τ : ℂ) : ℂ :=
  jacobiTheta₂ (z + 1 / 2) τ

/-- The normalized theta-two expression obtained by translating `θ₃`.

It agrees with the classical `θ₂` series when `τ` is in the upper half-plane.
-/
def thetaTwo (z τ : ℂ) : ℂ :=
  cexp (π * I * (τ / 4 + z)) * jacobiTheta₂ (z + τ / 2) τ

/-- The normalized theta-one expression obtained by translating `θ₃`.

It agrees with the classical `θ₁` series when `τ` is in the upper half-plane.
-/
def thetaOne (z τ : ℂ) : ℂ :=
  -I * cexp (π * I * (τ / 4 + z)) *
    jacobiTheta₂ (z + (1 + τ) / 2) τ

/-- The first-variable derivative of `thetaThree`. -/
def thetaThreePrime (z τ : ℂ) : ℂ :=
  jacobiTheta₂' z τ

/-- The first-variable derivative of `thetaFour`. -/
def thetaFourPrime (z τ : ℂ) : ℂ :=
  jacobiTheta₂' (z + 1 / 2) τ

/-- The derivative of `thetaThree` with respect to its first argument. -/
theorem hasDerivAt_thetaThree (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (thetaThree · τ) (thetaThreePrime z τ) z := by
  simpa [thetaThree, thetaThreePrime] using
    hasDerivAt_jacobiTheta₂_fst z hτ

/-- The derivative of `thetaFour` with respect to its first argument. -/
theorem hasDerivAt_thetaFour (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (thetaFour · τ) (thetaFourPrime z τ) z := by
  simpa [thetaFour, thetaFourPrime, Function.comp_def] using
    (hasDerivAt_jacobiTheta₂_fst (z + 1 / 2) hτ).comp z
      ((hasDerivAt_id z).add_const (1 / 2))

/-- `thetaThree` has period one in its first argument. -/
theorem thetaThree_add_one (z τ : ℂ) :
    thetaThree (z + 1) τ = thetaThree z τ := by
  exact jacobiTheta₂_add_left z τ

/-- `thetaFour` has period one in its first argument. -/
theorem thetaFour_add_one (z τ : ℂ) :
    thetaFour (z + 1) τ = thetaFour z τ := by
  rw [thetaFour, thetaFour]
  convert jacobiTheta₂_add_left (z + 1 / 2) τ using 1
  ring_nf

/-- `thetaThree` is even in its first argument. -/
theorem thetaThree_neg (z τ : ℂ) :
    thetaThree (-z) τ = thetaThree z τ := by
  exact jacobiTheta₂_neg_left z τ

/-- `thetaFour` is even in its first argument. -/
theorem thetaFour_neg (z τ : ℂ) :
    thetaFour (-z) τ = thetaFour z τ := by
  rw [thetaFour, thetaFour]
  rw [show -z + 1 / 2 = -(z + 1 / 2) + 1 by ring]
  rw [jacobiTheta₂_add_left, jacobiTheta₂_neg_left]

/-- The first-variable derivative of `thetaThree` has period one. -/
theorem thetaThreePrime_add_one (z τ : ℂ) :
    thetaThreePrime (z + 1) τ = thetaThreePrime z τ := by
  exact jacobiTheta₂'_add_left z τ

/-- The first-variable derivative of `thetaFour` has period one. -/
theorem thetaFourPrime_add_one (z τ : ℂ) :
    thetaFourPrime (z + 1) τ = thetaFourPrime z τ := by
  rw [thetaFourPrime, thetaFourPrime]
  convert jacobiTheta₂'_add_left (z + 1 / 2) τ using 1
  ring_nf

/-- The first-variable derivative of `thetaThree` is odd. -/
theorem thetaThreePrime_neg (z τ : ℂ) :
    thetaThreePrime (-z) τ = -thetaThreePrime z τ := by
  exact jacobiTheta₂'_neg_left z τ

/-- The first-variable derivative of `thetaFour` is odd. -/
theorem thetaFourPrime_neg (z τ : ℂ) :
    thetaFourPrime (-z) τ = -thetaFourPrime z τ := by
  rw [thetaFourPrime, thetaFourPrime]
  rw [show -z + 1 / 2 = -(z + 1 / 2) + 1 by ring]
  rw [jacobiTheta₂'_add_left, jacobiTheta₂'_neg_left]

/-- The theta-constant expression for the elliptic modulus `k`.

The expression is totalized when `thetaThree 0 τ = 0`.  No range or
nonvanishing theorem is asserted here.
-/
def ellipticModulusThetaExpression (τ : ℂ) : ℂ :=
  (thetaTwo 0 τ / thetaThree 0 τ) ^ 2

/-- The theta-constant expression for the complete elliptic integral `K`.

Identifying it with the real complete elliptic integral requires a compatible
relation between `τ` and the modulus and is outside this file.
-/
def completeKThetaExpression (τ : ℂ) : ℂ :=
  π / 2 * thetaThree 0 τ ^ 2

/-- The normalized theta argument `u/(2K)` used in the Jacobi formulas. -/
def normalizedThetaArgument (u τ : ℂ) : ℂ :=
  u / (2 * completeKThetaExpression τ)

/-- The theta-one expression with an elliptic argument `u`, rather than
Mathlib's normalized theta argument. -/
def thetaOneEllipticArgument (u τ : ℂ) : ℂ :=
  thetaOne (normalizedThetaArgument u τ) τ

/-- The theta-three expression with an elliptic argument `u`, rather than
Mathlib's normalized theta argument. -/
def thetaThreeEllipticArgument (u τ : ℂ) : ℂ :=
  thetaThree (normalizedThetaArgument u τ) τ

/-- The product `Θ₁(u) Θ₃(u)` occurring in Lebedev's theta quotient, where
the capital theta functions use the paper's elliptic argument. -/
def ellipticThetaOneThreeProduct (u τ : ℂ) : ℂ :=
  thetaOneEllipticArgument u τ * thetaThreeEllipticArgument u τ

/-- Lebedev's basic theta quotient
`A(a,u,τ) = θ₁(a+u)θ₃(a+u) / (θ₁(a-u)θ₃(a-u))`.

This is only the analytic quotient.  No nonvanishing or polynomiality claim is
part of the definition.
-/
def lebedevThetaRatio (a u τ : ℂ) : ℂ :=
  ellipticThetaOneThreeProduct (a + u) τ /
    ellipticThetaOneThreeProduct (a - u) τ

/-- Negating the auxiliary variable inverts Lebedev's theta quotient.

Because inversion and division in `ℂ` are totalized at zero, the identity does
not require a separate nonvanishing hypothesis.
-/
theorem lebedevThetaRatio_neg (a u τ : ℂ) :
    lebedevThetaRatio a (-u) τ = (lebedevThetaRatio a u τ)⁻¹ := by
  rw [lebedevThetaRatio, lebedevThetaRatio]
  rw [show a + -u = a - u by ring, show a - -u = a + u by ring]
  exact (inv_div _ _).symm

/-- The symmetric power of Lebedev's theta quotient.

This is the analytic expression `(A^N + A⁻ᴺ)/2` from the paper.  Calling it a
polynomial in a separate real coordinate requires a substantial theorem and is
intentionally not asserted here.
-/
def lebedevSymmetricThetaPower (N : ℕ) (a u τ : ℂ) : ℂ :=
  ((lebedevThetaRatio a u τ) ^ N +
      ((lebedevThetaRatio a u τ)⁻¹) ^ N) / 2

/-- The symmetric theta power is even in its auxiliary variable. -/
theorem lebedevSymmetricThetaPower_neg (N : ℕ) (a u τ : ℂ) :
    lebedevSymmetricThetaPower N a (-u) τ =
      lebedevSymmetricThetaPower N a u τ := by
  simp only [lebedevSymmetricThetaPower, lebedevThetaRatio_neg, inv_inv]
  rw [add_comm]

/-- The theta quotient which represents Jacobi `sn` under the classical
upper-half-plane and nonvanishing hypotheses.

This definition records the expression only; division is totalized if a theta
constant or `thetaFour` vanishes.
-/
def jacobiSnThetaExpression (u τ : ℂ) : ℂ :=
  thetaThree 0 τ / thetaTwo 0 τ *
    (thetaOne (normalizedThetaArgument u τ) τ /
      thetaFour (normalizedThetaArgument u τ) τ)

/-- The theta quotient which represents Jacobi `cn` under the classical
upper-half-plane and nonvanishing hypotheses. -/
def jacobiCnThetaExpression (u τ : ℂ) : ℂ :=
  thetaFour 0 τ / thetaTwo 0 τ *
    (thetaTwo (normalizedThetaArgument u τ) τ /
      thetaFour (normalizedThetaArgument u τ) τ)

/-- The theta quotient which represents Jacobi `dn` under the classical
upper-half-plane and nonvanishing hypotheses. -/
def jacobiDnThetaExpression (u τ : ℂ) : ℂ :=
  thetaFour 0 τ / thetaThree 0 τ *
    (thetaThree (normalizedThetaArgument u τ) τ /
      thetaFour (normalizedThetaArgument u τ) τ)

/-- The logarithmic-theta-derivative expression which represents Jacobi's
zeta function under the classical upper-half-plane and nonvanishing hypotheses.

The factor `2K` corresponds to the normalized theta argument `u/(2K)`.
-/
def jacobiZetaThetaExpression (u τ : ℂ) : ℂ :=
  thetaFourPrime (normalizedThetaArgument u τ) τ /
    (2 * completeKThetaExpression τ *
      thetaFour (normalizedThetaArgument u τ) τ)

end JoseSmoothest
