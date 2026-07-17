# Blueprint for `JoseSmoothest/SpecialFunctions/RiemannTheta.lean`

## Purpose and priority

This optional foundational module defines the genus-`g` Riemann theta series
and proves its basic analytic and transformation laws.  By itself it does not
give an effective hyperelliptic Pell formula; that would additionally require
a specialized Abel-coordinate/prime-form or theta-ratio bridge.  It is
**not** on the logical path to the Pell--Abel period criterion or to an
unconditional even-order minimax theorem.  It should be implemented only
after the genus-one period construction and the eighth-order parity case are
stable.

The definitions use the convention

```text
θ(z | Ω) = ∑_{n∈ℤ^g} exp(π i (nᵀ Ω n + 2 nᵀ z)).
```

## Imports

```lean
import JoseSmoothest.SpecialFunctions.PeriodMatrix
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Complex Matrix
open scoped ComplexConjugate

namespace RiemannTheta

variable {g : ℕ}

def integerVectorComplex (n : Fin g → ℤ) : Fin g → ℂ :=
  fun j ↦ n j

def quadraticTerm (S : SiegelUpperHalfSpace g)
    (n : Fin g → ℤ) : ℂ :=
  dotProduct (integerVectorComplex n)
    (S.periodMatrix *ᵥ integerVectorComplex n)

def linearTerm (z : Fin g → ℂ) (n : Fin g → ℤ) : ℂ :=
  dotProduct (integerVectorComplex n) z

def term (S : SiegelUpperHalfSpace g) (z : Fin g → ℂ)
    (n : Fin g → ℤ) : ℂ :=
  exp (π * I * (quadraticTerm S n + 2 * linearTerm z n))

def theta (S : SiegelUpperHalfSpace g) (z : Fin g → ℂ) : ℂ :=
  ∑' n : Fin g → ℤ, term S z n

def LocallyUniformlySummable
    (f : (Fin g → ℤ) → (Fin g → ℂ) → ℂ) : Prop :=
  ∀ K : Set (Fin g → ℂ), IsCompact K →
    Summable (fun n ↦ sSup {r : ℝ | ∃ z ∈ K, r = ‖f n z‖})

theorem summable_norm_term
    (S : SiegelUpperHalfSpace g) (z : Fin g → ℂ) :
    Summable (fun n : Fin g → ℤ ↦ ‖term S z n‖)

theorem locallyUniformlySummable_term
    (S : SiegelUpperHalfSpace g) :
    LocallyUniformlySummable (fun n : Fin g → ℤ ↦ term S · n)

theorem differentiable_theta (S : SiegelUpperHalfSpace g) :
    Differentiable ℂ (theta S)

theorem theta_neg (S : SiegelUpperHalfSpace g) (z : Fin g → ℂ) :
    theta S (-z) = theta S z

theorem theta_add_integer (S : SiegelUpperHalfSpace g)
    (z : Fin g → ℂ) (m : Fin g → ℤ) :
    theta S (z + integerVectorComplex m) = theta S z

theorem theta_add_period (S : SiegelUpperHalfSpace g)
    (z : Fin g → ℂ) (m : Fin g → ℤ) :
    theta S (z + S.periodMatrix *ᵥ integerVectorComplex m) =
      exp (-π * I *
        (quadraticTerm S m + 2 * linearTerm z m)) * theta S z

theorem theta_conj (S : SiegelUpperHalfSpace g)
    (z : Fin g → ℂ) :
    conj (theta S z) = theta S.conjugateNeg (-conj z)

structure Characteristic (g : ℕ) where
  epsilon : Fin g → ZMod 2
  delta : Fin g → ZMod 2

def thetaWithCharacteristic
    (S : SiegelUpperHalfSpace g) (c : Characteristic g)
    (z : Fin g → ℂ) : ℂ

def Characteristic.parity (c : Characteristic g) : ZMod 2 :=
  ∑ j, c.epsilon j * c.delta j

def Characteristic.integerMultiplier
    (c : Characteristic g) (m : Fin g → ℤ) : ℂ

theorem thetaWithCharacteristic_neg
    (S : SiegelUpperHalfSpace g) (c : Characteristic g)
    (z : Fin g → ℂ) :
    thetaWithCharacteristic S c (-z) =
      (-1 : ℂ) ^ c.parity.val * thetaWithCharacteristic S c z

theorem thetaWithCharacteristic_add_integer
    (S : SiegelUpperHalfSpace g) (c : Characteristic g)
    (z : Fin g → ℂ) (m : Fin g → ℤ) :
    thetaWithCharacteristic S c (z + integerVectorComplex m) =
      c.integerMultiplier m * thetaWithCharacteristic S c z

theorem theta_genusOne_eq_jacobiTheta₂
    (S : SiegelUpperHalfSpace 1) (z : Fin 1 → ℂ) :
    theta S z =
      jacobiTheta₂ (z 0) (S.periodMatrix 0 0)

end RiemannTheta

end JoseSmoothest
```

`LocallyUniformlySummable`, `Characteristic.integerMultiplier`, and the
choice of representatives of `ZMod 2` may require small local definitions.
The final public theorem names should follow Mathlib's conventions once the
implementation identifies the closest existing local-uniform convergence
API.

## Detailed natural-language proof blueprint

### Convergence

Positive definiteness of `Im Ω` gives a constant `c>0` with

```text
nᵀ Im(Ω) n ≥ c ‖n‖².
```

On a compact set of `z`, its imaginary part is uniformly bounded, so the norm
of the `n`-th summand is bounded by

```text
exp(-π c ‖n‖² + C ‖n‖).
```

Complete the square and compare with a product of one-dimensional Gaussian
series.  Mathlib's integer-lattice summability supplies the final summation.
The same estimate is uniform on compact `z`-sets, giving normal convergence.
Each term is entire, hence the locally uniform sum is entire and can be
differentiated term by term.

### Parity and integer periodicity

For evenness, reindex the absolutely convergent series by `n↦-n`; the
quadratic term is unchanged and the linear term changes sign.  For an integer
shift `z↦z+m`, every summand acquires
`exp(2πi nᵀm)=1`.

### Quasiperiodicity

Replace `z` by `z+Ωm`, expand the exponent using symmetry of `Ω`, and
complete the square:

```text
nᵀΩn + 2nᵀ(z+Ωm)
 = (n+m)ᵀΩ(n+m) + 2(n+m)ᵀz
   - mᵀΩm - 2mᵀz.
```

Pull out the last two terms and reindex by the integer-lattice translation
`n↦n+m`.  This proves `theta_add_period`.

### Conjugation

Conjugating a term replaces `i` by `-i`, `Ω` by `conj Ω`, and `z` by
`conj z`.  This is exactly the theta term for period matrix `-conj Ω` at
`-conj z`.  Its imaginary part is the original positive-definite matrix, so
it lies again in Siegel upper half-space.  Absolute convergence justifies
commuting conjugation with the sum.

### Characteristics

Choose zero/one representatives `ε,δ` and define the characteristic theta
as the shifted base theta multiplied by the standard exponential prefactor.
Changing representatives alters the expression by factors already controlled
by integer periodicity, so the result is well-defined.  Apply parity and
quasiperiodicity of the base theta to derive the characteristic parity and
shift laws.

### Genus-one compatibility

For `g=1`, a lattice vector is one integer and the matrix quadratic form is
`n²τ`.  The defining series is therefore term-for-term Mathlib's
`jacobiTheta₂` series.  This theorem is an essential normalization test:
all later genus-one specializations must reduce to the already used
`JacobiTheta.lean` convention.
