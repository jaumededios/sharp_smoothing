# Blueprint for `JoseSmoothest/SpecialFunctions/PellAbel.lean`

## Purpose and status

This module contains only polynomial algebra.  It packages solutions of

```text
P² - D Q² = 1,
```

proves the derivative divisibility `Q ∣ P'`, controls all degrees, and
computes the valuations forced by endpoint contact.  No Riemann surface,
period, or existence theorem occurs here.  It is now the first implemented
module of the arbitrary-even workstream and is a strong candidate for an
independent Mathlib contribution.

## Imports

```lean
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Real.Basic
```

## Public declarations

```lean
noncomputable section

namespace Polynomial

open scoped Polynomial

structure PellAbelSolution {R : Type*} [CommRing R]
    (D : R[X]) where
  P : R[X]
  Q : R[X]
  equation : P ^ 2 - D * Q ^ 2 = 1

namespace PellAbelSolution

variable {R : Type*} [CommRing R] {D : R[X]}

@[simp] theorem equation_add (s : PellAbelSolution D) :
    s.P ^ 2 = 1 + D * s.Q ^ 2

def one : PellAbelSolution D

def neg (s : PellAbelSolution D) : PellAbelSolution D

@[simp] theorem neg_P (s : PellAbelSolution D) : s.neg.P = -s.P

@[simp] theorem neg_Q (s : PellAbelSolution D) : s.neg.Q = -s.Q

def mul (s t : PellAbelSolution D) : PellAbelSolution D

@[simp] theorem mul_P (s t : PellAbelSolution D) :
    (s.mul t).P = s.P * t.P + D * s.Q * t.Q

@[simp] theorem mul_Q (s t : PellAbelSolution D) :
    (s.mul t).Q = s.P * t.Q + s.Q * t.P

def pow (s : PellAbelSolution D) (n : ℕ) : PellAbelSolution D

@[simp] theorem pow_zero (s : PellAbelSolution D) :
    s.pow 0 = one

@[simp] theorem pow_succ (s : PellAbelSolution D) (n : ℕ) :
    s.pow (n + 1) = (s.pow n).mul s

section CommRing

theorem isCoprime_P_Q (s : PellAbelSolution D) :
    IsCoprime s.P s.Q

theorem isCoprime_P_D (s : PellAbelSolution D) :
    IsCoprime s.P D

end CommRing

section Field

variable {R : Type*} [Field R] {D : R[X]}

def differentialNumerator (s : PellAbelSolution D) : R[X] :=
  derivative s.P / s.Q

theorem natDegree_Q {g N : ℕ} (s : PellAbelSolution D)
    (hD : D.natDegree = 2 * g + 2)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hP : s.P.natDegree = N) (hN : g + 1 ≤ N) :
    s.Q.natDegree = N - g - 1

end Field

section CharZeroField

variable {R : Type*} [Field R] [CharZero R] {D : R[X]}

theorem Q_dvd_derivative_P (s : PellAbelSolution D) :
    s.Q ∣ derivative s.P

theorem derivative_P_eq (s : PellAbelSolution D) :
    derivative s.P = s.differentialNumerator * s.Q

theorem natDegree_differentialNumerator_le {g N : ℕ}
    (s : PellAbelSolution D)
    (hD : D.natDegree = 2 * g + 2)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hP : s.P.natDegree = N) (hN : g + 1 ≤ N) :
    s.differentialNumerator.natDegree ≤ g

theorem rootMultiplicity_one_sub_P {a : R}
    (s : PellAbelSolution D)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (ha : s.P.eval a = 1) :
    rootMultiplicity a (1 - s.P) =
      rootMultiplicity a D + 2 * rootMultiplicity a s.Q

theorem rootMultiplicity_D_eq_mod_two {a : R} {m : ℕ}
    (s : PellAbelSolution D)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hsqfree : Squarefree D)
    (ha : s.P.eval a = 1)
    (hm : rootMultiplicity a (1 - s.P) = m) :
    rootMultiplicity a D = m % 2

theorem rootMultiplicity_Q_eq_half {a : R} {m : ℕ}
    (s : PellAbelSolution D)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hsqfree : Squarefree D)
    (ha : s.P.eval a = 1)
    (hm : rootMultiplicity a (1 - s.P) = m) :
    rootMultiplicity a s.Q = m / 2

theorem rootMultiplicity_differentialNumerator {a : R} {m : ℕ}
    (s : PellAbelSolution D)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hsqfree : Squarefree D) (ha : s.P.eval a = 1)
    (hm0 : 0 < m)
    (hm : rootMultiplicity a (1 - s.P) = m) :
    rootMultiplicity a s.differentialNumerator = (m - 1) / 2

end CharZeroField

section Real

variable {D : ℝ[X]}

theorem abs_eval_P_le_one_of_nonpos
    (s : PellAbelSolution D) {a b x : ℝ}
    (hD : ∀ y ∈ Set.Icc a b, D.eval y ≤ 0)
    (hx : x ∈ Set.Icc a b) :
    |s.P.eval x| ≤ 1

end Real

end PellAbelSolution

end Polynomial
```

## Detailed natural-language proof blueprint

### The norm-one multiplication law

Regard `P + Q√D` as a formal element of the quadratic algebra
`R[X][Y]/(Y²-D)`.  Multiplication gives

```text
(P₁ + Q₁√D)(P₂ + Q₂√D)
  = (P₁P₂ + DQ₁Q₂) + (P₁Q₂ + Q₁P₂)√D.
```

Multiplying the conjugates shows that norms multiply.  Therefore two
solutions give another solution with the displayed `P` and `Q`.  The unit
solution, sign change, and natural powers follow.  The implementation should
define the operations directly on the two polynomial coordinates; introducing
the quotient quadratic algebra is unnecessary overhead.

### Coprimality

Any common divisor of `P` and `Q` divides `P²` and `D Q²`.  The Pell equation
then says it divides one.  Bézout's characterization of polynomial coprimality
gives `isCoprime_P_Q`.  The same reduction modulo a common divisor of `P` and
`D` proves `isCoprime_P_D`.

There is deliberately no unconditional `P_ne_zero` theorem.  For example
`D=-1`, `Q=1`, `P=0` is a Pell solution over any characteristic-zero field.
Every later degree theorem that needs nonzeroness obtains it from a positive
degree hypothesis.

### Derivative divisibility

Differentiate

```text
P² - DQ² = 1
```

to obtain

```text
2 P P' = D' Q² + 2 D Q Q'.
```

Thus `Q ∣ 2 P P'`.  Characteristic zero makes the constant two a unit,
and `P` is coprime to `Q`, so Euclid's lemma gives `Q ∣ P'`.  Polynomial
Euclidean division therefore has zero remainder, proving
`derivative_P_eq` for the quotient chosen in `differentialNumerator`.

### Degrees

Assume `deg D = 2g+2`, `deg P=N`, and `Q≠0`.  In the Pell identity the
nonconstant leading terms of `P²` and `D Q²` must cancel, since their
difference is one.  Hence

```text
2N = (2g+2) + 2 deg Q,
```

which rearranges to `deg Q=N-g-1`.  Since `deg P'≤N-1` and
`P'=A Q`, the quotient `A` has degree at most `g`.  Keep this proof in terms
of `degree` until nonzeroness is established, then translate to `natDegree`;
doing arithmetic directly with the zero polynomial's `natDegree` convention
is brittle.

### Endpoint valuations

At a point with `P(a)=1`, the factor `P+1` is nonzero.  Factorization gives

```text
(P-1)(P+1) = D Q².
```

Orders of vanishing are additive under products, while `P+1` contributes
zero.  Negating `P-1` does not change its order, so

```text
ordₐ(1-P) = ordₐ(D) + 2 ordₐ(Q).
```

If `D` is squarefree, `ordₐ(D)` is either zero or one.  Reducing the
identity modulo two gives `ordₐ(D)=m mod 2`, and ordinary natural-number
arithmetic then gives `ordₐ(Q)=m/2`.

If `1-P` has exact order `m>0`, its derivative has exact order `m-1`.
Subtracting the order `m/2` of `Q` from the identity `P'=A Q` yields

```text
ordₐ(A) = m - 1 - m/2 = (m-1)/2.
```

This last calculation is the algebraic source of the minimum genus forced by
endpoint contact in the smoothing problem.

### Real interval bound

Evaluating the Pell identity at a real `x` gives

```text
P(x)² = 1 + D(x) Q(x)².
```

If `D(x)≤0`, the second term is nonpositive, hence `P(x)²≤1`.
Taking the nonnegative square root proves `|P(x)|≤1`.  Notice that this
argument gives the bound without any Abelian integral; periods are needed to
construct a solution, not to verify a polynomial solution already in hand.
