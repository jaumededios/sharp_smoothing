# Blueprint for `JoseSmoothest/EvenOrder/EndpointContact.lean`

## Purpose

This project-specific algebraic adapter proves the genus lower bound forced
by order-`m` endpoint contact.  Its main structure then packages the
minimal-genus equality case selected by alternation and derives the odd/even
squarefree-factor split, universal differential identity, and endpoint
scale.  It does not assume periods or equioscillation.

The smoothing difference order is `2*m`; `N` is the degree of the normalized
extremal polynomial, usually `supportRadius + m`.

## Imports

```lean
import JoseSmoothest.SpecialFunctions.PellAbel
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

def endpointGenus (m : ℕ) : ℕ := (m - 1) / 2

@[simp] theorem endpointGenus_two_mul_add_one (g : ℕ) :
    endpointGenus (2 * g + 1) = g

@[simp] theorem endpointGenus_two_mul_add_two (g : ℕ) :
    endpointGenus (2 * g + 2) = g

theorem two_mul_endpointGenus_add_parity (m : ℕ) (hm : 0 < m) :
    2 * endpointGenus m + 1 + (1 - m % 2) = m

theorem endpointGenus_le_curveGenus
    {g m N : ℕ} {D : ℝ[X]}
    (s : Polynomial.PellAbelSolution D)
    (hm0 : 0 < m) (hD : D.natDegree = 2 * g + 2)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hsqfree : Squarefree D)
    (hP : s.P.natDegree = N) (hN : g + 1 ≤ N)
    (heval : s.P.eval 1 = 1)
    (hcontact : rootMultiplicity 1 (1 - s.P) = m) :
    endpointGenus m ≤ g


structure EndpointContactData (m N : ℕ) where
  D : ℝ[X]
  solution : Polynomial.PellAbelSolution D
  one_le_m : 1 ≤ m
  m_le_N : m ≤ N
  monic_D : D.Monic
  squarefree_D : Squarefree D
  natDegree_D : D.natDegree = 2 * endpointGenus m + 2
  leadingCoeff_eq : solution.P.leadingCoeff = solution.Q.leadingCoeff
  natDegree_P : solution.P.natDegree = N
  eval_P_one : solution.P.eval 1 = 1
  contact_one : rootMultiplicity 1 (1 - solution.P) = m

namespace EndpointContactData

variable {m N : ℕ} (d : EndpointContactData m N)

theorem D_ne_zero : d.D ≠ 0

theorem P_ne_zero : d.solution.P ≠ 0

theorem Q_ne_zero : d.solution.Q ≠ 0

theorem rootMultiplicity_D_one :
    rootMultiplicity 1 d.D = m % 2

theorem rootMultiplicity_Q_one :
    rootMultiplicity 1 d.solution.Q = m / 2

theorem rootMultiplicity_differentialNumerator_one :
    rootMultiplicity 1 d.solution.differentialNumerator = endpointGenus m

theorem differentialNumerator_eq :
    d.solution.differentialNumerator =
      Polynomial.C (N : ℝ) * (X - Polynomial.C 1) ^ endpointGenus m

theorem derivative_P_eq :
    derivative d.solution.P =
      Polynomial.C (N : ℝ) *
        (X - Polynomial.C 1) ^ endpointGenus m * d.solution.Q

def endpointParityFactor : ℝ[X] :=
  (X - Polynomial.C 1) ^ (m % 2)

def endpointDQuotient : ℝ[X] :=
  d.D / d.endpointParityFactor

theorem endpointParityFactor_dvd :
    d.endpointParityFactor ∣ d.D

theorem endpoint_D_factorization :
    d.endpointParityFactor * d.endpointDQuotient = d.D

theorem eval_endpointDQuotient_one_ne_zero :
    d.endpointDQuotient.eval 1 ≠ 0

def endpointDValue : ℝ := d.endpointDQuotient.eval 1

theorem endpointDValue_ne_zero : d.endpointDValue ≠ 0

theorem endpointDValue_eq_even (hm : Even m) :
    d.endpointDValue = d.D.eval 1

theorem endpointDValue_eq_odd (hm : Odd m) :
    d.endpointDValue = (derivative d.D).eval 1

theorem mthDerivative_P_at_one :
    (derivative^[m] d.solution.P).eval 1 =
      (m.factorial : ℝ) *
        (2 * (N : ℝ) ^ 2 / ((m : ℝ) ^ 2 * d.endpointDValue))

def endpointScale : ℝ :=
  (-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 * d.endpointDValue /
    (2 * (N : ℝ) ^ 2)

theorem endpointScale_ne_zero : d.endpointScale ≠ 0

theorem endpointScale_eq_derivative :
    d.endpointScale =
      (-1 : ℝ) ^ (m + 1) * (m.factorial : ℝ) /
        (derivative^[m] d.solution.P).eval 1

def endpointNumerator : ℝ[X] :=
  Polynomial.C d.endpointScale * (1 - d.solution.P)

theorem endpoint_factor_dvd_numerator :
    (Polynomial.C 1 - X) ^ m ∣ d.endpointNumerator

def endpointQuotient : ℝ[X] :=
  d.endpointNumerator / ((Polynomial.C 1 - X) ^ m)

theorem endpoint_factorization :
    (Polynomial.C 1 - X) ^ m * d.endpointQuotient =
      d.endpointNumerator

theorem endpointQuotient_eval_one :
    d.endpointQuotient.eval 1 = 1

theorem natDegree_endpointQuotient_le :
    d.endpointQuotient.natDegree ≤ N - m

end EndpointContactData

end JoseSmoothest
```

## Detailed natural-language proof blueprint

### Genus arithmetic

Splitting `m` into `2g+1` or `2g+2` proves the two simp lemmas and the parity
identity.  This is the natural-number form of
`g=floor((m-1)/2)`.  Keep these arithmetic lemmas centralized: repeatedly
asking `omega` to rediscover the parity split will make later files fragile.

For the lower bound, the Pell--Abel endpoint valuations show that the
differential numerator `P'/Q` has a zero of order `endpointGenus m` at one.
Its degree is at most the curve genus `g`, so root multiplicity is bounded by
degree and `endpointGenus m ≤ g`.  `EndpointContactData` deliberately assumes
equality through `deg D=2*endpointGenus m+2`; that minimal-genus fact will come
from exhaustion of all critical points by the minimizer's alternation, not
from endpoint contact alone.

### Endpoint valuations

The Pell--Abel valuation theorems apply directly to the exact `m`-fold zero
of `1-P`.  Squarefreeness gives

```text
ord₁ D = m mod 2,
ord₁ Q = m/2,
ord₁(P'/Q) = (m-1)/2.
```

The differential numerator has degree at most `endpointGenus m`.  Its order
at one already equals that degree bound, so it is a scalar multiple of
`(X-1)^g`.  Comparing leading coefficients determines the scalar.  Since
`P` and `Q` have equal nonzero leading coefficients and degrees `N` and
`N-g-1`, the quotient `P'/Q` has leading coefficient `N`.  This proves the
two differential identities.  The equality, rather than monicity, is the
correct orientation condition: already in genus zero the Chebyshev solution
has leading coefficient `2^(N-1)`.

This is why the numerator `(x-1)^g` is not an analytic guess: once a
degree-`N` endpoint-contact Pell solution exists, polynomial algebra forces
it.

### Odd/even factor at one

Squarefreeness and `ord₁D=m mod 2` say that `D` contains `(X-1)` exactly
when `m` is odd.  Divide by the monic parity factor.  Exact multiplicity makes
the quotient nonzero at one.  For even `m`, the factor is one and its endpoint
value is simply `D(1)`.  For odd `m`, differentiating
`D=(X-1)D₁` and evaluating at one gives `D'(1)=D₁(1)`.

If the real-phase file also supplies a simple root at `-1`, these facts refine
to

```text
m=2g+1:  D=(X²-1)H,  deg H=2g,
m=2g+2:  D=(X+1)H,   deg H=2g+1.
```

That interval-specific statement belongs in `AbelianCertificate`, not in the
bare endpoint-contact structure.

### First nonzero endpoint coefficient

Write `t=x-1`, `D=t^ε(d+O(t))`, `Q=t^(m/2)(v+O(t))`, and
`P=1+a t^m+O(t^(m+1))`.  The Pell identity gives

```text
2a = d v².
```

The differential identity gives

```text
m a = N v.
```

Eliminate `v` and use `a≠0` to obtain

```text
a = 2N²/(m²d).
```

Multiplying by `m!` gives `mthDerivative_P_at_one`.  In Lean, prove the same
calculation with polynomial root-multiplicity factorizations and evaluations
at one; formal power series are unnecessary.

### Scale and normalized quotient

The `m`-th derivative at one of `(1-x)^m p(x)` is
`(-1)^m m! p(1)`.  For `scale*(1-P)`, it is
`-scale*P^[m](1)`.  Equating them with `p(1)=1` gives

```text
scale = (-1)^(m+1) m! / P^[m](1)
      = (-1)^(m+1) m²d/(2N²).
```

The exact contact proves divisibility by `(1-X)^m`; polynomial division then
defines the quotient.  The derivative coefficient calculation proves its
value at one is one.  Dividing a degree-`N` numerator by a degree-`m` monic
factor gives degree at most `N-m`.
