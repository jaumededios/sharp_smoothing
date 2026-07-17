# Blueprint for `JoseSmoothest/EvenOrder/PellExtraction.lean`

## Purpose

This purely algebraic module extracts the minimal squarefree Pell--Abel
factor from the endpoint alternant.  It retains the actual extremal
polynomial as the `P` coordinate.  No hyperelliptic surface, path integral,
period, or phase is imported, so this layer can be formalized immediately.

## Imports

```lean
import JoseSmoothest.EvenOrder.EndpointContact
import JoseSmoothest.EvenOrder.EndpointAlternation
```

## Public declarations

`EndpointAlternation` proves the hard exhaustion statement for the normalized
extremizer.  This file packages the endpoint-inclusive result abstractly as
`EndpointAlternant`, defines its interior nodes, and repeats the now-short
generic factorization argument from those structure fields.

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial Real

namespace EndpointAlternant

variable {m N : ℕ} {Z : ℝ[X]} (a : EndpointAlternant m N Z)

def interiorNode (i : Fin (N - m)) : ℝ :=
  a.nodes ⟨i + 1, by omega⟩

theorem interiorNode_mem_Ioo (i : Fin (N - m)) :
    a.interiorNode i ∈ Set.Ioo (-1 : ℝ) 1

theorem interiorNode_injective :
    Function.Injective a.interiorNode

def squareFactor : ℝ[X] :=
  (X - Polynomial.C 1) ^ (m / 2) *
    ∏ i : Fin (N - m), (X - Polynomial.C (a.interiorNode i))

theorem squareFactor_monic : a.squareFactor.Monic

theorem squareFactor_ne_zero : a.squareFactor ≠ 0

theorem natDegree_squareFactor :
    a.squareFactor.natDegree = m / 2 + (N - m)

def leadingScale (_a : EndpointAlternant m N Z) : ℝ := Z.leadingCoeff

theorem leadingScale_ne_zero : a.leadingScale ≠ 0

def Q : ℝ[X] :=
  Polynomial.C a.leadingScale * a.squareFactor

theorem Q_ne_zero : a.Q ≠ 0

theorem natDegree_Q :
    a.Q.natDegree = N - endpointGenus m - 1

theorem leadingCoeff_Q :
    a.Q.leadingCoeff = Z.leadingCoeff

theorem derivative_eq :
    derivative Z =
      Polynomial.C ((N : ℝ) * Z.leadingCoeff) *
        (X - Polynomial.C 1) ^ (m - 1) *
          ∏ i : Fin (N - m),
            (X - Polynomial.C (a.interiorNode i))

theorem derivative_Z_eq :
    derivative Z =
      Polynomial.C (N : ℝ) *
        (X - Polynomial.C 1) ^ endpointGenus m * a.Q

theorem squareFactor_sq_dvd :
    a.squareFactor ^ 2 ∣ Z ^ 2 - 1

def D : ℝ[X] :=
  Polynomial.C ((a.leadingScale ^ 2)⁻¹) *
    ((Z ^ 2 - 1) /ₘ (a.squareFactor ^ 2))

theorem pell_factorization :
    Z ^ 2 - 1 = a.D * a.Q ^ 2

theorem monic_D : a.D.Monic

theorem squarefree_D : Squarefree a.D

theorem natDegree_D :
    a.D.natDegree = 2 * endpointGenus m + 2

theorem rootMultiplicity_Q_one :
    rootMultiplicity 1 a.Q = m / 2

theorem dvd_derivative_of_sq_dvd_sub_one
    {P F : ℝ[X]} (hdiv : F ^ 2 ∣ P ^ 2 - 1) :
    F ∣ derivative P

def solution : Polynomial.PellAbelSolution a.D where
  P := Z
  Q := a.Q
  equation := by rw [sub_eq_iff_eq_add, a.pell_factorization]; ring

theorem rootMultiplicity_D_neg_one :
    rootMultiplicity (-1) a.D = 1

theorem eval_D_neg_one : a.D.eval (-1) = 0

theorem rootMultiplicity_D_one :
    rootMultiplicity 1 a.D = m % 2

theorem neg_D :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, a.D.eval x < 0

theorem nonpos_D :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, a.D.eval x ≤ 0

def contactData : EndpointContactData m N where
  D := a.D
  solution := a.solution
  one_le_m := a.one_le_m
  m_le_N := a.m_le_N
  monic_D := a.monic_D
  squarefree_D := a.squarefree_D
  natDegree_D := a.natDegree_D
  leadingCoeff_eq := by
    simpa [solution] using a.leadingCoeff_Q.symm
  natDegree_P := a.natDegree_eq
  eval_P_one := a.eval_one
  contact_one := a.contact_one

end EndpointAlternant

end JoseSmoothest
```

## Detailed natural-language proof blueprint

### Exhausting the critical points

The endpoint alternant has `N-m` interior nodes.  At each node `Z` attains
`1` or `-1` while remaining in `[-1,1]`, so its derivative vanishes.  Exact
`m`-fold contact at one contributes derivative multiplicity `m-1`.  The
total is `(N-m)+(m-1)=N-1`, exactly the degree of `Z'`.  Thus the listed
roots exhaust the derivative, all interior critical points are simple, and
there are no further real or complex critical points.

Set

```text
S₀=(X-1)^(m/2) ∏_interior (X-x_j).
```

The root at one has the indicated square multiplicity in `Z²-1`; every
interior extremum is an exact double root.  Hence `S₀²` divides `Z²-1`.
If `λ` is the nonzero leading coefficient of `Z`, define

```text
Q = λ S₀,
D = λ⁻² (Z²-1)/S₀².
```

Then `D` is monic, `Z²-DQ²=1`, and `Z,Q` have equal leading
coefficients.

### Degree, squarefreeness, and derivative identity

The square factor has degree `m/2+(N-m)`, hence

```text
deg D = 2N-2(m/2+N-m)
      = m+(m mod 2)
      = 2 endpointGenus(m)+2.
```

A repeated irreducible factor of `D` would leave excess square divisibility
in `Z²-1`.  The key reusable real-polynomial lemma says that

```text
f² ∣ Z²-1  implies  f ∣ Z'.
```

Indeed the displayed divisibility makes `f` coprime to `Z`; differentiate
the identity and cancel the unit `2` and the coprime factor `Z`.  If an
irreducible `p` satisfies `p²∣D`, Pell factorization gives
`(p*S₀)²∣Z²-1`, hence `p*S₀∣Z'`.  The exhausted derivative factorization
cancels `S₀` and forces `p∣(X-1)^endpointGenus(m)`.  Primality makes `p`
associated to `X-1`, contradicting the already computed residual endpoint
multiplicity `m mod 2 < 2`.  This proves squarefreeness entirely in
`ℝ[X]`, including irreducible quadratic factors, without a complexification
detour.  The unremoved real multiplicity is one at `-1`, `m mod 2` at one,
and zero at every interior node.

Use monic division `/ₘ` throughout: `squareFactor_monic` makes exact
division, degree, and leading-coefficient lemmas substantially more direct
than field Euclidean division `/`.

Both `Z'` and `N(X-1)^endpointGenus(m)Q` have the same `N-1` roots with the
same multiplicities and leading coefficient `Nλ`, proving the derivative
identity.

### Sign and contact package

For nonpositivity, suppose `D` were positive somewhere on the closed
interval.  Positivity is open, and every endpoint lies in the closure of the
open interval, so there is an open subinterval inside `(-1,1)` on which `D`
is positive.  The nonzero polynomial `Q` has only finitely many real roots;
choose a point of that subinterval where `Q` does not vanish.  The bound
`|Z|≤1` makes the left side of `Z²-1=DQ²` nonpositive, whereas the right side
is strictly positive, a contradiction.  Thus `D≤0` on `[-1,1]`.

If `D` vanished at an interior point, that point would be a local maximum of
the globally nonpositive polynomial.  Hence both `D` and `D'` would vanish
there, giving root multiplicity at least two.  This contradicts the already
proved squarefreeness of `D`, so `D<0` throughout `(-1,1)`.  This density and
squarefreeness argument avoids a separate classification of every equality
point of `Z`.  The constructed solution, degree, squarefreeness, orientation,
and endpoint contact now populate `EndpointContactData`.
