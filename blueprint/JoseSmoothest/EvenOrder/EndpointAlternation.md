# Blueprint for `JoseSmoothest/EvenOrder/EndpointAlternation.lean`

## Purpose

This algebraic module normalizes generic extremal data to a polynomial `Z`
bounded by one, proves that the first alternation node is `-1`, exhausts all
critical points, and appends the endpoint `1`.  Its resulting
`EndpointAlternant` is the exact input to `PellExtraction`.

## Imports

```lean
import JoseSmoothest.EvenOrder.Equioscillation
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

structure EndpointAlternant
    (m N : ℕ) (Z : ℝ[X]) where
  one_le_m : 1 ≤ m
  m_le_N : m ≤ N
  natDegree_eq : Z.natDegree = N
  bounds : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    -1 ≤ Z.eval x ∧ Z.eval x ≤ 1
  eval_one : Z.eval 1 = 1
  contact_one : rootMultiplicity 1 (1 - Z) = m
  orientation : ℝ
  orientation_eq : orientation = 1 ∨ orientation = -1
  nodes : Fin (N - m + 2) → ℝ
  strictMono_nodes : StrictMono nodes
  node_zero : nodes 0 = -1
  node_last : nodes (Fin.last (N - m + 1)) = 1
  node_value : ∀ j,
    Z.eval (nodes j) =
      orientation * (-1 : ℝ) ^ (j : ℕ)

namespace EvenWeightedExtremalData

variable {m N : ℕ} (E : EvenWeightedExtremalData m N)

def normalizedAlternant : ℝ[X] :=
  1 - Polynomial.C (2 / E.M) * E.q

theorem M_pos (hm : 1 ≤ m) (hN : m ≤ N) : 0 < E.M

def interiorCertificateNode (i : Fin (N - m)) : ℝ :=
  E.certificate.nodes i.succ

theorem normalizedAlternant_natDegree_eq
    (hm : 1 ≤ m) (hN : m ≤ N) :
    E.normalizedAlternant.natDegree = N

theorem normalizedAlternant_derivative_eq
    (hm : 1 ≤ m) (hN : m ≤ N) :
    derivative E.normalizedAlternant =
      C ((N : ℝ) * E.normalizedAlternant.leadingCoeff) *
        (X - C 1) ^ (m - 1) *
          ∏ i : Fin (N - m),
            (X - C (E.interiorCertificateNode i))

def endpointAlternant
    (hm : 1 ≤ m) (hN : m ≤ N) :
    EndpointAlternant m N E.normalizedAlternant

end EvenWeightedExtremalData

end JoseSmoothest
```

## Detailed natural-language proof blueprint

Set `Z=1-2q/M`.  Positivity of `M` and the certificate bound `0≤q≤M`
give `-1≤Z≤1`.  Since `q=(1-X)^mS` and `S(1)=1`, the polynomial
`1-Z` has exact multiplicity `m` at one.  The certificate nodes have values
`orientation*(-1)^j` for `Z`.

Every certificate node in the open interval is a local extremum of `Z`, so
the polynomial derivative vanishes there.  Endpoint contact makes `Z'`
vanish at one to multiplicity `m-1`.  If the first certificate node were
strictly greater than `-1`, all `N-m+1` certificate nodes would be interior;
together with the endpoint multiplicity they would give at least `N`
derivative roots.  But `deg Z≤N`, so `deg Z'≤N-1`, a contradiction.
Therefore the first node is exactly `-1`.

The remaining `N-m` nodes are interior.  Their distinct linear factors,
together with `(X-1)^(m-1)`, divide `Z'` and have total degree `N-1`.
Consequently `deg Z=N`; this factorization exhausts `Z'`, every interior
critical root is simple, and there are no other complex critical roots.  The
public `normalizedAlternant_derivative_eq` records the resulting exact
factorization, including its leading coefficient, for the Pell extraction
layer.

The endpoint value cannot equal the last certificate value: if both values
were `1`, Rolle's theorem would produce another derivative root strictly
between the last node and `1`.  The exhausted derivative factorization says
that every root is either an earlier interior certificate node or the endpoint
itself, a contradiction in either case.  Hence the last certificate value is
`-1`.  Append `1` to the existing node family.  This yields `N-m+2` strictly
increasing endpoint-inclusive nodes with the required alternating values and
completes `EndpointAlternant`.
