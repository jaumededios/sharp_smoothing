# Blueprint for `JoseSmoothest/EvenOrder/WeightedMinimax.lean`

## Purpose

This module develops the order-independent weighted polynomial problem and
the sufficient zero--peak certificate.  It is the generic version of the
existing cubic argument in `SixthOrder.lean`.  Existence and necessity of a
certificate are deferred to `Equioscillation.lean`.

The smoothing difference order is `2*m`, while `N` is the degree before
removing the endpoint factor.  Thus admissible quotients have degree at most
`N-m`.

## Imports

```lean
import JoseSmoothest.Alternation
import JoseSmoothest.Chebyshev
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

def evenWeightedNumerator (m : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (Polynomial.C 1 - Polynomial.X) ^ m * p

def evenWeightedPolynomialNorm (m : ℕ) (p : ℝ[X]) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    r = |(1 - x) ^ m * p.eval x|}

theorem evenWeightedValue_le_norm
    (m : ℕ) (p : ℝ[X]) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(1 - x) ^ m * p.eval x| ≤ evenWeightedPolynomialNorm m p

theorem evenWeightedPolynomialNorm_nonneg (m : ℕ) (p : ℝ[X]) :
    0 ≤ evenWeightedPolynomialNorm m p

structure IsAdmissibleEvenWeightedPolynomial
    (m N : ℕ) (p : ℝ[X]) : Prop where
  degree_le : p.natDegree ≤ N - m
  nonnegative : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x
  eval_one : p.eval 1 = 1

structure EvenZeroPeakCertificate
    (m N : ℕ) (q : ℝ[X]) (M : ℝ) where
  orientation : ℝ
  orientation_eq : orientation = 1 ∨ orientation = -1
  nodes : Fin (N - m + 1) → ℝ
  strictMono_nodes : StrictMono nodes
  nodes_mem_Ico : ∀ i, nodes i ∈ Set.Ico (-1 : ℝ) 1
  bounds : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    0 ≤ q.eval x ∧ q.eval x ≤ M
  exists_peak : ∃ x ∈ Set.Icc (-1 : ℝ) 1, q.eval x = M
  node_value : ∀ i,
    q.eval (nodes i) =
      M / 2 * (1 - orientation * (-1 : ℝ) ^ (i : ℕ))

structure EvenWeightedExtremalData (m N : ℕ) where
  S : ℝ[X]
  q : ℝ[X]
  M : ℝ
  admissible : IsAdmissibleEvenWeightedPolynomial m N S
  factorization : evenWeightedNumerator m S = q
  certificate : EvenZeroPeakCertificate m N q M

namespace EvenWeightedExtremalData

variable {m N : ℕ} (E : EvenWeightedExtremalData m N)

theorem norm_eq : evenWeightedPolynomialNorm m E.S = E.M

theorem M_nonneg : 0 ≤ E.M

end EvenWeightedExtremalData

theorem evenWeightedPolynomialNorm_eq_of_certificate
    {m N : ℕ} {S q : ℝ[X]} {M : ℝ}
    (hSq : evenWeightedNumerator m S = q)
    (certificate : EvenZeroPeakCertificate m N q M) :
    evenWeightedPolynomialNorm m S = M

theorem evenWeightedPolynomial_eq_of_norm_le
    (m N : ℕ) (hN : m ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleEvenWeightedPolynomial m N p)
    (hS : IsAdmissibleEvenWeightedPolynomial m N S)
    (hSq : evenWeightedNumerator m S = q)
    (certificate : EvenZeroPeakCertificate m N q M)
    (hnorm : evenWeightedPolynomialNorm m p ≤ M) :
    p = S

theorem evenWeightedPolynomialNorm_ge_of_certificate
    (m N : ℕ) (hN : m ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleEvenWeightedPolynomial m N p)
    (hS : IsAdmissibleEvenWeightedPolynomial m N S)
    (hSq : evenWeightedNumerator m S = q)
    (certificate : EvenZeroPeakCertificate m N q M) :
    M ≤ evenWeightedPolynomialNorm m p

theorem evenWeightedPolynomialNorm_eq_iff_of_certificate
    (m N : ℕ) (hN : m ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleEvenWeightedPolynomial m N p)
    (hS : IsAdmissibleEvenWeightedPolynomial m N S)
    (hSq : evenWeightedNumerator m S = q)
    (certificate : EvenZeroPeakCertificate m N q M) :
    evenWeightedPolynomialNorm m p = M ↔ p = S

end JoseSmoothest
```

## Detailed natural-language proof blueprint

### Weighted norm

The range in the supremum is nonempty (evaluate at zero) and bounded above:
it is the image of `[-1,1]` under the continuous function
`x ↦ |(1-x)^m p(x)|`.  Compactness therefore gives the pointwise bound.
The range consists of nonnegative values, which proves nonnegativity of the
supremum.

### Norm of a certified candidate

Evaluating `evenWeightedNumerator m S=q` gives

```text
(1-x)^m S(x)=q(x).
```

The certificate places this value between zero and `M`, and says `M` is
attained.  Thus `M` is both an upper bound and an element of the range
defining the norm.  The two `csSup` inequalities prove equality.

### Uniqueness below the certified peak

Let `d=p-S`.  Normalization at one gives `d(1)=0`, so

```text
p-S=(X-1)r.
```

The degree bounds imply `deg r < N-m`.  At a certificate node `x<1`,

```text
(1-x)^m p(x)-q(x)=-(1-x)^(m+1) r(x).
```

The last factor before `r(x)` is strictly positive.  At a zero node,
nonnegativity of `p` gives one weak sign of `r`; at a peak node, the assumed
norm bound gives the opposite sign.  Multiplying `r` by minus the certificate
orientation produces

```text
0 ≤ (-1)^i t(nodes i).
```

There are `N-m+1` strictly increasing nodes and `deg t<N-m`.
`polynomial_eq_zero_of_alternating_signs` forces `t=0`.  The orientation is
nonzero, hence `r=0` and `p=S`.

When `N=m`, both admissible polynomials have degree zero and value one, so
they are the constant polynomial one.  Split this boundary case before
using `divByMonic`; no artificial positivity assumption on `m` is needed for
the sufficient-certificate theorem.

### Lower bound and equality

If an admissible polynomial had norm strictly below `M`, the uniqueness
theorem would identify it with the candidate, contradicting the already
computed norm.  This proves the lower bound.  The same uniqueness implication
and the candidate norm give the equality equivalence.
