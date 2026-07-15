# Blueprint for `JoseSmoothest/EvenOrder/Equioscillation.lean`

## Purpose

This module proves that the generic weighted problem has a unique minimizer
and that every minimizer has the full zero--peak alternation needed by
`WeightedMinimax`.  This is the unconditional existence step: no Pell
equation, period, or special function is assumed.  Normalization and critical
point exhaustion continue in `EndpointAlternation.lean`.

## Imports

```lean
import JoseSmoothest.EvenOrder.ActiveSetPerturbation
import JoseSmoothest.EvenOrder.WeightedMinimax
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Polynomial
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

def IsEvenWeightedMinimizer
    (m N : ℕ) (S : ℝ[X]) : Prop :=
  IsAdmissibleEvenWeightedPolynomial m N S ∧
    ∀ p, IsAdmissibleEvenWeightedPolynomial m N p →
      evenWeightedPolynomialNorm m S ≤ evenWeightedPolynomialNorm m p

theorem admissible_eq_one_of_same_order
    {m : ℕ} (hm : 1 ≤ m) {p : ℝ[X]}
    (hp : IsAdmissibleEvenWeightedPolynomial m m p) :
    p = 1

theorem evenWeightedPolynomialNorm_one (m : ℕ) :
    evenWeightedPolynomialNorm m 1 = (2 : ℝ) ^ m

def diagonalEvenZeroPeakCertificate
    (m : ℕ) (hm : 1 ≤ m) :
    EvenZeroPeakCertificate m m
      ((Polynomial.C 1 - Polynomial.X) ^ m) ((2 : ℝ) ^ m)

def diagonalEvenWeightedExtremalData
    (m : ℕ) (hm : 1 ≤ m) :
    EvenWeightedExtremalData m m

theorem exists_evenWeightedMinimizer
    (m N : ℕ) (hm : 1 ≤ m) (hN : m ≤ N) :
    ∃ S, IsEvenWeightedMinimizer m N S

theorem evenWeightedPolynomialNorm_pos_of_admissible
    {m N : ℕ} (hm : 1 ≤ m) {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S) :
    0 < evenWeightedPolynomialNorm m S

theorem not_isEvenWeightedMinimizer_of_separator
    {m N : ℕ} (hm : 1 ≤ m) (hN : m < N)
    {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S)
    (hsep : StrictPolynomialSeparator (N - m)
      (zeroActiveSet S) (peakActiveSet m S)) :
    ¬ IsEvenWeightedMinimizer m N S

theorem nonempty_evenZeroPeakCertificate_of_minimizer
    {m N : ℕ} (hm : 1 ≤ m) (hN : m ≤ N)
    {S : ℝ[X]} (hS : IsEvenWeightedMinimizer m N S) :
    Nonempty (EvenZeroPeakCertificate m N
      (evenWeightedNumerator m S)
      (evenWeightedPolynomialNorm m S))

noncomputable def evenZeroPeakCertificate_of_minimizer
    {m N : ℕ} (hm : 1 ≤ m) (hN : m ≤ N)
    {S : ℝ[X]} (hS : IsEvenWeightedMinimizer m N S) :
    EvenZeroPeakCertificate m N
      (evenWeightedNumerator m S)
      (evenWeightedPolynomialNorm m S) :=
  Classical.choice
    (nonempty_evenZeroPeakCertificate_of_minimizer hm hN hS)

theorem exists_evenWeightedExtremalData
    (m N : ℕ) (hm : 1 ≤ m) (hN : m ≤ N) :
    Nonempty (EvenWeightedExtremalData m N)

theorem existsUnique_evenWeightedMinimizer
    (m N : ℕ) (hm : 1 ≤ m) (hN : m ≤ N) :
    ∃! S, IsEvenWeightedMinimizer m N S

end JoseSmoothest
```

## Detailed natural-language proof blueprint

### Compact minimizer existence

Put `d=N-m` and identify polynomials of degree at most `d` with coefficient
vectors `Fin (d+1) → ℝ`.  The constant polynomial one is feasible and has
norm `2^m`, so it suffices to minimize on the feasible sublevel with norm at
most `2^m`.

Choose `d+1` distinct interpolation nodes in `[-1,0]`, for example

```text
x_i = -1 + i/(d+1).
```

At these nodes `(1-x_i)^m≥1`.  Feasibility and the sublevel bound therefore
bound every `p(x_i)`.  Evaluation at distinct nodes is a Vandermonde linear
equivalence, so the coefficient vectors are bounded.  Polynomial evaluation,
the nonnegativity constraints, normalization, and the weighted supremum norm
are continuous in this finite-dimensional space.  Hence the feasible
sublevel is closed and bounded, therefore compact.  Weierstrass gives a
minimizer.

For `N=m`, the only feasible polynomial is one.  The explicit diagonal
certificate has its unique node at `-1`, orientation `-1`, and peak `2^m`.
Split this case before all separator arguments.

### Active sets

For an admissible `S`, the norm is positive: continuity at `1` gives nearby
points where `S>0`, while `(1-x)^m>0` to the left of one.  The weighted
numerator is nonnegative, so compactness says its maximum is exactly the
weighted norm and is attained.

The zero active set is finite because `S(1)=1` makes `S` nonzero.  The peak
active set is finite because its defining polynomial is not constant: it is
zero at `1`, while its positive maximum is attained elsewhere.  The sets are
disjoint and the peak set is nonempty.

### A separator improves the minimizer

`ActiveSetPerturbation` proves the needed strict improvement.  Concretely,
let `r` be negative on zeros of `S` and positive at every peak of its weighted
numerator, and perturb by

```text
Sε = S + ε (X-1) r.
```

The extra factor preserves `Sε(1)=1`, and `deg r<N-m` preserves the degree
bound.  Near a zero of `S`, the perturbation is positive because `x-1<0` and
`r<0`.  Away from small neighborhoods of the finite zero set, compactness
gives a uniform positive lower bound for `S`.  Thus sufficiently small
positive `ε` preserves nonnegativity.

For the weighted numerator the perturbation is

```text
-ε (1-x)^(m+1) r(x).
```

It is strictly negative near every peak.  Away from peak neighborhoods the
old numerator has a uniform gap below its maximum.  Shrinking the same `ε`
again makes the new numerator everywhere strictly below the old maximum.
This contradicts minimality.  The perturbation module explicitly chooses the
minimum of the finitely many local and two compact-complement margins; a
pointwise `ε` is not sufficient.

### Necessity of alternation

Apply `finite_alternation_or_separator` to the zero and peak active sets with
`d=N-m`.  The separator branch contradicts the perturbation theorem, leaving
`d+1` strictly increasing alternating active points.  Since the dichotomy is
Prop-valued while a certificate carries data, the proof first returns
`Nonempty (EvenZeroPeakCertificate ...)`; a separate noncomputable definition
chooses one.  At a zero of `S` the
weighted numerator is zero, and at a peak it equals the norm.  Translating
the two labels into `0` and `M` populates `EvenZeroPeakCertificate`.

The sufficient theorem from `WeightedMinimax` now shows that any two
minimizers coincide.  Pair the chosen minimizer with its certificate to get
`EvenWeightedExtremalData`.
