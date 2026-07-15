# Blueprint for `JoseSmoothest/EvenOrder/ActiveSetPerturbation.lean`

## Purpose

This module is the analytic finite-dimensional complement to
`TwoSetAlternation`: a strict polynomial separator between the zero and peak
active sets produces a feasible perturbation with strictly smaller weighted
norm.  It does not define or construct a minimizer.

## Imports

```lean
import JoseSmoothest.TwoSetAlternation
import JoseSmoothest.EvenOrder.WeightedMinimax
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

def zeroActiveSet (S : ℝ[X]) : Set ℝ :=
  {x ∈ Set.Icc (-1 : ℝ) 1 | S.eval x = 0}

def peakActiveSet (m : ℕ) (S : ℝ[X]) : Set ℝ :=
  {x ∈ Set.Icc (-1 : ℝ) 1 |
    (evenWeightedNumerator m S).eval x =
      evenWeightedPolynomialNorm m S}

theorem zeroActiveSet_finite
    {m N : ℕ} {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S) :
    (zeroActiveSet S).Finite

theorem peakActiveSet_finite
    {m N : ℕ} (hm : 1 ≤ m) {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S) :
    (peakActiveSet m S).Finite

theorem peakActiveSet_nonempty
    {m N : ℕ} (hm : 1 ≤ m) {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S) :
    (peakActiveSet m S).Nonempty

theorem activeSets_disjoint
    {m N : ℕ} (hm : 1 ≤ m) {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S) :
    Disjoint (zeroActiveSet S) (peakActiveSet m S)

theorem exists_strict_weighted_improvement_of_separator
    {m N : ℕ} (hm : 1 ≤ m) (hN : m < N)
    {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S)
    (hsep : StrictPolynomialSeparator (N - m)
      (zeroActiveSet S) (peakActiveSet m S)) :
    ∃ p : ℝ[X],
      IsAdmissibleEvenWeightedPolynomial m N p ∧
        evenWeightedPolynomialNorm m p < evenWeightedPolynomialNorm m S

end JoseSmoothest
```

## Detailed natural-language proof blueprint

The zero set is finite because `S(1)=1`, so `S` is nonzero.  The peak is
positive and attained on the compact interval.  The peak set is the root set
of `evenWeightedNumerator m S - C M`; this polynomial is nonzero because it
vanishes at one while `M>0`, so the peak set is finite and nonempty.  A point
cannot be both a zero of `S` and a positive peak, proving disjointness.

For a separator `r`, perturb by

```text
pε = S + ε (X-1) r.
```

The factor `X-1` preserves normalization, and `deg r<N-m` preserves the
degree bound.  Near every zero of `S`, `r<0` and `x-1<0`, so the perturbation
is positive.  On the compact complement of small neighborhoods of the finite
zero set, `S` has a uniform positive minimum.  Thus every sufficiently small
positive `ε` preserves nonnegativity.

The weighted numerator changes by

```text
-ε (1-x)^(m+1) r(x).
```

This is uniformly negative near the finite peak set because `r>0` there and
peaks lie strictly left of one.  On the compact complement of those
neighborhoods, the old numerator has a uniform gap below `M`.  Choose one
positive `ε` below all feasibility and improvement bounds.  The new
polynomial is admissible and its nonnegative weighted numerator is everywhere
strictly below `M`; compactness then gives a weighted norm strictly below the
old norm.
