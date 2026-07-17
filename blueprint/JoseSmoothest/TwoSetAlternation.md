# Blueprint for `JoseSmoothest/TwoSetAlternation.lean`

## Purpose

This reusable finite-dimensional lemma is the combinatorial engine behind
the necessary equioscillation theorem.  Two disjoint finite subsets of the
real line either contain a prescribed number of alternating points, or a
polynomial of correspondingly small degree has strict opposite signs on the
two sets.  The statement is independent of smoothing and weighted norms.

## Imports

```lean
import JoseSmoothest.Alternation
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

structure AlternatingMembership
    (k : ℕ) (A B : Set ℝ) where
  orientation : ℝ
  orientation_eq : orientation = 1 ∨ orientation = -1
  nodes : Fin k → ℝ
  strictMono_nodes : StrictMono nodes
  node_mem : ∀ i,
    (orientation * (-1 : ℝ) ^ (i : ℕ) = 1 ∧ nodes i ∈ A) ∨
    (orientation * (-1 : ℝ) ^ (i : ℕ) = -1 ∧ nodes i ∈ B)

structure StrictPolynomialSeparator
    (d : ℕ) (A B : Set ℝ) where
  polynomial : ℝ[X]
  natDegree_lt : polynomial.natDegree < d
  negative_on_first : ∀ x ∈ A, polynomial.eval x < 0
  positive_on_second : ∀ x ∈ B, 0 < polynomial.eval x

theorem finite_alternation_or_separator
    (d : ℕ) {A B : Set ℝ}
    (hA : A.Finite) (hB : B.Finite)
    (hdisjoint : Disjoint A B) (hB_nonempty : B.Nonempty) :
    Nonempty (AlternatingMembership (d + 1) A B) ∨
      Nonempty (StrictPolynomialSeparator d A B)

end JoseSmoothest
```

## Detailed natural-language proof blueprint

### Sort the active points

Replace `A` and `B` by finite sets and sort their disjoint union in strictly
increasing order.  Label each point by the Boolean recording whether it came
from `A` or `B`.  Disjointness makes the label unambiguous.  Compress the
ordered labelled list into maximal constant-label runs.

If the list has at least `d+1` runs, choose one point from each of the first
`d+1` runs.  Consecutive chosen points have opposite labels and remain
strictly ordered.  Choose the orientation according to the label of the
first point.  These data give `AlternatingMembership (d+1) A B`.

The case `d=0` is included here: nonemptiness of `B` supplies the unique node
of a one-point alternating family.

### Construct the separator

Suppose there are at most `d` runs.  Between every two consecutive runs,
choose the midpoint of the last point of the left run and the first point of
the right run.  These midpoints are strictly ordered and lie outside
`A∪B`.  Form the product

```text
r(X) = c ∏_j (X - midpoint_j).
```

There is one factor per change of label, hence fewer than `d` factors.  The
sign of this product is constant on each run and flips at every chosen
midpoint, exactly when the label changes.  Choose `c=1` or `c=-1` so the
product is negative on `A` and positive on `B`.  This is the required strict
separator.

### Lean implementation notes

Keep three private lemmas in this file: increasing enumeration of a finite
subset of a linear order, the run-count/alternating-subsequence dichotomy for
a Boolean-labelled list, and the sign of a product of ordered linear factors.
The public theorem should not expose the particular enumeration or midpoint
choices.  Its strict inequalities are essential: the later perturbation
argument obtains uniform margins from them.
