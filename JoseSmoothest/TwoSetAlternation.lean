import JoseSmoothest.Alternation
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Alternation or strict polynomial separation

This file isolates the finite combinatorial argument used by the weighted
equioscillation theorem.  After sorting the union of two finite sets, the
number of changes between their labels either supplies enough alternating
nodes or bounds the degree of a product of linear factors placed between
successive runs.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

/-- A strictly ordered family whose membership alternates between two sets. -/
structure AlternatingMembership
    (k : ℕ) (A B : Set ℝ) where
  orientation : ℝ
  orientation_eq : orientation = 1 ∨ orientation = -1
  nodes : Fin k → ℝ
  strictMono_nodes : StrictMono nodes
  node_mem : ∀ i : Fin k,
    (orientation * (-1 : ℝ) ^ (i : ℕ) = 1 ∧ nodes i ∈ A) ∨
    (orientation * (-1 : ℝ) ^ (i : ℕ) = -1 ∧ nodes i ∈ B)

/-- A polynomial of degree below `d` which has strict opposite signs on two sets. -/
structure StrictPolynomialSeparator
    (d : ℕ) (A B : Set ℝ) where
  polynomial : ℝ[X]
  natDegree_lt : polynomial.natDegree < d
  negative_on_first : ∀ x ∈ A, polynomial.eval x < 0
  positive_on_second : ∀ x ∈ B, 0 < polynomial.eval x

private def labelSign (b : Bool) : ℝ := if b then 1 else -1

private lemma labelSign_eq_one_or_neg_one (b : Bool) :
    labelSign b = 1 ∨ labelSign b = -1 := by
  cases b <;> simp [labelSign]

private lemma labelSign_sq (b : Bool) : labelSign b * labelSign b = 1 := by
  cases b <;> simp [labelSign]

private lemma labelSign_ne_zero (b : Bool) : labelSign b ≠ 0 := by
  cases b <;> simp [labelSign]

private lemma labelSign_eq_neg_of_ne {a b : Bool} (h : a ≠ b) :
    labelSign a = -labelSign b := by
  cases a <;> cases b <;> simp_all [labelSign]

/-- The number of changes of a Boolean label along a list. -/
private def transitionCount (label : α → Bool) : List α → ℕ
  | [] | [_] => 0
  | x :: y :: xs =>
      (if label x = label y then 0 else 1) + transitionCount label (y :: xs)

/-- A family beginning in the first label of a list and alternating thereafter. -/
private structure AlternatingPrefix
    (label : ℝ → Bool) (n : ℕ) (x : ℝ) (xs : List ℝ) where
  nodes : Fin (n + 1) → ℝ
  strictMono_nodes : StrictMono nodes
  node_mem : ∀ i, nodes i ∈ x :: xs
  label_eq : ∀ i,
    labelSign (label (nodes i)) = labelSign (label x) * (-1 : ℝ) ^ (i : ℕ)

private lemma strictMono_fin_cons
    {n : ℕ} {a : ℝ} {f : Fin (n + 1) → ℝ}
    (hf : StrictMono f) (ha : a < f 0) :
    StrictMono (Fin.cons a f) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using ha
  · simpa using hf Fin.castSucc_lt_succ

private lemma alternatingPrefix_of_le_transitionCount
    (label : ℝ → Bool) :
    ∀ (x : ℝ) (xs : List ℝ),
      (x :: xs).Pairwise (· < ·) →
      ∀ n, n ≤ transitionCount label (x :: xs) →
        Nonempty (AlternatingPrefix label n x xs) := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      intro hsorted n hn
      have hn0 : n = 0 := by
        simpa [transitionCount] using hn
      subst n
      refine ⟨{
        nodes := fun _ ↦ x
        strictMono_nodes := ?_
        node_mem := ?_
        label_eq := ?_
      }⟩
      · intro i j hij
        omega
      · intro i
        simp
      · intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        simp
  | cons y ys ih =>
      intro hsorted n hn
      have hxy : x < y := (List.pairwise_cons.mp hsorted).1 y (by simp)
      have htail : List.Pairwise (· < ·) (y :: ys) := (List.pairwise_cons.mp hsorted).2
      by_cases hlabel : label x = label y
      · have hn' : n ≤ transitionCount label (y :: ys) := by
          simpa [transitionCount, hlabel] using hn
        let p := (ih y htail n hn').some
        refine ⟨{
          nodes := p.nodes
          strictMono_nodes := p.strictMono_nodes
          node_mem := ?_
          label_eq := ?_
        }⟩
        · intro i
          exact List.mem_cons_of_mem x (p.node_mem i)
        · intro i
          rw [p.label_eq, hlabel]
      · cases n with
        | zero =>
            refine ⟨{
              nodes := fun _ ↦ x
              strictMono_nodes := ?_
              node_mem := ?_
              label_eq := ?_
            }⟩
            · intro i j hij
              omega
            · intro i
              simp
            · intro i
              have hi : i = 0 := Fin.eq_zero i
              subst i
              simp
        | succ n =>
            have hn' : n ≤ transitionCount label (y :: ys) := by
              have : n < 1 + transitionCount label (y :: ys) := by
                simpa [transitionCount, hlabel] using hn
              omega
            let p := (ih y htail n hn').some
            have hxnodes : x < p.nodes 0 := by
              exact (List.pairwise_cons.mp hsorted).1 (p.nodes 0) (p.node_mem 0)
            refine ⟨{
              nodes := Fin.cons x p.nodes
              strictMono_nodes := strictMono_fin_cons p.strictMono_nodes hxnodes
              node_mem := ?_
              label_eq := ?_
            }⟩
            · intro i
              refine Fin.cases ?_ (fun j ↦ ?_) i
              · simp
              · simp only [Fin.cons_succ]
                exact List.mem_cons_of_mem x (p.node_mem j)
            · intro i
              refine Fin.cases ?_ (fun j ↦ ?_) i
              · simp
              · simp only [Fin.cons_succ, Fin.val_succ]
                rw [p.label_eq, labelSign_eq_neg_of_ne hlabel]
                have hpow : (-1 : ℝ) ^ ((j : ℕ) + 1) =
                    -((-1 : ℝ) ^ (j : ℕ)) := by
                  rw [pow_succ]
                  ring
                rw [hpow]
                ring

/-- The product separator, with one root at the midpoint of each label change. -/
private def separatorPolynomial (label : ℝ → Bool) : List ℝ → ℝ[X]
  | [] => 0
  | [x] => C (labelSign (label x))
  | x :: y :: xs =>
      if label x = label y then
        separatorPolynomial label (y :: xs)
      else
        (X - C ((x + y) / 2)) * separatorPolynomial label (y :: xs)

private lemma separatorPolynomial_sign
    (label : ℝ → Bool) :
    ∀ (x : ℝ) (xs : List ℝ),
      (x :: xs).Pairwise (· < ·) →
      (∀ z ∈ x :: xs,
          0 < labelSign (label z) * (separatorPolynomial label (x :: xs)).eval z) ∧
        (∀ z ≤ x,
          0 < labelSign (label x) * (separatorPolynomial label (x :: xs)).eval z) := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      intro hsorted
      constructor
      · intro z hz
        simp only [List.mem_singleton] at hz
        subst z
        simp [separatorPolynomial, labelSign_sq]
      · intro z hz
        simp [separatorPolynomial, labelSign_sq]
  | cons y ys ih =>
      intro hsorted
      have hxy : x < y := (List.pairwise_cons.mp hsorted).1 y (by simp)
      have htail : List.Pairwise (· < ·) (y :: ys) := (List.pairwise_cons.mp hsorted).2
      obtain ⟨htail_sign, htail_left⟩ := ih y htail
      by_cases hlabel : label x = label y
      · constructor
        · intro z hz
          rw [separatorPolynomial, if_pos hlabel]
          simp only [List.mem_cons] at hz
          rcases hz with (rfl | hz)
          · rw [hlabel]
            exact htail_left z hxy.le
          · exact htail_sign z (by simpa using hz)
        · intro z hz
          rw [separatorPolynomial, if_pos hlabel, hlabel]
          exact htail_left z (hz.trans hxy.le)
      · have hsign : labelSign (label x) = -labelSign (label y) :=
          labelSign_eq_neg_of_ne hlabel
        constructor
        · intro z hz
          rw [separatorPolynomial, if_neg hlabel, eval_mul, eval_sub, eval_X, eval_C]
          simp only [List.mem_cons] at hz
          rcases hz with (rfl | hz)
          · have hmid : z - (z + y) / 2 < 0 := by linarith
            have hp := htail_left z hxy.le
            rw [hsign]
            have hprod := mul_pos_of_neg_of_neg hmid (neg_neg_of_pos hp)
            simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
          · have hyz : y ≤ z := by
              rcases hz with (rfl | hz)
              · exact le_rfl
              · exact ((List.pairwise_cons.mp htail).1 z hz).le
            have hmid : 0 < z - (x + y) / 2 := by linarith
            have hp := htail_sign z (by simpa using hz)
            have hprod := mul_pos hmid hp
            simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
        · intro z hz
          rw [separatorPolynomial, if_neg hlabel, eval_mul, eval_sub, eval_X, eval_C, hsign]
          have hmid : z - (x + y) / 2 < 0 := by linarith
          have hp := htail_left z (hz.trans hxy.le)
          have hprod := mul_pos_of_neg_of_neg hmid (neg_neg_of_pos hp)
          simpa [mul_assoc, mul_left_comm, mul_comm] using hprod

private lemma separatorPolynomial_natDegree_le
    (label : ℝ → Bool) : ∀ (xs : List ℝ),
    (separatorPolynomial label xs).natDegree ≤ transitionCount label xs := by
  intro xs
  induction xs with
  | nil => simp [separatorPolynomial, transitionCount]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [separatorPolynomial, transitionCount]
      | cons y ys =>
          by_cases hlabel : label x = label y
          · simpa [separatorPolynomial, transitionCount, hlabel] using ih
          · rw [separatorPolynomial, if_neg hlabel, transitionCount, if_neg hlabel]
            calc
              ((X - C ((x + y) / 2)) * separatorPolynomial label (y :: ys)).natDegree
                  ≤ (X - C ((x + y) / 2)).natDegree +
                    (separatorPolynomial label (y :: ys)).natDegree := natDegree_mul_le
              _ ≤ 1 + transitionCount label (y :: ys) := by
                have hlin : (X - C ((x + y) / 2) : ℝ[X]).natDegree = 1 :=
                  natDegree_X_sub_C _
                rw [hlin]
                omega

/-- Two disjoint finite subsets of the line either contain `d + 1`
alternating points, or have a strict separator of degree below `d`. -/
theorem finite_alternation_or_separator
    (d : ℕ) {A B : Set ℝ}
    (hA : A.Finite) (hB : B.Finite)
    (hdisjoint : Disjoint A B) (hB_nonempty : B.Nonempty) :
    Nonempty (AlternatingMembership (d + 1) A B) ∨
      Nonempty (StrictPolynomialSeparator d A B) := by
  classical
  let points : Finset ℝ := hA.toFinset ∪ hB.toFinset
  let xs : List ℝ := points.sort
  let label : ℝ → Bool := fun x ↦ decide (x ∈ B)
  have hsorted : xs.Pairwise (· < ·) := by
    exact points.sortedLT_sort.pairwise
  have hxs_nonempty : xs ≠ [] := by
    obtain ⟨b, hb⟩ := hB_nonempty
    have hbpoints : b ∈ points := by simp [points, hb]
    intro hnil
    have : b ∈ xs := by simpa [xs] using hbpoints
    simp [hnil] at this
  cases hxs_eq : xs with
  | nil => exact (hxs_nonempty hxs_eq).elim
  | cons x rest =>
    have hsorted' : List.Pairwise (· < ·) (x :: rest) := by
      simpa [hxs_eq] using hsorted
    by_cases hmany : d ≤ transitionCount label (x :: rest)
    · left
      let p := (alternatingPrefix_of_le_transitionCount label x rest hsorted' d hmany).some
      let orientation := -labelSign (label x)
      refine ⟨{
        orientation := orientation
        orientation_eq := ?_
        nodes := p.nodes
        strictMono_nodes := p.strictMono_nodes
        node_mem := ?_
      }⟩
      · rcases labelSign_eq_one_or_neg_one (label x) with h | h
        · right
          simp [orientation, h]
        · left
          simp [orientation, h]
      · intro i
        have hmem_points : p.nodes i ∈ points := by
          have hmem_list := p.node_mem i
          have : p.nodes i ∈ xs := by simpa [hxs_eq] using hmem_list
          simpa [xs] using this
        have hAB : p.nodes i ∈ A ∨ p.nodes i ∈ B := by
          simpa [points] using hmem_points
        have horient : orientation * (-1 : ℝ) ^ (i : ℕ) =
            -labelSign (label (p.nodes i)) := by
          rw [p.label_eq]
          simp only [orientation]
          have hsquare : ((-1 : ℝ) ^ (i : ℕ)) *
              ((-1 : ℝ) ^ (i : ℕ)) = 1 := by
            rw [← pow_add, ← two_mul, pow_mul]
            norm_num
          nlinarith
        by_cases hnodeB : p.nodes i ∈ B
        · right
          constructor
          · rw [horient]
            simp [label, hnodeB, labelSign]
          · exact hnodeB
        · left
          constructor
          · rw [horient]
            simp [label, hnodeB, labelSign]
          · exact hAB.resolve_right hnodeB
    · right
      have hdegree : (separatorPolynomial label (x :: rest)).natDegree < d :=
        (separatorPolynomial_natDegree_le label (x :: rest)).trans_lt (Nat.lt_of_not_ge hmany)
      obtain ⟨hsign, -⟩ := separatorPolynomial_sign label x rest hsorted'
      refine ⟨{
        polynomial := separatorPolynomial label (x :: rest)
        natDegree_lt := hdegree
        negative_on_first := ?_
        positive_on_second := ?_
      }⟩
      · intro a ha
        have ha_not_B : a ∉ B := Set.disjoint_left.mp hdisjoint ha
        have ha_mem : a ∈ x :: rest := by
          have : a ∈ points := by simp [points, ha]
          have : a ∈ xs := by simpa [xs] using this
          simpa [hxs_eq] using this
        have hp := hsign a ha_mem
        simp [label, ha_not_B, labelSign] at hp
        linarith
      · intro b hb
        have hb_mem : b ∈ x :: rest := by
          have : b ∈ points := by simp [points, hb]
          have : b ∈ xs := by simpa [xs] using this
          simpa [hxs_eq] using this
        have hp := hsign b hb_mem
        simpa [label, hb, labelSign] using hp

end JoseSmoothest
