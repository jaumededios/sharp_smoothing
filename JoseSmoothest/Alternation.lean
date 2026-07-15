import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# A weak alternation principle for real polynomials

The proof uses the leading-coefficient formula from Lagrange interpolation.
Its barycentric denominators have an explicitly alternating sign on a
strictly ordered family of nodes.  Consequently all terms in the formula
have one sign, while their sum is zero for a polynomial of degree `< m`.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

private theorem ordered_denominator_sign
    {m : ℕ}
    {x : Fin (m + 1) → ℝ}
    (hx : StrictMono x)
    (i : Fin (m + 1)) :
    0 < (-1 : ℝ) ^ (m - (i : ℕ)) *
      ∏ j ∈ (Finset.univ.erase i), (x i - x j) := by
  have hunion : (Finset.univ.erase i) = Finset.Iio i ∪ Finset.Ioi i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
      Finset.mem_Iio, Finset.mem_Ioi]
    omega
  have hdisjoint : Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    apply Finset.disjoint_left.mpr
    intro j hjlo hjhi
    simp only [Finset.mem_Iio] at hjlo
    simp only [Finset.mem_Ioi] at hjhi
    omega
  have hlo : 0 < ∏ j ∈ Finset.Iio i, (x i - x j) := by
    apply Finset.prod_pos
    intro j hj
    exact sub_pos.mpr (hx (Finset.mem_Iio.mp hj))
  have hhi : 0 < ∏ j ∈ Finset.Ioi i, (-1 : ℝ) * (x i - x j) := by
    apply Finset.prod_pos
    intro j hj
    exact mul_pos_of_neg_of_neg (by norm_num)
      (sub_neg.mpr (hx (Finset.mem_Ioi.mp hj)))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Fin.card_Ioi] at hhi
  have hhi' : 0 < (-1 : ℝ) ^ (m - (i : ℕ)) *
      ∏ j ∈ Finset.Ioi i, (x i - x j) := by
    simpa using hhi
  rw [hunion, Finset.prod_union hdisjoint]
  calc
    0 < (∏ j ∈ Finset.Iio i, (x i - x j)) *
        ((-1 : ℝ) ^ (m - (i : ℕ)) *
          ∏ j ∈ Finset.Ioi i, (x i - x j)) := mul_pos hlo hhi'
    _ = (-1 : ℝ) ^ (m - (i : ℕ)) *
        ((∏ j ∈ Finset.Iio i, (x i - x j)) *
          ∏ j ∈ Finset.Ioi i, (x i - x j)) := by ring

private theorem ordered_denominator_inv_sign
    {m : ℕ}
    {x : Fin (m + 1) → ℝ}
    (hx : StrictMono x)
    (i : Fin (m + 1)) :
    0 < (-1 : ℝ) ^ (m - (i : ℕ)) *
      (∏ j ∈ (Finset.univ.erase i), (x i - x j))⁻¹ := by
  have h := inv_pos_of_pos (ordered_denominator_sign hx i)
  rwa [mul_inv, ← inv_pow, inv_neg_one] at h

private theorem signed_lagrange_term_nonnegative
    {m : ℕ}
    {p : ℝ[X]}
    {x : Fin (m + 1) → ℝ}
    (hx : StrictMono x)
    (halt : ∀ i : Fin (m + 1),
      0 ≤ (-1 : ℝ) ^ (i : ℕ) * p.eval (x i))
    (i : Fin (m + 1)) :
    0 ≤ (-1 : ℝ) ^ m *
      (p.eval (x i) /
        ∏ j ∈ (Finset.univ.erase i), (x i - x j)) := by
  have hi : (i : ℕ) ≤ m := by omega
  have hsign := ordered_denominator_inv_sign hx i
  calc
    (-1 : ℝ) ^ m *
        (p.eval (x i) /
          ∏ j ∈ (Finset.univ.erase i), (x i - x j)) =
      ((-1 : ℝ) ^ (i : ℕ) * p.eval (x i)) *
        ((-1 : ℝ) ^ (m - (i : ℕ)) *
          (∏ j ∈ (Finset.univ.erase i), (x i - x j))⁻¹) := by
        have hpows : (-1 : ℝ) ^ m =
            (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (m - (i : ℕ)) := by
          rw [← pow_add, Nat.add_sub_of_le hi]
        rw [div_eq_mul_inv, hpows]
        ring
    _ ≥ 0 := mul_nonneg (halt i) hsign.le

/-- A polynomial of degree `< m` cannot have weakly alternating signs at
`m + 1` strictly ordered points unless it is zero. -/
theorem polynomial_eq_zero_of_alternating_signs
    {m : ℕ}
    {p : ℝ[X]}
    (hdeg : p.natDegree < m)
    {x : Fin (m + 1) → ℝ}
    (hx : StrictMono x)
    (halt : ∀ i : Fin (m + 1),
      0 ≤ (-1 : ℝ) ^ (i : ℕ) * p.eval (x i)) :
    p = 0 := by
  classical
  by_cases hp : p = 0
  · exact hp
  -- Lagrange interpolation identifies the forbidden leading coefficient
  -- with a sum of barycentric terms.
  have hdegree : p.degree < (Finset.univ : Finset (Fin (m + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin, degree_eq_natDegree hp]
    norm_cast
    omega
  have hlagrange := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin (m + 1))))
    (v := x) hx.injective.injOn hdegree
  have hcoeff : p.coeff
      ((Finset.univ : Finset (Fin (m + 1))).card - 1) = 0 := by
    simpa using coeff_eq_zero_of_natDegree_lt hdeg
  have hsum :
      ∑ i : Fin (m + 1),
        p.eval (x i) /
          ∏ j ∈ (Finset.univ.erase i), (x i - x j) = 0 := by
    rw [← hlagrange, hcoeff]
  have hsigned_sum :
      ∑ i : Fin (m + 1),
        ((-1 : ℝ) ^ m *
          (p.eval (x i) /
            ∏ j ∈ (Finset.univ.erase i), (x i - x j))) = 0 := by
    rw [← Finset.mul_sum, hsum, mul_zero]
  -- After multiplying by the common sign, every summand is nonnegative.
  -- Since their sum is zero, every summand vanishes.
  have hterm (i : Fin (m + 1)) :
      (-1 : ℝ) ^ m *
        (p.eval (x i) /
          ∏ j ∈ (Finset.univ.erase i), (x i - x j)) = 0 := by
    have hall := (Fintype.sum_eq_zero_iff_of_nonneg
      (fun i ↦ signed_lagrange_term_nonnegative hx halt i)).mp hsigned_sum
    exact congrFun hall i
  -- The interpolation denominators are nonzero, so all node evaluations
  -- vanish. A polynomial below the interpolation degree is then zero.
  have heval (i : Fin (m + 1)) : p.eval (x i) = 0 := by
    have hquot : p.eval (x i) /
        ∏ j ∈ (Finset.univ.erase i), (x i - x j) = 0 :=
      (mul_eq_zero.mp (hterm i)).resolve_left (pow_ne_zero _ (by norm_num))
    have hden_pos := ordered_denominator_sign hx i
    have hden_ne : (∏ j ∈ (Finset.univ.erase i), (x i - x j)) ≠ 0 := by
      intro hzero
      simp [hzero] at hden_pos
    rw [div_eq_mul_inv] at hquot
    exact (mul_eq_zero.mp hquot).resolve_right (inv_ne_zero hden_ne)
  exact Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
    (Finset.univ : Finset (Fin (m + 1))) hx.injective.injOn hdegree
    (fun i _ ↦ heval i)

end JoseSmoothest
