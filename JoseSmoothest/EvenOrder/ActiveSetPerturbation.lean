import JoseSmoothest.TwoSetAlternation
import JoseSmoothest.EvenOrder.WeightedMinimax
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Order.Compact

/-!
# Active sets and strict weighted perturbations

A polynomial which strictly separates the zero and peak active sets gives an
inward perturbation.  Two compactness lemmas below make the usual
"sufficiently small epsilon" argument uniform on the whole interval.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

/-- Zeros of an admissible quotient on the approximation interval. -/
def zeroActiveSet (S : ℝ[X]) : Set ℝ :=
  {x ∈ Set.Icc (-1 : ℝ) 1 | S.eval x = 0}

/-- Points where the restored weighted numerator attains the weighted norm. -/
def peakActiveSet (m : ℕ) (S : ℝ[X]) : Set ℝ :=
  {x ∈ Set.Icc (-1 : ℝ) 1 |
    (evenWeightedNumerator m S).eval x = evenWeightedPolynomialNorm m S}

private theorem evenWeightedPolynomialNorm_pos_of_admissible_aux
    {m N : ℕ} (_hm : 1 ≤ m) {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S) :
    0 < evenWeightedPolynomialNorm m S := by
  apply (evenWeightedPolynomialNorm_nonneg m S).lt_of_ne'
  intro hzero
  have hroot : Set.Ioo (-1 : ℝ) 1 ⊆ {x | S.IsRoot x} := by
    intro x hx
    have hvalue := evenWeightedValue_le_norm m S
      (⟨hx.1.le, hx.2.le⟩ : x ∈ Set.Icc (-1 : ℝ) 1)
    rw [hzero] at hvalue
    have hweighted : (1 - x) ^ m * S.eval x = 0 := by
      have : |(1 - x) ^ m * S.eval x| = 0 :=
        le_antisymm hvalue (abs_nonneg _)
      exact abs_eq_zero.mp this
    have hpow : (1 - x) ^ m ≠ 0 := by
      exact pow_ne_zero _ (sub_ne_zero.mpr (ne_of_gt hx.2))
    exact (mul_eq_zero.mp hweighted).resolve_left hpow
  have hinfinite : Set.Infinite {x | S.IsRoot x} :=
    (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).mono hroot
  have hSz : S = 0 := Polynomial.eq_zero_of_infinite_isRoot S hinfinite
  have hone := hS.eval_one
  rw [hSz] at hone
  norm_num at hone

private theorem exists_evenWeightedNorm_point
    (m : ℕ) (S : ℝ[X]) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      |(1 - x) ^ m * S.eval x| = evenWeightedPolynomialNorm m S := by
  let f : ℝ → ℝ := fun x ↦ |(1 - x) ^ m * S.eval x|
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  obtain ⟨x, hx, hxmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1)) hf.continuousOn
  refine ⟨x, hx, le_antisymm (evenWeightedValue_le_norm m S hx) ?_⟩
  unfold evenWeightedPolynomialNorm
  apply csSup_le
  · refine ⟨|(1 - 0) ^ m * S.eval 0|, 0, ?_, rfl⟩
    constructor <;> norm_num
  · rintro r ⟨y, hy, rfl⟩
    exact hxmax hy

/-- The zero active set of an admissible quotient is finite. -/
theorem zeroActiveSet_finite
    {m N : ℕ} {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S) :
    (zeroActiveSet S).Finite := by
  have hSne : S ≠ 0 := by
    intro hzero
    have hone := hS.eval_one
    rw [hzero] at hone
    norm_num at hone
  apply (Polynomial.finite_setOf_isRoot hSne).subset
  intro x hx
  exact hx.2

/-- The peak active set is finite at positive endpoint order. -/
theorem peakActiveSet_finite
    {m N : ℕ} (hm : 1 ≤ m) {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S) :
    (peakActiveSet m S).Finite := by
  let M := evenWeightedPolynomialNorm m S
  let q := evenWeightedNumerator m S - C M
  have hM : 0 < M := evenWeightedPolynomialNorm_pos_of_admissible_aux hm hS
  have hqeval : q.eval 1 = -M := by
    simp [q, evenWeightedNumerator, Nat.ne_zero_of_lt hm]
  have hqne : q ≠ 0 := by
    intro hzero
    have := hqeval
    rw [hzero] at this
    simp at this
    linarith
  apply (Polynomial.finite_setOf_isRoot hqne).subset
  intro x hx
  dsimp [q]
  rw [IsRoot, eval_sub, eval_C, hx.2]
  simp [M]

/-- The weighted numerator attains its peak on the compact interval. -/
theorem peakActiveSet_nonempty
    {m N : ℕ} (_hm : 1 ≤ m) {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S) :
    (peakActiveSet m S).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := exists_evenWeightedNorm_point m S
  refine ⟨x, hx, ?_⟩
  have hxpow : 0 ≤ (1 - x) ^ m :=
    pow_nonneg (sub_nonneg.mpr hx.2) m
  have hxS : 0 ≤ S.eval x := hS.nonnegative x hx
  have hnonneg : 0 ≤ (1 - x) ^ m * S.eval x := mul_nonneg hxpow hxS
  have hqeval : (evenWeightedNumerator m S).eval x =
      (1 - x) ^ m * S.eval x := by
    simp [evenWeightedNumerator]
  rw [abs_of_nonneg hnonneg] at hmax
  exact hqeval.trans hmax

/-- Zero and positive-peak active sets cannot meet. -/
theorem activeSets_disjoint
    {m N : ℕ} (hm : 1 ≤ m) {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S) :
    Disjoint (zeroActiveSet S) (peakActiveSet m S) := by
  apply Set.disjoint_left.mpr
  intro x hxzero hxpeak
  have hM := evenWeightedPolynomialNorm_pos_of_admissible_aux hm hS
  have hqzero : (evenWeightedNumerator m S).eval x = 0 := by
    simp [evenWeightedNumerator, hxzero.2]
  have hxpeak_eq := hxpeak.2
  rw [hqzero] at hxpeak_eq
  exact (ne_of_gt hM) hxpeak_eq.symm

private theorem exists_uniform_nonnegative_perturbation
    {K : Set ℝ} {f g : ℝ → ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hf : Continuous f) (hg : Continuous g)
    (hf_nonneg : ∀ x ∈ K, 0 ≤ f x)
    (hzero : ∀ x ∈ K, f x = 0 → 0 < g x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
        ∀ x ∈ K, 0 ≤ f x + ε * g x := by
  let C : Set ℝ := K ∩ {x | g x ≤ 0}
  have hC : IsCompact C := hK.inter_right (isClosed_Iic.preimage hg)
  by_cases hCne : C.Nonempty
  · obtain ⟨c, hc, hcmin⟩ := hC.exists_isMinOn hCne hf.continuousOn
    obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn hKne hg.abs.continuousOn
    have hfc : 0 < f c := by
      have hfc0 := hf_nonneg c hc.1
      apply hfc0.lt_of_ne'
      intro hfcz
      have := hzero c hc.1 hfcz
      exact (not_lt_of_ge hc.2) this
    have hA : 0 ≤ |g b| := abs_nonneg _
    let δ := f c / (|g b| + 1)
    have hden : 0 < |g b| + 1 := by positivity
    have hδ : 0 < δ := div_pos hfc hden
    refine ⟨δ, hδ, ?_⟩
    intro ε hε hεδ x hx
    by_cases hgpos : 0 < g x
    · exact add_nonneg (hf_nonneg x hx) (mul_nonneg hε hgpos.le)
    · have hxC : x ∈ C := ⟨hx, le_of_not_gt hgpos⟩
      have hfc_le : f c ≤ f x := hcmin hxC
      have habs : |g x| ≤ |g b| := hbmax hx
      have hg_lower : -|g b| ≤ g x :=
        (neg_le_of_abs_le habs)
      have hmul_lower : -ε * |g b| ≤ ε * g x := by
        nlinarith [mul_le_mul_of_nonneg_left hg_lower hε]
      have hmul_eps : ε * |g b| ≤ δ * |g b| :=
        mul_le_mul_of_nonneg_right hεδ hA
      have hδgap : δ * |g b| < f c := by
        have hδeq : δ * (|g b| + 1) = f c := by
          dsimp [δ]
          field_simp
        nlinarith
      nlinarith
  · refine ⟨1, by norm_num, ?_⟩
    intro ε hε hε1 x hx
    have hgpos : 0 < g x := by
      by_contra hnot
      exact hCne ⟨x, hx, le_of_not_gt hnot⟩
    exact add_nonneg (hf_nonneg x hx) (mul_nonneg hε hgpos.le)

private theorem exists_uniform_strict_upper_perturbation
    {K : Set ℝ} {f g : ℝ → ℝ} {M : ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hf : Continuous f) (hg : Continuous g)
    (hf_upper : ∀ x ∈ K, f x ≤ M)
    (hpeak : ∀ x ∈ K, f x = M → g x < 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        ∀ x ∈ K, f x + ε * g x < M := by
  let C : Set ℝ := K ∩ {x | 0 ≤ g x}
  have hC : IsCompact C := hK.inter_right (isClosed_Ici.preimage hg)
  by_cases hCne : C.Nonempty
  · obtain ⟨c, hc, hcmax⟩ := hC.exists_isMaxOn hCne hf.continuousOn
    obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn hKne hg.abs.continuousOn
    have hfc : f c < M := by
      have hfc_le := hf_upper c hc.1
      apply hfc_le.lt_of_ne
      intro hfceq
      have := hpeak c hc.1 hfceq
      exact (not_lt_of_ge hc.2) this
    have hA : 0 ≤ |g b| := abs_nonneg _
    let δ := (M - f c) / (|g b| + 1)
    have hden : 0 < |g b| + 1 := by positivity
    have hδ : 0 < δ := div_pos (sub_pos.mpr hfc) hden
    refine ⟨δ, hδ, ?_⟩
    intro ε hε hεδ x hx
    by_cases hgneg : g x < 0
    · have := mul_neg_of_pos_of_neg hε hgneg
      nlinarith [hf_upper x hx]
    · have hxC : x ∈ C := ⟨hx, le_of_not_gt hgneg⟩
      have hfx_le : f x ≤ f c := hcmax hxC
      have habs : |g x| ≤ |g b| := hbmax hx
      have hg_upper : g x ≤ |g b| := (le_abs_self _).trans habs
      have hmul_g : ε * g x ≤ ε * |g b| :=
        mul_le_mul_of_nonneg_left hg_upper hε.le
      have hmul_eps : ε * |g b| ≤ δ * |g b| :=
        mul_le_mul_of_nonneg_right hεδ hA
      have hδgap : δ * |g b| < M - f c := by
        have hδeq : δ * (|g b| + 1) = M - f c := by
          dsimp [δ]
          field_simp
        nlinarith
      nlinarith
  · refine ⟨1, by norm_num, ?_⟩
    intro ε hε hε1 x hx
    have hgneg : g x < 0 := by
      by_contra hnot
      exact hCne ⟨x, hx, le_of_not_gt hnot⟩
    have := mul_neg_of_pos_of_neg hε hgneg
    nlinarith [hf_upper x hx]

/-- A strict separator between the zero and peak active sets gives a feasible
quotient with strictly smaller weighted norm. -/
theorem exists_strict_weighted_improvement_of_separator
    {m N : ℕ} (hm : 1 ≤ m) (_hN : m < N)
    {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S)
    (hsep : StrictPolynomialSeparator (N - m)
      (zeroActiveSet S) (peakActiveSet m S)) :
    ∃ p : ℝ[X],
      IsAdmissibleEvenWeightedPolynomial m N p ∧
        evenWeightedPolynomialNorm m p < evenWeightedPolynomialNorm m S := by
  let K : Set ℝ := Set.Icc (-1 : ℝ) 1
  let r := hsep.polynomial
  let f : ℝ → ℝ := fun x ↦ S.eval x
  let g : ℝ → ℝ := fun x ↦ (x - 1) * r.eval x
  let F : ℝ → ℝ := fun x ↦ (1 - x) ^ m * S.eval x
  let G : ℝ → ℝ := fun x ↦ (1 - x) ^ m * g x
  have hK : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := Set.nonempty_Icc.mpr (by norm_num)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g, r]; fun_prop
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hf_nonneg : ∀ x ∈ K, 0 ≤ f x := hS.nonnegative
  have hzero : ∀ x ∈ K, f x = 0 → 0 < g x := by
    intro x hx hxzero
    have hrneg := hsep.negative_on_first x ⟨hx, hxzero⟩
    have hxlt : x < 1 := by
      apply lt_of_le_of_ne hx.2
      intro hxeq
      have : f x = 1 := by simpa [f, hxeq] using hS.eval_one
      linarith
    dsimp [g]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hxlt) hrneg
  obtain ⟨δ0, hδ0, hfeasible⟩ := exists_uniform_nonnegative_perturbation
    hK hKne hf hg hf_nonneg hzero
  let M := evenWeightedPolynomialNorm m S
  have hM : 0 < M := evenWeightedPolynomialNorm_pos_of_admissible_aux hm hS
  have hF_nonneg : ∀ x ∈ K, 0 ≤ F x := by
    intro x hx
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) m) (hS.nonnegative x hx)
  have hF_upper : ∀ x ∈ K, F x ≤ M := by
    intro x hx
    exact calc
      F x ≤ |F x| := le_abs_self _
      _ ≤ M := by simpa [F, M] using evenWeightedValue_le_norm m S hx
  have hpeak : ∀ x ∈ K, F x = M → G x < 0 := by
    intro x hx hxpeak
    have hqeval : (evenWeightedNumerator m S).eval x = F x := by
      simp [evenWeightedNumerator, F]
    have hrpos := hsep.positive_on_second x ⟨hx, by simpa [hqeval, M] using hxpeak⟩
    have hxlt : x < 1 := by
      apply lt_of_le_of_ne hx.2
      intro hxeq
      subst x
      have : F 1 = 0 := by simp [F, Nat.ne_zero_of_lt hm]
      rw [this] at hxpeak
      linarith
    have hpow : 0 < (1 - x) ^ m := pow_pos (sub_pos.mpr hxlt) m
    have hgneg : g x < 0 := by
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hxlt) hrpos
    exact mul_neg_of_pos_of_neg hpow hgneg
  obtain ⟨δ1, hδ1, himprove⟩ := exists_uniform_strict_upper_perturbation
    hK hKne hF hG hF_upper hpeak
  let ε := min δ0 δ1
  have hε : 0 < ε := lt_min hδ0 hδ1
  have hεδ0 : ε ≤ δ0 := min_le_left _ _
  have hεδ1 : ε ≤ δ1 := min_le_right _ _
  let p : ℝ[X] := S + C ε * ((X - C 1) * r)
  have hp_eval (x : ℝ) : p.eval x = f x + ε * g x := by
    simp [p, f, g, r]
  have hp_degree : p.natDegree ≤ N - m := by
    have hrdeg : r.natDegree < N - m := hsep.natDegree_lt
    have hlin : (X - C (1 : ℝ)).natDegree = 1 := natDegree_X_sub_C 1
    have hprod : ((X - C (1 : ℝ)) * r).natDegree ≤ N - m := by
      calc
        ((X - C (1 : ℝ)) * r).natDegree
            ≤ (X - C (1 : ℝ)).natDegree + r.natDegree := natDegree_mul_le
        _ ≤ N - m := by rw [hlin]; omega
    exact (natDegree_add_le _ _).trans
      (max_le hS.degree_le
        ((natDegree_C_mul_le ε ((X - C (1 : ℝ)) * r)).trans hprod))
  have hp_admissible : IsAdmissibleEvenWeightedPolynomial m N p := {
    degree_le := hp_degree
    nonnegative := by
      intro x hx
      rw [hp_eval]
      exact hfeasible ε hε.le hεδ0 x hx
    eval_one := by simp [p, hS.eval_one]
  }
  refine ⟨p, hp_admissible, ?_⟩
  obtain ⟨x, hx, hxnorm⟩ := exists_evenWeightedNorm_point m p
  have hpweight_nonneg : 0 ≤ (1 - x) ^ m * p.eval x :=
    mul_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) m)
      (hp_admissible.nonnegative x hx)
  have hweighted : (1 - x) ^ m * p.eval x = F x + ε * G x := by
    rw [hp_eval]
    simp only [F, G]
    ring
  rw [abs_of_nonneg hpweight_nonneg] at hxnorm
  rw [← hxnorm, hweighted]
  exact himprove ε hε hεδ1 x hx

end JoseSmoothest
