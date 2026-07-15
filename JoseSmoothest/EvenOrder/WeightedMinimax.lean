import JoseSmoothest.Alternation
import JoseSmoothest.Chebyshev

/-!
# The weighted polynomial problem for an arbitrary even difference

This file isolates the order-independent approximation problem underlying an
even difference of order `2 * m`.  It also proves that a zero--peak
alternation certificate is sufficient for sharpness and uniqueness.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

/-- The polynomial numerator obtained by restoring the endpoint zero of order `m`. -/
def evenWeightedNumerator (m : ℕ) (p : ℝ[X]) : ℝ[X] :=
  (C 1 - X) ^ m * p

/-- The weighted uniform norm associated with a difference of order `2 * m`. -/
def evenWeightedPolynomialNorm (m : ℕ) (p : ℝ[X]) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    r = |(1 - x) ^ m * p.eval x|}

private theorem evenWeightedRange_nonempty (m : ℕ) (p : ℝ[X]) :
    {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      r = |(1 - x) ^ m * p.eval x|}.Nonempty := by
  refine ⟨|(1 - 0) ^ m * p.eval 0|, 0, ?_, rfl⟩
  constructor <;> norm_num

private theorem evenWeightedRange_bddAbove (m : ℕ) (p : ℝ[X]) :
    BddAbove {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      r = |(1 - x) ^ m * p.eval x|} := by
  let g : ℝ → ℝ := fun x ↦ |(1 - x) ^ m * p.eval x|
  have hg : Continuous g := by
    unfold g
    fun_prop
  have hset : {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      r = |(1 - x) ^ m * p.eval x|} = g '' Set.Icc (-1 : ℝ) 1 := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hset]
  exact (isCompact_Icc.image hg).bddAbove

/-- Every weighted value on `[-1, 1]` is bounded by the weighted norm. -/
theorem evenWeightedValue_le_norm
    (m : ℕ) (p : ℝ[X]) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(1 - x) ^ m * p.eval x| ≤ evenWeightedPolynomialNorm m p := by
  unfold evenWeightedPolynomialNorm
  exact le_csSup (evenWeightedRange_bddAbove m p) ⟨x, hx, rfl⟩

/-- The weighted polynomial norm is nonnegative. -/
theorem evenWeightedPolynomialNorm_nonneg (m : ℕ) (p : ℝ[X]) :
    0 ≤ evenWeightedPolynomialNorm m p := by
  have h := evenWeightedValue_le_norm m p
    (x := 0) (⟨by norm_num, by norm_num⟩ : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  exact (abs_nonneg _).trans h

/-- A feasible quotient for the weighted extremal problem with endpoint order `m`
and total numerator degree at most `N`. -/
structure IsAdmissibleEvenWeightedPolynomial
    (m N : ℕ) (p : ℝ[X]) : Prop where
  /-- The degree bound after removing the endpoint factor. -/
  degree_le : p.natDegree ≤ N - m
  /-- Nonnegativity on the approximation interval. -/
  nonnegative : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x
  /-- Normalization at the distinguished endpoint. -/
  eval_one : p.eval 1 = 1

/-- Data certifying that a numerator alternates between zero and its peak often
enough to solve the weighted extremal problem. -/
structure EvenZeroPeakCertificate
    (m N : ℕ) (q : ℝ[X]) (M : ℝ) where
  /-- The orientation of the zero--peak alternation. -/
  orientation : ℝ
  /-- The orientation is a sign. -/
  orientation_eq : orientation = 1 ∨ orientation = -1
  /-- The nodes away from the distinguished endpoint `1`. -/
  nodes : Fin (N - m + 1) → ℝ
  /-- The nodes are strictly increasing. -/
  strictMono_nodes : StrictMono nodes
  /-- Every alternation node lies in `[-1, 1)`. -/
  nodes_mem_Ico : ∀ i, nodes i ∈ Set.Ico (-1 : ℝ) 1
  /-- The numerator lies between zero and its peak throughout the interval. -/
  bounds : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    0 ≤ q.eval x ∧ q.eval x ≤ M
  /-- The peak value is attained. -/
  exists_peak : ∃ x ∈ Set.Icc (-1 : ℝ) 1, q.eval x = M
  /-- Successive node values alternate between zero and `M`. -/
  node_value : ∀ i,
    q.eval (nodes i) =
      M / 2 * (1 - orientation * (-1 : ℝ) ^ (i : ℕ))

/-- A packaged admissible optimizer and its sufficient zero--peak certificate. -/
structure EvenWeightedExtremalData (m N : ℕ) where
  /-- The admissible quotient. -/
  S : ℝ[X]
  /-- The numerator with its endpoint factor restored. -/
  q : ℝ[X]
  /-- The certified peak. -/
  M : ℝ
  /-- Feasibility of the quotient. -/
  admissible : IsAdmissibleEvenWeightedPolynomial m N S
  /-- Exact endpoint factorization. -/
  factorization : evenWeightedNumerator m S = q
  /-- The zero--peak certificate. -/
  certificate : EvenZeroPeakCertificate m N q M

/-- An exact factorization and a zero--peak certificate compute the weighted
norm of the proposed optimizer. -/
theorem evenWeightedPolynomialNorm_eq_of_certificate
    {m N : ℕ} {S q : ℝ[X]} {M : ℝ}
    (hSq : evenWeightedNumerator m S = q)
    (certificate : EvenZeroPeakCertificate m N q M) :
    evenWeightedPolynomialNorm m S = M := by
  let B : Set ℝ := {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    r = |(1 - x) ^ m * S.eval x|}
  have hvalue (x : ℝ) : (1 - x) ^ m * S.eval x = q.eval x := by
    have h := congrArg (fun p : ℝ[X] ↦ p.eval x) hSq
    simpa [evenWeightedNumerator] using h
  have hB_nonempty : B.Nonempty := by
    simpa [B] using evenWeightedRange_nonempty m S
  have hB_upper : ∀ r ∈ B, r ≤ M := by
    rintro r ⟨x, hx, rfl⟩
    rw [hvalue, abs_of_nonneg (certificate.bounds x hx).1]
    exact (certificate.bounds x hx).2
  have hB_bdd : BddAbove B := ⟨M, hB_upper⟩
  have hM_nonneg : 0 ≤ M := by
    obtain ⟨x, hx, hpeak⟩ := certificate.exists_peak
    rw [← hpeak]
    exact (certificate.bounds x hx).1
  have hM_mem : M ∈ B := by
    obtain ⟨x, hx, hpeak⟩ := certificate.exists_peak
    refine ⟨x, hx, ?_⟩
    rw [hvalue, hpeak, abs_of_nonneg hM_nonneg]
  change sSup B = M
  apply le_antisymm
  · exact csSup_le hB_nonempty hB_upper
  · exact le_csSup hB_bdd hM_mem

namespace EvenWeightedExtremalData

variable {m N : ℕ} (E : EvenWeightedExtremalData m N)

/-- The peak in packaged extremal data is its quotient's weighted norm. -/
theorem norm_eq : evenWeightedPolynomialNorm m E.S = E.M :=
  evenWeightedPolynomialNorm_eq_of_certificate E.factorization E.certificate

/-- The peak in packaged extremal data is nonnegative. -/
theorem M_nonneg : 0 ≤ E.M := by
  obtain ⟨x, hx, hpeak⟩ := E.certificate.exists_peak
  rw [← hpeak]
  exact (E.certificate.bounds x hx).1

end EvenWeightedExtremalData

private theorem polynomial_eq_one_of_natDegree_le_zero
    (p : ℝ[X]) (hdeg : p.natDegree ≤ 0) (hone : p.eval 1 = 1) :
    p = 1 := by
  rw [eq_C_of_natDegree_le_zero hdeg]
  have h := hone
  rw [eq_C_of_natDegree_le_zero hdeg] at h
  simp only [eval_C] at h
  rw [h]
  simp

/-- A zero--peak certificate forces uniqueness among admissible polynomials
whose weighted norm is at most the certified peak. -/
theorem evenWeightedPolynomial_eq_of_norm_le
    (m N : ℕ) (hN : m ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleEvenWeightedPolynomial m N p)
    (hS : IsAdmissibleEvenWeightedPolynomial m N S)
    (hSq : evenWeightedNumerator m S = q)
    (certificate : EvenZeroPeakCertificate m N q M)
    (hnorm : evenWeightedPolynomialNorm m p ≤ M) :
    p = S := by
  by_cases hNm : N = m
  · subst N
    have hp_one := polynomial_eq_one_of_natDegree_le_zero p
      (by simpa using hp.degree_le) hp.eval_one
    have hS_one := polynomial_eq_one_of_natDegree_le_zero S
      (by simpa using hS.degree_le) hS.eval_one
    rw [hp_one, hS_one]
  have hmN : m + 1 ≤ N := by omega
  let d : ℝ[X] := p - S
  let r : ℝ[X] := d /ₘ (X - C 1)
  have hdroot : d.IsRoot 1 := by
    simp [d, IsRoot, hp.eval_one, hS.eval_one]
  have hfactor : (X - C 1) * r = d :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hdroot
  have hddeg : d.natDegree ≤ N - m :=
    (natDegree_sub_le p S).trans (max_le hp.degree_le hS.degree_le)
  have hrdeg : r.natDegree < N - m := by
    dsimp [r]
    rw [natDegree_divByMonic _ (monic_X_sub_C 1), natDegree_X_sub_C]
    omega
  let t : ℝ[X] := (-certificate.orientation) • r
  have htdeg : t.natDegree < N - m :=
    (natDegree_smul_le (-certificate.orientation) r).trans_lt hrdeg
  have halt (i : Fin (N - m + 1)) :
      0 ≤ (-1 : ℝ) ^ (i : ℕ) * t.eval (certificate.nodes i) := by
    let x := certificate.nodes i
    have hxIco : x ∈ Set.Ico (-1 : ℝ) 1 := certificate.nodes_mem_Ico i
    have hx : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hxIco.1, hxIco.2.le⟩
    have hxpos : 0 < 1 - x := sub_pos.mpr hxIco.2
    have hpower : 0 < (1 - x) ^ (m + 1) := pow_pos hxpos (m + 1)
    have hpweight_nonneg : 0 ≤ (1 - x) ^ m * p.eval x :=
      mul_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) m) (hp.nonnegative x hx)
    have hpweight_abs : |(1 - x) ^ m * p.eval x| ≤
        evenWeightedPolynomialNorm m p := evenWeightedValue_le_norm m p hx
    have hpweight_le : (1 - x) ^ m * p.eval x ≤ M := by
      calc
        (1 - x) ^ m * p.eval x ≤ |(1 - x) ^ m * p.eval x| := le_abs_self _
        _ ≤ evenWeightedPolynomialNorm m p := hpweight_abs
        _ ≤ M := hnorm
    have hSeval : (1 - x) ^ m * S.eval x = q.eval x := by
      have h := congrArg (fun a : ℝ[X] ↦ a.eval x) hSq
      simpa [evenWeightedNumerator] using h
    have hdeval : p.eval x - S.eval x = (x - 1) * r.eval x := by
      have h := congrArg (fun a : ℝ[X] ↦ a.eval x) hfactor
      simpa [d] using h.symm
    have hdiff : (1 - x) ^ m * p.eval x - q.eval x =
        -(1 - x) ^ (m + 1) * r.eval x := by
      rw [← hSeval, ← mul_sub, hdeval, pow_succ]
      ring
    have hnode := certificate.node_value i
    rcases certificate.orientation_eq with horient | horient
    · rcases Nat.even_or_odd (i : ℕ) with hi | hi
      · rw [horient, hi.neg_one_pow] at hnode
        norm_num at hnode
        rw [hnode] at hdiff
        dsimp [t]
        simp only [eval_smul, smul_eq_mul, horient, hi.neg_one_pow]
        have hr : r.eval x ≤ 0 := by nlinarith
        nlinarith
      · rw [horient, hi.neg_one_pow] at hnode
        norm_num at hnode
        rw [hnode] at hdiff
        dsimp [t]
        simp only [eval_smul, smul_eq_mul, horient, hi.neg_one_pow]
        have hr : 0 ≤ r.eval x := by nlinarith
        nlinarith
    · rcases Nat.even_or_odd (i : ℕ) with hi | hi
      · rw [horient, hi.neg_one_pow] at hnode
        norm_num at hnode
        rw [hnode] at hdiff
        dsimp [t]
        simp only [eval_smul, smul_eq_mul, horient, hi.neg_one_pow]
        have hr : 0 ≤ r.eval x := by nlinarith
        nlinarith
      · rw [horient, hi.neg_one_pow] at hnode
        norm_num at hnode
        rw [hnode] at hdiff
        dsimp [t]
        simp only [eval_smul, smul_eq_mul, horient, hi.neg_one_pow]
        have hr : r.eval x ≤ 0 := by nlinarith
        nlinarith
  have ht_zero : t = 0 := polynomial_eq_zero_of_alternating_signs
    htdeg certificate.strictMono_nodes halt
  have horientation_ne : -certificate.orientation ≠ 0 := by
    rcases certificate.orientation_eq with h | h <;> simp [h]
  have hr_zero : r = 0 := by
    dsimp [t] at ht_zero
    exact (smul_eq_zero.mp ht_zero).resolve_left horientation_ne
  have hd_zero : d = 0 := by rw [← hfactor, hr_zero, mul_zero]
  exact sub_eq_zero.mp hd_zero

/-- A certified optimizer gives the sharp lower bound for every admissible
polynomial. -/
theorem evenWeightedPolynomialNorm_ge_of_certificate
    (m N : ℕ) (hN : m ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleEvenWeightedPolynomial m N p)
    (hS : IsAdmissibleEvenWeightedPolynomial m N S)
    (hSq : evenWeightedNumerator m S = q)
    (certificate : EvenZeroPeakCertificate m N q M) :
    M ≤ evenWeightedPolynomialNorm m p := by
  by_contra hnot
  have hlt : evenWeightedPolynomialNorm m p < M := lt_of_not_ge hnot
  have heq := evenWeightedPolynomial_eq_of_norm_le m N hN hp hS hSq
    certificate hlt.le
  rw [heq, evenWeightedPolynomialNorm_eq_of_certificate hSq certificate] at hlt
  exact lt_irrefl _ hlt

/-- Equality in the certified weighted problem holds exactly at the proposed
optimizer. -/
theorem evenWeightedPolynomialNorm_eq_iff_of_certificate
    (m N : ℕ) (hN : m ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleEvenWeightedPolynomial m N p)
    (hS : IsAdmissibleEvenWeightedPolynomial m N S)
    (hSq : evenWeightedNumerator m S = q)
    (certificate : EvenZeroPeakCertificate m N q M) :
    evenWeightedPolynomialNorm m p = M ↔ p = S := by
  constructor
  · intro hnorm
    exact evenWeightedPolynomial_eq_of_norm_le m N hN hp hS hSq
      certificate hnorm.le
  · rintro rfl
    exact evenWeightedPolynomialNorm_eq_of_certificate hSq certificate

end JoseSmoothest
