import JoseSmoothest.Alternation
import JoseSmoothest.Chebyshev

/-!
# The cubic weighted polynomial problem

This file isolates the approximation-theoretic part of the sixth-difference
problem.  The downstream `Zolotarev` module constructs the certificate below
from the polynomial Pell--Abel, differential, and equioscillation data.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

/-- The weighted norm associated with a sixth discrete difference. -/
def cubicWeightedPolynomialNorm (p : ℝ[X]) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    r = |(1 - x) ^ 3 * p.eval x|}

/-- A feasible polynomial for the cubic weighted extremal problem of order `N`. -/
structure IsAdmissibleCubicWeightedPolynomial (N : ℕ) (p : ℝ[X]) : Prop where
  /-- The degree bound after removing a cubic endpoint factor. -/
  degree_le : p.natDegree ≤ N - 3
  /-- Nonnegativity on the approximation interval. -/
  nonnegative : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x
  /-- Normalization at the right endpoint. -/
  eval_one : p.eval 1 = 1

/-- An admissible kernel gives a feasible polynomial for the cubic weighted
problem after the substitution `x = cos ξ`. -/
theorem IsAdmissibleKernel.cubicKernelPolynomial
    {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    IsAdmissibleCubicWeightedPolynomial (n + 3) (kernelPolynomial n u) where
  degree_le := by
    simpa using kernelPolynomial_natDegree_le n u
  nonnegative :=
    kernelPolynomial_nonnegative_on_Icc n u h.support h.symmetric
      h.fourier_nonnegative
  eval_one :=
    kernelPolynomial_eval_one n u h.support h.symmetric h.sum_eq_one

/-- Data certifying that `q` alternates between zero and `M` often enough
to solve the cubic weighted extremal problem.  The orientation is allowed
to be either `1` or `-1`, so the first node may be either a zero or a peak. -/
structure CubicZeroPeakCertificate (N : ℕ) (q : ℝ[X]) (M : ℝ) where
  /-- The orientation of the zero--peak alternation. -/
  orientation : ℝ
  /-- The orientation is a sign. -/
  orientation_eq : orientation = 1 ∨ orientation = -1
  /-- The nodes away from the distinguished endpoint `1`. -/
  nodes : Fin (N - 3 + 1) → ℝ
  /-- The nodes are strictly increasing. -/
  strictMono_nodes : StrictMono nodes
  /-- Every alternation node lies in `[-1, 1)`. -/
  nodes_mem_Ico : ∀ i, nodes i ∈ Set.Ico (-1 : ℝ) 1
  /-- The candidate numerator lies between zero and its peak on the interval. -/
  bounds : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ q.eval x ∧ q.eval x ≤ M
  /-- The peak value is attained. -/
  exists_peak : ∃ x ∈ Set.Icc (-1 : ℝ) 1, q.eval x = M
  /-- Values at successive nodes alternate between zero and `M`. -/
  node_value : ∀ i,
    q.eval (nodes i) =
      M / 2 * (1 - orientation * (-1 : ℝ) ^ (i : ℕ))

private theorem cubicWeightedRange_nonempty (p : ℝ[X]) :
    {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      r = |(1 - x) ^ 3 * p.eval x|}.Nonempty := by
  refine ⟨|(1 - 0) ^ 3 * p.eval 0|, 0, ?_, rfl⟩
  constructor <;> norm_num

private theorem cubicWeightedRange_bddAbove (p : ℝ[X]) :
    BddAbove {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      r = |(1 - x) ^ 3 * p.eval x|} := by
  let g : ℝ → ℝ := fun x ↦ |(1 - x) ^ 3 * p.eval x|
  have hg : Continuous g := by
    unfold g
    fun_prop
  have hset : {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      r = |(1 - x) ^ 3 * p.eval x|} = g '' Set.Icc (-1 : ℝ) 1 := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [hset]
  exact (isCompact_Icc.image hg).bddAbove

private theorem cubicWeightedValue_le_norm
    (p : ℝ[X]) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(1 - x) ^ 3 * p.eval x| ≤ cubicWeightedPolynomialNorm p := by
  unfold cubicWeightedPolynomialNorm
  exact le_csSup (cubicWeightedRange_bddAbove p) ⟨x, hx, rfl⟩

/-- The sixth-difference operator norm is eight times the cubic weighted
norm of the kernel polynomial. -/
theorem differenceSmoothness_six_eq_eight_mul_cubicWeightedPolynomialNorm
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    differenceSmoothness 6 u =
      8 * cubicWeightedPolynomialNorm (kernelPolynomial n u) := by
  let p := kernelPolynomial n u
  let A : Set ℝ := {a : ℝ | ∃ ξ : ℝ, a = differenceMultiplier 6 u ξ}
  let B : Set ℝ := {b : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    b = |(1 - x) ^ 3 * p.eval x|}
  have hvalue (ξ : ℝ) : differenceMultiplier 6 u ξ =
      8 * |(1 - Real.cos ξ) ^ 3 * p.eval (Real.cos ξ)| := by
    rw [differenceMultiplier_six]
    rw [kernelPolynomial_eval_cos n u support symmetric]
    have hnonneg : 0 ≤ (1 - Real.cos ξ) ^ 3 :=
      pow_nonneg (sub_nonneg.mpr (Real.cos_le_one ξ)) 3
    rw [abs_mul, abs_of_nonneg hnonneg]
    ring
  have hB_nonempty : B.Nonempty := by
    simpa [B, p] using cubicWeightedRange_nonempty (kernelPolynomial n u)
  have hB_bdd : BddAbove B := by
    simpa [B, p] using cubicWeightedRange_bddAbove (kernelPolynomial n u)
  have hA_nonempty : A.Nonempty := ⟨differenceMultiplier 6 u 0, 0, rfl⟩
  have hA_bdd : BddAbove A := by
    obtain ⟨M, hM⟩ := hB_bdd
    refine ⟨8 * M, ?_⟩
    rintro a ⟨ξ, rfl⟩
    rw [hvalue]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply hM
    exact ⟨Real.cos ξ, ⟨Real.neg_one_le_cos ξ, Real.cos_le_one ξ⟩, rfl⟩
  rw [differenceSmoothness_eq_multiplierNorm 6 u symmetric]
  change sSup A = 8 * sSup B
  apply le_antisymm
  · apply csSup_le hA_nonempty
    rintro a ⟨ξ, rfl⟩
    rw [hvalue]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply le_csSup hB_bdd
    exact ⟨Real.cos ξ, ⟨Real.neg_one_le_cos ξ, Real.cos_le_one ξ⟩, rfl⟩
  · have hsup : sSup B ≤ sSup A / 8 := by
      apply csSup_le hB_nonempty
      rintro b ⟨x, hx, rfl⟩
      have hle := le_csSup hA_bdd
        (⟨Real.arccos x, rfl⟩ : differenceMultiplier 6 u (Real.arccos x) ∈ A)
      rw [hvalue, Real.cos_arccos hx.1 hx.2] at hle
      linarith
    linarith

private theorem polynomial_eq_one_of_natDegree_le_zero
    (p : ℝ[X]) (hdeg : p.natDegree ≤ 0) (hone : p.eval 1 = 1) :
    p = 1 := by
  rw [eq_C_of_natDegree_le_zero hdeg]
  have h := hone
  rw [eq_C_of_natDegree_le_zero hdeg] at h
  simp only [eval_C] at h
  rw [h]
  simp

/-- An exact cubic factorization and a zero--peak certificate compute the
weighted norm of the proposed optimizer. -/
theorem cubicWeightedPolynomialNorm_eq_of_certificate
    {N : ℕ} {S q : ℝ[X]} {M : ℝ}
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate N q M) :
    cubicWeightedPolynomialNorm S = M := by
  let B : Set ℝ := {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    r = |(1 - x) ^ 3 * S.eval x|}
  have hvalue (x : ℝ) : (1 - x) ^ 3 * S.eval x = q.eval x := by
    have h := congrArg (fun p : ℝ[X] ↦ p.eval x) hSq
    simpa using h
  have hB_nonempty : B.Nonempty := by
    simpa [B] using cubicWeightedRange_nonempty S
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

/-- A cubic zero--peak certificate forces uniqueness among admissible
polynomials whose weighted norm is at most the certified peak. -/
theorem cubicWeightedPolynomial_eq_of_norm_le
    (N : ℕ) (hN : 3 ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleCubicWeightedPolynomial N p)
    (hS : IsAdmissibleCubicWeightedPolynomial N S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate N q M)
    (hnorm : cubicWeightedPolynomialNorm p ≤ M) :
    p = S := by
  by_cases hNthree : N = 3
  · subst N
    have hp_one := polynomial_eq_one_of_natDegree_le_zero p
      (by simpa using hp.degree_le) hp.eval_one
    have hS_one := polynomial_eq_one_of_natDegree_le_zero S
      (by simpa using hS.degree_le) hS.eval_one
    rw [hp_one, hS_one]
  have hNfour : 4 ≤ N := by omega
  let d : ℝ[X] := p - S
  let r : ℝ[X] := d /ₘ (X - C 1)
  have hdroot : d.IsRoot 1 := by
    simp [d, IsRoot, hp.eval_one, hS.eval_one]
  have hfactor : (X - C 1) * r = d :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hdroot
  have hddeg : d.natDegree ≤ N - 3 :=
    (natDegree_sub_le p S).trans (max_le hp.degree_le hS.degree_le)
  have hrdeg : r.natDegree < N - 3 := by
    dsimp [r]
    rw [natDegree_divByMonic _ (monic_X_sub_C 1), natDegree_X_sub_C]
    omega
  let t : ℝ[X] := (-certificate.orientation) • r
  have htdeg : t.natDegree < N - 3 :=
    (natDegree_smul_le (-certificate.orientation) r).trans_lt hrdeg
  have halt (i : Fin (N - 3 + 1)) :
      0 ≤ (-1 : ℝ) ^ (i : ℕ) * t.eval (certificate.nodes i) := by
    let x := certificate.nodes i
    have hxIco : x ∈ Set.Ico (-1 : ℝ) 1 := certificate.nodes_mem_Ico i
    have hx : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hxIco.1, hxIco.2.le⟩
    have hxpos : 0 < 1 - x := sub_pos.mpr hxIco.2
    have hpower : 0 < (1 - x) ^ 4 := pow_pos hxpos 4
    have hpweight_nonneg : 0 ≤ (1 - x) ^ 3 * p.eval x :=
      mul_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) 3) (hp.nonnegative x hx)
    have hpweight_abs : |(1 - x) ^ 3 * p.eval x| ≤
        cubicWeightedPolynomialNorm p := cubicWeightedValue_le_norm p x hx
    have hpweight_le : (1 - x) ^ 3 * p.eval x ≤ M := by
      calc
        (1 - x) ^ 3 * p.eval x ≤ |(1 - x) ^ 3 * p.eval x| := le_abs_self _
        _ ≤ cubicWeightedPolynomialNorm p := hpweight_abs
        _ ≤ M := hnorm
    have hSeval : (1 - x) ^ 3 * S.eval x = q.eval x := by
      have h := congrArg (fun a : ℝ[X] ↦ a.eval x) hSq
      simpa using h
    have hdeval : p.eval x - S.eval x = (x - 1) * r.eval x := by
      have h := congrArg (fun a : ℝ[X] ↦ a.eval x) hfactor
      simpa [d] using h.symm
    have hdiff : (1 - x) ^ 3 * p.eval x - q.eval x =
        -(1 - x) ^ 4 * r.eval x := by
      rw [← hSeval, ← mul_sub, hdeval]
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

/-- A certified cubic optimizer gives the sharp lower bound for every
admissible polynomial. -/
theorem cubicWeightedPolynomialNorm_ge_of_certificate
    (N : ℕ) (hN : 3 ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleCubicWeightedPolynomial N p)
    (hS : IsAdmissibleCubicWeightedPolynomial N S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate N q M) :
    M ≤ cubicWeightedPolynomialNorm p := by
  by_contra hnot
  have hlt : cubicWeightedPolynomialNorm p < M := lt_of_not_ge hnot
  have heq := cubicWeightedPolynomial_eq_of_norm_le N hN hp hS hSq
    certificate hlt.le
  rw [heq, cubicWeightedPolynomialNorm_eq_of_certificate hSq certificate] at hlt
  exact lt_irrefl _ hlt

/-- Equality in the certified cubic problem holds exactly at the proposed optimizer. -/
theorem cubicWeightedPolynomialNorm_eq_iff_of_certificate
    (N : ℕ) (hN : 3 ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleCubicWeightedPolynomial N p)
    (hS : IsAdmissibleCubicWeightedPolynomial N S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate N q M) :
    cubicWeightedPolynomialNorm p = M ↔ p = S := by
  constructor
  · intro hnorm
    exact cubicWeightedPolynomial_eq_of_norm_le N hN hp hS hSq
      certificate hnorm.le
  · rintro rfl
    exact cubicWeightedPolynomialNorm_eq_of_certificate hSq certificate

/-! ## Conditional kernel theorem -/

/-- The kernel reconstructed from the Chebyshev coefficients of a proposed
cubic weighted optimizer. -/
def certifiedSixthOrderKernel (n : ℕ) (S : ℝ[X]) : Kernel :=
  kernelOfPolynomial n S

/-- The polynomial symbol of the reconstructed kernel is the proposed optimizer. -/
theorem kernelPolynomial_certifiedSixthOrderKernel
    (n : ℕ)
    {S : ℝ[X]}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S) :
    kernelPolynomial n (certifiedSixthOrderKernel n S) = S := by
  apply kernelPolynomial_kernelOfPolynomial
  simpa using hS.degree_le

/-- A feasible cubic weighted polynomial reconstructs an admissible kernel. -/
theorem certifiedSixthOrderKernel_isAdmissible
    (n : ℕ)
    {S : ℝ[X]}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S) :
    IsAdmissibleKernel n (certifiedSixthOrderKernel n S) := by
  apply kernelOfPolynomial_isAdmissible
  · simpa using hS.degree_le
  · exact hS.nonnegative
  · exact hS.eval_one

/-- A certified cubic weighted optimizer reconstructs a kernel attaining
the corresponding sixth-order constant. -/
theorem certifiedSixthOrderKernel_attains
    (n : ℕ)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    differenceSmoothness 6 (certifiedSixthOrderKernel n S) = 8 * M := by
  let u := certifiedSixthOrderKernel n S
  have hu : IsAdmissibleKernel n u :=
    certifiedSixthOrderKernel_isAdmissible n hS
  calc
    differenceSmoothness 6 u =
        8 * cubicWeightedPolynomialNorm (kernelPolynomial n u) :=
      differenceSmoothness_six_eq_eight_mul_cubicWeightedPolynomialNorm
        n u hu.support hu.symmetric
    _ = 8 * cubicWeightedPolynomialNorm S := by
      rw [kernelPolynomial_certifiedSixthOrderKernel n hS]
    _ = 8 * M := by
      rw [cubicWeightedPolynomialNorm_eq_of_certificate hSq certificate]

/-- Every admissible kernel satisfies the sharp sixth-order lower bound
provided by a certified cubic weighted optimizer. -/
theorem sixthOrderSmoothness_ge_of_certificate
    (n : ℕ)
    (u : Kernel)
    (hu : IsAdmissibleKernel n u)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    8 * M ≤ differenceSmoothness 6 u := by
  calc
    8 * M ≤ 8 * cubicWeightedPolynomialNorm (kernelPolynomial n u) := by
      gcongr
      exact cubicWeightedPolynomialNorm_ge_of_certificate
        (n + 3) (by omega) hu.cubicKernelPolynomial hS hSq certificate
    _ = differenceSmoothness 6 u :=
      (differenceSmoothness_six_eq_eight_mul_cubicWeightedPolynomialNorm
        n u hu.support hu.symmetric).symm

/-- Equality in the conditional sixth-order kernel bound is equivalent to
equality of the associated kernel polynomial with the certified optimizer. -/
theorem sixthOrderSmoothness_eq_iff_kernelPolynomial_eq_of_certificate
    (n : ℕ)
    (u : Kernel)
    (hu : IsAdmissibleKernel n u)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    differenceSmoothness 6 u = 8 * M ↔ kernelPolynomial n u = S := by
  rw [differenceSmoothness_six_eq_eight_mul_cubicWeightedPolynomialNorm
    n u hu.support hu.symmetric]
  constructor
  · intro hequality
    apply (cubicWeightedPolynomialNorm_eq_iff_of_certificate
      (n + 3) (by omega) hu.cubicKernelPolynomial hS hSq certificate).1
    linarith
  · intro hpolynomial
    have hnorm := (cubicWeightedPolynomialNorm_eq_iff_of_certificate
      (n + 3) (by omega) hu.cubicKernelPolynomial hS hSq certificate).2
        hpolynomial
    linarith

/-- Equality in the conditional sixth-order bound characterizes the
coefficient-reconstructed kernel itself. -/
theorem sixthOrderSmoothness_eq_iff_eq_certifiedKernel
    (n : ℕ)
    (u : Kernel)
    (hu : IsAdmissibleKernel n u)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    differenceSmoothness 6 u = 8 * M ↔
      u = certifiedSixthOrderKernel n S := by
  constructor
  · intro hattains
    apply kernel_eq_of_kernelPolynomial_eq n hu.support hu.symmetric
      (certifiedSixthOrderKernel_isAdmissible n hS).support
      (certifiedSixthOrderKernel_isAdmissible n hS).symmetric
    exact ((sixthOrderSmoothness_eq_iff_kernelPolynomial_eq_of_certificate
      n u hu hS hSq certificate).1 hattains).trans
        (kernelPolynomial_certifiedSixthOrderKernel n hS).symm
  · rintro rfl
    exact certifiedSixthOrderKernel_attains n hS hSq certificate

/-- A cubic zero--peak certificate supplies an admissible kernel attaining
the conditional sixth-order constant. -/
theorem exists_certifiedSixthOrderKernel
    (n : ℕ)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    ∃ u : Kernel,
      IsAdmissibleKernel n u ∧ differenceSmoothness 6 u = 8 * M :=
  ⟨certifiedSixthOrderKernel n S,
    certifiedSixthOrderKernel_isAdmissible n hS,
    certifiedSixthOrderKernel_attains n hS hSq certificate⟩

/-- The kernel reconstructed from a certified cubic optimizer is the unique
admissible kernel attaining the conditional sixth-order constant. -/
theorem existsUnique_certifiedSixthOrderKernel
    (n : ℕ)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧ differenceSmoothness 6 u = 8 * M := by
  refine ⟨certifiedSixthOrderKernel n S,
    ⟨certifiedSixthOrderKernel_isAdmissible n hS,
      certifiedSixthOrderKernel_attains n hS hSq certificate⟩, ?_⟩
  intro u hu
  exact (sixthOrderSmoothness_eq_iff_eq_certifiedKernel
    n u hu.1 hS hSq certificate).1 hu.2

end JoseSmoothest
