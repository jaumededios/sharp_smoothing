import JoseSmoothest.EvenOrder.ActiveSetPerturbation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Equioscillation for the generic even-order weighted problem

This file begins the necessity half of the generic weighted minimax theorem.
It records the minimizer predicate, settles the diagonal case `N = m`, and
proves the positivity needed to normalize a non-diagonal minimizer.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

/-- An admissible polynomial whose weighted norm is no larger than that of
any other admissible polynomial. -/
def IsEvenWeightedMinimizer
    (m N : ℕ) (S : ℝ[X]) : Prop :=
  IsAdmissibleEvenWeightedPolynomial m N S ∧
    ∀ p, IsAdmissibleEvenWeightedPolynomial m N p →
      evenWeightedPolynomialNorm m S ≤ evenWeightedPolynomialNorm m p

/-- In the diagonal problem `N = m`, admissibility forces the constant
polynomial one. -/
theorem admissible_eq_one_of_same_order
    {m : ℕ} (_hm : 1 ≤ m) {p : ℝ[X]}
    (hp : IsAdmissibleEvenWeightedPolynomial m m p) :
    p = 1 := by
  have hdeg : p.natDegree ≤ 0 := by
    simpa using hp.degree_le
  rw [eq_C_of_natDegree_le_zero hdeg]
  have hone := hp.eval_one
  rw [eq_C_of_natDegree_le_zero hdeg] at hone
  simp only [eval_C] at hone
  rw [hone]
  simp

private def diagonalEvenZeroPeakCertificateAux
    (m : ℕ) :
    EvenZeroPeakCertificate m m
      ((Polynomial.C 1 - Polynomial.X) ^ m) ((2 : ℝ) ^ m) where
  orientation := -1
  orientation_eq := Or.inr rfl
  nodes := fun _ ↦ -1
  strictMono_nodes := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    simp only [Nat.sub_self, zero_add] at hi hj
    have hij_eq : i = j := by
      apply Fin.ext
      omega
    exact (hij.ne hij_eq).elim
  nodes_mem_Ico := by
    intro i
    constructor <;> norm_num
  bounds := by
    intro x hx
    simp only [eval_pow, eval_sub, eval_C, eval_X]
    constructor
    · exact pow_nonneg (by linarith [hx.2]) m
    · have hbase : 1 - x ≤ 2 := by linarith [hx.1]
      exact pow_le_pow_left₀ (by linarith [hx.2]) hbase m
  exists_peak := by
    refine ⟨-1, ⟨le_rfl, by norm_num⟩, ?_⟩
    norm_num
  node_value := by
    intro i
    have hi : (i : ℕ) = 0 := by omega
    simp [hi]
    ring

/-- The single endpoint-away node certifies the diagonal weighted problem. -/
def diagonalEvenZeroPeakCertificate
    (m : ℕ) (_hm : 1 ≤ m) :
    EvenZeroPeakCertificate m m
      ((Polynomial.C 1 - Polynomial.X) ^ m) ((2 : ℝ) ^ m) :=
  diagonalEvenZeroPeakCertificateAux m

/-- The weighted norm of the constant polynomial one is the endpoint value
`2 ^ m`. -/
theorem evenWeightedPolynomialNorm_one (m : ℕ) :
    evenWeightedPolynomialNorm m 1 = (2 : ℝ) ^ m := by
  apply evenWeightedPolynomialNorm_eq_of_certificate
    (q := (Polynomial.C 1 - Polynomial.X) ^ m)
  · simp [evenWeightedNumerator]
  · exact diagonalEvenZeroPeakCertificateAux m

private def coefficientPolynomial (d : ℕ)
    (a : Fin (d + 1) → ℝ) : ℝ[X] :=
  ((degreeLTEquiv ℝ (d + 1)).symm a : degreeLT ℝ (d + 1)).1

private theorem coefficientPolynomial_mem_degreeLT
    (d : ℕ) (a : Fin (d + 1) → ℝ) :
    coefficientPolynomial d a ∈ degreeLT ℝ (d + 1) :=
  ((degreeLTEquiv ℝ (d + 1)).symm a : degreeLT ℝ (d + 1)).2

private theorem coefficientPolynomial_natDegree_le
    (d : ℕ) (a : Fin (d + 1) → ℝ) :
    (coefficientPolynomial d a).natDegree ≤ d := by
  by_cases hp : coefficientPolynomial d a = 0
  · simp [hp]
  · have hdeg := mem_degreeLT.mp (coefficientPolynomial_mem_degreeLT d a)
    rw [degree_eq_natDegree hp] at hdeg
    have hnat : (coefficientPolynomial d a).natDegree < d + 1 := by
      exact_mod_cast hdeg
    omega

private theorem coefficientPolynomial_eval
    (d : ℕ) (a : Fin (d + 1) → ℝ) (x : ℝ) :
    (coefficientPolynomial d a).eval x =
      ∑ i, a i * x ^ (i : ℕ) := by
  have h := eval_eq_sum_degreeLTEquiv
    (coefficientPolynomial_mem_degreeLT d a) x
  simpa only [coefficientPolynomial,
    (degreeLTEquiv ℝ (d + 1)).apply_symm_apply] using h

private theorem continuous_coefficientPolynomial_eval
    (d : ℕ) (x : ℝ) :
    Continuous fun a : Fin (d + 1) → ℝ ↦
      (coefficientPolynomial d a).eval x := by
  simp_rw [coefficientPolynomial_eval]
  fun_prop

private theorem continuous_coefficientWeightedNorm
    (m d : ℕ) :
    Continuous fun a : Fin (d + 1) → ℝ ↦
      evenWeightedPolynomialNorm m (coefficientPolynomial d a) := by
  let f : (Fin (d + 1) → ℝ) → ℝ → ℝ := fun a x ↦
    |(1 - x) ^ m * (coefficientPolynomial d a).eval x|
  have hf : Continuous ↿f := by
    dsimp only [f, Function.uncurry]
    simp_rw [coefficientPolynomial_eval]
    fun_prop
  have hrange (a : Fin (d + 1) → ℝ) :
      {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        r = |(1 - x) ^ m * (coefficientPolynomial d a).eval x|} =
        f a '' Set.Icc (-1 : ℝ) 1 := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  simp_rw [evenWeightedPolynomialNorm, hrange]
  exact isCompact_Icc.continuous_sSup hf

private def compactnessNode (d : ℕ) (i : Fin (d + 1)) : ℝ :=
  -((i : ℝ) / (d + 1))

private theorem compactnessNode_injective (d : ℕ) :
    Function.Injective (compactnessNode d) := by
  intro i j hij
  have hden : (d + 1 : ℝ) ≠ 0 := by positivity
  change -((i : ℝ) / (d + 1)) = -((j : ℝ) / (d + 1)) at hij
  have hdiv : (i : ℝ) / (d + 1) = (j : ℝ) / (d + 1) :=
    neg_inj.mp hij
  have hcast : (i : ℝ) = (j : ℝ) := (div_left_inj' hden).mp hdiv
  apply Fin.ext
  exact_mod_cast hcast

private theorem compactnessNode_mem_Icc
    (d : ℕ) (i : Fin (d + 1)) :
    compactnessNode d i ∈ Set.Icc (-1 : ℝ) 0 := by
  have hi : (i : ℕ) ≤ d := by omega
  have hden : 0 < (d + 1 : ℝ) := by positivity
  have hi_real : (i : ℝ) ≤ d := by exact_mod_cast hi
  have hquot : (i : ℝ) / (d + 1) ≤ 1 := by
    apply (div_le_one hden).2
    calc
      (i : ℝ) ≤ (d : ℝ) := hi_real
      _ ≤ (d : ℝ) + 1 := by linarith
  constructor
  · dsimp [compactnessNode]
    linarith
  · exact neg_nonpos.mpr (div_nonneg (Nat.cast_nonneg _) hden.le)

private def interpolationLinearMap (d : ℕ) :
    (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) where
  toFun a i := (coefficientPolynomial d a).eval (compactnessNode d i)
  map_add' a b := by
    funext i
    simp only [coefficientPolynomial_eval, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  map_smul' c a := by
    funext i
    simp only [coefficientPolynomial_eval]
    change (∑ j, (c * a j) * compactnessNode d i ^ (j : ℕ)) =
      c * ∑ j, a j * compactnessNode d i ^ (j : ℕ)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

private theorem interpolationLinearMap_injective (d : ℕ) :
    Function.Injective (interpolationLinearMap d) := by
  intro a b hab
  let q : ℝ[X] := coefficientPolynomial d a - coefficientPolynomial d b
  have hqmem : q ∈ degreeLT ℝ (d + 1) :=
    Submodule.sub_mem _ (coefficientPolynomial_mem_degreeLT d a)
      (coefficientPolynomial_mem_degreeLT d b)
  have hqdeg : q.degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    simpa using mem_degreeLT.mp hqmem
  have hqeval : ∀ i ∈ (Finset.univ : Finset (Fin (d + 1))),
      q.eval (compactnessNode d i) = 0 := by
    intro i hi
    have hi_eval := congrFun hab i
    dsimp only [interpolationLinearMap] at hi_eval
    dsimp only [q]
    rw [eval_sub, sub_eq_zero]
    exact hi_eval
  have hqzero : q = 0 :=
    eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ
      (compactnessNode_injective d).injOn hqdeg hqeval
  have hpoly : coefficientPolynomial d a = coefficientPolynomial d b :=
    sub_eq_zero.mp hqzero
  apply (degreeLTEquiv ℝ (d + 1)).symm.injective
  apply Subtype.ext
  exact hpoly

private def feasibleCoefficientSet (m d : ℕ) :
    Set (Fin (d + 1) → ℝ) :=
  {a | (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ (coefficientPolynomial d a).eval x) ∧
    (coefficientPolynomial d a).eval 1 = 1 ∧
    evenWeightedPolynomialNorm m (coefficientPolynomial d a) ≤ (2 : ℝ) ^ m}

private theorem feasibleCoefficientSet_isClosed (m d : ℕ) :
    IsClosed (feasibleCoefficientSet m d) := by
  let A : Set (Fin (d + 1) → ℝ) :=
    {a | ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ (coefficientPolynomial d a).eval x}
  let B : Set (Fin (d + 1) → ℝ) :=
    {a | (coefficientPolynomial d a).eval 1 = 1}
  let C : Set (Fin (d + 1) → ℝ) :=
    {a | evenWeightedPolynomialNorm m (coefficientPolynomial d a) ≤ (2 : ℝ) ^ m}
  have hA : IsClosed A := by
    have heq : A = ⋂ x ∈ Set.Icc (-1 : ℝ) 1,
        {a | 0 ≤ (coefficientPolynomial d a).eval x} := by
      ext a
      simp [A]
    rw [heq]
    exact isClosed_biInter fun x hx ↦
      isClosed_le continuous_const (continuous_coefficientPolynomial_eval d x)
  have hB : IsClosed B := by
    exact isClosed_eq (continuous_coefficientPolynomial_eval d 1) continuous_const
  have hC : IsClosed C := by
    exact isClosed_le (continuous_coefficientWeightedNorm m d) continuous_const
  have heq : feasibleCoefficientSet m d = A ∩ B ∩ C := by
    ext a
    simp only [feasibleCoefficientSet, Set.mem_setOf_eq, Set.mem_inter_iff, A, B, C]
    tauto
  rw [heq]
  exact (hA.inter hB).inter hC

private theorem feasibleCoefficientSet_isBounded (m d : ℕ) :
    Bornology.IsBounded (feasibleCoefficientSet m d) := by
  obtain ⟨K, hKpos, hanti⟩ :=
    (interpolationLinearMap d).injective_iff_antilipschitz.mp
      (interpolationLinearMap_injective d)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(K : ℝ) * (2 : ℝ) ^ m, ?_⟩
  intro a ha
  have hC : 0 ≤ (2 : ℝ) ^ m := by positivity
  have hEnorm : ‖interpolationLinearMap d a‖ ≤ (2 : ℝ) ^ m := by
    apply (pi_norm_le_iff_of_nonneg hC).2
    intro i
    let x := compactnessNode d i
    have hx0 : x ∈ Set.Icc (-1 : ℝ) 0 := compactnessNode_mem_Icc d i
    have hx : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hx0.1, hx0.2.trans zero_le_one⟩
    have hweight : 1 ≤ (1 - x) ^ m := one_le_pow₀ (by linarith [hx0.2])
    have habsp : |(coefficientPolynomial d a).eval x| ≤
        |(1 - x) ^ m * (coefficientPolynomial d a).eval x| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) m)]
      exact le_mul_of_one_le_left (abs_nonneg _) hweight
    have hvalue := evenWeightedValue_le_norm m (coefficientPolynomial d a) hx
    change |(coefficientPolynomial d a).eval x| ≤ (2 : ℝ) ^ m
    exact habsp.trans (hvalue.trans ha.2.2)
  exact (ZeroHomClass.bound_of_antilipschitz
    (interpolationLinearMap d) hanti a).trans
      (mul_le_mul_of_nonneg_left hEnorm K.coe_nonneg)

/-- The generic weighted problem admits a minimizer. -/
theorem exists_evenWeightedMinimizer
    (m N : ℕ) (_hm : 1 ≤ m) (_hN : m ≤ N) :
    ∃ S, IsEvenWeightedMinimizer m N S := by
  let d := N - m
  have hcompact : IsCompact (feasibleCoefficientSet m d) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨feasibleCoefficientSet_isClosed m d,
        feasibleCoefficientSet_isBounded m d⟩
  have hone_mem : (1 : ℝ[X]) ∈ degreeLT ℝ (d + 1) := by
    rw [degreeLT_succ_eq_degreeLE, mem_degreeLE]
    simp
  let aOne : Fin (d + 1) → ℝ :=
    degreeLTEquiv ℝ (d + 1) ⟨1, hone_mem⟩
  have hpolyOne : coefficientPolynomial d aOne = 1 := by
    change (((degreeLTEquiv ℝ (d + 1)).symm
      ((degreeLTEquiv ℝ (d + 1)) ⟨1, hone_mem⟩) :
        degreeLT ℝ (d + 1)) : ℝ[X]) = 1
    rw [(degreeLTEquiv ℝ (d + 1)).symm_apply_apply]
  have hnonempty : (feasibleCoefficientSet m d).Nonempty := by
    refine ⟨aOne, ?_⟩
    simp only [feasibleCoefficientSet, Set.mem_setOf_eq, hpolyOne]
    refine ⟨?_, by simp, ?_⟩
    · intro x hx
      simp
    · rw [evenWeightedPolynomialNorm_one]
  obtain ⟨a, ha, hmin⟩ := hcompact.exists_isMinOn hnonempty
    (continuous_coefficientWeightedNorm m d).continuousOn
  refine ⟨coefficientPolynomial d a, ?_⟩
  constructor
  · refine {
      degree_le := (coefficientPolynomial_natDegree_le d a).trans ?_
      nonnegative := ha.1
      eval_one := ha.2.1 }
    exact le_rfl
  · intro p hp
    by_cases hpC : evenWeightedPolynomialNorm m p ≤ (2 : ℝ) ^ m
    · have hp_mem : p ∈ degreeLT ℝ (d + 1) := by
        rw [mem_degreeLT]
        by_cases hp0 : p = 0
        · simp [hp0]
        · rw [degree_eq_natDegree hp0]
          have hpdeg : p.natDegree ≤ d := by
            exact hp.degree_le.trans (by simp [d])
          have hpdeg' : p.natDegree < d + 1 := by omega
          exact_mod_cast hpdeg'
      let b : Fin (d + 1) → ℝ :=
        degreeLTEquiv ℝ (d + 1) ⟨p, hp_mem⟩
      have hpolyb : coefficientPolynomial d b = p := by
        change (((degreeLTEquiv ℝ (d + 1)).symm
          ((degreeLTEquiv ℝ (d + 1)) ⟨p, hp_mem⟩) :
            degreeLT ℝ (d + 1)) : ℝ[X]) = p
        rw [(degreeLTEquiv ℝ (d + 1)).symm_apply_apply]
      have hb : b ∈ feasibleCoefficientSet m d := by
        simp only [feasibleCoefficientSet, Set.mem_setOf_eq, hpolyb]
        exact ⟨hp.nonnegative, hp.eval_one, hpC⟩
      have hminb := hmin hb
      change evenWeightedPolynomialNorm m (coefficientPolynomial d a) ≤
        evenWeightedPolynomialNorm m (coefficientPolynomial d b) at hminb
      simpa only [hpolyb] using hminb
    · exact ha.2.2.trans (le_of_not_ge hpC)

/-- Complete certified extremal data for the diagonal problem `N = m`. -/
def diagonalEvenWeightedExtremalData
    (m : ℕ) (hm : 1 ≤ m) :
    EvenWeightedExtremalData m m where
  S := 1
  q := (Polynomial.C 1 - Polynomial.X) ^ m
  M := (2 : ℝ) ^ m
  admissible := {
    degree_le := by simp
    nonnegative := by simp
    eval_one := by simp }
  factorization := by simp [evenWeightedNumerator]
  certificate := diagonalEvenZeroPeakCertificate m hm

/-- Every admissible weighted polynomial has strictly positive weighted norm.

The proof uses positivity of the polynomial on a sufficiently small interval
to the left of the normalized endpoint `1`. -/
theorem evenWeightedPolynomialNorm_pos_of_admissible
    {m N : ℕ} (_hm : 1 ≤ m) {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S) :
    0 < evenWeightedPolynomialNorm m S := by
  have hpositive_nhds : {x : ℝ | 0 < S.eval x} ∈ nhds (1 : ℝ) := by
    have htarget : {y : ℝ | 0 < y} ∈ nhds (S.eval 1) := by
      change Set.Ioi 0 ∈ nhds (S.eval 1)
      rw [hS.eval_one]
      exact Ioi_mem_nhds zero_lt_one
    exact S.continuousAt htarget
  obtain ⟨a, b, hab, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hpositive_nhds
  let c : ℝ := max a (-1)
  let x : ℝ := (c + 1) / 2
  have hac : a ≤ c := le_max_left _ _
  have hnegc : -1 ≤ c := le_max_right _ _
  have hc_one : c < 1 := by
    dsimp [c]
    exact max_lt hab.1 (by norm_num)
  have hax : a < x := by
    dsimp [x]
    linarith
  have hxb : x < b := by
    dsimp [x]
    linarith [hab.2]
  have hxmem : x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · dsimp [x]
      linarith
    · dsimp [x]
      linarith
  have hSx : 0 < S.eval x := hsub ⟨hax, hxb⟩
  have hweight : 0 < (1 - x) ^ m * S.eval x := by
    have hxlt : x < 1 := by
      dsimp [x]
      linarith
    exact mul_pos (pow_pos (sub_pos.mpr hxlt) m) hSx
  have hle := evenWeightedValue_le_norm m S hxmem
  rw [abs_of_pos hweight] at hle
  exact hweight.trans_le hle

/-- A strict separator of the zero and peak active sets contradicts weighted
minimality. -/
theorem not_isEvenWeightedMinimizer_of_separator
    {m N : ℕ} (hm : 1 ≤ m) (hN : m < N)
    {S : ℝ[X]}
    (hS : IsAdmissibleEvenWeightedPolynomial m N S)
    (hsep : StrictPolynomialSeparator (N - m)
      (zeroActiveSet S) (peakActiveSet m S)) :
    ¬ IsEvenWeightedMinimizer m N S := by
  intro hmin
  obtain ⟨p, hp, hlt⟩ :=
    exists_strict_weighted_improvement_of_separator hm hN hS hsep
  exact (not_lt_of_ge (hmin.2 p hp)) hlt

theorem nonempty_evenZeroPeakCertificate_of_minimizer
    {m N : ℕ} (hm : 1 ≤ m) (hN : m ≤ N)
    {S : ℝ[X]} (hS : IsEvenWeightedMinimizer m N S) :
    Nonempty (EvenZeroPeakCertificate m N
      (evenWeightedNumerator m S)
      (evenWeightedPolynomialNorm m S)) := by
  by_cases hdiag : N = m
  · subst N
    have hSone : S = 1 := admissible_eq_one_of_same_order hm hS.1
    subst S
    exact ⟨by
      simpa [evenWeightedNumerator, evenWeightedPolynomialNorm_one] using
        diagonalEvenZeroPeakCertificate m hm⟩
  · have hlt : m < N := lt_of_le_of_ne hN (Ne.symm hdiag)
    obtain halt | hsep := finite_alternation_or_separator (N - m)
      (zeroActiveSet_finite hS.1) (peakActiveSet_finite hm hS.1)
      (activeSets_disjoint hm hS.1) (peakActiveSet_nonempty hm hS.1)
    · let A := halt.some
      refine ⟨{
        orientation := A.orientation
        orientation_eq := A.orientation_eq
        nodes := A.nodes
        strictMono_nodes := A.strictMono_nodes
        nodes_mem_Ico := ?_
        bounds := ?_
        exists_peak := ?_
        node_value := ?_ }⟩
      · intro i
        rcases A.node_mem i with hzero | hpeak
        · have hx := hzero.2.1
          refine ⟨hx.1, lt_of_le_of_ne hx.2 ?_⟩
          intro heq
          have hroot := hzero.2.2
          rw [heq, hS.1.eval_one] at hroot
          norm_num at hroot
        · have hx := hpeak.2.1
          refine ⟨hx.1, lt_of_le_of_ne hx.2 ?_⟩
          intro heq
          have hpeak_eq := hpeak.2.2
          rw [heq] at hpeak_eq
          have hqone : (evenWeightedNumerator m S).eval 1 = 0 := by
            simp [evenWeightedNumerator, Nat.ne_zero_of_lt hm]
          rw [hqone] at hpeak_eq
          exact (ne_of_gt (evenWeightedPolynomialNorm_pos_of_admissible hm hS.1))
            hpeak_eq.symm
      · intro x hx
        have hqeval : (evenWeightedNumerator m S).eval x =
            (1 - x) ^ m * S.eval x := by
          simp [evenWeightedNumerator]
        rw [hqeval]
        have hnonneg : 0 ≤ (1 - x) ^ m * S.eval x :=
          mul_nonneg (pow_nonneg (sub_nonneg.mpr hx.2) m)
            (hS.1.nonnegative x hx)
        exact ⟨hnonneg,
          (le_abs_self _).trans (evenWeightedValue_le_norm m S hx)⟩
      · obtain ⟨x, hx⟩ := peakActiveSet_nonempty hm hS.1
        exact ⟨x, hx.1, hx.2⟩
      · intro i
        rcases A.node_mem i with hzero | hpeak
        · rw [hzero.1]
          simp [evenWeightedNumerator, hzero.2.2]
        · rw [hpeak.1, hpeak.2.2]
          ring
    · exact (not_isEvenWeightedMinimizer_of_separator hm hlt hS.1 hsep.some hS).elim

/-- Every minimizer has the full zero--peak alternation certificate. -/
noncomputable def evenZeroPeakCertificate_of_minimizer
    {m N : ℕ} (hm : 1 ≤ m) (hN : m ≤ N)
    {S : ℝ[X]} (hS : IsEvenWeightedMinimizer m N S) :
    EvenZeroPeakCertificate m N
      (evenWeightedNumerator m S)
      (evenWeightedPolynomialNorm m S) :=
  (nonempty_evenZeroPeakCertificate_of_minimizer hm hN hS).some

/-- The weighted problem has unconditional certified extremal data. -/
theorem exists_evenWeightedExtremalData
    (m N : ℕ) (hm : 1 ≤ m) (hN : m ≤ N) :
    Nonempty (EvenWeightedExtremalData m N) := by
  obtain ⟨S, hS⟩ := exists_evenWeightedMinimizer m N hm hN
  exact ⟨{
    S := S
    q := evenWeightedNumerator m S
    M := evenWeightedPolynomialNorm m S
    admissible := hS.1
    factorization := rfl
    certificate := evenZeroPeakCertificate_of_minimizer hm hN hS }⟩

/-- The generic weighted minimizer exists and is unique. -/
theorem existsUnique_evenWeightedMinimizer
    (m N : ℕ) (hm : 1 ≤ m) (hN : m ≤ N) :
    ∃! S, IsEvenWeightedMinimizer m N S := by
  obtain ⟨S, hS⟩ := exists_evenWeightedMinimizer m N hm hN
  refine ⟨S, hS, ?_⟩
  intro p hp
  have certificate := evenZeroPeakCertificate_of_minimizer hm hN hS
  exact evenWeightedPolynomial_eq_of_norm_le m N hN hp.1 hS.1 rfl
    certificate (hp.2 S hS.1)

end JoseSmoothest
