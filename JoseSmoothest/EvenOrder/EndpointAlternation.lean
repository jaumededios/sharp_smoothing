import JoseSmoothest.EvenOrder.Equioscillation
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Endpoint alternation for the generic even-order problem

This file normalizes the zero--peak extremal polynomial to take values in
`[-1, 1]`.  It then uses the endpoint contact and the interior extrema to
exhaust the derivative roots.  In particular the first alternation node is
forced to be `-1`, and the distinguished endpoint `1` can be appended to the
alternation family.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

/-- A polynomial of degree `N`, with exact contact of order `m` at `1`, whose
endpoint-inclusive nodes alternate between the values `1` and `-1`. -/
structure EndpointAlternant
    (m N : ℕ) (Z : ℝ[X]) where
  one_le_m : 1 ≤ m
  m_le_N : m ≤ N
  natDegree_eq : Z.natDegree = N
  bounds : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    -1 ≤ Z.eval x ∧ Z.eval x ≤ 1
  eval_one : Z.eval 1 = 1
  contact_one : rootMultiplicity 1 (1 - Z) = m
  orientation : ℝ
  orientation_eq : orientation = 1 ∨ orientation = -1
  nodes : Fin (N - m + 2) → ℝ
  strictMono_nodes : StrictMono nodes
  node_zero : nodes 0 = -1
  node_last : nodes (Fin.last (N - m + 1)) = 1
  node_value : ∀ j,
    Z.eval (nodes j) =
      orientation * (-1 : ℝ) ^ (j : ℕ)

namespace EvenWeightedExtremalData

variable {m N : ℕ} (E : EvenWeightedExtremalData m N)

/-- The affine normalization which sends numerator zeroes to `1` and peaks
to `-1`. -/
def normalizedAlternant : ℝ[X] :=
  1 - Polynomial.C (2 / E.M) * E.q

/-- The certified peak is strictly positive. -/
theorem M_pos (hm : 1 ≤ m) (_hN : m ≤ N) : 0 < E.M := by
  rw [← E.norm_eq]
  exact evenWeightedPolynomialNorm_pos_of_admissible hm E.admissible

private theorem normalizedAlternant_eval (x : ℝ) :
    E.normalizedAlternant.eval x = 1 - (2 / E.M) * E.q.eval x := by
  simp [normalizedAlternant]

private theorem normalizedAlternant_eval_one (hm : 1 ≤ m) :
    E.normalizedAlternant.eval 1 = 1 := by
  rw [normalizedAlternant_eval]
  have hq : E.q.eval 1 = 0 := by
    rw [← E.factorization]
    simp [evenWeightedNumerator, Nat.ne_zero_of_lt hm]
  rw [hq]
  ring

private theorem normalizedAlternant_bounds
    (hm : 1 ≤ m) (hN : m ≤ N) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    -1 ≤ E.normalizedAlternant.eval x ∧
      E.normalizedAlternant.eval x ≤ 1 := by
  have hM := E.M_pos hm hN
  have hq := E.certificate.bounds x hx
  rw [normalizedAlternant_eval]
  constructor <;> (field_simp; nlinarith)

private theorem normalizedAlternant_node_value
    (hm : 1 ≤ m) (hN : m ≤ N)
    (i : Fin (N - m + 1)) :
    E.normalizedAlternant.eval (E.certificate.nodes i) =
      E.certificate.orientation * (-1 : ℝ) ^ (i : ℕ) := by
  have hM := E.M_pos hm hN
  rw [normalizedAlternant_eval, E.certificate.node_value]
  field_simp
  ring

private theorem normalizedAlternant_natDegree_le (hN : m ≤ N) :
    E.normalizedAlternant.natDegree ≤ N := by
  have hqdeg : E.q.natDegree ≤ N := by
    rw [← E.factorization]
    unfold evenWeightedNumerator
    calc
      (((C (1 : ℝ) - X) ^ m) * E.S).natDegree
          ≤ ((C (1 : ℝ) - X) ^ m).natDegree + E.S.natDegree :=
            natDegree_mul_le
      _ ≤ m + (N - m) := by
        gcongr
        · calc
            ((C (1 : ℝ) - X) ^ m).natDegree
                ≤ m * (C (1 : ℝ) - X).natDegree := natDegree_pow_le
            _ ≤ m * 1 := Nat.mul_le_mul_left m (natDegree_sub_le _ _ |>.trans
              (max_le (by simp) (by simp)))
            _ = m := by omega
        · exact E.admissible.degree_le
      _ = N := Nat.add_sub_of_le hN
  unfold normalizedAlternant
  exact (natDegree_sub_le _ _).trans
    (max_le (by simp) ((natDegree_C_mul_le _ _).trans hqdeg))

private theorem normalizedAlternant_contact_one
    (hm : 1 ≤ m) (hN : m ≤ N) :
    rootMultiplicity 1 (1 - E.normalizedAlternant) = m := by
  have hM : E.M ≠ 0 := ne_of_gt (E.M_pos hm hN)
  have hS : E.S ≠ 0 := by
    intro hzero
    have := E.admissible.eval_one
    rw [hzero] at this
    norm_num at this
  have hfac :
      1 - E.normalizedAlternant =
        C (2 / E.M) * ((C 1 - X) ^ m * E.S) := by
    rw [normalizedAlternant, ← E.factorization]
    simp only [evenWeightedNumerator]
    ring
  have hscalar : C (2 / E.M : ℝ) ≠ 0 := by
    apply C_ne_zero.mpr
    positivity
  have hpow : (C (1 : ℝ) - X) ^ m ≠ 0 := by
    exact pow_ne_zero _ (sub_ne_zero.mpr (by simpa using (X_ne_C (1 : ℝ)).symm))
  rw [hfac, rootMultiplicity_mul (mul_ne_zero hscalar (mul_ne_zero hpow hS)),
    rootMultiplicity_mul (mul_ne_zero hpow hS)]
  have hC : rootMultiplicity 1 (C (2 / E.M : ℝ)) = 0 := by
    exact rootMultiplicity_eq_zero (not_isRoot_C _ _ (by positivity))
  have hSroot : rootMultiplicity 1 E.S = 0 := by
    apply rootMultiplicity_eq_zero
    simp [IsRoot, E.admissible.eval_one]
  have hpowmult : rootMultiplicity 1 ((C (1 : ℝ) - X) ^ m) = m := by
    have hfactor : (C (1 : ℝ) - X) ^ m =
        C ((-1 : ℝ) ^ m) * (X - C 1) ^ m := by
      rw [show C (1 : ℝ) - X = -(X - C 1) by ring]
      rw [neg_pow]
      congr 1
      rw [show (-1 : ℝ[X]) = C (-1 : ℝ) by norm_num]
      exact (map_pow C (-1 : ℝ) m).symm
    rw [hfactor, rootMultiplicity_mul (mul_ne_zero
      (C_ne_zero.mpr (by positivity)) (pow_ne_zero _ (X_sub_C_ne_zero 1))),
      rootMultiplicity_C, rootMultiplicity_X_sub_C_pow]
    simp
  rw [hC, hpowmult, hSroot]
  omega

private theorem normalizedAlternant_derivative_ne_zero
    (hm : 1 ≤ m) (hN : m ≤ N) :
    derivative E.normalizedAlternant ≠ 0 := by
  intro hderiv
  have hconst := eq_C_of_derivative_eq_zero hderiv
  have hZ : E.normalizedAlternant = 1 := by
    rw [hconst]
    have hone := E.normalizedAlternant_eval_one hm
    rw [hconst] at hone
    simp only [eval_C] at hone
    rw [hone]
    simp
  have hcontact := E.normalizedAlternant_contact_one hm hN
  rw [hZ] at hcontact
  simp at hcontact
  omega

private theorem endpoint_power_dvd_derivative
    (hm : 1 ≤ m) (hN : m ≤ N) :
    (X - C (1 : ℝ)) ^ (m - 1) ∣ derivative E.normalizedAlternant := by
  have hcontact := E.normalizedAlternant_contact_one hm hN
  have hsubne : 1 - E.normalizedAlternant ≠ 0 := by
    intro hzero
    rw [hzero, rootMultiplicity_zero] at hcontact
    omega
  have hpow : (X - C (1 : ℝ)) ^ m ∣ 1 - E.normalizedAlternant :=
    (le_rootMultiplicity_iff hsubne).mp (by omega)
  have hderiv : (X - C (1 : ℝ)) ^ (m - 1) ∣
      derivative (1 - E.normalizedAlternant) :=
    pow_sub_one_dvd_derivative_of_pow_dvd hpow
  simpa using hderiv.neg_right

private theorem endpoint_rootMultiplicity_derivative
    (hm : 1 ≤ m) (hN : m ≤ N) :
    m - 1 ≤ rootMultiplicity 1 (derivative E.normalizedAlternant) := by
  rw [le_rootMultiplicity_iff (E.normalizedAlternant_derivative_ne_zero hm hN)]
  exact E.endpoint_power_dvd_derivative hm hN

private theorem certificate_orientation_value
    (i : Fin (N - m + 1)) :
    E.certificate.orientation * (-1 : ℝ) ^ (i : ℕ) = 1 ∨
      E.certificate.orientation * (-1 : ℝ) ^ (i : ℕ) = -1 := by
  rcases E.certificate.orientation_eq with horient | horient
  · rcases Nat.even_or_odd (i : ℕ) with hi | hi
    · left
      simp [horient, hi.neg_one_pow]
    · right
      simp [horient, hi.neg_one_pow]
  · rcases Nat.even_or_odd (i : ℕ) with hi | hi
    · right
      simp [horient, hi.neg_one_pow]
    · left
      simp [horient, hi.neg_one_pow]

private theorem derivative_eval_certificate_node
    (hm : 1 ≤ m) (hN : m ≤ N)
    (i : Fin (N - m + 1))
    (hleft : -1 < E.certificate.nodes i) :
    (derivative E.normalizedAlternant).eval (E.certificate.nodes i) = 0 := by
  let x := E.certificate.nodes i
  have hxIco := E.certificate.nodes_mem_Ico i
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hxIco.1, hxIco.2.le⟩
  have hxnhds : Set.Icc (-1 : ℝ) 1 ∈ nhds x :=
    Icc_mem_nhds hleft hxIco.2
  have hnode := E.normalizedAlternant_node_value hm hN i
  rcases E.certificate_orientation_value i with hplus | hminus
  · have hmax : IsMaxOn (fun y : ℝ ↦ E.normalizedAlternant.eval y)
        (Set.Icc (-1 : ℝ) 1) x := by
      intro y hy
      change E.normalizedAlternant.eval y ≤ E.normalizedAlternant.eval x
      dsimp only [x]
      rw [hnode, hplus]
      exact (E.normalizedAlternant_bounds hm hN y hy).2
    exact hmax.isLocalMax hxnhds |>.hasDerivAt_eq_zero
      (E.normalizedAlternant.hasDerivAt x)
  · have hmin : IsMinOn (fun y : ℝ ↦ E.normalizedAlternant.eval y)
        (Set.Icc (-1 : ℝ) 1) x := by
      intro y hy
      change E.normalizedAlternant.eval x ≤ E.normalizedAlternant.eval y
      dsimp only [x]
      rw [hnode, hminus]
      exact (E.normalizedAlternant_bounds hm hN y hy).1
    exact hmin.isLocalMin hxnhds |>.hasDerivAt_eq_zero
      (E.normalizedAlternant.hasDerivAt x)

private def certificateNodeFinset : Finset ℝ :=
  Finset.univ.image E.certificate.nodes

private theorem certificateNodeFinset_card :
    E.certificateNodeFinset.card = N - m + 1 := by
  rw [certificateNodeFinset, Finset.card_image_of_injective]
  · simp
  · exact E.certificate.strictMono_nodes.injective

private theorem one_not_mem_certificateNodeFinset :
    (1 : ℝ) ∉ E.certificateNodeFinset := by
  intro hone
  simp only [certificateNodeFinset, Finset.mem_image, Finset.mem_univ, true_and] at hone
  obtain ⟨i, hi⟩ := hone
  have hlt := (E.certificate.nodes_mem_Ico i).2
  linarith

private def allCriticalRootMultiset : Multiset ℝ :=
  E.certificateNodeFinset.1 + Multiset.replicate (m - 1) 1

private theorem allCriticalRootMultiset_card (hm : 1 ≤ m) (hN : m ≤ N) :
    E.allCriticalRootMultiset.card = N := by
  rw [allCriticalRootMultiset, Multiset.card_add, Multiset.card_replicate]
  change E.certificateNodeFinset.card + (m - 1) = N
  rw [E.certificateNodeFinset_card]
  omega

private theorem allCriticalRootMultiset_le_roots
    (hm : 1 ≤ m) (hN : m ≤ N)
    (hfirst : -1 < E.certificate.nodes 0) :
    E.allCriticalRootMultiset ≤ (derivative E.normalizedAlternant).roots := by
  apply Multiset.le_iff_count.mpr
  intro x
  rw [allCriticalRootMultiset, Multiset.count_add, count_roots]
  by_cases hx1 : x = 1
  · subst x
    have hnotmem : (1 : ℝ) ∉ E.certificateNodeFinset.1 := by
      simpa using E.one_not_mem_certificateNodeFinset
    rw [Multiset.count_eq_zero_of_notMem hnotmem,
      Multiset.count_replicate_self, zero_add]
    exact E.endpoint_rootMultiplicity_derivative hm hN
  · have hrep : (Multiset.replicate (m - 1) (1 : ℝ)).count x = 0 := by
      rw [Multiset.count_replicate]
      simp [Ne.symm hx1]
    rw [hrep, add_zero]
    by_cases hxmem : x ∈ E.certificateNodeFinset
    · have hxmem' : x ∈ E.certificateNodeFinset.1 := by simpa using hxmem
      have hcount : E.certificateNodeFinset.1.count x = 1 :=
        Multiset.count_eq_one_of_mem E.certificateNodeFinset.2 hxmem'
      rw [hcount]
      apply (rootMultiplicity_pos
        (E.normalizedAlternant_derivative_ne_zero hm hN)).mpr
      simp only [certificateNodeFinset, Finset.mem_image, Finset.mem_univ,
        true_and] at hxmem
      obtain ⟨i, rfl⟩ := hxmem
      have hnode0 : E.certificate.nodes 0 ≤ E.certificate.nodes i := by
        exact E.certificate.strictMono_nodes.monotone (Fin.zero_le i)
      exact E.derivative_eval_certificate_node hm hN i (hfirst.trans_le hnode0)
    · have hxmem' : x ∉ E.certificateNodeFinset.1 := by simpa using hxmem
      rw [Multiset.count_eq_zero_of_notMem hxmem']
      exact Nat.zero_le _

private theorem first_certificate_node_eq_neg_one
    (hm : 1 ≤ m) (hN : m ≤ N) :
    E.certificate.nodes 0 = -1 := by
  have hleft := (E.certificate.nodes_mem_Ico 0).1
  apply le_antisymm
  · apply le_of_not_gt
    intro hgt
    have hmult := E.allCriticalRootMultiset_le_roots hm hN hgt
    have hcard := Multiset.card_le_card hmult
    rw [E.allCriticalRootMultiset_card hm hN] at hcard
    have hroots := (derivative E.normalizedAlternant).card_roots'
    have hderivdeg := natDegree_derivative_le E.normalizedAlternant
    have hZdeg := E.normalizedAlternant_natDegree_le hN
    omega
  · exact hleft

/-- The certificate nodes strictly between the two distinguished endpoints. -/
def interiorCertificateNode (i : Fin (N - m)) : ℝ :=
  E.certificate.nodes i.succ

private theorem interiorCertificateNode_injective :
    Function.Injective E.interiorCertificateNode := by
  exact E.certificate.strictMono_nodes.injective.comp (Fin.succ_injective _)

private theorem interiorCertificateNode_mem_Ioo
    (hm : 1 ≤ m) (hN : m ≤ N) (i : Fin (N - m)) :
    E.interiorCertificateNode i ∈ Set.Ioo (-1 : ℝ) 1 := by
  constructor
  · rw [← E.first_certificate_node_eq_neg_one hm hN]
    exact E.certificate.strictMono_nodes (Fin.succ_pos i)
  · exact (E.certificate.nodes_mem_Ico i.succ).2

private theorem derivative_eval_interiorCertificateNode
    (hm : 1 ≤ m) (hN : m ≤ N) (i : Fin (N - m)) :
    (derivative E.normalizedAlternant).eval (E.interiorCertificateNode i) = 0 :=
  E.derivative_eval_certificate_node hm hN i.succ
    (E.interiorCertificateNode_mem_Ioo hm hN i).1

private def interiorCertificateNodeFinset : Finset ℝ :=
  Finset.univ.image E.interiorCertificateNode

private theorem interiorCertificateNodeFinset_card :
    E.interiorCertificateNodeFinset.card = N - m := by
  rw [interiorCertificateNodeFinset, Finset.card_image_of_injective]
  · simp
  · exact E.interiorCertificateNode_injective

private theorem one_not_mem_interiorCertificateNodeFinset :
    (1 : ℝ) ∉ E.interiorCertificateNodeFinset := by
  intro hone
  simp only [interiorCertificateNodeFinset, Finset.mem_image, Finset.mem_univ,
    true_and] at hone
  obtain ⟨i, hi⟩ := hone
  have hlt := (E.certificate.nodes_mem_Ico i.succ).2
  dsimp only [interiorCertificateNode] at hi
  linarith

private def endpointCriticalRootMultiset : Multiset ℝ :=
  E.interiorCertificateNodeFinset.1 + Multiset.replicate (m - 1) 1

private theorem endpointCriticalRootMultiset_card
    (hm : 1 ≤ m) (hN : m ≤ N) :
    E.endpointCriticalRootMultiset.card = N - 1 := by
  rw [endpointCriticalRootMultiset, Multiset.card_add, Multiset.card_replicate]
  change E.interiorCertificateNodeFinset.card + (m - 1) = N - 1
  rw [E.interiorCertificateNodeFinset_card]
  omega

private theorem endpointCriticalRootMultiset_le_roots
    (hm : 1 ≤ m) (hN : m ≤ N) :
    E.endpointCriticalRootMultiset ≤
      (derivative E.normalizedAlternant).roots := by
  apply Multiset.le_iff_count.mpr
  intro x
  rw [endpointCriticalRootMultiset, Multiset.count_add, count_roots]
  by_cases hx1 : x = 1
  · subst x
    have hnotmem : (1 : ℝ) ∉ E.interiorCertificateNodeFinset.1 := by
      simpa using E.one_not_mem_interiorCertificateNodeFinset
    rw [Multiset.count_eq_zero_of_notMem hnotmem,
      Multiset.count_replicate_self, zero_add]
    exact E.endpoint_rootMultiplicity_derivative hm hN
  · have hrep : (Multiset.replicate (m - 1) (1 : ℝ)).count x = 0 := by
      rw [Multiset.count_replicate]
      simp [Ne.symm hx1]
    rw [hrep, add_zero]
    by_cases hxmem : x ∈ E.interiorCertificateNodeFinset
    · have hxmem' : x ∈ E.interiorCertificateNodeFinset.1 := by simpa using hxmem
      have hcount : E.interiorCertificateNodeFinset.1.count x = 1 :=
        Multiset.count_eq_one_of_mem E.interiorCertificateNodeFinset.2 hxmem'
      rw [hcount]
      apply (rootMultiplicity_pos
        (E.normalizedAlternant_derivative_ne_zero hm hN)).mpr
      simp only [interiorCertificateNodeFinset, Finset.mem_image,
        Finset.mem_univ, true_and] at hxmem
      obtain ⟨i, rfl⟩ := hxmem
      exact E.derivative_eval_interiorCertificateNode hm hN i
    · have hxmem' : x ∉ E.interiorCertificateNodeFinset.1 := by simpa using hxmem
      rw [Multiset.count_eq_zero_of_notMem hxmem']
      exact Nat.zero_le _

/-- The endpoint contact and the interior alternation nodes exhaust the
degree of the derivative. -/
theorem normalizedAlternant_natDegree_eq
    (hm : 1 ≤ m) (hN : m ≤ N) :
    E.normalizedAlternant.natDegree = N := by
  have hmult := E.endpointCriticalRootMultiset_le_roots hm hN
  have hcard := Multiset.card_le_card hmult
  rw [E.endpointCriticalRootMultiset_card hm hN] at hcard
  have hroots := (derivative E.normalizedAlternant).card_roots'
  have hderivdeg := natDegree_derivative_le E.normalizedAlternant
  have hZdeg := E.normalizedAlternant_natDegree_le hN
  have hZpos : E.normalizedAlternant.natDegree ≠ 0 := by
    exact derivative_ne_zero.mp
      (E.normalizedAlternant_derivative_ne_zero hm hN)
  have hderivexact := natDegree_derivative E.normalizedAlternant
  omega

private theorem normalizedAlternant_derivative_natDegree_eq
    (hm : 1 ≤ m) (hN : m ≤ N) :
    (derivative E.normalizedAlternant).natDegree = N - 1 := by
  rw [natDegree_derivative, E.normalizedAlternant_natDegree_eq hm hN]

private theorem endpointCriticalRootMultiset_eq_roots
    (hm : 1 ≤ m) (hN : m ≤ N) :
    E.endpointCriticalRootMultiset =
      (derivative E.normalizedAlternant).roots := by
  apply Multiset.eq_of_le_of_card_le
    (E.endpointCriticalRootMultiset_le_roots hm hN)
  rw [E.endpointCriticalRootMultiset_card hm hN]
  exact (derivative E.normalizedAlternant).card_roots' |>.trans_eq
    (E.normalizedAlternant_derivative_natDegree_eq hm hN)

/-- Exact factorization of the derivative by the endpoint contact and all
interior alternation nodes.  This is the algebraic exhaustion statement used
by Pell--Abel extraction. -/
theorem normalizedAlternant_derivative_eq
    (hm : 1 ≤ m) (hN : m ≤ N) :
    derivative E.normalizedAlternant =
      C ((N : ℝ) * E.normalizedAlternant.leadingCoeff) *
        (X - C 1) ^ (m - 1) *
          ∏ i : Fin (N - m), (X - C (E.interiorCertificateNode i)) := by
  let F : ℝ[X] :=
    (X - C 1) ^ (m - 1) *
      ∏ i : Fin (N - m), (X - C (E.interiorCertificateNode i))
  have hFmonic : F.Monic := by
    dsimp only [F]
    exact ((monic_X_sub_C 1).pow (m - 1)).mul
      (monic_prod_of_monic Finset.univ _ fun i hi ↦
        monic_X_sub_C (E.interiorCertificateNode i))
  have hprod :
      (E.endpointCriticalRootMultiset.map fun a ↦ X - C a).prod = F := by
    rw [endpointCriticalRootMultiset, Multiset.map_add, Multiset.prod_add,
      Multiset.map_replicate, Multiset.prod_replicate]
    dsimp only [F]
    rw [mul_comm]
    congr 1
    change E.interiorCertificateNodeFinset.prod (fun a ↦ X - C a) =
      ∏ i : Fin (N - m), (X - C (E.interiorCertificateNode i))
    rw [interiorCertificateNodeFinset, Finset.prod_image]
    exact E.interiorCertificateNode_injective.injOn
  have hFdvd : F ∣ derivative E.normalizedAlternant := by
    rw [← hprod]
    exact (Multiset.prod_X_sub_C_dvd_iff_le_roots
      (E.normalizedAlternant_derivative_ne_zero hm hN)
      E.endpointCriticalRootMultiset).mpr
        (E.endpointCriticalRootMultiset_le_roots hm hN)
  have hFdeg : F.natDegree = N - 1 := by
    let G : ℝ[X] :=
      ∏ i : Fin (N - m), (X - C (E.interiorCertificateNode i))
    have hGmonic : G.Monic :=
      monic_prod_of_monic Finset.univ _ fun i hi ↦
        monic_X_sub_C (E.interiorCertificateNode i)
    change (((X - C 1) ^ (m - 1)) * G).natDegree = N - 1
    rw [((monic_X_sub_C (1 : ℝ)).pow (m - 1)).natDegree_mul'
      hGmonic.ne_zero, natDegree_pow, natDegree_X_sub_C]
    have hGdeg : G.natDegree = N - m := by
      dsimp only [G]
      simpa only [Finset.card_univ, Fintype.card_fin] using
        natDegree_finsetProd_X_sub_C_eq_card
          (R := ℝ) (Finset.univ : Finset (Fin (N - m)))
          E.interiorCertificateNode
    rw [hGdeg]
    omega
  have heq := eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
    hFmonic hFdvd (by rw [hFdeg, E.normalizedAlternant_derivative_natDegree_eq hm hN])
  rw [heq]
  dsimp only [F]
  rw [leadingCoeff_derivative, E.normalizedAlternant_natDegree_eq hm hN]
  rw [mul_comm E.normalizedAlternant.leadingCoeff (N : ℝ)]
  ring

private theorem last_certificate_node_value
    (hm : 1 ≤ m) (hN : m ≤ N) :
    E.normalizedAlternant.eval
        (E.certificate.nodes (Fin.last (N - m))) = -1 := by
  let k : Fin (N - m + 1) := Fin.last (N - m)
  have hnode := E.normalizedAlternant_node_value hm hN k
  rcases E.certificate_orientation_value k with hplus | hminus
  · exfalso
    have hlastlt : E.certificate.nodes k < 1 :=
      (E.certificate.nodes_mem_Ico k).2
    have hequal :
        E.normalizedAlternant.eval (E.certificate.nodes k) =
          E.normalizedAlternant.eval 1 := by
      rw [hnode, hplus, E.normalizedAlternant_eval_one hm]
    obtain ⟨c, hc, hcderiv⟩ := exists_deriv_eq_zero hlastlt
      E.normalizedAlternant.continuousOn hequal
    rw [E.normalizedAlternant.deriv] at hcderiv
    have hcroot : c ∈ (derivative E.normalizedAlternant).roots :=
      (mem_roots (E.normalizedAlternant_derivative_ne_zero hm hN)).mpr hcderiv
    rw [← E.endpointCriticalRootMultiset_eq_roots hm hN,
      endpointCriticalRootMultiset, Multiset.mem_add] at hcroot
    rcases hcroot with hcint | hcone
    · have hcint' : c ∈ E.interiorCertificateNodeFinset := by simpa using hcint
      simp only [interiorCertificateNodeFinset, Finset.mem_image,
        Finset.mem_univ, true_and] at hcint'
      obtain ⟨i, rfl⟩ := hcint'
      have hindex : i.succ ≤ k := Fin.le_last i.succ
      have hnodele : E.certificate.nodes i.succ ≤ E.certificate.nodes k :=
        E.certificate.strictMono_nodes.monotone hindex
      exact (not_lt_of_ge hnodele) hc.1
    · have hc_one : c = 1 := Multiset.eq_of_mem_replicate hcone
      exact (ne_of_lt hc.2) hc_one
  · exact hnode.trans hminus

private def endpointNodes : Fin (N - m + 2) → ℝ :=
  Fin.lastCases 1 E.certificate.nodes

private theorem endpointNodes_strictMono
    (_hm : 1 ≤ m) (_hN : m ≤ N) :
    StrictMono E.endpointNodes := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [endpointNodes, Fin.lastCases_castSucc]
    rw [Fin.succ_last, Fin.lastCases_last]
    exact (E.certificate.nodes_mem_Ico (Fin.last (N - m))).2
  · rw [Fin.succ_castSucc]
    simp only [endpointNodes, Fin.lastCases_castSucc]
    exact E.certificate.strictMono_nodes Fin.castSucc_lt_succ

private theorem endpointNodes_zero
    (hm : 1 ≤ m) (hN : m ≤ N) :
    E.endpointNodes 0 = -1 := by
  rw [show (0 : Fin (N - m + 2)) =
      Fin.castSucc (0 : Fin (N - m + 1)) by rfl]
  simp only [endpointNodes, Fin.lastCases_castSucc]
  exact E.first_certificate_node_eq_neg_one hm hN

private theorem endpointNodes_last :
    E.endpointNodes (Fin.last (N - m + 1)) = 1 := by
  simp [endpointNodes]

private theorem endpointNodes_value
    (hm : 1 ≤ m) (hN : m ≤ N) (j : Fin (N - m + 2)) :
    E.normalizedAlternant.eval (E.endpointNodes j) =
      E.certificate.orientation * (-1 : ℝ) ^ (j : ℕ) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · rw [E.endpointNodes_last, E.normalizedAlternant_eval_one hm]
    symm
    have hlastNode := E.normalizedAlternant_node_value hm hN (Fin.last (N - m))
    have hlastValue := E.last_certificate_node_value hm hN
    have hsign : E.certificate.orientation * (-1 : ℝ) ^ (N - m) = -1 := by
      have hindex : ((Fin.last (N - m) : Fin (N - m + 1)) : ℕ) = N - m := rfl
      rw [hindex] at hlastNode
      linarith
    calc
      E.certificate.orientation * (-1 : ℝ) ^
          ((Fin.last (N - m + 1) : Fin (N - m + 2)) : ℕ) =
          E.certificate.orientation * (-1 : ℝ) ^ (N - m + 1) := by rfl
      _ = -(E.certificate.orientation * (-1 : ℝ) ^ (N - m)) := by
        rw [pow_succ]
        ring
      _ = 1 := by rw [hsign]; norm_num
  · simp only [endpointNodes, Fin.lastCases_castSucc, Fin.val_castSucc]
    exact E.normalizedAlternant_node_value hm hN i

/-- The normalized generic extremal polynomial, with both endpoints included
in its alternating node family. -/
def endpointAlternant
    (hm : 1 ≤ m) (hN : m ≤ N) :
    EndpointAlternant m N E.normalizedAlternant where
  one_le_m := hm
  m_le_N := hN
  natDegree_eq := E.normalizedAlternant_natDegree_eq hm hN
  bounds := E.normalizedAlternant_bounds hm hN
  eval_one := E.normalizedAlternant_eval_one hm
  contact_one := E.normalizedAlternant_contact_one hm hN
  orientation := E.certificate.orientation
  orientation_eq := E.certificate.orientation_eq
  nodes := E.endpointNodes
  strictMono_nodes := E.endpointNodes_strictMono hm hN
  node_zero := E.endpointNodes_zero hm hN
  node_last := E.endpointNodes_last
  node_value := E.endpointNodes_value hm hN

end EvenWeightedExtremalData

end JoseSmoothest
