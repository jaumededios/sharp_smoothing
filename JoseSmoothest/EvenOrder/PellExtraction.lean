import JoseSmoothest.EvenOrder.EndpointContact
import JoseSmoothest.EvenOrder.EndpointAlternation

/-!
# Pell--Abel extraction from an endpoint alternant

This file performs the algebraic normalization which turns an endpoint
alternant into a polynomial Pell--Abel equation.  The square factor removes
half of the distinguished endpoint contact and the double factors at the
interior alternation nodes.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

namespace EndpointAlternant

variable {m N : ℕ} {Z : ℝ[X]} (a : EndpointAlternant m N Z)

/-- The interior alternation nodes, excluding the two endpoints. -/
def interiorNode (i : Fin (N - m)) : ℝ :=
  a.nodes ⟨i + 1, by omega⟩

theorem interiorNode_mem_Ioo (i : Fin (N - m)) :
    a.interiorNode i ∈ Set.Ioo (-1 : ℝ) 1 := by
  constructor
  · rw [← a.node_zero]
    apply a.strictMono_nodes
    change (0 : ℕ) < (i : ℕ) + 1
    omega
  · rw [← a.node_last]
    apply a.strictMono_nodes
    change (i : ℕ) + 1 < N - m + 1
    omega

theorem interiorNode_injective : Function.Injective a.interiorNode := by
  intro i j hij
  have hindex := a.strictMono_nodes.injective hij
  apply Fin.ext
  have hvalue := Fin.ext_iff.mp hindex
  dsimp only [interiorNode] at hvalue
  omega

/-- The monic factor whose square removes all forced even multiplicities. -/
def squareFactor : ℝ[X] :=
  (X - C 1) ^ (m / 2) *
    ∏ i : Fin (N - m), (X - C (a.interiorNode i))

theorem squareFactor_monic : a.squareFactor.Monic := by
  exact ((monic_X_sub_C (1 : ℝ)).pow (m / 2)).mul
    (monic_prod_of_monic Finset.univ _ fun i _ ↦
      monic_X_sub_C (a.interiorNode i))

theorem squareFactor_ne_zero : a.squareFactor ≠ 0 :=
  a.squareFactor_monic.ne_zero

theorem natDegree_squareFactor :
    a.squareFactor.natDegree = m / 2 + (N - m) := by
  have hprodmonic :
      (∏ i : Fin (N - m), (X - C (a.interiorNode i))).Monic :=
    monic_prod_of_monic Finset.univ _ fun i _ ↦
      monic_X_sub_C (a.interiorNode i)
  rw [squareFactor, ((monic_X_sub_C (1 : ℝ)).pow (m / 2)).natDegree_mul'
    hprodmonic.ne_zero,
    natDegree_pow, natDegree_X_sub_C]
  have hprod :
      (∏ i : Fin (N - m), (X - C (a.interiorNode i))).natDegree = N - m := by
    rw [natDegree_finsetProd_X_sub_C_eq_card]
    simp
  rw [hprod]
  omega

/-- The common leading scale of the Pell numerator and denominator. -/
def leadingScale (_a : EndpointAlternant m N Z) : ℝ := Z.leadingCoeff

theorem leadingScale_ne_zero : a.leadingScale ≠ 0 := by
  rw [leadingScale]
  apply leadingCoeff_ne_zero.mpr
  intro hZ
  have hdeg : Z.natDegree = 0 := by simp [hZ]
  rw [a.natDegree_eq] at hdeg
  have := a.one_le_m.trans a.m_le_N
  omega

/-- The Pell denominator before extracting the residual squarefree weight. -/
def Q : ℝ[X] :=
  C a.leadingScale * a.squareFactor

theorem Q_ne_zero : a.Q ≠ 0 :=
  mul_ne_zero (C_ne_zero.mpr a.leadingScale_ne_zero) a.squareFactor_ne_zero

theorem natDegree_Q :
    a.Q.natDegree = N - endpointGenus m - 1 := by
  rw [Q, natDegree_mul (C_ne_zero.mpr a.leadingScale_ne_zero)
    a.squareFactor_ne_zero, natDegree_C, zero_add, a.natDegree_squareFactor]
  simp only [endpointGenus]
  have := a.one_le_m
  have := a.m_le_N
  omega

theorem leadingCoeff_Q : a.Q.leadingCoeff = Z.leadingCoeff := by
  rw [Q, leadingCoeff_mul, leadingCoeff_C, a.squareFactor_monic.leadingCoeff,
    mul_one]
  rfl

private theorem derivative_Z_ne_zero (a : EndpointAlternant m N Z) : derivative Z ≠ 0 := by
  rw [Polynomial.derivative_ne_zero, a.natDegree_eq]
  exact Nat.ne_zero_of_lt (a.one_le_m.trans a.m_le_N)

private theorem interiorNode_value (i : Fin (N - m)) :
    Z.eval (a.interiorNode i) = 1 ∨ Z.eval (a.interiorNode i) = -1 := by
  have hvalue := a.node_value ⟨i + 1, by omega⟩
  rcases a.orientation_eq with horient | horient
  · rcases Nat.even_or_odd (i + 1) with hi | hi
    · left
      simpa [interiorNode, horient, hi.neg_one_pow] using hvalue
    · right
      simpa [interiorNode, horient, hi.neg_one_pow] using hvalue
  · rcases Nat.even_or_odd (i + 1) with hi | hi
    · right
      simpa [interiorNode, horient, hi.neg_one_pow] using hvalue
    · left
      simpa [interiorNode, horient, hi.neg_one_pow] using hvalue

private theorem derivative_eval_interiorNode (i : Fin (N - m)) :
    (derivative Z).eval (a.interiorNode i) = 0 := by
  have hx := a.interiorNode_mem_Ioo i
  have hxIcc : a.interiorNode i ∈ Set.Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hxnhds : Set.Icc (-1 : ℝ) 1 ∈ nhds (a.interiorNode i) :=
    Icc_mem_nhds hx.1 hx.2
  rcases a.interiorNode_value i with hplus | hminus
  · have hmax : IsMaxOn (fun y : ℝ ↦ Z.eval y)
        (Set.Icc (-1 : ℝ) 1) (a.interiorNode i) := by
      intro y hy
      change Z.eval y ≤ Z.eval (a.interiorNode i)
      rw [hplus]
      exact (a.bounds y hy).2
    exact hmax.isLocalMax hxnhds |>.hasDerivAt_eq_zero (Z.hasDerivAt _)
  · have hmin : IsMinOn (fun y : ℝ ↦ Z.eval y)
        (Set.Icc (-1 : ℝ) 1) (a.interiorNode i) := by
      intro y hy
      change Z.eval (a.interiorNode i) ≤ Z.eval y
      rw [hminus]
      exact (a.bounds y hy).1
    exact hmin.isLocalMin hxnhds |>.hasDerivAt_eq_zero (Z.hasDerivAt _)

private theorem endpoint_power_dvd_derivative (a : EndpointAlternant m N Z) :
    (X - C (1 : ℝ)) ^ (m - 1) ∣ derivative Z := by
  have hsub : 1 - Z ≠ 0 := by
    intro hzero
    have hcontact := a.contact_one
    rw [hzero, rootMultiplicity_zero] at hcontact
    have := a.one_le_m
    omega
  have hpow : (X - C (1 : ℝ)) ^ m ∣ 1 - Z := by
    rw [← a.contact_one]
    exact pow_rootMultiplicity_dvd _ _
  have hderiv := pow_sub_one_dvd_derivative_of_pow_dvd hpow
  simpa using hderiv.neg_right

private def criticalRootFinset : Finset ℝ :=
  Finset.univ.image a.interiorNode

private theorem criticalRootFinset_card :
    a.criticalRootFinset.card = N - m := by
  rw [criticalRootFinset, Finset.card_image_of_injective]
  · simp
  · exact a.interiorNode_injective

private theorem one_not_mem_criticalRootFinset :
    (1 : ℝ) ∉ a.criticalRootFinset := by
  intro hone
  simp only [criticalRootFinset, Finset.mem_image, Finset.mem_univ,
    true_and] at hone
  obtain ⟨i, hi⟩ := hone
  exact (ne_of_lt (a.interiorNode_mem_Ioo i).2) hi

private def criticalRootMultiset : Multiset ℝ :=
  a.criticalRootFinset.1 + Multiset.replicate (m - 1) 1

private theorem criticalRootMultiset_card :
    a.criticalRootMultiset.card = N - 1 := by
  rw [criticalRootMultiset, Multiset.card_add, Multiset.card_replicate]
  change a.criticalRootFinset.card + (m - 1) = N - 1
  rw [a.criticalRootFinset_card]
  have := a.m_le_N
  have := a.one_le_m
  omega

private theorem criticalRootMultiset_le_roots :
    a.criticalRootMultiset ≤ (derivative Z).roots := by
  apply Multiset.le_iff_count.mpr
  intro x
  rw [criticalRootMultiset, Multiset.count_add, count_roots]
  by_cases hx1 : x = 1
  · subst x
    have hnotmem : (1 : ℝ) ∉ a.criticalRootFinset.1 := by
      simpa using a.one_not_mem_criticalRootFinset
    rw [Multiset.count_eq_zero_of_notMem hnotmem,
      Multiset.count_replicate_self, zero_add, le_rootMultiplicity_iff a.derivative_Z_ne_zero]
    exact a.endpoint_power_dvd_derivative
  · have hrep : (Multiset.replicate (m - 1) (1 : ℝ)).count x = 0 := by
      rw [Multiset.count_replicate]
      simp [Ne.symm hx1]
    rw [hrep, add_zero]
    by_cases hxmem : x ∈ a.criticalRootFinset
    · have hxmem' : x ∈ a.criticalRootFinset.1 := by simpa using hxmem
      rw [Multiset.count_eq_one_of_mem a.criticalRootFinset.2 hxmem']
      apply (rootMultiplicity_pos a.derivative_Z_ne_zero).mpr
      simp only [criticalRootFinset, Finset.mem_image, Finset.mem_univ,
        true_and] at hxmem
      obtain ⟨i, rfl⟩ := hxmem
      exact a.derivative_eval_interiorNode i
    · have hxmem' : x ∉ a.criticalRootFinset.1 := by simpa using hxmem
      rw [Multiset.count_eq_zero_of_notMem hxmem']
      exact Nat.zero_le _

private theorem criticalRootMultiset_eq_roots :
    a.criticalRootMultiset = (derivative Z).roots := by
  apply Multiset.eq_of_le_of_card_le a.criticalRootMultiset_le_roots
  rw [a.criticalRootMultiset_card]
  exact (derivative Z).card_roots' |>.trans_eq (by
    rw [natDegree_derivative, a.natDegree_eq])

/-- Exact factorization of the derivative by endpoint contact and the
interior alternation nodes. -/
theorem derivative_eq :
    derivative Z =
      C ((N : ℝ) * Z.leadingCoeff) *
        (X - C 1) ^ (m - 1) *
          ∏ i : Fin (N - m), (X - C (a.interiorNode i)) := by
  let F : ℝ[X] :=
    (X - C 1) ^ (m - 1) *
      ∏ i : Fin (N - m), (X - C (a.interiorNode i))
  have hFmonic : F.Monic := by
    dsimp only [F]
    exact ((monic_X_sub_C 1).pow (m - 1)).mul
      (monic_prod_of_monic Finset.univ _ fun i _ ↦ monic_X_sub_C _)
  have hprod :
      (a.criticalRootMultiset.map fun x ↦ X - C x).prod = F := by
    rw [criticalRootMultiset, Multiset.map_add, Multiset.prod_add,
      Multiset.map_replicate, Multiset.prod_replicate]
    dsimp only [F]
    rw [mul_comm]
    congr 1
    change a.criticalRootFinset.prod (fun x ↦ X - C x) =
      ∏ i : Fin (N - m), (X - C (a.interiorNode i))
    rw [criticalRootFinset, Finset.prod_image]
    exact a.interiorNode_injective.injOn
  have hFdvd : F ∣ derivative Z := by
    rw [← hprod]
    exact (Multiset.prod_X_sub_C_dvd_iff_le_roots a.derivative_Z_ne_zero
      a.criticalRootMultiset).mpr a.criticalRootMultiset_le_roots
  have hFdeg : F.natDegree = N - 1 := by
    let G : ℝ[X] := ∏ i : Fin (N - m), (X - C (a.interiorNode i))
    have hGmonic : G.Monic :=
      monic_prod_of_monic Finset.univ _ fun i _ ↦ monic_X_sub_C _
    change (((X - C 1) ^ (m - 1)) * G).natDegree = N - 1
    rw [((monic_X_sub_C (1 : ℝ)).pow (m - 1)).natDegree_mul'
      hGmonic.ne_zero, natDegree_pow, natDegree_X_sub_C]
    have hGdeg : G.natDegree = N - m := by
      dsimp only [G]
      rw [natDegree_finsetProd_X_sub_C_eq_card]
      simp
    rw [hGdeg]
    have := a.m_le_N
    have := a.one_le_m
    omega
  have heq := eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
    hFmonic hFdvd (by rw [hFdeg, natDegree_derivative, a.natDegree_eq])
  rw [heq]
  dsimp only [F]
  rw [leadingCoeff_derivative, a.natDegree_eq]
  rw [mul_comm Z.leadingCoeff (N : ℝ)]
  ring

/-- The derivative factorization in the normalization used by the endpoint
contact package. -/
theorem derivative_Z_eq :
    derivative Z =
      C (N : ℝ) * (X - C 1) ^ endpointGenus m * a.Q := by
  rw [a.derivative_eq, Q, squareFactor]
  have hexponent : endpointGenus m + m / 2 = m - 1 := by
    simp only [endpointGenus]
    have := a.one_le_m
    omega
  rw [← hexponent, pow_add]
  simp only [leadingScale, map_mul, C_1]
  ring

private theorem pellNumerator_ne_zero (a : EndpointAlternant m N Z) : Z ^ 2 - 1 ≠ 0 := by
  intro hzero
  have hsquare : Z ^ 2 = 1 := sub_eq_zero.mp hzero
  have hdegree := congrArg natDegree hsquare
  simp only [natDegree_pow, natDegree_one, a.natDegree_eq] at hdegree
  have := (a.one_le_m).trans a.m_le_N
  omega

private def forcedSquareRoots : Multiset ℝ :=
  Multiset.replicate (2 * (m / 2)) 1 +
    a.criticalRootFinset.1 + a.criticalRootFinset.1

private theorem forcedSquareRoots_le_roots :
    a.forcedSquareRoots ≤ (Z ^ 2 - 1).roots := by
  apply Multiset.le_iff_count.mpr
  intro x
  rw [forcedSquareRoots, Multiset.count_add, Multiset.count_add, count_roots]
  by_cases hx1 : x = 1
  · subst x
    have hnotmem : (1 : ℝ) ∉ a.criticalRootFinset.1 := by
      simpa using a.one_not_mem_criticalRootFinset
    rw [Multiset.count_replicate_self,
      Multiset.count_eq_zero_of_notMem hnotmem, add_zero, add_zero,
      le_rootMultiplicity_iff a.pellNumerator_ne_zero]
    have hcontact : (X - C (1 : ℝ)) ^ m ∣ 1 - Z := by
      rw [← a.contact_one]
      exact pow_rootMultiplicity_dvd _ _
    have hsub : 1 - Z ∣ Z ^ 2 - 1 := by
      refine ⟨-(Z + 1), ?_⟩
      ring
    exact (pow_dvd_pow (X - C (1 : ℝ)) (by omega : 2 * (m / 2) ≤ m)).trans
      (hcontact.trans hsub)
  · have hrep : (Multiset.replicate (2 * (m / 2)) (1 : ℝ)).count x = 0 := by
      rw [Multiset.count_replicate]
      simp [Ne.symm hx1]
    rw [hrep, zero_add]
    by_cases hxmem : x ∈ a.criticalRootFinset
    · have hxmem' : x ∈ a.criticalRootFinset.1 := by simpa using hxmem
      rw [Multiset.count_eq_one_of_mem a.criticalRootFinset.2 hxmem']
      norm_num only [Nat.reduceAdd]
      rw [show 2 ≤ rootMultiplicity x (Z ^ 2 - 1) ↔
          1 < rootMultiplicity x (Z ^ 2 - 1) by omega]
      rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot a.pellNumerator_ne_zero]
      simp only [criticalRootFinset, Finset.mem_image, Finset.mem_univ,
        true_and] at hxmem
      obtain ⟨i, rfl⟩ := hxmem
      constructor
      · simp only [IsRoot, eval_sub, eval_pow]
        rcases a.interiorNode_value i with hplus | hminus
        · rw [hplus]
          norm_num
        · rw [hminus]
          norm_num
      · simp [IsRoot, derivative_pow, a.derivative_eval_interiorNode i]
    · have hxmem' : x ∉ a.criticalRootFinset.1 := by simpa using hxmem
      simp only [Multiset.count_eq_zero_of_notMem hxmem', zero_add]
      exact Nat.zero_le _

private theorem forcedSquareRoots_prod :
    (a.forcedSquareRoots.map fun x ↦ X - C x).prod = a.squareFactor ^ 2 := by
  rw [forcedSquareRoots, Multiset.map_add, Multiset.map_add,
    Multiset.prod_add, Multiset.prod_add, Multiset.map_replicate,
    Multiset.prod_replicate]
  change (X - C 1) ^ (2 * (m / 2)) *
      a.criticalRootFinset.prod (fun x ↦ X - C x) *
        a.criticalRootFinset.prod (fun x ↦ X - C x) = a.squareFactor ^ 2
  have hprod : a.criticalRootFinset.prod (fun x ↦ X - C x) =
      ∏ i : Fin (N - m), (X - C (a.interiorNode i)) := by
    rw [criticalRootFinset, Finset.prod_image]
    exact a.interiorNode_injective.injOn
  rw [hprod, squareFactor]
  have hpow : (X - C (1 : ℝ)) ^ (2 * (m / 2)) =
      ((X - C 1) ^ (m / 2)) ^ 2 := by
    rw [show 2 * (m / 2) = (m / 2) * 2 by omega, ← pow_mul]
  rw [hpow]
  ring

theorem squareFactor_sq_dvd : a.squareFactor ^ 2 ∣ Z ^ 2 - 1 := by
  rw [← a.forcedSquareRoots_prod]
  exact (Multiset.prod_X_sub_C_dvd_iff_le_roots a.pellNumerator_ne_zero
    a.forcedSquareRoots).mpr a.forcedSquareRoots_le_roots

/-- The residual Pell weight after monic division by the forced square. -/
def D : ℝ[X] :=
  C ((a.leadingScale ^ 2)⁻¹) *
    ((Z ^ 2 - 1) /ₘ (a.squareFactor ^ 2))

private theorem squareFactor_sq_mul_div :
    a.squareFactor ^ 2 * ((Z ^ 2 - 1) /ₘ (a.squareFactor ^ 2)) = Z ^ 2 - 1 := by
  have hmod : (Z ^ 2 - 1) %ₘ (a.squareFactor ^ 2) = 0 :=
    (modByMonic_eq_zero_iff_dvd (a.squareFactor_monic.pow 2)).2
      a.squareFactor_sq_dvd
  have hdivision := modByMonic_add_div (Z ^ 2 - 1) (a.squareFactor ^ 2)
  rw [hmod, zero_add] at hdivision
  exact hdivision

theorem pell_factorization : Z ^ 2 - 1 = a.D * a.Q ^ 2 := by
  have hscalar :
      C ((a.leadingScale ^ 2)⁻¹) * C a.leadingScale ^ 2 = (1 : ℝ[X]) := by
    rw [← map_pow]
    rw [← map_mul]
    simp [a.leadingScale_ne_zero]
  rw [D, Q]
  calc
    Z ^ 2 - 1 = a.squareFactor ^ 2 *
        ((Z ^ 2 - 1) /ₘ (a.squareFactor ^ 2)) := a.squareFactor_sq_mul_div.symm
    _ = (C ((a.leadingScale ^ 2)⁻¹) *
          ((Z ^ 2 - 1) /ₘ (a.squareFactor ^ 2))) *
        (C a.leadingScale * a.squareFactor) ^ 2 := by
      rw [show (C ((a.leadingScale ^ 2)⁻¹) *
          ((Z ^ 2 - 1) /ₘ (a.squareFactor ^ 2))) *
        (C a.leadingScale * a.squareFactor) ^ 2 =
          (C ((a.leadingScale ^ 2)⁻¹) * C a.leadingScale ^ 2) *
            (a.squareFactor ^ 2 *
              ((Z ^ 2 - 1) /ₘ (a.squareFactor ^ 2))) by ring]
      rw [hscalar, one_mul]

private theorem natDegree_pellNumerator (a : EndpointAlternant m N Z) :
    (Z ^ 2 - 1).natDegree = 2 * N := by
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · rw [natDegree_pow, a.natDegree_eq]
  · simp only [natDegree_one, natDegree_pow, a.natDegree_eq]
    have := (a.one_le_m).trans a.m_le_N
    omega

private theorem leadingCoeff_pellNumerator :
    (Z ^ 2 - 1).leadingCoeff = a.leadingScale ^ 2 := by
  rw [leadingCoeff_sub_of_degree_lt]
  · rw [leadingCoeff_pow, leadingScale]
  · apply degree_lt_degree
    simp only [natDegree_one, natDegree_pow, a.natDegree_eq]
    have := (a.one_le_m).trans a.m_le_N
    omega

private theorem leadingCoeff_squareQuotient :
    ((Z ^ 2 - 1) /ₘ (a.squareFactor ^ 2)).leadingCoeff = a.leadingScale ^ 2 := by
  have hlead := congrArg leadingCoeff a.squareFactor_sq_mul_div
  rw [leadingCoeff_monic_mul (a.squareFactor_monic.pow 2),
    a.leadingCoeff_pellNumerator] at hlead
  exact hlead

theorem monic_D : a.D.Monic := by
  rw [Monic.def, D, leadingCoeff_mul, leadingCoeff_C,
    a.leadingCoeff_squareQuotient]
  exact inv_mul_cancel₀ (pow_ne_zero 2 a.leadingScale_ne_zero)

theorem natDegree_D :
    a.D.natDegree = 2 * endpointGenus m + 2 := by
  rw [D, natDegree_mul (C_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2
    a.leadingScale_ne_zero))) (by
      intro hzero
      have hlead := a.leadingCoeff_squareQuotient
      rw [hzero, leadingCoeff_zero] at hlead
      exact (pow_ne_zero 2 a.leadingScale_ne_zero) hlead.symm),
    natDegree_C, zero_add, natDegree_divByMonic _ (a.squareFactor_monic.pow 2),
    a.natDegree_pellNumerator, natDegree_pow, a.natDegree_squareFactor]
  simp only [endpointGenus]
  have := a.one_le_m
  have := a.m_le_N
  omega

private theorem Z_sub_one_ne_zero (a : EndpointAlternant m N Z) : Z - 1 ≠ 0 := by
  intro hzero
  have hZ : Z = 1 := sub_eq_zero.mp hzero
  have hdegree := congrArg natDegree hZ
  rw [a.natDegree_eq, natDegree_one] at hdegree
  have := a.one_le_m.trans a.m_le_N
  omega

private theorem Z_add_one_ne_zero (a : EndpointAlternant m N Z) : Z + 1 ≠ 0 := by
  intro hzero
  have heval := congrArg (eval (1 : ℝ)) hzero
  simp only [eval_add, a.eval_one, eval_zero] at heval
  norm_num at heval

private theorem rootMultiplicity_pellNumerator_one (a : EndpointAlternant m N Z) :
    rootMultiplicity 1 (Z ^ 2 - 1) = m := by
  have hfactor : Z ^ 2 - 1 = (Z - 1) * (Z + 1) := by ring
  rw [hfactor, rootMultiplicity_mul
    (mul_ne_zero a.Z_sub_one_ne_zero a.Z_add_one_ne_zero)]
  have hplus : rootMultiplicity 1 (Z + 1) = 0 := by
    apply rootMultiplicity_eq_zero
    simp [IsRoot, a.eval_one]
  have hminus : rootMultiplicity 1 (Z - 1) = rootMultiplicity 1 (1 - Z) := by
    have hneg : Z - 1 = C (-1 : ℝ) * (1 - Z) := by
      norm_num
    rw [hneg, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (by norm_num))
      (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp a.Z_sub_one_ne_zero)))),
      rootMultiplicity_C]
    simp
  rw [hplus, add_zero, hminus, a.contact_one]

private theorem interiorProduct_eval_one_ne_zero :
    (∏ i : Fin (N - m), (X - C (a.interiorNode i))).eval 1 ≠ 0 := by
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact sub_ne_zero.mpr (ne_of_gt (a.interiorNode_mem_Ioo i).2)

theorem rootMultiplicity_Q_one : rootMultiplicity 1 a.Q = m / 2 := by
  let G : ℝ[X] := ∏ i : Fin (N - m), (X - C (a.interiorNode i))
  have hGmonic : G.Monic :=
    monic_prod_of_monic Finset.univ _ fun i _ ↦ monic_X_sub_C _
  have hGroot : rootMultiplicity 1 G = 0 := by
    apply rootMultiplicity_eq_zero
    simpa only [IsRoot] using a.interiorProduct_eval_one_ne_zero
  rw [Q, squareFactor,
    rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr a.leadingScale_ne_zero)
      (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero 1)) hGmonic.ne_zero)),
    rootMultiplicity_C,
    rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero 1))
      hGmonic.ne_zero), rootMultiplicity_X_sub_C_pow, hGroot]
  simp

/-- Every square factor of `P² - 1` divides `P'`.  This UFD lemma sees
irreducible quadratic factors as well as real linear factors. -/
theorem dvd_derivative_of_sq_dvd_sub_one
    {P F : ℝ[X]} (hdiv : F ^ 2 ∣ P ^ 2 - 1) : F ∣ derivative P := by
  obtain ⟨K, hK⟩ := hdiv
  have hcoprime : IsCoprime F P := by
    refine ⟨-(F * K), P, ?_⟩
    calc
      -(F * K) * F + P * P = P ^ 2 - F ^ 2 * K := by ring
      _ = 1 := by rw [← hK]; ring
  have hderivative : F ∣ derivative (P ^ 2 - 1) := by
    rw [hK]
    refine ⟨C (2 : ℝ) * derivative F * K + F * derivative K, ?_⟩
    simp only [derivative_pow, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      derivative_mul]
    ring
  have hshape : derivative (P ^ 2 - 1) = C (2 : ℝ) * P * derivative P := by
    simp [derivative_pow]
  rw [hshape] at hderivative
  have htwo : IsUnit (C (2 : ℝ) : ℝ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
  have hcoprime' : IsCoprime F (C (2 : ℝ) * P) :=
    (isCoprime_mul_unit_left_right htwo F P).mpr hcoprime
  exact hcoprime'.dvd_of_dvd_mul_left hderivative

theorem squarefree_D : Squarefree a.D := by
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero a.monic_D.ne_zero]
  intro p hp hpsquare
  have hpsquare' := hpsquare
  obtain ⟨R, hR⟩ := hpsquare
  have hpQsquare : (p * a.Q) ^ 2 ∣ Z ^ 2 - 1 := by
    refine ⟨R, ?_⟩
    rw [a.pell_factorization, hR]
    ring
  have hpQderivative : p * a.Q ∣ derivative Z :=
    dvd_derivative_of_sq_dvd_sub_one hpQsquare
  obtain ⟨K, hK⟩ := hpQderivative
  have hcancel : C (N : ℝ) * (X - C 1) ^ endpointGenus m = p * K := by
    apply mul_right_cancel₀ a.Q_ne_zero
    calc
      (C (N : ℝ) * (X - C 1) ^ endpointGenus m) * a.Q = derivative Z :=
        a.derivative_Z_eq.symm
      _ = (p * a.Q) * K := hK
      _ = (p * K) * a.Q := by ring
  have hpdvd : p ∣ C (N : ℝ) * (X - C 1) ^ endpointGenus m :=
    ⟨K, hcancel⟩
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_zero_of_lt (a.one_le_m.trans a.m_le_N)
  have hCunit : IsUnit (C (N : ℝ) : ℝ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hN)
  have hppow : p ∣ (X - C 1) ^ endpointGenus m := by
    rcases hp.prime.dvd_mul.mp hpdvd with hpC | hpow
    · exfalso
      apply hp.not_isUnit
      rw [isUnit_iff_dvd_one]
      exact hpC.trans hCunit.dvd
    · exact hpow
  have hplinear : p ∣ X - C (1 : ℝ) :=
    hp.prime.dvd_of_dvd_pow hppow
  have hassociated : Associated p (X - C (1 : ℝ)) :=
    hp.associated_of_dvd (irreducible_X_sub_C 1) hplinear
  have hsquareAssociated : Associated (p * p)
      ((X - C (1 : ℝ)) * (X - C 1)) :=
    (hassociated.mul_right p).trans (hassociated.mul_left (X - C (1 : ℝ)))
  have hlinearSquare : (X - C (1 : ℝ)) ^ 2 ∣ a.D := by
    rw [pow_two]
    exact hsquareAssociated.dvd_iff_dvd_left.mp hpsquare'
  have hDmult : 2 ≤ rootMultiplicity 1 a.D := by
    rw [le_rootMultiplicity_iff a.monic_D.ne_zero]
    exact hlinearSquare
  have hvaluation := congrArg (rootMultiplicity (1 : ℝ)) a.pell_factorization
  rw [a.rootMultiplicity_pellNumerator_one,
    rootMultiplicity_mul (mul_ne_zero a.monic_D.ne_zero (pow_ne_zero 2 a.Q_ne_zero)),
    pow_two, rootMultiplicity_mul (mul_ne_zero a.Q_ne_zero a.Q_ne_zero),
    a.rootMultiplicity_Q_one] at hvaluation
  omega

/-- The retained alternant and the extracted denominator solve the
Pell--Abel equation for the residual weight. -/
def solution : Polynomial.PellAbelSolution a.D where
  P := Z
  Q := a.Q
  equation := by
    calc
      Z ^ 2 - a.D * a.Q ^ 2 = (Z ^ 2 - 1) - a.D * a.Q ^ 2 + 1 := by ring
      _ = 1 := by rw [a.pell_factorization]; ring

theorem rootMultiplicity_D_one :
    rootMultiplicity 1 a.D = m % 2 :=
  a.solution.rootMultiplicity_D_eq_mod_two a.monic_D.ne_zero a.Q_ne_zero
    a.squarefree_D a.eval_one a.contact_one

private theorem eval_Z_neg_one : Z.eval (-1) = a.orientation := by
  have hvalue := a.node_value 0
  rw [a.node_zero] at hvalue
  simpa using hvalue

private theorem eval_Q_neg_one_ne_zero : a.Q.eval (-1) ≠ 0 := by
  rw [Q, squareFactor]
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_prod]
  apply mul_ne_zero a.leadingScale_ne_zero
  apply mul_ne_zero
  · apply pow_ne_zero
    norm_num
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hx := (a.interiorNode_mem_Ioo i).1
    linarith

private theorem derivative_eval_neg_one_ne_zero (a : EndpointAlternant m N Z) :
    (derivative Z).eval (-1) ≠ 0 := by
  rw [a.derivative_Z_eq]
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact_mod_cast Nat.ne_zero_of_lt (a.one_le_m.trans a.m_le_N)
    · apply pow_ne_zero
      norm_num
  · exact a.eval_Q_neg_one_ne_zero

private theorem rootMultiplicity_pellNumerator_neg_one (a : EndpointAlternant m N Z) :
    rootMultiplicity (-1) (Z ^ 2 - 1) = 1 := by
  have hroot : (Z ^ 2 - 1).IsRoot (-1) := by
    simp only [IsRoot, eval_sub, eval_pow]
    rw [a.eval_Z_neg_one]
    rcases a.orientation_eq with horient | horient <;> rw [horient] <;> norm_num
  have hpositive : 0 < rootMultiplicity (-1) (Z ^ 2 - 1) :=
    (rootMultiplicity_pos a.pellNumerator_ne_zero).mpr hroot
  have hnotTwo : ¬1 < rootMultiplicity (-1) (Z ^ 2 - 1) := by
    intro htwo
    have hderivRoot :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot a.pellNumerator_ne_zero).mp htwo |>.2
    simp only [IsRoot, derivative_sub, derivative_pow, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, derivative_one, sub_zero, eval_mul, eval_C] at hderivRoot
    apply a.derivative_eval_neg_one_ne_zero
    have hZ : Z.eval (-1) ≠ 0 := by
      rw [a.eval_Z_neg_one]
      rcases a.orientation_eq with horient | horient <;> rw [horient] <;> norm_num
    exact (mul_eq_zero.mp hderivRoot |>.resolve_left (mul_ne_zero (by norm_num) hZ))
  omega

theorem rootMultiplicity_D_neg_one :
    rootMultiplicity (-1) a.D = 1 := by
  have hvaluation := congrArg (rootMultiplicity (-1 : ℝ)) a.pell_factorization
  have hQroot : rootMultiplicity (-1) a.Q = 0 := by
    apply rootMultiplicity_eq_zero
    simpa only [IsRoot] using a.eval_Q_neg_one_ne_zero
  rw [a.rootMultiplicity_pellNumerator_neg_one,
    rootMultiplicity_mul (mul_ne_zero a.monic_D.ne_zero (pow_ne_zero 2 a.Q_ne_zero)),
    pow_two, rootMultiplicity_mul (mul_ne_zero a.Q_ne_zero a.Q_ne_zero),
    hQroot] at hvaluation
  omega

theorem eval_D_neg_one : a.D.eval (-1) = 0 := by
  exact (rootMultiplicity_pos a.monic_D.ne_zero).mp (by
    rw [a.rootMultiplicity_D_neg_one]
    norm_num)

theorem nonpos_D :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, a.D.eval x ≤ 0 := by
  intro x hx
  apply le_of_not_gt
  intro hxpositive
  let U : Set ℝ := {y | 0 < a.D.eval y}
  have hUopen : IsOpen U := isOpen_lt continuous_const a.D.continuous
  have hxU : x ∈ U := hxpositive
  have hxclosure : x ∈ closure (Set.Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
    exact hx
  obtain ⟨z, hzU, hzinterval⟩ :=
    (mem_closure_iff.mp hxclosure U hUopen hxU)
  have hVopen : IsOpen (U ∩ Set.Ioo (-1 : ℝ) 1) :=
    hUopen.inter isOpen_Ioo
  have hzV : z ∈ U ∩ Set.Ioo (-1 : ℝ) 1 := ⟨hzU, hzinterval⟩
  have hVnhds : U ∩ Set.Ioo (-1 : ℝ) 1 ∈ nhds z := hVopen.mem_nhds hzV
  obtain ⟨l, u, hzlu, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hVnhds
  have hlu' : l < u := hzlu.1.trans hzlu.2
  have hnotSubset : ¬ Set.Ioo l u ⊆ {y : ℝ | a.Q.IsRoot y} := by
    intro hsubset
    have hfinite := Polynomial.finite_setOf_isRoot a.Q_ne_zero
    have hinfinite : ({y : ℝ | a.Q.IsRoot y} : Set ℝ).Infinite :=
      (Set.Ioo_infinite hlu').mono hsubset
    exact hinfinite hfinite
  obtain ⟨y, hylu, hyQ⟩ := Set.not_subset.mp hnotSubset
  have hyV := hlu hylu
  have hyIcc : y ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨hyV.2.1.le, hyV.2.2.le⟩
  have hbounds := a.bounds y hyIcc
  have hQeval : a.Q.eval y ≠ 0 := by
    change ¬a.Q.IsRoot y at hyQ
    exact hyQ
  have hequation := congrArg (eval y) a.pell_factorization
  simp only [eval_sub, eval_pow, eval_mul] at hequation
  norm_num at hequation
  have hQsquare : 0 < a.Q.eval y ^ 2 := sq_pos_of_ne_zero hQeval
  have hZsquare : Z.eval y ^ 2 ≤ 1 := by nlinarith
  have hDpositive : 0 < a.D.eval y := hyV.1
  nlinarith

theorem neg_D :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, a.D.eval x < 0 := by
  intro x hx
  have hnonpos := a.nonpos_D x ⟨hx.1.le, hx.2.le⟩
  apply lt_of_le_of_ne hnonpos
  intro hzero
  have hDeval : a.D.eval x = 0 := hzero
  have hxnhds : Set.Icc (-1 : ℝ) 1 ∈ nhds x := Icc_mem_nhds hx.1 hx.2
  have hmax : IsMaxOn (fun y : ℝ ↦ a.D.eval y)
      (Set.Icc (-1 : ℝ) 1) x := by
    intro y hy
    change a.D.eval y ≤ a.D.eval x
    rw [hDeval]
    exact a.nonpos_D y hy
  have hderivative : (derivative a.D).eval x = 0 :=
    hmax.isLocalMax hxnhds |>.hasDerivAt_eq_zero (a.D.hasDerivAt x)
  have hmultiple : 1 < rootMultiplicity x a.D :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot a.monic_D.ne_zero).mpr
      ⟨hDeval, hderivative⟩
  have hsimple : rootMultiplicity x a.D ≤ 1 := by
    rw [rootMultiplicity_le_iff a.monic_D.ne_zero]
    intro hdvd
    apply not_isUnit_X_sub_C x
    apply a.squarefree_D (X - C x)
    simpa only [Nat.reduceAdd, pow_two] using hdvd
  omega

/-- The algebraic extraction supplies exactly the endpoint-contact package
used by the later coefficient calculation. -/
def contactData : EndpointContactData m N where
  D := a.D
  solution := a.solution
  one_le_m := a.one_le_m
  m_le_N := a.m_le_N
  monic_D := a.monic_D
  squarefree_D := a.squarefree_D
  natDegree_D := a.natDegree_D
  leadingCoeff_eq := by
    simpa only [solution] using a.leadingCoeff_Q.symm
  natDegree_P := by
    simpa only [solution] using a.natDegree_eq
  eval_P_one := by
    simpa only [solution] using a.eval_one
  contact_one := by
    simpa only [solution] using a.contact_one

end EndpointAlternant

end JoseSmoothest
