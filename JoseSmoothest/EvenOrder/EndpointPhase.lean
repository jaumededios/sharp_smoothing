import JoseSmoothest.EvenOrder.PellExtraction
import JoseSmoothest.SpecialFunctions.RealPellPhase
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# The direct real phase of an endpoint alternant

This file removes the forced endpoint factors from the squarefree Pell weight
of an endpoint alternant.  The resulting nonvanishing core controls the two
integrable square-root singularities of the real Pell phase.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial Real Set MeasureTheory intervalIntegral

namespace EndpointAlternant

variable {m N : ℕ} {Z : ℝ[X]} (a : EndpointAlternant m N Z)

/-- The endpoint factors removed from the extracted squarefree Pell weight. -/
def phaseEndpointFactor (_a : EndpointAlternant m N Z) : ℝ[X] :=
  (X + C 1) * (X - C 1) ^ (m % 2)

/-- The factor of `D` which has no zero on `[-1,1]`. -/
def phaseCore : ℝ[X] :=
  a.D /ₘ a.phaseEndpointFactor

private theorem phaseEndpointFactor_monic : a.phaseEndpointFactor.Monic := by
  rw [phaseEndpointFactor,
    show X + C (1 : ℝ) = X - C (-1) by norm_num [map_neg]]
  exact (monic_X_sub_C (-1)).mul ((monic_X_sub_C 1).pow (m % 2))

private theorem rootMultiplicity_phaseEndpointFactor_neg_one :
    rootMultiplicity (-1) a.phaseEndpointFactor = 1 := by
  rw [phaseEndpointFactor,
    show X + C (1 : ℝ) = X - C (-1) by norm_num [map_neg],
    rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero (-1))
      (pow_ne_zero _ (X_sub_C_ne_zero 1))),
    rootMultiplicity_X_sub_C]
  have hroot : rootMultiplicity (-1 : ℝ) ((X - C (1 : ℝ)) ^ (m % 2)) = 0 := by
    apply rootMultiplicity_eq_zero
    simp only [IsRoot, eval_pow, eval_sub, eval_X, eval_C]
    exact pow_ne_zero _ (by norm_num)
  rw [hroot]
  simp

private theorem rootMultiplicity_phaseEndpointFactor_one :
    rootMultiplicity 1 a.phaseEndpointFactor = m % 2 := by
  rw [phaseEndpointFactor,
    show X + C (1 : ℝ) = X - C (-1) by norm_num [map_neg],
    rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero (-1))
      (pow_ne_zero _ (X_sub_C_ne_zero 1))),
    rootMultiplicity_X_sub_C_pow]
  have hroot : rootMultiplicity (1 : ℝ) (X - C (-1 : ℝ)) = 0 := by
    rw [rootMultiplicity_eq_zero]
    simp [IsRoot]
  rw [hroot]
  simp

/-- The forced endpoint factor divides the extracted Pell weight. -/
theorem phaseEndpointFactor_dvd :
    a.phaseEndpointFactor ∣ a.D := by
  have hleft : X + C (1 : ℝ) ∣ a.D := by
    have h := pow_rootMultiplicity_dvd a.D (-1 : ℝ)
    rw [a.rootMultiplicity_D_neg_one] at h
    simpa [show X + C (1 : ℝ) = X - C (-1) by norm_num [map_neg]] using h
  have hright : (X - C (1 : ℝ)) ^ (m % 2) ∣ a.D := by
    rw [← a.rootMultiplicity_D_one]
    exact pow_rootMultiplicity_dvd _ _
  apply IsCoprime.mul_dvd _ hleft hright
  rw [show X + C (1 : ℝ) = X - C (-1) by norm_num [map_neg]]
  exact (isCoprime_X_sub_C_of_isUnit_sub
    (by norm_num : IsUnit ((-1 : ℝ) - 1))).pow_right

/-- Factorization of the Pell weight into its endpoint and nonvanishing factors. -/
theorem endpoint_D_core_factorization :
    a.phaseEndpointFactor * a.phaseCore = a.D := by
  change a.phaseEndpointFactor * (a.D /ₘ a.phaseEndpointFactor) = a.D
  have hmod : a.D %ₘ a.phaseEndpointFactor = 0 :=
    (modByMonic_eq_zero_iff_dvd a.phaseEndpointFactor_monic).2
      a.phaseEndpointFactor_dvd
  calc
    a.phaseEndpointFactor * (a.D /ₘ a.phaseEndpointFactor) =
        0 + a.phaseEndpointFactor * (a.D /ₘ a.phaseEndpointFactor) := by simp
    _ = a.D %ₘ a.phaseEndpointFactor +
        a.phaseEndpointFactor * (a.D /ₘ a.phaseEndpointFactor) := by rw [hmod]
    _ = a.D := modByMonic_add_div _ _

private theorem phaseCore_ne_zero : a.phaseCore ≠ 0 := by
  intro hzero
  have := a.endpoint_D_core_factorization
  rw [hzero, mul_zero] at this
  exact a.monic_D.ne_zero this.symm

/-- The core factor has no zero on the closed approximation interval. -/
theorem eval_phaseCore_ne_zero
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    a.phaseCore.eval x ≠ 0 := by
  intro hzero
  have hDroot : a.D.eval x = 0 := by
    rw [← a.endpoint_D_core_factorization, eval_mul, hzero, mul_zero]
  rcases eq_or_lt_of_le hx.1 with rfl | hleft
  · have hmult := congrArg (rootMultiplicity (-1 : ℝ))
      a.endpoint_D_core_factorization
    rw [rootMultiplicity_mul (mul_ne_zero a.phaseEndpointFactor_monic.ne_zero
      a.phaseCore_ne_zero), a.rootMultiplicity_phaseEndpointFactor_neg_one,
      a.rootMultiplicity_D_neg_one] at hmult
    have hpos : 0 < rootMultiplicity (-1 : ℝ) a.phaseCore :=
      (rootMultiplicity_pos a.phaseCore_ne_zero).2 (by simpa [IsRoot] using hzero)
    omega
  · rcases eq_or_lt_of_le hx.2 with rfl | hright
    · have hmult := congrArg (rootMultiplicity (1 : ℝ))
          a.endpoint_D_core_factorization
      rw [rootMultiplicity_mul (mul_ne_zero a.phaseEndpointFactor_monic.ne_zero
        a.phaseCore_ne_zero), a.rootMultiplicity_phaseEndpointFactor_one,
        a.rootMultiplicity_D_one] at hmult
      have hpos : 0 < rootMultiplicity (1 : ℝ) a.phaseCore :=
        (rootMultiplicity_pos a.phaseCore_ne_zero).2 (by simpa [IsRoot] using hzero)
      omega
    · exact (ne_of_lt (a.neg_D x ⟨hleft, hright⟩)) hDroot

private theorem phaseCore_sign_odd_Ioo (hm : Odd m)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < a.phaseCore.eval x := by
  have heps : m % 2 = 1 := Nat.odd_iff.mp hm
  have hfactor := congrArg (eval x) a.endpoint_D_core_factorization
  simp only [phaseEndpointFactor, eval_mul, eval_add, eval_X, eval_C,
    eval_sub, heps, pow_one] at hfactor
  have hD := a.neg_D x hx
  have hleft : 0 < x + 1 := by linarith [hx.1]
  have hright : x - 1 < 0 := by linarith [hx.2]
  have hfactorneg : (x + 1) * (x - 1) < 0 :=
    mul_neg_of_pos_of_neg hleft hright
  rw [← hfactor] at hD
  exact pos_of_mul_neg_right hD hfactorneg.le

/-- For odd contact order, the core factor is positive on the closed interval. -/
theorem phaseCore_sign_odd (hm : Odd m)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 < a.phaseCore.eval x := by
  have hmid : 0 < a.phaseCore.eval 0 :=
    a.phaseCore_sign_odd_Ioo hm (by constructor <;> norm_num)
  apply lt_of_not_ge
  intro hxnonpos
  have hxneg : a.phaseCore.eval x < 0 :=
    lt_of_le_of_ne hxnonpos (a.eval_phaseCore_ne_zero hx)
  have hzeroRange : (0 : ℝ) ∈ Set.Icc (a.phaseCore.eval x) (a.phaseCore.eval 0) :=
    ⟨hxneg.le, hmid.le⟩
  have himage := isPreconnected_Icc.intermediate_value hx
    (show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> norm_num)
    a.phaseCore.continuous.continuousOn hzeroRange
  obtain ⟨z, hz, hzzero⟩ := himage
  exact a.eval_phaseCore_ne_zero hz hzzero

private theorem phaseCore_sign_even_Ioo (hm : Even m)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    a.phaseCore.eval x < 0 := by
  have heps : m % 2 = 0 := Nat.even_iff.mp hm
  have hfactor := congrArg (eval x) a.endpoint_D_core_factorization
  simp only [phaseEndpointFactor, eval_mul, eval_add, eval_X, eval_C,
    heps, pow_zero, mul_one] at hfactor
  have hD := a.neg_D x hx
  have hleft : 0 < x + 1 := by linarith [hx.1]
  rw [← hfactor] at hD
  exact neg_of_mul_neg_right hD hleft.le

/-- For even contact order, the core factor is negative on the closed interval. -/
theorem phaseCore_sign_even (hm : Even m)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    a.phaseCore.eval x < 0 := by
  have hmid : a.phaseCore.eval 0 < 0 :=
    a.phaseCore_sign_even_Ioo hm (by constructor <;> norm_num)
  apply lt_of_not_ge
  intro hxnonneg
  have hxpos : 0 < a.phaseCore.eval x :=
    lt_of_le_of_ne hxnonneg (a.eval_phaseCore_ne_zero hx).symm
  have hzeroRange : (0 : ℝ) ∈ Set.Icc (a.phaseCore.eval 0) (a.phaseCore.eval x) :=
    ⟨hmid.le, hxpos.le⟩
  have himage := isPreconnected_Icc.intermediate_value
    (show (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> norm_num)
    hx a.phaseCore.continuous.continuousOn hzeroRange
  obtain ⟨z, hz, hzzero⟩ := himage
  exact a.eval_phaseCore_ne_zero hz hzzero

/-- The orientation which makes `(X-1)^g` positive on the open interval. -/
def phaseOrientation (_a : EndpointAlternant m N Z) : ℝ :=
  (-1 : ℝ) ^ endpointGenus m

private theorem phaseOrientation_mul_eval (x : ℝ) :
    a.phaseOrientation * ((X - C (1 : ℝ)) ^ endpointGenus m).eval x =
      (1 - x) ^ endpointGenus m := by
  simp only [phaseOrientation, eval_pow, eval_sub, eval_X, eval_C]
  rw [← mul_pow]
  congr 1
  ring

private theorem phaseDensity_intervalIntegrable :
    IntervalIntegrable
      (fun x ↦ a.phaseOrientation *
        ((X - C (1 : ℝ)) ^ endpointGenus m).eval x / √(-a.D.eval x))
      volume (-1) 1 := by
  simp_rw [a.phaseOrientation_mul_eval]
  rcases Nat.even_or_odd m with hm | hm
  · have hweight : IntervalIntegrable
        (fun x : ℝ ↦ (√(x + 1))⁻¹) volume (-1) 1 := by
      have hrpow : IntervalIntegrable
          (fun x : ℝ ↦ (x + 1) ^ (-(1 / 2 : ℝ))) volume (-1) 1 := by
        have hbase : IntervalIntegrable
            (fun x : ℝ ↦ x ^ (-(1 / 2 : ℝ))) volume 0 2 :=
          intervalIntegral.intervalIntegrable_rpow' (by norm_num)
        convert hbase.comp_add_right 1 using 1 <;> norm_num
      refine hrpow.congr ?_
      intro x hx
      have hxnonneg : 0 ≤ x + 1 := by
        rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
        linarith [hx.1]
      change (x + 1) ^ (-(1 / 2 : ℝ)) = (√(x + 1))⁻¹
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hxnonneg]
    let multiplier : ℝ → ℝ := fun x ↦
      (1 - x) ^ endpointGenus m / √(-a.phaseCore.eval x)
    have hmultiplier : ContinuousOn multiplier (uIcc (-1 : ℝ) 1) := by
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      apply ContinuousOn.div
      · exact ((continuous_const.sub continuous_id).pow _).continuousOn
      · exact a.phaseCore.continuous.neg.sqrt.continuousOn
      · intro x hx
        exact (sqrt_pos.2 (by linarith [a.phaseCore_sign_even hm hx])).ne'
    refine (hweight.continuousOn_mul hmultiplier).congr ?_
    intro x hx
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have hfactor := congrArg (eval x) a.endpoint_D_core_factorization
    have heps : m % 2 = 0 := Nat.even_iff.mp hm
    simp only [phaseEndpointFactor, eval_mul, eval_add, eval_X, eval_C,
      heps, pow_zero, mul_one] at hfactor
    have hD : -a.D.eval x = (x + 1) * (-a.phaseCore.eval x) := by
      rw [← hfactor]
      ring
    have hxleft : 0 ≤ x + 1 := by linarith [hx.1]
    change multiplier x * (√(x + 1))⁻¹ =
      (1 - x) ^ endpointGenus m / √(-a.D.eval x)
    rw [hD, Real.sqrt_mul hxleft]
    simp only [multiplier, div_eq_mul_inv, mul_inv_rev]
    ring
  · let multiplier : ℝ → ℝ := fun x ↦
      (1 - x) ^ endpointGenus m / √(a.phaseCore.eval x)
    have hmultiplier : ContinuousOn multiplier (uIcc (-1 : ℝ) 1) := by
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      apply ContinuousOn.div
      · exact ((continuous_const.sub continuous_id).pow _).continuousOn
      · exact a.phaseCore.continuous.sqrt.continuousOn
      · intro x hx
        exact (sqrt_pos.2 (a.phaseCore_sign_odd hm hx)).ne'
    have hproduct :=
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul
        hmultiplier
    refine hproduct.congr ?_
    intro x hx
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    have hfactor := congrArg (eval x) a.endpoint_D_core_factorization
    have heps : m % 2 = 1 := Nat.odd_iff.mp hm
    simp only [phaseEndpointFactor, eval_mul, eval_add, eval_X, eval_C,
      eval_sub, heps, pow_one] at hfactor
    have hD : -a.D.eval x = (1 - x ^ 2) * a.phaseCore.eval x := by
      rw [← hfactor]
      ring
    have hsquare : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    change multiplier x * √((1 - x ^ 2)⁻¹) =
      (1 - x) ^ endpointGenus m / √(-a.D.eval x)
    rw [Real.sqrt_inv]
    rw [hD, Real.sqrt_mul hsquare]
    simp only [multiplier, div_eq_mul_inv, mul_inv_rev]
    ring

/-- The direct real phase data of the extracted Pell solution. -/
def realPhaseInterval : Polynomial.RealPellPhaseInterval
    a.D ((X - C 1) ^ endpointGenus m) where
  left := -1
  right := 1
  left_lt_right := by norm_num
  eval_D_left := a.eval_D_neg_one
  neg_D := a.neg_D
  orientation := a.phaseOrientation
  orientation_sq := by
    simp only [phaseOrientation]
    rw [← pow_mul, mul_comm]
    simp [pow_mul]
  numerator_pos := by
    intro x hx
    rw [a.phaseOrientation_mul_eval]
    exact pow_pos (sub_pos.mpr hx.2) _
  density_intervalIntegrable := a.phaseDensity_intervalIntegrable

/-- The canonical real phase of the endpoint alternant. -/
def phase (x : ℝ) : ℝ :=
  a.realPhaseInterval.phase x

/-- The phase density written with a manifestly nonnegative numerator. -/
theorem phase_density_eq {x : ℝ} :
    a.realPhaseInterval.density x =
      (1 - x) ^ endpointGenus m / √(-a.D.eval x) := by
  rw [Polynomial.RealPellPhaseInterval.density, realPhaseInterval,
    a.phaseOrientation_mul_eval]

/-- The canonical phase is continuous on the closed approximation interval. -/
theorem continuousOn_phase :
    ContinuousOn a.phase (Set.Icc (-1 : ℝ) 1) :=
  a.realPhaseInterval.continuousOn_phase

/-- The canonical phase is normalized to vanish at the left endpoint. -/
@[simp] theorem phase_neg_one : a.phase (-1) = 0 :=
  a.realPhaseInterval.phase_left

/-- The phase density is strictly positive in the open interval. -/
theorem phase_density_pos {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < a.realPhaseInterval.density x :=
  a.realPhaseInterval.density_pos hx

/-- The canonical phase is strictly increasing on the closed interval. -/
theorem strictMonoOn_phase :
    StrictMonoOn a.phase (Set.Icc (-1 : ℝ) 1) :=
  a.realPhaseInterval.strictMonoOn_phase

private theorem eval_Z_neg_one_eq_orientation :
    Z.eval (-1) = a.orientation := by
  have h := a.node_value 0
  rw [a.node_zero] at h
  simpa using h

/-- The endpoint alternant is the cosine of its canonical real phase. -/
theorem eval_eq_cos_phase {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Z.eval x =
      a.orientation * Real.cos ((N : ℝ) * a.phase x) := by
  have h := a.realPhaseInterval.pell_eval_eq_cos_phase
    a.solution a.Q_ne_zero a.derivative_Z_eq hx
  change Z.eval x = Z.eval (-1) * Real.cos ((N : ℝ) * a.phase x) at h
  rw [a.eval_Z_neg_one_eq_orientation] at h
  exact h

/-- The Pell companion is the sine component of the canonical real phase. -/
theorem companion_eq_sin_phase {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    √(-a.D.eval x) * a.Q.eval x =
      -a.phaseOrientation * a.orientation *
        Real.sin ((N : ℝ) * a.phase x) := by
  have h := a.realPhaseInterval.pell_companion_eq_sin_phase
    a.solution a.Q_ne_zero a.derivative_Z_eq hx
  change √(-a.D.eval x) * a.Q.eval x =
    -a.phaseOrientation * Z.eval (-1) *
      Real.sin ((N : ℝ) * a.phase x) at h
  rw [a.eval_Z_neg_one_eq_orientation] at h
  exact h

private theorem node_mem_Icc (j : Fin (N - m + 2)) :
    a.nodes j ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · rw [← a.node_zero]
    exact a.strictMono_nodes.monotone (Fin.zero_le j)
  · rw [← a.node_last]
    exact a.strictMono_nodes.monotone (Fin.le_last j)

private theorem derivative_eval_ne_zero_between_nodes
    (j : Fin (N - m + 1)) {x : ℝ}
    (hleft : a.nodes j.castSucc < x)
    (hright : x < a.nodes j.succ) :
    (derivative Z).eval x ≠ 0 := by
  rw [a.derivative_eq]
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_prod]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast Nat.ne_zero_of_lt (a.one_le_m.trans a.m_le_N)
      · exact a.leadingScale_ne_zero
    · apply pow_ne_zero
      have hnodeRight : a.nodes j.succ ≤ 1 :=
        (a.node_mem_Icc j.succ).2
      linarith
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply sub_ne_zero.mpr
    intro heq
    let k : Fin (N - m + 2) := ⟨(i : ℕ) + 1, by omega⟩
    have hk : a.nodes k = a.interiorNode i := by
      rfl
    have hjkValues : a.nodes j.castSucc < a.nodes k := by
      rw [hk, ← heq]
      exact hleft
    have hkjValues : a.nodes k < a.nodes j.succ := by
      rw [hk, ← heq]
      exact hright
    have hjk : j.castSucc < k :=
      a.strictMono_nodes.lt_iff_lt.mp hjkValues
    have hkj : k < j.succ :=
      a.strictMono_nodes.lt_iff_lt.mp hkjValues
    change (j : ℕ) < (i : ℕ) + 1 at hjk
    change (i : ℕ) + 1 < (j : ℕ) + 1 at hkj
    omega

private theorem node_value_eq_one_or_neg_one (j : Fin (N - m + 2)) :
    Z.eval (a.nodes j) = 1 ∨ Z.eval (a.nodes j) = -1 := by
  rw [a.node_value]
  rcases a.orientation_eq with horient | horient
  · rcases Nat.even_or_odd (j : ℕ) with hj | hj
    · left
      simp [horient, hj.neg_one_pow]
    · right
      simp [horient, hj.neg_one_pow]
  · rcases Nat.even_or_odd (j : ℕ) with hj | hj
    · right
      simp [horient, hj.neg_one_pow]
    · left
      simp [horient, hj.neg_one_pow]

private theorem derivative_eval_eq_zero_of_eval_eq_node
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (j : Fin (N - m + 2))
    (heval : Z.eval x = Z.eval (a.nodes j)) :
    (derivative Z).eval x = 0 := by
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hxnhds : Set.Icc (-1 : ℝ) 1 ∈ nhds x :=
    Icc_mem_nhds hx.1 hx.2
  rcases a.node_value_eq_one_or_neg_one j with hplus | hminus
  · have hmax : IsMaxOn (fun y : ℝ ↦ Z.eval y)
        (Set.Icc (-1 : ℝ) 1) x := by
      intro y hy
      change Z.eval y ≤ Z.eval x
      rw [heval, hplus]
      exact (a.bounds y hy).2
    exact hmax.isLocalMax hxnhds |>.hasDerivAt_eq_zero (Z.hasDerivAt x)
  · have hmin : IsMinOn (fun y : ℝ ↦ Z.eval y)
        (Set.Icc (-1 : ℝ) 1) x := by
      intro y hy
      change Z.eval x ≤ Z.eval y
      rw [heval, hminus]
      exact (a.bounds y hy).1
    exact hmin.isLocalMin hxnhds |>.hasDerivAt_eq_zero (Z.hasDerivAt x)

/-- The phase at the `j`-th alternating node is exactly `j * π / N`. -/
theorem phase_node (j : Fin (N - m + 2)) :
    (N : ℝ) * a.phase (a.nodes j) = (j : ℕ) * Real.pi := by
  have hNnat : 0 < N := a.one_le_m.trans a.m_le_N
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNnat
  induction j using Fin.induction with
  | zero =>
      rw [a.node_zero, a.phase_neg_one]
      norm_num
  | @succ j ih =>
      let theta : ℝ → ℝ := fun x ↦ (N : ℝ) * a.phase x
      have hleftMem := a.node_mem_Icc j.castSucc
      have hrightMem := a.node_mem_Icc j.succ
      have hnodeLt : a.nodes j.castSucc < a.nodes j.succ :=
        a.strictMono_nodes Fin.castSucc_lt_succ
      have hphaseLt : a.phase (a.nodes j.castSucc) < a.phase (a.nodes j.succ) :=
        a.strictMonoOn_phase hleftMem hrightMem hnodeLt
      have hthetaLt : theta (a.nodes j.castSucc) < theta (a.nodes j.succ) :=
        mul_lt_mul_of_pos_left hphaseLt hNreal
      have horient : a.orientation ≠ 0 := by
        rcases a.orientation_eq with h | h <;> rw [h] <;> norm_num
      have hcos : Real.cos (theta (a.nodes j.succ)) =
          (-1 : ℝ) ^ (j.succ : ℕ) := by
        have hphaseCos := a.eval_eq_cos_phase hrightMem
        have hnodeValue := a.node_value j.succ
        change Z.eval (a.nodes j.succ) =
          a.orientation * Real.cos (theta (a.nodes j.succ)) at hphaseCos
        rw [hnodeValue] at hphaseCos
        exact mul_left_cancel₀ horient hphaseCos.symm
      have hsin : Real.sin (theta (a.nodes j.succ)) = 0 := by
        have htrig := Real.sin_sq_add_cos_sq (theta (a.nodes j.succ))
        rw [hcos] at htrig
        have hpow : ((-1 : ℝ) ^ (j.succ : ℕ)) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm]
          simp [pow_mul]
        nlinarith [sq_nonneg (Real.sin (theta (a.nodes j.succ)))]
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
      have hthetaLt' : ((j : ℕ) : ℝ) * Real.pi <
          (k : ℝ) * Real.pi := by
        calc
          ((j : ℕ) : ℝ) * Real.pi = theta (a.nodes j.castSucc) := by
            simpa [theta] using ih.symm
          _ < theta (a.nodes j.succ) := hthetaLt
          _ = (k : ℝ) * Real.pi := hk.symm
      have hjkReal : ((j : ℕ) : ℝ) < (k : ℝ) :=
        lt_of_mul_lt_mul_right hthetaLt' Real.pi_pos.le
      have hjk : ((j : ℕ) : ℤ) < k := by
        exact_mod_cast hjkReal
      have hlower : ((j : ℕ) : ℤ) + 1 ≤ k :=
        Int.add_one_le_iff.mpr hjk
      have hkExact : k = ((j : ℕ) : ℤ) + 1 := by
        by_contra hne
        have hskip : ((j : ℕ) : ℤ) + 1 < k :=
          lt_of_le_of_ne hlower (Ne.symm hne)
        have hskipReal : (((j : ℕ) + 1 : ℕ) : ℝ) < (k : ℝ) := by
          exact_mod_cast hskip
        let target : ℝ := (((j : ℕ) + 1 : ℕ) : ℝ) * Real.pi
        have htargetLeft : theta (a.nodes j.castSucc) < target := by
          calc
            theta (a.nodes j.castSucc) = ((j : ℕ) : ℝ) * Real.pi := by
              simpa [theta] using ih
            _ < (((j : ℕ) + 1 : ℕ) : ℝ) * Real.pi := by
              apply mul_lt_mul_of_pos_right
              · norm_num
              · exact Real.pi_pos
            _ = target := by rfl
        have htargetRight : target < theta (a.nodes j.succ) := by
          calc
            target = (((j : ℕ) + 1 : ℕ) : ℝ) * Real.pi := by rfl
            _ < (k : ℝ) * Real.pi :=
              mul_lt_mul_of_pos_right hskipReal Real.pi_pos
            _ = theta (a.nodes j.succ) := hk
        have hthetaContinuous : ContinuousOn theta
            (Set.Icc (a.nodes j.castSucc) (a.nodes j.succ)) := by
          apply (continuousOn_const.mul a.continuousOn_phase).mono
          exact Set.Icc_subset_Icc hleftMem.1 hrightMem.2
        have himage := intermediate_value_Icc hnodeLt.le hthetaContinuous
          (show target ∈ Set.Icc
              (theta (a.nodes j.castSucc)) (theta (a.nodes j.succ)) by
            exact ⟨htargetLeft.le, htargetRight.le⟩)
        obtain ⟨x, hxnodes, hthetaX⟩ := himage
        have hxleft : a.nodes j.castSucc < x := by
          apply lt_of_le_of_ne hxnodes.1
          intro heq
          have : theta (a.nodes j.castSucc) = target := by
            rw [heq]
            exact hthetaX
          exact (ne_of_lt htargetLeft) this
        have hxright : x < a.nodes j.succ := by
          apply lt_of_le_of_ne hxnodes.2
          intro heq
          have : target = theta (a.nodes j.succ) := by
            rw [← heq]
            exact hthetaX.symm
          exact (ne_of_lt htargetRight) this
        have hxGlobal : x ∈ Set.Ioo (-1 : ℝ) 1 := by
          constructor
          · exact lt_of_le_of_lt hleftMem.1 hxleft
          · exact lt_of_lt_of_le hxright hrightMem.2
        have hevalX : Z.eval x =
            a.orientation * (-1 : ℝ) ^ ((j : ℕ) + 1) := by
          rw [a.eval_eq_cos_phase ⟨hxGlobal.1.le, hxGlobal.2.le⟩]
          change a.orientation * Real.cos (theta x) = _
          rw [hthetaX]
          exact congrArg (a.orientation * ·)
            (Real.cos_nat_mul_pi ((j : ℕ) + 1))
        have hevalNode : Z.eval (a.nodes j.succ) =
            a.orientation * (-1 : ℝ) ^ ((j : ℕ) + 1) := by
          simpa using a.node_value j.succ
        have hderivative := a.derivative_eval_eq_zero_of_eval_eq_node
          hxGlobal j.succ (hevalX.trans hevalNode.symm)
        exact a.derivative_eval_ne_zero_between_nodes j hxleft hxright hderivative
      calc
        theta (a.nodes j.succ) = (k : ℝ) * Real.pi := hk.symm
        _ = (((j : ℕ) + 1 : ℕ) : ℝ) * Real.pi := by
          rw [hkExact]
          norm_num
        _ = ((j.succ : ℕ) : ℝ) * Real.pi := by rfl

/-- The total phase winding is exactly `(N - m + 1) * π`. -/
theorem phaseLength :
    (N : ℝ) * a.phase 1 = ((N - m + 1 : ℕ) : ℝ) * Real.pi := by
  have h := a.phase_node (Fin.last (N - m + 1))
  rw [a.node_last] at h
  simpa using h

end EndpointAlternant

end JoseSmoothest
