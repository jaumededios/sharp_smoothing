import JoseSmoothest.SpecialFunctions.PellAbel

/-!
# Endpoint contact for even-order extremal polynomials

This file is the algebraic adapter between polynomial Pell--Abel solutions and
the endpoint normalization used in the arbitrary-even-order smoothing problem.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

/-- The smallest possible genus forced by endpoint contact of order `m`. -/
def endpointGenus (m : ℕ) : ℕ := (m - 1) / 2

@[simp] theorem endpointGenus_two_mul_add_one (g : ℕ) :
    endpointGenus (2 * g + 1) = g := by
  simp only [endpointGenus]
  omega

@[simp] theorem endpointGenus_two_mul_add_two (g : ℕ) :
    endpointGenus (2 * g + 2) = g := by
  simp only [endpointGenus]
  omega

theorem two_mul_endpointGenus_add_parity (m : ℕ) (hm : 0 < m) :
    2 * endpointGenus m + 1 + (1 - m % 2) = m := by
  simp only [endpointGenus]
  omega

/-- Exact endpoint contact on a squarefree Pell--Abel curve forces the curve
genus to be at least `endpointGenus m`. -/
theorem endpointGenus_le_curveGenus
    {g m N : ℕ} {D : ℝ[X]}
    (s : Polynomial.PellAbelSolution D)
    (hm0 : 0 < m) (hD : D.natDegree = 2 * g + 2)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hsqfree : Squarefree D)
    (hP : s.P.natDegree = N) (hN : g + 1 ≤ N)
    (heval : s.P.eval 1 = 1)
    (hcontact : rootMultiplicity 1 (1 - s.P) = m) :
    endpointGenus m ≤ g := by
  have hval := s.rootMultiplicity_differentialNumerator hD0 hQ0 hsqfree heval hm0 hcontact
  have hdeg := s.natDegree_differentialNumerator_le hD hD0 hQ0 hP hN
  have hderiv0 : derivative s.P ≠ 0 := by
    rw [Polynomial.derivative_ne_zero, hP]
    omega
  have hA0 : s.differentialNumerator ≠ 0 := by
    intro hA
    apply hderiv0
    rw [s.derivative_P_eq, hA, zero_mul]
  have hdvd : (X - C (1 : ℝ)) ^ endpointGenus m ∣ s.differentialNumerator := by
    rw [endpointGenus, ← hval]
    exact pow_rootMultiplicity_dvd _ _
  have hrootdeg := natDegree_le_of_dvd hdvd hA0
  have hroot : endpointGenus m ≤ s.differentialNumerator.natDegree := by
    simpa only [natDegree_pow, natDegree_X_sub_C, mul_one] using hrootdeg
  exact hroot.trans hdeg

/-- Minimal-genus endpoint-contact data for an oriented Pell--Abel solution.
The condition on leading coefficients fixes the simultaneous sign and scale
needed by the differential identity. -/
structure EndpointContactData (m N : ℕ) where
  D : ℝ[X]
  solution : Polynomial.PellAbelSolution D
  one_le_m : 1 ≤ m
  m_le_N : m ≤ N
  monic_D : D.Monic
  squarefree_D : Squarefree D
  natDegree_D : D.natDegree = 2 * endpointGenus m + 2
  leadingCoeff_eq : solution.P.leadingCoeff = solution.Q.leadingCoeff
  natDegree_P : solution.P.natDegree = N
  eval_P_one : solution.P.eval 1 = 1
  contact_one : rootMultiplicity 1 (1 - solution.P) = m

namespace EndpointContactData

variable {m N : ℕ} (d : EndpointContactData m N)

/-- The monic Pell weight is nonzero. -/
theorem D_ne_zero : d.D ≠ 0 := d.monic_D.ne_zero

/-- Endpoint normalization forces the Pell numerator to be nonzero. -/
theorem P_ne_zero : d.solution.P ≠ 0 := by
  intro hP
  have := d.eval_P_one
  simp [hP] at this

/-- Equality of leading coefficients forces the Pell denominator to be
nonzero. -/
theorem Q_ne_zero : d.solution.Q ≠ 0 := by
  intro hQ
  have hPlead : d.solution.P.leadingCoeff = 0 := by
    rw [d.leadingCoeff_eq, hQ, leadingCoeff_zero]
  exact d.P_ne_zero (leadingCoeff_eq_zero.mp hPlead)

theorem rootMultiplicity_D_one :
    rootMultiplicity 1 d.D = m % 2 :=
  d.solution.rootMultiplicity_D_eq_mod_two d.D_ne_zero d.Q_ne_zero
    d.squarefree_D d.eval_P_one d.contact_one

theorem rootMultiplicity_Q_one :
    rootMultiplicity 1 d.solution.Q = m / 2 :=
  d.solution.rootMultiplicity_Q_eq_half d.D_ne_zero d.Q_ne_zero
    d.squarefree_D d.eval_P_one d.contact_one

theorem rootMultiplicity_differentialNumerator_one :
    rootMultiplicity 1 d.solution.differentialNumerator = endpointGenus m := by
  simpa only [endpointGenus] using
    d.solution.rootMultiplicity_differentialNumerator d.D_ne_zero d.Q_ne_zero
      d.squarefree_D d.eval_P_one d.one_le_m d.contact_one

private theorem one_le_N (d : EndpointContactData m N) : 1 ≤ N :=
  d.one_le_m.trans d.m_le_N

private theorem genus_add_one_le_N (d : EndpointContactData m N) :
    endpointGenus m + 1 ≤ N := by
  have hg : endpointGenus m ≤ m - 1 := Nat.div_le_self (m - 1) 2
  have hm : 0 < m := d.one_le_m
  have hmN := d.m_le_N
  omega

private theorem differentialNumerator_ne_zero :
    d.solution.differentialNumerator ≠ 0 := by
  intro hA
  have hderiv : derivative d.solution.P = 0 := by
    rw [d.solution.derivative_P_eq, hA, zero_mul]
  have : d.solution.P.natDegree = 0 := Polynomial.derivative_eq_zero.mp hderiv
  rw [d.natDegree_P] at this
  have hN := one_le_N d
  omega

private theorem differentialNumerator_le_genus :
    d.solution.differentialNumerator.natDegree ≤ endpointGenus m :=
  d.solution.natDegree_differentialNumerator_le d.natDegree_D d.D_ne_zero d.Q_ne_zero
    d.natDegree_P (genus_add_one_le_N d)

private theorem differentialNumerator_dvd :
    (X - C (1 : ℝ)) ^ endpointGenus m ∣ d.solution.differentialNumerator := by
  rw [← d.rootMultiplicity_differentialNumerator_one]
  exact pow_rootMultiplicity_dvd _ _

private theorem leadingCoeff_differentialNumerator :
    d.solution.differentialNumerator.leadingCoeff = (N : ℝ) := by
  have hlead := congrArg leadingCoeff d.solution.derivative_P_eq
  simp only [leadingCoeff_derivative, leadingCoeff_mul, d.natDegree_P] at hlead
  have hQlead : d.solution.Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr d.Q_ne_zero
  rw [d.leadingCoeff_eq] at hlead
  rw [mul_comm d.solution.Q.leadingCoeff (N : ℝ)] at hlead
  exact mul_right_cancel₀ hQlead hlead.symm

theorem differentialNumerator_eq :
    d.solution.differentialNumerator =
      C (N : ℝ) * (X - C 1) ^ endpointGenus m := by
  have hdeg : d.solution.differentialNumerator.natDegree ≤
      ((X - C (1 : ℝ)) ^ endpointGenus m).natDegree := by
    simpa only [natDegree_pow, natDegree_X_sub_C, mul_one] using
      d.differentialNumerator_le_genus
  have hshape := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    ((monic_X_sub_C (1 : ℝ)).pow (endpointGenus m)) d.differentialNumerator_dvd
      hdeg
  rw [hshape, d.leadingCoeff_differentialNumerator]

theorem derivative_P_eq :
    derivative d.solution.P =
      C (N : ℝ) * (X - C 1) ^ endpointGenus m * d.solution.Q := by
  rw [d.solution.derivative_P_eq, d.differentialNumerator_eq]

/-- The possible squarefree factor of `D` at the contact endpoint. -/
def endpointParityFactor (_d : EndpointContactData m N) : ℝ[X] :=
  (X - C 1) ^ (m % 2)

/-- The Pell weight with its possible simple endpoint factor removed. -/
def endpointDQuotient : ℝ[X] :=
  d.D / d.endpointParityFactor

theorem endpointParityFactor_dvd :
    d.endpointParityFactor ∣ d.D := by
  rw [endpointParityFactor, ← d.rootMultiplicity_D_one]
  exact pow_rootMultiplicity_dvd _ _

theorem endpoint_D_factorization :
    d.endpointParityFactor * d.endpointDQuotient = d.D := by
  exact EuclideanDomain.mul_div_cancel'
    (pow_ne_zero _ (X_sub_C_ne_zero (1 : ℝ))) d.endpointParityFactor_dvd

theorem eval_endpointDQuotient_one_ne_zero :
    d.endpointDQuotient.eval 1 ≠ 0 := by
  have hmonic : ((X - C (1 : ℝ)) ^ rootMultiplicity 1 d.D).Monic :=
    (monic_X_sub_C (1 : ℝ)).pow _
  have hne := eval_divByMonic_pow_rootMultiplicity_ne_zero (1 : ℝ) d.D_ne_zero
  rw [divByMonic_eq_div d.D hmonic] at hne
  simpa only [endpointDQuotient, endpointParityFactor, d.rootMultiplicity_D_one] using hne

/-- The nonzero coefficient of the squarefree Pell weight at the endpoint. -/
def endpointDValue : ℝ := d.endpointDQuotient.eval 1

/-- The endpoint coefficient of the squarefree Pell weight does not vanish. -/
theorem endpointDValue_ne_zero : d.endpointDValue ≠ 0 :=
  d.eval_endpointDQuotient_one_ne_zero

theorem endpointDValue_eq_even (hm : Even m) :
    d.endpointDValue = d.D.eval 1 := by
  obtain ⟨k, rfl⟩ := hm
  have hmod : (k + k) % 2 = 0 := by omega
  simp [endpointDValue, endpointDQuotient, endpointParityFactor, hmod]

theorem endpointDValue_eq_odd (hm : Odd m) :
    d.endpointDValue = (derivative d.D).eval 1 := by
  obtain ⟨k, rfl⟩ := hm
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  have hfactor := d.endpoint_D_factorization
  simp only [endpointParityFactor, hmod, pow_one] at hfactor
  calc
    d.endpointDValue = d.endpointDQuotient.eval 1 := rfl
    _ = (derivative ((X - C (1 : ℝ)) * d.endpointDQuotient)).eval 1 := by simp
    _ = (derivative d.D).eval 1 := by rw [hfactor]

private def endpointContactQuotient : ℝ[X] :=
  (1 - d.solution.P) /ₘ (X - C 1) ^ m

private def endpointQQuotient : ℝ[X] :=
  d.solution.Q /ₘ (X - C 1) ^ (m / 2)

private theorem endpoint_contact_factorization :
    (X - C (1 : ℝ)) ^ m * d.endpointContactQuotient = 1 - d.solution.P := by
  simpa only [endpointContactQuotient, d.contact_one] using
    (1 - d.solution.P).pow_mul_divByMonic_rootMultiplicity_eq (1 : ℝ)

private theorem endpoint_Q_factorization :
    (X - C (1 : ℝ)) ^ (m / 2) * d.endpointQQuotient = d.solution.Q := by
  simpa only [endpointQQuotient, d.rootMultiplicity_Q_one] using
    d.solution.Q.pow_mul_divByMonic_rootMultiplicity_eq (1 : ℝ)

private theorem eval_endpointContactQuotient_one_ne_zero :
    d.endpointContactQuotient.eval 1 ≠ 0 := by
  simp only [endpointContactQuotient]
  have hpow : (X - C (1 : ℝ)) ^ m =
      (X - C 1) ^ rootMultiplicity 1 (1 - d.solution.P) := by
    rw [d.contact_one]
  rw [hpow]
  exact eval_divByMonic_pow_rootMultiplicity_ne_zero (p := 1 - d.solution.P) (1 : ℝ) (by
      intro h
      have hm := d.contact_one
      rw [h] at hm
      have hmzero : (0 : ℕ) = m := by
        simpa only [rootMultiplicity_zero] using hm
      have hmpos := d.one_le_m
      omega)

private theorem eval_endpointQQuotient_one_ne_zero :
    d.endpointQQuotient.eval 1 ≠ 0 := by
  simp only [endpointQQuotient]
  have hpow : (X - C (1 : ℝ)) ^ (m / 2) =
      (X - C 1) ^ rootMultiplicity 1 d.solution.Q := by
    rw [d.rootMultiplicity_Q_one]
  rw [hpow]
  exact eval_divByMonic_pow_rootMultiplicity_ne_zero (1 : ℝ) d.Q_ne_zero

private theorem differential_exponent_sum :
    endpointGenus m + m / 2 = m - 1 := by
  simp only [endpointGenus]
  omega

private theorem endpoint_pell_coefficient :
    2 * d.endpointContactQuotient.eval 1 =
      -(d.endpointDValue * d.endpointQQuotient.eval 1 ^ 2) := by
  let T : ℝ[X] := X - C 1
  have hpow : T ^ (m % 2) * (T ^ (m / 2)) ^ 2 = T ^ m := by
    rw [pow_two, ← pow_add, ← pow_add]
    congr 1
    omega
  have hDfac : T ^ (m % 2) * d.endpointDQuotient = d.D := by
    simpa only [T, endpointParityFactor] using d.endpoint_D_factorization
  have hPell : (1 - d.solution.P) * (d.solution.P + 1) =
      -(d.D * d.solution.Q ^ 2) := by
    calc
      (1 - d.solution.P) * (d.solution.P + 1) = 1 - d.solution.P ^ 2 := by ring
      _ = -(d.D * d.solution.Q ^ 2) := by rw [d.solution.equation_add]; ring
  have hpoly :
      T ^ m * (d.endpointContactQuotient * (d.solution.P + 1)) =
        T ^ m * (-(d.endpointDQuotient * d.endpointQQuotient ^ 2)) := by
    calc
      T ^ m * (d.endpointContactQuotient * (d.solution.P + 1)) =
          (1 - d.solution.P) * (d.solution.P + 1) := by
            rw [← d.endpoint_contact_factorization]
            dsimp only [T]
            ring
      _ = -(d.D * d.solution.Q ^ 2) := hPell
      _ = -((T ^ (m % 2) * d.endpointDQuotient) *
          (T ^ (m / 2) * d.endpointQQuotient) ^ 2) := by
            rw [hDfac, d.endpoint_Q_factorization]
      _ = T ^ m * (-(d.endpointDQuotient * d.endpointQQuotient ^ 2)) := by
            rw [← hpow]
            ring
  have hbase : d.endpointContactQuotient * (d.solution.P + 1) =
      -(d.endpointDQuotient * d.endpointQQuotient ^ 2) :=
    mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero (1 : ℝ))) hpoly
  have heval := congrArg (eval (1 : ℝ)) hbase
  simp only [eval_mul, eval_add, d.eval_P_one, eval_one, eval_neg, eval_pow] at heval
  change 2 * d.endpointContactQuotient.eval 1 =
    -(d.endpointDValue * d.endpointQQuotient.eval 1 ^ 2)
  dsimp only [endpointDValue]
  nlinarith

private theorem endpoint_differential_coefficient :
    (m : ℝ) * d.endpointContactQuotient.eval 1 =
      -(N : ℝ) * d.endpointQQuotient.eval 1 := by
  let T : ℝ[X] := X - C 1
  have hcontactDeriv :
      T ^ (m - 1) *
          (C (m : ℝ) * d.endpointContactQuotient +
            T * derivative d.endpointContactQuotient) =
        -derivative d.solution.P := by
    calc
      T ^ (m - 1) *
          (C (m : ℝ) * d.endpointContactQuotient +
            T * derivative d.endpointContactQuotient) =
          derivative (T ^ m * d.endpointContactQuotient) := by
            dsimp only [T]
            rw [derivative_mul, derivative_pow]
            simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one]
            have hpow : (X - C (1 : ℝ)) ^ m =
                (X - C 1) ^ (m - 1) * (X - C 1) := by
              rw [← pow_succ]
              congr 1
              have hmpos := d.one_le_m
              omega
            rw [hpow]
            ring
      _ = derivative (1 - d.solution.P) := by rw [d.endpoint_contact_factorization]
      _ = -derivative d.solution.P := by simp
  have hPder : derivative d.solution.P =
      T ^ (m - 1) * (C (N : ℝ) * d.endpointQQuotient) := by
    calc
      derivative d.solution.P =
          C (N : ℝ) * T ^ endpointGenus m * d.solution.Q := by
            simpa only [T] using d.derivative_P_eq
      _ = C (N : ℝ) * T ^ endpointGenus m *
          (T ^ (m / 2) * d.endpointQQuotient) := by
            rw [d.endpoint_Q_factorization]
      _ = T ^ (m - 1) * (C (N : ℝ) * d.endpointQQuotient) := by
            rw [show m - 1 = endpointGenus m + m / 2 from
              (differential_exponent_sum (m := m)).symm, pow_add]
            ring
  have hpoly :
      T ^ (m - 1) *
          (C (m : ℝ) * d.endpointContactQuotient +
            T * derivative d.endpointContactQuotient) =
        T ^ (m - 1) * (-(C (N : ℝ) * d.endpointQQuotient)) := by
    rw [hPder] at hcontactDeriv
    calc
      T ^ (m - 1) *
          (C (m : ℝ) * d.endpointContactQuotient +
            T * derivative d.endpointContactQuotient) =
          -(T ^ (m - 1) * (C (N : ℝ) * d.endpointQQuotient)) := hcontactDeriv
      _ = T ^ (m - 1) * (-(C (N : ℝ) * d.endpointQQuotient)) := by ring
  have hbase :
      C (m : ℝ) * d.endpointContactQuotient +
          T * derivative d.endpointContactQuotient =
        -(C (N : ℝ) * d.endpointQQuotient) :=
    mul_left_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero (1 : ℝ))) hpoly
  have heval := congrArg (eval (1 : ℝ)) hbase
  simpa only [eval_add, eval_mul, eval_C, eval_neg, T, eval_sub, eval_X,
    sub_self, zero_mul, add_zero, neg_mul] using heval

private theorem mthDerivative_eq_contactCoefficient :
    (derivative^[m] d.solution.P).eval 1 =
      -(m.factorial : ℝ) * d.endpointContactQuotient.eval 1 := by
  have hiter := eval_iterate_derivative_rootMultiplicity
    (p := 1 - d.solution.P) (t := (1 : ℝ))
  have hleft :
      (derivative^[m] (1 - d.solution.P)).eval 1 =
        (derivative^[rootMultiplicity 1 (1 - d.solution.P)]
          (1 - d.solution.P)).eval 1 :=
    congrArg (fun k => (derivative^[k] (1 - d.solution.P)).eval 1) d.contact_one.symm
  have hpow : (X - C (1 : ℝ)) ^ rootMultiplicity 1 (1 - d.solution.P) =
      (X - C 1) ^ m := congrArg ((X - C (1 : ℝ)) ^ ·) d.contact_one
  have hfactorial : (rootMultiplicity 1 (1 - d.solution.P)).factorial = m.factorial :=
    congrArg Nat.factorial d.contact_one
  have hcontact :
      (derivative^[m] (1 - d.solution.P)).eval 1 =
        (m.factorial : ℝ) * d.endpointContactQuotient.eval 1 := by
    rw [hleft, hiter, nsmul_eq_mul, hfactorial, hpow]
    rfl
  rw [iterate_derivative_sub, iterate_derivative_one d.one_le_m, zero_sub] at hcontact
  simp only [eval_neg] at hcontact
  linarith

theorem mthDerivative_P_at_one :
    (derivative^[m] d.solution.P).eval 1 =
      (m.factorial : ℝ) *
        (2 * (N : ℝ) ^ 2 / ((m : ℝ) ^ 2 * d.endpointDValue)) := by
  let c : ℝ := d.endpointContactQuotient.eval 1
  let v : ℝ := d.endpointQQuotient.eval 1
  let delta : ℝ := d.endpointDValue
  have hPell : 2 * c = -(delta * v ^ 2) := by
    simpa only [c, v, delta] using d.endpoint_pell_coefficient
  have hdiff : (m : ℝ) * c = -(N : ℝ) * v := by
    simpa only [c, v] using d.endpoint_differential_coefficient
  have hc0 : c ≠ 0 := by
    simpa only [c] using d.eval_endpointContactQuotient_one_ne_zero
  have hdelta0 : delta ≠ 0 := by
    change d.endpointDQuotient.eval 1 ≠ 0
    exact d.eval_endpointDQuotient_one_ne_zero
  have hm0 : (m : ℝ) ≠ 0 := by
    have hmpos := d.one_le_m
    exact_mod_cast (show m ≠ 0 by omega)
  have hden : (m : ℝ) ^ 2 * delta ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hm0) hdelta0
  have hsquare : (m : ℝ) ^ 2 * c ^ 2 = (N : ℝ) ^ 2 * v ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hdiff
    nlinarith
  have hzero : c * (2 * (N : ℝ) ^ 2 + delta * (m : ℝ) ^ 2 * c) = 0 := by
    calc
      c * (2 * (N : ℝ) ^ 2 + delta * (m : ℝ) ^ 2 * c) =
          (N : ℝ) ^ 2 * (2 * c + delta * v ^ 2) +
            delta * ((m : ℝ) ^ 2 * c ^ 2 - (N : ℝ) ^ 2 * v ^ 2) := by ring
      _ = 0 := by
        rw [show 2 * c + delta * v ^ 2 = 0 by linarith,
          show (m : ℝ) ^ 2 * c ^ 2 - (N : ℝ) ^ 2 * v ^ 2 = 0 by linarith]
        ring
  have hlinear : 2 * (N : ℝ) ^ 2 + delta * (m : ℝ) ^ 2 * c = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hc0
  have hc : c = -(2 * (N : ℝ) ^ 2) / ((m : ℝ) ^ 2 * delta) := by
    apply (eq_div_iff hden).2
    nlinarith
  rw [d.mthDerivative_eq_contactCoefficient]
  dsimp only [c] at hc
  dsimp only [delta] at hc
  rw [hc]
  ring

/-- The scale which makes the endpoint quotient equal to one. -/
def endpointScale : ℝ :=
  (-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 * d.endpointDValue /
    (2 * (N : ℝ) ^ 2)

/-- The scale determined by the endpoint coefficient is nonzero. -/
theorem endpointScale_ne_zero : d.endpointScale ≠ 0 := by
  unfold endpointScale
  have hm0 : (m : ℝ) ≠ 0 := by
    have hmpos := d.one_le_m
    exact_mod_cast (show m ≠ 0 by omega)
  have hN0 : (N : ℝ) ≠ 0 := by
    have hNpos := one_le_N d
    exact_mod_cast (show N ≠ 0 by omega)
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hm0))
      d.endpointDValue_ne_zero
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ hN0)

theorem endpointScale_eq_derivative :
    d.endpointScale =
      (-1 : ℝ) ^ (m + 1) * (m.factorial : ℝ) /
        (derivative^[m] d.solution.P).eval 1 := by
  unfold endpointScale
  have hm0 : (m : ℝ) ≠ 0 := by
    have hmpos := d.one_le_m
    exact_mod_cast (show m ≠ 0 by omega)
  have hN0 : (N : ℝ) ≠ 0 := by
    have hNpos := one_le_N d
    exact_mod_cast (show N ≠ 0 by omega)
  have hd0 : d.endpointDValue ≠ 0 := by
    change d.endpointDQuotient.eval 1 ≠ 0
    exact d.eval_endpointDQuotient_one_ne_zero
  have hfac0 : (m.factorial : ℝ) ≠ 0 := by positivity
  have hden0 : (m : ℝ) ^ 2 * d.endpointDValue ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hm0) hd0
  have hnum0 : 2 * (N : ℝ) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hN0)
  have hratio0 : 2 * (N : ℝ) ^ 2 /
      ((m : ℝ) ^ 2 * d.endpointDValue) ≠ 0 := div_ne_zero hnum0 hden0
  have hderiv0 : (derivative^[m] d.solution.P).eval 1 ≠ 0 := by
    rw [d.mthDerivative_P_at_one]
    exact mul_ne_zero hfac0 hratio0
  have hscaleDen0 : 2 * (N : ℝ) ^ 2 ≠ 0 := hnum0
  apply (div_eq_div_iff hscaleDen0 hderiv0).2
  rw [d.mthDerivative_P_at_one]
  calc
    ((-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 * d.endpointDValue) *
        ((m.factorial : ℝ) *
          (2 * (N : ℝ) ^ 2 / ((m : ℝ) ^ 2 * d.endpointDValue))) =
      (-1 : ℝ) ^ (m + 1) * (m.factorial : ℝ) *
        ((2 * (N : ℝ) ^ 2 / ((m : ℝ) ^ 2 * d.endpointDValue)) *
          ((m : ℝ) ^ 2 * d.endpointDValue)) := by ring
    _ = (-1 : ℝ) ^ (m + 1) * (m.factorial : ℝ) * (2 * (N : ℝ) ^ 2) := by
      rw [div_mul_cancel₀ _ hden0]

/-- The polynomial numerator in the endpoint-normalized weighted problem. -/
def endpointNumerator : ℝ[X] :=
  C d.endpointScale * (1 - d.solution.P)

theorem endpoint_factor_dvd_numerator :
    (C 1 - X) ^ m ∣ d.endpointNumerator := by
  have hT : (X - C (1 : ℝ)) ^ m ∣ 1 - d.solution.P := by
    have hpow : (X - C (1 : ℝ)) ^ m =
        (X - C 1) ^ rootMultiplicity 1 (1 - d.solution.P) :=
      congrArg ((X - C (1 : ℝ)) ^ ·) d.contact_one.symm
    rw [hpow]
    exact pow_rootMultiplicity_dvd _ _
  have hbase : Associated (C (1 : ℝ) - X) (X - C 1) := by
    have hneg : C (1 : ℝ) - X = -(X - C 1) := by ring
    rw [hneg]
    exact Associated.neg_left Associated.rfl
  have hfactor : (C (1 : ℝ) - X) ^ m ∣ 1 - d.solution.P :=
    (hbase.pow_pow.dvd_iff_dvd_left).mpr hT
  unfold endpointNumerator
  exact dvd_mul_of_dvd_right hfactor _

/-- The endpoint-normalized quotient polynomial. -/
def endpointQuotient : ℝ[X] :=
  d.endpointNumerator / ((C 1 - X) ^ m)

theorem endpoint_factorization :
    (C 1 - X) ^ m * d.endpointQuotient = d.endpointNumerator := by
  exact EuclideanDomain.mul_div_cancel'
    (pow_ne_zero _ (sub_ne_zero.mpr (X_ne_C (1 : ℝ)).symm))
    d.endpoint_factor_dvd_numerator

private theorem endpointQuotient_eq :
    d.endpointQuotient =
      C (((-1 : ℝ) ^ m) * d.endpointScale) * d.endpointContactQuotient := by
  have hsign : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  have hfactorBase : C (1 : ℝ) - X = -(X - C 1) := by ring
  have hCsign : C ((-1 : ℝ) ^ m) * C ((-1 : ℝ) ^ m) = (1 : ℝ[X]) := by
    rw [← C_mul, show (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = ((-1 : ℝ) ^ m) ^ 2 by ring,
      hsign]
    simp
  have hpolySign : ((-1 : ℝ[X]) ^ m) = C ((-1 : ℝ) ^ m) := by
    simpa only [map_neg, map_one] using
      ((Polynomial.C : ℝ →+* ℝ[X]).map_pow (-1 : ℝ) m).symm
  have hpoly :
      (C 1 - X) ^ m * d.endpointQuotient =
        (C 1 - X) ^ m *
          (C (((-1 : ℝ) ^ m) * d.endpointScale) * d.endpointContactQuotient) := by
    rw [d.endpoint_factorization]
    unfold endpointNumerator
    rw [← d.endpoint_contact_factorization]
    rw [hfactorBase, neg_pow]
    rw [hpolySign]
    rw [map_mul]
    calc
      C d.endpointScale * ((X - C 1) ^ m * d.endpointContactQuotient) =
          (C ((-1 : ℝ) ^ m) * C ((-1 : ℝ) ^ m)) *
            (C d.endpointScale * ((X - C 1) ^ m * d.endpointContactQuotient)) := by
              rw [hCsign, one_mul]
      _ = C ((-1 : ℝ) ^ m) * (X - C 1) ^ m *
          (C ((-1 : ℝ) ^ m) * C d.endpointScale * d.endpointContactQuotient) := by ring
  exact mul_left_cancel₀
    (pow_ne_zero _ (sub_ne_zero.mpr (X_ne_C (1 : ℝ)).symm)) hpoly

theorem endpointQuotient_eval_one :
    d.endpointQuotient.eval 1 = 1 := by
  rw [d.endpointQuotient_eq]
  simp only [eval_mul, eval_C]
  have hc0 := d.eval_endpointContactQuotient_one_ne_zero
  have hfac0 : (m.factorial : ℝ) ≠ 0 := by positivity
  have hderiv := d.mthDerivative_eq_contactCoefficient
  have hscale := d.endpointScale_eq_derivative
  rw [hderiv] at hscale
  have hden0 : -(m.factorial : ℝ) * d.endpointContactQuotient.eval 1 ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hfac0) hc0
  rw [hscale]
  have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ (m + 1) = -1 := by
    rw [pow_succ]
    have hsquare : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
      rw [← pow_mul]
      norm_num
    nlinarith
  calc
    (-1 : ℝ) ^ m *
        (((-1 : ℝ) ^ (m + 1) * (m.factorial : ℝ)) *
          (-(m.factorial : ℝ) * d.endpointContactQuotient.eval 1)⁻¹) *
        d.endpointContactQuotient.eval 1 =
      ((-1 : ℝ) ^ m * (-1 : ℝ) ^ (m + 1)) * (m.factorial : ℝ) *
        (-(m.factorial : ℝ) * d.endpointContactQuotient.eval 1)⁻¹ *
        d.endpointContactQuotient.eval 1 := by ring
    _ = -1 * ((m.factorial : ℝ) *
        (-(m.factorial : ℝ) * d.endpointContactQuotient.eval 1)⁻¹) *
        d.endpointContactQuotient.eval 1 := by rw [hsign]; ring
    _ =
      (-(m.factorial : ℝ) * d.endpointContactQuotient.eval 1) *
        (-(m.factorial : ℝ) * d.endpointContactQuotient.eval 1)⁻¹ := by ring
    _ = 1 := mul_inv_cancel₀ hden0

theorem natDegree_endpointQuotient_le :
    d.endpointQuotient.natDegree ≤ N - m := by
  by_cases hq : d.endpointQuotient = 0
  · simp [hq]
  have hfactor0 : (C (1 : ℝ) - X) ^ m ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.mpr (X_ne_C (1 : ℝ)).symm)
  have hdegreeFactor : ((C (1 : ℝ) - X) ^ m).natDegree = m := by
    have hbase : C (1 : ℝ) - X = -(X - C 1) := by ring
    rw [hbase, natDegree_pow, natDegree_neg, natDegree_X_sub_C, mul_one]
  have hnumDegree : d.endpointNumerator.natDegree ≤ N := by
    unfold endpointNumerator
    calc
      (C d.endpointScale * (1 - d.solution.P)).natDegree ≤
          (C d.endpointScale).natDegree + (1 - d.solution.P).natDegree := natDegree_mul_le
      _ ≤ 0 + N := Nat.add_le_add (by simp) <|
        (natDegree_sub_le (1 : ℝ[X]) d.solution.P).trans <| by
          rw [d.natDegree_P]
          simp
      _ = N := zero_add N
  have hmul := congrArg natDegree d.endpoint_factorization
  rw [natDegree_mul hfactor0 hq, hdegreeFactor] at hmul
  omega

end EndpointContactData

end JoseSmoothest
