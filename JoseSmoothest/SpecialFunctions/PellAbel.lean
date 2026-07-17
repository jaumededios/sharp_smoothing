import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Real.Basic

/-!
# Polynomial Pell--Abel equations

This file develops the algebraic part of the Pell--Abel equation

`P ^ 2 - D * Q ^ 2 = 1`.

It is independent of the later construction of solutions by Abelian
integrals.  In particular, it proves the derivative divisibility, degree
formulae, and endpoint valuation identities needed by the even-order
smoothing problem.
-/

noncomputable section

namespace Polynomial

/-- A polynomial solution of `P² - D Q² = 1`. -/
structure PellAbelSolution {R : Type*} [CommRing R] (D : R[X]) where
  /-- The first coordinate of the solution. -/
  P : R[X]
  /-- The second coordinate of the solution. -/
  Q : R[X]
  /-- The polynomial Pell--Abel equation. -/
  equation : P ^ 2 - D * Q ^ 2 = 1

namespace PellAbelSolution

section CommRing

variable {R : Type*} [CommRing R] {D : R[X]}

/-- The Pell--Abel equation with the second term moved to the right. -/
@[simp] theorem equation_add (s : PellAbelSolution D) :
    s.P ^ 2 = 1 + D * s.Q ^ 2 := by
  calc
    s.P ^ 2 = (s.P ^ 2 - D * s.Q ^ 2) + D * s.Q ^ 2 := by ring
    _ = 1 + D * s.Q ^ 2 := by rw [s.equation]

/-- The trivial Pell--Abel solution. -/
def one : PellAbelSolution D where
  P := 1
  Q := 0
  equation := by simp

/-- Simultaneously negate the two coordinates of a Pell--Abel solution. -/
def neg (s : PellAbelSolution D) : PellAbelSolution D where
  P := -s.P
  Q := -s.Q
  equation := by
    calc
      (-s.P) ^ 2 - D * (-s.Q) ^ 2 = s.P ^ 2 - D * s.Q ^ 2 := by ring
      _ = 1 := s.equation

@[simp] theorem neg_P (s : PellAbelSolution D) : s.neg.P = -s.P := rfl

@[simp] theorem neg_Q (s : PellAbelSolution D) : s.neg.Q = -s.Q := rfl

/-- Multiply the formal expressions `P + Q√D` associated to two solutions. -/
def mul (s t : PellAbelSolution D) : PellAbelSolution D where
  P := s.P * t.P + D * s.Q * t.Q
  Q := s.P * t.Q + s.Q * t.P
  equation := by
    rw [show (s.P * t.P + D * s.Q * t.Q) ^ 2 -
      D * (s.P * t.Q + s.Q * t.P) ^ 2 =
      (s.P ^ 2 - D * s.Q ^ 2) * (t.P ^ 2 - D * t.Q ^ 2) by ring]
    rw [s.equation, t.equation, one_mul]

@[simp] theorem mul_P (s t : PellAbelSolution D) :
    (s.mul t).P = s.P * t.P + D * s.Q * t.Q := rfl

@[simp] theorem mul_Q (s t : PellAbelSolution D) :
    (s.mul t).Q = s.P * t.Q + s.Q * t.P := rfl

/-- The natural power of a Pell--Abel solution under norm-one multiplication. -/
def pow (s : PellAbelSolution D) : ℕ → PellAbelSolution D
  | 0 => one
  | n + 1 => mul (pow s n) s

@[simp] theorem pow_zero (s : PellAbelSolution D) : s.pow 0 = one := rfl

@[simp] theorem pow_succ (s : PellAbelSolution D) (n : ℕ) :
    s.pow (n + 1) = (s.pow n).mul s := rfl

/-- The two coordinates of a Pell--Abel solution are coprime. -/
theorem isCoprime_P_Q (s : PellAbelSolution D) : IsCoprime s.P s.Q := by
  refine ⟨s.P, -(D * s.Q), ?_⟩
  calc
    s.P * s.P + -(D * s.Q) * s.Q = s.P ^ 2 - D * s.Q ^ 2 := by ring
    _ = 1 := s.equation

/-- The first coordinate of a Pell--Abel solution is coprime to its weight. -/
theorem isCoprime_P_D (s : PellAbelSolution D) : IsCoprime s.P D := by
  refine ⟨s.P, -(s.Q ^ 2), ?_⟩
  calc
    s.P * s.P + -(s.Q ^ 2) * D = s.P ^ 2 - D * s.Q ^ 2 := by ring
    _ = 1 := s.equation

end CommRing

section Field

variable {R : Type*} [Field R] {D : R[X]}

/-- The polynomial quotient `P' / Q` attached to a Pell--Abel solution. -/
def differentialNumerator (s : PellAbelSolution D) : R[X] :=
  derivative s.P / s.Q

/-- If `deg D = 2g+2` and `deg P = N`, then `deg Q = N-g-1`. -/
theorem natDegree_Q {g N : ℕ} (s : PellAbelSolution D)
    (hD : D.natDegree = 2 * g + 2)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hP : s.P.natDegree = N) (hN : g + 1 ≤ N) :
    s.Q.natDegree = N - g - 1 := by
  have hdeg := congrArg natDegree s.equation_add
  simp only [natDegree_pow, hP] at hdeg
  rw [show (1 : R[X]) = C 1 by simp, natDegree_C_add,
    natDegree_mul hD0 (pow_ne_zero 2 hQ0), natDegree_pow, hD] at hdeg
  omega

section CharZero

variable [CharZero R]

/-- In characteristic zero, `Q` divides `P'` in every Pell--Abel solution. -/
theorem Q_dvd_derivative_P (s : PellAbelSolution D) :
    s.Q ∣ derivative s.P := by
  have hderiv := congrArg derivative s.equation
  simp only [derivative_sub, derivative_pow, derivative_mul, derivative_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one] at hderiv
  have hdiv : s.Q ∣ C (2 : R) * s.P * derivative s.P := by
    refine ⟨derivative D * s.Q + C (2 : R) * D * derivative s.Q, ?_⟩
    have heq : C (2 : R) * s.P * derivative s.P =
        derivative D * s.Q ^ 2 + D * (C (2 : R) * s.Q * derivative s.Q) := by
      exact sub_eq_zero.mp hderiv
    calc
      C (2 : R) * s.P * derivative s.P =
          derivative D * s.Q ^ 2 + D * (C (2 : R) * s.Q * derivative s.Q) := heq
      _ = s.Q * (derivative D * s.Q + C (2 : R) * D * derivative s.Q) := by ring
  have htwo : IsUnit (C (2 : R)) := Polynomial.isUnit_C.mpr <|
    isUnit_iff_ne_zero.mpr (by exact OfNat.ofNat_ne_zero 2)
  have hcop : IsCoprime s.Q (C (2 : R) * s.P) :=
    (isCoprime_mul_unit_left_right htwo s.Q s.P).mpr s.isCoprime_P_Q.symm
  exact hcop.dvd_of_dvd_mul_left hdiv

/-- Multiplying `P' / Q` back by `Q` recovers `P'`. -/
theorem derivative_P_eq (s : PellAbelSolution D) :
    derivative s.P = s.differentialNumerator * s.Q := by
  by_cases hQ : s.Q = 0
  · have hderiv : derivative s.P = 0 := by
      simpa only [hQ, zero_dvd_iff] using s.Q_dvd_derivative_P
    simp [differentialNumerator, hQ, hderiv]
  · change derivative s.P = (derivative s.P / s.Q) * s.Q
    rw [mul_comm]
    exact (EuclideanDomain.mul_div_cancel' hQ s.Q_dvd_derivative_P).symm

/-- For a weight of degree `2g+2`, the differential numerator has degree at most `g`. -/
theorem natDegree_differentialNumerator_le {g N : ℕ}
    (s : PellAbelSolution D)
    (hD : D.natDegree = 2 * g + 2)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hP : s.P.natDegree = N) (hN : g + 1 ≤ N) :
    s.differentialNumerator.natDegree ≤ g := by
  by_cases hA : s.differentialNumerator = 0
  · simp [hA]
  have hmul := congrArg natDegree s.derivative_P_eq
  rw [natDegree_mul hA hQ0] at hmul
  have hderiv : (derivative s.P).natDegree ≤ N - 1 := by
    simpa only [hP] using natDegree_derivative_le s.P
  have hQ := s.natDegree_Q hD hD0 hQ0 hP hN
  omega

/-- The endpoint valuation identity obtained by factoring `(P-1)(P+1)`. -/
theorem rootMultiplicity_one_sub_P {a : R}
    (s : PellAbelSolution D)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (ha : s.P.eval a = 1) :
    rootMultiplicity a (1 - s.P) =
      rootMultiplicity a D + 2 * rootMultiplicity a s.Q := by
  have hPsub : s.P - 1 ≠ 0 := by
    intro h
    have hP : s.P = 1 := sub_eq_zero.mp h
    have hadd := s.equation_add
    rw [hP] at hadd
    have hzero : D * s.Q ^ 2 = 0 := by
      apply add_left_cancel (a := (1 : R[X]))
      calc
        1 + D * s.Q ^ 2 = 1 := by simpa only [one_pow] using hadd.symm
        _ = 1 + 0 := by simp
    exact mul_ne_zero hD0 (pow_ne_zero 2 hQ0) hzero
  have hPadd : s.P + 1 ≠ 0 := by
    intro h
    have heval := congrArg (eval a) h
    simp only [eval_add, ha, eval_one] at heval
    norm_num at heval
  have hfactor : (s.P - 1) * (s.P + 1) = D * s.Q ^ 2 := by
    calc
      (s.P - 1) * (s.P + 1) = s.P ^ 2 - 1 := by ring
      _ = D * s.Q ^ 2 := by rw [s.equation_add]; ring
  have hr := congrArg (rootMultiplicity a) hfactor
  rw [pow_two] at hr
  rw [rootMultiplicity_mul (mul_ne_zero hPsub hPadd),
    rootMultiplicity_mul (mul_ne_zero hD0 (mul_ne_zero hQ0 hQ0)),
    rootMultiplicity_mul (mul_ne_zero hQ0 hQ0)] at hr
  have hPaddRoot : rootMultiplicity a (s.P + 1) = 0 := by
    apply rootMultiplicity_eq_zero
    simp only [IsRoot, eval_add, ha, eval_one]
    norm_num
  have hneg : rootMultiplicity a (1 - s.P) = rootMultiplicity a (s.P - 1) := by
    have hrel : 1 - s.P = C (-1 : R) * (s.P - 1) := by simp
    rw [hrel, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (by norm_num)) hPsub),
      rootMultiplicity_C]
    simp
  rw [hPaddRoot] at hr
  rw [hneg]
  omega

/-- For squarefree `D`, its endpoint valuation is the parity of the contact order. -/
theorem rootMultiplicity_D_eq_mod_two {a : R} {m : ℕ}
    (s : PellAbelSolution D)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hsqfree : Squarefree D)
    (ha : s.P.eval a = 1)
    (hm : rootMultiplicity a (1 - s.P) = m) :
    rootMultiplicity a D = m % 2 := by
  have hDle : rootMultiplicity a D ≤ 1 := by
    rw [rootMultiplicity_le_iff hD0]
    intro hdvd
    apply not_isUnit_X_sub_C a
    apply hsqfree (X - C a)
    simpa only [Nat.reduceAdd, pow_two] using hdvd
  have hval := s.rootMultiplicity_one_sub_P hD0 hQ0 ha
  rw [hm] at hval
  omega

/-- For squarefree `D`, `Q` has half the endpoint contact order, rounded down. -/
theorem rootMultiplicity_Q_eq_half {a : R} {m : ℕ}
    (s : PellAbelSolution D)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hsqfree : Squarefree D)
    (ha : s.P.eval a = 1)
    (hm : rootMultiplicity a (1 - s.P) = m) :
    rootMultiplicity a s.Q = m / 2 := by
  have hD := s.rootMultiplicity_D_eq_mod_two hD0 hQ0 hsqfree ha hm
  have hval := s.rootMultiplicity_one_sub_P hD0 hQ0 ha
  rw [hm, hD] at hval
  omega

/-- The endpoint contact forces order `(m-1)/2` in the differential numerator. -/
theorem rootMultiplicity_differentialNumerator {a : R} {m : ℕ}
    (s : PellAbelSolution D)
    (hD0 : D ≠ 0) (hQ0 : s.Q ≠ 0)
    (hsqfree : Squarefree D) (ha : s.P.eval a = 1)
    (hm0 : 0 < m)
    (hm : rootMultiplicity a (1 - s.P) = m) :
    rootMultiplicity a s.differentialNumerator = (m - 1) / 2 := by
  have hPsub : s.P - 1 ≠ 0 := by
    intro h
    have hP : s.P = 1 := sub_eq_zero.mp h
    rw [hP] at hm
    simp at hm
    omega
  have hPsubRoot : (s.P - 1).IsRoot a := by
    simp only [IsRoot, eval_sub, ha, eval_one, sub_self]
  have hPsubVal : rootMultiplicity a (s.P - 1) = m := by
    have hrel : 1 - s.P = C (-1 : R) * (s.P - 1) := by simp
    rw [hrel, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (by norm_num)) hPsub),
      rootMultiplicity_C] at hm
    simpa only [zero_add] using hm
  have hderivVal : rootMultiplicity a (derivative s.P) = m - 1 := by
    have h := derivative_rootMultiplicity_of_root hPsubRoot
    simp only [derivative_sub, derivative_one, sub_zero, hPsubVal] at h
    exact h
  have hderiv0 : derivative s.P ≠ 0 := by
    intro hzero
    have hc := eq_C_of_derivative_eq_zero hzero
    have hcval := congrArg (eval a) hc
    simp only [ha, eval_C] at hcval
    apply hPsub
    rw [hc, ← hcval, C_1, sub_self]
  have hA0 : s.differentialNumerator ≠ 0 := by
    intro hA
    apply hderiv0
    rw [s.derivative_P_eq, hA, zero_mul]
  have hmul := congrArg (rootMultiplicity a) s.derivative_P_eq
  rw [rootMultiplicity_mul (mul_ne_zero hA0 hQ0)] at hmul
  have hQval := s.rootMultiplicity_Q_eq_half hD0 hQ0 hsqfree ha hm
  rw [hderivVal, hQval] at hmul
  omega

end CharZero

end Field

section Real

variable {D : ℝ[X]}

/-- On intervals where `D ≤ 0`, the first Pell--Abel coordinate is bounded by one. -/
theorem abs_eval_P_le_one_of_nonpos
    (s : PellAbelSolution D) {a b x : ℝ}
    (hD : ∀ y ∈ Set.Icc a b, D.eval y ≤ 0)
    (hx : x ∈ Set.Icc a b) :
    |s.P.eval x| ≤ 1 := by
  have heq := congrArg (eval x) s.equation_add
  simp only [eval_pow, eval_add, eval_one, eval_mul] at heq
  have hprod : D.eval x * s.Q.eval x ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (hD x hx) (sq_nonneg _)
  have hsquare : s.P.eval x ^ 2 ≤ 1 := by linarith
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (s.P.eval x - 1), sq_nonneg (s.P.eval x + 1)]

end Real

end PellAbelSolution

end Polynomial
