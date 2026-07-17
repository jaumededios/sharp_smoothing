import JoseSmoothest.SixthOrder

/-!
# The algebraic Zolotarev certificate

This file separates the algebra in the Zolotarev construction from its
elliptic-function input.  The input below is the polynomial Pell equation,
the differential equation, and the equioscillation information supplied by
the first Zolotarev polynomial.  From those data we construct the polynomial
used in the cubic weighted problem and prove its full zero--peak certificate.

The sign of the Pell weight is important: it is `(X ^ 2 - 1) * H`.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

/-- The polynomial multiplying the square in the Zolotarev Pell equation. -/
def zolotarevPellWeight (H : ℝ[X]) : ℝ[X] :=
  (X ^ 2 - 1) * H

/-- Polynomial data supplied by the first Zolotarev polynomial in the cubic
endpoint case.  The analytic construction is responsible for the interval
bounds and equioscillation fields; the remaining fields are polynomial
identities.

`r` is the elliptic ratio `(1 - cn (2a)) / dn (2a)` from the paper. -/
structure CubicZolotarevData (N : ℕ) where
  /-- The first Zolotarev polynomial. -/
  Z : ℝ[X]
  /-- Its companion polynomial in the Pell equation. -/
  V : ℝ[X]
  /-- The remaining quadratic factor of the Pell weight. -/
  H : ℝ[X]
  /-- The endpoint scale coming from the elliptic parameter. -/
  r : ℝ
  /-- The construction is used from degree three onward. -/
  three_le : 3 ≤ N
  /-- The Zolotarev polynomial has the advertised degree bound. -/
  natDegree_Z_le : Z.natDegree ≤ N
  /-- The distinguished endpoint has positive orientation. -/
  eval_one : Z.eval 1 = 1
  /-- The polynomial Pell equation. -/
  pell : Z ^ 2 - zolotarevPellWeight H * V ^ 2 = 1
  /-- Lebedev's differential identity in the endpoint case `c = 1`. -/
  differential : derivative Z = C (N : ℝ) * (X - C 1) * V
  /-- The endpoint value `H(1) = r²`. -/
  eval_H_one : H.eval 1 = r ^ 2
  /-- The elliptic scale is nonzero. -/
  r_ne_zero : r ≠ 0
  /-- The endpoint zero of `V` is simple. -/
  derivative_V_eval_one_ne_zero : (derivative V).eval 1 ≠ 0
  /-- The Zolotarev polynomial is bounded by one on the real interval. -/
  bounds : ∀ x ∈ Set.Icc (-1 : ℝ) 1, -1 ≤ Z.eval x ∧ Z.eval x ≤ 1
  /-- The alternation orientation. -/
  orientation : ℝ
  /-- The orientation is a sign. -/
  orientation_eq : orientation = 1 ∨ orientation = -1
  /-- The equioscillation nodes away from the distinguished endpoint. -/
  nodes : Fin (N - 3 + 1) → ℝ
  /-- The nodes are strictly increasing. -/
  strictMono_nodes : StrictMono nodes
  /-- Every node lies in `[-1, 1)`. -/
  nodes_mem_Ico : ∀ i, nodes i ∈ Set.Ico (-1 : ℝ) 1
  /-- Successive values of `Z` alternate between the two extrema. -/
  node_value : ∀ i, Z.eval (nodes i) = orientation * (-1 : ℝ) ^ (i : ℕ)
  /-- Both extremal values occur on the interval. -/
  exists_negative : ∃ x ∈ Set.Icc (-1 : ℝ) 1, Z.eval x = -1

/-- The scale multiplying `1 - Z` in the cubic Zolotarev numerator. -/
def CubicZolotarevData.scale {N : ℕ} (d : CubicZolotarevData N) : ℝ :=
  9 * d.r ^ 2 / (N : ℝ) ^ 2

/-- The sharp peak in the cubic weighted polynomial problem. -/
def CubicZolotarevData.peak {N : ℕ} (d : CubicZolotarevData N) : ℝ :=
  18 * d.r ^ 2 / (N : ℝ) ^ 2

/-- The numerator obtained from the first Zolotarev polynomial. -/
def CubicZolotarevData.numerator {N : ℕ} (d : CubicZolotarevData N) : ℝ[X] :=
  C d.scale * (1 - d.Z)

/-- The polynomial quotient by the cubic endpoint zero.  Division is taken
by the monic `(X - 1) ^ 3`; the minus sign converts it to the denominator
`(1 - X) ^ 3` used in the weighted problem. -/
def CubicZolotarevData.endpointQuotient {N : ℕ}
    (d : CubicZolotarevData N) : ℝ[X] :=
  -(d.numerator /ₘ ((X - C 1) ^ 3))

@[simp] theorem zolotarevPellWeight_eval_one (H : ℝ[X]) :
    (zolotarevPellWeight H).eval 1 = 0 := by
  simp [zolotarevPellWeight]

theorem zolotarevPellWeight_derivative_eval_one (H : ℝ[X]) :
    (derivative (zolotarevPellWeight H)).eval 1 = 2 * H.eval 1 := by
  simp [zolotarevPellWeight, derivative_mul, derivative_pow]

/-- The elementary Jacobi identities compute the endpoint value of the
quadratic Pell factor.  This is the algebraic simplification used in the
paper to identify `H(1)` with the square of the elliptic ratio
`(1 - cn (2a)) / dn (2a)`. -/
theorem zolotarevEllipticEndpointScale_identity
    (k kComplement sn cn dn : ℝ)
    (hsn_dn : k ^ 2 * sn ^ 2 + dn ^ 2 = 1)
    (hsn_cn : kComplement ^ 2 * sn ^ 2 + cn ^ 2 = dn ^ 2)
    (hdn : dn ≠ 0) :
    (1 - cn / dn ^ 2) ^ 2 +
        (k * kComplement * sn ^ 2 / dn ^ 2) ^ 2 =
      ((1 - cn) / dn) ^ 2 := by
  field_simp
  nlinarith [sq_nonneg (k * kComplement * sn ^ 2)]

/-- The differential identity makes `1` a critical point of `Z`. -/
theorem CubicZolotarevData.derivative_Z_eval_one {N : ℕ}
    (d : CubicZolotarevData N) :
    (derivative d.Z).eval 1 = 0 := by
  rw [d.differential]
  simp

/-- The Pell equation forces the companion polynomial to vanish at the
distinguished endpoint. -/
theorem CubicZolotarevData.eval_V_one {N : ℕ}
    (d : CubicZolotarevData N) :
    d.V.eval 1 = 0 := by
  have hpell := congrArg derivative d.pell
  have hpell_one := congrArg (fun p : ℝ[X] ↦ p.eval 1) hpell
  simp only [derivative_sub, derivative_pow, derivative_mul, derivative_one,
    eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_zero,
    zolotarevPellWeight_eval_one, d.derivative_Z_eval_one,
    zolotarevPellWeight_derivative_eval_one] at hpell_one
  rw [d.eval_H_one] at hpell_one
  norm_num at hpell_one
  exact hpell_one.resolve_left d.r_ne_zero

/-- The distinguished endpoint is also a zero of the second derivative of
`Z`; this is the second of the three endpoint conditions. -/
theorem CubicZolotarevData.secondDerivative_Z_eval_one {N : ℕ}
    (d : CubicZolotarevData N) :
    (derivative (derivative d.Z)).eval 1 = 0 := by
  have hdifferential := congrArg derivative d.differential
  have hdifferential_one :=
    congrArg (fun p : ℝ[X] ↦ p.eval 1) hdifferential
  simp only [derivative_mul, derivative_C, zero_mul, derivative_sub,
    derivative_X, sub_zero, eval_add, eval_mul, eval_C,
    eval_sub, eval_X, d.eval_V_one] at hdifferential_one
  simpa using hdifferential_one

private theorem CubicZolotarevData.thirdDerivative_relation {N : ℕ}
    (d : CubicZolotarevData N) :
    (derivative (derivative (derivative d.Z))).eval 1 =
      2 * (N : ℝ) * (derivative d.V).eval 1 := by
  have hdifferential := congrArg derivative (congrArg derivative d.differential)
  have hdifferential_one :=
    congrArg (fun p : ℝ[X] ↦ p.eval 1) hdifferential
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_sub, derivative_X, derivative_one, sub_zero, eval_add,
    eval_mul, eval_C, eval_sub, eval_X, eval_zero,
    d.eval_V_one] at hdifferential_one
  norm_num at hdifferential_one
  linarith

private theorem CubicZolotarevData.thirdDerivative_pell {N : ℕ}
    (d : CubicZolotarevData N) :
    (derivative (derivative (derivative d.Z))).eval 1 =
      6 * d.r ^ 2 * ((derivative d.V).eval 1) ^ 2 := by
  have hpell := congrArg derivative
    (congrArg derivative (congrArg derivative d.pell))
  have hpell_one := congrArg (fun p : ℝ[X] ↦ p.eval 1) hpell
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_C, derivative_one, zero_mul, zero_add,
    eval_add, eval_sub, eval_mul, eval_pow, eval_C,
    zolotarevPellWeight_eval_one, zolotarevPellWeight_derivative_eval_one,
    d.eval_one, d.derivative_Z_eval_one, d.secondDerivative_Z_eval_one,
    d.eval_V_one] at hpell_one
  rw [d.eval_H_one] at hpell_one
  norm_num at hpell_one
  nlinarith

/-- The Pell and differential identities determine the first nonzero endpoint
coefficient of the companion polynomial. -/
theorem CubicZolotarevData.derivative_V_eval_one {N : ℕ}
    (d : CubicZolotarevData N) :
    (derivative d.V).eval 1 = (N : ℝ) / (3 * d.r ^ 2) := by
  let v := (derivative d.V).eval 1
  have hdiff := d.thirdDerivative_relation
  have hpell := d.thirdDerivative_pell
  have hproduct : v * (2 * (N : ℝ) - 6 * d.r ^ 2 * v) = 0 := by
    dsimp [v]
    nlinarith
  have hlinear : 2 * (N : ℝ) - 6 * d.r ^ 2 * v = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left d.derivative_V_eval_one_ne_zero
  have hdenom : 3 * d.r ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 d.r_ne_zero)
  apply (eq_div_iff hdenom).2
  dsimp [v] at hlinear ⊢
  linarith

/-- The endpoint third derivative is the normalization constant used in the
paper.  This is derived here from the Pell and differential identities. -/
theorem CubicZolotarevData.thirdDerivative_Z_eval_one {N : ℕ}
    (d : CubicZolotarevData N) :
    (derivative (derivative (derivative d.Z))).eval 1 =
      2 * (N : ℝ) ^ 2 / (3 * d.r ^ 2) := by
  rw [d.thirdDerivative_relation, d.derivative_V_eval_one]
  have hdenom : 3 * d.r ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 d.r_ne_zero)
  field_simp

/-- The endpoint conditions forced by the Pell system give the required
cubic zero of `1 - Z`. -/
theorem CubicZolotarevData.cubic_dvd_one_sub_Z {N : ℕ}
    (d : CubicZolotarevData N) :
    (X - C 1) ^ 3 ∣ 1 - d.Z := by
  let p : ℝ[X] := 1 - d.Z
  by_cases hp : p = 0
  · simp [p, hp]
  rw [← le_rootMultiplicity_iff hp]
  have hm : 2 < p.rootMultiplicity 1 := by
    apply lt_rootMultiplicity_of_isRoot_iterate_derivative hp
    intro m hm
    interval_cases m <;>
      simp_all [p, IsRoot, Function.iterate_succ_apply',
        d.eval_one, d.derivative_Z_eval_one, d.secondDerivative_Z_eval_one]
  omega

/-- Consequently the scaled numerator has the same cubic endpoint factor. -/
theorem CubicZolotarevData.cubic_dvd_numerator {N : ℕ}
    (d : CubicZolotarevData N) :
    (X - C 1) ^ 3 ∣ d.numerator := by
  obtain ⟨T, hT⟩ := d.cubic_dvd_one_sub_Z
  refine ⟨C d.scale * T, ?_⟩
  rw [CubicZolotarevData.numerator, hT]
  ring

/-- Exact division by the cubic endpoint factor. -/
theorem CubicZolotarevData.endpoint_factorization {N : ℕ}
    (d : CubicZolotarevData N) :
    (C 1 - X) ^ 3 * d.endpointQuotient = d.numerator := by
  obtain ⟨T, hT⟩ := d.cubic_dvd_numerator
  have hmonic : ((X - C 1) ^ 3 : ℝ[X]).Monic :=
    (monic_X_sub_C 1).pow 3
  have hdiv : d.numerator /ₘ ((X - C 1) ^ 3) = T := by
    rw [hT, mul_divByMonic_cancel_left T hmonic]
  rw [CubicZolotarevData.endpointQuotient, hdiv, hT]
  ring

/-- The Zolotarev numerator has degree at most `N`. -/
theorem CubicZolotarevData.natDegree_numerator_le {N : ℕ}
    (d : CubicZolotarevData N) :
    d.numerator.natDegree ≤ N := by
  rw [CubicZolotarevData.numerator]
  calc
    (C d.scale * (1 - d.Z)).natDegree ≤
        (C d.scale).natDegree + (1 - d.Z).natDegree := natDegree_mul_le
    _ ≤ 0 + N := by
      gcongr
      · simp
      · exact (natDegree_sub_le 1 d.Z).trans
          (max_le (by simp) d.natDegree_Z_le)
    _ = N := zero_add N

/-- Removing the endpoint cube leaves the degree required by the cubic
weighted extremal problem. -/
theorem CubicZolotarevData.natDegree_endpointQuotient_le {N : ℕ}
    (d : CubicZolotarevData N) :
    d.endpointQuotient.natDegree ≤ N - 3 := by
  rw [CubicZolotarevData.endpointQuotient, natDegree_neg,
    natDegree_divByMonic _ ((monic_X_sub_C 1).pow 3),
    (monic_X_sub_C 1).natDegree_pow, natDegree_X_sub_C]
  simpa using Nat.sub_le_sub_right d.natDegree_numerator_le 3

private theorem thirdDerivative_endpointCube_eval_one (S : ℝ[X]) :
    (derivative (derivative (derivative ((C 1 - X) ^ 3 * S)))).eval 1 =
      -6 * S.eval 1 := by
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_sub,
    derivative_C, derivative_X, derivative_one, eval_add, eval_sub, eval_mul,
    eval_pow, eval_C, eval_X, eval_zero]
  norm_num

private theorem CubicZolotarevData.thirdDerivative_numerator_eval_one
    {N : ℕ} (d : CubicZolotarevData N) :
    (derivative (derivative (derivative d.numerator))).eval 1 =
      -d.scale * (derivative (derivative (derivative d.Z))).eval 1 := by
  simp [CubicZolotarevData.numerator, derivative_mul]

/-- The elliptic scale chosen in the paper normalizes the quotient to one at
the distinguished endpoint. -/
theorem CubicZolotarevData.endpointQuotient_eval_one {N : ℕ}
    (d : CubicZolotarevData N) :
    d.endpointQuotient.eval 1 = 1 := by
  have hfactor := congrArg derivative
    (congrArg derivative (congrArg derivative d.endpoint_factorization))
  have hfactor_one := congrArg (fun p : ℝ[X] ↦ p.eval 1) hfactor
  rw [thirdDerivative_endpointCube_eval_one,
    d.thirdDerivative_numerator_eval_one, d.thirdDerivative_Z_eval_one]
    at hfactor_one
  have hNnat : N ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) d.three_le)
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hNnat
  have hr : d.r ^ 2 ≠ 0 := pow_ne_zero 2 d.r_ne_zero
  rw [CubicZolotarevData.scale] at hfactor_one
  field_simp [hN, d.r_ne_zero] at hfactor_one
  ring_nf at hfactor_one
  linarith

/-- Positivity of the Zolotarev scaling factor. -/
theorem CubicZolotarevData.scale_pos {N : ℕ}
    (d : CubicZolotarevData N) :
    0 < d.scale := by
  have hNnat : 0 < N := lt_of_lt_of_le (by norm_num) d.three_le
  have hN : 0 < (N : ℝ) := by exact_mod_cast hNnat
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero d.r_ne_zero))
    (sq_pos_of_pos hN)

/-- The peak is twice the numerator scale. -/
theorem CubicZolotarevData.peak_eq_two_mul_scale {N : ℕ}
    (d : CubicZolotarevData N) :
    d.peak = 2 * d.scale := by
  unfold peak scale
  ring

/-- Interval bounds for the scaled Zolotarev numerator. -/
theorem CubicZolotarevData.numerator_bounds {N : ℕ}
    (d : CubicZolotarevData N) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ d.numerator.eval x ∧ d.numerator.eval x ≤ d.peak := by
  have hz := d.bounds x hx
  have hs := d.scale_pos
  have hvalue : d.numerator.eval x = d.scale * (1 - d.Z.eval x) := by
    simp [CubicZolotarevData.numerator]
  rw [hvalue, d.peak_eq_two_mul_scale]
  constructor <;> nlinarith

/-- The endpoint quotient is nonnegative on the approximation interval. -/
theorem CubicZolotarevData.endpointQuotient_nonnegative {N : ℕ}
    (d : CubicZolotarevData N) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ d.endpointQuotient.eval x := by
  by_cases hxeq : x = 1
  · rw [hxeq, d.endpointQuotient_eval_one]
    norm_num
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hxeq
  have hfactor := congrArg (fun p : ℝ[X] ↦ p.eval x) d.endpoint_factorization
  have hvalue :
      (1 - x) ^ 3 * d.endpointQuotient.eval x = d.numerator.eval x := by
    simpa using hfactor
  have hcube : 0 < (1 - x) ^ 3 := pow_pos (sub_pos.mpr hxlt) 3
  have hq := (d.numerator_bounds x hx).1
  nlinarith

/-- The endpoint quotient is feasible for the cubic weighted polynomial
problem. -/
theorem CubicZolotarevData.endpointQuotient_isAdmissible {N : ℕ}
    (d : CubicZolotarevData N) :
    IsAdmissibleCubicWeightedPolynomial N d.endpointQuotient where
  degree_le := d.natDegree_endpointQuotient_le
  nonnegative := d.endpointQuotient_nonnegative
  eval_one := d.endpointQuotient_eval_one

/-- The Zolotarev equioscillation data become the zero--peak certificate
needed by the cubic weighted problem. -/
def CubicZolotarevData.zeroPeakCertificate {N : ℕ}
    (d : CubicZolotarevData N) :
    CubicZeroPeakCertificate N d.numerator d.peak where
  orientation := d.orientation
  orientation_eq := d.orientation_eq
  nodes := d.nodes
  strictMono_nodes := d.strictMono_nodes
  nodes_mem_Ico := d.nodes_mem_Ico
  bounds := d.numerator_bounds
  exists_peak := by
    obtain ⟨x, hx, hZ⟩ := d.exists_negative
    refine ⟨x, hx, ?_⟩
    have hvalue : d.numerator.eval x = d.scale * (1 - d.Z.eval x) := by
      simp [CubicZolotarevData.numerator]
    rw [hvalue, hZ, d.peak_eq_two_mul_scale]
    ring
  node_value := by
    intro i
    have hvalue : d.numerator.eval (d.nodes i) =
        d.scale * (1 - d.Z.eval (d.nodes i)) := by
      simp [CubicZolotarevData.numerator]
    rw [hvalue, d.node_value, d.peak_eq_two_mul_scale]
    ring

/-! ## Consequences for the sixth-difference kernel problem -/

/-- The kernel reconstructed from the Zolotarev endpoint quotient. -/
def CubicZolotarevData.sixthOrderKernel {n : ℕ}
    (d : CubicZolotarevData (n + 3)) : Kernel :=
  certifiedSixthOrderKernel n d.endpointQuotient

/-- The cubic weighted norm of the Zolotarev endpoint quotient is its
explicit peak. -/
theorem CubicZolotarevData.cubicWeightedPolynomialNorm_endpointQuotient
    {N : ℕ} (d : CubicZolotarevData N) :
    cubicWeightedPolynomialNorm d.endpointQuotient = d.peak :=
  cubicWeightedPolynomialNorm_eq_of_certificate d.endpoint_factorization
    d.zeroPeakCertificate

/-- The reconstructed Zolotarev kernel attains the sixth-order constant. -/
theorem CubicZolotarevData.sixthOrderKernel_attains {n : ℕ}
    (d : CubicZolotarevData (n + 3)) :
    differenceSmoothness 6 d.sixthOrderKernel = 8 * d.peak :=
  certifiedSixthOrderKernel_attains n d.endpointQuotient_isAdmissible
    d.endpoint_factorization d.zeroPeakCertificate

/-- The attained constant in the exact elliptic-ratio form of the paper. -/
theorem CubicZolotarevData.sixthOrderKernel_attains_explicit {n : ℕ}
    (d : CubicZolotarevData (n + 3)) :
    differenceSmoothness 6 d.sixthOrderKernel =
      8 * (18 * d.r ^ 2 / ((n + 3 : ℕ) : ℝ) ^ 2) := by
  simpa [CubicZolotarevData.peak] using d.sixthOrderKernel_attains

/-- The attained constant in the simplified `2⁴ · 3²` form appearing in
Theorem 1.7 of the paper. -/
theorem CubicZolotarevData.sixthOrderKernel_attains_paperConstant {n : ℕ}
    (d : CubicZolotarevData (n + 3)) :
    differenceSmoothness 6 d.sixthOrderKernel =
      144 * d.r ^ 2 / ((n + 3 : ℕ) : ℝ) ^ 2 := by
  rw [d.sixthOrderKernel_attains_explicit]
  ring

/-- Every admissible kernel satisfies the Zolotarev sixth-order lower bound. -/
theorem CubicZolotarevData.sixthOrderSmoothness_ge {n : ℕ}
    (d : CubicZolotarevData (n + 3))
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    8 * d.peak ≤ differenceSmoothness 6 u :=
  sixthOrderSmoothness_ge_of_certificate n u hu
    d.endpointQuotient_isAdmissible d.endpoint_factorization
    d.zeroPeakCertificate

/-- Every admissible kernel satisfies the sixth-order bound in the exact
constant form printed in Theorem 1.7. -/
theorem CubicZolotarevData.sixthOrderSmoothness_ge_paperConstant {n : ℕ}
    (d : CubicZolotarevData (n + 3))
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    144 * d.r ^ 2 / ((n + 3 : ℕ) : ℝ) ^ 2 ≤
      differenceSmoothness 6 u := by
  convert d.sixthOrderSmoothness_ge u hu using 1
  unfold CubicZolotarevData.peak
  ring

/-- Equality in the Zolotarev bound characterizes the reconstructed kernel. -/
theorem CubicZolotarevData.sixthOrderSmoothness_eq_iff {n : ℕ}
    (d : CubicZolotarevData (n + 3))
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    differenceSmoothness 6 u = 8 * d.peak ↔ u = d.sixthOrderKernel :=
  sixthOrderSmoothness_eq_iff_eq_certifiedKernel n u hu
    d.endpointQuotient_isAdmissible d.endpoint_factorization
    d.zeroPeakCertificate

/-- The Zolotarev construction gives the unique admissible kernel attaining
the sharp sixth-order constant. -/
theorem CubicZolotarevData.existsUnique_sixthOrderKernel {n : ℕ}
    (d : CubicZolotarevData (n + 3)) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧ differenceSmoothness 6 u = 8 * d.peak :=
  existsUnique_certifiedSixthOrderKernel n d.endpointQuotient_isAdmissible
    d.endpoint_factorization d.zeroPeakCertificate

end JoseSmoothest
