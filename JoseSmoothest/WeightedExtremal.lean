import JoseSmoothest.Alternation
import JoseSmoothest.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

/-!
# The weighted Chebyshev extremal problem

This file formalizes Proposition 1.6 of Gaitán--Garzón--Madrid.  The
optimizer is obtained by composing a Chebyshev polynomial with an affine map
and removing its double zero at `1`.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

/-- The sharp constant in Proposition 1.6. -/
def weightedChebyshevConstant (N : ℕ) : ℝ :=
  16 / (N : ℝ) ^ 2 * Real.tan (Real.pi / (2 * (N : ℝ))) ^ 2

/-- The affine argument used to transform `T_N`. -/
def affineChebyshevArgument (N : ℕ) : ℝ[X] :=
  C ((1 + Real.cos (Real.pi / (N : ℝ))) / 2) * (X + 1) - 1

/-- The numerator `(8/N²)tan²(π/2N) * (1 + T_N(L(X)))`. -/
def transformedChebyshevPolynomial (N : ℕ) : ℝ[X] :=
  C (8 / (N : ℝ) ^ 2 * Real.tan (Real.pi / (2 * (N : ℝ))) ^ 2) *
    (1 + (Polynomial.Chebyshev.T ℝ N).comp
      (affineChebyshevArgument N))

/-- The polynomial optimizer `S_{N-2}` from equation (1.8). -/
def weightedExtremalPolynomial (N : ℕ) : ℝ[X] :=
  transformedChebyshevPolynomial N / (C 1 - X) ^ 2

theorem weightedChebyshevConstant_nonneg (N : ℕ) :
    0 ≤ weightedChebyshevConstant N := by
  unfold weightedChebyshevConstant
  positivity

private def affineScale (N : ℕ) : ℝ :=
  (1 + Real.cos (Real.pi / (N : ℝ))) / 2

private def transformedScale (N : ℕ) : ℝ :=
  8 / (N : ℝ) ^ 2 * Real.tan (Real.pi / (2 * (N : ℝ))) ^ 2

private theorem affineChebyshevArgument_eval (N : ℕ) (x : ℝ) :
    (affineChebyshevArgument N).eval x = affineScale N * (x + 1) - 1 := by
  simp [affineChebyshevArgument, affineScale]

private theorem transformedChebyshevPolynomial_eval (N : ℕ) (x : ℝ) :
    (transformedChebyshevPolynomial N).eval x =
      transformedScale N *
        (1 + (Polynomial.Chebyshev.T ℝ N).eval
          (affineScale N * (x + 1) - 1)) := by
  simp [transformedChebyshevPolynomial, transformedScale,
    affineChebyshevArgument_eval]

private theorem chebyshevAngle_pos_lt_pi (N : ℕ) (hN : 2 ≤ N) :
    0 < Real.pi / (N : ℝ) ∧ Real.pi / (N : ℝ) < Real.pi := by
  have hNr : 0 < (N : ℝ) := by positivity
  constructor
  · exact div_pos Real.pi_pos hNr
  · rw [div_lt_iff₀ hNr]
    have hNone : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    nlinarith [Real.pi_pos]

private theorem chebyshev_eval_endpoint (N : ℕ) (hN : 2 ≤ N) :
    (Polynomial.Chebyshev.T ℝ N).eval
      (Real.cos (Real.pi / (N : ℝ))) = -1 := by
  rw [Polynomial.Chebyshev.T_real_cos]
  have hNr : (N : ℝ) ≠ 0 := by positivity
  simp only [Int.cast_natCast]
  rw [show (N : ℝ) * (Real.pi / (N : ℝ)) = Real.pi by field_simp]
  exact Real.cos_pi

private theorem chebyshev_derivative_eval_endpoint
    (N : ℕ) (hN : 2 ≤ N) :
    (derivative (Polynomial.Chebyshev.T ℝ N)).eval
      (Real.cos (Real.pi / (N : ℝ))) = 0 := by
  let θ : ℝ := Real.pi / (N : ℝ)
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hsin : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi
      (chebyshevAngle_pos_lt_pi N hN).1
      (chebyshevAngle_pos_lt_pi N hN).2).ne'
  have hmul : (N : ℝ) * θ = Real.pi := by
    dsimp [θ]
    field_simp
  have hu := Polynomial.Chebyshev.U_real_cos θ ((N : ℤ) - 1)
  have hu_zero : (Polynomial.Chebyshev.U ℝ ((N : ℤ) - 1)).eval
      (Real.cos θ) = 0 := by
    apply (mul_eq_zero_iff_right hsin).mp
    rw [hu]
    convert Real.sin_pi using 2
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
    calc
      ((N : ℝ) - 1 + 1) * θ = (N : ℝ) * θ := by ring
      _ = Real.pi := hmul
  rw [Polynomial.Chebyshev.T_derivative_eq_U, eval_mul]
  simp only [eval_intCast, Int.cast_natCast]
  rw [hu_zero, mul_zero]

private theorem affineScale_pos (N : ℕ) (hN : 2 ≤ N) :
    0 < affineScale N := by
  let θ : ℝ := Real.pi / (N : ℝ)
  have hθ := chebyshevAngle_pos_lt_pi N hN
  have hcos : 0 < Real.cos (θ / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hdouble : 1 + Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 := by
    rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
    ring
  unfold affineScale
  change 0 < (1 + Real.cos θ) / 2
  rw [hdouble]
  positivity

private theorem transformedScale_pos (N : ℕ) (hN : 2 ≤ N) :
    0 < transformedScale N := by
  have hNr : 0 < (N : ℝ) := by positivity
  have hangle : 0 < Real.pi / (2 * (N : ℝ)) := by positivity
  have hangle_lt : Real.pi / (2 * (N : ℝ)) < Real.pi / 2 := by
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * N) (by norm_num : (0 : ℝ) < 2)]
    have hNone : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    nlinarith [Real.pi_pos]
  unfold transformedScale
  exact mul_pos (div_pos (by norm_num) (sq_pos_of_pos hNr))
    (sq_pos_of_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hangle hangle_lt))

private theorem affineChebyshevArgument_eval_one (N : ℕ) :
    (affineChebyshevArgument N).eval 1 =
      Real.cos (Real.pi / (N : ℝ)) := by
  rw [affineChebyshevArgument_eval]
  unfold affineScale
  ring

private theorem transformedChebyshevPolynomial_eval_one
    (N : ℕ) (hN : 2 ≤ N) :
    (transformedChebyshevPolynomial N).eval 1 = 0 := by
  rw [transformedChebyshevPolynomial_eval]
  rw [show affineScale N * (1 + 1) - 1 =
      Real.cos (Real.pi / (N : ℝ)) by
    unfold affineScale
    ring]
  rw [chebyshev_eval_endpoint N hN]
  ring

private theorem affineChebyshevArgument_derivative (N : ℕ) :
    derivative (affineChebyshevArgument N) = C (affineScale N) := by
  simp [affineChebyshevArgument, affineScale]

private theorem transformedChebyshevPolynomial_derivative_eval_one
    (N : ℕ) (hN : 2 ≤ N) :
    (derivative (transformedChebyshevPolynomial N)).eval 1 = 0 := by
  simp only [transformedChebyshevPolynomial, derivative_mul, derivative_C, zero_mul,
    zero_add, derivative_add, derivative_one, derivative_comp, eval_mul, eval_C,
    eval_comp, affineChebyshevArgument_derivative]
  rw [affineChebyshevArgument_eval_one,
    chebyshev_derivative_eval_endpoint N hN]
  simp

private theorem transformedChebyshevPolynomial_ne_zero
    (N : ℕ) (hN : 2 ≤ N) :
    transformedChebyshevPolynomial N ≠ 0 := by
  let a := affineScale N
  let y : ℝ := 2 / a - 1
  have ha : a ≠ 0 := (affineScale_pos N hN).ne'
  have harg : a * (y + 1) - 1 = 1 := by
    dsimp [y]
    field_simp
    ring
  intro hzero
  have heval := congrArg (fun q : ℝ[X] ↦ q.eval y) hzero
  rw [transformedChebyshevPolynomial_eval] at heval
  simp only [eval_zero] at heval
  change transformedScale N *
      (1 + (Polynomial.Chebyshev.T ℝ N).eval (a * (y + 1) - 1)) = 0 at heval
  rw [harg] at heval
  simp at heval
  nlinarith [transformedScale_pos N hN]

private theorem transformedChebyshevPolynomial_second_derivative_formula (N : ℕ) :
    (derivative^[2] (transformedChebyshevPolynomial N)).eval 1 =
      transformedScale N * affineScale N ^ 2 *
        (derivative^[2] (Polynomial.Chebyshev.T ℝ N)).eval
          (Real.cos (Real.pi / (N : ℝ))) := by
  simp only [transformedChebyshevPolynomial, Function.iterate_succ_apply,
    Function.iterate_zero_apply, derivative_mul, derivative_C, zero_mul,
    zero_add, derivative_add, derivative_one, derivative_comp,
    affineChebyshevArgument_derivative, mul_zero, add_zero, eval_mul,
    eval_C, eval_comp, affineChebyshevArgument_eval_one]
  simp [transformedScale, affineScale]
  ring

private theorem chebyshev_second_derivative_eval_endpoint
    (N : ℕ) (hN : 2 ≤ N) :
    (1 - Real.cos (Real.pi / (N : ℝ)) ^ 2) *
        (derivative^[2] (Polynomial.Chebyshev.T ℝ N)).eval
          (Real.cos (Real.pi / (N : ℝ))) = (N : ℝ) ^ 2 := by
  have h :=
    Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T
      (R := ℝ) (N : ℤ)
  have he := congrArg
    (fun p : ℝ[X] ↦ p.eval (Real.cos (Real.pi / (N : ℝ)))) h
  simp only [eval_mul, eval_sub, eval_one, eval_pow, eval_X,
    Int.cast_pow, Int.cast_natCast] at he
  rw [chebyshev_derivative_eval_endpoint N hN,
    chebyshev_eval_endpoint N hN] at he
  norm_num at he ⊢
  simpa using he

private theorem transformedChebyshevPolynomial_second_derivative_eval_one
    (N : ℕ) (hN : 2 ≤ N) :
    (derivative^[2] (transformedChebyshevPolynomial N)).eval 1 = 2 := by
  rw [transformedChebyshevPolynomial_second_derivative_formula]
  let θ : ℝ := Real.pi / (N : ℝ)
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hθpos : 0 < θ := by dsimp [θ]; positivity
  have hθlt : θ < Real.pi := by
    dsimp [θ]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < N)]
    have hNone : (1 : ℝ) < N := by
      exact_mod_cast (show 1 < N by omega)
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (θ / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hcosdouble : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
    ring
  have hhalf :
      Real.tan (θ / 2) ^ 2 * (1 + Real.cos θ) ^ 2 =
        1 - Real.cos θ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos, hcosdouble]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]
  have hscale :
      transformedScale N * affineScale N ^ 2 =
        2 * (1 - Real.cos θ ^ 2) / (N : ℝ) ^ 2 := by
    unfold transformedScale affineScale
    rw [show Real.pi / (2 * (N : ℝ)) = θ / 2 by
      dsimp [θ]
      ring]
    change 8 / (N : ℝ) ^ 2 * Real.tan (θ / 2) ^ 2 *
        ((1 + Real.cos θ) / 2) ^ 2 =
      2 * (1 - Real.cos θ ^ 2) / (N : ℝ) ^ 2
    calc
      8 / (N : ℝ) ^ 2 * Real.tan (θ / 2) ^ 2 *
          ((1 + Real.cos θ) / 2) ^ 2 =
          2 / (N : ℝ) ^ 2 *
            (Real.tan (θ / 2) ^ 2 * (1 + Real.cos θ) ^ 2) := by ring
      _ = 2 / (N : ℝ) ^ 2 * (1 - Real.cos θ ^ 2) := by rw [hhalf]
      _ = 2 * (1 - Real.cos θ ^ 2) / (N : ℝ) ^ 2 := by ring
  rw [hscale]
  have hsecond := chebyshev_second_derivative_eval_endpoint N hN
  change (1 - Real.cos θ ^ 2) *
      (derivative^[2] (Polynomial.Chebyshev.T ℝ N)).eval (Real.cos θ) =
        (N : ℝ) ^ 2 at hsecond
  calc
    2 * (1 - Real.cos θ ^ 2) / (N : ℝ) ^ 2 *
        (derivative^[2] (Polynomial.Chebyshev.T ℝ N)).eval (Real.cos θ) =
        2 * ((1 - Real.cos θ ^ 2) *
          (derivative^[2] (Polynomial.Chebyshev.T ℝ N)).eval (Real.cos θ)) /
            (N : ℝ) ^ 2 := by ring
    _ = 2 * (N : ℝ) ^ 2 / (N : ℝ) ^ 2 := by rw [hsecond]
    _ = 2 := by field_simp

private theorem transformedChebyshevPolynomial_double_root_dvd
    (N : ℕ) (hN : 2 ≤ N) :
    (C 1 - X) ^ 2 ∣ transformedChebyshevPolynomial N := by
  let q := transformedChebyshevPolynomial N
  have hq : q ≠ 0 := transformedChebyshevPolynomial_ne_zero N hN
  have hroot : q.IsRoot 1 := by
    exact transformedChebyshevPolynomial_eval_one N hN
  have hroot' : (derivative q).IsRoot 1 := by
    exact transformedChebyshevPolynomial_derivative_eval_one N hN
  have hmult : 1 < q.rootMultiplicity 1 :=
    (one_lt_rootMultiplicity_iff_isRoot hq).2 ⟨hroot, hroot'⟩
  have hdvd : (X - C 1) ^ 2 ∣ q :=
    (le_rootMultiplicity_iff hq).1 (by omega)
  rw [show (C 1 - X : ℝ[X]) ^ 2 = (X - C 1) ^ 2 by ring]
  exact hdvd

private theorem denominator_monic : ((C 1 - X : ℝ[X]) ^ 2).Monic := by
  rw [show (C 1 - X : ℝ[X]) ^ 2 = (X - C 1) ^ 2 by ring]
  exact (monic_X_sub_C 1).pow 2

private theorem transformedChebyshevPolynomial_eq_mul_weightedExtremal
    (N : ℕ) (hN : 2 ≤ N) :
    (C 1 - X) ^ 2 * weightedExtremalPolynomial N =
      transformedChebyshevPolynomial N := by
  let d : ℝ[X] := (C 1 - X) ^ 2
  let q : ℝ[X] := transformedChebyshevPolynomial N
  have hd : d.Monic := denominator_monic
  have hdvd : d ∣ q := transformedChebyshevPolynomial_double_root_dvd N hN
  have hmod : q %ₘ d = 0 := (modByMonic_eq_zero_iff_dvd hd).2 hdvd
  unfold weightedExtremalPolynomial
  rw [← divByMonic_eq_div _ denominator_monic]
  change d * (q /ₘ d) = q
  nth_rewrite 2 [← modByMonic_add_div q d]
  rw [hmod, zero_add]

theorem weightedExtremalPolynomial_eval_one
    (N : ℕ) (hN : 2 ≤ N) :
    (weightedExtremalPolynomial N).eval 1 = 1 := by
  have h := transformedChebyshevPolynomial_eq_mul_weightedExtremal N hN
  have hd := congrArg
    (fun r : ℝ[X] ↦ (derivative^[2] r).eval 1) h
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply] at hd
  have hsecond :
      (derivative (derivative (transformedChebyshevPolynomial N))).eval 1 = 2 := by
    simpa [Function.iterate_succ_apply] using
      transformedChebyshevPolynomial_second_derivative_eval_one N hN
  rw [hsecond] at hd
  simp [derivative_mul, derivative_pow, derivative_sub, derivative_C,
    derivative_X] at hd
  linarith

private theorem affineChebyshevArgument_natDegree_le (N : ℕ) :
    (affineChebyshevArgument N).natDegree ≤ 1 := by
  unfold affineChebyshevArgument
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · apply (natDegree_mul_le).trans
    calc
      (C ((1 + Real.cos (Real.pi / (N : ℝ))) / 2)).natDegree +
          (X + 1).natDegree ≤ 0 + 1 := Nat.add_le_add (by simp)
        ((natDegree_add_le _ _).trans (by simp))
      _ = 1 := by omega
  · simp

private theorem transformedChebyshevPolynomial_natDegree_le (N : ℕ) :
    (transformedChebyshevPolynomial N).natDegree ≤ N := by
  unfold transformedChebyshevPolynomial
  apply (natDegree_mul_le).trans
  simp only [natDegree_C, zero_add]
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact natDegree_comp_le.trans <| by
      rw [Polynomial.Chebyshev.natDegree_T]
      simp only [Int.natAbs_natCast]
      simpa using Nat.mul_le_mul_left N (affineChebyshevArgument_natDegree_le N)

theorem weightedExtremalPolynomial_natDegree_le
    (N : ℕ) (hN : 2 ≤ N) :
    (weightedExtremalPolynomial N).natDegree ≤ N - 2 := by
  unfold weightedExtremalPolynomial
  rw [← divByMonic_eq_div _ denominator_monic]
  rw [natDegree_divByMonic _ denominator_monic]
  have hden : ((C 1 - X : ℝ[X]) ^ 2).natDegree = 2 := by
    rw [show (C 1 - X : ℝ[X]) ^ 2 = (X - C 1) ^ 2 by ring,
      natDegree_pow, natDegree_X_sub_C]
  rw [hden]
  exact Nat.sub_le_sub_right (transformedChebyshevPolynomial_natDegree_le N) 2

private theorem affineChebyshevArgument_maps_Icc
    (N : ℕ) (hN : 2 ≤ N)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    affineScale N * (x + 1) - 1 ∈ Set.Icc (-1 : ℝ) 1 := by
  have ha : 0 ≤ affineScale N := (affineScale_pos N hN).le
  have hxadd : 0 ≤ x + 1 := by linarith [hx.1]
  have hxadd_le : x + 1 ≤ 2 := by linarith [hx.2]
  have hacos : affineScale N ≤ 1 := by
    unfold affineScale
    linarith [Real.cos_le_one (Real.pi / (N : ℝ))]
  constructor
  · nlinarith [mul_nonneg ha hxadd]
  · nlinarith [mul_le_mul_of_nonneg_left hxadd_le ha,
      mul_le_mul_of_nonneg_right hacos (by norm_num : (0 : ℝ) ≤ 2)]

private theorem transformedChebyshevPolynomial_bounds
    (N : ℕ) (hN : 2 ≤ N)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ (transformedChebyshevPolynomial N).eval x ∧
      (transformedChebyshevPolynomial N).eval x ≤ 2 * transformedScale N := by
  rw [transformedChebyshevPolynomial_eval]
  have harg := affineChebyshevArgument_maps_Icc N hN hx
  have hT := Polynomial.Chebyshev.abs_eval_T_real_le_one (N : ℤ)
    (show |affineScale N * (x + 1) - 1| ≤ 1 by
      exact (abs_le).2 harg)
  have hT' := (abs_le.mp hT)
  have hs := (transformedScale_pos N hN).le
  constructor <;> nlinarith

theorem weightedExtremalPolynomial_nonnegative
    (N : ℕ) (hN : 2 ≤ N) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ (weightedExtremalPolynomial N).eval x := by
  intro x hx
  by_cases hx1 : x = 1
  · subst x
    rw [weightedExtremalPolynomial_eval_one N hN]
    norm_num
  have hq := (transformedChebyshevPolynomial_bounds N hN hx).1
  have hmul := transformedChebyshevPolynomial_eq_mul_weightedExtremal N hN
  have heval := congrArg (fun q : ℝ[X] ↦ q.eval x) hmul
  simp only [eval_mul, eval_pow, eval_sub, eval_C, eval_X] at heval
  have hd : 0 < (1 - x) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hx1))
  nlinarith

private def transformedPeakPoint (N : ℕ) : ℝ :=
  (1 + Real.cos (2 * (Real.pi / (N : ℝ)))) / affineScale N - 1

private theorem transformedPeakPoint_mem_Icc
    (N : ℕ) (hN : 2 ≤ N) :
    transformedPeakPoint N ∈ Set.Icc (-1 : ℝ) 1 := by
  let θ : ℝ := Real.pi / (N : ℝ)
  have hθ := chebyshevAngle_pos_lt_pi N hN
  have h2θ : 2 * θ ≤ Real.pi := by
    have hNr : (0 : ℝ) < N := by positivity
    rw [show 2 * θ = 2 * Real.pi / N by
      dsimp [θ]
      field_simp]
    rw [div_le_iff₀ hNr]
    have hNtwo : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.pi_pos]
  have hcosle : Real.cos (2 * θ) ≤ Real.cos θ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hθ.1.le h2θ (by linarith [hθ.1])
  have ha := affineScale_pos N hN
  have hnum : 0 ≤ 1 + Real.cos (2 * θ) := by
    linarith [Real.neg_one_le_cos (2 * θ)]
  have htwoa : 2 * affineScale N = 1 + Real.cos θ := by
    unfold affineScale
    dsimp [θ]
    ring
  change (1 + Real.cos (2 * θ)) / affineScale N - 1 ∈ Set.Icc (-1 : ℝ) 1
  constructor
  · have := div_nonneg hnum ha.le
    linarith
  · rw [sub_le_iff_le_add, show (1 : ℝ) + 1 = 2 by norm_num,
      div_le_iff₀ ha]
    nlinarith

private theorem affineChebyshevArgument_peak (N : ℕ) (hN : 2 ≤ N) :
    affineScale N * (transformedPeakPoint N + 1) - 1 =
      Real.cos (2 * (Real.pi / (N : ℝ))) := by
  have ha : affineScale N ≠ 0 := (affineScale_pos N hN).ne'
  unfold transformedPeakPoint
  field_simp
  ring

private theorem chebyshev_eval_peak (N : ℕ) (hN : 2 ≤ N) :
    (Polynomial.Chebyshev.T ℝ N).eval
      (Real.cos (2 * (Real.pi / (N : ℝ)))) = 1 := by
  rw [Polynomial.Chebyshev.T_real_cos]
  simp only [Int.cast_natCast]
  have hNr : (N : ℝ) ≠ 0 := by positivity
  rw [show (N : ℝ) * (2 * (Real.pi / (N : ℝ))) = 2 * Real.pi by
    field_simp]
  exact Real.cos_two_pi

private theorem transformedChebyshevPolynomial_eval_peak
    (N : ℕ) (hN : 2 ≤ N) :
    (transformedChebyshevPolynomial N).eval (transformedPeakPoint N) =
      2 * transformedScale N := by
  rw [transformedChebyshevPolynomial_eval, affineChebyshevArgument_peak N hN,
    chebyshev_eval_peak N hN]
  ring

private theorem weightedChebyshevConstant_eq_two_mul_transformedScale (N : ℕ) :
    weightedChebyshevConstant N = 2 * transformedScale N := by
  unfold weightedChebyshevConstant transformedScale
  ring

theorem weightedExtremalPolynomial_norm
    (N : ℕ) (hN : 2 ≤ N) :
    weightedPolynomialNorm (weightedExtremalPolynomial N) =
      weightedChebyshevConstant N := by
  let S := weightedExtremalPolynomial N
  let q := transformedChebyshevPolynomial N
  let B : Set ℝ := {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    r = |(1 - x) ^ 2 * S.eval x|}
  have hmul_eval (x : ℝ) :
      (1 - x) ^ 2 * S.eval x = q.eval x := by
    have h := congrArg (fun r : ℝ[X] ↦ r.eval x)
      (transformedChebyshevPolynomial_eq_mul_weightedExtremal N hN)
    simpa [S, q] using h
  have hq_bounds (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      0 ≤ q.eval x ∧ q.eval x ≤ weightedChebyshevConstant N := by
    have h := transformedChebyshevPolynomial_bounds N hN hx
    simpa [q, weightedChebyshevConstant_eq_two_mul_transformedScale] using h
  have hq_peak : q.eval (transformedPeakPoint N) = weightedChebyshevConstant N := by
    rw [show q.eval (transformedPeakPoint N) = 2 * transformedScale N by
      exact transformedChebyshevPolynomial_eval_peak N hN]
    exact (weightedChebyshevConstant_eq_two_mul_transformedScale N).symm
  have hB_nonempty : B.Nonempty := by
    refine ⟨|(1 - 0) ^ 2 * S.eval 0|, 0, ?_, rfl⟩
    constructor <;> norm_num
  have hB_upper : ∀ r ∈ B, r ≤ weightedChebyshevConstant N := by
    rintro r ⟨x, hx, rfl⟩
    rw [hmul_eval, abs_of_nonneg (hq_bounds x hx).1]
    exact (hq_bounds x hx).2
  have hB_bdd : BddAbove B :=
    ⟨weightedChebyshevConstant N, hB_upper⟩
  have hwitness : weightedChebyshevConstant N ∈ B := by
    refine ⟨transformedPeakPoint N, transformedPeakPoint_mem_Icc N hN, ?_⟩
    rw [hmul_eval, hq_peak,
      abs_of_nonneg (weightedChebyshevConstant_nonneg N)]
  change sSup B = weightedChebyshevConstant N
  apply le_antisymm
  · exact csSup_le hB_nonempty hB_upper
  · exact le_csSup hB_bdd hwitness

/-- The sharp constant in Theorem 1.4. -/
def sharpConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 6 / ((n : ℝ) + 2) ^ 2 *
    Real.tan (Real.pi / (2 * (n : ℝ) + 4)) ^ 2

/-- The pointwise formula for `S_n`, with its removable singularity filled. -/
def extremalPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  if x = 1 then
    1
  else
    8 / ((n : ℝ) + 2) ^ 2 *
      Real.tan (Real.pi / (2 * (n : ℝ) + 4)) ^ 2 /
      (1 - x) ^ 2 *
      (1 + chebyshevT (n + 2)
        (((1 + Real.cos (Real.pi / ((n : ℝ) + 2))) / 2) *
          (x + 1) - 1))

theorem sharpConstant_eq_four_mul_weightedChebyshevConstant (n : ℕ) :
    sharpConstant n = 4 * weightedChebyshevConstant (n + 2) := by
  unfold sharpConstant weightedChebyshevConstant
  push_cast
  ring

theorem weightedExtremalPolynomial_eval (n : ℕ) (x : ℝ) :
    (weightedExtremalPolynomial (n + 2)).eval x =
      extremalPolynomial n x := by
  by_cases hx : x = 1
  · subst x
    rw [weightedExtremalPolynomial_eval_one (n + 2) (by omega)]
    simp [extremalPolynomial]
  · rw [extremalPolynomial, if_neg hx]
    have heval := congrArg (fun q : ℝ[X] ↦ q.eval x)
      (transformedChebyshevPolynomial_eq_mul_weightedExtremal
        (n + 2) (by omega))
    simp only [eval_mul, eval_pow, eval_sub, eval_C, eval_X] at heval
    rw [transformedChebyshevPolynomial_eval] at heval
    unfold transformedScale affineScale at heval
    unfold chebyshevT
    push_cast at heval ⊢
    have hden : (1 - x) ^ 2 ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hx))
    field_simp [hden] at heval ⊢
    convert heval using 1 <;> ring

/-! ### Alternation proof of the sharp lower bound and uniqueness -/

private def transformedAlternationNode (N i : ℕ) : ℝ :=
  (Polynomial.Chebyshev.node N (N - i) + 1) / affineScale N - 1

private theorem transformedAlternationNode_affine
    (N i : ℕ) (hN : 2 ≤ N) :
    affineScale N * (transformedAlternationNode N i + 1) - 1 =
      Polynomial.Chebyshev.node N (N - i) := by
  have ha := (affineScale_pos N hN).ne'
  unfold transformedAlternationNode
  field_simp
  ring

private theorem transformedAlternationNode_mem_Icc
    (N : ℕ) (hN : 3 ≤ N) (i : Fin (N - 2 + 1)) :
    transformedAlternationNode N i ∈ Set.Icc (-1 : ℝ) 1 := by
  have hi : (i : ℕ) ≤ N - 2 := by omega
  have hik : 1 < N - (i : ℕ) := by omega
  have hkle : N - (i : ℕ) ≤ N := Nat.sub_le _ _
  have ha := affineScale_pos N (by omega)
  have hnode_mem := Polynomial.Chebyshev.node_mem_Icc
    (n := N) (i := N - (i : ℕ))
  have hnode_lt : Polynomial.Chebyshev.node N (N - (i : ℕ)) <
      Polynomial.Chebyshev.node N 1 :=
    Polynomial.Chebyshev.node_lt hkle hik
  have hnode_one : Polynomial.Chebyshev.node N 1 =
      Real.cos (Real.pi / (N : ℝ)) := by
    simp [Polynomial.Chebyshev.node]
  constructor
  · unfold transformedAlternationNode
    have := hnode_mem.1
    rw [le_sub_iff_add_le]
    norm_num
    exact div_nonneg (by linarith) ha.le
  · unfold transformedAlternationNode
    rw [hnode_one] at hnode_lt
    rw [sub_le_iff_le_add]
    norm_num
    unfold affineScale at ha ⊢
    rw [div_le_iff₀ ha]
    linarith

private theorem transformedAlternationNode_lt_one
    (N : ℕ) (hN : 3 ≤ N) (i : Fin (N - 2 + 1)) :
    transformedAlternationNode N i < 1 := by
  have hi : (i : ℕ) ≤ N - 2 := by omega
  have hik : 1 < N - (i : ℕ) := by omega
  have hkle : N - (i : ℕ) ≤ N := Nat.sub_le _ _
  have hnode_lt : Polynomial.Chebyshev.node N (N - (i : ℕ)) <
      Polynomial.Chebyshev.node N 1 :=
    Polynomial.Chebyshev.node_lt hkle hik
  have hnode_one : Polynomial.Chebyshev.node N 1 =
      Real.cos (Real.pi / (N : ℝ)) := by
    simp [Polynomial.Chebyshev.node]
  have ha := affineScale_pos N (by omega)
  unfold transformedAlternationNode
  rw [hnode_one] at hnode_lt
  rw [sub_lt_iff_lt_add]
  norm_num
  unfold affineScale at ha ⊢
  rw [div_lt_iff₀ ha]
  linarith

private theorem transformedAlternationNode_strictMono
    (N : ℕ) (hN : 3 ≤ N) :
    StrictMono (fun i : Fin (N - 2 + 1) ↦ transformedAlternationNode N i) := by
  intro i j hij
  have hi : (i : ℕ) ≤ N - 2 := by omega
  have hj : (j : ℕ) ≤ N - 2 := by omega
  have hsub : N - (j : ℕ) < N - (i : ℕ) := by omega
  have hkle : N - (i : ℕ) ≤ N := Nat.sub_le _ _
  have hnode : Polynomial.Chebyshev.node N (N - (i : ℕ)) <
      Polynomial.Chebyshev.node N (N - (j : ℕ)) :=
    Polynomial.Chebyshev.node_lt hkle hsub
  have ha := affineScale_pos N (by omega)
  unfold transformedAlternationNode
  apply sub_lt_sub_right
  apply div_lt_div_of_pos_right _ ha
  linarith

private theorem transformedChebyshevPolynomial_eval_alternationNode
    (N : ℕ) (hN : 3 ≤ N) (i : Fin (N - 2 + 1)) :
    (transformedChebyshevPolynomial N).eval (transformedAlternationNode N i) =
      transformedScale N * (1 + (-1 : ℝ) ^ (N - (i : ℕ))) := by
  rw [transformedChebyshevPolynomial_eval,
    transformedAlternationNode_affine N i (by omega),
    Polynomial.Chebyshev.eval_T_real_node]
  simp

private theorem weightedValue_le_norm
    (p : ℝ[X]) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(1 - x) ^ 2 * p.eval x| ≤ weightedPolynomialNorm p := by
  unfold weightedPolynomialNorm
  apply le_csSup
  · let g : ℝ → ℝ := fun y ↦ |(1 - y) ^ 2 * p.eval y|
    have hg : Continuous g := by
      unfold g
      fun_prop
    have hset : {r : ℝ | ∃ y ∈ Set.Icc (-1 : ℝ) 1,
        r = |(1 - y) ^ 2 * p.eval y|} = g '' Set.Icc (-1 : ℝ) 1 := by
      ext r
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [hset]
    exact (isCompact_Icc.image hg).bddAbove
  · exact ⟨x, hx, rfl⟩

private theorem weightedUniqueness_core
    (N : ℕ)
    (hN : 3 ≤ N)
    (p S : ℝ[X])
    (hpdeg : p.natDegree ≤ N - 2)
    (hSdeg : S.natDegree ≤ N - 2)
    (hpnonneg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x)
    (hpone : p.eval 1 = 1)
    (hSone : S.eval 1 = 1)
    (hSq : (C 1 - X) ^ 2 * S = transformedChebyshevPolynomial N)
    (hnorm : weightedPolynomialNorm p ≤ weightedChebyshevConstant N) :
    p = S := by
  let d : ℝ[X] := p - S
  let r : ℝ[X] := d /ₘ (X - C 1)
  have hdroot : d.IsRoot 1 := by
    simp [d, IsRoot, hpone, hSone]
  have hfactor : (X - C 1) * r = d := by
    exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hdroot
  have hddeg : d.natDegree ≤ N - 2 := by
    exact (natDegree_sub_le p S).trans (max_le hpdeg hSdeg)
  have hrdeg : r.natDegree < N - 2 := by
    dsimp [r]
    rw [natDegree_divByMonic _ (monic_X_sub_C 1), natDegree_X_sub_C]
    omega
  let s : ℝ[X] := ((-1 : ℝ) ^ N) • r
  have hsdeg : s.natDegree < N - 2 :=
    (natDegree_smul_le ((-1 : ℝ) ^ N) r).trans_lt hrdeg
  have halt_r (i : Fin (N - 2 + 1)) :
      0 ≤ (-1 : ℝ) ^ (N - (i : ℕ)) *
        r.eval (transformedAlternationNode N i) := by
    let x := transformedAlternationNode N i
    let k := N - (i : ℕ)
    have hx : x ∈ Set.Icc (-1 : ℝ) 1 := transformedAlternationNode_mem_Icc N hN i
    have hxlt : x < 1 := transformedAlternationNode_lt_one N hN i
    have hpositive : 0 < (1 - x) ^ 3 := by positivity
    have hpweight_nonneg : 0 ≤ (1 - x) ^ 2 * p.eval x :=
      mul_nonneg (sq_nonneg _) (hpnonneg x hx)
    have hpweight_abs : |(1 - x) ^ 2 * p.eval x| ≤
        weightedPolynomialNorm p := weightedValue_le_norm p x hx
    have hpweight_le : (1 - x) ^ 2 * p.eval x ≤ 2 * transformedScale N := by
      calc
        (1 - x) ^ 2 * p.eval x ≤ |(1 - x) ^ 2 * p.eval x| := le_abs_self _
        _ ≤ weightedPolynomialNorm p := hpweight_abs
        _ ≤ weightedChebyshevConstant N := hnorm
        _ = 2 * transformedScale N := weightedChebyshevConstant_eq_two_mul_transformedScale N
    have hqeval : (transformedChebyshevPolynomial N).eval x =
        transformedScale N * (1 + (-1 : ℝ) ^ k) := by
      simpa [x, k] using transformedChebyshevPolynomial_eval_alternationNode N hN i
    have hSeval : (1 - x) ^ 2 * S.eval x =
        (transformedChebyshevPolynomial N).eval x := by
      have heval := congrArg (fun q : ℝ[X] ↦ q.eval x) hSq
      simpa [eval_mul] using heval
    have hdeval : p.eval x - S.eval x = (x - 1) * r.eval x := by
      have heval := congrArg (fun q : ℝ[X] ↦ q.eval x) hfactor
      simpa [d, eval_mul] using heval.symm
    have hdiff : (1 - x) ^ 2 * p.eval x -
        (transformedChebyshevPolynomial N).eval x =
        -(1 - x) ^ 3 * r.eval x := by
      rw [← hSeval, ← mul_sub, hdeval]
      ring
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow]
      have hq : (transformedChebyshevPolynomial N).eval x =
          2 * transformedScale N := by
        rw [hqeval, hk.neg_one_pow]
        ring
      have hprod : 0 ≤ (1 - x) ^ 3 * r.eval x := by
        rw [hq] at hdiff
        linarith
      simpa using (mul_nonneg_iff_of_pos_left hpositive).mp hprod
    · rw [hk.neg_one_pow]
      have hq : (transformedChebyshevPolynomial N).eval x = 0 := by
        rw [hqeval, hk.neg_one_pow]
        ring
      have hprod : 0 ≤ (1 - x) ^ 3 * (-r.eval x) := by
        rw [hq] at hdiff
        nlinarith
      have := (mul_nonneg_iff_of_pos_left hpositive).mp hprod
      linarith
  have halt_s (i : Fin (N - 2 + 1)) :
      0 ≤ (-1 : ℝ) ^ (i : ℕ) * s.eval (transformedAlternationNode N i) := by
    have hi : (i : ℕ) ≤ N := by omega
    have hNi : N - (i : ℕ) + (i : ℕ) = N := Nat.sub_add_cancel hi
    have h := halt_r i
    dsimp [s]
    rw [eval_smul, smul_eq_mul]
    have hpow : (-1 : ℝ) ^ N =
        (-1 : ℝ) ^ (N - (i : ℕ)) * (-1 : ℝ) ^ (i : ℕ) := by
      rw [← pow_add, hNi]
    calc
      0 ≤ (-1 : ℝ) ^ (N - (i : ℕ)) *
          r.eval (transformedAlternationNode N i) := h
      _ = (-1 : ℝ) ^ (i : ℕ) *
          ((-1 : ℝ) ^ N * r.eval (transformedAlternationNode N i)) := by
        rw [hpow]
        have hsquare : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 := by
          rw [← mul_pow]
          norm_num
        symm
        calc
          (-1 : ℝ) ^ (i : ℕ) *
              ((-1 : ℝ) ^ (N - (i : ℕ)) * (-1 : ℝ) ^ (i : ℕ) *
                r.eval (transformedAlternationNode N i)) =
              ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) *
                ((-1 : ℝ) ^ (N - (i : ℕ)) *
                  r.eval (transformedAlternationNode N i)) := by ring
          _ = (-1 : ℝ) ^ (N - (i : ℕ)) *
              r.eval (transformedAlternationNode N i) := by rw [hsquare, one_mul]
  have hs_zero : s = 0 := polynomial_eq_zero_of_alternating_signs
    (m := N - 2) (by omega) hsdeg
      (transformedAlternationNode_strictMono N hN) halt_s
  have hr_zero : r = 0 := by
    have hscalar : ((-1 : ℝ) ^ N) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (smul_eq_zero.mp hs_zero).resolve_left hscalar
  have hd_zero : d = 0 := by rw [← hfactor, hr_zero, mul_zero]
  exact sub_eq_zero.mp hd_zero

private theorem polynomial_eq_one_of_natDegree_le_zero
    (p : ℝ[X]) (hdeg : p.natDegree ≤ 0) (hone : p.eval 1 = 1) :
    p = 1 := by
  rw [eq_C_of_natDegree_le_zero hdeg]
  have h := hone
  rw [eq_C_of_natDegree_le_zero hdeg] at h
  simp only [eval_C] at h
  rw [h]
  simp

private theorem weightedUniqueness
    (N : ℕ)
    (hN : 2 ≤ N)
    (p : ℝ[X])
    (hpdeg : p.natDegree ≤ N - 2)
    (hpnonneg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x)
    (hpone : p.eval 1 = 1)
    (hnorm : weightedPolynomialNorm p ≤ weightedChebyshevConstant N) :
    p = weightedExtremalPolynomial N := by
  by_cases hNtwo : N = 2
  · subst N
    have hp : p = 1 := polynomial_eq_one_of_natDegree_le_zero p
      (by simpa using hpdeg) hpone
    have hS : weightedExtremalPolynomial 2 = 1 :=
      polynomial_eq_one_of_natDegree_le_zero (weightedExtremalPolynomial 2)
        (by simpa using weightedExtremalPolynomial_natDegree_le 2 (by omega))
        (weightedExtremalPolynomial_eval_one 2 (by omega))
    rw [hp, hS]
  · exact weightedUniqueness_core N (by omega) p (weightedExtremalPolynomial N)
      hpdeg (weightedExtremalPolynomial_natDegree_le N hN) hpnonneg hpone
      (weightedExtremalPolynomial_eval_one N hN)
      (transformedChebyshevPolynomial_eq_mul_weightedExtremal N hN) hnorm

/-- Proposition 1.6, sharp inequality. -/
theorem weightedPolynomialNorm_ge
    (N : ℕ)
    (hN : 2 ≤ N)
    (p : ℝ[X])
    (hdeg : p.natDegree ≤ N - 2)
    (hnonneg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x)
    (hone : p.eval 1 = 1) :
    weightedChebyshevConstant N ≤ weightedPolynomialNorm p := by
  by_contra hnot
  have hlt : weightedPolynomialNorm p < weightedChebyshevConstant N := lt_of_not_ge hnot
  have heq := weightedUniqueness N hN p hdeg hnonneg hone hlt.le
  rw [heq, weightedExtremalPolynomial_norm N hN] at hlt
  exact lt_irrefl _ hlt

/-- Proposition 1.6, uniqueness of the equality case. -/
theorem weightedPolynomialNorm_eq_iff
    (N : ℕ)
    (hN : 2 ≤ N)
    (p : ℝ[X])
    (hdeg : p.natDegree ≤ N - 2)
    (hnonneg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x)
    (hone : p.eval 1 = 1) :
    weightedPolynomialNorm p = weightedChebyshevConstant N ↔
      p = weightedExtremalPolynomial N := by
  constructor
  · intro hnorm
    exact weightedUniqueness N hN p hdeg hnonneg hone hnorm.le
  · rintro rfl
    exact weightedExtremalPolynomial_norm N hN


end JoseSmoothest
