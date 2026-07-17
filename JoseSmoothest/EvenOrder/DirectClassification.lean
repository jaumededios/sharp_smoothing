import JoseSmoothest.EvenOrder
import JoseSmoothest.EvenOrder.EndpointPhase

/-!
# Direct classification of the arbitrary-even-order extremizer

This file identifies the intrinsic weighted peak with the endpoint
coefficient of the squarefree Pell weight extracted from the canonical
minimizer and packages its exact direct real-phase classification.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

namespace EvenWeightedExtremalData

variable {m N : ℕ} (E : EvenWeightedExtremalData m N)

/-- The endpoint alternant attached to an extremal datum. -/
def extractedAlternant (hm : 1 ≤ m) (hN : m ≤ N) :
    EndpointAlternant m N E.normalizedAlternant :=
  E.endpointAlternant hm hN

/-- The minimal-genus endpoint-contact package extracted from an extremal
datum. -/
def extractedContactData (hm : 1 ≤ m) (hN : m ≤ N) :
    EndpointContactData m N :=
  (E.extractedAlternant hm hN).contactData

/-- The endpoint normalization scale is exactly half of the weighted peak. -/
theorem extractedEndpointScale_eq
    (hm : 1 ≤ m) (hN : m ≤ N) :
    (E.extractedContactData hm hN).endpointScale = E.M / 2 := by
  let d := E.extractedContactData hm hN
  have hM : E.M ≠ 0 := ne_of_gt (E.M_pos hm hN)
  have hfactor :
      (C (1 : ℝ) - X) ^ m * d.endpointQuotient =
        (C (1 : ℝ) - X) ^ m *
          (C d.endpointScale * C (2 / E.M) * E.S) := by
    calc
      (C (1 : ℝ) - X) ^ m * d.endpointQuotient =
          d.endpointNumerator := d.endpoint_factorization
      _ = C d.endpointScale * (1 - E.normalizedAlternant) := rfl
      _ = C d.endpointScale *
          (C (2 / E.M) * ((C (1 : ℝ) - X) ^ m * E.S)) := by
            rw [normalizedAlternant, ← E.factorization]
            simp only [evenWeightedNumerator]
            ring
      _ = (C (1 : ℝ) - X) ^ m *
          (C d.endpointScale * C (2 / E.M) * E.S) := by ring
  have hcancel : d.endpointQuotient =
      C d.endpointScale * C (2 / E.M) * E.S :=
    mul_left_cancel₀
      (pow_ne_zero _ (sub_ne_zero.mpr (X_ne_C (1 : ℝ)).symm)) hfactor
  have heval := congrArg (eval (1 : ℝ)) hcancel
  simp only [d.endpointQuotient_eval_one, eval_mul, eval_C,
    E.admissible.eval_one] at heval
  apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  field_simp at heval
  nlinarith

/-- The intrinsic peak is the endpoint coefficient of the extracted
squarefree Pell weight. -/
theorem M_eq_endpointDValue
    (hm : 1 ≤ m) (hN : m ≤ N) :
    E.M =
      (-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 *
        (E.extractedContactData hm hN).endpointDValue /
          (N : ℝ) ^ 2 := by
  let d := E.extractedContactData hm hN
  have hscale := E.extractedEndpointScale_eq hm hN
  change d.endpointScale = E.M / 2 at hscale
  rw [EndpointContactData.endpointScale] at hscale
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  field_simp [hN0] at hscale ⊢
  nlinarith

end EvenWeightedExtremalData

/-- The extracted endpoint alternant for the canonical weighted minimizer. -/
def smoothestEvenOrderAlternant (m n : ℕ) (hm : 1 ≤ m) :
    EndpointAlternant m (n + m)
      (canonicalEvenWeightedExtremalData m n hm).normalizedAlternant :=
  (canonicalEvenWeightedExtremalData m n hm).extractedAlternant hm (by omega)

/-- The canonical direct phase classifying the order `2m` minimizer. -/
def smoothestEvenOrderPhase (m n : ℕ) (hm : 1 ≤ m) (x : ℝ) : ℝ :=
  (smoothestEvenOrderAlternant m n hm).phase x

/-- The normalized canonical extremizer is the cosine of its strictly
increasing direct Pell phase. -/
theorem smoothestEvenOrder_cosine_classification
    (m n : ℕ) (hm : 1 ≤ m)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (canonicalEvenWeightedExtremalData m n hm).normalizedAlternant.eval x =
      (smoothestEvenOrderAlternant m n hm).orientation *
        Real.cos (((n + m : ℕ) : ℝ) *
          smoothestEvenOrderPhase m n hm x) := by
  exact (smoothestEvenOrderAlternant m n hm).eval_eq_cos_phase hx

/-- The canonical phase makes exactly `n + 1` half-turns across `[-1,1]`. -/
theorem smoothestEvenOrder_phaseLength
    (m n : ℕ) (hm : 1 ≤ m) :
    ((n + m : ℕ) : ℝ) * smoothestEvenOrderPhase m n hm 1 =
      (n + 1 : ℕ) * Real.pi := by
  have h := (smoothestEvenOrderAlternant m n hm).phaseLength
  simpa only [smoothestEvenOrderPhase, Nat.add_sub_cancel_right] using h

/-- The canonical weighted peak is the endpoint coefficient of its extracted
squarefree Pell weight. -/
theorem canonicalEvenWeightedPeak_eq_endpointDValue
    (m n : ℕ) (hm : 1 ≤ m) :
    (canonicalEvenWeightedExtremalData m n hm).M =
      (-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 *
        ((smoothestEvenOrderAlternant m n hm).contactData.endpointDValue) /
          ((n + m : ℕ) : ℝ) ^ 2 := by
  exact (canonicalEvenWeightedExtremalData m n hm).M_eq_endpointDValue hm (by omega)

/-- Endpoint-coefficient formula for the sharp order-`2m` difference
constant. -/
theorem sharpEvenDifferenceConstant_eq_endpointDValue
    (m n : ℕ) (hm : 1 ≤ m) :
    sharpEvenDifferenceConstant m n hm =
      2 ^ m *
        ((-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 *
          ((smoothestEvenOrderAlternant m n hm).contactData.endpointDValue) /
            ((n + m : ℕ) : ℝ) ^ 2) := by
  rw [sharpEvenDifferenceConstant,
    canonicalEvenWeightedPeak_eq_endpointDValue]

end JoseSmoothest
