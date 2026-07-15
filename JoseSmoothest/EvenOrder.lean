import JoseSmoothest.EvenOrder.Equioscillation
import JoseSmoothest.EvenOrder.FourierReduction

/-!
# The smoothest kernel for an arbitrary even difference order

This file transports the unconditional weighted-polynomial minimizer back to
the kernel problem.  The resulting sharp constant is defined intrinsically;
its later Pell--Abel description is logically downstream from this theorem.
-/

noncomputable section

namespace JoseSmoothest

open Polynomial

/-- A chosen certified minimizer for the weighted problem of total degree
`n + m`.  Uniqueness makes its polynomial independent of this choice. -/
def canonicalEvenWeightedExtremalData
    (m n : ℕ) (hm : 1 ≤ m) :
    EvenWeightedExtremalData m (n + m) :=
  Classical.choice
    (exists_evenWeightedExtremalData m (n + m) hm (by omega))

/-- The intrinsic sharp constant for the difference of order `2 * m`. -/
def sharpEvenDifferenceConstant
    (m n : ℕ) (hm : 1 ≤ m) : ℝ :=
  (2 : ℝ) ^ m * (canonicalEvenWeightedExtremalData m n hm).M

/-- The kernel reconstructed from the unique weighted minimizer. -/
def smoothestEvenOrderKernel
    (m n : ℕ) (hm : 1 ≤ m) : Kernel :=
  kernelOfPolynomial n (canonicalEvenWeightedExtremalData m n hm).S

/-- Reconstructing the chosen minimizer as a kernel preserves its polynomial
symbol. -/
theorem kernelPolynomial_smoothestEvenOrderKernel
    (m n : ℕ) (hm : 1 ≤ m) :
    kernelPolynomial n (smoothestEvenOrderKernel m n hm) =
      (canonicalEvenWeightedExtremalData m n hm).S := by
  apply kernelPolynomial_kernelOfPolynomial
  simpa using
    (canonicalEvenWeightedExtremalData m n hm).admissible.degree_le

/-- The reconstructed minimizer satisfies the kernel support, symmetry,
normalization, and Fourier-positivity conditions. -/
theorem smoothestEvenOrderKernel_isAdmissible
    (m n : ℕ) (hm : 1 ≤ m) :
    IsAdmissibleKernel n (smoothestEvenOrderKernel m n hm) := by
  let E := canonicalEvenWeightedExtremalData m n hm
  apply kernelOfPolynomial_isAdmissible
  · simpa [E] using E.admissible.degree_le
  · exact E.admissible.nonnegative
  · exact E.admissible.eval_one

/-- The canonical kernel attains the intrinsic sharp constant. -/
theorem smoothestEvenOrderKernel_attains
    (m n : ℕ) (hm : 1 ≤ m) :
    differenceSmoothness (2 * m) (smoothestEvenOrderKernel m n hm) =
      sharpEvenDifferenceConstant m n hm := by
  let E := canonicalEvenWeightedExtremalData m n hm
  let u := smoothestEvenOrderKernel m n hm
  have hu := smoothestEvenOrderKernel_isAdmissible m n hm
  rw [differenceSmoothness_two_mul_eq_pow_mul_evenWeightedPolynomialNorm
    m n u hu.support hu.symmetric]
  rw [kernelPolynomial_smoothestEvenOrderKernel m n hm]
  exact congrArg ((2 : ℝ) ^ m * ·) E.norm_eq

/-- Every admissible kernel has even-order smoothness at least the intrinsic
sharp constant. -/
theorem evenOrderSmoothness_ge
    (m n : ℕ) (hm : 1 ≤ m)
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    sharpEvenDifferenceConstant m n hm ≤
      differenceSmoothness (2 * m) u := by
  let E := canonicalEvenWeightedExtremalData m n hm
  have hweighted : E.M ≤
      evenWeightedPolynomialNorm m (kernelPolynomial n u) :=
    evenWeightedPolynomialNorm_ge_of_certificate m (n + m) (by omega)
      hu.evenWeightedKernelPolynomial E.admissible E.factorization E.certificate
  rw [sharpEvenDifferenceConstant,
    differenceSmoothness_two_mul_eq_pow_mul_evenWeightedPolynomialNorm
      m n u hu.support hu.symmetric]
  exact mul_le_mul_of_nonneg_left hweighted (by positivity)

/-- Equality holds precisely when the kernel polynomial is the unique
weighted minimizer. -/
theorem evenOrderSmoothness_eq_iff_kernelPolynomial_eq
    (m n : ℕ) (hm : 1 ≤ m)
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    differenceSmoothness (2 * m) u = sharpEvenDifferenceConstant m n hm ↔
      kernelPolynomial n u =
        (canonicalEvenWeightedExtremalData m n hm).S := by
  let E := canonicalEvenWeightedExtremalData m n hm
  have hcertificate := evenWeightedPolynomialNorm_eq_iff_of_certificate
    m (n + m) (by omega) hu.evenWeightedKernelPolynomial E.admissible
      E.factorization E.certificate
  rw [differenceSmoothness_two_mul_eq_pow_mul_evenWeightedPolynomialNorm
    m n u hu.support hu.symmetric, sharpEvenDifferenceConstant]
  constructor
  · intro h
    apply hcertificate.mp
    have hpow : 0 < (2 : ℝ) ^ m := by positivity
    nlinarith
  · intro h
    have hnorm := hcertificate.mpr h
    rw [hnorm]

/-- Equality holds precisely at the canonical kernel itself. -/
theorem evenOrderSmoothness_eq_iff_eq_smoothestKernel
    (m n : ℕ) (hm : 1 ≤ m)
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    differenceSmoothness (2 * m) u = sharpEvenDifferenceConstant m n hm ↔
      u = smoothestEvenOrderKernel m n hm := by
  rw [evenOrderSmoothness_eq_iff_kernelPolynomial_eq m n hm u hu]
  constructor
  · intro hpolynomial
    let v := smoothestEvenOrderKernel m n hm
    have hv := smoothestEvenOrderKernel_isAdmissible m n hm
    apply kernel_eq_of_kernelPolynomial_eq n hu.support hu.symmetric
      hv.support hv.symmetric
    exact hpolynomial.trans
      (kernelPolynomial_smoothestEvenOrderKernel m n hm).symm
  · rintro rfl
    exact kernelPolynomial_smoothestEvenOrderKernel m n hm

/-- For every positive half-order, there is a unique admissible kernel which
attains the sharp even-order smoothness constant. -/
theorem existsUnique_smoothestEvenOrderKernel
    (m n : ℕ) (hm : 1 ≤ m) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧
        differenceSmoothness (2 * m) u =
          sharpEvenDifferenceConstant m n hm := by
  refine ⟨smoothestEvenOrderKernel m n hm,
    ⟨smoothestEvenOrderKernel_isAdmissible m n hm,
      smoothestEvenOrderKernel_attains m n hm⟩, ?_⟩
  intro u hu
  exact (evenOrderSmoothness_eq_iff_eq_smoothestKernel
    m n hm u hu.1).mp hu.2

end JoseSmoothest
