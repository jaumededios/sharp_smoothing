# Blueprint for `JoseSmoothest/EvenOrder.lean`

## Purpose

This is the unconditional arbitrary-even-order smoothing theorem.  It transports the
unconditional weighted minimizer through the Chebyshev kernel equivalence,
proves the sharp lower bound and unique equality case for every difference
order `2*m` with `m≥1`.  The sharp constant is unconditional even when no
closed theta formula for it is available.  The optional special-function
forward construction lives downstream in `EvenOrder/Classification.lean`.
The implemented direct real-phase classification lives downstream in
`EvenOrder/DirectClassification.lean`; neither branch is needed by this main
existence and uniqueness theorem.

## Imports

```lean
import JoseSmoothest.EvenOrder.Equioscillation
import JoseSmoothest.EvenOrder.FourierReduction
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

def canonicalEvenWeightedExtremalData
    (m n : ℕ) (hm : 1 ≤ m) :
    EvenWeightedExtremalData m (n + m) :=
  Classical.choice (exists_evenWeightedExtremalData m (n + m) hm (by omega))

def sharpEvenDifferenceConstant
    (m n : ℕ) (hm : 1 ≤ m) : ℝ :=
  (2 : ℝ) ^ m * (canonicalEvenWeightedExtremalData m n hm).M

def smoothestEvenOrderKernel
    (m n : ℕ) (hm : 1 ≤ m) : Kernel :=
  kernelOfPolynomial n (canonicalEvenWeightedExtremalData m n hm).S

theorem kernelPolynomial_smoothestEvenOrderKernel
    (m n : ℕ) (hm : 1 ≤ m) :
    kernelPolynomial n (smoothestEvenOrderKernel m n hm) =
      (canonicalEvenWeightedExtremalData m n hm).S

theorem smoothestEvenOrderKernel_isAdmissible
    (m n : ℕ) (hm : 1 ≤ m) :
    IsAdmissibleKernel n (smoothestEvenOrderKernel m n hm)

theorem smoothestEvenOrderKernel_attains
    (m n : ℕ) (hm : 1 ≤ m) :
    differenceSmoothness (2 * m) (smoothestEvenOrderKernel m n hm) =
      sharpEvenDifferenceConstant m n hm

theorem evenOrderSmoothness_ge
    (m n : ℕ) (hm : 1 ≤ m)
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    sharpEvenDifferenceConstant m n hm ≤
      differenceSmoothness (2 * m) u

theorem evenOrderSmoothness_eq_iff_kernelPolynomial_eq
    (m n : ℕ) (hm : 1 ≤ m)
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    differenceSmoothness (2 * m) u = sharpEvenDifferenceConstant m n hm ↔
      kernelPolynomial n u =
        (canonicalEvenWeightedExtremalData m n hm).S

theorem evenOrderSmoothness_eq_iff_eq_smoothestKernel
    (m n : ℕ) (hm : 1 ≤ m)
    (u : Kernel) (hu : IsAdmissibleKernel n u) :
    differenceSmoothness (2 * m) u = sharpEvenDifferenceConstant m n hm ↔
      u = smoothestEvenOrderKernel m n hm

theorem existsUnique_smoothestEvenOrderKernel
    (m n : ℕ) (hm : 1 ≤ m) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧
        differenceSmoothness (2 * m) u = sharpEvenDifferenceConstant m n hm

end JoseSmoothest
```

## Detailed natural-language proof blueprint

### Fourier-to-polynomial identity

`FourierReduction` supplies the exact factor `2^m` and transports kernel
admissibility to weighted-polynomial admissibility at `N=n+m`.

### Canonical minimizer and kernel

`Equioscillation` proves that extremal data exist, so classical choice fixes
one package.  Its polynomial is in fact independent of the choice because
the minimizer is unique.  Reconstruct a kernel from its Chebyshev
coefficients.  The inverse Chebyshev theorem identifies the reconstructed
kernel polynomial with the chosen minimizer, and transfers degree,
nonnegativity, and normalization to kernel admissibility.

The Fourier-to-polynomial identity and the certified norm compute the
attained value as `2^m M`.  Applying the generic polynomial lower bound to
the kernel polynomial of any admissible kernel proves sharpness.  Equality
forces equality of kernel polynomials, and supported symmetric kernels are
determined by those polynomials.  This proves the unique equality case.

The downstream `Classification` module applies curve extraction to this
already existing minimizer.  Keeping that import downstream is the formal
expression of the proof's logical independence from special functions.
