# Blueprint for `JoseSmoothest/EvenOrder/Classification.lean`

## Purpose

This optional downstream module classifies the canonical arbitrary-even
minimizer by its minimal-genus Pell--Abel curve, normalized differential,
quantized periods, and real phase.  It contains no part of the unconditional
sharp-bound proof in `EvenOrder.lean`.

## Imports

```lean
import JoseSmoothest.EvenOrder
import JoseSmoothest.EvenOrder.CurveExtraction
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

def smoothestEvenOrderAbelianData
    (m n : ℕ) (hm : 1 ≤ m) : EndpointAbelianData m (n + m) :=
  (canonicalEvenWeightedExtremalData m n hm).extractedEndpointAbelianData
    hm (by omega)

theorem smoothestEvenOrder_minimal_genus
    (m n : ℕ) (hm : 1 ≤ m) :
    (smoothestEvenOrderAbelianData m n hm).contact.D.natDegree =
      2 * endpointGenus m + 2

theorem smoothestEvenOrder_endpointNumerator
    (m n : ℕ) (hm : 1 ≤ m) :
    (smoothestEvenOrderAbelianData m n hm).contact.curve.thirdKindNumerator =
      (Polynomial.X - Polynomial.C 1) ^ endpointGenus m

theorem smoothestEvenOrder_hasDegreePeriods
    (m n : ℕ) (hm : 1 ≤ m) :
    (smoothestEvenOrderAbelianData m n hm).contact.curve.HasDegreeNPeriods
      (n + m)

theorem smoothestEvenOrder_phaseLength
    (m n : ℕ) (hm : 1 ≤ m) :
    (smoothestEvenOrderAbelianData m n hm).phaseInterval.HasLength
      (n + m) (n + 1)

theorem sharpEvenDifferenceConstant_eq_endpointDValue
    (m n : ℕ) (hm : 1 ≤ m) :
    sharpEvenDifferenceConstant m n hm =
      (2 : ℝ) ^ m * (-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 *
        (smoothestEvenOrderAbelianData m n hm).contact.endpointDValue /
          ((n + m : ℕ) : ℝ) ^ 2

end JoseSmoothest
```

## Detailed natural-language proof blueprint

Apply `CurveExtraction` to the canonical extremal package chosen in
`EvenOrder`.  It retains that package's normalized alternant as the Pell
solution, so no uniqueness comparison with an analytic construction is
needed.  The extracted curve has degree `2*endpointGenus m+2`, its normalized
third-kind numerator is `(X-1)^endpointGenus m`, and the reverse Pell theorem
gives degree-`n+m` period quantization.

The general phase-length formula is `N-m+1`.  Substituting `N=n+m` reduces it
to `n+1`, which says that the extremal polynomial makes exactly one half-turn
per zero--peak interval of the kernel problem.

Curve extraction also proves that the Abelian certificate's peak is the same
`M` used in the intrinsic definition of `sharpEvenDifferenceConstant`.
Substitute the certificate's endpoint-scale formula and `N=n+m` to obtain
the displayed endpoint-curve expression.

For `m=3` these data recover the existing genus-one Zolotarev certificate and
constant.  For `m=4` they give the eighth-difference problem on the same
genus-one level but with even endpoint parity.  These are the two mandatory
regression cases before implementing genus two.
