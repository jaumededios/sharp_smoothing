# Blueprint for `JoseSmoothest/EvenOrder/DirectClassification.lean`

## Purpose

This file packages the direct real-phase classification for the canonical
even-order smoothing extremizer.  It identifies the endpoint coefficient of
the extracted squarefree Pell weight with the intrinsic minimax peak and
therefore gives an exact endpoint formula for the sharp operator constant.

Unlike the optional Abelian construction blueprints, this theorem is
unconditional: its Pell data are extracted from the already proved canonical
minimizer.

## Imports

```lean
import JoseSmoothest.EvenOrder
import JoseSmoothest.EvenOrder.EndpointPhase
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

namespace EvenWeightedExtremalData

variable {m N : ℕ} (E : EvenWeightedExtremalData m N)

/-- The endpoint alternant attached to an extremal datum. -/
def extractedAlternant (hm : 1 ≤ m) (hN : m ≤ N) :
    EndpointAlternant m N E.normalizedAlternant :=
  E.endpointAlternant hm hN

/-- Its minimal-genus endpoint-contact package. -/
def extractedContactData (hm : 1 ≤ m) (hN : m ≤ N) :
    EndpointContactData m N :=
  (E.extractedAlternant hm hN).contactData

theorem extractedEndpointScale_eq
    (hm : 1 ≤ m) (hN : m ≤ N) :
    (E.extractedContactData hm hN).endpointScale = E.M / 2

theorem M_eq_endpointDValue
    (hm : 1 ≤ m) (hN : m ≤ N) :
    E.M =
      (-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 *
        (E.extractedContactData hm hN).endpointDValue /
          (N : ℝ) ^ 2

end EvenWeightedExtremalData

/-- The extracted endpoint alternant for the canonical weighted minimizer. -/
def smoothestEvenOrderAlternant (m n : ℕ) (hm : 1 ≤ m) :
    EndpointAlternant m (n + m)
      (canonicalEvenWeightedExtremalData m n hm).normalizedAlternant :=
  (canonicalEvenWeightedExtremalData m n hm).extractedAlternant hm (by omega)

/-- The canonical direct phase classifying the order `2m` minimizer. -/
def smoothestEvenOrderPhase (m n : ℕ) (hm : 1 ≤ m) (x : ℝ) : ℝ :=
  (smoothestEvenOrderAlternant m n hm).phase x

theorem smoothestEvenOrder_cosine_classification
    (m n : ℕ) (hm : 1 ≤ m)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (canonicalEvenWeightedExtremalData m n hm).normalizedAlternant.eval x =
      (smoothestEvenOrderAlternant m n hm).orientation *
        Real.cos (((n + m : ℕ) : ℝ) *
          smoothestEvenOrderPhase m n hm x)

theorem smoothestEvenOrder_phaseLength
    (m n : ℕ) (hm : 1 ≤ m) :
    ((n + m : ℕ) : ℝ) * smoothestEvenOrderPhase m n hm 1 =
      (n + 1 : ℕ) * Real.pi

theorem canonicalEvenWeightedPeak_eq_endpointDValue
    (m n : ℕ) (hm : 1 ≤ m) :
    (canonicalEvenWeightedExtremalData m n hm).M =
      (-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 *
        ((smoothestEvenOrderAlternant m n hm).contactData.endpointDValue) /
          ((n + m : ℕ) : ℝ) ^ 2

theorem sharpEvenDifferenceConstant_eq_endpointDValue
    (m n : ℕ) (hm : 1 ≤ m) :
    sharpEvenDifferenceConstant m n hm =
      2 ^ m *
        ((-1 : ℝ) ^ (m + 1) * (m : ℝ) ^ 2 *
          ((smoothestEvenOrderAlternant m n hm).contactData.endpointDValue) /
            ((n + m : ℕ) : ℝ) ^ 2)

end JoseSmoothest
```

## Detailed natural-language proof blueprint

### Identifying the endpoint scale

For an extremal datum, by definition of the normalized alternant,

```text
1 - Z = (2/M) q,
q = (1-X)^m S,
S(1)=1.
```

The endpoint-contact package forms
`endpointNumerator = endpointScale * (1-Z)`, divides out `(1-X)^m`, and
proves that the resulting quotient evaluates to one at `1`.  Substitute the
two displayed factorizations, cancel the nonzero polynomial `(1-X)^m`, and
evaluate at one.  The result is

```text
endpointScale * (2/M) = 1.
```

The peak `M` is strictly positive, so division is legitimate and
`endpointScale=M/2`.

By the already proved definition and nonvanishing theorem for endpoint scale,

```text
endpointScale =
  (-1)^(m+1) m² endpointDValue / (2 N²).
```

Equating the two expressions and multiplying by two gives the endpoint
formula for `M`.

### Canonical classification

Instantiate the preceding algebra and `EndpointPhase` with
`canonicalEvenWeightedExtremalData m n`, whose polynomial degree is
`N=n+m`.  The general cosine theorem gives the pointwise classification on
`[-1,1]`.  The endpoint phase theorem gives

```text
(n+m) phase(1) = ((n+m)-m+1) π = (n+1) π.
```

Finally, the Fourier reduction already identifies the sharp iterated
difference constant with `2^m M`.  Substitute the endpoint formula for `M`.
This yields an unconditional exact formula in terms of the endpoint value of
the squarefree Pell weight extracted from the actual optimizer.

### Regression cases

- `m=N=1`: `Z=X`, `Q=1`, `D=X²-1`, the phase length is `π`, `M=2`, and
  the sharp constant is `4`.
- `m=N`: there are only the two endpoint nodes, so the phase makes exactly
  one half-turn.
- odd `m`: `endpointDValue=D'(1)>0`.
- even `m`: `endpointDValue=D(1)<0`; the factor `(-1)^(m+1)` makes the peak
  positive in both parities.
