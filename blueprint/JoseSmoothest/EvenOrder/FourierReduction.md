# Blueprint for `JoseSmoothest/EvenOrder/FourierReduction.lean`

## Purpose

This module performs the order-independent passage from an even difference
of order `2*m` to the weighted polynomial norm.  It contains no extremal or
special-function argument.

## Imports

```lean
import JoseSmoothest.EvenOrder.WeightedMinimax
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

theorem IsAdmissibleKernel.evenWeightedKernelPolynomial
    {m n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    IsAdmissibleEvenWeightedPolynomial m (n + m)
      (kernelPolynomial n u)

theorem differenceSmoothness_two_mul_eq_pow_mul_evenWeightedPolynomialNorm
    (m n : ℕ) (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    differenceSmoothness (2 * m) u =
      (2 : ℝ) ^ m *
        evenWeightedPolynomialNorm m (kernelPolynomial n u)

end JoseSmoothest
```

## Detailed natural-language proof blueprint

An admissible kernel has kernel-polynomial degree at most `n`, is
nonnegative on `[-1,1]`, and has value one at one.  Since
`(n+m)-m=n`, these are exactly the fields of generic weighted
admissibility.

For a supported symmetric kernel, its Fourier transform at `ξ` is the
kernel polynomial at `cos ξ`.  The generic multiplier theorem gives

```text
differenceMultiplier (2m) u ξ
  = [2(1-cos ξ)]^m |kernelPolynomial(cos ξ)|.
```

Because `1-cos ξ≥0`, this is `2^m` times the weighted polynomial
value.  Cosine maps the real line into `[-1,1]`; conversely, for every
`x∈[-1,1]`, `cos(arccos x)=x`.  Compare the two nonempty bounded ranges in
both directions using `csSup`.  Multiplication by the positive scalar `2^m`
then gives the exact identity.
