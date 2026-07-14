# Internal Lean Library

The internal modules follow the dependency order of the proof.

- `Basic.lean`: real `L²(ℤ)`, finitely supported kernels, and translations.
- `Kernel.lean`: bounded difference and finite-convolution operators.
- `Fourier.lean`: the counting-measure Fourier equivalence and exact
  convolution-multiplier operator norm.
- `Chebyshev.lean`: the kernel polynomial, weighted norm, and exact Chebyshev
  coefficient reconstruction.
- `Alternation.lean`: the weak alternating-sign polynomial theorem used for
  uniqueness.
- `WeightedExtremal.lean`: Proposition 1.6, including construction, sharp
  norm, lower bound, and the unique equality case.
- `Challenge.lean`: assembly of the sharp inequality and coefficient-level
  equality characterization in Theorem 1.4.

The root module `JoseSmoothest.lean` imports `JoseSmoothest.Challenge` and
therefore exposes the complete formalization.
