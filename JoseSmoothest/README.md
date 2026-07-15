# Internal Lean Library

The internal modules follow the dependency order of the proof.

- `Basic.lean`: real `L²(ℤ)`, finitely supported kernels, and translations.
- `Kernel.lean`: bounded difference and finite-convolution operators.
- `Fourier.lean`: the counting-measure Fourier equivalence and exact
  convolution-multiplier operator norm.
- `Chebyshev.lean`: the kernel polynomial, weighted norm, exact Chebyshev
  coefficient reconstruction, and the inverse polynomial-to-kernel bridge.
- `Alternation.lean`: the weak alternating-sign polynomial theorem used for
  uniqueness.
- `WeightedExtremal.lean`: Proposition 1.6, including construction, sharp
  norm, lower bound, and the unique equality case.
- `Challenge.lean`: complete assembly of Theorem 1.4, including the explicit
  admissible extremal kernel, attainment, and uniqueness.
- `SixthOrder.lean`: exact sixth-difference norm reduction and a property-first
  cubic weighted extremal theorem from an abstract zero--peak certificate,
  including conditional kernel reconstruction, attainment, and uniqueness.
- `JacobiTheta.lean`: carefully normalized theta-one through theta-four
  expressions, Lebedev's theta ratio, and the theta expressions for the
  Jacobi functions, with only the derivative and symmetry facts currently
  justified by Mathlib.
- `Zolotarev.lean`: the complete polynomial endpoint calculation from
  Pell--Abel, differential, and equioscillation data to the cubic certificate,
  the exact `144 r² / N²` bound as a function of the supplied abstract
  endpoint parameter `r`, and the unique sixth-order kernel. Identifying this
  `r` with the paper's Jacobi elliptic ratio remains part of the missing
  analytic construction.
- `SpecialFunctions/PellAbel.lean`: reusable polynomial Pell--Abel algebra,
  derivative divisibility, degree formulas, endpoint valuations, and the real
  interval bound.
- `SpecialFunctions/RealPellPhase.lean`: a reusable real-variable phase
  theorem for a supplied Pell--Abel solution, including strict monotonicity
  and exact cosine/sine formulae without compact-curve or period theory.
- `EvenOrder/WeightedMinimax.lean`: the generic weighted norm and sufficient
  zero--peak certificate theorem at arbitrary half-order `m`.
- `EvenOrder/FourierReduction.lean`: the exact identity between a `2m`-fold
  difference norm and `2^m` times the generic weighted polynomial norm.
- `EvenOrder/EndpointContact.lean`: the forced minimum-genus bound, endpoint
  valuations and differential identity, exact endpoint coefficient/scale,
  and normalized quotient for arbitrary contact order `m`.
- `TwoSetAlternation.lean`: the finite two-set dichotomy producing either
  alternating nodes or a strict low-degree polynomial separator.
- `EvenOrder/ActiveSetPerturbation.lean`: a separator produces one uniformly
  feasible perturbation with strictly smaller weighted norm.
- `EvenOrder/Equioscillation.lean`: compact minimizer existence, necessary
  zero--peak alternation, certified extremal data, and uniqueness for every
  `1 ≤ m ≤ N`.
- `EvenOrder/EndpointAlternation.lean`: normalizes the minimizer to `[-1,1]`,
  forces the left endpoint into the alternation, exhausts all derivative
  roots, and appends the right endpoint.
- `EvenOrder/PellExtraction.lean`: extracts the monic minimal-genus
  squarefree Pell weight and denominator, proves both endpoint valuations and
  the interval sign, and packages the resulting endpoint-contact data.
- `EvenOrder/EndpointPhase.lean`: proves endpoint square-root integrability,
  classifies the extracted alternant as a cosine of a strictly increasing
  phase, and proves the exact scaled winding
  `N * phase(1) = (N - m + 1) * π`.
- `EvenOrder/DirectClassification.lean`: applies the direct phase to the
  canonical minimizer and expresses both its weighted peak and the sharp
  kernel constant through the endpoint coefficient of the extracted Pell
  weight.
- `EvenOrder.lean`: reconstructs the minimizer as a kernel and proves the
  unconditional sharp lower bound, equality characterization, and unique
  optimizer for every difference order `2m` with `m ≥ 1`.

The root module `JoseSmoothest.lean` exposes the complete fourth-order
formalization, the unconditional arbitrary-even-order minimization theorem,
its direct minimal-genus Pell/phase classification, and the theta foundation
and algebraic Zolotarev sixth-order extension.  The remaining analytic task is
a forward special-function construction from prescribed periods or theta
data; for the paper's sixth-order presentation, the paper itself does not
prove existence of its parameter `k_N`.

The complete statement-first plan for arbitrary even difference order starts
at [`blueprint/JoseSmoothest/EvenOrder.md`](../blueprint/JoseSmoothest/EvenOrder.md),
with the reusable analytic prerequisites under
[`blueprint/JoseSmoothest/SpecialFunctions.md`](../blueprint/JoseSmoothest/SpecialFunctions.md).
It contains one Markdown file for every planned Lean module, the corrected
minimal genus `floor ((m-1)/2)` at order `2m`, compact minimizer and necessary
equioscillation proofs, explicit curve extraction, the odd/even endpoint
parity split, and the final unique-kernel theorem.  The pure polynomial
Pell--Abel layer, unconditional kernel theorem, and direct real-phase
classification are now implemented.  The compact-curve, period, and theta
modules remain an optional forward-construction branch in the blueprint.
