# Blueprint for `JoseSmoothest/SixthOrder.lean`

## Purpose

This module isolates the part of the sixth-difference problem that does not
depend on constructing Jacobi elliptic functions or Zolotarev polynomials.
It defines the cubic weighted norm and its admissible class, then packages
the precise zero--peak properties needed from a Zolotarev numerator. The
downstream `Zolotarev` module produces this certificate from the polynomial
Pell--Abel/differential/equioscillation package. Any polynomial satisfying the
certificate is proved to be the unique sharp optimizer.

## Imports

```lean
import JoseSmoothest.Alternation
import JoseSmoothest.Chebyshev
```

## Public declarations

```lean
noncomputable section

namespace JoseSmoothest

open Polynomial

def cubicWeightedPolynomialNorm (p : ℝ[X]) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Set.Icc (-1 : ℝ) 1,
    r = |(1 - x) ^ 3 * p.eval x|}

structure IsAdmissibleCubicWeightedPolynomial (N : ℕ) (p : ℝ[X]) : Prop where
  degree_le : p.natDegree ≤ N - 3
  nonnegative : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ p.eval x
  eval_one : p.eval 1 = 1

theorem IsAdmissibleKernel.cubicKernelPolynomial
    {n : ℕ} {u : Kernel} (h : IsAdmissibleKernel n u) :
    IsAdmissibleCubicWeightedPolynomial (n + 3) (kernelPolynomial n u)

structure CubicZeroPeakCertificate (N : ℕ) (q : ℝ[X]) (M : ℝ) where
  orientation : ℝ
  orientation_eq : orientation = 1 ∨ orientation = -1
  nodes : Fin (N - 3 + 1) → ℝ
  strictMono_nodes : StrictMono nodes
  nodes_mem_Ico : ∀ i, nodes i ∈ Set.Ico (-1 : ℝ) 1
  bounds : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ q.eval x ∧ q.eval x ≤ M
  exists_peak : ∃ x ∈ Set.Icc (-1 : ℝ) 1, q.eval x = M
  node_value : ∀ i,
    q.eval (nodes i) =
      M / 2 * (1 - orientation * (-1 : ℝ) ^ (i : ℕ))

theorem differenceSmoothness_six_eq_eight_mul_cubicWeightedPolynomialNorm
    (n : ℕ)
    (u : Kernel)
    (support : ∀ k : ℤ, k ∉ Finset.Icc (-(n : ℤ)) n → u k = 0)
    (symmetric : ∀ k : ℤ, u (-k) = u k) :
    differenceSmoothness 6 u =
      8 * cubicWeightedPolynomialNorm (kernelPolynomial n u)

theorem cubicWeightedPolynomialNorm_eq_of_certificate
    {N : ℕ} {S q : ℝ[X]} {M : ℝ}
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate N q M) :
    cubicWeightedPolynomialNorm S = M

theorem cubicWeightedPolynomial_eq_of_norm_le
    (N : ℕ) (hN : 3 ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleCubicWeightedPolynomial N p)
    (hS : IsAdmissibleCubicWeightedPolynomial N S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate N q M)
    (hnorm : cubicWeightedPolynomialNorm p ≤ M) :
    p = S

theorem cubicWeightedPolynomialNorm_ge_of_certificate
    (N : ℕ) (hN : 3 ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleCubicWeightedPolynomial N p)
    (hS : IsAdmissibleCubicWeightedPolynomial N S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate N q M) :
    M ≤ cubicWeightedPolynomialNorm p

theorem cubicWeightedPolynomialNorm_eq_iff_of_certificate
    (N : ℕ) (hN : 3 ≤ N)
    {p S q : ℝ[X]} {M : ℝ}
    (hp : IsAdmissibleCubicWeightedPolynomial N p)
    (hS : IsAdmissibleCubicWeightedPolynomial N S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate N q M) :
    cubicWeightedPolynomialNorm p = M ↔ p = S

def certifiedSixthOrderKernel (n : ℕ) (S : ℝ[X]) : Kernel :=
  kernelOfPolynomial n S

theorem kernelPolynomial_certifiedSixthOrderKernel
    (n : ℕ)
    {S : ℝ[X]}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S) :
    kernelPolynomial n (certifiedSixthOrderKernel n S) = S

theorem certifiedSixthOrderKernel_isAdmissible
    (n : ℕ)
    {S : ℝ[X]}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S) :
    IsAdmissibleKernel n (certifiedSixthOrderKernel n S)

theorem certifiedSixthOrderKernel_attains
    (n : ℕ)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    differenceSmoothness 6 (certifiedSixthOrderKernel n S) = 8 * M

theorem sixthOrderSmoothness_ge_of_certificate
    (n : ℕ)
    (u : Kernel)
    (hu : IsAdmissibleKernel n u)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    8 * M ≤ differenceSmoothness 6 u

theorem sixthOrderSmoothness_eq_iff_kernelPolynomial_eq_of_certificate
    (n : ℕ)
    (u : Kernel)
    (hu : IsAdmissibleKernel n u)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    differenceSmoothness 6 u = 8 * M ↔ kernelPolynomial n u = S

theorem sixthOrderSmoothness_eq_iff_eq_certifiedKernel
    (n : ℕ)
    (u : Kernel)
    (hu : IsAdmissibleKernel n u)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    differenceSmoothness 6 u = 8 * M ↔
      u = certifiedSixthOrderKernel n S

theorem exists_certifiedSixthOrderKernel
    (n : ℕ)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    ∃ u : Kernel,
      IsAdmissibleKernel n u ∧ differenceSmoothness 6 u = 8 * M

theorem existsUnique_certifiedSixthOrderKernel
    (n : ℕ)
    {S q : ℝ[X]} {M : ℝ}
    (hS : IsAdmissibleCubicWeightedPolynomial (n + 3) S)
    (hSq : (C 1 - X) ^ 3 * S = q)
    (certificate : CubicZeroPeakCertificate (n + 3) q M) :
    ∃! u : Kernel,
      IsAdmissibleKernel n u ∧ differenceSmoothness 6 u = 8 * M

end JoseSmoothest
```

## Detailed proof blueprint

### The cubic weighted norm

The defining range is nonempty because it contains the weighted value at
zero.  It is bounded above because it is the image of the compact interval
`[-1,1]` under the continuous function

`x ↦ |(1-x)^3 p(x)|`.

Consequently every pointwise weighted value is at most the supremum.

### Kernel reduction and the factor eight

An admissible kernel has a degree-`n` kernel polynomial, nonnegative on the
interval and normalized at one.  Reindexing by `N=n+3` therefore produces an
admissible cubic weighted polynomial.

The generic Fourier theorem identifies `differenceSmoothness 6 u` with the
supremum of `differenceMultiplier 6 u`.  At order six the multiplier is

`8 * (1-cos ξ)^3 * |kernelFourierTransform u ξ|`.

For a supported symmetric kernel, `kernelPolynomial_eval_cos` replaces the
Fourier transform by the kernel polynomial evaluated at `cos ξ`.  This shows
pointwise that multiplier values are eight times cubic weighted values.
Cosine sends the circle into `[-1,1]`, while `arccos` supplies the reverse
comparison.  Two `csSup` arguments prove the exact identity.

### Norm of a certified candidate

Assume `(C 1-X)^3 S=q`.  Evaluation turns this identity into

`(1-x)^3 S(x)=q(x)`.

The certificate bounds `q` between zero and `M`, so every value in the range
defining `cubicWeightedPolynomialNorm S` is at most `M`.  The certified peak
is a member of this range and equals `M`.  The two `csSup` inequalities give
exact equality.

### Conditional uniqueness

Let `p` and `S` be admissible and assume the norm of `p` is at most `M`.
When `N=3`, both have degree zero and value one at `1`, hence both equal the
constant polynomial one.

Suppose `N≥4`.  Since `p(1)=S(1)`, factor

`p-S=(X-C 1)r`.

The degree hypotheses give `r.natDegree<N-3`.  At every certified node
`x<1`, exact factorization gives

`(1-x)^3 p(x)-q(x)=-(1-x)^4 r(x)`.

The factor `(1-x)^4` is strictly positive.  At a zero node, nonnegativity of
`p` fixes one weak sign of `r`; at a peak node, the norm bound fixes the
opposite sign.  Multiplying `r` by the negative certificate orientation makes
these signs exactly

`0 ≤ (-1)^i t(nodes i)`.

There are `N-3+1` strictly increasing nodes, so
`polynomial_eq_zero_of_alternating_signs` proves `t=0`.  The orientation is
nonzero, hence `r=0`, and the factorization yields `p=S`.

### Sharpness and equality

If an admissible `p` had norm strictly below `M`, conditional uniqueness
would identify it with `S`, contradicting the already computed norm of `S`.
This proves the sharp lower bound.  Applying uniqueness to an equality and
using the candidate norm in the reverse direction gives the equality
characterization.

### Conditional kernel theorem

Reconstruct the candidate kernel from the Chebyshev coefficients of `S`.
The polynomial reconstruction theorem gives its kernel polynomial exactly,
and the degree, nonnegativity, and normalization fields of `hS` prove kernel
admissibility.

The exact factor-eight identity transfers the certified polynomial norm and
lower bound to `differenceSmoothness 6`.  The polynomial equality theorem
characterizes equality by `kernelPolynomial n u=S`.  Finally, supported
symmetric kernels are determined by their kernel polynomials, so equality
holds exactly at `certifiedSixthOrderKernel n S`.  This supplies both an
existence theorem and an `∃!` theorem without assuming any analytic
Zolotarev construction.

## Downstream Zolotarev layer

`JoseSmoothest/Zolotarev.lean` takes the polynomial Pell--Abel identity,
Lebedev differential equation, endpoint scale, bounds, and equioscillation
nodes as input. It proves that `q` proportional to `1-Z` has a cubic factor at
`1`, constructs and normalizes the quotient `S`, and populates the
`CubicZeroPeakCertificate` used here. The remaining open work is analytic:
construct those input polynomials and nodes from the theta quotient and prove
existence of the modulus `k_N`.
