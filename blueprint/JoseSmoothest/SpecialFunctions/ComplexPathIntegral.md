# Blueprint for `JoseSmoothest/SpecialFunctions/ComplexPathIntegral.lean`

## Purpose

Mathlib already has curve-integral, path, homotopy, Poincaré, and covering-map
infrastructure.  The remaining need is a thin compatibility layer between
those APIs and the concrete piecewise-`C¹` cut paths used for Abelian periods.
This module records that adapter surface.  During implementation, each
declaration below should first be discharged directly from the existing
Mathlib API; the custom structure should be retained only where the finite
break-point and absolute-continuity data genuinely fail to fit.  The module
remains about paths in `ℂ`; integration on an abstract Riemann surface is
deliberately out of scope.

## Imports

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Topology.Homotopy.Path
```

## Public declarations

```lean
noncomputable section

namespace Complex

structure PiecewiseC1Path (a b : ℂ) where
  toFun : ℝ → ℂ
  source : toFun 0 = a
  target : toFun 1 = b
  continuousOn : ContinuousOn toFun (Set.Icc (0 : ℝ) 1)
  absolutelyContinuous : AbsolutelyContinuousOnInterval toFun 0 1
  velocity : ℝ → ℂ
  breaks : Finset ℝ
  hasDerivAt_toFun :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ breaks →
      HasDerivAt toFun velocity t
  intervalIntegrable_velocity :
    IntervalIntegrable velocity volume 0 1

namespace PiecewiseC1Path

instance {a b : ℂ} : CoeFun (PiecewiseC1Path a b) (fun _ ↦ ℝ → ℂ) :=
  ⟨PiecewiseC1Path.toFun⟩

def constant (a : ℂ) : PiecewiseC1Path a a

def line (a b : ℂ) : PiecewiseC1Path a b

def reverse {a b : ℂ} (p : PiecewiseC1Path a b) :
    PiecewiseC1Path b a

def trans {a b c : ℂ} (p : PiecewiseC1Path a b)
    (q : PiecewiseC1Path b c) : PiecewiseC1Path a c

structure Reparametrization where
  toFun : ℝ → ℝ
  mapsTo : Set.MapsTo toFun (Set.Icc 0 1) (Set.Icc 0 1)
  source : toFun 0 = 0
  target : toFun 1 = 1
  continuousOn : ContinuousOn toFun (Set.Icc 0 1)
  absolutelyContinuous : AbsolutelyContinuousOnInterval toFun 0 1
  strictMonoOn : StrictMonoOn toFun (Set.Icc 0 1)
  velocity : ℝ → ℝ
  breaks : Finset ℝ
  hasDerivAt_toFun :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ breaks →
      HasDerivAt toFun (velocity t) t
  intervalIntegrable_velocity :
    IntervalIntegrable velocity volume 0 1

def reparam {a b : ℂ} (p : PiecewiseC1Path a b)
    (e : PiecewiseC1Path.Reparametrization) : PiecewiseC1Path a b

def integral {a b : ℂ} (p : PiecewiseC1Path a b) (f : ℂ → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, f (p t) * p.velocity t

def image {a b : ℂ} (p : PiecewiseC1Path a b) : Set ℂ :=
  p.toFun '' Set.Icc (0 : ℝ) 1

@[simp] theorem integral_constant (a : ℂ) (f : ℂ → ℂ) :
    (constant a).integral f = 0

theorem integral_line (a b : ℂ) (f : ℂ → ℂ) :
    (line a b).integral f =
      ∫ t in (0 : ℝ)..1, f (a + t * (b - a)) * (b - a)

theorem integral_reverse {a b : ℂ} (p : PiecewiseC1Path a b)
    (f : ℂ → ℂ) (hf : ContinuousOn f p.image) :
    p.reverse.integral f = -p.integral f

theorem integral_trans {a b c : ℂ}
    (p : PiecewiseC1Path a b) (q : PiecewiseC1Path b c) (f : ℂ → ℂ)
    (hf : ContinuousOn f (p.image ∪ q.image)) :
    (p.trans q).integral f = p.integral f + q.integral f

theorem integral_reparam {a b : ℂ} (p : PiecewiseC1Path a b)
    (e : PiecewiseC1Path.Reparametrization) (f : ℂ → ℂ)
    (hf : ContinuousOn f p.image) :
    (p.reparam e).integral f = p.integral f

theorem integral_deriv_eq_sub {a b : ℂ} (p : PiecewiseC1Path a b)
    {U : Set ℂ} (hU : IsOpen U) (hp : p.image ⊆ U)
    {F : ℂ → ℂ} {f : ℂ → ℂ}
    (hf : ContinuousOn f U)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z) :
    p.integral f = F b - F a

structure PiecewiseC1Homotopy {a b : ℂ}
    (p q : PiecewiseC1Path a b) where
  toFun : ℝ × ℝ → ℂ
  boundary_zero : ∀ s ∈ Set.Icc (0 : ℝ) 1, toFun (s, 0) = a
  boundary_one : ∀ s ∈ Set.Icc (0 : ℝ) 1, toFun (s, 1) = b
  start_path : ∀ t ∈ Set.Icc (0 : ℝ) 1, toFun (0, t) = p t
  end_path : ∀ t ∈ Set.Icc (0 : ℝ) 1, toFun (1, t) = q t
  contDiff : ContDiffOn ℝ 1 toFun (Set.Icc 0 1 ×ˢ Set.Icc 0 1)

theorem integral_eq_of_c1HomotopicOn {a b : ℂ}
    {p q : PiecewiseC1Path a b} (H : PiecewiseC1Homotopy p q)
    {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (himage : H.toFun '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) ⊆ U) :
    p.integral f = q.integral f

theorem integral_closed_eq_zero_of_hasPrimitive
    {a : ℂ} (p : PiecewiseC1Path a a) {U : Set ℂ}
    (hU : IsOpen U) {f : ℂ → ℂ} (hp : p.image ⊆ U)
    (hf : ContinuousOn f U)
    (hprimitive : ∃ F : ℂ → ℂ,
      ∀ z ∈ U, HasDerivAt F (f z) z) :
    p.integral f = 0

end PiecewiseC1Path

end Complex
```

`Reparametrization` carries the same finite-break derivative data as
`PiecewiseC1Path`, now for a real-valued map.  Absolute continuity is included
explicitly in both structures; derivative existence and Lebesgue
integrability alone would not justify the fundamental theorem.  Clients
should normally use only `reparam` and `integral_reparam`.

## Detailed natural-language proof blueprint

### Definition and elementary paths

The integral is the ordinary real interval integral of the complex-valued
function

```text
t ↦ f(p(t)) p'(t).
```

The path is continuous and absolutely continuous, with an
interval-integrable velocity agreeing with its derivative away from a finite
set of break points.  Absolute continuity supplies the fundamental-theorem
hypothesis and is closed under the affine reversal and concatenation used
here.  A
constant path has zero velocity.  The line from `a` to `b` has parametrization
`a+t(b-a)` and constant velocity `b-a`, giving the two simp lemmas by
unfolding.

### Reversal and concatenation

The reverse path is `t ↦ p(1-t)` with velocity `-p'(1-t)`.  Substitute
`u=1-t` in the interval integral; the orientation reversal contributes the
minus sign.

For concatenation, run `p` at double speed on `[0,1/2]` and `q` at double
speed on `[1/2,1]`.  Split the integral at `1/2` and use affine changes of
variables on both halves.  The factor two in each velocity cancels the
Jacobian factor one half.  The possible derivative mismatch at the joining
point is inserted into the finite `breaks` set and is irrelevant to the
integral.  Continuity of `f` on the compact path images makes both integrands
interval-integrable, avoiding false identities caused by Lean's totalized
integral.  Thus `trans` really inhabits the displayed public structure.

### Reparametrization

For an absolutely continuous, increasing endpoint-preserving
reparametrization `e`, the chain rule
turns the new integrand into

```text
f(p(e(t))) p'(e(t)) e'(t).
```

The interval-integral substitution theorem proves invariance.  This is the
key fact allowing later period calculations to choose convenient cut
parametrizations.

### Fundamental theorem for a primitive

On the open neighborhood `U`, continuity of the derivative `f` makes `F`
continuously differentiable along the compact path image.  Composition with
the absolutely continuous path is absolutely continuous.  Its almost-
everywhere real derivative is the complex product `f(p(t))p'(t)` by the
complex chain rule, so the interval fundamental theorem applies.  The
endpoints of `p` are definitionally `a` and `b`, so the result is `F(b)-F(a)`.
The closed-path corollary follows immediately.

### Homotopy invariance

For each homotopy parameter `s`, integrate `f` along the horizontal path
`t ↦ H(s,t)`.  Differentiate this integral with respect to `s` under the
integral sign.  Holomorphy gives the equality of the two mixed derivatives;
integration by parts converts the derivative to boundary terms.  Both
vertical boundary paths are constant at `a` and `b`, so those terms vanish.
The path integral is therefore constant in `s`, and its values at zero and
one are the integrals along `p` and `q`.

This is the only homotopy theorem required by the cut model.  A general
fundamental-group or singular-homology formalization is intentionally not a
prerequisite.
