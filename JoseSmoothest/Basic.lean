import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic

/-!
# Basic sequence spaces and translations

This file contains real `L²(ℤ)` for counting measure, finitely supported
kernels, and translations as linear isometries.
-/

noncomputable section

open MeasureTheory

namespace JoseSmoothest

/-- The real Hilbert space `L²(ℤ)` for counting measure on the integers. -/
abbrev Sequence := Lp ℝ 2 (Measure.count : Measure ℤ)

/-- A real-valued kernel with finite support on `ℤ`. -/
abbrev Kernel := ℤ →₀ ℝ

/-- Translation by `k`, sending `f(j)` to `f(j-k)`, as an isometry of `L²(ℤ)`. -/
def translation (k : ℤ) : Sequence →ₗᵢ[ℝ] Sequence :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun j : ℤ ↦ -k + j)
    (measurePreserving_vadd (-k) (Measure.count : Measure ℤ))

end JoseSmoothest
