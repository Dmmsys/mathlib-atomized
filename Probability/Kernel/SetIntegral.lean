/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Kernel.Integral

/-! # Integral against a kernel over a set

This file contains lemmas about the integral against a kernel and over a set.

-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {X Y E : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  [NormedAddCommGroup E] [NormedSpace Real E] (κ : Kernel X Y)

/--
lemma `integral_integral_indicator` / 引理 `integral_integral_indicator`

English:
lemma integral_integral_indicator
  statement: (μ : Measure X) (f : X -> Y -> E) {s : Set X}
  proof: by
  simp_rw [← integral_indicator hs, Kernel.integral_indicator₂]

中文:
引理 integral_integral_indicator
  结论: (μ : 测度 X) (f : X -> Y -> E) {s : 集合 X}
  证明: by
  simp_rw [← integral_indicator hs, Kernel.integral_indicator₂]

Depends on / 依赖: Kernel, Kernel.integral_indicator, integral_indicator, simp_rw
-/
lemma integral_integral_indicator (μ : Measure X) (f : X -> Y -> E) {s : Set X}
    (hs : MeasurableSet s) :
    ∫ x, ∫ y, s.indicator (f · y) x ∂κ x ∂μ = ∫ x in s, ∫ y, f x y ∂κ x ∂μ := by
  simp_rw [← integral_indicator hs, Kernel.integral_indicator₂]

end ProbabilityTheory.Kernel
