/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Measurability and integrability of the sinc function

## Main statements

* `measurable_sinc`: the sinc function is measurable.
* `integrable_sinc`: the sinc function is integrable with respect to any finite measure on `ℝ`.

-/

public section

open MeasureTheory

variable {α : Type*} {_ : MeasurableSpace α} {f : α -> Real} {μ : Measure α}

namespace Real

@[fun_prop]
/--
lemma `measurable_sinc` / 引理 `measurable_sinc`

English:
lemma measurable_sinc
  statement: Measurable sinc
  proof: continuous_sinc.measurable

@[fun_prop]

中文:
引理 measurable_sinc
  结论: 可测 sinc
  证明: continuous_sinc.measurable

@[fun_prop]

Depends on / 依赖: continuous_sinc, continuous_sinc.measurable, measurable
-/
lemma measurable_sinc : Measurable sinc := continuous_sinc.measurable

@[fun_prop]
/--
lemma `stronglyMeasurable_sinc` / 引理 `stronglyMeasurable_sinc`

English:
lemma stronglyMeasurable_sinc
  statement: StronglyMeasurable sinc
  proof: measurable_sinc.stronglyMeasurable

@[fun_prop]

中文:
引理 stronglyMeasurable_sinc
  结论: StronglyMeasurable sinc
  证明: measurable_sinc.stronglyMeasurable

@[fun_prop]

Depends on / 依赖: measurable_sinc, measurable_sinc.stronglyMeasurable, stronglyMeasurable
-/
lemma stronglyMeasurable_sinc : StronglyMeasurable sinc := measurable_sinc.stronglyMeasurable

@[fun_prop]
/--
lemma `integrable_sinc` / 引理 `integrable_sinc`

English:
lemma integrable_sinc
  given: {μ : Measure Real} [IsFiniteMeasure μ]
  proof: by
refine Integrable.mono' (g := fun _ => 1) (by fun_prop) (by fun_prop) ae_of_all _ fun x => ?_
  rw [Real.norm_eq_abs]
  exact abs_sinc_le_one x

中文:
引理 integrable_sinc
  条件: {μ : 测度 实数} [是有限测度 μ]
  证明: by
refine Integrable.mono' (g := fun _ => 1) (by fun_prop) (by fun_prop) ae_of_all _ fun x => ?_
  rw [Real.norm_eq_abs]
  exact abs_sinc_le_one x

Depends on / 依赖: Integrable, Integrable.mono, Real.norm_eq_abs, abs_sinc_le_one, ae_of_all, fun_prop, norm_eq_abs
-/
lemma integrable_sinc {μ : Measure Real} [IsFiniteMeasure μ] :
    Integrable sinc μ := by
refine Integrable.mono' (g := fun _ => 1) (by fun_prop) (by fun_prop) ae_of_all _ fun x => ?_
  rw [Real.norm_eq_abs]
  exact abs_sinc_le_one x

end Real

open Real

@[fun_prop]
/--
theorem `Measurable.sinc` / 定理 `Measurable.sinc`

English:
theorem Measurable.sinc
  given: (hf : Measurable f)
  statement: Measurable fun x => sinc (f x)
  proof: Real.measurable_sinc.comp hf

@[fun_prop]

中文:
定理 可测.sinc
  条件: (hf : 可测 f)
  结论: 可测 fun x => sinc (f x)
  证明: Real.measurable_sinc.comp hf

@[fun_prop]
-/
protected theorem Measurable.sinc (hf : Measurable f) : Measurable fun x => sinc (f x) :=
  Real.measurable_sinc.comp hf

@[fun_prop]
/--
theorem `AEMeasurable.sinc` / 定理 `AEMeasurable.sinc`

English:
theorem AEMeasurable.sinc
  given: (hf : AEMeasurable f μ)
  statement: AEMeasurable (fun x => sinc (f x)) μ
  proof: Real.measurable_sinc.comp_aemeasurable hf

@[fun_prop]

中文:
定理 几乎处处可测.sinc
  条件: (hf : 几乎处处可测 f μ)
  结论: 几乎处处可测 (fun x => sinc (f x)) μ
  证明: Real.measurable_sinc.comp_aemeasurable hf

@[fun_prop]
-/
protected theorem AEMeasurable.sinc (hf : AEMeasurable f μ) : AEMeasurable (fun x => sinc (f x)) μ :=
  Real.measurable_sinc.comp_aemeasurable hf

@[fun_prop]
/--
theorem `MeasureTheory.StronglyMeasurable.sinc` / 定理 `MeasureTheory.StronglyMeasurable.sinc`

English:
theorem MeasureTheory.StronglyMeasurable.sinc
  given: (hf : StronglyMeasurable f)
  proof: Real.stronglyMeasurable_sinc.comp_measurable hf.measurable

@[fun_prop]

中文:
定理 测度论.StronglyMeasurable.sinc
  条件: (hf : StronglyMeasurable f)
  证明: Real.stronglyMeasurable_sinc.comp_measurable hf.measurable

@[fun_prop]
-/
protected theorem MeasureTheory.StronglyMeasurable.sinc (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => sinc (f x) :=
  Real.stronglyMeasurable_sinc.comp_measurable hf.measurable

@[fun_prop]
/--
theorem `MeasureTheory.AEStronglyMeasurable.sinc` / 定理 `MeasureTheory.AEStronglyMeasurable.sinc`

English:
theorem MeasureTheory.AEStronglyMeasurable.sinc
  given: (hf : AEStronglyMeasurable f μ)
  proof: by
  rw [aestronglyMeasurable_iff_aemeasurable] at hf ⊢
  exact hf.sinc

中文:
定理 测度论.AEStronglyMeasurable.sinc
  条件: (hf : AEStronglyMeasurable f μ)
  证明: by
  rw [aestronglyMeasurable_iff_aemeasurable] at hf ⊢
  exact hf.sinc
-/
protected theorem MeasureTheory.AEStronglyMeasurable.sinc (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => sinc (f x)) μ := by
  rw [aestronglyMeasurable_iff_aemeasurable] at hf ⊢
  exact hf.sinc
