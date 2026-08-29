/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Kernel.Basic

/-!
# Bochner integrals of kernels

-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Kernel α β}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : β -> E} {a : α}

namespace Kernel

/--
lemma `IsFiniteKernel.integrable` / 引理 `IsFiniteKernel.integrable`

English:
lemma IsFiniteKernel.integrable
  statement: (μ : Measure α) [IsFiniteMeasure μ]
  proof: by
  refine Integrable.mono' (integrable_const κ.bound.toReal)
    ((κ.measurable_coe hs).ennreal_toReal.aestronglyMeasurable)
    (ae_of_all μ fun x => ?_)
  rw [Real.norm_eq_abs]; rw [abs_of_nonneg measureReal_nonneg]
  exact ENNReal.toReal_mono (Kernel.bound_ne_top _) (Kernel.measure_le_bound _ _

中文:
引理 IsFiniteKernel.integrable
  结论: (μ : Measure α) [IsFiniteMeasure μ]
  证明: by
  refine Integrable.mono' (integrable_const κ.bound.toReal)
    ((κ.measurable_coe hs).ennreal_toReal.aestronglyMeasurable)
    (ae_of_all μ fun x => ?_)
  rw [Real.norm_eq_abs]; rw [abs_of_nonneg measureReal_nonneg]
  exact ENNReal.toReal_mono (Kernel.bound_ne_top _) (Kernel.measure_le_bound _ _

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, Integrable, Integrable.mono, Kernel, Kernel.bound_ne_top, Kernel.measure_le_bound, Real.norm_eq_abs, abs_of_nonneg, ae_of_all, aestronglyMeasurable, bound.toReal, bound_ne_top, ennreal_toReal, ennreal_toReal.aestronglyMeasurable, integrable_const, measurable_coe, measureReal_nonneg, measure_le_bound, norm_eq_abs
-/
lemma IsFiniteKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsFiniteKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x => (κ x).real s) μ := by
  refine Integrable.mono' (integrable_const κ.bound.toReal)
    ((κ.measurable_coe hs).ennreal_toReal.aestronglyMeasurable)
    (ae_of_all μ fun x => ?_)
  rw [Real.norm_eq_abs]; rw [abs_of_nonneg measureReal_nonneg]
  exact ENNReal.toReal_mono (Kernel.bound_ne_top _) (Kernel.measure_le_bound _ _ _)

/--
lemma `IsMarkovKernel.integrable` / 引理 `IsMarkovKernel.integrable`

English:
lemma IsMarkovKernel.integrable
  statement: (μ : Measure α) [IsFiniteMeasure μ]
  proof: IsFiniteKernel.integrable μ κ hs

中文:
引理 IsMarkovKernel.integrable
  结论: (μ : Measure α) [IsFiniteMeasure μ]
  证明: IsFiniteKernel.integrable μ κ hs

Depends on / 依赖: IsFiniteKernel, IsFiniteKernel.integrable, integrable
-/
lemma IsMarkovKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x => (κ x).real s) μ :=
  IsFiniteKernel.integrable μ κ hs

/--
lemma `integral_congr_ae₂` / 引理 `integral_congr_ae₂`

English:
lemma integral_congr_ae₂
  given: {f g : α -> β -> E} {μ : Measure α} (h : forallᵐ a ∂μ, f a =ᵐ[κ a] g a)
  proof: by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

中文:
引理 integral_congr_ae₂
  条件: {f g : α -> β -> E} {μ : Measure α} (h : 对任意ᵐ a ∂μ, f a =ᵐ[κ a] g a)
  证明: by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

Depends on / 依赖: filter_upwards, integral_congr_ae
-/
lemma integral_congr_ae₂ {f g : α -> β -> E} {μ : Measure α} (h : forallᵐ a ∂μ, f a =ᵐ[κ a] g a) :
    ∫ a, ∫ b, f a b ∂(κ a) ∂μ = ∫ a, ∫ b, g a b ∂(κ a) ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

/--
lemma `integral_indicator₂` / 引理 `integral_indicator₂`

English:
lemma integral_indicator₂
  given: (f : α -> β -> E) (s : Set α) (a : α)
  proof: by
  by_cases ha : a in s <;> simp [ha]

中文:
引理 integral_indicator₂
  条件: (f : α -> β -> E) (s : Set α) (a : α)
  证明: by
  by_cases ha : a in s <;> simp [ha]
-/
lemma integral_indicator₂ (f : α -> β -> E) (s : Set α) (a : α) :
    ∫ y, s.indicator (f · y) a ∂κ a = s.indicator (fun x => ∫ y, f x y ∂κ x) a := by
  by_cases ha : a in s <;> simp [ha]

section Deterministic

variable [CompleteSpace E] {g : α -> β}

/--
theorem `integral_deterministic'` / 定理 `integral_deterministic'`

English:
theorem integral_deterministic'
  given: (hg : Measurable g) (hf : StronglyMeasurable f)
  proof: by
  rw [deterministic_apply]; rw [integral_dirac' _ _ hf]

@[simp]

中文:
定理 integral_deterministic'
  条件: (hg : Measurable g) (hf : StronglyMeasurable f)
  证明: by
  rw [deterministic_apply]; rw [integral_dirac' _ _ hf]

@[simp]

Depends on / 依赖: deterministic_apply, integral_dirac
-/
theorem integral_deterministic' (hg : Measurable g) (hf : StronglyMeasurable f) :
    ∫ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply]; rw [integral_dirac' _ _ hf]

@[simp]
/--
theorem `integral_deterministic` / 定理 `integral_deterministic`

English:
theorem integral_deterministic
  given: [MeasurableSingletonClass β] (hg : Measurable g)
  proof: by
  rw [deterministic_apply]; rw [integral_dirac _ (g a)]

中文:
定理 integral_deterministic
  条件: [MeasurableSingletonClass β] (hg : Measurable g)
  证明: by
  rw [deterministic_apply]; rw [integral_dirac _ (g a)]

Depends on / 依赖: deterministic_apply, integral_dirac
-/
theorem integral_deterministic [MeasurableSingletonClass β] (hg : Measurable g) :
    ∫ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply]; rw [integral_dirac _ (g a)]

/--
theorem `setIntegral_deterministic'` / 定理 `setIntegral_deterministic'`

English:
theorem setIntegral_deterministic'
  statement: (hg : Measurable g)
  proof: by
  rw [deterministic_apply]; rw [setIntegral_dirac' hf _ hs]

@[simp]

中文:
定理 setIntegral_deterministic'
  结论: (hg : Measurable g)
  证明: by
  rw [deterministic_apply]; rw [setIntegral_dirac' hf _ hs]

@[simp]

Depends on / 依赖: deterministic_apply, setIntegral_dirac
-/
theorem setIntegral_deterministic' (hg : Measurable g)
    (hf : StronglyMeasurable f) {s : Set β} (hs : MeasurableSet s) [Decidable (g a in s)] :
    ∫ x in s, f x ∂deterministic g hg a = if g a in s then f (g a) else 0 := by
  rw [deterministic_apply]; rw [setIntegral_dirac' hf _ hs]

@[simp]
/--
theorem `setIntegral_deterministic` / 定理 `setIntegral_deterministic`

English:
theorem setIntegral_deterministic
  statement: [MeasurableSingletonClass β] (hg : Measurable g)
  proof: by
  rw [deterministic_apply]; rw [setIntegral_dirac f _ s]

中文:
定理 setIntegral_deterministic
  结论: [MeasurableSingletonClass β] (hg : Measurable g)
  证明: by
  rw [deterministic_apply]; rw [setIntegral_dirac f _ s]

Depends on / 依赖: deterministic_apply, setIntegral_dirac
-/
theorem setIntegral_deterministic [MeasurableSingletonClass β] (hg : Measurable g)
    (s : Set β) [Decidable (g a in s)] :
    ∫ x in s, f x ∂deterministic g hg a = if g a in s then f (g a) else 0 := by
  rw [deterministic_apply]; rw [setIntegral_dirac f _ s]

end Deterministic

section Const

@[simp]
/--
theorem `integral_const` / 定理 `integral_const`

English:
theorem integral_const
  given: {μ : Measure β}
  statement: ∫ x, f x ∂const α μ a = ∫ x, f x ∂μ
  proof: by
  rw [const_apply]

@[simp]

中文:
定理 integral_const
  条件: {μ : Measure β}
  结论: ∫ x, f x ∂const α μ a = ∫ x, f x ∂μ
  证明: by
  rw [const_apply]

@[simp]

Depends on / 依赖: const_apply
-/
theorem integral_const {μ : Measure β} : ∫ x, f x ∂const α μ a = ∫ x, f x ∂μ := by
  rw [const_apply]

@[simp]
/--
theorem `setIntegral_const` / 定理 `setIntegral_const`

English:
theorem setIntegral_const
  given: {μ : Measure β} {s : Set β}
  proof: by rw [const_apply]

中文:
定理 setIntegral_const
  条件: {μ : Measure β} {s : Set β}
  证明: by rw [const_apply]

Depends on / 依赖: const_apply
-/
theorem setIntegral_const {μ : Measure β} {s : Set β} :
    ∫ x in s, f x ∂const α μ a = ∫ x in s, f x ∂μ := by rw [const_apply]

end Const

section Restrict

variable {s : Set β}

@[simp]
/--
theorem `integral_restrict` / 定理 `integral_restrict`

English:
theorem integral_restrict
  given: (hs : MeasurableSet s)
  proof: by
  rw [restrict_apply]

@[simp]

中文:
定理 integral_restrict
  条件: (hs : MeasurableSet s)
  证明: by
  rw [restrict_apply]

@[simp]

Depends on / 依赖: restrict_apply
-/
theorem integral_restrict (hs : MeasurableSet s) :
    ∫ x, f x ∂κ.restrict hs a = ∫ x in s, f x ∂κ a := by
  rw [restrict_apply]

@[simp]
/--
theorem `setIntegral_restrict` / 定理 `setIntegral_restrict`

English:
theorem setIntegral_restrict
  given: (hs : MeasurableSet s) (t : Set β)
  proof: by
  rw [restrict_apply]; rw [Measure.restrict_restrict' hs]

中文:
定理 setIntegral_restrict
  条件: (hs : MeasurableSet s) (t : Set β)
  证明: by
  rw [restrict_apply]; rw [Measure.restrict_restrict' hs]

Depends on / 依赖: Measure, Measure.restrict_restrict, restrict_apply, restrict_restrict
-/
theorem setIntegral_restrict (hs : MeasurableSet s) (t : Set β) :
    ∫ x in t, f x ∂κ.restrict hs a = ∫ x in t inter s, f x ∂κ a := by
  rw [restrict_apply]; rw [Measure.restrict_restrict' hs]

end Restrict

section Piecewise

variable {η : Kernel α β} {s : Set α} {hs : MeasurableSet s} [DecidablePred (· in s)]

/--
theorem `integral_piecewise` / 定理 `integral_piecewise`

English:
theorem integral_piecewise
  given: (a : α) (g : β -> E)
  proof: by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

中文:
定理 integral_piecewise
  条件: (a : α) (g : β -> E)
  证明: by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

Depends on / 依赖: piecewise_apply, simp_rw, split_ifs
-/
theorem integral_piecewise (a : α) (g : β -> E) :
    ∫ b, g b ∂piecewise hs κ η a = if a in s then ∫ b, g b ∂κ a else ∫ b, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

/--
theorem `setIntegral_piecewise` / 定理 `setIntegral_piecewise`

English:
theorem setIntegral_piecewise
  given: (a : α) (g : β -> E) (t : Set β)
  proof: by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

中文:
定理 setIntegral_piecewise
  条件: (a : α) (g : β -> E) (t : Set β)
  证明: by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

Depends on / 依赖: piecewise_apply, simp_rw, split_ifs
-/
theorem setIntegral_piecewise (a : α) (g : β -> E) (t : Set β) :
    ∫ b in t, g b ∂piecewise hs κ η a =
      if a in s then ∫ b in t, g b ∂κ a else ∫ b in t, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

end Piecewise

end Kernel
end ProbabilityTheory
