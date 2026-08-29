/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Functions integrable on a set and at a filter

We define `IntegrableOn f s μ := Integrable f (μ.restrict s)` and prove theorems like
`integrableOn_union : IntegrableOn f (s ∪ t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ`.

Next we define a predicate `IntegrableAtFilter (f : α → E) (l : Filter α) (μ : Measure α)`
saying that `f` is integrable at some set `s ∈ l` and prove that a measurable function is integrable
at `l` with respect to `μ` provided that `f` is bounded above at `l ⊓ ae μ` and `μ` is finite
at `l`.

-/

@[expose] public section


noncomputable section

open Set Filter TopologicalSpace MeasureTheory Function

open scoped Topology Interval Filter ENNReal MeasureTheory

variable {α β ε ε' E F : Type*} {mα : MeasurableSpace α}

section

variable [TopologicalSpace β] [ENorm ε] [TopologicalSpace ε]
  {l l' : Filter α} {f g : α -> β} {μ ν : Measure α}

/--
Definition of `StronglyMeasurableAtFilter` / `StronglyMeasurableAtFilter` 的定义

English:
definition StronglyMeasurableAtFilter
  signature: (f : α -> β) (l : Filter α) (μ : Measure α := by volume_tac)
  body: exists s in l, AEStronglyMeasurable f (μ.restrict s)

@[simp]

中文:
定义 StronglyMeasurableAtFilter
  签名: (f : α -> β) (l : 滤子 α) (μ : 测度 α := by volume_tac)
  定义体: exists s in l, AEStronglyMeasurable f (μ.restrict s)

@[simp]

Depends on / 依赖: AEStronglyMeasurable, restrict, volume_tac
-/
def StronglyMeasurableAtFilter (f : α -> β) (l : Filter α) (μ : Measure α := by volume_tac) :=
  exists s in l, AEStronglyMeasurable f (μ.restrict s)

@[simp]
/--
theorem `stronglyMeasurableAt_bot` / 定理 `stronglyMeasurableAt_bot`

English:
theorem stronglyMeasurableAt_bot
  given: {f : α -> β}
  statement: StronglyMeasurableAtFilter f ⊥ μ
  proof: ⟨∅, mem_bot, by simp⟩

中文:
定理 stronglyMeasurableAt_bot
  条件: {f : α -> β}
  结论: StronglyMeasurableAtFilter f ⊥ μ
  证明: ⟨∅, mem_bot, by simp⟩

Depends on / 依赖: mem_bot
-/
theorem stronglyMeasurableAt_bot {f : α -> β} : StronglyMeasurableAtFilter f ⊥ μ :=
  ⟨∅, mem_bot, by simp⟩

/--
theorem `StronglyMeasurableAtFilter.eventually` / 定理 `StronglyMeasurableAtFilter.eventually`

English:
theorem StronglyMeasurableAtFilter.eventually
  given: (h : StronglyMeasurableAtFilter f l μ)
  proof: (eventually_smallSets' fun _ _ => AEStronglyMeasurable.mono_set).2 h

中文:
定理 StronglyMeasurableAtFilter.eventually
  条件: (h : StronglyMeasurableAtFilter f l μ)
  证明: (eventually_smallSets' fun _ _ => AEStronglyMeasurable.mono_set).2 h
-/
protected theorem StronglyMeasurableAtFilter.eventually (h : StronglyMeasurableAtFilter f l μ) :
    forallᶠ s in l.smallSets, AEStronglyMeasurable f (μ.restrict s) :=
  (eventually_smallSets' fun _ _ => AEStronglyMeasurable.mono_set).2 h

/--
theorem `StronglyMeasurableAtFilter.filter_mono` / 定理 `StronglyMeasurableAtFilter.filter_mono`

English:
theorem StronglyMeasurableAtFilter.filter_mono
  statement: (h : StronglyMeasurableAtFilter f l μ)
  proof: let ⟨s, hsl, hs⟩ := h
  ⟨s, h' hsl, hs⟩

中文:
定理 StronglyMeasurableAtFilter.filter_mono
  结论: (h : StronglyMeasurableAtFilter f l μ)
  证明: let ⟨s, hsl, hs⟩ := h
  ⟨s, h' hsl, hs⟩
-/
protected theorem StronglyMeasurableAtFilter.filter_mono (h : StronglyMeasurableAtFilter f l μ)
    (h' : l' <= l) : StronglyMeasurableAtFilter f l' μ :=
  let ⟨s, hsl, hs⟩ := h
  ⟨s, h' hsl, hs⟩

/--
theorem `MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter` / 定理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter`

English:
theorem MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter
  proof: ⟨univ, univ_mem, by rwa [Measure.restrict_univ]⟩

中文:
定理 测度论.AEStronglyMeasurable.stronglyMeasurableAtFilter
  证明: ⟨univ, univ_mem, by rwa [Measure.restrict_univ]⟩
-/
protected theorem MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter
    (h : AEStronglyMeasurable f μ) : StronglyMeasurableAtFilter f l μ :=
  ⟨univ, univ_mem, by rwa [Measure.restrict_univ]⟩

/--
theorem `AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem` / 定理 `AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem`

English:
theorem AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
  statement: {s}
  proof: ⟨s, hl, h⟩

中文:
定理 AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
  结论: {s}
  证明: ⟨s, hl, h⟩
-/
theorem AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem {s}
    (h : AEStronglyMeasurable f (μ.restrict s)) (hl : s in l) : StronglyMeasurableAtFilter f l μ :=
  ⟨s, hl, h⟩

/--
theorem `MeasureTheory.StronglyMeasurable.stronglyMeasurableAtFilter` / 定理 `MeasureTheory.StronglyMeasurable.stronglyMeasurableAtFilter`

English:
theorem MeasureTheory.StronglyMeasurable.stronglyMeasurableAtFilter
  proof: h.aestronglyMeasurable.stronglyMeasurableAtFilter

中文:
定理 测度论.StronglyMeasurable.stronglyMeasurableAtFilter
  证明: h.aestronglyMeasurable.stronglyMeasurableAtFilter
-/
protected theorem MeasureTheory.StronglyMeasurable.stronglyMeasurableAtFilter
    (h : StronglyMeasurable f) : StronglyMeasurableAtFilter f l μ :=
  h.aestronglyMeasurable.stronglyMeasurableAtFilter

end

namespace MeasureTheory

section NormedAddCommGroup

/--
theorem `HasFiniteIntegral.restrict_of_bounded` / 定理 `HasFiniteIntegral.restrict_of_bounded`

English:
theorem HasFiniteIntegral.restrict_of_bounded
  statement: [NormedAddCommGroup E] {f : α -> E} {s : Set α}
  proof: haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  .of_bounded hf

中文:
定理 HasFinite整数egral.restrict_of_bounded
  结论: [赋范交换加群 E] {f : α -> E} {s : 集合 α}
  证明: haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  .of_bounded hf

Depends on / 依赖: IsFiniteMeasure, Measure, Measure.restrict_apply_univ, of_bounded, restrict, restrict_apply_univ
-/
theorem HasFiniteIntegral.restrict_of_bounded [NormedAddCommGroup E] {f : α -> E} {s : Set α}
    {μ : Measure α} (C : Real) (hs : μ s < ∞) (hf : forallᵐ x ∂μ.restrict s, ‖f x‖ <= C) :
    HasFiniteIntegral f (μ.restrict s) :=
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  .of_bounded hf

variable [NormedAddCommGroup E] {f g : α -> ε} {s t : Set α} {μ ν : Measure α}
  [TopologicalSpace ε] [ContinuousENorm ε]

/--
theorem `HasFiniteIntegral.restrict_of_bounded_enorm` / 定理 `HasFiniteIntegral.restrict_of_bounded_enorm`

English:
theorem HasFiniteIntegral.restrict_of_bounded_enorm
  statement: {C : Real>=0∞} (hC : ‖C‖ₑ != ∞ := by finiteness)
  proof: haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ]; exact hs.lt_top⟩
  .of_bounded_enorm hC hf

中文:
定理 HasFinite整数egral.restrict_of_bounded_enorm
  结论: {C : 实数>=0∞} (hC : ‖C‖ₑ != ∞ := by finiteness)
  证明: haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ]; exact hs.lt_top⟩
  .of_bounded_enorm hC hf

Depends on / 依赖: HasFiniteIntegral, IsFiniteMeasure, Measure, Measure.restrict_apply_univ, finiteness, hs.lt_top, lt_top, of_bounded_enorm, restrict, restrict_apply_univ
-/
theorem HasFiniteIntegral.restrict_of_bounded_enorm {C : Real>=0∞} (hC : ‖C‖ₑ != ∞ := by finiteness)
    (hs : μ s != ∞ := by finiteness) (hf : forallᵐ x ∂μ.restrict s, ‖f x‖ₑ <= C) :
    HasFiniteIntegral f (μ.restrict s) :=
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ]; exact hs.lt_top⟩
  .of_bounded_enorm hC hf

/--
Definition of `IntegrableOn` / `IntegrableOn` 的定义

English:
definition IntegrableOn
  signature: (f : α -> ε) (s : Set α) (μ : Measure α := by volume_tac)
  body: Integrable f (μ.restrict s)

中文:
定义 整数egrableOn
  签名: (f : α -> ε) (s : 集合 α) (μ : 测度 α := by volume_tac)
  定义体: Integrable f (μ.restrict s)

Depends on / 依赖: Integrable, restrict, volume_tac
-/
def IntegrableOn (f : α -> ε) (s : Set α) (μ : Measure α := by volume_tac) : Prop :=
  Integrable f (μ.restrict s)

/--
theorem `IntegrableOn.integrable` / 定理 `IntegrableOn.integrable`

English:
theorem IntegrableOn.integrable
  given: (h : IntegrableOn f s μ)
  statement: Integrable f (μ.restrict s)
  proof: h

中文:
定理 整数egrableOn.integrable
  条件: (h : 整数egrableOn f s μ)
  结论: 可积 f (μ.restrict s)
  证明: h
-/
theorem IntegrableOn.integrable (h : IntegrableOn f s μ) : Integrable f (μ.restrict s) :=
  h

variable [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

@[simp]
/--
theorem `integrableOn_empty` / 定理 `integrableOn_empty`

English:
theorem integrableOn_empty
  statement: IntegrableOn f ∅ μ
  proof: by
  simp [IntegrableOn]

@[simp]

中文:
定理 integrableOn_empty
  结论: 整数egrableOn f ∅ μ
  证明: by
  simp [IntegrableOn]

@[simp]

Depends on / 依赖: IntegrableOn
-/
theorem integrableOn_empty : IntegrableOn f ∅ μ := by
  simp [IntegrableOn]

@[simp]
/--
theorem `integrableOn_univ` / 定理 `integrableOn_univ`

English:
theorem integrableOn_univ
  statement: IntegrableOn f univ μ ↔ Integrable f μ
  proof: by
  rw [IntegrableOn]; rw [Measure.restrict_univ]

中文:
定理 integrableOn_univ
  结论: 整数egrableOn f univ μ ↔ 可积 f μ
  证明: by
  rw [IntegrableOn]; rw [Measure.restrict_univ]

Depends on / 依赖: IntegrableOn, Measure, Measure.restrict_univ, restrict_univ
-/
theorem integrableOn_univ : IntegrableOn f univ μ ↔ Integrable f μ := by
  rw [IntegrableOn]; rw [Measure.restrict_univ]

/--
theorem `integrableOn_zero` / 定理 `integrableOn_zero`

English:
theorem integrableOn_zero
  statement: IntegrableOn (fun _ => (0 : ε')) s μ
  proof: integrable_zero _ _ _

中文:
定理 integrableOn_zero
  结论: 整数egrableOn (fun _ => (0 : ε')) s μ
  证明: integrable_zero _ _ _

Depends on / 依赖: integrable_zero
-/
theorem integrableOn_zero : IntegrableOn (fun _ => (0 : ε')) s μ :=
  integrable_zero _ _ _

/--
theorem `IntegrableOn.of_measure_zero` / 定理 `IntegrableOn.of_measure_zero`

English:
theorem IntegrableOn.of_measure_zero
  given: (hs : μ s = 0)
  statement: IntegrableOn f s μ
  proof: by
  simp [IntegrableOn, Measure.restrict_eq_zero.2 hs]

@[simp]

中文:
定理 整数egrableOn.of_measure_zero
  条件: (hs : μ s = 0)
  结论: 整数egrableOn f s μ
  证明: by
  simp [IntegrableOn, Measure.restrict_eq_zero.2 hs]

@[simp]

Depends on / 依赖: IntegrableOn, Measure, Measure.restrict_eq_zero, restrict_eq_zero
-/
theorem IntegrableOn.of_measure_zero (hs : μ s = 0) : IntegrableOn f s μ := by
  simp [IntegrableOn, Measure.restrict_eq_zero.2 hs]

@[simp]
/--
theorem `integrableOn_const_iff` / 定理 `integrableOn_const_iff`

English:
theorem integrableOn_const_iff
  given: {C : ε'} (hC : ‖C‖ₑ != ∞ := by finiteness)
  proof: by
  rw [IntegrableOn]; rw [integrable_const_iff_enorm hC]; rw [isFiniteMeasure_restrict]; rw [lt_top_iff_ne_top]

中文:
定理 integrableOn_const_iff
  条件: {C : ε'} (hC : ‖C‖ₑ != ∞ := by finiteness)
  证明: by
  rw [IntegrableOn]; rw [integrable_const_iff_enorm hC]; rw [isFiniteMeasure_restrict]; rw [lt_top_iff_ne_top]

Depends on / 依赖: IntegrableOn, finiteness, integrable_const_iff_enorm, isFiniteMeasure_restrict, lt_top_iff_ne_top
-/
theorem integrableOn_const_iff {C : ε'} (hC : ‖C‖ₑ != ∞ := by finiteness) :
    IntegrableOn (fun _ => C) s μ ↔ ‖C‖ₑ = 0 ∨ μ s < ∞ := by
  rw [IntegrableOn]; rw [integrable_const_iff_enorm hC]; rw [isFiniteMeasure_restrict]; rw [lt_top_iff_ne_top]

/--
theorem `integrableOn_const` / 定理 `integrableOn_const`

English:
theorem integrableOn_const
  statement: {C : ε'} (hs : μ s != ∞ := by finiteness)
  proof: (integrableOn_const_iff hC).2 Or.inr lt_top_iff_ne_top.2 hs

@[gcongr]

中文:
定理 integrableOn_const
  结论: {C : ε'} (hs : μ s != ∞ := by finiteness)
  证明: (integrableOn_const_iff hC).2 Or.inr lt_top_iff_ne_top.2 hs

@[gcongr]

Depends on / 依赖: IntegrableOn, Or.inr, finiteness, integrableOn_const_iff, lt_top_iff_ne_top
-/
theorem integrableOn_const {C : ε'} (hs : μ s != ∞ := by finiteness)
    (hC : ‖C‖ₑ != ∞ := by finiteness) : IntegrableOn (fun _ => C) s μ :=
(integrableOn_const_iff hC).2 Or.inr lt_top_iff_ne_top.2 hs

@[gcongr]
/--
theorem `IntegrableOn.mono` / 定理 `IntegrableOn.mono`

English:
theorem IntegrableOn.mono
  given: (h : IntegrableOn f t ν) (hs : s subseteq t) (hμ : μ <= ν)
  statement: IntegrableOn f s μ
  proof: h.mono_measure Measure.restrict_mono hs hμ

@[gcongr]

中文:
定理 整数egrableOn.mono
  条件: (h : 整数egrableOn f t ν) (hs : s subseteq t) (hμ : μ <= ν)
  结论: 整数egrableOn f s μ
  证明: h.mono_measure Measure.restrict_mono hs hμ

@[gcongr]

Depends on / 依赖: Measure, Measure.restrict_mono, h.mono_measure, mono_measure, restrict_mono
-/
theorem IntegrableOn.mono (h : IntegrableOn f t ν) (hs : s subseteq t) (hμ : μ <= ν) : IntegrableOn f s μ :=
h.mono_measure Measure.restrict_mono hs hμ

@[gcongr]
/--
theorem `IntegrableOn.mono_set` / 定理 `IntegrableOn.mono_set`

English:
theorem IntegrableOn.mono_set
  given: (h : IntegrableOn f t μ) (hst : s subseteq t)
  statement: IntegrableOn f s μ
  proof: h.mono hst le_rfl

中文:
定理 整数egrableOn.mono_set
  条件: (h : 整数egrableOn f t μ) (hst : s subseteq t)
  结论: 整数egrableOn f s μ
  证明: h.mono hst le_rfl

Depends on / 依赖: h.mono, le_rfl
-/
theorem IntegrableOn.mono_set (h : IntegrableOn f t μ) (hst : s subseteq t) : IntegrableOn f s μ :=
  h.mono hst le_rfl

/--
theorem `IntegrableOn.mono_measure` / 定理 `IntegrableOn.mono_measure`

English:
theorem IntegrableOn.mono_measure
  given: (h : IntegrableOn f s ν) (hμ : μ <= ν)
  statement: IntegrableOn f s μ
  proof: h.mono (Subset.refl _) hμ

中文:
定理 整数egrableOn.mono_measure
  条件: (h : 整数egrableOn f s ν) (hμ : μ <= ν)
  结论: 整数egrableOn f s μ
  证明: h.mono (Subset.refl _) hμ

Depends on / 依赖: Subset, Subset.refl, h.mono
-/
theorem IntegrableOn.mono_measure (h : IntegrableOn f s ν) (hμ : μ <= ν) : IntegrableOn f s μ :=
  h.mono (Subset.refl _) hμ

/--
theorem `IntegrableOn.mono_measure'` / 定理 `IntegrableOn.mono_measure'`

English:
theorem IntegrableOn.mono_measure'
  given: (h : IntegrableOn f s ν) (hμ : μ.restrict s <= ν.restrict s)
  proof: Integrable.mono_measure h hμ

中文:
定理 整数egrableOn.mono_measure'
  条件: (h : 整数egrableOn f s ν) (hμ : μ.restrict s <= ν.restrict s)
  证明: Integrable.mono_measure h hμ

Depends on / 依赖: Integrable, Integrable.mono_measure, mono_measure
-/
theorem IntegrableOn.mono_measure' (h : IntegrableOn f s ν) (hμ : μ.restrict s <= ν.restrict s) :
    IntegrableOn f s μ :=
  Integrable.mono_measure h hμ

/--
theorem `IntegrableOn.mono_set_ae` / 定理 `IntegrableOn.mono_set_ae`

English:
theorem IntegrableOn.mono_set_ae
  given: (h : IntegrableOn f t μ) (hst : s <=ᵐ[μ] t)
  statement: IntegrableOn f s μ
  proof: h.integrable.mono_measure Measure.restrict_mono_ae hst

中文:
定理 整数egrableOn.mono_set_ae
  条件: (h : 整数egrableOn f t μ) (hst : s <=ᵐ[μ] t)
  结论: 整数egrableOn f s μ
  证明: h.integrable.mono_measure Measure.restrict_mono_ae hst

Depends on / 依赖: Measure, Measure.restrict_mono_ae, h.integrable.mono_measure, integrable, mono_measure, restrict_mono_ae
-/
theorem IntegrableOn.mono_set_ae (h : IntegrableOn f t μ) (hst : s <=ᵐ[μ] t) : IntegrableOn f s μ :=
h.integrable.mono_measure Measure.restrict_mono_ae hst

/--
theorem `IntegrableOn.congr_set_ae` / 定理 `IntegrableOn.congr_set_ae`

English:
theorem IntegrableOn.congr_set_ae
  given: (h : IntegrableOn f t μ) (hst : s =ᵐ[μ] t)
  statement: IntegrableOn f s μ
  proof: h.mono_set_ae hst.le

中文:
定理 整数egrableOn.congr_set_ae
  条件: (h : 整数egrableOn f t μ) (hst : s =ᵐ[μ] t)
  结论: 整数egrableOn f s μ
  证明: h.mono_set_ae hst.le

Depends on / 依赖: h.mono_set_ae, hst.le, mono_set_ae
-/
theorem IntegrableOn.congr_set_ae (h : IntegrableOn f t μ) (hst : s =ᵐ[μ] t) : IntegrableOn f s μ :=
  h.mono_set_ae hst.le

/--
theorem `integrableOn_congr_set_ae` / 定理 `integrableOn_congr_set_ae`

English:
theorem integrableOn_congr_set_ae
  given: (hst : s =ᵐ[μ] t)
  statement: IntegrableOn f s μ ↔ IntegrableOn f t μ
  proof: ⟨fun h => h.congr_set_ae hst.symm, fun h => h.congr_set_ae hst⟩

中文:
定理 integrableOn_congr_set_ae
  条件: (hst : s =ᵐ[μ] t)
  结论: 整数egrableOn f s μ ↔ 整数egrableOn f t μ
  证明: ⟨fun h => h.congr_set_ae hst.symm, fun h => h.congr_set_ae hst⟩

Depends on / 依赖: congr_set_ae, h.congr_set_ae, hst.symm
-/
theorem integrableOn_congr_set_ae (hst : s =ᵐ[μ] t) : IntegrableOn f s μ ↔ IntegrableOn f t μ :=
  ⟨fun h => h.congr_set_ae hst.symm, fun h => h.congr_set_ae hst⟩

/--
theorem `IntegrableOn.congr_fun_ae` / 定理 `IntegrableOn.congr_fun_ae`

English:
theorem IntegrableOn.congr_fun_ae
  given: (h : IntegrableOn f s μ) (hst : f =ᵐ[μ.restrict s] g)
  proof: Integrable.congr h hst

@[gcongr]

中文:
定理 整数egrableOn.congr_fun_ae
  条件: (h : 整数egrableOn f s μ) (hst : f =ᵐ[μ.restrict s] g)
  证明: Integrable.congr h hst

@[gcongr]

Depends on / 依赖: Integrable, Integrable.congr
-/
theorem IntegrableOn.congr_fun_ae (h : IntegrableOn f s μ) (hst : f =ᵐ[μ.restrict s] g) :
    IntegrableOn g s μ :=
  Integrable.congr h hst

@[gcongr]
/--
theorem `integrableOn_congr_fun_ae` / 定理 `integrableOn_congr_fun_ae`

English:
theorem integrableOn_congr_fun_ae
  given: (hst : f =ᵐ[μ.restrict s] g)
  proof: ⟨fun h => h.congr_fun_ae hst, fun h => h.congr_fun_ae hst.symm⟩

中文:
定理 integrableOn_congr_fun_ae
  条件: (hst : f =ᵐ[μ.restrict s] g)
  证明: ⟨fun h => h.congr_fun_ae hst, fun h => h.congr_fun_ae hst.symm⟩

Depends on / 依赖: congr_fun_ae, h.congr_fun_ae, hst.symm
-/
theorem integrableOn_congr_fun_ae (hst : f =ᵐ[μ.restrict s] g) :
    IntegrableOn f s μ ↔ IntegrableOn g s μ :=
  ⟨fun h => h.congr_fun_ae hst, fun h => h.congr_fun_ae hst.symm⟩

/--
theorem `IntegrableOn.congr_fun` / 定理 `IntegrableOn.congr_fun`

English:
theorem IntegrableOn.congr_fun
  given: (h : IntegrableOn f s μ) (hst : EqOn f g s) (hs : MeasurableSet s)
  proof: h.congr_fun_ae ((ae_restrict_iff' hs).2 (Eventually.of_forall hst))

中文:
定理 整数egrableOn.congr_fun
  条件: (h : 整数egrableOn f s μ) (hst : EqOn f g s) (hs : 可测集 s)
  证明: h.congr_fun_ae ((ae_restrict_iff' hs).2 (Eventually.of_forall hst))

Depends on / 依赖: Eventually, Eventually.of_forall, ae_restrict_iff, congr_fun_ae, h.congr_fun_ae, of_forall
-/
theorem IntegrableOn.congr_fun (h : IntegrableOn f s μ) (hst : EqOn f g s) (hs : MeasurableSet s) :
    IntegrableOn g s μ :=
  h.congr_fun_ae ((ae_restrict_iff' hs).2 (Eventually.of_forall hst))

/--
theorem `integrableOn_congr_fun` / 定理 `integrableOn_congr_fun`

English:
theorem integrableOn_congr_fun
  given: (hst : EqOn f g s) (hs : MeasurableSet s)
  proof: ⟨fun h => h.congr_fun hst hs, fun h => h.congr_fun hst.symm hs⟩

中文:
定理 integrableOn_congr_fun
  条件: (hst : EqOn f g s) (hs : 可测集 s)
  证明: ⟨fun h => h.congr_fun hst hs, fun h => h.congr_fun hst.symm hs⟩

Depends on / 依赖: congr_fun, h.congr_fun, hst.symm
-/
theorem integrableOn_congr_fun (hst : EqOn f g s) (hs : MeasurableSet s) :
    IntegrableOn f s μ ↔ IntegrableOn g s μ :=
  ⟨fun h => h.congr_fun hst hs, fun h => h.congr_fun hst.symm hs⟩

/--
theorem `Integrable.integrableOn` / 定理 `Integrable.integrableOn`

English:
theorem Integrable.integrableOn
  given: (h : Integrable f μ)
  statement: IntegrableOn f s μ
  proof: h.restrict

@[simp]

中文:
定理 可积.integrableOn
  条件: (h : 可积 f μ)
  结论: 整数egrableOn f s μ
  证明: h.restrict

@[simp]

Depends on / 依赖: h.restrict, restrict
-/
theorem Integrable.integrableOn (h : Integrable f μ) : IntegrableOn f s μ := h.restrict

@[simp]
/--
lemma `IntegrableOn.of_subsingleton_codomain` / 引理 `IntegrableOn.of_subsingleton_codomain`

English:
lemma IntegrableOn.of_subsingleton_codomain
  given: [Subsingleton ε'] {f : α -> ε'}
  proof: Integrable.of_subsingleton_codomain

中文:
引理 整数egrableOn.of_subsingleton_codomain
  条件: [子单例 ε'] {f : α -> ε'}
  证明: Integrable.of_subsingleton_codomain

Depends on / 依赖: Integrable, Integrable.of_subsingleton_codomain, of_subsingleton_codomain
-/
lemma IntegrableOn.of_subsingleton_codomain [Subsingleton ε'] {f : α -> ε'} :
    IntegrableOn f s μ :=
  Integrable.of_subsingleton_codomain

/--
lemma `Integrable.of_bound` / 引理 `Integrable.of_bound`

English:
lemma Integrable.of_bound
  statement: [IsFiniteMeasure μ] {f : α -> E} (hf : AEStronglyMeasurable f μ) (C : Real)
  proof: ⟨hf, .of_bounded hfC⟩

中文:
引理 可积.of_bound
  结论: [是有限测度 μ] {f : α -> E} (hf : AEStronglyMeasurable f μ) (C : 实数)
  证明: ⟨hf, .of_bounded hfC⟩

Depends on / 依赖: of_bounded
-/
lemma Integrable.of_bound [IsFiniteMeasure μ] {f : α -> E} (hf : AEStronglyMeasurable f μ) (C : Real)
    (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : Integrable f μ := ⟨hf, .of_bounded hfC⟩

/--
lemma `IntegrableOn.of_bound` / 引理 `IntegrableOn.of_bound`

English:
lemma IntegrableOn.of_bound
  statement: (hs : μ s < ∞) {f : α -> E} (hf : AEStronglyMeasurable f (μ.restrict s))
  proof: ⟨hf, .restrict_of_bounded C hs hfC⟩

中文:
引理 整数egrableOn.of_bound
  结论: (hs : μ s < ∞) {f : α -> E} (hf : AEStronglyMeasurable f (μ.restrict s))
  证明: ⟨hf, .restrict_of_bounded C hs hfC⟩

Depends on / 依赖: restrict_of_bounded
-/
lemma IntegrableOn.of_bound (hs : μ s < ∞) {f : α -> E} (hf : AEStronglyMeasurable f (μ.restrict s))
    (C : Real) (hfC : forallᵐ x ∂μ.restrict s, ‖f x‖ <= C) : IntegrableOn f s μ :=
  ⟨hf, .restrict_of_bounded C hs hfC⟩

/--
theorem `IntegrableOn.restrict` / 定理 `IntegrableOn.restrict`

English:
theorem IntegrableOn.restrict
  given: (h : IntegrableOn f s μ)
  statement: IntegrableOn f s (μ.restrict t)
  proof: by
  dsimp only [IntegrableOn] at h ⊢
exact h.mono_measure Measure.restrict_mono_measure Measure.restrict_le_self _

中文:
定理 整数egrableOn.restrict
  条件: (h : 整数egrableOn f s μ)
  结论: 整数egrableOn f s (μ.restrict t)
  证明: by
  dsimp only [IntegrableOn] at h ⊢
exact h.mono_measure Measure.restrict_mono_measure Measure.restrict_le_self _

Depends on / 依赖: IntegrableOn, Measure, Measure.restrict_le_self, Measure.restrict_mono_measure, h.mono_measure, mono_measure, restrict_le_self, restrict_mono_measure
-/
theorem IntegrableOn.restrict (h : IntegrableOn f s μ) : IntegrableOn f s (μ.restrict t) := by
  dsimp only [IntegrableOn] at h ⊢
exact h.mono_measure Measure.restrict_mono_measure Measure.restrict_le_self _

/--
theorem `IntegrableOn.inter_of_restrict` / 定理 `IntegrableOn.inter_of_restrict`

English:
theorem IntegrableOn.inter_of_restrict
  given: (h : IntegrableOn f s (μ.restrict t))
  proof: by
  have := h.mono_set (inter_subset_left (t := t))
  rwa [IntegrableOn, μ.restrict_restrict_of_subset inter_subset_right] at this

中文:
定理 整数egrableOn.inter_of_restrict
  条件: (h : 整数egrableOn f s (μ.restrict t))
  证明: by
  have := h.mono_set (inter_subset_left (t := t))
  rwa [IntegrableOn, μ.restrict_restrict_of_subset inter_subset_right] at this

Depends on / 依赖: IntegrableOn, h.mono_set, inter_subset_left, inter_subset_right, mono_set, restrict_restrict_of_subset
-/
theorem IntegrableOn.inter_of_restrict (h : IntegrableOn f s (μ.restrict t)) :
    IntegrableOn f (s inter t) μ := by
  have := h.mono_set (inter_subset_left (t := t))
  rwa [IntegrableOn, μ.restrict_restrict_of_subset inter_subset_right] at this

/--
lemma `Integrable.piecewise` / 引理 `Integrable.piecewise`

English:
lemma Integrable.piecewise
  statement: {f g : α -> ε'} [DecidablePred (· in s)]
  proof: by
  rw [IntegrableOn] at hf hg
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact MemLp.piecewise hs hf hg

中文:
引理 可积.piecewise
  结论: {f g : α -> ε'} [DecidablePred (· in s)]
  证明: by
  rw [IntegrableOn] at hf hg
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact MemLp.piecewise hs hf hg

Depends on / 依赖: IntegrableOn, MemLp.piecewise, memLp_one_iff_integrable, piecewise
-/
lemma Integrable.piecewise {f g : α -> ε'} [DecidablePred (· in s)]
    (hs : MeasurableSet s) (hf : IntegrableOn f s μ) (hg : IntegrableOn g sᶜ μ) :
    Integrable (s.piecewise f g) μ := by
  rw [IntegrableOn] at hf hg
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact MemLp.piecewise hs hf hg

/--
theorem `IntegrableOn.left_of_union` / 定理 `IntegrableOn.left_of_union`

English:
theorem IntegrableOn.left_of_union
  given: (h : IntegrableOn f (s union t) μ)
  statement: IntegrableOn f s μ
  proof: h.mono_set subset_union_left

中文:
定理 整数egrableOn.left_of_union
  条件: (h : 整数egrableOn f (s union t) μ)
  结论: 整数egrableOn f s μ
  证明: h.mono_set subset_union_left

Depends on / 依赖: h.mono_set, mono_set, subset_union_left
-/
theorem IntegrableOn.left_of_union (h : IntegrableOn f (s union t) μ) : IntegrableOn f s μ :=
  h.mono_set subset_union_left

/--
theorem `IntegrableOn.right_of_union` / 定理 `IntegrableOn.right_of_union`

English:
theorem IntegrableOn.right_of_union
  given: (h : IntegrableOn f (s union t) μ)
  statement: IntegrableOn f t μ
  proof: h.mono_set subset_union_right

中文:
定理 整数egrableOn.right_of_union
  条件: (h : 整数egrableOn f (s union t) μ)
  结论: 整数egrableOn f t μ
  证明: h.mono_set subset_union_right

Depends on / 依赖: h.mono_set, mono_set, subset_union_right
-/
theorem IntegrableOn.right_of_union (h : IntegrableOn f (s union t) μ) : IntegrableOn f t μ :=
  h.mono_set subset_union_right

/--
theorem `IntegrableOn.union` / 定理 `IntegrableOn.union`

English:
theorem IntegrableOn.union
  statement: [PseudoMetrizableSpace ε]
  proof: (hs.add_measure ht).mono_measure Measure.restrict_union_le _ _

@[simp]

中文:
定理 整数egrableOn.union
  结论: [PseudoMetrizable空间 ε]
  证明: (hs.add_measure ht).mono_measure Measure.restrict_union_le _ _

@[simp]

Depends on / 依赖: Measure, Measure.restrict_union_le, add_measure, hs.add_measure, mono_measure, restrict_union_le
-/
theorem IntegrableOn.union [PseudoMetrizableSpace ε]
    (hs : IntegrableOn f s μ) (ht : IntegrableOn f t μ) :
    IntegrableOn f (s union t) μ :=
(hs.add_measure ht).mono_measure Measure.restrict_union_le _ _

@[simp]
/--
theorem `integrableOn_union` / 定理 `integrableOn_union`

English:
theorem integrableOn_union
  given: [PseudoMetrizableSpace ε]
  proof: ⟨fun h => ⟨h.left_of_union, h.right_of_union⟩, fun h => h.1.union h.2⟩

@[simp]

中文:
定理 integrableOn_union
  条件: [PseudoMetrizable空间 ε]
  证明: ⟨fun h => ⟨h.left_of_union, h.right_of_union⟩, fun h => h.1.union h.2⟩

@[simp]

Depends on / 依赖: h.left_of_union, h.right_of_union, left_of_union, right_of_union
-/
theorem integrableOn_union [PseudoMetrizableSpace ε] :
    IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ :=
  ⟨fun h => ⟨h.left_of_union, h.right_of_union⟩, fun h => h.1.union h.2⟩

@[simp]
/--
theorem `integrableOn_singleton_iff` / 定理 `integrableOn_singleton_iff`

English:
theorem integrableOn_singleton_iff
  statement: {f : α -> ε'} {x : α}
  proof: by
  have : f =ᵐ[μ.restrict {x}] fun _ => f x := by
    filter_upwards [ae_restrict_mem (measurableSet_singleton x)] with _ ha
    simp only [mem_singleton_iff.1 ha]
  rw [IntegrableOn]; rw [integrable_congr this]; rw [integrable_const_iff_enorm]; rw [isFiniteMeasure_restrict]; rw [lt_top_iff_ne_top]
  exact hfx

中文:
定理 integrableOn_singleton_iff
  结论: {f : α -> ε'} {x : α}
  证明: by
  have : f =ᵐ[μ.restrict {x}] fun _ => f x := by
    filter_upwards [ae_restrict_mem (measurableSet_singleton x)] with _ ha
    simp only [mem_singleton_iff.1 ha]
  rw [IntegrableOn]; rw [integrable_congr this]; rw [integrable_const_iff_enorm]; rw [isFiniteMeasure_restrict]; rw [lt_top_iff_ne_top]
  exact hfx

Depends on / 依赖: IntegrableOn, ae_restrict_mem, filter_upwards, finiteness, integrable_congr, integrable_const_iff_enorm, isFiniteMeasure_restrict, lt_top_iff_ne_top, measurableSet_singleton, mem_singleton_iff, restrict
-/
theorem integrableOn_singleton_iff {f : α -> ε'} {x : α}
    [MeasurableSingletonClass α] (hfx : ‖f x‖ₑ != ⊤ := by finiteness) :
    IntegrableOn f {x} μ ↔ ‖f x‖ₑ = 0 ∨ μ {x} < ∞ := by
  have : f =ᵐ[μ.restrict {x}] fun _ => f x := by
    filter_upwards [ae_restrict_mem (measurableSet_singleton x)] with _ ha
    simp only [mem_singleton_iff.1 ha]
  rw [IntegrableOn]; rw [integrable_congr this]; rw [integrable_const_iff_enorm]; rw [isFiniteMeasure_restrict]; rw [lt_top_iff_ne_top]
  exact hfx

/--
theorem `integrableOn_singleton` / 定理 `integrableOn_singleton`

English:
theorem integrableOn_singleton
  statement: {f : α -> ε'} {x : α} [MeasurableSingletonClass α]
  proof: (integrableOn_singleton_iff hfx).mpr (Or.inr hx)

@[simp]

中文:
定理 integrableOn_singleton
  结论: {f : α -> ε'} {x : α} [MeasurableSingleton类 α]
  证明: (integrableOn_singleton_iff hfx).mpr (Or.inr hx)

@[simp]

Depends on / 依赖: IntegrableOn, Or.inr, finiteness, integrableOn_singleton_iff
-/
theorem integrableOn_singleton {f : α -> ε'} {x : α} [MeasurableSingletonClass α]
    (hfx : ‖f x‖ₑ != ⊤ := by finiteness) (hx : μ {x} < ∞ := by finiteness) : IntegrableOn f {x} μ :=
  (integrableOn_singleton_iff hfx).mpr (Or.inr hx)

@[simp]
/--
theorem `integrableOn_finite_biUnion` / 定理 `integrableOn_finite_biUnion`

English:
theorem integrableOn_finite_biUnion
  statement: [PseudoMetrizableSpace ε]
  proof: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hf => simp [hf, or_imp, forall_and]

@[simp]

中文:
定理 integrableOn_finite_biUnion
  结论: [PseudoMetrizable空间 ε]
  证明: by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hf => simp [hf, or_imp, forall_and]

@[simp]

Depends on / 依赖: Finite, Set.Finite.induction_on, forall_and, induction_on, insert, or_imp
-/
theorem integrableOn_finite_biUnion [PseudoMetrizableSpace ε]
    {s : Set β} (hs : s.Finite) {t : β -> Set α} :
    IntegrableOn f (⋃ i in s, t i) μ ↔ forall i in s, IntegrableOn f (t i) μ := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hf => simp [hf, or_imp, forall_and]

@[simp]
/--
theorem `integrableOn_finset_iUnion` / 定理 `integrableOn_finset_iUnion`

English:
theorem integrableOn_finset_iUnion
  given: [PseudoMetrizableSpace ε] {s : Finset β} {t : β -> Set α}
  proof: integrableOn_finite_biUnion s.finite_toSet

@[simp]

中文:
定理 integrableOn_finset_iUnion
  条件: [PseudoMetrizable空间 ε] {s : 有限集 β} {t : β -> 集合 α}
  证明: integrableOn_finite_biUnion s.finite_toSet

@[simp]

Depends on / 依赖: finite_toSet, integrableOn_finite_biUnion, s.finite_toSet
-/
theorem integrableOn_finset_iUnion [PseudoMetrizableSpace ε] {s : Finset β} {t : β -> Set α} :
    IntegrableOn f (⋃ i in s, t i) μ ↔ forall i in s, IntegrableOn f (t i) μ :=
  integrableOn_finite_biUnion s.finite_toSet

@[simp]
/--
theorem `integrableOn_finite_iUnion` / 定理 `integrableOn_finite_iUnion`

English:
theorem integrableOn_finite_iUnion
  given: [PseudoMetrizableSpace ε] [Finite β] {t : β -> Set α}
  proof: by
  cases nonempty_fintype β
  simpa using integrableOn_finset_iUnion (f := f) (μ := μ) (s := Finset.univ) (t := t)

中文:
定理 integrableOn_finite_iUnion
  条件: [PseudoMetrizable空间 ε] [有限 β] {t : β -> 集合 α}
  证明: by
  cases nonempty_fintype β
  simpa using integrableOn_finset_iUnion (f := f) (μ := μ) (s := Finset.univ) (t := t)

Depends on / 依赖: Finset, Finset.univ, integrableOn_finset_iUnion, nonempty_fintype
-/
theorem integrableOn_finite_iUnion [PseudoMetrizableSpace ε] [Finite β] {t : β -> Set α} :
    IntegrableOn f (⋃ i, t i) μ ↔ forall i, IntegrableOn f (t i) μ := by
  cases nonempty_fintype β
  simpa using integrableOn_finset_iUnion (f := f) (μ := μ) (s := Finset.univ) (t := t)

-- TODO: generalise this lemma and the next to enorm classes; this entails assuming that
-- f is finite on almost every element of `s`
/--
lemma `IntegrableOn.finset` / 引理 `IntegrableOn.finset`

English:
lemma IntegrableOn.finset
  statement: [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
  proof: by
  rw [← (s : Set α).biUnion_of_singleton]
  simp [integrableOn_finset_iUnion, measure_lt_top]

中文:
引理 整数egrableOn.finset
  结论: [MeasurableSingleton类 α] {μ : 测度 α} [是有限测度 μ]
  证明: by
  rw [← (s : Set α).biUnion_of_singleton]
  simp [integrableOn_finset_iUnion, measure_lt_top]

Depends on / 依赖: biUnion_of_singleton, integrableOn_finset_iUnion, measure_lt_top
-/
lemma IntegrableOn.finset [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    {s : Finset α} {f : α -> E} : IntegrableOn f s μ := by
  rw [← (s : Set α).biUnion_of_singleton]
  simp [integrableOn_finset_iUnion, measure_lt_top]

/--
lemma `IntegrableOn.of_finite` / 引理 `IntegrableOn.of_finite`

English:
lemma IntegrableOn.of_finite
  statement: [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
  proof: by
  simpa using IntegrableOn.finset (s := hs.toFinset)

中文:
引理 整数egrableOn.of_finite
  结论: [MeasurableSingleton类 α] {μ : 测度 α} [是有限测度 μ]
  证明: by
  simpa using IntegrableOn.finset (s := hs.toFinset)

Depends on / 依赖: IntegrableOn, IntegrableOn.finset, finset, hs.toFinset, toFinset
-/
lemma IntegrableOn.of_finite [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    {s : Set α} (hs : s.Finite) {f : α -> E} : IntegrableOn f s μ := by
  simpa using IntegrableOn.finset (s := hs.toFinset)

/--
lemma `IntegrableOn.of_subsingleton` / 引理 `IntegrableOn.of_subsingleton`

English:
lemma IntegrableOn.of_subsingleton
  statement: [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
  proof: .of_finite hs.finite

中文:
引理 整数egrableOn.of_subsingleton
  结论: [MeasurableSingleton类 α] {μ : 测度 α} [是有限测度 μ]
  证明: .of_finite hs.finite

Depends on / 依赖: finite, hs.finite, of_finite
-/
lemma IntegrableOn.of_subsingleton [MeasurableSingletonClass α] {μ : Measure α} [IsFiniteMeasure μ]
    {s : Set α} (hs : s.Subsingleton) {f : α -> E} :
    IntegrableOn f s μ :=
  .of_finite hs.finite

/--
theorem `IntegrableOn.add_measure` / 定理 `IntegrableOn.add_measure`

English:
theorem IntegrableOn.add_measure
  statement: [PseudoMetrizableSpace ε]
  proof: by
  delta IntegrableOn; rw [Measure.restrict_add]; exact hμ.integrable.add_measure hν

@[to_fun]

中文:
定理 整数egrableOn.add_measure
  结论: [PseudoMetrizable空间 ε]
  证明: by
  delta IntegrableOn; rw [Measure.restrict_add]; exact hμ.integrable.add_measure hν

@[to_fun]

Depends on / 依赖: IntegrableOn, Measure, Measure.restrict_add, add_measure, integrable, integrable.add_measure, restrict_add
-/
theorem IntegrableOn.add_measure [PseudoMetrizableSpace ε]
    (hμ : IntegrableOn f s μ) (hν : IntegrableOn f s ν) :
    IntegrableOn f s (μ + ν) := by
  delta IntegrableOn; rw [Measure.restrict_add]; exact hμ.integrable.add_measure hν

@[to_fun]
/--
theorem `IntegrableOn.add` / 定理 `IntegrableOn.add`

English:
theorem IntegrableOn.add
  statement: [ContinuousAdd ε'] {f g : α -> ε'}
  proof: Integrable.add hf hg

@[to_fun]

中文:
定理 整数egrableOn.add
  结论: [连续加法 ε'] {f g : α -> ε'}
  证明: Integrable.add hf hg

@[to_fun]

Depends on / 依赖: Integrable, Integrable.add
-/
theorem IntegrableOn.add [ContinuousAdd ε'] {f g : α -> ε'}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) : IntegrableOn (f + g) s μ :=
  Integrable.add hf hg

@[to_fun]
/--
theorem `IntegrableOn.sub` / 定理 `IntegrableOn.sub`

English:
theorem IntegrableOn.sub
  statement: {f g : α -> E}
  proof: Integrable.sub hf hg

@[to_fun]

中文:
定理 整数egrableOn.sub
  结论: {f g : α -> E}
  证明: Integrable.sub hf hg

@[to_fun]

Depends on / 依赖: Integrable, Integrable.sub
-/
theorem IntegrableOn.sub {f g : α -> E}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) : IntegrableOn (f - g) s μ :=
  Integrable.sub hf hg

@[to_fun]
/--
theorem `IntegrableOn.neg` / 定理 `IntegrableOn.neg`

English:
theorem IntegrableOn.neg
  given: {f : α -> E} (hf : IntegrableOn f s μ)
  statement: IntegrableOn (-f) s μ
  proof: Integrable.neg hf

@[simp]

中文:
定理 整数egrableOn.neg
  条件: {f : α -> E} (hf : 整数egrableOn f s μ)
  结论: 整数egrableOn (-f) s μ
  证明: Integrable.neg hf

@[simp]

Depends on / 依赖: Integrable, Integrable.neg
-/
theorem IntegrableOn.neg {f : α -> E} (hf : IntegrableOn f s μ) : IntegrableOn (-f) s μ :=
  Integrable.neg hf

@[simp]
/--
theorem `integrableOn_neg_iff` / 定理 `integrableOn_neg_iff`

English:
theorem integrableOn_neg_iff
  given: {f : α -> E}
  statement: IntegrableOn (-f) s μ ↔ IntegrableOn f s μ
  proof: integrable_neg_iff

@[simp]

中文:
定理 integrableOn_neg_iff
  条件: {f : α -> E}
  结论: 整数egrableOn (-f) s μ ↔ 整数egrableOn f s μ
  证明: integrable_neg_iff

@[simp]

Depends on / 依赖: integrable_neg_iff
-/
theorem integrableOn_neg_iff {f : α -> E} : IntegrableOn (-f) s μ ↔ IntegrableOn f s μ :=
  integrable_neg_iff

@[simp]
/--
theorem `integrableOn_fun_neg_iff` / 定理 `integrableOn_fun_neg_iff`

English:
theorem integrableOn_fun_neg_iff
  given: {f : α -> E}
  proof: integrable_neg_iff

@[simp]

中文:
定理 integrableOn_fun_neg_iff
  条件: {f : α -> E}
  证明: integrable_neg_iff

@[simp]

Depends on / 依赖: integrable_neg_iff
-/
theorem integrableOn_fun_neg_iff {f : α -> E} :
    IntegrableOn (fun x => -f x) s μ ↔ IntegrableOn f s μ :=
  integrable_neg_iff

@[simp]
/--
theorem `integrableOn_add_measure` / 定理 `integrableOn_add_measure`

English:
theorem integrableOn_add_measure
  given: [PseudoMetrizableSpace ε]
  proof: ⟨fun h =>
    ⟨h.mono_measure (Measure.le_add_right le_rfl), h.mono_measure (Measure.le_add_left le_rfl)⟩,
    fun h => h.1.add_measure h.2⟩

中文:
定理 integrableOn_add_measure
  条件: [PseudoMetrizable空间 ε]
  证明: ⟨fun h =>
    ⟨h.mono_measure (Measure.le_add_right le_rfl), h.mono_measure (Measure.le_add_left le_rfl)⟩,
    fun h => h.1.add_measure h.2⟩

Depends on / 依赖: Measure, Measure.le_add_left, Measure.le_add_right, add_measure, h.mono_measure, le_add_left, le_add_right, le_rfl, mono_measure
-/
theorem integrableOn_add_measure [PseudoMetrizableSpace ε] :
    IntegrableOn f s (μ + ν) ↔ IntegrableOn f s μ ∧ IntegrableOn f s ν :=
  ⟨fun h =>
    ⟨h.mono_measure (Measure.le_add_right le_rfl), h.mono_measure (Measure.le_add_left le_rfl)⟩,
    fun h => h.1.add_measure h.2⟩

/--
theorem `_root_.MeasurableEmbedding.integrableOn_map_iff` / 定理 `_root_.MeasurableEmbedding.integrableOn_map_iff`

English:
theorem _root_.MeasurableEmbedding.integrableOn_map_iff
  statement: [MeasurableSpace β] {e : α -> β}
  proof: by
  simp_rw [IntegrableOn, he.restrict_map, he.integrable_map_iff]

中文:
定理 _root_.可测嵌入.integrableOn_map_iff
  结论: [可测空间 β] {e : α -> β}
  证明: by
  simp_rw [IntegrableOn, he.restrict_map, he.integrable_map_iff]

Depends on / 依赖: IntegrableOn, he.integrable_map_iff, he.restrict_map, integrable_map_iff, restrict_map, simp_rw
-/
theorem _root_.MeasurableEmbedding.integrableOn_map_iff [MeasurableSpace β] {e : α -> β}
    (he : MeasurableEmbedding e) {f : β -> ε} {μ : Measure α} {s : Set β} :
    IntegrableOn f s (μ.map e) ↔ IntegrableOn (f ∘ e) (e ⁻¹' s) μ := by
  simp_rw [IntegrableOn, he.restrict_map, he.integrable_map_iff]

/--
theorem `_root_.MeasurableEmbedding.integrableOn_iff_comap` / 定理 `_root_.MeasurableEmbedding.integrableOn_iff_comap`

English:
theorem _root_.MeasurableEmbedding.integrableOn_iff_comap
  statement: [MeasurableSpace β] {e : α -> β}
  proof: by
  simp_rw [← he.integrableOn_map_iff, he.map_comap, IntegrableOn,
    Measure.restrict_restrict_of_subset hs]

中文:
定理 _root_.可测嵌入.integrableOn_iff_comap
  结论: [可测空间 β] {e : α -> β}
  证明: by
  simp_rw [← he.integrableOn_map_iff, he.map_comap, IntegrableOn,
    Measure.restrict_restrict_of_subset hs]

Depends on / 依赖: IntegrableOn, Measure, Measure.restrict_restrict_of_subset, he.integrableOn_map_iff, he.map_comap, integrableOn_map_iff, map_comap, restrict_restrict_of_subset, simp_rw
-/
theorem _root_.MeasurableEmbedding.integrableOn_iff_comap [MeasurableSpace β] {e : α -> β}
    (he : MeasurableEmbedding e) {f : β -> ε} {μ : Measure β} {s : Set β} (hs : s subseteq range e) :
    IntegrableOn f s μ ↔ IntegrableOn (f ∘ e) (e ⁻¹' s) (μ.comap e) := by
  simp_rw [← he.integrableOn_map_iff, he.map_comap, IntegrableOn,
    Measure.restrict_restrict_of_subset hs]

/--
theorem `_root_.MeasurableEmbedding.integrableOn_range_iff_comap` / 定理 `_root_.MeasurableEmbedding.integrableOn_range_iff_comap`

English:
theorem _root_.MeasurableEmbedding.integrableOn_range_iff_comap
  statement: [MeasurableSpace β] {e : α -> β}
  proof: by
  rw [he.integrableOn_iff_comap .rfl]; rw [preimage_range]; rw [integrableOn_univ]

中文:
定理 _root_.可测嵌入.integrableOn_range_iff_comap
  结论: [可测空间 β] {e : α -> β}
  证明: by
  rw [he.integrableOn_iff_comap .rfl]; rw [preimage_range]; rw [integrableOn_univ]

Depends on / 依赖: he.integrableOn_iff_comap, integrableOn_iff_comap, integrableOn_univ, preimage_range
-/
theorem _root_.MeasurableEmbedding.integrableOn_range_iff_comap [MeasurableSpace β] {e : α -> β}
    (he : MeasurableEmbedding e) {f : β -> ε} {μ : Measure β} :
    IntegrableOn f (range e) μ ↔ Integrable (f ∘ e) (μ.comap e) := by
  rw [he.integrableOn_iff_comap .rfl]; rw [preimage_range]; rw [integrableOn_univ]

/--
theorem `integrableOn_iff_comap_subtypeVal` / 定理 `integrableOn_iff_comap_subtypeVal`

English:
theorem integrableOn_iff_comap_subtypeVal
  given: (hs : MeasurableSet s)
  proof: by
  rw [← (MeasurableEmbedding.subtype_coe hs).integrableOn_range_iff_comap]; rw [Subtype.range_val]

中文:
定理 integrableOn_iff_comap_subtypeVal
  条件: (hs : 可测集 s)
  证明: by
  rw [← (MeasurableEmbedding.subtype_coe hs).integrableOn_range_iff_comap]; rw [Subtype.range_val]

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, Subtype, Subtype.range_val, integrableOn_range_iff_comap, range_val, subtype_coe
-/
theorem integrableOn_iff_comap_subtypeVal (hs : MeasurableSet s) :
    IntegrableOn f s μ ↔ Integrable (f ∘ (↑) : s -> ε) (μ.comap (↑)) := by
  rw [← (MeasurableEmbedding.subtype_coe hs).integrableOn_range_iff_comap]; rw [Subtype.range_val]

/--
theorem `integrableOn_map_equiv` / 定理 `integrableOn_map_equiv`

English:
theorem integrableOn_map_equiv
  statement: [MeasurableSpace β] (e : α ≃ᵐ β) {f : β -> ε} {μ : Measure α}
  proof: by
  simp only [IntegrableOn, e.restrict_map, integrable_map_equiv e]

中文:
定理 integrableOn_map_equiv
  结论: [可测空间 β] (e : α ≃ᵐ β) {f : β -> ε} {μ : 测度 α}
  证明: by
  simp only [IntegrableOn, e.restrict_map, integrable_map_equiv e]

Depends on / 依赖: IntegrableOn, e.restrict_map, integrable_map_equiv, restrict_map
-/
theorem integrableOn_map_equiv [MeasurableSpace β] (e : α ≃ᵐ β) {f : β -> ε} {μ : Measure α}
    {s : Set β} : IntegrableOn f s (μ.map e) ↔ IntegrableOn (f ∘ e) (e ⁻¹' s) μ := by
  simp only [IntegrableOn, e.restrict_map, integrable_map_equiv e]

/--
theorem `MeasurePreserving.integrableOn_comp_preimage` / 定理 `MeasurePreserving.integrableOn_comp_preimage`

English:
theorem MeasurePreserving.integrableOn_comp_preimage
  statement: [MeasurableSpace β] {e : α -> β} {ν}
  proof: (h₁.restrict_preimage_emb h₂ s).integrable_comp_emb h₂

中文:
定理 保测.integrableOn_comp_preimage
  结论: [可测空间 β] {e : α -> β} {ν}
  证明: (h₁.restrict_preimage_emb h₂ s).integrable_comp_emb h₂

Depends on / 依赖: integrable_comp_emb, restrict_preimage_emb
-/
theorem MeasurePreserving.integrableOn_comp_preimage [MeasurableSpace β] {e : α -> β} {ν}
    (h₁ : MeasurePreserving e μ ν) (h₂ : MeasurableEmbedding e) {f : β -> ε} {s : Set β} :
    IntegrableOn (f ∘ e) (e ⁻¹' s) μ ↔ IntegrableOn f s ν :=
  (h₁.restrict_preimage_emb h₂ s).integrable_comp_emb h₂

/--
theorem `MeasurePreserving.integrableOn_image` / 定理 `MeasurePreserving.integrableOn_image`

English:
theorem MeasurePreserving.integrableOn_image
  statement: [MeasurableSpace β] {e : α -> β} {ν}
  proof: ((h₁.restrict_image_emb h₂ s).integrable_comp_emb h₂).symm

中文:
定理 保测.integrableOn_image
  结论: [可测空间 β] {e : α -> β} {ν}
  证明: ((h₁.restrict_image_emb h₂ s).integrable_comp_emb h₂).symm

Depends on / 依赖: integrable_comp_emb, restrict_image_emb
-/
theorem MeasurePreserving.integrableOn_image [MeasurableSpace β] {e : α -> β} {ν}
    (h₁ : MeasurePreserving e μ ν) (h₂ : MeasurableEmbedding e) {f : β -> ε} {s : Set α} :
    IntegrableOn f (e '' s) ν ↔ IntegrableOn (f ∘ e) s μ :=
  ((h₁.restrict_image_emb h₂ s).integrable_comp_emb h₂).symm

section indicator

-- All results in this section hold for any enormed monoid.
variable {f : α -> ε'}

/--
theorem `integrable_indicator_iff` / 定理 `integrable_indicator_iff`

English:
theorem integrable_indicator_iff
  given: (hs : MeasurableSet s)
  proof: by
  simp_rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_enorm,
    enorm_indicator_eq_indicator_enorm, lintegral_indicator hs,
    aestronglyMeasurable_indicator_iff hs]

中文:
定理 integrable_indicator_iff
  条件: (hs : 可测集 s)
  证明: by
  simp_rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_enorm,
    enorm_indicator_eq_indicator_enorm, lintegral_indicator hs,
    aestronglyMeasurable_indicator_iff hs]

Depends on / 依赖: Integrable, IntegrableOn, aestronglyMeasurable_indicator_iff, enorm_indicator_eq_indicator_enorm, hasFiniteIntegral_iff_enorm, lintegral_indicator, simp_rw
-/
theorem integrable_indicator_iff (hs : MeasurableSet s) :
    Integrable (indicator s f) μ ↔ IntegrableOn f s μ := by
  simp_rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_enorm,
    enorm_indicator_eq_indicator_enorm, lintegral_indicator hs,
    aestronglyMeasurable_indicator_iff hs]

/--
theorem `IntegrableOn.integrable_indicator` / 定理 `IntegrableOn.integrable_indicator`

English:
theorem IntegrableOn.integrable_indicator
  given: (h : IntegrableOn f s μ) (hs : MeasurableSet s)
  proof: (integrable_indicator_iff hs).2 h

中文:
定理 整数egrableOn.integrable_indicator
  条件: (h : 整数egrableOn f s μ) (hs : 可测集 s)
  证明: (integrable_indicator_iff hs).2 h

Depends on / 依赖: integrable_indicator_iff
-/
theorem IntegrableOn.integrable_indicator (h : IntegrableOn f s μ) (hs : MeasurableSet s) :
    Integrable (indicator s f) μ :=
  (integrable_indicator_iff hs).2 h

/--
theorem `IntegrableOn.integrable_indicator₀` / 定理 `IntegrableOn.integrable_indicator₀`

English:
theorem IntegrableOn.integrable_indicator₀
  given: (h : IntegrableOn f s μ) (hs : NullMeasurableSet s μ)
  proof: (h.congr_set_ae hs.toMeasurable_ae_eq).integrable_indicator
.congr (measurableSet_toMeasurable μ s)
    (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)

@[fun_prop]

中文:
定理 整数egrableOn.integrable_indicator₀
  条件: (h : 整数egrableOn f s μ) (hs : NullMeasurableSet s μ)
  证明: (h.congr_set_ae hs.toMeasurable_ae_eq).integrable_indicator
.congr (measurableSet_toMeasurable μ s)
    (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)

@[fun_prop]

Depends on / 依赖: congr_set_ae, h.congr_set_ae, hs.toMeasurable_ae_eq, indicator_ae_eq_of_ae_eq_set, integrable_indicator, measurableSet_toMeasurable, toMeasurable_ae_eq
-/
theorem IntegrableOn.integrable_indicator₀ (h : IntegrableOn f s μ) (hs : NullMeasurableSet s μ) :
    Integrable (indicator s f) μ :=
  (h.congr_set_ae hs.toMeasurable_ae_eq).integrable_indicator
.congr (measurableSet_toMeasurable μ s)
    (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq)

@[fun_prop]
/--
theorem `Integrable.indicator` / 定理 `Integrable.indicator`

English:
theorem Integrable.indicator
  given: (h : Integrable f μ) (hs : MeasurableSet s)
  proof: h.integrableOn.integrable_indicator hs

@[fun_prop]

中文:
定理 可积.indicator
  条件: (h : 可积 f μ) (hs : 可测集 s)
  证明: h.integrableOn.integrable_indicator hs

@[fun_prop]

Depends on / 依赖: h.integrableOn.integrable_indicator, integrableOn, integrable_indicator
-/
theorem Integrable.indicator (h : Integrable f μ) (hs : MeasurableSet s) :
    Integrable (indicator s f) μ :=
  h.integrableOn.integrable_indicator hs

@[fun_prop]
/--
theorem `Integrable.indicator₀` / 定理 `Integrable.indicator₀`

English:
theorem Integrable.indicator₀
  given: (h : Integrable f μ) (hs : NullMeasurableSet s μ)
  proof: h.integrableOn.integrable_indicator₀ hs

中文:
定理 可积.indicator₀
  条件: (h : 可积 f μ) (hs : NullMeasurableSet s μ)
  证明: h.integrableOn.integrable_indicator₀ hs

Depends on / 依赖: h.integrableOn.integrable_indicator, integrableOn
-/
theorem Integrable.indicator₀ (h : Integrable f μ) (hs : NullMeasurableSet s μ) :
    Integrable (s.indicator f) μ :=
  h.integrableOn.integrable_indicator₀ hs

/--
theorem `IntegrableOn.indicator` / 定理 `IntegrableOn.indicator`

English:
theorem IntegrableOn.indicator
  given: (h : IntegrableOn f s μ) (ht : MeasurableSet t)
  proof: Integrable.indicator h ht

中文:
定理 整数egrableOn.indicator
  条件: (h : 整数egrableOn f s μ) (ht : 可测集 t)
  证明: Integrable.indicator h ht

Depends on / 依赖: Integrable, Integrable.indicator, indicator
-/
theorem IntegrableOn.indicator (h : IntegrableOn f s μ) (ht : MeasurableSet t) :
    IntegrableOn (indicator t f) s μ :=
  Integrable.indicator h ht

/--
theorem `integrable_indicatorConstLp` / 定理 `integrable_indicatorConstLp`

English:
theorem integrable_indicatorConstLp
  statement: {E} [NormedAddCommGroup E] {p : Real>=0∞} {s : Set α}
  proof: by
  rw [integrable_congr indicatorConstLp_coeFn]; rw [integrable_indicator_iff hs]; rw [IntegrableOn]; rw [integrable_const_iff]; rw [isFiniteMeasure_restrict]
  exact .inr hμs

中文:
定理 integrable_indicatorConstLp
  结论: {E} [赋范交换加群 E] {p : 实数>=0∞} {s : 集合 α}
  证明: by
  rw [integrable_congr indicatorConstLp_coeFn]; rw [integrable_indicator_iff hs]; rw [IntegrableOn]; rw [integrable_const_iff]; rw [isFiniteMeasure_restrict]
  exact .inr hμs

Depends on / 依赖: IntegrableOn, indicatorConstLp_coeFn, integrable_congr, integrable_const_iff, integrable_indicator_iff, isFiniteMeasure_restrict
-/
theorem integrable_indicatorConstLp {E} [NormedAddCommGroup E] {p : Real>=0∞} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E) :
    Integrable (indicatorConstLp p hs hμs c) μ := by
  rw [integrable_congr indicatorConstLp_coeFn]; rw [integrable_indicator_iff hs]; rw [IntegrableOn]; rw [integrable_const_iff]; rw [isFiniteMeasure_restrict]
  exact .inr hμs

/--
theorem `integrableOn_indicator_iff` / 定理 `integrableOn_indicator_iff`

English:
theorem integrableOn_indicator_iff
  given: (hs : MeasurableSet s)
  proof: by
  simp_rw [IntegrableOn, integrable_indicator_iff hs, IntegrableOn, Measure.restrict_restrict hs]

中文:
定理 integrableOn_indicator_iff
  条件: (hs : 可测集 s)
  证明: by
  simp_rw [IntegrableOn, integrable_indicator_iff hs, IntegrableOn, Measure.restrict_restrict hs]

Depends on / 依赖: IntegrableOn, Measure, Measure.restrict_restrict, integrable_indicator_iff, restrict_restrict, simp_rw
-/
theorem integrableOn_indicator_iff (hs : MeasurableSet s) :
    IntegrableOn (indicator s f) t μ ↔ IntegrableOn f (s inter t) μ := by
  simp_rw [IntegrableOn, integrable_indicator_iff hs, IntegrableOn, Measure.restrict_restrict hs]

end indicator

/--
theorem `IntegrableOn.restrict_toMeasurable` / 定理 `IntegrableOn.restrict_toMeasurable`

English:
theorem IntegrableOn.restrict_toMeasurable
  statement: {f : α -> ε'}
  proof: by
  rcases exists_seq_strictAnti_tendsto' ENNReal.zero_lt_top with ⟨u, _, u_pos, u_lim⟩
  let v n := toMeasurable (μ.restrict s) { x | u n <= ‖f x‖ₑ }
  have A : forall n, μ (s inter v n) != ∞ := by
    intro n
    rw [inter_comm]; rw [← Measure.restrict_apply (measurableSet_toMeasurable _ _)]; rw [measure_toMeasurable]
    exact (hf.measure_enorm_ge_lt_top (u_pos n).1 (u_pos n).2.ne).ne
  apply Measure.restrict_toMeasurable_of_cover _ A
  intro x hx
  obtain ⟨n, hn⟩ : exists n, u n < ‖f x‖ₑ :=
    ((tendsto_order.1 u_lim).2 _ (pos_of_ne_zero (h's x hx))).exists
  exact mem_iUnion.2 ⟨n, subset_toMeasurable _ _ hn.le⟩

中文:
定理 整数egrableOn.restrict_toMeasurable
  结论: {f : α -> ε'}
  证明: by
  rcases exists_seq_strictAnti_tendsto' ENNReal.zero_lt_top with ⟨u, _, u_pos, u_lim⟩
  let v n := toMeasurable (μ.restrict s) { x | u n <= ‖f x‖ₑ }
  have A : forall n, μ (s inter v n) != ∞ := by
    intro n
    rw [inter_comm]; rw [← Measure.restrict_apply (measurableSet_toMeasurable _ _)]; rw [measure_toMeasurable]
    exact (hf.measure_enorm_ge_lt_top (u_pos n).1 (u_pos n).2.ne).ne
  apply Measure.restrict_toMeasurable_of_cover _ A
  intro x hx
  obtain ⟨n, hn⟩ : exists n, u n < ‖f x‖ₑ :=
    ((tendsto_order.1 u_lim).2 _ (pos_of_ne_zero (h's x hx))).exists
  exact mem_iUnion.2 ⟨n, subset_toMeasurable _ _ hn.le⟩

Depends on / 依赖: ENNReal, ENNReal.zero_lt_top, Measure, Measure.restrict_apply, Measure.restrict_toMeasurable_of_cover, exists_seq_strictAnti_tendsto, hf.measure_enorm_ge_lt_top, inter_comm, measurableSet_toMeasurable, measure_enorm_ge_lt_top, measure_toMeasurable, restrict, restrict_apply, restrict_toMeasurable_of_cover, tendsto_order, toMeasurable, u_lim, u_pos, zero_lt_top
-/
theorem IntegrableOn.restrict_toMeasurable {f : α -> ε'}
    (hf : IntegrableOn f s μ) (h's : forall x in s, ‖f x‖ₑ != 0) :
    μ.restrict (toMeasurable μ s) = μ.restrict s := by
  rcases exists_seq_strictAnti_tendsto' ENNReal.zero_lt_top with ⟨u, _, u_pos, u_lim⟩
  let v n := toMeasurable (μ.restrict s) { x | u n <= ‖f x‖ₑ }
  have A : forall n, μ (s inter v n) != ∞ := by
    intro n
    rw [inter_comm]; rw [← Measure.restrict_apply (measurableSet_toMeasurable _ _)]; rw [measure_toMeasurable]
    exact (hf.measure_enorm_ge_lt_top (u_pos n).1 (u_pos n).2.ne).ne
  apply Measure.restrict_toMeasurable_of_cover _ A
  intro x hx
  obtain ⟨n, hn⟩ : exists n, u n < ‖f x‖ₑ :=
    ((tendsto_order.1 u_lim).2 _ (pos_of_ne_zero (h's x hx))).exists
  exact mem_iUnion.2 ⟨n, subset_toMeasurable _ _ hn.le⟩

-- TODO: investigate generalising this section to e-seminormed monoids
section ENormedAddMonoid

variable {ε' : Type*} [TopologicalSpace ε'] [ENormedAddMonoid ε'] [PseudoMetrizableSpace ε']

-- TODO: generalise this to e-seminormed commutative monoids,
-- by merely assuming ‖f x‖ₑ vanishes on t \ s
/--
theorem `IntegrableOn.of_ae_sdiff_eq_zero` / 定理 `IntegrableOn.of_ae_sdiff_eq_zero`

English:
theorem IntegrableOn.of_ae_sdiff_eq_zero
  statement: {f : α -> ε'}
  proof: by
  let u := { x in s | f x != 0 }
  have hu : IntegrableOn f u μ := hf.mono_set fun x hx => hx.1
  let v := toMeasurable μ u
  have A : IntegrableOn f v μ := by
    rw [IntegrableOn]; rw [hu.restrict_toMeasurable]
    · exact hu
    · intro x hx; simpa using hx.2
  have B : IntegrableOn f (t \ v) μ := by
    apply integrableOn_zero.congr
    filter_upwards [ae_restrict_of_ae h't,
      ae_restrict_mem₀ (ht.diff (measurableSet_toMeasurable μ u).nullMeasurableSet)] with x hxt hx
    by_cases h'x : x in s
    · by_contra H
      exact hx.2 (subset_toMeasurable μ u ⟨h'x, Ne.symm H⟩)
    · exact (hxt ⟨hx.1, h'x⟩).symm
  apply (A.union B).mono_set _
  rw [union_sdiff_self]
  exact subset_union_right

@[deprecated (since := "2026-06-03")]
alias IntegrableOn.of_ae_diff_eq_zero := IntegrableOn.of_ae_sdiff_eq_zero

中文:
定理 整数egrableOn.of_ae_sdiff_eq_zero
  结论: {f : α -> ε'}
  证明: by
  let u := { x in s | f x != 0 }
  have hu : IntegrableOn f u μ := hf.mono_set fun x hx => hx.1
  let v := toMeasurable μ u
  have A : IntegrableOn f v μ := by
    rw [IntegrableOn]; rw [hu.restrict_toMeasurable]
    · exact hu
    · intro x hx; simpa using hx.2
  have B : IntegrableOn f (t \ v) μ := by
    apply integrableOn_zero.congr
    filter_upwards [ae_restrict_of_ae h't,
      ae_restrict_mem₀ (ht.diff (measurableSet_toMeasurable μ u).nullMeasurableSet)] with x hxt hx
    by_cases h'x : x in s
    · by_contra H
      exact hx.2 (subset_toMeasurable μ u ⟨h'x, Ne.symm H⟩)
    · exact (hxt ⟨hx.1, h'x⟩).symm
  apply (A.union B).mono_set _
  rw [union_sdiff_self]
  exact subset_union_right

@[deprecated (since := "2026-06-03")]
alias IntegrableOn.of_ae_diff_eq_zero := IntegrableOn.of_ae_sdiff_eq_zero

Depends on / 依赖: IntegrableOn, ae_restrict_of_ae, filter_upwards, hf.mono_set, ht.diff, hu.restrict_toMeasurable, integrableOn_zero, integrableOn_zero.congr, measurableSet_toMeasurable, mono_set, nullMeasurableSet, restrict_toMeasurable, toMeasurable
-/
theorem IntegrableOn.of_ae_sdiff_eq_zero {f : α -> ε'}
    (hf : IntegrableOn f s μ) (ht : NullMeasurableSet t μ)
    (h't : forallᵐ x ∂μ, x in t \ s -> f x = 0) : IntegrableOn f t μ := by
  let u := { x in s | f x != 0 }
  have hu : IntegrableOn f u μ := hf.mono_set fun x hx => hx.1
  let v := toMeasurable μ u
  have A : IntegrableOn f v μ := by
    rw [IntegrableOn]; rw [hu.restrict_toMeasurable]
    · exact hu
    · intro x hx; simpa using hx.2
  have B : IntegrableOn f (t \ v) μ := by
    apply integrableOn_zero.congr
    filter_upwards [ae_restrict_of_ae h't,
      ae_restrict_mem₀ (ht.diff (measurableSet_toMeasurable μ u).nullMeasurableSet)] with x hxt hx
    by_cases h'x : x in s
    · by_contra H
      exact hx.2 (subset_toMeasurable μ u ⟨h'x, Ne.symm H⟩)
    · exact (hxt ⟨hx.1, h'x⟩).symm
  apply (A.union B).mono_set _
  rw [union_sdiff_self]
  exact subset_union_right

@[deprecated (since := "2026-06-03")]
alias IntegrableOn.of_ae_diff_eq_zero := IntegrableOn.of_ae_sdiff_eq_zero

/--
theorem `IntegrableOn.of_forall_sdiff_eq_zero` / 定理 `IntegrableOn.of_forall_sdiff_eq_zero`

English:
theorem IntegrableOn.of_forall_sdiff_eq_zero
  statement: {f : α -> ε'}
  proof: hf.of_ae_sdiff_eq_zero ht.nullMeasurableSet (Eventually.of_forall h't)

@[deprecated (since := "2026-06-03")]
alias IntegrableOn.of_forall_diff_eq_zero := IntegrableOn.of_forall_sdiff_eq_zero

中文:
定理 整数egrableOn.of_对任意_sdiff_eq_zero
  结论: {f : α -> ε'}
  证明: hf.of_ae_sdiff_eq_zero ht.nullMeasurableSet (Eventually.of_forall h't)

@[deprecated (since := "2026-06-03")]
alias IntegrableOn.of_forall_diff_eq_zero := IntegrableOn.of_forall_sdiff_eq_zero

Depends on / 依赖: Eventually, Eventually.of_forall, hf.of_ae_sdiff_eq_zero, ht.nullMeasurableSet, nullMeasurableSet, of_ae_sdiff_eq_zero, of_forall
-/
theorem IntegrableOn.of_forall_sdiff_eq_zero {f : α -> ε'}
    (hf : IntegrableOn f s μ) (ht : MeasurableSet t)
    (h't : forall x in t \ s, f x = 0) : IntegrableOn f t μ :=
  hf.of_ae_sdiff_eq_zero ht.nullMeasurableSet (Eventually.of_forall h't)

@[deprecated (since := "2026-06-03")]
alias IntegrableOn.of_forall_diff_eq_zero := IntegrableOn.of_forall_sdiff_eq_zero

/--
theorem `IntegrableOn.integrable_of_ae_notMem_eq_zero` / 定理 `IntegrableOn.integrable_of_ae_notMem_eq_zero`

English:
theorem IntegrableOn.integrable_of_ae_notMem_eq_zero
  proof: by
  rw [← integrableOn_univ]
  apply hf.of_ae_sdiff_eq_zero nullMeasurableSet_univ
  filter_upwards [h't] with x hx h'x using hx h'x.2

中文:
定理 整数egrableOn.integrable_of_ae_notMem_eq_zero
  证明: by
  rw [← integrableOn_univ]
  apply hf.of_ae_sdiff_eq_zero nullMeasurableSet_univ
  filter_upwards [h't] with x hx h'x using hx h'x.2

Depends on / 依赖: filter_upwards, hf.of_ae_sdiff_eq_zero, integrableOn_univ, nullMeasurableSet_univ, of_ae_sdiff_eq_zero
-/
theorem IntegrableOn.integrable_of_ae_notMem_eq_zero
    {f : α -> ε'} (hf : IntegrableOn f s μ) (h't : forallᵐ x ∂μ, x ∉ s -> f x = 0) : Integrable f μ := by
  rw [← integrableOn_univ]
  apply hf.of_ae_sdiff_eq_zero nullMeasurableSet_univ
  filter_upwards [h't] with x hx h'x using hx h'x.2

/--
theorem `IntegrableOn.integrable_of_forall_notMem_eq_zero` / 定理 `IntegrableOn.integrable_of_forall_notMem_eq_zero`

English:
theorem IntegrableOn.integrable_of_forall_notMem_eq_zero
  proof: hf.integrable_of_ae_notMem_eq_zero (Eventually.of_forall fun x hx => h't x hx)

中文:
定理 整数egrableOn.integrable_of_对任意_notMem_eq_zero
  证明: hf.integrable_of_ae_notMem_eq_zero (Eventually.of_forall fun x hx => h't x hx)

Depends on / 依赖: Eventually, Eventually.of_forall, hf.integrable_of_ae_notMem_eq_zero, integrable_of_ae_notMem_eq_zero, of_forall
-/
theorem IntegrableOn.integrable_of_forall_notMem_eq_zero
    {f : α -> ε'} (hf : IntegrableOn f s μ) (h't : forall x, x ∉ s -> f x = 0) : Integrable f μ :=
  hf.integrable_of_ae_notMem_eq_zero (Eventually.of_forall fun x hx => h't x hx)

/--
theorem `IntegrableOn.of_inter_support` / 定理 `IntegrableOn.of_inter_support`

English:
theorem IntegrableOn.of_inter_support
  statement: {f : α -> ε'}
  proof: by
  simpa using hf.of_forall_sdiff_eq_zero hs

中文:
定理 整数egrableOn.of_inter_support
  结论: {f : α -> ε'}
  证明: by
  simpa using hf.of_forall_sdiff_eq_zero hs

Depends on / 依赖: hf.of_forall_sdiff_eq_zero, of_forall_sdiff_eq_zero
-/
theorem IntegrableOn.of_inter_support {f : α -> ε'}
    (hs : MeasurableSet s) (hf : IntegrableOn f (s inter support f) μ) :
    IntegrableOn f s μ := by
  simpa using hf.of_forall_sdiff_eq_zero hs

/--
theorem `integrableOn_iff_integrable_of_support_subset` / 定理 `integrableOn_iff_integrable_of_support_subset`

English:
theorem integrableOn_iff_integrable_of_support_subset
  proof: by
  refine ⟨fun h => ?_, fun h => h.integrableOn⟩
  refine h.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  contrapose! hx
  exact h1s (mem_support.2 hx)

中文:
定理 integrableOn_iff_integrable_of_support_subset
  证明: by
  refine ⟨fun h => ?_, fun h => h.integrableOn⟩
  refine h.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  contrapose! hx
  exact h1s (mem_support.2 hx)

Depends on / 依赖: contrapose, h.integrableOn, h.integrable_of_forall_notMem_eq_zero, integrableOn, integrable_of_forall_notMem_eq_zero, mem_support
-/
theorem integrableOn_iff_integrable_of_support_subset
    {f : α -> ε'} (h1s : support f subseteq s) : IntegrableOn f s μ ↔ Integrable f μ := by
  refine ⟨fun h => ?_, fun h => h.integrableOn⟩
  refine h.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  contrapose! hx
  exact h1s (mem_support.2 hx)

end ENormedAddMonoid

/--
theorem `integrableOn_Lp_of_measure_ne_top` / 定理 `integrableOn_Lp_of_measure_ne_top`

English:
theorem integrableOn_Lp_of_measure_ne_top
  statement: {E} [NormedAddCommGroup E] {p : Real>=0∞} {s : Set α}
  proof: by
  refine memLp_one_iff_integrable.mp ?_
  have hμ_restrict_univ : (μ.restrict s) Set.univ < ∞ := by
    simpa only [Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply, lt_top_iff_ne_top]
  have hμ_finite : IsFiniteMeasure (μ.restrict s) := ⟨hμ_restrict_univ⟩
  exact ((Lp.memLp _).restrict s).mono_exponent hp

中文:
定理 integrableOn_Lp_of_measure_ne_top
  结论: {E} [赋范交换加群 E] {p : 实数>=0∞} {s : 集合 α}
  证明: by
  refine memLp_one_iff_integrable.mp ?_
  have hμ_restrict_univ : (μ.restrict s) Set.univ < ∞ := by
    simpa only [Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply, lt_top_iff_ne_top]
  have hμ_finite : IsFiniteMeasure (μ.restrict s) := ⟨hμ_restrict_univ⟩
  exact ((Lp.memLp _).restrict s).mono_exponent hp

Depends on / 依赖: IsFiniteMeasure, Lp.memLp, MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_apply, Set.univ, Set.univ_inter, lt_top_iff_ne_top, memLp_one_iff_integrable, memLp_one_iff_integrable.mp, mono_exponent, restrict, restrict_apply, univ_inter
-/
theorem integrableOn_Lp_of_measure_ne_top {E} [NormedAddCommGroup E] {p : Real>=0∞} {s : Set α}
    (f : Lp E p μ) (hp : 1 <= p) (hμs : μ s != ∞) : IntegrableOn f s μ := by
  refine memLp_one_iff_integrable.mp ?_
  have hμ_restrict_univ : (μ.restrict s) Set.univ < ∞ := by
    simpa only [Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply, lt_top_iff_ne_top]
  have hμ_finite : IsFiniteMeasure (μ.restrict s) := ⟨hμ_restrict_univ⟩
  exact ((Lp.memLp _).restrict s).mono_exponent hp

/--
theorem `Integrable.lintegral_lt_top` / 定理 `Integrable.lintegral_lt_top`

English:
theorem Integrable.lintegral_lt_top
  given: {f : α -> Real} (hf : Integrable f μ)
  proof: calc
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) <= ∫⁻ x, ↑‖f x‖₊ ∂μ := lintegral_ofReal_le_lintegral_enorm f
    _ < ∞ := hf.2

中文:
定理 可积.lintegral_lt_top
  条件: {f : α -> 实数} (hf : 可积 f μ)
  证明: calc
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) <= ∫⁻ x, ↑‖f x‖₊ ∂μ := lintegral_ofReal_le_lintegral_enorm f
    _ < ∞ := hf.2

Depends on / 依赖: ENNReal, ENNReal.ofReal, lintegral_ofReal_le_lintegral_enorm, ofReal
-/
theorem Integrable.lintegral_lt_top {f : α -> Real} (hf : Integrable f μ) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) < ∞ :=
  calc
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) <= ∫⁻ x, ↑‖f x‖₊ ∂μ := lintegral_ofReal_le_lintegral_enorm f
    _ < ∞ := hf.2

/--
theorem `IntegrableOn.setLIntegral_lt_top` / 定理 `IntegrableOn.setLIntegral_lt_top`

English:
theorem IntegrableOn.setLIntegral_lt_top
  given: {f : α -> Real} {s : Set α} (hf : IntegrableOn f s μ)
  proof: Integrable.lintegral_lt_top hf

中文:
定理 整数egrableOn.setL整数egral_lt_top
  条件: {f : α -> 实数} {s : 集合 α} (hf : 整数egrableOn f s μ)
  证明: Integrable.lintegral_lt_top hf

Depends on / 依赖: Integrable, Integrable.lintegral_lt_top, lintegral_lt_top
-/
theorem IntegrableOn.setLIntegral_lt_top {f : α -> Real} {s : Set α} (hf : IntegrableOn f s μ) :
    (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) < ∞ :=
  Integrable.lintegral_lt_top hf

/--
theorem `_root_.ContinuousLinearMap.integrableOn_comp` / 定理 `_root_.ContinuousLinearMap.integrableOn_comp`

English:
theorem _root_.ContinuousLinearMap.integrableOn_comp
  statement: {E H 𝕜 𝕜' : Type*}
  proof: L.integrable_comp hf

中文:
定理 _root_.连续线性映射.integrableOn_comp
  结论: {E H 𝕜 𝕜' : 类型}
  证明: L.integrable_comp hf

Depends on / 依赖: L.integrable_comp, integrable_comp
-/
theorem _root_.ContinuousLinearMap.integrableOn_comp {E H 𝕜 𝕜' : Type*}
    [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
    [NormedAddCommGroup E] [NormedSpace 𝕜' E] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {σ : 𝕜 ->+* 𝕜'} [RingHomIsometric σ] {f : α -> H} (L : H ->SL[σ] E) (hf : IntegrableOn f s μ) :
    IntegrableOn (L ∘ f) s μ :=
  L.integrable_comp hf

/--
Definition of `IntegrableAtFilter` / `IntegrableAtFilter` 的定义

English:
definition IntegrableAtFilter
  signature: (f : α -> ε) (l : Filter α) (μ : Measure α := by volume_tac)
  body: exists s in l, IntegrableOn f s μ

中文:
定义 整数egrableAtFilter
  签名: (f : α -> ε) (l : 滤子 α) (μ : 测度 α := by volume_tac)
  定义体: exists s in l, IntegrableOn f s μ

Depends on / 依赖: IntegrableOn, volume_tac
-/
def IntegrableAtFilter (f : α -> ε) (l : Filter α) (μ : Measure α := by volume_tac) :=
  exists s in l, IntegrableOn f s μ

variable {l l' : Filter α}

/--
theorem `_root_.MeasurableEmbedding.integrableAtFilter_map_iff` / 定理 `_root_.MeasurableEmbedding.integrableAtFilter_map_iff`

English:
theorem _root_.MeasurableEmbedding.integrableAtFilter_map_iff
  statement: [MeasurableSpace β] {e : α -> β}
  proof: by
  simp_rw [IntegrableAtFilter, he.integrableOn_map_iff]
  constructor <;> rintro ⟨s, hs⟩
  · exact ⟨_, hs⟩
  · exact ⟨e '' s, by rwa [mem_map, he.injective.preimage_image]⟩

中文:
定理 _root_.可测嵌入.integrableAtFilter_map_iff
  结论: [可测空间 β] {e : α -> β}
  证明: by
  simp_rw [IntegrableAtFilter, he.integrableOn_map_iff]
  constructor <;> rintro ⟨s, hs⟩
  · exact ⟨_, hs⟩
  · exact ⟨e '' s, by rwa [mem_map, he.injective.preimage_image]⟩

Depends on / 依赖: IntegrableAtFilter, he.injective.preimage_image, he.integrableOn_map_iff, injective, integrableOn_map_iff, mem_map, preimage_image, simp_rw
-/
theorem _root_.MeasurableEmbedding.integrableAtFilter_map_iff [MeasurableSpace β] {e : α -> β}
    (he : MeasurableEmbedding e) {f : β -> ε} :
    IntegrableAtFilter f (l.map e) (μ.map e) ↔ IntegrableAtFilter (f ∘ e) l μ := by
  simp_rw [IntegrableAtFilter, he.integrableOn_map_iff]
  constructor <;> rintro ⟨s, hs⟩
  · exact ⟨_, hs⟩
  · exact ⟨e '' s, by rwa [mem_map, he.injective.preimage_image]⟩

/--
theorem `_root_.MeasurableEmbedding.integrableAtFilter_iff_comap` / 定理 `_root_.MeasurableEmbedding.integrableAtFilter_iff_comap`

English:
theorem _root_.MeasurableEmbedding.integrableAtFilter_iff_comap
  statement: [MeasurableSpace β] {e : α -> β}
  proof: by
  simp_rw [← he.integrableAtFilter_map_iff, IntegrableAtFilter, he.map_comap]
  constructor <;> rintro ⟨s, hs, int⟩
· exact ⟨s, hs, int.mono_measure μ.restrict_le_self⟩
  · exact ⟨_, inter_mem hs range_mem_map, int.inter_of_restrict⟩

中文:
定理 _root_.可测嵌入.integrableAtFilter_iff_comap
  结论: [可测空间 β] {e : α -> β}
  证明: by
  simp_rw [← he.integrableAtFilter_map_iff, IntegrableAtFilter, he.map_comap]
  constructor <;> rintro ⟨s, hs, int⟩
· exact ⟨s, hs, int.mono_measure μ.restrict_le_self⟩
  · exact ⟨_, inter_mem hs range_mem_map, int.inter_of_restrict⟩

Depends on / 依赖: IntegrableAtFilter, he.integrableAtFilter_map_iff, he.map_comap, int.inter_of_restrict, int.mono_measure, integrableAtFilter_map_iff, inter_mem, inter_of_restrict, map_comap, mono_measure, range_mem_map, restrict_le_self, simp_rw
-/
theorem _root_.MeasurableEmbedding.integrableAtFilter_iff_comap [MeasurableSpace β] {e : α -> β}
    (he : MeasurableEmbedding e) {f : β -> ε} {μ : Measure β} :
    IntegrableAtFilter f (l.map e) μ ↔ IntegrableAtFilter (f ∘ e) l (μ.comap e) := by
  simp_rw [← he.integrableAtFilter_map_iff, IntegrableAtFilter, he.map_comap]
  constructor <;> rintro ⟨s, hs, int⟩
· exact ⟨s, hs, int.mono_measure μ.restrict_le_self⟩
  · exact ⟨_, inter_mem hs range_mem_map, int.inter_of_restrict⟩

/--
theorem `Integrable.integrableAtFilter` / 定理 `Integrable.integrableAtFilter`

English:
theorem Integrable.integrableAtFilter
  given: (h : Integrable f μ) (l : Filter α)
  proof: ⟨univ, Filter.univ_mem, integrableOn_univ.2 h⟩

中文:
定理 可积.integrableAtFilter
  条件: (h : 可积 f μ) (l : 滤子 α)
  证明: ⟨univ, Filter.univ_mem, integrableOn_univ.2 h⟩

Depends on / 依赖: Filter, Filter.univ_mem, integrableOn_univ, univ_mem
-/
theorem Integrable.integrableAtFilter (h : Integrable f μ) (l : Filter α) :
    IntegrableAtFilter f l μ :=
  ⟨univ, Filter.univ_mem, integrableOn_univ.2 h⟩

/--
theorem `IntegrableAtFilter.eventually` / 定理 `IntegrableAtFilter.eventually`

English:
theorem IntegrableAtFilter.eventually
  given: (h : IntegrableAtFilter f l μ)
  proof: Iff.mpr (eventually_smallSets' fun _s _t hst ht => ht.mono_set hst) h

中文:
定理 整数egrableAtFilter.eventually
  条件: (h : 整数egrableAtFilter f l μ)
  证明: Iff.mpr (eventually_smallSets' fun _s _t hst ht => ht.mono_set hst) h
-/
protected theorem IntegrableAtFilter.eventually (h : IntegrableAtFilter f l μ) :
    forallᶠ s in l.smallSets, IntegrableOn f s μ :=
  Iff.mpr (eventually_smallSets' fun _s _t hst ht => ht.mono_set hst) h

/--
theorem `integrableAtFilter_atBot_iff` / 定理 `integrableAtFilter_atBot_iff`

English:
theorem integrableAtFilter_atBot_iff
  given: [Preorder α] [IsCodirectedOrder α] [Nonempty α]
  proof: by
  refine ⟨fun ⟨s, hs, hi⟩ => ?_, fun ⟨a, ha⟩ => ⟨Iic a, Iic_mem_atBot a, ha⟩⟩
  obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs
  exact ⟨t, hi.mono_set fun _ hx => ht _ hx⟩

中文:
定理 integrableAtFilter_atBot_iff
  条件: [预序 α] [IsCodirectedOrder α] [非空 α]
  证明: by
  refine ⟨fun ⟨s, hs, hi⟩ => ?_, fun ⟨a, ha⟩ => ⟨Iic a, Iic_mem_atBot a, ha⟩⟩
  obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs
  exact ⟨t, hi.mono_set fun _ hx => ht _ hx⟩

Depends on / 依赖: Iic_mem_atBot, hi.mono_set, mem_atBot_sets, mem_atBot_sets.mp, mono_set
-/
theorem integrableAtFilter_atBot_iff [Preorder α] [IsCodirectedOrder α] [Nonempty α] :
    IntegrableAtFilter f atBot μ ↔ exists a, IntegrableOn f (Iic a) μ := by
  refine ⟨fun ⟨s, hs, hi⟩ => ?_, fun ⟨a, ha⟩ => ⟨Iic a, Iic_mem_atBot a, ha⟩⟩
  obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs
  exact ⟨t, hi.mono_set fun _ hx => ht _ hx⟩

/--
theorem `integrableAtFilter_atTop_iff` / 定理 `integrableAtFilter_atTop_iff`

English:
theorem integrableAtFilter_atTop_iff
  given: [Preorder α] [IsDirectedOrder α] [Nonempty α]
  proof: integrableAtFilter_atBot_iff (α := αᵒᵈ)

@[gcongr]

中文:
定理 integrableAtFilter_atTop_iff
  条件: [预序 α] [IsDirectedOrder α] [非空 α]
  证明: integrableAtFilter_atBot_iff (α := αᵒᵈ)

@[gcongr]

Depends on / 依赖: integrableAtFilter_atBot_iff
-/
theorem integrableAtFilter_atTop_iff [Preorder α] [IsDirectedOrder α] [Nonempty α] :
    IntegrableAtFilter f atTop μ ↔ exists a, IntegrableOn f (Ici a) μ :=
  integrableAtFilter_atBot_iff (α := αᵒᵈ)

@[gcongr]
/--
lemma `IntegrableAtFilter.mono_measure` / 引理 `IntegrableAtFilter.mono_measure`

English:
lemma IntegrableAtFilter.mono_measure
  given: (hf : IntegrableAtFilter f l μ) (h : ν <= μ)
  proof: let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.mono_measure h⟩

@[gcongr]

中文:
引理 整数egrableAtFilter.mono_measure
  条件: (hf : 整数egrableAtFilter f l μ) (h : ν <= μ)
  证明: let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.mono_measure h⟩

@[gcongr]

Depends on / 依赖: hf.mono_measure, mono_measure
-/
lemma IntegrableAtFilter.mono_measure (hf : IntegrableAtFilter f l μ) (h : ν <= μ) :
    IntegrableAtFilter f l ν :=
  let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.mono_measure h⟩

@[gcongr]
/--
lemma `IntegrableAtFilter.congr` / 引理 `IntegrableAtFilter.congr`

English:
lemma IntegrableAtFilter.congr
  given: (hf : IntegrableAtFilter f l μ) (h : f =ᵐ[μ] g)
  proof: let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.congr h.restrict⟩

中文:
引理 整数egrableAtFilter.congr
  条件: (hf : 整数egrableAtFilter f l μ) (h : f =ᵐ[μ] g)
  证明: let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.congr h.restrict⟩

Depends on / 依赖: h.restrict, hf.congr, restrict
-/
lemma IntegrableAtFilter.congr (hf : IntegrableAtFilter f l μ) (h : f =ᵐ[μ] g) :
    IntegrableAtFilter g l μ :=
  let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.congr h.restrict⟩

/--
lemma `integrableAtFilter_congr` / 引理 `integrableAtFilter_congr`

English:
lemma integrableAtFilter_congr
  given: (h : f =ᵐ[μ] g)
  proof: ⟨(·.congr h), (·.congr h.symm)⟩

中文:
引理 integrableAtFilter_congr
  条件: (h : f =ᵐ[μ] g)
  证明: ⟨(·.congr h), (·.congr h.symm)⟩

Depends on / 依赖: h.symm
-/
lemma integrableAtFilter_congr (h : f =ᵐ[μ] g) :
    IntegrableAtFilter f l μ ↔ IntegrableAtFilter g l μ :=
  ⟨(·.congr h), (·.congr h.symm)⟩

/--
lemma `IntegrableAtFilter.congr'_enorm` / 引理 `IntegrableAtFilter.congr'_enorm`

English:
lemma IntegrableAtFilter.congr'_enorm
  statement: {ε'' : Type*} [TopologicalSpace ε''] [ContinuousENorm ε'']
  proof: let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.congr'_enorm hg.restrict (ae_restrict_le h)⟩

@[simp]

中文:
引理 整数egrableAtFilter.congr'_enorm
  结论: {ε'' : 类型} [拓扑空间 ε''] [余ntinuousE范数 ε'']
  证明: let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.congr'_enorm hg.restrict (ae_restrict_le h)⟩

@[simp]

Depends on / 依赖: _enorm, ae_restrict_le, hf.congr, hg.restrict, restrict
-/
lemma IntegrableAtFilter.congr'_enorm {ε'' : Type*} [TopologicalSpace ε''] [ContinuousENorm ε'']
    {g : α -> ε''} (hf : IntegrableAtFilter f l μ) (hg : AEStronglyMeasurable g μ)
    (h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    IntegrableAtFilter g l μ :=
  let ⟨s, hs, hf⟩ := hf; ⟨s, hs, hf.congr'_enorm hg.restrict (ae_restrict_le h)⟩

@[simp]
/--
lemma `integrableAtFilter_zero` / 引理 `integrableAtFilter_zero`

English:
lemma integrableAtFilter_zero
  statement: IntegrableAtFilter (0 : α -> E) l μ
  proof: ⟨univ, by simp, integrableOn_univ.mpr (integrable_zero ..)⟩

中文:
引理 integrableAtFilter_zero
  结论: 整数egrableAtFilter (0 : α -> E) l μ
  证明: ⟨univ, by simp, integrableOn_univ.mpr (integrable_zero ..)⟩

Depends on / 依赖: integrableOn_univ, integrableOn_univ.mpr, integrable_zero
-/
lemma integrableAtFilter_zero : IntegrableAtFilter (0 : α -> E) l μ :=
  ⟨univ, by simp, integrableOn_univ.mpr (integrable_zero ..)⟩

/--
theorem `IntegrableAtFilter.add` / 定理 `IntegrableAtFilter.add`

English:
theorem IntegrableAtFilter.add
  statement: [ContinuousAdd ε'] {f g : α -> ε'}
  proof: by
  rcases hf with ⟨s, sl, hs⟩
  rcases hg with ⟨t, tl, ht⟩
  refine ⟨s inter t, inter_mem sl tl, ?_⟩
  exact (hs.mono_set inter_subset_left).add (ht.mono_set inter_subset_right)

中文:
定理 整数egrableAtFilter.add
  结论: [连续加法 ε'] {f g : α -> ε'}
  证明: by
  rcases hf with ⟨s, sl, hs⟩
  rcases hg with ⟨t, tl, ht⟩
  refine ⟨s inter t, inter_mem sl tl, ?_⟩
  exact (hs.mono_set inter_subset_left).add (ht.mono_set inter_subset_right)
-/
protected theorem IntegrableAtFilter.add [ContinuousAdd ε'] {f g : α -> ε'}
    (hf : IntegrableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter (f + g) l μ := by
  rcases hf with ⟨s, sl, hs⟩
  rcases hg with ⟨t, tl, ht⟩
  refine ⟨s inter t, inter_mem sl tl, ?_⟩
  exact (hs.mono_set inter_subset_left).add (ht.mono_set inter_subset_right)

/--
theorem `IntegrableAtFilter.neg` / 定理 `IntegrableAtFilter.neg`

English:
theorem IntegrableAtFilter.neg
  given: {f : α -> E} (hf : IntegrableAtFilter f l μ)
  proof: by
  rcases hf with ⟨s, sl, hs⟩
  exact ⟨s, sl, hs.neg⟩

@[simp]

中文:
定理 整数egrableAtFilter.neg
  条件: {f : α -> E} (hf : 整数egrableAtFilter f l μ)
  证明: by
  rcases hf with ⟨s, sl, hs⟩
  exact ⟨s, sl, hs.neg⟩

@[simp]
-/
protected theorem IntegrableAtFilter.neg {f : α -> E} (hf : IntegrableAtFilter f l μ) :
    IntegrableAtFilter (-f) l μ := by
  rcases hf with ⟨s, sl, hs⟩
  exact ⟨s, sl, hs.neg⟩

@[simp]
/--
theorem `integrableAtFilter_neg_iff` / 定理 `integrableAtFilter_neg_iff`

English:
theorem integrableAtFilter_neg_iff
  given: {f : α -> E}
  proof: by
  refine ⟨fun h => ?_, fun h => h.neg⟩
  convert! h.neg; simp

中文:
定理 integrableAtFilter_neg_iff
  条件: {f : α -> E}
  证明: by
  refine ⟨fun h => ?_, fun h => h.neg⟩
  convert! h.neg; simp
-/
protected theorem integrableAtFilter_neg_iff {f : α -> E} :
    IntegrableAtFilter (-f) l μ ↔ IntegrableAtFilter f l μ := by
  refine ⟨fun h => ?_, fun h => h.neg⟩
  convert! h.neg; simp

/--
theorem `IntegrableAtFilter.sub` / 定理 `IntegrableAtFilter.sub`

English:
theorem IntegrableAtFilter.sub
  statement: {f g : α -> E}
  proof: by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

中文:
定理 整数egrableAtFilter.sub
  结论: {f g : α -> E}
  证明: by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg
-/
protected theorem IntegrableAtFilter.sub {f g : α -> E}
    (hf : IntegrableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter (f - g) l μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/--
theorem `IntegrableAtFilter.smul` / 定理 `IntegrableAtFilter.smul`

English:
theorem IntegrableAtFilter.smul
  statement: {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
  proof: by
  rcases hf with ⟨s, sl, hs⟩
  exact ⟨s, sl, hs.smul c⟩

中文:
定理 整数egrableAtFilter.smul
  结论: {𝕜 : 类型} [赋范交换加群 𝕜] [SMulZero类 𝕜 E]
  证明: by
  rcases hf with ⟨s, sl, hs⟩
  exact ⟨s, sl, hs.smul c⟩
-/
protected theorem IntegrableAtFilter.smul {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
    [IsBoundedSMul 𝕜 E] {f : α -> E} (hf : IntegrableAtFilter f l μ) (c : 𝕜) :
    IntegrableAtFilter (c • f) l μ := by
  rcases hf with ⟨s, sl, hs⟩
  exact ⟨s, sl, hs.smul c⟩

-- See `integrableAtFilter_smul_iff` below for the fully general version.
/--
theorem `integrableAtFilter_smul_iff'` / 定理 `integrableAtFilter_smul_iff'`

English:
theorem integrableAtFilter_smul_iff'
  statement: {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
  proof: by
  refine ⟨fun hf => ?_, fun h => h.smul c⟩
  convert! hf.smul c⁻¹
  simp [← smul_assoc, inv_mul_cancel₀ hc]

中文:
定理 integrableAtFilter_smul_iff'
  结论: {𝕜 : 类型} [赋范域 𝕜] [赋范空间 𝕜 E]
  证明: by
  refine ⟨fun hf => ?_, fun h => h.smul c⟩
  convert! hf.smul c⁻¹
  simp [← smul_assoc, inv_mul_cancel₀ hc]
-/
private theorem integrableAtFilter_smul_iff' {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : α -> E} {c : 𝕜} (hc : c != 0) :
    IntegrableAtFilter (c • f) l μ ↔ IntegrableAtFilter f l μ := by
  refine ⟨fun hf => ?_, fun h => h.smul c⟩
  convert! hf.smul c⁻¹
  simp [← smul_assoc, inv_mul_cancel₀ hc]

/--
theorem `integrableAtFilter_smul_iff` / 定理 `integrableAtFilter_smul_iff`

English:
theorem integrableAtFilter_smul_iff
  statement: {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
  proof: by
  by_cases hc : c = 0
  · simp [hc]
  · simpa [hc] using MeasureTheory.integrableAtFilter_smul_iff' hc

中文:
定理 integrableAtFilter_smul_iff
  结论: {𝕜 : 类型} [赋范域 𝕜] [赋范空间 𝕜 E]
  证明: by
  by_cases hc : c = 0
  · simp [hc]
  · simpa [hc] using MeasureTheory.integrableAtFilter_smul_iff' hc

Depends on / 依赖: MeasureTheory, MeasureTheory.integrableAtFilter_smul_iff, integrableAtFilter_smul_iff
-/
theorem integrableAtFilter_smul_iff {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : α -> E} (c : 𝕜) :
    IntegrableAtFilter (c • f) l μ ↔ c = 0 ∨ IntegrableAtFilter f l μ := by
  by_cases hc : c = 0
  · simp [hc]
  · simpa [hc] using MeasureTheory.integrableAtFilter_smul_iff' hc

/--
theorem `IntegrableAtFilter.enorm` / 定理 `IntegrableAtFilter.enorm`

English:
theorem IntegrableAtFilter.enorm
  given: (hf : IntegrableAtFilter f l μ)
  proof: Exists.casesOn hf fun s hs => ⟨s, hs.1, hs.2.enorm⟩

中文:
定理 整数egrableAtFilter.enorm
  条件: (hf : 整数egrableAtFilter f l μ)
  证明: Exists.casesOn hf fun s hs => ⟨s, hs.1, hs.2.enorm⟩
-/
protected theorem IntegrableAtFilter.enorm (hf : IntegrableAtFilter f l μ) :
    IntegrableAtFilter (fun x => ‖f x‖ₑ) l μ :=
  Exists.casesOn hf fun s hs => ⟨s, hs.1, hs.2.enorm⟩

/--
theorem `IntegrableAtFilter.norm` / 定理 `IntegrableAtFilter.norm`

English:
theorem IntegrableAtFilter.norm
  given: {f : α -> E} (hf : IntegrableAtFilter f l μ)
  proof: Exists.casesOn hf fun s hs => ⟨s, hs.1, hs.2.norm⟩

中文:
定理 整数egrableAtFilter.norm
  条件: {f : α -> E} (hf : 整数egrableAtFilter f l μ)
  证明: Exists.casesOn hf fun s hs => ⟨s, hs.1, hs.2.norm⟩
-/
protected theorem IntegrableAtFilter.norm {f : α -> E} (hf : IntegrableAtFilter f l μ) :
    IntegrableAtFilter (fun x => ‖f x‖) l μ :=
  Exists.casesOn hf fun s hs => ⟨s, hs.1, hs.2.norm⟩

/--
theorem `IntegrableAtFilter.filter_mono` / 定理 `IntegrableAtFilter.filter_mono`

English:
theorem IntegrableAtFilter.filter_mono
  given: (hl : l <= l') (hl' : IntegrableAtFilter f l' μ)
  proof: let ⟨s, hs, hsf⟩ := hl'
  ⟨s, hl hs, hsf⟩

中文:
定理 整数egrableAtFilter.filter_mono
  条件: (hl : l <= l') (hl' : 整数egrableAtFilter f l' μ)
  证明: let ⟨s, hs, hsf⟩ := hl'
  ⟨s, hl hs, hsf⟩
-/
theorem IntegrableAtFilter.filter_mono (hl : l <= l') (hl' : IntegrableAtFilter f l' μ) :
    IntegrableAtFilter f l μ :=
  let ⟨s, hs, hsf⟩ := hl'
  ⟨s, hl hs, hsf⟩

/--
theorem `IntegrableAtFilter.inf_of_left` / 定理 `IntegrableAtFilter.inf_of_left`

English:
theorem IntegrableAtFilter.inf_of_left
  given: (hl : IntegrableAtFilter f l μ)
  proof: hl.filter_mono inf_le_left

中文:
定理 整数egrableAtFilter.inf_of_left
  条件: (hl : 整数egrableAtFilter f l μ)
  证明: hl.filter_mono inf_le_left

Depends on / 依赖: filter_mono, hl.filter_mono, inf_le_left
-/
theorem IntegrableAtFilter.inf_of_left (hl : IntegrableAtFilter f l μ) :
    IntegrableAtFilter f (l ⊓ l') μ :=
  hl.filter_mono inf_le_left

/--
theorem `IntegrableAtFilter.inf_of_right` / 定理 `IntegrableAtFilter.inf_of_right`

English:
theorem IntegrableAtFilter.inf_of_right
  given: (hl : IntegrableAtFilter f l μ)
  proof: hl.filter_mono inf_le_right

@[simp]

中文:
定理 整数egrableAtFilter.inf_of_right
  条件: (hl : 整数egrableAtFilter f l μ)
  证明: hl.filter_mono inf_le_right

@[simp]

Depends on / 依赖: filter_mono, hl.filter_mono, inf_le_right
-/
theorem IntegrableAtFilter.inf_of_right (hl : IntegrableAtFilter f l μ) :
    IntegrableAtFilter f (l' ⊓ l) μ :=
  hl.filter_mono inf_le_right

@[simp]
/--
theorem `IntegrableAtFilter.inf_ae_iff` / 定理 `IntegrableAtFilter.inf_ae_iff`

English:
theorem IntegrableAtFilter.inf_ae_iff
  given: {l : Filter α}
  proof: by
  refine ⟨?_, fun h => h.filter_mono inf_le_left⟩
  rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hf⟩
refine ⟨t, ht, hf.congr_set_ae eventuallyEq_set.2 ?_⟩
  filter_upwards [hu] with x hx using (and_iff_left hx).symm

alias ⟨IntegrableAtFilter.of_inf_ae, _⟩ := IntegrableAtFilter.inf_ae_iff

中文:
定理 整数egrableAtFilter.inf_ae_iff
  条件: {l : 滤子 α}
  证明: by
  refine ⟨?_, fun h => h.filter_mono inf_le_left⟩
  rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hf⟩
refine ⟨t, ht, hf.congr_set_ae eventuallyEq_set.2 ?_⟩
  filter_upwards [hu] with x hx using (and_iff_left hx).symm

alias ⟨IntegrableAtFilter.of_inf_ae, _⟩ := IntegrableAtFilter.inf_ae_iff

Depends on / 依赖: and_iff_left, congr_set_ae, eventuallyEq_set, filter_mono, filter_upwards, h.filter_mono, hf.congr_set_ae, inf_le_left
-/
theorem IntegrableAtFilter.inf_ae_iff {l : Filter α} :
    IntegrableAtFilter f (l ⊓ ae μ) μ ↔ IntegrableAtFilter f l μ := by
  refine ⟨?_, fun h => h.filter_mono inf_le_left⟩
  rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hf⟩
refine ⟨t, ht, hf.congr_set_ae eventuallyEq_set.2 ?_⟩
  filter_upwards [hu] with x hx using (and_iff_left hx).symm

alias ⟨IntegrableAtFilter.of_inf_ae, _⟩ := IntegrableAtFilter.inf_ae_iff

variable {ε' : Type*} [TopologicalSpace ε'] [ENormedAddMonoid ε'] in
@[simp]
/--
theorem `integrableAtFilter_top` / 定理 `integrableAtFilter_top`

English:
theorem integrableAtFilter_top
  given: [PseudoMetrizableSpace ε'] {f : α -> ε'}
  proof: by
  refine ⟨fun h => ?_, fun h => h.integrableAtFilter ⊤⟩
  obtain ⟨s, hsf, hs⟩ := h
  exact (integrableOn_iff_integrable_of_support_subset fun _ _ => hsf _).mp hs

中文:
定理 integrableAtFilter_top
  条件: [PseudoMetrizable空间 ε'] {f : α -> ε'}
  证明: by
  refine ⟨fun h => ?_, fun h => h.integrableAtFilter ⊤⟩
  obtain ⟨s, hsf, hs⟩ := h
  exact (integrableOn_iff_integrable_of_support_subset fun _ _ => hsf _).mp hs

Depends on / 依赖: h.integrableAtFilter, integrableAtFilter, integrableOn_iff_integrable_of_support_subset
-/
theorem integrableAtFilter_top [PseudoMetrizableSpace ε'] {f : α -> ε'} :
    IntegrableAtFilter f ⊤ μ ↔ Integrable f μ := by
  refine ⟨fun h => ?_, fun h => h.integrableAtFilter ⊤⟩
  obtain ⟨s, hsf, hs⟩ := h
  exact (integrableOn_iff_integrable_of_support_subset fun _ _ => hsf _).mp hs

/--
theorem `IntegrableAtFilter.sup_iff` / 定理 `IntegrableAtFilter.sup_iff`

English:
theorem IntegrableAtFilter.sup_iff
  given: [PseudoMetrizableSpace ε'] {f : α -> ε'} {l l' : Filter α}
  proof: by
  constructor
  · exact fun h => ⟨h.filter_mono le_sup_left, h.filter_mono le_sup_right⟩
  · exact fun ⟨⟨s, hsl, hs⟩, ⟨t, htl, ht⟩⟩ => ⟨s union t, union_mem_sup hsl htl, hs.union ht⟩

中文:
定理 整数egrableAtFilter.sup_iff
  条件: [PseudoMetrizable空间 ε'] {f : α -> ε'} {l l' : 滤子 α}
  证明: by
  constructor
  · exact fun h => ⟨h.filter_mono le_sup_left, h.filter_mono le_sup_right⟩
  · exact fun ⟨⟨s, hsl, hs⟩, ⟨t, htl, ht⟩⟩ => ⟨s union t, union_mem_sup hsl htl, hs.union ht⟩

Depends on / 依赖: filter_mono, h.filter_mono, hs.union, le_sup_left, le_sup_right, union_mem_sup
-/
theorem IntegrableAtFilter.sup_iff [PseudoMetrizableSpace ε'] {f : α -> ε'} {l l' : Filter α} :
    IntegrableAtFilter f (l ⊔ l') μ ↔ IntegrableAtFilter f l μ ∧ IntegrableAtFilter f l' μ := by
  constructor
  · exact fun h => ⟨h.filter_mono le_sup_left, h.filter_mono le_sup_right⟩
  · exact fun ⟨⟨s, hsl, hs⟩, ⟨t, htl, ht⟩⟩ => ⟨s union t, union_mem_sup hsl htl, hs.union ht⟩

/--
theorem `_root_.ContinuousLinearMap.integrableAtFilter_comp` / 定理 `_root_.ContinuousLinearMap.integrableAtFilter_comp`

English:
theorem _root_.ContinuousLinearMap.integrableAtFilter_comp
  statement: {E H 𝕜 𝕜' : Type*}
  proof: let ⟨s, hs, hf⟩ := hf; ⟨s, hs, L.integrableOn_comp hf⟩

中文:
定理 _root_.连续线性映射.integrableAtFilter_comp
  结论: {E H 𝕜 𝕜' : 类型}
  证明: let ⟨s, hs, hf⟩ := hf; ⟨s, hs, L.integrableOn_comp hf⟩

Depends on / 依赖: L.integrableOn_comp, integrableOn_comp
-/
theorem _root_.ContinuousLinearMap.integrableAtFilter_comp {E H 𝕜 𝕜' : Type*}
    [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
    [NormedAddCommGroup E] [NormedSpace 𝕜' E] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {σ : 𝕜 ->+* 𝕜'} [RingHomIsometric σ] {f : α -> H} (L : H ->SL[σ] E)
    (hf : IntegrableAtFilter f l μ) : IntegrableAtFilter (L ∘ f) l μ :=
  let ⟨s, hs, hf⟩ := hf; ⟨s, hs, L.integrableOn_comp hf⟩

/--
theorem `Measure.FiniteAtFilter.integrableAtFilter` / 定理 `Measure.FiniteAtFilter.integrableAtFilter`

English:
theorem Measure.FiniteAtFilter.integrableAtFilter
  statement: {f : α -> E} {l : Filter α}
  proof: by
  obtain ⟨C, hC⟩ : exists C, forallᶠ s in l.smallSets, forall x in s, ‖f x‖ <= C :=
    hf.imp fun C hC => eventually_smallSets.2 ⟨_, hC, fun t => id⟩
  rcases (hfm.eventually.and (hμ.eventually.and hC)).exists_measurable_mem_of_smallSets with
    ⟨s, hsl, hsm, hfm, hμ, hC⟩
  refine ⟨s, hsl, ⟨hfm, .restrict_of_bounded hμ (C := C) ?_⟩⟩
  rw [ae_restrict_eq hsm]; rw [eventually_inf_principal]
  exact Eventually.of_forall hC

中文:
定理 测度.FiniteAtFilter.integrableAtFilter
  结论: {f : α -> E} {l : 滤子 α}
  证明: by
  obtain ⟨C, hC⟩ : exists C, forallᶠ s in l.smallSets, forall x in s, ‖f x‖ <= C :=
    hf.imp fun C hC => eventually_smallSets.2 ⟨_, hC, fun t => id⟩
  rcases (hfm.eventually.and (hμ.eventually.and hC)).exists_measurable_mem_of_smallSets with
    ⟨s, hsl, hsm, hfm, hμ, hC⟩
  refine ⟨s, hsl, ⟨hfm, .restrict_of_bounded hμ (C := C) ?_⟩⟩
  rw [ae_restrict_eq hsm]; rw [eventually_inf_principal]
  exact Eventually.of_forall hC

Depends on / 依赖: Eventually, Eventually.of_forall, ae_restrict_eq, eventually, eventually.and, eventually_inf_principal, eventually_smallSets, exists_measurable_mem_of_smallSets, hf.imp, hfm.eventually.and, l.smallSets, of_forall, restrict_of_bounded, smallSets
-/
theorem Measure.FiniteAtFilter.integrableAtFilter {f : α -> E} {l : Filter α}
    [IsMeasurablyGenerated l] (hfm : StronglyMeasurableAtFilter f l μ) (hμ : μ.FiniteAtFilter l)
    (hf : l.IsBoundedUnder (· <= ·) (norm ∘ f)) : IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ : exists C, forallᶠ s in l.smallSets, forall x in s, ‖f x‖ <= C :=
    hf.imp fun C hC => eventually_smallSets.2 ⟨_, hC, fun t => id⟩
  rcases (hfm.eventually.and (hμ.eventually.and hC)).exists_measurable_mem_of_smallSets with
    ⟨s, hsl, hsm, hfm, hμ, hC⟩
  refine ⟨s, hsl, ⟨hfm, .restrict_of_bounded hμ (C := C) ?_⟩⟩
  rw [ae_restrict_eq hsm]; rw [eventually_inf_principal]
  exact Eventually.of_forall hC

/--
theorem `Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae` / 定理 `Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae`

English:
theorem Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae
  statement: {f : α -> E} {l : Filter α}
  proof: (hμ.inf_of_left.integrableAtFilter (hfm.filter_mono inf_le_left)
      hf.norm.isBoundedUnder_le).of_inf_ae

alias _root_.Filter.Tendsto.integrableAtFilter_ae :=
  Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae

中文:
定理 测度.FiniteAtFilter.integrableAtFilter_of_tendsto_ae
  结论: {f : α -> E} {l : 滤子 α}
  证明: (hμ.inf_of_left.integrableAtFilter (hfm.filter_mono inf_le_left)
      hf.norm.isBoundedUnder_le).of_inf_ae

alias _root_.Filter.Tendsto.integrableAtFilter_ae :=
  Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae

Depends on / 依赖: filter_mono, hf.norm.isBoundedUnder_le, hfm.filter_mono, inf_le_left, inf_of_left, inf_of_left.integrableAtFilter, integrableAtFilter, isBoundedUnder_le, of_inf_ae
-/
theorem Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae {f : α -> E} {l : Filter α}
    [IsMeasurablyGenerated l] (hfm : StronglyMeasurableAtFilter f l μ) (hμ : μ.FiniteAtFilter l) {b}
    (hf : Tendsto f (l ⊓ ae μ) (𝓝 b)) : IntegrableAtFilter f l μ :=
  (hμ.inf_of_left.integrableAtFilter (hfm.filter_mono inf_le_left)
      hf.norm.isBoundedUnder_le).of_inf_ae

alias _root_.Filter.Tendsto.integrableAtFilter_ae :=
  Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae

/--
theorem `Measure.FiniteAtFilter.integrableAtFilter_of_tendsto` / 定理 `Measure.FiniteAtFilter.integrableAtFilter_of_tendsto`

English:
theorem Measure.FiniteAtFilter.integrableAtFilter_of_tendsto
  statement: {f : α -> E} {l : Filter α}
  proof: hμ.integrableAtFilter hfm hf.norm.isBoundedUnder_le

alias _root_.Filter.Tendsto.integrableAtFilter :=
  Measure.FiniteAtFilter.integrableAtFilter_of_tendsto

中文:
定理 测度.FiniteAtFilter.integrableAtFilter_of_tendsto
  结论: {f : α -> E} {l : 滤子 α}
  证明: hμ.integrableAtFilter hfm hf.norm.isBoundedUnder_le

alias _root_.Filter.Tendsto.integrableAtFilter :=
  Measure.FiniteAtFilter.integrableAtFilter_of_tendsto

Depends on / 依赖: hf.norm.isBoundedUnder_le, integrableAtFilter, isBoundedUnder_le
-/
theorem Measure.FiniteAtFilter.integrableAtFilter_of_tendsto {f : α -> E} {l : Filter α}
    [IsMeasurablyGenerated l] (hfm : StronglyMeasurableAtFilter f l μ) (hμ : μ.FiniteAtFilter l) {b}
    (hf : Tendsto f l (𝓝 b)) : IntegrableAtFilter f l μ :=
  hμ.integrableAtFilter hfm hf.norm.isBoundedUnder_le

alias _root_.Filter.Tendsto.integrableAtFilter :=
  Measure.FiniteAtFilter.integrableAtFilter_of_tendsto

/--
lemma `Measure.integrableOn_of_bounded` / 引理 `Measure.integrableOn_of_bounded`

English:
lemma Measure.integrableOn_of_bounded
  statement: {f : α -> E} (s_finite : μ s != ∞)
  proof: ⟨f_mble.restrict, .restrict_of_bounded (C := M) s_finite.lt_top f_bdd⟩

中文:
引理 测度.integrableOn_of_bounded
  结论: {f : α -> E} (s_finite : μ s != ∞)
  证明: ⟨f_mble.restrict, .restrict_of_bounded (C := M) s_finite.lt_top f_bdd⟩

Depends on / 依赖: f_bdd, f_mble, f_mble.restrict, lt_top, restrict, restrict_of_bounded, s_finite, s_finite.lt_top
-/
lemma Measure.integrableOn_of_bounded {f : α -> E} (s_finite : μ s != ∞)
    (f_mble : AEStronglyMeasurable f μ) {M : Real} (f_bdd : forallᵐ a ∂(μ.restrict s), ‖f a‖ <= M) :
    IntegrableOn f s μ :=
  ⟨f_mble.restrict, .restrict_of_bounded (C := M) s_finite.lt_top f_bdd⟩

/--
theorem `integrable_add_of_disjoint` / 定理 `integrable_add_of_disjoint`

English:
theorem integrable_add_of_disjoint
  statement: {f g : α -> E} (h : Disjoint (support f) (support g))
  proof: by
  refine ⟨fun hfg => ⟨?_, ?_⟩, fun h => h.1.add h.2⟩
  · rw [← indicator_add_eq_left h]; exact hfg.indicator hf.measurableSet_support
  · rw [← indicator_add_eq_right h]; exact hfg.indicator hg.measurableSet_support

中文:
定理 integrable_add_of_disjoint
  结论: {f g : α -> E} (h : Disjoint (support f) (support g))
  证明: by
  refine ⟨fun hfg => ⟨?_, ?_⟩, fun h => h.1.add h.2⟩
  · rw [← indicator_add_eq_left h]; exact hfg.indicator hf.measurableSet_support
  · rw [← indicator_add_eq_right h]; exact hfg.indicator hg.measurableSet_support

Depends on / 依赖: hf.measurableSet_support, hfg.indicator, hg.measurableSet_support, indicator, indicator_add_eq_left, indicator_add_eq_right, measurableSet_support
-/
theorem integrable_add_of_disjoint {f g : α -> E} (h : Disjoint (support f) (support g))
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ := by
  refine ⟨fun hfg => ⟨?_, ?_⟩, fun h => h.1.add h.2⟩
  · rw [← indicator_add_eq_left h]; exact hfg.indicator hf.measurableSet_support
  · rw [← indicator_add_eq_right h]; exact hfg.indicator hg.measurableSet_support

/--
lemma `IntegrableAtFilter.eq_zero_of_tendsto` / 引理 `IntegrableAtFilter.eq_zero_of_tendsto`

English:
lemma IntegrableAtFilter.eq_zero_of_tendsto
  statement: {f : α -> E}
  proof: by
  by_contra H
  obtain ⟨ε, εpos, hε⟩ : exists (ε : Real), 0 < ε ∧ ε < ‖a‖ := exists_between (norm_pos_iff.mpr H)
  rcases h with ⟨u, ul, hu⟩
  let v := u inter {b | ε < ‖f b‖}
  have hv : IntegrableOn f v μ := hu.mono_set inter_subset_left
  have vl : v in l := inter_mem ul ((tendsto_order.1 hf.norm).1 _ hε)
  have : μ.restrict v v < ∞ := lt_of_le_of_lt (measure_mono inter_subset_right)
    (Integrable.measure_gt_lt_top hv.norm εpos)
  have : μ v != ∞ := ne_of_lt (by simpa only [Measure.restrict_apply_self])
  exact this (h' v vl)

中文:
引理 整数egrableAtFilter.eq_zero_of_tendsto
  结论: {f : α -> E}
  证明: by
  by_contra H
  obtain ⟨ε, εpos, hε⟩ : exists (ε : Real), 0 < ε ∧ ε < ‖a‖ := exists_between (norm_pos_iff.mpr H)
  rcases h with ⟨u, ul, hu⟩
  let v := u inter {b | ε < ‖f b‖}
  have hv : IntegrableOn f v μ := hu.mono_set inter_subset_left
  have vl : v in l := inter_mem ul ((tendsto_order.1 hf.norm).1 _ hε)
  have : μ.restrict v v < ∞ := lt_of_le_of_lt (measure_mono inter_subset_right)
    (Integrable.measure_gt_lt_top hv.norm εpos)
  have : μ v != ∞ := ne_of_lt (by simpa only [Measure.restrict_apply_self])
  exact this (h' v vl)

Depends on / 依赖: Integrable, Integrable.measure_gt_lt_top, IntegrableOn, Measure, Measure.restrict_apply_self, exists_between, hf.norm, hu.mono_set, hv.norm, inter_mem, inter_subset_left, inter_subset_right, lt_of_le_of_lt, measure_gt_lt_top, measure_mono, mono_set, ne_of_lt, norm_pos_iff, norm_pos_iff.mpr, restrict
-/
lemma IntegrableAtFilter.eq_zero_of_tendsto {f : α -> E}
    (h : IntegrableAtFilter f l μ) (h' : forall s in l, μ s = ∞) {a : E}
    (hf : Tendsto f l (𝓝 a)) : a = 0 := by
  by_contra H
  obtain ⟨ε, εpos, hε⟩ : exists (ε : Real), 0 < ε ∧ ε < ‖a‖ := exists_between (norm_pos_iff.mpr H)
  rcases h with ⟨u, ul, hu⟩
  let v := u inter {b | ε < ‖f b‖}
  have hv : IntegrableOn f v μ := hu.mono_set inter_subset_left
  have vl : v in l := inter_mem ul ((tendsto_order.1 hf.norm).1 _ hε)
  have : μ.restrict v v < ∞ := lt_of_le_of_lt (measure_mono inter_subset_right)
    (Integrable.measure_gt_lt_top hv.norm εpos)
  have : μ v != ∞ := ne_of_lt (by simpa only [Measure.restrict_apply_self])
  exact this (h' v vl)

end NormedAddCommGroup

end MeasureTheory

open MeasureTheory

variable [NormedAddCommGroup E]

/--
theorem `ContinuousOn.aemeasurable` / 定理 `ContinuousOn.aemeasurable`

English:
theorem ContinuousOn.aemeasurable
  statement: [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
  proof: by
  classical
  nontriviality α; inhabit α
  have : (Set.piecewise s f fun _ => f default) =ᵐ[μ.restrict s] f := piecewise_ae_eq_restrict hs
  refine ⟨Set.piecewise s f fun _ => f default, ?_, this.symm⟩
  apply measurable_of_isOpen
  intro t ht
  obtain ⟨u, u_open, hu⟩ : exists u : Set α, IsOpen u ∧ f ⁻¹' t inter s = u inter s :=
    _root_.continuousOn_iff'.1 hf t ht
  rw [piecewise_preimage]; rw [Set.ite]; rw [hu]
  exact (u_open.measurableSet.inter hs).union ((measurable_const ht.measurableSet).diff hs)

中文:
定理 ContinuousOn.aemeasurable
  结论: [拓扑空间 α] [OpensMeasurable空间 α] [可测空间 β]
  证明: by
  classical
  nontriviality α; inhabit α
  have : (Set.piecewise s f fun _ => f default) =ᵐ[μ.restrict s] f := piecewise_ae_eq_restrict hs
  refine ⟨Set.piecewise s f fun _ => f default, ?_, this.symm⟩
  apply measurable_of_isOpen
  intro t ht
  obtain ⟨u, u_open, hu⟩ : exists u : Set α, IsOpen u ∧ f ⁻¹' t inter s = u inter s :=
    _root_.continuousOn_iff'.1 hf t ht
  rw [piecewise_preimage]; rw [Set.ite]; rw [hu]
  exact (u_open.measurableSet.inter hs).union ((measurable_const ht.measurableSet).diff hs)

Depends on / 依赖: IsOpen, Set.ite, Set.piecewise, _root_, _root_.continuousOn_iff, classical, continuousOn_iff, ht.measurableSet, inhabit, measurableSet, measurable_const, measurable_of_isOpen, nontriviality, piecewise, piecewise_ae_eq_restrict, piecewise_preimage, restrict, this.symm, u_open, u_open.measurableSet.inter
-/
theorem ContinuousOn.aemeasurable [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β] {f : α -> β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) : AEMeasurable f (μ.restrict s) := by
  classical
  nontriviality α; inhabit α
  have : (Set.piecewise s f fun _ => f default) =ᵐ[μ.restrict s] f := piecewise_ae_eq_restrict hs
  refine ⟨Set.piecewise s f fun _ => f default, ?_, this.symm⟩
  apply measurable_of_isOpen
  intro t ht
  obtain ⟨u, u_open, hu⟩ : exists u : Set α, IsOpen u ∧ f ⁻¹' t inter s = u inter s :=
    _root_.continuousOn_iff'.1 hf t ht
  rw [piecewise_preimage]; rw [Set.ite]; rw [hu]
  exact (u_open.measurableSet.inter hs).union ((measurable_const ht.measurableSet).diff hs)

/--
theorem `ContinuousOn.aemeasurable₀` / 定理 `ContinuousOn.aemeasurable₀`

English:
theorem ContinuousOn.aemeasurable₀
  statement: [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
  proof: by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  rw [← Measure.restrict_congr_set t_eq_s]
  exact ContinuousOn.aemeasurable (hf.mono ts) ht

中文:
定理 ContinuousOn.aemeasurable₀
  结论: [拓扑空间 α] [OpensMeasurable空间 α] [可测空间 β]
  证明: by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  rw [← Measure.restrict_congr_set t_eq_s]
  exact ContinuousOn.aemeasurable (hf.mono ts) ht

Depends on / 依赖: ContinuousOn, ContinuousOn.aemeasurable, Measure, Measure.restrict_congr_set, aemeasurable, exists_measurable_subset_ae_eq, hf.mono, hs.exists_measurable_subset_ae_eq, restrict_congr_set, t_eq_s
-/
theorem ContinuousOn.aemeasurable₀ [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β] {f : α -> β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : NullMeasurableSet s μ) : AEMeasurable f (μ.restrict s) := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  rw [← Measure.restrict_congr_set t_eq_s]
  exact ContinuousOn.aemeasurable (hf.mono ts) ht

/--
theorem `ContinuousOn.aestronglyMeasurable_of_isSeparable` / 定理 `ContinuousOn.aestronglyMeasurable_of_isSeparable`

English:
theorem ContinuousOn.aestronglyMeasurable_of_isSeparable
  statement: [TopologicalSpace α]
  proof: by
  let := pseudoMetrizableSpacePseudoMetric α
  borelize β
  rw [aestronglyMeasurable_iff_aemeasurable_separable]
  refine ⟨hf.aemeasurable hs, f '' s, hf.isSeparable_image h's, ?_⟩
  exact mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _)

中文:
定理 ContinuousOn.aestronglyMeasurable_of_isSeparable
  结论: [拓扑空间 α]
  证明: by
  let := pseudoMetrizableSpacePseudoMetric α
  borelize β
  rw [aestronglyMeasurable_iff_aemeasurable_separable]
  refine ⟨hf.aemeasurable hs, f '' s, hf.isSeparable_image h's, ?_⟩
  exact mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _)

Depends on / 依赖: aemeasurable, aestronglyMeasurable_iff_aemeasurable_separable, borelize, hf.aemeasurable, hf.isSeparable_image, isSeparable_image, mem_of_superset, pseudoMetrizableSpacePseudoMetric, self_mem_ae_restrict, subset_preimage_image
-/
theorem ContinuousOn.aestronglyMeasurable_of_isSeparable [TopologicalSpace α]
    [PseudoMetrizableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β]
    [PseudoMetrizableSpace β] {f : α -> β} {s : Set α} {μ : Measure α} (hf : ContinuousOn f s)
    (hs : MeasurableSet s) (h's : TopologicalSpace.IsSeparable s) :
    AEStronglyMeasurable f (μ.restrict s) := by
  let := pseudoMetrizableSpacePseudoMetric α
  borelize β
  rw [aestronglyMeasurable_iff_aemeasurable_separable]
  refine ⟨hf.aemeasurable hs, f '' s, hf.isSeparable_image h's, ?_⟩
  exact mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _)

/--
theorem `ContinuousOn.aestronglyMeasurable` / 定理 `ContinuousOn.aestronglyMeasurable`

English:
theorem ContinuousOn.aestronglyMeasurable
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: by
  borelize β
  refine
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨hf.aemeasurable hs, f '' s, ?_,
        mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _)⟩
  cases h.out
  · rw [image_eq_range]
exact isSeparable_range continuousOn_iff_continuous_domRestrict.1 hf
  · exact .of_separableSpace _

中文:
定理 ContinuousOn.aestronglyMeasurable
  结论: [拓扑空间 α] [拓扑空间 β]
  证明: by
  borelize β
  refine
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨hf.aemeasurable hs, f '' s, ?_,
        mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _)⟩
  cases h.out
  · rw [image_eq_range]
exact isSeparable_range continuousOn_iff_continuous_domRestrict.1 hf
  · exact .of_separableSpace _

Depends on / 依赖: aemeasurable, aestronglyMeasurable_iff_aemeasurable_separable, borelize, continuousOn_iff_continuous_domRestrict, h.out, hf.aemeasurable, image_eq_range, isSeparable_range, mem_of_superset, of_separableSpace, self_mem_ae_restrict, subset_preimage_image
-/
theorem ContinuousOn.aestronglyMeasurable [TopologicalSpace α] [TopologicalSpace β]
    [h : SecondCountableTopologyEither α β] [OpensMeasurableSpace α] [PseudoMetrizableSpace β]
    {f : α -> β} {s : Set α} {μ : Measure α} (hf : ContinuousOn f s) (hs : MeasurableSet s) :
    AEStronglyMeasurable f (μ.restrict s) := by
  borelize β
  refine
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨hf.aemeasurable hs, f '' s, ?_,
        mem_of_superset (self_mem_ae_restrict hs) (subset_preimage_image _ _)⟩
  cases h.out
  · rw [image_eq_range]
exact isSeparable_range continuousOn_iff_continuous_domRestrict.1 hf
  · exact .of_separableSpace _

/--
theorem `ContinuousOn.aestronglyMeasurable_of_subset_isCompact` / 定理 `ContinuousOn.aestronglyMeasurable_of_subset_isCompact`

English:
theorem ContinuousOn.aestronglyMeasurable_of_subset_isCompact
  proof: by
  borelize β
  rw [aestronglyMeasurable_iff_aemeasurable_separable]
  refine ⟨(hf.mono hts).aemeasurable ht, f '' s, ?_, ?_⟩
  · exact (hs.image_of_continuousOn hf).isSeparable
  · filter_upwards [ae_restrict_mem ht] with a ha using image_mono hts (mem_image_of_mem f ha)

中文:
定理 ContinuousOn.aestronglyMeasurable_of_subset_isCompact
  证明: by
  borelize β
  rw [aestronglyMeasurable_iff_aemeasurable_separable]
  refine ⟨(hf.mono hts).aemeasurable ht, f '' s, ?_, ?_⟩
  · exact (hs.image_of_continuousOn hf).isSeparable
  · filter_upwards [ae_restrict_mem ht] with a ha using image_mono hts (mem_image_of_mem f ha)

Depends on / 依赖: ae_restrict_mem, aemeasurable, aestronglyMeasurable_iff_aemeasurable_separable, borelize, filter_upwards, hf.mono, hs.image_of_continuousOn, image_mono, image_of_continuousOn, isSeparable, mem_image_of_mem
-/
theorem ContinuousOn.aestronglyMeasurable_of_subset_isCompact
    [TopologicalSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [PseudoMetrizableSpace β] {f : α -> β} {s t : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : IsCompact s) (ht : MeasurableSet t) (hts : t subseteq s) :
    AEStronglyMeasurable f (μ.restrict t) := by
  borelize β
  rw [aestronglyMeasurable_iff_aemeasurable_separable]
  refine ⟨(hf.mono hts).aemeasurable ht, f '' s, ?_, ?_⟩
  · exact (hs.image_of_continuousOn hf).isSeparable
  · filter_upwards [ae_restrict_mem ht] with a ha using image_mono hts (mem_image_of_mem f ha)

/--
theorem `ContinuousOn.aestronglyMeasurable_of_isCompact` / 定理 `ContinuousOn.aestronglyMeasurable_of_isCompact`

English:
theorem ContinuousOn.aestronglyMeasurable_of_isCompact
  statement: [TopologicalSpace α] [OpensMeasurableSpace α]
  proof: hf.aestronglyMeasurable_of_subset_isCompact hs h's Subset.rfl

中文:
定理 ContinuousOn.aestronglyMeasurable_of_isCompact
  结论: [拓扑空间 α] [OpensMeasurable空间 α]
  证明: hf.aestronglyMeasurable_of_subset_isCompact hs h's Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, aestronglyMeasurable_of_subset_isCompact, hf.aestronglyMeasurable_of_subset_isCompact
-/
theorem ContinuousOn.aestronglyMeasurable_of_isCompact [TopologicalSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [PseudoMetrizableSpace β] {f : α -> β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : IsCompact s) (h's : MeasurableSet s) :
    AEStronglyMeasurable f (μ.restrict s) :=
  hf.aestronglyMeasurable_of_subset_isCompact hs h's Subset.rfl

/--
lemma `Continuous.aestronglyMeasurable_of_compactSpace` / 引理 `Continuous.aestronglyMeasurable_of_compactSpace`

English:
lemma Continuous.aestronglyMeasurable_of_compactSpace
  statement: [TopologicalSpace α] [OpensMeasurableSpace α]
  proof: by
  simpa using hf.continuousOn.aestronglyMeasurable_of_isCompact isCompact_univ .univ

中文:
引理 连续.aestronglyMeasurable_of_compactSpace
  结论: [拓扑空间 α] [OpensMeasurable空间 α]
  证明: by
  simpa using hf.continuousOn.aestronglyMeasurable_of_isCompact isCompact_univ .univ

Depends on / 依赖: aestronglyMeasurable_of_isCompact, continuousOn, hf.continuousOn.aestronglyMeasurable_of_isCompact, isCompact_univ
-/
lemma Continuous.aestronglyMeasurable_of_compactSpace [TopologicalSpace α] [OpensMeasurableSpace α]
    [CompactSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β] {μ : Measure α} {f : α -> β}
    (hf : Continuous f) : AEStronglyMeasurable f μ := by
  simpa using hf.continuousOn.aestronglyMeasurable_of_isCompact isCompact_univ .univ

/--
theorem `ContinuousOn.integrableAt_nhdsWithin_of_isSeparable` / 定理 `ContinuousOn.integrableAt_nhdsWithin_of_isSeparable`

English:
theorem ContinuousOn.integrableAt_nhdsWithin_of_isSeparable
  statement: [TopologicalSpace α]
  proof: haveI : (𝓝[t] a).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hft a ha).integrableAtFilter
    ⟨_, self_mem_nhdsWithin, hft.aestronglyMeasurable_of_isSeparable ht h't⟩
    (μ.finiteAt_nhdsWithin _ _)

中文:
定理 ContinuousOn.integrableAt_nhdsWithin_of_isSeparable
  结论: [拓扑空间 α]
  证明: haveI : (𝓝[t] a).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hft a ha).integrableAtFilter
    ⟨_, self_mem_nhdsWithin, hft.aestronglyMeasurable_of_isSeparable ht h't⟩
    (μ.finiteAt_nhdsWithin _ _)

Depends on / 依赖: IsMeasurablyGenerated, aestronglyMeasurable_of_isSeparable, finiteAt_nhdsWithin, hft.aestronglyMeasurable_of_isSeparable, ht.nhdsWithin_isMeasurablyGenerated, integrableAtFilter, nhdsWithin_isMeasurablyGenerated, self_mem_nhdsWithin
-/
theorem ContinuousOn.integrableAt_nhdsWithin_of_isSeparable [TopologicalSpace α]
    [PseudoMetrizableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsLocallyFiniteMeasure μ]
    {a : α} {t : Set α} {f : α -> E} (hft : ContinuousOn f t) (ht : MeasurableSet t)
    (h't : TopologicalSpace.IsSeparable t) (ha : a in t) : IntegrableAtFilter f (𝓝[t] a) μ :=
  haveI : (𝓝[t] a).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hft a ha).integrableAtFilter
    ⟨_, self_mem_nhdsWithin, hft.aestronglyMeasurable_of_isSeparable ht h't⟩
    (μ.finiteAt_nhdsWithin _ _)

/--
theorem `ContinuousOn.integrableAt_nhdsWithin` / 定理 `ContinuousOn.integrableAt_nhdsWithin`

English:
theorem ContinuousOn.integrableAt_nhdsWithin
  statement: [TopologicalSpace α]
  proof: haveI : (𝓝[t] a).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hft a ha).integrableAtFilter ⟨_, self_mem_nhdsWithin, hft.aestronglyMeasurable ht⟩
    (μ.finiteAt_nhdsWithin _ _)

中文:
定理 ContinuousOn.integrableAt_nhdsWithin
  结论: [拓扑空间 α]
  证明: haveI : (𝓝[t] a).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hft a ha).integrableAtFilter ⟨_, self_mem_nhdsWithin, hft.aestronglyMeasurable ht⟩
    (μ.finiteAt_nhdsWithin _ _)

Depends on / 依赖: IsMeasurablyGenerated, aestronglyMeasurable, finiteAt_nhdsWithin, hft.aestronglyMeasurable, ht.nhdsWithin_isMeasurablyGenerated, integrableAtFilter, nhdsWithin_isMeasurablyGenerated, self_mem_nhdsWithin
-/
theorem ContinuousOn.integrableAt_nhdsWithin [TopologicalSpace α]
    [SecondCountableTopologyEither α E] [OpensMeasurableSpace α] {μ : Measure α}
    [IsLocallyFiniteMeasure μ] {a : α} {t : Set α} {f : α -> E} (hft : ContinuousOn f t)
    (ht : MeasurableSet t) (ha : a in t) : IntegrableAtFilter f (𝓝[t] a) μ :=
  haveI : (𝓝[t] a).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hft a ha).integrableAtFilter ⟨_, self_mem_nhdsWithin, hft.aestronglyMeasurable ht⟩
    (μ.finiteAt_nhdsWithin _ _)

/--
theorem `Continuous.integrableAt_nhds` / 定理 `Continuous.integrableAt_nhds`

English:
theorem Continuous.integrableAt_nhds
  statement: [TopologicalSpace α] [SecondCountableTopologyEither α E]
  proof: by
  rw [← nhdsWithin_univ]
  exact hf.continuousOn.integrableAt_nhdsWithin MeasurableSet.univ (mem_univ a)

中文:
定理 连续.integrableAt_nhds
  结论: [拓扑空间 α] [SecondCountableTopologyEither α E]
  证明: by
  rw [← nhdsWithin_univ]
  exact hf.continuousOn.integrableAt_nhdsWithin MeasurableSet.univ (mem_univ a)

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, continuousOn, hf.continuousOn.integrableAt_nhdsWithin, integrableAt_nhdsWithin, mem_univ, nhdsWithin_univ
-/
theorem Continuous.integrableAt_nhds [TopologicalSpace α] [SecondCountableTopologyEither α E]
    [OpensMeasurableSpace α] {μ : Measure α} [IsLocallyFiniteMeasure μ] {f : α -> E}
    (hf : Continuous f) (a : α) : IntegrableAtFilter f (𝓝 a) μ := by
  rw [← nhdsWithin_univ]
  exact hf.continuousOn.integrableAt_nhdsWithin MeasurableSet.univ (mem_univ a)

/--
theorem `ContinuousOn.stronglyMeasurableAtFilter` / 定理 `ContinuousOn.stronglyMeasurableAtFilter`

English:
theorem ContinuousOn.stronglyMeasurableAtFilter
  statement: [TopologicalSpace α] [OpensMeasurableSpace α]
  proof: fun _x hx =>
  ⟨s, IsOpen.mem_nhds hs hx, hf.aestronglyMeasurable hs.measurableSet⟩

中文:
定理 ContinuousOn.stronglyMeasurableAtFilter
  结论: [拓扑空间 α] [OpensMeasurable空间 α]
  证明: fun _x hx =>
  ⟨s, IsOpen.mem_nhds hs hx, hf.aestronglyMeasurable hs.measurableSet⟩
-/
theorem ContinuousOn.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] {f : α -> β}
    {s : Set α} {μ : Measure α} (hs : IsOpen s) (hf : ContinuousOn f s) :
    forall x in s, StronglyMeasurableAtFilter f (𝓝 x) μ := fun _x hx =>
  ⟨s, IsOpen.mem_nhds hs hx, hf.aestronglyMeasurable hs.measurableSet⟩

/--
theorem `ContinuousAt.stronglyMeasurableAtFilter` / 定理 `ContinuousAt.stronglyMeasurableAtFilter`

English:
theorem ContinuousAt.stronglyMeasurableAtFilter
  statement: [TopologicalSpace α] [OpensMeasurableSpace α]
  proof: ContinuousOn.stronglyMeasurableAtFilter hs continuousOn_of_forall_continuousAt hf

中文:
定理 ContinuousAt.stronglyMeasurableAtFilter
  结论: [拓扑空间 α] [OpensMeasurable空间 α]
  证明: ContinuousOn.stronglyMeasurableAtFilter hs continuousOn_of_forall_continuousAt hf

Depends on / 依赖: ContinuousOn, ContinuousOn.stronglyMeasurableAtFilter, continuousOn_of_forall_continuousAt, stronglyMeasurableAtFilter
-/
theorem ContinuousAt.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopologyEither α E] {f : α -> E} {s : Set α} {μ : Measure α} (hs : IsOpen s)
    (hf : forall x in s, ContinuousAt f x) : forall x in s, StronglyMeasurableAtFilter f (𝓝 x) μ :=
ContinuousOn.stronglyMeasurableAtFilter hs continuousOn_of_forall_continuousAt hf

/--
theorem `Continuous.stronglyMeasurableAtFilter` / 定理 `Continuous.stronglyMeasurableAtFilter`

English:
theorem Continuous.stronglyMeasurableAtFilter
  statement: [TopologicalSpace α] [OpensMeasurableSpace α]
  proof: hf.stronglyMeasurable.stronglyMeasurableAtFilter

中文:
定理 连续.stronglyMeasurableAtFilter
  结论: [拓扑空间 α] [OpensMeasurable空间 α]
  证明: hf.stronglyMeasurable.stronglyMeasurableAtFilter

Depends on / 依赖: hf.stronglyMeasurable.stronglyMeasurableAtFilter, stronglyMeasurable, stronglyMeasurableAtFilter
-/
theorem Continuous.stronglyMeasurableAtFilter [TopologicalSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] {f : α -> β}
    (hf : Continuous f) (μ : Measure α) (l : Filter α) : StronglyMeasurableAtFilter f l μ :=
  hf.stronglyMeasurable.stronglyMeasurableAtFilter

/--
theorem `ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin` / 定理 `ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin`

English:
theorem ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin
  statement: {α β : Type*} [MeasurableSpace α]
  proof: ⟨s, self_mem_nhdsWithin, hf.aestronglyMeasurable hs⟩

中文:
定理 ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin
  结论: {α β : 类型} [可测空间 α]
  证明: ⟨s, self_mem_nhdsWithin, hf.aestronglyMeasurable hs⟩

Depends on / 依赖: aestronglyMeasurable, hf.aestronglyMeasurable, self_mem_nhdsWithin
-/
theorem ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin {α β : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [SecondCountableTopologyEither α β] {f : α -> β} {s : Set α} {μ : Measure α}
    (hf : ContinuousOn f s) (hs : MeasurableSet s) (x : α) :
    StronglyMeasurableAtFilter f (𝓝[s] x) μ :=
  ⟨s, self_mem_nhdsWithin, hf.aestronglyMeasurable hs⟩

/-! ### Lemmas about adding and removing interval boundaries

The primed lemmas take explicit arguments about the measure being finite at the endpoint, while
the unprimed ones use `[NullSingletonClass μ]`.
-/


section PartialOrder

variable [PartialOrder α] [MeasurableSingletonClass α]
  [TopologicalSpace ε'] [ESeminormedAddMonoid ε'] [PseudoMetrizableSpace ε']
  {f : α -> ε'} {μ : Measure α} {a b : α}

/--
theorem `integrableOn_Icc_iff_integrableOn_Ioc'` / 定理 `integrableOn_Icc_iff_integrableOn_Ioc'`

English:
theorem integrableOn_Icc_iff_integrableOn_Ioc'
  proof: by
  by_cases hab : a <= b
  · rw [← Ioc_union_left hab, integrableOn_union, eq_true (integrableOn_singleton ha'), and_true]
  · rw [Icc_eq_empty hab, Ioc_eq_empty]
    contrapose hab
    exact hab.le

中文:
定理 integrableOn_Icc_iff_integrableOn_Ioc'
  证明: by
  by_cases hab : a <= b
  · rw [← Ioc_union_left hab, integrableOn_union, eq_true (integrableOn_singleton ha'), and_true]
  · rw [Icc_eq_empty hab, Ioc_eq_empty]
    contrapose hab
    exact hab.le

Depends on / 依赖: Icc_eq_empty, IntegrableOn, Ioc_eq_empty, Ioc_union_left, and_true, contrapose, eq_true, finiteness, hab.le, integrableOn_singleton, integrableOn_union
-/
theorem integrableOn_Icc_iff_integrableOn_Ioc'
    (ha : μ {a} != ∞ := by finiteness) (ha' : ‖f a‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioc a b) μ := by
  by_cases hab : a <= b
  · rw [← Ioc_union_left hab, integrableOn_union, eq_true (integrableOn_singleton ha'), and_true]
  · rw [Icc_eq_empty hab, Ioc_eq_empty]
    contrapose hab
    exact hab.le

/--
theorem `integrableOn_Icc_iff_integrableOn_Ico'` / 定理 `integrableOn_Icc_iff_integrableOn_Ico'`

English:
theorem integrableOn_Icc_iff_integrableOn_Ico'
  proof: by
  by_cases hab : a <= b
  · rw [← Ico_union_right hab, integrableOn_union, eq_true (integrableOn_singleton hb'), and_true]
  · rw [Icc_eq_empty hab, Ico_eq_empty]
    contrapose hab
    exact hab.le

中文:
定理 integrableOn_Icc_iff_integrableOn_Ico'
  证明: by
  by_cases hab : a <= b
  · rw [← Ico_union_right hab, integrableOn_union, eq_true (integrableOn_singleton hb'), and_true]
  · rw [Icc_eq_empty hab, Ico_eq_empty]
    contrapose hab
    exact hab.le

Depends on / 依赖: Icc_eq_empty, Ico_eq_empty, Ico_union_right, IntegrableOn, NonemptyChain, NonemptyChain.carrier, and_true, carrier, contrapose, eq_true, finiteness, hab.le, integrableOn_singleton, integrableOn_union
-/
theorem integrableOn_Icc_iff_integrableOn_Ico'
    (hb : μ {b} != ∞) (hb' : ‖f b‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ico a b) μ := by
  by_cases hab : a <= b
  · rw [← Ico_union_right hab, integrableOn_union, eq_true (integrableOn_singleton hb'), and_true]
  · rw [Icc_eq_empty hab, Ico_eq_empty]
    contrapose hab
    exact hab.le

/--
theorem `integrableOn_Ico_iff_integrableOn_Ioo'` / 定理 `integrableOn_Ico_iff_integrableOn_Ioo'`

English:
theorem integrableOn_Ico_iff_integrableOn_Ioo'
  proof: by
  by_cases hab : a < b
  · rw [← Ioo_union_left hab, integrableOn_union,
      eq_true (integrableOn_singleton ha'), and_true]
  · rw [Ioo_eq_empty hab, Ico_eq_empty hab]

中文:
定理 integrableOn_Ico_iff_integrableOn_Ioo'
  证明: by
  by_cases hab : a < b
  · rw [← Ioo_union_left hab, integrableOn_union,
      eq_true (integrableOn_singleton ha'), and_true]
  · rw [Ioo_eq_empty hab, Ico_eq_empty hab]

Depends on / 依赖: Ico_eq_empty, IntegrableOn, Ioo_eq_empty, Ioo_union_left, NonemptyChain, and_true, eq_true, finiteness, integrableOn_singleton, integrableOn_union, ofSetLike
-/
theorem integrableOn_Ico_iff_integrableOn_Ioo'
    (ha : μ {a} != ∞) (ha' : ‖f a‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Ico a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  by_cases hab : a < b
  · rw [← Ioo_union_left hab, integrableOn_union,
      eq_true (integrableOn_singleton ha'), and_true]
  · rw [Ioo_eq_empty hab, Ico_eq_empty hab]

/--
theorem `integrableOn_Ioc_iff_integrableOn_Ioo'` / 定理 `integrableOn_Ioc_iff_integrableOn_Ioo'`

English:
theorem integrableOn_Ioc_iff_integrableOn_Ioo'
  proof: by
  by_cases hab : a < b
  · rw [← Ioo_union_right hab, integrableOn_union, eq_true (integrableOn_singleton hb'), and_true]
  · rw [Ioo_eq_empty hab, Ioc_eq_empty hab]

中文:
定理 integrableOn_Ioc_iff_integrableOn_Ioo'
  证明: by
  by_cases hab : a < b
  · rw [← Ioo_union_right hab, integrableOn_union, eq_true (integrableOn_singleton hb'), and_true]
  · rw [Ioo_eq_empty hab, Ioc_eq_empty hab]

Depends on / 依赖: IntegrableOn, Ioc_eq_empty, Ioo_eq_empty, Ioo_union_right, and_true, eq_true, finiteness, integrableOn_singleton, integrableOn_union
-/
theorem integrableOn_Ioc_iff_integrableOn_Ioo'
    (hb : μ {b} != ∞) (hb' : ‖f b‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Ioc a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  by_cases hab : a < b
  · rw [← Ioo_union_right hab, integrableOn_union, eq_true (integrableOn_singleton hb'), and_true]
  · rw [Ioo_eq_empty hab, Ioc_eq_empty hab]

/--
theorem `integrableOn_Icc_iff_integrableOn_Ioo'` / 定理 `integrableOn_Icc_iff_integrableOn_Ioo'`

English:
theorem integrableOn_Icc_iff_integrableOn_Ioo'
  statement: (ha : μ {a} != ∞)
  proof: by
  rw [integrableOn_Icc_iff_integrableOn_Ioc' ha ha']; rw [integrableOn_Ioc_iff_integrableOn_Ioo' hb hb']

中文:
定理 integrableOn_Icc_iff_integrableOn_Ioo'
  结论: (ha : μ {a} != ∞)
  证明: by
  rw [integrableOn_Icc_iff_integrableOn_Ioc' ha ha']; rw [integrableOn_Ioc_iff_integrableOn_Ioo' hb hb']

Depends on / 依赖: IntegrableOn, finiteness, integrableOn_Icc_iff_integrableOn_Ioc, integrableOn_Ioc_iff_integrableOn_Ioo
-/
theorem integrableOn_Icc_iff_integrableOn_Ioo' (ha : μ {a} != ∞)
    (ha' : ‖f a‖ₑ != ∞ := by finiteness) (hb : μ {b} != ∞) (hb' : ‖f b‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc' ha ha']; rw [integrableOn_Ioc_iff_integrableOn_Ioo' hb hb']

/--
theorem `integrableOn_Ici_iff_integrableOn_Ioi'` / 定理 `integrableOn_Ici_iff_integrableOn_Ioi'`

English:
theorem integrableOn_Ici_iff_integrableOn_Ioi'
  proof: by
  rw [← Ioi_union_left]; rw [integrableOn_union]; rw [eq_true (integrableOn_singleton hb')]; rw [and_true]

中文:
定理 integrableOn_Ici_iff_integrableOn_Ioi'
  证明: by
  rw [← Ioi_union_left]; rw [integrableOn_union]; rw [eq_true (integrableOn_singleton hb')]; rw [and_true]

Depends on / 依赖: IntegrableOn, Ioi_union_left, and_true, eq_true, finiteness, integrableOn_singleton, integrableOn_union
-/
theorem integrableOn_Ici_iff_integrableOn_Ioi'
    (hb : μ {b} != ∞ := by finiteness) (hb' : ‖f b‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Ici b) μ ↔ IntegrableOn f (Ioi b) μ := by
  rw [← Ioi_union_left]; rw [integrableOn_union]; rw [eq_true (integrableOn_singleton hb')]; rw [and_true]

/--
theorem `integrableOn_Iic_iff_integrableOn_Iio'` / 定理 `integrableOn_Iic_iff_integrableOn_Iio'`

English:
theorem integrableOn_Iic_iff_integrableOn_Iio'
  proof: by
  rw [← Iio_union_right]; rw [integrableOn_union]; rw [eq_true (integrableOn_singleton hb')]; rw [and_true]

中文:
定理 integrableOn_Iic_iff_integrableOn_Iio'
  证明: by
  rw [← Iio_union_right]; rw [integrableOn_union]; rw [eq_true (integrableOn_singleton hb')]; rw [and_true]

Depends on / 依赖: Iio_union_right, IntegrableOn, and_true, eq_true, finiteness, integrableOn_singleton, integrableOn_union
-/
theorem integrableOn_Iic_iff_integrableOn_Iio'
    (hb : μ {b} != ∞ := by finiteness) (hb' : ‖f b‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Iic b) μ ↔ IntegrableOn f (Iio b) μ := by
  rw [← Iio_union_right]; rw [integrableOn_union]; rw [eq_true (integrableOn_singleton hb')]; rw [and_true]

variable [NullSingletonClass μ]

/--
theorem `integrableOn_Icc_iff_integrableOn_Ioc` / 定理 `integrableOn_Icc_iff_integrableOn_Ioc`

English:
theorem integrableOn_Icc_iff_integrableOn_Ioc
  given: (ha : ‖f a‖ₑ != ∞ := by finiteness)
  proof: integrableOn_Icc_iff_integrableOn_Ioc' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) ha

中文:
定理 integrableOn_Icc_iff_integrableOn_Ioc
  条件: (ha : ‖f a‖ₑ != ∞ := by finiteness)
  证明: integrableOn_Icc_iff_integrableOn_Ioc' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) ha

Depends on / 依赖: ENNReal, ENNReal.zero_ne_top, IntegrableOn, finiteness, integrableOn_Icc_iff_integrableOn_Ioc, measure_singleton, zero_ne_top
-/
theorem integrableOn_Icc_iff_integrableOn_Ioc (ha : ‖f a‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioc a b) μ :=
  integrableOn_Icc_iff_integrableOn_Ioc' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) ha

/--
theorem `integrableOn_Icc_iff_integrableOn_Ico` / 定理 `integrableOn_Icc_iff_integrableOn_Ico`

English:
theorem integrableOn_Icc_iff_integrableOn_Ico
  given: (hb : ‖f b‖ₑ != ∞ := by finiteness)
  proof: integrableOn_Icc_iff_integrableOn_Ico' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

中文:
定理 integrableOn_Icc_iff_integrableOn_Ico
  条件: (hb : ‖f b‖ₑ != ∞ := by finiteness)
  证明: integrableOn_Icc_iff_integrableOn_Ico' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

Depends on / 依赖: ENNReal, ENNReal.zero_ne_top, IntegrableOn, finiteness, integrableOn_Icc_iff_integrableOn_Ico, measure_singleton, zero_ne_top
-/
theorem integrableOn_Icc_iff_integrableOn_Ico (hb : ‖f b‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ico a b) μ :=
  integrableOn_Icc_iff_integrableOn_Ico' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

/--
theorem `integrableOn_Ico_iff_integrableOn_Ioo` / 定理 `integrableOn_Ico_iff_integrableOn_Ioo`

English:
theorem integrableOn_Ico_iff_integrableOn_Ioo
  given: (ha : ‖f a‖ₑ != ∞ := by finiteness)
  proof: integrableOn_Ico_iff_integrableOn_Ioo' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) ha

中文:
定理 integrableOn_Ico_iff_integrableOn_Ioo
  条件: (ha : ‖f a‖ₑ != ∞ := by finiteness)
  证明: integrableOn_Ico_iff_integrableOn_Ioo' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) ha

Depends on / 依赖: ENNReal, ENNReal.zero_ne_top, IntegrableOn, finiteness, integrableOn_Ico_iff_integrableOn_Ioo, measure_singleton, zero_ne_top
-/
theorem integrableOn_Ico_iff_integrableOn_Ioo (ha : ‖f a‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Ico a b) μ ↔ IntegrableOn f (Ioo a b) μ :=
  integrableOn_Ico_iff_integrableOn_Ioo' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) ha

/--
theorem `integrableOn_Ioc_iff_integrableOn_Ioo` / 定理 `integrableOn_Ioc_iff_integrableOn_Ioo`

English:
theorem integrableOn_Ioc_iff_integrableOn_Ioo
  given: (hb : ‖f b‖ₑ != ∞ := by finiteness)
  proof: integrableOn_Ioc_iff_integrableOn_Ioo' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

中文:
定理 integrableOn_Ioc_iff_integrableOn_Ioo
  条件: (hb : ‖f b‖ₑ != ∞ := by finiteness)
  证明: integrableOn_Ioc_iff_integrableOn_Ioo' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

Depends on / 依赖: ENNReal, ENNReal.zero_ne_top, IntegrableOn, finiteness, integrableOn_Ioc_iff_integrableOn_Ioo, measure_singleton, zero_ne_top
-/
theorem integrableOn_Ioc_iff_integrableOn_Ioo (hb : ‖f b‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Ioc a b) μ ↔ IntegrableOn f (Ioo a b) μ :=
  integrableOn_Ioc_iff_integrableOn_Ioo' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

/--
theorem `integrableOn_Icc_iff_integrableOn_Ioo` / 定理 `integrableOn_Icc_iff_integrableOn_Ioo`

English:
theorem integrableOn_Icc_iff_integrableOn_Ioo
  proof: by
  rw [integrableOn_Icc_iff_integrableOn_Ioc ha]; rw [integrableOn_Ioc_iff_integrableOn_Ioo hb]

中文:
定理 integrableOn_Icc_iff_integrableOn_Ioo
  证明: by
  rw [integrableOn_Icc_iff_integrableOn_Ioc ha]; rw [integrableOn_Ioc_iff_integrableOn_Ioo hb]

Depends on / 依赖: IntegrableOn, finiteness, integrableOn_Icc_iff_integrableOn_Ioc, integrableOn_Ioc_iff_integrableOn_Ioo
-/
theorem integrableOn_Icc_iff_integrableOn_Ioo
    (ha : ‖f a‖ₑ != ∞ := by finiteness) (hb : ‖f b‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Icc a b) μ ↔ IntegrableOn f (Ioo a b) μ := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc ha]; rw [integrableOn_Ioc_iff_integrableOn_Ioo hb]

/--
theorem `integrableOn_Ici_iff_integrableOn_Ioi` / 定理 `integrableOn_Ici_iff_integrableOn_Ioi`

English:
theorem integrableOn_Ici_iff_integrableOn_Ioi
  given: (hb : ‖f b‖ₑ != ∞ := by finiteness)
  proof: integrableOn_Ici_iff_integrableOn_Ioi' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

中文:
定理 integrableOn_Ici_iff_integrableOn_Ioi
  条件: (hb : ‖f b‖ₑ != ∞ := by finiteness)
  证明: integrableOn_Ici_iff_integrableOn_Ioi' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

Depends on / 依赖: ENNReal, ENNReal.zero_ne_top, IntegrableOn, finiteness, integrableOn_Ici_iff_integrableOn_Ioi, measure_singleton, zero_ne_top
-/
theorem integrableOn_Ici_iff_integrableOn_Ioi (hb : ‖f b‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Ici b) μ ↔ IntegrableOn f (Ioi b) μ :=
  integrableOn_Ici_iff_integrableOn_Ioi' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

/--
theorem `integrableOn_Iic_iff_integrableOn_Iio` / 定理 `integrableOn_Iic_iff_integrableOn_Iio`

English:
theorem integrableOn_Iic_iff_integrableOn_Iio
  given: (hb : ‖f b‖ₑ != ∞ := by finiteness)
  proof: integrableOn_Iic_iff_integrableOn_Iio' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

中文:
定理 integrableOn_Iic_iff_integrableOn_Iio
  条件: (hb : ‖f b‖ₑ != ∞ := by finiteness)
  证明: integrableOn_Iic_iff_integrableOn_Iio' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

Depends on / 依赖: ENNReal, ENNReal.zero_ne_top, IntegrableOn, finiteness, integrableOn_Iic_iff_integrableOn_Iio, measure_singleton, zero_ne_top
-/
theorem integrableOn_Iic_iff_integrableOn_Iio (hb : ‖f b‖ₑ != ∞ := by finiteness) :
    IntegrableOn f (Iic b) μ ↔ IntegrableOn f (Iio b) μ :=
  integrableOn_Iic_iff_integrableOn_Iio' (by rw [measure_singleton]; exact ENNReal.zero_ne_top) hb

end PartialOrder
