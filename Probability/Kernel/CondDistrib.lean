/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Regular conditional probability distribution

We define the regular conditional probability distribution of `Y : α → Ω` given `X : α → β`, where
`Ω` is a standard Borel space. This is a `Kernel β Ω` such that for almost all `a`, `condDistrib`
evaluated at `X a` and a measurable set `s` is equal to the conditional expectation
`μ⟦Y ⁻¹' s | mβ.comap X⟧` evaluated at `a`.

`μ⟦Y ⁻¹' s | mβ.comap X⟧` maps a measurable set `s` to a function `α → ℝ≥0∞`, and for all `s` that
map is unique up to a `μ`-null set. For all `a`, the map from sets to `ℝ≥0∞` that we obtain that way
verifies some of the properties of a measure, but in general the fact that the `μ`-null set depends
on `s` can prevent us from finding versions of the conditional expectation that combine into a true
measure. The standard Borel space assumption on `Ω` allows us to do so.

The case `Y = X = id` is developed in more detail in `Mathlib/Probability/Kernel/Condexp.lean`: here
`X` is understood as a map from `Ω` with a sub-σ-algebra `m` to `Ω` with its default σ-algebra and
the conditional distribution defines a kernel associated with the conditional expectation with
respect to `m`.

## Main definitions

* `condDistrib Y X μ`: regular conditional probability distribution of `Y : α → Ω` given
  `X : α → β`, where `Ω` is a standard Borel space.

## Main statements

* `condDistrib_ae_eq_condExp`: for almost all `a`, `condDistrib` evaluated at `X a` and a
  measurable set `s` is equal to the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`.
* `condExp_prod_ae_eq_integral_condDistrib`: the conditional expectation
  `μ[(fun a => f (X a, Y a)) | X; mβ]` is almost everywhere equal to the integral
  `∫ y, f (X a, y) ∂(condDistrib Y X μ (X a))`.

-/

@[expose] public section


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω F : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [Nonempty Ω] [NormedAddCommGroup F] {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  {X : α -> β} {Y : α -> Ω}

/-- **Regular conditional probability distribution**: kernel associated with the conditional
expectation of `Y` given `X`.
For almost all `a`, `condDistrib Y X μ` evaluated at `X a` and a measurable set `s` is equal to
the conditional expectation `μ⟦Y ⁻¹' s | mβ.comap X⟧ a`. It also satisfies the equality
`μ[(fun a => f (X a, Y a)) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(condDistrib Y X μ (X a))`
for all integrable functions `f`. -/
noncomputable irreducible_def condDistrib {_ : MeasurableSpace α} [MeasurableSpace β] (Y : α -> Ω)
    (X : α -> β) (μ : Measure α) [IsFiniteMeasure μ] : Kernel β Ω :=
  (μ.map fun a => (X a, Y a)).condKernel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MeasurableSpace
  signature: β] : IsMarkovKernel (condDistrib Y X μ)
  body: by
  rw [condDistrib]; infer_instance

中文:
实例 [可测空间
  签名: β] : 是MarkovKernel (condDistrib Y X μ)
  定义体: by
  rw [condDistrib]; infer_instance

Depends on / 依赖: condDistrib, infer_instance
-/
instance [MeasurableSpace β] : IsMarkovKernel (condDistrib Y X μ) := by
  rw [condDistrib]; infer_instance

variable {mβ : MeasurableSpace β} {s : Set Ω} {t : Set β} {f : β × Ω -> F}

/--
lemma `condDistrib_apply_of_ne_zero` / 引理 `condDistrib_apply_of_ne_zero`

English:
lemma condDistrib_apply_of_ne_zero
  statement: [MeasurableSingletonClass β]
  proof: by
  rw [condDistrib]; rw [Measure.condKernel_apply_of_ne_zero _ s]
  · rw [Measure.fst_map_prodMk hY]
  · rwa [Measure.fst_map_prodMk hY]

中文:
引理 condDistrib_apply_of_ne_zero
  结论: [MeasurableSingleton类 β]
  证明: by
  rw [condDistrib]; rw [Measure.condKernel_apply_of_ne_zero _ s]
  · rw [Measure.fst_map_prodMk hY]
  · rwa [Measure.fst_map_prodMk hY]

Depends on / 依赖: Measure, Measure.condKernel_apply_of_ne_zero, Measure.fst_map_prodMk, condDistrib, condKernel_apply_of_ne_zero, fst_map_prodMk
-/
lemma condDistrib_apply_of_ne_zero [MeasurableSingletonClass β]
    (hY : Measurable Y) (x : β) (hX : μ.map X {x} != 0) (s : Set Ω) :
    condDistrib Y X μ x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s) := by
  rw [condDistrib]; rw [Measure.condKernel_apply_of_ne_zero _ s]
  · rw [Measure.fst_map_prodMk hY]
  · rwa [Measure.fst_map_prodMk hY]

/--
lemma `compProd_map_condDistrib` / 引理 `compProd_map_condDistrib`

English:
lemma compProd_map_condDistrib
  given: (hY : AEMeasurable Y μ)
  proof: by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ hY]; rw [Measure.disintegrate]

中文:
引理 compProd_map_condDistrib
  条件: (hY : 几乎处处可测 Y μ)
  证明: by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ hY]; rw [Measure.disintegrate]

Depends on / 依赖: Measure, Measure.disintegrate, Measure.fst_map_prodMk, condDistrib, disintegrate
-/
lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) :
    (μ.map X) otimesₘ condDistrib Y X μ = μ.map fun a => (X a, Y a) := by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ hY]; rw [Measure.disintegrate]

/--
lemma `condDistrib_comp_map` / 引理 `condDistrib_comp_map`

English:
lemma condDistrib_comp_map
  given: (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
  proof: by
  rw [← Measure.snd_compProd]; rw [compProd_map_condDistrib hY]; rw [Measure.snd_map_prodMk₀ hX]

中文:
引理 condDistrib_comp_map
  条件: (hX : 几乎处处可测 X μ) (hY : 几乎处处可测 Y μ)
  证明: by
  rw [← Measure.snd_compProd]; rw [compProd_map_condDistrib hY]; rw [Measure.snd_map_prodMk₀ hX]

Depends on / 依赖: Measure, Measure.snd_compProd, Measure.snd_map_prodMk, compProd_map_condDistrib, snd_compProd
-/
lemma condDistrib_comp_map (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Y X μ ∘ₘ (μ.map X) = μ.map Y := by
  rw [← Measure.snd_compProd]; rw [compProd_map_condDistrib hY]; rw [Measure.snd_map_prodMk₀ hX]

/--
lemma `condDistrib_congr` / 引理 `condDistrib_congr`

English:
lemma condDistrib_congr
  given: {X' : α -> β} {Y' : α -> Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X')
  proof: by
  rw [condDistrib]; rw [condDistrib]
  congr 1
  rw [Measure.map_congr]
  filter_upwards [hX, hY] with a ha hb using by rw [ha, hb]

中文:
引理 condDistrib_congr
  条件: {X' : α -> β} {Y' : α -> Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X')
  证明: by
  rw [condDistrib]; rw [condDistrib]
  congr 1
  rw [Measure.map_congr]
  filter_upwards [hX, hY] with a ha hb using by rw [ha, hb]

Depends on / 依赖: Measure, Measure.map_congr, condDistrib, filter_upwards, map_congr
-/
lemma condDistrib_congr {X' : α -> β} {Y' : α -> Ω} (hY : Y =ᵐ[μ] Y') (hX : X =ᵐ[μ] X') :
    condDistrib Y X μ = condDistrib Y' X' μ := by
  rw [condDistrib]; rw [condDistrib]
  congr 1
  rw [Measure.map_congr]
  filter_upwards [hX, hY] with a ha hb using by rw [ha, hb]

/--
lemma `condDistrib_congr_right` / 引理 `condDistrib_congr_right`

English:
lemma condDistrib_congr_right
  given: {X' : α -> β} (hX : X =ᵐ[μ] X')
  proof: condDistrib_congr (by rfl) hX

中文:
引理 condDistrib_congr_right
  条件: {X' : α -> β} (hX : X =ᵐ[μ] X')
  证明: condDistrib_congr (by rfl) hX

Depends on / 依赖: condDistrib_congr
-/
lemma condDistrib_congr_right {X' : α -> β} (hX : X =ᵐ[μ] X') :
    condDistrib Y X μ = condDistrib Y X' μ :=
  condDistrib_congr (by rfl) hX

/--
lemma `condDistrib_congr_left` / 引理 `condDistrib_congr_left`

English:
lemma condDistrib_congr_left
  given: {Y' : α -> Ω} (hY : Y =ᵐ[μ] Y')
  proof: condDistrib_congr hY (by rfl)

中文:
引理 condDistrib_congr_left
  条件: {Y' : α -> Ω} (hY : Y =ᵐ[μ] Y')
  证明: condDistrib_congr hY (by rfl)

Depends on / 依赖: condDistrib_congr
-/
lemma condDistrib_congr_left {Y' : α -> Ω} (hY : Y =ᵐ[μ] Y') :
    condDistrib Y X μ = condDistrib Y' X μ :=
  condDistrib_congr hY (by rfl)

section Measurability

/--
theorem `measurable_condDistrib` / 定理 `measurable_condDistrib`

English:
theorem measurable_condDistrib
  given: (hs : MeasurableSet s)
  proof: (Kernel.measurable_coe _ hs).comp (Measurable.of_comap_le le_rfl)

中文:
定理 measurable_condDistrib
  条件: (hs : 可测集 s)
  证明: (Kernel.measurable_coe _ hs).comp (Measurable.of_comap_le le_rfl)

Depends on / 依赖: Kernel, Kernel.measurable_coe, Measurable, Measurable.of_comap_le, le_rfl, measurable_coe, of_comap_le
-/
theorem measurable_condDistrib (hs : MeasurableSet s) :
    Measurable[mβ.comap X] fun a => condDistrib Y X μ (X a) s :=
  (Kernel.measurable_coe _ hs).comp (Measurable.of_comap_le le_rfl)

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
  proof: by
  rw [condDistrib]; rw [← hf.ae_integrable_condKernel_iff]; rw [Measure.fst_map_prodMk₀ hY]

中文:
定理 _root_.测度论.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
  证明: by
  rw [condDistrib]; rw [← hf.ae_integrable_condKernel_iff]; rw [Measure.fst_map_prodMk₀ hY]

Depends on / 依赖: Measure, Measure.fst_map_prodMk, ae_integrable_condKernel_iff, condDistrib, hf.ae_integrable_condKernel_iff
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    (forallᵐ a ∂μ.map X, Integrable (fun ω => f (a, ω)) (condDistrib Y X μ a)) ∧
      Integrable (fun a => ∫ ω, ‖f (a, ω)‖ ∂condDistrib Y X μ a) (μ.map X) ↔
    Integrable f (μ.map fun a => (X a, Y a)) := by
  rw [condDistrib]; rw [← hf.ae_integrable_condKernel_iff]; rw [Measure.fst_map_prodMk₀ hY]

variable [NormedSpace Real F]

/--
theorem `_root_.MeasureTheory.StronglyMeasurable.integral_condDistrib` / 定理 `_root_.MeasureTheory.StronglyMeasurable.integral_condDistrib`

English:
theorem _root_.MeasureTheory.StronglyMeasurable.integral_condDistrib
  given: (hf : StronglyMeasurable f)
  proof: by
  rw [condDistrib]; exact hf.integral_kernel_prod_right'

中文:
定理 _root_.测度论.StronglyMeasurable.integral_condDistrib
  条件: (hf : StronglyMeasurable f)
  证明: by
  rw [condDistrib]; exact hf.integral_kernel_prod_right'

Depends on / 依赖: condDistrib, hf.integral_kernel_prod_right, integral_kernel_prod_right
-/
theorem _root_.MeasureTheory.StronglyMeasurable.integral_condDistrib (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun x => ∫ y, f (x, y) ∂condDistrib Y X μ x) := by
  rw [condDistrib]; exact hf.integral_kernel_prod_right'

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map
  proof: by
  rw [← Measure.fst_map_prodMk₀ hY]; rw [condDistrib]; exact hf.integral_condKernel

中文:
定理 _root_.测度论.AEStronglyMeasurable.integral_condDistrib_map
  证明: by
  rw [← Measure.fst_map_prodMk₀ hY]; rw [condDistrib]; exact hf.integral_condKernel

Depends on / 依赖: Measure, Measure.fst_map_prodMk, condDistrib, hf.integral_condKernel, integral_condKernel
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂condDistrib Y X μ x) (μ.map X) := by
  rw [← Measure.fst_map_prodMk₀ hY]; rw [condDistrib]; exact hf.integral_condKernel

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib
  statement: (hX : AEMeasurable X μ)
  proof: (hf.integral_condDistrib_map hY).comp_aemeasurable hX

中文:
定理 _root_.测度论.AEStronglyMeasurable.integral_condDistrib
  结论: (hX : 几乎处处可测 X μ)
  证明: (hf.integral_condDistrib_map hY).comp_aemeasurable hX

Depends on / 依赖: comp_aemeasurable, hf.integral_condDistrib_map, integral_condDistrib_map
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf.integral_condDistrib_map hY).comp_aemeasurable hX

/--
theorem `stronglyMeasurable_integral_condDistrib` / 定理 `stronglyMeasurable_integral_condDistrib`

English:
theorem stronglyMeasurable_integral_condDistrib
  given: (hf : StronglyMeasurable f)
  proof: (hf.integral_condDistrib).comp_measurable Measurable.of_comap_le le_rfl

中文:
定理 stronglyMeasurable_integral_condDistrib
  条件: (hf : StronglyMeasurable f)
  证明: (hf.integral_condDistrib).comp_measurable Measurable.of_comap_le le_rfl

Depends on / 依赖: Measurable, Measurable.of_comap_le, comp_measurable, hf.integral_condDistrib, integral_condDistrib, le_rfl, of_comap_le
-/
theorem stronglyMeasurable_integral_condDistrib (hf : StronglyMeasurable f) :
    StronglyMeasurable[mβ.comap X] (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) :=
(hf.integral_condDistrib).comp_measurable Measurable.of_comap_le le_rfl

/--
theorem `aestronglyMeasurable_integral_condDistrib` / 定理 `aestronglyMeasurable_integral_condDistrib`

English:
theorem aestronglyMeasurable_integral_condDistrib
  statement: (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
  proof: (hf.integral_condDistrib_map hY).comp_ae_measurable' hX

中文:
定理 aestronglyMeasurable_integral_condDistrib
  结论: (hX : 几乎处处可测 X μ) (hY : 几乎处处可测 Y μ)
  证明: (hf.integral_condDistrib_map hY).comp_ae_measurable' hX

Depends on / 依赖: comp_ae_measurable, hf.integral_condDistrib_map, integral_condDistrib_map
-/
theorem aestronglyMeasurable_integral_condDistrib (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a))) :
    AEStronglyMeasurable[mβ.comap X] (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf.integral_condDistrib_map hY).comp_ae_measurable' hX

end Measurability

/--
theorem `condDistrib_ae_eq_of_measure_eq_compProd_of_measurable` / 定理 `condDistrib_ae_eq_of_measure_eq_compProd_of_measurable`

English:
theorem condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
  proof: by
  have heq : μ.map X = (μ.map (fun x => (X x, Y x))).fst := by
    ext s hs
    rw [Measure.map_apply hX hs]; rw [Measure.fst_apply hs]; rw [Measure.map_apply]
    exacts [rfl, Measurable.prod hX hY, measurable_fst hs]
  rw [heq]; rw [condDistrib]
  symm
  refine eq_condKernel_of_measure_eq_compProd _ ?_
  convert! hκ
  exact heq.symm

中文:
定理 condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
  证明: by
  have heq : μ.map X = (μ.map (fun x => (X x, Y x))).fst := by
    ext s hs
    rw [Measure.map_apply hX hs]; rw [Measure.fst_apply hs]; rw [Measure.map_apply]
    exacts [rfl, Measurable.prod hX hY, measurable_fst hs]
  rw [heq]; rw [condDistrib]
  symm
  refine eq_condKernel_of_measure_eq_compProd _ ?_
  convert! hκ
  exact heq.symm

Depends on / 依赖: Measurable, Measurable.prod, Measure, Measure.fst_apply, Measure.map_apply, condDistrib, convert, eq_condKernel_of_measure_eq_compProd, exacts, fst_apply, heq.symm, map_apply, measurable_fst
-/
theorem condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (hX : Measurable X) (hY : Measurable Y)
    {κ : Kernel β Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x, Y x)) = μ.map X otimesₘ κ) :
    condDistrib Y X μ =ᵐ[μ.map X] κ := by
  have heq : μ.map X = (μ.map (fun x => (X x, Y x))).fst := by
    ext s hs
    rw [Measure.map_apply hX hs]; rw [Measure.fst_apply hs]; rw [Measure.map_apply]
    exacts [rfl, Measurable.prod hX hY, measurable_fst hs]
  rw [heq]; rw [condDistrib]
  symm
  refine eq_condKernel_of_measure_eq_compProd _ ?_
  convert! hκ
  exact heq.symm

/--
lemma `condDistrib_ae_eq_of_measure_eq_compProd` / 引理 `condDistrib_ae_eq_of_measure_eq_compProd`

English:
lemma condDistrib_ae_eq_of_measure_eq_compProd
  proof: by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  suffices condDistrib (hY.mk Y) (hX.mk X) μ =ᵐ[μ.map (hX.mk X)] κ by
    rwa [Measure.map_congr hX.ae_eq_mk, condDistrib_congr hY.ae_eq_mk hX.ae_eq_mk]
  refine condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (μ := μ)
    hX.measurable_mk hY.measurable_mk ((Eq.trans ?_ hκ).trans ?_)
  · refine Measure.map_congr ?_
    filter_upwards [hX.ae_eq_mk, hY.ae_eq_mk] with a haX haY using by rw [haX, haY]
  · rw [Measure.map_congr hX.ae_eq_mk]

中文:
引理 condDistrib_ae_eq_of_measure_eq_compProd
  证明: by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  suffices condDistrib (hY.mk Y) (hX.mk X) μ =ᵐ[μ.map (hX.mk X)] κ by
    rwa [Measure.map_congr hX.ae_eq_mk, condDistrib_congr hY.ae_eq_mk hX.ae_eq_mk]
  refine condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (μ := μ)
    hX.measurable_mk hY.measurable_mk ((Eq.trans ?_ hκ).trans ?_)
  · refine Measure.map_congr ?_
    filter_upwards [hX.ae_eq_mk, hY.ae_eq_mk] with a haX haY using by rw [haX, haY]
  · rw [Measure.map_congr hX.ae_eq_mk]

Depends on / 依赖: AEMeasurable, Eq.trans, EventuallyEq, Filter, Filter.EventuallyEq, Measure, Measure.map_congr, Measure.map_of_not_aemeasurable, ae_eq_mk, condDistrib, condDistrib_ae_eq_of_measure_eq_compProd_of_measurable, condDistrib_congr, filter_upwards, hX.ae_eq_mk, hX.measurable_mk, hX.mk, hY.ae_eq_mk, hY.measurable_mk, hY.mk, map_congr
-/
lemma condDistrib_ae_eq_of_measure_eq_compProd
    (X : α -> β) (hY : AEMeasurable Y μ) {κ : Kernel β Ω} [IsFiniteKernel κ]
    (hκ : μ.map (fun x => (X x, Y x)) = μ.map X otimesₘ κ) :
    condDistrib Y X μ =ᵐ[μ.map X] κ := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  suffices condDistrib (hY.mk Y) (hX.mk X) μ =ᵐ[μ.map (hX.mk X)] κ by
    rwa [Measure.map_congr hX.ae_eq_mk, condDistrib_congr hY.ae_eq_mk hX.ae_eq_mk]
  refine condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (μ := μ)
    hX.measurable_mk hY.measurable_mk ((Eq.trans ?_ hκ).trans ?_)
  · refine Measure.map_congr ?_
    filter_upwards [hX.ae_eq_mk, hY.ae_eq_mk] with a haX haY using by rw [haX, haY]
  · rw [Measure.map_congr hX.ae_eq_mk]

/--
lemma `condDistrib_ae_eq_iff_measure_eq_compProd` / 引理 `condDistrib_ae_eq_iff_measure_eq_compProd`

English:
lemma condDistrib_ae_eq_iff_measure_eq_compProd
  proof: by
  refine ⟨fun h => ?_, condDistrib_ae_eq_of_measure_eq_compProd X hY⟩
  rw [Measure.compProd_congr h.symm]; rw [compProd_map_condDistrib hY]

中文:
引理 condDistrib_ae_eq_iff_measure_eq_compProd
  证明: by
  refine ⟨fun h => ?_, condDistrib_ae_eq_of_measure_eq_compProd X hY⟩
  rw [Measure.compProd_congr h.symm]; rw [compProd_map_condDistrib hY]

Depends on / 依赖: Measure, Measure.compProd_congr, compProd_congr, compProd_map_condDistrib, condDistrib_ae_eq_of_measure_eq_compProd, h.symm
-/
lemma condDistrib_ae_eq_iff_measure_eq_compProd
    (X : α -> β) (hY : AEMeasurable Y μ) (κ : Kernel β Ω) [IsFiniteKernel κ] :
    (condDistrib Y X μ =ᵐ[μ.map X] κ) ↔ μ.map (fun x => (X x, Y x)) = μ.map X otimesₘ κ := by
  refine ⟨fun h => ?_, condDistrib_ae_eq_of_measure_eq_compProd X hY⟩
  rw [Measure.compProd_congr h.symm]; rw [compProd_map_condDistrib hY]

/--
lemma `condDistrib_comp` / 引理 `condDistrib_comp`

English:
lemma condDistrib_comp
  statement: {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω']
  proof: by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  refine condDistrib_ae_eq_of_measure_eq_compProd X (by fun_prop) ?_
  calc μ.map (fun x => (X x, (f ∘ Y) x))
  _ = (μ.map (fun x => (X x, Y x))).map (Prod.map id f) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    simp [Function.comp_def]
  _ = (μ.map X otimesₘ condDistrib Y X μ).map (Prod.map id f) := by rw [compProd_map_condDistrib hY]
  _ = μ.map X otimesₘ (condDistrib Y X μ).map f := by rw [Measure.compProd_map hf]

中文:
引理 condDistrib_comp
  结论: {Ω' : 类型} {mΩ' : 可测空间 Ω'} [StandardBorel空间 Ω']
  证明: by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  refine condDistrib_ae_eq_of_measure_eq_compProd X (by fun_prop) ?_
  calc μ.map (fun x => (X x, (f ∘ Y) x))
  _ = (μ.map (fun x => (X x, Y x))).map (Prod.map id f) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    simp [Function.comp_def]
  _ = (μ.map X otimesₘ condDistrib Y X μ).map (Prod.map id f) := by rw [compProd_map_condDistrib hY]
  _ = μ.map X otimesₘ (condDistrib Y X μ).map f := by rw [Measure.compProd_map hf]

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, EventuallyEq, Filter, Filter.EventuallyEq, Function, Function.comp_def, Measure, Measure.map_of_not_aemeasurable, Prod.map, compProd_map_condDistrib, comp_def, condDistrib, condDistrib_ae_eq_of_measure_eq_compProd, fun_prop, map_map_of_aemeasurable, map_of_not_aemeasurable
-/
lemma condDistrib_comp {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω']
    [Nonempty Ω'] (X : α -> β) (hY : AEMeasurable Y μ) {f : Ω -> Ω'} (hf : Measurable f) :
    condDistrib (f ∘ Y) X μ =ᵐ[μ.map X] (condDistrib Y X μ).map f := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  refine condDistrib_ae_eq_of_measure_eq_compProd X (by fun_prop) ?_
  calc μ.map (fun x => (X x, (f ∘ Y) x))
  _ = (μ.map (fun x => (X x, Y x))).map (Prod.map id f) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    simp [Function.comp_def]
  _ = (μ.map X otimesₘ condDistrib Y X μ).map (Prod.map id f) := by rw [compProd_map_condDistrib hY]
  _ = μ.map X otimesₘ (condDistrib Y X μ).map f := by rw [Measure.compProd_map hf]

/--
lemma `condDistrib_comp_self` / 引理 `condDistrib_comp_self`

English:
lemma condDistrib_comp_self
  given: (X : α -> β) {f : β -> Ω} (hf : Measurable f)
  proof: by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  refine condDistrib_ae_eq_of_measure_eq_compProd X (by fun_prop) ?_
  rw [Measure.compProd_deterministic]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
  simp [Function.comp_def]

中文:
引理 condDistrib_comp_self
  条件: (X : α -> β) {f : β -> Ω} (hf : 可测 f)
  证明: by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  refine condDistrib_ae_eq_of_measure_eq_compProd X (by fun_prop) ?_
  rw [Measure.compProd_deterministic]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
  simp [Function.comp_def]

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, EventuallyEq, Filter, Filter.EventuallyEq, Function, Function.comp_def, Measure, Measure.compProd_deterministic, Measure.map_of_not_aemeasurable, compProd_deterministic, comp_def, condDistrib_ae_eq_of_measure_eq_compProd, fun_prop, map_map_of_aemeasurable, map_of_not_aemeasurable
-/
lemma condDistrib_comp_self (X : α -> β) {f : β -> Ω} (hf : Measurable f) :
    condDistrib (f ∘ X) X μ =ᵐ[μ.map X] Kernel.deterministic f hf := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  refine condDistrib_ae_eq_of_measure_eq_compProd X (by fun_prop) ?_
  rw [Measure.compProd_deterministic]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]
  simp [Function.comp_def]

/--
lemma `condDistrib_self` / 引理 `condDistrib_self`

English:
lemma condDistrib_self
  given: (Y : α -> Ω)
  statement: condDistrib Y Y μ =ᵐ[μ.map Y] Kernel.id
  proof: by
  simpa using! condDistrib_comp_self Y measurable_id

中文:
引理 condDistrib_self
  条件: (Y : α -> Ω)
  结论: condDistrib Y Y μ =ᵐ[μ.map Y] 核.id
  证明: by
  simpa using! condDistrib_comp_self Y measurable_id

Depends on / 依赖: condDistrib_comp_self, measurable_id
-/
lemma condDistrib_self (Y : α -> Ω) : condDistrib Y Y μ =ᵐ[μ.map Y] Kernel.id := by
  simpa using! condDistrib_comp_self Y measurable_id

/--
lemma `condDistrib_const` / 引理 `condDistrib_const`

English:
lemma condDistrib_const
  given: (X : α -> β) (c : Ω)
  proof: by
  have : (fun _ : α => c) = (fun _ : β => c) ∘ X := rfl
  rw [this]
  filter_upwards [condDistrib_comp_self X (measurable_const (a := c))] with b hb
  rw [hb]

中文:
引理 condDistrib_const
  条件: (X : α -> β) (c : Ω)
  证明: by
  have : (fun _ : α => c) = (fun _ : β => c) ∘ X := rfl
  rw [this]
  filter_upwards [condDistrib_comp_self X (measurable_const (a := c))] with b hb
  rw [hb]

Depends on / 依赖: condDistrib_comp_self, filter_upwards, fun_prop, measurable_const
-/
lemma condDistrib_const (X : α -> β) (c : Ω) :
    condDistrib (fun _ => c) X μ =ᵐ[μ.map X]
      Kernel.deterministic (mα := mβ) (fun _ => c) (by fun_prop) := by
  have : (fun _ : α => c) = (fun _ : β => c) ∘ X := rfl
  rw [this]
  filter_upwards [condDistrib_comp_self X (measurable_const (a := c))] with b hb
  rw [hb]

/--
lemma `condDistrib_map` / 引理 `condDistrib_map`

English:
lemma condDistrib_map
  statement: {γ : Type*} {mγ : MeasurableSpace γ}
  proof: by
  rw [← AEMeasurable.map_map_of_aemeasurable hX hf]
  refine condDistrib_ae_eq_of_measure_eq_compProd (μ := ν.map f) X hY ?_
  rw [AEMeasurable.map_map_of_aemeasurable hX hf]; rw [compProd_map_condDistrib (by fun_prop)]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  simp [Function.comp_def]

中文:
引理 condDistrib_map
  结论: {γ : 类型} {mγ : 可测空间 γ}
  证明: by
  rw [← AEMeasurable.map_map_of_aemeasurable hX hf]
  refine condDistrib_ae_eq_of_measure_eq_compProd (μ := ν.map f) X hY ?_
  rw [AEMeasurable.map_map_of_aemeasurable hX hf]; rw [compProd_map_condDistrib (by fun_prop)]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  simp [Function.comp_def]

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, Function, Function.comp_def, compProd_map_condDistrib, comp_def, condDistrib_ae_eq_of_measure_eq_compProd, fun_prop, map_map_of_aemeasurable
-/
lemma condDistrib_map {γ : Type*} {mγ : MeasurableSpace γ}
    {ν : Measure γ} [IsFiniteMeasure ν] {f : γ -> α}
    (hX : AEMeasurable X (ν.map f)) (hY : AEMeasurable Y (ν.map f)) (hf : AEMeasurable f ν) :
    condDistrib Y X (ν.map f) =ᵐ[ν.map (X ∘ f)] condDistrib (Y ∘ f) (X ∘ f) ν := by
  rw [← AEMeasurable.map_map_of_aemeasurable hX hf]
  refine condDistrib_ae_eq_of_measure_eq_compProd (μ := ν.map f) X hY ?_
  rw [AEMeasurable.map_map_of_aemeasurable hX hf]; rw [compProd_map_condDistrib (by fun_prop)]; rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hf]
  simp [Function.comp_def]

/--
lemma `condDistrib_fst_prod` / 引理 `condDistrib_fst_prod`

English:
lemma condDistrib_fst_prod
  statement: {γ : Type*} {mγ : MeasurableSpace γ}
  proof: by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.fst (α := α) (β := γ))
      (ν := μ.prod ν) (mα := inferInstance) (mβ := inferInstance)
      (by simpa) (by simpa) (by fun_prop)
  rw [← AEMeasurable.map_map_of_aemeasurable (by simpa) (by fun_prop)] at h_map
  simp only [Measure.map_fst_prod, measure_univ, one_smul] at h_map
  exact h_map.symm

中文:
引理 condDistrib_fst_prod
  结论: {γ : 类型} {mγ : 可测空间 γ}
  证明: by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.fst (α := α) (β := γ))
      (ν := μ.prod ν) (mα := inferInstance) (mβ := inferInstance)
      (by simpa) (by simpa) (by fun_prop)
  rw [← AEMeasurable.map_map_of_aemeasurable (by simpa) (by fun_prop)] at h_map
  simp only [Measure.map_fst_prod, measure_univ, one_smul] at h_map
  exact h_map.symm

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, EventuallyEq, Filter, Filter.EventuallyEq, Measure, Measure.map_fst_prod, Measure.map_of_not_aemeasurable, Prod.fst, condDistrib_map, fun_prop, h_map, h_map.symm, map_fst_prod, map_map_of_aemeasurable, map_of_not_aemeasurable, measure_univ, one_smul
-/
lemma condDistrib_fst_prod {γ : Type*} {mγ : MeasurableSpace γ}
    (X : α -> β) (hY : AEMeasurable Y μ) (ν : Measure γ) [IsProbabilityMeasure ν] :
    condDistrib (fun ω => Y ω.1) (fun ω => X ω.1) (μ.prod ν) =ᵐ[μ.map X] condDistrib Y X μ := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.fst (α := α) (β := γ))
      (ν := μ.prod ν) (mα := inferInstance) (mβ := inferInstance)
      (by simpa) (by simpa) (by fun_prop)
  rw [← AEMeasurable.map_map_of_aemeasurable (by simpa) (by fun_prop)] at h_map
  simp only [Measure.map_fst_prod, measure_univ, one_smul] at h_map
  exact h_map.symm

/--
lemma `condDistrib_snd_prod` / 引理 `condDistrib_snd_prod`

English:
lemma condDistrib_snd_prod
  statement: {γ : Type*} {mγ : MeasurableSpace γ}
  proof: by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.snd (β := α) (α := γ))
      (ν := ν.prod μ) (mα := inferInstance) (mβ := inferInstance)
      (by simpa) (by simpa) (by fun_prop)
  rw [← AEMeasurable.map_map_of_aemeasurable (by simpa) (by fun_prop)] at h_map
  simp only [Measure.map_snd_prod, measure_univ, one_smul] at h_map
  exact h_map.symm

中文:
引理 condDistrib_snd_prod
  结论: {γ : 类型} {mγ : 可测空间 γ}
  证明: by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.snd (β := α) (α := γ))
      (ν := ν.prod μ) (mα := inferInstance) (mβ := inferInstance)
      (by simpa) (by simpa) (by fun_prop)
  rw [← AEMeasurable.map_map_of_aemeasurable (by simpa) (by fun_prop)] at h_map
  simp only [Measure.map_snd_prod, measure_univ, one_smul] at h_map
  exact h_map.symm

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, EventuallyEq, Filter, Filter.EventuallyEq, Measure, Measure.map_of_not_aemeasurable, Measure.map_snd_prod, Prod.snd, condDistrib_map, fun_prop, h_map, h_map.symm, map_map_of_aemeasurable, map_of_not_aemeasurable, map_snd_prod, measure_univ, one_smul
-/
lemma condDistrib_snd_prod {γ : Type*} {mγ : MeasurableSpace γ}
    (X : α -> β) (hY : AEMeasurable Y μ) (ν : Measure γ) [IsProbabilityMeasure ν] :
    condDistrib (fun ω => Y ω.2) (fun ω => X ω.2) (ν.prod μ) =ᵐ[μ.map X] condDistrib Y X μ := by
  by_cases hX : AEMeasurable X μ
  swap; · simp [Measure.map_of_not_aemeasurable hX, Filter.EventuallyEq]
  have h_map := condDistrib_map (X := X) (Y := Y) (f := Prod.snd (β := α) (α := γ))
      (ν := ν.prod μ) (mα := inferInstance) (mβ := inferInstance)
      (by simpa) (by simpa) (by fun_prop)
  rw [← AEMeasurable.map_map_of_aemeasurable (by simpa) (by fun_prop)] at h_map
  simp only [Measure.map_snd_prod, measure_univ, one_smul] at h_map
  exact h_map.symm

section Integrability

/--
theorem `integrable_toReal_condDistrib` / 定理 `integrable_toReal_condDistrib`

English:
theorem integrable_toReal_condDistrib
  given: (hX : AEMeasurable X μ) (hs : MeasurableSet s)
  proof: by
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · exact Measurable.comp_aemeasurable (Kernel.measurable_coe _ hs) hX
  · refine ne_of_lt ?_
    calc
      ∫⁻ a, condDistrib Y X μ (X a) s ∂μ <= ∫⁻ _, 1 ∂μ := lintegral_mono fun a => prob_le_one
      _ = μ univ := lintegral_one
      _ < ∞ := measure_lt_top _ _

中文:
定理 integrable_to实数_condDistrib
  条件: (hX : 几乎处处可测 X μ) (hs : 可测集 s)
  证明: by
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · exact Measurable.comp_aemeasurable (Kernel.measurable_coe _ hs) hX
  · refine ne_of_lt ?_
    calc
      ∫⁻ a, condDistrib Y X μ (X a) s ∂μ <= ∫⁻ _, 1 ∂μ := lintegral_mono fun a => prob_le_one
      _ = μ univ := lintegral_one
      _ < ∞ := measure_lt_top _ _

Depends on / 依赖: Kernel, Kernel.measurable_coe, Measurable, Measurable.comp_aemeasurable, comp_aemeasurable, condDistrib, integrable_toReal_of_lintegral_ne_top, lintegral_mono, lintegral_one, measurable_coe, measure_lt_top, ne_of_lt, prob_le_one
-/
theorem integrable_toReal_condDistrib (hX : AEMeasurable X μ) (hs : MeasurableSet s) :
    Integrable (fun a => (condDistrib Y X μ (X a)).real s) μ := by
  refine integrable_toReal_of_lintegral_ne_top ?_ ?_
  · exact Measurable.comp_aemeasurable (Kernel.measurable_coe _ hs) hX
  · refine ne_of_lt ?_
    calc
      ∫⁻ a, condDistrib Y X μ (X a) s ∂μ <= ∫⁻ _, 1 ∂μ := lintegral_mono fun a => prob_le_one
      _ = μ univ := lintegral_one
      _ < ∞ := measure_lt_top _ _

/--
theorem `_root_.MeasureTheory.Integrable.condDistrib_ae_map` / 定理 `_root_.MeasureTheory.Integrable.condDistrib_ae_map`

English:
theorem _root_.MeasureTheory.Integrable.condDistrib_ae_map
  proof: by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.condKernel_ae

中文:
定理 _root_.测度论.可积.condDistrib_ae_map
  证明: by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.condKernel_ae

Depends on / 依赖: Measure, Measure.fst_map_prodMk, condDistrib, condKernel_ae, hf_int, hf_int.condKernel_ae
-/
theorem _root_.MeasureTheory.Integrable.condDistrib_ae_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    forallᵐ b ∂μ.map X, Integrable (fun ω => f (b, ω)) (condDistrib Y X μ b) := by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.condKernel_ae

/--
theorem `_root_.MeasureTheory.Integrable.condDistrib_ae` / 定理 `_root_.MeasureTheory.Integrable.condDistrib_ae`

English:
theorem _root_.MeasureTheory.Integrable.condDistrib_ae
  statement: (hX : AEMeasurable X μ)
  proof: ae_of_ae_map hX (hf_int.condDistrib_ae_map hY)

中文:
定理 _root_.测度论.可积.condDistrib_ae
  结论: (hX : 几乎处处可测 X μ)
  证明: ae_of_ae_map hX (hf_int.condDistrib_ae_map hY)

Depends on / 依赖: ae_of_ae_map, condDistrib_ae_map, hf_int, hf_int.condDistrib_ae_map
-/
theorem _root_.MeasureTheory.Integrable.condDistrib_ae (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    forallᵐ a ∂μ, Integrable (fun ω => f (X a, ω)) (condDistrib Y X μ (X a)) :=
  ae_of_ae_map hX (hf_int.condDistrib_ae_map hY)

/--
theorem `_root_.MeasureTheory.Integrable.integral_norm_condDistrib_map` / 定理 `_root_.MeasureTheory.Integrable.integral_norm_condDistrib_map`

English:
theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib_map
  proof: by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.integral_norm_condKernel

中文:
定理 _root_.测度论.可积.integral_norm_condDistrib_map
  证明: by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.integral_norm_condKernel

Depends on / 依赖: Measure, Measure.fst_map_prodMk, condDistrib, hf_int, hf_int.integral_norm_condKernel, integral_norm_condKernel
-/
theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂condDistrib Y X μ x) (μ.map X) := by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.integral_norm_condKernel

/--
theorem `_root_.MeasureTheory.Integrable.integral_norm_condDistrib` / 定理 `_root_.MeasureTheory.Integrable.integral_norm_condDistrib`

English:
theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib
  statement: (hX : AEMeasurable X μ)
  proof: (hf_int.integral_norm_condDistrib_map hY).comp_aemeasurable hX

中文:
定理 _root_.测度论.可积.integral_norm_condDistrib
  结论: (hX : 几乎处处可测 X μ)
  证明: (hf_int.integral_norm_condDistrib_map hY).comp_aemeasurable hX

Depends on / 依赖: comp_aemeasurable, hf_int, hf_int.integral_norm_condDistrib_map, integral_norm_condDistrib_map
-/
theorem _root_.MeasureTheory.Integrable.integral_norm_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, ‖f (X a, y)‖ ∂condDistrib Y X μ (X a)) μ :=
  (hf_int.integral_norm_condDistrib_map hY).comp_aemeasurable hX

variable [NormedSpace Real F]

/--
theorem `_root_.MeasureTheory.Integrable.norm_integral_condDistrib_map` / 定理 `_root_.MeasureTheory.Integrable.norm_integral_condDistrib_map`

English:
theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib_map
  proof: by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.norm_integral_condKernel

中文:
定理 _root_.测度论.可积.norm_integral_condDistrib_map
  证明: by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.norm_integral_condKernel

Depends on / 依赖: Measure, Measure.fst_map_prodMk, condDistrib, hf_int, hf_int.norm_integral_condKernel, norm_integral_condKernel
-/
theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ‖∫ y, f (x, y) ∂condDistrib Y X μ x‖) (μ.map X) := by
  rw [condDistrib]; rw [← Measure.fst_map_prodMk₀ (X := X) hY]; exact hf_int.norm_integral_condKernel

/--
theorem `_root_.MeasureTheory.Integrable.norm_integral_condDistrib` / 定理 `_root_.MeasureTheory.Integrable.norm_integral_condDistrib`

English:
theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib
  statement: (hX : AEMeasurable X μ)
  proof: (hf_int.norm_integral_condDistrib_map hY).comp_aemeasurable hX

中文:
定理 _root_.测度论.可积.norm_integral_condDistrib
  结论: (hX : 几乎处处可测 X μ)
  证明: (hf_int.norm_integral_condDistrib_map hY).comp_aemeasurable hX

Depends on / 依赖: comp_aemeasurable, hf_int, hf_int.norm_integral_condDistrib_map, norm_integral_condDistrib_map
-/
theorem _root_.MeasureTheory.Integrable.norm_integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ‖∫ y, f (X a, y) ∂condDistrib Y X μ (X a)‖) μ :=
  (hf_int.norm_integral_condDistrib_map hY).comp_aemeasurable hX

/--
theorem `_root_.MeasureTheory.Integrable.integral_condDistrib_map` / 定理 `_root_.MeasureTheory.Integrable.integral_condDistrib_map`

English:
theorem _root_.MeasureTheory.Integrable.integral_condDistrib_map
  proof: (integrable_norm_iff (hf_int.1.integral_condDistrib_map hY)).mp
    (hf_int.norm_integral_condDistrib_map hY)

中文:
定理 _root_.测度论.可积.integral_condDistrib_map
  证明: (integrable_norm_iff (hf_int.1.integral_condDistrib_map hY)).mp
    (hf_int.norm_integral_condDistrib_map hY)

Depends on / 依赖: hf_int, hf_int.norm_integral_condDistrib_map, integrable_norm_iff, integral_condDistrib_map, norm_integral_condDistrib_map
-/
theorem _root_.MeasureTheory.Integrable.integral_condDistrib_map
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun x => ∫ y, f (x, y) ∂condDistrib Y X μ x) (μ.map X) :=
  (integrable_norm_iff (hf_int.1.integral_condDistrib_map hY)).mp
    (hf_int.norm_integral_condDistrib_map hY)

/--
theorem `_root_.MeasureTheory.Integrable.integral_condDistrib` / 定理 `_root_.MeasureTheory.Integrable.integral_condDistrib`

English:
theorem _root_.MeasureTheory.Integrable.integral_condDistrib
  statement: (hX : AEMeasurable X μ)
  proof: (hf_int.integral_condDistrib_map hY).comp_aemeasurable hX

中文:
定理 _root_.测度论.可积.integral_condDistrib
  结论: (hX : 几乎处处可测 X μ)
  证明: (hf_int.integral_condDistrib_map hY).comp_aemeasurable hX

Depends on / 依赖: comp_aemeasurable, hf_int, hf_int.integral_condDistrib_map, integral_condDistrib_map
-/
theorem _root_.MeasureTheory.Integrable.integral_condDistrib (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    Integrable (fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a)) μ :=
  (hf_int.integral_condDistrib_map hY).comp_aemeasurable hX

end Integrability

/--
theorem `setLIntegral_preimage_condDistrib` / 定理 `setLIntegral_preimage_condDistrib`

English:
theorem setLIntegral_preimage_condDistrib
  statement: (hX : Measurable X) (hY : AEMeasurable Y μ)
  proof: by
  rw [← lintegral_map (Kernel.measurable_coe _ hs) hX]; rw [condDistrib]; rw [← Measure.restrict_map hX ht]; rw [← Measure.fst_map_prodMk₀ hY]; rw [Measure.setLIntegral_condKernel_eq_measure_prod ht hs]; rw [Measure.map_apply_of_aemeasurable (hX.aemeasurable.prodMk hY) (ht.prod hs)]; rw [mk_preimage_prod]

中文:
定理 setL整数egral_preimage_condDistrib
  结论: (hX : 可测 X) (hY : 几乎处处可测 Y μ)
  证明: by
  rw [← lintegral_map (Kernel.measurable_coe _ hs) hX]; rw [condDistrib]; rw [← Measure.restrict_map hX ht]; rw [← Measure.fst_map_prodMk₀ hY]; rw [Measure.setLIntegral_condKernel_eq_measure_prod ht hs]; rw [Measure.map_apply_of_aemeasurable (hX.aemeasurable.prodMk hY) (ht.prod hs)]; rw [mk_preimage_prod]

Depends on / 依赖: Kernel, Kernel.measurable_coe, Measure, Measure.fst_map_prodMk, Measure.map_apply_of_aemeasurable, Measure.restrict_map, Measure.setLIntegral_condKernel_eq_measure_prod, aemeasurable, condDistrib, hX.aemeasurable.prodMk, ht.prod, lintegral_map, map_apply_of_aemeasurable, measurable_coe, mk_preimage_prod, prodMk, restrict_map, setLIntegral_condKernel_eq_measure_prod
-/
theorem setLIntegral_preimage_condDistrib (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ a in X ⁻¹' t, condDistrib Y X μ (X a) s ∂μ = μ (X ⁻¹' t inter Y ⁻¹' s) := by
  rw [← lintegral_map (Kernel.measurable_coe _ hs) hX]; rw [condDistrib]; rw [← Measure.restrict_map hX ht]; rw [← Measure.fst_map_prodMk₀ hY]; rw [Measure.setLIntegral_condKernel_eq_measure_prod ht hs]; rw [Measure.map_apply_of_aemeasurable (hX.aemeasurable.prodMk hY) (ht.prod hs)]; rw [mk_preimage_prod]

/--
theorem `setLIntegral_condDistrib_of_measurableSet` / 定理 `setLIntegral_condDistrib_of_measurableSet`

English:
theorem setLIntegral_condDistrib_of_measurableSet
  statement: (hX : Measurable X) (hY : AEMeasurable Y μ)
  proof: by
  obtain ⟨t', ht', rfl⟩ := ht
  rw [setLIntegral_preimage_condDistrib hX hY hs ht']

中文:
定理 setL整数egral_condDistrib_of_measurableSet
  结论: (hX : 可测 X) (hY : 几乎处处可测 Y μ)
  证明: by
  obtain ⟨t', ht', rfl⟩ := ht
  rw [setLIntegral_preimage_condDistrib hX hY hs ht']

Depends on / 依赖: setLIntegral_preimage_condDistrib
-/
theorem setLIntegral_condDistrib_of_measurableSet (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hs : MeasurableSet s) {t : Set α} (ht : MeasurableSet[mβ.comap X] t) :
    ∫⁻ a in t, condDistrib Y X μ (X a) s ∂μ = μ (t inter Y ⁻¹' s) := by
  obtain ⟨t', ht', rfl⟩ := ht
  rw [setLIntegral_preimage_condDistrib hX hY hs ht']

/--
theorem `condDistrib_ae_eq_condExp` / 定理 `condDistrib_ae_eq_condExp`

English:
theorem condDistrib_ae_eq_condExp
  given: (hX : Measurable X) (hY : Measurable Y) (hs : MeasurableSet s)
  proof: by
  refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le ?_ ?_ ?_ ?_
  · exact (integrable_const _).indicator (hY hs)
  · exact fun t _ _ => (integrable_toReal_condDistrib hX.aemeasurable hs).integrableOn
  · intro t ht _
    simp_rw [measureReal_def]
    rw [integral_toReal ((measurable_condDistrib hs).mono hX.comap_le le_rfl).aemeasurable
      (Eventually.of_forall fun ω => measure_lt_top (condDistrib Y X μ (X ω)) _)]; rw [integral_indicator_const _ (hY hs)]; rw [measureReal_restrict_apply (hY hs)]; rw [smul_eq_mul]; rw [mul_one]; rw [inter_comm]; rw [setLIntegral_condDistrib_of_measurableSet hX hY.aemeasurable hs ht]; rw [measureReal_def]
  · exact (measurable_condDistrib hs).ennreal_toReal.aestronglyMeasurable

中文:
定理 condDistrib_ae_eq_condExp
  条件: (hX : 可测 X) (hY : 可测 Y) (hs : 可测集 s)
  证明: by
  refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le ?_ ?_ ?_ ?_
  · exact (integrable_const _).indicator (hY hs)
  · exact fun t _ _ => (integrable_toReal_condDistrib hX.aemeasurable hs).integrableOn
  · intro t ht _
    simp_rw [measureReal_def]
    rw [integral_toReal ((measurable_condDistrib hs).mono hX.comap_le le_rfl).aemeasurable
      (Eventually.of_forall fun ω => measure_lt_top (condDistrib Y X μ (X ω)) _)]; rw [integral_indicator_const _ (hY hs)]; rw [measureReal_restrict_apply (hY hs)]; rw [smul_eq_mul]; rw [mul_one]; rw [inter_comm]; rw [setLIntegral_condDistrib_of_measurableSet hX hY.aemeasurable hs ht]; rw [measureReal_def]
  · exact (measurable_condDistrib hs).ennreal_toReal.aestronglyMeasurable

Depends on / 依赖: Eventually, Eventually.of_forall, ae_eq_condExp_of_forall_setIntegral_eq, aemeasurable, comap_le, condDistrib, hX.aemeasurable, hX.comap_le, indicator, integrableOn, integrable_const, integrable_toReal_condDistrib, integral_indicator_const, integral_toReal, le_rfl, measurable_condDistrib, measureReal_def, measureReal_restrict_apply, measure_lt_top, of_forall
-/
theorem condDistrib_ae_eq_condExp (hX : Measurable X) (hY : Measurable Y) (hs : MeasurableSet s) :
    (fun a => (condDistrib Y X μ (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s | mβ.comap X⟧ := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le ?_ ?_ ?_ ?_
  · exact (integrable_const _).indicator (hY hs)
  · exact fun t _ _ => (integrable_toReal_condDistrib hX.aemeasurable hs).integrableOn
  · intro t ht _
    simp_rw [measureReal_def]
    rw [integral_toReal ((measurable_condDistrib hs).mono hX.comap_le le_rfl).aemeasurable
      (Eventually.of_forall fun ω => measure_lt_top (condDistrib Y X μ (X ω)) _)]; rw [integral_indicator_const _ (hY hs)]; rw [measureReal_restrict_apply (hY hs)]; rw [smul_eq_mul]; rw [mul_one]; rw [inter_comm]; rw [setLIntegral_condDistrib_of_measurableSet hX hY.aemeasurable hs ht]; rw [measureReal_def]
  · exact (measurable_condDistrib hs).ennreal_toReal.aestronglyMeasurable

/--
theorem `condExp_prod_ae_eq_integral_condDistrib'` / 定理 `condExp_prod_ae_eq_integral_condDistrib'`

English:
theorem condExp_prod_ae_eq_integral_condDistrib'
  statement: [NormedSpace Real F] [CompleteSpace F]
  proof: by
  have hf_int' : Integrable (fun a => f (X a, Y a)) μ :=
    (integrable_map_measure hf_int.1 (hX.aemeasurable.prodMk hY)).mp hf_int
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hf_int' (fun s _ _ => ?_) ?_ ?_).symm
  · exact (hf_int.integral_condDistrib hX.aemeasurable hY).integrableOn
  · rintro s ⟨t, ht, rfl⟩ _
    change ∫ a in X ⁻¹' t, ((fun x' => ∫ y, f (x', y) ∂(condDistrib Y X μ) x') ∘ X) a ∂μ =
      ∫ a in X ⁻¹' t, f (X a, Y a) ∂μ
    simp only [Function.comp_apply]
    rw [← integral_map hX.aemeasurable (f := fun x' => ∫ y]; rw [f (x']; rw [y) ∂(condDistrib Y X μ) x')]
    swap
    · rw [← Measure.restrict_map hX ht]
      exact (hf_int.1.integral_condDistrib_map hY).restrict
    rw [← Measure.restrict_map hX ht]; rw [← Measure.fst_map_prodMk₀ hY]; rw [condDistrib]; rw [Measure.setIntegral_condKernel_univ_right ht hf_int.integrableOn]; rw [setIntegral_map (ht.prod MeasurableSet.univ) hf_int.1 (hX.aemeasurable.prodMk hY)]; rw [mk_preimage_prod]; rw [preimage_univ]; rw [inter_univ]
  · exact aestronglyMeasurable_integral_condDistrib hX.aemeasurable hY hf_int.1

中文:
定理 condExp_prod_ae_eq_integral_condDistrib'
  结论: [赋范空间 实数 F] [完备空间 F]
  证明: by
  have hf_int' : Integrable (fun a => f (X a, Y a)) μ :=
    (integrable_map_measure hf_int.1 (hX.aemeasurable.prodMk hY)).mp hf_int
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hf_int' (fun s _ _ => ?_) ?_ ?_).symm
  · exact (hf_int.integral_condDistrib hX.aemeasurable hY).integrableOn
  · rintro s ⟨t, ht, rfl⟩ _
    change ∫ a in X ⁻¹' t, ((fun x' => ∫ y, f (x', y) ∂(condDistrib Y X μ) x') ∘ X) a ∂μ =
      ∫ a in X ⁻¹' t, f (X a, Y a) ∂μ
    simp only [Function.comp_apply]
    rw [← integral_map hX.aemeasurable (f := fun x' => ∫ y]; rw [f (x']; rw [y) ∂(condDistrib Y X μ) x')]
    swap
    · rw [← Measure.restrict_map hX ht]
      exact (hf_int.1.integral_condDistrib_map hY).restrict
    rw [← Measure.restrict_map hX ht]; rw [← Measure.fst_map_prodMk₀ hY]; rw [condDistrib]; rw [Measure.setIntegral_condKernel_univ_right ht hf_int.integrableOn]; rw [setIntegral_map (ht.prod MeasurableSet.univ) hf_int.1 (hX.aemeasurable.prodMk hY)]; rw [mk_preimage_prod]; rw [preimage_univ]; rw [inter_univ]
  · exact aestronglyMeasurable_integral_condDistrib hX.aemeasurable hY hf_int.1

Depends on / 依赖: Function, Function.comp_apply, Integrable, ae_eq_condExp_of_forall_setIntegral_eq, aemeasurable, comap_le, comp_apply, condDistrib, hX.aeme, hX.aemeasurable, hX.aemeasurable.prodMk, hX.comap_le, hf_int, hf_int.integral_condDistrib, integrableOn, integrable_map_measure, integral_condDistrib, integral_map, prodMk
-/
theorem condExp_prod_ae_eq_integral_condDistrib' [NormedSpace Real F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hf_int : Integrable f (μ.map fun a => (X a, Y a))) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ]
      fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) := by
  have hf_int' : Integrable (fun a => f (X a, Y a)) μ :=
    (integrable_map_measure hf_int.1 (hX.aemeasurable.prodMk hY)).mp hf_int
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hf_int' (fun s _ _ => ?_) ?_ ?_).symm
  · exact (hf_int.integral_condDistrib hX.aemeasurable hY).integrableOn
  · rintro s ⟨t, ht, rfl⟩ _
    change ∫ a in X ⁻¹' t, ((fun x' => ∫ y, f (x', y) ∂(condDistrib Y X μ) x') ∘ X) a ∂μ =
      ∫ a in X ⁻¹' t, f (X a, Y a) ∂μ
    simp only [Function.comp_apply]
    rw [← integral_map hX.aemeasurable (f := fun x' => ∫ y]; rw [f (x']; rw [y) ∂(condDistrib Y X μ) x')]
    swap
    · rw [← Measure.restrict_map hX ht]
      exact (hf_int.1.integral_condDistrib_map hY).restrict
    rw [← Measure.restrict_map hX ht]; rw [← Measure.fst_map_prodMk₀ hY]; rw [condDistrib]; rw [Measure.setIntegral_condKernel_univ_right ht hf_int.integrableOn]; rw [setIntegral_map (ht.prod MeasurableSet.univ) hf_int.1 (hX.aemeasurable.prodMk hY)]; rw [mk_preimage_prod]; rw [preimage_univ]; rw [inter_univ]
  · exact aestronglyMeasurable_integral_condDistrib hX.aemeasurable hY hf_int.1

/--
theorem `condExp_prod_ae_eq_integral_condDistrib₀` / 定理 `condExp_prod_ae_eq_integral_condDistrib₀`

English:
theorem condExp_prod_ae_eq_integral_condDistrib₀
  statement: [NormedSpace Real F] [CompleteSpace F]
  proof: have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf (hX.aemeasurable.prodMk hY)]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hf_int'

中文:
定理 condExp_prod_ae_eq_integral_condDistrib₀
  结论: [赋范空间 实数 F] [完备空间 F]
  证明: have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf (hX.aemeasurable.prodMk hY)]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hf_int'

Depends on / 依赖: Integrable, aemeasurable, condExp_prod_ae_eq_integral_condDistrib, hX.aemeasurable.prodMk, hf_int, integrable_map_measure, prodMk
-/
theorem condExp_prod_ae_eq_integral_condDistrib₀ [NormedSpace Real F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ)
    (hf : AEStronglyMeasurable f (μ.map fun a => (X a, Y a)))
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) :=
  have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf (hX.aemeasurable.prodMk hY)]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hf_int'

/--
theorem `condExp_prod_ae_eq_integral_condDistrib` / 定理 `condExp_prod_ae_eq_integral_condDistrib`

English:
theorem condExp_prod_ae_eq_integral_condDistrib
  statement: [NormedSpace Real F] [CompleteSpace F]
  proof: have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf.aestronglyMeasurable (hX.aemeasurable.prodMk hY)]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hf_int'

中文:
定理 condExp_prod_ae_eq_integral_condDistrib
  结论: [赋范空间 实数 F] [完备空间 F]
  证明: have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf.aestronglyMeasurable (hX.aemeasurable.prodMk hY)]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hf_int'

Depends on / 依赖: Integrable, aemeasurable, aestronglyMeasurable, condExp_prod_ae_eq_integral_condDistrib, hX.aemeasurable.prodMk, hf.aestronglyMeasurable, hf_int, integrable_map_measure, prodMk
-/
theorem condExp_prod_ae_eq_integral_condDistrib [NormedSpace Real F] [CompleteSpace F]
    (hX : Measurable X) (hY : AEMeasurable Y μ) (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (X a, Y a)) μ) :
    μ[fun a => f (X a, Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂condDistrib Y X μ (X a) :=
  have hf_int' : Integrable f (μ.map fun a => (X a, Y a)) := by
    rwa [integrable_map_measure hf.aestronglyMeasurable (hX.aemeasurable.prodMk hY)]
  condExp_prod_ae_eq_integral_condDistrib' hX hY hf_int'

/--
theorem `condExp_ae_eq_integral_condDistrib` / 定理 `condExp_ae_eq_integral_condDistrib`

English:
theorem condExp_ae_eq_integral_condDistrib
  statement: [NormedSpace Real F] [CompleteSpace F] (hX : Measurable X)
  proof: condExp_prod_ae_eq_integral_condDistrib hX hY (hf.comp_measurable measurable_snd) hf_int

中文:
定理 condExp_ae_eq_integral_condDistrib
  结论: [赋范空间 实数 F] [完备空间 F] (hX : 可测 X)
  证明: condExp_prod_ae_eq_integral_condDistrib hX hY (hf.comp_measurable measurable_snd) hf_int

Depends on / 依赖: comp_measurable, condExp_prod_ae_eq_integral_condDistrib, hf.comp_measurable, hf_int, measurable_snd
-/
theorem condExp_ae_eq_integral_condDistrib [NormedSpace Real F] [CompleteSpace F] (hX : Measurable X)
    (hY : AEMeasurable Y μ) {f : Ω -> F} (hf : StronglyMeasurable f)
    (hf_int : Integrable (fun a => f (Y a)) μ) :
    μ[fun a => f (Y a) | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib Y X μ (X a) :=
  condExp_prod_ae_eq_integral_condDistrib hX hY (hf.comp_measurable measurable_snd) hf_int

/--
theorem `condExp_ae_eq_integral_condDistrib'` / 定理 `condExp_ae_eq_integral_condDistrib'`

English:
theorem condExp_ae_eq_integral_condDistrib'
  statement: {Ω : Type*} [NormedAddCommGroup Ω] [NormedSpace Real Ω]
  proof: condExp_ae_eq_integral_condDistrib hX hY_int.1.aemeasurable stronglyMeasurable_id hY_int

中文:
定理 condExp_ae_eq_integral_condDistrib'
  结论: {Ω : 类型} [赋范交换加群 Ω] [赋范空间 实数 Ω]
  证明: condExp_ae_eq_integral_condDistrib hX hY_int.1.aemeasurable stronglyMeasurable_id hY_int

Depends on / 依赖: aemeasurable, condExp_ae_eq_integral_condDistrib, hY_int, stronglyMeasurable_id
-/
theorem condExp_ae_eq_integral_condDistrib' {Ω : Type*} [NormedAddCommGroup Ω] [NormedSpace Real Ω]
    [CompleteSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] {Y : α -> Ω}
    (hX : Measurable X) (hY_int : Integrable Y μ) :
    μ[Y | mβ.comap X] =ᵐ[μ] fun a => ∫ y, y ∂condDistrib Y X μ (X a) :=
  condExp_ae_eq_integral_condDistrib hX hY_int.1.aemeasurable stronglyMeasurable_id hY_int

open MeasureTheory

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prodMk` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prodMk`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prodMk
  statement: {Ω F} {mΩ : MeasurableSpace Ω}
  proof: by
  refine ⟨fun x => hf.mk f x.2, hf.stronglyMeasurable_mk.comp_measurable measurable_snd, ?_⟩
  suffices h : Measure.QuasiMeasurePreserving Prod.snd (μ.map fun ω => (X ω, ω)) μ from
    Measure.QuasiMeasurePreserving.ae_eq h hf.ae_eq_mk
  refine ⟨measurable_snd, Measure.AbsolutelyContinuous.mk fun s hs hμs => ?_⟩
  rw [Measure.map_apply measurable_snd hs]
  by_cases hX : AEMeasurable X μ
  · rw [Measure.map_apply_of_aemeasurable]
    · rw [← univ_prod, mk_preimage_prod, preimage_univ, univ_inter, preimage_id']
      exact hμs
    · exact hX.prodMk aemeasurable_id
    · exact measurable_snd hs
  · rw [Measure.map_of_not_aemeasurable]
    · simp
    · contrapose hX; exact measurable_fst.comp_aemeasurable hX

中文:
定理 _root_.测度论.AEStronglyMeasurable.comp_snd_map_prodMk
  结论: {Ω F} {mΩ : 可测空间 Ω}
  证明: by
  refine ⟨fun x => hf.mk f x.2, hf.stronglyMeasurable_mk.comp_measurable measurable_snd, ?_⟩
  suffices h : Measure.QuasiMeasurePreserving Prod.snd (μ.map fun ω => (X ω, ω)) μ from
    Measure.QuasiMeasurePreserving.ae_eq h hf.ae_eq_mk
  refine ⟨measurable_snd, Measure.AbsolutelyContinuous.mk fun s hs hμs => ?_⟩
  rw [Measure.map_apply measurable_snd hs]
  by_cases hX : AEMeasurable X μ
  · rw [Measure.map_apply_of_aemeasurable]
    · rw [← univ_prod, mk_preimage_prod, preimage_univ, univ_inter, preimage_id']
      exact hμs
    · exact hX.prodMk aemeasurable_id
    · exact measurable_snd hs
  · rw [Measure.map_of_not_aemeasurable]
    · simp
    · contrapose hX; exact measurable_fst.comp_aemeasurable hX

Depends on / 依赖: AEMeasurable, AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.mk, Measure.QuasiMeasurePreserving, Measure.QuasiMeasurePreserving.ae_eq, Measure.map_apply, Measure.map_apply_of_aemeasurable, Prod.snd, QuasiMeasurePreserving, ae_eq, ae_eq_mk, comp_measurable, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.comp_measurable, map_apply, map_apply_of_aemeasurable, measurable_snd, mk_preimage_prod
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prodMk {Ω F} {mΩ : MeasurableSpace Ω}
    (X : Ω -> β) {μ : Measure Ω} [TopologicalSpace F] {f : Ω -> F} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  refine ⟨fun x => hf.mk f x.2, hf.stronglyMeasurable_mk.comp_measurable measurable_snd, ?_⟩
  suffices h : Measure.QuasiMeasurePreserving Prod.snd (μ.map fun ω => (X ω, ω)) μ from
    Measure.QuasiMeasurePreserving.ae_eq h hf.ae_eq_mk
  refine ⟨measurable_snd, Measure.AbsolutelyContinuous.mk fun s hs hμs => ?_⟩
  rw [Measure.map_apply measurable_snd hs]
  by_cases hX : AEMeasurable X μ
  · rw [Measure.map_apply_of_aemeasurable]
    · rw [← univ_prod, mk_preimage_prod, preimage_univ, univ_inter, preimage_id']
      exact hμs
    · exact hX.prodMk aemeasurable_id
    · exact measurable_snd hs
  · rw [Measure.map_of_not_aemeasurable]
    · simp
    · contrapose hX; exact measurable_fst.comp_aemeasurable hX

/--
theorem `_root_.MeasureTheory.Integrable.comp_snd_map_prodMk` / 定理 `_root_.MeasureTheory.Integrable.comp_snd_map_prodMk`

English:
theorem _root_.MeasureTheory.Integrable.comp_snd_map_prodMk
  proof: by
  by_cases hX : AEMeasurable X μ
  · have hf := hf_int.1.comp_snd_map_prodMk X (mΩ := mΩ) (mβ := mβ)
    refine ⟨hf, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]; rw [lintegral_map' hf.enorm (hX.prodMk aemeasurable_id)]
    exact hf_int.2
  · rw [Measure.map_of_not_aemeasurable]
    · simp
    · contrapose hX; exact measurable_fst.comp_aemeasurable hX

中文:
定理 _root_.测度论.可积.comp_snd_map_prodMk
  证明: by
  by_cases hX : AEMeasurable X μ
  · have hf := hf_int.1.comp_snd_map_prodMk X (mΩ := mΩ) (mβ := mβ)
    refine ⟨hf, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]; rw [lintegral_map' hf.enorm (hX.prodMk aemeasurable_id)]
    exact hf_int.2
  · rw [Measure.map_of_not_aemeasurable]
    · simp
    · contrapose hX; exact measurable_fst.comp_aemeasurable hX

Depends on / 依赖: AEMeasurable, Measure, Measure.map_of_not_aemeasurable, aemeasurable_id, comp_aemeasurable, comp_snd_map_prodMk, contrapose, hX.prodMk, hasFiniteIntegral_iff_enorm, hf.enorm, hf_int, lintegral_map, map_of_not_aemeasurable, measurable_fst, measurable_fst.comp_aemeasurable, prodMk
-/
theorem _root_.MeasureTheory.Integrable.comp_snd_map_prodMk
    {Ω} {mΩ : MeasurableSpace Ω} (X : Ω -> β) {μ : Measure Ω} {f : Ω -> F} (hf_int : Integrable f μ) :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) := by
  by_cases hX : AEMeasurable X μ
  · have hf := hf_int.1.comp_snd_map_prodMk X (mΩ := mΩ) (mβ := mβ)
    refine ⟨hf, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]; rw [lintegral_map' hf.enorm (hX.prodMk aemeasurable_id)]
    exact hf_int.2
  · rw [Measure.map_of_not_aemeasurable]
    · simp
    · contrapose hX; exact measurable_fst.comp_aemeasurable hX

/--
theorem `aestronglyMeasurable_comp_snd_map_prodMk_iff` / 定理 `aestronglyMeasurable_comp_snd_map_prodMk_iff`

English:
theorem aestronglyMeasurable_comp_snd_map_prodMk_iff
  statement: {Ω F} {_ : MeasurableSpace Ω}
  proof: ⟨fun h => h.comp_measurable (hX.prodMk measurable_id), fun h => h.comp_snd_map_prodMk X⟩

中文:
定理 aestronglyMeasurable_comp_snd_map_prodMk_iff
  结论: {Ω F} {_ : 可测空间 Ω}
  证明: ⟨fun h => h.comp_measurable (hX.prodMk measurable_id), fun h => h.comp_snd_map_prodMk X⟩

Depends on / 依赖: comp_measurable, comp_snd_map_prodMk, h.comp_measurable, h.comp_snd_map_prodMk, hX.prodMk, measurable_id, prodMk
-/
theorem aestronglyMeasurable_comp_snd_map_prodMk_iff {Ω F} {_ : MeasurableSpace Ω}
    [TopologicalSpace F] {X : Ω -> β} {μ : Measure Ω} (hX : Measurable X) {f : Ω -> F} :
    AEStronglyMeasurable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔
      AEStronglyMeasurable f μ :=
  ⟨fun h => h.comp_measurable (hX.prodMk measurable_id), fun h => h.comp_snd_map_prodMk X⟩

/--
theorem `integrable_comp_snd_map_prodMk_iff` / 定理 `integrable_comp_snd_map_prodMk_iff`

English:
theorem integrable_comp_snd_map_prodMk_iff
  statement: {Ω} {_ : MeasurableSpace Ω} {X : Ω -> β} {μ : Measure Ω}
  proof: ⟨fun h => h.comp_measurable (hX.prodMk measurable_id), fun h => h.comp_snd_map_prodMk X⟩

中文:
定理 integrable_comp_snd_map_prodMk_iff
  结论: {Ω} {_ : 可测空间 Ω} {X : Ω -> β} {μ : 测度 Ω}
  证明: ⟨fun h => h.comp_measurable (hX.prodMk measurable_id), fun h => h.comp_snd_map_prodMk X⟩

Depends on / 依赖: comp_measurable, comp_snd_map_prodMk, h.comp_measurable, h.comp_snd_map_prodMk, hX.prodMk, measurable_id, prodMk
-/
theorem integrable_comp_snd_map_prodMk_iff {Ω} {_ : MeasurableSpace Ω} {X : Ω -> β} {μ : Measure Ω}
    (hX : Measurable X) {f : Ω -> F} :
    Integrable (fun x : β × Ω => f x.2) (μ.map fun ω => (X ω, ω)) ↔ Integrable f μ :=
  ⟨fun h => h.comp_measurable (hX.prodMk measurable_id), fun h => h.comp_snd_map_prodMk X⟩

/--
theorem `condExp_ae_eq_integral_condDistrib_id` / 定理 `condExp_ae_eq_integral_condDistrib_id`

English:
theorem condExp_ae_eq_integral_condDistrib_id
  statement: [NormedSpace Real F] [CompleteSpace F] {X : Ω -> β}
  proof: condExp_prod_ae_eq_integral_condDistrib' hX aemeasurable_id (hf_int.comp_snd_map_prodMk X)

中文:
定理 condExp_ae_eq_integral_condDistrib_id
  结论: [赋范空间 实数 F] [完备空间 F] {X : Ω -> β}
  证明: condExp_prod_ae_eq_integral_condDistrib' hX aemeasurable_id (hf_int.comp_snd_map_prodMk X)

Depends on / 依赖: aemeasurable_id, comp_snd_map_prodMk, condExp_prod_ae_eq_integral_condDistrib, hf_int, hf_int.comp_snd_map_prodMk
-/
theorem condExp_ae_eq_integral_condDistrib_id [NormedSpace Real F] [CompleteSpace F] {X : Ω -> β}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hX : Measurable X) {f : Ω -> F} (hf_int : Integrable f μ) :
    μ[f | mβ.comap X] =ᵐ[μ] fun a => ∫ y, f y ∂condDistrib id X μ (X a) :=
  condExp_prod_ae_eq_integral_condDistrib' hX aemeasurable_id (hf_int.comp_snd_map_prodMk X)

end ProbabilityTheory
