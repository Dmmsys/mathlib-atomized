/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integration with respect to the product measure

In this file we prove Fubini's theorem.

## Main results

* `MeasureTheory.integrable_prod_iff` states that a binary function is integrable iff both
  * `y ↦ f (x, y)` is integrable for almost every `x`, and
  * the function `x ↦ ∫ ‖f (x, y)‖ dy` is integrable.
* `MeasureTheory.integral_prod`: Fubini's theorem. It states that for an integrable function
  `α × β → E` (where `E` is a second countable Banach space) we have
  `∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ`. This theorem has the same variants as
  Tonelli's theorem (see `MeasureTheory.lintegral_prod`). The lemma
  `MeasureTheory.Integrable.integral_prod_right` states that the inner integral of the right-hand
  side is integrable.
* `MeasureTheory.integral_integral_swap_of_hasCompactSupport`: a version of Fubini's theorem for
  continuous functions with compact support, which does not assume that the measures are σ-finite
  contrary to all the usual versions of Fubini.

## Tags

product measure, Fubini's theorem, Fubini-Tonelli theorem
-/

public section

noncomputable section

open scoped Topology ENNReal MeasureTheory

open Set Function Real ENNReal

open MeasureTheory MeasurableSpace MeasureTheory.Measure

open TopologicalSpace

open Filter hiding prod_eq map

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
variable [NormedAddCommGroup E]

/-! ### Measurability

Before we define the product measure, we can talk about the measurability of operations on binary
functions. We show that if `f` is a binary measurable function, then the function that integrates
along one of the variables (using either the Lebesgue or Bochner integral) is measurable.
-/

section

variable [NormedSpace Real E]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `MeasureTheory.StronglyMeasurable.integral_prod_right` / 定理 `MeasureTheory.StronglyMeasurable.integral_prod_right`

English:
theorem MeasureTheory.StronglyMeasurable.integral_prod_right
  given: [SFinite ν] ⦃f
  statement: α -> β -> E⦄
  proof: by
  simp only [integral_eq_setToFun]
  apply StronglyMeasurable.setToFun_prod_right _ (fun s hs => ?_) hf
  refine (Measurable.ennreal_toReal ?_).stronglyMeasurable.smul_const _
  exact measurable_measure_prodMk_left hs

中文:
定理 测度论.StronglyMeasurable.integral_prod_right
  条件: [SFinite ν] ⦃f
  结论: α -> β -> E⦄
  证明: by
  simp only [integral_eq_setToFun]
  apply StronglyMeasurable.setToFun_prod_right _ (fun s hs => ?_) hf
  refine (Measurable.ennreal_toReal ?_).stronglyMeasurable.smul_const _
  exact measurable_measure_prodMk_left hs

Depends on / 依赖: Measurable, Measurable.ennreal_toReal, StronglyMeasurable, StronglyMeasurable.setToFun_prod_right, ennreal_toReal, integral_eq_setToFun, measurable_measure_prodMk_left, setToFun_prod_right, smul_const, stronglyMeasurable, stronglyMeasurable.smul_const
-/
theorem MeasureTheory.StronglyMeasurable.integral_prod_right [SFinite ν] ⦃f : α -> β -> E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun x => ∫ y, f x y ∂ν := by
  simp only [integral_eq_setToFun]
  apply StronglyMeasurable.setToFun_prod_right _ (fun s hs => ?_) hf
  refine (Measurable.ennreal_toReal ?_).stronglyMeasurable.smul_const _
  exact measurable_measure_prodMk_left hs

/--
theorem `MeasureTheory.StronglyMeasurable.integral_prod_right'` / 定理 `MeasureTheory.StronglyMeasurable.integral_prod_right'`

English:
theorem MeasureTheory.StronglyMeasurable.integral_prod_right'
  given: [SFinite ν] ⦃f
  statement: α × β -> E⦄
  proof: by
  rw [← uncurry_curry f] at hf; exact hf.integral_prod_right

中文:
定理 测度论.StronglyMeasurable.integral_prod_right'
  条件: [SFinite ν] ⦃f
  结论: α × β -> E⦄
  证明: by
  rw [← uncurry_curry f] at hf; exact hf.integral_prod_right

Depends on / 依赖: hf.integral_prod_right, integral_prod_right, uncurry_curry
-/
theorem MeasureTheory.StronglyMeasurable.integral_prod_right' [SFinite ν] ⦃f : α × β -> E⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ∫ y, f (x, y) ∂ν := by
  rw [← uncurry_curry f] at hf; exact hf.integral_prod_right

/--
theorem `MeasureTheory.StronglyMeasurable.integral_prod_left` / 定理 `MeasureTheory.StronglyMeasurable.integral_prod_left`

English:
theorem MeasureTheory.StronglyMeasurable.integral_prod_left
  given: [SFinite μ] ⦃f
  statement: α -> β -> E⦄
  proof: (hf.comp_measurable measurable_swap).integral_prod_right'

中文:
定理 测度论.StronglyMeasurable.integral_prod_left
  条件: [SFinite μ] ⦃f
  结论: α -> β -> E⦄
  证明: (hf.comp_measurable measurable_swap).integral_prod_right'

Depends on / 依赖: comp_measurable, hf.comp_measurable, integral_prod_right, measurable_swap
-/
theorem MeasureTheory.StronglyMeasurable.integral_prod_left [SFinite μ] ⦃f : α -> β -> E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun y => ∫ x, f x y ∂μ :=
  (hf.comp_measurable measurable_swap).integral_prod_right'

/--
theorem `MeasureTheory.StronglyMeasurable.integral_prod_left'` / 定理 `MeasureTheory.StronglyMeasurable.integral_prod_left'`

English:
theorem MeasureTheory.StronglyMeasurable.integral_prod_left'
  given: [SFinite μ] ⦃f
  statement: α × β -> E⦄
  proof: (hf.comp_measurable measurable_swap).integral_prod_right'

中文:
定理 测度论.StronglyMeasurable.integral_prod_left'
  条件: [SFinite μ] ⦃f
  结论: α × β -> E⦄
  证明: (hf.comp_measurable measurable_swap).integral_prod_right'

Depends on / 依赖: comp_measurable, hf.comp_measurable, integral_prod_right, measurable_swap
-/
theorem MeasureTheory.StronglyMeasurable.integral_prod_left' [SFinite μ] ⦃f : α × β -> E⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun y => ∫ x, f (x, y) ∂μ :=
  (hf.comp_measurable measurable_swap).integral_prod_right'

end

/-! ### The product measure -/


namespace MeasureTheory

namespace Measure

variable [SFinite ν]

/--
theorem `integrable_measure_prodMk_left` / 定理 `integrable_measure_prodMk_left`

English:
theorem integrable_measure_prodMk_left
  statement: {s : Set (α × β)} (hs : MeasurableSet s)
  proof: by
  refine ⟨(measurable_measure_prodMk_left hs).ennreal_toReal.aemeasurable.aestronglyMeasurable, ?_⟩
  simp_rw [hasFiniteIntegral_iff_enorm, measureReal_def, enorm_eq_ofReal toReal_nonneg]
  convert! h2s.lt_top using 1
  rw [prod_apply hs]
  apply lintegral_congr_ae
  filter_upwards [ae_measure_lt_top hs h2s] with x hx
  rw [lt_top_iff_ne_top] at hx
  simp [ofReal_toReal, hx]

中文:
定理 integrable_measure_prodMk_left
  结论: {s : 集合 (α × β)} (hs : 可测集 s)
  证明: by
  refine ⟨(measurable_measure_prodMk_left hs).ennreal_toReal.aemeasurable.aestronglyMeasurable, ?_⟩
  simp_rw [hasFiniteIntegral_iff_enorm, measureReal_def, enorm_eq_ofReal toReal_nonneg]
  convert! h2s.lt_top using 1
  rw [prod_apply hs]
  apply lintegral_congr_ae
  filter_upwards [ae_measure_lt_top hs h2s] with x hx
  rw [lt_top_iff_ne_top] at hx
  simp [ofReal_toReal, hx]

Depends on / 依赖: ae_measure_lt_top, aemeasurable, aestronglyMeasurable, convert, ennreal_toReal, ennreal_toReal.aemeasurable.aestronglyMeasurable, enorm_eq_ofReal, filter_upwards, h2s.lt_top, hasFiniteIntegral_iff_enorm, lintegral_congr_ae, lt_top, lt_top_iff_ne_top, measurable_measure_prodMk_left, measureReal_def, ofReal_toReal, prod_apply, simp_rw, toReal_nonneg
-/
theorem integrable_measure_prodMk_left {s : Set (α × β)} (hs : MeasurableSet s)
    (h2s : (μ.prod ν) s != ∞) : Integrable (fun x => ν.real (Prod.mk x ⁻¹' s)) μ := by
  refine ⟨(measurable_measure_prodMk_left hs).ennreal_toReal.aemeasurable.aestronglyMeasurable, ?_⟩
  simp_rw [hasFiniteIntegral_iff_enorm, measureReal_def, enorm_eq_ofReal toReal_nonneg]
  convert! h2s.lt_top using 1
  rw [prod_apply hs]
  apply lintegral_congr_ae
  filter_upwards [ae_measure_lt_top hs h2s] with x hx
  rw [lt_top_iff_ne_top] at hx
  simp [ofReal_toReal, hx]

end Measure

end MeasureTheory

open MeasureTheory.Measure

section

variable {X : Type*} [TopologicalSpace X]

/--
theorem `MeasureTheory.AEStronglyMeasurable.prod_swap` / 定理 `MeasureTheory.AEStronglyMeasurable.prod_swap`

English:
theorem MeasureTheory.AEStronglyMeasurable.prod_swap
  statement: [SFinite μ] [SFinite ν]
  proof: by
  rw [← prod_swap] at hf
  exact hf.comp_measurable measurable_swap

中文:
定理 测度论.AEStronglyMeasurable.prod_swap
  结论: [SFinite μ] [SFinite ν]
  证明: by
  rw [← prod_swap] at hf
  exact hf.comp_measurable measurable_swap
-/
protected theorem MeasureTheory.AEStronglyMeasurable.prod_swap [SFinite μ] [SFinite ν]
    {f : β × α -> X} (hf : AEStronglyMeasurable f (ν.prod μ)) :
    AEStronglyMeasurable (fun z : α × β => f z.swap) (μ.prod ν) := by
  rw [← prod_swap] at hf
  exact hf.comp_measurable measurable_swap

/--
theorem `MeasureTheory.AEStronglyMeasurable.comp_fst` / 定理 `MeasureTheory.AEStronglyMeasurable.comp_fst`

English:
theorem MeasureTheory.AEStronglyMeasurable.comp_fst
  statement: {γ} [TopologicalSpace γ] {f : α -> γ}
  proof: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

中文:
定理 测度论.AEStronglyMeasurable.comp_fst
  结论: {γ} [拓扑空间 γ] {f : α -> γ}
  证明: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

Depends on / 依赖: comp_quasiMeasurePreserving, hf.comp_quasiMeasurePreserving, quasiMeasurePreserving_fst
-/
theorem MeasureTheory.AEStronglyMeasurable.comp_fst {γ} [TopologicalSpace γ] {f : α -> γ}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun z : α × β => f z.1) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst

/--
theorem `MeasureTheory.AEStronglyMeasurable.comp_snd` / 定理 `MeasureTheory.AEStronglyMeasurable.comp_snd`

English:
theorem MeasureTheory.AEStronglyMeasurable.comp_snd
  statement: {γ} [TopologicalSpace γ] {f : β -> γ}
  proof: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

中文:
定理 测度论.AEStronglyMeasurable.comp_snd
  结论: {γ} [拓扑空间 γ] {f : β -> γ}
  证明: hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

Depends on / 依赖: comp_quasiMeasurePreserving, hf.comp_quasiMeasurePreserving, quasiMeasurePreserving_snd
-/
theorem MeasureTheory.AEStronglyMeasurable.comp_snd {γ} [TopologicalSpace γ] {f : β -> γ}
    (hf : AEStronglyMeasurable f ν) : AEStronglyMeasurable (fun z : α × β => f z.2) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd

/--
theorem `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` / 定理 `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`

English:
theorem MeasureTheory.AEStronglyMeasurable.integral_prod_right'
  statement: [SFinite ν] [NormedSpace Real E]
  proof: ⟨fun x => ∫ y, hf.mk f (x, y) ∂ν, hf.stronglyMeasurable_mk.integral_prod_right', by
    filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

中文:
定理 测度论.AEStronglyMeasurable.integral_prod_right'
  结论: [SFinite ν] [赋范空间 实数 E]
  证明: ⟨fun x => ∫ y, hf.mk f (x, y) ∂ν, hf.stronglyMeasurable_mk.integral_prod_right', by
    filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

Depends on / 依赖: ae_ae_of_ae_prod, ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.integral_prod_right, integral_congr_ae, integral_prod_right, stronglyMeasurable_mk
-/
theorem MeasureTheory.AEStronglyMeasurable.integral_prod_right' [SFinite ν] [NormedSpace Real E]
    ⦃f : α × β -> E⦄ (hf : AEStronglyMeasurable f (μ.prod ν)) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) μ :=
  ⟨fun x => ∫ y, hf.mk f (x, y) ∂ν, hf.stronglyMeasurable_mk.integral_prod_right', by
    filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

/--
theorem `MeasureTheory.AEStronglyMeasurable.prodMk_left` / 定理 `MeasureTheory.AEStronglyMeasurable.prodMk_left`

English:
theorem MeasureTheory.AEStronglyMeasurable.prodMk_left
  statement: [SFinite ν] {f : α × β -> X}
  proof: by
  filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with x hx
  exact ⟨fun y => hf.mk f (x, y),
    hf.stronglyMeasurable_mk.comp_measurable measurable_prodMk_left, hx⟩

中文:
定理 测度论.AEStronglyMeasurable.prodMk_left
  结论: [SFinite ν] {f : α × β -> X}
  证明: by
  filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with x hx
  exact ⟨fun y => hf.mk f (x, y),
    hf.stronglyMeasurable_mk.comp_measurable measurable_prodMk_left, hx⟩

Depends on / 依赖: ae_ae_of_ae_prod, ae_eq_mk, comp_measurable, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.comp_measurable, measurable_prodMk_left, stronglyMeasurable_mk
-/
theorem MeasureTheory.AEStronglyMeasurable.prodMk_left [SFinite ν] {f : α × β -> X}
    (hf : AEStronglyMeasurable f (μ.prod ν)) :
    forallᵐ x ∂μ, AEStronglyMeasurable (fun y => f (x, y)) ν := by
  filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with x hx
  exact ⟨fun y => hf.mk f (x, y),
    hf.stronglyMeasurable_mk.comp_measurable measurable_prodMk_left, hx⟩

/--
theorem `MeasureTheory.AEStronglyMeasurable.prodMk_right` / 定理 `MeasureTheory.AEStronglyMeasurable.prodMk_right`

English:
theorem MeasureTheory.AEStronglyMeasurable.prodMk_right
  statement: [SFinite μ] [SFinite ν] {f : α × β -> X}
  proof: hf.prod_swap.prodMk_left

中文:
定理 测度论.AEStronglyMeasurable.prodMk_right
  结论: [SFinite μ] [SFinite ν] {f : α × β -> X}
  证明: hf.prod_swap.prodMk_left

Depends on / 依赖: hf.prod_swap.prodMk_left, prodMk_left, prod_swap
-/
theorem MeasureTheory.AEStronglyMeasurable.prodMk_right [SFinite μ] [SFinite ν] {f : α × β -> X}
    (hf : AEStronglyMeasurable f (μ.prod ν)) :
    forallᵐ y ∂ν, AEStronglyMeasurable (fun x => f (x, y)) μ :=
  hf.prod_swap.prodMk_left

/--
theorem `MeasureTheory.AEStronglyMeasurable.of_comp_snd` / 定理 `MeasureTheory.AEStronglyMeasurable.of_comp_snd`

English:
theorem MeasureTheory.AEStronglyMeasurable.of_comp_snd
  statement: {f : β -> X} [SFinite ν]
  proof: by
  have := NeZero.mk hμ
  obtain ⟨y, hy⟩ := hf.prodMk_left.exists
  exact hy

中文:
定理 测度论.AEStronglyMeasurable.of_comp_snd
  结论: {f : β -> X} [SFinite ν]
  证明: by
  have := NeZero.mk hμ
  obtain ⟨y, hy⟩ := hf.prodMk_left.exists
  exact hy
-/
protected theorem MeasureTheory.AEStronglyMeasurable.of_comp_snd {f : β -> X} [SFinite ν]
    (hf : AEStronglyMeasurable (f ·.2) (μ.prod ν)) (hμ : μ != 0) : AEStronglyMeasurable f ν := by
  have := NeZero.mk hμ
  obtain ⟨y, hy⟩ := hf.prodMk_left.exists
  exact hy

/--
theorem `MeasureTheory.AEStronglyMeasurable.of_comp_fst` / 定理 `MeasureTheory.AEStronglyMeasurable.of_comp_fst`

English:
theorem MeasureTheory.AEStronglyMeasurable.of_comp_fst
  statement: {f : α -> X} [SFinite μ] [SFinite ν]
  proof: hf.prod_swap.of_comp_snd hν

中文:
定理 测度论.AEStronglyMeasurable.of_comp_fst
  结论: {f : α -> X} [SFinite μ] [SFinite ν]
  证明: hf.prod_swap.of_comp_snd hν
-/
protected theorem MeasureTheory.AEStronglyMeasurable.of_comp_fst {f : α -> X} [SFinite μ] [SFinite ν]
    (hf : AEStronglyMeasurable (f ·.1) (μ.prod ν)) (hν : ν != 0) : AEStronglyMeasurable f μ :=
  hf.prod_swap.of_comp_snd hν

/--
theorem `MeasureTheory.AEStronglyMeasurable.comp_fst_iff` / 定理 `MeasureTheory.AEStronglyMeasurable.comp_fst_iff`

English:
theorem MeasureTheory.AEStronglyMeasurable.comp_fst_iff
  statement: [SFinite μ] [SFinite ν] {f : α -> X}
  proof: ⟨(.of_comp_fst · hν), .comp_fst⟩

中文:
定理 测度论.AEStronglyMeasurable.comp_fst_iff
  结论: [SFinite μ] [SFinite ν] {f : α -> X}
  证明: ⟨(.of_comp_fst · hν), .comp_fst⟩

Depends on / 依赖: comp_fst, of_comp_fst
-/
theorem MeasureTheory.AEStronglyMeasurable.comp_fst_iff [SFinite μ] [SFinite ν] {f : α -> X}
    (hν : ν != 0) : AEStronglyMeasurable (f ·.1) (μ.prod ν) ↔ AEStronglyMeasurable f μ :=
  ⟨(.of_comp_fst · hν), .comp_fst⟩

/--
theorem `MeasureTheory.AEStronglyMeasurable.comp_snd_iff` / 定理 `MeasureTheory.AEStronglyMeasurable.comp_snd_iff`

English:
theorem MeasureTheory.AEStronglyMeasurable.comp_snd_iff
  statement: [SFinite ν] {f : β -> X}
  proof: ⟨(.of_comp_snd · hμ), .comp_snd⟩

中文:
定理 测度论.AEStronglyMeasurable.comp_snd_iff
  结论: [SFinite ν] {f : β -> X}
  证明: ⟨(.of_comp_snd · hμ), .comp_snd⟩

Depends on / 依赖: comp_snd, of_comp_snd
-/
theorem MeasureTheory.AEStronglyMeasurable.comp_snd_iff [SFinite ν] {f : β -> X}
    (hμ : μ != 0) : AEStronglyMeasurable (f ·.2) (μ.prod ν) ↔ AEStronglyMeasurable f ν :=
  ⟨(.of_comp_snd · hμ), .comp_snd⟩

end

namespace MeasureTheory

variable [SFinite ν]

/-! ### Integrability on a product -/

section

/--
theorem `integrable_swap_iff` / 定理 `integrable_swap_iff`

English:
theorem integrable_swap_iff
  given: [SFinite μ] {f : α × β -> E}
  proof: measurePreserving_swap.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding

中文:
定理 integrable_swap_iff
  条件: [SFinite μ] {f : α × β -> E}
  证明: measurePreserving_swap.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.prodComm.measurableEmbedding, integrable_comp_emb, measurableEmbedding, measurePreserving_swap, measurePreserving_swap.integrable_comp_emb, prodComm
-/
theorem integrable_swap_iff [SFinite μ] {f : α × β -> E} :
    Integrable (f ∘ Prod.swap) (ν.prod μ) ↔ Integrable f (μ.prod ν) :=
  measurePreserving_swap.integrable_comp_emb MeasurableEquiv.prodComm.measurableEmbedding

/--
theorem `Integrable.swap` / 定理 `Integrable.swap`

English:
theorem Integrable.swap
  given: [SFinite μ] ⦃f
  statement: α × β -> E⦄ (hf : Integrable f (μ.prod ν)) :
  proof: integrable_swap_iff.2 hf

中文:
定理 可积.swap
  条件: [SFinite μ] ⦃f
  结论: α × β -> E⦄ (hf : 可积 f (μ.乘积 ν)) :
  证明: integrable_swap_iff.2 hf

Depends on / 依赖: integrable_swap_iff
-/
theorem Integrable.swap [SFinite μ] ⦃f : α × β -> E⦄ (hf : Integrable f (μ.prod ν)) :
    Integrable (f ∘ Prod.swap) (ν.prod μ) :=
  integrable_swap_iff.2 hf

/--
theorem `hasFiniteIntegral_prod_iff` / 定理 `hasFiniteIntegral_prod_iff`

English:
theorem hasFiniteIntegral_prod_iff
  given: ⦃f
  statement: α × β -> E⦄ (h1f : StronglyMeasurable f) :
  proof: by
  simp only [hasFiniteIntegral_iff_enorm, lintegral_prod _ h1f.enorm.aemeasurable]
  have (x : _) : forallᵐ y ∂ν, 0 <= ‖f (x, y)‖ := by filter_upwards with y using norm_nonneg _
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
      (h1f.norm.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
    enorm_eq_ofReal toReal_nonneg, ofReal_norm]
  -- this fact is probably too specialized to be its own lemma
  have : forall {p q r : Prop} (_ : r -> p), (r ↔ p ∧ q) ↔ p -> (r ↔ q) := fun {p q r} h1 => by
    rw [← and_congr_right_iff]; rw [and_iff_right_of_imp h1]
  rw [this]
  · intro h2f; rw [lintegral_congr_ae]
    filter_upwards [h2f] with x hx
    rw [ofReal_toReal]; rw [← lt_top_iff_ne_top]; exact hx
  · intro h2f; refine ae_lt_top ?_ h2f.ne; exact h1f.enorm.lintegral_prod_right'

中文:
定理 hasFinite整数egral_prod_iff
  条件: ⦃f
  结论: α × β -> E⦄ (h1f : StronglyMeasurable f) :
  证明: by
  simp only [hasFiniteIntegral_iff_enorm, lintegral_prod _ h1f.enorm.aemeasurable]
  have (x : _) : forallᵐ y ∂ν, 0 <= ‖f (x, y)‖ := by filter_upwards with y using norm_nonneg _
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
      (h1f.norm.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
    enorm_eq_ofReal toReal_nonneg, ofReal_norm]
  -- this fact is probably too specialized to be its own lemma
  have : forall {p q r : Prop} (_ : r -> p), (r ↔ p ∧ q) ↔ p -> (r ↔ q) := fun {p q r} h1 => by
    rw [← and_congr_right_iff]; rw [and_iff_right_of_imp h1]
  rw [this]
  · intro h2f; rw [lintegral_congr_ae]
    filter_upwards [h2f] with x hx
    rw [ofReal_toReal]; rw [← lt_top_iff_ne_top]; exact hx
  · intro h2f; refine ae_lt_top ?_ h2f.ne; exact h1f.enorm.lintegral_prod_right'

Depends on / 依赖: aemeasurable, aestronglyMeasurable, comp_measurable, enorm_eq_ofReal, filter_upwards, h1f.enorm.aemeasurable, h1f.norm.comp_measurable, hasFiniteIntegral_iff_enorm, integral_eq_lintegral_of_nonneg_ae, lintegral_prod, measurable_prodMk_left, norm_nonneg, ofReal_norm, simp_rw, toReal_nonneg
-/
theorem hasFiniteIntegral_prod_iff ⦃f : α × β -> E⦄ (h1f : StronglyMeasurable f) :
    HasFiniteIntegral f (μ.prod ν) ↔
      (forallᵐ x ∂μ, HasFiniteIntegral (fun y => f (x, y)) ν) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  simp only [hasFiniteIntegral_iff_enorm, lintegral_prod _ h1f.enorm.aemeasurable]
  have (x : _) : forallᵐ y ∂ν, 0 <= ‖f (x, y)‖ := by filter_upwards with y using norm_nonneg _
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
      (h1f.norm.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
    enorm_eq_ofReal toReal_nonneg, ofReal_norm]
  -- this fact is probably too specialized to be its own lemma
  have : forall {p q r : Prop} (_ : r -> p), (r ↔ p ∧ q) ↔ p -> (r ↔ q) := fun {p q r} h1 => by
    rw [← and_congr_right_iff]; rw [and_iff_right_of_imp h1]
  rw [this]
  · intro h2f; rw [lintegral_congr_ae]
    filter_upwards [h2f] with x hx
    rw [ofReal_toReal]; rw [← lt_top_iff_ne_top]; exact hx
  · intro h2f; refine ae_lt_top ?_ h2f.ne; exact h1f.enorm.lintegral_prod_right'

/--
theorem `hasFiniteIntegral_prod_iff'` / 定理 `hasFiniteIntegral_prod_iff'`

English:
theorem hasFiniteIntegral_prod_iff'
  given: ⦃f
  statement: α × β -> E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) :
  proof: by
  rw [hasFiniteIntegral_congr h1f.ae_eq_mk]; rw [hasFiniteIntegral_prod_iff h1f.stronglyMeasurable_mk]
  apply and_congr
  · apply eventually_congr
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm]
    intro x hx
    exact hasFiniteIntegral_congr hx
  · apply hasFiniteIntegral_congr
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm] with _ hx using
      integral_congr_ae (EventuallyEq.fun_comp hx _)

中文:
定理 hasFinite整数egral_prod_iff'
  条件: ⦃f
  结论: α × β -> E⦄ (h1f : AEStronglyMeasurable f (μ.乘积 ν)) :
  证明: by
  rw [hasFiniteIntegral_congr h1f.ae_eq_mk]; rw [hasFiniteIntegral_prod_iff h1f.stronglyMeasurable_mk]
  apply and_congr
  · apply eventually_congr
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm]
    intro x hx
    exact hasFiniteIntegral_congr hx
  · apply hasFiniteIntegral_congr
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm] with _ hx using
      integral_congr_ae (EventuallyEq.fun_comp hx _)

Depends on / 依赖: EventuallyEq, EventuallyEq.fun_comp, ae_ae_of_ae_prod, ae_eq_mk, and_congr, eventually_congr, filter_upwards, fun_comp, h1f.ae_eq_mk, h1f.ae_eq_mk.symm, h1f.stronglyMeasurable_mk, hasFiniteIntegral_congr, hasFiniteIntegral_prod_iff, integral_congr_ae, stronglyMeasurable_mk
-/
theorem hasFiniteIntegral_prod_iff' ⦃f : α × β -> E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) :
    HasFiniteIntegral f (μ.prod ν) ↔
      (forallᵐ x ∂μ, HasFiniteIntegral (fun y => f (x, y)) ν) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  rw [hasFiniteIntegral_congr h1f.ae_eq_mk]; rw [hasFiniteIntegral_prod_iff h1f.stronglyMeasurable_mk]
  apply and_congr
  · apply eventually_congr
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm]
    intro x hx
    exact hasFiniteIntegral_congr hx
  · apply hasFiniteIntegral_congr
    filter_upwards [ae_ae_of_ae_prod h1f.ae_eq_mk.symm] with _ hx using
      integral_congr_ae (EventuallyEq.fun_comp hx _)

/--
theorem `integrable_prod_iff` / 定理 `integrable_prod_iff`

English:
theorem integrable_prod_iff
  given: ⦃f
  statement: α × β -> E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) :
  proof: by
  simp [Integrable, h1f, hasFiniteIntegral_prod_iff', h1f.norm.integral_prod_right',
    h1f.prodMk_left]

中文:
定理 integrable_prod_iff
  条件: ⦃f
  结论: α × β -> E⦄ (h1f : AEStronglyMeasurable f (μ.乘积 ν)) :
  证明: by
  simp [Integrable, h1f, hasFiniteIntegral_prod_iff', h1f.norm.integral_prod_right',
    h1f.prodMk_left]

Depends on / 依赖: Integrable, h1f.norm.integral_prod_right, h1f.prodMk_left, hasFiniteIntegral_prod_iff, integral_prod_right, prodMk_left
-/
theorem integrable_prod_iff ⦃f : α × β -> E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) :
    Integrable f (μ.prod ν) ↔
      (forallᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧ Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ := by
  simp [Integrable, h1f, hasFiniteIntegral_prod_iff', h1f.norm.integral_prod_right',
    h1f.prodMk_left]

/--
theorem `integrable_prod_iff'` / 定理 `integrable_prod_iff'`

English:
theorem integrable_prod_iff'
  given: [SFinite μ] ⦃f
  statement: α × β -> E⦄
  proof: by
  convert! integrable_prod_iff h1f.prod_swap using 1
  rw [funext fun _ => Function.comp_apply.symm]; rw [integrable_swap_iff]

中文:
定理 integrable_prod_iff'
  条件: [SFinite μ] ⦃f
  结论: α × β -> E⦄
  证明: by
  convert! integrable_prod_iff h1f.prod_swap using 1
  rw [funext fun _ => Function.comp_apply.symm]; rw [integrable_swap_iff]

Depends on / 依赖: Function, Function.comp_apply.symm, comp_apply, convert, h1f.prod_swap, integrable_prod_iff, integrable_swap_iff, prod_swap
-/
theorem integrable_prod_iff' [SFinite μ] ⦃f : α × β -> E⦄
    (h1f : AEStronglyMeasurable f (μ.prod ν)) :
    Integrable f (μ.prod ν) ↔
      (forallᵐ y ∂ν, Integrable (fun x => f (x, y)) μ) ∧ Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν := by
  convert! integrable_prod_iff h1f.prod_swap using 1
  rw [funext fun _ => Function.comp_apply.symm]; rw [integrable_swap_iff]

/--
theorem `Integrable.prod_left_ae` / 定理 `Integrable.prod_left_ae`

English:
theorem Integrable.prod_left_ae
  given: [SFinite μ] ⦃f
  statement: α × β -> E⦄ (hf : Integrable f (μ.prod ν)) :
  proof: ((integrable_prod_iff' hf.aestronglyMeasurable).mp hf).1

中文:
定理 可积.prod_left_ae
  条件: [SFinite μ] ⦃f
  结论: α × β -> E⦄ (hf : 可积 f (μ.乘积 ν)) :
  证明: ((integrable_prod_iff' hf.aestronglyMeasurable).mp hf).1

Depends on / 依赖: aestronglyMeasurable, hf.aestronglyMeasurable, integrable_prod_iff
-/
theorem Integrable.prod_left_ae [SFinite μ] ⦃f : α × β -> E⦄ (hf : Integrable f (μ.prod ν)) :
    forallᵐ y ∂ν, Integrable (fun x => f (x, y)) μ :=
  ((integrable_prod_iff' hf.aestronglyMeasurable).mp hf).1

/--
theorem `Integrable.prod_right_ae` / 定理 `Integrable.prod_right_ae`

English:
theorem Integrable.prod_right_ae
  given: [SFinite μ] ⦃f
  statement: α × β -> E⦄ (hf : Integrable f (μ.prod ν)) :
  proof: hf.swap.prod_left_ae

中文:
定理 可积.prod_right_ae
  条件: [SFinite μ] ⦃f
  结论: α × β -> E⦄ (hf : 可积 f (μ.乘积 ν)) :
  证明: hf.swap.prod_left_ae

Depends on / 依赖: hf.swap.prod_left_ae, prod_left_ae
-/
theorem Integrable.prod_right_ae [SFinite μ] ⦃f : α × β -> E⦄ (hf : Integrable f (μ.prod ν)) :
    forallᵐ x ∂μ, Integrable (fun y => f (x, y)) ν :=
  hf.swap.prod_left_ae

/--
theorem `Integrable.integral_norm_prod_left` / 定理 `Integrable.integral_norm_prod_left`

English:
theorem Integrable.integral_norm_prod_left
  given: ⦃f
  statement: α × β -> E⦄ (hf : Integrable f (μ.prod ν)) :
  proof: ((integrable_prod_iff hf.aestronglyMeasurable).mp hf).2

中文:
定理 可积.integral_norm_prod_left
  条件: ⦃f
  结论: α × β -> E⦄ (hf : 可积 f (μ.乘积 ν)) :
  证明: ((integrable_prod_iff hf.aestronglyMeasurable).mp hf).2

Depends on / 依赖: aestronglyMeasurable, hf.aestronglyMeasurable, integrable_prod_iff
-/
theorem Integrable.integral_norm_prod_left ⦃f : α × β -> E⦄ (hf : Integrable f (μ.prod ν)) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) μ :=
  ((integrable_prod_iff hf.aestronglyMeasurable).mp hf).2

/--
theorem `Integrable.integral_norm_prod_right` / 定理 `Integrable.integral_norm_prod_right`

English:
theorem Integrable.integral_norm_prod_right
  given: [SFinite μ] ⦃f
  statement: α × β -> E⦄
  proof: hf.swap.integral_norm_prod_left

omit [SFinite ν] in

中文:
定理 可积.integral_norm_prod_right
  条件: [SFinite μ] ⦃f
  结论: α × β -> E⦄
  证明: hf.swap.integral_norm_prod_left

omit [SFinite ν] in

Depends on / 依赖: hf.swap.integral_norm_prod_left, integral_norm_prod_left
-/
theorem Integrable.integral_norm_prod_right [SFinite μ] ⦃f : α × β -> E⦄
    (hf : Integrable f (μ.prod ν)) : Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂μ) ν :=
  hf.swap.integral_norm_prod_left

omit [SFinite ν] in
/--
theorem `Integrable.op_fst_snd` / 定理 `Integrable.op_fst_snd`

English:
theorem Integrable.op_fst_snd
  statement: {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
  proof: by
  use hop.comp_aestronglyMeasurable₂ hf.1.comp_fst hg.1.comp_snd
  rcases hop_norm with ⟨C, hC⟩
  calc
    ∫⁻ z, ‖op (f z.1) (g z.2)‖ₑ ∂μ.prod ν <= ∫⁻ z, .ofReal C * ‖f z.1‖ₑ * ‖g z.2‖ₑ ∂μ.prod ν := by
      gcongr with z
      simp only [enorm_eq_nnnorm, ENNReal.ofReal, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
        ← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm]
      refine (hC _ _).trans ?_
      gcongr
      apply le_coe_toNNReal
    _ <= ∫⁻ x, ∫⁻ y, .ofReal C * ‖f x‖ₑ * ‖g y‖ₑ ∂ν ∂μ := lintegral_prod_le _
    _ <= .ofReal C * (∫⁻ x, ‖f x‖ₑ ∂μ) * ∫⁻ y, ‖g y‖ₑ ∂ν := by
      simp [lintegral_const_mul', lintegral_mul_const', hg.2.ne, mul_assoc]
    _ < ∞ := by apply_rules [ENNReal.mul_lt_top, hf.2, hg.2, ENNReal.ofReal_lt_top]

中文:
定理 可积.op_fst_snd
  结论: {F G : 类型} [赋范交换加群 F] [赋范交换加群 G]
  证明: by
  use hop.comp_aestronglyMeasurable₂ hf.1.comp_fst hg.1.comp_snd
  rcases hop_norm with ⟨C, hC⟩
  calc
    ∫⁻ z, ‖op (f z.1) (g z.2)‖ₑ ∂μ.prod ν <= ∫⁻ z, .ofReal C * ‖f z.1‖ₑ * ‖g z.2‖ₑ ∂μ.prod ν := by
      gcongr with z
      simp only [enorm_eq_nnnorm, ENNReal.ofReal, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
        ← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm]
      refine (hC _ _).trans ?_
      gcongr
      apply le_coe_toNNReal
    _ <= ∫⁻ x, ∫⁻ y, .ofReal C * ‖f x‖ₑ * ‖g y‖ₑ ∂ν ∂μ := lintegral_prod_le _
    _ <= .ofReal C * (∫⁻ x, ‖f x‖ₑ ∂μ) * ∫⁻ y, ‖g y‖ₑ ∂ν := by
      simp [lintegral_const_mul', lintegral_mul_const', hg.2.ne, mul_assoc]
    _ < ∞ := by apply_rules [ENNReal.mul_lt_top, hf.2, hg.2, ENNReal.ofReal_lt_top]

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.ofReal, NNReal, NNReal.coe_le_coe, NNReal.coe_mul, coe_le_coe, coe_mul, coe_nnnorm, comp_fst, comp_snd, disjoint_comm, enorm_eq_nnnorm, hop.comp_aestronglyMeasurable, hop_norm, le_coe_toNNReal, lintegral_prod_le, ofReal
-/
theorem Integrable.op_fst_snd {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {op : E -> F -> G} (hop : Continuous op.uncurry) (hop_norm : exists C, forall x y, ‖op x y‖ <= C * ‖x‖ * ‖y‖)
    {f : α -> E} {g : β -> F} (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun z => op (f z.1) (g z.2)) (μ.prod ν) := by
  use hop.comp_aestronglyMeasurable₂ hf.1.comp_fst hg.1.comp_snd
  rcases hop_norm with ⟨C, hC⟩
  calc
    ∫⁻ z, ‖op (f z.1) (g z.2)‖ₑ ∂μ.prod ν <= ∫⁻ z, .ofReal C * ‖f z.1‖ₑ * ‖g z.2‖ₑ ∂μ.prod ν := by
      gcongr with z
      simp only [enorm_eq_nnnorm, ENNReal.ofReal, ← ENNReal.coe_mul, ENNReal.coe_le_coe,
        ← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm]
      refine (hC _ _).trans ?_
      gcongr
      apply le_coe_toNNReal
    _ <= ∫⁻ x, ∫⁻ y, .ofReal C * ‖f x‖ₑ * ‖g y‖ₑ ∂ν ∂μ := lintegral_prod_le _
    _ <= .ofReal C * (∫⁻ x, ‖f x‖ₑ ∂μ) * ∫⁻ y, ‖g y‖ₑ ∂ν := by
      simp [lintegral_const_mul', lintegral_mul_const', hg.2.ne, mul_assoc]
    _ < ∞ := by apply_rules [ENNReal.mul_lt_top, hf.2, hg.2, ENNReal.ofReal_lt_top]

/--
lemma `Integrable.comp_fst` / 引理 `Integrable.comp_fst`

English:
lemma Integrable.comp_fst
  given: {f : α -> E} (hf : Integrable f μ) (ν : Measure β) [IsFiniteMeasure ν]
  proof: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_fst ν

中文:
引理 可积.comp_fst
  条件: {f : α -> E} (hf : 可积 f μ) (ν : 测度 β) [是有限测度 ν]
  证明: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_fst ν

Depends on / 依赖: comp_fst, hf.comp_fst, memLp_one_iff_integrable
-/
lemma Integrable.comp_fst {f : α -> E} (hf : Integrable f μ) (ν : Measure β) [IsFiniteMeasure ν] :
    Integrable (fun x => f x.1) (μ.prod ν) := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_fst ν

/--
lemma `Integrable.comp_snd` / 引理 `Integrable.comp_snd`

English:
lemma Integrable.comp_snd
  given: {f : β -> E} (hf : Integrable f ν) (μ : Measure α) [IsFiniteMeasure μ]
  proof: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_snd μ

omit [SFinite ν] in
@[fun_prop]

中文:
引理 可积.comp_snd
  条件: {f : β -> E} (hf : 可积 f ν) (μ : 测度 α) [是有限测度 μ]
  证明: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_snd μ

omit [SFinite ν] in
@[fun_prop]

Depends on / 依赖: comp_snd, hf.comp_snd, memLp_one_iff_integrable
-/
lemma Integrable.comp_snd {f : β -> E} (hf : Integrable f ν) (μ : Measure α) [IsFiniteMeasure μ] :
    Integrable (fun x => f x.2) (μ.prod ν) := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.comp_snd μ

omit [SFinite ν] in
@[fun_prop]
/--
theorem `Integrable.smul_prod` / 定理 `Integrable.smul_prod`

English:
theorem Integrable.smul_prod
  statement: {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E]
  proof: hf.op_fst_snd continuous_smul ⟨1, by simpa using norm_smul_le⟩ hg

omit [SFinite ν] in
@[fun_prop]

中文:
定理 可积.smul_prod
  结论: {R : 类型} [赋范环 R] [模 R E] [是BoundedSMul R E]
  证明: hf.op_fst_snd continuous_smul ⟨1, by simpa using norm_smul_le⟩ hg

omit [SFinite ν] in
@[fun_prop]

Depends on / 依赖: continuous_smul, hf.op_fst_snd, norm_smul_le, op_fst_snd
-/
theorem Integrable.smul_prod {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E]
    {f : α -> R} {g : β -> E} (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun z : α × β => f z.1 • g z.2) (μ.prod ν) :=
  hf.op_fst_snd continuous_smul ⟨1, by simpa using norm_smul_le⟩ hg

omit [SFinite ν] in
@[fun_prop]
/--
theorem `Integrable.mul_prod` / 定理 `Integrable.mul_prod`

English:
theorem Integrable.mul_prod
  statement: {L : Type*} [NormedRing L] {f : α -> L} {g : β -> L} (hf : Integrable f μ)
  proof: hf.smul_prod hg

中文:
定理 可积.mul_prod
  结论: {L : 类型} [赋范环 L] {f : α -> L} {g : β -> L} (hf : 可积 f μ)
  证明: hf.smul_prod hg

Depends on / 依赖: ha.trans, hc.trans, hf.smul_prod, smul_prod
-/
theorem Integrable.mul_prod {L : Type*} [NormedRing L] {f : α -> L} {g : β -> L} (hf : Integrable f μ)
    (hg : Integrable g ν) : Integrable (fun z : α × β => f z.1 * g z.2) (μ.prod ν) :=
  hf.smul_prod hg

/--
theorem `IntegrableOn.swap` / 定理 `IntegrableOn.swap`

English:
theorem IntegrableOn.swap
  statement: [SFinite μ] {f : α × β -> E} {s : Set α} {t : Set β}
  proof: by
  rw [IntegrableOn]; rw [← Measure.prod_restrict] at hf ⊢
  exact hf.swap

中文:
定理 整数egrableOn.swap
  结论: [SFinite μ] {f : α × β -> E} {s : 集合 α} {t : 集合 β}
  证明: by
  rw [IntegrableOn]; rw [← Measure.prod_restrict] at hf ⊢
  exact hf.swap

Depends on / 依赖: IntegrableOn, Measure, Measure.prod_restrict, hf.swap, prod_restrict
-/
theorem IntegrableOn.swap [SFinite μ] {f : α × β -> E} {s : Set α} {t : Set β}
    (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    IntegrableOn (f ∘ Prod.swap) (t ×ˢ s) (ν.prod μ) := by
  rw [IntegrableOn]; rw [← Measure.prod_restrict] at hf ⊢
  exact hf.swap

/--
theorem `Integrable.of_comp_snd` / 定理 `Integrable.of_comp_snd`

English:
theorem Integrable.of_comp_snd
  given: {f : β -> E} (hf : Integrable (f ·.2) (μ.prod ν)) (hμ : μ != 0)
  proof: by
  rcases hf with ⟨hf_meas, hf_fin⟩
  use hf_meas.of_comp_snd hμ
  have := hf_meas.enorm
  aesop (add simp [HasFiniteIntegral, lintegral_prod, ENNReal.mul_lt_top_iff])

中文:
定理 可积.of_comp_snd
  条件: {f : β -> E} (hf : 可积 (f ·.2) (μ.乘积 ν)) (hμ : μ != 0)
  证明: by
  rcases hf with ⟨hf_meas, hf_fin⟩
  use hf_meas.of_comp_snd hμ
  have := hf_meas.enorm
  aesop (add simp [HasFiniteIntegral, lintegral_prod, ENNReal.mul_lt_top_iff])

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top_iff, HasFiniteIntegral, hf_fin, hf_meas, hf_meas.enorm, hf_meas.of_comp_snd, lintegral_prod, mul_lt_top_iff, of_comp_snd
-/
theorem Integrable.of_comp_snd {f : β -> E} (hf : Integrable (f ·.2) (μ.prod ν)) (hμ : μ != 0) :
    Integrable f ν := by
  rcases hf with ⟨hf_meas, hf_fin⟩
  use hf_meas.of_comp_snd hμ
  have := hf_meas.enorm
  aesop (add simp [HasFiniteIntegral, lintegral_prod, ENNReal.mul_lt_top_iff])

/--
theorem `Integrable.of_comp_fst` / 定理 `Integrable.of_comp_fst`

English:
theorem Integrable.of_comp_fst
  statement: [SFinite μ] {f : α -> E} (hf : Integrable (f ·.1) (μ.prod ν))
  proof: hf.swap.of_comp_snd hν

中文:
定理 可积.of_comp_fst
  结论: [SFinite μ] {f : α -> E} (hf : 可积 (f ·.1) (μ.乘积 ν))
  证明: hf.swap.of_comp_snd hν

Depends on / 依赖: hf.swap.of_comp_snd, of_comp_snd
-/
theorem Integrable.of_comp_fst [SFinite μ] {f : α -> E} (hf : Integrable (f ·.1) (μ.prod ν))
    (hν : ν != 0) : Integrable f μ :=
  hf.swap.of_comp_snd hν

/--
theorem `Integrable.comp_snd_iff` / 定理 `Integrable.comp_snd_iff`

English:
theorem Integrable.comp_snd_iff
  given: [IsFiniteMeasure μ] {f : β -> E} (hμ : μ != 0)
  proof: ⟨(.of_comp_snd · hμ), (.comp_snd · μ)⟩

omit [SFinite ν] in

中文:
定理 可积.comp_snd_iff
  条件: [是有限测度 μ] {f : β -> E} (hμ : μ != 0)
  证明: ⟨(.of_comp_snd · hμ), (.comp_snd · μ)⟩

omit [SFinite ν] in

Depends on / 依赖: comp_snd, of_comp_snd
-/
theorem Integrable.comp_snd_iff [IsFiniteMeasure μ] {f : β -> E} (hμ : μ != 0) :
    Integrable (f ·.2) (μ.prod ν) ↔ Integrable f ν :=
  ⟨(.of_comp_snd · hμ), (.comp_snd · μ)⟩

omit [SFinite ν] in
/--
theorem `Integrable.comp_fst_iff` / 定理 `Integrable.comp_fst_iff`

English:
theorem Integrable.comp_fst_iff
  given: [SFinite μ] [IsFiniteMeasure ν] {f : α -> E} (hν : ν != 0)
  proof: ⟨(.of_comp_fst · hν), (.comp_fst · ν)⟩

中文:
定理 可积.comp_fst_iff
  条件: [SFinite μ] [是有限测度 ν] {f : α -> E} (hν : ν != 0)
  证明: ⟨(.of_comp_fst · hν), (.comp_fst · ν)⟩

Depends on / 依赖: comp_fst, of_comp_fst
-/
theorem Integrable.comp_fst_iff [SFinite μ] [IsFiniteMeasure ν] {f : α -> E} (hν : ν != 0) :
    Integrable (f ·.1) (μ.prod ν) ↔ Integrable f μ :=
  ⟨(.of_comp_fst · hν), (.comp_fst · ν)⟩

end

variable [NormedSpace Real E]

/--
theorem `Integrable.integral_prod_left` / 定理 `Integrable.integral_prod_left`

English:
theorem Integrable.integral_prod_left
  given: ⦃f
  statement: α × β -> E⦄ (hf : Integrable f (μ.prod ν)) :
  proof: by
  apply Integrable.mono hf.integral_norm_prod_left hf.aestronglyMeasurable.integral_prod_right'
  filter_upwards with x
  grw [norm_integral_le_integral_norm]
  exact le_abs_self _

中文:
定理 可积.integral_prod_left
  条件: ⦃f
  结论: α × β -> E⦄ (hf : 可积 f (μ.乘积 ν)) :
  证明: by
  apply Integrable.mono hf.integral_norm_prod_left hf.aestronglyMeasurable.integral_prod_right'
  filter_upwards with x
  grw [norm_integral_le_integral_norm]
  exact le_abs_self _

Depends on / 依赖: Integrable, Integrable.mono, aestronglyMeasurable, filter_upwards, hf.aestronglyMeasurable.integral_prod_right, hf.integral_norm_prod_left, integral_norm_prod_left, integral_prod_right, le_abs_self, norm_integral_le_integral_norm
-/
theorem Integrable.integral_prod_left ⦃f : α × β -> E⦄ (hf : Integrable f (μ.prod ν)) :
    Integrable (fun x => ∫ y, f (x, y) ∂ν) μ := by
  apply Integrable.mono hf.integral_norm_prod_left hf.aestronglyMeasurable.integral_prod_right'
  filter_upwards with x
  grw [norm_integral_le_integral_norm]
  exact le_abs_self _

/--
theorem `Integrable.integral_prod_right` / 定理 `Integrable.integral_prod_right`

English:
theorem Integrable.integral_prod_right
  given: [SFinite μ] ⦃f
  statement: α × β -> E⦄
  proof: hf.swap.integral_prod_left

中文:
定理 可积.integral_prod_right
  条件: [SFinite μ] ⦃f
  结论: α × β -> E⦄
  证明: hf.swap.integral_prod_left

Depends on / 依赖: hf.swap.integral_prod_left, integral_prod_left
-/
theorem Integrable.integral_prod_right [SFinite μ] ⦃f : α × β -> E⦄
    (hf : Integrable f (μ.prod ν)) : Integrable (fun y => ∫ x, f (x, y) ∂μ) ν :=
  hf.swap.integral_prod_left

/-! ### The Bochner integral on a product -/

variable [SFinite μ]

/--
theorem `integral_prod_swap` / 定理 `integral_prod_swap`

English:
theorem integral_prod_swap
  given: (f : α × β -> E)
  proof: measurePreserving_swap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding _

中文:
定理 integral_prod_swap
  条件: (f : α × β -> E)
  证明: measurePreserving_swap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding _

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.prodComm.measurableEmbedding, integral_comp, measurableEmbedding, measurePreserving_swap, measurePreserving_swap.integral_comp, prodComm
-/
theorem integral_prod_swap (f : α × β -> E) :
    ∫ z, f z.swap ∂ν.prod μ = ∫ z, f z ∂μ.prod ν :=
  measurePreserving_swap.integral_comp MeasurableEquiv.prodComm.measurableEmbedding _

/--
theorem `setIntegral_prod_swap` / 定理 `setIntegral_prod_swap`

English:
theorem setIntegral_prod_swap
  given: (s : Set α) (t : Set β) (f : α × β -> E)
  proof: by
  rw [← Measure.prod_restrict]; rw [← Measure.prod_restrict]; rw [integral_prod_swap]

中文:
定理 set整数egral_prod_swap
  条件: (s : 集合 α) (t : 集合 β) (f : α × β -> E)
  证明: by
  rw [← Measure.prod_restrict]; rw [← Measure.prod_restrict]; rw [integral_prod_swap]

Depends on / 依赖: Measure, Measure.prod_restrict, integral_prod_swap, prod_restrict
-/
theorem setIntegral_prod_swap (s : Set α) (t : Set β) (f : α × β -> E) :
    ∫ (z : β × α) in t ×ˢ s, f z.swap ∂ν.prod μ = ∫ (z : α × β) in s ×ˢ t, f z ∂μ.prod ν := by
  rw [← Measure.prod_restrict]; rw [← Measure.prod_restrict]; rw [integral_prod_swap]

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']

/-! Some rules about the sum/difference of double integrals. They follow from `integral_add`, but
  we separate them out as separate lemmas, because they involve quite some steps. -/


/--
theorem `integral_fn_integral_add` / 定理 `integral_fn_integral_add`

English:
theorem integral_fn_integral_add
  given: ⦃f g
  statement: α × β -> E⦄ (F : E -> E') (hf : Integrable f (μ.prod ν))
  proof: by
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_add h2f h2g]

中文:
定理 integral_fn_integral_add
  条件: ⦃f g
  结论: α × β -> E⦄ (F : E -> E') (hf : 可积 f (μ.乘积 ν))
  证明: by
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_add h2f h2g]

Depends on / 依赖: filter_upwards, hf.prod_right_ae, hg.prod_right_ae, integral_add, integral_congr_ae, prod_right_ae
-/
theorem integral_fn_integral_add ⦃f g : α × β -> E⦄ (F : E -> E') (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, F (∫ y, f (x, y) + g (x, y) ∂ν) ∂μ) =
      ∫ x, F ((∫ y, f (x, y) ∂ν) + ∫ y, g (x, y) ∂ν) ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_add h2f h2g]

/--
theorem `integral_fn_integral_sub` / 定理 `integral_fn_integral_sub`

English:
theorem integral_fn_integral_sub
  given: ⦃f g
  statement: α × β -> E⦄ (F : E -> E') (hf : Integrable f (μ.prod ν))
  proof: by
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_sub h2f h2g]

中文:
定理 integral_fn_integral_sub
  条件: ⦃f g
  结论: α × β -> E⦄ (F : E -> E') (hf : 可积 f (μ.乘积 ν))
  证明: by
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_sub h2f h2g]

Depends on / 依赖: filter_upwards, hf.prod_right_ae, hg.prod_right_ae, integral_congr_ae, integral_sub, prod_right_ae
-/
theorem integral_fn_integral_sub ⦃f g : α × β -> E⦄ (F : E -> E') (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ) =
      ∫ x, F ((∫ y, f (x, y) ∂ν) - ∫ y, g (x, y) ∂ν) ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_sub h2f h2g]

/--
theorem `lintegral_fn_integral_sub` / 定理 `lintegral_fn_integral_sub`

English:
theorem lintegral_fn_integral_sub
  given: ⦃f g
  statement: α × β -> E⦄ (F : E -> Real>=0∞) (hf : Integrable f (μ.prod ν))
  proof: by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_sub h2f h2g]

中文:
定理 lintegral_fn_integral_sub
  条件: ⦃f g
  结论: α × β -> E⦄ (F : E -> 实数>=0∞) (hf : 可积 f (μ.乘积 ν))
  证明: by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_sub h2f h2g]

Depends on / 依赖: filter_upwards, hf.prod_right_ae, hg.prod_right_ae, integral_sub, lintegral_congr_ae, prod_right_ae
-/
theorem lintegral_fn_integral_sub ⦃f g : α × β -> E⦄ (F : E -> Real>=0∞) (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫⁻ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ) =
      ∫⁻ x, F ((∫ y, f (x, y) ∂ν) - ∫ y, g (x, y) ∂ν) ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.prod_right_ae, hg.prod_right_ae] with _ h2f h2g
  simp [integral_sub h2f h2g]

/--
theorem `integral_integral_add` / 定理 `integral_integral_add`

English:
theorem integral_integral_add
  given: ⦃f g
  statement: α × β -> E⦄ (hf : Integrable f (μ.prod ν))
  proof: (integral_fn_integral_add id hf hg).trans
    integral_add hf.integral_prod_left hg.integral_prod_left

中文:
定理 integral_integral_add
  条件: ⦃f g
  结论: α × β -> E⦄ (hf : 可积 f (μ.乘积 ν))
  证明: (integral_fn_integral_add id hf hg).trans
    integral_add hf.integral_prod_left hg.integral_prod_left

Depends on / 依赖: hf.integral_prod_left, hg.integral_prod_left, integral_add, integral_fn_integral_add, integral_prod_left
-/
theorem integral_integral_add ⦃f g : α × β -> E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, f (x, y) + g (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
(integral_fn_integral_add id hf hg).trans
    integral_add hf.integral_prod_left hg.integral_prod_left

/--
theorem `integral_integral_add'` / 定理 `integral_integral_add'`

English:
theorem integral_integral_add'
  given: ⦃f g
  statement: α × β -> E⦄ (hf : Integrable f (μ.prod ν))
  proof: integral_integral_add hf hg

中文:
定理 integral_integral_add'
  条件: ⦃f g
  结论: α × β -> E⦄ (hf : 可积 f (μ.乘积 ν))
  证明: integral_integral_add hf hg

Depends on / 依赖: integral_integral_add
-/
theorem integral_integral_add' ⦃f g : α × β -> E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, (f + g) (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) + ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  integral_integral_add hf hg

/--
theorem `integral_integral_sub` / 定理 `integral_integral_sub`

English:
theorem integral_integral_sub
  given: ⦃f g
  statement: α × β -> E⦄ (hf : Integrable f (μ.prod ν))
  proof: (integral_fn_integral_sub id hf hg).trans
    integral_sub hf.integral_prod_left hg.integral_prod_left

中文:
定理 integral_integral_sub
  条件: ⦃f g
  结论: α × β -> E⦄ (hf : 可积 f (μ.乘积 ν))
  证明: (integral_fn_integral_sub id hf hg).trans
    integral_sub hf.integral_prod_left hg.integral_prod_left

Depends on / 依赖: hf.integral_prod_left, hg.integral_prod_left, integral_fn_integral_sub, integral_prod_left, integral_sub
-/
theorem integral_integral_sub ⦃f g : α × β -> E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, f (x, y) - g (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
(integral_fn_integral_sub id hf hg).trans
    integral_sub hf.integral_prod_left hg.integral_prod_left

/--
theorem `integral_integral_sub'` / 定理 `integral_integral_sub'`

English:
theorem integral_integral_sub'
  given: ⦃f g
  statement: α × β -> E⦄ (hf : Integrable f (μ.prod ν))
  proof: integral_integral_sub hf hg

中文:
定理 integral_integral_sub'
  条件: ⦃f g
  结论: α × β -> E⦄ (hf : 可积 f (μ.乘积 ν))
  证明: integral_integral_sub hf hg

Depends on / 依赖: integral_integral_sub
-/
theorem integral_integral_sub' ⦃f g : α × β -> E⦄ (hf : Integrable f (μ.prod ν))
    (hg : Integrable g (μ.prod ν)) :
    (∫ x, ∫ y, (f - g) (x, y) ∂ν ∂μ) = (∫ x, ∫ y, f (x, y) ∂ν ∂μ) - ∫ x, ∫ y, g (x, y) ∂ν ∂μ :=
  integral_integral_sub hf hg

/--
theorem `continuous_integral_integral` / 定理 `continuous_integral_integral`

English:
theorem continuous_integral_integral
  proof: by
  rw [continuous_iff_continuousAt]; intro g
  refine
    tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_prod_left.aestronglyMeasurable
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_prod_left) ?_
  simp_rw [← lintegral_fn_integral_sub _ (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun i => zero_le) _
  · exact fun i => ∫⁻ x, ∫⁻ y, ‖i (x, y) - g (x, y)‖ₑ ∂ν ∂μ
  swap; · exact fun i => lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
  have (i : α × β ->₁[μ.prod ν] E) : Measurable fun z => ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [← lintegral_prod _ (this _).aemeasurable, ← L1.ofReal_norm_sub_eq_lintegral,
    ← ofReal_zero]
  refine (continuous_ofReal.tendsto 0).comp ?_
  rw [← tendsto_iff_norm_sub_tendsto_zero]; exact tendsto_id

中文:
定理 continuous_integral_integral
  证明: by
  rw [continuous_iff_continuousAt]; intro g
  refine
    tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_prod_left.aestronglyMeasurable
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_prod_left) ?_
  simp_rw [← lintegral_fn_integral_sub _ (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun i => zero_le) _
  · exact fun i => ∫⁻ x, ∫⁻ y, ‖i (x, y) - g (x, y)‖ₑ ∂ν ∂μ
  swap; · exact fun i => lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
  have (i : α × β ->₁[μ.prod ν] E) : Measurable fun z => ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [← lintegral_prod _ (this _).aemeasurable, ← L1.ofReal_norm_sub_eq_lintegral,
    ← ofReal_zero]
  refine (continuous_ofReal.tendsto 0).comp ?_
  rw [← tendsto_iff_norm_sub_tendsto_zero]; exact tendsto_id

Depends on / 依赖: Eventually, Eventually.of_forall, L1.integrable_coeFn, aestronglyMeasurable, continuous_iff_continuousAt, integrable_coeFn, integral_prod_left, integral_prod_left.aestronglyMeasurable, lintegral_fn_integral_sub, lintegral_mono, of_forall, simp_rw, tendsto_const_nhds, tendsto_integral_of_L1, tendsto_of_tendsto_of_tendsto_of_le_of_le, zero_le
-/
theorem continuous_integral_integral :
    Continuous fun f : α × β ->₁[μ.prod ν] E => ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  rw [continuous_iff_continuousAt]; intro g
  refine
    tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_prod_left.aestronglyMeasurable
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_prod_left) ?_
  simp_rw [← lintegral_fn_integral_sub _ (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun i => zero_le) _
  · exact fun i => ∫⁻ x, ∫⁻ y, ‖i (x, y) - g (x, y)‖ₑ ∂ν ∂μ
  swap; · exact fun i => lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
  have (i : α × β ->₁[μ.prod ν] E) : Measurable fun z => ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [← lintegral_prod _ (this _).aemeasurable, ← L1.ofReal_norm_sub_eq_lintegral,
    ← ofReal_zero]
  refine (continuous_ofReal.tendsto 0).comp ?_
  rw [← tendsto_iff_norm_sub_tendsto_zero]; exact tendsto_id

/--
theorem `integral_prod` / 定理 `integral_prod`

English:
theorem integral_prod
  given: (f : α × β -> E) (hf : Integrable f (μ.prod ν))
  proof: by
  by_cases hE : CompleteSpace E; swap; · simp only [integral, dif_neg hE]
  revert f
  apply Integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), setIntegral_const, integral_smul_const,
      measureReal_def,
      integral_toReal (measurable_measure_prodMk_left hs).aemeasurable
        (ae_measure_lt_top hs h2s.ne)]
    rw [Measure.prod_apply hs]
  · rintro f g - i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, integral_integral_add' i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral continuous_integral_integral
  · rintro f g hfg - hf; convert! hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_prod hfg] with x hfgx using integral_congr_ae (ae_eq_symm hfgx)

中文:
定理 integral_prod
  条件: (f : α × β -> E) (hf : 可积 f (μ.乘积 ν))
  证明: by
  by_cases hE : CompleteSpace E; swap; · simp only [integral, dif_neg hE]
  revert f
  apply Integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), setIntegral_const, integral_smul_const,
      measureReal_def,
      integral_toReal (measurable_measure_prodMk_left hs).aemeasurable
        (ae_measure_lt_top hs h2s.ne)]
    rw [Measure.prod_apply hs]
  · rintro f g - i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, integral_integral_add' i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral continuous_integral_integral
  · rintro f g hfg - hf; convert! hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_prod hfg] with x hfgx using integral_congr_ae (ae_eq_symm hfgx)

Depends on / 依赖: CompleteSpace, Function, Function.comp_def, Integrable, Integrable.induction, Measure, Measure.prod_apply, ae_measure_lt_top, aemeasurable, comp_def, dif_neg, h2s.ne, indicator_comp_right, integr, integral, integral_add, integral_indicator, integral_smul_const, integral_toReal, measurable_measure_prodMk_left
-/
theorem integral_prod (f : α × β -> E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  by_cases hE : CompleteSpace E; swap; · simp only [integral, dif_neg hE]
  revert f
  apply Integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), setIntegral_const, integral_smul_const,
      measureReal_def,
      integral_toReal (measurable_measure_prodMk_left hs).aemeasurable
        (ae_measure_lt_top hs h2s.ne)]
    rw [Measure.prod_apply hs]
  · rintro f g - i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, integral_integral_add' i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral continuous_integral_integral
  · rintro f g hfg - hf; convert! hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_prod hfg] with x hfgx using integral_congr_ae (ae_eq_symm hfgx)

/--
theorem `integral_prod_symm` / 定理 `integral_prod_symm`

English:
theorem integral_prod_symm
  given: (f : α × β -> E) (hf : Integrable f (μ.prod ν))
  proof: by
  rw [← integral_prod_swap f]; exact integral_prod _ hf.swap

中文:
定理 integral_prod_symm
  条件: (f : α × β -> E) (hf : 可积 f (μ.乘积 ν))
  证明: by
  rw [← integral_prod_swap f]; exact integral_prod _ hf.swap

Depends on / 依赖: hf.swap, integral_prod, integral_prod_swap
-/
theorem integral_prod_symm (f : α × β -> E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  rw [← integral_prod_swap f]; exact integral_prod _ hf.swap

/--
theorem `integral_integral` / 定理 `integral_integral`

English:
theorem integral_integral
  given: {f : α -> β -> E} (hf : Integrable (uncurry f) (μ.prod ν))
  proof: (integral_prod _ hf).symm

中文:
定理 integral_integral
  条件: {f : α -> β -> E} (hf : 可积 (uncurry f) (μ.乘积 ν))
  证明: (integral_prod _ hf).symm

Depends on / 依赖: integral_prod
-/
theorem integral_integral {f : α -> β -> E} (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.1 z.2 ∂μ.prod ν :=
  (integral_prod _ hf).symm

/--
theorem `integral_integral_symm` / 定理 `integral_integral_symm`

English:
theorem integral_integral_symm
  given: {f : α -> β -> E} (hf : Integrable (uncurry f) (μ.prod ν))
  proof: (integral_prod_symm _ hf.swap).symm

中文:
定理 integral_integral_symm
  条件: {f : α -> β -> E} (hf : 可积 (uncurry f) (μ.乘积 ν))
  证明: (integral_prod_symm _ hf.swap).symm

Depends on / 依赖: hf.swap, integral_prod_symm
-/
theorem integral_integral_symm {f : α -> β -> E} (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ z, f z.2 z.1 ∂ν.prod μ :=
  (integral_prod_symm _ hf.swap).symm

/--
theorem `integral_integral_swap` / 定理 `integral_integral_swap`

English:
theorem integral_integral_swap
  given: ⦃f
  statement: α -> β -> E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) :
  proof: (integral_integral hf).trans (integral_prod_symm _ hf)

中文:
定理 integral_integral_swap
  条件: ⦃f
  结论: α -> β -> E⦄ (hf : 可积 (uncurry f) (μ.乘积 ν)) :
  证明: (integral_integral hf).trans (integral_prod_symm _ hf)

Depends on / 依赖: integral_integral, integral_prod_symm
-/
theorem integral_integral_swap ⦃f : α -> β -> E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν :=
  (integral_integral hf).trans (integral_prod_symm _ hf)

/--
lemma `intervalIntegral_integral_swap` / 引理 `intervalIntegral_integral_swap`

English:
lemma intervalIntegral_integral_swap
  statement: {a b : Real} {f : Real -> α -> E}
  proof: by
  rcases le_total a b with (hab | hab)
  · simp_rw [intervalIntegral.integral_of_le hab]
    simp only [hab, Set.uIoc_of_le] at h_int
    exact integral_integral_swap h_int
  · simp_rw [intervalIntegral.integral_of_ge hab]
    simp only [hab, Set.uIoc_of_ge] at h_int
    rw [integral_integral_swap h_int]; rw [integral_neg]

中文:
引理 interval整数egral_integral_swap
  结论: {a b : 实数} {f : 实数 -> α -> E}
  证明: by
  rcases le_total a b with (hab | hab)
  · simp_rw [intervalIntegral.integral_of_le hab]
    simp only [hab, Set.uIoc_of_le] at h_int
    exact integral_integral_swap h_int
  · simp_rw [intervalIntegral.integral_of_ge hab]
    simp only [hab, Set.uIoc_of_ge] at h_int
    rw [integral_integral_swap h_int]; rw [integral_neg]

Depends on / 依赖: Set.uIoc_of_ge, Set.uIoc_of_le, h_int, integral_integral_swap, integral_neg, integral_of_ge, integral_of_le, intervalIntegral, intervalIntegral.integral_of_ge, intervalIntegral.integral_of_le, le_total, simp_rw, uIoc_of_ge, uIoc_of_le
-/
lemma intervalIntegral_integral_swap {a b : Real} {f : Real -> α -> E}
    (h_int : Integrable (uncurry f) ((volume.restrict (Set.uIoc a b)).prod μ)) :
    ∫ x in a..b, ∫ y, f x y ∂μ = ∫ y, (∫ x in a..b, f x y) ∂μ := by
  rcases le_total a b with (hab | hab)
  · simp_rw [intervalIntegral.integral_of_le hab]
    simp only [hab, Set.uIoc_of_le] at h_int
    exact integral_integral_swap h_int
  · simp_rw [intervalIntegral.integral_of_ge hab]
    simp only [hab, Set.uIoc_of_ge] at h_int
    rw [integral_integral_swap h_int]; rw [integral_neg]

/--
lemma `intervalIntegral_intervalIntegral_swap` / 引理 `intervalIntegral_intervalIntegral_swap`

English:
lemma intervalIntegral_intervalIntegral_swap
  statement: {F : Real -> Real -> E} {a b c d : Real}
  proof: by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]; rw [← intervalIntegral_integral_swap]; rw [← intervalIntegral.integral_smul]
  · simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  · rwa [← integrable_swap_iff, Measure.prod_restrict, ← Measure.volume_eq_prod, ← IntegrableOn]

中文:
引理 interval整数egral_interval整数egral_swap
  结论: {F : 实数 -> 实数 -> E} {a b c d : 实数}
  证明: by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]; rw [← intervalIntegral_integral_swap]; rw [← intervalIntegral.integral_smul]
  · simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  · rwa [← integrable_swap_iff, Measure.prod_restrict, ← Measure.volume_eq_prod, ← IntegrableOn]

Depends on / 依赖: IntegrableOn, Measure, Measure.prod_restrict, Measure.volume_eq_prod, integrable_swap_iff, integral_smul, intervalIntegral, intervalIntegral.integral_smul, intervalIntegral.intervalIntegral_eq_integral_uIoc, intervalIntegral_eq_integral_uIoc, intervalIntegral_integral_swap, prod_restrict, simp_rw, volume_eq_prod
-/
lemma intervalIntegral_intervalIntegral_swap {F : Real -> Real -> E} {a b c d : Real}
    (h : IntegrableOn F.uncurry (uIoc a b ×ˢ uIoc c d)) :
    ∫ x in a..b, ∫ y in c..d, F x y = ∫ y in c..d, ∫ x in a..b, F x y := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]; rw [← intervalIntegral_integral_swap]; rw [← intervalIntegral.integral_smul]
  · simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  · rwa [← integrable_swap_iff, Measure.prod_restrict, ← Measure.volume_eq_prod, ← IntegrableOn]

/--
theorem `setIntegral_prod` / 定理 `setIntegral_prod`

English:
theorem setIntegral_prod
  statement: (f : α × β -> E) {s : Set α} {t : Set β}
  proof: by
  simp only [← Measure.prod_restrict s t, IntegrableOn] at hf ⊢
  exact integral_prod f hf

中文:
定理 set整数egral_prod
  结论: (f : α × β -> E) {s : 集合 α} {t : 集合 β}
  证明: by
  simp only [← Measure.prod_restrict s t, IntegrableOn] at hf ⊢
  exact integral_prod f hf

Depends on / 依赖: IntegrableOn, Measure, Measure.prod_restrict, integral_prod, prod_restrict
-/
theorem setIntegral_prod (f : α × β -> E) {s : Set α} {t : Set β}
    (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    ∫ z in s ×ˢ t, f z ∂μ.prod ν = ∫ x in s, ∫ y in t, f (x, y) ∂ν ∂μ := by
  simp only [← Measure.prod_restrict s t, IntegrableOn] at hf ⊢
  exact integral_prod f hf

/--
theorem `integral_prod_bilin` / 定理 `integral_prod_bilin`

English:
theorem integral_prod_bilin
  statement: {E F G 𝕜 : Type*} [RCLike 𝕜]
  proof: by
  have : Integrable (fun z => B (f z.1) (g z.2)) (μ.prod ν) :=
    hf.op_fst_snd (by fun_prop) ⟨‖B‖, B.le_opNorm₂⟩ hg
  simp_rw [integral_prod _ this, ContinuousLinearMap.integral_comp_comm _ hg]
  change ∫ x, B.flip (∫ y, g y ∂ν) (f x) ∂μ = _
  rw [ContinuousLinearMap.integral_comp_comm _ hf]
  simp

中文:
定理 integral_prod_bilin
  结论: {E F G 𝕜 : 类型} [RCLike 𝕜]
  证明: by
  have : Integrable (fun z => B (f z.1) (g z.2)) (μ.prod ν) :=
    hf.op_fst_snd (by fun_prop) ⟨‖B‖, B.le_opNorm₂⟩ hg
  simp_rw [integral_prod _ this, ContinuousLinearMap.integral_comp_comm _ hg]
  change ∫ x, B.flip (∫ y, g y ∂ν) (f x) ∂μ = _
  rw [ContinuousLinearMap.integral_comp_comm _ hf]
  simp

Depends on / 依赖: B.flip, B.le_opNorm, ContinuousLinearMap, ContinuousLinearMap.integral_comp_comm, Integrable, fun_prop, hf.op_fst_snd, integral_comp_comm, integral_prod, op_fst_snd, simp_rw
-/
theorem integral_prod_bilin {E F G 𝕜 : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace Real F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace Real G] [NormedSpace 𝕜 G] [CompleteSpace G]
    (B : E ->L[𝕜] F ->L[𝕜] G) {f : α -> E} {g : β -> F}
    (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ z, B (f z.1) (g z.2) ∂μ.prod ν = B (∫ x, f x ∂μ) (∫ y, g y ∂ν) := by
  have : Integrable (fun z => B (f z.1) (g z.2)) (μ.prod ν) :=
    hf.op_fst_snd (by fun_prop) ⟨‖B‖, B.le_opNorm₂⟩ hg
  simp_rw [integral_prod _ this, ContinuousLinearMap.integral_comp_comm _ hg]
  change ∫ x, B.flip (∫ y, g y ∂ν) (f x) ∂μ = _
  rw [ContinuousLinearMap.integral_comp_comm _ hf]
  simp

/--
theorem `integral_prod_smul` / 定理 `integral_prod_smul`

English:
theorem integral_prod_smul
  given: {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (f : α -> 𝕜) (g : β -> E)
  proof: by
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE]
  by_cases h : Integrable (fun z : α × β => f z.1 • g z.2) (μ.prod ν)
  · rw [integral_prod _ h]
    simp_rw [integral_smul, integral_smul_const]
  have H : ¬Integrable f μ ∨ ¬Integrable g ν := by
    contrapose! h
    exact h.1.smul_prod h.2
  rcases H with H | H <;> simp [integral_undef h, integral_undef H]

中文:
定理 integral_prod_smul
  条件: {𝕜 : 类型} [RCLike 𝕜] [赋范空间 𝕜 E] (f : α -> 𝕜) (g : β -> E)
  证明: by
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE]
  by_cases h : Integrable (fun z : α × β => f z.1 • g z.2) (μ.prod ν)
  · rw [integral_prod _ h]
    simp_rw [integral_smul, integral_smul_const]
  have H : ¬Integrable f μ ∨ ¬Integrable g ν := by
    contrapose! h
    exact h.1.smul_prod h.2
  rcases H with H | H <;> simp [integral_undef h, integral_undef H]

Depends on / 依赖: CompleteSpace, Integrable, contrapose, integral, integral_prod, integral_smul, integral_smul_const, integral_undef, simp_rw, smul_prod
-/
theorem integral_prod_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] (f : α -> 𝕜) (g : β -> E) :
    ∫ z, f z.1 • g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) • ∫ y, g y ∂ν := by
  by_cases hE : CompleteSpace E; swap; · simp [integral, hE]
  by_cases h : Integrable (fun z : α × β => f z.1 • g z.2) (μ.prod ν)
  · rw [integral_prod _ h]
    simp_rw [integral_smul, integral_smul_const]
  have H : ¬Integrable f μ ∨ ¬Integrable g ν := by
    contrapose! h
    exact h.1.smul_prod h.2
  rcases H with H | H <;> simp [integral_undef h, integral_undef H]

/--
theorem `integral_prod_mul` / 定理 `integral_prod_mul`

English:
theorem integral_prod_mul
  given: {L : Type*} [RCLike L] (f : α -> L) (g : β -> L)
  proof: integral_prod_smul f g

中文:
定理 integral_prod_mul
  条件: {L : 类型} [RCLike L] (f : α -> L) (g : β -> L)
  证明: integral_prod_smul f g

Depends on / 依赖: integral_prod_smul
-/
theorem integral_prod_mul {L : Type*} [RCLike L] (f : α -> L) (g : β -> L) :
    ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y, g y ∂ν :=
  integral_prod_smul f g

/--
theorem `setIntegral_prod_mul` / 定理 `setIntegral_prod_mul`

English:
theorem setIntegral_prod_mul
  statement: {L : Type*} [RCLike L] (f : α -> L) (g : β -> L) (s : Set α)
  proof: by
  rw [← Measure.prod_restrict s t]
  apply integral_prod_mul

中文:
定理 set整数egral_prod_mul
  结论: {L : 类型} [RCLike L] (f : α -> L) (g : β -> L) (s : 集合 α)
  证明: by
  rw [← Measure.prod_restrict s t]
  apply integral_prod_mul

Depends on / 依赖: Measure, Measure.prod_restrict, integral_prod_mul, prod_restrict
-/
theorem setIntegral_prod_mul {L : Type*} [RCLike L] (f : α -> L) (g : β -> L) (s : Set α)
    (t : Set β) :
    ∫ z in s ×ˢ t, f z.1 * g z.2 ∂μ.prod ν = (∫ x in s, f x ∂μ) * ∫ y in t, g y ∂ν := by
  rw [← Measure.prod_restrict s t]
  apply integral_prod_mul

/--
theorem `integral_fun_snd` / 定理 `integral_fun_snd`

English:
theorem integral_fun_snd
  given: (f : β -> E)
  statement: ∫ z, f z.2 ∂μ.prod ν = μ.real univ • ∫ y, f y ∂ν
  proof: by
  simpa using integral_prod_smul (1 : α -> Real) f

中文:
定理 integral_fun_snd
  条件: (f : β -> E)
  结论: ∫ z, f z.2 ∂μ.乘积 ν = μ.real univ • ∫ y, f y ∂ν
  证明: by
  simpa using integral_prod_smul (1 : α -> Real) f

Depends on / 依赖: integral_prod_smul
-/
theorem integral_fun_snd (f : β -> E) : ∫ z, f z.2 ∂μ.prod ν = μ.real univ • ∫ y, f y ∂ν := by
  simpa using integral_prod_smul (1 : α -> Real) f

/--
theorem `integral_fun_fst` / 定理 `integral_fun_fst`

English:
theorem integral_fun_fst
  given: (f : α -> E)
  statement: ∫ z, f z.1 ∂μ.prod ν = ν.real univ • ∫ x, f x ∂μ
  proof: by
  rw [← integral_prod_swap]
  apply integral_fun_snd

中文:
定理 integral_fun_fst
  条件: (f : α -> E)
  结论: ∫ z, f z.1 ∂μ.乘积 ν = ν.real univ • ∫ x, f x ∂μ
  证明: by
  rw [← integral_prod_swap]
  apply integral_fun_snd

Depends on / 依赖: integral_fun_snd, integral_prod_swap
-/
theorem integral_fun_fst (f : α -> E) : ∫ z, f z.1 ∂μ.prod ν = ν.real univ • ∫ x, f x ∂μ := by
  rw [← integral_prod_swap]
  apply integral_fun_snd

section ContinuousLinearMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace Real F] {mF : MeasurableSpace F}
  [NormedAddCommGroup G] [NormedSpace Real G] {mG : MeasurableSpace G}
  {μ : Measure E} [IsProbabilityMeasure μ] {ν : Measure F} [IsProbabilityMeasure ν]
  {L : E × F ->L[Real] G}

/--
lemma `integrable_continuousLinearMap_prod'` / 引理 `integrable_continuousLinearMap_prod'`

English:
lemma integrable_continuousLinearMap_prod'
  proof: by
  change Integrable (fun v => L v) (μ.prod ν)
  simp_rw [← L.comp_inl_add_comp_inr]
  exact (hLμ.comp_fst ν).add (hLν.comp_snd μ)

中文:
引理 integrable_continuousLinearMap_prod'
  证明: by
  change Integrable (fun v => L v) (μ.prod ν)
  simp_rw [← L.comp_inl_add_comp_inr]
  exact (hLμ.comp_fst ν).add (hLν.comp_snd μ)

Depends on / 依赖: Integrable, L.comp_inl_add_comp_inr, comp_fst, comp_inl_add_comp_inr, comp_snd, simp_rw
-/
lemma integrable_continuousLinearMap_prod'
    (hLμ : Integrable (L.comp (.inl Real E F)) μ) (hLν : Integrable (L.comp (.inr Real E F)) ν) :
    Integrable L (μ.prod ν) := by
  change Integrable (fun v => L v) (μ.prod ν)
  simp_rw [← L.comp_inl_add_comp_inr]
  exact (hLμ.comp_fst ν).add (hLν.comp_snd μ)

/--
lemma `integrable_continuousLinearMap_prod` / 引理 `integrable_continuousLinearMap_prod`

English:
lemma integrable_continuousLinearMap_prod
  given: (hμ : Integrable id μ) (hν : Integrable id ν)
  proof: integrable_continuousLinearMap_prod' (ContinuousLinearMap.integrable_comp _ hμ)
    (ContinuousLinearMap.integrable_comp _ hν)

中文:
引理 integrable_continuousLinearMap_prod
  条件: (hμ : 可积 id μ) (hν : 可积 id ν)
  证明: integrable_continuousLinearMap_prod' (ContinuousLinearMap.integrable_comp _ hμ)
    (ContinuousLinearMap.integrable_comp _ hν)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integrable_comp, integrable_comp, integrable_continuousLinearMap_prod
-/
lemma integrable_continuousLinearMap_prod (hμ : Integrable id μ) (hν : Integrable id ν) :
    Integrable L (μ.prod ν) :=
  integrable_continuousLinearMap_prod' (ContinuousLinearMap.integrable_comp _ hμ)
    (ContinuousLinearMap.integrable_comp _ hν)

variable [CompleteSpace G]

/--
lemma `integral_continuousLinearMap_prod'` / 引理 `integral_continuousLinearMap_prod'`

English:
lemma integral_continuousLinearMap_prod'
  proof: by
  simp_rw [← L.comp_inl_add_comp_inr]
  replace hLμ := ((memLp_one_iff_integrable.mpr hLμ).comp_fst ν).integrable le_rfl
  replace hLν := ((memLp_one_iff_integrable.mpr hLν).comp_snd μ).integrable le_rfl
  rw [integral_add hLμ hLν]; rw [integral_prod _ hLμ]; rw [integral_prod _ hLν]
  simp

中文:
引理 integral_continuousLinearMap_prod'
  证明: by
  simp_rw [← L.comp_inl_add_comp_inr]
  replace hLμ := ((memLp_one_iff_integrable.mpr hLμ).comp_fst ν).integrable le_rfl
  replace hLν := ((memLp_one_iff_integrable.mpr hLν).comp_snd μ).integrable le_rfl
  rw [integral_add hLμ hLν]; rw [integral_prod _ hLμ]; rw [integral_prod _ hLν]
  simp

Depends on / 依赖: L.comp_inl_add_comp_inr, comp_fst, comp_inl_add_comp_inr, comp_snd, integrable, integral_add, integral_prod, le_rfl, memLp_one_iff_integrable, memLp_one_iff_integrable.mpr, replace, simp_rw
-/
lemma integral_continuousLinearMap_prod'
    (hLμ : Integrable (L.comp (.inl Real E F)) μ) (hLν : Integrable (L.comp (.inr Real E F)) ν) :
    ∫ p, L p ∂(μ.prod ν) = ∫ x, L.comp (.inl Real E F) x ∂μ + ∫ y, L.comp (.inr Real E F) y ∂ν := by
  simp_rw [← L.comp_inl_add_comp_inr]
  replace hLμ := ((memLp_one_iff_integrable.mpr hLμ).comp_fst ν).integrable le_rfl
  replace hLν := ((memLp_one_iff_integrable.mpr hLν).comp_snd μ).integrable le_rfl
  rw [integral_add hLμ hLν]; rw [integral_prod _ hLμ]; rw [integral_prod _ hLν]
  simp

/--
lemma `integral_continuousLinearMap_prod` / 引理 `integral_continuousLinearMap_prod`

English:
lemma integral_continuousLinearMap_prod
  given: (hμ : Integrable id μ) (hν : Integrable id ν)
  proof: integral_continuousLinearMap_prod' (ContinuousLinearMap.integrable_comp _ hμ)
    (ContinuousLinearMap.integrable_comp _ hν)

中文:
引理 integral_continuousLinearMap_prod
  条件: (hμ : 可积 id μ) (hν : 可积 id ν)
  证明: integral_continuousLinearMap_prod' (ContinuousLinearMap.integrable_comp _ hμ)
    (ContinuousLinearMap.integrable_comp _ hν)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integrable_comp, integrable_comp, integral_continuousLinearMap_prod
-/
lemma integral_continuousLinearMap_prod (hμ : Integrable id μ) (hν : Integrable id ν) :
    ∫ p, L p ∂(μ.prod ν) = ∫ x, L.comp (.inl Real E F) x ∂μ + ∫ y, L.comp (.inr Real E F) y ∂ν :=
  integral_continuousLinearMap_prod' (ContinuousLinearMap.integrable_comp _ hμ)
    (ContinuousLinearMap.integrable_comp _ hν)

end ContinuousLinearMap

section

variable {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]

/--
lemma `integral_integral_swap_of_hasCompactSupport` / 引理 `integral_integral_swap_of_hasCompactSupport`

English:
lemma integral_integral_swap_of_hasCompactSupport
  proof: by
  let U := Prod.fst '' (tsupport f.uncurry)
  have : Fact (μ U < ∞) := ⟨(IsCompact.image h'f continuous_fst).measure_lt_top⟩
  let V := Prod.snd '' (tsupport f.uncurry)
  have : Fact (ν V < ∞) := ⟨(IsCompact.image h'f continuous_snd).measure_lt_top⟩
  calc
  ∫ x, (∫ y, f x y ∂ν) ∂μ = ∫ x, (∫ y in V, f x y ∂ν) ∂μ := by
    congr 1 with x
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
    contrapose! hy
    have : (x, y) in Function.support f.uncurry := hy
    exact mem_image_of_mem _ (subset_tsupport _ this)
  _ = ∫ x in U, (∫ y in V, f x y ∂ν) ∂μ := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
    have : forall y, f x y = 0 := by
      intro y
      contrapose! hx
      have : (x, y) in Function.support f.uncurry := hx
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y in V, (∫ x in U, f x y ∂μ) ∂ν := by
    apply integral_integral_swap
    apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f.uncurry)).mp
    refine ⟨(h'f.stronglyMeasurable_of_prod hf).aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC⟩ : exists C, forall p, ‖f.uncurry p‖ <= C := hf.bounded_above_of_compact_support h'f
    exact .of_bounded (C := C) (.of_forall hC)
  _ = ∫ y, (∫ x in U, f x y ∂μ) ∂ν := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
    have : forall x, f x y = 0 := by
      intro x
      contrapose! hy
      have : (x, y) in Function.support f.uncurry := hy
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y, (∫ x, f x y ∂μ) ∂ν := by
    congr 1 with y
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    contrapose! hx
    have : (x, y) in Function.support f.uncurry := hx
    exact mem_image_of_mem _ (subset_tsupport _ this)

中文:
引理 integral_integral_swap_of_hasCompactSupport
  证明: by
  let U := Prod.fst '' (tsupport f.uncurry)
  have : Fact (μ U < ∞) := ⟨(IsCompact.image h'f continuous_fst).measure_lt_top⟩
  let V := Prod.snd '' (tsupport f.uncurry)
  have : Fact (ν V < ∞) := ⟨(IsCompact.image h'f continuous_snd).measure_lt_top⟩
  calc
  ∫ x, (∫ y, f x y ∂ν) ∂μ = ∫ x, (∫ y in V, f x y ∂ν) ∂μ := by
    congr 1 with x
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
    contrapose! hy
    have : (x, y) in Function.support f.uncurry := hy
    exact mem_image_of_mem _ (subset_tsupport _ this)
  _ = ∫ x in U, (∫ y in V, f x y ∂ν) ∂μ := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
    have : forall y, f x y = 0 := by
      intro y
      contrapose! hx
      have : (x, y) in Function.support f.uncurry := hx
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y in V, (∫ x in U, f x y ∂μ) ∂ν := by
    apply integral_integral_swap
    apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f.uncurry)).mp
    refine ⟨(h'f.stronglyMeasurable_of_prod hf).aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC⟩ : exists C, forall p, ‖f.uncurry p‖ <= C := hf.bounded_above_of_compact_support h'f
    exact .of_bounded (C := C) (.of_forall hC)
  _ = ∫ y, (∫ x in U, f x y ∂μ) ∂ν := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
    have : forall x, f x y = 0 := by
      intro x
      contrapose! hy
      have : (x, y) in Function.support f.uncurry := hy
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y, (∫ x, f x y ∂μ) ∂ν := by
    congr 1 with y
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    contrapose! hx
    have : (x, y) in Function.support f.uncurry := hx
    exact mem_image_of_mem _ (subset_tsupport _ this)

Depends on / 依赖: Function, Function.support, IsCompact, IsCompact.image, Prod.fst, Prod.snd, continuous_fst, continuous_snd, contrapose, f.uncurry, measure_lt_top, mem_image_of_mem, setIntegral_eq_integral_of_forall_compl_eq_zero, support, tsupport, uncurry
-/
lemma integral_integral_swap_of_hasCompactSupport
    {f : X -> Y -> E} (hf : Continuous f.uncurry) (h'f : HasCompactSupport f.uncurry)
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    ∫ x, (∫ y, f x y ∂ν) ∂μ = ∫ y, (∫ x, f x y ∂μ) ∂ν := by
  let U := Prod.fst '' (tsupport f.uncurry)
  have : Fact (μ U < ∞) := ⟨(IsCompact.image h'f continuous_fst).measure_lt_top⟩
  let V := Prod.snd '' (tsupport f.uncurry)
  have : Fact (ν V < ∞) := ⟨(IsCompact.image h'f continuous_snd).measure_lt_top⟩
  calc
  ∫ x, (∫ y, f x y ∂ν) ∂μ = ∫ x, (∫ y in V, f x y ∂ν) ∂μ := by
    congr 1 with x
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
    contrapose! hy
    have : (x, y) in Function.support f.uncurry := hy
    exact mem_image_of_mem _ (subset_tsupport _ this)
  _ = ∫ x in U, (∫ y in V, f x y ∂ν) ∂μ := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
    have : forall y, f x y = 0 := by
      intro y
      contrapose! hx
      have : (x, y) in Function.support f.uncurry := hx
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y in V, (∫ x in U, f x y ∂μ) ∂ν := by
    apply integral_integral_swap
    apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f.uncurry)).mp
    refine ⟨(h'f.stronglyMeasurable_of_prod hf).aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC⟩ : exists C, forall p, ‖f.uncurry p‖ <= C := hf.bounded_above_of_compact_support h'f
    exact .of_bounded (C := C) (.of_forall hC)
  _ = ∫ y, (∫ x in U, f x y ∂μ) ∂ν := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
    have : forall x, f x y = 0 := by
      intro x
      contrapose! hy
      have : (x, y) in Function.support f.uncurry := hy
      exact mem_image_of_mem _ (subset_tsupport _ this)
    simp [this]
  _ = ∫ y, (∫ x, f x y ∂μ) ∂ν := by
    congr 1 with y
    apply setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    contrapose! hx
    have : (x, y) in Function.support f.uncurry := hx
    exact mem_image_of_mem _ (subset_tsupport _ this)

end

end MeasureTheory
