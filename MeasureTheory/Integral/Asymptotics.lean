/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bounding of integrals by asymptotics

We establish integrability of `f` from `f = O(g)`.

## Main results

* `Asymptotics.IsBigO.integrableAtFilter`: If `f = O[l] g` on measurably generated `l`,
  `f` is strongly measurable at `l`, and `g` is integrable at `l`, then `f` is integrable at `l`.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_cocompact`: If `f` is locally integrable,
  and `f =O[cocompact] g` for some `g` integrable at `cocompact`, then `f` is integrable.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atBot_atTop`: If `f` is locally integrable,
  and `f =O[atBot] g`, `f =O[atTop] g'` for some `g`, `g'` integrable `atBot` and `atTop`
  respectively, then `f` is integrable.
* `MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant`:
  If `f` is locally integrable, `‖f(-x)‖ = ‖f(x)‖`, and `f =O[atTop] g` for some
  `g` integrable `atTop`, then `f` is integrable.
-/

public section

open Asymptotics MeasureTheory Set Filter

variable {α E F : Type*} [NormedAddCommGroup E] {f : α -> E} {g : α -> F} {a : α} {l : Filter α}

namespace Asymptotics

section Basic

variable [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}

/--
theorem `IsBigO.integrableAtFilter` / 定理 `IsBigO.integrableAtFilter`

English:
theorem IsBigO.integrableAtFilter
  statement: [IsMeasurablyGenerated l]
  proof: by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨s, hsl, hsm, hfg, hf, hg⟩ :=
    (hC.smallSets.and <| hfm.eventually.and hg.eventually).exists_measurable_mem_of_smallSets
  refine ⟨s, hsl, (hg.norm.const_mul C).mono hf ?_⟩
  refine (ae_restrict_mem hsm).mono fun x hx => ?_
  exact (hfg x hx).trans (le_abs

中文:
定理 IsBigO.integrableAtFilter
  结论: [IsMeasurablyGenerated l]
  证明: by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨s, hsl, hsm, hfg, hf, hg⟩ :=
    (hC.smallSets.and <| hfm.eventually.and hg.eventually).exists_measurable_mem_of_smallSets
  refine ⟨s, hsl, (hg.norm.const_mul C).mono hf ?_⟩
  refine (ae_restrict_mem hsm).mono fun x hx => ?_
  exact (hfg x hx).trans (le_abs

Depends on / 依赖: ae_restrict_mem, const_mul, eventually, exists_measurable_mem_of_smallSets, hC.smallSets.and, hf.bound, hfm.eventually.and, hg.eventually, hg.norm.const_mul, le_abs_self, smallSets
-/
theorem IsBigO.integrableAtFilter [IsMeasurablyGenerated l]
    (hf : f =O[l] g) (hfm : StronglyMeasurableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨s, hsl, hsm, hfg, hf, hg⟩ :=
    (hC.smallSets.and <| hfm.eventually.and hg.eventually).exists_measurable_mem_of_smallSets
  refine ⟨s, hsl, (hg.norm.const_mul C).mono hf ?_⟩
  refine (ae_restrict_mem hsm).mono fun x hx => ?_
  exact (hfg x hx).trans (le_abs_self _)

/--
theorem `IsBigO.integrable` / 定理 `IsBigO.integrable`

English:
theorem IsBigO.integrable
  statement: (hfm : AEStronglyMeasurable f μ)
  proof: by
  rewrite [← integrableAtFilter_top] at *
  exact hf.integrableAtFilter ⟨univ, univ_mem, hfm.restrict⟩ hg

中文:
定理 IsBigO.integrable
  结论: (hfm : AEStronglyMeasurable f μ)
  证明: by
  rewrite [← integrableAtFilter_top] at *
  exact hf.integrableAtFilter ⟨univ, univ_mem, hfm.restrict⟩ hg

Depends on / 依赖: hf.integrableAtFilter, hfm.restrict, integrableAtFilter, integrableAtFilter_top, restrict, rewrite, univ_mem
-/
theorem IsBigO.integrable (hfm : AEStronglyMeasurable f μ)
    (hf : f =O[⊤] g) (hg : Integrable g μ) : Integrable f μ := by
  rewrite [← integrableAtFilter_top] at *
  exact hf.integrableAtFilter ⟨univ, univ_mem, hfm.restrict⟩ hg

end Basic

variable {ι : Type*} [MeasurableSpace ι] {f : ι × α -> E} {s : Set ι} {μ : Measure ι}

/--
theorem `IsBigO.eventually_integrableOn` / 定理 `IsBigO.eventually_integrableOn`

English:
theorem IsBigO.eventually_integrableOn
  statement: [Norm F]
  proof: by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  obtain ⟨w, hwl, hw⟩ := hfm.exists_mem
  refine eventually_iff_exists_mem.mpr ⟨w inter v, inter_mem hwl hv, fun x hx => ?_⟩
  have : IsFiniteMeasure (μ.restrict s) := ⟨M

中文:
定理 IsBigO.eventually_integrableOn
  结论: [Norm F]
  证明: by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  obtain ⟨w, hwl, hw⟩ := hfm.exists_mem
  refine eventually_iff_exists_mem.mpr ⟨w inter v, inter_mem hwl hv, fun x hx => ?_⟩
  have : IsFiniteMeasure (μ.restrict s) := ⟨M

Depends on / 依赖: Filter, Filter.mem_prod_iff.mp, Integrable, Integrable.mono, IsFiniteMeasure, Measure, Measure.restrict_apply_univ, MeasureTheory, MeasureTheory.self_mem_ae_restrict, eventually_iff_exists_mem, eventually_iff_exists_mem.mpr, exists_mem, filter_upwards, hC.exists_mem, hf.bound, hfm.exists_mem, integrable_const, inter_mem, mem_prod_iff, restrict
-/
theorem IsBigO.eventually_integrableOn [Norm F]
    (hf : f =O[𝓟 s ×ˢ l] (g ∘ Prod.snd))
    (hfm : forallᶠ x in l, AEStronglyMeasurable (fun i => f (i, x)) (μ.restrict s))
    (hs : MeasurableSet s) (hμ : μ s < ⊤) :
    forallᶠ x in l, IntegrableOn (fun i => f (i, x)) s μ := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  obtain ⟨w, hwl, hw⟩ := hfm.exists_mem
  refine eventually_iff_exists_mem.mpr ⟨w inter v, inter_mem hwl hv, fun x hx => ?_⟩
  have : IsFiniteMeasure (μ.restrict s) := ⟨Measure.restrict_apply_univ s ▸ hμ⟩
  refine Integrable.mono' (integrable_const (C * ‖g x‖)) (hw x hx.1) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict hs]
  intro y hy
exact ht (y, x) huv ⟨hu hy, hx.2⟩

variable [NormedSpace Real E] [NormedAddCommGroup F]

/--
theorem `IsBigO.set_integral_isBigO` / 定理 `IsBigO.set_integral_isBigO`

English:
theorem IsBigO.set_integral_isBigO
  given: (hf : f =O[𝓟 s ×ˢ l] (g ∘ Prod.snd)) (hμ : μ s < ⊤)
  proof: by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C * μ.real s, eventually_iff_exists_mem.mpr ⟨v, hv, fun x hx => ?_⟩⟩
  calc
    _ <= C * ‖g x‖ * μ.real s :=
norm_setIntegral_le_of_norm_le_const hμ fun

中文:
定理 IsBigO.set_integral_isBigO
  条件: (hf : f =O[𝓟 s ×ˢ l] (g ∘ Prod.snd)) (hμ : μ s < ⊤)
  证明: by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C * μ.real s, eventually_iff_exists_mem.mpr ⟨v, hv, fun x hx => ?_⟩⟩
  calc
    _ <= C * ‖g x‖ * μ.real s :=
norm_setIntegral_le_of_norm_le_const hμ fun

Depends on / 依赖: eventually_iff_exists_mem, eventually_iff_exists_mem.mpr, exists_mem, hC.exists_mem, hf.bound, isBigO_iff, isBigO_iff.mpr, mem_prod_iff, mem_prod_iff.mp, norm_setIntegral_le_of_norm_le_const
-/
theorem IsBigO.set_integral_isBigO (hf : f =O[𝓟 s ×ˢ l] (g ∘ Prod.snd)) (hμ : μ s < ⊤) :
    (fun x => ∫ i in s, f (i, x) ∂μ) =O[l] g := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C * μ.real s, eventually_iff_exists_mem.mpr ⟨v, hv, fun x hx => ?_⟩⟩
  calc
    _ <= C * ‖g x‖ * μ.real s :=
norm_setIntegral_le_of_norm_le_const hμ fun y hy => ht (y, x) huv ⟨hu hy, hx⟩
    _ = _ := by ring

end Asymptotics

variable [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup F]

namespace MeasureTheory

/--
theorem `LocallyIntegrable.integrable_of_isBigO_cocompact` / 定理 `LocallyIntegrable.integrable_of_isBigO_cocompact`

English:
theorem LocallyIntegrable.integrable_of_isBigO_cocompact
  statement: [IsMeasurablyGenerated (cocompact α)]
  proof: by
  refine integrable_iff_integrableAtFilter_cocompact.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

中文:
定理 LocallyIntegrable.integrable_of_isBigO_cocompact
  结论: [IsMeasurablyGenerated (cocompact α)]
  证明: by
  refine integrable_iff_integrableAtFilter_cocompact.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

Depends on / 依赖: aestronglyMeasurable, hf.aestronglyMeasurable.stronglyMeasurableAtFilter, ho.integrableAtFilter, integrableAtFilter, integrable_iff_integrableAtFilter_cocompact, integrable_iff_integrableAtFilter_cocompact.mpr, stronglyMeasurableAtFilter
-/
theorem LocallyIntegrable.integrable_of_isBigO_cocompact [IsMeasurablyGenerated (cocompact α)]
    (hf : LocallyIntegrable f μ) (ho : f =O[cocompact α] g)
    (hg : IntegrableAtFilter g (cocompact α) μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_cocompact.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

section LinearOrder

variable [LinearOrder α] [CompactIccSpace α] {g' : α -> F}

/--
theorem `LocallyIntegrable.integrable_of_isBigO_atBot_atTop` / 定理 `LocallyIntegrable.integrable_of_isBigO_atBot_atTop`

English:
theorem LocallyIntegrable.integrable_of_isBigO_atBot_atTop
  proof: by
  refine integrable_iff_integrableAtFilter_atBot_atTop.mpr
    ⟨⟨ho.integrableAtFilter ?_ hg, ho'.integrableAtFilter ?_ hg'⟩, hf⟩
  all_goals exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

中文:
定理 LocallyIntegrable.integrable_of_isBigO_atBot_atTop
  证明: by
  refine integrable_iff_integrableAtFilter_atBot_atTop.mpr
    ⟨⟨ho.integrableAtFilter ?_ hg, ho'.integrableAtFilter ?_ hg'⟩, hf⟩
  all_goals exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

Depends on / 依赖: IsMeasurablyGenerated
-/
theorem LocallyIntegrable.integrable_of_isBigO_atBot_atTop
    [IsMeasurablyGenerated (atBot (α := α))] [IsMeasurablyGenerated (atTop (α := α))]
    (hf : LocallyIntegrable f μ)
    (ho : f =O[atBot] g) (hg : IntegrableAtFilter g atBot μ)
    (ho' : f =O[atTop] g') (hg' : IntegrableAtFilter g' atTop μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_atBot_atTop.mpr
    ⟨⟨ho.integrableAtFilter ?_ hg, ho'.integrableAtFilter ?_ hg'⟩, hf⟩
  all_goals exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

/--
theorem `LocallyIntegrableOn.integrableOn_of_isBigO_atBot` / 定理 `LocallyIntegrableOn.integrableOn_of_isBigO_atBot`

English:
theorem LocallyIntegrableOn.integrableOn_of_isBigO_atBot
  statement: [IsMeasurablyGenerated (atBot (α := α))]
  proof: by
  refine integrableOn_Iic_iff_integrableAtFilter_atBot.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact ⟨Iic a, Iic_mem_atBot a, hf.aestronglyMeasurable⟩

中文:
定理 LocallyIntegrableOn.integrableOn_of_isBigO_atBot
  结论: [IsMeasurablyGenerated (atBot (α := α))]
  证明: by
  refine integrableOn_Iic_iff_integrableAtFilter_atBot.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact ⟨Iic a, Iic_mem_atBot a, hf.aestronglyMeasurable⟩
-/
theorem LocallyIntegrableOn.integrableOn_of_isBigO_atBot [IsMeasurablyGenerated (atBot (α := α))]
    (hf : LocallyIntegrableOn f (Iic a) μ) (ho : f =O[atBot] g)
    (hg : IntegrableAtFilter g atBot μ) : IntegrableOn f (Iic a) μ := by
  refine integrableOn_Iic_iff_integrableAtFilter_atBot.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact ⟨Iic a, Iic_mem_atBot a, hf.aestronglyMeasurable⟩

/--
theorem `LocallyIntegrableOn.integrableOn_of_isBigO_atTop` / 定理 `LocallyIntegrableOn.integrableOn_of_isBigO_atTop`

English:
theorem LocallyIntegrableOn.integrableOn_of_isBigO_atTop
  statement: [IsMeasurablyGenerated (atTop (α := α))]
  proof: by
  refine integrableOn_Ici_iff_integrableAtFilter_atTop.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact ⟨Ici a, Ici_mem_atTop a, hf.aestronglyMeasurable⟩

中文:
定理 LocallyIntegrableOn.integrableOn_of_isBigO_atTop
  结论: [IsMeasurablyGenerated (atTop (α := α))]
  证明: by
  refine integrableOn_Ici_iff_integrableAtFilter_atTop.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact ⟨Ici a, Ici_mem_atTop a, hf.aestronglyMeasurable⟩
-/
theorem LocallyIntegrableOn.integrableOn_of_isBigO_atTop [IsMeasurablyGenerated (atTop (α := α))]
    (hf : LocallyIntegrableOn f (Ici a) μ) (ho : f =O[atTop] g)
    (hg : IntegrableAtFilter g atTop μ) : IntegrableOn f (Ici a) μ := by
  refine integrableOn_Ici_iff_integrableAtFilter_atTop.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact ⟨Ici a, Ici_mem_atTop a, hf.aestronglyMeasurable⟩

/--
theorem `LocallyIntegrable.integrable_of_isBigO_atBot` / 定理 `LocallyIntegrable.integrable_of_isBigO_atBot`

English:
theorem LocallyIntegrable.integrable_of_isBigO_atBot
  statement: [IsMeasurablyGenerated (atBot (α := α))]
  proof: by
  refine integrable_iff_integrableAtFilter_atBot.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

中文:
定理 LocallyIntegrable.integrable_of_isBigO_atBot
  结论: [IsMeasurablyGenerated (atBot (α := α))]
  证明: by
  refine integrable_iff_integrableAtFilter_atBot.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter
-/
theorem LocallyIntegrable.integrable_of_isBigO_atBot [IsMeasurablyGenerated (atBot (α := α))]
    [OrderTop α] (hf : LocallyIntegrable f μ) (ho : f =O[atBot] g)
    (hg : IntegrableAtFilter g atBot μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_atBot.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

/--
theorem `LocallyIntegrable.integrable_of_isBigO_atTop` / 定理 `LocallyIntegrable.integrable_of_isBigO_atTop`

English:
theorem LocallyIntegrable.integrable_of_isBigO_atTop
  statement: [IsMeasurablyGenerated (atTop (α := α))]
  proof: by
  refine integrable_iff_integrableAtFilter_atTop.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

中文:
定理 LocallyIntegrable.integrable_of_isBigO_atTop
  结论: [IsMeasurablyGenerated (atTop (α := α))]
  证明: by
  refine integrable_iff_integrableAtFilter_atTop.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter
-/
theorem LocallyIntegrable.integrable_of_isBigO_atTop [IsMeasurablyGenerated (atTop (α := α))]
    [OrderBot α] (hf : LocallyIntegrable f μ) (ho : f =O[atTop] g)
    (hg : IntegrableAtFilter g atTop μ) : Integrable f μ := by
  refine integrable_iff_integrableAtFilter_atTop.mpr ⟨ho.integrableAtFilter ?_ hg, hf⟩
  exact hf.aestronglyMeasurable.stronglyMeasurableAtFilter

end LinearOrder

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [CompactIccSpace α]

/--
theorem `LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant` / 定理 `LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant`

English:
theorem LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
  proof: by
  have h_int := (hf.locallyIntegrableOn (Ici 0)).integrableOn_of_isBigO_atTop ho hg
  rw [← integrableOn_univ]; rw [← Iic_union_Ici_of_le le_rfl]; rw [integrableOn_union]
  refine ⟨?_, h_int⟩
  have h_map_neg : (μ.restrict (Ici 0)).map Neg.neg = μ.restrict (Iic 0) := by
    conv => rhs; rw [← Mea

中文:
定理 LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
  证明: by
  have h_int := (hf.locallyIntegrableOn (Ici 0)).integrableOn_of_isBigO_atTop ho hg
  rw [← integrableOn_univ]; rw [← Iic_union_Ici_of_le le_rfl]; rw [integrableOn_union]
  refine ⟨?_, h_int⟩
  have h_map_neg : (μ.restrict (Ici 0)).map Neg.neg = μ.restrict (Iic 0) := by
    conv => rhs; rw [← Mea

Depends on / 依赖: IsNegInvariant, MeasurableNeg
-/
theorem LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    [IsMeasurablyGenerated (atTop (α := α))] [MeasurableNeg α] [μ.IsNegInvariant]
    (hf : LocallyIntegrable f μ) (hsymm : norm ∘ f =ᵐ[μ] norm ∘ f ∘ Neg.neg) (ho : f =O[atTop] g)
    (hg : IntegrableAtFilter g atTop μ) : Integrable f μ := by
  have h_int := (hf.locallyIntegrableOn (Ici 0)).integrableOn_of_isBigO_atTop ho hg
  rw [← integrableOn_univ]; rw [← Iic_union_Ici_of_le le_rfl]; rw [integrableOn_union]
  refine ⟨?_, h_int⟩
  have h_map_neg : (μ.restrict (Ici 0)).map Neg.neg = μ.restrict (Iic 0) := by
    conv => rhs; rw [← Measure.map_neg_eq_self μ, measurableEmbedding_neg.restrict_map]
    simp
  rw [IntegrableOn]; rw [← h_map_neg]; rw [measurableEmbedding_neg.integrable_map_iff]
  refine h_int.congr' ?_ hsymm.restrict
  refine AEStronglyMeasurable.comp_aemeasurable ?_ measurable_neg.aemeasurable
  exact h_map_neg ▸ hf.aestronglyMeasurable.restrict

end LinearOrderedAddCommGroup

end MeasureTheory
