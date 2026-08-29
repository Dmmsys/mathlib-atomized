/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Results about strongly measurable functions

In measure theory it is often assumed that some space is a `PolishSpace`, i.e. a separable and
completely metrizable topological space, because it ensures a nice interaction between the topology
and the measurable space structure. Moreover a strongly measurable function whose codomain is a
metric space is measurable and has a separable range
(see `stronglyMeasurable_iff_measurable_separable`). Therefore if the codomain is also complete,
by corestricting the function to the closure of its range, some results about measurable functions
can be extended to strongly measurable functions without assuming separability on the codomain.
The purpose of this file is to collect those results.
-/

public section

open Filter MeasureTheory Set TopologicalSpace

open scoped Topology

variable {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [Countable ι] {l : Filter ι}
  [l.IsCountablyGenerated] {f : ι -> X -> E}

namespace MeasureTheory.StronglyMeasurable

/--
theorem `measurableSet_exists_tendsto` / 定理 `measurableSet_exists_tendsto`

English:
theorem measurableSet_exists_tendsto
  statement: [IsCompletelyPseudoMetrizableSpace E]
  proof: by
  obtain rfl | hl := eq_or_neBot l
  · simp_all
  borelize E
  let := upgradeIsCompletelyPseudoMetrizable E
  let s := closure (⋃ i, range (f i))
  have : SecondCountableTopology s := @UniformSpace.secondCountable_of_separable s _ _
    (IsSeparable.iUnion (fun i => (hf i).isSeparable_range)).clo

中文:
定理 measurableSet_exists_tendsto
  结论: [IsCompletelyPseudoMetrizableSpace E]
  证明: by
  obtain rfl | hl := eq_or_neBot l
  · simp_all
  borelize E
  let := upgradeIsCompletelyPseudoMetrizable E
  let s := closure (⋃ i, range (f i))
  have : SecondCountableTopology s := @UniformSpace.secondCountable_of_separable s _ _
    (IsSeparable.iUnion (fun i => (hf i).isSeparable_range)).clo

Depends on / 依赖: IsCompletelyPseudoMetrizableSpace, IsSeparable, IsSeparable.iUnion, Measurable, SecondCountableTopology, UniformSpace, UniformSpace.secondCountable_of_separable, borelize, closure, closure.separableSpace, eq_or_neBot, iUnion, isClosed_closure, isClosed_closure.isCompletelyPseudoMetrizableSpace, isCompletelyPseudoMetrizableSpace, isSeparable_range, mem_iUnion, secondCountable_of_separable, separableSpace, subset_closure
-/
theorem measurableSet_exists_tendsto [IsCompletelyPseudoMetrizableSpace E]
    (hf : forall i, StronglyMeasurable (f i)) :
    MeasurableSet {x | exists c, Tendsto (f · x) l (𝓝 c)} := by
  obtain rfl | hl := eq_or_neBot l
  · simp_all
  borelize E
  let := upgradeIsCompletelyPseudoMetrizable E
  let s := closure (⋃ i, range (f i))
  have : SecondCountableTopology s := @UniformSpace.secondCountable_of_separable s _ _
    (IsSeparable.iUnion (fun i => (hf i).isSeparable_range)).closure.separableSpace
  have : IsCompletelyPseudoMetrizableSpace s := isClosed_closure.isCompletelyPseudoMetrizableSpace
let g i x : s := ⟨f i x, subset_closure mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩⟩
  have mg i : Measurable (g i) := (hf i).measurable.subtype_mk
  convert! MeasureTheory.measurableSet_exists_tendsto (l := l) mg with x
  refine ⟨fun ⟨c, hc⟩ => ⟨⟨c, ?_⟩, tendsto_subtype_rng.2 hc⟩,
    fun ⟨c, hc⟩ => ⟨c, tendsto_subtype_rng.1 hc⟩⟩
  exact mem_closure_of_tendsto hc (Eventually.of_forall fun i => mem_iUnion.2 ⟨i, ⟨x, rfl⟩⟩)

/--
theorem `limUnder` / 定理 `limUnder`

English:
theorem limUnder
  statement: [hE : Nonempty E] [IsCompletelyMetrizableSpace E]
  proof: by
  obtain rfl | hl := eq_or_neBot l
  · simpa [limUnder, Filter.map_bot] using stronglyMeasurable_const
  let e := Classical.choice hE
  let conv := {x | exists c, Tendsto (f · x) l (𝓝 c)}
  have mconv : MeasurableSet conv := StronglyMeasurable.measurableSet_exists_tendsto hf
  have hconv : Strong

中文:
定理 limUnder
  结论: [hE : Nonempty E] [IsCompletelyMetrizableSpace E]
  证明: by
  obtain rfl | hl := eq_or_neBot l
  · simpa [limUnder, Filter.map_bot] using stronglyMeasurable_const
  let e := Classical.choice hE
  let conv := {x | exists c, Tendsto (f · x) l (𝓝 c)}
  have mconv : MeasurableSet conv := StronglyMeasurable.measurableSet_exists_tendsto hf
  have hconv : Strong
-/
protected theorem limUnder [hE : Nonempty E] [IsCompletelyMetrizableSpace E]
    (hf : forall i, StronglyMeasurable (f i)) :
    StronglyMeasurable (fun x => limUnder l (f · x)) := by
  obtain rfl | hl := eq_or_neBot l
  · simpa [limUnder, Filter.map_bot] using stronglyMeasurable_const
  let e := Classical.choice hE
  let conv := {x | exists c, Tendsto (f · x) l (𝓝 c)}
  have mconv : MeasurableSet conv := StronglyMeasurable.measurableSet_exists_tendsto hf
  have hconv : StronglyMeasurable (fun x : conv => limUnder l (f · x)) := by
    refine stronglyMeasurable_of_tendsto l
      (fun i => (hf i).comp_measurable measurable_subtype_coe) ?_
    refine tendsto_pi_nhds.2 fun x => ?_
    obtain ⟨c, hc⟩ := x.2
    rwa [hc.limUnder_eq]
  have : (fun x => limUnder l (f · x)) = ((↑) : conv -> X).extend
      (fun x => limUnder l (f · x)) (fun _ => e) := by
    ext x
    by_cases hx : x in conv
    · rw [Function.extend_val_apply hx]
    · rw [Function.extend_val_apply' hx, limUnder_of_not_tendsto hx]
  rw [this]
  exact (MeasurableEmbedding.subtype_coe mconv).stronglyMeasurable_extend hconv
    stronglyMeasurable_const

end MeasureTheory.StronglyMeasurable

namespace MeasureTheory

variable {X E ι : Type*} [MeasurableSpace X] [CommMonoid E] [TopologicalSpace E]

section

variable [ContinuousMul E] {L : SummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]

/-- The infinite product of strongly measurable functions is measurable, `HasProd` version. -/
@[to_additive (attr := fun_prop)
/-- The infinite sum of strongly measurable functions is measurable, `HasSum` version. -/]
/--
theorem `StronglyMeasurable.hasProd` / 定理 `StronglyMeasurable.hasProd`

English:
theorem StronglyMeasurable.hasProd
  statement: [PseudoMetrizableSpace E] {f : ι -> X -> E} {g : X -> E}
  proof: by
  refine stronglyMeasurable_of_tendsto L.filter ?_ (tendsto_pi_nhds.mpr h')
  fun_prop

中文:
定理 StronglyMeasurable.hasProd
  结论: [PseudoMetrizableSpace E] {f : ι -> X -> E} {g : X -> E}
  证明: by
  refine stronglyMeasurable_of_tendsto L.filter ?_ (tendsto_pi_nhds.mpr h')
  fun_prop

Depends on / 依赖: L.filter, filter, fun_prop, stronglyMeasurable_of_tendsto, tendsto_pi_nhds, tendsto_pi_nhds.mpr
-/
theorem StronglyMeasurable.hasProd [PseudoMetrizableSpace E] {f : ι -> X -> E} {g : X -> E}
    (h : forall i : ι, StronglyMeasurable (f i)) (h' : forall x, HasProd (fun i => f i x) (g x) L) :
    StronglyMeasurable g := by
  refine stronglyMeasurable_of_tendsto L.filter ?_ (tendsto_pi_nhds.mpr h')
  fun_prop

variable [IsCompletelyPseudoMetrizableSpace E] [Countable ι]

/-- The infinite product of strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The infinite sum of strongly measurable functions is measurable. -/]
/--
theorem `StronglyMeasurable.tprod` / 定理 `StronglyMeasurable.tprod`

English:
theorem StronglyMeasurable.tprod
  given: {f : ι -> X -> E} (h : forall i : ι, StronglyMeasurable (f i))
  proof: by
  let E := { x | Multipliable (f · x) L }
  have hE : MeasurableSet E := StronglyMeasurable.measurableSet_exists_tendsto (by fun_prop)
  have h0 : (Eᶜ.domRestrict fun x => ∏'[L] i, f i x) = fun _ => 1 :=
    funext fun ⟨x, hx⟩ => tprod_eq_one_of_not_multipliable hx
  refine stronglyMeasurable_of_

中文:
定理 StronglyMeasurable.tprod
  条件: {f : ι -> X -> E} (h : 对任意 i : ι, StronglyMeasurable (f i))
  证明: by
  let E := { x | Multipliable (f · x) L }
  have hE : MeasurableSet E := StronglyMeasurable.measurableSet_exists_tendsto (by fun_prop)
  have h0 : (Eᶜ.domRestrict fun x => ∏'[L] i, f i x) = fun _ => 1 :=
    funext fun ⟨x, hx⟩ => tprod_eq_one_of_not_multipliable hx
  refine stronglyMeasurable_of_

Depends on / 依赖: L.filter, MeasurableSet, Multipliable, StronglyMeasurable, StronglyMeasurable.measurableSet_exists_tendsto, domRestrict, filter, fun_prop, hasProd, measurableSet_exists_tendsto, stronglyMeasurable_const, stronglyMeasurable_of_restrict_of_restrict_compl, stronglyMeasurable_of_tendsto, tendsto_pi_nhds, tendsto_pi_nhds.mpr, tprod_eq_one_of_not_multipliable
-/
theorem StronglyMeasurable.tprod {f : ι -> X -> E} (h : forall i : ι, StronglyMeasurable (f i)) :
    StronglyMeasurable (fun x => ∏'[L] i : ι, f i x) := by
  let E := { x | Multipliable (f · x) L }
  have hE : MeasurableSet E := StronglyMeasurable.measurableSet_exists_tendsto (by fun_prop)
  have h0 : (Eᶜ.domRestrict fun x => ∏'[L] i, f i x) = fun _ => 1 :=
    funext fun ⟨x, hx⟩ => tprod_eq_one_of_not_multipliable hx
  refine stronglyMeasurable_of_restrict_of_restrict_compl hE ?_ (h0 ▸ stronglyMeasurable_const)
  refine stronglyMeasurable_of_tendsto L.filter ?_ (tendsto_pi_nhds.mpr fun e => e.2.hasProd)
  fun_prop

/-- The product of almost everywhere strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of almost everywhere strongly measurable functions is measurable. -/]
/--
theorem `AEStronglyMeasurable.tprod` / 定理 `AEStronglyMeasurable.tprod`

English:
theorem AEStronglyMeasurable.tprod
  statement: {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
  proof: by
  choose g hg_meas hg_eq_f using h
  use (fun x => ∏'[L] i, g i x), StronglyMeasurable.tprod hg_meas
  filter_upwards [ae_all_iff.mpr hg_eq_f] with x h_eq using tprod_congr h_eq

中文:
定理 AEStronglyMeasurable.tprod
  结论: {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
  证明: by
  choose g hg_meas hg_eq_f using h
  use (fun x => ∏'[L] i, g i x), StronglyMeasurable.tprod hg_meas
  filter_upwards [ae_all_iff.mpr hg_eq_f] with x h_eq using tprod_congr h_eq

Depends on / 依赖: StronglyMeasurable, StronglyMeasurable.tprod, ae_all_iff, ae_all_iff.mpr, filter_upwards, h_eq, hg_eq_f, hg_meas, tprod_congr
-/
theorem AEStronglyMeasurable.tprod {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
    (h : forall i : ι, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x => ∏'[L] i : ι, f i x) μ := by
  choose g hg_meas hg_eq_f using h
  use (fun x => ∏'[L] i, g i x), StronglyMeasurable.tprod hg_meas
  filter_upwards [ae_all_iff.mpr hg_eq_f] with x h_eq using tprod_congr h_eq

end

section

variable [PseudoMetrizableSpace E] [ContinuousMul E]
  {L : SummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]

/-- The product of strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of strongly measurable functions is measurable. -/]
/--
theorem `StronglyMeasurable.tprod'` / 定理 `StronglyMeasurable.tprod'`

English:
theorem StronglyMeasurable.tprod'
  given: {f : ι -> X -> E} (h : forall i : ι, StronglyMeasurable (f i))
  proof: by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact stronglyMeasurable_one
  · refine Finset.stronglyMeasurable_prod _ (fun _ _ => ?_)
    rw [Set.mulIndicator]
    split_ifs
    · fun_prop
    · exact stronglyMeasurable_one
  · exact stronglyMeasurable_of_tendsto L.filter (

中文:
定理 StronglyMeasurable.tprod'
  条件: {f : ι -> X -> E} (h : 对任意 i : ι, StronglyMeasurable (f i))
  证明: by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact stronglyMeasurable_one
  · refine Finset.stronglyMeasurable_prod _ (fun _ _ => ?_)
    rw [Set.mulIndicator]
    split_ifs
    · fun_prop
    · exact stronglyMeasurable_one
  · exact stronglyMeasurable_of_tendsto L.filter (

Depends on / 依赖: Finset, Finset.stronglyMeasurable_prod, L.filter, Set.mulIndicator, any_goals, choose_spec, filter, finprod_def, fun_prop, hm.choose_spec, mulIndicator, split_ifs, stronglyMeasurable_of_tendsto, stronglyMeasurable_one, stronglyMeasurable_prod, tprod_def
-/
theorem StronglyMeasurable.tprod' {f : ι -> X -> E} (h : forall i : ι, StronglyMeasurable (f i)) :
    StronglyMeasurable (∏'[L] i : ι, f i) := by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact stronglyMeasurable_one
  · refine Finset.stronglyMeasurable_prod _ (fun _ _ => ?_)
    rw [Set.mulIndicator]
    split_ifs
    · fun_prop
    · exact stronglyMeasurable_one
  · exact stronglyMeasurable_of_tendsto L.filter (by fun_prop) hm.choose_spec

/-- The product of almost everywhere strongly measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of almost everywhere strongly measurable functions is measurable. -/]
/--
theorem `AEStronglyMeasurable.tprod'` / 定理 `AEStronglyMeasurable.tprod'`

English:
theorem AEStronglyMeasurable.tprod'
  statement: {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
  proof: by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact aestronglyMeasurable_one
  · refine Finset.aestronglyMeasurable_prod _ (fun _ _ => ?_)
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · apply aestronglyMeasurable_of_tendsto_ae L.filter (f := fun s => ∏ i in s, f i)

中文:
定理 AEStronglyMeasurable.tprod'
  结论: {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
  证明: by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact aestronglyMeasurable_one
  · refine Finset.aestronglyMeasurable_prod _ (fun _ _ => ?_)
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · apply aestronglyMeasurable_of_tendsto_ae L.filter (f := fun s => ∏ i in s, f i)

Depends on / 依赖: Finset, Finset.aestronglyMeasurable_prod, L.filter, Set.mulIndicator, aestronglyMeasurable_of_tendsto_ae, aestronglyMeasurable_one, aestronglyMeasurable_prod, any_goals, apply_nhds, choose_spec, filter, finprod_def, fun_prop, hm.choose_spec.apply_nhds, mulIndicator, of_forall, split_ifs, tprod_def
-/
theorem AEStronglyMeasurable.tprod' {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
    (h : forall i : ι, AEStronglyMeasurable (f i) μ) : AEStronglyMeasurable (∏'[L] i : ι, f i) μ := by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact aestronglyMeasurable_one
  · refine Finset.aestronglyMeasurable_prod _ (fun _ _ => ?_)
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · apply aestronglyMeasurable_of_tendsto_ae L.filter (f := fun s => ∏ i in s, f i) (by fun_prop)
    exact .of_forall fun x => hm.choose_spec.apply_nhds x

end

end MeasureTheory
