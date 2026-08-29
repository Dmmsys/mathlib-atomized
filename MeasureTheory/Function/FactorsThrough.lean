/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Process.Filtration

/-!
# Factorization of a map from measurability

Consider `f : X → Y` and `g : X → Z` and assume that `g` is measurable with respect to the pullback
along `f`. Then `g` factors through `f`, which means that (if `Z` is nonempty)
there exists `h : Y → Z` such that `g = h ∘ f`.

If `Z` is completely metrizable, the factorization map `h` can be taken to be measurable.
This is the content of the [Doob-Dynkin lemma](https://en.wikipedia.org/wiki/Doob–Dynkin_lemma):
see `exists_eq_measurable_comp`.
-/

public section

namespace MeasureTheory

open Filter Filtration Set TopologicalSpace

open scoped Topology

variable {X Y Z : Type*} [mY : MeasurableSpace Y] {f : X -> Y} {g : X -> Z}

section FactorsThrough

/--
theorem `_root_.Measurable.factorsThrough` / 定理 `_root_.Measurable.factorsThrough`

English:
theorem _root_.Measurable.factorsThrough
  statement: [MeasurableSpace Z] [MeasurableSingletonClass Z]
  proof: by
  refine fun x₁ x₂ h => eq_of_mem_singleton ?_
  obtain ⟨s, -, hs⟩ := hg (measurableSet_singleton (g x₂))
  rw [← mem_preimage]; rw [← hs]; rw [mem_preimage]; rw [h]; rw [← mem_preimage]; rw [hs]; rw [mem_preimage]; rw [mem_singleton_iff]

中文:
定理 _root_.可测.factorsThrough
  结论: [可测空间 Z] [MeasurableSingleton类 Z]
  证明: by
  refine fun x₁ x₂ h => eq_of_mem_singleton ?_
  obtain ⟨s, -, hs⟩ := hg (measurableSet_singleton (g x₂))
  rw [← mem_preimage]; rw [← hs]; rw [mem_preimage]; rw [h]; rw [← mem_preimage]; rw [hs]; rw [mem_preimage]; rw [mem_singleton_iff]

Depends on / 依赖: eq_of_mem_singleton, measurableSet_singleton, mem_preimage, mem_singleton_iff
-/
theorem _root_.Measurable.factorsThrough [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hg : Measurable[mY.comap f] g) : g.FactorsThrough f := by
  refine fun x₁ x₂ h => eq_of_mem_singleton ?_
  obtain ⟨s, -, hs⟩ := hg (measurableSet_singleton (g x₂))
  rw [← mem_preimage]; rw [← hs]; rw [mem_preimage]; rw [h]; rw [← mem_preimage]; rw [hs]; rw [mem_preimage]; rw [mem_singleton_iff]

/--
theorem `StronglyMeasurable.factorsThrough` / 定理 `StronglyMeasurable.factorsThrough`

English:
theorem StronglyMeasurable.factorsThrough
  statement: [TopologicalSpace Z]
  proof: by
  borelize Z
  exact hg.measurable.factorsThrough

中文:
定理 StronglyMeasurable.factorsThrough
  结论: [拓扑空间 Z]
  证明: by
  borelize Z
  exact hg.measurable.factorsThrough

Depends on / 依赖: borelize, factorsThrough, hg.measurable.factorsThrough, measurable
-/
theorem StronglyMeasurable.factorsThrough [TopologicalSpace Z]
    [PseudoMetrizableSpace Z] [T1Space Z] (hg : StronglyMeasurable[mY.comap f] g) :
    g.FactorsThrough f := by
  borelize Z
  exact hg.measurable.factorsThrough

set_option backward.isDefEq.respectTransparency false in
/--
theorem `StronglyMeasurable.exists_eq_measurable_comp` / 定理 `StronglyMeasurable.exists_eq_measurable_comp`

English:
theorem StronglyMeasurable.exists_eq_measurable_comp
  statement: [Nonempty Z] [TopologicalSpace Z]
  proof: by
  let mX : MeasurableSpace X := mY.comap f
  induction g, hg using StronglyMeasurable.induction' with
  | const z => exact ⟨fun _ => z, stronglyMeasurable_const, rfl⟩
  | @pcw g₁ g₂ s hg₁ hg₂ hs h₁ h₂ =>
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨h₁, mh₁, rfl⟩ := h₁
    obtain ⟨h₂, mh₂, rfl⟩ := h₂
    classical
    exact ⟨t.piecewise h₁ h₂, mh₁.piecewise ht mh₂, by rw [piecewise_comp]⟩
  | @lim g i hg hi h₁ h₂ =>
    choose h mh hh using h₁
    refine ⟨fun y => limUnder atTop (h · y), StronglyMeasurable.limUnder mh, ?_⟩
    ext x
    rw [Function.comp_apply]; rw [Tendsto.limUnder_eq]
    simp_all

中文:
定理 StronglyMeasurable.存在_eq_measurable_comp
  结论: [非空 Z] [拓扑空间 Z]
  证明: by
  let mX : MeasurableSpace X := mY.comap f
  induction g, hg using StronglyMeasurable.induction' with
  | const z => exact ⟨fun _ => z, stronglyMeasurable_const, rfl⟩
  | @pcw g₁ g₂ s hg₁ hg₂ hs h₁ h₂ =>
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨h₁, mh₁, rfl⟩ := h₁
    obtain ⟨h₂, mh₂, rfl⟩ := h₂
    classical
    exact ⟨t.piecewise h₁ h₂, mh₁.piecewise ht mh₂, by rw [piecewise_comp]⟩
  | @lim g i hg hi h₁ h₂ =>
    choose h mh hh using h₁
    refine ⟨fun y => limUnder atTop (h · y), StronglyMeasurable.limUnder mh, ?_⟩
    ext x
    rw [Function.comp_apply]; rw [Tendsto.limUnder_eq]
    simp_all

Depends on / 依赖: MeasurableSpace, StronglyMeasurable, StronglyMeasurable.induction, StronglyMeasurable.limUnder, classical, limUnder, mY.comap, piecewise, piecewise_comp, stronglyMeasurable_const, t.piecewise
-/
theorem StronglyMeasurable.exists_eq_measurable_comp [Nonempty Z] [TopologicalSpace Z]
    [IsCompletelyMetrizableSpace Z] (hg : StronglyMeasurable[mY.comap f] g) :
    exists h : Y -> Z, StronglyMeasurable h ∧ g = h ∘ f := by
  let mX : MeasurableSpace X := mY.comap f
  induction g, hg using StronglyMeasurable.induction' with
  | const z => exact ⟨fun _ => z, stronglyMeasurable_const, rfl⟩
  | @pcw g₁ g₂ s hg₁ hg₂ hs h₁ h₂ =>
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨h₁, mh₁, rfl⟩ := h₁
    obtain ⟨h₂, mh₂, rfl⟩ := h₂
    classical
    exact ⟨t.piecewise h₁ h₂, mh₁.piecewise ht mh₂, by rw [piecewise_comp]⟩
  | @lim g i hg hi h₁ h₂ =>
    choose h mh hh using h₁
    refine ⟨fun y => limUnder atTop (h · y), StronglyMeasurable.limUnder mh, ?_⟩
    ext x
    rw [Function.comp_apply]; rw [Tendsto.limUnder_eq]
    simp_all

/--
theorem `_root_.Measurable.exists_eq_measurable_comp` / 定理 `_root_.Measurable.exists_eq_measurable_comp`

English:
theorem _root_.Measurable.exists_eq_measurable_comp
  statement: [Nonempty Z] [MeasurableSpace Z]
  proof: by
  let := upgradeStandardBorel Z
  obtain ⟨h, mh, hh⟩ := hg.stronglyMeasurable.exists_eq_measurable_comp
  exact ⟨h, mh.measurable, hh⟩

中文:
定理 _root_.可测.存在_eq_measurable_comp
  结论: [非空 Z] [可测空间 Z]
  证明: by
  let := upgradeStandardBorel Z
  obtain ⟨h, mh, hh⟩ := hg.stronglyMeasurable.exists_eq_measurable_comp
  exact ⟨h, mh.measurable, hh⟩

Depends on / 依赖: exists_eq_measurable_comp, hg.stronglyMeasurable.exists_eq_measurable_comp, measurable, mh.measurable, stronglyMeasurable, upgradeStandardBorel
-/
theorem _root_.Measurable.exists_eq_measurable_comp [Nonempty Z] [MeasurableSpace Z]
    [StandardBorelSpace Z] (hg : Measurable[mY.comap f] g) :
    exists h : Y -> Z, Measurable h ∧ g = h ∘ f := by
  let := upgradeStandardBorel Z
  obtain ⟨h, mh, hh⟩ := hg.stronglyMeasurable.exists_eq_measurable_comp
  exact ⟨h, mh.measurable, hh⟩

end FactorsThrough

variable {ι : Type*} {X : ι -> Type*} [forall i, MeasurableSpace (X i)] {f : (Π i, X i) -> Z}

section piLE

variable [Preorder ι] {i : ι}

/--
theorem `_root_.Measurable.dependsOn_of_piLE` / 定理 `_root_.Measurable.dependsOn_of_piLE`

English:
theorem _root_.Measurable.dependsOn_of_piLE
  statement: [MeasurableSpace Z] [MeasurableSingletonClass Z]
  proof: dependsOn_iff_factorsThrough.2 hf.factorsThrough

中文:
定理 _root_.可测.dependsOn_of_piLE
  结论: [可测空间 Z] [MeasurableSingleton类 Z]
  证明: dependsOn_iff_factorsThrough.2 hf.factorsThrough

Depends on / 依赖: dependsOn_iff_factorsThrough, factorsThrough, hf.factorsThrough
-/
theorem _root_.Measurable.dependsOn_of_piLE [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hf : Measurable[piLE i] f) : DependsOn f (Iic i) :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

/--
theorem `StronglyMeasurable.dependsOn_of_piLE` / 定理 `StronglyMeasurable.dependsOn_of_piLE`

English:
theorem StronglyMeasurable.dependsOn_of_piLE
  statement: [TopologicalSpace Z] [PseudoMetrizableSpace Z]
  proof: dependsOn_iff_factorsThrough.2 hf.factorsThrough

中文:
定理 StronglyMeasurable.dependsOn_of_piLE
  结论: [拓扑空间 Z] [PseudoMetrizable空间 Z]
  证明: dependsOn_iff_factorsThrough.2 hf.factorsThrough

Depends on / 依赖: dependsOn_iff_factorsThrough, factorsThrough, hf.factorsThrough
-/
theorem StronglyMeasurable.dependsOn_of_piLE [TopologicalSpace Z] [PseudoMetrizableSpace Z]
    [T1Space Z] (hf : StronglyMeasurable[piLE i] f) : DependsOn f (Iic i) :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

end piLE

section piFinset

variable {s : Finset ι}

/--
theorem `_root_.Measurable.dependsOn_of_piFinset` / 定理 `_root_.Measurable.dependsOn_of_piFinset`

English:
theorem _root_.Measurable.dependsOn_of_piFinset
  statement: [MeasurableSpace Z] [MeasurableSingletonClass Z]
  proof: dependsOn_iff_factorsThrough.2 hf.factorsThrough

中文:
定理 _root_.可测.dependsOn_of_piFinset
  结论: [可测空间 Z] [MeasurableSingleton类 Z]
  证明: dependsOn_iff_factorsThrough.2 hf.factorsThrough

Depends on / 依赖: dependsOn_iff_factorsThrough, factorsThrough, hf.factorsThrough
-/
theorem _root_.Measurable.dependsOn_of_piFinset [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hf : Measurable[piFinset s] f) : DependsOn f s :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

/--
theorem `StronglyMeasurable.dependsOn_of_piFinset` / 定理 `StronglyMeasurable.dependsOn_of_piFinset`

English:
theorem StronglyMeasurable.dependsOn_of_piFinset
  statement: [TopologicalSpace Z] [PseudoMetrizableSpace Z]
  proof: dependsOn_iff_factorsThrough.2 hf.factorsThrough

中文:
定理 StronglyMeasurable.dependsOn_of_piFinset
  结论: [拓扑空间 Z] [PseudoMetrizable空间 Z]
  证明: dependsOn_iff_factorsThrough.2 hf.factorsThrough

Depends on / 依赖: dependsOn_iff_factorsThrough, factorsThrough, hf.factorsThrough
-/
theorem StronglyMeasurable.dependsOn_of_piFinset [TopologicalSpace Z] [PseudoMetrizableSpace Z]
    [T1Space Z] (hf : StronglyMeasurable[piFinset s] f) : DependsOn f s :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

end piFinset

end MeasureTheory
