/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Measure spaces

The definition of a measure and a measure space are in `MeasureTheory.MeasureSpaceDef`, with
only a few basic properties. This file provides many more properties of these objects.
This separation allows the measurability tactic to import only the file `MeasureSpaceDef`, and to
be available in `MeasureSpace` (through `MeasurableSpace`).

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `Measure.ofMeasurable` and `OuterMeasure.toMeasure` are two important ways to define a measure.

## Implementation notes

Given `μ : Measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `Measure.ofMeasurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `OuterMeasure.toMeasure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generateFrom_of_iUnion`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of
  the more general `ext_of_generateFrom_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generateFrom_of_iUnion` using
  `C ∪ {univ}`, but is easier to work with.

A `MeasureSpace` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/

@[expose] public section

noncomputable section

open Set

open Filter hiding map

open Function MeasurableSpace Topology Filter ENNReal NNReal Interval MeasureTheory
open scoped symmDiff

variable {α β γ δ ι R R' : Type*}

namespace MeasureTheory

section

variable {m : MeasurableSpace α} {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}

/--
Instance `ae_isMeasurablyGenerated` / 实例 `ae_isMeasurablyGenerated`

English:
instance ae_isMeasurablyGenerated
  signature: : IsMeasurablyGenerated (ae μ)
  body: ⟨fun _s hs =>
    let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs
    ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩

中文:
实例 ae_isMeasurablyGenerated
  签名: : 是MeasurablyGenerated (ae μ)
  定义体: ⟨fun _s hs =>
    let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs
    ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩

Depends on / 依赖: compl_mem_ae_iff, compl_subset_comm, exists_measurable_superset_of_null, htm.compl
-/
instance ae_isMeasurablyGenerated : IsMeasurablyGenerated (ae μ) :=
  ⟨fun _s hs =>
    let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs
    ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩

/--
theorem `ae_uIoc_iff` / 定理 `ae_uIoc_iff`

English:
theorem ae_uIoc_iff
  given: [LinearOrder α] {a b : α} {P : α -> Prop}
  proof: by
  simp only [uIoc_eq_union, mem_union, or_imp, eventually_and]

中文:
定理 ae_uIoc_iff
  条件: [线性序 α] {a b : α} {P : α -> 命题}
  证明: by
  simp only [uIoc_eq_union, mem_union, or_imp, eventually_and]

Depends on / 依赖: eventually_and, mem_union, or_imp, uIoc_eq_union
-/
theorem ae_uIoc_iff [LinearOrder α] {a b : α} {P : α -> Prop} :
    (forallᵐ x ∂μ, x in Ι a b -> P x) ↔ (forallᵐ x ∂μ, x in Ioc a b -> P x) ∧ forallᵐ x ∂μ, x in Ioc b a -> P x := by
  simp only [uIoc_eq_union, mem_union, or_imp, eventually_and]

/--
theorem `measure_union` / 定理 `measure_union`

English:
theorem measure_union
  given: (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂)
  statement: μ (s₁ union s₂) = μ s₁ + μ s₂
  proof: measure_union₀ h.nullMeasurableSet hd.aedisjoint

中文:
定理 measure_union
  条件: (hd : Disjoint s₁ s₂) (h : 可测集 s₂)
  结论: μ (s₁ union s₂) = μ s₁ + μ s₂
  证明: measure_union₀ h.nullMeasurableSet hd.aedisjoint

Depends on / 依赖: aedisjoint, h.nullMeasurableSet, hd.aedisjoint, nullMeasurableSet
-/
theorem measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂ :=
  measure_union₀ h.nullMeasurableSet hd.aedisjoint

/--
theorem `measure_union'` / 定理 `measure_union'`

English:
theorem measure_union'
  given: (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁)
  statement: μ (s₁ union s₂) = μ s₁ + μ s₂
  proof: measure_union₀' h.nullMeasurableSet hd.aedisjoint

中文:
定理 measure_union'
  条件: (hd : Disjoint s₁ s₂) (h : 可测集 s₁)
  结论: μ (s₁ union s₂) = μ s₁ + μ s₂
  证明: measure_union₀' h.nullMeasurableSet hd.aedisjoint

Depends on / 依赖: aedisjoint, h.nullMeasurableSet, hd.aedisjoint, nullMeasurableSet
-/
theorem measure_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁) : μ (s₁ union s₂) = μ s₁ + μ s₂ :=
  measure_union₀' h.nullMeasurableSet hd.aedisjoint

/--
theorem `measure_inter_add_sdiff` / 定理 `measure_inter_add_sdiff`

English:
theorem measure_inter_add_sdiff
  given: (s : Set α) (ht : MeasurableSet t)
  statement: μ (s inter t) + μ (s \ t) = μ s
  proof: measure_inter_add_sdiff₀ _ ht.nullMeasurableSet

@[deprecated (since := "2026-06-03")] alias measure_inter_add_diff := measure_inter_add_sdiff

中文:
定理 measure_inter_add_sdiff
  条件: (s : 集合 α) (ht : 可测集 t)
  结论: μ (s inter t) + μ (s \ t) = μ s
  证明: measure_inter_add_sdiff₀ _ ht.nullMeasurableSet

@[deprecated (since := "2026-06-03")] alias measure_inter_add_diff := measure_inter_add_sdiff

Depends on / 依赖: ht.nullMeasurableSet, nullMeasurableSet
-/
theorem measure_inter_add_sdiff (s : Set α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s :=
  measure_inter_add_sdiff₀ _ ht.nullMeasurableSet

@[deprecated (since := "2026-06-03")] alias measure_inter_add_diff := measure_inter_add_sdiff

/--
theorem `measure_sdiff_add_inter` / 定理 `measure_sdiff_add_inter`

English:
theorem measure_sdiff_add_inter
  given: (s : Set α) (ht : MeasurableSet t)
  statement: μ (s \ t) + μ (s inter t) = μ s
  proof: (add_comm _ _).trans (measure_inter_add_sdiff s ht)

@[deprecated (since := "2026-06-03")] alias measure_diff_add_inter := measure_sdiff_add_inter

中文:
定理 measure_sdiff_add_inter
  条件: (s : 集合 α) (ht : 可测集 t)
  结论: μ (s \ t) + μ (s inter t) = μ s
  证明: (add_comm _ _).trans (measure_inter_add_sdiff s ht)

@[deprecated (since := "2026-06-03")] alias measure_diff_add_inter := measure_sdiff_add_inter

Depends on / 依赖: add_comm, measure_inter_add_sdiff
-/
theorem measure_sdiff_add_inter (s : Set α) (ht : MeasurableSet t) : μ (s \ t) + μ (s inter t) = μ s :=
  (add_comm _ _).trans (measure_inter_add_sdiff s ht)

@[deprecated (since := "2026-06-03")] alias measure_diff_add_inter := measure_sdiff_add_inter

/--
theorem `measure_sdiff_eq_top` / 定理 `measure_sdiff_eq_top`

English:
theorem measure_sdiff_eq_top
  given: (hs : μ s = ∞) (ht : μ t != ∞)
  statement: μ (s \ t) = ∞
  proof: by
  contrapose! hs
  exact ((measure_mono (subset_sdiff_union s t)).trans_lt
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs.lt_top, ht.lt_top⟩))).ne

@[deprecated (since := "2026-06-03")] alias measure_diff_eq_top := measure_sdiff_eq_top

中文:
定理 measure_sdiff_eq_top
  条件: (hs : μ s = ∞) (ht : μ t != ∞)
  结论: μ (s \ t) = ∞
  证明: by
  contrapose! hs
  exact ((measure_mono (subset_sdiff_union s t)).trans_lt
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs.lt_top, ht.lt_top⟩))).ne

@[deprecated (since := "2026-06-03")] alias measure_diff_eq_top := measure_sdiff_eq_top

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, add_lt_top, contrapose, hs.lt_top, ht.lt_top, lt_top, measure_mono, measure_union_le, subset_sdiff_union, trans_lt
-/
theorem measure_sdiff_eq_top (hs : μ s = ∞) (ht : μ t != ∞) : μ (s \ t) = ∞ := by
  contrapose! hs
  exact ((measure_mono (subset_sdiff_union s t)).trans_lt
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs.lt_top, ht.lt_top⟩))).ne

@[deprecated (since := "2026-06-03")] alias measure_diff_eq_top := measure_sdiff_eq_top

/--
theorem `measure_union_add_inter` / 定理 `measure_union_add_inter`

English:
theorem measure_union_add_inter
  given: (s : Set α) (ht : MeasurableSet t)
  proof: by
  rw [← measure_inter_add_sdiff (s union t) ht]; rw [Set.union_inter_cancel_right]; rw [union_sdiff_right]; rw [←
    measure_inter_add_sdiff s ht]
  ac_rfl

中文:
定理 measure_union_add_inter
  条件: (s : 集合 α) (ht : 可测集 t)
  证明: by
  rw [← measure_inter_add_sdiff (s union t) ht]; rw [Set.union_inter_cancel_right]; rw [union_sdiff_right]; rw [←
    measure_inter_add_sdiff s ht]
  ac_rfl

Depends on / 依赖: Set.union_inter_cancel_right, measure_inter_add_sdiff, union_inter_cancel_right, union_sdiff_right
-/
theorem measure_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ (s union t) + μ (s inter t) = μ s + μ t := by
  rw [← measure_inter_add_sdiff (s union t) ht]; rw [Set.union_inter_cancel_right]; rw [union_sdiff_right]; rw [←
    measure_inter_add_sdiff s ht]
  ac_rfl

/--
theorem `measure_union_add_inter'` / 定理 `measure_union_add_inter'`

English:
theorem measure_union_add_inter'
  given: (hs : MeasurableSet s) (t : Set α)
  proof: by
  rw [union_comm]; rw [inter_comm]; rw [measure_union_add_inter t hs]; rw [add_comm]

中文:
定理 measure_union_add_inter'
  条件: (hs : 可测集 s) (t : 集合 α)
  证明: by
  rw [union_comm]; rw [inter_comm]; rw [measure_union_add_inter t hs]; rw [add_comm]

Depends on / 依赖: add_comm, inter_comm, measure_union_add_inter, union_comm
-/
theorem measure_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ (s union t) + μ (s inter t) = μ s + μ t := by
  rw [union_comm]; rw [inter_comm]; rw [measure_union_add_inter t hs]; rw [add_comm]

/--
lemma `measure_symmDiff_eq` / 引理 `measure_symmDiff_eq`

English:
lemma measure_symmDiff_eq
  given: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  proof: by
  simpa only [symmDiff_def, sup_eq_union]
    using measure_union₀ (ht.diff hs) disjoint_sdiff_sdiff.aedisjoint

中文:
引理 measure_symmDiff_eq
  条件: (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
  证明: by
  simpa only [symmDiff_def, sup_eq_union]
    using measure_union₀ (ht.diff hs) disjoint_sdiff_sdiff.aedisjoint

Depends on / 依赖: aedisjoint, disjoint_sdiff_sdiff, disjoint_sdiff_sdiff.aedisjoint, ht.diff, sup_eq_union, symmDiff_def
-/
lemma measure_symmDiff_eq (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    μ (s ∆ t) = μ (s \ t) + μ (t \ s) := by
  simpa only [symmDiff_def, sup_eq_union]
    using measure_union₀ (ht.diff hs) disjoint_sdiff_sdiff.aedisjoint

/--
lemma `measure_symmDiff_le` / 引理 `measure_symmDiff_le`

English:
lemma measure_symmDiff_le
  given: (s t u : Set α)
  proof: le_trans (μ.mono <| symmDiff_triangle s t u) (measure_union_le (s ∆ t) (t ∆ u))

中文:
引理 measure_symmDiff_le
  条件: (s t u : 集合 α)
  证明: le_trans (μ.mono <| symmDiff_triangle s t u) (measure_union_le (s ∆ t) (t ∆ u))

Depends on / 依赖: le_trans, measure_union_le, symmDiff_triangle
-/
lemma measure_symmDiff_le (s t u : Set α) :
    μ (s ∆ u) <= μ (s ∆ t) + μ (t ∆ u) :=
  le_trans (μ.mono <| symmDiff_triangle s t u) (measure_union_le (s ∆ t) (t ∆ u))

/--
theorem `measure_symmDiff_eq_top` / 定理 `measure_symmDiff_eq_top`

English:
theorem measure_symmDiff_eq_top
  given: (hs : μ s != ∞) (ht : μ t = ∞)
  statement: μ (s ∆ t) = ∞
  proof: measure_mono_top subset_union_right (measure_sdiff_eq_top ht hs)

中文:
定理 measure_symmDiff_eq_top
  条件: (hs : μ s != ∞) (ht : μ t = ∞)
  结论: μ (s ∆ t) = ∞
  证明: measure_mono_top subset_union_right (measure_sdiff_eq_top ht hs)

Depends on / 依赖: measure_mono_top, measure_sdiff_eq_top, subset_union_right
-/
theorem measure_symmDiff_eq_top (hs : μ s != ∞) (ht : μ t = ∞) : μ (s ∆ t) = ∞ :=
  measure_mono_top subset_union_right (measure_sdiff_eq_top ht hs)

/--
theorem `measure_add_measure_compl` / 定理 `measure_add_measure_compl`

English:
theorem measure_add_measure_compl
  given: (h : MeasurableSet s)
  statement: μ s + μ sᶜ = μ univ
  proof: measure_add_measure_compl₀ h.nullMeasurableSet

中文:
定理 measure_add_measure_compl
  条件: (h : 可测集 s)
  结论: μ s + μ sᶜ = μ univ
  证明: measure_add_measure_compl₀ h.nullMeasurableSet

Depends on / 依赖: h.nullMeasurableSet, nullMeasurableSet
-/
theorem measure_add_measure_compl (h : MeasurableSet s) : μ s + μ sᶜ = μ univ :=
  measure_add_measure_compl₀ h.nullMeasurableSet

/--
theorem `measure_biUnion₀` / 定理 `measure_biUnion₀`

English:
theorem measure_biUnion₀
  statement: {s : Set β} {f : β -> Set α} (hs : s.Countable)
  proof: by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]
  exact measure_iUnion₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2

中文:
定理 measure_biUnion₀
  结论: {s : 集合 β} {f : β -> 集合 α} (hs : s.可数)
  证明: by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]
  exact measure_iUnion₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2

Depends on / 依赖: Subtype, Subtype.coe_injective, biUnion_eq_iUnion, coe_injective, hd.on_injective, hs.toEncodable, on_injective, toEncodable
-/
theorem measure_biUnion₀ {s : Set β} {f : β -> Set α} (hs : s.Countable)
    (hd : s.Pairwise (AEDisjoint μ on f)) (h : forall b in s, NullMeasurableSet (f b) μ) :
    μ (⋃ b in s, f b) = ∑' p : s, μ (f p) := by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]
  exact measure_iUnion₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2

/--
theorem `measure_biUnion` / 定理 `measure_biUnion`

English:
theorem measure_biUnion
  statement: {s : Set β} {f : β -> Set α} (hs : s.Countable) (hd : s.PairwiseDisjoint f)
  proof: measure_biUnion₀ hs hd.aedisjoint fun b hb => (h b hb).nullMeasurableSet

中文:
定理 measure_biUnion
  结论: {s : 集合 β} {f : β -> 集合 α} (hs : s.可数) (hd : s.PairwiseDisjoint f)
  证明: measure_biUnion₀ hs hd.aedisjoint fun b hb => (h b hb).nullMeasurableSet

Depends on / 依赖: aedisjoint, hd.aedisjoint, nullMeasurableSet
-/
theorem measure_biUnion {s : Set β} {f : β -> Set α} (hs : s.Countable) (hd : s.PairwiseDisjoint f)
    (h : forall b in s, MeasurableSet (f b)) : μ (⋃ b in s, f b) = ∑' p : s, μ (f p) :=
  measure_biUnion₀ hs hd.aedisjoint fun b hb => (h b hb).nullMeasurableSet

/--
theorem `measure_sUnion₀` / 定理 `measure_sUnion₀`

English:
theorem measure_sUnion₀
  statement: {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise (AEDisjoint μ))
  proof: by
  rw [sUnion_eq_biUnion]; rw [measure_biUnion₀ hs hd h]

中文:
定理 measure_sUnion₀
  结论: {S : 集合 (集合 α)} (hs : S.可数) (hd : S.两两 (AEDisjoint μ))
  证明: by
  rw [sUnion_eq_biUnion]; rw [measure_biUnion₀ hs hd h]

Depends on / 依赖: sUnion_eq_biUnion
-/
theorem measure_sUnion₀ {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise (AEDisjoint μ))
    (h : forall s in S, NullMeasurableSet s μ) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion]; rw [measure_biUnion₀ hs hd h]

/--
theorem `measure_sUnion` / 定理 `measure_sUnion`

English:
theorem measure_sUnion
  statement: {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjoint)
  proof: by
  rw [sUnion_eq_biUnion]; rw [measure_biUnion hs hd h]

中文:
定理 measure_sUnion
  结论: {S : 集合 (集合 α)} (hs : S.可数) (hd : S.两两 Disjoint)
  证明: by
  rw [sUnion_eq_biUnion]; rw [measure_biUnion hs hd h]

Depends on / 依赖: measure_biUnion, sUnion_eq_biUnion
-/
theorem measure_sUnion {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjoint)
    (h : forall s in S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion]; rw [measure_biUnion hs hd h]

/--
theorem `measure_biUnion_finset₀` / 定理 `measure_biUnion_finset₀`

English:
theorem measure_biUnion_finset₀
  statement: {s : Finset ι} {f : ι -> Set α}
  proof: by
  rw [← Finset.sum_attach]; rw [Finset.attach_eq_univ]; rw [← tsum_fintype (L := .unconditional s)]
  exact measure_biUnion₀ s.countable_toSet hd hm

中文:
定理 measure_biUnion_finset₀
  结论: {s : 有限集 ι} {f : ι -> 集合 α}
  证明: by
  rw [← Finset.sum_attach]; rw [Finset.attach_eq_univ]; rw [← tsum_fintype (L := .unconditional s)]
  exact measure_biUnion₀ s.countable_toSet hd hm

Depends on / 依赖: Finset, Finset.attach_eq_univ, Finset.sum_attach, attach_eq_univ, countable_toSet, s.countable_toSet, sum_attach, tsum_fintype, unconditional
-/
theorem measure_biUnion_finset₀ {s : Finset ι} {f : ι -> Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : forall b in s, NullMeasurableSet (f b) μ) :
    μ (⋃ b in s, f b) = ∑ p in s, μ (f p) := by
  rw [← Finset.sum_attach]; rw [Finset.attach_eq_univ]; rw [← tsum_fintype (L := .unconditional s)]
  exact measure_biUnion₀ s.countable_toSet hd hm

/--
theorem `measure_biUnion_finset` / 定理 `measure_biUnion_finset`

English:
theorem measure_biUnion_finset
  statement: {s : Finset ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f)
  proof: measure_biUnion_finset₀ hd.aedisjoint fun b hb => (hm b hb).nullMeasurableSet

中文:
定理 measure_biUnion_finset
  结论: {s : 有限集 ι} {f : ι -> 集合 α} (hd : PairwiseDisjoint (↑s) f)
  证明: measure_biUnion_finset₀ hd.aedisjoint fun b hb => (hm b hb).nullMeasurableSet

Depends on / 依赖: aedisjoint, hd.aedisjoint, nullMeasurableSet
-/
theorem measure_biUnion_finset {s : Finset ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : forall b in s, MeasurableSet (f b)) : μ (⋃ b in s, f b) = ∑ p in s, μ (f p) :=
  measure_biUnion_finset₀ hd.aedisjoint fun b hb => (hm b hb).nullMeasurableSet

/--
theorem `tsum_meas_le_meas_iUnion_of_disjoint₀` / 定理 `tsum_meas_le_meas_iUnion_of_disjoint₀`

English:
theorem tsum_meas_le_meas_iUnion_of_disjoint₀
  statement: {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
  proof: by
  rw [ENNReal.tsum_eq_iSup_sum]; rw [iSup_le_iff]
  intro s
  simp only [← measure_biUnion_finset₀ (fun _i _hi _j _hj hij => As_disj hij) fun i _ => As_mble i]
  gcongr
  exact iUnion_subset fun _ => Subset.rfl

中文:
定理 tsum_meas_le_meas_iUnion_of_disjoint₀
  结论: {ι : 类型} {_ : 可测空间 α} (μ : 测度 α)
  证明: by
  rw [ENNReal.tsum_eq_iSup_sum]; rw [iSup_le_iff]
  intro s
  simp only [← measure_biUnion_finset₀ (fun _i _hi _j _hj hij => As_disj hij) fun i _ => As_mble i]
  gcongr
  exact iUnion_subset fun _ => Subset.rfl

Depends on / 依赖: As_disj, As_mble, ENNReal, ENNReal.tsum_eq_iSup_sum, Subset, Subset.rfl, iSup_le_iff, iUnion_subset, tsum_eq_iSup_sum
-/
theorem tsum_meas_le_meas_iUnion_of_disjoint₀ {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
    {As : ι -> Set α} (As_mble : forall i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) : (∑' i, μ (As i)) <= μ (⋃ i, As i) := by
  rw [ENNReal.tsum_eq_iSup_sum]; rw [iSup_le_iff]
  intro s
  simp only [← measure_biUnion_finset₀ (fun _i _hi _j _hj hij => As_disj hij) fun i _ => As_mble i]
  gcongr
  exact iUnion_subset fun _ => Subset.rfl

/--
theorem `tsum_meas_le_meas_iUnion_of_disjoint` / 定理 `tsum_meas_le_meas_iUnion_of_disjoint`

English:
theorem tsum_meas_le_meas_iUnion_of_disjoint
  statement: {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
  proof: tsum_meas_le_meas_iUnion_of_disjoint₀ μ (fun i => (As_mble i).nullMeasurableSet)
    (fun _ _ h => Disjoint.aedisjoint (As_disj h))

中文:
定理 tsum_meas_le_meas_iUnion_of_disjoint
  结论: {ι : 类型} {_ : 可测空间 α} (μ : 测度 α)
  证明: tsum_meas_le_meas_iUnion_of_disjoint₀ μ (fun i => (As_mble i).nullMeasurableSet)
    (fun _ _ h => Disjoint.aedisjoint (As_disj h))

Depends on / 依赖: As_disj, As_mble, Disjoint, Disjoint.aedisjoint, aedisjoint, nullMeasurableSet
-/
theorem tsum_meas_le_meas_iUnion_of_disjoint {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
    {As : ι -> Set α} (As_mble : forall i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : (∑' i, μ (As i)) <= μ (⋃ i, As i) :=
  tsum_meas_le_meas_iUnion_of_disjoint₀ μ (fun i => (As_mble i).nullMeasurableSet)
    (fun _ _ h => Disjoint.aedisjoint (As_disj h))

/--
theorem `tsum_measure_preimage_singleton` / 定理 `tsum_measure_preimage_singleton`

English:
theorem tsum_measure_preimage_singleton
  statement: {s : Set β} (hs : s.Countable) {f : α -> β}
  proof: by
  rw [← Set.biUnion_preimage_singleton]; rw [measure_biUnion hs (pairwiseDisjoint_fiber f s) hf]

中文:
定理 tsum_measure_preimage_singleton
  结论: {s : 集合 β} (hs : s.可数) {f : α -> β}
  证明: by
  rw [← Set.biUnion_preimage_singleton]; rw [measure_biUnion hs (pairwiseDisjoint_fiber f s) hf]

Depends on / 依赖: Set.biUnion_preimage_singleton, biUnion_preimage_singleton, measure_biUnion, pairwiseDisjoint_fiber
-/
theorem tsum_measure_preimage_singleton {s : Set β} (hs : s.Countable) {f : α -> β}
    (hf : forall y in s, MeasurableSet (f ⁻¹' {y})) : (∑' b : s, μ (f ⁻¹' {↑b})) = μ (f ⁻¹' s) := by
  rw [← Set.biUnion_preimage_singleton]; rw [measure_biUnion hs (pairwiseDisjoint_fiber f s) hf]

/--
lemma `measure_preimage_eq_zero_iff_of_countable` / 引理 `measure_preimage_eq_zero_iff_of_countable`

English:
lemma measure_preimage_eq_zero_iff_of_countable
  given: {s : Set β} {f : α -> β} (hs : s.Countable)
  proof: by
  rw [← biUnion_preimage_singleton]; rw [measure_biUnion_null_iff hs]

中文:
引理 measure_preimage_eq_zero_iff_of_countable
  条件: {s : 集合 β} {f : α -> β} (hs : s.可数)
  证明: by
  rw [← biUnion_preimage_singleton]; rw [measure_biUnion_null_iff hs]

Depends on / 依赖: biUnion_preimage_singleton, measure_biUnion_null_iff
-/
lemma measure_preimage_eq_zero_iff_of_countable {s : Set β} {f : α -> β} (hs : s.Countable) :
    μ (f ⁻¹' s) = 0 ↔ forall x in s, μ (f ⁻¹' {x}) = 0 := by
  rw [← biUnion_preimage_singleton]; rw [measure_biUnion_null_iff hs]

/--
theorem `sum_measure_preimage_singleton` / 定理 `sum_measure_preimage_singleton`

English:
theorem sum_measure_preimage_singleton
  statement: (s : Finset β) {f : α -> β}
  proof: by
  simp only [← measure_biUnion_finset (pairwiseDisjoint_fiber f s) hf,
    Finset.set_biUnion_preimage_singleton]

中文:
定理 sum_measure_preimage_singleton
  结论: (s : 有限集 β) {f : α -> β}
  证明: by
  simp only [← measure_biUnion_finset (pairwiseDisjoint_fiber f s) hf,
    Finset.set_biUnion_preimage_singleton]

Depends on / 依赖: Finset, Finset.set_biUnion_preimage_singleton, measure_biUnion_finset, pairwiseDisjoint_fiber, set_biUnion_preimage_singleton
-/
theorem sum_measure_preimage_singleton (s : Finset β) {f : α -> β}
    (hf : forall y in s, MeasurableSet (f ⁻¹' {y})) : (∑ b in s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s) := by
  simp only [← measure_biUnion_finset (pairwiseDisjoint_fiber f s) hf,
    Finset.set_biUnion_preimage_singleton]

/--
lemma `sum_measure_singleton` / 引理 `sum_measure_singleton`

English:
lemma sum_measure_singleton
  given: {s : Finset α} [MeasurableSingletonClass α]
  proof: by
  trans ∑ x in s, μ (id ⁻¹' {x})
  · simp
  rw [sum_measure_preimage_singleton]
  · simp
  · simp

中文:
引理 sum_measure_singleton
  条件: {s : 有限集 α} [MeasurableSingleton类 α]
  证明: by
  trans ∑ x in s, μ (id ⁻¹' {x})
  · simp
  rw [sum_measure_preimage_singleton]
  · simp
  · simp
-/
@[simp] lemma sum_measure_singleton {s : Finset α} [MeasurableSingletonClass α] :
    ∑ x in s, μ {x} = μ s := by
  trans ∑ x in s, μ (id ⁻¹' {x})
  · simp
  rw [sum_measure_preimage_singleton]
  · simp
  · simp

/--
theorem `measure_sdiff_null'` / 定理 `measure_sdiff_null'`

English:
theorem measure_sdiff_null'
  given: (h : μ (s₁ inter s₂) = 0)
  statement: μ (s₁ \ s₂) = μ s₁
  proof: measure_congr sdiff_ae_eq_self.2 h

@[deprecated (since := "2026-06-03")] alias measure_diff_null' := measure_sdiff_null'

中文:
定理 measure_sdiff_null'
  条件: (h : μ (s₁ inter s₂) = 0)
  结论: μ (s₁ \ s₂) = μ s₁
  证明: measure_congr sdiff_ae_eq_self.2 h

@[deprecated (since := "2026-06-03")] alias measure_diff_null' := measure_sdiff_null'

Depends on / 依赖: measure_congr, sdiff_ae_eq_self
-/
theorem measure_sdiff_null' (h : μ (s₁ inter s₂) = 0) : μ (s₁ \ s₂) = μ s₁ :=
measure_congr sdiff_ae_eq_self.2 h

@[deprecated (since := "2026-06-03")] alias measure_diff_null' := measure_sdiff_null'

/--
theorem `measure_add_sdiff` / 定理 `measure_add_sdiff`

English:
theorem measure_add_sdiff
  given: (hs : NullMeasurableSet s μ) (t : Set α)
  proof: by
  rw [← measure_union₀' hs disjoint_sdiff_right.aedisjoint]; rw [union_sdiff_self]

@[deprecated (since := "2026-06-03")] alias measure_add_diff := measure_add_sdiff

中文:
定理 measure_add_sdiff
  条件: (hs : NullMeasurableSet s μ) (t : 集合 α)
  证明: by
  rw [← measure_union₀' hs disjoint_sdiff_right.aedisjoint]; rw [union_sdiff_self]

@[deprecated (since := "2026-06-03")] alias measure_add_diff := measure_add_sdiff

Depends on / 依赖: aedisjoint, disjoint_sdiff_right, disjoint_sdiff_right.aedisjoint, union_sdiff_self
-/
theorem measure_add_sdiff (hs : NullMeasurableSet s μ) (t : Set α) :
    μ s + μ (t \ s) = μ (s union t) := by
  rw [← measure_union₀' hs disjoint_sdiff_right.aedisjoint]; rw [union_sdiff_self]

@[deprecated (since := "2026-06-03")] alias measure_add_diff := measure_add_sdiff

/--
theorem `measure_sdiff'` / 定理 `measure_sdiff'`

English:
theorem measure_sdiff'
  given: (s : Set α) (hm : NullMeasurableSet t μ) (h_fin : μ t != ∞)
  proof: ENNReal.eq_sub_of_add_eq h_fin by rw [add_comm, measure_add_sdiff hm, union_comm]

@[deprecated (since := "2026-06-03")] alias measure_diff' := measure_sdiff'

中文:
定理 measure_sdiff'
  条件: (s : 集合 α) (hm : NullMeasurableSet t μ) (h_fin : μ t != ∞)
  证明: ENNReal.eq_sub_of_add_eq h_fin by rw [add_comm, measure_add_sdiff hm, union_comm]

@[deprecated (since := "2026-06-03")] alias measure_diff' := measure_sdiff'

Depends on / 依赖: ENNReal, ENNReal.eq_sub_of_add_eq, add_comm, eq_sub_of_add_eq, h_fin, measure_add_sdiff, union_comm
-/
theorem measure_sdiff' (s : Set α) (hm : NullMeasurableSet t μ) (h_fin : μ t != ∞) :
    μ (s \ t) = μ (s union t) - μ t :=
ENNReal.eq_sub_of_add_eq h_fin by rw [add_comm, measure_add_sdiff hm, union_comm]

@[deprecated (since := "2026-06-03")] alias measure_diff' := measure_sdiff'

/--
theorem `measure_sdiff` / 定理 `measure_sdiff`

English:
theorem measure_sdiff
  given: (h : s₂ subseteq s₁) (h₂ : NullMeasurableSet s₂ μ) (h_fin : μ s₂ != ∞)
  proof: by rw [measure_sdiff' _ h₂ h_fin, union_eq_self_of_subset_right h]

@[deprecated (since := "2026-06-03")] alias measure_diff := measure_sdiff

中文:
定理 measure_sdiff
  条件: (h : s₂ subseteq s₁) (h₂ : NullMeasurableSet s₂ μ) (h_fin : μ s₂ != ∞)
  证明: by rw [measure_sdiff' _ h₂ h_fin, union_eq_self_of_subset_right h]

@[deprecated (since := "2026-06-03")] alias measure_diff := measure_sdiff

Depends on / 依赖: h_fin, measure_sdiff, union_eq_self_of_subset_right
-/
theorem measure_sdiff (h : s₂ subseteq s₁) (h₂ : NullMeasurableSet s₂ μ) (h_fin : μ s₂ != ∞) :
    μ (s₁ \ s₂) = μ s₁ - μ s₂ := by rw [measure_sdiff' _ h₂ h_fin, union_eq_self_of_subset_right h]

@[deprecated (since := "2026-06-03")] alias measure_diff := measure_sdiff

/--
theorem `le_measure_sdiff` / 定理 `le_measure_sdiff`

English:
theorem le_measure_sdiff
  statement: μ s₁ - μ s₂ <= μ (s₁ \ s₂)
  proof: tsub_le_iff_left.2 (measure_le_inter_add_sdiff μ s₁ s₂).trans by
    gcongr; apply inter_subset_right

@[deprecated (since := "2026-06-03")] alias le_measure_diff := le_measure_sdiff

中文:
定理 le_measure_sdiff
  结论: μ s₁ - μ s₂ <= μ (s₁ \ s₂)
  证明: tsub_le_iff_left.2 (measure_le_inter_add_sdiff μ s₁ s₂).trans by
    gcongr; apply inter_subset_right

@[deprecated (since := "2026-06-03")] alias le_measure_diff := le_measure_sdiff

Depends on / 依赖: inter_subset_right, measure_le_inter_add_sdiff, tsub_le_iff_left
-/
theorem le_measure_sdiff : μ s₁ - μ s₂ <= μ (s₁ \ s₂) :=
tsub_le_iff_left.2 (measure_le_inter_add_sdiff μ s₁ s₂).trans by
    gcongr; apply inter_subset_right

@[deprecated (since := "2026-06-03")] alias le_measure_diff := le_measure_sdiff

/--
theorem `le_measure_symmDiff` / 定理 `le_measure_symmDiff`

English:
theorem le_measure_symmDiff
  statement: μ s₁ - μ s₂ <= μ (s₁ ∆ s₂)
  proof: le_trans le_measure_sdiff (measure_mono <| by simp [symmDiff_def])

中文:
定理 le_measure_symmDiff
  结论: μ s₁ - μ s₂ <= μ (s₁ ∆ s₂)
  证明: le_trans le_measure_sdiff (measure_mono <| by simp [symmDiff_def])

Depends on / 依赖: le_measure_sdiff, le_trans, measure_mono, symmDiff_def
-/
theorem le_measure_symmDiff : μ s₁ - μ s₂ <= μ (s₁ ∆ s₂) :=
  le_trans le_measure_sdiff (measure_mono <| by simp [symmDiff_def])

/--
theorem `measure_eq_top_iff_of_symmDiff` / 定理 `measure_eq_top_iff_of_symmDiff`

English:
theorem measure_eq_top_iff_of_symmDiff
  given: (hμst : μ (s ∆ t) != ∞)
  statement: μ s = ∞ ↔ μ t = ∞
  proof: by
  suffices h : forall u v, μ (u ∆ v) != ∞ -> μ u = ∞ -> μ v = ∞
    from ⟨h s t hμst, h t s (symmDiff_comm s t ▸ hμst)⟩
  intro u v hμuv hμu
  by_contra! hμv
  apply hμuv
  rw [Set.symmDiff_def]; rw [eq_top_iff]
  calc
    ∞ = μ u - μ v := by rw [ENNReal.sub_eq_top_iff.2 ⟨hμu, hμv⟩]
    _ <= μ (u \ v) := le_measure_sdiff
    _ <= μ (u \ v union v \ u) := measure_mono subset_union_left

中文:
定理 measure_eq_top_iff_of_symmDiff
  条件: (hμst : μ (s ∆ t) != ∞)
  结论: μ s = ∞ ↔ μ t = ∞
  证明: by
  suffices h : forall u v, μ (u ∆ v) != ∞ -> μ u = ∞ -> μ v = ∞
    from ⟨h s t hμst, h t s (symmDiff_comm s t ▸ hμst)⟩
  intro u v hμuv hμu
  by_contra! hμv
  apply hμuv
  rw [Set.symmDiff_def]; rw [eq_top_iff]
  calc
    ∞ = μ u - μ v := by rw [ENNReal.sub_eq_top_iff.2 ⟨hμu, hμv⟩]
    _ <= μ (u \ v) := le_measure_sdiff
    _ <= μ (u \ v union v \ u) := measure_mono subset_union_left

Depends on / 依赖: ENNReal, ENNReal.sub_eq_top_iff, Set.symmDiff_def, eq_top_iff, le_measure_sdiff, measure_mono, sub_eq_top_iff, subset_union_left, symmDiff_comm, symmDiff_def
-/
theorem measure_eq_top_iff_of_symmDiff (hμst : μ (s ∆ t) != ∞) : μ s = ∞ ↔ μ t = ∞ := by
  suffices h : forall u v, μ (u ∆ v) != ∞ -> μ u = ∞ -> μ v = ∞
    from ⟨h s t hμst, h t s (symmDiff_comm s t ▸ hμst)⟩
  intro u v hμuv hμu
  by_contra! hμv
  apply hμuv
  rw [Set.symmDiff_def]; rw [eq_top_iff]
  calc
    ∞ = μ u - μ v := by rw [ENNReal.sub_eq_top_iff.2 ⟨hμu, hμv⟩]
    _ <= μ (u \ v) := le_measure_sdiff
    _ <= μ (u \ v union v \ u) := measure_mono subset_union_left

/--
theorem `measure_ne_top_iff_of_symmDiff` / 定理 `measure_ne_top_iff_of_symmDiff`

English:
theorem measure_ne_top_iff_of_symmDiff
  given: (hμst : μ (s ∆ t) != ∞)
  statement: μ s != ∞ ↔ μ t != ∞
  proof: (measure_eq_top_iff_of_symmDiff hμst).ne

中文:
定理 measure_ne_top_iff_of_symmDiff
  条件: (hμst : μ (s ∆ t) != ∞)
  结论: μ s != ∞ ↔ μ t != ∞
  证明: (measure_eq_top_iff_of_symmDiff hμst).ne

Depends on / 依赖: measure_eq_top_iff_of_symmDiff
-/
theorem measure_ne_top_iff_of_symmDiff (hμst : μ (s ∆ t) != ∞) : μ s != ∞ ↔ μ t != ∞ :=
    (measure_eq_top_iff_of_symmDiff hμst).ne

/--
theorem `measure_sdiff_lt_of_lt_add` / 定理 `measure_sdiff_lt_of_lt_add`

English:
theorem measure_sdiff_lt_of_lt_add
  statement: (hs : NullMeasurableSet s μ) (hst : s subseteq t) (hs' : μ s != ∞)
  proof: by
  rw [measure_sdiff hst hs hs']; rw [add_comm] at h
  exact ENNReal.sub_lt_of_lt_add (measure_mono hst) h

@[deprecated (since := "2026-06-03")] alias measure_diff_lt_of_lt_add := measure_sdiff_lt_of_lt_add

中文:
定理 measure_sdiff_lt_of_lt_add
  结论: (hs : NullMeasurableSet s μ) (hst : s subseteq t) (hs' : μ s != ∞)
  证明: by
  rw [measure_sdiff hst hs hs']; rw [add_comm] at h
  exact ENNReal.sub_lt_of_lt_add (measure_mono hst) h

@[deprecated (since := "2026-06-03")] alias measure_diff_lt_of_lt_add := measure_sdiff_lt_of_lt_add

Depends on / 依赖: ENNReal, ENNReal.sub_lt_of_lt_add, add_comm, measure_mono, measure_sdiff, sub_lt_of_lt_add
-/
theorem measure_sdiff_lt_of_lt_add (hs : NullMeasurableSet s μ) (hst : s subseteq t) (hs' : μ s != ∞)
    {ε : Real>=0∞} (h : μ t < μ s + ε) : μ (t \ s) < ε := by
  rw [measure_sdiff hst hs hs']; rw [add_comm] at h
  exact ENNReal.sub_lt_of_lt_add (measure_mono hst) h

@[deprecated (since := "2026-06-03")] alias measure_diff_lt_of_lt_add := measure_sdiff_lt_of_lt_add

/--
theorem `measure_sdiff_le_iff_le_add` / 定理 `measure_sdiff_le_iff_le_add`

English:
theorem measure_sdiff_le_iff_le_add
  statement: (hs : NullMeasurableSet s μ) (hst : s subseteq t) (hs' : μ s != ∞)
  proof: by
  rw [measure_sdiff hst hs hs']; rw [tsub_le_iff_left]

@[deprecated (since := "2026-06-03")]
alias measure_diff_le_iff_le_add := measure_sdiff_le_iff_le_add

中文:
定理 measure_sdiff_le_iff_le_add
  结论: (hs : NullMeasurableSet s μ) (hst : s subseteq t) (hs' : μ s != ∞)
  证明: by
  rw [measure_sdiff hst hs hs']; rw [tsub_le_iff_left]

@[deprecated (since := "2026-06-03")]
alias measure_diff_le_iff_le_add := measure_sdiff_le_iff_le_add

Depends on / 依赖: measure_sdiff, tsub_le_iff_left
-/
theorem measure_sdiff_le_iff_le_add (hs : NullMeasurableSet s μ) (hst : s subseteq t) (hs' : μ s != ∞)
    {ε : Real>=0∞} : μ (t \ s) <= ε ↔ μ t <= μ s + ε := by
  rw [measure_sdiff hst hs hs']; rw [tsub_le_iff_left]

@[deprecated (since := "2026-06-03")]
alias measure_diff_le_iff_le_add := measure_sdiff_le_iff_le_add

/--
theorem `measure_eq_measure_of_null_sdiff` / 定理 `measure_eq_measure_of_null_sdiff`

English:
theorem measure_eq_measure_of_null_sdiff
  given: {s t : Set α} (hst : s subseteq t) (h_nullsdiff : μ (t \ s) = 0)
  proof: measure_congr
      EventuallyLE.antisymm (LE.le.eventuallyLE hst) (ae_le_set.mpr h_nullsdiff)

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_of_null_diff := measure_eq_measure_of_null_sdiff

中文:
定理 measure_eq_measure_of_null_sdiff
  条件: {s t : 集合 α} (hst : s subseteq t) (h_nullsdiff : μ (t \ s) = 0)
  证明: measure_congr
      EventuallyLE.antisymm (LE.le.eventuallyLE hst) (ae_le_set.mpr h_nullsdiff)

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_of_null_diff := measure_eq_measure_of_null_sdiff

Depends on / 依赖: measure_congr
-/
theorem measure_eq_measure_of_null_sdiff {s t : Set α} (hst : s subseteq t) (h_nullsdiff : μ (t \ s) = 0) :
μ s = μ t := measure_congr
      EventuallyLE.antisymm (LE.le.eventuallyLE hst) (ae_le_set.mpr h_nullsdiff)

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_of_null_diff := measure_eq_measure_of_null_sdiff

/--
theorem `measure_eq_measure_of_between_null_sdiff` / 定理 `measure_eq_measure_of_between_null_sdiff`

English:
theorem measure_eq_measure_of_between_null_sdiff
  statement: {s₁ s₂ s₃ : Set α} (h12 : s₁ subseteq s₂) (h23 : s₂ subseteq s₃)
  proof: by
  have le12 : μ s₁ <= μ s₂ := measure_mono h12
  have le23 : μ s₂ <= μ s₃ := measure_mono h23
  have key : μ s₃ <= μ s₁ :=
    calc
      μ s₃ = μ (s₃ \ s₁ union s₁) := by rw [sdiff_union_of_subset (h12.trans h23)]
      _ <= μ (s₃ \ s₁) + μ s₁ := measure_union_le _ _
      _ = μ s₁ := by simp only [h_nullsdiff, zero_add]
  exact ⟨le12.antisymm (le23.trans key), le23.antisymm (key.trans le12)⟩

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_of_between_null_diff := measure_eq_measure_of_between_null_sdiff

中文:
定理 measure_eq_measure_of_between_null_sdiff
  结论: {s₁ s₂ s₃ : 集合 α} (h12 : s₁ subseteq s₂) (h23 : s₂ subseteq s₃)
  证明: by
  have le12 : μ s₁ <= μ s₂ := measure_mono h12
  have le23 : μ s₂ <= μ s₃ := measure_mono h23
  have key : μ s₃ <= μ s₁ :=
    calc
      μ s₃ = μ (s₃ \ s₁ union s₁) := by rw [sdiff_union_of_subset (h12.trans h23)]
      _ <= μ (s₃ \ s₁) + μ s₁ := measure_union_le _ _
      _ = μ s₁ := by simp only [h_nullsdiff, zero_add]
  exact ⟨le12.antisymm (le23.trans key), le23.antisymm (key.trans le12)⟩

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_of_between_null_diff := measure_eq_measure_of_between_null_sdiff

Depends on / 依赖: antisymm, h12.trans, h_nullsdiff, key.trans, le12.antisymm, le23.antisymm, le23.trans, measure_mono, measure_union_le, sdiff_union_of_subset, zero_add
-/
theorem measure_eq_measure_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 : s₁ subseteq s₂) (h23 : s₂ subseteq s₃)
    (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ := by
  have le12 : μ s₁ <= μ s₂ := measure_mono h12
  have le23 : μ s₂ <= μ s₃ := measure_mono h23
  have key : μ s₃ <= μ s₁ :=
    calc
      μ s₃ = μ (s₃ \ s₁ union s₁) := by rw [sdiff_union_of_subset (h12.trans h23)]
      _ <= μ (s₃ \ s₁) + μ s₁ := measure_union_le _ _
      _ = μ s₁ := by simp only [h_nullsdiff, zero_add]
  exact ⟨le12.antisymm (le23.trans key), le23.antisymm (key.trans le12)⟩

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_of_between_null_diff := measure_eq_measure_of_between_null_sdiff

/--
theorem `measure_eq_measure_smaller_of_between_null_sdiff` / 定理 `measure_eq_measure_smaller_of_between_null_sdiff`

English:
theorem measure_eq_measure_smaller_of_between_null_sdiff
  statement: {s₁ s₂ s₃ : Set α} (h12 : s₁ subseteq s₂)
  proof: (measure_eq_measure_of_between_null_sdiff h12 h23 h_nullsdiff).1

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_smaller_of_between_null_diff :=
  measure_eq_measure_smaller_of_between_null_sdiff

中文:
定理 measure_eq_measure_smaller_of_between_null_sdiff
  结论: {s₁ s₂ s₃ : 集合 α} (h12 : s₁ subseteq s₂)
  证明: (measure_eq_measure_of_between_null_sdiff h12 h23 h_nullsdiff).1

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_smaller_of_between_null_diff :=
  measure_eq_measure_smaller_of_between_null_sdiff

Depends on / 依赖: h_nullsdiff, measure_eq_measure_of_between_null_sdiff
-/
theorem measure_eq_measure_smaller_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 : s₁ subseteq s₂)
    (h23 : s₂ subseteq s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ :=
  (measure_eq_measure_of_between_null_sdiff h12 h23 h_nullsdiff).1

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_smaller_of_between_null_diff :=
  measure_eq_measure_smaller_of_between_null_sdiff

/--
theorem `measure_eq_measure_larger_of_between_null_sdiff` / 定理 `measure_eq_measure_larger_of_between_null_sdiff`

English:
theorem measure_eq_measure_larger_of_between_null_sdiff
  statement: {s₁ s₂ s₃ : Set α} (h12 : s₁ subseteq s₂)
  proof: (measure_eq_measure_of_between_null_sdiff h12 h23 h_nullsdiff).2

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_larger_of_between_null_diff :=
  measure_eq_measure_larger_of_between_null_sdiff

中文:
定理 measure_eq_measure_larger_of_between_null_sdiff
  结论: {s₁ s₂ s₃ : 集合 α} (h12 : s₁ subseteq s₂)
  证明: (measure_eq_measure_of_between_null_sdiff h12 h23 h_nullsdiff).2

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_larger_of_between_null_diff :=
  measure_eq_measure_larger_of_between_null_sdiff

Depends on / 依赖: h_nullsdiff, measure_eq_measure_of_between_null_sdiff
-/
theorem measure_eq_measure_larger_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 : s₁ subseteq s₂)
    (h23 : s₂ subseteq s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₂ = μ s₃ :=
  (measure_eq_measure_of_between_null_sdiff h12 h23 h_nullsdiff).2

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_larger_of_between_null_diff :=
  measure_eq_measure_larger_of_between_null_sdiff

/--
lemma `measure_compl₀` / 引理 `measure_compl₀`

English:
lemma measure_compl₀
  given: (h : NullMeasurableSet s μ) (hs : μ s != ∞)
  proof: by
  rw [← measure_add_measure_compl₀ h]; rw [ENNReal.add_sub_cancel_left hs]

中文:
引理 measure_compl₀
  条件: (h : NullMeasurableSet s μ) (hs : μ s != ∞)
  证明: by
  rw [← measure_add_measure_compl₀ h]; rw [ENNReal.add_sub_cancel_left hs]

Depends on / 依赖: ENNReal, ENNReal.add_sub_cancel_left, add_sub_cancel_left
-/
lemma measure_compl₀ (h : NullMeasurableSet s μ) (hs : μ s != ∞) :
    μ sᶜ = μ Set.univ - μ s := by
  rw [← measure_add_measure_compl₀ h]; rw [ENNReal.add_sub_cancel_left hs]

/--
theorem `measure_compl` / 定理 `measure_compl`

English:
theorem measure_compl
  given: (h₁ : MeasurableSet s) (h_fin : μ s != ∞)
  statement: μ sᶜ = μ univ - μ s
  proof: measure_compl₀ h₁.nullMeasurableSet h_fin

中文:
定理 measure_compl
  条件: (h₁ : 可测集 s) (h_fin : μ s != ∞)
  结论: μ sᶜ = μ univ - μ s
  证明: measure_compl₀ h₁.nullMeasurableSet h_fin

Depends on / 依赖: h_fin, nullMeasurableSet
-/
theorem measure_compl (h₁ : MeasurableSet s) (h_fin : μ s != ∞) : μ sᶜ = μ univ - μ s :=
  measure_compl₀ h₁.nullMeasurableSet h_fin

/--
lemma `measure_inter_conull'` / 引理 `measure_inter_conull'`

English:
lemma measure_inter_conull'
  given: (ht : μ (s \ t) = 0)
  statement: μ (s inter t) = μ s
  proof: by
  rw [← sdiff_compl]; rw [measure_sdiff_null']; rwa [← sdiff_eq]

中文:
引理 measure_inter_conull'
  条件: (ht : μ (s \ t) = 0)
  结论: μ (s inter t) = μ s
  证明: by
  rw [← sdiff_compl]; rw [measure_sdiff_null']; rwa [← sdiff_eq]

Depends on / 依赖: measure_sdiff_null, sdiff_compl, sdiff_eq
-/
lemma measure_inter_conull' (ht : μ (s \ t) = 0) : μ (s inter t) = μ s := by
  rw [← sdiff_compl]; rw [measure_sdiff_null']; rwa [← sdiff_eq]

/--
lemma `measure_inter_conull` / 引理 `measure_inter_conull`

English:
lemma measure_inter_conull
  given: (ht : μ tᶜ = 0)
  statement: μ (s inter t) = μ s
  proof: by
  rw [← sdiff_compl]; rw [measure_sdiff_null ht]

@[simp]

中文:
引理 measure_inter_conull
  条件: (ht : μ tᶜ = 0)
  结论: μ (s inter t) = μ s
  证明: by
  rw [← sdiff_compl]; rw [measure_sdiff_null ht]

@[simp]

Depends on / 依赖: measure_sdiff_null, sdiff_compl
-/
lemma measure_inter_conull (ht : μ tᶜ = 0) : μ (s inter t) = μ s := by
  rw [← sdiff_compl]; rw [measure_sdiff_null ht]

@[simp]
/--
theorem `union_ae_eq_left_iff_ae_subset` / 定理 `union_ae_eq_left_iff_ae_subset`

English:
theorem union_ae_eq_left_iff_ae_subset
  statement: (s union t : Set α) =ᵐ[μ] s ↔ t <=ᵐ[μ] s
  proof: by
  rw [ae_le_set]
  refine
    ⟨fun h => by simpa only [union_sdiff_left] using (ae_eq_set.mp h).1, fun h =>
      eventuallyLE_antisymm_iff.mpr
        ⟨by rwa [ae_le_set, union_sdiff_left],
          LE.le.eventuallyLE subset_union_left⟩⟩

@[simp]

中文:
定理 union_ae_eq_left_iff_ae_subset
  结论: (s union t : 集合 α) =ᵐ[μ] s ↔ t <=ᵐ[μ] s
  证明: by
  rw [ae_le_set]
  refine
    ⟨fun h => by simpa only [union_sdiff_left] using (ae_eq_set.mp h).1, fun h =>
      eventuallyLE_antisymm_iff.mpr
        ⟨by rwa [ae_le_set, union_sdiff_left],
          LE.le.eventuallyLE subset_union_left⟩⟩

@[simp]

Depends on / 依赖: LE.le.eventuallyLE, ae_eq_set, ae_eq_set.mp, ae_le_set, eventuallyLE, eventuallyLE_antisymm_iff, eventuallyLE_antisymm_iff.mpr, subset_union_left, union_sdiff_left
-/
theorem union_ae_eq_left_iff_ae_subset : (s union t : Set α) =ᵐ[μ] s ↔ t <=ᵐ[μ] s := by
  rw [ae_le_set]
  refine
    ⟨fun h => by simpa only [union_sdiff_left] using (ae_eq_set.mp h).1, fun h =>
      eventuallyLE_antisymm_iff.mpr
        ⟨by rwa [ae_le_set, union_sdiff_left],
          LE.le.eventuallyLE subset_union_left⟩⟩

@[simp]
/--
theorem `union_ae_eq_right_iff_ae_subset` / 定理 `union_ae_eq_right_iff_ae_subset`

English:
theorem union_ae_eq_right_iff_ae_subset
  statement: (s union t : Set α) =ᵐ[μ] t ↔ s <=ᵐ[μ] t
  proof: by
  rw [union_comm]; rw [union_ae_eq_left_iff_ae_subset]

中文:
定理 union_ae_eq_right_iff_ae_subset
  结论: (s union t : 集合 α) =ᵐ[μ] t ↔ s <=ᵐ[μ] t
  证明: by
  rw [union_comm]; rw [union_ae_eq_left_iff_ae_subset]

Depends on / 依赖: union_ae_eq_left_iff_ae_subset, union_comm
-/
theorem union_ae_eq_right_iff_ae_subset : (s union t : Set α) =ᵐ[μ] t ↔ s <=ᵐ[μ] t := by
  rw [union_comm]; rw [union_ae_eq_left_iff_ae_subset]

/--
theorem `ae_eq_of_ae_subset_of_measure_ge` / 定理 `ae_eq_of_ae_subset_of_measure_ge`

English:
theorem ae_eq_of_ae_subset_of_measure_ge
  statement: (h₁ : s <=ᵐ[μ] t) (h₂ : μ t <= μ s)
  proof: by
  refine eventuallyLE_antisymm_iff.mpr ⟨h₁, ae_le_set.mpr ?_⟩
  replace h₂ : μ t = μ s := h₂.antisymm (measure_mono_ae h₁)
  replace ht : μ s != ∞ := h₂ ▸ ht
  rw [measure_sdiff' t hsm ht]; rw [measure_congr (union_ae_eq_left_iff_ae_subset.mpr h₁)]; rw [h₂]; rw [tsub_self]

中文:
定理 ae_eq_of_ae_subset_of_measure_ge
  结论: (h₁ : s <=ᵐ[μ] t) (h₂ : μ t <= μ s)
  证明: by
  refine eventuallyLE_antisymm_iff.mpr ⟨h₁, ae_le_set.mpr ?_⟩
  replace h₂ : μ t = μ s := h₂.antisymm (measure_mono_ae h₁)
  replace ht : μ s != ∞ := h₂ ▸ ht
  rw [measure_sdiff' t hsm ht]; rw [measure_congr (union_ae_eq_left_iff_ae_subset.mpr h₁)]; rw [h₂]; rw [tsub_self]

Depends on / 依赖: ae_le_set, ae_le_set.mpr, antisymm, eventuallyLE_antisymm_iff, eventuallyLE_antisymm_iff.mpr, measure_congr, measure_mono_ae, measure_sdiff, replace, tsub_self, union_ae_eq_left_iff_ae_subset, union_ae_eq_left_iff_ae_subset.mpr
-/
theorem ae_eq_of_ae_subset_of_measure_ge (h₁ : s <=ᵐ[μ] t) (h₂ : μ t <= μ s)
    (hsm : NullMeasurableSet s μ) (ht : μ t != ∞) : s =ᵐ[μ] t := by
  refine eventuallyLE_antisymm_iff.mpr ⟨h₁, ae_le_set.mpr ?_⟩
  replace h₂ : μ t = μ s := h₂.antisymm (measure_mono_ae h₁)
  replace ht : μ s != ∞ := h₂ ▸ ht
  rw [measure_sdiff' t hsm ht]; rw [measure_congr (union_ae_eq_left_iff_ae_subset.mpr h₁)]; rw [h₂]; rw [tsub_self]

/--
theorem `ae_eq_of_subset_of_measure_ge` / 定理 `ae_eq_of_subset_of_measure_ge`

English:
theorem ae_eq_of_subset_of_measure_ge
  statement: (h₁ : s subseteq t) (h₂ : μ t <= μ s) (hsm : NullMeasurableSet s μ)
  proof: ae_eq_of_ae_subset_of_measure_ge h₁.eventuallyLE h₂ hsm ht

中文:
定理 ae_eq_of_subset_of_measure_ge
  结论: (h₁ : s subseteq t) (h₂ : μ t <= μ s) (hsm : NullMeasurableSet s μ)
  证明: ae_eq_of_ae_subset_of_measure_ge h₁.eventuallyLE h₂ hsm ht

Depends on / 依赖: ae_eq_of_ae_subset_of_measure_ge, eventuallyLE
-/
theorem ae_eq_of_subset_of_measure_ge (h₁ : s subseteq t) (h₂ : μ t <= μ s) (hsm : NullMeasurableSet s μ)
    (ht : μ t != ∞) : s =ᵐ[μ] t :=
  ae_eq_of_ae_subset_of_measure_ge h₁.eventuallyLE h₂ hsm ht

/--
theorem `measure_iUnion_congr_of_subset` / 定理 `measure_iUnion_congr_of_subset`

English:
theorem measure_iUnion_congr_of_subset
  statement: {ι : Sort*} [Countable ι] {s : ι -> Set α} {t : ι -> Set α}
  proof: by
  refine le_antisymm (by gcongr; apply hsub) ?_
  by_cases! htop : exists i, μ (t i) = ∞
  · rcases htop with ⟨i, hi⟩
    calc
      μ (⋃ i, t i) <= ∞ := le_top
      _ <= μ (s i) := hi ▸ h_le i
_ <= μ (⋃ i, s i) := measure_mono subset_iUnion _ _
  set M := toMeasurable μ
  have H : forall b, (M (t b) inter M (⋃ b, s b) : Set α) =ᵐ[μ] M (t b) := by
    refine fun b => ae_eq_of_subset_of_measure_ge inter_subset_left ?_ ?_ ?_
    · calc
        μ (M (t b)) = μ (t b) := measure_toMeasurable _
        _ <= μ (s b) := h_le b
        _ <= μ (M (t b) inter M (⋃ b, s b)) :=
measure_mono
            subset_inter ((hsub b).trans <| subset_toMeasurable _ _)
              ((subset_iUnion _ _).trans <| subset_toMeasurable _ _)
    · measurability
    · rw [measure_toMeasurable]
      exact htop b
  calc
    μ (⋃ b, t b) <= μ (⋃ b, M (t b)) := measure_mono (iUnion_mono fun b => subset_toMeasurable _ _)
    _ = μ (⋃ b, M (t b) inter M (⋃ b, s b)) :=
      measure_congr (Filter.EventuallyEq.countable_iUnion H).symm
    _ <= μ (M (⋃ b, s b)) := measure_mono (iUnion_subset fun b => inter_subset_right)
    _ = μ (⋃ b, s b) := measure_toMeasurable _

中文:
定理 measure_iUnion_congr_of_subset
  结论: {ι : 类型层*} [可数 ι] {s : ι -> 集合 α} {t : ι -> 集合 α}
  证明: by
  refine le_antisymm (by gcongr; apply hsub) ?_
  by_cases! htop : exists i, μ (t i) = ∞
  · rcases htop with ⟨i, hi⟩
    calc
      μ (⋃ i, t i) <= ∞ := le_top
      _ <= μ (s i) := hi ▸ h_le i
_ <= μ (⋃ i, s i) := measure_mono subset_iUnion _ _
  set M := toMeasurable μ
  have H : forall b, (M (t b) inter M (⋃ b, s b) : Set α) =ᵐ[μ] M (t b) := by
    refine fun b => ae_eq_of_subset_of_measure_ge inter_subset_left ?_ ?_ ?_
    · calc
        μ (M (t b)) = μ (t b) := measure_toMeasurable _
        _ <= μ (s b) := h_le b
        _ <= μ (M (t b) inter M (⋃ b, s b)) :=
measure_mono
            subset_inter ((hsub b).trans <| subset_toMeasurable _ _)
              ((subset_iUnion _ _).trans <| subset_toMeasurable _ _)
    · measurability
    · rw [measure_toMeasurable]
      exact htop b
  calc
    μ (⋃ b, t b) <= μ (⋃ b, M (t b)) := measure_mono (iUnion_mono fun b => subset_toMeasurable _ _)
    _ = μ (⋃ b, M (t b) inter M (⋃ b, s b)) :=
      measure_congr (Filter.EventuallyEq.countable_iUnion H).symm
    _ <= μ (M (⋃ b, s b)) := measure_mono (iUnion_subset fun b => inter_subset_right)
    _ = μ (⋃ b, s b) := measure_toMeasurable _

Depends on / 依赖: ae_eq_of_subset_of_measure_ge, h_le, inter_subset_left, le_antisymm, le_top, measure_mono, measure_toMeasurable, subset_iUnion, toMeasurable
-/
theorem measure_iUnion_congr_of_subset {ι : Sort*} [Countable ι] {s : ι -> Set α} {t : ι -> Set α}
    (hsub : forall i, s i subseteq t i) (h_le : forall i, μ (t i) <= μ (s i)) : μ (⋃ i, s i) = μ (⋃ i, t i) := by
  refine le_antisymm (by gcongr; apply hsub) ?_
  by_cases! htop : exists i, μ (t i) = ∞
  · rcases htop with ⟨i, hi⟩
    calc
      μ (⋃ i, t i) <= ∞ := le_top
      _ <= μ (s i) := hi ▸ h_le i
_ <= μ (⋃ i, s i) := measure_mono subset_iUnion _ _
  set M := toMeasurable μ
  have H : forall b, (M (t b) inter M (⋃ b, s b) : Set α) =ᵐ[μ] M (t b) := by
    refine fun b => ae_eq_of_subset_of_measure_ge inter_subset_left ?_ ?_ ?_
    · calc
        μ (M (t b)) = μ (t b) := measure_toMeasurable _
        _ <= μ (s b) := h_le b
        _ <= μ (M (t b) inter M (⋃ b, s b)) :=
measure_mono
            subset_inter ((hsub b).trans <| subset_toMeasurable _ _)
              ((subset_iUnion _ _).trans <| subset_toMeasurable _ _)
    · measurability
    · rw [measure_toMeasurable]
      exact htop b
  calc
    μ (⋃ b, t b) <= μ (⋃ b, M (t b)) := measure_mono (iUnion_mono fun b => subset_toMeasurable _ _)
    _ = μ (⋃ b, M (t b) inter M (⋃ b, s b)) :=
      measure_congr (Filter.EventuallyEq.countable_iUnion H).symm
    _ <= μ (M (⋃ b, s b)) := measure_mono (iUnion_subset fun b => inter_subset_right)
    _ = μ (⋃ b, s b) := measure_toMeasurable _

/--
theorem `measure_union_congr_of_subset` / 定理 `measure_union_congr_of_subset`

English:
theorem measure_union_congr_of_subset
  statement: {t₁ t₂ : Set α} (hs : s₁ subseteq s₂) (hsμ : μ s₂ <= μ s₁)
  proof: by
  rw [union_eq_iUnion]; rw [union_eq_iUnion]
  exact measure_iUnion_congr_of_subset (Bool.forall_bool.2 ⟨ht, hs⟩) (Bool.forall_bool.2 ⟨htμ, hsμ⟩)

@[simp]

中文:
定理 measure_union_congr_of_subset
  结论: {t₁ t₂ : 集合 α} (hs : s₁ subseteq s₂) (hsμ : μ s₂ <= μ s₁)
  证明: by
  rw [union_eq_iUnion]; rw [union_eq_iUnion]
  exact measure_iUnion_congr_of_subset (Bool.forall_bool.2 ⟨ht, hs⟩) (Bool.forall_bool.2 ⟨htμ, hsμ⟩)

@[simp]

Depends on / 依赖: Bool.forall_bool, forall_bool, measure_iUnion_congr_of_subset, union_eq_iUnion
-/
theorem measure_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ subseteq s₂) (hsμ : μ s₂ <= μ s₁)
    (ht : t₁ subseteq t₂) (htμ : μ t₂ <= μ t₁) : μ (s₁ union t₁) = μ (s₂ union t₂) := by
  rw [union_eq_iUnion]; rw [union_eq_iUnion]
  exact measure_iUnion_congr_of_subset (Bool.forall_bool.2 ⟨ht, hs⟩) (Bool.forall_bool.2 ⟨htμ, hsμ⟩)

@[simp]
/--
theorem `measure_iUnion_toMeasurable` / 定理 `measure_iUnion_toMeasurable`

English:
theorem measure_iUnion_toMeasurable
  given: {ι : Sort*} [Countable ι] (s : ι -> Set α)
  proof: Eq.symm measure_iUnion_congr_of_subset (fun _i => subset_toMeasurable _ _) fun _i =>
    (measure_toMeasurable _).le

中文:
定理 measure_iUnion_toMeasurable
  条件: {ι : 类型层*} [可数 ι] (s : ι -> 集合 α)
  证明: Eq.symm measure_iUnion_congr_of_subset (fun _i => subset_toMeasurable _ _) fun _i =>
    (measure_toMeasurable _).le

Depends on / 依赖: Eq.symm, measure_iUnion_congr_of_subset, measure_toMeasurable, subset_toMeasurable
-/
theorem measure_iUnion_toMeasurable {ι : Sort*} [Countable ι] (s : ι -> Set α) :
    μ (⋃ i, toMeasurable μ (s i)) = μ (⋃ i, s i) :=
Eq.symm measure_iUnion_congr_of_subset (fun _i => subset_toMeasurable _ _) fun _i =>
    (measure_toMeasurable _).le

/--
theorem `measure_biUnion_toMeasurable` / 定理 `measure_biUnion_toMeasurable`

English:
theorem measure_biUnion_toMeasurable
  given: {I : Set β} (hc : I.Countable) (s : β -> Set α)
  proof: by
  have := hc.toEncodable
  simp only [biUnion_eq_iUnion, measure_iUnion_toMeasurable]

@[simp]

中文:
定理 measure_biUnion_toMeasurable
  条件: {I : 集合 β} (hc : I.可数) (s : β -> 集合 α)
  证明: by
  have := hc.toEncodable
  simp only [biUnion_eq_iUnion, measure_iUnion_toMeasurable]

@[simp]

Depends on / 依赖: biUnion_eq_iUnion, hc.toEncodable, measure_iUnion_toMeasurable, toEncodable
-/
theorem measure_biUnion_toMeasurable {I : Set β} (hc : I.Countable) (s : β -> Set α) :
    μ (⋃ b in I, toMeasurable μ (s b)) = μ (⋃ b in I, s b) := by
  have := hc.toEncodable
  simp only [biUnion_eq_iUnion, measure_iUnion_toMeasurable]

@[simp]
/--
theorem `measure_toMeasurable_union` / 定理 `measure_toMeasurable_union`

English:
theorem measure_toMeasurable_union
  statement: μ (toMeasurable μ s union t) = μ (s union t)
  proof: Eq.symm
    measure_union_congr_of_subset (subset_toMeasurable _ _) (measure_toMeasurable _).le Subset.rfl
      le_rfl

@[simp]

中文:
定理 measure_toMeasurable_union
  结论: μ (toMeasurable μ s union t) = μ (s union t)
  证明: Eq.symm
    measure_union_congr_of_subset (subset_toMeasurable _ _) (measure_toMeasurable _).le Subset.rfl
      le_rfl

@[simp]

Depends on / 依赖: Eq.symm, Subset, Subset.rfl, le_rfl, measure_toMeasurable, measure_union_congr_of_subset, subset_toMeasurable
-/
theorem measure_toMeasurable_union : μ (toMeasurable μ s union t) = μ (s union t) :=
Eq.symm
    measure_union_congr_of_subset (subset_toMeasurable _ _) (measure_toMeasurable _).le Subset.rfl
      le_rfl

@[simp]
/--
theorem `measure_union_toMeasurable` / 定理 `measure_union_toMeasurable`

English:
theorem measure_union_toMeasurable
  statement: μ (s union toMeasurable μ t) = μ (s union t)
  proof: Eq.symm
    measure_union_congr_of_subset Subset.rfl le_rfl (subset_toMeasurable _ _)
      (measure_toMeasurable _).le

中文:
定理 measure_union_toMeasurable
  结论: μ (s union toMeasurable μ t) = μ (s union t)
  证明: Eq.symm
    measure_union_congr_of_subset Subset.rfl le_rfl (subset_toMeasurable _ _)
      (measure_toMeasurable _).le

Depends on / 依赖: Eq.symm, Subset, Subset.rfl, le_rfl, measure_toMeasurable, measure_union_congr_of_subset, subset_toMeasurable
-/
theorem measure_union_toMeasurable : μ (s union toMeasurable μ t) = μ (s union t) :=
Eq.symm
    measure_union_congr_of_subset Subset.rfl le_rfl (subset_toMeasurable _ _)
      (measure_toMeasurable _).le

/--
theorem `sum_measure_le_measure_univ` / 定理 `sum_measure_le_measure_univ`

English:
theorem sum_measure_le_measure_univ
  statement: {s : Finset ι} {t : ι -> Set α}
  proof: by
  rw [← measure_biUnion_finset₀ H h]
  exact measure_mono (subset_univ _)

中文:
定理 sum_measure_le_measure_univ
  结论: {s : 有限集 ι} {t : ι -> 集合 α}
  证明: by
  rw [← measure_biUnion_finset₀ H h]
  exact measure_mono (subset_univ _)

Depends on / 依赖: measure_mono, subset_univ
-/
theorem sum_measure_le_measure_univ {s : Finset ι} {t : ι -> Set α}
    (h : forall i in s, NullMeasurableSet (t i) μ) (H : Set.Pairwise s (AEDisjoint μ on t)) :
    (∑ i in s, μ (t i)) <= μ (univ : Set α) := by
  rw [← measure_biUnion_finset₀ H h]
  exact measure_mono (subset_univ _)

/--
theorem `tsum_measure_le_measure_univ` / 定理 `tsum_measure_le_measure_univ`

English:
theorem tsum_measure_le_measure_univ
  statement: {s : ι -> Set α} (hs : forall i, NullMeasurableSet (s i) μ)
  proof: by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s =>
    sum_measure_le_measure_univ (fun i _hi => hs i) fun i _hi j _hj hij => H hij

中文:
定理 tsum_measure_le_measure_univ
  结论: {s : ι -> 集合 α} (hs : 对任意 i, NullMeasurableSet (s i) μ)
  证明: by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s =>
    sum_measure_le_measure_univ (fun i _hi => hs i) fun i _hi j _hj hij => H hij

Depends on / 依赖: ENNReal, ENNReal.tsum_eq_iSup_sum, iSup_le, sum_measure_le_measure_univ, tsum_eq_iSup_sum
-/
theorem tsum_measure_le_measure_univ {s : ι -> Set α} (hs : forall i, NullMeasurableSet (s i) μ)
    (H : Pairwise (AEDisjoint μ on s)) : ∑' i, μ (s i) <= μ (univ : Set α) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s =>
    sum_measure_le_measure_univ (fun i _hi => hs i) fun i _hi j _hj hij => H hij

/--
theorem `exists_nonempty_inter_of_measure_univ_lt_tsum_measure` / 定理 `exists_nonempty_inter_of_measure_univ_lt_tsum_measure`

English:
theorem exists_nonempty_inter_of_measure_univ_lt_tsum_measure
  statement: {m : MeasurableSpace α}
  proof: by
  contrapose! H
  apply tsum_measure_le_measure_univ hs
  intro i j hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i j hij)).aedisjoint

中文:
定理 存在_nonempty_inter_of_measure_univ_lt_tsum_measure
  结论: {m : 可测空间 α}
  证明: by
  contrapose! H
  apply tsum_measure_le_measure_univ hs
  intro i j hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i j hij)).aedisjoint

Depends on / 依赖: aedisjoint, contrapose, disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty.mpr, tsum_measure_le_measure_univ
-/
theorem exists_nonempty_inter_of_measure_univ_lt_tsum_measure {m : MeasurableSpace α}
    (μ : Measure α) {s : ι -> Set α} (hs : forall i, NullMeasurableSet (s i) μ)
    (H : μ (univ : Set α) < ∑' i, μ (s i)) : exists i j, i != j ∧ (s i inter s j).Nonempty := by
  contrapose! H
  apply tsum_measure_le_measure_univ hs
  intro i j hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i j hij)).aedisjoint

/--
theorem `exists_nonempty_inter_of_measure_univ_lt_sum_measure` / 定理 `exists_nonempty_inter_of_measure_univ_lt_sum_measure`

English:
theorem exists_nonempty_inter_of_measure_univ_lt_sum_measure
  statement: {m : MeasurableSpace α} (μ : Measure α)
  proof: by
  contrapose! H
  apply sum_measure_le_measure_univ h
  intro i hi j hj hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i hi j hj hij)).aedisjoint

中文:
定理 存在_nonempty_inter_of_measure_univ_lt_sum_measure
  结论: {m : 可测空间 α} (μ : 测度 α)
  证明: by
  contrapose! H
  apply sum_measure_le_measure_univ h
  intro i hi j hj hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i hi j hj hij)).aedisjoint

Depends on / 依赖: aedisjoint, contrapose, disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty.mpr, sum_measure_le_measure_univ
-/
theorem exists_nonempty_inter_of_measure_univ_lt_sum_measure {m : MeasurableSpace α} (μ : Measure α)
    {s : Finset ι} {t : ι -> Set α} (h : forall i in s, NullMeasurableSet (t i) μ)
    (H : μ (univ : Set α) < ∑ i in s, μ (t i)) :
    exists i in s, exists j in s, exists _h : i != j, (t i inter t j).Nonempty := by
  contrapose! H
  apply sum_measure_le_measure_univ h
  intro i hi j hj hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i hi j hj hij)).aedisjoint

/--
theorem `nonempty_inter_of_measure_lt_add` / 定理 `nonempty_inter_of_measure_lt_add`

English:
theorem nonempty_inter_of_measure_lt_add
  statement: {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
  proof: by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! h
  calc
    μ s + μ t = μ (s union t) := (measure_union h ht).symm
    _ <= μ u := measure_mono (union_subset h's h't)

中文:
定理 nonempty_inter_of_measure_lt_add
  结论: {m : 可测空间 α} (μ : 测度 α) {s t u : 集合 α}
  证明: by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! h
  calc
    μ s + μ t = μ (s union t) := (measure_union h ht).symm
    _ <= μ u := measure_mono (union_subset h's h't)

Depends on / 依赖: Set.not_disjoint_iff_nonempty_inter, contrapose, measure_mono, measure_union, not_disjoint_iff_nonempty_inter, union_subset
-/
theorem nonempty_inter_of_measure_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (ht : MeasurableSet t) (h's : s subseteq u) (h't : t subseteq u) (h : μ u < μ s + μ t) :
    (s inter t).Nonempty := by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! h
  calc
    μ s + μ t = μ (s union t) := (measure_union h ht).symm
    _ <= μ u := measure_mono (union_subset h's h't)

/--
theorem `nonempty_inter_of_measure_lt_add'` / 定理 `nonempty_inter_of_measure_lt_add'`

English:
theorem nonempty_inter_of_measure_lt_add'
  statement: {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
  proof: by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measure_lt_add μ hs h't h's h

中文:
定理 nonempty_inter_of_measure_lt_add'
  结论: {m : 可测空间 α} (μ : 测度 α) {s t u : 集合 α}
  证明: by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measure_lt_add μ hs h't h's h

Depends on / 依赖: add_comm, inter_comm, nonempty_inter_of_measure_lt_add
-/
theorem nonempty_inter_of_measure_lt_add' {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (hs : MeasurableSet s) (h's : s subseteq u) (h't : t subseteq u) (h : μ u < μ s + μ t) :
    (s inter t).Nonempty := by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measure_lt_add μ hs h't h's h

/--
theorem `_root_.Directed.measure_iUnion` / 定理 `_root_.Directed.measure_iUnion`

English:
theorem _root_.Directed.measure_iUnion
  given: [Countable ι] {s : ι -> Set α} (hd : Directed (· subseteq ·) s)
  proof: by
  -- WLOG, `ι = ℕ`
  rcases Countable.exists_injective_nat ι with ⟨e, he⟩
  generalize ht : Function.extend e s ⊥ = t
  replace hd : Directed (· subseteq ·) t := ht ▸ hd.extend_bot he
  suffices μ (⋃ n, t n) = ⨆ n, μ (t n) by
    simp only [← ht, Function.apply_extend μ, ← iSup_eq_iUnion, iSup_extend_bot he,
      Function.comp_def, Pi.bot_apply, bot_eq_empty, measure_empty] at this
    exact this.trans (iSup_extend_bot he _)
  clear! ι
  -- The `≥` inequality is trivial
  refine le_antisymm ?_ (iSup_le fun i => measure_mono <| subset_iUnion _ _)
  -- Choose `T n ⊇ t n` of the same measure, put `Td n = disjointed T`
  set T : Nat -> Set α := fun n => toMeasurable μ (t n)
  set Td : Nat -> Set α := disjointed T
  have hm : forall n, MeasurableSet (Td n) := .disjointed fun n => measurableSet_toMeasurable _ _
  calc
    μ (⋃ n, t n) = μ (⋃ n, Td n) := by rw [iUnion_disjointed, measure_iUnion_toMeasurable]
    _ <= ∑' n, μ (Td n) := measure_iUnion_le _
    _ = ⨆ I : Finset Nat, ∑ n in I, μ (Td n) := ENNReal.tsum_eq_iSup_sum
    _ <= ⨆ n, μ (t n) := iSup_le fun I => by
      rcases hd.finset_le I with ⟨N, hN⟩
      calc
        (∑ n in I, μ (Td n)) = μ (⋃ n in I, Td n) :=
          (measure_biUnion_finset ((disjoint_disjointed T).set_pairwise I) fun n _ => hm n).symm
        _ <= μ (⋃ n in I, T n) := measure_mono (iUnion₂_mono fun n _hn => disjointed_subset _ _)
        _ = μ (⋃ n in I, t n) := measure_biUnion_toMeasurable I.countable_toSet _
        _ <= μ (t N) := measure_mono (iUnion₂_subset hN)
        _ <= ⨆ n, μ (t n) := le_iSup (μ ∘ t) N

中文:
定理 _root_.Directed.measure_iUnion
  条件: [可数 ι] {s : ι -> 集合 α} (hd : Directed (· subseteq ·) s)
  证明: by
  -- WLOG, `ι = ℕ`
  rcases Countable.exists_injective_nat ι with ⟨e, he⟩
  generalize ht : Function.extend e s ⊥ = t
  replace hd : Directed (· subseteq ·) t := ht ▸ hd.extend_bot he
  suffices μ (⋃ n, t n) = ⨆ n, μ (t n) by
    simp only [← ht, Function.apply_extend μ, ← iSup_eq_iUnion, iSup_extend_bot he,
      Function.comp_def, Pi.bot_apply, bot_eq_empty, measure_empty] at this
    exact this.trans (iSup_extend_bot he _)
  clear! ι
  -- The `≥` inequality is trivial
  refine le_antisymm ?_ (iSup_le fun i => measure_mono <| subset_iUnion _ _)
  -- Choose `T n ⊇ t n` of the same measure, put `Td n = disjointed T`
  set T : Nat -> Set α := fun n => toMeasurable μ (t n)
  set Td : Nat -> Set α := disjointed T
  have hm : forall n, MeasurableSet (Td n) := .disjointed fun n => measurableSet_toMeasurable _ _
  calc
    μ (⋃ n, t n) = μ (⋃ n, Td n) := by rw [iUnion_disjointed, measure_iUnion_toMeasurable]
    _ <= ∑' n, μ (Td n) := measure_iUnion_le _
    _ = ⨆ I : Finset Nat, ∑ n in I, μ (Td n) := ENNReal.tsum_eq_iSup_sum
    _ <= ⨆ n, μ (t n) := iSup_le fun I => by
      rcases hd.finset_le I with ⟨N, hN⟩
      calc
        (∑ n in I, μ (Td n)) = μ (⋃ n in I, Td n) :=
          (measure_biUnion_finset ((disjoint_disjointed T).set_pairwise I) fun n _ => hm n).symm
        _ <= μ (⋃ n in I, T n) := measure_mono (iUnion₂_mono fun n _hn => disjointed_subset _ _)
        _ = μ (⋃ n in I, t n) := measure_biUnion_toMeasurable I.countable_toSet _
        _ <= μ (t N) := measure_mono (iUnion₂_subset hN)
        _ <= ⨆ n, μ (t n) := le_iSup (μ ∘ t) N
-/
theorem _root_.Directed.measure_iUnion [Countable ι] {s : ι -> Set α} (hd : Directed (· subseteq ·) s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) := by
  -- WLOG, `ι = ℕ`
  rcases Countable.exists_injective_nat ι with ⟨e, he⟩
  generalize ht : Function.extend e s ⊥ = t
  replace hd : Directed (· subseteq ·) t := ht ▸ hd.extend_bot he
  suffices μ (⋃ n, t n) = ⨆ n, μ (t n) by
    simp only [← ht, Function.apply_extend μ, ← iSup_eq_iUnion, iSup_extend_bot he,
      Function.comp_def, Pi.bot_apply, bot_eq_empty, measure_empty] at this
    exact this.trans (iSup_extend_bot he _)
  clear! ι
  -- The `≥` inequality is trivial
  refine le_antisymm ?_ (iSup_le fun i => measure_mono <| subset_iUnion _ _)
  -- Choose `T n ⊇ t n` of the same measure, put `Td n = disjointed T`
  set T : Nat -> Set α := fun n => toMeasurable μ (t n)
  set Td : Nat -> Set α := disjointed T
  have hm : forall n, MeasurableSet (Td n) := .disjointed fun n => measurableSet_toMeasurable _ _
  calc
    μ (⋃ n, t n) = μ (⋃ n, Td n) := by rw [iUnion_disjointed, measure_iUnion_toMeasurable]
    _ <= ∑' n, μ (Td n) := measure_iUnion_le _
    _ = ⨆ I : Finset Nat, ∑ n in I, μ (Td n) := ENNReal.tsum_eq_iSup_sum
    _ <= ⨆ n, μ (t n) := iSup_le fun I => by
      rcases hd.finset_le I with ⟨N, hN⟩
      calc
        (∑ n in I, μ (Td n)) = μ (⋃ n in I, Td n) :=
          (measure_biUnion_finset ((disjoint_disjointed T).set_pairwise I) fun n _ => hm n).symm
        _ <= μ (⋃ n in I, T n) := measure_mono (iUnion₂_mono fun n _hn => disjointed_subset _ _)
        _ = μ (⋃ n in I, t n) := measure_biUnion_toMeasurable I.countable_toSet _
        _ <= μ (t N) := measure_mono (iUnion₂_subset hN)
        _ <= ⨆ n, μ (t n) := le_iSup (μ ∘ t) N

/--
theorem `_root_.Monotone.measure_iUnion` / 定理 `_root_.Monotone.measure_iUnion`

English:
theorem _root_.Monotone.measure_iUnion
  statement: [Preorder ι] [IsDirectedOrder ι]
  proof: by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp
  | inr _ =>
    rcases exists_seq_monotone_tendsto_atTop_atTop ι with ⟨x, hxm, hx⟩
    rw [← hs.iUnion_comp_tendsto_atTop hx]; rw [← Monotone.iSup_comp_tendsto_atTop _ hx]
    exacts [(hs.comp hxm).directed_le.measure_iUnion, fun _ _ h => measure_mono (hs h)]

中文:
定理 _root_.递增.measure_iUnion
  结论: [预序 ι] [IsDirectedOrder ι]
  证明: by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp
  | inr _ =>
    rcases exists_seq_monotone_tendsto_atTop_atTop ι with ⟨x, hxm, hx⟩
    rw [← hs.iUnion_comp_tendsto_atTop hx]; rw [← Monotone.iSup_comp_tendsto_atTop _ hx]
    exacts [(hs.comp hxm).directed_le.measure_iUnion, fun _ _ h => measure_mono (hs h)]

Depends on / 依赖: Monotone, Monotone.iSup_comp_tendsto_atTop, directed_le, directed_le.measure_iUnion, exacts, exists_seq_monotone_tendsto_atTop_atTop, hs.comp, hs.iUnion_comp_tendsto_atTop, iSup_comp_tendsto_atTop, iUnion_comp_tendsto_atTop, isEmpty_or_nonempty, measure_iUnion, measure_mono
-/
theorem _root_.Monotone.measure_iUnion [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι -> Set α} (hs : Monotone s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) := by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp
  | inr _ =>
    rcases exists_seq_monotone_tendsto_atTop_atTop ι with ⟨x, hxm, hx⟩
    rw [← hs.iUnion_comp_tendsto_atTop hx]; rw [← Monotone.iSup_comp_tendsto_atTop _ hx]
    exacts [(hs.comp hxm).directed_le.measure_iUnion, fun _ _ h => measure_mono (hs h)]

/--
theorem `_root_.Antitone.measure_iUnion` / 定理 `_root_.Antitone.measure_iUnion`

English:
theorem _root_.Antitone.measure_iUnion
  statement: [Preorder ι] [IsCodirectedOrder ι]
  proof: hs.dual_left.measure_iUnion

中文:
定理 _root_.递减.measure_iUnion
  结论: [预序 ι] [IsCodirectedOrder ι]
  证明: hs.dual_left.measure_iUnion

Depends on / 依赖: dual_left, hs.dual_left.measure_iUnion, measure_iUnion
-/
theorem _root_.Antitone.measure_iUnion [Preorder ι] [IsCodirectedOrder ι]
    [(atBot : Filter ι).IsCountablyGenerated] {s : ι -> Set α} (hs : Antitone s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) :=
  hs.dual_left.measure_iUnion

/--
theorem `measure_iUnion_eq_iSup_accumulate` / 定理 `measure_iUnion_eq_iSup_accumulate`

English:
theorem measure_iUnion_eq_iSup_accumulate
  statement: [Preorder ι] [IsDirectedOrder ι]
  proof: by
  rw [← iUnion_accumulate]
  exact monotone_accumulate.measure_iUnion

中文:
定理 measure_iUnion_eq_iSup_accumulate
  结论: [预序 ι] [IsDirectedOrder ι]
  证明: by
  rw [← iUnion_accumulate]
  exact monotone_accumulate.measure_iUnion

Depends on / 依赖: iUnion_accumulate, measure_iUnion, monotone_accumulate, monotone_accumulate.measure_iUnion
-/
theorem measure_iUnion_eq_iSup_accumulate [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] {f : ι -> Set α} :
    μ (⋃ i, f i) = ⨆ i, μ (accumulate f i) := by
  rw [← iUnion_accumulate]
  exact monotone_accumulate.measure_iUnion

/--
theorem `measure_biUnion_eq_iSup` / 定理 `measure_biUnion_eq_iSup`

English:
theorem measure_biUnion_eq_iSup
  statement: {s : ι -> Set α} {t : Set ι} (ht : t.Countable)
  proof: by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion]; rw [hd.directed_val.measure_iUnion]; rw [← iSup_subtype'']

中文:
定理 measure_biUnion_eq_iSup
  结论: {s : ι -> 集合 α} {t : 集合 ι} (ht : t.可数)
  证明: by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion]; rw [hd.directed_val.measure_iUnion]; rw [← iSup_subtype'']

Depends on / 依赖: biUnion_eq_iUnion, directed_val, hd.directed_val.measure_iUnion, ht.to_subtype, iSup_subtype, measure_iUnion, to_subtype
-/
theorem measure_biUnion_eq_iSup {s : ι -> Set α} {t : Set ι} (ht : t.Countable)
    (hd : DirectedOn ((· subseteq ·) on s) t) : μ (⋃ i in t, s i) = ⨆ i in t, μ (s i) := by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion]; rw [hd.directed_val.measure_iUnion]; rw [← iSup_subtype'']

/--
theorem `_root_.Directed.measure_iInter` / 定理 `_root_.Directed.measure_iInter`

English:
theorem _root_.Directed.measure_iInter
  statement: [Countable ι] {s : ι -> Set α}
  proof: by
  rcases hfin with ⟨k, hk⟩
  have : forall t subseteq s k, μ t != ∞ := fun t ht => ne_top_of_le_ne_top hk (measure_mono ht)
  rw [← ENNReal.sub_sub_cancel hk (iInf_le (fun i => μ (s i)) k)]; rw [ENNReal.sub_iInf]; rw [←
    ENNReal.sub_sub_cancel hk (measure_mono (iInter_subset _ k))]; rw [←
    measure_sdiff (iInter_subset _ k) (.iInter h) (this _ (iInter_subset _ k))]; rw [sdiff_iInter]; rw [Directed.measure_iUnion]
  · congr 1
    refine le_antisymm (iSup_mono' fun i => ?_) (iSup_mono fun i => le_measure_sdiff)
    rcases hd i k with ⟨j, hji, hjk⟩
    use j
    rw [← measure_sdiff hjk (h _) (this _ hjk)]
    gcongr
  · exact hd.mono_comp _ fun _ _ => sdiff_subset_sdiff_right

中文:
定理 _root_.Directed.measure_i整数er
  结论: [可数 ι] {s : ι -> 集合 α}
  证明: by
  rcases hfin with ⟨k, hk⟩
  have : forall t subseteq s k, μ t != ∞ := fun t ht => ne_top_of_le_ne_top hk (measure_mono ht)
  rw [← ENNReal.sub_sub_cancel hk (iInf_le (fun i => μ (s i)) k)]; rw [ENNReal.sub_iInf]; rw [←
    ENNReal.sub_sub_cancel hk (measure_mono (iInter_subset _ k))]; rw [←
    measure_sdiff (iInter_subset _ k) (.iInter h) (this _ (iInter_subset _ k))]; rw [sdiff_iInter]; rw [Directed.measure_iUnion]
  · congr 1
    refine le_antisymm (iSup_mono' fun i => ?_) (iSup_mono fun i => le_measure_sdiff)
    rcases hd i k with ⟨j, hji, hjk⟩
    use j
    rw [← measure_sdiff hjk (h _) (this _ hjk)]
    gcongr
  · exact hd.mono_comp _ fun _ _ => sdiff_subset_sdiff_right

Depends on / 依赖: Directed, Directed.measure_iUnion, ENNReal, ENNReal.sub_iInf, ENNReal.sub_sub_cancel, iInf_le, iInter, iInter_subset, iSup_mono, le_antisymm, le_measure_sdif, measure_iUnion, measure_mono, measure_sdiff, ne_top_of_le_ne_top, sdiff_iInter, sub_iInf, sub_sub_cancel, subseteq
-/
theorem _root_.Directed.measure_iInter [Countable ι] {s : ι -> Set α}
    (h : forall i, NullMeasurableSet (s i) μ) (hd : Directed (· ⊇ ·) s) (hfin : exists i, μ (s i) != ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  rcases hfin with ⟨k, hk⟩
  have : forall t subseteq s k, μ t != ∞ := fun t ht => ne_top_of_le_ne_top hk (measure_mono ht)
  rw [← ENNReal.sub_sub_cancel hk (iInf_le (fun i => μ (s i)) k)]; rw [ENNReal.sub_iInf]; rw [←
    ENNReal.sub_sub_cancel hk (measure_mono (iInter_subset _ k))]; rw [←
    measure_sdiff (iInter_subset _ k) (.iInter h) (this _ (iInter_subset _ k))]; rw [sdiff_iInter]; rw [Directed.measure_iUnion]
  · congr 1
    refine le_antisymm (iSup_mono' fun i => ?_) (iSup_mono fun i => le_measure_sdiff)
    rcases hd i k with ⟨j, hji, hjk⟩
    use j
    rw [← measure_sdiff hjk (h _) (this _ hjk)]
    gcongr
  · exact hd.mono_comp _ fun _ _ => sdiff_subset_sdiff_right

/--
theorem `_root_.Monotone.measure_iInter` / 定理 `_root_.Monotone.measure_iInter`

English:
theorem _root_.Monotone.measure_iInter
  statement: [Preorder ι] [IsCodirectedOrder ι]
  proof: by
  refine le_antisymm (le_iInf fun i => measure_mono <| iInter_subset _ _) ?_
  have := hfin.nonempty
  rcases exists_seq_antitone_tendsto_atTop_atBot ι with ⟨x, hxm, hx⟩
  calc
    ⨅ i, μ (s i) <= ⨅ n, μ (s (x n)) := le_iInf_comp (μ ∘ s) x
    _ = μ (⋂ n, s (x n)) := by
refine .symm (hs.comp_antitone hxm).directed_ge.measure_iInter (fun n => hsm _) ?_
      rcases hfin with ⟨k, hk⟩
      rcases (hx.eventually_le_atBot k).exists with ⟨n, hn⟩
exact ⟨n, ne_top_of_le_ne_top hk measure_mono hs hn⟩
    _ <= μ (⋂ i, s i) := by
refine measure_mono iInter_mono' fun i => ?_
      rcases (hx.eventually_le_atBot i).exists with ⟨n, hn⟩
      exact ⟨n, hs hn⟩

中文:
定理 _root_.递增.measure_i整数er
  结论: [预序 ι] [IsCodirectedOrder ι]
  证明: by
  refine le_antisymm (le_iInf fun i => measure_mono <| iInter_subset _ _) ?_
  have := hfin.nonempty
  rcases exists_seq_antitone_tendsto_atTop_atBot ι with ⟨x, hxm, hx⟩
  calc
    ⨅ i, μ (s i) <= ⨅ n, μ (s (x n)) := le_iInf_comp (μ ∘ s) x
    _ = μ (⋂ n, s (x n)) := by
refine .symm (hs.comp_antitone hxm).directed_ge.measure_iInter (fun n => hsm _) ?_
      rcases hfin with ⟨k, hk⟩
      rcases (hx.eventually_le_atBot k).exists with ⟨n, hn⟩
exact ⟨n, ne_top_of_le_ne_top hk measure_mono hs hn⟩
    _ <= μ (⋂ i, s i) := by
refine measure_mono iInter_mono' fun i => ?_
      rcases (hx.eventually_le_atBot i).exists with ⟨n, hn⟩
      exact ⟨n, hs hn⟩

Depends on / 依赖: comp_antitone, directed_ge, directed_ge.measure_iInter, eventually_le_atBot, exists_seq_antitone_tendsto_atTop_atBot, hfin.nonempty, hs.comp_antitone, hx.eventually_le_atBot, iInter_subset, le_antisymm, le_iInf, le_iInf_comp, measure_iInter, measure_mono, ne_top_of_le_ne_top, nonempty
-/
theorem _root_.Monotone.measure_iInter [Preorder ι] [IsCodirectedOrder ι]
    [(atBot : Filter ι).IsCountablyGenerated] {s : ι -> Set α} (hs : Monotone s)
    (hsm : forall i, NullMeasurableSet (s i) μ) (hfin : exists i, μ (s i) != ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  refine le_antisymm (le_iInf fun i => measure_mono <| iInter_subset _ _) ?_
  have := hfin.nonempty
  rcases exists_seq_antitone_tendsto_atTop_atBot ι with ⟨x, hxm, hx⟩
  calc
    ⨅ i, μ (s i) <= ⨅ n, μ (s (x n)) := le_iInf_comp (μ ∘ s) x
    _ = μ (⋂ n, s (x n)) := by
refine .symm (hs.comp_antitone hxm).directed_ge.measure_iInter (fun n => hsm _) ?_
      rcases hfin with ⟨k, hk⟩
      rcases (hx.eventually_le_atBot k).exists with ⟨n, hn⟩
exact ⟨n, ne_top_of_le_ne_top hk measure_mono hs hn⟩
    _ <= μ (⋂ i, s i) := by
refine measure_mono iInter_mono' fun i => ?_
      rcases (hx.eventually_le_atBot i).exists with ⟨n, hn⟩
      exact ⟨n, hs hn⟩

/--
theorem `measure_iInter_of_ae_monotone` / 定理 `measure_iInter_of_ae_monotone`

English:
theorem measure_iInter_of_ae_monotone
  statement: [Preorder ι] [IsCodirectedOrder ι]
  proof: by
  obtain ⟨i, hi⟩ := hfin
  have : Nonempty ι := ⟨i⟩
  let t : ι -> Set α := fun i => s i inter {ω | Monotone (ω in s ·)}
  have hst (i : ι) : s i =ᵐ[μ] t i := by
    filter_upwards [hs] with ω hω
    suffices ω in s i ↔ ω in t i from propext this
    simpa [t] using fun _ => hω
  have hMono : Monotone t := fun i j hij ω hω => ⟨hω.2 hij hω.1, hω.2⟩
  rw [iInf_congr <| fun i => measure_congr <| hst i]; rw [← hMono.measure_iInter (fun i => (hsm i).congr (hst i)) ⟨i]; rw [by rwa [← measure_congr (hst i)]⟩]
  refine measure_congr ?_
  nth_rw 1 [← iInter_inter, ← inter_univ (⋂ i, s i)]
  exact ae_eq_set_inter (by rfl) (ae_eq_univ.2 hs).symm

中文:
定理 measure_i整数er_of_ae_monotone
  结论: [预序 ι] [IsCodirectedOrder ι]
  证明: by
  obtain ⟨i, hi⟩ := hfin
  have : Nonempty ι := ⟨i⟩
  let t : ι -> Set α := fun i => s i inter {ω | Monotone (ω in s ·)}
  have hst (i : ι) : s i =ᵐ[μ] t i := by
    filter_upwards [hs] with ω hω
    suffices ω in s i ↔ ω in t i from propext this
    simpa [t] using fun _ => hω
  have hMono : Monotone t := fun i j hij ω hω => ⟨hω.2 hij hω.1, hω.2⟩
  rw [iInf_congr <| fun i => measure_congr <| hst i]; rw [← hMono.measure_iInter (fun i => (hsm i).congr (hst i)) ⟨i]; rw [by rwa [← measure_congr (hst i)]⟩]
  refine measure_congr ?_
  nth_rw 1 [← iInter_inter, ← inter_univ (⋂ i, s i)]
  exact ae_eq_set_inter (by rfl) (ae_eq_univ.2 hs).symm

Depends on / 依赖: Monotone, Nonempty, filter_upwards, hMono.measure_iInter, iInf_congr, measur, measure_congr, measure_iInter, propext
-/
theorem measure_iInter_of_ae_monotone [Preorder ι] [IsCodirectedOrder ι]
    [(atBot : Filter ι).IsCountablyGenerated] {s : ι -> Set α} (hs : forallᵐ ω ∂μ, Monotone (ω in s ·))
    (hsm : forall i, NullMeasurableSet (s i) μ) (hfin : exists i, μ (s i) != ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  obtain ⟨i, hi⟩ := hfin
  have : Nonempty ι := ⟨i⟩
  let t : ι -> Set α := fun i => s i inter {ω | Monotone (ω in s ·)}
  have hst (i : ι) : s i =ᵐ[μ] t i := by
    filter_upwards [hs] with ω hω
    suffices ω in s i ↔ ω in t i from propext this
    simpa [t] using fun _ => hω
  have hMono : Monotone t := fun i j hij ω hω => ⟨hω.2 hij hω.1, hω.2⟩
  rw [iInf_congr <| fun i => measure_congr <| hst i]; rw [← hMono.measure_iInter (fun i => (hsm i).congr (hst i)) ⟨i]; rw [by rwa [← measure_congr (hst i)]⟩]
  refine measure_congr ?_
  nth_rw 1 [← iInter_inter, ← inter_univ (⋂ i, s i)]
  exact ae_eq_set_inter (by rfl) (ae_eq_univ.2 hs).symm

/--
theorem `_root_.Antitone.measure_iInter` / 定理 `_root_.Antitone.measure_iInter`

English:
theorem _root_.Antitone.measure_iInter
  statement: [Preorder ι] [IsDirectedOrder ι]
  proof: hs.dual_left.measure_iInter hsm hfin

中文:
定理 _root_.递减.measure_i整数er
  结论: [预序 ι] [IsDirectedOrder ι]
  证明: hs.dual_left.measure_iInter hsm hfin

Depends on / 依赖: dual_left, hs.dual_left.measure_iInter, measure_iInter
-/
theorem _root_.Antitone.measure_iInter [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι -> Set α} (hs : Antitone s)
    (hsm : forall i, NullMeasurableSet (s i) μ) (hfin : exists i, μ (s i) != ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) :=
  hs.dual_left.measure_iInter hsm hfin

/--
lemma `measure_iInter_of_ae_antitone` / 引理 `measure_iInter_of_ae_antitone`

English:
lemma measure_iInter_of_ae_antitone
  statement: [Preorder ι] [IsDirectedOrder ι]
  proof: by
  refine measure_iInter_of_ae_monotone (ι := ιᵒᵈ) ?_ hsm hfin
  filter_upwards [hs] with ω hω using hω.dual_left

中文:
引理 measure_i整数er_of_ae_antitone
  结论: [预序 ι] [IsDirectedOrder ι]
  证明: by
  refine measure_iInter_of_ae_monotone (ι := ιᵒᵈ) ?_ hsm hfin
  filter_upwards [hs] with ω hω using hω.dual_left

Depends on / 依赖: dual_left, filter_upwards, measure_iInter_of_ae_monotone
-/
lemma measure_iInter_of_ae_antitone [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι -> Set α} (hs : forallᵐ ω ∂μ, Antitone (ω in s ·))
    (hsm : forall (i : ι), NullMeasurableSet (s i) μ) (hfin : exists i, μ (s i) != ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  refine measure_iInter_of_ae_monotone (ι := ιᵒᵈ) ?_ hsm hfin
  filter_upwards [hs] with ω hω using hω.dual_left

/--
theorem `measure_iInter_eq_iInf_measure_iInter_le` / 定理 `measure_iInter_eq_iInf_measure_iInter_le`

English:
theorem measure_iInter_eq_iInf_measure_iInter_le
  statement: {α ι : Type*} {_ : MeasurableSpace α}
  proof: by
  rw [← Antitone.measure_iInter]
  · rw [iInter_comm]
exact congrArg μ iInter_congr fun i => (biInf_const nonempty_Ici).symm
  · exact fun i j h => biInter_mono (Iic_subset_Iic.2 h) fun _ _ => Set.Subset.rfl
  · exact fun i => .biInter (to_countable _) fun _ _ => h _
· refine hfin.imp fun k hk => ne_top_of_le_ne_top hk measure_mono iInter₂_subset k ?_
    rfl

中文:
定理 measure_i整数er_eq_iInf_measure_i整数er_le
  结论: {α ι : 类型} {_ : 可测空间 α}
  证明: by
  rw [← Antitone.measure_iInter]
  · rw [iInter_comm]
exact congrArg μ iInter_congr fun i => (biInf_const nonempty_Ici).symm
  · exact fun i j h => biInter_mono (Iic_subset_Iic.2 h) fun _ _ => Set.Subset.rfl
  · exact fun i => .biInter (to_countable _) fun _ _ => h _
· refine hfin.imp fun k hk => ne_top_of_le_ne_top hk measure_mono iInter₂_subset k ?_
    rfl

Depends on / 依赖: Antitone, Antitone.measure_iInter, Iic_subset_Iic, Set.Subset.rfl, Subset, biInf_const, biInter, biInter_mono, hfin.imp, iInter_comm, iInter_congr, measure_iInter, measure_mono, ne_top_of_le_ne_top, nonempty_Ici, to_countable
-/
theorem measure_iInter_eq_iInf_measure_iInter_le {α ι : Type*} {_ : MeasurableSpace α}
    {μ : Measure α} [Countable ι] [Preorder ι] [IsDirectedOrder ι]
    {f : ι -> Set α} (h : forall i, NullMeasurableSet (f i) μ) (hfin : exists i, μ (f i) != ∞) :
    μ (⋂ i, f i) = ⨅ i, μ (⋂ j <= i, f j) := by
  rw [← Antitone.measure_iInter]
  · rw [iInter_comm]
exact congrArg μ iInter_congr fun i => (biInf_const nonempty_Ici).symm
  · exact fun i j h => biInter_mono (Iic_subset_Iic.2 h) fun _ _ => Set.Subset.rfl
  · exact fun i => .biInter (to_countable _) fun _ _ => h _
· refine hfin.imp fun k hk => ne_top_of_le_ne_top hk measure_mono iInter₂_subset k ?_
    rfl

/--
theorem `tendsto_measure_iUnion_atTop` / 定理 `tendsto_measure_iUnion_atTop`

English:
theorem tendsto_measure_iUnion_atTop
  statement: [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
  proof: by
  refine .of_neBot_imp fun h => ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iUnion]
exact tendsto_atTop_iSup fun n m hnm => measure_mono hm hnm

中文:
定理 tendsto_measure_iUnion_atTop
  结论: [预序 ι] [是余untablyGenerated (atTop : 滤子 ι)]
  证明: by
  refine .of_neBot_imp fun h => ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iUnion]
exact tendsto_atTop_iSup fun n m hnm => measure_mono hm hnm

Depends on / 依赖: atTop_neBot_iff, hm.measure_iUnion, measure_iUnion, measure_mono, of_neBot_imp, tendsto_atTop_iSup
-/
theorem tendsto_measure_iUnion_atTop [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
    {s : ι -> Set α} (hm : Monotone s) : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋃ n, s n))) := by
  refine .of_neBot_imp fun h => ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iUnion]
exact tendsto_atTop_iSup fun n m hnm => measure_mono hm hnm

/--
theorem `tendsto_measure_iUnion_atBot` / 定理 `tendsto_measure_iUnion_atBot`

English:
theorem tendsto_measure_iUnion_atBot
  statement: [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)]
  proof: tendsto_measure_iUnion_atTop (ι := ιᵒᵈ) hm.dual_left

中文:
定理 tendsto_measure_iUnion_atBot
  结论: [预序 ι] [是余untablyGenerated (atBot : 滤子 ι)]
  证明: tendsto_measure_iUnion_atTop (ι := ιᵒᵈ) hm.dual_left

Depends on / 依赖: dual_left, hm.dual_left, tendsto_measure_iUnion_atTop
-/
theorem tendsto_measure_iUnion_atBot [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)]
    {s : ι -> Set α} (hm : Antitone s) : Tendsto (μ ∘ s) atBot (𝓝 (μ (⋃ n, s n))) :=
  tendsto_measure_iUnion_atTop (ι := ιᵒᵈ) hm.dual_left

/--
theorem `tendsto_measure_iUnion_accumulate` / 定理 `tendsto_measure_iUnion_accumulate`

English:
theorem tendsto_measure_iUnion_accumulate
  statement: {α ι : Type*}
  proof: by
  refine .of_neBot_imp fun h => ?_
  have := (atTop_neBot_iff.1 h).2
  rw [measure_iUnion_eq_iSup_accumulate]
  exact tendsto_atTop_iSup fun i j hij => by gcongr

中文:
定理 tendsto_measure_iUnion_accumulate
  结论: {α ι : 类型}
  证明: by
  refine .of_neBot_imp fun h => ?_
  have := (atTop_neBot_iff.1 h).2
  rw [measure_iUnion_eq_iSup_accumulate]
  exact tendsto_atTop_iSup fun i j hij => by gcongr

Depends on / 依赖: atTop_neBot_iff, measure_iUnion_eq_iSup_accumulate, of_neBot_imp, tendsto_atTop_iSup
-/
theorem tendsto_measure_iUnion_accumulate {α ι : Type*}
    [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
    {_ : MeasurableSpace α} {μ : Measure α} {f : ι -> Set α} :
    Tendsto (fun i => μ (accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  refine .of_neBot_imp fun h => ?_
  have := (atTop_neBot_iff.1 h).2
  rw [measure_iUnion_eq_iSup_accumulate]
  exact tendsto_atTop_iSup fun i j hij => by gcongr

/--
theorem `tendsto_measure_iInter_atTop` / 定理 `tendsto_measure_iInter_atTop`

English:
theorem tendsto_measure_iInter_atTop
  statement: [Preorder ι]
  proof: by
  refine .of_neBot_imp fun h => ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iInter hs hf]
exact tendsto_atTop_iInf fun n m hnm => measure_mono hm hnm

中文:
定理 tendsto_measure_i整数er_atTop
  结论: [预序 ι]
  证明: by
  refine .of_neBot_imp fun h => ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iInter hs hf]
exact tendsto_atTop_iInf fun n m hnm => measure_mono hm hnm

Depends on / 依赖: atTop_neBot_iff, hm.measure_iInter, measure_iInter, measure_mono, of_neBot_imp, tendsto_atTop_iInf
-/
theorem tendsto_measure_iInter_atTop [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α}
    (hs : forall i, NullMeasurableSet (s i) μ) (hm : Antitone s) (hf : exists i, μ (s i) != ∞) :
    Tendsto (μ ∘ s) atTop (𝓝 (μ (⋂ n, s n))) := by
  refine .of_neBot_imp fun h => ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iInter hs hf]
exact tendsto_atTop_iInf fun n m hnm => measure_mono hm hnm

/--
theorem `tendsto_measure_iInter_atBot` / 定理 `tendsto_measure_iInter_atBot`

English:
theorem tendsto_measure_iInter_atBot
  statement: [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)]
  proof: tendsto_measure_iInter_atTop (ι := ιᵒᵈ) hs hm.dual_left hf

中文:
定理 tendsto_measure_i整数er_atBot
  结论: [预序 ι] [是余untablyGenerated (atBot : 滤子 ι)]
  证明: tendsto_measure_iInter_atTop (ι := ιᵒᵈ) hs hm.dual_left hf

Depends on / 依赖: dual_left, hm.dual_left, tendsto_measure_iInter_atTop
-/
theorem tendsto_measure_iInter_atBot [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)]
    {s : ι -> Set α} (hs : forall i, NullMeasurableSet (s i) μ) (hm : Monotone s)
    (hf : exists i, μ (s i) != ∞) : Tendsto (μ ∘ s) atBot (𝓝 (μ (⋂ n, s n))) :=
  tendsto_measure_iInter_atTop (ι := ιᵒᵈ) hs hm.dual_left hf

/--
theorem `tendsto_measure_iInter_le` / 定理 `tendsto_measure_iInter_le`

English:
theorem tendsto_measure_iInter_le
  statement: {α ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
  proof: by
  refine .of_neBot_imp fun hne => ?_
  cases atTop_neBot_iff.mp hne
  rw [measure_iInter_eq_iInf_measure_iInter_le hm hf]
  exact tendsto_atTop_iInf
fun i j hij => measure_mono biInter_subset_biInter_left fun k hki => le_trans hki hij

中文:
定理 tendsto_measure_i整数er_le
  结论: {α ι : 类型} {_ : 可测空间 α} {μ : 测度 α}
  证明: by
  refine .of_neBot_imp fun hne => ?_
  cases atTop_neBot_iff.mp hne
  rw [measure_iInter_eq_iInf_measure_iInter_le hm hf]
  exact tendsto_atTop_iInf
fun i j hij => measure_mono biInter_subset_biInter_left fun k hki => le_trans hki hij

Depends on / 依赖: atTop_neBot_iff, atTop_neBot_iff.mp, biInter_subset_biInter_left, le_trans, measure_iInter_eq_iInf_measure_iInter_le, measure_mono, of_neBot_imp, tendsto_atTop_iInf
-/
theorem tendsto_measure_iInter_le {α ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [Countable ι] [Preorder ι] {f : ι -> Set α} (hm : forall i, NullMeasurableSet (f i) μ)
    (hf : exists i, μ (f i) != ∞) :
    Tendsto (fun i => μ (⋂ j <= i, f j)) atTop (𝓝 (μ (⋂ i, f i))) := by
  refine .of_neBot_imp fun hne => ?_
  cases atTop_neBot_iff.mp hne
  rw [measure_iInter_eq_iInf_measure_iInter_le hm hf]
  exact tendsto_atTop_iInf
fun i j hij => measure_mono biInter_subset_biInter_left fun k hki => le_trans hki hij

/--
theorem `exists_measure_iInter_lt` / 定理 `exists_measure_iInter_lt`

English:
theorem exists_measure_iInter_lt
  statement: {α ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
  proof: by
  let F m := μ (⋂ n <= m, f n)
  have hFAnti : Antitone F :=
      fun i j hij => measure_mono (biInter_subset_biInter_left fun k hki => le_trans hki hij)
  suffices Filter.Tendsto F Filter.atTop (𝓝 0) by
    let _ := hfin.nonempty
    rw [ENNReal.tendsto_atTop_zero_iff_lt_of_antitone hFAnti] at this
    exact this ε hε
  have hzero : μ (⋂ n, f n) = 0 := by
    simp only [hfem, measure_empty]
  rw [← hzero]
  exact tendsto_measure_iInter_le hm hfin

中文:
定理 存在_measure_i整数er_lt
  结论: {α ι : 类型} {_ : 可测空间 α} {μ : 测度 α}
  证明: by
  let F m := μ (⋂ n <= m, f n)
  have hFAnti : Antitone F :=
      fun i j hij => measure_mono (biInter_subset_biInter_left fun k hki => le_trans hki hij)
  suffices Filter.Tendsto F Filter.atTop (𝓝 0) by
    let _ := hfin.nonempty
    rw [ENNReal.tendsto_atTop_zero_iff_lt_of_antitone hFAnti] at this
    exact this ε hε
  have hzero : μ (⋂ n, f n) = 0 := by
    simp only [hfem, measure_empty]
  rw [← hzero]
  exact tendsto_measure_iInter_le hm hfin

Depends on / 依赖: Antitone, ENNReal, ENNReal.tendsto_atTop_zero_iff_lt_of_antitone, Filter, Filter.Tendsto, Filter.atTop, Tendsto, biInter_subset_biInter_left, hFAnti, hfin.nonempty, le_trans, measure_empty, measure_mono, nonempty, tendsto_atTop_zero_iff_lt_of_antitone, tendsto_measure_iInter_le
-/
theorem exists_measure_iInter_lt {α ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SemilatticeSup ι] [Countable ι] {f : ι -> Set α}
    (hm : forall i, NullMeasurableSet (f i) μ) {ε : Real>=0∞} (hε : 0 < ε) (hfin : exists i, μ (f i) != ∞)
    (hfem : ⋂ n, f n = ∅) : exists m, μ (⋂ n <= m, f n) < ε := by
  let F m := μ (⋂ n <= m, f n)
  have hFAnti : Antitone F :=
      fun i j hij => measure_mono (biInter_subset_biInter_left fun k hki => le_trans hki hij)
  suffices Filter.Tendsto F Filter.atTop (𝓝 0) by
    let _ := hfin.nonempty
    rw [ENNReal.tendsto_atTop_zero_iff_lt_of_antitone hFAnti] at this
    exact this ε hε
  have hzero : μ (⋂ n, f n) = 0 := by
    simp only [hfem, measure_empty]
  rw [← hzero]
  exact tendsto_measure_iInter_le hm hfin

/--
theorem `tendsto_measure_biInter_gt` / 定理 `tendsto_measure_biInter_gt`

English:
theorem tendsto_measure_biInter_gt
  statement: {ι : Type*} [LinearOrder ι] [TopologicalSpace ι]
  proof: by
  by_cases ha : Order.IsPredPrelimit a
  · have : (atBot : Filter (Ioi a)).IsCountablyGenerated := by
      rw [← comap_coe_Ioi_nhdsGT a ha]
      infer_instance
    simp_rw [← map_coe_Ioi_atBot a ha, tendsto_map'_iff, ← mem_Ioi, biInter_eq_iInter]
    apply tendsto_measure_iInter_atBot
    · rwa [Subtype.forall]
    · exact fun i j h => hm i j i.2 h
    · simpa only [Subtype.exists, exists_prop]
  · rw [Order.not_isPredPrelimit_iff] at ha
    rcases ha with ⟨b, hab⟩
    simp [hab.nhdsGT]

中文:
定理 tendsto_measure_bi整数er_gt
  结论: {ι : 类型} [线性序 ι] [拓扑空间 ι]
  证明: by
  by_cases ha : Order.IsPredPrelimit a
  · have : (atBot : Filter (Ioi a)).IsCountablyGenerated := by
      rw [← comap_coe_Ioi_nhdsGT a ha]
      infer_instance
    simp_rw [← map_coe_Ioi_atBot a ha, tendsto_map'_iff, ← mem_Ioi, biInter_eq_iInter]
    apply tendsto_measure_iInter_atBot
    · rwa [Subtype.forall]
    · exact fun i j h => hm i j i.2 h
    · simpa only [Subtype.exists, exists_prop]
  · rw [Order.not_isPredPrelimit_iff] at ha
    rcases ha with ⟨b, hab⟩
    simp [hab.nhdsGT]

Depends on / 依赖: Filter, IsCountablyGenerated, IsPredPrelimit, Order.IsPredPrelimit, Order.not_isPredPrelimit_iff, Subtype, Subtype.exists, Subtype.forall, _iff, biInter_eq_iInter, comap_coe_Ioi_nhdsGT, exists_prop, hab.nhdsGT, infer_instance, map_coe_Ioi_atBot, mem_Ioi, nhdsGT, not_isPredPrelimit_iff, simp_rw, tendsto_map
-/
theorem tendsto_measure_biInter_gt {ι : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [FirstCountableTopology ι] {s : ι -> Set α}
    {a : ι} (hs : forall r > a, NullMeasurableSet (s r) μ) (hm : forall i j, a < i -> i <= j -> s i subseteq s j)
    (hf : exists r > a, μ (s r) != ∞) : Tendsto (μ ∘ s) (𝓝[Ioi a] a) (𝓝 (μ (⋂ r > a, s r))) := by
  by_cases ha : Order.IsPredPrelimit a
  · have : (atBot : Filter (Ioi a)).IsCountablyGenerated := by
      rw [← comap_coe_Ioi_nhdsGT a ha]
      infer_instance
    simp_rw [← map_coe_Ioi_atBot a ha, tendsto_map'_iff, ← mem_Ioi, biInter_eq_iInter]
    apply tendsto_measure_iInter_atBot
    · rwa [Subtype.forall]
    · exact fun i j h => hm i j i.2 h
    · simpa only [Subtype.exists, exists_prop]
  · rw [Order.not_isPredPrelimit_iff] at ha
    rcases ha with ⟨b, hab⟩
    simp [hab.nhdsGT]

/--
theorem `measure_if` / 定理 `measure_if`

English:
theorem measure_if
  given: {x : β} {t : Set β} {s : Set α} [Decidable (x in t)]
  proof: by split_ifs with h <;> simp [h]

中文:
定理 measure_if
  条件: {x : β} {t : 集合 β} {s : 集合 α} [可判定 (x in t)]
  证明: by split_ifs with h <;> simp [h]

Depends on / 依赖: split_ifs
-/
theorem measure_if {x : β} {t : Set β} {s : Set α} [Decidable (x in t)] :
    μ (if x in t then s else ∅) = indicator t (fun _ => μ s) x := by split_ifs with h <;> simp [h]

/--
lemma `ext_of_measurableAtoms` / 引理 `ext_of_measurableAtoms`

English:
lemma ext_of_measurableAtoms
  statement: [Countable α] {μ ν : Measure α}
  proof: by
  ext s hs
  have h1 : s = ⋃ x in s, measurableAtom x := by
    ext y
    simp only [mem_iUnion, exists_prop]
    refine ⟨fun hy => ?_, fun ⟨x, hx, hy⟩ => ?_⟩
    · exact ⟨y, hy, mem_measurableAtom_self y⟩
    · exact mem_of_mem_measurableAtom hy hs hx
  rw [← sUnion_image] at h1
  rw [h1]
  have h_count : (measurableAtom '' s).Countable := s.to_countable.image _
  have h_disj : (measurableAtom '' s).Pairwise Disjoint := by
    intro t ht t' ht' h_eq
    obtain ⟨y, hys, hy⟩ := ht
    obtain ⟨y', hy's, hy'⟩ := ht'
    rw [← hy]; rw [← hy'] at h_eq ⊢
    refine disjoint_measurableAtom_of_notMem fun hyy' => h_eq ?_
    exact measurableAtom_eq_of_mem hyy'
  have h_meas (t) (ht : t in measurableAtom '' s) : MeasurableSet t := by
    obtain ⟨x, hxs, hx⟩ := ht
    rw [← hx]
    exact MeasurableSet.measurableAtom_of_countable x
  rw [measure_sUnion h_count h_disj h_meas]; rw [measure_sUnion h_count h_disj h_meas]
  congr with s'
  have hs' := s'.2
  obtain ⟨x, hxs, hx⟩ := hs'
  rw [← hx]
  exact h x

中文:
引理 ext_of_measurableAtoms
  结论: [可数 α] {μ ν : 测度 α}
  证明: by
  ext s hs
  have h1 : s = ⋃ x in s, measurableAtom x := by
    ext y
    simp only [mem_iUnion, exists_prop]
    refine ⟨fun hy => ?_, fun ⟨x, hx, hy⟩ => ?_⟩
    · exact ⟨y, hy, mem_measurableAtom_self y⟩
    · exact mem_of_mem_measurableAtom hy hs hx
  rw [← sUnion_image] at h1
  rw [h1]
  have h_count : (measurableAtom '' s).Countable := s.to_countable.image _
  have h_disj : (measurableAtom '' s).Pairwise Disjoint := by
    intro t ht t' ht' h_eq
    obtain ⟨y, hys, hy⟩ := ht
    obtain ⟨y', hy's, hy'⟩ := ht'
    rw [← hy]; rw [← hy'] at h_eq ⊢
    refine disjoint_measurableAtom_of_notMem fun hyy' => h_eq ?_
    exact measurableAtom_eq_of_mem hyy'
  have h_meas (t) (ht : t in measurableAtom '' s) : MeasurableSet t := by
    obtain ⟨x, hxs, hx⟩ := ht
    rw [← hx]
    exact MeasurableSet.measurableAtom_of_countable x
  rw [measure_sUnion h_count h_disj h_meas]; rw [measure_sUnion h_count h_disj h_meas]
  congr with s'
  have hs' := s'.2
  obtain ⟨x, hxs, hx⟩ := hs'
  rw [← hx]
  exact h x

Depends on / 依赖: Countable, Disjoint, Pairwise, exists_prop, h_count, h_disj, h_eq, measurableAtom, mem_iUnion, mem_measurableAtom_self, mem_of_mem_measurableAtom, s.to_countable.image, sUnion_image, to_countable
-/
lemma ext_of_measurableAtoms [Countable α] {μ ν : Measure α}
    (h : forall x, μ (measurableAtom x) = ν (measurableAtom x)) : μ = ν := by
  ext s hs
  have h1 : s = ⋃ x in s, measurableAtom x := by
    ext y
    simp only [mem_iUnion, exists_prop]
    refine ⟨fun hy => ?_, fun ⟨x, hx, hy⟩ => ?_⟩
    · exact ⟨y, hy, mem_measurableAtom_self y⟩
    · exact mem_of_mem_measurableAtom hy hs hx
  rw [← sUnion_image] at h1
  rw [h1]
  have h_count : (measurableAtom '' s).Countable := s.to_countable.image _
  have h_disj : (measurableAtom '' s).Pairwise Disjoint := by
    intro t ht t' ht' h_eq
    obtain ⟨y, hys, hy⟩ := ht
    obtain ⟨y', hy's, hy'⟩ := ht'
    rw [← hy]; rw [← hy'] at h_eq ⊢
    refine disjoint_measurableAtom_of_notMem fun hyy' => h_eq ?_
    exact measurableAtom_eq_of_mem hyy'
  have h_meas (t) (ht : t in measurableAtom '' s) : MeasurableSet t := by
    obtain ⟨x, hxs, hx⟩ := ht
    rw [← hx]
    exact MeasurableSet.measurableAtom_of_countable x
  rw [measure_sUnion h_count h_disj h_meas]; rw [measure_sUnion h_count h_disj h_meas]
  congr with s'
  have hs' := s'.2
  obtain ⟨x, hxs, hx⟩ := hs'
  rw [← hx]
  exact h x

end

section OuterMeasure

variable [ms : MeasurableSpace α] {s t : Set α}

/--
Definition of `OuterMeasure.toMeasure` / `OuterMeasure.toMeasure` 的定义

English:
definition OuterMeasure.toMeasure
  signature: (m : OuterMeasure α) (h : ms <= m.caratheodory)
  body: Measure.ofMeasurable (fun s _ => m s) m.empty fun _f hf hd =>
    m.iUnion_eq_of_caratheodory (fun i => h _ (hf i)) hd

中文:
定义 外测度.toMeasure
  签名: (m : 外测度 α) (h : ms <= m.caratheodory)
  定义体: Measure.ofMeasurable (fun s _ => m s) m.empty fun _f hf hd =>
    m.iUnion_eq_of_caratheodory (fun i => h _ (hf i)) hd

Depends on / 依赖: Measure, Measure.ofMeasurable, iUnion_eq_of_caratheodory, m.empty, m.iUnion_eq_of_caratheodory, ofMeasurable
-/
def OuterMeasure.toMeasure (m : OuterMeasure α) (h : ms <= m.caratheodory) : Measure α :=
  Measure.ofMeasurable (fun s _ => m s) m.empty fun _f hf hd =>
    m.iUnion_eq_of_caratheodory (fun i => h _ (hf i)) hd

/--
theorem `le_toOuterMeasure_caratheodory` / 定理 `le_toOuterMeasure_caratheodory`

English:
theorem le_toOuterMeasure_caratheodory
  given: (μ : Measure α)
  statement: ms <= μ.toOuterMeasure.caratheodory
  proof: fun _s hs _t => (measure_inter_add_sdiff _ hs).symm

@[simp]

中文:
定理 le_toOuterMeasure_caratheodory
  条件: (μ : 测度 α)
  结论: ms <= μ.toOuterMeasure.caratheodory
  证明: fun _s hs _t => (measure_inter_add_sdiff _ hs).symm

@[simp]

Depends on / 依赖: measure_inter_add_sdiff
-/
theorem le_toOuterMeasure_caratheodory (μ : Measure α) : ms <= μ.toOuterMeasure.caratheodory :=
  fun _s hs _t => (measure_inter_add_sdiff _ hs).symm

@[simp]
/--
theorem `toMeasure_toOuterMeasure` / 定理 `toMeasure_toOuterMeasure`

English:
theorem toMeasure_toOuterMeasure
  given: (m : OuterMeasure α) (h : ms <= m.caratheodory)
  proof: rfl

@[simp]

中文:
定理 toMeasure_toOuterMeasure
  条件: (m : 外测度 α) (h : ms <= m.caratheodory)
  证明: rfl

@[simp]
-/
theorem toMeasure_toOuterMeasure (m : OuterMeasure α) (h : ms <= m.caratheodory) :
    (m.toMeasure h).toOuterMeasure = m.trim :=
  rfl

@[simp]
/--
theorem `toMeasure_apply` / 定理 `toMeasure_apply`

English:
theorem toMeasure_apply
  statement: (m : OuterMeasure α) (h : ms <= m.caratheodory) {s : Set α}
  proof: m.trim_eq hs

中文:
定理 toMeasure_apply
  结论: (m : 外测度 α) (h : ms <= m.caratheodory) {s : 集合 α}
  证明: m.trim_eq hs

Depends on / 依赖: m.trim_eq, trim_eq
-/
theorem toMeasure_apply (m : OuterMeasure α) (h : ms <= m.caratheodory) {s : Set α}
    (hs : MeasurableSet s) : m.toMeasure h s = m s :=
  m.trim_eq hs

/--
theorem `le_toMeasure_apply` / 定理 `le_toMeasure_apply`

English:
theorem le_toMeasure_apply
  given: (m : OuterMeasure α) (h : ms <= m.caratheodory) (s : Set α)
  proof: m.le_trim s

中文:
定理 le_toMeasure_apply
  条件: (m : 外测度 α) (h : ms <= m.caratheodory) (s : 集合 α)
  证明: m.le_trim s

Depends on / 依赖: le_trim, m.le_trim
-/
theorem le_toMeasure_apply (m : OuterMeasure α) (h : ms <= m.caratheodory) (s : Set α) :
    m s <= m.toMeasure h s :=
  m.le_trim s

/--
theorem `toMeasure_apply₀` / 定理 `toMeasure_apply₀`

English:
theorem toMeasure_apply₀
  statement: (m : OuterMeasure α) (h : ms <= m.caratheodory) {s : Set α}
  proof: by
  refine le_antisymm ?_ (le_toMeasure_apply _ _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, heq⟩
  calc
    m.toMeasure h s = m.toMeasure h t := measure_congr heq.symm
    _ = m t := toMeasure_apply m h htm
    _ <= m s := m.mono hts

@[simp]

中文:
定理 toMeasure_apply₀
  结论: (m : 外测度 α) (h : ms <= m.caratheodory) {s : 集合 α}
  证明: by
  refine le_antisymm ?_ (le_toMeasure_apply _ _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, heq⟩
  calc
    m.toMeasure h s = m.toMeasure h t := measure_congr heq.symm
    _ = m t := toMeasure_apply m h htm
    _ <= m s := m.mono hts

@[simp]

Depends on / 依赖: exists_measurable_subset_ae_eq, heq.symm, hs.exists_measurable_subset_ae_eq, le_antisymm, le_toMeasure_apply, m.mono, m.toMeasure, measure_congr, toMeasure, toMeasure_apply
-/
theorem toMeasure_apply₀ (m : OuterMeasure α) (h : ms <= m.caratheodory) {s : Set α}
    (hs : NullMeasurableSet s (m.toMeasure h)) : m.toMeasure h s = m s := by
  refine le_antisymm ?_ (le_toMeasure_apply _ _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, heq⟩
  calc
    m.toMeasure h s = m.toMeasure h t := measure_congr heq.symm
    _ = m t := toMeasure_apply m h htm
    _ <= m s := m.mono hts

@[simp]
/--
theorem `toOuterMeasure_toMeasure` / 定理 `toOuterMeasure_toMeasure`

English:
theorem toOuterMeasure_toMeasure
  given: {μ : Measure α}
  proof: Measure.ext fun _s => μ.toOuterMeasure.trim_eq

@[simp]

中文:
定理 toOuterMeasure_toMeasure
  条件: {μ : 测度 α}
  证明: Measure.ext fun _s => μ.toOuterMeasure.trim_eq

@[simp]

Depends on / 依赖: Measure, Measure.ext, toOuterMeasure, toOuterMeasure.trim_eq, trim_eq
-/
theorem toOuterMeasure_toMeasure {μ : Measure α} :
    μ.toOuterMeasure.toMeasure (le_toOuterMeasure_caratheodory _) = μ :=
  Measure.ext fun _s => μ.toOuterMeasure.trim_eq

@[simp]
/--
theorem `boundedBy_measure` / 定理 `boundedBy_measure`

English:
theorem boundedBy_measure
  given: (μ : Measure α)
  statement: OuterMeasure.boundedBy μ = μ.toOuterMeasure
  proof: μ.toOuterMeasure.boundedBy_eq_self

中文:
定理 boundedBy_measure
  条件: (μ : 测度 α)
  结论: 外测度.boundedBy μ = μ.toOuterMeasure
  证明: μ.toOuterMeasure.boundedBy_eq_self

Depends on / 依赖: boundedBy_eq_self, toOuterMeasure, toOuterMeasure.boundedBy_eq_self
-/
theorem boundedBy_measure (μ : Measure α) : OuterMeasure.boundedBy μ = μ.toOuterMeasure :=
  μ.toOuterMeasure.boundedBy_eq_self

end OuterMeasure

section

variable {m0 : MeasurableSpace α} {mβ : MeasurableSpace β} [MeasurableSpace γ]
variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}
namespace Measure

/--
theorem `measure_inter_eq_of_measure_eq` / 定理 `measure_inter_eq_of_measure_eq`

English:
theorem measure_inter_eq_of_measure_eq
  statement: {s t u : Set α} (hs : MeasurableSet s) (h : μ t = μ u)
  proof: by
  rw [h] at ht_ne_top
  refine le_antisymm (by gcongr) ?_
  have A : μ (u inter s) + μ (u \ s) <= μ (t inter s) + μ (u \ s) :=
    calc
      μ (u inter s) + μ (u \ s) = μ u := measure_inter_add_sdiff _ hs
      _ = μ t := h.symm
      _ = μ (t inter s) + μ (t \ s) := (measure_inter_add_sdiff _ hs).symm
      _ <= μ (t inter s) + μ (u \ s) := by gcongr
  have B : μ (u \ s) != ∞ := (lt_of_le_of_lt (measure_mono sdiff_subset) ht_ne_top.lt_top).ne
  exact ENNReal.le_of_add_le_add_right B A

中文:
定理 measure_inter_eq_of_measure_eq
  结论: {s t u : 集合 α} (hs : 可测集 s) (h : μ t = μ u)
  证明: by
  rw [h] at ht_ne_top
  refine le_antisymm (by gcongr) ?_
  have A : μ (u inter s) + μ (u \ s) <= μ (t inter s) + μ (u \ s) :=
    calc
      μ (u inter s) + μ (u \ s) = μ u := measure_inter_add_sdiff _ hs
      _ = μ t := h.symm
      _ = μ (t inter s) + μ (t \ s) := (measure_inter_add_sdiff _ hs).symm
      _ <= μ (t inter s) + μ (u \ s) := by gcongr
  have B : μ (u \ s) != ∞ := (lt_of_le_of_lt (measure_mono sdiff_subset) ht_ne_top.lt_top).ne
  exact ENNReal.le_of_add_le_add_right B A

Depends on / 依赖: ENNReal, ENNReal.le_of_add_le_add_right, h.symm, ht_ne_top, ht_ne_top.lt_top, le_antisymm, le_of_add_le_add_right, lt_of_le_of_lt, lt_top, measure_inter_add_sdiff, measure_mono, sdiff_subset
-/
theorem measure_inter_eq_of_measure_eq {s t u : Set α} (hs : MeasurableSet s) (h : μ t = μ u)
    (htu : t subseteq u) (ht_ne_top : μ t != ∞) : μ (t inter s) = μ (u inter s) := by
  rw [h] at ht_ne_top
  refine le_antisymm (by gcongr) ?_
  have A : μ (u inter s) + μ (u \ s) <= μ (t inter s) + μ (u \ s) :=
    calc
      μ (u inter s) + μ (u \ s) = μ u := measure_inter_add_sdiff _ hs
      _ = μ t := h.symm
      _ = μ (t inter s) + μ (t \ s) := (measure_inter_add_sdiff _ hs).symm
      _ <= μ (t inter s) + μ (u \ s) := by gcongr
  have B : μ (u \ s) != ∞ := (lt_of_le_of_lt (measure_mono sdiff_subset) ht_ne_top.lt_top).ne
  exact ENNReal.le_of_add_le_add_right B A

/--
lemma `measure_inter_eq_of_ae` / 引理 `measure_inter_eq_of_ae`

English:
lemma measure_inter_eq_of_ae
  given: {s t : Set α} (h : forallᵐ a ∂μ, a in t)
  proof: by
  refine le_antisymm (measure_mono inter_subset_right) ?_
  apply EventuallyLE.measure_le
  filter_upwards [h] with x hx h'x using ⟨hx, h'x⟩

中文:
引理 measure_inter_eq_of_ae
  条件: {s t : 集合 α} (h : 对任意ᵐ a ∂μ, a in t)
  证明: by
  refine le_antisymm (measure_mono inter_subset_right) ?_
  apply EventuallyLE.measure_le
  filter_upwards [h] with x hx h'x using ⟨hx, h'x⟩

Depends on / 依赖: EventuallyLE, EventuallyLE.measure_le, filter_upwards, inter_subset_right, le_antisymm, measure_le, measure_mono
-/
lemma measure_inter_eq_of_ae {s t : Set α} (h : forallᵐ a ∂μ, a in t) :
    μ (t inter s) = μ s := by
  refine le_antisymm (measure_mono inter_subset_right) ?_
  apply EventuallyLE.measure_le
  filter_upwards [h] with x hx h'x using ⟨hx, h'x⟩

/--
theorem `measure_toMeasurable_inter` / 定理 `measure_toMeasurable_inter`

English:
theorem measure_toMeasurable_inter
  given: {s t : Set α} (hs : MeasurableSet s) (ht : μ t != ∞)
  proof: (measure_inter_eq_of_measure_eq hs (measure_toMeasurable t).symm (subset_toMeasurable μ t)
      ht).symm

中文:
定理 measure_toMeasurable_inter
  条件: {s t : 集合 α} (hs : 可测集 s) (ht : μ t != ∞)
  证明: (measure_inter_eq_of_measure_eq hs (measure_toMeasurable t).symm (subset_toMeasurable μ t)
      ht).symm

Depends on / 依赖: measure_inter_eq_of_measure_eq, measure_toMeasurable, subset_toMeasurable
-/
theorem measure_toMeasurable_inter {s t : Set α} (hs : MeasurableSet s) (ht : μ t != ∞) :
    μ (toMeasurable μ t inter s) = μ (t inter s) :=
  (measure_inter_eq_of_measure_eq hs (measure_toMeasurable t).symm (subset_toMeasurable μ t)
      ht).symm


/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: {_ : MeasurableSpace α}
  body: ⟨{ toOuterMeasure := 0
      m_iUnion := fun _f _hf _hd => tsum_zero.symm
      trim_le := OuterMeasure.trim_zero.le }⟩

@[simp]

中文:
实例 instZero
  签名: {_ : 可测空间 α}
  定义体: ⟨{ toOuterMeasure := 0
      m_iUnion := fun _f _hf _hd => tsum_zero.symm
      trim_le := OuterMeasure.trim_zero.le }⟩

@[simp]

Depends on / 依赖: OuterMeasure, OuterMeasure.trim_zero.le, m_iUnion, toOuterMeasure, trim_le, trim_zero, tsum_zero, tsum_zero.symm
-/
instance instZero {_ : MeasurableSpace α} : Zero (Measure α) :=
  ⟨{ toOuterMeasure := 0
      m_iUnion := fun _f _hf _hd => tsum_zero.symm
      trim_le := OuterMeasure.trim_zero.le }⟩

@[simp]
/--
theorem `zero_toOuterMeasure` / 定理 `zero_toOuterMeasure`

English:
theorem zero_toOuterMeasure
  given: {_m : MeasurableSpace α}
  statement: (0 : Measure α).toOuterMeasure = 0
  proof: rfl

@[simp, norm_cast]

中文:
定理 zero_toOuterMeasure
  条件: {_m : 可测空间 α}
  结论: (0 : 测度 α).toOuterMeasure = 0
  证明: rfl

@[simp, norm_cast]
-/
theorem zero_toOuterMeasure {_m : MeasurableSpace α} : (0 : Measure α).toOuterMeasure = 0 :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  given: {_m : MeasurableSpace α}
  statement: ⇑(0 : Measure α) = 0
  proof: rfl

中文:
定理 coe_zero
  条件: {_m : 可测空间 α}
  结论: ⇑(0 : 测度 α) = 0
  证明: rfl
-/
theorem coe_zero {_m : MeasurableSpace α} : ⇑(0 : Measure α) = 0 :=
  rfl

/--
lemma `_root_.MeasureTheory.OuterMeasure.toMeasure_zero` / 引理 `_root_.MeasureTheory.OuterMeasure.toMeasure_zero`

English:
lemma _root_.MeasureTheory.OuterMeasure.toMeasure_zero
  proof: by
  ext s hs
  simp [hs]

中文:
引理 _root_.测度论.外测度.toMeasure_zero
  证明: by
  ext s hs
  simp [hs]
-/
@[simp] lemma _root_.MeasureTheory.OuterMeasure.toMeasure_zero
    [ms : MeasurableSpace α] (h : ms <= (0 : OuterMeasure α).caratheodory) :
    (0 : OuterMeasure α).toMeasure h = 0 := by
  ext s hs
  simp [hs]

/--
lemma `_root_.MeasureTheory.OuterMeasure.toMeasure_eq_zero` / 引理 `_root_.MeasureTheory.OuterMeasure.toMeasure_eq_zero`

English:
lemma _root_.MeasureTheory.OuterMeasure.toMeasure_eq_zero
  statement: {ms : MeasurableSpace α}
  proof: by ext s; exact le_bot_iff.1 (le_toMeasure_apply _ _ _).trans_eq congr($hμ s)
  mpr := by rintro rfl; simp

@[nontriviality]

中文:
引理 _root_.测度论.外测度.toMeasure_eq_zero
  结论: {ms : 可测空间 α}
  证明: by ext s; exact le_bot_iff.1 (le_toMeasure_apply _ _ _).trans_eq congr($hμ s)
  mpr := by rintro rfl; simp

@[nontriviality]
-/
@[simp] lemma _root_.MeasureTheory.OuterMeasure.toMeasure_eq_zero {ms : MeasurableSpace α}
    {μ : OuterMeasure α} (h : ms <= μ.caratheodory) : μ.toMeasure h = 0 ↔ μ = 0 where
mp hμ := by ext s; exact le_bot_iff.1 (le_toMeasure_apply _ _ _).trans_eq congr($hμ s)
  mpr := by rintro rfl; simp

@[nontriviality]
/--
lemma `apply_eq_zero_of_isEmpty` / 引理 `apply_eq_zero_of_isEmpty`

English:
lemma apply_eq_zero_of_isEmpty
  given: [IsEmpty α] {_ : MeasurableSpace α} (μ : Measure α) (s : Set α)
  proof: by
  rw [eq_empty_of_isEmpty s]; rw [measure_empty]

中文:
引理 apply_eq_zero_of_isEmpty
  条件: [是空 α] {_ : 可测空间 α} (μ : 测度 α) (s : 集合 α)
  证明: by
  rw [eq_empty_of_isEmpty s]; rw [measure_empty]

Depends on / 依赖: eq_empty_of_isEmpty, measure_empty
-/
lemma apply_eq_zero_of_isEmpty [IsEmpty α] {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ s = 0 := by
  rw [eq_empty_of_isEmpty s]; rw [measure_empty]

/--
Instance `instSubsingleton` / 实例 `instSubsingleton`

English:
instance instSubsingleton
  signature: [IsEmpty α] {m : MeasurableSpace α}
  body: ⟨fun μ ν => by ext1 s _; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩

中文:
实例 instSubsingleton
  签名: [是空 α] {m : 可测空间 α}
  定义体: ⟨fun μ ν => by ext1 s _; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩

Depends on / 依赖: apply_eq_zero_of_isEmpty
-/
instance instSubsingleton [IsEmpty α] {m : MeasurableSpace α} : Subsingleton (Measure α) :=
  ⟨fun μ ν => by ext1 s _; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩

/--
theorem `eq_zero_of_isEmpty` / 定理 `eq_zero_of_isEmpty`

English:
theorem eq_zero_of_isEmpty
  given: [IsEmpty α] {_m : MeasurableSpace α} (μ : Measure α)
  statement: μ = 0
  proof: Subsingleton.elim μ 0

@[simp]

中文:
定理 eq_zero_of_isEmpty
  条件: [是空 α] {_m : 可测空间 α} (μ : 测度 α)
  结论: μ = 0
  证明: Subsingleton.elim μ 0

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem eq_zero_of_isEmpty [IsEmpty α] {_m : MeasurableSpace α} (μ : Measure α) : μ = 0 :=
  Subsingleton.elim μ 0

@[simp]
/--
theorem `ofMeasurable_zero` / 定理 `ofMeasurable_zero`

English:
theorem ofMeasurable_zero
  statement: ofMeasurable (α := α) (fun _ _ => 0) rfl (by simp) = 0
  proof: by
  ext s
  simp [ofMeasurable, ← toOuterMeasure_apply, inducedOuterMeasure_zero MeasurableSet.iUnion]

中文:
定理 ofMeasurable_zero
  结论: ofMeasurable (α := α) (fun _ _ => 0) rfl (by simp) = 0
  证明: by
  ext s
  simp [ofMeasurable, ← toOuterMeasure_apply, inducedOuterMeasure_zero MeasurableSet.iUnion]

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, iUnion, inducedOuterMeasure_zero, ofMeasurable, toOuterMeasure_apply
-/
theorem ofMeasurable_zero : ofMeasurable (α := α) (fun _ _ => 0) rfl (by simp) = 0 := by
  ext s
  simp [ofMeasurable, ← toOuterMeasure_apply, inducedOuterMeasure_zero MeasurableSet.iUnion]

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: {_ : MeasurableSpace α}
  body: ⟨0⟩

中文:
实例 instInhabited
  签名: {_ : 可测空间 α}
  定义体: ⟨0⟩
-/
instance instInhabited {_ : MeasurableSpace α} : Inhabited (Measure α) :=
  ⟨0⟩

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: {_ : MeasurableSpace α}
  body: ⟨fun μ₁ μ₂ =>
    { toOuterMeasure := μ₁.toOuterMeasure + μ₂.toOuterMeasure
      m_iUnion := fun s hs hd =>
        show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, (μ₁ (s i) + μ₂ (s i)) by
          rw [ENNReal.tsum_add]; rw [measure_iUnion hd hs]; rw [measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩

@[simp]

中文:
实例 instAdd
  签名: {_ : 可测空间 α}
  定义体: ⟨fun μ₁ μ₂ =>
    { toOuterMeasure := μ₁.toOuterMeasure + μ₂.toOuterMeasure
      m_iUnion := fun s hs hd =>
        show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, (μ₁ (s i) + μ₂ (s i)) by
          rw [ENNReal.tsum_add]; rw [measure_iUnion hd hs]; rw [measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩

@[simp]

Depends on / 依赖: ENNReal, ENNReal.tsum_add, OuterMeasure, OuterMeasure.trim_add, m_iUnion, measure_iUnion, toOuterMeasure, trim_add, trim_le, trimmed, tsum_add
-/
instance instAdd {_ : MeasurableSpace α} : Add (Measure α) :=
  ⟨fun μ₁ μ₂ =>
    { toOuterMeasure := μ₁.toOuterMeasure + μ₂.toOuterMeasure
      m_iUnion := fun s hs hd =>
        show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, (μ₁ (s i) + μ₂ (s i)) by
          rw [ENNReal.tsum_add]; rw [measure_iUnion hd hs]; rw [measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩

@[simp]
/--
theorem `add_toOuterMeasure` / 定理 `add_toOuterMeasure`

English:
theorem add_toOuterMeasure
  given: {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α)
  proof: rfl

@[simp, norm_cast]

中文:
定理 add_toOuterMeasure
  条件: {_m : 可测空间 α} (μ₁ μ₂ : 测度 α)
  证明: rfl

@[simp, norm_cast]
-/
theorem add_toOuterMeasure {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) :
    (μ₁ + μ₂).toOuterMeasure = μ₁.toOuterMeasure + μ₂.toOuterMeasure :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α)
  statement: ⇑(μ₁ + μ₂) = μ₁ + μ₂
  proof: rfl

中文:
定理 coe_add
  条件: {_m : 可测空间 α} (μ₁ μ₂ : 测度 α)
  结论: ⇑(μ₁ + μ₂) = μ₁ + μ₂
  证明: rfl
-/
theorem coe_add {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂ :=
  rfl

/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α)
  proof: rfl

中文:
定理 add_apply
  条件: {_m : 可测空间 α} (μ₁ μ₂ : 测度 α) (s : 集合 α)
  证明: rfl
-/
theorem add_apply {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α) :
    (μ₁ + μ₂) s = μ₁ s + μ₂ s :=
  rfl

section SMul

variable [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
variable [SMul R' Real>=0∞] [IsScalarTower R' Real>=0∞ Real>=0∞]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: {_ : MeasurableSpace α}
  body: ⟨fun c μ =>
    { toOuterMeasure := c • μ.toOuterMeasure
      m_iUnion := fun s hs hd => by
        simp only [smul_apply, coe_toOuterMeasure, ENNReal.tsum_const_smul,
          measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_smul, μ.trimmed] }⟩

@[simp]

中文:
实例 instSMul
  签名: {_ : 可测空间 α}
  定义体: ⟨fun c μ =>
    { toOuterMeasure := c • μ.toOuterMeasure
      m_iUnion := fun s hs hd => by
        simp only [smul_apply, coe_toOuterMeasure, ENNReal.tsum_const_smul,
          measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_smul, μ.trimmed] }⟩

@[simp]

Depends on / 依赖: ENNReal, ENNReal.tsum_const_smul, OuterMeasure, OuterMeasure.trim_smul, coe_toOuterMeasure, m_iUnion, measure_iUnion, smul_apply, toOuterMeasure, trim_le, trim_smul, trimmed, tsum_const_smul
-/
instance instSMul {_ : MeasurableSpace α} : SMul R (Measure α) :=
  ⟨fun c μ =>
    { toOuterMeasure := c • μ.toOuterMeasure
      m_iUnion := fun s hs hd => by
        simp only [smul_apply, coe_toOuterMeasure, ENNReal.tsum_const_smul,
          measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_smul, μ.trimmed] }⟩

@[simp]
/--
theorem `smul_toOuterMeasure` / 定理 `smul_toOuterMeasure`

English:
theorem smul_toOuterMeasure
  given: {_m : MeasurableSpace α} (c : R) (μ : Measure α)
  proof: rfl

@[simp, norm_cast]

中文:
定理 smul_toOuterMeasure
  条件: {_m : 可测空间 α} (c : R) (μ : 测度 α)
  证明: rfl

@[simp, norm_cast]
-/
theorem smul_toOuterMeasure {_m : MeasurableSpace α} (c : R) (μ : Measure α) :
    (c • μ).toOuterMeasure = c • μ.toOuterMeasure :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: {_m : MeasurableSpace α} (c : R) (μ : Measure α)
  statement: ⇑(c • μ) = c • ⇑μ
  proof: rfl

@[simp]

中文:
定理 coe_smul
  条件: {_m : 可测空间 α} (c : R) (μ : 测度 α)
  结论: ⇑(c • μ) = c • ⇑μ
  证明: rfl

@[simp]
-/
theorem coe_smul {_m : MeasurableSpace α} (c : R) (μ : Measure α) : ⇑(c • μ) = c • ⇑μ :=
  rfl

@[simp]
/--
lemma `coe_nnreal_smul` / 引理 `coe_nnreal_smul`

English:
lemma coe_nnreal_smul
  given: (c : Real>=0) (μ : Measure α)
  statement: (c : Real>=0∞) • μ = c • μ
  proof: rfl

@[simp]

中文:
引理 coe_nnreal_smul
  条件: (c : 实数>=0) (μ : 测度 α)
  结论: (c : 实数>=0∞) • μ = c • μ
  证明: rfl

@[simp]
-/
lemma coe_nnreal_smul (c : Real>=0) (μ : Measure α) : (c : Real>=0∞) • μ = c • μ := rfl

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: {_m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α)
  proof: rfl

中文:
定理 smul_apply
  条件: {_m : 可测空间 α} (c : R) (μ : 测度 α) (s : 集合 α)
  证明: rfl
-/
theorem smul_apply {_m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α) :
    (c • μ) s = c • μ s :=
  rfl

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMulCommClass R R' Real>=0∞] {_ : MeasurableSpace α}
  body: ⟨fun _ _ _ => ext fun _ _ => smul_comm _ _ _⟩

中文:
实例 instSMulCommClass
  签名: [标量交换类 R R' 实数>=0∞] {_ : 可测空间 α}
  定义体: ⟨fun _ _ _ => ext fun _ _ => smul_comm _ _ _⟩

Depends on / 依赖: smul_comm
-/
instance instSMulCommClass [SMulCommClass R R' Real>=0∞] {_ : MeasurableSpace α} :
    SMulCommClass R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_comm _ _ _⟩

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul R R'] [IsScalarTower R R' Real>=0∞] {_ : MeasurableSpace α}
  body: ⟨fun _ _ _ => ext fun _ _ => smul_assoc _ _ _⟩

中文:
实例 instIsScalarTower
  签名: [标量乘法 R R'] [标量塔 R R' 实数>=0∞] {_ : 可测空间 α}
  定义体: ⟨fun _ _ _ => ext fun _ _ => smul_assoc _ _ _⟩

Depends on / 依赖: smul_assoc
-/
instance instIsScalarTower [SMul R R'] [IsScalarTower R R' Real>=0∞] {_ : MeasurableSpace α} :
    IsScalarTower R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_assoc _ _ _⟩

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [SMul Rᵐᵒᵖ Real>=0∞] [IsCentralScalar R Real>=0∞] {_ : MeasurableSpace α}
  body: ⟨fun _ _ => ext fun _ _ => op_smul_eq_smul _ _⟩

中文:
实例 instIsCentralScalar
  签名: [标量乘法 Rᵐᵒᵖ 实数>=0∞] [中心标量 R 实数>=0∞] {_ : 可测空间 α}
  定义体: ⟨fun _ _ => ext fun _ _ => op_smul_eq_smul _ _⟩

Depends on / 依赖: op_smul_eq_smul
-/
instance instIsCentralScalar [SMul Rᵐᵒᵖ Real>=0∞] [IsCentralScalar R Real>=0∞] {_ : MeasurableSpace α} :
    IsCentralScalar R (Measure α) :=
  ⟨fun _ _ => ext fun _ _ => op_smul_eq_smul _ _⟩

end SMul

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: [Monoid R] [MulAction R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  body: Injective.mulAction _ toOuterMeasure_injective smul_toOuterMeasure

中文:
实例 instMulAction
  签名: [幺半群 R] [乘法作用 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  定义体: Injective.mulAction _ toOuterMeasure_injective smul_toOuterMeasure

Depends on / 依赖: Injective, Injective.mulAction, mulAction, smul_toOuterMeasure, toOuterMeasure_injective
-/
instance instMulAction [Monoid R] [MulAction R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    {_ : MeasurableSpace α} : MulAction R (Measure α) :=
  Injective.mulAction _ toOuterMeasure_injective smul_toOuterMeasure

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: {_ : MeasurableSpace α}
  body: toOuterMeasure_injective.addCommMonoid toOuterMeasure zero_toOuterMeasure add_toOuterMeasure
    fun _ _ => smul_toOuterMeasure _ _

中文:
实例 instAddCommMonoid
  签名: {_ : 可测空间 α}
  定义体: toOuterMeasure_injective.addCommMonoid toOuterMeasure zero_toOuterMeasure add_toOuterMeasure
    fun _ _ => smul_toOuterMeasure _ _

Depends on / 依赖: addCommMonoid, add_toOuterMeasure, smul_toOuterMeasure, toOuterMeasure, toOuterMeasure_injective, toOuterMeasure_injective.addCommMonoid, zero_toOuterMeasure
-/
instance instAddCommMonoid {_ : MeasurableSpace α} : AddCommMonoid (Measure α) :=
  toOuterMeasure_injective.addCommMonoid toOuterMeasure zero_toOuterMeasure add_toOuterMeasure
    fun _ _ => smul_toOuterMeasure _ _

/--
Definition of `coeAddHom` / `coeAddHom` 的定义

English:
definition coeAddHom
  signature: {_ : MeasurableSpace α}
  body: (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]

中文:
定义 coeAddHom
  签名: {_ : 可测空间 α}
  定义体: (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
-/
def coeAddHom {_ : MeasurableSpace α} : Measure α ->+ Set α -> Real>=0∞ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/--
theorem `coeAddHom_apply` / 定理 `coeAddHom_apply`

English:
theorem coeAddHom_apply
  given: {_ : MeasurableSpace α} (μ : Measure α)
  statement: coeAddHom μ = ⇑μ
  proof: rfl

@[simp]

中文:
定理 coeAddHom_apply
  条件: {_ : 可测空间 α} (μ : 测度 α)
  结论: coeAddHom μ = ⇑μ
  证明: rfl

@[simp]
-/
theorem coeAddHom_apply {_ : MeasurableSpace α} (μ : Measure α) : coeAddHom μ = ⇑μ := rfl

@[simp]
/--
theorem `coe_finsetSum` / 定理 `coe_finsetSum`

English:
theorem coe_finsetSum
  given: {_m : MeasurableSpace α} (I : Finset ι) (μ : ι -> Measure α)
  proof: map_sum coeAddHom μ I

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum

中文:
定理 coe_finsetSum
  条件: {_m : 可测空间 α} (I : 有限集 ι) (μ : ι -> 测度 α)
  证明: map_sum coeAddHom μ I

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum

Depends on / 依赖: coeAddHom, map_sum
-/
theorem coe_finsetSum {_m : MeasurableSpace α} (I : Finset ι) (μ : ι -> Measure α) :
    ⇑(∑ i in I, μ i) = ∑ i in I, ⇑(μ i) := map_sum coeAddHom μ I

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum

/--
theorem `finsetSum_apply` / 定理 `finsetSum_apply`

English:
theorem finsetSum_apply
  given: {m : MeasurableSpace α} (I : Finset ι) (μ : ι -> Measure α) (s : Set α)
  proof: by rw [coe_finsetSum, Finset.sum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

中文:
定理 finsetSum_apply
  条件: {m : 可测空间 α} (I : 有限集 ι) (μ : ι -> 测度 α) (s : 集合 α)
  证明: by rw [coe_finsetSum, Finset.sum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

Depends on / 依赖: Finset, Finset.sum_apply, coe_finsetSum, sum_apply
-/
theorem finsetSum_apply {m : MeasurableSpace α} (I : Finset ι) (μ : ι -> Measure α) (s : Set α) :
    (∑ i in I, μ i) s = ∑ i in I, μ i s := by rw [coe_finsetSum, Finset.sum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [Monoid R] [DistribMulAction R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  body: Injective.distribMulAction ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

中文:
实例 instDistribMulAction
  签名: [幺半群 R] [分配乘法作用 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  定义体: Injective.distribMulAction ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

Depends on / 依赖: Injective, Injective.distribMulAction, add_toOuterMeasure, distribMulAction, smul_toOuterMeasure, toOuterMeasure, toOuterMeasure_injective, zero_toOuterMeasure
-/
instance instDistribMulAction [Monoid R] [DistribMulAction R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    {_ : MeasurableSpace α} : DistribMulAction R (Measure α) :=
  Injective.distribMulAction ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  body: Injective.module R ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

中文:
实例 instModule
  签名: [半环 R] [模 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  定义体: Injective.module R ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

Depends on / 依赖: Injective, Injective.module, add_toOuterMeasure, module, smul_toOuterMeasure, toOuterMeasure, toOuterMeasure_injective, zero_toOuterMeasure
-/
instance instModule [Semiring R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    {_ : MeasurableSpace α} : Module R (Measure α) :=
  Injective.module R ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

/--
Instance `instModuleIsTorsionFree` / 实例 `instModuleIsTorsionFree`

English:
instance instModuleIsTorsionFree
  signature: [Semiring R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  body: DFunLike.coe_injective.moduleIsTorsionFree _ (by simp)

中文:
实例 instModuleIsTorsionFree
  签名: [半环 R] [模 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  定义体: DFunLike.coe_injective.moduleIsTorsionFree _ (by simp)

Depends on / 依赖: DFunLike, DFunLike.coe_injective.moduleIsTorsionFree, coe_injective, moduleIsTorsionFree
-/
instance instModuleIsTorsionFree [Semiring R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    [Module.IsTorsionFree R Real>=0∞] : Module.IsTorsionFree R (Measure α) :=
  DFunLike.coe_injective.moduleIsTorsionFree _ (by simp)

/--
lemma `ennreal_smul_eq_zero` / 引理 `ennreal_smul_eq_zero`

English:
lemma ennreal_smul_eq_zero
  given: {c : Real>=0∞} {μ : Measure α}
  statement: c • μ = 0 ↔ c = 0 ∨ μ = 0
  proof: by
  simp [Measure.ext_iff', forall_or_left]

@[simp]

中文:
引理 ennreal_smul_eq_zero
  条件: {c : 实数>=0∞} {μ : 测度 α}
  结论: c • μ = 0 ↔ c = 0 ∨ μ = 0
  证明: by
  simp [Measure.ext_iff', forall_or_left]

@[simp]
-/
@[simp] lemma ennreal_smul_eq_zero {c : Real>=0∞} {μ : Measure α} : c • μ = 0 ↔ c = 0 ∨ μ = 0 := by
  simp [Measure.ext_iff', forall_or_left]

@[simp]
/--
theorem `coe_nnreal_smul_apply` / 定理 `coe_nnreal_smul_apply`

English:
theorem coe_nnreal_smul_apply
  given: {_m : MeasurableSpace α} (c : Real>=0) (μ : Measure α) (s : Set α)
  proof: rfl

@[simp]

中文:
定理 coe_nnreal_smul_apply
  条件: {_m : 可测空间 α} (c : 实数>=0) (μ : 测度 α) (s : 集合 α)
  证明: rfl

@[simp]
-/
theorem coe_nnreal_smul_apply {_m : MeasurableSpace α} (c : Real>=0) (μ : Measure α) (s : Set α) :
    (c • μ) s = c * μ s :=
  rfl

@[simp]
/--
theorem `nnreal_smul_coe_apply` / 定理 `nnreal_smul_coe_apply`

English:
theorem nnreal_smul_coe_apply
  given: {_m : MeasurableSpace α} (c : Real>=0) (μ : Measure α) (s : Set α)
  proof: rfl

中文:
定理 nnreal_smul_coe_apply
  条件: {_m : 可测空间 α} (c : 实数>=0) (μ : 测度 α) (s : 集合 α)
  证明: rfl
-/
theorem nnreal_smul_coe_apply {_m : MeasurableSpace α} (c : Real>=0) (μ : Measure α) (s : Set α) :
    c • μ s = c * μ s :=
  rfl

/--
theorem `ae_smul_measure` / 定理 `ae_smul_measure`

English:
theorem ae_smul_measure
  statement: {p : α -> Prop} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  proof: ae_iff.2 by rw [smul_apply, ae_iff.1 h, ← smul_one_smul Real>=0∞, smul_zero]

中文:
定理 ae_smul_measure
  结论: {p : α -> 命题} [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞]
  证明: ae_iff.2 by rw [smul_apply, ae_iff.1 h, ← smul_one_smul Real>=0∞, smul_zero]

Depends on / 依赖: ae_iff, smul_apply, smul_one_smul, smul_zero
-/
theorem ae_smul_measure {p : α -> Prop} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
    (h : forallᵐ x ∂μ, p x) (c : R) : forallᵐ x ∂c • μ, p x :=
ae_iff.2 by rw [smul_apply, ae_iff.1 h, ← smul_one_smul Real>=0∞, smul_zero]

/--
theorem `ae_smul_measure_le` / 定理 `ae_smul_measure_le`

English:
theorem ae_smul_measure_le
  given: [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R)
  proof: fun _ h => ae_smul_measure h c

中文:
定理 ae_smul_measure_le
  条件: [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞] (c : R)
  证明: fun _ h => ae_smul_measure h c

Depends on / 依赖: ae_smul_measure
-/
theorem ae_smul_measure_le [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) :
    ae (c • μ) <= ae μ := fun _ h => ae_smul_measure h c

section Module

variable {R : Type*} [Semiring R] [IsDomain R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞]
  [Module.IsTorsionFree R Real>=0∞] {c : R} {p : α -> Prop}

/--
lemma `ae_smul_measure_iff` / 引理 `ae_smul_measure_iff`

English:
lemma ae_smul_measure_iff
  given: (hc : c != 0) {μ : Measure α}
  statement: (forallᵐ x ∂c • μ, p x) ↔ forallᵐ x ∂μ, p x
  proof: by
  simp [ae_iff, hc]

中文:
引理 ae_smul_measure_iff
  条件: (hc : c != 0) {μ : 测度 α}
  结论: (对任意ᵐ x ∂c • μ, p x) ↔ 对任意ᵐ x ∂μ, p x
  证明: by
  simp [ae_iff, hc]

Depends on / 依赖: ae_iff
-/
lemma ae_smul_measure_iff (hc : c != 0) {μ : Measure α} : (forallᵐ x ∂c • μ, p x) ↔ forallᵐ x ∂μ, p x := by
  simp [ae_iff, hc]

/--
lemma `ae_smul_measure_eq` / 引理 `ae_smul_measure_eq`

English:
lemma ae_smul_measure_eq
  given: (hc : c != 0) (μ : Measure α)
  statement: ae (c • μ) = ae μ
  proof: by
  ext; exact ae_smul_measure_iff hc

中文:
引理 ae_smul_measure_eq
  条件: (hc : c != 0) (μ : 测度 α)
  结论: ae (c • μ) = ae μ
  证明: by
  ext; exact ae_smul_measure_iff hc

Depends on / 依赖: WellQuasiOrderedLE, WellQuasiOrderedLE.to_wellFoundedLT, to_wellFoundedLT
-/
@[simp] lemma ae_smul_measure_eq (hc : c != 0) (μ : Measure α) : ae (c • μ) = ae μ := by
  ext; exact ae_smul_measure_iff hc

end Module

/--
lemma `ae_ennreal_smul_measure_iff` / 引理 `ae_ennreal_smul_measure_iff`

English:
lemma ae_ennreal_smul_measure_iff
  given: {c : Real>=0∞} {p : α -> Prop} (hc : c != 0) {μ : Measure α}
  proof: by simp [ae_iff, hc]

中文:
引理 ae_ennreal_smul_measure_iff
  条件: {c : 实数>=0∞} {p : α -> 命题} (hc : c != 0) {μ : 测度 α}
  证明: by simp [ae_iff, hc]

Depends on / 依赖: ae_iff
-/
lemma ae_ennreal_smul_measure_iff {c : Real>=0∞} {p : α -> Prop} (hc : c != 0) {μ : Measure α} :
    (forallᵐ x ∂c • μ, p x) ↔ forallᵐ x ∂μ, p x := by simp [ae_iff, hc]

/--
lemma `ae_ennreal_smul_measure_eq` / 引理 `ae_ennreal_smul_measure_eq`

English:
lemma ae_ennreal_smul_measure_eq
  given: {c : Real>=0∞} (hc : c != 0) (μ : Measure α)
  proof: by ext; exact ae_ennreal_smul_measure_iff hc

中文:
引理 ae_ennreal_smul_measure_eq
  条件: {c : 实数>=0∞} (hc : c != 0) (μ : 测度 α)
  证明: by ext; exact ae_ennreal_smul_measure_iff hc
-/
@[simp] lemma ae_ennreal_smul_measure_eq {c : Real>=0∞} (hc : c != 0) (μ : Measure α) :
    ae (c • μ) = ae μ := by ext; exact ae_ennreal_smul_measure_iff hc

/--
theorem `measure_eq_left_of_subset_of_measure_add_eq` / 定理 `measure_eq_left_of_subset_of_measure_add_eq`

English:
theorem measure_eq_left_of_subset_of_measure_add_eq
  statement: {s t : Set α} (h : (μ + ν) t != ∞) (h' : s subseteq t)
  proof: by
  refine le_antisymm (measure_mono h') ?_
  have : μ t + ν t <= μ s + ν t :=
    calc
      μ t + ν t = μ s + ν s := h''.symm
      _ <= μ s + ν t := by gcongr
  apply ENNReal.le_of_add_le_add_right _ this
  exact ne_top_of_le_ne_top h (le_add_left le_rfl)

中文:
定理 measure_eq_left_of_subset_of_measure_add_eq
  结论: {s t : 集合 α} (h : (μ + ν) t != ∞) (h' : s subseteq t)
  证明: by
  refine le_antisymm (measure_mono h') ?_
  have : μ t + ν t <= μ s + ν t :=
    calc
      μ t + ν t = μ s + ν s := h''.symm
      _ <= μ s + ν t := by gcongr
  apply ENNReal.le_of_add_le_add_right _ this
  exact ne_top_of_le_ne_top h (le_add_left le_rfl)

Depends on / 依赖: ENNReal, ENNReal.le_of_add_le_add_right, le_add_left, le_antisymm, le_of_add_le_add_right, le_rfl, measure_mono, ne_top_of_le_ne_top
-/
theorem measure_eq_left_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t != ∞) (h' : s subseteq t)
    (h'' : (μ + ν) s = (μ + ν) t) : μ s = μ t := by
  refine le_antisymm (measure_mono h') ?_
  have : μ t + ν t <= μ s + ν t :=
    calc
      μ t + ν t = μ s + ν s := h''.symm
      _ <= μ s + ν t := by gcongr
  apply ENNReal.le_of_add_le_add_right _ this
  exact ne_top_of_le_ne_top h (le_add_left le_rfl)

/--
theorem `measure_eq_right_of_subset_of_measure_add_eq` / 定理 `measure_eq_right_of_subset_of_measure_add_eq`

English:
theorem measure_eq_right_of_subset_of_measure_add_eq
  statement: {s t : Set α} (h : (μ + ν) t != ∞) (h' : s subseteq t)
  proof: by
  rw [add_comm] at h'' h
  exact measure_eq_left_of_subset_of_measure_add_eq h h' h''

中文:
定理 measure_eq_right_of_subset_of_measure_add_eq
  结论: {s t : 集合 α} (h : (μ + ν) t != ∞) (h' : s subseteq t)
  证明: by
  rw [add_comm] at h'' h
  exact measure_eq_left_of_subset_of_measure_add_eq h h' h''

Depends on / 依赖: add_comm, measure_eq_left_of_subset_of_measure_add_eq
-/
theorem measure_eq_right_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t != ∞) (h' : s subseteq t)
    (h'' : (μ + ν) s = (μ + ν) t) : ν s = ν t := by
  rw [add_comm] at h'' h
  exact measure_eq_left_of_subset_of_measure_add_eq h h' h''

/--
theorem `measure_toMeasurable_add_inter_left` / 定理 `measure_toMeasurable_add_inter_left`

English:
theorem measure_toMeasurable_add_inter_left
  statement: {s t : Set α} (hs : MeasurableSet s)
  proof: by
  refine (measure_inter_eq_of_measure_eq hs ?_ (subset_toMeasurable _ _) ?_).symm
  · refine
      measure_eq_left_of_subset_of_measure_add_eq ?_ (subset_toMeasurable _ _)
        (measure_toMeasurable t).symm
    rwa [measure_toMeasurable t]
  · simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne, coe_add] at ht
    exact ht.1

中文:
定理 measure_toMeasurable_add_inter_left
  结论: {s t : 集合 α} (hs : 可测集 s)
  证明: by
  refine (measure_inter_eq_of_measure_eq hs ?_ (subset_toMeasurable _ _) ?_).symm
  · refine
      measure_eq_left_of_subset_of_measure_add_eq ?_ (subset_toMeasurable _ _)
        (measure_toMeasurable t).symm
    rwa [measure_toMeasurable t]
  · simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne, coe_add] at ht
    exact ht.1

Depends on / 依赖: ENNReal, ENNReal.add_eq_top, Pi.add_apply, add_apply, add_eq_top, coe_add, measure_eq_left_of_subset_of_measure_add_eq, measure_inter_eq_of_measure_eq, measure_toMeasurable, not_or, subset_toMeasurable
-/
theorem measure_toMeasurable_add_inter_left {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t != ∞) : μ (toMeasurable (μ + ν) t inter s) = μ (t inter s) := by
  refine (measure_inter_eq_of_measure_eq hs ?_ (subset_toMeasurable _ _) ?_).symm
  · refine
      measure_eq_left_of_subset_of_measure_add_eq ?_ (subset_toMeasurable _ _)
        (measure_toMeasurable t).symm
    rwa [measure_toMeasurable t]
  · simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne, coe_add] at ht
    exact ht.1

/--
theorem `measure_toMeasurable_add_inter_right` / 定理 `measure_toMeasurable_add_inter_right`

English:
theorem measure_toMeasurable_add_inter_right
  statement: {s t : Set α} (hs : MeasurableSet s)
  proof: by
  rw [add_comm] at ht ⊢
  exact measure_toMeasurable_add_inter_left hs ht

中文:
定理 measure_toMeasurable_add_inter_right
  结论: {s t : 集合 α} (hs : 可测集 s)
  证明: by
  rw [add_comm] at ht ⊢
  exact measure_toMeasurable_add_inter_left hs ht

Depends on / 依赖: add_comm, measure_toMeasurable_add_inter_left
-/
theorem measure_toMeasurable_add_inter_right {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t != ∞) : ν (toMeasurable (μ + ν) t inter s) = ν (t inter s) := by
  rw [add_comm] at ht ⊢
  exact measure_toMeasurable_add_inter_left hs ht

/-! ### The complete lattice of measures -/


/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: {_ : MeasurableSpace α}
  body: forall s, m₁ s <= m₂ s
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ s := le_trans (h₁ s) (h₂ s)
  le_antisymm _ _ h₁ h₂ := ext fun s _ => le_antisymm (h₁ s) (h₂ s)

中文:
实例 instPartialOrder
  签名: {_ : 可测空间 α}
  定义体: forall s, m₁ s <= m₂ s
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ s := le_trans (h₁ s) (h₂ s)
  le_antisymm _ _ h₁ h₂ := ext fun s _ => le_antisymm (h₁ s) (h₂ s)
-/
instance instPartialOrder {_ : MeasurableSpace α} : PartialOrder (Measure α) where
  le m₁ m₂ := forall s, m₁ s <= m₂ s
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ s := le_trans (h₁ s) (h₂ s)
  le_antisymm _ _ h₁ h₂ := ext fun s _ => le_antisymm (h₁ s) (h₂ s)

/--
theorem `toOuterMeasure_le` / 定理 `toOuterMeasure_le`

English:
theorem toOuterMeasure_le
  statement: μ₁.toOuterMeasure <= μ₂.toOuterMeasure ↔ μ₁ <= μ₂
  proof: .rfl

中文:
定理 toOuterMeasure_le
  结论: μ₁.toOuterMeasure <= μ₂.toOuterMeasure ↔ μ₁ <= μ₂
  证明: .rfl
-/
theorem toOuterMeasure_le : μ₁.toOuterMeasure <= μ₂.toOuterMeasure ↔ μ₁ <= μ₂ := .rfl

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  statement: μ₁ <= μ₂ ↔ forall s, MeasurableSet s -> μ₁ s <= μ₂ s
  proof: outerMeasure_le_iff

中文:
定理 le_iff
  结论: μ₁ <= μ₂ ↔ 对任意 s, 可测集 s -> μ₁ s <= μ₂ s
  证明: outerMeasure_le_iff

Depends on / 依赖: outerMeasure_le_iff
-/
theorem le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSet s -> μ₁ s <= μ₂ s := outerMeasure_le_iff

/--
theorem `le_intro` / 定理 `le_intro`

English:
theorem le_intro
  given: (h : forall s, MeasurableSet s -> s.Nonempty -> μ₁ s <= μ₂ s)
  statement: μ₁ <= μ₂
  proof: le_iff.2 fun s hs => s.eq_empty_or_nonempty.elim (by rintro rfl; simp) (h s hs)

中文:
定理 le_intro
  条件: (h : 对任意 s, 可测集 s -> s.非空 -> μ₁ s <= μ₂ s)
  结论: μ₁ <= μ₂
  证明: le_iff.2 fun s hs => s.eq_empty_or_nonempty.elim (by rintro rfl; simp) (h s hs)

Depends on / 依赖: eq_empty_or_nonempty, le_iff, s.eq_empty_or_nonempty.elim
-/
theorem le_intro (h : forall s, MeasurableSet s -> s.Nonempty -> μ₁ s <= μ₂ s) : μ₁ <= μ₂ :=
  le_iff.2 fun s hs => s.eq_empty_or_nonempty.elim (by rintro rfl; simp) (h s hs)

/--
theorem `le_iff'` / 定理 `le_iff'`

English:
theorem le_iff'
  statement: μ₁ <= μ₂ ↔ forall s, μ₁ s <= μ₂ s
  proof: .rfl

中文:
定理 le_iff'
  结论: μ₁ <= μ₂ ↔ 对任意 s, μ₁ s <= μ₂ s
  证明: .rfl
-/
theorem le_iff' : μ₁ <= μ₂ ↔ forall s, μ₁ s <= μ₂ s := .rfl

/--
theorem `measure_mono_left` / 定理 `measure_mono_left`

English:
theorem measure_mono_left
  given: (h : μ <= ν) (s : Set α)
  statement: μ s <= ν s
  proof: h s

@[gcongr]

中文:
定理 measure_mono_left
  条件: (h : μ <= ν) (s : 集合 α)
  结论: μ s <= ν s
  证明: h s

@[gcongr]
-/
@[gcongr] theorem measure_mono_left (h : μ <= ν) (s : Set α) : μ s <= ν s := h s

@[gcongr]
/--
theorem `measure_mono_both` / 定理 `measure_mono_both`

English:
theorem measure_mono_both
  given: (h₁ : μ <= ν) (h₂ : s subseteq t)
  statement: μ s <= ν t
  proof: (h₁ s).trans (measure_mono h₂)

中文:
定理 measure_mono_both
  条件: (h₁ : μ <= ν) (h₂ : s subseteq t)
  结论: μ s <= ν t
  证明: (h₁ s).trans (measure_mono h₂)

Depends on / 依赖: measure_mono
-/
theorem measure_mono_both (h₁ : μ <= ν) (h₂ : s subseteq t) : μ s <= ν t :=
  (h₁ s).trans (measure_mono h₂)

/--
theorem `lt_iff` / 定理 `lt_iff`

English:
theorem lt_iff
  statement: μ < ν ↔ μ <= ν ∧ exists s, MeasurableSet s ∧ μ s < ν s
  proof: lt_iff_le_not_ge.trans
and_congr Iff.rfl by simp only [le_iff, not_forall, not_le, exists_prop]

中文:
定理 lt_iff
  结论: μ < ν ↔ μ <= ν ∧ 存在 s, 可测集 s ∧ μ s < ν s
  证明: lt_iff_le_not_ge.trans
and_congr Iff.rfl by simp only [le_iff, not_forall, not_le, exists_prop]

Depends on / 依赖: Iff.rfl, and_congr, exists_prop, le_iff, lt_iff_le_not_ge, lt_iff_le_not_ge.trans, not_forall, not_le
-/
theorem lt_iff : μ < ν ↔ μ <= ν ∧ exists s, MeasurableSet s ∧ μ s < ν s :=
lt_iff_le_not_ge.trans
and_congr Iff.rfl by simp only [le_iff, not_forall, not_le, exists_prop]

/--
theorem `lt_iff'` / 定理 `lt_iff'`

English:
theorem lt_iff'
  statement: μ < ν ↔ μ <= ν ∧ exists s, μ s < ν s
  proof: lt_iff_le_not_ge.trans and_congr Iff.rfl by simp only [le_iff', not_forall, not_le]

中文:
定理 lt_iff'
  结论: μ < ν ↔ μ <= ν ∧ 存在 s, μ s < ν s
  证明: lt_iff_le_not_ge.trans and_congr Iff.rfl by simp only [le_iff', not_forall, not_le]

Depends on / 依赖: Iff.rfl, and_congr, le_iff, lt_iff_le_not_ge, lt_iff_le_not_ge.trans, not_forall, not_le
-/
theorem lt_iff' : μ < ν ↔ μ <= ν ∧ exists s, μ s < ν s :=
lt_iff_le_not_ge.trans and_congr Iff.rfl by simp only [le_iff', not_forall, not_le]

/--
Instance `instIsOrderedAddMonoid` / 实例 `instIsOrderedAddMonoid`

English:
instance instIsOrderedAddMonoid
  signature: {_ : MeasurableSpace α}
  body: add_le_add_left (h s) _

中文:
实例 instIsOrderedAddMonoid
  签名: {_ : 可测空间 α}
  定义体: add_le_add_left (h s) _

Depends on / 依赖: add_le_add_left
-/
instance instIsOrderedAddMonoid {_ : MeasurableSpace α} : IsOrderedAddMonoid (Measure α) where
  add_le_add_left _ _ h _ s := add_le_add_left (h s) _

/--
theorem `le_add_left` / 定理 `le_add_left`

English:
theorem le_add_left
  given: (h : μ <= ν)
  statement: μ <= ν' + ν
  proof: fun s => le_add_left (h s)

中文:
定理 le_add_left
  条件: (h : μ <= ν)
  结论: μ <= ν' + ν
  证明: fun s => le_add_left (h s)
-/
protected theorem le_add_left (h : μ <= ν) : μ <= ν' + ν := fun s => le_add_left (h s)

/--
theorem `le_add_right` / 定理 `le_add_right`

English:
theorem le_add_right
  given: (h : μ <= ν)
  statement: μ <= ν + ν'
  proof: fun s => le_add_right (h s)

中文:
定理 le_add_right
  条件: (h : μ <= ν)
  结论: μ <= ν + ν'
  证明: fun s => le_add_right (h s)
-/
protected theorem le_add_right (h : μ <= ν) : μ <= ν + ν' := fun s => le_add_right (h s)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] [CovariantClass R Real>=0∞ (· • ·) (· <= ·)] :
  body: by
    simp only [smul_apply]
    gcongr

中文:
实例 [标量乘法
  签名: R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞] [协变类 R 实数>=0∞ (· • ·) (· <= ·)] :
  定义体: by
    simp only [smul_apply]
    gcongr

Depends on / 依赖: smul_apply
-/
instance [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] [CovariantClass R Real>=0∞ (· • ·) (· <= ·)] :
    CovariantClass R (Measure α) (· • ·) (· <= ·) where
  elim c μ ν hμν s := by
    simp only [smul_apply]
    gcongr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R Real>=0∞] [LE R] [IsScalarTower R Real>=0∞ Real>=0∞] [IsOrderedSMul R Real>=0∞] :
  body: by gcongr
  smul_le_smul_right a b hab μ s := by
    simp only [smul_apply]
    gcongr

中文:
实例 [标量乘法
  签名: R 实数>=0∞] [LE R] [标量塔 R 实数>=0∞ 实数>=0∞] [是OrderedSMul R 实数>=0∞] :
  定义体: by gcongr
  smul_le_smul_right a b hab μ s := by
    simp only [smul_apply]
    gcongr

Depends on / 依赖: smul_apply, smul_le_smul_right
-/
instance [SMul R Real>=0∞] [LE R] [IsScalarTower R Real>=0∞ Real>=0∞] [IsOrderedSMul R Real>=0∞] :
    IsOrderedSMul R (Measure α) where
  smul_le_smul_left μ ν hμν a s := by gcongr
  smul_le_smul_right a b hab μ s := by
    simp only [smul_apply]
    gcongr

section sInf

variable {m : Set (Measure α)}

/--
theorem `sInf_caratheodory` / 定理 `sInf_caratheodory`

English:
theorem sInf_caratheodory
  given: (s : Set α) (hs : MeasurableSet s)
  proof: by
  rw [OuterMeasure.sInf_eq_boundedBy_sInfGen]
  refine OuterMeasure.boundedBy_caratheodory fun t => ?_
  simp only [OuterMeasure.sInfGen, le_iInf_iff, forall_mem_image, measure_eq_iInf t,
    coe_toOuterMeasure]
  intro μ hμ u htu _hu
  have hm : forall {s t}, s subseteq t -> OuterMeasure.sInfGen (toOuterMeasure '' m) s <= μ t := by
    intro s t hst
    rw [OuterMeasure.sInfGen_def]; rw [iInf_image]
exact iInf₂_le_of_le μ hμ measure_mono hst
  rw [← measure_inter_add_sdiff u hs]
  exact add_le_add (hm <| inter_subset_inter_left _ htu) (hm <| sdiff_subset_sdiff_left htu)

中文:
定理 sInf_caratheodory
  条件: (s : 集合 α) (hs : 可测集 s)
  证明: by
  rw [OuterMeasure.sInf_eq_boundedBy_sInfGen]
  refine OuterMeasure.boundedBy_caratheodory fun t => ?_
  simp only [OuterMeasure.sInfGen, le_iInf_iff, forall_mem_image, measure_eq_iInf t,
    coe_toOuterMeasure]
  intro μ hμ u htu _hu
  have hm : forall {s t}, s subseteq t -> OuterMeasure.sInfGen (toOuterMeasure '' m) s <= μ t := by
    intro s t hst
    rw [OuterMeasure.sInfGen_def]; rw [iInf_image]
exact iInf₂_le_of_le μ hμ measure_mono hst
  rw [← measure_inter_add_sdiff u hs]
  exact add_le_add (hm <| inter_subset_inter_left _ htu) (hm <| sdiff_subset_sdiff_left htu)

Depends on / 依赖: OuterMeasure, OuterMeasure.boundedBy_caratheodory, OuterMeasure.sInfGen, OuterMeasure.sInfGen_def, OuterMeasure.sInf_eq_boundedBy_sInfGen, add_le_add, boundedBy_caratheodory, coe_toOuterMeasure, forall_mem_image, iInf_image, inter_subset, le_iInf_iff, measure_eq_iInf, measure_inter_add_sdiff, measure_mono, sInfGen, sInfGen_def, sInf_eq_boundedBy_sInfGen, subseteq, toOuterMeasure
-/
theorem sInf_caratheodory (s : Set α) (hs : MeasurableSet s) :
    MeasurableSet[(sInf (toOuterMeasure '' m)).caratheodory] s := by
  rw [OuterMeasure.sInf_eq_boundedBy_sInfGen]
  refine OuterMeasure.boundedBy_caratheodory fun t => ?_
  simp only [OuterMeasure.sInfGen, le_iInf_iff, forall_mem_image, measure_eq_iInf t,
    coe_toOuterMeasure]
  intro μ hμ u htu _hu
  have hm : forall {s t}, s subseteq t -> OuterMeasure.sInfGen (toOuterMeasure '' m) s <= μ t := by
    intro s t hst
    rw [OuterMeasure.sInfGen_def]; rw [iInf_image]
exact iInf₂_le_of_le μ hμ measure_mono hst
  rw [← measure_inter_add_sdiff u hs]
  exact add_le_add (hm <| inter_subset_inter_left _ htu) (hm <| sdiff_subset_sdiff_left htu)

instance {_ : MeasurableSpace α} : InfSet (Measure α) :=
⟨fun m => (sInf (toOuterMeasure '' m)).toMeasure sInf_caratheodory⟩

/--
theorem `sInf_apply` / 定理 `sInf_apply`

English:
theorem sInf_apply
  given: (hs : MeasurableSet s)
  statement: sInf m s = sInf (toOuterMeasure '' m) s
  proof: toMeasure_apply _ _ hs

中文:
定理 sInf_apply
  条件: (hs : 可测集 s)
  结论: sInf m s = sInf (toOuterMeasure '' m) s
  证明: toMeasure_apply _ _ hs

Depends on / 依赖: toMeasure_apply
-/
theorem sInf_apply (hs : MeasurableSet s) : sInf m s = sInf (toOuterMeasure '' m) s :=
  toMeasure_apply _ _ hs

/--
theorem `measure_sInf_le` / 定理 `measure_sInf_le`

English:
theorem measure_sInf_le
  given: (h : μ in m)
  statement: sInf m <= μ
  proof: have : sInf (toOuterMeasure '' m) <= μ.toOuterMeasure := sInf_le (mem_image_of_mem _ h)
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s

中文:
定理 measure_sInf_le
  条件: (h : μ in m)
  结论: sInf m <= μ
  证明: have : sInf (toOuterMeasure '' m) <= μ.toOuterMeasure := sInf_le (mem_image_of_mem _ h)
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s
-/
private theorem measure_sInf_le (h : μ in m) : sInf m <= μ :=
  have : sInf (toOuterMeasure '' m) <= μ.toOuterMeasure := sInf_le (mem_image_of_mem _ h)
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s

/--
theorem `measure_le_sInf` / 定理 `measure_le_sInf`

English:
theorem measure_le_sInf
  given: (h : forall μ' in m, μ <= μ')
  statement: μ <= sInf m
  proof: have : μ.toOuterMeasure <= sInf (toOuterMeasure '' m) :=
le_sInf forall_mem_image.2 fun _ hμ => toOuterMeasure_le.2 h _ hμ
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s

中文:
定理 measure_le_sInf
  条件: (h : 对任意 μ' in m, μ <= μ')
  结论: μ <= sInf m
  证明: have : μ.toOuterMeasure <= sInf (toOuterMeasure '' m) :=
le_sInf forall_mem_image.2 fun _ hμ => toOuterMeasure_le.2 h _ hμ
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s
-/
private theorem measure_le_sInf (h : forall μ' in m, μ <= μ') : μ <= sInf m :=
  have : μ.toOuterMeasure <= sInf (toOuterMeasure '' m) :=
le_sInf forall_mem_image.2 fun _ hμ => toOuterMeasure_le.2 h _ hμ
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s

/--
Instance `instCompleteSemilatticeInf` / 实例 `instCompleteSemilatticeInf`

English:
instance instCompleteSemilatticeInf
  signature: {_ : MeasurableSpace α}
  body: private ⟨fun _ => measure_sInf_le, fun _ => measure_le_sInf⟩

中文:
实例 instCompleteSemilatticeInf
  签名: {_ : 可测空间 α}
  定义体: private ⟨fun _ => measure_sInf_le, fun _ => measure_le_sInf⟩

Depends on / 依赖: measure_le_sInf, measure_sInf_le, private
-/
instance instCompleteSemilatticeInf {_ : MeasurableSpace α} :
    CompleteSemilatticeInf (Measure α) where
  isGLB_sInf _ := private ⟨fun _ => measure_sInf_le, fun _ => measure_le_sInf⟩

/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: {_ : MeasurableSpace α}
  body: { completeLatticeOfCompleteSemilatticeInf (Measure α) with
    top :=
      { toOuterMeasure := ⊤,
        m_iUnion := by
          intro f _ _
          refine (measure_iUnion_le _).antisymm ?_
          if hne : (⋃ i, f i).Nonempty then
            rw [OuterMeasure.top_apply hne]
            exact le_top
          else
            simp_all [Set.not_nonempty_iff_eq_empty]
        trim_le := le_top },
    le_top := fun _ => toOuterMeasure_le.mp le_top
    bot := 0
    bot_le := fun _a _s => bot_le }

中文:
实例 instCompleteLattice
  签名: {_ : 可测空间 α}
  定义体: { completeLatticeOfCompleteSemilatticeInf (Measure α) with
    top :=
      { toOuterMeasure := ⊤,
        m_iUnion := by
          intro f _ _
          refine (measure_iUnion_le _).antisymm ?_
          if hne : (⋃ i, f i).Nonempty then
            rw [OuterMeasure.top_apply hne]
            exact le_top
          else
            simp_all [Set.not_nonempty_iff_eq_empty]
        trim_le := le_top },
    le_top := fun _ => toOuterMeasure_le.mp le_top
    bot := 0
    bot_le := fun _a _s => bot_le }

Depends on / 依赖: Measure, Nonempty, OuterMeasure, OuterMeasure.top_apply, Set.not_nonempty_iff_eq_empty, antisymm, bot_le, completeLatticeOfCompleteSemilatticeInf, le_top, m_iUnion, measure_iUnion_le, not_nonempty_iff_eq_empty, toOuterMeasure, toOuterMeasure_le, toOuterMeasure_le.mp, top_apply, trim_le
-/
instance instCompleteLattice {_ : MeasurableSpace α} : CompleteLattice (Measure α) :=
  { completeLatticeOfCompleteSemilatticeInf (Measure α) with
    top :=
      { toOuterMeasure := ⊤,
        m_iUnion := by
          intro f _ _
          refine (measure_iUnion_le _).antisymm ?_
          if hne : (⋃ i, f i).Nonempty then
            rw [OuterMeasure.top_apply hne]
            exact le_top
          else
            simp_all [Set.not_nonempty_iff_eq_empty]
        trim_le := le_top },
    le_top := fun _ => toOuterMeasure_le.mp le_top
    bot := 0
    bot_le := fun _a _s => bot_le }

end sInf

/--
lemma `inf_apply` / 引理 `inf_apply`

English:
lemma inf_apply
  given: {s : Set α} (hs : MeasurableSet s)
  proof: by
  -- `(μ ⊓ ν) s` is defined as `⊓ (t : ℕ → Set α) (ht : s ⊆ ⋃ n, t n), ∑' n, μ (t n) ⊓ ν (t n)`
  rw [← sInf_pair]; rw [Measure.sInf_apply hs]; rw [OuterMeasure.sInf_apply
    (image_nonempty.2 <| insert_nonempty μ {ν})]
  refine le_antisymm (le_sInf fun m ⟨t, ht₁⟩ => ?_) (le_iInf₂ fun t' ht' => ?_)
  · subst ht₁
    -- We first show `(μ ⊓ ν) s ≤ μ (t ∩ s) + ν (tᶜ ∩ s)` for any `t : Set α`
    -- For this, define the sequence `t' : ℕ → Set α` where `t' 0 = t ∩ s`, `t' 1 = tᶜ ∩ s` and
    -- `∅` otherwise. Then, we have by construction
    -- `(μ ⊓ ν) s ≤ ∑' n, μ (t' n) ⊓ ν (t' n) ≤ μ (t' 0) + ν (t' 1) = μ (t ∩ s) + ν (tᶜ ∩ s)`.
    set t' : Nat -> Set α := fun n => if n = 0 then t inter s else if n = 1 then tᶜ inter s else ∅ with ht'
    refine (iInf₂_le t' fun x hx => ?_).trans ?_
    · by_cases hxt : x in t
      · refine mem_iUnion.2 ⟨0, ?_⟩
        simp [hx, hxt]
      · refine mem_iUnion.2 ⟨1, ?_⟩
        simp [hx, hxt]
    · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
      rw [tsum_eq_add_tsum_ite 0]; rw [tsum_eq_add_tsum_ite 1]; rw [if_neg zero_ne_one.symm]; rw [ENNReal.summable.tsum_eq_zero_iff.2 _]; rw [add_zero]
      · exact add_le_add (inf_le_left.trans <| by simp [ht']) (inf_le_right.trans <| by simp [ht'])
      · simp only [ite_eq_left_iff]
        intro n hn₁ hn₀
        simp only [ht', if_neg hn₀, if_neg hn₁, measure_empty, le_refl, inf_of_le_left]
  · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
    -- Conversely, fixing `t' : ℕ → Set α` such that `s ⊆ ⋃ n, t' n`, we construct `t : Set α`
    -- for which `μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n, μ (t' n) ⊓ ν (t' n)`.
    -- Denoting `I := {n | μ (t' n) ≤ ν (t' n)}`, we set `t = ⋃ n ∈ I, t' n`.
    -- Clearly `μ (t ∩ s) ≤ ∑' n ∈ I, μ (t' n)` and `ν (tᶜ ∩ s) ≤ ∑' n ∉ I, ν (t' n)`, so
    -- `μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n ∈ I, μ (t' n) + ∑' n ∉ I, ν (t' n)`
    -- where the RHS equals `∑' n, μ (t' n) ⊓ ν (t' n)` by the choice of `I`.
    set t := ⋃ n in {k : Nat | μ (t' k) <= ν (t' k)}, t' n with ht
    suffices hadd : μ (t inter s) + ν (tᶜ inter s) <= ∑' n, μ (t' n) ⊓ ν (t' n) by
      exact le_trans (sInf_le ⟨t, rfl⟩) hadd
    have hle₁ : μ (t inter s) <= ∑' (n : {k | μ (t' k) <= ν (t' k)}), μ (t' n) :=
(measure_mono inter_subset_left).trans measure_biUnion_le _ (to_countable _) _
    have hcap : tᶜ inter s subseteq ⋃ n in {k | ν (t' k) < μ (t' k)}, t' n := by
      simp_rw [ht, compl_iUnion]
      refine fun x ⟨hx₁, hx₂⟩ => mem_iUnion₂.2 ?_
obtain ⟨i, hi⟩ := mem_iUnion.1 ht' hx₂
      refine ⟨i, ?_, hi⟩
      by_contra h
      simp only [mem_ofPred_eq, not_lt] at h
      exact mem_iInter₂.1 hx₁ i h hi
    have hle₂ : ν (tᶜ inter s) <= ∑' (n : {k | ν (t' k) < μ (t' k)}), ν (t' n) :=
      (measure_mono hcap).trans (measure_biUnion_le ν (to_countable {k | ν (t' k) < μ (t' k)}) _)
    refine (add_le_add hle₁ hle₂).trans ?_
    have heq : {k | μ (t' k) <= ν (t' k)} union {k | ν (t' k) < μ (t' k)} = univ := by
      ext k; simp [le_or_gt]
    conv in ∑' (n : Nat), μ (t' n) ⊓ ν (t' n) => rw [← tsum_univ, ← heq]
    rw [ENNReal.summable.tsum_union_disjoint (f := fun n => μ (t' n) ⊓ ν (t' n)) ?_ ENNReal.summable]
    · refine add_le_add (tsum_congr ?_).le (tsum_congr ?_).le
      · rw [Subtype.forall]
        intro n hn; simpa
      · rw [Subtype.forall]
        intro n hn
        rw [mem_ofPred_eq] at hn
        simp [le_of_lt hn]
    · rw [Set.disjoint_iff]
      rintro k ⟨hk₁, hk₂⟩
      rw [mem_ofPred_eq] at hk₁ hk₂
exact False.elim hk₂.not_ge hk₁

@[simp]

中文:
引理 inf_apply
  条件: {s : 集合 α} (hs : 可测集 s)
  证明: by
  -- `(μ ⊓ ν) s` is defined as `⊓ (t : ℕ → Set α) (ht : s ⊆ ⋃ n, t n), ∑' n, μ (t n) ⊓ ν (t n)`
  rw [← sInf_pair]; rw [Measure.sInf_apply hs]; rw [OuterMeasure.sInf_apply
    (image_nonempty.2 <| insert_nonempty μ {ν})]
  refine le_antisymm (le_sInf fun m ⟨t, ht₁⟩ => ?_) (le_iInf₂ fun t' ht' => ?_)
  · subst ht₁
    -- We first show `(μ ⊓ ν) s ≤ μ (t ∩ s) + ν (tᶜ ∩ s)` for any `t : Set α`
    -- For this, define the sequence `t' : ℕ → Set α` where `t' 0 = t ∩ s`, `t' 1 = tᶜ ∩ s` and
    -- `∅` otherwise. Then, we have by construction
    -- `(μ ⊓ ν) s ≤ ∑' n, μ (t' n) ⊓ ν (t' n) ≤ μ (t' 0) + ν (t' 1) = μ (t ∩ s) + ν (tᶜ ∩ s)`.
    set t' : Nat -> Set α := fun n => if n = 0 then t inter s else if n = 1 then tᶜ inter s else ∅ with ht'
    refine (iInf₂_le t' fun x hx => ?_).trans ?_
    · by_cases hxt : x in t
      · refine mem_iUnion.2 ⟨0, ?_⟩
        simp [hx, hxt]
      · refine mem_iUnion.2 ⟨1, ?_⟩
        simp [hx, hxt]
    · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
      rw [tsum_eq_add_tsum_ite 0]; rw [tsum_eq_add_tsum_ite 1]; rw [if_neg zero_ne_one.symm]; rw [ENNReal.summable.tsum_eq_zero_iff.2 _]; rw [add_zero]
      · exact add_le_add (inf_le_left.trans <| by simp [ht']) (inf_le_right.trans <| by simp [ht'])
      · simp only [ite_eq_left_iff]
        intro n hn₁ hn₀
        simp only [ht', if_neg hn₀, if_neg hn₁, measure_empty, le_refl, inf_of_le_left]
  · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
    -- Conversely, fixing `t' : ℕ → Set α` such that `s ⊆ ⋃ n, t' n`, we construct `t : Set α`
    -- for which `μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n, μ (t' n) ⊓ ν (t' n)`.
    -- Denoting `I := {n | μ (t' n) ≤ ν (t' n)}`, we set `t = ⋃ n ∈ I, t' n`.
    -- Clearly `μ (t ∩ s) ≤ ∑' n ∈ I, μ (t' n)` and `ν (tᶜ ∩ s) ≤ ∑' n ∉ I, ν (t' n)`, so
    -- `μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n ∈ I, μ (t' n) + ∑' n ∉ I, ν (t' n)`
    -- where the RHS equals `∑' n, μ (t' n) ⊓ ν (t' n)` by the choice of `I`.
    set t := ⋃ n in {k : Nat | μ (t' k) <= ν (t' k)}, t' n with ht
    suffices hadd : μ (t inter s) + ν (tᶜ inter s) <= ∑' n, μ (t' n) ⊓ ν (t' n) by
      exact le_trans (sInf_le ⟨t, rfl⟩) hadd
    have hle₁ : μ (t inter s) <= ∑' (n : {k | μ (t' k) <= ν (t' k)}), μ (t' n) :=
(measure_mono inter_subset_left).trans measure_biUnion_le _ (to_countable _) _
    have hcap : tᶜ inter s subseteq ⋃ n in {k | ν (t' k) < μ (t' k)}, t' n := by
      simp_rw [ht, compl_iUnion]
      refine fun x ⟨hx₁, hx₂⟩ => mem_iUnion₂.2 ?_
obtain ⟨i, hi⟩ := mem_iUnion.1 ht' hx₂
      refine ⟨i, ?_, hi⟩
      by_contra h
      simp only [mem_ofPred_eq, not_lt] at h
      exact mem_iInter₂.1 hx₁ i h hi
    have hle₂ : ν (tᶜ inter s) <= ∑' (n : {k | ν (t' k) < μ (t' k)}), ν (t' n) :=
      (measure_mono hcap).trans (measure_biUnion_le ν (to_countable {k | ν (t' k) < μ (t' k)}) _)
    refine (add_le_add hle₁ hle₂).trans ?_
    have heq : {k | μ (t' k) <= ν (t' k)} union {k | ν (t' k) < μ (t' k)} = univ := by
      ext k; simp [le_or_gt]
    conv in ∑' (n : Nat), μ (t' n) ⊓ ν (t' n) => rw [← tsum_univ, ← heq]
    rw [ENNReal.summable.tsum_union_disjoint (f := fun n => μ (t' n) ⊓ ν (t' n)) ?_ ENNReal.summable]
    · refine add_le_add (tsum_congr ?_).le (tsum_congr ?_).le
      · rw [Subtype.forall]
        intro n hn; simpa
      · rw [Subtype.forall]
        intro n hn
        rw [mem_ofPred_eq] at hn
        simp [le_of_lt hn]
    · rw [Set.disjoint_iff]
      rintro k ⟨hk₁, hk₂⟩
      rw [mem_ofPred_eq] at hk₁ hk₂
exact False.elim hk₂.not_ge hk₁

@[simp]
-/
lemma inf_apply {s : Set α} (hs : MeasurableSet s) :
    (μ ⊓ ν) s = sInf {m | exists t, m = μ (t inter s) + ν (tᶜ inter s)} := by
  -- `(μ ⊓ ν) s` is defined as `⊓ (t : ℕ → Set α) (ht : s ⊆ ⋃ n, t n), ∑' n, μ (t n) ⊓ ν (t n)`
  rw [← sInf_pair]; rw [Measure.sInf_apply hs]; rw [OuterMeasure.sInf_apply
    (image_nonempty.2 <| insert_nonempty μ {ν})]
  refine le_antisymm (le_sInf fun m ⟨t, ht₁⟩ => ?_) (le_iInf₂ fun t' ht' => ?_)
  · subst ht₁
    -- We first show `(μ ⊓ ν) s ≤ μ (t ∩ s) + ν (tᶜ ∩ s)` for any `t : Set α`
    -- For this, define the sequence `t' : ℕ → Set α` where `t' 0 = t ∩ s`, `t' 1 = tᶜ ∩ s` and
    -- `∅` otherwise. Then, we have by construction
    -- `(μ ⊓ ν) s ≤ ∑' n, μ (t' n) ⊓ ν (t' n) ≤ μ (t' 0) + ν (t' 1) = μ (t ∩ s) + ν (tᶜ ∩ s)`.
    set t' : Nat -> Set α := fun n => if n = 0 then t inter s else if n = 1 then tᶜ inter s else ∅ with ht'
    refine (iInf₂_le t' fun x hx => ?_).trans ?_
    · by_cases hxt : x in t
      · refine mem_iUnion.2 ⟨0, ?_⟩
        simp [hx, hxt]
      · refine mem_iUnion.2 ⟨1, ?_⟩
        simp [hx, hxt]
    · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
      rw [tsum_eq_add_tsum_ite 0]; rw [tsum_eq_add_tsum_ite 1]; rw [if_neg zero_ne_one.symm]; rw [ENNReal.summable.tsum_eq_zero_iff.2 _]; rw [add_zero]
      · exact add_le_add (inf_le_left.trans <| by simp [ht']) (inf_le_right.trans <| by simp [ht'])
      · simp only [ite_eq_left_iff]
        intro n hn₁ hn₀
        simp only [ht', if_neg hn₀, if_neg hn₁, measure_empty, le_refl, inf_of_le_left]
  · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
    -- Conversely, fixing `t' : ℕ → Set α` such that `s ⊆ ⋃ n, t' n`, we construct `t : Set α`
    -- for which `μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n, μ (t' n) ⊓ ν (t' n)`.
    -- Denoting `I := {n | μ (t' n) ≤ ν (t' n)}`, we set `t = ⋃ n ∈ I, t' n`.
    -- Clearly `μ (t ∩ s) ≤ ∑' n ∈ I, μ (t' n)` and `ν (tᶜ ∩ s) ≤ ∑' n ∉ I, ν (t' n)`, so
    -- `μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n ∈ I, μ (t' n) + ∑' n ∉ I, ν (t' n)`
    -- where the RHS equals `∑' n, μ (t' n) ⊓ ν (t' n)` by the choice of `I`.
    set t := ⋃ n in {k : Nat | μ (t' k) <= ν (t' k)}, t' n with ht
    suffices hadd : μ (t inter s) + ν (tᶜ inter s) <= ∑' n, μ (t' n) ⊓ ν (t' n) by
      exact le_trans (sInf_le ⟨t, rfl⟩) hadd
    have hle₁ : μ (t inter s) <= ∑' (n : {k | μ (t' k) <= ν (t' k)}), μ (t' n) :=
(measure_mono inter_subset_left).trans measure_biUnion_le _ (to_countable _) _
    have hcap : tᶜ inter s subseteq ⋃ n in {k | ν (t' k) < μ (t' k)}, t' n := by
      simp_rw [ht, compl_iUnion]
      refine fun x ⟨hx₁, hx₂⟩ => mem_iUnion₂.2 ?_
obtain ⟨i, hi⟩ := mem_iUnion.1 ht' hx₂
      refine ⟨i, ?_, hi⟩
      by_contra h
      simp only [mem_ofPred_eq, not_lt] at h
      exact mem_iInter₂.1 hx₁ i h hi
    have hle₂ : ν (tᶜ inter s) <= ∑' (n : {k | ν (t' k) < μ (t' k)}), ν (t' n) :=
      (measure_mono hcap).trans (measure_biUnion_le ν (to_countable {k | ν (t' k) < μ (t' k)}) _)
    refine (add_le_add hle₁ hle₂).trans ?_
    have heq : {k | μ (t' k) <= ν (t' k)} union {k | ν (t' k) < μ (t' k)} = univ := by
      ext k; simp [le_or_gt]
    conv in ∑' (n : Nat), μ (t' n) ⊓ ν (t' n) => rw [← tsum_univ, ← heq]
    rw [ENNReal.summable.tsum_union_disjoint (f := fun n => μ (t' n) ⊓ ν (t' n)) ?_ ENNReal.summable]
    · refine add_le_add (tsum_congr ?_).le (tsum_congr ?_).le
      · rw [Subtype.forall]
        intro n hn; simpa
      · rw [Subtype.forall]
        intro n hn
        rw [mem_ofPred_eq] at hn
        simp [le_of_lt hn]
    · rw [Set.disjoint_iff]
      rintro k ⟨hk₁, hk₂⟩
      rw [mem_ofPred_eq] at hk₁ hk₂
exact False.elim hk₂.not_ge hk₁

@[simp]
/--
theorem `_root_.MeasureTheory.OuterMeasure.toMeasure_top` / 定理 `_root_.MeasureTheory.OuterMeasure.toMeasure_top`

English:
theorem _root_.MeasureTheory.OuterMeasure.toMeasure_top
  proof: toOuterMeasure_toMeasure (μ := ⊤)

@[simp]

中文:
定理 _root_.测度论.外测度.toMeasure_top
  证明: toOuterMeasure_toMeasure (μ := ⊤)

@[simp]

Depends on / 依赖: toOuterMeasure_toMeasure
-/
theorem _root_.MeasureTheory.OuterMeasure.toMeasure_top :
    (⊤ : OuterMeasure α).toMeasure (by rw [OuterMeasure.top_caratheodory]; exact le_top) =
      (⊤ : Measure α) :=
  toOuterMeasure_toMeasure (μ := ⊤)

@[simp]
/--
theorem `toOuterMeasure_top` / 定理 `toOuterMeasure_top`

English:
theorem toOuterMeasure_top
  given: {_ : MeasurableSpace α}
  proof: rfl

@[simp]

中文:
定理 toOuterMeasure_top
  条件: {_ : 可测空间 α}
  证明: rfl

@[simp]
-/
theorem toOuterMeasure_top {_ : MeasurableSpace α} :
    (⊤ : Measure α).toOuterMeasure = (⊤ : OuterMeasure α) :=
  rfl

@[simp]
/--
theorem `top_add` / 定理 `top_add`

English:
theorem top_add
  statement: ⊤ + μ = ⊤
  proof: top_unique Measure.le_add_right le_rfl

@[simp]

中文:
定理 top_add
  结论: ⊤ + μ = ⊤
  证明: top_unique Measure.le_add_right le_rfl

@[simp]

Depends on / 依赖: Measure, Measure.le_add_right, le_add_right, le_rfl, top_unique
-/
theorem top_add : ⊤ + μ = ⊤ :=
top_unique Measure.le_add_right le_rfl

@[simp]
/--
theorem `add_top` / 定理 `add_top`

English:
theorem add_top
  statement: μ + ⊤ = ⊤
  proof: top_unique Measure.le_add_left le_rfl

中文:
定理 add_top
  结论: μ + ⊤ = ⊤
  证明: top_unique Measure.le_add_left le_rfl

Depends on / 依赖: Measure, Measure.le_add_left, le_add_left, le_rfl, top_unique
-/
theorem add_top : μ + ⊤ = ⊤ :=
top_unique Measure.le_add_left le_rfl

/--
theorem `zero_le` / 定理 `zero_le`

English:
theorem zero_le
  given: {_m0 : MeasurableSpace α} (μ : Measure α)
  statement: 0 <= μ
  proof: bot_le

中文:
定理 zero_le
  条件: {_m0 : 可测空间 α} (μ : 测度 α)
  结论: 0 <= μ
  证明: bot_le
-/
protected theorem zero_le {_m0 : MeasurableSpace α} (μ : Measure α) : 0 <= μ :=
  bot_le

/--
theorem `nonpos_iff_eq_zero'` / 定理 `nonpos_iff_eq_zero'`

English:
theorem nonpos_iff_eq_zero'
  statement: μ <= 0 ↔ μ = 0
  proof: μ.zero_le.ge_iff_eq'

@[simp]

中文:
定理 nonpos_iff_eq_zero'
  结论: μ <= 0 ↔ μ = 0
  证明: μ.zero_le.ge_iff_eq'

@[simp]

Depends on / 依赖: ge_iff_eq, zero_le, zero_le.ge_iff_eq
-/
theorem nonpos_iff_eq_zero' : μ <= 0 ↔ μ = 0 :=
  μ.zero_le.ge_iff_eq'

@[simp]
/--
theorem `measure_univ_eq_zero` / 定理 `measure_univ_eq_zero`

English:
theorem measure_univ_eq_zero
  statement: μ univ = 0 ↔ μ = 0
  proof: ⟨fun h => bot_unique fun s => (h ▸ measure_mono (subset_univ s) : μ s <= 0), fun h =>
    h.symm ▸ rfl⟩

中文:
定理 measure_univ_eq_zero
  结论: μ univ = 0 ↔ μ = 0
  证明: ⟨fun h => bot_unique fun s => (h ▸ measure_mono (subset_univ s) : μ s <= 0), fun h =>
    h.symm ▸ rfl⟩

Depends on / 依赖: bot_unique, h.symm, measure_mono, subset_univ
-/
theorem measure_univ_eq_zero : μ univ = 0 ↔ μ = 0 :=
  ⟨fun h => bot_unique fun s => (h ▸ measure_mono (subset_univ s) : μ s <= 0), fun h =>
    h.symm ▸ rfl⟩

/--
theorem `measure_univ_ne_zero` / 定理 `measure_univ_ne_zero`

English:
theorem measure_univ_ne_zero
  statement: μ univ != 0 ↔ μ != 0
  proof: measure_univ_eq_zero.not

中文:
定理 measure_univ_ne_zero
  结论: μ univ != 0 ↔ μ != 0
  证明: measure_univ_eq_zero.not

Depends on / 依赖: measure_univ_eq_zero, measure_univ_eq_zero.not
-/
theorem measure_univ_ne_zero : μ univ != 0 ↔ μ != 0 :=
  measure_univ_eq_zero.not

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NeZero
  signature: μ] : NeZero (μ univ)
  body: ⟨measure_univ_ne_zero.2 NeZero.ne μ⟩

@[simp]

中文:
实例 [NeZero
  签名: μ] : NeZero (μ univ)
  定义体: ⟨measure_univ_ne_zero.2 NeZero.ne μ⟩

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, measure_univ_ne_zero
-/
instance [NeZero μ] : NeZero (μ univ) := ⟨measure_univ_ne_zero.2 NeZero.ne μ⟩

@[simp]
/--
theorem `measure_univ_pos` / 定理 `measure_univ_pos`

English:
theorem measure_univ_pos
  statement: 0 < μ univ ↔ μ != 0
  proof: pos_iff_ne_zero.trans measure_univ_ne_zero

中文:
定理 measure_univ_pos
  结论: 0 < μ univ ↔ μ != 0
  证明: pos_iff_ne_zero.trans measure_univ_ne_zero

Depends on / 依赖: measure_univ_ne_zero, pos_iff_ne_zero, pos_iff_ne_zero.trans
-/
theorem measure_univ_pos : 0 < μ univ ↔ μ != 0 :=
  pos_iff_ne_zero.trans measure_univ_ne_zero

/--
lemma `nonempty_of_neZero` / 引理 `nonempty_of_neZero`

English:
lemma nonempty_of_neZero
  given: (μ : Measure α) [NeZero μ]
  statement: Nonempty α
  proof: (isEmpty_or_nonempty α).resolve_left fun h => by
    simpa [eq_empty_of_isEmpty] using NeZero.ne (μ univ)

中文:
引理 nonempty_of_neZero
  条件: (μ : 测度 α) [NeZero μ]
  结论: 非空 α
  证明: (isEmpty_or_nonempty α).resolve_left fun h => by
    simpa [eq_empty_of_isEmpty] using NeZero.ne (μ univ)

Depends on / 依赖: NeZero, NeZero.ne, eq_empty_of_isEmpty, isEmpty_or_nonempty, resolve_left
-/
lemma nonempty_of_neZero (μ : Measure α) [NeZero μ] : Nonempty α :=
  (isEmpty_or_nonempty α).resolve_left fun h => by
    simpa [eq_empty_of_isEmpty] using NeZero.ne (μ univ)

/--
theorem `measure_support_eq_zero_iff` / 定理 `measure_support_eq_zero_iff`

English:
theorem measure_support_eq_zero_iff
  statement: {E : Type*} [Zero E] (μ : Measure α := by volume_tac)
  proof: by
  rfl

中文:
定理 measure_support_eq_zero_iff
  结论: {E : 类型} [零 E] (μ : 测度 α := by volume_tac)
  证明: by
  rfl

Depends on / 依赖: f.support, support, volume_tac
-/
theorem measure_support_eq_zero_iff {E : Type*} [Zero E] (μ : Measure α := by volume_tac)
    {f : α -> E} : μ f.support = 0 ↔ f =ᵐ[μ] 0 := by
  rfl

section Sum
variable {f : ι -> Measure α}

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: (f : ι -> Measure α)
  body: (OuterMeasure.sum fun i => (f i).toOuterMeasure).toMeasure
    le_trans (le_iInf fun _ => le_toOuterMeasure_caratheodory _)
      (OuterMeasure.le_sum_caratheodory _)

中文:
定义 求和
  签名: (f : ι -> 测度 α)
  定义体: (OuterMeasure.sum fun i => (f i).toOuterMeasure).toMeasure
    le_trans (le_iInf fun _ => le_toOuterMeasure_caratheodory _)
      (OuterMeasure.le_sum_caratheodory _)

Depends on / 依赖: OuterMeasure, OuterMeasure.le_sum_caratheodory, OuterMeasure.sum, le_iInf, le_sum_caratheodory, le_toOuterMeasure_caratheodory, le_trans, toMeasure, toOuterMeasure
-/
noncomputable def sum (f : ι -> Measure α) : Measure α :=
(OuterMeasure.sum fun i => (f i).toOuterMeasure).toMeasure
    le_trans (le_iInf fun _ => le_toOuterMeasure_caratheodory _)
      (OuterMeasure.le_sum_caratheodory _)

/--
theorem `le_sum_apply` / 定理 `le_sum_apply`

English:
theorem le_sum_apply
  given: (f : ι -> Measure α) (s : Set α)
  statement: ∑' i, f i s <= sum f s
  proof: le_toMeasure_apply _ _ _

@[simp]

中文:
定理 le_sum_apply
  条件: (f : ι -> 测度 α) (s : 集合 α)
  结论: ∑' i, f i s <= 求和 f s
  证明: le_toMeasure_apply _ _ _

@[simp]

Depends on / 依赖: le_toMeasure_apply
-/
theorem le_sum_apply (f : ι -> Measure α) (s : Set α) : ∑' i, f i s <= sum f s :=
  le_toMeasure_apply _ _ _

@[simp]
/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  given: (f : ι -> Measure α) {s : Set α} (hs : MeasurableSet s)
  proof: toMeasure_apply _ _ hs

中文:
定理 sum_apply
  条件: (f : ι -> 测度 α) {s : 集合 α} (hs : 可测集 s)
  证明: toMeasure_apply _ _ hs

Depends on / 依赖: toMeasure_apply
-/
theorem sum_apply (f : ι -> Measure α) {s : Set α} (hs : MeasurableSet s) :
    sum f s = ∑' i, f i s :=
  toMeasure_apply _ _ hs

/--
theorem `sum_apply₀` / 定理 `sum_apply₀`

English:
theorem sum_apply₀
  given: (f : ι -> Measure α) {s : Set α} (hs : NullMeasurableSet s (sum f))
  proof: by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, t_meas, ht⟩
  calc
  sum f s = sum f t := measure_congr ht.symm
  _ = ∑' i, f i t := sum_apply _ t_meas
  _ <= ∑' i, f i s := ENNReal.tsum_le_tsum fun i => measure_mono ts

中文:
定理 sum_apply₀
  条件: (f : ι -> 测度 α) {s : 集合 α} (hs : NullMeasurableSet s (求和 f))
  证明: by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, t_meas, ht⟩
  calc
  sum f s = sum f t := measure_congr ht.symm
  _ = ∑' i, f i t := sum_apply _ t_meas
  _ <= ∑' i, f i s := ENNReal.tsum_le_tsum fun i => measure_mono ts

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, exists_measurable_subset_ae_eq, hs.exists_measurable_subset_ae_eq, ht.symm, le_antisymm, le_sum_apply, measure_congr, measure_mono, sum_apply, t_meas, tsum_le_tsum
-/
theorem sum_apply₀ (f : ι -> Measure α) {s : Set α} (hs : NullMeasurableSet s (sum f)) :
    sum f s = ∑' i, f i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, t_meas, ht⟩
  calc
  sum f s = sum f t := measure_congr ht.symm
  _ = ∑' i, f i t := sum_apply _ t_meas
  _ <= ∑' i, f i s := ENNReal.tsum_le_tsum fun i => measure_mono ts

/--
theorem `sum_apply_of_countable` / 定理 `sum_apply_of_countable`

English:
theorem sum_apply_of_countable
  given: [Countable ι] (f : ι -> Measure α) (s : Set α)
  proof: by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases exists_measurable_superset_forall_eq f s with ⟨t, hst, htm, ht⟩
  calc
  sum f s <= sum f t := measure_mono hst
  _ = ∑' i, f i t := sum_apply _ htm
  _ = ∑' i, f i s := by simp [ht]

中文:
定理 sum_apply_of_countable
  条件: [可数 ι] (f : ι -> 测度 α) (s : 集合 α)
  证明: by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases exists_measurable_superset_forall_eq f s with ⟨t, hst, htm, ht⟩
  calc
  sum f s <= sum f t := measure_mono hst
  _ = ∑' i, f i t := sum_apply _ htm
  _ = ∑' i, f i s := by simp [ht]

Depends on / 依赖: exists_measurable_superset_forall_eq, le_antisymm, le_sum_apply, measure_mono, sum_apply
-/
theorem sum_apply_of_countable [Countable ι] (f : ι -> Measure α) (s : Set α) :
    sum f s = ∑' i, f i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases exists_measurable_superset_forall_eq f s with ⟨t, hst, htm, ht⟩
  calc
  sum f s <= sum f t := measure_mono hst
  _ = ∑' i, f i t := sum_apply _ htm
  _ = ∑' i, f i s := by simp [ht]

/--
theorem `le_sum` / 定理 `le_sum`

English:
theorem le_sum
  given: (μ : ι -> Measure α) (i : ι)
  statement: μ i <= sum μ
  proof: le_iff.2 fun s hs => by simpa only [sum_apply μ hs] using ENNReal.le_tsum i

@[simp]

中文:
定理 le_sum
  条件: (μ : ι -> 测度 α) (i : ι)
  结论: μ i <= 求和 μ
  证明: le_iff.2 fun s hs => by simpa only [sum_apply μ hs] using ENNReal.le_tsum i

@[simp]

Depends on / 依赖: ENNReal, ENNReal.le_tsum, le_iff, le_tsum, sum_apply
-/
theorem le_sum (μ : ι -> Measure α) (i : ι) : μ i <= sum μ :=
  le_iff.2 fun s hs => by simpa only [sum_apply μ hs] using ENNReal.le_tsum i

@[simp]
/--
theorem `sum_apply_eq_zero` / 定理 `sum_apply_eq_zero`

English:
theorem sum_apply_eq_zero
  given: [Countable ι] {μ : ι -> Measure α} {s : Set α}
  proof: by
  simp [sum_apply_of_countable]

中文:
定理 sum_apply_eq_zero
  条件: [可数 ι] {μ : ι -> 测度 α} {s : 集合 α}
  证明: by
  simp [sum_apply_of_countable]

Depends on / 依赖: sum_apply_of_countable
-/
theorem sum_apply_eq_zero [Countable ι] {μ : ι -> Measure α} {s : Set α} :
    sum μ s = 0 ↔ forall i, μ i s = 0 := by
  simp [sum_apply_of_countable]

/--
theorem `sum_apply_eq_zero'` / 定理 `sum_apply_eq_zero'`

English:
theorem sum_apply_eq_zero'
  given: {μ : ι -> Measure α} {s : Set α} (hs : MeasurableSet s)
  proof: by simp [hs]

中文:
定理 sum_apply_eq_zero'
  条件: {μ : ι -> 测度 α} {s : 集合 α} (hs : 可测集 s)
  证明: by simp [hs]
-/
theorem sum_apply_eq_zero' {μ : ι -> Measure α} {s : Set α} (hs : MeasurableSet s) :
    sum μ s = 0 ↔ forall i, μ i s = 0 := by simp [hs]

/--
lemma `sum_eq_zero` / 引理 `sum_eq_zero`

English:
lemma sum_eq_zero
  statement: sum f = 0 ↔ forall i, f i = 0
  proof: by
  simp +contextual [Measure.ext_iff, forall_comm (α := ι)]

@[simp]

中文:
引理 sum_eq_zero
  结论: 求和 f = 0 ↔ 对任意 i, f i = 0
  证明: by
  simp +contextual [Measure.ext_iff, forall_comm (α := ι)]

@[simp]
-/
@[simp] lemma sum_eq_zero : sum f = 0 ↔ forall i, f i = 0 := by
  simp +contextual [Measure.ext_iff, forall_comm (α := ι)]

@[simp]
/--
lemma `sum_zero` / 引理 `sum_zero`

English:
lemma sum_zero
  statement: Measure.sum (fun (_ : ι) => (0 : Measure α)) = 0
  proof: by
  ext s hs
  simp [Measure.sum_apply _ hs]

中文:
引理 sum_zero
  结论: 测度.求和 (fun (_ : ι) => (0 : 测度 α)) = 0
  证明: by
  ext s hs
  simp [Measure.sum_apply _ hs]

Depends on / 依赖: Measure, Measure.sum_apply, sum_apply
-/
lemma sum_zero : Measure.sum (fun (_ : ι) => (0 : Measure α)) = 0 := by
  ext s hs
  simp [Measure.sum_apply _ hs]

/--
theorem `sum_sum` / 定理 `sum_sum`

English:
theorem sum_sum
  given: {ι' : Type*} (μ : ι -> ι' -> Measure α)
  proof: by
  ext1 s hs
  simp [sum_apply _ hs, ENNReal.tsum_prod']

中文:
定理 sum_sum
  条件: {ι' : 类型} (μ : ι -> ι' -> 测度 α)
  证明: by
  ext1 s hs
  simp [sum_apply _ hs, ENNReal.tsum_prod']

Depends on / 依赖: ENNReal, ENNReal.tsum_prod, sum_apply, tsum_prod
-/
theorem sum_sum {ι' : Type*} (μ : ι -> ι' -> Measure α) :
    (sum fun n => sum (μ n)) = sum (fun (p : ι × ι') => μ p.1 p.2) := by
  ext1 s hs
  simp [sum_apply _ hs, ENNReal.tsum_prod']

/--
theorem `sum_comm` / 定理 `sum_comm`

English:
theorem sum_comm
  given: {ι' : Type*} (μ : ι -> ι' -> Measure α)
  proof: by
  ext1 s hs
  simp_rw [sum_apply _ hs]
  rw [ENNReal.tsum_comm]

中文:
定理 sum_comm
  条件: {ι' : 类型} (μ : ι -> ι' -> 测度 α)
  证明: by
  ext1 s hs
  simp_rw [sum_apply _ hs]
  rw [ENNReal.tsum_comm]

Depends on / 依赖: ENNReal, ENNReal.tsum_comm, simp_rw, sum_apply, tsum_comm
-/
theorem sum_comm {ι' : Type*} (μ : ι -> ι' -> Measure α) :
    (sum fun n => sum (μ n)) = sum fun m => sum fun n => μ n m := by
  ext1 s hs
  simp_rw [sum_apply _ hs]
  rw [ENNReal.tsum_comm]

/--
theorem `ae_sum_iff` / 定理 `ae_sum_iff`

English:
theorem ae_sum_iff
  given: [Countable ι] {μ : ι -> Measure α} {p : α -> Prop}
  proof: sum_apply_eq_zero

中文:
定理 ae_sum_iff
  条件: [可数 ι] {μ : ι -> 测度 α} {p : α -> 命题}
  证明: sum_apply_eq_zero

Depends on / 依赖: sum_apply_eq_zero
-/
theorem ae_sum_iff [Countable ι] {μ : ι -> Measure α} {p : α -> Prop} :
    (forallᵐ x ∂sum μ, p x) ↔ forall i, forallᵐ x ∂μ i, p x :=
  sum_apply_eq_zero

/--
theorem `ae_sum_iff'` / 定理 `ae_sum_iff'`

English:
theorem ae_sum_iff'
  given: {μ : ι -> Measure α} {p : α -> Prop} (h : MeasurableSet { x | p x })
  proof: sum_apply_eq_zero' h.compl

@[simp]

中文:
定理 ae_sum_iff'
  条件: {μ : ι -> 测度 α} {p : α -> 命题} (h : 可测集 { x | p x })
  证明: sum_apply_eq_zero' h.compl

@[simp]

Depends on / 依赖: h.compl, sum_apply_eq_zero
-/
theorem ae_sum_iff' {μ : ι -> Measure α} {p : α -> Prop} (h : MeasurableSet { x | p x }) :
    (forallᵐ x ∂sum μ, p x) ↔ forall i, forallᵐ x ∂μ i, p x :=
  sum_apply_eq_zero' h.compl

@[simp]
/--
theorem `sum_fintype` / 定理 `sum_fintype`

English:
theorem sum_fintype
  given: [Fintype ι] (μ : ι -> Measure α)
  statement: sum μ = ∑ i, μ i
  proof: by
  ext1 s hs
  simp only [sum_apply, finsetSum_apply, hs, tsum_fintype]

中文:
定理 sum_fintype
  条件: [有限类型 ι] (μ : ι -> 测度 α)
  结论: 求和 μ = ∑ i, μ i
  证明: by
  ext1 s hs
  simp only [sum_apply, finsetSum_apply, hs, tsum_fintype]

Depends on / 依赖: finsetSum_apply, sum_apply, tsum_fintype
-/
theorem sum_fintype [Fintype ι] (μ : ι -> Measure α) : sum μ = ∑ i, μ i := by
  ext1 s hs
  simp only [sum_apply, finsetSum_apply, hs, tsum_fintype]

/--
theorem `sum_coe_finset` / 定理 `sum_coe_finset`

English:
theorem sum_coe_finset
  given: (s : Finset ι) (μ : ι -> Measure α)
  proof: by rw [sum_fintype, Finset.sum_coe_sort s μ]

@[simp]

中文:
定理 sum_coe_finset
  条件: (s : 有限集 ι) (μ : ι -> 测度 α)
  证明: by rw [sum_fintype, Finset.sum_coe_sort s μ]

@[simp]

Depends on / 依赖: Finset, Finset.sum_coe_sort, sum_coe_sort, sum_fintype
-/
theorem sum_coe_finset (s : Finset ι) (μ : ι -> Measure α) :
    (sum fun i : s => μ i) = ∑ i in s, μ i := by rw [sum_fintype, Finset.sum_coe_sort s μ]

@[simp]
/--
theorem `ae_sum_eq` / 定理 `ae_sum_eq`

English:
theorem ae_sum_eq
  given: [Countable ι] (μ : ι -> Measure α)
  statement: ae (sum μ) = ⨆ i, ae (μ i)
  proof: Filter.ext fun _ => ae_sum_iff.trans mem_iSup.symm

中文:
定理 ae_sum_eq
  条件: [可数 ι] (μ : ι -> 测度 α)
  结论: ae (求和 μ) = ⨆ i, ae (μ i)
  证明: Filter.ext fun _ => ae_sum_iff.trans mem_iSup.symm

Depends on / 依赖: Filter, Filter.ext, ae_sum_iff, ae_sum_iff.trans, mem_iSup, mem_iSup.symm
-/
theorem ae_sum_eq [Countable ι] (μ : ι -> Measure α) : ae (sum μ) = ⨆ i, ae (μ i) :=
  Filter.ext fun _ => ae_sum_iff.trans mem_iSup.symm

/--
theorem `sum_bool` / 定理 `sum_bool`

English:
theorem sum_bool
  given: (f : Bool -> Measure α)
  statement: sum f = f true + f false
  proof: by
  rw [sum_fintype]; rw [Fintype.sum_bool]

中文:
定理 sum_bool
  条件: (f : 布尔值 -> 测度 α)
  结论: 求和 f = f true + f false
  证明: by
  rw [sum_fintype]; rw [Fintype.sum_bool]

Depends on / 依赖: Fintype, Fintype.sum_bool, sum_bool, sum_fintype
-/
theorem sum_bool (f : Bool -> Measure α) : sum f = f true + f false := by
  rw [sum_fintype]; rw [Fintype.sum_bool]

/--
theorem `sum_cond` / 定理 `sum_cond`

English:
theorem sum_cond
  given: (μ ν : Measure α)
  statement: (sum fun b => cond b μ ν) = μ + ν
  proof: sum_bool _

@[simp]

中文:
定理 sum_cond
  条件: (μ ν : 测度 α)
  结论: (求和 fun b => cond b μ ν) = μ + ν
  证明: sum_bool _

@[simp]

Depends on / 依赖: sum_bool
-/
theorem sum_cond (μ ν : Measure α) : (sum fun b => cond b μ ν) = μ + ν :=
  sum_bool _

@[simp]
/--
theorem `sum_of_isEmpty` / 定理 `sum_of_isEmpty`

English:
theorem sum_of_isEmpty
  given: [IsEmpty ι] (μ : ι -> Measure α)
  statement: sum μ = 0
  proof: by
  rw [← measure_univ_eq_zero]; rw [sum_apply _ MeasurableSet.univ]; rw [tsum_empty]

中文:
定理 sum_of_isEmpty
  条件: [是空 ι] (μ : ι -> 测度 α)
  结论: 求和 μ = 0
  证明: by
  rw [← measure_univ_eq_zero]; rw [sum_apply _ MeasurableSet.univ]; rw [tsum_empty]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, measure_univ_eq_zero, sum_apply, tsum_empty
-/
theorem sum_of_isEmpty [IsEmpty ι] (μ : ι -> Measure α) : sum μ = 0 := by
  rw [← measure_univ_eq_zero]; rw [sum_apply _ MeasurableSet.univ]; rw [tsum_empty]

/--
theorem `sum_add_sum_compl` / 定理 `sum_add_sum_compl`

English:
theorem sum_add_sum_compl
  given: (s : Set ι) (μ : ι -> Measure α)
  proof: by
  ext1 t ht
  simp only [add_apply, sum_apply _ ht]
  exact ENNReal.summable.tsum_add_tsum_compl (f := fun i => μ i t) ENNReal.summable

中文:
定理 sum_add_sum_compl
  条件: (s : 集合 ι) (μ : ι -> 测度 α)
  证明: by
  ext1 t ht
  simp only [add_apply, sum_apply _ ht]
  exact ENNReal.summable.tsum_add_tsum_compl (f := fun i => μ i t) ENNReal.summable

Depends on / 依赖: ENNReal, ENNReal.summable, ENNReal.summable.tsum_add_tsum_compl, add_apply, sum_apply, summable, tsum_add_tsum_compl
-/
theorem sum_add_sum_compl (s : Set ι) (μ : ι -> Measure α) :
    ((sum fun i : s => μ i) + sum fun i : ↥sᶜ => μ i) = sum μ := by
  ext1 t ht
  simp only [add_apply, sum_apply _ ht]
  exact ENNReal.summable.tsum_add_tsum_compl (f := fun i => μ i t) ENNReal.summable

/--
theorem `sum_congr` / 定理 `sum_congr`

English:
theorem sum_congr
  given: {μ ν : Nat -> Measure α} (h : forall n, μ n = ν n)
  statement: sum μ = sum ν
  proof: congr_arg sum (funext h)

中文:
定理 sum_congr
  条件: {μ ν : 自然数 -> 测度 α} (h : 对任意 n, μ n = ν n)
  结论: 求和 μ = 求和 ν
  证明: congr_arg sum (funext h)

Depends on / 依赖: congr_arg
-/
theorem sum_congr {μ ν : Nat -> Measure α} (h : forall n, μ n = ν n) : sum μ = sum ν :=
  congr_arg sum (funext h)

/--
theorem `sum_add_sum` / 定理 `sum_add_sum`

English:
theorem sum_add_sum
  given: {ι : Type*} (μ ν : ι -> Measure α)
  statement: sum μ + sum ν = sum fun n => μ n + ν n
  proof: by
  ext1 s hs
  simp only [add_apply, sum_apply _ hs,
    ENNReal.summable.tsum_add ENNReal.summable]

中文:
定理 sum_add_sum
  条件: {ι : 类型} (μ ν : ι -> 测度 α)
  结论: 求和 μ + 求和 ν = 求和 fun n => μ n + ν n
  证明: by
  ext1 s hs
  simp only [add_apply, sum_apply _ hs,
    ENNReal.summable.tsum_add ENNReal.summable]

Depends on / 依赖: ENNReal, ENNReal.summable, ENNReal.summable.tsum_add, add_apply, sum_apply, summable, tsum_add
-/
theorem sum_add_sum {ι : Type*} (μ ν : ι -> Measure α) : sum μ + sum ν = sum fun n => μ n + ν n := by
  ext1 s hs
  simp only [add_apply, sum_apply _ hs,
    ENNReal.summable.tsum_add ENNReal.summable]

/--
lemma `sum_comp_equiv` / 引理 `sum_comp_equiv`

English:
lemma sum_comp_equiv
  given: {ι ι' : Type*} (e : ι' ≃ ι) (m : ι -> Measure α)
  proof: by
  ext s hs
  simpa [hs, sum_apply] using e.tsum_eq (fun n => m n s)

中文:
引理 sum_comp_equiv
  条件: {ι ι' : 类型} (e : ι' ≃ ι) (m : ι -> 测度 α)
  证明: by
  ext s hs
  simpa [hs, sum_apply] using e.tsum_eq (fun n => m n s)

Depends on / 依赖: WithBot, WithBot.LE, WithBot.instLE, instLE
-/
@[simp] lemma sum_comp_equiv {ι ι' : Type*} (e : ι' ≃ ι) (m : ι -> Measure α) :
    sum (m ∘ e) = sum m := by
  ext s hs
  simpa [hs, sum_apply] using e.tsum_eq (fun n => m n s)

/--
lemma `sum_extend_zero` / 引理 `sum_extend_zero`

English:
lemma sum_extend_zero
  given: {ι ι' : Type*} {f : ι -> ι'} (hf : Injective f) (m : ι -> Measure α)
  proof: by
  ext s hs
  simp [*, Function.apply_extend (fun μ : Measure α => μ s)]

中文:
引理 sum_extend_zero
  条件: {ι ι' : 类型} {f : ι -> ι'} (hf : 单射 f) (m : ι -> 测度 α)
  证明: by
  ext s hs
  simp [*, Function.apply_extend (fun μ : Measure α => μ s)]

Depends on / 依赖: WithBot, WithBot.LE, WithTop, WithTop.instLE, instLE
-/
@[simp] lemma sum_extend_zero {ι ι' : Type*} {f : ι -> ι'} (hf : Injective f) (m : ι -> Measure α) :
    sum (Function.extend f m 0) = sum m := by
  ext s hs
  simp [*, Function.apply_extend (fun μ : Measure α => μ s)]
end Sum

/-! ### The `cofinite` filter -/

/--
Definition of `cofinite` / `cofinite` 的定义

English:
definition cofinite
  signature: {m0 : MeasurableSpace α} (μ : Measure α)
  body: comk (μ · < ∞) (by simp) (fun _ ht _ hs => (measure_mono hs).trans_lt ht) fun s hs t ht =>
(measure_union_le s t).trans_lt ENNReal.add_lt_top.2 ⟨hs, ht⟩

中文:
定义 cofinite
  签名: {m0 : 可测空间 α} (μ : 测度 α)
  定义体: comk (μ · < ∞) (by simp) (fun _ ht _ hs => (measure_mono hs).trans_lt ht) fun s hs t ht =>
(measure_union_le s t).trans_lt ENNReal.add_lt_top.2 ⟨hs, ht⟩

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, add_lt_top, measure_mono, measure_union_le, trans_lt
-/
def cofinite {m0 : MeasurableSpace α} (μ : Measure α) : Filter α :=
  comk (μ · < ∞) (by simp) (fun _ ht _ hs => (measure_mono hs).trans_lt ht) fun s hs t ht =>
(measure_union_le s t).trans_lt ENNReal.add_lt_top.2 ⟨hs, ht⟩

/--
theorem `mem_cofinite` / 定理 `mem_cofinite`

English:
theorem mem_cofinite
  statement: s in μ.cofinite ↔ μ sᶜ < ∞
  proof: Iff.rfl

中文:
定理 mem_cofinite
  结论: s in μ.cofinite ↔ μ sᶜ < ∞
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_cofinite : s in μ.cofinite ↔ μ sᶜ < ∞ :=
  Iff.rfl

/--
theorem `compl_mem_cofinite` / 定理 `compl_mem_cofinite`

English:
theorem compl_mem_cofinite
  statement: sᶜ in μ.cofinite ↔ μ s < ∞
  proof: by rw [mem_cofinite, compl_compl]

中文:
定理 compl_mem_cofinite
  结论: sᶜ in μ.cofinite ↔ μ s < ∞
  证明: by rw [mem_cofinite, compl_compl]

Depends on / 依赖: compl_compl, mem_cofinite
-/
theorem compl_mem_cofinite : sᶜ in μ.cofinite ↔ μ s < ∞ := by rw [mem_cofinite, compl_compl]

/--
theorem `eventually_cofinite` / 定理 `eventually_cofinite`

English:
theorem eventually_cofinite
  given: {p : α -> Prop}
  statement: (forallᶠ x in μ.cofinite, p x) ↔ μ { x | ¬p x } < ∞
  proof: Iff.rfl

中文:
定理 eventually_cofinite
  条件: {p : α -> 命题}
  结论: (对任意ᶠ x in μ.cofinite, p x) ↔ μ { x | ¬p x } < ∞
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, WithBot, WithBot.LT, WithBot.instLT, instLT
-/
theorem eventually_cofinite {p : α -> Prop} : (forallᶠ x in μ.cofinite, p x) ↔ μ { x | ¬p x } < ∞ :=
  Iff.rfl

/--
Instance `cofinite.instIsMeasurablyGenerated` / 实例 `cofinite.instIsMeasurablyGenerated`

English:
instance cofinite.instIsMeasurablyGenerated
  signature: : IsMeasurablyGenerated μ.cofinite where
  body: by
    refine ⟨(toMeasurable μ sᶜ)ᶜ, ?_, (measurableSet_toMeasurable _ _).compl, ?_⟩
    · rwa [compl_mem_cofinite, measure_toMeasurable]
    · rw [compl_subset_comm]
      apply subset_toMeasurable

中文:
实例 cofinite.instIsMeasurablyGenerated
  签名: : 是MeasurablyGenerated μ.cofinite where
  定义体: by
    refine ⟨(toMeasurable μ sᶜ)ᶜ, ?_, (measurableSet_toMeasurable _ _).compl, ?_⟩
    · rwa [compl_mem_cofinite, measure_toMeasurable]
    · rw [compl_subset_comm]
      apply subset_toMeasurable

Depends on / 依赖: WithBot, WithBot.LT, WithTop, WithTop.instLT, compl_mem_cofinite, compl_subset_comm, instLT, measurableSet_toMeasurable, measure_toMeasurable, subset_toMeasurable, toMeasurable
-/
instance cofinite.instIsMeasurablyGenerated : IsMeasurablyGenerated μ.cofinite where
  exists_measurable_subset s hs := by
    refine ⟨(toMeasurable μ sᶜ)ᶜ, ?_, (measurableSet_toMeasurable _ _).compl, ?_⟩
    · rwa [compl_mem_cofinite, measure_toMeasurable]
    · rw [compl_subset_comm]
      apply subset_toMeasurable

/--
theorem `cofinite_le_ae` / 定理 `cofinite_le_ae`

English:
theorem cofinite_le_ae
  statement: μ.cofinite <= ae μ
  proof: by
  intro s hs
  simp_all [mem_cofinite, mem_ae_iff]

中文:
定理 cofinite_le_ae
  结论: μ.cofinite <= ae μ
  证明: by
  intro s hs
  simp_all [mem_cofinite, mem_ae_iff]

Depends on / 依赖: mem_ae_iff, mem_cofinite
-/
theorem cofinite_le_ae : μ.cofinite <= ae μ := by
  intro s hs
  simp_all [mem_cofinite, mem_ae_iff]

end Measure

open Measure

open MeasureTheory

/--
theorem `_root_.AEMeasurable.nullMeasurable` / 定理 `_root_.AEMeasurable.nullMeasurable`

English:
theorem _root_.AEMeasurable.nullMeasurable
  given: {f : α -> β} (h : AEMeasurable f μ)
  proof: let ⟨_g, hgm, hg⟩ := h; hgm.nullMeasurable.congr hg.symm

中文:
定理 _root_.几乎处处可测.nullMeasurable
  条件: {f : α -> β} (h : 几乎处处可测 f μ)
  证明: let ⟨_g, hgm, hg⟩ := h; hgm.nullMeasurable.congr hg.symm
-/
protected theorem _root_.AEMeasurable.nullMeasurable {f : α -> β} (h : AEMeasurable f μ) :
    NullMeasurable f μ :=
  let ⟨_g, hgm, hg⟩ := h; hgm.nullMeasurable.congr hg.symm

/--
lemma `_root_.AEMeasurable.nullMeasurableSet_preimage` / 引理 `_root_.AEMeasurable.nullMeasurableSet_preimage`

English:
lemma _root_.AEMeasurable.nullMeasurableSet_preimage
  statement: {f : α -> β} {s : Set β}
  proof: hf.nullMeasurable hs

@[simp]

中文:
引理 _root_.几乎处处可测.nullMeasurableSet_preimage
  结论: {f : α -> β} {s : 集合 β}
  证明: hf.nullMeasurable hs

@[simp]

Depends on / 依赖: hf.nullMeasurable, nullMeasurable
-/
lemma _root_.AEMeasurable.nullMeasurableSet_preimage {f : α -> β} {s : Set β}
    (hf : AEMeasurable f μ) (hs : MeasurableSet s) : NullMeasurableSet (f ⁻¹' s) μ :=
  hf.nullMeasurable hs

@[simp]
/--
theorem `ae_eq_bot` / 定理 `ae_eq_bot`

English:
theorem ae_eq_bot
  statement: ae μ = ⊥ ↔ μ = 0
  proof: by
  rw [← empty_mem_iff_bot]; rw [mem_ae_iff]; rw [compl_empty]; rw [measure_univ_eq_zero]

@[simp]

中文:
定理 ae_eq_bot
  结论: ae μ = ⊥ ↔ μ = 0
  证明: by
  rw [← empty_mem_iff_bot]; rw [mem_ae_iff]; rw [compl_empty]; rw [measure_univ_eq_zero]

@[simp]

Depends on / 依赖: compl_empty, empty_mem_iff_bot, measure_univ_eq_zero, mem_ae_iff
-/
theorem ae_eq_bot : ae μ = ⊥ ↔ μ = 0 := by
  rw [← empty_mem_iff_bot]; rw [mem_ae_iff]; rw [compl_empty]; rw [measure_univ_eq_zero]

@[simp]
/--
theorem `ae_neBot` / 定理 `ae_neBot`

English:
theorem ae_neBot
  statement: (ae μ).NeBot ↔ μ != 0
  proof: neBot_iff.trans (not_congr ae_eq_bot)

中文:
定理 ae_neBot
  结论: (ae μ).NeBot ↔ μ != 0
  证明: neBot_iff.trans (not_congr ae_eq_bot)

Depends on / 依赖: ae_eq_bot, neBot_iff, neBot_iff.trans, not_congr
-/
theorem ae_neBot : (ae μ).NeBot ↔ μ != 0 :=
  neBot_iff.trans (not_congr ae_eq_bot)

/--
Instance `Measure.ae.neBot` / 实例 `Measure.ae.neBot`

English:
instance Measure.ae.neBot
  signature: [NeZero μ]
  body: ae_neBot.2 NeZero.ne μ

@[simp]

中文:
实例 测度.ae.neBot
  签名: [NeZero μ]
  定义体: ae_neBot.2 NeZero.ne μ

@[simp]

Depends on / 依赖: NeZero, NeZero.ne, ae_neBot
-/
instance Measure.ae.neBot [NeZero μ] : (ae μ).NeBot := ae_neBot.2 NeZero.ne μ

@[simp]
/--
theorem `ae_zero` / 定理 `ae_zero`

English:
theorem ae_zero
  given: {_m0 : MeasurableSpace α}
  statement: ae (0 : Measure α) = ⊥
  proof: ae_eq_bot.2 rfl

中文:
定理 ae_zero
  条件: {_m0 : 可测空间 α}
  结论: ae (0 : 测度 α) = ⊥
  证明: ae_eq_bot.2 rfl

Depends on / 依赖: ae_eq_bot
-/
theorem ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measure α) = ⊥ :=
  ae_eq_bot.2 rfl

section Intervals

/--
theorem `biSup_measure_Iic` / 定理 `biSup_measure_Iic`

English:
theorem biSup_measure_Iic
  statement: [Preorder α] {s : Set α} (hsc : s.Countable)
  proof: by
  rw [← measure_biUnion_eq_iSup hsc]
  · congr
    simp only [← bex_def] at hst
    exact iUnion₂_eq_univ_iff.2 hst
  · exact directedOn_iff_directed.2 (hdir.directed_val.mono_comp _ fun x y => Iic_subset_Iic.2)

中文:
定理 biSup_measure_Iic
  结论: [预序 α] {s : 集合 α} (hsc : s.可数)
  证明: by
  rw [← measure_biUnion_eq_iSup hsc]
  · congr
    simp only [← bex_def] at hst
    exact iUnion₂_eq_univ_iff.2 hst
  · exact directedOn_iff_directed.2 (hdir.directed_val.mono_comp _ fun x y => Iic_subset_Iic.2)

Depends on / 依赖: Iic_subset_Iic, bex_def, directedOn_iff_directed, directed_val, hdir.directed_val.mono_comp, measure_biUnion_eq_iSup, mono_comp
-/
theorem biSup_measure_Iic [Preorder α] {s : Set α} (hsc : s.Countable)
    (hst : forall x : α, exists y in s, x <= y) (hdir : DirectedOn (· <= ·) s) :
    ⨆ x in s, μ (Iic x) = μ univ := by
  rw [← measure_biUnion_eq_iSup hsc]
  · congr
    simp only [← bex_def] at hst
    exact iUnion₂_eq_univ_iff.2 hst
  · exact directedOn_iff_directed.2 (hdir.directed_val.mono_comp _ fun x y => Iic_subset_Iic.2)

/--
theorem `tendsto_measure_Ico_atTop` / 定理 `tendsto_measure_Ico_atTop`

English:
theorem tendsto_measure_Ico_atTop
  statement: [Preorder α] [NoMaxOrder α]
  proof: by
  rw [← iUnion_Ico_right]
  exact tendsto_measure_iUnion_atTop (antitone_const.Ico monotone_id)

中文:
定理 tendsto_measure_Ico_atTop
  结论: [预序 α] [NoMax序 α]
  证明: by
  rw [← iUnion_Ico_right]
  exact tendsto_measure_iUnion_atTop (antitone_const.Ico monotone_id)

Depends on / 依赖: antitone_const, antitone_const.Ico, iUnion_Ico_right, monotone_id, tendsto_measure_iUnion_atTop
-/
theorem tendsto_measure_Ico_atTop [Preorder α] [NoMaxOrder α]
    [(atTop : Filter α).IsCountablyGenerated] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ico a x)) atTop (𝓝 (μ (Ici a))) := by
  rw [← iUnion_Ico_right]
  exact tendsto_measure_iUnion_atTop (antitone_const.Ico monotone_id)

/--
theorem `tendsto_measure_Ioc_atBot` / 定理 `tendsto_measure_Ioc_atBot`

English:
theorem tendsto_measure_Ioc_atBot
  statement: [Preorder α] [NoMinOrder α]
  proof: by
  rw [← iUnion_Ioc_left]
  exact tendsto_measure_iUnion_atBot (monotone_id.Ioc antitone_const)

中文:
定理 tendsto_measure_Ioc_atBot
  结论: [预序 α] [NoMin序 α]
  证明: by
  rw [← iUnion_Ioc_left]
  exact tendsto_measure_iUnion_atBot (monotone_id.Ioc antitone_const)

Depends on / 依赖: antitone_const, iUnion_Ioc_left, monotone_id, monotone_id.Ioc, tendsto_measure_iUnion_atBot
-/
theorem tendsto_measure_Ioc_atBot [Preorder α] [NoMinOrder α]
    [(atBot : Filter α).IsCountablyGenerated] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ioc x a)) atBot (𝓝 (μ (Iic a))) := by
  rw [← iUnion_Ioc_left]
  exact tendsto_measure_iUnion_atBot (monotone_id.Ioc antitone_const)

/--
theorem `tendsto_measure_Iic_atTop` / 定理 `tendsto_measure_Iic_atTop`

English:
theorem tendsto_measure_Iic_atTop
  statement: [Preorder α] [(atTop : Filter α).IsCountablyGenerated]
  proof: by
  rw [← iUnion_Iic]
  exact tendsto_measure_iUnion_atTop monotone_Iic

中文:
定理 tendsto_measure_Iic_atTop
  结论: [预序 α] [(atTop : 滤子 α).是余untablyGenerated]
  证明: by
  rw [← iUnion_Iic]
  exact tendsto_measure_iUnion_atTop monotone_Iic

Depends on / 依赖: iUnion_Iic, monotone_Iic, tendsto_measure_iUnion_atTop
-/
theorem tendsto_measure_Iic_atTop [Preorder α] [(atTop : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Iic x)) atTop (𝓝 (μ univ)) := by
  rw [← iUnion_Iic]
  exact tendsto_measure_iUnion_atTop monotone_Iic

/--
theorem `tendsto_measure_Ici_atBot` / 定理 `tendsto_measure_Ici_atBot`

English:
theorem tendsto_measure_Ici_atBot
  statement: [Preorder α] [(atBot : Filter α).IsCountablyGenerated]
  proof: tendsto_measure_Iic_atTop (α := αᵒᵈ) μ

中文:
定理 tendsto_measure_Ici_atBot
  结论: [预序 α] [(atBot : 滤子 α).是余untablyGenerated]
  证明: tendsto_measure_Iic_atTop (α := αᵒᵈ) μ

Depends on / 依赖: tendsto_measure_Iic_atTop
-/
theorem tendsto_measure_Ici_atBot [Preorder α] [(atBot : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Ici x)) atBot (𝓝 (μ univ)) :=
  tendsto_measure_Iic_atTop (α := αᵒᵈ) μ

variable [PartialOrder α] {a b : α}

/--
theorem `Iio_ae_eq_Iic'` / 定理 `Iio_ae_eq_Iic'`

English:
theorem Iio_ae_eq_Iic'
  given: (ha : μ {a} = 0)
  statement: Iio a =ᵐ[μ] Iic a
  proof: by
  rw [← Iic_sdiff_right]; rw [sdiff_ae_eq_self]; rw [measure_mono_null Set.inter_subset_right ha]

中文:
定理 Iio_ae_eq_Iic'
  条件: (ha : μ {a} = 0)
  结论: 左无界右开区间 a =ᵐ[μ] 左无界右闭区间 a
  证明: by
  rw [← Iic_sdiff_right]; rw [sdiff_ae_eq_self]; rw [measure_mono_null Set.inter_subset_right ha]

Depends on / 依赖: Iic_sdiff_right, Set.inter_subset_right, inter_subset_right, measure_mono_null, sdiff_ae_eq_self
-/
theorem Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ[μ] Iic a := by
  rw [← Iic_sdiff_right]; rw [sdiff_ae_eq_self]; rw [measure_mono_null Set.inter_subset_right ha]

/--
theorem `Ioi_ae_eq_Ici'` / 定理 `Ioi_ae_eq_Ici'`

English:
theorem Ioi_ae_eq_Ici'
  given: (ha : μ {a} = 0)
  statement: Ioi a =ᵐ[μ] Ici a
  proof: Iio_ae_eq_Iic' (α := αᵒᵈ) ha

中文:
定理 Ioi_ae_eq_Ici'
  条件: (ha : μ {a} = 0)
  结论: 左开右无界区间 a =ᵐ[μ] 左闭右无界区间 a
  证明: Iio_ae_eq_Iic' (α := αᵒᵈ) ha

Depends on / 依赖: Iio_ae_eq_Iic
-/
theorem Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ[μ] Ici a :=
  Iio_ae_eq_Iic' (α := αᵒᵈ) ha

/--
theorem `Ioo_ae_eq_Ioc'` / 定理 `Ioo_ae_eq_Ioc'`

English:
theorem Ioo_ae_eq_Ioc'
  given: (hb : μ {b} = 0)
  statement: Ioo a b =ᵐ[μ] Ioc a b
  proof: (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)

中文:
定理 Ioo_ae_eq_Ioc'
  条件: (hb : μ {b} = 0)
  结论: 开区间 a b =ᵐ[μ] 左开右闭区间 a b
  证明: (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)

Depends on / 依赖: Iio_ae_eq_Iic, ae_eq_refl
-/
theorem Ioo_ae_eq_Ioc' (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Ioc a b :=
  (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)

/--
theorem `Ioc_ae_eq_Icc'` / 定理 `Ioc_ae_eq_Icc'`

English:
theorem Ioc_ae_eq_Icc'
  given: (ha : μ {a} = 0)
  statement: Ioc a b =ᵐ[μ] Icc a b
  proof: (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)

中文:
定理 Ioc_ae_eq_Icc'
  条件: (ha : μ {a} = 0)
  结论: 左开右闭区间 a b =ᵐ[μ] 闭区间 a b
  证明: (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)

Depends on / 依赖: Ioi_ae_eq_Ici, ae_eq_refl
-/
theorem Ioc_ae_eq_Icc' (ha : μ {a} = 0) : Ioc a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)

/--
theorem `Ioo_ae_eq_Ico'` / 定理 `Ioo_ae_eq_Ico'`

English:
theorem Ioo_ae_eq_Ico'
  given: (ha : μ {a} = 0)
  statement: Ioo a b =ᵐ[μ] Ico a b
  proof: (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)

中文:
定理 Ioo_ae_eq_Ico'
  条件: (ha : μ {a} = 0)
  结论: 开区间 a b =ᵐ[μ] 左闭右开区间 a b
  证明: (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)

Depends on / 依赖: Ioi_ae_eq_Ici, ae_eq_refl
-/
theorem Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b =ᵐ[μ] Ico a b :=
  (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)

/--
theorem `Ioo_ae_eq_Icc'` / 定理 `Ioo_ae_eq_Icc'`

English:
theorem Ioo_ae_eq_Icc'
  given: (ha : μ {a} = 0) (hb : μ {b} = 0)
  statement: Ioo a b =ᵐ[μ] Icc a b
  proof: (Ioi_ae_eq_Ici' ha).inter (Iio_ae_eq_Iic' hb)

中文:
定理 Ioo_ae_eq_Icc'
  条件: (ha : μ {a} = 0) (hb : μ {b} = 0)
  结论: 开区间 a b =ᵐ[μ] 闭区间 a b
  证明: (Ioi_ae_eq_Ici' ha).inter (Iio_ae_eq_Iic' hb)

Depends on / 依赖: Iio_ae_eq_Iic, Ioi_ae_eq_Ici
-/
theorem Ioo_ae_eq_Icc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (Iio_ae_eq_Iic' hb)

/--
theorem `Ico_ae_eq_Icc'` / 定理 `Ico_ae_eq_Icc'`

English:
theorem Ico_ae_eq_Icc'
  given: (hb : μ {b} = 0)
  statement: Ico a b =ᵐ[μ] Icc a b
  proof: (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)

中文:
定理 Ico_ae_eq_Icc'
  条件: (hb : μ {b} = 0)
  结论: 左闭右开区间 a b =ᵐ[μ] 闭区间 a b
  证明: (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)

Depends on / 依赖: Iio_ae_eq_Iic, ae_eq_refl
-/
theorem Ico_ae_eq_Icc' (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Icc a b :=
  (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)

/--
theorem `Ico_ae_eq_Ioc'` / 定理 `Ico_ae_eq_Ioc'`

English:
theorem Ico_ae_eq_Ioc'
  given: (ha : μ {a} = 0) (hb : μ {b} = 0)
  statement: Ico a b =ᵐ[μ] Ioc a b
  proof: (Ioo_ae_eq_Ico' ha).symm.trans (Ioo_ae_eq_Ioc' hb)

中文:
定理 Ico_ae_eq_Ioc'
  条件: (ha : μ {a} = 0) (hb : μ {b} = 0)
  结论: 左闭右开区间 a b =ᵐ[μ] 左开右闭区间 a b
  证明: (Ioo_ae_eq_Ico' ha).symm.trans (Ioo_ae_eq_Ioc' hb)

Depends on / 依赖: Ioo_ae_eq_Ico, Ioo_ae_eq_Ioc, symm.trans
-/
theorem Ico_ae_eq_Ioc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Ioc a b :=
  (Ioo_ae_eq_Ico' ha).symm.trans (Ioo_ae_eq_Ioc' hb)

end Intervals

end

end MeasureTheory

end

set_option linter.style.longFile 1700
