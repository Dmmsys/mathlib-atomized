/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Locally integrable functions

A function is called *locally integrable* (`MeasureTheory.LocallyIntegrable`) if it is integrable
on a neighborhood of every point. More generally, it is *locally integrable on `s`* if it is
locally integrable on a neighbourhood within `s` of any point of `s`.

This file contains properties of locally integrable functions, and integrability results
on compact sets.

## Main statements

* `Continuous.locallyIntegrable`: A continuous function is locally integrable.
* `ContinuousOn.locallyIntegrableOn`: A function which is continuous on `s` is locally
  integrable on `s`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Bornology Filter

open scoped Topology Interval ENNReal

variable {X Y ε ε' ε'' E F R : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable [MeasurableSpace Y] [TopologicalSpace Y]
variable [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']
  [NormedAddCommGroup E] [NormedAddCommGroup F] {f g : X -> ε} {μ ν : Measure X} {s : Set X}

namespace MeasureTheory

section LocallyIntegrableOn

/--
Definition of `LocallyIntegrableOn` / `LocallyIntegrableOn` 的定义

English:
definition LocallyIntegrableOn
  signature: (f : X -> ε) (s : Set X) (μ : Measure X := by volume_tac)
  body: forall x : X, x in s -> IntegrableAtFilter f (𝓝[s] x) μ

@[gcongr]

中文:
定义 LocallyIntegrableOn
  签名: (f : X -> ε) (s : Set X) (μ : Measure X := by volume_tac)
  定义体: forall x : X, x in s -> IntegrableAtFilter f (𝓝[s] x) μ

@[gcongr]

Depends on / 依赖: IntegrableAtFilter, volume_tac
-/
def LocallyIntegrableOn (f : X -> ε) (s : Set X) (μ : Measure X := by volume_tac) : Prop :=
  forall x : X, x in s -> IntegrableAtFilter f (𝓝[s] x) μ

@[gcongr]
/--
theorem `LocallyIntegrableOn.mono_set` / 定理 `LocallyIntegrableOn.mono_set`

English:
theorem LocallyIntegrableOn.mono_set
  statement: (hf : LocallyIntegrableOn f s μ) {t : Set X}
  proof: fun x hx =>
  (hf x <| hst hx).filter_mono (nhdsWithin_mono x hst)

中文:
定理 LocallyIntegrableOn.mono_set
  结论: (hf : Locally整数egrableOn f s μ) {t : Set X}
  证明: fun x hx =>
  (hf x <| hst hx).filter_mono (nhdsWithin_mono x hst)
-/
theorem LocallyIntegrableOn.mono_set (hf : LocallyIntegrableOn f s μ) {t : Set X}
    (hst : t subseteq s) : LocallyIntegrableOn f t μ := fun x hx =>
  (hf x <| hst hx).filter_mono (nhdsWithin_mono x hst)

/--
theorem `LocallyIntegrableOn.enorm` / 定理 `LocallyIntegrableOn.enorm`

English:
theorem LocallyIntegrableOn.enorm
  given: (hf : LocallyIntegrableOn f s μ)
  proof: fun t ht =>
  let ⟨U, hU_nhd, hU_int⟩ := hf t ht
  ⟨U, hU_nhd, hU_int.enorm⟩

中文:
定理 LocallyIntegrableOn.enorm
  条件: (hf : Locally整数egrableOn f s μ)
  证明: fun t ht =>
  let ⟨U, hU_nhd, hU_int⟩ := hf t ht
  ⟨U, hU_nhd, hU_int.enorm⟩
-/
theorem LocallyIntegrableOn.enorm (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (‖f ·‖ₑ) s μ := fun t ht =>
  let ⟨U, hU_nhd, hU_int⟩ := hf t ht
  ⟨U, hU_nhd, hU_int.enorm⟩

/--
theorem `LocallyIntegrableOn.norm` / 定理 `LocallyIntegrableOn.norm`

English:
theorem LocallyIntegrableOn.norm
  given: {f : X -> E} (hf : LocallyIntegrableOn f s μ)
  proof: fun t ht =>
  let ⟨U, hU_nhd, hU_int⟩ := hf t ht
  ⟨U, hU_nhd, hU_int.norm⟩

中文:
定理 LocallyIntegrableOn.norm
  条件: {f : X -> E} (hf : Locally整数egrableOn f s μ)
  证明: fun t ht =>
  let ⟨U, hU_nhd, hU_int⟩ := hf t ht
  ⟨U, hU_nhd, hU_int.norm⟩
-/
theorem LocallyIntegrableOn.norm {f : X -> E} (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (fun x => ‖f x‖) s μ := fun t ht =>
  let ⟨U, hU_nhd, hU_int⟩ := hf t ht
  ⟨U, hU_nhd, hU_int.norm⟩

/--
theorem `LocallyIntegrableOn.mono_enorm` / 定理 `LocallyIntegrableOn.mono_enorm`

English:
theorem LocallyIntegrableOn.mono_enorm
  statement: (hf : LocallyIntegrableOn f s μ) {g : X -> ε'}
  proof: by
  intro x hx
  rcases hf x hx with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, ht.mono_enorm hg.restrict (ae_restrict_of_ae h)⟩

中文:
定理 LocallyIntegrableOn.mono_enorm
  结论: (hf : Locally整数egrableOn f s μ) {g : X -> ε'}
  证明: by
  intro x hx
  rcases hf x hx with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, ht.mono_enorm hg.restrict (ae_restrict_of_ae h)⟩

Depends on / 依赖: ae_restrict_of_ae, hg.restrict, ht.mono_enorm, mono_enorm, restrict, t_mem
-/
theorem LocallyIntegrableOn.mono_enorm (hf : LocallyIntegrableOn f s μ) {g : X -> ε'}
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ x ∂μ, ‖g x‖ₑ <= ‖f x‖ₑ) :
    LocallyIntegrableOn g s μ := by
  intro x hx
  rcases hf x hx with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, ht.mono_enorm hg.restrict (ae_restrict_of_ae h)⟩

/--
theorem `LocallyIntegrableOn.mono` / 定理 `LocallyIntegrableOn.mono`

English:
theorem LocallyIntegrableOn.mono
  statement: {f : X -> E} (hf : LocallyIntegrableOn f s μ) {g : X -> F}
  proof: by
  intro x hx
  rcases hf x hx with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, Integrable.mono ht hg.restrict (ae_restrict_of_ae h)⟩

中文:
定理 LocallyIntegrableOn.mono
  结论: {f : X -> E} (hf : Locally整数egrableOn f s μ) {g : X -> F}
  证明: by
  intro x hx
  rcases hf x hx with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, Integrable.mono ht hg.restrict (ae_restrict_of_ae h)⟩

Depends on / 依赖: Integrable, Integrable.mono, ae_restrict_of_ae, hg.restrict, restrict, t_mem
-/
theorem LocallyIntegrableOn.mono {f : X -> E} (hf : LocallyIntegrableOn f s μ) {g : X -> F}
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ x ∂μ, ‖g x‖ <= ‖f x‖) :
    LocallyIntegrableOn g s μ := by
  intro x hx
  rcases hf x hx with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, Integrable.mono ht hg.restrict (ae_restrict_of_ae h)⟩

/--
lemma `LocallyIntegrableOn.mono_measure'` / 引理 `LocallyIntegrableOn.mono_measure'`

English:
lemma LocallyIntegrableOn.mono_measure'
  statement: [OpensMeasurableSpace X] (hf : LocallyIntegrableOn f s μ)
  proof: by
  intro x hx
  obtain ⟨t, ht, hf⟩ := hf x hx
  obtain ⟨u, hu, hxu, hut⟩ := mem_nhdsWithin.mp ht
  refine ⟨u inter s, inter_mem (mem_nhdsWithin.mpr ⟨u, hu, hxu, inter_subset_left⟩) self_mem_nhdsWithin,
    ?_⟩
.mono_measure' ?_ refine hf.mono_set hut
  simp_rw [← restrict_restrict hu.measurableSet

中文:
引理 LocallyIntegrableOn.mono_measure'
  结论: [OpensMeasurableSpace X] (hf : Locally整数egrableOn f s μ)
  证明: by
  intro x hx
  obtain ⟨t, ht, hf⟩ := hf x hx
  obtain ⟨u, hu, hxu, hut⟩ := mem_nhdsWithin.mp ht
  refine ⟨u inter s, inter_mem (mem_nhdsWithin.mpr ⟨u, hu, hxu, inter_subset_left⟩) self_mem_nhdsWithin,
    ?_⟩
.mono_measure' ?_ refine hf.mono_set hut
  simp_rw [← restrict_restrict hu.measurableSet

Depends on / 依赖: hf.mono_set, hu.measurableSet, inter_mem, inter_subset_left, measurableSet, mem_nhdsWithin, mem_nhdsWithin.mp, mem_nhdsWithin.mpr, mono_measure, mono_set, restrict_restrict, self_mem_nhdsWithin, simp_rw
-/
lemma LocallyIntegrableOn.mono_measure' [OpensMeasurableSpace X] (hf : LocallyIntegrableOn f s μ)
    (h : ν.restrict s <= μ.restrict s) : LocallyIntegrableOn f s ν := by
  intro x hx
  obtain ⟨t, ht, hf⟩ := hf x hx
  obtain ⟨u, hu, hxu, hut⟩ := mem_nhdsWithin.mp ht
  refine ⟨u inter s, inter_mem (mem_nhdsWithin.mpr ⟨u, hu, hxu, inter_subset_left⟩) self_mem_nhdsWithin,
    ?_⟩
.mono_measure' ?_ refine hf.mono_set hut
  simp_rw [← restrict_restrict hu.measurableSet]
  gcongr

@[gcongr]
/--
lemma `LocallyIntegrableOn.mono_measure` / 引理 `LocallyIntegrableOn.mono_measure`

English:
lemma LocallyIntegrableOn.mono_measure
  given: (hf : LocallyIntegrableOn f s μ) (h : ν <= μ)
  proof: fun x hx => (hf x hx).mono_measure h

@[gcongr]

中文:
引理 LocallyIntegrableOn.mono_measure
  条件: (hf : Locally整数egrableOn f s μ) (h : ν <= μ)
  证明: fun x hx => (hf x hx).mono_measure h

@[gcongr]

Depends on / 依赖: mono_measure
-/
lemma LocallyIntegrableOn.mono_measure (hf : LocallyIntegrableOn f s μ) (h : ν <= μ) :
    LocallyIntegrableOn f s ν :=
  fun x hx => (hf x hx).mono_measure h

@[gcongr]
/--
lemma `LocallyIntegrableOn.congr` / 引理 `LocallyIntegrableOn.congr`

English:
lemma LocallyIntegrableOn.congr
  given: (h : f =ᵐ[μ.restrict s] g) (hf : LocallyIntegrableOn f s μ)
  proof: by
  intro x hx
  obtain ⟨t, hxt, hft⟩ := hf x hx
  refine ⟨s inter t, inter_mem self_mem_nhdsWithin hxt, ?_⟩
  refine (hft.mono_set inter_subset_right).congr ?_
  refine h.filter_mono ?_
  gcongr
  exact inter_subset_left

中文:
引理 LocallyIntegrableOn.congr
  条件: (h : f =ᵐ[μ.restrict s] g) (hf : Locally整数egrableOn f s μ)
  证明: by
  intro x hx
  obtain ⟨t, hxt, hft⟩ := hf x hx
  refine ⟨s inter t, inter_mem self_mem_nhdsWithin hxt, ?_⟩
  refine (hft.mono_set inter_subset_right).congr ?_
  refine h.filter_mono ?_
  gcongr
  exact inter_subset_left

Depends on / 依赖: filter_mono, h.filter_mono, hft.mono_set, inter_mem, inter_subset_left, inter_subset_right, mono_set, self_mem_nhdsWithin
-/
lemma LocallyIntegrableOn.congr (h : f =ᵐ[μ.restrict s] g) (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn g s μ := by
  intro x hx
  obtain ⟨t, hxt, hft⟩ := hf x hx
  refine ⟨s inter t, inter_mem self_mem_nhdsWithin hxt, ?_⟩
  refine (hft.mono_set inter_subset_right).congr ?_
  refine h.filter_mono ?_
  gcongr
  exact inter_subset_left

/--
lemma `locallyIntegrableOn_congr` / 引理 `locallyIntegrableOn_congr`

English:
lemma locallyIntegrableOn_congr
  given: (h : f =ᵐ[μ.restrict s] g)
  proof: ⟨(·.congr h), (·.congr h.symm)⟩

中文:
引理 locallyIntegrableOn_congr
  条件: (h : f =ᵐ[μ.restrict s] g)
  证明: ⟨(·.congr h), (·.congr h.symm)⟩

Depends on / 依赖: h.symm
-/
lemma locallyIntegrableOn_congr (h : f =ᵐ[μ.restrict s] g) :
    LocallyIntegrableOn f s μ ↔ LocallyIntegrableOn g s μ :=
  ⟨(·.congr h), (·.congr h.symm)⟩

/--
theorem `IntegrableOn.locallyIntegrableOn` / 定理 `IntegrableOn.locallyIntegrableOn`

English:
theorem IntegrableOn.locallyIntegrableOn
  given: (hf : IntegrableOn f s μ)
  statement: LocallyIntegrableOn f s μ
  proof: fun _ _ => ⟨s, self_mem_nhdsWithin, hf⟩

中文:
定理 IntegrableOn.locallyIntegrableOn
  条件: (hf : 整数egrableOn f s μ)
  结论: Locally整数egrableOn f s μ
  证明: fun _ _ => ⟨s, self_mem_nhdsWithin, hf⟩

Depends on / 依赖: self_mem_nhdsWithin
-/
theorem IntegrableOn.locallyIntegrableOn (hf : IntegrableOn f s μ) : LocallyIntegrableOn f s μ :=
  fun _ _ => ⟨s, self_mem_nhdsWithin, hf⟩

/--
theorem `LocallyIntegrableOn.integrableOn_isCompact` / 定理 `LocallyIntegrableOn.integrableOn_isCompact`

English:
theorem LocallyIntegrableOn.integrableOn_isCompact
  statement: [PseudoMetrizableSpace ε]
  proof: IsCompact.induction_on hs integrableOn_empty (fun _u _v huv hv => hv.mono_set huv)
    (fun _u _v hu hv => integrableOn_union.mpr ⟨hu, hv⟩) hf

中文:
定理 LocallyIntegrableOn.integrableOn_isCompact
  结论: [PseudoMetrizableSpace ε]
  证明: IsCompact.induction_on hs integrableOn_empty (fun _u _v huv hv => hv.mono_set huv)
    (fun _u _v hu hv => integrableOn_union.mpr ⟨hu, hv⟩) hf

Depends on / 依赖: IsCompact, IsCompact.induction_on, hv.mono_set, induction_on, integrableOn_empty, integrableOn_union, integrableOn_union.mpr, mono_set
-/
theorem LocallyIntegrableOn.integrableOn_isCompact [PseudoMetrizableSpace ε]
    (hf : LocallyIntegrableOn f s μ) (hs : IsCompact s) : IntegrableOn f s μ :=
  IsCompact.induction_on hs integrableOn_empty (fun _u _v huv hv => hv.mono_set huv)
    (fun _u _v hu hv => integrableOn_union.mpr ⟨hu, hv⟩) hf

/--
theorem `LocallyIntegrableOn.integrableOn_compact_subset` / 定理 `LocallyIntegrableOn.integrableOn_compact_subset`

English:
theorem LocallyIntegrableOn.integrableOn_compact_subset
  statement: [PseudoMetrizableSpace ε]
  proof: (hf.mono_set hst).integrableOn_isCompact ht

中文:
定理 LocallyIntegrableOn.integrableOn_compact_subset
  结论: [PseudoMetrizableSpace ε]
  证明: (hf.mono_set hst).integrableOn_isCompact ht

Depends on / 依赖: hf.mono_set, integrableOn_isCompact, mono_set
-/
theorem LocallyIntegrableOn.integrableOn_compact_subset [PseudoMetrizableSpace ε]
    (hf : LocallyIntegrableOn f s μ) {t : Set X} (hst : t subseteq s) (ht : IsCompact t) :
    IntegrableOn f t μ :=
  (hf.mono_set hst).integrableOn_isCompact ht

/--
theorem `LocallyIntegrableOn.exists_countable_integrableOn` / 定理 `LocallyIntegrableOn.exists_countable_integrableOn`

English:
theorem LocallyIntegrableOn.exists_countable_integrableOn
  statement: [SecondCountableTopology X]
  proof: by
  have : forall x : s, exists u, IsOpen u ∧ x.1 in u ∧ IntegrableOn f (u inter s) μ := by
    rintro ⟨x, hx⟩
    rcases hf x hx with ⟨t, ht, h't⟩
    rcases mem_nhdsWithin.1 ht with ⟨u, u_open, x_mem, u_sub⟩
    exact ⟨u, u_open, x_mem, h't.mono_set u_sub⟩
  choose u u_open xu hu using this
  obt

中文:
定理 LocallyIntegrableOn.exists_countable_integrableOn
  结论: [SecondCountableTopology X]
  证明: by
  have : forall x : s, exists u, IsOpen u ∧ x.1 in u ∧ IntegrableOn f (u inter s) μ := by
    rintro ⟨x, hx⟩
    rcases hf x hx with ⟨t, ht, h't⟩
    rcases mem_nhdsWithin.1 ht with ⟨u, u_open, x_mem, u_sub⟩
    exact ⟨u, u_open, x_mem, h't.mono_set u_sub⟩
  choose u u_open xu hu using this
  obt

Depends on / 依赖: Countable, IntegrableOn, IsOpen, T.Countable, T_count, hT_count, hT_un, isOpen_iUnion_counta, mem_iUnion_of_mem, mem_nhdsWithin, mono_set, subseteq, t.mono_set, u_open, u_sub, x_mem
-/
theorem LocallyIntegrableOn.exists_countable_integrableOn [SecondCountableTopology X]
    (hf : LocallyIntegrableOn f s μ) : exists T : Set (Set X), T.Countable ∧
    (forall u in T, IsOpen u) ∧ (s subseteq ⋃ u in T, u) ∧ (forall u in T, IntegrableOn f (u inter s) μ) := by
  have : forall x : s, exists u, IsOpen u ∧ x.1 in u ∧ IntegrableOn f (u inter s) μ := by
    rintro ⟨x, hx⟩
    rcases hf x hx with ⟨t, ht, h't⟩
    rcases mem_nhdsWithin.1 ht with ⟨u, u_open, x_mem, u_sub⟩
    exact ⟨u, u_open, x_mem, h't.mono_set u_sub⟩
  choose u u_open xu hu using this
  obtain ⟨T, T_count, hT⟩ : exists T : Set s, T.Countable ∧ s subseteq ⋃ i in T, u i := by
    have : s subseteq ⋃ x : s, u x := fun y hy => mem_iUnion_of_mem ⟨y, hy⟩ (xu ⟨y, hy⟩)
    obtain ⟨T, hT_count, hT_un⟩ := isOpen_iUnion_countable u u_open
    exact ⟨T, hT_count, by rwa [hT_un]⟩
  refine ⟨u '' T, T_count.image _, ?_, by rwa [biUnion_image], ?_⟩
  · rintro v ⟨w, -, rfl⟩
    exact u_open _
  · rintro v ⟨w, -, rfl⟩
    exact hu _

/--
theorem `LocallyIntegrableOn.exists_nat_integrableOn` / 定理 `LocallyIntegrableOn.exists_nat_integrableOn`

English:
theorem LocallyIntegrableOn.exists_nat_integrableOn
  statement: [SecondCountableTopology X]
  proof: by
  rcases hf.exists_countable_integrableOn with ⟨T, T_count, T_open, sT, hT⟩
  let T' : Set (Set X) := insert ∅ T
  have T'_count : T'.Countable := Countable.insert ∅ T_count
  have T'_ne : T'.Nonempty := by simp only [T', insert_nonempty]
  rcases T'_count.exists_eq_range T'_ne with ⟨u, hu⟩
  ref

中文:
定理 LocallyIntegrableOn.exists_nat_integrableOn
  结论: [SecondCountableTopology X]
  证明: by
  rcases hf.exists_countable_integrableOn with ⟨T, T_count, T_open, sT, hT⟩
  let T' : Set (Set X) := insert ∅ T
  have T'_count : T'.Countable := Countable.insert ∅ T_count
  have T'_ne : T'.Nonempty := by simp only [T', insert_nonempty]
  rcases T'_count.exists_eq_range T'_ne with ⟨u, hu⟩
  ref

Depends on / 依赖: Countable, Countable.insert, Nonempty, T_count, T_open, _count, _count.exists_eq_range, exists_countable_integrableOn, exists_eq_range, hf.exists_countable_integrableOn, insert, insert_nonempty, isOpen_empty, mem_insert_iff, mem_range_self
-/
theorem LocallyIntegrableOn.exists_nat_integrableOn [SecondCountableTopology X]
    (hf : LocallyIntegrableOn f s μ) : exists u : Nat -> Set X,
    (forall n, IsOpen (u n)) ∧ (s subseteq ⋃ n, u n) ∧ (forall n, IntegrableOn f (u n inter s) μ) := by
  rcases hf.exists_countable_integrableOn with ⟨T, T_count, T_open, sT, hT⟩
  let T' : Set (Set X) := insert ∅ T
  have T'_count : T'.Countable := Countable.insert ∅ T_count
  have T'_ne : T'.Nonempty := by simp only [T', insert_nonempty]
  rcases T'_count.exists_eq_range T'_ne with ⟨u, hu⟩
  refine ⟨u, ?_, ?_, ?_⟩
  · intro n
    have : u n in T' := by rw [hu]; exact mem_range_self n
    rcases mem_insert_iff.1 this with h | h
    · rw [h]
      exact isOpen_empty
    · exact T_open _ h
  · intro x hx
    obtain ⟨v, hv, h'v⟩ : exists v, v in T ∧ x in v := by simpa only [mem_iUnion, exists_prop] using sT hx
    have : v in range u := by rw [← hu]; exact subset_insert ∅ T hv
    obtain ⟨n, rfl⟩ : exists n, u n = v := by simpa only [mem_range] using this
    exact mem_iUnion_of_mem _ h'v
  · intro n
    have : u n in T' := by rw [hu]; exact mem_range_self n
    rcases mem_insert_iff.1 this with h | h
    · simp only [h, empty_inter, integrableOn_empty]
    · exact hT _ h

/--
theorem `LocallyIntegrableOn.aestronglyMeasurable` / 定理 `LocallyIntegrableOn.aestronglyMeasurable`

English:
theorem LocallyIntegrableOn.aestronglyMeasurable
  statement: [PseudoMetrizableSpace ε]
  proof: by
  rcases hf.exists_nat_integrableOn with ⟨u, -, su, hu⟩
  have : s = ⋃ n, u n inter s := by rw [← iUnion_inter]; exact (inter_eq_right.mpr su).symm
  rw [this]; rw [aestronglyMeasurable_iUnion_iff]
  exact fun i : Nat => (hu i).aestronglyMeasurable

中文:
定理 LocallyIntegrableOn.aestronglyMeasurable
  结论: [PseudoMetrizableSpace ε]
  证明: by
  rcases hf.exists_nat_integrableOn with ⟨u, -, su, hu⟩
  have : s = ⋃ n, u n inter s := by rw [← iUnion_inter]; exact (inter_eq_right.mpr su).symm
  rw [this]; rw [aestronglyMeasurable_iUnion_iff]
  exact fun i : Nat => (hu i).aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, aestronglyMeasurable_iUnion_iff, exists_nat_integrableOn, hf.exists_nat_integrableOn, iUnion_inter, inter_eq_right, inter_eq_right.mpr
-/
theorem LocallyIntegrableOn.aestronglyMeasurable [PseudoMetrizableSpace ε]
    [SecondCountableTopology X] (hf : LocallyIntegrableOn f s μ) :
    AEStronglyMeasurable f (μ.restrict s) := by
  rcases hf.exists_nat_integrableOn with ⟨u, -, su, hu⟩
  have : s = ⋃ n, u n inter s := by rw [← iUnion_inter]; exact (inter_eq_right.mpr su).symm
  rw [this]; rw [aestronglyMeasurable_iUnion_iff]
  exact fun i : Nat => (hu i).aestronglyMeasurable

/--
theorem `locallyIntegrableOn_iff` / 定理 `locallyIntegrableOn_iff`

English:
theorem locallyIntegrableOn_iff
  statement: [PseudoMetrizableSpace ε]
  proof: by
  refine ⟨fun hf k hk => hf.integrableOn_compact_subset hk, fun hf x hx => ?_⟩
  rcases hs with ⟨U, Z, hU, hZ, rfl⟩
  rcases exists_compact_subset hU hx.1 with ⟨K, hK, hxK, hKU⟩
  rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds <| hU.mem_nhds hx.1)]
  refine ⟨Z inter K, inter_mem_nhdsWithin _ (me

中文:
定理 locallyIntegrableOn_iff
  结论: [PseudoMetrizableSpace ε]
  证明: by
  refine ⟨fun hf k hk => hf.integrableOn_compact_subset hk, fun hf x hx => ?_⟩
  rcases hs with ⟨U, Z, hU, hZ, rfl⟩
  rcases exists_compact_subset hU hx.1 with ⟨K, hK, hxK, hKU⟩
  rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds <| hU.mem_nhds hx.1)]
  refine ⟨Z inter K, inter_mem_nhdsWithin _ (me

Depends on / 依赖: exists_compact_subset, hU.mem_nhds, hf.integrableOn_compact_subset, integrableOn_compact_subset, inter_left, inter_mem_nhdsWithin, mem_interior_iff_mem_nhds, mem_nhds, nhdsWithin_inter_of_mem, nhdsWithin_le_nhds
-/
theorem locallyIntegrableOn_iff [PseudoMetrizableSpace ε]
    [LocallyCompactSpace X] (hs : IsLocallyClosed s) :
    LocallyIntegrableOn f s μ ↔ forall (k : Set X), k subseteq s -> IsCompact k -> IntegrableOn f k μ := by
  refine ⟨fun hf k hk => hf.integrableOn_compact_subset hk, fun hf x hx => ?_⟩
  rcases hs with ⟨U, Z, hU, hZ, rfl⟩
  rcases exists_compact_subset hU hx.1 with ⟨K, hK, hxK, hKU⟩
  rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds <| hU.mem_nhds hx.1)]
  refine ⟨Z inter K, inter_mem_nhdsWithin _ (mem_interior_iff_mem_nhds.1 hxK), ?_⟩
  exact hf (Z inter K) (fun y hy => ⟨hKU hy.2, hy.1⟩) (.inter_left hK hZ)

/--
theorem `_root_.ContinuousLinearMap.locallyIntegrableOn_comp` / 定理 `_root_.ContinuousLinearMap.locallyIntegrableOn_comp`

English:
theorem _root_.ContinuousLinearMap.locallyIntegrableOn_comp
  statement: {E H 𝕜 𝕜' : Type*}
  proof: (L.integrableAtFilter_comp <| hf · ·)

中文:
定理 _root_.ContinuousLinearMap.locallyIntegrableOn_comp
  结论: {E H 𝕜 𝕜' : 类型}
  证明: (L.integrableAtFilter_comp <| hf · ·)

Depends on / 依赖: L.integrableAtFilter_comp, integrableAtFilter_comp
-/
theorem _root_.ContinuousLinearMap.locallyIntegrableOn_comp {E H 𝕜 𝕜' : Type*}
    [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
    [NormedAddCommGroup E] [NormedSpace 𝕜' E] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {σ : 𝕜 ->+* 𝕜'} [RingHomIsometric σ] {f : X -> H} (L : H ->SL[σ] E)
    (hf : LocallyIntegrableOn f s μ) : LocallyIntegrableOn (L ∘ f) s μ :=
  (L.integrableAtFilter_comp <| hf · ·)

/--
theorem `LocallyIntegrableOn.add` / 定理 `LocallyIntegrableOn.add`

English:
theorem LocallyIntegrableOn.add
  statement: [ContinuousAdd ε''] {f g : X -> ε''}
  proof: fun x hx => (hf x hx).add (hg x hx)

中文:
定理 LocallyIntegrableOn.add
  结论: [ContinuousAdd ε''] {f g : X -> ε''}
  证明: fun x hx => (hf x hx).add (hg x hx)

Depends on / 依赖: Ring.ne_bot_of_isMaximal_of_not_isField, RingOfIntegers, RingOfIntegers.not_isField, ne_bot_of_isMaximal_of_not_isField, not_isField
-/
protected theorem LocallyIntegrableOn.add [ContinuousAdd ε''] {f g : X -> ε''}
    (hf : LocallyIntegrableOn f s μ) (hg : LocallyIntegrableOn g s μ) :
    LocallyIntegrableOn (f + g) s μ := fun x hx => (hf x hx).add (hg x hx)

-- TODO: once mathlib has an ENormedAddCommSubMonoid, generalise this lemma also
/--
theorem `LocallyIntegrableOn.sub` / 定理 `LocallyIntegrableOn.sub`

English:
theorem LocallyIntegrableOn.sub
  proof: fun x hx => (hf x hx).sub (hg x hx)

中文:
定理 LocallyIntegrableOn.sub
  证明: fun x hx => (hf x hx).sub (hg x hx)
-/
protected theorem LocallyIntegrableOn.sub
    {f g : X -> E} (hf : LocallyIntegrableOn f s μ) (hg : LocallyIntegrableOn g s μ) :
    LocallyIntegrableOn (f - g) s μ := fun x hx => (hf x hx).sub (hg x hx)

/--
theorem `LocallyIntegrableOn.neg` / 定理 `LocallyIntegrableOn.neg`

English:
theorem LocallyIntegrableOn.neg
  given: {f : X -> E} (hf : LocallyIntegrableOn f s μ)
  proof: fun x hx => (hf x hx).neg

中文:
定理 LocallyIntegrableOn.neg
  条件: {f : X -> E} (hf : Locally整数egrableOn f s μ)
  证明: fun x hx => (hf x hx).neg
-/
protected theorem LocallyIntegrableOn.neg {f : X -> E} (hf : LocallyIntegrableOn f s μ) :
    LocallyIntegrableOn (-f) s μ := fun x hx => (hf x hx).neg

/--
theorem `locallyIntegrableOn_neg_iff` / 定理 `locallyIntegrableOn_neg_iff`

English:
theorem locallyIntegrableOn_neg_iff
  given: {f : X -> E}
  proof: by
  unfold LocallyIntegrableOn
  simp_rw [MeasureTheory.integrableAtFilter_neg_iff]

中文:
定理 locallyIntegrableOn_neg_iff
  条件: {f : X -> E}
  证明: by
  unfold LocallyIntegrableOn
  simp_rw [MeasureTheory.integrableAtFilter_neg_iff]
-/
@[simp] theorem locallyIntegrableOn_neg_iff {f : X -> E} :
    LocallyIntegrableOn (-f) s μ ↔ LocallyIntegrableOn f s μ := by
  unfold LocallyIntegrableOn
  simp_rw [MeasureTheory.integrableAtFilter_neg_iff]

-- TODO: generalise this to ENormed spaces, once there are suitable typeclasses
/--
theorem `LocallyIntegrableOn.smul` / 定理 `LocallyIntegrableOn.smul`

English:
theorem LocallyIntegrableOn.smul
  statement: {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
  proof: fun x hx => (hf x hx).smul c

中文:
定理 LocallyIntegrableOn.smul
  结论: {𝕜 : 类型} [NormedField 𝕜] [NormedSpace 𝕜 E]
  证明: fun x hx => (hf x hx).smul c
-/
protected theorem LocallyIntegrableOn.smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : X -> E} (hf : LocallyIntegrableOn f s μ) (c : 𝕜) :
  LocallyIntegrableOn (c • f) s μ := fun x hx => (hf x hx).smul c

-- TODO: generalise this to ENormed spaces, once there are suitable typeclasses
/--
theorem `locallyIntegrableOn_smul_iff` / 定理 `locallyIntegrableOn_smul_iff`

English:
theorem locallyIntegrableOn_smul_iff
  statement: {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
  proof: by
  unfold LocallyIntegrableOn
  grind [integrableAtFilter_smul_iff]

中文:
定理 locallyIntegrableOn_smul_iff
  结论: {𝕜 : 类型} [NormedField 𝕜] [NormedSpace 𝕜 E]
  证明: by
  unfold LocallyIntegrableOn
  grind [integrableAtFilter_smul_iff]
-/
@[simp] theorem locallyIntegrableOn_smul_iff {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : X -> E} (c : 𝕜) :
    LocallyIntegrableOn (c • f) s μ ↔ c = 0 ∨ LocallyIntegrableOn f s μ := by
  unfold LocallyIntegrableOn
  grind [integrableAtFilter_smul_iff]

end LocallyIntegrableOn

/--
Definition of `LocallyIntegrable` / `LocallyIntegrable` 的定义

English:
definition LocallyIntegrable
  signature: (f : X -> ε) (μ : Measure X := by volume_tac)
  body: forall x : X, IntegrableAtFilter f (𝓝 x) μ

中文:
定义 LocallyIntegrable
  签名: (f : X -> ε) (μ : Measure X := by volume_tac)
  定义体: forall x : X, IntegrableAtFilter f (𝓝 x) μ

Depends on / 依赖: IntegrableAtFilter, volume_tac
-/
def LocallyIntegrable (f : X -> ε) (μ : Measure X := by volume_tac) : Prop :=
  forall x : X, IntegrableAtFilter f (𝓝 x) μ

/--
theorem `locallyIntegrable_comap` / 定理 `locallyIntegrable_comap`

English:
theorem locallyIntegrable_comap
  given: (hs : MeasurableSet s)
  proof: by
  simp_rw [LocallyIntegrableOn, Subtype.forall', ← map_nhds_subtype_val]
  exact forall_congr' fun _ => (MeasurableEmbedding.subtype_coe hs).integrableAtFilter_iff_comap.symm

中文:
定理 locallyIntegrable_comap
  条件: (hs : MeasurableSet s)
  证明: by
  simp_rw [LocallyIntegrableOn, Subtype.forall', ← map_nhds_subtype_val]
  exact forall_congr' fun _ => (MeasurableEmbedding.subtype_coe hs).integrableAtFilter_iff_comap.symm

Depends on / 依赖: LocallyIntegrableOn, MeasurableEmbedding, MeasurableEmbedding.subtype_coe, Subtype, Subtype.forall, forall_congr, integrableAtFilter_iff_comap, integrableAtFilter_iff_comap.symm, map_nhds_subtype_val, simp_rw, subtype_coe
-/
theorem locallyIntegrable_comap (hs : MeasurableSet s) :
    LocallyIntegrable (fun x : s => f x) (μ.comap Subtype.val) ↔ LocallyIntegrableOn f s μ := by
  simp_rw [LocallyIntegrableOn, Subtype.forall', ← map_nhds_subtype_val]
  exact forall_congr' fun _ => (MeasurableEmbedding.subtype_coe hs).integrableAtFilter_iff_comap.symm

/--
theorem `locallyIntegrableOn_univ` / 定理 `locallyIntegrableOn_univ`

English:
theorem locallyIntegrableOn_univ
  statement: LocallyIntegrableOn f univ μ ↔ LocallyIntegrable f μ
  proof: by
  simp only [LocallyIntegrableOn, nhdsWithin_univ, mem_univ, true_imp_iff]; rfl

中文:
定理 locallyIntegrableOn_univ
  结论: Locally整数egrableOn f univ μ ↔ Locally整数egrable f μ
  证明: by
  simp only [LocallyIntegrableOn, nhdsWithin_univ, mem_univ, true_imp_iff]; rfl

Depends on / 依赖: LocallyIntegrableOn, mem_univ, nhdsWithin_univ, true_imp_iff
-/
theorem locallyIntegrableOn_univ : LocallyIntegrableOn f univ μ ↔ LocallyIntegrable f μ := by
  simp only [LocallyIntegrableOn, nhdsWithin_univ, mem_univ, true_imp_iff]; rfl

/--
theorem `LocallyIntegrable.locallyIntegrableOn` / 定理 `LocallyIntegrable.locallyIntegrableOn`

English:
theorem LocallyIntegrable.locallyIntegrableOn
  given: (hf : LocallyIntegrable f μ) (s : Set X)
  proof: fun x _ => (hf x).filter_mono nhdsWithin_le_nhds

中文:
定理 LocallyIntegrable.locallyIntegrableOn
  条件: (hf : Locally整数egrable f μ) (s : Set X)
  证明: fun x _ => (hf x).filter_mono nhdsWithin_le_nhds

Depends on / 依赖: filter_mono, nhdsWithin_le_nhds
-/
theorem LocallyIntegrable.locallyIntegrableOn (hf : LocallyIntegrable f μ) (s : Set X) :
    LocallyIntegrableOn f s μ := fun x _ => (hf x).filter_mono nhdsWithin_le_nhds

/--
theorem `Integrable.locallyIntegrable` / 定理 `Integrable.locallyIntegrable`

English:
theorem Integrable.locallyIntegrable
  given: (hf : Integrable f μ)
  statement: LocallyIntegrable f μ
  proof: fun _ =>
  hf.integrableAtFilter _

中文:
定理 Integrable.locallyIntegrable
  条件: (hf : 整数egrable f μ)
  结论: Locally整数egrable f μ
  证明: fun _ =>
  hf.integrableAtFilter _
-/
theorem Integrable.locallyIntegrable (hf : Integrable f μ) : LocallyIntegrable f μ := fun _ =>
  hf.integrableAtFilter _

/--
theorem `LocallyIntegrable.mono_enorm` / 定理 `LocallyIntegrable.mono_enorm`

English:
theorem LocallyIntegrable.mono_enorm
  statement: (hf : LocallyIntegrable f μ) {g : X -> ε'}
  proof: by
  rw [← locallyIntegrableOn_univ] at hf ⊢
  exact hf.mono_enorm hg h

中文:
定理 LocallyIntegrable.mono_enorm
  结论: (hf : Locally整数egrable f μ) {g : X -> ε'}
  证明: by
  rw [← locallyIntegrableOn_univ] at hf ⊢
  exact hf.mono_enorm hg h

Depends on / 依赖: hf.mono_enorm, locallyIntegrableOn_univ, mono_enorm
-/
theorem LocallyIntegrable.mono_enorm (hf : LocallyIntegrable f μ) {g : X -> ε'}
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ x ∂μ, ‖g x‖ₑ <= ‖f x‖ₑ) :
    LocallyIntegrable g μ := by
  rw [← locallyIntegrableOn_univ] at hf ⊢
  exact hf.mono_enorm hg h

/--
theorem `LocallyIntegrable.mono` / 定理 `LocallyIntegrable.mono`

English:
theorem LocallyIntegrable.mono
  statement: {f : X -> E} (hf : LocallyIntegrable f μ) {g : X -> F}
  proof: by
  rw [← locallyIntegrableOn_univ] at hf ⊢
  exact hf.mono hg h

@[gcongr]

中文:
定理 LocallyIntegrable.mono
  结论: {f : X -> E} (hf : Locally整数egrable f μ) {g : X -> F}
  证明: by
  rw [← locallyIntegrableOn_univ] at hf ⊢
  exact hf.mono hg h

@[gcongr]

Depends on / 依赖: hf.mono, locallyIntegrableOn_univ
-/
theorem LocallyIntegrable.mono {f : X -> E} (hf : LocallyIntegrable f μ) {g : X -> F}
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ x ∂μ, ‖g x‖ <= ‖f x‖) :
    LocallyIntegrable g μ := by
  rw [← locallyIntegrableOn_univ] at hf ⊢
  exact hf.mono hg h

@[gcongr]
/--
lemma `LocallyIntegrable.mono_measure` / 引理 `LocallyIntegrable.mono_measure`

English:
lemma LocallyIntegrable.mono_measure
  given: (hf : LocallyIntegrable f μ) (h : ν <= μ)
  proof: (hf · |>.mono_measure h)

@[gcongr]

中文:
引理 LocallyIntegrable.mono_measure
  条件: (hf : Locally整数egrable f μ) (h : ν <= μ)
  证明: (hf · |>.mono_measure h)

@[gcongr]

Depends on / 依赖: mono_measure
-/
lemma LocallyIntegrable.mono_measure (hf : LocallyIntegrable f μ) (h : ν <= μ) :
    LocallyIntegrable f ν :=
  (hf · |>.mono_measure h)

@[gcongr]
/--
lemma `LocallyIntegrable.congr` / 引理 `LocallyIntegrable.congr`

English:
lemma LocallyIntegrable.congr
  given: (hf : LocallyIntegrable f μ) (h : f =ᵐ[μ] g)
  proof: (hf · |>.congr h)

中文:
引理 LocallyIntegrable.congr
  条件: (hf : Locally整数egrable f μ) (h : f =ᵐ[μ] g)
  证明: (hf · |>.congr h)
-/
lemma LocallyIntegrable.congr (hf : LocallyIntegrable f μ) (h : f =ᵐ[μ] g) :
    LocallyIntegrable g μ :=
  (hf · |>.congr h)

/--
lemma `locallyIntegrable_congr` / 引理 `locallyIntegrable_congr`

English:
lemma locallyIntegrable_congr
  given: (h : f =ᵐ[μ] g)
  proof: ⟨(·.congr h), (·.congr h.symm)⟩

中文:
引理 locallyIntegrable_congr
  条件: (h : f =ᵐ[μ] g)
  证明: ⟨(·.congr h), (·.congr h.symm)⟩

Depends on / 依赖: h.symm
-/
lemma locallyIntegrable_congr (h : f =ᵐ[μ] g) :
    LocallyIntegrable f μ ↔ LocallyIntegrable g μ :=
  ⟨(·.congr h), (·.congr h.symm)⟩

/--
theorem `locallyIntegrableOn_of_locallyIntegrable_restrict` / 定理 `locallyIntegrableOn_of_locallyIntegrable_restrict`

English:
theorem locallyIntegrableOn_of_locallyIntegrable_restrict
  statement: [OpensMeasurableSpace X]
  proof: by
  intro x _
  obtain ⟨t, ht_mem, ht_int⟩ := hf x
  obtain ⟨u, hu_sub, hu_o, hu_mem⟩ := mem_nhds_iff.mp ht_mem
  refine ⟨_, inter_mem_nhdsWithin s (hu_o.mem_nhds hu_mem), ?_⟩
  simpa only [IntegrableOn, Measure.restrict_restrict hu_o.measurableSet, inter_comm] using
    ht_int.mono_set hu_sub

中文:
定理 locallyIntegrableOn_of_locallyIntegrable_restrict
  结论: [OpensMeasurableSpace X]
  证明: by
  intro x _
  obtain ⟨t, ht_mem, ht_int⟩ := hf x
  obtain ⟨u, hu_sub, hu_o, hu_mem⟩ := mem_nhds_iff.mp ht_mem
  refine ⟨_, inter_mem_nhdsWithin s (hu_o.mem_nhds hu_mem), ?_⟩
  simpa only [IntegrableOn, Measure.restrict_restrict hu_o.measurableSet, inter_comm] using
    ht_int.mono_set hu_sub

Depends on / 依赖: IntegrableOn, Measure, Measure.restrict_restrict, ht_int, ht_int.mono_set, ht_mem, hu_mem, hu_o, hu_o.measurableSet, hu_o.mem_nhds, hu_sub, inter_comm, inter_mem_nhdsWithin, measurableSet, mem_nhds, mem_nhds_iff, mem_nhds_iff.mp, mono_set, restrict_restrict
-/
theorem locallyIntegrableOn_of_locallyIntegrable_restrict [OpensMeasurableSpace X]
    (hf : LocallyIntegrable f (μ.restrict s)) : LocallyIntegrableOn f s μ := by
  intro x _
  obtain ⟨t, ht_mem, ht_int⟩ := hf x
  obtain ⟨u, hu_sub, hu_o, hu_mem⟩ := mem_nhds_iff.mp ht_mem
  refine ⟨_, inter_mem_nhdsWithin s (hu_o.mem_nhds hu_mem), ?_⟩
  simpa only [IntegrableOn, Measure.restrict_restrict hu_o.measurableSet, inter_comm] using
    ht_int.mono_set hu_sub

/--
theorem `locallyIntegrableOn_iff_locallyIntegrable_restrict` / 定理 `locallyIntegrableOn_iff_locallyIntegrable_restrict`

English:
theorem locallyIntegrableOn_iff_locallyIntegrable_restrict
  statement: [OpensMeasurableSpace X]
  proof: by
  refine ⟨fun hf x => ?_, locallyIntegrableOn_of_locallyIntegrable_restrict⟩
  by_cases h : x in s
  · obtain ⟨t, ht_nhds, ht_int⟩ := hf x h
    obtain ⟨u, hu_o, hu_x, hu_sub⟩ := mem_nhdsWithin.mp ht_nhds
    refine ⟨u, hu_o.mem_nhds hu_x, ?_⟩
    rw [IntegrableOn]; rw [restrict_restrict hu_o.mea

中文:
定理 locallyIntegrableOn_iff_locallyIntegrable_restrict
  结论: [OpensMeasurableSpace X]
  证明: by
  refine ⟨fun hf x => ?_, locallyIntegrableOn_of_locallyIntegrable_restrict⟩
  by_cases h : x in s
  · obtain ⟨t, ht_nhds, ht_int⟩ := hf x h
    obtain ⟨u, hu_o, hu_x, hu_sub⟩ := mem_nhdsWithin.mp ht_nhds
    refine ⟨u, hu_o.mem_nhds hu_x, ?_⟩
    rw [IntegrableOn]; rw [restrict_restrict hu_o.mea

Depends on / 依赖: IntegrableOn, exacts, hs.mem_nhds, ht_int, ht_int.mono_set, ht_nhds, hu_o, hu_o.measurableSet, hu_o.mem_nhds, hu_sub, hu_x, inter_comm, inter_compl_self, isOpen_compl_iff, locallyIntegrableOn_of_locallyIntegrable_restrict, measurableSet, mem_nhds, mem_nhdsWithin, mem_nhdsWithin.mp, mono_set
-/
theorem locallyIntegrableOn_iff_locallyIntegrable_restrict [OpensMeasurableSpace X]
    (hs : IsClosed s) : LocallyIntegrableOn f s μ ↔ LocallyIntegrable f (μ.restrict s) := by
  refine ⟨fun hf x => ?_, locallyIntegrableOn_of_locallyIntegrable_restrict⟩
  by_cases h : x in s
  · obtain ⟨t, ht_nhds, ht_int⟩ := hf x h
    obtain ⟨u, hu_o, hu_x, hu_sub⟩ := mem_nhdsWithin.mp ht_nhds
    refine ⟨u, hu_o.mem_nhds hu_x, ?_⟩
    rw [IntegrableOn]; rw [restrict_restrict hu_o.measurableSet]
    exact ht_int.mono_set hu_sub
  · rw [← isOpen_compl_iff] at hs
    refine ⟨sᶜ, hs.mem_nhds h, ?_⟩
    rw [IntegrableOn]; rw [restrict_restrict]; rw [inter_comm]; rw [inter_compl_self]; rw [← IntegrableOn]
    exacts [integrableOn_empty, hs.measurableSet]

/--
theorem `LocallyIntegrable.integrableOn_isCompact` / 定理 `LocallyIntegrable.integrableOn_isCompact`

English:
theorem LocallyIntegrable.integrableOn_isCompact
  statement: [PseudoMetrizableSpace ε]
  proof: (hf.locallyIntegrableOn k).integrableOn_isCompact hk

中文:
定理 LocallyIntegrable.integrableOn_isCompact
  结论: [PseudoMetrizableSpace ε]
  证明: (hf.locallyIntegrableOn k).integrableOn_isCompact hk

Depends on / 依赖: hf.locallyIntegrableOn, integrableOn_isCompact, locallyIntegrableOn
-/
theorem LocallyIntegrable.integrableOn_isCompact [PseudoMetrizableSpace ε]
    {k : Set X} (hf : LocallyIntegrable f μ) (hk : IsCompact k) : IntegrableOn f k μ :=
  (hf.locallyIntegrableOn k).integrableOn_isCompact hk

/--
theorem `LocallyIntegrable.integrableOn_nhds_isCompact` / 定理 `LocallyIntegrable.integrableOn_nhds_isCompact`

English:
theorem LocallyIntegrable.integrableOn_nhds_isCompact
  statement: [PseudoMetrizableSpace ε]
  proof: by
  refine IsCompact.induction_on hk ?_ ?_ ?_ ?_
  · refine ⟨∅, isOpen_empty, Subset.rfl, integrableOn_empty⟩
  · rintro s t hst ⟨u, u_open, tu, hu⟩
    exact ⟨u, u_open, hst.trans tu, hu⟩
  · rintro s t ⟨u, u_open, su, hu⟩ ⟨v, v_open, tv, hv⟩
    exact ⟨u union v, u_open.union v_open, union_subset

中文:
定理 LocallyIntegrable.integrableOn_nhds_isCompact
  结论: [PseudoMetrizableSpace ε]
  证明: by
  refine IsCompact.induction_on hk ?_ ?_ ?_ ?_
  · refine ⟨∅, isOpen_empty, Subset.rfl, integrableOn_empty⟩
  · rintro s t hst ⟨u, u_open, tu, hu⟩
    exact ⟨u, u_open, hst.trans tu, hu⟩
  · rintro s t ⟨u, u_open, su, hu⟩ ⟨v, v_open, tv, hv⟩
    exact ⟨u union v, u_open.union v_open, union_subset

Depends on / 依赖: IsCompact, IsCompact.induction_on, Subset, Subset.rfl, hst.trans, hu.mono_set, hu.union, induction_on, integrableOn_empty, isOpen_empty, mem_nhds, mem_nhds_iff, mono_set, nhdsWithin_le_nhds, u_open, u_open.union, union_subset_union, v_open, v_open.mem_nhds
-/
theorem LocallyIntegrable.integrableOn_nhds_isCompact [PseudoMetrizableSpace ε]
    (hf : LocallyIntegrable f μ) {k : Set X} (hk : IsCompact k) :
    exists u, IsOpen u ∧ k subseteq u ∧ IntegrableOn f u μ := by
  refine IsCompact.induction_on hk ?_ ?_ ?_ ?_
  · refine ⟨∅, isOpen_empty, Subset.rfl, integrableOn_empty⟩
  · rintro s t hst ⟨u, u_open, tu, hu⟩
    exact ⟨u, u_open, hst.trans tu, hu⟩
  · rintro s t ⟨u, u_open, su, hu⟩ ⟨v, v_open, tv, hv⟩
    exact ⟨u union v, u_open.union v_open, union_subset_union su tv, hu.union hv⟩
  · intro x _
    rcases hf x with ⟨u, ux, hu⟩
    rcases mem_nhds_iff.1 ux with ⟨v, vu, v_open, xv⟩
    exact ⟨v, nhdsWithin_le_nhds (v_open.mem_nhds xv), v, v_open, Subset.rfl, hu.mono_set vu⟩

/--
theorem `locallyIntegrable_iff` / 定理 `locallyIntegrable_iff`

English:
theorem locallyIntegrable_iff
  given: [PseudoMetrizableSpace ε] [LocallyCompactSpace X]
  proof: ⟨fun hf _k hk => hf.integrableOn_isCompact hk, fun hf x =>
    let ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x
    ⟨K, h2K, hf K hK⟩⟩

中文:
定理 locallyIntegrable_iff
  条件: [PseudoMetrizableSpace ε] [LocallyCompactSpace X]
  证明: ⟨fun hf _k hk => hf.integrableOn_isCompact hk, fun hf x =>
    let ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x
    ⟨K, h2K, hf K hK⟩⟩

Depends on / 依赖: exists_compact_mem_nhds, hf.integrableOn_isCompact, integrableOn_isCompact
-/
theorem locallyIntegrable_iff [PseudoMetrizableSpace ε] [LocallyCompactSpace X] :
    LocallyIntegrable f μ ↔ forall k : Set X, IsCompact k -> IntegrableOn f k μ :=
  ⟨fun hf _k hk => hf.integrableOn_isCompact hk, fun hf x =>
    let ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x
    ⟨K, h2K, hf K hK⟩⟩

/--
theorem `LocallyIntegrable.aestronglyMeasurable` / 定理 `LocallyIntegrable.aestronglyMeasurable`

English:
theorem LocallyIntegrable.aestronglyMeasurable
  statement: [PseudoMetrizableSpace ε] [SecondCountableTopology X]
  proof: by
  simpa only [restrict_univ] using (locallyIntegrableOn_univ.mpr hf).aestronglyMeasurable

中文:
定理 LocallyIntegrable.aestronglyMeasurable
  结论: [PseudoMetrizableSpace ε] [SecondCountableTopology X]
  证明: by
  simpa only [restrict_univ] using (locallyIntegrableOn_univ.mpr hf).aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, locallyIntegrableOn_univ, locallyIntegrableOn_univ.mpr, restrict_univ
-/
theorem LocallyIntegrable.aestronglyMeasurable [PseudoMetrizableSpace ε] [SecondCountableTopology X]
    (hf : LocallyIntegrable f μ) : AEStronglyMeasurable f μ := by
  simpa only [restrict_univ] using (locallyIntegrableOn_univ.mpr hf).aestronglyMeasurable

/--
theorem `LocallyIntegrable.exists_nat_integrableOn` / 定理 `LocallyIntegrable.exists_nat_integrableOn`

English:
theorem LocallyIntegrable.exists_nat_integrableOn
  statement: [SecondCountableTopology X]
  proof: by
  rcases (hf.locallyIntegrableOn univ).exists_nat_integrableOn with ⟨u, u_open, u_union, hu⟩
  refine ⟨u, u_open, eq_univ_of_univ_subset u_union, fun n => ?_⟩
  simpa only [inter_univ] using hu n

中文:
定理 LocallyIntegrable.exists_nat_integrableOn
  结论: [SecondCountableTopology X]
  证明: by
  rcases (hf.locallyIntegrableOn univ).exists_nat_integrableOn with ⟨u, u_open, u_union, hu⟩
  refine ⟨u, u_open, eq_univ_of_univ_subset u_union, fun n => ?_⟩
  simpa only [inter_univ] using hu n

Depends on / 依赖: eq_univ_of_univ_subset, exists_nat_integrableOn, hf.locallyIntegrableOn, inter_univ, locallyIntegrableOn, u_open, u_union
-/
theorem LocallyIntegrable.exists_nat_integrableOn [SecondCountableTopology X]
    (hf : LocallyIntegrable f μ) : exists u : Nat -> Set X,
    (forall n, IsOpen (u n)) ∧ ((⋃ n, u n) = univ) ∧ (forall n, IntegrableOn f (u n) μ) := by
  rcases (hf.locallyIntegrableOn univ).exists_nat_integrableOn with ⟨u, u_open, u_union, hu⟩
  refine ⟨u, u_open, eq_univ_of_univ_subset u_union, fun n => ?_⟩
  simpa only [inter_univ] using hu n

/--
theorem `MemLp.locallyIntegrable` / 定理 `MemLp.locallyIntegrable`

English:
theorem MemLp.locallyIntegrable
  statement: [IsLocallyFiniteMeasure μ] {p : Real>=0∞}
  proof: by
  intro x
  rcases μ.finiteAt_nhds x with ⟨U, hU, h'U⟩
  have : Fact (μ U < ⊤) := ⟨h'U⟩
  refine ⟨U, hU, ?_⟩
  rw [IntegrableOn]; rw [← memLp_one_iff_integrable]
  apply (hf.restrict U).mono_exponent hp

中文:
定理 MemLp.locallyIntegrable
  结论: [IsLocallyFiniteMeasure μ] {p : 实数>=0∞}
  证明: by
  intro x
  rcases μ.finiteAt_nhds x with ⟨U, hU, h'U⟩
  have : Fact (μ U < ⊤) := ⟨h'U⟩
  refine ⟨U, hU, ?_⟩
  rw [IntegrableOn]; rw [← memLp_one_iff_integrable]
  apply (hf.restrict U).mono_exponent hp

Depends on / 依赖: IntegrableOn, finiteAt_nhds, hf.restrict, memLp_one_iff_integrable, mono_exponent, restrict
-/
theorem MemLp.locallyIntegrable [IsLocallyFiniteMeasure μ] {p : Real>=0∞}
    (hf : MemLp f p μ) (hp : 1 <= p) : LocallyIntegrable f μ := by
  intro x
  rcases μ.finiteAt_nhds x with ⟨U, hU, h'U⟩
  have : Fact (μ U < ⊤) := ⟨h'U⟩
  refine ⟨U, hU, ?_⟩
  rw [IntegrableOn]; rw [← memLp_one_iff_integrable]
  apply (hf.restrict U).mono_exponent hp

/--
theorem `locallyIntegrable_const_enorm` / 定理 `locallyIntegrable_const_enorm`

English:
theorem locallyIntegrable_const_enorm
  given: [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞)
  proof: (memLp_top_const_enorm hc).locallyIntegrable le_top

中文:
定理 locallyIntegrable_const_enorm
  条件: [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞)
  证明: (memLp_top_const_enorm hc).locallyIntegrable le_top

Depends on / 依赖: algebraMap, charZero_of_injective_algebraMap, injective, le_top, locallyIntegrable, memLp_top_const_enorm
-/
theorem locallyIntegrable_const_enorm [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞) :
    LocallyIntegrable (fun _ => c) μ :=
  (memLp_top_const_enorm hc).locallyIntegrable le_top

/--
theorem `locallyIntegrable_const` / 定理 `locallyIntegrable_const`

English:
theorem locallyIntegrable_const
  given: [IsLocallyFiniteMeasure μ] (c : E)
  proof: locallyIntegrable_const_enorm enorm_ne_top

中文:
定理 locallyIntegrable_const
  条件: [IsLocallyFiniteMeasure μ] (c : E)
  证明: locallyIntegrable_const_enorm enorm_ne_top

Depends on / 依赖: enorm_ne_top, locallyIntegrable_const_enorm
-/
theorem locallyIntegrable_const [IsLocallyFiniteMeasure μ] (c : E) :
    LocallyIntegrable (fun _ => c) μ :=
  locallyIntegrable_const_enorm enorm_ne_top

/--
theorem `locallyIntegrableOn_const_enorm` / 定理 `locallyIntegrableOn_const_enorm`

English:
theorem locallyIntegrableOn_const_enorm
  given: [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞)
  proof: (locallyIntegrable_const_enorm hc).locallyIntegrableOn s

中文:
定理 locallyIntegrableOn_const_enorm
  条件: [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞)
  证明: (locallyIntegrable_const_enorm hc).locallyIntegrableOn s

Depends on / 依赖: locallyIntegrableOn, locallyIntegrable_const_enorm
-/
theorem locallyIntegrableOn_const_enorm [IsLocallyFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞) :
    LocallyIntegrableOn (fun _ => c) s μ :=
  (locallyIntegrable_const_enorm hc).locallyIntegrableOn s

/--
theorem `locallyIntegrableOn_const` / 定理 `locallyIntegrableOn_const`

English:
theorem locallyIntegrableOn_const
  given: [IsLocallyFiniteMeasure μ] (c : E)
  proof: locallyIntegrableOn_const_enorm enorm_ne_top

中文:
定理 locallyIntegrableOn_const
  条件: [IsLocallyFiniteMeasure μ] (c : E)
  证明: locallyIntegrableOn_const_enorm enorm_ne_top

Depends on / 依赖: enorm_ne_top, locallyIntegrableOn_const_enorm
-/
theorem locallyIntegrableOn_const [IsLocallyFiniteMeasure μ] (c : E) :
    LocallyIntegrableOn (fun _ => c) s μ :=
  locallyIntegrableOn_const_enorm enorm_ne_top

/--
theorem `locallyIntegrable_zero` / 定理 `locallyIntegrable_zero`

English:
theorem locallyIntegrable_zero
  statement: LocallyIntegrable (fun _ => (0 : ε'')) μ
  proof: (integrable_zero X ε'' μ).locallyIntegrable

中文:
定理 locallyIntegrable_zero
  结论: Locally整数egrable (fun _ => (0 : ε'')) μ
  证明: (integrable_zero X ε'' μ).locallyIntegrable

Depends on / 依赖: integrable_zero, locallyIntegrable
-/
theorem locallyIntegrable_zero : LocallyIntegrable (fun _ => (0 : ε'')) μ :=
  (integrable_zero X ε'' μ).locallyIntegrable

/--
theorem `locallyIntegrableOn_zero` / 定理 `locallyIntegrableOn_zero`

English:
theorem locallyIntegrableOn_zero
  statement: LocallyIntegrableOn (fun _ => (0 : ε'')) s μ
  proof: locallyIntegrable_zero.locallyIntegrableOn s

中文:
定理 locallyIntegrableOn_zero
  结论: Locally整数egrableOn (fun _ => (0 : ε'')) s μ
  证明: locallyIntegrable_zero.locallyIntegrableOn s

Depends on / 依赖: locallyIntegrableOn, locallyIntegrable_zero, locallyIntegrable_zero.locallyIntegrableOn
-/
theorem locallyIntegrableOn_zero : LocallyIntegrableOn (fun _ => (0 : ε'')) s μ :=
  locallyIntegrable_zero.locallyIntegrableOn s

/--
theorem `LocallyIntegrable.indicator` / 定理 `LocallyIntegrable.indicator`

English:
theorem LocallyIntegrable.indicator
  statement: {f : X -> ε''} (hf : LocallyIntegrable f μ) {s : Set X}
  proof: by
  intro x
  rcases hf x with ⟨U, hU, h'U⟩
  exact ⟨U, hU, h'U.indicator hs⟩

中文:
定理 LocallyIntegrable.indicator
  结论: {f : X -> ε''} (hf : Locally整数egrable f μ) {s : Set X}
  证明: by
  intro x
  rcases hf x with ⟨U, hU, h'U⟩
  exact ⟨U, hU, h'U.indicator hs⟩

Depends on / 依赖: U.indicator, indicator
-/
theorem LocallyIntegrable.indicator {f : X -> ε''} (hf : LocallyIntegrable f μ) {s : Set X}
    (hs : MeasurableSet s) : LocallyIntegrable (s.indicator f) μ := by
  intro x
  rcases hf x with ⟨U, hU, h'U⟩
  exact ⟨U, hU, h'U.indicator hs⟩

/--
theorem `locallyIntegrable_map_homeomorph` / 定理 `locallyIntegrable_map_homeomorph`

English:
theorem locallyIntegrable_map_homeomorph
  statement: [BorelSpace X] [BorelSpace Y] (e : X ≃ₜ Y) {f : Y -> ε''}
  proof: by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rcases h (e x) with ⟨U, hU, h'U⟩
    refine ⟨e ⁻¹' U, e.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
    exact (integrableOn_map_equiv e.toMeasurableEquiv).1 h'U
  · rcases h (e.symm x) with ⟨U, hU, h'U⟩
    refine ⟨e.symm ⁻¹' U, e.symm.continuous.

中文:
定理 locallyIntegrable_map_homeomorph
  结论: [BorelSpace X] [BorelSpace Y] (e : X ≃ₜ Y) {f : Y -> ε''}
  证明: by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rcases h (e x) with ⟨U, hU, h'U⟩
    refine ⟨e ⁻¹' U, e.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
    exact (integrableOn_map_equiv e.toMeasurableEquiv).1 h'U
  · rcases h (e.symm x) with ⟨U, hU, h'U⟩
    refine ⟨e.symm ⁻¹' U, e.symm.continuous.

Depends on / 依赖: Homeomorph, Homeomorph.symm_apply_apply, Homeomorph.toMeasurableEquiv_coe, continuous, continuousAt, convert, e.continuous.continuousAt.preimage_mem_nhds, e.symm, e.symm.continuous.continuousAt.preimage_mem_nhds, e.toMeasurableEquiv, integrableOn_map_equiv, mem_preimage, preimage_mem_nhds, symm_apply_apply, toMeasurableEquiv, toMeasurableEquiv_coe
-/
theorem locallyIntegrable_map_homeomorph [BorelSpace X] [BorelSpace Y] (e : X ≃ₜ Y) {f : Y -> ε''}
    {μ : Measure X} : LocallyIntegrable f (Measure.map e μ) ↔ LocallyIntegrable (f ∘ e) μ := by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rcases h (e x) with ⟨U, hU, h'U⟩
    refine ⟨e ⁻¹' U, e.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
    exact (integrableOn_map_equiv e.toMeasurableEquiv).1 h'U
  · rcases h (e.symm x) with ⟨U, hU, h'U⟩
    refine ⟨e.symm ⁻¹' U, e.symm.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
    apply (integrableOn_map_equiv e.toMeasurableEquiv).2
    simp only [Homeomorph.toMeasurableEquiv_coe]
    convert! h'U
    ext x
    simp only [mem_preimage, Homeomorph.symm_apply_apply]

/--
theorem `LocallyIntegrable.add` / 定理 `LocallyIntegrable.add`

English:
theorem LocallyIntegrable.add
  statement: [ContinuousAdd ε''] {f g : X -> ε''}
  proof: fun x => (hf x).add (hg x)

中文:
定理 LocallyIntegrable.add
  结论: [ContinuousAdd ε''] {f g : X -> ε''}
  证明: fun x => (hf x).add (hg x)
-/
protected theorem LocallyIntegrable.add [ContinuousAdd ε''] {f g : X -> ε''}
    (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ) : LocallyIntegrable (f + g) μ :=
  fun x => (hf x).add (hg x)

/--
theorem `LocallyIntegrable.sub` / 定理 `LocallyIntegrable.sub`

English:
theorem LocallyIntegrable.sub
  statement: {f g : X -> E}
  proof: fun x => (hf x).sub (hg x)

中文:
定理 LocallyIntegrable.sub
  结论: {f g : X -> E}
  证明: fun x => (hf x).sub (hg x)
-/
protected theorem LocallyIntegrable.sub {f g : X -> E}
    (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ) : LocallyIntegrable (f - g) μ :=
  fun x => (hf x).sub (hg x)

/--
theorem `LocallyIntegrable.neg` / 定理 `LocallyIntegrable.neg`

English:
theorem LocallyIntegrable.neg
  given: {f : X -> E} (hf : LocallyIntegrable f μ)
  proof: fun x => (hf x).neg

中文:
定理 LocallyIntegrable.neg
  条件: {f : X -> E} (hf : Locally整数egrable f μ)
  证明: fun x => (hf x).neg
-/
protected theorem LocallyIntegrable.neg {f : X -> E} (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (-f) μ := fun x => (hf x).neg

/--
theorem `locallyIntegrable_neg_iff` / 定理 `locallyIntegrable_neg_iff`

English:
theorem locallyIntegrable_neg_iff
  given: {f : X -> E}
  proof: by
  simp [← locallyIntegrableOn_univ]

中文:
定理 locallyIntegrable_neg_iff
  条件: {f : X -> E}
  证明: by
  simp [← locallyIntegrableOn_univ]
-/
@[simp] theorem locallyIntegrable_neg_iff {f : X -> E} :
    LocallyIntegrable (-f) μ ↔ LocallyIntegrable f μ := by
  simp [← locallyIntegrableOn_univ]

/--
theorem `LocallyIntegrable.smul` / 定理 `LocallyIntegrable.smul`

English:
theorem LocallyIntegrable.smul
  statement: {f : X -> E} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
  proof: fun x => (hf x).smul c

中文:
定理 LocallyIntegrable.smul
  结论: {f : X -> E} {𝕜 : 类型} [NormedAddCommGroup 𝕜]
  证明: fun x => (hf x).smul c
-/
protected theorem LocallyIntegrable.smul {f : X -> E} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] (hf : LocallyIntegrable f μ) (c : 𝕜) :
    LocallyIntegrable (c • f) μ := fun x => (hf x).smul c

-- TODO: generalise this to ENormed spaces, once there are suitable typeclasses
/--
theorem `locallyIntegrable_smul_iff` / 定理 `locallyIntegrable_smul_iff`

English:
theorem locallyIntegrable_smul_iff
  statement: {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
  proof: by
  simp [← locallyIntegrableOn_univ]

中文:
定理 locallyIntegrable_smul_iff
  结论: {𝕜 : 类型} [NormedField 𝕜] [NormedSpace 𝕜 E]
  证明: by
  simp [← locallyIntegrableOn_univ]
-/
@[simp] theorem locallyIntegrable_smul_iff {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]
    {f : X -> E} (c : 𝕜) :
    LocallyIntegrable (c • f) μ ↔ c = 0 ∨ LocallyIntegrable f μ := by
  simp [← locallyIntegrableOn_univ]

variable {ε''' : Type*} [TopologicalSpace ε'''] [ESeminormedAddCommMonoid ε''']
  [ContinuousAdd ε'''] in
/--
theorem `locallyIntegrable_finsetSum'` / 定理 `locallyIntegrable_finsetSum'`

English:
theorem locallyIntegrable_finsetSum'
  statement: {ι} (s : Finset ι) {f : ι -> X -> ε'''}
  proof: Finset.sum_induction f (fun g => LocallyIntegrable g μ) (fun _ _ => LocallyIntegrable.add)
    locallyIntegrable_zero hf

@[deprecated (since := "2026-04-08")]
alias locallyIntegrable_finset_sum' := locallyIntegrable_finsetSum'

中文:
定理 locallyIntegrable_finsetSum'
  结论: {ι} (s : Finset ι) {f : ι -> X -> ε'''}
  证明: Finset.sum_induction f (fun g => LocallyIntegrable g μ) (fun _ _ => LocallyIntegrable.add)
    locallyIntegrable_zero hf

@[deprecated (since := "2026-04-08")]
alias locallyIntegrable_finset_sum' := locallyIntegrable_finsetSum'

Depends on / 依赖: Finset, Finset.sum_induction, LocallyIntegrable, LocallyIntegrable.add, locallyIntegrable_zero, sum_induction
-/
theorem locallyIntegrable_finsetSum' {ι} (s : Finset ι) {f : ι -> X -> ε'''}
    (hf : forall i in s, LocallyIntegrable (f i) μ) : LocallyIntegrable (∑ i in s, f i) μ :=
  Finset.sum_induction f (fun g => LocallyIntegrable g μ) (fun _ _ => LocallyIntegrable.add)
    locallyIntegrable_zero hf

@[deprecated (since := "2026-04-08")]
alias locallyIntegrable_finset_sum' := locallyIntegrable_finsetSum'

variable {ε''' : Type*} [TopologicalSpace ε'''] [ESeminormedAddCommMonoid ε''']
  [ContinuousAdd ε'''] in
/--
theorem `locallyIntegrable_finsetSum` / 定理 `locallyIntegrable_finsetSum`

English:
theorem locallyIntegrable_finsetSum
  statement: {ι} (s : Finset ι) {f : ι -> X -> ε'''}
  proof: by
  simpa only [← Finset.sum_apply] using locallyIntegrable_finsetSum' s hf

@[deprecated (since := "2026-04-08")]
alias locallyIntegrable_finset_sum := locallyIntegrable_finsetSum

中文:
定理 locallyIntegrable_finsetSum
  结论: {ι} (s : Finset ι) {f : ι -> X -> ε'''}
  证明: by
  simpa only [← Finset.sum_apply] using locallyIntegrable_finsetSum' s hf

@[deprecated (since := "2026-04-08")]
alias locallyIntegrable_finset_sum := locallyIntegrable_finsetSum

Depends on / 依赖: Finset, Finset.sum_apply, locallyIntegrable_finsetSum, sum_apply
-/
theorem locallyIntegrable_finsetSum {ι} (s : Finset ι) {f : ι -> X -> ε'''}
    (hf : forall i in s, LocallyIntegrable (f i) μ) : LocallyIntegrable (fun a => ∑ i in s, f i a) μ := by
  simpa only [← Finset.sum_apply] using locallyIntegrable_finsetSum' s hf

@[deprecated (since := "2026-04-08")]
alias locallyIntegrable_finset_sum := locallyIntegrable_finsetSum

/--
theorem `LocallyIntegrable.integrable_smul_left_of_hasCompactSupport` / 定理 `LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`

English:
theorem LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
  proof: by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x => g x • f x) = (fun x => g x • f x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this]; rw [indicator_smul]
  apply Integr

中文:
定理 LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
  证明: by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x => g x • f x) = (fun x => g x • f x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this]; rw [indicator_smul]
  apply Integr

Depends on / 依赖: Integrable, Integrable.smul_of_top_right, IsCompact, K.indicator, hK.measurableSet, hf.integrableOn_isCompact, hg.memLp_top_of_hasCompactSupport, image_eq_zero_of_notMem_tsupport, indicator, indicator_eq_self, indicator_smul, integrableOn_isCompact, integrable_indicator_iff, measurableSet, memLp_top_of_hasCompactSupport, smul_of_top_right, support_subset_iff, tsupport
-/
theorem LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
    {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    [OpensMeasurableSpace X] [T2Space X] {f : X -> E} (hf : LocallyIntegrable f μ)
    {g : X -> 𝕜} (hg : Continuous g) (h'g : HasCompactSupport g) :
    Integrable (fun x => g x • f x) μ := by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x => g x • f x) = (fun x => g x • f x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this]; rw [indicator_smul]
  apply Integrable.smul_of_top_right
  · rw [integrable_indicator_iff hK.measurableSet]
    exact hf.integrableOn_isCompact hK
  · exact hg.memLp_top_of_hasCompactSupport h'g μ

/--
theorem `LocallyIntegrable.integrable_smul_right_of_hasCompactSupport` / 定理 `LocallyIntegrable.integrable_smul_right_of_hasCompactSupport`

English:
theorem LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
  proof: by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x => f x • g x) = (fun x => f x • g x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this]; rw [indicator_smul_left]
  apply I

中文:
定理 LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
  证明: by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x => f x • g x) = (fun x => f x • g x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this]; rw [indicator_smul_left]
  apply I

Depends on / 依赖: Integrable, Integrable.smul_of_top_left, IsCompact, K.indicator, hK.measurableSet, hf.integrableOn_isCompact, hg.memLp_top_of_hasCompactSupport, image_eq_zero_of_notMem_tsupport, indicator, indicator_eq_self, indicator_smul_left, integrableOn_isCompact, integrable_indicator_iff, measurableSet, memLp_top_of_hasCompactSupport, smul_of_top_left, support_subset_iff, tsupport
-/
theorem LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
     {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
     [OpensMeasurableSpace X] [T2Space X] {f : X -> 𝕜} (hf : LocallyIntegrable f μ)
     {g : X -> E} (hg : Continuous g) (h'g : HasCompactSupport g) :
    Integrable (fun x => f x • g x) μ := by
  let K := tsupport g
  have hK : IsCompact K := h'g
  have : K.indicator (fun x => f x • g x) = (fun x => f x • g x) := by
    apply indicator_eq_self.2
    apply support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this]; rw [indicator_smul_left]
  apply Integrable.smul_of_top_left
  · rw [integrable_indicator_iff hK.measurableSet]
    exact hf.integrableOn_isCompact hK
  · exact hg.memLp_top_of_hasCompactSupport h'g μ

open Filter

variable [PseudoMetrizableSpace ε]

/--
theorem `integrable_iff_integrableAtFilter_cocompact` / 定理 `integrable_iff_integrableAtFilter_cocompact`

English:
theorem integrable_iff_integrableAtFilter_cocompact
  proof: by
  refine ⟨fun hf => ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩, fun ⟨⟨s, hsc, hs⟩, hloc⟩ => ?_⟩
  obtain ⟨t, htc, ht⟩ := mem_cocompact'.mp hsc
  rewrite [← integrableOn_univ, ← compl_union_self s, integrableOn_union]
  exact ⟨(hloc.integrableOn_isCompact htc).mono ht le_rfl, hs⟩

中文:
定理 integrable_iff_integrableAtFilter_cocompact
  证明: by
  refine ⟨fun hf => ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩, fun ⟨⟨s, hsc, hs⟩, hloc⟩ => ?_⟩
  obtain ⟨t, htc, ht⟩ := mem_cocompact'.mp hsc
  rewrite [← integrableOn_univ, ← compl_union_self s, integrableOn_union]
  exact ⟨(hloc.integrableOn_isCompact htc).mono ht le_rfl, hs⟩

Depends on / 依赖: compl_union_self, hf.integrableAtFilter, hf.locallyIntegrable, hloc.integrableOn_isCompact, integrableAtFilter, integrableOn_isCompact, integrableOn_union, integrableOn_univ, le_rfl, locallyIntegrable, mem_cocompact, rewrite
-/
theorem integrable_iff_integrableAtFilter_cocompact :
    Integrable f μ ↔ (IntegrableAtFilter f (cocompact X) μ ∧ LocallyIntegrable f μ) := by
  refine ⟨fun hf => ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩, fun ⟨⟨s, hsc, hs⟩, hloc⟩ => ?_⟩
  obtain ⟨t, htc, ht⟩ := mem_cocompact'.mp hsc
  rewrite [← integrableOn_univ, ← compl_union_self s, integrableOn_union]
  exact ⟨(hloc.integrableOn_isCompact htc).mono ht le_rfl, hs⟩

/--
theorem `integrable_iff_integrableAtFilter_atBot_atTop` / 定理 `integrable_iff_integrableAtFilter_atBot_atTop`

English:
theorem integrable_iff_integrableAtFilter_atBot_atTop
  proof: by
  constructor
  · exact fun hf => ⟨⟨hf.integrableAtFilter _, hf.integrableAtFilter _⟩, hf.locallyIntegrable⟩
  · refine fun h => integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
    exact (IntegrableAtFilter.sup_iff.mpr h.1).filter_mono cocompact_le_atBot_atTop

中文:
定理 integrable_iff_integrableAtFilter_atBot_atTop
  证明: by
  constructor
  · exact fun hf => ⟨⟨hf.integrableAtFilter _, hf.integrableAtFilter _⟩, hf.locallyIntegrable⟩
  · refine fun h => integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
    exact (IntegrableAtFilter.sup_iff.mpr h.1).filter_mono cocompact_le_atBot_atTop

Depends on / 依赖: IntegrableAtFilter, IntegrableAtFilter.sup_iff.mpr, cocompact_le_atBot_atTop, filter_mono, hf.integrableAtFilter, hf.locallyIntegrable, integrableAtFilter, integrable_iff_integrableAtFilter_cocompact, integrable_iff_integrableAtFilter_cocompact.mpr, locallyIntegrable, sup_iff
-/
theorem integrable_iff_integrableAtFilter_atBot_atTop
    [PseudoMetrizableSpace ε''] {f : X -> ε''} [LinearOrder X] [CompactIccSpace X] :
    Integrable f μ ↔
    (IntegrableAtFilter f atBot μ ∧ IntegrableAtFilter f atTop μ) ∧ LocallyIntegrable f μ := by
  constructor
  · exact fun hf => ⟨⟨hf.integrableAtFilter _, hf.integrableAtFilter _⟩, hf.locallyIntegrable⟩
  · refine fun h => integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
    exact (IntegrableAtFilter.sup_iff.mpr h.1).filter_mono cocompact_le_atBot_atTop

/--
theorem `integrable_iff_integrableAtFilter_atBot` / 定理 `integrable_iff_integrableAtFilter_atBot`

English:
theorem integrable_iff_integrableAtFilter_atBot
  given: [LinearOrder X] [OrderTop X] [CompactIccSpace X]
  proof: by
  constructor
  · exact fun hf => ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩
  · refine fun h => integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
    exact h.1.filter_mono cocompact_le_atBot

中文:
定理 integrable_iff_integrableAtFilter_atBot
  条件: [LinearOrder X] [OrderTop X] [CompactIccSpace X]
  证明: by
  constructor
  · exact fun hf => ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩
  · refine fun h => integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
    exact h.1.filter_mono cocompact_le_atBot

Depends on / 依赖: cocompact_le_atBot, filter_mono, hf.integrableAtFilter, hf.locallyIntegrable, integrableAtFilter, integrable_iff_integrableAtFilter_cocompact, integrable_iff_integrableAtFilter_cocompact.mpr, locallyIntegrable
-/
theorem integrable_iff_integrableAtFilter_atBot [LinearOrder X] [OrderTop X] [CompactIccSpace X] :
    Integrable f μ ↔ IntegrableAtFilter f atBot μ ∧ LocallyIntegrable f μ := by
  constructor
  · exact fun hf => ⟨hf.integrableAtFilter _, hf.locallyIntegrable⟩
  · refine fun h => integrable_iff_integrableAtFilter_cocompact.mpr ⟨?_, h.2⟩
    exact h.1.filter_mono cocompact_le_atBot

/--
theorem `integrable_iff_integrableAtFilter_atTop` / 定理 `integrable_iff_integrableAtFilter_atTop`

English:
theorem integrable_iff_integrableAtFilter_atTop
  given: [LinearOrder X] [OrderBot X] [CompactIccSpace X]
  proof: integrable_iff_integrableAtFilter_atBot (X := Xᵒᵈ)

中文:
定理 integrable_iff_integrableAtFilter_atTop
  条件: [LinearOrder X] [OrderBot X] [CompactIccSpace X]
  证明: integrable_iff_integrableAtFilter_atBot (X := Xᵒᵈ)

Depends on / 依赖: integrable_iff_integrableAtFilter_atBot
-/
theorem integrable_iff_integrableAtFilter_atTop [LinearOrder X] [OrderBot X] [CompactIccSpace X] :
    Integrable f μ ↔ IntegrableAtFilter f atTop μ ∧ LocallyIntegrable f μ :=
  integrable_iff_integrableAtFilter_atBot (X := Xᵒᵈ)

variable {a : X}

/--
theorem `integrableOn_Iic_iff_integrableAtFilter_atBot` / 定理 `integrableOn_Iic_iff_integrableAtFilter_atBot`

English:
theorem integrableOn_Iic_iff_integrableAtFilter_atBot
  given: [LinearOrder X] [CompactIccSpace X]
  proof: by
  refine ⟨fun h => ⟨⟨Iic a, Iic_mem_atBot a, h⟩, h.locallyIntegrableOn⟩, fun ⟨⟨s, hsl, hs⟩, h⟩ => ?_⟩
  have : Nonempty X := Nonempty.intro a
  obtain ⟨a', ha'⟩ := mem_atBot_sets.mp hsl
  refine (integrableOn_union.mpr ⟨hs.mono ha' le_rfl, ?_⟩).mono Iic_subset_Iic_union_Icc le_rfl
  exact h.integ

中文:
定理 integrableOn_Iic_iff_integrableAtFilter_atBot
  条件: [LinearOrder X] [CompactIccSpace X]
  证明: by
  refine ⟨fun h => ⟨⟨Iic a, Iic_mem_atBot a, h⟩, h.locallyIntegrableOn⟩, fun ⟨⟨s, hsl, hs⟩, h⟩ => ?_⟩
  have : Nonempty X := Nonempty.intro a
  obtain ⟨a', ha'⟩ := mem_atBot_sets.mp hsl
  refine (integrableOn_union.mpr ⟨hs.mono ha' le_rfl, ?_⟩).mono Iic_subset_Iic_union_Icc le_rfl
  exact h.integ

Depends on / 依赖: Icc_subset_Iic_self, Iic_mem_atBot, Iic_subset_Iic_union_Icc, Nonempty, Nonempty.intro, h.integrableOn_compact_subset, h.locallyIntegrableOn, hs.mono, integrableOn_compact_subset, integrableOn_union, integrableOn_union.mpr, isCompact_Icc, le_rfl, locallyIntegrableOn, mem_atBot_sets, mem_atBot_sets.mp
-/
theorem integrableOn_Iic_iff_integrableAtFilter_atBot [LinearOrder X] [CompactIccSpace X] :
    IntegrableOn f (Iic a) μ ↔ IntegrableAtFilter f atBot μ ∧ LocallyIntegrableOn f (Iic a) μ := by
  refine ⟨fun h => ⟨⟨Iic a, Iic_mem_atBot a, h⟩, h.locallyIntegrableOn⟩, fun ⟨⟨s, hsl, hs⟩, h⟩ => ?_⟩
  have : Nonempty X := Nonempty.intro a
  obtain ⟨a', ha'⟩ := mem_atBot_sets.mp hsl
  refine (integrableOn_union.mpr ⟨hs.mono ha' le_rfl, ?_⟩).mono Iic_subset_Iic_union_Icc le_rfl
  exact h.integrableOn_compact_subset Icc_subset_Iic_self isCompact_Icc

/--
theorem `integrableOn_Ici_iff_integrableAtFilter_atTop` / 定理 `integrableOn_Ici_iff_integrableAtFilter_atTop`

English:
theorem integrableOn_Ici_iff_integrableAtFilter_atTop
  given: [LinearOrder X] [CompactIccSpace X]
  proof: integrableOn_Iic_iff_integrableAtFilter_atBot (X := Xᵒᵈ)

中文:
定理 integrableOn_Ici_iff_integrableAtFilter_atTop
  条件: [LinearOrder X] [CompactIccSpace X]
  证明: integrableOn_Iic_iff_integrableAtFilter_atBot (X := Xᵒᵈ)

Depends on / 依赖: integrableOn_Iic_iff_integrableAtFilter_atBot
-/
theorem integrableOn_Ici_iff_integrableAtFilter_atTop [LinearOrder X] [CompactIccSpace X] :
    IntegrableOn f (Ici a) μ ↔ IntegrableAtFilter f atTop μ ∧ LocallyIntegrableOn f (Ici a) μ :=
  integrableOn_Iic_iff_integrableAtFilter_atBot (X := Xᵒᵈ)

/--
theorem `integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin` / 定理 `integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin`

English:
theorem integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin
  proof: by
  constructor
  · intro h
    exact ⟨⟨Iio a, Iio_mem_atBot a, h⟩, ⟨Iio a, self_mem_nhdsWithin, h⟩, h.locallyIntegrableOn⟩
  · intro ⟨hbot, ⟨s, hsl, hs⟩, hlocal⟩
    obtain ⟨s', ⟨hs'_mono, hs'⟩⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hsl
    refine (integrableOn_union.mpr ⟨?_, hs.mono hs' le_rfl⟩)

中文:
定理 integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin
  证明: by
  constructor
  · intro h
    exact ⟨⟨Iio a, Iio_mem_atBot a, h⟩, ⟨Iio a, self_mem_nhdsWithin, h⟩, h.locallyIntegrableOn⟩
  · intro ⟨hbot, ⟨s, hsl, hs⟩, hlocal⟩
    obtain ⟨s', ⟨hs'_mono, hs'⟩⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hsl
    refine (integrableOn_union.mpr ⟨?_, hs.mono hs' le_rfl⟩)

Depends on / 依赖: Iic_subset_Iio, Iic_subset_Iio.mpr, Iio_mem_atBot, Iio_subset_Iic_union_Ioo, _mono, h.locallyIntegrableOn, hlocal, hlocal.mono_set, hs.mono, integrableOn_Iic_iff_integrableAtFilter_atBot, integrableOn_Iic_iff_integrableAtFilter_atBot.mpr, integrableOn_union, integrableOn_union.mpr, le_rfl, locallyIntegrableOn, mem_nhdsLT_iff_exists_Ioo_subset, mem_nhdsLT_iff_exists_Ioo_subset.mp, mono_set, self_mem_nhdsWithin
-/
theorem integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin
    [LinearOrder X] [CompactIccSpace X] [NoMinOrder X] [OrderTopology X] :
    IntegrableOn f (Iio a) μ ↔ IntegrableAtFilter f atBot μ ∧
    IntegrableAtFilter f (𝓝[<] a) μ ∧ LocallyIntegrableOn f (Iio a) μ := by
  constructor
  · intro h
    exact ⟨⟨Iio a, Iio_mem_atBot a, h⟩, ⟨Iio a, self_mem_nhdsWithin, h⟩, h.locallyIntegrableOn⟩
  · intro ⟨hbot, ⟨s, hsl, hs⟩, hlocal⟩
    obtain ⟨s', ⟨hs'_mono, hs'⟩⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hsl
    refine (integrableOn_union.mpr ⟨?_, hs.mono hs' le_rfl⟩).mono Iio_subset_Iic_union_Ioo le_rfl
    exact integrableOn_Iic_iff_integrableAtFilter_atBot.mpr
      ⟨hbot, hlocal.mono_set (Iic_subset_Iio.mpr hs'_mono)⟩

/--
theorem `integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin` / 定理 `integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin`

English:
theorem integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin
  proof: integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin (X := Xᵒᵈ)

中文:
定理 integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin
  证明: integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin (X := Xᵒᵈ)

Depends on / 依赖: integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin
-/
theorem integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin
    [LinearOrder X] [CompactIccSpace X] [NoMaxOrder X] [OrderTopology X] :
    IntegrableOn f (Ioi a) μ ↔ IntegrableAtFilter f atTop μ ∧
    IntegrableAtFilter f (𝓝[>] a) μ ∧ LocallyIntegrableOn f (Ioi a) μ :=
  integrableOn_Iio_iff_integrableAtFilter_atBot_nhdsWithin (X := Xᵒᵈ)

end MeasureTheory

open MeasureTheory

section borel

variable [OpensMeasurableSpace X]
variable {K : Set X} {f : X -> E} {a b : X}

/--
theorem `Continuous.locallyIntegrable` / 定理 `Continuous.locallyIntegrable`

English:
theorem Continuous.locallyIntegrable
  statement: [IsLocallyFiniteMeasure μ] [SecondCountableTopologyEither X E]
  proof: hf.integrableAt_nhds

中文:
定理 Continuous.locallyIntegrable
  结论: [IsLocallyFiniteMeasure μ] [SecondCountableTopologyEither X E]
  证明: hf.integrableAt_nhds

Depends on / 依赖: hf.integrableAt_nhds, integrableAt_nhds
-/
theorem Continuous.locallyIntegrable [IsLocallyFiniteMeasure μ] [SecondCountableTopologyEither X E]
    (hf : Continuous f) : LocallyIntegrable f μ :=
  hf.integrableAt_nhds

/--
theorem `ContinuousOn.locallyIntegrableOn` / 定理 `ContinuousOn.locallyIntegrableOn`

English:
theorem ContinuousOn.locallyIntegrableOn
  statement: [IsLocallyFiniteMeasure μ]
  proof: fun _x hx =>
  hf.integrableAt_nhdsWithin hK hx

中文:
定理 ContinuousOn.locallyIntegrableOn
  结论: [IsLocallyFiniteMeasure μ]
  证明: fun _x hx =>
  hf.integrableAt_nhdsWithin hK hx
-/
theorem ContinuousOn.locallyIntegrableOn [IsLocallyFiniteMeasure μ]
    [SecondCountableTopologyEither X E] (hf : ContinuousOn f K)
    (hK : MeasurableSet K) : LocallyIntegrableOn f K μ := fun _x hx =>
  hf.integrableAt_nhdsWithin hK hx

/--
theorem `ContinuousOn.integrableOn_of_subset_isCompact` / 定理 `ContinuousOn.integrableOn_of_subset_isCompact`

English:
theorem ContinuousOn.integrableOn_of_subset_isCompact
  statement: (hf : ContinuousOn f K)
  proof: by
  refine ⟨hf.aestronglyMeasurable_of_subset_isCompact hK hs h's, ?_⟩
  have : Fact (μ s < ∞) := ⟨mus.lt_top⟩
  obtain ⟨C, hC⟩ : exists C, forall x in f '' K, ‖x‖ <= C :=
    IsBounded.exists_norm_le (hK.image_of_continuousOn hf).isBounded
  apply HasFiniteIntegral.of_bounded (C := C)
  filter_upw

中文:
定理 ContinuousOn.integrableOn_of_subset_isCompact
  结论: (hf : ContinuousOn f K)
  证明: by
  refine ⟨hf.aestronglyMeasurable_of_subset_isCompact hK hs h's, ?_⟩
  have : Fact (μ s < ∞) := ⟨mus.lt_top⟩
  obtain ⟨C, hC⟩ : exists C, forall x in f '' K, ‖x‖ <= C :=
    IsBounded.exists_norm_le (hK.image_of_continuousOn hf).isBounded
  apply HasFiniteIntegral.of_bounded (C := C)
  filter_upw

Depends on / 依赖: HasFiniteIntegral, HasFiniteIntegral.of_bounded, IsBounded, IsBounded.exists_norm_le, ae_restrict_mem, aestronglyMeasurable_of_subset_isCompact, exists_norm_le, filter_upwards, hK.image_of_continuousOn, hf.aestronglyMeasurable_of_subset_isCompact, image_of_continuousOn, isBounded, lt_top, mem_image_of_mem, mus.lt_top, of_bounded
-/
theorem ContinuousOn.integrableOn_of_subset_isCompact (hf : ContinuousOn f K)
    (hK : IsCompact K) (hs : MeasurableSet s) (h's : s subseteq K) (mus : μ s != ∞) :
    IntegrableOn f s μ := by
  refine ⟨hf.aestronglyMeasurable_of_subset_isCompact hK hs h's, ?_⟩
  have : Fact (μ s < ∞) := ⟨mus.lt_top⟩
  obtain ⟨C, hC⟩ : exists C, forall x in f '' K, ‖x‖ <= C :=
    IsBounded.exists_norm_le (hK.image_of_continuousOn hf).isBounded
  apply HasFiniteIntegral.of_bounded (C := C)
  filter_upwards [ae_restrict_mem hs] with a ha using hC _ (mem_image_of_mem f (h's ha))

variable [IsFiniteMeasureOnCompacts μ]

/--
theorem `ContinuousOn.integrableOn_compact'` / 定理 `ContinuousOn.integrableOn_compact'`

English:
theorem ContinuousOn.integrableOn_compact'
  proof: hf.integrableOn_of_subset_isCompact hK h'K Subset.rfl hK.measure_ne_top

中文:
定理 ContinuousOn.integrableOn_compact'
  证明: hf.integrableOn_of_subset_isCompact hK h'K Subset.rfl hK.measure_ne_top

Depends on / 依赖: Subset, Subset.rfl, hK.measure_ne_top, hf.integrableOn_of_subset_isCompact, integrableOn_of_subset_isCompact, measure_ne_top
-/
theorem ContinuousOn.integrableOn_compact'
    (hK : IsCompact K) (h'K : MeasurableSet K) (hf : ContinuousOn f K) :
    IntegrableOn f K μ :=
  hf.integrableOn_of_subset_isCompact hK h'K Subset.rfl hK.measure_ne_top

/--
theorem `ContinuousOn.integrableOn_compact` / 定理 `ContinuousOn.integrableOn_compact`

English:
theorem ContinuousOn.integrableOn_compact
  statement: [T2Space X]
  proof: hf.integrableOn_compact' hK hK.measurableSet

中文:
定理 ContinuousOn.integrableOn_compact
  结论: [T2Space X]
  证明: hf.integrableOn_compact' hK hK.measurableSet

Depends on / 依赖: hK.measurableSet, hf.integrableOn_compact, integrableOn_compact, measurableSet
-/
theorem ContinuousOn.integrableOn_compact [T2Space X]
    (hK : IsCompact K) (hf : ContinuousOn f K) : IntegrableOn f K μ :=
  hf.integrableOn_compact' hK hK.measurableSet

/--
theorem `ContinuousOn.integrableOn_Icc` / 定理 `ContinuousOn.integrableOn_Icc`

English:
theorem ContinuousOn.integrableOn_Icc
  statement: [Preorder X] [CompactIccSpace X] [T2Space X]
  proof: hf.integrableOn_compact isCompact_Icc

中文:
定理 ContinuousOn.integrableOn_Icc
  结论: [Preorder X] [CompactIccSpace X] [T2Space X]
  证明: hf.integrableOn_compact isCompact_Icc

Depends on / 依赖: hf.integrableOn_compact, integrableOn_compact, isCompact_Icc
-/
theorem ContinuousOn.integrableOn_Icc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : ContinuousOn f (Icc a b)) : IntegrableOn f (Icc a b) μ :=
  hf.integrableOn_compact isCompact_Icc

/--
theorem `Continuous.integrableOn_Icc` / 定理 `Continuous.integrableOn_Icc`

English:
theorem Continuous.integrableOn_Icc
  statement: [Preorder X] [CompactIccSpace X] [T2Space X]
  proof: hf.continuousOn.integrableOn_Icc

中文:
定理 Continuous.integrableOn_Icc
  结论: [Preorder X] [CompactIccSpace X] [T2Space X]
  证明: hf.continuousOn.integrableOn_Icc

Depends on / 依赖: continuousOn, hf.continuousOn.integrableOn_Icc, integrableOn_Icc
-/
theorem Continuous.integrableOn_Icc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Icc a b) μ :=
  hf.continuousOn.integrableOn_Icc

/--
theorem `Continuous.integrableOn_Ioc` / 定理 `Continuous.integrableOn_Ioc`

English:
theorem Continuous.integrableOn_Ioc
  statement: [Preorder X] [CompactIccSpace X] [T2Space X]
  proof: hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self

中文:
定理 Continuous.integrableOn_Ioc
  结论: [Preorder X] [CompactIccSpace X] [T2Space X]
  证明: hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self

Depends on / 依赖: Ioc_subset_Icc_self, hf.integrableOn_Icc.mono_set, integrableOn_Icc, mono_set
-/
theorem Continuous.integrableOn_Ioc [Preorder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Ioc a b) μ :=
  hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/--
theorem `ContinuousOn.integrableOn_uIcc` / 定理 `ContinuousOn.integrableOn_uIcc`

English:
theorem ContinuousOn.integrableOn_uIcc
  statement: [LinearOrder X] [CompactIccSpace X] [T2Space X]
  proof: hf.integrableOn_Icc

中文:
定理 ContinuousOn.integrableOn_uIcc
  结论: [LinearOrder X] [CompactIccSpace X] [T2Space X]
  证明: hf.integrableOn_Icc

Depends on / 依赖: hf.integrableOn_Icc, integrableOn_Icc
-/
theorem ContinuousOn.integrableOn_uIcc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : ContinuousOn f [[a, b]]) : IntegrableOn f [[a, b]] μ :=
  hf.integrableOn_Icc

/--
theorem `Continuous.integrableOn_uIcc` / 定理 `Continuous.integrableOn_uIcc`

English:
theorem Continuous.integrableOn_uIcc
  statement: [LinearOrder X] [CompactIccSpace X] [T2Space X]
  proof: hf.integrableOn_Icc

中文:
定理 Continuous.integrableOn_uIcc
  结论: [LinearOrder X] [CompactIccSpace X] [T2Space X]
  证明: hf.integrableOn_Icc

Depends on / 依赖: hf.integrableOn_Icc, integrableOn_Icc
-/
theorem Continuous.integrableOn_uIcc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f [[a, b]] μ :=
  hf.integrableOn_Icc

open scoped Interval in
/--
theorem `Continuous.integrableOn_uIoc` / 定理 `Continuous.integrableOn_uIoc`

English:
theorem Continuous.integrableOn_uIoc
  statement: [LinearOrder X] [CompactIccSpace X] [T2Space X]
  proof: hf.integrableOn_Ioc

中文:
定理 Continuous.integrableOn_uIoc
  结论: [LinearOrder X] [CompactIccSpace X] [T2Space X]
  证明: hf.integrableOn_Ioc

Depends on / 依赖: hf.integrableOn_Ioc, integrableOn_Ioc
-/
theorem Continuous.integrableOn_uIoc [LinearOrder X] [CompactIccSpace X] [T2Space X]
    (hf : Continuous f) : IntegrableOn f (Ι a b) μ :=
  hf.integrableOn_Ioc

/--
theorem `Continuous.integrable_of_hasCompactSupport` / 定理 `Continuous.integrable_of_hasCompactSupport`

English:
theorem Continuous.integrable_of_hasCompactSupport
  given: (hf : Continuous f) (hcf : HasCompactSupport f)
  proof: (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
    hf.continuousOn.integrableOn_compact' hcf (isClosed_tsupport _).measurableSet

中文:
定理 Continuous.integrable_of_hasCompactSupport
  条件: (hf : Continuous f) (hcf : HasCompactSupport f)
  证明: (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
    hf.continuousOn.integrableOn_compact' hcf (isClosed_tsupport _).measurableSet

Depends on / 依赖: continuousOn, hf.continuousOn.integrableOn_compact, integrableOn_compact, integrableOn_iff_integrable_of_support_subset, isClosed_tsupport, measurableSet, subset_tsupport
-/
theorem Continuous.integrable_of_hasCompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) :
    Integrable f μ :=
(integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
    hf.continuousOn.integrableOn_compact' hcf (isClosed_tsupport _).measurableSet

end borel

open scoped ENNReal

section Monotone

variable [BorelSpace X] [ConditionallyCompleteLinearOrder X] [ConditionallyCompleteLinearOrder E]
  [OrderTopology X] [OrderTopology E] [SecondCountableTopology E] {p : Real>=0∞}
  {f : X -> E}

/--
theorem `MonotoneOn.memLp_top` / 定理 `MonotoneOn.memLp_top`

English:
theorem MonotoneOn.memLp_top
  statement: (hmono : MonotoneOn f s) {a b : X}
  proof: by
  borelize E
  have hbelow : BddBelow (f '' s) := ⟨f a, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono ha.1 hy (ha.2 hy)⟩
  have habove : BddAbove (f '' s) := ⟨f b, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono hy hb.1 (hb.2 hy)⟩
  have : IsBounded (f '' s) := Metric.isBounded_of_bddAbove_of_bddBelow habove hbelow
  rcas

中文:
定理 MonotoneOn.memLp_top
  结论: (hmono : MonotoneOn f s) {a b : X}
  证明: by
  borelize E
  have hbelow : BddBelow (f '' s) := ⟨f a, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono ha.1 hy (ha.2 hy)⟩
  have habove : BddAbove (f '' s) := ⟨f b, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono hy hb.1 (hb.2 hy)⟩
  have : IsBounded (f '' s) := Metric.isBounded_of_bddAbove_of_bddBelow habove hbelow
  rcas

Depends on / 依赖: BddAbove, BddBelow, IsBounded, MemLp.mono, Metric, Metric.isBounded_of_bddAbove_of_bddBelow, aemeasurable_restrict_of_monotoneOn, aestronglyMeasurable, borelize, habove, hbelow, isBounded_iff_forall_norm_le, isBounded_iff_forall_norm_le.mp, isBounded_of_bddAbove_of_bddBelow, memLp_top_const, restrict
-/
theorem MonotoneOn.memLp_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (h's : MeasurableSet s) :
    MemLp f ∞ (μ.restrict s) := by
  borelize E
  have hbelow : BddBelow (f '' s) := ⟨f a, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono ha.1 hy (ha.2 hy)⟩
  have habove : BddAbove (f '' s) := ⟨f b, fun x ⟨y, hy, hyx⟩ => hyx ▸ hmono hy hb.1 (hb.2 hy)⟩
  have : IsBounded (f '' s) := Metric.isBounded_of_bddAbove_of_bddBelow habove hbelow
  rcases isBounded_iff_forall_norm_le.mp this with ⟨C, hC⟩
  have A : MemLp (fun _ => C) ⊤ (μ.restrict s) := memLp_top_const _
  apply MemLp.mono A (aemeasurable_restrict_of_monotoneOn h's hmono).aestronglyMeasurable
  apply (ae_restrict_iff' h's).mpr
  apply ae_of_all _ fun y hy => ?_
  exact (hC _ (mem_image_of_mem f hy)).trans (le_abs_self _)

/--
theorem `MonotoneOn.memLp_of_measure_ne_top` / 定理 `MonotoneOn.memLp_of_measure_ne_top`

English:
theorem MonotoneOn.memLp_of_measure_ne_top
  statement: (hmono : MonotoneOn f s) {a b : X}
  proof: (hmono.memLp_top ha hb h's).mono_exponent_of_measure_support_ne_top (s := univ)
    (by simp) (by simpa using hs) le_top

中文:
定理 MonotoneOn.memLp_of_measure_ne_top
  结论: (hmono : MonotoneOn f s) {a b : X}
  证明: (hmono.memLp_top ha hb h's).mono_exponent_of_measure_support_ne_top (s := univ)
    (by simp) (by simpa using hs) le_top

Depends on / 依赖: hmono.memLp_top, le_top, memLp_top, mono_exponent_of_measure_support_ne_top
-/
theorem MonotoneOn.memLp_of_measure_ne_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s != ∞) (h's : MeasurableSet s) :
    MemLp f p (μ.restrict s) :=
  (hmono.memLp_top ha hb h's).mono_exponent_of_measure_support_ne_top (s := univ)
    (by simp) (by simpa using hs) le_top

/--
theorem `MonotoneOn.memLp_isCompact` / 定理 `MonotoneOn.memLp_isCompact`

English:
theorem MonotoneOn.memLp_isCompact
  statement: [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
  proof: by
  obtain rfl | h := s.eq_empty_or_nonempty
  · simp
  · exact hmono.memLp_of_measure_ne_top (hs.isLeast_sInf h) (hs.isGreatest_sSup h)
      hs.measure_lt_top.ne hs.measurableSet

中文:
定理 MonotoneOn.memLp_isCompact
  结论: [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
  证明: by
  obtain rfl | h := s.eq_empty_or_nonempty
  · simp
  · exact hmono.memLp_of_measure_ne_top (hs.isLeast_sInf h) (hs.isGreatest_sSup h)
      hs.measure_lt_top.ne hs.measurableSet

Depends on / 依赖: eq_empty_or_nonempty, hmono.memLp_of_measure_ne_top, hs.isGreatest_sSup, hs.isLeast_sInf, hs.measurableSet, hs.measure_lt_top.ne, isGreatest_sSup, isLeast_sInf, measurableSet, measure_lt_top, memLp_of_measure_ne_top, s.eq_empty_or_nonempty
-/
theorem MonotoneOn.memLp_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hmono : MonotoneOn f s) : MemLp f p (μ.restrict s) := by
  obtain rfl | h := s.eq_empty_or_nonempty
  · simp
  · exact hmono.memLp_of_measure_ne_top (hs.isLeast_sInf h) (hs.isGreatest_sSup h)
      hs.measure_lt_top.ne hs.measurableSet

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `AntitoneOn.memLp_top` / 定理 `AntitoneOn.memLp_top`

English:
theorem AntitoneOn.memLp_top
  statement: (hanti : AntitoneOn f s) {a b : X}
  proof: MonotoneOn.memLp_top (E := Eᵒᵈ) hanti ha hb h's

中文:
定理 AntitoneOn.memLp_top
  结论: (hanti : AntitoneOn f s) {a b : X}
  证明: MonotoneOn.memLp_top (E := Eᵒᵈ) hanti ha hb h's

Depends on / 依赖: MonotoneOn, MonotoneOn.memLp_top, memLp_top
-/
theorem AntitoneOn.memLp_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (h's : MeasurableSet s) :
    MemLp f ∞ (μ.restrict s) :=
  MonotoneOn.memLp_top (E := Eᵒᵈ) hanti ha hb h's

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `AntitoneOn.memLp_of_measure_ne_top` / 定理 `AntitoneOn.memLp_of_measure_ne_top`

English:
theorem AntitoneOn.memLp_of_measure_ne_top
  statement: (hanti : AntitoneOn f s) {a b : X}
  proof: MonotoneOn.memLp_of_measure_ne_top (E := Eᵒᵈ) hanti ha hb hs h's

中文:
定理 AntitoneOn.memLp_of_measure_ne_top
  结论: (hanti : AntitoneOn f s) {a b : X}
  证明: MonotoneOn.memLp_of_measure_ne_top (E := Eᵒᵈ) hanti ha hb hs h's

Depends on / 依赖: MonotoneOn, MonotoneOn.memLp_of_measure_ne_top, memLp_of_measure_ne_top
-/
theorem AntitoneOn.memLp_of_measure_ne_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s != ∞) (h's : MeasurableSet s) :
    MemLp f p (μ.restrict s) :=
  MonotoneOn.memLp_of_measure_ne_top (E := Eᵒᵈ) hanti ha hb hs h's

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `AntitoneOn.memLp_isCompact` / 定理 `AntitoneOn.memLp_isCompact`

English:
theorem AntitoneOn.memLp_isCompact
  statement: [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
  proof: MonotoneOn.memLp_isCompact (E := Eᵒᵈ) hs hanti

中文:
定理 AntitoneOn.memLp_isCompact
  结论: [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
  证明: MonotoneOn.memLp_isCompact (E := Eᵒᵈ) hs hanti

Depends on / 依赖: MonotoneOn, MonotoneOn.memLp_isCompact, memLp_isCompact
-/
theorem AntitoneOn.memLp_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hanti : AntitoneOn f s) : MemLp f p (μ.restrict s) :=
  MonotoneOn.memLp_isCompact (E := Eᵒᵈ) hs hanti

/--
theorem `MonotoneOn.integrableOn_of_measure_ne_top` / 定理 `MonotoneOn.integrableOn_of_measure_ne_top`

English:
theorem MonotoneOn.integrableOn_of_measure_ne_top
  statement: (hmono : MonotoneOn f s) {a b : X}
  proof: memLp_one_iff_integrable.1 (hmono.memLp_of_measure_ne_top ha hb hs h's)

中文:
定理 MonotoneOn.integrableOn_of_measure_ne_top
  结论: (hmono : MonotoneOn f s) {a b : X}
  证明: memLp_one_iff_integrable.1 (hmono.memLp_of_measure_ne_top ha hb hs h's)

Depends on / 依赖: hmono.memLp_of_measure_ne_top, memLp_of_measure_ne_top, memLp_one_iff_integrable
-/
theorem MonotoneOn.integrableOn_of_measure_ne_top (hmono : MonotoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s != ∞) (h's : MeasurableSet s) :
    IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hmono.memLp_of_measure_ne_top ha hb hs h's)

/--
theorem `MonotoneOn.integrableOn_isCompact` / 定理 `MonotoneOn.integrableOn_isCompact`

English:
theorem MonotoneOn.integrableOn_isCompact
  statement: [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
  proof: memLp_one_iff_integrable.1 (hmono.memLp_isCompact hs)

中文:
定理 MonotoneOn.integrableOn_isCompact
  结论: [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
  证明: memLp_one_iff_integrable.1 (hmono.memLp_isCompact hs)

Depends on / 依赖: hmono.memLp_isCompact, memLp_isCompact, memLp_one_iff_integrable
-/
theorem MonotoneOn.integrableOn_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hmono : MonotoneOn f s) : IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hmono.memLp_isCompact hs)

/--
theorem `AntitoneOn.integrableOn_of_measure_ne_top` / 定理 `AntitoneOn.integrableOn_of_measure_ne_top`

English:
theorem AntitoneOn.integrableOn_of_measure_ne_top
  statement: (hanti : AntitoneOn f s) {a b : X}
  proof: memLp_one_iff_integrable.1 (hanti.memLp_of_measure_ne_top ha hb hs h's)

中文:
定理 AntitoneOn.integrableOn_of_measure_ne_top
  结论: (hanti : AntitoneOn f s) {a b : X}
  证明: memLp_one_iff_integrable.1 (hanti.memLp_of_measure_ne_top ha hb hs h's)

Depends on / 依赖: hanti.memLp_of_measure_ne_top, memLp_of_measure_ne_top, memLp_one_iff_integrable
-/
theorem AntitoneOn.integrableOn_of_measure_ne_top (hanti : AntitoneOn f s) {a b : X}
    (ha : IsLeast s a) (hb : IsGreatest s b) (hs : μ s != ∞) (h's : MeasurableSet s) :
    IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hanti.memLp_of_measure_ne_top ha hb hs h's)

/--
theorem `AntitoneOn.integrableOn_isCompact` / 定理 `AntitoneOn.integrableOn_isCompact`

English:
theorem AntitoneOn.integrableOn_isCompact
  statement: [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
  proof: memLp_one_iff_integrable.1 (hanti.memLp_isCompact hs)

中文:
定理 AntitoneOn.integrableOn_isCompact
  结论: [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
  证明: memLp_one_iff_integrable.1 (hanti.memLp_isCompact hs)

Depends on / 依赖: hanti.memLp_isCompact, memLp_isCompact, memLp_one_iff_integrable
-/
theorem AntitoneOn.integrableOn_isCompact [IsFiniteMeasureOnCompacts μ] (hs : IsCompact s)
    (hanti : AntitoneOn f s) : IntegrableOn f s μ :=
  memLp_one_iff_integrable.1 (hanti.memLp_isCompact hs)

/--
theorem `Monotone.locallyIntegrable` / 定理 `Monotone.locallyIntegrable`

English:
theorem Monotone.locallyIntegrable
  given: [IsLocallyFiniteMeasure μ] (hmono : Monotone f)
  proof: by
  intro x
  rcases μ.finiteAt_nhds x with ⟨U, hU, h'U⟩
  obtain ⟨a, b, xab, hab, abU⟩ : exists a b : X, x in Icc a b ∧ Icc a b in 𝓝 x ∧ Icc a b subseteq U :=
    exists_Icc_mem_subset_of_mem_nhds hU
  have ab : a <= b := xab.1.trans xab.2
  refine ⟨Icc a b, hab, ?_⟩
  exact
    (hmono.monotoneOn 

中文:
定理 Monotone.locallyIntegrable
  条件: [IsLocallyFiniteMeasure μ] (hmono : Monotone f)
  证明: by
  intro x
  rcases μ.finiteAt_nhds x with ⟨U, hU, h'U⟩
  obtain ⟨a, b, xab, hab, abU⟩ : exists a b : X, x in Icc a b ∧ Icc a b in 𝓝 x ∧ Icc a b subseteq U :=
    exists_Icc_mem_subset_of_mem_nhds hU
  have ab : a <= b := xab.1.trans xab.2
  refine ⟨Icc a b, hab, ?_⟩
  exact
    (hmono.monotoneOn 

Depends on / 依赖: exists_Icc_mem_subset_of_mem_nhds, finiteAt_nhds, hmono.monotoneOn, integrableOn_of_measure_ne_top, isGreatest_Icc, isLeast_Icc, measurableSet_Icc, measure_mono, monotoneOn, subseteq, trans_lt
-/
theorem Monotone.locallyIntegrable [IsLocallyFiniteMeasure μ] (hmono : Monotone f) :
    LocallyIntegrable f μ := by
  intro x
  rcases μ.finiteAt_nhds x with ⟨U, hU, h'U⟩
  obtain ⟨a, b, xab, hab, abU⟩ : exists a b : X, x in Icc a b ∧ Icc a b in 𝓝 x ∧ Icc a b subseteq U :=
    exists_Icc_mem_subset_of_mem_nhds hU
  have ab : a <= b := xab.1.trans xab.2
  refine ⟨Icc a b, hab, ?_⟩
  exact
    (hmono.monotoneOn _).integrableOn_of_measure_ne_top (isLeast_Icc ab) (isGreatest_Icc ab)
      ((measure_mono abU).trans_lt h'U).ne measurableSet_Icc

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Antitone.locallyIntegrable` / 定理 `Antitone.locallyIntegrable`

English:
theorem Antitone.locallyIntegrable
  given: [IsLocallyFiniteMeasure μ] (hanti : Antitone f)
  proof: hanti.dual_right.locallyIntegrable

中文:
定理 Antitone.locallyIntegrable
  条件: [IsLocallyFiniteMeasure μ] (hanti : Antitone f)
  证明: hanti.dual_right.locallyIntegrable

Depends on / 依赖: dual_right, hanti.dual_right.locallyIntegrable, locallyIntegrable
-/
theorem Antitone.locallyIntegrable [IsLocallyFiniteMeasure μ] (hanti : Antitone f) :
    LocallyIntegrable f μ :=
  hanti.dual_right.locallyIntegrable

end Monotone

namespace MeasureTheory

variable [OpensMeasurableSpace X] {A K : Set X}

section Mul

variable [NormedRing R] [SecondCountableTopologyEither X R] {g g' : X -> R}

/--
theorem `IntegrableOn.mul_continuousOn_of_subset` / 定理 `IntegrableOn.mul_continuousOn_of_subset`

English:
theorem IntegrableOn.mul_continuousOn_of_subset
  statement: (hg : IntegrableOn g A μ) (hg' : ContinuousOn g' K)
  proof: by
  rcases IsCompact.exists_bound_of_continuousOn hK hg' with ⟨C, hC⟩
  exact hg.mul_bdd ((hg'.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

中文:
定理 IntegrableOn.mul_continuousOn_of_subset
  结论: (hg : 整数egrableOn g A μ) (hg' : ContinuousOn g' K)
  证明: by
  rcases IsCompact.exists_bound_of_continuousOn hK hg' with ⟨C, hC⟩
  exact hg.mul_bdd ((hg'.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

Depends on / 依赖: IsCompact, IsCompact.exists_bound_of_continuousOn, ae_restrict_of_forall_mem, aestronglyMeasurable, exists_bound_of_continuousOn, hg.mul_bdd, mul_bdd
-/
theorem IntegrableOn.mul_continuousOn_of_subset (hg : IntegrableOn g A μ) (hg' : ContinuousOn g' K)
    (hA : MeasurableSet A) (hK : IsCompact K) (hAK : A subseteq K) :
    IntegrableOn (fun x => g x * g' x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hg' with ⟨C, hC⟩
  exact hg.mul_bdd ((hg'.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

/--
theorem `IntegrableOn.mul_continuousOn` / 定理 `IntegrableOn.mul_continuousOn`

English:
theorem IntegrableOn.mul_continuousOn
  statement: [T2Space X] (hg : IntegrableOn g K μ)
  proof: hg.mul_continuousOn_of_subset hg' hK.measurableSet hK (Subset.refl _)

中文:
定理 IntegrableOn.mul_continuousOn
  结论: [T2Space X] (hg : 整数egrableOn g K μ)
  证明: hg.mul_continuousOn_of_subset hg' hK.measurableSet hK (Subset.refl _)

Depends on / 依赖: Subset, Subset.refl, hK.measurableSet, hg.mul_continuousOn_of_subset, measurableSet, mul_continuousOn_of_subset
-/
theorem IntegrableOn.mul_continuousOn [T2Space X] (hg : IntegrableOn g K μ)
    (hg' : ContinuousOn g' K) (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  hg.mul_continuousOn_of_subset hg' hK.measurableSet hK (Subset.refl _)

/--
theorem `IntegrableOn.continuousOn_mul_of_subset` / 定理 `IntegrableOn.continuousOn_mul_of_subset`

English:
theorem IntegrableOn.continuousOn_mul_of_subset
  statement: (hg : ContinuousOn g K) (hg' : IntegrableOn g' A μ)
  proof: by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  exact hg'.bdd_mul ((hg.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

中文:
定理 IntegrableOn.continuousOn_mul_of_subset
  结论: (hg : ContinuousOn g K) (hg' : 整数egrableOn g' A μ)
  证明: by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  exact hg'.bdd_mul ((hg.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

Depends on / 依赖: IsCompact, IsCompact.exists_bound_of_continuousOn, ae_restrict_of_forall_mem, aestronglyMeasurable, bdd_mul, exists_bound_of_continuousOn, hg.mono
-/
theorem IntegrableOn.continuousOn_mul_of_subset (hg : ContinuousOn g K) (hg' : IntegrableOn g' A μ)
    (hK : IsCompact K) (hA : MeasurableSet A) (hAK : A subseteq K) :
    IntegrableOn (fun x => g x * g' x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  exact hg'.bdd_mul ((hg.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

/--
theorem `IntegrableOn.continuousOn_mul` / 定理 `IntegrableOn.continuousOn_mul`

English:
theorem IntegrableOn.continuousOn_mul
  statement: [T2Space X] (hg : ContinuousOn g K)
  proof: hg'.continuousOn_mul_of_subset hg hK hK.measurableSet Subset.rfl

中文:
定理 IntegrableOn.continuousOn_mul
  结论: [T2Space X] (hg : ContinuousOn g K)
  证明: hg'.continuousOn_mul_of_subset hg hK hK.measurableSet Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, continuousOn_mul_of_subset, hK.measurableSet, measurableSet
-/
theorem IntegrableOn.continuousOn_mul [T2Space X] (hg : ContinuousOn g K)
    (hg' : IntegrableOn g' K μ) (hK : IsCompact K) : IntegrableOn (fun x => g x * g' x) K μ :=
  hg'.continuousOn_mul_of_subset hg hK hK.measurableSet Subset.rfl

end Mul

section SMul

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/--
theorem `IntegrableOn.continuousOn_smul_of_subset` / 定理 `IntegrableOn.continuousOn_smul_of_subset`

English:
theorem IntegrableOn.continuousOn_smul_of_subset
  statement: [SecondCountableTopologyEither X 𝕜] {f : X -> 𝕜}
  proof: by
  rcases IsCompact.exists_bound_of_continuousOn hK hf with ⟨C, hC⟩
  exact hg.bdd_smul C ((hf.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

中文:
定理 IntegrableOn.continuousOn_smul_of_subset
  结论: [SecondCountableTopologyEither X 𝕜] {f : X -> 𝕜}
  证明: by
  rcases IsCompact.exists_bound_of_continuousOn hK hf with ⟨C, hC⟩
  exact hg.bdd_smul C ((hf.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

Depends on / 依赖: IsCompact, IsCompact.exists_bound_of_continuousOn, ae_restrict_of_forall_mem, aestronglyMeasurable, bdd_smul, exists_bound_of_continuousOn, hf.mono, hg.bdd_smul
-/
theorem IntegrableOn.continuousOn_smul_of_subset [SecondCountableTopologyEither X 𝕜] {f : X -> 𝕜}
    (hf : ContinuousOn f K) {g : X -> E} (hg : IntegrableOn g A μ)
    (hK : IsCompact K) (hA : MeasurableSet A) (hAK : A subseteq K) :
    IntegrableOn (fun x => f x • g x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hf with ⟨C, hC⟩
  exact hg.bdd_smul C ((hf.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

/--
theorem `IntegrableOn.continuousOn_smul` / 定理 `IntegrableOn.continuousOn_smul`

English:
theorem IntegrableOn.continuousOn_smul
  statement: [T2Space X] [SecondCountableTopologyEither X 𝕜] {g : X -> E}
  proof: hg.continuousOn_smul_of_subset hf hK hK.measurableSet Subset.rfl

中文:
定理 IntegrableOn.continuousOn_smul
  结论: [T2Space X] [SecondCountableTopologyEither X 𝕜] {g : X -> E}
  证明: hg.continuousOn_smul_of_subset hf hK hK.measurableSet Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, continuousOn_smul_of_subset, hK.measurableSet, hg.continuousOn_smul_of_subset, measurableSet
-/
theorem IntegrableOn.continuousOn_smul [T2Space X] [SecondCountableTopologyEither X 𝕜] {g : X -> E}
    (hg : IntegrableOn g K μ) {f : X -> 𝕜} (hf : ContinuousOn f K) (hK : IsCompact K) :
    IntegrableOn (fun x => f x • g x) K μ :=
  hg.continuousOn_smul_of_subset hf hK hK.measurableSet Subset.rfl

/--
theorem `IntegrableOn.smul_continuousOn_of_subset` / 定理 `IntegrableOn.smul_continuousOn_of_subset`

English:
theorem IntegrableOn.smul_continuousOn_of_subset
  statement: [SecondCountableTopologyEither X E] {f : X -> 𝕜}
  proof: by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  exact hf.smul_bdd C ((hg.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

中文:
定理 IntegrableOn.smul_continuousOn_of_subset
  结论: [SecondCountableTopologyEither X E] {f : X -> 𝕜}
  证明: by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  exact hf.smul_bdd C ((hg.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

Depends on / 依赖: IsCompact, IsCompact.exists_bound_of_continuousOn, ae_restrict_of_forall_mem, aestronglyMeasurable, exists_bound_of_continuousOn, hf.smul_bdd, hg.mono, smul_bdd
-/
theorem IntegrableOn.smul_continuousOn_of_subset [SecondCountableTopologyEither X E] {f : X -> 𝕜}
    (hf : IntegrableOn f A μ) {g : X -> E} (hg : ContinuousOn g K)
    (hA : MeasurableSet A) (hK : IsCompact K) (hAK : A subseteq K) :
    IntegrableOn (fun x => f x • g x) A μ := by
  rcases IsCompact.exists_bound_of_continuousOn hK hg with ⟨C, hC⟩
  exact hf.smul_bdd C ((hg.mono hAK).aestronglyMeasurable hA)
    (ae_restrict_of_forall_mem hA fun x hx => hC x (hAK hx))

/--
theorem `IntegrableOn.smul_continuousOn` / 定理 `IntegrableOn.smul_continuousOn`

English:
theorem IntegrableOn.smul_continuousOn
  statement: [T2Space X] [SecondCountableTopologyEither X E] {f : X -> 𝕜}
  proof: hf.smul_continuousOn_of_subset hg hK.measurableSet hK (Subset.refl _)

中文:
定理 IntegrableOn.smul_continuousOn
  结论: [T2Space X] [SecondCountableTopologyEither X E] {f : X -> 𝕜}
  证明: hf.smul_continuousOn_of_subset hg hK.measurableSet hK (Subset.refl _)

Depends on / 依赖: Subset, Subset.refl, hK.measurableSet, hf.smul_continuousOn_of_subset, measurableSet, smul_continuousOn_of_subset
-/
theorem IntegrableOn.smul_continuousOn [T2Space X] [SecondCountableTopologyEither X E] {f : X -> 𝕜}
    (hf : IntegrableOn f K μ) {g : X -> E} (hg : ContinuousOn g K) (hK : IsCompact K) :
    IntegrableOn (fun x => f x • g x) K μ :=
  hf.smul_continuousOn_of_subset hg hK.measurableSet hK (Subset.refl _)

end SMul

namespace LocallyIntegrableOn

/--
theorem `continuousOn_mul` / 定理 `continuousOn_mul`

English:
theorem continuousOn_mul
  statement: [LocallyCompactSpace X] [T2Space X] [NormedRing R]
  proof: by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_mul (hg.mono hk_sub) hk_c

中文:
定理 continuousOn_mul
  结论: [LocallyCompactSpace X] [T2Space X] [NormedRing R]
  证明: by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_mul (hg.mono hk_sub) hk_c

Depends on / 依赖: MeasureTheory, MeasureTheory.locallyIntegrableOn_iff, continuousOn_mul, hg.mono, hk_c, hk_sub, locallyIntegrableOn_iff
-/
theorem continuousOn_mul [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X -> R} {s : Set X} (hf : LocallyIntegrableOn f s μ)
    (hg : ContinuousOn g s) (hs : IsLocallyClosed s) :
    LocallyIntegrableOn (fun x => g x * f x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_mul (hg.mono hk_sub) hk_c

/--
theorem `mul_continuousOn` / 定理 `mul_continuousOn`

English:
theorem mul_continuousOn
  statement: [LocallyCompactSpace X] [T2Space X] [NormedRing R]
  proof: by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).mul_continuousOn (hg.mono hk_sub) hk_c

中文:
定理 mul_continuousOn
  结论: [LocallyCompactSpace X] [T2Space X] [NormedRing R]
  证明: by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).mul_continuousOn (hg.mono hk_sub) hk_c

Depends on / 依赖: MeasureTheory, MeasureTheory.locallyIntegrableOn_iff, hg.mono, hk_c, hk_sub, locallyIntegrableOn_iff, mul_continuousOn
-/
theorem mul_continuousOn [LocallyCompactSpace X] [T2Space X] [NormedRing R]
    [SecondCountableTopologyEither X R] {f g : X -> R} {s : Set X} (hf : LocallyIntegrableOn f s μ)
    (hg : ContinuousOn g s) (hs : IsLocallyClosed s) :
    LocallyIntegrableOn (fun x => f x * g x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).mul_continuousOn (hg.mono hk_sub) hk_c

/--
theorem `continuousOn_smul` / 定理 `continuousOn_smul`

English:
theorem continuousOn_smul
  statement: [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedRing 𝕜]
  proof: by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_smul (hg.mono hk_sub) hk_c

中文:
定理 continuousOn_smul
  结论: [LocallyCompactSpace X] [T2Space X] {𝕜 : 类型} [NormedRing 𝕜]
  证明: by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_smul (hg.mono hk_sub) hk_c

Depends on / 依赖: MeasureTheory, MeasureTheory.locallyIntegrableOn_iff, continuousOn_smul, hg.mono, hk_c, hk_sub, locallyIntegrableOn_iff
-/
theorem continuousOn_smul [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedRing 𝕜]
    [SecondCountableTopologyEither X 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {f : X -> E} {g : X -> 𝕜}
    {s : Set X} (hs : IsLocallyClosed s) (hf : LocallyIntegrableOn f s μ) (hg : ContinuousOn g s) :
    LocallyIntegrableOn (fun x => g x • f x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).continuousOn_smul (hg.mono hk_sub) hk_c

/--
theorem `smul_continuousOn` / 定理 `smul_continuousOn`

English:
theorem smul_continuousOn
  statement: [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedRing 𝕜]
  proof: by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).smul_continuousOn (hg.mono hk_sub) hk_c

中文:
定理 smul_continuousOn
  结论: [LocallyCompactSpace X] [T2Space X] {𝕜 : 类型} [NormedRing 𝕜]
  证明: by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).smul_continuousOn (hg.mono hk_sub) hk_c

Depends on / 依赖: MeasureTheory, MeasureTheory.locallyIntegrableOn_iff, hg.mono, hk_c, hk_sub, locallyIntegrableOn_iff, smul_continuousOn
-/
theorem smul_continuousOn [LocallyCompactSpace X] [T2Space X] {𝕜 : Type*} [NormedRing 𝕜]
    [SecondCountableTopologyEither X E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {f : X -> 𝕜} {g : X -> E}
    {s : Set X} (hs : IsLocallyClosed s) (hf : LocallyIntegrableOn f s μ) (hg : ContinuousOn g s) :
    LocallyIntegrableOn (fun x => f x • g x) s μ := by
  rw [MeasureTheory.locallyIntegrableOn_iff hs] at hf ⊢
  exact fun k hk_sub hk_c => (hf k hk_sub hk_c).smul_continuousOn (hg.mono hk_sub) hk_c

end LocallyIntegrableOn

namespace LocallyIntegrable

variable [LocallyCompactSpace X] [T2Space X] [NormedRing R] [SecondCountableTopologyEither X R]
  {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/--
theorem `continuous_mul` / 定理 `continuous_mul`

English:
theorem continuous_mul
  statement: {f g : X -> R} (hg : Continuous g)
  proof: locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).continuousOn_mul
    hg.continuousOn isOpen_univ.isLocallyClosed)

中文:
定理 continuous_mul
  结论: {f g : X -> R} (hg : Continuous g)
  证明: locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).continuousOn_mul
    hg.continuousOn isOpen_univ.isLocallyClosed)

Depends on / 依赖: continuousOn, continuousOn_mul, hf.locallyIntegrableOn, hg.continuousOn, isLocallyClosed, isOpen_univ, isOpen_univ.isLocallyClosed, locallyIntegrableOn, locallyIntegrableOn_univ
-/
theorem continuous_mul {f g : X -> R} (hg : Continuous g)
    (hf : LocallyIntegrable f μ) : LocallyIntegrable (fun x => g x * f x) μ :=
  locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).continuousOn_mul
    hg.continuousOn isOpen_univ.isLocallyClosed)

/--
theorem `mul_continuous` / 定理 `mul_continuous`

English:
theorem mul_continuous
  statement: {f g : X -> R} (hg : Continuous g)
  proof: locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).mul_continuousOn
    hg.continuousOn isOpen_univ.isLocallyClosed)

中文:
定理 mul_continuous
  结论: {f g : X -> R} (hg : Continuous g)
  证明: locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).mul_continuousOn
    hg.continuousOn isOpen_univ.isLocallyClosed)

Depends on / 依赖: continuousOn, hf.locallyIntegrableOn, hg.continuousOn, isLocallyClosed, isOpen_univ, isOpen_univ.isLocallyClosed, locallyIntegrableOn, locallyIntegrableOn_univ, mul_continuousOn
-/
theorem mul_continuous {f g : X -> R} (hg : Continuous g)
    (hf : LocallyIntegrable f μ) : LocallyIntegrable (fun x => f x * g x) μ :=
  locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).mul_continuousOn
    hg.continuousOn isOpen_univ.isLocallyClosed)

/--
theorem `continuous_smul` / 定理 `continuous_smul`

English:
theorem continuous_smul
  statement: [SecondCountableTopologyEither X 𝕜] {f : X -> E} {g : X -> 𝕜}
  proof: locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).continuousOn_smul
    isOpen_univ.isLocallyClosed hg.continuousOn)

中文:
定理 continuous_smul
  结论: [SecondCountableTopologyEither X 𝕜] {f : X -> E} {g : X -> 𝕜}
  证明: locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).continuousOn_smul
    isOpen_univ.isLocallyClosed hg.continuousOn)

Depends on / 依赖: continuousOn, continuousOn_smul, hf.locallyIntegrableOn, hg.continuousOn, isLocallyClosed, isOpen_univ, isOpen_univ.isLocallyClosed, locallyIntegrableOn, locallyIntegrableOn_univ
-/
theorem continuous_smul [SecondCountableTopologyEither X 𝕜] {f : X -> E} {g : X -> 𝕜}
    (hg : Continuous g) (hf : LocallyIntegrable f μ) : LocallyIntegrable (fun x => g x • f x) μ :=
  locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).continuousOn_smul
    isOpen_univ.isLocallyClosed hg.continuousOn)

/--
theorem `smul_continuous` / 定理 `smul_continuous`

English:
theorem smul_continuous
  statement: [SecondCountableTopologyEither X E] {f : X -> 𝕜} {g : X -> E}
  proof: locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).smul_continuousOn
    isOpen_univ.isLocallyClosed hg.continuousOn)

中文:
定理 smul_continuous
  结论: [SecondCountableTopologyEither X E] {f : X -> 𝕜} {g : X -> E}
  证明: locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).smul_continuousOn
    isOpen_univ.isLocallyClosed hg.continuousOn)

Depends on / 依赖: continuousOn, hf.locallyIntegrableOn, hg.continuousOn, isLocallyClosed, isOpen_univ, isOpen_univ.isLocallyClosed, locallyIntegrableOn, locallyIntegrableOn_univ, smul_continuousOn
-/
theorem smul_continuous [SecondCountableTopologyEither X E] {f : X -> 𝕜} {g : X -> E}
    (hg : Continuous g) (hf : LocallyIntegrable f μ) : LocallyIntegrable (fun x => f x • g x) μ :=
  locallyIntegrableOn_univ.1 ((hf.locallyIntegrableOn univ).smul_continuousOn
    isOpen_univ.isLocallyClosed hg.continuousOn)

end LocallyIntegrable

end MeasureTheory
