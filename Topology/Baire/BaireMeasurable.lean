/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
module

public import Mathlib.Topology.LocallyClosed
public import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Baire category and Baire measurable sets

This file defines some of the basic notions of Baire category and Baire measurable sets.

## Main definitions

First, we define the notation `=ᵇ`. This denotes eventual equality with respect to the filter of
`residual` sets in a topological space.

A set `s` in a topological space `α` is called a `BaireMeasurableSet` or said to have the
*property of Baire* if it satisfies either of the following equivalent conditions:

* There is a *Borel* set `u` such that `s =ᵇ u`. (This is our definition)
* There is an *open* set `u` such that `s =ᵇ u`. (See `BaireMeasurableSet.residual_eq_open`)

-/

@[expose] public section

variable (α : Type*) {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

open Topology

/-- Notation for `=ᶠ[residual _]`. That is, eventual equality with respect to
the filter of residual sets.
In lemma names, this is called `residualEq`. -/
scoped[Topology] notation:50 f " =ᵇ " g:50 => Filter.EventuallyEq (residual _) f g

/-- Notation to say that a property of points in a topological space holds
almost everywhere in the sense of Baire category. That is, on a residual set. -/
scoped[Topology] notation3 "forallᵇ " (...) ", " r:(scoped p => Filter.Eventually p <| residual _) => r

/-- Notation to say that a property of points in a topological space holds on a nonmeager set. -/
scoped[Topology] notation3 "existsᵇ " (...) ", " r:(scoped p => Filter.Frequently p <| residual _) => r

variable {α}

/--
theorem `coborder_mem_residual` / 定理 `coborder_mem_residual`

English:
theorem coborder_mem_residual
  given: {s : Set α} (hs : IsLocallyClosed s)
  statement: coborder s in residual α
  proof: residual_of_dense_open hs.isOpen_coborder dense_coborder

中文:
定理 coborder_mem_residual
  条件: {s : Set α} (hs : IsLocallyClosed s)
  结论: coborder s in residual α
  证明: residual_of_dense_open hs.isOpen_coborder dense_coborder

Depends on / 依赖: dense_coborder, hs.isOpen_coborder, isOpen_coborder, residual_of_dense_open
-/
theorem coborder_mem_residual {s : Set α} (hs : IsLocallyClosed s) : coborder s in residual α :=
  residual_of_dense_open hs.isOpen_coborder dense_coborder

/--
theorem `closure_residualEq` / 定理 `closure_residualEq`

English:
theorem closure_residualEq
  given: {s : Set α} (hs : IsLocallyClosed s)
  statement: closure s =ᵇ s
  proof: by
  rw [Filter.eventuallyEq_set]
  filter_upwards [coborder_mem_residual hs] with x hx
  nth_rewrite 2 [← closure_inter_coborder (s := s)]
  simp [hx]

中文:
定理 closure_residualEq
  条件: {s : Set α} (hs : IsLocallyClosed s)
  结论: closure s =ᵇ s
  证明: by
  rw [Filter.eventuallyEq_set]
  filter_upwards [coborder_mem_residual hs] with x hx
  nth_rewrite 2 [← closure_inter_coborder (s := s)]
  simp [hx]

Depends on / 依赖: Filter, Filter.eventuallyEq_set, closure_inter_coborder, coborder_mem_residual, eventuallyEq_set, filter_upwards, nth_rewrite
-/
theorem closure_residualEq {s : Set α} (hs : IsLocallyClosed s) : closure s =ᵇ s := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [coborder_mem_residual hs] with x hx
  nth_rewrite 2 [← closure_inter_coborder (s := s)]
  simp [hx]

/--
Definition of `BaireMeasurableSet` / `BaireMeasurableSet` 的定义

English:
definition BaireMeasurableSet
  signature: (s : Set α)
  body: @MeasurableSet _ (eventuallyMeasurableSpace (borel _) (residual _)) s

中文:
定义 BaireMeasurableSet
  签名: (s : Set α)
  定义体: @MeasurableSet _ (eventuallyMeasurableSpace (borel _) (residual _)) s

Depends on / 依赖: MeasurableSet, eventuallyMeasurableSpace, residual
-/
def BaireMeasurableSet (s : Set α) : Prop :=
  @MeasurableSet _ (eventuallyMeasurableSpace (borel _) (residual _)) s

variable {s t : Set α}

namespace BaireMeasurableSet

/--
theorem `of_mem_residual` / 定理 `of_mem_residual`

English:
theorem of_mem_residual
  given: (h : s in residual _)
  statement: BaireMeasurableSet s
  proof: eventuallyMeasurableSet_of_mem_filter (α := α) h

中文:
定理 of_mem_residual
  条件: (h : s in residual _)
  结论: BaireMeasurableSet s
  证明: eventuallyMeasurableSet_of_mem_filter (α := α) h

Depends on / 依赖: eventuallyMeasurableSet_of_mem_filter
-/
theorem of_mem_residual (h : s in residual _) : BaireMeasurableSet s :=
  eventuallyMeasurableSet_of_mem_filter (α := α) h

/--
theorem `_root_.MeasurableSet.baireMeasurableSet` / 定理 `_root_.MeasurableSet.baireMeasurableSet`

English:
theorem _root_.MeasurableSet.baireMeasurableSet
  statement: [MeasurableSpace α] [BorelSpace α]
  proof: by
  borelize α
  exact h.eventuallyMeasurableSet

中文:
定理 _root_.MeasurableSet.baireMeasurableSet
  结论: [MeasurableSpace α] [BorelSpace α]
  证明: by
  borelize α
  exact h.eventuallyMeasurableSet

Depends on / 依赖: borelize, eventuallyMeasurableSet, h.eventuallyMeasurableSet
-/
theorem _root_.MeasurableSet.baireMeasurableSet [MeasurableSpace α] [BorelSpace α]
    (h : MeasurableSet s) : BaireMeasurableSet s := by
  borelize α
  exact h.eventuallyMeasurableSet

/--
theorem `_root_.IsOpen.baireMeasurableSet` / 定理 `_root_.IsOpen.baireMeasurableSet`

English:
theorem _root_.IsOpen.baireMeasurableSet
  given: (h : IsOpen s)
  statement: BaireMeasurableSet s
  proof: by
  borelize α
  exact h.measurableSet.baireMeasurableSet

中文:
定理 _root_.IsOpen.baireMeasurableSet
  条件: (h : IsOpen s)
  结论: BaireMeasurableSet s
  证明: by
  borelize α
  exact h.measurableSet.baireMeasurableSet

Depends on / 依赖: baireMeasurableSet, borelize, h.measurableSet.baireMeasurableSet, measurableSet
-/
theorem _root_.IsOpen.baireMeasurableSet (h : IsOpen s) : BaireMeasurableSet s := by
  borelize α
  exact h.measurableSet.baireMeasurableSet

/--
theorem `compl` / 定理 `compl`

English:
theorem compl
  given: (h : BaireMeasurableSet s)
  statement: BaireMeasurableSet sᶜ
  proof: MeasurableSet.compl h

中文:
定理 compl
  条件: (h : BaireMeasurableSet s)
  结论: BaireMeasurableSet sᶜ
  证明: MeasurableSet.compl h

Depends on / 依赖: MeasurableSet, MeasurableSet.compl
-/
theorem compl (h : BaireMeasurableSet s) : BaireMeasurableSet sᶜ := MeasurableSet.compl h

/--
theorem `of_compl` / 定理 `of_compl`

English:
theorem of_compl
  given: (h : BaireMeasurableSet sᶜ)
  statement: BaireMeasurableSet s
  proof: MeasurableSet.of_compl h

中文:
定理 of_compl
  条件: (h : BaireMeasurableSet sᶜ)
  结论: BaireMeasurableSet s
  证明: MeasurableSet.of_compl h

Depends on / 依赖: MeasurableSet, MeasurableSet.of_compl, of_compl
-/
theorem of_compl (h : BaireMeasurableSet sᶜ) : BaireMeasurableSet s := MeasurableSet.of_compl h

/--
theorem `_root_.IsMeagre.baireMeasurableSet` / 定理 `_root_.IsMeagre.baireMeasurableSet`

English:
theorem _root_.IsMeagre.baireMeasurableSet
  given: (h : IsMeagre s)
  statement: BaireMeasurableSet s
  proof: (of_mem_residual h).of_compl

中文:
定理 _root_.IsMeagre.baireMeasurableSet
  条件: (h : IsMeagre s)
  结论: BaireMeasurableSet s
  证明: (of_mem_residual h).of_compl

Depends on / 依赖: of_compl, of_mem_residual
-/
theorem _root_.IsMeagre.baireMeasurableSet (h : IsMeagre s) : BaireMeasurableSet s :=
  (of_mem_residual h).of_compl

/--
theorem `iUnion` / 定理 `iUnion`

English:
theorem iUnion
  statement: {ι : Sort*} [Countable ι] {s : ι -> Set α}
  proof: MeasurableSet.iUnion h

中文:
定理 iUnion
  结论: {ι : Sort*} [Countable ι] {s : ι -> Set α}
  证明: MeasurableSet.iUnion h

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, iUnion
-/
theorem iUnion {ι : Sort*} [Countable ι] {s : ι -> Set α}
    (h : forall i, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋃ i, s i) :=
  MeasurableSet.iUnion h

/--
theorem `biUnion` / 定理 `biUnion`

English:
theorem biUnion
  statement: {ι : Type*} {s : ι -> Set α} {t : Set ι} (ht : t.Countable)
  proof: MeasurableSet.biUnion ht h

中文:
定理 biUnion
  结论: {ι : 类型} {s : ι -> Set α} {t : Set ι} (ht : t.Countable)
  证明: MeasurableSet.biUnion ht h

Depends on / 依赖: MeasurableSet, MeasurableSet.biUnion, biUnion
-/
theorem biUnion {ι : Type*} {s : ι -> Set α} {t : Set ι} (ht : t.Countable)
    (h : forall i in t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋃ i in t, s i) :=
  MeasurableSet.biUnion ht h

/--
theorem `sUnion` / 定理 `sUnion`

English:
theorem sUnion
  statement: {s : Set (Set α)} (hs : s.Countable)
  proof: MeasurableSet.sUnion hs h

中文:
定理 sUnion
  结论: {s : Set (Set α)} (hs : s.Countable)
  证明: MeasurableSet.sUnion hs h

Depends on / 依赖: MeasurableSet, MeasurableSet.sUnion, sUnion
-/
theorem sUnion {s : Set (Set α)} (hs : s.Countable)
    (h : forall t in s, BaireMeasurableSet t) : BaireMeasurableSet (⋃₀ s) :=
  MeasurableSet.sUnion hs h

/--
theorem `iInter` / 定理 `iInter`

English:
theorem iInter
  statement: {ι : Sort*} [Countable ι] {s : ι -> Set α}
  proof: MeasurableSet.iInter h

中文:
定理 iInter
  结论: {ι : Sort*} [Countable ι] {s : ι -> Set α}
  证明: MeasurableSet.iInter h

Depends on / 依赖: MeasurableSet, MeasurableSet.iInter, iInter
-/
theorem iInter {ι : Sort*} [Countable ι] {s : ι -> Set α}
    (h : forall i, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋂ i, s i) :=
  MeasurableSet.iInter h

/--
theorem `biInter` / 定理 `biInter`

English:
theorem biInter
  statement: {ι : Type*} {s : ι -> Set α} {t : Set ι} (ht : t.Countable)
  proof: MeasurableSet.biInter ht h

中文:
定理 biInter
  结论: {ι : 类型} {s : ι -> Set α} {t : Set ι} (ht : t.Countable)
  证明: MeasurableSet.biInter ht h

Depends on / 依赖: MeasurableSet, MeasurableSet.biInter, biInter
-/
theorem biInter {ι : Type*} {s : ι -> Set α} {t : Set ι} (ht : t.Countable)
    (h : forall i in t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋂ i in t, s i) :=
  MeasurableSet.biInter ht h

/--
theorem `sInter` / 定理 `sInter`

English:
theorem sInter
  statement: {s : Set (Set α)} (hs : s.Countable)
  proof: MeasurableSet.sInter hs h

中文:
定理 sInter
  结论: {s : Set (Set α)} (hs : s.Countable)
  证明: MeasurableSet.sInter hs h

Depends on / 依赖: MeasurableSet, MeasurableSet.sInter, sInter
-/
theorem sInter {s : Set (Set α)} (hs : s.Countable)
    (h : forall t in s, BaireMeasurableSet t) : BaireMeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs h

/--
theorem `union` / 定理 `union`

English:
theorem union
  given: (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t)
  proof: MeasurableSet.union hs ht

中文:
定理 union
  条件: (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t)
  证明: MeasurableSet.union hs ht

Depends on / 依赖: MeasurableSet, MeasurableSet.union
-/
theorem union (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s union t) :=
  MeasurableSet.union hs ht

/--
theorem `inter` / 定理 `inter`

English:
theorem inter
  given: (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t)
  proof: MeasurableSet.inter hs ht

中文:
定理 inter
  条件: (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t)
  证明: MeasurableSet.inter hs ht

Depends on / 依赖: MeasurableSet, MeasurableSet.inter
-/
theorem inter (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s inter t) :=
  MeasurableSet.inter hs ht

/--
theorem `diff` / 定理 `diff`

English:
theorem diff
  given: (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t)
  proof: MeasurableSet.diff hs ht

中文:
定理 diff
  条件: (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t)
  证明: MeasurableSet.diff hs ht

Depends on / 依赖: MeasurableSet, MeasurableSet.diff
-/
theorem diff (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s \ t) :=
  MeasurableSet.diff hs ht

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: (hs : BaireMeasurableSet s) (h : s =ᵇ t)
  statement: BaireMeasurableSet t
  proof: EventuallyMeasurableSet.congr (α := α) hs h.symm

中文:
定理 congr
  条件: (hs : BaireMeasurableSet s) (h : s =ᵇ t)
  结论: BaireMeasurableSet t
  证明: EventuallyMeasurableSet.congr (α := α) hs h.symm

Depends on / 依赖: EventuallyMeasurableSet, EventuallyMeasurableSet.congr, h.symm
-/
theorem congr (hs : BaireMeasurableSet s) (h : s =ᵇ t) : BaireMeasurableSet t :=
  EventuallyMeasurableSet.congr (α := α) hs h.symm

end BaireMeasurableSet

open Filter

/--
theorem `MeasurableSet.residualEq_isOpen` / 定理 `MeasurableSet.residualEq_isOpen`

English:
theorem MeasurableSet.residualEq_isOpen
  given: [MeasurableSpace α] [BorelSpace α] (h : MeasurableSet s)
  proof: by
  induction s, h using MeasurableSet.induction_on_open with
  | isOpen U hU => exact ⟨U, hU, .rfl⟩
  | compl s _ ihs =>
    obtain ⟨U, Uo, hsU⟩ := ihs
    use (closure U)ᶜ, isClosed_closure.isOpen_compl
exact .compl hsU.trans .symm closure_residualEq Uo.isLocallyClosed
  | iUnion f _ _ ihf =>
   

中文:
定理 MeasurableSet.residualEq_isOpen
  条件: [MeasurableSpace α] [BorelSpace α] (h : MeasurableSet s)
  证明: by
  induction s, h using MeasurableSet.induction_on_open with
  | isOpen U hU => exact ⟨U, hU, .rfl⟩
  | compl s _ ihs =>
    obtain ⟨U, Uo, hsU⟩ := ihs
    use (closure U)ᶜ, isClosed_closure.isOpen_compl
exact .compl hsU.trans .symm closure_residualEq Uo.isLocallyClosed
  | iUnion f _ _ ihf =>
   

Depends on / 依赖: MeasurableSet, MeasurableSet.induction_on_open, Uo.isLocallyClosed, closure, closure_residualEq, countable_iUnion, hsU.trans, iUnion, induction_on_open, isClosed_closure, isClosed_closure.isOpen_compl, isLocallyClosed, isOpen, isOpen_compl, isOpen_iUnion
-/
theorem MeasurableSet.residualEq_isOpen [MeasurableSpace α] [BorelSpace α] (h : MeasurableSet s) :
    exists u : Set α, IsOpen u ∧ s =ᵇ u := by
  induction s, h using MeasurableSet.induction_on_open with
  | isOpen U hU => exact ⟨U, hU, .rfl⟩
  | compl s _ ihs =>
    obtain ⟨U, Uo, hsU⟩ := ihs
    use (closure U)ᶜ, isClosed_closure.isOpen_compl
exact .compl hsU.trans .symm closure_residualEq Uo.isLocallyClosed
  | iUnion f _ _ ihf =>
    choose u uo su using ihf
    exact ⟨⋃ i, u i, isOpen_iUnion uo, .countable_iUnion su⟩

/--
theorem `BaireMeasurableSet.residualEq_isOpen` / 定理 `BaireMeasurableSet.residualEq_isOpen`

English:
theorem BaireMeasurableSet.residualEq_isOpen
  given: (h : BaireMeasurableSet s)
  proof: by
  borelize α
  rcases h with ⟨t, ht, hst⟩
  rcases ht.residualEq_isOpen with ⟨u, hu, htu⟩
  exact ⟨u, hu, hst.trans htu⟩

中文:
定理 BaireMeasurableSet.residualEq_isOpen
  条件: (h : BaireMeasurableSet s)
  证明: by
  borelize α
  rcases h with ⟨t, ht, hst⟩
  rcases ht.residualEq_isOpen with ⟨u, hu, htu⟩
  exact ⟨u, hu, hst.trans htu⟩

Depends on / 依赖: borelize, hst.trans, ht.residualEq_isOpen, residualEq_isOpen
-/
theorem BaireMeasurableSet.residualEq_isOpen (h : BaireMeasurableSet s) :
    exists u : Set α, (IsOpen u) ∧ s =ᵇ u := by
  borelize α
  rcases h with ⟨t, ht, hst⟩
  rcases ht.residualEq_isOpen with ⟨u, hu, htu⟩
  exact ⟨u, hu, hst.trans htu⟩

/--
theorem `BaireMeasurableSet.iff_residualEq_isOpen` / 定理 `BaireMeasurableSet.iff_residualEq_isOpen`

English:
theorem BaireMeasurableSet.iff_residualEq_isOpen
  proof: ⟨fun h => h.residualEq_isOpen, fun ⟨_, uo, ueq⟩ => uo.baireMeasurableSet.congr ueq.symm⟩

中文:
定理 BaireMeasurableSet.iff_residualEq_isOpen
  证明: ⟨fun h => h.residualEq_isOpen, fun ⟨_, uo, ueq⟩ => uo.baireMeasurableSet.congr ueq.symm⟩

Depends on / 依赖: baireMeasurableSet, h.residualEq_isOpen, residualEq_isOpen, ueq.symm, uo.baireMeasurableSet.congr
-/
theorem BaireMeasurableSet.iff_residualEq_isOpen :
    BaireMeasurableSet s ↔ exists u : Set α, (IsOpen u) ∧ s =ᵇ u :=
  ⟨fun h => h.residualEq_isOpen, fun ⟨_, uo, ueq⟩ => uo.baireMeasurableSet.congr ueq.symm⟩

section Map

open Set

variable {f : α -> β}

/--
theorem `tendsto_residual_of_isOpenMap` / 定理 `tendsto_residual_of_isOpenMap`

English:
theorem tendsto_residual_of_isOpenMap
  given: (hc : Continuous f) (ho : IsOpenMap f)
  proof: by
  apply le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro t ⟨ht, htd⟩
  exact residual_of_dense_open (ht.preimage hc) (htd.preimage ho)

中文:
定理 tendsto_residual_of_isOpenMap
  条件: (hc : Continuous f) (ho : IsOpenMap f)
  证明: by
  apply le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro t ⟨ht, htd⟩
  exact residual_of_dense_open (ht.preimage hc) (htd.preimage ho)

Depends on / 依赖: ht.preimage, htd.preimage, le_countableGenerate_iff_of_countableInterFilter, le_countableGenerate_iff_of_countableInterFilter.mpr, preimage, residual_of_dense_open
-/
theorem tendsto_residual_of_isOpenMap (hc : Continuous f) (ho : IsOpenMap f) :
    Tendsto f (residual α) (residual β) := by
  apply le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro t ⟨ht, htd⟩
  exact residual_of_dense_open (ht.preimage hc) (htd.preimage ho)

/--
theorem `IsMeagre.preimage_of_isOpenMap` / 定理 `IsMeagre.preimage_of_isOpenMap`

English:
theorem IsMeagre.preimage_of_isOpenMap
  statement: (hc : Continuous f) (ho : IsOpenMap f)
  proof: tendsto_residual_of_isOpenMap hc ho h

中文:
定理 IsMeagre.preimage_of_isOpenMap
  结论: (hc : Continuous f) (ho : IsOpenMap f)
  证明: tendsto_residual_of_isOpenMap hc ho h

Depends on / 依赖: tendsto_residual_of_isOpenMap
-/
theorem IsMeagre.preimage_of_isOpenMap (hc : Continuous f) (ho : IsOpenMap f)
    {s : Set β} (h : IsMeagre s) : IsMeagre (f ⁻¹' s) :=
  tendsto_residual_of_isOpenMap hc ho h

/--
theorem `BaireMeasurableSet.preimage` / 定理 `BaireMeasurableSet.preimage`

English:
theorem BaireMeasurableSet.preimage
  statement: (hc : Continuous f) (ho : IsOpenMap f)
  proof: by
  rcases h with ⟨u, hu, hsu⟩
refine ⟨f ⁻¹' u, ?_, hsu.filter_mono tendsto_residual_of_isOpenMap hc ho⟩
  borelize α β
  exact hc.measurable hu

中文:
定理 BaireMeasurableSet.preimage
  结论: (hc : Continuous f) (ho : IsOpenMap f)
  证明: by
  rcases h with ⟨u, hu, hsu⟩
refine ⟨f ⁻¹' u, ?_, hsu.filter_mono tendsto_residual_of_isOpenMap hc ho⟩
  borelize α β
  exact hc.measurable hu

Depends on / 依赖: borelize, filter_mono, hc.measurable, hsu.filter_mono, measurable, tendsto_residual_of_isOpenMap
-/
theorem BaireMeasurableSet.preimage (hc : Continuous f) (ho : IsOpenMap f)
    {s : Set β} (h : BaireMeasurableSet s) : BaireMeasurableSet (f ⁻¹' s) := by
  rcases h with ⟨u, hu, hsu⟩
refine ⟨f ⁻¹' u, ?_, hsu.filter_mono tendsto_residual_of_isOpenMap hc ho⟩
  borelize α β
  exact hc.measurable hu

/--
theorem `Homeomorph.residual_map_eq` / 定理 `Homeomorph.residual_map_eq`

English:
theorem Homeomorph.residual_map_eq
  given: (h : α ≃ₜ β)
  statement: (residual α).map h = residual β
  proof: by
  refine le_antisymm (tendsto_residual_of_isOpenMap h.continuous h.isOpenMap) (le_map ?_)
  simp_rw [← preimage_symm]
  exact tendsto_residual_of_isOpenMap h.symm.continuous h.symm.isOpenMap

中文:
定理 Homeomorph.residual_map_eq
  条件: (h : α ≃ₜ β)
  结论: (residual α).map h = residual β
  证明: by
  refine le_antisymm (tendsto_residual_of_isOpenMap h.continuous h.isOpenMap) (le_map ?_)
  simp_rw [← preimage_symm]
  exact tendsto_residual_of_isOpenMap h.symm.continuous h.symm.isOpenMap

Depends on / 依赖: continuous, h.continuous, h.isOpenMap, h.symm.continuous, h.symm.isOpenMap, isOpenMap, le_antisymm, le_map, preimage_symm, simp_rw, tendsto_residual_of_isOpenMap
-/
theorem Homeomorph.residual_map_eq (h : α ≃ₜ β) : (residual α).map h = residual β := by
  refine le_antisymm (tendsto_residual_of_isOpenMap h.continuous h.isOpenMap) (le_map ?_)
  simp_rw [← preimage_symm]
  exact tendsto_residual_of_isOpenMap h.symm.continuous h.symm.isOpenMap

end Map
