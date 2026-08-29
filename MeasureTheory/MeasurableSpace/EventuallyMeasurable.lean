/-
Copyright (c) 2024 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Order.Filter.CountableInter

/-!
# Measurability modulo a filter

In this file we consider the general notion of measurability modulo a σ-filter.
Two important instances of this construction are null-measurability with respect to a measure,
where the filter is the collection of co-null sets, and
Baire-measurability with respect to a topology,
where the filter is the collection of comeager (residual) sets.
(not to be confused with measurability with respect to the sigma algebra
of Baire sets, which is sometimes also called this.)
TODO: Implement the latter.

## Main definitions

* `eventuallyMeasurableSpace`: A `MeasurableSpace` on a type `α` consisting of sets which are
  `Filter.EventuallyEq` to a measurable set with respect to a given `CountableInterFilter` on `α`
  and `MeasurableSpace` on `α`.
* `EventuallyMeasurableSet`: A `Prop` for sets which are measurable with respect to some
  `eventuallyMeasurableSpace`.
* `EventuallyMeasurable`: A `Prop` for functions which are measurable with respect to some
  `eventuallyMeasurableSpace` on the domain.

-/

@[expose] public section

open Filter Set MeasurableSpace

variable {α : Type*} (m : MeasurableSpace α) {s t : Set α}

/-- The `MeasurableSpace` of sets which are measurable with respect to a given σ-algebra `m`
on `α`, modulo a given σ-filter `l` on `α`. -/
@[instance_reducible]
/--
Definition of `eventuallyMeasurableSpace` / `eventuallyMeasurableSpace` 的定义

English:
definition eventuallyMeasurableSpace
  signature: (l : Filter α) [CountableInterFilter l]
  body: exists t, MeasurableSet t ∧ s =ᶠ[l] t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, EventuallyEq.refl _ _ ⟩
  measurableSet_compl := fun _ ⟨t, ht, hts⟩ => ⟨tᶜ, ht.compl, hts.compl⟩
  measurableSet_iUnion s hs := by
    choose t ht hts using hs
    exact ⟨⋃ i, t i, MeasurableSet.iUnion ht, .count

中文:
定义 eventuallyMeasurableSpace
  签名: (l : Filter α) [Countable整数erFilter l]
  定义体: exists t, MeasurableSet t ∧ s =ᶠ[l] t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, EventuallyEq.refl _ _ ⟩
  measurableSet_compl := fun _ ⟨t, ht, hts⟩ => ⟨tᶜ, ht.compl, hts.compl⟩
  measurableSet_iUnion s hs := by
    choose t ht hts using hs
    exact ⟨⋃ i, t i, MeasurableSet.iUnion ht, .count

Depends on / 依赖: MeasurableSet
-/
def eventuallyMeasurableSpace (l : Filter α) [CountableInterFilter l] : MeasurableSpace α where
  MeasurableSet' s := exists t, MeasurableSet t ∧ s =ᶠ[l] t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, EventuallyEq.refl _ _ ⟩
  measurableSet_compl := fun _ ⟨t, ht, hts⟩ => ⟨tᶜ, ht.compl, hts.compl⟩
  measurableSet_iUnion s hs := by
    choose t ht hts using hs
    exact ⟨⋃ i, t i, MeasurableSet.iUnion ht, .countable_iUnion hts⟩

/--
Definition of `EventuallyMeasurableSet` / `EventuallyMeasurableSet` 的定义

English:
definition EventuallyMeasurableSet
  signature: (l : Filter α) [CountableInterFilter l] (s : Set α)
  body: @MeasurableSet _ (eventuallyMeasurableSpace m l) s

中文:
定义 EventuallyMeasurableSet
  签名: (l : Filter α) [Countable整数erFilter l] (s : Set α)
  定义体: @MeasurableSet _ (eventuallyMeasurableSpace m l) s

Depends on / 依赖: MeasurableSet, eventuallyMeasurableSpace
-/
def EventuallyMeasurableSet (l : Filter α) [CountableInterFilter l] (s : Set α) : Prop :=
  @MeasurableSet _ (eventuallyMeasurableSpace m l) s

variable {l : Filter α} [CountableInterFilter l]
variable {m}

/--
theorem `MeasurableSet.eventuallyMeasurableSet` / 定理 `MeasurableSet.eventuallyMeasurableSet`

English:
theorem MeasurableSet.eventuallyMeasurableSet
  given: (hs : MeasurableSet s)
  proof: ⟨s, hs, EventuallyEq.refl _ _⟩

中文:
定理 MeasurableSet.eventuallyMeasurableSet
  条件: (hs : MeasurableSet s)
  证明: ⟨s, hs, EventuallyEq.refl _ _⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.refl
-/
theorem MeasurableSet.eventuallyMeasurableSet (hs : MeasurableSet s) :
    EventuallyMeasurableSet m l s :=
  ⟨s, hs, EventuallyEq.refl _ _⟩

/--
theorem `le_eventuallyMeasurableSpace` / 定理 `le_eventuallyMeasurableSpace`

English:
theorem le_eventuallyMeasurableSpace
  statement: m <= eventuallyMeasurableSpace m l
  proof: fun _ hs => hs.eventuallyMeasurableSet

中文:
定理 le_eventuallyMeasurableSpace
  结论: m <= eventuallyMeasurableSpace m l
  证明: fun _ hs => hs.eventuallyMeasurableSet

Depends on / 依赖: eventuallyMeasurableSet, hs.eventuallyMeasurableSet
-/
theorem le_eventuallyMeasurableSpace : m <= eventuallyMeasurableSpace m l :=
  fun _ hs => hs.eventuallyMeasurableSet

/--
theorem `eventuallyMeasurableSet_of_mem_filter` / 定理 `eventuallyMeasurableSet_of_mem_filter`

English:
theorem eventuallyMeasurableSet_of_mem_filter
  given: (hs : s in l)
  statement: EventuallyMeasurableSet m l s
  proof: ⟨univ, MeasurableSet.univ, eventuallyEq_univ.mpr hs⟩

中文:
定理 eventuallyMeasurableSet_of_mem_filter
  条件: (hs : s in l)
  结论: EventuallyMeasurableSet m l s
  证明: ⟨univ, MeasurableSet.univ, eventuallyEq_univ.mpr hs⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, eventuallyEq_univ, eventuallyEq_univ.mpr
-/
theorem eventuallyMeasurableSet_of_mem_filter (hs : s in l) : EventuallyMeasurableSet m l s :=
  ⟨univ, MeasurableSet.univ, eventuallyEq_univ.mpr hs⟩

/--
theorem `EventuallyMeasurableSet.congr` / 定理 `EventuallyMeasurableSet.congr`

English:
theorem EventuallyMeasurableSet.congr
  proof: by
  rcases ht with ⟨t', ht', htt'⟩
  exact ⟨t', ht', hst.trans htt'⟩

中文:
定理 EventuallyMeasurableSet.congr
  证明: by
  rcases ht with ⟨t', ht', htt'⟩
  exact ⟨t', ht', hst.trans htt'⟩

Depends on / 依赖: hst.trans
-/
theorem EventuallyMeasurableSet.congr
    (ht : EventuallyMeasurableSet m l t) (hst : s =ᶠ[l] t) : EventuallyMeasurableSet m l s := by
  rcases ht with ⟨t', ht', htt'⟩
  exact ⟨t', ht', hst.trans htt'⟩

section instances

/--
Instance `eventuallyMeasurableSingleton` / 实例 `eventuallyMeasurableSingleton`

English:
instance eventuallyMeasurableSingleton
  signature: [MeasurableSingletonClass α]
  body: @MeasurableSingletonClass.mk _ (_) fun x => (MeasurableSet.singleton x).eventuallyMeasurableSet

中文:
实例 eventuallyMeasurableSingleton
  签名: [MeasurableSingletonClass α]
  定义体: @MeasurableSingletonClass.mk _ (_) fun x => (MeasurableSet.singleton x).eventuallyMeasurableSet

Depends on / 依赖: MeasurableSet, MeasurableSet.singleton, MeasurableSingletonClass, MeasurableSingletonClass.mk, eventuallyMeasurableSet, singleton
-/
instance eventuallyMeasurableSingleton [MeasurableSingletonClass α] :
    @MeasurableSingletonClass α (eventuallyMeasurableSpace m l) :=
@MeasurableSingletonClass.mk _ (_) fun x => (MeasurableSet.singleton x).eventuallyMeasurableSet

end instances

section EventuallyMeasurable

open Function

variable (m l) {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]

/--
Definition of `EventuallyMeasurable` / `EventuallyMeasurable` 的定义

English:
definition EventuallyMeasurable
  signature: (f : α -> β)
  body: @Measurable _ _ (eventuallyMeasurableSpace m l) _ f

中文:
定义 EventuallyMeasurable
  签名: (f : α -> β)
  定义体: @Measurable _ _ (eventuallyMeasurableSpace m l) _ f

Depends on / 依赖: Measurable, eventuallyMeasurableSpace
-/
def EventuallyMeasurable (f : α -> β) : Prop := @Measurable _ _ (eventuallyMeasurableSpace m l) _ f

variable {m l} {f g : α -> β} {h : β -> γ}

/--
theorem `Measurable.eventuallyMeasurable` / 定理 `Measurable.eventuallyMeasurable`

English:
theorem Measurable.eventuallyMeasurable
  given: (hf : Measurable f)
  statement: EventuallyMeasurable m l f
  proof: hf.le le_eventuallyMeasurableSpace

中文:
定理 Measurable.eventuallyMeasurable
  条件: (hf : Measurable f)
  结论: EventuallyMeasurable m l f
  证明: hf.le le_eventuallyMeasurableSpace

Depends on / 依赖: hf.le, le_eventuallyMeasurableSpace
-/
theorem Measurable.eventuallyMeasurable (hf : Measurable f) : EventuallyMeasurable m l f :=
  hf.le le_eventuallyMeasurableSpace

/--
theorem `Measurable.comp_eventuallyMeasurable` / 定理 `Measurable.comp_eventuallyMeasurable`

English:
theorem Measurable.comp_eventuallyMeasurable
  given: (hh : Measurable h) (hf : EventuallyMeasurable m l f)
  proof: hh.comp hf

中文:
定理 Measurable.comp_eventuallyMeasurable
  条件: (hh : Measurable h) (hf : EventuallyMeasurable m l f)
  证明: hh.comp hf

Depends on / 依赖: hh.comp
-/
theorem Measurable.comp_eventuallyMeasurable (hh : Measurable h) (hf : EventuallyMeasurable m l f) :
    EventuallyMeasurable m l (h ∘ f) :=
  hh.comp hf

/--
theorem `EventuallyMeasurable.congr` / 定理 `EventuallyMeasurable.congr`

English:
theorem EventuallyMeasurable.congr
  proof: fun _ hs => EventuallyMeasurableSet.congr (hf hs)
    (hgf.preimage _)

中文:
定理 EventuallyMeasurable.congr
  证明: fun _ hs => EventuallyMeasurableSet.congr (hf hs)
    (hgf.preimage _)

Depends on / 依赖: EventuallyMeasurableSet, EventuallyMeasurableSet.congr, hgf.preimage, preimage
-/
theorem EventuallyMeasurable.congr
    (hf : EventuallyMeasurable m l f) (hgf : g =ᶠ[l] f) : EventuallyMeasurable m l g :=
  fun _ hs => EventuallyMeasurableSet.congr (hf hs)
    (hgf.preimage _)

/--
theorem `Measurable.eventuallyMeasurable_of_eventuallyEq` / 定理 `Measurable.eventuallyMeasurable_of_eventuallyEq`

English:
theorem Measurable.eventuallyMeasurable_of_eventuallyEq
  proof: hf.eventuallyMeasurable.congr hgf

中文:
定理 Measurable.eventuallyMeasurable_of_eventuallyEq
  证明: hf.eventuallyMeasurable.congr hgf

Depends on / 依赖: eventuallyMeasurable, hf.eventuallyMeasurable.congr
-/
theorem Measurable.eventuallyMeasurable_of_eventuallyEq
    (hf : Measurable f) (hgf : g =ᶠ[l] f) : EventuallyMeasurable m l g :=
  hf.eventuallyMeasurable.congr hgf

end EventuallyMeasurable
