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
/-
**eventuallyMeasurableSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：eventuallyMeasurableSpace (l : Filter α) [CountableInterFilter l] : Measur
ableSpace α where MeasurableSet' s
参数：l : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MeasurableSpace` of sets which are measurable with respect to a given σ-alg
ebra `m`
on `α`, modulo a given σ-filter `l` on `α`.
-/
def eventuallyMeasurableSpace (l : Filter α) [CountableInterFilter l] : MeasurableSpace α where
  MeasurableSet' s := ∃ t, MeasurableSet t ∧ s =ᶠ[l] t
  measurableSet_empty := ⟨∅, MeasurableSet.empty, EventuallyEq.refl _ _ ⟩
  measurableSet_compl := fun _ ⟨t, ht, hts⟩ => ⟨tᶜ, ht.compl, hts.compl⟩
  measurableSet_iUnion s hs := by
    choose t ht hts using hs
    exact ⟨⋃ i, t i, MeasurableSet.iUnion ht, .countable_iUnion hts⟩

/-- We say a set `s` is an `EventuallyMeasurableSet` with respect to a given
σ-algebra `m` and σ-filter `l` if it differs from a set in `m` by a set in
the dual ideal of `l`. -/
/-
**EventuallyMeasurableSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：EventuallyMeasurableSet (l : Filter α) [CountableInterFilter l] (s : Set α
) : Prop
参数：l : Filter α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say a set `s` is an `EventuallyMeasurableSet` with respect to a given
σ-algebra `m` and σ-filter `l` if it differs from a set in `m` by a set in
the dual ideal of `l`.
-/
def EventuallyMeasurableSet (l : Filter α) [CountableInterFilter l] (s : Set α) : Prop :=
  @MeasurableSet _ (eventuallyMeasurableSpace m l) s

variable {l : Filter α} [CountableInterFilter l]
variable {m}
/-
**MeasurableSet.eventuallyMeasurableSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.eventuallyMeasurableSet (hs : MeasurableSet s) : EventuallyM
easurableSet m l s
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem MeasurableSet.eventuallyMeasurableSet (hs : MeasurableSet s) :
    EventuallyMeasurableSet m l s :=
  ⟨s, hs, EventuallyEq.refl _ _⟩
/-
**le_eventuallyMeasurableSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_eventuallyMeasurableSpace : m <= eventuallyMeasurableSpace m l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.eventuallyMeasurableSet`：MeasurableSet.eventuallyMeasurabl
eSet (hs : MeasurableSet s) : EventuallyMeasurableSet m l s
-/
theorem le_eventuallyMeasurableSpace : m ≤ eventuallyMeasurableSpace m l :=
  fun _ hs => hs.eventuallyMeasurableSet
/-
**eventuallyMeasurableSet_of_mem_filter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventuallyMeasurableSet_of_mem_filter (hs : s in l) : EventuallyMeasurable
Set m l s
参数：hs : s in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_univ`：eventuallyEq_univ {s : Set α} {l : Filter α} :
 s =ᶠ[l] univ ↔ s in l
-/
theorem eventuallyMeasurableSet_of_mem_filter (hs : s ∈ l) : EventuallyMeasurableSet m l s :=
  ⟨univ, MeasurableSet.univ, eventuallyEq_univ.mpr hs⟩

/-- A set which is `EventuallyEq` to an `EventuallyMeasurableSet`
is an `EventuallyMeasurableSet`. -/
/-
**EventuallyMeasurableSet.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EventuallyMeasurableSet.congr (ht : EventuallyMeasurableSet m l t) (hst : 
s =ᶠ[l] t) : EventuallyMeasurableSet m l s
参数：ht : EventuallyMeasurableSet m l t；hst : s =ᶠ[l] t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h

--- 原说明 ---
A set which is `EventuallyEq` to an `EventuallyMeasurableSet`
is an `EventuallyMeasurableSet`.
-/
theorem EventuallyMeasurableSet.congr
    (ht : EventuallyMeasurableSet m l t) (hst : s =ᶠ[l] t) : EventuallyMeasurableSet m l s := by
  rcases ht with ⟨t', ht', htt'⟩
  exact ⟨t', ht', hst.trans htt'⟩

section instances

/-
**eventuallyMeasurableSingleton** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：eventuallyMeasurableSingleton [MeasurableSingletonClass α] : @MeasurableSi
ngletonClass α (eventuallyMeasurableSpace m l)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.eventuallyMeasurableSet`：MeasurableSet.eventuallyMeasurabl
eSet (hs : MeasurableSet s) : EventuallyMeasurableSet m l s
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
-/
instance eventuallyMeasurableSingleton [MeasurableSingletonClass α] :
    @MeasurableSingletonClass α (eventuallyMeasurableSpace m l) :=
  @MeasurableSingletonClass.mk _ (_) <| fun x => (MeasurableSet.singleton x).eventuallyMeasurableSet

end instances

section EventuallyMeasurable

open Function

variable (m l) {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]

/-- We say a function is `EventuallyMeasurable` with respect to a given
σ-algebra `m` and σ-filter `l` if the preimage of any measurable set is equal to some
`m`-measurable set modulo `l`.
Warning: This is not always the same as being equal to some `m`-measurable function modulo `l`.
In general it is weaker. See `Measurable.eventuallyMeasurable_of_eventuallyEq`.
*TODO*: Add lemmas about when these are equivalent. -/
/-
**EventuallyMeasurable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：EventuallyMeasurable (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say a function is `EventuallyMeasurable` with respect to a given
σ-algebra `m` and σ-filter `l` if the preimage of any measurable set is equal to
 some
`m`-measurable set modulo `l`.
Warning: This is not always the same as being equal to some `m`-measurable funct
ion modulo `l`.
In general it is weaker. See `Measurable.eventuallyMeasurable_of_eventuallyEq`.
*TODO*: Add lemmas about when these are equivalent.
-/
def EventuallyMeasurable (f : α → β) : Prop := @Measurable _ _ (eventuallyMeasurableSpace m l) _ f

variable {m l} {f g : α → β} {h : β → γ}
/-
**Measurable.eventuallyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.eventuallyMeasurable (hf : Measurable f) : EventuallyMeasurable
 m l f
参数：hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.le`：Measurable.le {α} {m m0 : MeasurableSpace α} {_ : Measura
bleSpace β} (hm : m <= m0) {f : α -> β} (hf : Measurable[m] f) : Measurable[m0] 
f
· 使用定理 `le_eventuallyMeasurableSpace`：le_eventuallyMeasurableSpace : m <= eventu
allyMeasurableSpace m l
-/
theorem Measurable.eventuallyMeasurable (hf : Measurable f) : EventuallyMeasurable m l f :=
  hf.le le_eventuallyMeasurableSpace
/-
**Measurable.comp_eventuallyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.comp_eventuallyMeasurable (hh : Measurable h) (hf : EventuallyM
easurable m l f) : EventuallyMeasurable m l (h ∘ f)
参数：hh : Measurable h；hf : EventuallyMeasurable m l f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
-/
theorem Measurable.comp_eventuallyMeasurable (hh : Measurable h) (hf : EventuallyMeasurable m l f) :
    EventuallyMeasurable m l (h ∘ f) :=
  hh.comp hf

/-- A function which is `EventuallyEq` to some `EventuallyMeasurable` function
is `EventuallyMeasurable`. -/
/-
**EventuallyMeasurable.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EventuallyMeasurable.congr (hf : EventuallyMeasurable m l f) (hgf : g =ᶠ[l
] f) : EventuallyMeasurable m l g
参数：hf : EventuallyMeasurable m l f；hgf : g =ᶠ[l] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EventuallyMeasurableSet.congr`：EventuallyMeasurableSet.congr (ht : Event
uallyMeasurableSet m l t) (hst : s =ᶠ[l] t) : EventuallyMeasurableSet m l s
· 使用定理 `Filter.EventuallyEq.preimage`：∀ {α : Type u} {β : Type v} {l : Filter α}
 {f g : α → β}, f =ᶠ[l] g → ∀ (s : Set β), f ⁻¹' s =ᶠ[l] g ⁻¹' s

--- 原说明 ---
A function which is `EventuallyEq` to some `EventuallyMeasurable` function
is `EventuallyMeasurable`.
-/
theorem EventuallyMeasurable.congr
    (hf : EventuallyMeasurable m l f) (hgf : g =ᶠ[l] f) : EventuallyMeasurable m l g :=
  fun _ hs => EventuallyMeasurableSet.congr (hf hs)
    (hgf.preimage _)

/-- A function which is `EventuallyEq` to some `Measurable` function is `EventuallyMeasurable`. -/
/-
**Measurable.eventuallyMeasurable_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.eventuallyMeasurable_of_eventuallyEq (hf : Measurable f) (hgf :
 g =ᶠ[l] f) : EventuallyMeasurable m l g
参数：hf : Measurable f；hgf : g =ᶠ[l] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EventuallyMeasurable.congr`：EventuallyMeasurable.congr (hf : EventuallyM
easurable m l f) (hgf : g =ᶠ[l] f) : EventuallyMeasurable m l g
· 使用定理 `Measurable.eventuallyMeasurable`：Measurable.eventuallyMeasurable (hf : M
easurable f) : EventuallyMeasurable m l f

--- 原说明 ---
A function which is `EventuallyEq` to some `Measurable` function is `EventuallyM
easurable`.
-/
theorem Measurable.eventuallyMeasurable_of_eventuallyEq
    (hf : Measurable f) (hgf : g =ᶠ[l] f) : EventuallyMeasurable m l g :=
  hf.eventuallyMeasurable.congr hgf

end EventuallyMeasurable

