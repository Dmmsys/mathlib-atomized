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
scoped[Topology] notation3 "∀ᵇ " (...) ", " r:(scoped p => Filter.Eventually p <| residual _) => r

/-- Notation to say that a property of points in a topological space holds on a nonmeager set. -/
scoped[Topology] notation3 "∃ᵇ " (...) ", " r:(scoped p => Filter.Frequently p <| residual _) => r

variable {α}

/-
**coborder_mem_residual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coborder_mem_residual {s : Set α} (hs : IsLocallyClosed s) : coborder s in
 residual α
参数：hs : IsLocallyClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `residual_of_dense_open`：residual_of_dense_open {s : Set X} (ho : IsOpen 
s) (hd : Dense s) : s in residual X
· 使用定理 `IsLocallyClosed.isOpen_coborder`：∀ {X : Type u_1} [inst : TopologicalSpa
ce X] {s : Set X}, IsLocallyClosed s → IsOpen (coborder s)
· 使用定理 `dense_coborder`：dense_coborder {s : Set X} : Dense (coborder s)
-/
theorem coborder_mem_residual {s : Set α} (hs : IsLocallyClosed s) : coborder s ∈ residual α :=
  residual_of_dense_open hs.isOpen_coborder dense_coborder
/-
**closure_residualEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closure_residualEq {s : Set α} (hs : IsLocallyClosed s) : closure s =ᵇ s
参数：hs : IsLocallyClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyEq_set`：eventuallyEq_set {s t : Set α} {l : Filter α} :
 s =ᶠ[l] t ↔ forallᶠ x in l, x in s ↔ x in t
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `coborder_mem_residual`：coborder_mem_residual {s : Set α} (hs : IsLocally
Closed s) : coborder s in residual α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `closure_inter_coborder`：closure_inter_coborder : closure s inter coborde
r s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem closure_residualEq {s : Set α} (hs : IsLocallyClosed s) : closure s =ᵇ s := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [coborder_mem_residual hs] with x hx
  nth_rewrite 2 [← closure_inter_coborder (s := s)]
  simp [hx]

/-- We say a set is a `BaireMeasurableSet` if it differs from some Borel set by
a meager set. This forms a σ-algebra.

It is equivalent, and a more standard definition, to say that the set differs from
some *open* set by a meager set. See `BaireMeasurableSet.iff_residualEq_isOpen` -/
/-
**BaireMeasurableSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：BaireMeasurableSet (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say a set is a `BaireMeasurableSet` if it differs from some Borel set by
a meager set. This forms a σ-algebra.

It is equivalent, and a more standard definition, to say that the set differs fr
om
some *open* set by a meager set. See `BaireMeasurableSet.iff_residualEq_isOpen`
-/
def BaireMeasurableSet (s : Set α) : Prop :=
  @MeasurableSet _ (eventuallyMeasurableSpace (borel _) (residual _)) s

variable {s t : Set α}

namespace BaireMeasurableSet

/-
**BaireMeasurableSet.of_mem_residual** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableS
et`。
形式化陈述：of_mem_residual (h : s in residual _) : BaireMeasurableSet s
参数：h : s in residual _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventuallyMeasurableSet_of_mem_filter`：eventuallyMeasurableSet_of_mem_fi
lter (hs : s in l) : EventuallyMeasurableSet m l s
-/
theorem of_mem_residual (h : s ∈ residual _) : BaireMeasurableSet s :=
  eventuallyMeasurableSet_of_mem_filter (α := α) h
/-
**BaireMeasurableSet._root_.MeasurableSet.baireMeasurableSet** 是 Mathlib 中的一个定理，
位于命名空间 `BaireMeasurableSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableSet.baireMeasurableSet [MeasurableSpace α] [BorelSpace α]
    (h : MeasurableSet s) : BaireMeasurableSet s := by
  borelize α
  exact h.eventuallyMeasurableSet
/-
**BaireMeasurableSet._root_.IsOpen.baireMeasurableSet** 是 Mathlib 中的一个定理，位于命名空间 
`BaireMeasurableSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.baireMeasurableSet (h : IsOpen s) : BaireMeasurableSet s := by
  borelize α
  exact h.measurableSet.baireMeasurableSet
/-
**BaireMeasurableSet.compl** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：compl (h : BaireMeasurableSet s) : BaireMeasurableSet sᶜ
参数：h : BaireMeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem compl (h : BaireMeasurableSet s) : BaireMeasurableSet sᶜ := MeasurableSet.compl h
/-
**BaireMeasurableSet.of_compl** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：of_compl (h : BaireMeasurableSet sᶜ) : BaireMeasurableSet s
参数：h : BaireMeasurableSet sᶜ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.of_compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpac
e α}, MeasurableSet sᶜ → MeasurableSet s
-/
theorem of_compl (h : BaireMeasurableSet sᶜ) : BaireMeasurableSet s := MeasurableSet.of_compl h
/-
**BaireMeasurableSet._root_.IsMeagre.baireMeasurableSet** 是 Mathlib 中的一个定理，位于命名空
间 `BaireMeasurableSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsMeagre.baireMeasurableSet (h : IsMeagre s) : BaireMeasurableSet s :=
  (of_mem_residual h).of_compl
/-
**BaireMeasurableSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：iUnion {ι : Sort*} [Countable ι] {s : ι -> Set α} (h : forall i, BaireMeas
urableSet (s i)) : BaireMeasurableSet (⋃ i, s i)
参数：h : forall i, BaireMeasurableSet (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
-/
theorem iUnion {ι : Sort*} [Countable ι] {s : ι → Set α}
    (h : ∀ i, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋃ i, s i) :=
  MeasurableSet.iUnion h
/-
**BaireMeasurableSet.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：biUnion {ι : Type*} {s : ι -> Set α} {t : Set ι} (ht : t.Countable) (h : f
orall i in t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋃ i in t, s i)
参数：ht : t.Countable；h : forall i in t, BaireMeasurableSet (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
-/
theorem biUnion {ι : Type*} {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (h : ∀ i ∈ t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋃ i ∈ t, s i) :=
  MeasurableSet.biUnion ht h
/-
**BaireMeasurableSet.sUnion** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：sUnion {s : Set (Set α)} (hs : s.Countable) (h : forall t in s, BaireMeasu
rableSet t) : BaireMeasurableSet (⋃₀ s)
参数：Set α；hs : s.Countable；h : forall t in s, BaireMeasurableSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.sUnion`：∀ {α : Type u_1} {m : MeasurableSpace α} {s : Set 
(Set α)},   s.Countable → (∀ t ∈ s, MeasurableSet t) → MeasurableSet (⋃₀ s)
-/
theorem sUnion {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, BaireMeasurableSet t) : BaireMeasurableSet (⋃₀ s) :=
  MeasurableSet.sUnion hs h
/-
**BaireMeasurableSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：iInter {ι : Sort*} [Countable ι] {s : ι -> Set α} (h : forall i, BaireMeas
urableSet (s i)) : BaireMeasurableSet (⋂ i, s i)
参数：h : forall i, BaireMeasurableSet (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
-/
theorem iInter {ι : Sort*} [Countable ι] {s : ι → Set α}
    (h : ∀ i, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋂ i, s i) :=
  MeasurableSet.iInter h
/-
**BaireMeasurableSet.biInter** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：biInter {ι : Type*} {s : ι -> Set α} {t : Set ι} (ht : t.Countable) (h : f
orall i in t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋂ i in t, s i)
参数：ht : t.Countable；h : forall i in t, BaireMeasurableSet (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.biInter`：MeasurableSet.biInter {f : β -> Set α} {s : Set β
} (hs : s.Countable) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂
 b in s, f …
-/
theorem biInter {ι : Type*} {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (h : ∀ i ∈ t, BaireMeasurableSet (s i)) : BaireMeasurableSet (⋂ i ∈ t, s i) :=
  MeasurableSet.biInter ht h
/-
**BaireMeasurableSet.sInter** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：sInter {s : Set (Set α)} (hs : s.Countable) (h : forall t in s, BaireMeasu
rableSet t) : BaireMeasurableSet (⋂₀ s)
参数：Set α；hs : s.Countable；h : forall t in s, BaireMeasurableSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.sInter`：MeasurableSet.sInter {s : Set (Set α)} (hs : s.Cou
ntable) (h : forall t in s, MeasurableSet t) : MeasurableSet (⋂₀ s)
-/
theorem sInter {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, BaireMeasurableSet t) : BaireMeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs h
/-
**BaireMeasurableSet.union** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：union (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) : BaireMeasu
rableSet (s union t)
参数：hs : BaireMeasurableSet s；ht : BaireMeasurableSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
-/
theorem union (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s ∪ t) :=
  MeasurableSet.union hs ht
/-
**BaireMeasurableSet.inter** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：inter (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) : BaireMeasu
rableSet (s inter t)
参数：hs : BaireMeasurableSet s；ht : BaireMeasurableSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
theorem inter (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s ∩ t) :=
  MeasurableSet.inter hs ht
/-
**BaireMeasurableSet.diff** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：diff (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) : BaireMeasur
ableSet (s \ t)
参数：hs : BaireMeasurableSet s；ht : BaireMeasurableSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
-/
theorem diff (hs : BaireMeasurableSet s) (ht : BaireMeasurableSet t) :
    BaireMeasurableSet (s \ t) :=
  MeasurableSet.diff hs ht
/-
**BaireMeasurableSet.congr** 是 Mathlib 中的一个定理，位于命名空间 `BaireMeasurableSet`。
形式化陈述：congr (hs : BaireMeasurableSet s) (h : s =ᵇ t) : BaireMeasurableSet t
参数：hs : BaireMeasurableSet s；h : s =ᵇ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EventuallyMeasurableSet.congr`：EventuallyMeasurableSet.congr (ht : Event
uallyMeasurableSet m l t) (hst : s =ᶠ[l] t) : EventuallyMeasurableSet m l s
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem congr (hs : BaireMeasurableSet s) (h : s =ᵇ t) : BaireMeasurableSet t :=
  EventuallyMeasurableSet.congr (α := α) hs h.symm

end BaireMeasurableSet

open Filter

/-- Any Borel set differs from some open set by a meager set. -/
/-
**MeasurableSet.residualEq_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.residualEq_isOpen [MeasurableSpace α] [BorelSpace α] (h : Me
asurableSet s) : exists u : Set α, IsOpen u ∧ s =ᵇ u
参数：h : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.induction_on_open`：MeasurableSet.induction_on_open {C : fo
rall s : Set γ, MeasurableSet s -> Prop} (isOpen : forall U (hU : IsOpen U), C U
 hU.measurableSet) (c…
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Filter.EventuallyEq.compl`：∀ {α : Type u} {s t : Set α} {l : Filter α}, 
s =ᶠ[l] t → sᶜ =ᶠ[l] tᶜ
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `closure_residualEq`：closure_residualEq {s : Set α} (hs : IsLocallyClosed
 s) : closure s =ᵇ s
· 使用引理 `IsOpen.isLocallyClosed`：IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocal
lyClosed s
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.EventuallyEq.countable_iUnion`：∀ {ι : Sort u_1} {α : Type u_2} {l
 : Filter α} [CountableInterFilter l] [Countable ι] {s t : ι → Set α},   (∀ (i :
 ι), s i =ᶠ[l] t i) → ⋃ i,…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Any Borel set differs from some open set by a meager set.
-/
theorem MeasurableSet.residualEq_isOpen [MeasurableSpace α] [BorelSpace α] (h : MeasurableSet s) :
    ∃ u : Set α, IsOpen u ∧ s =ᵇ u := by
  induction s, h using MeasurableSet.induction_on_open with
  | isOpen U hU => exact ⟨U, hU, .rfl⟩
  | compl s _ ihs =>
    obtain ⟨U, Uo, hsU⟩ := ihs
    use (closure U)ᶜ, isClosed_closure.isOpen_compl
    exact .compl <| hsU.trans <| .symm <| closure_residualEq Uo.isLocallyClosed
  | iUnion f _ _ ihf =>
    choose u uo su using ihf
    exact ⟨⋃ i, u i, isOpen_iUnion uo, .countable_iUnion su⟩

/-- Any `BaireMeasurableSet` differs from some open set by a meager set. -/
/-
**BaireMeasurableSet.residualEq_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BaireMeasurableSet.residualEq_isOpen (h : BaireMeasurableSet s) : exists u
 : Set α, (IsOpen u) ∧ s =ᵇ u
参数：h : BaireMeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.residualEq_isOpen`：MeasurableSet.residualEq_isOpen [Measur
ableSpace α] [BorelSpace α] (h : MeasurableSet s) : exists u : Set α, IsOpen u ∧
 s =ᵇ u
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h

--- 原说明 ---
Any `BaireMeasurableSet` differs from some open set by a meager set.
-/
theorem BaireMeasurableSet.residualEq_isOpen (h : BaireMeasurableSet s) :
    ∃ u : Set α, (IsOpen u) ∧ s =ᵇ u := by
  borelize α
  rcases h with ⟨t, ht, hst⟩
  rcases ht.residualEq_isOpen with ⟨u, hu, htu⟩
  exact ⟨u, hu, hst.trans htu⟩

/-- A set is Baire measurable if and only if it differs from some open set by a meager set. -/
/-
**BaireMeasurableSet.iff_residualEq_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BaireMeasurableSet.iff_residualEq_isOpen : BaireMeasurableSet s ↔ exists u
 : Set α, (IsOpen u) ∧ s =ᵇ u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BaireMeasurableSet.residualEq_isOpen`：BaireMeasurableSet.residualEq_isOp
en (h : BaireMeasurableSet s) : exists u : Set α, (IsOpen u) ∧ s =ᵇ u
· 使用定理 `BaireMeasurableSet.congr`：congr (hs : BaireMeasurableSet s) (h : s =ᵇ t)
 : BaireMeasurableSet t
· 使用定理 `IsOpen.baireMeasurableSet`：∀ {α : Type u_1} [inst : TopologicalSpace α] 
{s : Set α}, IsOpen s → BaireMeasurableSet s
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
A set is Baire measurable if and only if it differs from some open set by a meag
er set.
-/
theorem BaireMeasurableSet.iff_residualEq_isOpen :
    BaireMeasurableSet s ↔ ∃ u : Set α, (IsOpen u) ∧ s =ᵇ u :=
  ⟨fun h => h.residualEq_isOpen, fun ⟨_, uo, ueq⟩ => uo.baireMeasurableSet.congr ueq.symm⟩

section Map

open Set

variable {f : α → β}

/-
**tendsto_residual_of_isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_residual_of_isOpenMap (hc : Continuous f) (ho : IsOpenMap f) : Ten
dsto f (residual α) (residual β)
参数：hc : Continuous f；ho : IsOpenMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_countableGenerate_iff_of_countableInterFilter`：le_countableGen
erate_iff_of_countableInterFilter {f : Filter α} [CountableInterFilter f] : f <=
 countableGenerate g ↔ g subseteq f.sets
· 使用定理 `instCountableInterFilterMap`：∀ {α : Type u_2} {β : Type u_3} (l : Filter
 α) [CountableInterFilter l] (f : α → β),   CountableInterFilter (Filter.map f l
)
· 使用定理 `residual_of_dense_open`：residual_of_dense_open {s : Set X} (ho : IsOpen 
s) (hd : Dense s) : s in residual X
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Dense.preimage`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] {s : Set Y},   Dense s → IsOpenMap
 f →…
-/
theorem tendsto_residual_of_isOpenMap (hc : Continuous f) (ho : IsOpenMap f) :
    Tendsto f (residual α) (residual β) := by
  apply le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro t ⟨ht, htd⟩
  exact residual_of_dense_open (ht.preimage hc) (htd.preimage ho)

/-- The preimage of a meager set under a continuous open map is meager. -/
/-
**IsMeagre.preimage_of_isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMeagre.preimage_of_isOpenMap (hc : Continuous f) (ho : IsOpenMap f) {s :
 Set β} (h : IsMeagre s) : IsMeagre (f ⁻¹' s)
参数：hc : Continuous f；ho : IsOpenMap f；h : IsMeagre s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_residual_of_isOpenMap`：tendsto_residual_of_isOpenMap (hc : Conti
nuous f) (ho : IsOpenMap f) : Tendsto f (residual α) (residual β)

--- 原说明 ---
The preimage of a meager set under a continuous open map is meager.
-/
theorem IsMeagre.preimage_of_isOpenMap (hc : Continuous f) (ho : IsOpenMap f)
    {s : Set β} (h : IsMeagre s) : IsMeagre (f ⁻¹' s) :=
  tendsto_residual_of_isOpenMap hc ho h

/-- The preimage of a `BaireMeasurableSet` under a continuous open map is Baire measurable. -/
/-
**BaireMeasurableSet.preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BaireMeasurableSet.preimage (hc : Continuous f) (ho : IsOpenMap f) {s : Se
t β} (h : BaireMeasurableSet s) : BaireMeasurableSet (f ⁻¹' s)
参数：hc : Continuous f；ho : IsOpenMap f；h : BaireMeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `tendsto_residual_of_isOpenMap`：tendsto_residual_of_isOpenMap (hc : Conti
nuous f) (ho : IsOpenMap f) : Tendsto f (residual α) (residual β)

--- 原说明 ---
The preimage of a `BaireMeasurableSet` under a continuous open map is Baire meas
urable.
-/
theorem BaireMeasurableSet.preimage (hc : Continuous f) (ho : IsOpenMap f)
    {s : Set β} (h : BaireMeasurableSet s) : BaireMeasurableSet (f ⁻¹' s) := by
  rcases h with ⟨u, hu, hsu⟩
  refine ⟨f ⁻¹' u, ?_, hsu.filter_mono <| tendsto_residual_of_isOpenMap hc ho⟩
  borelize α β
  exact hc.measurable hu
/-
**Homeomorph.residual_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.residual_map_eq (h : α ≃ₜ β) : (residual α).map h = residual β
参数：h : α ≃ₜ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `tendsto_residual_of_isOpenMap`：tendsto_residual_of_isOpenMap (hc : Conti
nuous f) (ho : IsOpenMap f) : Tendsto f (residual α) (residual β)
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
· 使用定理 `Filter.le_map`：le_map {f : Filter α} {m : α -> β} {g : Filter β} (h : fo
rall s in f, m '' s in g) : g <= f.map m
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem Homeomorph.residual_map_eq (h : α ≃ₜ β) : (residual α).map h = residual β := by
  refine le_antisymm (tendsto_residual_of_isOpenMap h.continuous h.isOpenMap) (le_map ?_)
  simp_rw [← preimage_symm]
  exact tendsto_residual_of_isOpenMap h.symm.continuous h.symm.isOpenMap

end Map

