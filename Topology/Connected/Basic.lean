/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Order.SuccPred.Relation
public import Mathlib.Topology.Order.OrderClosed

/-!
# Connected subsets of topological spaces

In this file we define connected subsets of a topological spaces and various other properties and
classes related to connectivity.

## Main definitions

We define the following properties for sets in a topological space:

* `IsConnected`: a nonempty set that has no non-trivial open partition.
  See also the section below in the module doc.
* `connectedComponent` is the connected component of an element in the space.

We also have a class stating that the whole space satisfies that property: `ConnectedSpace`

## On the definition of connected sets/spaces

In informal mathematics, connected spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `IsPreconnected`.
In other words, the only difference is whether the empty space counts as connected.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
-/

@[expose] public section

open Set Function Topology TopologicalSpace Relation

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section Preconnected

/-- A preconnected set is one where there is no non-trivial open partition. -/
/-
**IsPreconnected** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsPreconnected (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preconnected set is one where there is no non-trivial open partition.
-/
def IsPreconnected (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v → (s ∩ u).Nonempty → (s ∩ v).Nonempty →
    (s ∩ (u ∩ v)).Nonempty

/-- A connected set is one that is nonempty and where there is no non-trivial open partition. -/
/-
**IsConnected** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsConnected (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A connected set is one that is nonempty and where there is no non-trivial open p
artition.
-/
def IsConnected (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreconnected s
/-
**IsConnected.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConnected.nonempty {s : Set α} (h : IsConnected s) : s.Nonempty
参数：h : IsConnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsConnected.nonempty {s : Set α} (h : IsConnected s) : s.Nonempty :=
  h.1
/-
**IsConnected.isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConnected.isPreconnected {s : Set α} (h : IsConnected s) : IsPreconnecte
d s
参数：h : IsConnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsConnected.isPreconnected {s : Set α} (h : IsConnected s) : IsPreconnected s :=
  h.2
/-
**IsPreirreducible.isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreirreducible.isPreconnected {s : Set α} (H : IsPreirreducible s) : IsP
reconnected s
参数：H : IsPreirreducible s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsPreirreducible.isPreconnected {s : Set α} (H : IsPreirreducible s) : IsPreconnected s :=
  fun _ _ hu hv _ => H _ _ hu hv
/-
**IsIrreducible.isConnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIrreducible.isConnected {s : Set α} (H : IsIrreducible s) : IsConnected 
s
参数：H : IsIrreducible s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIrreducible.nonempty`：IsIrreducible.nonempty (h : IsIrreducible s) : s
.Nonempty
· 使用定理 `IsPreirreducible.isPreconnected`：IsPreirreducible.isPreconnected {s : Se
t α} (H : IsPreirreducible s) : IsPreconnected s
· 使用定理 `IsIrreducible.isPreirreducible`：IsIrreducible.isPreirreducible (h : IsIr
reducible s) : IsPreirreducible s
-/
theorem IsIrreducible.isConnected {s : Set α} (H : IsIrreducible s) : IsConnected s :=
  ⟨H.nonempty, H.isPreirreducible.isPreconnected⟩
/-
**isPreconnected_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_empty : IsPreconnected (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreirreducible.isPreconnected`：IsPreirreducible.isPreconnected {s : Se
t α} (H : IsPreirreducible s) : IsPreconnected s
· 使用定理 `isPreirreducible_empty`：isPreirreducible_empty : IsPreirreducible (∅ : S
et X)
-/
theorem isPreconnected_empty : IsPreconnected (∅ : Set α) :=
  isPreirreducible_empty.isPreconnected
/-
**isConnected_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_singleton {x} : IsConnected ({x} : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIrreducible.isConnected`：IsIrreducible.isConnected {s : Set α} (H : Is
Irreducible s) : IsConnected s
· 使用定理 `isIrreducible_singleton`：isIrreducible_singleton {x} : IsIrreducible ({x
} : Set X)
-/
theorem isConnected_singleton {x} : IsConnected ({x} : Set α) :=
  isIrreducible_singleton.isConnected
/-
**isPreconnected_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_singleton {x} : IsPreconnected ({x} : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `isConnected_singleton`：isConnected_singleton {x} : IsConnected ({x} : Se
t α)
-/
theorem isPreconnected_singleton {x} : IsPreconnected ({x} : Set α) :=
  isConnected_singleton.isPreconnected
/-
**Set.Subsingleton.isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.isPreconnected {s : Set α} (hs : s.Subsingleton) : IsPrec
onnected s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.induction_on`：∀ {α : Type u} {s : Set α} {p : Set α → P
rop}, s.Subsingleton → p ∅ → (∀ (x : α), p {x}) → p s
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)
· 使用定理 `isPreconnected_singleton`：isPreconnected_singleton {x} : IsPreconnected 
({x} : Set α)
-/
theorem Set.Subsingleton.isPreconnected {s : Set α} (hs : s.Subsingleton) : IsPreconnected s :=
  hs.induction_on isPreconnected_empty fun _ => isPreconnected_singleton

/-- If any point of a set is joined to a fixed point by a preconnected subset,
then the original set is preconnected as well. -/
/-
**isPreconnected_of_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_of_forall {s : Set α} (x : α) (H : forall y in s, exists t,
 t subseteq s ∧ x in t ∧ y in t ∧ IsPreconnected t) : IsPreconnected s
参数：x : α；H : forall y in s, exists t, t subseteq s ∧ x in t ∧ y in t ∧ IsPreconn
ected t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a

--- 原说明 ---
If any point of a set is joined to a fixed point by a preconnected subset,
then the original set is preconnected as well.
-/
theorem isPreconnected_of_forall {s : Set α} (x : α)
    (H : ∀ y ∈ s, ∃ t, t ⊆ s ∧ x ∈ t ∧ y ∈ t ∧ IsPreconnected t) : IsPreconnected s := by
  rintro u v hu hv hs ⟨z, zs, zu⟩ ⟨y, ys, yv⟩
  have xs : x ∈ s := by
    rcases H y ys with ⟨t, ts, xt, -, -⟩
    exact ts xt
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: use `wlog xu : x ∈ u := hs xs using u v y z, v u z y`
  cases hs xs with
  | inl xu =>
    rcases H y ys with ⟨t, ts, xt, yt, ht⟩
    have := ht u v hu hv (ts.trans hs) ⟨x, xt, xu⟩ ⟨y, yt, yv⟩
    exact this.imp fun z hz => ⟨ts hz.1, hz.2⟩
  | inr xv =>
    rcases H z zs with ⟨t, ts, xt, zt, ht⟩
    have := ht v u hv hu (ts.trans <| by rwa [union_comm]) ⟨x, xt, xv⟩ ⟨z, zt, zu⟩
    exact this.imp fun _ h => ⟨ts h.1, h.2.2, h.2.1⟩

/-- If any two points of a set are contained in a preconnected subset,
then the original set is preconnected as well. -/
/-
**isPreconnected_of_forall_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_of_forall_pair {s : Set α} (H : forall x in s, forall y in 
s, exists t, t subseteq s ∧ x in t ∧ y in t ∧ IsPreconnected t) : IsPreconnected
 s
参数：H : forall x in s, forall y in s, exists t, t subseteq s ∧ x in t ∧ y in t ∧ 
IsPreconnected t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isPreconnected_of_forall`：isPreconnected_of_forall {s : Set α} (x : α) (
H : forall y in s, exists t, t subseteq s ∧ x in t ∧ y in t ∧ IsPreconnected t) 
: IsPreconnect…

--- 原说明 ---
If any two points of a set are contained in a preconnected subset,
then the original set is preconnected as well.
-/
theorem isPreconnected_of_forall_pair {s : Set α}
    (H : ∀ x ∈ s, ∀ y ∈ s, ∃ t, t ⊆ s ∧ x ∈ t ∧ y ∈ t ∧ IsPreconnected t) :
    IsPreconnected s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  exacts [isPreconnected_empty, isPreconnected_of_forall x fun y => H x hx y]

/-- A union of a family of preconnected sets with a common point is preconnected as well. -/
/-
**isPreconnected_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_sUnion (x : α) (c : Set (Set α)) (H1 : forall s in c, x in 
s) (H2 : forall s in c, IsPreconnected s) : IsPreconnected (⋃₀ c)
参数：x : α；c : Set (Set α)；H1 : forall s in c, x in s；H2 : forall s in c, IsPrecon
nected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isPreconnected_of_forall`：isPreconnected_of_forall {s : Set α} (x : α) (
H : forall y in s, exists t, t subseteq s ∧ x in t ∧ y in t ∧ IsPreconnected t) 
: IsPreconnect…
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S

--- 原说明 ---
A union of a family of preconnected sets with a common point is preconnected as 
well.
-/
theorem isPreconnected_sUnion (x : α) (c : Set (Set α)) (H1 : ∀ s ∈ c, x ∈ s)
    (H2 : ∀ s ∈ c, IsPreconnected s) : IsPreconnected (⋃₀ c) := by
  apply isPreconnected_of_forall x
  rintro y ⟨s, sc, ys⟩
  exact ⟨s, subset_sUnion_of_mem sc, H1 s sc, ys, H2 s sc⟩
/-
**isPreconnected_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_iUnion {ι : Sort*} {s : ι -> Set α} (h₁ : (⋂ i, s i).Nonemp
ty) (h₂ : forall i, IsPreconnected (s i)) : IsPreconnected (⋃ i, s i)
参数：h₁ : (⋂ i, s i).Nonempty；h₂ : forall i, IsPreconnected (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `isPreconnected_sUnion`：isPreconnected_sUnion (x : α) (c : Set (Set α)) (
H1 : forall s in c, x in s) (H2 : forall s in c, IsPreconnected s) : IsPreconnec
ted (⋃₀ c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem isPreconnected_iUnion {ι : Sort*} {s : ι → Set α} (h₁ : (⋂ i, s i).Nonempty)
    (h₂ : ∀ i, IsPreconnected (s i)) : IsPreconnected (⋃ i, s i) :=
  Exists.elim h₁ fun f hf => isPreconnected_sUnion f _ hf (forall_mem_range.2 h₂)
/-
**IsPreconnected.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.union (x : α) {s t : Set α} (H1 : x in s) (H2 : x in t) (H3
 : IsPreconnected s) (H4 : IsPreconnected t) : IsPreconnected (s union t)
参数：x : α；H1 : x in s；H2 : x in t；H3 : IsPreconnected s；H4 : IsPreconnected t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isPreconnected_sUnion`：isPreconnected_sUnion (x : α) (c : Set (Set α)) (
H1 : forall s in c, x in s) (H2 : forall s in c, IsPreconnected s) : IsPreconnec
ted (⋃₀ c)
· 使用定理 `Set.sUnion_pair`：sUnion_pair (s t : Set α) : ⋃₀ {s, t} = s union t
-/
theorem IsPreconnected.union (x : α) {s t : Set α} (H1 : x ∈ s) (H2 : x ∈ t) (H3 : IsPreconnected s)
    (H4 : IsPreconnected t) : IsPreconnected (s ∪ t) :=
  sUnion_pair s t ▸ isPreconnected_sUnion x {s, t} (by rintro r (rfl | rfl | h) <;> assumption)
    (by rintro r (rfl | rfl | h) <;> assumption)
/-
**IsPreconnected.union'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.union' {s t : Set α} (H : (s inter t).Nonempty) (hs : IsPre
connected s) (ht : IsPreconnected t) : IsPreconnected (s union t)
参数：H : (s inter t).Nonempty；hs : IsPreconnected s；ht : IsPreconnected t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.union`：IsPreconnected.union (x : α) {s t : Set α} (H1 : x
 in s) (H2 : x in t) (H3 : IsPreconnected s) (H4 : IsPreconnected t) : IsPreconn
ected (s u…
-/
theorem IsPreconnected.union' {s t : Set α} (H : (s ∩ t).Nonempty) (hs : IsPreconnected s)
    (ht : IsPreconnected t) : IsPreconnected (s ∪ t) := by
  rcases H with ⟨x, hxs, hxt⟩
  exact hs.union x hxs hxt ht
/-
**IsConnected.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConnected.union {s t : Set α} (H : (s inter t).Nonempty) (Hs : IsConnect
ed s) (Ht : IsConnected t) : IsConnected (s union t)
参数：H : (s inter t).Nonempty；Hs : IsConnected s；Ht : IsConnected t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Set.mem_of_mem_inter_left`：mem_of_mem_inter_left {x : α} {a b : Set α} (
h : x in a inter b) : x in a
· 使用定理 `IsPreconnected.union`：IsPreconnected.union (x : α) {s t : Set α} (H1 : x
 in s) (H2 : x in t) (H3 : IsPreconnected s) (H4 : IsPreconnected t) : IsPreconn
ected (s u…
· 使用定理 `Set.mem_of_mem_inter_right`：mem_of_mem_inter_right {x : α} {a b : Set α}
 (h : x in a inter b) : x in b
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
-/
theorem IsConnected.union {s t : Set α} (H : (s ∩ t).Nonempty) (Hs : IsConnected s)
    (Ht : IsConnected t) : IsConnected (s ∪ t) := by
  rcases H with ⟨x, hx⟩
  refine ⟨⟨x, mem_union_left t (mem_of_mem_inter_left hx)⟩, ?_⟩
  exact Hs.isPreconnected.union x (mem_of_mem_inter_left hx) (mem_of_mem_inter_right hx)
    Ht.isPreconnected

/-- The directed sUnion of a set S of preconnected subsets is preconnected. -/
/-
**IsPreconnected.sUnion_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.sUnion_directed {S : Set (Set α)} (K : DirectedOn (· subset
eq ·) S) (H : forall s in S, IsPreconnected s) : IsPreconnected (⋃₀ S)
参数：Set α；K : DirectedOn (· subseteq ·) S；H : forall s in S, IsPreconnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty

--- 原说明 ---
The directed sUnion of a set S of preconnected subsets is preconnected.
-/
theorem IsPreconnected.sUnion_directed {S : Set (Set α)} (K : DirectedOn (· ⊆ ·) S)
    (H : ∀ s ∈ S, IsPreconnected s) : IsPreconnected (⋃₀ S) := by
  rintro u v hu hv Huv ⟨a, ⟨s, hsS, has⟩, hau⟩ ⟨b, ⟨t, htS, hbt⟩, hbv⟩
  obtain ⟨r, hrS, hsr, htr⟩ : ∃ r ∈ S, s ⊆ r ∧ t ⊆ r := K s hsS t htS
  have Hnuv : (r ∩ (u ∩ v)).Nonempty :=
    H _ hrS u v hu hv ((subset_sUnion_of_mem hrS).trans Huv) ⟨a, hsr has, hau⟩ ⟨b, htr hbt, hbv⟩
  have Kruv : r ∩ (u ∩ v) ⊆ ⋃₀ S ∩ (u ∩ v) := inter_subset_inter_left _ (subset_sUnion_of_mem hrS)
  exact Hnuv.mono Kruv

/-- The biUnion of a family of preconnected sets is preconnected if the graph determined by
whether two sets intersect is preconnected. -/
/-
**IsPreconnected.biUnion_of_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.biUnion_of_reflTransGen {ι : Type*} {t : Set ι} {s : ι -> S
et α} (H : forall i in t, IsPreconnected (s i)) (K : forall i, i in t -> forall 
j, j in t -> ReflTransGen (fun i j => (s i inter s j).Nonempty ∧ i in t) i j) : 
IsPreconnected (⋃ n in t, s n)
参数：H : forall i in t, IsPreconnected (s i)；K : forall i, i in t -> forall j, j i
n t -> ReflTransGen (fun i j => (s i inter s j).Nonempty ∧ i in t) i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_singleton`：biUnion_singleton (a : α) (s : α -> Set β) : ⋃ x 
in ({a} : Set α), s x = s a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.biUnion_insert`：biUnion_insert (a : α) (s : Set α) (t : α -> Set β) 
: ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `IsPreconnected.union'`：IsPreconnected.union' {s t : Set α} (H : (s inter
 t).Nonempty) (hs : IsPreconnected s) (ht : IsPreconnected t) : IsPreconnected (
s union t)
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isPreconnected_of_forall_pair`：isPreconnected_of_forall_pair {s : Set α}
 (H : forall x in s, forall y in s, exists t, t subseteq s ∧ x in t ∧ y in t ∧ I
sPreconnected t) : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x

--- 原说明 ---
The biUnion of a family of preconnected sets is preconnected if the graph determ
ined by
whether two sets intersect is preconnected.
-/
theorem IsPreconnected.biUnion_of_reflTransGen {ι : Type*} {t : Set ι} {s : ι → Set α}
    (H : ∀ i ∈ t, IsPreconnected (s i))
    (K : ∀ i, i ∈ t → ∀ j, j ∈ t → ReflTransGen (fun i j => (s i ∩ s j).Nonempty ∧ i ∈ t) i j) :
    IsPreconnected (⋃ n ∈ t, s n) := by
  let R := fun i j : ι => (s i ∩ s j).Nonempty ∧ i ∈ t
  have P : ∀ i, i ∈ t → ∀ j, j ∈ t → ReflTransGen R i j →
      ∃ p, p ⊆ t ∧ i ∈ p ∧ j ∈ p ∧ IsPreconnected (⋃ j ∈ p, s j) := fun i hi j hj h => by
    induction h with
    | refl =>
      refine ⟨{i}, singleton_subset_iff.mpr hi, mem_singleton i, mem_singleton i, ?_⟩
      rw [biUnion_singleton]
      exact H i hi
    | @tail j k _ hjk ih =>
      obtain ⟨p, hpt, hip, hjp, hp⟩ := ih hjk.2
      refine ⟨insert k p, insert_subset_iff.mpr ⟨hj, hpt⟩, mem_insert_of_mem k hip,
        mem_insert k p, ?_⟩
      rw [biUnion_insert]
      refine (H k hj).union' (hjk.1.mono ?_) hp
      rw [inter_comm]
      exact inter_subset_inter_right _ (subset_biUnion_of_mem hjp)
  refine isPreconnected_of_forall_pair ?_
  intro x hx y hy
  obtain ⟨i : ι, hi : i ∈ t, hxi : x ∈ s i⟩ := mem_iUnion₂.1 hx
  obtain ⟨j : ι, hj : j ∈ t, hyj : y ∈ s j⟩ := mem_iUnion₂.1 hy
  obtain ⟨p, hpt, hip, hjp, hp⟩ := P i hi j hj (K i hi j hj)
  exact ⟨⋃ j ∈ p, s j, biUnion_subset_biUnion_left hpt, mem_biUnion hip hxi,
    mem_biUnion hjp hyj, hp⟩

/-- The biUnion of a family of preconnected sets is preconnected if the graph determined by
whether two sets intersect is preconnected. -/
/-
**IsConnected.biUnion_of_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConnected.biUnion_of_reflTransGen {ι : Type*} {t : Set ι} {s : ι -> Set 
α} (ht : t.Nonempty) (H : forall i in t, IsConnected (s i)) (K : forall i, i in 
t -> forall j, j in t -> ReflTransGen (fun i j : ι => (s i inter s j).Nonempty ∧
 i in t) i j) : IsConnected (⋃ n in t, s n)
参数：ht : t.Nonempty；H : forall i in t, IsConnected (s i)；K : forall i, i in t -> 
forall j, j in t -> ReflTransGen (fun i j : ι => (s i inter s j).Nonempty ∧ i in
 t) i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_biUnion`：nonempty_biUnion {t : Set α} {s : α -> Set β} : (⋃
 i in t, s i).Nonempty ↔ exists i in t, (s i).Nonempty
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `IsPreconnected.biUnion_of_reflTransGen`：IsPreconnected.biUnion_of_reflTr
ansGen {ι : Type*} {t : Set ι} {s : ι -> Set α} (H : forall i in t, IsPreconnect
ed (s i)) (K : forall i, i i…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s

--- 原说明 ---
The biUnion of a family of preconnected sets is preconnected if the graph determ
ined by
whether two sets intersect is preconnected.
-/
theorem IsConnected.biUnion_of_reflTransGen {ι : Type*} {t : Set ι} {s : ι → Set α}
    (ht : t.Nonempty) (H : ∀ i ∈ t, IsConnected (s i))
    (K : ∀ i, i ∈ t → ∀ j, j ∈ t → ReflTransGen (fun i j : ι => (s i ∩ s j).Nonempty ∧ i ∈ t) i j) :
    IsConnected (⋃ n ∈ t, s n) :=
  ⟨nonempty_biUnion.2 <| ⟨ht.some, ht.some_mem, (H _ ht.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_reflTransGen (fun i hi => (H i hi).isPreconnected) K⟩

/-- Preconnectedness of the iUnion of a family of preconnected sets
indexed by the vertices of a preconnected graph,
where two vertices are joined when the corresponding sets intersect. -/
/-
**IsPreconnected.iUnion_of_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.iUnion_of_reflTransGen {ι : Type*} {s : ι -> Set α} (H : fo
rall i, IsPreconnected (s i)) (K : forall i j, ReflTransGen (fun i j : ι => (s i
 inter s j).Nonempty) i j) : IsPreconnected (⋃ n, s n)
参数：H : forall i, IsPreconnected (s i)；K : forall i j, ReflTransGen (fun i j : ι 
=> (s i inter s j).Nonempty) i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_univ`：biUnion_univ (s : α -> Set β) : ⋃ x in @univ α, s x = 
⋃ x, s x
· 使用定理 `IsPreconnected.biUnion_of_reflTransGen`：IsPreconnected.biUnion_of_reflTr
ansGen {ι : Type*} {t : Set ι} {s : ι -> Set α} (H : forall i in t, IsPreconnect
ed (s i)) (K : forall i, i i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
Preconnectedness of the iUnion of a family of preconnected sets
indexed by the vertices of a preconnected graph,
where two vertices are joined when the corresponding sets intersect.
-/
theorem IsPreconnected.iUnion_of_reflTransGen {ι : Type*} {s : ι → Set α}
    (H : ∀ i, IsPreconnected (s i))
    (K : ∀ i j, ReflTransGen (fun i j : ι => (s i ∩ s j).Nonempty) i j) :
    IsPreconnected (⋃ n, s n) := by
  rw [← biUnion_univ]
  exact IsPreconnected.biUnion_of_reflTransGen (fun i _ => H i) fun i _ j _ => by
    simpa [mem_univ] using K i j
/-
**IsConnected.iUnion_of_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConnected.iUnion_of_reflTransGen {ι : Type*} [Nonempty ι] {s : ι -> Set 
α} (H : forall i, IsConnected (s i)) (K : forall i j, ReflTransGen (fun i j : ι 
=> (s i inter s j).Nonempty) i j) : IsConnected (⋃ n, s n)
参数：H : forall i, IsConnected (s i)；K : forall i j, ReflTransGen (fun i j : ι => 
(s i inter s j).Nonempty) i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iUnion`：nonempty_iUnion : (⋃ i, s i).Nonempty ↔ exists i, (
s i).Nonempty
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `IsPreconnected.iUnion_of_reflTransGen`：IsPreconnected.iUnion_of_reflTran
sGen {ι : Type*} {s : ι -> Set α} (H : forall i, IsPreconnected (s i)) (K : fora
ll i j, ReflTransGen (fun i…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
-/
theorem IsConnected.iUnion_of_reflTransGen {ι : Type*} [Nonempty ι] {s : ι → Set α}
    (H : ∀ i, IsConnected (s i))
    (K : ∀ i j, ReflTransGen (fun i j : ι => (s i ∩ s j).Nonempty) i j) : IsConnected (⋃ n, s n) :=
  ⟨nonempty_iUnion.2 <| Nonempty.elim ‹_› fun i : ι => ⟨i, (H _).nonempty⟩,
    IsPreconnected.iUnion_of_reflTransGen (fun i => (H i).isPreconnected) K⟩
/-
**IsPreconnected.transGen_of_iUnion** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPreconnected.transGen_of_iUnion {ι : Type*} {s : ι -> Set α} (hs : IsPre
connected (⋃ n, s n)) (hs' : forall i, IsOpen (s i)) (i j : ι) (hi : (s i).Nonem
pty) (hj : (s j).Nonempty) : TransGen (fun a b => (s a inter s b).Nonempty) i j
参数：hs : IsPreconnected (⋃ n, s n)；hs' : forall i, IsOpen (s i)；i j : ι；hi : (s i
).Nonempty；hj : (s j).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `iSup_split`：iSup_split (f : β -> α) (p : β -> Prop) : ⨆ i, f i = (⨆ (i) 
(_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), f i
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `Set.mem_iUnion₂_of_mem`：mem_iUnion₂_of_mem {s : forall i, κ i -> Set α} 
{a : α} {i : ι} (j : κ i) (ha : a in s i j) : a in ⋃ (i) (j), s i j
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma IsPreconnected.transGen_of_iUnion {ι : Type*} {s : ι → Set α}
    (hs : IsPreconnected (⋃ n, s n)) (hs' : ∀ i, IsOpen (s i)) (i j : ι) (hi : (s i).Nonempty)
    (hj : (s j).Nonempty) : TransGen (fun a b ↦ (s a ∩ s b).Nonempty) i j := by
  by_contra hij
  let S : Set ι := {k | TransGen (fun a b ↦ (s a ∩ s b).Nonempty) i k}
  let U : Set α := ⋃ k ∈ S, s k
  let V : Set α := ⋃ k ∈ Sᶜ, s k
  have hsplit : (⋃ n, s n) = U ∪ V := iSup_split s (· ∈ S)
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  let hi_S : i ∈ S := Relation.TransGen.single ⟨a, ha, ha⟩
  have hUne : ((⋃ n, s n) ∩ U).Nonempty := ⟨a, mem_iUnion_of_mem i ha, mem_iUnion₂_of_mem hi_S ha⟩
  have hVne : ((⋃ n, s n) ∩ V).Nonempty := ⟨b, mem_iUnion_of_mem j hb, mem_iUnion₂_of_mem hij hb⟩
  obtain ⟨x, -, hxU, hxV⟩ := hs U V (isOpen_biUnion fun i a ↦ hs' i)
    (isOpen_biUnion fun i a ↦ hs' i) hsplit.le hUne hVne
  simp only [mem_iUnion, exists_prop, mem_compl_iff, U, V] at hxU hxV
  obtain ⟨k, hk, hxk⟩ := hxU
  obtain ⟨l, hl, hxl⟩ := hxV
  exact hl (hk.tail ⟨x, hxk, hxl⟩)

section SuccOrder

open Order

variable [LinearOrder β] [SuccOrder β] [IsSuccArchimedean β]

/-- The iUnion of connected sets indexed by a type with an archimedean successor (like `ℕ` or `ℤ`)
  such that any two neighboring sets meet is preconnected. -/
/-
**IsPreconnected.iUnion_of_chain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.iUnion_of_chain {s : β -> Set α} (H : forall n, IsPreconnec
ted (s n)) (K : forall n, (s n inter s (succ n)).Nonempty) : IsPreconnected (⋃ n
, s n)
参数：H : forall n, IsPreconnected (s n)；K : forall n, (s n inter s (succ n)).Nonem
pty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.iUnion_of_reflTransGen`：IsPreconnected.iUnion_of_reflTran
sGen {ι : Type*} {s : ι -> Set α} (H : forall i, IsPreconnected (s i)) (K : fora
ll i j, ReflTransGen (fun i…
· 使用定理 `reflTransGen_of_succ`：reflTransGen_of_succ (r : α -> α -> Prop) {n m : α
} (h1 : forall i in Ico n m, r i (succ i)) (h2 : forall i in Ico m n, r (succ i)
 i) : Refl…

--- 原说明 ---
The iUnion of connected sets indexed by a type with an archimedean successor (li
ke `ℕ` or `ℤ`)
  such that any two neighboring sets meet is preconnected.
-/
theorem IsPreconnected.iUnion_of_chain {s : β → Set α} (H : ∀ n, IsPreconnected (s n))
    (K : ∀ n, (s n ∩ s (succ n)).Nonempty) : IsPreconnected (⋃ n, s n) :=
  IsPreconnected.iUnion_of_reflTransGen H fun _ _ =>
    reflTransGen_of_succ _ (fun i _ => K i) (by grind)

/-- The iUnion of connected sets indexed by a type with an archimedean successor (like `ℕ` or `ℤ`)
  such that any two neighboring sets meet is connected. -/
/-
**IsConnected.iUnion_of_chain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConnected.iUnion_of_chain [Nonempty β] {s : β -> Set α} (H : forall n, I
sConnected (s n)) (K : forall n, (s n inter s (succ n)).Nonempty) : IsConnected 
(⋃ n, s n)
参数：H : forall n, IsConnected (s n)；K : forall n, (s n inter s (succ n)).Nonempty
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.iUnion_of_reflTransGen`：IsConnected.iUnion_of_reflTransGen {
ι : Type*} [Nonempty ι] {s : ι -> Set α} (H : forall i, IsConnected (s i)) (K : 
forall i j, ReflTransGen…
· 使用定理 `reflTransGen_of_succ`：reflTransGen_of_succ (r : α -> α -> Prop) {n m : α
} (h1 : forall i in Ico n m, r i (succ i)) (h2 : forall i in Ico m n, r (succ i)
 i) : Refl…

--- 原说明 ---
The iUnion of connected sets indexed by a type with an archimedean successor (li
ke `ℕ` or `ℤ`)
  such that any two neighboring sets meet is connected.
-/
theorem IsConnected.iUnion_of_chain [Nonempty β] {s : β → Set α} (H : ∀ n, IsConnected (s n))
    (K : ∀ n, (s n ∩ s (succ n)).Nonempty) : IsConnected (⋃ n, s n) :=
  IsConnected.iUnion_of_reflTransGen H fun _ _ => reflTransGen_of_succ _ (fun i _ => K i) (by grind)

/-- The iUnion of preconnected sets indexed by a subset of a type with an archimedean successor
  (like `ℕ` or `ℤ`) such that any two neighboring sets meet is preconnected. -/
/-
**IsPreconnected.biUnion_of_chain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.biUnion_of_chain {s : β -> Set α} {t : Set β} (ht : OrdConn
ected t) (H : forall n in t, IsPreconnected (s n)) (K : forall n : β, n in t -> 
succ n in t -> (s n inter s (succ n)).Nonempty) : IsPreconnected (⋃ n in t, s n)
参数：ht : OrdConnected t；H : forall n in t, IsPreconnected (s n)；K : forall n : β,
 n in t -> succ n in t -> (s n inter s (succ n)).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsPreconnected.biUnion_of_reflTransGen`：IsPreconnected.biUnion_of_reflTr
ansGen {ι : Type*} {t : Set ι} {s : ι -> Set α} (H : forall i in t, IsPreconnect
ed (s i)) (K : forall i, i i…
· 使用定理 `reflTransGen_of_succ`：reflTransGen_of_succ (r : α -> α -> Prop) {n m : α
} (h1 : forall i in Ico n m, r i (succ i)) (h2 : forall i in Ico m n, r (succ i)
 i) : Refl…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
The iUnion of preconnected sets indexed by a subset of a type with an archimedea
n successor
  (like `ℕ` or `ℤ`) such that any two neighboring sets meet is preconnected.
-/
theorem IsPreconnected.biUnion_of_chain {s : β → Set α} {t : Set β} (ht : OrdConnected t)
    (H : ∀ n ∈ t, IsPreconnected (s n))
    (K : ∀ n : β, n ∈ t → succ n ∈ t → (s n ∩ s (succ n)).Nonempty) :
    IsPreconnected (⋃ n ∈ t, s n) := by
  have h1 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → k ∈ t := fun hi hj hk =>
    ht.out hi hj (Ico_subset_Icc_self hk)
  have h2 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → succ k ∈ t := fun hi hj hk =>
    ht.out hi hj ⟨hk.1.trans <| le_succ _, succ_le_of_lt hk.2⟩
  have h3 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → (s k ∩ s (succ k)).Nonempty :=
    fun hi hj hk => K _ (h1 hi hj hk) (h2 hi hj hk)
  refine IsPreconnected.biUnion_of_reflTransGen H fun i hi j hj => ?_
  exact reflTransGen_of_succ _ (fun k hk => ⟨h3 hi hj hk, h1 hi hj hk⟩) fun k hk =>
      ⟨by rw [inter_comm]; exact h3 hj hi hk, h2 hj hi hk⟩

/-- The iUnion of connected sets indexed by a subset of a type with an archimedean successor
  (like `ℕ` or `ℤ`) such that any two neighboring sets meet is preconnected. -/
/-
**IsConnected.biUnion_of_chain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConnected.biUnion_of_chain {s : β -> Set α} {t : Set β} (hnt : t.Nonempt
y) (ht : OrdConnected t) (H : forall n in t, IsConnected (s n)) (K : forall n : 
β, n in t -> succ n in t -> (s n inter s (succ n)).Nonempty) : IsConnected (⋃ n 
in t, s n)
参数：hnt : t.Nonempty；ht : OrdConnected t；H : forall n in t, IsConnected (s n)；K :
 forall n : β, n in t -> succ n in t -> (s n inter s (succ n)).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_biUnion`：nonempty_biUnion {t : Set α} {s : α -> Set β} : (⋃
 i in t, s i).Nonempty ↔ exists i in t, (s i).Nonempty
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `IsPreconnected.biUnion_of_chain`：IsPreconnected.biUnion_of_chain {s : β 
-> Set α} {t : Set β} (ht : OrdConnected t) (H : forall n in t, IsPreconnected (
s n)) (K : forall n :…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s

--- 原说明 ---
The iUnion of connected sets indexed by a subset of a type with an archimedean s
uccessor
  (like `ℕ` or `ℤ`) such that any two neighboring sets meet is preconnected.
-/
theorem IsConnected.biUnion_of_chain {s : β → Set α} {t : Set β} (hnt : t.Nonempty)
    (ht : OrdConnected t) (H : ∀ n ∈ t, IsConnected (s n))
    (K : ∀ n : β, n ∈ t → succ n ∈ t → (s n ∩ s (succ n)).Nonempty) : IsConnected (⋃ n ∈ t, s n) :=
  ⟨nonempty_biUnion.2 <| ⟨hnt.some, hnt.some_mem, (H _ hnt.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_chain ht (fun i hi => (H i hi).isPreconnected) K⟩

end SuccOrder

/-- Theorem of bark and tree: if a set is within a preconnected set and its closure, then it is
preconnected as well. See also `IsConnected.subset_closure`. -/
/-
**IsPreconnected.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `IsPreconnected`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] {s t : Set α}, IsPreconnected s
 → s ⊆ t → t ⊆ closure s → IsPreconnected t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall o, IsOpen o -
> x in o -> (o inter s).Nonempty
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c

--- 原说明 ---
Theorem of bark and tree: if a set is within a preconnected set and its closure,
 then it is
preconnected as well. See also `IsConnected.subset_closure`.
-/
protected theorem IsPreconnected.subset_closure {s : Set α} {t : Set α} (H : IsPreconnected s)
    (Kst : s ⊆ t) (Ktcs : t ⊆ closure s) : IsPreconnected t :=
  fun u v hu hv htuv ⟨_y, hyt, hyu⟩ ⟨_z, hzt, hzv⟩ =>
  let ⟨p, hpu, hps⟩ := mem_closure_iff.1 (Ktcs hyt) u hu hyu
  let ⟨q, hqv, hqs⟩ := mem_closure_iff.1 (Ktcs hzt) v hv hzv
  let ⟨r, hrs, hruv⟩ := H u v hu hv (Subset.trans Kst htuv) ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩
  ⟨r, Kst hrs, hruv⟩

/-- Theorem of bark and tree: if a set is within a connected set and its closure, then it is
connected as well. See also `IsPreconnected.subset_closure`. -/
/-
**IsConnected.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `IsConnected`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] {s t : Set α}, IsConnected s → 
s ⊆ t → t ⊆ closure s → IsConnected t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsPreconnected.subset_closure`：∀ {α : Type u} [inst : TopologicalSpace α
] {s t : Set α}, IsPreconnected s → s ⊆ t → t ⊆ closure s → IsPreconnected t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Theorem of bark and tree: if a set is within a connected set and its closure, th
en it is
connected as well. See also `IsPreconnected.subset_closure`.
-/
protected theorem IsConnected.subset_closure {s : Set α} {t : Set α} (H : IsConnected s)
    (Kst : s ⊆ t) (Ktcs : t ⊆ closure s) : IsConnected t :=
  ⟨Nonempty.mono Kst H.left, IsPreconnected.subset_closure H.right Kst Ktcs⟩

/-- The closure of a preconnected set is preconnected as well. -/
/-
**IsPreconnected.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsPreconnected`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] {s : Set α}, IsPreconnected s →
 IsPreconnected (closure s)
参数：closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.subset_closure`：∀ {α : Type u} [inst : TopologicalSpace α
] {s t : Set α}, IsPreconnected s → s ⊆ t → t ⊆ closure s → IsPreconnected t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
The closure of a preconnected set is preconnected as well.
-/
protected theorem IsPreconnected.closure {s : Set α} (H : IsPreconnected s) :
    IsPreconnected (closure s) :=
  IsPreconnected.subset_closure H subset_closure Subset.rfl

/-- The closure of a connected set is connected as well. -/
/-
**IsConnected.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsConnected`。
形式化陈述：∀ {α : Type u} [inst : TopologicalSpace α] {s : Set α}, IsConnected s → Is
Connected (closure s)
参数：closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.subset_closure`：∀ {α : Type u} [inst : TopologicalSpace α] {
s t : Set α}, IsConnected s → s ⊆ t → t ⊆ closure s → IsConnected t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
The closure of a connected set is connected as well.
-/
protected theorem IsConnected.closure {s : Set α} (H : IsConnected s) : IsConnected (closure s) :=
  IsConnected.subset_closure H subset_closure <| Subset.rfl

/-- The image of a preconnected set is preconnected as well. -/
/-
**IsPreconnected.image** 是 Mathlib 中的一个定理，位于命名空间 `IsPreconnected`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : Topologi
calSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α → β), ContinuousOn f s → 
IsPreconnected (f '' s)
参数：f : α → β；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff'`：continuousOn_iff' : ContinuousOn f s ↔ forall t : Set
 β, IsOpen t -> exists u, IsOpen u ∧ f ⁻¹' t inter s = u inter s
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_union`：preimage_union {s t : Set β} : f ⁻¹' (s union t) = f
 ⁻¹' s union f ⁻¹' t
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_left_comm`：inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ inter (s₂ i
nter s₃) = s₂ inter (s₁ inter s₃)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a

--- 原说明 ---
The image of a preconnected set is preconnected as well.
-/
protected theorem IsPreconnected.image [TopologicalSpace β] {s : Set α} (H : IsPreconnected s)
    (f : α → β) (hf : ContinuousOn f s) : IsPreconnected (f '' s) := by
  -- Unfold/destruct definitions in hypotheses
  rintro u v hu hv huv ⟨_, ⟨x, xs, rfl⟩, xu⟩ ⟨_, ⟨y, ys, rfl⟩, yv⟩
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  -- Reformulate `huv : f '' s ⊆ u ∪ v` in terms of `u'` and `v'`
  replace huv : s ⊆ u' ∪ v' := by
    rw [image_subset_iff, preimage_union] at huv
    replace huv := subset_inter huv Subset.rfl
    rw [union_inter_distrib_right, u'_eq, v'_eq, ← union_inter_distrib_right] at huv
    exact (subset_inter_iff.1 huv).1
  -- Now `s ⊆ u' ∪ v'`, so we can apply `‹IsPreconnected s›`
  obtain ⟨z, hz⟩ : (s ∩ (u' ∩ v')).Nonempty := by
    refine H u' v' hu' hv' huv ⟨x, ?_⟩ ⟨y, ?_⟩ <;> rw [inter_comm]
    exacts [u'_eq ▸ ⟨xu, xs⟩, v'_eq ▸ ⟨yv, ys⟩]
  rw [← inter_self s, inter_assoc, inter_left_comm s u', ← inter_assoc, inter_comm s, inter_comm s,
    ← u'_eq, ← v'_eq] at hz
  exact ⟨f z, ⟨z, hz.1.2, rfl⟩, hz.1.1, hz.2.1⟩

/-- The image of a connected set is connected as well. -/
/-
**IsConnected.image** 是 Mathlib 中的一个定理，位于命名空间 `IsConnected`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [inst_1 : Topologi
calSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), ContinuousOn f s → IsC
onnected (f '' s)
参数：f : α → β；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s

--- 原说明 ---
The image of a connected set is connected as well.
-/
protected theorem IsConnected.image [TopologicalSpace β] {s : Set α} (H : IsConnected s) (f : α → β)
    (hf : ContinuousOn f s) : IsConnected (f '' s) :=
  ⟨image_nonempty.mpr H.nonempty, H.isPreconnected.image f hf⟩
/-
**isPreconnected_closed_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_closed_iff {s : Set α} : IsPreconnected s ↔ forall t t', Is
Closed t -> IsClosed t' -> s subseteq t union t' -> (s inter t).Nonempty -> (s i
nter t').Nonempty -> (s inter (t inter t')).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `LE.le.disjoint_compl_right`：LE.le.disjoint_compl_right (h : a <= b) : Di
sjoint a bᶜ
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
-/
theorem isPreconnected_closed_iff {s : Set α} :
    IsPreconnected s ↔ ∀ t t', IsClosed t → IsClosed t' →
      s ⊆ t ∪ t' → (s ∩ t).Nonempty → (s ∩ t').Nonempty → (s ∩ (t ∩ t')).Nonempty :=
  ⟨by
      rintro h t t' ht ht' htt' ⟨x, xs, xt⟩ ⟨y, ys, yt'⟩
      rw [← not_disjoint_iff_nonempty_inter, ← subset_compl_iff_disjoint_right, compl_inter]
      intro h'
      have xt' : x ∉ t' := (h' xs).resolve_left (absurd xt)
      have yt : y ∉ t := (h' ys).resolve_right (absurd yt')
      have := h _ _ ht.isOpen_compl ht'.isOpen_compl h' ⟨y, ys, yt⟩ ⟨x, xs, xt'⟩
      rw [← compl_union] at this
      exact this.ne_empty htt'.disjoint_compl_right.inter_eq,
    by
      rintro h u v hu hv huv ⟨x, xs, xu⟩ ⟨y, ys, yv⟩
      rw [← not_disjoint_iff_nonempty_inter, ← subset_compl_iff_disjoint_right, compl_inter]
      intro h'
      have xv : x ∉ v := (h' xs).elim (absurd xu) id
      have yu : y ∉ u := (h' ys).elim id (absurd yv)
      have := h _ _ hu.isClosed_compl hv.isClosed_compl h' ⟨y, ys, yu⟩ ⟨x, xs, xv⟩
      rw [← compl_union] at this
      exact this.ne_empty huv.disjoint_compl_right.inter_eq⟩
/-
**Topology.IsInducing.isPreconnected_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.isPreconnected_image [TopologicalSpace β] {s : Set α} 
{f : α -> β} (hf : IsInducing f) : IsPreconnected (f '' s) ↔ IsPreconnected s
参数：hf : IsInducing f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
-/
theorem Topology.IsInducing.isPreconnected_image [TopologicalSpace β] {s : Set α} {f : α → β}
    (hf : IsInducing f) : IsPreconnected (f '' s) ↔ IsPreconnected s := by
  refine ⟨fun h => ?_, fun h => h.image _ hf.continuous.continuousOn⟩
  rintro u v hu' hv' huv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
  rcases hf.isOpen_iff.1 hu' with ⟨u, hu, rfl⟩
  rcases hf.isOpen_iff.1 hv' with ⟨v, hv, rfl⟩
  replace huv : f '' s ⊆ u ∪ v := by rwa [image_subset_iff]
  rcases h u v hu hv huv ⟨f x, mem_image_of_mem _ hxs, hxu⟩ ⟨f y, mem_image_of_mem _ hys, hyv⟩ with
    ⟨_, ⟨z, hzs, rfl⟩, hzuv⟩
  exact ⟨z, hzs, hzuv⟩

/- TODO: The following lemmas about connection of preimages hold more generally for strict maps
(the quotient and subspace topologies of the image agree) whose fibers are preconnected. -/

/-
**IsPreconnected.preimage_of_isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.preimage_of_isOpenMap [TopologicalSpace β] {f : α -> β} {s 
: Set β} (hs : IsPreconnected s) (hinj : Function.Injective f) (hf : IsOpenMap f
) (hsf : s subseteq range f) : IsPreconnected (f ⁻¹' s)
参数：hs : IsPreconnected s；hinj : Function.Injective f；hf : IsOpenMap f；hsf : s su
bseteq range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.image_preimage_inter`：image_preimage_inter (f : α -> β) (s : Set α) 
(t : Set β) : f '' (f ⁻¹' t inter s) = t inter f '' s
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s

--- 原说明 ---
TODO: The following lemmas about connection of preimages hold more generally for
 strict maps
(the quotient and subspace topologies of the image agree) whose fibers are preco
nnected.
-/
theorem IsPreconnected.preimage_of_isOpenMap [TopologicalSpace β] {f : α → β} {s : Set β}
    (hs : IsPreconnected s) (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf : s ⊆ range f) :
    IsPreconnected (f ⁻¹' s) := fun u v hu hv hsuv hsu hsv => by
  replace hsf : f '' f ⁻¹' s = s := image_preimage_eq_of_subset hsf
  obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s ∩ (f '' u ∩ f '' v)).Nonempty := by
    refine hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
    · simpa only [hsf, image_union] using image_mono (f := f) hsuv
    · simpa only [image_preimage_inter] using hsu.image f
    · simpa only [image_preimage_inter] using hsv.image f
  · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩
/-
**IsPreconnected.preimage_of_isClosedMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.preimage_of_isClosedMap [TopologicalSpace β] {s : Set β} (h
s : IsPreconnected s) {f : α -> β} (hinj : Function.Injective f) (hf : IsClosedM
ap f) (hsf : s subseteq range f) : IsPreconnected (f ⁻¹' s)
参数：hs : IsPreconnected s；hinj : Function.Injective f；hf : IsClosedMap f；hsf : s 
subseteq range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPreconnected_closed_iff`：isPreconnected_closed_iff {s : Set α} : IsPre
connected s ↔ forall t t', IsClosed t -> IsClosed t' -> s subseteq t union t' ->
 (s inter t).No…
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.image_preimage_inter`：image_preimage_inter (f : α -> β) (s : Set α) 
(t : Set β) : f '' (f ⁻¹' t inter s) = t inter f '' s
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
-/
theorem IsPreconnected.preimage_of_isClosedMap [TopologicalSpace β] {s : Set β}
    (hs : IsPreconnected s) {f : α → β} (hinj : Function.Injective f) (hf : IsClosedMap f)
    (hsf : s ⊆ range f) : IsPreconnected (f ⁻¹' s) :=
  isPreconnected_closed_iff.2 fun u v hu hv hsuv hsu hsv => by
    replace hsf : f '' f ⁻¹' s = s := image_preimage_eq_of_subset hsf
    obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s ∩ (f '' u ∩ f '' v)).Nonempty := by
      refine isPreconnected_closed_iff.1 hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
      · simpa only [hsf, image_union] using image_mono (f := f) hsuv
      · simpa only [image_preimage_inter] using hsu.image f
      · simpa only [image_preimage_inter] using hsv.image f
    · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩
/-
**IsConnected.preimage_of_isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConnected.preimage_of_isOpenMap [TopologicalSpace β] {s : Set β} (hs : I
sConnected s) {f : α -> β} (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf
 : s subseteq range f) : IsConnected (f ⁻¹' s)
参数：hs : IsConnected s；hinj : Function.Injective f；hf : IsOpenMap f；hsf : s subse
teq range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.preimage'`：∀ {α : Type u_1} {β : Type u_2} {s : Set β}, s.N
onempty → ∀ {f : α → β}, s ⊆ Set.range f → (f ⁻¹' s).Nonempty
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `IsPreconnected.preimage_of_isOpenMap`：IsPreconnected.preimage_of_isOpenM
ap [TopologicalSpace β] {f : α -> β} {s : Set β} (hs : IsPreconnected s) (hinj :
 Function.Injective f) (hf…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
-/
theorem IsConnected.preimage_of_isOpenMap [TopologicalSpace β] {s : Set β} (hs : IsConnected s)
    {f : α → β} (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf : s ⊆ range f) :
    IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_isOpenMap hinj hf hsf⟩
/-
**IsConnected.preimage_of_isClosedMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConnected.preimage_of_isClosedMap [TopologicalSpace β] {s : Set β} (hs :
 IsConnected s) {f : α -> β} (hinj : Function.Injective f) (hf : IsClosedMap f) 
(hsf : s subseteq range f) : IsConnected (f ⁻¹' s)
参数：hs : IsConnected s；hinj : Function.Injective f；hf : IsClosedMap f；hsf : s sub
seteq range f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.preimage'`：∀ {α : Type u_1} {β : Type u_2} {s : Set β}, s.N
onempty → ∀ {f : α → β}, s ⊆ Set.range f → (f ⁻¹' s).Nonempty
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `IsPreconnected.preimage_of_isClosedMap`：IsPreconnected.preimage_of_isClo
sedMap [TopologicalSpace β] {s : Set β} (hs : IsPreconnected s) {f : α -> β} (hi
nj : Function.Injective f) (…
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
-/
theorem IsConnected.preimage_of_isClosedMap [TopologicalSpace β] {s : Set β} (hs : IsConnected s)
    {f : α → β} (hinj : Function.Injective f) (hf : IsClosedMap f) (hsf : s ⊆ range f) :
    IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_isClosedMap hinj hf hsf⟩
/-
**IsPreconnected.subset_or_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.subset_or_subset (hu : IsOpen u) (hv : IsOpen v) (huv : Dis
joint u v) (hsuv : s subseteq u union v) (hs : IsPreconnected s) : s subseteq u 
∨ s subseteq v
参数：hu : IsOpen u；hv : IsOpen v；huv : Disjoint u v；hsuv : s subseteq u union v；hs
 : IsPreconnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Disjoint.subset_right_of_subset_union`：subset_right_of_subset_union (h :
 s subseteq t union u) (hab : Disjoint s t) : s subseteq u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Disjoint.subset_left_of_subset_union`：subset_left_of_subset_union (h : s
 subseteq t union u) (hac : Disjoint s u) : s subseteq t
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_empty`：∀ {α : Type u} (s : Set α), Disjoint s ∅
-/
theorem IsPreconnected.subset_or_subset (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
    (hsuv : s ⊆ u ∪ v) (hs : IsPreconnected s) : s ⊆ u ∨ s ⊆ v := by
  specialize hs u v hu hv hsuv
  obtain hsu | hsu := (s ∩ u).eq_empty_or_nonempty
  · exact Or.inr ((Set.disjoint_iff_inter_eq_empty.2 hsu).subset_right_of_subset_union hsuv)
  · replace hs := mt (hs hsu)
    simp_rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty,
      disjoint_iff_inter_eq_empty.1 huv] at hs
    exact Or.inl ((hs s.disjoint_empty).subset_left_of_subset_union hsuv)

section OrderClosedTopology

variable [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] {f : α → β} {b : β}

/-
**IsPreconnected.mapsTo_Ioi_or_Iio** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPreconnected.mapsTo_Ioi_or_Iio (hs : IsPreconnected s) (hf : ContinuousO
n f s) (hfb : forall x in s, f x != b) : Set.MapsTo f s (Set.Ioi b) ∨ Set.MapsTo
 f s (Set.Iio b)
参数：hs : IsPreconnected s；hf : ContinuousOn f s；hfb : forall x in s, f x != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsPreconnected.subset_or_subset`：IsPreconnected.subset_or_subset (hu : I
sOpen u) (hv : IsOpen v) (huv : Disjoint u v) (hsuv : s subseteq u union v) (hs 
: IsPreconnected s) :…
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
-/
lemma IsPreconnected.mapsTo_Ioi_or_Iio (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (hfb : ∀ x ∈ s, f x ≠ b) : Set.MapsTo f s (Set.Ioi b) ∨ Set.MapsTo f s (Set.Iio b) := by
  simpa [mapsTo_iff_image_subset] using
    (hs.image f hf).subset_or_subset isOpen_Ioi isOpen_Iio (by grind) (by grind)
/-
**IsPreconnected.lt_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPreconnected.lt_of_ne (hs : IsPreconnected s) (hf : ContinuousOn f s) (h
fb : forall x in s, f x != b) (hfx : exists x in s, b < f x) {x : α} (hx : x in 
s) : b < f x
参数：hs : IsPreconnected s；hf : ContinuousOn f s；hfb : forall x in s, f x != b；hfx
 : exists x in s, b < f x；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `IsPreconnected.mapsTo_Ioi_or_Iio`：IsPreconnected.mapsTo_Ioi_or_Iio (hs :
 IsPreconnected s) (hf : ContinuousOn f s) (hfb : forall x in s, f x != b) : Set
.MapsTo f s (Set.Ioi b…
· 使用定理 `not_forall₂_of_exists₂_not`：not_forall₂_of_exists₂_not : (exists x h, ¬P
 x h) -> ¬forall x h, P x h | ⟨x, h, hp⟩, al => hp al x h  -- See Note [decidabl
e namespace] pro…
-/
lemma IsPreconnected.lt_of_ne (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (hfb : ∀ x ∈ s, f x ≠ b) (hfx : ∃ x ∈ s, b < f x) {x : α} (hx : x ∈ s) : b < f x :=
  (hs.mapsTo_Ioi_or_Iio hf hfb).resolve_right (not_forall₂_of_exists₂_not (by grind)) hx
/-
**IsPreconnected.gt_of_ne** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPreconnected.gt_of_ne (hs : IsPreconnected s) (hf : ContinuousOn f s) (h
fb : forall x in s, f x != b) (hfx : exists x in s, f x < b) {x : α} (hx : x in 
s) : f x < b
参数：hs : IsPreconnected s；hf : ContinuousOn f s；hfb : forall x in s, f x != b；hfx
 : exists x in s, f x < b；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `IsPreconnected.mapsTo_Ioi_or_Iio`：IsPreconnected.mapsTo_Ioi_or_Iio (hs :
 IsPreconnected s) (hf : ContinuousOn f s) (hfb : forall x in s, f x != b) : Set
.MapsTo f s (Set.Ioi b…
· 使用定理 `not_forall₂_of_exists₂_not`：not_forall₂_of_exists₂_not : (exists x h, ¬P
 x h) -> ¬forall x h, P x h | ⟨x, h, hp⟩, al => hp al x h  -- See Note [decidabl
e namespace] pro…
-/
lemma IsPreconnected.gt_of_ne (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (hfb : ∀ x ∈ s, f x ≠ b) (hfx : ∃ x ∈ s, f x < b) {x : α} (hx : x ∈ s) : f x < b :=
  (hs.mapsTo_Ioi_or_Iio hf hfb).resolve_left (not_forall₂_of_exists₂_not (by grind)) hx

end OrderClosedTopology

/-
**IsPreconnected.subset_left_of_subset_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.subset_left_of_subset_union (hu : IsOpen u) (hv : IsOpen v)
 (huv : Disjoint u v) (hsuv : s subseteq u union v) (hsu : (s inter u).Nonempty)
 (hs : IsPreconnected s) : s subseteq u
参数：hu : IsOpen u；hv : IsOpen v；huv : Disjoint u v；hsuv : s subseteq u union v；hs
u : (s inter u).Nonempty；hs : IsPreconnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.subset_left_of_subset_union`：subset_left_of_subset_union (h : s
 subseteq t union u) (hac : Disjoint s u) : s subseteq t
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
-/
theorem IsPreconnected.subset_left_of_subset_union (hu : IsOpen u) (hv : IsOpen v)
    (huv : Disjoint u v) (hsuv : s ⊆ u ∪ v) (hsu : (s ∩ u).Nonempty) (hs : IsPreconnected s) :
    s ⊆ u :=
  Disjoint.subset_left_of_subset_union hsuv
    (by
      by_contra hsv
      rw [not_disjoint_iff_nonempty_inter] at hsv
      obtain ⟨x, _, hx⟩ := hs u v hu hv hsuv hsu hsv
      exact Set.disjoint_iff.1 huv hx)
/-
**IsPreconnected.subset_right_of_subset_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.subset_right_of_subset_union (hu : IsOpen u) (hv : IsOpen v
) (huv : Disjoint u v) (hsuv : s subseteq u union v) (hsv : (s inter v).Nonempty
) (hs : IsPreconnected s) : s subseteq v
参数：hu : IsOpen u；hv : IsOpen v；huv : Disjoint u v；hsuv : s subseteq u union v；hs
v : (s inter v).Nonempty；hs : IsPreconnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.subset_left_of_subset_union`：IsPreconnected.subset_left_o
f_subset_union (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v) (hsuv : s su
bseteq u union v) (hsu : (s inte…
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
-/
theorem IsPreconnected.subset_right_of_subset_union (hu : IsOpen u) (hv : IsOpen v)
    (huv : Disjoint u v) (hsuv : s ⊆ u ∪ v) (hsv : (s ∩ v).Nonempty) (hs : IsPreconnected s) :
    s ⊆ v :=
  hs.subset_left_of_subset_union hv hu huv.symm (union_comm u v ▸ hsuv) hsv

/-- If a preconnected set `s` intersects an open set `u`, and limit points of `u` inside `s` are
contained in `u`, then the whole set `s` is contained in `u`. -/
/-
**IsPreconnected.subset_of_closure_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.subset_of_closure_inter_subset (hs : IsPreconnected s) (hu 
: IsOpen u) (h'u : (s inter u).Nonempty) (h : closure u inter s subseteq u) : s 
subseteq u
参数：hs : IsPreconnected s；hu : IsOpen u；h'u : (s inter u).Nonempty；h : closure u 
inter s subseteq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `IsPreconnected.subset_left_of_subset_union`：IsPreconnected.subset_left_o
f_subset_union (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v) (hsuv : s su
bseteq u union v) (hsu : (s inte…
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ

--- 原说明 ---
If a preconnected set `s` intersects an open set `u`, and limit points of `u` in
side `s` are
contained in `u`, then the whole set `s` is contained in `u`.
-/
theorem IsPreconnected.subset_of_closure_inter_subset (hs : IsPreconnected s) (hu : IsOpen u)
    (h'u : (s ∩ u).Nonempty) (h : closure u ∩ s ⊆ u) : s ⊆ u := by
  have A : s ⊆ u ∪ (closure u)ᶜ := by
    intro x hx
    by_cases xu : x ∈ u
    · exact Or.inl xu
    · right
      intro h'x
      exact xu (h (mem_inter h'x hx))
  apply hs.subset_left_of_subset_union hu isClosed_closure.isOpen_compl _ A h'u
  exact disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)
/-
**IsPreconnected.prod** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：IsPreconnected.prod [IsPreconnected J] [IsPreconnected K] : IsPreconnected
 (J × K)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isPreconnected_of_forall_pair`：isPreconnected_of_forall_pair {s : Set α}
 (H : forall x in s, forall y in s, exists t, t subseteq s ∧ x in t ∧ y in t ∧ I
sPreconnected t) : …
· 使用定理 `IsPreconnected.union`：IsPreconnected.union (x : α) {s t : Set α} (H1 : x
 in s) (H2 : x in t) (H3 : IsPreconnected s) (H4 : IsPreconnected t) : IsPreconn
ected (s u…
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk_left`：Continuous.prodMk_left (y : Y) : Continuous fun 
x : X => (x, y)
-/
theorem IsPreconnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsPreconnected s)
    (ht : IsPreconnected t) : IsPreconnected (s ×ˢ t) := by
  apply isPreconnected_of_forall_pair
  rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩
  refine ⟨Prod.mk a₁ '' t ∪ flip Prod.mk b₂ '' s, ?_, .inl ⟨b₁, hb₁, rfl⟩, .inr ⟨a₂, ha₂, rfl⟩, ?_⟩
  · rintro _ (⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩)
    exacts [⟨ha₁, hy⟩, ⟨hx, hb₂⟩]
  · exact (ht.image _ (by fun_prop)).union (a₁, b₂) ⟨b₂, hb₂, rfl⟩
      ⟨a₁, ha₁, rfl⟩ (hs.image _ (Continuous.prodMk_left _).continuousOn)
/-
**IsConnected.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsConn
ected s) (ht : IsConnected t) : IsConnected (s ×ˢ t)
参数：hs : IsConnected s；ht : IsConnected t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.prod`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set 
β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsConnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsConnected s)
    (ht : IsConnected t) : IsConnected (s ×ˢ t) :=
  ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩
/-
**isPreconnected_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_univ_pi [forall i, TopologicalSpace (X i)] {s : forall i, S
et (X i)} (hs : forall i, IsPreconnected (s i)) : IsPreconnected (pi univ s)
参数：X i；X i；hs : forall i, IsPreconnected (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_finset_piecewise_mem_of_mem_nhds`：exists_finset_piecewise_mem_of_
mem_nhds [DecidableEq ι] {s : Set (forall a, A a)} {x : forall a, A a} (hs : s i
n 𝓝 x) (y : forall a, A a) : …
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.piecewise_empty`：piecewise_empty [forall i : ι, Decidable (i in (
∅ : Finset ι))] : piecewise ∅ f g = g
· 使用引理 `Finset.piecewise_mem_set_pi`：piecewise_mem_set_pi (hf : f in Set.pi t t'
) (hg : g in Set.pi t t') : s.piecewise f g in Set.pi t t'
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.update_preimage_univ_pi`：update_preimage_univ_pi [DecidableEq ι] {f 
: forall i, α i} (hf : forall j != i, f j in t j) : update f i ⁻¹' pi univ t = t
 i
· 使用定理 `trivial`：True
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.update`：Continuous.update [DecidableEq ι] (hf : Continuous f)
 (i : ι) {g : X -> A i} (hg : Continuous g) : Continuous fun a => update (f a) i
 (g a)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `Finset.piecewise_insert`：piecewise_insert [DecidableEq ι] (j : ι) [foral
l i, Decidable (i in insert j s)] : (insert j s).piecewise f g = update (s.piece
wise f g) j (…
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem isPreconnected_univ_pi [∀ i, TopologicalSpace (X i)] {s : ∀ i, Set (X i)}
    (hs : ∀ i, IsPreconnected (s i)) : IsPreconnected (pi univ s) := by
  rintro u v uo vo hsuv ⟨f, hfs, hfu⟩ ⟨g, hgs, hgv⟩
  classical
  rcases exists_finset_piecewise_mem_of_mem_nhds (uo.mem_nhds hfu) g with ⟨I, hI⟩
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨g, hgs, ⟨?_, hgv⟩⟩
    simpa using hI
  | insert i I _ ihI =>
    rw [Finset.piecewise_insert] at hI
    have := I.piecewise_mem_set_pi hfs hgs
    refine (hsuv this).elim ihI fun h => ?_
    set S := update (I.piecewise f g) i '' s i
    have hsub : S ⊆ pi univ s := by
      refine image_subset_iff.2 fun z hz => ?_
      rwa [update_preimage_univ_pi]
      exact fun j _ => this j trivial
    have hconn : IsPreconnected S :=
      (hs i).image _ (continuous_const.update i continuous_id).continuousOn
    have hSu : (S ∩ u).Nonempty := ⟨_, mem_image_of_mem _ (hfs _ trivial), hI⟩
    have hSv : (S ∩ v).Nonempty := ⟨_, ⟨_, this _ trivial, update_eq_self _ _⟩, h⟩
    refine (hconn u v uo vo (hsub.trans hsuv) hSu hSv).mono ?_
    exact inter_subset_inter_left _ hsub

@[simp]
/-
**isConnected_univ_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_univ_pi [forall i, TopologicalSpace (X i)] {s : forall i, Set 
(X i)} : IsConnected (pi univ s) ↔ forall i, IsConnected (s i)
参数：X i；X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eval_image_univ_pi`：eval_image_univ_pi (ht : (pi univ t).Nonempty) :
 (fun f : forall i, α i => f i) '' pi univ t = t i
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `isPreconnected_univ_pi`：isPreconnected_univ_pi [forall i, TopologicalSpa
ce (X i)] {s : forall i, Set (X i)} (hs : forall i, IsPreconnected (s i)) : IsPr
econnected (…
-/
theorem isConnected_univ_pi [∀ i, TopologicalSpace (X i)] {s : ∀ i, Set (X i)} :
    IsConnected (pi univ s) ↔ ∀ i, IsConnected (s i) := by
  simp only [IsConnected, ← univ_pi_nonempty_iff, forall_and, and_congr_right_iff]
  refine fun hne => ⟨fun hc i => ?_, isPreconnected_univ_pi⟩
  rw [← eval_image_univ_pi hne]
  exact hc.image _ (continuous_apply _).continuousOn

/-- The connected component of a point is the maximal connected set
that contains this point. -/
/-
**connectedComponent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：connectedComponent (x : α) : Set α
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connected component of a point is the maximal connected set
that contains this point.
-/
def connectedComponent (x : α) : Set α :=
  ⋃₀ { s : Set α | IsPreconnected s ∧ x ∈ s }

open scoped Classical in
/-- Given a set `F` in a topological space `α` and a point `x : α`, the connected
component of `x` in `F` is the connected component of `x` in the subtype `F` seen as
a set in `α`. This definition does not make sense if `x` is not in `F` so we return the
empty set in this case. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**connectedComponentIn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：connectedComponentIn (F : Set α) (x : α) : Set α
参数：F : Set α；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def connectedComponentIn (F : Set α) (x : α) : Set α :=
  if h : x ∈ F then (↑) '' connectedComponent (⟨x, h⟩ : F) else ∅
/-
**connectedComponentIn_eq_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponentIn_eq_image {F : Set α} {x : α} (h : x in F) : connected
ComponentIn F x = (↑) '' connectedComponent (⟨x, h⟩ : F)
参数：h : x in F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem connectedComponentIn_eq_image {F : Set α} {x : α} (h : x ∈ F) :
    connectedComponentIn F x = (↑) '' connectedComponent (⟨x, h⟩ : F) :=
  dif_pos h
/-
**connectedComponentIn_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponentIn_eq_empty {F : Set α} {x : α} (h : x ∉ F) : connectedC
omponentIn F x = ∅
参数：h : x ∉ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem connectedComponentIn_eq_empty {F : Set α} {x : α} (h : x ∉ F) :
    connectedComponentIn F x = ∅ :=
  dif_neg h
/-
**mem_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_connectedComponent {x : α} : x in connectedComponent x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_sUnion_of_mem`：mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (S
et α)} (hx : x in t) (ht : t in S) : x in ⋃₀ S
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `isPreconnected_singleton`：isPreconnected_singleton {x} : IsPreconnected 
({x} : Set α)
-/
theorem mem_connectedComponent {x : α} : x ∈ connectedComponent x :=
  mem_sUnion_of_mem (mem_singleton x) ⟨isPreconnected_singleton, mem_singleton x⟩
/-
**mem_connectedComponentIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_connectedComponentIn {x : α} {F : Set α} (hx : x in F) : x in connecte
dComponentIn F x
参数：hx : x in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `connectedComponentIn_eq_image`：connectedComponentIn_eq_image {F : Set α}
 {x : α} (h : x in F) : connectedComponentIn F x = (↑) '' connectedComponent (⟨x
, h⟩ : F)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem mem_connectedComponentIn {x : α} {F : Set α} (hx : x ∈ F) :
    x ∈ connectedComponentIn F x := by
  simp [connectedComponentIn_eq_image hx, mem_connectedComponent, hx]
/-
**connectedComponent_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponent_nonempty {x : α} : (connectedComponent x).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
-/
theorem connectedComponent_nonempty {x : α} : (connectedComponent x).Nonempty :=
  ⟨x, mem_connectedComponent⟩
/-
**connectedComponentIn_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponentIn_nonempty_iff {x : α} {F : Set α} : (connectedComponen
tIn F x).Nonempty ↔ x in F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `connectedComponentIn.eq_1`：∀ {α : Type u} [inst : TopologicalSpace α] (F
 : Set α) (x : α),   connectedComponentIn F x = if h : x ∈ F then Subtype.val ''
 connectedCompo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem connectedComponentIn_nonempty_iff {x : α} {F : Set α} :
    (connectedComponentIn F x).Nonempty ↔ x ∈ F := by
  rw [connectedComponentIn]
  split_ifs <;> simp [connectedComponent_nonempty, *]
/-
**connectedComponentIn_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponentIn_subset (F : Set α) (x : α) : connectedComponentIn F x
 subseteq F
参数：F : Set α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `connectedComponentIn.eq_1`：∀ {α : Type u} [inst : TopologicalSpace α] (F
 : Set α) (x : α),   connectedComponentIn F x = if h : x ∈ F then Subtype.val ''
 connectedCompo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem connectedComponentIn_subset (F : Set α) (x : α) : connectedComponentIn F x ⊆ F := by
  rw [connectedComponentIn]
  split_ifs <;> simp
/-
**isPreconnected_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_connectedComponent {x : α} : IsPreconnected (connectedCompo
nent x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isPreconnected_sUnion`：isPreconnected_sUnion (x : α) (c : Set (Set α)) (
H1 : forall s in c, x in s) (H2 : forall s in c, IsPreconnected s) : IsPreconnec
ted (⋃₀ c)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isPreconnected_connectedComponent {x : α} : IsPreconnected (connectedComponent x) :=
  isPreconnected_sUnion x _ (fun _ => And.right) fun _ => And.left
/-
**isPreconnected_connectedComponentIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_connectedComponentIn {x : α} {F : Set α} : IsPreconnected (
connectedComponentIn F x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `connectedComponentIn.eq_1`：∀ {α : Type u} [inst : TopologicalSpace α] (F
 : Set α) (x : α),   connectedComponentIn F x = if h : x ∈ F then Subtype.val ''
 connectedCompo…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsInducing.isPreconnected_image`：Topology.IsInducing.isPreconne
cted_image [TopologicalSpace β] {s : Set α} {f : α -> β} (hf : IsInducing f) : I
sPreconnected (f '' s) ↔ IsPre…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)
-/
theorem isPreconnected_connectedComponentIn {x : α} {F : Set α} :
    IsPreconnected (connectedComponentIn F x) := by
  rw [connectedComponentIn]; split_ifs
  · exact IsInducing.subtypeVal.isPreconnected_image.mpr isPreconnected_connectedComponent
  · exact isPreconnected_empty
/-
**isConnected_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_connectedComponent {x : α} : IsConnected (connectedComponent x
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
-/
theorem isConnected_connectedComponent {x : α} : IsConnected (connectedComponent x) :=
  ⟨⟨x, mem_connectedComponent⟩, isPreconnected_connectedComponent⟩
/-
**isConnected_connectedComponentIn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_connectedComponentIn_iff {x : α} {F : Set α} : IsConnected (co
nnectedComponentIn F x) ↔ x in F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isConnected_connectedComponentIn_iff {x : α} {F : Set α} :
    IsConnected (connectedComponentIn F x) ↔ x ∈ F := by
  simp_rw [← connectedComponentIn_nonempty_iff, IsConnected, isPreconnected_connectedComponentIn,
    and_true]
/-
**IsPreconnected.subset_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.subset_connectedComponent {x : α} {s : Set α} (H1 : IsPreco
nnected s) (H2 : x in s) : s subseteq connectedComponent x
参数：H1 : IsPreconnected s；H2 : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_sUnion_of_mem`：mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (S
et α)} (hx : x in t) (ht : t in S) : x in ⋃₀ S
-/
theorem IsPreconnected.subset_connectedComponent {x : α} {s : Set α} (H1 : IsPreconnected s)
    (H2 : x ∈ s) : s ⊆ connectedComponent x := fun _z hz => mem_sUnion_of_mem hz ⟨H1, H2⟩
/-
**IsPreconnected.subset_connectedComponentIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.subset_connectedComponentIn {x : α} {F : Set α} (hs : IsPre
connected s) (hxs : x in s) (hsF : s subseteq F) : s subseteq connectedComponent
In F x
参数：hs : IsPreconnected s；hxs : x in s；hsF : s subseteq F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isPreconnected_image`：Topology.IsInducing.isPreconne
cted_image [TopologicalSpace β] {s : Set α} {f : α -> β} (hf : IsInducing f) : I
sPreconnected (f '' s) ↔ IsPre…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `IsPreconnected.subset_connectedComponent`：IsPreconnected.subset_connecte
dComponent {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x in s) : s subsete
q connectedComponent x
· 使用定理 `connectedComponentIn_eq_image`：connectedComponentIn_eq_image {F : Set α}
 {x : α} (h : x in F) : connectedComponentIn F x = (↑) '' connectedComponent (⟨x
, h⟩ : F)
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem IsPreconnected.subset_connectedComponentIn {x : α} {F : Set α} (hs : IsPreconnected s)
    (hxs : x ∈ s) (hsF : s ⊆ F) : s ⊆ connectedComponentIn F x := by
  have : IsPreconnected (((↑) : F → α) ⁻¹' s) := by
    refine IsInducing.subtypeVal.isPreconnected_image.mp ?_
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hsF]
  have h2xs : (⟨x, hsF hxs⟩ : F) ∈ (↑) ⁻¹' s := by
    rw [mem_preimage]
    exact hxs
  have := this.subset_connectedComponent h2xs
  rw [connectedComponentIn_eq_image (hsF hxs)]
  refine Subset.trans ?_ (image_mono this)
  rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsF]
/-
**IsConnected.subset_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConnected.subset_connectedComponent {x : α} {s : Set α} (H1 : IsConnecte
d s) (H2 : x in s) : s subseteq connectedComponent x
参数：H1 : IsConnected s；H2 : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.subset_connectedComponent`：IsPreconnected.subset_connecte
dComponent {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x in s) : s subsete
q connectedComponent x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsConnected.subset_connectedComponent {x : α} {s : Set α} (H1 : IsConnected s)
    (H2 : x ∈ s) : s ⊆ connectedComponent x :=
  H1.2.subset_connectedComponent H2
/-
**IsPreconnected.connectedComponentIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.connectedComponentIn {x : α} {F : Set α} (h : IsPreconnecte
d F) (hx : x in F) : connectedComponentIn F x = F
参数：h : IsPreconnected F；hx : x in F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `connectedComponentIn_subset`：connectedComponentIn_subset (F : Set α) (x 
: α) : connectedComponentIn F x subseteq F
· 使用定理 `IsPreconnected.subset_connectedComponentIn`：IsPreconnected.subset_connec
tedComponentIn {x : α} {F : Set α} (hs : IsPreconnected s) (hxs : x in s) (hsF :
 s subseteq F) : s subseteq conn…
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem IsPreconnected.connectedComponentIn {x : α} {F : Set α} (h : IsPreconnected F)
    (hx : x ∈ F) : connectedComponentIn F x = F :=
  (connectedComponentIn_subset F x).antisymm (h.subset_connectedComponentIn hx subset_rfl)
/-
**connectedComponent_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponent_eq {x y : α} (h : y in connectedComponent x) : connecte
dComponent x = connectedComponent y
参数：h : y in connectedComponent x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
· 使用定理 `IsConnected.subset_connectedComponent`：IsConnected.subset_connectedCompo
nent {x : α} {s : Set α} (H1 : IsConnected s) (H2 : x in s) : s subseteq connect
edComponent x
· 使用定理 `isConnected_connectedComponent`：isConnected_connectedComponent {x : α} :
 IsConnected (connectedComponent x)
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
-/
theorem connectedComponent_eq {x y : α} (h : y ∈ connectedComponent x) :
    connectedComponent x = connectedComponent y :=
  eq_of_subset_of_subset (isConnected_connectedComponent.subset_connectedComponent h)
    (isConnected_connectedComponent.subset_connectedComponent
      (Set.mem_of_mem_of_subset mem_connectedComponent
        (isConnected_connectedComponent.subset_connectedComponent h)))
/-
**connectedComponent_eq_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponent_eq_iff_mem {x y : α} : connectedComponent x = connected
Component y ↔ x in connectedComponent y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `connectedComponent_eq`：connectedComponent_eq {x y : α} (h : y in connect
edComponent x) : connectedComponent x = connectedComponent y
-/
theorem connectedComponent_eq_iff_mem {x y : α} :
    connectedComponent x = connectedComponent y ↔ x ∈ connectedComponent y :=
  ⟨fun h => h ▸ mem_connectedComponent, fun h => (connectedComponent_eq h).symm⟩
/-
**connectedComponentIn_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponentIn_eq {x y : α} {F : Set α} (h : y in connectedComponent
In F x) : connectedComponentIn F x = connectedComponentIn F y
参数：h : y in connectedComponentIn F x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `connectedComponentIn_nonempty_iff`：connectedComponentIn_nonempty_iff {x 
: α} {F : Set α} : (connectedComponentIn F x).Nonempty ↔ x in F
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `connectedComponentIn_eq_image`：connectedComponentIn_eq_image {F : Set α}
 {x : α} (h : x in F) : connectedComponentIn F x = (↑) '' connectedComponent (⟨x
, h⟩ : F)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `connectedComponent_eq`：connectedComponent_eq {x y : α} (h : y in connect
edComponent x) : connectedComponent x = connectedComponent y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem connectedComponentIn_eq {x y : α} {F : Set α} (h : y ∈ connectedComponentIn F x) :
    connectedComponentIn F x = connectedComponentIn F y := by
  have hx : x ∈ F := connectedComponentIn_nonempty_iff.mp ⟨y, h⟩
  simp_rw [connectedComponentIn_eq_image hx] at h ⊢
  obtain ⟨⟨y, hy⟩, h2y, rfl⟩ := h
  simp_rw [connectedComponentIn_eq_image hy, connectedComponent_eq h2y]
/-
**connectedComponentIn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponentIn_univ (x : α) : connectedComponentIn univ x = connecte
dComponent x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `IsPreconnected.subset_connectedComponent`：IsPreconnected.subset_connecte
dComponent {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x in s) : s subsete
q connectedComponent x
· 使用定理 `isPreconnected_connectedComponentIn`：isPreconnected_connectedComponentIn
 {x : α} {F : Set α} : IsPreconnected (connectedComponentIn F x)
· 使用定理 `mem_connectedComponentIn`：mem_connectedComponentIn {x : α} {F : Set α} (
hx : x in F) : x in connectedComponentIn F x
· 使用定理 `trivial`：True
· 使用定理 `IsPreconnected.subset_connectedComponentIn`：IsPreconnected.subset_connec
tedComponentIn {x : α} {F : Set α} (hs : IsPreconnected s) (hxs : x in s) (hsF :
 s subseteq F) : s subseteq conn…
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem connectedComponentIn_univ (x : α) : connectedComponentIn univ x = connectedComponent x :=
  subset_antisymm
    (isPreconnected_connectedComponentIn.subset_connectedComponent <|
      mem_connectedComponentIn trivial)
    (isPreconnected_connectedComponent.subset_connectedComponentIn mem_connectedComponent <|
      subset_univ _)
/-
**connectedComponent_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponent_disjoint {x y : α} (h : connectedComponent x != connect
edComponent y) : Disjoint (connectedComponent x) (connectedComponent y)
参数：h : connectedComponent x != connectedComponent y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `connectedComponent_eq`：connectedComponent_eq {x y : α} (h : y in connect
edComponent x) : connectedComponent x = connectedComponent y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem connectedComponent_disjoint {x y : α} (h : connectedComponent x ≠ connectedComponent y) :
    Disjoint (connectedComponent x) (connectedComponent y) :=
  Set.disjoint_left.2 fun _ h1 h2 =>
    h ((connectedComponent_eq h1).trans (connectedComponent_eq h2).symm)
/-
**isClosed_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_connectedComponent {x : α} : IsClosed (connectedComponent x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `closure_subset_iff_isClosed`：closure_subset_iff_isClosed : closure s sub
seteq s ↔ IsClosed s
· 使用定理 `IsConnected.subset_connectedComponent`：IsConnected.subset_connectedCompo
nent {x : α} {s : Set α} (H1 : IsConnected s) (H2 : x in s) : s subseteq connect
edComponent x
· 使用定理 `IsConnected.closure`：∀ {α : Type u} [inst : TopologicalSpace α] {s : Set
 α}, IsConnected s → IsConnected (closure s)
· 使用定理 `isConnected_connectedComponent`：isConnected_connectedComponent {x : α} :
 IsConnected (connectedComponent x)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
-/
theorem isClosed_connectedComponent {x : α} : IsClosed (connectedComponent x) :=
  closure_subset_iff_isClosed.1 <|
    isConnected_connectedComponent.closure.subset_connectedComponent <|
      subset_closure mem_connectedComponent
/-
**Continuous.image_connectedComponent_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.image_connectedComponent_subset [TopologicalSpace β] {f : α -> 
β} (h : Continuous f) (a : α) : f '' connectedComponent a subseteq connectedComp
onent (f a)
参数：h : Continuous f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.subset_connectedComponent`：IsConnected.subset_connectedCompo
nent {x : α} {s : Set α} (H1 : IsConnected s) (H2 : x in s) : s subseteq connect
edComponent x
· 使用定理 `IsConnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace 
α] [inst_1 : TopologicalSpace β] {s : Set α},   IsConnected s → ∀ (f : α → β), C
ontinuo…
· 使用定理 `isConnected_connectedComponent`：isConnected_connectedComponent {x : α} :
 IsConnected (connectedComponent x)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x
-/
theorem Continuous.image_connectedComponent_subset [TopologicalSpace β] {f : α → β}
    (h : Continuous f) (a : α) : f '' connectedComponent a ⊆ connectedComponent (f a) :=
  (isConnected_connectedComponent.image f h.continuousOn).subset_connectedComponent
    ((mem_image f (connectedComponent a) (f a)).2 ⟨a, mem_connectedComponent, rfl⟩)
/-
**ContinuousOn.image_connectedComponentIn_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.image_connectedComponentIn_subset [TopologicalSpace β] {f : α
 -> β} {s : Set α} {a : α} (hf : ContinuousOn f s) (hx : a in s) : f '' connecte
dComponentIn s a subseteq connectedComponentIn (f '' s) (f a)
参数：hf : ContinuousOn f s；hx : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.subset_connectedComponentIn`：IsPreconnected.subset_connec
tedComponentIn {x : α} {F : Set α} (hs : IsPreconnected s) (hxs : x in s) (hsF :
 s subseteq F) : s subseteq conn…
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `isPreconnected_connectedComponentIn`：isPreconnected_connectedComponentIn
 {x : α} {F : Set α} : IsPreconnected (connectedComponentIn F x)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `connectedComponentIn_subset`：connectedComponentIn_subset (F : Set α) (x 
: α) : connectedComponentIn F x subseteq F
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `mem_connectedComponentIn`：mem_connectedComponentIn {x : α} {F : Set α} (
hx : x in F) : x in connectedComponentIn F x
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem ContinuousOn.image_connectedComponentIn_subset [TopologicalSpace β] {f : α → β} {s : Set α}
    {a : α} (hf : ContinuousOn f s) (hx : a ∈ s) :
    f '' connectedComponentIn s a ⊆ connectedComponentIn (f '' s) (f a) :=
  (isPreconnected_connectedComponentIn.image _ <| hf.mono <| connectedComponentIn_subset _ _)
    |>.subset_connectedComponentIn (mem_image_of_mem _ <| mem_connectedComponentIn hx)
      (image_mono <| connectedComponentIn_subset _ _)

@[deprecated ContinuousOn.image_connectedComponentIn_subset (since := "2026-07-27")]
/-
**Continuous.image_connectedComponentIn_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.image_connectedComponentIn_subset [TopologicalSpace β] {f : α -
> β} {s : Set α} {a : α} (hf : Continuous f) (hx : a in s) : f '' connectedCompo
nentIn s a subseteq connectedComponentIn (f '' s) (f a)
参数：hf : Continuous f；hx : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_connectedComponentIn_subset`：ContinuousOn.image_conne
ctedComponentIn_subset [TopologicalSpace β] {f : α -> β} {s : Set α} {a : α} (hf
 : ContinuousOn f s) (hx : a in s) :…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem Continuous.image_connectedComponentIn_subset [TopologicalSpace β] {f : α → β} {s : Set α}
    {a : α} (hf : Continuous f) (hx : a ∈ s) :
    f '' connectedComponentIn s a ⊆ connectedComponentIn (f '' s) (f a) :=
  hf.continuousOn.image_connectedComponentIn_subset hx
/-
**Continuous.mapsTo_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.mapsTo_connectedComponent [TopologicalSpace β] {f : α -> β} (h 
: Continuous f) (a : α) : MapsTo f (connectedComponent a) (connectedComponent (f
 a))
参数：h : Continuous f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `Continuous.image_connectedComponent_subset`：Continuous.image_connectedCo
mponent_subset [TopologicalSpace β] {f : α -> β} (h : Continuous f) (a : α) : f 
'' connectedComponent a subseteq…
-/
theorem Continuous.mapsTo_connectedComponent [TopologicalSpace β] {f : α → β} (h : Continuous f)
    (a : α) : MapsTo f (connectedComponent a) (connectedComponent (f a)) :=
  mapsTo_iff_image_subset.2 <| h.image_connectedComponent_subset a
/-
**ContinuousOn.mapsTo_connectedComponentIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.mapsTo_connectedComponentIn [TopologicalSpace β] {f : α -> β}
 {s : Set α} (h : ContinuousOn f s) {a : α} (hx : a in s) : MapsTo f (connectedC
omponentIn s a) (connectedComponentIn (f '' s) (f a))
参数：h : ContinuousOn f s；hx : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `ContinuousOn.image_connectedComponentIn_subset`：ContinuousOn.image_conne
ctedComponentIn_subset [TopologicalSpace β] {f : α -> β} {s : Set α} {a : α} (hf
 : ContinuousOn f s) (hx : a in s) :…
-/
theorem ContinuousOn.mapsTo_connectedComponentIn [TopologicalSpace β] {f : α → β} {s : Set α}
    (h : ContinuousOn f s) {a : α} (hx : a ∈ s) :
    MapsTo f (connectedComponentIn s a) (connectedComponentIn (f '' s) (f a)) :=
  mapsTo_iff_image_subset.2 <| h.image_connectedComponentIn_subset hx

@[deprecated ContinuousOn.mapsTo_connectedComponentIn (since := "2026-07-27")]
/-
**Continuous.mapsTo_connectedComponentIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.mapsTo_connectedComponentIn [TopologicalSpace β] {f : α -> β} {
s : Set α} (h : Continuous f) {a : α} (hx : a in s) : MapsTo f (connectedCompone
ntIn s a) (connectedComponentIn (f '' s) (f a))
参数：h : Continuous f；hx : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mapsTo_connectedComponentIn`：ContinuousOn.mapsTo_connectedC
omponentIn [TopologicalSpace β] {f : α -> β} {s : Set α} (h : ContinuousOn f s) 
{a : α} (hx : a in s) : MapsTo…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem Continuous.mapsTo_connectedComponentIn [TopologicalSpace β] {f : α → β} {s : Set α}
    (h : Continuous f) {a : α} (hx : a ∈ s) :
    MapsTo f (connectedComponentIn s a) (connectedComponentIn (f '' s) (f a)) :=
  h.continuousOn.mapsTo_connectedComponentIn hx

/-- The connected component of `(x, y)` in the product space is the product of the connected
components of `x` and `y`. -/
/-
**connectedComponent_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponent_prod [TopologicalSpace β] (x : α) (y : β) : connectedCo
mponent (x, y) = connectedComponent x ×ˢ connectedComponent y
参数：x : α；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Continuous.mapsTo_connectedComponent`：Continuous.mapsTo_connectedCompone
nt [TopologicalSpace β] {f : α -> β} (h : Continuous f) (a : α) : MapsTo f (conn
ectedComponent a) (connect…
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `IsPreconnected.subset_connectedComponent`：IsPreconnected.subset_connecte
dComponent {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x in s) : s subsete
q connectedComponent x
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x

--- 原说明 ---
The connected component of `(x, y)` in the product space is the product of the c
onnected
components of `x` and `y`.
-/
theorem connectedComponent_prod [TopologicalSpace β] (x : α) (y : β) :
    connectedComponent (x, y) = connectedComponent x ×ˢ connectedComponent y :=
  subset_antisymm
    (fun _ hp ↦ ⟨continuous_fst.mapsTo_connectedComponent (x, y) hp,
      continuous_snd.mapsTo_connectedComponent (x, y) hp⟩)
    (isPreconnected_connectedComponent.prod isPreconnected_connectedComponent
      |>.subset_connectedComponent ⟨mem_connectedComponent, mem_connectedComponent⟩)

/-- The connected component of `x` in a product space is the product of the connected components
of its coordinates. -/
/-
**connectedComponent_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponent_pi [forall i, TopologicalSpace (X i)] (x : forall i, X 
i) : connectedComponent x = univ.pi fun i => connectedComponent (x i)
参数：X i；x : forall i, X i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Continuous.mapsTo_connectedComponent`：Continuous.mapsTo_connectedCompone
nt [TopologicalSpace β] {f : α -> β} (h : Continuous f) (a : α) : MapsTo f (conn
ectedComponent a) (connect…
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `IsPreconnected.subset_connectedComponent`：IsPreconnected.subset_connecte
dComponent {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x in s) : s subsete
q connectedComponent x
· 使用定理 `isPreconnected_univ_pi`：isPreconnected_univ_pi [forall i, TopologicalSpa
ce (X i)] {s : forall i, Set (X i)} (hs : forall i, IsPreconnected (s i)) : IsPr
econnected (…
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
· 使用定理 `mem_connectedComponent`：mem_connectedComponent {x : α} : x in connectedC
omponent x

--- 原说明 ---
The connected component of `x` in a product space is the product of the connecte
d components
of its coordinates.
-/
theorem connectedComponent_pi [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i) :
    connectedComponent x = univ.pi fun i ↦ connectedComponent (x i) :=
  subset_antisymm (fun _ hy i _ ↦ (continuous_apply i).mapsTo_connectedComponent x hy)
    (isPreconnected_univ_pi (fun _ ↦ isPreconnected_connectedComponent)
      |>.subset_connectedComponent fun _ _ ↦ mem_connectedComponent)
/-
**irreducibleComponent_subset_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irreducibleComponent_subset_connectedComponent {x : α} : irreducibleCompon
ent x subseteq connectedComponent x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.subset_connectedComponent`：IsConnected.subset_connectedCompo
nent {x : α} {s : Set α} (H1 : IsConnected s) (H2 : x in s) : s subseteq connect
edComponent x
· 使用定理 `IsIrreducible.isConnected`：IsIrreducible.isConnected {s : Set α} (H : Is
Irreducible s) : IsConnected s
· 使用定理 `isIrreducible_irreducibleComponent`：isIrreducible_irreducibleComponent {
x : X} : IsIrreducible (irreducibleComponent x)
· 使用定理 `mem_irreducibleComponent`：mem_irreducibleComponent {x : X} : x in irredu
cibleComponent x
-/
theorem irreducibleComponent_subset_connectedComponent {x : α} :
    irreducibleComponent x ⊆ connectedComponent x :=
  isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent mem_irreducibleComponent

@[gcongr, mono]
/-
**connectedComponentIn_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedComponentIn_mono (x : α) {F G : Set α} (h : F subseteq G) : conne
ctedComponentIn F x subseteq connectedComponentIn G x
参数：x : α；h : F subseteq G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `connectedComponentIn_eq_image`：connectedComponentIn_eq_image {F : Set α}
 {x : α} (h : x in F) : connectedComponentIn F x = (↑) '' connectedComponent (⟨x
, h⟩ : F)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Continuous.image_connectedComponent_subset`：Continuous.image_connectedCo
mponent_subset [TopologicalSpace β] {f : α -> β} (h : Continuous f) (a : α) : f 
'' connectedComponent a subseteq…
· 使用定理 `continuous_inclusion`：continuous_inclusion {s t : Set X} (h : s subseteq
 t) : Continuous (inclusion h)
· 使用定理 `connectedComponentIn_eq_empty`：connectedComponentIn_eq_empty {F : Set α}
 {x : α} (h : x ∉ F) : connectedComponentIn F x = ∅
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem connectedComponentIn_mono (x : α) {F G : Set α} (h : F ⊆ G) :
    connectedComponentIn F x ⊆ connectedComponentIn G x := by
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image (h hx), ←
      show ((↑) : G → α) ∘ inclusion h = (↑) from rfl, image_comp]
    exact image_mono ((continuous_inclusion h).image_connectedComponent_subset ⟨x, hx⟩)
  · rw [connectedComponentIn_eq_empty hx]
    exact Set.empty_subset _

/-- The preimage of a connected component of `F` is the union of the connected components of
`f ⁻¹' F` at the points of that preimage. -/
/-
**ContinuousOn.preimage_connectedComponentIn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.preimage_connectedComponentIn [TopologicalSpace β] {f : α -> 
β} {F : Set β} (hf : ContinuousOn f (f ⁻¹' F)) (y : β) : f ⁻¹' connectedComponen
tIn F y = ⋃ x in f ⁻¹' connectedComponentIn F y, connectedComponentIn (f ⁻¹' F) 
x
参数：hf : ContinuousOn f (f ⁻¹' F)；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `mem_connectedComponentIn`：mem_connectedComponentIn {x : α} {F : Set α} (
hx : x in F) : x in connectedComponentIn F x
· 使用定理 `connectedComponentIn_subset`：connectedComponentIn_subset (F : Set α) (x 
: α) : connectedComponentIn F x subseteq F
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `connectedComponentIn_eq`：connectedComponentIn_eq {x y : α} {F : Set α} (
h : y in connectedComponentIn F x) : connectedComponentIn F x = connectedCompone
ntIn F y
· 使用定理 `connectedComponentIn_mono`：connectedComponentIn_mono (x : α) {F G : Set 
α} (h : F subseteq G) : connectedComponentIn F x subseteq connectedComponentIn G
 x
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `ContinuousOn.mapsTo_connectedComponentIn`：ContinuousOn.mapsTo_connectedC
omponentIn [TopologicalSpace β] {f : α -> β} {s : Set α} (h : ContinuousOn f s) 
{a : α} (hx : a in s) : MapsTo…

--- 原说明 ---
The preimage of a connected component of `F` is the union of the connected compo
nents of
`f ⁻¹' F` at the points of that preimage.
-/
theorem ContinuousOn.preimage_connectedComponentIn [TopologicalSpace β] {f : α → β} {F : Set β}
    (hf : ContinuousOn f (f ⁻¹' F)) (y : β) :
    f ⁻¹' connectedComponentIn F y =
      ⋃ x ∈ f ⁻¹' connectedComponentIn F y, connectedComponentIn (f ⁻¹' F) x := by
  refine subset_antisymm (fun z hz ↦ ?_) (iUnion₂_subset fun x hx z hz ↦ ?_)
  · exact mem_biUnion hz (mem_connectedComponentIn (connectedComponentIn_subset F y hz))
  · rw [mem_preimage, connectedComponentIn_eq hx]
    exact connectedComponentIn_mono _ (image_preimage_subset f F)
      (hf.mapsTo_connectedComponentIn (connectedComponentIn_subset F y hx) hz)

/-- The preimage of a connected component is the union of the connected components at the points
of that preimage. -/
/-
**Continuous.preimage_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.preimage_connectedComponent [TopologicalSpace β] {f : α -> β} (
hf : Continuous f) (y : β) : f ⁻¹' connectedComponent y = ⋃ x in f ⁻¹' connected
Component y, connectedComponent x
参数：hf : Continuous f；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `connectedComponentIn_univ`：connectedComponentIn_univ (x : α) : connected
ComponentIn univ x = connectedComponent x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousOn.preimage_connectedComponentIn`：ContinuousOn.preimage_connec
tedComponentIn [TopologicalSpace β] {f : α -> β} {F : Set β} (hf : ContinuousOn 
f (f ⁻¹' F)) (y : β) : f ⁻¹' con…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
The preimage of a connected component is the union of the connected components a
t the points
of that preimage.
-/
theorem Continuous.preimage_connectedComponent [TopologicalSpace β] {f : α → β}
    (hf : Continuous f) (y : β) :
    f ⁻¹' connectedComponent y = ⋃ x ∈ f ⁻¹' connectedComponent y, connectedComponent x := by
  simpa [connectedComponentIn_univ] using
    hf.continuousOn.preimage_connectedComponentIn (F := univ) y

/-- A preconnected space is one where there is no non-trivial open partition. -/
/-
**PreconnectedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preconnected space is one where there is no non-trivial open partition.
-/
class PreconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a preconnected space is a preconnected set. -/
  isPreconnected_univ : IsPreconnected (univ : Set α)

export PreconnectedSpace (isPreconnected_univ)

/-- A connected space is a nonempty one where there is no non-trivial open partition. -/
@[wikidata Q1491995, mk_iff]
/-
**ConnectedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A connected space is a nonempty one where there is no non-trivial open partition
.
-/
class ConnectedSpace (α : Type u) [TopologicalSpace α] : Prop extends PreconnectedSpace α where
  /-- A connected space is nonempty. -/
  toNonempty : Nonempty α

attribute [instance 50] ConnectedSpace.toNonempty  -- see Note [lower instance priority]

-- see Note [lower instance priority]
/-
**isConnected_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_univ [ConnectedSpace α] : IsConnected (univ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
-/
theorem isConnected_univ [ConnectedSpace α] : IsConnected (univ : Set α) :=
  ⟨univ_nonempty, isPreconnected_univ⟩
/-
**preconnectedSpace_iff_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：preconnectedSpace_iff_univ : PreconnectedSpace α ↔ IsPreconnected (univ : 
Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
-/
lemma preconnectedSpace_iff_univ : PreconnectedSpace α ↔ IsPreconnected (univ : Set α) :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩
/-
**connectedSpace_iff_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：connectedSpace_iff_univ : ConnectedSpace α ↔ IsConnected (univ : Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma connectedSpace_iff_univ : ConnectedSpace α ↔ IsConnected (univ : Set α) :=
  ⟨fun h ↦ ⟨univ_nonempty, h.1.1⟩,
   fun h ↦ ConnectedSpace.mk (toPreconnectedSpace := ⟨h.2⟩) ⟨h.1.some⟩⟩
/-
**isPreconnected_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_range [TopologicalSpace β] [PreconnectedSpace α] {f : α -> 
β} (h : Continuous f) : IsPreconnected (range f)
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem isPreconnected_range [TopologicalSpace β] [PreconnectedSpace α] {f : α → β}
    (h : Continuous f) : IsPreconnected (range f) :=
  @image_univ _ _ f ▸ isPreconnected_univ.image _ h.continuousOn
/-
**isConnected_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_range [TopologicalSpace β] [ConnectedSpace α] {f : α -> β} (h 
: Continuous f) : IsConnected (range f)
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `isPreconnected_range`：isPreconnected_range [TopologicalSpace β] [Preconn
ectedSpace α] {f : α -> β} (h : Continuous f) : IsPreconnected (range f)
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
-/
theorem isConnected_range [TopologicalSpace β] [ConnectedSpace α] {f : α → β} (h : Continuous f) :
    IsConnected (range f) :=
  ⟨range_nonempty f, isPreconnected_range h⟩
/-
**Function.Surjective.connectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.connectedSpace [ConnectedSpace α] [TopologicalSpace β]
 {f : α -> β} (hf : Surjective f) (hf' : Continuous f) : ConnectedSpace β
参数：hf : Surjective f；hf' : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `connectedSpace_iff_univ`：connectedSpace_iff_univ : ConnectedSpace α ↔ Is
Connected (univ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `isConnected_range`：isConnected_range [TopologicalSpace β] [ConnectedSpac
e α] {f : α -> β} (h : Continuous f) : IsConnected (range f)
-/
theorem Function.Surjective.connectedSpace [ConnectedSpace α] [TopologicalSpace β]
    {f : α → β} (hf : Surjective f) (hf' : Continuous f) : ConnectedSpace β := by
  rw [connectedSpace_iff_univ, ← hf.range_eq]
  exact isConnected_range hf'
/-
**Homeomorph.connectedSpace_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Homeomorph.connectedSpace_iff [TopologicalSpace β] (e : α ≃ₜ β) : Connecte
dSpace α ↔ ConnectedSpace β
参数：e : α ≃ₜ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.connectedSpace`：Function.Surjective.connectedSpace [
ConnectedSpace α] [TopologicalSpace β] {f : α -> β} (hf : Surjective f) (hf' : C
ontinuous f) : Connected…
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
-/
lemma Homeomorph.connectedSpace_iff [TopologicalSpace β] (e : α ≃ₜ β) :
    ConnectedSpace α ↔ ConnectedSpace β :=
  ⟨fun _ ↦ e.surjective.connectedSpace e.continuous,
    fun _ ↦ e.symm.surjective.connectedSpace e.symm.continuous⟩
/-
**Quotient.instConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.instConnectedSpace {s : Setoid α} [ConnectedSpace α] : ConnectedS
pace (Quotient s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.connectedSpace`：Function.Surjective.connectedSpace [
ConnectedSpace α] [TopologicalSpace β] {f : α -> β} (hf : Surjective f) (hf' : C
ontinuous f) : Connected…
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Quotient.mk'_surjective`：∀ {α : Sort u_1} [s : Setoid α], Function.Surje
ctive Quotient.mk'
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
-/
instance Quotient.instConnectedSpace {s : Setoid α} [ConnectedSpace α] :
    ConnectedSpace (Quotient s) :=
  Quotient.mk'_surjective.connectedSpace continuous_coinduced_rng
/-
**DenseRange.preconnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.preconnectedSpace [TopologicalSpace β] [PreconnectedSpace α] {f
 : α -> β} (hf : DenseRange f) (hc : Continuous f) : PreconnectedSpace β
参数：hf : DenseRange f；hc : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.closure`：∀ {α : Type u} [inst : TopologicalSpace α] {s : 
Set α}, IsPreconnected s → IsPreconnected (closure s)
· 使用定理 `isPreconnected_range`：isPreconnected_range [TopologicalSpace β] [Preconn
ectedSpace α] {f : α -> β} (h : Continuous f) : IsPreconnected (range f)
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
-/
theorem DenseRange.preconnectedSpace [TopologicalSpace β] [PreconnectedSpace α] {f : α → β}
    (hf : DenseRange f) (hc : Continuous f) : PreconnectedSpace β :=
  ⟨hf.closure_eq ▸ (isPreconnected_range hc).closure⟩
/-
**connectedSpace_iff_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：connectedSpace_iff_connectedComponent : ConnectedSpace α ↔ exists x : α, c
onnectedComponent x = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_univ_subset`：∀ {α : Type u} {s : Set α}, Set.univ ⊆ s → s
 = Set.univ
· 使用定理 `IsPreconnected.subset_connectedComponent`：IsPreconnected.subset_connecte
dComponent {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x in s) : s subsete
q connectedComponent x
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
-/
theorem connectedSpace_iff_connectedComponent :
    ConnectedSpace α ↔ ∃ x : α, connectedComponent x = univ := by
  constructor
  · rintro ⟨⟨x⟩⟩
    exact
      ⟨x, eq_univ_of_univ_subset <| isPreconnected_univ.subset_connectedComponent (mem_univ x)⟩
  · rintro ⟨x, h⟩
    have : PreconnectedSpace α :=
      ⟨by rw [← h]; exact isPreconnected_connectedComponent⟩
    exact ⟨⟨x⟩⟩
/-
**preconnectedSpace_iff_connectedComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preconnectedSpace_iff_connectedComponent : PreconnectedSpace α ↔ forall x 
: α, connectedComponent x = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_univ_subset`：∀ {α : Type u} {s : Set α}, Set.univ ⊆ s → s
 = Set.univ
· 使用定理 `IsPreconnected.subset_connectedComponent`：IsPreconnected.subset_connecte
dComponent {x : α} {s : Set α} (H1 : IsPreconnected s) (H2 : x in s) : s subsete
q connectedComponent x
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.univ_eq_empty_iff`：univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty 
α
· 使用定理 `isPreconnected_empty`：isPreconnected_empty : IsPreconnected (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isPreconnected_connectedComponent`：isPreconnected_connectedComponent {x 
: α} : IsPreconnected (connectedComponent x)
-/
theorem preconnectedSpace_iff_connectedComponent :
    PreconnectedSpace α ↔ ∀ x : α, connectedComponent x = univ := by
  constructor
  · intro h x
    exact eq_univ_of_univ_subset <| isPreconnected_univ.subset_connectedComponent (mem_univ x)
  · intro h
    rcases isEmpty_or_nonempty α with hα | hα
    · exact ⟨by rw [univ_eq_empty_iff.mpr hα]; exact isPreconnected_empty⟩
    · exact ⟨by rw [← h (Classical.choice hα)]; exact isPreconnected_connectedComponent⟩

@[simp]
/-
**PreconnectedSpace.connectedComponent_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PreconnectedSpace.connectedComponent_eq_univ {X : Type*} [TopologicalSpace
 X] [h : PreconnectedSpace X] (x : X) : connectedComponent x = univ
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `preconnectedSpace_iff_connectedComponent`：preconnectedSpace_iff_connecte
dComponent : PreconnectedSpace α ↔ forall x : α, connectedComponent x = univ
-/
theorem PreconnectedSpace.connectedComponent_eq_univ {X : Type*} [TopologicalSpace X]
    [h : PreconnectedSpace X] (x : X) : connectedComponent x = univ :=
  preconnectedSpace_iff_connectedComponent.mp h x
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace β] [PreconnectedSpace α] [PreconnectedSpace β] :
    PreconnectedSpace (α × β) :=
  ⟨by
    rw [← univ_prod_univ]
    exact isPreconnected_univ.prod isPreconnected_univ⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace β] [ConnectedSpace α] [ConnectedSpace β] : ConnectedSpace (α × β) :=
  ⟨inferInstance⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, TopologicalSpace (X i)] [∀ i, PreconnectedSpace (X i)] :
    PreconnectedSpace (∀ i, X i) :=
  ⟨by rw [← pi_univ univ]; exact isPreconnected_univ_pi fun i => isPreconnected_univ⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, TopologicalSpace (X i)] [∀ i, ConnectedSpace (X i)] : ConnectedSpace (∀ i, X i) :=
  ⟨inferInstance⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PreirreducibleSpace.preconnectedSpace (α : Type u) [TopologicalSpace α]
    [PreirreducibleSpace α] : PreconnectedSpace α :=
  ⟨isPreirreducible_univ.isPreconnected⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IrreducibleSpace.connectedSpace (α : Type u) [TopologicalSpace α]
    [IrreducibleSpace α] : ConnectedSpace α where toNonempty := IrreducibleSpace.toNonempty
/-
**Subtype.preconnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.preconnectedSpace {s : Set α} (h : IsPreconnected s) : Preconnecte
dSpace s where isPreconnected_univ
参数：h : IsPreconnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.isPreconnected_image`：Topology.IsInducing.isPreconne
cted_image [TopologicalSpace β] {s : Set α} {f : α -> β} (hf : IsInducing f) : I
sPreconnected (f '' s) ↔ IsPre…
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
-/
theorem Subtype.preconnectedSpace {s : Set α} (h : IsPreconnected s) : PreconnectedSpace s where
  isPreconnected_univ := by
    rwa [← IsInducing.subtypeVal.isPreconnected_image, image_univ, Subtype.range_val]
/-
**Subtype.connectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subtype.connectedSpace {s : Set α} (h : IsConnected s) : ConnectedSpace s 
where toPreconnectedSpace
参数：h : IsConnected s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.preconnectedSpace`：Subtype.preconnectedSpace {s : Set α} (h : Is
Preconnected s) : PreconnectedSpace s where isPreconnected_univ
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
-/
theorem Subtype.connectedSpace {s : Set α} (h : IsConnected s) : ConnectedSpace s where
  toPreconnectedSpace := Subtype.preconnectedSpace h.isPreconnected
  toNonempty := h.nonempty.to_subtype
/-
**isPreconnected_iff_preconnectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPreconnected_iff_preconnectedSpace {s : Set α} : IsPreconnected s ↔ Prec
onnectedSpace s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.preconnectedSpace`：Subtype.preconnectedSpace {s : Set α} (h : Is
Preconnected s) : PreconnectedSpace s where isPreconnected_univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem isPreconnected_iff_preconnectedSpace {s : Set α} : IsPreconnected s ↔ PreconnectedSpace s :=
  ⟨Subtype.preconnectedSpace, fun h => by
    simpa using isPreconnected_univ.image ((↑) : s → α) continuous_subtype_val.continuousOn⟩
/-
**isConnected_iff_connectedSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConnected_iff_connectedSpace {s : Set α} : IsConnected s ↔ ConnectedSpac
e s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.connectedSpace`：Subtype.connectedSpace {s : Set α} (h : IsConnec
ted s) : ConnectedSpace s where toPreconnectedSpace
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPreconnected_iff_preconnectedSpace`：isPreconnected_iff_preconnectedSpa
ce {s : Set α} : IsPreconnected s ↔ PreconnectedSpace s
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
-/
theorem isConnected_iff_connectedSpace {s : Set α} : IsConnected s ↔ ConnectedSpace s :=
  ⟨Subtype.connectedSpace, fun h =>
    ⟨nonempty_subtype.mp h.2, isPreconnected_iff_preconnectedSpace.mpr h.1⟩⟩

end Preconnected

