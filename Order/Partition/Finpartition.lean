/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Order.Atoms
public import Mathlib.Order.SupIndep

/-!
# Finite partitions

In this file, we define finite partitions. A finpartition of `a : α` is a finite set of pairwise
disjoint parts `parts : Finset α` which does not contain `⊥` and whose supremum is `a`.

Finpartitions of a finset are at the heart of Szemerédi's regularity lemma. They are also studied
purely order theoretically in Sperner theory.

## Constructions

We provide many ways to build finpartitions:
* `Finpartition.ofErase`: Builds a finpartition by erasing `⊥` for you.
* `Finpartition.ofSubset`: Builds a finpartition from a subset of the parts of a previous
  finpartition.
* `Finpartition.empty`: The empty finpartition of `⊥`.
* `Finpartition.indiscrete`: The indiscrete, aka trivial, aka pure, finpartition made of a single
  part.
* `Finpartition.discrete`: The discrete finpartition of `s : Finset α` made of singletons.
* `Finpartition.toSubtype`: Turns a finpartition of a type to one of a subtype.
* `Finpartition.bind`: Puts together the finpartitions of the parts of a finpartition into a new
  finpartition.
* `Finpartition.extend`: Extends a finpartition of `a` to a finpartition of `a ⊔ b` by adding `b`
  as a new part.
* `Finpartition.extendOfLE`: Extends a finpartition of `a` to a finpartition of `b` when `a ≤ b`,
  by adding `b \ a` as a new part (if nonempty).
* `Finpartition.restrict`: Restricts a finpartition of `a` to `b` where `b ≤ a` by intersecting
  each part with `b`.
* `Finpartition.ofPairwiseDisjoint`: Builds a finpartition from a finset `parts` of pairwise
  disjoint elements.
* `Finpartition.combine`: Combines a family of partitions of pairwise disjoint elements into a
  partition of their sup.
* `Finpartition.ofExistsUnique`: Builds a finpartition from a collection of parts such that each
  element is in exactly one part.
* `Finpartition.ofSetoid`: With `Fintype α`, constructs the finpartition of `univ : Finset α`
  induced by the equivalence classes of `s : Setoid α`.
* `Finpartition.atomise`: Makes a finpartition of `s : Finset α` by breaking `s` along all finsets
  in `F : Finset (Finset α)`. Two elements of `s` belong to the same part iff they belong to the
  same elements of `F`.

`Finpartition.indiscrete` and `Finpartition.bind` together form the monadic structure of
`Finpartition`.

## Implementation notes

Forbidding `⊥` as a part follows mathematical tradition and is a pragmatic choice concerning
operations on `Finpartition`. Not caring about `⊥` being a part or not breaks extensionality (it's
not because the parts of `P` and the parts of `Q` have the same elements that `P = Q`). Enforcing
`⊥` to be a part makes `Finpartition.bind` uglier and doesn't rid us of the need of
`Finpartition.ofErase`.

## TODO

The order is the wrong way around to make `Finpartition a` a graded order. Is it bad to depart from
the literature and turn the order around?

The specialisation to `Finset α` could be generalised to atomistic orders.
-/

@[expose] public section


open Finset Function

variable {α : Type*}

/-- A finite partition of `a : α` is a pairwise disjoint finite set of elements whose supremum is
`a`. We forbid `⊥` as a part. -/
@[ext]
/-
**Finpartition** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [inst : Lattice α] → [OrderBot α] → α → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite partition of `a : α` is a pairwise disjoint finite set of elements whos
e supremum is
`a`. We forbid `⊥` as a part.
-/
structure Finpartition [Lattice α] [OrderBot α] (a : α) where
  /-- The elements of the finite partition of `a` -/
  parts : Finset α
  /-- The partition is supremum-independent -/
  protected supIndep : parts.SupIndep id
  /-- The supremum of the partition is `a` -/
  sup_parts : parts.sup id = a
  /-- No element of the partition is bottom -/
  bot_notMem : ⊥ ∉ parts
  deriving DecidableEq

namespace Finpartition

section Lattice

variable [Lattice α] [OrderBot α]

/-- A `Finpartition` constructor which does not insist on `⊥` not being a part. -/
@[simps]
/-
**Finpartition.ofErase** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：ofErase [DecidableEq α] {a : α} (parts : Finset α) (sup_indep : parts.SupI
ndep id) (sup_parts : parts.sup id = a) : Finpartition a where parts
参数：parts : Finset α；sup_indep : parts.SupIndep id；sup_parts : parts.sup id = a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Finpartition` constructor which does not insist on `⊥` not being a part.
-/
def ofErase [DecidableEq α] {a : α} (parts : Finset α) (sup_indep : parts.SupIndep id)
    (sup_parts : parts.sup id = a) : Finpartition a where
  parts := parts.erase ⊥
  supIndep := sup_indep.subset (erase_subset _ _)
  sup_parts := (sup_erase_bot _).trans sup_parts
  bot_notMem := notMem_erase _ _

/-- A `Finpartition` constructor from a bigger existing finpartition. -/
@[simps]
/-
**Finpartition.ofSubset** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：ofSubset {a b : α} (P : Finpartition a) {parts : Finset α} (subset : parts
 subseteq P.parts) (sup_parts : parts.sup id = b) : Finpartition b
参数：P : Finpartition a；subset : parts subseteq P.parts；sup_parts : parts.sup id =
 b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Finpartition` constructor from a bigger existing finpartition.
-/
def ofSubset {a b : α} (P : Finpartition a) {parts : Finset α} (subset : parts ⊆ P.parts)
    (sup_parts : parts.sup id = b) : Finpartition b :=
  { parts := parts
    supIndep := P.supIndep.subset subset
    sup_parts := sup_parts
    bot_notMem := fun h ↦ P.bot_notMem (subset h) }
/-
**Finpartition.sum_ofSubset_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：sum_ofSubset_eq_sum {a b : α} (P : Finpartition a) {parts : Finset α} (sub
set : parts subseteq P.parts) (sup_parts : parts.sup id = b) {X : Type*} [AddCom
mMonoid X] (f : α -> X) (hf : forall p in P.parts, p ∉ parts -> f p = 0) : ∑ p i
n (P.ofSubset subset sup_parts).parts, f p = ∑ p in P.parts, f p
参数：P : Finpartition a；subset : parts subseteq P.parts；sup_parts : parts.sup id =
 b；f : α -> X；hf : forall p in P.parts, p ∉ parts -> f p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
-/
lemma sum_ofSubset_eq_sum {a b : α} (P : Finpartition a) {parts : Finset α}
    (subset : parts ⊆ P.parts) (sup_parts : parts.sup id = b)
    {X : Type*} [AddCommMonoid X] (f : α → X) (hf : ∀ p ∈ P.parts, p ∉ parts → f p = 0) :
    ∑ p ∈ (P.ofSubset subset sup_parts).parts, f p = ∑ p ∈ P.parts, f p :=
  Finset.sum_subset subset hf

/-- Changes the type of a finpartition to an equal one. -/
@[simps]
/-
**Finpartition.copy** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：copy {a b : α} (P : Finpartition a) (h : a = b) : Finpartition b where par
ts
参数：P : Finpartition a；h : a = b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.supIndep`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (self : Finpartition a), self.parts.SupIndep id
· 使用定理 `Finpartition.bot_notMem`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : O
rderBot α] {a : α} (self : Finpartition a), ⊥ ∉ self.parts

--- 原说明 ---
Changes the type of a finpartition to an equal one.
-/
def copy {a b : α} (P : Finpartition a) (h : a = b) : Finpartition b where
  parts := P.parts
  supIndep := P.supIndep
  sup_parts := h ▸ P.sup_parts
  bot_notMem := P.bot_notMem

/-- Transfer a finpartition over an order isomorphism. -/
/-
**Finpartition.map** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：map {β : Type*} [Lattice β] [OrderBot β] {a : α} (e : α ≃o β) (P : Finpart
ition a) : Finpartition (e a) where parts
参数：e : α ≃o β；P : Finpartition a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer a finpartition over an order isomorphism.
-/
def map {β : Type*} [Lattice β] [OrderBot β] {a : α} (e : α ≃o β) (P : Finpartition a) :
    Finpartition (e a) where
  parts := P.parts.map e
  supIndep u hu _ hb hbu _ hx hxu := by
    rw [← map_symm_subset] at hu
    simp only [mem_map_equiv] at hb
    have := P.supIndep hu hb (by simp [hbu]) (map_rel e.symm hx) ?_
    · rw [← e.symm.map_bot] at this
      exact e.symm.map_rel_iff.mp this
    · convert! e.symm.map_rel_iff.mpr hxu
      rw [map_finset_sup, sup_map]
      rfl
  sup_parts := by simp [← P.sup_parts]
  bot_notMem := by
    rw [mem_map_equiv]
    convert! P.bot_notMem
    exact e.symm.map_bot

@[simp]
/-
**Finpartition.parts_map** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：parts_map {β : Type*} [Lattice β] [OrderBot β] {a : α} {e : α ≃o β} {P : F
inpartition a} : (P.map e).parts = P.parts.map e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parts_map {β : Type*} [Lattice β] [OrderBot β] {a : α} {e : α ≃o β} {P : Finpartition a} :
    (P.map e).parts = P.parts.map e := rfl

variable (α)

/-- The empty finpartition. -/
@[simps]
/-
**Finpartition.empty** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：(α : Type u_1) → [inst : Lattice α] → [inst_1 : OrderBot α] → Finpartition
 ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty finpartition.
-/
protected def empty : Finpartition (⊥ : α) where
  parts := ∅
  supIndep := supIndep_empty _
  sup_parts := Finset.sup_empty
  bot_notMem := notMem_empty ⊥
/-
**Finpartition.** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Finpartition (⊥ : α)) :=
  ⟨Finpartition.empty α⟩

@[simp]
/-
**Finpartition.default_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：default_eq_empty : (default : Finpartition (⊥ : α)) = Finpartition.empty α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem default_eq_empty : (default : Finpartition (⊥ : α)) = Finpartition.empty α :=
  rfl

variable {α} {a : α}

/-- The finpartition in one part, aka indiscrete finpartition. -/
@[simps]
/-
**Finpartition.indiscrete** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：indiscrete (ha : a != ⊥) : Finpartition a where parts
参数：ha : a != ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finpartition in one part, aka indiscrete finpartition.
-/
def indiscrete (ha : a ≠ ⊥) : Finpartition a where
  parts := {a}
  supIndep := supIndep_singleton _ _
  sup_parts := Finset.sup_singleton
  bot_notMem h := ha (mem_singleton.1 h).symm

variable (P : Finpartition a)
/-
**Finpartition.le** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot α] {a : α} (P : Fin
partition a) {b : α}, b ∈ P.parts → b ≤ a
参数：P : Finpartition a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
-/
protected theorem le {b : α} (hb : b ∈ P.parts) : b ≤ a :=
  (le_sup hb).trans P.sup_parts.le
/-
**Finpartition.ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：ne_bot {b : α} (hb : b in P.parts) : b != ⊥
参数：hb : b in P.parts。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.bot_notMem`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : O
rderBot α] {a : α} (self : Finpartition a), ⊥ ∉ self.parts
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ne_bot {b : α} (hb : b ∈ P.parts) : b ≠ ⊥ := by
  intro h
  refine P.bot_notMem (?_)
  rw [h] at hb
  exact hb
/-
**Finpartition.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot α] {a : α} (P : Fin
partition a), (↑P.parts).PairwiseDisjoint id
参数：P : Finpartition a；↑P.parts。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.SupIndep.pairwiseDisjoint`：∀ {α : Type u_1} {ι : Type u_3} [inst 
: Lattice α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α},   s.SupIndep f → 
(↑s).PairwiseDisjoint …
· 使用定理 `Finpartition.supIndep`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (self : Finpartition a), self.parts.SupIndep id
-/
protected theorem disjoint : (P.parts : Set α).PairwiseDisjoint id :=
  P.supIndep.pairwiseDisjoint

section Apply

variable {β : Type*} {f : α → β}

/-- The `sup` of a sup-bot-preserving map `f` over the parts of a `Finpartition` equals `f a`. -/
/-
**Finpartition.sup_parts_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：sup_parts_apply [SemilatticeSup β] [OrderBot β] (hf : forall x y, f (x ⊔ y
) = f x ⊔ f y) (hbot : f ⊥ = ⊥) : P.parts.sup f = f a
参数：hf : forall x y, f (x ⊔ y) = f x ⊔ f y；hbot : f ⊥ = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.apply_sup_eq_sup_comp`：apply_sup_eq_sup_comp [SemilatticeSup γ] [
OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ) (g_sup : forall x y, g (x ⊔
 y) = g x ⊔ g y) (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a

--- 原说明 ---
The `sup` of a sup-bot-preserving map `f` over the parts of a `Finpartition` equ
als `f a`.
-/
theorem sup_parts_apply [SemilatticeSup β] [OrderBot β] (hf : ∀ x y, f (x ⊔ y) = f x ⊔ f y)
    (hbot : f ⊥ = ⊥) : P.parts.sup f = f a :=
  (apply_sup_eq_sup_comp f hf hbot).symm.trans (congrArg f P.sup_parts)

/-- Parts of a `Finpartition` are pairwise disjoint under an inf-bot-preserving map. -/
/-
**Finpartition.pairwiseDisjoint_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：pairwiseDisjoint_apply [SemilatticeInf β] [OrderBot β] (hf : forall x y, f
 (x ⊓ y) = f x ⊓ f y) (hbot : f ⊥ = ⊥) : (P.parts : Set α).PairwiseDisjoint f
参数：hf : forall x y, f (x ⊓ y) = f x ⊓ f y；hbot : f ⊥ = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Parts of a `Finpartition` are pairwise disjoint under an inf-bot-preserving map.
-/
theorem pairwiseDisjoint_apply [SemilatticeInf β] [OrderBot β] (hf : ∀ x y, f (x ⊓ y) = f x ⊓ f y)
    (hbot : f ⊥ = ⊥) : (P.parts : Set α).PairwiseDisjoint f := by
  intro _ hx _ hy hxy
  have := (P.disjoint hx hy hxy).eq_bot
  simp_all [disjoint_iff, ← hf]

end Apply

variable {P}

@[simp]
/-
**Finpartition.parts_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：parts_eq_empty_iff : P.parts = ∅ ↔ a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Finse
t α} : s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Finpartition.bot_notMem`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : O
rderBot α] {a : α} (self : Finpartition a), ⊥ ∉ self.parts
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem parts_eq_empty_iff : P.parts = ∅ ↔ a = ⊥ := by
  simp_rw [← P.sup_parts]
  refine ⟨fun h ↦ ?_, fun h ↦ eq_empty_iff_forall_notMem.2 fun b hb ↦ P.bot_notMem ?_⟩
  · rw [h]
    exact Finset.sup_empty
  · rwa [← le_bot_iff.1 ((le_sup hb).trans h.le)]

@[simp]
/-
**Finpartition.parts_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：parts_nonempty_iff : P.parts.Nonempty ↔ a != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.parts_eq_empty_iff`：parts_eq_empty_iff : P.parts = ∅ ↔ a = 
⊥
-/
theorem parts_nonempty_iff : P.parts.Nonempty ↔ a ≠ ⊥ := by
  contrapose!; exact parts_eq_empty_iff
/-
**Finpartition.parts_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：parts_nonempty (P : Finpartition a) (ha : a != ⊥) : P.parts.Nonempty
参数：P : Finpartition a；ha : a != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finpartition.parts_nonempty_iff`：parts_nonempty_iff : P.parts.Nonempty ↔
 a != ⊥
-/
theorem parts_nonempty (P : Finpartition a) (ha : a ≠ ⊥) : P.parts.Nonempty :=
  parts_nonempty_iff.2 ha
/-
**Finpartition.** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (Finpartition (⊥ : α)) :=
  { (inferInstance : Inhabited (Finpartition (⊥ : α))) with
    uniq := fun P ↦ by
      ext a
      exact iff_of_false (fun h ↦ P.ne_bot h <| le_bot_iff.1 <| P.le h) (notMem_empty a) }
/-
**Finpartition.instNonempty** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
形式化陈述：instNonempty : Nonempty (Finpartition a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance instNonempty : Nonempty (Finpartition a) := by
  by_cases h : a = ⊥
  · rw [h]; exact ⟨Finpartition.empty α⟩
  · exact ⟨Finpartition.indiscrete h⟩

-- See note [reducible non-instances]
/-- There's a unique partition of an atom. -/
/-
**Finpartition._root_.IsAtom.uniqueFinpartition** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fin
partition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There's a unique partition of an atom.
-/
abbrev _root_.IsAtom.uniqueFinpartition (ha : IsAtom a) : Unique (Finpartition a) where
  default := indiscrete ha.1
  uniq P := by
    have h : ∀ b ∈ P.parts, b = a := fun _ hb ↦
      (ha.le_iff.mp <| P.le hb).resolve_left (P.ne_bot hb)
    ext b
    refine Iff.trans ⟨h b, ?_⟩ mem_singleton.symm
    rintro rfl
    obtain ⟨c, hc⟩ := P.parts_nonempty ha.1
    simp_rw [← h c hc]
    exact hc
/-
**Finpartition.** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype α] [DecidableEq α] (a : α) : Fintype (Finpartition a) :=
  @Fintype.ofSurjective { p : Finset α // p.SupIndep id ∧ p.sup id = a ∧ ⊥ ∉ p } (Finpartition a) _
    (Subtype.fintype _) (fun i ↦ ⟨i.1, i.2.1, i.2.2.1, i.2.2.2⟩) fun ⟨_, y, z, w⟩ ↦
    ⟨⟨_, y, z, w⟩, rfl⟩

/-! ### Refinement order -/


section Order

/-- We say that `P ≤ Q` if `P` refines `Q`: each part of `P` is less than some part of `Q`. -/
/-
**Finpartition.** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `P ≤ Q` if `P` refines `Q`: each part of `P` is less than some part 
of `Q`.
-/
instance : LE (Finpartition a) :=
  ⟨fun P Q ↦ ∀ ⦃b⦄, b ∈ P.parts → ∃ c ∈ Q.parts, b ≤ c⟩
/-
**Finpartition.** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Finpartition a) :=
  { (inferInstance : LE (Finpartition a)) with
    le_refl := fun _ b hb ↦ ⟨b, hb, le_rfl⟩
    le_trans := fun _ Q R hPQ hQR b hb ↦ by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      obtain ⟨d, hd, hcd⟩ := hQR hc
      exact ⟨d, hd, hbc.trans hcd⟩
    le_antisymm := fun P Q hPQ hQP ↦ by
      ext b
      refine ⟨fun hb ↦ ?_, fun hb ↦ ?_⟩
      · obtain ⟨c, hc, hbc⟩ := hPQ hb
        obtain ⟨d, hd, hcd⟩ := hQP hc
        rwa [hbc.antisymm]
        rwa [P.disjoint.eq_of_le hb hd (P.ne_bot hb) (hbc.trans hcd)]
      · obtain ⟨c, hc, hbc⟩ := hQP hb
        obtain ⟨d, hd, hcd⟩ := hPQ hc
        rwa [hbc.antisymm]
        rwa [Q.disjoint.eq_of_le hb hd (Q.ne_bot hb) (hbc.trans hcd)] }
/-
**Finpartition.** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Decidable (a = ⊥)] : OrderTop (Finpartition a) where
  top := if ha : a = ⊥ then (Finpartition.empty α).copy ha.symm else indiscrete ha
  le_top P := by
    split_ifs with h
    · intro x hx
      simpa [h, P.ne_bot hx] using P.le hx
    · exact fun b hb ↦ ⟨a, mem_singleton_self _, P.le hb⟩
/-
**Finpartition.parts_top_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：parts_top_subset (a : α) [Decidable (a = ⊥)] : (⊤ : Finpartition a).parts 
subseteq {a}
参数：a : α；a = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.copy_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : O
rderBot α] {a b : α} (P : Finpartition a) (h : a = b),   (P.copy h).parts = P.pa
rts
· 使用定理 `Finpartition.empty_parts`：∀ (α : Type u_1) [inst : Lattice α] [inst_1 : 
OrderBot α], (Finpartition.empty α).parts = ∅
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem parts_top_subset (a : α) [Decidable (a = ⊥)] : (⊤ : Finpartition a).parts ⊆ {a} := by
  intro b hb
  have hb : b ∈ Finpartition.parts (dite _ _ _) := hb
  split_ifs at hb
  · simp only [copy_parts, empty_parts, notMem_empty] at hb
  · exact hb
/-
**Finpartition.parts_top_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：parts_top_subsingleton (a : α) [Decidable (a = ⊥)] : ((⊤ : Finpartition a)
.parts : Set α).Subsingleton
参数：a : α；a = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_of_subset_singleton`：subsingleton_of_subset_singleton (
h : s subseteq {a}) : s.Subsingleton
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finpartition.parts_top_subset`：parts_top_subset (a : α) [Decidable (a = 
⊥)] : (⊤ : Finpartition a).parts subseteq {a}
-/
theorem parts_top_subsingleton (a : α) [Decidable (a = ⊥)] :
    ((⊤ : Finpartition a).parts : Set α).Subsingleton :=
  Set.subsingleton_of_subset_singleton fun _ hb ↦ mem_singleton.1 <| parts_top_subset _ hb

-- TODO: this instance takes double-exponential time to generate all partitions, find a faster way
/-
**Finpartition.** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] {s : Finset α} : Fintype (Finpartition s) where
  elems := s.powerset.powerset.image
    fun ps ↦ if h : ps.sup id = s ∧ ⊥ ∉ ps ∧ ps.SupIndep id then ⟨ps, h.2.2, h.1, h.2.1⟩ else ⊤
  complete P := by
    refine mem_image.mpr ⟨P.parts, ?_, ?_⟩
    · rw [mem_powerset]; intro p hp; rw [mem_powerset]; exact P.le hp
    · simp [P.supIndep, P.sup_parts, P.bot_notMem, -bot_eq_empty]
/-
**Finpartition.exists_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：exists_le_of_le {a b : α} {P Q : Finpartition a} (h : P <= Q) (hb : b in Q
.parts) : exists c in P.parts, c <= b
参数：h : P <= Q；hb : b in Q.parts。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Finpartition.ne_bot`：ne_bot {b : α} (hb : b in P.parts) : b != ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finpartition.supIndep`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (self : Finpartition a), self.parts.SupIndep id
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
-/
theorem exists_le_of_le {a b : α} {P Q : Finpartition a} (h : P ≤ Q) (hb : b ∈ Q.parts) :
    ∃ c ∈ P.parts, c ≤ b := by
  classical
  by_contra H
  refine Q.ne_bot hb (disjoint_self.1 <| Disjoint.mono_right (Q.le hb) ?_)
  have : ∀ p ∈ P.parts, ∃ q ∈ Q.parts.erase b, p ≤ q := by grind [h _]
  have : P.parts.sup id ≤ (Q.parts.erase b).sup id := by grind [Finset.le_sup, Finset.sup_le_iff]
  grw [← P.sup_parts, this]
  exact Q.supIndep (erase_subset _ _) hb (notMem_erase _ _)
/-
**Finpartition.card_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：card_mono {a : α} {P Q : Finpartition a} (h : P <= Q) : #Q.parts <= #P.par
ts
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.exists_le_of_le`：exists_le_of_le {a b : α} {P Q : Finpartit
ion a} (h : P <= Q) (hb : b in Q.parts) : exists c in P.parts, c <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Set.PairwiseDisjoint.elim`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f
 → ∀ {i j : ι},…
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
· 使用定理 `Finpartition.ne_bot`：ne_bot {b : α} (hb : b in P.parts) : b != ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem card_mono {a : α} {P Q : Finpartition a} (h : P ≤ Q) : #Q.parts ≤ #P.parts := by
  have : ∀ b ∈ Q.parts, ∃ c ∈ P.parts, c ≤ b := fun b ↦ exists_le_of_le h
  choose f hP hf using this
  rw [← card_attach]
  refine card_le_card_of_injOn (fun b ↦ f _ b.2) (fun b _ ↦ hP _ b.2) fun b _ c _ h ↦ ?_
  exact
    Subtype.coe_injective
      (Q.disjoint.elim b.2 c.2 fun H ↦
        P.ne_bot (hP _ b.2) <| disjoint_self.1 <| H.mono (hf _ b.2) <| h.le.trans <| hf _ c.2)

end Order

section ToSubtype

variable {s : α} (P : Finpartition s) {Pr : α → Prop}
  (Prsup : ∀ ⦃s t : α⦄, Pr s → Pr t → Pr (s ⊔ t)) (Prinf : ∀ ⦃s t : α⦄, Pr s → Pr t → Pr (s ⊓ t))
  (Prbot : Pr (⊥ : α)) (hs : Pr s) (hP : ∀ p ∈ P.parts, Pr p)

/-- A `Finpartition` constructor in `Subtype Pr` for `Pr : Set X → Prop` such that `Pr` is closed
under intersection and union and `Pr ⊥` holds from a `P : Finpartition s` with explicit assumptions
that `Pr s` and `Pr p` for each part `p`. -/
/-
**Finpartition.toSubtype** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：toSubtype : letI : Lattice (Subtype Pr)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Finpartition` constructor in `Subtype Pr` for `Pr : Set X → Prop` such that `
Pr` is closed
under intersection and union and `Pr ⊥` holds from a `P : Finpartition s` with e
xplicit assumptions
that `Pr s` and `Pr p` for each part `p`.
-/
noncomputable def toSubtype :
    letI : Lattice (Subtype Pr) := Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    Finpartition (⟨s, hs⟩ : Subtype Pr) :=
  letI : Lattice (Subtype Pr) := Subtype.lattice Prsup Prinf
  letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
  { parts := preimage P.parts Subtype.val Subtype.val_injective.injOn
    supIndep t ht i hi hi' := by
      classical
      have : (fun (i : Subtype Pr) => (id i).val) = id ∘ Subtype.val := rfl
      rw [disjoint_subtype_iff Prinf Prbot, sup_coe, this, ← sup_image t Subtype.val id]
      · apply P.supIndep
        · simpa [image_subset_iff_subset_preimage] using ht
        · simpa using hi
        · simpa [i.property] using hi'
      exact Prsup
    sup_parts := by
      simpa [Finset.sup_preimage_val_id Prsup Prbot hP] using P.sup_parts
    bot_notMem := by simpa [mem_preimage, Subtype.coe_bot Prbot] using P.bot_notMem }

@[simp]
/-
**Finpartition.mem_toSubtype_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：mem_toSubtype_iff (p : Subtype Pr) : letI : Lattice (Subtype Pr)
参数：p : Subtype Pr。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_toSubtype_iff (p : Subtype Pr) :
    letI : Lattice (Subtype Pr) := Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    p ∈ (toSubtype P Prsup Prinf Prbot hs hP).parts ↔ p.val ∈ P.parts := by simp [toSubtype]
/-
**Finpartition.sum_eq_sum_finpartition_subtype** 是 Mathlib 中的一个引理，位于命名空间 `Finpar
tition`。
形式化陈述：sum_eq_sum_finpartition_subtype {X : Type*} [AddCommMonoid X] (f : α -> X)
 : letI : Lattice (Subtype Pr)
参数：f : α -> X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_bij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a 
: ι)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_eq_sum_finpartition_subtype {X : Type*} [AddCommMonoid X] (f : α → X) :
    letI : Lattice (Subtype Pr) := Subtype.lattice Prsup Prinf
    letI : OrderBot (Subtype Pr) := Subtype.orderBot Prbot
    ∑ p ∈ P.parts, f p = ∑ p ∈ (Finpartition.toSubtype P Prsup Prinf Prbot hs hP).parts, f p := by
  apply Finset.sum_bij (fun p hpP => ⟨p, hP p hpP⟩) <;> simp

end ToSubtype

end Lattice

section DistribLattice

variable [DistribLattice α] [OrderBot α] [DecidableEq α] {a b c : α}

/-
**Finpartition.** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (Finpartition a) :=
  ⟨fun P Q ↦
    ofErase ((P.parts ×ˢ Q.parts).image fun bc ↦ bc.1 ⊓ bc.2)
      (by
        rw [supIndep_iff_disjoint_erase]
        simp only [mem_image, and_imp, forall_exists_index, id, Prod.exists,
          mem_product, Finset.disjoint_sup_right, mem_erase, Ne]
        rintro _ x₁ y₁ hx₁ hy₁ rfl _ h x₂ y₂ hx₂ hy₂ rfl
        rcases eq_or_ne x₁ x₂ with (rfl | xdiff)
        · refine Disjoint.mono inf_le_right inf_le_right (Q.disjoint hy₁ hy₂ ?_)
          intro t
          simp [t] at h
        exact Disjoint.mono inf_le_left inf_le_left (P.disjoint hx₁ hx₂ xdiff))
      (by
        rw [sup_image, id_comp, sup_product_left]
        trans P.parts.sup id ⊓ Q.parts.sup id
        · simp_rw [Finset.sup_inf_distrib_right, Finset.sup_inf_distrib_left]
          rfl
        · rw [P.sup_parts, Q.sup_parts, inf_idem])⟩

@[simp]
/-
**Finpartition.parts_inf** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：parts_inf (P Q : Finpartition a) : (P ⊓ Q).parts = ((P.parts ×ˢ Q.parts).i
mage fun bc : α × α => bc.1 ⊓ bc.2).erase ⊥
参数：P Q : Finpartition a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parts_inf (P Q : Finpartition a) :
    (P ⊓ Q).parts = ((P.parts ×ˢ Q.parts).image fun bc : α × α ↦ bc.1 ⊓ bc.2).erase ⊥ :=
  rfl
/-
**Finpartition.** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (Finpartition a) :=
  { inf := Min.min
    inf_le_left := fun P Q b hb ↦ by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      rw [mem_product] at hc
      exact ⟨c.1, hc.1, inf_le_left⟩
    inf_le_right := fun P Q b hb ↦ by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 (mem_of_mem_erase hb)
      rw [mem_product] at hc
      exact ⟨c.2, hc.2, inf_le_right⟩
    le_inf := fun P Q R hPQ hPR b hb ↦ by
      obtain ⟨c, hc, hbc⟩ := hPQ hb
      obtain ⟨d, hd, hbd⟩ := hPR hb
      have h := _root_.le_inf hbc hbd
      refine
        ⟨c ⊓ d,
          mem_erase_of_ne_of_mem (ne_bot_of_le_ne_bot (P.ne_bot hb) h)
            (mem_image.2 ⟨(c, d), mem_product.2 ⟨hc, hd⟩, rfl⟩),
          h⟩ }

/-- Restrict a partition of `a` to `b` where `b ≤ a` by intersecting each part with `b`. -/
/-
**Finpartition.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：restrict (P : Finpartition a) (hb : b <= a) : Finpartition b where parts
参数：P : Finpartition a；hb : b <= a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a partition of `a` to `b` where `b ≤ a` by intersecting each part with 
`b`.
-/
def restrict (P : Finpartition a) (hb : b ≤ a) : Finpartition b where
  parts := (P.parts.image (· ⊓ b)).erase ⊥
  supIndep := supIndep_iff_pairwiseDisjoint.mpr fun x hx y hy hxy => by
    simp only [coe_erase, coe_image, Set.mem_sdiff, Set.mem_image, Set.mem_singleton_iff] at hx hy
    obtain ⟨⟨px, hpx, rfl⟩, _⟩ := hx
    obtain ⟨⟨py, hpy, rfl⟩, _⟩ := hy
    simpa [Function.onFun, id_eq]
      using (P.disjoint hpx hpy fun h => hxy (h ▸ rfl)).mono inf_le_left inf_le_left
  sup_parts := by
    simp only [sup_erase_bot, sup_image, Function.id_comp, (sup_inf_distrib_right ..).symm]
    have : P.parts.sup (fun x => x) = a := P.sup_parts
    rw [this, inf_eq_right.mpr hb]
  bot_notMem := notMem_erase _ _

/-- The sum of a set-valued function over restricted partition parts equals the sum over original
parts with `f (· ⊓ b)`, provided `f ⊥ = 0` (so bottom terms don't contribute). -/
/-
**Finpartition.sum_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：sum_restrict (P : Finpartition a) (hb : b <= a) {M : Type*} [AddCommMonoid
 M] (f : α -> M) (hf : f ⊥ = 0) : ∑ p in (P.restrict hb).parts, f p = ∑ q in P.p
arts, f (q ⊓ b)
参数：P : Finpartition a；hb : b <= a；f : α -> M；hf : f ⊥ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finpartition.mk.congr_simp`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 
: OrderBot α] {a : α} (parts parts_1 : Finset α) (e_parts : parts = parts_1)   (
supIndep : parts…
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter_add_sum_filter_not`：∀ {ι : Type u_1} {M : Type u_4} [i
nst : AddCommMonoid M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p] 
  [inst_2 : (x : ι) → Deci…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The sum of a set-valued function over restricted partition parts equals the sum 
over original
parts with `f (· ⊓ b)`, provided `f ⊥ = 0` (so bottom terms don't contribute).
-/
lemma sum_restrict (P : Finpartition a) (hb : b ≤ a) {M : Type*} [AddCommMonoid M]
    (f : α → M) (hf : f ⊥ = 0) :
    ∑ p ∈ (P.restrict hb).parts, f p = ∑ q ∈ P.parts, f (q ⊓ b) := by
  have hinj : ∀ x ∈ P.parts.filter (· ⊓ b ≠ ⊥), ∀ y ∈ P.parts.filter (· ⊓ b ≠ ⊥),
      x ⊓ b = y ⊓ b → x = y := fun x hx y hy hxy => by
    by_contra hne
    simp only [Finset.mem_filter] at hx hy
    have : Disjoint (x ⊓ b) (y ⊓ b) := (P.disjoint hx.1 hy.1 hne).mono inf_le_left inf_le_left
    grind
  have heq : (P.parts.image (· ⊓ b)).erase ⊥ = (P.parts.filter (· ⊓ b ≠ ⊥)).image (· ⊓ b) := by
    grind
  have hz : ∑ x ∈ P.parts.filter (¬ · ⊓ b ≠ ⊥), f (x ⊓ b) = 0 := Finset.sum_eq_zero fun x hx => by
    simp only [ne_eq, Decidable.not_not, Finset.mem_filter] at hx
    rw [hx.2, hf]
  simp only [restrict, heq, ← Finset.sum_filter_add_sum_filter_not P.parts (· ⊓ b ≠ ⊥), hz,
    Finset.sum_image hinj, add_zero]

/-- A `Finpartition` constructor of `parts.sup id` from a finset `parts` of pairwise disjoint
elements. Any `⊥` elements in `parts` are erased. -/
@[simps]
/-
**Finpartition.ofPairwiseDisjoint** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：ofPairwiseDisjoint (parts : Finset α) (hdisjoint : (parts : Set α).Pairwis
eDisjoint id) : Finpartition (parts.sup id) where parts
参数：parts : Finset α；hdisjoint : (parts : Set α).PairwiseDisjoint id。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Finpartition` constructor of `parts.sup id` from a finset `parts` of pairwise
 disjoint
elements. Any `⊥` elements in `parts` are erased.
-/
def ofPairwiseDisjoint (parts : Finset α) (hdisjoint : (parts : Set α).PairwiseDisjoint id) :
    Finpartition (parts.sup id) where
  parts := parts.erase ⊥
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun _ ha _ hb hab =>
    hdisjoint (Finset.erase_subset _ _ ha) (Finset.erase_subset _ _ hb) hab
  sup_parts := Finset.sup_erase_bot parts
  bot_notMem := Finset.notMem_erase _ _
/-
**Finpartition.sum_ofPairwiseDisjoint_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finparti
tion`。
形式化陈述：sum_ofPairwiseDisjoint_eq_sum {parts : Finset α} (hdisjoint : (parts : Set
 α).PairwiseDisjoint id) {X : Type*} [AddCommMonoid X] {f : α -> X} (hf : f ⊥ = 
0) : ∑ p in (ofPairwiseDisjoint parts hdisjoint).parts, f p = ∑ p in parts, f p
参数：hdisjoint : (parts : Set α).PairwiseDisjoint id；hf : f ⊥ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.erase_union_eq`：erase_union_eq (a : α) (s : Finset α) (h : a in s
) : (erase s a) union {a} = s
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `Finset.sum_union_eq_right`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Fins
et ι} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   (∀ a ∈ s₁
, a ∉ s₂ → f a …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.erase_insert_eq_erase`：erase_insert_eq_erase (s : Finset α) (a : 
α) : (insert a s).erase a = s.erase a
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finpartition.ofPairwiseDisjoint_parts`：∀ {α : Type u_1} [inst : DistribL
attice α] [inst_1 : OrderBot α] [inst_2 : DecidableEq α] (parts : Finset α)   (h
disjoint : (↑parts).Pairwis…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma sum_ofPairwiseDisjoint_eq_sum {parts : Finset α}
    (hdisjoint : (parts : Set α).PairwiseDisjoint id)
    {X : Type*} [AddCommMonoid X] {f : α → X} (hf : f ⊥ = 0) :
    ∑ p ∈ (ofPairwiseDisjoint parts hdisjoint).parts, f p = ∑ p ∈ parts, f p := by
  by_cases hbot : ⊥ ∈ parts
  · simp only [Finpartition.ofPairwiseDisjoint]
    rw [← erase_union_eq ⊥ parts hbot, union_comm, sum_union_eq_right]
    · simp
    grind
  · simp_all

end DistribLattice

section IsModularLattice

variable [Lattice α] [OrderBot α] [IsModularLattice α] [DecidableEq α] {a b c : α}

/-- Combine a family of partitions of pairwise disjoint elements into a partition of their sup. -/
@[simps]
/-
**Finpartition.combine** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：combine {ι : Type*} {I : Finset ι} {a : ι -> α} (P : forall i, Finpartitio
n (a i)) (ha : I.SupIndep a) : Finpartition (I.sup a) where parts
参数：P : forall i, Finpartition (a i)；ha : I.SupIndep a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine a family of partitions of pairwise disjoint elements into a partition of
 their sup.
-/
def combine {ι : Type*} {I : Finset ι} {a : ι → α} (P : ∀ i, Finpartition (a i))
    (ha : I.SupIndep a) : Finpartition (I.sup a) where
  parts := I.biUnion fun i => (P i).parts
  supIndep :=
    .biUnion (by simpa only [sup_parts]) (fun i _ ↦ (P i).supIndep)
  sup_parts := by
    rw [sup_biUnion]
    exact sup_congr rfl fun i _ => (P i).sup_parts
  bot_notMem := by
    rw [mem_biUnion]; push Not; exact fun i _ => (P i).bot_notMem

/-- The sum of a set-valued function over a combined partition equals the sum of sums over component
partitions. -/
/-
**Finpartition.sum_combine** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：sum_combine {ι : Type*} {I : Finset ι} {s : ι -> α} (P : forall i, Finpart
ition (s i)) (ha : I.SupIndep s) {M : Type*} [AddCommMonoid M] (f : α -> M) : ∑ 
p in (Finpartition.combine P ha).parts, f p = ∑ i in I, ∑ p in (P i).parts, f p
参数：P : forall i, Finpartition (s i)；ha : I.SupIndep s；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_biUnion`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst
 : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {t : κ
 → Finse…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.onFun.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β 
→ β → φ) (g : α → β) (x y : α),   Function.onFun f g x y = f (g x) (g y)
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `Finset.SupIndep.pairwiseDisjoint`：∀ {α : Type u_1} {ι : Type u_3} [inst 
: Lattice α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α},   s.SupIndep f → 
(↑s).PairwiseDisjoint …
· 使用定理 `Finpartition.ne_bot`：ne_bot {b : α} (hb : b in P.parts) : b != ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥

--- 原说明 ---
The sum of a set-valued function over a combined partition equals the sum of sum
s over component
partitions.
-/
lemma sum_combine {ι : Type*} {I : Finset ι} {s : ι → α} (P : ∀ i, Finpartition (s i))
    (ha : I.SupIndep s) {M : Type*} [AddCommMonoid M] (f : α → M) :
    ∑ p ∈ (Finpartition.combine P ha).parts, f p = ∑ i ∈ I, ∑ p ∈ (P i).parts, f p := by
  simp_rw [combine]
  refine Finset.sum_biUnion fun i hi j hj hij => ?_
  rw [Function.onFun, Finset.disjoint_left]
  intro p hpi hpj
  have hp_disj : Disjoint p p := (ha.pairwiseDisjoint hi hj hij).mono ((P i).le hpi) ((P j).le hpj)
  exact (P i).ne_bot hpi (disjoint_self.mp hp_disj)

section Bind

variable {P : Finpartition a} {Q : ∀ i ∈ P.parts, Finpartition i}

/-- Given a finpartition `P` of `a` and finpartitions of each part of `P`, this yields the
finpartition of `a` obtained by juxtaposing all the subpartitions. -/
@[simps! parts]
/-
**Finpartition.bind** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：bind (P : Finpartition a) (Q : forall i in P.parts, Finpartition i) : Finp
artition a
参数：P : Finpartition a；Q : forall i in P.parts, Finpartition i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finpartition `P` of `a` and finpartitions of each part of `P`, this yiel
ds the
finpartition of `a` obtained by juxtaposing all the subpartitions.
-/
def bind (P : Finpartition a) (Q : ∀ i ∈ P.parts, Finpartition i) : Finpartition a :=
  (combine (fun i : P.parts => Q i.1 i.2) P.supIndep.attach).copy <| by
    rw [Finset.sup_attach (f := fun x => x), ← Function.id_def, P.sup_parts]
/-
**Finpartition.mem_bind** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：mem_bind : b in (P.bind Q).parts ↔ exists A hA, b in (Q A hA).parts
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.bind_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : O
rderBot α] [inst_2 : IsModularLattice α] [inst_3 : DecidableEq α] {a : α}   (P :
 Finpartition…
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `Finset.mem_attach`：mem_attach (s : Finset α) : forall x, x in s.attach
-/
theorem mem_bind : b ∈ (P.bind Q).parts ↔ ∃ A hA, b ∈ (Q A hA).parts := by
  rw [bind_parts, mem_biUnion]
  constructor
  · rintro ⟨⟨A, hA⟩, -, h⟩
    exact ⟨A, hA, h⟩
  · rintro ⟨A, hA, h⟩
    exact ⟨⟨A, hA⟩, mem_attach _ ⟨A, hA⟩, h⟩
/-
**Finpartition.card_bind** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：card_bind (Q : forall i in P.parts, Finpartition i) : #(P.bind Q).parts = 
∑ A in P.parts.attach, #(Q _ A.2).parts
参数：Q : forall i in P.parts, Finpartition i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.onFun.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β 
→ β → φ) (g : α → β) (x y : α),   Function.onFun f g x y = f (g x) (g y)
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Finpartition.ne_bot`：ne_bot {b : α} (hb : b in P.parts) : b != ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
-/
theorem card_bind (Q : ∀ i ∈ P.parts, Finpartition i) :
    #(P.bind Q).parts = ∑ A ∈ P.parts.attach, #(Q _ A.2).parts := by
  apply card_biUnion
  rintro ⟨b, hb⟩ - ⟨c, hc⟩ - hbc
  rw [Function.onFun, Finset.disjoint_left]
  rintro d hdb hdc
  rw [Ne, Subtype.mk_eq_mk] at hbc
  exact
    (Q b hb).ne_bot hdb
      (eq_bot_iff.2 <|
        (le_inf ((Q b hb).le hdb) <| (Q c hc).le hdc).trans <| (P.disjoint hb hc hbc).le_bot)

end Bind

/-- Adds `b` to a finpartition of `a` to make a finpartition of `a ⊔ b`. -/
@[simps]
/-
**Finpartition.extend** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：extend (P : Finpartition a) (hb : b != ⊥) (hab : Disjoint a b) (hc : a ⊔ b
 = c) : Finpartition c where parts
参数：P : Finpartition a；hb : b != ⊥；hab : Disjoint a b；hc : a ⊔ b = c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Adds `b` to a finpartition of `a` to make a finpartition of `a ⊔ b`.
-/
def extend (P : Finpartition a) (hb : b ≠ ⊥) (hab : Disjoint a b) (hc : a ⊔ b = c) :
    Finpartition c where
  parts := insert b P.parts
  supIndep := by
    refine P.supIndep.insert ?_
    rwa [sup_parts, disjoint_comm]
  sup_parts := by rwa [sup_insert, P.sup_parts, id, _root_.sup_comm]
  bot_notMem h := (mem_insert.1 h).elim hb.symm P.bot_notMem
/-
**Finpartition.card_extend** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：card_extend (P : Finpartition a) (b c : α) {hb : b != ⊥} {hab : Disjoint a
 b} {hc : a ⊔ b = c} : #(P.extend hb hab hc).parts = #P.parts + 1
参数：P : Finpartition a；b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `Disjoint.eq_bot_of_le`：Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a
 <= b) : a = ⊥
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
-/
theorem card_extend (P : Finpartition a) (b c : α) {hb : b ≠ ⊥} {hab : Disjoint a b}
    {hc : a ⊔ b = c} : #(P.extend hb hab hc).parts = #P.parts + 1 :=
  card_insert_of_notMem fun h ↦ hb <| hab.symm.eq_bot_of_le <| P.le h

end IsModularLattice

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] [DecidableEq α] {a b c : α} (P : Finpartition a)

/-- Restricts a finpartition to avoid a given element. -/
@[simps!]
/-
**Finpartition.avoid** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：avoid (b : α) : Finpartition (a \ b)
参数：b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricts a finpartition to avoid a given element.
-/
def avoid (b : α) : Finpartition (a \ b) :=
  ofErase
    (P.parts.image (· \ b))
    (P.disjoint.image_finset_of_le fun _ ↦ sdiff_le).supIndep
    (by rw [sup_image, id_comp, Finset.sup_sdiff_right, ← Function.id_def, P.sup_parts])

@[simp]
/-
**Finpartition.mem_avoid** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：mem_avoid : c in (P.avoid b).parts ↔ exists d in P.parts, ¬d <= b ∧ d \ b 
= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_left_comm`：∀ {a b c : Prop}, a ∧ b ∧ c ↔ b ∧ a ∧ c
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `and_congr_left`：∀ {c a b : Prop}, (c → (a ↔ b)) → (a ∧ c ↔ b ∧ c)
· 使用定理 `sdiff_eq_bot_iff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α
] {a b : α}, b \ a = ⊥ ↔ b ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_avoid : c ∈ (P.avoid b).parts ↔ ∃ d ∈ P.parts, ¬d ≤ b ∧ d \ b = c := by
  simp only [avoid, ofErase, mem_erase, Ne, mem_image, ← exists_and_left,
    @and_left_comm (c ≠ ⊥)]
  refine exists_congr fun d ↦ and_congr_right' <| and_congr_left ?_
  rintro rfl
  rw [sdiff_eq_bot_iff]

/-- Extend a partition of `a` to a partition of `b` when `a ≤ b`, by adding `b \ a` as a `part`. -/
/-
**Finpartition.extendOfLE** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：extendOfLE (hab : a <= b) : Finpartition b
参数：hab : a <= b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)

--- 原说明 ---
Extend a partition of `a` to a partition of `b` when `a ≤ b`, by adding `b \ a` 
as a `part`.
-/
def extendOfLE (hab : a ≤ b) : Finpartition b :=
  if hr : b \ a = ⊥ then (le_antisymm (sdiff_eq_bot_iff.mp hr) hab) ▸ P
    else P.extend hr disjoint_sdiff_self_right (sup_sdiff_cancel_right hab)
/-
**Finpartition.parts_extendOfLE_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：parts_extendOfLE_of_eq (hab : a = b) : (P.extendOfLE hab.le).parts = P.par
ts
参数：hab : a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma parts_extendOfLE_of_eq (hab : a = b) : (P.extendOfLE hab.le).parts = P.parts := by
  subst hab; simp [extendOfLE]
/-
**Finpartition.parts_extendOfLE_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：parts_extendOfLE_of_lt (hab : a < b) : (P.extendOfLE (le_of_lt hab)).parts
 = insert (b \ a) P.parts
参数：hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `sdiff_eq_bot_iff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α
] {a b : α}, b \ a = ⊥ ↔ b ≤ a
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Finpartition.extend_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 :
 OrderBot α] [inst_2 : IsModularLattice α] [inst_3 : DecidableEq α]   {a b c : α
} (P : Finparti…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma parts_extendOfLE_of_lt (hab : a < b) :
    (P.extendOfLE (le_of_lt hab)).parts = insert (b \ a) P.parts := by
  simp [extendOfLE, sdiff_eq_bot_iff.not.mpr (not_le_of_gt hab)]
/-
**Finpartition.parts_subset_extendOfLE** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：parts_subset_extendOfLE (hab : a <= b) : P.parts subseteq (P.extendOfLE ha
b).parts
参数：hab : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sdiff_self_right`：disjoint_sdiff_self_right : Disjoint x (y \ x
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sdiff_eq_bot_iff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α
] {a b : α}, b \ a = ⊥ ↔ b ≤ a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
-/
lemma parts_subset_extendOfLE (hab : a ≤ b) : P.parts ⊆ (P.extendOfLE hab).parts := by
  unfold extendOfLE
  split_ifs with hr
  · cases le_antisymm (sdiff_eq_bot_iff.mp hr) hab; rfl
  · exact Finset.subset_insert _ _
/-
**Finpartition.mem_parts_or_eq_sdiff_of_mem_extendOfLE** 是 Mathlib 中的一个引理，位于命名空间
 `Finpartition`。
形式化陈述：mem_parts_or_eq_sdiff_of_mem_extendOfLE (hab : a <= b) {p : α} (hp : p in 
(P.extendOfLE hab).parts) : p in P.parts ∨ p = b \ a
参数：hab : a <= b；hp : p in (P.extendOfLE hab).parts。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finpartition.parts_extendOfLE_of_lt`：parts_extendOfLE_of_lt (hab : a < b
) : (P.extendOfLE (le_of_lt hab)).parts = insert (b \ a) P.parts
· 使用引理 `Finpartition.parts_extendOfLE_of_eq`：parts_extendOfLE_of_eq (hab : a = b
) : (P.extendOfLE hab.le).parts = P.parts
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
-/
lemma mem_parts_or_eq_sdiff_of_mem_extendOfLE (hab : a ≤ b) {p : α}
    (hp : p ∈ (P.extendOfLE hab).parts) : p ∈ P.parts ∨ p = b \ a := by
  by_cases h : a < b
  · simp_all [parts_extendOfLE_of_lt _ h, mem_insert, Or.comm]
  · left
    simpa [parts_extendOfLE_of_eq _ (LE.le.eq_of_not_lt hab h)] using hp

end GeneralizedBooleanAlgebra

end Finpartition

/-! ### Finite partitions of finsets -/


namespace Finpartition

variable [DecidableEq α] {s t u : Finset α} (P : Finpartition s) {a : α}

/-
**Finpartition.subset** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：subset {a : Finset α} (ha : a in P.parts) : a subseteq s
参数：ha : a in P.parts。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
-/
lemma subset {a : Finset α} (ha : a ∈ P.parts) : a ⊆ s := P.le ha
/-
**Finpartition.nonempty_of_mem_parts** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：nonempty_of_mem_parts {a : Finset α} (ha : a in P.parts) : a.Nonempty
参数：ha : a in P.parts。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `Finpartition.ne_bot`：ne_bot {b : α} (hb : b in P.parts) : b != ⊥
-/
theorem nonempty_of_mem_parts {a : Finset α} (ha : a ∈ P.parts) : a.Nonempty :=
  nonempty_iff_ne_empty.2 <| P.ne_bot ha

@[simp]
/-
**Finpartition.empty_notMem_parts** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：empty_notMem_parts : ∅ ∉ P.parts
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.bot_notMem`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : O
rderBot α] {a : α} (self : Finpartition a), ⊥ ∉ self.parts
-/
theorem empty_notMem_parts : ∅ ∉ P.parts := P.bot_notMem
/-
**Finpartition.ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：ne_empty (h : t in P.parts) : t != ∅
参数：h : t in P.parts。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.ne_bot`：ne_bot {b : α} (hb : b in P.parts) : b != ⊥
-/
theorem ne_empty (h : t ∈ P.parts) : t ≠ ∅ := P.ne_bot h
/-
**Finpartition.eq_of_mem_parts** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：eq_of_mem_parts (ht : t in P.parts) (hu : u in P.parts) (hat : a in t) (ha
u : a in u) : t = u
参数：ht : t in P.parts；hu : u in P.parts；hat : a in t；hau : a in u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.elim`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f
 → ∀ {i j : ι},…
· 使用定理 `Finpartition.disjoint`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (P : Finpartition a), (↑P.parts).PairwiseDisjoint id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists a, a 
in s ∧ a in t
-/
lemma eq_of_mem_parts (ht : t ∈ P.parts) (hu : u ∈ P.parts) (hat : a ∈ t) (hau : a ∈ u) : t = u :=
  P.disjoint.elim ht hu <| not_disjoint_iff.2 ⟨a, hat, hau⟩
/-
**Finpartition.exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：exists_mem (ha : a in s) : exists t in P.parts, a in t
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sup`：∀ {α : Type u_2} {ι : Type u_5} [inst : DecidableEq α] {
s : Finset ι} {f : ι → Finset α} {a : α},   a ∈ s.sup f ↔ ∃ i ∈ s, a ∈ f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
-/
theorem exists_mem (ha : a ∈ s) : ∃ t ∈ P.parts, a ∈ t := by
  simp_rw [← P.sup_parts] at ha
  exact mem_sup.1 ha
/-
**Finpartition.biUnion_parts** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：biUnion_parts : P.parts.biUnion id = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_eq_biUnion`：sup_eq_biUnion {α β} [DecidableEq β] (s : Finset 
α) (t : α -> Finset β) : s.sup t = s.biUnion t
· 使用定理 `Finpartition.sup_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Or
derBot α] {a : α} (self : Finpartition a), self.parts.sup id = a
-/
theorem biUnion_parts : P.parts.biUnion id = s :=
  (sup_eq_biUnion _ _).symm.trans P.sup_parts
/-
**Finpartition.existsUnique_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：existsUnique_mem (ha : a in s) : exists! t, t in P.parts ∧ a in t
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.exists_mem`：exists_mem (ha : a in s) : exists t in P.parts,
 a in t
· 使用引理 `Finpartition.eq_of_mem_parts`：eq_of_mem_parts (ht : t in P.parts) (hu : 
u in P.parts) (hat : a in t) (hau : a in u) : t = u
-/
theorem existsUnique_mem (ha : a ∈ s) : ∃! t, t ∈ P.parts ∧ a ∈ t := by
  obtain ⟨t, ht, ht'⟩ := P.exists_mem ha
  refine ⟨t, ⟨ht, ht'⟩, ?_⟩
  rintro u ⟨hu, hu'⟩
  exact P.eq_of_mem_parts hu ht hu' ht'

/--
Construct a `Finpartition s` from a finset of finsets `parts` such that each element of `s` is in
exactly one member of `parts`. This provides a converse to `Finpartition.subset`,
`Finpartition.not_empty_mem_parts` and `Finpartition.existsUnique_mem`.
-/
@[simps]
/-
**Finpartition.ofExistsUnique** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：ofExistsUnique (parts : Finset (Finset α)) (h : forall p in parts, p subse
teq s) (h' : forall a in s, exists! t in parts, a in t) (h'' : ∅ ∉ parts) : Finp
artition s where parts
参数：parts : Finset (Finset α)；h : forall p in parts, p subseteq s；h' : forall a i
n s, exists! t in parts, a in t；h'' : ∅ ∉ parts。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a `Finpartition s` from a finset of finsets `parts` such that each ele
ment of `s` is in
exactly one member of `parts`. This provides a converse to `Finpartition.subset`
,
`Finpartition.not_empty_mem_parts` and `Finpartition.existsUnique_mem`.
-/
def ofExistsUnique (parts : Finset (Finset α)) (h : ∀ p ∈ parts, p ⊆ s)
    (h' : ∀ a ∈ s, ∃! t ∈ parts, a ∈ t) (h'' : ∅ ∉ parts) :
    Finpartition s where
  parts := parts
  supIndep := by
    simp only [supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hab
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    exact hab ((h' x (h _ ha hx)).unique ⟨ha, hx⟩ ⟨hb, hx'⟩)
  sup_parts := by
    ext i
    simp only [mem_sup, id_eq]
    constructor
    · rintro ⟨j, hj, hj'⟩
      exact h j hj hj'
    · rintro hi
      exact (h' i hi).exists
  bot_notMem := h''

/-- The part of the finpartition that `a` lies in. -/
/-
**Finpartition.part** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：part (a : α) : Finset α
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.existsUnique_mem`：existsUnique_mem (ha : a in s) : exists! 
t, t in P.parts ∧ a in t

--- 原说明 ---
The part of the finpartition that `a` lies in.
-/
def part (a : α) : Finset α := if ha : a ∈ s then choose (hp := P.existsUnique_mem ha) else ∅

@[simp]
/-
**Finpartition.part_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：part_mem : P.part a in P.parts ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.existsUnique_mem`：existsUnique_mem (ha : a in s) : exists! 
t, t in P.parts ∧ a in t
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma part_mem : P.part a ∈ P.parts ↔ a ∈ s := by
  by_cases ha : a ∈ s <;> simp [part, ha, choose_mem]

@[simp]
/-
**Finpartition.part_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：part_eq_empty : P.part a = ∅ ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.ne_empty`：ne_empty (h : t in P.parts) : t != ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finpartition.part_mem`：part_mem : P.part a in P.parts ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Finpartition.existsUnique_mem`：existsUnique_mem (ha : a in s) : exists! 
t, t in P.parts ∧ a in t
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma part_eq_empty : P.part a = ∅ ↔ a ∉ s :=
  ⟨fun h has ↦ P.ne_empty (P.part_mem.2 has) h, fun h ↦ by simp [part, h]⟩

@[simp]
/-
**Finpartition.part_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：part_nonempty : (P.part a).Nonempty ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finpartition.part_eq_empty`：part_eq_empty : P.part a = ∅ ↔ a ∉ s
-/
lemma part_nonempty : (P.part a).Nonempty ↔ a ∈ s := by
  contrapose!; exact part_eq_empty P

@[simp]
/-
**Finpartition.part_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：part_subset (a : α) : P.part a subseteq s
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finpartition.part_mem`：part_mem : P.part a in P.parts ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finpartition.part_eq_empty`：part_eq_empty : P.part a = ∅ ↔ a ∉ s
-/
lemma part_subset (a : α) : P.part a ⊆ s := by
  by_cases ha : a ∈ s
  · exact P.le <| P.part_mem.2 ha
  · simp [P.part_eq_empty.2 ha]

@[simp]
/-
**Finpartition.mem_part_self** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：mem_part_self : a in P.part a ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.existsUnique_mem`：existsUnique_mem (ha : a in s) : exists! 
t, t in P.parts ∧ a in t
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.choose_property`：choose_property (hp : exists! a, a in l ∧ p a) :
 p (l.choose p hp)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finpartition.part_eq_empty`：part_eq_empty : P.part a = ∅ ↔ a ∉ s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mem_part_self : a ∈ P.part a ↔ a ∈ s := by
  by_cases ha : a ∈ s
  · simp [part, ha, choose_property (p := fun s => a ∈ s) P.parts (P.existsUnique_mem ha)]
  · simp [P.part_eq_empty.2, ha]

alias ⟨_, mem_part⟩ := mem_part_self
/-
**Finpartition.part_eq_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：part_eq_iff_mem (ht : t in P.parts) : P.part a = t ↔ a in t
参数：ht : t in P.parts。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Finpartition.eq_of_mem_parts`：eq_of_mem_parts (ht : t in P.parts) (hu : 
u in P.parts) (hat : a in t) (hau : a in u) : t = u
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
-/
lemma part_eq_iff_mem (ht : t ∈ P.parts) : P.part a = t ↔ a ∈ t := by
  constructor
  · rintro rfl
    simp_all
  · intro hat
    apply P.eq_of_mem_parts (a := a) <;> simp [*, P.le ht hat]
/-
**Finpartition.part_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：part_eq_of_mem (ht : t in P.parts) (hat : a in t) : P.part a = t
参数：ht : t in P.parts；hat : a in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finpartition.part_eq_iff_mem`：part_eq_iff_mem (ht : t in P.parts) : P.pa
rt a = t ↔ a in t
-/
lemma part_eq_of_mem (ht : t ∈ P.parts) (hat : a ∈ t) : P.part a = t :=
  (P.part_eq_iff_mem ht).2 hat
/-
**Finpartition.mem_part_iff_part_eq_part** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition
`。
形式化陈述：mem_part_iff_part_eq_part {b : α} (ha : a in s) (hb : b in s) : a in P.par
t b ↔ P.part a = P.part b
参数：ha : a in s；hb : b in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finpartition.part_eq_of_mem`：part_eq_of_mem (ht : t in P.parts) (hat : a
 in t) : P.part a = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finpartition.part_mem`：part_mem : P.part a in P.parts ↔ a in s
· 使用定理 `Finpartition.mem_part`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Fins
et α} (P : Finpartition s) {a : α}, a ∈ s → a ∈ P.part a
-/
lemma mem_part_iff_part_eq_part {b : α} (ha : a ∈ s) (hb : b ∈ s) :
    a ∈ P.part b ↔ P.part a = P.part b :=
  ⟨fun c ↦ (P.part_eq_of_mem (P.part_mem.2 hb) c), fun c ↦ c ▸ P.mem_part ha⟩
/-
**Finpartition.part_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：part_surjOn : Set.SurjOn P.part s P.parts
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.nonempty_of_mem_parts`：nonempty_of_mem_parts {a : Finset α}
 (ha : a in P.parts) : a.Nonempty
· 使用定理 `Finset.mem_of_subset`：mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ subs
eteq s₂ -> a in s₁ -> a in s₂
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Finpartition.existsUnique_mem`：existsUnique_mem (ha : a in s) : exists! 
t, t in P.parts ∧ a in t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finpartition.part_mem`：part_mem : P.part a in P.parts ↔ a in s
· 使用定理 `Finpartition.mem_part`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Fins
et α} (P : Finpartition s) {a : α}, a ∈ s → a ∈ P.part a
-/
theorem part_surjOn : Set.SurjOn P.part s P.parts := fun p hp ↦ by
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hp
  have hx' := mem_of_subset (P.le hp) hx
  use x, hx', (P.existsUnique_mem hx').unique ⟨P.part_mem.2 hx', P.mem_part hx'⟩ ⟨hp, hx⟩
/-
**Finpartition.exists_subset_part_bijOn** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`
。
形式化陈述：exists_subset_part_bijOn : exists r subseteq s, Set.BijOn P.part r P.parts
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SurjOn.exists_bijOn_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {t : Set β} {f : α → β}, Set.SurjOn f s t → ∃ s' ⊆ s, Set.BijOn f s' t
· 使用定理 `Finpartition.part_surjOn`：part_surjOn : Set.SurjOn P.part s P.parts
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
-/
theorem exists_subset_part_bijOn : ∃ r ⊆ s, Set.BijOn P.part r P.parts := by
  obtain ⟨r, hrs, hr⟩ := P.part_surjOn.exists_bijOn_subset
  lift r to Finset α using s.finite_toSet.subset hrs
  exact ⟨r, mod_cast hrs, hr⟩
/-
**Finpartition.mem_part_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：mem_part_iff_exists {b} : a in P.part b ↔ exists p in P.parts, a in p ∧ b 
in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finpartition.part_nonempty`：part_nonempty : (P.part a).Nonempty ↔ a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Finpartition.part_eq_of_mem`：part_eq_of_mem (ht : t in P.parts) (hat : a
 in t) : P.part a = t
-/
theorem mem_part_iff_exists {b} : a ∈ P.part b ↔ ∃ p ∈ P.parts, a ∈ p ∧ b ∈ p := by
  constructor
  · intro h
    have : b ∈ s := P.part_nonempty.1 ⟨a, h⟩
    refine ⟨_, ?_, h, ?_⟩ <;> simp [this]
  · rintro ⟨p, hp, hap, hbp⟩
    obtain rfl : P.part b = p := P.part_eq_of_mem hp hbp
    exact hap

/-- Equivalence between a finpartition's parts as a dependent sum and the partitioned set. -/
/-
**Finpartition.equivSigmaParts** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：equivSigmaParts : s ≃ Σ t : P.parts, t.1 where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between a finpartition's parts as a dependent sum and the partitione
d set.
-/
def equivSigmaParts : s ≃ Σ t : P.parts, t.1 where
  toFun x := ⟨⟨P.part x.1, P.part_mem.2 x.2⟩, ⟨x, P.mem_part x.2⟩⟩
  invFun x := ⟨x.2, mem_of_subset (P.le x.1.2) x.2.2⟩
  left_inv x := by simp
  right_inv x := by
    ext e
    · obtain ⟨⟨p, mp⟩, ⟨f, mf⟩⟩ := x
      dsimp only at mf ⊢
      rw [P.part_eq_of_mem mp mf]
    · simp

set_option backward.isDefEq.respectTransparency false in
/-
**Finpartition.exists_enumeration** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：exists_enumeration : exists f : s ≃ Σ t : P.parts, Fin #t.1, forall a b : 
s, P.part a = P.part b ↔ (f a).1 = (f b).1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `Equiv.sigmaCongrRight_apply`：∀ {α : Type u_3} {β₁ : α → Type u_1} {β₂ : 
α → Type u_2} (F : (a : α) → β₁ a ≃ β₂ a) (a : (a : α) × β₁ a),   (Equiv.sigmaCo
ngrRight F) a = ⟨…
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma exists_enumeration : ∃ f : s ≃ Σ t : P.parts, Fin #t.1,
    ∀ a b : s, P.part a = P.part b ↔ (f a).1 = (f b).1 := by
  use P.equivSigmaParts.trans ((Equiv.refl _).sigmaCongr (fun t ↦ t.1.equivFin))
  simp [equivSigmaParts, Equiv.sigmaCongr, Equiv.sigmaCongrLeft]
/-
**Finpartition.sum_card_parts** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：sum_card_parts : ∑ i in P.parts, #i = #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用定理 `Finset.SupIndep.pairwiseDisjoint`：∀ {α : Type u_1} {ι : Type u_3} [inst 
: Lattice α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α},   s.SupIndep f → 
(↑s).PairwiseDisjoint …
· 使用定理 `Finpartition.supIndep`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Ord
erBot α] {a : α} (self : Finpartition a), self.parts.SupIndep id
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finpartition.biUnion_parts`：biUnion_parts : P.parts.biUnion id = s
-/
theorem sum_card_parts : ∑ i ∈ P.parts, #i = #s := by
  convert! congr_arg Finset.card P.biUnion_parts
  rw [card_biUnion P.supIndep.pairwiseDisjoint]
  rfl

/-- `⊥` is the partition in singletons, aka discrete partition. -/
/-
**Finpartition.** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`⊥` is the partition in singletons, aka discrete partition.
-/
instance (s : Finset α) : Bot (Finpartition s) :=
  ⟨{  parts := s.map ⟨singleton, singleton_injective⟩
      supIndep := Set.PairwiseDisjoint.supIndep <| by
        rw [Finset.coe_map]
        exact Finset.pairwiseDisjoint_range_singleton.subset (Set.image_subset_range _ _)
      sup_parts := by rw [sup_map, id_comp, Embedding.coeFn_mk, Finset.sup_singleton_eq_self]
      bot_notMem := by simp }⟩

@[simp]
/-
**Finpartition.parts_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：parts_bot (s : Finset α) : (⊥ : Finpartition s).parts = s.map ⟨singleton, 
singleton_injective⟩
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parts_bot (s : Finset α) :
    (⊥ : Finpartition s).parts = s.map ⟨singleton, singleton_injective⟩ :=
  rfl
/-
**Finpartition.card_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：card_bot (s : Finset α) : #(⊥ : Finpartition s).parts = #s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.singleton_injective`：singleton_injective : Injective (singleton :
 α -> Finset α)
-/
theorem card_bot (s : Finset α) : #(⊥ : Finpartition s).parts = #s := Finset.card_map _
/-
**Finpartition.mem_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：mem_bot_iff : t in (⊥ : Finpartition s).parts ↔ exists a in s, {a} = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Finset.singleton_injective`：singleton_injective : Injective (singleton :
 α -> Finset α)
-/
theorem mem_bot_iff : t ∈ (⊥ : Finpartition s).parts ↔ ∃ a ∈ s, {a} = t :=
  mem_map
/-
**Finpartition.** 是 Mathlib 中的一个实例，位于命名空间 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : Finset α) : OrderBot (Finpartition s) :=
  { (inferInstance : Bot (Finpartition s)) with
    bot_le := fun P t ht ↦ by
      rw [mem_bot_iff] at ht
      obtain ⟨a, ha, rfl⟩ := ht
      obtain ⟨t, ht, hat⟩ := P.exists_mem ha
      exact ⟨t, ht, singleton_subset_iff.2 hat⟩ }
/-
**Finpartition.card_parts_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：card_parts_le_card : #P.parts <= #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.card_bot`：card_bot (s : Finset α) : #(⊥ : Finpartition s).p
arts = #s
· 使用定理 `Finpartition.card_mono`：card_mono {a : α} {P Q : Finpartition a} (h : P 
<= Q) : #Q.parts <= #P.parts
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem card_parts_le_card : #P.parts ≤ #s := by
  rw [← card_bot s]
  exact card_mono bot_le
/-
**Finpartition.card_mod_card_parts_le** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：card_mod_card_parts_le : #s % #P.parts <= #P.parts
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Finset.bot_eq_empty`：bot_eq_empty : (⊥ : Finset α) = ∅
· 使用定理 `Finpartition.parts_eq_empty_iff`：parts_eq_empty_iff : P.parts = ∅ ↔ a = 
⊥
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
-/
lemma card_mod_card_parts_le : #s % #P.parts ≤ #P.parts := by
  obtain h | h := (#P.parts).eq_zero_or_pos
  · rw [h]
    rw [Finset.card_eq_zero, parts_eq_empty_iff, bot_eq_empty, ← Finset.card_eq_zero] at h
    rw [h]
  · exact (Nat.mod_lt _ h).le

section SetSetoid

/-- A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes. -/
@[simps -isSimp]
/-
**Finpartition.ofSetSetoid** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：ofSetSetoid (s : Setoid α) (x : Finset α) [DecidableRel s.r] : Finpartitio
n x where parts
参数：s : Setoid α；x : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes.
-/
def ofSetSetoid (s : Setoid α) (x : Finset α) [DecidableRel s.r] : Finpartition x where
  parts := x.image fun a ↦ {b ∈ x | s.r a b}
  supIndep := by
    suffices ∀ (a b c d : α), s a d → s b d → (s a c ↔ s b c) by
      simp only [supIndep_iff_pairwiseDisjoint, Set.PairwiseDisjoint, Set.Pairwise, coe_image,
        Set.mem_image, mem_coe, ne_eq, onFun, id_eq, disjoint_iff_ne, forall_mem_not_eq,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_filter, not_and, filter_inj',
        not_forall, @not_imp_comm (_ ↔ _), Decidable.not_not]
      intro _ _ _ _ _ _ _ _ ha _ hb
      exact ⟨(s.trans' hb <| s.trans' (s.symm' ha) ·), (s.trans' ha <| s.trans' (s.symm' hb) ·)⟩
    simp +contextual [← Quotient.eq]
  sup_parts := by
    ext a
    simp_rw [sup_image, id_comp, mem_sup, mem_filter]
    refine ⟨(·.choose_spec.2.1), fun _ ↦ by use a⟩
  bot_notMem := by
    suffices ∀ x₁ ∈ x, ∃ x₂ ∈ x, s x₁ x₂ by simpa [filter_eq_empty_iff]
    intro x _
    use x
/-
**Finpartition.mem_part_ofSetSetoid_iff_rel** 是 Mathlib 中的一个定理，位于命名空间 `Finpartit
ion`。
形式化陈述：mem_part_ofSetSetoid_iff_rel {s : Setoid α} (x : Finset α) [DecidableRel s
.r] {b : α} : b in (ofSetSetoid s x).part a ↔ a in x ∧ b in x ∧ s a b
参数：x : Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.trans'`：trans' (r : Setoid α) : forall {x y z}, r x y -> r y z ->
 r x z
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finpartition.ofSetSetoid_parts`：∀ {α : Type u_1} [inst : DecidableEq α] 
(s : Setoid α) (x : Finset α) [inst_1 : DecidableRel ⇑s],   (Finpartition.ofSetS
etoid s x).parts = F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem mem_part_ofSetSetoid_iff_rel {s : Setoid α} (x : Finset α) [DecidableRel s.r] {b : α} :
    b ∈ (ofSetSetoid s x).part a ↔ a ∈ x ∧ b ∈ x ∧ s a b := by
  suffices (∃ a₁ ∈ x, (b ∈ x ∧ s a₁ b) ∧ a ∈ x ∧ s a₁ a) ↔ a ∈ x ∧ b ∈ x ∧ s a b by
    simpa [mem_part_iff_exists, ofSetSetoid_parts]
  exact ⟨
    fun ⟨c, _, ⟨hb, hcb⟩, ⟨ha, hca⟩⟩ ↦ ⟨ha, hb, s.trans' (s.symm' hca) hcb⟩,
    fun h ↦ ⟨a, ⟨h.1, ⟨⟨h.2.1, h.2.2⟩, ⟨h.1, s.refl _⟩⟩⟩⟩
  ⟩

end SetSetoid

section Setoid

variable [Fintype α]

/-- A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes. -/
@[simps! -isSimp]
/-
**Finpartition.ofSetoid** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：ofSetoid (s : Setoid α) [DecidableRel s.r] : Finpartition (univ : Finset α
)
参数：s : Setoid α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A setoid over a finite type induces a finpartition of the type's elements,
where the parts are the setoid's equivalence classes.
-/
def ofSetoid (s : Setoid α) [DecidableRel s.r] : Finpartition (univ : Finset α) :=
  ofSetSetoid s univ
/-
**Finpartition.mem_part_ofSetoid_iff_rel** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition
`。
形式化陈述：mem_part_ofSetoid_iff_rel {s : Setoid α} [DecidableRel s.r] {b : α} : b in
 (ofSetoid s).part a ↔ s a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.mem_part_ofSetSetoid_iff_rel`：mem_part_ofSetSetoid_iff_rel 
{s : Setoid α} (x : Finset α) [DecidableRel s.r] {b : α} : b in (ofSetSetoid s x
).part a ↔ a in x ∧ b in x ∧ s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem mem_part_ofSetoid_iff_rel {s : Setoid α} [DecidableRel s.r] {b : α} :
    b ∈ (ofSetoid s).part a ↔ s a b := by
  suffices b ∈ (ofSetSetoid s univ).part a ↔ a ∈ univ ∧ b ∈ univ ∧ s a b by simpa
  exact mem_part_ofSetSetoid_iff_rel univ

end Setoid

section Atomise

/-- Cuts `s` along the finsets in `F`: Two elements of `s` will be in the same part if they are
in the same finsets of `F`. -/
/-
**Finpartition.atomise** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：atomise (s : Finset α) (F : Finset (Finset α)) : Finpartition s
参数：s : Finset α；F : Finset (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cuts `s` along the finsets in `F`: Two elements of `s` will be in the same part 
if they are
in the same finsets of `F`.
-/
def atomise (s : Finset α) (F : Finset (Finset α)) : Finpartition s :=
  ofErase (F.powerset.image fun Q ↦ {i ∈ s | ∀ t ∈ F, t ∈ Q ↔ i ∈ t})
    (Set.PairwiseDisjoint.supIndep fun x hx y hy h ↦
      disjoint_left.mpr fun z hz1 hz2 ↦
        h (by
            rw [mem_coe, mem_image] at hx hy
            obtain ⟨Q, hQ, rfl⟩ := hx
            obtain ⟨R, hR, rfl⟩ := hy
            suffices h' : Q = R by
              subst h'
              exact of_eq_true (eq_self {i ∈ s | ∀ t ∈ F, t ∈ Q ↔ i ∈ t})
            rw [id, mem_filter] at hz1 hz2
            rw [mem_powerset] at hQ hR
            ext i
            refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
            · rwa [hz2.2 _ (hQ hi), ← hz1.2 _ (hQ hi)]
            · rwa [hz1.2 _ (hR hi), ← hz2.2 _ (hR hi)]))
    (by
      refine (Finset.sup_le fun t ht ↦ ?_).antisymm fun a ha ↦ ?_
      · rw [mem_image] at ht
        obtain ⟨A, _, rfl⟩ := ht
        exact s.filter_subset _
      · rw [mem_sup]
        refine
          ⟨{i ∈ s | ∀ t ∈ F, t ∈ {u ∈ F | a ∈ u} ↔ i ∈ t},
            mem_image_of_mem _ (mem_powerset.2 <| filter_subset _ _),
            mem_filter.2 ⟨ha, fun t ht ↦ ?_⟩⟩
        rw [mem_filter]
        exact and_iff_right ht)

variable {F : Finset (Finset α)}
/-
**Finpartition.mem_atomise** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：mem_atomise : t in (atomise s F).parts ↔ t.Nonempty ∧ exists Q subseteq F,
 {i in s | forall u in F, u in Q ↔ i in u} = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_atomise :
    t ∈ (atomise s F).parts ↔
      t.Nonempty ∧ ∃ Q ⊆ F, {i ∈ s | ∀ u ∈ F, u ∈ Q ↔ i ∈ u} = t := by
  simp only [atomise, ofErase, bot_eq_empty, mem_erase, mem_image, nonempty_iff_ne_empty,
    mem_powerset]
/-
**Finpartition.atomise_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：atomise_empty (hs : s.Nonempty) : (atomise s ∅).parts = {s}
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Finset.filter_true`：∀ {α : Type u_1} {h : DecidablePred fun x => True} (
s : Finset α), {x ∈ s | True} = s
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
· 使用定理 `Finpartition.ofErase.congr_simp`：∀ {α : Type u_1} [inst : Lattice α] [in
st_1 : OrderBot α] [inst_2 : DecidableEq α] {a : α} (parts parts_1 : Finset α)  
 (e_parts : parts = p…
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.notMem_singleton`：notMem_singleton {a b : α} : a ∉ ({b} : Finset 
α) ↔ a != b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.Nonempty.ne_empty`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
s ≠ ∅
-/
theorem atomise_empty (hs : s.Nonempty) : (atomise s ∅).parts = {s} := by
  simp only [atomise, powerset_empty, image_singleton, notMem_empty, IsEmpty.forall_iff,
    imp_true_iff, filter_true]
  exact erase_eq_of_notMem (notMem_singleton.2 hs.ne_empty.symm)
/-
**Finpartition.card_atomise_le** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：card_atomise_le : #(atomise s F).parts <= 2 ^ #F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.card_powerset`：card_powerset (s : Finset α) : card (powerset s) =
 2 ^ card s
-/
theorem card_atomise_le : #(atomise s F).parts ≤ 2 ^ #F :=
  (card_le_card <| erase_subset _ _).trans <| Finset.card_image_le.trans (card_powerset _).le
/-
**Finpartition.biUnion_filter_atomise** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：biUnion_filter_atomise (ht : t in F) (hts : t subseteq s) : {u in (atomise
 s F).parts | u subseteq t ∧ u.Nonempty}.biUnion id = t
参数：ht : t in F；hts : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finpartition.exists_mem`：exists_mem (ha : a in s) : exists t in P.parts,
 a in t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finpartition.mem_atomise`：mem_atomise : t in (atomise s F).parts ↔ t.Non
empty ∧ exists Q subseteq F, {i in s | forall u in F, u in Q ↔ i in u} = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem biUnion_filter_atomise (ht : t ∈ F) (hts : t ⊆ s) :
    {u ∈ (atomise s F).parts | u ⊆ t ∧ u.Nonempty}.biUnion id = t := by
  ext a
  refine mem_biUnion.trans ⟨fun ⟨u, hu, ha⟩ ↦ (mem_filter.1 hu).2.1 ha, fun ha ↦ ?_⟩
  obtain ⟨u, hu, hau⟩ := (atomise s F).exists_mem (hts ha)
  refine ⟨u, mem_filter.2 ⟨hu, fun b hb ↦ ?_, _, hau⟩, hau⟩
  obtain ⟨Q, _hQ, rfl⟩ := (mem_atomise.1 hu).2
  rw [mem_filter] at hau hb
  rwa [← hb.2 _ ht, hau.2 _ ht]
/-
**Finpartition.card_filter_atomise_le_two_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finpart
ition`。
形式化陈述：card_filter_atomise_le_two_pow (ht : t in F) : #{u in (atomise s F).parts 
| u subseteq t ∧ u.Nonempty} <= 2 ^ (#F - 1)
参数：ht : t in F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.subset_iff`：subset_iff {s₁ s₂ : Finset α} : s₁ subseteq s₂ ↔ fora
ll ⦃x⦄, x in s₁ -> x in s₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.erase_subset_erase`：erase_subset_erase (a : α) {s t : Finset α} (
h : s subseteq t) : erase s a subseteq erase t a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
· 使用定理 `Finset.card_powerset`：card_powerset (s : Finset α) : card (powerset s) =
 2 ^ card s
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem card_filter_atomise_le_two_pow (ht : t ∈ F) :
    #{u ∈ (atomise s F).parts | u ⊆ t ∧ u.Nonempty} ≤ 2 ^ (#F - 1) := by
  suffices h :
    {u ∈ (atomise s F).parts | u ⊆ t ∧ u.Nonempty} ⊆
      (F.erase t).powerset.image fun P ↦ {i ∈ s | ∀ x ∈ F, x ∈ insert t P ↔ i ∈ x} by
    refine (card_le_card h).trans (card_image_le.trans ?_)
    rw [card_powerset, card_erase_of_mem ht]
  rw [subset_iff]
  simp_rw [mem_image, mem_powerset, mem_filter, and_imp, Finset.Nonempty, exists_imp, mem_atomise,
    and_imp, Finset.Nonempty, exists_imp, and_imp]
  rintro P' i hi P PQ rfl hy₂ j _hj
  refine ⟨P.erase t, erase_subset_erase _ PQ, ?_⟩
  simp only [insert_erase (((mem_filter.1 hi).2 _ ht).2 <| hy₂ hi)]

end Atomise

end Finpartition

