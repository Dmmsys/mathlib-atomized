/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Aesop
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Tactic.Simproc.ExistsAndEq

/-!
# Lemmas about insertion, singleton, and pairs

This file provides extra lemmas about `insert`, `singleton`, and `pair`.

## Tags

insert, singleton

-/

@[expose] public section

assert_not_exists HeytingAlgebra

/-! ### Set coercion to a type -/

open Function

namespace Set

variable {α β : Type*} {s t : Set α} {a b : α}

/-!
### Lemmas about `insert`

`insert a s` is the set `{a} ∪ s`.
-/

/-
**Set.insert_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_def (x : α) (s : Set α) : insert x s = { y | y = x ∨ y in s }
参数：x : α；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Lemmas about `insert`

`insert a s` is the set `{a} ∪ s`.
-/
theorem insert_def (x : α) (s : Set α) : insert x s = { y | y = x ∨ y ∈ s } :=
  rfl

@[simp]
/-
**Set.subset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_insert (x : α) (s : Set α) : s subseteq insert x s
参数：x : α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_insert (x : α) (s : Set α) : s ⊆ insert x s := fun _ => Or.inr

-- This is a fairly aggressive pattern; it might be safer to use
-- `s ⊆ insert x s` or `_ ⊆ insert x s` instead.
-- Currently Cslib relies on this.
-- See `MathlibTest/grind/set.lean` for a test case illustrating the reasoning
-- that Cslib is relying on.
grind_pattern subset_insert => insert x s
/-
**Set.mem_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_insert (x : α) (s : Set α) : x in insert x s
参数：x : α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_insert (x : α) (s : Set α) : x ∈ insert x s :=
  Or.inl rfl
/-
**Set.mem_insert_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x in s -> x in insert y s
参数：y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_insert_of_mem {x : α} {s : Set α} (y : α) : x ∈ s → x ∈ insert y s :=
  Or.inr
/-
**Set.eq_or_mem_of_mem_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_or_mem_of_mem_insert {x a : α} {s : Set α} : x in insert a s -> x = a ∨
 x in s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_or_mem_of_mem_insert {x a : α} {s : Set α} : x ∈ insert a s → x = a ∨ x ∈ s :=
  id
/-
**Set.mem_of_mem_insert_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_of_mem_insert_of_ne : b in insert a s -> b != a -> b in s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
-/
theorem mem_of_mem_insert_of_ne : b ∈ insert a s → b ≠ a → b ∈ s :=
  Or.resolve_left
/-
**Set.eq_of_mem_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_of_mem_insert_of_notMem : b in insert a s -> b ∉ s -> b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
-/
theorem eq_of_mem_insert_of_notMem : b ∈ insert a s → b ∉ s → b = a :=
  Or.resolve_right

@[simp, grind =, push]
/-
**Set.mem_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_insert_iff {x a : α} {s : Set α} : x in insert a s ↔ x = a ∨ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_insert_iff {x a : α} {s : Set α} : x ∈ insert a s ↔ x = a ∨ x ∈ s :=
  Iff.rfl

@[simp]
/-
**Set.insert_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) : insert a s = s
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_eq_of_mem {a : α} {s : Set α} (h : a ∈ s) : insert a s = s := by grind
/-
**Set.ne_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ne_insert_of_notMem {s : Set α} (t : Set α) {a : α} : a ∉ s -> s != insert
 a t
参数：t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ne_insert_of_notMem {s : Set α} (t : Set α) {a : α} : a ∉ s → s ≠ insert a t := by grind

@[simp]
/-
**Set.insert_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_eq_self : insert a s = s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_eq_self : insert a s = s ↔ a ∈ s := by grind
/-
**Set.insert_ne_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_ne_self : insert a s != s ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_ne_self : insert a s ≠ s ↔ a ∉ s := by grind
/-
**Set.insert_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_subset_iff : insert a s subseteq t ↔ a in t ∧ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_subset_iff : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by grind
/-
**Set.insert_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_subset (ha : a in t) (hs : s subseteq t) : insert a s subseteq t
参数：ha : a in t；hs : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_subset (ha : a ∈ t) (hs : s ⊆ t) : insert a s ⊆ t := by grind

@[gcongr]
/-
**Set.insert_subset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_subset_insert (h : s subseteq t) : insert a s subseteq insert a t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t := by grind
/-
**Set.insert_subset_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s t : Set α} {a : α}, a ∉ s → (insert a s ⊆ insert a t ↔
 s ⊆ t)
参数：insert a s ⊆ insert a t ↔ s ⊆ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t := by grind
/-
**Set.subset_insert_iff_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_insert_iff_of_notMem (ha : a ∉ s) : s subseteq insert a t ↔ s subse
teq t
参数：ha : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_insert_iff_of_notMem (ha : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t := by grind
/-
**Set.ssubset_iff_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ exists a ∉ s, insert a s subset
eq t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t := by grind
/-
**Set._root_.LE.le.ssubset_of_mem_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LE.le.ssubset_of_mem_notMem (hst : s ⊆ t) (hat : a ∈ t) (has : a ∉ s) :
    s ⊂ t := by grind

@[deprecated (since := "2026-06-05")]
alias _root_.HasSubset.Subset.ssubset_of_mem_notMem := LE.le.ssubset_of_mem_notMem
/-
**Set.ssubset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂ insert a s
参数：h : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂ insert a s := by grind
/-
**Set.insert_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_comm (a b : α) (s : Set α) : insert a (insert b s) = insert b (inse
rt a s)
参数：a b : α；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_comm (a b : α) (s : Set α) : insert a (insert b s) = insert b (insert a s) := by
  grind
/-
**Set.insert_idem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_idem (a : α) (s : Set α) : insert a (insert a s) = insert a s
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_idem (a : α) (s : Set α) : insert a (insert a s) = insert a s := by grind
/-
**Set.insert_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_union : insert a s union t = insert a (s union t)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_union : insert a s ∪ t = insert a (s ∪ t) := by grind

@[simp]
/-
**Set.union_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_insert : s union insert a t = insert a (s union t)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_insert : s ∪ insert a t = insert a (s ∪ t) := by grind

@[simp]
/-
**Set.insert_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_nonempty (a : α) (s : Set α) : (insert a s).Nonempty
参数：a : α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem insert_nonempty (a : α) (s : Set α) : (insert a s).Nonempty :=
  ⟨a, mem_insert a s⟩
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : α) (s : Set α) : Nonempty (insert a s : Set α) :=
  (insert_nonempty a s).to_subtype
/-
**Set.insert_inter_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_inter_distrib (a : α) (s t : Set α) : insert a (s inter t) = insert
 a s inter insert a t
参数：a : α；s t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_inter_distrib (a : α) (s t : Set α) :
    insert a (s ∩ t) = insert a s ∩ insert a t := by grind
/-
**Set.insert_union_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_union_distrib (a : α) (s t : Set α) : insert a (s union t) = insert
 a s union insert a t
参数：a : α；s t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_union_distrib (a : α) (s t : Set α) :
    insert a (s ∪ t) = insert a s ∪ insert a t := by grind

-- useful in proofs by induction
/-
**Set.forall_of_forall_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_of_forall_insert {P : α -> Prop} {a : α} {s : Set α} (H : forall x,
 x in insert a s -> P x) (x) (h : x in s) : P x
参数：H : forall x, x in insert a s -> P x；x；h : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ insert a s → P x)
    (x) (h : x ∈ s) : P x := by grind
/-
**Set.forall_insert_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_insert_of_forall {P : α -> Prop} {a : α} {s : Set α} (H : forall x,
 x in s -> P x) (ha : P a) (x) (h : x in insert a s) : P x
参数：H : forall x, x in s -> P x；ha : P a；x；h : x in insert a s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ s → P x) (ha : P a)
    (x) (h : x ∈ insert a s) : P x := by grind
/-
**Set.exists_mem_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_mem_insert {P : α -> Prop} {a : α} {s : Set α} : (exists x in inser
t a s, P x) ↔ (P a ∨ exists x in s, P x)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_mem_insert {P : α → Prop} {a : α} {s : Set α} :
    (∃ x ∈ insert a s, P x) ↔ (P a ∨ ∃ x ∈ s, P x) := by grind
/-
**Set.forall_mem_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_mem_insert {P : α -> Prop} {a : α} {s : Set α} : (forall x in inser
t a s, P x) ↔ P a ∧ forall x in s, P x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_mem_insert {P : α → Prop} {a : α} {s : Set α} :
    (∀ x ∈ insert a s, P x) ↔ P a ∧ ∀ x ∈ s, P x := by grind

/-- Inserting an element to a set is equivalent to the option type. -/
/-
**Set.subtypeInsertEquivOption** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：subtypeInsertEquivOption [DecidableEq α] {t : Set α} {x : α} (h : x ∉ t) :
 { i // i in insert x t } ≃ Option { i // i in t } where toFun y
参数：h : x ∉ t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s

--- 原说明 ---
Inserting an element to a set is equivalent to the option type.
-/
def subtypeInsertEquivOption
    [DecidableEq α] {t : Set α} {x : α} (h : x ∉ t) :
    { i // i ∈ insert x t } ≃ Option { i // i ∈ t } where
  toFun y := if h : ↑y = x then none else some ⟨y, by grind⟩
  invFun y := (y.elim ⟨x, mem_insert _ _⟩) fun z => ⟨z, by grind⟩
  left_inv y := by grind
  right_inv := by rintro (_ | y) <;> grind

/-! ### Lemmas about singletons -/

/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Lemmas about singletons
-/
instance : LawfulSingleton α (Set α) :=
  ⟨fun x => Set.ext fun a => by
    simp only [mem_empty_iff_false, mem_insert_iff, or_false]
    exact Iff.rfl⟩
/-
**Set.singleton_def** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_def (a : α) : ({a} : Set α) = insert a ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Set.instLawfulSingleton`：∀ {α : Type u_1}, LawfulSingleton α (Set α)
-/
theorem singleton_def (a : α) : ({a} : Set α) = insert a ∅ :=
  (insert_empty_eq a).symm

@[simp, grind =, push]
/-
**Set.mem_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_singleton_iff {a b : α} : a in ({b} : Set α) ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b :=
  Iff.rfl
/-
**Set.notMem_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_singleton_iff {a b : α} : a ∉ ({b} : Set α) ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem notMem_singleton_iff {a b : α} : a ∉ ({b} : Set α) ↔ a ≠ b :=
  Iff.rfl

@[simp]
/-
**Set.ofPred_eq_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_eq_eq_singleton {a : α} : { n | n = a } = {a}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofPred_eq_eq_singleton {a : α} : { n | n = a } = {a} :=
  rfl

@[deprecated (since := "2026-07-09")] alias setOf_eq_eq_singleton := ofPred_eq_eq_singleton

@[simp]
/-
**Set.ofPred_eq_eq_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_eq_eq_singleton' {a : α} : { x | a = x } = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem ofPred_eq_eq_singleton' {a : α} : { x | a = x } = {a} :=
  ext fun _ => eq_comm

@[deprecated (since := "2026-07-09")] alias setOf_eq_eq_singleton' := ofPred_eq_eq_singleton'

-- TODO: again, annotation needed
-- Not `@[simp]` since `mem_singleton_iff` proves it.
/-
**Set.mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_singleton (a : α) : a in ({a} : Set α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_singleton (a : α) : a ∈ ({a} : Set α) :=
  @rfl _ _
/-
**Set.eq_of_mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_of_mem_singleton {x y : α} (h : x in ({y} : Set α)) : x = y
参数：h : x in ({y} : Set α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Set α)) : x = y :=
  h

@[simp]
/-
**Set.singleton_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_eq_singleton_iff {x y : α} : {x} = ({y} : Set α) ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `eq_iff_eq_cancel_left`：∀ {α : Sort u_1} {b c : α}, (∀ {a : α}, a = b ↔ a
 = c) ↔ b = c
-/
theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : Set α) ↔ x = y :=
  Set.ext_iff.trans eq_iff_eq_cancel_left
/-
**Set.singleton_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_injective : Injective (singleton : α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_eq_singleton_iff`：singleton_eq_singleton_iff {x y : α} : {
x} = ({y} : Set α) ↔ x = y
-/
theorem singleton_injective : Injective (singleton : α → Set α) := fun _ _ =>
  singleton_eq_singleton_iff.mp
/-
**Set.mem_singleton_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_singleton_of_eq {x y : α} (H : x = y) : x in ({y} : Set α)
参数：H : x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : Set α) :=
  H
/-
**Set.insert_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α) union s
参数：x : α；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α) ∪ s :=
  rfl

@[simp]
/-
**Set.singleton_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_nonempty (a : α) : ({a} : Set α).Nonempty
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_nonempty (a : α) : ({a} : Set α).Nonempty :=
  ⟨a, rfl⟩

@[simp]
/-
**Set.singleton_ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_ne_empty (a : α) : ({a} : Set α) != ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
-/
theorem singleton_ne_empty (a : α) : ({a} : Set α) ≠ ∅ :=
  (singleton_nonempty _).ne_empty

@[simp]
/-
**Set.empty_ne_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_ne_singleton (a : α) : ∅ != ({a} : Set α)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Set.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Set α) != ∅
-/
theorem empty_ne_singleton (a : α) : ∅ ≠ ({a} : Set α) :=
  (singleton_ne_empty a).symm
/-
**Set.empty_ssubset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_ssubset_singleton : (∅ : Set α) ⊂ {a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.empty_ssubset`：∀ {α : Type u} {s : Set α}, s.Nonempty → ∅ ⊂
 s
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
-/
theorem empty_ssubset_singleton : (∅ : Set α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset

@[simp, grind =]
/-
**Set.singleton_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_subset_iff {a : α} {s : Set α} : {a} subseteq s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_eq`：∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∀ (a : α), a = a' 
→ p a) ↔ p a'
-/
theorem singleton_subset_iff {a : α} {s : Set α} : {a} ⊆ s ↔ a ∈ s :=
  forall_eq

@[gcongr]
/-
**Set.singleton_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_subset_singleton : ({a} : Set α) subseteq {b} ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_subset_singleton : ({a} : Set α) ⊆ {b} ↔ a = b := by simp
/-
**Set.set_compr_eq_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：set_compr_eq_eq_singleton {a : α} : { b | b = a } = {a}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem set_compr_eq_eq_singleton {a : α} : { b | b = a } = {a} :=
  rfl

@[simp]
/-
**Set.singleton_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_union : {a} union s = insert a s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_union : {a} ∪ s = insert a s :=
  rfl

@[simp]
/-
**Set.union_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_singleton : s union {a} = insert a s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
-/
theorem union_singleton : s ∪ {a} = insert a s :=
  union_comm _ _

@[simp]
/-
**Set.singleton_inter_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_inter_nonempty : ({a} inter s).Nonempty ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_inter_nonempty : ({a} ∩ s).Nonempty ↔ a ∈ s := by
  simp only [Set.Nonempty, mem_inter_iff, mem_singleton_iff, exists_eq_left]

@[simp]
/-
**Set.inter_singleton_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_singleton_nonempty : (s inter {a}).Nonempty ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.singleton_inter_nonempty`：singleton_inter_nonempty : ({a} inter s).N
onempty ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inter_singleton_nonempty : (s ∩ {a}).Nonempty ↔ a ∈ s := by
  rw [inter_comm, singleton_inter_nonempty]

@[simp]
/-
**Set.singleton_inter_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_inter_eq_empty : {a} inter s = ∅ ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.singleton_inter_nonempty`：singleton_inter_nonempty : ({a} inter s).N
onempty ↔ a in s
-/
theorem singleton_inter_eq_empty : {a} ∩ s = ∅ ↔ a ∉ s :=
  not_nonempty_iff_eq_empty.symm.trans singleton_inter_nonempty.not

@[simp]
/-
**Set.inter_singleton_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_singleton_eq_empty : s inter {a} = ∅ ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.singleton_inter_eq_empty`：singleton_inter_eq_empty : {a} inter s = ∅
 ↔ a ∉ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inter_singleton_eq_empty : s ∩ {a} = ∅ ↔ a ∉ s := by
  rw [inter_comm, singleton_inter_eq_empty]

@[simp] alias ⟨_, singleton_inter_of_notMem⟩ := singleton_inter_eq_empty
@[simp] alias ⟨_, inter_singleton_of_notMem⟩ := inter_singleton_eq_empty
/-
**Set.singleton_inter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s → {a} ∩ s = {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma singleton_inter_of_mem (ha : a ∈ s) : {a} ∩ s = {a} := by simpa
/-
**Set.inter_singleton_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s → s ∩ {a} = {a}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[simp] lemma inter_singleton_of_mem (ha : a ∈ s) : s ∩ {a} = {a} := by simpa
/-
**Set.notMem_singleton_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_singleton_empty {s : Set α} : s ∉ ({∅} : Set (Set α)) ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
theorem notMem_singleton_empty {s : Set α} : s ∉ ({∅} : Set (Set α)) ↔ s.Nonempty :=
  nonempty_iff_ne_empty.symm
/-
**Set.uniqueSingleton** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：uniqueSingleton (a : α) : Unique (↥({a} : Set α))
参数：a : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
instance uniqueSingleton (a : α) : Unique (↥({a} : Set α)) :=
  ⟨⟨⟨a, mem_singleton a⟩⟩, fun ⟨_, h⟩ => Subtype.ext h⟩
/-
**Set.eq_singleton_iff_unique_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_singleton_iff_unique_mem : s = {a} ↔ a in s ∧ forall x in s, x = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.Subset.antisymm_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ a ⊆ b ∧ b
 ⊆ a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `and_congr_left'`：∀ {a b c : Prop}, (a ↔ b) → (a ∧ c ↔ b ∧ c)
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem eq_singleton_iff_unique_mem : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
  Subset.antisymm_iff.trans <| and_comm.trans <| and_congr_left' singleton_subset_iff
/-
**Set.eq_singleton_iff_nonempty_unique_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_singleton_iff_nonempty_unique_mem : s = {a} ↔ s.Nonempty ∧ forall x in 
s, x = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `and_congr_left`：∀ {c a b : Prop}, (c → (a ↔ b)) → (a ∧ c ↔ b ∧ c)
-/
theorem eq_singleton_iff_nonempty_unique_mem : s = {a} ↔ s.Nonempty ∧ ∀ x ∈ s, x = a :=
  eq_singleton_iff_unique_mem.trans <|
    and_congr_left fun H => ⟨fun h' => ⟨_, h'⟩, fun ⟨x, h⟩ => H x h ▸ h⟩
/-
**Set.singleton_iff_unique_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：singleton_iff_unique_mem : (exists a, s = {a}) ↔ exists! a, a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_iff_unique_mem : (∃ a, s = {a}) ↔ ∃! a, a ∈ s :=
  ⟨fun ⟨a, h⟩ ↦ ⟨a, by grind⟩, fun ⟨a, h⟩ ↦ ⟨a, by grind⟩⟩
/-
**Set.ofPred_mem_list_eq_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_mem_list_eq_replicate {l : List α} {a : α} : { x | x in l } = {a} ↔
 exists n > 0, l = List.replicate n a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem ofPred_mem_list_eq_replicate {l : List α} {a : α} :
    { x | x ∈ l } = {a} ↔ ∃ n > 0, l = List.replicate n a := by
  simpa +contextual [Set.ext_iff, iff_iff_implies_and_implies, forall_and, List.eq_replicate_iff,
    List.length_pos_iff_exists_mem] using ⟨fun _ _ ↦ ⟨_, ‹_›⟩, fun x hx h ↦ h _ hx ▸ hx⟩

@[deprecated (since := "2026-07-09")]
alias setOf_mem_list_eq_replicate := ofPred_mem_list_eq_replicate
/-
**Set.ofPred_mem_list_eq_singleton_of_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ofPred_mem_list_eq_singleton_of_nodup {l : List α} (H : l.Nodup) {a : α} :
 { x | x in l } = {a} ↔ l = [a]
参数：H : l.Nodup。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ofPred_mem_list_eq_replicate`：ofPred_mem_list_eq_replicate {l : List
 α} {a : α} : { x | x in l } = {a} ↔ exists n > 0, l = List.replicate n a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem ofPred_mem_list_eq_singleton_of_nodup {l : List α} (H : l.Nodup) {a : α} :
    { x | x ∈ l } = {a} ↔ l = [a] := by
  constructor
  · rw [ofPred_mem_list_eq_replicate]
    rintro ⟨n, hn, rfl⟩
    simp only [List.nodup_replicate] at H
    simp [show n = 1 by lia]
  · rintro rfl
    simp

@[deprecated (since := "2026-07-09")]
alias setOf_mem_list_eq_singleton_of_nodup := ofPred_mem_list_eq_singleton_of_nodup

-- while `simp` is capable of proving this, it is not capable of turning the LHS into the RHS.
@[simp]
/-
**Set.default_coe_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：default_coe_singleton (x : α) : (default : ({x} : Set α)) = ⟨x, rfl⟩
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem default_coe_singleton (x : α) : (default : ({x} : Set α)) = ⟨x, rfl⟩ :=
  rfl

@[simp]
/-
**Set.subset_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_singleton_iff {α : Type*} {s : Set α} {x : α} : s subseteq {x} ↔ fo
rall y in s, y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_singleton_iff {α : Type*} {s : Set α} {x : α} : s ⊆ {x} ↔ ∀ y ∈ s, y = x :=
  Iff.rfl
/-
**Set.subset_singleton_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_singleton_iff_eq {s : Set α} {x : α} : s subseteq {x} ↔ s = ∅ ∨ s =
 {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_singleton_iff_eq {s : Set α} {x : α} : s ⊆ {x} ↔ s = ∅ ∨ s = {x} := by grind
/-
**Set.Nonempty.subset_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {a : α}, s.Nonempty → (s ⊆ {a} ↔ s = {a})
参数：s ⊆ {a} ↔ s = {a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.subset_singleton_iff_eq`：subset_singleton_iff_eq {s : Set α} {x : α}
 : s subseteq {x} ↔ s = ∅ ∨ s = {x}
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
-/
theorem Nonempty.subset_singleton_iff (h : s.Nonempty) : s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff_eq.trans <| or_iff_right h.ne_empty
/-
**Set.ssubset_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ssubset_singleton_iff {s : Set α} {x : α} : s ⊂ {x} ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ssubset_iff_subset_ne`：∀ {α : Type u_2} [UsesSetNotationForOrder α] [ins
t : PartialOrder α] {a b : α}, a ⊂ b ↔ a ⊆ b ∧ a ≠ b
· 使用定理 `Set.subset_singleton_iff_eq`：subset_singleton_iff_eq {s : Set α} {x : α}
 : s subseteq {x} ↔ s = ∅ ∨ s = {x}
· 使用定理 `or_and_right`：∀ {a b c : Prop}, (a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c
· 使用定理 `and_not_self_iff`：∀ (a : Prop), a ∧ ¬a ↔ False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_iff_left_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ a) ↔ a → b
· 使用定理 `Set.empty_ne_singleton`：empty_ne_singleton (a : α) : ∅ != ({a} : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ssubset_singleton_iff {s : Set α} {x : α} : s ⊂ {x} ↔ s = ∅ := by
  rw [ssubset_iff_subset_ne, subset_singleton_iff_eq, or_and_right, and_not_self_iff, or_false,
    and_iff_left_iff_imp]
  exact fun h => h ▸ empty_ne_singleton _
/-
**Set.eq_empty_of_ssubset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_empty_of_ssubset_singleton {s : Set α} {x : α} (hs : s ⊂ {x}) : s = ∅
参数：hs : s ⊂ {x}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ssubset_singleton_iff`：ssubset_singleton_iff {s : Set α} {x : α} : s
 ⊂ {x} ↔ s = ∅
-/
theorem eq_empty_of_ssubset_singleton {s : Set α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs
/-
**Set.eq_of_nonempty_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_of_nonempty_of_subsingleton {α} [Subsingleton α] (s t : Set α) [Nonempt
y s] [Nonempty t] : s = t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Nonempty.eq_univ`：∀ {α : Type u} {s : Set α} [Subsingleton α], s.Non
empty → s = Set.univ
· 使用定理 `Set.Nonempty.of_subtype`：∀ {α : Type u} {s : Set α} [Nonempty ↑s], s.Non
empty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_nonempty_of_subsingleton {α} [Subsingleton α] (s t : Set α) [Nonempty s]
    [Nonempty t] : s = t :=
  Nonempty.of_subtype.eq_univ.trans Nonempty.of_subtype.eq_univ.symm
/-
**Set.eq_of_nonempty_of_subsingleton'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_of_nonempty_of_subsingleton' {α} [Subsingleton α] {s : Set α} (t : Set 
α) (hs : s.Nonempty) [Nonempty t] : s = t
参数：t : Set α；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Set.eq_of_nonempty_of_subsingleton`：eq_of_nonempty_of_subsingleton {α} [
Subsingleton α] (s t : Set α) [Nonempty s] [Nonempty t] : s = t
-/
theorem eq_of_nonempty_of_subsingleton' {α} [Subsingleton α] {s : Set α} (t : Set α)
    (hs : s.Nonempty) [Nonempty t] : s = t :=
  have := hs.to_subtype; eq_of_nonempty_of_subsingleton s t
/-
**Set.Nonempty.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} [Subsingleton α] [inst : Zero α] {s : Set α}, s.Nonempty 
→ s = {0}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_nonempty_of_subsingleton'`：eq_of_nonempty_of_subsingleton' {α}
 [Subsingleton α] {s : Set α} (t : Set α) (hs : s.Nonempty) [Nonempty t] : s = t
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem Nonempty.eq_zero [Subsingleton α] [Zero α] {s : Set α} (h : s.Nonempty) :
    s = {0} := eq_of_nonempty_of_subsingleton' {0} h
/-
**Set.Nonempty.eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} [Subsingleton α] [inst : One α] {s : Set α}, s.Nonempty →
 s = {1}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_nonempty_of_subsingleton'`：eq_of_nonempty_of_subsingleton' {α}
 [Subsingleton α] {s : Set α} (t : Set α) (hs : s.Nonempty) [Nonempty t] : s = t
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem Nonempty.eq_one [Subsingleton α] [One α] {s : Set α} (h : s.Nonempty) :
    s = {1} := eq_of_nonempty_of_subsingleton' {1} h

/-! ### Disjointness -/

@[simp default + 1]
/-
**Set.disjoint_singleton_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_singleton_left : Disjoint {a} s ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Disjointness
-/
lemma disjoint_singleton_left : Disjoint {a} s ↔ a ∉ s := by simp [Set.disjoint_iff, subset_def]

@[simp]
/-
**Set.disjoint_singleton_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_singleton_right : Disjoint s {a} ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用引理 `Set.disjoint_singleton_left`：disjoint_singleton_left : Disjoint {a} s ↔ 
a ∉ s
-/
lemma disjoint_singleton_right : Disjoint s {a} ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left
/-
**Set.disjoint_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_singleton : Disjoint ({a} : Set α) {b} ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma disjoint_singleton : Disjoint ({a} : Set α) {b} ↔ a ≠ b := by
  simp

@[simp]
/-
**Set.disjoint_insert_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [Set.disjoint_left, Set.mem_insert_iff, forall_eq_or_imp]

@[simp]
/-
**Set.disjoint_insert_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Set.disjoint_insert_left`：disjoint_insert_left : Disjoint (insert a s) t
 ↔ a ∉ t ∧ Disjoint s t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [disjoint_comm, disjoint_insert_left, disjoint_comm]
/-
**Set.insert_inj** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b
参数：ha : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_mem_insert_of_notMem`：eq_of_mem_insert_of_notMem : b in insert
 a s -> b ∉ s -> b = a
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_mem_insert_of_notMem (h ▸ mem_insert a s) ha,
    congr_arg (fun x => insert x s)⟩

@[simp]
/-
**Set.insert_sdiff_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_sdiff_eq_singleton {a : α} {s : Set α} (h : a ∉ s) : insert a s \ s
 = {a}
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_sdiff_eq_singleton {a : α} {s : Set α} (h : a ∉ s) : insert a s \ s = {a} := by grind

@[deprecated (since := "2026-06-03")] alias insert_diff_eq_singleton := insert_sdiff_eq_singleton
/-
**Set.inter_insert_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_insert_of_mem (h : a in s) : s inter insert a t = insert a (s inter 
t)
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_insert_of_mem (h : a ∈ s) : s ∩ insert a t = insert a (s ∩ t) := by grind
/-
**Set.insert_inter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_inter_of_mem (h : a in t) : insert a s inter t = insert a (s inter 
t)
参数：h : a in t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_inter_of_mem (h : a ∈ t) : insert a s ∩ t = insert a (s ∩ t) := by grind
/-
**Set.inter_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_insert_of_notMem (h : a ∉ s) : s inter insert a t = s inter t
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_insert_of_notMem (h : a ∉ s) : s ∩ insert a t = s ∩ t := by grind
/-
**Set.insert_inter_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_inter_of_notMem (h : a ∉ t) : insert a s inter t = s inter t
参数：h : a ∉ t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_inter_of_notMem (h : a ∉ t) : insert a s ∩ t = s ∩ t := by grind

/-! ### Lemmas about pairs -/

/-
**Set.pair_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pair_eq_singleton (a : α) : ({a, a} : Set α) = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a

--- 原说明 ---
### Lemmas about pairs
-/
theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
  union_self _
/-
**Set.pair_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
-/
theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
  union_comm _ _
/-
**Set.pair_eq_pair_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pair_eq_pair_iff {x y z w : α} : ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w
 ∨ x = w ∧ y = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem pair_eq_pair_iff {x y z w : α} :
    ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp [subset_antisymm_iff, insert_subset_iff]; aesop
/-
**Set.pair_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pair_subset_iff : {a, b} subseteq s ↔ a in s ∧ b in s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pair_subset_iff : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by grind
/-
**Set.pair_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pair_subset (ha : a in s) (hb : b in s) : {a, b} subseteq s
参数：ha : a in s；hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.pair_subset_iff`：pair_subset_iff : {a, b} subseteq s ↔ a in s ∧ b in
 s
-/
theorem pair_subset (ha : a ∈ s) (hb : b ∈ s) : {a, b} ⊆ s :=
  pair_subset_iff.2 ⟨ha,hb⟩
/-
**Set.subset_pair_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_pair_iff : s subseteq {a, b} ↔ forall x in s, x = a ∨ x = b
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_pair_iff : s ⊆ {a, b} ↔ ∀ x ∈ s, x = a ∨ x = b := by grind
/-
**Set.subset_pair_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_pair_iff_eq {x y : α} : s subseteq {x, y} ↔ s = ∅ ∨ s = {x} ∨ s = {
y} ∨ s = {x, y} where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_pair_iff_eq {x y : α} : s ⊆ {x, y} ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x, y} where
  mp := by grind
  mpr := by grind
/-
**Set.Nonempty.subset_pair_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {a b : α}, s.Nonempty → (s ⊆ {a, b} ↔ s = {a}
 ∨ s = {b} ∨ s = {a, b})
参数：s ⊆ {a, b} ↔ s = {a} ∨ s = {b} ∨ s = {a, b}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_pair_iff_eq`：subset_pair_iff_eq {x y : α} : s subseteq {x, y}
 ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x, y} where mp
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Nonempty.subset_pair_iff_eq (hs : s.Nonempty) :
    s ⊆ {a, b} ↔ s = {a} ∨ s = {b} ∨ s = {a, b} := by
  rw [Set.subset_pair_iff_eq, or_iff_right]; exact hs.ne_empty
/-
**Set.range_ite_const** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_ite_const {p : α -> Prop} [DecidablePred p] {x y : β} (hp : exists a
, p a) (hn : exists a, ¬ p a) : Set.range (fun a => if p a then x else y) = {x, 
y}
参数：hp : exists a, p a；hn : exists a, ¬ p a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_ite_const {p : α → Prop} [DecidablePred p] {x y : β}
    (hp : ∃ a, p a) (hn : ∃ a, ¬ p a) :
    Set.range (fun a ↦ if p a then x else y) = {x, y} := by
  grind

/-! ### Powerset -/

/-- The powerset of a singleton contains only `∅` and the singleton itself. -/
/-
**Set.powerset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：powerset_singleton (x : α) : 𝒫 {x} = {∅, {x}}
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The powerset of a singleton contains only `∅` and the singleton itself.
-/
theorem powerset_singleton (x : α) : 𝒫 {x} = {∅, {x}} := by grind

section
variable {α β : Type*} {a : α} {b : β}

/-
**Set.preimage_fst_singleton_eq_range** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_fst_singleton_eq_range : (Prod.fst ⁻¹' {a} : Set (α × β)) = range
 (a, ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_fst_singleton_eq_range : (Prod.fst ⁻¹' {a} : Set (α × β)) = range (a, ·) := by
  grind
/-
**Set.preimage_snd_singleton_eq_range** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_snd_singleton_eq_range : (Prod.snd ⁻¹' {b} : Set (α × β)) = range
 (·, b)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_snd_singleton_eq_range : (Prod.snd ⁻¹' {b} : Set (α × β)) = range (·, b) := by
  grind

end

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

/-! ### Decidability instances for sets -/

variable (s t : Set α) (a b : α)

/-
**Set.decidableSingleton** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableSingleton [Decidable (a = b)] : Decidable (a in ({b} : Set α))
参数：a = b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableSingleton [Decidable (a = b)] : Decidable (a ∈ ({b} : Set α)) :=
  inferInstanceAs (Decidable (a = b))

end Set

open Set

/-
**Prop.compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Prop`。
形式化陈述：∀ (p : Prop), {p}ᶜ = {¬p}
参数：p : Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `not_iff`：not_iff : ¬(a ↔ b) ↔ (¬a ↔ b)
-/
@[simp] theorem Prop.compl_singleton (p : Prop) : ({p}ᶜ : Set Prop) = {¬p} :=
  ext fun q ↦ by simpa [@Iff.comm q] using not_iff
