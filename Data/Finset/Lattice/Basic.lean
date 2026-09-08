/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.FinsetOps

/-!
# Lattice structure on finite sets

This file puts a lattice structure on finite sets using the union and intersection operators.

For `Finset α`, where `α` is a lattice, see also `Mathlib/Data/Finset/Lattice/Fold.lean`.

## Main declarations

There is a natural lattice structure on the subsets of a set.
In Lean, we use lattice notation to talk about things involving unions and intersections. See
`Mathlib/Order/Lattice.lean`. For the lattice structure on finsets, `⊥` is called `bot` with
`⊥ = ∅` and `⊤` is called `top` with `⊤ = univ`.


## Implementation Notes

All the theorems and instances expect `DecidableEq` instance for `α`

## Tags

finite sets, finset

-/

public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### Lattice structure -/

section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a : α}

/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`.
-/
instance : Union (Finset α) :=
  ⟨fun s t => ⟨_, t.2.ndunion s.1⟩⟩

/-- `s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`. -/
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`.
-/
instance : Inter (Finset α) :=
  ⟨fun s t => ⟨_, s.2.ndinter t.1⟩⟩
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lattice (Finset α) where
  sup := (· ∪ ·)
  sup_le := fun _ _ _ hs ht _ ha => (mem_ndunion.1 ha).elim (fun h => hs h) fun h => ht h
  le_sup_left := fun _ _ _ h => mem_ndunion.2 <| Or.inl h
  le_sup_right := fun _ _ _ h => mem_ndunion.2 <| Or.inr h
  inf := (· ∩ ·)
  le_inf := fun _ _ _ ht hu _ h => mem_ndinter.2 ⟨ht h, hu h⟩
  inf_le_left := fun _ _ _ h => (mem_ndinter.1 h).1
  inf_le_right := fun _ _ _ h => (mem_ndinter.1 h).2

@[simp]
/-
**Finset.sup_eq_union'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_eq_union' : (Max.max : Finset α -> Finset α -> Finset α) = Union.union
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_eq_union' : (Max.max : Finset α → Finset α → Finset α) = Union.union :=
  rfl

@[grind =]
/-
**Finset.sup_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_eq_union {s t : Finset α} : s ⊔ t = s union t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_eq_union {s t : Finset α} : s ⊔ t = s ∪ t :=
  rfl

@[simp]
/-
**Finset.inf_eq_inter'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inf_eq_inter' : (Min.min : Finset α -> Finset α -> Finset α) = Inter.inter
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_eq_inter' : (Min.min : Finset α → Finset α → Finset α) = Inter.inter :=
  rfl

@[grind =]
/-
**Finset.inf_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inf_eq_inter {s t : Finset α} : s ⊓ t = s inter t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_eq_inter {s t : Finset α} : s ⊓ t = s ∩ t :=
  rfl

/-! #### union -/

/-
**Finset.union_val_nd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_val_nd (s t : Finset α) : (s union t).1 = ndunion s.1 t.1
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
#### union
-/
theorem union_val_nd (s t : Finset α) : (s ∪ t).1 = ndunion s.1 t.1 :=
  rfl

@[simp]
/-
**Finset.union_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_val (s t : Finset α) : (s union t).1 = s.1 union t.1
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ndunion_eq_union`：ndunion_eq_union {s t : Multiset α} (d : Nodu
p s) : ndunion s t = s union t
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem union_val (s t : Finset α) : (s ∪ t).1 = s.1 ∪ t.1 :=
  ndunion_eq_union s.2

@[simp, grind =]
/-
**Finset.mem_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_union : a in s union t ↔ a in s ∨ a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_ndunion`：mem_ndunion {s t : Multiset α} {a : α} : a in ndun
ion s t ↔ a in s ∨ a in t
-/
theorem mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  mem_ndunion
/-
**Finset.mem_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_union_left (t : Finset α) (h : a in s) : a in s union t
参数：t : Finset α；h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
-/
theorem mem_union_left (t : Finset α) (h : a ∈ s) : a ∈ s ∪ t :=
  mem_union.2 <| Or.inl h
/-
**Finset.mem_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_union_right (s : Finset α) (h : a in t) : a in s union t
参数：s : Finset α；h : a in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
-/
theorem mem_union_right (s : Finset α) (h : a ∈ t) : a ∈ s ∪ t :=
  mem_union.2 <| Or.inr h
/-
**Finset.forall_mem_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：forall_mem_union {p : α -> Prop} : (forall a in s union t, p a) ↔ (forall 
a in s, p a) ∧ forall a in t, p a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_mem_union {p : α → Prop} : (∀ a ∈ s ∪ t, p a) ↔ (∀ a ∈ s, p a) ∧ ∀ a ∈ t, p a := by
  grind
/-
**Finset.notMem_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_union : a ∉ s union t ↔ a ∉ s ∧ a ∉ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem notMem_union : a ∉ s ∪ t ↔ a ∉ s ∧ a ∉ t := by rw [mem_union, not_or]

@[simp, norm_cast]
/-
**Finset.coe_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ union s₂ : Set α)
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
-/
theorem coe_union (s₁ s₂ : Finset α) : ↑(s₁ ∪ s₂) = (s₁ ∪ s₂ : Set α) :=
  Set.ext fun _ => mem_union
/-
**Finset.union_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_subset (hs : s subseteq u) : t subseteq u -> s union t subseteq u
参数：hs : s subseteq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
theorem union_subset (hs : s ⊆ u) : t ⊆ u → s ∪ t ⊆ u :=
  sup_le hs
/-
**Finset.subset_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂ : Finset α}, s₁ ⊆ s₁ ∪ s₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_union_left`：mem_union_left (t : Finset α) (h : a in s) : a in
 s union t
-/
@[simp] lemma subset_union_left : s₁ ⊆ s₁ ∪ s₂ := fun _ ↦ mem_union_left _
/-
**Finset.subset_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_union_right`：mem_union_right (s : Finset α) (h : a in t) : a 
in s union t
-/
@[simp] lemma subset_union_right : s₂ ⊆ s₁ ∪ s₂ := fun _ ↦ mem_union_right _

@[gcongr]
/-
**Finset.union_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_subset_union (hsu : s subseteq u) (htv : t subseteq v) : s union t s
ubseteq u union v
参数：hsu : s subseteq u；htv : t subseteq v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
-/
theorem union_subset_union (hsu : s ⊆ u) (htv : t ⊆ v) : s ∪ t ⊆ u ∪ v :=
  sup_le_sup hsu htv
/-
**Finset.union_subset_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_subset_union_left (h : s₁ subseteq s₂) : s₁ union t subseteq s₂ unio
n t
参数：h : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.union_subset_union`：union_subset_union (hsu : s subseteq u) (htv 
: t subseteq v) : s union t subseteq u union v
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem union_subset_union_left (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h Subset.rfl
/-
**Finset.union_subset_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_subset_union_right (h : t₁ subseteq t₂) : s union t₁ subseteq s unio
n t₂
参数：h : t₁ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.union_subset_union`：union_subset_union (hsu : s subseteq u) (htv 
: t subseteq v) : s union t subseteq u union v
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem union_subset_union_right (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union Subset.rfl h
/-
**Finset.union_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ union s₁
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem union_comm (s₁ s₂ : Finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ := sup_comm _ _
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Commutative (α := Finset α) (· ∪ ·) :=
  ⟨union_comm⟩

@[simp]
/-
**Finset.union_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_assoc (s₁ s₂ s₃ : Finset α) : s₁ union s₂ union s₃ = s₁ union (s₂ un
ion s₃)
参数：s₁ s₂ s₃ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
-/
theorem union_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := sup_assoc _ _ _
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Associative (α := Finset α) (· ∪ ·) :=
  ⟨union_assoc⟩

@[simp]
/-
**Finset.union_idempotent** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_idempotent (s : Finset α) : s union s = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
-/
theorem union_idempotent (s : Finset α) : s ∪ s = s := sup_idem _
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.IdempotentOp (α := Finset α) (· ∪ ·) :=
  ⟨union_idempotent⟩
/-
**Finset.union_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_subset_left (h : s union t subseteq u) : s subseteq u
参数：h : s union t subseteq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
-/
theorem union_subset_left (h : s ∪ t ⊆ u) : s ⊆ u :=
  subset_union_left.trans h
/-
**Finset.union_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_subset_right {s t u : Finset α} (h : s union t subseteq u) : t subse
teq u
参数：h : s union t subseteq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
-/
theorem union_subset_right {s t u : Finset α} (h : s ∪ t ⊆ u) : t ⊆ u :=
  Subset.trans subset_union_right h
/-
**Finset.union_left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_left_comm (s t u : Finset α) : s union (t union u) = t union (s unio
n u)
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem union_left_comm (s t u : Finset α) : s ∪ (t ∪ u) = t ∪ (s ∪ u) :=
  ext fun _ => by simp only [mem_union, or_left_comm]
/-
**Finset.union_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_right_comm (s t u : Finset α) : s union t union u = s union u union 
t
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem union_right_comm (s t u : Finset α) : s ∪ t ∪ u = s ∪ u ∪ t :=
  ext fun x => by simp only [mem_union, or_assoc, @or_comm (x ∈ t)]
/-
**Finset.union_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_self (s : Finset α) : s union s = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.union_idempotent`：union_idempotent (s : Finset α) : s union s = s
-/
theorem union_self (s : Finset α) : s ∪ s = s :=
  union_idempotent s
/-
**Finset.union_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, s ∪ t = s ↔ t ⊆ 
s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
-/
@[simp] lemma union_eq_left : s ∪ t = s ↔ t ⊆ s := sup_eq_left
/-
**Finset.left_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, s = s ∪ t ↔ t ⊆ 
s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.union_eq_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fin
set α}, s ∪ t = s ↔ t ⊆ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma left_eq_union : s = s ∪ t ↔ t ⊆ s := by rw [eq_comm, union_eq_left]
/-
**Finset.union_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, s ∪ t = t ↔ s ⊆ 
t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
-/
@[simp] lemma union_eq_right : s ∪ t = t ↔ s ⊆ t := sup_eq_right
/-
**Finset.right_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, s = t ∪ s ↔ t ⊆ 
s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.union_eq_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fi
nset α}, s ∪ t = t ↔ s ⊆ t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma right_eq_union : s = t ∪ s ↔ t ⊆ s := by rw [eq_comm, union_eq_right]
/-
**Finset.union_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_congr_left (ht : t subseteq s union u) (hu : u subseteq s union t) :
 s union t = s union u
参数：ht : t subseteq s union u；hu : u subseteq s union t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_congr_left`：sup_congr_left (hb : b <= a ⊔ c) (hc : c <= a ⊔ b) : a ⊔
 b = a ⊔ c
-/
theorem union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ∪ u :=
  sup_congr_left ht hu
/-
**Finset.union_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_congr_right (hs : s subseteq t union u) (ht : t subseteq s union u) 
: s union u = t union u
参数：hs : s subseteq t union u；ht : t subseteq s union u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_congr_right`：sup_congr_right (ha : a <= b ⊔ c) (hb : b <= a ⊔ c) : a
 ⊔ c = b ⊔ c
-/
theorem union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u :=
  sup_congr_right hs ht
/-
**Finset.union_eq_union_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_eq_union_iff_left : s union t = s union u ↔ t subseteq s union u ∧ u
 subseteq s union t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_sup_iff_left`：sup_eq_sup_iff_left : a ⊔ b = a ⊔ c ↔ b <= a ⊔ c ∧ 
c <= a ⊔ b
-/
theorem union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t :=
  sup_eq_sup_iff_left
/-
**Finset.union_eq_union_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_eq_union_iff_right : s union u = t union u ↔ s subseteq t union u ∧ 
t subseteq s union u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_sup_iff_right`：sup_eq_sup_iff_right : a ⊔ c = b ⊔ c ↔ a <= b ⊔ c 
∧ b <= a ⊔ c
-/
theorem union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u :=
  sup_eq_sup_iff_right
/-
**Finset.inter_val_nd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_val_nd (s₁ s₂ : Finset α) : (s₁ inter s₂).1 = ndinter s₁.1 s₂.1
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_val_nd (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = ndinter s₁.1 s₂.1 :=
  rfl

@[simp]
/-
**Finset.inter_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_val (s₁ s₂ : Finset α) : (s₁ inter s₂).1 = s₁.1 inter s₂.1
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ndinter_eq_inter`：ndinter_eq_inter {s t : Multiset α} (d : Nodu
p s) : ndinter s t = s inter t
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem inter_val (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = s₁.1 ∩ s₂.1 :=
  ndinter_eq_inter s₁.2

@[simp, grind =]
/-
**Finset.mem_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s₂ ↔ a in s₁ ∧ a in s
₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_ndinter`：mem_ndinter {s t : Multiset α} {a : α} : a in ndin
ter s t ↔ a in s ∧ a in t
-/
theorem mem_inter {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
  mem_ndinter
/-
**Finset.mem_of_mem_inter_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_of_mem_inter_left {a : α} {s₁ s₂ : Finset α} (h : a in s₁ inter s₂) : 
a in s₁
参数：h : a in s₁ inter s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
-/
theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₁ :=
  (mem_inter.1 h).1
/-
**Finset.mem_of_mem_inter_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_of_mem_inter_right {a : α} {s₁ s₂ : Finset α} (h : a in s₁ inter s₂) :
 a in s₂
参数：h : a in s₁ inter s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
-/
theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₂ :=
  (mem_inter.1 h).2
/-
**Finset.mem_inter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a in s₁ -> a in s₂ -> a in s
₁ inter s₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
-/
theorem mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
  and_imp.1 mem_inter.2
/-
**Finset.inter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂ : Finset α}, s₁ ∩ s₂ ⊆ s₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_of_mem_inter_left`：mem_of_mem_inter_left {a : α} {s₁ s₂ : Fin
set α} (h : a in s₁ inter s₂) : a in s₁
-/
@[simp] lemma inter_subset_left : s₁ ∩ s₂ ⊆ s₁ := fun _ ↦ mem_of_mem_inter_left
/-
**Finset.inter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_of_mem_inter_right`：mem_of_mem_inter_right {a : α} {s₁ s₂ : F
inset α} (h : a in s₁ inter s₂) : a in s₂
-/
@[simp] lemma inter_subset_right : s₁ ∩ s₂ ⊆ s₂ := fun _ ↦ mem_of_mem_inter_right
/-
**Finset.subset_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_inter {s₁ s₂ u : Finset α} : s₁ subseteq s₂ -> s₁ subseteq u -> s₁ 
subseteq s₂ inter u
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_inter {s₁ s₂ u : Finset α} : s₁ ⊆ s₂ → s₁ ⊆ u → s₁ ⊆ s₂ ∩ u := by grind

@[simp, norm_cast]
/-
**Finset.coe_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ inter s₂ : Set α)
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
-/
theorem coe_inter (s₁ s₂ : Finset α) : ↑(s₁ ∩ s₂) = (s₁ ∩ s₂ : Set α) :=
  Set.ext fun _ => mem_inter

@[simp]
/-
**Finset.union_inter_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_inter_cancel_left {s t : Finset α} : (s union t) inter s = s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_inter_cancel_left {s t : Finset α} : (s ∪ t) ∩ s = s := by grind

@[simp]
/-
**Finset.union_inter_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_inter_cancel_right {s t : Finset α} : (s union t) inter t = t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_inter_cancel_right {s t : Finset α} : (s ∪ t) ∩ t = t := by grind
/-
**Finset.inter_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inter s₁
参数：s₁ s₂ : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_comm (s₁ s₂ : Finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ := by grind

@[simp]
/-
**Finset.inter_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_assoc (s₁ s₂ s₃ : Finset α) : s₁ inter s₂ inter s₃ = s₁ inter (s₂ in
ter s₃)
参数：s₁ s₂ s₃ : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) := by grind
/-
**Finset.inter_left_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_left_comm (s₁ s₂ s₃ : Finset α) : s₁ inter (s₂ inter s₃) = s₂ inter 
(s₁ inter s₃)
参数：s₁ s₂ s₃ : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_left_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) := by grind
/-
**Finset.inter_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_right_comm (s₁ s₂ s₃ : Finset α) : s₁ inter s₂ inter s₃ = s₁ inter s
₃ inter s₂
参数：s₁ s₂ s₃ : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_right_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ := by grind

@[simp]
/-
**Finset.inter_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_self (s : Finset α) : s inter s = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
· 使用定理 `and_self_iff`：∀ {a : Prop}, a ∧ a ↔ a
-/
theorem inter_self (s : Finset α) : s ∩ s = s :=
  ext fun _ => mem_inter.trans <| and_self_iff

@[simp]
/-
**Finset.inter_union_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_union_self (s t : Finset α) : s inter (t union s) = s
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.union_inter_cancel_right`：union_inter_cancel_right {s t : Finset 
α} : (s union t) inter t = t
-/
theorem inter_union_self (s t : Finset α) : s ∩ (t ∪ s) = s := by
  rw [inter_comm, union_inter_cancel_right]

@[mono, gcongr]
/-
**Finset.inter_subset_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_subset_inter {x y s t : Finset α} (h : x subseteq y) (h' : s subsete
q t) : x inter s subseteq y inter t
参数：h : x subseteq y；h' : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
-/
theorem inter_subset_inter {x y s t : Finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t :=
  inf_le_inf h h'
/-
**Finset.inter_subset_inter_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_subset_inter_left (h : t subseteq u) : s inter t subseteq s inter u
参数：h : t subseteq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inter_subset_inter`：inter_subset_inter {x y s t : Finset α} (h : 
x subseteq y) (h' : s subseteq t) : x inter s subseteq y inter t
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem inter_subset_inter_left (h : t ⊆ u) : s ∩ t ⊆ s ∩ u :=
  inter_subset_inter Subset.rfl h
/-
**Finset.inter_subset_inter_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_subset_inter_right (h : s subseteq t) : s inter u subseteq t inter u
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inter_subset_inter`：inter_subset_inter {x y s t : Finset α} (h : 
x subseteq y) (h' : s subseteq t) : x inter s subseteq y inter t
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
-/
theorem inter_subset_inter_right (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter h Subset.rfl
/-
**Finset.inter_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_subset_union : s inter t subseteq s union t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_sup`：inf_le_sup : a ⊓ b <= a ⊔ b
-/
theorem inter_subset_union : s ∩ t ⊆ s ∪ t :=
  inf_le_sup
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribLattice (Finset α) :=
  { le_sup_inf := fun a b c => by
      simp +contextual only
        [sup_eq_union, inf_eq_inter, subset_iff, mem_inter, mem_union, and_imp,
        or_imp, true_or, imp_true_iff, true_and, or_true] }

@[simp]
/-
**Finset.union_left_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_left_idem (s t : Finset α) : s union (s union t) = s union t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_left_idem`：sup_left_idem (a b : α) : a ⊔ (a ⊔ b) = a ⊔ b
-/
theorem union_left_idem (s t : Finset α) : s ∪ (s ∪ t) = s ∪ t := sup_left_idem _ _
/-
**Finset.union_right_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_right_idem (s t : Finset α) : s union t union t = s union t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_right_idem`：sup_right_idem (a b : α) : a ⊔ b ⊔ b = a ⊔ b
-/
theorem union_right_idem (s t : Finset α) : s ∪ t ∪ t = s ∪ t := sup_right_idem _ _

@[simp]
/-
**Finset.inter_left_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_left_idem (s t : Finset α) : s inter (s inter t) = s inter t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_left_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ (
a ⊓ b) = a ⊓ b
-/
theorem inter_left_idem (s t : Finset α) : s ∩ (s ∩ t) = s ∩ t := inf_left_idem _ _
/-
**Finset.inter_right_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_right_idem (s t : Finset α) : s inter t inter t = s inter t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_right_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ 
b ⊓ b = a ⊓ b
-/
theorem inter_right_idem (s t : Finset α) : s ∩ t ∩ t = s ∩ t := inf_right_idem _ _
/-
**Finset.inter_union_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_union_distrib_left (s t u : Finset α) : s inter (t union u) = s inte
r t union s inter u
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
-/
theorem inter_union_distrib_left (s t u : Finset α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left _ _ _
/-
**Finset.union_inter_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_inter_distrib_right (s t u : Finset α) : (s union t) inter u = s int
er u union t inter u
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_sup_right`：inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = a ⊓ c ⊔ b ⊓ c
-/
theorem union_inter_distrib_right (s t u : Finset α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right _ _ _
/-
**Finset.union_inter_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_inter_distrib_left (s t u : Finset α) : s union t inter u = (s union
 t) inter (s union u)
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_inf_left`：sup_inf_left (a b c : α) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
-/
theorem union_inter_distrib_left (s t u : Finset α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left _ _ _
/-
**Finset.inter_union_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_union_distrib_right (s t u : Finset α) : s inter t union u = (s unio
n u) inter (t union u)
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_inf_right`：sup_inf_right (a b c : α) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
-/
theorem inter_union_distrib_right (s t u : Finset α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right _ _ _
/-
**Finset.union_union_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_union_distrib_left (s t u : Finset α) : s union (t union u) = s unio
n t union (s union u)
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sup_distrib_left`：sup_sup_distrib_left (a b c : α) : a ⊔ (b ⊔ c) = a
 ⊔ b ⊔ (a ⊔ c)
-/
theorem union_union_distrib_left (s t u : Finset α) : s ∪ (t ∪ u) = s ∪ t ∪ (s ∪ u) :=
  sup_sup_distrib_left _ _ _
/-
**Finset.union_union_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_union_distrib_right (s t u : Finset α) : s union t union u = s union
 u union (t union u)
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sup_distrib_right`：sup_sup_distrib_right (a b c : α) : a ⊔ b ⊔ c = a
 ⊔ c ⊔ (b ⊔ c)
-/
theorem union_union_distrib_right (s t u : Finset α) : s ∪ t ∪ u = s ∪ u ∪ (t ∪ u) :=
  sup_sup_distrib_right _ _ _
/-
**Finset.inter_inter_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_inter_distrib_left (s t u : Finset α) : s inter (t inter u) = s inte
r t inter (s inter u)
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_inf_distrib_left`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : 
α), a ⊓ (b ⊓ c) = a ⊓ b ⊓ (a ⊓ c)
-/
theorem inter_inter_distrib_left (s t u : Finset α) : s ∩ (t ∩ u) = s ∩ t ∩ (s ∩ u) :=
  inf_inf_distrib_left _ _ _
/-
**Finset.inter_inter_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_inter_distrib_right (s t u : Finset α) : s inter t inter u = s inter
 u inter (t inter u)
参数：s t u : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_inf_distrib_right`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c :
 α), a ⊓ b ⊓ c = a ⊓ c ⊓ (b ⊓ c)
-/
theorem inter_inter_distrib_right (s t u : Finset α) : s ∩ t ∩ u = s ∩ u ∩ (t ∩ u) :=
  inf_inf_distrib_right _ _ _
/-
**Finset.union_union_union_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_union_union_comm (s t u v : Finset α) : s union t union (u union v) 
= s union u union (t union v)
参数：s t u v : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_sup_sup_comm`：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔
 c ⊔ (b ⊔ d)
-/
theorem union_union_union_comm (s t u v : Finset α) : s ∪ t ∪ (u ∪ v) = s ∪ u ∪ (t ∪ v) :=
  sup_sup_sup_comm _ _ _ _
/-
**Finset.inter_inter_inter_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_inter_inter_comm (s t u v : Finset α) : s inter t inter (u inter v) 
= s inter u inter (t inter v)
参数：s t u v : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_inf_inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c d : α)
, a ⊓ b ⊓ (c ⊓ d) = a ⊓ c ⊓ (b ⊓ d)
-/
theorem inter_inter_inter_comm (s t u v : Finset α) : s ∩ t ∩ (u ∩ v) = s ∩ u ∩ (t ∩ v) :=
  inf_inf_inf_comm _ _ _ _
/-
**Finset.union_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_subset_iff : s union t subseteq u ↔ s subseteq u ∧ t subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
-/
theorem union_subset_iff : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (sup_le_iff : s ⊔ t ≤ u ↔ s ≤ u ∧ t ≤ u)
/-
**Finset.subset_inter_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_inter_iff : s subseteq t inter u ↔ s subseteq t ∧ s subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
-/
theorem subset_inter_iff : s ⊆ t ∩ u ↔ s ⊆ t ∧ s ⊆ u :=
  (le_inf_iff : s ≤ t ⊓ u ↔ s ≤ t ∧ s ≤ u)
/-
**Finset.inter_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, s ∩ t = s ↔ s ⊆ 
t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
-/
@[simp] lemma inter_eq_left : s ∩ t = s ↔ s ⊆ t := inf_eq_left
/-
**Finset.inter_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, t ∩ s = s ↔ s ⊆ 
t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
-/
@[simp] lemma inter_eq_right : t ∩ s = s ↔ s ⊆ t := inf_eq_right
/-
**Finset.inter_congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_congr_left (ht : s inter u subseteq t) (hu : s inter t subseteq u) :
 s inter t = s inter u
参数：ht : s inter u subseteq t；hu : s inter t subseteq u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_congr_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α}, a 
⊓ c ≤ b → a ⊓ b ≤ c → a ⊓ b = a ⊓ c
-/
theorem inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u :=
  inf_congr_left ht hu
/-
**Finset.inter_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_congr_right (hs : t inter u subseteq s) (ht : s inter u subseteq t) 
: s inter u = t inter u
参数：hs : t inter u subseteq s；ht : s inter u subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_congr_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α}, b
 ⊓ c ≤ a → a ⊓ c ≤ b → a ⊓ c = b ⊓ c
-/
theorem inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u :=
  inf_congr_right hs ht
/-
**Finset.inter_eq_inter_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_eq_inter_iff_left : s inter t = s inter u ↔ s inter u subseteq t ∧ s
 inter t subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_inf_iff_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α
}, a ⊓ b = a ⊓ c ↔ a ⊓ c ≤ b ∧ a ⊓ b ≤ c
-/
theorem inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u :=
  inf_eq_inf_iff_left
/-
**Finset.inter_eq_inter_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_eq_inter_iff_right : s inter u = t inter u ↔ t inter u subseteq s ∧ 
s inter u subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_eq_inf_iff_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : 
α}, a ⊓ c = b ⊓ c ↔ b ⊓ c ≤ a ∧ a ⊓ c ≤ b
-/
theorem inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t :=
  inf_eq_inf_iff_right
/-
**Finset.ite_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ite_subset_union (s s' : Finset α) (P : Prop) [Decidable P] : ite P s s' s
ubseteq s union s'
参数：s s' : Finset α；P : Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ite_le_sup`：ite_le_sup (a b : α) (P : Prop) [Decidable P] : ite P a b <=
 a ⊔ b
-/
theorem ite_subset_union (s s' : Finset α) (P : Prop) [Decidable P] : ite P s s' ⊆ s ∪ s' :=
  ite_le_sup s s' P
/-
**Finset.inter_subset_ite** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_subset_ite (s s' : Finset α) (P : Prop) [Decidable P] : s inter s' s
ubseteq ite P s s'
参数：s s' : Finset α；P : Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_ite`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α) (P : Prop
) [inst_1 : Decidable P], a ⊓ b ≤ if P then a else b
-/
theorem inter_subset_ite (s s' : Finset α) (P : Prop) [Decidable P] : s ∩ s' ⊆ ite P s s' :=
  inf_le_ite s s' P

end Lattice

end Finset

