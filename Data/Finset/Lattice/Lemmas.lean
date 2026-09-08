/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# Lemmas about the lattice structure of finite sets

This file contains many results on the lattice structure of `Finset α`, in particular the
interaction between union, intersection, empty set and inserting elements.

## Tags

finite sets, finset

-/

public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### Lattice structure -/


section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a b : α}

/-
**Finset.disjoint_iff_inter_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjoint_iff_inter_eq_empty : Disjoint s t ↔ s inter t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
-/
theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

/-! #### union -/

@[simp]
/-
**Finset.union_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_empty (s : Finset α) : s union ∅ = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
#### union
-/
theorem union_empty (s : Finset α) : s ∪ ∅ = s :=
  ext fun x => mem_union.trans <| by simp

@[simp]
/-
**Finset.empty_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_union (s : Finset α) : ∅ union s = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem empty_union (s : Finset α) : ∅ ∪ s = s :=
  ext fun x => mem_union.trans <| by simp

@[aesop unsafe apply (rule_sets := [finsetNonempty])]
/-
**Finset.Nonempty.inl** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, s.Nonempty → (s 
∪ t).Nonempty
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.mono`：∀ {α : Type u_1} {s t : Finset α}, s ⊆ t → s.Nonem
pty → t.Nonempty
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
-/
theorem Nonempty.inl {s t : Finset α} (h : s.Nonempty) : (s ∪ t).Nonempty :=
  h.mono subset_union_left

@[aesop unsafe apply (rule_sets := [finsetNonempty])]
/-
**Finset.Nonempty.inr** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, t.Nonempty → (s 
∪ t).Nonempty
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.mono`：∀ {α : Type u_1} {s t : Finset α}, s ⊆ t → s.Nonem
pty → t.Nonempty
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
-/
theorem Nonempty.inr {s t : Finset α} (h : t.Nonempty) : (s ∪ t).Nonempty :=
  h.mono subset_union_right
/-
**Finset.insert_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_eq (a : α) (s : Finset α) : insert a s = {a} union s
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_eq (a : α) (s : Finset α) : insert a s = {a} ∪ s :=
  rfl

@[simp, grind =]
/-
**Finset.singleton_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：singleton_union (x : α) (s : Finset α) : {x} union s = insert x s
参数：x : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma singleton_union (x : α) (s : Finset α) : {x} ∪ s = insert x s :=
  rfl

/- We lower the simp-priority of `union_singleton` to ensure that `{x} ∪ {y}`
simplifies to `{x, y}` and not `{y, x}`. -/

@[simp 900, grind =]
/-
**Finset.union_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：union_singleton (x : α) (s : Finset α) : s union {x} = insert x s
参数：x : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用引理 `Finset.singleton_union`：singleton_union (x : α) (s : Finset α) : {x} uni
on s = insert x s

--- 原说明 ---
We lower the simp-priority of `union_singleton` to ensure that `{x} ∪ {y}`
simplifies to `{x, y}` and not `{y, x}`.
-/
lemma union_singleton (x : α) (s : Finset α) : s ∪ {x} = insert x s := by
  rw [Finset.union_comm, singleton_union]

@[simp, grind =]
/-
**Finset.insert_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_union (a : α) (s t : Finset α) : insert a s union t = insert a (s u
nion t)
参数：a : α；s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_assoc`：union_assoc (s₁ s₂ s₃ : Finset α) : s₁ union s₂ unio
n s₃ = s₁ union (s₂ union s₃)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_union (a : α) (s t : Finset α) : insert a s ∪ t = insert a (s ∪ t) := by
  simp only [insert_eq, union_assoc]

@[simp, grind =]
/-
**Finset.union_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_insert (a : α) (s t : Finset α) : s union insert a t = insert a (s u
nion t)
参数：a : α；s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_left_comm`：union_left_comm (s t u : Finset α) : s union (t 
union u) = t union (s union u)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem union_insert (a : α) (s t : Finset α) : s ∪ insert a t = insert a (s ∪ t) := by
  simp only [insert_eq, union_left_comm]
/-
**Finset.insert_union_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_union_distrib (a : α) (s t : Finset α) : insert a (s union t) = ins
ert a s union insert a t
参数：a : α；s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Finset.insert_idem`：insert_idem (a : α) (s : Finset α) : insert a (inser
t a s) = insert a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insert_union_distrib (a : α) (s t : Finset α) :
    insert a (s ∪ t) = insert a s ∪ insert a t := by
  simp only [insert_union, union_insert, insert_idem]

/-- To prove a relation on pairs of `Finset X`, it suffices to show that it is
  * symmetric,
  * it holds when one of the `Finset`s is empty,
  * it holds for pairs of singletons,
  * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
/-
**Finset.induction_on_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：induction_on_union (P : Finset α -> Finset α -> Prop) (symm : forall {a b}
, P a b -> P b a) (empty_right : forall {a}, P a ∅) (singletons : forall {a b}, 
P {a} {b}) (union_of : forall {a b c}, P a c -> P b c -> P (a union b) c) : fora
ll a b, P a b
参数：P : Finset α -> Finset α -> Prop；symm : forall {a b}, P a b -> P b a；empty_ri
ght : forall {a}, P a ∅；singletons : forall {a b}, P {a} {b}；union_of : forall {
a b c}, P a c -> P b c -> P (a union b) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_eq`：insert_eq (a : α) (s : Finset α) : insert a s = {a} un
ion s

--- 原说明 ---
To prove a relation on pairs of `Finset X`, it suffices to show that it is
  * symmetric,
  * it holds when one of the `Finset`s is empty,
  * it holds for pairs of singletons,
  * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
theorem induction_on_union (P : Finset α → Finset α → Prop) (symm : ∀ {a b}, P a b → P b a)
    (empty_right : ∀ {a}, P a ∅) (singletons : ∀ {a b}, P {a} {b})
    (union_of : ∀ {a b c}, P a c → P b c → P (a ∪ b) c) : ∀ a b, P a b := by
  intro a b
  refine Finset.induction_on b empty_right fun x s _xs hi => symm ?_
  rw [Finset.insert_eq]
  apply union_of _ (symm hi)
  refine Finset.induction_on a empty_right fun a t _ta hi => symm ?_
  rw [Finset.insert_eq]
  exact union_of singletons (symm hi)

/-! #### inter -/

@[simp]
/-
**Finset.inter_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_empty (s : Finset α) : s inter ∅ = ∅
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
#### inter
-/
theorem inter_empty (s : Finset α) : s ∩ ∅ = ∅ :=
  ext fun _ => mem_inter.trans <| by simp

@[simp]
/-
**Finset.empty_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_inter (s : Finset α) : ∅ inter s = ∅
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem empty_inter (s : Finset α) : ∅ ∩ s = ∅ :=
  ext fun _ => mem_inter.trans <| by simp

@[simp]
/-
**Finset.insert_inter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_inter_of_mem {s₁ s₂ : Finset α} {a : α} (h : a in s₂) : insert a s₁
 inter s₂ = insert a (s₁ inter s₂)
参数：h : a in s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `or_iff_right_of_imp`：∀ {a b : Prop}, (a → b) → (a ∨ b ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem insert_inter_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₂) :
    insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
  ext fun x => by
    have : x = a ∨ x ∈ s₂ ↔ x ∈ s₂ := or_iff_right_of_imp <| by rintro rfl; exact h
    simp only [mem_inter, mem_insert, or_and_left, this]

@[simp]
/-
**Finset.inter_insert_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_insert_of_mem {s₁ s₂ : Finset α} {a : α} (h : a in s₁) : s₁ inter in
sert a s₂ = insert a (s₁ inter s₂)
参数：h : a in s₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.insert_inter_of_mem`：insert_inter_of_mem {s₁ s₂ : Finset α} {a : 
α} (h : a in s₂) : insert a s₁ inter s₂ = insert a (s₁ inter s₂)
-/
theorem inter_insert_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₁) :
    s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) := by rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp]
/-
**Finset.insert_inter_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_inter_of_notMem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₂) : insert a 
s₁ inter s₂ = s₁ inter s₂
参数：h : a ∉ s₂。
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
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem insert_inter_of_notMem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₂) :
    insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
  ext fun x => by
    have : ¬(x = a ∧ x ∈ s₂) := by rintro ⟨rfl, H⟩; exact h H
    simp only [mem_inter, mem_insert, or_and_right, this, false_or]

@[simp]
/-
**Finset.inter_insert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_insert_of_notMem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₁) : s₁ inter 
insert a s₂ = s₁ inter s₂
参数：h : a ∉ s₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.insert_inter_of_notMem`：insert_inter_of_notMem {s₁ s₂ : Finset α}
 {a : α} (h : a ∉ s₂) : insert a s₁ inter s₂ = s₁ inter s₂
-/
theorem inter_insert_of_notMem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₁) :
    s₁ ∩ insert a s₂ = s₁ ∩ s₂ := by rw [inter_comm, insert_inter_of_notMem h, inter_comm]

@[grind =]
/-
**Finset.inter_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_insert {s₁ s₂ : Finset α} {a : α} : insert a s₁ inter s₂ = if a in s
₂ then insert a (s₁ inter s₂) else s₁ inter s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.insert_inter_of_mem`：insert_inter_of_mem {s₁ s₂ : Finset α} {a : 
α} (h : a in s₂) : insert a s₁ inter s₂ = insert a (s₁ inter s₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.insert_inter_of_notMem`：insert_inter_of_notMem {s₁ s₂ : Finset α}
 {a : α} (h : a ∉ s₂) : insert a s₁ inter s₂ = s₁ inter s₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem inter_insert {s₁ s₂ : Finset α} {a : α} :
    insert a s₁ ∩ s₂ = if a ∈ s₂ then insert a (s₁ ∩ s₂) else s₁ ∩ s₂ := by
  split_ifs <;> simp [*]

@[grind =]
/-
**Finset.insert_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_inter {s₁ s₂ : Finset α} {a : α} : s₁ inter insert a s₂ = if a in s
₁ then insert a (s₁ inter s₂) else s₁ inter s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.inter_insert_of_mem`：inter_insert_of_mem {s₁ s₂ : Finset α} {a : 
α} (h : a in s₁) : s₁ inter insert a s₂ = insert a (s₁ inter s₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.inter_insert_of_notMem`：inter_insert_of_notMem {s₁ s₂ : Finset α}
 {a : α} (h : a ∉ s₁) : s₁ inter insert a s₂ = s₁ inter s₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem insert_inter {s₁ s₂ : Finset α} {a : α} :
    s₁ ∩ insert a s₂ = if a ∈ s₁ then insert a (s₁ ∩ s₂) else s₁ ∩ s₂ := by
  split_ifs <;> simp [*]

@[simp]
/-
**Finset.singleton_inter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_inter_of_mem {a : α} {s : Finset α} (H : a in s) : {a} inter s =
 {a}
参数：H : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_inter_of_mem`：insert_inter_of_mem {s₁ s₂ : Finset α} {a : 
α} (h : a in s₂) : insert a s₁ inter s₂ = insert a (s₁ inter s₂)
· 使用定理 `Finset.empty_inter`：empty_inter (s : Finset α) : ∅ inter s = ∅
-/
theorem singleton_inter_of_mem {a : α} {s : Finset α} (H : a ∈ s) : {a} ∩ s = {a} :=
  show insert a ∅ ∩ s = insert a ∅ by rw [insert_inter_of_mem H, empty_inter]

@[simp]
/-
**Finset.singleton_inter_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_inter_of_notMem {a : α} {s : Finset α} (H : a ∉ s) : {a} inter s
 = ∅
参数：H : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem {s : Finset 
α} (H : forall x, x ∉ s) : s = ∅
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem singleton_inter_of_notMem {a : α} {s : Finset α} (H : a ∉ s) : {a} ∩ s = ∅ :=
  eq_empty_of_forall_notMem <| by
    simp only [mem_inter, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h

@[grind =]
/-
**Finset.singleton_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：singleton_inter {a : α} {s : Finset α} : {a} inter s = if a in s then {a} 
else ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.singleton_inter_of_mem`：singleton_inter_of_mem {a : α} {s : Finse
t α} (H : a in s) : {a} inter s = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.singleton_inter_of_notMem`：singleton_inter_of_notMem {a : α} {s :
 Finset α} (H : a ∉ s) : {a} inter s = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma singleton_inter {a : α} {s : Finset α} :
    {a} ∩ s = if a ∈ s then {a} else ∅ := by
  split_ifs with h <;> simp [h]

@[simp]
/-
**Finset.inter_singleton_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_singleton_of_mem {a : α} {s : Finset α} (h : a in s) : s inter {a} =
 {a}
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.singleton_inter_of_mem`：singleton_inter_of_mem {a : α} {s : Finse
t α} (H : a in s) : {a} inter s = {a}
-/
theorem inter_singleton_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ∩ {a} = {a} := by
  rw [inter_comm, singleton_inter_of_mem h]

@[simp]
/-
**Finset.inter_singleton_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_singleton_of_notMem {a : α} {s : Finset α} (h : a ∉ s) : s inter {a}
 = ∅
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.singleton_inter_of_notMem`：singleton_inter_of_notMem {a : α} {s :
 Finset α} (H : a ∉ s) : {a} inter s = ∅
-/
theorem inter_singleton_of_notMem {a : α} {s : Finset α} (h : a ∉ s) : s ∩ {a} = ∅ := by
  rw [inter_comm, singleton_inter_of_notMem h]
/-
**Finset.inter_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inter_singleton {a : α} {s : Finset α} : s inter {a} = if a in s then {a} 
else ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.inter_singleton_of_mem`：inter_singleton_of_mem {a : α} {s : Finse
t α} (h : a in s) : s inter {a} = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.inter_singleton_of_notMem`：inter_singleton_of_notMem {a : α} {s :
 Finset α} (h : a ∉ s) : s inter {a} = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma inter_singleton {a : α} {s : Finset α} :
    s ∩ {a} = if a ∈ s then {a} else ∅ := by
  split_ifs with h <;> simp [h]
/-
**Finset.union_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, s ∪ t = ∅ ↔ s = 
∅ ∧ t = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_bot_iff`：sup_eq_bot_iff : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥
-/
@[simp] lemma union_eq_empty : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ := sup_eq_bot_iff
/-
**Finset.union_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, (s ∪ t).Nonempty
 ↔ s.Nonempty ∨ t.Nonempty
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_nonempty`：union_nonempty : (s union t).Nonempty ↔ s.Nonempty ∨
 t.Nonempty
-/
@[simp] lemma union_nonempty : (s ∪ t).Nonempty ↔ s.Nonempty ∨ t.Nonempty :=
  mod_cast Set.union_nonempty (α := α) (s := s) (t := t)
/-
**Finset.insert_union_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：insert_union_comm (s t : Finset α) (a : α) : insert a s union t = s union 
insert a t
参数：s t : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
-/
theorem insert_union_comm (s t : Finset α) (a : α) : insert a s ∪ t = s ∪ insert a t := by
  rw [insert_union, union_insert]

end Lattice

end Finset

namespace List

variable [DecidableEq α] {l l' : List α}

@[simp]
/-
**List.toFinset_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：toFinset_append : toFinset (l ++ l') = l.toFinset union l'.toFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.empty_union`：empty_union (s : Finset α) : ∅ union s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.toFinset_cons`：toFinset_cons : toFinset (a :: l) = insert a (toFins
et l)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
-/
theorem toFinset_append : toFinset (l ++ l') = l.toFinset ∪ l'.toFinset := by
  induction l with
  | nil => simp
  | cons hd tl hl => simp [hl]

end List

