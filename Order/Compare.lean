/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Ordering.Basic
public import Mathlib.Order.OrderDual

/-!
# Comparison

This file provides basic results about orderings and comparison in linear orders.


## Definitions

* `CmpLE`: An `Ordering` from `≤`.
* `Ordering.Compares`: Turns an `Ordering` into `<` and `=` propositions.
* `linearOrderOfCompares`: Constructs a `LinearOrder` instance from the fact that any two
  elements that are not one strictly less than the other either way are equal.
-/

@[expose] public section


variable {α β : Type*}

/-- Like `cmp`, but uses a `≤` on the type instead of `<`. Given two elements `x` and `y`, returns a
three-way comparison result `Ordering`. -/
/-
**cmpLE** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：cmpLE {α} [LE α] [DecidableLE α] (x y : α) : Ordering
参数：x y : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Like `cmp`, but uses a `≤` on the type instead of `<`. Given two elements `x` an
d `y`, returns a
three-way comparison result `Ordering`.
-/
def cmpLE {α} [LE α] [DecidableLE α] (x y : α) : Ordering :=
  if x ≤ y then if y ≤ x then Ordering.eq else Ordering.lt else Ordering.gt
/-
**cmpLE_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmpLE_swap {α} [LE α] [@Std.Total α (· <= ·)] [DecidableLE α] (x y : α) : 
(cmpLE x y).swap = cmpLE y x
参数：· <= ·；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
-/
theorem cmpLE_swap {α} [LE α] [@Std.Total α (· ≤ ·)] [DecidableLE α] (x y : α) :
    (cmpLE x y).swap = cmpLE y x := by
  by_cases xy : x ≤ y <;> by_cases yx : y ≤ x <;> simp [cmpLE, *, Ordering.swap]
  cases not_or_intro xy yx (total_of _ _ _)
/-
**cmpLE_eq_cmp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmpLE_eq_cmp {α} [Preorder α] [@Std.Total α (· <= ·)] [DecidableLE α] [Dec
idableLT α] (x y : α) : cmpLE x y = cmp x y
参数：· <= ·；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
-/
theorem cmpLE_eq_cmp {α} [Preorder α] [@Std.Total α (· ≤ ·)] [DecidableLE α] [DecidableLT α]
    (x y : α) : cmpLE x y = cmp x y := by
  by_cases xy : x ≤ y <;> by_cases yx : y ≤ x <;> simp [cmpLE, lt_iff_le_not_ge, *, cmp, cmpUsing]
  cases not_or_intro xy yx (total_of _ _ _)

namespace Ordering

/-
**Ordering.compares_swap** 是 Mathlib 中的一个定理，位于命名空间 `Ordering`。
形式化陈述：compares_swap [LT α] {a b : α} {o : Ordering} : o.swap.Compares a b ↔ o.Co
mpares b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem compares_swap [LT α] {a b : α} {o : Ordering} : o.swap.Compares a b ↔ o.Compares b a := by
  cases o
  · exact Iff.rfl
  · exact eq_comm
  · exact Iff.rfl

alias ⟨Compares.of_swap, Compares.swap⟩ := compares_swap
/-
**Ordering.swap_eq_iff_eq_swap** 是 Mathlib 中的一个定理，位于命名空间 `Ordering`。
形式化陈述：swap_eq_iff_eq_swap {o o' : Ordering} : o.swap = o' ↔ o = o'.swap
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordering.swap_inj`：∀ {o₁ o₂ : Ordering}, o₁.swap = o₂.swap ↔ o₁ = o₂
· 使用定理 `Ordering.swap_swap`：∀ {o : Ordering}, o.swap.swap = o
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem swap_eq_iff_eq_swap {o o' : Ordering} : o.swap = o' ↔ o = o'.swap := by
  rw [← swap_inj, swap_swap]
/-
**Ordering.Compares.eq_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordering.Compares`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {o : Ordering} {a b : α}, o.Compares 
a b → (o = Ordering.lt ↔ a < b)
参数：o = Ordering.lt ↔ a < b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_asymm`：lt_asymm (h : a < b) : ¬b < a
-/
theorem Compares.eq_lt [Preorder α] : ∀ {o} {a b : α}, Compares o a b → (o = lt ↔ a < b)
  | lt, _, _, h => ⟨fun _ => h, fun _ => rfl⟩
  | eq, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_lt h' h).elim⟩
  | gt, a, b, h => ⟨fun h => by injection h, fun h' => (lt_asymm h h').elim⟩
/-
**Ordering.Compares.ne_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordering.Compares`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {o : Ordering} {a b : α}, o.Compares 
a b → (o ≠ Ordering.lt ↔ b ≤ a)
参数：o ≠ Ordering.lt ↔ b ≤ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Compares.ne_lt [Preorder α] : ∀ {o} {a b : α}, Compares o a b → (o ≠ lt ↔ b ≤ a)
  | lt, _, _, h => ⟨absurd rfl, fun h' => (not_le_of_gt h h').elim⟩
  | eq, _, _, h => ⟨fun _ => ge_of_eq h, fun _ h => by injection h⟩
  | gt, _, _, h => ⟨fun _ => le_of_lt h, fun _ h => by injection h⟩
/-
**Ordering.Compares.eq_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordering.Compares`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {o : Ordering} {a b : α}, o.Compares 
a b → (o = Ordering.eq ↔ a = b)
参数：o = Ordering.eq ↔ a = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem Compares.eq_eq [Preorder α] : ∀ {o} {a b : α}, Compares o a b → (o = eq ↔ a = b)
  | lt, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_lt h h').elim⟩
  | eq, _, _, h => ⟨fun _ => h, fun _ => rfl⟩
  | gt, a, b, h => ⟨fun h => by injection h, fun h' => (ne_of_gt h h').elim⟩
/-
**Ordering.Compares.eq_gt** 是 Mathlib 中的一个定理，位于命名空间 `Ordering.Compares`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {o : Ordering} {a b : α}, o.Compares 
a b → (o = Ordering.gt ↔ b < a)
参数：o = Ordering.gt ↔ b < a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ordering.swap_eq_iff_eq_swap`：swap_eq_iff_eq_swap {o o' : Ordering} : o.
swap = o' ↔ o = o'.swap
· 使用定理 `Ordering.Compares.eq_lt`：∀ {α : Type u_1} [inst : Preorder α] {o : Order
ing} {a b : α}, o.Compares a b → (o = Ordering.lt ↔ a < b)
· 使用定理 `Ordering.Compares.swap`：∀ {α : Type u_1} [inst : LT α] {a b : α} {o : Or
dering}, o.Compares b a → o.swap.Compares a b
-/
theorem Compares.eq_gt [Preorder α] {o} {a b : α} (h : Compares o a b) : o = gt ↔ b < a :=
  swap_eq_iff_eq_swap.symm.trans h.swap.eq_lt
/-
**Ordering.Compares.ne_gt** 是 Mathlib 中的一个定理，位于命名空间 `Ordering.Compares`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {o : Ordering} {a b : α}, o.Compares 
a b → (o ≠ Ordering.gt ↔ a ≤ b)
参数：o ≠ Ordering.gt ↔ a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ordering.swap_eq_iff_eq_swap`：swap_eq_iff_eq_swap {o o' : Ordering} : o.
swap = o' ↔ o = o'.swap
· 使用定理 `Ordering.Compares.ne_lt`：∀ {α : Type u_1} [inst : Preorder α] {o : Order
ing} {a b : α}, o.Compares a b → (o ≠ Ordering.lt ↔ b ≤ a)
· 使用定理 `Ordering.Compares.swap`：∀ {α : Type u_1} [inst : LT α] {a b : α} {o : Or
dering}, o.Compares b a → o.swap.Compares a b
-/
theorem Compares.ne_gt [Preorder α] {o} {a b : α} (h : Compares o a b) : o ≠ gt ↔ a ≤ b :=
  (not_congr swap_eq_iff_eq_swap.symm).trans h.swap.ne_lt
/-
**Ordering.Compares.le_total** 是 Mathlib 中的一个定理，位于命名空间 `Ordering.Compares`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α} {o : Ordering}, o.Compares 
a b → a ≤ b ∨ b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem Compares.le_total [Preorder α] {a b : α} : ∀ {o}, Compares o a b → a ≤ b ∨ b ≤ a
  | lt, h => Or.inl (le_of_lt h)
  | eq, h => Or.inl (le_of_eq h)
  | gt, h => Or.inr (le_of_lt h)
/-
**Ordering.Compares.le_antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Ordering.Compares`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α} {o : Ordering}, o.Compares 
a b → a ≤ b → b ≤ a → a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem Compares.le_antisymm [Preorder α] {a b : α} : ∀ {o}, Compares o a b → a ≤ b → b ≤ a → a = b
  | lt, h, _, hba => (not_le_of_gt h hba).elim
  | eq, h, _, _ => h
  | gt, h, hab, _ => (not_le_of_gt h hab).elim
/-
**Ordering.Compares.inj** 是 Mathlib 中的一个定理，位于命名空间 `Ordering.Compares`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {o₁ o₂ : Ordering} {a b : α}, o₁.Comp
ares a b → o₂.Compares a b → o₁ = o₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordering.Compares.eq_lt`：∀ {α : Type u_1} [inst : Preorder α] {o : Order
ing} {a b : α}, o.Compares a b → (o = Ordering.lt ↔ a < b)
· 使用定理 `Ordering.Compares.eq_eq`：∀ {α : Type u_1} [inst : Preorder α] {o : Order
ing} {a b : α}, o.Compares a b → (o = Ordering.eq ↔ a = b)
· 使用定理 `Ordering.Compares.eq_gt`：∀ {α : Type u_1} [inst : Preorder α] {o : Order
ing} {a b : α}, o.Compares a b → (o = Ordering.gt ↔ b < a)
-/
theorem Compares.inj [Preorder α] {o₁} :
    ∀ {o₂} {a b : α}, Compares o₁ a b → Compares o₂ a b → o₁ = o₂
  | lt, _, _, h₁, h₂ => h₁.eq_lt.2 h₂
  | eq, _, _, h₁, h₂ => h₁.eq_eq.2 h₂
  | gt, _, _, h₁, h₂ => h₁.eq_gt.2 h₂
/-
**Ordering.compares_iff_of_compares_impl** 是 Mathlib 中的一个定理，位于命名空间 `Ordering`。
形式化陈述：compares_iff_of_compares_impl [LinearOrder α] [Preorder β] {a b : α} {a' b
' : β} (h : forall {o}, Compares o a b -> Compares o a' b') (o) : Compares o a b
 ↔ Compares o a' b'
参数：h : forall {o}, Compares o a b -> Compares o a' b'；o。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordering.Compares.inj`：∀ {α : Type u_1} [inst : Preorder α] {o₁ o₂ : Ord
ering} {a b : α}, o₁.Compares a b → o₂.Compares a b → o₁ = o₂
-/
theorem compares_iff_of_compares_impl [LinearOrder α] [Preorder β] {a b : α} {a' b' : β}
    (h : ∀ {o}, Compares o a b → Compares o a' b') (o) : Compares o a b ↔ Compares o a' b' := by
  refine ⟨h, fun ho => ?_⟩
  rcases lt_trichotomy a b with hab | hab | hab
  · have hab : Compares Ordering.lt a b := hab
    rwa [ho.inj (h hab)]
  · have hab : Compares Ordering.eq a b := hab
    rwa [ho.inj (h hab)]
  · have hab : Compares Ordering.gt a b := hab
    rwa [ho.inj (h hab)]

end Ordering

open Ordering OrderDual

@[simp]
/-
**toDual_compares_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_compares_toDual [LT α] {a b : α} {o : Ordering} : Compares o (toDua
l a) (toDual b) ↔ Compares o b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem toDual_compares_toDual [LT α] {a b : α} {o : Ordering} :
    Compares o (toDual a) (toDual b) ↔ Compares o b a := by
  cases o
  exacts [Iff.rfl, eq_comm, Iff.rfl]

@[simp]
/-
**ofDual_compares_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_compares_ofDual [LT α] {a b : αᵒᵈ} {o : Ordering} : Compares o (ofD
ual a) (ofDual b) ↔ Compares o b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem ofDual_compares_ofDual [LT α] {a b : αᵒᵈ} {o : Ordering} :
    Compares o (ofDual a) (ofDual b) ↔ Compares o b a := by
  cases o
  exacts [Iff.rfl, eq_comm, Iff.rfl]
/-
**cmp_compares** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_compares [LinearOrder α] (a b : α) : (cmp a b).Compares a b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
-/
theorem cmp_compares [LinearOrder α] (a b : α) : (cmp a b).Compares a b := by
  obtain h | h | h := lt_trichotomy a b <;> simp [cmp, cmpUsing, h, h.not_gt]
/-
**Ordering.Compares.cmp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ordering.Compares.cmp_eq [LinearOrder α] {a b : α} {o : Ordering} (h : o.C
ompares a b) : cmp a b = o
参数：h : o.Compares a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordering.Compares.inj`：∀ {α : Type u_1} [inst : Preorder α] {o₁ o₂ : Ord
ering} {a b : α}, o₁.Compares a b → o₂.Compares a b → o₁ = o₂
· 使用定理 `cmp_compares`：cmp_compares [LinearOrder α] (a b : α) : (cmp a b).Compare
s a b
-/
theorem Ordering.Compares.cmp_eq [LinearOrder α] {a b : α} {o : Ordering} (h : o.Compares a b) :
    cmp a b = o :=
  (cmp_compares a b).inj h

@[simp]
/-
**cmp_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_swap [Preorder α] [DecidableLT α] (a b : α) : (cmp a b).swap = cmp b a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem cmp_swap [Preorder α] [DecidableLT α] (a b : α) : (cmp a b).swap = cmp b a := by
  unfold cmp cmpUsing
  by_cases h : a < b <;> by_cases h₂ : b < a <;> simp_all [lt_asymm]

@[simp]
/-
**cmpLE_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmpLE_toDual [LE α] [DecidableLE α] (x y : α) : cmpLE (toDual x) (toDual y
) = cmpLE y x
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cmpLE_toDual [LE α] [DecidableLE α] (x y : α) : cmpLE (toDual x) (toDual y) = cmpLE y x :=
  rfl

@[simp]
/-
**cmpLE_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmpLE_ofDual [LE α] [DecidableLE α] (x y : αᵒᵈ) : cmpLE (ofDual x) (ofDual
 y) = cmpLE y x
参数：x y : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cmpLE_ofDual [LE α] [DecidableLE α] (x y : αᵒᵈ) : cmpLE (ofDual x) (ofDual y) = cmpLE y x :=
  rfl

@[simp]
/-
**cmp_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_toDual [LT α] [DecidableLT α] (x y : α) : cmp (toDual x) (toDual y) = 
cmp y x
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cmp_toDual [LT α] [DecidableLT α] (x y : α) : cmp (toDual x) (toDual y) = cmp y x :=
  rfl

@[simp]
/-
**cmp_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_ofDual [LT α] [DecidableLT α] (x y : αᵒᵈ) : cmp (ofDual x) (ofDual y) 
= cmp y x
参数：x y : αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cmp_ofDual [LT α] [DecidableLT α] (x y : αᵒᵈ) : cmp (ofDual x) (ofDual y) = cmp y x :=
  rfl

/-- Generate a linear order structure from a preorder and `cmp` function. -/
@[instance_reducible]
/-
**linearOrderOfCompares** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：linearOrderOfCompares [Preorder α] (cmp : α -> α -> Ordering) (h : forall 
a b, (cmp a b).Compares a b) : LinearOrder α
参数：cmp : α -> α -> Ordering；h : forall a b, (cmp a b).Compares a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generate a linear order structure from a preorder and `cmp` function.
-/
def linearOrderOfCompares [Preorder α] (cmp : α → α → Ordering)
    (h : ∀ a b, (cmp a b).Compares a b) : LinearOrder α :=
  let H : DecidableLE α := fun a b => decidable_of_iff _ (h a b).ne_gt
  { (inferInstance : Preorder α) with
    le_antisymm := fun a b => (h a b).le_antisymm,
    le_total := fun a b => (h a b).le_total,
    toMin := minOfLe,
    toMax := maxOfLe,
    toDecidableLE := H,
    toDecidableLT := fun a b => decidable_of_iff _ (h a b).eq_lt,
    toDecidableEq := fun a b => decidable_of_iff _ (h a b).eq_eq }

variable [LinearOrder α] (x y : α)

@[simp]
/-
**cmp_eq_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_eq_lt_iff : cmp x y = Ordering.lt ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordering.Compares.eq_lt`：∀ {α : Type u_1} [inst : Preorder α] {o : Order
ing} {a b : α}, o.Compares a b → (o = Ordering.lt ↔ a < b)
· 使用定理 `cmp_compares`：cmp_compares [LinearOrder α] (a b : α) : (cmp a b).Compare
s a b
-/
theorem cmp_eq_lt_iff : cmp x y = Ordering.lt ↔ x < y :=
  Ordering.Compares.eq_lt (cmp_compares x y)

@[simp]
/-
**cmp_eq_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_eq_eq_iff : cmp x y = Ordering.eq ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordering.Compares.eq_eq`：∀ {α : Type u_1} [inst : Preorder α] {o : Order
ing} {a b : α}, o.Compares a b → (o = Ordering.eq ↔ a = b)
· 使用定理 `cmp_compares`：cmp_compares [LinearOrder α] (a b : α) : (cmp a b).Compare
s a b
-/
theorem cmp_eq_eq_iff : cmp x y = Ordering.eq ↔ x = y :=
  Ordering.Compares.eq_eq (cmp_compares x y)

@[simp]
/-
**cmp_eq_gt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_eq_gt_iff : cmp x y = Ordering.gt ↔ y < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordering.Compares.eq_gt`：∀ {α : Type u_1} [inst : Preorder α] {o : Order
ing} {a b : α}, o.Compares a b → (o = Ordering.gt ↔ b < a)
· 使用定理 `cmp_compares`：cmp_compares [LinearOrder α] (a b : α) : (cmp a b).Compare
s a b
-/
theorem cmp_eq_gt_iff : cmp x y = Ordering.gt ↔ y < x :=
  Ordering.Compares.eq_gt (cmp_compares x y)

@[simp]
/-
**cmp_self_eq_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_self_eq_eq : cmp x x = Ordering.eq
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cmp_eq_eq_iff`：cmp_eq_eq_iff : cmp x y = Ordering.eq ↔ x = y
-/
theorem cmp_self_eq_eq : cmp x x = Ordering.eq := by rw [cmp_eq_eq_iff]

variable {x y} {β : Type*} [LinearOrder β] {x' y' : β}
/-
**cmp_eq_cmp_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y' x'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `cmp_swap`：cmp_swap [Preorder α] [DecidableLT α] (a b : α) : (cmp a b).sw
ap = cmp b a
· 使用定理 `Ordering.swap_inj`：∀ {o₁ o₂ : Ordering}, o₁.swap = o₂.swap ↔ o₁ = o₂
-/
theorem cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y' x' :=
  ⟨fun h => by rwa [← cmp_swap x', ← cmp_swap, swap_inj],
   fun h => by rwa [← cmp_swap y', ← cmp_swap, swap_inj]⟩
/-
**lt_iff_lt_of_cmp_eq_cmp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_iff_lt_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x < y ↔ x' < y'
参数：h : cmp x y = cmp x' y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `cmp_eq_lt_iff`：cmp_eq_lt_iff : cmp x y = Ordering.lt ↔ x < y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_iff_lt_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x < y ↔ x' < y' := by
  rw [← cmp_eq_lt_iff, ← cmp_eq_lt_iff, h]
/-
**le_iff_le_of_cmp_eq_cmp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_le_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x <= y ↔ x' <= y'
参数：h : cmp x y = cmp x' y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `lt_iff_lt_of_cmp_eq_cmp`：lt_iff_lt_of_cmp_eq_cmp (h : cmp x y = cmp x' y
') : x < y ↔ x' < y'
· 使用定理 `cmp_eq_cmp_symm`：cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y
' x'
-/
theorem le_iff_le_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x ≤ y ↔ x' ≤ y' := by
  rw [← not_lt, ← not_lt]
  apply not_congr
  apply lt_iff_lt_of_cmp_eq_cmp
  rwa [cmp_eq_cmp_symm]
/-
**eq_iff_eq_of_cmp_eq_cmp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_iff_eq_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x = y ↔ x' = y'
参数：h : cmp x y = cmp x' y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `le_iff_le_of_cmp_eq_cmp`：le_iff_le_of_cmp_eq_cmp (h : cmp x y = cmp x' y
') : x <= y ↔ x' <= y'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cmp_eq_cmp_symm`：cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y
' x'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_iff_eq_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x = y ↔ x' = y' := by
  rw [le_antisymm_iff, le_antisymm_iff, le_iff_le_of_cmp_eq_cmp h,
      le_iff_le_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 h)]
/-
**LT.lt.cmp_eq_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LT.lt.cmp_eq_lt (h : x < y) : cmp x y = Ordering.lt
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `cmp_eq_lt_iff`：cmp_eq_lt_iff : cmp x y = Ordering.lt ↔ x < y
-/
theorem LT.lt.cmp_eq_lt (h : x < y) : cmp x y = Ordering.lt :=
  (cmp_eq_lt_iff _ _).2 h
/-
**LT.lt.cmp_eq_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LT.lt.cmp_eq_gt (h : x < y) : cmp y x = Ordering.gt
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `cmp_eq_gt_iff`：cmp_eq_gt_iff : cmp x y = Ordering.gt ↔ y < x
-/
theorem LT.lt.cmp_eq_gt (h : x < y) : cmp y x = Ordering.gt :=
  (cmp_eq_gt_iff _ _).2 h
/-
**Eq.cmp_eq_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Eq.cmp_eq_eq (h : x = y) : cmp x y = Ordering.eq
参数：h : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `cmp_eq_eq_iff`：cmp_eq_eq_iff : cmp x y = Ordering.eq ↔ x = y
-/
theorem Eq.cmp_eq_eq (h : x = y) : cmp x y = Ordering.eq :=
  (cmp_eq_eq_iff _ _).2 h
/-
**Eq.cmp_eq_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Eq.cmp_eq_eq' (h : x = y) : cmp y x = Ordering.eq
参数：h : x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.cmp_eq_eq`：Eq.cmp_eq_eq (h : x = y) : cmp x y = Ordering.eq
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Eq.cmp_eq_eq' (h : x = y) : cmp y x = Ordering.eq :=
  h.symm.cmp_eq_eq
