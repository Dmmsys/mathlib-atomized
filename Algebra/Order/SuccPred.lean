/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Order.SuccPred.WithBot

/-!
# Interaction between successors and arithmetic

We define the `SuccAddOrder` and `PredSubOrder` typeclasses, for orders satisfying `succ x = x + 1`
and `pred x = x - 1` respectively. This allows us to transfer the API for successors and
predecessors into these common arithmetical forms.
-/

public section

/-- A typeclass for `succ x = x + 1`. -/
/-
**SuccAddOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Preorder α] → [Add α] → [One α] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass for `succ x = x + 1`.
-/
class SuccAddOrder (α : Type*) [Preorder α] [Add α] [One α] extends SuccOrder α where
  succ_eq_add_one (x : α) : succ x = x + 1

/-- A typeclass for `pred x = x - 1`. -/
/-
**PredSubOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Preorder α] → [Sub α] → [One α] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass for `pred x = x - 1`.
-/
class PredSubOrder (α : Type*) [Preorder α] [Sub α] [One α] extends PredOrder α where
  pred_eq_sub_one (x : α) : pred x = x - 1

variable {α : Type*} {x y : α}

namespace Order

section Preorder

variable [Preorder α]

section Add

variable [Add α] [One α] [SuccAddOrder α]

@[simp]
/-
**Order.succ_eq_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_eq_add_one (x : α) : succ x = x + 1
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccAddOrder.succ_eq_add_one`：∀ {α : Type u_1} {inst : Preorder α} {inst
_1 : Add α} {inst_2 : One α} [self : SuccAddOrder α] (x : α),   SuccOrder.succ x
 = x + 1
-/
theorem succ_eq_add_one (x : α) : succ x = x + 1 :=
  SuccAddOrder.succ_eq_add_one x
/-
**Order.add_one_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：add_one_le_of_lt (h : x < y) : x + 1 <= y
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
-/
theorem add_one_le_of_lt (h : x < y) : x + 1 ≤ y := by
  rw [← succ_eq_add_one]
  exact succ_le_of_lt h
/-
**Order.add_one_le_iff_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：add_one_le_iff_of_not_isMax (hx : ¬ IsMax x) : x + 1 <= y ↔ x < y
参数：hx : ¬ IsMax x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_one_le_iff_of_not_isMax (hx : ¬ IsMax x) : x + 1 ≤ y ↔ x < y := by
  rw [← succ_eq_add_one, succ_le_iff_of_not_isMax hx]
/-
**Order.add_one_le_iff_of_not_isMax'** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：add_one_le_iff_of_not_isMax' (hy : ¬ IsMax y) : x + 1 <= y ↔ x < y
参数：hy : ¬ IsMax y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Order.succ_le_iff_of_not_isMax'`：succ_le_iff_of_not_isMax' (hb : ¬IsMax 
b) : succ a <= b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_one_le_iff_of_not_isMax' (hy : ¬ IsMax y) : x + 1 ≤ y ↔ x < y := by
  rw [← succ_eq_add_one, succ_le_iff_of_not_isMax' hy]

@[simp]
/-
**Order.add_one_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：add_one_le_iff [NoMaxOrder α] : x + 1 <= y ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.add_one_le_iff_of_not_isMax`：add_one_le_iff_of_not_isMax (hx : ¬ I
sMax x) : x + 1 <= y ↔ x < y
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem add_one_le_iff [NoMaxOrder α] : x + 1 ≤ y ↔ x < y :=
  add_one_le_iff_of_not_isMax (not_isMax x)

@[simp]
/-
**Order.wcovBy_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：wcovBy_add_one (x : α) : x ⩿ x + 1
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Order.wcovBy_succ`：wcovBy_succ (a : α) : a ⩿ succ a
-/
theorem wcovBy_add_one (x : α) : x ⩿ x + 1 := by
  rw [← succ_eq_add_one]
  exact wcovBy_succ x

@[simp]
/-
**Order.covBy_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：covBy_add_one [NoMaxOrder α] (x : α) : x ⋖ x + 1
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Order.covBy_succ`：covBy_succ (a : α) : a ⋖ succ a
-/
theorem covBy_add_one [NoMaxOrder α] (x : α) : x ⋖ x + 1 := by
  rw [← succ_eq_add_one]
  exact covBy_succ x

end Add

section Sub

variable [Sub α] [One α] [PredSubOrder α]

@[simp]
/-
**Order.pred_eq_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：pred_eq_sub_one (x : α) : pred x = x - 1
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PredSubOrder.pred_eq_sub_one`：∀ {α : Type u_1} {inst : Preorder α} {inst
_1 : Sub α} {inst_2 : One α} [self : PredSubOrder α] (x : α),   PredOrder.pred x
 = x - 1
-/
theorem pred_eq_sub_one (x : α) : pred x = x - 1 :=
  PredSubOrder.pred_eq_sub_one x
/-
**Order.le_sub_one_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_sub_one_of_lt (h : x < y) : x <= y - 1
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用定理 `Order.le_pred_of_lt`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pred
Order α] {a b : α}, b < a → b ≤ Order.pred a
-/
theorem le_sub_one_of_lt (h : x < y) : x ≤ y - 1 := by
  rw [← pred_eq_sub_one]
  exact le_pred_of_lt h
/-
**Order.le_sub_one_iff_of_not_isMin** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_sub_one_iff_of_not_isMin (hy : ¬ IsMin y) : x <= y - 1 ↔ x < y
参数：hy : ¬ IsMin y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用定理 `Order.le_pred_iff_of_not_isMin`：∀ {α : Type u_1} [inst : Preorder α] [in
st_1 : PredOrder α] {a b : α}, ¬IsMin a → (b ≤ Order.pred a ↔ b < a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_sub_one_iff_of_not_isMin (hy : ¬ IsMin y) : x ≤ y - 1 ↔ x < y := by
  rw [← pred_eq_sub_one, le_pred_iff_of_not_isMin hy]

@[simp]
/-
**Order.le_sub_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_sub_one_iff [NoMinOrder α] : x <= y - 1 ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_sub_one_iff_of_not_isMin`：le_sub_one_iff_of_not_isMin (hy : ¬ I
sMin y) : x <= y - 1 ↔ x < y
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
theorem le_sub_one_iff [NoMinOrder α] : x ≤ y - 1 ↔ x < y :=
  le_sub_one_iff_of_not_isMin (not_isMin y)

@[simp]
/-
**Order.sub_one_wcovBy** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：sub_one_wcovBy (x : α) : x - 1 ⩿ x
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用定理 `Order.pred_wcovBy`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOr
der α] (a : α), Order.pred a ⩿ a
-/
theorem sub_one_wcovBy (x : α) : x - 1 ⩿ x := by
  rw [← pred_eq_sub_one]
  exact pred_wcovBy x

@[simp]
/-
**Order.sub_one_covBy** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：sub_one_covBy [NoMinOrder α] (x : α) : x - 1 ⋖ x
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用定理 `Order.pred_covBy`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOrd
er α] [NoMinOrder α] (a : α), Order.pred a ⋖ a
-/
theorem sub_one_covBy [NoMinOrder α] (x : α) : x - 1 ⋖ x := by
  rw [← pred_eq_sub_one]
  exact pred_covBy x

end Sub

@[simp]
/-
**Order.succ_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_iterate [AddMonoidWithOne α] [SuccAddOrder α] (x : α) (n : Nat) : suc
c^[n] x = x + n
参数：x : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_zero_apply`：iterate_zero_apply (x : α) : f^[0] x = x
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem succ_iterate [AddMonoidWithOne α] [SuccAddOrder α] (x : α) (n : ℕ) :
    succ^[n] x = x + n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, add_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply', IH, Nat.cast_add, succ_eq_add_one, Nat.cast_one, add_assoc]

@[simp]
/-
**Order.pred_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：pred_iterate [AddCommGroupWithOne α] [PredSubOrder α] (x : α) (n : Nat) : 
pred^[n] x = x - n
参数：x : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_zero_apply`：iterate_zero_apply (x : α) : f^[0] x = x
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
-/
theorem pred_iterate [AddCommGroupWithOne α] [PredSubOrder α] (x : α) (n : ℕ) :
    pred^[n] x = x - n := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.cast_zero, sub_zero]
  | succ n IH =>
    rw [Function.iterate_succ_apply', IH, Nat.cast_add, pred_eq_sub_one, Nat.cast_one, sub_sub]

end Preorder

section PartialOrder

variable [PartialOrder α]

/-
**Order.not_isMax_zero** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isMax_zero [Zero α] [One α] [ZeroLEOneClass α] [NeZero (1 : α)] : ¬ Is
Max (0 : α)
参数：1 : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_isMax_iff`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, ¬IsMax a ↔ 
∃ b, a < b
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
-/
theorem not_isMax_zero [Zero α] [One α] [ZeroLEOneClass α] [NeZero (1 : α)] : ¬ IsMax (0 : α) := by
  rw [not_isMax_iff]
  exact ⟨1, one_pos⟩
/-
**Order.one_le_iff_pos** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)] [S
uccAddOrder α] : 1 <= x ↔ 0 < x
参数：1 : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_le_iff_of_not_isMax`：succ_le_iff_of_not_isMax (ha : ¬IsMax a)
 : succ a <= b ↔ a < b
· 使用定理 `Order.not_isMax_zero`：not_isMax_zero [Zero α] [One α] [ZeroLEOneClass α]
 [NeZero (1 : α)] : ¬ IsMax (0 : α)
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] : 1 ≤ x ↔ 0 < x := by
  rw [← succ_le_iff_of_not_isMax not_isMax_zero, succ_eq_add_one, zero_add]
/-
**Order.one_le_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZero (1 : α)] [SuccAddOrder α] 
[IsBotZeroClass α] : 1 <= x ↔ x != 0
参数：1 : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_le_iff_ne_zero [AddMonoidWithOne α] [NeZero (1 : α)]
    [SuccAddOrder α] [IsBotZeroClass α] : 1 ≤ x ↔ x ≠ 0 := by
  rw [Order.one_le_iff_pos, pos_iff_ne_zero]
/-
**Order.covBy_iff_add_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：covBy_iff_add_one_eq [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] : x ⋖
 y ↔ x + 1 = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Order.succ_eq_iff_covBy`：succ_eq_iff_covBy : succ a = b ↔ a ⋖ b
-/
theorem covBy_iff_add_one_eq [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    x ⋖ y ↔ x + 1 = y := by
  rw [← succ_eq_add_one]
  exact succ_eq_iff_covBy.symm
/-
**Order.covBy_iff_sub_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：covBy_iff_sub_one_eq [Sub α] [One α] [PredSubOrder α] [NoMinOrder α] : x ⋖
 y ↔ y - 1 = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Order.pred_eq_iff_covBy`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_
1 : PredOrder α] {a b : α} [NoMinOrder α], Order.pred a = b ↔ b ⋖ a
-/
theorem covBy_iff_sub_one_eq [Sub α] [One α] [PredSubOrder α] [NoMinOrder α] :
    x ⋖ y ↔ y - 1 = x := by
  rw [← pred_eq_sub_one]
  exact pred_eq_iff_covBy.symm
/-
**Order.IsSuccPrelimit.add_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPrelimi
t`。
形式化陈述：∀ {α : Type u_1} {x y : α} [inst : PartialOrder α] [inst_1 : Add α] [inst_
2 : One α] [SuccAddOrder α],   Order.IsSuccPrelimit x → y < x → y + 1 < x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Order.IsSuccPrelimit.succ_lt`：∀ {α : Type u_1} {a b : α} [inst : Partial
Order α] [inst_1 : SuccOrder α],   Order.IsSuccPrelimit b → a < b → Order.succ a
 < b
-/
theorem IsSuccPrelimit.add_one_lt [Add α] [One α] [SuccAddOrder α]
    (hx : IsSuccPrelimit x) (hy : y < x) : y + 1 < x := by
  rw [← succ_eq_add_one]
  exact hx.succ_lt hy
/-
**Order.IsPredPrelimit.lt_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsPredPrelimi
t`。
形式化陈述：∀ {α : Type u_1} {x y : α} [inst : PartialOrder α] [inst_1 : Sub α] [inst_
2 : One α] [PredSubOrder α],   Order.IsPredPrelimit x → x < y → x < y - 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用定理 `Order.IsPredPrelimit.lt_pred`：∀ {α : Type u_1} {a b : α} [inst : Partial
Order α] [inst_1 : PredOrder α],   Order.IsPredPrelimit b → b < a → b < Order.pr
ed a
-/
theorem IsPredPrelimit.lt_sub_one [Sub α] [One α] [PredSubOrder α]
    (hx : IsPredPrelimit x) (hy : x < y) : x < y - 1 := by
  rw [← pred_eq_sub_one]
  exact hx.lt_pred hy
/-
**Order.IsSuccLimit.add_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {x y : α} [inst : PartialOrder α] [inst_1 : Add α] [inst_
2 : One α] [SuccAddOrder α],   Order.IsSuccLimit x → y < x → y + 1 < x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.add_one_lt`：∀ {α : Type u_1} {x y : α} [inst : Part
ialOrder α] [inst_1 : Add α] [inst_2 : One α] [SuccAddOrder α],   Order.IsSuccPr
elimit x → y < x → y …
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem IsSuccLimit.add_one_lt [Add α] [One α] [SuccAddOrder α]
    (hx : IsSuccLimit x) (hy : y < x) : y + 1 < x :=
  hx.isSuccPrelimit.add_one_lt hy
/-
**Order.IsPredLimit.lt_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsPredLimit`。
形式化陈述：∀ {α : Type u_1} {x y : α} [inst : PartialOrder α] [inst_1 : Sub α] [inst_
2 : One α] [PredSubOrder α],   Order.IsPredLimit x → x < y → x < y - 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsPredPrelimit.lt_sub_one`：∀ {α : Type u_1} {x y : α} [inst : Part
ialOrder α] [inst_1 : Sub α] [inst_2 : One α] [PredSubOrder α],   Order.IsPredPr
elimit x → x < y → x …
· 使用定理 `Order.IsPredLimit.isPredPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsPredLimit a → Order.IsPredPrelimit a
-/
theorem IsPredLimit.lt_sub_one [Sub α] [One α] [PredSubOrder α]
    (hx : IsPredLimit x) (hy : x < y) : x < y - 1 :=
  hx.isPredPrelimit.lt_sub_one hy
/-
**Order.IsSuccPrelimit.add_natCast_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccPre
limit`。
形式化陈述：∀ {α : Type u_1} {x y : α} [inst : PartialOrder α] [inst_1 : AddMonoidWith
One α] [SuccAddOrder α],   Order.IsSuccPrelimit x → y < x → ∀ (n : ℕ), y + ↑n < 
x
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsSuccPrelimit.add_natCast_lt [AddMonoidWithOne α] [SuccAddOrder α]
    (hx : IsSuccPrelimit x) (hy : y < x) : ∀ n : ℕ, y + n < x
  | 0 => by simpa
  | n + 1 => by
    rw [Nat.cast_add_one, ← add_assoc]
    exact hx.add_one_lt (hx.add_natCast_lt hy n)
/-
**Order.IsPredPrelimit.lt_sub_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsPredPre
limit`。
形式化陈述：∀ {α : Type u_1} {x y : α} [inst : PartialOrder α] [inst_1 : AddCommGroupW
ithOne α] [PredSubOrder α],   Order.IsPredPrelimit x → x < y → ∀ (n : ℕ), x < y 
- ↑n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsPredPrelimit.lt_sub_natCast [AddCommGroupWithOne α] [PredSubOrder α]
    (hx : IsPredPrelimit x) (hy : x < y) : ∀ n : ℕ, x < y - n
  | 0 => by simpa
  | n + 1 => by
    rw [Nat.cast_add_one, ← sub_sub]
    exact hx.lt_sub_one (hx.lt_sub_natCast hy n)
/-
**Order.IsSuccLimit.add_natCast_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`
。
形式化陈述：∀ {α : Type u_1} {x y : α} [inst : PartialOrder α] [inst_1 : AddMonoidWith
One α] [SuccAddOrder α],   Order.IsSuccLimit x → y < x → ∀ (n : ℕ), y + ↑n < x
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.add_natCast_lt`：∀ {α : Type u_1} {x y : α} [inst : 
PartialOrder α] [inst_1 : AddMonoidWithOne α] [SuccAddOrder α],   Order.IsSuccPr
elimit x → y < x → ∀ (n :…
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem IsSuccLimit.add_natCast_lt [AddMonoidWithOne α] [SuccAddOrder α]
    (hx : IsSuccLimit x) (hy : y < x) : ∀ n : ℕ, y + n < x :=
  hx.isSuccPrelimit.add_natCast_lt hy
/-
**Order.IsPredLimit.lt_sub_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsPredLimit`
。
形式化陈述：∀ {α : Type u_1} {x y : α} [inst : PartialOrder α] [inst_1 : AddCommGroupW
ithOne α] [PredSubOrder α],   Order.IsPredLimit x → x < y → ∀ (n : ℕ), x < y - ↑
n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsPredPrelimit.lt_sub_natCast`：∀ {α : Type u_1} {x y : α} [inst : 
PartialOrder α] [inst_1 : AddCommGroupWithOne α] [PredSubOrder α],   Order.IsPre
dPrelimit x → x < y → ∀ (…
· 使用定理 `Order.IsPredLimit.isPredPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsPredLimit a → Order.IsPredPrelimit a
-/
theorem IsPredLimit.lt_sub_natCast [AddCommGroupWithOne α] [PredSubOrder α]
    (hx : IsPredLimit x) (hy : x < y) : ∀ n : ℕ, x < y - n :=
  hx.isPredPrelimit.lt_sub_natCast hy
/-
**Order.IsSuccLimit.natCast_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsSuccLimit`。
形式化陈述：∀ {α : Type u_1} {x : α} [inst : PartialOrder α] [inst_1 : AddMonoidWithOn
e α] [SuccAddOrder α] [IsBotZeroClass α],   Order.IsSuccLimit x → ∀ (n : ℕ), ↑n 
< x
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Order.IsSuccLimit.add_natCast_lt`：∀ {α : Type u_1} {x y : α} [inst : Par
tialOrder α] [inst_1 : AddMonoidWithOne α] [SuccAddOrder α],   Order.IsSuccLimit
 x → y < x → ∀ (n : ℕ)…
· 使用定理 `Order.IsSuccLimit.pos`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [ins
t_1 : Zero α] [IsBotZeroClass α], Order.IsSuccLimit a → 0 < a
-/
theorem IsSuccLimit.natCast_lt [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α]
    (hx : IsSuccLimit x) : ∀ n : ℕ, n < x := by
  simpa using hx.add_natCast_lt hx.pos
/-
**Order.not_isSuccLimit_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccLimit_natCast [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroCl
ass α] (n : Nat) : ¬ IsSuccLimit (n : α)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Order.IsSuccLimit.natCast_lt`：∀ {α : Type u_1} {x : α} [inst : PartialOr
der α] [inst_1 : AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α],   Orde
r.IsSuccLimit x → …
-/
theorem not_isSuccLimit_natCast [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α] (n : ℕ) :
    ¬ IsSuccLimit (n : α) :=
  fun h ↦ (h.natCast_lt n).false

@[simp]
/-
**Order.not_isSuccPrelimit_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccPrelimit_add_one (a : α) [Add α] [One α] [SuccAddOrder α] [NoMax
Order α] : ¬ IsSuccPrelimit (a + 1)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.not_isSuccPrelimit_succ`：not_isSuccPrelimit_succ (a : α) : ¬IsSucc
Prelimit (succ a)
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
-/
theorem not_isSuccPrelimit_add_one (a : α) [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    ¬ IsSuccPrelimit (a + 1) :=
  succ_eq_add_one a ▸ not_isSuccPrelimit_succ a

@[simp]
/-
**Order.not_isSuccLimit_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：not_isSuccLimit_add_one (a : α) [Add α] [One α] [SuccAddOrder α] [NoMaxOrd
er α] : ¬ IsSuccLimit (a + 1)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.not_isSuccLimit_succ`：not_isSuccLimit_succ (a : α) : ¬IsSuccLimit 
(succ a)
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
-/
theorem not_isSuccLimit_add_one (a : α) [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] :
    ¬ IsSuccLimit (a + 1) :=
  succ_eq_add_one a ▸ not_isSuccLimit_succ a

@[simp]
/-
**Order.succ_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：succ_eq_zero [AddZeroClass α] [OrderBot α] [IsBotZeroClass α] [One α] [NoM
axOrder α] [SuccAddOrder α] {a : WithBot α} : WithBot.succ a = 0 ↔ a = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Order.max_of_succ_le`：max_of_succ_le {a : α} : succ a <= a -> IsMax a
-/
theorem succ_eq_zero [AddZeroClass α] [OrderBot α] [IsBotZeroClass α] [One α] [NoMaxOrder α]
    [SuccAddOrder α] {a : WithBot α} : WithBot.succ a = 0 ↔ a = ⊥ := by
  cases a
  · simp [bot_eq_zero]
  · rename_i a
    simp only [WithBot.succ_coe, WithBot.coe_ne_bot, iff_false, succ_eq_add_one]
    by_contra h
    simpa [h] using max_of_succ_le (a := a)

end PartialOrder

section LinearOrder

variable [LinearOrder α]

section Add

variable [Add α] [One α] [SuccAddOrder α]

/-
**Order.le_of_lt_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_of_lt_add_one (h : x < y + 1) : x <= y
参数：h : x < y + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_of_lt_succ`：le_of_lt_succ {a b : α} : a < succ b -> a <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
-/
theorem le_of_lt_add_one (h : x < y + 1) : x ≤ y := by
  rw [← succ_eq_add_one] at h
  exact le_of_lt_succ h
/-
**Order.lt_add_one_iff_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_add_one_iff_of_not_isMax (hy : ¬ IsMax y) : x < y + 1 ↔ x <= y
参数：hy : ¬ IsMax y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_add_one_iff_of_not_isMax (hy : ¬ IsMax y) : x < y + 1 ↔ x ≤ y := by
  rw [← succ_eq_add_one, lt_succ_iff_of_not_isMax hy]
/-
**Order.lt_add_one_iff_of_not_isMax'** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_add_one_iff_of_not_isMax' (hx : ¬ IsMax x) : x < y + 1 ↔ x <= y
参数：hx : ¬ IsMax x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Order.lt_succ_iff_of_not_isMax'`：lt_succ_iff_of_not_isMax' (hb : ¬IsMax 
b) : b < succ a ↔ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_add_one_iff_of_not_isMax' (hx : ¬ IsMax x) : x < y + 1 ↔ x ≤ y := by
  rw [← succ_eq_add_one, lt_succ_iff_of_not_isMax' hx]

@[simp]
/-
**Order.lt_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.lt_add_one_iff_of_not_isMax`：lt_add_one_iff_of_not_isMax (hy : ¬ I
sMax y) : x < y + 1 ↔ x <= y
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x ≤ y :=
  lt_add_one_iff_of_not_isMax (not_isMax y)

@[simp]
/-
**Order.add_one_inj** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：add_one_inj [NoMaxOrder α] : x + 1 = y + 1 ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_one_inj [NoMaxOrder α] : x + 1 = y + 1 ↔ x = y := by
  simp [← succ_eq_add_one]

end Add

@[simp]
/-
**Order.lt_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_two_iff [AddMonoidWithOne α] [SuccAddOrder α] [NoMaxOrder α] : x < 2 ↔ 
x <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Order.lt_add_one_iff`：lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x <= y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_two_iff [AddMonoidWithOne α] [SuccAddOrder α] [NoMaxOrder α] : x < 2 ↔ x ≤ 1 := by
  rw [← one_add_one_eq_two, lt_add_one_iff]

section AddMonoidWithOne
variable [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α] [NeZero (1 : α)]

@[simp]
/-
**Order.lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_one_iff : x < 1 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
-/
theorem lt_one_iff : x < 1 ↔ x = 0 := by
  simpa using (one_le_iff_ne_zero (x := x)).not
/-
**Order.le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_one_iff : x ≤ 1 ↔ x = 0 ∨ x = 1 := by
  rw [le_iff_lt_or_eq, lt_one_iff]

@[simp]
/-
**Order.Iio_one** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Iio_one : Set.Iio (1 : α) = {0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iio_one : Set.Iio (1 : α) = {0} := by
  ext; simp
/-
**Order.Iic_one** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Iic_one : Set.Iic (1 : α) = {0, 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iic_one : Set.Iic (1 : α) = {0, 1} := by
  ext; simp [le_one_iff]

variable [NoMaxOrder α]
/-
**Order.le_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_two_iff : x <= 2 ↔ x = 0 ∨ x = 1 ∨ x = 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `Order.lt_two_iff`：lt_two_iff [AddMonoidWithOne α] [SuccAddOrder α] [NoMa
xOrder α] : x < 2 ↔ x <= 1
· 使用定理 `Order.le_one_iff`：le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_two_iff : x ≤ 2 ↔ x = 0 ∨ x = 1 ∨ x = 2 := by
  rw [le_iff_lt_or_eq, lt_two_iff, le_one_iff, or_assoc]
/-
**Order.Iio_two** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Iio_two : Set.Iio (2 : α) = {0, 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iio_two : Set.Iio (2 : α) = {0, 1} := by
  ext; simp [le_one_iff]
/-
**Order.Iic_two** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：Iic_two : Set.Iic (2 : α) = {0, 1, 2}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iic_two : Set.Iic (2 : α) = {0, 1, 2} := by
  ext; simp [le_two_iff]

end AddMonoidWithOne

section Sub

variable [Sub α] [One α] [PredSubOrder α]

/-
**Order.le_of_sub_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：le_of_sub_one_lt (h : x - 1 < y) : x <= y
参数：h : x - 1 < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_of_pred_lt`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : P
redOrder α] {a b : α}, Order.pred b < a → b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
-/
theorem le_of_sub_one_lt (h : x - 1 < y) : x ≤ y := by
  rw [← pred_eq_sub_one] at h
  exact le_of_pred_lt h
/-
**Order.sub_one_lt_iff_of_not_isMin** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：sub_one_lt_iff_of_not_isMin (hx : ¬ IsMin x) : x - 1 < y ↔ x <= y
参数：hx : ¬ IsMin x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用定理 `Order.pred_lt_iff_of_not_isMin`：∀ {α : Type u_1} [inst : LinearOrder α] 
[inst_1 : PredOrder α] {a b : α}, ¬IsMin a → (Order.pred a < b ↔ a ≤ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_one_lt_iff_of_not_isMin (hx : ¬ IsMin x) : x - 1 < y ↔ x ≤ y := by
  rw [← pred_eq_sub_one, pred_lt_iff_of_not_isMin hx]

@[simp]
/-
**Order.sub_one_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：sub_one_lt_iff [NoMinOrder α] : x - 1 < y ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.sub_one_lt_iff_of_not_isMin`：sub_one_lt_iff_of_not_isMin (hx : ¬ I
sMin x) : x - 1 < y ↔ x <= y
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
theorem sub_one_lt_iff [NoMinOrder α] : x - 1 < y ↔ x ≤ y :=
  sub_one_lt_iff_of_not_isMin (not_isMin x)

end Sub

/-
**Order.lt_one_iff_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：lt_one_iff_nonpos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
 [SuccAddOrder α] : x < 1 ↔ x <= 0
参数：1 : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.lt_succ_iff_of_not_isMax`：lt_succ_iff_of_not_isMax (ha : ¬IsMax a)
 : b < succ a ↔ b <= a
· 使用定理 `Order.not_isMax_zero`：not_isMax_zero [Zero α] [One α] [ZeroLEOneClass α]
 [NeZero (1 : α)] : ¬ IsMax (0 : α)
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_one_iff_nonpos [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] : x < 1 ↔ x ≤ 0 := by
  rw [← lt_succ_iff_of_not_isMax not_isMax_zero, succ_eq_add_one, zero_add]

end LinearOrder

end Order

section Monotone
variable {α β : Type*} [PartialOrder α] [Preorder β]

section SuccAddOrder
variable [Add α] [One α] [SuccAddOrder α] [IsSuccArchimedean α] {s : Set α} {f : α → β}

/-
**monotoneOn_of_le_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotoneOn_of_le_add_one (hs : s.OrdConnected) : (forall a, ¬ IsMax a -> a
 in s -> a + 1 in s -> f a <= f (a + 1)) -> MonotoneOn f s
参数：hs : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `monotoneOn_of_le_succ`：monotoneOn_of_le_succ (hs : s.OrdConnected) (hf :
 forall a, ¬ IsMax a -> a in s -> succ a in s -> f a <= f (succ a)) : MonotoneOn
 f s
-/
lemma monotoneOn_of_le_add_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMax a → a ∈ s → a + 1 ∈ s → f a ≤ f (a + 1)) → MonotoneOn f s := by
  simpa [Order.succ_eq_add_one] using monotoneOn_of_le_succ hs (f := f)
/-
**antitoneOn_of_add_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitoneOn_of_add_one_le (hs : s.OrdConnected) : (forall a, ¬ IsMax a -> a
 in s -> a + 1 in s -> f (a + 1) <= f a) -> AntitoneOn f s
参数：hs : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `antitoneOn_of_succ_le`：antitoneOn_of_succ_le (hs : s.OrdConnected) (hf :
 forall a, ¬ IsMax a -> a in s -> succ a in s -> f (succ a) <= f a) : AntitoneOn
 f s
-/
lemma antitoneOn_of_add_one_le (hs : s.OrdConnected) :
    (∀ a, ¬ IsMax a → a ∈ s → a + 1 ∈ s → f (a + 1) ≤ f a) → AntitoneOn f s := by
  simpa [Order.succ_eq_add_one] using antitoneOn_of_succ_le hs (f := f)
/-
**strictMonoOn_of_lt_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMonoOn_of_lt_add_one (hs : s.OrdConnected) : (forall a, ¬ IsMax a ->
 a in s -> a + 1 in s -> f a < f (a + 1)) -> StrictMonoOn f s
参数：hs : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `strictMonoOn_of_lt_succ`：strictMonoOn_of_lt_succ (hs : s.OrdConnected) (
hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f a < f (succ a)) : StrictM
onoOn f s
-/
lemma strictMonoOn_of_lt_add_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMax a → a ∈ s → a + 1 ∈ s → f a < f (a + 1)) → StrictMonoOn f s := by
  simpa [Order.succ_eq_add_one] using strictMonoOn_of_lt_succ hs (f := f)
/-
**strictAntiOn_of_add_one_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAntiOn_of_add_one_lt (hs : s.OrdConnected) : (forall a, ¬ IsMax a ->
 a in s -> a + 1 in s -> f (a + 1) < f a) -> StrictAntiOn f s
参数：hs : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `strictAntiOn_of_succ_lt`：strictAntiOn_of_succ_lt (hs : s.OrdConnected) (
hf : forall a, ¬ IsMax a -> a in s -> succ a in s -> f (succ a) < f a) : StrictA
ntiOn f s
-/
lemma strictAntiOn_of_add_one_lt (hs : s.OrdConnected) :
    (∀ a, ¬ IsMax a → a ∈ s → a + 1 ∈ s → f (a + 1) < f a) → StrictAntiOn f s := by
  simpa [Order.succ_eq_add_one] using strictAntiOn_of_succ_lt hs (f := f)
/-
**monotone_of_le_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_of_le_add_one : (forall a, ¬ IsMax a -> f a <= f (a + 1)) -> Mono
tone f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `monotone_of_le_succ`：monotone_of_le_succ (hf : forall a, ¬ IsMax a -> f 
a <= f (succ a)) : Monotone f
-/
lemma monotone_of_le_add_one : (∀ a, ¬ IsMax a → f a ≤ f (a + 1)) → Monotone f := by
  simpa [Order.succ_eq_add_one] using monotone_of_le_succ (f := f)
/-
**antitone_of_add_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitone_of_add_one_le : (forall a, ¬ IsMax a -> f (a + 1) <= f a) -> Anti
tone f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `antitone_of_succ_le`：antitone_of_succ_le (hf : forall a, ¬ IsMax a -> f 
(succ a) <= f a) : Antitone f
-/
lemma antitone_of_add_one_le : (∀ a, ¬ IsMax a → f (a + 1) ≤ f a) → Antitone f := by
  simpa [Order.succ_eq_add_one] using antitone_of_succ_le (f := f)
/-
**strictMono_of_lt_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMono_of_lt_add_one : (forall a, ¬ IsMax a -> f a < f (a + 1)) -> Str
ictMono f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `strictMono_of_lt_succ`：strictMono_of_lt_succ (hf : forall a, ¬ IsMax a -
> f a < f (succ a)) : StrictMono f
-/
lemma strictMono_of_lt_add_one : (∀ a, ¬ IsMax a → f a < f (a + 1)) → StrictMono f := by
  simpa [Order.succ_eq_add_one] using strictMono_of_lt_succ (f := f)
/-
**strictAnti_of_add_one_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAnti_of_add_one_lt : (forall a, ¬ IsMax a -> f (a + 1) < f a) -> Str
ictAnti f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用引理 `strictAnti_of_succ_lt`：strictAnti_of_succ_lt (hf : forall a, ¬ IsMax a -
> f (succ a) < f a) : StrictAnti f
-/
lemma strictAnti_of_add_one_lt : (∀ a, ¬ IsMax a → f (a + 1) < f a) → StrictAnti f := by
  simpa [Order.succ_eq_add_one] using strictAnti_of_succ_lt (f := f)

end SuccAddOrder

section PredSubOrder
variable [Sub α] [One α] [PredSubOrder α] [IsPredArchimedean α] {s : Set α} {f : α → β}

/-
**monotoneOn_of_sub_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotoneOn_of_sub_one_le (hs : s.OrdConnected) : (forall a, ¬ IsMin a -> a
 in s -> a - 1 in s -> f (a - 1) <= f a) -> MonotoneOn f s
参数：hs : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `monotoneOn_of_pred_le`：monotoneOn_of_pred_le (hs : s.OrdConnected) (hf :
 forall a, ¬ IsMin a -> a in s -> pred a in s -> f (pred a) <= f a) : MonotoneOn
 f s
-/
lemma monotoneOn_of_sub_one_le (hs : s.OrdConnected) :
    (∀ a, ¬ IsMin a → a ∈ s → a - 1 ∈ s → f (a - 1) ≤ f a) → MonotoneOn f s := by
  simpa [Order.pred_eq_sub_one] using monotoneOn_of_pred_le hs (f := f)
/-
**antitoneOn_of_le_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitoneOn_of_le_sub_one (hs : s.OrdConnected) : (forall a, ¬ IsMin a -> a
 in s -> a - 1 in s -> f a <= f (a - 1)) -> AntitoneOn f s
参数：hs : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `antitoneOn_of_le_pred`：antitoneOn_of_le_pred (hs : s.OrdConnected) (hf :
 forall a, ¬ IsMin a -> a in s -> pred a in s -> f a <= f (pred a)) : AntitoneOn
 f s
-/
lemma antitoneOn_of_le_sub_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMin a → a ∈ s → a - 1 ∈ s → f a ≤ f (a - 1)) → AntitoneOn f s := by
  simpa [Order.pred_eq_sub_one] using antitoneOn_of_le_pred hs (f := f)
/-
**strictMonoOn_of_sub_one_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMonoOn_of_sub_one_lt (hs : s.OrdConnected) : (forall a, ¬ IsMin a ->
 a in s -> a - 1 in s -> f (a - 1) < f a) -> StrictMonoOn f s
参数：hs : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `strictMonoOn_of_pred_lt`：strictMonoOn_of_pred_lt (hs : s.OrdConnected) (
hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f (pred a) < f a) : StrictM
onoOn f s
-/
lemma strictMonoOn_of_sub_one_lt (hs : s.OrdConnected) :
    (∀ a, ¬ IsMin a → a ∈ s → a - 1 ∈ s → f (a - 1) < f a) → StrictMonoOn f s := by
  simpa [Order.pred_eq_sub_one] using strictMonoOn_of_pred_lt hs (f := f)
/-
**strictAntiOn_of_lt_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAntiOn_of_lt_sub_one (hs : s.OrdConnected) : (forall a, ¬ IsMin a ->
 a in s -> a - 1 in s -> f a < f (a - 1)) -> StrictAntiOn f s
参数：hs : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `strictAntiOn_of_lt_pred`：strictAntiOn_of_lt_pred (hs : s.OrdConnected) (
hf : forall a, ¬ IsMin a -> a in s -> pred a in s -> f a < f (pred a)) : StrictA
ntiOn f s
-/
lemma strictAntiOn_of_lt_sub_one (hs : s.OrdConnected) :
    (∀ a, ¬ IsMin a → a ∈ s → a - 1 ∈ s → f a < f (a - 1)) → StrictAntiOn f s := by
  simpa [Order.pred_eq_sub_one] using strictAntiOn_of_lt_pred hs (f := f)
/-
**monotone_of_sub_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_of_sub_one_le : (forall a, ¬ IsMin a -> f (a - 1) <= f a) -> Mono
tone f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `monotone_of_pred_le`：monotone_of_pred_le (hf : forall a, ¬ IsMin a -> f 
(pred a) <= f a) : Monotone f
-/
lemma monotone_of_sub_one_le : (∀ a, ¬ IsMin a → f (a - 1) ≤ f a) → Monotone f := by
  simpa [Order.pred_eq_sub_one] using monotone_of_pred_le (f := f)
/-
**antitone_of_le_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitone_of_le_sub_one : (forall a, ¬ IsMin a -> f a <= f (a - 1)) -> Anti
tone f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `antitone_of_le_pred`：antitone_of_le_pred (hf : forall a, ¬ IsMin a -> f 
a <= f (pred a)) : Antitone f
-/
lemma antitone_of_le_sub_one : (∀ a, ¬ IsMin a → f a ≤ f (a - 1)) → Antitone f := by
  simpa [Order.pred_eq_sub_one] using antitone_of_le_pred (f := f)
/-
**strictMono_of_sub_one_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMono_of_sub_one_lt : (forall a, ¬ IsMin a -> f (a - 1) < f a) -> Str
ictMono f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `strictMono_of_pred_lt`：strictMono_of_pred_lt (hf : forall a, ¬ IsMin a -
> f (pred a) < f a) : StrictMono f
-/
lemma strictMono_of_sub_one_lt : (∀ a, ¬ IsMin a → f (a - 1) < f a) → StrictMono f := by
  simpa [Order.pred_eq_sub_one] using strictMono_of_pred_lt (f := f)
/-
**strictAnti_of_lt_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAnti_of_lt_sub_one : (forall a, ¬ IsMin a -> f a < f (a - 1)) -> Str
ictAnti f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_eq_sub_one`：pred_eq_sub_one (x : α) : pred x = x - 1
· 使用引理 `strictAnti_of_lt_pred`：strictAnti_of_lt_pred (hf : forall a, ¬ IsMin a -
> f a < f (pred a)) : StrictAnti f
-/
lemma strictAnti_of_lt_sub_one : (∀ a, ¬ IsMin a → f a < f (a - 1)) → StrictAnti f := by
  simpa [Order.pred_eq_sub_one] using strictAnti_of_lt_pred (f := f)

end PredSubOrder
end Monotone

