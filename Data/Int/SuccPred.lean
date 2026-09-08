/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Nat.SuccPred

/-!
# Successors and predecessors of integers

In this file, we show that `ℤ` is both an archimedean `SuccOrder` and an archimedean `PredOrder`.
-/

public section


open Function Order

namespace Int

/-
**Int.instSuccOrder** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instSuccOrder : SuccOrder Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSuccOrder : SuccOrder ℤ :=
  { SuccOrder.ofSuccLeIff succ fun {_ _} => Iff.rfl with succ := succ }
/-
**Int.instSuccAddOrder** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instSuccAddOrder : SuccAddOrder Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSuccAddOrder : SuccAddOrder ℤ := ⟨fun _ => rfl⟩
/-
**Int.instPredOrder** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instPredOrder : PredOrder Int where pred
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_sub_one_of_lt`：∀ {a b : ℤ}, a < b → a ≤ b - 1
-/
instance instPredOrder : PredOrder ℤ where
  pred := pred
  pred_le _ := (sub_one_lt_of_le le_rfl).le
  min_of_le_pred ha := ((sub_one_lt_of_le le_rfl).not_ge ha).elim
  le_pred_of_lt {_ _} := le_sub_one_of_lt
/-
**Int.instPredSubOrder** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instPredSubOrder : PredSubOrder Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPredSubOrder : PredSubOrder ℤ := ⟨fun _ => rfl⟩

@[simp]
/-
**Int.succ_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：succ_eq_succ : Order.succ = succ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succ_eq_succ : Order.succ = succ :=
  rfl

@[simp]
/-
**Int.pred_eq_pred** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：pred_eq_pred : Order.pred = pred
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pred_eq_pred : Order.pred = pred :=
  rfl
/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSuccArchimedean ℤ :=
  ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [succ_iterate, toNat_sub_of_le h, ← add_sub_assoc, add_sub_cancel_left]⟩⟩
/-
**Int.** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPredArchimedean ℤ :=
  ⟨fun {a b} h =>
    ⟨(b - a).toNat, by rw [pred_iterate, toNat_sub_of_le h, sub_sub_cancel]⟩⟩

/-! ### Covering relation -/


@[simp, norm_cast]
/-
**Int.natCast_covBy** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natCast_covBy {a b : Nat} : (a : Int) ⋖ b ↔ a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.covBy_iff_add_one_eq`：covBy_iff_add_one_eq [Add α] [One α] [SuccAd
dOrder α] [NoMaxOrder α] : x ⋖ y ↔ x + 1 = y
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n

--- 原说明 ---
### Covering relation
-/
theorem natCast_covBy {a b : ℕ} : (a : ℤ) ⋖ b ↔ a ⋖ b := by
  rw [Order.covBy_iff_add_one_eq, Order.covBy_iff_add_one_eq]
  exact Int.natCast_inj

end Int

alias ⟨_, CovBy.intCast⟩ := Int.natCast_covBy

