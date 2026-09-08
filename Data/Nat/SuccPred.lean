/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Nat
public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Order.SuccPred.WithBot

/-!
# Successors and predecessors of naturals

In this file, we show that `ℕ` is both an archimedean `succOrder` and an archimedean `predOrder`.
-/

public section


open Function Order

namespace Nat
variable {m n : ℕ}

/-
**Nat.instSuccOrder** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instSuccOrder : SuccOrder Nat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
-/
instance instSuccOrder : SuccOrder ℕ :=
  SuccOrder.ofSuccLeIff succ Nat.succ_le_iff
/-
**Nat.instSuccAddOrder** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instSuccAddOrder : SuccAddOrder Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSuccAddOrder : SuccAddOrder ℕ := ⟨fun _ => rfl⟩
/-
**Nat.instPredOrder** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instPredOrder : PredOrder Nat where pred
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
-/
instance instPredOrder : PredOrder ℕ where
  pred := pred
  pred_le := pred_le
  min_of_le_pred {a} ha := by
    cases a
    · exact isMin_bot
    · exact (not_succ_le_self _ ha).elim
  le_pred_of_lt {a} {b} h := by
    cases b
    · exact (a.not_lt_zero h).elim
    · exact le_of_succ_le_succ h
/-
**Nat.instPredSubOrder** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instPredSubOrder : PredSubOrder Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPredSubOrder : PredSubOrder ℕ := ⟨fun _ => rfl⟩

@[simp]
/-
**Nat.succ_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succ_eq_succ : Order.succ = succ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succ_eq_succ : Order.succ = succ :=
  rfl

@[simp]
/-
**Nat.pred_eq_pred** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pred_eq_pred : Order.pred = pred
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pred_eq_pred : Order.pred = pred :=
  rfl
/-
**Nat.succ_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a n : ℕ), Nat.succ^[n] a = a + n
参数：a n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.succ_iterate`：succ_iterate [AddMonoidWithOne α] [SuccAddOrder α] (
x : α) (n : Nat) : succ^[n] x = x + n
-/
protected theorem succ_iterate (a : ℕ) : ∀ n, succ^[n] a = a + n :=
  Order.succ_iterate a
/-
**Nat.pred_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a n : ℕ), Nat.pred^[n] a = a - n
参数：a n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem pred_iterate (a : ℕ) : ∀ n, pred^[n] a = a - n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ', sub_succ]
    exact congr_arg _ (Nat.pred_iterate a n)

/-- A special case of `Order.covBy_iff_add_one_eq` for use by simp. -/
/-
**Nat.covBy_iff_add_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, m ⋖ n ↔ m + 1 = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.covBy_iff_add_one_eq`：covBy_iff_add_one_eq [Add α] [One α] [SuccAd
dOrder α] [NoMaxOrder α] : x ⋖ y ↔ x + 1 = y

--- 原说明 ---
A special case of `Order.covBy_iff_add_one_eq` for use by simp.
-/
@[simp] lemma covBy_iff_add_one_eq : m ⋖ n ↔ m + 1 = n := Order.covBy_iff_add_one_eq
/-
**Nat.le_succ_iff_eq_or_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：le_succ_iff_eq_or_le : m <= n.succ ↔ m = n.succ ∨ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_succ_iff_eq_or_le`：le_succ_iff_eq_or_le : a <= succ b ↔ a = suc
c b ∨ a <= b

--- 原说明 ---
A special case of `Order.covBy_iff_add_one_eq` for use by simp.
-/
lemma le_succ_iff_eq_or_le : m ≤ n.succ ↔ m = n.succ ∨ m ≤ n := Order.le_succ_iff_eq_or_le
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSuccArchimedean ℕ :=
  ⟨fun {a} {b} h => ⟨b - a, by rw [succ_eq_succ, Nat.succ_iterate, add_tsub_cancel_of_le h]⟩⟩
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPredArchimedean ℕ :=
  ⟨fun {a} {b} h => ⟨b - a, by rw [pred_eq_pred, Nat.pred_iterate, tsub_tsub_cancel_of_le h]⟩⟩
/-
**Nat.forall_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：forall_ne_zero_iff (P : Nat -> Prop) : (forall i, i != 0 -> P i) ↔ (forall
 i, P (i + 1))
参数：P : Nat -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SuccOrder.forall_ne_bot_iff`：SuccOrder.forall_ne_bot_iff [Nontrivial α] 
[PartialOrder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α] (P : α -> Prop
) : (forall i, i …
· 使用定理 `Nat.instIsSuccArchimedean`：IsSuccArchimedean ℕ
-/
lemma forall_ne_zero_iff (P : ℕ → Prop) :
    (∀ i, i ≠ 0 → P i) ↔ (∀ i, P (i + 1)) :=
  SuccOrder.forall_ne_bot_iff P

end Nat

/-
**Fin.covBy_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {n : ℕ} {a b : Fin n}, a ⋖ b ↔ ↑a ⋖ ↑b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
@[simp] theorem Fin.covBy_iff {n : ℕ} {a b : Fin n} : a ⋖ b ↔ (a : ℕ) ⋖ b :=
  and_congr_right' ⟨fun h c ha hb ↦ @h ⟨c, hb.trans b.prop⟩ ha hb, fun h _c hc ↦ h hc⟩

@[deprecated Fin.covBy_iff "use Fin.covBy_iff.symm instead" (since := "2026-02-13")]
/-
**Fin.coe_covBy_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fin.coe_covBy_iff {n : Nat} {a b : Fin n} : (a : Nat) ⋖ b ↔ a ⋖ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Fin.covBy_iff`：∀ {n : ℕ} {a b : Fin n}, a ⋖ b ↔ ↑a ⋖ ↑b
-/
theorem Fin.coe_covBy_iff {n : ℕ} {a b : Fin n} : (a : ℕ) ⋖ b ↔ a ⋖ b := Fin.covBy_iff.symm

alias ⟨CovBy.coe_fin, _⟩ := Fin.covBy_iff

@[simp]
/-
**withBotSucc_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：withBotSucc_zero : WithBot.succ 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withBotSucc_zero : WithBot.succ 0 = 1 := rfl

@[simp]
/-
**withBotSucc_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：withBotSucc_one : WithBot.succ 1 = 2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem withBotSucc_one : WithBot.succ 1 = 2 := rfl
