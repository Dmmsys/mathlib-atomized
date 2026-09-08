/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.SuccPred.Basic

/-!
# `SuccOrder` and `PredOrder` of `Fin n`

In this file, we show that `Fin n` is both a `SuccOrder` and a `PredOrder`. Note that they are
also archimedean, but this is derived from the general instance for well-orderings as opposed
to a specific `Fin` instance.

-/

public section


namespace Fin

/-
**Fin.** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ∀ {n : ℕ}, SuccOrder (Fin n)
  | 0 => by constructor <;> intro a <;> exact elim0 a
  | n + 1 =>
    SuccOrder.ofCore (Fin.lastCases (Fin.last n) Fin.succ)
      (fun {i} hi j ↦ by
        obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (by simpa using! hi)
        simp [castSucc_lt_iff_succ_le])
      (fun i hi ↦ by
        obtain rfl : i = Fin.last n := by simpa using! hi
        simp)
/-
**Fin.orderSucc_eq** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：orderSucc_eq {n : Nat} : Order.succ = Fin.lastCases (Fin.last n) Fin.succ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orderSucc_eq {n : ℕ} :
    Order.succ = Fin.lastCases (Fin.last n) Fin.succ := rfl
/-
**Fin.orderSucc_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：orderSucc_apply {n : Nat} (i : Fin (n + 1)) : Order.succ i = Fin.lastCases
 (Fin.last n) Fin.succ i
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orderSucc_apply {n : ℕ} (i : Fin (n + 1)) :
    Order.succ i = Fin.lastCases (Fin.last n) Fin.succ i := rfl

@[simp]
/-
**Fin.orderSucc_last** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：orderSucc_last (n : Nat) : Order.succ (Fin.last n) = Fin.last n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.lastCases_last`：∀ {n : ℕ} {motive : Fin (n + 1) → Sort u_1} {last : 
motive (Fin.last n)} {cast : (i : Fin n) → motive i.castSucc},   Fin.lastCases l
ast cast…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma orderSucc_last (n : ℕ) :
    Order.succ (Fin.last n) = Fin.last n := by
  simp [orderSucc_apply]

@[simp]
/-
**Fin.orderSucc_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：orderSucc_castSucc {n : Nat} (i : Fin n) : Order.succ i.castSucc = i.succ
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.lastCases_castSucc`：∀ {n : ℕ} {motive : Fin (n + 1) → Sort u_1} {las
t : motive (Fin.last n)} {cast : (i : Fin n) → motive i.castSucc}   (i : Fin n),
 Fin.lastCas…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma orderSucc_castSucc {n : ℕ} (i : Fin n) :
    Order.succ i.castSucc = i.succ := by
  simp [orderSucc_apply]
/-
**Fin.** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ∀ {n : ℕ}, PredOrder (Fin n)
  | 0 => by constructor <;> first | intro a; exact elim0 a
  | n + 1 =>
    PredOrder.ofCore
      (Fin.cases 0 Fin.castSucc)
      (fun {i} hi j ↦ by
        obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (by simpa using! hi)
        simp [le_castSucc_iff])
      (fun i hi ↦ by
        obtain rfl : i = 0 := by simpa using! hi
        rfl)
/-
**Fin.orderPred_eq** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：orderPred_eq {n : Nat} : Order.pred = Fin.cases 0 Fin.castSucc (n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orderPred_eq {n : ℕ} :
    Order.pred = Fin.cases 0 Fin.castSucc (n := n) := rfl
/-
**Fin.orderPred_apply** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：orderPred_apply {n : Nat} (i : Fin (n + 1)) : Order.pred i = Fin.cases 0 F
in.castSucc i
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orderPred_apply {n : ℕ} (i : Fin (n + 1)) :
    Order.pred i = Fin.cases 0 Fin.castSucc i := rfl

@[simp]
/-
**Fin.orderPred_zero** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：orderPred_zero (n : Nat) : Order.pred (0 : Fin (n + 1)) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma orderPred_zero (n : ℕ) :
    Order.pred (0 : Fin (n + 1)) = 0 :=
  rfl

@[simp]
/-
**Fin.orderPred_succ** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：orderPred_succ {n : Nat} (i : Fin n) : Order.pred i.succ = i.castSucc
参数：i : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orderPred_succ {n : ℕ} (i : Fin n) :
    Order.pred i.succ = i.castSucc :=
  rfl

end Fin

