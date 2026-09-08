/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jeremy Avigad
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Ring.Canonical

/-!
# Distance function on ℕ

This file defines a simple distance function on naturals from truncated subtraction.
-/

@[expose] public section


namespace Nat

/-- Distance (absolute value of difference) between natural numbers. -/
/-
**Nat.dist** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：dist (n m : Nat)
参数：n m : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Distance (absolute value of difference) between natural numbers.
-/
def dist (n m : ℕ) :=
  n - m + (m - n)
/-
**Nat.dist_comm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_comm (n m : Nat) : dist n m = dist m n
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_comm (n m : ℕ) : dist n m = dist m n := by simp [dist, add_comm]

@[simp]
/-
**Nat.dist_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_self (n : Nat) : dist n n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_self (n : ℕ) : dist n n = 0 := by simp [dist, tsub_self]
/-
**Nat.eq_of_dist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_of_dist_eq_zero {n m : Nat} (h : dist n m = 0) : n = m
参数：h : dist n m = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_of_dist_eq_zero {n m : ℕ} (h : dist n m = 0) : n = m := by unfold Nat.dist at h; lia
/-
**Nat.dist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_eq_zero {n m : Nat} (h : n = m) : dist n m = 0
参数：h : n = m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq_zero {n m : ℕ} (h : n = m) : dist n m = 0 := by unfold Nat.dist; lia
/-
**Nat.dist_eq_sub_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_eq_sub_of_le {n m : Nat} (h : n <= m) : dist n m = m - n
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq_sub_of_le {n m : ℕ} (h : n ≤ m) : dist n m = m - n := by unfold Nat.dist; lia
/-
**Nat.dist_eq_sub_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_eq_sub_of_le_right {n m : Nat} (h : m <= n) : dist n m = n - m
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq_sub_of_le_right {n m : ℕ} (h : m ≤ n) : dist n m = n - m := by
  unfold Nat.dist; lia
/-
**Nat.dist_tri_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_tri_left (n m : Nat) : m <= dist n m + n
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_tri_left (n m : ℕ) : m ≤ dist n m + n := by unfold Nat.dist; lia
/-
**Nat.dist_tri_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_tri_right (n m : Nat) : m <= n + dist n m
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_tri_right (n m : ℕ) : m ≤ n + dist n m := by unfold Nat.dist; lia
/-
**Nat.dist_tri_left'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_tri_left' (n m : Nat) : n <= dist n m + m
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_tri_left' (n m : ℕ) : n ≤ dist n m + m := by unfold Nat.dist; lia
/-
**Nat.dist_tri_right'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_tri_right' (n m : Nat) : n <= m + dist n m
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_tri_right' (n m : ℕ) : n ≤ m + dist n m := by unfold Nat.dist; lia
/-
**Nat.dist_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_zero_right (n : Nat) : dist n 0 = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_zero_right (n : ℕ) : dist n 0 = n := by unfold Nat.dist; lia
/-
**Nat.dist_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_zero_left (n : Nat) : dist 0 n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_zero_left (n : ℕ) : dist 0 n = n := by unfold Nat.dist; lia
/-
**Nat.dist_add_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_add_add_right (n k m : Nat) : dist (n + k) (m + k) = dist n m
参数：n k m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_add_add_right (n k m : ℕ) : dist (n + k) (m + k) = dist n m := by
  unfold Nat.dist; lia
/-
**Nat.dist_add_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_add_add_left (k n m : Nat) : dist (k + n) (k + m) = dist n m
参数：k n m : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_add_add_left (k n m : ℕ) : dist (k + n) (k + m) = dist n m := by
  unfold Nat.dist; lia
/-
**Nat.dist_eq_intro** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_eq_intro {n m k l : Nat} (h : n + m = k + l) : dist n k = dist l m
参数：h : n + m = k + l。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq_intro {n m k l : ℕ} (h : n + m = k + l) : dist n k = dist l m := by
  unfold Nat.dist; lia
/-
**Nat.dist.triangle_inequality** 是 Mathlib 中的一个定理，位于命名空间 `Nat.dist`。
形式化陈述：∀ (n m k : ℕ), n.dist k ≤ n.dist m + m.dist k
参数：n m k : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist.triangle_inequality (n m k : ℕ) : dist n k ≤ dist n m + dist m k := by
  unfold Nat.dist; lia
/-
**Nat.dist_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_mul_right (n k m : Nat) : dist (n * k) (m * k) = dist n m * k
参数：n k m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.dist.eq_1`：∀ (n m : ℕ), n.dist m = n - m + (m - n)
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `tsub_mul`：tsub_mul [MulRightMono R] (a b c : R) : (a - b) * c = a * c - 
b * c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem dist_mul_right (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist, dist, right_distrib, tsub_mul n, tsub_mul m]
/-
**Nat.dist_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_mul_left (k n m : Nat) : dist (k * n) (k * m) = k * dist n m
参数：k n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.dist_mul_right`：dist_mul_right (n k m : Nat) : dist (n * k) (m * k) 
= dist n m * k
-/
theorem dist_mul_left (k n m : ℕ) : dist (k * n) (k * m) = k * dist n m := by
  rw [mul_comm k n, mul_comm k m, dist_mul_right, mul_comm]
/-
**Nat.dist_eq_max_sub_min** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_eq_max_sub_min {i j : Nat} : dist i j = (max i j) - min i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
theorem dist_eq_max_sub_min {i j : ℕ} : dist i j = (max i j) - min i j := by
  cases le_total i j <;> simp [Nat.dist, *]
/-
**Nat.dist_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_succ_succ {i j : Nat} : dist (succ i) (succ j) = dist i j
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_succ_succ {i j : Nat} : dist (succ i) (succ j) = dist i j := by unfold Nat.dist; lia
/-
**Nat.dist_pos_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_pos_of_ne {i j : Nat} (h : i != j) : 0 < dist i j
参数：h : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_pos_of_ne {i j : Nat} (h : i ≠ j) : 0 < dist i j := by unfold Nat.dist; lia

end Nat

