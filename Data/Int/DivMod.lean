/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Batteries.Tactic.Alias
public import Mathlib.Init

/-!
# Basic lemmas about division and modulo for integers

-/

public section

namespace Int

/-! ### `ediv` and `fdiv` -/

/-
**Int.mul_ediv_le_mul_ediv_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：mul_ediv_le_mul_ediv_assoc {a : Int} (ha : 0 <= a) (b : Int) {c : Int} (hc
 : 0 <= c) : a * (b / c) <= a * b / c
参数：ha : 0 <= a；b : Int；hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ediv_zero`：∀ (a : ℤ), a / 0 = 0
· 使用定理 `Int.mul_zero`：∀ (a : ℤ), a * 0 = 0
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Std.IsLinearPreorder.toIsPreorder`：∀ {α : Type u} {inst : LE α} [self : 
Std.IsLinearPreorder α], Std.IsPreorder α
· 使用定理 `Std.IsLinearOrder.toIsLinearPreorder`：∀ {α : Type u} [inst : LE α] [self
 : Std.IsLinearOrder α], Std.IsLinearPreorder α
· 使用定理 `Lean.Grind.instIsLinearOrderInt`：Std.IsLinearOrder ℤ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.le_ediv_iff_mul_le`：∀ {a b c : ℤ}, 0 < c → (a ≤ b / c ↔ a * c ≤ b)
· 使用定理 `Int.mul_assoc`：∀ (a b c : ℤ), a * b * c = a * (b * c)
· 使用定理 `Int.mul_le_mul_of_nonneg_left`：∀ {a b c : ℤ}, a ≤ b → 0 ≤ c → c * a ≤ c 
* b
· 使用定理 `Int.ediv_mul_le`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → a / b * b ≤ a
· 使用定理 `Int.ne_of_gt`：∀ {a b : ℤ}, b < a → a ≠ b

--- 原说明 ---
### `ediv` and `fdiv`
-/
theorem mul_ediv_le_mul_ediv_assoc {a : Int} (ha : 0 ≤ a) (b : Int) {c : Int} (hc : 0 ≤ c) :
    a * (b / c) ≤ a * b / c := by
  obtain rfl | hlt : c = 0 ∨ 0 < c := by lia
  · simp
  · rw [Int.le_ediv_iff_mul_le hlt, Int.mul_assoc]
    exact Int.mul_le_mul_of_nonneg_left (Int.ediv_mul_le b (Int.ne_of_gt hlt)) ha
/-
**Int.fdiv_fdiv_eq_fdiv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：fdiv_fdiv_eq_fdiv_mul (m : Int) {n k : Int} (hn : 0 <= n) (hk : 0 <= k) : 
(m.fdiv n).fdiv k = m.fdiv (n * k)
参数：m : Int；hn : 0 <= n；hk : 0 <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.fdiv_eq_ediv_of_nonneg`：∀ (a : ℤ) {b : ℤ}, 0 ≤ b → a.fdiv b = a / b
· 使用定理 `Int.mul_nonneg`：∀ {a b : ℤ}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `Int.ediv_ediv_of_nonneg`：∀ {x y z : ℤ}, 0 ≤ y → x / y / z = x / (y * z)
-/
theorem fdiv_fdiv_eq_fdiv_mul (m : Int) {n k : Int} (hn : 0 ≤ n) (hk : 0 ≤ k) :
    (m.fdiv n).fdiv k = m.fdiv (n * k) := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ hn,
    Int.fdiv_eq_ediv_of_nonneg _ hk,
    Int.fdiv_eq_ediv_of_nonneg _ (Int.mul_nonneg hn hk),
    ediv_ediv_of_nonneg hn]

/-! ### `emod` -/

/-
**Int.emod_eq_sub_self_emod** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：emod_eq_sub_self_emod {a b : Int} : a % b = (a - b) % b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.sub_emod_right`：∀ (a b : ℤ), (a - b) % b = a % b

--- 原说明 ---
### `emod`
-/
theorem emod_eq_sub_self_emod {a b : Int} : a % b = (a - b) % b :=
  (sub_emod_right a b).symm

end Int

