/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic.Common

/-!
# Square root of integers

This file defines the square root function on integers. `Int.sqrt z` is the greatest integer `r`
such that `r * r ≤ z`. If `z ≤ 0`, then `Int.sqrt z = 0`.
-/

@[expose] public section


namespace Int

/-- `sqrt z` is the square root of an integer `z`. If `z` is positive, it returns the largest
integer `r` such that `r * r ≤ n`. If it is negative, it returns `0`. For example, `sqrt (-1) = 0`,
`sqrt 1 = 1`, `sqrt 2 = 1` -/
@[pp_nodot]
/-
**Int.sqrt** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：sqrt (z : Int) : Int
参数：z : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sqrt z` is the square root of an integer `z`. If `z` is positive, it returns th
e largest
integer `r` such that `r * r ≤ n`. If it is negative, it returns `0`. For exampl
e, `sqrt (-1) = 0`,
`sqrt 1 = 1`, `sqrt 2 = 1`
-/
def sqrt (z : ℤ) : ℤ :=
  Nat.sqrt <| Int.toNat z
/-
**Int.sqrt_eq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sqrt_eq (n : Int) : sqrt (n * n) = n.natAbs
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.sqrt.eq_1`：∀ (z : ℤ), Int.sqrt z = ↑z.toNat.sqrt
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natAbs_mul_self`：∀ {a : ℤ}, ↑(a.natAbs * a.natAbs) = a * a
· 使用定理 `Int.toNat_natCast`：∀ (n : ℕ), (↑n).toNat = n
· 使用引理 `Nat.sqrt_eq`：sqrt_eq (n : Nat) : sqrt (n * n) = n
-/
theorem sqrt_eq (n : ℤ) : sqrt (n * n) = n.natAbs := by
  rw [sqrt, ← natAbs_mul_self, toNat_natCast, Nat.sqrt_eq]
/-
**Int.exists_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：exists_mul_self (x : Int) : (exists n, n * n = x) ↔ sqrt x * sqrt x = x
参数：x : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.sqrt_eq`：sqrt_eq (n : Int) : sqrt (n * n) = n.natAbs
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `Int.natAbs_mul_self`：∀ {a : ℤ}, ↑(a.natAbs * a.natAbs) = a * a
-/
theorem exists_mul_self (x : ℤ) : (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, ← Int.natCast_mul, natAbs_mul_self], fun h => ⟨sqrt x, h⟩⟩
/-
**Int.sqrt_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sqrt_nonneg (n : Int) : 0 <= sqrt n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
-/
theorem sqrt_nonneg (n : ℤ) : 0 ≤ sqrt n :=
  natCast_nonneg _

@[simp, norm_cast]
/-
**Int.sqrt_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sqrt_natCast (n : Nat) : Int.sqrt (n : Int) = Nat.sqrt n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.sqrt.eq_1`：∀ (z : ℤ), Int.sqrt z = ↑z.toNat.sqrt
· 使用定理 `Int.toNat_natCast`：∀ (n : ℕ), (↑n).toNat = n
-/
theorem sqrt_natCast (n : ℕ) : Int.sqrt (n : ℤ) = Nat.sqrt n := by rw [sqrt, toNat_natCast]

@[simp]
/-
**Int.sqrt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：sqrt_ofNat (n : Nat) : Int.sqrt ofNat(n) = Nat.sqrt ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.sqrt_natCast`：sqrt_natCast (n : Nat) : Int.sqrt (n : Int) = Nat.sqrt
 n
-/
theorem sqrt_ofNat (n : ℕ) : Int.sqrt ofNat(n) = Nat.sqrt ofNat(n) :=
  sqrt_natCast _

end Int

