/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Data.Nat.Notation
public import Init.Data.Fin.Bitwise

/-!
# Basic operations on bounded natural numbers.

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.
-/

@[expose] public section

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

namespace Fin

variable {n k : ℕ}

/-
**Fin.xor_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：xor_assoc (h : k = 2 ^ n) (a b c : Fin k) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^
 c)
参数：h : k = 2 ^ n；a b c : Fin k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xor_assoc (h : k = 2 ^ n) (a b c : Fin k) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  grind [Fin.xor_val, Nat.xor_mod_two_pow, Nat.mod_mod]
/-
**Fin.xor_comm** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：xor_comm (a b : Fin k) : a ^^^ b = b ^^^ a
参数：a b : Fin k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem xor_comm (a b : Fin k) : a ^^^ b = b ^^^ a := by grind [Fin.xor_val]
/-
**Fin.xor_self** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {k : ℕ} [inst : NeZero k] (a : Fin k), a ^^^ a = 0
参数：a : Fin k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem xor_self [NeZero k] (a : Fin k) : a ^^^ a = 0 := by
  grind [Fin.xor_val, Nat.zero_mod]
/-
**Fin.xor_zero** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：∀ {k : ℕ} [inst : NeZero k] (a : Fin k), a ^^^ 0 = a
参数：a : Fin k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem xor_zero [NeZero k] (a : Fin k) : a ^^^ 0 = a := by
  grind [Fin.xor_val, Fin.val_zero, Nat.mod_eq_of_lt]

end Fin

