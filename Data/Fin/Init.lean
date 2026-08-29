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

variable {n k : Nat}

/--
theorem `xor_assoc` / 定理 `xor_assoc`

English:
theorem xor_assoc
  given: (h : k = 2 ^ n) (a b c : Fin k)
  statement: (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c)
  proof: by
  grind [Fin.xor_val, Nat.xor_mod_two_pow, Nat.mod_mod]

中文:
定理 xor_assoc
  条件: (h : k = 2 ^ n) (a b c : 有限集 k)
  结论: (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c)
  证明: by
  grind [Fin.xor_val, Nat.xor_mod_two_pow, Nat.mod_mod]

Depends on / 依赖: Fin.xor_val, Nat.mod_mod, Nat.xor_mod_two_pow, mod_mod, xor_mod_two_pow, xor_val
-/
theorem xor_assoc (h : k = 2 ^ n) (a b c : Fin k) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  grind [Fin.xor_val, Nat.xor_mod_two_pow, Nat.mod_mod]
/--
theorem `xor_comm` / 定理 `xor_comm`

English:
theorem xor_comm
  given: (a b : Fin k)
  statement: a ^^^ b = b ^^^ a
  proof: by grind [Fin.xor_val]

中文:
定理 xor_comm
  条件: (a b : 有限集 k)
  结论: a ^^^ b = b ^^^ a
  证明: by grind [Fin.xor_val]

Depends on / 依赖: Fin.val_zero, Fin.xor_val, Nat.mod_eq_of_lt, Nat.zero_mod, NeZero, mod_eq_of_lt, theorem, val_zero, xor_self, xor_val, xor_zero, zero_mod
-/
theorem xor_comm (a b : Fin k) : a ^^^ b = b ^^^ a := by grind [Fin.xor_val]
/--
theorem `xor_self` / 定理 `xor_self`

English:
theorem xor_self
  given: [NeZero k] (a : Fin k)
  statement: a ^^^ a = 0
  proof: by
  grind [Fin.xor_val, Nat.zero_mod]

中文:
定理 xor_self
  条件: [NeZero k] (a : 有限集 k)
  结论: a ^^^ a = 0
  证明: by
  grind [Fin.xor_val, Nat.zero_mod]
-/
@[simp] theorem xor_self [NeZero k] (a : Fin k) : a ^^^ a = 0 := by
  grind [Fin.xor_val, Nat.zero_mod]
/--
theorem `xor_zero` / 定理 `xor_zero`

English:
theorem xor_zero
  given: [NeZero k] (a : Fin k)
  statement: a ^^^ 0 = a
  proof: by
  grind [Fin.xor_val, Fin.val_zero, Nat.mod_eq_of_lt]

中文:
定理 xor_zero
  条件: [NeZero k] (a : 有限集 k)
  结论: a ^^^ 0 = a
  证明: by
  grind [Fin.xor_val, Fin.val_zero, Nat.mod_eq_of_lt]
-/
@[simp] theorem xor_zero [NeZero k] (a : Fin k) : a ^^^ 0 = a := by
  grind [Fin.xor_val, Fin.val_zero, Nat.mod_eq_of_lt]

end Fin
