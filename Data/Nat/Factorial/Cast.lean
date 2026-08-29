/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Cast of factorials

This file allows calculating factorials (including ascending and descending ones) as elements of a
semiring.

This is particularly crucial for `Nat.descFactorial` as subtraction on `ℕ` does **not** correspond
to subtraction on a general semiring. For example, we can't rely on existing cast lemmas to prove
`↑(a.descFactorial 2) = ↑a * (↑a - 1)`. We must use the fact that, whenever `↑(a - 1)` is not equal
to `↑a - 1`, the other factor is `0` anyway.
-/

public section


open Nat

variable (S : Type*)

namespace Nat

section Ring

variable [Ring S] (a b : Nat)

/--
theorem `cast_descFactorial_two` / 定理 `cast_descFactorial_two`

English:
theorem cast_descFactorial_two
  statement: (a.descFactorial 2 : S) = a * (a - 1)
  proof: by
  rw [descFactorial]
  cases a
  · simp
  · simp [mul_add, add_mul]

中文:
定理 cast_descFactorial_two
  结论: (a.descFactorial 2 : S) = a * (a - 1)
  证明: by
  rw [descFactorial]
  cases a
  · simp
  · simp [mul_add, add_mul]

Depends on / 依赖: add_mul, descFactorial, mul_add
-/
theorem cast_descFactorial_two : (a.descFactorial 2 : S) = a * (a - 1) := by
  rw [descFactorial]
  cases a
  · simp
  · simp [mul_add, add_mul]

end Ring

end Nat
