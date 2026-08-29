/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Cast

/-!
# Cast of binomial coefficients

This file allows calculating the binomial coefficient `a.choose b` as an element of a division ring
of characteristic `0`.
-/

public section


open Nat

variable (K : Type*)

namespace Nat
section DivisionSemiring
variable [DivisionSemiring K] [CharZero K]

/--
theorem `cast_choose` / 定理 `cast_choose`

English:
theorem cast_choose
  given: {a b : Nat} (h : a <= b)
  statement: (b.choose a : K) = b ! / (a ! * (b - a)!)
  proof: by
  have : forall {n : Nat}, (n ! : K) != 0 := Nat.cast_ne_zero.2 (factorial_pos _).ne'
  rw [eq_div_iff_mul_eq (mul_ne_zero this this)]
  rw_mod_cast [← mul_assoc, choose_mul_factorial_mul_factorial h]

中文:
定理 cast_choose
  条件: {a b : 自然数} (h : a <= b)
  结论: (b.choose a : K) = b ! / (a ! * (b - a)!)
  证明: by
  have : forall {n : Nat}, (n ! : K) != 0 := Nat.cast_ne_zero.2 (factorial_pos _).ne'
  rw [eq_div_iff_mul_eq (mul_ne_zero this this)]
  rw_mod_cast [← mul_assoc, choose_mul_factorial_mul_factorial h]

Depends on / 依赖: Nat.cast_ne_zero, cast_ne_zero, choose_mul_factorial_mul_factorial, eq_div_iff_mul_eq, factorial_pos, mul_assoc, mul_ne_zero, rw_mod_cast
-/
theorem cast_choose {a b : Nat} (h : a <= b) : (b.choose a : K) = b ! / (a ! * (b - a)!) := by
  have : forall {n : Nat}, (n ! : K) != 0 := Nat.cast_ne_zero.2 (factorial_pos _).ne'
  rw [eq_div_iff_mul_eq (mul_ne_zero this this)]
  rw_mod_cast [← mul_assoc, choose_mul_factorial_mul_factorial h]

/--
theorem `cast_add_choose` / 定理 `cast_add_choose`

English:
theorem cast_add_choose
  given: {a b : Nat}
  statement: ((a + b).choose a : K) = (a + b)! / (a ! * b !)
  proof: by
  rw [cast_choose K (le_add_right _ _)]; rw [Nat.add_sub_cancel_left]

中文:
定理 cast_add_choose
  条件: {a b : 自然数}
  结论: ((a + b).choose a : K) = (a + b)! / (a ! * b !)
  证明: by
  rw [cast_choose K (le_add_right _ _)]; rw [Nat.add_sub_cancel_left]

Depends on / 依赖: Nat.add_sub_cancel_left, add_sub_cancel_left, cast_choose, le_add_right
-/
theorem cast_add_choose {a b : Nat} : ((a + b).choose a : K) = (a + b)! / (a ! * b !) := by
  rw [cast_choose K (le_add_right _ _)]; rw [Nat.add_sub_cancel_left]

end DivisionSemiring

section DivisionRing
variable [DivisionRing K] [NeZero (2 : K)]

/--
theorem `cast_choose_two` / 定理 `cast_choose_two`

English:
theorem cast_choose_two
  given: (a : Nat)
  statement: (a.choose 2 : K) = a * (a - 1) / 2
  proof: by
  rw [← cast_descFactorial_two]; rw [descFactorial_eq_factorial_mul_choose]; rw [factorial_two]; rw [mul_comm]; rw [cast_mul]; rw [cast_two]; rw [eq_div_iff_mul_eq two_ne_zero]

中文:
定理 cast_choose_two
  条件: (a : 自然数)
  结论: (a.choose 2 : K) = a * (a - 1) / 2
  证明: by
  rw [← cast_descFactorial_two]; rw [descFactorial_eq_factorial_mul_choose]; rw [factorial_two]; rw [mul_comm]; rw [cast_mul]; rw [cast_two]; rw [eq_div_iff_mul_eq two_ne_zero]

Depends on / 依赖: cast_descFactorial_two, cast_mul, cast_two, descFactorial_eq_factorial_mul_choose, eq_div_iff_mul_eq, factorial_two, mul_comm, two_ne_zero
-/
theorem cast_choose_two (a : Nat) : (a.choose 2 : K) = a * (a - 1) / 2 := by
  rw [← cast_descFactorial_two]; rw [descFactorial_eq_factorial_mul_choose]; rw [factorial_two]; rw [mul_comm]; rw [cast_mul]; rw [cast_two]; rw [eq_div_iff_mul_eq two_ne_zero]

end DivisionRing
end Nat
