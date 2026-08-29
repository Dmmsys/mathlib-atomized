/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Order.AbsoluteValue.Basic

/-!
# Absolute values and the integers

This file contains some results on absolute values applied to integers.

## Main results

* `AbsoluteValue.map_units_int`: an absolute value sends all units of `ℤ` to `1`
-/

public section

variable {R S : Type*} [Ring R] [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

@[simp]
/--
theorem `AbsoluteValue.map_units_int` / 定理 `AbsoluteValue.map_units_int`

English:
theorem AbsoluteValue.map_units_int
  given: (abv : AbsoluteValue Int S) (x : Intˣ)
  statement: abv x = 1
  proof: by
  rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp

@[simp]

中文:
定理 绝对值.map_units_int
  条件: (abv : 绝对值 整数 S) (x : 整数ˣ)
  结论: abv x = 1
  证明: by
  rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp

@[simp]

Depends on / 依赖: Int.units_eq_one_or, units_eq_one_or
-/
theorem AbsoluteValue.map_units_int (abv : AbsoluteValue Int S) (x : Intˣ) : abv x = 1 := by
  rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp

@[simp]
/--
theorem `AbsoluteValue.map_units_intCast` / 定理 `AbsoluteValue.map_units_intCast`

English:
theorem AbsoluteValue.map_units_intCast
  given: [Nontrivial R] (abv : AbsoluteValue R S) (x : Intˣ)
  proof: by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp

@[simp]

中文:
定理 绝对值.map_units_intCast
  条件: [非平凡 R] (abv : 绝对值 R S) (x : 整数ˣ)
  证明: by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp

@[simp]

Depends on / 依赖: Int.units_eq_one_or, units_eq_one_or
-/
theorem AbsoluteValue.map_units_intCast [Nontrivial R] (abv : AbsoluteValue R S) (x : Intˣ) :
    abv ((x : Int) : R) = 1 := by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp

@[simp]
/--
theorem `AbsoluteValue.map_units_int_smul` / 定理 `AbsoluteValue.map_units_int_smul`

English:
theorem AbsoluteValue.map_units_int_smul
  given: (abv : AbsoluteValue R S) (x : Intˣ) (y : R)
  proof: by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp

中文:
定理 绝对值.map_units_int_smul
  条件: (abv : 绝对值 R S) (x : 整数ˣ) (y : R)
  证明: by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp

Depends on / 依赖: Int.units_eq_one_or, units_eq_one_or
-/
theorem AbsoluteValue.map_units_int_smul (abv : AbsoluteValue R S) (x : Intˣ) (y : R) :
    abv (x • y) = abv y := by rcases Int.units_eq_one_or x with (rfl | rfl) <;> simp
