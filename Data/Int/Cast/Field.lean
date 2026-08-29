/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Cast of integers into fields

This file concerns the canonical homomorphism `ℤ → F`, where `F` is a field.

## Main results

* `Int.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/

public section


namespace Int

open Nat

variable {α : Type*}

/-- Auxiliary lemma for `norm_cast` to move the cast `-↑n` upwards to `↑-↑n`.

(The restriction to `DivisionRing` is necessary, otherwise this would also apply in the case where
`R = ℤ` and cause nontermination.)
-/
@[norm_cast]
/--
theorem `cast_neg_natCast` / 定理 `cast_neg_natCast`

English:
theorem cast_neg_natCast
  given: {R} [DivisionRing R] (n : Nat)
  statement: ((-n : Int) : R) = -n
  proof: by simp

@[simp]

中文:
定理 cast_neg_natCast
  条件: {R} [除环 R] (n : 自然数)
  结论: ((-n : 整数) : R) = -n
  证明: by simp

@[simp]
-/
theorem cast_neg_natCast {R} [DivisionRing R] (n : Nat) : ((-n : Int) : R) = -n := by simp

@[simp]
/--
theorem `cast_div` / 定理 `cast_div`

English:
theorem cast_div
  given: [DivisionRing α] {m n : Int} (n_dvd : n ∣ m) (hn : (n : α) != 0)
  proof: by
  rcases n_dvd with ⟨k, rfl⟩
  have : n != 0 := by rintro rfl; simp at hn
  rw [Int.mul_ediv_cancel_left _ this]; rw [mul_comm n]; rw [Int.cast_mul]; rw [mul_div_cancel_right₀ _ hn]

中文:
定理 cast_div
  条件: [除环 α] {m n : 整数} (n_dvd : n ∣ m) (hn : (n : α) != 0)
  证明: by
  rcases n_dvd with ⟨k, rfl⟩
  have : n != 0 := by rintro rfl; simp at hn
  rw [Int.mul_ediv_cancel_left _ this]; rw [mul_comm n]; rw [Int.cast_mul]; rw [mul_div_cancel_right₀ _ hn]

Depends on / 依赖: Int.cast_mul, Int.mul_ediv_cancel_left, cast_mul, mul_comm, mul_ediv_cancel_left, n_dvd
-/
theorem cast_div [DivisionRing α] {m n : Int} (n_dvd : n ∣ m) (hn : (n : α) != 0) :
    ((m / n : Int) : α) = m / n := by
  rcases n_dvd with ⟨k, rfl⟩
  have : n != 0 := by rintro rfl; simp at hn
  rw [Int.mul_ediv_cancel_left _ this]; rw [mul_comm n]; rw [Int.cast_mul]; rw [mul_div_cancel_right₀ _ hn]

end Int
