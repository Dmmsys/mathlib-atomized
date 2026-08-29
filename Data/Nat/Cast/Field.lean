/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Patrick Stevens
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Cast of naturals into fields

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a field.

## Main results

* `Nat.cast_div`: if `n` divides `m`, then `↑(m / n) = ↑m / ↑n`
-/

public section


namespace Nat

variable {K : Type*} [DivisionSemiring K] {d m n : Nat}

@[simp]
/--
lemma `cast_div` / 引理 `cast_div`

English:
lemma cast_div
  given: (hnm : n ∣ m) (hn : (n : K) != 0)
  statement: (↑(m / n) : K) = m / n
  proof: by
  obtain ⟨k, rfl⟩ := hnm
  have : n != 0 := by rintro rfl; simp at hn
  rw [Nat.mul_div_cancel_left _ <| zero_lt_of_ne_zero this]; rw [mul_comm n]; rw [cast_mul]; rw [mul_div_cancel_right₀ _ hn]

中文:
引理 cast_div
  条件: (hnm : n ∣ m) (hn : (n : K) != 0)
  结论: (↑(m / n) : K) = m / n
  证明: by
  obtain ⟨k, rfl⟩ := hnm
  have : n != 0 := by rintro rfl; simp at hn
  rw [Nat.mul_div_cancel_left _ <| zero_lt_of_ne_zero this]; rw [mul_comm n]; rw [cast_mul]; rw [mul_div_cancel_right₀ _ hn]

Depends on / 依赖: Nat.mul_div_cancel_left, cast_mul, mul_comm, mul_div_cancel_left, zero_lt_of_ne_zero
-/
lemma cast_div (hnm : n ∣ m) (hn : (n : K) != 0) : (↑(m / n) : K) = m / n := by
  obtain ⟨k, rfl⟩ := hnm
  have : n != 0 := by rintro rfl; simp at hn
  rw [Nat.mul_div_cancel_left _ <| zero_lt_of_ne_zero this]; rw [mul_comm n]; rw [cast_mul]; rw [mul_div_cancel_right₀ _ hn]

variable [CharZero K]

@[simp, norm_cast]
/--
lemma `cast_div_charZero` / 引理 `cast_div_charZero`

English:
lemma cast_div_charZero
  given: (hnm : n ∣ m)
  statement: (↑(m / n) : K) = m / n
  proof: by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

中文:
引理 cast_div_charZero
  条件: (hnm : n ∣ m)
  结论: (↑(m / n) : K) = m / n
  证明: by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
lemma cast_div_charZero (hnm : n ∣ m) : (↑(m / n) : K) = m / n := by
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

/--
lemma `cast_div_div_div_cancel_right` / 引理 `cast_div_div_div_cancel_right`

English:
lemma cast_div_div_div_cancel_right
  given: (hn : d ∣ n) (hm : d ∣ m)
  proof: by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [Nat.zero_dvd.1 hm]
  replace hd : (d : K) != 0 := by norm_cast
  rw [cast_div hm]; rw [cast_div hn]; rw [div_div_div_cancel_right₀ hd] <;> exact hd

中文:
引理 cast_div_div_div_cancel_right
  条件: (hn : d ∣ n) (hm : d ∣ m)
  证明: by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [Nat.zero_dvd.1 hm]
  replace hd : (d : K) != 0 := by norm_cast
  rw [cast_div hm]; rw [cast_div hn]; rw [div_div_div_cancel_right₀ hd] <;> exact hd

Depends on / 依赖: Nat.zero_dvd, cast_div, eq_or_ne, replace, zero_dvd
-/
lemma cast_div_div_div_cancel_right (hn : d ∣ n) (hm : d ∣ m) :
    (↑(m / d) : K) / (↑(n / d) : K) = (m : K) / n := by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [Nat.zero_dvd.1 hm]
  replace hd : (d : K) != 0 := by norm_cast
  rw [cast_div hm]; rw [cast_div hn]; rw [div_div_div_cancel_right₀ hd] <;> exact hd

end Nat
