/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
module

public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Rounding

This file defines the `round` function, which uses the `floor` or `ceil` function to round a number
to the nearest integer.

## Main Definitions

* `round a`: Nearest integer to `a`. It rounds halves towards infinity.

## Tags

rounding
-/

@[expose] public section

assert_not_exists Finset

open Set

variable {F α β : Type*}

open Int

/-! ### Round -/

section round

section LinearOrderedRing

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

/--
Definition of `round` / `round` 的定义

English:
definition round
  signature: (x : α)
  body: if 2 * fract x < 1 then ⌊x⌋ else ⌈x⌉

中文:
定义 round
  签名: (x : α)
  定义体: if 2 * fract x < 1 then ⌊x⌋ else ⌈x⌉
-/
def round (x : α) : Int :=
  if 2 * fract x < 1 then ⌊x⌋ else ⌈x⌉

/--
theorem `round_eq_div` / 定理 `round_eq_div`

English:
theorem round_eq_div
  given: (x : α)
  statement: round x = (⌊2 * x⌋ + 1) / 2
  proof: by
  rw [← floor_add_fract x]; rw [round]; rw [fract_intCast_add]; rw [fract_fract]; rw [floor_intCast_add]; rw [mul_add]; rw [← Int.cast_ofNat]; rw [← Int.cast_mul]; rw [floor_intCast_add]; rw [ceil_intCast_add]; rw [add_assoc]; rw [Int.mul_add_ediv_left _ _ two_ne_zero]; rw [Int.cast_ofNat]
  split_ifs with h <;> congr 1
  · rw [Int.floor_eq_zero_iff.mpr, Int.floor_eq_zero_iff.mpr]
    · simp
    · simp [h]
    · suffices fract x < 1 by simpa
      refine lt_of_le_of_lt ?_ h
      apply le_mul_of_one_le_left <;> simp
  · have H : ⌊2 * fract x⌋ = 1 := by simpa [floor_eq_iff, ← two_mul, fract_lt_one] using h
    suffices 0 < fract x by simp [this, H, ceil_eq_iff, (fract_lt_one _).le]
    contrapose! h
    grw [h]
    simp

@[simp]

中文:
定理 round_eq_div
  条件: (x : α)
  结论: round x = (⌊2 * x⌋ + 1) / 2
  证明: by
  rw [← floor_add_fract x]; rw [round]; rw [fract_intCast_add]; rw [fract_fract]; rw [floor_intCast_add]; rw [mul_add]; rw [← Int.cast_ofNat]; rw [← Int.cast_mul]; rw [floor_intCast_add]; rw [ceil_intCast_add]; rw [add_assoc]; rw [Int.mul_add_ediv_left _ _ two_ne_zero]; rw [Int.cast_ofNat]
  split_ifs with h <;> congr 1
  · rw [Int.floor_eq_zero_iff.mpr, Int.floor_eq_zero_iff.mpr]
    · simp
    · simp [h]
    · suffices fract x < 1 by simpa
      refine lt_of_le_of_lt ?_ h
      apply le_mul_of_one_le_left <;> simp
  · have H : ⌊2 * fract x⌋ = 1 := by simpa [floor_eq_iff, ← two_mul, fract_lt_one] using h
    suffices 0 < fract x by simp [this, H, ceil_eq_iff, (fract_lt_one _).le]
    contrapose! h
    grw [h]
    simp

@[simp]

Depends on / 依赖: Int.cast_mul, Int.cast_ofNat, Int.floor_eq_zero_iff.mpr, Int.mul_add_ediv_left, add_assoc, cast_mul, cast_ofNat, ceil_intCast_add, floor_add_fract, floor_eq_zero_iff, floor_intCast_add, fract_fract, fract_intCast_add, le_mul_of_one_le_left, lt_of_le_of_lt, mul_add, mul_add_ediv_left, split_ifs, two_ne_zero
-/
theorem round_eq_div (x : α) : round x = (⌊2 * x⌋ + 1) / 2 := by
  rw [← floor_add_fract x]; rw [round]; rw [fract_intCast_add]; rw [fract_fract]; rw [floor_intCast_add]; rw [mul_add]; rw [← Int.cast_ofNat]; rw [← Int.cast_mul]; rw [floor_intCast_add]; rw [ceil_intCast_add]; rw [add_assoc]; rw [Int.mul_add_ediv_left _ _ two_ne_zero]; rw [Int.cast_ofNat]
  split_ifs with h <;> congr 1
  · rw [Int.floor_eq_zero_iff.mpr, Int.floor_eq_zero_iff.mpr]
    · simp
    · simp [h]
    · suffices fract x < 1 by simpa
      refine lt_of_le_of_lt ?_ h
      apply le_mul_of_one_le_left <;> simp
  · have H : ⌊2 * fract x⌋ = 1 := by simpa [floor_eq_iff, ← two_mul, fract_lt_one] using h
    suffices 0 < fract x by simp [this, H, ceil_eq_iff, (fract_lt_one _).le]
    contrapose! h
    grw [h]
    simp

@[simp]
/--
theorem `round_zero` / 定理 `round_zero`

English:
theorem round_zero
  statement: round (0 : α) = 0
  proof: by simp [round]

@[simp]

中文:
定理 round_zero
  结论: round (0 : α) = 0
  证明: by simp [round]

@[simp]
-/
theorem round_zero : round (0 : α) = 0 := by simp [round]

@[simp]
/--
theorem `round_one` / 定理 `round_one`

English:
theorem round_one
  statement: round (1 : α) = 1
  proof: by simp [round]

@[simp]

中文:
定理 round_one
  结论: round (1 : α) = 1
  证明: by simp [round]

@[simp]
-/
theorem round_one : round (1 : α) = 1 := by simp [round]

@[simp]
/--
theorem `round_natCast` / 定理 `round_natCast`

English:
theorem round_natCast
  given: (n : Nat)
  statement: round (n : α) = n
  proof: by simp [round]

@[simp]

中文:
定理 round_natCast
  条件: (n : 自然数)
  结论: round (n : α) = n
  证明: by simp [round]

@[simp]
-/
theorem round_natCast (n : Nat) : round (n : α) = n := by simp [round]

@[simp]
/--
theorem `round_ofNat` / 定理 `round_ofNat`

English:
theorem round_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: round (ofNat(n) : α) = ofNat(n)
  proof: round_natCast n

@[simp]

中文:
定理 round_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: round (of自然数(n) : α) = of自然数(n)
  证明: round_natCast n

@[simp]

Depends on / 依赖: round_natCast
-/
theorem round_ofNat (n : Nat) [n.AtLeastTwo] : round (ofNat(n) : α) = ofNat(n) :=
  round_natCast n

@[simp]
/--
theorem `round_intCast` / 定理 `round_intCast`

English:
theorem round_intCast
  given: (n : Int)
  statement: round (n : α) = n
  proof: by simp [round]

中文:
定理 round_intCast
  条件: (n : 整数)
  结论: round (n : α) = n
  证明: by simp [round]
-/
theorem round_intCast (n : Int) : round (n : α) = n := by simp [round]

/--
theorem `round_eq_half_ceil_two_mul` / 定理 `round_eq_half_ceil_two_mul`

English:
theorem round_eq_half_ceil_two_mul
  given: {x : α} (hx : 2 * fract x != 1)
  statement: round x = ⌈2 * x⌉ / 2
  proof: by
  rcases em (2 * x in range Int.cast) with ⟨m, hm⟩ | hx'
  · rw [← hm, ceil_intCast]
    rcases m.even_or_odd with ⟨m, rfl⟩ | ⟨m, rfl⟩
· obtain rfl : m = x := mul_left_cancel₀ two_ne_zero by simp [← hm, ← two_mul]
      rw [round_intCast]; rw [← two_mul]; rw [Int.mul_ediv_cancel_left _ two_ne_zero]
    · refine absurd ?_ hx
      exact (mul_fract_eq_one_iff_exists_int one_lt_two).mpr ⟨m, mod_cast hm.symm⟩
  · rw [round_eq_div, (ceil_eq_floor_add_one_iff_notMem _).mpr hx']

@[simp]

中文:
定理 round_eq_half_ceil_two_mul
  条件: {x : α} (hx : 2 * fract x != 1)
  结论: round x = ⌈2 * x⌉ / 2
  证明: by
  rcases em (2 * x in range Int.cast) with ⟨m, hm⟩ | hx'
  · rw [← hm, ceil_intCast]
    rcases m.even_or_odd with ⟨m, rfl⟩ | ⟨m, rfl⟩
· obtain rfl : m = x := mul_left_cancel₀ two_ne_zero by simp [← hm, ← two_mul]
      rw [round_intCast]; rw [← two_mul]; rw [Int.mul_ediv_cancel_left _ two_ne_zero]
    · refine absurd ?_ hx
      exact (mul_fract_eq_one_iff_exists_int one_lt_two).mpr ⟨m, mod_cast hm.symm⟩
  · rw [round_eq_div, (ceil_eq_floor_add_one_iff_notMem _).mpr hx']

@[simp]

Depends on / 依赖: Int.cast, Int.mul_ediv_cancel_left, absurd, ceil_eq_floor_add_one_iff_notMem, ceil_intCast, even_or_odd, hm.symm, m.even_or_odd, mod_cast, mul_ediv_cancel_left, mul_fract_eq_one_iff_exists_int, one_lt_two, round_eq_div, round_intCast, two_mul, two_ne_zero
-/
theorem round_eq_half_ceil_two_mul {x : α} (hx : 2 * fract x != 1) : round x = ⌈2 * x⌉ / 2 := by
  rcases em (2 * x in range Int.cast) with ⟨m, hm⟩ | hx'
  · rw [← hm, ceil_intCast]
    rcases m.even_or_odd with ⟨m, rfl⟩ | ⟨m, rfl⟩
· obtain rfl : m = x := mul_left_cancel₀ two_ne_zero by simp [← hm, ← two_mul]
      rw [round_intCast]; rw [← two_mul]; rw [Int.mul_ediv_cancel_left _ two_ne_zero]
    · refine absurd ?_ hx
      exact (mul_fract_eq_one_iff_exists_int one_lt_two).mpr ⟨m, mod_cast hm.symm⟩
  · rw [round_eq_div, (ceil_eq_floor_add_one_iff_notMem _).mpr hx']

@[simp]
/--
theorem `round_add_intCast` / 定理 `round_add_intCast`

English:
theorem round_add_intCast
  given: (x : α) (y : Int)
  statement: round (x + y) = round x + y
  proof: by
  rw [round]; rw [round]; rw [Int.fract_add_intCast]; rw [Int.floor_add_intCast]; rw [Int.ceil_add_intCast]; rw [← apply_ite₂]; rw [ite_self]

@[simp]

中文:
定理 round_add_intCast
  条件: (x : α) (y : 整数)
  结论: round (x + y) = round x + y
  证明: by
  rw [round]; rw [round]; rw [Int.fract_add_intCast]; rw [Int.floor_add_intCast]; rw [Int.ceil_add_intCast]; rw [← apply_ite₂]; rw [ite_self]

@[simp]

Depends on / 依赖: Int.ceil_add_intCast, Int.floor_add_intCast, Int.fract_add_intCast, ceil_add_intCast, floor_add_intCast, fract_add_intCast, ite_self
-/
theorem round_add_intCast (x : α) (y : Int) : round (x + y) = round x + y := by
  rw [round]; rw [round]; rw [Int.fract_add_intCast]; rw [Int.floor_add_intCast]; rw [Int.ceil_add_intCast]; rw [← apply_ite₂]; rw [ite_self]

@[simp]
/--
theorem `round_add_one` / 定理 `round_add_one`

English:
theorem round_add_one
  given: (a : α)
  statement: round (a + 1) = round a + 1
  proof: by
  rw [← round_add_intCast a 1]; rw [cast_one]

@[simp]

中文:
定理 round_add_one
  条件: (a : α)
  结论: round (a + 1) = round a + 1
  证明: by
  rw [← round_add_intCast a 1]; rw [cast_one]

@[simp]

Depends on / 依赖: cast_one, round_add_intCast
-/
theorem round_add_one (a : α) : round (a + 1) = round a + 1 := by
  rw [← round_add_intCast a 1]; rw [cast_one]

@[simp]
/--
theorem `round_sub_intCast` / 定理 `round_sub_intCast`

English:
theorem round_sub_intCast
  given: (x : α) (y : Int)
  statement: round (x - y) = round x - y
  proof: by
  rw [sub_eq_add_neg]
  norm_cast
  rw [round_add_intCast]; rw [sub_eq_add_neg]

@[simp]

中文:
定理 round_sub_intCast
  条件: (x : α) (y : 整数)
  结论: round (x - y) = round x - y
  证明: by
  rw [sub_eq_add_neg]
  norm_cast
  rw [round_add_intCast]; rw [sub_eq_add_neg]

@[simp]

Depends on / 依赖: round_add_intCast, sub_eq_add_neg
-/
theorem round_sub_intCast (x : α) (y : Int) : round (x - y) = round x - y := by
  rw [sub_eq_add_neg]
  norm_cast
  rw [round_add_intCast]; rw [sub_eq_add_neg]

@[simp]
/--
theorem `round_sub_one` / 定理 `round_sub_one`

English:
theorem round_sub_one
  given: (a : α)
  statement: round (a - 1) = round a - 1
  proof: by
  rw [← round_sub_intCast a 1]; rw [cast_one]

@[simp]

中文:
定理 round_sub_one
  条件: (a : α)
  结论: round (a - 1) = round a - 1
  证明: by
  rw [← round_sub_intCast a 1]; rw [cast_one]

@[simp]

Depends on / 依赖: cast_one, round_sub_intCast
-/
theorem round_sub_one (a : α) : round (a - 1) = round a - 1 := by
  rw [← round_sub_intCast a 1]; rw [cast_one]

@[simp]
/--
theorem `round_add_natCast` / 定理 `round_add_natCast`

English:
theorem round_add_natCast
  given: (x : α) (y : Nat)
  statement: round (x + y) = round x + y
  proof: mod_cast round_add_intCast x y

@[simp]

中文:
定理 round_add_natCast
  条件: (x : α) (y : 自然数)
  结论: round (x + y) = round x + y
  证明: mod_cast round_add_intCast x y

@[simp]

Depends on / 依赖: mod_cast, round_add_intCast
-/
theorem round_add_natCast (x : α) (y : Nat) : round (x + y) = round x + y :=
  mod_cast round_add_intCast x y

@[simp]
/--
theorem `round_add_ofNat` / 定理 `round_add_ofNat`

English:
theorem round_add_ofNat
  given: (x : α) (n : Nat) [n.AtLeastTwo]
  proof: round_add_natCast x n

@[simp]

中文:
定理 round_add_of自然数
  条件: (x : α) (n : 自然数) [n.AtLeastTwo]
  证明: round_add_natCast x n

@[simp]

Depends on / 依赖: round_add_natCast
-/
theorem round_add_ofNat (x : α) (n : Nat) [n.AtLeastTwo] :
    round (x + ofNat(n)) = round x + ofNat(n) :=
  round_add_natCast x n

@[simp]
/--
theorem `round_sub_natCast` / 定理 `round_sub_natCast`

English:
theorem round_sub_natCast
  given: (x : α) (y : Nat)
  statement: round (x - y) = round x - y
  proof: mod_cast round_sub_intCast x y

@[simp]

中文:
定理 round_sub_natCast
  条件: (x : α) (y : 自然数)
  结论: round (x - y) = round x - y
  证明: mod_cast round_sub_intCast x y

@[simp]

Depends on / 依赖: mod_cast, round_sub_intCast
-/
theorem round_sub_natCast (x : α) (y : Nat) : round (x - y) = round x - y :=
  mod_cast round_sub_intCast x y

@[simp]
/--
theorem `round_sub_ofNat` / 定理 `round_sub_ofNat`

English:
theorem round_sub_ofNat
  given: (x : α) (n : Nat) [n.AtLeastTwo]
  proof: round_sub_natCast x n

@[simp]

中文:
定理 round_sub_of自然数
  条件: (x : α) (n : 自然数) [n.AtLeastTwo]
  证明: round_sub_natCast x n

@[simp]

Depends on / 依赖: round_sub_natCast
-/
theorem round_sub_ofNat (x : α) (n : Nat) [n.AtLeastTwo] :
    round (x - ofNat(n)) = round x - ofNat(n) :=
  round_sub_natCast x n

@[simp]
/--
theorem `round_intCast_add` / 定理 `round_intCast_add`

English:
theorem round_intCast_add
  given: (x : α) (y : Int)
  statement: round ((y : α) + x) = y + round x
  proof: by
  rw [add_comm]; rw [round_add_intCast]; rw [add_comm]

@[simp]

中文:
定理 round_intCast_add
  条件: (x : α) (y : 整数)
  结论: round ((y : α) + x) = y + round x
  证明: by
  rw [add_comm]; rw [round_add_intCast]; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, round_add_intCast
-/
theorem round_intCast_add (x : α) (y : Int) : round ((y : α) + x) = y + round x := by
  rw [add_comm]; rw [round_add_intCast]; rw [add_comm]

@[simp]
/--
theorem `round_natCast_add` / 定理 `round_natCast_add`

English:
theorem round_natCast_add
  given: (x : α) (y : Nat)
  statement: round ((y : α) + x) = y + round x
  proof: by
  rw [add_comm]; rw [round_add_natCast]; rw [add_comm]

@[simp]

中文:
定理 round_natCast_add
  条件: (x : α) (y : 自然数)
  结论: round ((y : α) + x) = y + round x
  证明: by
  rw [add_comm]; rw [round_add_natCast]; rw [add_comm]

@[simp]

Depends on / 依赖: add_comm, round_add_natCast
-/
theorem round_natCast_add (x : α) (y : Nat) : round ((y : α) + x) = y + round x := by
  rw [add_comm]; rw [round_add_natCast]; rw [add_comm]

@[simp]
/--
theorem `round_ofNat_add` / 定理 `round_ofNat_add`

English:
theorem round_ofNat_add
  given: (n : Nat) [n.AtLeastTwo] (x : α)
  proof: round_natCast_add x n

中文:
定理 round_of自然数_add
  条件: (n : 自然数) [n.AtLeastTwo] (x : α)
  证明: round_natCast_add x n

Depends on / 依赖: round_natCast_add
-/
theorem round_ofNat_add (n : Nat) [n.AtLeastTwo] (x : α) :
    round (ofNat(n) + x) = ofNat(n) + round x :=
  round_natCast_add x n

/--
theorem `abs_sub_round_eq_min` / 定理 `abs_sub_round_eq_min`

English:
theorem abs_sub_round_eq_min
  given: (x : α)
  statement: |x - round x| = min (fract x) (1 - fract x)
  proof: by
  simp_rw [round, min_def_lt, two_mul, ← lt_tsub_iff_left]
  rcases lt_or_ge (fract x) (1 - fract x) with hx | hx
  · rw [if_pos hx, if_pos hx, self_sub_floor, abs_fract]
  · have : 0 < fract x := by
      replace hx : 0 < fract x + fract x := lt_of_lt_of_le zero_lt_one (tsub_le_iff_left.mp hx)
      simpa only [← two_mul, mul_pos_iff_of_pos_left, zero_lt_two] using hx
    rw [if_neg (not_lt.mpr hx)]; rw [if_neg (not_lt.mpr hx)]; rw [abs_sub_comm]; rw [ceil_sub_self_eq this.ne.symm]; rw [abs_one_sub_fract]

中文:
定理 abs_sub_round_eq_min
  条件: (x : α)
  结论: |x - round x| = 最小值 (fract x) (1 - fract x)
  证明: by
  simp_rw [round, min_def_lt, two_mul, ← lt_tsub_iff_left]
  rcases lt_or_ge (fract x) (1 - fract x) with hx | hx
  · rw [if_pos hx, if_pos hx, self_sub_floor, abs_fract]
  · have : 0 < fract x := by
      replace hx : 0 < fract x + fract x := lt_of_lt_of_le zero_lt_one (tsub_le_iff_left.mp hx)
      simpa only [← two_mul, mul_pos_iff_of_pos_left, zero_lt_two] using hx
    rw [if_neg (not_lt.mpr hx)]; rw [if_neg (not_lt.mpr hx)]; rw [abs_sub_comm]; rw [ceil_sub_self_eq this.ne.symm]; rw [abs_one_sub_fract]

Depends on / 依赖: abs_fract, abs_one_sub_fract, abs_sub_comm, ceil_sub_self_eq, if_neg, if_pos, lt_of_lt_of_le, lt_or_ge, lt_tsub_iff_left, min_def_lt, mul_pos_iff_of_pos_left, not_lt, not_lt.mpr, replace, self_sub_floor, simp_rw, this.ne.symm, tsub_le_iff_left, tsub_le_iff_left.mp, two_mul
-/
theorem abs_sub_round_eq_min (x : α) : |x - round x| = min (fract x) (1 - fract x) := by
  simp_rw [round, min_def_lt, two_mul, ← lt_tsub_iff_left]
  rcases lt_or_ge (fract x) (1 - fract x) with hx | hx
  · rw [if_pos hx, if_pos hx, self_sub_floor, abs_fract]
  · have : 0 < fract x := by
      replace hx : 0 < fract x + fract x := lt_of_lt_of_le zero_lt_one (tsub_le_iff_left.mp hx)
      simpa only [← two_mul, mul_pos_iff_of_pos_left, zero_lt_two] using hx
    rw [if_neg (not_lt.mpr hx)]; rw [if_neg (not_lt.mpr hx)]; rw [abs_sub_comm]; rw [ceil_sub_self_eq this.ne.symm]; rw [abs_one_sub_fract]

/--
theorem `round_le` / 定理 `round_le`

English:
theorem round_le
  given: (x : α) (z : Int)
  statement: |x - round x| <= |x - z|
  proof: by
  rw [abs_sub_round_eq_min]; rw [min_le_iff]
  rcases le_or_gt (z : α) x with (hx | hx) <;> [left; right]
  · conv_rhs => rw [abs_eq_self.mpr (sub_nonneg.mpr hx), ← fract_add_floor x, add_sub_assoc]
    simpa only [le_add_iff_nonneg_right, sub_nonneg, cast_le] using le_floor.mpr hx
  · rw [abs_eq_neg_self.mpr (sub_neg.mpr hx).le]
    conv_rhs => rw [← fract_add_floor x]
    rw [add_sub_assoc]; rw [add_comm]; rw [neg_add]; rw [neg_sub]; rw [le_add_neg_iff_add_le]; rw [sub_add_cancel]; rw [le_sub_comm]
    norm_cast
    rwa [le_sub_one_iff, floor_lt]

中文:
定理 round_le
  条件: (x : α) (z : 整数)
  结论: |x - round x| <= |x - z|
  证明: by
  rw [abs_sub_round_eq_min]; rw [min_le_iff]
  rcases le_or_gt (z : α) x with (hx | hx) <;> [left; right]
  · conv_rhs => rw [abs_eq_self.mpr (sub_nonneg.mpr hx), ← fract_add_floor x, add_sub_assoc]
    simpa only [le_add_iff_nonneg_right, sub_nonneg, cast_le] using le_floor.mpr hx
  · rw [abs_eq_neg_self.mpr (sub_neg.mpr hx).le]
    conv_rhs => rw [← fract_add_floor x]
    rw [add_sub_assoc]; rw [add_comm]; rw [neg_add]; rw [neg_sub]; rw [le_add_neg_iff_add_le]; rw [sub_add_cancel]; rw [le_sub_comm]
    norm_cast
    rwa [le_sub_one_iff, floor_lt]

Depends on / 依赖: abs_eq_neg_self, abs_eq_neg_self.mpr, abs_eq_self, abs_eq_self.mpr, abs_sub_round_eq_min, add_comm, add_sub_assoc, cast_le, conv_rhs, fract_add_floor, le_add_iff_nonneg_right, le_add_neg_iff_add_le, le_floor, le_floor.mpr, le_or_gt, le_sub_comm, min_le_iff, neg_add, neg_sub, sub_add_cancel
-/
theorem round_le (x : α) (z : Int) : |x - round x| <= |x - z| := by
  rw [abs_sub_round_eq_min]; rw [min_le_iff]
  rcases le_or_gt (z : α) x with (hx | hx) <;> [left; right]
  · conv_rhs => rw [abs_eq_self.mpr (sub_nonneg.mpr hx), ← fract_add_floor x, add_sub_assoc]
    simpa only [le_add_iff_nonneg_right, sub_nonneg, cast_le] using le_floor.mpr hx
  · rw [abs_eq_neg_self.mpr (sub_neg.mpr hx).le]
    conv_rhs => rw [← fract_add_floor x]
    rw [add_sub_assoc]; rw [add_comm]; rw [neg_add]; rw [neg_sub]; rw [le_add_neg_iff_add_le]; rw [sub_add_cancel]; rw [le_sub_comm]
    norm_cast
    rwa [le_sub_one_iff, floor_lt]

end LinearOrderedRing

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

/--
theorem `round_eq` / 定理 `round_eq`

English:
theorem round_eq
  given: (x : α)
  statement: round x = ⌊x + 1 / 2⌋
  proof: by
  rw [← cast_mul_floor_div_cancel_of_pos two_pos]; rw [round_eq_div]
  simp [mul_add]

中文:
定理 round_eq
  条件: (x : α)
  结论: round x = ⌊x + 1 / 2⌋
  证明: by
  rw [← cast_mul_floor_div_cancel_of_pos two_pos]; rw [round_eq_div]
  simp [mul_add]

Depends on / 依赖: cast_mul_floor_div_cancel_of_pos, mul_add, round_eq_div, two_pos
-/
theorem round_eq (x : α) : round x = ⌊x + 1 / 2⌋ := by
  rw [← cast_mul_floor_div_cancel_of_pos two_pos]; rw [round_eq_div]
  simp [mul_add]

/--
theorem `round_eq_iff` / 定理 `round_eq_iff`

English:
theorem round_eq_iff
  given: {x : α} {n : Int}
  statement: round x = n ↔ x in Ico (n - 1 / 2 : α) (n + 1 / 2)
  proof: by
  norm_num [round_eq, floor_eq_iff, ← lt_sub_iff_add_lt, add_sub_assoc]

@[simp]

中文:
定理 round_eq_iff
  条件: {x : α} {n : 整数}
  结论: round x = n ↔ x in 左闭右开区间 (n - 1 / 2 : α) (n + 1 / 2)
  证明: by
  norm_num [round_eq, floor_eq_iff, ← lt_sub_iff_add_lt, add_sub_assoc]

@[simp]

Depends on / 依赖: add_sub_assoc, floor_eq_iff, lt_sub_iff_add_lt, round_eq
-/
theorem round_eq_iff {x : α} {n : Int} : round x = n ↔ x in Ico (n - 1 / 2 : α) (n + 1 / 2) := by
  norm_num [round_eq, floor_eq_iff, ← lt_sub_iff_add_lt, add_sub_assoc]

@[simp]
/--
theorem `round_two_inv` / 定理 `round_two_inv`

English:
theorem round_two_inv
  statement: round (2⁻¹ : α) = 1
  proof: by norm_num [round_eq_iff]

@[simp]

中文:
定理 round_two_inv
  结论: round (2⁻¹ : α) = 1
  证明: by norm_num [round_eq_iff]

@[simp]

Depends on / 依赖: round_eq_iff
-/
theorem round_two_inv : round (2⁻¹ : α) = 1 := by norm_num [round_eq_iff]

@[simp]
/--
theorem `round_neg_two_inv` / 定理 `round_neg_two_inv`

English:
theorem round_neg_two_inv
  statement: round (-2⁻¹ : α) = 0
  proof: by norm_num [round_eq_iff]

@[simp]

中文:
定理 round_neg_two_inv
  结论: round (-2⁻¹ : α) = 0
  证明: by norm_num [round_eq_iff]

@[simp]

Depends on / 依赖: round_eq_iff
-/
theorem round_neg_two_inv : round (-2⁻¹ : α) = 0 := by norm_num [round_eq_iff]

@[simp]
/--
theorem `round_eq_zero_iff` / 定理 `round_eq_zero_iff`

English:
theorem round_eq_zero_iff
  given: {x : α}
  statement: round x = 0 ↔ x in Ico (-(1 / 2)) ((1 : α) / 2)
  proof: by
  simp [round_eq_iff]

中文:
定理 round_eq_zero_iff
  条件: {x : α}
  结论: round x = 0 ↔ x in 左闭右开区间 (-(1 / 2)) ((1 : α) / 2)
  证明: by
  simp [round_eq_iff]

Depends on / 依赖: round_eq_iff
-/
theorem round_eq_zero_iff {x : α} : round x = 0 ↔ x in Ico (-(1 / 2)) ((1 : α) / 2) := by
  simp [round_eq_iff]

/--
theorem `abs_sub_round` / 定理 `abs_sub_round`

English:
theorem abs_sub_round
  given: (x : α)
  statement: |x - round x| <= 1 / 2
  proof: by
  rw [round_eq]; rw [abs_sub_le_iff]
  have := floor_le (x + 1 / 2)
  have := lt_floor_add_one (x + 1 / 2)
  constructor <;> linarith

中文:
定理 abs_sub_round
  条件: (x : α)
  结论: |x - round x| <= 1 / 2
  证明: by
  rw [round_eq]; rw [abs_sub_le_iff]
  have := floor_le (x + 1 / 2)
  have := lt_floor_add_one (x + 1 / 2)
  constructor <;> linarith

Depends on / 依赖: abs_sub_le_iff, floor_le, lt_floor_add_one, round_eq
-/
theorem abs_sub_round (x : α) : |x - round x| <= 1 / 2 := by
  rw [round_eq]; rw [abs_sub_le_iff]
  have := floor_le (x + 1 / 2)
  have := lt_floor_add_one (x + 1 / 2)
  constructor <;> linarith

/--
theorem `abs_sub_round_div_natCast_eq` / 定理 `abs_sub_round_div_natCast_eq`

English:
theorem abs_sub_round_div_natCast_eq
  given: {m n : Nat}
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn' : 0 < (n : α) := by
    norm_cast
  rw [abs_sub_round_eq_min]; rw [Nat.cast_min]; rw [← min_div_div_right hn'.le]; rw [fract_div_natCast_eq_div_natCast_mod]; rw [Nat.cast_sub (m.mod_lt hn).le]; rw [sub_div]; rw [div_self hn'.ne']

@[bound]

中文:
定理 abs_sub_round_div_natCast_eq
  条件: {m n : 自然数}
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn' : 0 < (n : α) := by
    norm_cast
  rw [abs_sub_round_eq_min]; rw [Nat.cast_min]; rw [← min_div_div_right hn'.le]; rw [fract_div_natCast_eq_div_natCast_mod]; rw [Nat.cast_sub (m.mod_lt hn).le]; rw [sub_div]; rw [div_self hn'.ne']

@[bound]

Depends on / 依赖: Nat.cast_min, Nat.cast_sub, abs_sub_round_eq_min, cast_min, cast_sub, div_self, eq_zero_or_pos, fract_div_natCast_eq_div_natCast_mod, m.mod_lt, min_div_div_right, mod_lt, n.eq_zero_or_pos, sub_div
-/
theorem abs_sub_round_div_natCast_eq {m n : Nat} :
    |(m : α) / n - round ((m : α) / n)| = ↑(min (m % n) (n - m % n)) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn' : 0 < (n : α) := by
    norm_cast
  rw [abs_sub_round_eq_min]; rw [Nat.cast_min]; rw [← min_div_div_right hn'.le]; rw [fract_div_natCast_eq_div_natCast_mod]; rw [Nat.cast_sub (m.mod_lt hn).le]; rw [sub_div]; rw [div_self hn'.ne']

@[bound]
/--
theorem `sub_half_lt_round` / 定理 `sub_half_lt_round`

English:
theorem sub_half_lt_round
  given: (x : α)
  statement: x - 1 / 2 < round x
  proof: by
  rw [round_eq x]; rw [show x - 1 / 2 = x + 1 / 2 - 1 by linarith]
  exact Int.sub_one_lt_floor (x + 1 / 2)

@[bound]

中文:
定理 sub_half_lt_round
  条件: (x : α)
  结论: x - 1 / 2 < round x
  证明: by
  rw [round_eq x]; rw [show x - 1 / 2 = x + 1 / 2 - 1 by linarith]
  exact Int.sub_one_lt_floor (x + 1 / 2)

@[bound]

Depends on / 依赖: Int.sub_one_lt_floor, round_eq, sub_one_lt_floor
-/
theorem sub_half_lt_round (x : α) : x - 1 / 2 < round x := by
  rw [round_eq x]; rw [show x - 1 / 2 = x + 1 / 2 - 1 by linarith]
  exact Int.sub_one_lt_floor (x + 1 / 2)

@[bound]
/--
theorem `round_le_add_half` / 定理 `round_le_add_half`

English:
theorem round_le_add_half
  given: (x : α)
  statement: round x <= x + 1 / 2
  proof: by
  rw [round_eq x]
  exact Int.floor_le (x + 1 / 2)

中文:
定理 round_le_add_half
  条件: (x : α)
  结论: round x <= x + 1 / 2
  证明: by
  rw [round_eq x]
  exact Int.floor_le (x + 1 / 2)

Depends on / 依赖: Int.floor_le, floor_le, round_eq
-/
theorem round_le_add_half (x : α) : round x <= x + 1 / 2 := by
  rw [round_eq x]
  exact Int.floor_le (x + 1 / 2)

end LinearOrderedField

end round

namespace Int

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [LinearOrder β] [IsStrictOrderedRing β] [FloorRing α] [FloorRing β]
variable [FunLike F α β] [RingHomClass F α β] {a : α} {b : β}

/--
theorem `map_round` / 定理 `map_round`

English:
theorem map_round
  given: (f : F) (hf : StrictMono f) (a : α)
  statement: round (f a) = round a
  proof: by
  simp_rw [round_eq, ← map_floor _ hf, map_add, one_div, map_inv₀, map_ofNat]

中文:
定理 map_round
  条件: (f : F) (hf : 严格递增 f) (a : α)
  结论: round (f a) = round a
  证明: by
  simp_rw [round_eq, ← map_floor _ hf, map_add, one_div, map_inv₀, map_ofNat]

Depends on / 依赖: map_add, map_floor, map_ofNat, one_div, round_eq, simp_rw
-/
theorem map_round (f : F) (hf : StrictMono f) (a : α) : round (f a) = round a := by
  simp_rw [round_eq, ← map_floor _ hf, map_add, one_div, map_inv₀, map_ofNat]

end Int
