/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Lemmas about `invOf` in ordered (semi)rings.
-/

public section

variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R}

@[simp]
/--
theorem `invOf_pos` / 定理 `invOf_pos`

English:
theorem invOf_pos
  given: [Invertible a]
  statement: 0 < ⅟a ↔ 0 < a
  proof: haveI : 0 < a * ⅟a := by simp only [mul_invOf_self, zero_lt_one]
  ⟨fun h => pos_of_mul_pos_left this h.le, fun h => pos_of_mul_pos_right this h.le⟩

@[simp]

中文:
定理 invOf_pos
  条件: [可逆 a]
  结论: 0 < ⅟a ↔ 0 < a
  证明: haveI : 0 < a * ⅟a := by simp only [mul_invOf_self, zero_lt_one]
  ⟨fun h => pos_of_mul_pos_left this h.le, fun h => pos_of_mul_pos_right this h.le⟩

@[simp]

Depends on / 依赖: h.le, mul_invOf_self, pos_of_mul_pos_left, pos_of_mul_pos_right, zero_lt_one
-/
theorem invOf_pos [Invertible a] : 0 < ⅟a ↔ 0 < a :=
  haveI : 0 < a * ⅟a := by simp only [mul_invOf_self, zero_lt_one]
  ⟨fun h => pos_of_mul_pos_left this h.le, fun h => pos_of_mul_pos_right this h.le⟩

@[simp]
/--
theorem `invOf_nonpos` / 定理 `invOf_nonpos`

English:
theorem invOf_nonpos
  given: [Invertible a]
  statement: ⅟a <= 0 ↔ a <= 0
  proof: by simp only [← not_lt, invOf_pos]

@[simp]

中文:
定理 invOf_nonpos
  条件: [可逆 a]
  结论: ⅟a <= 0 ↔ a <= 0
  证明: by simp only [← not_lt, invOf_pos]

@[simp]

Depends on / 依赖: invOf_pos, not_lt
-/
theorem invOf_nonpos [Invertible a] : ⅟a <= 0 ↔ a <= 0 := by simp only [← not_lt, invOf_pos]

@[simp]
/--
theorem `invOf_nonneg` / 定理 `invOf_nonneg`

English:
theorem invOf_nonneg
  given: [Invertible a]
  statement: 0 <= ⅟a ↔ 0 <= a
  proof: haveI : 0 < a * ⅟a := by simp only [mul_invOf_self, zero_lt_one]
  ⟨fun h => (pos_of_mul_pos_left this h).le, fun h => (pos_of_mul_pos_right this h).le⟩

@[simp]

中文:
定理 invOf_nonneg
  条件: [可逆 a]
  结论: 0 <= ⅟a ↔ 0 <= a
  证明: haveI : 0 < a * ⅟a := by simp only [mul_invOf_self, zero_lt_one]
  ⟨fun h => (pos_of_mul_pos_left this h).le, fun h => (pos_of_mul_pos_right this h).le⟩

@[simp]

Depends on / 依赖: mul_invOf_self, pos_of_mul_pos_left, pos_of_mul_pos_right, zero_lt_one
-/
theorem invOf_nonneg [Invertible a] : 0 <= ⅟a ↔ 0 <= a :=
  haveI : 0 < a * ⅟a := by simp only [mul_invOf_self, zero_lt_one]
  ⟨fun h => (pos_of_mul_pos_left this h).le, fun h => (pos_of_mul_pos_right this h).le⟩

@[simp]
/--
theorem `invOf_lt_zero` / 定理 `invOf_lt_zero`

English:
theorem invOf_lt_zero
  given: [Invertible a]
  statement: ⅟a < 0 ↔ a < 0
  proof: by simp only [← not_le, invOf_nonneg]

@[simp]

中文:
定理 invOf_lt_zero
  条件: [可逆 a]
  结论: ⅟a < 0 ↔ a < 0
  证明: by simp only [← not_le, invOf_nonneg]

@[simp]

Depends on / 依赖: invOf_nonneg, not_le
-/
theorem invOf_lt_zero [Invertible a] : ⅟a < 0 ↔ a < 0 := by simp only [← not_le, invOf_nonneg]

@[simp]
/--
theorem `invOf_le_one` / 定理 `invOf_le_one`

English:
theorem invOf_le_one
  given: [Invertible a] (h : 1 <= a)
  statement: ⅟a <= 1
  proof: mul_invOf_self a ▸ le_mul_of_one_le_left (invOf_nonneg.2 <| zero_le_one.trans h) h

@[simp]

中文:
定理 invOf_le_one
  条件: [可逆 a] (h : 1 <= a)
  结论: ⅟a <= 1
  证明: mul_invOf_self a ▸ le_mul_of_one_le_left (invOf_nonneg.2 <| zero_le_one.trans h) h

@[simp]

Depends on / 依赖: invOf_nonneg, le_mul_of_one_le_left, mul_invOf_self, zero_le_one, zero_le_one.trans
-/
theorem invOf_le_one [Invertible a] (h : 1 <= a) : ⅟a <= 1 :=
  mul_invOf_self a ▸ le_mul_of_one_le_left (invOf_nonneg.2 <| zero_le_one.trans h) h

@[simp]
/--
theorem `invOf_lt_one` / 定理 `invOf_lt_one`

English:
theorem invOf_lt_one
  given: [Invertible a] (h : 1 < a)
  statement: ⅟a < 1
  proof: mul_invOf_self a ▸ lt_mul_of_one_lt_left (invOf_pos.2 <| one_pos.trans h) h

中文:
定理 invOf_lt_one
  条件: [可逆 a] (h : 1 < a)
  结论: ⅟a < 1
  证明: mul_invOf_self a ▸ lt_mul_of_one_lt_left (invOf_pos.2 <| one_pos.trans h) h

Depends on / 依赖: invOf_pos, lt_mul_of_one_lt_left, mul_invOf_self, one_pos, one_pos.trans
-/
theorem invOf_lt_one [Invertible a] (h : 1 < a) : ⅟a < 1 :=
  mul_invOf_self a ▸ lt_mul_of_one_lt_left (invOf_pos.2 <| one_pos.trans h) h

/--
theorem `pos_invOf_of_invertible_cast` / 定理 `pos_invOf_of_invertible_cast`

English:
theorem pos_invOf_of_invertible_cast
  given: (n : Nat) [Invertible (n : R)]
  statement: 0 < ⅟(n : R)
  proof: invOf_pos.2 Nat.cast_pos.2 pos_of_invertible_cast (R := R) n

中文:
定理 pos_invOf_of_invertible_cast
  条件: (n : 自然数) [可逆 (n : R)]
  结论: 0 < ⅟(n : R)
  证明: invOf_pos.2 Nat.cast_pos.2 pos_of_invertible_cast (R := R) n

Depends on / 依赖: Nat.cast_pos, cast_pos, invOf_pos, pos_of_invertible_cast
-/
theorem pos_invOf_of_invertible_cast (n : Nat) [Invertible (n : R)] : 0 < ⅟(n : R) :=
invOf_pos.2 Nat.cast_pos.2 pos_of_invertible_cast (R := R) n
