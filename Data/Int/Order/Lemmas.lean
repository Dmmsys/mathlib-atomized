/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Further lemmas about the integers

The distinction between this file and `Mathlib/Data/Int/Order/Basic.lean` is not particularly clear.
They are separated by now to minimize the porting requirements for tactics during the transition to
mathlib4. Please feel free to reorganize these two files.
-/

public section

open Function Nat

namespace Int


/--
theorem `natAbs_eq_iff_mul_self_eq` / 定理 `natAbs_eq_iff_mul_self_eq`

English:
theorem natAbs_eq_iff_mul_self_eq
  given: {a b : Int}
  statement: a.natAbs = b.natAbs ↔ a * a = b * b
  proof: by
  rw [← abs_eq_iff_mul_self_eq]; rw [abs_eq_natAbs]; rw [abs_eq_natAbs]
  exact Int.natCast_inj.symm

中文:
定理 natAbs_eq_iff_mul_self_eq
  条件: {a b : 整数}
  结论: a.natAbs = b.natAbs ↔ a * a = b * b
  证明: by
  rw [← abs_eq_iff_mul_self_eq]; rw [abs_eq_natAbs]; rw [abs_eq_natAbs]
  exact Int.natCast_inj.symm

Depends on / 依赖: Int.natCast_inj.symm, abs_eq_iff_mul_self_eq, abs_eq_natAbs, natCast_inj
-/
theorem natAbs_eq_iff_mul_self_eq {a b : Int} : a.natAbs = b.natAbs ↔ a * a = b * b := by
  rw [← abs_eq_iff_mul_self_eq]; rw [abs_eq_natAbs]; rw [abs_eq_natAbs]
  exact Int.natCast_inj.symm

/--
theorem `natAbs_lt_iff_mul_self_lt` / 定理 `natAbs_lt_iff_mul_self_lt`

English:
theorem natAbs_lt_iff_mul_self_lt
  given: {a b : Int}
  statement: a.natAbs < b.natAbs ↔ a * a < b * b
  proof: by
  rw [← abs_lt_iff_mul_self_lt]; rw [abs_eq_natAbs]; rw [abs_eq_natAbs]
  exact Int.ofNat_lt.symm

中文:
定理 natAbs_lt_iff_mul_self_lt
  条件: {a b : 整数}
  结论: a.natAbs < b.natAbs ↔ a * a < b * b
  证明: by
  rw [← abs_lt_iff_mul_self_lt]; rw [abs_eq_natAbs]; rw [abs_eq_natAbs]
  exact Int.ofNat_lt.symm

Depends on / 依赖: Int.ofNat_lt.symm, abs_eq_natAbs, abs_lt_iff_mul_self_lt, ofNat_lt
-/
theorem natAbs_lt_iff_mul_self_lt {a b : Int} : a.natAbs < b.natAbs ↔ a * a < b * b := by
  rw [← abs_lt_iff_mul_self_lt]; rw [abs_eq_natAbs]; rw [abs_eq_natAbs]
  exact Int.ofNat_lt.symm

/--
theorem `natAbs_le_iff_mul_self_le` / 定理 `natAbs_le_iff_mul_self_le`

English:
theorem natAbs_le_iff_mul_self_le
  given: {a b : Int}
  statement: a.natAbs <= b.natAbs ↔ a * a <= b * b
  proof: by
  rw [← abs_le_iff_mul_self_le]; rw [abs_eq_natAbs]; rw [abs_eq_natAbs]
  exact Int.ofNat_le.symm

中文:
定理 natAbs_le_iff_mul_self_le
  条件: {a b : 整数}
  结论: a.natAbs <= b.natAbs ↔ a * a <= b * b
  证明: by
  rw [← abs_le_iff_mul_self_le]; rw [abs_eq_natAbs]; rw [abs_eq_natAbs]
  exact Int.ofNat_le.symm

Depends on / 依赖: Int.ofNat_le.symm, abs_eq_natAbs, abs_le_iff_mul_self_le, ofNat_le
-/
theorem natAbs_le_iff_mul_self_le {a b : Int} : a.natAbs <= b.natAbs ↔ a * a <= b * b := by
  rw [← abs_le_iff_mul_self_le]; rw [abs_eq_natAbs]; rw [abs_eq_natAbs]
  exact Int.ofNat_le.symm


/--
theorem `abs_le_sqrt` / 定理 `abs_le_sqrt`

English:
theorem abs_le_sqrt
  given: {a b : Int} (hn : 0 <= b)
  proof: by
  rw [← abs_mul_abs_self]; rw [eq_natCast_toNat.mpr hn]; rw [eq_natCast_toNat.mpr (abs_nonneg a)]; rw [Int.sqrt_natCast]; rw [← Int.natCast_mul]; rw [Nat.cast_le]; rw [Nat.cast_le]; rw [Nat.le_sqrt]

中文:
定理 abs_le_sqrt
  条件: {a b : 整数} (hn : 0 <= b)
  证明: by
  rw [← abs_mul_abs_self]; rw [eq_natCast_toNat.mpr hn]; rw [eq_natCast_toNat.mpr (abs_nonneg a)]; rw [Int.sqrt_natCast]; rw [← Int.natCast_mul]; rw [Nat.cast_le]; rw [Nat.cast_le]; rw [Nat.le_sqrt]

Depends on / 依赖: Int.natCast_mul, Int.sqrt_natCast, Nat.cast_le, Nat.le_sqrt, abs_mul_abs_self, abs_nonneg, cast_le, eq_natCast_toNat, eq_natCast_toNat.mpr, le_sqrt, natCast_mul, sqrt_natCast
-/
theorem abs_le_sqrt {a b : Int} (hn : 0 <= b) :
    |a| <= b.sqrt ↔ a * a <= b := by
  rw [← abs_mul_abs_self]; rw [eq_natCast_toNat.mpr hn]; rw [eq_natCast_toNat.mpr (abs_nonneg a)]; rw [Int.sqrt_natCast]; rw [← Int.natCast_mul]; rw [Nat.cast_le]; rw [Nat.cast_le]; rw [Nat.le_sqrt]

/--
theorem `abs_le_sqrt_iff_sq_le` / 定理 `abs_le_sqrt_iff_sq_le`

English:
theorem abs_le_sqrt_iff_sq_le
  given: {a b : Int} (hn : 0 <= b)
  proof: pow_two a ▸ abs_le_sqrt hn

中文:
定理 abs_le_sqrt_iff_sq_le
  条件: {a b : 整数} (hn : 0 <= b)
  证明: pow_two a ▸ abs_le_sqrt hn

Depends on / 依赖: abs_le_sqrt, pow_two
-/
theorem abs_le_sqrt_iff_sq_le {a b : Int} (hn : 0 <= b) :
    |a| <= b.sqrt ↔ a ^ 2 <= b :=
  pow_two a ▸ abs_le_sqrt hn

end Int
