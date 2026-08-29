/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Algebra.Order.GroupWithZero.Synonym

/-!
# Order properties of cast of integers

This file proves additional properties about the *canonical* homomorphism from
the integers into an additive group with a one (`Int.cast`),
particularly results involving algebraic homomorphisms or the order structure on `ℤ`
which were not available in the import dependencies of `Mathlib/Data/Int/Cast/Basic.lean`.

## TODO

Move order lemmas about `Nat.cast`, `Rat.cast`, `NNRat.cast` here.
-/

public section

open Function Nat

variable {R : Type*}

namespace Int
section OrderedAddCommGroupWithOne

variable [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R]
variable [ZeroLEOneClass R]

@[gcongr]
/--
lemma `cast_mono` / 引理 `cast_mono`

English:
lemma cast_mono
  statement: Monotone (Int.cast : Int -> R)
  proof: by
  intro m n h
  rw [← sub_nonneg] at h
  lift n - m to Nat using h with k hk
  rw [← sub_nonneg]; rw [← cast_sub]; rw [← hk]; rw [cast_natCast]
  exact k.cast_nonneg'

中文:
引理 cast_mono
  结论: 递增 (整数.cast : 整数 -> R)
  证明: by
  intro m n h
  rw [← sub_nonneg] at h
  lift n - m to Nat using h with k hk
  rw [← sub_nonneg]; rw [← cast_sub]; rw [← hk]; rw [cast_natCast]
  exact k.cast_nonneg'

Depends on / 依赖: cast_natCast, cast_nonneg, cast_sub, k.cast_nonneg, sub_nonneg
-/
lemma cast_mono : Monotone (Int.cast : Int -> R) := by
  intro m n h
  rw [← sub_nonneg] at h
  lift n - m to Nat using h with k hk
  rw [← sub_nonneg]; rw [← cast_sub]; rw [← hk]; rw [cast_natCast]
  exact k.cast_nonneg'

/--
lemma `cast_nonneg` / 引理 `cast_nonneg`

English:
lemma cast_nonneg
  statement: forall {n : Int}, 0 <= n -> (0 : R) <= n | (n : Nat), _ => by simp

中文:
引理 cast_nonneg
  结论: 对任意 {n : 整数}, 0 <= n -> (0 : R) <= n | (n : 自然数), _ => by simp
-/
@[simp] lemma cast_nonneg : forall {n : Int}, 0 <= n -> (0 : R) <= n | (n : Nat), _ => by simp

variable [NeZero (1 : R)] {m n : Int}

/--
lemma `cast_nonneg_iff` / 引理 `cast_nonneg_iff`

English:
lemma cast_nonneg_iff
  statement: forall {n : Int}, (0 : R) <= n ↔ 0 <= n
  proof: lt_of_le_of_lt (by simp) zero_lt_one
    simpa [(negSucc_lt_zero n).not_ge, ← sub_eq_add_neg, le_neg] using this.not_ge

中文:
引理 cast_nonneg_iff
  结论: 对任意 {n : 整数}, (0 : R) <= n ↔ 0 <= n
  证明: lt_of_le_of_lt (by simp) zero_lt_one
    simpa [(negSucc_lt_zero n).not_ge, ← sub_eq_add_neg, le_neg] using this.not_ge
-/
@[simp] lemma cast_nonneg_iff : forall {n : Int}, (0 : R) <= n ↔ 0 <= n
  | (n : Nat) => by simp
  | -[n+1] => by
    have : -(n : R) < 1 := lt_of_le_of_lt (by simp) zero_lt_one
    simpa [(negSucc_lt_zero n).not_ge, ← sub_eq_add_neg, le_neg] using this.not_ge

/--
lemma `cast_le` / 引理 `cast_le`

English:
lemma cast_le
  statement: (m : R) <= n ↔ m <= n
  proof: by
  rw [← sub_nonneg]; rw [← cast_sub]; rw [cast_nonneg_iff]; rw [sub_nonneg]

中文:
引理 cast_le
  结论: (m : R) <= n ↔ m <= n
  证明: by
  rw [← sub_nonneg]; rw [← cast_sub]; rw [cast_nonneg_iff]; rw [sub_nonneg]
-/
@[simp, norm_cast] lemma cast_le : (m : R) <= n ↔ m <= n := by
  rw [← sub_nonneg]; rw [← cast_sub]; rw [cast_nonneg_iff]; rw [sub_nonneg]

/--
lemma `cast_strictMono` / 引理 `cast_strictMono`

English:
lemma cast_strictMono
  statement: StrictMono (fun x : Int => (x : R))
  proof: strictMono_of_le_iff_le fun _ _ => cast_le.symm

中文:
引理 cast_strictMono
  结论: 严格递增 (fun x : 整数 => (x : R))
  证明: strictMono_of_le_iff_le fun _ _ => cast_le.symm

Depends on / 依赖: cast_le, cast_le.symm, strictMono_of_le_iff_le
-/
lemma cast_strictMono : StrictMono (fun x : Int => (x : R)) :=
  strictMono_of_le_iff_le fun _ _ => cast_le.symm

/--
lemma `cast_lt` / 引理 `cast_lt`

English:
lemma cast_lt
  statement: (m : R) < n ↔ m < n
  proof: cast_strictMono.lt_iff_lt

中文:
引理 cast_lt
  结论: (m : R) < n ↔ m < n
  证明: cast_strictMono.lt_iff_lt
-/
@[simp, norm_cast, gcongr] lemma cast_lt : (m : R) < n ↔ m < n := cast_strictMono.lt_iff_lt

/--
lemma `cast_nonpos` / 引理 `cast_nonpos`

English:
lemma cast_nonpos
  statement: (n : R) <= 0 ↔ n <= 0
  proof: by rw [← cast_zero, cast_le]

中文:
引理 cast_nonpos
  结论: (n : R) <= 0 ↔ n <= 0
  证明: by rw [← cast_zero, cast_le]
-/
@[simp] lemma cast_nonpos : (n : R) <= 0 ↔ n <= 0 := by rw [← cast_zero, cast_le]

/--
lemma `cast_pos` / 引理 `cast_pos`

English:
lemma cast_pos
  statement: (0 : R) < n ↔ 0 < n
  proof: by rw [← cast_zero, cast_lt]

中文:
引理 cast_pos
  结论: (0 : R) < n ↔ 0 < n
  证明: by rw [← cast_zero, cast_lt]
-/
@[simp] lemma cast_pos : (0 : R) < n ↔ 0 < n := by rw [← cast_zero, cast_lt]

/--
lemma `cast_lt_zero` / 引理 `cast_lt_zero`

English:
lemma cast_lt_zero
  statement: (n : R) < 0 ↔ n < 0
  proof: by rw [← cast_zero, cast_lt]

中文:
引理 cast_lt_zero
  结论: (n : R) < 0 ↔ n < 0
  证明: by rw [← cast_zero, cast_lt]
-/
@[simp] lemma cast_lt_zero : (n : R) < 0 ↔ n < 0 := by rw [← cast_zero, cast_lt]

end OrderedAddCommGroupWithOne

section LinearOrderedRing
variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a b n : Int} {x : R}

@[simp, norm_cast]
/--
lemma `cast_min` / 引理 `cast_min`

English:
lemma cast_min
  statement: ↑(min a b) = (min a b : R)
  proof: Monotone.map_min cast_mono

@[simp, norm_cast]

中文:
引理 cast_min
  结论: ↑(最小值 a b) = (最小值 a b : R)
  证明: Monotone.map_min cast_mono

@[simp, norm_cast]

Depends on / 依赖: Monotone, Monotone.map_min, cast_mono, map_min
-/
lemma cast_min : ↑(min a b) = (min a b : R) := Monotone.map_min cast_mono

@[simp, norm_cast]
/--
lemma `cast_max` / 引理 `cast_max`

English:
lemma cast_max
  statement: (↑(max a b) : R) = max (a : R) (b : R)
  proof: Monotone.map_max cast_mono

@[simp, norm_cast]

中文:
引理 cast_max
  结论: (↑(最大值 a b) : R) = 最大值 (a : R) (b : R)
  证明: Monotone.map_max cast_mono

@[simp, norm_cast]

Depends on / 依赖: Monotone, Monotone.map_max, cast_mono, map_max
-/
lemma cast_max : (↑(max a b) : R) = max (a : R) (b : R) := Monotone.map_max cast_mono

@[simp, norm_cast]
/--
lemma `cast_abs` / 引理 `cast_abs`

English:
lemma cast_abs
  statement: (↑|a| : R) = |(a : R)|
  proof: by simp [abs_eq_max_neg]

中文:
引理 cast_abs
  结论: (↑|a| : R) = |(a : R)|
  证明: by simp [abs_eq_max_neg]

Depends on / 依赖: abs_eq_max_neg
-/
lemma cast_abs : (↑|a| : R) = |(a : R)| := by simp [abs_eq_max_neg]

/--
lemma `cast_one_le_of_pos` / 引理 `cast_one_le_of_pos`

English:
lemma cast_one_le_of_pos
  given: (h : 0 < a)
  statement: (1 : R) <= a
  proof: mod_cast Int.add_one_le_of_lt h

中文:
引理 cast_one_le_of_pos
  条件: (h : 0 < a)
  结论: (1 : R) <= a
  证明: mod_cast Int.add_one_le_of_lt h

Depends on / 依赖: Int.add_one_le_of_lt, add_one_le_of_lt, mod_cast
-/
lemma cast_one_le_of_pos (h : 0 < a) : (1 : R) <= a := mod_cast Int.add_one_le_of_lt h

/--
lemma `cast_le_neg_one_of_neg` / 引理 `cast_le_neg_one_of_neg`

English:
lemma cast_le_neg_one_of_neg
  given: (h : a < 0)
  statement: (a : R) <= -1
  proof: by
  rw [← Int.cast_one]; rw [← Int.cast_neg]; rw [cast_le]
  exact Int.le_sub_one_of_lt h

中文:
引理 cast_le_neg_one_of_neg
  条件: (h : a < 0)
  结论: (a : R) <= -1
  证明: by
  rw [← Int.cast_one]; rw [← Int.cast_neg]; rw [cast_le]
  exact Int.le_sub_one_of_lt h

Depends on / 依赖: Int.cast_neg, Int.cast_one, Int.le_sub_one_of_lt, cast_le, cast_neg, cast_one, le_sub_one_of_lt
-/
lemma cast_le_neg_one_of_neg (h : a < 0) : (a : R) <= -1 := by
  rw [← Int.cast_one]; rw [← Int.cast_neg]; rw [cast_le]
  exact Int.le_sub_one_of_lt h

variable (R) in
/--
lemma `cast_le_neg_one_or_one_le_cast_of_ne_zero` / 引理 `cast_le_neg_one_or_one_le_cast_of_ne_zero`

English:
lemma cast_le_neg_one_or_one_le_cast_of_ne_zero
  given: (hn : n != 0)
  statement: (n : R) <= -1 ∨ 1 <= (n : R)
  proof: hn.lt_or_gt.imp cast_le_neg_one_of_neg cast_one_le_of_pos

中文:
引理 cast_le_neg_one_or_one_le_cast_of_ne_zero
  条件: (hn : n != 0)
  结论: (n : R) <= -1 ∨ 1 <= (n : R)
  证明: hn.lt_or_gt.imp cast_le_neg_one_of_neg cast_one_le_of_pos

Depends on / 依赖: cast_le_neg_one_of_neg, cast_one_le_of_pos, hn.lt_or_gt.imp, lt_or_gt
-/
lemma cast_le_neg_one_or_one_le_cast_of_ne_zero (hn : n != 0) : (n : R) <= -1 ∨ 1 <= (n : R) :=
  hn.lt_or_gt.imp cast_le_neg_one_of_neg cast_one_le_of_pos

/--
lemma `nneg_mul_add_sq_of_abs_le_one` / 引理 `nneg_mul_add_sq_of_abs_le_one`

English:
lemma nneg_mul_add_sq_of_abs_le_one
  given: (n : Int) (hx : |x| <= 1)
  statement: (0 : R) <= n * x + n * n
  proof: by
  have hnx : 0 < n -> 0 <= x + n := fun hn => by
    have := _root_.add_le_add (neg_le_of_abs_le hx) (cast_one_le_of_pos hn)
    rwa [neg_add_cancel] at this
  have hnx' : n < 0 -> x + n <= 0 := fun hn => by
    have := _root_.add_le_add (le_of_abs_le hx) (cast_le_neg_one_of_neg hn)
    rwa [add_neg_cancel] at this
  rw [← mul_add]; rw [mul_nonneg_iff]
  rcases lt_trichotomy n 0 with (h | rfl | h)
  · exact Or.inr ⟨mod_cast h.le, hnx' h⟩
  · simp [le_total 0 x]
  · exact Or.inl ⟨mod_cast h.le, hnx h⟩

中文:
引理 nneg_mul_add_sq_of_abs_le_one
  条件: (n : 整数) (hx : |x| <= 1)
  结论: (0 : R) <= n * x + n * n
  证明: by
  have hnx : 0 < n -> 0 <= x + n := fun hn => by
    have := _root_.add_le_add (neg_le_of_abs_le hx) (cast_one_le_of_pos hn)
    rwa [neg_add_cancel] at this
  have hnx' : n < 0 -> x + n <= 0 := fun hn => by
    have := _root_.add_le_add (le_of_abs_le hx) (cast_le_neg_one_of_neg hn)
    rwa [add_neg_cancel] at this
  rw [← mul_add]; rw [mul_nonneg_iff]
  rcases lt_trichotomy n 0 with (h | rfl | h)
  · exact Or.inr ⟨mod_cast h.le, hnx' h⟩
  · simp [le_total 0 x]
  · exact Or.inl ⟨mod_cast h.le, hnx h⟩

Depends on / 依赖: Or.inl, Or.inr, _root_, _root_.add_le_add, add_le_add, add_neg_cancel, cast_le_neg_one_of_neg, cast_one_le_of_pos, h.le, le_of_abs_le, le_total, lt_trichotomy, mod_cast, mul_add, mul_nonneg_iff, neg_add_cancel, neg_le_of_abs_le
-/
lemma nneg_mul_add_sq_of_abs_le_one (n : Int) (hx : |x| <= 1) : (0 : R) <= n * x + n * n := by
  have hnx : 0 < n -> 0 <= x + n := fun hn => by
    have := _root_.add_le_add (neg_le_of_abs_le hx) (cast_one_le_of_pos hn)
    rwa [neg_add_cancel] at this
  have hnx' : n < 0 -> x + n <= 0 := fun hn => by
    have := _root_.add_le_add (le_of_abs_le hx) (cast_le_neg_one_of_neg hn)
    rwa [add_neg_cancel] at this
  rw [← mul_add]; rw [mul_nonneg_iff]
  rcases lt_trichotomy n 0 with (h | rfl | h)
  · exact Or.inr ⟨mod_cast h.le, hnx' h⟩
  · simp [le_total 0 x]
  · exact Or.inl ⟨mod_cast h.le, hnx h⟩

end LinearOrderedRing
end Int
