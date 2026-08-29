/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.Tauto

/-!
# Basic facts for ordered rings and semirings

This file develops the basics of ordered (semi)rings in an unbundled fashion for later use with
the bundled classes from `Mathlib/Algebra/Order/Ring/Defs.lean`.

## Generality

Each section is labelled with a corresponding bundled ordered ring typeclass in mind. Mixins for
relating the order structures and ring structures are added as needed.

## TODO

The mixin assumptions can be relaxed in most cases.
-/

public section

assert_not_exists IsOrderedMonoid MonoidHom

open Function

universe u

variable {R : Type u} {α : Type*}



/--
theorem `add_one_le_two_mul` / 定理 `add_one_le_two_mul`

English:
theorem add_one_le_two_mul
  statement: [LE R] [NonAssocSemiring R] [AddLeftMono R] {a : R}
  proof: calc
    a + 1 <= a + a := by gcongr
    _ = 2 * a := (two_mul _).symm

中文:
定理 add_one_le_two_mul
  结论: [LE R] [非结合半环 R] [AddLeftMono R] {a : R}
  证明: calc
    a + 1 <= a + a := by gcongr
    _ = 2 * a := (two_mul _).symm

Depends on / 依赖: two_mul
-/
theorem add_one_le_two_mul [LE R] [NonAssocSemiring R] [AddLeftMono R] {a : R}
    (a1 : 1 <= a) : a + 1 <= 2 * a :=
  calc
    a + 1 <= a + a := by gcongr
    _ = 2 * a := (two_mul _).symm

section OrderedSemiring

variable [Semiring R] [Preorder R] {a b c d : R}

/--
theorem `add_le_mul_two_add` / 定理 `add_le_mul_two_add`

English:
theorem add_le_mul_two_add
  statement: [ZeroLEOneClass R] [MulPosMono R] [AddLeftMono R]
  proof: calc
    a + (2 + b) <= a + (a + a * b) := by
gcongr; exact le_mul_of_one_le_left b0 one_le_two.trans a2
    _ <= a * (2 + b) := by rw [mul_add, mul_two, add_assoc]

中文:
定理 add_le_mul_two_add
  结论: [ZeroLEOne类 R] [乘正递增 R] [AddLeftMono R]
  证明: calc
    a + (2 + b) <= a + (a + a * b) := by
gcongr; exact le_mul_of_one_le_left b0 one_le_two.trans a2
    _ <= a * (2 + b) := by rw [mul_add, mul_two, add_assoc]

Depends on / 依赖: add_assoc, le_mul_of_one_le_left, mul_add, mul_two, one_le_two, one_le_two.trans
-/
theorem add_le_mul_two_add [ZeroLEOneClass R] [MulPosMono R] [AddLeftMono R]
    (a2 : 2 <= a) (b0 : 0 <= b) : a + (2 + b) <= a * (2 + b) :=
  calc
    a + (2 + b) <= a + (a + a * b) := by
gcongr; exact le_mul_of_one_le_left b0 one_le_two.trans a2
    _ <= a * (2 + b) := by rw [mul_add, mul_two, add_assoc]

/--
theorem `mul_le_mul_of_nonpos_left` / 定理 `mul_le_mul_of_nonpos_left`

English:
theorem mul_le_mul_of_nonpos_left
  statement: [ExistsAddOfLE R] [PosMulMono R]
  proof: by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := d * b + d * a) ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
_ <= d * a := by gcongr; exact hcd.trans_le add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

中文:
定理 mul_le_mul_of_nonpos_left
  结论: [ExistsAddOfLE R] [正乘递增 R]
  证明: by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := d * b + d * a) ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
_ <= d * a := by gcongr; exact hcd.trans_le add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

Depends on / 依赖: add_assoc, add_le_of_nonpos_left, add_left_comm, add_mul, add_zero, exists_add_of_le, hcd.trans_le, le_of_add_le_add_right, trans_le, zero_add, zero_mul
-/
theorem mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : b <= a) (hc : c <= 0) : c * a <= c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := d * b + d * a) ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
_ <= d * a := by gcongr; exact hcd.trans_le add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

/--
theorem `mul_le_mul_of_nonpos_right` / 定理 `mul_le_mul_of_nonpos_right`

English:
theorem mul_le_mul_of_nonpos_right
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := b * d + a * d) ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
_ <= a * d := by gcongr; exact hcd.trans_le add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

中文:
定理 mul_le_mul_of_nonpos_right
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := b * d + a * d) ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
_ <= a * d := by gcongr; exact hcd.trans_le add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

Depends on / 依赖: add_assoc, add_le_of_nonpos_left, add_left_comm, add_zero, exists_add_of_le, hcd.trans_le, le_of_add_le_add_right, mul_add, mul_zero, trans_le, zero_add
-/
theorem mul_le_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : b <= a) (hc : c <= 0) : a * c <= b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := b * d + a * d) ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
_ <= a * d := by gcongr; exact hcd.trans_le add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

/--
theorem `mul_nonneg_of_nonpos_of_nonpos` / 定理 `mul_nonneg_of_nonpos_of_nonpos`

English:
theorem mul_nonneg_of_nonpos_of_nonpos
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: by
  simpa only [zero_mul] using mul_le_mul_of_nonpos_right ha hb

中文:
定理 mul_nonneg_of_nonpos_of_nonpos
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: by
  simpa only [zero_mul] using mul_le_mul_of_nonpos_right ha hb

Depends on / 依赖: mul_le_mul_of_nonpos_right, zero_mul
-/
theorem mul_nonneg_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a <= 0) (hb : b <= 0) : 0 <= a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonpos_right ha hb

/--
theorem `mul_le_mul_of_nonneg_of_nonpos` / 定理 `mul_le_mul_of_nonneg_of_nonpos`

English:
theorem mul_le_mul_of_nonneg_of_nonpos
  statement: [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
  proof: (mul_le_mul_of_nonpos_right hca hb).trans by gcongr; assumption

中文:
定理 mul_le_mul_of_nonneg_of_nonpos
  结论: [ExistsAddOfLE R] [乘正递增 R] [正乘递增 R]
  证明: (mul_le_mul_of_nonpos_right hca hb).trans by gcongr; assumption

Depends on / 依赖: mul_le_mul_of_nonpos_right
-/
theorem mul_le_mul_of_nonneg_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c <= a) (hbd : b <= d) (hc : 0 <= c) (hb : b <= 0) : a * b <= c * d :=
(mul_le_mul_of_nonpos_right hca hb).trans by gcongr; assumption

/--
theorem `mul_le_mul_of_nonneg_of_nonpos'` / 定理 `mul_le_mul_of_nonneg_of_nonpos'`

English:
theorem mul_le_mul_of_nonneg_of_nonpos'
  statement: [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
  proof: (mul_le_mul_of_nonneg_left hbd ha).trans mul_le_mul_of_nonpos_right hca hd

中文:
定理 mul_le_mul_of_nonneg_of_nonpos'
  结论: [ExistsAddOfLE R] [正乘递增 R] [乘正递增 R]
  证明: (mul_le_mul_of_nonneg_left hbd ha).trans mul_le_mul_of_nonpos_right hca hd

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_le_mul_of_nonpos_right
-/
theorem mul_le_mul_of_nonneg_of_nonpos' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c <= a) (hbd : b <= d) (ha : 0 <= a) (hd : d <= 0) : a * b <= c * d :=
(mul_le_mul_of_nonneg_left hbd ha).trans mul_le_mul_of_nonpos_right hca hd

/--
theorem `mul_le_mul_of_nonpos_of_nonneg` / 定理 `mul_le_mul_of_nonpos_of_nonneg`

English:
theorem mul_le_mul_of_nonpos_of_nonneg
  statement: [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
  proof: (mul_le_mul_of_nonneg_right hac hb).trans mul_le_mul_of_nonpos_left hdb hc

中文:
定理 mul_le_mul_of_nonpos_of_nonneg
  结论: [ExistsAddOfLE R] [乘正递增 R] [正乘递增 R]
  证明: (mul_le_mul_of_nonneg_right hac hb).trans mul_le_mul_of_nonpos_left hdb hc

Depends on / 依赖: mul_le_mul_of_nonneg_right, mul_le_mul_of_nonpos_left
-/
theorem mul_le_mul_of_nonpos_of_nonneg [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hac : a <= c) (hdb : d <= b) (hc : c <= 0) (hb : 0 <= b) : a * b <= c * d :=
(mul_le_mul_of_nonneg_right hac hb).trans mul_le_mul_of_nonpos_left hdb hc

/--
theorem `mul_le_mul_of_nonpos_of_nonneg'` / 定理 `mul_le_mul_of_nonpos_of_nonneg'`

English:
theorem mul_le_mul_of_nonpos_of_nonneg'
  statement: [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
  proof: (mul_le_mul_of_nonneg_left hbd ha).trans mul_le_mul_of_nonpos_right hca hd

中文:
定理 mul_le_mul_of_nonpos_of_nonneg'
  结论: [ExistsAddOfLE R] [正乘递增 R] [乘正递增 R]
  证明: (mul_le_mul_of_nonneg_left hbd ha).trans mul_le_mul_of_nonpos_right hca hd

Depends on / 依赖: mul_le_mul_of_nonneg_left, mul_le_mul_of_nonpos_right
-/
theorem mul_le_mul_of_nonpos_of_nonneg' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c <= a) (hbd : b <= d) (ha : 0 <= a) (hd : d <= 0) : a * b <= c * d :=
(mul_le_mul_of_nonneg_left hbd ha).trans mul_le_mul_of_nonpos_right hca hd

/--
theorem `mul_le_mul_of_nonpos_of_nonpos` / 定理 `mul_le_mul_of_nonpos_of_nonpos`

English:
theorem mul_le_mul_of_nonpos_of_nonpos
  statement: [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
  proof: (mul_le_mul_of_nonpos_right hca hb).trans mul_le_mul_of_nonpos_left hdb hc

中文:
定理 mul_le_mul_of_nonpos_of_nonpos
  结论: [ExistsAddOfLE R] [乘正递增 R] [正乘递增 R]
  证明: (mul_le_mul_of_nonpos_right hca hb).trans mul_le_mul_of_nonpos_left hdb hc

Depends on / 依赖: mul_le_mul_of_nonpos_left, mul_le_mul_of_nonpos_right
-/
theorem mul_le_mul_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c <= a) (hdb : d <= b) (hc : c <= 0) (hb : b <= 0) : a * b <= c * d :=
(mul_le_mul_of_nonpos_right hca hb).trans mul_le_mul_of_nonpos_left hdb hc

/--
theorem `mul_le_mul_of_nonpos_of_nonpos'` / 定理 `mul_le_mul_of_nonpos_of_nonpos'`

English:
theorem mul_le_mul_of_nonpos_of_nonpos'
  statement: [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
  proof: (mul_le_mul_of_nonpos_left hdb ha).trans mul_le_mul_of_nonpos_right hca hd

中文:
定理 mul_le_mul_of_nonpos_of_nonpos'
  结论: [ExistsAddOfLE R] [正乘递增 R] [乘正递增 R]
  证明: (mul_le_mul_of_nonpos_left hdb ha).trans mul_le_mul_of_nonpos_right hca hd

Depends on / 依赖: mul_le_mul_of_nonpos_left, mul_le_mul_of_nonpos_right
-/
theorem mul_le_mul_of_nonpos_of_nonpos' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c <= a) (hdb : d <= b) (ha : a <= 0) (hd : d <= 0) : a * b <= c * d :=
(mul_le_mul_of_nonpos_left hdb ha).trans mul_le_mul_of_nonpos_right hca hd

/--
theorem `le_mul_of_le_one_left` / 定理 `le_mul_of_le_one_left`

English:
theorem le_mul_of_le_one_left
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

中文:
定理 le_mul_of_le_one_left
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

Depends on / 依赖: mul_le_mul_of_nonpos_right, one_mul
-/
theorem le_mul_of_le_one_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hb : b <= 0) (h : a <= 1) : b <= a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

/--
theorem `mul_le_of_one_le_left` / 定理 `mul_le_of_one_le_left`

English:
theorem mul_le_of_one_le_left
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

中文:
定理 mul_le_of_one_le_left
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

Depends on / 依赖: mul_le_mul_of_nonpos_right, one_mul
-/
theorem mul_le_of_one_le_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hb : b <= 0) (h : 1 <= a) : a * b <= b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

/--
theorem `le_mul_of_le_one_right` / 定理 `le_mul_of_le_one_right`

English:
theorem le_mul_of_le_one_right
  statement: [ExistsAddOfLE R] [PosMulMono R]
  proof: by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

中文:
定理 le_mul_of_le_one_right
  结论: [ExistsAddOfLE R] [正乘递增 R]
  证明: by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

Depends on / 依赖: mul_le_mul_of_nonpos_left, mul_one
-/
theorem le_mul_of_le_one_right [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a <= 0) (h : b <= 1) : a <= a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

/--
theorem `mul_le_of_one_le_right` / 定理 `mul_le_of_one_le_right`

English:
theorem mul_le_of_one_le_right
  statement: [ExistsAddOfLE R] [PosMulMono R]
  proof: by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

中文:
定理 mul_le_of_one_le_right
  结论: [ExistsAddOfLE R] [正乘递增 R]
  证明: by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

Depends on / 依赖: mul_le_mul_of_nonpos_left, mul_one
-/
theorem mul_le_of_one_le_right [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a <= 0) (h : 1 <= b) : a * b <= a := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

section Monotone

variable [Preorder α] {f g : α -> R}

/--
theorem `antitone_mul_left` / 定理 `antitone_mul_left`

English:
theorem antitone_mul_left
  statement: [ExistsAddOfLE R] [PosMulMono R]
  proof: fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_left b_le_c ha

中文:
定理 antitone_mul_left
  结论: [ExistsAddOfLE R] [正乘递增 R]
  证明: fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_left b_le_c ha

Depends on / 依赖: b_le_c
-/
theorem antitone_mul_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a : R} (ha : a <= 0) : Antitone (a * ·) := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_left b_le_c ha

/--
theorem `antitone_mul_right` / 定理 `antitone_mul_right`

English:
theorem antitone_mul_right
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_right b_le_c ha

中文:
定理 antitone_mul_right
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_right b_le_c ha

Depends on / 依赖: b_le_c
-/
theorem antitone_mul_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a : R} (ha : a <= 0) : Antitone fun x => x * a := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_right b_le_c ha

/--
theorem `Monotone.const_mul_of_nonpos` / 定理 `Monotone.const_mul_of_nonpos`

English:
theorem Monotone.const_mul_of_nonpos
  statement: [ExistsAddOfLE R] [PosMulMono R]
  proof: (antitone_mul_left ha).comp_monotone hf

中文:
定理 递增.const_mul_of_nonpos
  结论: [ExistsAddOfLE R] [正乘递增 R]
  证明: (antitone_mul_left ha).comp_monotone hf

Depends on / 依赖: antitone_mul_left, comp_monotone
-/
theorem Monotone.const_mul_of_nonpos [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (ha : a <= 0) : Antitone fun x => a * f x :=
  (antitone_mul_left ha).comp_monotone hf

/--
theorem `Monotone.mul_const_of_nonpos` / 定理 `Monotone.mul_const_of_nonpos`

English:
theorem Monotone.mul_const_of_nonpos
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: (antitone_mul_right ha).comp_monotone hf

中文:
定理 递增.mul_const_of_nonpos
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: (antitone_mul_right ha).comp_monotone hf

Depends on / 依赖: antitone_mul_right, comp_monotone
-/
theorem Monotone.mul_const_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (ha : a <= 0) : Antitone fun x => f x * a :=
  (antitone_mul_right ha).comp_monotone hf

/--
theorem `Antitone.const_mul_of_nonpos` / 定理 `Antitone.const_mul_of_nonpos`

English:
theorem Antitone.const_mul_of_nonpos
  statement: [ExistsAddOfLE R] [PosMulMono R]
  proof: (antitone_mul_left ha).comp hf

中文:
定理 递减.const_mul_of_nonpos
  结论: [ExistsAddOfLE R] [正乘递增 R]
  证明: (antitone_mul_left ha).comp hf

Depends on / 依赖: antitone_mul_left
-/
theorem Antitone.const_mul_of_nonpos [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (ha : a <= 0) : Monotone fun x => a * f x :=
  (antitone_mul_left ha).comp hf

/--
theorem `Antitone.mul_const_of_nonpos` / 定理 `Antitone.mul_const_of_nonpos`

English:
theorem Antitone.mul_const_of_nonpos
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: (antitone_mul_right ha).comp hf

中文:
定理 递减.mul_const_of_nonpos
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: (antitone_mul_right ha).comp hf

Depends on / 依赖: antitone_mul_right
-/
theorem Antitone.mul_const_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (ha : a <= 0) : Monotone fun x => f x * a :=
  (antitone_mul_right ha).comp hf

/--
theorem `Antitone.mul_monotone` / 定理 `Antitone.mul_monotone`

English:
theorem Antitone.mul_monotone
  statement: [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
  proof: fun _ _ h =>
  mul_le_mul_of_nonpos_of_nonneg (hf h) (hg h) (hf₀ _) (hg₀ _)

中文:
定理 递减.mul_monotone
  结论: [ExistsAddOfLE R] [正乘递增 R] [乘正递增 R]
  证明: fun _ _ h =>
  mul_le_mul_of_nonpos_of_nonneg (hf h) (hg h) (hf₀ _) (hg₀ _)
-/
theorem Antitone.mul_monotone [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (hg : Monotone g) (hf₀ : forall x, f x <= 0)
    (hg₀ : forall x, 0 <= g x) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonpos_of_nonneg (hf h) (hg h) (hf₀ _) (hg₀ _)

/--
theorem `Monotone.mul_antitone` / 定理 `Monotone.mul_antitone`

English:
theorem Monotone.mul_antitone
  statement: [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
  proof: fun _ _ h =>
  mul_le_mul_of_nonneg_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

中文:
定理 递增.mul_antitone
  结论: [ExistsAddOfLE R] [正乘递增 R] [乘正递增 R]
  证明: fun _ _ h =>
  mul_le_mul_of_nonneg_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)
-/
theorem Monotone.mul_antitone [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (hg : Antitone g) (hf₀ : forall x, 0 <= f x)
    (hg₀ : forall x, g x <= 0) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonneg_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

/--
theorem `Antitone.mul` / 定理 `Antitone.mul`

English:
theorem Antitone.mul
  statement: [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
  proof: fun _ _ h => mul_le_mul_of_nonpos_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

中文:
定理 递减.mul
  结论: [ExistsAddOfLE R] [正乘递增 R] [乘正递增 R]
  证明: fun _ _ h => mul_le_mul_of_nonpos_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

Depends on / 依赖: mul_le_mul_of_nonpos_of_nonpos
-/
theorem Antitone.mul [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (hg : Antitone g) (hf₀ : forall x, f x <= 0) (hg₀ : forall x, g x <= 0) :
    Monotone (f * g) := fun _ _ h => mul_le_mul_of_nonpos_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

end Monotone
end OrderedSemiring

section OrderedCommRing

section StrictOrderedSemiring

variable [Semiring R] [PartialOrder R] {a b c d : R}

/--
theorem `lt_two_mul_self` / 定理 `lt_two_mul_self`

English:
theorem lt_two_mul_self
  statement: [ZeroLEOneClass R] [MulPosStrictMono R] [NeZero (1 : R)]
  proof: lt_mul_of_one_lt_left ha one_lt_two

中文:
定理 lt_two_mul_self
  结论: [ZeroLEOne类 R] [乘正严格递增 R] [NeZero (1 : R)]
  证明: lt_mul_of_one_lt_left ha one_lt_two

Depends on / 依赖: lt_mul_of_one_lt_left, one_lt_two
-/
theorem lt_two_mul_self [ZeroLEOneClass R] [MulPosStrictMono R] [NeZero (1 : R)]
    [AddLeftStrictMono R] (ha : 0 < a) : a < 2 * a :=
  lt_mul_of_one_lt_left ha one_lt_two

/--
theorem `mul_lt_mul_of_neg_left` / 定理 `mul_lt_mul_of_neg_left`

English:
theorem mul_lt_mul_of_neg_left
  statement: [ExistsAddOfLE R] [PosMulStrictMono R]
  proof: by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (d * b + d * a)).1 ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
_ < d * a := mul_lt_mul_of_pos_left h hcd.trans_lt add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

中文:
定理 mul_lt_mul_of_neg_left
  结论: [ExistsAddOfLE R] [正乘严格递增 R]
  证明: by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (d * b + d * a)).1 ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
_ < d * a := mul_lt_mul_of_pos_left h hcd.trans_lt add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

Depends on / 依赖: add_assoc, add_left_comm, add_lt_add_iff_right, add_lt_of_neg_left, add_mul, add_zero, exists_add_of_le, hc.le, hcd.trans_lt, mul_lt_mul_of_pos_left, trans_lt, zero_add, zero_mul
-/
theorem mul_lt_mul_of_neg_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (h : b < a) (hc : c < 0) : c * a < c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (d * b + d * a)).1 ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
_ < d * a := mul_lt_mul_of_pos_left h hcd.trans_lt add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]

/--
theorem `mul_lt_mul_of_neg_right` / 定理 `mul_lt_mul_of_neg_right`

English:
theorem mul_lt_mul_of_neg_right
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (b * d + a * d)).1 ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
_ < a * d := mul_lt_mul_of_pos_right h hcd.trans_lt add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

中文:
定理 mul_lt_mul_of_neg_right
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (b * d + a * d)).1 ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
_ < a * d := mul_lt_mul_of_pos_right h hcd.trans_lt add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

Depends on / 依赖: add_assoc, add_left_comm, add_lt_add_iff_right, add_lt_of_neg_left, add_zero, exists_add_of_le, hc.le, hcd.trans_lt, mul_add, mul_lt_mul_of_pos_right, mul_zero, trans_lt, zero_add
-/
theorem mul_lt_mul_of_neg_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (h : b < a) (hc : c < 0) : a * c < b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (b * d + a * d)).1 ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
_ < a * d := mul_lt_mul_of_pos_right h hcd.trans_lt add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]

/--
theorem `mul_pos_of_neg_of_neg` / 定理 `mul_pos_of_neg_of_neg`

English:
theorem mul_pos_of_neg_of_neg
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: by
  simpa only [zero_mul] using mul_lt_mul_of_neg_right ha hb

中文:
定理 mul_pos_of_neg_of_neg
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: by
  simpa only [zero_mul] using mul_lt_mul_of_neg_right ha hb

Depends on / 依赖: mul_lt_mul_of_neg_right, zero_mul
-/
theorem mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b : R} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_neg_right ha hb

/--
theorem `lt_mul_of_lt_one_left` / 定理 `lt_mul_of_lt_one_left`

English:
theorem lt_mul_of_lt_one_left
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

中文:
定理 lt_mul_of_lt_one_left
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

Depends on / 依赖: mul_lt_mul_of_neg_right, one_mul
-/
theorem lt_mul_of_lt_one_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hb : b < 0) (h : a < 1) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

/--
theorem `mul_lt_of_one_lt_left` / 定理 `mul_lt_of_one_lt_left`

English:
theorem mul_lt_of_one_lt_left
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

中文:
定理 mul_lt_of_one_lt_left
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

Depends on / 依赖: mul_lt_mul_of_neg_right, one_mul
-/
theorem mul_lt_of_one_lt_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hb : b < 0) (h : 1 < a) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

/--
theorem `lt_mul_of_lt_one_right` / 定理 `lt_mul_of_lt_one_right`

English:
theorem lt_mul_of_lt_one_right
  statement: [ExistsAddOfLE R] [PosMulStrictMono R]
  proof: by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

中文:
定理 lt_mul_of_lt_one_right
  结论: [ExistsAddOfLE R] [正乘严格递增 R]
  证明: by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

Depends on / 依赖: mul_lt_mul_of_neg_left, mul_one
-/
theorem lt_mul_of_lt_one_right [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (ha : a < 0) (h : b < 1) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

/--
theorem `mul_lt_of_one_lt_right` / 定理 `mul_lt_of_one_lt_right`

English:
theorem mul_lt_of_one_lt_right
  statement: [ExistsAddOfLE R] [PosMulStrictMono R]
  proof: by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

中文:
定理 mul_lt_of_one_lt_right
  结论: [ExistsAddOfLE R] [正乘严格递增 R]
  证明: by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

Depends on / 依赖: mul_lt_mul_of_neg_left, mul_one
-/
theorem mul_lt_of_one_lt_right [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (ha : a < 0) (h : 1 < b) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

section Monotone

variable [Preorder α] {f : α -> R}

/--
theorem `strictAnti_mul_left` / 定理 `strictAnti_mul_left`

English:
theorem strictAnti_mul_left
  statement: [ExistsAddOfLE R] [PosMulStrictMono R]
  proof: fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_left b_lt_c ha

中文:
定理 strictAnti_mul_left
  结论: [ExistsAddOfLE R] [正乘严格递增 R]
  证明: fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_left b_lt_c ha

Depends on / 依赖: b_lt_c
-/
theorem strictAnti_mul_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a : R} (ha : a < 0) : StrictAnti (a * ·) := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_left b_lt_c ha

/--
theorem `strictAnti_mul_right` / 定理 `strictAnti_mul_right`

English:
theorem strictAnti_mul_right
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_right b_lt_c ha

中文:
定理 strictAnti_mul_right
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_right b_lt_c ha

Depends on / 依赖: b_lt_c
-/
theorem strictAnti_mul_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a : R} (ha : a < 0) : StrictAnti fun x => x * a := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_right b_lt_c ha

/--
theorem `StrictMono.const_mul_of_neg` / 定理 `StrictMono.const_mul_of_neg`

English:
theorem StrictMono.const_mul_of_neg
  statement: [ExistsAddOfLE R] [PosMulStrictMono R]
  proof: (strictAnti_mul_left ha).comp_strictMono hf

中文:
定理 严格递增.const_mul_of_neg
  结论: [ExistsAddOfLE R] [正乘严格递增 R]
  证明: (strictAnti_mul_left ha).comp_strictMono hf

Depends on / 依赖: comp_strictMono, strictAnti_mul_left
-/
theorem StrictMono.const_mul_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => a * f x :=
  (strictAnti_mul_left ha).comp_strictMono hf

/--
theorem `StrictMono.mul_const_of_neg` / 定理 `StrictMono.mul_const_of_neg`

English:
theorem StrictMono.mul_const_of_neg
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: (strictAnti_mul_right ha).comp_strictMono hf

中文:
定理 严格递增.mul_const_of_neg
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: (strictAnti_mul_right ha).comp_strictMono hf

Depends on / 依赖: comp_strictMono, strictAnti_mul_right
-/
theorem StrictMono.mul_const_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => f x * a :=
  (strictAnti_mul_right ha).comp_strictMono hf

/--
theorem `StrictAnti.const_mul_of_neg` / 定理 `StrictAnti.const_mul_of_neg`

English:
theorem StrictAnti.const_mul_of_neg
  statement: [ExistsAddOfLE R] [PosMulStrictMono R]
  proof: (strictAnti_mul_left ha).comp hf

中文:
定理 严格递减.const_mul_of_neg
  结论: [ExistsAddOfLE R] [正乘严格递增 R]
  证明: (strictAnti_mul_left ha).comp hf

Depends on / 依赖: strictAnti_mul_left
-/
theorem StrictAnti.const_mul_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictAnti f) (ha : a < 0) : StrictMono fun x => a * f x :=
  (strictAnti_mul_left ha).comp hf

/--
theorem `StrictAnti.mul_const_of_neg` / 定理 `StrictAnti.mul_const_of_neg`

English:
theorem StrictAnti.mul_const_of_neg
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: (strictAnti_mul_right ha).comp hf

中文:
定理 严格递减.mul_const_of_neg
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: (strictAnti_mul_right ha).comp hf

Depends on / 依赖: strictAnti_mul_right
-/
theorem StrictAnti.mul_const_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictAnti f) (ha : a < 0) : StrictMono fun x => f x * a :=
  (strictAnti_mul_right ha).comp hf

end Monotone

/--
lemma `mul_add_mul_le_mul_add_mul` / 引理 `mul_add_mul_le_mul_add_mul`

English:
lemma mul_add_mul_le_mul_add_mul
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: by
  obtain ⟨d, hd, rfl⟩ := exists_nonneg_add_of_le hcd
  rw [mul_add]; rw [add_right_comm]; rw [mul_add]; rw [← add_assoc]
  gcongr
  assumption

中文:
引理 mul_add_mul_le_mul_add_mul
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: by
  obtain ⟨d, hd, rfl⟩ := exists_nonneg_add_of_le hcd
  rw [mul_add]; rw [add_right_comm]; rw [mul_add]; rw [← add_assoc]
  gcongr
  assumption

Depends on / 依赖: add_assoc, add_right_comm, exists_nonneg_add_of_le, mul_add
-/
lemma mul_add_mul_le_mul_add_mul [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (hab : a <= b) (hcd : c <= d) : a * d + b * c <= a * c + b * d := by
  obtain ⟨d, hd, rfl⟩ := exists_nonneg_add_of_le hcd
  rw [mul_add]; rw [add_right_comm]; rw [mul_add]; rw [← add_assoc]
  gcongr
  assumption

/--
lemma `mul_add_mul_le_mul_add_mul'` / 引理 `mul_add_mul_le_mul_add_mul'`

English:
lemma mul_add_mul_le_mul_add_mul'
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: by
  rw [add_comm (a * d)]; rw [add_comm (a * c)]; exact mul_add_mul_le_mul_add_mul hba hdc

中文:
引理 mul_add_mul_le_mul_add_mul'
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: by
  rw [add_comm (a * d)]; rw [add_comm (a * c)]; exact mul_add_mul_le_mul_add_mul hba hdc

Depends on / 依赖: add_comm, mul_add_mul_le_mul_add_mul
-/
lemma mul_add_mul_le_mul_add_mul' [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (hba : b <= a) (hdc : d <= c) : a * d + b * c <= a * c + b * d := by
  rw [add_comm (a * d)]; rw [add_comm (a * c)]; exact mul_add_mul_le_mul_add_mul hba hdc

variable [AddLeftReflectLT R]

/--
lemma `mul_add_mul_lt_mul_add_mul` / 引理 `mul_add_mul_lt_mul_add_mul`

English:
lemma mul_add_mul_lt_mul_add_mul
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: by
  obtain ⟨d, hd, rfl⟩ := exists_pos_add_of_lt' hcd
  rw [mul_add]; rw [add_right_comm]; rw [mul_add]; rw [← add_assoc]
  gcongr
  exact hd

中文:
引理 mul_add_mul_lt_mul_add_mul
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: by
  obtain ⟨d, hd, rfl⟩ := exists_pos_add_of_lt' hcd
  rw [mul_add]; rw [add_right_comm]; rw [mul_add]; rw [← add_assoc]
  gcongr
  exact hd

Depends on / 依赖: add_assoc, add_right_comm, exists_pos_add_of_lt, mul_add
-/
lemma mul_add_mul_lt_mul_add_mul [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftStrictMono R]
    (hab : a < b) (hcd : c < d) : a * d + b * c < a * c + b * d := by
  obtain ⟨d, hd, rfl⟩ := exists_pos_add_of_lt' hcd
  rw [mul_add]; rw [add_right_comm]; rw [mul_add]; rw [← add_assoc]
  gcongr
  exact hd

/--
lemma `mul_add_mul_lt_mul_add_mul'` / 引理 `mul_add_mul_lt_mul_add_mul'`

English:
lemma mul_add_mul_lt_mul_add_mul'
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: by
  rw [add_comm (a * d)]; rw [add_comm (a * c)]
  exact mul_add_mul_lt_mul_add_mul hba hdc

中文:
引理 mul_add_mul_lt_mul_add_mul'
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: by
  rw [add_comm (a * d)]; rw [add_comm (a * c)]
  exact mul_add_mul_lt_mul_add_mul hba hdc

Depends on / 依赖: add_comm, mul_add_mul_lt_mul_add_mul
-/
lemma mul_add_mul_lt_mul_add_mul' [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftStrictMono R]
    (hba : b < a) (hdc : d < c) : a * d + b * c < a * c + b * d := by
  rw [add_comm (a * d)]; rw [add_comm (a * c)]
  exact mul_add_mul_lt_mul_add_mul hba hdc

end StrictOrderedSemiring

section LinearOrderedSemiring

variable [Semiring R] [LinearOrder R] {a b c : R}

/--
theorem `nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg` / 定理 `nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg`

English:
theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg
  proof: by
  refine Decidable.or_iff_not_not_and_not.2 ?_
  simp only [not_and, not_le]; intro ab nab; apply not_lt_of_ge hab _
  rcases lt_trichotomy 0 a with (ha | rfl | ha)
  · exact mul_neg_of_pos_of_neg ha (ab ha.le)
  · exact ((ab le_rfl).asymm (nab le_rfl)).elim
  · exact mul_neg_of_neg_of_pos ha (nab ha.le)

中文:
定理 nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg
  证明: by
  refine Decidable.or_iff_not_not_and_not.2 ?_
  simp only [not_and, not_le]; intro ab nab; apply not_lt_of_ge hab _
  rcases lt_trichotomy 0 a with (ha | rfl | ha)
  · exact mul_neg_of_pos_of_neg ha (ab ha.le)
  · exact ((ab le_rfl).asymm (nab le_rfl)).elim
  · exact mul_neg_of_neg_of_pos ha (nab ha.le)

Depends on / 依赖: Decidable, Decidable.or_iff_not_not_and_not, ha.le, le_rfl, lt_trichotomy, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg, not_and, not_le, not_lt_of_ge, or_iff_not_not_and_not
-/
theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg
    [MulPosStrictMono R] [PosMulStrictMono R]
    (hab : 0 <= a * b) : 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 := by
  refine Decidable.or_iff_not_not_and_not.2 ?_
  simp only [not_and, not_le]; intro ab nab; apply not_lt_of_ge hab _
  rcases lt_trichotomy 0 a with (ha | rfl | ha)
  · exact mul_neg_of_pos_of_neg ha (ab ha.le)
  · exact ((ab le_rfl).asymm (nab le_rfl)).elim
  · exact mul_neg_of_neg_of_pos ha (nab ha.le)

/--
theorem `nonneg_of_mul_nonneg_left` / 定理 `nonneg_of_mul_nonneg_left`

English:
theorem nonneg_of_mul_nonneg_left
  statement: [MulPosStrictMono R]
  proof: le_of_not_gt fun ha => (mul_neg_of_neg_of_pos ha hb).not_ge h

中文:
定理 nonneg_of_mul_nonneg_left
  结论: [乘正严格递增 R]
  证明: le_of_not_gt fun ha => (mul_neg_of_neg_of_pos ha hb).not_ge h

Depends on / 依赖: le_of_not_gt, mul_neg_of_neg_of_pos, not_ge
-/
theorem nonneg_of_mul_nonneg_left [MulPosStrictMono R]
    (h : 0 <= a * b) (hb : 0 < b) : 0 <= a :=
  le_of_not_gt fun ha => (mul_neg_of_neg_of_pos ha hb).not_ge h

/--
theorem `nonneg_of_mul_nonneg_right` / 定理 `nonneg_of_mul_nonneg_right`

English:
theorem nonneg_of_mul_nonneg_right
  statement: [PosMulStrictMono R]
  proof: le_of_not_gt fun hb => (mul_neg_of_pos_of_neg ha hb).not_ge h

中文:
定理 nonneg_of_mul_nonneg_right
  结论: [正乘严格递增 R]
  证明: le_of_not_gt fun hb => (mul_neg_of_pos_of_neg ha hb).not_ge h

Depends on / 依赖: le_of_not_gt, mul_neg_of_pos_of_neg, not_ge
-/
theorem nonneg_of_mul_nonneg_right [PosMulStrictMono R]
    (h : 0 <= a * b) (ha : 0 < a) : 0 <= b :=
  le_of_not_gt fun hb => (mul_neg_of_pos_of_neg ha hb).not_ge h

/--
theorem `nonpos_of_mul_nonpos_left` / 定理 `nonpos_of_mul_nonpos_left`

English:
theorem nonpos_of_mul_nonpos_left
  statement: [PosMulStrictMono R]
  proof: le_of_not_gt fun ha : a > 0 => (mul_pos ha hb).not_ge h

中文:
定理 nonpos_of_mul_nonpos_left
  结论: [正乘严格递增 R]
  证明: le_of_not_gt fun ha : a > 0 => (mul_pos ha hb).not_ge h

Depends on / 依赖: le_of_not_gt, mul_pos, not_ge
-/
theorem nonpos_of_mul_nonpos_left [PosMulStrictMono R]
    (h : a * b <= 0) (hb : 0 < b) : a <= 0 :=
  le_of_not_gt fun ha : a > 0 => (mul_pos ha hb).not_ge h

/--
theorem `nonpos_of_mul_nonpos_right` / 定理 `nonpos_of_mul_nonpos_right`

English:
theorem nonpos_of_mul_nonpos_right
  statement: [PosMulStrictMono R]
  proof: le_of_not_gt fun hb : b > 0 => (mul_pos ha hb).not_ge h

@[simp]

中文:
定理 nonpos_of_mul_nonpos_right
  结论: [正乘严格递增 R]
  证明: le_of_not_gt fun hb : b > 0 => (mul_pos ha hb).not_ge h

@[simp]

Depends on / 依赖: le_of_not_gt, mul_pos, not_ge
-/
theorem nonpos_of_mul_nonpos_right [PosMulStrictMono R]
    (h : a * b <= 0) (ha : 0 < a) : b <= 0 :=
  le_of_not_gt fun hb : b > 0 => (mul_pos ha hb).not_ge h

@[simp]
/--
theorem `mul_nonneg_iff_of_pos_left` / 定理 `mul_nonneg_iff_of_pos_left`

English:
theorem mul_nonneg_iff_of_pos_left
  statement: [PosMulStrictMono R]
  proof: by
  convert! mul_le_mul_iff_right₀ h
  simp

@[simp]

中文:
定理 mul_nonneg_iff_of_pos_left
  结论: [正乘严格递增 R]
  证明: by
  convert! mul_le_mul_iff_right₀ h
  simp

@[simp]

Depends on / 依赖: convert
-/
theorem mul_nonneg_iff_of_pos_left [PosMulStrictMono R]
    (h : 0 < c) : 0 <= c * b ↔ 0 <= b := by
  convert! mul_le_mul_iff_right₀ h
  simp

@[simp]
/--
theorem `mul_nonneg_iff_of_pos_right` / 定理 `mul_nonneg_iff_of_pos_right`

English:
theorem mul_nonneg_iff_of_pos_right
  statement: [MulPosStrictMono R]
  proof: by
  simpa using (mul_le_mul_iff_left₀ h : 0 * c <= b * c ↔ 0 <= b)

中文:
定理 mul_nonneg_iff_of_pos_right
  结论: [乘正严格递增 R]
  证明: by
  simpa using (mul_le_mul_iff_left₀ h : 0 * c <= b * c ↔ 0 <= b)
-/
theorem mul_nonneg_iff_of_pos_right [MulPosStrictMono R]
    (h : 0 < c) : 0 <= b * c ↔ 0 <= b := by
  simpa using (mul_le_mul_iff_left₀ h : 0 * c <= b * c ↔ 0 <= b)

/--
theorem `add_le_mul_of_left_le_right` / 定理 `add_le_mul_of_left_le_right`

English:
theorem add_le_mul_of_left_le_right
  statement: [ZeroLEOneClass R] [NeZero (1 : R)]
  proof: have : 0 < b :=
    calc
      0 < 2 := zero_lt_two
      _ <= a := a2
      _ <= b := ab
  calc
    a + b <= b + b := by gcongr
    _ = 2 * b := (two_mul b).symm
    _ <= a * b := (mul_le_mul_iff_left₀ this).mpr a2

中文:
定理 add_le_mul_of_left_le_right
  结论: [ZeroLEOne类 R] [NeZero (1 : R)]
  证明: have : 0 < b :=
    calc
      0 < 2 := zero_lt_two
      _ <= a := a2
      _ <= b := ab
  calc
    a + b <= b + b := by gcongr
    _ = 2 * b := (two_mul b).symm
    _ <= a * b := (mul_le_mul_iff_left₀ this).mpr a2

Depends on / 依赖: two_mul, zero_lt_two
-/
theorem add_le_mul_of_left_le_right [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [AddLeftMono R]
    (a2 : 2 <= a) (ab : a <= b) : a + b <= a * b :=
  have : 0 < b :=
    calc
      0 < 2 := zero_lt_two
      _ <= a := a2
      _ <= b := ab
  calc
    a + b <= b + b := by gcongr
    _ = 2 * b := (two_mul b).symm
    _ <= a * b := (mul_le_mul_iff_left₀ this).mpr a2

/--
theorem `add_le_mul_of_right_le_left` / 定理 `add_le_mul_of_right_le_left`

English:
theorem add_le_mul_of_right_le_left
  statement: [ZeroLEOneClass R] [NeZero (1 : R)]
  proof: have : 0 < a :=
    calc 0
      _ < 2 := zero_lt_two
      _ <= b := b2
      _ <= a := ba
  calc
    a + b <= a + a := by gcongr
    _ = a * 2 := (mul_two a).symm
    _ <= a * b := (mul_le_mul_iff_right₀ this).mpr b2

中文:
定理 add_le_mul_of_right_le_left
  结论: [ZeroLEOne类 R] [NeZero (1 : R)]
  证明: have : 0 < a :=
    calc 0
      _ < 2 := zero_lt_two
      _ <= b := b2
      _ <= a := ba
  calc
    a + b <= a + a := by gcongr
    _ = a * 2 := (mul_two a).symm
    _ <= a * b := (mul_le_mul_iff_right₀ this).mpr b2

Depends on / 依赖: mul_two, zero_lt_two
-/
theorem add_le_mul_of_right_le_left [ZeroLEOneClass R] [NeZero (1 : R)]
    [AddLeftMono R] [PosMulStrictMono R]
    (b2 : 2 <= b) (ba : b <= a) : a + b <= a * b :=
  have : 0 < a :=
    calc 0
      _ < 2 := zero_lt_two
      _ <= b := b2
      _ <= a := ba
  calc
    a + b <= a + a := by gcongr
    _ = a * 2 := (mul_two a).symm
    _ <= a * b := (mul_le_mul_iff_right₀ this).mpr b2

/--
theorem `add_le_mul` / 定理 `add_le_mul`

English:
theorem add_le_mul
  statement: [ZeroLEOneClass R] [NeZero (1 : R)]
  proof: if hab : a <= b then add_le_mul_of_left_le_right a2 hab
  else add_le_mul_of_right_le_left b2 (le_of_not_ge hab)

中文:
定理 add_le_mul
  结论: [ZeroLEOne类 R] [NeZero (1 : R)]
  证明: if hab : a <= b then add_le_mul_of_left_le_right a2 hab
  else add_le_mul_of_right_le_left b2 (le_of_not_ge hab)

Depends on / 依赖: add_le_mul_of_left_le_right, add_le_mul_of_right_le_left, le_of_not_ge
-/
theorem add_le_mul [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (a2 : 2 <= a) (b2 : 2 <= b) : a + b <= a * b :=
  if hab : a <= b then add_le_mul_of_left_le_right a2 hab
  else add_le_mul_of_right_le_left b2 (le_of_not_ge hab)

/--
theorem `add_le_mul'` / 定理 `add_le_mul'`

English:
theorem add_le_mul'
  statement: [ZeroLEOneClass R] [NeZero (1 : R)]
  proof: (le_of_eq (add_comm _ _)).trans (add_le_mul b2 a2)

中文:
定理 add_le_mul'
  结论: [ZeroLEOne类 R] [NeZero (1 : R)]
  证明: (le_of_eq (add_comm _ _)).trans (add_le_mul b2 a2)

Depends on / 依赖: add_comm, add_le_mul, le_of_eq
-/
theorem add_le_mul' [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (a2 : 2 <= a) (b2 : 2 <= b) : a + b <= b * a :=
  (le_of_eq (add_comm _ _)).trans (add_le_mul b2 a2)

/--
theorem `mul_nonneg_iff_right_nonneg_of_pos` / 定理 `mul_nonneg_iff_right_nonneg_of_pos`

English:
theorem mul_nonneg_iff_right_nonneg_of_pos
  statement: [PosMulStrictMono R]
  proof: ⟨fun h => nonneg_of_mul_nonneg_right h ha, mul_nonneg ha.le⟩

中文:
定理 mul_nonneg_iff_right_nonneg_of_pos
  结论: [正乘严格递增 R]
  证明: ⟨fun h => nonneg_of_mul_nonneg_right h ha, mul_nonneg ha.le⟩

Depends on / 依赖: ha.le, mul_nonneg, nonneg_of_mul_nonneg_right
-/
theorem mul_nonneg_iff_right_nonneg_of_pos [PosMulStrictMono R]
    (ha : 0 < a) : 0 <= a * b ↔ 0 <= b :=
  ⟨fun h => nonneg_of_mul_nonneg_right h ha, mul_nonneg ha.le⟩

/--
theorem `mul_nonneg_iff_left_nonneg_of_pos` / 定理 `mul_nonneg_iff_left_nonneg_of_pos`

English:
theorem mul_nonneg_iff_left_nonneg_of_pos
  statement: [PosMulStrictMono R] [MulPosStrictMono R]
  proof: ⟨fun h => nonneg_of_mul_nonneg_left h hb, fun h => mul_nonneg h hb.le⟩

中文:
定理 mul_nonneg_iff_left_nonneg_of_pos
  结论: [正乘严格递增 R] [乘正严格递增 R]
  证明: ⟨fun h => nonneg_of_mul_nonneg_left h hb, fun h => mul_nonneg h hb.le⟩

Depends on / 依赖: hb.le, mul_nonneg, nonneg_of_mul_nonneg_left
-/
theorem mul_nonneg_iff_left_nonneg_of_pos [PosMulStrictMono R] [MulPosStrictMono R]
    (hb : 0 < b) : 0 <= a * b ↔ 0 <= a :=
  ⟨fun h => nonneg_of_mul_nonneg_left h hb, fun h => mul_nonneg h hb.le⟩

/--
theorem `nonpos_of_mul_nonneg_left` / 定理 `nonpos_of_mul_nonneg_left`

English:
theorem nonpos_of_mul_nonneg_left
  statement: [PosMulStrictMono R]
  proof: le_of_not_gt fun ha => absurd h (mul_neg_of_pos_of_neg ha hb).not_ge

中文:
定理 nonpos_of_mul_nonneg_left
  结论: [正乘严格递增 R]
  证明: le_of_not_gt fun ha => absurd h (mul_neg_of_pos_of_neg ha hb).not_ge

Depends on / 依赖: absurd, le_of_not_gt, mul_neg_of_pos_of_neg, not_ge
-/
theorem nonpos_of_mul_nonneg_left [PosMulStrictMono R]
    (h : 0 <= a * b) (hb : b < 0) : a <= 0 :=
  le_of_not_gt fun ha => absurd h (mul_neg_of_pos_of_neg ha hb).not_ge

/--
theorem `nonpos_of_mul_nonneg_right` / 定理 `nonpos_of_mul_nonneg_right`

English:
theorem nonpos_of_mul_nonneg_right
  statement: [MulPosStrictMono R]
  proof: le_of_not_gt fun hb => absurd h (mul_neg_of_neg_of_pos ha hb).not_ge

@[simp]

中文:
定理 nonpos_of_mul_nonneg_right
  结论: [乘正严格递增 R]
  证明: le_of_not_gt fun hb => absurd h (mul_neg_of_neg_of_pos ha hb).not_ge

@[simp]

Depends on / 依赖: absurd, le_of_not_gt, mul_neg_of_neg_of_pos, not_ge
-/
theorem nonpos_of_mul_nonneg_right [MulPosStrictMono R]
    (h : 0 <= a * b) (ha : a < 0) : b <= 0 :=
  le_of_not_gt fun hb => absurd h (mul_neg_of_neg_of_pos ha hb).not_ge

@[simp]
/--
theorem `Units.inv_pos` / 定理 `Units.inv_pos`

English:
theorem Units.inv_pos
  proof: have : forall {u : Rˣ}, (0 : R) < u -> (0 : R) < ↑u⁻¹ := @fun u h =>
(mul_pos_iff_of_pos_left h).mp u.mul_inv.symm ▸ zero_lt_one
  ⟨this, this⟩

@[simp]

中文:
定理 单位群.inv_pos
  证明: have : forall {u : Rˣ}, (0 : R) < u -> (0 : R) < ↑u⁻¹ := @fun u h =>
(mul_pos_iff_of_pos_left h).mp u.mul_inv.symm ▸ zero_lt_one
  ⟨this, this⟩

@[simp]

Depends on / 依赖: mul_inv, mul_pos_iff_of_pos_left, u.mul_inv.symm, zero_lt_one
-/
theorem Units.inv_pos
    [ZeroLEOneClass R] [NeZero (1 : R)] [PosMulStrictMono R]
    {u : Rˣ} : (0 : R) < ↑u⁻¹ ↔ (0 : R) < u :=
  have : forall {u : Rˣ}, (0 : R) < u -> (0 : R) < ↑u⁻¹ := @fun u h =>
(mul_pos_iff_of_pos_left h).mp u.mul_inv.symm ▸ zero_lt_one
  ⟨this, this⟩

@[simp]
/--
theorem `Units.inv_neg` / 定理 `Units.inv_neg`

English:
theorem Units.inv_neg
  proof: have : forall {u : Rˣ}, ↑u < (0 : R) -> ↑u⁻¹ < (0 : R) := @fun u h =>
    neg_of_mul_pos_right (u.mul_inv.symm ▸ zero_lt_one) h.le
  ⟨this, this⟩

中文:
定理 单位群.inv_neg
  证明: have : forall {u : Rˣ}, ↑u < (0 : R) -> ↑u⁻¹ < (0 : R) := @fun u h =>
    neg_of_mul_pos_right (u.mul_inv.symm ▸ zero_lt_one) h.le
  ⟨this, this⟩

Depends on / 依赖: h.le, mul_inv, neg_of_mul_pos_right, u.mul_inv.symm, zero_lt_one
-/
theorem Units.inv_neg
    [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosMono R] [PosMulMono R]
    {u : Rˣ} : ↑u⁻¹ < (0 : R) ↔ ↑u < (0 : R) :=
  have : forall {u : Rˣ}, ↑u < (0 : R) -> ↑u⁻¹ < (0 : R) := @fun u h =>
    neg_of_mul_pos_right (u.mul_inv.symm ▸ zero_lt_one) h.le
  ⟨this, this⟩

/--
theorem `cmp_mul_pos_left` / 定理 `cmp_mul_pos_left`

English:
theorem cmp_mul_pos_left
  statement: [PosMulStrictMono R]
  proof: (strictMono_mul_left_of_pos ha).cmp_map_eq b c

中文:
定理 cmp_mul_pos_left
  结论: [正乘严格递增 R]
  证明: (strictMono_mul_left_of_pos ha).cmp_map_eq b c

Depends on / 依赖: cmp_map_eq, strictMono_mul_left_of_pos
-/
theorem cmp_mul_pos_left [PosMulStrictMono R]
    (ha : 0 < a) (b c : R) : cmp (a * b) (a * c) = cmp b c :=
  (strictMono_mul_left_of_pos ha).cmp_map_eq b c

/--
theorem `cmp_mul_pos_right` / 定理 `cmp_mul_pos_right`

English:
theorem cmp_mul_pos_right
  statement: [MulPosStrictMono R]
  proof: (strictMono_mul_right_of_pos ha).cmp_map_eq b c

中文:
定理 cmp_mul_pos_right
  结论: [乘正严格递增 R]
  证明: (strictMono_mul_right_of_pos ha).cmp_map_eq b c

Depends on / 依赖: cmp_map_eq, strictMono_mul_right_of_pos
-/
theorem cmp_mul_pos_right [MulPosStrictMono R]
    (ha : 0 < a) (b c : R) : cmp (b * a) (c * a) = cmp b c :=
  (strictMono_mul_right_of_pos ha).cmp_map_eq b c

/--
theorem `mul_max_of_nonneg` / 定理 `mul_max_of_nonneg`

English:
theorem mul_max_of_nonneg
  statement: [PosMulMono R]
  proof: (monotone_mul_left_of_nonneg ha).map_max

中文:
定理 mul_max_of_nonneg
  结论: [正乘递增 R]
  证明: (monotone_mul_left_of_nonneg ha).map_max

Depends on / 依赖: map_max, monotone_mul_left_of_nonneg
-/
theorem mul_max_of_nonneg [PosMulMono R]
    (b c : R) (ha : 0 <= a) : a * max b c = max (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_max

/--
theorem `mul_min_of_nonneg` / 定理 `mul_min_of_nonneg`

English:
theorem mul_min_of_nonneg
  statement: [PosMulMono R]
  proof: (monotone_mul_left_of_nonneg ha).map_min

中文:
定理 mul_min_of_nonneg
  结论: [正乘递增 R]
  证明: (monotone_mul_left_of_nonneg ha).map_min

Depends on / 依赖: map_min, monotone_mul_left_of_nonneg
-/
theorem mul_min_of_nonneg [PosMulMono R]
    (b c : R) (ha : 0 <= a) : a * min b c = min (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_min

/--
theorem `max_mul_of_nonneg` / 定理 `max_mul_of_nonneg`

English:
theorem max_mul_of_nonneg
  statement: [MulPosMono R]
  proof: (monotone_mul_right_of_nonneg hc).map_max

中文:
定理 max_mul_of_nonneg
  结论: [乘正递增 R]
  证明: (monotone_mul_right_of_nonneg hc).map_max

Depends on / 依赖: map_max, monotone_mul_right_of_nonneg
-/
theorem max_mul_of_nonneg [MulPosMono R]
    (a b : R) (hc : 0 <= c) : max a b * c = max (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_max

/--
theorem `min_mul_of_nonneg` / 定理 `min_mul_of_nonneg`

English:
theorem min_mul_of_nonneg
  statement: [MulPosMono R]
  proof: (monotone_mul_right_of_nonneg hc).map_min

中文:
定理 min_mul_of_nonneg
  结论: [乘正递增 R]
  证明: (monotone_mul_right_of_nonneg hc).map_min

Depends on / 依赖: map_min, monotone_mul_right_of_nonneg
-/
theorem min_mul_of_nonneg [MulPosMono R]
    (a b : R) (hc : 0 <= c) : min a b * c = min (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_min

/--
theorem `le_of_mul_le_of_one_le` / 定理 `le_of_mul_le_of_one_le`

English:
theorem le_of_mul_le_of_one_le
  proof: le_of_mul_le_mul_right (h.trans <| le_mul_of_one_le_right hb hc) zero_lt_one.trans_le hc

中文:
定理 le_of_mul_le_of_one_le
  证明: le_of_mul_le_mul_right (h.trans <| le_mul_of_one_le_right hb hc) zero_lt_one.trans_le hc

Depends on / 依赖: h.trans, le_mul_of_one_le_right, le_of_mul_le_mul_right, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem le_of_mul_le_of_one_le
    [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosStrictMono R] [PosMulMono R]
    {a b c : R} (h : a * c <= b) (hb : 0 <= b) (hc : 1 <= c) : a <= b :=
le_of_mul_le_mul_right (h.trans <| le_mul_of_one_le_right hb hc) zero_lt_one.trans_le hc

/--
theorem `nonneg_le_nonneg_of_sq_le_sq` / 定理 `nonneg_le_nonneg_of_sq_le_sq`

English:
theorem nonneg_le_nonneg_of_sq_le_sq
  statement: [PosMulStrictMono R] [MulPosMono R]
  proof: le_of_not_gt fun hab => (mul_self_lt_mul_self hb hab).not_ge h

中文:
定理 nonneg_le_nonneg_of_sq_le_sq
  结论: [正乘严格递增 R] [乘正递增 R]
  证明: le_of_not_gt fun hab => (mul_self_lt_mul_self hb hab).not_ge h

Depends on / 依赖: le_of_not_gt, mul_self_lt_mul_self, not_ge
-/
theorem nonneg_le_nonneg_of_sq_le_sq [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (hb : 0 <= b) (h : a * a <= b * b) : a <= b :=
  le_of_not_gt fun hab => (mul_self_lt_mul_self hb hab).not_ge h

/--
theorem `mul_self_le_mul_self_iff` / 定理 `mul_self_le_mul_self_iff`

English:
theorem mul_self_le_mul_self_iff
  statement: [PosMulStrictMono R] [MulPosMono R]
  proof: ⟨mul_self_le_mul_self h1, nonneg_le_nonneg_of_sq_le_sq h2⟩

中文:
定理 mul_self_le_mul_self_iff
  结论: [正乘严格递增 R] [乘正递增 R]
  证明: ⟨mul_self_le_mul_self h1, nonneg_le_nonneg_of_sq_le_sq h2⟩

Depends on / 依赖: mul_self_le_mul_self, nonneg_le_nonneg_of_sq_le_sq
-/
theorem mul_self_le_mul_self_iff [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 <= a) (h2 : 0 <= b) : a <= b ↔ a * a <= b * b :=
  ⟨mul_self_le_mul_self h1, nonneg_le_nonneg_of_sq_le_sq h2⟩

/--
theorem `mul_self_lt_mul_self_iff` / 定理 `mul_self_lt_mul_self_iff`

English:
theorem mul_self_lt_mul_self_iff
  statement: [PosMulStrictMono R] [MulPosMono R]
  proof: ((@strictMonoOn_mul_self R _).lt_iff_lt h1 h2).symm

中文:
定理 mul_self_lt_mul_self_iff
  结论: [正乘严格递增 R] [乘正递增 R]
  证明: ((@strictMonoOn_mul_self R _).lt_iff_lt h1 h2).symm

Depends on / 依赖: lt_iff_lt, strictMonoOn_mul_self
-/
theorem mul_self_lt_mul_self_iff [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 <= a) (h2 : 0 <= b) : a < b ↔ a * a < b * b :=
  ((@strictMonoOn_mul_self R _).lt_iff_lt h1 h2).symm

/--
theorem `mul_self_inj` / 定理 `mul_self_inj`

English:
theorem mul_self_inj
  statement: [PosMulStrictMono R] [MulPosMono R]
  proof: (@strictMonoOn_mul_self R _).eq_iff_eq h1 h2

中文:
定理 mul_self_inj
  结论: [正乘严格递增 R] [乘正递增 R]
  证明: (@strictMonoOn_mul_self R _).eq_iff_eq h1 h2

Depends on / 依赖: eq_iff_eq, strictMonoOn_mul_self
-/
theorem mul_self_inj [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 <= a) (h2 : 0 <= b) : a * a = b * b ↔ a = b :=
  (@strictMonoOn_mul_self R _).eq_iff_eq h1 h2

/--
lemma `sign_cases_of_C_mul_pow_nonneg` / 引理 `sign_cases_of_C_mul_pow_nonneg`

English:
lemma sign_cases_of_C_mul_pow_nonneg
  statement: [PosMulStrictMono R]
  proof: by
  have : 0 <= a := by simpa only [pow_zero, mul_one] using h 0
  refine this.eq_or_lt'.imp_right fun ha => ⟨ha, nonneg_of_mul_nonneg_right ?_ ha⟩
  simpa only [pow_one] using h 1

中文:
引理 sign_cases_of_C_mul_pow_nonneg
  结论: [正乘严格递增 R]
  证明: by
  have : 0 <= a := by simpa only [pow_zero, mul_one] using h 0
  refine this.eq_or_lt'.imp_right fun ha => ⟨ha, nonneg_of_mul_nonneg_right ?_ ha⟩
  simpa only [pow_one] using h 1

Depends on / 依赖: eq_or_lt, imp_right, mul_one, nonneg_of_mul_nonneg_right, pow_one, pow_zero, this.eq_or_lt
-/
lemma sign_cases_of_C_mul_pow_nonneg [PosMulStrictMono R]
    (h : forall n, 0 <= a * b ^ n) : a = 0 ∨ 0 < a ∧ 0 <= b := by
  have : 0 <= a := by simpa only [pow_zero, mul_one] using h 0
  refine this.eq_or_lt'.imp_right fun ha => ⟨ha, nonneg_of_mul_nonneg_right ?_ ha⟩
  simpa only [pow_one] using h 1

/--
theorem `mul_pos_iff` / 定理 `mul_pos_iff`

English:
theorem mul_pos_iff
  statement: [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
  proof: ⟨pos_and_pos_or_neg_and_neg_of_mul_pos, fun h =>
    h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩

中文:
定理 mul_pos_iff
  结论: [ExistsAddOfLE R] [正乘严格递增 R] [乘正严格递增 R]
  证明: ⟨pos_and_pos_or_neg_and_neg_of_mul_pos, fun h =>
    h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩

Depends on / 依赖: and_imp, h.elim, mul_pos, mul_pos_of_neg_of_neg, pos_and_pos_or_neg_and_neg_of_mul_pos
-/
theorem mul_pos_iff [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftStrictMono R] [AddLeftReflectLT R] :
    0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
  ⟨pos_and_pos_or_neg_and_neg_of_mul_pos, fun h =>
    h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩

/--
theorem `mul_nonneg_iff` / 定理 `mul_nonneg_iff`

English:
theorem mul_nonneg_iff
  statement: [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
  proof: ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg, fun h =>
    h.elim (and_imp.2 mul_nonneg) (and_imp.2 mul_nonneg_of_nonpos_of_nonpos)⟩

中文:
定理 mul_nonneg_iff
  结论: [ExistsAddOfLE R] [乘正严格递增 R] [正乘严格递增 R]
  证明: ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg, fun h =>
    h.elim (and_imp.2 mul_nonneg) (and_imp.2 mul_nonneg_of_nonpos_of_nonpos)⟩

Depends on / 依赖: and_imp, h.elim, mul_nonneg, mul_nonneg_of_nonpos_of_nonpos, nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg
-/
theorem mul_nonneg_iff [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] :
    0 <= a * b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 :=
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg, fun h =>
    h.elim (and_imp.2 mul_nonneg) (and_imp.2 mul_nonneg_of_nonpos_of_nonpos)⟩

/--
theorem `mul_nonneg_of_three` / 定理 `mul_nonneg_of_three`

English:
theorem mul_nonneg_of_three
  statement: [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
  proof: by
  iterate 3 rw [mul_nonneg_iff]
  have or_a := le_total 0 a
  have or_b := le_total 0 b
  have or_c := le_total 0 c
  aesop

中文:
定理 mul_nonneg_of_three
  结论: [ExistsAddOfLE R] [乘正严格递增 R] [正乘严格递增 R]
  证明: by
  iterate 3 rw [mul_nonneg_iff]
  have or_a := le_total 0 a
  have or_b := le_total 0 b
  have or_c := le_total 0 c
  aesop

Depends on / 依赖: iterate, le_total, mul_nonneg_iff, or_a, or_b, or_c
-/
theorem mul_nonneg_of_three [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (a b c : R) : 0 <= a * b ∨ 0 <= b * c ∨ 0 <= c * a := by
  iterate 3 rw [mul_nonneg_iff]
  have or_a := le_total 0 a
  have or_b := le_total 0 b
  have or_c := le_total 0 c
  aesop

/--
lemma `mul_nonneg_iff_pos_imp_nonneg` / 引理 `mul_nonneg_iff_pos_imp_nonneg`

English:
lemma mul_nonneg_iff_pos_imp_nonneg
  statement: [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
  proof: by
  refine mul_nonneg_iff.trans ?_
  simp_rw [← not_le, ← or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

@[simp]

中文:
引理 mul_nonneg_iff_pos_imp_nonneg
  结论: [ExistsAddOfLE R] [正乘严格递增 R] [乘正严格递增 R]
  证明: by
  refine mul_nonneg_iff.trans ?_
  simp_rw [← not_le, ← or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

@[simp]

Depends on / 依赖: le_total, mul_nonneg_iff, mul_nonneg_iff.trans, not_le, or_iff_not_imp_left, simp_rw
-/
lemma mul_nonneg_iff_pos_imp_nonneg [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    0 <= a * b ↔ (0 < a -> 0 <= b) ∧ (0 < b -> 0 <= a) := by
  refine mul_nonneg_iff.trans ?_
  simp_rw [← not_le, ← or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

@[simp]
/--
theorem `mul_le_mul_left_of_neg` / 定理 `mul_le_mul_left_of_neg`

English:
theorem mul_le_mul_left_of_neg
  statement: [ExistsAddOfLE R] [PosMulStrictMono R]
  proof: (strictAnti_mul_left h).le_iff_ge

@[simp]

中文:
定理 mul_le_mul_left_of_neg
  结论: [ExistsAddOfLE R] [正乘严格递增 R]
  证明: (strictAnti_mul_left h).le_iff_ge

@[simp]

Depends on / 依赖: le_iff_ge, strictAnti_mul_left
-/
theorem mul_le_mul_left_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b c : R} (h : c < 0) : c * a <= c * b ↔ b <= a :=
  (strictAnti_mul_left h).le_iff_ge

@[simp]
/--
theorem `mul_le_mul_right_of_neg` / 定理 `mul_le_mul_right_of_neg`

English:
theorem mul_le_mul_right_of_neg
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: (strictAnti_mul_right h).le_iff_ge

@[simp]

中文:
定理 mul_le_mul_right_of_neg
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: (strictAnti_mul_right h).le_iff_ge

@[simp]

Depends on / 依赖: le_iff_ge, strictAnti_mul_right
-/
theorem mul_le_mul_right_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b c : R} (h : c < 0) : a * c <= b * c ↔ b <= a :=
  (strictAnti_mul_right h).le_iff_ge

@[simp]
/--
theorem `mul_lt_mul_left_of_neg` / 定理 `mul_lt_mul_left_of_neg`

English:
theorem mul_lt_mul_left_of_neg
  statement: [ExistsAddOfLE R] [PosMulStrictMono R]
  proof: (strictAnti_mul_left h).lt_iff_gt

@[simp]

中文:
定理 mul_lt_mul_left_of_neg
  结论: [ExistsAddOfLE R] [正乘严格递增 R]
  证明: (strictAnti_mul_left h).lt_iff_gt

@[simp]

Depends on / 依赖: lt_iff_gt, strictAnti_mul_left
-/
theorem mul_lt_mul_left_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b c : R} (h : c < 0) : c * a < c * b ↔ b < a :=
  (strictAnti_mul_left h).lt_iff_gt

@[simp]
/--
theorem `mul_lt_mul_right_of_neg` / 定理 `mul_lt_mul_right_of_neg`

English:
theorem mul_lt_mul_right_of_neg
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: (strictAnti_mul_right h).lt_iff_gt

中文:
定理 mul_lt_mul_right_of_neg
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: (strictAnti_mul_right h).lt_iff_gt

Depends on / 依赖: lt_iff_gt, strictAnti_mul_right
-/
theorem mul_lt_mul_right_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b c : R} (h : c < 0) : a * c < b * c ↔ b < a :=
  (strictAnti_mul_right h).lt_iff_gt

/--
theorem `lt_of_mul_lt_mul_of_nonpos_left` / 定理 `lt_of_mul_lt_mul_of_nonpos_left`

English:
theorem lt_of_mul_lt_mul_of_nonpos_left
  statement: [ExistsAddOfLE R] [PosMulMono R]
  proof: (antitone_mul_left hc).reflect_lt h

中文:
定理 lt_of_mul_lt_mul_of_nonpos_left
  结论: [ExistsAddOfLE R] [正乘递增 R]
  证明: (antitone_mul_left hc).reflect_lt h

Depends on / 依赖: antitone_mul_left, reflect_lt
-/
theorem lt_of_mul_lt_mul_of_nonpos_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : c * a < c * b) (hc : c <= 0) : b < a :=
  (antitone_mul_left hc).reflect_lt h

/--
theorem `lt_of_mul_lt_mul_of_nonpos_right` / 定理 `lt_of_mul_lt_mul_of_nonpos_right`

English:
theorem lt_of_mul_lt_mul_of_nonpos_right
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: (antitone_mul_right hc).reflect_lt h

中文:
定理 lt_of_mul_lt_mul_of_nonpos_right
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: (antitone_mul_right hc).reflect_lt h

Depends on / 依赖: antitone_mul_right, reflect_lt
-/
theorem lt_of_mul_lt_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : a * c < b * c) (hc : c <= 0) : b < a :=
  (antitone_mul_right hc).reflect_lt h

/--
theorem `cmp_mul_neg_left` / 定理 `cmp_mul_neg_left`

English:
theorem cmp_mul_neg_left
  statement: [ExistsAddOfLE R] [PosMulStrictMono R]
  proof: (strictAnti_mul_left ha).cmp_map_eq b c

中文:
定理 cmp_mul_neg_left
  结论: [ExistsAddOfLE R] [正乘严格递增 R]
  证明: (strictAnti_mul_left ha).cmp_map_eq b c

Depends on / 依赖: cmp_map_eq, strictAnti_mul_left
-/
theorem cmp_mul_neg_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightReflectLT R] [AddRightStrictMono R]
    {a : R} (ha : a < 0) (b c : R) : cmp (a * b) (a * c) = cmp c b :=
  (strictAnti_mul_left ha).cmp_map_eq b c

/--
theorem `cmp_mul_neg_right` / 定理 `cmp_mul_neg_right`

English:
theorem cmp_mul_neg_right
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: (strictAnti_mul_right ha).cmp_map_eq b c

@[simp]

中文:
定理 cmp_mul_neg_right
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: (strictAnti_mul_right ha).cmp_map_eq b c

@[simp]

Depends on / 依赖: cmp_map_eq, strictAnti_mul_right
-/
theorem cmp_mul_neg_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightReflectLT R] [AddRightStrictMono R]
    {a : R} (ha : a < 0) (b c : R) : cmp (b * a) (c * a) = cmp c b :=
  (strictAnti_mul_right ha).cmp_map_eq b c

@[simp]
/--
theorem `mul_self_pos` / 定理 `mul_self_pos`

English:
theorem mul_self_pos
  statement: [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
  proof: by
  constructor
  · rintro h rfl
    rw [mul_zero] at h
    exact h.false
  · intro h
    rcases h.lt_or_gt with h | h
    exacts [mul_pos_of_neg_of_neg h h, mul_pos h h]

中文:
定理 mul_self_pos
  结论: [ExistsAddOfLE R] [正乘严格递增 R] [乘正严格递增 R]
  证明: by
  constructor
  · rintro h rfl
    rw [mul_zero] at h
    exact h.false
  · intro h
    rcases h.lt_or_gt with h | h
    exacts [mul_pos_of_neg_of_neg h h, mul_pos h h]

Depends on / 依赖: exacts, h.false, h.lt_or_gt, lt_or_gt, mul_pos, mul_pos_of_neg_of_neg, mul_zero
-/
theorem mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftStrictMono R] [AddLeftReflectLT R]
    {a : R} : 0 < a * a ↔ a != 0 := by
  constructor
  · rintro h rfl
    rw [mul_zero] at h
    exact h.false
  · intro h
    rcases h.lt_or_gt with h | h
    exacts [mul_pos_of_neg_of_neg h h, mul_pos h h]

/--
theorem `nonneg_of_mul_nonpos_left` / 定理 `nonneg_of_mul_nonpos_left`

English:
theorem nonneg_of_mul_nonpos_left
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: le_of_not_gt fun ha => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge

中文:
定理 nonneg_of_mul_nonpos_left
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: le_of_not_gt fun ha => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge

Depends on / 依赖: absurd, le_of_not_gt, mul_pos_of_neg_of_neg, not_ge
-/
theorem nonneg_of_mul_nonpos_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b <= 0) (hb : b < 0) : 0 <= a :=
  le_of_not_gt fun ha => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge

/--
theorem `nonneg_of_mul_nonpos_right` / 定理 `nonneg_of_mul_nonpos_right`

English:
theorem nonneg_of_mul_nonpos_right
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: le_of_not_gt fun hb => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge

中文:
定理 nonneg_of_mul_nonpos_right
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: le_of_not_gt fun hb => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge

Depends on / 依赖: absurd, le_of_not_gt, mul_pos_of_neg_of_neg, not_ge
-/
theorem nonneg_of_mul_nonpos_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b <= 0) (ha : a < 0) : 0 <= b :=
  le_of_not_gt fun hb => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge

/--
theorem `pos_of_mul_neg_left` / 定理 `pos_of_mul_neg_left`

English:
theorem pos_of_mul_neg_left
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: lt_of_not_ge fun ha => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt

中文:
定理 pos_of_mul_neg_left
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: lt_of_not_ge fun ha => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt

Depends on / 依赖: absurd, lt_of_not_ge, mul_nonneg_of_nonpos_of_nonpos, not_gt
-/
theorem pos_of_mul_neg_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b < 0) (hb : b <= 0) : 0 < a :=
  lt_of_not_ge fun ha => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt

/--
theorem `pos_of_mul_neg_right` / 定理 `pos_of_mul_neg_right`

English:
theorem pos_of_mul_neg_right
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: lt_of_not_ge fun hb => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt

中文:
定理 pos_of_mul_neg_right
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: lt_of_not_ge fun hb => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt

Depends on / 依赖: absurd, lt_of_not_ge, mul_nonneg_of_nonpos_of_nonpos, not_gt
-/
theorem pos_of_mul_neg_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b < 0) (ha : a <= 0) : 0 < b :=
  lt_of_not_ge fun hb => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt

/--
theorem `neg_iff_pos_of_mul_neg` / 定理 `neg_iff_pos_of_mul_neg`

English:
theorem neg_iff_pos_of_mul_neg
  statement: [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
  proof: ⟨pos_of_mul_neg_right hab ∘ le_of_lt, neg_of_mul_neg_left hab ∘ le_of_lt⟩

中文:
定理 neg_iff_pos_of_mul_neg
  结论: [ExistsAddOfLE R] [正乘递增 R] [乘正递增 R]
  证明: ⟨pos_of_mul_neg_right hab ∘ le_of_lt, neg_of_mul_neg_left hab ∘ le_of_lt⟩

Depends on / 依赖: le_of_lt, neg_of_mul_neg_left, pos_of_mul_neg_right
-/
theorem neg_iff_pos_of_mul_neg [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hab : a * b < 0) : a < 0 ↔ 0 < b :=
  ⟨pos_of_mul_neg_right hab ∘ le_of_lt, neg_of_mul_neg_left hab ∘ le_of_lt⟩

/--
theorem `pos_iff_neg_of_mul_neg` / 定理 `pos_iff_neg_of_mul_neg`

English:
theorem pos_iff_neg_of_mul_neg
  statement: [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
  proof: ⟨neg_of_mul_neg_right hab ∘ le_of_lt, pos_of_mul_neg_left hab ∘ le_of_lt⟩

中文:
定理 pos_iff_neg_of_mul_neg
  结论: [ExistsAddOfLE R] [正乘递增 R] [乘正递增 R]
  证明: ⟨neg_of_mul_neg_right hab ∘ le_of_lt, pos_of_mul_neg_left hab ∘ le_of_lt⟩

Depends on / 依赖: le_of_lt, neg_of_mul_neg_right, pos_of_mul_neg_left
-/
theorem pos_iff_neg_of_mul_neg [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hab : a * b < 0) : 0 < a ↔ b < 0 :=
  ⟨neg_of_mul_neg_right hab ∘ le_of_lt, pos_of_mul_neg_left hab ∘ le_of_lt⟩

/--
lemma `sq_nonneg` / 引理 `sq_nonneg`

English:
lemma sq_nonneg
  statement: [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
  proof: by
  obtain ha | ha := le_or_gt 0 a
  · exact pow_succ_nonneg ha _
  obtain ⟨b, hab⟩ := exists_add_of_le ha.le
  have hb : 0 < b := not_le.1 fun hb => (add_neg_of_neg_of_nonpos ha hb).ne' hab
  calc
    0 <= b ^ 2 := pow_succ_nonneg hb.le _
    _ = b ^ 2 + a * (a + b) := by rw [← hab, mul_zero, add_zero]
    _ = a ^ 2 + (a + b) * b := by rw [add_mul, mul_add, sq, sq, add_comm, add_assoc]
    _ = a ^ 2 := by rw [← hab, zero_mul, add_zero]

@[simp]

中文:
引理 sq_nonneg
  结论: [ExistsAddOfLE R] [正乘递增 R] [AddLeftMono R]
  证明: by
  obtain ha | ha := le_or_gt 0 a
  · exact pow_succ_nonneg ha _
  obtain ⟨b, hab⟩ := exists_add_of_le ha.le
  have hb : 0 < b := not_le.1 fun hb => (add_neg_of_neg_of_nonpos ha hb).ne' hab
  calc
    0 <= b ^ 2 := pow_succ_nonneg hb.le _
    _ = b ^ 2 + a * (a + b) := by rw [← hab, mul_zero, add_zero]
    _ = a ^ 2 + (a + b) * b := by rw [add_mul, mul_add, sq, sq, add_comm, add_assoc]
    _ = a ^ 2 := by rw [← hab, zero_mul, add_zero]

@[simp]

Depends on / 依赖: add_assoc, add_comm, add_mul, add_neg_of_neg_of_nonpos, add_zero, exists_add_of_le, ha.le, hb.le, le_or_gt, mul_add, mul_zero, not_le, pow_succ_nonneg, zero_mul
-/
lemma sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (a : R) : 0 <= a ^ 2 := by
  obtain ha | ha := le_or_gt 0 a
  · exact pow_succ_nonneg ha _
  obtain ⟨b, hab⟩ := exists_add_of_le ha.le
  have hb : 0 < b := not_le.1 fun hb => (add_neg_of_neg_of_nonpos ha hb).ne' hab
  calc
    0 <= b ^ 2 := pow_succ_nonneg hb.le _
    _ = b ^ 2 + a * (a + b) := by rw [← hab, mul_zero, add_zero]
    _ = a ^ 2 + (a + b) * b := by rw [add_mul, mul_add, sq, sq, add_comm, add_assoc]
    _ = a ^ 2 := by rw [← hab, zero_mul, add_zero]

@[simp]
/--
lemma `sq_nonpos_iff` / 引理 `sq_nonpos_iff`

English:
lemma sq_nonpos_iff
  statement: [ExistsAddOfLE R]
  proof: by
  trans r ^ 2 = 0
  · rw [le_antisymm_iff, and_iff_left (sq_nonneg r)]
  · exact sq_eq_zero_iff

alias pow_two_nonneg := sq_nonneg

中文:
引理 sq_nonpos_iff
  结论: [ExistsAddOfLE R]
  证明: by
  trans r ^ 2 = 0
  · rw [le_antisymm_iff, and_iff_left (sq_nonneg r)]
  · exact sq_eq_zero_iff

alias pow_two_nonneg := sq_nonneg

Depends on / 依赖: and_iff_left, le_antisymm_iff, sq_eq_zero_iff, sq_nonneg
-/
lemma sq_nonpos_iff [ExistsAddOfLE R]
    [PosMulMono R] [AddLeftMono R] [NoZeroDivisors R] (r : R) :
    r ^ 2 <= 0 ↔ r = 0 := by
  trans r ^ 2 = 0
  · rw [le_antisymm_iff, and_iff_left (sq_nonneg r)]
  · exact sq_eq_zero_iff

alias pow_two_nonneg := sq_nonneg

/--
lemma `mul_self_nonneg` / 引理 `mul_self_nonneg`

English:
lemma mul_self_nonneg
  statement: [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
  proof: by simpa only [sq] using sq_nonneg a

中文:
引理 mul_self_nonneg
  结论: [ExistsAddOfLE R] [正乘递增 R] [AddLeftMono R]
  证明: by simpa only [sq] using sq_nonneg a

Depends on / 依赖: sq_nonneg
-/
lemma mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (a : R) : 0 <= a * a := by simpa only [sq] using sq_nonneg a

instance (priority := 100) [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] :
    ZeroLEOneClass R where
  zero_le_one := by simpa only [one_mul] using mul_self_nonneg (1 : R)

/--
lemma `mul_self_add_mul_self_eq_zero` / 引理 `mul_self_add_mul_self_eq_zero`

English:
lemma mul_self_add_mul_self_eq_zero
  statement: [NoZeroDivisors R]
  proof: by
  rw [add_eq_zero_iff_of_nonneg]; rw [mul_self_eq_zero (M₀ := R)]; rw [mul_self_eq_zero (M₀ := R)] <;>
    apply mul_self_nonneg

中文:
引理 mul_self_add_mul_self_eq_zero
  结论: [无零因子 R]
  证明: by
  rw [add_eq_zero_iff_of_nonneg]; rw [mul_self_eq_zero (M₀ := R)]; rw [mul_self_eq_zero (M₀ := R)] <;>
    apply mul_self_nonneg

Depends on / 依赖: add_eq_zero_iff_of_nonneg, mul_self_eq_zero, mul_self_nonneg
-/
lemma mul_self_add_mul_self_eq_zero [NoZeroDivisors R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] :
    a * a + b * b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_zero_iff_of_nonneg]; rw [mul_self_eq_zero (M₀ := R)]; rw [mul_self_eq_zero (M₀ := R)] <;>
    apply mul_self_nonneg

/--
lemma `eq_zero_of_mul_self_add_mul_self_eq_zero` / 引理 `eq_zero_of_mul_self_add_mul_self_eq_zero`

English:
lemma eq_zero_of_mul_self_add_mul_self_eq_zero
  statement: [NoZeroDivisors R]
  proof: (mul_self_add_mul_self_eq_zero.mp h).left

中文:
引理 eq_zero_of_mul_self_add_mul_self_eq_zero
  结论: [无零因子 R]
  证明: (mul_self_add_mul_self_eq_zero.mp h).left

Depends on / 依赖: mul_self_add_mul_self_eq_zero, mul_self_add_mul_self_eq_zero.mp
-/
lemma eq_zero_of_mul_self_add_mul_self_eq_zero [NoZeroDivisors R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (h : a * a + b * b = 0) : a = 0 :=
  (mul_self_add_mul_self_eq_zero.mp h).left

/--
theorem `pos_of_right_mul_lt_le` / 定理 `pos_of_right_mul_lt_le`

English:
theorem pos_of_right_mul_lt_le
  statement: [ExistsAddOfLE R] [PosMulMono R]
  proof: by
  by_cases! ha : 0 < a
  · exact ha
  · grind [mul_le_mul_of_nonpos_left hbc ha]

中文:
定理 pos_of_right_mul_lt_le
  结论: [ExistsAddOfLE R] [正乘递增 R]
  证明: by
  by_cases! ha : 0 < a
  · exact ha
  · grind [mul_le_mul_of_nonpos_left hbc ha]

Depends on / 依赖: mul_le_mul_of_nonpos_left
-/
theorem pos_of_right_mul_lt_le [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : a * b < a * c) (hbc : b <= c) :
    0 < a := by
  by_cases! ha : 0 < a
  · exact ha
  · grind [mul_le_mul_of_nonpos_left hbc ha]

/--
theorem `pos_of_left_mul_lt_le` / 定理 `pos_of_left_mul_lt_le`

English:
theorem pos_of_left_mul_lt_le
  statement: [ExistsAddOfLE R] [MulPosMono R]
  proof: by
  by_cases! ha : 0 < a
  · exact ha
  · grind [mul_le_mul_of_nonpos_right hbc ha]

中文:
定理 pos_of_left_mul_lt_le
  结论: [ExistsAddOfLE R] [乘正递增 R]
  证明: by
  by_cases! ha : 0 < a
  · exact ha
  · grind [mul_le_mul_of_nonpos_right hbc ha]

Depends on / 依赖: mul_le_mul_of_nonpos_right
-/
theorem pos_of_left_mul_lt_le [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddRightReflectLE R]
    (h : b * a < c * a) (hbc : b <= c) :
    0 < a := by
  by_cases! ha : 0 < a
  · exact ha
  · grind [mul_le_mul_of_nonpos_right hbc ha]

end LinearOrderedSemiring

section LinearOrderedCommSemiring

variable [CommSemiring R] [LinearOrder R] {a d : R}

/--
lemma `max_mul_mul_le_max_mul_max` / 引理 `max_mul_mul_le_max_mul_max`

English:
lemma max_mul_mul_le_max_mul_max
  given: [PosMulMono R] [MulPosMono R] (b c : R) (ha : 0 <= a) (hd : 0 <= d)
  proof: have ba : b * a <= max d b * max c a := by
    gcongr
    exacts [ha, hd.trans <| le_max_left d b, le_max_right d b, le_max_right c a]
  have cd : c * d <= max a c * max b d :=
    mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c))
  max_le (by simpa [mul_comm, max_comm] using ba) (by simpa [mul_comm, max_comm] using cd)

中文:
引理 max_mul_mul_le_max_mul_max
  条件: [正乘递增 R] [乘正递增 R] (b c : R) (ha : 0 <= a) (hd : 0 <= d)
  证明: have ba : b * a <= max d b * max c a := by
    gcongr
    exacts [ha, hd.trans <| le_max_left d b, le_max_right d b, le_max_right c a]
  have cd : c * d <= max a c * max b d :=
    mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c))
  max_le (by simpa [mul_comm, max_comm] using ba) (by simpa [mul_comm, max_comm] using cd)

Depends on / 依赖: exacts, hd.trans, le_max_left, le_max_right, le_trans, max_comm, max_le, mul_comm, mul_le_mul
-/
lemma max_mul_mul_le_max_mul_max [PosMulMono R] [MulPosMono R] (b c : R) (ha : 0 <= a) (hd : 0 <= d) :
    max (a * b) (d * c) <= max a c * max d b :=
  have ba : b * a <= max d b * max c a := by
    gcongr
    exacts [ha, hd.trans <| le_max_left d b, le_max_right d b, le_max_right c a]
  have cd : c * d <= max a c * max b d :=
    mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c))
  max_le (by simpa [mul_comm, max_comm] using ba) (by simpa [mul_comm, max_comm] using cd)

/--
lemma `two_mul_le_add_sq` / 引理 `two_mul_le_add_sq`

English:
lemma two_mul_le_add_sq
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: by
  simpa [fn_min_add_fn_max (fun x => x * x), sq, two_mul, add_mul]
    using mul_add_mul_le_mul_add_mul (@min_le_max _ _ a b) (@min_le_max _ _ a b)

alias two_mul_le_add_pow_two := two_mul_le_add_sq

中文:
引理 two_mul_le_add_sq
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: by
  simpa [fn_min_add_fn_max (fun x => x * x), sq, two_mul, add_mul]
    using mul_add_mul_le_mul_add_mul (@min_le_max _ _ a b) (@min_le_max _ _ a b)

alias two_mul_le_add_pow_two := two_mul_le_add_sq

Depends on / 依赖: add_mul, fn_min_add_fn_max, min_le_max, mul_add_mul_le_mul_add_mul, two_mul
-/
lemma two_mul_le_add_sq [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R]
    (a b : R) : 2 * a * b <= a ^ 2 + b ^ 2 := by
  simpa [fn_min_add_fn_max (fun x => x * x), sq, two_mul, add_mul]
    using mul_add_mul_le_mul_add_mul (@min_le_max _ _ a b) (@min_le_max _ _ a b)

alias two_mul_le_add_pow_two := two_mul_le_add_sq

/--
lemma `four_mul_le_sq_add` / 引理 `four_mul_le_sq_add`

English:
lemma four_mul_le_sq_add
  statement: [ExistsAddOfLE R] [MulPosStrictMono R]
  proof: by
  calc 4 * a * b
    _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, two_add_two_eq_four.symm, add_mul, mul_assoc]
    _ <= a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
    _ = (a + b) ^ 2 := (add_sq a b).symm

alias four_mul_le_pow_two_add := four_mul_le_sq_add

中文:
引理 four_mul_le_sq_add
  结论: [ExistsAddOfLE R] [乘正严格递增 R]
  证明: by
  calc 4 * a * b
    _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, two_add_two_eq_four.symm, add_mul, mul_assoc]
    _ <= a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
    _ = (a + b) ^ 2 := (add_sq a b).symm

alias four_mul_le_pow_two_add := four_mul_le_sq_add

Depends on / 依赖: add_mul, add_right_comm, add_sq, mul_assoc, two_add_two_eq_four, two_add_two_eq_four.symm, two_mul_le_add_sq
-/
lemma four_mul_le_sq_add [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R]
    (a b : R) : 4 * a * b <= (a + b) ^ 2 := by
  calc 4 * a * b
    _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, two_add_two_eq_four.symm, add_mul, mul_assoc]
    _ <= a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
    _ = (a + b) ^ 2 := (add_sq a b).symm

alias four_mul_le_pow_two_add := four_mul_le_sq_add

/--
lemma `two_mul_le_add_of_sq_le_mul` / 引理 `two_mul_le_add_of_sq_le_mul`

English:
lemma two_mul_le_add_of_sq_le_mul
  statement: [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
  proof: by
  apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
  rw [mul_mul_mul_comm]; rw [← pow_two r]; rw [two_mul]; rw [two_add_two_eq_four]
  grw [mul_le_mul_of_nonneg_left ht zero_le_four, ← mul_assoc, four_mul_le_sq_add a b, sq]

@[deprecated two_mul_le_add_of_sq_le_mul (since := "2026-04-20")]

中文:
引理 two_mul_le_add_of_sq_le_mul
  结论: [ExistsAddOfLE R] [乘正严格递增 R] [正乘严格递增 R]
  证明: by
  apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
  rw [mul_mul_mul_comm]; rw [← pow_two r]; rw [two_mul]; rw [two_add_two_eq_four]
  grw [mul_le_mul_of_nonneg_left ht zero_le_four, ← mul_assoc, four_mul_le_sq_add a b, sq]

@[deprecated two_mul_le_add_of_sq_le_mul (since := "2026-04-20")]

Depends on / 依赖: Left.add_nonneg, add_nonneg, four_mul_le_sq_add, mul_assoc, mul_le_mul_of_nonneg_left, mul_mul_mul_comm, nonneg_le_nonneg_of_sq_le_sq, pow_two, two_add_two_eq_four, two_mul, zero_le_four
-/
lemma two_mul_le_add_of_sq_le_mul [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] {a b r : R}
    (ha : 0 <= a) (hb : 0 <= b) (ht : r ^ 2 <= a * b) : 2 * r <= a + b := by
  apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
  rw [mul_mul_mul_comm]; rw [← pow_two r]; rw [two_mul]; rw [two_add_two_eq_four]
  grw [mul_le_mul_of_nonneg_left ht zero_le_four, ← mul_assoc, four_mul_le_sq_add a b, sq]

@[deprecated two_mul_le_add_of_sq_le_mul (since := "2026-04-20")]
/--
lemma `two_mul_le_add_of_sq_eq_mul` / 引理 `two_mul_le_add_of_sq_eq_mul`

English:
lemma two_mul_le_add_of_sq_eq_mul
  statement: [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
  proof: two_mul_le_add_of_sq_le_mul ha hb ht.le

中文:
引理 two_mul_le_add_of_sq_eq_mul
  结论: [ExistsAddOfLE R] [乘正严格递增 R] [正乘严格递增 R]
  证明: two_mul_le_add_of_sq_le_mul ha hb ht.le

Depends on / 依赖: ht.le, two_mul_le_add_of_sq_le_mul
-/
lemma two_mul_le_add_of_sq_eq_mul [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] {a b r : R}
    (ha : 0 <= a) (hb : 0 <= b) (ht : r ^ 2 = a * b) : 2 * r <= a + b :=
  two_mul_le_add_of_sq_le_mul ha hb ht.le

end LinearOrderedCommSemiring

section LinearOrderedRing

variable [Ring R] [LinearOrder R] {a b : R}

-- TODO: Can the following five lemmas be generalised to
-- `[Semiring R] [LinearOrder R] [ExistsAddOfLE R] ..`?

/--
lemma `mul_neg_iff` / 引理 `mul_neg_iff`

English:
lemma mul_neg_iff
  statement: [PosMulStrictMono R] [MulPosStrictMono R]
  proof: by
  rw [← neg_pos]; rw [neg_mul_eq_mul_neg]; rw [mul_pos_iff (R := R)]; rw [neg_pos]; rw [neg_lt_zero]

中文:
引理 mul_neg_iff
  结论: [正乘严格递增 R] [乘正严格递增 R]
  证明: by
  rw [← neg_pos]; rw [neg_mul_eq_mul_neg]; rw [mul_pos_iff (R := R)]; rw [neg_pos]; rw [neg_lt_zero]

Depends on / 依赖: mul_pos_iff, neg_lt_zero, neg_mul_eq_mul_neg, neg_pos
-/
lemma mul_neg_iff [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftReflectLT R] [AddLeftStrictMono R] :
    a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← neg_pos]; rw [neg_mul_eq_mul_neg]; rw [mul_pos_iff (R := R)]; rw [neg_pos]; rw [neg_lt_zero]

/--
lemma `mul_nonpos_iff` / 引理 `mul_nonpos_iff`

English:
lemma mul_nonpos_iff
  statement: [MulPosStrictMono R] [PosMulStrictMono R]
  proof: by
  rw [← neg_nonneg]; rw [neg_mul_eq_mul_neg]; rw [mul_nonneg_iff (R := R)]; rw [neg_nonneg]; rw [neg_nonpos]

中文:
引理 mul_nonpos_iff
  结论: [乘正严格递增 R] [正乘严格递增 R]
  证明: by
  rw [← neg_nonneg]; rw [neg_mul_eq_mul_neg]; rw [mul_nonneg_iff (R := R)]; rw [neg_nonneg]; rw [neg_nonpos]

Depends on / 依赖: mul_nonneg_iff, neg_mul_eq_mul_neg, neg_nonneg, neg_nonpos
-/
lemma mul_nonpos_iff [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] :
    a * b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b := by
  rw [← neg_nonneg]; rw [neg_mul_eq_mul_neg]; rw [mul_nonneg_iff (R := R)]; rw [neg_nonneg]; rw [neg_nonpos]

/--
lemma `mul_nonneg_iff_neg_imp_nonpos` / 引理 `mul_nonneg_iff_neg_imp_nonpos`

English:
lemma mul_nonneg_iff_neg_imp_nonpos
  statement: [PosMulStrictMono R] [MulPosStrictMono R]
  proof: by
  rw [← neg_mul_neg]; rw [mul_nonneg_iff_pos_imp_nonneg (R := R)]; simp only [neg_pos, neg_nonneg]

中文:
引理 mul_nonneg_iff_neg_imp_nonpos
  结论: [正乘严格递增 R] [乘正严格递增 R]
  证明: by
  rw [← neg_mul_neg]; rw [mul_nonneg_iff_pos_imp_nonneg (R := R)]; simp only [neg_pos, neg_nonneg]

Depends on / 依赖: mul_nonneg_iff_pos_imp_nonneg, neg_mul_neg, neg_nonneg, neg_pos
-/
lemma mul_nonneg_iff_neg_imp_nonpos [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    0 <= a * b ↔ (a < 0 -> b <= 0) ∧ (b < 0 -> a <= 0) := by
  rw [← neg_mul_neg]; rw [mul_nonneg_iff_pos_imp_nonneg (R := R)]; simp only [neg_pos, neg_nonneg]

/--
lemma `mul_nonpos_iff_pos_imp_nonpos` / 引理 `mul_nonpos_iff_pos_imp_nonpos`

English:
lemma mul_nonpos_iff_pos_imp_nonpos
  statement: [PosMulStrictMono R] [MulPosStrictMono R]
  proof: by
  rw [← neg_nonneg]; rw [← mul_neg]; rw [mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]

中文:
引理 mul_nonpos_iff_pos_imp_nonpos
  结论: [正乘严格递增 R] [乘正严格递增 R]
  证明: by
  rw [← neg_nonneg]; rw [← mul_neg]; rw [mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]

Depends on / 依赖: mul_neg, mul_nonneg_iff_pos_imp_nonneg, neg_nonneg, neg_pos
-/
lemma mul_nonpos_iff_pos_imp_nonpos [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    a * b <= 0 ↔ (0 < a -> b <= 0) ∧ (b < 0 -> 0 <= a) := by
  rw [← neg_nonneg]; rw [← mul_neg]; rw [mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]

/--
lemma `mul_nonpos_iff_neg_imp_nonneg` / 引理 `mul_nonpos_iff_neg_imp_nonneg`

English:
lemma mul_nonpos_iff_neg_imp_nonneg
  statement: [PosMulStrictMono R] [MulPosStrictMono R]
  proof: by
  rw [← neg_nonneg]; rw [← neg_mul]; rw [mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]

中文:
引理 mul_nonpos_iff_neg_imp_nonneg
  结论: [正乘严格递增 R] [乘正严格递增 R]
  证明: by
  rw [← neg_nonneg]; rw [← neg_mul]; rw [mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]

Depends on / 依赖: mul_nonneg_iff_pos_imp_nonneg, neg_mul, neg_nonneg, neg_pos
-/
lemma mul_nonpos_iff_neg_imp_nonneg [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    a * b <= 0 ↔ (a < 0 -> 0 <= b) ∧ (0 < b -> a <= 0) := by
  rw [← neg_nonneg]; rw [← neg_mul]; rw [mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]

/--
lemma `neg_one_lt_zero` / 引理 `neg_one_lt_zero`

English:
lemma neg_one_lt_zero
  proof: neg_lt_zero.2 zero_lt_one

中文:
引理 neg_one_lt_zero
  证明: neg_lt_zero.2 zero_lt_one

Depends on / 依赖: neg_lt_zero, zero_lt_one
-/
lemma neg_one_lt_zero
    [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStrictMono R] :
    -1 < (0 : R) := neg_lt_zero.2 zero_lt_one

/--
lemma `sub_one_lt` / 引理 `sub_one_lt`

English:
lemma sub_one_lt
  statement: [ZeroLEOneClass R] [NeZero (1 : R)]
  proof: sub_lt_iff_lt_add.2 lt_add_one a

中文:
引理 sub_one_lt
  结论: [ZeroLEOne类 R] [NeZero (1 : R)]
  证明: sub_lt_iff_lt_add.2 lt_add_one a

Depends on / 依赖: lt_add_one, sub_lt_iff_lt_add
-/
lemma sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)]
    [AddLeftStrictMono R]
(a : R) : a - 1 < a := sub_lt_iff_lt_add.2 lt_add_one a

/--
lemma `mul_self_le_mul_self_of_le_of_neg_le` / 引理 `mul_self_le_mul_self_of_le_of_neg_le`

English:
lemma mul_self_le_mul_self_of_le_of_neg_le
  proof: (le_total 0 a).elim (mul_self_le_mul_self · h₁) fun h =>
(neg_mul_neg a a).symm.trans_le
mul_le_mul h₂ h₂ (neg_nonneg.2 h) (neg_nonneg.2 h).trans h₂

中文:
引理 mul_self_le_mul_self_of_le_of_neg_le
  证明: (le_total 0 a).elim (mul_self_le_mul_self · h₁) fun h =>
(neg_mul_neg a a).symm.trans_le
mul_le_mul h₂ h₂ (neg_nonneg.2 h) (neg_nonneg.2 h).trans h₂

Depends on / 依赖: le_total, mul_le_mul, mul_self_le_mul_self, neg_mul_neg, neg_nonneg, symm.trans_le, trans_le
-/
lemma mul_self_le_mul_self_of_le_of_neg_le
    [MulPosMono R] [PosMulMono R] [AddLeftMono R]
    (h₁ : a <= b) (h₂ : -a <= b) : a * a <= b * b :=
  (le_total 0 a).elim (mul_self_le_mul_self · h₁) fun h =>
(neg_mul_neg a a).symm.trans_le
mul_le_mul h₂ h₂ (neg_nonneg.2 h) (neg_nonneg.2 h).trans h₂

/--
lemma `sub_mul_sub_nonneg_iff` / 引理 `sub_mul_sub_nonneg_iff`

English:
lemma sub_mul_sub_nonneg_iff
  statement: [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
  proof: by
  rw [mul_nonneg_iff]; rw [sub_nonneg]; rw [sub_nonneg]; rw [sub_nonpos]; rw [sub_nonpos]; rw [and_iff_right_of_imp h.trans]; rw [and_iff_left_of_imp h.trans']; rw [or_comm]

中文:
引理 sub_mul_sub_nonneg_iff
  结论: [乘正严格递增 R] [正乘严格递增 R] [AddLeftMono R]
  证明: by
  rw [mul_nonneg_iff]; rw [sub_nonneg]; rw [sub_nonneg]; rw [sub_nonpos]; rw [sub_nonpos]; rw [and_iff_right_of_imp h.trans]; rw [and_iff_left_of_imp h.trans']; rw [or_comm]

Depends on / 依赖: and_iff_left_of_imp, and_iff_right_of_imp, h.trans, mul_nonneg_iff, or_comm, sub_nonneg, sub_nonpos
-/
lemma sub_mul_sub_nonneg_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a <= b) : 0 <= (x - a) * (x - b) ↔ x <= a ∨ b <= x := by
  rw [mul_nonneg_iff]; rw [sub_nonneg]; rw [sub_nonneg]; rw [sub_nonpos]; rw [sub_nonpos]; rw [and_iff_right_of_imp h.trans]; rw [and_iff_left_of_imp h.trans']; rw [or_comm]

/--
lemma `sub_mul_sub_nonpos_iff` / 引理 `sub_mul_sub_nonpos_iff`

English:
lemma sub_mul_sub_nonpos_iff
  statement: [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
  proof: by
  rw [mul_nonpos_iff]; rw [sub_nonneg]; rw [sub_nonneg]; rw [sub_nonpos]; rw [sub_nonpos]; rw [or_iff_left_iff_imp]; rw [and_comm]
  exact And.imp h.trans h.trans'

中文:
引理 sub_mul_sub_nonpos_iff
  结论: [乘正严格递增 R] [正乘严格递增 R] [AddLeftMono R]
  证明: by
  rw [mul_nonpos_iff]; rw [sub_nonneg]; rw [sub_nonneg]; rw [sub_nonpos]; rw [sub_nonpos]; rw [or_iff_left_iff_imp]; rw [and_comm]
  exact And.imp h.trans h.trans'

Depends on / 依赖: And.imp, and_comm, h.trans, mul_nonpos_iff, or_iff_left_iff_imp, sub_nonneg, sub_nonpos
-/
lemma sub_mul_sub_nonpos_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a <= b) : (x - a) * (x - b) <= 0 ↔ a <= x ∧ x <= b := by
  rw [mul_nonpos_iff]; rw [sub_nonneg]; rw [sub_nonneg]; rw [sub_nonpos]; rw [sub_nonpos]; rw [or_iff_left_iff_imp]; rw [and_comm]
  exact And.imp h.trans h.trans'

/--
lemma `sub_mul_sub_pos_iff` / 引理 `sub_mul_sub_pos_iff`

English:
lemma sub_mul_sub_pos_iff
  statement: [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
  proof: by
  rw [mul_pos_iff]; rw [sub_pos]; rw [sub_pos]; rw [sub_neg]; rw [sub_neg]; rw [and_iff_right_of_imp h.trans_lt]; rw [and_iff_left_of_imp h.trans_lt']; rw [or_comm]

中文:
引理 sub_mul_sub_pos_iff
  结论: [乘正严格递增 R] [正乘严格递增 R] [AddLeftMono R]
  证明: by
  rw [mul_pos_iff]; rw [sub_pos]; rw [sub_pos]; rw [sub_neg]; rw [sub_neg]; rw [and_iff_right_of_imp h.trans_lt]; rw [and_iff_left_of_imp h.trans_lt']; rw [or_comm]

Depends on / 依赖: and_iff_left_of_imp, and_iff_right_of_imp, h.trans_lt, mul_pos_iff, or_comm, sub_neg, sub_pos, trans_lt
-/
lemma sub_mul_sub_pos_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a <= b) : 0 < (x - a) * (x - b) ↔ x < a ∨ b < x := by
  rw [mul_pos_iff]; rw [sub_pos]; rw [sub_pos]; rw [sub_neg]; rw [sub_neg]; rw [and_iff_right_of_imp h.trans_lt]; rw [and_iff_left_of_imp h.trans_lt']; rw [or_comm]

/--
lemma `sub_mul_sub_neg_iff` / 引理 `sub_mul_sub_neg_iff`

English:
lemma sub_mul_sub_neg_iff
  statement: [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
  proof: by
  rw [mul_neg_iff]; rw [sub_pos]; rw [sub_pos]; rw [sub_neg]; rw [sub_neg]; rw [or_iff_left_iff_imp]; rw [and_comm]
  exact And.imp h.trans_lt h.trans_lt'

中文:
引理 sub_mul_sub_neg_iff
  结论: [乘正严格递增 R] [正乘严格递增 R] [AddLeftMono R]
  证明: by
  rw [mul_neg_iff]; rw [sub_pos]; rw [sub_pos]; rw [sub_neg]; rw [sub_neg]; rw [or_iff_left_iff_imp]; rw [and_comm]
  exact And.imp h.trans_lt h.trans_lt'

Depends on / 依赖: And.imp, and_comm, h.trans_lt, mul_neg_iff, or_iff_left_iff_imp, sub_neg, sub_pos, trans_lt
-/
lemma sub_mul_sub_neg_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a <= b) : (x - a) * (x - b) < 0 ↔ a < x ∧ x < b := by
  rw [mul_neg_iff]; rw [sub_pos]; rw [sub_pos]; rw [sub_neg]; rw [sub_neg]; rw [or_iff_left_iff_imp]; rw [and_comm]
  exact And.imp h.trans_lt h.trans_lt'

end LinearOrderedRing
end OrderedCommRing
