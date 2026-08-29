/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.Int.Cast.Field
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Cast.Pi

/-!
# Injectivity of `Int.Cast` into characteristic zero rings and fields.

-/

public section

open Nat Set

variable {α β : Type*}

namespace Int

@[simp, norm_cast]
/--
theorem `cast_div_charZero` / 定理 `cast_div_charZero`

English:
theorem cast_div_charZero
  given: {k : Type*} [DivisionRing k] [CharZero k] {m n : Int} (n_dvd : n ∣ m)
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [Int.ediv_zero]
  · exact cast_div n_dvd (cast_ne_zero.mpr hn)

中文:
定理 cast_div_charZero
  条件: {k : 类型} [DivisionRing k] [CharZero k] {m n : 整数} (n_dvd : n ∣ m)
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [Int.ediv_zero]
  · exact cast_div n_dvd (cast_ne_zero.mpr hn)

Depends on / 依赖: Int.ediv_zero, cast_div, cast_ne_zero, cast_ne_zero.mpr, ediv_zero, eq_or_ne, n_dvd
-/
theorem cast_div_charZero {k : Type*} [DivisionRing k] [CharZero k] {m n : Int} (n_dvd : n ∣ m) :
    ((m / n : Int) : k) = m / n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [Int.ediv_zero]
  · exact cast_div n_dvd (cast_ne_zero.mpr hn)

-- Necessary for confluence with `ofNat_ediv` and `cast_div_charZero`.
@[simp, norm_cast]
/--
theorem `cast_div_ofNat_charZero` / 定理 `cast_div_ofNat_charZero`

English:
theorem cast_div_ofNat_charZero
  statement: {k : Type*} [DivisionRing k] [CharZero k] {m n : Nat}
  proof: by
  rw [cast_div_charZero (Int.ofNat_dvd.mpr n_dvd)]; rw [cast_natCast]; rw [cast_natCast]

中文:
定理 cast_div_ofNat_charZero
  结论: {k : 类型} [DivisionRing k] [CharZero k] {m n : 自然数}
  证明: by
  rw [cast_div_charZero (Int.ofNat_dvd.mpr n_dvd)]; rw [cast_natCast]; rw [cast_natCast]

Depends on / 依赖: Int.ofNat_dvd.mpr, cast_div_charZero, cast_natCast, n_dvd, ofNat_dvd
-/
theorem cast_div_ofNat_charZero {k : Type*} [DivisionRing k] [CharZero k] {m n : Nat}
    (n_dvd : n ∣ m) : (((m : Int) / (n : Int) : Int) : k) = m / n := by
  rw [cast_div_charZero (Int.ofNat_dvd.mpr n_dvd)]; rw [cast_natCast]; rw [cast_natCast]

end Int

/--
theorem `RingHom.injective_int` / 定理 `RingHom.injective_int`

English:
theorem RingHom.injective_int
  given: {α : Type*} [NonAssocRing α] (f : Int ->+* α) [CharZero α]
  proof: Subsingleton.elim (Int.castRingHom _) f ▸ Int.cast_injective

中文:
定理 RingHom.injective_int
  条件: {α : 类型} [NonAssocRing α] (f : 整数 ->+* α) [CharZero α]
  证明: Subsingleton.elim (Int.castRingHom _) f ▸ Int.cast_injective

Depends on / 依赖: Int.castRingHom, Int.cast_injective, Subsingleton, Subsingleton.elim, castRingHom, cast_injective
-/
theorem RingHom.injective_int {α : Type*} [NonAssocRing α] (f : Int ->+* α) [CharZero α] :
    Function.Injective f :=
  Subsingleton.elim (Int.castRingHom _) f ▸ Int.cast_injective

namespace Function
variable [AddGroupWithOne β] [CharZero β] {n : Int}

/--
lemma `support_intCast` / 引理 `support_intCast`

English:
lemma support_intCast
  given: (hn : n != 0)
  statement: support (n : α -> β) = univ
  proof: support_const Int.cast_ne_zero.2 hn

中文:
引理 support_intCast
  条件: (hn : n != 0)
  结论: support (n : α -> β) = univ
  证明: support_const Int.cast_ne_zero.2 hn

Depends on / 依赖: Int.cast_ne_zero, cast_ne_zero, support_const
-/
lemma support_intCast (hn : n != 0) : support (n : α -> β) = univ :=
support_const Int.cast_ne_zero.2 hn

/--
lemma `mulSupport_intCast` / 引理 `mulSupport_intCast`

English:
lemma mulSupport_intCast
  given: (hn : n != 1)
  statement: mulSupport (n : α -> β) = univ
  proof: mulSupport_const Int.cast_ne_one.2 hn

中文:
引理 mulSupport_intCast
  条件: (hn : n != 1)
  结论: mulSupport (n : α -> β) = univ
  证明: mulSupport_const Int.cast_ne_one.2 hn

Depends on / 依赖: Int.cast_ne_one, cast_ne_one, mulSupport_const
-/
lemma mulSupport_intCast (hn : n != 1) : mulSupport (n : α -> β) = univ :=
mulSupport_const Int.cast_ne_one.2 hn

end Function
