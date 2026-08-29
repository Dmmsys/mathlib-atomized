/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Data.Nat.Cast.Basic

/-!
# Transporting `CharZero` across injective `AddMonoidHom`s

This file exists in order to avoid adding extra imports to other files in this subdirectory.
-/

public section

/--
theorem `CharZero.of_addMonoidHom` / 定理 `CharZero.of_addMonoidHom`

English:
theorem CharZero.of_addMonoidHom
  statement: {M N : Type*} [AddCommMonoidWithOne M] [AddCommMonoidWithOne N]
  proof: by
    rwa [← map_natCast' _ he, ← map_natCast' _ he, he'.eq_iff, Nat.cast_inj] at h

中文:
定理 特征零.of_addMonoidHom
  结论: {M N : 类型} [加法交换带幺幺半群 M] [加法交换带幺幺半群 N]
  证明: by
    rwa [← map_natCast' _ he, ← map_natCast' _ he, he'.eq_iff, Nat.cast_inj] at h

Depends on / 依赖: Nat.cast_inj, cast_inj, eq_iff, map_natCast
-/
theorem CharZero.of_addMonoidHom {M N : Type*} [AddCommMonoidWithOne M] [AddCommMonoidWithOne N]
    [CharZero M] (e : M ->+ N) (he : e 1 = 1) (he' : Function.Injective e) : CharZero N where
  cast_injective n m h := by
    rwa [← map_natCast' _ he, ← map_natCast' _ he, he'.eq_iff, Nat.cast_inj] at h
