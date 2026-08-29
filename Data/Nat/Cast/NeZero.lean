/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Gabriel Ebner
-/
module

public import Mathlib.Data.Nat.Cast.Defs

/-!
# Lemmas about nonzero elements of an `AddMonoidWithOne`
-/

public section

open Nat

namespace NeZero

/--
theorem `one_le` / 定理 `one_le`

English:
theorem one_le
  given: {n : Nat} [NeZero n]
  statement: 1 <= n
  proof: by have := NeZero.ne n; lia

中文:
定理 one_le
  条件: {n : 自然数} [NeZero n]
  结论: 1 <= n
  证明: by have := NeZero.ne n; lia

Depends on / 依赖: NeZero, NeZero.ne
-/
theorem one_le {n : Nat} [NeZero n] : 1 <= n := by have := NeZero.ne n; lia

/--
lemma `natCast_ne` / 引理 `natCast_ne`

English:
lemma natCast_ne
  given: (n : Nat) (R) [AddMonoidWithOne R] [h : NeZero (n : R)]
  statement: (n : R) != 0
  proof: h.out

中文:
引理 natCast_ne
  条件: (n : 自然数) (R) [AddMonoidWithOne R] [h : NeZero (n : R)]
  结论: (n : R) != 0
  证明: h.out

Depends on / 依赖: h.out
-/
lemma natCast_ne (n : Nat) (R) [AddMonoidWithOne R] [h : NeZero (n : R)] : (n : R) != 0 := h.out

/--
lemma `of_neZero_natCast` / 引理 `of_neZero_natCast`

English:
lemma of_neZero_natCast
  given: (R) [AddMonoidWithOne R] {n : Nat} [h : NeZero (n : R)]
  statement: NeZero n
  proof: ⟨by rintro rfl; exact h.out Nat.cast_zero⟩

中文:
引理 of_neZero_natCast
  条件: (R) [AddMonoidWithOne R] {n : 自然数} [h : NeZero (n : R)]
  结论: NeZero n
  证明: ⟨by rintro rfl; exact h.out Nat.cast_zero⟩

Depends on / 依赖: Nat.cast_zero, cast_zero, h.out
-/
lemma of_neZero_natCast (R) [AddMonoidWithOne R] {n : Nat} [h : NeZero (n : R)] : NeZero n :=
  ⟨by rintro rfl; exact h.out Nat.cast_zero⟩

/--
lemma `pos_of_neZero_natCast` / 引理 `pos_of_neZero_natCast`

English:
lemma pos_of_neZero_natCast
  given: (R) [AddMonoidWithOne R] {n : Nat} [NeZero (n : R)]
  statement: 0 < n
  proof: Nat.pos_of_ne_zero (of_neZero_natCast R).out

中文:
引理 pos_of_neZero_natCast
  条件: (R) [AddMonoidWithOne R] {n : 自然数} [NeZero (n : R)]
  结论: 0 < n
  证明: Nat.pos_of_ne_zero (of_neZero_natCast R).out

Depends on / 依赖: Nat.pos_of_ne_zero, of_neZero_natCast, pos_of_ne_zero
-/
lemma pos_of_neZero_natCast (R) [AddMonoidWithOne R] {n : Nat} [NeZero (n : R)] : 0 < n :=
  Nat.pos_of_ne_zero (of_neZero_natCast R).out

end NeZero
