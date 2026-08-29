/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Matrix.Diagonal

/-!
# Matrices in prime characteristic

In this file we prove that matrices over a ring of characteristic `p`
with nonempty index type have the same characteristic.
-/

public section


open Matrix

variable {n : Type*} {R : Type*} [AddMonoidWithOne R]

/--
Instance `Matrix.charP` / 实例 `Matrix.charP`

English:
instance Matrix.charP
  signature: [DecidableEq n] [Nonempty n] (p : Nat) [CharP R p]
  body: by simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
    CharP.cast_eq_zero_iff R p k, forall_const]

中文:
实例 Matrix.charP
  签名: [DecidableEq n] [Nonempty n] (p : 自然数) [CharP R p]
  定义体: by simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
    CharP.cast_eq_zero_iff R p k, forall_const]

Depends on / 依赖: CharP.cast_eq_zero_iff, cast_eq_zero_iff, diagonal_eq_diagonal_iff, diagonal_natCast, diagonal_zero, forall_const, simp_rw
-/
instance Matrix.charP [DecidableEq n] [Nonempty n] (p : Nat) [CharP R p] :
    CharP (Matrix n n R) p where
  cast_eq_zero_iff k := by simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
    CharP.cast_eq_zero_iff R p k, forall_const]
