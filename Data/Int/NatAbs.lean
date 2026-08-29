/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Jeremy Tan
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Lemmas about `Int.natAbs`

This file contains some results on `Int.natAbs`, the absolute value of an integer as a
natural number.

## Main results

* `Int.natAbsHom`: `Int.natAbs` bundled as a `MonoidWithZeroHom`.
-/

@[expose] public section

namespace Int

/-- `Int.natAbs` as a bundled `MonoidWithZeroHom`. -/
@[simps]
/--
Definition of `natAbsHom` / `natAbsHom` 的定义

English:
definition natAbsHom
  signature: : Int ->*₀ Nat where
  body: Int.natAbs
  map_mul' := Int.natAbs_mul
  map_one' := Int.natAbs_one
  map_zero' := Int.natAbs_zero

中文:
定义 natAbsHom
  签名: : 整数 ->*₀ 自然数 where
  定义体: Int.natAbs
  map_mul' := Int.natAbs_mul
  map_one' := Int.natAbs_one
  map_zero' := Int.natAbs_zero

Depends on / 依赖: Int.natAbs, natAbs
-/
def natAbsHom : Int ->*₀ Nat where
  toFun := Int.natAbs
  map_mul' := Int.natAbs_mul
  map_one' := Int.natAbs_one
  map_zero' := Int.natAbs_zero

/--
lemma `natAbs_natCast_sub_natCast_of_ge` / 引理 `natAbs_natCast_sub_natCast_of_ge`

English:
lemma natAbs_natCast_sub_natCast_of_ge
  given: {a b : Nat} (h : b <= a)
  statement: Int.natAbs (↑a - ↑b) = a - b
  proof: by
  lia

中文:
引理 natAbs_natCast_sub_natCast_of_ge
  条件: {a b : 自然数} (h : b <= a)
  结论: 整数.natAbs (↑a - ↑b) = a - b
  证明: by
  lia
-/
lemma natAbs_natCast_sub_natCast_of_ge {a b : Nat} (h : b <= a) : Int.natAbs (↑a - ↑b) = a - b := by
  lia

/--
lemma `natAbs_natCast_sub_natCast_of_le` / 引理 `natAbs_natCast_sub_natCast_of_le`

English:
lemma natAbs_natCast_sub_natCast_of_le
  given: {a b : Nat} (h : a <= b)
  statement: Int.natAbs (↑a - ↑b) = b - a
  proof: by
  lia

中文:
引理 natAbs_natCast_sub_natCast_of_le
  条件: {a b : 自然数} (h : a <= b)
  结论: 整数.natAbs (↑a - ↑b) = b - a
  证明: by
  lia
-/
lemma natAbs_natCast_sub_natCast_of_le {a b : Nat} (h : a <= b) : Int.natAbs (↑a - ↑b) = b - a := by
  lia

end Int
