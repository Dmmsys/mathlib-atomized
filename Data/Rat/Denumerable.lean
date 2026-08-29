/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Logic.Denumerable

/-!
# Denumerability of ℚ

This file proves that ℚ is denumerable.

The fact that ℚ has cardinality ℵ₀ is proved in `Mathlib/Data/Rat/Cardinal.lean`
-/

public section

assert_not_exists Module Field

namespace Rat

open Denumerable

/--
Instance `instDenumerable` / 实例 `instDenumerable`

English:
instance instDenumerable
  signature: : Denumerable Rat
  body: ofEncodableOfInfinite Rat

中文:
实例 instDenumerable
  签名: : Denumerable Rat
  定义体: ofEncodableOfInfinite Rat

Depends on / 依赖: ofEncodableOfInfinite
-/
instance instDenumerable : Denumerable Rat := ofEncodableOfInfinite Rat

end Rat
