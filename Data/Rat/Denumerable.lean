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

/-- **Denumerability of the Rational Numbers** -/
/-
**Rat.instDenumerable** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instDenumerable : Denumerable Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Denumerability of the Rational Numbers**
-/
instance instDenumerable : Denumerable ℚ := ofEncodableOfInfinite ℚ

end Rat

