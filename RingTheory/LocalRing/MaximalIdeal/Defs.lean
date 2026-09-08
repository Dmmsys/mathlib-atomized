/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.LocalRing.Basic

/-!

# Maximal ideal of local rings

We define the maximal ideal of a local ring as the ideal of all nonunits.

## Main definitions

* `IsLocalRing.maximalIdeal`: The unique maximal ideal for a local rings. Its carrier set is the
  set of nonunits.

-/

@[expose] public section

namespace IsLocalRing

variable (R : Type*) [CommSemiring R] [IsLocalRing R]

/-- The ideal of elements that are not units. -/
/-
**IsLocalRing.maximalIdeal** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing`。
形式化陈述：maximalIdeal : Ideal R where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ideal of elements that are not units.
-/
def maximalIdeal : Ideal R where
  __ := nonunitsAddSubmonoid R
  smul_mem' _ _ := mul_mem_nonunits_right

end IsLocalRing

