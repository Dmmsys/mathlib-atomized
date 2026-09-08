/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Opposite
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Opposite

/-!
# Module operations on `Mᵐᵒᵖ`

This file contains definitions that build on top of the group action definitions in
`Mathlib/Algebra/GroupWithZero/Action/Opposite.lean`.
-/

public section

assert_not_exists LinearMap

section

variable {R M : Type*} [Semiring R] [AddCommMonoid M]

-- see Note [lower instance priority]
/-- Like `Semiring.toModule`, but multiplies on the right. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Like `Semiring.toModule`, but multiplies on the right.
-/
instance (priority := 910) Semiring.toOppositeModule : Module Rᵐᵒᵖ R :=
  { MonoidWithZero.toOppositeMulActionWithZero R with
    smul_add := fun _ _ _ => add_mul _ _ _
    add_smul := fun _ _ _ => mul_add _ _ _ }

end

namespace MulOpposite

universe u v

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- `MulOpposite.distribMulAction` extends to a `Module` -/
/-
**MulOpposite.instModule** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instModule : Module R Mᵐᵒᵖ where add_smul _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulOpposite.distribMulAction` extends to a `Module`
-/
instance instModule : Module R Mᵐᵒᵖ where
  add_smul _ _ _ := unop_injective <| add_smul _ _ _
  zero_smul _ := unop_injective <| zero_smul _ _

end MulOpposite

