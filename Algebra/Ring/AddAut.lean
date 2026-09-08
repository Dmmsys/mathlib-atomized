/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.Module.Opposite

/-!
# Multiplication on the left/right as additive automorphisms

In this file we define `AddAut.mulLeft` and `AddAut.mulRight`.

See also `AddMonoidHom.mulLeft`, `AddMonoidHom.mulRight`, `AddMonoid.End.mulLeft`, and
`AddMonoid.End.mulRight` for multiplication by `R` as an endomorphism instead of multiplication by
`Rˣ` as an automorphism.
-/

@[expose] public section


namespace AddAut

variable {R : Type*} [Semiring R]

/-- Left multiplication by a unit of a semiring as an additive automorphism. -/
@[simps! +simpRhs]
/-
**AddAut.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `AddAut`。
形式化陈述：mulLeft : Rˣ ->* Multiplicative (AddAut R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left multiplication by a unit of a semiring as an additive automorphism.
-/
def mulLeft : Rˣ →* Multiplicative (AddAut R) :=
  DistribMulAction.toAddAut _ _

/-- Right multiplication by a unit of a semiring as an additive automorphism. -/
/-
**AddAut.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `AddAut`。
形式化陈述：mulRight (u : Rˣ) : AddAut R
参数：u : Rˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right multiplication by a unit of a semiring as an additive automorphism.
-/
def mulRight (u : Rˣ) : AddAut R :=
  DistribMulAction.toAddAut Rᵐᵒᵖˣ R (Units.opEquiv.symm <| MulOpposite.op u)

@[simp]
/-
**AddAut.mulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddAut`。
形式化陈述：mulRight_apply (u : Rˣ) (x : R) : mulRight u x = x * u
参数：u : Rˣ；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulRight_apply (u : Rˣ) (x : R) : mulRight u x = x * u :=
  rfl

@[simp]
/-
**AddAut.mulRight_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddAut`。
形式化陈述：mulRight_symm_apply (u : Rˣ) (x : R) : (mulRight u).symm x = x * u⁻¹
参数：u : Rˣ；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulRight_symm_apply (u : Rˣ) (x : R) : (mulRight u).symm x = x * u⁻¹ :=
  rfl

end AddAut

