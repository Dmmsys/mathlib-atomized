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
/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: : Rˣ ->* Multiplicative (AddAut R)
  body: DistribMulAction.toAddAut _ _

中文:
定义 mulLeft
  签名: : Rˣ ->* Multiplicative (AddAut R)
  定义体: DistribMulAction.toAddAut _ _

Depends on / 依赖: DistribMulAction, DistribMulAction.toAddAut, toAddAut
-/
def mulLeft : Rˣ ->* Multiplicative (AddAut R) :=
  DistribMulAction.toAddAut _ _

/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: (u : Rˣ)
  body: DistribMulAction.toAddAut Rᵐᵒᵖˣ R (Units.opEquiv.symm <| MulOpposite.op u)

@[simp]

中文:
定义 mulRight
  签名: (u : Rˣ)
  定义体: DistribMulAction.toAddAut Rᵐᵒᵖˣ R (Units.opEquiv.symm <| MulOpposite.op u)

@[simp]

Depends on / 依赖: DistribMulAction, DistribMulAction.toAddAut, MulOpposite, MulOpposite.op, Units.opEquiv.symm, opEquiv, toAddAut
-/
def mulRight (u : Rˣ) : AddAut R :=
  DistribMulAction.toAddAut Rᵐᵒᵖˣ R (Units.opEquiv.symm <| MulOpposite.op u)

@[simp]
/--
theorem `mulRight_apply` / 定理 `mulRight_apply`

English:
theorem mulRight_apply
  given: (u : Rˣ) (x : R)
  statement: mulRight u x = x * u
  proof: rfl

@[simp]

中文:
定理 mulRight_apply
  条件: (u : Rˣ) (x : R)
  结论: mulRight u x = x * u
  证明: rfl

@[simp]
-/
theorem mulRight_apply (u : Rˣ) (x : R) : mulRight u x = x * u :=
  rfl

@[simp]
/--
theorem `mulRight_symm_apply` / 定理 `mulRight_symm_apply`

English:
theorem mulRight_symm_apply
  given: (u : Rˣ) (x : R)
  statement: (mulRight u).symm x = x * u⁻¹
  proof: rfl

中文:
定理 mulRight_symm_apply
  条件: (u : Rˣ) (x : R)
  结论: (mulRight u).symm x = x * u⁻¹
  证明: rfl
-/
theorem mulRight_symm_apply (u : Rˣ) (x : R) : (mulRight u).symm x = x * u⁻¹ :=
  rfl

end AddAut
