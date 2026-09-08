/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.Algebra.Ring.Equiv

/-!
# If a group acts multiplicatively on a semiring, each group element acts by a ring automorphism.

This result is split out from `Mathlib/Algebra/Ring/Action/Basic.lean`
to avoid needing the import of `Mathlib/Algebra/GroupWithZero/Action/Basic.lean`.
-/

@[expose] public section

section Semiring

variable (G : Type*) [Group G]
variable (R : Type*) [Semiring R]

/-- Each element of the group defines a semiring isomorphism. -/
@[simps!]
/-
**MulSemiringAction.toRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulSemiringAction.toRingEquiv [MulSemiringAction G R] : G ->* (R ≃+* R) wh
ere toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the group defines a semiring isomorphism.
-/
def MulSemiringAction.toRingEquiv [MulSemiringAction G R] : G →* (R ≃+* R) where
  toFun x := { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]

@[deprecated (since := "2026-06-19")] alias MulSemiringAction.toRingEquiv_apply :=
MulSemiringAction.toRingEquiv_apply_apply

@[deprecated (since := "2026-06-19")] alias MulSemiringAction.toRingEquiv_symm_apply :=
MulSemiringAction.toRingEquiv_apply_symm_apply
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulSemiringAction (R ≃+* R) R where
  smul := (· ·)
  mul_smul _ _ _ := rfl
  one_smul _ := rfl
  smul_zero := map_zero
  smul_one := map_one
  smul_add := map_add
  smul_mul := map_mul

end Semiring

