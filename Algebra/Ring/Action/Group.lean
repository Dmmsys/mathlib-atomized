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
/--
Definition of `MulSemiringAction.toRingEquiv` / `MulSemiringAction.toRingEquiv` 的定义

English:
definition MulSemiringAction.toRingEquiv
  signature: [MulSemiringAction G R]
  body: { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]

@[deprecated (since := "2026-06-19")] alias MulSemiringAction.toRingEquiv_apply :=
MulSemiringAction.toRingEquiv_apply_apply

@[deprecated (since := "2026

中文:
定义 MulSemiringAction.toRingEquiv
  签名: [MulSemiringAction G R]
  定义体: { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]

@[deprecated (since := "2026-06-19")] alias MulSemiringAction.toRingEquiv_apply :=
MulSemiringAction.toRingEquiv_apply_apply

@[deprecated (since := "2026

Depends on / 依赖: DistribMulAction, DistribMulAction.toAddEquiv, MulSemiringAction, MulSemiringAction.toRingHom, toAddEquiv, toRingHom
-/
def MulSemiringAction.toRingEquiv [MulSemiringAction G R] : G ->* (R ≃+* R) where
  toFun x := { DistribMulAction.toAddEquiv R x, MulSemiringAction.toRingHom G R x with }
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]

@[deprecated (since := "2026-06-19")] alias MulSemiringAction.toRingEquiv_apply :=
MulSemiringAction.toRingEquiv_apply_apply

@[deprecated (since := "2026-06-19")] alias MulSemiringAction.toRingEquiv_symm_apply :=
MulSemiringAction.toRingEquiv_apply_symm_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulSemiringAction (R ≃+* R) R
  body: (· ·)
  mul_smul _ _ _ := rfl
  one_smul _ := rfl
  smul_zero := map_zero
  smul_one := map_one
  smul_add := map_add
  smul_mul := map_mul

中文:
实例 :
  签名: MulSemiringAction (R ≃+* R) R
  定义体: (· ·)
  mul_smul _ _ _ := rfl
  one_smul _ := rfl
  smul_zero := map_zero
  smul_one := map_one
  smul_add := map_add
  smul_mul := map_mul
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
