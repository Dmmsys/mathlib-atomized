/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.GroupWithZero.Action.End
public import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `MulSemiringAction M R`.

An example of a `MulSemiringAction` is the action of the Galois group `Gal(L/K)` on
the big field `L`. Note that `Algebra` does not in general satisfy the axioms
of `MulSemiringAction`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `MulSemiringAction`.

## Note

The corresponding typeclass of subrings invariant under such an action, `IsInvariantSubring`, is
defined in `Mathlib/Algebra/Ring/Action/Invariant.lean`.

## Tags

group action

-/

@[expose] public section

assert_not_exists Equiv.Perm.equivUnitsEnd Prod.fst_mul

universe u v

/--
Definition of `MulSemiringAction` / `MulSemiringAction` 的定义

English:
class MulSemiringAction
  parameters: (M : Type u) (R : Type v) [Monoid M] [Semiring R]
  axioms and operations (2):
    - smul_one : forall g : M, (g • (1 : R) : R) = 1
    - smul_mul : forall (g : M) (x y : R), g • (x * y) = g • x * g • y

中文:
类 MulSemiringAction
  参数: (M : 类型u) (R : 类型v) [Monoid M] [Semiring R]
  公理与运算 (2 个):
    - smul_one : 对任意 g : M, (g • (1 : R) : R) = 1
    - smul_mul : 对任意 (g : M) (x y : R), g • (x * y) = g • x * g • y
-/
class MulSemiringAction (M : Type u) (R : Type v) [Monoid M] [Semiring R] extends
  DistribMulAction M R where
  /-- Multiplying `1` by a scalar gives `1` -/
  smul_one : forall g : M, (g • (1 : R) : R) = 1
  /-- Scalar multiplication distributes across multiplication -/
  smul_mul : forall (g : M) (x y : R), g • (x * y) = g • x * g • y

section Semiring

variable (M N : Type*) [Monoid M] [Monoid N]
variable (R : Type v) [Semiring R]

-- note we could not use `extends` since these typeclasses are made with `old_structure_cmd`
instance (priority := 100) MulSemiringAction.toMulDistribMulAction
    (M R) {_ : Monoid M} {_ : Semiring R} [h : MulSemiringAction M R] :
    MulDistribMulAction M R :=
  { h with }

/-- Each element of the monoid defines a semiring homomorphism. -/
@[simps!]
/--
Definition of `MulSemiringAction.toRingHom` / `MulSemiringAction.toRingHom` 的定义

English:
definition MulSemiringAction.toRingHom
  signature: [MulSemiringAction M R] (x : M)
  body: { MulDistribMulAction.toMonoidHom R x, DistribSMul.toAddMonoidHom R x with }

中文:
定义 MulSemiringAction.toRingHom
  签名: [MulSemiringAction M R] (x : M)
  定义体: { MulDistribMulAction.toMonoidHom R x, DistribSMul.toAddMonoidHom R x with }

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, MulDistribMulAction, MulDistribMulAction.toMonoidHom, toAddMonoidHom, toMonoidHom
-/
def MulSemiringAction.toRingHom [MulSemiringAction M R] (x : M) : R ->+* R :=
  { MulDistribMulAction.toMonoidHom R x, DistribSMul.toAddMonoidHom R x with }

/--
theorem `toRingHom_injective` / 定理 `toRingHom_injective`

English:
theorem toRingHom_injective
  given: [MulSemiringAction M R] [FaithfulSMul M R]
  proof: fun _ _ h =>
  eq_of_smul_eq_smul fun r => RingHom.ext_iff.1 h r

中文:
定理 toRingHom_injective
  条件: [MulSemiringAction M R] [FaithfulSMul M R]
  证明: fun _ _ h =>
  eq_of_smul_eq_smul fun r => RingHom.ext_iff.1 h r
-/
theorem toRingHom_injective [MulSemiringAction M R] [FaithfulSMul M R] :
    Function.Injective (MulSemiringAction.toRingHom M R) := fun _ _ h =>
  eq_of_smul_eq_smul fun r => RingHom.ext_iff.1 h r

/--
Instance `RingHom.applyMulSemiringAction` / 实例 `RingHom.applyMulSemiringAction`

English:
instance RingHom.applyMulSemiringAction
  signature: : MulSemiringAction (R ->+* R) R where
  body: (· <| ·)
  smul_one := map_one
  smul_mul := map_mul
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]

中文:
实例 RingHom.applyMulSemiringAction
  签名: : MulSemiringAction (R ->+* R) R where
  定义体: (· <| ·)
  smul_one := map_one
  smul_mul := map_mul
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
-/
instance RingHom.applyMulSemiringAction : MulSemiringAction (R ->+* R) R where
  smul := (· <| ·)
  smul_one := map_one
  smul_mul := map_mul
  smul_zero := map_zero
  smul_add := map_add
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/--
theorem `RingHom.smul_def` / 定理 `RingHom.smul_def`

English:
theorem RingHom.smul_def
  given: (f : R ->+* R) (a : R)
  statement: f • a = f a
  proof: rfl

中文:
定理 RingHom.smul_def
  条件: (f : R ->+* R) (a : R)
  结论: f • a = f a
  证明: rfl
-/
protected theorem RingHom.smul_def (f : R ->+* R) (a : R) : f • a = f a :=
  rfl

/--
Instance `RingHom.applyFaithfulSMul` / 实例 `RingHom.applyFaithfulSMul`

English:
instance RingHom.applyFaithfulSMul
  signature: : FaithfulSMul (R ->+* R) R
  body: ⟨fun {_ _} h => RingHom.ext h⟩

中文:
实例 RingHom.applyFaithfulSMul
  签名: : FaithfulSMul (R ->+* R) R
  定义体: ⟨fun {_ _} h => RingHom.ext h⟩

Depends on / 依赖: RingHom, RingHom.ext
-/
instance RingHom.applyFaithfulSMul : FaithfulSMul (R ->+* R) R :=
  ⟨fun {_ _} h => RingHom.ext h⟩

section

variable {M N}

/--
Definition of `MulSemiringAction.compHom` / `MulSemiringAction.compHom` 的定义

English:
abbreviation MulSemiringAction.compHom
  signature: (f : N ->* M) [MulSemiringAction M R]
  body: { DistribMulAction.compHom R f, MulDistribMulAction.compHom R f with }

中文:
缩写 MulSemiringAction.compHom
  签名: (f : N ->* M) [MulSemiringAction M R]
  定义体: { DistribMulAction.compHom R f, MulDistribMulAction.compHom R f with }

Depends on / 依赖: DistribMulAction, DistribMulAction.compHom, MulDistribMulAction, MulDistribMulAction.compHom, compHom
-/
abbrev MulSemiringAction.compHom (f : N ->* M) [MulSemiringAction M R] : MulSemiringAction N R :=
  { DistribMulAction.compHom R f, MulDistribMulAction.compHom R f with }

end

section SimpLemmas

attribute [simp] smul_one smul_mul' smul_zero smul_add

end SimpLemmas

end Semiring
