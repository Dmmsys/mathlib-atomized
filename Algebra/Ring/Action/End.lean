/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Ring.Action.Group
public import Mathlib.Algebra.Ring.Aut

/-!
# Ring automorphisms

This file defines the automorphism group structure on `RingAut R := RingEquiv R R`.

## Implementation notes

The definition of multiplication in the automorphism group agrees with function composition,
multiplication in `Equiv.Perm`, and multiplication in `CategoryTheory.End`, but not with
`CategoryTheory.comp`.

This file is kept separate from `Mathlib/Algebra/Ring/Equiv.lean` so that
`Mathlib/Data/Fintype/Perm.lean` is free to use equivalences (and other files that use them) before
the group structure is defined.

## Tags

ring aut
-/

@[expose] public section

namespace RingAut
variable {G R : Type*} [Group G] [Semiring R]

/-- The tautological action by the group of automorphism of a ring `R` on `R`. -/
/-
**RingAut.applyMulSemiringAction** 是 Mathlib 中的一个实例，位于命名空间 `RingAut`。
形式化陈述：applyMulSemiringAction : MulSemiringAction (RingAut R) R where smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological action by the group of automorphism of a ring `R` on `R`.
-/
instance applyMulSemiringAction :
    MulSemiringAction (RingAut R) R where
  smul := (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  smul_one := map_one
  smul_mul := map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
/-
**RingAut.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `RingAut`。
形式化陈述：∀ {R : Type u_2} [inst : Semiring R] (f : RingAut R) (r : R), f • r = f r
参数：f : RingAut R；r : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem smul_def (f : RingAut R) (r : R) : f • r = f r :=
  rfl
/-
**RingAut.apply_faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `RingAut`。
形式化陈述：apply_faithfulSMul : FaithfulSMul (RingAut R) R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
-/
instance apply_faithfulSMul : FaithfulSMul (RingAut R) R :=
  ⟨RingEquiv.ext⟩

variable (G R)

/-- Each element of the group defines a ring automorphism.

This is a stronger version of `DistribMulAction.toAddAut` and
`MulDistribMulAction.toMulAut`. -/
@[simps]
/-
**RingAut._root_.MulSemiringAction.toRingAut** 是 Mathlib 中的一个定义，位于命名空间 `RingAut`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the group defines a ring automorphism.

This is a stronger version of `DistribMulAction.toAddAut` and
`MulDistribMulAction.toMulAut`.
-/
def _root_.MulSemiringAction.toRingAut [MulSemiringAction G R] :
    G →* RingAut R where
  toFun := MulSemiringAction.toRingEquiv G R
  map_mul' g h := RingEquiv.ext <| mul_smul g h
  map_one' := RingEquiv.ext <| one_smul _

end RingAut

