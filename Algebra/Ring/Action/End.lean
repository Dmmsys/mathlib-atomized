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

/--
Instance `applyMulSemiringAction` / 实例 `applyMulSemiringAction`

English:
instance applyMulSemiringAction
  signature: :
  body: (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  smul_one := map_one
  smul_mul := map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]

中文:
实例 applyMulSemiringAction
  签名: :
  定义体: (· <| ·)
  smul_zero := map_zero
  smul_add := map_add
  smul_one := map_one
  smul_mul := map_mul
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
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
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (f : RingAut R) (r : R)
  statement: f • r = f r
  proof: rfl

中文:
定理 smul_def
  条件: (f : RingAut R) (r : R)
  结论: f • r = f r
  证明: rfl
-/
protected theorem smul_def (f : RingAut R) (r : R) : f • r = f r :=
  rfl

/--
Instance `apply_faithfulSMul` / 实例 `apply_faithfulSMul`

English:
instance apply_faithfulSMul
  signature: : FaithfulSMul (RingAut R) R
  body: ⟨RingEquiv.ext⟩

中文:
实例 apply_faithfulSMul
  签名: : 忠实标量乘法 (RingAut R) R
  定义体: ⟨RingEquiv.ext⟩

Depends on / 依赖: RingEquiv, RingEquiv.ext
-/
instance apply_faithfulSMul : FaithfulSMul (RingAut R) R :=
  ⟨RingEquiv.ext⟩

variable (G R)

/-- Each element of the group defines a ring automorphism.

This is a stronger version of `DistribMulAction.toAddAut` and
`MulDistribMulAction.toMulAut`. -/
@[simps]
/--
Definition of `_root_.MulSemiringAction.toRingAut` / `_root_.MulSemiringAction.toRingAut` 的定义

English:
definition _root_.MulSemiringAction.toRingAut
  signature: [MulSemiringAction G R]
  body: MulSemiringAction.toRingEquiv G R
map_mul' g h := RingEquiv.ext mul_smul g h
map_one' := RingEquiv.ext one_smul _

中文:
定义 _root_.MulSemiring作用.toRingAut
  签名: [MulSemiring作用 G R]
  定义体: MulSemiringAction.toRingEquiv G R
map_mul' g h := RingEquiv.ext mul_smul g h
map_one' := RingEquiv.ext one_smul _

Depends on / 依赖: MulSemiringAction, MulSemiringAction.toRingEquiv, toRingEquiv
-/
def _root_.MulSemiringAction.toRingAut [MulSemiringAction G R] :
    G ->* RingAut R where
  toFun := MulSemiringAction.toRingEquiv G R
map_mul' g h := RingEquiv.ext mul_smul g h
map_one' := RingEquiv.ext one_smul _

end RingAut
