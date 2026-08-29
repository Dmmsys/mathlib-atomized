/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Module.NatInt

/-!
# Module structure and endomorphisms

In this file, we define `Module.toAddMonoidEnd`, which is `(•)` as a monoid homomorphism.
We use this to prove some results on scalar multiplication by integers.
-/

@[expose] public section

assert_not_exists RelIso Multiset Set.indicator Pi.single_smul₀ Field

open Function Set

universe u v

variable {R S M M₂ : Type*}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

/--
theorem `AddMonoid.End.natCast_def` / 定理 `AddMonoid.End.natCast_def`

English:
theorem AddMonoid.End.natCast_def
  given: (n : Nat)
  proof: rfl

中文:
定理 AddMonoid.End.natCast_def
  条件: (n : 自然数)
  证明: rfl
-/
theorem AddMonoid.End.natCast_def (n : Nat) :
    (↑n : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd Nat M n :=
  rfl

variable (R M)

set_option backward.isDefEq.respectTransparency false in
/-- `(•)` as an `AddMonoidHom`.

This is a stronger version of `DistribMulAction.toAddMonoidEnd` -/
@[simps! apply_apply]
/--
Definition of `Module.toAddMonoidEnd` / `Module.toAddMonoidEnd` 的定义

English:
definition Module.toAddMonoidEnd
  signature: : R ->+* AddMonoid.End M
  body: { DistribMulAction.toAddMonoidEnd R M with
    map_zero' := AddMonoidHom.ext fun r => by simp
    map_add' x y :=
      AddMonoidHom.ext fun r => by simp [(AddMonoidHom.add_apply), add_smul] }

中文:
定义 Module.toAddMonoidEnd
  签名: : R ->+* AddMonoid.End M
  定义体: { DistribMulAction.toAddMonoidEnd R M with
    map_zero' := AddMonoidHom.ext fun r => by simp
    map_add' x y :=
      AddMonoidHom.ext fun r => by simp [(AddMonoidHom.add_apply), add_smul] }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.add_apply, AddMonoidHom.ext, DistribMulAction, DistribMulAction.toAddMonoidEnd, add_apply, add_smul, map_add, map_zero, toAddMonoidEnd
-/
def Module.toAddMonoidEnd : R ->+* AddMonoid.End M :=
  { DistribMulAction.toAddMonoidEnd R M with
    map_zero' := AddMonoidHom.ext fun r => by simp
    map_add' x y :=
      AddMonoidHom.ext fun r => by simp [(AddMonoidHom.add_apply), add_smul] }

/--
Definition of `smulAddHom` / `smulAddHom` 的定义

English:
definition smulAddHom
  signature: : R ->+ M ->+ M
  body: (Module.toAddMonoidEnd R M).toAddMonoidHom

中文:
定义 smulAddHom
  签名: : R ->+ M ->+ M
  定义体: (Module.toAddMonoidEnd R M).toAddMonoidHom

Depends on / 依赖: Module, Module.toAddMonoidEnd, toAddMonoidEnd, toAddMonoidHom
-/
def smulAddHom : R ->+ M ->+ M :=
  (Module.toAddMonoidEnd R M).toAddMonoidHom

variable {R M}

@[simp]
/--
theorem `smulAddHom_apply` / 定理 `smulAddHom_apply`

English:
theorem smulAddHom_apply
  statement: smulAddHom R M r x = r • x
  proof: rfl

中文:
定理 smulAddHom_apply
  结论: smulAddHom R M r x = r • x
  证明: rfl
-/
theorem smulAddHom_apply : smulAddHom R M r x = r • x :=
  rfl

variable {x}

/--
lemma `IsAddUnit.smul_left` / 引理 `IsAddUnit.smul_left`

English:
lemma IsAddUnit.smul_left
  given: [DistribSMul S M] (hx : IsAddUnit x) (s : S)
  proof: hx.map (DistribSMul.toAddMonoidHom M s)

中文:
引理 IsAddUnit.smul_left
  条件: [DistribSMul S M] (hx : IsAddUnit x) (s : S)
  证明: hx.map (DistribSMul.toAddMonoidHom M s)

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, hx.map, toAddMonoidHom
-/
lemma IsAddUnit.smul_left [DistribSMul S M] (hx : IsAddUnit x) (s : S) :
    IsAddUnit (s • x) :=
  hx.map (DistribSMul.toAddMonoidHom M s)

variable {r} (x)

/--
lemma `IsAddUnit.smul_right` / 引理 `IsAddUnit.smul_right`

English:
lemma IsAddUnit.smul_right
  given: (hr : IsAddUnit r)
  statement: IsAddUnit (r • x)
  proof: hr.map (AddMonoidHom.flip (smulAddHom R M) x)

中文:
引理 IsAddUnit.smul_right
  条件: (hr : IsAddUnit r)
  结论: IsAddUnit (r • x)
  证明: hr.map (AddMonoidHom.flip (smulAddHom R M) x)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.flip, hr.map, smulAddHom
-/
lemma IsAddUnit.smul_right (hr : IsAddUnit r) : IsAddUnit (r • x) :=
  hr.map (AddMonoidHom.flip (smulAddHom R M) x)

end AddCommMonoid

section AddCommGroup

variable (R M) [Semiring R] [AddCommGroup M]

/--
theorem `AddMonoid.End.intCast_def` / 定理 `AddMonoid.End.intCast_def`

English:
theorem AddMonoid.End.intCast_def
  given: (z : Int)
  proof: rfl

中文:
定理 AddMonoid.End.intCast_def
  条件: (z : 整数)
  证明: rfl
-/
theorem AddMonoid.End.intCast_def (z : Int) :
    (↑z : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd Int M z :=
  rfl

end AddCommGroup
