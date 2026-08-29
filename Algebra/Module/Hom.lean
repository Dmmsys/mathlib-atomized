/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.GroupWithZero.Action.End
public import Mathlib.Algebra.GroupWithZero.Action.Hom
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Bundled Hom instances for module and multiplicative actions

This file defines instances for `Module` on bundled `Hom` types.

These are analogous to the instances in `Algebra.Module.Pi`, but for bundled instead of unbundled
functions.

We also define a bundled versions of `(· • ·)` as `AddMonoidHom.smul`.
-/

@[expose] public section

variable {R S M A B : Type*}

namespace ZeroHom

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B]
  body: ZeroHom.instMulActionWithZero
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

中文:
实例 instModule
  签名: [半环 R] [加法幺半群 A] [加法交换幺半群 B] [模 R B]
  定义体: ZeroHom.instMulActionWithZero
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

Depends on / 依赖: ZeroHom, ZeroHom.instMulActionWithZero, instMulActionWithZero
-/
instance instModule [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] :
    Module R (ZeroHom A B) where
  __ : MulActionWithZero _ _ := ZeroHom.instMulActionWithZero
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

end ZeroHom

/-! ### Instances for `AddMonoidHom` -/

namespace AddMonoidHom

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B]
  body: ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

中文:
实例 instModule
  签名: [半环 R] [加法幺半群 A] [加法交换幺半群 B] [模 R B]
  定义体: ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

Depends on / 依赖: add_smul
-/
instance instModule [Semiring R] [AddMonoid A] [AddCommMonoid B] [Module R B] :
    Module R (A ->+ B) where
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul _ _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instDomMulActModule` / 实例 `instDomMulActModule`

English:
instance instDomMulActModule
  body: AddMonoidHom.ext fun m => by
    simp_rw [AddMonoidHom.add_apply, DomMulAct.smul_addMonoidHom_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := AddMonoidHom.ext fun _ => by
    rw [DomMulAct.smul_addMonoidHom_apply]
    -- TODO there should be a simp lemma for `DomMulAct.mk.symm 0`
    simp [DomMu

中文:
实例 instDomMulActModule
  定义体: AddMonoidHom.ext fun m => by
    simp_rw [AddMonoidHom.add_apply, DomMulAct.smul_addMonoidHom_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := AddMonoidHom.ext fun _ => by
    rw [DomMulAct.smul_addMonoidHom_apply]
    -- TODO there should be a simp lemma for `DomMulAct.mk.symm 0`
    simp [DomMu

Depends on / 依赖: AddMonoidHom, AddMonoidHom.add_apply, AddMonoidHom.ext, DomMulAct, DomMulAct.smul_addMonoidHom_apply, add_apply, add_smul, map_add, simp_rw, smul_addMonoidHom_apply, zero_smul
-/
instance instDomMulActModule
    {S M M₂ : Type*} [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂] [Module S M] :
    Module Sᵈᵐᵃ (M ->+ M₂) where
  add_smul s s' f := AddMonoidHom.ext fun m => by
    simp_rw [AddMonoidHom.add_apply, DomMulAct.smul_addMonoidHom_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := AddMonoidHom.ext fun _ => by
    rw [DomMulAct.smul_addMonoidHom_apply]
    -- TODO there should be a simp lemma for `DomMulAct.mk.symm 0`
    simp [DomMulAct.mk, MulOpposite.opEquiv]

end AddMonoidHom

/-!
### Instances for `AddMonoid.End`

These are direct copies of the instances above.
-/

namespace AddMonoid.End

section

variable [Monoid R] [Monoid S] [AddCommMonoid A]

/--
Instance `instDistribSMul` / 实例 `instDistribSMul`

English:
instance instDistribSMul
  signature: [DistribSMul M A]
  body: inferInstanceAs DistribSMul M (A ->+ A)

中文:
实例 instDistribSMul
  签名: [分配标量乘法 M A]
  定义体: inferInstanceAs DistribSMul M (A ->+ A)

Depends on / 依赖: DistribSMul
-/
instance instDistribSMul [DistribSMul M A] : DistribSMul M (AddMonoid.End A) :=
inferInstanceAs DistribSMul M (A ->+ A)

variable [DistribMulAction R A] [DistribMulAction S A]

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: : DistribMulAction R (AddMonoid.End A)
  body: inferInstanceAs DistribMulAction R (A ->+ A)

中文:
实例 instDistribMulAction
  签名: : 分配乘法作用 R (加法幺半群.End A)
  定义体: inferInstanceAs DistribMulAction R (A ->+ A)

Depends on / 依赖: DistribMulAction
-/
instance instDistribMulAction : DistribMulAction R (AddMonoid.End A) :=
inferInstanceAs DistribMulAction R (A ->+ A)

/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (r : R) (f : AddMonoid.End A)
  statement: ⇑(r • f) = r • ⇑f
  proof: rfl

中文:
定理 coe_smul
  条件: (r : R) (f : 加法幺半群.End A)
  结论: ⇑(r • f) = r • ⇑f
  证明: rfl
-/
@[simp] theorem coe_smul (r : R) (f : AddMonoid.End A) : ⇑(r • f) = r • ⇑f := rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (r : R) (f : AddMonoid.End A) (x : A)
  statement: (r • f) x = r • f x
  proof: rfl

中文:
定理 smul_apply
  条件: (r : R) (f : 加法幺半群.End A) (x : A)
  结论: (r • f) x = r • f x
  证明: rfl
-/
theorem smul_apply (r : R) (f : AddMonoid.End A) (x : A) : (r • f) x = r • f x :=
  rfl

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: [SMulCommClass R S A]
  body: AddMonoidHom.instSMulCommClass

中文:
实例 smulCommClass
  签名: [标量交换类 R S A]
  定义体: AddMonoidHom.instSMulCommClass

Depends on / 依赖: AddMonoidHom, AddMonoidHom.instSMulCommClass, instSMulCommClass
-/
instance smulCommClass [SMulCommClass R S A] : SMulCommClass R S (AddMonoid.End A) :=
  AddMonoidHom.instSMulCommClass

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul R S] [IsScalarTower R S A]
  body: AddMonoidHom.instIsScalarTower

中文:
实例 isScalarTower
  签名: [标量乘法 R S] [标量塔 R S A]
  定义体: AddMonoidHom.instIsScalarTower

Depends on / 依赖: AddMonoidHom, AddMonoidHom.instIsScalarTower, instIsScalarTower
-/
instance isScalarTower [SMul R S] [IsScalarTower R S A] : IsScalarTower R S (AddMonoid.End A) :=
  AddMonoidHom.instIsScalarTower

/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [DistribMulAction Rᵐᵒᵖ A] [IsCentralScalar R A]
  body: AddMonoidHom.instIsCentralScalar

中文:
实例 isCentralScalar
  签名: [分配乘法作用 Rᵐᵒᵖ A] [中心标量 R A]
  定义体: AddMonoidHom.instIsCentralScalar

Depends on / 依赖: AddMonoidHom, AddMonoidHom.instIsCentralScalar, instIsCentralScalar
-/
instance isCentralScalar [DistribMulAction Rᵐᵒᵖ A] [IsCentralScalar R A] :
    IsCentralScalar R (AddMonoid.End A) :=
  AddMonoidHom.instIsCentralScalar

end

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring R] [AddCommMonoid A] [Module R A]
  body: inferInstanceAs Module R (A ->+ A)

中文:
实例 instModule
  签名: [半环 R] [加法交换幺半群 A] [模 R A]
  定义体: inferInstanceAs Module R (A ->+ A)

Depends on / 依赖: Module
-/
instance instModule [Semiring R] [AddCommMonoid A] [Module R A] : Module R (AddMonoid.End A) :=
inferInstanceAs Module R (A ->+ A)

/--
Instance `applyModule` / 实例 `applyModule`

English:
instance applyModule
  signature: [AddCommMonoid A]
  body: rfl
  zero_smul _ := rfl

中文:
实例 applyModule
  签名: [加法交换幺半群 A]
  定义体: rfl
  zero_smul _ := rfl
-/
instance applyModule [AddCommMonoid A] : Module (AddMonoid.End A) A where
  add_smul _ _ _ := rfl
  zero_smul _ := rfl

end AddMonoid.End

/-! ### Miscellaneous morphisms -/

namespace AddMonoidHom

/-- Scalar multiplication on the left as an additive monoid homomorphism.

See also the linear map version of this `Module.End.smulLeft`. -/
@[simps! -fullyApplied, deprecated DistribSMul.toAddMonoidHom (since := "2026-01-07")]
/--
Definition of `smulLeft` / `smulLeft` 的定义

English:
definition smulLeft
  signature: [AddMonoid A] [DistribSMul M A] (c : M)
  body: DistribSMul.toAddMonoidHom _ c

中文:
定义 smulLeft
  签名: [加法幺半群 A] [分配标量乘法 M A] (c : M)
  定义体: DistribSMul.toAddMonoidHom _ c
-/
protected def smulLeft [AddMonoid A] [DistribSMul M A] (c : M) : A ->+ A :=
  DistribSMul.toAddMonoidHom _ c

/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: [Semiring R] [AddCommMonoid M] [Module R M]
  body: (Module.toAddMonoidEnd R M).toAddMonoidHom

中文:
定义 smul
  签名: [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: (Module.toAddMonoidEnd R M).toAddMonoidHom
-/
protected def smul [Semiring R] [AddCommMonoid M] [Module R M] : R ->+ M ->+ M :=
  (Module.toAddMonoidEnd R M).toAddMonoidHom

/--
theorem `coe_smul'` / 定理 `coe_smul'`

English:
theorem coe_smul'
  given: [Semiring R] [AddCommMonoid M] [Module R M]
  proof: rfl

中文:
定理 coe_smul'
  条件: [半环 R] [加法交换幺半群 M] [模 R M]
  证明: rfl
-/
@[simp] theorem coe_smul' [Semiring R] [AddCommMonoid M] [Module R M] :
    ⇑(.smul : R ->+ M ->+ M) = DistribSMul.toAddMonoidHom _ := rfl

end AddMonoidHom
