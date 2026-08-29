/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.GroupWithZero.ULift
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.ULift

/-!
# `ULift` instances for module and multiplicative actions

This file defines instances for `Module`, `MulAction` and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ULift.moduleEquiv : ULift M ≃ₗ[R] M`.
-/

@[expose] public section


namespace ULift

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}

@[to_additive]
/--
Instance `smulLeft` / 实例 `smulLeft`

English:
instance smulLeft
  signature: [SMul R M]
  body: ⟨fun s x => s.down • x⟩

@[to_additive (attr := simp)]

中文:
实例 smulLeft
  签名: [SMul R M]
  定义体: ⟨fun s x => s.down • x⟩

@[to_additive (attr := simp)]

Depends on / 依赖: s.down
-/
instance smulLeft [SMul R M] : SMul (ULift R) M :=
  ⟨fun s x => s.down • x⟩

@[to_additive (attr := simp)]
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: [SMul R M] (s : ULift R) (x : M)
  statement: s • x = s.down • x
  proof: rfl

中文:
定理 smul_def
  条件: [SMul R M] (s : ULift R) (x : M)
  结论: s • x = s.down • x
  证明: rfl
-/
theorem smul_def [SMul R M] (s : ULift R) (x : M) : s • x = s.down • x :=
  rfl

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N]
  body: ⟨fun x y z => show (x.down • y) • z = x.down • y • z from smul_assoc _ _ _⟩

中文:
实例 isScalarTower
  签名: [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N]
  定义体: ⟨fun x y z => show (x.down • y) • z = x.down • y • z from smul_assoc _ _ _⟩

Depends on / 依赖: smul_assoc, x.down
-/
instance isScalarTower [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower (ULift R) M N :=
  ⟨fun x y z => show (x.down • y) • z = x.down • y • z from smul_assoc _ _ _⟩

/--
Instance `isScalarTower'` / 实例 `isScalarTower'`

English:
instance isScalarTower'
  signature: [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N]
  body: ⟨fun x y z => show (x • y.down) • z = x • y.down • z from smul_assoc _ _ _⟩

中文:
实例 isScalarTower'
  签名: [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N]
  定义体: ⟨fun x y z => show (x • y.down) • z = x • y.down • z from smul_assoc _ _ _⟩

Depends on / 依赖: smul_assoc, y.down
-/
instance isScalarTower' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower R (ULift M) N :=
  ⟨fun x y z => show (x • y.down) • z = x • y.down • z from smul_assoc _ _ _⟩

/--
Instance `isScalarTower''` / 实例 `isScalarTower''`

English:
instance isScalarTower''
  signature: [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N]
  body: ⟨fun x y z => show up ((x • y) • z.down) = ⟨x • y • z.down⟩ by rw [smul_assoc]⟩

中文:
实例 isScalarTower''
  签名: [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N]
  定义体: ⟨fun x y z => show up ((x • y) • z.down) = ⟨x • y • z.down⟩ by rw [smul_assoc]⟩

Depends on / 依赖: smul_assoc, z.down
-/
instance isScalarTower'' [SMul R M] [SMul M N] [SMul R N] [IsScalarTower R M N] :
    IsScalarTower R M (ULift N) :=
  ⟨fun x y z => show up ((x • y) • z.down) = ⟨x • y • z.down⟩ by rw [smul_assoc]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R M] [SMul Rᵐᵒᵖ M] [IsCentralScalar R M] : IsCentralScalar R (ULift M)
  body: ⟨fun r m => congr_arg up op_smul_eq_smul r m.down⟩

@[to_additive]

中文:
实例 [SMul
  签名: R M] [SMul Rᵐᵒᵖ M] [IsCentralScalar R M] : IsCentralScalar R (ULift M)
  定义体: ⟨fun r m => congr_arg up op_smul_eq_smul r m.down⟩

@[to_additive]

Depends on / 依赖: congr_arg, m.down, op_smul_eq_smul
-/
instance [SMul R M] [SMul Rᵐᵒᵖ M] [IsCentralScalar R M] : IsCentralScalar R (ULift M) :=
⟨fun r m => congr_arg up op_smul_eq_smul r m.down⟩

@[to_additive]
/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: [Monoid R] [MulAction R M]
  body: mul_smul _ _
  one_smul := one_smul _

@[to_additive]

中文:
实例 mulAction
  签名: [Monoid R] [MulAction R M]
  定义体: mul_smul _ _
  one_smul := one_smul _

@[to_additive]

Depends on / 依赖: mul_smul
-/
instance mulAction [Monoid R] [MulAction R M] : MulAction (ULift R) M where
  mul_smul _ _ := mul_smul _ _
  one_smul := one_smul _

@[to_additive]
/--
Instance `mulAction'` / 实例 `mulAction'`

English:
instance mulAction'
  signature: [Monoid R] [MulAction R M]
  body: fun _ _ _ => congr_arg ULift.up mul_smul _ _ _
one_smul := fun _ => congr_arg ULift.up one_smul _ _

中文:
实例 mulAction'
  签名: [Monoid R] [MulAction R M]
  定义体: fun _ _ _ => congr_arg ULift.up mul_smul _ _ _
one_smul := fun _ => congr_arg ULift.up one_smul _ _

Depends on / 依赖: ULift.up, congr_arg, mul_smul
-/
instance mulAction' [Monoid R] [MulAction R M] : MulAction R (ULift M) where
mul_smul := fun _ _ _ => congr_arg ULift.up mul_smul _ _ _
one_smul := fun _ => congr_arg ULift.up one_smul _ _

/--
Instance `smulZeroClass` / 实例 `smulZeroClass`

English:
instance smulZeroClass
  signature: [Zero M] [SMulZeroClass R M]
  body: { ULift.smulLeft with smul_zero := fun _ => smul_zero _ }

中文:
实例 smulZeroClass
  签名: [Zero M] [SMulZeroClass R M]
  定义体: { ULift.smulLeft with smul_zero := fun _ => smul_zero _ }

Depends on / 依赖: ULift.smulLeft, smulLeft, smul_zero
-/
instance smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass (ULift R) M :=
  { ULift.smulLeft with smul_zero := fun _ => smul_zero _ }

/--
Instance `smulZeroClass'` / 实例 `smulZeroClass'`

English:
instance smulZeroClass'
  signature: [Zero M] [SMulZeroClass R M]
  body: by { ext; simp [smul_zero] }

中文:
实例 smulZeroClass'
  签名: [Zero M] [SMulZeroClass R M]
  定义体: by { ext; simp [smul_zero] }

Depends on / 依赖: smul_zero
-/
instance smulZeroClass' [Zero M] [SMulZeroClass R M] : SMulZeroClass R (ULift M) where
  smul_zero c := by { ext; simp [smul_zero] }

/--
Instance `distribSMul` / 实例 `distribSMul`

English:
instance distribSMul
  signature: [AddZeroClass M] [DistribSMul R M]
  body: smul_add _

中文:
实例 distribSMul
  签名: [AddZeroClass M] [DistribSMul R M]
  定义体: smul_add _

Depends on / 依赖: smul_add
-/
instance distribSMul [AddZeroClass M] [DistribSMul R M] : DistribSMul (ULift R) M where
  smul_add _ := smul_add _

/--
Instance `distribSMul'` / 实例 `distribSMul'`

English:
instance distribSMul'
  signature: [AddZeroClass M] [DistribSMul R M]
  body: by
    ext
    simp [smul_add]

中文:
实例 distribSMul'
  签名: [AddZeroClass M] [DistribSMul R M]
  定义体: by
    ext
    simp [smul_add]

Depends on / 依赖: IsOrderedCancelSMul, smul_add
-/
instance distribSMul' [AddZeroClass M] [DistribSMul R M] : DistribSMul R (ULift M) where
  smul_add c f g := by
    ext
    simp [smul_add]

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: [Monoid R] [AddMonoid M] [DistribMulAction R M]
  body: { ULift.mulAction, ULift.distribSMul with }

中文:
实例 distribMulAction
  签名: [Monoid R] [AddMonoid M] [DistribMulAction R M]
  定义体: { ULift.mulAction, ULift.distribSMul with }

Depends on / 依赖: ULift.distribSMul, ULift.mulAction, distribSMul, mulAction
-/
instance distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction (ULift R) M :=
  { ULift.mulAction, ULift.distribSMul with }

/--
Instance `distribMulAction'` / 实例 `distribMulAction'`

English:
instance distribMulAction'
  signature: [Monoid R] [AddMonoid M] [DistribMulAction R M]
  body: { ULift.mulAction', ULift.distribSMul' with }

中文:
实例 distribMulAction'
  签名: [Monoid R] [AddMonoid M] [DistribMulAction R M]
  定义体: { ULift.mulAction', ULift.distribSMul' with }

Depends on / 依赖: ULift.distribSMul, ULift.mulAction, distribSMul, mulAction
-/
instance distribMulAction' [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction R (ULift M) :=
  { ULift.mulAction', ULift.distribSMul' with }

/--
Instance `mulDistribMulAction` / 实例 `mulDistribMulAction`

English:
instance mulDistribMulAction
  signature: [Monoid R] [Monoid M] [MulDistribMulAction R M]
  body: smul_one _
  smul_mul _ := smul_mul' _

中文:
实例 mulDistribMulAction
  签名: [Monoid R] [Monoid M] [MulDistribMulAction R M]
  定义体: smul_one _
  smul_mul _ := smul_mul' _

Depends on / 依赖: smul_one
-/
instance mulDistribMulAction [Monoid R] [Monoid M] [MulDistribMulAction R M] :
    MulDistribMulAction (ULift R) M where
  smul_one _ := smul_one _
  smul_mul _ := smul_mul' _

/--
Instance `mulDistribMulAction'` / 实例 `mulDistribMulAction'`

English:
instance mulDistribMulAction'
  signature: [Monoid R] [Monoid M] [MulDistribMulAction R M]
  body: { ULift.mulAction' with
    smul_one := fun _ => by
      ext
      simp [smul_one]
    smul_mul := fun _ _ _ => by
      ext
      simp [smul_mul'] }

中文:
实例 mulDistribMulAction'
  签名: [Monoid R] [Monoid M] [MulDistribMulAction R M]
  定义体: { ULift.mulAction' with
    smul_one := fun _ => by
      ext
      simp [smul_one]
    smul_mul := fun _ _ _ => by
      ext
      simp [smul_mul'] }

Depends on / 依赖: ULift.mulAction, mulAction, smul_mul, smul_one
-/
instance mulDistribMulAction' [Monoid R] [Monoid M] [MulDistribMulAction R M] :
    MulDistribMulAction R (ULift M) :=
  { ULift.mulAction' with
    smul_one := fun _ => by
      ext
      simp [smul_one]
    smul_mul := fun _ _ _ => by
      ext
      simp [smul_mul'] }

/--
Instance `smulWithZero` / 实例 `smulWithZero`

English:
instance smulWithZero
  signature: [Zero R] [Zero M] [SMulWithZero R M]
  body: { ULift.smulLeft with
    smul_zero := fun _ => smul_zero _
    zero_smul := zero_smul _ }

中文:
实例 smulWithZero
  签名: [Zero R] [Zero M] [SMulWithZero R M]
  定义体: { ULift.smulLeft with
    smul_zero := fun _ => smul_zero _
    zero_smul := zero_smul _ }

Depends on / 依赖: ULift.smulLeft, smulLeft, smul_zero, zero_smul
-/
instance smulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero (ULift R) M :=
  { ULift.smulLeft with
    smul_zero := fun _ => smul_zero _
    zero_smul := zero_smul _ }

/--
Instance `smulWithZero'` / 实例 `smulWithZero'`

English:
instance smulWithZero'
  signature: [Zero R] [Zero M] [SMulWithZero R M]
  body: ULift.ext _ _ smul_zero _
zero_smul _ := ULift.ext _ _ zero_smul _ _

中文:
实例 smulWithZero'
  签名: [Zero R] [Zero M] [SMulWithZero R M]
  定义体: ULift.ext _ _ smul_zero _
zero_smul _ := ULift.ext _ _ zero_smul _ _

Depends on / 依赖: ULift.ext, smul_zero
-/
instance smulWithZero' [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (ULift M) where
smul_zero _ := ULift.ext _ _ smul_zero _
zero_smul _ := ULift.ext _ _ zero_smul _ _

/--
Instance `mulActionWithZero` / 实例 `mulActionWithZero`

English:
instance mulActionWithZero
  signature: [MonoidWithZero R] [Zero M] [MulActionWithZero R M]
  body: { ULift.smulWithZero with
    one_smul := one_smul _
    mul_smul := mul_smul }

中文:
实例 mulActionWithZero
  签名: [MonoidWithZero R] [Zero M] [MulActionWithZero R M]
  定义体: { ULift.smulWithZero with
    one_smul := one_smul _
    mul_smul := mul_smul }

Depends on / 依赖: ULift.smulWithZero, mul_smul, one_smul, smulWithZero
-/
instance mulActionWithZero [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero (ULift R) M :=
  { ULift.smulWithZero with
    one_smul := one_smul _
    mul_smul := mul_smul }

/--
Instance `mulActionWithZero'` / 实例 `mulActionWithZero'`

English:
instance mulActionWithZero'
  signature: [MonoidWithZero R] [Zero M] [MulActionWithZero R M]
  body: { ULift.smulWithZero' with
    one_smul := one_smul _
    mul_smul := mul_smul }

中文:
实例 mulActionWithZero'
  签名: [MonoidWithZero R] [Zero M] [MulActionWithZero R M]
  定义体: { ULift.smulWithZero' with
    one_smul := one_smul _
    mul_smul := mul_smul }

Depends on / 依赖: ULift.smulWithZero, mul_smul, one_smul, smulWithZero
-/
instance mulActionWithZero' [MonoidWithZero R] [Zero M] [MulActionWithZero R M] :
    MulActionWithZero R (ULift M) :=
  { ULift.smulWithZero' with
    one_smul := one_smul _
    mul_smul := mul_smul }

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: [Semiring R] [AddCommMonoid M] [Module R M]
  body: { ULift.smulWithZero with
    add_smul := fun _ _ => add_smul _ _
    smul_add := smul_add
    one_smul := one_smul _
    mul_smul := mul_smul }

中文:
实例 module
  签名: [Semiring R] [AddCommMonoid M] [Module R M]
  定义体: { ULift.smulWithZero with
    add_smul := fun _ _ => add_smul _ _
    smul_add := smul_add
    one_smul := one_smul _
    mul_smul := mul_smul }

Depends on / 依赖: ULift.smulWithZero, add_smul, mul_smul, one_smul, smulWithZero, smul_add
-/
instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module (ULift R) M :=
  { ULift.smulWithZero with
    add_smul := fun _ _ => add_smul _ _
    smul_add := smul_add
    one_smul := one_smul _
    mul_smul := mul_smul }

/--
Instance `module'` / 实例 `module'`

English:
instance module'
  signature: [Semiring R] [AddCommMonoid M] [Module R M]
  body: { ULift.smulWithZero' with
add_smul := fun _ _ _ => ULift.ext _ _ add_smul _ _ _
    one_smul := one_smul _
    mul_smul := mul_smul
    smul_add := smul_add }

中文:
实例 module'
  签名: [Semiring R] [AddCommMonoid M] [Module R M]
  定义体: { ULift.smulWithZero' with
add_smul := fun _ _ _ => ULift.ext _ _ add_smul _ _ _
    one_smul := one_smul _
    mul_smul := mul_smul
    smul_add := smul_add }

Depends on / 依赖: ULift.ext, ULift.smulWithZero, add_smul, mul_smul, one_smul, smulWithZero, smul_add
-/
instance module' [Semiring R] [AddCommMonoid M] [Module R M] : Module R (ULift M) :=
  { ULift.smulWithZero' with
add_smul := fun _ _ _ => ULift.ext _ _ add_smul _ _ _
    one_smul := one_smul _
    mul_smul := mul_smul
    smul_add := smul_add }

/-- The `R`-linear equivalence between `ULift M` and `M`.

This is a linear version of `AddEquiv.ulift`. -/
@[simps apply symm_apply]
/--
Definition of `moduleEquiv` / `moduleEquiv` 的定义

English:
definition moduleEquiv
  signature: [Semiring R] [AddCommMonoid M] [Module R M]
  body: ULift.down
  invFun := ULift.up
  map_smul' _ _ := rfl
  __ := AddEquiv.ulift

中文:
定义 moduleEquiv
  签名: [Semiring R] [AddCommMonoid M] [Module R M]
  定义体: ULift.down
  invFun := ULift.up
  map_smul' _ _ := rfl
  __ := AddEquiv.ulift

Depends on / 依赖: ULift.down
-/
def moduleEquiv [Semiring R] [AddCommMonoid M] [Module R M] : ULift.{w} M ≃ₗ[R] M where
  toFun := ULift.down
  invFun := ULift.up
  map_smul' _ _ := rfl
  __ := AddEquiv.ulift

end ULift
