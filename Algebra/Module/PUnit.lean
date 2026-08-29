/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.PUnit

/-!
# Instances on PUnit

This file collects facts about module structures on the one-element type
-/

public section

namespace PUnit

variable {R S : Type*}

@[to_additive]
/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: : SMul R PUnit
  body: ⟨fun _ _ => unit⟩

@[to_additive (attr := simp)]

中文:
实例 smul
  签名: : SMul R PUnit
  定义体: ⟨fun _ _ => unit⟩

@[to_additive (attr := simp)]
-/
instance smul : SMul R PUnit :=
  ⟨fun _ _ => unit⟩

@[to_additive (attr := simp)]
/--
theorem `smul_eq` / 定理 `smul_eq`

English:
theorem smul_eq
  given: {R : Type*} (y : PUnit) (r : R)
  statement: r • y = unit
  proof: rfl

@[to_additive]

中文:
定理 smul_eq
  条件: {R : 类型} (y : PUnit) (r : R)
  结论: r • y = unit
  证明: rfl

@[to_additive]
-/
theorem smul_eq {R : Type*} (y : PUnit) (r : R) : r • y = unit :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCentralScalar R PUnit
  body: ⟨fun _ _ => rfl⟩

@[to_additive]

中文:
实例 :
  签名: IsCentralScalar R PUnit
  定义体: ⟨fun _ _ => rfl⟩

@[to_additive]
-/
instance : IsCentralScalar R PUnit :=
  ⟨fun _ _ => rfl⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass R S PUnit
  body: ⟨fun _ _ _ => rfl⟩

@[to_additive]

中文:
实例 :
  签名: SMulCommClass R S PUnit
  定义体: ⟨fun _ _ _ => rfl⟩

@[to_additive]
-/
instance : SMulCommClass R S PUnit :=
  ⟨fun _ _ _ => rfl⟩

@[to_additive]
/--
Instance `instIsScalarTowerOfSMul` / 实例 `instIsScalarTowerOfSMul`

English:
instance instIsScalarTowerOfSMul
  signature: [SMul R S]
  body: ⟨fun _ _ _ => rfl⟩

中文:
实例 instIsScalarTowerOfSMul
  签名: [SMul R S]
  定义体: ⟨fun _ _ _ => rfl⟩
-/
instance instIsScalarTowerOfSMul [SMul R S] : IsScalarTower R S PUnit :=
  ⟨fun _ _ _ => rfl⟩

/--
Instance `smulWithZero` / 实例 `smulWithZero`

English:
instance smulWithZero
  signature: [Zero R]
  body: PUnit.smul
  smul_zero := by subsingleton
  zero_smul := by subsingleton

中文:
实例 smulWithZero
  签名: [Zero R]
  定义体: PUnit.smul
  smul_zero := by subsingleton
  zero_smul := by subsingleton

Depends on / 依赖: PUnit.smul
-/
instance smulWithZero [Zero R] : SMulWithZero R PUnit where
  __ := PUnit.smul
  smul_zero := by subsingleton
  zero_smul := by subsingleton

/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: [Monoid R]
  body: PUnit.smul
  one_smul := by subsingleton
  mul_smul := by subsingleton

中文:
实例 mulAction
  签名: [Monoid R]
  定义体: PUnit.smul
  one_smul := by subsingleton
  mul_smul := by subsingleton

Depends on / 依赖: PUnit.smul
-/
instance mulAction [Monoid R] : MulAction R PUnit where
  __ := PUnit.smul
  one_smul := by subsingleton
  mul_smul := by subsingleton

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: [Monoid R]
  body: PUnit.mulAction
  smul_zero := by subsingleton
  smul_add := by subsingleton

中文:
实例 distribMulAction
  签名: [Monoid R]
  定义体: PUnit.mulAction
  smul_zero := by subsingleton
  smul_add := by subsingleton

Depends on / 依赖: PUnit.mulAction, mulAction
-/
instance distribMulAction [Monoid R] : DistribMulAction R PUnit where
  __ := PUnit.mulAction
  smul_zero := by subsingleton
  smul_add := by subsingleton

/--
Instance `mulDistribMulAction` / 实例 `mulDistribMulAction`

English:
instance mulDistribMulAction
  signature: [Monoid R]
  body: PUnit.mulAction
  smul_mul := by subsingleton
  smul_one := by subsingleton

中文:
实例 mulDistribMulAction
  签名: [Monoid R]
  定义体: PUnit.mulAction
  smul_mul := by subsingleton
  smul_one := by subsingleton

Depends on / 依赖: PUnit.mulAction, mulAction
-/
instance mulDistribMulAction [Monoid R] : MulDistribMulAction R PUnit where
  __ := PUnit.mulAction
  smul_mul := by subsingleton
  smul_one := by subsingleton

/--
Instance `mulSemiringAction` / 实例 `mulSemiringAction`

English:
instance mulSemiringAction
  signature: [Semiring R]
  body: { PUnit.distribMulAction, PUnit.mulDistribMulAction with }

中文:
实例 mulSemiringAction
  签名: [Semiring R]
  定义体: { PUnit.distribMulAction, PUnit.mulDistribMulAction with }

Depends on / 依赖: PUnit.distribMulAction, PUnit.mulDistribMulAction, distribMulAction, mulDistribMulAction
-/
instance mulSemiringAction [Semiring R] : MulSemiringAction R PUnit :=
  { PUnit.distribMulAction, PUnit.mulDistribMulAction with }

/--
Instance `mulActionWithZero` / 实例 `mulActionWithZero`

English:
instance mulActionWithZero
  signature: [MonoidWithZero R]
  body: { PUnit.mulAction, PUnit.smulWithZero with }

中文:
实例 mulActionWithZero
  签名: [MonoidWithZero R]
  定义体: { PUnit.mulAction, PUnit.smulWithZero with }

Depends on / 依赖: PUnit.mulAction, PUnit.smulWithZero, mulAction, smulWithZero
-/
instance mulActionWithZero [MonoidWithZero R] : MulActionWithZero R PUnit :=
  { PUnit.mulAction, PUnit.smulWithZero with }

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: [Semiring R]
  body: PUnit.distribMulAction
  add_smul := by subsingleton
  zero_smul := by subsingleton

@[to_additive]

中文:
实例 module
  签名: [Semiring R]
  定义体: PUnit.distribMulAction
  add_smul := by subsingleton
  zero_smul := by subsingleton

@[to_additive]

Depends on / 依赖: PUnit.distribMulAction, distribMulAction
-/
instance module [Semiring R] : Module R PUnit where
  __ := PUnit.distribMulAction
  add_smul := by subsingleton
  zero_smul := by subsingleton

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul PUnit R
  body: x

中文:
实例 :
  签名: SMul PUnit R
  定义体: x
-/
instance : SMul PUnit R where smul _ x := x

/-- The one-element type acts trivially on every element. -/
@[to_additive (attr := simp)]
/--
lemma `smul_eq'` / 引理 `smul_eq'`

English:
lemma smul_eq'
  given: (r : PUnit) (a : R)
  statement: r • a = a
  proof: rfl

中文:
引理 smul_eq'
  条件: (r : PUnit) (a : R)
  结论: r • a = a
  证明: rfl
-/
lemma smul_eq' (r : PUnit) (a : R) : r • a = a := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R S] : SMulCommClass PUnit R S
  body: ⟨by simp⟩

中文:
实例 [SMul
  签名: R S] : SMulCommClass PUnit R S
  定义体: ⟨by simp⟩
-/
@[to_additive] instance [SMul R S] : SMulCommClass PUnit R S := ⟨by simp⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: R S] : IsScalarTower PUnit R S
  body: ⟨by simp⟩

中文:
实例 [SMul
  签名: R S] : IsScalarTower PUnit R S
  定义体: ⟨by simp⟩
-/
instance [SMul R S] : IsScalarTower PUnit R S := ⟨by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction PUnit R
  body: (inferInstance : SMul PUnit R)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

中文:
实例 :
  签名: MulAction PUnit R
  定义体: (inferInstance : SMul PUnit R)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
-/
instance : MulAction PUnit R where
  __ := (inferInstance : SMul PUnit R)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] : SMulZeroClass PUnit R where
  body: (inferInstance : SMul PUnit R)
  smul_zero _ := rfl

中文:
实例 [Zero
  签名: R] : SMulZeroClass PUnit R where
  定义体: (inferInstance : SMul PUnit R)
  smul_zero _ := rfl
-/
instance [Zero R] : SMulZeroClass PUnit R where
  __ := (inferInstance : SMul PUnit R)
  smul_zero _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: R] : DistribMulAction PUnit R where
  body: (inferInstance : MulAction PUnit R)
  __ := (inferInstance : SMulZeroClass PUnit R)
  smul_add _ _ _ := rfl

中文:
实例 [AddMonoid
  签名: R] : DistribMulAction PUnit R where
  定义体: (inferInstance : MulAction PUnit R)
  __ := (inferInstance : SMulZeroClass PUnit R)
  smul_add _ _ _ := rfl

Depends on / 依赖: MulAction
-/
instance [AddMonoid R] : DistribMulAction PUnit R where
  __ := (inferInstance : MulAction PUnit R)
  __ := (inferInstance : SMulZeroClass PUnit R)
  smul_add _ _ _ := rfl

end PUnit
