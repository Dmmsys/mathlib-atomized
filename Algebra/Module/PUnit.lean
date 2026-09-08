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
/-
**PUnit.smul** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：smul : SMul R PUnit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul : SMul R PUnit :=
  ⟨fun _ _ => unit⟩

@[to_additive (attr := simp)]
/-
**PUnit.smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：smul_eq {R : Type*} (y : PUnit) (r : R) : r • y = unit
参数：y : PUnit；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_eq {R : Type*} (y : PUnit) (r : R) : r • y = unit :=
  rfl

@[to_additive]
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCentralScalar R PUnit :=
  ⟨fun _ _ => rfl⟩

@[to_additive]
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass R S PUnit :=
  ⟨fun _ _ _ => rfl⟩

@[to_additive]
/-
**PUnit.instIsScalarTowerOfSMul** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：instIsScalarTowerOfSMul [SMul R S] : IsScalarTower R S PUnit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTowerOfSMul [SMul R S] : IsScalarTower R S PUnit :=
  ⟨fun _ _ _ => rfl⟩
/-
**PUnit.smulWithZero** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：smulWithZero [Zero R] : SMulWithZero R PUnit where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulWithZero [Zero R] : SMulWithZero R PUnit where
  __ := PUnit.smul
  smul_zero := by subsingleton
  zero_smul := by subsingleton
/-
**PUnit.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：mulAction [Monoid R] : MulAction R PUnit where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction [Monoid R] : MulAction R PUnit where
  __ := PUnit.smul
  one_smul := by subsingleton
  mul_smul := by subsingleton
/-
**PUnit.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：distribMulAction [Monoid R] : DistribMulAction R PUnit where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction [Monoid R] : DistribMulAction R PUnit where
  __ := PUnit.mulAction
  smul_zero := by subsingleton
  smul_add := by subsingleton
/-
**PUnit.mulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：mulDistribMulAction [Monoid R] : MulDistribMulAction R PUnit where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulDistribMulAction [Monoid R] : MulDistribMulAction R PUnit where
  __ := PUnit.mulAction
  smul_mul := by subsingleton
  smul_one := by subsingleton
/-
**PUnit.mulSemiringAction** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：mulSemiringAction [Semiring R] : MulSemiringAction R PUnit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulSemiringAction [Semiring R] : MulSemiringAction R PUnit :=
  { PUnit.distribMulAction, PUnit.mulDistribMulAction with }
/-
**PUnit.mulActionWithZero** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：mulActionWithZero [MonoidWithZero R] : MulActionWithZero R PUnit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulActionWithZero [MonoidWithZero R] : MulActionWithZero R PUnit :=
  { PUnit.mulAction, PUnit.smulWithZero with }
/-
**PUnit.module** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：module [Semiring R] : Module R PUnit where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module [Semiring R] : Module R PUnit where
  __ := PUnit.distribMulAction
  add_smul := by subsingleton
  zero_smul := by subsingleton

@[to_additive]
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul PUnit R where smul _ x := x

/-- The one-element type acts trivially on every element. -/
@[to_additive (attr := simp)]
/-
**PUnit.smul_eq'** 是 Mathlib 中的一个引理，位于命名空间 `PUnit`。
形式化陈述：smul_eq' (r : PUnit) (a : R) : r • a = a
参数：r : PUnit；a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The one-element type acts trivially on every element.
-/
lemma smul_eq' (r : PUnit) (a : R) : r • a = a := rfl
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [SMul R S] : SMulCommClass PUnit R S := ⟨by simp⟩
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R S] : IsScalarTower PUnit R S := ⟨by simp⟩
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction PUnit R where
  __ := (inferInstance : SMul PUnit R)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] : SMulZeroClass PUnit R where
  __ := (inferInstance : SMul PUnit R)
  smul_zero _ := rfl
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid R] : DistribMulAction PUnit R where
  __ := (inferInstance : MulAction PUnit R)
  __ := (inferInstance : SMulZeroClass PUnit R)
  smul_add _ _ _ := rfl

end PUnit

