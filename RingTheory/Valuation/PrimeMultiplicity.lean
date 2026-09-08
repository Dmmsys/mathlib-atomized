/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes
-/
module

public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.Valuation.Basic

/-!
# `multiplicity` of a prime in an integral domain as an additive valuation
-/

@[expose] public section

variable {R : Type*} [CommRing R] [IsDomain R] {p : R}

/-- `multiplicity` of a prime in an integral domain as an additive valuation to `ℕ∞`. -/
/-
**multiplicity_addValuation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：multiplicity_addValuation (hp : Prime p) : AddValuation R Nat∞
参数：hp : Prime p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`multiplicity` of a prime in an integral domain as an additive valuation to `ℕ∞`
.
-/
noncomputable def multiplicity_addValuation (hp : Prime p) : AddValuation R ℕ∞ :=
  AddValuation.of (emultiplicity p) (emultiplicity_zero _)
    (emultiplicity_of_one_right hp.not_isUnit)
      (fun _ _ => min_le_emultiplicity_add) fun _ _ => emultiplicity_mul hp

@[simp]
/-
**multiplicity_addValuation_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiplicity_addValuation_apply {hp : Prime p} {r : R} : multiplicity_addV
aluation hp r = emultiplicity p r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multiplicity_addValuation_apply {hp : Prime p} {r : R} :
    multiplicity_addValuation hp r = emultiplicity p r :=
  rfl
