/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

public section

assert_not_exists Module

namespace Equiv
variable {α β : Type*} (e : α ≃ β)

-- See note [instance transfer via equivalence]
/-- Transfer `NNRatCast` across an `Equiv` -/
/-
**Equiv.nnratCast** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [NNRatCast β] → NNRatCast α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `NNRatCast` across an `Equiv`
-/
protected abbrev nnratCast [NNRatCast β] : NNRatCast α where nnratCast q := e.invFun q

/-- Transfer `RatCast` across an `Equiv` -/
/-
**Equiv.ratCast** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [RatCast β] → RatCast α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer `RatCast` across an `Equiv`
-/
protected abbrev ratCast [RatCast β] : RatCast α where ratCast n := e.invFun n

/-- Transfer `DivisionRing` across an `Equiv` -/
/-
**Equiv.divisionRing** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [DivisionRing β] → DivisionRing 
α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `DivisionRing` across an `Equiv`
-/
protected abbrev divisionRing [DivisionRing β] : DivisionRing α := by
  let add_group_with_one := e.addGroupWithOne
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  let nnratCast := e.nnratCast
  let ratCast := e.ratCast
  let nnqsmul := e.smul ℚ≥0
  let qsmul := e.smul ℚ
  apply e.injective.divisionRing _ <;> intros <;> exact e.apply_symm_apply _

/-- Transfer `Field` across an `Equiv` -/
/-
**Equiv.field** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [Field β] → Field α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Transfer `Field` across an `Equiv`
-/
protected abbrev field [Field β] : Field α := by
  let add_group_with_one := e.addGroupWithOne
  let neg := e.Neg
  let inv := e.Inv
  let div := e.div
  let mul := e.mul
  let npow := e.pow ℕ
  let zpow := e.pow ℤ
  let nnratCast := e.nnratCast
  let ratCast := e.ratCast
  let nnqsmul := e.smul ℚ≥0
  let qsmul := e.smul ℚ
  apply e.injective.field _ <;> intros <;> exact e.apply_symm_apply _

end Equiv

