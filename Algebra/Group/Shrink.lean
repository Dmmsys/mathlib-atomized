/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.Logic.Small.Defs

/-!
# Transfer group structures from `α` to `Shrink α`
-/

@[expose] public noncomputable section

universe v
variable {M α : Type*} [Small.{v} α]

namespace Shrink

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: α] : One (Shrink.{v} α)
  body: (equivShrink α).symm.one

中文:
实例 [One
  签名: α] : One (Shrink.{v} α)
  定义体: (equivShrink α).symm.one
-/
@[to_additive] instance [One α] : One (Shrink.{v} α) := (equivShrink α).symm.one
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] : Mul (Shrink.{v} α)
  body: (equivShrink α).symm.mul

中文:
实例 [Mul
  签名: α] : Mul (Shrink.{v} α)
  定义体: (equivShrink α).symm.mul
-/
@[to_additive] instance [Mul α] : Mul (Shrink.{v} α) := (equivShrink α).symm.mul
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Div
  signature: α] : Div (Shrink.{v} α)
  body: (equivShrink α).symm.div

中文:
实例 [Div
  签名: α] : Div (Shrink.{v} α)
  定义体: (equivShrink α).symm.div
-/
@[to_additive] instance [Div α] : Div (Shrink.{v} α) := (equivShrink α).symm.div
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inv
  signature: α] : Inv (Shrink.{v} α)
  body: (equivShrink α).symm.Inv

中文:
实例 [Inv
  签名: α] : Inv (Shrink.{v} α)
  定义体: (equivShrink α).symm.Inv
-/
@[to_additive] instance [Inv α] : Inv (Shrink.{v} α) := (equivShrink α).symm.Inv
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Pow
  signature: α M] : Pow (Shrink.{v} α) M
  body: (equivShrink α).symm.pow M

中文:
实例 [Pow
  签名: α M] : Pow (Shrink.{v} α) M
  定义体: (equivShrink α).symm.pow M
-/
@[to_additive] instance [Pow α M] : Pow (Shrink.{v} α) M := (equivShrink α).symm.pow M

end Shrink

@[to_additive (attr := simp)]
/--
lemma `equivShrink_symm_one` / 引理 `equivShrink_symm_one`

English:
lemma equivShrink_symm_one
  given: [One α]
  statement: (equivShrink α).symm 1 = 1
  proof: (equivShrink α).symm_apply_apply 1

@[to_additive (attr := simp)]

中文:
引理 equivShrink_symm_one
  条件: [One α]
  结论: (equivShrink α).symm 1 = 1
  证明: (equivShrink α).symm_apply_apply 1

@[to_additive (attr := simp)]

Depends on / 依赖: equivShrink, symm_apply_apply
-/
lemma equivShrink_symm_one [One α] : (equivShrink α).symm 1 = 1 :=
  (equivShrink α).symm_apply_apply 1

@[to_additive (attr := simp)]
/--
lemma `equivShrink_symm_mul` / 引理 `equivShrink_symm_mul`

English:
lemma equivShrink_symm_mul
  given: [Mul α] (x y : Shrink α)
  proof: by
  simp [Equiv.mul_def]

@[to_additive (attr := simp)]

中文:
引理 equivShrink_symm_mul
  条件: [Mul α] (x y : Shrink α)
  证明: by
  simp [Equiv.mul_def]

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.mul_def, mul_def
-/
lemma equivShrink_symm_mul [Mul α] (x y : Shrink α) :
    (equivShrink α).symm (x * y) = (equivShrink α).symm x * (equivShrink α).symm y := by
  simp [Equiv.mul_def]

@[to_additive (attr := simp)]
/--
lemma `equivShrink_mul` / 引理 `equivShrink_mul`

English:
lemma equivShrink_mul
  given: [Mul α] (x y : α)
  proof: by
  simp [Equiv.mul_def]

@[simp]

中文:
引理 equivShrink_mul
  条件: [Mul α] (x y : α)
  证明: by
  simp [Equiv.mul_def]

@[simp]

Depends on / 依赖: Equiv.mul_def, mul_def
-/
lemma equivShrink_mul [Mul α] (x y : α) :
    equivShrink α (x * y) = equivShrink α x * equivShrink α y := by
  simp [Equiv.mul_def]

@[simp]
/--
lemma `equivShrink_symm_smul` / 引理 `equivShrink_symm_smul`

English:
lemma equivShrink_symm_smul
  given: {M : Type*} [SMul M α] (m : M) (x : Shrink α)
  proof: by
  simp [Equiv.smul_def]

@[simp]

中文:
引理 equivShrink_symm_smul
  条件: {M : 类型} [SMul M α] (m : M) (x : Shrink α)
  证明: by
  simp [Equiv.smul_def]

@[simp]

Depends on / 依赖: Equiv.smul_def, smul_def
-/
lemma equivShrink_symm_smul {M : Type*} [SMul M α] (m : M) (x : Shrink α) :
    (equivShrink α).symm (m • x) = m • (equivShrink α).symm x := by
  simp [Equiv.smul_def]

@[simp]
/--
lemma `equivShrink_smul` / 引理 `equivShrink_smul`

English:
lemma equivShrink_smul
  given: {M : Type*} [SMul M α] (m : M) (x : α)
  proof: by
  simp [Equiv.smul_def]
@[to_additive (attr := simp)]

中文:
引理 equivShrink_smul
  条件: {M : 类型} [SMul M α] (m : M) (x : α)
  证明: by
  simp [Equiv.smul_def]
@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.smul_def, smul_def, to_additive
-/
lemma equivShrink_smul {M : Type*} [SMul M α] (m : M) (x : α) :
    equivShrink α (m • x) = m • equivShrink α x := by
  simp [Equiv.smul_def]
@[to_additive (attr := simp)]
/--
lemma `equivShrink_symm_div` / 引理 `equivShrink_symm_div`

English:
lemma equivShrink_symm_div
  given: [Div α] (x y : Shrink α)
  proof: by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]

中文:
引理 equivShrink_symm_div
  条件: [Div α] (x y : Shrink α)
  证明: by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.div_def, div_def
-/
lemma equivShrink_symm_div [Div α] (x y : Shrink α) :
    (equivShrink α).symm (x / y) = (equivShrink α).symm x / (equivShrink α).symm y := by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]
/--
lemma `equivShrink_div` / 引理 `equivShrink_div`

English:
lemma equivShrink_div
  given: [Div α] (x y : α)
  proof: by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]

中文:
引理 equivShrink_div
  条件: [Div α] (x y : α)
  证明: by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.div_def, div_def
-/
lemma equivShrink_div [Div α] (x y : α) :
    equivShrink α (x / y) = equivShrink α x / equivShrink α y := by
  simp [Equiv.div_def]

@[to_additive (attr := simp)]
/--
lemma `equivShrink_symm_inv` / 引理 `equivShrink_symm_inv`

English:
lemma equivShrink_symm_inv
  given: [Inv α] (x : Shrink α)
  proof: by
  simp [Equiv.inv_def]

@[to_additive (attr := simp)]

中文:
引理 equivShrink_symm_inv
  条件: [Inv α] (x : Shrink α)
  证明: by
  simp [Equiv.inv_def]

@[to_additive (attr := simp)]

Depends on / 依赖: Equiv.inv_def, inv_def
-/
lemma equivShrink_symm_inv [Inv α] (x : Shrink α) :
    (equivShrink α).symm x⁻¹ = ((equivShrink α).symm x)⁻¹ := by
  simp [Equiv.inv_def]

@[to_additive (attr := simp)]
/--
lemma `equivShrink_inv` / 引理 `equivShrink_inv`

English:
lemma equivShrink_inv
  given: [Inv α] (x : α)
  statement: equivShrink α x⁻¹ = (equivShrink α x)⁻¹
  proof: by
  simp [Equiv.inv_def]

中文:
引理 equivShrink_inv
  条件: [Inv α] (x : α)
  结论: equivShrink α x⁻¹ = (equivShrink α x)⁻¹
  证明: by
  simp [Equiv.inv_def]

Depends on / 依赖: Equiv.inv_def, inv_def
-/
lemma equivShrink_inv [Inv α] (x : α) : equivShrink α x⁻¹ = (equivShrink α x)⁻¹ := by
  simp [Equiv.inv_def]

namespace Shrink

/-- Shrink `α` to a smaller universe preserves multiplication. -/
@[to_additive /-- Shrink `α` to a smaller universe preserves addition. -/]
/--
Definition of `mulEquiv` / `mulEquiv` 的定义

English:
definition mulEquiv
  signature: [Mul α]
  body: (equivShrink α).symm.mulEquiv

@[to_additive]

中文:
定义 mulEquiv
  签名: [Mul α]
  定义体: (equivShrink α).symm.mulEquiv

@[to_additive]

Depends on / 依赖: equivShrink, mulEquiv, symm.mulEquiv
-/
def mulEquiv [Mul α] : Shrink.{v} α ≃* α := (equivShrink α).symm.mulEquiv

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semigroup
  signature: α] : Semigroup (Shrink.{v} α)
  body: (equivShrink α).symm.semigroup

@[to_additive]

中文:
实例 [Semigroup
  签名: α] : Semigroup (Shrink.{v} α)
  定义体: (equivShrink α).symm.semigroup

@[to_additive]

Depends on / 依赖: equivShrink, semigroup, symm.semigroup
-/
instance [Semigroup α] : Semigroup (Shrink.{v} α) := (equivShrink α).symm.semigroup

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemigroup
  signature: α] : CommSemigroup (Shrink.{v} α)
  body: (equivShrink α).symm.commSemigroup

@[to_additive]

中文:
实例 [CommSemigroup
  签名: α] : CommSemigroup (Shrink.{v} α)
  定义体: (equivShrink α).symm.commSemigroup

@[to_additive]

Depends on / 依赖: commSemigroup, equivShrink, symm.commSemigroup
-/
instance [CommSemigroup α] : CommSemigroup (Shrink.{v} α) := (equivShrink α).symm.commSemigroup

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsLeftCancelMul α] : IsLeftCancelMul (Shrink.{v} α)
  body: (equivShrink α).symm.isLeftCancelMul

@[to_additive]

中文:
实例 [Mul
  签名: α] [IsLeftCancelMul α] : IsLeftCancelMul (Shrink.{v} α)
  定义体: (equivShrink α).symm.isLeftCancelMul

@[to_additive]

Depends on / 依赖: equivShrink, isLeftCancelMul, symm.isLeftCancelMul
-/
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Shrink.{v} α) :=
  (equivShrink α).symm.isLeftCancelMul

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsRightCancelMul α] : IsRightCancelMul (Shrink.{v} α)
  body: (equivShrink α).symm.isRightCancelMul

@[to_additive]

中文:
实例 [Mul
  签名: α] [IsRightCancelMul α] : IsRightCancelMul (Shrink.{v} α)
  定义体: (equivShrink α).symm.isRightCancelMul

@[to_additive]

Depends on / 依赖: equivShrink, isRightCancelMul, symm.isRightCancelMul
-/
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Shrink.{v} α) :=
  (equivShrink α).symm.isRightCancelMul

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [IsCancelMul α] : IsCancelMul (Shrink.{v} α)
  body: (equivShrink α).symm.isCancelMul

@[to_additive]

中文:
实例 [Mul
  签名: α] [IsCancelMul α] : IsCancelMul (Shrink.{v} α)
  定义体: (equivShrink α).symm.isCancelMul

@[to_additive]

Depends on / 依赖: equivShrink, isCancelMul, symm.isCancelMul
-/
instance [Mul α] [IsCancelMul α] : IsCancelMul (Shrink.{v} α) := (equivShrink α).symm.isCancelMul

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: α] : MulOneClass (Shrink.{v} α)
  body: (equivShrink α).symm.mulOneClass

@[to_additive]

中文:
实例 [MulOneClass
  签名: α] : MulOneClass (Shrink.{v} α)
  定义体: (equivShrink α).symm.mulOneClass

@[to_additive]

Depends on / 依赖: equivShrink, mulOneClass, symm.mulOneClass
-/
instance [MulOneClass α] : MulOneClass (Shrink.{v} α) := (equivShrink α).symm.mulOneClass

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] : Monoid (Shrink.{v} α)
  body: (equivShrink α).symm.monoid

@[to_additive]

中文:
实例 [Monoid
  签名: α] : Monoid (Shrink.{v} α)
  定义体: (equivShrink α).symm.monoid

@[to_additive]

Depends on / 依赖: equivShrink, monoid, symm.monoid
-/
instance [Monoid α] : Monoid (Shrink.{v} α) := (equivShrink α).symm.monoid

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: α] : CommMonoid (Shrink.{v} α)
  body: (equivShrink α).symm.commMonoid

@[to_additive]

中文:
实例 [CommMonoid
  签名: α] : CommMonoid (Shrink.{v} α)
  定义体: (equivShrink α).symm.commMonoid

@[to_additive]

Depends on / 依赖: commMonoid, equivShrink, symm.commMonoid
-/
instance [CommMonoid α] : CommMonoid (Shrink.{v} α) := (equivShrink α).symm.commMonoid

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: α] : Group (Shrink.{v} α)
  body: (equivShrink α).symm.group

@[to_additive]

中文:
实例 [Group
  签名: α] : Group (Shrink.{v} α)
  定义体: (equivShrink α).symm.group

@[to_additive]

Depends on / 依赖: equivShrink, symm.group
-/
instance [Group α] : Group (Shrink.{v} α) := (equivShrink α).symm.group

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommGroup
  signature: α] : CommGroup (Shrink.{v} α)
  body: (equivShrink α).symm.commGroup

@[to_additive]

中文:
实例 [CommGroup
  签名: α] : CommGroup (Shrink.{v} α)
  定义体: (equivShrink α).symm.commGroup

@[to_additive]

Depends on / 依赖: commGroup, equivShrink, symm.commGroup
-/
instance [CommGroup α] : CommGroup (Shrink.{v} α) := (equivShrink α).symm.commGroup

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [MulAction M α] : MulAction M (Shrink.{v} α)
  body: (equivShrink α).symm.mulAction M

中文:
实例 [Monoid
  签名: M] [MulAction M α] : MulAction M (Shrink.{v} α)
  定义体: (equivShrink α).symm.mulAction M

Depends on / 依赖: equivShrink, mulAction, symm.mulAction
-/
instance [Monoid M] [MulAction M α] : MulAction M (Shrink.{v} α) := (equivShrink α).symm.mulAction M

end Shrink
