/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.InjSurj

/-!
# `ULift` instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `MulEquiv.ulift : ULift R ≃* R` (and its additive analogue).
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

universe u v w

variable {α : Type u} {β : Type v} {x y : ULift.{w} α}

namespace ULift

@[to_additive]
/--
Instance `one` / 实例 `one`

English:
instance one
  signature: [One α]
  body: ⟨⟨1⟩⟩

@[to_additive (attr := simp)]

中文:
实例 one
  签名: [One α]
  定义体: ⟨⟨1⟩⟩

@[to_additive (attr := simp)]
-/
instance one [One α] : One (ULift α) :=
  ⟨⟨1⟩⟩

@[to_additive (attr := simp)]
/--
theorem `one_down` / 定理 `one_down`

English:
theorem one_down
  given: [One α]
  statement: (1 : ULift α).down = 1
  proof: rfl

@[to_additive]

中文:
定理 one_down
  条件: [One α]
  结论: (1 : ULift α).down = 1
  证明: rfl

@[to_additive]
-/
theorem one_down [One α] : (1 : ULift α).down = 1 :=
  rfl

@[to_additive]
/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: [Mul α]
  body: ⟨fun f g => ⟨f.down * g.down⟩⟩

@[to_additive (attr := simp)]

中文:
实例 mul
  签名: [Mul α]
  定义体: ⟨fun f g => ⟨f.down * g.down⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: f.down, g.down
-/
instance mul [Mul α] : Mul (ULift α) :=
  ⟨fun f g => ⟨f.down * g.down⟩⟩

@[to_additive (attr := simp)]
/--
theorem `mul_down` / 定理 `mul_down`

English:
theorem mul_down
  given: [Mul α]
  statement: (x * y).down = x.down * y.down
  proof: rfl

@[to_additive]

中文:
定理 mul_down
  条件: [Mul α]
  结论: (x * y).down = x.down * y.down
  证明: rfl

@[to_additive]
-/
theorem mul_down [Mul α] : (x * y).down = x.down * y.down :=
  rfl

@[to_additive]
/--
Instance `div` / 实例 `div`

English:
instance div
  signature: [Div α]
  body: ⟨fun f g => ⟨f.down / g.down⟩⟩

@[to_additive (attr := simp)]

中文:
实例 div
  签名: [Div α]
  定义体: ⟨fun f g => ⟨f.down / g.down⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: f.down, g.down
-/
instance div [Div α] : Div (ULift α) :=
  ⟨fun f g => ⟨f.down / g.down⟩⟩

@[to_additive (attr := simp)]
/--
theorem `div_down` / 定理 `div_down`

English:
theorem div_down
  given: [Div α]
  statement: (x / y).down = x.down / y.down
  proof: rfl

@[to_additive]

中文:
定理 div_down
  条件: [Div α]
  结论: (x / y).down = x.down / y.down
  证明: rfl

@[to_additive]
-/
theorem div_down [Div α] : (x / y).down = x.down / y.down :=
  rfl

@[to_additive]
/--
Instance `inv` / 实例 `inv`

English:
instance inv
  signature: [Inv α]
  body: ⟨fun f => ⟨f.down⁻¹⟩⟩

@[to_additive (attr := simp)]

中文:
实例 inv
  签名: [Inv α]
  定义体: ⟨fun f => ⟨f.down⁻¹⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: f.down
-/
instance inv [Inv α] : Inv (ULift α) :=
  ⟨fun f => ⟨f.down⁻¹⟩⟩

@[to_additive (attr := simp)]
/--
theorem `inv_down` / 定理 `inv_down`

English:
theorem inv_down
  given: [Inv α]
  statement: x⁻¹.down = x.down⁻¹
  proof: rfl

@[to_additive (attr := to_additive) smul]

中文:
定理 inv_down
  条件: [Inv α]
  结论: x⁻¹.down = x.down⁻¹
  证明: rfl

@[to_additive (attr := to_additive) smul]
-/
theorem inv_down [Inv α] : x⁻¹.down = x.down⁻¹ :=
  rfl

@[to_additive (attr := to_additive) smul]
/--
Instance `pow` / 实例 `pow`

English:
instance pow
  signature: [Pow α β]
  body: ⟨fun x n => up (x.down ^ n)⟩

@[to_additive (attr := to_additive, simp) smul_down]

中文:
实例 pow
  签名: [Pow α β]
  定义体: ⟨fun x n => up (x.down ^ n)⟩

@[to_additive (attr := to_additive, simp) smul_down]

Depends on / 依赖: x.down
-/
instance pow [Pow α β] : Pow (ULift α) β :=
  ⟨fun x n => up (x.down ^ n)⟩

@[to_additive (attr := to_additive, simp) smul_down]
/--
theorem `pow_down` / 定理 `pow_down`

English:
theorem pow_down
  given: [Pow α β] (a : ULift.{w} α) (b : β)
  statement: (a ^ b).down = a.down ^ b
  proof: rfl

中文:
定理 pow_down
  条件: [Pow α β] (a : ULift.{w} α) (b : β)
  结论: (a ^ b).down = a.down ^ b
  证明: rfl
-/
theorem pow_down [Pow α β] (a : ULift.{w} α) (b : β) : (a ^ b).down = a.down ^ b :=
  rfl

/-- The multiplicative equivalence between `ULift α` and `α`.
-/
@[to_additive /-- The additive equivalence between `ULift α` and `α`. -/]
/--
Definition of `_root_.MulEquiv.ulift` / `_root_.MulEquiv.ulift` 的定义

English:
definition _root_.MulEquiv.ulift
  signature: [Mul α]
  body: { Equiv.ulift with map_mul' := fun _ _ => rfl }

@[to_additive]

中文:
定义 _root_.MulEquiv.ulift
  签名: [Mul α]
  定义体: { Equiv.ulift with map_mul' := fun _ _ => rfl }

@[to_additive]

Depends on / 依赖: Equiv.ulift, map_mul
-/
def _root_.MulEquiv.ulift [Mul α] : ULift α ≃* α :=
  { Equiv.ulift with map_mul' := fun _ _ => rfl }

@[to_additive]
/--
Instance `semigroup` / 实例 `semigroup`

English:
instance semigroup
  signature: [Semigroup α]
  body: (MulEquiv.ulift.injective.semigroup _) fun _ _ => rfl

@[to_additive]

中文:
实例 semigroup
  签名: [Semigroup α]
  定义体: (MulEquiv.ulift.injective.semigroup _) fun _ _ => rfl

@[to_additive]

Depends on / 依赖: MulEquiv, MulEquiv.ulift.injective.semigroup, injective, semigroup
-/
instance semigroup [Semigroup α] : Semigroup (ULift α) :=
  (MulEquiv.ulift.injective.semigroup _) fun _ _ => rfl

@[to_additive]
/--
Instance `commSemigroup` / 实例 `commSemigroup`

English:
instance commSemigroup
  signature: [CommSemigroup α]
  body: (Equiv.ulift.injective.commSemigroup _) fun _ _ => rfl

@[to_additive]

中文:
实例 commSemigroup
  签名: [CommSemigroup α]
  定义体: (Equiv.ulift.injective.commSemigroup _) fun _ _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.commSemigroup, commSemigroup, injective
-/
instance commSemigroup [CommSemigroup α] : CommSemigroup (ULift α) :=
  (Equiv.ulift.injective.commSemigroup _) fun _ _ => rfl

@[to_additive]
/--
Instance `mulOneClass` / 实例 `mulOneClass`

English:
instance mulOneClass
  signature: [MulOneClass α]
  body: Equiv.ulift.injective.mulOneClass _ rfl (by intros; rfl)

@[to_additive]

中文:
实例 mulOneClass
  签名: [MulOneClass α]
  定义体: Equiv.ulift.injective.mulOneClass _ rfl (by intros; rfl)

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.mulOneClass, injective, intros, mulOneClass
-/
instance mulOneClass [MulOneClass α] : MulOneClass (ULift α) :=
  Equiv.ulift.injective.mulOneClass _ rfl (by intros; rfl)

@[to_additive]
/--
Instance `monoid` / 实例 `monoid`

English:
instance monoid
  signature: [Monoid α]
  body: Equiv.ulift.injective.monoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

中文:
实例 monoid
  签名: [Monoid α]
  定义体: Equiv.ulift.injective.monoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.monoid, injective, monoid
-/
instance monoid [Monoid α] : Monoid (ULift α) :=
  Equiv.ulift.injective.monoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/--
Instance `commMonoid` / 实例 `commMonoid`

English:
instance commMonoid
  signature: [CommMonoid α]
  body: Equiv.ulift.injective.commMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

中文:
实例 commMonoid
  签名: [CommMonoid α]
  定义体: Equiv.ulift.injective.commMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.commMonoid, commMonoid, injective
-/
instance commMonoid [CommMonoid α] : CommMonoid (ULift α) :=
  Equiv.ulift.injective.commMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/--
Instance `divInvMonoid` / 实例 `divInvMonoid`

English:
instance divInvMonoid
  signature: [DivInvMonoid α]
  body: Equiv.ulift.injective.divInvMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

中文:
实例 divInvMonoid
  签名: [DivInvMonoid α]
  定义体: Equiv.ulift.injective.divInvMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.divInvMonoid, divInvMonoid, injective
-/
instance divInvMonoid [DivInvMonoid α] : DivInvMonoid (ULift α) :=
  Equiv.ulift.injective.divInvMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/--
Instance `group` / 实例 `group`

English:
instance group
  signature: [Group α]
  body: Equiv.ulift.injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

中文:
实例 group
  签名: [Group α]
  定义体: Equiv.ulift.injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.group, injective
-/
instance group [Group α] : Group (ULift α) :=
  Equiv.ulift.injective.group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/--
Instance `commGroup` / 实例 `commGroup`

English:
instance commGroup
  signature: [CommGroup α]
  body: Equiv.ulift.injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

中文:
实例 commGroup
  签名: [CommGroup α]
  定义体: Equiv.ulift.injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.commGroup, commGroup, injective
-/
instance commGroup [CommGroup α] : CommGroup (ULift α) :=
  Equiv.ulift.injective.commGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/--
Instance `leftCancelSemigroup` / 实例 `leftCancelSemigroup`

English:
instance leftCancelSemigroup
  signature: [LeftCancelSemigroup α]
  body: Equiv.ulift.injective.leftCancelSemigroup _ fun _ _ => rfl

@[to_additive]

中文:
实例 leftCancelSemigroup
  签名: [LeftCancelSemigroup α]
  定义体: Equiv.ulift.injective.leftCancelSemigroup _ fun _ _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.leftCancelSemigroup, injective, leftCancelSemigroup
-/
instance leftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup (ULift α) :=
  Equiv.ulift.injective.leftCancelSemigroup _ fun _ _ => rfl

@[to_additive]
/--
Instance `rightCancelSemigroup` / 实例 `rightCancelSemigroup`

English:
instance rightCancelSemigroup
  signature: [RightCancelSemigroup α]
  body: Equiv.ulift.injective.rightCancelSemigroup _ fun _ _ => rfl

@[to_additive]

中文:
实例 rightCancelSemigroup
  签名: [RightCancelSemigroup α]
  定义体: Equiv.ulift.injective.rightCancelSemigroup _ fun _ _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.rightCancelSemigroup, injective, rightCancelSemigroup
-/
instance rightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup (ULift α) :=
  Equiv.ulift.injective.rightCancelSemigroup _ fun _ _ => rfl

@[to_additive]
/--
Instance `leftCancelMonoid` / 实例 `leftCancelMonoid`

English:
instance leftCancelMonoid
  signature: [LeftCancelMonoid α]
  body: Equiv.ulift.injective.leftCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

中文:
实例 leftCancelMonoid
  签名: [LeftCancelMonoid α]
  定义体: Equiv.ulift.injective.leftCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.leftCancelMonoid, injective, leftCancelMonoid
-/
instance leftCancelMonoid [LeftCancelMonoid α] : LeftCancelMonoid (ULift α) :=
  Equiv.ulift.injective.leftCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/--
Instance `rightCancelMonoid` / 实例 `rightCancelMonoid`

English:
instance rightCancelMonoid
  signature: [RightCancelMonoid α]
  body: Equiv.ulift.injective.rightCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

中文:
实例 rightCancelMonoid
  签名: [RightCancelMonoid α]
  定义体: Equiv.ulift.injective.rightCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.rightCancelMonoid, injective, rightCancelMonoid
-/
instance rightCancelMonoid [RightCancelMonoid α] : RightCancelMonoid (ULift α) :=
  Equiv.ulift.injective.rightCancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/--
Instance `cancelMonoid` / 实例 `cancelMonoid`

English:
instance cancelMonoid
  signature: [CancelMonoid α]
  body: Equiv.ulift.injective.cancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

中文:
实例 cancelMonoid
  签名: [CancelMonoid α]
  定义体: Equiv.ulift.injective.cancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]

Depends on / 依赖: Equiv.ulift.injective.cancelMonoid, apply_symm_apply, cancelMonoid, injective
-/
instance cancelMonoid [CancelMonoid α] : CancelMonoid (ULift α) :=
  Equiv.ulift.injective.cancelMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
/--
Instance `cancelCommMonoid` / 实例 `cancelCommMonoid`

English:
instance cancelCommMonoid
  signature: [CancelCommMonoid α]
  body: Equiv.ulift.injective.cancelCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 cancelCommMonoid
  签名: [CancelCommMonoid α]
  定义体: Equiv.ulift.injective.cancelCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: Equiv.ulift.injective.cancelCommMonoid, cancelCommMonoid, injective
-/
instance cancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid (ULift α) :=
  Equiv.ulift.injective.cancelCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: [Nontrivial α]
  body: Equiv.ulift.symm.injective.nontrivial

中文:
实例 nontrivial
  签名: [Nontrivial α]
  定义体: Equiv.ulift.symm.injective.nontrivial

Depends on / 依赖: Equiv.ulift.symm.injective.nontrivial, injective, nontrivial
-/
instance nontrivial [Nontrivial α] : Nontrivial (ULift α) :=
  Equiv.ulift.symm.injective.nontrivial

-- TODO: We don't do `IsOrderedCancelMonoid`.
-- We'd need to add instances for `ULift` in `Order.Basic`.
end ULift
