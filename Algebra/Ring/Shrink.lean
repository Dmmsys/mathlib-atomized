/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# Transfer ring structures from `α` to `Shrink α`
-/

@[expose] public section

noncomputable section

namespace Shrink
universe v
variable {α : Type*} [Small.{v} α]

variable (α) in
/--
Definition of `ringEquiv` / `ringEquiv` 的定义

English:
definition ringEquiv
  signature: [Add α] [Mul α]
  body: (equivShrink α).symm.ringEquiv

中文:
定义 ringEquiv
  签名: [加法 α] [乘法 α]
  定义体: (equivShrink α).symm.ringEquiv

Depends on / 依赖: equivShrink, ringEquiv, symm.ringEquiv
-/
def ringEquiv [Add α] [Mul α] : Shrink.{v} α ≃+* α := (equivShrink α).symm.ringEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: α] : NonUnitalNonAssocSemiring (Shrink.{v} α)
  body: (equivShrink α).symm.nonUnitalNonAssocSemiring

中文:
实例 [非幺非结合半环
  签名: α] : 非幺非结合半环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.nonUnitalNonAssocSemiring
-/
instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocSemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: α] : NonUnitalSemiring (Shrink.{v} α)
  body: (equivShrink α).symm.nonUnitalSemiring

中文:
实例 [非幺半环
  签名: α] : 非幺半环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.nonUnitalSemiring

Depends on / 依赖: equivShrink, nonUnitalSemiring, symm.nonUnitalSemiring
-/
instance [NonUnitalSemiring α] : NonUnitalSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalSemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoidWithOne
  signature: α] : AddMonoidWithOne (Shrink.{v} α)
  body: (equivShrink α).symm.addMonoidWithOne

中文:
实例 [加法带幺幺半群
  签名: α] : 加法带幺幺半群 (Shrink.{v} α)
  定义体: (equivShrink α).symm.addMonoidWithOne

Depends on / 依赖: addMonoidWithOne, equivShrink, symm.addMonoidWithOne
-/
instance [AddMonoidWithOne α] : AddMonoidWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addMonoidWithOne

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroupWithOne
  signature: α] : AddGroupWithOne (Shrink.{v} α)
  body: (equivShrink α).symm.addGroupWithOne

中文:
实例 [加法带幺群
  签名: α] : 加法带幺群 (Shrink.{v} α)
  定义体: (equivShrink α).symm.addGroupWithOne

Depends on / 依赖: Scheme, Scheme.homOfLE, addGroupWithOne, equivShrink, homOfLE, infer_instance, symm.addGroupWithOne
-/
instance [AddGroupWithOne α] : AddGroupWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addGroupWithOne

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocSemiring
  signature: α] : NonAssocSemiring (Shrink.{v} α)
  body: (equivShrink α).symm.nonAssocSemiring

中文:
实例 [非结合半环
  签名: α] : 非结合半环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.nonAssocSemiring

Depends on / 依赖: equivShrink, nonAssocSemiring, symm.nonAssocSemiring
-/
instance [NonAssocSemiring α] : NonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonAssocSemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: α] : Semiring (Shrink.{v} α)
  body: (equivShrink α).symm.semiring

中文:
实例 [半环
  签名: α] : 半环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.semiring

Depends on / 依赖: equivShrink, semiring, symm.semiring
-/
instance [Semiring α] : Semiring (Shrink.{v} α) := (equivShrink α).symm.semiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommSemiring
  signature: α] : NonUnitalCommSemiring (Shrink.{v} α)
  body: (equivShrink α).symm.nonUnitalCommSemiring

中文:
实例 [非幺交换半环
  签名: α] : 非幺交换半环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.nonUnitalCommSemiring

Depends on / 依赖: equivShrink, nonUnitalCommSemiring, symm.nonUnitalCommSemiring
-/
instance [NonUnitalCommSemiring α] : NonUnitalCommSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommSemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: α] : CommSemiring (Shrink.{v} α)
  body: (equivShrink α).symm.commSemiring

中文:
实例 [交换半环
  签名: α] : 交换半环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.commSemiring

Depends on / 依赖: commSemiring, equivShrink, symm.commSemiring
-/
instance [CommSemiring α] : CommSemiring (Shrink.{v} α) := (equivShrink α).symm.commSemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: α] : NonUnitalNonAssocRing (Shrink.{v} α)
  body: (equivShrink α).symm.nonUnitalNonAssocRing

中文:
实例 [非幺非结合环
  签名: α] : 非幺非结合环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.nonUnitalNonAssocRing

Depends on / 依赖: equivShrink, nonUnitalNonAssocRing, symm.nonUnitalNonAssocRing
-/
instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalRing
  signature: α] : NonUnitalRing (Shrink.{v} α)
  body: (equivShrink α).symm.nonUnitalRing

中文:
实例 [非幺环
  签名: α] : 非幺环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.nonUnitalRing

Depends on / 依赖: equivShrink, nonUnitalRing, symm.nonUnitalRing
-/
instance [NonUnitalRing α] : NonUnitalRing (Shrink.{v} α) := (equivShrink α).symm.nonUnitalRing
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocRing
  signature: α] : NonAssocRing (Shrink.{v} α)
  body: (equivShrink α).symm.nonAssocRing

中文:
实例 [非结合环
  签名: α] : 非结合环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.nonAssocRing

Depends on / 依赖: equivShrink, nonAssocRing, symm.nonAssocRing
-/
instance [NonAssocRing α] : NonAssocRing (Shrink.{v} α) := (equivShrink α).symm.nonAssocRing
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: α] : Ring (Shrink.{v} α)
  body: (equivShrink α).symm.ring

中文:
实例 [环
  签名: α] : 环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.ring

Depends on / 依赖: equivShrink, symm.ring
-/
instance [Ring α] : Ring (Shrink.{v} α) := (equivShrink α).symm.ring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommRing
  signature: α] : NonUnitalCommRing (Shrink.{v} α)
  body: (equivShrink α).symm.nonUnitalCommRing

中文:
实例 [非幺交换环
  签名: α] : 非幺交换环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.nonUnitalCommRing

Depends on / 依赖: equivShrink, nonUnitalCommRing, symm.nonUnitalCommRing
-/
instance [NonUnitalCommRing α] : NonUnitalCommRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: α] : CommRing (Shrink.{v} α)
  body: (equivShrink α).symm.commRing

中文:
实例 [交换环
  签名: α] : 交换环 (Shrink.{v} α)
  定义体: (equivShrink α).symm.commRing

Depends on / 依赖: commRing, equivShrink, symm.commRing
-/
instance [CommRing α] : CommRing (Shrink.{v} α) := (equivShrink α).symm.commRing
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: α] [IsDomain α] : IsDomain (Shrink.{v} α)
  body: (Shrink.ringEquiv α).isDomain

中文:
实例 [半环
  签名: α] [是整环 α] : 是整环 (Shrink.{v} α)
  定义体: (Shrink.ringEquiv α).isDomain

Depends on / 依赖: Shrink, Shrink.ringEquiv, isDomain, ringEquiv
-/
instance [Semiring α] [IsDomain α] : IsDomain (Shrink.{v} α) := (Shrink.ringEquiv α).isDomain

end Shrink
