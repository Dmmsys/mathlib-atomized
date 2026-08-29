/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Opposite

/-!
# Ring involutions

This file defines a ring involution as a structure extending `R ≃+* Rᵐᵒᵖ`,
with the additional fact `f.involution : (f (f x).unop).unop = x`.

## Notation

We provide a coercion to a function `R → Rᵐᵒᵖ`.

## References

* <https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory>

## Tags

Ring involution
-/

@[expose] public section

variable {F : Type*} (R : Type*)

/--
Definition of `RingInvo` / `RingInvo` 的定义

English:
structure RingInvo
  parameters: [Semiring R]
  extends: R ≃+* Rᵐᵒᵖ
  axioms and operations (1):
    - involution' : forall x, (toFun (toFun x).unop).unop = x

中文:
结构 RingInvo
  参数: [半环 R]
  继承: R ≃+* Rᵐᵒᵖ
  公理与运算 (1 个):
    - involution' : 对任意 x, (toFun (toFun x).unop).unop = x
-/
structure RingInvo [Semiring R] extends R ≃+* Rᵐᵒᵖ where
  /-- The requirement that the ring homomorphism is its own inverse -/
  involution' : forall x, (toFun (toFun x).unop).unop = x

/-- The equivalence of rings underlying a ring involution. -/
add_decl_doc RingInvo.toRingEquiv

/--
Definition of `RingInvoClass` / `RingInvoClass` 的定义

English:
class RingInvoClass
  parameters: (F R : Type*) [Semiring R] [EquivLike F R Rᵐᵒᵖ]
  extends: RingEquivClass F R Rᵐᵒᵖ
  axioms and operations (1):
    - involution : forall (f : F) (x), (f (f x).unop).unop = x

中文:
类 RingInvo类
  参数: (F R : 类型) [半环 R] [等价状 F R Rᵐᵒᵖ]
  继承: 环等价类 F R Rᵐᵒᵖ
  公理与运算 (1 个):
    - involution : 对任意 (f : F) (x), (f (f x).unop).unop = x
-/
class RingInvoClass (F R : Type*) [Semiring R] [EquivLike F R Rᵐᵒᵖ] : Prop
  extends RingEquivClass F R Rᵐᵒᵖ where
  /-- Every ring involution must be its own inverse -/
  involution : forall (f : F) (x), (f (f x).unop).unop = x


/-- Turn an element of a type `F` satisfying `RingInvoClass F R` into an actual
`RingInvo`. This is declared as the default coercion from `F` to `RingInvo R`. -/
@[coe]
/--
Definition of `RingInvoClass.toRingInvo` / `RingInvoClass.toRingInvo` 的定义

English:
definition RingInvoClass.toRingInvo
  signature: {R} [Semiring R] [EquivLike F R Rᵐᵒᵖ] [RingInvoClass F R] (f : F)
  body: { (RingEquivClass.toRingEquiv f : R ≃+* Rᵐᵒᵖ) with involution' := RingInvoClass.involution f }

中文:
定义 RingInvo类.toRingInvo
  签名: {R} [半环 R] [等价状 F R Rᵐᵒᵖ] [RingInvo类 F R] (f : F)
  定义体: { (RingEquivClass.toRingEquiv f : R ≃+* Rᵐᵒᵖ) with involution' := RingInvoClass.involution f }

Depends on / 依赖: RingEquivClass, RingEquivClass.toRingEquiv, RingInvoClass, RingInvoClass.involution, involution, toRingEquiv
-/
def RingInvoClass.toRingInvo {R} [Semiring R] [EquivLike F R Rᵐᵒᵖ] [RingInvoClass F R] (f : F) :
    RingInvo R :=
  { (RingEquivClass.toRingEquiv f : R ≃+* Rᵐᵒᵖ) with involution' := RingInvoClass.involution f }

namespace RingInvo

variable {R} [Semiring R] [EquivLike F R Rᵐᵒᵖ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RingInvoClass
  signature: F R] : CoeTC F (RingInvo R)
  body: ⟨RingInvoClass.toRingInvo⟩

中文:
实例 [RingInvo类
  签名: F R] : CoeTC F (RingInvo R)
  定义体: ⟨RingInvoClass.toRingInvo⟩

Depends on / 依赖: RingInvoClass, RingInvoClass.toRingInvo, toRingInvo
-/
instance [RingInvoClass F R] : CoeTC F (RingInvo R) :=
  ⟨RingInvoClass.toRingInvo⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (RingInvo R) R Rᵐᵒᵖ
  body: f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    rcases e with ⟨⟨tE, _⟩, _⟩; rcases f with ⟨⟨tF, _⟩, _⟩
    cases tE
    cases tF
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

中文:
实例 :
  签名: 等价状 (RingInvo R) R Rᵐᵒᵖ
  定义体: f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    rcases e with ⟨⟨tE, _⟩, _⟩; rcases f with ⟨⟨tF, _⟩, _⟩
    cases tE
    cases tF
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

Depends on / 依赖: f.toFun
-/
instance : EquivLike (RingInvo R) R Rᵐᵒᵖ where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    rcases e with ⟨⟨tE, _⟩, _⟩; rcases f with ⟨⟨tF, _⟩, _⟩
    cases tE
    cases tF
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RingInvoClass (RingInvo R) R
  body: f.map_add'
  map_mul f := f.map_mul'
  involution f := f.involution'

中文:
实例 :
  签名: RingInvo类 (RingInvo R) R
  定义体: f.map_add'
  map_mul f := f.map_mul'
  involution f := f.involution'

Depends on / 依赖: f.map_add, map_add
-/
instance : RingInvoClass (RingInvo R) R where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  involution f := f.involution'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (RingInvo R) (R ≃+* Rᵐᵒᵖ)
  body: toRingEquiv

中文:
实例 :
  签名: CoeOut (RingInvo R) (R ≃+* Rᵐᵒᵖ)
  定义体: toRingEquiv

Depends on / 依赖: toRingEquiv
-/
instance : CoeOut (RingInvo R) (R ≃+* Rᵐᵒᵖ) where coe := toRingEquiv

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (f : R ->+* Rᵐᵒᵖ) (involution : forall r, (f (f r).unop).unop = r)
  body: { f with
    invFun := fun r => (f r.unop).unop
    left_inv := fun r => involution r
right_inv := fun _ => MulOpposite.unop_injective involution _
    involution' := involution }

@[simp]

中文:
定义 mk'
  签名: (f : R ->+* Rᵐᵒᵖ) (involution : 对任意 r, (f (f r).unop).unop = r)
  定义体: { f with
    invFun := fun r => (f r.unop).unop
    left_inv := fun r => involution r
right_inv := fun _ => MulOpposite.unop_injective involution _
    involution' := involution }

@[simp]

Depends on / 依赖: MulOpposite, MulOpposite.unop_injective, invFun, involution, left_inv, r.unop, right_inv, unop_injective
-/
def mk' (f : R ->+* Rᵐᵒᵖ) (involution : forall r, (f (f r).unop).unop = r) : RingInvo R :=
  { f with
    invFun := fun r => (f r.unop).unop
    left_inv := fun r => involution r
right_inv := fun _ => MulOpposite.unop_injective involution _
    involution' := involution }

@[simp]
/--
theorem `involution` / 定理 `involution`

English:
theorem involution
  given: (f : RingInvo R) (x : R)
  statement: (f (f x).unop).unop = x
  proof: f.involution' x

中文:
定理 involution
  条件: (f : RingInvo R) (x : R)
  结论: (f (f x).unop).unop = x
  证明: f.involution' x

Depends on / 依赖: f.involution, involution
-/
theorem involution (f : RingInvo R) (x : R) : (f (f x).unop).unop = x :=
  f.involution' x

/--
theorem `coe_ringEquiv` / 定理 `coe_ringEquiv`

English:
theorem coe_ringEquiv
  given: (f : RingInvo R) (a : R)
  statement: (f : R ≃+* Rᵐᵒᵖ) a = f a
  proof: rfl

中文:
定理 coe_ringEquiv
  条件: (f : RingInvo R) (a : R)
  结论: (f : R ≃+* Rᵐᵒᵖ) a = f a
  证明: rfl
-/
theorem coe_ringEquiv (f : RingInvo R) (a : R) : (f : R ≃+* Rᵐᵒᵖ) a = f a :=
  rfl

/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: (f : RingInvo R) {x : R}
  statement: f x = 0 ↔ x = 0
  proof: f.toRingEquiv.map_eq_zero_iff

中文:
定理 map_eq_zero_iff
  条件: (f : RingInvo R) {x : R}
  结论: f x = 0 ↔ x = 0
  证明: f.toRingEquiv.map_eq_zero_iff

Depends on / 依赖: f.toRingEquiv.map_eq_zero_iff, map_eq_zero_iff, toRingEquiv
-/
theorem map_eq_zero_iff (f : RingInvo R) {x : R} : f x = 0 ↔ x = 0 :=
  f.toRingEquiv.map_eq_zero_iff

end RingInvo

open RingInvo

section CommRing

variable [CommRing R]

/--
Definition of `RingInvo.id` / `RingInvo.id` 的定义

English:
definition RingInvo.id
  signature: : RingInvo R
  body: { RingEquiv.toOpposite R with involution' := fun _ => rfl }

中文:
定义 RingInvo.id
  签名: : RingInvo R
  定义体: { RingEquiv.toOpposite R with involution' := fun _ => rfl }
-/
protected def RingInvo.id : RingInvo R :=
  { RingEquiv.toOpposite R with involution' := fun _ => rfl }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (RingInvo R)
  body: ⟨RingInvo.id _⟩

中文:
实例 :
  签名: 可居 (RingInvo R)
  定义体: ⟨RingInvo.id _⟩

Depends on / 依赖: RingInvo, RingInvo.id
-/
instance : Inhabited (RingInvo R) :=
  ⟨RingInvo.id _⟩

end CommRing
