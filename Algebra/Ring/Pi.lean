/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.GroupWithZero.Pi
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Pi instances for ring

This file defines instances for ring, semiring and related structures on Pi Types
-/

@[expose] public section

-- Porting note: used to import `tactic.pi_instances`

namespace Pi

universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I -> Type v}

variable (i : I)

/--
Instance `distrib` / 实例 `distrib`

English:
instance distrib
  signature: [forall i, Distrib <| f i]
  body: by intros; ext; exact mul_add _ _ _
  right_distrib := by intros; ext; exact add_mul _ _ _

中文:
实例 distrib
  签名: [对任意 i, Distrib <| f i]
  定义体: by intros; ext; exact mul_add _ _ _
  right_distrib := by intros; ext; exact add_mul _ _ _

Depends on / 依赖: add_mul, intros, mul_add, right_distrib
-/
instance distrib [forall i, Distrib <| f i] : Distrib (forall i : I, f i) where
  left_distrib := by intros; ext; exact mul_add _ _ _
  right_distrib := by intros; ext; exact add_mul _ _ _

/--
Instance `hasDistribNeg` / 实例 `hasDistribNeg`

English:
instance hasDistribNeg
  signature: [forall i, Mul (f i)] [forall i, HasDistribNeg (f i)]
  body: funext fun _ => neg_mul _ _
  mul_neg _ _ := funext fun _ => mul_neg _ _

中文:
实例 hasDistribNeg
  签名: [对任意 i, 乘法 (f i)] [对任意 i, 有DistribNeg (f i)]
  定义体: funext fun _ => neg_mul _ _
  mul_neg _ _ := funext fun _ => mul_neg _ _

Depends on / 依赖: neg_mul
-/
instance hasDistribNeg [forall i, Mul (f i)] [forall i, HasDistribNeg (f i)] : HasDistribNeg (forall i, f i) where
  neg_mul _ _ := funext fun _ => neg_mul _ _
  mul_neg _ _ := funext fun _ => mul_neg _ _

/--
Instance `addMonoidWithOne` / 实例 `addMonoidWithOne`

English:
instance addMonoidWithOne
  signature: [forall i, AddMonoidWithOne (f i)]
  body: n
  natCast_zero := funext fun _ => AddMonoidWithOne.natCast_zero
  natCast_succ n := funext fun _ => AddMonoidWithOne.natCast_succ n

中文:
实例 addMonoidWithOne
  签名: [对任意 i, 加法带幺幺半群 (f i)]
  定义体: n
  natCast_zero := funext fun _ => AddMonoidWithOne.natCast_zero
  natCast_succ n := funext fun _ => AddMonoidWithOne.natCast_succ n
-/
instance addMonoidWithOne [forall i, AddMonoidWithOne (f i)] : AddMonoidWithOne (forall i, f i) where
  natCast n _ := n
  natCast_zero := funext fun _ => AddMonoidWithOne.natCast_zero
  natCast_succ n := funext fun _ => AddMonoidWithOne.natCast_succ n

/--
Instance `addGroupWithOne` / 实例 `addGroupWithOne`

English:
instance addGroupWithOne
  signature: [forall i, AddGroupWithOne (f i)]
  body: addGroup
  __ := addMonoidWithOne
  intCast n _ := n
  intCast_ofNat n := funext fun _ => AddGroupWithOne.intCast_ofNat n
  intCast_negSucc n := funext fun _ => AddGroupWithOne.intCast_negSucc n

中文:
实例 addGroupWithOne
  签名: [对任意 i, 加法带幺群 (f i)]
  定义体: addGroup
  __ := addMonoidWithOne
  intCast n _ := n
  intCast_ofNat n := funext fun _ => AddGroupWithOne.intCast_ofNat n
  intCast_negSucc n := funext fun _ => AddGroupWithOne.intCast_negSucc n

Depends on / 依赖: IsAffine, IsQuasiAffine, X.IsQuasiAffine, addGroup
-/
instance addGroupWithOne [forall i, AddGroupWithOne (f i)] : AddGroupWithOne (forall i, f i) where
  __ := addGroup
  __ := addMonoidWithOne
  intCast n _ := n
  intCast_ofNat n := funext fun _ => AddGroupWithOne.intCast_ofNat n
  intCast_negSucc n := funext fun _ => AddGroupWithOne.intCast_negSucc n

/--
Instance `nonUnitalNonAssocSemiring` / 实例 `nonUnitalNonAssocSemiring`

English:
instance nonUnitalNonAssocSemiring
  signature: [forall i, NonUnitalNonAssocSemiring <| f i]
  body: { Pi.distrib, Pi.addCommMonoid, Pi.mulZeroClass with }

中文:
实例 nonUnitalNonAssocSemiring
  签名: [对任意 i, 非幺非结合半环 <| f i]
  定义体: { Pi.distrib, Pi.addCommMonoid, Pi.mulZeroClass with }

Depends on / 依赖: IsQuasiAffine, IsSeparated, Pi.addCommMonoid, Pi.distrib, Pi.mulZeroClass, X.IsQuasiAffine, X.IsSeparated, addCommMonoid, distrib, mulZeroClass
-/
instance nonUnitalNonAssocSemiring [forall i, NonUnitalNonAssocSemiring <| f i] :
    NonUnitalNonAssocSemiring (forall i : I, f i) :=
  { Pi.distrib, Pi.addCommMonoid, Pi.mulZeroClass with }

/--
Instance `nonUnitalSemiring` / 实例 `nonUnitalSemiring`

English:
instance nonUnitalSemiring
  signature: [forall i, NonUnitalSemiring <| f i]
  body: { Pi.nonUnitalNonAssocSemiring, Pi.semigroupWithZero with }

中文:
实例 nonUnitalSemiring
  签名: [对任意 i, 非幺半环 <| f i]
  定义体: { Pi.nonUnitalNonAssocSemiring, Pi.semigroupWithZero with }

Depends on / 依赖: Pi.nonUnitalNonAssocSemiring, Pi.semigroupWithZero, nonUnitalNonAssocSemiring, semigroupWithZero
-/
instance nonUnitalSemiring [forall i, NonUnitalSemiring <| f i] : NonUnitalSemiring (forall i : I, f i) :=
  { Pi.nonUnitalNonAssocSemiring, Pi.semigroupWithZero with }

/--
Instance `nonAssocSemiring` / 实例 `nonAssocSemiring`

English:
instance nonAssocSemiring
  signature: [forall i, NonAssocSemiring <| f i]
  body: { Pi.nonUnitalNonAssocSemiring, Pi.mulZeroOneClass, Pi.addMonoidWithOne with }

中文:
实例 nonAssocSemiring
  签名: [对任意 i, 非结合半环 <| f i]
  定义体: { Pi.nonUnitalNonAssocSemiring, Pi.mulZeroOneClass, Pi.addMonoidWithOne with }

Depends on / 依赖: Pi.addMonoidWithOne, Pi.mulZeroOneClass, Pi.nonUnitalNonAssocSemiring, addMonoidWithOne, mulZeroOneClass, nonUnitalNonAssocSemiring
-/
instance nonAssocSemiring [forall i, NonAssocSemiring <| f i] : NonAssocSemiring (forall i : I, f i) :=
  { Pi.nonUnitalNonAssocSemiring, Pi.mulZeroOneClass, Pi.addMonoidWithOne with }

/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: [forall i, Semiring <| f i]
  body: { Pi.nonUnitalSemiring, Pi.nonAssocSemiring, Pi.monoidWithZero with }

中文:
实例 semiring
  签名: [对任意 i, 半环 <| f i]
  定义体: { Pi.nonUnitalSemiring, Pi.nonAssocSemiring, Pi.monoidWithZero with }

Depends on / 依赖: Pi.monoidWithZero, Pi.nonAssocSemiring, Pi.nonUnitalSemiring, monoidWithZero, nonAssocSemiring, nonUnitalSemiring
-/
instance semiring [forall i, Semiring <| f i] : Semiring (forall i : I, f i) :=
  { Pi.nonUnitalSemiring, Pi.nonAssocSemiring, Pi.monoidWithZero with }

/--
Instance `nonUnitalCommSemiring` / 实例 `nonUnitalCommSemiring`

English:
instance nonUnitalCommSemiring
  signature: [forall i, NonUnitalCommSemiring <| f i]
  body: { Pi.nonUnitalSemiring, Pi.commSemigroup with }

中文:
实例 nonUnitalCommSemiring
  签名: [对任意 i, 非幺交换半环 <| f i]
  定义体: { Pi.nonUnitalSemiring, Pi.commSemigroup with }

Depends on / 依赖: Pi.commSemigroup, Pi.nonUnitalSemiring, commSemigroup, nonUnitalSemiring
-/
instance nonUnitalCommSemiring [forall i, NonUnitalCommSemiring <| f i] :
    NonUnitalCommSemiring (forall i : I, f i) :=
  { Pi.nonUnitalSemiring, Pi.commSemigroup with }

/--
Instance `commSemiring` / 实例 `commSemiring`

English:
instance commSemiring
  signature: [forall i, CommSemiring <| f i]
  body: { Pi.semiring, Pi.commMonoid with }

中文:
实例 commSemiring
  签名: [对任意 i, 交换半环 <| f i]
  定义体: { Pi.semiring, Pi.commMonoid with }

Depends on / 依赖: Pi.commMonoid, Pi.semiring, commMonoid, semiring
-/
instance commSemiring [forall i, CommSemiring <| f i] : CommSemiring (forall i : I, f i) :=
  { Pi.semiring, Pi.commMonoid with }

/--
Instance `nonUnitalNonAssocRing` / 实例 `nonUnitalNonAssocRing`

English:
instance nonUnitalNonAssocRing
  signature: [forall i, NonUnitalNonAssocRing <| f i]
  body: { Pi.addCommGroup, Pi.nonUnitalNonAssocSemiring with }

中文:
实例 nonUnitalNonAssocRing
  签名: [对任意 i, 非幺非结合环 <| f i]
  定义体: { Pi.addCommGroup, Pi.nonUnitalNonAssocSemiring with }

Depends on / 依赖: Pi.addCommGroup, Pi.nonUnitalNonAssocSemiring, addCommGroup, nonUnitalNonAssocSemiring
-/
instance nonUnitalNonAssocRing [forall i, NonUnitalNonAssocRing <| f i] :
    NonUnitalNonAssocRing (forall i : I, f i) :=
  { Pi.addCommGroup, Pi.nonUnitalNonAssocSemiring with }

/--
Instance `nonUnitalRing` / 实例 `nonUnitalRing`

English:
instance nonUnitalRing
  signature: [forall i, NonUnitalRing <| f i]
  body: { Pi.nonUnitalNonAssocRing, Pi.nonUnitalSemiring with }

中文:
实例 nonUnitalRing
  签名: [对任意 i, 非幺环 <| f i]
  定义体: { Pi.nonUnitalNonAssocRing, Pi.nonUnitalSemiring with }

Depends on / 依赖: Pi.nonUnitalNonAssocRing, Pi.nonUnitalSemiring, nonUnitalNonAssocRing, nonUnitalSemiring
-/
instance nonUnitalRing [forall i, NonUnitalRing <| f i] : NonUnitalRing (forall i : I, f i) :=
  { Pi.nonUnitalNonAssocRing, Pi.nonUnitalSemiring with }

/--
Instance `nonAssocRing` / 实例 `nonAssocRing`

English:
instance nonAssocRing
  signature: [forall i, NonAssocRing <| f i]
  body: { Pi.nonUnitalNonAssocRing, Pi.nonAssocSemiring, Pi.addGroupWithOne with }

中文:
实例 nonAssocRing
  签名: [对任意 i, 非结合环 <| f i]
  定义体: { Pi.nonUnitalNonAssocRing, Pi.nonAssocSemiring, Pi.addGroupWithOne with }

Depends on / 依赖: Pi.addGroupWithOne, Pi.nonAssocSemiring, Pi.nonUnitalNonAssocRing, addGroupWithOne, nonAssocSemiring, nonUnitalNonAssocRing
-/
instance nonAssocRing [forall i, NonAssocRing <| f i] : NonAssocRing (forall i : I, f i) :=
  { Pi.nonUnitalNonAssocRing, Pi.nonAssocSemiring, Pi.addGroupWithOne with }

/--
Instance `ring` / 实例 `ring`

English:
instance ring
  signature: [forall i, Ring <| f i]
  body: { Pi.semiring, Pi.addCommGroup, Pi.addGroupWithOne with }

中文:
实例 ring
  签名: [对任意 i, 环 <| f i]
  定义体: { Pi.semiring, Pi.addCommGroup, Pi.addGroupWithOne with }

Depends on / 依赖: MorphismProperty, MorphismProperty.of_isPullback, Pi.addCommGroup, Pi.addGroupWithOne, Pi.semiring, addCommGroup, addGroupWithOne, d.equifibered, equifibered, infer_instance, of_isPullback, semiring
-/
instance ring [forall i, Ring <| f i] : Ring (forall i : I, f i) :=
  { Pi.semiring, Pi.addCommGroup, Pi.addGroupWithOne with }

/--
Instance `nonUnitalCommRing` / 实例 `nonUnitalCommRing`

English:
instance nonUnitalCommRing
  signature: [forall i, NonUnitalCommRing <| f i]
  body: { Pi.nonUnitalRing, Pi.commSemigroup with }

中文:
实例 nonUnitalCommRing
  签名: [对任意 i, 非幺交换环 <| f i]
  定义体: { Pi.nonUnitalRing, Pi.commSemigroup with }

Depends on / 依赖: Pi.commSemigroup, Pi.nonUnitalRing, commSemigroup, nonUnitalRing
-/
instance nonUnitalCommRing [forall i, NonUnitalCommRing <| f i] : NonUnitalCommRing (forall i : I, f i) :=
  { Pi.nonUnitalRing, Pi.commSemigroup with }

/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: [forall i, CommRing <| f i]
  body: { Pi.ring, Pi.commSemiring with }

中文:
实例 commRing
  签名: [对任意 i, 交换环 <| f i]
  定义体: { Pi.ring, Pi.commSemiring with }

Depends on / 依赖: Pi.commSemiring, Pi.ring, commSemiring
-/
instance commRing [forall i, CommRing <| f i] : CommRing (forall i : I, f i) :=
  { Pi.ring, Pi.commSemiring with }

end Pi

section NonUnitalRingHom

universe u v

variable {I : Type u}

/-- A family of non-unital ring homomorphisms `f a : γ →ₙ+* β a` defines a non-unital ring
homomorphism `NonUnitalRingHom.pi f : γ →+* Π a, β a` given by
`NonUnitalRingHom.pi f x b = f b x`. -/
@[simps]
/--
Definition of `NonUnitalRingHom.pi` / `NonUnitalRingHom.pi` 的定义

English:
definition NonUnitalRingHom.pi
  signature: {f : I -> Type*} {γ : Type*} [forall i, NonUnitalNonAssocSemiring (f i)]
  body: { MulHom.pi fun i => (g i).toMulHom, AddMonoidHom.pi fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }

@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom := NonUnitalRingHom.pi
@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom_apply :=

中文:
定义 非幺环态射.pi
  签名: {f : I -> 类型} {γ : 类型} [对任意 i, 非幺非结合半环 (f i)]
  定义体: { MulHom.pi fun i => (g i).toMulHom, AddMonoidHom.pi fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }

@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom := NonUnitalRingHom.pi
@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom_apply :=

Depends on / 依赖: AddMonoidHom, AddMonoidHom.pi, MulHom, MulHom.pi, toAddMonoidHom, toMulHom
-/
def NonUnitalRingHom.pi {f : I -> Type*} {γ : Type*} [forall i, NonUnitalNonAssocSemiring (f i)]
    [NonUnitalNonAssocSemiring γ] (g : forall i, γ ->ₙ+* f i) : γ ->ₙ+* forall i, f i :=
  { MulHom.pi fun i => (g i).toMulHom, AddMonoidHom.pi fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }

@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom := NonUnitalRingHom.pi
@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom_apply :=
  NonUnitalRingHom.pi_apply

/--
theorem `NonUnitalRingHom.pi_injective` / 定理 `NonUnitalRingHom.pi_injective`

English:
theorem NonUnitalRingHom.pi_injective
  statement: {f : I -> Type*} {γ : Type*} [Nonempty I]
  proof: MulHom.pi_injective (fun i => (g i).toMulHom) hg

@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom_injective :=
  NonUnitalRingHom.pi_injective

中文:
定理 非幺环态射.pi_injective
  结论: {f : I -> 类型} {γ : 类型} [非空 I]
  证明: MulHom.pi_injective (fun i => (g i).toMulHom) hg

@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom_injective :=
  NonUnitalRingHom.pi_injective

Depends on / 依赖: MulHom, MulHom.pi_injective, pi_injective, toMulHom
-/
theorem NonUnitalRingHom.pi_injective {f : I -> Type*} {γ : Type*} [Nonempty I]
    [forall i, NonUnitalNonAssocSemiring (f i)] [NonUnitalNonAssocSemiring γ] (g : forall i, γ ->ₙ+* f i)
    (hg : forall i, Function.Injective (g i)) : Function.Injective (NonUnitalRingHom.pi g) :=
  MulHom.pi_injective (fun i => (g i).toMulHom) hg

@[deprecated (since := "2026-05-30")] protected alias Pi.nonUnitalRingHom_injective :=
  NonUnitalRingHom.pi_injective

/-- Evaluation of functions into an indexed collection of non-unital rings at a point is a
non-unital ring homomorphism. This is `Function.eval` as a `NonUnitalRingHom`. -/
@[simps!]
/--
Definition of `Pi.evalNonUnitalRingHom` / `Pi.evalNonUnitalRingHom` 的定义

English:
definition Pi.evalNonUnitalRingHom
  signature: (f : I -> Type v) [forall i, NonUnitalNonAssocSemiring (f i)] (i : I)
  body: { Pi.evalMulHom f i, Pi.evalAddMonoidHom f i with }

中文:
定义 依赖函数类型.evalNonUnitalRingHom
  签名: (f : I -> 类型v) [对任意 i, 非幺非结合半环 (f i)] (i : I)
  定义体: { Pi.evalMulHom f i, Pi.evalAddMonoidHom f i with }

Depends on / 依赖: Pi.evalAddMonoidHom, Pi.evalMulHom, evalAddMonoidHom, evalMulHom
-/
def Pi.evalNonUnitalRingHom (f : I -> Type v) [forall i, NonUnitalNonAssocSemiring (f i)] (i : I) :
    (forall i, f i) ->ₙ+* f i :=
  { Pi.evalMulHom f i, Pi.evalAddMonoidHom f i with }

/-- `Function.const` as a `NonUnitalRingHom`. -/
@[simps]
/--
Definition of `Pi.constNonUnitalRingHom` / `Pi.constNonUnitalRingHom` 的定义

English:
definition Pi.constNonUnitalRingHom
  signature: (α β : Type*) [NonUnitalNonAssocSemiring β]
  body: { NonUnitalRingHom.pi fun _ => NonUnitalRingHom.id β with toFun := Function.const _ }

中文:
定义 依赖函数类型.constNonUnitalRingHom
  签名: (α β : 类型) [非幺非结合半环 β]
  定义体: { NonUnitalRingHom.pi fun _ => NonUnitalRingHom.id β with toFun := Function.const _ }

Depends on / 依赖: Function, Function.const, NonUnitalRingHom, NonUnitalRingHom.id, NonUnitalRingHom.pi
-/
def Pi.constNonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring β] : β ->ₙ+* α -> β :=
  { NonUnitalRingHom.pi fun _ => NonUnitalRingHom.id β with toFun := Function.const _ }

/-- Non-unital ring homomorphism between the function spaces `I → α` and `I → β`, induced by a
non-unital ring homomorphism `f` between `α` and `β`. -/
@[simps]
/--
Definition of `NonUnitalRingHom.compLeft` / `NonUnitalRingHom.compLeft` 的定义

English:
definition NonUnitalRingHom.compLeft
  signature: {α β : Type*} [NonUnitalNonAssocSemiring α]
  body: { f.toMulHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }

中文:
定义 非幺环态射.compLeft
  签名: {α β : 类型} [非幺非结合半环 α]
  定义体: { f.toMulHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }
-/
protected def NonUnitalRingHom.compLeft {α β : Type*} [NonUnitalNonAssocSemiring α]
    [NonUnitalNonAssocSemiring β] (f : α ->ₙ+* β) (I : Type*) : (I -> α) ->ₙ+* I -> β :=
  { f.toMulHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }

end NonUnitalRingHom

section RingHom

universe u v

variable {I : Type u}

/-- A family of ring homomorphisms `f a : γ →+* β a` defines a ring homomorphism
`RingHom.pi f : γ →+* Π a, β a` given by `RingHom.pi f x b = f b x`. -/
@[simps]
/--
Definition of `RingHom.pi` / `RingHom.pi` 的定义

English:
definition RingHom.pi
  signature: {f : I -> Type*} {γ : Type*} [forall i, NonAssocSemiring (f i)]
  body: { MonoidHom.pi fun i => (g i).toMonoidHom, AddMonoidHom.pi fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }

@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom := RingHom.pi
@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom_apply := RingHom.pi_apply

中文:
定义 环态射.pi
  签名: {f : I -> 类型} {γ : 类型} [对任意 i, 非结合半环 (f i)]
  定义体: { MonoidHom.pi fun i => (g i).toMonoidHom, AddMonoidHom.pi fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }

@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom := RingHom.pi
@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom_apply := RingHom.pi_apply
-/
protected def RingHom.pi {f : I -> Type*} {γ : Type*} [forall i, NonAssocSemiring (f i)]
    [NonAssocSemiring γ] (g : forall i, γ ->+* f i) : γ ->+* forall i, f i :=
  { MonoidHom.pi fun i => (g i).toMonoidHom, AddMonoidHom.pi fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }

@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom := RingHom.pi
@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom_apply := RingHom.pi_apply

/--
theorem `RingHom.pi_injective` / 定理 `RingHom.pi_injective`

English:
theorem RingHom.pi_injective
  statement: {f : I -> Type*} {γ : Type*} [Nonempty I] [forall i, NonAssocSemiring (f i)]
  proof: MonoidHom.pi_injective (fun i => (g i).toMonoidHom) hg

@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom_injective := RingHom.pi_injective

中文:
定理 环态射.pi_injective
  结论: {f : I -> 类型} {γ : 类型} [非空 I] [对任意 i, 非结合半环 (f i)]
  证明: MonoidHom.pi_injective (fun i => (g i).toMonoidHom) hg

@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom_injective := RingHom.pi_injective

Depends on / 依赖: MonoidHom, MonoidHom.pi_injective, pi_injective, toMonoidHom
-/
theorem RingHom.pi_injective {f : I -> Type*} {γ : Type*} [Nonempty I] [forall i, NonAssocSemiring (f i)]
    [NonAssocSemiring γ] (g : forall i, γ ->+* f i) (hg : forall i, Function.Injective (g i)) :
    Function.Injective (RingHom.pi g) :=
  MonoidHom.pi_injective (fun i => (g i).toMonoidHom) hg

@[deprecated (since := "2026-05-30")] protected alias Pi.ringHom_injective := RingHom.pi_injective

/-- Evaluation of functions into an indexed collection of rings at a point is a ring
homomorphism. This is `Function.eval` as a `RingHom`. -/
@[simps!]
/--
Definition of `Pi.evalRingHom` / `Pi.evalRingHom` 的定义

English:
definition Pi.evalRingHom
  signature: (f : I -> Type v) [forall i, NonAssocSemiring (f i)] (i : I)
  body: { Pi.evalMonoidHom f i, Pi.evalAddMonoidHom f i with }

中文:
定义 依赖函数类型.evalRingHom
  签名: (f : I -> 类型v) [对任意 i, 非结合半环 (f i)] (i : I)
  定义体: { Pi.evalMonoidHom f i, Pi.evalAddMonoidHom f i with }

Depends on / 依赖: Pi.evalAddMonoidHom, Pi.evalMonoidHom, evalAddMonoidHom, evalMonoidHom
-/
def Pi.evalRingHom (f : I -> Type v) [forall i, NonAssocSemiring (f i)] (i : I) : (forall i, f i) ->+* f i :=
  { Pi.evalMonoidHom f i, Pi.evalAddMonoidHom f i with }

instance (f : I -> Type*) [forall i, Semiring (f i)] (i) :
    RingHomSurjective (Pi.evalRingHom f i) where
  is_surjective x := ⟨by classical exact (if h : · = i then h ▸ x else 0), by simp⟩

/-- `Function.const` as a `RingHom`. -/
@[simps]
/--
Definition of `Pi.constRingHom` / `Pi.constRingHom` 的定义

English:
definition Pi.constRingHom
  signature: (α β : Type*) [NonAssocSemiring β]
  body: { RingHom.pi fun _ => RingHom.id β with toFun := Function.const _ }

中文:
定义 依赖函数类型.constRingHom
  签名: (α β : 类型) [非结合半环 β]
  定义体: { RingHom.pi fun _ => RingHom.id β with toFun := Function.const _ }

Depends on / 依赖: Function, Function.const, RingHom, RingHom.id, RingHom.pi
-/
def Pi.constRingHom (α β : Type*) [NonAssocSemiring β] : β ->+* α -> β :=
  { RingHom.pi fun _ => RingHom.id β with toFun := Function.const _ }

/-- Ring homomorphism between the function spaces `I → α` and `I → β`, induced by a ring
homomorphism `f` between `α` and `β`. -/
@[simps]
/--
Definition of `RingHom.compLeft` / `RingHom.compLeft` 的定义

English:
definition RingHom.compLeft
  signature: {α β : Type*} [NonAssocSemiring α] [NonAssocSemiring β]
  body: { f.toMonoidHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }

中文:
定义 环态射.compLeft
  签名: {α β : 类型} [非结合半环 α] [非结合半环 β]
  定义体: { f.toMonoidHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }

Depends on / 依赖: IsLocalRing, IsLocalRing.ResidueField, ResidueField, X.presheaf.stalk, presheaf
-/
protected def RingHom.compLeft {α β : Type*} [NonAssocSemiring α] [NonAssocSemiring β]
    (f : α ->+* β) (I : Type*) : (I -> α) ->+* I -> β :=
  { f.toMonoidHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }

end RingHom
