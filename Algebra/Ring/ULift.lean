/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Tactic.PPWithUniv

/-!
# `ULift` instances for ring

This file defines instances for ring, semiring and related structures on `ULift` types.

(Recall `ULift R` is just a "copy" of a type `R` in a higher universe.)

We also provide `ULift.ringEquiv : ULift R ≃+* R`.
-/

@[expose] public section


universe u u₁ u₂

variable {R : Type u}
namespace ULift

/--
Instance `mulZeroClass` / 实例 `mulZeroClass`

English:
instance mulZeroClass
  signature: {M₀ : Type*} [MulZeroClass M₀]
  body: (Equiv.ulift).injective (by simp)
  mul_zero _ := (Equiv.ulift).injective (by simp)

中文:
实例 mulZeroClass
  签名: {M₀ : 类型} [MulZeroClass M₀]
  定义体: (Equiv.ulift).injective (by simp)
  mul_zero _ := (Equiv.ulift).injective (by simp)

Depends on / 依赖: Equiv.ulift, injective
-/
instance mulZeroClass {M₀ : Type*} [MulZeroClass M₀] : MulZeroClass (ULift M₀) where
  zero_mul _ := (Equiv.ulift).injective (by simp)
  mul_zero _ := (Equiv.ulift).injective (by simp)

/--
Instance `distrib` / 实例 `distrib`

English:
instance distrib
  signature: [Distrib R]
  body: (Equiv.ulift).injective (by simp [left_distrib])
  right_distrib _ _ _ := (Equiv.ulift).injective (by simp [right_distrib])

中文:
实例 distrib
  签名: [Distrib R]
  定义体: (Equiv.ulift).injective (by simp [left_distrib])
  right_distrib _ _ _ := (Equiv.ulift).injective (by simp [right_distrib])

Depends on / 依赖: Equiv.ulift, injective, left_distrib
-/
instance distrib [Distrib R] : Distrib (ULift R) where
  left_distrib _ _ _ := (Equiv.ulift).injective (by simp [left_distrib])
  right_distrib _ _ _ := (Equiv.ulift).injective (by simp [right_distrib])

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: [NatCast R]
  body: ⟨(up ·)⟩

中文:
实例 instNatCast
  签名: [自然数Cast R]
  定义体: ⟨(up ·)⟩
-/
instance instNatCast [NatCast R] : NatCast (ULift R) := ⟨(up ·)⟩
/--
Instance `instIntCast` / 实例 `instIntCast`

English:
instance instIntCast
  signature: [IntCast R]
  body: ⟨(up ·)⟩

@[simp, norm_cast]

中文:
实例 instIntCast
  签名: [整数Cast R]
  定义体: ⟨(up ·)⟩

@[simp, norm_cast]
-/
instance instIntCast [IntCast R] : IntCast (ULift R) := ⟨(up ·)⟩

@[simp, norm_cast]
/--
theorem `up_natCast` / 定理 `up_natCast`

English:
theorem up_natCast
  given: [NatCast R] (n : Nat)
  statement: up (n : R) = n
  proof: rfl

@[simp]

中文:
定理 up_natCast
  条件: [自然数Cast R] (n : 自然数)
  结论: up (n : R) = n
  证明: rfl

@[simp]
-/
theorem up_natCast [NatCast R] (n : Nat) : up (n : R) = n :=
  rfl

@[simp]
/--
theorem `up_ofNat` / 定理 `up_ofNat`

English:
theorem up_ofNat
  given: [NatCast R] (n : Nat) [n.AtLeastTwo]
  proof: rfl

@[simp, norm_cast]

中文:
定理 up_ofNat
  条件: [自然数Cast R] (n : 自然数) [n.AtLeastTwo]
  证明: rfl

@[simp, norm_cast]
-/
theorem up_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] :
    up (ofNat(n) : R) = ofNat(n) :=
  rfl

@[simp, norm_cast]
/--
theorem `up_intCast` / 定理 `up_intCast`

English:
theorem up_intCast
  given: [IntCast R] (n : Int)
  statement: up (n : R) = n
  proof: rfl

@[simp, norm_cast]

中文:
定理 up_intCast
  条件: [整数Cast R] (n : 整数)
  结论: up (n : R) = n
  证明: rfl

@[simp, norm_cast]
-/
theorem up_intCast [IntCast R] (n : Int) : up (n : R) = n :=
  rfl

@[simp, norm_cast]
/--
theorem `down_natCast` / 定理 `down_natCast`

English:
theorem down_natCast
  given: [NatCast R] (n : Nat)
  statement: down (n : ULift R) = n
  proof: rfl

@[simp]

中文:
定理 down_natCast
  条件: [自然数Cast R] (n : 自然数)
  结论: down (n : ULift R) = n
  证明: rfl

@[simp]
-/
theorem down_natCast [NatCast R] (n : Nat) : down (n : ULift R) = n :=
  rfl

@[simp]
/--
theorem `down_ofNat` / 定理 `down_ofNat`

English:
theorem down_ofNat
  given: [NatCast R] (n : Nat) [n.AtLeastTwo]
  proof: rfl

@[simp, norm_cast]

中文:
定理 down_ofNat
  条件: [自然数Cast R] (n : 自然数) [n.AtLeastTwo]
  证明: rfl

@[simp, norm_cast]
-/
theorem down_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] :
    down (ofNat(n) : ULift R) = ofNat(n) :=
  rfl

@[simp, norm_cast]
/--
theorem `down_intCast` / 定理 `down_intCast`

English:
theorem down_intCast
  given: [IntCast R] (n : Int)
  statement: down (n : ULift R) = n
  proof: rfl

中文:
定理 down_intCast
  条件: [整数Cast R] (n : 整数)
  结论: down (n : ULift R) = n
  证明: rfl
-/
theorem down_intCast [IntCast R] (n : Int) : down (n : ULift R) = n :=
  rfl

/--
Instance `addMonoidWithOne` / 实例 `addMonoidWithOne`

English:
instance addMonoidWithOne
  signature: [AddMonoidWithOne R]
  body: congr_arg ULift.up Nat.cast_zero
  natCast_succ _ := congr_arg ULift.up (Nat.cast_succ _)

中文:
实例 addMonoidWithOne
  签名: [AddMonoidWithOne R]
  定义体: congr_arg ULift.up Nat.cast_zero
  natCast_succ _ := congr_arg ULift.up (Nat.cast_succ _)

Depends on / 依赖: Nat.cast_zero, ULift.up, cast_zero, congr_arg
-/
instance addMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne (ULift R) where
  natCast_zero := congr_arg ULift.up Nat.cast_zero
  natCast_succ _ := congr_arg ULift.up (Nat.cast_succ _)

/--
Instance `addCommMonoidWithOne` / 实例 `addCommMonoidWithOne`

English:
instance addCommMonoidWithOne
  signature: [AddCommMonoidWithOne R]

中文:
实例 addCommMonoidWithOne
  签名: [AddCommMonoidWithOne R]
-/
instance addCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne (ULift R) where

/--
Instance `addGroupWithOne` / 实例 `addGroupWithOne`

English:
instance addGroupWithOne
  signature: [AddGroupWithOne R]
  body: congr_arg ULift.up (Int.cast_natCast _)
  intCast_negSucc _ := congr_arg ULift.up (Int.cast_negSucc _)

中文:
实例 addGroupWithOne
  签名: [AddGroupWithOne R]
  定义体: congr_arg ULift.up (Int.cast_natCast _)
  intCast_negSucc _ := congr_arg ULift.up (Int.cast_negSucc _)

Depends on / 依赖: Int.cast_natCast, ULift.up, cast_natCast, congr_arg
-/
instance addGroupWithOne [AddGroupWithOne R] : AddGroupWithOne (ULift R) where
  intCast_ofNat _ := congr_arg ULift.up (Int.cast_natCast _)
  intCast_negSucc _ := congr_arg ULift.up (Int.cast_negSucc _)

/--
Instance `addCommGroupWithOne` / 实例 `addCommGroupWithOne`

English:
instance addCommGroupWithOne
  signature: [AddCommGroupWithOne R]

中文:
实例 addCommGroupWithOne
  签名: [AddCommGroupWithOne R]
-/
instance addCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne (ULift R) where

/--
Instance `nonUnitalNonAssocSemiring` / 实例 `nonUnitalNonAssocSemiring`

English:
instance nonUnitalNonAssocSemiring
  signature: [NonUnitalNonAssocSemiring R]

中文:
实例 nonUnitalNonAssocSemiring
  签名: [NonUnitalNonAssocSemiring R]
-/
instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (ULift R) where

/--
Instance `nonAssocSemiring` / 实例 `nonAssocSemiring`

English:
instance nonAssocSemiring
  signature: [NonAssocSemiring R]

中文:
实例 nonAssocSemiring
  签名: [NonAssocSemiring R]
-/
instance nonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring (ULift R) where

/--
Instance `nonUnitalSemiring` / 实例 `nonUnitalSemiring`

English:
instance nonUnitalSemiring
  signature: [NonUnitalSemiring R]

中文:
实例 nonUnitalSemiring
  签名: [NonUnitalSemiring R]
-/
instance nonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring (ULift R) where

/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: [Semiring R]

中文:
实例 semiring
  签名: [Semiring R]
-/
instance semiring [Semiring R] : Semiring (ULift R) where

/--
Definition of `ringEquiv` / `ringEquiv` 的定义

English:
definition ringEquiv
  signature: [NonUnitalNonAssocSemiring R]
  body: ULift.down
  invFun := ULift.up
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 ringEquiv
  签名: [NonUnitalNonAssocSemiring R]
  定义体: ULift.down
  invFun := ULift.up
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: ULift.down
-/
def ringEquiv [NonUnitalNonAssocSemiring R] : ULift R ≃+* R where
  toFun := ULift.down
  invFun := ULift.up
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/--
Instance `nonUnitalCommSemiring` / 实例 `nonUnitalCommSemiring`

English:
instance nonUnitalCommSemiring
  signature: [NonUnitalCommSemiring R]

中文:
实例 nonUnitalCommSemiring
  签名: [NonUnitalCommSemiring R]
-/
instance nonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring (ULift R) where

/--
Instance `commSemiring` / 实例 `commSemiring`

English:
instance commSemiring
  signature: [CommSemiring R]

中文:
实例 commSemiring
  签名: [CommSemiring R]
-/
instance commSemiring [CommSemiring R] : CommSemiring (ULift R) where

/--
Instance `nonUnitalNonAssocRing` / 实例 `nonUnitalNonAssocRing`

English:
instance nonUnitalNonAssocRing
  signature: [NonUnitalNonAssocRing R]

中文:
实例 nonUnitalNonAssocRing
  签名: [NonUnitalNonAssocRing R]
-/
instance nonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (ULift R) where

/--
Instance `nonUnitalRing` / 实例 `nonUnitalRing`

English:
instance nonUnitalRing
  signature: [NonUnitalRing R]

中文:
实例 nonUnitalRing
  签名: [NonUnitalRing R]
-/
instance nonUnitalRing [NonUnitalRing R] : NonUnitalRing (ULift R) where

/--
Instance `nonAssocRing` / 实例 `nonAssocRing`

English:
instance nonAssocRing
  signature: [NonAssocRing R]

中文:
实例 nonAssocRing
  签名: [NonAssocRing R]
-/
instance nonAssocRing [NonAssocRing R] : NonAssocRing (ULift R) where

/--
Instance `ring` / 实例 `ring`

English:
instance ring
  signature: [Ring R]

中文:
实例 ring
  签名: [Ring R]
-/
instance ring [Ring R] : Ring (ULift R) where

/--
Instance `nonUnitalCommRing` / 实例 `nonUnitalCommRing`

English:
instance nonUnitalCommRing
  signature: [NonUnitalCommRing R]

中文:
实例 nonUnitalCommRing
  签名: [NonUnitalCommRing R]

Depends on / 依赖: h1.out.pow, h2.out.pow, isElliptic_iff
-/
instance nonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing (ULift R) where

/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: [CommRing R]

中文:
实例 commRing
  签名: [CommRing R]
-/
instance commRing [CommRing R] : CommRing (ULift R) where

end ULift

section RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `ULift` is functorial for ring homomorphisms. -/
@[pp_with_univ]
/--
Definition of `RingHom.ulift` / `RingHom.ulift` 的定义

English:
definition RingHom.ulift
  signature: (f : R ->+* S)
  body: RingHom.comp ULift.ringEquiv.symm.toRingHom (f.comp ULift.ringEquiv.toRingHom)

中文:
定义 RingHom.ulift
  签名: (f : R ->+* S)
  定义体: RingHom.comp ULift.ringEquiv.symm.toRingHom (f.comp ULift.ringEquiv.toRingHom)

Depends on / 依赖: RingHom, RingHom.comp, ULift.ringEquiv.symm.toRingHom, ULift.ringEquiv.toRingHom, f.comp, ringEquiv, toRingHom
-/
def RingHom.ulift (f : R ->+* S) : ULift.{u₁} R ->+* ULift.{u₂} S :=
  RingHom.comp ULift.ringEquiv.symm.toRingHom (f.comp ULift.ringEquiv.toRingHom)

/--
lemma `RingHom.ulift_apply` / 引理 `RingHom.ulift_apply`

English:
lemma RingHom.ulift_apply
  given: (f : R ->+* S) (x : ULift.{u₁} R)
  statement: f.ulift x = ⟨f x.down⟩
  proof: rfl

@[simp]

中文:
引理 RingHom.ulift_apply
  条件: (f : R ->+* S) (x : ULift.{u₁} R)
  结论: f.ulift x = ⟨f x.down⟩
  证明: rfl

@[simp]
-/
lemma RingHom.ulift_apply (f : R ->+* S) (x : ULift.{u₁} R) : f.ulift x = ⟨f x.down⟩ :=
  rfl

@[simp]
/--
lemma `RingHom.down_ulift_apply` / 引理 `RingHom.down_ulift_apply`

English:
lemma RingHom.down_ulift_apply
  given: (f : R ->+* S) (x : ULift.{u₁} R)
  proof: rfl

中文:
引理 RingHom.down_ulift_apply
  条件: (f : R ->+* S) (x : ULift.{u₁} R)
  证明: rfl
-/
lemma RingHom.down_ulift_apply (f : R ->+* S) (x : ULift.{u₁} R) :
    (f.ulift x).down = f x.down :=
  rfl

/--
lemma `RingHom.comp_ulift_eq` / 引理 `RingHom.comp_ulift_eq`

English:
lemma RingHom.comp_ulift_eq
  given: (f : R ->+* S)
  proof: rfl

中文:
引理 RingHom.comp_ulift_eq
  条件: (f : R ->+* S)
  证明: rfl
-/
lemma RingHom.comp_ulift_eq (f : R ->+* S) :
    ULift.ringEquiv.toRingHom.comp ((ulift.{u₁, u₂} f).comp ULift.ringEquiv.symm.toRingHom) = f :=
  rfl

end RingHom
