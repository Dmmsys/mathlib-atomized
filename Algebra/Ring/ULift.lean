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

/-
**ULift.mulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：mulZeroClass {M₀ : Type*} [MulZeroClass M₀] : MulZeroClass (ULift M₀) wher
e zero_mul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulZeroClass {M₀ : Type*} [MulZeroClass M₀] : MulZeroClass (ULift M₀) where
  zero_mul _ := (Equiv.ulift).injective (by simp)
  mul_zero _ := (Equiv.ulift).injective (by simp)
/-
**ULift.distrib** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：distrib [Distrib R] : Distrib (ULift R) where left_distrib _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distrib [Distrib R] : Distrib (ULift R) where
  left_distrib _ _ _ := (Equiv.ulift).injective (by simp [left_distrib])
  right_distrib _ _ _ := (Equiv.ulift).injective (by simp [right_distrib])
/-
**ULift.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：instNatCast [NatCast R] : NatCast (ULift R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNatCast [NatCast R] : NatCast (ULift R) := ⟨(up ·)⟩
/-
**ULift.instIntCast** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：instIntCast [IntCast R] : IntCast (ULift R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIntCast [IntCast R] : IntCast (ULift R) := ⟨(up ·)⟩

@[simp, norm_cast]
/-
**ULift.up_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：up_natCast [NatCast R] (n : Nat) : up (n : R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem up_natCast [NatCast R] (n : ℕ) : up (n : R) = n :=
  rfl

@[simp]
/-
**ULift.up_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：up_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] : up (ofNat(n) : R) = ofNat(
n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem up_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    up (ofNat(n) : R) = ofNat(n) :=
  rfl

@[simp, norm_cast]
/-
**ULift.up_intCast** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：up_intCast [IntCast R] (n : Int) : up (n : R) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem up_intCast [IntCast R] (n : ℤ) : up (n : R) = n :=
  rfl

@[simp, norm_cast]
/-
**ULift.down_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：down_natCast [NatCast R] (n : Nat) : down (n : ULift R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem down_natCast [NatCast R] (n : ℕ) : down (n : ULift R) = n :=
  rfl

@[simp]
/-
**ULift.down_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：down_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] : down (ofNat(n) : ULift R
) = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem down_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    down (ofNat(n) : ULift R) = ofNat(n) :=
  rfl

@[simp, norm_cast]
/-
**ULift.down_intCast** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：down_intCast [IntCast R] (n : Int) : down (n : ULift R) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem down_intCast [IntCast R] (n : ℤ) : down (n : ULift R) = n :=
  rfl
/-
**ULift.addMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：addMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne (ULift R) where n
atCast_zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne (ULift R) where
  natCast_zero := congr_arg ULift.up Nat.cast_zero
  natCast_succ _ := congr_arg ULift.up (Nat.cast_succ _)
/-
**ULift.addCommMonoidWithOne** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [AddCommMonoidWithOne R] → AddCommMonoidWithOne (ULift.{u_1
, u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne (ULift R) where
/-
**ULift.addGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：addGroupWithOne [AddGroupWithOne R] : AddGroupWithOne (ULift R) where intC
ast_ofNat _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addGroupWithOne [AddGroupWithOne R] : AddGroupWithOne (ULift R) where
  intCast_ofNat _ := congr_arg ULift.up (Int.cast_natCast _)
  intCast_negSucc _ := congr_arg ULift.up (Int.cast_negSucc _)
/-
**ULift.addCommGroupWithOne** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [AddCommGroupWithOne R] → AddCommGroupWithOne (ULift.{u_1, 
u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne (ULift R) where
/-
**ULift.nonUnitalNonAssocSemiring** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [NonUnitalNonAssocSemiring R] → NonUnitalNonAssocSemiring (
ULift.{u_1, u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (ULift R) where
/-
**ULift.nonAssocSemiring** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [NonAssocSemiring R] → NonAssocSemiring (ULift.{u_1, u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring (ULift R) where
/-
**ULift.nonUnitalSemiring** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [NonUnitalSemiring R] → NonUnitalSemiring (ULift.{u_1, u} R
)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring (ULift R) where
/-
**ULift.semiring** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [Semiring R] → Semiring (ULift.{u_1, u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiring [Semiring R] : Semiring (ULift R) where

/-- The ring equivalence between `ULift R` and `R`. -/
/-
**ULift.ringEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：ringEquiv [NonUnitalNonAssocSemiring R] : ULift R ≃+* R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring equivalence between `ULift R` and `R`.
-/
def ringEquiv [NonUnitalNonAssocSemiring R] : ULift R ≃+* R where
  toFun := ULift.down
  invFun := ULift.up
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
/-
**ULift.nonUnitalCommSemiring** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [NonUnitalCommSemiring R] → NonUnitalCommSemiring (ULift.{u
_1, u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring (ULift R) where
/-
**ULift.commSemiring** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [CommSemiring R] → CommSemiring (ULift.{u_1, u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commSemiring [CommSemiring R] : CommSemiring (ULift R) where
/-
**ULift.nonUnitalNonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [NonUnitalNonAssocRing R] → NonUnitalNonAssocRing (ULift.{u
_1, u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (ULift R) where
/-
**ULift.nonUnitalRing** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [NonUnitalRing R] → NonUnitalRing (ULift.{u_1, u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalRing [NonUnitalRing R] : NonUnitalRing (ULift R) where
/-
**ULift.nonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [NonAssocRing R] → NonAssocRing (ULift.{u_1, u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonAssocRing [NonAssocRing R] : NonAssocRing (ULift R) where
/-
**ULift.ring** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [Ring R] → Ring (ULift.{u_1, u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ring [Ring R] : Ring (ULift R) where
/-
**ULift.nonUnitalCommRing** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [NonUnitalCommRing R] → NonUnitalCommRing (ULift.{u_1, u} R
)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing (ULift R) where
/-
**ULift.commRing** 是 Mathlib 中的一个定义，位于命名空间 `ULift`。
形式化陈述：{R : Type u} → [CommRing R] → CommRing (ULift.{u_1, u} R)
参数：ULift.{u_1, u} R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commRing [CommRing R] : CommRing (ULift R) where

end ULift

section RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `ULift` is functorial for ring homomorphisms. -/
@[pp_with_univ]
/-
**RingHom.ulift** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.ulift (f : R ->+* S) : ULift.{u₁} R ->+* ULift.{u₂} S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ULift` is functorial for ring homomorphisms.
-/
def RingHom.ulift (f : R →+* S) : ULift.{u₁} R →+* ULift.{u₂} S :=
  RingHom.comp ULift.ringEquiv.symm.toRingHom (f.comp ULift.ringEquiv.toRingHom)
/-
**RingHom.ulift_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.ulift_apply (f : R ->+* S) (x : ULift.{u₁} R) : f.ulift x = ⟨f x.d
own⟩
参数：f : R ->+* S；x : ULift.{u₁} R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RingHom.ulift_apply (f : R →+* S) (x : ULift.{u₁} R) : f.ulift x = ⟨f x.down⟩ :=
  rfl

@[simp]
/-
**RingHom.down_ulift_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.down_ulift_apply (f : R ->+* S) (x : ULift.{u₁} R) : (f.ulift x).d
own = f x.down
参数：f : R ->+* S；x : ULift.{u₁} R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RingHom.down_ulift_apply (f : R →+* S) (x : ULift.{u₁} R) :
    (f.ulift x).down = f x.down :=
  rfl
/-
**RingHom.comp_ulift_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.comp_ulift_eq (f : R ->+* S) : ULift.ringEquiv.toRingHom.comp ((ul
ift.{u₁, u₂} f).comp ULift.ringEquiv.symm.toRingHom) = f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RingHom.comp_ulift_eq (f : R →+* S) :
    ULift.ringEquiv.toRingHom.comp ((ulift.{u₁, u₂} f).comp ULift.ringEquiv.symm.toRingHom) = f :=
  rfl

end RingHom

