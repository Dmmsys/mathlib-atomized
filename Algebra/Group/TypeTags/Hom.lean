/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Transport algebra morphisms between additive and multiplicative types.
-/

@[expose] public section

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

variable {M N α β : Type*}

/-- Reinterpret `α →+ β` as `Multiplicative α →* Multiplicative β`. -/
@[simps]
/--
Definition of `AddMonoidHom.toMultiplicative` / `AddMonoidHom.toMultiplicative` 的定义

English:
definition AddMonoidHom.toMultiplicative
  signature: [AddZeroClass α] [AddZeroClass β]
  body: {
    toFun := fun a => ofAdd (f a.toAdd)
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
.toAdd toFun := fun a => f (ofAdd a)
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]

中文:
定义 加法幺半群态射.toMultiplicative
  签名: [加法零类 α] [加法零类 β]
  定义体: {
    toFun := fun a => ofAdd (f a.toAdd)
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
.toAdd toFun := fun a => f (ofAdd a)
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
-/
def AddMonoidHom.toMultiplicative [AddZeroClass α] [AddZeroClass β] :
    (α ->+ β) ≃ (Multiplicative α ->* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f a.toAdd)
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
.toAdd toFun := fun a => f (ofAdd a)
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
/--
lemma `AddMonoidHom.coe_toMultiplicative` / 引理 `AddMonoidHom.coe_toMultiplicative`

English:
lemma AddMonoidHom.coe_toMultiplicative
  given: [AddZeroClass α] [AddZeroClass β] (f : α ->+ β)
  proof: rfl

@[simp]

中文:
引理 加法幺半群态射.coe_toMultiplicative
  条件: [加法零类 α] [加法零类 β] (f : α ->+ β)
  证明: rfl

@[simp]
-/
lemma AddMonoidHom.coe_toMultiplicative [AddZeroClass α] [AddZeroClass β] (f : α ->+ β) :
    ⇑(toMultiplicative f) = ofAdd ∘ f ∘ toAdd := rfl

@[simp]
/--
lemma `AddMonoidHom.toMultiplicative_id` / 引理 `AddMonoidHom.toMultiplicative_id`

English:
lemma AddMonoidHom.toMultiplicative_id
  given: [AddZeroClass α]
  statement: (id α).toMultiplicative = .id _
  proof: rfl

中文:
引理 加法幺半群态射.toMultiplicative_id
  条件: [加法零类 α]
  结论: (id α).toMultiplicative = .id _
  证明: rfl
-/
lemma AddMonoidHom.toMultiplicative_id [AddZeroClass α] : (id α).toMultiplicative = .id _ := rfl

/-- Reinterpret `α →* β` as `Additive α →+ Additive β`. -/
@[simps]
/--
Definition of `MonoidHom.toAdditive` / `MonoidHom.toAdditive` 的定义

English:
definition MonoidHom.toAdditive
  signature: [MulOneClass α] [MulOneClass β]
  body: {
    toFun := fun a => ofMul (f a.toMul)
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  invFun f := {
    toFun := fun a => (f (ofMul a)).toMul
    map_mul' := f.map_add
    map_one' := f.map_zero
  }

@[simp, norm_cast]

中文:
定义 幺半群态射.toAdditive
  签名: [MulOne类 α] [MulOne类 β]
  定义体: {
    toFun := fun a => ofMul (f a.toMul)
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  invFun f := {
    toFun := fun a => (f (ofMul a)).toMul
    map_mul' := f.map_add
    map_one' := f.map_zero
  }

@[simp, norm_cast]
-/
def MonoidHom.toAdditive [MulOneClass α] [MulOneClass β] :
    (α ->* β) ≃ (Additive α ->+ Additive β) where
  toFun f := {
    toFun := fun a => ofMul (f a.toMul)
    map_add' := f.map_mul
    map_zero' := f.map_one
  }
  invFun f := {
    toFun := fun a => (f (ofMul a)).toMul
    map_mul' := f.map_add
    map_one' := f.map_zero
  }

@[simp, norm_cast]
/--
lemma `MonoidHom.coe_toAdditive` / 引理 `MonoidHom.coe_toAdditive`

English:
lemma MonoidHom.coe_toAdditive
  given: [MulOneClass α] [MulOneClass β] (f : α ->* β)
  proof: rfl

中文:
引理 幺半群态射.coe_toAdditive
  条件: [MulOne类 α] [MulOne类 β] (f : α ->* β)
  证明: rfl
-/
lemma MonoidHom.coe_toAdditive [MulOneClass α] [MulOneClass β] (f : α ->* β) :
    ⇑(toAdditive f) = ofMul ∘ f ∘ toMul := rfl

/--
lemma `MonoidHom.toAdditive_id` / 引理 `MonoidHom.toAdditive_id`

English:
lemma MonoidHom.toAdditive_id
  given: [MulOneClass α]
  statement: (id α).toAdditive = .id _
  proof: rfl

中文:
引理 幺半群态射.toAdditive_id
  条件: [MulOne类 α]
  结论: (id α).toAdditive = .id _
  证明: rfl

Depends on / 依赖: equivShrink, mulZeroOneClass, symm.mulZeroOneClass
-/
@[simp] lemma MonoidHom.toAdditive_id [MulOneClass α] : (id α).toAdditive = .id _ := rfl

/-- Reinterpret `Additive α →+ β` as `α →* Multiplicative β`. -/
@[simps]
/--
Definition of `AddMonoidHom.toMultiplicativeRight` / `AddMonoidHom.toMultiplicativeRight` 的定义

English:
definition AddMonoidHom.toMultiplicativeRight
  signature: [MulOneClass α] [AddZeroClass β]
  body: {
    toFun := fun a => ofAdd (f (ofMul a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => (f a.toMul).toAdd
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]

中文:
定义 加法幺半群态射.toMultiplicativeRight
  签名: [MulOne类 α] [加法零类 β]
  定义体: {
    toFun := fun a => ofAdd (f (ofMul a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => (f a.toMul).toAdd
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
-/
def AddMonoidHom.toMultiplicativeRight [MulOneClass α] [AddZeroClass β] :
    (Additive α ->+ β) ≃ (α ->* Multiplicative β) where
  toFun f := {
    toFun := fun a => ofAdd (f (ofMul a))
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => (f a.toMul).toAdd
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
/--
lemma `AddMonoidHom.coe_toMultiplicativeRight` / 引理 `AddMonoidHom.coe_toMultiplicativeRight`

English:
lemma AddMonoidHom.coe_toMultiplicativeRight
  statement: [MulOneClass α] [AddZeroClass β]
  proof: rfl

中文:
引理 加法幺半群态射.coe_toMultiplicativeRight
  结论: [MulOne类 α] [加法零类 β]
  证明: rfl
-/
lemma AddMonoidHom.coe_toMultiplicativeRight [MulOneClass α] [AddZeroClass β]
    (f : Additive α ->+ β) : ⇑(toMultiplicativeRight f) = ofAdd ∘ f ∘ ofMul := rfl

/-- Reinterpret `α →* Multiplicative β` as `Additive α →+ β`. -/
@[simps!]
/--
Definition of `MonoidHom.toAdditiveLeft` / `MonoidHom.toAdditiveLeft` 的定义

English:
definition MonoidHom.toAdditiveLeft
  signature: [MulOneClass α] [AddZeroClass β]
  body: AddMonoidHom.toMultiplicativeRight.symm

@[simp, norm_cast]

中文:
定义 幺半群态射.toAdditiveLeft
  签名: [MulOne类 α] [加法零类 β]
  定义体: AddMonoidHom.toMultiplicativeRight.symm

@[simp, norm_cast]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toMultiplicativeRight.symm, toMultiplicativeRight
-/
def MonoidHom.toAdditiveLeft [MulOneClass α] [AddZeroClass β] :
    (α ->* Multiplicative β) ≃ (Additive α ->+ β) :=
  AddMonoidHom.toMultiplicativeRight.symm

@[simp, norm_cast]
/--
lemma `MonoidHom.coe_toAdditiveLeft` / 引理 `MonoidHom.coe_toAdditiveLeft`

English:
lemma MonoidHom.coe_toAdditiveLeft
  given: [MulOneClass α] [AddZeroClass β] (f : α ->* Multiplicative β)
  proof: rfl

中文:
引理 幺半群态射.coe_toAdditiveLeft
  条件: [MulOne类 α] [加法零类 β] (f : α ->* Multiplicative β)
  证明: rfl
-/
lemma MonoidHom.coe_toAdditiveLeft [MulOneClass α] [AddZeroClass β] (f : α ->* Multiplicative β) :
    ⇑(toAdditiveLeft f) = toAdd ∘ f ∘ toMul := rfl

/-- Reinterpret `α →+ Additive β` as `Multiplicative α →* β`. -/
@[simps]
/--
Definition of `AddMonoidHom.toMultiplicativeLeft` / `AddMonoidHom.toMultiplicativeLeft` 的定义

English:
definition AddMonoidHom.toMultiplicativeLeft
  signature: [AddZeroClass α] [MulOneClass β]
  body: {
    toFun := fun a => (f a.toAdd).toMul
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => ofMul (f (ofAdd a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]

中文:
定义 加法幺半群态射.toMultiplicativeLeft
  签名: [加法零类 α] [MulOne类 β]
  定义体: {
    toFun := fun a => (f a.toAdd).toMul
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => ofMul (f (ofAdd a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
-/
def AddMonoidHom.toMultiplicativeLeft [AddZeroClass α] [MulOneClass β] :
    (α ->+ Additive β) ≃ (Multiplicative α ->* β) where
  toFun f := {
    toFun := fun a => (f a.toAdd).toMul
    map_mul' := f.map_add
    map_one' := f.map_zero
  }
  invFun f := {
    toFun := fun a => ofMul (f (ofAdd a))
    map_add' := f.map_mul
    map_zero' := f.map_one
  }

@[simp, norm_cast]
/--
lemma `AddMonoidHom.coe_toMultiplicativeLeft` / 引理 `AddMonoidHom.coe_toMultiplicativeLeft`

English:
lemma AddMonoidHom.coe_toMultiplicativeLeft
  given: [AddZeroClass α] [MulOneClass β] (f : α ->+ Additive β)
  proof: rfl

中文:
引理 加法幺半群态射.coe_toMultiplicativeLeft
  条件: [加法零类 α] [MulOne类 β] (f : α ->+ 加性 β)
  证明: rfl
-/
lemma AddMonoidHom.coe_toMultiplicativeLeft [AddZeroClass α] [MulOneClass β] (f : α ->+ Additive β) :
    ⇑(toMultiplicativeLeft f) = toMul ∘ f ∘ toAdd := rfl

/-- Reinterpret `Multiplicative α →* β` as `α →+ Additive β`. -/
@[simps!]
/--
Definition of `MonoidHom.toAdditiveRight` / `MonoidHom.toAdditiveRight` 的定义

English:
definition MonoidHom.toAdditiveRight
  signature: [AddZeroClass α] [MulOneClass β]
  body: AddMonoidHom.toMultiplicativeLeft.symm

@[simp, norm_cast]

中文:
定义 幺半群态射.toAdditiveRight
  签名: [加法零类 α] [MulOne类 β]
  定义体: AddMonoidHom.toMultiplicativeLeft.symm

@[simp, norm_cast]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toMultiplicativeLeft.symm, toMultiplicativeLeft
-/
def MonoidHom.toAdditiveRight [AddZeroClass α] [MulOneClass β] :
    (Multiplicative α ->* β) ≃ (α ->+ Additive β) :=
  AddMonoidHom.toMultiplicativeLeft.symm

@[simp, norm_cast]
/--
lemma `MonoidHom.coe_toAdditiveRight` / 引理 `MonoidHom.coe_toAdditiveRight`

English:
lemma MonoidHom.coe_toAdditiveRight
  given: [AddZeroClass α] [MulOneClass β] (f : Multiplicative α ->* β)
  proof: rfl

中文:
引理 幺半群态射.coe_toAdditiveRight
  条件: [加法零类 α] [MulOne类 β] (f : Multiplicative α ->* β)
  证明: rfl
-/
lemma MonoidHom.coe_toAdditiveRight [AddZeroClass α] [MulOneClass β] (f : Multiplicative α ->* β) :
    ⇑(toAdditiveRight f) = ofMul ∘ f ∘ ofAdd := rfl

/-- This ext lemma moves the type tag to the codomain, since most ext lemmas act on the domain.

WARNING: This has the potential to send `ext` into a loop if someone locally adds the inverse ext
lemma proving equality in `α →+ Additive β` from equality in `Multiplicative α →* β`. -/
@[ext]
/--
lemma `Multiplicative.monoidHom_ext` / 引理 `Multiplicative.monoidHom_ext`

English:
lemma Multiplicative.monoidHom_ext
  statement: [AddZeroClass α] [MulOneClass β]
  proof: MonoidHom.toAdditiveRight.injective h

中文:
引理 Multiplicative.monoidHom_ext
  结论: [加法零类 α] [MulOne类 β]
  证明: MonoidHom.toAdditiveRight.injective h

Depends on / 依赖: MonoidHom, MonoidHom.toAdditiveRight.injective, injective, toAdditiveRight
-/
lemma Multiplicative.monoidHom_ext [AddZeroClass α] [MulOneClass β]
    (f g : Multiplicative α ->* β) (h : f.toAdditiveRight = g.toAdditiveRight) : f = g :=
  MonoidHom.toAdditiveRight.injective h

/-- This ext lemma moves the type tag to the codomain, since most ext lemmas act on the domain.

WARNING: This has the potential to send `ext` into a loop if someone locally adds the inverse ext
lemma proving equality in `α →* Multiplicative β` from equality in `Additive α →+ β`. -/
@[ext]
/--
lemma `Additive.addMonoidHom_ext` / 引理 `Additive.addMonoidHom_ext`

English:
lemma Additive.addMonoidHom_ext
  statement: [MulOneClass α] [AddZeroClass β]
  proof: AddMonoidHom.toMultiplicativeRight.injective h

中文:
引理 加性.addMonoidHom_ext
  结论: [MulOne类 α] [加法零类 β]
  证明: AddMonoidHom.toMultiplicativeRight.injective h

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toMultiplicativeRight.injective, injective, toMultiplicativeRight
-/
lemma Additive.addMonoidHom_ext [MulOneClass α] [AddZeroClass β]
    (f g : Additive α ->+ β) (h : f.toMultiplicativeRight = g.toMultiplicativeRight) : f = g :=
  AddMonoidHom.toMultiplicativeRight.injective h

section AddCommMonoid
variable [AddMonoid M] [AddCommMonoid N]

@[simp]
/--
lemma `AddMonoidHom.toMultiplicative_add` / 引理 `AddMonoidHom.toMultiplicative_add`

English:
lemma AddMonoidHom.toMultiplicative_add
  given: (f g : M ->+ N)
  proof: rfl

中文:
引理 加法幺半群态射.toMultiplicative_add
  条件: (f g : M ->+ N)
  证明: rfl
-/
lemma AddMonoidHom.toMultiplicative_add (f g : M ->+ N) :
    (f + g).toMultiplicative = f.toMultiplicative * g.toMultiplicative := rfl

end AddCommMonoid

/--
Definition of `AddMonoidHom.toMultiplicativeLeftAddEquiv` / `AddMonoidHom.toMultiplicativeLeftAddEquiv` 的定义

English:
definition AddMonoidHom.toMultiplicativeLeftAddEquiv
  signature: [AddMonoid M] [CommMonoid N]
  body: AddMonoidHom.toMultiplicativeLeft.trans Additive.ofMul
  map_add' _ _ := rfl

中文:
定义 加法幺半群态射.toMultiplicativeLeftAddEquiv
  签名: [加法幺半群 M] [交换幺半群 N]
  定义体: AddMonoidHom.toMultiplicativeLeft.trans Additive.ofMul
  map_add' _ _ := rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toMultiplicativeLeft.trans, Additive, Additive.ofMul, toMultiplicativeLeft
-/
def AddMonoidHom.toMultiplicativeLeftAddEquiv [AddMonoid M] [CommMonoid N] :
    (M ->+ Additive N) ≃+ Additive (Multiplicative M ->* N) where
  toEquiv := AddMonoidHom.toMultiplicativeLeft.trans Additive.ofMul
  map_add' _ _ := rfl

/--
Definition of `AddMonoidHom.toMultiplicativeRightAddEquiv` / `AddMonoidHom.toMultiplicativeRightAddEquiv` 的定义

English:
definition AddMonoidHom.toMultiplicativeRightAddEquiv
  signature: [Monoid M] [AddCommMonoid N]
  body: AddMonoidHom.toMultiplicativeRight.trans Additive.ofMul
  map_add' _ _ := rfl

中文:
定义 加法幺半群态射.toMultiplicativeRightAddEquiv
  签名: [幺半群 M] [加法交换幺半群 N]
  定义体: AddMonoidHom.toMultiplicativeRight.trans Additive.ofMul
  map_add' _ _ := rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toMultiplicativeRight.trans, Additive, Additive.ofMul, toMultiplicativeRight
-/
def AddMonoidHom.toMultiplicativeRightAddEquiv [Monoid M] [AddCommMonoid N] :
    (Additive M ->+ N) ≃+ Additive (M ->* Multiplicative N) where
  toEquiv := AddMonoidHom.toMultiplicativeRight.trans Additive.ofMul
  map_add' _ _ := rfl

/--
Definition of `MonoidHom.toAdditiveLeftMulEquiv` / `MonoidHom.toAdditiveLeftMulEquiv` 的定义

English:
definition MonoidHom.toAdditiveLeftMulEquiv
  signature: [Monoid M] [AddCommMonoid N]
  body: MonoidHom.toAdditiveLeft.trans Multiplicative.ofAdd
  map_mul' _ _ := rfl

中文:
定义 幺半群态射.toAdditiveLeftMulEquiv
  签名: [幺半群 M] [加法交换幺半群 N]
  定义体: MonoidHom.toAdditiveLeft.trans Multiplicative.ofAdd
  map_mul' _ _ := rfl

Depends on / 依赖: MonoidHom, MonoidHom.toAdditiveLeft.trans, Multiplicative, Multiplicative.ofAdd, toAdditiveLeft
-/
def MonoidHom.toAdditiveLeftMulEquiv [Monoid M] [AddCommMonoid N] :
    (M ->* Multiplicative N) ≃* Multiplicative (Additive M ->+ N) where
  toEquiv := MonoidHom.toAdditiveLeft.trans Multiplicative.ofAdd
  map_mul' _ _ := rfl

/--
Definition of `MonoidHom.toAdditiveRightMulEquiv` / `MonoidHom.toAdditiveRightMulEquiv` 的定义

English:
definition MonoidHom.toAdditiveRightMulEquiv
  signature: [AddMonoid M] [CommMonoid N]
  body: MonoidHom.toAdditiveRight.trans Multiplicative.ofAdd
  map_mul' _ _ := rfl

中文:
定义 幺半群态射.toAdditiveRightMulEquiv
  签名: [加法幺半群 M] [交换幺半群 N]
  定义体: MonoidHom.toAdditiveRight.trans Multiplicative.ofAdd
  map_mul' _ _ := rfl

Depends on / 依赖: MonoidHom, MonoidHom.toAdditiveRight.trans, Multiplicative, Multiplicative.ofAdd, toAdditiveRight
-/
def MonoidHom.toAdditiveRightMulEquiv [AddMonoid M] [CommMonoid N] :
    (Multiplicative M ->* N) ≃* Multiplicative (M ->+ Additive N) where
  toEquiv := MonoidHom.toAdditiveRight.trans Multiplicative.ofAdd
  map_mul' _ _ := rfl
