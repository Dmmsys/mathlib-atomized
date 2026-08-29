/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.CategoryTheory.Yoneda

/-!
# The forgetful functor is corepresentable

The forgetful functor `AddCommMonCat.{u} ⥤ Type u` is corepresentable
by `ULift ℕ`. Similar results are obtained for the variants `CommMonCat`, `AddMonCat`
and `MonCat`.

-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u

open CategoryTheory Opposite

/-!
### `(ULift ℕ →+ G) ≃ G`

These universe-monomorphic variants of `multiplesHom`/`powersHom` are put here since they
shouldn't be useful outside of category theory.
-/

/-- Monoid homomorphisms from `ULift ℕ` are defined by the image of `1`. -/
@[simps!]
/--
Definition of `uliftMultiplesHom` / `uliftMultiplesHom` 的定义

English:
definition uliftMultiplesHom
  signature: (M : Type u) [AddMonoid M]
  body: (multiplesHom _).trans AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv

中文:
定义 uliftMultiplesHom
  签名: (M : 类型u) [AddMonoid M]
  定义体: (multiplesHom _).trans AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv

Depends on / 依赖: AddEquiv, AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv, addMonoidHomCongrLeftEquiv, multiplesHom
-/
def uliftMultiplesHom (M : Type u) [AddMonoid M] : M ≃ (ULift.{u} Nat ->+ M) :=
  (multiplesHom _).trans AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv

/-- Monoid homomorphisms from `ULift (Multiplicative ℕ)` are defined by the image
of `Multiplicative.ofAdd 1`. -/
@[simps!]
/--
Definition of `uliftPowersHom` / `uliftPowersHom` 的定义

English:
definition uliftPowersHom
  signature: (M : Type u) [Monoid M]
  body: (powersHom _).trans MulEquiv.ulift.symm.monoidHomCongrLeftEquiv

中文:
定义 uliftPowersHom
  签名: (M : 类型u) [Monoid M]
  定义体: (powersHom _).trans MulEquiv.ulift.symm.monoidHomCongrLeftEquiv

Depends on / 依赖: MulEquiv, MulEquiv.ulift.symm.monoidHomCongrLeftEquiv, monoidHomCongrLeftEquiv, powersHom
-/
def uliftPowersHom (M : Type u) [Monoid M] : M ≃ (ULift.{u} (Multiplicative Nat) ->* M) :=
  (powersHom _).trans MulEquiv.ulift.symm.monoidHomCongrLeftEquiv

/--
Definition of `MonCat.coyonedaObjIsoForget` / `MonCat.coyonedaObjIsoForget` 的定义

English:
definition MonCat.coyonedaObjIsoForget
  signature: :
  body: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftPowersHom M.carrier).symm).toIso

中文:
定义 MonCat.coyonedaObjIsoForget
  签名: :
  定义体: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftPowersHom M.carrier).symm).toIso

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv.trans, M.carrier, NatIso, NatIso.ofComponents, carrier, homEquiv, ofComponents, uliftPowersHom
-/
def MonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative Nat)))) ≅ forget MonCat.{u} :=
  NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftPowersHom M.carrier).symm).toIso


/--
Definition of `CommMonCat.coyonedaObjIsoForget` / `CommMonCat.coyonedaObjIsoForget` 的定义

English:
definition CommMonCat.coyonedaObjIsoForget
  signature: :
  body: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftPowersHom M.carrier).symm).toIso

中文:
定义 CommMonCat.coyonedaObjIsoForget
  签名: :
  定义体: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftPowersHom M.carrier).symm).toIso

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv.trans, M.carrier, NatIso, NatIso.ofComponents, carrier, homEquiv, ofComponents, uliftPowersHom
-/
def CommMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative Nat)))) ≅ forget CommMonCat.{u} :=
  NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftPowersHom M.carrier).symm).toIso

/--
Definition of `AddMonCat.coyonedaObjIsoForget` / `AddMonCat.coyonedaObjIsoForget` 的定义

English:
definition AddMonCat.coyonedaObjIsoForget
  signature: :
  body: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftMultiplesHom M.carrier).symm).toIso

中文:
定义 AddMonCat.coyonedaObjIsoForget
  签名: :
  定义体: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftMultiplesHom M.carrier).symm).toIso

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv.trans, M.carrier, NatIso, NatIso.ofComponents, carrier, homEquiv, ofComponents, uliftMultiplesHom
-/
def AddMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} Nat))) ≅ forget AddMonCat.{u} :=
  NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftMultiplesHom M.carrier).symm).toIso

/--
Definition of `AddCommMonCat.coyonedaObjIsoForget` / `AddCommMonCat.coyonedaObjIsoForget` 的定义

English:
definition AddCommMonCat.coyonedaObjIsoForget
  signature: :
  body: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftMultiplesHom M.carrier).symm).toIso

中文:
定义 AddCommMonCat.coyonedaObjIsoForget
  签名: :
  定义体: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftMultiplesHom M.carrier).symm).toIso

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv.trans, M.carrier, NatIso, NatIso.ofComponents, carrier, homEquiv, ofComponents, uliftMultiplesHom
-/
def AddCommMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} Nat))) ≅ forget AddCommMonCat.{u} :=
  NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftMultiplesHom M.carrier).symm).toIso

/--
Instance `MonCat.forget_isCorepresentable` / 实例 `MonCat.forget_isCorepresentable`

English:
instance MonCat.forget_isCorepresentable
  signature: :
  body: Functor.IsCorepresentable.mk' MonCat.coyonedaObjIsoForget

中文:
实例 MonCat.forget_isCorepresentable
  签名: :
  定义体: Functor.IsCorepresentable.mk' MonCat.coyonedaObjIsoForget

Depends on / 依赖: Functor, Functor.IsCorepresentable.mk, IsCorepresentable, MonCat, MonCat.coyonedaObjIsoForget, coyonedaObjIsoForget
-/
instance MonCat.forget_isCorepresentable :
    (forget MonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' MonCat.coyonedaObjIsoForget

/--
Instance `CommMonCat.forget_isCorepresentable` / 实例 `CommMonCat.forget_isCorepresentable`

English:
instance CommMonCat.forget_isCorepresentable
  signature: :
  body: Functor.IsCorepresentable.mk' CommMonCat.coyonedaObjIsoForget

中文:
实例 CommMonCat.forget_isCorepresentable
  签名: :
  定义体: Functor.IsCorepresentable.mk' CommMonCat.coyonedaObjIsoForget

Depends on / 依赖: CommMonCat, CommMonCat.coyonedaObjIsoForget, Functor, Functor.IsCorepresentable.mk, IsCorepresentable, coyonedaObjIsoForget
-/
instance CommMonCat.forget_isCorepresentable :
    (forget CommMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' CommMonCat.coyonedaObjIsoForget

/--
Instance `AddMonCat.forget_isCorepresentable` / 实例 `AddMonCat.forget_isCorepresentable`

English:
instance AddMonCat.forget_isCorepresentable
  signature: :
  body: Functor.IsCorepresentable.mk' AddMonCat.coyonedaObjIsoForget

中文:
实例 AddMonCat.forget_isCorepresentable
  签名: :
  定义体: Functor.IsCorepresentable.mk' AddMonCat.coyonedaObjIsoForget

Depends on / 依赖: AddMonCat, AddMonCat.coyonedaObjIsoForget, Functor, Functor.IsCorepresentable.mk, IsCorepresentable, coyonedaObjIsoForget
-/
instance AddMonCat.forget_isCorepresentable :
    (forget AddMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddMonCat.coyonedaObjIsoForget

/--
Instance `AddCommMonCat.forget_isCorepresentable` / 实例 `AddCommMonCat.forget_isCorepresentable`

English:
instance AddCommMonCat.forget_isCorepresentable
  signature: :
  body: Functor.IsCorepresentable.mk' AddCommMonCat.coyonedaObjIsoForget

中文:
实例 AddCommMonCat.forget_isCorepresentable
  签名: :
  定义体: Functor.IsCorepresentable.mk' AddCommMonCat.coyonedaObjIsoForget

Depends on / 依赖: AddCommMonCat, AddCommMonCat.coyonedaObjIsoForget, Functor, Functor.IsCorepresentable.mk, HasLimit, IsCorepresentable, ModuleCat, ModuleCat.restrictScalars, R.map, coyonedaObjIsoForget, evaluation, infer_instance, restrictScalars
-/
instance AddCommMonCat.forget_isCorepresentable :
    (forget AddCommMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddCommMonCat.coyonedaObjIsoForget
