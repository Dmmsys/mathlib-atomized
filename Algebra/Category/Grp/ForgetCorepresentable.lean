/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.Grp.Preadditive

/-!
# The forget functor is corepresentable

It is shown that the forget functor `AddCommGrpCat.{u} ⥤ Type u` is corepresentable
by `ULift ℤ`. Similar results are obtained for the variants `CommGrpCat`, `AddGrpCat`
and `GrpCat`.

-/

@[expose] public section

universe u

open CategoryTheory Opposite

/-!
### `(ULift ℤ →+ G) ≃ G`

These universe-monomorphic variants of `zmultiplesHom`/`zpowersHom` are put here since they
shouldn't be useful outside of category theory.
-/

/-- The equivalence `(ULift ℤ →+ G) ≃ G` for any additive group `G`. -/
@[simps!]
/--
Definition of `uliftZMultiplesHom` / `uliftZMultiplesHom` 的定义

English:
definition uliftZMultiplesHom
  signature: (G : Type u) [AddGroup G]
  body: (zmultiplesHom _).trans AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv

中文:
定义 uliftZMultiplesHom
  签名: (G : 类型u) [加法群 G]
  定义体: (zmultiplesHom _).trans AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv

Depends on / 依赖: AddEquiv, AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv, addMonoidHomCongrLeftEquiv, zmultiplesHom
-/
def uliftZMultiplesHom (G : Type u) [AddGroup G] : G ≃ (ULift.{u} Int ->+ G) :=
  (zmultiplesHom _).trans AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv

/-- The equivalence `(ULift (Multiplicative ℤ) →* G) ≃ G` for any group `G`. -/
@[simps!]
/--
Definition of `uliftZPowersHom` / `uliftZPowersHom` 的定义

English:
definition uliftZPowersHom
  signature: (G : Type u) [Group G]
  body: (zpowersHom _).trans MulEquiv.ulift.symm.monoidHomCongrLeftEquiv

中文:
定义 uliftZPowersHom
  签名: (G : 类型u) [群 G]
  定义体: (zpowersHom _).trans MulEquiv.ulift.symm.monoidHomCongrLeftEquiv

Depends on / 依赖: MulEquiv, MulEquiv.ulift.symm.monoidHomCongrLeftEquiv, monoidHomCongrLeftEquiv, zpowersHom
-/
def uliftZPowersHom (G : Type u) [Group G] : G ≃ (ULift.{u} (Multiplicative Int) ->* G) :=
  (zpowersHom _).trans MulEquiv.ulift.symm.monoidHomCongrLeftEquiv

/--
Definition of `GrpCat.coyonedaObjIsoForget` / `GrpCat.coyonedaObjIsoForget` 的定义

English:
definition GrpCat.coyonedaObjIsoForget
  signature: :
  body: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

中文:
定义 群范畴.coyonedaObjIsoForget
  签名: :
  定义体: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv.trans, M.carrier, NatIso, NatIso.ofComponents, carrier, homEquiv, ofComponents, uliftZPowersHom
-/
def GrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative Int)))) ≅ forget GrpCat.{u} :=
  NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

/--
Definition of `CommGrpCat.coyonedaObjIsoForget` / `CommGrpCat.coyonedaObjIsoForget` 的定义

English:
definition CommGrpCat.coyonedaObjIsoForget
  signature: :
  body: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

中文:
定义 交换群范畴.coyonedaObjIsoForget
  签名: :
  定义体: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv.trans, M.carrier, NatIso, NatIso.ofComponents, carrier, homEquiv, ofComponents, uliftZPowersHom
-/
def CommGrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative Int)))) ≅ forget CommGrpCat.{u} :=
  NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

/--
Definition of `AddGrpCat.coyonedaObjIsoForget` / `AddGrpCat.coyonedaObjIsoForget` 的定义

English:
definition AddGrpCat.coyonedaObjIsoForget
  signature: :
  body: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso

中文:
定义 加法群范畴.coyonedaObjIsoForget
  签名: :
  定义体: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv.trans, M.carrier, NatIso, NatIso.ofComponents, carrier, homEquiv, ofComponents, uliftZMultiplesHom
-/
def AddGrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} Int))) ≅ forget AddGrpCat.{u} :=
  NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso

/--
Definition of `AddCommGrpCat.coyonedaObjIsoForget` / `AddCommGrpCat.coyonedaObjIsoForget` 的定义

English:
definition AddCommGrpCat.coyonedaObjIsoForget
  signature: :
  body: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso

中文:
定义 加法交换群范畴.coyonedaObjIsoForget
  签名: :
  定义体: NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv.trans, M.carrier, NatIso, NatIso.ofComponents, carrier, homEquiv, ofComponents, uliftZMultiplesHom
-/
def AddCommGrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} Int))) ≅ forget AddCommGrpCat.{u} :=
  NatIso.ofComponents fun M =>
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso

/--
Instance `GrpCat.forget_isCorepresentable` / 实例 `GrpCat.forget_isCorepresentable`

English:
instance GrpCat.forget_isCorepresentable
  signature: :
  body: Functor.IsCorepresentable.mk' GrpCat.coyonedaObjIsoForget

中文:
实例 群范畴.forget_isCorepresentable
  签名: :
  定义体: Functor.IsCorepresentable.mk' GrpCat.coyonedaObjIsoForget

Depends on / 依赖: Functor, Functor.IsCorepresentable.mk, GrpCat, GrpCat.coyonedaObjIsoForget, IsCorepresentable, coyonedaObjIsoForget
-/
instance GrpCat.forget_isCorepresentable :
    (forget GrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' GrpCat.coyonedaObjIsoForget

/--
Instance `CommGrpCat.forget_isCorepresentable` / 实例 `CommGrpCat.forget_isCorepresentable`

English:
instance CommGrpCat.forget_isCorepresentable
  signature: :
  body: Functor.IsCorepresentable.mk' CommGrpCat.coyonedaObjIsoForget

中文:
实例 交换群范畴.forget_isCorepresentable
  签名: :
  定义体: Functor.IsCorepresentable.mk' CommGrpCat.coyonedaObjIsoForget

Depends on / 依赖: CommGrpCat, CommGrpCat.coyonedaObjIsoForget, Functor, Functor.IsCorepresentable.mk, IsCorepresentable, coyonedaObjIsoForget
-/
instance CommGrpCat.forget_isCorepresentable :
    (forget CommGrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' CommGrpCat.coyonedaObjIsoForget

/--
Instance `AddGrpCat.forget_isCorepresentable` / 实例 `AddGrpCat.forget_isCorepresentable`

English:
instance AddGrpCat.forget_isCorepresentable
  signature: :
  body: Functor.IsCorepresentable.mk' AddGrpCat.coyonedaObjIsoForget

中文:
实例 加法群范畴.forget_isCorepresentable
  签名: :
  定义体: Functor.IsCorepresentable.mk' AddGrpCat.coyonedaObjIsoForget

Depends on / 依赖: AddGrpCat, AddGrpCat.coyonedaObjIsoForget, Functor, Functor.IsCorepresentable.mk, IsCorepresentable, coyonedaObjIsoForget
-/
instance AddGrpCat.forget_isCorepresentable :
    (forget AddGrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddGrpCat.coyonedaObjIsoForget

/--
Instance `AddCommGrpCat.forget_isCorepresentable` / 实例 `AddCommGrpCat.forget_isCorepresentable`

English:
instance AddCommGrpCat.forget_isCorepresentable
  signature: :
  body: Functor.IsCorepresentable.mk' AddCommGrpCat.coyonedaObjIsoForget

中文:
实例 加法交换群范畴.forget_isCorepresentable
  签名: :
  定义体: Functor.IsCorepresentable.mk' AddCommGrpCat.coyonedaObjIsoForget

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.coyonedaObjIsoForget, Functor, Functor.IsCorepresentable.mk, IsCorepresentable, coyonedaObjIsoForget
-/
instance AddCommGrpCat.forget_isCorepresentable :
    (forget AddCommGrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddCommGrpCat.coyonedaObjIsoForget

/--
theorem `uliftZMultiplesHom_apply_add` / 定理 `uliftZMultiplesHom_apply_add`

English:
theorem uliftZMultiplesHom_apply_add
  given: (G : Type u) [AddCommGroup G] (x y : G)
  proof: by
  ext
  simp_all only [uliftZMultiplesHom_apply_apply, smul_add, AddMonoidHom.add_apply]

中文:
定理 uliftZMultiplesHom_apply_add
  条件: (G : 类型u) [加法交换群 G] (x y : G)
  证明: by
  ext
  simp_all only [uliftZMultiplesHom_apply_apply, smul_add, AddMonoidHom.add_apply]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.add_apply, add_apply, smul_add, uliftZMultiplesHom_apply_apply
-/
theorem uliftZMultiplesHom_apply_add (G : Type u) [AddCommGroup G] (x y : G) :
    uliftZMultiplesHom G (x + y) = uliftZMultiplesHom G x + uliftZMultiplesHom G y := by
  ext
  simp_all only [uliftZMultiplesHom_apply_apply, smul_add, AddMonoidHom.add_apply]

/-- The additive equivalence `(ℤ ⟶ G) ≃+ G` -/
@[simps!]
/--
Definition of `AddCommGrpCat.uliftZMultiplesAddEquiv` / `AddCommGrpCat.uliftZMultiplesAddEquiv` 的定义

English:
definition AddCommGrpCat.uliftZMultiplesAddEquiv
  signature: (G : AddCommGrpCat)
  body: AddCommGrpCat.homAddEquiv.trans
    (AddEquiv.mk' (uliftZMultiplesHom G) (uliftZMultiplesHom_apply_add G)).symm

中文:
定义 加法交换群范畴.uliftZMultiplesAddEquiv
  签名: (G : 加法交换群范畴)
  定义体: AddCommGrpCat.homAddEquiv.trans
    (AddEquiv.mk' (uliftZMultiplesHom G) (uliftZMultiplesHom_apply_add G)).symm

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.homAddEquiv.trans, AddEquiv, AddEquiv.mk, homAddEquiv, uliftZMultiplesHom, uliftZMultiplesHom_apply_add
-/
def AddCommGrpCat.uliftZMultiplesAddEquiv (G : AddCommGrpCat) : (of (ULift Int) ⟶ G) ≃+ G :=
  AddCommGrpCat.homAddEquiv.trans
    (AddEquiv.mk' (uliftZMultiplesHom G) (uliftZMultiplesHom_apply_add G)).symm
