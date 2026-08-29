/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Equivalence between `Group` and `AddGroup`

This file contains two equivalences:
* `groupAddGroupEquivalence` : the equivalence between `GrpCat` and `AddGrpCat` by sending
  `X : GrpCat` to `Additive X` and `Y : AddGrpCat` to `Multiplicative Y`.
* `commGroupAddCommGroupEquivalence` : the equivalence between `CommGrpCat` and `AddCommGrpCat`
  by sending `X : CommGrpCat` to `Additive X` and `Y : AddCommGrpCat` to `Multiplicative Y`.
-/

@[expose] public section


open CategoryTheory

namespace GrpCat

/-- The functor `GrpCat ⥤ AddGrpCat` by sending `X ↦ Additive X` and `f ↦ f`.
-/
@[simps]
/--
Definition of `toAddGrp` / `toAddGrp` 的定义

English:
definition toAddGrp
  signature: : GrpCat ⥤ AddGrpCat where
  body: AddGrpCat.of (Additive X)
  map {_} {_} f := AddGrpCat.ofHom f.hom.toAdditive

中文:
定义 toAddGrp
  签名: : 群范畴 ⥤ 加法群范畴 where
  定义体: AddGrpCat.of (Additive X)
  map {_} {_} f := AddGrpCat.ofHom f.hom.toAdditive

Depends on / 依赖: AddGrpCat, AddGrpCat.of, Additive
-/
def toAddGrp : GrpCat ⥤ AddGrpCat where
  obj X := AddGrpCat.of (Additive X)
  map {_} {_} f := AddGrpCat.ofHom f.hom.toAdditive

end GrpCat

namespace CommGrpCat

/-- The functor `CommGrpCat ⥤ AddCommGrpCat` by sending `X ↦ Additive X` and `f ↦ f`.
-/
@[simps]
/--
Definition of `toAddCommGrp` / `toAddCommGrp` 的定义

English:
definition toAddCommGrp
  signature: : CommGrpCat ⥤ AddCommGrpCat where
  body: AddCommGrpCat.of (Additive X)
  map {_} {_} f := AddCommGrpCat.ofHom f.hom.toAdditive

中文:
定义 toAddCommGrp
  签名: : 交换群范畴 ⥤ 加法交换群范畴 where
  定义体: AddCommGrpCat.of (Additive X)
  map {_} {_} f := AddCommGrpCat.ofHom f.hom.toAdditive

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of, Additive
-/
def toAddCommGrp : CommGrpCat ⥤ AddCommGrpCat where
  obj X := AddCommGrpCat.of (Additive X)
  map {_} {_} f := AddCommGrpCat.ofHom f.hom.toAdditive

end CommGrpCat

namespace AddGrpCat

/-- The functor `AddGrpCat ⥤ GrpCat` by sending `X ↦ Multiplicative X` and `f ↦ f`.
-/
@[simps]
/--
Definition of `toGrp` / `toGrp` 的定义

English:
definition toGrp
  signature: : AddGrpCat ⥤ GrpCat where
  body: GrpCat.of (Multiplicative X)
  map {_} {_} f := GrpCat.ofHom f.hom.toMultiplicative

中文:
定义 toGrp
  签名: : 加法群范畴 ⥤ 群范畴 where
  定义体: GrpCat.of (Multiplicative X)
  map {_} {_} f := GrpCat.ofHom f.hom.toMultiplicative

Depends on / 依赖: GrpCat, GrpCat.of, Multiplicative
-/
def toGrp : AddGrpCat ⥤ GrpCat where
  obj X := GrpCat.of (Multiplicative X)
  map {_} {_} f := GrpCat.ofHom f.hom.toMultiplicative

end AddGrpCat

namespace AddCommGrpCat

/-- The functor `AddCommGrpCat ⥤ CommGrpCat` by sending `X ↦ Multiplicative X` and `f ↦ f`.
-/
@[simps]
/--
Definition of `toCommGrp` / `toCommGrp` 的定义

English:
definition toCommGrp
  signature: : AddCommGrpCat ⥤ CommGrpCat where
  body: CommGrpCat.of (Multiplicative X)
  map {_} {_} f := CommGrpCat.ofHom f.hom.toMultiplicative

中文:
定义 toCommGrp
  签名: : 加法交换群范畴 ⥤ 交换群范畴 where
  定义体: CommGrpCat.of (Multiplicative X)
  map {_} {_} f := CommGrpCat.ofHom f.hom.toMultiplicative

Depends on / 依赖: CommGrpCat, CommGrpCat.of, Multiplicative
-/
def toCommGrp : AddCommGrpCat ⥤ CommGrpCat where
  obj X := CommGrpCat.of (Multiplicative X)
  map {_} {_} f := CommGrpCat.ofHom f.hom.toMultiplicative

end AddCommGrpCat

/-- The equivalence of categories between `GrpCat` and `AddGrpCat`
-/
@[simps]
/--
Definition of `groupAddGroupEquivalence` / `groupAddGroupEquivalence` 的定义

English:
definition groupAddGroupEquivalence
  signature: : GrpCat ≌ AddGrpCat where
  body: GrpCat.toAddGrp
  inverse := AddGrpCat.toGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 groupAddGroupEquivalence
  签名: : 群范畴 ≌ 加法群范畴 where
  定义体: GrpCat.toAddGrp
  inverse := AddGrpCat.toGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: GrpCat, GrpCat.toAddGrp, toAddGrp
-/
def groupAddGroupEquivalence : GrpCat ≌ AddGrpCat where
  functor := GrpCat.toAddGrp
  inverse := AddGrpCat.toGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The equivalence of categories between `CommGrpCat` and `AddCommGrpCat`.
-/
@[simps]
/--
Definition of `commGroupAddCommGroupEquivalence` / `commGroupAddCommGroupEquivalence` 的定义

English:
definition commGroupAddCommGroupEquivalence
  signature: : CommGrpCat ≌ AddCommGrpCat where
  body: CommGrpCat.toAddCommGrp
  inverse := AddCommGrpCat.toCommGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 commGroupAddCommGroupEquivalence
  签名: : 交换群范畴 ≌ 加法交换群范畴 where
  定义体: CommGrpCat.toAddCommGrp
  inverse := AddCommGrpCat.toCommGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: CommGrpCat, CommGrpCat.toAddCommGrp, toAddCommGrp
-/
def commGroupAddCommGroupEquivalence : CommGrpCat ≌ AddCommGrpCat where
  functor := CommGrpCat.toAddCommGrp
  inverse := AddCommGrpCat.toCommGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _
