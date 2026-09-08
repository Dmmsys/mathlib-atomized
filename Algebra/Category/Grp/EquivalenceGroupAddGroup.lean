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
/-
**GrpCat.toAddGrp** 是 Mathlib 中的一个定义，位于命名空间 `GrpCat`。
形式化陈述：toAddGrp : GrpCat ⥤ AddGrpCat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `GrpCat ⥤ AddGrpCat` by sending `X ↦ Additive X` and `f ↦ f`.
-/
def toAddGrp : GrpCat ⥤ AddGrpCat where
  obj X := AddGrpCat.of (Additive X)
  map {_} {_} f := AddGrpCat.ofHom f.hom.toAdditive

end GrpCat

namespace CommGrpCat

/-- The functor `CommGrpCat ⥤ AddCommGrpCat` by sending `X ↦ Additive X` and `f ↦ f`.
-/
@[simps]
/-
**CommGrpCat.toAddCommGrp** 是 Mathlib 中的一个定义，位于命名空间 `CommGrpCat`。
形式化陈述：toAddCommGrp : CommGrpCat ⥤ AddCommGrpCat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `CommGrpCat ⥤ AddCommGrpCat` by sending `X ↦ Additive X` and `f ↦ f`
.
-/
def toAddCommGrp : CommGrpCat ⥤ AddCommGrpCat where
  obj X := AddCommGrpCat.of (Additive X)
  map {_} {_} f := AddCommGrpCat.ofHom f.hom.toAdditive

end CommGrpCat

namespace AddGrpCat

/-- The functor `AddGrpCat ⥤ GrpCat` by sending `X ↦ Multiplicative X` and `f ↦ f`.
-/
@[simps]
/-
**AddGrpCat.toGrp** 是 Mathlib 中的一个定义，位于命名空间 `AddGrpCat`。
形式化陈述：toGrp : AddGrpCat ⥤ GrpCat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `AddGrpCat ⥤ GrpCat` by sending `X ↦ Multiplicative X` and `f ↦ f`.
-/
def toGrp : AddGrpCat ⥤ GrpCat where
  obj X := GrpCat.of (Multiplicative X)
  map {_} {_} f := GrpCat.ofHom f.hom.toMultiplicative

end AddGrpCat

namespace AddCommGrpCat

/-- The functor `AddCommGrpCat ⥤ CommGrpCat` by sending `X ↦ Multiplicative X` and `f ↦ f`.
-/
@[simps]
/-
**AddCommGrpCat.toCommGrp** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：toCommGrp : AddCommGrpCat ⥤ CommGrpCat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `AddCommGrpCat ⥤ CommGrpCat` by sending `X ↦ Multiplicative X` and `
f ↦ f`.
-/
def toCommGrp : AddCommGrpCat ⥤ CommGrpCat where
  obj X := CommGrpCat.of (Multiplicative X)
  map {_} {_} f := CommGrpCat.ofHom f.hom.toMultiplicative

end AddCommGrpCat

/-- The equivalence of categories between `GrpCat` and `AddGrpCat`
-/
@[simps]
/-
**groupAddGroupEquivalence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：groupAddGroupEquivalence : GrpCat ≌ AddGrpCat where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories between `GrpCat` and `AddGrpCat`
-/
def groupAddGroupEquivalence : GrpCat ≌ AddGrpCat where
  functor := GrpCat.toAddGrp
  inverse := AddGrpCat.toGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The equivalence of categories between `CommGrpCat` and `AddCommGrpCat`.
-/
@[simps]
/-
**commGroupAddCommGroupEquivalence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：commGroupAddCommGroupEquivalence : CommGrpCat ≌ AddCommGrpCat where functo
r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories between `CommGrpCat` and `AddCommGrpCat`.
-/
def commGroupAddCommGroupEquivalence : CommGrpCat ≌ AddCommGrpCat where
  functor := CommGrpCat.toAddCommGrp
  inverse := AddCommGrpCat.toCommGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _
