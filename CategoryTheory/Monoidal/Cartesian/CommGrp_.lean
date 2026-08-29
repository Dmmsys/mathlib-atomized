/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# Yoneda embedding of `CommGrp C`
-/

@[expose] public section

assert_not_exists Field

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory
universe w v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C] {X : C}

variable (X) in
/--
Definition of `abbrev` / `abbrev` 的定义

English:
class abbrev
  parameters: CommGrpObj
  (no additional axioms)

中文:
类 abbrev
  参数: CommGrpObj
  (无附加公理)

Depends on / 依赖: GrpObj, IsCommMonObj
-/
class abbrev CommGrpObj := GrpObj X, IsCommMonObj X

variable (X) in
/-- If `X` represents a presheaf of commutative groups, then `X` is a commutative group object. -/
@[instance_reducible]
/--
Definition of `CommGrpObj.ofRepresentableBy` / `CommGrpObj.ofRepresentableBy` 的定义

English:
definition CommGrpObj.ofRepresentableBy
  signature: (F : Cᵒᵖ ⥤ CommGrpCat.{w})
  body: GrpObj.ofRepresentableBy X (F ⋙ forget₂ CommGrpCat GrpCat) α
  __ := IsCommMonObj.ofRepresentableBy X (F ⋙ forget₂ CommGrpCat CommMonCat) α

中文:
定义 CommGrpObj.ofRepresentableBy
  签名: (F : Cᵒᵖ ⥤ 交换群范畴.{w})
  定义体: GrpObj.ofRepresentableBy X (F ⋙ forget₂ CommGrpCat GrpCat) α
  __ := IsCommMonObj.ofRepresentableBy X (F ⋙ forget₂ CommGrpCat CommMonCat) α

Depends on / 依赖: CommGrpCat, GrpCat, GrpObj, GrpObj.ofRepresentableBy, ofRepresentableBy
-/
def CommGrpObj.ofRepresentableBy (F : Cᵒᵖ ⥤ CommGrpCat.{w})
    (α : (F ⋙ forget _).RepresentableBy X) : CommGrpObj X where
  __ := GrpObj.ofRepresentableBy X (F ⋙ forget₂ CommGrpCat GrpCat) α
  __ := IsCommMonObj.ofRepresentableBy X (F ⋙ forget₂ CommGrpCat CommMonCat) α

set_option backward.defeqAttrib.useBackward true in
/-- The yoneda embedding of `CommGrp C` into presheaves of groups. -/
@[simps]
/--
Definition of `yonedaCommGrpGrpObj` / `yonedaCommGrpGrpObj` 的定义

English:
definition yonedaCommGrpGrpObj
  signature: (G : CommGrp C)
  body: .of (unop H ⟶ G.toGrp)
  map {H I} f := CommGrpCat.ofHom {
    toFun := (f.unop ≫ ·)
    map_one' := by ext; simp [Mon.Hom.hom_one]
    map_mul' g h := by
      ext
      simpa using! ((yonedaGrpObj G.X).map f.unop.hom.hom.op).hom.map_mul g.hom.hom h.hom.hom }

中文:
定义 yonedaCommGrpGrpObj
  签名: (G : 交换群 C)
  定义体: .of (unop H ⟶ G.toGrp)
  map {H I} f := CommGrpCat.ofHom {
    toFun := (f.unop ≫ ·)
    map_one' := by ext; simp [Mon.Hom.hom_one]
    map_mul' g h := by
      ext
      simpa using! ((yonedaGrpObj G.X).map f.unop.hom.hom.op).hom.map_mul g.hom.hom h.hom.hom }

Depends on / 依赖: G.toGrp
-/
def yonedaCommGrpGrpObj (G : CommGrp C) : (Grp C)ᵒᵖ ⥤ CommGrpCat where
  obj H := .of (unop H ⟶ G.toGrp)
  map {H I} f := CommGrpCat.ofHom {
    toFun := (f.unop ≫ ·)
    map_one' := by ext; simp [Mon.Hom.hom_one]
    map_mul' g h := by
      ext
      simpa using! ((yonedaGrpObj G.X).map f.unop.hom.hom.op).hom.map_mul g.hom.hom h.hom.hom }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The yoneda embedding of `CommGrp C` into presheaves of groups. -/
@[simps]
/--
Definition of `yonedaCommGrpGrp` / `yonedaCommGrpGrp` 的定义

English:
definition yonedaCommGrpGrp
  signature: : CommGrp C ⥤ (Grp C)ᵒᵖ ⥤ CommGrpCat where
  body: yonedaCommGrpGrpObj
  map {X₁ X₂} ψ := {
    app Y := CommGrpCat.ofHom {
      toFun := (· ≫ ψ.hom)
      map_one' := by ext; simp
      map_mul' f g := by
        ext
        simpa using ((yonedaGrp.map ψ.hom).app (op (unop Y).X)).hom.map_mul f.hom.hom g.hom.hom } }

中文:
定义 yonedaCommGrpGrp
  签名: : 交换群 C ⥤ (群 C)ᵒᵖ ⥤ 交换群范畴 where
  定义体: yonedaCommGrpGrpObj
  map {X₁ X₂} ψ := {
    app Y := CommGrpCat.ofHom {
      toFun := (· ≫ ψ.hom)
      map_one' := by ext; simp
      map_mul' f g := by
        ext
        simpa using ((yonedaGrp.map ψ.hom).app (op (unop Y).X)).hom.map_mul f.hom.hom g.hom.hom } }

Depends on / 依赖: yonedaCommGrpGrpObj
-/
def yonedaCommGrpGrp : CommGrp C ⥤ (Grp C)ᵒᵖ ⥤ CommGrpCat where
  obj := yonedaCommGrpGrpObj
  map {X₁ X₂} ψ := {
    app Y := CommGrpCat.ofHom {
      toFun := (· ≫ ψ.hom)
      map_one' := by ext; simp
      map_mul' f g := by
        ext
        simpa using ((yonedaGrp.map ψ.hom).app (op (unop Y).X)).hom.map_mul f.hom.hom g.hom.hom } }

end CategoryTheory
