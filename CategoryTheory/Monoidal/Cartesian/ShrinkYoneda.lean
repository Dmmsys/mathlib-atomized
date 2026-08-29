/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.MonCat.Shrink
public import Mathlib.Algebra.Category.Grp.Shrink
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The Yoneda embedding for monoid objects for locally small categories

Let `C` be a locally `w`-small category. We define the Yoneda
embedding `shrinkYonedaMon : Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w} w` and its `Grp` analogue.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] [CartesianMonoidalCategory C]

set_option backward.defeqAttrib.useBackward true in
instance (M : Mon C) (X : Cᵒᵖ) : Small.{w} ((yonedaMon.obj M).obj X) := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (M : Grp C) (X : Cᵒᵖ) : Small.{w} ((yonedaGrp.obj M).obj X) := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda embedding `Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w}` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
/--
Definition of `shrinkYonedaMon` / `shrinkYonedaMon` 的定义

English:
definition shrinkYonedaMon
  signature: :
  body: MonCat.shrinkFunctor (yonedaMon.obj X)
  map f := MonCat.shrinkFunctorMap (yonedaMon.map f)

中文:
定义 shrinkYonedaMon
  签名: :
  定义体: MonCat.shrinkFunctor (yonedaMon.obj X)
  map f := MonCat.shrinkFunctorMap (yonedaMon.map f)

Depends on / 依赖: MonCat, MonCat.shrinkFunctor, shrinkFunctor, yonedaMon, yonedaMon.obj
-/
noncomputable def shrinkYonedaMon :
    Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w} where
  obj X := MonCat.shrinkFunctor (yonedaMon.obj X)
  map f := MonCat.shrinkFunctorMap (yonedaMon.map f)

open MonObj

/--
Definition of `shrinkYonedaMonObjObjEquiv` / `shrinkYonedaMonObjObjEquiv` 的定义

English:
definition shrinkYonedaMonObjObjEquiv
  signature: {M : Mon C} {Y : Cᵒᵖ}
  body: Shrink.mulEquiv

中文:
定义 shrinkYonedaMonObjObjEquiv
  签名: {M : Mon C} {Y : Cᵒᵖ}
  定义体: Shrink.mulEquiv

Depends on / 依赖: Shrink, Shrink.mulEquiv, mulEquiv
-/
noncomputable def shrinkYonedaMonObjObjEquiv {M : Mon C} {Y : Cᵒᵖ} :
    (shrinkYonedaMon.{w}.obj M).obj Y ≃* (Y.unop ⟶ M.X) :=
  Shrink.mulEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm` / 引理 `shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm`

English:
lemma shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm
  proof: by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

中文:
引理 shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm
  证明: by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

Depends on / 依赖: shrinkYonedaMon, shrinkYonedaMonObjObjEquiv
-/
lemma shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm
    {M : Mon C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) :
    (shrinkYonedaMon.{w}.obj _).map g (shrinkYonedaMonObjObjEquiv.symm f) =
      shrinkYonedaMonObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

/--
lemma `shrinkYonedaMonObjObjEquiv_symm_comp` / 引理 `shrinkYonedaMonObjObjEquiv_symm_comp`

English:
lemma shrinkYonedaMonObjObjEquiv_symm_comp
  given: {M : Mon C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X)
  proof: (shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm g.op f).symm

中文:
引理 shrinkYonedaMonObjObjEquiv_symm_comp
  条件: {M : Mon C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X)
  证明: (shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm g.op f).symm

Depends on / 依赖: g.op, shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm
-/
lemma shrinkYonedaMonObjObjEquiv_symm_comp {M : Mon C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X) :
    shrinkYonedaMonObjObjEquiv.symm (g ≫ f) =
    (shrinkYonedaMon.obj _).map g.op (shrinkYonedaMonObjObjEquiv.symm f) :=
  (shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm g.op f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `shrinkYonedaMon_map_app_shrinkYonedaObjObjEquiv_symm` / 引理 `shrinkYonedaMon_map_app_shrinkYonedaObjObjEquiv_symm`

English:
lemma shrinkYonedaMon_map_app_shrinkYonedaObjObjEquiv_symm
  proof: by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

中文:
引理 shrinkYonedaMon_map_app_shrinkYonedaObjObjEquiv_symm
  证明: by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

Depends on / 依赖: shrinkYonedaMon, shrinkYonedaMonObjObjEquiv
-/
lemma shrinkYonedaMon_map_app_shrinkYonedaObjObjEquiv_symm
    {M M' : Mon C} {Y : Cᵒᵖ} (f : Y.unop ⟶ M.X) (g : M ⟶ M') :
    (shrinkYonedaMon.map g).app _ (shrinkYonedaMonObjObjEquiv.symm f) =
      shrinkYonedaMonObjObjEquiv.symm (f ≫ g.hom) := by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda embedding `Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{w}` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
/--
Definition of `shrinkYonedaGrp` / `shrinkYonedaGrp` 的定义

English:
definition shrinkYonedaGrp
  signature: :
  body: GrpCat.shrinkFunctor (yonedaGrp.obj X)
  map f := GrpCat.shrinkFunctorMap (yonedaGrp.map f)

中文:
定义 shrinkYonedaGrp
  签名: :
  定义体: GrpCat.shrinkFunctor (yonedaGrp.obj X)
  map f := GrpCat.shrinkFunctorMap (yonedaGrp.map f)

Depends on / 依赖: GrpCat, GrpCat.shrinkFunctor, shrinkFunctor, yonedaGrp, yonedaGrp.obj
-/
noncomputable def shrinkYonedaGrp :
    Grp C ⥤ Cᵒᵖ ⥤ GrpCat.{w} where
  obj X := GrpCat.shrinkFunctor (yonedaGrp.obj X)
  map f := GrpCat.shrinkFunctorMap (yonedaGrp.map f)

/--
Definition of `shrinkYonedaGrpObjObjEquiv` / `shrinkYonedaGrpObjObjEquiv` 的定义

English:
definition shrinkYonedaGrpObjObjEquiv
  signature: {M : Grp C} {Y : Cᵒᵖ}
  body: Shrink.mulEquiv

中文:
定义 shrinkYonedaGrpObjObjEquiv
  签名: {M : Grp C} {Y : Cᵒᵖ}
  定义体: Shrink.mulEquiv

Depends on / 依赖: Shrink, Shrink.mulEquiv, mulEquiv
-/
noncomputable def shrinkYonedaGrpObjObjEquiv {M : Grp C} {Y : Cᵒᵖ} :
    (shrinkYonedaGrp.{w}.obj M).obj Y ≃* (Y.unop ⟶ M.X) :=
  Shrink.mulEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm` / 引理 `shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm`

English:
lemma shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm
  proof: by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]

中文:
引理 shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm
  证明: by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]

Depends on / 依赖: shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv
-/
lemma shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm
    {M : Grp C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ M.X) :
    (shrinkYonedaGrp.{w}.obj _).map g (shrinkYonedaGrpObjObjEquiv.symm f) =
      shrinkYonedaGrpObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]

/--
lemma `shrinkYonedaGrpObjObjEquiv_symm_comp` / 引理 `shrinkYonedaGrpObjObjEquiv_symm_comp`

English:
lemma shrinkYonedaGrpObjObjEquiv_symm_comp
  given: {M : Grp C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X)
  proof: (shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm g.op f).symm

中文:
引理 shrinkYonedaGrpObjObjEquiv_symm_comp
  条件: {M : Grp C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X)
  证明: (shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm g.op f).symm

Depends on / 依赖: g.op, shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm
-/
lemma shrinkYonedaGrpObjObjEquiv_symm_comp {M : Grp C} {Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ M.X) :
    shrinkYonedaGrpObjObjEquiv.symm (g ≫ f) =
    (shrinkYonedaGrp.obj _).map g.op (shrinkYonedaGrpObjObjEquiv.symm f) :=
  (shrinkYonedaGrp_obj_map_shrinkYonedaGrpObjObjEquiv_symm g.op f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `shrinkYonedaGrp_map_app_shrinkYonedaObjObjEquiv_symm` / 引理 `shrinkYonedaGrp_map_app_shrinkYonedaObjObjEquiv_symm`

English:
lemma shrinkYonedaGrp_map_app_shrinkYonedaObjObjEquiv_symm
  proof: by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]

中文:
引理 shrinkYonedaGrp_map_app_shrinkYonedaObjObjEquiv_symm
  证明: by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]

Depends on / 依赖: shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv
-/
lemma shrinkYonedaGrp_map_app_shrinkYonedaObjObjEquiv_symm
    {M M' : Grp C} {Y : Cᵒᵖ} (f : Y.unop ⟶ M.X) (g : M ⟶ M') :
    (shrinkYonedaGrp.map g).app _ (shrinkYonedaGrpObjObjEquiv.symm f) =
      shrinkYonedaGrpObjObjEquiv.symm (f ≫ g.hom.hom) := by
  simp [shrinkYonedaGrp, shrinkYonedaGrpObjObjEquiv]

end CategoryTheory
