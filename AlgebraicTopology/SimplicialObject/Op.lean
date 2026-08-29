/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The covariant involution of the category of simplicial objects

In this file, we define the covariant involution `SimplicialObject.opFunctor`
of the category of simplicial objects that is induced by the
covariant involution `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`.

-/

@[expose] public section

universe v

open CategoryTheory

namespace SimplicialObject

variable {C : Type*} [Category.{v} C]

/--
Definition of `opFunctor` / `opFunctor` 的定义

English:
definition opFunctor
  signature: : SimplicialObject C ⥤ SimplicialObject C
  body: (Functor.whiskeringLeft _ _ _).obj SimplexCategory.rev.op

中文:
定义 opFunctor
  签名: : SimplicialObject C ⥤ SimplicialObject C
  定义体: (Functor.whiskeringLeft _ _ _).obj SimplexCategory.rev.op

Depends on / 依赖: Functor, Functor.whiskeringLeft, SimplexCategory, SimplexCategory.rev.op, whiskeringLeft
-/
def opFunctor : SimplicialObject C ⥤ SimplicialObject C :=
  (Functor.whiskeringLeft _ _ _).obj SimplexCategory.rev.op

/--
Definition of `opObjIso` / `opObjIso` 的定义

English:
definition opObjIso
  signature: {X : SimplicialObject C} {n : SimplexCategoryᵒᵖ}
  body: Iso.refl _

@[simp]

中文:
定义 opObjIso
  签名: {X : SimplicialObject C} {n : SimplexCategoryᵒᵖ}
  定义体: Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl
-/
def opObjIso {X : SimplicialObject C} {n : SimplexCategoryᵒᵖ} :
    (opFunctor.obj X).obj n ≅ X.obj n := Iso.refl _

@[simp]
/--
lemma `opFunctor_map_app` / 引理 `opFunctor_map_app`

English:
lemma opFunctor_map_app
  given: {X Y : SimplicialObject C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
  proof: by
  simp [opFunctor, opObjIso]

@[simp]

中文:
引理 opFunctor_map_app
  条件: {X Y : SimplicialObject C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
  证明: by
  simp [opFunctor, opObjIso]

@[simp]

Depends on / 依赖: opFunctor, opObjIso
-/
lemma opFunctor_map_app {X Y : SimplicialObject C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (opFunctor.map f).app n = opObjIso.hom ≫ f.app n ≫ opObjIso.inv := by
  simp [opFunctor, opObjIso]

@[simp]
/--
lemma `opFunctor_obj_map` / 引理 `opFunctor_obj_map`

English:
lemma opFunctor_obj_map
  given: (X : SimplicialObject C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
  proof: by
  simp [opFunctor, opObjIso]

@[simp]

中文:
引理 opFunctor_obj_map
  条件: (X : SimplicialObject C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
  证明: by
  simp [opFunctor, opObjIso]

@[simp]

Depends on / 依赖: opFunctor, opObjIso
-/
lemma opFunctor_obj_map (X : SimplicialObject C) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (opFunctor.obj X).map f =
      opObjIso.hom ≫ X.map (SimplexCategory.rev.map f.unop).op ≫ opObjIso.inv := by
  simp [opFunctor, opObjIso]

@[simp]
/--
lemma `opFunctor_obj_δ` / 引理 `opFunctor_obj_δ`

English:
lemma opFunctor_obj_δ
  given: (X : SimplicialObject C) {n : Nat} (i : Fin (n + 2))
  proof: by
  simp [opObjIso, SimplicialObject.δ]

@[simp]

中文:
引理 opFunctor_obj_δ
  条件: (X : SimplicialObject C) {n : 自然数} (i : 有限集 (n + 2))
  证明: by
  simp [opObjIso, SimplicialObject.δ]

@[simp]

Depends on / 依赖: SimplicialObject, opObjIso
-/
lemma opFunctor_obj_δ (X : SimplicialObject C) {n : Nat} (i : Fin (n + 2)) :
    (opFunctor.obj X).δ i = opObjIso.hom ≫ X.δ i.rev ≫ opObjIso.inv := by
  simp [opObjIso, SimplicialObject.δ]

@[simp]
/--
lemma `opFunctor_obj_σ` / 引理 `opFunctor_obj_σ`

English:
lemma opFunctor_obj_σ
  given: (X : SimplicialObject C) {n : Nat} (i : Fin (n + 1))
  proof: by
  simp [opObjIso, SimplicialObject.σ]

中文:
引理 opFunctor_obj_σ
  条件: (X : SimplicialObject C) {n : 自然数} (i : 有限集 (n + 1))
  证明: by
  simp [opObjIso, SimplicialObject.σ]

Depends on / 依赖: SimplicialObject, opObjIso
-/
lemma opFunctor_obj_σ (X : SimplicialObject C) {n : Nat} (i : Fin (n + 1)) :
    (opFunctor.obj X).σ i = opObjIso.hom ≫ X.σ i.rev ≫ opObjIso.inv := by
  simp [opObjIso, SimplicialObject.σ]

/--
Definition of `opFunctorCompOpFunctorIso` / `opFunctorCompOpFunctorIso` 的定义

English:
definition opFunctorCompOpFunctorIso
  signature: : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _
  body: (Functor.whiskeringLeftObjCompIso _ _).symm ≪≫
    (Functor.whiskeringLeft _ _ _).mapIso
    ((Functor.opHom _ _).mapIso (SimplexCategory.revCompRevIso).symm.op) ≪≫
    Functor.whiskeringLeftObjIdIso

@[simp]

中文:
定义 opFunctorCompOpFunctorIso
  签名: : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _
  定义体: (Functor.whiskeringLeftObjCompIso _ _).symm ≪≫
    (Functor.whiskeringLeft _ _ _).mapIso
    ((Functor.opHom _ _).mapIso (SimplexCategory.revCompRevIso).symm.op) ≪≫
    Functor.whiskeringLeftObjIdIso

@[simp]

Depends on / 依赖: opFunctor
-/
def opFunctorCompOpFunctorIso : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _ :=
  (Functor.whiskeringLeftObjCompIso _ _).symm ≪≫
    (Functor.whiskeringLeft _ _ _).mapIso
    ((Functor.opHom _ _).mapIso (SimplexCategory.revCompRevIso).symm.op) ≪≫
    Functor.whiskeringLeftObjIdIso

@[simp]
/--
lemma `opFunctorCompOpFunctorIso_hom_app_app` / 引理 `opFunctorCompOpFunctorIso_hom_app_app`

English:
lemma opFunctorCompOpFunctorIso_hom_app_app
  given: (X : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
  proof: by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

@[simp]

中文:
引理 opFunctorCompOpFunctorIso_hom_app_app
  条件: (X : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
  证明: by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

@[simp]

Depends on / 依赖: opFunctor, opFunctorCompOpFunctorIso, opObjIso
-/
lemma opFunctorCompOpFunctorIso_hom_app_app (X : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    (opFunctorCompOpFunctorIso.hom.app X).app n = opObjIso.hom ≫ opObjIso.hom := by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

@[simp]
/--
lemma `opFunctorCompOpFunctorIso_inv_app_app` / 引理 `opFunctorCompOpFunctorIso_inv_app_app`

English:
lemma opFunctorCompOpFunctorIso_inv_app_app
  given: (X : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
  proof: by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

中文:
引理 opFunctorCompOpFunctorIso_inv_app_app
  条件: (X : SimplicialObject C) (n : SimplexCategoryᵒᵖ)
  证明: by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

Depends on / 依赖: opFunctor, opFunctorCompOpFunctorIso, opObjIso
-/
lemma opFunctorCompOpFunctorIso_inv_app_app (X : SimplicialObject C) (n : SimplexCategoryᵒᵖ) :
    (opFunctorCompOpFunctorIso.inv.app X).app n = opObjIso.inv ≫ opObjIso.inv := by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

/-- The functor `opFunctor : SimplicialObject C ⥤ SimplicialObject C`
as an equivalence of categories. -/
@[simps]
/--
Definition of `opEquivalence` / `opEquivalence` 的定义

English:
definition opEquivalence
  signature: : SimplicialObject C ≌ SimplicialObject C where
  body: opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso

中文:
定义 opEquivalence
  签名: : SimplicialObject C ≌ SimplicialObject C where
  定义体: opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso

Depends on / 依赖: opFunctor
-/
def opEquivalence : SimplicialObject C ≌ SimplicialObject C where
  functor := opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso

end SimplicialObject
