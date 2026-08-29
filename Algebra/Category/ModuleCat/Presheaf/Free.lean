/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Joel Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# The free presheaf of modules on a presheaf of sets

In this file, given a presheaf of rings `R` on a category `C`,
we construct the functor
`PresheafOfModules.free : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R`
which sends a presheaf of types to the corresponding presheaf of free modules.
`PresheafOfModules.freeAdjunction` shows that this functor is the left
adjoint to the forget functor.

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.

-/

@[expose] public section

universe u v₁ u₁

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

set_option backward.isDefEq.respectTransparency.types false in
variable {R} in
/-- Given a presheaf of types `F : Cᵒᵖ ⥤ Type u`, this is the presheaf
of modules over `R` which sends `X : Cᵒᵖ` to the free `R.obj X`-module on `F.obj X`. -/
@[simps]
/--
Definition of `freeObj` / `freeObj` 的定义

English:
definition freeObj
  signature: (F : Cᵒᵖ ⥤ Type u)
  body: (ModuleCat.free (R.obj X)).obj (F.obj X)
  map {X Y} f := ModuleCat.freeDesc (↾fun x => ModuleCat.freeMk (F.map f x))
  map_id := by aesop

中文:
定义 freeObj
  签名: (F : Cᵒᵖ ⥤ 类型u)
  定义体: (ModuleCat.free (R.obj X)).obj (F.obj X)
  map {X Y} f := ModuleCat.freeDesc (↾fun x => ModuleCat.freeMk (F.map f x))
  map_id := by aesop

Depends on / 依赖: F.obj, ModuleCat, ModuleCat.free, R.obj
-/
noncomputable def freeObj (F : Cᵒᵖ ⥤ Type u) : PresheafOfModules.{u} R where
  obj X := (ModuleCat.free (R.obj X)).obj (F.obj X)
  map {X Y} f := ModuleCat.freeDesc (↾fun x => ModuleCat.freeMk (F.map f x))
  map_id := by aesop

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The free presheaf of modules functor `(Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R`. -/
@[simps]
/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R where
  body: freeObj
  map {F G} φ := { app := fun X => (ModuleCat.free (R.obj X)).map (φ.app X) }

中文:
定义 free
  签名: : (Cᵒᵖ ⥤ 类型u) ⥤ PresheafOfModules.{u} R where
  定义体: freeObj
  map {F G} φ := { app := fun X => (ModuleCat.free (R.obj X)).map (φ.app X) }

Depends on / 依赖: freeObj
-/
noncomputable def free : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R where
  obj := freeObj
  map {F G} φ := { app := fun X => (ModuleCat.free (R.obj X)).map (φ.app X) }

section

variable {R}

variable {F : Cᵒᵖ ⥤ Type u} {G : PresheafOfModules.{u} R}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The morphism of presheaves of modules `freeObj F ⟶ G` corresponding to
a morphism `F ⟶ G.presheaf ⋙ forget _` of presheaves of types. -/
@[simps]
/--
Definition of `freeObjDesc` / `freeObjDesc` 的定义

English:
definition freeObjDesc
  signature: (φ : F ⟶ G.presheaf ⋙ forget _)
  body: ModuleCat.freeDesc (φ.app X)
  naturality {X Y} f := by
    dsimp
    ext x
    simpa using! NatTrans.naturality_apply φ f x

中文:
定义 freeObjDesc
  签名: (φ : F ⟶ G.presheaf ⋙ forget _)
  定义体: ModuleCat.freeDesc (φ.app X)
  naturality {X Y} f := by
    dsimp
    ext x
    simpa using! NatTrans.naturality_apply φ f x

Depends on / 依赖: ModuleCat, ModuleCat.freeDesc, freeDesc
-/
noncomputable def freeObjDesc (φ : F ⟶ G.presheaf ⋙ forget _) : freeObj F ⟶ G where
  app X := ModuleCat.freeDesc (φ.app X)
  naturality {X Y} f := by
    dsimp
    ext x
    simpa using! NatTrans.naturality_apply φ f x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (F R) in
/-- The unit of `PresheafOfModules.freeAdjunction`. -/
@[simps]
/--
Definition of `freeAdjunctionUnit` / `freeAdjunctionUnit` 的定义

English:
definition freeAdjunctionUnit
  signature: : F ⟶ (freeObj (R := R) F).presheaf ⋙ forget _ where
  body: ↾fun x => ModuleCat.freeMk x
  naturality X Y f := by ext; simp [presheaf]

中文:
定义 freeAdjunctionUnit
  签名: : F ⟶ (freeObj (R := R) F).presheaf ⋙ forget _ where
  定义体: ↾fun x => ModuleCat.freeMk x
  naturality X Y f := by ext; simp [presheaf]

Depends on / 依赖: forget, presheaf
-/
noncomputable def freeAdjunctionUnit : F ⟶ (freeObj (R := R) F).presheaf ⋙ forget _ where
  app X := ↾fun x => ModuleCat.freeMk x
  naturality X Y f := by ext; simp [presheaf]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `freeHomEquiv` / `freeHomEquiv` 的定义

English:
definition freeHomEquiv
  signature: : (freeObj F ⟶ G) ≃ (F ⟶ G.presheaf ⋙ forget _) where
  body: freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ) _
  invFun φ := freeObjDesc φ
  left_inv ψ := by ext1 X; dsimp; ext x; simp [toPresheaf]
  right_inv φ := by ext; simp [toPresheaf]

中文:
定义 freeHomEquiv
  签名: : (freeObj F ⟶ G) ≃ (F ⟶ G.presheaf ⋙ forget _) where
  定义体: freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ) _
  invFun φ := freeObjDesc φ
  left_inv ψ := by ext1 X; dsimp; ext x; simp [toPresheaf]
  right_inv φ := by ext; simp [toPresheaf]

Depends on / 依赖: Functor, Functor.whiskerRight, freeAdjunctionUnit, toPresheaf, whiskerRight
-/
noncomputable def freeHomEquiv : (freeObj F ⟶ G) ≃ (F ⟶ G.presheaf ⋙ forget _) where
  toFun ψ := freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ) _
  invFun φ := freeObjDesc φ
  left_inv ψ := by ext1 X; dsimp; ext x; simp [toPresheaf]
  right_inv φ := by ext; simp [toPresheaf]

/--
lemma `free_hom_ext` / 引理 `free_hom_ext`

English:
lemma free_hom_ext
  statement: {ψ ψ' : freeObj F ⟶ G}
  proof: freeHomEquiv.injective h

中文:
引理 free_hom_ext
  结论: {ψ ψ' : freeObj F ⟶ G}
  证明: freeHomEquiv.injective h

Depends on / 依赖: freeHomEquiv, freeHomEquiv.injective, injective
-/
lemma free_hom_ext {ψ ψ' : freeObj F ⟶ G}
    (h : freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ) _ =
      freeAdjunctionUnit R F ≫ Functor.whiskerRight ((toPresheaf _).map ψ') _) : ψ = ψ' :=
  freeHomEquiv.injective h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R) in
/--
Definition of `freeAdjunction` / `freeAdjunction` 的定义

English:
definition freeAdjunction
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => freeHomEquiv
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} f g =>
        free_hom_ext (by ext; simp [freeHomEquiv, toPresheaf])
      homEquiv_naturality_right := fun {F G₁ G₂} f g => rfl }

中文:
定义 freeAdjunction
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => freeHomEquiv
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} f g =>
        free_hom_ext (by ext; simp [freeHomEquiv, toPresheaf])
      homEquiv_naturality_right := fun {F G₁ G₂} f g => rfl }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, freeHomEquiv, free_hom_ext, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, mkOfHomEquiv, toPresheaf
-/
noncomputable def freeAdjunction :
    free.{u} R ⊣ (toPresheaf R ⋙ (Functor.whiskeringRight _ _ _).obj (forget Ab)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => freeHomEquiv
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} f g =>
        free_hom_ext (by ext; simp [freeHomEquiv, toPresheaf])
      homEquiv_naturality_right := fun {F G₁ G₂} f g => rfl }

set_option backward.isDefEq.respectTransparency.types false in
variable (F G) in
@[simp]
/--
lemma `freeAdjunction_homEquiv` / 引理 `freeAdjunction_homEquiv`

English:
lemma freeAdjunction_homEquiv
  statement: (freeAdjunction R).homEquiv F G = freeHomEquiv
  proof: by
  simp [freeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

中文:
引理 freeAdjunction_homEquiv
  结论: (freeAdjunction R).homEquiv F G = freeHomEquiv
  证明: by
  simp [freeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv_homEquiv, freeAdjunction, mkOfHomEquiv_homEquiv
-/
lemma freeAdjunction_homEquiv : (freeAdjunction R).homEquiv F G = freeHomEquiv := by
  simp [freeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

set_option backward.isDefEq.respectTransparency.types false in
variable (R F) in
@[simp]
/--
lemma `freeAdjunction_unit_app` / 引理 `freeAdjunction_unit_app`

English:
lemma freeAdjunction_unit_app
  proof: rfl

中文:
引理 freeAdjunction_unit_app
  证明: rfl
-/
lemma freeAdjunction_unit_app :
    (freeAdjunction R).unit.app F = freeAdjunctionUnit R F := rfl

end

end PresheafOfModules
