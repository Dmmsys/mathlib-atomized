/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf

/-!
# Change of presheaf of rings

In this file, we define the restriction of scalars functor
`restrictScalars α : PresheafOfModules.{v} R' ⥤ PresheafOfModules.{v} R`
attached to a morphism of presheaves of rings `α : R ⟶ R'`.

-/

@[expose] public section

universe v v' u u'

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}}

/-- The restriction of scalars of presheaves of modules, on objects. -/
@[simps]
/--
Definition of `restrictScalarsObj` / `restrictScalarsObj` 的定义

English:
definition restrictScalarsObj
  signature: (M' : PresheafOfModules.{v} R') (α : R ⟶ R')
  body: fun X => (ModuleCat.restrictScalars (α.app X).hom).obj (M'.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)` and `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map := fun {X Y} f => ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars (α.app X).hom).obj (M'.obj X))
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
        ((ModuleCat.restrictScalars (α.app Y).hom).obj (M'.obj Y)))
    { toFun := M'.map f
      map_add' := map_add _
      map_smul' := fun r x => (M'.map_smul f (α.app _ r) x).trans (by
        have eq := RingHom.congr_fun (congrArg RingCat.Hom.hom <| α.naturality f) r
        dsimp at eq
        rw [← eq]
        rfl) }

中文:
定义 restrictScalarsObj
  签名: (M' : 预模层.{v} R') (α : R ⟶ R')
  定义体: fun X => (ModuleCat.restrictScalars (α.app X).hom).obj (M'.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)` and `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map := fun {X Y} f => ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars (α.app X).hom).obj (M'.obj X))
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
        ((ModuleCat.restrictScalars (α.app Y).hom).obj (M'.obj Y)))
    { toFun := M'.map f
      map_add' := map_add _
      map_smul' := fun r x => (M'.map_smul f (α.app _ r) x).trans (by
        have eq := RingHom.congr_fun (congrArg RingCat.Hom.hom <| α.naturality f) r
        dsimp at eq
        rw [← eq]
        rfl) }

Depends on / 依赖: ModuleCat, ModuleCat.restrictScalars, restrictScalars
-/
noncomputable def restrictScalarsObj (M' : PresheafOfModules.{v} R') (α : R ⟶ R') :
    PresheafOfModules R where
  obj := fun X => (ModuleCat.restrictScalars (α.app X).hom).obj (M'.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(X := ...)` and `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map := fun {X Y} f => ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars (α.app X).hom).obj (M'.obj X))
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
        ((ModuleCat.restrictScalars (α.app Y).hom).obj (M'.obj Y)))
    { toFun := M'.map f
      map_add' := map_add _
      map_smul' := fun r x => (M'.map_smul f (α.app _ r) x).trans (by
        have eq := RingHom.congr_fun (congrArg RingCat.Hom.hom <| α.naturality f) r
        dsimp at eq
        rw [← eq]
        rfl) }

/-- The restriction of scalars functor `PresheafOfModules R' ⥤ PresheafOfModules R`
induced by a morphism of presheaves of rings `R ⟶ R'`. -/
@[simps]
/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (α : R ⟶ R')
  body: M'.restrictScalarsObj α
  map φ' :=
    { app := fun X => (ModuleCat.restrictScalars (α.app X).hom).map (Hom.app φ' X)
      naturality := fun {X Y} f => by
        ext x
        exact naturality_apply φ' f x }

中文:
定义 restrictScalars
  签名: (α : R ⟶ R')
  定义体: M'.restrictScalarsObj α
  map φ' :=
    { app := fun X => (ModuleCat.restrictScalars (α.app X).hom).map (Hom.app φ' X)
      naturality := fun {X Y} f => by
        ext x
        exact naturality_apply φ' f x }

Depends on / 依赖: restrictScalarsObj
-/
noncomputable def restrictScalars (α : R ⟶ R') :
    PresheafOfModules.{v} R' ⥤ PresheafOfModules.{v} R where
  obj M' := M'.restrictScalarsObj α
  map φ' :=
    { app := fun X => (ModuleCat.restrictScalars (α.app X).hom).map (Hom.app φ' X)
      naturality := fun {X Y} f => by
        ext x
        exact naturality_apply φ' f x }

instance (α : R ⟶ R') : (restrictScalars.{v} α).Additive where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (restrictScalars (𝟙 R)).Full
  body: inferInstanceAs (𝟭 _).Full

中文:
实例 :
  签名: (restrictScalars (𝟙 R)).满
  定义体: inferInstanceAs (𝟭 _).Full
-/
instance : (restrictScalars (𝟙 R)).Full := inferInstanceAs (𝟭 _).Full

instance (α : R ⟶ R') : (restrictScalars α).Faithful where
  map_injective h := (toPresheaf R').map_injective ((toPresheaf R).congr_map h)

/--
Definition of `restrictScalarsCompToPresheaf` / `restrictScalarsCompToPresheaf` 的定义

English:
definition restrictScalarsCompToPresheaf
  signature: (α : R ⟶ R')
  body: Iso.refl _

中文:
定义 restrictScalarsCompToPresheaf
  签名: (α : R ⟶ R')
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def restrictScalarsCompToPresheaf (α : R ⟶ R') :
    restrictScalars.{v} α ⋙ toPresheaf R ≅ toPresheaf R' := Iso.refl _

end PresheafOfModules
