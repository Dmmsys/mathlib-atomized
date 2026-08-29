/-
Copyright (c) 2023 Anne Baanen, Sam van Gool, Leo Mayer, Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Sam van Gool, Leo Mayer, Brendan Murphy
-/
module

public import Mathlib.Topology.Category.Locale

/-!
# Adjunction between Locales and Topological Spaces

This file defines the point functor from the category of locales to topological spaces
and proves that it is right adjoint to the forgetful functor from topological spaces to locales.

## Main declarations

* `Locale.pt`: the *points* functor from the category of locales to the category of topological
  spaces.

* `Locale.adjunctionTopToLocalePT`: the adjunction between the functors `topToLocale` and `pt`.

## Motivation

This adjunction provides a framework in which several Stone-type dualities fit.

## Implementation notes

* In naming the various functions below, we follow common terminology and reserve the word *point*
  for an inhabitant of a type `X` which is a topological space, while we use the word *element* for
  an inhabitant of a type `L` which is a locale.

## References

* [J. Picado and A. Pultr, Frames and Locales: topology without points][picado2011frames]

## Tags

topological space, frame, locale, Stone duality, adjunction, points
-/

@[expose] public section

open CategoryTheory Order Set Topology TopologicalSpace

namespace Locale

/-! ### Definition of the points functor `pt` -/
section pt_definition

variable (L : Type*) [CompleteLattice L]

/--
Definition of `PT` / `PT` 的定义

English:
abbreviation PT
  body: FrameHom L Prop

中文:
缩写 PT
  定义体: FrameHom L Prop

Depends on / 依赖: FrameHom
-/
abbrev PT := FrameHom L Prop

/-- The frame homomorphism from a complete lattice `L` to the complete lattice of sets of
points of `L`. -/
@[simps]
/--
Definition of `openOfElementHom` / `openOfElementHom` 的定义

English:
definition openOfElementHom
  signature: : FrameHom L (Set (PT L)) where
  body: {x | x u}
  map_inf' a b := by simp [Set.ofPred_and]
  map_top' := by simp
  map_sSup' S := by ext; simp [Prop.exists_iff]

中文:
定义 openOfElementHom
  签名: : FrameHom L (Set (PT L)) where
  定义体: {x | x u}
  map_inf' a b := by simp [Set.ofPred_and]
  map_top' := by simp
  map_sSup' S := by ext; simp [Prop.exists_iff]
-/
def openOfElementHom : FrameHom L (Set (PT L)) where
  toFun u := {x | x u}
  map_inf' a b := by simp [Set.ofPred_and]
  map_top' := by simp
  map_sSup' S := by ext; simp [Prop.exists_iff]

namespace PT

/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace (PT L) where
  body: exists u, {x | x u} = s
  isOpen_univ := ⟨⊤, by simp⟩
  isOpen_inter := by rintro s t ⟨u, rfl⟩ ⟨v, rfl⟩; use u ⊓ v; simp_rw [map_inf]; rfl
  isOpen_sUnion S hS := by
    choose f hf using hS
    use ⨆ t, ⨆ ht, f t ht
    simp_rw [map_iSup, iSup_Prop_eq, ofPred_exists, hf, sUnion_eq_biUnion]

中文:
实例 instTopologicalSpace
  签名: : TopologicalSpace (PT L) where
  定义体: exists u, {x | x u} = s
  isOpen_univ := ⟨⊤, by simp⟩
  isOpen_inter := by rintro s t ⟨u, rfl⟩ ⟨v, rfl⟩; use u ⊓ v; simp_rw [map_inf]; rfl
  isOpen_sUnion S hS := by
    choose f hf using hS
    use ⨆ t, ⨆ ht, f t ht
    simp_rw [map_iSup, iSup_Prop_eq, ofPred_exists, hf, sUnion_eq_biUnion]
-/
instance instTopologicalSpace : TopologicalSpace (PT L) where
  IsOpen s := exists u, {x | x u} = s
  isOpen_univ := ⟨⊤, by simp⟩
  isOpen_inter := by rintro s t ⟨u, rfl⟩ ⟨v, rfl⟩; use u ⊓ v; simp_rw [map_inf]; rfl
  isOpen_sUnion S hS := by
    choose f hf using hS
    use ⨆ t, ⨆ ht, f t ht
    simp_rw [map_iSup, iSup_Prop_eq, ofPred_exists, hf, sUnion_eq_biUnion]

/--
lemma `isOpen_iff` / 引理 `isOpen_iff`

English:
lemma isOpen_iff
  given: (U : Set (PT L))
  statement: IsOpen U ↔ exists u : L, {x | x u} = U
  proof: Iff.rfl

中文:
引理 isOpen_iff
  条件: (U : Set (PT L))
  结论: IsOpen U ↔ 存在 u : L, {x | x u} = U
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isOpen_iff (U : Set (PT L)) : IsOpen U ↔ exists u : L, {x | x u} = U := Iff.rfl

end PT

/--
Definition of `pt` / `pt` 的定义

English:
definition pt
  signature: : Locale ⥤ TopCat where
  body: .of (PT L.unop)
  map f := TopCat.ofHom ⟨fun p => p.comp f.unop.hom,
continuous_def.2 by rintro s ⟨u, rfl⟩; use f.unop u; rfl⟩

中文:
定义 pt
  签名: : Locale ⥤ TopCat where
  定义体: .of (PT L.unop)
  map f := TopCat.ofHom ⟨fun p => p.comp f.unop.hom,
continuous_def.2 by rintro s ⟨u, rfl⟩; use f.unop u; rfl⟩

Depends on / 依赖: L.unop
-/
def pt : Locale ⥤ TopCat where
  obj L := .of (PT L.unop)
  map f := TopCat.ofHom ⟨fun p => p.comp f.unop.hom,
continuous_def.2 by rintro s ⟨u, rfl⟩; use f.unop u; rfl⟩

end pt_definition

section locale_top_adjunction

variable (X : Type*) [TopologicalSpace X] (L : Locale)

/-- The unit of the adjunction between locales and topological spaces, which associates with
a point `x` of the space `X` a point of the locale of opens of `X`. -/
@[simps]
/--
Definition of `localePointOfSpacePoint` / `localePointOfSpacePoint` 的定义

English:
definition localePointOfSpacePoint
  signature: (x : X)
  body: (x in ·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' S := by simp [Prop.exists_iff]

中文:
定义 localePointOfSpacePoint
  签名: (x : X)
  定义体: (x in ·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' S := by simp [Prop.exists_iff]
-/
def localePointOfSpacePoint (x : X) : PT (Opens X) where
  toFun := (x in ·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' S := by simp [Prop.exists_iff]

/--
Definition of `counitAppCont` / `counitAppCont` 的定义

English:
definition counitAppCont
  signature: : FrameHom L (Opens <| PT L) where
  body: ⟨openOfElementHom L u, u, rfl⟩
  map_inf' a b := by simp
  map_top' := by simp
  map_sSup' S := by ext; simp

中文:
定义 counitAppCont
  签名: : FrameHom L (Opens <| PT L) where
  定义体: ⟨openOfElementHom L u, u, rfl⟩
  map_inf' a b := by simp
  map_top' := by simp
  map_sSup' S := by ext; simp

Depends on / 依赖: openOfElementHom
-/
def counitAppCont : FrameHom L (Opens <| PT L) where
  toFun u := ⟨openOfElementHom L u, u, rfl⟩
  map_inf' a b := by simp
  map_top' := by simp
  map_sSup' S := by ext; simp

/--
Definition of `adjunctionTopToLocalePT` / `adjunctionTopToLocalePT` 的定义

English:
definition adjunctionTopToLocalePT
  signature: : topToLocale ⊣ pt where
  body: { app := fun X => TopCat.ofHom ⟨localePointOfSpacePoint X, continuous_def.2 <|
        by rintro _ ⟨u, rfl⟩; simpa using! u.2⟩ }
  counit := { app := fun L => ⟨Frm.ofHom (counitAppCont L)⟩ }

中文:
定义 adjunctionTopToLocalePT
  签名: : topToLocale ⊣ pt where
  定义体: { app := fun X => TopCat.ofHom ⟨localePointOfSpacePoint X, continuous_def.2 <|
        by rintro _ ⟨u, rfl⟩; simpa using! u.2⟩ }
  counit := { app := fun L => ⟨Frm.ofHom (counitAppCont L)⟩ }

Depends on / 依赖: TopCat, TopCat.ofHom, continuous_def, localePointOfSpacePoint
-/
def adjunctionTopToLocalePT : topToLocale ⊣ pt where
  unit := { app := fun X => TopCat.ofHom ⟨localePointOfSpacePoint X, continuous_def.2 <|
        by rintro _ ⟨u, rfl⟩; simpa using! u.2⟩ }
  counit := { app := fun L => ⟨Frm.ofHom (counitAppCont L)⟩ }

end locale_top_adjunction

end Locale
