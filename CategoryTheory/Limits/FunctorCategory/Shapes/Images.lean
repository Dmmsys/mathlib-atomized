/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.Tactic.CategoryTheory.CategoryStar

/-!

# The category of type-valued functors has images
-/

@[expose] public section

universe u

namespace CategoryTheory.FunctorToTypes

open Limits

variable {C : Type*} [Category* C]

attribute [local simp] FunctorToTypes.naturality in
/-- The image of a natural transformation between type-valued functors is a `MonoFactorisation` -/
@[simps]
/--
Definition of `monoFactorisation` / `monoFactorisation` 的定义

English:
definition monoFactorisation
  signature: {F G : C ⥤ Type u} (f : F ⟶ G)
  body: (Subfunctor.range f).toFunctor
  m := (Subfunctor.range f).ι
  e := Subfunctor.toRange f

中文:
定义 monoFactorisation
  签名: {F G : C ⥤ 类型u} (f : F ⟶ G)
  定义体: (Subfunctor.range f).toFunctor
  m := (Subfunctor.range f).ι
  e := Subfunctor.toRange f

Depends on / 依赖: Subfunctor, Subfunctor.range, toFunctor
-/
def monoFactorisation {F G : C ⥤ Type u} (f : F ⟶ G) : MonoFactorisation f where
  I := (Subfunctor.range f).toFunctor
  m := (Subfunctor.range f).ι
  e := Subfunctor.toRange f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `monoFactorisationIsImage` / `monoFactorisationIsImage` 的定义

English:
definition monoFactorisationIsImage
  signature: {F G : C ⥤ Type u} (f : F ⟶ G)
  body: {
    app X := ↾fun ⟨x, hx⟩ => H.e.app _ hx.choose
    naturality X Y g := by
      ext
      apply injective_of_mono (H.m.app Y)
      simp
      grind }
  lift_fac H := by
    ext
    simp
    grind

中文:
定义 monoFactorisationIsImage
  签名: {F G : C ⥤ 类型u} (f : F ⟶ G)
  定义体: {
    app X := ↾fun ⟨x, hx⟩ => H.e.app _ hx.choose
    naturality X Y g := by
      ext
      apply injective_of_mono (H.m.app Y)
      simp
      grind }
  lift_fac H := by
    ext
    simp
    grind
-/
noncomputable def monoFactorisationIsImage {F G : C ⥤ Type u} (f : F ⟶ G) :
IsImage monoFactorisation f where
  lift H := {
    app X := ↾fun ⟨x, hx⟩ => H.e.app _ hx.choose
    naturality X Y g := by
      ext
      apply injective_of_mono (H.m.app Y)
      simp
      grind }
  lift_fac H := by
    ext
    simp
    grind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasImages (C ⥤ Type*)
  body: { exists_image := ⟨ { F := _, isImage := monoFactorisationIsImage f } ⟩ }

中文:
实例 :
  签名: HasImages (C ⥤ 类型)
  定义体: { exists_image := ⟨ { F := _, isImage := monoFactorisationIsImage f } ⟩ }

Depends on / 依赖: exists_image, isImage, monoFactorisationIsImage
-/
instance : HasImages (C ⥤ Type*) where
  has_image f := { exists_image := ⟨ { F := _, isImage := monoFactorisationIsImage f } ⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasStrongEpiMonoFactorisations (C ⥤ Type*)
  body: ⟨{ I := image f, m := image.ι f, e := factorThruImage f }⟩

中文:
实例 :
  签名: HasStrongEpiMonoFactorisations (C ⥤ 类型)
  定义体: ⟨{ I := image f, m := image.ι f, e := factorThruImage f }⟩

Depends on / 依赖: factorThruImage
-/
instance : HasStrongEpiMonoFactorisations (C ⥤ Type*) where
  has_fac {F G} f := ⟨{ I := image f, m := image.ι f, e := factorThruImage f }⟩

end CategoryTheory.FunctorToTypes
