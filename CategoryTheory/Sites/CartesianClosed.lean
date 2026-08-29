/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Ideal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Sheafification
/-!

# Sheaf categories are Cartesian closed

...if the underlying presheaf category is Cartesian closed, the target category has
(chosen) finite products, and there exists a sheafification functor.
-/

public section

noncomputable section

open CategoryTheory Presheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (A : Type*) [Category* A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasSheafify
  signature: J A] [CartesianMonoidalCategory A] [MonoidalClosed (Cᵒᵖ ⥤ A)] :
  body: cartesianClosedOfReflective' (sheafToPresheaf _ _) {
    obj F := ⟨F.obj, (isSheaf_of_iso_iff F.2.choose_spec.some).1 F.2.choose.property⟩
    map f := ⟨f.hom⟩ } (Iso.refl _)

中文:
实例 [HasSheafify
  签名: J A] [CartesianMonoidalCategory A] [MonoidalClosed (Cᵒᵖ ⥤ A)] :
  定义体: cartesianClosedOfReflective' (sheafToPresheaf _ _) {
    obj F := ⟨F.obj, (isSheaf_of_iso_iff F.2.choose_spec.some).1 F.2.choose.property⟩
    map f := ⟨f.hom⟩ } (Iso.refl _)

Depends on / 依赖: F.obj, Iso.refl, cartesianClosedOfReflective, choose.property, choose_spec, choose_spec.some, f.hom, isSheaf_of_iso_iff, property, sheafToPresheaf
-/
instance [HasSheafify J A] [CartesianMonoidalCategory A] [MonoidalClosed (Cᵒᵖ ⥤ A)] :
    MonoidalClosed (Sheaf J A) :=
  cartesianClosedOfReflective' (sheafToPresheaf _ _) {
    obj F := ⟨F.obj, (isSheaf_of_iso_iff F.2.choose_spec.some).1 F.2.choose.property⟩
    map f := ⟨f.hom⟩ } (Iso.refl _)
