/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# Sieves attached to subpresheaves

Given a subpresheaf `G` of a presheaf of types `F : Cᵒᵖ ⥤ Type w` and
a section `s : F.obj U`, we define a sieve `G.sieveOfSection s : Sieve (unop U)`
and the associated compatible family of elements with values in `G.toFunctor`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory.Subfunctor

open Opposite

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w} (G : Subfunctor F)

/-- Given a subpresheaf `G` of `F`, an `F`-section `s` on `U`, we may define a sieve of `U`
consisting of all `f : V ⟶ U` such that the restriction of `s` along `f` is in `G`. -/
@[simps]
/--
Definition of `sieveOfSection` / `sieveOfSection` 的定义

English:
definition sieveOfSection
  signature: {U : Cᵒᵖ} (s : F.obj U)
  body: F.map f.op s in G.obj (op V)
  downward_closed := @fun V W i hi j => by
    simpa using G.map _ hi

中文:
定义 sieveOfSection
  签名: {U : Cᵒᵖ} (s : F.obj U)
  定义体: F.map f.op s in G.obj (op V)
  downward_closed := @fun V W i hi j => by
    simpa using G.map _ hi

Depends on / 依赖: F.map, G.obj, f.op
-/
def sieveOfSection {U : Cᵒᵖ} (s : F.obj U) : Sieve (unop U) where
  arrows V f := F.map f.op s in G.obj (op V)
  downward_closed := @fun V W i hi j => by
    simpa using G.map _ hi

/--
Definition of `familyOfElementsOfSection` / `familyOfElementsOfSection` 的定义

English:
definition familyOfElementsOfSection
  signature: {U : Cᵒᵖ} (s : F.obj U)
  body: fun _ i hi => ⟨F.map i.op s, hi⟩

中文:
定义 familyOfElementsOfSection
  签名: {U : Cᵒᵖ} (s : F.obj U)
  定义体: fun _ i hi => ⟨F.map i.op s, hi⟩

Depends on / 依赖: F.map, i.op
-/
def familyOfElementsOfSection {U : Cᵒᵖ} (s : F.obj U) :
    (G.sieveOfSection s).1.FamilyOfElements G.toFunctor := fun _ i hi => ⟨F.map i.op s, hi⟩

/--
theorem `family_of_elements_compatible` / 定理 `family_of_elements_compatible`

English:
theorem family_of_elements_compatible
  given: {U : Cᵒᵖ} (s : F.obj U)
  proof: by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  refine Subtype.ext ?_ -- Porting note: `ext1` does not work here
  change F.map g₁.op (F.map f₁.op s) = F.map g₂.op (F.map f₂.op s)
  rw [← comp_apply]; rw [← Functor.map_comp]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [← op_comp]; rw [e

中文:
定理 family_of_elements_compatible
  条件: {U : Cᵒᵖ} (s : F.obj U)
  证明: by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  refine Subtype.ext ?_ -- Porting note: `ext1` does not work here
  change F.map g₁.op (F.map f₁.op s) = F.map g₂.op (F.map f₂.op s)
  rw [← comp_apply]; rw [← Functor.map_comp]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [← op_comp]; rw [e

Depends on / 依赖: F.map, Functor, Functor.map_comp, Porting, Subtype, Subtype.ext, comp_apply, map_comp, op_comp
-/
theorem family_of_elements_compatible {U : Cᵒᵖ} (s : F.obj U) :
    (G.familyOfElementsOfSection s).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  refine Subtype.ext ?_ -- Porting note: `ext1` does not work here
  change F.map g₁.op (F.map f₁.op s) = F.map g₂.op (F.map f₂.op s)
  rw [← comp_apply]; rw [← Functor.map_comp]; rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [← op_comp]; rw [e]

end CategoryTheory.Subfunctor
