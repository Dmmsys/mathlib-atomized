/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Structured arrow categories on `Comma.map`

We characterize structured arrow categories on arbitrary instances of `Comma.map` as a
comma category itself.
-/

@[expose] public section

namespace CategoryTheory

namespace StructuredArrow

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {T : Type u₃} [Category.{v₃} T] {L : C ⥤ T} {R : D ⥤ T}
  {C' : Type u₄} [Category.{v₄} C'] {D' : Type u₅} [Category.{v₅} D'] {T' : Type u₆}
  [Category.{v₆} T'] {L' : C' ⥤ T'} {R' : D' ⥤ T'} {F₁ : C ⥤ C'} {F₂ : D ⥤ D'} {F : T ⥤ T'}
  (α : F₁ ⋙ L' ⟶ L ⋙ F) (β : R ⋙ F ⟶ F₂ ⋙ R')

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor establishing the equivalence `StructuredArrow.commaMapEquivalence`. -/
@[simps, implicit_reducible]
/--
Definition of `commaMapEquivalenceFunctor` / `commaMapEquivalenceFunctor` 的定义

English:
definition commaMapEquivalenceFunctor
  signature: [IsIso β] (X : Comma L' R')
  body: ⟨mk Y.hom.left, mk Y.hom.right,
    homMk Y.right.hom
      (by simpa only [Functor.const_obj_obj, map₂_obj_left, mk_left, map₂_obj_right, mk_right,
        map₂_obj_hom, mk_hom_eq_self, Category.id_comp, Category.assoc, NatIso.isIso_inv_app,
        Functor.comp_obj, Comma.map_obj_right, Comma.map_

中文:
定义 commaMapEquivalenceFunctor
  签名: [是同构 β] (X : 交换a L' R')
  定义体: ⟨mk Y.hom.left, mk Y.hom.right,
    homMk Y.right.hom
      (by simpa only [Functor.const_obj_obj, map₂_obj_left, mk_left, map₂_obj_right, mk_right,
        map₂_obj_hom, mk_hom_eq_self, Category.id_comp, Category.assoc, NatIso.isIso_inv_app,
        Functor.comp_obj, Comma.map_obj_right, Comma.map_

Depends on / 依赖: CreatesLimitsOfShape, Discrete, Ind.equivalence, ObjectProperty, Y.hom.left, Y.hom.right, equivalence, functor
-/
def commaMapEquivalenceFunctor [IsIso β] (X : Comma L' R') :
    StructuredArrow X (Comma.map α β) ⥤ Comma (map₂ (𝟙 _) α) (map₂ X.hom (inv β)) where
  obj Y := ⟨mk Y.hom.left, mk Y.hom.right,
    homMk Y.right.hom
      (by simpa only [Functor.const_obj_obj, map₂_obj_left, mk_left, map₂_obj_right, mk_right,
        map₂_obj_hom, mk_hom_eq_self, Category.id_comp, Category.assoc, NatIso.isIso_inv_app,
        Functor.comp_obj, Comma.map_obj_right, Comma.map_obj_left, Comma.map_obj_hom,
        IsIso.hom_inv_id, Category.comp_id] using
        congrFun (congrArg CategoryStruct.comp Y.hom.w) (inv (β.app Y.right.right) :))⟩
  map {Y Z} f := ⟨homMk f.right.left (congrArg CommaMorphism.left (StructuredArrow.w f)),
    homMk f.right.right (congrArg CommaMorphism.right (StructuredArrow.w f)),
    by simp only [map₂_obj_right, mk_right, hom_eq_iff, comp_right,
      map₂_map_right, homMk_right, CommaMorphism.w] ⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor establishing the equivalence `StructuredArrow.commaMapEquivalence`. -/
@[simps]
/--
Definition of `commaMapEquivalenceInverse` / `commaMapEquivalenceInverse` 的定义

English:
definition commaMapEquivalenceInverse
  signature: [IsIso β] (X : Comma L' R')
  body: mk (Y := ⟨Y.left.right, Y.right.right, Y.hom.right⟩)
    ⟨by exact Y.left.hom, by exact Y.right.hom, by
      simpa using congrFun (congrArg CategoryStruct.comp (StructuredArrow.w Y.hom))
        (β.app Y.right.right)⟩
  map {Y Z} f := homMk ⟨by exact f.left.right, by exact f.right.right,
    congrA

中文:
定义 commaMapEquivalenceInverse
  签名: [是同构 β] (X : 交换a L' R')
  定义体: mk (Y := ⟨Y.left.right, Y.right.right, Y.hom.right⟩)
    ⟨by exact Y.left.hom, by exact Y.right.hom, by
      simpa using congrFun (congrArg CategoryStruct.comp (StructuredArrow.w Y.hom))
        (β.app Y.right.right)⟩
  map {Y Z} f := homMk ⟨by exact f.left.right, by exact f.right.right,
    congrA

Depends on / 依赖: Ind.inclusion, Y.hom.right, Y.left.right, Y.right.right, hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape, inclusion
-/
def commaMapEquivalenceInverse [IsIso β] (X : Comma L' R') :
    Comma (map₂ (𝟙 _) α) (map₂ X.hom (inv β)) ⥤ StructuredArrow X (Comma.map α β) where
  obj Y := mk (Y := ⟨Y.left.right, Y.right.right, Y.hom.right⟩)
    ⟨by exact Y.left.hom, by exact Y.right.hom, by
      simpa using congrFun (congrArg CategoryStruct.comp (StructuredArrow.w Y.hom))
        (β.app Y.right.right)⟩
  map {Y Z} f := homMk ⟨by exact f.left.right, by exact f.right.right,
    congrArg CommaMorphism.right f.w⟩

set_option backward.defeqAttrib.useBackward true in
/-- The unit establishing the equivalence `StructuredArrow.commaMapEquivalence`. -/
@[simps!]
/--
Definition of `commaMapEquivalenceUnitIso` / `commaMapEquivalenceUnitIso` 的定义

English:
definition commaMapEquivalenceUnitIso
  signature: [IsIso β] (X : Comma L' R')
  body: NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

中文:
定义 commaMapEquivalenceUnitIso
  签名: [是同构 β] (X : 交换a L' R')
  定义体: NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def commaMapEquivalenceUnitIso [IsIso β] (X : Comma L' R') :
    𝟭 (StructuredArrow X (Comma.map α β)) ≅
      commaMapEquivalenceFunctor α β X ⋙ commaMapEquivalenceInverse α β X :=
  NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

set_option backward.defeqAttrib.useBackward true in
/-- The counit functor establishing the equivalence `StructuredArrow.commaMapEquivalence`. -/
@[simps!]
/--
Definition of `commaMapEquivalenceCounitIso` / `commaMapEquivalenceCounitIso` 的定义

English:
definition commaMapEquivalenceCounitIso
  signature: [IsIso β] (X : Comma L' R')
  body: NatIso.ofComponents (fun _ => Comma.isoMk (Iso.refl _) (Iso.refl _))

中文:
定义 commaMapEquivalenceCounitIso
  签名: [是同构 β] (X : 交换a L' R')
  定义体: NatIso.ofComponents (fun _ => Comma.isoMk (Iso.refl _) (Iso.refl _))

Depends on / 依赖: Comma.isoMk, Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def commaMapEquivalenceCounitIso [IsIso β] (X : Comma L' R') :
    commaMapEquivalenceInverse α β X ⋙ commaMapEquivalenceFunctor α β X ≅
      𝟭 (Comma (map₂ (𝟙 (L'.obj X.left)) α) (map₂ X.hom (inv β))) :=
  NatIso.ofComponents (fun _ => Comma.isoMk (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `commaMapEquivalence` / `commaMapEquivalence` 的定义

English:
definition commaMapEquivalence
  signature: [IsIso β] (X : Comma L' R')
  body: commaMapEquivalenceFunctor α β X
  inverse := commaMapEquivalenceInverse α β X
  unitIso := commaMapEquivalenceUnitIso α β X
  counitIso := commaMapEquivalenceCounitIso α β X

中文:
定义 commaMapEquivalence
  签名: [是同构 β] (X : 交换a L' R')
  定义体: commaMapEquivalenceFunctor α β X
  inverse := commaMapEquivalenceInverse α β X
  unitIso := commaMapEquivalenceUnitIso α β X
  counitIso := commaMapEquivalenceCounitIso α β X

Depends on / 依赖: commaMapEquivalenceFunctor
-/
def commaMapEquivalence [IsIso β] (X : Comma L' R') :
    StructuredArrow X (Comma.map α β) ≌ Comma (map₂ (𝟙 _) α) (map₂ X.hom (inv β)) where
  functor := commaMapEquivalenceFunctor α β X
  inverse := commaMapEquivalenceInverse α β X
  unitIso := commaMapEquivalenceUnitIso α β X
  counitIso := commaMapEquivalenceCounitIso α β X

end

end StructuredArrow

end CategoryTheory
