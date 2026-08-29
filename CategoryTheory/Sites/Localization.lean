/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Bousfield
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The sheaf category as a localized category

In this file, it is shown that the category of sheaves `Sheaf J A` is a localization
of the category `Presheaf J A` with respect to the class `J.W` of morphisms
of presheaves which become isomorphisms after applying the sheafification functor.

-/

universe w

public section

namespace CategoryTheory

open Localization

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {A : Type*} [Category* A]

namespace GrothendieckTopology

/--
Definition of `W` / `W` 的定义

English:
abbreviation W
  signature: : MorphismProperty (Cᵒᵖ ⥤ A)
  body: ObjectProperty.isLocal (Presheaf.IsSheaf J)

中文:
缩写 W
  签名: : MorphismProperty (Cᵒᵖ ⥤ A)
  定义体: ObjectProperty.isLocal (Presheaf.IsSheaf J)

Depends on / 依赖: IsSheaf, ObjectProperty, ObjectProperty.isLocal, Presheaf, Presheaf.IsSheaf, isLocal
-/
abbrev W : MorphismProperty (Cᵒᵖ ⥤ A) := ObjectProperty.isLocal (Presheaf.IsSheaf J)

variable (A) in
/--
lemma `W_eq_isLocal_range_sheafToPresheaf_obj` / 引理 `W_eq_isLocal_range_sheafToPresheaf_obj`

English:
lemma W_eq_isLocal_range_sheafToPresheaf_obj
  proof: by
  apply congr_arg
  ext P
  constructor
  · intro hP
    exact ⟨⟨P, hP⟩, rfl⟩
  · rintro ⟨F, rfl⟩
    exact F.property

中文:
引理 W_eq_isLocal_range_sheafToPresheaf_obj
  证明: by
  apply congr_arg
  ext P
  constructor
  · intro hP
    exact ⟨⟨P, hP⟩, rfl⟩
  · rintro ⟨F, rfl⟩
    exact F.property

Depends on / 依赖: F.property, congr_arg, property
-/
lemma W_eq_isLocal_range_sheafToPresheaf_obj :
    J.W = ObjectProperty.isLocal (· in Set.range (sheafToPresheaf J A).obj) := by
  apply congr_arg
  ext P
  constructor
  · intro hP
    exact ⟨⟨P, hP⟩, rfl⟩
  · rintro ⟨F, rfl⟩
    exact F.property

/--
lemma `W_sheafToPresheaf_map_iff_isIso` / 引理 `W_sheafToPresheaf_map_iff_isIso`

English:
lemma W_sheafToPresheaf_map_iff_isIso
  given: {F₁ F₂ : Sheaf J A} (φ : F₁ ⟶ F₂)
  proof: by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]; rw [ObjectProperty.isLocal_iff_isIso _ _ ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]; rw [isIso_iff_of_reflects_iso]

中文:
引理 W_sheafToPresheaf_map_iff_isIso
  条件: {F₁ F₂ : 层 J A} (φ : F₁ ⟶ F₂)
  证明: by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]; rw [ObjectProperty.isLocal_iff_isIso _ _ ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]; rw [isIso_iff_of_reflects_iso]

Depends on / 依赖: ObjectProperty, ObjectProperty.isLocal_iff_isIso, W_eq_isLocal_range_sheafToPresheaf_obj, isIso_iff_of_reflects_iso, isLocal_iff_isIso
-/
lemma W_sheafToPresheaf_map_iff_isIso {F₁ F₂ : Sheaf J A} (φ : F₁ ⟶ F₂) :
    J.W ((sheafToPresheaf J A).map φ) ↔ IsIso φ := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]; rw [ObjectProperty.isLocal_iff_isIso _ _ ⟨_]; rw [rfl⟩ ⟨_]; rw [rfl⟩]; rw [isIso_iff_of_reflects_iso]

section Adjunction

variable {G : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A}

/--
lemma `W_adj_unit_app` / 引理 `W_adj_unit_app`

English:
lemma W_adj_unit_app
  given: (adj : G ⊣ sheafToPresheaf J A) (P : Cᵒᵖ ⥤ A)
  statement: J.W (adj.unit.app P)
  proof: by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]
  exact ObjectProperty.isLocal_adj_unit_app adj P

中文:
引理 W_adj_unit_app
  条件: (adj : G ⊣ sheafToPresheaf J A) (P : Cᵒᵖ ⥤ A)
  结论: J.W (adj.unit.app P)
  证明: by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]
  exact ObjectProperty.isLocal_adj_unit_app adj P

Depends on / 依赖: ObjectProperty, ObjectProperty.isLocal_adj_unit_app, W_eq_isLocal_range_sheafToPresheaf_obj, isLocal_adj_unit_app
-/
lemma W_adj_unit_app (adj : G ⊣ sheafToPresheaf J A) (P : Cᵒᵖ ⥤ A) : J.W (adj.unit.app P) := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]
  exact ObjectProperty.isLocal_adj_unit_app adj P

/--
lemma `W_iff_isIso_map_of_adjunction` / 引理 `W_iff_isIso_map_of_adjunction`

English:
lemma W_iff_isIso_map_of_adjunction
  statement: (adj : G ⊣ sheafToPresheaf J A)
  proof: by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]
  exact ObjectProperty.isLocal_iff_isIso_map adj f

中文:
引理 W_iff_isIso_map_of_adjunction
  结论: (adj : G ⊣ sheafToPresheaf J A)
  证明: by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]
  exact ObjectProperty.isLocal_iff_isIso_map adj f

Depends on / 依赖: ObjectProperty, ObjectProperty.isLocal_iff_isIso_map, W_eq_isLocal_range_sheafToPresheaf_obj, isLocal_iff_isIso_map
-/
lemma W_iff_isIso_map_of_adjunction (adj : G ⊣ sheafToPresheaf J A)
    {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) :
    J.W f ↔ IsIso (G.map f) := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]
  exact ObjectProperty.isLocal_iff_isIso_map adj f

/--
lemma `W_eq_inverseImage_isomorphisms_of_adjunction` / 引理 `W_eq_inverseImage_isomorphisms_of_adjunction`

English:
lemma W_eq_inverseImage_isomorphisms_of_adjunction
  given: (adj : G ⊣ sheafToPresheaf J A)
  proof: by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]; rw [ObjectProperty.isLocal_eq_inverseImage_isomorphisms adj]

中文:
引理 W_eq_inverseImage_isomorphisms_of_adjunction
  条件: (adj : G ⊣ sheafToPresheaf J A)
  证明: by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]; rw [ObjectProperty.isLocal_eq_inverseImage_isomorphisms adj]

Depends on / 依赖: ObjectProperty, ObjectProperty.isLocal_eq_inverseImage_isomorphisms, W_eq_isLocal_range_sheafToPresheaf_obj, isLocal_eq_inverseImage_isomorphisms
-/
lemma W_eq_inverseImage_isomorphisms_of_adjunction (adj : G ⊣ sheafToPresheaf J A) :
    J.W = (MorphismProperty.isomorphisms _).inverseImage G := by
  rw [W_eq_isLocal_range_sheafToPresheaf_obj]; rw [ObjectProperty.isLocal_eq_inverseImage_isomorphisms adj]

end Adjunction

section HasWeakSheafify

variable [HasWeakSheafify J A]

/--
lemma `W_toSheafify` / 引理 `W_toSheafify`

English:
lemma W_toSheafify
  given: (P : Cᵒᵖ ⥤ A)
  statement: J.W (toSheafify J P)
  proof: J.W_adj_unit_app (sheafificationAdjunction J A) P

中文:
引理 W_toSheafify
  条件: (P : Cᵒᵖ ⥤ A)
  结论: J.W (toSheafify J P)
  证明: J.W_adj_unit_app (sheafificationAdjunction J A) P

Depends on / 依赖: J.W_adj_unit_app, W_adj_unit_app, sheafificationAdjunction
-/
lemma W_toSheafify (P : Cᵒᵖ ⥤ A) : J.W (toSheafify J P) :=
  J.W_adj_unit_app (sheafificationAdjunction J A) P

/--
lemma `W_iff` / 引理 `W_iff`

English:
lemma W_iff
  given: {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂)
  proof: J.W_iff_isIso_map_of_adjunction (sheafificationAdjunction J A) f

中文:
引理 W_iff
  条件: {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂)
  证明: J.W_iff_isIso_map_of_adjunction (sheafificationAdjunction J A) f

Depends on / 依赖: J.W_iff_isIso_map_of_adjunction, W_iff_isIso_map_of_adjunction, sheafificationAdjunction
-/
lemma W_iff {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) :
    J.W f ↔ IsIso ((presheafToSheaf J A).map f) :=
  J.W_iff_isIso_map_of_adjunction (sheafificationAdjunction J A) f

variable (A) in
/--
lemma `W_eq_inverseImage_isomorphisms` / 引理 `W_eq_inverseImage_isomorphisms`

English:
lemma W_eq_inverseImage_isomorphisms
  proof: J.W_eq_inverseImage_isomorphisms_of_adjunction (sheafificationAdjunction J A)

中文:
引理 W_eq_inverseImage_isomorphisms
  证明: J.W_eq_inverseImage_isomorphisms_of_adjunction (sheafificationAdjunction J A)

Depends on / 依赖: J.W_eq_inverseImage_isomorphisms_of_adjunction, W_eq_inverseImage_isomorphisms_of_adjunction, sheafificationAdjunction
-/
lemma W_eq_inverseImage_isomorphisms :
    J.W = (MorphismProperty.isomorphisms _).inverseImage (presheafToSheaf J A) :=
  J.W_eq_inverseImage_isomorphisms_of_adjunction (sheafificationAdjunction J A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (presheafToSheaf J A).IsLocalization J.W
  body: by
  rw [W_eq_inverseImage_isomorphisms]
  exact (sheafificationAdjunction J A).isLocalization

中文:
实例 :
  签名: (presheafToSheaf J A).是Localization J.W
  定义体: by
  rw [W_eq_inverseImage_isomorphisms]
  exact (sheafificationAdjunction J A).isLocalization

Depends on / 依赖: W_eq_inverseImage_isomorphisms, isLocalization, sheafificationAdjunction
-/
instance : (presheafToSheaf J A).IsLocalization J.W := by
  rw [W_eq_inverseImage_isomorphisms]
  exact (sheafificationAdjunction J A).isLocalization

end HasWeakSheafify

end GrothendieckTopology

/--
lemma `Sieve.W_shrinkFunctor_ι_of_mem` / 引理 `Sieve.W_shrinkFunctor_ι_of_mem`

English:
lemma Sieve.W_shrinkFunctor_ι_of_mem
  given: [LocallySmall.{w} C] {X : C} (S : Sieve X) (hS : S in J X)
  proof: by
  intro Z hZ
  rw [isSheaf_iff_isSheaf_of_type] at hZ
  rw [← Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
  exact hZ _ hS

中文:
引理 筛.W_shrinkFunctor_ι_of_mem
  条件: [LocallySmall.{w} C] {X : C} (S : 筛 X) (hS : S in J X)
  证明: by
  intro Z hZ
  rw [isSheaf_iff_isSheaf_of_type] at hZ
  rw [← Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
  exact hZ _ hS

Depends on / 依赖: Presieve, Presieve.isSheafFor_iff_bijective_shrinkFunctor_, isSheaf_iff_isSheaf_of_type
-/
lemma Sieve.W_shrinkFunctor_ι_of_mem [LocallySmall.{w} C] {X : C} (S : Sieve X) (hS : S in J X) :
    J.W (Sieve.shrinkFunctor.{w} S).ι := by
  intro Z hZ
  rw [isSheaf_iff_isSheaf_of_type] at hZ
  rw [← Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
  exact hZ _ hS

variable {D : Type*} [Category* D] {K : GrothendieckTopology D}

/--
lemma `Presieve.IsSheaf.comp_of_W_map_of_adjunction` / 引理 `Presieve.IsSheaf.comp_of_W_map_of_adjunction`

English:
lemma Presieve.IsSheaf.comp_of_W_map_of_adjunction
  proof: by
  intro X S hS
  rw [Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]; rw [← Functor.whiskeringLeft_obj_obj]; rw [← adj.map_comp_bijective_iff]
  refine h hS _ ?_
  rwa [isSheaf_iff_isSheaf_of_type]

中文:
引理 Presieve.是层.comp_of_W_map_of_adjunction
  证明: by
  intro X S hS
  rw [Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]; rw [← Functor.whiskeringLeft_obj_obj]; rw [← adj.map_comp_bijective_iff]
  refine h hS _ ?_
  rwa [isSheaf_iff_isSheaf_of_type]

Depends on / 依赖: Functor, Functor.whiskeringLeft_obj_obj, Presieve, Presieve.isSheafFor_iff_bijective_shrinkFunctor_, adj.map_comp_bijective_iff, isSheaf_iff_isSheaf_of_type, map_comp_bijective_iff, whiskeringLeft_obj_obj
-/
lemma Presieve.IsSheaf.comp_of_W_map_of_adjunction
    [LocallySmall.{w} C] {F : C ⥤ D} {H : (Cᵒᵖ ⥤ Type w) ⥤ (Dᵒᵖ ⥤ Type w)}
    (adj : H ⊣ (Functor.whiskeringLeft _ _ _).obj F.op)
    (h : forall ⦃X : C⦄ ⦃S : Sieve X⦄, S in J X -> K.W (H.map <| (Sieve.shrinkFunctor.{w} S).ι))
    (G : Dᵒᵖ ⥤ Type w) (hG : Presieve.IsSheaf K G) :
    Presieve.IsSheaf J (F.op ⋙ G) := by
  intro X S hS
  rw [Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]; rw [← Functor.whiskeringLeft_obj_obj]; rw [← adj.map_comp_bijective_iff]
  refine h hS _ ?_
  rwa [isSheaf_iff_isSheaf_of_type]

end CategoryTheory
