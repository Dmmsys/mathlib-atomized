/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Preservation of zero objects and zero morphisms

We define the class `PreservesZeroMorphisms` and show basic properties.

## Main results

We provide the following results:
* Left adjoints and right adjoints preserve zero morphisms;
* full functors preserve zero morphisms;
* if both categories involved have a zero object, then a functor preserves zero morphisms if and
  only if it preserves the zero object;
* functors which preserve initial or terminal objects preserve zero morphisms.

-/

@[expose] public section


universe v u v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]

section ZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

/--
Definition of `PreservesZeroMorphisms` / `PreservesZeroMorphisms` 的定义

English:
class PreservesZeroMorphisms
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - map_zero : forall X Y : C, F.map (0 : X ⟶ Y) = 0  [default: by aesop]

中文:
类 PreservesZeroMorphisms
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - map_zero : 对任意 X Y : C, F.map (0 : X ⟶ Y) = 0  [默认: by aesop]
-/
class PreservesZeroMorphisms (F : C ⥤ D) : Prop where
  /-- For any pair objects `F (0: X ⟶ Y) = (0 : F X ⟶ F Y)` -/
  map_zero : forall X Y : C, F.map (0 : X ⟶ Y) = 0 := by aesop

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (F : C ⥤ D) [PreservesZeroMorphisms F] (X Y : C)
  proof: PreservesZeroMorphisms.map_zero _ _

中文:
定理 map_zero
  条件: (F : C ⥤ D) [PreservesZeroMorphisms F] (X Y : C)
  证明: PreservesZeroMorphisms.map_zero _ _
-/
protected theorem map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] (X Y : C) :
    F.map (0 : X ⟶ Y) = 0 :=
  PreservesZeroMorphisms.map_zero _ _

/--
lemma `map_isZero` / 引理 `map_isZero`

English:
lemma map_isZero
  given: (F : C ⥤ D) [PreservesZeroMorphisms F] {X : C} (hX : IsZero X)
  proof: by
  simp only [IsZero.iff_id_eq_zero] at hX ⊢
  rw [← F.map_id]; rw [hX]; rw [F.map_zero]

中文:
引理 map_isZero
  条件: (F : C ⥤ D) [PreservesZeroMorphisms F] {X : C} (hX : IsZero X)
  证明: by
  simp only [IsZero.iff_id_eq_zero] at hX ⊢
  rw [← F.map_id]; rw [hX]; rw [F.map_zero]

Depends on / 依赖: F.map_id, F.map_zero, IsZero, IsZero.iff_id_eq_zero, iff_id_eq_zero, map_id, map_zero
-/
lemma map_isZero (F : C ⥤ D) [PreservesZeroMorphisms F] {X : C} (hX : IsZero X) :
    IsZero (F.obj X) := by
  simp only [IsZero.iff_id_eq_zero] at hX ⊢
  rw [← F.map_id]; rw [hX]; rw [F.map_zero]

/--
theorem `zero_of_map_zero` / 定理 `zero_of_map_zero`

English:
theorem zero_of_map_zero
  statement: (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} (f : X ⟶ Y)
  proof: F.map_injective h.trans Eq.symm F.map_zero _ _

中文:
定理 zero_of_map_zero
  结论: (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} (f : X ⟶ Y)
  证明: F.map_injective h.trans Eq.symm F.map_zero _ _

Depends on / 依赖: Eq.symm, F.map_injective, F.map_zero, h.trans, map_injective, map_zero
-/
theorem zero_of_map_zero (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} (f : X ⟶ Y)
    (h : F.map f = 0) : f = 0 :=
F.map_injective h.trans Eq.symm F.map_zero _ _

/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} {f : X ⟶ Y}
  proof: ⟨F.zero_of_map_zero _, by
    rintro rfl
    exact F.map_zero _ _⟩

中文:
定理 map_eq_zero_iff
  条件: (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} {f : X ⟶ Y}
  证明: ⟨F.zero_of_map_zero _, by
    rintro rfl
    exact F.map_zero _ _⟩

Depends on / 依赖: F.map_zero, F.zero_of_map_zero, map_zero, zero_of_map_zero
-/
theorem map_eq_zero_iff (F : C ⥤ D) [PreservesZeroMorphisms F] [Faithful F] {X Y : C} {f : X ⟶ Y} :
    F.map f = 0 ↔ f = 0 :=
  ⟨F.zero_of_map_zero _, by
    rintro rfl
    exact F.map_zero _ _⟩

set_option backward.isDefEq.respectTransparency false in
instance (priority := 100) preservesZeroMorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesZeroMorphisms F where
  map_zero X Y := by
    let adj := Adjunction.ofIsLeftAdjoint F
    calc
      dsimp% F.map (0 : X ⟶ Y) = F.map 0 ≫ F.map (adj.unit.app Y) ≫ adj.counit.app (F.obj Y) := ?_
      _ = F.map 0 ≫ F.map ((rightAdjoint F).map (0 : F.obj X ⟶ _)) ≫ adj.counit.app (F.obj Y) := ?_
      _ = 0 := ?_
    · rw [Adjunction.left_triangle_components]
      exact (Category.comp_id _).symm
    · simp only [← Category.assoc, ← F.map_comp, zero_comp]
    · simp

set_option backward.isDefEq.respectTransparency false in
instance (priority := 100) preservesZeroMorphisms_of_isRightAdjoint (G : C ⥤ D) [IsRightAdjoint G] :
    PreservesZeroMorphisms G where
  map_zero X Y := by
    let adj := Adjunction.ofIsRightAdjoint G
    calc
      G.map (0 : X ⟶ Y) = adj.unit.app (G.obj X) ≫ G.map (adj.counit.app X) ≫ G.map 0 := ?_
      _ = adj.unit.app (G.obj X) ≫ G.map ((leftAdjoint G).map (0 : _ ⟶ G.obj X)) ≫ G.map 0 := ?_
      _ = 0 := ?_
    · rw [Adjunction.right_triangle_components_assoc]
    · simp only [← G.map_comp, comp_zero]
    · simp only [id_obj, Adjunction.unit_naturality_assoc, zero_comp]

instance (priority := 100) preservesZeroMorphisms_of_full (F : C ⥤ D) [Full F] :
    PreservesZeroMorphisms F where
  map_zero X Y :=
    calc
      F.map (0 : X ⟶ Y) = F.map (0 ≫ F.preimage (0 : F.obj Y ⟶ F.obj Y)) := by rw [zero_comp]
      _ = 0 := by rw [F.map_comp, F.map_preimage, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `preservesZeroMorphisms_comp` / 实例 `preservesZeroMorphisms_comp`

English:
instance preservesZeroMorphisms_comp
  signature: (F : C ⥤ D) (G : D ⥤ E)
  body: ⟨by simp⟩

中文:
实例 preservesZeroMorphisms_comp
  签名: (F : C ⥤ D) (G : D ⥤ E)
  定义体: ⟨by simp⟩
-/
instance preservesZeroMorphisms_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    (F ⋙ G).PreservesZeroMorphisms := ⟨by simp⟩

/--
lemma `preservesZeroMorphisms_of_iso` / 引理 `preservesZeroMorphisms_of_iso`

English:
lemma preservesZeroMorphisms_of_iso
  given: {F₁ F₂ : C ⥤ D} [F₁.PreservesZeroMorphisms] (e : F₁ ≅ F₂)
  proof: by simp only [← cancel_epi (e.hom.app X), ← e.hom.naturality,
    F₁.map_zero, zero_comp, comp_zero]

中文:
引理 preservesZeroMorphisms_of_iso
  条件: {F₁ F₂ : C ⥤ D} [F₁.PreservesZeroMorphisms] (e : F₁ ≅ F₂)
  证明: by simp only [← cancel_epi (e.hom.app X), ← e.hom.naturality,
    F₁.map_zero, zero_comp, comp_zero]

Depends on / 依赖: cancel_epi, comp_zero, e.hom.app, e.hom.naturality, map_zero, naturality, zero_comp
-/
lemma preservesZeroMorphisms_of_iso {F₁ F₂ : C ⥤ D} [F₁.PreservesZeroMorphisms] (e : F₁ ≅ F₂) :
    F₂.PreservesZeroMorphisms where
  map_zero X Y := by simp only [← cancel_epi (e.hom.app X), ← e.hom.naturality,
    F₁.map_zero, zero_comp, comp_zero]

/--
Instance `preservesZeroMorphisms_evaluation_obj` / 实例 `preservesZeroMorphisms_evaluation_obj`

English:
instance preservesZeroMorphisms_evaluation_obj
  signature: (j : D)

中文:
实例 preservesZeroMorphisms_evaluation_obj
  签名: (j : D)
-/
instance preservesZeroMorphisms_evaluation_obj (j : D) :
    PreservesZeroMorphisms ((evaluation D C).obj j) where

instance (F : C ⥤ D ⥤ E) [forall X, (F.obj X).PreservesZeroMorphisms] :
    F.flip.PreservesZeroMorphisms where

instance (F : C ⥤ D ⥤ E) [F.PreservesZeroMorphisms] (Y : D) :
    (F.flip.obj Y).PreservesZeroMorphisms where

omit [HasZeroMorphisms C] in
/--
lemma `whiskerRight_zero` / 引理 `whiskerRight_zero`

English:
lemma whiskerRight_zero
  given: {F G : C ⥤ D} (H : D ⥤ E) [H.PreservesZeroMorphisms]
  proof: by cat_disch

omit [HasZeroMorphisms C] in

中文:
引理 whiskerRight_zero
  条件: {F G : C ⥤ D} (H : D ⥤ E) [H.PreservesZeroMorphisms]
  证明: by cat_disch

omit [HasZeroMorphisms C] in
-/
@[simp] lemma whiskerRight_zero {F G : C ⥤ D} (H : D ⥤ E) [H.PreservesZeroMorphisms] :
    whiskerRight (0 : F ⟶ G) H = 0 := by cat_disch

omit [HasZeroMorphisms C] in
/--
lemma `FullyFaithful.preservesZeroMorphisms` / 引理 `FullyFaithful.preservesZeroMorphisms`

English:
lemma FullyFaithful.preservesZeroMorphisms
  given: (F : C ⥤ D) (hF : F.FullyFaithful)
  proof: hF.hasZeroMorphisms
    F.PreservesZeroMorphisms :=
  letI : HasZeroMorphisms C := hF.hasZeroMorphisms
  ⟨fun _ _ => hF.map_preimage _⟩

中文:
引理 FullyFaithful.preservesZeroMorphisms
  条件: (F : C ⥤ D) (hF : F.FullyFaithful)
  证明: hF.hasZeroMorphisms
    F.PreservesZeroMorphisms :=
  letI : HasZeroMorphisms C := hF.hasZeroMorphisms
  ⟨fun _ _ => hF.map_preimage _⟩

Depends on / 依赖: hF.hasZeroMorphisms, hasZeroMorphisms
-/
lemma FullyFaithful.preservesZeroMorphisms (F : C ⥤ D) (hF : F.FullyFaithful) :
    letI : HasZeroMorphisms C := hF.hasZeroMorphisms
    F.PreservesZeroMorphisms :=
  letI : HasZeroMorphisms C := hF.hasZeroMorphisms
  ⟨fun _ _ => hF.map_preimage _⟩

end ZeroMorphisms

section ZeroObject

variable [HasZeroObject C] [HasZeroObject D]

open ZeroObject

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)

/-- A functor that preserves zero morphisms also preserves the zero object. -/
@[simps]
/--
Definition of `mapZeroObject` / `mapZeroObject` 的定义

English:
definition mapZeroObject
  signature: [PreservesZeroMorphisms F]
  body: 0
  inv := 0
  hom_inv_id := by rw [← F.map_id, id_zero, F.map_zero, zero_comp]
  inv_hom_id := by rw [id_zero, comp_zero]

中文:
定义 mapZeroObject
  签名: [PreservesZeroMorphisms F]
  定义体: 0
  inv := 0
  hom_inv_id := by rw [← F.map_id, id_zero, F.map_zero, zero_comp]
  inv_hom_id := by rw [id_zero, comp_zero]
-/
def mapZeroObject [PreservesZeroMorphisms F] : F.obj 0 ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := by rw [← F.map_id, id_zero, F.map_zero, zero_comp]
  inv_hom_id := by rw [id_zero, comp_zero]

variable {F}

/--
theorem `preservesZeroMorphisms_of_map_zero_object` / 定理 `preservesZeroMorphisms_of_map_zero_object`

English:
theorem preservesZeroMorphisms_of_map_zero_object
  given: (i : F.obj 0 ≅ 0)
  statement: PreservesZeroMorphisms F where
  proof: calc
      F.map (0 : X ⟶ Y) = F.map (0 : X ⟶ 0) ≫ F.map 0 := by rw [← Functor.map_comp, comp_zero]
      _ = F.map 0 ≫ (i.hom ≫ i.inv) ≫ F.map 0 := by rw [Iso.hom_inv_id, Category.id_comp]
      _ = 0 := by simp only [zero_of_to_zero i.hom, zero_comp, comp_zero]

中文:
定理 preservesZeroMorphisms_of_map_zero_object
  条件: (i : F.obj 0 ≅ 0)
  结论: PreservesZeroMorphisms F where
  证明: calc
      F.map (0 : X ⟶ Y) = F.map (0 : X ⟶ 0) ≫ F.map 0 := by rw [← Functor.map_comp, comp_zero]
      _ = F.map 0 ≫ (i.hom ≫ i.inv) ≫ F.map 0 := by rw [Iso.hom_inv_id, Category.id_comp]
      _ = 0 := by simp only [zero_of_to_zero i.hom, zero_comp, comp_zero]

Depends on / 依赖: Category, Category.id_comp, F.map, Functor, Functor.map_comp, Iso.hom_inv_id, comp_zero, hom_inv_id, i.hom, i.inv, id_comp, map_comp, zero_comp, zero_of_to_zero
-/
theorem preservesZeroMorphisms_of_map_zero_object (i : F.obj 0 ≅ 0) : PreservesZeroMorphisms F where
  map_zero X Y :=
    calc
      F.map (0 : X ⟶ Y) = F.map (0 : X ⟶ 0) ≫ F.map 0 := by rw [← Functor.map_comp, comp_zero]
      _ = F.map 0 ≫ (i.hom ≫ i.inv) ≫ F.map 0 := by rw [Iso.hom_inv_id, Category.id_comp]
      _ = 0 := by simp only [zero_of_to_zero i.hom, zero_comp, comp_zero]

instance (priority := 100) preservesZeroMorphisms_of_preserves_initial_object
    [PreservesColimit (Functor.empty.{0} C) F] : PreservesZeroMorphisms F :=
preservesZeroMorphisms_of_map_zero_object
    F.mapIso HasZeroObject.zeroIsoInitial ≪≫
      PreservesInitial.iso F ≪≫ HasZeroObject.zeroIsoInitial.symm

instance (priority := 100) preservesZeroMorphisms_of_preserves_terminal_object
    [PreservesLimit (Functor.empty.{0} C) F] : PreservesZeroMorphisms F :=
preservesZeroMorphisms_of_map_zero_object
    F.mapIso HasZeroObject.zeroIsoTerminal ≪≫
      PreservesTerminal.iso F ≪≫ HasZeroObject.zeroIsoTerminal.symm

variable (F)

/--
lemma `preservesTerminalObject_of_preservesZeroMorphisms` / 引理 `preservesTerminalObject_of_preservesZeroMorphisms`

English:
lemma preservesTerminalObject_of_preservesZeroMorphisms
  given: [PreservesZeroMorphisms F]
  proof: preservesTerminal_of_iso F
    F.mapIso HasZeroObject.zeroIsoTerminal.symm ≪≫ mapZeroObject F ≪≫ HasZeroObject.zeroIsoTerminal

中文:
引理 preservesTerminalObject_of_preservesZeroMorphisms
  条件: [PreservesZeroMorphisms F]
  证明: preservesTerminal_of_iso F
    F.mapIso HasZeroObject.zeroIsoTerminal.symm ≪≫ mapZeroObject F ≪≫ HasZeroObject.zeroIsoTerminal

Depends on / 依赖: F.mapIso, HasZeroObject, HasZeroObject.zeroIsoTerminal, HasZeroObject.zeroIsoTerminal.symm, mapIso, mapZeroObject, preservesTerminal_of_iso, zeroIsoTerminal
-/
lemma preservesTerminalObject_of_preservesZeroMorphisms [PreservesZeroMorphisms F] :
    PreservesLimit (Functor.empty.{0} C) F :=
preservesTerminal_of_iso F
    F.mapIso HasZeroObject.zeroIsoTerminal.symm ≪≫ mapZeroObject F ≪≫ HasZeroObject.zeroIsoTerminal

/--
lemma `preservesInitialObject_of_preservesZeroMorphisms` / 引理 `preservesInitialObject_of_preservesZeroMorphisms`

English:
lemma preservesInitialObject_of_preservesZeroMorphisms
  given: [PreservesZeroMorphisms F]
  proof: preservesInitial_of_iso F
    HasZeroObject.zeroIsoInitial.symm ≪≫
      (mapZeroObject F).symm ≪≫ (F.mapIso HasZeroObject.zeroIsoInitial.symm).symm

中文:
引理 preservesInitialObject_of_preservesZeroMorphisms
  条件: [PreservesZeroMorphisms F]
  证明: preservesInitial_of_iso F
    HasZeroObject.zeroIsoInitial.symm ≪≫
      (mapZeroObject F).symm ≪≫ (F.mapIso HasZeroObject.zeroIsoInitial.symm).symm

Depends on / 依赖: F.mapIso, HasZeroObject, HasZeroObject.zeroIsoInitial.symm, mapIso, mapZeroObject, preservesInitial_of_iso, zeroIsoInitial
-/
lemma preservesInitialObject_of_preservesZeroMorphisms [PreservesZeroMorphisms F] :
    PreservesColimit (Functor.empty.{0} C) F :=
preservesInitial_of_iso F
    HasZeroObject.zeroIsoInitial.symm ≪≫
      (mapZeroObject F).symm ≪≫ (F.mapIso HasZeroObject.zeroIsoInitial.symm).symm

end ZeroObject

section

variable [HasZeroObject D] [HasZeroMorphisms D]
  (G : C ⥤ D) (hG : IsZero G) (J : Type*) [Category* J]

include hG

/--
lemma `preservesLimitsOfShape_of_isZero` / 引理 `preservesLimitsOfShape_of_isZero`

English:
lemma preservesLimitsOfShape_of_isZero
  statement: PreservesLimitsOfShape J G where
  proof: ⟨fun _ => ⟨by
    rw [Functor.isZero_iff] at hG
    exact IsLimit.ofIsZero _ ((K ⋙ G).isZero (fun X => hG _)) (hG _)⟩⟩

中文:
引理 preservesLimitsOfShape_of_isZero
  结论: PreservesLimitsOfShape J G where
  证明: ⟨fun _ => ⟨by
    rw [Functor.isZero_iff] at hG
    exact IsLimit.ofIsZero _ ((K ⋙ G).isZero (fun X => hG _)) (hG _)⟩⟩

Depends on / 依赖: Functor, Functor.isZero_iff, IsLimit, IsLimit.ofIsZero, isZero, isZero_iff, ofIsZero
-/
lemma preservesLimitsOfShape_of_isZero : PreservesLimitsOfShape J G where
  preservesLimit {K} := ⟨fun _ => ⟨by
    rw [Functor.isZero_iff] at hG
    exact IsLimit.ofIsZero _ ((K ⋙ G).isZero (fun X => hG _)) (hG _)⟩⟩

/--
lemma `preservesColimitsOfShape_of_isZero` / 引理 `preservesColimitsOfShape_of_isZero`

English:
lemma preservesColimitsOfShape_of_isZero
  statement: PreservesColimitsOfShape J G where
  proof: ⟨fun _ => ⟨by
    rw [Functor.isZero_iff] at hG
    exact IsColimit.ofIsZero _ ((K ⋙ G).isZero (fun X => hG _)) (hG _)⟩⟩

中文:
引理 preservesColimitsOfShape_of_isZero
  结论: PreservesColimitsOfShape J G where
  证明: ⟨fun _ => ⟨by
    rw [Functor.isZero_iff] at hG
    exact IsColimit.ofIsZero _ ((K ⋙ G).isZero (fun X => hG _)) (hG _)⟩⟩

Depends on / 依赖: Functor, Functor.isZero_iff, IsColimit, IsColimit.ofIsZero, isZero, isZero_iff, ofIsZero
-/
lemma preservesColimitsOfShape_of_isZero : PreservesColimitsOfShape J G where
  preservesColimit {K} := ⟨fun _ => ⟨by
    rw [Functor.isZero_iff] at hG
    exact IsColimit.ofIsZero _ ((K ⋙ G).isZero (fun X => hG _)) (hG _)⟩⟩

/--
lemma `preservesLimitsOfSize_of_isZero` / 引理 `preservesLimitsOfSize_of_isZero`

English:
lemma preservesLimitsOfSize_of_isZero
  statement: PreservesLimitsOfSize.{v, u} G where
  proof: G.preservesLimitsOfShape_of_isZero hG _

中文:
引理 preservesLimitsOfSize_of_isZero
  结论: PreservesLimitsOfSize.{v, u} G where
  证明: G.preservesLimitsOfShape_of_isZero hG _

Depends on / 依赖: G.preservesLimitsOfShape_of_isZero, preservesLimitsOfShape_of_isZero
-/
lemma preservesLimitsOfSize_of_isZero : PreservesLimitsOfSize.{v, u} G where
  preservesLimitsOfShape := G.preservesLimitsOfShape_of_isZero hG _

/--
lemma `preservesColimitsOfSize_of_isZero` / 引理 `preservesColimitsOfSize_of_isZero`

English:
lemma preservesColimitsOfSize_of_isZero
  statement: PreservesColimitsOfSize.{v, u} G where
  proof: G.preservesColimitsOfShape_of_isZero hG _

中文:
引理 preservesColimitsOfSize_of_isZero
  结论: PreservesColimitsOfSize.{v, u} G where
  证明: G.preservesColimitsOfShape_of_isZero hG _

Depends on / 依赖: G.preservesColimitsOfShape_of_isZero, preservesColimitsOfShape_of_isZero
-/
lemma preservesColimitsOfSize_of_isZero : PreservesColimitsOfSize.{v, u} G where
  preservesColimitsOfShape := G.preservesColimitsOfShape_of_isZero hG _

end

end CategoryTheory.Functor
