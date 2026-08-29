/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.GuitartExact.Basic

/-!
# Vertical composition of Guitart exact squares

In this file, we show that the vertical composition of Guitart exact squares
is Guitart exact.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]

namespace TwoSquare

section WhiskerVertical

variable {T : C₁ ⥤ D₁} {L : C₁ ⥤ C₂} {R : D₁ ⥤ D₂} {B : C₂ ⥤ D₂} (w : TwoSquare T L R B)
  {L' : C₁ ⥤ C₂} {R' : D₁ ⥤ D₂}

/-- Given `w : TwoSquare T L R B`, one may obtain a 2-square `TwoSquare T L' R' B` if we
provide natural transformations `α : L ⟶ L'` and `β : R' ⟶ R`. -/
@[simps!]
/--
Definition of `whiskerVertical` / `whiskerVertical` 的定义

English:
definition whiskerVertical
  signature: (α : L ⟶ L') (β : R' ⟶ R)
  body: (w.whiskerLeft α).whiskerRight β

中文:
定义 whiskerVertical
  签名: (α : L ⟶ L') (β : R' ⟶ R)
  定义体: (w.whiskerLeft α).whiskerRight β

Depends on / 依赖: w.whiskerLeft, whiskerLeft, whiskerRight
-/
def whiskerVertical (α : L ⟶ L') (β : R' ⟶ R) :
    TwoSquare T L' R' B :=
  (w.whiskerLeft α).whiskerRight β

namespace GuitartExact

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `whiskerVertical` / 引理 `whiskerVertical`

English:
lemma whiskerVertical
  given: [w.GuitartExact] (α : L ≅ L') (β : R ≅ R')
  proof: by
  rw [guitartExact_iff_initial]
  intro X₂
  let e : structuredArrowDownwards (w.whiskerVertical α.hom β.inv) X₂ ≅
      w.structuredArrowDownwards X₂ ⋙ (StructuredArrow.mapIso (β.app X₂)).functor :=
    NatIso.ofComponents (fun f => StructuredArrow.isoMk (α.symm.app f.right) (by
      dsimp
    

中文:
引理 whiskerVertical
  条件: [w.GuitartExact] (α : L ≅ L') (β : R ≅ R')
  证明: by
  rw [guitartExact_iff_initial]
  intro X₂
  let e : structuredArrowDownwards (w.whiskerVertical α.hom β.inv) X₂ ≅
      w.structuredArrowDownwards X₂ ⋙ (StructuredArrow.mapIso (β.app X₂)).functor :=
    NatIso.ofComponents (fun f => StructuredArrow.isoMk (α.symm.app f.right) (by
      dsimp
    

Depends on / 依赖: B.map_comp, B.map_id, Functor, Functor.initial_natIso_iff, Iso.hom_inv_id_app, NatIso, NatIso.ofComponents, NatTrans, NatTrans.naturality_assoc, StructuredArrow, StructuredArrow.isoMk, StructuredArrow.mapIso, comp_id, f.right, functor, guitartExact_iff_initial, hom_inv_id_app, infer_instance, initial_natIso_iff, mapIso
-/
lemma whiskerVertical [w.GuitartExact] (α : L ≅ L') (β : R ≅ R') :
    (w.whiskerVertical α.hom β.inv).GuitartExact := by
  rw [guitartExact_iff_initial]
  intro X₂
  let e : structuredArrowDownwards (w.whiskerVertical α.hom β.inv) X₂ ≅
      w.structuredArrowDownwards X₂ ⋙ (StructuredArrow.mapIso (β.app X₂)).functor :=
    NatIso.ofComponents (fun f => StructuredArrow.isoMk (α.symm.app f.right) (by
      dsimp
      simp only [NatTrans.naturality_assoc, assoc, ← B.map_comp,
        Iso.hom_inv_id_app, B.map_id, comp_id]))
  rw [Functor.initial_natIso_iff e]
  infer_instance

/-- A 2-square is Guitart exact iff it is so after replacing the left and right functors by
isomorphic functors. -/
@[simp]
/--
lemma `whiskerVertical_iff` / 引理 `whiskerVertical_iff`

English:
lemma whiskerVertical_iff
  given: (α : L ≅ L') (β : R ≅ R')
  proof: by
  constructor
  · intro h
    have : w = (w.whiskerVertical α.hom β.inv).whiskerVertical α.inv β.hom := by
      ext X₁
      simp only [Functor.comp_obj, whiskerVertical_app, assoc, Iso.hom_inv_id_app_assoc,
        ← B.map_comp, Iso.hom_inv_id_app, B.map_id, comp_id]
    rw [this]
    exact whi

中文:
引理 whiskerVertical_iff
  条件: (α : L ≅ L') (β : R ≅ R')
  证明: by
  constructor
  · intro h
    have : w = (w.whiskerVertical α.hom β.inv).whiskerVertical α.inv β.hom := by
      ext X₁
      simp only [Functor.comp_obj, whiskerVertical_app, assoc, Iso.hom_inv_id_app_assoc,
        ← B.map_comp, Iso.hom_inv_id_app, B.map_id, comp_id]
    rw [this]
    exact whi

Depends on / 依赖: B.map_comp, B.map_id, Functor, Functor.comp_obj, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, comp_id, comp_obj, hom_inv_id_app, hom_inv_id_app_assoc, map_comp, map_id, w.whiskerVertical, whiskerVertical, whiskerVertical_app
-/
lemma whiskerVertical_iff (α : L ≅ L') (β : R ≅ R') :
    (w.whiskerVertical α.hom β.inv).GuitartExact ↔ w.GuitartExact := by
  constructor
  · intro h
    have : w = (w.whiskerVertical α.hom β.inv).whiskerVertical α.inv β.hom := by
      ext X₁
      simp only [Functor.comp_obj, whiskerVertical_app, assoc, Iso.hom_inv_id_app_assoc,
        ← B.map_comp, Iso.hom_inv_id_app, B.map_id, comp_id]
    rw [this]
    exact whiskerVertical (w.whiskerVertical α.hom β.inv) α.symm β.symm
  · intro h
    exact whiskerVertical w α β

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [w.GuitartExact]
  signature: (α : L ⟶ L') (β : R' ⟶ R)
  body: whiskerVertical w (asIso α) (asIso β).symm

中文:
实例 [w.GuitartExact]
  签名: (α : L ⟶ L') (β : R' ⟶ R)
  定义体: whiskerVertical w (asIso α) (asIso β).symm

Depends on / 依赖: whiskerVertical
-/
instance [w.GuitartExact] (α : L ⟶ L') (β : R' ⟶ R)
    [IsIso α] [IsIso β] : (w.whiskerVertical α β).GuitartExact :=
  whiskerVertical w (asIso α) (asIso β).symm

end GuitartExact

end WhiskerVertical

section VerticalComposition

variable {H₁ : C₁ ⥤ D₁} {L₁ : C₁ ⥤ C₂} {R₁ : D₁ ⥤ D₂} {H₂ : C₂ ⥤ D₂}
  (w : TwoSquare H₁ L₁ R₁ H₂)
  {L₂ : C₂ ⥤ C₃} {R₂ : D₂ ⥤ D₃} {H₃ : C₃ ⥤ D₃}
  (w' : TwoSquare H₂ L₂ R₂ H₃)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `structuredArrowDownwardsComp` / `structuredArrowDownwardsComp` 的定义

English:
definition structuredArrowDownwardsComp
  signature: (Y₁ : D₁)
  body: NatIso.ofComponents (fun _ => StructuredArrow.isoMk (Iso.refl _))

中文:
定义 structuredArrowDownwardsComp
  签名: (Y₁ : D₁)
  定义体: NatIso.ofComponents (fun _ => StructuredArrow.isoMk (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, StructuredArrow, StructuredArrow.isoMk, ofComponents
-/
def structuredArrowDownwardsComp (Y₁ : D₁) :
    w.structuredArrowDownwards Y₁ ⋙ w'.structuredArrowDownwards (R₁.obj Y₁) ≅
      (w ≫ᵥ w').structuredArrowDownwards Y₁ :=
  NatIso.ofComponents (fun _ => StructuredArrow.isoMk (Iso.refl _))

/-- The vertical composition of 2-squares. (Variant where we allow the replacement of
the vertical compositions by isomorphic functors.) -/
@[simps!]
/--
Definition of `vComp'` / `vComp'` 的定义

English:
definition vComp'
  signature: {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂)
  body: (w ≫ᵥ w').whiskerVertical eL.hom eR.inv

中文:
定义 vComp'
  签名: {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂)
  定义体: (w ≫ᵥ w').whiskerVertical eL.hom eR.inv

Depends on / 依赖: eL.hom, eR.inv, whiskerVertical
-/
def vComp' {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂)
    (eR : R₁ ⋙ R₂ ≅ R₁₂) : TwoSquare H₁ L₁₂ R₁₂ H₃ :=
  (w ≫ᵥ w').whiskerVertical eL.hom eR.inv

namespace GuitartExact

/--
Instance `vComp` / 实例 `vComp`

English:
instance vComp
  signature: [hw : w.GuitartExact] [hw' : w'.GuitartExact]
  body: by
  simp only [TwoSquare.guitartExact_iff_initial]
  intro Y₁
  rw [← Functor.initial_natIso_iff (structuredArrowDownwardsComp w w' Y₁)]
  infer_instance

中文:
实例 vComp
  签名: [hw : w.GuitartExact] [hw' : w'.GuitartExact]
  定义体: by
  simp only [TwoSquare.guitartExact_iff_initial]
  intro Y₁
  rw [← Functor.initial_natIso_iff (structuredArrowDownwardsComp w w' Y₁)]
  infer_instance

Depends on / 依赖: Functor, Functor.initial_natIso_iff, TwoSquare, TwoSquare.guitartExact_iff_initial, guitartExact_iff_initial, infer_instance, initial_natIso_iff, structuredArrowDownwardsComp
-/
instance vComp [hw : w.GuitartExact] [hw' : w'.GuitartExact] :
    (w ≫ᵥ w').GuitartExact := by
  simp only [TwoSquare.guitartExact_iff_initial]
  intro Y₁
  rw [← Functor.initial_natIso_iff (structuredArrowDownwardsComp w w' Y₁)]
  infer_instance

/--
Instance `vComp'` / 实例 `vComp'`

English:
instance vComp'
  signature: [GuitartExact w] [GuitartExact w'] {L₁₂ : C₁ ⥤ C₃}
  body: by
  dsimp only [TwoSquare.vComp']
  infer_instance

中文:
实例 vComp'
  签名: [GuitartExact w] [GuitartExact w'] {L₁₂ : C₁ ⥤ C₃}
  定义体: by
  dsimp only [TwoSquare.vComp']
  infer_instance

Depends on / 依赖: TwoSquare, TwoSquare.vComp, infer_instance
-/
instance vComp' [GuitartExact w] [GuitartExact w'] {L₁₂ : C₁ ⥤ C₃}
    {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂)
    (eR : R₁ ⋙ R₂ ≅ R₁₂) : (w.vComp' w' eL eR).GuitartExact := by
  dsimp only [TwoSquare.vComp']
  infer_instance

/--
lemma `of_vComp` / 引理 `of_vComp`

English:
lemma of_vComp
  given: [R₁.EssSurj] [w.GuitartExact] [(w ≫ᵥ w').GuitartExact]
  proof: by
  rw [guitartExact_iff_initial]
  intro Y₂
  rw [structuredArrowDownwards_initial_iff_of_iso _ (R₁.objObjPreimageIso Y₂).symm]
  have := Functor.initial_of_natIso (structuredArrowDownwardsComp w w' (R₁.objPreimage Y₂)).symm
  exact Functor.initial_of_initial_comp (w.structuredArrowDownwards (R₁.o

中文:
引理 of_vComp
  条件: [R₁.本质满射] [w.GuitartExact] [(w ≫ᵥ w').GuitartExact]
  证明: by
  rw [guitartExact_iff_initial]
  intro Y₂
  rw [structuredArrowDownwards_initial_iff_of_iso _ (R₁.objObjPreimageIso Y₂).symm]
  have := Functor.initial_of_natIso (structuredArrowDownwardsComp w w' (R₁.objPreimage Y₂)).symm
  exact Functor.initial_of_initial_comp (w.structuredArrowDownwards (R₁.o

Depends on / 依赖: Functor, Functor.initial_of_initial_comp, Functor.initial_of_natIso, guitartExact_iff_initial, initial_of_initial_comp, initial_of_natIso, objObjPreimageIso, objPreimage, structuredArrowDownwards, structuredArrowDownwardsComp, structuredArrowDownwards_initial_iff_of_iso, w.structuredArrowDownwards
-/
lemma of_vComp [R₁.EssSurj] [w.GuitartExact] [(w ≫ᵥ w').GuitartExact] :
    w'.GuitartExact := by
  rw [guitartExact_iff_initial]
  intro Y₂
  rw [structuredArrowDownwards_initial_iff_of_iso _ (R₁.objObjPreimageIso Y₂).symm]
  have := Functor.initial_of_natIso (structuredArrowDownwardsComp w w' (R₁.objPreimage Y₂)).symm
  exact Functor.initial_of_initial_comp (w.structuredArrowDownwards (R₁.objPreimage Y₂)) _

/--
lemma `of_vComp'` / 引理 `of_vComp'`

English:
lemma of_vComp'
  statement: {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂) (eR : R₁ ⋙ R₂ ≅ R₁₂)
  proof: by
  dsimp [TwoSquare.vComp'] at h
  rw [whiskerVertical_iff] at h
  exact of_vComp w w'

中文:
引理 of_vComp'
  结论: {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂) (eR : R₁ ⋙ R₂ ≅ R₁₂)
  证明: by
  dsimp [TwoSquare.vComp'] at h
  rw [whiskerVertical_iff] at h
  exact of_vComp w w'

Depends on / 依赖: TwoSquare, TwoSquare.vComp, of_vComp, whiskerVertical_iff
-/
lemma of_vComp' {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂) (eR : R₁ ⋙ R₂ ≅ R₁₂)
    [R₁.EssSurj] [w.GuitartExact] [h : (w.vComp' w' eL eR).GuitartExact] :
    w'.GuitartExact := by
  dsimp [TwoSquare.vComp'] at h
  rw [whiskerVertical_iff] at h
  exact of_vComp w w'

/--
lemma `vComp_iff_of_essSurj` / 引理 `vComp_iff_of_essSurj`

English:
lemma vComp_iff_of_essSurj
  given: [R₁.EssSurj] [w.GuitartExact]
  proof: ⟨fun _ => of_vComp w w', fun _ => inferInstance⟩

中文:
引理 vComp_iff_of_essSurj
  条件: [R₁.本质满射] [w.GuitartExact]
  证明: ⟨fun _ => of_vComp w w', fun _ => inferInstance⟩

Depends on / 依赖: of_vComp
-/
lemma vComp_iff_of_essSurj [R₁.EssSurj] [w.GuitartExact] :
    (w ≫ᵥ w').GuitartExact ↔ w'.GuitartExact :=
  ⟨fun _ => of_vComp w w', fun _ => inferInstance⟩

/--
lemma `vComp'_iff_of_essSurj` / 引理 `vComp'_iff_of_essSurj`

English:
lemma vComp'_iff_of_essSurj
  proof: ⟨fun _ => of_vComp' w w' eL eR, fun _ => inferInstance⟩

中文:
引理 vComp'_iff_of_essSurj
  证明: ⟨fun _ => of_vComp' w w' eL eR, fun _ => inferInstance⟩
-/
lemma vComp'_iff_of_essSurj
    {L₁₂ : C₁ ⥤ C₃} {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ L₂ ≅ L₁₂) (eR : R₁ ⋙ R₂ ≅ R₁₂)
    [R₁.EssSurj] [w.GuitartExact] :
    (w.vComp' w' eL eR).GuitartExact ↔ w'.GuitartExact :=
  ⟨fun _ => of_vComp' w w' eL eR, fun _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `vComp_iff_of_equivalences` / 引理 `vComp_iff_of_equivalences`

English:
lemma vComp_iff_of_equivalences
  statement: (eL : C₂ ≌ C₃) (eR : D₂ ≌ D₃)
  proof: by
  constructor
  · intro hww'
    let : CatCommSq H₂ eL.functor eR.functor H₃ := ⟨w'⟩
    have hw' : CatCommSq.iso H₂ eL.functor eR.functor H₃ = w' := rfl
    let : CatCommSq H₃ eL.inverse eR.inverse H₂ := CatCommSq.vInvEquiv _ _ _ _ inferInstance
    let w'' := CatCommSq.iso H₃ eL.inverse eR.inve

中文:
引理 vComp_iff_of_equivalences
  结论: (eL : C₂ ≌ C₃) (eR : D₂ ≌ D₃)
  证明: by
  constructor
  · intro hww'
    let : CatCommSq H₂ eL.functor eR.functor H₃ := ⟨w'⟩
    have hw' : CatCommSq.iso H₂ eL.functor eR.functor H₃ = w' := rfl
    let : CatCommSq H₃ eL.inverse eR.inverse H₂ := CatCommSq.vInvEquiv _ _ _ _ inferInstance
    let w'' := CatCommSq.iso H₃ eL.inverse eR.inve

Depends on / 依赖: CatCommSq, CatCommSq.iso, CatCommSq.vInvEquiv, Functor, Functor.associator, Functor.isoWhiskerLeft, associator, eL.functor, eL.inverse, eL.unitIso.symm, eR.functor, eR.inverse, functor, inverse, isoWhiskerLeft, rightUnitor, unitIso, vInvEquiv
-/
lemma vComp_iff_of_equivalences (eL : C₂ ≌ C₃) (eR : D₂ ≌ D₃)
    (w' : H₂ ⋙ eR.functor ≅ eL.functor ⋙ H₃) :
    (w ≫ᵥ w'.hom).GuitartExact ↔ w.GuitartExact := by
  constructor
  · intro hww'
    let : CatCommSq H₂ eL.functor eR.functor H₃ := ⟨w'⟩
    have hw' : CatCommSq.iso H₂ eL.functor eR.functor H₃ = w' := rfl
    let : CatCommSq H₃ eL.inverse eR.inverse H₂ := CatCommSq.vInvEquiv _ _ _ _ inferInstance
    let w'' := CatCommSq.iso H₃ eL.inverse eR.inverse H₂
    let α : (L₁ ⋙ eL.functor) ⋙ eL.inverse ≅ L₁ :=
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L₁ eL.unitIso.symm ≪≫ L₁.rightUnitor
    let β : (R₁ ⋙ eR.functor) ⋙ eR.inverse ≅ R₁ :=
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R₁ eR.unitIso.symm ≪≫ R₁.rightUnitor
    have : w = (w ≫ᵥ w'.hom).vComp' w''.hom α β := by
      ext X₁
      simp? [w'', α, β] says
        simp only [Functor.comp_obj, vComp'_app, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
          Iso.symm_inv, assoc, NatTrans.comp_app, Functor.id_obj, Functor.rightUnitor_inv_app,
          Functor.whiskerLeft_app, Functor.associator_inv_app, comp_id, id_comp, vComp_app,
          Functor.map_comp, Equivalence.inv_fun_map, CatCommSq.vInv_iso_hom_app, Iso.trans_hom,
          Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.associator_hom_app,
          Functor.rightUnitor_hom_app, Iso.hom_inv_id_app_assoc, w'', α, β]
      simp only [hw', ← eR.inverse.map_comp_assoc]
      rw [Equivalence.counitInv_app_functor]; rw [← Functor.comp_map]; rw [← NatTrans.naturality_assoc]
      simp [← H₂.map_comp]
    rw [this]
    infer_instance
  · intro
    exact vComp w w'.hom

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `vComp'_iff_of_equivalences` / 引理 `vComp'_iff_of_equivalences`

English:
lemma vComp'_iff_of_equivalences
  statement: (E : C₂ ≌ C₃) (E' : D₂ ≌ D₃)
  proof: by
  rw [← vComp_iff_of_equivalences w E E' w']; rw [TwoSquare.vComp']; rw [whiskerVertical_iff]

中文:
引理 vComp'_iff_of_equivalences
  结论: (E : C₂ ≌ C₃) (E' : D₂ ≌ D₃)
  证明: by
  rw [← vComp_iff_of_equivalences w E E' w']; rw [TwoSquare.vComp']; rw [whiskerVertical_iff]
-/
lemma vComp'_iff_of_equivalences (E : C₂ ≌ C₃) (E' : D₂ ≌ D₃)
    (w' : H₂ ⋙ E'.functor ≅ E.functor ⋙ H₃) {L₁₂ : C₁ ⥤ C₃}
    {R₁₂ : D₁ ⥤ D₃} (eL : L₁ ⋙ E.functor ≅ L₁₂)
    (eR : R₁ ⋙ E'.functor ≅ R₁₂) :
    (w.vComp' w'.hom eL eR).GuitartExact ↔ w.GuitartExact := by
  rw [← vComp_iff_of_equivalences w E E' w']; rw [TwoSquare.vComp']; rw [whiskerVertical_iff]

end GuitartExact

end VerticalComposition

end TwoSquare

end CategoryTheory
