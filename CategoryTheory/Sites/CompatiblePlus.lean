/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Plus

/-!

In this file, we prove that the plus functor is compatible with functors which
preserve the correct limits and colimits.

See `CategoryTheory/Sites/CompatibleSheafification` for the compatibility
of sheafification, which follows easily from the content in this file.

-/

@[expose] public section

noncomputable section

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory Limits Opposite CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type*} [Category* D]
variable {E : Type*} [Category* E]
variable (F : D ⥤ E)
variable [forall (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) D]
variable [forall (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) E]
variable [forall (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
variable (P : Cᵒᵖ ⥤ D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `diagramCompIso` / `diagramCompIso` 的定义

English:
definition diagramCompIso
  signature: (X : C)
  body: NatIso.ofComponents
    (fun W => by
      refine ?_ ≪≫ HasLimit.isoOfNatIso (W.unop.multicospanComp _ _).symm
      refine
        (isLimitOfPreserves F (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _))
    (by
      intro A B f
      dsimp
      ext g
      simp [← F.map_comp])

中文:
定义 diagramCompIso
  签名: (X : C)
  定义体: NatIso.ofComponents
    (fun W => by
      refine ?_ ≪≫ HasLimit.isoOfNatIso (W.unop.multicospanComp _ _).symm
      refine
        (isLimitOfPreserves F (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _))
    (by
      intro A B f
      dsimp
      ext g
      simp [← F.map_comp])

Depends on / 依赖: F.map_comp, HasLimit, HasLimit.isoOfNatIso, NatIso, NatIso.ofComponents, W.unop.multicospanComp, conePointUniqueUpToIso, isLimit, isLimitOfPreserves, isoOfNatIso, limit.isLimit, map_comp, multicospanComp, ofComponents
-/
def diagramCompIso (X : C) : J.diagram P X ⋙ F ≅ J.diagram (P ⋙ F) X :=
  NatIso.ofComponents
    (fun W => by
      refine ?_ ≪≫ HasLimit.isoOfNatIso (W.unop.multicospanComp _ _).symm
      refine
        (isLimitOfPreserves F (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _))
    (by
      intro A B f
      dsimp
      ext g
      simp [← F.map_comp])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `diagramCompIso_hom_ι` / 定理 `diagramCompIso_hom_ι`

English:
theorem diagramCompIso_hom_ι
  given: (X : C) (W : (J.Cover X)ᵒᵖ) (i : W.unop.Arrow)
  proof: by
  delta diagramCompIso
  simp

中文:
定理 diagramCompIso_hom_ι
  条件: (X : C) (W : (J.Cover X)ᵒᵖ) (i : W.unop.箭头)
  证明: by
  delta diagramCompIso
  simp

Depends on / 依赖: diagramCompIso, encard_eq_encard_of_isBase, hI.encard_eq_encard_of_isBase, isBase_restrict_iff
-/
theorem diagramCompIso_hom_ι (X : C) (W : (J.Cover X)ᵒᵖ) (i : W.unop.Arrow) :
    (J.diagramCompIso F P X).hom.app W ≫ Multiequalizer.ι ((unop W).index (P ⋙ F)) i =
    F.map (Multiequalizer.ι _ _) := by
  delta diagramCompIso
  simp

variable [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ E]
variable [forall X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `plusCompIso` / `plusCompIso` 的定义

English:
definition plusCompIso
  signature: : J.plusObj P ⋙ F ≅ J.plusObj (P ⋙ F)
  body: NatIso.ofComponents
    (fun X => by
      refine ?_ ≪≫ HasColimit.isoOfNatIso (J.diagramCompIso F P X.unop)
      refine
        (isColimitOfPreserves F
              (colimit.isColimit (J.diagram P (unop X)))).coconePointUniqueUpToIso
          (colimit.isColimit _))
    (by
      intro X Y f
    

中文:
定义 plusCompIso
  签名: : J.plusObj P ⋙ F ≅ J.plusObj (P ⋙ F)
  定义体: NatIso.ofComponents
    (fun X => by
      refine ?_ ≪≫ HasColimit.isoOfNatIso (J.diagramCompIso F P X.unop)
      refine
        (isColimitOfPreserves F
              (colimit.isColimit (J.diagram P (unop X)))).coconePointUniqueUpToIso
          (colimit.isColimit _))
    (by
      intro X Y f
    

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, HasColimit, HasColimit.isoOfNatIso, J.diagram, J.diagramCompIso, NatIso, NatIso.ofComponents, X.unop, coconePointUniqueUpToIso, colimit, colimit.isColimit, diagram, diagramCompIso, hom_ext, isColimit, isColimitOfPreserves, isoOfNatIso
-/
def plusCompIso : J.plusObj P ⋙ F ≅ J.plusObj (P ⋙ F) :=
  NatIso.ofComponents
    (fun X => by
      refine ?_ ≪≫ HasColimit.isoOfNatIso (J.diagramCompIso F P X.unop)
      refine
        (isColimitOfPreserves F
              (colimit.isColimit (J.diagram P (unop X)))).coconePointUniqueUpToIso
          (colimit.isColimit _))
    (by
      intro X Y f
      apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
      intro W
      dsimp [plusObj, plusMap]
      simp only [Functor.map_comp, Category.assoc]
      slice_rhs 1 2 =>
        erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).fac]
      slice_lhs 1 3 =>
        simp only [← F.map_comp]
        dsimp [colimMap, IsColimit.map, colimit.pre]
        simp only [colimit.ι_desc_assoc, colimit.ι_desc]
        dsimp [Cocone.precompose]
        simp only [Category.assoc, colimit.ι_desc]
        dsimp [Cocone.whisker]
        rw [F.map_comp]
      simp only [Category.assoc]
      slice_lhs 2 3 =>
        erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P Y.unop))).fac]
      dsimp
      simp only [HasColimit.isoOfNatIso_ι_hom_assoc, GrothendieckTopology.diagramPullback_app,
        colimit.ι_pre, HasColimit.isoOfNatIso_ι_hom, ι_colimMap_assoc]
      simp only [← Category.assoc]
      dsimp
      congr 1
      ext
      dsimp
      simp only [Category.assoc]
      rw [Multiequalizer.lift_ι]; rw [diagramCompIso_hom_ι]; rw [diagramCompIso_hom_ι]; rw [← F.map_comp]; rw [Multiequalizer.lift_ι])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `ι_plusCompIso_hom` / 定理 `ι_plusCompIso_hom`

English:
theorem ι_plusCompIso_hom
  given: (X) (W)
  proof: by
  delta diagramCompIso plusCompIso
  simp only [Iso.trans_hom, NatIso.ofComponents_hom_app, ←
    Category.assoc]
  erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P (unop X)))).fac]
  simp

中文:
定理 ι_plusCompIso_hom
  条件: (X) (W)
  证明: by
  delta diagramCompIso plusCompIso
  simp only [Iso.trans_hom, NatIso.ofComponents_hom_app, ←
    Category.assoc]
  erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P (unop X)))).fac]
  simp

Depends on / 依赖: Category, Category.assoc, Iso.trans_hom, J.diagram, NatIso, NatIso.ofComponents_hom_app, colimit, colimit.isColimit, diagram, diagramCompIso, isColimit, isColimitOfPreserves, ofComponents_hom_app, plusCompIso, trans_hom
-/
theorem ι_plusCompIso_hom (X) (W) :
    F.map (colimit.ι _ W) ≫ (J.plusCompIso F P).hom.app X =
      (J.diagramCompIso F P X.unop).hom.app W ≫ colimit.ι _ W := by
  delta diagramCompIso plusCompIso
  simp only [Iso.trans_hom, NatIso.ofComponents_hom_app, ←
    Category.assoc]
  erw [(isColimitOfPreserves F (colimit.isColimit (J.diagram P (unop X)))).fac]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `plusCompIso_whiskerLeft` / 定理 `plusCompIso_whiskerLeft`

English:
theorem plusCompIso_whiskerLeft
  statement: {F G : D ⥤ E} (η : F ⟶ G) (P : Cᵒᵖ ⥤ D)
  proof: by
  ext X
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp [plusObj, plusMap]
  simp only [ι_plusCompIso_hom, ι_colimMap, whiskerLeft_app, ι_plusCompIso_hom_assoc,
    NatTrans.naturality_assoc, GrothendieckTopology.diagramNatTrans_app]
  simp only

中文:
定理 plusCompIso_whiskerLeft
  结论: {F G : D ⥤ E} (η : F ⟶ G) (P : Cᵒᵖ ⥤ D)
  证明: by
  ext X
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp [plusObj, plusMap]
  simp only [ι_plusCompIso_hom, ι_colimMap, whiskerLeft_app, ι_plusCompIso_hom_assoc,
    NatTrans.naturality_assoc, GrothendieckTopology.diagramNatTrans_app]
  simp only

Depends on / 依赖: Category, Category.assoc, GrothendieckTopology, GrothendieckTopology.diagramNatTrans_app, J.diagram, NatTrans, NatTrans.naturality_assoc, X.unop, cat_disch, colimit, colimit.isColimit, diagram, diagramNatTrans_app, hom_ext, isColimit, isColimitOfPreserves, naturality_assoc, plusMap, plusObj, whiskerLeft_app
-/
theorem plusCompIso_whiskerLeft {F G : D ⥤ E} (η : F ⟶ G) (P : Cᵒᵖ ⥤ D)
    [forall X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [forall (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
    [forall X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ G]
    [forall (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan G] :
    whiskerLeft _ η ≫ (J.plusCompIso G P).hom =
      (J.plusCompIso F P).hom ≫ J.plusMap (whiskerLeft _ η) := by
  ext X
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp [plusObj, plusMap]
  simp only [ι_plusCompIso_hom, ι_colimMap, whiskerLeft_app, ι_plusCompIso_hom_assoc,
    NatTrans.naturality_assoc, GrothendieckTopology.diagramNatTrans_app]
  simp only [← Category.assoc]
  congr 1
  cat_disch

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `F`. -/
@[simps! hom_app inv_app]
/--
Definition of `plusFunctorWhiskerLeftIso` / `plusFunctorWhiskerLeftIso` 的定义

English:
definition plusFunctorWhiskerLeftIso
  signature: (P : Cᵒᵖ ⥤ D)
  body: NatIso.ofComponents (fun _ => plusCompIso _ _ _) @fun _ _ _ => plusCompIso_whiskerLeft _ _ _

中文:
定义 plusFunctorWhiskerLeftIso
  签名: (P : Cᵒᵖ ⥤ D)
  定义体: NatIso.ofComponents (fun _ => plusCompIso _ _ _) @fun _ _ _ => plusCompIso_whiskerLeft _ _ _

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, plusCompIso, plusCompIso_whiskerLeft
-/
def plusFunctorWhiskerLeftIso (P : Cᵒᵖ ⥤ D)
    [forall (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [forall (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.plusObj P) ≅ (whiskeringLeft _ _ _).obj P ⋙ J.plusFunctor E :=
  NatIso.ofComponents (fun _ => plusCompIso _ _ _) @fun _ _ _ => plusCompIso_whiskerLeft _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `plusCompIso_whiskerRight` / 定理 `plusCompIso_whiskerRight`

English:
theorem plusCompIso_whiskerRight
  given: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  proof: by
  ext X
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp [plusObj, plusMap]
  simp only [ι_colimMap, whiskerRight_app, ι_plusCompIso_hom_assoc,
    GrothendieckTopology.diagramNatTrans_app]
  simp only [← Category.assoc, ← F.map_comp]
  dsimp [co

中文:
定理 plusCompIso_whiskerRight
  条件: {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
  证明: by
  ext X
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp [plusObj, plusMap]
  simp only [ι_colimMap, whiskerRight_app, ι_plusCompIso_hom_assoc,
    GrothendieckTopology.diagramNatTrans_app]
  simp only [← Category.assoc, ← F.map_comp]
  dsimp [co

Depends on / 依赖: Category, Category.assoc, Cocone, Cocone.precompose, F.map_comp, Functor, Functor.map_comp, GrothendieckTopology, GrothendieckTopology.diagramNatTrans_app, IsColimit, IsColimit.map, J.diagram, X.unop, colimMap, colimit, colimit.isColimit, diagram, diagramNatTrans_app, hom_ext, isColimit
-/
theorem plusCompIso_whiskerRight {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    whiskerRight (J.plusMap η) F ≫ (J.plusCompIso F Q).hom =
      (J.plusCompIso F P).hom ≫ J.plusMap (whiskerRight η F) := by
  ext X
  apply (isColimitOfPreserves F (colimit.isColimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp [plusObj, plusMap]
  simp only [ι_colimMap, whiskerRight_app, ι_plusCompIso_hom_assoc,
    GrothendieckTopology.diagramNatTrans_app]
  simp only [← Category.assoc, ← F.map_comp]
  dsimp [colimMap, IsColimit.map]
  simp only [colimit.ι_desc]
  dsimp [Cocone.precompose]
  simp only [Functor.map_comp, Category.assoc, ι_plusCompIso_hom]
  simp only [← Category.assoc]
  congr 1
  dsimp only [diagram] -- Need to unfold `diagram` before `ext` applies.
  ext a
  dsimp
  simp only [diagramCompIso_hom_ι_assoc, Multiequalizer.lift_ι, diagramCompIso_hom_ι,
    Category.assoc]
  simp only [← F.map_comp, Multiequalizer.lift_ι]

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `P`. -/
@[simps! hom_app inv_app]
/--
Definition of `plusFunctorWhiskerRightIso` / `plusFunctorWhiskerRightIso` 的定义

English:
definition plusFunctorWhiskerRightIso
  signature: :
  body: NatIso.ofComponents (fun _ => J.plusCompIso _ _) @fun _ _ _ => plusCompIso_whiskerRight _ _ _

中文:
定义 plusFunctorWhiskerRightIso
  签名: :
  定义体: NatIso.ofComponents (fun _ => J.plusCompIso _ _) @fun _ _ _ => plusCompIso_whiskerRight _ _ _

Depends on / 依赖: J.plusCompIso, NatIso, NatIso.ofComponents, ofComponents, plusCompIso, plusCompIso_whiskerRight
-/
def plusFunctorWhiskerRightIso :
    J.plusFunctor D ⋙ (whiskeringRight _ _ _).obj F ≅
      (whiskeringRight _ _ _).obj F ⋙ J.plusFunctor E :=
  NatIso.ofComponents (fun _ => J.plusCompIso _ _) @fun _ _ _ => plusCompIso_whiskerRight _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `whiskerRight_toPlus_comp_plusCompIso_hom` / 定理 `whiskerRight_toPlus_comp_plusCompIso_hom`

English:
theorem whiskerRight_toPlus_comp_plusCompIso_hom
  proof: by
  ext
  dsimp [toPlus]
  simp only [ι_plusCompIso_hom, Functor.map_comp, Category.assoc]
  simp only [← Category.assoc]
  congr 1
  dsimp only [diagram] -- Need to unfold `diagram` before `ext` applies.
  ext a
  rw [Category.assoc]; rw [diagramCompIso_hom_ι]; rw [← F.map_comp]
  simp only [unop_

中文:
定理 whiskerRight_toPlus_comp_plusCompIso_hom
  证明: by
  ext
  dsimp [toPlus]
  simp only [ι_plusCompIso_hom, Functor.map_comp, Category.assoc]
  simp only [← Category.assoc]
  congr 1
  dsimp only [diagram] -- Need to unfold `diagram` before `ext` applies.
  ext a
  rw [Category.assoc]; rw [diagramCompIso_hom_ι]; rw [← F.map_comp]
  simp only [unop_

Depends on / 依赖: Category, Category.assoc, F.map_comp, Functor, Functor.comp_map, Functor.comp_obj, Functor.map_comp, Multifork, Multifork.of, applies, before, comp_map, comp_obj, diagram, limit.lift_, map_comp, toPlus, unop_op
-/
theorem whiskerRight_toPlus_comp_plusCompIso_hom :
    whiskerRight (J.toPlus _) _ ≫ (J.plusCompIso F P).hom = J.toPlus _ := by
  ext
  dsimp [toPlus]
  simp only [ι_plusCompIso_hom, Functor.map_comp, Category.assoc]
  simp only [← Category.assoc]
  congr 1
  dsimp only [diagram] -- Need to unfold `diagram` before `ext` applies.
  ext a
  rw [Category.assoc]; rw [diagramCompIso_hom_ι]; rw [← F.map_comp]
  simp only [unop_op, limit.lift_π, Multifork.ofι_π_app, Functor.comp_obj, Functor.comp_map]

@[simp]
/--
theorem `toPlus_comp_plusCompIso_inv` / 定理 `toPlus_comp_plusCompIso_inv`

English:
theorem toPlus_comp_plusCompIso_inv
  proof: by simp [Iso.comp_inv_eq]

中文:
定理 toPlus_comp_plusCompIso_inv
  证明: by simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem toPlus_comp_plusCompIso_inv :
    J.toPlus _ ≫ (J.plusCompIso F P).inv = whiskerRight (J.toPlus _) _ := by simp [Iso.comp_inv_eq]

/--
theorem `plusCompIso_inv_eq_plusLift` / 定理 `plusCompIso_inv_eq_plusLift`

English:
theorem plusCompIso_inv_eq_plusLift
  given: (hP : Presheaf.IsSheaf J (J.plusObj P ⋙ F))
  proof: by
  apply J.plusLift_unique
  simp

中文:
定理 plusCompIso_inv_eq_plusLift
  条件: (hP : 预层.是层 J (J.plusObj P ⋙ F))
  证明: by
  apply J.plusLift_unique
  simp

Depends on / 依赖: J.plusLift_unique, cardinalMk_le_cRank, isBase_restrict_iff, plusLift_unique
-/
theorem plusCompIso_inv_eq_plusLift (hP : Presheaf.IsSheaf J (J.plusObj P ⋙ F)) :
    (J.plusCompIso F P).inv = J.plusLift (whiskerRight (J.toPlus _) _) hP := by
  apply J.plusLift_unique
  simp

end CategoryTheory.GrothendieckTopology
