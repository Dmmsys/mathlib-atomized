/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!
# Left exactness of sheafification

In this file we show that sheafification commutes with finite limits.
-/

@[expose] public section


open CategoryTheory Limits Opposite

universe s t w' w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

noncomputable section

namespace CategoryTheory.GrothendieckTopology

variable {D : Type w} [Category.{t} D]
variable [forall (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary definition to be used in the proof of the fact that
`J.diagramFunctor D X` preserves limits. -/
@[simps]
/--
Definition of `coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation` / `coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation` 的定义

English:
definition coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation
  signature: {X : C} {K : Type s}
  body: E.pt
  π :=
    { app := fun k => E.π.app k ≫ Multiequalizer.ι (W.index (F.obj k)) i
      naturality := by
        intro a b f
        dsimp
        rw [Category.id_comp]; rw [Category.assoc]; rw [← E.w f]
        dsimp [diagramNatTrans]
        simp only [Multiequalizer.lift_ι, Category.assoc] }

中文:
定义 coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation
  签名: {X : C} {K : 类型 s}
  定义体: E.pt
  π :=
    { app := fun k => E.π.app k ≫ Multiequalizer.ι (W.index (F.obj k)) i
      naturality := by
        intro a b f
        dsimp
        rw [Category.id_comp]; rw [Category.assoc]; rw [← E.w f]
        dsimp [diagramNatTrans]
        simp only [Multiequalizer.lift_ι, Category.assoc] }

Depends on / 依赖: E.pt
-/
def coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation {X : C} {K : Type s}
    [SmallCategory K] {F : K ⥤ Cᵒᵖ ⥤ D} {W : J.Cover X} (i : W.Arrow)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj (op W))) :
    Cone (F ⋙ (evaluation _ _).obj (op i.Y)) where
  pt := E.pt
  π :=
    { app := fun k => E.π.app k ≫ Multiequalizer.ι (W.index (F.obj k)) i
      naturality := by
        intro a b f
        dsimp
        rw [Category.id_comp]; rw [Category.assoc]; rw [← E.w f]
        dsimp [diagramNatTrans]
        simp only [Multiequalizer.lift_ι, Category.assoc] }

/--
Definition of `liftToDiagramLimitObjAux` / `liftToDiagramLimitObjAux` 的定义

English:
definition liftToDiagramLimitObjAux
  signature: {X : C} {K : Type s} [SmallCategory K] [HasLimitsOfShape K D]
  body: (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) (limit.isLimit F)).lift
        (coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation i E)

@[reassoc (attr := simp)]

中文:
定义 liftToDiagramLimitObjAux
  签名: {X : C} {K : 类型 s} [小范畴 K] [有形状极限 K D]
  定义体: (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) (limit.isLimit F)).lift
        (coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation i E)

@[reassoc (attr := simp)]

Depends on / 依赖: coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation, evaluation, isLimit, isLimitOfPreserves, limit.isLimit
-/
def liftToDiagramLimitObjAux {X : C} {K : Type s} [SmallCategory K] [HasLimitsOfShape K D]
    {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W))
    (i : (unop W).Arrow) :
    E.pt ⟶ (limit F).obj (op i.Y) :=
  (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) (limit.isLimit F)).lift
        (coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation i E)

@[reassoc (attr := simp)]
/--
lemma `liftToDiagramLimitObjAux_fac` / 引理 `liftToDiagramLimitObjAux_fac`

English:
lemma liftToDiagramLimitObjAux_fac
  statement: {X : C} {K : Type s} [SmallCategory K]
  proof: IsLimit.fac _ _ _

中文:
引理 liftToDiagramLimitObjAux_fac
  结论: {X : C} {K : 类型 s} [小范畴 K]
  证明: IsLimit.fac _ _ _

Depends on / 依赖: IsLimit, IsLimit.fac
-/
lemma liftToDiagramLimitObjAux_fac {X : C} {K : Type s} [SmallCategory K]
    [HasLimitsOfShape K D] {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W))
    (i : (unop W).Arrow) (k : K) :
    liftToDiagramLimitObjAux F E i ≫ (limit.π F k).app (op i.Y) = E.π.app k ≫
      Multiequalizer.ι ((unop W).index (F.obj k)) i :=
  IsLimit.fac _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftToDiagramLimitObj` / `liftToDiagramLimitObj` 的定义

English:
abbreviation liftToDiagramLimitObj
  signature: {X : C} {K : Type s} [SmallCategory K] [HasLimitsOfShape K D]
  body: Multiequalizer.lift ((unop W).index (limit F)) E.pt (liftToDiagramLimitObjAux F E)
    (by
      intro i
      dsimp
      ext k
      simp only [Category.assoc, NatTrans.naturality, liftToDiagramLimitObjAux_fac_assoc]
      erw [Multiequalizer.condition]
      rfl)

中文:
缩写 liftToDiagramLimitObj
  签名: {X : C} {K : 类型 s} [小范畴 K] [有形状极限 K D]
  定义体: Multiequalizer.lift ((unop W).index (limit F)) E.pt (liftToDiagramLimitObjAux F E)
    (by
      intro i
      dsimp
      ext k
      simp only [Category.assoc, NatTrans.naturality, liftToDiagramLimitObjAux_fac_assoc]
      erw [Multiequalizer.condition]
      rfl)

Depends on / 依赖: Category, Category.assoc, E.pt, Multiequalizer, Multiequalizer.condition, Multiequalizer.lift, NatTrans, NatTrans.naturality, condition, liftToDiagramLimitObjAux, liftToDiagramLimitObjAux_fac_assoc, naturality
-/
abbrev liftToDiagramLimitObj {X : C} {K : Type s} [SmallCategory K] [HasLimitsOfShape K D]
    {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W)) :
    E.pt ⟶ (J.diagram (limit F) X).obj W :=
  Multiequalizer.lift ((unop W).index (limit F)) E.pt (liftToDiagramLimitObjAux F E)
    (by
      intro i
      dsimp
      ext k
      simp only [Category.assoc, NatTrans.naturality, liftToDiagramLimitObjAux_fac_assoc]
      erw [Multiequalizer.condition]
      rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `preservesLimit_diagramFunctor` / 实例 `preservesLimit_diagramFunctor`

English:
instance preservesLimit_diagramFunctor
  body: preservesLimit_of_evaluation _ _ fun W =>
    preservesLimit_of_preserves_limit_cone (limit.isLimit _)
      { lift := fun E => liftToDiagramLimitObj.{_, t, w, v, u} F E
        fac := by
          intro E k
          dsimp [diagramNatTrans]
          refine Multiequalizer.hom_ext _ _ _ (fun a => ?_)
          simp only [Multiequalizer.lift_ι, Multiequalizer.lift_ι_assoc, Category.assoc,
            liftToDiagramLimitObjAux_fac]
        uniq := by
          intro E m hm
          refine Multiequalizer.hom_ext _ _ _ (fun a => limit_obj_ext (fun j => ?_))
          dsimp [liftToDiagramLimitObj]
          rw [Multiequalizer.lift_ι]; rw [Category.assoc]; rw [liftToDiagramLimitObjAux_fac]; rw [← hm]; rw [Category.assoc]
          dsimp
          rw [limit.lift_π]
          dsimp }

中文:
实例 preservesLimit_diagramFunctor
  定义体: preservesLimit_of_evaluation _ _ fun W =>
    preservesLimit_of_preserves_limit_cone (limit.isLimit _)
      { lift := fun E => liftToDiagramLimitObj.{_, t, w, v, u} F E
        fac := by
          intro E k
          dsimp [diagramNatTrans]
          refine Multiequalizer.hom_ext _ _ _ (fun a => ?_)
          simp only [Multiequalizer.lift_ι, Multiequalizer.lift_ι_assoc, Category.assoc,
            liftToDiagramLimitObjAux_fac]
        uniq := by
          intro E m hm
          refine Multiequalizer.hom_ext _ _ _ (fun a => limit_obj_ext (fun j => ?_))
          dsimp [liftToDiagramLimitObj]
          rw [Multiequalizer.lift_ι]; rw [Category.assoc]; rw [liftToDiagramLimitObjAux_fac]; rw [← hm]; rw [Category.assoc]
          dsimp
          rw [limit.lift_π]
          dsimp }

Depends on / 依赖: Category, Category.assoc, Multiequalizer, Multiequalizer.hom_ext, Multiequalizer.lift_, diagramNatTrans, hom_ext, isLimit, liftToDiagramLimitObj, liftToDiagramLimitObjAux_fac, limit.isLimit, limit_obj_ext, preservesLimit_of_evaluation, preservesLimit_of_preserves_limit_cone
-/
instance preservesLimit_diagramFunctor
    (X : C) (K : Type s) [SmallCategory K] [HasLimitsOfShape K D] (F : K ⥤ Cᵒᵖ ⥤ D) :
    PreservesLimit F (J.diagramFunctor D X) :=
  preservesLimit_of_evaluation _ _ fun W =>
    preservesLimit_of_preserves_limit_cone (limit.isLimit _)
      { lift := fun E => liftToDiagramLimitObj.{_, t, w, v, u} F E
        fac := by
          intro E k
          dsimp [diagramNatTrans]
          refine Multiequalizer.hom_ext _ _ _ (fun a => ?_)
          simp only [Multiequalizer.lift_ι, Multiequalizer.lift_ι_assoc, Category.assoc,
            liftToDiagramLimitObjAux_fac]
        uniq := by
          intro E m hm
          refine Multiequalizer.hom_ext _ _ _ (fun a => limit_obj_ext (fun j => ?_))
          dsimp [liftToDiagramLimitObj]
          rw [Multiequalizer.lift_ι]; rw [Category.assoc]; rw [liftToDiagramLimitObjAux_fac]; rw [← hm]; rw [Category.assoc]
          dsimp
          rw [limit.lift_π]
          dsimp }

/--
Instance `preservesLimitsOfShape_diagramFunctor` / 实例 `preservesLimitsOfShape_diagramFunctor`

English:
instance preservesLimitsOfShape_diagramFunctor
  body: ⟨by apply preservesLimit_diagramFunctor.{s, t, w, v, u}⟩

中文:
实例 preservesLimitsOfShape_diagramFunctor
  定义体: ⟨by apply preservesLimit_diagramFunctor.{s, t, w, v, u}⟩

Depends on / 依赖: preservesLimit_diagramFunctor
-/
instance preservesLimitsOfShape_diagramFunctor
    (X : C) (K : Type s) [SmallCategory K] [HasLimitsOfShape K D] :
    PreservesLimitsOfShape K (J.diagramFunctor D X) :=
  ⟨by apply preservesLimit_diagramFunctor.{s, t, w, v, u}⟩

/--
Instance `preservesLimits_diagramFunctor` / 实例 `preservesLimits_diagramFunctor`

English:
instance preservesLimits_diagramFunctor
  signature: (X : C) [HasLimitsOfSize.{max t u v, max t u v} D]
  body: by
  constructor
  intro _ _
  apply preservesLimitsOfShape_diagramFunctor.{max t u v}

中文:
实例 preservesLimits_diagramFunctor
  签名: (X : C) [有LimitsOfSize.{最大值 t u v, 最大值 t u v} D]
  定义体: by
  constructor
  intro _ _
  apply preservesLimitsOfShape_diagramFunctor.{max t u v}

Depends on / 依赖: preservesLimitsOfShape_diagramFunctor
-/
instance preservesLimits_diagramFunctor (X : C) [HasLimitsOfSize.{max t u v, max t u v} D] :
    PreservesLimits (J.diagramFunctor D X) := by
  constructor
  intro _ _
  apply preservesLimitsOfShape_diagramFunctor.{max t u v}

variable [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable {FD : D -> D -> Type*} {CD : D -> Type t} [forall X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD]
variable [forall X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
variable [forall X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftToPlusObjLimitObj` / `liftToPlusObjLimitObj` 的定义

English:
definition liftToPlusObjLimitObj
  signature: {K : Type s} [SmallCategory K] [FinCategory K]
  body: let F' := F ⋙ J.diagramFunctor D X
  let e := colimitLimitIso (F ⋙ J.diagramFunctor D X)
  let t : J.diagram (limit F) X ≅ limit (F ⋙ J.diagramFunctor D X) :=
    (isLimitOfPreserves (J.diagramFunctor D X) (limit.isLimit F)).conePointUniqueUpToIso
      (limit.isLimit _)
  let p : (J.plusObj (limit F)).obj (op X) ≅ colimit (limit (F ⋙ J.diagramFunctor D X)) :=
    HasColimit.isoOfNatIso t
  let s :
    colimit (F ⋙ J.diagramFunctor D X).flip ≅ F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X) :=
    NatIso.ofComponents (fun k => colimitObjIsoColimitCompEvaluation _ k)
      (by
        intro i j f
        rw [← Iso.eq_comp_inv]; rw [Category.assoc]; rw [← Iso.inv_comp_eq]
        refine colimit.hom_ext (fun w => ?_)
        dsimp [plusMap]
        erw [colimit.ι_map_assoc,
          colimitObjIsoColimitCompEvaluation_ι_inv (F ⋙ J.diagramFunctor D X).flip w j,
          colimitObjIsoColimitCompEvaluation_ι_inv_assoc (F ⋙ J.diagramFunctor D X).flip w i]
        rw [← (colimit.ι (F ⋙ J.diagramFunctor D X).flip w).naturality]
        rfl)
  limit.lift _ S ≫ (HasLimit.isoOfNatIso s.symm).hom ≫ e.inv ≫ p.inv

中文:
定义 liftToPlusObjLimitObj
  签名: {K : 类型 s} [小范畴 K] [有限范畴 K]
  定义体: let F' := F ⋙ J.diagramFunctor D X
  let e := colimitLimitIso (F ⋙ J.diagramFunctor D X)
  let t : J.diagram (limit F) X ≅ limit (F ⋙ J.diagramFunctor D X) :=
    (isLimitOfPreserves (J.diagramFunctor D X) (limit.isLimit F)).conePointUniqueUpToIso
      (limit.isLimit _)
  let p : (J.plusObj (limit F)).obj (op X) ≅ colimit (limit (F ⋙ J.diagramFunctor D X)) :=
    HasColimit.isoOfNatIso t
  let s :
    colimit (F ⋙ J.diagramFunctor D X).flip ≅ F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X) :=
    NatIso.ofComponents (fun k => colimitObjIsoColimitCompEvaluation _ k)
      (by
        intro i j f
        rw [← Iso.eq_comp_inv]; rw [Category.assoc]; rw [← Iso.inv_comp_eq]
        refine colimit.hom_ext (fun w => ?_)
        dsimp [plusMap]
        erw [colimit.ι_map_assoc,
          colimitObjIsoColimitCompEvaluation_ι_inv (F ⋙ J.diagramFunctor D X).flip w j,
          colimitObjIsoColimitCompEvaluation_ι_inv_assoc (F ⋙ J.diagramFunctor D X).flip w i]
        rw [← (colimit.ι (F ⋙ J.diagramFunctor D X).flip w).naturality]
        rfl)
  limit.lift _ S ≫ (HasLimit.isoOfNatIso s.symm).hom ≫ e.inv ≫ p.inv

Depends on / 依赖: HasColimit, HasColimit.isoOfNatIso, J.diagram, J.diagramFunctor, J.plusFunctor, J.plusObj, NatIso, NatIso.ofComponents, colimit, colimitLimitIso, conePointUniqueUpToIso, diagram, diagramFunctor, evaluation, isLimit, isLimitOfPreserves, isoOfNatIso, limit.isLimit, ofComponents, plusFunctor
-/
def liftToPlusObjLimitObj {K : Type s} [SmallCategory K] [FinCategory K]
    [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)]
    [ReflectsLimitsOfShape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) :
    S.pt ⟶ (J.plusObj (limit F)).obj (op X) :=
  let F' := F ⋙ J.diagramFunctor D X
  let e := colimitLimitIso (F ⋙ J.diagramFunctor D X)
  let t : J.diagram (limit F) X ≅ limit (F ⋙ J.diagramFunctor D X) :=
    (isLimitOfPreserves (J.diagramFunctor D X) (limit.isLimit F)).conePointUniqueUpToIso
      (limit.isLimit _)
  let p : (J.plusObj (limit F)).obj (op X) ≅ colimit (limit (F ⋙ J.diagramFunctor D X)) :=
    HasColimit.isoOfNatIso t
  let s :
    colimit (F ⋙ J.diagramFunctor D X).flip ≅ F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X) :=
    NatIso.ofComponents (fun k => colimitObjIsoColimitCompEvaluation _ k)
      (by
        intro i j f
        rw [← Iso.eq_comp_inv]; rw [Category.assoc]; rw [← Iso.inv_comp_eq]
        refine colimit.hom_ext (fun w => ?_)
        dsimp [plusMap]
        erw [colimit.ι_map_assoc,
          colimitObjIsoColimitCompEvaluation_ι_inv (F ⋙ J.diagramFunctor D X).flip w j,
          colimitObjIsoColimitCompEvaluation_ι_inv_assoc (F ⋙ J.diagramFunctor D X).flip w i]
        rw [← (colimit.ι (F ⋙ J.diagramFunctor D X).flip w).naturality]
        rfl)
  limit.lift _ S ≫ (HasLimit.isoOfNatIso s.symm).hom ≫ e.inv ≫ p.inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- This lemma should not be used directly. Instead, one should use the fact that
-- `J.plusFunctor D` preserves finite limits, along with the fact that
-- evaluation preserves limits.
/--
theorem `liftToPlusObjLimitObj_fac` / 定理 `liftToPlusObjLimitObj_fac`

English:
theorem liftToPlusObjLimitObj_fac
  statement: {K : Type s} [SmallCategory K] [FinCategory K]
  proof: by
  dsimp only [liftToPlusObjLimitObj]
  rw [← (limit.isLimit (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))).fac S k]; rw [Category.assoc]
  congr 1
  dsimp
  rw [Category.assoc]; rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [Iso.inv_comp_eq]; rw [Iso.inv_comp_eq]
  refine colimit.hom_ext (fun j => ?_)
  dsimp [plusMap]
  simp only [HasColimit.isoOfNatIso_ι_hom_assoc, ι_colimMap]
  dsimp [IsLimit.conePointUniqueUpToIso, HasLimit.isoOfNatIso, IsLimit.map]
  rw [limit.lift_π]
  dsimp
  rw [ι_colimitLimitIso_limit_π_assoc]
  simp_rw [← Category.assoc, ← NatTrans.comp_app]
  rw [limit.lift_π]; rw [Category.assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  erw [colimit.ι_desc]
  rfl

中文:
定理 liftToPlusObjLimitObj_fac
  结论: {K : 类型 s} [小范畴 K] [有限范畴 K]
  证明: by
  dsimp only [liftToPlusObjLimitObj]
  rw [← (limit.isLimit (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))).fac S k]; rw [Category.assoc]
  congr 1
  dsimp
  rw [Category.assoc]; rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [Iso.inv_comp_eq]; rw [Iso.inv_comp_eq]
  refine colimit.hom_ext (fun j => ?_)
  dsimp [plusMap]
  simp only [HasColimit.isoOfNatIso_ι_hom_assoc, ι_colimMap]
  dsimp [IsLimit.conePointUniqueUpToIso, HasLimit.isoOfNatIso, IsLimit.map]
  rw [limit.lift_π]
  dsimp
  rw [ι_colimitLimitIso_limit_π_assoc]
  simp_rw [← Category.assoc, ← NatTrans.comp_app]
  rw [limit.lift_π]; rw [Category.assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  erw [colimit.ι_desc]
  rfl

Depends on / 依赖: Category, Category.assoc, HasColimit, HasColimit.isoOfNatIso_, HasLimit, HasLimit.isoOfNatIso, IsLimit, IsLimit.conePointUniqueUpToIso, IsLimit.map, Iso.eq_inv_comp, Iso.inv_comp_eq, J.plusFunctor, colimit, colimit.hom_ext, conePointUniqueUpToIso, eq_inv_comp, evaluation, hom_ext, inv_comp_eq, isLimit
-/
theorem liftToPlusObjLimitObj_fac {K : Type s} [SmallCategory K] [FinCategory K]
    [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)]
    [ReflectsLimitsOfShape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) (k) :
    liftToPlusObjLimitObj F X S ≫ (J.plusMap (limit.π F k)).app (op X) = S.π.app k := by
  dsimp only [liftToPlusObjLimitObj]
  rw [← (limit.isLimit (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))).fac S k]; rw [Category.assoc]
  congr 1
  dsimp
  rw [Category.assoc]; rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [Iso.inv_comp_eq]; rw [Iso.inv_comp_eq]
  refine colimit.hom_ext (fun j => ?_)
  dsimp [plusMap]
  simp only [HasColimit.isoOfNatIso_ι_hom_assoc, ι_colimMap]
  dsimp [IsLimit.conePointUniqueUpToIso, HasLimit.isoOfNatIso, IsLimit.map]
  rw [limit.lift_π]
  dsimp
  rw [ι_colimitLimitIso_limit_π_assoc]
  simp_rw [← Category.assoc, ← NatTrans.comp_app]
  rw [limit.lift_π]; rw [Category.assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  erw [colimit.ι_desc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `preservesLimitsOfShape_plusFunctor` / 实例 `preservesLimitsOfShape_plusFunctor`

English:
instance preservesLimitsOfShape_plusFunctor
  body: by
  constructor; intro F; apply preservesLimit_of_evaluation; intro X
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
  refine ⟨fun S => liftToPlusObjLimitObj F X.unop S, ?_, ?_⟩
  · intro S k
    apply liftToPlusObjLimitObj_fac
  · intro S m hm
    dsimp [liftToPlusObjLimitObj]
    simp_rw [← Category.assoc, Iso.eq_comp_inv, ← Iso.comp_inv_eq]
    refine limit.hom_ext (fun k => ?_)
    simp only [limit.lift_π, Category.assoc, ← hm]
    congr 1
    refine colimit.hom_ext (fun k => ?_)
    dsimp [plusMap, plusObj]
    erw [colimit.ι_map, colimit.ι_desc_assoc, limit.lift_π]
    conv_lhs => dsimp
    simp only [Category.assoc]
    rw [ι_colimitLimitIso_limit_π_assoc]
    simp only [colimitObjIsoColimitCompEvaluation_ι_app_hom]
    conv_lhs =>
      dsimp [IsLimit.conePointUniqueUpToIso]
    rw [← Category.assoc]; rw [← NatTrans.comp_app]; rw [limit.lift_π]
    rfl

中文:
实例 preservesLimitsOfShape_plusFunctor
  定义体: by
  constructor; intro F; apply preservesLimit_of_evaluation; intro X
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
  refine ⟨fun S => liftToPlusObjLimitObj F X.unop S, ?_, ?_⟩
  · intro S k
    apply liftToPlusObjLimitObj_fac
  · intro S m hm
    dsimp [liftToPlusObjLimitObj]
    simp_rw [← Category.assoc, Iso.eq_comp_inv, ← Iso.comp_inv_eq]
    refine limit.hom_ext (fun k => ?_)
    simp only [limit.lift_π, Category.assoc, ← hm]
    congr 1
    refine colimit.hom_ext (fun k => ?_)
    dsimp [plusMap, plusObj]
    erw [colimit.ι_map, colimit.ι_desc_assoc, limit.lift_π]
    conv_lhs => dsimp
    simp only [Category.assoc]
    rw [ι_colimitLimitIso_limit_π_assoc]
    simp only [colimitObjIsoColimitCompEvaluation_ι_app_hom]
    conv_lhs =>
      dsimp [IsLimit.conePointUniqueUpToIso]
    rw [← Category.assoc]; rw [← NatTrans.comp_app]; rw [limit.lift_π]
    rfl

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, Iso.eq_comp_inv, X.unop, colimit, colimit.hom_ext, comp_inv_eq, eq_comp_inv, hom_ext, isLimit, liftToPlusObjLimitObj, liftToPlusObjLimitObj_fac, limit.hom_ext, limit.isLimit, limit.lift_, plusMap, plusObj, preservesLimit_of_evaluation, preservesLimit_of_preserves_limit_cone
-/
instance preservesLimitsOfShape_plusFunctor
    (K : Type t) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.plusFunctor D) := by
  constructor; intro F; apply preservesLimit_of_evaluation; intro X
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
  refine ⟨fun S => liftToPlusObjLimitObj F X.unop S, ?_, ?_⟩
  · intro S k
    apply liftToPlusObjLimitObj_fac
  · intro S m hm
    dsimp [liftToPlusObjLimitObj]
    simp_rw [← Category.assoc, Iso.eq_comp_inv, ← Iso.comp_inv_eq]
    refine limit.hom_ext (fun k => ?_)
    simp only [limit.lift_π, Category.assoc, ← hm]
    congr 1
    refine colimit.hom_ext (fun k => ?_)
    dsimp [plusMap, plusObj]
    erw [colimit.ι_map, colimit.ι_desc_assoc, limit.lift_π]
    conv_lhs => dsimp
    simp only [Category.assoc]
    rw [ι_colimitLimitIso_limit_π_assoc]
    simp only [colimitObjIsoColimitCompEvaluation_ι_app_hom]
    conv_lhs =>
      dsimp [IsLimit.conePointUniqueUpToIso]
    rw [← Category.assoc]; rw [← NatTrans.comp_app]; rw [limit.lift_π]
    rfl

/--
Instance `preserveFiniteLimits_plusFunctor` / 实例 `preserveFiniteLimits_plusFunctor`

English:
instance preserveFiniteLimits_plusFunctor
  body: by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intro K _ _
  have : ReflectsLimitsOfShape K (forget D) := reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply preservesLimitsOfShape_plusFunctor

中文:
实例 preserveFiniteLimits_plusFunctor
  定义体: by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intro K _ _
  have : ReflectsLimitsOfShape K (forget D) := reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply preservesLimitsOfShape_plusFunctor

Depends on / 依赖: ReflectsLimitsOfShape, forget, preservesFiniteLimits_of_preservesFiniteLimitsOfSize, preservesLimitsOfShape_plusFunctor, reflectsLimitsOfShape_of_reflectsIsomorphisms
-/
instance preserveFiniteLimits_plusFunctor
    [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [(forget D).ReflectsIsomorphisms] :
    PreservesFiniteLimits (J.plusFunctor D) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intro K _ _
  have : ReflectsLimitsOfShape K (forget D) := reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply preservesLimitsOfShape_plusFunctor

/--
Instance `preservesLimitsOfShape_sheafification` / 实例 `preservesLimitsOfShape_sheafification`

English:
instance preservesLimitsOfShape_sheafification
  body: Limits.comp_preservesLimitsOfShape _ _

中文:
实例 preservesLimitsOfShape_sheafification
  定义体: Limits.comp_preservesLimitsOfShape _ _

Depends on / 依赖: Limits, Limits.comp_preservesLimitsOfShape, comp_preservesLimitsOfShape
-/
instance preservesLimitsOfShape_sheafification
    (K : Type t) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.sheafification D) :=
  Limits.comp_preservesLimitsOfShape _ _

/--
Instance `preservesFiniteLimits_sheafification` / 实例 `preservesFiniteLimits_sheafification`

English:
instance preservesFiniteLimits_sheafification
  body: Limits.comp_preservesFiniteLimits _ _

中文:
实例 preservesFiniteLimits_sheafification
  定义体: Limits.comp_preservesFiniteLimits _ _

Depends on / 依赖: Limits, Limits.comp_preservesFiniteLimits, comp_preservesFiniteLimits
-/
instance preservesFiniteLimits_sheafification
    [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [(forget D).ReflectsIsomorphisms] :
    PreservesFiniteLimits (J.sheafification D) :=
  Limits.comp_preservesFiniteLimits _ _

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory

section

variable {D : Type w} [Category.{t} D]
variable [forall (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
variable [forall X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable {FD : D -> D -> Type*} {CD : D -> Type t}
variable [forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{t} D FD]
variable [forall X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
variable [(forget D).ReflectsIsomorphisms]
variable [forall {X : C} (S : J.Cover X), PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget D)]
variable (K : Type w')
variable [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]

/--
Instance `preservesLimitsOfShape_presheafToSheaf` / 实例 `preservesLimitsOfShape_presheafToSheaf`

English:
instance preservesLimitsOfShape_presheafToSheaf
  body: by
  let e := (FinCategory.equivAsType K).symm.trans (AsSmall.equiv.{0, 0, t})
  have : HasLimitsOfShape (AsSmall.{t} (FinCategory.AsType K)) D :=
    Limits.hasLimitsOfShape_of_equivalence e
  have : FinCategory (AsSmall.{t} (FinCategory.AsType K)) := by
    constructor
    · change Fintype (ULift _)
      infer_instance
    · intro j j'
      change Fintype (ULift _)
      infer_instance
  refine @preservesLimitsOfShape_of_equiv _ _ _ _ _ _ _ _ e.symm _ (show _ from ?_)
  constructor; intro F; constructor; intro S hS; constructor
  apply isLimitOfReflects (sheafToPresheaf J D)
  have : ReflectsLimitsOfShape (AsSmall.{t} (FinCategory.AsType K)) (forget D) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply isLimitOfPreserves (J.sheafification D) hS

中文:
实例 preservesLimitsOfShape_presheafToSheaf
  定义体: by
  let e := (FinCategory.equivAsType K).symm.trans (AsSmall.equiv.{0, 0, t})
  have : HasLimitsOfShape (AsSmall.{t} (FinCategory.AsType K)) D :=
    Limits.hasLimitsOfShape_of_equivalence e
  have : FinCategory (AsSmall.{t} (FinCategory.AsType K)) := by
    constructor
    · change Fintype (ULift _)
      infer_instance
    · intro j j'
      change Fintype (ULift _)
      infer_instance
  refine @preservesLimitsOfShape_of_equiv _ _ _ _ _ _ _ _ e.symm _ (show _ from ?_)
  constructor; intro F; constructor; intro S hS; constructor
  apply isLimitOfReflects (sheafToPresheaf J D)
  have : ReflectsLimitsOfShape (AsSmall.{t} (FinCategory.AsType K)) (forget D) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply isLimitOfPreserves (J.sheafification D) hS

Depends on / 依赖: AsSmall, AsSmall.equiv, AsType, FinCategory, FinCategory.AsType, FinCategory.equivAsType, Fintype, HasLimitsOfShape, Limits, Limits.hasLimitsOfShape_of_equivalence, e.symm, equivAsType, hasLimitsOfShape_of_equivalence, infer_instance, preservesLimitsOfShape_of_equiv, symm.trans
-/
instance preservesLimitsOfShape_presheafToSheaf
    [PreservesLimits (forget D)] [forall X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] :
    PreservesLimitsOfShape K (plusPlusSheaf J D) := by
  let e := (FinCategory.equivAsType K).symm.trans (AsSmall.equiv.{0, 0, t})
  have : HasLimitsOfShape (AsSmall.{t} (FinCategory.AsType K)) D :=
    Limits.hasLimitsOfShape_of_equivalence e
  have : FinCategory (AsSmall.{t} (FinCategory.AsType K)) := by
    constructor
    · change Fintype (ULift _)
      infer_instance
    · intro j j'
      change Fintype (ULift _)
      infer_instance
  refine @preservesLimitsOfShape_of_equiv _ _ _ _ _ _ _ _ e.symm _ (show _ from ?_)
  constructor; intro F; constructor; intro S hS; constructor
  apply isLimitOfReflects (sheafToPresheaf J D)
  have : ReflectsLimitsOfShape (AsSmall.{t} (FinCategory.AsType K)) (forget D) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply isLimitOfPreserves (J.sheafification D) hS

/--
Instance `preservesFiniteLimits_presheafToSheaf` / 实例 `preservesFiniteLimits_presheafToSheaf`

English:
instance preservesFiniteLimits_presheafToSheaf
  signature: [PreservesLimits (forget D)]
  body: by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intros
  infer_instance

中文:
实例 preservesFiniteLimits_presheafToSheaf
  签名: [PreservesLimits (forget D)]
  定义体: by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intros
  infer_instance

Depends on / 依赖: infer_instance, intros, preservesFiniteLimits_of_preservesFiniteLimitsOfSize
-/
instance preservesFiniteLimits_presheafToSheaf [PreservesLimits (forget D)]
    [forall X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] [HasFiniteLimits D] :
    PreservesFiniteLimits (plusPlusSheaf J D) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intros
  infer_instance

variable (J D)

/--
Definition of `plusPlusSheafIsoPresheafToSheaf` / `plusPlusSheafIsoPresheafToSheaf` 的定义

English:
definition plusPlusSheafIsoPresheafToSheaf
  signature: : plusPlusSheaf J D ≅ presheafToSheaf J D
  body: (plusPlusAdjunction J D).leftAdjointUniq (sheafificationAdjunction J D)

中文:
定义 plusPlusSheafIsoPresheafToSheaf
  签名: : plusPlusSheaf J D ≅ presheafToSheaf J D
  定义体: (plusPlusAdjunction J D).leftAdjointUniq (sheafificationAdjunction J D)

Depends on / 依赖: leftAdjointUniq, plusPlusAdjunction, sheafificationAdjunction
-/
def plusPlusSheafIsoPresheafToSheaf : plusPlusSheaf J D ≅ presheafToSheaf J D :=
  (plusPlusAdjunction J D).leftAdjointUniq (sheafificationAdjunction J D)

/--
Definition of `plusPlusFunctorIsoSheafification` / `plusPlusFunctorIsoSheafification` 的定义

English:
definition plusPlusFunctorIsoSheafification
  signature: : J.sheafification D ≅ sheafification J D
  body: Functor.isoWhiskerRight (plusPlusSheafIsoPresheafToSheaf J D) (sheafToPresheaf J D)

中文:
定义 plusPlusFunctorIsoSheafification
  签名: : J.sheafification D ≅ sheafification J D
  定义体: Functor.isoWhiskerRight (plusPlusSheafIsoPresheafToSheaf J D) (sheafToPresheaf J D)

Depends on / 依赖: Functor, Functor.isoWhiskerRight, isoWhiskerRight, plusPlusSheafIsoPresheafToSheaf, sheafToPresheaf
-/
def plusPlusFunctorIsoSheafification : J.sheafification D ≅ sheafification J D :=
  Functor.isoWhiskerRight (plusPlusSheafIsoPresheafToSheaf J D) (sheafToPresheaf J D)

/--
Definition of `plusPlusIsoSheafify` / `plusPlusIsoSheafify` 的定义

English:
definition plusPlusIsoSheafify
  signature: (P : Cᵒᵖ ⥤ D)
  body: (sheafToPresheaf J D).mapIso ((plusPlusSheafIsoPresheafToSheaf J D).app P)

中文:
定义 plusPlusIsoSheafify
  签名: (P : Cᵒᵖ ⥤ D)
  定义体: (sheafToPresheaf J D).mapIso ((plusPlusSheafIsoPresheafToSheaf J D).app P)

Depends on / 依赖: mapIso, plusPlusSheafIsoPresheafToSheaf, sheafToPresheaf
-/
def plusPlusIsoSheafify (P : Cᵒᵖ ⥤ D) : J.sheafify P ≅ sheafify J P :=
  (sheafToPresheaf J D).mapIso ((plusPlusSheafIsoPresheafToSheaf J D).app P)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `toSheafify_plusPlusIsoSheafify_hom` / 引理 `toSheafify_plusPlusIsoSheafify_hom`

English:
lemma toSheafify_plusPlusIsoSheafify_hom
  given: (P : Cᵒᵖ ⥤ D)
  proof: by
  convert!
    Adjunction.unit_leftAdjointUniq_hom_app (plusPlusAdjunction J D) (sheafificationAdjunction J D)
      P
  ext1 P
  dsimp [GrothendieckTopology.toSheafify, plusPlusAdjunction]
  rw [Category.comp_id]

中文:
引理 toSheafify_plusPlusIsoSheafify_hom
  条件: (P : Cᵒᵖ ⥤ D)
  证明: by
  convert!
    Adjunction.unit_leftAdjointUniq_hom_app (plusPlusAdjunction J D) (sheafificationAdjunction J D)
      P
  ext1 P
  dsimp [GrothendieckTopology.toSheafify, plusPlusAdjunction]
  rw [Category.comp_id]

Depends on / 依赖: Adjunction, Adjunction.unit_leftAdjointUniq_hom_app, Category, Category.comp_id, GrothendieckTopology, GrothendieckTopology.toSheafify, comp_id, convert, plusPlusAdjunction, sheafificationAdjunction, toSheafify, unit_leftAdjointUniq_hom_app
-/
lemma toSheafify_plusPlusIsoSheafify_hom (P : Cᵒᵖ ⥤ D) :
    J.toSheafify P ≫ (plusPlusIsoSheafify J D P).hom = toSheafify J P := by
  convert!
    Adjunction.unit_leftAdjointUniq_hom_app (plusPlusAdjunction J D) (sheafificationAdjunction J D)
      P
  ext1 P
  dsimp [GrothendieckTopology.toSheafify, plusPlusAdjunction]
  rw [Category.comp_id]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesLimits
  signature: (forget D)] [HasFiniteLimits D]
  body: HasSheafify.mk' J D (plusPlusAdjunction J D)

中文:
实例 [PreservesLimits
  签名: (forget D)] [有有限极限 D]
  定义体: HasSheafify.mk' J D (plusPlusAdjunction J D)

Depends on / 依赖: HasSheafify, HasSheafify.mk, plusPlusAdjunction
-/
instance [PreservesLimits (forget D)] [HasFiniteLimits D]
    [forall X : C, Small.{t, max u v} (J.Cover X)ᵒᵖ] :
    HasSheafify J D :=
  HasSheafify.mk' J D (plusPlusAdjunction J D)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSheafify J (Type (max u v))
  body: by
  infer_instance

中文:
实例 :
  签名: 有Sheafify J (类型 (最大值 u v))
  定义体: by
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : HasSheafify J (Type (max u v)) := by
  infer_instance

end

variable {D : Type w} [Category.{w'} D]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FinitaryExtensive
  signature: D] [HasPullbacks D] [HasSheafify J D] :
  body: finitaryExtensive_of_reflective (sheafificationAdjunction _ _)

中文:
实例 [有限广延
  签名: D] [有Pullbacks D] [有Sheafify J D] :
  定义体: finitaryExtensive_of_reflective (sheafificationAdjunction _ _)

Depends on / 依赖: finitaryExtensive_of_reflective, sheafificationAdjunction
-/
instance [FinitaryExtensive D] [HasPullbacks D] [HasSheafify J D] :
    FinitaryExtensive (Sheaf J D) :=
  finitaryExtensive_of_reflective (sheafificationAdjunction _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Adhesive
  signature: D] [HasPullbacks D] [HasPushouts D] [HasSheafify J D] :
  body: adhesive_of_reflective (sheafificationAdjunction _ _)

中文:
实例 [Adhesive
  签名: D] [有Pullbacks D] [有Pushouts D] [有Sheafify J D] :
  定义体: adhesive_of_reflective (sheafificationAdjunction _ _)

Depends on / 依赖: adhesive_of_reflective, sheafificationAdjunction
-/
instance [Adhesive D] [HasPullbacks D] [HasPushouts D] [HasSheafify J D] :
    Adhesive (Sheaf J D) :=
  adhesive_of_reflective (sheafificationAdjunction _ _)

/--
Instance `SheafOfTypes.finitary_extensive` / 实例 `SheafOfTypes.finitary_extensive`

English:
instance SheafOfTypes.finitary_extensive
  signature: [HasSheafify J (Type w)]
  body: inferInstance

中文:
实例 SheafOfTypes.finitary_extensive
  签名: [有Sheafify J (类型 w)]
  定义体: inferInstance
-/
instance SheafOfTypes.finitary_extensive [HasSheafify J (Type w)] :
    FinitaryExtensive (Sheaf J (Type w)) :=
  inferInstance

/--
Instance `SheafOfTypes.adhesive` / 实例 `SheafOfTypes.adhesive`

English:
instance SheafOfTypes.adhesive
  signature: [HasSheafify J (Type w)]
  body: inferInstance

中文:
实例 SheafOfTypes.adhesive
  签名: [有Sheafify J (类型 w)]
  定义体: inferInstance
-/
instance SheafOfTypes.adhesive [HasSheafify J (Type w)] :
    Adhesive (Sheaf J (Type w)) :=
  inferInstance

/--
Instance `SheafOfTypes.balanced` / 实例 `SheafOfTypes.balanced`

English:
instance SheafOfTypes.balanced
  signature: [HasSheafify J (Type w)]
  body: inferInstance

中文:
实例 SheafOfTypes.balanced
  签名: [有Sheafify J (类型 w)]
  定义体: inferInstance
-/
instance SheafOfTypes.balanced [HasSheafify J (Type w)] :
    Balanced (Sheaf J (Type w)) :=
  inferInstance

end CategoryTheory
