/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.FunctorToTypes

/-!
# Yoneda preserves certain colimits

Given a bifunctor `F : J ⥤ Cᵒᵖ ⥤ Type v`, we prove the isomorphism
`Hom(YX, colim_j F(j, -)) ≅ colim_j Hom(YX, F(j, -))`, where `Y` is the Yoneda embedding.

We state this in two ways. One is functorial in `X` and stated as a natural isomorphism of functors
`yoneda.op ⋙ yoneda.obj (colimit F) ≅ yoneda.op ⋙ colimit (F ⋙ yoneda)`, and from this we
deduce the more traditional preservation statement
`PreservesColimit F (coyoneda.obj (op (yoneda.obj X)))`.

The proof combines the Yoneda lemma with the fact that colimits in functor categories are computed
pointwise.

## See also

There is also a relative version of this statement where `F : J ⥤ Over A` for some presheaf
`A`, see `Mathlib/CategoryTheory/Comma/Presheaf/Colimit.lean`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open CategoryTheory.Limits Opposite CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]

variable {J : Type u₂} [Category.{v₂} J] [HasColimitsOfShape J (Type v₁)]
  [HasColimitsOfShape J (Type (max u₁ v₁))] (F : J ⥤ Cᵒᵖ ⥤ Type v₁)

/--
Definition of `yonedaYonedaColimit` / `yonedaYonedaColimit` 的定义

English:
definition yonedaYonedaColimit
  signature: :
  body: calc
  yoneda.op ⋙ yoneda.obj (colimit F)
    ≅ colimit F ⋙ uliftFunctor.{u₁} := yonedaOpCompYonedaObj (colimit F)
  _ ≅ F.flip ⋙ colim ⋙ uliftFunctor.{u₁} :=
        isoWhiskerRight (colimitIsoFlipCompColim F) uliftFunctor.{u₁}
  _ ≅ F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} ⋙ colim :=
        isoWhiskerLeft F.flip (preservesColimitNatIso uliftFunctor.{u₁})
  _ ≅ (yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F) ⋙ colim := isoWhiskerRight
        (isoWhiskerRight largeCurriedYonedaLemma.symm ((whiskeringLeft _ _ _).obj F)) colim
  _ ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) :=
        isoWhiskerLeft yoneda.op (colimitIsoFlipCompColim (F ⋙ yoneda)).symm

中文:
定义 yonedaYonedaColimit
  签名: :
  定义体: calc
  yoneda.op ⋙ yoneda.obj (colimit F)
    ≅ colimit F ⋙ uliftFunctor.{u₁} := yonedaOpCompYonedaObj (colimit F)
  _ ≅ F.flip ⋙ colim ⋙ uliftFunctor.{u₁} :=
        isoWhiskerRight (colimitIsoFlipCompColim F) uliftFunctor.{u₁}
  _ ≅ F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} ⋙ colim :=
        isoWhiskerLeft F.flip (preservesColimitNatIso uliftFunctor.{u₁})
  _ ≅ (yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F) ⋙ colim := isoWhiskerRight
        (isoWhiskerRight largeCurriedYonedaLemma.symm ((whiskeringLeft _ _ _).obj F)) colim
  _ ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) :=
        isoWhiskerLeft yoneda.op (colimitIsoFlipCompColim (F ⋙ yoneda)).symm
-/
noncomputable def yonedaYonedaColimit :
    yoneda.op ⋙ yoneda.obj (colimit F) ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) := calc
  yoneda.op ⋙ yoneda.obj (colimit F)
    ≅ colimit F ⋙ uliftFunctor.{u₁} := yonedaOpCompYonedaObj (colimit F)
  _ ≅ F.flip ⋙ colim ⋙ uliftFunctor.{u₁} :=
        isoWhiskerRight (colimitIsoFlipCompColim F) uliftFunctor.{u₁}
  _ ≅ F.flip ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} ⋙ colim :=
        isoWhiskerLeft F.flip (preservesColimitNatIso uliftFunctor.{u₁})
  _ ≅ (yoneda.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj F) ⋙ colim := isoWhiskerRight
        (isoWhiskerRight largeCurriedYonedaLemma.symm ((whiskeringLeft _ _ _).obj F)) colim
  _ ≅ yoneda.op ⋙ colimit (F ⋙ yoneda) :=
        isoWhiskerLeft yoneda.op (colimitIsoFlipCompColim (F ⋙ yoneda)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `yonedaYonedaColimit_app_inv` / 定理 `yonedaYonedaColimit_app_inv`

English:
theorem yonedaYonedaColimit_app_inv
  given: {X : C}
  statement: ((yonedaYonedaColimit F).app (op X)).inv =
  proof: by
  dsimp [yonedaYonedaColimit]
  simp only [Iso.cancel_iso_hom_left]
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_post]; rw [ι_colimMap_assoc]
  simp only [← CategoryTheory.Functor.assoc, comp_evaluation]
  rw [ι_preservesColimitIso_inv_assoc]
  simp only [← comp_evaluation, comp_obj, evaluation_obj_obj, yoneda_obj_obj, uliftFunctor_obj,
    whiskerLeft_app, uliftFunctor_map, Functor.comp_map, evaluation_obj_map, yoneda_map_app]
  ext η Y f
  dsimp [largeCurriedYonedaLemma, yonedaOpCompYonedaObj, yonedaEquiv]
  simp only [← comp_apply, Category.assoc, colimitObjIsoColimitCompEvaluation_ι_inv,
    ← NatTrans.naturality, ← NatTrans.naturality_assoc, yoneda_obj_obj, yoneda_obj_map,
    Quiver.Hom.unop_op]
  simp

中文:
定理 yonedaYonedaColimit_app_inv
  条件: {X : C}
  结论: ((yonedaYonedaColimit F).app (op X)).inv =
  证明: by
  dsimp [yonedaYonedaColimit]
  simp only [Iso.cancel_iso_hom_left]
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_post]; rw [ι_colimMap_assoc]
  simp only [← CategoryTheory.Functor.assoc, comp_evaluation]
  rw [ι_preservesColimitIso_inv_assoc]
  simp only [← comp_evaluation, comp_obj, evaluation_obj_obj, yoneda_obj_obj, uliftFunctor_obj,
    whiskerLeft_app, uliftFunctor_map, Functor.comp_map, evaluation_obj_map, yoneda_map_app]
  ext η Y f
  dsimp [largeCurriedYonedaLemma, yonedaOpCompYonedaObj, yonedaEquiv]
  simp only [← comp_apply, Category.assoc, colimitObjIsoColimitCompEvaluation_ι_inv,
    ← NatTrans.naturality, ← NatTrans.naturality_assoc, yoneda_obj_obj, yoneda_obj_map,
    Quiver.Hom.unop_op]
  simp

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.assoc, Functor, Functor.comp_map, Iso.cancel_iso_hom_left, cancel_iso_hom_left, colimit, colimit.hom_ext, comp_evaluation, comp_map, comp_obj, evaluation_obj_map, evaluation_obj_obj, hom_ext, largeCurriedYonedaLemma, uliftFunctor_map, uliftFunctor_obj, whiskerLeft_app, yonedaEquiv, yonedaOpCompYonedaObj
-/
theorem yonedaYonedaColimit_app_inv {X : C} : ((yonedaYonedaColimit F).app (op X)).inv =
    (colimitObjIsoColimitCompEvaluation _ _).hom ≫
      (colimit.post F (coyoneda.obj (op (yoneda.obj X)))) := by
  dsimp [yonedaYonedaColimit]
  simp only [Iso.cancel_iso_hom_left]
  apply colimit.hom_ext
  intro j
  rw [colimit.ι_post]; rw [ι_colimMap_assoc]
  simp only [← CategoryTheory.Functor.assoc, comp_evaluation]
  rw [ι_preservesColimitIso_inv_assoc]
  simp only [← comp_evaluation, comp_obj, evaluation_obj_obj, yoneda_obj_obj, uliftFunctor_obj,
    whiskerLeft_app, uliftFunctor_map, Functor.comp_map, evaluation_obj_map, yoneda_map_app]
  ext η Y f
  dsimp [largeCurriedYonedaLemma, yonedaOpCompYonedaObj, yonedaEquiv]
  simp only [← comp_apply, Category.assoc, colimitObjIsoColimitCompEvaluation_ι_inv,
    ← NatTrans.naturality, ← NatTrans.naturality_assoc, yoneda_obj_obj, yoneda_obj_map,
    Quiver.Hom.unop_op]
  simp

set_option backward.isDefEq.respectTransparency false in
noncomputable instance {X : C} : PreservesColimit F (coyoneda.obj (op (yoneda.obj X))) := by
  suffices IsIso (colimit.post F (coyoneda.obj (op (yoneda.obj X)))) from
    preservesColimit_of_isIso_post _ _
  suffices colimit.post F (coyoneda.obj (op (yoneda.obj X))) =
      (colimitObjIsoColimitCompEvaluation _ _).inv ≫ ((yonedaYonedaColimit F).app (op X)).inv from
    this ▸ inferInstance
  rw [yonedaYonedaColimit_app_inv]; rw [Iso.inv_hom_id_assoc]

end CategoryTheory
