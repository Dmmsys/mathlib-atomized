/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GuitartExact.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Guitart exact squares and Kan extensions

Given a Guitart exact square `w : T ⋙ R ⟶ L ⋙ B`,
```
     T
  C₁ ⥤ C₂
L | | R
  v v
  C₃ ⥤ C₄
     B
```
we show that an extension `F' : C₄ ⥤ D` of `F : C₂ ⥤ D` along `R`
is a pointwise left Kan extension at `B.obj X₃` iff
the composition `T ⋙ F'` is a pointwise left Kan extension at `X₃`
of `B ⋙ F'`.

When suitable (pointwise) left Kan extensions exist, we also show that
the natural transformation of functors `(C₂ ⥤ D) ⥤ C₃ ⥤ D`
`(whiskeringLeft C₁ C₂ D).obj T ⋙ L.lan ⟶ R.lan ⋙ (whiskeringLeft C₃ C₄ D).obj B`
induced by a Guitart exact square `w` is an isomorphism.

## References

* https://ncatlab.org/nlab/show/exact+square

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} {D : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  [Category.{v₅} D]

namespace Functor.LeftExtension

variable {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
  {F : C₂ ⥤ D} (E : R.LeftExtension F)

/--
Definition of `compTwoSquare` / `compTwoSquare` 的定义

English:
abbreviation compTwoSquare
  signature: (w : TwoSquare T L R B)
  body: LeftExtension.mk (B ⋙ E.right)
    (whiskerLeft _ E.hom ≫ (associator _ _ _).inv ≫
      whiskerRight w.natTrans _ ≫ (associator _ _ _).hom)

中文:
缩写 compTwoSquare
  签名: (w : TwoSquare T L R B)
  定义体: LeftExtension.mk (B ⋙ E.right)
    (whiskerLeft _ E.hom ≫ (associator _ _ _).inv ≫
      whiskerRight w.natTrans _ ≫ (associator _ _ _).hom)

Depends on / 依赖: E.hom, E.right, LeftExtension, LeftExtension.mk, associator, natTrans, w.natTrans, whiskerLeft, whiskerRight
-/
abbrev compTwoSquare (w : TwoSquare T L R B) : L.LeftExtension (T ⋙ F) :=
  LeftExtension.mk (B ⋙ E.right)
    (whiskerLeft _ E.hom ≫ (associator _ _ _).inv ≫
      whiskerRight w.natTrans _ ≫ (associator _ _ _).hom)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isPointwiseLeftKanExtensionAtCompTwoSquareEquiv` / `isPointwiseLeftKanExtensionAtCompTwoSquareEquiv` 的定义

English:
definition isPointwiseLeftKanExtensionAtCompTwoSquareEquiv
  body: by
  refine Equiv.trans ?_ (Final.isColimitWhiskerEquiv (w.costructuredArrowRightwards X₃) _)
  exact IsColimit.equivIsoColimit (Cocone.ext (Iso.refl _))

中文:
定义 isPointwiseLeftKanExtensionAtCompTwoSquareEquiv
  定义体: by
  refine Equiv.trans ?_ (Final.isColimitWhiskerEquiv (w.costructuredArrowRightwards X₃) _)
  exact IsColimit.equivIsoColimit (Cocone.ext (Iso.refl _))

Depends on / 依赖: Cocone, Cocone.ext, Equiv.trans, Final.isColimitWhiskerEquiv, IsColimit, IsColimit.equivIsoColimit, Iso.refl, costructuredArrowRightwards, equivIsoColimit, isColimitWhiskerEquiv, w.costructuredArrowRightwards
-/
noncomputable def isPointwiseLeftKanExtensionAtCompTwoSquareEquiv
    (w : TwoSquare T L R B) (X₃ : C₃) [Final (w.costructuredArrowRightwards X₃)] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtensionAt X₃ ≃
      E.IsPointwiseLeftKanExtensionAt (B.obj X₃) := by
  refine Equiv.trans ?_ (Final.isColimitWhiskerEquiv (w.costructuredArrowRightwards X₃) _)
  exact IsColimit.equivIsoColimit (Cocone.ext (Iso.refl _))

/--
lemma `nonempty_isPointwiseLeftKanExtensionAt_compTwoSquare_iff` / 引理 `nonempty_isPointwiseLeftKanExtensionAt_compTwoSquare_iff`

English:
lemma nonempty_isPointwiseLeftKanExtensionAt_compTwoSquare_iff
  proof: (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _).nonempty_congr

中文:
引理 nonempty_isPointwiseLeftKanExtensionAt_compTwoSquare_iff
  证明: (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _).nonempty_congr

Depends on / 依赖: E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv, isPointwiseLeftKanExtensionAtCompTwoSquareEquiv, nonempty_congr
-/
lemma nonempty_isPointwiseLeftKanExtensionAt_compTwoSquare_iff
    (w : TwoSquare T L R B) (X₃ : C₃) [Final (w.costructuredArrowRightwards X₃)] :
    Nonempty ((E.compTwoSquare w).IsPointwiseLeftKanExtensionAt X₃) ↔
      Nonempty (E.IsPointwiseLeftKanExtensionAt (B.obj X₃)) :=
  (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _).nonempty_congr

variable {E} in
/--
Definition of `IsPointwiseLeftKanExtension.compTwoSquare` / `IsPointwiseLeftKanExtension.compTwoSquare` 的定义

English:
definition IsPointwiseLeftKanExtension.compTwoSquare
  body: fun X₃ => (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w X₃).symm (h _)

中文:
定义 IsPointwiseLeftKanExtension.compTwoSquare
  定义体: fun X₃ => (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w X₃).symm (h _)

Depends on / 依赖: E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv, isPointwiseLeftKanExtensionAtCompTwoSquareEquiv
-/
noncomputable def IsPointwiseLeftKanExtension.compTwoSquare
    (h : E.IsPointwiseLeftKanExtension) (w : TwoSquare T L R B) [w.GuitartExact] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtension :=
  fun X₃ => (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w X₃).symm (h _)

/--
Definition of `isPointwiseLeftKanExtensionOfCompTwoSquare` / `isPointwiseLeftKanExtensionOfCompTwoSquare` 的定义

English:
definition isPointwiseLeftKanExtensionOfCompTwoSquare
  body: fun X₄ => E.isPointwiseLeftKanExtensionAtOfIso'
    (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _ (h (B.objPreimage X₄)))
    (B.objObjPreimageIso X₄)

中文:
定义 isPointwiseLeftKanExtensionOfCompTwoSquare
  定义体: fun X₄ => E.isPointwiseLeftKanExtensionAtOfIso'
    (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _ (h (B.objPreimage X₄)))
    (B.objObjPreimageIso X₄)

Depends on / 依赖: B.objObjPreimageIso, B.objPreimage, E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv, E.isPointwiseLeftKanExtensionAtOfIso, hasPushout_op_iff_hasPullback, isPointwiseLeftKanExtensionAtCompTwoSquareEquiv, isPointwiseLeftKanExtensionAtOfIso, objObjPreimageIso, objPreimage
-/
noncomputable def isPointwiseLeftKanExtensionOfCompTwoSquare
    (w : TwoSquare T L R B) [w.GuitartExact] [B.EssSurj]
    (h : (E.compTwoSquare w).IsPointwiseLeftKanExtension) :
    E.IsPointwiseLeftKanExtension :=
  fun X₄ => E.isPointwiseLeftKanExtensionAtOfIso'
    (E.isPointwiseLeftKanExtensionAtCompTwoSquareEquiv w _ (h (B.objPreimage X₄)))
    (B.objObjPreimageIso X₄)

/--
Definition of `isPointwiseLeftKanExtensionEquivOfGuitartExact` / `isPointwiseLeftKanExtensionEquivOfGuitartExact` 的定义

English:
definition isPointwiseLeftKanExtensionEquivOfGuitartExact
  body: E.isPointwiseLeftKanExtensionOfCompTwoSquare w h
  invFun h := h.compTwoSquare w
  left_inv _ := by subsingleton
  right_inv _ := by subsingleton

中文:
定义 isPointwiseLeftKanExtensionEquivOfGuitartExact
  定义体: E.isPointwiseLeftKanExtensionOfCompTwoSquare w h
  invFun h := h.compTwoSquare w
  left_inv _ := by subsingleton
  right_inv _ := by subsingleton

Depends on / 依赖: E.isPointwiseLeftKanExtensionOfCompTwoSquare, hasPushout_unop_iff_hasPullback, isPointwiseLeftKanExtensionOfCompTwoSquare
-/
noncomputable def isPointwiseLeftKanExtensionEquivOfGuitartExact
    (w : TwoSquare T L R B) [w.GuitartExact] [B.EssSurj] :
    (E.compTwoSquare w).IsPointwiseLeftKanExtension ≃
      E.IsPointwiseLeftKanExtension where
  toFun h := E.isPointwiseLeftKanExtensionOfCompTwoSquare w h
  invFun h := h.compTwoSquare w
  left_inv _ := by subsingleton
  right_inv _ := by subsingleton

end Functor.LeftExtension

namespace TwoSquare

variable {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
  (w : TwoSquare T L R B)

include w

/--
lemma `hasPointwiseLeftKanExtensionAt_iff` / 引理 `hasPointwiseLeftKanExtensionAt_iff`

English:
lemma hasPointwiseLeftKanExtensionAt_iff
  proof: by
  dsimp [Functor.HasPointwiseLeftKanExtensionAt]
  rw [← Functor.Final.hasColimit_comp_iff (w.costructuredArrowRightwards X₃)]
  rfl

中文:
引理 hasPointwiseLeftKanExtensionAt_iff
  证明: by
  dsimp [Functor.HasPointwiseLeftKanExtensionAt]
  rw [← Functor.Final.hasColimit_comp_iff (w.costructuredArrowRightwards X₃)]
  rfl

Depends on / 依赖: Functor, Functor.Final.hasColimit_comp_iff, Functor.HasPointwiseLeftKanExtensionAt, HasPointwiseLeftKanExtensionAt, costructuredArrowRightwards, hasColimit_comp_iff, w.costructuredArrowRightwards
-/
lemma hasPointwiseLeftKanExtensionAt_iff
    (F : C₂ ⥤ D) (X₃ : C₃) [(w.costructuredArrowRightwards X₃).Final] :
    L.HasPointwiseLeftKanExtensionAt (T ⋙ F) X₃ ↔
      R.HasPointwiseLeftKanExtensionAt F (B.obj X₃) := by
  dsimp [Functor.HasPointwiseLeftKanExtensionAt]
  rw [← Functor.Final.hasColimit_comp_iff (w.costructuredArrowRightwards X₃)]
  rfl

/--
lemma `hasPointwiseLeftKanExtension_iff` / 引理 `hasPointwiseLeftKanExtension_iff`

English:
lemma hasPointwiseLeftKanExtension_iff
  given: [w.GuitartExact] [B.EssSurj] (F : C₂ ⥤ D)
  proof: by
  dsimp [Functor.HasPointwiseLeftKanExtension]
  simp only [hasPointwiseLeftKanExtensionAt_iff w]
  refine ⟨fun h X₄ => ?_, fun h _ => h _⟩
  rw [← Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso _ _ (B.objObjPreimageIso X₄)]
  apply h

中文:
引理 hasPointwiseLeftKanExtension_iff
  条件: [w.GuitartExact] [B.本质满射] (F : C₂ ⥤ D)
  证明: by
  dsimp [Functor.HasPointwiseLeftKanExtension]
  simp only [hasPointwiseLeftKanExtensionAt_iff w]
  refine ⟨fun h X₄ => ?_, fun h _ => h _⟩
  rw [← Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso _ _ (B.objObjPreimageIso X₄)]
  apply h

Depends on / 依赖: B.objObjPreimageIso, Functor, Functor.HasPointwiseLeftKanExtension, Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso, HasPointwiseLeftKanExtension, hasPointwiseLeftKanExtensionAt_iff, hasPointwiseLeftKanExtensionAt_iff_of_iso, objObjPreimageIso
-/
lemma hasPointwiseLeftKanExtension_iff [w.GuitartExact] [B.EssSurj] (F : C₂ ⥤ D) :
    L.HasPointwiseLeftKanExtension (T ⋙ F) ↔
      R.HasPointwiseLeftKanExtension F := by
  dsimp [Functor.HasPointwiseLeftKanExtension]
  simp only [hasPointwiseLeftKanExtensionAt_iff w]
  refine ⟨fun h X₄ => ?_, fun h _ => h _⟩
  rw [← Functor.hasPointwiseLeftKanExtensionAt_iff_of_iso _ _ (B.objObjPreimageIso X₄)]
  apply h

/--
lemma `hasPointwiseLeftKanExtension` / 引理 `hasPointwiseLeftKanExtension`

English:
lemma hasPointwiseLeftKanExtension
  statement: [w.GuitartExact]
  proof: ((R.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    F).compTwoSquare w).hasPointwiseLeftKanExtension

中文:
引理 hasPointwiseLeftKanExtension
  结论: [w.GuitartExact]
  证明: ((R.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    F).compTwoSquare w).hasPointwiseLeftKanExtension

Depends on / 依赖: R.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension, compTwoSquare, hasPointwiseLeftKanExtension, pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
-/
lemma hasPointwiseLeftKanExtension [w.GuitartExact]
    (F : C₂ ⥤ D) [R.HasPointwiseLeftKanExtension F] :
    L.HasPointwiseLeftKanExtension (T ⋙ F) :=
  ((R.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
    F).compTwoSquare w).hasPointwiseLeftKanExtension

/--
lemma `hasLeftKanExtension` / 引理 `hasLeftKanExtension`

English:
lemma hasLeftKanExtension
  statement: [w.GuitartExact]
  proof: by
  have := w.hasPointwiseLeftKanExtension F
  infer_instance

中文:
引理 hasLeftKanExtension
  结论: [w.GuitartExact]
  证明: by
  have := w.hasPointwiseLeftKanExtension F
  infer_instance

Depends on / 依赖: hasPointwiseLeftKanExtension, infer_instance, w.hasPointwiseLeftKanExtension
-/
lemma hasLeftKanExtension [w.GuitartExact]
    (F : C₂ ⥤ D) [R.HasPointwiseLeftKanExtension F] :
    L.HasLeftKanExtension (T ⋙ F) := by
  have := w.hasPointwiseLeftKanExtension F
  infer_instance

section

open CategoryTheory.Functor

section

variable [forall (F : C₁ ⥤ D), L.HasLeftKanExtension F] [forall (F : C₂ ⥤ D), R.HasLeftKanExtension F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The base change natural transformation for left Kan extensions associated to
a 2-square. -/
@[simps -isSimp]
/--
Definition of `lanBaseChange` / `lanBaseChange` 的定义

English:
definition lanBaseChange
  signature: :
  body: ((L.lanAdjunction D).homEquiv _ _).symm
      ((LeftExtension.mk _ (R.lanUnit.app F)).compTwoSquare w).hom
  naturality {F₁ F₂} τ := by
    dsimp
    refine (Adjunction.homEquiv_naturality_left_symm ..).symm.trans
      (Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm ..))
    congr 1
    ext

中文:
定义 lanBaseChange
  签名: :
  定义体: ((L.lanAdjunction D).homEquiv _ _).symm
      ((LeftExtension.mk _ (R.lanUnit.app F)).compTwoSquare w).hom
  naturality {F₁ F₂} τ := by
    dsimp
    refine (Adjunction.homEquiv_naturality_left_symm ..).symm.trans
      (Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm ..))
    congr 1
    ext

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm, Eq.trans, L.lanAdjunction, LeftExtension, LeftExtension.mk, R.lanUnit.app, R.lanUnit.naturality_app, T.obj, compTwoSquare, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right_symm, lanAdjunction, lanUnit, naturality, naturality_app, reassoc_of, symm.trans
-/
noncomputable def lanBaseChange :
    (whiskeringLeft C₁ C₂ D).obj T ⋙ L.lan ⟶ R.lan ⋙ (whiskeringLeft C₃ C₄ D).obj B where
  app F :=
    ((L.lanAdjunction D).homEquiv _ _).symm
      ((LeftExtension.mk _ (R.lanUnit.app F)).compTwoSquare w).hom
  naturality {F₁ F₂} τ := by
    dsimp
    refine (Adjunction.homEquiv_naturality_left_symm ..).symm.trans
      (Eq.trans ?_ (Adjunction.homEquiv_naturality_right_symm ..))
    congr 1
    ext X
    have := R.lanUnit.naturality_app (T.obj X) τ
    simp [reassoc_of% this]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso_lanBaseChange_app_iff` / 引理 `isIso_lanBaseChange_app_iff`

English:
lemma isIso_lanBaseChange_app_iff
  given: (F : C₂ ⥤ D)
  proof: by
  rw [lanBaseChange_app]; rw [isIso_lanAdjunction_homEquiv_symm_iff]
  simp

中文:
引理 isIso_lanBaseChange_app_iff
  条件: (F : C₂ ⥤ D)
  证明: by
  rw [lanBaseChange_app]; rw [isIso_lanAdjunction_homEquiv_symm_iff]
  simp

Depends on / 依赖: isIso_lanAdjunction_homEquiv_symm_iff, lanBaseChange_app
-/
lemma isIso_lanBaseChange_app_iff (F : C₂ ⥤ D) :
    IsIso (w.lanBaseChange.app F) ↔
      IsLeftKanExtension _ ((LeftExtension.mk _ (R.lanUnit.app F)).compTwoSquare w).hom := by
  rw [lanBaseChange_app]; rw [isIso_lanAdjunction_homEquiv_symm_iff]
  simp

/--
Instance `isIso_lanBaseChange_app` / 实例 `isIso_lanBaseChange_app`

English:
instance isIso_lanBaseChange_app
  signature: (F : C₂ ⥤ D)
  body: by
  rw [isIso_lanBaseChange_app_iff]
  let hF := isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _ (R.lanUnit.app F)
  exact (hF.compTwoSquare w).isLeftKanExtension

中文:
实例 isIso_lanBaseChange_app
  签名: (F : C₂ ⥤ D)
  定义体: by
  rw [isIso_lanBaseChange_app_iff]
  let hF := isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _ (R.lanUnit.app F)
  exact (hF.compTwoSquare w).isLeftKanExtension

Depends on / 依赖: R.lanUnit.app, compTwoSquare, hF.compTwoSquare, isIso_lanBaseChange_app_iff, isLeftKanExtension, isPointwiseLeftKanExtensionOfIsLeftKanExtension, lanUnit
-/
instance isIso_lanBaseChange_app (F : C₂ ⥤ D)
    [R.HasPointwiseLeftKanExtension F] [w.GuitartExact] :
    IsIso (w.lanBaseChange.app F) := by
  rw [isIso_lanBaseChange_app_iff]
  let hF := isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _ (R.lanUnit.app F)
  exact (hF.compTwoSquare w).isLeftKanExtension

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: (F : C₁ ⥤ D), L.HasLeftKanExtension F]
  body: by
  rw [NatTrans.isIso_iff_isIso_app]
  infer_instance

中文:
实例 [对任意
  签名: (F : C₁ ⥤ D), L.有LeftKanExtension F]
  定义体: by
  rw [NatTrans.isIso_iff_isIso_app]
  infer_instance

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, infer_instance, isIso_iff_isIso_app
-/
instance [forall (F : C₁ ⥤ D), L.HasLeftKanExtension F]
    [forall (F : C₂ ⥤ D), R.HasPointwiseLeftKanExtension F] [w.GuitartExact] :
    IsIso (w.lanBaseChange (D := D)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  infer_instance

end

end TwoSquare

end CategoryTheory
