/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Limit properties relating to the (co)yoneda embedding.

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `PUnit`.
(This is used in characterising cofinal functors.)

We also show the (co)yoneda embeddings preserve limits and jointly reflect them.
-/

@[expose] public section

assert_not_exists AddCommMonoid

open Opposite CategoryTheory Limits ConcreteCategory

universe t w w' v u

namespace CategoryTheory

namespace Coyoneda

variable {C : Type u} [Category.{v} C]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The colimit cocone over `coyoneda.obj X`, with cocone point `PUnit`.
-/
@[simps]
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: (X : Cᵒᵖ)
  body: PUnit
  ι := { app _ := ↾fun _ => by cat_disch }

中文:
定义 colimitCocone
  签名: (X : Cᵒᵖ)
  定义体: PUnit
  ι := { app _ := ↾fun _ => by cat_disch }
-/
def colimitCocone (X : Cᵒᵖ) : Cocone (coyoneda.obj X) where
  pt := PUnit
  ι := { app _ := ↾fun _ => by cat_disch }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: (X : Cᵒᵖ)
  body: ↾fun _ => s.ι.app (unop X) (𝟙 _)
  fac s Y := by
    ext f
    simpa using congr_hom (s.w f).symm (𝟙 (unop X))
  uniq s m w := by
    ext ⟨⟩
    simp [← w]

中文:
定义 colimitCoconeIsColimit
  签名: (X : Cᵒᵖ)
  定义体: ↾fun _ => s.ι.app (unop X) (𝟙 _)
  fac s Y := by
    ext f
    simpa using congr_hom (s.w f).symm (𝟙 (unop X))
  uniq s m w := by
    ext ⟨⟩
    simp [← w]
-/
def colimitCoconeIsColimit (X : Cᵒᵖ) : IsColimit (colimitCocone X) where
  desc s := ↾fun _ => s.ι.app (unop X) (𝟙 _)
  fac s Y := by
    ext f
    simpa using congr_hom (s.w f).symm (𝟙 (unop X))
  uniq s m w := by
    ext ⟨⟩
    simp [← w]

instance (X : Cᵒᵖ) : HasColimit (coyoneda.obj X) :=
  HasColimit.mk
    { cocone := _
      isColimit := colimitCoconeIsColimit X }

/--
Definition of `colimitCoyonedaIso` / `colimitCoyonedaIso` 的定义

English:
definition colimitCoyonedaIso
  signature: (X : Cᵒᵖ)
  body: by
  apply colimit.isoColimitCocone
    { cocone := _
      isColimit := colimitCoconeIsColimit X }

中文:
定义 colimitCoyonedaIso
  签名: (X : Cᵒᵖ)
  定义体: by
  apply colimit.isoColimitCocone
    { cocone := _
      isColimit := colimitCoconeIsColimit X }

Depends on / 依赖: cocone, colimit, colimit.isoColimitCocone, colimitCoconeIsColimit, isColimit, isoColimitCocone
-/
noncomputable def colimitCoyonedaIso (X : Cᵒᵖ) : colimit (coyoneda.obj X) ≅ PUnit := by
  apply colimit.isoColimitCocone
    { cocone := _
      isColimit := colimitCoconeIsColimit X }

end Coyoneda

variable {C : Type u} [Category.{v} C]

open Limits

section

variable {J : Type w} [Category.{t} J]

set_option backward.defeqAttrib.useBackward true in
/-- The cone of `F` corresponding to an element in `(F ⋙ yoneda.obj X).sections`. -/
@[simps]
/--
Definition of `Limits.coneOfSectionCompYoneda` / `Limits.coneOfSectionCompYoneda` 的定义

English:
definition Limits.coneOfSectionCompYoneda
  signature: (F : J ⥤ Cᵒᵖ) (X : C)
  body: Opposite.op X
  π := {
    app := fun j => (s.val j).op
    naturality _ _ f := by simp [(s.property f).symm] }

中文:
定义 Limits.coneOfSectionCompYoneda
  签名: (F : J ⥤ Cᵒᵖ) (X : C)
  定义体: Opposite.op X
  π := {
    app := fun j => (s.val j).op
    naturality _ _ f := by simp [(s.property f).symm] }

Depends on / 依赖: Opposite, Opposite.op, S.prop
-/
def Limits.coneOfSectionCompYoneda (F : J ⥤ Cᵒᵖ) (X : C)
    (s : (F ⋙ yoneda.obj X).sections) : Cone F where
  pt := Opposite.op X
  π := {
    app := fun j => (s.val j).op
    naturality _ _ f := by simp [(s.property f).symm] }

/--
Instance `yoneda_preservesLimit` / 实例 `yoneda_preservesLimit`

English:
instance yoneda_preservesLimit
  signature: (F : J ⥤ Cᵒᵖ) (X : C)
  body: by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨(hc.lift (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩)).unop,
      fun j => Quiver.Hom.op_inj (hc.fac (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) j),
      fun m hm => Quiver.Hom.op_inj
        (hc.uniq (Limits.coneOfSectionCompYoneda F X ⟨s, 

中文:
实例 yoneda_preservesLimit
  签名: (F : J ⥤ Cᵒᵖ) (X : C)
  定义体: by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨(hc.lift (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩)).unop,
      fun j => Quiver.Hom.op_inj (hc.fac (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) j),
      fun m hm => Quiver.Hom.op_inj
        (hc.uniq (Limits.coneOfSectionCompYoneda F X ⟨s, 

Depends on / 依赖: Limits, Limits.coneOfSectionCompYoneda, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, Types.isLimit_iff, coneOfSectionCompYoneda, hc.fac, hc.lift, hc.uniq, isCardinalFiltered_of_hasTerminal, isLimit_iff, op_inj, unop_inj
-/
instance yoneda_preservesLimit (F : J ⥤ Cᵒᵖ) (X : C) :
    PreservesLimit F (yoneda.obj X) where
  preserves {c} hc := by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨(hc.lift (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩)).unop,
      fun j => Quiver.Hom.op_inj (hc.fac (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) j),
      fun m hm => Quiver.Hom.op_inj
        (hc.uniq (Limits.coneOfSectionCompYoneda F X ⟨s, hs⟩) _
          (fun j => Quiver.Hom.unop_inj (hm j)))⟩

variable (J) in
/--
Instance `yoneda_preservesLimitsOfShape` / 实例 `yoneda_preservesLimitsOfShape`

English:
instance yoneda_preservesLimitsOfShape
  signature: (X : C)

中文:
实例 yoneda_preservesLimitsOfShape
  签名: (X : C)
-/
noncomputable instance yoneda_preservesLimitsOfShape (X : C) :
    PreservesLimitsOfShape J (yoneda.obj X) where

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `yonedaJointlyReflectsLimits` / `yonedaJointlyReflectsLimits` 的定义

English:
definition yonedaJointlyReflectsLimits
  signature: (F : J ⥤ Cᵒᵖ) (c : Cone F)
  body: ((hc s.pt.unop).lift ((yoneda.obj s.pt.unop).mapCone s) (𝟙 _)).op
  fac s j := Quiver.Hom.unop_inj (by
    simpa using congr_hom ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 (unop s.pt)))
  uniq s m hm := Quiver.Hom.unop_inj (by
    apply (Types.isLimitEquivSections (hc s.pt.unop)).i

中文:
定义 yonedaJointlyReflectsLimits
  签名: (F : J ⥤ Cᵒᵖ) (c : Cone F)
  定义体: ((hc s.pt.unop).lift ((yoneda.obj s.pt.unop).mapCone s) (𝟙 _)).op
  fac s j := Quiver.Hom.unop_inj (by
    simpa using congr_hom ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 (unop s.pt)))
  uniq s m hm := Quiver.Hom.unop_inj (by
    apply (Types.isLimitEquivSections (hc s.pt.unop)).i

Depends on / 依赖: mapCone, s.pt.unop, yoneda, yoneda.obj
-/
def yonedaJointlyReflectsLimits (F : J ⥤ Cᵒᵖ) (c : Cone F)
    (hc : forall X : C, IsLimit ((yoneda.obj X).mapCone c)) : IsLimit c where
  lift s := ((hc s.pt.unop).lift ((yoneda.obj s.pt.unop).mapCone s) (𝟙 _)).op
  fac s j := Quiver.Hom.unop_inj (by
    simpa using congr_hom ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 (unop s.pt)))
  uniq s m hm := Quiver.Hom.unop_inj (by
    apply (Types.isLimitEquivSections (hc s.pt.unop)).injective
    ext j
    have eq := congr_hom ((hc s.pt.unop).fac ((yoneda.obj s.pt.unop).mapCone s) j) (𝟙 (unop s.pt))
    dsimp [Types.isLimitEquivSections, Types.sectionOfCone]
    simp_all [← hm])

/--
Definition of `Limits.Cocone.isColimitYonedaEquiv` / `Limits.Cocone.isColimitYonedaEquiv` 的定义

English:
definition Limits.Cocone.isColimitYonedaEquiv
  signature: {F : J ⥤ C} (c : Cocone F)
  body: isLimitOfPreserves _ h.op
  invFun h := IsLimit.unop (yonedaJointlyReflectsLimits _ _ h)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

中文:
定义 Limits.Cocone.isColimitYonedaEquiv
  签名: {F : J ⥤ C} (c : Cocone F)
  定义体: isLimitOfPreserves _ h.op
  invFun h := IsLimit.unop (yonedaJointlyReflectsLimits _ _ h)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

Depends on / 依赖: h.op, isLimitOfPreserves
-/
noncomputable def Limits.Cocone.isColimitYonedaEquiv {F : J ⥤ C} (c : Cocone F) :
    IsColimit c ≃ forall (X : C), IsLimit ((yoneda.obj X).mapCone c.op) where
  toFun h _ := isLimitOfPreserves _ h.op
  invFun h := IsLimit.unop (yonedaJointlyReflectsLimits _ _ h)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

set_option backward.defeqAttrib.useBackward true in
/-- The cone of `F` corresponding to an element in `(F ⋙ coyoneda.obj X).sections`. -/
@[simps]
/--
Definition of `Limits.coneOfSectionCompCoyoneda` / `Limits.coneOfSectionCompCoyoneda` 的定义

English:
definition Limits.coneOfSectionCompCoyoneda
  signature: (F : J ⥤ C) (X : Cᵒᵖ)
  body: X.unop
  π := {
    app := fun j => s.val j
    naturality _ _ f := by simp [(s.property f).symm] }

中文:
定义 Limits.coneOfSectionCompCoyoneda
  签名: (F : J ⥤ C) (X : Cᵒᵖ)
  定义体: X.unop
  π := {
    app := fun j => s.val j
    naturality _ _ f := by simp [(s.property f).symm] }

Depends on / 依赖: X.unop
-/
def Limits.coneOfSectionCompCoyoneda (F : J ⥤ C) (X : Cᵒᵖ)
    (s : (F ⋙ coyoneda.obj X).sections) : Cone F where
  pt := X.unop
  π := {
    app := fun j => s.val j
    naturality _ _ f := by simp [(s.property f).symm] }

/--
Instance `coyoneda_preservesLimit` / 实例 `coyoneda_preservesLimit`

English:
instance coyoneda_preservesLimit
  signature: (F : J ⥤ C) (X : Cᵒᵖ)
  body: by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨hc.lift (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩), hc.fac _,
      hc.uniq (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩)⟩

中文:
实例 coyoneda_preservesLimit
  签名: (F : J ⥤ C) (X : Cᵒᵖ)
  定义体: by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨hc.lift (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩), hc.fac _,
      hc.uniq (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩)⟩

Depends on / 依赖: Limits, Limits.coneOfSectionCompCoyoneda, Types.isLimit_iff, coneOfSectionCompCoyoneda, hc.fac, hc.lift, hc.uniq, isLimit_iff
-/
instance coyoneda_preservesLimit (F : J ⥤ C) (X : Cᵒᵖ) :
    PreservesLimit F (coyoneda.obj X) where
  preserves {c} hc := by
    rw [Types.isLimit_iff]
    intro s hs
    exact ⟨hc.lift (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩), hc.fac _,
      hc.uniq (Limits.coneOfSectionCompCoyoneda F X ⟨s, hs⟩)⟩

variable (J) in
/--
Instance `coyonedaPreservesLimitsOfShape` / 实例 `coyonedaPreservesLimitsOfShape`

English:
instance coyonedaPreservesLimitsOfShape
  signature: (X : Cᵒᵖ)

中文:
实例 coyonedaPreservesLimitsOfShape
  签名: (X : Cᵒᵖ)
-/
noncomputable instance coyonedaPreservesLimitsOfShape (X : Cᵒᵖ) :
    PreservesLimitsOfShape J (coyoneda.obj X) where

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coyonedaJointlyReflectsLimits` / `coyonedaJointlyReflectsLimits` 的定义

English:
definition coyonedaJointlyReflectsLimits
  signature: (F : J ⥤ C) (c : Cone F)
  body: (hc (op s.pt)).lift ((coyoneda.obj (op s.pt)).mapCone s) (𝟙 _)
  fac s j := by simpa using congr_hom ((hc (op s.pt)).fac
    ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 s.pt)
  uniq s m hm := by
    apply (Types.isLimitEquivSections (hc (op s.pt))).injective
    ext j
    dsimp [Types.isLimitEquivSec

中文:
定义 coyonedaJointlyReflectsLimits
  签名: (F : J ⥤ C) (c : Cone F)
  定义体: (hc (op s.pt)).lift ((coyoneda.obj (op s.pt)).mapCone s) (𝟙 _)
  fac s j := by simpa using congr_hom ((hc (op s.pt)).fac
    ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 s.pt)
  uniq s m hm := by
    apply (Types.isLimitEquivSections (hc (op s.pt))).injective
    ext j
    dsimp [Types.isLimitEquivSec

Depends on / 依赖: coyoneda, coyoneda.obj, mapCone, s.pt
-/
def coyonedaJointlyReflectsLimits (F : J ⥤ C) (c : Cone F)
    (hc : forall X : Cᵒᵖ, IsLimit ((coyoneda.obj X).mapCone c)) : IsLimit c where
  lift s := (hc (op s.pt)).lift ((coyoneda.obj (op s.pt)).mapCone s) (𝟙 _)
  fac s j := by simpa using congr_hom ((hc (op s.pt)).fac
    ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 s.pt)
  uniq s m hm := by
    apply (Types.isLimitEquivSections (hc (op s.pt))).injective
    ext j
    dsimp [Types.isLimitEquivSections, Types.sectionOfCone]
    have eq := congr_hom ((hc (op s.pt)).fac ((coyoneda.obj (op s.pt)).mapCone s) j) (𝟙 s.pt)
    cat_disch

/--
Definition of `Limits.Cone.isLimitCoyonedaEquiv` / `Limits.Cone.isLimitCoyonedaEquiv` 的定义

English:
definition Limits.Cone.isLimitCoyonedaEquiv
  signature: {F : J ⥤ C} (c : Cone F)
  body: isLimitOfPreserves _ h
  invFun h := coyonedaJointlyReflectsLimits _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

中文:
定义 Limits.Cone.isLimitCoyonedaEquiv
  签名: {F : J ⥤ C} (c : Cone F)
  定义体: isLimitOfPreserves _ h
  invFun h := coyonedaJointlyReflectsLimits _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

Depends on / 依赖: isLimitOfPreserves
-/
noncomputable def Limits.Cone.isLimitCoyonedaEquiv {F : J ⥤ C} (c : Cone F) :
    IsLimit c ≃ forall (X : Cᵒᵖ), IsLimit ((coyoneda.obj X).mapCone c) where
  toFun h _ := isLimitOfPreserves _ h
  invFun h := coyonedaJointlyReflectsLimits _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := by ext; apply Subsingleton.elim

end

/--
Instance `yoneda_preservesLimits` / 实例 `yoneda_preservesLimits`

English:
instance yoneda_preservesLimits
  signature: (X : C)

中文:
实例 yoneda_preservesLimits
  签名: (X : C)
-/
instance yoneda_preservesLimits (X : C) :
    PreservesLimitsOfSize.{t, w} (yoneda.obj X) where

/--
Instance `coyoneda_preservesLimits` / 实例 `coyoneda_preservesLimits`

English:
instance coyoneda_preservesLimits
  signature: (X : Cᵒᵖ)

中文:
实例 coyoneda_preservesLimits
  签名: (X : Cᵒᵖ)
-/
instance coyoneda_preservesLimits (X : Cᵒᵖ) :
    PreservesLimitsOfSize.{t, w} (coyoneda.obj X) where

/--
Instance `yonedaFunctor_preservesLimits` / 实例 `yonedaFunctor_preservesLimits`

English:
instance yonedaFunctor_preservesLimits
  signature: :
  body: by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (coyoneda.obj K)
  infer_instance

中文:
实例 yonedaFunctor_preservesLimits
  签名: :
  定义体: by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (coyoneda.obj K)
  infer_instance

Depends on / 依赖: PreservesLimitsOfSize, coyoneda, coyoneda.obj, infer_instance, preservesLimits_of_evaluation
-/
instance yonedaFunctor_preservesLimits :
    PreservesLimitsOfSize.{t, w} (@yoneda C _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (coyoneda.obj K)
  infer_instance

/--
Instance `coyonedaFunctor_preservesLimits` / 实例 `coyonedaFunctor_preservesLimits`

English:
instance coyonedaFunctor_preservesLimits
  signature: :
  body: by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (yoneda.obj K)
  infer_instance

中文:
实例 coyonedaFunctor_preservesLimits
  签名: :
  定义体: by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (yoneda.obj K)
  infer_instance

Depends on / 依赖: PreservesLimitsOfSize, infer_instance, preservesLimits_of_evaluation, yoneda, yoneda.obj
-/
noncomputable instance coyonedaFunctor_preservesLimits :
    PreservesLimitsOfSize.{t, w} (@coyoneda C _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize (yoneda.obj K)
  infer_instance

/--
Instance `yonedaFunctor_reflectsLimits` / 实例 `yonedaFunctor_reflectsLimits`

English:
instance yonedaFunctor_reflectsLimits
  signature: :
  body: inferInstance

中文:
实例 yonedaFunctor_reflectsLimits
  签名: :
  定义体: inferInstance
-/
noncomputable instance yonedaFunctor_reflectsLimits :
    ReflectsLimitsOfSize.{t, w} (@yoneda C _) := inferInstance

/--
Instance `coyonedaFunctor_reflectsLimits` / 实例 `coyonedaFunctor_reflectsLimits`

English:
instance coyonedaFunctor_reflectsLimits
  signature: :
  body: inferInstance

中文:
实例 coyonedaFunctor_reflectsLimits
  签名: :
  定义体: inferInstance
-/
noncomputable instance coyonedaFunctor_reflectsLimits :
    ReflectsLimitsOfSize.{t, w} (@coyoneda C _) := inferInstance

/--
Instance `uliftYonedaFunctor_preservesLimits` / 实例 `uliftYonedaFunctor_preservesLimits`

English:
instance uliftYonedaFunctor_preservesLimits
  signature: :
  body: by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize.{t, w} (coyoneda.obj K ⋙ uliftFunctor.{w'})
  infer_instance

中文:
实例 uliftYonedaFunctor_preservesLimits
  签名: :
  定义体: by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize.{t, w} (coyoneda.obj K ⋙ uliftFunctor.{w'})
  infer_instance

Depends on / 依赖: PreservesLimitsOfSize, coyoneda, coyoneda.obj, infer_instance, preservesLimits_of_evaluation, uliftFunctor
-/
instance uliftYonedaFunctor_preservesLimits :
    PreservesLimitsOfSize.{t, w} (uliftYoneda.{w'} : C ⥤ _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize.{t, w} (coyoneda.obj K ⋙ uliftFunctor.{w'})
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfSize.{t, w} (uliftCoyoneda.{w'} : Cᵒᵖ ⥤ _)
  body: by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize.{t, w} (yoneda.obj _ ⋙ uliftFunctor.{w'})
  infer_instance

中文:
实例 :
  签名: PreservesLimitsOfSize.{t, w} (uliftCoyoneda.{w'} : Cᵒᵖ ⥤ _)
  定义体: by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize.{t, w} (yoneda.obj _ ⋙ uliftFunctor.{w'})
  infer_instance

Depends on / 依赖: PreservesLimitsOfSize, infer_instance, preservesLimits_of_evaluation, uliftFunctor, yoneda, yoneda.obj
-/
instance : PreservesLimitsOfSize.{t, w} (uliftCoyoneda.{w'} : Cᵒᵖ ⥤ _) := by
  apply preservesLimits_of_evaluation
  intro K
  change PreservesLimitsOfSize.{t, w} (yoneda.obj _ ⋙ uliftFunctor.{w'})
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallySmall.{w'}
  signature: C] :
  body: preservesLimits_of_evaluation _ (fun K => ⟨fun {J _} => by
    have := preservesLimitsOfShape_of_natIso (J := J) (Functor.associator _ _ _ ≪≫
      shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor.{w'} K).symm
    exact preservesLimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{v}⟩)

中文:
实例 [LocallySmall.{w'}
  签名: C] :
  定义体: preservesLimits_of_evaluation _ (fun K => ⟨fun {J _} => by
    have := preservesLimitsOfShape_of_natIso (J := J) (Functor.associator _ _ _ ≪≫
      shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor.{w'} K).symm
    exact preservesLimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{v}⟩)
-/
instance [LocallySmall.{w'} C] :
    PreservesLimitsOfSize.{t, w} (shrinkYoneda.{w'} (C := C)) :=
  preservesLimits_of_evaluation _ (fun K => ⟨fun {J _} => by
    have := preservesLimitsOfShape_of_natIso (J := J) (Functor.associator _ _ _ ≪≫
      shrinkYonedaCompEvaluationCompUliftFunctorIsoUliftFunctor.{w'} K).symm
    exact preservesLimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{v}⟩)

namespace Functor

section Representable

variable (F : Cᵒᵖ ⥤ Type w') [F.IsRepresentable]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfSize.{t, w} F
  body: by
  suffices PreservesLimitsOfSize (F ⋙ uliftFunctor.{v}) from
    preservesLimits_of_reflects_of_preserves _ (uliftFunctor.{v})
  rw [preservesLimitsOfSize_iff_of_natIso (F ⋙ uliftFunctor.{v}).uliftYonedaReprXIso.symm]
exact inferInstanceAs PreservesLimitsOfSize (yoneda.obj _ ⋙ uliftFunctor)

中文:
实例 :
  签名: PreservesLimitsOfSize.{t, w} F
  定义体: by
  suffices PreservesLimitsOfSize (F ⋙ uliftFunctor.{v}) from
    preservesLimits_of_reflects_of_preserves _ (uliftFunctor.{v})
  rw [preservesLimitsOfSize_iff_of_natIso (F ⋙ uliftFunctor.{v}).uliftYonedaReprXIso.symm]
exact inferInstanceAs PreservesLimitsOfSize (yoneda.obj _ ⋙ uliftFunctor)

Depends on / 依赖: PreservesLimitsOfSize, preservesLimitsOfSize_iff_of_natIso, preservesLimits_of_reflects_of_preserves, uliftFunctor, uliftYonedaReprXIso, uliftYonedaReprXIso.symm, yoneda, yoneda.obj
-/
instance : PreservesLimitsOfSize.{t, w} F := by
  suffices PreservesLimitsOfSize (F ⋙ uliftFunctor.{v}) from
    preservesLimits_of_reflects_of_preserves _ (uliftFunctor.{v})
  rw [preservesLimitsOfSize_iff_of_natIso (F ⋙ uliftFunctor.{v}).uliftYonedaReprXIso.symm]
exact inferInstanceAs PreservesLimitsOfSize (yoneda.obj _ ⋙ uliftFunctor)

end Representable

section Corepresentable

variable (F : C ⥤ Type*) [F.IsCorepresentable]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfSize.{t, w} F
  body: by
  suffices PreservesLimitsOfSize (F ⋙ uliftFunctor.{v}) from
    preservesLimits_of_reflects_of_preserves _ (uliftFunctor.{v})
  rw [preservesLimitsOfSize_iff_of_natIso (F ⋙ uliftFunctor.{v}).uliftCoyonedaCoreprXIso.symm]
exact inferInstanceAs PreservesLimitsOfSize (coyoneda.obj _ ⋙ uliftFunctor)

中文:
实例 :
  签名: PreservesLimitsOfSize.{t, w} F
  定义体: by
  suffices PreservesLimitsOfSize (F ⋙ uliftFunctor.{v}) from
    preservesLimits_of_reflects_of_preserves _ (uliftFunctor.{v})
  rw [preservesLimitsOfSize_iff_of_natIso (F ⋙ uliftFunctor.{v}).uliftCoyonedaCoreprXIso.symm]
exact inferInstanceAs PreservesLimitsOfSize (coyoneda.obj _ ⋙ uliftFunctor)

Depends on / 依赖: PreservesLimitsOfSize, coyoneda, coyoneda.obj, preservesLimitsOfSize_iff_of_natIso, preservesLimits_of_reflects_of_preserves, uliftCoyonedaCoreprXIso, uliftCoyonedaCoreprXIso.symm, uliftFunctor
-/
instance : PreservesLimitsOfSize.{t, w} F := by
  suffices PreservesLimitsOfSize (F ⋙ uliftFunctor.{v}) from
    preservesLimits_of_reflects_of_preserves _ (uliftFunctor.{v})
  rw [preservesLimitsOfSize_iff_of_natIso (F ⋙ uliftFunctor.{v}).uliftCoyonedaCoreprXIso.symm]
exact inferInstanceAs PreservesLimitsOfSize (coyoneda.obj _ ⋙ uliftFunctor)

end Corepresentable

end Functor

end CategoryTheory
