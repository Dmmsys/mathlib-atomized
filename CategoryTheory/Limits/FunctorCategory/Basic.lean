/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# (Co)limits in functor categories.

We show that if `D` has limits, then the functor category `C ⥤ D` also has limits
(`CategoryTheory.Limits.functorCategoryHasLimits`),
and the evaluation functors preserve limits
(`CategoryTheory.Limits.evaluation_preservesLimits`)
(and similarly for colimits).

We also show that `F : D ⥤ K ⥤ C` preserves (co)limits if it does so for each `k : K`
(`CategoryTheory.Limits.preservesLimits_of_evaluation` and
`CategoryTheory.Limits.preservesColimits_of_evaluation`).
-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Functor

-- morphism levels before object levels. See note [category theory universes].
universe w' w v₁ v₂ u₁ u₂ v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

@[reassoc (attr := simp)]
/--
theorem `limit.lift_π_app` / 定理 `limit.lift_π_app`

English:
theorem limit.lift_π_app
  given: (H : J ⥤ K ⥤ C) [HasLimit H] (c : Cone H) (j : J) (k : K)
  proof: congr_app (limit.lift_π c j) k

@[reassoc (attr := simp)]

中文:
定理 limit.lift_π_app
  条件: (H : J ⥤ K ⥤ C) [有极限 H] (c : 锥 H) (j : J) (k : K)
  证明: congr_app (limit.lift_π c j) k

@[reassoc (attr := simp)]

Depends on / 依赖: congr_app, limit.lift_
-/
theorem limit.lift_π_app (H : J ⥤ K ⥤ C) [HasLimit H] (c : Cone H) (j : J) (k : K) :
    (limit.lift H c).app k ≫ (limit.π H j).app k = (c.π.app j).app k :=
  congr_app (limit.lift_π c j) k

@[reassoc (attr := simp)]
/--
theorem `colimit.ι_desc_app` / 定理 `colimit.ι_desc_app`

English:
theorem colimit.ι_desc_app
  given: (H : J ⥤ K ⥤ C) [HasColimit H] (c : Cocone H) (j : J) (k : K)
  proof: congr_app (colimit.ι_desc c j) k

中文:
定理 colimit.ι_desc_app
  条件: (H : J ⥤ K ⥤ C) [有余极限 H] (c : 余锥 H) (j : J) (k : K)
  证明: congr_app (colimit.ι_desc c j) k

Depends on / 依赖: colimit, congr_app
-/
theorem colimit.ι_desc_app (H : J ⥤ K ⥤ C) [HasColimit H] (c : Cocone H) (j : J) (k : K) :
    (colimit.ι H j).app k ≫ (colimit.desc H c).app k = (c.ι.app j).app k :=
  congr_app (colimit.ι_desc c j) k

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `evaluationJointlyReflectsLimits` / `evaluationJointlyReflectsLimits` 的定义

English:
definition evaluationJointlyReflectsLimits
  signature: {F : J ⥤ K ⥤ C} (c : Cone F)
  body: { app := fun k => (t k).lift ⟨s.pt.obj k, whiskerRight s.π ((evaluation K C).obj k)⟩
      naturality := fun X Y f =>
        (t Y).hom_ext fun j => by
          rw [assoc]; rw [(t Y).fac _ j]
          simpa using
            ((t X).fac_assoc ⟨s.pt.obj X, whiskerRight s.π ((evaluation K C).obj X)⟩ j _).symm }
  fac s j := by ext k; exact (t k).fac _ j
  uniq s m w := by
    ext x
    exact (t x).hom_ext fun j =>
      (congr_app (w j) x).trans
        ((t x).fac ⟨s.pt.obj _, whiskerRight s.π ((evaluation K C).obj _)⟩ j).symm

中文:
定义 evaluationJointlyReflectsLimits
  签名: {F : J ⥤ K ⥤ C} (c : 锥 F)
  定义体: { app := fun k => (t k).lift ⟨s.pt.obj k, whiskerRight s.π ((evaluation K C).obj k)⟩
      naturality := fun X Y f =>
        (t Y).hom_ext fun j => by
          rw [assoc]; rw [(t Y).fac _ j]
          simpa using
            ((t X).fac_assoc ⟨s.pt.obj X, whiskerRight s.π ((evaluation K C).obj X)⟩ j _).symm }
  fac s j := by ext k; exact (t k).fac _ j
  uniq s m w := by
    ext x
    exact (t x).hom_ext fun j =>
      (congr_app (w j) x).trans
        ((t x).fac ⟨s.pt.obj _, whiskerRight s.π ((evaluation K C).obj _)⟩ j).symm

Depends on / 依赖: congr_app, evaluation, fac_assoc, hom_ext, naturality, s.pt.obj, whiskerRight
-/
def evaluationJointlyReflectsLimits {F : J ⥤ K ⥤ C} (c : Cone F)
    (t : forall k : K, IsLimit (((evaluation K C).obj k).mapCone c)) : IsLimit c where
  lift s :=
    { app := fun k => (t k).lift ⟨s.pt.obj k, whiskerRight s.π ((evaluation K C).obj k)⟩
      naturality := fun X Y f =>
        (t Y).hom_ext fun j => by
          rw [assoc]; rw [(t Y).fac _ j]
          simpa using
            ((t X).fac_assoc ⟨s.pt.obj X, whiskerRight s.π ((evaluation K C).obj X)⟩ j _).symm }
  fac s j := by ext k; exact (t k).fac _ j
  uniq s m w := by
    ext x
    exact (t x).hom_ext fun j =>
      (congr_app (w j) x).trans
        ((t x).fac ⟨s.pt.obj _, whiskerRight s.π ((evaluation K C).obj _)⟩ j).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `F` and a collection of limit cones for each diagram `X ↦ F X k`, we can stitch
them together to give a cone for the diagram `F`.
`combinedIsLimit` shows that the new cone is limiting, and `evalCombined` shows it is
(essentially) made up of the original cones.
-/
@[simps]
/--
Definition of `combineCones` / `combineCones` 的定义

English:
definition combineCones
  signature: (F : J ⥤ K ⥤ C) (c : forall k : K, LimitCone (F.flip.obj k))
  body: { obj := fun k => (c k).cone.pt
      map := fun {k₁} {k₂} f => (c k₂).isLimit.lift ⟨_, (c k₁).cone.π ≫ F.flip.map f⟩
      map_id := fun k =>
        (c k).isLimit.hom_ext fun j => by simp
      map_comp := fun {k₁} {k₂} {k₃} f₁ f₂ => (c k₃).isLimit.hom_ext fun j => by simp }
  π :=
    { app := fun j => { app := fun k => (c k).cone.π.app j }
      naturality := fun j₁ j₂ g => by ext k; exact (c k).cone.π.naturality g }

中文:
定义 combineCones
  签名: (F : J ⥤ K ⥤ C) (c : 对任意 k : K, 极限锥 (F.flip.obj k))
  定义体: { obj := fun k => (c k).cone.pt
      map := fun {k₁} {k₂} f => (c k₂).isLimit.lift ⟨_, (c k₁).cone.π ≫ F.flip.map f⟩
      map_id := fun k =>
        (c k).isLimit.hom_ext fun j => by simp
      map_comp := fun {k₁} {k₂} {k₃} f₁ f₂ => (c k₃).isLimit.hom_ext fun j => by simp }
  π :=
    { app := fun j => { app := fun k => (c k).cone.π.app j }
      naturality := fun j₁ j₂ g => by ext k; exact (c k).cone.π.naturality g }

Depends on / 依赖: F.flip.map, cone.pt, hom_ext, isLimit, isLimit.hom_ext, isLimit.lift, map_comp, map_id, naturality
-/
def combineCones (F : J ⥤ K ⥤ C) (c : forall k : K, LimitCone (F.flip.obj k)) : Cone F where
  pt :=
    { obj := fun k => (c k).cone.pt
      map := fun {k₁} {k₂} f => (c k₂).isLimit.lift ⟨_, (c k₁).cone.π ≫ F.flip.map f⟩
      map_id := fun k =>
        (c k).isLimit.hom_ext fun j => by simp
      map_comp := fun {k₁} {k₂} {k₃} f₁ f₂ => (c k₃).isLimit.hom_ext fun j => by simp }
  π :=
    { app := fun j => { app := fun k => (c k).cone.π.app j }
      naturality := fun j₁ j₂ g => by ext k; exact (c k).cone.π.naturality g }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `evaluateCombinedCones` / `evaluateCombinedCones` 的定义

English:
definition evaluateCombinedCones
  signature: (F : J ⥤ K ⥤ C) (c : forall k : K, LimitCone (F.flip.obj k)) (k : K)
  body: Cone.ext (Iso.refl _)

中文:
定义 evaluateCombinedCones
  签名: (F : J ⥤ K ⥤ C) (c : 对任意 k : K, 极限锥 (F.flip.obj k)) (k : K)
  定义体: Cone.ext (Iso.refl _)

Depends on / 依赖: Cone.ext, Iso.refl
-/
def evaluateCombinedCones (F : J ⥤ K ⥤ C) (c : forall k : K, LimitCone (F.flip.obj k)) (k : K) :
    ((evaluation K C).obj k).mapCone (combineCones F c) ≅ (c k).cone :=
  Cone.ext (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `combinedIsLimit` / `combinedIsLimit` 的定义

English:
definition combinedIsLimit
  signature: (F : J ⥤ K ⥤ C) (c : forall k : K, LimitCone (F.flip.obj k))
  body: evaluationJointlyReflectsLimits _ fun k =>
    (c k).isLimit.ofIsoLimit (evaluateCombinedCones F c k).symm

中文:
定义 combinedIsLimit
  签名: (F : J ⥤ K ⥤ C) (c : 对任意 k : K, 极限锥 (F.flip.obj k))
  定义体: evaluationJointlyReflectsLimits _ fun k =>
    (c k).isLimit.ofIsoLimit (evaluateCombinedCones F c k).symm

Depends on / 依赖: evaluateCombinedCones, evaluationJointlyReflectsLimits, isLimit, isLimit.ofIsoLimit, ofIsoLimit
-/
def combinedIsLimit (F : J ⥤ K ⥤ C) (c : forall k : K, LimitCone (F.flip.obj k)) :
    IsLimit (combineCones F c) :=
  evaluationJointlyReflectsLimits _ fun k =>
    (c k).isLimit.ofIsoLimit (evaluateCombinedCones F c k).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `evaluationJointlyReflectsColimits` / `evaluationJointlyReflectsColimits` 的定义

English:
definition evaluationJointlyReflectsColimits
  signature: {F : J ⥤ K ⥤ C} (c : Cocone F)
  body: { app := fun k => (t k).desc ⟨s.pt.obj k, whiskerRight s.ι ((evaluation K C).obj k)⟩
      naturality := fun X Y f =>
        (t X).hom_ext fun j => by
          rw [(t X).fac_assoc _ j]
          erw [← (c.ι.app j).naturality_assoc f]
          erw [(t Y).fac ⟨s.pt.obj _, whiskerRight s.ι _⟩ j]
          simp }
  fac s j := by ext k; exact (t k).fac _ j
  uniq s m w := by
    ext x
    exact (t x).hom_ext fun j =>
      (congr_app (w j) x).trans
        ((t x).fac ⟨s.pt.obj _, whiskerRight s.ι ((evaluation K C).obj _)⟩ j).symm

中文:
定义 evaluationJointlyReflectsColimits
  签名: {F : J ⥤ K ⥤ C} (c : 余锥 F)
  定义体: { app := fun k => (t k).desc ⟨s.pt.obj k, whiskerRight s.ι ((evaluation K C).obj k)⟩
      naturality := fun X Y f =>
        (t X).hom_ext fun j => by
          rw [(t X).fac_assoc _ j]
          erw [← (c.ι.app j).naturality_assoc f]
          erw [(t Y).fac ⟨s.pt.obj _, whiskerRight s.ι _⟩ j]
          simp }
  fac s j := by ext k; exact (t k).fac _ j
  uniq s m w := by
    ext x
    exact (t x).hom_ext fun j =>
      (congr_app (w j) x).trans
        ((t x).fac ⟨s.pt.obj _, whiskerRight s.ι ((evaluation K C).obj _)⟩ j).symm

Depends on / 依赖: congr_app, evaluation, fac_assoc, hom_ext, naturality, naturality_assoc, s.pt.obj, whiskerRight
-/
def evaluationJointlyReflectsColimits {F : J ⥤ K ⥤ C} (c : Cocone F)
    (t : forall k : K, IsColimit (((evaluation K C).obj k).mapCocone c)) : IsColimit c where
  desc s :=
    { app := fun k => (t k).desc ⟨s.pt.obj k, whiskerRight s.ι ((evaluation K C).obj k)⟩
      naturality := fun X Y f =>
        (t X).hom_ext fun j => by
          rw [(t X).fac_assoc _ j]
          erw [← (c.ι.app j).naturality_assoc f]
          erw [(t Y).fac ⟨s.pt.obj _, whiskerRight s.ι _⟩ j]
          simp }
  fac s j := by ext k; exact (t k).fac _ j
  uniq s m w := by
    ext x
    exact (t x).hom_ext fun j =>
      (congr_app (w j) x).trans
        ((t x).fac ⟨s.pt.obj _, whiskerRight s.ι ((evaluation K C).obj _)⟩ j).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Given a functor `F` and a collection of colimit cocones for each diagram `X ↦ F X k`, we can stitch
them together to give a cocone for the diagram `F`.
`combinedIsColimit` shows that the new cocone is colimiting, and `evalCombined` shows it is
(essentially) made up of the original cocones.
-/
@[simps]
/--
Definition of `combineCocones` / `combineCocones` 的定义

English:
definition combineCocones
  signature: (F : J ⥤ K ⥤ C) (c : forall k : K, ColimitCocone (F.flip.obj k))
  body: { obj := fun k => (c k).cocone.pt
      map := fun {k₁} {k₂} f => (c k₁).isColimit.desc ⟨_, F.flip.map f ≫ (c k₂).cocone.ι⟩
      map_id := fun k =>
        (c k).isColimit.hom_ext fun j => by simp
      map_comp := fun {k₁} {k₂} {k₃} f₁ f₂ => (c k₁).isColimit.hom_ext fun j => by simp }
  ι :=
    { app := fun j => { app := fun k => (c k).cocone.ι.app j }
      naturality := fun j₁ j₂ g => by ext k; exact (c k).cocone.ι.naturality g }

中文:
定义 combineCocones
  签名: (F : J ⥤ K ⥤ C) (c : 对任意 k : K, 余极限余锥 (F.flip.obj k))
  定义体: { obj := fun k => (c k).cocone.pt
      map := fun {k₁} {k₂} f => (c k₁).isColimit.desc ⟨_, F.flip.map f ≫ (c k₂).cocone.ι⟩
      map_id := fun k =>
        (c k).isColimit.hom_ext fun j => by simp
      map_comp := fun {k₁} {k₂} {k₃} f₁ f₂ => (c k₁).isColimit.hom_ext fun j => by simp }
  ι :=
    { app := fun j => { app := fun k => (c k).cocone.ι.app j }
      naturality := fun j₁ j₂ g => by ext k; exact (c k).cocone.ι.naturality g }

Depends on / 依赖: F.flip.map, cocone, cocone.pt, hom_ext, isColimit, isColimit.desc, isColimit.hom_ext, map_comp, map_id, naturality
-/
def combineCocones (F : J ⥤ K ⥤ C) (c : forall k : K, ColimitCocone (F.flip.obj k)) : Cocone F where
  pt :=
    { obj := fun k => (c k).cocone.pt
      map := fun {k₁} {k₂} f => (c k₁).isColimit.desc ⟨_, F.flip.map f ≫ (c k₂).cocone.ι⟩
      map_id := fun k =>
        (c k).isColimit.hom_ext fun j => by simp
      map_comp := fun {k₁} {k₂} {k₃} f₁ f₂ => (c k₁).isColimit.hom_ext fun j => by simp }
  ι :=
    { app := fun j => { app := fun k => (c k).cocone.ι.app j }
      naturality := fun j₁ j₂ g => by ext k; exact (c k).cocone.ι.naturality g }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `evaluateCombinedCocones` / `evaluateCombinedCocones` 的定义

English:
definition evaluateCombinedCocones
  signature: (F : J ⥤ K ⥤ C) (c : forall k : K, ColimitCocone (F.flip.obj k)) (k : K)
  body: Cocone.ext (Iso.refl _)

中文:
定义 evaluateCombinedCocones
  签名: (F : J ⥤ K ⥤ C) (c : 对任意 k : K, 余极限余锥 (F.flip.obj k)) (k : K)
  定义体: Cocone.ext (Iso.refl _)

Depends on / 依赖: Cocone, Cocone.ext, Iso.refl, Opposite, Opposite.unop, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, exists_leftFraction, h.exists_leftFraction, h.ext, op_inj, s.op, t.unop, unop_inj
-/
def evaluateCombinedCocones (F : J ⥤ K ⥤ C) (c : forall k : K, ColimitCocone (F.flip.obj k)) (k : K) :
    ((evaluation K C).obj k).mapCocone (combineCocones F c) ≅ (c k).cocone :=
  Cocone.ext (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `combinedIsColimit` / `combinedIsColimit` 的定义

English:
definition combinedIsColimit
  signature: (F : J ⥤ K ⥤ C) (c : forall k : K, ColimitCocone (F.flip.obj k))
  body: evaluationJointlyReflectsColimits _ fun k =>
    (c k).isColimit.ofIsoColimit (evaluateCombinedCocones F c k).symm

中文:
定义 combinedIsColimit
  签名: (F : J ⥤ K ⥤ C) (c : 对任意 k : K, 余极限余锥 (F.flip.obj k))
  定义体: evaluationJointlyReflectsColimits _ fun k =>
    (c k).isColimit.ofIsoColimit (evaluateCombinedCocones F c k).symm

Depends on / 依赖: Opposite, Opposite.unop, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, evaluateCombinedCocones, evaluationJointlyReflectsColimits, exists_rightFraction, h.exists_rightFraction, h.ext, isColimit, isColimit.ofIsoColimit, ofIsoColimit, op_inj, s.op, t.unop, unop_inj
-/
def combinedIsColimit (F : J ⥤ K ⥤ C) (c : forall k : K, ColimitCocone (F.flip.obj k)) :
    IsColimit (combineCocones F c) :=
  evaluationJointlyReflectsColimits _ fun k =>
    (c k).isColimit.ofIsoColimit (evaluateCombinedCocones F c k).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
An alternative colimit cocone in the functor category `K ⥤ C` in the case where `C` has
`J`-shaped colimits, with cocone point `F.flip ⋙ colim`.
-/
@[simps]
/--
Definition of `pointwiseCocone` / `pointwiseCocone` 的定义

English:
definition pointwiseCocone
  signature: [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
  body: F.flip ⋙ colim
  ι := {
    app X := { app Y := (colimit.ι _ X : (F.flip.obj Y).obj X ⟶ _) }
    naturality X Y f := by
      ext x
      simp only [Functor.const_obj_obj, Functor.comp_obj, colim_obj, NatTrans.comp_app,
        Functor.const_obj_map, Category.comp_id]
      change (F.flip.obj x).map f ≫ _ = _
      rw [colimit.w] }

中文:
定义 pointwiseCocone
  签名: [有形状余极限 J C] (F : J ⥤ K ⥤ C)
  定义体: F.flip ⋙ colim
  ι := {
    app X := { app Y := (colimit.ι _ X : (F.flip.obj Y).obj X ⟶ _) }
    naturality X Y f := by
      ext x
      simp only [Functor.const_obj_obj, Functor.comp_obj, colim_obj, NatTrans.comp_app,
        Functor.const_obj_map, Category.comp_id]
      change (F.flip.obj x).map f ≫ _ = _
      rw [colimit.w] }

Depends on / 依赖: F.flip
-/
noncomputable def pointwiseCocone [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) : Cocone F where
  pt := F.flip ⋙ colim
  ι := {
    app X := { app Y := (colimit.ι _ X : (F.flip.obj Y).obj X ⟶ _) }
    naturality X Y f := by
      ext x
      simp only [Functor.const_obj_obj, Functor.comp_obj, colim_obj, NatTrans.comp_app,
        Functor.const_obj_map, Category.comp_id]
      change (F.flip.obj x).map f ≫ _ = _
      rw [colimit.w] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `pointwiseIsColimit` / `pointwiseIsColimit` 的定义

English:
definition pointwiseIsColimit
  signature: [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
  body: by
  apply IsColimit.ofIsoColimit (combinedIsColimit _
    (fun k => ⟨colimit.cocone _, colimit.isColimit _⟩))
  exact Cocone.ext (Iso.refl _)

noncomputable section

中文:
定义 pointwiseIsColimit
  签名: [有形状余极限 J C] (F : J ⥤ K ⥤ C)
  定义体: by
  apply IsColimit.ofIsoColimit (combinedIsColimit _
    (fun k => ⟨colimit.cocone _, colimit.isColimit _⟩))
  exact Cocone.ext (Iso.refl _)

noncomputable section

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, cocone, colimit, colimit.cocone, colimit.isColimit, combinedIsColimit, isColimit, ofIsoColimit
-/
noncomputable def pointwiseIsColimit [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) :
    IsColimit (pointwiseCocone F) := by
  apply IsColimit.ofIsoColimit (combinedIsColimit _
    (fun k => ⟨colimit.cocone _, colimit.isColimit _⟩))
  exact Cocone.ext (Iso.refl _)

noncomputable section

/--
Instance `functorCategoryHasLimit` / 实例 `functorCategoryHasLimit`

English:
instance functorCategoryHasLimit
  signature: (F : J ⥤ K ⥤ C) [forall k, HasLimit (F.flip.obj k)]
  body: HasLimit.mk
    { cone := combineCones F fun _ => getLimitCone _
      isLimit := combinedIsLimit _ _ }

中文:
实例 functorCategoryHasLimit
  签名: (F : J ⥤ K ⥤ C) [对任意 k, 有极限 (F.flip.obj k)]
  定义体: HasLimit.mk
    { cone := combineCones F fun _ => getLimitCone _
      isLimit := combinedIsLimit _ _ }

Depends on / 依赖: HasLimit, HasLimit.mk, combineCones, combinedIsLimit, getLimitCone, isLimit
-/
instance functorCategoryHasLimit (F : J ⥤ K ⥤ C) [forall k, HasLimit (F.flip.obj k)] : HasLimit F :=
  HasLimit.mk
    { cone := combineCones F fun _ => getLimitCone _
      isLimit := combinedIsLimit _ _ }

/--
Instance `functorCategoryHasLimitsOfShape` / 实例 `functorCategoryHasLimitsOfShape`

English:
instance functorCategoryHasLimitsOfShape
  signature: [HasLimitsOfShape J C]
  body: inferInstance

中文:
实例 functorCategoryHasLimitsOfShape
  签名: [有形状极限 J C]
  定义体: inferInstance
-/
instance functorCategoryHasLimitsOfShape [HasLimitsOfShape J C] : HasLimitsOfShape J (K ⥤ C) where
  has_limit _ := inferInstance

/--
Instance `functorCategoryHasColimit` / 实例 `functorCategoryHasColimit`

English:
instance functorCategoryHasColimit
  signature: (F : J ⥤ K ⥤ C) [forall k, HasColimit (F.flip.obj k)]
  body: HasColimit.mk
    { cocone := combineCocones F fun _ => getColimitCocone _
      isColimit := combinedIsColimit _ _ }

中文:
实例 functorCategoryHasColimit
  签名: (F : J ⥤ K ⥤ C) [对任意 k, 有余极限 (F.flip.obj k)]
  定义体: HasColimit.mk
    { cocone := combineCocones F fun _ => getColimitCocone _
      isColimit := combinedIsColimit _ _ }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, combineCocones, combinedIsColimit, getColimitCocone, isColimit
-/
instance functorCategoryHasColimit (F : J ⥤ K ⥤ C) [forall k, HasColimit (F.flip.obj k)] :
    HasColimit F :=
  HasColimit.mk
    { cocone := combineCocones F fun _ => getColimitCocone _
      isColimit := combinedIsColimit _ _ }

/--
Instance `functorCategoryHasColimitsOfShape` / 实例 `functorCategoryHasColimitsOfShape`

English:
instance functorCategoryHasColimitsOfShape
  signature: [HasColimitsOfShape J C]
  body: inferInstance

中文:
实例 functorCategoryHasColimitsOfShape
  签名: [有形状余极限 J C]
  定义体: inferInstance
-/
instance functorCategoryHasColimitsOfShape [HasColimitsOfShape J C] :
    HasColimitsOfShape J (K ⥤ C) where
  has_colimit _ := inferInstance

/--
Instance `functorCategoryHasLimitsOfSize` / 实例 `functorCategoryHasLimitsOfSize`

English:
instance functorCategoryHasLimitsOfSize
  signature: [HasLimitsOfSize.{v₁, u₁} C]
  body: inferInstance

中文:
实例 functorCategoryHasLimitsOfSize
  签名: [有LimitsOfSize.{v₁, u₁} C]
  定义体: inferInstance
-/
instance functorCategoryHasLimitsOfSize [HasLimitsOfSize.{v₁, u₁} C] :
    HasLimitsOfSize.{v₁, u₁} (K ⥤ C) where
  has_limits_of_shape := inferInstance

/--
Instance `functorCategoryHasColimitsOfSize` / 实例 `functorCategoryHasColimitsOfSize`

English:
instance functorCategoryHasColimitsOfSize
  signature: [HasColimitsOfSize.{v₁, u₁} C]
  body: inferInstance

中文:
实例 functorCategoryHasColimitsOfSize
  签名: [有余limitsOfSize.{v₁, u₁} C]
  定义体: inferInstance
-/
instance functorCategoryHasColimitsOfSize [HasColimitsOfSize.{v₁, u₁} C] :
    HasColimitsOfSize.{v₁, u₁} (K ⥤ C) where
  has_colimits_of_shape := inferInstance

instance (priority := low) hasLimitCompEvaluation (F : J ⥤ K ⥤ C) (k : K)
    [HasLimit (F.flip.obj k)] : HasLimit (F ⋙ (evaluation _ _).obj k) :=
  hasLimit_of_iso (F := F.flip.obj k) (Iso.refl _)

/--
Instance `evaluation_preservesLimit` / 实例 `evaluation_preservesLimit`

English:
instance evaluation_preservesLimit
  signature: (F : J ⥤ K ⥤ C) [forall k, HasLimit (F.flip.obj k)] (k : K)
  body: -- Porting note: added a let because X was not inferred
  let X : (k : K) -> LimitCone (F.flip.obj k) := fun k => getLimitCone (F.flip.obj k)
preservesLimit_of_preserves_limit_cone (combinedIsLimit _ X)
    IsLimit.ofIsoLimit (limit.isLimit _) (evaluateCombinedCones F X k).symm

中文:
实例 evaluation_preservesLimit
  签名: (F : J ⥤ K ⥤ C) [对任意 k, 有极限 (F.flip.obj k)] (k : K)
  定义体: -- Porting note: added a let because X was not inferred
  let X : (k : K) -> LimitCone (F.flip.obj k) := fun k => getLimitCone (F.flip.obj k)
preservesLimit_of_preserves_limit_cone (combinedIsLimit _ X)
    IsLimit.ofIsoLimit (limit.isLimit _) (evaluateCombinedCones F X k).symm
-/
instance evaluation_preservesLimit (F : J ⥤ K ⥤ C) [forall k, HasLimit (F.flip.obj k)] (k : K) :
    PreservesLimit F ((evaluation K C).obj k) :=
  -- Porting note: added a let because X was not inferred
  let X : (k : K) -> LimitCone (F.flip.obj k) := fun k => getLimitCone (F.flip.obj k)
preservesLimit_of_preserves_limit_cone (combinedIsLimit _ X)
    IsLimit.ofIsoLimit (limit.isLimit _) (evaluateCombinedCones F X k).symm

/--
Instance `evaluation_preservesLimitsOfShape` / 实例 `evaluation_preservesLimitsOfShape`

English:
instance evaluation_preservesLimitsOfShape
  signature: [HasLimitsOfShape J C] (k : K)
  body: inferInstance

中文:
实例 evaluation_preservesLimitsOfShape
  签名: [有形状极限 J C] (k : K)
  定义体: inferInstance
-/
instance evaluation_preservesLimitsOfShape [HasLimitsOfShape J C] (k : K) :
    PreservesLimitsOfShape J ((evaluation K C).obj k) where
  preservesLimit := inferInstance

/--
Definition of `limitObjIsoLimitCompEvaluation` / `limitObjIsoLimitCompEvaluation` 的定义

English:
definition limitObjIsoLimitCompEvaluation
  signature: [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (k : K)
  body: preservesLimitIso ((evaluation K C).obj k) F

中文:
定义 limitObjIsoLimitCompEvaluation
  签名: [有形状极限 J C] (F : J ⥤ K ⥤ C) (k : K)
  定义体: preservesLimitIso ((evaluation K C).obj k) F

Depends on / 依赖: evaluation, preservesLimitIso
-/
def limitObjIsoLimitCompEvaluation [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (k : K) :
    (limit F).obj k ≅ limit (F ⋙ (evaluation K C).obj k) :=
  preservesLimitIso ((evaluation K C).obj k) F

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `limitObjIsoLimitCompEvaluation_hom_π` / 定理 `limitObjIsoLimitCompEvaluation_hom_π`

English:
theorem limitObjIsoLimitCompEvaluation_hom_π
  statement: [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J)
  proof: by
  dsimp [limitObjIsoLimitCompEvaluation]
  simp

中文:
定理 limitObjIsoLimitCompEvaluation_hom_π
  结论: [有形状极限 J C] (F : J ⥤ K ⥤ C) (j : J)
  证明: by
  dsimp [limitObjIsoLimitCompEvaluation]
  simp

Depends on / 依赖: limitObjIsoLimitCompEvaluation
-/
theorem limitObjIsoLimitCompEvaluation_hom_π [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J)
    (k : K) :
    (limitObjIsoLimitCompEvaluation F k).hom ≫ limit.π (F ⋙ (evaluation K C).obj k) j =
      (limit.π F j).app k := by
  dsimp [limitObjIsoLimitCompEvaluation]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `limitObjIsoLimitCompEvaluation_inv_π_app` / 定理 `limitObjIsoLimitCompEvaluation_inv_π_app`

English:
theorem limitObjIsoLimitCompEvaluation_inv_π_app
  statement: [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J)
  proof: by
  dsimp [limitObjIsoLimitCompEvaluation]
  rw [Iso.inv_comp_eq]
  simp

中文:
定理 limitObjIsoLimitCompEvaluation_inv_π_app
  结论: [有形状极限 J C] (F : J ⥤ K ⥤ C) (j : J)
  证明: by
  dsimp [limitObjIsoLimitCompEvaluation]
  rw [Iso.inv_comp_eq]
  simp

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq, limitObjIsoLimitCompEvaluation
-/
theorem limitObjIsoLimitCompEvaluation_inv_π_app [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J)
    (k : K) :
    (limitObjIsoLimitCompEvaluation F k).inv ≫ (limit.π F j).app k =
      limit.π (F ⋙ (evaluation K C).obj k) j := by
  dsimp [limitObjIsoLimitCompEvaluation]
  rw [Iso.inv_comp_eq]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `limit_map_limitObjIsoLimitCompEvaluation_hom` / 定理 `limit_map_limitObjIsoLimitCompEvaluation_hom`

English:
theorem limit_map_limitObjIsoLimitCompEvaluation_hom
  statement: [HasLimitsOfShape J C] {i j : K}
  proof: by
  ext
  simp

@[reassoc (attr := simp)]

中文:
定理 limit_map_limitObjIsoLimitCompEvaluation_hom
  结论: [有形状极限 J C] {i j : K}
  证明: by
  ext
  simp

@[reassoc (attr := simp)]
-/
theorem limit_map_limitObjIsoLimitCompEvaluation_hom [HasLimitsOfShape J C] {i j : K}
    (F : J ⥤ K ⥤ C) (f : i ⟶ j) : (limit F).map f ≫ (limitObjIsoLimitCompEvaluation _ _).hom =
    (limitObjIsoLimitCompEvaluation _ _).hom ≫ limMap (whiskerLeft _ ((evaluation _ _).map f)) := by
  ext
  simp

@[reassoc (attr := simp)]
/--
theorem `limitObjIsoLimitCompEvaluation_inv_limit_map` / 定理 `limitObjIsoLimitCompEvaluation_inv_limit_map`

English:
theorem limitObjIsoLimitCompEvaluation_inv_limit_map
  statement: [HasLimitsOfShape J C] {i j : K}
  proof: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [limit_map_limitObjIsoLimitCompEvaluation_hom]

中文:
定理 limitObjIsoLimitCompEvaluation_inv_limit_map
  结论: [有形状极限 J C] {i j : K}
  证明: by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [limit_map_limitObjIsoLimitCompEvaluation_hom]

Depends on / 依赖: Category, Category.assoc, Iso.eq_comp_inv, Iso.inv_comp_eq, eq_comp_inv, inv_comp_eq, limit_map_limitObjIsoLimitCompEvaluation_hom
-/
theorem limitObjIsoLimitCompEvaluation_inv_limit_map [HasLimitsOfShape J C] {i j : K}
    (F : J ⥤ K ⥤ C) (f : i ⟶ j) : (limitObjIsoLimitCompEvaluation _ _).inv ≫ (limit F).map f =
    limMap (whiskerLeft _ ((evaluation _ _).map f)) ≫ (limitObjIsoLimitCompEvaluation _ _).inv := by
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]; rw [limit_map_limitObjIsoLimitCompEvaluation_hom]

set_option backward.isDefEq.respectTransparency false in
@[ext]
/--
theorem `limit_obj_ext` / 定理 `limit_obj_ext`

English:
theorem limit_obj_ext
  statement: {H : J ⥤ K ⥤ C} [HasLimitsOfShape J C] {k : K} {W : C}
  proof: by
  apply (cancel_mono (limitObjIsoLimitCompEvaluation H k).hom).1
  ext j
  simpa using w j

中文:
定理 limit_obj_ext
  结论: {H : J ⥤ K ⥤ C} [有形状极限 J C] {k : K} {W : C}
  证明: by
  apply (cancel_mono (limitObjIsoLimitCompEvaluation H k).hom).1
  ext j
  simpa using w j

Depends on / 依赖: cancel_mono, limitObjIsoLimitCompEvaluation
-/
theorem limit_obj_ext {H : J ⥤ K ⥤ C} [HasLimitsOfShape J C] {k : K} {W : C}
    {f g : W ⟶ (limit H).obj k}
    (w : forall j, f ≫ (Limits.limit.π H j).app k = g ≫ (Limits.limit.π H j).app k) : f = g := by
  apply (cancel_mono (limitObjIsoLimitCompEvaluation H k).hom).1
  ext j
  simpa using w j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `limitCompWhiskeringLeftIsoCompLimit` / `limitCompWhiskeringLeftIsoCompLimit` 的定义

English:
definition limitCompWhiskeringLeftIsoCompLimit
  signature: (F : J ⥤ K ⥤ C) (G : D ⥤ K) [HasLimitsOfShape J C]
  body: NatIso.ofComponents (fun j =>
    limitObjIsoLimitCompEvaluation (F ⋙ (whiskeringLeft _ _ _).obj G) j ≪≫
      HasLimit.isoOfNatIso (isoWhiskerLeft F (whiskeringLeftCompEvaluation G j)) ≪≫
      (limitObjIsoLimitCompEvaluation F (G.obj j)).symm)

中文:
定义 limitCompWhiskeringLeftIsoCompLimit
  签名: (F : J ⥤ K ⥤ C) (G : D ⥤ K) [有形状极限 J C]
  定义体: NatIso.ofComponents (fun j =>
    limitObjIsoLimitCompEvaluation (F ⋙ (whiskeringLeft _ _ _).obj G) j ≪≫
      HasLimit.isoOfNatIso (isoWhiskerLeft F (whiskeringLeftCompEvaluation G j)) ≪≫
      (limitObjIsoLimitCompEvaluation F (G.obj j)).symm)

Depends on / 依赖: G.obj, HasLimit, HasLimit.isoOfNatIso, NatIso, NatIso.ofComponents, isoOfNatIso, isoWhiskerLeft, limitObjIsoLimitCompEvaluation, ofComponents, whiskeringLeft, whiskeringLeftCompEvaluation
-/
def limitCompWhiskeringLeftIsoCompLimit (F : J ⥤ K ⥤ C) (G : D ⥤ K) [HasLimitsOfShape J C] :
    limit (F ⋙ (whiskeringLeft _ _ _).obj G) ≅ G ⋙ limit F :=
  NatIso.ofComponents (fun j =>
    limitObjIsoLimitCompEvaluation (F ⋙ (whiskeringLeft _ _ _).obj G) j ≪≫
      HasLimit.isoOfNatIso (isoWhiskerLeft F (whiskeringLeftCompEvaluation G j)) ≪≫
      (limitObjIsoLimitCompEvaluation F (G.obj j)).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `limitCompWhiskeringLeftIsoCompLimit_hom_whiskerLeft_π` / 定理 `limitCompWhiskeringLeftIsoCompLimit_hom_whiskerLeft_π`

English:
theorem limitCompWhiskeringLeftIsoCompLimit_hom_whiskerLeft_π
  statement: (F : J ⥤ K ⥤ C) (G : D ⥤ K)
  proof: by
  ext d
  simp [limitCompWhiskeringLeftIsoCompLimit]

中文:
定理 limitCompWhiskeringLeftIsoCompLimit_hom_whiskerLeft_π
  结论: (F : J ⥤ K ⥤ C) (G : D ⥤ K)
  证明: by
  ext d
  simp [limitCompWhiskeringLeftIsoCompLimit]

Depends on / 依赖: limitCompWhiskeringLeftIsoCompLimit
-/
theorem limitCompWhiskeringLeftIsoCompLimit_hom_whiskerLeft_π (F : J ⥤ K ⥤ C) (G : D ⥤ K)
    [HasLimitsOfShape J C] (j : J) :
    (limitCompWhiskeringLeftIsoCompLimit F G).hom ≫ whiskerLeft G (limit.π F j) =
      limit.π (F ⋙ (whiskeringLeft _ _ _).obj G) j := by
  ext d
  simp [limitCompWhiskeringLeftIsoCompLimit]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `limitCompWhiskeringLeftIsoCompLimit_inv_π` / 定理 `limitCompWhiskeringLeftIsoCompLimit_inv_π`

English:
theorem limitCompWhiskeringLeftIsoCompLimit_inv_π
  statement: (F : J ⥤ K ⥤ C) (G : D ⥤ K)
  proof: by
  simp [Iso.inv_comp_eq]

中文:
定理 limitCompWhiskeringLeftIsoCompLimit_inv_π
  结论: (F : J ⥤ K ⥤ C) (G : D ⥤ K)
  证明: by
  simp [Iso.inv_comp_eq]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem limitCompWhiskeringLeftIsoCompLimit_inv_π (F : J ⥤ K ⥤ C) (G : D ⥤ K)
    [HasLimitsOfShape J C] (j : J) :
    (limitCompWhiskeringLeftIsoCompLimit F G).inv ≫ limit.π (F ⋙ (whiskeringLeft _ _ _).obj G) j =
      whiskerLeft G (limit.π F j) := by
  simp [Iso.inv_comp_eq]

/--
Instance `hasColimitCompEvaluation` / 实例 `hasColimitCompEvaluation`

English:
instance hasColimitCompEvaluation
  signature: (F : J ⥤ K ⥤ C) (k : K) [HasColimit (F.flip.obj k)]
  body: hasColimit_of_iso (F := F.flip.obj k) (Iso.refl _)

中文:
实例 hasColimitCompEvaluation
  签名: (F : J ⥤ K ⥤ C) (k : K) [有余极限 (F.flip.obj k)]
  定义体: hasColimit_of_iso (F := F.flip.obj k) (Iso.refl _)

Depends on / 依赖: F.flip.obj, Iso.refl, hasColimit_of_iso
-/
instance hasColimitCompEvaluation (F : J ⥤ K ⥤ C) (k : K) [HasColimit (F.flip.obj k)] :
    HasColimit (F ⋙ (evaluation _ _).obj k) :=
  hasColimit_of_iso (F := F.flip.obj k) (Iso.refl _)

/--
Instance `evaluation_preservesColimit` / 实例 `evaluation_preservesColimit`

English:
instance evaluation_preservesColimit
  signature: (F : J ⥤ K ⥤ C) [forall k, HasColimit (F.flip.obj k)] (k : K)
  body: -- Porting note: added a let because X was not inferred
  let X : (k : K) -> ColimitCocone (F.flip.obj k) := fun k => getColimitCocone (F.flip.obj k)
preservesColimit_of_preserves_colimit_cocone (combinedIsColimit _ X)
    IsColimit.ofIsoColimit (colimit.isColimit _) (evaluateCombinedCocones F X k).symm

中文:
实例 evaluation_preservesColimit
  签名: (F : J ⥤ K ⥤ C) [对任意 k, 有余极限 (F.flip.obj k)] (k : K)
  定义体: -- Porting note: added a let because X was not inferred
  let X : (k : K) -> ColimitCocone (F.flip.obj k) := fun k => getColimitCocone (F.flip.obj k)
preservesColimit_of_preserves_colimit_cocone (combinedIsColimit _ X)
    IsColimit.ofIsoColimit (colimit.isColimit _) (evaluateCombinedCocones F X k).symm
-/
instance evaluation_preservesColimit (F : J ⥤ K ⥤ C) [forall k, HasColimit (F.flip.obj k)] (k : K) :
    PreservesColimit F ((evaluation K C).obj k) :=
  -- Porting note: added a let because X was not inferred
  let X : (k : K) -> ColimitCocone (F.flip.obj k) := fun k => getColimitCocone (F.flip.obj k)
preservesColimit_of_preserves_colimit_cocone (combinedIsColimit _ X)
    IsColimit.ofIsoColimit (colimit.isColimit _) (evaluateCombinedCocones F X k).symm

/--
Instance `evaluation_preservesColimitsOfShape` / 实例 `evaluation_preservesColimitsOfShape`

English:
instance evaluation_preservesColimitsOfShape
  signature: [HasColimitsOfShape J C] (k : K)
  body: inferInstance

中文:
实例 evaluation_preservesColimitsOfShape
  签名: [有形状余极限 J C] (k : K)
  定义体: inferInstance
-/
instance evaluation_preservesColimitsOfShape [HasColimitsOfShape J C] (k : K) :
    PreservesColimitsOfShape J ((evaluation K C).obj k) where
  preservesColimit := inferInstance

/--
Definition of `colimitObjIsoColimitCompEvaluation` / `colimitObjIsoColimitCompEvaluation` 的定义

English:
definition colimitObjIsoColimitCompEvaluation
  signature: [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (k : K)
  body: preservesColimitIso ((evaluation K C).obj k) F

中文:
定义 colimitObjIsoColimitCompEvaluation
  签名: [有形状余极限 J C] (F : J ⥤ K ⥤ C) (k : K)
  定义体: preservesColimitIso ((evaluation K C).obj k) F

Depends on / 依赖: evaluation, preservesColimitIso
-/
def colimitObjIsoColimitCompEvaluation [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (k : K) :
    (colimit F).obj k ≅ colimit (F ⋙ (evaluation K C).obj k) :=
  preservesColimitIso ((evaluation K C).obj k) F

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `colimitObjIsoColimitCompEvaluation_ι_inv` / 定理 `colimitObjIsoColimitCompEvaluation_ι_inv`

English:
theorem colimitObjIsoColimitCompEvaluation_ι_inv
  statement: [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J)
  proof: by
  dsimp [colimitObjIsoColimitCompEvaluation]
  simp

中文:
定理 colimitObjIsoColimitCompEvaluation_ι_inv
  结论: [有形状余极限 J C] (F : J ⥤ K ⥤ C) (j : J)
  证明: by
  dsimp [colimitObjIsoColimitCompEvaluation]
  simp

Depends on / 依赖: colimitObjIsoColimitCompEvaluation
-/
theorem colimitObjIsoColimitCompEvaluation_ι_inv [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J)
    (k : K) :
    colimit.ι (F ⋙ (evaluation K C).obj k) j ≫ (colimitObjIsoColimitCompEvaluation F k).inv =
      (colimit.ι F j).app k := by
  dsimp [colimitObjIsoColimitCompEvaluation]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `colimitObjIsoColimitCompEvaluation_ι_app_hom` / 定理 `colimitObjIsoColimitCompEvaluation_ι_app_hom`

English:
theorem colimitObjIsoColimitCompEvaluation_ι_app_hom
  statement: [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
  proof: by
  dsimp [colimitObjIsoColimitCompEvaluation]
  rw [← Iso.eq_comp_inv]
  simp

中文:
定理 colimitObjIsoColimitCompEvaluation_ι_app_hom
  结论: [有形状余极限 J C] (F : J ⥤ K ⥤ C)
  证明: by
  dsimp [colimitObjIsoColimitCompEvaluation]
  rw [← Iso.eq_comp_inv]
  simp

Depends on / 依赖: Iso.eq_comp_inv, colimitObjIsoColimitCompEvaluation, eq_comp_inv
-/
theorem colimitObjIsoColimitCompEvaluation_ι_app_hom [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
    (j : J) (k : K) :
    (colimit.ι F j).app k ≫ (colimitObjIsoColimitCompEvaluation F k).hom =
      colimit.ι (F ⋙ (evaluation K C).obj k) j := by
  dsimp [colimitObjIsoColimitCompEvaluation]
  rw [← Iso.eq_comp_inv]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `colimitObjIsoColimitCompEvaluation_inv_colimit_map` / 定理 `colimitObjIsoColimitCompEvaluation_inv_colimit_map`

English:
theorem colimitObjIsoColimitCompEvaluation_inv_colimit_map
  statement: [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
  proof: by
  ext
  simp

@[reassoc (attr := simp)]

中文:
定理 colimitObjIsoColimitCompEvaluation_inv_colimit_map
  结论: [有形状余极限 J C] (F : J ⥤ K ⥤ C)
  证明: by
  ext
  simp

@[reassoc (attr := simp)]
-/
theorem colimitObjIsoColimitCompEvaluation_inv_colimit_map [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
    {i j : K} (f : i ⟶ j) :
    (colimitObjIsoColimitCompEvaluation _ _).inv ≫ (colimit F).map f =
      colimMap (whiskerLeft _ ((evaluation _ _).map f)) ≫
        (colimitObjIsoColimitCompEvaluation _ _).inv := by
  ext
  simp

@[reassoc (attr := simp)]
/--
theorem `colimit_map_colimitObjIsoColimitCompEvaluation_hom` / 定理 `colimit_map_colimitObjIsoColimitCompEvaluation_hom`

English:
theorem colimit_map_colimitObjIsoColimitCompEvaluation_hom
  statement: [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
  proof: by
  rw [← Iso.inv_comp_eq]; rw [← Category.assoc]; rw [← Iso.eq_comp_inv]; rw [colimitObjIsoColimitCompEvaluation_inv_colimit_map]

中文:
定理 colimit_map_colimitObjIsoColimitCompEvaluation_hom
  结论: [有形状余极限 J C] (F : J ⥤ K ⥤ C)
  证明: by
  rw [← Iso.inv_comp_eq]; rw [← Category.assoc]; rw [← Iso.eq_comp_inv]; rw [colimitObjIsoColimitCompEvaluation_inv_colimit_map]

Depends on / 依赖: Category, Category.assoc, Iso.eq_comp_inv, Iso.inv_comp_eq, colimitObjIsoColimitCompEvaluation_inv_colimit_map, eq_comp_inv, inv_comp_eq
-/
theorem colimit_map_colimitObjIsoColimitCompEvaluation_hom [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
    {i j : K} (f : i ⟶ j) :
    (colimit F).map f ≫ (colimitObjIsoColimitCompEvaluation _ _).hom =
      (colimitObjIsoColimitCompEvaluation _ _).hom ≫
        colimMap (whiskerLeft _ ((evaluation _ _).map f)) := by
  rw [← Iso.inv_comp_eq]; rw [← Category.assoc]; rw [← Iso.eq_comp_inv]; rw [colimitObjIsoColimitCompEvaluation_inv_colimit_map]

set_option backward.isDefEq.respectTransparency false in
@[ext]
/--
theorem `colimit_obj_ext` / 定理 `colimit_obj_ext`

English:
theorem colimit_obj_ext
  statement: {H : J ⥤ K ⥤ C} [HasColimitsOfShape J C] {k : K} {W : C}
  proof: by
  apply (cancel_epi (colimitObjIsoColimitCompEvaluation H k).inv).1
  ext j
  simpa using w j

中文:
定理 colimit_obj_ext
  结论: {H : J ⥤ K ⥤ C} [有形状余极限 J C] {k : K} {W : C}
  证明: by
  apply (cancel_epi (colimitObjIsoColimitCompEvaluation H k).inv).1
  ext j
  simpa using w j

Depends on / 依赖: cancel_epi, colimitObjIsoColimitCompEvaluation
-/
theorem colimit_obj_ext {H : J ⥤ K ⥤ C} [HasColimitsOfShape J C] {k : K} {W : C}
    {f g : (colimit H).obj k ⟶ W} (w : forall j, (colimit.ι H j).app k ≫ f = (colimit.ι H j).app k ≫ g) :
    f = g := by
  apply (cancel_epi (colimitObjIsoColimitCompEvaluation H k).inv).1
  ext j
  simpa using w j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `colimitCompWhiskeringLeftIsoCompColimit` / `colimitCompWhiskeringLeftIsoCompColimit` 的定义

English:
definition colimitCompWhiskeringLeftIsoCompColimit
  signature: (F : J ⥤ K ⥤ C) (G : D ⥤ K) [HasColimitsOfShape J C]
  body: NatIso.ofComponents (fun j =>
    colimitObjIsoColimitCompEvaluation (F ⋙ (whiskeringLeft _ _ _).obj G) j ≪≫
      HasColimit.isoOfNatIso (isoWhiskerLeft F (whiskeringLeftCompEvaluation G j)) ≪≫
      (colimitObjIsoColimitCompEvaluation F (G.obj j)).symm)

中文:
定义 colimitCompWhiskeringLeftIsoCompColimit
  签名: (F : J ⥤ K ⥤ C) (G : D ⥤ K) [有形状余极限 J C]
  定义体: NatIso.ofComponents (fun j =>
    colimitObjIsoColimitCompEvaluation (F ⋙ (whiskeringLeft _ _ _).obj G) j ≪≫
      HasColimit.isoOfNatIso (isoWhiskerLeft F (whiskeringLeftCompEvaluation G j)) ≪≫
      (colimitObjIsoColimitCompEvaluation F (G.obj j)).symm)

Depends on / 依赖: G.obj, HasColimit, HasColimit.isoOfNatIso, NatIso, NatIso.ofComponents, colimitObjIsoColimitCompEvaluation, isoOfNatIso, isoWhiskerLeft, ofComponents, whiskeringLeft, whiskeringLeftCompEvaluation
-/
def colimitCompWhiskeringLeftIsoCompColimit (F : J ⥤ K ⥤ C) (G : D ⥤ K) [HasColimitsOfShape J C] :
    colimit (F ⋙ (whiskeringLeft _ _ _).obj G) ≅ G ⋙ colimit F :=
  NatIso.ofComponents (fun j =>
    colimitObjIsoColimitCompEvaluation (F ⋙ (whiskeringLeft _ _ _).obj G) j ≪≫
      HasColimit.isoOfNatIso (isoWhiskerLeft F (whiskeringLeftCompEvaluation G j)) ≪≫
      (colimitObjIsoColimitCompEvaluation F (G.obj j)).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `ι_colimitCompWhiskeringLeftIsoCompColimit_hom` / 定理 `ι_colimitCompWhiskeringLeftIsoCompColimit_hom`

English:
theorem ι_colimitCompWhiskeringLeftIsoCompColimit_hom
  statement: (F : J ⥤ K ⥤ C) (G : D ⥤ K)
  proof: by
  ext d
  simp [colimitCompWhiskeringLeftIsoCompColimit]

中文:
定理 ι_colimitCompWhiskeringLeftIsoCompColimit_hom
  结论: (F : J ⥤ K ⥤ C) (G : D ⥤ K)
  证明: by
  ext d
  simp [colimitCompWhiskeringLeftIsoCompColimit]

Depends on / 依赖: colimitCompWhiskeringLeftIsoCompColimit
-/
theorem ι_colimitCompWhiskeringLeftIsoCompColimit_hom (F : J ⥤ K ⥤ C) (G : D ⥤ K)
    [HasColimitsOfShape J C] (j : J) :
    colimit.ι (F ⋙ (whiskeringLeft _ _ _).obj G) j ≫
      (colimitCompWhiskeringLeftIsoCompColimit F G).hom = whiskerLeft G (colimit.ι F j) := by
  ext d
  simp [colimitCompWhiskeringLeftIsoCompColimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `whiskerLeft_ι_colimitCompWhiskeringLeftIsoCompColimit_inv` / 定理 `whiskerLeft_ι_colimitCompWhiskeringLeftIsoCompColimit_inv`

English:
theorem whiskerLeft_ι_colimitCompWhiskeringLeftIsoCompColimit_inv
  statement: (F : J ⥤ K ⥤ C) (G : D ⥤ K)
  proof: by
  simp [Iso.comp_inv_eq]

中文:
定理 whiskerLeft_ι_colimitCompWhiskeringLeftIsoCompColimit_inv
  结论: (F : J ⥤ K ⥤ C) (G : D ⥤ K)
  证明: by
  simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem whiskerLeft_ι_colimitCompWhiskeringLeftIsoCompColimit_inv (F : J ⥤ K ⥤ C) (G : D ⥤ K)
    [HasColimitsOfShape J C] (j : J) :
    whiskerLeft G (colimit.ι F j) ≫ (colimitCompWhiskeringLeftIsoCompColimit F G).inv =
      colimit.ι (F ⋙ (whiskeringLeft _ _ _).obj G) j := by
  simp [Iso.comp_inv_eq]

/--
Instance `evaluationPreservesLimits` / 实例 `evaluationPreservesLimits`

English:
instance evaluationPreservesLimits
  signature: [HasLimits C] (k : K)
  body: inferInstance

中文:
实例 evaluationPreservesLimits
  签名: [有极限 C] (k : K)
  定义体: inferInstance
-/
instance evaluationPreservesLimits [HasLimits C] (k : K) :
    PreservesLimits ((evaluation K C).obj k) where
  preservesLimitsOfShape {_} _𝒥 := inferInstance

/--
lemma `preservesLimit_of_evaluation` / 引理 `preservesLimit_of_evaluation`

English:
lemma preservesLimit_of_evaluation
  statement: (F : D ⥤ K ⥤ C) (G : J ⥤ D)
  proof: ⟨fun {c} hc => ⟨by
    apply evaluationJointlyReflectsLimits
    intro X
    haveI := H X
    change IsLimit ((F ⋙ (evaluation K C).obj X).mapCone c)
    exact isLimitOfPreserves _ hc⟩⟩

中文:
引理 preservesLimit_of_evaluation
  结论: (F : D ⥤ K ⥤ C) (G : J ⥤ D)
  证明: ⟨fun {c} hc => ⟨by
    apply evaluationJointlyReflectsLimits
    intro X
    haveI := H X
    change IsLimit ((F ⋙ (evaluation K C).obj X).mapCone c)
    exact isLimitOfPreserves _ hc⟩⟩

Depends on / 依赖: IsLimit, evaluation, evaluationJointlyReflectsLimits, isLimitOfPreserves, mapCone
-/
lemma preservesLimit_of_evaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D)
    (H : forall k : K, PreservesLimit G (F ⋙ (evaluation K C).obj k : D ⥤ C)) : PreservesLimit G F :=
  ⟨fun {c} hc => ⟨by
    apply evaluationJointlyReflectsLimits
    intro X
    haveI := H X
    change IsLimit ((F ⋙ (evaluation K C).obj X).mapCone c)
    exact isLimitOfPreserves _ hc⟩⟩

/--
lemma `preservesLimitsOfShape_of_evaluation` / 引理 `preservesLimitsOfShape_of_evaluation`

English:
lemma preservesLimitsOfShape_of_evaluation
  statement: (F : D ⥤ K ⥤ C) (J : Type*) [Category* J]
  proof: ⟨fun {G} => preservesLimit_of_evaluation F G fun _ => PreservesLimitsOfShape.preservesLimit⟩

中文:
引理 preservesLimitsOfShape_of_evaluation
  结论: (F : D ⥤ K ⥤ C) (J : 类型) [范畴* J]
  证明: ⟨fun {G} => preservesLimit_of_evaluation F G fun _ => PreservesLimitsOfShape.preservesLimit⟩

Depends on / 依赖: PreservesLimitsOfShape, PreservesLimitsOfShape.preservesLimit, preservesLimit, preservesLimit_of_evaluation
-/
lemma preservesLimitsOfShape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type*) [Category* J]
    (_ : forall k : K, PreservesLimitsOfShape J (F ⋙ (evaluation K C).obj k)) :
    PreservesLimitsOfShape J F :=
  ⟨fun {G} => preservesLimit_of_evaluation F G fun _ => PreservesLimitsOfShape.preservesLimit⟩

/--
lemma `preservesLimits_of_evaluation` / 引理 `preservesLimits_of_evaluation`

English:
lemma preservesLimits_of_evaluation
  statement: (F : D ⥤ K ⥤ C)
  proof: ⟨fun {L} _ =>
    preservesLimitsOfShape_of_evaluation F L fun _ => PreservesLimitsOfSize.preservesLimitsOfShape⟩

中文:
引理 preservesLimits_of_evaluation
  结论: (F : D ⥤ K ⥤ C)
  证明: ⟨fun {L} _ =>
    preservesLimitsOfShape_of_evaluation F L fun _ => PreservesLimitsOfSize.preservesLimitsOfShape⟩

Depends on / 依赖: PreservesLimitsOfSize, PreservesLimitsOfSize.preservesLimitsOfShape, preservesLimitsOfShape, preservesLimitsOfShape_of_evaluation
-/
lemma preservesLimits_of_evaluation (F : D ⥤ K ⥤ C)
    (_ : forall k : K, PreservesLimitsOfSize.{w', w} (F ⋙ (evaluation K C).obj k)) :
    PreservesLimitsOfSize.{w', w} F :=
  ⟨fun {L} _ =>
    preservesLimitsOfShape_of_evaluation F L fun _ => PreservesLimitsOfSize.preservesLimitsOfShape⟩

/--
Instance `preservesLimits_const` / 实例 `preservesLimits_const`

English:
instance preservesLimits_const
  signature: : PreservesLimitsOfSize.{w', w} (const D : C ⥤ _)
  body: preservesLimits_of_evaluation _ fun _ =>
preservesLimits_of_natIso Iso.symm constCompEvaluationObj _ _

中文:
实例 preservesLimits_const
  签名: : 保持LimitsOfSize.{w', w} (const D : C ⥤ _)
  定义体: preservesLimits_of_evaluation _ fun _ =>
preservesLimits_of_natIso Iso.symm constCompEvaluationObj _ _

Depends on / 依赖: Iso.symm, constCompEvaluationObj, preservesLimits_of_evaluation, preservesLimits_of_natIso
-/
instance preservesLimits_const : PreservesLimitsOfSize.{w', w} (const D : C ⥤ _) :=
  preservesLimits_of_evaluation _ fun _ =>
preservesLimits_of_natIso Iso.symm constCompEvaluationObj _ _

/--
Instance `evaluation_preservesColimits` / 实例 `evaluation_preservesColimits`

English:
instance evaluation_preservesColimits
  signature: [HasColimits C] (k : K)
  body: inferInstance

中文:
实例 evaluation_preservesColimits
  签名: [有余极限 C] (k : K)
  定义体: inferInstance
-/
instance evaluation_preservesColimits [HasColimits C] (k : K) :
    PreservesColimits ((evaluation K C).obj k) where
  preservesColimitsOfShape := inferInstance

/--
lemma `preservesColimit_of_evaluation` / 引理 `preservesColimit_of_evaluation`

English:
lemma preservesColimit_of_evaluation
  statement: (F : D ⥤ K ⥤ C) (G : J ⥤ D)
  proof: ⟨fun {c} hc => ⟨by
    apply evaluationJointlyReflectsColimits
    intro X
    haveI := H X
    change IsColimit ((F ⋙ (evaluation K C).obj X).mapCocone c)
    exact isColimitOfPreserves _ hc⟩⟩

中文:
引理 preservesColimit_of_evaluation
  结论: (F : D ⥤ K ⥤ C) (G : J ⥤ D)
  证明: ⟨fun {c} hc => ⟨by
    apply evaluationJointlyReflectsColimits
    intro X
    haveI := H X
    change IsColimit ((F ⋙ (evaluation K C).obj X).mapCocone c)
    exact isColimitOfPreserves _ hc⟩⟩

Depends on / 依赖: IsColimit, evaluation, evaluationJointlyReflectsColimits, isColimitOfPreserves, mapCocone
-/
lemma preservesColimit_of_evaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D)
    (H : forall k, PreservesColimit G (F ⋙ (evaluation K C).obj k)) : PreservesColimit G F :=
  ⟨fun {c} hc => ⟨by
    apply evaluationJointlyReflectsColimits
    intro X
    haveI := H X
    change IsColimit ((F ⋙ (evaluation K C).obj X).mapCocone c)
    exact isColimitOfPreserves _ hc⟩⟩

/--
lemma `preservesColimitsOfShape_of_evaluation` / 引理 `preservesColimitsOfShape_of_evaluation`

English:
lemma preservesColimitsOfShape_of_evaluation
  statement: (F : D ⥤ K ⥤ C) (J : Type*) [Category* J]
  proof: ⟨fun {G} => preservesColimit_of_evaluation F G fun _ => PreservesColimitsOfShape.preservesColimit⟩

中文:
引理 preservesColimitsOfShape_of_evaluation
  结论: (F : D ⥤ K ⥤ C) (J : 类型) [范畴* J]
  证明: ⟨fun {G} => preservesColimit_of_evaluation F G fun _ => PreservesColimitsOfShape.preservesColimit⟩

Depends on / 依赖: PreservesColimitsOfShape, PreservesColimitsOfShape.preservesColimit, preservesColimit, preservesColimit_of_evaluation
-/
lemma preservesColimitsOfShape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type*) [Category* J]
    (_ : forall k : K, PreservesColimitsOfShape J (F ⋙ (evaluation K C).obj k)) :
    PreservesColimitsOfShape J F :=
  ⟨fun {G} => preservesColimit_of_evaluation F G fun _ => PreservesColimitsOfShape.preservesColimit⟩

/--
lemma `preservesColimits_of_evaluation` / 引理 `preservesColimits_of_evaluation`

English:
lemma preservesColimits_of_evaluation
  statement: (F : D ⥤ K ⥤ C)
  proof: ⟨fun {L} _ =>
    preservesColimitsOfShape_of_evaluation F L fun _ =>
      PreservesColimitsOfSize.preservesColimitsOfShape⟩

中文:
引理 preservesColimits_of_evaluation
  结论: (F : D ⥤ K ⥤ C)
  证明: ⟨fun {L} _ =>
    preservesColimitsOfShape_of_evaluation F L fun _ =>
      PreservesColimitsOfSize.preservesColimitsOfShape⟩

Depends on / 依赖: PreservesColimitsOfSize, PreservesColimitsOfSize.preservesColimitsOfShape, preservesColimitsOfShape, preservesColimitsOfShape_of_evaluation
-/
lemma preservesColimits_of_evaluation (F : D ⥤ K ⥤ C)
    (_ : forall k : K, PreservesColimitsOfSize.{w', w} (F ⋙ (evaluation K C).obj k)) :
    PreservesColimitsOfSize.{w', w} F :=
  ⟨fun {L} _ =>
    preservesColimitsOfShape_of_evaluation F L fun _ =>
      PreservesColimitsOfSize.preservesColimitsOfShape⟩

/--
Instance `preservesColimits_const` / 实例 `preservesColimits_const`

English:
instance preservesColimits_const
  signature: : PreservesColimitsOfSize.{w', w} (const D : C ⥤ _)
  body: preservesColimits_of_evaluation _ fun _ =>
preservesColimits_of_natIso Iso.symm constCompEvaluationObj _ _

中文:
实例 preservesColimits_const
  签名: : 保持余limitsOfSize.{w', w} (const D : C ⥤ _)
  定义体: preservesColimits_of_evaluation _ fun _ =>
preservesColimits_of_natIso Iso.symm constCompEvaluationObj _ _

Depends on / 依赖: Iso.symm, constCompEvaluationObj, preservesColimits_of_evaluation, preservesColimits_of_natIso
-/
instance preservesColimits_const : PreservesColimitsOfSize.{w', w} (const D : C ⥤ _) :=
  preservesColimits_of_evaluation _ fun _ =>
preservesColimits_of_natIso Iso.symm constCompEvaluationObj _ _

open CategoryTheory.prod

set_option backward.isDefEq.respectTransparency false in
/-- The limit of a diagram `F : J ⥤ K ⥤ C` is isomorphic to the functor given by
the individual limits on objects. -/
@[simps!]
/--
Definition of `limitIsoFlipCompLim` / `limitIsoFlipCompLim` 的定义

English:
definition limitIsoFlipCompLim
  signature: [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C)
  body: NatIso.ofComponents (limitObjIsoLimitCompEvaluation F)

中文:
定义 limitIsoFlipCompLim
  签名: [有形状极限 J C] (F : J ⥤ K ⥤ C)
  定义体: NatIso.ofComponents (limitObjIsoLimitCompEvaluation F)

Depends on / 依赖: NatIso, NatIso.ofComponents, limitObjIsoLimitCompEvaluation, ofComponents
-/
def limitIsoFlipCompLim [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) : limit F ≅ F.flip ⋙ lim :=
  NatIso.ofComponents (limitObjIsoLimitCompEvaluation F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `limitIsoFlipCompLim` is natural with respect to diagrams. -/
@[simps!]
/--
Definition of `limIsoFlipCompWhiskerLim` / `limIsoFlipCompWhiskerLim` 的定义

English:
definition limIsoFlipCompWhiskerLim
  signature: [HasLimitsOfShape J C]
  body: (NatIso.ofComponents (limitIsoFlipCompLim · |>.symm) fun {F G} η => by
    ext k
    apply limit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app (limMap η)]).symm

中文:
定义 limIsoFlipCompWhiskerLim
  签名: [有形状极限 J C]
  定义体: (NatIso.ofComponents (limitIsoFlipCompLim · |>.symm) fun {F G} η => by
    ext k
    apply limit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app (limMap η)]).symm

Depends on / 依赖: NatIso, NatIso.ofComponents, NatTrans, NatTrans.comp_app, comp_app, comp_evaluation, limMap, limitIsoFlipCompLim, limit_obj_ext, ofComponents
-/
def limIsoFlipCompWhiskerLim [HasLimitsOfShape J C] :
    lim ≅ flipFunctor J K C ⋙ (whiskeringRight _ _ _).obj lim :=
  (NatIso.ofComponents (limitIsoFlipCompLim · |>.symm) fun {F G} η => by
    ext k
    apply limit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app (limMap η)]).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A variant of `limitIsoFlipCompLim` where the arguments of `F` are flipped. -/
@[simps!]
/--
Definition of `limitFlipIsoCompLim` / `limitFlipIsoCompLim` 的定义

English:
definition limitFlipIsoCompLim
  signature: [HasLimitsOfShape J C] (F : K ⥤ J ⥤ C)
  body: let f := fun k =>
    limitObjIsoLimitCompEvaluation F.flip k ≪≫ HasLimit.isoOfNatIso (flipCompEvaluation _ _)
  NatIso.ofComponents f

中文:
定义 limitFlipIsoCompLim
  签名: [有形状极限 J C] (F : K ⥤ J ⥤ C)
  定义体: let f := fun k =>
    limitObjIsoLimitCompEvaluation F.flip k ≪≫ HasLimit.isoOfNatIso (flipCompEvaluation _ _)
  NatIso.ofComponents f

Depends on / 依赖: F.flip, HasLimit, HasLimit.isoOfNatIso, NatIso, NatIso.ofComponents, flipCompEvaluation, isoOfNatIso, limitObjIsoLimitCompEvaluation, ofComponents
-/
def limitFlipIsoCompLim [HasLimitsOfShape J C] (F : K ⥤ J ⥤ C) : limit F.flip ≅ F ⋙ lim :=
  let f := fun k =>
    limitObjIsoLimitCompEvaluation F.flip k ≪≫ HasLimit.isoOfNatIso (flipCompEvaluation _ _)
  NatIso.ofComponents f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `limitFlipIsoCompLim` is natural with respect to diagrams. -/
@[simps!]
/--
Definition of `limCompFlipIsoWhiskerLim` / `limCompFlipIsoWhiskerLim` 的定义

English:
definition limCompFlipIsoWhiskerLim
  signature: [HasLimitsOfShape J C]
  body: (NatIso.ofComponents (limitFlipIsoCompLim · |>.symm) fun {F G} η => by
    ext k
    apply limit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app (limMap _)]).symm

中文:
定义 limCompFlipIsoWhiskerLim
  签名: [有形状极限 J C]
  定义体: (NatIso.ofComponents (limitFlipIsoCompLim · |>.symm) fun {F G} η => by
    ext k
    apply limit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app (limMap _)]).symm

Depends on / 依赖: NatIso, NatIso.ofComponents, NatTrans, NatTrans.comp_app, comp_app, comp_evaluation, limMap, limitFlipIsoCompLim, limit_obj_ext, ofComponents
-/
def limCompFlipIsoWhiskerLim [HasLimitsOfShape J C] :
    flipFunctor K J C ⋙ lim ≅ (whiskeringRight _ _ _).obj lim :=
  (NatIso.ofComponents (limitFlipIsoCompLim · |>.symm) fun {F G} η => by
    ext k
    apply limit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app (limMap _)]).symm

/-- For a functor `G : J ⥤ K ⥤ C`, its limit `K ⥤ C` is given by `(G' : K ⥤ J ⥤ C) ⋙ lim`.
Note that this does not require `K` to be small.
-/
@[simps!]
/--
Definition of `limitIsoSwapCompLim` / `limitIsoSwapCompLim` 的定义

English:
definition limitIsoSwapCompLim
  signature: [HasLimitsOfShape J C] (G : J ⥤ K ⥤ C)
  body: limitIsoFlipCompLim G ≪≫ isoWhiskerRight (flipIsoCurrySwapUncurry _) _

中文:
定义 limitIsoSwapCompLim
  签名: [有形状极限 J C] (G : J ⥤ K ⥤ C)
  定义体: limitIsoFlipCompLim G ≪≫ isoWhiskerRight (flipIsoCurrySwapUncurry _) _

Depends on / 依赖: flipIsoCurrySwapUncurry, isoWhiskerRight, limitIsoFlipCompLim
-/
def limitIsoSwapCompLim [HasLimitsOfShape J C] (G : J ⥤ K ⥤ C) :
    limit G ≅ curry.obj (Prod.swap K J ⋙ uncurry.obj G) ⋙ lim :=
  limitIsoFlipCompLim G ≪≫ isoWhiskerRight (flipIsoCurrySwapUncurry _) _

set_option backward.isDefEq.respectTransparency false in
/-- The colimit of a diagram `F : J ⥤ K ⥤ C` is isomorphic to the functor given by
the individual colimits on objects. -/
@[simps!]
/--
Definition of `colimitIsoFlipCompColim` / `colimitIsoFlipCompColim` 的定义

English:
definition colimitIsoFlipCompColim
  signature: [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
  body: NatIso.ofComponents (colimitObjIsoColimitCompEvaluation F)

中文:
定义 colimitIsoFlipCompColim
  签名: [有形状余极限 J C] (F : J ⥤ K ⥤ C)
  定义体: NatIso.ofComponents (colimitObjIsoColimitCompEvaluation F)

Depends on / 依赖: NatIso, NatIso.ofComponents, colimitObjIsoColimitCompEvaluation, ofComponents
-/
def colimitIsoFlipCompColim [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) : colimit F ≅ F.flip ⋙ colim :=
  NatIso.ofComponents (colimitObjIsoColimitCompEvaluation F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `colimitIsoFlipCompColim` is natural with respect to diagrams. -/
@[simps!]
/--
Definition of `colimIsoFlipCompWhiskerColim` / `colimIsoFlipCompWhiskerColim` 的定义

English:
definition colimIsoFlipCompWhiskerColim
  signature: [HasColimitsOfShape J C]
  body: NatIso.ofComponents colimitIsoFlipCompColim fun {F G} η => by
    ext k
    apply colimit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app_assoc _ (colimMap η)]

中文:
定义 colimIsoFlipCompWhiskerColim
  签名: [有形状余极限 J C]
  定义体: NatIso.ofComponents colimitIsoFlipCompColim fun {F G} η => by
    ext k
    apply colimit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app_assoc _ (colimMap η)]

Depends on / 依赖: NatIso, NatIso.ofComponents, NatTrans, NatTrans.comp_app_assoc, colimMap, colimitIsoFlipCompColim, colimit_obj_ext, comp_app_assoc, comp_evaluation, ofComponents
-/
def colimIsoFlipCompWhiskerColim [HasColimitsOfShape J C] :
    colim ≅ flipFunctor J K C ⋙ (whiskeringRight _ _ _).obj colim :=
  NatIso.ofComponents colimitIsoFlipCompColim fun {F G} η => by
    ext k
    apply colimit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app_assoc _ (colimMap η)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A variant of `colimitIsoFlipCompColim` where the arguments of `F` are flipped. -/
@[simps!]
/--
Definition of `colimitFlipIsoCompColim` / `colimitFlipIsoCompColim` 的定义

English:
definition colimitFlipIsoCompColim
  signature: [HasColimitsOfShape J C] (F : K ⥤ J ⥤ C)
  body: let f := fun _ =>
      colimitObjIsoColimitCompEvaluation _ _ ≪≫ HasColimit.isoOfNatIso (flipCompEvaluation _ _)
  NatIso.ofComponents f

中文:
定义 colimitFlipIsoCompColim
  签名: [有形状余极限 J C] (F : K ⥤ J ⥤ C)
  定义体: let f := fun _ =>
      colimitObjIsoColimitCompEvaluation _ _ ≪≫ HasColimit.isoOfNatIso (flipCompEvaluation _ _)
  NatIso.ofComponents f

Depends on / 依赖: HasColimit, HasColimit.isoOfNatIso, NatIso, NatIso.ofComponents, colimitObjIsoColimitCompEvaluation, flipCompEvaluation, isoOfNatIso, ofComponents
-/
def colimitFlipIsoCompColim [HasColimitsOfShape J C] (F : K ⥤ J ⥤ C) : colimit F.flip ≅ F ⋙ colim :=
  let f := fun _ =>
      colimitObjIsoColimitCompEvaluation _ _ ≪≫ HasColimit.isoOfNatIso (flipCompEvaluation _ _)
  NatIso.ofComponents f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `colimitFlipIsoCompColim` is natural with respect to diagrams. -/
@[simps!]
/--
Definition of `colimCompFlipIsoWhiskerColim` / `colimCompFlipIsoWhiskerColim` 的定义

English:
definition colimCompFlipIsoWhiskerColim
  signature: [HasColimitsOfShape J C]
  body: NatIso.ofComponents colimitFlipIsoCompColim fun {F G} η => by
    ext k
    apply colimit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app_assoc _ (colimMap _)]

中文:
定义 colimCompFlipIsoWhiskerColim
  签名: [有形状余极限 J C]
  定义体: NatIso.ofComponents colimitFlipIsoCompColim fun {F G} η => by
    ext k
    apply colimit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app_assoc _ (colimMap _)]

Depends on / 依赖: NatIso, NatIso.ofComponents, NatTrans, NatTrans.comp_app_assoc, colimMap, colimitFlipIsoCompColim, colimit_obj_ext, comp_app_assoc, comp_evaluation, ofComponents
-/
def colimCompFlipIsoWhiskerColim [HasColimitsOfShape J C] :
    flipFunctor K J C ⋙ colim ≅ (whiskeringRight _ _ _).obj colim :=
  NatIso.ofComponents colimitFlipIsoCompColim fun {F G} η => by
    ext k
    apply colimit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app_assoc _ (colimMap _)]

/-- For a functor `G : J ⥤ K ⥤ C`, its colimit `K ⥤ C` is given by `(G' : K ⥤ J ⥤ C) ⋙ colim`.
Note that this does not require `K` to be small.
-/
@[simps!]
/--
Definition of `colimitIsoSwapCompColim` / `colimitIsoSwapCompColim` 的定义

English:
definition colimitIsoSwapCompColim
  signature: [HasColimitsOfShape J C] (G : J ⥤ K ⥤ C)
  body: colimitIsoFlipCompColim G ≪≫ isoWhiskerRight (flipIsoCurrySwapUncurry _) _

中文:
定义 colimitIsoSwapCompColim
  签名: [有形状余极限 J C] (G : J ⥤ K ⥤ C)
  定义体: colimitIsoFlipCompColim G ≪≫ isoWhiskerRight (flipIsoCurrySwapUncurry _) _

Depends on / 依赖: colimitIsoFlipCompColim, flipIsoCurrySwapUncurry, isoWhiskerRight
-/
def colimitIsoSwapCompColim [HasColimitsOfShape J C] (G : J ⥤ K ⥤ C) :
    colimit G ≅ curry.obj (Prod.swap K J ⋙ uncurry.obj G) ⋙ colim :=
  colimitIsoFlipCompColim G ≪≫ isoWhiskerRight (flipIsoCurrySwapUncurry _) _

end

end Limits

end CategoryTheory
