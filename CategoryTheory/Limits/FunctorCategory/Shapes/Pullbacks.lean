/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks in functor categories

We prove the isomorphism `(pullback f g).obj d ≅ pullback (f.app d) (g.app d)`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F G H : D ⥤ C}

section Pullback

set_option backward.isDefEq.respectTransparency false in
/-- Given functors `F G H` and natural transformations `f : F ⟶ H` and `g : g : G ⟶ H`, together
with a collection of limiting pullback cones for each cospan `F X ⟶ H X, G X ⟶ H X`, we can stitch
them together to give a pullback cone for the cospan formed by `f` and `g`.
`combinePullbackConesIsLimit` shows that this pullback cone is limiting. -/
@[simps!]
/--
Definition of `PullbackCone.combine` / `PullbackCone.combine` 的定义

English:
definition PullbackCone.combine
  signature: (f : F ⟶ H) (g : G ⟶ H) (c : forall X, PullbackCone (f.app X) (g.app X))
  body: PullbackCone.mk (W := {
    obj X := (c X).pt
    map {X Y} h := (hc Y).lift ⟨_, (c X).π ≫ cospanHomMk (H.map h) (F.map h) (G.map h)⟩
map_id _ := (hc _).hom_ext by rintro (_ | _ | _); all_goals simp
map_comp _ _ := (hc _).hom_ext by rintro (_ | _ | _); all_goals simp })
    { app X := (c X).fst }
    { app X := (c X).snd }
    (by ext; simp [(c _).condition])

中文:
定义 PullbackCone.combine
  签名: (f : F ⟶ H) (g : G ⟶ H) (c : 对任意 X, PullbackCone (f.app X) (g.app X))
  定义体: PullbackCone.mk (W := {
    obj X := (c X).pt
    map {X Y} h := (hc Y).lift ⟨_, (c X).π ≫ cospanHomMk (H.map h) (F.map h) (G.map h)⟩
map_id _ := (hc _).hom_ext by rintro (_ | _ | _); all_goals simp
map_comp _ _ := (hc _).hom_ext by rintro (_ | _ | _); all_goals simp })
    { app X := (c X).fst }
    { app X := (c X).snd }
    (by ext; simp [(c _).condition])

Depends on / 依赖: F.map, G.map, H.map, PullbackCone, PullbackCone.mk, all_goals, condition, cospanHomMk, hom_ext, map_comp, map_id
-/
def PullbackCone.combine (f : F ⟶ H) (g : G ⟶ H) (c : forall X, PullbackCone (f.app X) (g.app X))
    (hc : forall X, IsLimit (c X)) : PullbackCone f g :=
  PullbackCone.mk (W := {
    obj X := (c X).pt
    map {X Y} h := (hc Y).lift ⟨_, (c X).π ≫ cospanHomMk (H.map h) (F.map h) (G.map h)⟩
map_id _ := (hc _).hom_ext by rintro (_ | _ | _); all_goals simp
map_comp _ _ := (hc _).hom_ext by rintro (_ | _ | _); all_goals simp })
    { app X := (c X).fst }
    { app X := (c X).snd }
    (by ext; simp [(c _).condition])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `PullbackCone.combineIsLimit` / `PullbackCone.combineIsLimit` 的定义

English:
definition PullbackCone.combineIsLimit
  signature: (f : F ⟶ H) (g : G ⟶ H)
  body: evaluationJointlyReflectsLimits _ fun k => by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (hc k)
    · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · refine Cone.ext (Iso.refl _) ?_
      rintro (_ | _ | _)
      all_goals cat_disch

中文:
定义 PullbackCone.combineIsLimit
  签名: (f : F ⟶ H) (g : G ⟶ H)
  定义体: evaluationJointlyReflectsLimits _ fun k => by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (hc k)
    · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · refine Cone.ext (Iso.refl _) ?_
      rintro (_ | _ | _)
      all_goals cat_disch

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.equivOfNatIsoOfIso, Iso.refl, all_goals, cat_disch, cospanIsoMk, equivOfNatIsoOfIso, evaluationJointlyReflectsLimits
-/
def PullbackCone.combineIsLimit (f : F ⟶ H) (g : G ⟶ H)
    (c : forall X, PullbackCone (f.app X) (g.app X)) (hc : forall X, IsLimit (c X)) :
    IsLimit (combine f g c hc) :=
  evaluationJointlyReflectsLimits _ fun k => by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (hc k)
    · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · refine Cone.ext (Iso.refl _) ?_
      rintro (_ | _ | _)
      all_goals cat_disch

variable [HasPullbacks C]

/--
Definition of `pullbackObjIso` / `pullbackObjIso` 的定义

English:
definition pullbackObjIso
  signature: (f : F ⟶ H) (g : G ⟶ H) (d : D)
  body: limitObjIsoLimitCompEvaluation (cospan f g) d ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _)

中文:
定义 pullbackObjIso
  签名: (f : F ⟶ H) (g : G ⟶ H) (d : D)
  定义体: limitObjIsoLimitCompEvaluation (cospan f g) d ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _)

Depends on / 依赖: HasLimit, HasLimit.isoOfNatIso, cospan, diagramIsoCospan, isoOfNatIso, limitObjIsoLimitCompEvaluation
-/
noncomputable def pullbackObjIso (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullback f g).obj d ≅ pullback (f.app d) (g.app d) :=
  limitObjIsoLimitCompEvaluation (cospan f g) d ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackObjIso_hom_comp_fst` / 定理 `pullbackObjIso_hom_comp_fst`

English:
theorem pullbackObjIso_hom_comp_fst
  given: (f : F ⟶ H) (g : G ⟶ H) (d : D)
  proof: by
  simp [pullbackObjIso]

中文:
定理 pullbackObjIso_hom_comp_fst
  条件: (f : F ⟶ H) (g : G ⟶ H) (d : D)
  证明: by
  simp [pullbackObjIso]

Depends on / 依赖: pullbackObjIso
-/
theorem pullbackObjIso_hom_comp_fst (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).hom ≫ pullback.fst (f.app d) (g.app d) = (pullback.fst f g).app d := by
  simp [pullbackObjIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackObjIso_hom_comp_snd` / 定理 `pullbackObjIso_hom_comp_snd`

English:
theorem pullbackObjIso_hom_comp_snd
  given: (f : F ⟶ H) (g : G ⟶ H) (d : D)
  proof: by
  simp [pullbackObjIso]

中文:
定理 pullbackObjIso_hom_comp_snd
  条件: (f : F ⟶ H) (g : G ⟶ H) (d : D)
  证明: by
  simp [pullbackObjIso]

Depends on / 依赖: pullbackObjIso
-/
theorem pullbackObjIso_hom_comp_snd (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).hom ≫ pullback.snd (f.app d) (g.app d) = (pullback.snd f g).app d := by
  simp [pullbackObjIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackObjIso_inv_comp_fst` / 定理 `pullbackObjIso_inv_comp_fst`

English:
theorem pullbackObjIso_inv_comp_fst
  given: (f : F ⟶ H) (g : G ⟶ H) (d : D)
  proof: by
  simp [pullbackObjIso]

中文:
定理 pullbackObjIso_inv_comp_fst
  条件: (f : F ⟶ H) (g : G ⟶ H) (d : D)
  证明: by
  simp [pullbackObjIso]

Depends on / 依赖: pullbackObjIso
-/
theorem pullbackObjIso_inv_comp_fst (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).inv ≫ (pullback.fst f g).app d = pullback.fst (f.app d) (g.app d) := by
  simp [pullbackObjIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackObjIso_inv_comp_snd` / 定理 `pullbackObjIso_inv_comp_snd`

English:
theorem pullbackObjIso_inv_comp_snd
  given: (f : F ⟶ H) (g : G ⟶ H) (d : D)
  proof: by
  simp [pullbackObjIso]

中文:
定理 pullbackObjIso_inv_comp_snd
  条件: (f : F ⟶ H) (g : G ⟶ H) (d : D)
  证明: by
  simp [pullbackObjIso]

Depends on / 依赖: pullbackObjIso
-/
theorem pullbackObjIso_inv_comp_snd (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).inv ≫ (pullback.snd f g).app d = pullback.snd (f.app d) (g.app d) := by
  simp [pullbackObjIso]

end Pullback

section Pushout

variable [HasPushouts C]

/--
Definition of `pushoutObjIso` / `pushoutObjIso` 的定义

English:
definition pushoutObjIso
  signature: (f : F ⟶ G) (g : F ⟶ H) (d : D)
  body: colimitObjIsoColimitCompEvaluation (span f g) d ≪≫ HasColimit.isoOfNatIso (diagramIsoSpan _)

中文:
定义 pushoutObjIso
  签名: (f : F ⟶ G) (g : F ⟶ H) (d : D)
  定义体: colimitObjIsoColimitCompEvaluation (span f g) d ≪≫ HasColimit.isoOfNatIso (diagramIsoSpan _)

Depends on / 依赖: HasColimit, HasColimit.isoOfNatIso, colimitObjIsoColimitCompEvaluation, diagramIsoSpan, isoOfNatIso
-/
noncomputable def pushoutObjIso (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    (pushout f g).obj d ≅ pushout (f.app d) (g.app d) :=
  colimitObjIsoColimitCompEvaluation (span f g) d ≪≫ HasColimit.isoOfNatIso (diagramIsoSpan _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `inl_comp_pushoutObjIso_hom` / 定理 `inl_comp_pushoutObjIso_hom`

English:
theorem inl_comp_pushoutObjIso_hom
  given: (f : F ⟶ G) (g : F ⟶ H) (d : D)
  proof: by
  simp [pushoutObjIso]

中文:
定理 inl_comp_pushoutObjIso_hom
  条件: (f : F ⟶ G) (g : F ⟶ H) (d : D)
  证明: by
  simp [pushoutObjIso]

Depends on / 依赖: pushoutObjIso
-/
theorem inl_comp_pushoutObjIso_hom (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    (pushout.inl f g).app d ≫ (pushoutObjIso f g d).hom = pushout.inl (f.app d) (g.app d) := by
  simp [pushoutObjIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `inr_comp_pushoutObjIso_hom` / 定理 `inr_comp_pushoutObjIso_hom`

English:
theorem inr_comp_pushoutObjIso_hom
  given: (f : F ⟶ G) (g : F ⟶ H) (d : D)
  proof: by
  simp [pushoutObjIso]

中文:
定理 inr_comp_pushoutObjIso_hom
  条件: (f : F ⟶ G) (g : F ⟶ H) (d : D)
  证明: by
  simp [pushoutObjIso]

Depends on / 依赖: pushoutObjIso
-/
theorem inr_comp_pushoutObjIso_hom (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    (pushout.inr f g).app d ≫ (pushoutObjIso f g d).hom = pushout.inr (f.app d) (g.app d) := by
  simp [pushoutObjIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `inl_comp_pushoutObjIso_inv` / 定理 `inl_comp_pushoutObjIso_inv`

English:
theorem inl_comp_pushoutObjIso_inv
  given: (f : F ⟶ G) (g : F ⟶ H) (d : D)
  proof: by
  simp [pushoutObjIso]

中文:
定理 inl_comp_pushoutObjIso_inv
  条件: (f : F ⟶ G) (g : F ⟶ H) (d : D)
  证明: by
  simp [pushoutObjIso]

Depends on / 依赖: pushoutObjIso
-/
theorem inl_comp_pushoutObjIso_inv (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    pushout.inl (f.app d) (g.app d) ≫ (pushoutObjIso f g d).inv = (pushout.inl f g).app d := by
  simp [pushoutObjIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `inr_comp_pushoutObjIso_inv` / 定理 `inr_comp_pushoutObjIso_inv`

English:
theorem inr_comp_pushoutObjIso_inv
  given: (f : F ⟶ G) (g : F ⟶ H) (d : D)
  proof: by
  simp [pushoutObjIso]

中文:
定理 inr_comp_pushoutObjIso_inv
  条件: (f : F ⟶ G) (g : F ⟶ H) (d : D)
  证明: by
  simp [pushoutObjIso]

Depends on / 依赖: pushoutObjIso
-/
theorem inr_comp_pushoutObjIso_inv (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    pushout.inr (f.app d) (g.app d) ≫ (pushoutObjIso f g d).inv = (pushout.inr f g).app d := by
  simp [pushoutObjIso]

end Pushout

end CategoryTheory.Limits
