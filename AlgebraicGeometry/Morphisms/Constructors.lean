/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.RingTheory.RingHomProperties

/-!

# Constructors for properties of morphisms between schemes

This file provides some constructors to obtain morphism properties of schemes from other morphism
properties:

- `AffineTargetMorphismProperty.diagonal` : Given an affine target morphism property `P`,
  `P.diagonal f` holds if `P (pullback.mapDesc f₁ f₂ f)` holds for two affine open
  immersions `f₁` and `f₂`.
- `AffineTargetMorphismProperty.of`: Given a morphism property `P` of schemes,
  this is the restriction of `P` to morphisms with affine target. If `P` is local at the
  target, we have `(toAffineTargetMorphismProperty P).targetAffineLocally = P`, see:
  `MorphismProperty.targetAffineLocally_toAffineTargetMorphismProperty_eq_of_isZariskiLocalAtTarget`
- `MorphismProperty.topologically`: Given a property `P` of maps of topological spaces,
  `(topologically P) f` holds if `P` holds for the underlying continuous map of `f`.
- `MorphismProperty.stalkwise`: Given a property `P` of ring homomorphisms,
  `(stalkwise P) f` holds if `P` holds for all stalk maps.

Also provides API for showing the standard locality and stability properties for these
types of properties.

-/

@[expose] public section

universe u v w

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

section Diagonal

/--
Definition of `AffineTargetMorphismProperty.diagonal` / `AffineTargetMorphismProperty.diagonal` 的定义

English:
definition AffineTargetMorphismProperty.diagonal
  signature: (P : AffineTargetMorphismProperty)
  body: fun {X _} f _ =>
    forall ⦃U₁ U₂ : Scheme⦄ (f₁ : U₁ ⟶ X) (f₂ : U₂ ⟶ X) [IsAffine U₁] [IsAffine U₂] [IsOpenImmersion f₁]
      [IsOpenImmersion f₂], P (pullback.mapDesc f₁ f₂ f)

中文:
定义 AffineTargetMorphismProperty.diagonal
  签名: (P : AffineTargetMorphismProperty)
  定义体: fun {X _} f _ =>
    forall ⦃U₁ U₂ : Scheme⦄ (f₁ : U₁ ⟶ X) (f₂ : U₂ ⟶ X) [IsAffine U₁] [IsAffine U₂] [IsOpenImmersion f₁]
      [IsOpenImmersion f₂], P (pullback.mapDesc f₁ f₂ f)

Depends on / 依赖: IsAffine, IsOpenImmersion, Scheme, mapDesc, pullback, pullback.mapDesc
-/
def AffineTargetMorphismProperty.diagonal (P : AffineTargetMorphismProperty) :
    AffineTargetMorphismProperty :=
  fun {X _} f _ =>
    forall ⦃U₁ U₂ : Scheme⦄ (f₁ : U₁ ⟶ X) (f₂ : U₂ ⟶ X) [IsAffine U₁] [IsAffine U₂] [IsOpenImmersion f₁]
      [IsOpenImmersion f₂], P (pullback.mapDesc f₁ f₂ f)

/--
Instance `AffineTargetMorphismProperty.diagonal_respectsIso` / 实例 `AffineTargetMorphismProperty.diagonal_respectsIso`

English:
instance AffineTargetMorphismProperty.diagonal_respectsIso
  signature: (P : AffineTargetMorphismProperty)
  body: by
  delta AffineTargetMorphismProperty.diagonal
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H _ _
    rw [pullback.mapDesc_comp]; rw [P.cancel_left_of_respectsIso]; rw [P.cancel_right_of_respectsIso]
    apply H
  · introv H _ _
    rw [pullback.mapDesc_comp]; rw [P.cancel_right_of_respectsIso]
    apply H

中文:
实例 AffineTargetMorphismProperty.diagonal_respectsIso
  签名: (P : AffineTargetMorphismProperty)
  定义体: by
  delta AffineTargetMorphismProperty.diagonal
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H _ _
    rw [pullback.mapDesc_comp]; rw [P.cancel_left_of_respectsIso]; rw [P.cancel_right_of_respectsIso]
    apply H
  · introv H _ _
    rw [pullback.mapDesc_comp]; rw [P.cancel_right_of_respectsIso]
    apply H

Depends on / 依赖: AffineTargetMorphismProperty, AffineTargetMorphismProperty.diagonal, AffineTargetMorphismProperty.respectsIso_mk, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso, cancel_left_of_respectsIso, cancel_right_of_respectsIso, diagonal, introv, mapDesc_comp, pullback, pullback.mapDesc_comp, respectsIso_mk
-/
instance AffineTargetMorphismProperty.diagonal_respectsIso (P : AffineTargetMorphismProperty)
    [P.toProperty.RespectsIso] : P.diagonal.toProperty.RespectsIso := by
  delta AffineTargetMorphismProperty.diagonal
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H _ _
    rw [pullback.mapDesc_comp]; rw [P.cancel_left_of_respectsIso]; rw [P.cancel_right_of_respectsIso]
    apply H
  · introv H _ _
    rw [pullback.mapDesc_comp]; rw [P.cancel_right_of_respectsIso]
    apply H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `HasAffineProperty.diagonal_of_openCover` / 定理 `HasAffineProperty.diagonal_of_openCover`

English:
theorem HasAffineProperty.diagonal_of_openCover
  statement: (P) {Q} [HasAffineProperty P Q]
  proof: by
  let := isLocal_affineProperty P
  let 𝒱 := (Scheme.Pullback.openCoverOfBase 𝒰 f f).bind fun i =>
    Scheme.Pullback.openCoverOfLeftRight.{u} (𝒰' i) (𝒰' i) (pullback.snd _ _) (pullback.snd _ _)
  have i1 : forall i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  apply of_openCover 𝒱
  rintro ⟨i, j, k⟩
  dsimp [𝒱]
  convert!
    (Q.cancel_left_of_respectsIso
          ((pullbackDiagonalMapIso _ _ ((𝒰' i).f j) ((𝒰' i).f k)).inv ≫
            pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _)
          (pullback.snd _ _)).mp
      _
      using 1
  · simp
  · ext1 <;> simp
  · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      Category.comp_id]
    convert! h𝒰' i j k
    ext1 <;> simp [Scheme.Cover.pullbackHom]

中文:
定理 有AffineProperty.diagonal_of_openCover
  结论: (P) {Q} [有AffineProperty P Q]
  证明: by
  let := isLocal_affineProperty P
  let 𝒱 := (Scheme.Pullback.openCoverOfBase 𝒰 f f).bind fun i =>
    Scheme.Pullback.openCoverOfLeftRight.{u} (𝒰' i) (𝒰' i) (pullback.snd _ _) (pullback.snd _ _)
  have i1 : forall i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  apply of_openCover 𝒱
  rintro ⟨i, j, k⟩
  dsimp [𝒱]
  convert!
    (Q.cancel_left_of_respectsIso
          ((pullbackDiagonalMapIso _ _ ((𝒰' i).f j) ((𝒰' i).f k)).inv ≫
            pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _)
          (pullback.snd _ _)).mp
      _
      using 1
  · simp
  · ext1 <;> simp
  · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      Category.comp_id]
    convert! h𝒰' i j k
    ext1 <;> simp [Scheme.Cover.pullbackHom]

Depends on / 依赖: IsAffine, Pullback, Q.cancel_left_of_respectsIso, Scheme, Scheme.Pullback.openCoverOfBase, Scheme.Pullback.openCoverOfLeftRight, cancel_left_of_respectsIso, convert, infer_instance, isLocal_affineProperty, of_openCover, openCoverOfBase, openCoverOfLeftRight, pullback, pullback.map, pullback.snd, pullbackDiagonalMapIso
-/
theorem HasAffineProperty.diagonal_of_openCover (P) {Q} [HasAffineProperty P Q]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{v} Y) [forall i, IsAffine (𝒰.X i)]
    (𝒰' : forall i, Scheme.OpenCover.{w} (pullback f (𝒰.f i))) [forall i j, IsAffine ((𝒰' i).X j)]
    (h𝒰' : forall i j k,
      Q (pullback.mapDesc ((𝒰' i).f j) ((𝒰' i).f k) (𝒰.pullbackHom f i))) :
    P.diagonal f := by
  let := isLocal_affineProperty P
  let 𝒱 := (Scheme.Pullback.openCoverOfBase 𝒰 f f).bind fun i =>
    Scheme.Pullback.openCoverOfLeftRight.{u} (𝒰' i) (𝒰' i) (pullback.snd _ _) (pullback.snd _ _)
  have i1 : forall i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  apply of_openCover 𝒱
  rintro ⟨i, j, k⟩
  dsimp [𝒱]
  convert!
    (Q.cancel_left_of_respectsIso
          ((pullbackDiagonalMapIso _ _ ((𝒰' i).f j) ((𝒰' i).f k)).inv ≫
            pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _)
          (pullback.snd _ _)).mp
      _
      using 1
  · simp
  · ext1 <;> simp
  · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      Category.comp_id]
    convert! h𝒰' i j k
    ext1 <;> simp [Scheme.Cover.pullbackHom]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `HasAffineProperty.diagonal_of_openCover_diagonal` / 定理 `HasAffineProperty.diagonal_of_openCover_diagonal`

English:
theorem HasAffineProperty.diagonal_of_openCover_diagonal
  proof: diagonal_of_openCover P f 𝒰 (fun _ => Scheme.affineCover _)
    (fun _ _ _ => h𝒰 _ _ _)

中文:
定理 有AffineProperty.diagonal_of_openCover_diagonal
  证明: diagonal_of_openCover P f 𝒰 (fun _ => Scheme.affineCover _)
    (fun _ _ _ => h𝒰 _ _ _)

Depends on / 依赖: Scheme, Scheme.affineCover, affineCover, diagonal_of_openCover
-/
theorem HasAffineProperty.diagonal_of_openCover_diagonal
    (P) {Q} [HasAffineProperty P Q]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover Y) [forall i, IsAffine (𝒰.X i)]
    (h𝒰 : forall i, Q.diagonal (𝒰.pullbackHom f i)) :
    P.diagonal f :=
  diagonal_of_openCover P f 𝒰 (fun _ => Scheme.affineCover _)
    (fun _ _ _ => h𝒰 _ _ _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `HasAffineProperty.diagonal_of_diagonal_of_isPullback` / 定理 `HasAffineProperty.diagonal_of_diagonal_of_isPullback`

English:
theorem HasAffineProperty.diagonal_of_diagonal_of_isPullback
  proof: by
  let := isLocal_affineProperty P
  rw [← Q.diagonal.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_snd]
  rintro U V f₁ f₂ hU hV hf₁ hf₂
  rw [← Q.cancel_left_of_respectsIso (pullbackDiagonalMapIso f _ f₁ f₂).hom]
  convert! HasAffineProperty.of_isPullback (P := P) (.of_hasPullback _ _) H
  · apply pullback.hom_ext <;> simp
  · infer_instance
  · infer_instance

中文:
定理 有AffineProperty.diagonal_of_diagonal_of_isPullback
  证明: by
  let := isLocal_affineProperty P
  rw [← Q.diagonal.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_snd]
  rintro U V f₁ f₂ hU hV hf₁ hf₂
  rw [← Q.cancel_left_of_respectsIso (pullbackDiagonalMapIso f _ f₁ f₂).hom]
  convert! HasAffineProperty.of_isPullback (P := P) (.of_hasPullback _ _) H
  · apply pullback.hom_ext <;> simp
  · infer_instance
  · infer_instance

Depends on / 依赖: HasAffineProperty, HasAffineProperty.of_isPullback, Q.cancel_left_of_respectsIso, Q.diagonal.cancel_left_of_respectsIso, cancel_left_of_respectsIso, convert, diagonal, h.isoPullback.inv, h.isoPullback_inv_snd, hom_ext, infer_instance, isLocal_affineProperty, isoPullback, isoPullback_inv_snd, of_hasPullback, of_isPullback, pullback, pullback.hom_ext, pullbackDiagonalMapIso
-/
theorem HasAffineProperty.diagonal_of_diagonal_of_isPullback
    (P) {Q} [HasAffineProperty P Q]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {g : U ⟶ Y}
    [IsAffine U] [IsOpenImmersion g]
    {iV : V ⟶ X} {f' : V ⟶ U} (h : IsPullback iV f' f g) (H : P.diagonal f) :
    Q.diagonal f' := by
  let := isLocal_affineProperty P
  rw [← Q.diagonal.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_snd]
  rintro U V f₁ f₂ hU hV hf₁ hf₂
  rw [← Q.cancel_left_of_respectsIso (pullbackDiagonalMapIso f _ f₁ f₂).hom]
  convert! HasAffineProperty.of_isPullback (P := P) (.of_hasPullback _ _) H
  · apply pullback.hom_ext <;> simp
  · infer_instance
  · infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `HasAffineProperty.diagonal_iff` / 定理 `HasAffineProperty.diagonal_iff`

English:
theorem HasAffineProperty.diagonal_iff
  proof: by
  let := isLocal_affineProperty P
  refine ⟨fun hf => ?_, diagonal_of_diagonal_of_isPullback P .of_id_fst⟩
  rw [← Q.diagonal.cancel_left_of_respectsIso
    (pullback.fst (f := f) (g := 𝟙 Y))]; rw [pullback.condition]; rw [Category.comp_id] at hf
  let 𝒰 := X.affineCover.pushforwardIso (inv (pullback.fst (f := f) (g := 𝟙 Y)))
  have (i : _) : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
  exact HasAffineProperty.diagonal_of_openCover.{u, u, u} P f (Scheme.coverOfIsIso (𝟙 _))
    (fun _ => 𝒰) (fun _ _ _ => hf _ _)

中文:
定理 有AffineProperty.diagonal_iff
  证明: by
  let := isLocal_affineProperty P
  refine ⟨fun hf => ?_, diagonal_of_diagonal_of_isPullback P .of_id_fst⟩
  rw [← Q.diagonal.cancel_left_of_respectsIso
    (pullback.fst (f := f) (g := 𝟙 Y))]; rw [pullback.condition]; rw [Category.comp_id] at hf
  let 𝒰 := X.affineCover.pushforwardIso (inv (pullback.fst (f := f) (g := 𝟙 Y)))
  have (i : _) : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
  exact HasAffineProperty.diagonal_of_openCover.{u, u, u} P f (Scheme.coverOfIsIso (𝟙 _))
    (fun _ => 𝒰) (fun _ _ _ => hf _ _)

Depends on / 依赖: Category, Category.comp_id, HasAffineProperty, HasAffineProperty.diagonal_of_openCover, IsAffine, Q.diagonal.cancel_left_of_respectsIso, Scheme, Scheme.coverOfIsIso, X.affineCover.pushforwardIso, affineCover, cancel_left_of_respectsIso, comp_id, condition, coverOfIsIso, diagonal, diagonal_of_diagonal_of_isPullback, diagonal_of_openCover, infer_instance, isLocal_affineProperty, of_id_fst
-/
theorem HasAffineProperty.diagonal_iff
    (P) {Q} [HasAffineProperty P Q] {X Y : Scheme.{u}} {f : X ⟶ Y} [IsAffine Y] :
    Q.diagonal f ↔ P.diagonal f := by
  let := isLocal_affineProperty P
  refine ⟨fun hf => ?_, diagonal_of_diagonal_of_isPullback P .of_id_fst⟩
  rw [← Q.diagonal.cancel_left_of_respectsIso
    (pullback.fst (f := f) (g := 𝟙 Y))]; rw [pullback.condition]; rw [Category.comp_id] at hf
  let 𝒰 := X.affineCover.pushforwardIso (inv (pullback.fst (f := f) (g := 𝟙 Y)))
  have (i : _) : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
  exact HasAffineProperty.diagonal_of_openCover.{u, u, u} P f (Scheme.coverOfIsIso (𝟙 _))
    (fun _ => 𝒰) (fun _ _ _ => hf _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `AffineTargetMorphismProperty.diagonal_of_openCover_source` / 定理 `AffineTargetMorphismProperty.diagonal_of_openCover_source`

English:
theorem AffineTargetMorphismProperty.diagonal_of_openCover_source
  proof: by
  rw [HasAffineProperty.diagonal_iff (targetAffineLocally Q)]
  let 𝒱 := Scheme.Pullback.openCoverOfLeftRight.{u} 𝒰 𝒰 f f
  have i1 : forall i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  refine HasAffineProperty.of_openCover (P := targetAffineLocally Q) 𝒱 fun i => ?_
  dsimp [𝒱, Scheme.Cover.pullbackHom]
  have : IsPullback (pullback.fst _ _ ≫ 𝒰.f _) (pullback.mapDesc (𝒰.f i.1) (𝒰.f i.2) f)
      (pullback.diagonal f) (pullback.map _ _ _ _ (𝒰.f _) (𝒰.f _) (𝟙 Y) (by simp) (by simp)) :=
    .of_iso (pullback_fst_map_snd_isPullback f (𝟙 _) (𝒰.f i.1 ≫ pullback.lift (𝟙 _) f)
      (𝒰.f i.2 ≫ pullback.lift (𝟙 _) f)) (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _)
      (pullback.fst _ _) (by simp) (by simp))) (.refl _) (pullback.congrHom (by simp) (by simp))
      (.refl _) (by simp) (by cat_disch) (by simp) (by cat_disch)
  rw [← Q.cancel_left_of_respectsIso this.isoPullback.hom]; rw [IsPullback.isoPullback_hom_snd]
  exact h𝒰 _ _

中文:
定理 AffineTargetMorphismProperty.diagonal_of_openCover_source
  证明: by
  rw [HasAffineProperty.diagonal_iff (targetAffineLocally Q)]
  let 𝒱 := Scheme.Pullback.openCoverOfLeftRight.{u} 𝒰 𝒰 f f
  have i1 : forall i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  refine HasAffineProperty.of_openCover (P := targetAffineLocally Q) 𝒱 fun i => ?_
  dsimp [𝒱, Scheme.Cover.pullbackHom]
  have : IsPullback (pullback.fst _ _ ≫ 𝒰.f _) (pullback.mapDesc (𝒰.f i.1) (𝒰.f i.2) f)
      (pullback.diagonal f) (pullback.map _ _ _ _ (𝒰.f _) (𝒰.f _) (𝟙 Y) (by simp) (by simp)) :=
    .of_iso (pullback_fst_map_snd_isPullback f (𝟙 _) (𝒰.f i.1 ≫ pullback.lift (𝟙 _) f)
      (𝒰.f i.2 ≫ pullback.lift (𝟙 _) f)) (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _)
      (pullback.fst _ _) (by simp) (by simp))) (.refl _) (pullback.congrHom (by simp) (by simp))
      (.refl _) (by simp) (by cat_disch) (by simp) (by cat_disch)
  rw [← Q.cancel_left_of_respectsIso this.isoPullback.hom]; rw [IsPullback.isoPullback_hom_snd]
  exact h𝒰 _ _

Depends on / 依赖: HasAffineProperty, HasAffineProperty.diagonal_iff, HasAffineProperty.of_openCover, IsAffine, IsPullback, Pullback, Scheme, Scheme.Cover.pullbackHom, Scheme.Pullback.openCoverOfLeftRight, diagonal, diagonal_iff, infer_instance, mapDesc, of_iso, of_openCover, openCoverOfLeftRight, pullback, pullback.diagonal, pullback.fst, pullback.map
-/
theorem AffineTargetMorphismProperty.diagonal_of_openCover_source
    {Q : AffineTargetMorphismProperty} [Q.IsLocal]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{v} X) [forall i, IsAffine (𝒰.X i)]
    [IsAffine Y] (h𝒰 : forall i j, Q (pullback.mapDesc (𝒰.f i) (𝒰.f j) f)) :
    Q.diagonal f := by
  rw [HasAffineProperty.diagonal_iff (targetAffineLocally Q)]
  let 𝒱 := Scheme.Pullback.openCoverOfLeftRight.{u} 𝒰 𝒰 f f
  have i1 : forall i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  refine HasAffineProperty.of_openCover (P := targetAffineLocally Q) 𝒱 fun i => ?_
  dsimp [𝒱, Scheme.Cover.pullbackHom]
  have : IsPullback (pullback.fst _ _ ≫ 𝒰.f _) (pullback.mapDesc (𝒰.f i.1) (𝒰.f i.2) f)
      (pullback.diagonal f) (pullback.map _ _ _ _ (𝒰.f _) (𝒰.f _) (𝟙 Y) (by simp) (by simp)) :=
    .of_iso (pullback_fst_map_snd_isPullback f (𝟙 _) (𝒰.f i.1 ≫ pullback.lift (𝟙 _) f)
      (𝒰.f i.2 ≫ pullback.lift (𝟙 _) f)) (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _)
      (pullback.fst _ _) (by simp) (by simp))) (.refl _) (pullback.congrHom (by simp) (by simp))
      (.refl _) (by simp) (by cat_disch) (by simp) (by cat_disch)
  rw [← Q.cancel_left_of_respectsIso this.isoPullback.hom]; rw [IsPullback.isoPullback_hom_snd]
  exact h𝒰 _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `HasAffineProperty.diagonal_affineProperty_isLocal` / 实例 `HasAffineProperty.diagonal_affineProperty_isLocal`

English:
instance HasAffineProperty.diagonal_affineProperty_isLocal
  body: inferInstance
  to_basicOpen {_ Y} _ f r hf :=
    diagonal_of_diagonal_of_isPullback (targetAffineLocally Q)
      (isPullback_morphismRestrict f (Y.basicOpen r)).flip
      ((diagonal_iff (targetAffineLocally Q)).mp hf)
  of_basicOpenCover {X Y} _ f s hs hs' := by
    refine (diagonal_iff (targetAffineLocally Q)).mpr ?_
    let 𝒰 := Y.openCoverOfIsOpenCover _
      ((isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs)
    have (i : _) : IsAffine (𝒰.X i) := (isAffineOpen_top Y).basicOpen i.1
    refine diagonal_of_openCover_diagonal (targetAffineLocally Q) f 𝒰 ?_
    intro i
    exact (Q.diagonal.arrow_mk_iso_iff
      (morphismRestrictEq _ (by simp [𝒰]) ≪≫ morphismRestrictOpensRange _ _)).mp (hs' i)

中文:
实例 有AffineProperty.diagonal_affineProperty_isLocal
  定义体: inferInstance
  to_basicOpen {_ Y} _ f r hf :=
    diagonal_of_diagonal_of_isPullback (targetAffineLocally Q)
      (isPullback_morphismRestrict f (Y.basicOpen r)).flip
      ((diagonal_iff (targetAffineLocally Q)).mp hf)
  of_basicOpenCover {X Y} _ f s hs hs' := by
    refine (diagonal_iff (targetAffineLocally Q)).mpr ?_
    let 𝒰 := Y.openCoverOfIsOpenCover _
      ((isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs)
    have (i : _) : IsAffine (𝒰.X i) := (isAffineOpen_top Y).basicOpen i.1
    refine diagonal_of_openCover_diagonal (targetAffineLocally Q) f 𝒰 ?_
    intro i
    exact (Q.diagonal.arrow_mk_iso_iff
      (morphismRestrictEq _ (by simp [𝒰]) ≪≫ morphismRestrictOpensRange _ _)).mp (hs' i)
-/
instance HasAffineProperty.diagonal_affineProperty_isLocal
    {Q : AffineTargetMorphismProperty} [Q.IsLocal] :
    Q.diagonal.IsLocal where
  respectsIso := inferInstance
  to_basicOpen {_ Y} _ f r hf :=
    diagonal_of_diagonal_of_isPullback (targetAffineLocally Q)
      (isPullback_morphismRestrict f (Y.basicOpen r)).flip
      ((diagonal_iff (targetAffineLocally Q)).mp hf)
  of_basicOpenCover {X Y} _ f s hs hs' := by
    refine (diagonal_iff (targetAffineLocally Q)).mpr ?_
    let 𝒰 := Y.openCoverOfIsOpenCover _
      ((isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs)
    have (i : _) : IsAffine (𝒰.X i) := (isAffineOpen_top Y).basicOpen i.1
    refine diagonal_of_openCover_diagonal (targetAffineLocally Q) f 𝒰 ?_
    intro i
    exact (Q.diagonal.arrow_mk_iso_iff
      (morphismRestrictEq _ (by simp [𝒰]) ≪≫ morphismRestrictOpensRange _ _)).mp (hs' i)

instance (P) {Q} [HasAffineProperty P Q] : HasAffineProperty P.diagonal Q.diagonal where
  isLocal_affineProperty := letI := HasAffineProperty.isLocal_affineProperty P; inferInstance
  eq_targetAffineLocally' := by
    ext X Y f
    let := HasAffineProperty.isLocal_affineProperty P
    constructor
    · exact fun H U => HasAffineProperty.diagonal_of_diagonal_of_isPullback P
        (isPullback_morphismRestrict f U).flip H
    · exact fun H => HasAffineProperty.diagonal_of_openCover_diagonal P f Y.affineCover
        (fun i => of_targetAffineLocally_of_isPullback (.of_hasPullback _ _) H)

instance (P) [IsZariskiLocalAtTarget P] : IsZariskiLocalAtTarget P.diagonal :=
  letI := HasAffineProperty.of_isZariskiLocalAtTarget P
  inferInstance

open MorphismProperty in
instance (P : MorphismProperty Scheme)
    [P.HasOfPostcompProperty @IsOpenImmersion] [P.RespectsRight @IsOpenImmersion]
    [IsZariskiLocalAtSource P] : IsZariskiLocalAtSource P.diagonal := by
  let g {X Y : Scheme} (f : X ⟶ Y) (U : X.Opens) :=
    pullback.map (U.ι ≫ f) (U.ι ≫ f) f f U.ι U.ι (𝟙 Y) (by simp) (by simp)
  refine IsZariskiLocalAtSource.mk' (fun {X Y} f U hf => ?_) (fun {X Y} f {ι} U hU hf => ?_)
  · change P _
    apply P.of_postcomp (W' := @IsOpenImmersion) (pullback.diagonal (U.ι ≫ f)) (g f U) inferInstance
    rw [← pullback.comp_diagonal]
    apply IsZariskiLocalAtSource.comp
    exact hf
  · change P _
    refine IsZariskiLocalAtSource.of_iSup_eq_top U hU fun i => ?_
    rw [pullback.comp_diagonal]
    exact RespectsRight.postcomp (P := P) (Q := @IsOpenImmersion) (g _ _) inferInstance _ (hf i)

end Diagonal

section Universally

/--
theorem `universally_isZariskiLocalAtTarget` / 定理 `universally_isZariskiLocalAtTarget`

English:
theorem universally_isZariskiLocalAtTarget
  statement: (P : MorphismProperty Scheme)
  proof: by
  apply IsZariskiLocalAtTarget.mk'
  · exact fun {X Y} f U => P.universally.of_isPullback
      (isPullback_morphismRestrict f U).flip
  · intro X Y f ι U hU H X' Y' i₁ i₂ f' h
    apply hP₂ _ (fun i => i₂ ⁻¹ᵁ U i)
    · simp only [IsOpenCover, ← top_le_iff] at hU ⊢
      rintro x -
      simpa using @hU (i₂ x) trivial
    · rintro i
      refine H _ ((X'.isoOfEq ?_).hom ≫ i₁ ∣_ _) (i₂ ∣_ _) _ ?_
      · exact congr($(h.1.1) ⁻¹ᵁ U i)
      · rw [← (isPullback_morphismRestrict f _).paste_vert_iff]
        · simp only [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
          exact (isPullback_morphismRestrict f' (i₂ ⁻¹ᵁ U i)).paste_vert h
        · rw [← cancel_mono (Scheme.Opens.ι _)]
          simp [morphismRestrict_ι_assoc, h.1.1]

中文:
定理 universally_isZariskiLocalAtTarget
  结论: (P : MorphismProperty 概形)
  证明: by
  apply IsZariskiLocalAtTarget.mk'
  · exact fun {X Y} f U => P.universally.of_isPullback
      (isPullback_morphismRestrict f U).flip
  · intro X Y f ι U hU H X' Y' i₁ i₂ f' h
    apply hP₂ _ (fun i => i₂ ⁻¹ᵁ U i)
    · simp only [IsOpenCover, ← top_le_iff] at hU ⊢
      rintro x -
      simpa using @hU (i₂ x) trivial
    · rintro i
      refine H _ ((X'.isoOfEq ?_).hom ≫ i₁ ∣_ _) (i₂ ∣_ _) _ ?_
      · exact congr($(h.1.1) ⁻¹ᵁ U i)
      · rw [← (isPullback_morphismRestrict f _).paste_vert_iff]
        · simp only [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
          exact (isPullback_morphismRestrict f' (i₂ ⁻¹ᵁ U i)).paste_vert h
        · rw [← cancel_mono (Scheme.Opens.ι _)]
          simp [morphismRestrict_ι_assoc, h.1.1]

Depends on / 依赖: Category, Category.assoc, IsOpenCover, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.mk, P.universally.of_isPullback, isPullback_morphismRestrict, isoOfEq, of_isPullback, paste_vert_iff, top_le_iff, universally
-/
theorem universally_isZariskiLocalAtTarget (P : MorphismProperty Scheme)
    (hP₂ : forall {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι -> Y.Opens)
      (_ : IsOpenCover U), (forall i, P (f ∣_ U i)) -> P f) : IsZariskiLocalAtTarget P.universally := by
  apply IsZariskiLocalAtTarget.mk'
  · exact fun {X Y} f U => P.universally.of_isPullback
      (isPullback_morphismRestrict f U).flip
  · intro X Y f ι U hU H X' Y' i₁ i₂ f' h
    apply hP₂ _ (fun i => i₂ ⁻¹ᵁ U i)
    · simp only [IsOpenCover, ← top_le_iff] at hU ⊢
      rintro x -
      simpa using @hU (i₂ x) trivial
    · rintro i
      refine H _ ((X'.isoOfEq ?_).hom ≫ i₁ ∣_ _) (i₂ ∣_ _) _ ?_
      · exact congr($(h.1.1) ⁻¹ᵁ U i)
      · rw [← (isPullback_morphismRestrict f _).paste_vert_iff]
        · simp only [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
          exact (isPullback_morphismRestrict f' (i₂ ⁻¹ᵁ U i)).paste_vert h
        · rw [← cancel_mono (Scheme.Opens.ι _)]
          simp [morphismRestrict_ι_assoc, h.1.1]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `universally_isZariskiLocalAtSource` / 引理 `universally_isZariskiLocalAtSource`

English:
lemma universally_isZariskiLocalAtSource
  statement: (P : MorphismProperty Scheme)
  proof: by
  refine .mk_of_iff_of_zeroHypercover ?_
  intro X Y f 𝒰
  refine ⟨fun hf i => ?_, fun hf => ?_⟩
  · apply MorphismProperty.universally_mk'
    intro T g _
    rw [← P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso g f _).hom]; rw [pullbackLeftPullbackSndIso_hom_fst]
    exact IsZariskiLocalAtSource.comp (hf _ _ _ (IsPullback.of_hasPullback ..)) _
  · apply MorphismProperty.universally_mk'
    intro T g _
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (𝒰.pullback₁ <| pullback.snd g f)]
    intro i
    dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f]
    rw [← pullbackLeftPullbackSndIso_hom_fst]; rw [P.cancel_left_of_respectsIso]
    exact hf i _ _ _ (IsPullback.of_hasPullback ..)

中文:
引理 universally_isZariskiLocalAtSource
  结论: (P : MorphismProperty 概形)
  证明: by
  refine .mk_of_iff_of_zeroHypercover ?_
  intro X Y f 𝒰
  refine ⟨fun hf i => ?_, fun hf => ?_⟩
  · apply MorphismProperty.universally_mk'
    intro T g _
    rw [← P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso g f _).hom]; rw [pullbackLeftPullbackSndIso_hom_fst]
    exact IsZariskiLocalAtSource.comp (hf _ _ _ (IsPullback.of_hasPullback ..)) _
  · apply MorphismProperty.universally_mk'
    intro T g _
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (𝒰.pullback₁ <| pullback.snd g f)]
    intro i
    dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f]
    rw [← pullbackLeftPullbackSndIso_hom_fst]; rw [P.cancel_left_of_respectsIso]
    exact hf i _ _ _ (IsPullback.of_hasPullback ..)

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, IsZariskiLocalAtSource, IsZariskiLocalAtSource.comp, IsZariskiLocalAtSource.iff_of_openCover, MorphismProperty, MorphismProperty.universally_mk, P.cancel_left_of_respectsIso, cancel_left_of_respectsIso, iff_of_openCover, mk_of_iff_of_zeroHypercover, of_hasPullback, pullback, pullback.snd, pullbackLeftPullbackSndIso, pullbackLeftPullbackSndIso_hom_fst, universally_mk
-/
lemma universally_isZariskiLocalAtSource (P : MorphismProperty Scheme)
    [IsZariskiLocalAtSource P] : IsZariskiLocalAtSource P.universally := by
  refine .mk_of_iff_of_zeroHypercover ?_
  intro X Y f 𝒰
  refine ⟨fun hf i => ?_, fun hf => ?_⟩
  · apply MorphismProperty.universally_mk'
    intro T g _
    rw [← P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso g f _).hom]; rw [pullbackLeftPullbackSndIso_hom_fst]
    exact IsZariskiLocalAtSource.comp (hf _ _ _ (IsPullback.of_hasPullback ..)) _
  · apply MorphismProperty.universally_mk'
    intro T g _
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (𝒰.pullback₁ <| pullback.snd g f)]
    intro i
    dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f]
    rw [← pullbackLeftPullbackSndIso_hom_fst]; rw [P.cancel_left_of_respectsIso]
    exact hf i _ _ _ (IsPullback.of_hasPullback ..)

end Universally

section Topologically

/--
Definition of `topologically` / `topologically` 的定义

English:
definition topologically
  body: fun _ _ f => P f

中文:
定义 topologically
  定义体: fun _ _ f => P f
-/
def topologically
    (P : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (_ : α -> β), Prop) :
    MorphismProperty Scheme.{u} := fun _ _ f => P f

variable (P : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (_ : α -> β), Prop)

/--
lemma `topologically_isStableUnderComposition` / 引理 `topologically_isStableUnderComposition`

English:
lemma topologically_isStableUnderComposition
  proof: by
    simp only [topologically, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact hP _ _ hf hg

中文:
引理 topologically_isStableUnderComposition
  证明: by
    simp only [topologically, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact hP _ _ hf hg

Depends on / 依赖: Scheme, Scheme.Hom.comp_base, TopCat, TopCat.coe_comp, coe_comp, comp_base, topologically
-/
lemma topologically_isStableUnderComposition
    (hP : forall {α β γ : Type u} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
      (f : α -> β) (g : β -> γ) (_ : P f) (_ : P g), P (g ∘ f)) :
    (topologically P).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    simp only [topologically, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact hP _ _ hf hg

/--
lemma `topologically_iso_le` / 引理 `topologically_iso_le`

English:
lemma topologically_iso_le
  proof: by
  intro X Y e (he : IsIso e)
  exact hP (TopCat.homeoOfIso (asIso e.base))

中文:
引理 topologically_iso_le
  证明: by
  intro X Y e (he : IsIso e)
  exact hP (TopCat.homeoOfIso (asIso e.base))

Depends on / 依赖: TopCat, TopCat.homeoOfIso, e.base, homeoOfIso
-/
lemma topologically_iso_le
    (hP : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ₜ β), P f) :
    MorphismProperty.isomorphisms Scheme <= (topologically P) := by
  intro X Y e (he : IsIso e)
  exact hP (TopCat.homeoOfIso (asIso e.base))

/--
lemma `topologically_respectsIso` / 引理 `topologically_respectsIso`

English:
lemma topologically_respectsIso
  proof: have : (topologically P).IsStableUnderComposition :=
    topologically_isStableUnderComposition P hP₂
  MorphismProperty.respectsIso_of_isStableUnderComposition (topologically_iso_le P hP₁)

中文:
引理 topologically_respectsIso
  证明: have : (topologically P).IsStableUnderComposition :=
    topologically_isStableUnderComposition P hP₂
  MorphismProperty.respectsIso_of_isStableUnderComposition (topologically_iso_le P hP₁)

Depends on / 依赖: IsStableUnderComposition, MorphismProperty, MorphismProperty.respectsIso_of_isStableUnderComposition, respectsIso_of_isStableUnderComposition, topologically, topologically_isStableUnderComposition, topologically_iso_le
-/
lemma topologically_respectsIso
    (hP₁ : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ₜ β), P f)
    (hP₂ : forall {α β γ : Type u} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
      (f : α -> β) (g : β -> γ) (_ : P f) (_ : P g), P (g ∘ f)) :
      (topologically P).RespectsIso :=
  have : (topologically P).IsStableUnderComposition :=
    topologically_isStableUnderComposition P hP₂
  MorphismProperty.respectsIso_of_isStableUnderComposition (topologically_iso_le P hP₁)

/--
lemma `topologically_isZariskiLocalAtTarget` / 引理 `topologically_isZariskiLocalAtTarget`

English:
lemma topologically_isZariskiLocalAtTarget
  statement: [(topologically P).RespectsIso]
  proof: by
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf
    simp_rw [topologically, morphismRestrict_base]
    exact hP₂ f U.carrier f.continuous U.2 hf
  · intro X Y f ι U hU hf
    apply hP₃ f U hU f.continuous fun i => ?_
    rw [← morphismRestrict_base]
    exact hf i

中文:
引理 topologically_isZariskiLocalAtTarget
  结论: [(topologically P).RespectsIso]
  证明: by
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf
    simp_rw [topologically, morphismRestrict_base]
    exact hP₂ f U.carrier f.continuous U.2 hf
  · intro X Y f ι U hU hf
    apply hP₃ f U hU f.continuous fun i => ?_
    rw [← morphismRestrict_base]
    exact hf i

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.mk, U.carrier, carrier, continuous, f.continuous, morphismRestrict_base, simp_rw, topologically
-/
lemma topologically_isZariskiLocalAtTarget [(topologically P).RespectsIso]
    (hP₂ : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α -> β) (s : Set β)
      (_ : Continuous f) (_ : IsOpen s), P f -> P (s.restrictPreimage f))
    (hP₃ : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α -> β) {ι : Type u}
      (U : ι -> Opens β) (_ : IsOpenCover U) (_ : Continuous f),
      (forall i, P ((U i).carrier.restrictPreimage f)) -> P f) :
    IsZariskiLocalAtTarget (topologically P) := by
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf
    simp_rw [topologically, morphismRestrict_base]
    exact hP₂ f U.carrier f.continuous U.2 hf
  · intro X Y f ι U hU hf
    apply hP₃ f U hU f.continuous fun i => ?_
    rw [← morphismRestrict_base]
    exact hf i

/--
lemma `topologically_isZariskiLocalAtTarget'` / 引理 `topologically_isZariskiLocalAtTarget'`

English:
lemma topologically_isZariskiLocalAtTarget'
  statement: [(topologically P).RespectsIso]
  proof: by
  refine topologically_isZariskiLocalAtTarget P ?_ (fun f _ U hU hU' => (hP f U hU hU').mpr)
  introv hf hs H
  refine (hP f (![⊤, Opens.mk s hs] ∘ Equiv.ulift) ?_ hf).mp H ⟨1⟩
  rw [IsOpenCover]; rw [← top_le_iff]
  exact le_iSup (![⊤, Opens.mk s hs] ∘ Equiv.ulift) ⟨0⟩

中文:
引理 topologically_isZariskiLocalAtTarget'
  结论: [(topologically P).RespectsIso]
  证明: by
  refine topologically_isZariskiLocalAtTarget P ?_ (fun f _ U hU hU' => (hP f U hU hU').mpr)
  introv hf hs H
  refine (hP f (![⊤, Opens.mk s hs] ∘ Equiv.ulift) ?_ hf).mp H ⟨1⟩
  rw [IsOpenCover]; rw [← top_le_iff]
  exact le_iSup (![⊤, Opens.mk s hs] ∘ Equiv.ulift) ⟨0⟩

Depends on / 依赖: Equiv.ulift, IsOpenCover, Opens.mk, introv, le_iSup, top_le_iff, topologically_isZariskiLocalAtTarget
-/
lemma topologically_isZariskiLocalAtTarget' [(topologically P).RespectsIso]
    (hP : forall {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α -> β) {ι : Type u}
      (U : ι -> Opens β) (_ : IsOpenCover U) (_ : Continuous f),
      P f ↔ (forall i, P ((U i).carrier.restrictPreimage f))) :
    IsZariskiLocalAtTarget (topologically P) := by
  refine topologically_isZariskiLocalAtTarget P ?_ (fun f _ U hU hU' => (hP f U hU hU').mpr)
  introv hf hs H
  refine (hP f (![⊤, Opens.mk s hs] ∘ Equiv.ulift) ?_ hf).mp H ⟨1⟩
  rw [IsOpenCover]; rw [← top_le_iff]
  exact le_iSup (![⊤, Opens.mk s hs] ∘ Equiv.ulift) ⟨0⟩

/--
lemma `topologically_isZariskiLocalAtSource` / 引理 `topologically_isZariskiLocalAtSource`

English:
lemma topologically_isZariskiLocalAtSource
  statement: [(topologically P).RespectsIso]
  proof: by
  apply IsZariskiLocalAtSource.mk'
  · introv hf
    exact hP₁ f f.continuous _ hf
  · introv hU hf
    exact hP₂ f f.continuous _ hU hf

中文:
引理 topologically_isZariskiLocalAtSource
  结论: [(topologically P).RespectsIso]
  证明: by
  apply IsZariskiLocalAtSource.mk'
  · introv hf
    exact hP₁ f f.continuous _ hf
  · introv hU hf
    exact hP₂ f f.continuous _ hU hf

Depends on / 依赖: IsZariskiLocalAtSource, IsZariskiLocalAtSource.mk, continuous, f.continuous, introv
-/
lemma topologically_isZariskiLocalAtSource [(topologically P).RespectsIso]
    (hP₁ : forall {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X -> Y)
      (_ : Continuous f) (U : Opens X), P f -> P (f ∘ ((↑) : U -> X)))
    (hP₂ : forall {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X -> Y)
      (_ : Continuous f) {ι : Type u} (U : ι -> Opens X),
      IsOpenCover U -> (forall i, P (f ∘ ((↑) : U i -> X))) -> P f) :
    IsZariskiLocalAtSource (topologically P) := by
  apply IsZariskiLocalAtSource.mk'
  · introv hf
    exact hP₁ f f.continuous _ hf
  · introv hU hf
    exact hP₂ f f.continuous _ hU hf

/--
lemma `topologically_isZariskiLocalAtSource'` / 引理 `topologically_isZariskiLocalAtSource'`

English:
lemma topologically_isZariskiLocalAtSource'
  statement: [(topologically P).RespectsIso]
  proof: by
  refine topologically_isZariskiLocalAtSource P ?_ (fun f hf _ U hU hf' => (hP f U hU hf).mpr hf')
  introv hf hs
  refine (hP f (![⊤, U] ∘ Equiv.ulift) ?_ hf).mp hs ⟨1⟩
  rw [IsOpenCover]; rw [← top_le_iff]
  exact le_iSup (![⊤, U] ∘ Equiv.ulift) ⟨0⟩

中文:
引理 topologically_isZariskiLocalAtSource'
  结论: [(topologically P).RespectsIso]
  证明: by
  refine topologically_isZariskiLocalAtSource P ?_ (fun f hf _ U hU hf' => (hP f U hU hf).mpr hf')
  introv hf hs
  refine (hP f (![⊤, U] ∘ Equiv.ulift) ?_ hf).mp hs ⟨1⟩
  rw [IsOpenCover]; rw [← top_le_iff]
  exact le_iSup (![⊤, U] ∘ Equiv.ulift) ⟨0⟩

Depends on / 依赖: Equiv.ulift, IsOpenCover, introv, le_iSup, top_le_iff, topologically_isZariskiLocalAtSource
-/
lemma topologically_isZariskiLocalAtSource' [(topologically P).RespectsIso]
    (hP : forall {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X -> Y) {ι : Type u}
      (U : ι -> Opens X) (_ : IsOpenCover U) (_ : Continuous f),
      P f ↔ (forall i, P (f ∘ ((↑) : U i -> X)))) :
    IsZariskiLocalAtSource (topologically P) := by
  refine topologically_isZariskiLocalAtSource P ?_ (fun f hf _ U hU hf' => (hP f U hU hf).mpr hf')
  introv hf hs
  refine (hP f (![⊤, U] ∘ Equiv.ulift) ?_ hf).mp hs ⟨1⟩
  rw [IsOpenCover]; rw [← top_le_iff]
  exact le_iSup (![⊤, U] ∘ Equiv.ulift) ⟨0⟩

end Topologically

/--
Definition of `stalkwise` / `stalkwise` 的定义

English:
definition stalkwise
  signature: (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop)
  body: fun _ _ f => forall x, P (f.stalkMap x).hom

中文:
定义 stalkwise
  签名: (P : 对任意 {R S : 类型u} [交换环 R] [交换环 S], (R ->+* S) -> 命题)
  定义体: fun _ _ f => forall x, P (f.stalkMap x).hom

Depends on / 依赖: f.stalkMap, stalkMap
-/
def stalkwise (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop) :
    MorphismProperty Scheme.{u} :=
  fun _ _ f => forall x, P (f.stalkMap x).hom

section Stalkwise

variable {P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}

/--
lemma `stalkwise_respectsIso` / 引理 `stalkwise_respectsIso`

English:
lemma stalkwise_respectsIso
  given: (hP : RingHom.RespectsIso P)
  proof: by
    simp only [stalkwise, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    intro x
    rw [Scheme.Hom.stalkMap_comp]
exact (RingHom.RespectsIso.cancel_right_isIso hP _ _).mpr hf (e x)
  postcomp {X Y Z} e (he : IsIso _) f hf := by
    simp only [stalkwise, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    intro x
    rw [Scheme.Hom.stalkMap_comp]
exact (RingHom.RespectsIso.cancel_left_isIso hP _ _).mpr hf x

中文:
引理 stalkwise_respectsIso
  条件: (hP : 环态射.RespectsIso P)
  证明: by
    simp only [stalkwise, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    intro x
    rw [Scheme.Hom.stalkMap_comp]
exact (RingHom.RespectsIso.cancel_right_isIso hP _ _).mpr hf (e x)
  postcomp {X Y Z} e (he : IsIso _) f hf := by
    simp only [stalkwise, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    intro x
    rw [Scheme.Hom.stalkMap_comp]
exact (RingHom.RespectsIso.cancel_left_isIso hP _ _).mpr hf x

Depends on / 依赖: Function, Function.comp_apply, RespectsIso, RingHom, RingHom.RespectsIso.cancel_left_isIso, RingHom.RespectsIso.cancel_right_isIso, Scheme, Scheme.Hom.comp_base, Scheme.Hom.stalkMap_comp, TopCat, TopCat.coe_comp, cancel_left_isIso, cancel_right_isIso, coe_comp, comp_apply, comp_base, postcomp, stalkMap_comp, stalkwise
-/
lemma stalkwise_respectsIso (hP : RingHom.RespectsIso P) :
    (stalkwise P).RespectsIso where
  precomp {X Y Z} e (he : IsIso e) f hf := by
    simp only [stalkwise, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    intro x
    rw [Scheme.Hom.stalkMap_comp]
exact (RingHom.RespectsIso.cancel_right_isIso hP _ _).mpr hf (e x)
  postcomp {X Y Z} e (he : IsIso _) f hf := by
    simp only [stalkwise, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    intro x
    rw [Scheme.Hom.stalkMap_comp]
exact (RingHom.RespectsIso.cancel_left_isIso hP _ _).mpr hf x

/--
lemma `stalkwiseIsZariskiLocalAtTarget_of_respectsIso` / 引理 `stalkwiseIsZariskiLocalAtTarget_of_respectsIso`

English:
lemma stalkwiseIsZariskiLocalAtTarget_of_respectsIso
  given: (hP : RingHom.RespectsIso P)
  proof: by
  have hP' : (RingHom.toMorphismProperty P).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hP
  let := stalkwise_respectsIso hP
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf x
    apply ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f U x).mpr <| hf _
  · intro X Y f ι U hU hf x
    have hy : f x in iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f (U i) ⟨x, hi⟩).mp <| hf i ⟨x, hi⟩

中文:
引理 stalkwiseIsZariskiLocalAtTarget_of_respectsIso
  条件: (hP : 环态射.RespectsIso P)
  证明: by
  have hP' : (RingHom.toMorphismProperty P).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hP
  let := stalkwise_respectsIso hP
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf x
    apply ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f U x).mpr <| hf _
  · intro X Y f ι U hU hf x
    have hy : f x in iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f (U i) ⟨x, hi⟩).mp <| hf i ⟨x, hi⟩

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.mk, Opens.mem_iSup.mp, RespectsIso, RingHom, RingHom.toMorphismProperty, RingHom.toMorphismProperty_respectsIso_iff.mp, arrow_mk_iso_iff, mem_iSup, morphismRestrictStalkMap, stalkwise_respectsIso, toMorphismProperty, toMorphismProperty_respectsIso_iff
-/
lemma stalkwiseIsZariskiLocalAtTarget_of_respectsIso (hP : RingHom.RespectsIso P) :
    IsZariskiLocalAtTarget (stalkwise P) := by
  have hP' : (RingHom.toMorphismProperty P).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hP
  let := stalkwise_respectsIso hP
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf x
    apply ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f U x).mpr <| hf _
  · intro X Y f ι U hU hf x
    have hy : f x in iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f (U i) ⟨x, hi⟩).mp <| hf i ⟨x, hi⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `stalkwise_isZariskiLocalAtSource_of_respectsIso` / 引理 `stalkwise_isZariskiLocalAtSource_of_respectsIso`

English:
lemma stalkwise_isZariskiLocalAtSource_of_respectsIso
  given: (hP : RingHom.RespectsIso P)
  proof: by
  let := stalkwise_respectsIso hP
  apply IsZariskiLocalAtSource.mk'
  · intro X Y f U hf x
    rw [Scheme.Hom.stalkMap_comp]; rw [CommRingCat.hom_comp]; rw [hP.cancel_right_isIso]
    exact hf _
  · intro X Y f ι U hU hf x
    have hy : x in iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    rw [← hP.cancel_right_isIso _ ((U i).ι.stalkMap ⟨x]; rw [hi⟩)]
    simpa [Scheme.Hom.stalkMap_comp] using hf i ⟨x, hi⟩

中文:
引理 stalkwise_isZariskiLocalAtSource_of_respectsIso
  条件: (hP : 环态射.RespectsIso P)
  证明: by
  let := stalkwise_respectsIso hP
  apply IsZariskiLocalAtSource.mk'
  · intro X Y f U hf x
    rw [Scheme.Hom.stalkMap_comp]; rw [CommRingCat.hom_comp]; rw [hP.cancel_right_isIso]
    exact hf _
  · intro X Y f ι U hU hf x
    have hy : x in iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    rw [← hP.cancel_right_isIso _ ((U i).ι.stalkMap ⟨x]; rw [hi⟩)]
    simpa [Scheme.Hom.stalkMap_comp] using hf i ⟨x, hi⟩

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, IsZariskiLocalAtSource, IsZariskiLocalAtSource.mk, Opens.mem_iSup.mp, Scheme, Scheme.Hom.stalkMap_comp, cancel_right_isIso, hP.cancel_right_isIso, hom_comp, mem_iSup, stalkMap, stalkMap_comp, stalkwise_respectsIso
-/
lemma stalkwise_isZariskiLocalAtSource_of_respectsIso (hP : RingHom.RespectsIso P) :
    IsZariskiLocalAtSource (stalkwise P) := by
  let := stalkwise_respectsIso hP
  apply IsZariskiLocalAtSource.mk'
  · intro X Y f U hf x
    rw [Scheme.Hom.stalkMap_comp]; rw [CommRingCat.hom_comp]; rw [hP.cancel_right_isIso]
    exact hf _
  · intro X Y f ι U hU hf x
    have hy : x in iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    rw [← hP.cancel_right_isIso _ ((U i).ι.stalkMap ⟨x]; rw [hi⟩)]
    simpa [Scheme.Hom.stalkMap_comp] using hf i ⟨x, hi⟩

/--
lemma `stalkwise_SpecMap_iff` / 引理 `stalkwise_SpecMap_iff`

English:
lemma stalkwise_SpecMap_iff
  given: (hP : RingHom.RespectsIso P) {R S : CommRingCat} (φ : R ⟶ S)
  proof: by
  have hP' : (RingHom.toMorphismProperty P).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hP
  trans forall (p : PrimeSpectrum S), P (Localization.localRingHom _ p.asIdeal φ.hom rfl)
  · exact forall_congr' fun p =>
      (RingHom.toMorphismProperty P).arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso _ _)
  · exact ⟨fun H p hp => H ⟨p, hp⟩, fun H p => H p.1 p.2⟩

中文:
引理 stalkwise_SpecMap_iff
  条件: (hP : 环态射.RespectsIso P) {R S : 交换环范畴} (φ : R ⟶ S)
  证明: by
  have hP' : (RingHom.toMorphismProperty P).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hP
  trans forall (p : PrimeSpectrum S), P (Localization.localRingHom _ p.asIdeal φ.hom rfl)
  · exact forall_congr' fun p =>
      (RingHom.toMorphismProperty P).arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso _ _)
  · exact ⟨fun H p hp => H ⟨p, hp⟩, fun H p => H p.1 p.2⟩

Depends on / 依赖: Localization, Localization.localRingHom, PrimeSpectrum, RespectsIso, RingHom, RingHom.toMorphismProperty, RingHom.toMorphismProperty_respectsIso_iff.mp, Scheme, Scheme.arrowStalkMapSpecIso, arrowStalkMapSpecIso, arrow_mk_iso_iff, asIdeal, forall_congr, localRingHom, p.asIdeal, toMorphismProperty, toMorphismProperty_respectsIso_iff
-/
lemma stalkwise_SpecMap_iff (hP : RingHom.RespectsIso P) {R S : CommRingCat} (φ : R ⟶ S) :
    stalkwise P (Spec.map φ) ↔ forall (p : Ideal S) (_ : p.IsPrime),
      P (Localization.localRingHom _ p φ.hom rfl) := by
  have hP' : (RingHom.toMorphismProperty P).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hP
  trans forall (p : PrimeSpectrum S), P (Localization.localRingHom _ p.asIdeal φ.hom rfl)
  · exact forall_congr' fun p =>
      (RingHom.toMorphismProperty P).arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso _ _)
  · exact ⟨fun H p hp => H ⟨p, hp⟩, fun H p => H p.1 p.2⟩

end Stalkwise

namespace AffineTargetMorphismProperty

/--
lemma `isStableUnderBaseChange_of_isStableUnderBaseChangeOnAffine_of_isZariskiLocalAtTarget` / 引理 `isStableUnderBaseChange_of_isStableUnderBaseChangeOnAffine_of_isZariskiLocalAtTarget`

English:
lemma isStableUnderBaseChange_of_isStableUnderBaseChangeOnAffine_of_isZariskiLocalAtTarget
  proof: letI := HasAffineProperty.of_isZariskiLocalAtTarget P
  HasAffineProperty.isStableUnderBaseChange hP₂

中文:
引理 isStableUnderBaseChange_of_isStableUnderBaseChangeOnAffine_of_isZariskiLocalAtTarget
  证明: letI := HasAffineProperty.of_isZariskiLocalAtTarget P
  HasAffineProperty.isStableUnderBaseChange hP₂

Depends on / 依赖: HasAffineProperty, HasAffineProperty.isStableUnderBaseChange, HasAffineProperty.of_isZariskiLocalAtTarget, isStableUnderBaseChange, of_isZariskiLocalAtTarget
-/
lemma isStableUnderBaseChange_of_isStableUnderBaseChangeOnAffine_of_isZariskiLocalAtTarget
    (P : MorphismProperty Scheme) [IsZariskiLocalAtTarget P]
    (hP₂ : (of P).IsStableUnderBaseChange) :
    P.IsStableUnderBaseChange :=
  letI := HasAffineProperty.of_isZariskiLocalAtTarget P
  HasAffineProperty.isStableUnderBaseChange hP₂

end AffineTargetMorphismProperty

end AlgebraicGeometry
