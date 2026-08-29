/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.RingTheory.RingHom.Integral

/-!

# Integral morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is integral if the preimage
of an arbitrary affine open subset of `Y` is affine and the induced ring map is integral.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine
and the induced ring map is integral.

-/

public section

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is integral if the preimage of any affine open subset of `Y` is
affine and the induced ring hom on sections is integral. -/
@[mk_iff]
/--
Definition of `IsIntegralHom` / `IsIntegralHom` 的定义

English:
class IsIntegralHom
  parameters: {X Y : Scheme} (f : X ⟶ Y)
  extends: IsAffineHom f
  axioms and operations (1):
    - isIntegral_app((f) (U : Y.Opens) (hU : IsAffineOpen U)) : (f.app U).hom.IsIntegral

中文:
类 是整态射
  参数: {X Y : 概形} (f : X ⟶ Y)
  继承: 是仿射态射 f
  公理与运算 (1 个):
    - isIntegral_app((f) (U : Y.Opens) (hU : 是仿射开集 U)) : (f.app U).hom.是整

Depends on / 依赖: IsIntegralHom, IsIntegralHom.isIntegral_app, isIntegral_app
-/
class IsIntegralHom {X Y : Scheme} (f : X ⟶ Y) : Prop extends IsAffineHom f where
  isIntegral_app (f) (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral

alias Scheme.Hom.isIntegral_app := IsIntegralHom.isIntegral_app

namespace IsIntegralHom

variable {X Y Z S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `hasAffineProperty` / 实例 `hasAffineProperty`

English:
instance hasAffineProperty
  signature: : HasAffineProperty @IsIntegralHom
  body: by
  change HasAffineProperty @IsIntegralHom (affineAnd RingHom.IsIntegral)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.isIntegral_respectsIso
    RingHom.isIntegral_isStableUnderBaseChange.localizationPreserves.away
    RingHom.isIntegral_ofLocalizationSpan]
  simp [isIntegralHom_iff]

中文:
实例 hasAffineProperty
  签名: : 有AffineProperty @是整态射
  定义体: by
  change HasAffineProperty @IsIntegralHom (affineAnd RingHom.IsIntegral)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.isIntegral_respectsIso
    RingHom.isIntegral_isStableUnderBaseChange.localizationPreserves.away
    RingHom.isIntegral_ofLocalizationSpan]
  simp [isIntegralHom_iff]

Depends on / 依赖: HasAffineProperty, HasAffineProperty.affineAnd_iff, IsIntegral, IsIntegralHom, RingHom, RingHom.IsIntegral, RingHom.isIntegral_isStableUnderBaseChange.localizationPreserves.away, RingHom.isIntegral_ofLocalizationSpan, RingHom.isIntegral_respectsIso, affineAnd, affineAnd_iff, isIntegralHom_iff, isIntegral_isStableUnderBaseChange, isIntegral_ofLocalizationSpan, isIntegral_respectsIso, localizationPreserves
-/
instance hasAffineProperty : HasAffineProperty @IsIntegralHom
    fun X _ f _ => IsAffine X ∧ RingHom.IsIntegral (f.app ⊤).hom := by
  change HasAffineProperty @IsIntegralHom (affineAnd RingHom.IsIntegral)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.isIntegral_respectsIso
    RingHom.isIntegral_isStableUnderBaseChange.localizationPreserves.away
    RingHom.isIntegral_ofLocalizationSpan]
  simp [isIntegralHom_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderComposition @IsIntegralHom
  body: HasAffineProperty.affineAnd_isStableUnderComposition (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_stableUnderComposition

中文:
实例 :
  签名: 是StableUnderComposition @是整态射
  定义体: HasAffineProperty.affineAnd_isStableUnderComposition (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_stableUnderComposition

Depends on / 依赖: HasAffineProperty, HasAffineProperty.affineAnd_isStableUnderComposition, IsIntegral, RingHom, RingHom.IsIntegral, RingHom.isIntegral_stableUnderComposition, affineAnd_isStableUnderComposition, hasAffineProperty, isIntegral_stableUnderComposition
-/
instance : IsStableUnderComposition @IsIntegralHom :=
  HasAffineProperty.affineAnd_isStableUnderComposition (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_stableUnderComposition

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderBaseChange @IsIntegralHom
  body: HasAffineProperty.affineAnd_isStableUnderBaseChange (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_respectsIso RingHom.isIntegral_isStableUnderBaseChange

中文:
实例 :
  签名: 是StableUnderBaseChange @是整态射
  定义体: HasAffineProperty.affineAnd_isStableUnderBaseChange (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_respectsIso RingHom.isIntegral_isStableUnderBaseChange

Depends on / 依赖: HasAffineProperty, HasAffineProperty.affineAnd_isStableUnderBaseChange, IsIntegral, RingHom, RingHom.IsIntegral, RingHom.isIntegral_isStableUnderBaseChange, RingHom.isIntegral_respectsIso, affineAnd_isStableUnderBaseChange, hasAffineProperty, isIntegral_isStableUnderBaseChange, isIntegral_respectsIso
-/
instance : IsStableUnderBaseChange @IsIntegralHom :=
  HasAffineProperty.affineAnd_isStableUnderBaseChange (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_respectsIso RingHom.isIntegral_isStableUnderBaseChange

instance (priority := low) (f : X ⟶ Y) [IsClosedImmersion f] : IsIntegralHom f where
  isIntegral_app U hU := (RingHom.Finite.of_surjective _ (f.app_surjective U hU)).to_isIntegral

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMultiplicative @IsIntegralHom
  body: inferInstance

中文:
实例 :
  签名: 是Multiplicative @是整态射
  定义体: inferInstance
-/
instance : IsMultiplicative @IsIntegralHom where
  id_mem _ := inferInstance

instance (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom f] [IsIntegralHom g] : IsIntegralHom (f ≫ g) :=
  MorphismProperty.comp_mem _ _ _ ‹_› ‹_›

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ S) (g : Y ⟶ S) [IsIntegralHom g] : IsIntegralHom (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ S) (g : Y ⟶ S) [IsIntegralHom f] : IsIntegralHom (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (V : Y.Opens) [IsIntegralHom f] : IsIntegralHom (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @IsIntegralHom @IsSeparated
  body: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsIntegralHom _)

中文:
实例 :
  签名: MorphismProperty.有OfPostcompProperty @是整态射 @是分离
  定义体: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsIntegralHom _)

Depends on / 依赖: IsIntegralHom, MorphismProperty, MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr, hasOfPostcompProperty_iff_le_diagonal
-/
instance : MorphismProperty.HasOfPostcompProperty @IsIntegralHom @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsIntegralHom _)

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  given: (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom (f ≫ g)] [IsSeparated g]
  proof: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

中文:
引理 of_comp
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) [是整态射 (f ≫ g)] [是分离 g]
  证明: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

Depends on / 依赖: MorphismProperty, MorphismProperty.of_postcomp, of_postcomp
-/
lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom (f ≫ g)] [IsSeparated g] :
    IsIntegralHom f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

/--
lemma `comp_iff` / 引理 `comp_iff`

English:
lemma comp_iff
  given: {f : X ⟶ Y} {g : Y ⟶ Z} [IsIntegralHom g]
  proof: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

中文:
引理 comp_iff
  条件: {f : X ⟶ Y} {g : Y ⟶ Z} [是整态射 g]
  证明: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

Depends on / 依赖: of_comp
-/
lemma comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} [IsIntegralHom g] :
    IsIntegralHom (f ≫ g) ↔ IsIntegralHom f :=
  ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `SpecMap_iff` / 引理 `SpecMap_iff`

English:
lemma SpecMap_iff
  given: {R S : CommRingCat} {φ : R ⟶ S}
  proof: by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  rw [HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)]; rw [and_iff_right]
  exacts [MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.IsIntegral)
    (arrowIsoΓSpecOfIsAffine φ).symm, inferInstance]

中文:
引理 SpecMap_iff
  条件: {R S : 交换环范畴} {φ : R ⟶ S}
  证明: by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  rw [HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)]; rw [and_iff_right]
  exacts [MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.IsIntegral)
    (arrowIsoΓSpecOfIsAffine φ).symm, inferInstance]

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, IsIntegral, IsIntegralHom, MorphismProperty, MorphismProperty.arrow_mk_iso_iff, RingHom, RingHom.IsIntegral, RingHom.isIntegral_respectsIso, RingHom.toMorphismProperty, RingHom.toMorphismProperty_respectsIso_iff.mp, and_iff_right, arrow_mk_iso_iff, exacts, iff_of_isAffine, isIntegral_respectsIso, toMorphismProperty, toMorphismProperty_respectsIso_iff
-/
lemma SpecMap_iff {R S : CommRingCat} {φ : R ⟶ S} :
    IsIntegralHom (Spec.map φ) ↔ φ.hom.IsIntegral := by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  rw [HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom)]; rw [and_iff_right]
  exacts [MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.IsIntegral)
    (arrowIsoΓSpecOfIsAffine φ).symm, inferInstance]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMultiplicative @IsIntegralHom

中文:
实例 :
  签名: 是Multiplicative @是整态射
-/
instance : IsMultiplicative @IsIntegralHom where

instance {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) [IsIntegralHom f] [IsIntegralHom g] :
    IsIntegralHom (Limits.coprod.desc f g) := by
  refine hasAffineProperty.coprodDesc_affineAnd RingHom.isIntegral_respectsIso ?_ _ _ ‹_› ‹_›
  intros R S T _ _ _ f g _ _
  algebraize [f, g]
  refine algebraMap_isIntegral_iff.mpr inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (priority := 100) (f : X ⟶ Y) [IsIntegralHom f] :
    UniversallyClosed f := by
  revert X Y f ‹IsIntegralHom f›
  rw [universallyClosed_eq]; rw [← IsStableUnderBaseChange.universally_eq (P := @IsIntegralHom)]
  apply universally_mono
  intro X Y f
  wlog hY : exists R, Y = Spec R generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := topologically _) Y.affineCover]
    exact fun a i => this _ ⟨_, rfl⟩ (a i)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S generalizing X
  · intro H
    have inst : IsAffine X := isAffine_of_isAffineHom f
    rw [← cancel_left_of_respectsIso (P := topologically _) X.isoSpec.inv]
    rw [← cancel_left_of_respectsIso (P := @IsIntegralHom) X.isoSpec.inv] at H
    exact this _ ⟨_, rfl⟩ H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [SpecMap_iff]
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `iff_universallyClosed_and_isAffineHom` / 引理 `iff_universallyClosed_and_isAffineHom`

English:
lemma iff_universallyClosed_and_isAffineHom
  given: {X Y : Scheme.{u}} {f : X ⟶ Y}
  proof: by
  refine ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨H₁, H₂⟩ => ?_⟩
  clear * -
  wlog hY : exists R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover]
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) Y.affineCover] at H₁
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsAffineHom) Y.affineCover] at H₂
    exact fun _ => this inferInstance inferInstance ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S
  · have inst : IsAffine X := isAffine_of_isAffineHom f
    rw [← cancel_left_of_respectsIso (P := @IsIntegralHom) X.isoSpec.inv]
    exact this _ inferInstance inferInstance ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ : exists φ, Spec.map φ = f := ⟨_, Spec.map_preimage _⟩
  rw [SpecMap_iff]
  apply PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom
  algebraize [φ.1, Polynomial.mapRingHom φ.1]
  exact H₁.universally_isClosedMap (Spec.map (CommRingCat.ofHom Polynomial.C))
    (Spec.map (CommRingCat.ofHom Polynomial.C)) (Spec.map _)
    (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S (Polynomial R) (Polynomial S))).flip

中文:
引理 iff_universallyClosed_and_isAffineHom
  条件: {X Y : 概形.{u}} {f : X ⟶ Y}
  证明: by
  refine ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨H₁, H₂⟩ => ?_⟩
  clear * -
  wlog hY : exists R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover]
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) Y.affineCover] at H₁
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsAffineHom) Y.affineCover] at H₂
    exact fun _ => this inferInstance inferInstance ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S
  · have inst : IsAffine X := isAffine_of_isAffineHom f
    rw [← cancel_left_of_respectsIso (P := @IsIntegralHom) X.isoSpec.inv]
    exact this _ inferInstance inferInstance ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ : exists φ, Spec.map φ = f := ⟨_, Spec.map_preimage _⟩
  rw [SpecMap_iff]
  apply PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom
  algebraize [φ.1, Polynomial.mapRingHom φ.1]
  exact H₁.universally_isClosedMap (Spec.map (CommRingCat.ofHom Polynomial.C))
    (Spec.map (CommRingCat.ofHom Polynomial.C)) (Spec.map _)
    (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S (Polynomial R) (Polynomial S))).flip

Depends on / 依赖: IsAffineHom, IsIntegralHom, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_openCover, UniversallyClosed, Y.affineCover, affineCover, iff_of_openCover
-/
lemma iff_universallyClosed_and_isAffineHom {X Y : Scheme.{u}} {f : X ⟶ Y} :
    IsIntegralHom f ↔ UniversallyClosed f ∧ IsAffineHom f := by
  refine ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨H₁, H₂⟩ => ?_⟩
  clear * -
  wlog hY : exists R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover]
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) Y.affineCover] at H₁
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsAffineHom) Y.affineCover] at H₂
    exact fun _ => this inferInstance inferInstance ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S
  · have inst : IsAffine X := isAffine_of_isAffineHom f
    rw [← cancel_left_of_respectsIso (P := @IsIntegralHom) X.isoSpec.inv]
    exact this _ inferInstance inferInstance ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ : exists φ, Spec.map φ = f := ⟨_, Spec.map_preimage _⟩
  rw [SpecMap_iff]
  apply PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom
  algebraize [φ.1, Polynomial.mapRingHom φ.1]
  exact H₁.universally_isClosedMap (Spec.map (CommRingCat.ofHom Polynomial.C))
    (Spec.map (CommRingCat.ofHom Polynomial.C)) (Spec.map _)
    (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S (Polynomial R) (Polynomial S))).flip

/--
lemma `eq_universallyClosed_inf_isAffineHom` / 引理 `eq_universallyClosed_inf_isAffineHom`

English:
lemma eq_universallyClosed_inf_isAffineHom
  proof: by
  ext
  exact iff_universallyClosed_and_isAffineHom

中文:
引理 eq_universallyClosed_inf_isAffineHom
  证明: by
  ext
  exact iff_universallyClosed_and_isAffineHom

Depends on / 依赖: iff_universallyClosed_and_isAffineHom
-/
lemma eq_universallyClosed_inf_isAffineHom :
    @IsIntegralHom = (@UniversallyClosed ⊓ @IsAffineHom : MorphismProperty Scheme) := by
  ext
  exact iff_universallyClosed_and_isAffineHom

end IsIntegralHom

end AlgebraicGeometry
