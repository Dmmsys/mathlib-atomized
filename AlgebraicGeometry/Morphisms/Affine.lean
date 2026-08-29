/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!

# Affine morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is affine if the preimage
of an arbitrary affine open subset of `Y` is affine.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine.

## Main results

- `AlgebraicGeometry.IsAffineHom`: The class of affine morphisms.
- `AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen`:
  If `s` is a spanning set of `Γ(X, U)`, such that each `X.basicOpen i` is affine,
  then `U` is also affine.
- `AlgebraicGeometry.isAffineHom_isStableUnderBaseChange`:
  Affine morphisms are stable under base change.

We also provide the instance `HasAffineProperty @IsAffineHom fun X _ _ _ ↦ IsAffine X`.

-/

public section

universe v u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes `X ⟶ Y` is affine if
the preimage of any affine open subset of `Y` is affine. -/
@[mk_iff]
/--
Definition of `IsAffineHom` / `IsAffineHom` 的定义

English:
class IsAffineHom
  parameters: {X Y : Scheme} (f : X ⟶ Y)
  axioms and operations (1):
    - isAffine_preimage : forall U : Y.Opens, IsAffineOpen U -> IsAffineOpen (f ⁻¹ᵁ U)

中文:
类 是仿射态射
  参数: {X Y : 概形} (f : X ⟶ Y)
  公理与运算 (1 个):
    - isAffine_preimage : 对任意 U : Y.Opens, 是仿射开集 U -> 是仿射开集 (f ⁻¹ᵁ U)
-/
class IsAffineHom {X Y : Scheme} (f : X ⟶ Y) : Prop where
  isAffine_preimage : forall U : Y.Opens, IsAffineOpen U -> IsAffineOpen (f ⁻¹ᵁ U)

/--
lemma `IsAffineOpen.preimage` / 引理 `IsAffineOpen.preimage`

English:
lemma IsAffineOpen.preimage
  statement: {X Y : Scheme} {U : Y.Opens} (hU : IsAffineOpen U)
  proof: IsAffineHom.isAffine_preimage _ hU

中文:
引理 是仿射开集.原像
  结论: {X Y : 概形} {U : Y.Opens} (hU : 是仿射开集 U)
  证明: IsAffineHom.isAffine_preimage _ hU

Depends on / 依赖: IsAffineHom, IsAffineHom.isAffine_preimage, isAffine_preimage
-/
lemma IsAffineOpen.preimage {X Y : Scheme} {U : Y.Opens} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsAffineHom f] :
    IsAffineOpen (f ⁻¹ᵁ U) :=
  IsAffineHom.isAffine_preimage _ hU

instance (priority := 900) [IsIso f] : IsAffineHom f :=
  ⟨fun _ hU => hU.preimage_of_isIso f⟩

instance (priority := 900) [IsAffineHom f] : QuasiCompact f :=
  quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU => (hU.preimage f).isCompact

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsAffineHom
  signature: f] [IsAffineHom g] : IsAffineHom (f ≫ g)
  body: by
  constructor
  intro U hU
  rw [Scheme.Hom.comp_base]; rw [Opens.map_comp_obj]
  apply IsAffineHom.isAffine_preimage
  apply IsAffineHom.isAffine_preimage
  exact hU

中文:
实例 [是仿射态射
  签名: f] [是仿射态射 g] : 是仿射态射 (f ≫ g)
  定义体: by
  constructor
  intro U hU
  rw [Scheme.Hom.comp_base]; rw [Opens.map_comp_obj]
  apply IsAffineHom.isAffine_preimage
  apply IsAffineHom.isAffine_preimage
  exact hU

Depends on / 依赖: IsAffineHom, IsAffineHom.isAffine_preimage, Opens.map_comp_obj, Scheme, Scheme.Hom.comp_base, comp_base, isAffine_preimage, map_comp_obj
-/
instance [IsAffineHom f] [IsAffineHom g] : IsAffineHom (f ≫ g) := by
  constructor
  intro U hU
  rw [Scheme.Hom.comp_base]; rw [Opens.map_comp_obj]
  apply IsAffineHom.isAffine_preimage
  apply IsAffineHom.isAffine_preimage
  exact hU

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @IsAffineHom
  body: inferInstance
  comp_mem _ _ _ _ := inferInstance

中文:
实例 :
  签名: MorphismProperty.是Multiplicative @是仿射态射
  定义体: inferInstance
  comp_mem _ _ _ _ := inferInstance
-/
instance : MorphismProperty.IsMultiplicative @IsAffineHom where
  id_mem := inferInstance
  comp_mem _ _ _ _ := inferInstance

instance {X : Scheme} (r : Γ(X, ⊤)) :
    IsAffineHom (X.basicOpen r).ι := by
  constructor
  intro U hU
  fapply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (X.basicOpen r).ι).mp
  convert! hU.basicOpen (X.presheaf.map (homOfLE le_top).op r)
  rw [X.basicOpen_res]
  ext1
  refine Set.image_preimage_eq_inter_range.trans ?_
  simp

/--
lemma `isRetrocompact_basicOpen` / 引理 `isRetrocompact_basicOpen`

English:
lemma isRetrocompact_basicOpen
  given: (s : Γ(X, ⊤))
  statement: IsRetrocompact (X := X) (X.basicOpen s)
  proof: IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr (X.basicOpen s).ι.isSpectralMap

中文:
引理 isRetrocompact_basicOpen
  条件: (s : Γ(X, ⊤))
  结论: IsRetrocompact (X := X) (X.basicOpen s)
  证明: IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr (X.basicOpen s).ι.isSpectralMap

Depends on / 依赖: X.basicOpen, basicOpen
-/
lemma isRetrocompact_basicOpen (s : Γ(X, ⊤)) : IsRetrocompact (X := X) (X.basicOpen s) :=
  IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr (X.basicOpen s).ι.isSpectralMap

/--
lemma `isAffine_of_isAffineOpen_basicOpen_aux` / 引理 `isAffine_of_isAffineOpen_basicOpen_aux`

English:
lemma isAffine_of_isAffineOpen_basicOpen_aux
  statement: (s : Set Γ(X, ⊤))
  proof: by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
  rw [← Set.inter_univ (_ inter _)]; rw [← Opens.coe_top]; rw [← iSup_basicOpen_of_span_eq_top _ _ e]; rw [← iSup_subtype'']; rw [Opens.coe_iSup]; rw [Set.inter_iUnion]
  

中文:
引理 isAffine_of_isAffineOpen_basicOpen_aux
  结论: (s : 集合 Γ(X, ⊤))
  证明: by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
  rw [← Set.inter_univ (_ inter _)]; rw [← Opens.coe_top]; rw [← iSup_basicOpen_of_span_eq_top _ _ e]; rw [← iSup_subtype'']; rw [Opens.coe_iSup]; rw [Set.inter_iUnion]
  
-/
private lemma isAffine_of_isAffineOpen_basicOpen_aux (s : Set Γ(X, ⊤))
    (hs : Ideal.span s = ⊤) (hs₂ : forall i in s, IsAffineOpen (X.basicOpen i)) :
    QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
  rw [← Set.inter_univ (_ inter _)]; rw [← Opens.coe_top]; rw [← iSup_basicOpen_of_span_eq_top _ _ e]; rw [← iSup_subtype'']; rw [Opens.coe_iSup]; rw [Set.inter_iUnion]
  apply isCompact_iUnion
  intro i
  rw [Set.inter_inter_distrib_right]
  refine (hs₂ i (hs' i.2)).isQuasiSeparated _ _ Set.inter_subset_right
    (U.1.2.inter (X.basicOpen _).2) ?_ Set.inter_subset_right (V.1.2.inter (X.basicOpen _).2) ?_
  · rw [← Opens.coe_inf, ← X.basicOpen_res _ (homOfLE le_top).op]
    exact (U.2.basicOpen _).isCompact
  · rw [← Opens.coe_inf, ← X.basicOpen_res _ (homOfLE le_top).op]
    exact (V.2.basicOpen _).isCompact

set_option backward.isDefEq.respectTransparency false in
@[stacks 01QF]
/--
lemma `isAffine_of_isAffineOpen_basicOpen` / 引理 `isAffine_of_isAffineOpen_basicOpen`

English:
lemma isAffine_of_isAffineOpen_basicOpen
  statement: (s : Set Γ(X, ⊤))
  proof: by
  have : QuasiSeparatedSpace X := isAffine_of_isAffineOpen_basicOpen_aux s hs hs₂
  have : CompactSpace X := by
    obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
    rw [← isCompact_univ_iff]; rw [← Opens.coe_top]; rw [← iSup_basicOpen_of_span_eq_top _ _ e]
    simp only [Finset.m

中文:
引理 isAffine_of_isAffineOpen_basicOpen
  结论: (s : 集合 Γ(X, ⊤))
  证明: by
  have : QuasiSeparatedSpace X := isAffine_of_isAffineOpen_basicOpen_aux s hs hs₂
  have : CompactSpace X := by
    obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
    rw [← isCompact_univ_iff]; rw [← Opens.coe_top]; rw [← iSup_basicOpen_of_span_eq_top _ _ e]
    simp only [Finset.m

Depends on / 依赖: CompactSpace, Finset, Finset.mem_coe, HasAffineProperty, HasAffineProperty.of_iSup_eq_top, Ideal.span_eq_top_iff_finite, MorphismProperty, MorphismProperty.isomorphis, Opens.carrier_eq_coe, Opens.coe_mk, Opens.coe_top, Opens.iSup_mk, QuasiSeparatedSpace, carrier_eq_coe, coe_mk, coe_top, iSup_basicOpen_of_span_eq_top, iSup_mk, isAffine_of_isAffineOpen_basicOpen_aux, isCompact
-/
lemma isAffine_of_isAffineOpen_basicOpen (s : Set Γ(X, ⊤))
    (hs : Ideal.span s = ⊤) (hs₂ : forall i in s, IsAffineOpen (X.basicOpen i)) :
    IsAffine X := by
  have : QuasiSeparatedSpace X := isAffine_of_isAffineOpen_basicOpen_aux s hs hs₂
  have : CompactSpace X := by
    obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
    rw [← isCompact_univ_iff]; rw [← Opens.coe_top]; rw [← iSup_basicOpen_of_span_eq_top _ _ e]
    simp only [Finset.mem_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk]
    apply s'.isCompact_biUnion
    exact fun i hi => (hs₂ _ (hs' hi)).isCompact
  constructor
  refine HasAffineProperty.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun i : s => ⟨PrimeSpectrum.basicOpen i.1, ?_⟩) ?_ (fun i => ⟨?_, ?_⟩)
  · change IsAffineOpen _
    simp only [← basicOpen_eq_of_affine]
    exact (isAffineOpen_top (Scheme.Spec.obj (op _))).basicOpen _
  · rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Subtype.range_coe_subtype, Set.ofPred_mem_eq, hs]
  · rw [Scheme.toSpecΓ_preimage_basicOpen]
    exact hs₂ _ i.2
  · simp only [Opens.map_top, morphismRestrict_app]
    refine IsIso.comp_isIso' ?_ inferInstance
    convert! isIso_ΓSpec_adjunction_unit_app_basicOpen i.1 using 0
    exact congr(IsIso ((ΓSpec.adjunction.unit.app X).app $(by simp)))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isAffineOpen_of_isAffineOpen_basicOpen` / 引理 `isAffineOpen_of_isAffineOpen_basicOpen`

English:
lemma isAffineOpen_of_isAffineOpen_basicOpen
  statement: (U) (s : Set Γ(X, U))
  proof: by
  apply isAffine_of_isAffineOpen_basicOpen (U.topIso.inv '' s)
  · rw [← Ideal.map_span U.topIso.inv.hom, hs, Ideal.map_top]
  · rintro _ ⟨j, hj, rfl⟩
    rw [← (Scheme.Opens.ι _).isAffineOpen_iff_of_isOpenImmersion]; rw [Scheme.image_basicOpen]
    simpa [Scheme.Opens.toScheme_presheaf_obj] usin

中文:
引理 isAffineOpen_of_isAffineOpen_basicOpen
  结论: (U) (s : 集合 Γ(X, U))
  证明: by
  apply isAffine_of_isAffineOpen_basicOpen (U.topIso.inv '' s)
  · rw [← Ideal.map_span U.topIso.inv.hom, hs, Ideal.map_top]
  · rintro _ ⟨j, hj, rfl⟩
    rw [← (Scheme.Opens.ι _).isAffineOpen_iff_of_isOpenImmersion]; rw [Scheme.image_basicOpen]
    simpa [Scheme.Opens.toScheme_presheaf_obj] usin

Depends on / 依赖: Ideal.map_span, Ideal.map_top, Scheme, Scheme.Opens, Scheme.Opens.toScheme_presheaf_obj, Scheme.image_basicOpen, U.topIso.inv, U.topIso.inv.hom, image_basicOpen, isAffineOpen_iff_of_isOpenImmersion, isAffine_of_isAffineOpen_basicOpen, map_span, map_top, toScheme_presheaf_obj, topIso
-/
lemma isAffineOpen_of_isAffineOpen_basicOpen (U) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤) (hs₂ : forall i in s, IsAffineOpen (X.basicOpen i)) :
    IsAffineOpen U := by
  apply isAffine_of_isAffineOpen_basicOpen (U.topIso.inv '' s)
  · rw [← Ideal.map_span U.topIso.inv.hom, hs, Ideal.map_top]
  · rintro _ ⟨j, hj, rfl⟩
    rw [← (Scheme.Opens.ι _).isAffineOpen_iff_of_isOpenImmersion]; rw [Scheme.image_basicOpen]
    simpa [Scheme.Opens.toScheme_presheaf_obj] using hs₂ j hj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasAffineProperty @IsAffineHom fun X _ _ _ => IsAffine X
  body: by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk
      · rintro X Y Z e _ _ H
        have : IsAffine _ := H
        exact .of_isIso e.hom
      · exact fun _ _ _ => id
    · intro X Y _ f r H
      have : IsAffine X := H
      change IsAffineOpen _
      rw [Scheme.preimag

中文:
实例 :
  签名: 有AffineProperty @是仿射态射 fun X _ _ _ => 是仿射 X
  定义体: by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk
      · rintro X Y Z e _ _ H
        have : IsAffine _ := H
        exact .of_isIso e.hom
      · exact fun _ _ _ => id
    · intro X Y _ f r H
      have : IsAffine X := H
      change IsAffineOpen _
      rw [Scheme.preimag

Depends on / 依赖: AffineTargetMorphismProperty, AffineTargetMorphismProperty.respectsIso_mk, Ideal.map, Ideal.map_span, Ideal.map_top, IsAffine, IsAffineOpen, Scheme, Scheme.preimage_basicOpen, Y.basic, appTop, apply_fun, basicOpen, e.hom, f.appTop, isAffineOpen_top, isAffine_of_isAffineOpen_basicOpen, map_span, map_top, of_isIso
-/
instance : HasAffineProperty @IsAffineHom fun X _ _ _ => IsAffine X where
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk
      · rintro X Y Z e _ _ H
        have : IsAffine _ := H
        exact .of_isIso e.hom
      · exact fun _ _ _ => id
    · intro X Y _ f r H
      have : IsAffine X := H
      change IsAffineOpen _
      rw [Scheme.preimage_basicOpen]
      exact (isAffineOpen_top X).basicOpen _
    · intro X Y _ f S hS hS'
      apply_fun Ideal.map (f.appTop).hom at hS
      rw [Ideal.map_span]; rw [Ideal.map_top] at hS
      apply isAffine_of_isAffineOpen_basicOpen _ hS
      have : forall i : S, IsAffineOpen (f ⁻¹ᵁ Y.basicOpen i.1) := hS'
      simpa [Scheme.preimage_basicOpen] using! this
  eq_targetAffineLocally' := by
    ext X Y f
    simp only [targetAffineLocally, Scheme.affineOpens, Set.coe_ofPred, Set.mem_ofPred_eq,
      Subtype.forall, isAffineHom_iff]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isAffineHom_isStableUnderBaseChange` / 实例 `isAffineHom_isStableUnderBaseChange`

English:
instance isAffineHom_isStableUnderBaseChange
  signature: :
  body: by
  apply HasAffineProperty.isStableUnderBaseChange
  let := HasAffineProperty.isLocal_affineProperty
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  introv X hX H
  infer_instance

中文:
实例 isAffineHom_isStableUnderBaseChange
  签名: :
  定义体: by
  apply HasAffineProperty.isStableUnderBaseChange
  let := HasAffineProperty.isLocal_affineProperty
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  introv X hX H
  infer_instance

Depends on / 依赖: AffineTargetMorphismProperty, AffineTargetMorphismProperty.IsStableUnderBaseChange.mk, HasAffineProperty, HasAffineProperty.isLocal_affineProperty, HasAffineProperty.isStableUnderBaseChange, IsStableUnderBaseChange, infer_instance, introv, isLocal_affineProperty, isStableUnderBaseChange
-/
instance isAffineHom_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsAffineHom := by
  apply HasAffineProperty.isStableUnderBaseChange
  let := HasAffineProperty.isLocal_affineProperty
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  introv X hX H
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance (priority := 100) isAffineHom_of_isAffine [IsAffine X] [IsAffine Y] : IsAffineHom f :=
  (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom)).mpr inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isAffine_of_isAffineHom` / 引理 `isAffine_of_isAffineHom`

English:
lemma isAffine_of_isAffineHom
  given: [IsAffineHom f] [IsAffine Y]
  statement: IsAffine X
  proof: (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom) (f := f)).mp inferInstance

中文:
引理 isAffine_of_isAffineHom
  条件: [是仿射态射 f] [是仿射 Y]
  结论: 是仿射 X
  证明: (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom) (f := f)).mp inferInstance

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, IsAffineHom, iff_of_isAffine
-/
lemma isAffine_of_isAffineHom [IsAffineHom f] [IsAffine Y] : IsAffine X :=
  (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom) (f := f)).mp inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isAffineHom_of_forall_exists_isAffineOpen` / 引理 `isAffineHom_of_forall_exists_isAffineOpen`

English:
lemma isAffineHom_of_forall_exists_isAffineOpen
  proof: by
  choose U hxU hU hfU using H
  rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom) fun i => ⟨U i]; rw [hU i⟩]
  · exact hfU
  · exact top_le_iff.mp (fun x _ => by simpa using ⟨x, hxU x⟩)

中文:
引理 isAffineHom_of_对任意_存在_isAffineOpen
  证明: by
  choose U hxU hU hfU using H
  rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom) fun i => ⟨U i]; rw [hU i⟩]
  · exact hfU
  · exact top_le_iff.mp (fun x _ => by simpa using ⟨x, hxU x⟩)

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_iSup_eq_top, IsAffineHom, iff_of_iSup_eq_top, top_le_iff, top_le_iff.mp
-/
lemma isAffineHom_of_forall_exists_isAffineOpen
    (H : forall x : Y, exists U : Y.Opens, x in U ∧ IsAffineOpen U ∧ IsAffineOpen (f ⁻¹ᵁ U)) :
    IsAffineHom f := by
  choose U hxU hU hfU using H
  rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom) fun i => ⟨U i]; rw [hU i⟩]
  · exact hfU
  · exact top_le_iff.mp (fun x _ => by simpa using ⟨x, hxU x⟩)

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom f] [IsAffine Y] :
    IsAffine (pullback f g) :=
  letI : IsAffineHom (pullback.snd f g) := MorphismProperty.pullback_snd _ _ ‹_›
  isAffine_of_isAffineHom (pullback.snd f g)

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom g] [IsAffine X] :
    IsAffine (pullback f g) :=
  letI : IsAffineHom (pullback.fst f g) := MorphismProperty.pullback_fst _ _ ‹_›
  isAffine_of_isAffineHom (pullback.fst f g)

/--
lemma `IsAffine.of_isPullback` / 引理 `IsAffine.of_isPullback`

English:
lemma IsAffine.of_isPullback
  statement: {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  proof: .of_isIso h.isoPullback.hom

中文:
引理 是仿射.of_isPullback
  结论: {P : 概形.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
  证明: .of_isIso h.isoPullback.hom

Depends on / 依赖: h.isoPullback.hom, isoPullback, of_isIso
-/
lemma IsAffine.of_isPullback {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    [IsAffine X] [IsAffineHom g] (h : IsPullback fst snd f g) :
    IsAffine P :=
  .of_isIso h.isoPullback.hom

/--
lemma `isPushout_appTop_of_isPullback` / 引理 `isPushout_appTop_of_isPullback`

English:
lemma isPushout_appTop_of_isPullback
  statement: {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
  proof: by
  have : IsAffine P := .of_isPullback h
  have : IsPullback (AffineScheme.ofHom fst) (AffineScheme.ofHom snd) (AffineScheme.ofHom f)
      (AffineScheme.ofHom g) :=
    IsPullback.of_map_of_faithful AffineScheme.forgetToScheme.{u} h
  exact (IsPullback.map AffineScheme.Γ.rightOp this).unop.flip

中文:
引理 isPushout_appTop_of_isPullback
  结论: {P : 概形.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
  证明: by
  have : IsAffine P := .of_isPullback h
  have : IsPullback (AffineScheme.ofHom fst) (AffineScheme.ofHom snd) (AffineScheme.ofHom f)
      (AffineScheme.ofHom g) :=
    IsPullback.of_map_of_faithful AffineScheme.forgetToScheme.{u} h
  exact (IsPullback.map AffineScheme.Γ.rightOp this).unop.flip

Depends on / 依赖: AffineScheme, AffineScheme.forgetToScheme, AffineScheme.ofHom, IsAffine, IsPullback, IsPullback.map, IsPullback.of_map_of_faithful, forgetToScheme, of_isPullback, of_map_of_faithful, rightOp, unop.flip
-/
lemma isPushout_appTop_of_isPullback {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} [IsAffine X] [IsAffine Y] [IsAffine Z] (h : IsPullback fst snd f g) :
    IsPushout f.appTop g.appTop fst.appTop snd.appTop := by
  have : IsAffine P := .of_isPullback h
  have : IsPullback (AffineScheme.ofHom fst) (AffineScheme.ofHom snd) (AffineScheme.ofHom f)
      (AffineScheme.ofHom g) :=
    IsPullback.of_map_of_faithful AffineScheme.forgetToScheme.{u} h
  exact (IsPullback.map AffineScheme.Γ.rightOp this).unop.flip

set_option backward.isDefEq.respectTransparency false in
instance {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) [IsAffineHom f] [IsAffineHom g] :
    IsAffineHom (coprod.desc f g) := by
  refine ⟨fun W hW => ?_⟩
  have : IsAffine (f ⁻¹ᵁ W).toScheme := hW.preimage f
  have : IsAffine (g ⁻¹ᵁ W).toScheme := hW.preimage g
  let i : (f ⁻¹ᵁ W).toScheme ⨿ (g ⁻¹ᵁ W).toScheme ⟶ U ⨿ V := coprod.map (f ⁻¹ᵁ W).ι (g ⁻¹ᵁ W).ι
  convert! isAffineOpen_opensRange i
  apply le_antisymm
  · intro x hx
    obtain ⟨(x | x), rfl⟩ := (coprodMk U V).surjective x
    · replace hx : f x in W := by simpa [← Scheme.Hom.comp_apply] using hx
      exact ⟨coprodMk _ _ (.inl ⟨x, hx⟩), by simp [i, ← Scheme.Hom.comp_apply]⟩
    · replace hx : g x in W := by simpa [← Scheme.Hom.comp_apply] using hx
      exact ⟨coprodMk _ _ (.inr ⟨x, hx⟩), by simp [i, ← Scheme.Hom.comp_apply]⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨(⟨x, hx⟩ | ⟨x, hx⟩), rfl⟩ := (coprodMk _ _).surjective x
    · simpa [← Scheme.Hom.comp_apply, i] using hx
    · simpa [← Scheme.Hom.comp_apply, i] using hx

/-- If the underlying map of a morphism is inducing and has closed range, then it is affine. -/
@[stacks 04DE]
/--
lemma `isAffineHom_of_isInducing` / 引理 `isAffineHom_of_isInducing`

English:
lemma isAffineHom_of_isInducing
  proof: by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  by_cases hy : y in Set.range f
  · obtain ⟨x, rfl⟩ := hy
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.i

中文:
引理 isAffineHom_of_isInducing
  证明: by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  by_cases hy : y in Set.range f
  · obtain ⟨x, rfl⟩ := hy
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.i

Depends on / 依赖: Set.mem_univ, Set.range, X.isBasis_affineOpens.exists_subset_of_mem_open, Y.Opens, Y.isBasis_affineOpens.exists_subset_of_mem_open, exists_subset_of_mem_open, inf_le_right, isAffineHom_of_forall_exists_isAffineOpen, isBasis_affineOpens, isOpen, isOpen_iff, isOpen_iff.mp, isOpen_univ, mem_univ
-/
lemma isAffineHom_of_isInducing
    (hf₁ : Topology.IsInducing f)
    (hf₂ : IsClosed (Set.range f)) :
    IsAffineHom f := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  by_cases hy : y in Set.range f
  · obtain ⟨x, rfl⟩ := hy
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
    obtain ⟨U', hU'U, rfl⟩ : exists U' : Y.Opens, U' <= U ∧ f ⁻¹ᵁ U' = V := by
      obtain ⟨U', hU', e⟩ := hf₁.isOpen_iff.mp V.2
      exact ⟨⟨U', hU'⟩ ⊓ U, inf_le_right, Opens.ext (by simpa [e] using hVU)⟩
    obtain ⟨r, hrU', hxr⟩ := hU.exists_basicOpen_le ⟨f x, hxV⟩ hxU
    refine ⟨_, hxr, hU.basicOpen r, ?_⟩
    convert hV.basicOpen (f.app _ (Y.presheaf.map (homOfLE hU'U).op r))
    simp only [Scheme.preimage_basicOpen, ← CommRingCat.comp_apply, f.naturality]
    simpa using ((Opens.map f.base).map (homOfLE hrU')).le
  · obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hU'⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy hf₂.isOpen_compl
    rw [Set.subset_compl_iff_disjoint_right]; rw [← Set.preimage_eq_empty_iff] at hU'
    refine ⟨U, hyU, hU, ?_⟩
    convert isAffineOpen_bot _
    exact Opens.ext hU'

/--
lemma `IsAffineOpen.isCompact_pullback_inf` / 引理 `IsAffineOpen.isCompact_pullback_inf`

English:
lemma IsAffineOpen.isCompact_pullback_inf
  statement: {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
  proof: by
  have : IsAffine U.toScheme := hU
  have : IsAffine W.toScheme := hW
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV
  let f' : U.toScheme ⟶ W := f.resLE _ _ hUW
  let q : Scheme.Opens.toScheme V ⟶ W :=
IsOpenImmersion.lift W.ι (Scheme.Opens.ι _ ≫ g) by simpa [Set.range_comp]
  let p

中文:
引理 是仿射开集.isCompact_pullback_inf
  结论: {X Y Z : 概形.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
  证明: by
  have : IsAffine U.toScheme := hU
  have : IsAffine W.toScheme := hW
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV
  let f' : U.toScheme ⟶ W := f.resLE _ _ hUW
  let q : Scheme.Opens.toScheme V ⟶ W :=
IsOpenImmersion.lift W.ι (Scheme.Opens.ι _ ≫ g) by simpa [Set.range_comp]
  let p

Depends on / 依赖: CompactSpace, IsAffine, IsOpenImmersion, IsOpenImmersion.lift, Pullback, Scheme, Scheme.Opens, Scheme.Opens.toScheme, Scheme.Pullback.range_map, Set.range_comp, U.toScheme, W.toScheme, continuous, convert, f.resLE, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, isCompact_range, p.continuous, pullback
-/
lemma IsAffineOpen.isCompact_pullback_inf {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsCompact (V : Set Y))
    {W : Z.Opens} (hW : IsAffineOpen W) (hUW : U <= f ⁻¹ᵁ W) (hVW : V <= g ⁻¹ᵁ W) :
    IsCompact (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V : Set ↑(pullback f g)) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine W.toScheme := hW
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV
  let f' : U.toScheme ⟶ W := f.resLE _ _ hUW
  let q : Scheme.Opens.toScheme V ⟶ W :=
IsOpenImmersion.lift W.ι (Scheme.Opens.ι _ ≫ g) by simpa [Set.range_comp]
  let p : pullback f' q ⟶ pullback f g :=
    pullback.map _ _ _ _ U.ι (Scheme.Opens.ι _) W.ι (by simp [f']) (by simp [q])
  convert! isCompact_range p.continuous
  simp [p, Scheme.Pullback.range_map]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_morphismRestrict_iff_isIso_app` / 引理 `isIso_morphismRestrict_iff_isIso_app`

English:
lemma isIso_morphismRestrict_iff_isIso_app
  given: [IsAffineHom f] {U : Y.Opens} (hU : IsAffineOpen U)
  proof: by
  have : IsAffine U := hU
refine (HasAffineProperty.iff_of_isAffine (P := .isomorphisms _)).trans
    (and_iff_right (hU.preimage f)).trans ?_
  rw [Scheme.Hom.app_eq_appLE]
  simp only [morphismRestrict_app', TopologicalSpace.Opens.map_top]
  congr! <;> simp [Scheme.Opens.toScheme_presheaf_obj]

中文:
引理 isIso_morphismRestrict_iff_isIso_app
  条件: [是仿射态射 f] {U : Y.Opens} (hU : 是仿射开集 U)
  证明: by
  have : IsAffine U := hU
refine (HasAffineProperty.iff_of_isAffine (P := .isomorphisms _)).trans
    (and_iff_right (hU.preimage f)).trans ?_
  rw [Scheme.Hom.app_eq_appLE]
  simp only [morphismRestrict_app', TopologicalSpace.Opens.map_top]
  congr! <;> simp [Scheme.Opens.toScheme_presheaf_obj]

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, IsAffine, Scheme, Scheme.Hom.app_eq_appLE, Scheme.Opens.toScheme_presheaf_obj, TopologicalSpace, TopologicalSpace.Opens.map_top, and_iff_right, app_eq_appLE, hU.preimage, iff_of_isAffine, isomorphisms, map_top, morphismRestrict_app, preimage, toScheme_presheaf_obj
-/
lemma isIso_morphismRestrict_iff_isIso_app [IsAffineHom f] {U : Y.Opens} (hU : IsAffineOpen U) :
    IsIso (f ∣_ U) ↔ IsIso (f.app U) := by
  have : IsAffine U := hU
refine (HasAffineProperty.iff_of_isAffine (P := .isomorphisms _)).trans
    (and_iff_right (hU.preimage f)).trans ?_
  rw [Scheme.Hom.app_eq_appLE]
  simp only [morphismRestrict_app', TopologicalSpace.Opens.map_top]
  congr! <;> simp [Scheme.Opens.toScheme_presheaf_obj]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `diagonal_isAffine_iff_forall_isAffineOpen_inf` / 定理 `diagonal_isAffine_iff_forall_isAffineOpen_inf`

English:
theorem diagonal_isAffine_iff_forall_isAffineOpen_inf
  given: [IsAffine Y] (f : X ⟶ Y)
  proof: by
  delta AffineTargetMorphismProperty.diagonal
  constructor
  · intro H U V hU hV
    dsimp at H
    have : IsAffine _ := hU
    have : IsAffine _ := hV
    let g : pullback U.ι V.ι ⟶ X := pullback.fst _ _ ≫ U.ι
    have := IsOpenImmersion.isPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_righ

中文:
定理 diagonal_isAffine_iff_对任意_isAffineOpen_inf
  条件: [是仿射 Y] (f : X ⟶ Y)
  证明: by
  delta AffineTargetMorphismProperty.diagonal
  constructor
  · intro H U V hU hV
    dsimp at H
    have : IsAffine _ := hU
    have : IsAffine _ := hV
    let g : pullback U.ι V.ι ⟶ X := pullback.fst _ _ ≫ U.ι
    have := IsOpenImmersion.isPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_righ

Depends on / 依赖: AffineTargetMorphismProperty, AffineTargetMorphismProperty.diagonal, IsAffine, IsAffineOpen, IsOpenImmersion, IsOpenImmersion.isPullback, X.homOfLE, convert, diagonal, homOfLE, inf_le_left, inf_le_right, introv, isAffineOpen_opensRange, isPullback, isoPullback, of_isIso, opensRange, pullback, pullback.fst
-/
theorem diagonal_isAffine_iff_forall_isAffineOpen_inf [IsAffine Y] (f : X ⟶ Y) :
    AffineTargetMorphismProperty.diagonal (fun X _ _ _ => IsAffine X) f ↔
      forall (U V : X.Opens), IsAffineOpen U -> IsAffineOpen V -> IsAffineOpen (U ⊓ V) := by
  delta AffineTargetMorphismProperty.diagonal
  constructor
  · intro H U V hU hV
    dsimp at H
    have : IsAffine _ := hU
    have : IsAffine _ := hV
    let g : pullback U.ι V.ι ⟶ X := pullback.fst _ _ ≫ U.ι
    have := IsOpenImmersion.isPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right)
      U.ι V.ι (by simp) (by ext; simp)
    exact .of_isIso this.isoPullback.hom
  · introv H h₁ h₂
    have : IsAffineOpen (pullback.fst f₁ f₂ ≫ f₁).opensRange := by
      convert! H _ _ (isAffineOpen_opensRange f₁) (isAffineOpen_opensRange f₂)
      exact Opens.ext (IsOpenImmersion.range_pullback_to_base_of_left _ _)
    change IsAffine _ at this
    exact .of_isIso (pullback.fst f₁ f₂ ≫ f₁).isoOpensRange.hom

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isAffineHom_diagonal_iff` / 定理 `isAffineHom_diagonal_iff`

English:
theorem isAffineHom_diagonal_iff
  given: {f : X ⟶ Y}
  proof: by
  refine congr($(HasAffineProperty.eq_targetAffineLocally
    (.diagonal @IsAffineHom)) f).to_iff.trans ?_
  simp only [targetAffineLocally, diagonal_isAffine_iff_forall_isAffineOpen_inf,
    (IsOpenImmersion.opensEquiv (f ⁻¹ᵁ _).ι).forall_congr_left, Scheme.affineOpens,
    Subtype.forall, Set.m

中文:
定理 isAffineHom_diagonal_iff
  条件: {f : X ⟶ Y}
  证明: by
  refine congr($(HasAffineProperty.eq_targetAffineLocally
    (.diagonal @IsAffineHom)) f).to_iff.trans ?_
  simp only [targetAffineLocally, diagonal_isAffine_iff_forall_isAffineOpen_inf,
    (IsOpenImmersion.opensEquiv (f ⁻¹ᵁ _).ι).forall_congr_left, Scheme.affineOpens,
    Subtype.forall, Set.m

Depends on / 依赖: HasAffineProperty, HasAffineProperty.eq_targetAffineLocally, IsAffineHom, IsOpenImmersion, IsOpenImmersion.opensEquiv, IsOpenImmersion.opensEquiv_symm_apply, Scheme, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.preimage_inf, Scheme.Opens, Scheme.Opens.opensRange_, Scheme.affineOpens, Set.mem_ofPred_eq, Subtype, Subtype.forall, affineOpens, diagonal, diagonal_isAffine_iff_forall_isAffineOpen_inf, eq_targetAffineLocally
-/
theorem isAffineHom_diagonal_iff {f : X ⟶ Y} :
    IsAffineHom (pullback.diagonal f) ↔
      forall (U : Y.Opens), IsAffineOpen U -> forall V₁ <= f ⁻¹ᵁ U, forall V₂ <= f ⁻¹ᵁ U,
        IsAffineOpen V₁ -> IsAffineOpen V₂ -> IsAffineOpen (V₁ ⊓ V₂) := by
  refine congr($(HasAffineProperty.eq_targetAffineLocally
    (.diagonal @IsAffineHom)) f).to_iff.trans ?_
  simp only [targetAffineLocally, diagonal_isAffine_iff_forall_isAffineOpen_inf,
    (IsOpenImmersion.opensEquiv (f ⁻¹ᵁ _).ι).forall_congr_left, Scheme.affineOpens,
    Subtype.forall, Set.mem_ofPred_eq, Scheme.Opens.opensRange_ι, ← Scheme.Hom.preimage_inf,
    IsOpenImmersion.opensEquiv_symm_apply, Scheme.Hom.image_preimage_eq_opensRange_inf,
    ← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (Scheme.Opens.ι _)]
  congr! with U hU V₁ hV₁ V₂ hV₂
  rw [inf_eq_right.mpr hV₁]; rw [inf_eq_right.mpr hV₂]; rw [inf_eq_right.mpr (inf_le_left.trans hV₁)]

/--
lemma `IsAffineOpen.inf` / 引理 `IsAffineOpen.inf`

English:
lemma IsAffineOpen.inf
  statement: [IsAffineHom (pullback.diagonal (terminal.from X))]
  proof: isAffineHom_diagonal_iff.mp ‹_› ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV

中文:
引理 是仿射开集.下确界
  结论: [是仿射态射 (pullback.diagonal (terminal.from X))]
  证明: isAffineHom_diagonal_iff.mp ‹_› ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV

Depends on / 依赖: isAffineHom_diagonal_iff, isAffineHom_diagonal_iff.mp, isAffineOpen_top
-/
lemma IsAffineOpen.inf [IsAffineHom (pullback.diagonal (terminal.from X))]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) :=
  isAffineHom_diagonal_iff.mp ‹_› ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV

/--
lemma `IsAffineOpen.iInf` / 引理 `IsAffineOpen.iInf`

English:
lemma IsAffineOpen.iInf
  statement: [IsAffineHom (pullback.diagonal (terminal.from X))]
  proof: InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen) (fun _ h _ h' => h.inf h') hU

中文:
引理 是仿射开集.iInf
  结论: [是仿射态射 (pullback.diagonal (terminal.from X))]
  证明: InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen) (fun _ h _ h' => h.inf h') hU

Depends on / 依赖: InfClosed, InfClosed.iInf_mem_of_nonempty, IsAffineOpen, Set.ofPred, h.inf, iInf_mem_of_nonempty, ofPred
-/
lemma IsAffineOpen.iInf [IsAffineHom (pullback.diagonal (terminal.from X))]
    {ι : Sort*} [Finite ι] [Nonempty ι] {U : ι -> X.Opens} (hU : forall i, IsAffineOpen (U i)) :
      IsAffineOpen (⨅ i, U i) :=
  InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen) (fun _ h _ h' => h.inf h') hU

/--
lemma `IsAffineOpen.biInf` / 引理 `IsAffineOpen.biInf`

English:
lemma IsAffineOpen.biInf
  statement: [IsAffineHom (pullback.diagonal (terminal.from X))]
  proof: InfClosed.biInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen) (fun _ h _ h' => h.inf h') hs hs' hU

中文:
引理 是仿射开集.biInf
  结论: [是仿射态射 (pullback.diagonal (terminal.from X))]
  证明: InfClosed.biInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen) (fun _ h _ h' => h.inf h') hs hs' hU

Depends on / 依赖: InfClosed, InfClosed.biInf_mem_of_nonempty, IsAffineOpen, Set.ofPred, biInf_mem_of_nonempty, h.inf, ofPred
-/
lemma IsAffineOpen.biInf [IsAffineHom (pullback.diagonal (terminal.from X))]
    {ι : Type*} (s : Set ι) (hs : s.Finite) (hs' : s.Nonempty) {U : ι -> X.Opens}
    (hU : forall i in s, IsAffineOpen (U i)) : IsAffineOpen (⨅ i in s, U i) :=
  InfClosed.biInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen) (fun _ h _ h' => h.inf h') hs hs' hU

end AlgebraicGeometry
