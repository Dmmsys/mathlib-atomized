/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!

# Morphisms of finite presentation

A morphism of schemes `f : X ⟶ Y` is locally of finite presentation if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite presentation.

A morphism of schemes is of finite presentation if it is both locally of finite presentation and
quasi-compact. We do not provide a separate declaration for this, instead simply assume both
conditions.

We show that these properties are local, and are stable under compositions.

-/

public section


noncomputable section

open CategoryTheory Topology

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite presentation if for each affine `U ⊆ Y`
and `V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite presentation. -/
@[mk_iff]
/--
Definition of `LocallyOfFinitePresentation` / `LocallyOfFinitePresentation` 的定义

English:
class LocallyOfFinitePresentation
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - finitePresentation_appLE((f)) : forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.FinitePresentation

中文:
类 LocallyOfFinitePresentation
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - finitePresentation_appLE((f)) : 对任意 {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.FinitePresentation

Depends on / 依赖: LocallyOfFinitePresentation, LocallyOfFinitePresentation.finitePresentation_appLE, finitePresentation_appLE
-/
class LocallyOfFinitePresentation (f : X ⟶ Y) : Prop where
  finitePresentation_appLE (f) :
    forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U),
      (f.appLE U V e).hom.FinitePresentation

alias Scheme.Hom.finitePresentation_appLE := LocallyOfFinitePresentation.finitePresentation_appLE

@[deprecated (since := "2026-01-20")]
alias LocallyOfFinitePresentation.finitePresentation_of_affine_subset :=
  Scheme.Hom.finitePresentation_appLE

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasRingHomProperty @LocallyOfFinitePresentation RingHom.FinitePresentation
  body: RingHom.finitePresentation_isLocal
  eq_affineLocally' := by
    ext X Y f
    rw [locallyOfFinitePresentation_iff]; rw [affineLocally_iff_forall_isAffineOpen]

中文:
实例 :
  签名: HasRingHom命题erty @LocallyOfFinitePresentation RingHom.FinitePresentation
  定义体: RingHom.finitePresentation_isLocal
  eq_affineLocally' := by
    ext X Y f
    rw [locallyOfFinitePresentation_iff]; rw [affineLocally_iff_forall_isAffineOpen]

Depends on / 依赖: RingHom, RingHom.finitePresentation_isLocal, finitePresentation_isLocal
-/
instance : HasRingHomProperty @LocallyOfFinitePresentation RingHom.FinitePresentation where
  isLocal_ringHomProperty := RingHom.finitePresentation_isLocal
  eq_affineLocally' := by
    ext X Y f
    rw [locallyOfFinitePresentation_iff]; rw [affineLocally_iff_forall_isAffineOpen]

instance (priority := 900) locallyOfFinitePresentation_of_isOpenImmersion [IsOpenImmersion f] :
    LocallyOfFinitePresentation f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.finitePresentation_holdsForLocalizationAway.containsIdentities

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsStableUnderComposition @LocallyOfFinitePresentation
  body: HasRingHomProperty.stableUnderComposition RingHom.finitePresentation_stableUnderComposition

@[simp]

中文:
实例 :
  签名: Morphism命题erty.IsStableUnderComposition @LocallyOfFinitePresentation
  定义体: HasRingHomProperty.stableUnderComposition RingHom.finitePresentation_stableUnderComposition

@[simp]

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.stableUnderComposition, RingHom, RingHom.finitePresentation_stableUnderComposition, finitePresentation_stableUnderComposition, stableUnderComposition
-/
instance : MorphismProperty.IsStableUnderComposition @LocallyOfFinitePresentation :=
  HasRingHomProperty.stableUnderComposition RingHom.finitePresentation_stableUnderComposition

@[simp]
/--
lemma `LocallyOfFinitePresentation.SpecMap_iff` / 引理 `LocallyOfFinitePresentation.SpecMap_iff`

English:
lemma LocallyOfFinitePresentation.SpecMap_iff
  given: {R S : CommRingCat.{u}} (f : R ⟶ S)
  proof: HasRingHomProperty.Spec_iff

中文:
引理 LocallyOfFinitePresentation.SpecMap_iff
  条件: {R S : CommRingCat.{u}} (f : R ⟶ S)
  证明: HasRingHomProperty.Spec_iff

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.Spec_iff, Spec_iff
-/
lemma LocallyOfFinitePresentation.SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    LocallyOfFinitePresentation (Spec.map f) ↔ f.hom.FinitePresentation :=
  HasRingHomProperty.Spec_iff

/--
lemma `Scheme.Hom.finitePresentation_appTop` / 引理 `Scheme.Hom.finitePresentation_appTop`

English:
lemma Scheme.Hom.finitePresentation_appTop
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
  proof: HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) _ inferInstance

中文:
引理 Scheme.Hom.finitePresentation_appTop
  结论: {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
  证明: HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) _ inferInstance

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.appTop, LocallyOfFinitePresentation, appTop
-/
lemma Scheme.Hom.finitePresentation_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    [LocallyOfFinitePresentation f] :
    f.appTop.hom.FinitePresentation :=
  HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) _ inferInstance

/--
Instance `locallyOfFinitePresentation_comp` / 实例 `locallyOfFinitePresentation_comp`

English:
instance locallyOfFinitePresentation_comp
  signature: {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: MorphismProperty.comp_mem _ f g hf hg

中文:
实例 locallyOfFinitePresentation_comp
  签名: {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: MorphismProperty.comp_mem _ f g hf hg

Depends on / 依赖: MorphismProperty, MorphismProperty.comp_mem, comp_mem
-/
instance locallyOfFinitePresentation_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFinitePresentation f] [hg : LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

/--
Instance `locallyOfFinitePresentation_isStableUnderBaseChange` / 实例 `locallyOfFinitePresentation_isStableUnderBaseChange`

English:
instance locallyOfFinitePresentation_isStableUnderBaseChange
  signature: :
  body: HasRingHomProperty.isStableUnderBaseChange RingHom.finitePresentation_isStableUnderBaseChange

中文:
实例 locallyOfFinitePresentation_isStableUnderBaseChange
  签名: :
  定义体: HasRingHomProperty.isStableUnderBaseChange RingHom.finitePresentation_isStableUnderBaseChange

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.isStableUnderBaseChange, RingHom, RingHom.finitePresentation_isStableUnderBaseChange, finitePresentation_isStableUnderBaseChange, isStableUnderBaseChange
-/
instance locallyOfFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @LocallyOfFinitePresentation :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.finitePresentation_isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (V : Y.Opens) [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : LocallyOfFinitePresentation f] :
    LocallyOfFiniteType f := by
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation] at hf
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFiniteType]
  refine affineLocally_le (fun hf => ?_) f hf
  exact RingHom.FiniteType.of_finitePresentation hf

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Chevalley's Theorem**: The image of a locally constructible set under a
morphism of finite presentation is locally constructible. -/
@[stacks 054K]
-- `nonrec` is needed for `wlog`
nonrec lemma Scheme.Hom.isLocallyConstructible_image (f : X ⟶ Y)
    [hf : LocallyOfFinitePresentation f] [QuasiCompact f]
    {s : Set X} (hs : IsLocallyConstructible s) :
    IsLocallyConstructible (f '' s) := by
  wlog hY : exists R, Y = Spec R
  · refine .of_isOpenCover Y.affineCover.isOpenCover_opensRange fun i => ?_
    have inst : LocallyOfFinitePresentation (Y.affineCover.pullbackHom f i) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have inst : QuasiCompact (Y.affineCover.pullbackHom f i) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    convert!
      (this (Y.affineCover.pullbackHom f i)
            (hs.preimage_of_isOpenEmbedding ((Y.affineCover.pullback₁ f).f i).isOpenEmbedding)
            ⟨_, rfl⟩).preimage_of_isOpenEmbedding
        (Y.affineCover.f i).isoOpensRange.inv.isOpenEmbedding
    refine .trans ?_
      ((Scheme.homeoOfIso (Y.affineCover.f i).isoOpensRange).image_eq_preimage_symm _)
    apply Set.image_injective.mpr Subtype.val_injective
    rw [Set.image_preimage_eq_inter_range]; rw [← Set.image_comp]; rw [← Set.image_comp]; rw [Subtype.range_coe_subtype]; rw [Set.ofPred_mem_eq]
    change _ = (Y.affineCover.pullbackHom f i ≫
      (Y.affineCover.f i).isoOpensRange.hom ≫ Opens.ι _).base.hom '' _
    rw [Scheme.Hom.isoOpensRange_hom_ι]; rw [Cover.pullbackHom_map]; rw [Scheme.Hom.comp_base]; rw [TopCat.hom_comp]; rw [ContinuousMap.coe_comp]; rw [Set.image_comp]; rw [Set.image_preimage_eq_inter_range]
    simp [IsOpenImmersion.range_pullbackFst, Set.image_inter_preimage]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S
  · have inst : CompactSpace X := HasAffineProperty.iff_of_isAffine.mp ‹QuasiCompact f›
    let 𝒰 := X.affineCover.finiteSubcover
    rw [← 𝒰.isOpenCover_opensRange.iUnion_inter s]; rw [Set.image_iUnion]
    refine .iUnion fun i => ?_
    have inst : QuasiCompact (𝒰.f i ≫ f) :=
      HasAffineProperty.iff_of_isAffine.mpr (inferInstanceAs (CompactSpace (Spec _)))
    convert! this (hs.preimage_of_isOpenEmbedding (𝒰.f i).isOpenEmbedding) _ (𝒰.f i ≫ f) ⟨_, rfl⟩
    rw [Scheme.Hom.comp_base]; rw [← TopCat.Hom.hom]; rw [← TopCat.Hom.hom]; rw [TopCat.hom_comp]; rw [ContinuousMap.coe_comp]; rw [Set.image_comp]; rw [Set.image_preimage_eq_inter_range]; rw [coe_opensRange]
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hf
  exact (PrimeSpectrum.isConstructible_comap_image hf hs.isConstructible).isLocallyConstructible

/-- **Chevalley's Theorem**: The image of a constructible set under a
morphism of finite presentation into a qcqs scheme is constructible. -/
@[stacks 054J]
/--
lemma `Scheme.Hom.isConstructible_image` / 引理 `Scheme.Hom.isConstructible_image`

English:
lemma Scheme.Hom.isConstructible_image
  statement: (f : X ⟶ Y)
  proof: (f.isLocallyConstructible_image hs.isLocallyConstructible).isConstructible

@[stacks 054I]

中文:
引理 Scheme.Hom.isConstructible_image
  结论: (f : X ⟶ Y)
  证明: (f.isLocallyConstructible_image hs.isLocallyConstructible).isConstructible

@[stacks 054I]

Depends on / 依赖: f.isLocallyConstructible_image, hs.isLocallyConstructible, isConstructible, isLocallyConstructible, isLocallyConstructible_image
-/
lemma Scheme.Hom.isConstructible_image (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    {s : Set X} (hs : IsConstructible s) :
    IsConstructible (f '' s) :=
  (f.isLocallyConstructible_image hs.isLocallyConstructible).isConstructible

@[stacks 054I]
/--
lemma `Scheme.Hom.isConstructible_preimage` / 引理 `Scheme.Hom.isConstructible_preimage`

English:
lemma Scheme.Hom.isConstructible_preimage
  given: (f : X ⟶ Y) {s : Set Y} (hs : IsConstructible s)
  proof: hs.preimage f.continuous fun t ht ht' => IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr
    (quasiCompact_iff_isSpectralMap.mp
    (MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_morphismRestrict f ⟨t, ht⟩)
    (quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralM

中文:
引理 Scheme.Hom.isConstructible_preimage
  条件: (f : X ⟶ Y) {s : Set Y} (hs : IsConstructible s)
  证明: hs.preimage f.continuous fun t ht ht' => IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr
    (quasiCompact_iff_isSpectralMap.mp
    (MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_morphismRestrict f ⟨t, ht⟩)
    (quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralM

Depends on / 依赖: IsRetrocompact_iff_isSpectralMap_subtypeVal, IsRetrocompact_iff_isSpectralMap_subtypeVal.mp, IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr, MorphismProperty, MorphismProperty.of_isPullback, QuasiCompact, continuous, f.continuous, hs.preimage, isPullback_morphismRestrict, of_isPullback, preimage, quasiCompact_iff_isSpectralMap, quasiCompact_iff_isSpectralMap.mp, quasiCompact_iff_isSpectralMap.mpr
-/
lemma Scheme.Hom.isConstructible_preimage (f : X ⟶ Y) {s : Set Y} (hs : IsConstructible s) :
    IsConstructible (f ⁻¹' s) :=
  hs.preimage f.continuous fun t ht ht' => IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr
    (quasiCompact_iff_isSpectralMap.mp
    (MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_morphismRestrict f ⟨t, ht⟩)
    (quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp ht'))))

end AlgebraicGeometry
