/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.RingTheory.RingHom.Surjective
public import Mathlib.RingTheory.Spectrum.Prime.TensorProduct
public import Mathlib.Topology.LocalAtTarget

/-!
# Morphisms surjective on stalks

We define the class of morphisms between schemes that are surjective on stalks.
We show that this class is stable under composition and base change.

We also show that (`AlgebraicGeometry.SurjectiveOnStalks.isEmbedding_pullback`)
if `Y ⟶ S` is surjective on stalks, then for every `X ⟶ S`, `X ×ₛ Y` is a subset of
`X × Y` (Cartesian product as topological spaces) with the induced topology.
-/

public section

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The class of morphisms `f : X ⟶ Y` between schemes such that
`𝒪_{Y, f x} ⟶ 𝒪_{X, x}` is surjective for all `x : X`. -/
@[mk_iff]
/--
Definition of `SurjectiveOnStalks` / `SurjectiveOnStalks` 的定义

English:
class SurjectiveOnStalks
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - stalkMap_surjective((f)) : forall x, Function.Surjective (f.stalkMap x)

中文:
类 SurjectiveOnStalks
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - stalkMap_surjective((f)) : 对任意 x, 函数.满射 (f.stalkMap x)

Depends on / 依赖: SurjectiveOnStalks, SurjectiveOnStalks.stalkMap_surjective, stalkMap_surjective
-/
class SurjectiveOnStalks (f : X ⟶ Y) : Prop where
  stalkMap_surjective (f) : forall x, Function.Surjective (f.stalkMap x)

alias Scheme.Hom.stalkMap_surjective := SurjectiveOnStalks.stalkMap_surjective

@[deprecated (since := "2026-01-20")]
alias SurjectiveOnStalks.surj_on_stalks := Scheme.Hom.stalkMap_surjective

namespace SurjectiveOnStalks

instance (priority := 900) [IsOpenImmersion f] : SurjectiveOnStalks f :=
  ⟨fun _ => (ConcreteCategory.bijective_of_isIso _).2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @SurjectiveOnStalks
  body: inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine ⟨fun x => ?_⟩
    rw [Scheme.Hom.stalkMap_comp]
    exact (f.stalkMap_surjective x).comp (g.stalkMap_surjective (f x))

中文:
实例 :
  签名: MorphismProperty.是Multiplicative @SurjectiveOnStalks
  定义体: inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine ⟨fun x => ?_⟩
    rw [Scheme.Hom.stalkMap_comp]
    exact (f.stalkMap_surjective x).comp (g.stalkMap_surjective (f x))
-/
instance : MorphismProperty.IsMultiplicative @SurjectiveOnStalks where
  id_mem _ := inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine ⟨fun x => ?_⟩
    rw [Scheme.Hom.stalkMap_comp]
    exact (f.stalkMap_surjective x).comp (g.stalkMap_surjective (f x))

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [SurjectiveOnStalks f]
  body: MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

中文:
实例 comp
  签名: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z) [SurjectiveOnStalks f]
  定义体: MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

Depends on / 依赖: IsStableUnderComposition, MorphismProperty, MorphismProperty.IsStableUnderComposition.comp_mem, comp_mem
-/
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [SurjectiveOnStalks f]
    [SurjectiveOnStalks g] : SurjectiveOnStalks (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

/--
lemma `eq_stalkwise` / 引理 `eq_stalkwise`

English:
lemma eq_stalkwise
  proof: by
  ext; exact surjectiveOnStalks_iff _

中文:
引理 eq_stalkwise
  证明: by
  ext; exact surjectiveOnStalks_iff _

Depends on / 依赖: surjectiveOnStalks_iff
-/
lemma eq_stalkwise :
    @SurjectiveOnStalks = stalkwise (Function.Surjective ·) := by
  ext; exact surjectiveOnStalks_iff _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtTarget @SurjectiveOnStalks
  body: eq_stalkwise ▸ stalkwiseIsZariskiLocalAtTarget_of_respectsIso RingHom.surjective_respectsIso

中文:
实例 :
  签名: IsZariskiLocalAtTarget @SurjectiveOnStalks
  定义体: eq_stalkwise ▸ stalkwiseIsZariskiLocalAtTarget_of_respectsIso RingHom.surjective_respectsIso

Depends on / 依赖: RingHom, RingHom.surjective_respectsIso, eq_stalkwise, stalkwiseIsZariskiLocalAtTarget_of_respectsIso, surjective_respectsIso
-/
instance : IsZariskiLocalAtTarget @SurjectiveOnStalks :=
  eq_stalkwise ▸ stalkwiseIsZariskiLocalAtTarget_of_respectsIso RingHom.surjective_respectsIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtSource @SurjectiveOnStalks
  body: eq_stalkwise ▸ stalkwise_isZariskiLocalAtSource_of_respectsIso RingHom.surjective_respectsIso

中文:
实例 :
  签名: IsZariskiLocalAtSource @SurjectiveOnStalks
  定义体: eq_stalkwise ▸ stalkwise_isZariskiLocalAtSource_of_respectsIso RingHom.surjective_respectsIso

Depends on / 依赖: RingHom, RingHom.surjective_respectsIso, eq_stalkwise, stalkwise_isZariskiLocalAtSource_of_respectsIso, surjective_respectsIso
-/
instance : IsZariskiLocalAtSource @SurjectiveOnStalks :=
  eq_stalkwise ▸ stalkwise_isZariskiLocalAtSource_of_respectsIso RingHom.surjective_respectsIso

/--
lemma `Spec_iff` / 引理 `Spec_iff`

English:
lemma Spec_iff
  given: {R S : CommRingCat.{u}} {φ : R ⟶ S}
  proof: by
  rw [eq_stalkwise]; rw [stalkwise_SpecMap_iff RingHom.surjective_respectsIso]; rw [RingHom.SurjectiveOnStalks]

中文:
引理 Spec_iff
  条件: {R S : 交换环范畴.{u}} {φ : R ⟶ S}
  证明: by
  rw [eq_stalkwise]; rw [stalkwise_SpecMap_iff RingHom.surjective_respectsIso]; rw [RingHom.SurjectiveOnStalks]

Depends on / 依赖: RingHom, RingHom.SurjectiveOnStalks, RingHom.surjective_respectsIso, SurjectiveOnStalks, eq_stalkwise, stalkwise_SpecMap_iff, surjective_respectsIso
-/
lemma Spec_iff {R S : CommRingCat.{u}} {φ : R ⟶ S} :
    SurjectiveOnStalks (Spec.map φ) ↔ RingHom.SurjectiveOnStalks φ.hom := by
  rw [eq_stalkwise]; rw [stalkwise_SpecMap_iff RingHom.surjective_respectsIso]; rw [RingHom.SurjectiveOnStalks]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasRingHomProperty @SurjectiveOnStalks RingHom.SurjectiveOnStalks
  body: eq_stalkwise ▸ .stalkwise RingHom.surjective_respectsIso

中文:
实例 :
  签名: 有RingHomProperty @SurjectiveOnStalks 环态射.SurjectiveOnStalks
  定义体: eq_stalkwise ▸ .stalkwise RingHom.surjective_respectsIso

Depends on / 依赖: RingHom, RingHom.surjective_respectsIso, eq_stalkwise, stalkwise, surjective_respectsIso
-/
instance : HasRingHomProperty @SurjectiveOnStalks RingHom.SurjectiveOnStalks :=
  eq_stalkwise ▸ .stalkwise RingHom.surjective_respectsIso

set_option backward.isDefEq.respectTransparency false in
variable {f} in
/--
lemma `iff_of_isAffine` / 引理 `iff_of_isAffine`

English:
lemma iff_of_isAffine
  given: [IsAffine X] [IsAffine Y]
  proof: by
  rw [← Spec_iff]; rw [MorphismProperty.arrow_mk_iso_iff @SurjectiveOnStalks (arrowIsoSpecΓOfIsAffine f)]

中文:
引理 iff_of_isAffine
  条件: [是仿射 X] [是仿射 Y]
  证明: by
  rw [← Spec_iff]; rw [MorphismProperty.arrow_mk_iso_iff @SurjectiveOnStalks (arrowIsoSpecΓOfIsAffine f)]

Depends on / 依赖: MorphismProperty, MorphismProperty.arrow_mk_iso_iff, Spec_iff, SurjectiveOnStalks, arrow_mk_iso_iff
-/
lemma iff_of_isAffine [IsAffine X] [IsAffine Y] :
    SurjectiveOnStalks f ↔ RingHom.SurjectiveOnStalks (f.app ⊤).hom := by
  rw [← Spec_iff]; rw [MorphismProperty.arrow_mk_iso_iff @SurjectiveOnStalks (arrowIsoSpecΓOfIsAffine f)]

/--
theorem `of_comp` / 定理 `of_comp`

English:
theorem of_comp
  given: [SurjectiveOnStalks (f ≫ g)]
  statement: SurjectiveOnStalks f
  proof: by
  refine ⟨fun x => ?_⟩
  have := (f ≫ g).stalkMap_surjective x
  rw [Scheme.Hom.stalkMap_comp] at this
  exact Function.Surjective.of_comp this

中文:
定理 of_comp
  条件: [SurjectiveOnStalks (f ≫ g)]
  结论: SurjectiveOnStalks f
  证明: by
  refine ⟨fun x => ?_⟩
  have := (f ≫ g).stalkMap_surjective x
  rw [Scheme.Hom.stalkMap_comp] at this
  exact Function.Surjective.of_comp this

Depends on / 依赖: Function, Function.Surjective.of_comp, Scheme, Scheme.Hom.stalkMap_comp, Surjective, of_comp, stalkMap_comp, stalkMap_surjective
-/
theorem of_comp [SurjectiveOnStalks (f ≫ g)] : SurjectiveOnStalks f := by
  refine ⟨fun x => ?_⟩
  have := (f ≫ g).stalkMap_surjective x
  rw [Scheme.Hom.stalkMap_comp] at this
  exact Function.Surjective.of_comp this

/--
Instance `stableUnderBaseChange` / 实例 `stableUnderBaseChange`

English:
instance stableUnderBaseChange
  signature: :
  body: by
  apply HasRingHomProperty.isStableUnderBaseChange
  apply RingHom.IsStableUnderBaseChange.mk
  · exact (HasRingHomProperty.isLocal_ringHomProperty @SurjectiveOnStalks).respectsIso
  intro R S T _ _ _ _ _ H
  exact H.baseChange

中文:
实例 stableUnderBaseChange
  签名: :
  定义体: by
  apply HasRingHomProperty.isStableUnderBaseChange
  apply RingHom.IsStableUnderBaseChange.mk
  · exact (HasRingHomProperty.isLocal_ringHomProperty @SurjectiveOnStalks).respectsIso
  intro R S T _ _ _ _ _ H
  exact H.baseChange

Depends on / 依赖: H.baseChange, HasRingHomProperty, HasRingHomProperty.isLocal_ringHomProperty, HasRingHomProperty.isStableUnderBaseChange, IsStableUnderBaseChange, RingHom, RingHom.IsStableUnderBaseChange.mk, SurjectiveOnStalks, baseChange, isLocal_ringHomProperty, isStableUnderBaseChange, respectsIso
-/
instance stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @SurjectiveOnStalks := by
  apply HasRingHomProperty.isStableUnderBaseChange
  apply RingHom.IsStableUnderBaseChange.mk
  · exact (HasRingHomProperty.isLocal_ringHomProperty @SurjectiveOnStalks).respectsIso
  intro R S T _ _ _ _ _ H
  exact H.baseChange

variable {f} in
/--
lemma `mono_of_injective` / 引理 `mono_of_injective`

English:
lemma mono_of_injective
  given: [SurjectiveOnStalks f] (hf : Function.Injective f)
  statement: Mono f
  proof: by
  refine (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).mono_of_mono_map ?_
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact hf
  · exact fun x => ConcreteCategory.epi_of_surjective _ (f.stalkMap_surjective x)

中文:
引理 mono_of_injective
  条件: [SurjectiveOnStalks f] (hf : 函数.单射 f)
  结论: 单态射 f
  证明: by
  refine (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).mono_of_mono_map ?_
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact hf
  · exact fun x => ConcreteCategory.epi_of_surjective _ (f.stalkMap_surjective x)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.epi_of_surjective, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace, Scheme, Scheme.forgetToLocallyRingedSpace, SheafedSpace, SheafedSpace.mono_of_base_injective_of_stalk_epi, epi_of_surjective, f.stalkMap_surjective, forgetToLocallyRingedSpace, forgetToSheafedSpace, mono_of_base_injective_of_stalk_epi, mono_of_mono_map, stalkMap_surjective
-/
lemma mono_of_injective [SurjectiveOnStalks f] (hf : Function.Injective f) : Mono f := by
  refine (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).mono_of_mono_map ?_
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact hf
  · exact fun x => ConcreteCategory.epi_of_surjective _ (f.stalkMap_surjective x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isEmbedding_pullback` / 引理 `isEmbedding_pullback`

English:
lemma isEmbedding_pullback
  given: {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [SurjectiveOnStalks g]
  proof: by
  let L := (fun x => (pullback.fst f g x, pullback.snd f g x))
  have H : forall R A B (f' : Spec A ⟶ Spec R) (g' : Spec B ⟶ Spec R) (iX : Spec A ⟶ X)
      (iY : Spec B ⟶ Y) (iS : Spec R ⟶ S) (e₁ e₂), IsOpenImmersion iX -> IsOpenImmersion iY ->
      IsOpenImmersion iS -> IsEmbedding (L ∘ pullback.map f' g' f g iX iY iS e₁ e₂) := by
    intro R A B f' g' iX iY iS e₁ e₂ _ _ _
    have H : SurjectiveOnStalks g' :=
      have : SurjectiveOnStalks (g' ≫ iS) := e₂ ▸ inferInstance
      .of_comp _ iS
    obtain ⟨φ, rfl⟩ : exists φ, Spec.map φ = f' := ⟨_, Spec.map_preimage _⟩
    obtain ⟨ψ, rfl⟩ : exists ψ, Spec.map ψ = g' := ⟨_, Spec.map_preimage _⟩
    algebraize [φ.hom, ψ.hom]
    rw [HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)] at H
    convert!
      ((iX.isOpenEmbedding.prodMap iY.isOpenEmbedding).isEmbedding.comp
            (PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks R A B H)).comp
        (Scheme.homeoOfIso (pullbackSpecIso R A B)).isEmbedding
    ext1 x
    obtain ⟨x, rfl⟩ := (Scheme.homeoOfIso (pullbackSpecIso R A B).symm).surjective x
    simp only [Scheme.homeoOfIso_apply, Function.comp_apply]
    ext
    · simp only [L, ← Scheme.Hom.comp_apply, pullback.lift_fst, Iso.symm_hom,
        Iso.inv_hom_id]
      erw [← Scheme.Hom.comp_apply, pullbackSpecIso_inv_fst_assoc]
      rfl
    · simp only [L, ← Scheme.Hom.comp_apply, pullback.lift_snd, Iso.symm_hom,
        Iso.inv_hom_id]
      erw [← Scheme.Hom.comp_apply, pullbackSpecIso_inv_snd_assoc]
      rfl
  let 𝒰 := S.affineOpenCover.openCover
  let 𝒱 (i) := ((𝒰.pullback₁ f).X i).affineOpenCover.openCover
  let 𝒲 (i) := ((𝒰.pullback₁ g).X i).affineOpenCover.openCover
  let U (ijk : Σ i, (𝒱 i).I₀ × (𝒲 i).I₀) : TopologicalSpace.Opens (X.carrier × Y) :=
    ⟨{ P | P.1 in ((𝒱 ijk.1).f ijk.2.1 ≫ (𝒰.pullback₁ f).f ijk.1).opensRange ∧
          P.2 in ((𝒲 ijk.1).f ijk.2.2 ≫ (𝒰.pullback₁ g).f ijk.1).opensRange },
      (continuous_fst.1 _ ((𝒱 ijk.1).f ijk.2.1 ≫
      (𝒰.pullback₁ f).f ijk.1).opensRange.2).inter (continuous_snd.1 _
      ((𝒲 ijk.1).f ijk.2.2 ≫ (𝒰.pullback₁ g).f ijk.1).opensRange.2)⟩
  have : Set.range L subseteq (iSup U :) := by
    simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_I₀, PreZeroHypercover.pullback₁_X, Set.range_subset_iff]
    intro z
    simp only [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup, Sigma.exists, Prod.exists]
    obtain ⟨is, s, hsx⟩ := 𝒰.exists_eq (f (pullback.fst f g z))
    have hsy : 𝒰.f is s = g (pullback.snd f g z) := by
      rwa [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    obtain ⟨x : (𝒰.pullback₁ f).X is, hx⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hsx.symm
    obtain ⟨y : (𝒰.pullback₁ g).X is, hy⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hsy.symm
    obtain ⟨ix, x, rfl⟩ := (𝒱 is).exists_eq x
    obtain ⟨iy, y, rfl⟩ := (𝒲 is).exists_eq y
    refine ⟨is, ix, iy, ⟨x, hx⟩, ⟨y, hy⟩⟩
  let 𝓤 := (Scheme.Pullback.openCoverOfBase 𝒰 f g).bind
    (fun i => Scheme.Pullback.openCoverOfLeftRight (𝒱 i) (𝒲 i) _ _)
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range _ ?_ U this _ (𝓤.f ·)
    (fun i => (𝓤.f i).continuous) ?_ ?_
  · fun_prop
  · rintro i x ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    obtain ⟨x₁', hx₁'⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hx₁.symm
    obtain ⟨x₂', hx₂'⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hx₂.symm
    obtain ⟨z, hz⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ (hx₁'.trans hx₂'.symm)
    refine ⟨(pullbackFstFstIso _ _ _ _ _ _ (𝒰.f i.1) ?_ ?_).hom z, ?_⟩
    · simp [pullback.condition]
    · simp [pullback.condition]
    · dsimp only
      rw [← hx₁']; rw [← hz]; rw [← Scheme.Hom.comp_apply]
      erw [← Scheme.Hom.comp_apply]
      congr 5
      apply pullback.hom_ext <;> simp [𝓤, ← pullback.condition, ← pullback.condition_assoc]
  · intro i
    have := H (S.affineOpenCover.X i.1) (((𝒰.pullback₁ f).X i.1).affineOpenCover.X i.2.1)
        (((𝒰.pullback₁ g).X i.1).affineOpenCover.X i.2.2)
        ((𝒱 i.1).f i.2.1 ≫ 𝒰.pullbackHom f i.1)
        ((𝒲 i.1).f i.2.2 ≫ 𝒰.pullbackHom g i.1)
        ((𝒱 i.1).f i.2.1 ≫ (𝒰.pullback₁ f).f i.1)
        ((𝒲 i.1).f i.2.2 ≫ (𝒰.pullback₁ g).f i.1)
        (𝒰.f i.1) (by simp [pullback.condition]) (by simp [pullback.condition])
        inferInstance inferInstance inferInstance
    convert! this using 7
    apply pullback.hom_ext <;>
      simp [𝓤, Scheme.Cover.pullbackHom]

中文:
引理 isEmbedding_pullback
  条件: {X Y S : 概形.{u}} (f : X ⟶ S) (g : Y ⟶ S) [SurjectiveOnStalks g]
  证明: by
  let L := (fun x => (pullback.fst f g x, pullback.snd f g x))
  have H : forall R A B (f' : Spec A ⟶ Spec R) (g' : Spec B ⟶ Spec R) (iX : Spec A ⟶ X)
      (iY : Spec B ⟶ Y) (iS : Spec R ⟶ S) (e₁ e₂), IsOpenImmersion iX -> IsOpenImmersion iY ->
      IsOpenImmersion iS -> IsEmbedding (L ∘ pullback.map f' g' f g iX iY iS e₁ e₂) := by
    intro R A B f' g' iX iY iS e₁ e₂ _ _ _
    have H : SurjectiveOnStalks g' :=
      have : SurjectiveOnStalks (g' ≫ iS) := e₂ ▸ inferInstance
      .of_comp _ iS
    obtain ⟨φ, rfl⟩ : exists φ, Spec.map φ = f' := ⟨_, Spec.map_preimage _⟩
    obtain ⟨ψ, rfl⟩ : exists ψ, Spec.map ψ = g' := ⟨_, Spec.map_preimage _⟩
    algebraize [φ.hom, ψ.hom]
    rw [HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)] at H
    convert!
      ((iX.isOpenEmbedding.prodMap iY.isOpenEmbedding).isEmbedding.comp
            (PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks R A B H)).comp
        (Scheme.homeoOfIso (pullbackSpecIso R A B)).isEmbedding
    ext1 x
    obtain ⟨x, rfl⟩ := (Scheme.homeoOfIso (pullbackSpecIso R A B).symm).surjective x
    simp only [Scheme.homeoOfIso_apply, Function.comp_apply]
    ext
    · simp only [L, ← Scheme.Hom.comp_apply, pullback.lift_fst, Iso.symm_hom,
        Iso.inv_hom_id]
      erw [← Scheme.Hom.comp_apply, pullbackSpecIso_inv_fst_assoc]
      rfl
    · simp only [L, ← Scheme.Hom.comp_apply, pullback.lift_snd, Iso.symm_hom,
        Iso.inv_hom_id]
      erw [← Scheme.Hom.comp_apply, pullbackSpecIso_inv_snd_assoc]
      rfl
  let 𝒰 := S.affineOpenCover.openCover
  let 𝒱 (i) := ((𝒰.pullback₁ f).X i).affineOpenCover.openCover
  let 𝒲 (i) := ((𝒰.pullback₁ g).X i).affineOpenCover.openCover
  let U (ijk : Σ i, (𝒱 i).I₀ × (𝒲 i).I₀) : TopologicalSpace.Opens (X.carrier × Y) :=
    ⟨{ P | P.1 in ((𝒱 ijk.1).f ijk.2.1 ≫ (𝒰.pullback₁ f).f ijk.1).opensRange ∧
          P.2 in ((𝒲 ijk.1).f ijk.2.2 ≫ (𝒰.pullback₁ g).f ijk.1).opensRange },
      (continuous_fst.1 _ ((𝒱 ijk.1).f ijk.2.1 ≫
      (𝒰.pullback₁ f).f ijk.1).opensRange.2).inter (continuous_snd.1 _
      ((𝒲 ijk.1).f ijk.2.2 ≫ (𝒰.pullback₁ g).f ijk.1).opensRange.2)⟩
  have : Set.range L subseteq (iSup U :) := by
    simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_I₀, PreZeroHypercover.pullback₁_X, Set.range_subset_iff]
    intro z
    simp only [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup, Sigma.exists, Prod.exists]
    obtain ⟨is, s, hsx⟩ := 𝒰.exists_eq (f (pullback.fst f g z))
    have hsy : 𝒰.f is s = g (pullback.snd f g z) := by
      rwa [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    obtain ⟨x : (𝒰.pullback₁ f).X is, hx⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hsx.symm
    obtain ⟨y : (𝒰.pullback₁ g).X is, hy⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hsy.symm
    obtain ⟨ix, x, rfl⟩ := (𝒱 is).exists_eq x
    obtain ⟨iy, y, rfl⟩ := (𝒲 is).exists_eq y
    refine ⟨is, ix, iy, ⟨x, hx⟩, ⟨y, hy⟩⟩
  let 𝓤 := (Scheme.Pullback.openCoverOfBase 𝒰 f g).bind
    (fun i => Scheme.Pullback.openCoverOfLeftRight (𝒱 i) (𝒲 i) _ _)
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range _ ?_ U this _ (𝓤.f ·)
    (fun i => (𝓤.f i).continuous) ?_ ?_
  · fun_prop
  · rintro i x ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    obtain ⟨x₁', hx₁'⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hx₁.symm
    obtain ⟨x₂', hx₂'⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hx₂.symm
    obtain ⟨z, hz⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ (hx₁'.trans hx₂'.symm)
    refine ⟨(pullbackFstFstIso _ _ _ _ _ _ (𝒰.f i.1) ?_ ?_).hom z, ?_⟩
    · simp [pullback.condition]
    · simp [pullback.condition]
    · dsimp only
      rw [← hx₁']; rw [← hz]; rw [← Scheme.Hom.comp_apply]
      erw [← Scheme.Hom.comp_apply]
      congr 5
      apply pullback.hom_ext <;> simp [𝓤, ← pullback.condition, ← pullback.condition_assoc]
  · intro i
    have := H (S.affineOpenCover.X i.1) (((𝒰.pullback₁ f).X i.1).affineOpenCover.X i.2.1)
        (((𝒰.pullback₁ g).X i.1).affineOpenCover.X i.2.2)
        ((𝒱 i.1).f i.2.1 ≫ 𝒰.pullbackHom f i.1)
        ((𝒲 i.1).f i.2.2 ≫ 𝒰.pullbackHom g i.1)
        ((𝒱 i.1).f i.2.1 ≫ (𝒰.pullback₁ f).f i.1)
        ((𝒲 i.1).f i.2.2 ≫ (𝒰.pullback₁ g).f i.1)
        (𝒰.f i.1) (by simp [pullback.condition]) (by simp [pullback.condition])
        inferInstance inferInstance inferInstance
    convert! this using 7
    apply pullback.hom_ext <;>
      simp [𝓤, Scheme.Cover.pullbackHom]

Depends on / 依赖: IsEmbedding, IsOpenImmersion, SurjectiveOnStalks, of_comp, pullback, pullback.fst, pullback.map, pullback.snd
-/
lemma isEmbedding_pullback {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [SurjectiveOnStalks g] :
    IsEmbedding fun x => (pullback.fst f g x, pullback.snd f g x) := by
  let L := (fun x => (pullback.fst f g x, pullback.snd f g x))
  have H : forall R A B (f' : Spec A ⟶ Spec R) (g' : Spec B ⟶ Spec R) (iX : Spec A ⟶ X)
      (iY : Spec B ⟶ Y) (iS : Spec R ⟶ S) (e₁ e₂), IsOpenImmersion iX -> IsOpenImmersion iY ->
      IsOpenImmersion iS -> IsEmbedding (L ∘ pullback.map f' g' f g iX iY iS e₁ e₂) := by
    intro R A B f' g' iX iY iS e₁ e₂ _ _ _
    have H : SurjectiveOnStalks g' :=
      have : SurjectiveOnStalks (g' ≫ iS) := e₂ ▸ inferInstance
      .of_comp _ iS
    obtain ⟨φ, rfl⟩ : exists φ, Spec.map φ = f' := ⟨_, Spec.map_preimage _⟩
    obtain ⟨ψ, rfl⟩ : exists ψ, Spec.map ψ = g' := ⟨_, Spec.map_preimage _⟩
    algebraize [φ.hom, ψ.hom]
    rw [HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)] at H
    convert!
      ((iX.isOpenEmbedding.prodMap iY.isOpenEmbedding).isEmbedding.comp
            (PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks R A B H)).comp
        (Scheme.homeoOfIso (pullbackSpecIso R A B)).isEmbedding
    ext1 x
    obtain ⟨x, rfl⟩ := (Scheme.homeoOfIso (pullbackSpecIso R A B).symm).surjective x
    simp only [Scheme.homeoOfIso_apply, Function.comp_apply]
    ext
    · simp only [L, ← Scheme.Hom.comp_apply, pullback.lift_fst, Iso.symm_hom,
        Iso.inv_hom_id]
      erw [← Scheme.Hom.comp_apply, pullbackSpecIso_inv_fst_assoc]
      rfl
    · simp only [L, ← Scheme.Hom.comp_apply, pullback.lift_snd, Iso.symm_hom,
        Iso.inv_hom_id]
      erw [← Scheme.Hom.comp_apply, pullbackSpecIso_inv_snd_assoc]
      rfl
  let 𝒰 := S.affineOpenCover.openCover
  let 𝒱 (i) := ((𝒰.pullback₁ f).X i).affineOpenCover.openCover
  let 𝒲 (i) := ((𝒰.pullback₁ g).X i).affineOpenCover.openCover
  let U (ijk : Σ i, (𝒱 i).I₀ × (𝒲 i).I₀) : TopologicalSpace.Opens (X.carrier × Y) :=
    ⟨{ P | P.1 in ((𝒱 ijk.1).f ijk.2.1 ≫ (𝒰.pullback₁ f).f ijk.1).opensRange ∧
          P.2 in ((𝒲 ijk.1).f ijk.2.2 ≫ (𝒰.pullback₁ g).f ijk.1).opensRange },
      (continuous_fst.1 _ ((𝒱 ijk.1).f ijk.2.1 ≫
      (𝒰.pullback₁ f).f ijk.1).opensRange.2).inter (continuous_snd.1 _
      ((𝒲 ijk.1).f ijk.2.2 ≫ (𝒰.pullback₁ g).f ijk.1).opensRange.2)⟩
  have : Set.range L subseteq (iSup U :) := by
    simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_I₀, PreZeroHypercover.pullback₁_X, Set.range_subset_iff]
    intro z
    simp only [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup, Sigma.exists, Prod.exists]
    obtain ⟨is, s, hsx⟩ := 𝒰.exists_eq (f (pullback.fst f g z))
    have hsy : 𝒰.f is s = g (pullback.snd f g z) := by
      rwa [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    obtain ⟨x : (𝒰.pullback₁ f).X is, hx⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hsx.symm
    obtain ⟨y : (𝒰.pullback₁ g).X is, hy⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hsy.symm
    obtain ⟨ix, x, rfl⟩ := (𝒱 is).exists_eq x
    obtain ⟨iy, y, rfl⟩ := (𝒲 is).exists_eq y
    refine ⟨is, ix, iy, ⟨x, hx⟩, ⟨y, hy⟩⟩
  let 𝓤 := (Scheme.Pullback.openCoverOfBase 𝒰 f g).bind
    (fun i => Scheme.Pullback.openCoverOfLeftRight (𝒱 i) (𝒲 i) _ _)
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range _ ?_ U this _ (𝓤.f ·)
    (fun i => (𝓤.f i).continuous) ?_ ?_
  · fun_prop
  · rintro i x ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    obtain ⟨x₁', hx₁'⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hx₁.symm
    obtain ⟨x₂', hx₂'⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hx₂.symm
    obtain ⟨z, hz⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ (hx₁'.trans hx₂'.symm)
    refine ⟨(pullbackFstFstIso _ _ _ _ _ _ (𝒰.f i.1) ?_ ?_).hom z, ?_⟩
    · simp [pullback.condition]
    · simp [pullback.condition]
    · dsimp only
      rw [← hx₁']; rw [← hz]; rw [← Scheme.Hom.comp_apply]
      erw [← Scheme.Hom.comp_apply]
      congr 5
      apply pullback.hom_ext <;> simp [𝓤, ← pullback.condition, ← pullback.condition_assoc]
  · intro i
    have := H (S.affineOpenCover.X i.1) (((𝒰.pullback₁ f).X i.1).affineOpenCover.X i.2.1)
        (((𝒰.pullback₁ g).X i.1).affineOpenCover.X i.2.2)
        ((𝒱 i.1).f i.2.1 ≫ 𝒰.pullbackHom f i.1)
        ((𝒲 i.1).f i.2.2 ≫ 𝒰.pullbackHom g i.1)
        ((𝒱 i.1).f i.2.1 ≫ (𝒰.pullback₁ f).f i.1)
        ((𝒲 i.1).f i.2.2 ≫ (𝒰.pullback₁ g).f i.1)
        (𝒰.f i.1) (by simp [pullback.condition]) (by simp [pullback.condition])
        inferInstance inferInstance inferInstance
    convert! this using 7
    apply pullback.hom_ext <;>
      simp [𝓤, Scheme.Cover.pullbackHom]

end SurjectiveOnStalks

end AlgebraicGeometry
