/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer

/-!

# Separated morphisms

A morphism of schemes is separated if its diagonal morphism is a closed immersion.

## Main definitions
- `AlgebraicGeometry.IsSeparated`: The class of separated morphisms.
- `AlgebraicGeometry.Scheme.IsSeparated`: The class of separated schemes.
- `AlgebraicGeometry.IsSeparated.hasAffineProperty`:
  A morphism is separated iff the preimage of affine opens are separated schemes.
-/

public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is separated if the diagonal map is a closed immersion. -/
@[mk_iff]
/--
Definition of `IsSeparated` / `IsSeparated` 的定义

English:
class IsSeparated
  parameters: : Prop where
  axioms and operations (1):
    - isClosedImmersion_diagonal : IsClosedImmersion (pullback.diagonal f)  [default: by infer_instance]

中文:
类 IsSeparated
  参数: : 命题 where
  公理与运算 (1 个):
    - isClosedImmersion_diagonal : IsClosedImmersion (pullback.diagonal f)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsSeparated : Prop where
  /-- A morphism is separated if the diagonal map is a closed immersion. -/
  isClosedImmersion_diagonal : IsClosedImmersion (pullback.diagonal f) := by infer_instance

@[deprecated (since := "2026-01-20")]
alias IsSeparated.diagonal_isClosedImmersion := IsSeparated.isClosedImmersion_diagonal

namespace IsSeparated

attribute [instance] diagonal_isClosedImmersion

/--
theorem `isSeparated_eq_diagonal_isClosedImmersion` / 定理 `isSeparated_eq_diagonal_isClosedImmersion`

English:
theorem isSeparated_eq_diagonal_isClosedImmersion
  proof: by
  ext
  exact isSeparated_iff _

中文:
定理 isSeparated_eq_diagonal_isClosedImmersion
  证明: by
  ext
  exact isSeparated_iff _

Depends on / 依赖: isSeparated_iff
-/
theorem isSeparated_eq_diagonal_isClosedImmersion :
    @IsSeparated = MorphismProperty.diagonal @IsClosedImmersion := by
  ext
  exact isSeparated_iff _

/-- Monomorphisms are separated. -/
instance (priority := 900) isSeparated_of_mono [Mono f] : IsSeparated f where

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.RespectsIso @IsSeparated
  body: by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

中文:
实例 :
  签名: Morphism命题erty.RespectsIso @IsSeparated
  定义体: by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

Depends on / 依赖: infer_instance, isSeparated_eq_diagonal_isClosedImmersion
-/
instance : MorphismProperty.RespectsIso @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

instance (priority := 900) [IsSeparated f] : QuasiSeparated f where

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `stableUnderComposition` / 实例 `stableUnderComposition`

English:
instance stableUnderComposition
  signature: : MorphismProperty.IsStableUnderComposition @IsSeparated
  body: by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

中文:
实例 stableUnderComposition
  签名: : Morphism命题erty.IsStableUnderComposition @IsSeparated
  定义体: by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

Depends on / 依赖: infer_instance, isSeparated_eq_diagonal_isClosedImmersion
-/
instance stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSeparated
  signature: f] [IsSeparated g] : IsSeparated (f ≫ g)
  body: stableUnderComposition.comp_mem f g inferInstance inferInstance

中文:
实例 [IsSeparated
  签名: f] [IsSeparated g] : IsSeparated (f ≫ g)
  定义体: stableUnderComposition.comp_mem f g inferInstance inferInstance

Depends on / 依赖: comp_mem, stableUnderComposition, stableUnderComposition.comp_mem
-/
instance [IsSeparated f] [IsSeparated g] : IsSeparated (f ≫ g) :=
  stableUnderComposition.comp_mem f g inferInstance inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @IsSeparated
  body: inferInstance

中文:
实例 :
  签名: Morphism命题erty.IsMultiplicative @IsSeparated
  定义体: inferInstance
-/
instance : MorphismProperty.IsMultiplicative @IsSeparated where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isStableUnderBaseChange` / 实例 `isStableUnderBaseChange`

English:
instance isStableUnderBaseChange
  signature: : MorphismProperty.IsStableUnderBaseChange @IsSeparated
  body: by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

中文:
实例 isStableUnderBaseChange
  签名: : Morphism命题erty.IsStableUnderBaseChange @IsSeparated
  定义体: by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

Depends on / 依赖: infer_instance, isSeparated_eq_diagonal_isClosedImmersion
-/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtTarget @IsSeparated
  body: by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

中文:
实例 :
  签名: IsZariskiLocalAtTarget @IsSeparated
  定义体: by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

Depends on / 依赖: infer_instance, isSeparated_eq_diagonal_isClosedImmersion
-/
instance : IsZariskiLocalAtTarget @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated g] :
    IsSeparated (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f] :
    IsSeparated (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [IsSeparated f] : IsSeparated (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [IsSeparated f] :
    IsSeparated (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

instance (R S : CommRingCat.{u}) (f : R ⟶ S) : IsSeparated (Spec.map f) := by
  constructor
  let := f.hom.toAlgebra
  change IsClosedImmersion
    (Limits.pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  rw [diagonal_SpecMap]; rw [MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
  exact .spec_of_surjective _ fun x => ⟨.tmul R 1 x,
    (Algebra.TensorProduct.lmul'_apply_tmul (R := R) (S := S) 1 x).trans (one_mul x)⟩

set_option backward.isDefEq.respectTransparency.types false in
@[instance 100]
/--
lemma `of_isAffineHom` / 引理 `of_isAffineHom`

English:
lemma of_isAffineHom
  given: [h : IsAffineHom f]
  statement: IsSeparated f
  proof: by
  wlog hY : IsAffine Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : IsAffineHom (f ∣_ U) := IsZariskiLocalAtTarget.restrict h U
    exact this _ U.2
  have : IsAffine X := HasAffineProperty.iff_of_isAffine.mp h

中文:
引理 of_isAffineHom
  条件: [h : IsAffineHom f]
  结论: IsSeparated f
  证明: by
  wlog hY : IsAffine Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : IsAffineHom (f ∣_ U) := IsZariskiLocalAtTarget.restrict h U
    exact this _ U.2
  have : IsAffine X := HasAffineProperty.iff_of_isAffine.mp h

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine.mp, IsAffine, IsAffineHom, IsSeparated, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_iSup_eq_top, IsZariskiLocalAtTarget.restrict, MorphismProperty, MorphismProperty.arrow_mk_iso_iff, arrow_mk_iso_iff, iSup_affineOpens_eq_top, iff_of_iSup_eq_top, iff_of_isAffine, infer_instance, restrict
-/
lemma of_isAffineHom [h : IsAffineHom f] : IsSeparated f := by
  wlog hY : IsAffine Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : IsAffineHom (f ∣_ U) := IsZariskiLocalAtTarget.restrict h U
    exact this _ U.2
  have : IsAffine X := HasAffineProperty.iff_of_isAffine.mp h
  rw [MorphismProperty.arrow_mk_iso_iff @IsSeparated (arrowIsoSpecΓOfIsAffine f)]
  infer_instance

instance {S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [IsSeparated i] :
    IsClosedImmersion (pullback.mapDesc f g i) :=
  MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f g i)
    inferInstance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSeparated
  signature: g] :
  body: by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.fst f (𝟙 Y))]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (pullback.congrHom rfl (Category.id_comp g)).inv]
  convert (inferInstance : IsClosedImmersion (pullback.mapDesc f (𝟙 _) g))

中文:
实例 [IsSeparated
  签名: g] :
  定义体: by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.fst f (𝟙 Y))]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (pullback.congrHom rfl (Category.id_comp g)).inv]
  convert (inferInstance : IsClosedImmersion (pullback.mapDesc f (𝟙 _) g))

Depends on / 依赖: Category, Category.id_comp, IsClosedImmersion, MorphismProperty, MorphismProperty.cancel_left_of_respectsIso, MorphismProperty.cancel_right_of_respectsIso, cancel_left_of_respectsIso, cancel_right_of_respectsIso, condition, congrHom, convert, id_comp, mapDesc, pullback, pullback.condition, pullback.congrHom, pullback.fst, pullback.mapDesc
-/
instance [IsSeparated g] :
    IsClosedImmersion (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ g))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.fst f (𝟙 Y))]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (pullback.congrHom rfl (Category.id_comp g)).inv]
  convert (inferInstance : IsClosedImmersion (pullback.mapDesc f (𝟙 _) g))
  ext : 1 <;> simp [pullback.condition]

end IsSeparated

section of_injective

open Scheme Pullback

variable (𝒰 : Y.OpenCover) (𝒱 : forall i, (pullback f (𝒰.f i)).OpenCover)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Scheme.Pullback.diagonalCoverDiagonalRange_eq_top_of_injective` / 引理 `Scheme.Pullback.diagonalCoverDiagonalRange_eq_top_of_injective`

English:
lemma Scheme.Pullback.diagonalCoverDiagonalRange_eq_top_of_injective
  proof: by
  rw [← top_le_iff]
  rintro x -
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_I₀, openCoverOfBase_X,
    openCoverOfLeftRight_I₀, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.coe_opensRange, Opens.mem_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  have H : pullback.fst f f x = pul

中文:
引理 Scheme.Pullback.diagonalCoverDiagonalRange_eq_top_of_injective
  证明: by
  rw [← top_le_iff]
  rintro x -
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_I₀, openCoverOfBase_X,
    openCoverOfLeftRight_I₀, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.coe_opensRange, Opens.mem_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  have H : pullback.fst f f x = pul

Depends on / 依赖: Hom.coe_opensRange, Opens.carrier_eq_coe, Opens.iSup_mk, Opens.mem_mk, Scheme, Scheme.Hom.comp_apply, Set.mem_iUnion, Set.mem_range, Sigma.exists, carrier_eq_coe, coe_opensRange, comp_apply, condition, covers, diagonalCoverDiagonalRange, iSup_mk, mem_iUnion, mem_mk, mem_range, openCoverOfBase_X
-/
lemma Scheme.Pullback.diagonalCoverDiagonalRange_eq_top_of_injective
    (hf : Function.Injective f) :
    diagonalCoverDiagonalRange f 𝒰 𝒱 = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_I₀, openCoverOfBase_X,
    openCoverOfLeftRight_I₀, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.coe_opensRange, Opens.mem_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  have H : pullback.fst f f x = pullback.snd f f x :=
    hf (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
  let i := 𝒰.idx (f (pullback.fst f f x))
  obtain ⟨y : 𝒰.X i, hy : 𝒰.f i y = f _⟩ :=
    𝒰.covers (f (pullback.fst f f x))
  obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_pullback _ _ hy.symm
  let j := (𝒱 i).idx z
  obtain ⟨w : (𝒱 i).X j, hy : (𝒱 i).f j w = z⟩ := (𝒱 i).covers z
  refine ⟨i, j, ?_⟩
  simp_rw [diagonalCover_map]
  change x in Set.range _
  simp only [diagonalCover, openCoverOfBase_I₀,
    Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
    Precoverage.ZeroHypercover.bind_toPreZeroHypercover, openCoverOfBase_X,
    PreZeroHypercover.bind_X, openCoverOfLeftRight_I₀, openCoverOfLeftRight_X]
  rw [range_map]
  simp [← H, ← hz₁, ← hy]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange` / 引理 `Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange`

English:
lemma Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange
  proof: by
  rintro _ ⟨x, rfl⟩
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_I₀, openCoverOfBase_X,
    openCoverOfLeftRight_I₀, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.coe_opensRange, Opens.coe_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  let i := 𝒰.idx (f x)
  obtain ⟨y : 𝒰.X i, hy :

中文:
引理 Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange
  证明: by
  rintro _ ⟨x, rfl⟩
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_I₀, openCoverOfBase_X,
    openCoverOfLeftRight_I₀, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.coe_opensRange, Opens.coe_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  let i := 𝒰.idx (f x)
  obtain ⟨y : 𝒰.X i, hy :

Depends on / 依赖: Hom.coe_opensRange, Opens.carrier_eq_coe, Opens.coe_mk, Opens.iSup_mk, Set.mem_iUnion, Set.mem_range, Sigma.exists, carrier_eq_coe, coe_mk, coe_opensRange, covers, diagonal, diagonalCoverDiagonalRange, exists_preimage_pullback, hy.symm, iSup_mk, mem_iUnion, mem_range, openCoverOfBase_X, pullback
-/
lemma Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange :
    Set.range (pullback.diagonal f) subseteq diagonalCoverDiagonalRange f 𝒰 𝒱 := by
  rintro _ ⟨x, rfl⟩
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_I₀, openCoverOfBase_X,
    openCoverOfLeftRight_I₀, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.coe_opensRange, Opens.coe_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  let i := 𝒰.idx (f x)
  obtain ⟨y : 𝒰.X i, hy : 𝒰.f i y = f x⟩ := 𝒰.covers (f x)
  obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_pullback _ _ hy.symm
  let j := (𝒱 i).idx z
  obtain ⟨w : (𝒱 i).X j, hy : (𝒱 i).f j w = z⟩ := (𝒱 i).covers z
  refine ⟨i, j, pullback.diagonal ((𝒱 i).f j ≫ pullback.snd f (𝒰.f i)) w, ?_⟩
  rw [← hz₁]; rw [← hy]; rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]
  simp only [diagonalCover, openCoverOfBase_I₀,
    Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
    Cover.pullbackHom, Precoverage.ZeroHypercover.bind_toPreZeroHypercover, openCoverOfBase_X,
    PreZeroHypercover.bind_X, openCoverOfLeftRight_I₀, openCoverOfLeftRight_X,
    PreZeroHypercover.bind_f, openCoverOfLeftRight_f, openCoverOfBase_f, Hom.comp_base,
    TopCat.hom_comp, ContinuousMap.comp_apply, ContinuousMap.comp_assoc]
  simp_rw [← Scheme.Hom.comp_apply]
  congr 5
  apply pullback.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange` / 引理 `isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange`

English:
lemma isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange
  proof: by
  let U : (Σ i, (𝒱 i).I₀) -> (diagonalCoverDiagonalRange f 𝒰 𝒱).toScheme.Opens := fun i =>
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ⁻¹ᵁ ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange
  have hU (i) : (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ''ᵁ U i =
      ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2

中文:
引理 isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange
  证明: by
  let U : (Σ i, (𝒱 i).I₀) -> (diagonalCoverDiagonalRange f 𝒰 𝒱).toScheme.Opens := fun i =>
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ⁻¹ᵁ ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange
  have hU (i) : (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ''ᵁ U i =
      ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2

Depends on / 依赖: Opens.opensRange_, Scheme, Scheme.Hom.image_preimage_eq_opensRange_inf, diagonalCover, diagonalCoverDiagonalRange, image_preimage_eq_opensRange_inf, inf_eq_right, le_iSup, opensRange, toScheme, toScheme.Opens
-/
lemma isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange
    [forall i, IsAffine (𝒰.X i)] [forall i j, IsAffine ((𝒱 i).X j)] :
    IsClosedImmersion (pullback.diagonal f ∣_ diagonalCoverDiagonalRange f 𝒰 𝒱) := by
  let U : (Σ i, (𝒱 i).I₀) -> (diagonalCoverDiagonalRange f 𝒰 𝒱).toScheme.Opens := fun i =>
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ⁻¹ᵁ ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange
  have hU (i) : (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ''ᵁ U i =
      ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; rw [inf_eq_right]; rw [Opens.opensRange_ι]
    exact le_iSup (fun i : Σ i, (𝒱 i).I₀ => ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange) i
  have hf : iSup U = ⊤ := (TopologicalSpace.Opens.map_iSup _ _).symm.trans
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι_preimage_self
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _ hf]
  intro i
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictRestrict _ _ _)]; rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictEq _ (hU i))]; rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (diagonalRestrictIsoDiagonal ..)]
  infer_instance

@[stacks 0DVA]
/--
lemma `isSeparated_of_injective` / 引理 `isSeparated_of_injective`

English:
lemma isSeparated_of_injective
  given: (hf : Function.Injective f)
  proof: by
  constructor
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.f i)).affineCover
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i : PUnit.{0} => ⊤) (by simp) fun _ => ?_
  rw [← diagonalCoverDiagonalRange_eq_top_of_injective f 𝒰 𝒱 hf]
  exact isClosedImmersion_diagonal_restrict_diagona

中文:
引理 isSeparated_of_injective
  条件: (hf : Function.Injective f)
  证明: by
  constructor
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.f i)).affineCover
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i : PUnit.{0} => ⊤) (by simp) fun _ => ?_
  rw [← diagonalCoverDiagonalRange_eq_top_of_injective f 𝒰 𝒱 hf]
  exact isClosedImmersion_diagonal_restrict_diagona

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.of_iSup_eq_top, Y.affineCover, affineCover, diagonalCoverDiagonalRange_eq_top_of_injective, isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange, of_iSup_eq_top, pullback
-/
lemma isSeparated_of_injective (hf : Function.Injective f) :
    IsSeparated f := by
  constructor
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.f i)).affineCover
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i : PUnit.{0} => ⊤) (by simp) fun _ => ?_
  rw [← diagonalCoverDiagonalRange_eq_top_of_injective f 𝒰 𝒱 hf]
  exact isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange f 𝒰 𝒱

end of_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @IsClosedImmersion @IsSeparated
  body: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsClosedImmersion _)

中文:
实例 :
  签名: Morphism命题erty.HasOfPostcomp命题erty @IsClosedImmersion @IsSeparated
  定义体: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsClosedImmersion _)

Depends on / 依赖: IsClosedImmersion, MorphismProperty, MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr, hasOfPostcompProperty_iff_le_diagonal
-/
instance : MorphismProperty.HasOfPostcompProperty @IsClosedImmersion @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsClosedImmersion _)

/--
lemma `IsClosedImmersion.of_comp` / 引理 `IsClosedImmersion.of_comp`

English:
lemma IsClosedImmersion.of_comp
  given: [IsClosedImmersion (f ≫ g)] [IsSeparated g]
  proof: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

中文:
引理 IsClosedImmersion.of_comp
  条件: [IsClosedImmersion (f ≫ g)] [IsSeparated g]
  证明: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

Depends on / 依赖: MorphismProperty, MorphismProperty.of_postcomp, of_postcomp
-/
lemma IsClosedImmersion.of_comp [IsClosedImmersion (f ≫ g)] [IsSeparated g] :
    IsClosedImmersion f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

variable {f g} in
/--
lemma `IsClosedImmersion.comp_iff` / 引理 `IsClosedImmersion.comp_iff`

English:
lemma IsClosedImmersion.comp_iff
  given: [IsClosedImmersion g]
  proof: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

中文:
引理 IsClosedImmersion.comp_iff
  条件: [IsClosedImmersion g]
  证明: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

Depends on / 依赖: of_comp
-/
lemma IsClosedImmersion.comp_iff [IsClosedImmersion g] :
    IsClosedImmersion (f ≫ g) ↔ IsClosedImmersion f :=
  ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

instance {I J : X.IdealSheafData} (h : I <= J) : IsClosedImmersion (I.inclusion h) := by
  have : IsClosedImmersion (I.inclusion h ≫ I.subschemeι) := by
    simp only [Scheme.IdealSheafData.inclusion_subschemeι]
    infer_instance
  exact .of_comp _ I.subschemeι

/--
lemma `IsSeparated.of_comp` / 引理 `IsSeparated.of_comp`

English:
lemma IsSeparated.of_comp
  given: [IsSeparated (f ≫ g)]
  statement: IsSeparated f
  proof: by
  have : IsClosedImmersion (pullback.diagonal (f ≫ g)) := inferInstance
  rw [pullback.diagonal_comp] at this
  exact ⟨@IsClosedImmersion.of_comp _ _ _ _ _ this inferInstance⟩

中文:
引理 IsSeparated.of_comp
  条件: [IsSeparated (f ≫ g)]
  结论: IsSeparated f
  证明: by
  have : IsClosedImmersion (pullback.diagonal (f ≫ g)) := inferInstance
  rw [pullback.diagonal_comp] at this
  exact ⟨@IsClosedImmersion.of_comp _ _ _ _ _ this inferInstance⟩

Depends on / 依赖: IsClosedImmersion, IsClosedImmersion.of_comp, diagonal, diagonal_comp, of_comp, pullback, pullback.diagonal, pullback.diagonal_comp
-/
lemma IsSeparated.of_comp [IsSeparated (f ≫ g)] : IsSeparated f := by
  have : IsClosedImmersion (pullback.diagonal (f ≫ g)) := inferInstance
  rw [pullback.diagonal_comp] at this
  exact ⟨@IsClosedImmersion.of_comp _ _ _ _ _ this inferInstance⟩

variable {f g} in
/--
lemma `IsSeparated.comp_iff` / 引理 `IsSeparated.comp_iff`

English:
lemma IsSeparated.comp_iff
  given: [IsSeparated g]
  statement: IsSeparated (f ≫ g) ↔ IsSeparated f
  proof: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

中文:
引理 IsSeparated.comp_iff
  条件: [IsSeparated g]
  结论: IsSeparated (f ≫ g) ↔ IsSeparated f
  证明: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

Depends on / 依赖: of_comp
-/
lemma IsSeparated.comp_iff [IsSeparated g] : IsSeparated (f ≫ g) ↔ IsSeparated f :=
  ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @IsSeparated ⊤
  body: .of_comp f g

中文:
实例 :
  签名: Morphism命题erty.HasOfPostcomp命题erty @IsSeparated ⊤
  定义体: .of_comp f g

Depends on / 依赖: of_comp
-/
instance : MorphismProperty.HasOfPostcompProperty @IsSeparated ⊤ where
  of_postcomp f g _ _ := .of_comp f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @IsAffineHom @IsSeparated
  body: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsAffineHom _)

中文:
实例 :
  签名: Morphism命题erty.HasOfPostcomp命题erty @IsAffineHom @IsSeparated
  定义体: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsAffineHom _)

Depends on / 依赖: IsAffineHom, MorphismProperty, MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr, hasOfPostcompProperty_iff_le_diagonal
-/
instance : MorphismProperty.HasOfPostcompProperty @IsAffineHom @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsAffineHom _)

/--
lemma `IsAffineHom.of_comp` / 引理 `IsAffineHom.of_comp`

English:
lemma IsAffineHom.of_comp
  given: [IsAffineHom (f ≫ g)] [IsSeparated g]
  proof: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

中文:
引理 IsAffineHom.of_comp
  条件: [IsAffineHom (f ≫ g)] [IsSeparated g]
  证明: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

Depends on / 依赖: MorphismProperty, MorphismProperty.of_postcomp, of_postcomp
-/
lemma IsAffineHom.of_comp [IsAffineHom (f ≫ g)] [IsSeparated g] :
    IsAffineHom f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

variable {f g} in
/--
lemma `IsAffineHom.comp_iff` / 引理 `IsAffineHom.comp_iff`

English:
lemma IsAffineHom.comp_iff
  given: [IsAffineHom g]
  statement: IsAffineHom (f ≫ g) ↔ IsAffineHom f
  proof: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

中文:
引理 IsAffineHom.comp_iff
  条件: [IsAffineHom g]
  结论: IsAffineHom (f ≫ g) ↔ IsAffineHom f
  证明: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

Depends on / 依赖: of_comp
-/
lemma IsAffineHom.comp_iff [IsAffineHom g] : IsAffineHom (f ≫ g) ↔ IsAffineHom f :=
  ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
@[stacks 01KM]
/--
Instance `isClosedImmersion_equalizer_ι_left` / 实例 `isClosedImmersion_equalizer_ι_left`

English:
instance isClosedImmersion_equalizer_ι_left
  signature: {S : Scheme} {X Y : Over S} [IsSeparated Y.hom]
  body: by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsClosedImmersion (pullback.diagonal Y.hom

中文:
实例 isClosedImmersion_equalizer_ι_left
  签名: {S : Scheme} {X Y : Over S} [IsSeparated Y.hom]
  定义体: by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsClosedImmersion (pullback.diagonal Y.hom

Depends on / 依赖: IsClosedImmersion, Limits, Limits.isPullback_equalizer_prod, MorphismProperty, MorphismProperty.cancel_right_of_respectsIso, MorphismProperty.of_isPullback, Over.comp_left, Over.forget, Over.prodLeftIsoPullback, Y.hom, cancel_right_of_respectsIso, comp_left, convert, diagonal, forget, isPullback_equalizer_prod, of_isPullback, prodLeftIsoPullback, pullback, pullback.diagonal
-/
instance isClosedImmersion_equalizer_ι_left {S : Scheme} {X Y : Over S} [IsSeparated Y.hom]
    (f g : X ⟶ Y) : IsClosedImmersion (equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsClosedImmersion (pullback.diagonal Y.hom))
  ext1 <;> simp [← Over.comp_left]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ext_of_isDominant_of_isSeparated` / 引理 `ext_of_isDominant_of_isSeparated`

English:
lemma ext_of_isDominant_of_isSeparated
  statement: [IsReduced X] {f g : X ⟶ Y}
  proof: by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have : IsDominant (equalizer.ι f' g').left := 

中文:
引理 ext_of_isDominant_of_isSeparated
  结论: [IsReduced X] {f g : X ⟶ Y}
  证明: by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have : IsDominant (equalizer.ι f' g').left := 

Depends on / 依赖: IsDominant, IsDominant.of_comp, IsSeparated, Over.comp_left, Over.homMk, Over.mk, Surjective, allowSynthFailures, comp_left, equalizer, equalizer.lift, equalizer.lift_, of_comp, surjective_of_isDominant_of_isClos
-/
lemma ext_of_isDominant_of_isSeparated [IsReduced X] {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have : IsDominant (equalizer.ι f' g').left := by
    apply +allowSynthFailures IsDominant.of_comp (equalizer.lift ι' ?_).left
    · rwa [← Over.comp_left, equalizer.lift_ι]
    · ext1; exact hU
  have : Surjective (equalizer.ι f' g').left :=
    surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range
  have := isIso_of_isClosedImmersion_of_surjective (Y := X) (equalizer.ι f' g').left
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

/--
lemma `ext_of_fromSpecResidueField_eq` / 引理 `ext_of_fromSpecResidueField_eq`

English:
lemma ext_of_fromSpecResidueField_eq
  statement: (f g : X ⟶ Y) (i : Y ⟶ Z) [IsSeparated i] [IsReduced X]
  proof: by
  suffices IsDominant (equalizer.ι f g) from
    ext_of_isDominant_of_isSeparated i H' (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨.mono (fun x hx => ⟨equalizer.lift _ (H _ hx) default, ?_⟩) hS'⟩
  rw [← Scheme.Hom.comp_apply]; rw [equalizer.lift_ι]; rw [Scheme.fromSpecResidueField_appl

中文:
引理 ext_of_fromSpecResidueField_eq
  结论: (f g : X ⟶ Y) (i : Y ⟶ Z) [IsSeparated i] [IsReduced X]
  证明: by
  suffices IsDominant (equalizer.ι f g) from
    ext_of_isDominant_of_isSeparated i H' (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨.mono (fun x hx => ⟨equalizer.lift _ (H _ hx) default, ?_⟩) hS'⟩
  rw [← Scheme.Hom.comp_apply]; rw [equalizer.lift_ι]; rw [Scheme.fromSpecResidueField_appl

Depends on / 依赖: IsDominant, Scheme, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, comp_apply, condition, equalizer, equalizer.condition, equalizer.lift, equalizer.lift_, ext_of_isDominant_of_isSeparated, fromSpecResidueField_apply
-/
lemma ext_of_fromSpecResidueField_eq (f g : X ⟶ Y) (i : Y ⟶ Z) [IsSeparated i] [IsReduced X]
    (S : Set X) (hS' : Dense S)
    (H : forall x in S, X.fromSpecResidueField x ≫ f = X.fromSpecResidueField x ≫ g)
    (H' : f ≫ i = g ≫ i) : f = g := by
  suffices IsDominant (equalizer.ι f g) from
    ext_of_isDominant_of_isSeparated i H' (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨.mono (fun x hx => ⟨equalizer.lift _ (H _ hx) default, ?_⟩) hS'⟩
  rw [← Scheme.Hom.comp_apply]; rw [equalizer.lift_ι]; rw [Scheme.fromSpecResidueField_apply]

variable (S) in
/--
lemma `ext_of_isDominant_of_isSeparated'` / 引理 `ext_of_isDominant_of_isSeparated'`

English:
lemma ext_of_isDominant_of_isSeparated'
  statement: [X.Over S] [Y.Over S] [IsReduced X] [IsSeparated (Y ↘ S)]
  proof: ext_of_isDominant_of_isSeparated (Y ↘ S) (by simp) ι hU

中文:
引理 ext_of_isDominant_of_isSeparated'
  结论: [X.Over S] [Y.Over S] [IsReduced X] [IsSeparated (Y ↘ S)]
  证明: ext_of_isDominant_of_isSeparated (Y ↘ S) (by simp) ι hU

Depends on / 依赖: ext_of_isDominant_of_isSeparated
-/
lemma ext_of_isDominant_of_isSeparated' [X.Over S] [Y.Over S] [IsReduced X] [IsSeparated (Y ↘ S)]
    {f g : X ⟶ Y} [f.IsOver S] [g.IsOver S] {W} (ι : W ⟶ X) [IsDominant ι]
    (hU : ι ≫ f = ι ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated (Y ↘ S) (by simp) ι hU

namespace Scheme

/-- A scheme `X` is separated if it is separated over `⊤_ Scheme`. -/
@[mk_iff]
/--
Definition of `IsSeparated` / `IsSeparated` 的定义

English:
class IsSeparated
  parameters: (X : Scheme.{u})
  axioms and operations (1):
    - isSeparated_terminal_from : IsSeparated (terminal.from X)

中文:
类 IsSeparated
  参数: (X : Scheme.{u})
  公理与运算 (1 个):
    - isSeparated_terminal_from : IsSeparated (terminal.from X)
-/
protected class IsSeparated (X : Scheme.{u}) : Prop where
  isSeparated_terminal_from : IsSeparated (terminal.from X)

attribute [instance] IsSeparated.isSeparated_terminal_from

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isSeparated_iff_isClosedImmersion_prod_lift` / 引理 `isSeparated_iff_isClosedImmersion_prod_lift`

English:
lemma isSeparated_iff_isClosedImmersion_prod_lift
  given: {X : Scheme.{u}}
  proof: by
  rw [isSeparated_iff]; rw [AlgebraicGeometry.isSeparated_iff]; rw [iff_iff_eq]; rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ (prodIsoPullback X X).hom]
  congr
  ext : 1 <;> simp

中文:
引理 isSeparated_iff_isClosedImmersion_prod_lift
  条件: {X : Scheme.{u}}
  证明: by
  rw [isSeparated_iff]; rw [AlgebraicGeometry.isSeparated_iff]; rw [iff_iff_eq]; rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ (prodIsoPullback X X).hom]
  congr
  ext : 1 <;> simp

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.isSeparated_iff, IsClosedImmersion, MorphismProperty, MorphismProperty.cancel_right_of_respectsIso, cancel_right_of_respectsIso, iff_iff_eq, isSeparated_iff, prodIsoPullback
-/
lemma isSeparated_iff_isClosedImmersion_prod_lift {X : Scheme.{u}} :
    X.IsSeparated ↔ IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rw [isSeparated_iff]; rw [AlgebraicGeometry.isSeparated_iff]; rw [iff_iff_eq]; rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ (prodIsoPullback X X).hom]
  congr
  ext : 1 <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.IsSeparated]
  signature: : IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X))
  body: by
  rwa [← isSeparated_iff_isClosedImmersion_prod_lift]

中文:
实例 [X.IsSeparated]
  签名: : IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X))
  定义体: by
  rwa [← isSeparated_iff_isClosedImmersion_prod_lift]

Depends on / 依赖: isSeparated_iff_isClosedImmersion_prod_lift
-/
instance [X.IsSeparated] : IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rwa [← isSeparated_iff_isClosedImmersion_prod_lift]

instance (priority := 900) {X : Scheme.{u}} [IsAffine X] : X.IsSeparated := ⟨inferInstance⟩

instance (priority := low) {X : Scheme.{u}} [X.IsSeparated] : QuasiSeparatedSpace X :=
  quasiSeparatedSpace_of_quasiSeparated (terminal.from X)

instance (priority := 900) [X.IsSeparated] : IsSeparated f := by
  apply +allowSynthFailures @IsSeparated.of_comp (g := terminal.from Y)
  rw [terminal.comp_from]
  infer_instance

instance (f g : X ⟶ Y) [Y.IsSeparated] : IsClosedImmersion (Limits.equalizer.ι f g) :=
  MorphismProperty.of_isPullback (isPullback_equalizer_prod f g).flip inferInstance

end Scheme

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `IsSeparated.hasAffineProperty` / 实例 `IsSeparated.hasAffineProperty`

English:
instance IsSeparated.hasAffineProperty
  signature: :
  body: by
  convert! HasAffineProperty.of_isZariskiLocalAtTarget @IsSeparated with X Y f hY
  rw [Scheme.isSeparated_iff]; rw [← terminal.comp_from f]; rw [IsSeparated.comp_iff]
  rfl

中文:
实例 IsSeparated.hasAffineProperty
  签名: :
  定义体: by
  convert! HasAffineProperty.of_isZariskiLocalAtTarget @IsSeparated with X Y f hY
  rw [Scheme.isSeparated_iff]; rw [← terminal.comp_from f]; rw [IsSeparated.comp_iff]
  rfl

Depends on / 依赖: HasAffineProperty, HasAffineProperty.of_isZariskiLocalAtTarget, IsSeparated, IsSeparated.comp_iff, Scheme, Scheme.isSeparated_iff, comp_from, comp_iff, convert, isSeparated_iff, of_isZariskiLocalAtTarget, terminal, terminal.comp_from
-/
instance IsSeparated.hasAffineProperty :
    HasAffineProperty @IsSeparated fun X _ _ _ => X.IsSeparated := by
  convert! HasAffineProperty.of_isZariskiLocalAtTarget @IsSeparated with X Y f hY
  rw [Scheme.isSeparated_iff]; rw [← terminal.comp_from f]; rw [IsSeparated.comp_iff]
  rfl

/--
lemma `ext_of_isDominant` / 引理 `ext_of_isDominant`

English:
lemma ext_of_isDominant
  statement: [IsReduced X] {f g : X ⟶ Y} [Y.IsSeparated]
  proof: ext_of_isDominant_of_isSeparated (Limits.terminal.from _) (Limits.terminal.hom_ext _ _) ι hU

中文:
引理 ext_of_isDominant
  结论: [IsReduced X] {f g : X ⟶ Y} [Y.IsSeparated]
  证明: ext_of_isDominant_of_isSeparated (Limits.terminal.from _) (Limits.terminal.hom_ext _ _) ι hU

Depends on / 依赖: Limits, Limits.terminal.from, Limits.terminal.hom_ext, ext_of_isDominant_of_isSeparated, hom_ext, terminal
-/
lemma ext_of_isDominant [IsReduced X] {f g : X ⟶ Y} [Y.IsSeparated]
    (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated (Limits.terminal.from _) (Limits.terminal.hom_ext _ _) ι hU

end AlgebraicGeometry
