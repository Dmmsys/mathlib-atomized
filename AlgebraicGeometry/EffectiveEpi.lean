/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
module

public import Mathlib.Algebra.Category.Ring.EqualizerPushout
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.Category.TopCat.EffectiveEpi
public import Mathlib.CategoryTheory.EffectiveEpi.Preserves

/-!
# Effective epimorphisms in the category of schemes

We collect results about effective epimorphisms in the category of schemes.

## Main results

For a surjective and flat morphism `π : X ⟶ Y` between affine schemes, we prove the following.
* `exists_comp_eq_of_flat_of_isAffine`: Any morphism `f : X ⟶ S` of schemes whose two pullbacks to
  `X ×[Y] X` agree descends to a morphism `u : Y ⟶ S` with `π ≫ u = f`.
* `isRegularEpi_of_flat_of_surjective_of_isAffine`: The map `π : X ⟶ Y` is a regular epimorphism
  in the category of schemes. This implies `EffectiveEpi π` by `inferInstance`.

For the general result that a quasi-compact, surjective and flat morphism is an effective
epimorphism, see the file `Mathlib.AlgebraicGeometry.Sites.Fpqc`.

## Reference

* https://stacks.math.columbia.edu/tag/023Q

-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

section Scheme

/--
Instance `effectiveEpi_base_of_flat` / 实例 `effectiveEpi_base_of_flat`

English:
instance effectiveEpi_base_of_flat
  signature: {X Y : Scheme.{u}} {f : X ⟶ Y} [Flat f] [Surjective f]
  body: by
  rw [TopCat.effectiveEpi_iff_isQuotientMap]
  exact Flat.isQuotientMap_of_surjective _

中文:
实例 effectiveEpi_base_of_flat
  签名: {X Y : Scheme.{u}} {f : X ⟶ Y} [Flat f] [Surjective f]
  定义体: by
  rw [TopCat.effectiveEpi_iff_isQuotientMap]
  exact Flat.isQuotientMap_of_surjective _

Depends on / 依赖: Flat.isQuotientMap_of_surjective, TopCat, TopCat.effectiveEpi_iff_isQuotientMap, effectiveEpi_iff_isQuotientMap, isQuotientMap_of_surjective, map_prop
-/
instance effectiveEpi_base_of_flat {X Y : Scheme.{u}} {f : X ⟶ Y} [Flat f] [Surjective f]
    [QuasiCompact f] : EffectiveEpi f.base := by
  rw [TopCat.effectiveEpi_iff_isQuotientMap]
  exact Flat.isQuotientMap_of_surjective _

namespace EffectiveEpiConstruction

/--
lemma `of_isAffine_target` / 引理 `of_isAffine_target`

English:
lemma of_isAffine_target
  statement: {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
  proof: by
  have : EffectiveEpi (AffineScheme.ofHom π) := by
    apply AffineScheme.equivCommRingCat.functor.effectiveEpi_of_map
    apply CommRingCat.Opposite.effectiveEpi_of_faithfullyFlat
    exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine π).mp ⟨‹_›, ‹_›⟩
  obtain ⟨u, hu⟩ := IsRegularEpi

中文:
引理 of_isAffine_target
  结论: {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
  证明: by
  have : EffectiveEpi (AffineScheme.ofHom π) := by
    apply AffineScheme.equivCommRingCat.functor.effectiveEpi_of_map
    apply CommRingCat.Opposite.effectiveEpi_of_faithfullyFlat
    exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine π).mp ⟨‹_›, ‹_›⟩
  obtain ⟨u, hu⟩ := IsRegularEpi
-/
private lemma of_isAffine_target {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
    [Surjective π] [Flat π]
    (f : X ⟶ S) (hf : pullback.fst π π ≫ f = pullback.snd π π ≫ f)
    [IsAffine S] :
    exists u : Y ⟶ S, π ≫ u = f := by
  have : EffectiveEpi (AffineScheme.ofHom π) := by
    apply AffineScheme.equivCommRingCat.functor.effectiveEpi_of_map
    apply CommRingCat.Opposite.effectiveEpi_of_faithfullyFlat
    exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine π).mp ⟨‹_›, ‹_›⟩
  obtain ⟨u, hu⟩ := IsRegularEpi.exists_of_isKernelPair
    (AffineScheme.ofHom π)
    (IsPullback.of_map (f := AffineScheme.ofHom (pullback.fst π π)) (AffineScheme.forgetToScheme)
      (InducedCategory.Hom.ext pullback.condition) (.of_hasPullback _ _))
    (AffineScheme.ofHom f) (InducedCategory.Hom.ext hf)
  use u.hom, InducedCategory.Hom.ext_iff.mp hu

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open pullback in
/--
lemma `exists_openCover_exists` / 引理 `exists_openCover_exists`

English:
lemma exists_openCover_exists
  statement: {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
  proof: by
  obtain ⟨b, hfac⟩ : exists (u : Y.carrier ⟶ S.carrier), π.base ≫ u = f.base := by
    apply IsRegularEpi.exists_of_isKernelPair _ (IsPullback.of_hasPullback _ _)
    have := congr(Scheme.forgetToTop.map $hf)
    rwa [Functor.map_comp, Functor.map_comp, ← pullbackComparison_comp_fst_assoc,
      

中文:
引理 exists_openCover_exists
  结论: {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
  证明: by
  obtain ⟨b, hfac⟩ : exists (u : Y.carrier ⟶ S.carrier), π.base ≫ u = f.base := by
    apply IsRegularEpi.exists_of_isKernelPair _ (IsPullback.of_hasPullback _ _)
    have := congr(Scheme.forgetToTop.map $hf)
    rwa [Functor.map_comp, Functor.map_comp, ← pullbackComparison_comp_fst_assoc,
      
-/
private lemma exists_openCover_exists {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y)
    [Surjective π] [Flat π]
    (f : X ⟶ S) (hf : pullback.fst π π ≫ f = pullback.snd π π ≫ f) :
    exists (𝒰 : OpenCover.{u} Y),
      forall i : 𝒰.I₀, exists (u : 𝒰.X i ⟶ S), pullback.fst π (𝒰.f i) ≫ f = pullback.snd _ _ ≫ u := by
  obtain ⟨b, hfac⟩ : exists (u : Y.carrier ⟶ S.carrier), π.base ≫ u = f.base := by
    apply IsRegularEpi.exists_of_isKernelPair _ (IsPullback.of_hasPullback _ _)
    have := congr(Scheme.forgetToTop.map $hf)
    rwa [Functor.map_comp, Functor.map_comp, ← pullbackComparison_comp_fst_assoc,
      ← pullbackComparison_comp_snd_assoc, cancel_epi] at this
let 𝒰 := Y.openCoverOfIsOpenCover _ Y.isBasis_affineOpens.isOpenCover_mem_and_le
    (S.isBasis_affineOpens.isOpenCover.comap b.hom)
  refine ⟨𝒰, fun i => ?_⟩
  have : IsAffine (𝒰.X i) := i.2.1
  let f' : pullback π (𝒰.f i) ⟶ i.1.2.1 := by
    apply IsOpenImmersion.lift (Scheme.Opens.ι i.1.2.1) (pullback.fst _ _ ≫ f)
    dsimp
    rw [← hfac]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base_assoc]; rw [pullback.condition]
    simp only [Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp,
      range_eq_univ, Set.image_univ, Opens.range_ι, Set.image_subset_iff]
    exact trans (by simp [𝒰]) i.2.2
  have h1 : fst (snd π (𝒰.f i)) _ ≫ fst _ _ = map _ _ _ _ (fst _ _) (fst _ _) _
    condition.symm condition.symm ≫ fst π π := by simp
  have h2 : snd (snd π (𝒰.f i)) _ ≫ fst _ _ = map _ _ _ _ (fst _ _) (fst _ _) _
    condition.symm condition.symm ≫ snd π π := by simp
obtain ⟨u, hu⟩ := of_isAffine_target (pullback.snd π (𝒰.f i)) f' by
    simp only [← cancel_mono (Scheme.Opens.ι i.1.2.1),
      Category.assoc, IsOpenImmersion.lift_fac, f', reassoc_of% h1, reassoc_of% h2, hf]
  refine ⟨u ≫ Scheme.Opens.ι _, ?_⟩
  simp [reassoc_of% hu, f']

end EffectiveEpiConstruction

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `π : X ⟶ Y` is a flat and surjective morphism between affine schemes, then `π` is a
regular epimorphism in the category of schemes. -/
@[stacks 023Q]
/--
lemma `isRegularEpi_of_flat_of_surjective_of_isAffine` / 引理 `isRegularEpi_of_flat_of_surjective_of_isAffine`

English:
lemma isRegularEpi_of_flat_of_surjective_of_isAffine
  proof: by
  have : Epi π := Flat.epi_of_flat_of_surjective _
  refine .of_epi_of_exists fun Z f hf => ?_
  obtain ⟨𝒰, h⟩ := EffectiveEpiConstruction.exists_openCover_exists π f hf
  choose u hfac using h
  refine ⟨𝒰.glueMorphisms u ?_, ?_⟩
  · intro i j
    have : Epi (pullback.snd π (pullback.fst (𝒰.f i) 

中文:
引理 isRegularEpi_of_flat_of_surjective_of_isAffine
  证明: by
  have : Epi π := Flat.epi_of_flat_of_surjective _
  refine .of_epi_of_exists fun Z f hf => ?_
  obtain ⟨𝒰, h⟩ := EffectiveEpiConstruction.exists_openCover_exists π f hf
  choose u hfac using h
  refine ⟨𝒰.glueMorphisms u ?_, ?_⟩
  · intro i j
    have : Epi (pullback.snd π (pullback.fst (𝒰.f i) 

Depends on / 依赖: EffectiveEpiConstruction, EffectiveEpiConstruction.exists_openCover_exists, Flat.epi_of_flat_of_surjective, cancel_epi, condition, congrHom, conv_rhs, epi_of_flat_of_surjective, exists_openCover_exists, glueMorphisms, of_epi_of_exists, pullback, pullback.condition.symm, pullback.congrHom, pullback.fst, pullback.snd
-/
lemma isRegularEpi_of_flat_of_surjective_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (π : X ⟶ Y) [Surjective π] [Flat π] :
    IsRegularEpi π := by
  have : Epi π := Flat.epi_of_flat_of_surjective _
  refine .of_epi_of_exists fun Z f hf => ?_
  obtain ⟨𝒰, h⟩ := EffectiveEpiConstruction.exists_openCover_exists π f hf
  choose u hfac using h
  refine ⟨𝒰.glueMorphisms u ?_, ?_⟩
  · intro i j
    have : Epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)) :=
      Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.snd π (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i))]; rw [← cancel_epi (pullback.congrHom rfl pullback.condition.symm).hom]
    conv_rhs =>
      simp only [pullback.congrHom_hom, limit.lift_π_assoc, PullbackCone.mk_pt, cospan_right,
      PullbackCone.mk_π_app, Category.comp_id]
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd]; rw [Category.assoc]; rw [← pullbackLeftPullbackSndIso_inv_snd_snd]; rw [Category.assoc]; rw [← pullback.condition_assoc]; rw [← hfac i]; rw [← pullback.condition_assoc]; rw [← hfac j]
    simp
  · apply Cover.hom_ext (𝒰.pullback₁ π)
    intro i
    simp [pullback.condition_assoc, hfac]

end Scheme

end AlgebraicGeometry
