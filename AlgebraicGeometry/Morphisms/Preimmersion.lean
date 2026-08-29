/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

/-!

# Preimmersions of schemes

A morphism of schemes `f : X ⟶ Y` is a preimmersion if the underlying map of topological spaces
is an embedding and the induced morphisms of stalks are all surjective. This is not a concept seen
in the literature but it is useful for generalizing results on immersions to other maps including
`Spec 𝒪_{X, x} ⟶ X` and inclusions of fibers `κ(x) ×ₓ Y ⟶ Y`.

-/

public section

universe v u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ Y` is a preimmersion if the underlying map of
topological spaces is an embedding and the induced morphisms of stalks are all surjective. -/
@[mk_iff]
/--
Definition of `IsPreimmersion` / `IsPreimmersion` 的定义

English:
class IsPreimmersion
  parameters: {X Y : Scheme} (f : X ⟶ Y)
  extends: SurjectiveOnStalks f
  axioms and operations (1):
    - isEmbedding((f)) : IsEmbedding f

中文:
类 是Preimmersion
  参数: {X Y : 概形} (f : X ⟶ Y)
  继承: SurjectiveOnStalks f
  公理与运算 (1 个):
    - isEmbedding((f)) : 是嵌入 f

Depends on / 依赖: IsPreimmersion, IsPreimmersion.isEmbedding, isEmbedding
-/
class IsPreimmersion {X Y : Scheme} (f : X ⟶ Y) : Prop extends SurjectiveOnStalks f where
  isEmbedding (f) : IsEmbedding f

alias Scheme.Hom.isEmbedding := IsPreimmersion.isEmbedding

@[deprecated (since := "2026-01-20")] alias IsPreimmersion.base_embedding := Scheme.Hom.isEmbedding

/--
lemma `isPreimmersion_eq_inf` / 引理 `isPreimmersion_eq_inf`

English:
lemma isPreimmersion_eq_inf
  proof: by
  ext
  rw [isPreimmersion_iff]
  rfl

中文:
引理 isPreimmersion_eq_inf
  证明: by
  ext
  rw [isPreimmersion_iff]
  rfl

Depends on / 依赖: isPreimmersion_iff
-/
lemma isPreimmersion_eq_inf :
    @IsPreimmersion = (@SurjectiveOnStalks ⊓ topologically IsEmbedding : MorphismProperty _) := by
  ext
  rw [isPreimmersion_iff]
  rfl

namespace IsPreimmersion

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtTarget @IsPreimmersion
  body: isPreimmersion_eq_inf ▸ inferInstance

中文:
实例 :
  签名: IsZariskiLocalAtTarget @是Preimmersion
  定义体: isPreimmersion_eq_inf ▸ inferInstance

Depends on / 依赖: isPreimmersion_eq_inf
-/
instance : IsZariskiLocalAtTarget @IsPreimmersion :=
  isPreimmersion_eq_inf ▸ inferInstance

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : IsPreimmersion f where
  isEmbedding := f.isOpenEmbedding.isEmbedding
  stalkMap_surjective _ := (ConcreteCategory.bijective_of_isIso _).2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @IsPreimmersion
  body: inferInstance
  comp_mem f g _ _ := ⟨g.isEmbedding.comp f.isEmbedding⟩

中文:
实例 :
  签名: MorphismProperty.是Multiplicative @是Preimmersion
  定义体: inferInstance
  comp_mem f g _ _ := ⟨g.isEmbedding.comp f.isEmbedding⟩
-/
instance : MorphismProperty.IsMultiplicative @IsPreimmersion where
  id_mem _ := inferInstance
  comp_mem f g _ _ := ⟨g.isEmbedding.comp f.isEmbedding⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion f]
  body: MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

中文:
实例 comp
  签名: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z) [是Preimmersion f]
  定义体: MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

Depends on / 依赖: IsStableUnderComposition, MorphismProperty, MorphismProperty.IsStableUnderComposition.comp_mem, comp_mem
-/
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion f]
    [IsPreimmersion g] : IsPreimmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

instance (priority := 900) {X Y} (f : X ⟶ Y) [IsPreimmersion f] : Mono f :=
  SurjectiveOnStalks.mono_of_injective f.isEmbedding.injective

/--
theorem `of_comp` / 定理 `of_comp`

English:
theorem of_comp
  statement: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g]
  proof: by
    have h := (f ≫ g).isEmbedding
    rwa [← g.isEmbedding.of_comp_iff]
  stalkMap_surjective x := by
    have h := (f ≫ g).stalkMap_surjective x
    rw [Scheme.Hom.stalkMap_comp] at h
    exact Function.Surjective.of_comp h

中文:
定理 of_comp
  结论: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z) [是Preimmersion g]
  证明: by
    have h := (f ≫ g).isEmbedding
    rwa [← g.isEmbedding.of_comp_iff]
  stalkMap_surjective x := by
    have h := (f ≫ g).stalkMap_surjective x
    rw [Scheme.Hom.stalkMap_comp] at h
    exact Function.Surjective.of_comp h

Depends on / 依赖: Function, Function.Surjective.of_comp, Scheme, Scheme.Hom.stalkMap_comp, Surjective, g.isEmbedding.of_comp_iff, isEmbedding, of_comp, of_comp_iff, stalkMap_comp, stalkMap_surjective
-/
theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g]
    [IsPreimmersion (f ≫ g)] : IsPreimmersion f where
  isEmbedding := by
    have h := (f ≫ g).isEmbedding
    rwa [← g.isEmbedding.of_comp_iff]
  stalkMap_surjective x := by
    have h := (f ≫ g).stalkMap_surjective x
    rw [Scheme.Hom.stalkMap_comp] at h
    exact Function.Surjective.of_comp h

/--
theorem `comp_iff` / 定理 `comp_iff`

English:
theorem comp_iff
  given: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g]
  proof: ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

中文:
定理 comp_iff
  条件: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z) [是Preimmersion g]
  证明: ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

Depends on / 依赖: of_comp
-/
theorem comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g] :
    IsPreimmersion (f ≫ g) ↔ IsPreimmersion f :=
  ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

/--
lemma `SpecMap_iff` / 引理 `SpecMap_iff`

English:
lemma SpecMap_iff
  given: {R S : CommRingCat.{u}} (f : R ⟶ S)
  proof: by
  rw [← HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)]; rw [isPreimmersion_iff]; rw [and_comm]
  rfl

中文:
引理 SpecMap_iff
  条件: {R S : 交换环范畴.{u}} (f : R ⟶ S)
  证明: by
  rw [← HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)]; rw [isPreimmersion_iff]; rw [and_comm]
  rfl

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.Spec_iff, Spec_iff, SurjectiveOnStalks, and_comm, isPreimmersion_iff
-/
lemma SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPreimmersion (Spec.map f) ↔ IsEmbedding (PrimeSpectrum.comap f.hom) ∧
      f.hom.SurjectiveOnStalks := by
  rw [← HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)]; rw [isPreimmersion_iff]; rw [and_comm]
  rfl

/--
lemma `mk_SpecMap` / 引理 `mk_SpecMap`

English:
lemma mk_SpecMap
  statement: {R S : CommRingCat.{u}} {f : R ⟶ S}
  proof: (SpecMap_iff f).mpr ⟨h₁, h₂⟩

中文:
引理 mk_SpecMap
  结论: {R S : 交换环范畴.{u}} {f : R ⟶ S}
  证明: (SpecMap_iff f).mpr ⟨h₁, h₂⟩

Depends on / 依赖: SpecMap_iff
-/
lemma mk_SpecMap {R S : CommRingCat.{u}} {f : R ⟶ S}
    (h₁ : IsEmbedding (PrimeSpectrum.comap f.hom)) (h₂ : f.hom.SurjectiveOnStalks) :
    IsPreimmersion (Spec.map f) :=
  (SpecMap_iff f).mpr ⟨h₁, h₂⟩

/--
lemma `of_isLocalization` / 引理 `of_isLocalization`

English:
lemma of_isLocalization
  statement: {R S : Type u} [CommRing R] (M : Submonoid R) [CommRing S]
  proof: IsPreimmersion.mk_SpecMap
    (PrimeSpectrum.localization_comap_isEmbedding (R := R) S M)
    (RingHom.surjectiveOnStalks_of_isLocalization (M := M) S)

中文:
引理 of_isLocalization
  结论: {R S : 类型u} [交换环 R] (M : 子幺半群 R) [交换环 S]
  证明: IsPreimmersion.mk_SpecMap
    (PrimeSpectrum.localization_comap_isEmbedding (R := R) S M)
    (RingHom.surjectiveOnStalks_of_isLocalization (M := M) S)

Depends on / 依赖: IsPreimmersion, IsPreimmersion.mk_SpecMap, PrimeSpectrum, PrimeSpectrum.localization_comap_isEmbedding, RingHom, RingHom.surjectiveOnStalks_of_isLocalization, SimplexCategory, SimplexCategory.mkOfSucc_zero_eq_, StrictSegal, StrictSegal.spineEquiv, localization_comap_isEmbedding, mk_SpecMap, spineEquiv, surjectiveOnStalks_of_isLocalization
-/
lemma of_isLocalization {R S : Type u} [CommRing R] (M : Submonoid R) [CommRing S]
    [Algebra R S] [IsLocalization M S] :
    IsPreimmersion (Spec.map (CommRingCat.ofHom <| algebraMap R S)) :=
  IsPreimmersion.mk_SpecMap
    (PrimeSpectrum.localization_comap_isEmbedding (R := R) S M)
    (RingHom.surjectiveOnStalks_of_isLocalization (M := M) S)

set_option backward.isDefEq.respectTransparency.types false in
open Limits MorphismProperty in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderBaseChange @IsPreimmersion
  body: by
  refine .mk' fun X Y Z f g _ _ => ?_
  have := pullback_fst (P := @SurjectiveOnStalks) f g inferInstance
  constructor
  let L (x : (pullback f g :)) : { x : X × Y | f x.1 = g x.2 } :=
    ⟨⟨pullback.fst f g x, pullback.snd f g x⟩,
    by simp only [Set.mem_ofPred, ← Scheme.Hom.comp_apply, pullb

中文:
实例 :
  签名: 是StableUnderBaseChange @是Preimmersion
  定义体: by
  refine .mk' fun X Y Z f g _ _ => ?_
  have := pullback_fst (P := @SurjectiveOnStalks) f g inferInstance
  constructor
  let L (x : (pullback f g :)) : { x : X × Y | f x.1 = g x.2 } :=
    ⟨⟨pullback.fst f g x, pullback.snd f g x⟩,
    by simp only [Set.mem_ofPred, ← Scheme.Hom.comp_apply, pullb

Depends on / 依赖: IsEmbedding, IsEmbedding.of_comp, IsEmbedding.subtypeVal.comp, Scheme, Scheme.Hom.comp_apply, Set.mem_ofPred, SurjectiveOnStalks, SurjectiveOnStalks.isEmbedding_pullback, TopCat, TopCat.pullbackHomeoPreimage, comp_apply, condition, continuous_subtype_val, f.cont, fun_prop, isEmbedding_pullback, mem_ofPred, of_comp, pullback, pullback.condition
-/
instance : IsStableUnderBaseChange @IsPreimmersion := by
  refine .mk' fun X Y Z f g _ _ => ?_
  have := pullback_fst (P := @SurjectiveOnStalks) f g inferInstance
  constructor
  let L (x : (pullback f g :)) : { x : X × Y | f x.1 = g x.2 } :=
    ⟨⟨pullback.fst f g x, pullback.snd f g x⟩,
    by simp only [Set.mem_ofPred, ← Scheme.Hom.comp_apply, pullback.condition]⟩
  have : IsEmbedding L := IsEmbedding.of_comp (by fun_prop) continuous_subtype_val
    (SurjectiveOnStalks.isEmbedding_pullback f g)
  exact IsEmbedding.subtypeVal.comp ((TopCat.pullbackHomeoPreimage _ f.continuous _
    g.isEmbedding).isEmbedding.comp this)

variable {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsPreimmersion
  signature: g] : IsPreimmersion (Limits.pullback.fst f g)
  body: MorphismProperty.pullback_fst f g inferInstance

中文:
实例 [是Preimmersion
  签名: g] : 是Preimmersion (Limits.pullback.fst f g)
  定义体: MorphismProperty.pullback_fst f g inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
instance [IsPreimmersion g] : IsPreimmersion (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsPreimmersion
  signature: f] : IsPreimmersion (Limits.pullback.snd f g)
  body: MorphismProperty.pullback_snd f g inferInstance

中文:
实例 [是Preimmersion
  签名: f] : 是Preimmersion (Limits.pullback.snd f g)
  定义体: MorphismProperty.pullback_snd f g inferInstance

Depends on / 依赖: Functor, Functor.map_comp_apply, MorphismProperty, MorphismProperty.pullback_snd, SimplexCategory, SimplexCategory.mkOfSucc_one_eq_, SimplexCategory.mkOfSucc_zero_eq_, StrictSegal, StrictSegal.spineEquiv, fin_cases, hY.spineEquiv, injective, map_comp_apply, op_comp, pullback_snd, spineEquiv
-/
instance [IsPreimmersion f] : IsPreimmersion (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [IsPreimmersion f] : IsPreimmersion (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

end IsPreimmersion

end AlgebraicGeometry
