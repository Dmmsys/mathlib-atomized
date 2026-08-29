/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Flat morphisms

A morphism of schemes `f : X ⟶ Y` is flat if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is flat. This is equivalent to
asking that all stalk maps are flat (see `AlgebraicGeometry.Flat.iff_flat_stalkMap`).

We show that this property is local, and are stable under compositions and base change.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is flat if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is flat. This is equivalent to
asking that all stalk maps are flat (see `AlgebraicGeometry.Flat.iff_flat_stalkMap`).
-/
@[mk_iff]
/--
Definition of `Flat` / `Flat` 的定义

English:
class Flat
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - flat_appLE((f)) : forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.Flat

中文:
类 平坦
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - flat_appLE((f)) : 对任意 {U : Y.Opens} (_ : 是仿射开集 U) {V : X.Opens} (_ : 是仿射开集 V) (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.平坦

Depends on / 依赖: Flat.flat_appLE, flat_appLE
-/
class Flat (f : X ⟶ Y) : Prop where
  flat_appLE (f) :
    forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U),
      (f.appLE U V e).hom.Flat

alias Scheme.Hom.flat_appLE := Flat.flat_appLE

@[deprecated (since := "2026-01-20")] alias Flat.flat_of_affine_subset := Scheme.Hom.flat_appLE

namespace Flat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasRingHomProperty @Flat RingHom.Flat
  body: RingHom.Flat.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [flat_iff]; rw [affineLocally_iff_forall_isAffineOpen]

中文:
实例 :
  签名: 有RingHomProperty @平坦 环态射.平坦
  定义体: RingHom.Flat.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [flat_iff]; rw [affineLocally_iff_forall_isAffineOpen]

Depends on / 依赖: RingHom, RingHom.Flat.propertyIsLocal, propertyIsLocal
-/
instance : HasRingHomProperty @Flat RingHom.Flat where
  isLocal_ringHomProperty := RingHom.Flat.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [flat_iff]; rw [affineLocally_iff_forall_isAffineOpen]

instance (priority := 900) [IsOpenImmersion f] : Flat f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.Flat.containsIdentities

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsStableUnderComposition @Flat
  body: HasRingHomProperty.stableUnderComposition RingHom.Flat.stableUnderComposition

@[simp]

中文:
实例 :
  签名: MorphismProperty.是StableUnderComposition @平坦
  定义体: HasRingHomProperty.stableUnderComposition RingHom.Flat.stableUnderComposition

@[simp]

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.stableUnderComposition, RingHom, RingHom.Flat.stableUnderComposition, stableUnderComposition
-/
instance : MorphismProperty.IsStableUnderComposition @Flat :=
  HasRingHomProperty.stableUnderComposition RingHom.Flat.stableUnderComposition

@[simp]
/--
lemma `SpecMap_iff` / 引理 `SpecMap_iff`

English:
lemma SpecMap_iff
  given: {R S : CommRingCat.{u}} {f : R ⟶ S}
  statement: Flat (Spec.map f) ↔ f.hom.Flat
  proof: HasRingHomProperty.Spec_iff

中文:
引理 SpecMap_iff
  条件: {R S : 交换环范畴.{u}} {f : R ⟶ S}
  结论: 平坦 (Spec.map f) ↔ f.hom.平坦
  证明: HasRingHomProperty.Spec_iff

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.Spec_iff, Spec_iff
-/
lemma SpecMap_iff {R S : CommRingCat.{u}} {f : R ⟶ S} : Flat (Spec.map f) ↔ f.hom.Flat :=
  HasRingHomProperty.Spec_iff

/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: MorphismProperty.comp_mem _ f g hf hg

中文:
实例 comp
  签名: {X Y Z : 概形} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: MorphismProperty.comp_mem _ f g hf hg

Depends on / 依赖: MorphismProperty, MorphismProperty.comp_mem, comp_mem
-/
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : Flat f] [hg : Flat g] : Flat (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.Respects @Flat @IsOpenImmersion
  body: inferInstance

中文:
实例 :
  签名: MorphismProperty.Respects @平坦 @是开浸入
  定义体: inferInstance
-/
instance : MorphismProperty.Respects @Flat @IsOpenImmersion where
  postcomp _ _ _ _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @Flat
  body: inferInstance

中文:
实例 :
  签名: MorphismProperty.是Multiplicative @平坦
  定义体: inferInstance
-/
instance : MorphismProperty.IsMultiplicative @Flat where
  id_mem _ := inferInstance

/--
Instance `isStableUnderBaseChange` / 实例 `isStableUnderBaseChange`

English:
instance isStableUnderBaseChange
  signature: : MorphismProperty.IsStableUnderBaseChange @Flat
  body: HasRingHomProperty.isStableUnderBaseChange RingHom.Flat.isStableUnderBaseChange

中文:
实例 isStableUnderBaseChange
  签名: : MorphismProperty.是StableUnderBaseChange @平坦
  定义体: HasRingHomProperty.isStableUnderBaseChange RingHom.Flat.isStableUnderBaseChange

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.isStableUnderBaseChange, RingHom, RingHom.Flat.isStableUnderBaseChange, isStableUnderBaseChange
-/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Flat :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.Flat.isStableUnderBaseChange

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [Flat g] : Flat (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [Flat f] : Flat (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (V : Y.Opens) [Flat f] : Flat (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Flat f] : Flat (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

/--
lemma `of_stalkMap` / 引理 `of_stalkMap`

English:
lemma of_stalkMap
  given: (H : forall x, (f.stalkMap x).hom.Flat)
  statement: Flat f
  proof: HasRingHomProperty.of_stalkMap RingHom.Flat.ofLocalizationPrime H

中文:
引理 of_stalkMap
  条件: (H : 对任意 x, (f.stalkMap x).hom.平坦)
  结论: 平坦 f
  证明: HasRingHomProperty.of_stalkMap RingHom.Flat.ofLocalizationPrime H

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.of_stalkMap, RingHom, RingHom.Flat.ofLocalizationPrime, ofLocalizationPrime, of_stalkMap
-/
lemma of_stalkMap (H : forall x, (f.stalkMap x).hom.Flat) : Flat f :=
  HasRingHomProperty.of_stalkMap RingHom.Flat.ofLocalizationPrime H

/--
lemma `stalkMap` / 引理 `stalkMap`

English:
lemma stalkMap
  given: [Flat f] (x : X)
  statement: (f.stalkMap x).hom.Flat
  proof: HasRingHomProperty.stalkMap (P := @Flat)
    (fun f hf J hJ => hf.localRingHom J (J.comap f) rfl) ‹_› x

中文:
引理 stalkMap
  条件: [平坦 f] (x : X)
  结论: (f.stalkMap x).hom.平坦
  证明: HasRingHomProperty.stalkMap (P := @Flat)
    (fun f hf J hJ => hf.localRingHom J (J.comap f) rfl) ‹_› x

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.stalkMap, J.comap, hf.localRingHom, localRingHom, stalkMap
-/
lemma stalkMap [Flat f] (x : X) : (f.stalkMap x).hom.Flat :=
  HasRingHomProperty.stalkMap (P := @Flat)
    (fun f hf J hJ => hf.localRingHom J (J.comap f) rfl) ‹_› x

/--
lemma `iff_flat_stalkMap` / 引理 `iff_flat_stalkMap`

English:
lemma iff_flat_stalkMap
  statement: Flat f ↔ forall x, (f.stalkMap x).hom.Flat
  proof: ⟨fun _ => stalkMap f, fun H => of_stalkMap f H⟩

中文:
引理 iff_flat_stalkMap
  结论: 平坦 f ↔ 对任意 x, (f.stalkMap x).hom.平坦
  证明: ⟨fun _ => stalkMap f, fun H => of_stalkMap f H⟩

Depends on / 依赖: of_stalkMap, stalkMap
-/
lemma iff_flat_stalkMap : Flat f ↔ forall x, (f.stalkMap x).hom.Flat :=
  ⟨fun _ => stalkMap f, fun H => of_stalkMap f H⟩

set_option backward.isDefEq.respectTransparency.types false in
instance {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] {Y : ι -> Scheme.{u}} {f : forall i, Y i ⟶ X}
    [forall i, Flat (f i)] : Flat (Sigma.desc f) :=
  IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)

set_option backward.isDefEq.respectTransparency false in
instance (priority := low) [Subsingleton Y] [IsIntegral Y] : Flat f := by
  refine (MorphismProperty.cancel_right_of_respectsIso @Flat _ Y.isoSpec.hom).mp ?_
  refine (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i => ?_
  rw [← Spec.map_preimage (X.affineCover.f i ≫ f ≫ Y.isoSpec.hom)]; rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact .of_isField (isField_of_isIntegral_of_subsingleton _) _

/-- A surjective, quasi-compact, flat morphism is a quotient map. -/
@[stacks 02JY]
/--
lemma `isQuotientMap_of_surjective` / 引理 `isQuotientMap_of_surjective`

English:
lemma isQuotientMap_of_surjective
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f]
  proof: by
  rw [Topology.isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s =>
    ⟨fun hs => ?_, fun hs => hs.preimage f.continuous⟩, f.surjective⟩
  wlog hY : exists R, Y = Spec R
  · let 𝒰 := Y.affineCover
    rw [𝒰.isOpenCover_opensRange.isOpen_iff_inter]
    intro i
    rw [Scheme.Hom.coe_opensRange]; rw [← Set.image_preimage_eq_inter_range]
    apply (𝒰.f i).isOpenEmbedding.isOpenMap
    refine this (f := pullback.fst (𝒰.f i) f) _ ?_ ⟨_, rfl⟩
    rw [← Set.preimage_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [pullback.condition]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]
    exact hs.preimage (Scheme.Hom.continuous _)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S
  · have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    let 𝒰 := X.affineCover.finiteSubcover
    let p : ∐ (fun i : 𝒰.I₀ => 𝒰.X i) ⟶ X := Sigma.desc (fun i => 𝒰.f i)
    refine this (f := (∐ (fun i : 𝒰.I₀ => 𝒰.X i)).isoSpec.inv ≫ p ≫ f) _ _ ?_ ⟨_, rfl⟩
    rw [← Category.assoc]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]
    exact hs.preimage (_ ≫ p).continuous
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ((PrimeSpectrum.isQuotientMap_of_generalizingMap ?_ ?_).isOpen_preimage).mp hs
  · exact (surjective_iff (Spec.map φ)).mp inferInstance
  · apply RingHom.Flat.generalizingMap_comap
    rwa [← HasRingHomProperty.Spec_iff (P := @Flat)]

中文:
引理 isQuotientMap_of_surjective
  结论: {X Y : 概形.{u}} (f : X ⟶ Y) [平坦 f] [拟紧 f]
  证明: by
  rw [Topology.isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s =>
    ⟨fun hs => ?_, fun hs => hs.preimage f.continuous⟩, f.surjective⟩
  wlog hY : exists R, Y = Spec R
  · let 𝒰 := Y.affineCover
    rw [𝒰.isOpenCover_opensRange.isOpen_iff_inter]
    intro i
    rw [Scheme.Hom.coe_opensRange]; rw [← Set.image_preimage_eq_inter_range]
    apply (𝒰.f i).isOpenEmbedding.isOpenMap
    refine this (f := pullback.fst (𝒰.f i) f) _ ?_ ⟨_, rfl⟩
    rw [← Set.preimage_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [pullback.condition]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]
    exact hs.preimage (Scheme.Hom.continuous _)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S
  · have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    let 𝒰 := X.affineCover.finiteSubcover
    let p : ∐ (fun i : 𝒰.I₀ => 𝒰.X i) ⟶ X := Sigma.desc (fun i => 𝒰.f i)
    refine this (f := (∐ (fun i : 𝒰.I₀ => 𝒰.X i)).isoSpec.inv ≫ p ≫ f) _ _ ?_ ⟨_, rfl⟩
    rw [← Category.assoc]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]
    exact hs.preimage (_ ≫ p).continuous
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ((PrimeSpectrum.isQuotientMap_of_generalizingMap ?_ ?_).isOpen_preimage).mp hs
  · exact (surjective_iff (Spec.map φ)).mp inferInstance
  · apply RingHom.Flat.generalizingMap_comap
    rwa [← HasRingHomProperty.Spec_iff (P := @Flat)]

Depends on / 依赖: Scheme, Scheme.Hom.coe_opensRange, Scheme.Hom.comp, Set.image_preimage_eq_inter_range, Set.preimage_comp, TopCat, TopCat.coe_comp, Topology, Topology.isQuotientMap_iff, Y.affineCover, affineCover, coe_comp, coe_opensRange, continuous, f.continuous, f.surjective, hs.preimage, image_preimage_eq_inter_range, isOpenCover_opensRange, isOpenCover_opensRange.isOpen_iff_inter
-/
lemma isQuotientMap_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f]
    [Surjective f] : Topology.IsQuotientMap f := by
  rw [Topology.isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen fun s =>
    ⟨fun hs => ?_, fun hs => hs.preimage f.continuous⟩, f.surjective⟩
  wlog hY : exists R, Y = Spec R
  · let 𝒰 := Y.affineCover
    rw [𝒰.isOpenCover_opensRange.isOpen_iff_inter]
    intro i
    rw [Scheme.Hom.coe_opensRange]; rw [← Set.image_preimage_eq_inter_range]
    apply (𝒰.f i).isOpenEmbedding.isOpenMap
    refine this (f := pullback.fst (𝒰.f i) f) _ ?_ ⟨_, rfl⟩
    rw [← Set.preimage_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [pullback.condition]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]
    exact hs.preimage (Scheme.Hom.continuous _)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S
  · have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    let 𝒰 := X.affineCover.finiteSubcover
    let p : ∐ (fun i : 𝒰.I₀ => 𝒰.X i) ⟶ X := Sigma.desc (fun i => 𝒰.f i)
    refine this (f := (∐ (fun i : 𝒰.I₀ => 𝒰.X i)).isoSpec.inv ≫ p ≫ f) _ _ ?_ ⟨_, rfl⟩
    rw [← Category.assoc]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]
    exact hs.preimage (_ ≫ p).continuous
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ((PrimeSpectrum.isQuotientMap_of_generalizingMap ?_ ?_).isOpen_preimage).mp hs
  · exact (surjective_iff (Spec.map φ)).mp inferInstance
  · apply RingHom.Flat.generalizingMap_comap
    rwa [← HasRingHomProperty.Spec_iff (P := @Flat)]

set_option backward.isDefEq.respectTransparency.types false in
/-- A flat surjective morphism of schemes is an epimorphism in the category of schemes. -/
@[stacks 02VW]
/--
lemma `epi_of_flat_of_surjective` / 引理 `epi_of_flat_of_surjective`

English:
lemma epi_of_flat_of_surjective
  given: (f : X ⟶ Y) [Flat f] [Surjective f]
  statement: Epi f
  proof: by
  apply CategoryTheory.Functor.epi_of_epi_map (Scheme.forgetToLocallyRingedSpace)
  apply CategoryTheory.Functor.epi_of_epi_map (LocallyRingedSpace.forgetToSheafedSpace)
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _ ‹Surjective f›.surj
  intro x
  apply ConcreteCategory.mono_of_injective
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

中文:
引理 epi_of_flat_of_surjective
  条件: (f : X ⟶ Y) [平坦 f] [满射 f]
  结论: 满态射 f
  证明: by
  apply CategoryTheory.Functor.epi_of_epi_map (Scheme.forgetToLocallyRingedSpace)
  apply CategoryTheory.Functor.epi_of_epi_map (LocallyRingedSpace.forgetToSheafedSpace)
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _ ‹Surjective f›.surj
  intro x
  apply ConcreteCategory.mono_of_injective
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.epi_of_epi_map, ConcreteCategory, ConcreteCategory.mono_of_injective, FaithfullyFlat, Flat.stalkMap, Functor, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace, Module, Module.FaithfullyFlat, Module.FaithfullyFlat.of_flat_of_isLocalHom, Scheme, Scheme.forgetToLocallyRingedSpace, SheafedSpace, SheafedSpace.epi_of_base_surjective_of_stalk_mono, Surjective, X.presheaf.stalk, Y.presheaf.stalk, algebraize
-/
lemma epi_of_flat_of_surjective (f : X ⟶ Y) [Flat f] [Surjective f] : Epi f := by
  apply CategoryTheory.Functor.epi_of_epi_map (Scheme.forgetToLocallyRingedSpace)
  apply CategoryTheory.Functor.epi_of_epi_map (LocallyRingedSpace.forgetToSheafedSpace)
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _ ‹Surjective f›.surj
  intro x
  apply ConcreteCategory.mono_of_injective
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `flat_and_surjective_iff_faithfullyFlat_of_isAffine` / 引理 `flat_and_surjective_iff_faithfullyFlat_of_isAffine`

English:
lemma flat_and_surjective_iff_faithfullyFlat_of_isAffine
  given: [IsAffine X] [IsAffine Y]
  proof: by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]; rw [MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine f)]; rw [MorphismProperty.arrow_mk_iso_iff @Flat (arrowIsoSpecΓOfIsAffine f)]; rw [← HasRingHomProperty.Spec_iff (P := @Flat)]; rw [surjective_iff]
  rfl

中文:
引理 flat_and_surjective_iff_faithfullyFlat_of_isAffine
  条件: [是仿射 X] [是仿射 Y]
  证明: by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]; rw [MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine f)]; rw [MorphismProperty.arrow_mk_iso_iff @Flat (arrowIsoSpecΓOfIsAffine f)]; rw [← HasRingHomProperty.Spec_iff (P := @Flat)]; rw [surjective_iff]
  rfl

Depends on / 依赖: FaithfullyFlat, HasRingHomProperty, HasRingHomProperty.Spec_iff, MorphismProperty, MorphismProperty.arrow_mk_iso_iff, RingHom, RingHom.FaithfullyFlat.iff_flat_and_comap_surjective, Spec_iff, Surjective, arrow_mk_iso_iff, iff_flat_and_comap_surjective, surjective_iff
-/
lemma flat_and_surjective_iff_faithfullyFlat_of_isAffine [IsAffine X] [IsAffine Y] :
    Flat f ∧ Surjective f ↔ f.appTop.hom.FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]; rw [MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine f)]; rw [MorphismProperty.arrow_mk_iso_iff @Flat (arrowIsoSpecΓOfIsAffine f)]; rw [← HasRingHomProperty.Spec_iff (P := @Flat)]; rw [surjective_iff]
  rfl

end Flat

/--
lemma `Scheme.Hom.flat_appTop` / 引理 `Scheme.Hom.flat_appTop`

English:
lemma Scheme.Hom.flat_appTop
  given: [IsAffine X] [IsAffine Y] [Flat f]
  proof: HasRingHomProperty.appTop (P := @Flat) _ inferInstance

中文:
引理 概形.态射.flat_appTop
  条件: [是仿射 X] [是仿射 Y] [平坦 f]
  证明: HasRingHomProperty.appTop (P := @Flat) _ inferInstance

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.appTop, appTop
-/
lemma Scheme.Hom.flat_appTop [IsAffine X] [IsAffine Y] [Flat f] :
    f.appTop.hom.Flat :=
  HasRingHomProperty.appTop (P := @Flat) _ inferInstance

/--
lemma `flat_and_surjective_SpecMap_iff` / 引理 `flat_and_surjective_SpecMap_iff`

English:
lemma flat_and_surjective_SpecMap_iff
  given: {R S : CommRingCat.{u}} (f : R ⟶ S)
  proof: by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]; rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]; rw [surjective_iff]
  rfl

中文:
引理 flat_and_surjective_SpecMap_iff
  条件: {R S : 交换环范畴.{u}} (f : R ⟶ S)
  证明: by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]; rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]; rw [surjective_iff]
  rfl

Depends on / 依赖: FaithfullyFlat, HasRingHomProperty, HasRingHomProperty.Spec_iff, RingHom, RingHom.FaithfullyFlat.iff_flat_and_comap_surjective, Spec_iff, iff_flat_and_comap_surjective, surjective_iff
-/
lemma flat_and_surjective_SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Flat (Spec.map f) ∧ Surjective (Spec.map f) ↔ f.hom.FaithfullyFlat := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]; rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]; rw [surjective_iff]
  rfl

section sections

/-!
## Sections of fibered products

Suppose we are given the following cartesian square:
```
Y --g-→ X
| |
iY iX
↓ |
T --f-→ S
```
Let `Uₛ` be an open of `S`, `Uₓ` and `Uₜ` be opens of `X` and `T` mapping into `Uₛ`.
There is a canonical map `Γ(X, Uₓ) ⊗[Γ(S, Uₛ)] Γ(T, Uₜ) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ Uₓ ∩ pr₂ ⁻¹ Uₜ)`.

We show that this map is
1. `isIso_pushoutSection_of_isAffineOpen`:
  bijective when `Uₛ`, `Uₜ`, and `Uₓ` are all affine.
2. `mono_pushoutSection_of_isCompact_of_flat_right`:
  injective when `Uₛ`, `Uₜ` are affine, `Uₓ` is compact, and `f` is flat.
3. `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`:
  bijective when `Uₛ`, `Uₜ` are affine, `Uₓ` is qcqs, and `f` is flat.
4. `mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`:
  injective when `Uₛ` is affine, `Uₜ` is compact, `Uₓ` is qcqs, `f` is flat,
  and `Γ(T, Uₜ)` is flat over `Γ(S, Uₛ)` (typically true when `S = Spec k`.)
5. `isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`:
  bijective when `Uₛ` is affine, `Uₜ` and `Uₓ` are qcqs, `f` is flat,
  and `Γ(T, Uₜ)` is flat over `Γ(S, Uₛ)` (typically true when `S = Spec k`.)

-/

variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
  (H : IsPullback g iY iX f)
  {US : S.Opens} {UT : T.Opens}
  {UX : X.Opens} (hUST : UT <= f ⁻¹ᵁ US) (hUSX : UX <= iX ⁻¹ᵁ US)
  {UY : Y.Opens} (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)

/--
Definition of `pushoutSection` / `pushoutSection` 的定义

English:
abbreviation pushoutSection
  signature: : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ⟶ Γ(Y, UY)
  body: pushout.desc (g.appLE UX UY (by simp [*])) (iY.appLE UT UY (by simp [*]))
    (by simp only [Scheme.Hom.appLE_comp_appLE, H.w])

中文:
缩写 pushoutSection
  签名: : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ⟶ Γ(Y, UY)
  定义体: pushout.desc (g.appLE UX UY (by simp [*])) (iY.appLE UT UY (by simp [*]))
    (by simp only [Scheme.Hom.appLE_comp_appLE, H.w])

Depends on / 依赖: Scheme, Scheme.Hom.appLE_comp_appLE, appLE_comp_appLE, g.appLE, iY.appLE, pushout, pushout.desc
-/
abbrev pushoutSection : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ⟶ Γ(Y, UY) :=
  pushout.desc (g.appLE UX UY (by simp [*])) (iY.appLE UT UY (by simp [*]))
    (by simp only [Scheme.Hom.appLE_comp_appLE, H.w])

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_pushoutSection_iff` / 引理 `isIso_pushoutSection_iff`

English:
lemma isIso_pushoutSection_iff
  proof: ⟨fun _ => .of_iso (.of_hasPushout _ _) (.refl _) (.refl _) (.refl _)
    (asIso (pushoutSection H hUST hUSX hUY)) (by simp) (by simp) (by simp) (by simp),
    fun h => inferInstanceAs (IsIso h.isoPushout.inv)⟩

中文:
引理 isIso_pushoutSection_iff
  证明: ⟨fun _ => .of_iso (.of_hasPushout _ _) (.refl _) (.refl _) (.refl _)
    (asIso (pushoutSection H hUST hUSX hUY)) (by simp) (by simp) (by simp) (by simp),
    fun h => inferInstanceAs (IsIso h.isoPushout.inv)⟩

Depends on / 依赖: h.isoPushout.inv, isoPushout, of_hasPushout, of_iso, pushoutSection
-/
lemma isIso_pushoutSection_iff :
    IsIso (pushoutSection H hUST hUSX hUY) ↔ IsPushout (iX.appLE US UX hUSX) (f.appLE US UT hUST)
      (g.appLE UX UY (by simp [*])) (iY.appLE UT UY (by simp [*])) :=
  ⟨fun _ => .of_iso (.of_hasPushout _ _) (.refl _) (.refl _) (.refl _)
    (asIso (pushoutSection H hUST hUSX hUY)) (by simp) (by simp) (by simp) (by simp),
    fun h => inferInstanceAs (IsIso h.isoPushout.inv)⟩

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] IsAffineOpen.isoSpec_hom in
attribute [local simp← ] Scheme.Hom.resLE_eq_morphismRestrict in
/--
lemma `isIso_pushoutSection_of_isAffineOpen` / 引理 `isIso_pushoutSection_of_isAffineOpen`

English:
lemma isIso_pushoutSection_of_isAffineOpen
  statement: (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
  proof: by
  refine (isIso_pushoutSection_iff ..).mpr (IsPullback.of_map_of_faithful Scheme.Spec ?_).unop
  have : IsAffine _ := hUS
  have : IsAffine _ := hUT
  have : IsAffine _ := hUX
  have hUY' : IsAffineOpen UY :=
    .of_isIso (Scheme.Hom.isPullback_resLE H hUST hUSX hUY).isoPullback.hom
  exact .of_iso (Scheme.Hom.isPullback_resLE H hUST hUSX hUY).flip hUY'.isoSpec hUT.isoSpec
    hUX.isoSpec hUS.isoSpec (by simp) (by simp) (by simp) (by simp)

中文:
引理 isIso_pushoutSection_of_isAffineOpen
  结论: (hUS : 是仿射开集 US) (hUT : 是仿射开集 UT)
  证明: by
  refine (isIso_pushoutSection_iff ..).mpr (IsPullback.of_map_of_faithful Scheme.Spec ?_).unop
  have : IsAffine _ := hUS
  have : IsAffine _ := hUT
  have : IsAffine _ := hUX
  have hUY' : IsAffineOpen UY :=
    .of_isIso (Scheme.Hom.isPullback_resLE H hUST hUSX hUY).isoPullback.hom
  exact .of_iso (Scheme.Hom.isPullback_resLE H hUST hUSX hUY).flip hUY'.isoSpec hUT.isoSpec
    hUX.isoSpec hUS.isoSpec (by simp) (by simp) (by simp) (by simp)

Depends on / 依赖: IsAffine, IsAffineOpen, IsPullback, IsPullback.of_map_of_faithful, Scheme, Scheme.Hom.isPullback_resLE, Scheme.Spec, hUS.isoSpec, hUT.isoSpec, hUX.isoSpec, isIso_pushoutSection_iff, isPullback_resLE, isoPullback, isoPullback.hom, isoSpec, of_isIso, of_iso, of_map_of_faithful
-/
lemma isIso_pushoutSection_of_isAffineOpen (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hUX : IsAffineOpen UX) : IsIso (pushoutSection H hUST hUSX hUY) := by
  refine (isIso_pushoutSection_iff ..).mpr (IsPullback.of_map_of_faithful Scheme.Spec ?_).unop
  have : IsAffine _ := hUS
  have : IsAffine _ := hUT
  have : IsAffine _ := hUX
  have hUY' : IsAffineOpen UY :=
    .of_isIso (Scheme.Hom.isPullback_resLE H hUST hUSX hUY).isoPullback.hom
  exact .of_iso (Scheme.Hom.isPullback_resLE H hUST hUSX hUY).flip hUY'.isoSpec hUT.isoSpec
    hUX.isoSpec hUS.isoSpec (by simp) (by simp) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
/--
lemma `mono_pushoutSection_of_iSup_eq` / 引理 `mono_pushoutSection_of_iSup_eq`

English:
lemma mono_pushoutSection_of_iSup_eq
  statement: {ι : Type*} [Finite ι] (VX : ι -> X.Opens) (hVU : iSup VX = UX)
  proof: by
  /-
  We shall show that `Γ(T, Uₜ) ⊗[Γ(S, Uₛ)] Γ(X, U) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ U ∩ pr₂ ⁻¹ Uₜ)` is
  injective using the following diagram
  ```
  Γ(T, Uₜ) ⊗ Γ(X, U) ------→ Γ(T, Uₜ) ⊗ ∏ᵢ Γ(X, Vᵢ)
           | |
           ↓ ↓
  Γ(X ×ₛ T, U ∩ Uₜ) ------→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)
  ```
  -/
  have (i : _) : VX i <= iX ⁻¹ᵁ US := by clear hV; aesop
  classical
  algebraize [(iX.appLE US UX hUSX).hom, (f.appLE US UT hUST).hom]
  let (i : _) := (iX.appLE US (VX i) (by aesop)).hom.toAlgebra
  -- This is the map `Γ(X ×ₛ T, U ∩ Uₜ) ⟶ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)` on the bottom.
  let ψY : Γ(Y, UY) ->+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) := RingHom.pi fun i =>
      (Y.presheaf.map (homOfLE (by subst hUY hVU; gcongr; exact le_iSup _ _)).op).hom
  -- The map `Γ(X, U) ⟶ ∏ᵢ Γ(X, Vᵢ)`
  let ψ : Γ(X, UX) ->ₐ[Γ(S, US)] Π i, Γ(X, VX i) := AlgHom.pi fun i =>
    ⟨(X.presheaf.map (homOfLE (hVU ▸ le_iSup VX i)).op).hom, fun r => by
      dsimp [RingHom.algebraMap_toAlgebra]
      simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]⟩
  -- ... is injective by the sheaf axiom,
  have hψ : Function.Injective ψ := by
    intro s t est
    apply X.IsSheaf.section_ext fun x hx => ?_
    simp only [← hVU, Opens.mem_iSup] at hx
    obtain ⟨i, hxi⟩ := hx
    exact ⟨_, _, hxi, congr($est i)⟩
  -- ... and remains injective after tensoring with `Γ(T, Uₜ)` by the flatness assumption.
  have hψ' : Function.Injective (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ.toLinearMap hψ
  simp_rw [@ConcreteCategory.mono_iff_injective_of_preservesPullback] at hV ⊢
  cases nonempty_fintype ι
  -- And the map at the right
  let φ : (Γ(T, UT) otimes[Γ(S, US)] Π i, Γ(X, VX i)) ->+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) :=
    (RingHom.pi fun i => (pushoutSection H hUST (show VX i <= _ by aesop) rfl).hom.comp
      ((CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.hom.hom.comp
      (by exact Pi.evalRingHom _ _))).comp (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).toRingHom
  -- ... is also injective by our hypotheses on `Vᵢ`.
  have hφ : Function.Injective φ := by
    dsimp [φ]
    refine .comp ?_ (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).injective
exact .piMap fun i => (hV _).comp CommRingCat.isPushout_tensorProduct _ _ _
.flip.isoPushout.commRingCatIsoToRingEquiv.injective
  let e : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ≅
      .of (Γ(T, UT) otimes[Γ(S, US)] Γ(X, UX)) :=
    (CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.symm
  -- It remains to check that the square indeed commutes, and we may conclude that the map
  -- at the left is also injective.
  suffices (ψY.comp (pushoutSection H hUST hUSX hUY).hom).comp e.inv.hom = φ.comp
      (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ).toRingHom by
    refine .of_comp (f := ψY) ?_
    convert (hφ.comp hψ').comp e.commRingCatIsoToRingEquiv.injective
    ext1 x; simpa using! congr($this (e.hom x))
  ext1
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeLeftRingHom =
        (pushout.inr (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inr_isoPushout_hom).hom)
    have H₂ (x j) : φ (x otimesₜ[↑Γ(S, US)] 1) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inr (C := CommRingCat) _ _ x) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inr_isoPushout_hom) x))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, ← CategoryTheory.comp_apply, pushoutSection]
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeRight.toRingHom =
        (pushout.inl (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inl_isoPushout_hom).hom)
    have H₂ (x j) : φ (1 otimesₜ[↑Γ(S, US)] x) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inl (C := CommRingCat) _ _ (x j)) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inl_isoPushout_hom) (x j)))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, -CommRingCat.hom_comp, ← CategoryTheory.comp_apply, pushoutSection, ψ]

中文:
引理 mono_pushoutSection_of_iSup_eq
  结论: {ι : 类型} [有限 ι] (VX : ι -> X.Opens) (hVU : iSup VX = UX)
  证明: by
  /-
  We shall show that `Γ(T, Uₜ) ⊗[Γ(S, Uₛ)] Γ(X, U) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ U ∩ pr₂ ⁻¹ Uₜ)` is
  injective using the following diagram
  ```
  Γ(T, Uₜ) ⊗ Γ(X, U) ------→ Γ(T, Uₜ) ⊗ ∏ᵢ Γ(X, Vᵢ)
           | |
           ↓ ↓
  Γ(X ×ₛ T, U ∩ Uₜ) ------→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)
  ```
  -/
  have (i : _) : VX i <= iX ⁻¹ᵁ US := by clear hV; aesop
  classical
  algebraize [(iX.appLE US UX hUSX).hom, (f.appLE US UT hUST).hom]
  let (i : _) := (iX.appLE US (VX i) (by aesop)).hom.toAlgebra
  -- This is the map `Γ(X ×ₛ T, U ∩ Uₜ) ⟶ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)` on the bottom.
  let ψY : Γ(Y, UY) ->+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) := RingHom.pi fun i =>
      (Y.presheaf.map (homOfLE (by subst hUY hVU; gcongr; exact le_iSup _ _)).op).hom
  -- The map `Γ(X, U) ⟶ ∏ᵢ Γ(X, Vᵢ)`
  let ψ : Γ(X, UX) ->ₐ[Γ(S, US)] Π i, Γ(X, VX i) := AlgHom.pi fun i =>
    ⟨(X.presheaf.map (homOfLE (hVU ▸ le_iSup VX i)).op).hom, fun r => by
      dsimp [RingHom.algebraMap_toAlgebra]
      simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]⟩
  -- ... is injective by the sheaf axiom,
  have hψ : Function.Injective ψ := by
    intro s t est
    apply X.IsSheaf.section_ext fun x hx => ?_
    simp only [← hVU, Opens.mem_iSup] at hx
    obtain ⟨i, hxi⟩ := hx
    exact ⟨_, _, hxi, congr($est i)⟩
  -- ... and remains injective after tensoring with `Γ(T, Uₜ)` by the flatness assumption.
  have hψ' : Function.Injective (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ.toLinearMap hψ
  simp_rw [@ConcreteCategory.mono_iff_injective_of_preservesPullback] at hV ⊢
  cases nonempty_fintype ι
  -- And the map at the right
  let φ : (Γ(T, UT) otimes[Γ(S, US)] Π i, Γ(X, VX i)) ->+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) :=
    (RingHom.pi fun i => (pushoutSection H hUST (show VX i <= _ by aesop) rfl).hom.comp
      ((CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.hom.hom.comp
      (by exact Pi.evalRingHom _ _))).comp (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).toRingHom
  -- ... is also injective by our hypotheses on `Vᵢ`.
  have hφ : Function.Injective φ := by
    dsimp [φ]
    refine .comp ?_ (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).injective
exact .piMap fun i => (hV _).comp CommRingCat.isPushout_tensorProduct _ _ _
.flip.isoPushout.commRingCatIsoToRingEquiv.injective
  let e : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ≅
      .of (Γ(T, UT) otimes[Γ(S, US)] Γ(X, UX)) :=
    (CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.symm
  -- It remains to check that the square indeed commutes, and we may conclude that the map
  -- at the left is also injective.
  suffices (ψY.comp (pushoutSection H hUST hUSX hUY).hom).comp e.inv.hom = φ.comp
      (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ).toRingHom by
    refine .of_comp (f := ψY) ?_
    convert (hφ.comp hψ').comp e.commRingCatIsoToRingEquiv.injective
    ext1 x; simpa using! congr($this (e.hom x))
  ext1
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeLeftRingHom =
        (pushout.inr (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inr_isoPushout_hom).hom)
    have H₂ (x j) : φ (x otimesₜ[↑Γ(S, US)] 1) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inr (C := CommRingCat) _ _ x) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inr_isoPushout_hom) x))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, ← CategoryTheory.comp_apply, pushoutSection]
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeRight.toRingHom =
        (pushout.inl (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inl_isoPushout_hom).hom)
    have H₂ (x j) : φ (1 otimesₜ[↑Γ(S, US)] x) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inl (C := CommRingCat) _ _ (x j)) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inl_isoPushout_hom) (x j)))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, -CommRingCat.hom_comp, ← CategoryTheory.comp_apply, pushoutSection, ψ]
-/
lemma mono_pushoutSection_of_iSup_eq {ι : Type*} [Finite ι] (VX : ι -> X.Opens) (hVU : iSup VX = UX)
    (hV : forall i, Mono (pushoutSection H hUST (show VX i <= _ by aesop) rfl))
    (hT : (f.appLE US UT hUST).hom.Flat) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  /-
  We shall show that `Γ(T, Uₜ) ⊗[Γ(S, Uₛ)] Γ(X, U) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ U ∩ pr₂ ⁻¹ Uₜ)` is
  injective using the following diagram
  ```
  Γ(T, Uₜ) ⊗ Γ(X, U) ------→ Γ(T, Uₜ) ⊗ ∏ᵢ Γ(X, Vᵢ)
           | |
           ↓ ↓
  Γ(X ×ₛ T, U ∩ Uₜ) ------→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)
  ```
  -/
  have (i : _) : VX i <= iX ⁻¹ᵁ US := by clear hV; aesop
  classical
  algebraize [(iX.appLE US UX hUSX).hom, (f.appLE US UT hUST).hom]
  let (i : _) := (iX.appLE US (VX i) (by aesop)).hom.toAlgebra
  -- This is the map `Γ(X ×ₛ T, U ∩ Uₜ) ⟶ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ)` on the bottom.
  let ψY : Γ(Y, UY) ->+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) := RingHom.pi fun i =>
      (Y.presheaf.map (homOfLE (by subst hUY hVU; gcongr; exact le_iSup _ _)).op).hom
  -- The map `Γ(X, U) ⟶ ∏ᵢ Γ(X, Vᵢ)`
  let ψ : Γ(X, UX) ->ₐ[Γ(S, US)] Π i, Γ(X, VX i) := AlgHom.pi fun i =>
    ⟨(X.presheaf.map (homOfLE (hVU ▸ le_iSup VX i)).op).hom, fun r => by
      dsimp [RingHom.algebraMap_toAlgebra]
      simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]⟩
  -- ... is injective by the sheaf axiom,
  have hψ : Function.Injective ψ := by
    intro s t est
    apply X.IsSheaf.section_ext fun x hx => ?_
    simp only [← hVU, Opens.mem_iSup] at hx
    obtain ⟨i, hxi⟩ := hx
    exact ⟨_, _, hxi, congr($est i)⟩
  -- ... and remains injective after tensoring with `Γ(T, Uₜ)` by the flatness assumption.
  have hψ' : Function.Injective (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ) :=
    Module.Flat.lTensor_preserves_injective_linearMap ψ.toLinearMap hψ
  simp_rw [@ConcreteCategory.mono_iff_injective_of_preservesPullback] at hV ⊢
  cases nonempty_fintype ι
  -- And the map at the right
  let φ : (Γ(T, UT) otimes[Γ(S, US)] Π i, Γ(X, VX i)) ->+* Π i, Γ(Y, g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT) :=
    (RingHom.pi fun i => (pushoutSection H hUST (show VX i <= _ by aesop) rfl).hom.comp
      ((CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.hom.hom.comp
      (by exact Pi.evalRingHom _ _))).comp (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).toRingHom
  -- ... is also injective by our hypotheses on `Vᵢ`.
  have hφ : Function.Injective φ := by
    dsimp [φ]
    refine .comp ?_ (Algebra.TensorProduct.piRight _ Γ(S, US) _ _).injective
exact .piMap fun i => (hV _).comp CommRingCat.isPushout_tensorProduct _ _ _
.flip.isoPushout.commRingCatIsoToRingEquiv.injective
  let e : pushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) ≅
      .of (Γ(T, UT) otimes[Γ(S, US)] Γ(X, UX)) :=
    (CommRingCat.isPushout_tensorProduct _ _ _).flip.isoPushout.symm
  -- It remains to check that the square indeed commutes, and we may conclude that the map
  -- at the left is also injective.
  suffices (ψY.comp (pushoutSection H hUST hUSX hUY).hom).comp e.inv.hom = φ.comp
      (Algebra.TensorProduct.map (AlgHom.id Γ(T, UT) Γ(T, UT)) ψ).toRingHom by
    refine .of_comp (f := ψY) ?_
    convert (hφ.comp hψ').comp e.commRingCatIsoToRingEquiv.injective
    ext1 x; simpa using! congr($this (e.hom x))
  ext1
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeLeftRingHom =
        (pushout.inr (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inr_isoPushout_hom).hom)
    have H₂ (x j) : φ (x otimesₜ[↑Γ(S, US)] 1) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inr (C := CommRingCat) _ _ x) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inr_isoPushout_hom) x))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, ← CategoryTheory.comp_apply, pushoutSection]
  · have H₁ : e.inv.hom.comp Algebra.TensorProduct.includeRight.toRingHom =
        (pushout.inl (C := CommRingCat) _ _).hom :=
      congr($((CommRingCat.isPushout_tensorProduct _ _ _).flip.inl_isoPushout_hom).hom)
    have H₂ (x j) : φ (1 otimesₜ[↑Γ(S, US)] x) j = pushoutSection H hUST (UX := VX j) (by simp_all) rfl
        (pushout.inl (C := CommRingCat) _ _ (x j)) := congr(pushoutSection H hUST (UX := VX j) _ rfl
        ($((CommRingCat.isPushout_tensorProduct ↑Γ(S, US)
          ↑Γ(T, UT) ↑Γ(X, VX j)).flip.inl_isoPushout_hom) (x j)))
    simp only [RingHom.comp_assoc, H₁]
    ext x j
    simp [ψY, H₂, -CommRingCat.hom_comp, ← CategoryTheory.comp_apply, pushoutSection, ψ]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_pushoutSection_of_iSup_eq` / 引理 `isIso_pushoutSection_of_iSup_eq`

English:
lemma isIso_pushoutSection_of_iSup_eq
  proof: by
  classical
  /-
  We shall show that `Γ(T, Uₜ) ⊗[Γ(S, Uₛ)] Γ(X, U) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ U ∩ pr₂ ⁻¹ Uₜ)` is
  injective using the following diagram
  ```
  0 → Γ(T, Uₜ) ⊗ Γ(X, U) ------→ Γ(T, Uₜ) ⊗ ∏ᵢ Γ(X, Vᵢ) ---→ Γ(T, Uₜ) ⊗ ∏ᵢⱼ Γ(X, Vᵢ ∩ Vⱼ)
           | | |
           ↓ ↓ ↓
  0 → Γ(X ×ₛ T, U ∩ Uₜ) ------→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ) ---→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Vⱼ ∩ Uₜ)
  ```
  The two rows are exact because of the sheaf axiom (and additionally the flatness assumption for
  the top row). The vertical arrow in the middle is an isomorphism by assumption, and the one
  one the right is monomorphic by assumption. Hence the left arrow is also an isomorphism.

  In the actual proof we use `Pairwise`-indexed diagrams instead of nested limits because it works
  better with the existing API.
  -/
  -- The diagram consisting of `Γ(X, Vᵢ) ⟶ Γ(X, Vᵢ ∩ Vⱼ)`.
  let D := Pairwise.diagram VX
  have h : iSup D.obj = UX := by
    refine le_antisymm (iSup_le_iff.mpr ?_) ?_
    · subst hVU; rintro (i | ⟨i, j⟩); exacts [le_iSup VX _, inf_le_left.trans (le_iSup VX _)]
    · subst hVU; exact iSup_le_iff.mpr fun i => le_iSup D.obj (.single i)
  let c₀ : Cocone D := (colimit.cocone _).extend
    (eqToIso (Y := UX) (by simpa [CompleteLattice.colimit_eq_iSup])).hom
  -- The diagram consisting of `Γ(T, Uₜ) ⊗ Γ(X, Vᵢ) ⟶ Γ(T, Uₜ) ⊗ Γ(X, Vᵢ ∩ Vⱼ)`.
  let F := Under.lift _ ((Functor.const _).map (iX.appLE US UX hUSX) ≫
    ((X.presheaf.mapCone c₀.op).π)) ⋙ Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _
  let G : X.Opens ⥤ Y.Opens :=
    { obj U := g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ UT, map h := homOfLE (by gcongr; exact h.le) }
  -- The natural transformation between the diagrams at the top and bottom.
  let αF : F ⟶ D.op ⋙ G.op ⋙ Y.presheaf :=
  { app i := (pushout.congrHom (by simp) rfl).hom ≫
      pushoutSection H hUST (by grw [← hUSX, ← h]; exact le_iSup D.obj i.unop) rfl }
  -- `Γ(T, Uₜ) ⊗ Γ(X, U)` as a (limit) cone over the top diagram.
  let c : Cone F := (Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _).mapCone
    (Under.liftCone (X.presheaf.mapCone c₀.op) _)
  have := CommRingCat.Under.preservesFiniteLimits_of_flat _ hT
  cases nonempty_fintype ι
  let hc : IsLimit c :=
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections
      _).mp X.IsSheaf VX).preserves (c := c₀.op)
    haveI HX := (HX (IsColimit.extendIso _ (colimit.isColimit _)).op).some
    isLimitOfPreserves (Under.pushout _ ⋙ Under.forget _) (Under.isLimitLiftCone _ _ HX)
  let c'₀ : Cocone (D ⋙ G) := (colimit.cocone _).extend
    (eqToIso (Y := UY) (by
      simp only [colimit.cocone_x, CompleteLattice.colimit_eq_iSup]
      eta_expand
      dsimp [G]
      rw [← iSup_inf_eq]; rw [← Scheme.Hom.preimage_iSup]; rw [h]; rw [hUY])).hom
  -- `Γ(X ×ₛ T, U ∩ Uₜ)` as a (limit) cone over the bottom diagram.
  let c' : Cone (D.op ⋙ G.op ⋙ Y.presheaf) := Y.presheaf.mapCone c'₀.op
  let hc' : IsLimit c' := by
    letI e : D ⋙ G ≅ Pairwise.diagram fun i => g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT :=
      NatIso.ofComponents (fun | .single i => .refl _ | .pair i j => eqToIso (by
        dsimp [D, G]; rw [Scheme.Hom.preimage_inf, inf_inf_distrib_right]))
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections _).mp
      Y.IsSheaf (fun i => g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT)).preserves
        (c := ((Cocone.precompose e.inv).obj c'₀).op)
    exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight (NatIso.op e.symm) Y.presheaf) _)
      ((HX ((IsColimit.precomposeInvEquiv e _).symm
        (IsColimit.extendIso _ (colimit.isColimit _))).op).some.ofIsoLimit (Cone.ext (.refl _)))
  have HαF₂ (i j : _) : Mono (αF.app (.op <| .pair i j)) := by infer_instance
  -- We construct the morphisms between the cone points,
  let f₁ : c.pt ⟶ c'.pt := hc'.lift ((Cone.postcompose αF).obj c)
  let f₂ : c'.pt ⟶ c.pt := hc.lift ⟨c'.pt, ⟨fun
    | .op (.single i) => c'.π.app _ ≫ inv (αF.app (.op <| .single i))
    | .op (.pair i j) => c'.π.app (.op (.single i)) ≫ inv (αF.app (.op <| .single i)) ≫
        F.map (Quiver.Hom.op <| Pairwise.Hom.left i j), by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain ⟨i | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩, rfl⟩ :=
      (show Function.Surjective Quiver.Hom.op from Quiver.Hom.opEquiv.surjective) f
    · simp [show Pairwise.Hom.id_single i = 𝟙 (Pairwise.single i) from rfl]
    · simp [show Pairwise.Hom.id_pair i j = 𝟙 (Pairwise.pair i j) from rfl]
    · simp
    · rw [← cancel_mono (αF.app _)]
      simpa using (c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)).trans
        (c'.w (Quiver.Hom.op <| Pairwise.Hom.right i j)).symm⟩⟩
  -- and prove that they form an isomorphism.
  let e : c.pt ≅ c'.pt := by
    refine ⟨f₁, f₂, hc.hom_ext ?_, hc'.hom_ext ?_⟩
    · rintro ⟨i | ⟨i, j⟩⟩ <;> simp [f₁, f₂]
    · rintro ⟨i | ⟨i, j⟩⟩
      · simp [f₁, f₂]
      · simpa [f₁, f₂] using c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)
  convert! e.isIso_hom using 1
  · refine hc'.hom_ext fun i => ?_
    rw [hc'.fac]
    ext1
    · simp [αF, c, Under.liftCone, c', c₀]
    · simp [αF, c, c']

中文:
引理 isIso_pushoutSection_of_iSup_eq
  证明: by
  classical
  /-
  We shall show that `Γ(T, Uₜ) ⊗[Γ(S, Uₛ)] Γ(X, U) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ U ∩ pr₂ ⁻¹ Uₜ)` is
  injective using the following diagram
  ```
  0 → Γ(T, Uₜ) ⊗ Γ(X, U) ------→ Γ(T, Uₜ) ⊗ ∏ᵢ Γ(X, Vᵢ) ---→ Γ(T, Uₜ) ⊗ ∏ᵢⱼ Γ(X, Vᵢ ∩ Vⱼ)
           | | |
           ↓ ↓ ↓
  0 → Γ(X ×ₛ T, U ∩ Uₜ) ------→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ) ---→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Vⱼ ∩ Uₜ)
  ```
  The two rows are exact because of the sheaf axiom (and additionally the flatness assumption for
  the top row). The vertical arrow in the middle is an isomorphism by assumption, and the one
  one the right is monomorphic by assumption. Hence the left arrow is also an isomorphism.

  In the actual proof we use `Pairwise`-indexed diagrams instead of nested limits because it works
  better with the existing API.
  -/
  -- The diagram consisting of `Γ(X, Vᵢ) ⟶ Γ(X, Vᵢ ∩ Vⱼ)`.
  let D := Pairwise.diagram VX
  have h : iSup D.obj = UX := by
    refine le_antisymm (iSup_le_iff.mpr ?_) ?_
    · subst hVU; rintro (i | ⟨i, j⟩); exacts [le_iSup VX _, inf_le_left.trans (le_iSup VX _)]
    · subst hVU; exact iSup_le_iff.mpr fun i => le_iSup D.obj (.single i)
  let c₀ : Cocone D := (colimit.cocone _).extend
    (eqToIso (Y := UX) (by simpa [CompleteLattice.colimit_eq_iSup])).hom
  -- The diagram consisting of `Γ(T, Uₜ) ⊗ Γ(X, Vᵢ) ⟶ Γ(T, Uₜ) ⊗ Γ(X, Vᵢ ∩ Vⱼ)`.
  let F := Under.lift _ ((Functor.const _).map (iX.appLE US UX hUSX) ≫
    ((X.presheaf.mapCone c₀.op).π)) ⋙ Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _
  let G : X.Opens ⥤ Y.Opens :=
    { obj U := g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ UT, map h := homOfLE (by gcongr; exact h.le) }
  -- The natural transformation between the diagrams at the top and bottom.
  let αF : F ⟶ D.op ⋙ G.op ⋙ Y.presheaf :=
  { app i := (pushout.congrHom (by simp) rfl).hom ≫
      pushoutSection H hUST (by grw [← hUSX, ← h]; exact le_iSup D.obj i.unop) rfl }
  -- `Γ(T, Uₜ) ⊗ Γ(X, U)` as a (limit) cone over the top diagram.
  let c : Cone F := (Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _).mapCone
    (Under.liftCone (X.presheaf.mapCone c₀.op) _)
  have := CommRingCat.Under.preservesFiniteLimits_of_flat _ hT
  cases nonempty_fintype ι
  let hc : IsLimit c :=
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections
      _).mp X.IsSheaf VX).preserves (c := c₀.op)
    haveI HX := (HX (IsColimit.extendIso _ (colimit.isColimit _)).op).some
    isLimitOfPreserves (Under.pushout _ ⋙ Under.forget _) (Under.isLimitLiftCone _ _ HX)
  let c'₀ : Cocone (D ⋙ G) := (colimit.cocone _).extend
    (eqToIso (Y := UY) (by
      simp only [colimit.cocone_x, CompleteLattice.colimit_eq_iSup]
      eta_expand
      dsimp [G]
      rw [← iSup_inf_eq]; rw [← Scheme.Hom.preimage_iSup]; rw [h]; rw [hUY])).hom
  -- `Γ(X ×ₛ T, U ∩ Uₜ)` as a (limit) cone over the bottom diagram.
  let c' : Cone (D.op ⋙ G.op ⋙ Y.presheaf) := Y.presheaf.mapCone c'₀.op
  let hc' : IsLimit c' := by
    letI e : D ⋙ G ≅ Pairwise.diagram fun i => g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT :=
      NatIso.ofComponents (fun | .single i => .refl _ | .pair i j => eqToIso (by
        dsimp [D, G]; rw [Scheme.Hom.preimage_inf, inf_inf_distrib_right]))
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections _).mp
      Y.IsSheaf (fun i => g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT)).preserves
        (c := ((Cocone.precompose e.inv).obj c'₀).op)
    exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight (NatIso.op e.symm) Y.presheaf) _)
      ((HX ((IsColimit.precomposeInvEquiv e _).symm
        (IsColimit.extendIso _ (colimit.isColimit _))).op).some.ofIsoLimit (Cone.ext (.refl _)))
  have HαF₂ (i j : _) : Mono (αF.app (.op <| .pair i j)) := by infer_instance
  -- We construct the morphisms between the cone points,
  let f₁ : c.pt ⟶ c'.pt := hc'.lift ((Cone.postcompose αF).obj c)
  let f₂ : c'.pt ⟶ c.pt := hc.lift ⟨c'.pt, ⟨fun
    | .op (.single i) => c'.π.app _ ≫ inv (αF.app (.op <| .single i))
    | .op (.pair i j) => c'.π.app (.op (.single i)) ≫ inv (αF.app (.op <| .single i)) ≫
        F.map (Quiver.Hom.op <| Pairwise.Hom.left i j), by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain ⟨i | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩, rfl⟩ :=
      (show Function.Surjective Quiver.Hom.op from Quiver.Hom.opEquiv.surjective) f
    · simp [show Pairwise.Hom.id_single i = 𝟙 (Pairwise.single i) from rfl]
    · simp [show Pairwise.Hom.id_pair i j = 𝟙 (Pairwise.pair i j) from rfl]
    · simp
    · rw [← cancel_mono (αF.app _)]
      simpa using (c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)).trans
        (c'.w (Quiver.Hom.op <| Pairwise.Hom.right i j)).symm⟩⟩
  -- and prove that they form an isomorphism.
  let e : c.pt ≅ c'.pt := by
    refine ⟨f₁, f₂, hc.hom_ext ?_, hc'.hom_ext ?_⟩
    · rintro ⟨i | ⟨i, j⟩⟩ <;> simp [f₁, f₂]
    · rintro ⟨i | ⟨i, j⟩⟩
      · simp [f₁, f₂]
      · simpa [f₁, f₂] using c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)
  convert! e.isIso_hom using 1
  · refine hc'.hom_ext fun i => ?_
    rw [hc'.fac]
    ext1
    · simp [αF, c, Under.liftCone, c', c₀]
    · simp [αF, c, c']

Depends on / 依赖: classical
-/
lemma isIso_pushoutSection_of_iSup_eq
    {ι : Type u} [Finite ι] (VX : ι -> X.Opens) (hVU : iSup VX = UX)
    (hV : forall i, IsIso (pushoutSection H hUST (show VX i <= _ by aesop) rfl))
    (hV' : forall i j, Mono (pushoutSection H hUST
      (show VX i ⊓ VX j <= _ from inf_le_left.trans (by clear hV; aesop)) rfl))
    (hT : (f.appLE US UT hUST).hom.Flat) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  classical
  /-
  We shall show that `Γ(T, Uₜ) ⊗[Γ(S, Uₛ)] Γ(X, U) ⟶ Γ(X ×ₛ T, pr₁ ⁻¹ U ∩ pr₂ ⁻¹ Uₜ)` is
  injective using the following diagram
  ```
  0 → Γ(T, Uₜ) ⊗ Γ(X, U) ------→ Γ(T, Uₜ) ⊗ ∏ᵢ Γ(X, Vᵢ) ---→ Γ(T, Uₜ) ⊗ ∏ᵢⱼ Γ(X, Vᵢ ∩ Vⱼ)
           | | |
           ↓ ↓ ↓
  0 → Γ(X ×ₛ T, U ∩ Uₜ) ------→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Uₜ) ---→ ∏ᵢ Γ(X ×ₛ T, Vᵢ ∩ Vⱼ ∩ Uₜ)
  ```
  The two rows are exact because of the sheaf axiom (and additionally the flatness assumption for
  the top row). The vertical arrow in the middle is an isomorphism by assumption, and the one
  one the right is monomorphic by assumption. Hence the left arrow is also an isomorphism.

  In the actual proof we use `Pairwise`-indexed diagrams instead of nested limits because it works
  better with the existing API.
  -/
  -- The diagram consisting of `Γ(X, Vᵢ) ⟶ Γ(X, Vᵢ ∩ Vⱼ)`.
  let D := Pairwise.diagram VX
  have h : iSup D.obj = UX := by
    refine le_antisymm (iSup_le_iff.mpr ?_) ?_
    · subst hVU; rintro (i | ⟨i, j⟩); exacts [le_iSup VX _, inf_le_left.trans (le_iSup VX _)]
    · subst hVU; exact iSup_le_iff.mpr fun i => le_iSup D.obj (.single i)
  let c₀ : Cocone D := (colimit.cocone _).extend
    (eqToIso (Y := UX) (by simpa [CompleteLattice.colimit_eq_iSup])).hom
  -- The diagram consisting of `Γ(T, Uₜ) ⊗ Γ(X, Vᵢ) ⟶ Γ(T, Uₜ) ⊗ Γ(X, Vᵢ ∩ Vⱼ)`.
  let F := Under.lift _ ((Functor.const _).map (iX.appLE US UX hUSX) ≫
    ((X.presheaf.mapCone c₀.op).π)) ⋙ Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _
  let G : X.Opens ⥤ Y.Opens :=
    { obj U := g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ UT, map h := homOfLE (by gcongr; exact h.le) }
  -- The natural transformation between the diagrams at the top and bottom.
  let αF : F ⟶ D.op ⋙ G.op ⋙ Y.presheaf :=
  { app i := (pushout.congrHom (by simp) rfl).hom ≫
      pushoutSection H hUST (by grw [← hUSX, ← h]; exact le_iSup D.obj i.unop) rfl }
  -- `Γ(T, Uₜ) ⊗ Γ(X, U)` as a (limit) cone over the top diagram.
  let c : Cone F := (Under.pushout (f.appLE US UT hUST) ⋙ Under.forget _).mapCone
    (Under.liftCone (X.presheaf.mapCone c₀.op) _)
  have := CommRingCat.Under.preservesFiniteLimits_of_flat _ hT
  cases nonempty_fintype ι
  let hc : IsLimit c :=
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections
      _).mp X.IsSheaf VX).preserves (c := c₀.op)
    haveI HX := (HX (IsColimit.extendIso _ (colimit.isColimit _)).op).some
    isLimitOfPreserves (Under.pushout _ ⋙ Under.forget _) (Under.isLimitLiftCone _ _ HX)
  let c'₀ : Cocone (D ⋙ G) := (colimit.cocone _).extend
    (eqToIso (Y := UY) (by
      simp only [colimit.cocone_x, CompleteLattice.colimit_eq_iSup]
      eta_expand
      dsimp [G]
      rw [← iSup_inf_eq]; rw [← Scheme.Hom.preimage_iSup]; rw [h]; rw [hUY])).hom
  -- `Γ(X ×ₛ T, U ∩ Uₜ)` as a (limit) cone over the bottom diagram.
  let c' : Cone (D.op ⋙ G.op ⋙ Y.presheaf) := Y.presheaf.mapCone c'₀.op
  let hc' : IsLimit c' := by
    letI e : D ⋙ G ≅ Pairwise.diagram fun i => g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT :=
      NatIso.ofComponents (fun | .single i => .refl _ | .pair i j => eqToIso (by
        dsimp [D, G]; rw [Scheme.Hom.preimage_inf, inf_inf_distrib_right]))
    haveI HX := ((TopCat.Presheaf.isSheaf_iff_isSheafPreservesLimitPairwiseIntersections _).mp
      Y.IsSheaf (fun i => g ⁻¹ᵁ VX i ⊓ iY ⁻¹ᵁ UT)).preserves
        (c := ((Cocone.precompose e.inv).obj c'₀).op)
    exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight (NatIso.op e.symm) Y.presheaf) _)
      ((HX ((IsColimit.precomposeInvEquiv e _).symm
        (IsColimit.extendIso _ (colimit.isColimit _))).op).some.ofIsoLimit (Cone.ext (.refl _)))
  have HαF₂ (i j : _) : Mono (αF.app (.op <| .pair i j)) := by infer_instance
  -- We construct the morphisms between the cone points,
  let f₁ : c.pt ⟶ c'.pt := hc'.lift ((Cone.postcompose αF).obj c)
  let f₂ : c'.pt ⟶ c.pt := hc.lift ⟨c'.pt, ⟨fun
    | .op (.single i) => c'.π.app _ ≫ inv (αF.app (.op <| .single i))
    | .op (.pair i j) => c'.π.app (.op (.single i)) ≫ inv (αF.app (.op <| .single i)) ≫
        F.map (Quiver.Hom.op <| Pairwise.Hom.left i j), by
    rintro ⟨i⟩ ⟨j⟩ f
    obtain ⟨i | ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩, rfl⟩ :=
      (show Function.Surjective Quiver.Hom.op from Quiver.Hom.opEquiv.surjective) f
    · simp [show Pairwise.Hom.id_single i = 𝟙 (Pairwise.single i) from rfl]
    · simp [show Pairwise.Hom.id_pair i j = 𝟙 (Pairwise.pair i j) from rfl]
    · simp
    · rw [← cancel_mono (αF.app _)]
      simpa using (c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)).trans
        (c'.w (Quiver.Hom.op <| Pairwise.Hom.right i j)).symm⟩⟩
  -- and prove that they form an isomorphism.
  let e : c.pt ≅ c'.pt := by
    refine ⟨f₁, f₂, hc.hom_ext ?_, hc'.hom_ext ?_⟩
    · rintro ⟨i | ⟨i, j⟩⟩ <;> simp [f₁, f₂]
    · rintro ⟨i | ⟨i, j⟩⟩
      · simp [f₁, f₂]
      · simpa [f₁, f₂] using c'.w (Quiver.Hom.op <| Pairwise.Hom.left i j)
  convert! e.isIso_hom using 1
  · refine hc'.hom_ext fun i => ?_
    rw [hc'.fac]
    ext1
    · simp [αF, c, Under.liftCone, c', c₀]
    · simp [αF, c, c']

/--
lemma `mono_pushoutSection_of_isCompact_of_flat_right` / 引理 `mono_pushoutSection_of_isCompact_of_flat_right`

English:
lemma mono_pushoutSection_of_isCompact_of_flat_right
  statement: [Flat f]
  proof: by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have := hI.to_subtype
  exact mono_pushoutSection_of_iSup_eq (ι := I) H hUST hUSX hUY (·) (by rwa [iSup_subtype, eq_comm])
    (fun i => have := isIso_pushoutSection_of_isAffineOpen H hUST _ rfl hUS hUT i.1.2; inferInstance)
    (f.flat_appLE hUS hUT _)

中文:
引理 mono_pushoutSection_of_isCompact_of_flat_right
  结论: [平坦 f]
  证明: by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have := hI.to_subtype
  exact mono_pushoutSection_of_iSup_eq (ι := I) H hUST hUSX hUY (·) (by rwa [iSup_subtype, eq_comm])
    (fun i => have := isIso_pushoutSection_of_isAffineOpen H hUST _ rfl hUS hUT i.1.2; inferInstance)
    (f.flat_appLE hUS hUT _)
-/
lemma mono_pushoutSection_of_isCompact_of_flat_right [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsCompact (X := X) UX) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have := hI.to_subtype
  exact mono_pushoutSection_of_iSup_eq (ι := I) H hUST hUSX hUY (·) (by rwa [iSup_subtype, eq_comm])
    (fun i => have := isIso_pushoutSection_of_isAffineOpen H hUST _ rfl hUS hUT i.1.2; inferInstance)
    (f.flat_appLE hUS hUT _)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mono_pushoutSection_of_isCompact_of_flat_left` / 引理 `mono_pushoutSection_of_isCompact_of_flat_left`

English:
lemma mono_pushoutSection_of_isCompact_of_flat_left
  statement: [Flat iX]
  proof: by
  suffices Mono (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← mono_comp_iff_of_isIso (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact mono_pushoutSection_of_isCompact_of_flat_right _ _ _ _ hUS hUX hUT

中文:
引理 mono_pushoutSection_of_isCompact_of_flat_left
  结论: [平坦 iX]
  证明: by
  suffices Mono (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← mono_comp_iff_of_isIso (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact mono_pushoutSection_of_isCompact_of_flat_right _ _ _ _ hUS hUX hUT
-/
lemma mono_pushoutSection_of_isCompact_of_flat_left [Flat iX]
    (hUS : IsAffineOpen US) (hUX : IsAffineOpen UX) (hUT : IsCompact (X := T) UT) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  suffices Mono (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← mono_comp_iff_of_isIso (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact mono_pushoutSection_of_isCompact_of_flat_right _ _ _ _ hUS hUX hUT

/--
lemma `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` / 引理 `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`

English:
lemma isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
  statement: [Flat f]
  proof: by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have hIUX (i : I) : i.1 <= UX := by rw [e]; intro i; aesop
  have := hI.to_subtype
  exact isIso_pushoutSection_of_iSup_eq H hUST hUSX hUY (fun i : I => i) (by rwa [iSup_subtype,
    eq_comm]) (fun i => isIso_pushoutSection_of_isAffineOpen _ _ _ _ hUS hUT i.1.2) (fun i j =>
    mono_pushoutSection_of_isCompact_of_flat_right _ _ _ _ hUS hUT (hUX' _ _ (hIUX _) i.1.1.2
    i.1.2.isCompact (hIUX _) j.1.1.2 j.1.2.isCompact))
    (f.flat_appLE hUS hUT _)

中文:
引理 isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
  结论: [平坦 f]
  证明: by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have hIUX (i : I) : i.1 <= UX := by rw [e]; intro i; aesop
  have := hI.to_subtype
  exact isIso_pushoutSection_of_iSup_eq H hUST hUSX hUY (fun i : I => i) (by rwa [iSup_subtype,
    eq_comm]) (fun i => isIso_pushoutSection_of_isAffineOpen _ _ _ _ hUS hUT i.1.2) (fun i j =>
    mono_pushoutSection_of_isCompact_of_flat_right _ _ _ _ hUS hUT (hUX' _ _ (hIUX _) i.1.1.2
    i.1.2.isCompact (hIUX _) j.1.1.2 j.1.2.isCompact))
    (f.flat_appLE hUS hUT _)

Depends on / 依赖: IsQuasiSeparated
-/
lemma isIso_pushoutSection_of_isQuasiSeparated_of_flat_right [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
    (hUX : IsCompact (X := X) UX) (hUX' : IsQuasiSeparated (α := X) UX) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have hIUX (i : I) : i.1 <= UX := by rw [e]; intro i; aesop
  have := hI.to_subtype
  exact isIso_pushoutSection_of_iSup_eq H hUST hUSX hUY (fun i : I => i) (by rwa [iSup_subtype,
    eq_comm]) (fun i => isIso_pushoutSection_of_isAffineOpen _ _ _ _ hUS hUT i.1.2) (fun i j =>
    mono_pushoutSection_of_isCompact_of_flat_right _ _ _ _ hUS hUT (hUX' _ _ (hIUX _) i.1.1.2
    i.1.2.isCompact (hIUX _) j.1.1.2 j.1.2.isCompact))
    (f.flat_appLE hUS hUT _)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_pushoutSection_of_isQuasiSeparated_of_flat_left` / 引理 `isIso_pushoutSection_of_isQuasiSeparated_of_flat_left`

English:
lemma isIso_pushoutSection_of_isQuasiSeparated_of_flat_left
  statement: [Flat iX]
  proof: by
  suffices IsIso (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← isIso_comp_left_iff (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact isIso_pushoutSection_of_isQuasiSeparated_of_flat_right _ _ _ _ hUS hUX hUT hUT'

中文:
引理 isIso_pushoutSection_of_isQuasiSeparated_of_flat_left
  结论: [平坦 iX]
  证明: by
  suffices IsIso (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← isIso_comp_left_iff (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact isIso_pushoutSection_of_isQuasiSeparated_of_flat_right _ _ _ _ hUS hUX hUT hUT'

Depends on / 依赖: IsQuasiSeparated
-/
lemma isIso_pushoutSection_of_isQuasiSeparated_of_flat_left [Flat iX]
    (hUS : IsAffineOpen US) (hUX : IsAffineOpen UX)
    (hUT : IsCompact (X := T) UT) (hUT' : IsQuasiSeparated (α := T) UT) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  suffices IsIso (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← isIso_comp_left_iff (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact isIso_pushoutSection_of_isQuasiSeparated_of_flat_right _ _ _ _ hUS hUX hUT hUT'

/--
lemma `mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat` / 引理 `mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat`

English:
lemma mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat
  statement: [Flat iX]
  proof: by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have := hI.to_subtype
  exact mono_pushoutSection_of_iSup_eq _ _ _ _ (fun i : I => i) (by rwa [iSup_subtype, eq_comm])
    (fun i => mono_pushoutSection_of_isCompact_of_flat_left _ _ _ _ hUS i.1.2 hUT) hf

中文:
引理 mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat
  结论: [平坦 iX]
  证明: by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have := hI.to_subtype
  exact mono_pushoutSection_of_iSup_eq _ _ _ _ (fun i : I => i) (by rwa [iSup_subtype, eq_comm])
    (fun i => mono_pushoutSection_of_isCompact_of_flat_left _ _ _ _ hUS i.1.2 hUT) hf
-/
lemma mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat [Flat iX]
    (hUS : IsAffineOpen US) (hUT : IsCompact (X := T) UT)
    (hUX : IsCompact (X := X) UX) (hf : (f.appLE US UT hUST).hom.Flat) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUX
  have := hI.to_subtype
  exact mono_pushoutSection_of_iSup_eq _ _ _ _ (fun i : I => i) (by rwa [iSup_subtype, eq_comm])
    (fun i => mono_pushoutSection_of_isCompact_of_flat_left _ _ _ _ hUS i.1.2 hUT) hf

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat` / 引理 `mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`

English:
lemma mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat
  statement: [Flat f]
  proof: by
  suffices Mono (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← mono_comp_iff_of_isIso (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat _ _ _ _ hUS hUX hUT hiX

中文:
引理 mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat
  结论: [平坦 f]
  证明: by
  suffices Mono (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← mono_comp_iff_of_isIso (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat _ _ _ _ hUS hUX hUT hiX
-/
lemma mono_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsCompact (X := T) UT)
    (hUX : IsCompact (X := X) UX) (hiX : (iX.appLE US UX hUSX).hom.Flat) :
    Mono (pushoutSection H hUST hUSX hUY) := by
  suffices Mono (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← mono_comp_iff_of_isIso (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  exact mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat _ _ _ _ hUS hUX hUT hiX

set_option backward.isDefEq.respectTransparency false in
include H in
/--
lemma `isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat` / 引理 `isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat`

English:
lemma isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat
  statement: [Flat f]
  proof: by
  suffices IsIso (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← isIso_comp_left_iff (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUT
  have hIUT (i : I) : i.1 <= UT := by rw [e]; intro i; aesop
  have := hI.to_subtype
  exact isIso_pushoutSection_of_iSup_eq _ _ _ _ (fun i : I => i) (by rwa [iSup_subtype, eq_comm])
    (fun i => isIso_pushoutSection_of_isQuasiSeparated_of_flat_left _ _ _ _ hUS i.1.2 hUX hUX')
    (fun i j => mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat _ _ _ _ hUS hUX
    (hUT' _ _ (hIUT _) i.1.1.2 i.1.2.isCompact (hIUT _) j.1.1.2 j.1.2.isCompact) hiX) hiX

中文:
引理 isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat
  结论: [平坦 f]
  证明: by
  suffices IsIso (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← isIso_comp_left_iff (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUT
  have hIUT (i : I) : i.1 <= UT := by rw [e]; intro i; aesop
  have := hI.to_subtype
  exact isIso_pushoutSection_of_iSup_eq _ _ _ _ (fun i : I => i) (by rwa [iSup_subtype, eq_comm])
    (fun i => isIso_pushoutSection_of_isQuasiSeparated_of_flat_left _ _ _ _ hUS i.1.2 hUX hUX')
    (fun i j => mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat _ _ _ _ hUS hUX
    (hUT' _ _ (hIUT _) i.1.1.2 i.1.2.isCompact (hIUT _) j.1.1.2 j.1.2.isCompact) hiX) hiX

Depends on / 依赖: IsQuasiSeparated
-/
lemma isIso_pushoutSection_of_isCompact_of_flat_right_of_ringHomFlat [Flat f]
    (hUS : IsAffineOpen US) (hUT : IsCompact (X := T) UT) (hUT' : IsQuasiSeparated (α := T) UT)
    (hUX : IsCompact (X := X) UX) (hUX' : IsQuasiSeparated (α := X) UX)
    (hiX : (iX.appLE US UX hUSX).hom.Flat) :
    IsIso (pushoutSection H hUST hUSX hUY) := by
  suffices IsIso (pushoutSection H.flip hUSX hUST (hUY.trans (inf_comm _ _))) by
    rw [← isIso_comp_left_iff (pushoutSymmetry _ _).hom]; convert! this; cat_disch
  obtain ⟨I, hI, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hUT
  have hIUT (i : I) : i.1 <= UT := by rw [e]; intro i; aesop
  have := hI.to_subtype
  exact isIso_pushoutSection_of_iSup_eq _ _ _ _ (fun i : I => i) (by rwa [iSup_subtype, eq_comm])
    (fun i => isIso_pushoutSection_of_isQuasiSeparated_of_flat_left _ _ _ _ hUS i.1.2 hUX hUX')
    (fun i j => mono_pushoutSection_of_isCompact_of_flat_left_of_ringHomFlat _ _ _ _ hUS hUX
    (hUT' _ _ (hIUT _) i.1.1.2 i.1.2.isCompact (hIUT _) j.1.1.2 j.1.2.isCompact) hiX) hiX

end sections

end AlgebraicGeometry
