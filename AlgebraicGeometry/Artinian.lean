/-
Copyright (c) 2025 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Artinian and Locally Artinian Schemes

We define and prove basic properties about Artinian and locally Artinian Schemes.

## Main definitions

* `AlgebraicGeometry.IsLocallyArtinian`: A scheme is locally Artinian if for all open affines,
  the section ring is an Artinian ring.

* `AlgebraicGeometry.IsArtinianScheme`: A scheme is Artinian if it is locally Artinian and
  quasi-compact.

## Main results

* `AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology`: A scheme is
  locally Artinian if and only if it is LocallyNoetherian and it has the discrete topology.

* `AlgebraicGeometry.IsArtinianScheme.iff_isNoetherian_and_discreteTopology`: A scheme is Artinian
  if and only if it is Noetherian and has the discrete topology.

* `AlgebraicGeometry.IsArtinianScheme.finite`: An Artinian scheme is finite.

* `AlgebraicGeometry.Scheme.isArtinianScheme_Spec`: A commutative ring R is Artinian if and only if
  Spec R is Artinian.

-/

public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
Definition of `IsLocallyArtinian` / `IsLocallyArtinian` 的定义

English:
class IsLocallyArtinian
  parameters: (X : Scheme)
  axioms and operations (1):
    - isArtinianRing_presheaf_obj : forall (U : X.affineOpens), IsArtinianRing Γ(X, U)  [default: by infer_instance]

中文:
类 是LocallyArtinian
  参数: (X : 概形)
  公理与运算 (1 个):
    - isArtinianRing_presheaf_obj : 对任意 (U : X.affineOpens), 是Artin环 Γ(X, U)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsLocallyArtinian (X : Scheme) : Prop where
  isArtinianRing_presheaf_obj : forall (U : X.affineOpens),
    IsArtinianRing Γ(X, U) := by infer_instance

attribute [instance] IsLocallyArtinian.isArtinianRing_presheaf_obj

/--
Instance `IsLocallyArtinian.isLocallyNoetherian` / 实例 `IsLocallyArtinian.isLocallyNoetherian`

English:
instance IsLocallyArtinian.isLocallyNoetherian
  signature: [h : IsLocallyArtinian X]

中文:
实例 是LocallyArtinian.isLocallyNoetherian
  签名: [h : 是LocallyArtinian X]
-/
instance IsLocallyArtinian.isLocallyNoetherian [h : IsLocallyArtinian X] :
    IsLocallyNoetherian X where

/--
Instance `IsLocallyArtinian.isArtinianRing_of_isAffine` / 实例 `IsLocallyArtinian.isArtinianRing_of_isAffine`

English:
instance IsLocallyArtinian.isArtinianRing_of_isAffine
  signature: [h : IsLocallyArtinian X] [IsAffine X]
  body: h.1 ⟨⊤, isAffineOpen_top X⟩

中文:
实例 是LocallyArtinian.isArtinianRing_of_isAffine
  签名: [h : 是LocallyArtinian X] [是仿射 X]
  定义体: h.1 ⟨⊤, isAffineOpen_top X⟩

Depends on / 依赖: isAffineOpen_top
-/
instance IsLocallyArtinian.isArtinianRing_of_isAffine [h : IsLocallyArtinian X] [IsAffine X] :
    IsArtinianRing Γ(X, ⊤) :=
  h.1 ⟨⊤, isAffineOpen_top X⟩

/--
lemma `IsLocallyArtinian.of_topologicalKrullDim_le_zero` / 引理 `IsLocallyArtinian.of_topologicalKrullDim_le_zero`

English:
lemma IsLocallyArtinian.of_topologicalKrullDim_le_zero
  proof: by
    have _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    rw [isArtinianRing_iff_krullDimLE_zero]; rw [Ring.KrullDimLE]; rw [Order.krullDimLE_iff]; rw [← ringKrullDim]; rw [Nat.cast_zero]; rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X]; rw [U)]
    change topologicalKrullDim (Spec Γ(X, U)) <= 0
    rw [← IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_subspace_le X U).trans h

中文:
引理 是LocallyArtinian.of_topologicalKrullDim_le_zero
  证明: by
    have _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    rw [isArtinianRing_iff_krullDimLE_zero]; rw [Ring.KrullDimLE]; rw [Order.krullDimLE_iff]; rw [← ringKrullDim]; rw [Nat.cast_zero]; rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X]; rw [U)]
    change topologicalKrullDim (Spec Γ(X, U)) <= 0
    rw [← IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_subspace_le X U).trans h

Depends on / 依赖: IsHomeomorph, IsHomeomorph.topologicalKrullDim_eq, IsLocallyNoetherian, IsLocallyNoetherian.component_noetherian, IsNoetherianRing, IsOpenImmersion, KrullDimLE, MorphismProperty, MorphismProperty.of_isPullback, Nat.cast_zero, Order.krullDimLE_iff, PrimeSpectrum, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, Ring.KrullDimLE, UniversallyOpen, cast_zero, component_noetherian, hf.flip, homeomorph, isArtinianRing_iff_krullDimLE_zero
-/
lemma IsLocallyArtinian.of_topologicalKrullDim_le_zero
    [IsLocallyNoetherian X] (h : topologicalKrullDim X <= 0) : IsLocallyArtinian X where
  isArtinianRing_presheaf_obj U := by
    have _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    rw [isArtinianRing_iff_krullDimLE_zero]; rw [Ring.KrullDimLE]; rw [Order.krullDimLE_iff]; rw [← ringKrullDim]; rw [Nat.cast_zero]; rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X]; rw [U)]
    change topologicalKrullDim (Spec Γ(X, U)) <= 0
    rw [← IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_subspace_le X U).trans h

/--
theorem `IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology` / 定理 `IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology`

English:
theorem IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology
  proof: .of_topologicalKrullDim_le_zero (topologicalKrullDim_zero_of_discreteTopology X)

中文:
定理 是LocallyArtinian.of_isLocallyNoetherian_of_discreteTopology
  证明: .of_topologicalKrullDim_le_zero (topologicalKrullDim_zero_of_discreteTopology X)

Depends on / 依赖: of_topologicalKrullDim_le_zero, topologicalKrullDim_zero_of_discreteTopology
-/
theorem IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology
    [IsLocallyNoetherian X] [DiscreteTopology X] :
    IsLocallyArtinian X :=
  .of_topologicalKrullDim_le_zero (topologicalKrullDim_zero_of_discreteTopology X)

/--
lemma `IsLocallyArtinian.of_isOpenImmersion` / 引理 `IsLocallyArtinian.of_isOpenImmersion`

English:
lemma IsLocallyArtinian.of_isOpenImmersion
  given: [IsOpenImmersion f] [IsLocallyArtinian Y]
  proof: have : IsArtinianRing ↑Γ(Y, f ''ᵁ ↑U) :=
      IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, U.2.image_of_isOpenImmersion f⟩
    (f.appIso U).commRingCatIsoToRingEquiv.surjective.isArtinianRing

中文:
引理 是LocallyArtinian.of_isOpenImmersion
  条件: [是开浸入 f] [是LocallyArtinian Y]
  证明: have : IsArtinianRing ↑Γ(Y, f ''ᵁ ↑U) :=
      IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, U.2.image_of_isOpenImmersion f⟩
    (f.appIso U).commRingCatIsoToRingEquiv.surjective.isArtinianRing
-/
private lemma IsLocallyArtinian.of_isOpenImmersion [IsOpenImmersion f] [IsLocallyArtinian Y] :
    IsLocallyArtinian X where
  isArtinianRing_presheaf_obj U :=
    have : IsArtinianRing ↑Γ(Y, f ''ᵁ ↑U) :=
      IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, U.2.image_of_isOpenImmersion f⟩
    (f.appIso U).commRingCatIsoToRingEquiv.surjective.isArtinianRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLocallyArtinian
  signature: X] {U
  body: .of_isOpenImmersion U.ι

中文:
实例 [是LocallyArtinian
  签名: X] {U
  定义体: .of_isOpenImmersion U.ι

Depends on / 依赖: of_isOpenImmersion
-/
instance [IsLocallyArtinian X] {U : X.Opens} : IsLocallyArtinian U := .of_isOpenImmersion U.ι

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLocallyArtinian
  signature: X] {U
  body: .of_isOpenImmersion (U.f i)

中文:
实例 [是LocallyArtinian
  签名: X] {U
  定义体: .of_isOpenImmersion (U.f i)

Depends on / 依赖: of_isOpenImmersion
-/
instance [IsLocallyArtinian X] {U : X.OpenCover} (i) : IsLocallyArtinian (U.X i) :=
  .of_isOpenImmersion (U.f i)

set_option backward.isDefEq.respectTransparency false in
instance (priority := low) IsLocallyArtinian.discreteTopology [IsLocallyArtinian X] :
    DiscreteTopology X := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  obtain ⟨W, hW1, hW2, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  have : IsArtinianRing Γ(X, W) := IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, hW1⟩
  have : DiscreteTopology (Spec Γ(X, W)) := inferInstanceAs (DiscreteTopology (PrimeSpectrum _))
  have : DiscreteTopology W := hW1.isoSpec.hom.homeomorph.symm.discreteTopology
  simpa using (isOpen_discrete ({⟨x, hW2⟩} : Set W)).trans W.2

@[deprecated (since := "2026-01-14")]
alias IsLocallyArtinian.discreteTopology_of_isAffine := IsLocallyArtinian.discreteTopology

/--
theorem `IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology` / 定理 `IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology`

English:
theorem IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology
  proof: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => .of_isLocallyNoetherian_of_discreteTopology⟩

中文:
定理 是LocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology
  证明: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => .of_isLocallyNoetherian_of_discreteTopology⟩

Depends on / 依赖: comp_mem, of_isLocallyNoetherian_of_discreteTopology
-/
theorem IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology :
    IsLocallyArtinian X ↔ IsLocallyNoetherian X ∧ DiscreteTopology X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => .of_isLocallyNoetherian_of_discreteTopology⟩

-- This can be extended to locally quasi-finite morphisms.
/--
theorem `IsLocallyArtinian.of_isImmersion` / 定理 `IsLocallyArtinian.of_isImmersion`

English:
theorem IsLocallyArtinian.of_isImmersion
  given: [IsImmersion f] [IsLocallyArtinian Y]
  proof: iff_isLocallyNoetherian_and_discreteTopology.mpr
    ⟨LocallyOfFiniteType.isLocallyNoetherian f, f.isEmbedding.discreteTopology⟩

中文:
定理 是LocallyArtinian.of_isImmersion
  条件: [是Immersion f] [是LocallyArtinian Y]
  证明: iff_isLocallyNoetherian_and_discreteTopology.mpr
    ⟨LocallyOfFiniteType.isLocallyNoetherian f, f.isEmbedding.discreteTopology⟩

Depends on / 依赖: LocallyOfFiniteType, LocallyOfFiniteType.isLocallyNoetherian, discreteTopology, f.isEmbedding.discreteTopology, iff_isLocallyNoetherian_and_discreteTopology, iff_isLocallyNoetherian_and_discreteTopology.mpr, isEmbedding, isLocallyNoetherian
-/
theorem IsLocallyArtinian.of_isImmersion [IsImmersion f] [IsLocallyArtinian Y] :
    IsLocallyArtinian X :=
  iff_isLocallyNoetherian_and_discreteTopology.mpr
    ⟨LocallyOfFiniteType.isLocallyNoetherian f, f.isEmbedding.discreteTopology⟩

/--
theorem `Scheme.isLocallyArtinianScheme_Spec` / 定理 `Scheme.isLocallyArtinianScheme_Spec`

English:
theorem Scheme.isLocallyArtinianScheme_Spec
  given: {R : CommRingCat}
  proof: (AlgebraicGeometry.Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.isArtinianRing
  mpr _ := .of_topologicalKrullDim_le_zero
    (topologicalKrullDim_zero_of_discreteTopology (PrimeSpectrum _))

中文:
定理 概形.isLocallyArtinianScheme_Spec
  条件: {R : 交换环范畴}
  证明: (AlgebraicGeometry.Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.isArtinianRing
  mpr _ := .of_topologicalKrullDim_le_zero
    (topologicalKrullDim_zero_of_discreteTopology (PrimeSpectrum _))
-/
@[simp] theorem Scheme.isLocallyArtinianScheme_Spec {R : CommRingCat} :
    IsLocallyArtinian (Spec R) ↔ IsArtinianRing R where
  mp _ := (AlgebraicGeometry.Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.isArtinianRing
  mpr _ := .of_topologicalKrullDim_le_zero
    (topologicalKrullDim_zero_of_discreteTopology (PrimeSpectrum _))

/--
theorem `isLocallyArtinian_iff_openCover` / 定理 `isLocallyArtinian_iff_openCover`

English:
theorem isLocallyArtinian_iff_openCover
  given: (𝒰 : X.OpenCover)
  proof: by
  refine ⟨fun h => inferInstance, fun H => ?_⟩
  refine IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mpr ⟨?_, ?_⟩
  · exact (isLocallyNoetherian_iff_openCover 𝒰).mpr inferInstance
  · refine discreteTopology_iff_isOpen_singleton.mpr fun x => ?_
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    simpa using (𝒰.f i).isOpenEmbedding.isOpenMap _ (isOpen_discrete {x})

中文:
定理 isLocallyArtinian_iff_openCover
  条件: (𝒰 : X.OpenCover)
  证明: by
  refine ⟨fun h => inferInstance, fun H => ?_⟩
  refine IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mpr ⟨?_, ?_⟩
  · exact (isLocallyNoetherian_iff_openCover 𝒰).mpr inferInstance
  · refine discreteTopology_iff_isOpen_singleton.mpr fun x => ?_
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    simpa using (𝒰.f i).isOpenEmbedding.isOpenMap _ (isOpen_discrete {x})

Depends on / 依赖: IsLocallyArtinian, IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mpr, discreteTopology_iff_isOpen_singleton, discreteTopology_iff_isOpen_singleton.mpr, exists_eq, iff_isLocallyNoetherian_and_discreteTopology, isLocallyNoetherian_iff_openCover, isOpenEmbedding, isOpenEmbedding.isOpenMap, isOpenMap, isOpen_discrete
-/
theorem isLocallyArtinian_iff_openCover (𝒰 : X.OpenCover) :
    IsLocallyArtinian X ↔ forall (i : 𝒰.I₀), IsLocallyArtinian (𝒰.X i) := by
  refine ⟨fun h => inferInstance, fun H => ?_⟩
  refine IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mpr ⟨?_, ?_⟩
  · exact (isLocallyNoetherian_iff_openCover 𝒰).mpr inferInstance
  · refine discreteTopology_iff_isOpen_singleton.mpr fun x => ?_
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    simpa using (𝒰.f i).isOpenEmbedding.isOpenMap _ (isOpen_discrete {x})

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isLocallyArtinian_iff_of_isOpenCover` / 定理 `isLocallyArtinian_iff_of_isOpenCover`

English:
theorem isLocallyArtinian_iff_of_isOpenCover
  statement: {ι : Type*} {U : ι -> X.Opens}
  proof: by
  refine ⟨fun _ _ => IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, hU' _⟩, fun H => ?_⟩
  rw [isLocallyArtinian_iff_openCover (X.openCoverOfIsOpenCover U hU)]
  have : forall i, IsLocallyArtinian (Spec Γ(X, U i)) := by simpa
  exact fun i => .of_isImmersion (hU' _).isoSpec.hom

中文:
定理 isLocallyArtinian_iff_of_isOpenCover
  结论: {ι : 类型} {U : ι -> X.Opens}
  证明: by
  refine ⟨fun _ _ => IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, hU' _⟩, fun H => ?_⟩
  rw [isLocallyArtinian_iff_openCover (X.openCoverOfIsOpenCover U hU)]
  have : forall i, IsLocallyArtinian (Spec Γ(X, U i)) := by simpa
  exact fun i => .of_isImmersion (hU' _).isoSpec.hom

Depends on / 依赖: IsLocallyArtinian, IsLocallyArtinian.isArtinianRing_presheaf_obj, X.openCoverOfIsOpenCover, isArtinianRing_presheaf_obj, isLocallyArtinian_iff_openCover, isoSpec, isoSpec.hom, of_isImmersion, openCoverOfIsOpenCover
-/
theorem isLocallyArtinian_iff_of_isOpenCover {ι : Type*} {U : ι -> X.Opens}
    (hU : TopologicalSpace.IsOpenCover U) (hU' : forall i, IsAffineOpen (U i)) :
    IsLocallyArtinian X ↔ forall i, IsArtinianRing Γ(X, U i) := by
  refine ⟨fun _ _ => IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, hU' _⟩, fun H => ?_⟩
  rw [isLocallyArtinian_iff_openCover (X.openCoverOfIsOpenCover U hU)]
  have : forall i, IsLocallyArtinian (Spec Γ(X, U i)) := by simpa
  exact fun i => .of_isImmersion (hU' _).isoSpec.hom

instance (priority := low) {X : Scheme} [IsEmpty X] : IsLocallyArtinian X where

set_option backward.isDefEq.respectTransparency.types false in
instance (priority := low) {X : Scheme} [DiscreteTopology X] [IsReduced X] :
    IsLocallyArtinian X := by
  wlog hX : Subsingleton X generalizing X
  · let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover
      (fun x : X => ⟨{x}, isOpen_discrete _⟩) (.mk (by ext; simp))
    have inst (i : _) : DiscreteTopology (𝒰.X i) := (𝒰.f i).isOpenEmbedding.discreteTopology
    have inst (i : _) : IsReduced (𝒰.X i) := isReduced_of_isOpenImmersion (𝒰.f i)
    exact (isLocallyArtinian_iff_openCover 𝒰).mpr
      fun i => this (inferInstanceAs (Subsingleton ({i} : Set X)))
  cases isEmpty_or_nonempty X
  · infer_instance
  have : IsIntegral X := (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr
    ⟨⟨inferInstance⟩, inferInstance⟩
  let := (isField_of_isIntegral_of_subsingleton X).toField
  have : IsLocallyArtinian (Spec Γ(X, ⊤)) := Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  exact .of_isImmersion X.isoSpec.hom

/-- A scheme is Artinian if it is locally Artinian and quasi-compact -/
@[mk_iff]
/--
Definition of `IsArtinianScheme` / `IsArtinianScheme` 的定义

English:
class IsArtinianScheme
  parameters: (X : Scheme.{u})
  extends: IsLocallyArtinian X, CompactSpace X
  (no additional axioms)

中文:
类 是ArtinianScheme
  参数: (X : 概形.{u})
  继承: 是LocallyArtinian X, 紧空间 X
  (无附加公理)
-/
class IsArtinianScheme (X : Scheme.{u}) : Prop extends IsLocallyArtinian X, CompactSpace X

/-- The underlying type of an Artinian Scheme is finite -/
instance (priority := low) IsArtinianScheme.finite [IsArtinianScheme X] :
    Finite X := finite_of_compact_of_discrete

instance (priority := low) IsArtinianScheme.isNoetherianScheme [IsArtinianScheme X] :
    IsNoetherian X where

/--
theorem `IsArtinianScheme.iff_isNoetherian_and_discreteTopology` / 定理 `IsArtinianScheme.iff_isNoetherian_and_discreteTopology`

English:
theorem IsArtinianScheme.iff_isNoetherian_and_discreteTopology
  proof: by
  aesop (add simp [isArtinianScheme_iff, isNoetherian_iff,
    IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology])

中文:
定理 是ArtinianScheme.iff_isNoetherian_and_discreteTopology
  证明: by
  aesop (add simp [isArtinianScheme_iff, isNoetherian_iff,
    IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology])

Depends on / 依赖: IsLocallyArtinian, IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology, iff_isLocallyNoetherian_and_discreteTopology, isArtinianScheme_iff, isNoetherian_iff
-/
theorem IsArtinianScheme.iff_isNoetherian_and_discreteTopology :
    IsArtinianScheme X ↔ IsNoetherian X ∧ DiscreteTopology X := by
  aesop (add simp [isArtinianScheme_iff, isNoetherian_iff,
    IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology])

instance {R : CommRingCat} [IsArtinianRing R] :
    IsArtinianScheme (Spec R) :=
  IsArtinianScheme.iff_isNoetherian_and_discreteTopology.mpr
    ⟨inferInstance, inferInstanceAs (DiscreteTopology (PrimeSpectrum R))⟩

/-- Spec of a field is artinian. -/
instance (priority := low) {X : Scheme} [Subsingleton X] [IsReduced X] :
    IsArtinianScheme X where

/--
theorem `Scheme.isArtinianScheme_Spec` / 定理 `Scheme.isArtinianScheme_Spec`

English:
theorem Scheme.isArtinianScheme_Spec
  given: {R : CommRingCat}
  proof: by
  simp [isArtinianScheme_iff, (inferInstance : CompactSpace (Spec R))]

中文:
定理 概形.isArtinianScheme_Spec
  条件: {R : 交换环范畴}
  证明: by
  simp [isArtinianScheme_iff, (inferInstance : CompactSpace (Spec R))]

Depends on / 依赖: CompactSpace, isArtinianScheme_iff
-/
theorem Scheme.isArtinianScheme_Spec {R : CommRingCat} :
    IsArtinianScheme (Spec R) ↔ IsArtinianRing R := by
  simp [isArtinianScheme_iff, (inferInstance : CompactSpace (Spec R))]

end AlgebraicGeometry
