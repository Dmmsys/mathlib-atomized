/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Quasi-compact morphisms

A morphism of schemes is quasi-compact if the preimages of quasi-compact open sets are
quasi-compact.

It suffices to check that preimages of affine open sets are compact
(`quasiCompact_iff_forall_isAffineOpen`).

-/

public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism is "quasi-compact" if the underlying map of topological spaces is, i.e. if the preimages
of quasi-compact open sets are quasi-compact.
-/
@[mk_iff]
/--
Definition of `QuasiCompact` / `QuasiCompact` 的定义

English:
class QuasiCompact
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - isCompact_preimage : forall U : Set Y, IsOpen U -> IsCompact U -> IsCompact (f ⁻¹' U)

中文:
类 QuasiCompact
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - isCompact_preimage : 对任意 U : Set Y, IsOpen U -> IsCompact U -> IsCompact (f ⁻¹' U)
-/
class QuasiCompact (f : X ⟶ Y) : Prop where
  /-- The preimage of a compact open set under a quasi-compact morphism between schemes is
  compact. -/
  isCompact_preimage : forall U : Set Y, IsOpen U -> IsCompact U -> IsCompact (f ⁻¹' U)

variable {f} in
/--
theorem `quasiCompact_iff_isSpectralMap` / 定理 `quasiCompact_iff_isSpectralMap`

English:
theorem quasiCompact_iff_isSpectralMap
  statement: QuasiCompact f ↔ IsSpectralMap f
  proof: ⟨fun ⟨h⟩ => ⟨by fun_prop, h⟩, fun h => ⟨h.2⟩⟩

中文:
定理 quasiCompact_iff_isSpectralMap
  结论: QuasiCompact f ↔ IsSpectralMap f
  证明: ⟨fun ⟨h⟩ => ⟨by fun_prop, h⟩, fun h => ⟨h.2⟩⟩

Depends on / 依赖: fun_prop
-/
theorem quasiCompact_iff_isSpectralMap : QuasiCompact f ↔ IsSpectralMap f :=
  ⟨fun ⟨h⟩ => ⟨by fun_prop, h⟩, fun h => ⟨h.2⟩⟩

/--
theorem `Scheme.Hom.isSpectralMap` / 定理 `Scheme.Hom.isSpectralMap`

English:
theorem Scheme.Hom.isSpectralMap
  given: [QuasiCompact f]
  statement: IsSpectralMap f
  proof: by
  rwa [← quasiCompact_iff_isSpectralMap]

中文:
定理 Scheme.Hom.isSpectralMap
  条件: [QuasiCompact f]
  结论: IsSpectralMap f
  证明: by
  rwa [← quasiCompact_iff_isSpectralMap]

Depends on / 依赖: quasiCompact_iff_isSpectralMap
-/
theorem Scheme.Hom.isSpectralMap [QuasiCompact f] : IsSpectralMap f := by
  rwa [← quasiCompact_iff_isSpectralMap]

/--
lemma `Scheme.Hom.isCompact_preimage` / 引理 `Scheme.Hom.isCompact_preimage`

English:
lemma Scheme.Hom.isCompact_preimage
  statement: [QuasiCompact f] {U : Opens Y}
  proof: f.isSpectralMap.2 U.2 hU

中文:
引理 Scheme.Hom.isCompact_preimage
  结论: [QuasiCompact f] {U : Opens Y}
  证明: f.isSpectralMap.2 U.2 hU

Depends on / 依赖: f.isSpectralMap, isSpectralMap
-/
lemma Scheme.Hom.isCompact_preimage [QuasiCompact f] {U : Opens Y}
    (hU : IsCompact (U : Set Y)) : IsCompact (f ⁻¹ᵁ U : Set X) :=
  f.isSpectralMap.2 U.2 hU

instance (priority := 900) quasiCompact_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    QuasiCompact f := by
  constructor
  intro U _ hU'
  convert! hU'.image (inv f.base).hom.continuous_toFun using 1
  rw [Set.image_eq_preimage_of_inverse]
  · delta Function.LeftInverse
    exact IsIso.inv_hom_id_apply f.base
  · exact IsIso.hom_inv_id_apply f.base

/--
Instance `quasiCompact_comp` / 实例 `quasiCompact_comp`

English:
instance quasiCompact_comp
  signature: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f]
  body: by
  constructor
  intro U hU hU'
  rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]
  apply QuasiCompact.isCompact_preimage
  · exact Continuous.isOpen_preimage (by fun_prop) _ hU
  apply QuasiCompact.isCompact_preimage <;> assumption

中文:
实例 quasiCompact_comp
  签名: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f]
  定义体: by
  constructor
  intro U hU hU'
  rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]
  apply QuasiCompact.isCompact_preimage
  · exact Continuous.isOpen_preimage (by fun_prop) _ hU
  apply QuasiCompact.isCompact_preimage <;> assumption

Depends on / 依赖: Continuous, Continuous.isOpen_preimage, QuasiCompact, QuasiCompact.isCompact_preimage, Scheme, Scheme.Hom.comp_base, Set.preimage_comp, TopCat, TopCat.coe_comp, coe_comp, comp_base, fun_prop, isCompact_preimage, isOpen_preimage, preimage_comp
-/
instance quasiCompact_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f]
    [QuasiCompact g] : QuasiCompact (f ≫ g) := by
  constructor
  intro U hU hU'
  rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]
  apply QuasiCompact.isCompact_preimage
  · exact Continuous.isOpen_preimage (by fun_prop) _ hU
  apply QuasiCompact.isCompact_preimage <;> assumption

/--
theorem `isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens` / 定理 `isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens`

English:
theorem isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
  given: {U : Set X}
  proof: by
  apply Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion
    (fun (U : X.affineOpens) => (U : X.Opens))
  · rw [Subtype.range_coe]; exact X.isBasis_affineOpens
  · exact fun i => i.2.isCompact

中文:
定理 isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
  条件: {U : Set X}
  证明: by
  apply Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion
    (fun (U : X.affineOpens) => (U : X.Opens))
  · rw [Subtype.range_coe]; exact X.isBasis_affineOpens
  · exact fun i => i.2.isCompact

Depends on / 依赖: IsBasis, Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion, Subtype, Subtype.range_coe, X.Opens, X.affineOpens, X.isBasis_affineOpens, affineOpens, isBasis_affineOpens, isCompact, isCompact_open_iff_eq_finite_iUnion, range_coe
-/
theorem isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens {U : Set X} :
    IsCompact U ∧ IsOpen U ↔ exists s : Set X.affineOpens, s.Finite ∧ U = ⋃ i in s, i := by
  apply Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion
    (fun (U : X.affineOpens) => (U : X.Opens))
  · rw [Subtype.range_coe]; exact X.isBasis_affineOpens
  · exact fun i => i.2.isCompact

/--
theorem `isCompact_iff_finite_and_eq_biUnion_affineOpens` / 定理 `isCompact_iff_finite_and_eq_biUnion_affineOpens`

English:
theorem isCompact_iff_finite_and_eq_biUnion_affineOpens
  given: {U : X.Opens}
  proof: by
  convert isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (U := U.1) with s
  · simp [U.isOpen]
  · convert! SetLike.coe_injective.eq_iff.symm; simp

中文:
定理 isCompact_iff_finite_and_eq_biUnion_affineOpens
  条件: {U : X.Opens}
  证明: by
  convert isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (U := U.1) with s
  · simp [U.isOpen]
  · convert! SetLike.coe_injective.eq_iff.symm; simp

Depends on / 依赖: Finite, SetLike, SetLike.coe_injective.eq_iff.symm, U.isOpen, X.Opens, X.affineOpens, affineOpens, coe_injective, convert, eq_iff, isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens, isOpen, s.Finite
-/
theorem isCompact_iff_finite_and_eq_biUnion_affineOpens {U : X.Opens} :
    IsCompact (X := X) U ↔ exists s : Set X.affineOpens, s.Finite ∧ U = ⨆ i in s, (i : X.Opens) := by
  convert isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (U := U.1) with s
  · simp [U.isOpen]
  · convert! SetLike.coe_injective.eq_iff.symm; simp

/--
theorem `isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen` / 定理 `isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen`

English:
theorem isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen
  given: [IsAffine X] {U : Set X}
  proof: (isBasis_basicOpen X).isCompact_open_iff_eq_finite_iUnion _
    (fun _ => ((isAffineOpen_top _).basicOpen _).isCompact) _

中文:
定理 isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen
  条件: [IsAffine X] {U : Set X}
  证明: (isBasis_basicOpen X).isCompact_open_iff_eq_finite_iUnion _
    (fun _ => ((isAffineOpen_top _).basicOpen _).isCompact) _

Depends on / 依赖: basicOpen, isAffineOpen_top, isBasis_basicOpen, isCompact, isCompact_open_iff_eq_finite_iUnion
-/
theorem isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen [IsAffine X] {U : Set X} :
    IsCompact U ∧ IsOpen U ↔ exists s : Set Γ(X, ⊤), s.Finite ∧ U = ⋃ i in s, X.basicOpen i :=
  (isBasis_basicOpen X).isCompact_open_iff_eq_finite_iUnion _
    (fun _ => ((isAffineOpen_top _).basicOpen _).isCompact) _

variable {f} in
/--
theorem `quasiCompact_iff_forall_isAffineOpen` / 定理 `quasiCompact_iff_forall_isAffineOpen`

English:
theorem quasiCompact_iff_forall_isAffineOpen
  proof: by
  rw [quasiCompact_iff]
  refine ⟨fun H U hU => H U U.isOpen hU.isCompact, ?_⟩
  intro H U hU hU'
  obtain ⟨S, hS, rfl⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU', hU⟩
  simp only [Set.preimage_iUnion]
  exact Set.Finite.isCompact_biUnion hS (fun i _ => H i i.prop)

中文:
定理 quasiCompact_iff_forall_isAffineOpen
  证明: by
  rw [quasiCompact_iff]
  refine ⟨fun H U hU => H U U.isOpen hU.isCompact, ?_⟩
  intro H U hU hU'
  obtain ⟨S, hS, rfl⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU', hU⟩
  simp only [Set.preimage_iUnion]
  exact Set.Finite.isCompact_biUnion hS (fun i _ => H i i.prop)

Depends on / 依赖: Finite, Set.Finite.isCompact_biUnion, Set.preimage_iUnion, U.isOpen, hU.isCompact, i.prop, isCompact, isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens, isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp, isCompact_biUnion, isOpen, preimage_iUnion, quasiCompact_iff
-/
theorem quasiCompact_iff_forall_isAffineOpen :
    QuasiCompact f ↔ forall U : Y.Opens, IsAffineOpen U -> IsCompact (f ⁻¹ᵁ U : Set X) := by
  rw [quasiCompact_iff]
  refine ⟨fun H U hU => H U U.isOpen hU.isCompact, ?_⟩
  intro H U hU hU'
  obtain ⟨S, hS, rfl⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU', hU⟩
  simp only [Set.preimage_iUnion]
  exact Set.Finite.isCompact_biUnion hS (fun i _ => H i i.prop)

/--
theorem `isCompact_basicOpen` / 定理 `isCompact_basicOpen`

English:
theorem isCompact_basicOpen
  statement: (X : Scheme) {U : X.Opens} (hU : IsCompact (U : Set X))
  proof: by
  refine isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ?_
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  let g : s -> X.affineOpens := fun V => ⟨V.1 ⊓ X.basicOpen f, by
    rw [← X.basicOpen_res _ (homOfLE ((le_iSup₂ V.1 V.2).trans_eq e.symm)).op]
    exact V

中文:
定理 isCompact_basicOpen
  结论: (X : Scheme) {U : X.Opens} (hU : IsCompact (U : Set X))
  证明: by
  refine isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ?_
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  let g : s -> X.affineOpens := fun V => ⟨V.1 ⊓ X.basicOpen f, by
    rw [← X.basicOpen_res _ (homOfLE ((le_iSup₂ V.1 V.2).trans_eq e.symm)).op]
    exact V

Depends on / 依赖: Finite, Set.finite_range, Set.range, X.affineOpens, X.basicOpen, X.basicOpen_le, X.basicOpen_res, affineOpens, basicOpen, basicOpen_le, basicOpen_res, e.symm, finite_range, homOfLE, hs.to_subtype, iSup_inf_eq, iSup_range, iSup_subtype, inf_eq_right, inf_eq_right.mpr
-/
theorem isCompact_basicOpen (X : Scheme) {U : X.Opens} (hU : IsCompact (U : Set X))
    (f : Γ(X, U)) : IsCompact (X.basicOpen f : Set X) := by
  refine isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ?_
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  let g : s -> X.affineOpens := fun V => ⟨V.1 ⊓ X.basicOpen f, by
    rw [← X.basicOpen_res _ (homOfLE ((le_iSup₂ V.1 V.2).trans_eq e.symm)).op]
    exact V.1.2.basicOpen _⟩
  have : Finite s := hs.to_subtype
  refine ⟨Set.range g, Set.finite_range g, ?_⟩
  rw [iSup_range]; rw [← iSup_inf_eq]; rw [iSup_subtype]; rw [← e]; rw [inf_eq_right.mpr (X.basicOpen_le f)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasAffineProperty @QuasiCompact (fun X _ _ _ => CompactSpace X)
  body: by
    ext X Y f
    simp only [quasiCompact_iff_forall_isAffineOpen, isCompact_iff_compactSpace,
      targetAffineLocally, Subtype.forall]
    rfl
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk <;> rintro X Y Z e _ _ H
      exacts [@Homeomor

中文:
实例 :
  签名: HasAffine命题erty @QuasiCompact (fun X _ _ _ => CompactSpace X)
  定义体: by
    ext X Y f
    simp only [quasiCompact_iff_forall_isAffineOpen, isCompact_iff_compactSpace,
      targetAffineLocally, Subtype.forall]
    rfl
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk <;> rintro X Y Z e _ _ H
      exacts [@Homeomor

Depends on / 依赖: AffineTargetMorphismProperty, AffineTargetMorphismProperty.respectsIso_mk, Homeomorph, Homeomorph.compactSpace, Scheme, Scheme.preimage_basicOpen, Subtype, Subtype.forall, TopCat, TopCat.homeoOfIso, compactSpace, e.inv.base, exacts, homeoOfIso, introv, isCompact_basicOpen, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, isCompact_univ, isLocal_affineProperty
-/
instance : HasAffineProperty @QuasiCompact (fun X _ _ _ => CompactSpace X) where
  eq_targetAffineLocally' := by
    ext X Y f
    simp only [quasiCompact_iff_forall_isAffineOpen, isCompact_iff_compactSpace,
      targetAffineLocally, Subtype.forall]
    rfl
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk <;> rintro X Y Z e _ _ H
      exacts [@Homeomorph.compactSpace _ _ _ _ H (TopCat.homeoOfIso (asIso e.inv.base)), H]
    · introv _ H
      rw [Scheme.preimage_basicOpen f r]
      exact (isCompact_iff_compactSpace.mp (isCompact_basicOpen _ isCompact_univ _))
    · rintro X Y H f S hS hS'
      rw [← (isAffineOpen_top _).iSup_basicOpen_eq_self_iff] at hS
      rw [← isCompact_univ_iff]; rw [← Opens.coe_top]; rw [← f.preimage_top]; rw [← hS]; rw [Scheme.Hom.preimage_iSup]; rw [Opens.iSup_mk]; rw [Opens.coe_mk]
      exact isCompact_iUnion fun i => isCompact_iff_compactSpace.mpr (hS' i)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `compactSpace_iff_quasiCompact` / 定理 `compactSpace_iff_quasiCompact`

English:
theorem compactSpace_iff_quasiCompact
  given: (X : Scheme)
  proof: by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]

中文:
定理 compactSpace_iff_quasiCompact
  条件: (X : Scheme)
  证明: by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, QuasiCompact, iff_of_isAffine
-/
theorem compactSpace_iff_quasiCompact (X : Scheme) :
    CompactSpace X ↔ QuasiCompact (terminal.from X) := by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]

set_option backward.isDefEq.respectTransparency.types false in
instance {X : Scheme} [CompactSpace X] : QuasiCompact X.toSpecΓ :=
  HasAffineProperty.iff_of_isAffine.mpr ‹_›

/--
lemma `QuasiCompact.compactSpace_of_compactSpace` / 引理 `QuasiCompact.compactSpace_of_compactSpace`

English:
lemma QuasiCompact.compactSpace_of_compactSpace
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  proof: by
  constructor
  rw [← Set.preimage_univ (f := f)]
  exact QuasiCompact.isCompact_preimage _ isOpen_univ CompactSpace.isCompact_univ

中文:
引理 QuasiCompact.compactSpace_of_compactSpace
  结论: {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
  证明: by
  constructor
  rw [← Set.preimage_univ (f := f)]
  exact QuasiCompact.isCompact_preimage _ isOpen_univ CompactSpace.isCompact_univ

Depends on / 依赖: CompactSpace, CompactSpace.isCompact_univ, Functor, Functor.isoWhiskerRight, IsIso.of_isIso_fac_right, QuasiCompact, QuasiCompact.isCompact_preimage, Set.preimage_univ, associator, hoFunctor, isCompact_preimage, isCompact_univ, isOpen_univ, iso.hom, isoWhiskerRight, leftUnitor, nerveFunctor, nerveFunctor.associator, nerveFunctor.leftUnitor, nerveFunctorCompHoFunctorIso
-/
lemma QuasiCompact.compactSpace_of_compactSpace {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [CompactSpace Y] : CompactSpace X := by
  constructor
  rw [← Set.preimage_univ (f := f)]
  exact QuasiCompact.isCompact_preimage _ isOpen_univ CompactSpace.isCompact_univ

/--
Instance `quasiCompact_isStableUnderComposition` / 实例 `quasiCompact_isStableUnderComposition`

English:
instance quasiCompact_isStableUnderComposition
  signature: :
  body: inferInstance

中文:
实例 quasiCompact_isStableUnderComposition
  签名: :
  定义体: inferInstance
-/
instance quasiCompact_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @QuasiCompact where
  comp_mem _ _ _ _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @QuasiCompact
  body: inferInstance

中文:
实例 :
  签名: Morphism命题erty.IsMultiplicative @QuasiCompact
  定义体: inferInstance

Depends on / 依赖: Cat.of, IsIso.of_isIso_fac_left, IsIso.of_isIso_fac_right, hoFunctor, isIso_of_fully_faithful, nerveFunctor, nerveFunctor.map, of_isIso_fac_left, of_isIso_fac_right, prodComparison, prodComparison_comp
-/
instance : MorphismProperty.IsMultiplicative @QuasiCompact where
  id_mem _ := inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `quasiCompact_isStableUnderBaseChange` / 实例 `quasiCompact_isStableUnderBaseChange`

English:
instance quasiCompact_isStableUnderBaseChange
  signature: :
  body: by
  let := HasAffineProperty.isLocal_affineProperty @QuasiCompact
  apply HasAffineProperty.isStableUnderBaseChange
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g h
  let 𝒰 := Scheme.Pullback.openCoverOfRight Y.affineCover.finiteSubcover f g
  have : Finite 𝒰.

中文:
实例 quasiCompact_isStableUnderBaseChange
  签名: :
  定义体: by
  let := HasAffineProperty.isLocal_affineProperty @QuasiCompact
  apply HasAffineProperty.isStableUnderBaseChange
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g h
  let 𝒰 := Scheme.Pullback.openCoverOfRight Y.affineCover.finiteSubcover f g
  have : Finite 𝒰.

Depends on / 依赖: AffineTargetMorphismProperty, AffineTargetMorphismProperty.IsStableUnderBaseChange.mk, CompactSpace, Finite, HasAffineProperty, HasAffineProperty.isLocal_affineProperty, HasAffineProperty.isStableUnderBaseChange, IsStableUnderBaseChange, Pullback, QuasiCompact, Scheme, Scheme.Pullback.openCoverOfRight, Y.affineCover.finiteSubcover, affineCover, compactSpace, finiteSubcover, infer_instance, isLocal_affineProperty, isStableUnderBaseChange, openCoverOfRight
-/
instance quasiCompact_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @QuasiCompact := by
  let := HasAffineProperty.isLocal_affineProperty @QuasiCompact
  apply HasAffineProperty.isStableUnderBaseChange
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g h
  let 𝒰 := Scheme.Pullback.openCoverOfRight Y.affineCover.finiteSubcover f g
  have : Finite 𝒰.I₀ := by dsimp [𝒰]; infer_instance
  have : forall i, CompactSpace (𝒰.X i) := by intro i; dsimp [𝒰]; infer_instance
  exact 𝒰.compactSpace

variable {Z : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact g] : QuasiCompact (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact f] : QuasiCompact (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (V : Y.Opens) [QuasiCompact f] : QuasiCompact (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact f] [CompactSpace Y] : CompactSpace ↑(pullback f g) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)

instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact g] [CompactSpace X] : CompactSpace ↑(pullback f g) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst _ _)

/--
lemma `compactSpace_iff_exists` / 引理 `compactSpace_iff_exists`

English:
lemma compactSpace_iff_exists
  proof: let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
    ⟨Γ(∐ 𝒰.X, ⊤), (∐ 𝒰.X).isoSpec.inv ≫ Sigma.desc 𝒰.f, Surjective.surj⟩
  mpr := fun ⟨_, f, hf⟩ => ⟨hf.range_eq ▸ isCompact_range f.continuous⟩

中文:
引理 compactSpace_iff_exists
  证明: let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
    ⟨Γ(∐ 𝒰.X, ⊤), (∐ 𝒰.X).isoSpec.inv ≫ Sigma.desc 𝒰.f, Surjective.surj⟩
  mpr := fun ⟨_, f, hf⟩ => ⟨hf.range_eq ▸ isCompact_range f.continuous⟩

Depends on / 依赖: OpenCover, X.OpenCover, X.affineCover.finiteSubcover, affineCover, finiteSubcover
-/
lemma compactSpace_iff_exists :
    CompactSpace X ↔ exists R, exists f : Spec R ⟶ X, Function.Surjective f where
  mp _ := let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
    ⟨Γ(∐ 𝒰.X, ⊤), (∐ 𝒰.X).isoSpec.inv ≫ Sigma.desc 𝒰.f, Surjective.surj⟩
  mpr := fun ⟨_, f, hf⟩ => ⟨hf.range_eq ▸ isCompact_range f.continuous⟩


/--
lemma `isCompact_iff_exists` / 引理 `isCompact_iff_exists`

English:
lemma isCompact_iff_exists
  given: {U : X.Opens}
  proof: by
  refine isCompact_iff_compactSpace.trans ((compactSpace_iff_exists (X := U)).trans ?_)
  refine ⟨fun ⟨R, f, hf⟩ => ⟨R, f ≫ U.ι, by simp [hf.range_comp]⟩, fun ⟨R, f, hf⟩ => ?_⟩
  refine ⟨R, IsOpenImmersion.lift U.ι f (by simp [hf]), ?_⟩
  rw [← Set.range_eq_univ]
  apply show Function.Injective (

中文:
引理 isCompact_iff_exists
  条件: {U : X.Opens}
  证明: by
  refine isCompact_iff_compactSpace.trans ((compactSpace_iff_exists (X := U)).trans ?_)
  refine ⟨fun ⟨R, f, hf⟩ => ⟨R, f ≫ U.ι, by simp [hf.range_comp]⟩, fun ⟨R, f, hf⟩ => ?_⟩
  refine ⟨R, IsOpenImmersion.lift U.ι f (by simp [hf]), ?_⟩
  rw [← Set.range_eq_univ]
  apply show Function.Injective (

Depends on / 依赖: Function, Function.Injective, Injective, IsOpenImmersion, IsOpenImmersion.lift, IsOpenImmersion.lift_fac, Scheme, Scheme.Hom.comp_base, Scheme.Opens.range_, Set.image_univ, Set.image_val_injective, Set.range_comp, Set.range_eq_univ, TopCat, TopCat.coe_comp, coe_comp, comp_base, compactSpace_iff_exists, hf.range_comp, image_univ
-/
lemma isCompact_iff_exists {U : X.Opens} :
    IsCompact (U : Set X) ↔ exists R, exists f : Spec R ⟶ X, Set.range f = U := by
  refine isCompact_iff_compactSpace.trans ((compactSpace_iff_exists (X := U)).trans ?_)
  refine ⟨fun ⟨R, f, hf⟩ => ⟨R, f ≫ U.ι, by simp [hf.range_comp]⟩, fun ⟨R, f, hf⟩ => ?_⟩
  refine ⟨R, IsOpenImmersion.lift U.ι f (by simp [hf]), ?_⟩
  rw [← Set.range_eq_univ]
  apply show Function.Injective (U.ι '' ·) from Set.image_val_injective
  simp only [Set.image_univ, Scheme.Opens.range_ι]
  rwa [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, IsOpenImmersion.lift_fac]

set_option backward.isDefEq.respectTransparency.types false in
@[stacks 01K9]
nonrec lemma isClosedMap_iff_specializingMap (f : X ⟶ Y) [QuasiCompact f] :
    IsClosedMap f ↔ SpecializingMap f := by
  refine ⟨fun h => h.specializingMap, fun H => ?_⟩
  wlog hY : exists R, Y = Spec R
  · change topologically @IsClosedMap f
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := topologically @IsClosedMap) Y.affineCover]
    intro i
    have _ : QuasiCompact (Y.affineCover.pullbackHom f i) := MorphismProperty.pullback_snd _ _ ‹_›
    refine this (Y.affineCover.pullbackHom f i) ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtTarget.of_isPullback
      (P := topologically @SpecializingMap) (.of_hasPullback _ _) H
  obtain ⟨S, rfl⟩ := hY
  intro Z hZ
  replace H := hZ.stableUnderSpecialization.image H
  wlog hX : exists R, X = Spec R
  · obtain ⟨R, g, hg⟩ := compactSpace_iff_exists.mp (QuasiCompact.compactSpace_of_compactSpace f)
    have inst : QuasiCompact (g ≫ f) := HasAffineProperty.iff_of_isAffine.mpr (by infer_instance)
    have := this _ (g ≫ f) (g ⁻¹' Z) (hZ.preimage g.continuous)
    simp_rw [Scheme.Hom.comp_base, TopCat.comp_app, ← Set.image_image,
      Set.image_preimage_eq _ hg] at this
    exact this H ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.homEquiv.symm.surjective f
  exact PrimeSpectrum.isClosed_image_of_stableUnderSpecialization φ.hom Z hZ H

@[elab_as_elim]
/--
theorem `compact_open_induction_on` / 定理 `compact_open_induction_on`

English:
theorem compact_open_induction_on
  statement: {P : X.Opens -> Prop} (S : X.Opens)
  proof: by
  obtain ⟨s, hs, rfl⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hS
  refine hs.induction_on _ (by simpa using h₁) fun {x s} _ hs h₄ => ?_
  rw [iSup_insert]; rw [sup_comm]
  exact h₂ _ (isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ⟨s, hs, by simp⟩) x h₄

中文:
定理 compact_open_induction_on
  结论: {P : X.Opens -> 命题} (S : X.Opens)
  证明: by
  obtain ⟨s, hs, rfl⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hS
  refine hs.induction_on _ (by simpa using h₁) fun {x s} _ hs h₄ => ?_
  rw [iSup_insert]; rw [sup_comm]
  exact h₂ _ (isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ⟨s, hs, by simp⟩) x h₄

Depends on / 依赖: hs.induction_on, iSup_insert, induction_on, isCompact_iff_finite_and_eq_biUnion_affineOpens, isCompact_iff_finite_and_eq_biUnion_affineOpens.mp, isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr, sup_comm
-/
theorem compact_open_induction_on {P : X.Opens -> Prop} (S : X.Opens)
    (hS : IsCompact (S : Set X)) (h₁ : P ⊥)
    (h₂ : forall (S : X.Opens) (_ : IsCompact S.1) (U : X.affineOpens), P S -> P (S ⊔ U)) :
    P S := by
  obtain ⟨s, hs, rfl⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hS
  refine hs.induction_on _ (by simpa using h₁) fun {x s} _ hs h₄ => ?_
  rw [iSup_insert]; rw [sup_comm]
  exact h₂ _ (isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ⟨s, hs, by simp⟩) x h₄

/--
theorem `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen` / 定理 `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen`

English:
theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen
  statement: (X : Scheme)
  proof: by
  rw [← map_zero (X.presheaf.map (homOfLE <| X.basicOpen_le f : X.basicOpen f ⟶ U).op).hom] at H
  obtain ⟨n, e⟩ := (hU.isLocalization_basicOpen f).exists_of_eq _ H
  exact ⟨n, by simpa [mul_comm x] using e⟩

中文:
定理 exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen
  结论: (X : Scheme)
  证明: by
  rw [← map_zero (X.presheaf.map (homOfLE <| X.basicOpen_le f : X.basicOpen f ⟶ U).op).hom] at H
  obtain ⟨n, e⟩ := (hU.isLocalization_basicOpen f).exists_of_eq _ H
  exact ⟨n, by simpa [mul_comm x] using e⟩

Depends on / 依赖: X.basicOpen, X.basicOpen_le, X.presheaf.map, basicOpen, basicOpen_le, exists_of_eq, hU.isLocalization_basicOpen, homOfLE, isLocalization_basicOpen, map_zero, mul_comm, presheaf
-/
theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen (X : Scheme)
    {U : X.Opens} (hU : IsAffineOpen U) (x f : Γ(X, U))
    (H : x |_ (X.basicOpen f) = 0) :
    exists n : Nat, f ^ n * x = 0 := by
  rw [← map_zero (X.presheaf.map (homOfLE <| X.basicOpen_le f : X.basicOpen f ⟶ U).op).hom] at H
  obtain ⟨n, e⟩ := (hU.isLocalization_basicOpen f).exists_of_eq _ H
  exact ⟨n, by simpa [mul_comm x] using e⟩

/--
theorem `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact` / 定理 `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact`

English:
theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
  statement: (X : Scheme.{u})
  proof: by
  obtain ⟨s, hs, e⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by
    ext1; simpa using e
  have h₁ (i : s) : i.1.1 <= U := by
    rw [e]
    exact le_iSup (fun (i : s) => (i : Opens (X.toPresheafedSpace))) _
  h

中文:
定理 exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
  结论: (X : Scheme.{u})
  证明: by
  obtain ⟨s, hs, e⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by
    ext1; simpa using e
  have h₁ (i : s) : i.1.1 <= U := by
    rw [e]
    exact le_iSup (fun (i : s) => (i : Opens (X.toPresheafedSpace))) _
  h

Depends on / 依赖: X.Opens, X.presheaf.map, X.toPresheafedSpace, exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen, homOfLE, isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens, isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp, le_iSup, presheaf, replace, toPresheafedSpace
-/
theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (X : Scheme.{u})
    {U : X.Opens} (hU : IsCompact U.1) (x f : Γ(X, U))
    (H : x |_ (X.basicOpen f) = 0) :
    exists n : Nat, f ^ n * x = 0 := by
  obtain ⟨s, hs, e⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by
    ext1; simpa using e
  have h₁ (i : s) : i.1.1 <= U := by
    rw [e]
    exact le_iSup (fun (i : s) => (i : Opens (X.toPresheafedSpace))) _
  have H' := fun i : s =>
    exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X i.1.2
      (X.presheaf.map (homOfLE (h₁ i)).op x) (X.presheaf.map (homOfLE (h₁ i)).op f) ?_
  swap
  · change (X.presheaf.map (homOfLE _).op) ((X.presheaf.map (homOfLE _).op).hom x) = 0
    have H : (X.presheaf.map (homOfLE _).op) x = 0 := H
    convert! congr_arg (X.presheaf.map (homOfLE _).op).hom H
    · simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
      · rfl
    · rw [map_zero]
    · simp only [Scheme.basicOpen_res, inf_le_right]
  choose n hn using H'
  have := hs.to_subtype
  cases nonempty_fintype s
  use Finset.univ.sup n
  suffices forall i : s, X.presheaf.map (homOfLE (h₁ i)).op (f ^ Finset.univ.sup n * x) = 0 by
    subst e
    apply TopCat.Sheaf.eq_of_locally_eq X.sheaf fun i : s => (i : X.Opens)
    intro i
    change _ = (X.sheaf.obj.map _) 0
    rw [map_zero]
    apply this
  intro i
  replace hn :=
    congr_arg (fun x => X.presheaf.map (homOfLE (h₁ i)).op (f ^ (Finset.univ.sup n - n i)) * x)
      (hn i)
  dsimp at hn
  simp only [← map_mul, ← map_pow] at hn
  rwa [mul_zero, ← mul_assoc, ← pow_add, tsub_add_cancel_of_le] at hn
  apply Finset.le_sup (Finset.mem_univ i)

/--
lemma `Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact` / 引理 `Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact`

English:
lemma Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact
  statement: {X : Scheme.{u}}
  proof: by
  refine ⟨X.basicOpen_eq_bot_of_isNilpotent U f, fun hf => ?_⟩
  have h : (1 : Γ(X, U)) |_ (X.basicOpen f) = 0 := by
    have e : X.basicOpen f <= ⊥ := by rw [hf]
    rw [← TopCat.Presheaf.restrict_restrict e bot_le]
    rw [Subsingleton.eq_zero (1 |_ ⊥)]
    change X.presheaf.map _ 0 = 0
    rw 

中文:
引理 Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact
  结论: {X : Scheme.{u}}
  证明: by
  refine ⟨X.basicOpen_eq_bot_of_isNilpotent U f, fun hf => ?_⟩
  have h : (1 : Γ(X, U)) |_ (X.basicOpen f) = 0 := by
    have e : X.basicOpen f <= ⊥ := by rw [hf]
    rw [← TopCat.Presheaf.restrict_restrict e bot_le]
    rw [Subsingleton.eq_zero (1 |_ ⊥)]
    change X.presheaf.map _ 0 = 0
    rw 

Depends on / 依赖: Presheaf, Subsingleton, Subsingleton.eq_zero, TopCat, TopCat.Presheaf.restrict_restrict, X.basicOpen, X.basicOpen_eq_bot_of_isNilpotent, X.presheaf.map, basicOpen, basicOpen_eq_bot_of_isNilpotent, bot_le, eq_zero, exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact, map_zero, mul_one, presheaf, restrict_restrict
-/
lemma Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact {X : Scheme.{u}}
    {U : X.Opens} (hU : IsCompact (U : Set X)) (f : Γ(X, U)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ := by
  refine ⟨X.basicOpen_eq_bot_of_isNilpotent U f, fun hf => ?_⟩
  have h : (1 : Γ(X, U)) |_ (X.basicOpen f) = 0 := by
    have e : X.basicOpen f <= ⊥ := by rw [hf]
    rw [← TopCat.Presheaf.restrict_restrict e bot_le]
    rw [Subsingleton.eq_zero (1 |_ ⊥)]
    change X.presheaf.map _ 0 = 0
    rw [map_zero]
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU 1 f h
  rw [mul_one] at hn
  use n

/--
lemma `Scheme.isNilpotent_iff_basicOpen_eq_bot` / 引理 `Scheme.isNilpotent_iff_basicOpen_eq_bot`

English:
lemma Scheme.isNilpotent_iff_basicOpen_eq_bot
  statement: {X : Scheme.{u}}
  proof: isNilpotent_iff_basicOpen_eq_bot_of_isCompact (U := ⊤) (CompactSpace.isCompact_univ) f

中文:
引理 Scheme.isNilpotent_iff_basicOpen_eq_bot
  结论: {X : Scheme.{u}}
  证明: isNilpotent_iff_basicOpen_eq_bot_of_isCompact (U := ⊤) (CompactSpace.isCompact_univ) f

Depends on / 依赖: CompactSpace, CompactSpace.isCompact_univ, isCompact_univ, isNilpotent_iff_basicOpen_eq_bot_of_isCompact
-/
lemma Scheme.isNilpotent_iff_basicOpen_eq_bot {X : Scheme.{u}}
    [CompactSpace X] (f : Γ(X, ⊤)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ :=
  isNilpotent_iff_basicOpen_eq_bot_of_isCompact (U := ⊤) (CompactSpace.isCompact_univ) f

/--
lemma `Scheme.zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact` / 引理 `Scheme.zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact`

English:
lemma Scheme.zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact
  statement: {X : Scheme.{u}} {U : X.Opens}
  proof: by
  simp [Scheme.zeroLocus_def, ← Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU,
    ← mem_nilradical, Set.subset_def]

中文:
引理 Scheme.zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact
  结论: {X : Scheme.{u}} {U : X.Opens}
  证明: by
  simp [Scheme.zeroLocus_def, ← Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU,
    ← mem_nilradical, Set.subset_def]

Depends on / 依赖: Scheme, Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact, Scheme.zeroLocus_def, Set.subset_def, isNilpotent_iff_basicOpen_eq_bot_of_isCompact, mem_nilradical, subset_def, zeroLocus_def
-/
lemma Scheme.zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact {X : Scheme.{u}} {U : X.Opens}
    (hU : IsCompact (U : Set X)) (s : Set Γ(X, U)) :
    X.zeroLocus s = Set.univ ↔ s subseteq nilradical Γ(X, U) := by
  simp [Scheme.zeroLocus_def, ← Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU,
    ← mem_nilradical, Set.subset_def]

/--
lemma `Scheme.zeroLocus_eq_univ_iff_subset_nilradical` / 引理 `Scheme.zeroLocus_eq_univ_iff_subset_nilradical`

English:
lemma Scheme.zeroLocus_eq_univ_iff_subset_nilradical
  statement: {X : Scheme.{u}}
  proof: zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact (U := ⊤) (CompactSpace.isCompact_univ) s

中文:
引理 Scheme.zeroLocus_eq_univ_iff_subset_nilradical
  结论: {X : Scheme.{u}}
  证明: zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact (U := ⊤) (CompactSpace.isCompact_univ) s

Depends on / 依赖: CompactSpace, CompactSpace.isCompact_univ, isCompact_univ, zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact
-/
lemma Scheme.zeroLocus_eq_univ_iff_subset_nilradical {X : Scheme.{u}}
    [CompactSpace X] (s : Set Γ(X, ⊤)) :
    X.zeroLocus s = Set.univ ↔ s subseteq nilradical Γ(X, ⊤) :=
  zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact (U := ⊤) (CompactSpace.isCompact_univ) s

end AlgebraicGeometry
