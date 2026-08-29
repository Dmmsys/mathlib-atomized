/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-!
# Open covers of schemes

This file provides the basic API for open covers of schemes.

## Main definition
- `AlgebraicGeometry.Scheme.OpenCover`: The type of open covers of a scheme `X`,
  consisting of a family of open immersions into `X`,
  and for each `x : X` an open immersion (indexed by `f x`) that covers `x`.
- `AlgebraicGeometry.Scheme.affineCover`: `X.affineCover` is a choice of an affine cover of `X`.
- `AlgebraicGeometry.Scheme.AffineOpenCover`: The type of affine open covers of a scheme `X`.
-/

@[expose] public section


noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

universe v v₁ v₂ u

namespace AlgebraicGeometry

namespace Scheme

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasPullbacks IsOpenImmersion
  body: inferInstance

中文:
实例 :
  签名: MorphismProperty.有Pullbacks 是开浸入
  定义体: inferInstance
-/
instance : MorphismProperty.HasPullbacks IsOpenImmersion where
  hasPullback _ _ := inferInstance

/--
Definition of `OpenCover` / `OpenCover` 的定义

English:
abbreviation OpenCover
  signature: (X : Scheme.{u})
  body: Cover.{v} (precoverage @IsOpenImmersion) X

中文:
缩写 OpenCover
  签名: (X : 概形.{u})
  定义体: Cover.{v} (precoverage @IsOpenImmersion) X

Depends on / 依赖: IsOpenImmersion, precoverage
-/
abbrev OpenCover (X : Scheme.{u}) : Type _ := Cover.{v} (precoverage @IsOpenImmersion) X

variable {X Y Z : Scheme.{u}} (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [forall x, HasPullback (𝒰.f x ≫ f) g]

instance (i : 𝒰.I₀) : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i

instance {𝒱 : OpenCover X} (f : 𝒰 ⟶ 𝒱) (i : 𝒰.I₀) : IsOpenImmersion (f.h₀ i) :=
  have : IsOpenImmersion (f.h₀ i ≫ 𝒱.f (f.s₀ i)) := by rw [f.w₀]; infer_instance
  .of_comp _ (𝒱.f _)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `affineCover` / `affineCover` 的定义

English:
definition affineCover
  signature: (X : Scheme.{u})
  body: by
  choose U R h using X.local_affine
  let e (x) := (h x).some
  exact
  { I₀ := X
    X x := Spec (R x)
    f x := ⟨(e x).inv ≫ X.toLocallyRingedSpace.ofRestrict _⟩
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ⟨x, ⟨(e x).hom.base ⟨x, (U x).2⟩, ?_⟩⟩, inferInstance

中文:
定义 affineCover
  签名: (X : 概形.{u})
  定义体: by
  choose U R h using X.local_affine
  let e (x) := (h x).some
  exact
  { I₀ := X
    X x := Spec (R x)
    f x := ⟨(e x).inv ≫ X.toLocallyRingedSpace.ofRestrict _⟩
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ⟨x, ⟨(e x).hom.base ⟨x, (U x).2⟩, ?_⟩⟩, inferInstance

Depends on / 依赖: X.local_affine, X.ofRestrict, X.toLocallyRingedSpace.ofRestrict, cat_disch, hom.base, local_affine, ofRestrict, toLocallyRingedSpace
-/
def affineCover (X : Scheme.{u}) : OpenCover X := by
  choose U R h using X.local_affine
  let e (x) := (h x).some
  exact
  { I₀ := X
    X x := Spec (R x)
    f x := ⟨(e x).inv ≫ X.toLocallyRingedSpace.ofRestrict _⟩
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ⟨x, ⟨(e x).hom.base ⟨x, (U x).2⟩, ?_⟩⟩, inferInstance⟩
      change ((((e x).hom ≫ (e x).inv).base ≫ (X.ofRestrict _).base)) ⟨x, _⟩ = x
      cat_disch }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited X.OpenCover
  body: ⟨X.affineCover⟩

中文:
实例 :
  签名: 可居 X.OpenCover
  定义体: ⟨X.affineCover⟩

Depends on / 依赖: X.affineCover, affineCover
-/
instance : Inhabited X.OpenCover :=
  ⟨X.affineCover⟩

/--
theorem `OpenCover.iSup_opensRange` / 定理 `OpenCover.iSup_opensRange`

English:
theorem OpenCover.iSup_opensRange
  given: {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X)
  proof: Opens.ext by rw [Opens.coe_iSup]; exact 𝒰.iUnion_range

中文:
定理 OpenCover.iSup_opensRange
  条件: {X : 概形.{u}} (𝒰 : 概形.OpenCover.{v} X)
  证明: Opens.ext by rw [Opens.coe_iSup]; exact 𝒰.iUnion_range

Depends on / 依赖: Opens.coe_iSup, Opens.ext, coe_iSup, iUnion_range
-/
theorem OpenCover.iSup_opensRange {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X) :
    ⨆ i, (𝒰.f i).opensRange = ⊤ :=
Opens.ext by rw [Opens.coe_iSup]; exact 𝒰.iUnion_range

/--
lemma `OpenCover.isOpenCover_opensRange` / 引理 `OpenCover.isOpenCover_opensRange`

English:
lemma OpenCover.isOpenCover_opensRange
  given: {X : Scheme.{u}} (𝒰 : OpenCover.{v} X)
  proof: .mk 𝒰.iSup_opensRange

中文:
引理 OpenCover.isOpenCover_opensRange
  条件: {X : 概形.{u}} (𝒰 : OpenCover.{v} X)
  证明: .mk 𝒰.iSup_opensRange

Depends on / 依赖: iSup_opensRange
-/
lemma OpenCover.isOpenCover_opensRange {X : Scheme.{u}} (𝒰 : OpenCover.{v} X) :
    IsOpenCover fun i => (𝒰.f i).opensRange :=
  .mk 𝒰.iSup_opensRange

/-- Every open cover of a quasi-compact scheme can be refined into a finite subcover.
-/
@[simps! X f]
/--
Definition of `OpenCover.finiteSubcover` / `OpenCover.finiteSubcover` 的定义

English:
definition OpenCover.finiteSubcover
  signature: {X : Scheme.{u}} (𝒰 : OpenCover.{v} X) [H : CompactSpace X]
  body: by
  have :=
    @CompactSpace.elim_nhds_subcover _ _ H (fun x : X => Set.range (𝒰.f (𝒰.idx x)))
      fun x => (IsOpenImmersion.isOpen_range (𝒰.f (𝒰.idx x))).mem_nhds (𝒰.covers x)
  let t := this.choose
  have h : forall x : X, exists y : t, x in Set.range (𝒰.f (𝒰.idx y)) := by
    intro x
    have

中文:
定义 OpenCover.finiteSubcover
  签名: {X : 概形.{u}} (𝒰 : OpenCover.{v} X) [H : 紧空间 X]
  定义体: by
  have :=
    @CompactSpace.elim_nhds_subcover _ _ H (fun x : X => Set.range (𝒰.f (𝒰.idx x)))
      fun x => (IsOpenImmersion.isOpen_range (𝒰.f (𝒰.idx x))).mem_nhds (𝒰.covers x)
  let t := this.choose
  have h : forall x : X, exists y : t, x in Set.range (𝒰.f (𝒰.idx y)) := by
    intro x
    have

Depends on / 依赖: Classical, Classical.choose_spec, CompactSpace, CompactSpace.elim_nhds_subcover, IsOpenImmersion, IsOpenImmersion.isOpen_range, Set.mem_iUnion, Set.range, choose_spec, covers, elim_nhds_subcover, isOpen_range, mem_iUnion, mem_nhds, this.choose
-/
def OpenCover.finiteSubcover {X : Scheme.{u}} (𝒰 : OpenCover.{v} X) [H : CompactSpace X] :
    OpenCover X := by
  have :=
    @CompactSpace.elim_nhds_subcover _ _ H (fun x : X => Set.range (𝒰.f (𝒰.idx x)))
      fun x => (IsOpenImmersion.isOpen_range (𝒰.f (𝒰.idx x))).mem_nhds (𝒰.covers x)
  let t := this.choose
  have h : forall x : X, exists y : t, x in Set.range (𝒰.f (𝒰.idx y)) := by
    intro x
    have h' : x in (⊤ : Set X) := trivial
    rw [← Classical.choose_spec this]; rw [Set.mem_iUnion] at h'
    rcases h' with ⟨y, _, ⟨hy, rfl⟩, hy'⟩
    exact ⟨⟨y, hy⟩, hy'⟩
  exact
    { I₀ := t
      X := fun x => 𝒰.X (𝒰.idx x.1)
      f := fun x => 𝒰.f (𝒰.idx x.1)
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        exact ⟨h, inferInstance⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [H
  signature: : CompactSpace X] : Fintype 𝒰.finiteSubcover.I₀
  body: by
  delta OpenCover.finiteSubcover; infer_instance

中文:
实例 [H
  签名: : 紧空间 X] : 有限类型 𝒰.finiteSubcover.I₀
  定义体: by
  delta OpenCover.finiteSubcover; infer_instance

Depends on / 依赖: OpenCover, OpenCover.finiteSubcover, finiteSubcover, infer_instance
-/
instance [H : CompactSpace X] : Fintype 𝒰.finiteSubcover.I₀ := by
  delta OpenCover.finiteSubcover; infer_instance

/--
theorem `OpenCover.compactSpace` / 定理 `OpenCover.compactSpace`

English:
theorem OpenCover.compactSpace
  statement: {X : Scheme.{u}} (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
  proof: by
  cases nonempty_fintype 𝒰.I₀
  rw [← isCompact_univ_iff]; rw [← 𝒰.iUnion_range]
  apply isCompact_iUnion
  intro i
  rw [isCompact_iff_compactSpace]
  exact
    @Homeomorph.compactSpace _ _ _ _ (H i)
      (TopCat.homeoOfIso
        (asIso
          (IsOpenImmersion.isoOfRangeEq (𝒰.f i)
        

中文:
定理 OpenCover.compactSpace
  结论: {X : 概形.{u}} (𝒰 : X.OpenCover) [有限 𝒰.I₀]
  证明: by
  cases nonempty_fintype 𝒰.I₀
  rw [← isCompact_univ_iff]; rw [← 𝒰.iUnion_range]
  apply isCompact_iUnion
  intro i
  rw [isCompact_iff_compactSpace]
  exact
    @Homeomorph.compactSpace _ _ _ _ (H i)
      (TopCat.homeoOfIso
        (asIso
          (IsOpenImmersion.isoOfRangeEq (𝒰.f i)
        

Depends on / 依赖: Homeomorph, Homeomorph.compactSpace, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, Opens.isOpenEmbedding, Subtype, Subtype.range_coe.symm, TopCat, TopCat.homeoOfIso, X.ofRestrict, base_open, base_open.isOpen_range, compactSpace, hom.base, homeoOfIso, iUnion_range, isCompact_iUnion, isCompact_iff_compactSpace, isCompact_univ_iff, isOpenEmbedding
-/
theorem OpenCover.compactSpace {X : Scheme.{u}} (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [H : forall i, CompactSpace (𝒰.X i)] : CompactSpace X := by
  cases nonempty_fintype 𝒰.I₀
  rw [← isCompact_univ_iff]; rw [← 𝒰.iUnion_range]
  apply isCompact_iUnion
  intro i
  rw [isCompact_iff_compactSpace]
  exact
    @Homeomorph.compactSpace _ _ _ _ (H i)
      (TopCat.homeoOfIso
        (asIso
          (IsOpenImmersion.isoOfRangeEq (𝒰.f i)
            (X.ofRestrict (Opens.isOpenEmbedding ⟨_, (𝒰.map_prop i).base_open.isOpen_range⟩))
            Subtype.range_coe.symm).hom.base))
/--
Definition of `AffineOpenCover` / `AffineOpenCover` 的定义

English:
abbreviation AffineOpenCover
  signature: (X : Scheme.{u})
  body: AffineCover.{v} @IsOpenImmersion X

中文:
缩写 AffineOpenCover
  签名: (X : 概形.{u})
  定义体: AffineCover.{v} @IsOpenImmersion X

Depends on / 依赖: AffineCover, IsOpenImmersion
-/
abbrev AffineOpenCover (X : Scheme.{u}) : Type _ :=
  AffineCover.{v} @IsOpenImmersion X

namespace AffineOpenCover

instance {X : Scheme.{u}} (𝒰 : X.AffineOpenCover) (j : 𝒰.I₀) : IsOpenImmersion (𝒰.f j) :=
  𝒰.map_prop j

/-- The open cover associated to an affine open cover. -/
@[simps! I₀ X f]
/--
Definition of `openCover` / `openCover` 的定义

English:
definition openCover
  signature: {X : Scheme.{u}} (𝒰 : X.AffineOpenCover)
  body: AffineCover.cover 𝒰

中文:
定义 openCover
  签名: {X : 概形.{u}} (𝒰 : X.AffineOpenCover)
  定义体: AffineCover.cover 𝒰

Depends on / 依赖: AffineCover, AffineCover.cover
-/
def openCover {X : Scheme.{u}} (𝒰 : X.AffineOpenCover) : X.OpenCover :=
  AffineCover.cover 𝒰

end AffineOpenCover

set_option backward.isDefEq.respectTransparency false in
/-- A choice of an affine open cover of a scheme. -/
@[simps]
/--
Definition of `affineOpenCover` / `affineOpenCover` 的定义

English:
definition affineOpenCover
  signature: (X : Scheme.{u})
  body: _
  I₀ := X.affineCover.I₀
  f := X.affineCover.f
  idx x := (X.affineCover.exists_eq x).choose
  covers x := (X.affineCover.exists_eq x).choose_spec

@[simp]

中文:
定义 affineOpenCover
  签名: (X : 概形.{u})
  定义体: _
  I₀ := X.affineCover.I₀
  f := X.affineCover.f
  idx x := (X.affineCover.exists_eq x).choose
  covers x := (X.affineCover.exists_eq x).choose_spec

@[simp]
-/
def affineOpenCover (X : Scheme.{u}) : X.AffineOpenCover where
  X := _
  I₀ := X.affineCover.I₀
  f := X.affineCover.f
  idx x := (X.affineCover.exists_eq x).choose
  covers x := (X.affineCover.exists_eq x).choose_spec

@[simp]
/--
lemma `openCover_affineOpenCover` / 引理 `openCover_affineOpenCover`

English:
lemma openCover_affineOpenCover
  given: (X : Scheme.{u})
  statement: X.affineOpenCover.openCover = X.affineCover
  proof: rfl

中文:
引理 openCover_affineOpenCover
  条件: (X : 概形.{u})
  结论: X.affineOpenCover.openCover = X.affineCover
  证明: rfl
-/
lemma openCover_affineOpenCover (X : Scheme.{u}) : X.affineOpenCover.openCover = X.affineCover :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `OpenCover.affineRefinement` / `OpenCover.affineRefinement` 的定义

English:
definition OpenCover.affineRefinement
  signature: {X : Scheme.{u}} (𝓤 : X.OpenCover)
  body: _
  I₀ := (𝓤.bind fun j => (𝓤.X j).affineCover).I₀
  f := (𝓤.bind fun j => (𝓤.X j).affineCover).f
  idx := Cover.idx (𝓤.bind fun j => (𝓤.X j).affineCover)
  covers := Cover.covers (𝓤.bind fun j => (𝓤.X j).affineCover)

中文:
定义 OpenCover.affineRefinement
  签名: {X : 概形.{u}} (𝓤 : X.OpenCover)
  定义体: _
  I₀ := (𝓤.bind fun j => (𝓤.X j).affineCover).I₀
  f := (𝓤.bind fun j => (𝓤.X j).affineCover).f
  idx := Cover.idx (𝓤.bind fun j => (𝓤.X j).affineCover)
  covers := Cover.covers (𝓤.bind fun j => (𝓤.X j).affineCover)
-/
def OpenCover.affineRefinement {X : Scheme.{u}} (𝓤 : X.OpenCover) : X.AffineOpenCover where
  X := _
  I₀ := (𝓤.bind fun j => (𝓤.X j).affineCover).I₀
  f := (𝓤.bind fun j => (𝓤.X j).affineCover).f
  idx := Cover.idx (𝓤.bind fun j => (𝓤.X j).affineCover)
  covers := Cover.covers (𝓤.bind fun j => (𝓤.X j).affineCover)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `OpenCover.pullbackCoverAffineRefinementObjIso` / `OpenCover.pullbackCoverAffineRefinementObjIso` 的定义

English:
definition OpenCover.pullbackCoverAffineRefinementObjIso
  signature: (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i)
  body: pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso _ _ _).symm ≪≫
    pullbackSymmetry _ _ ≪≫ asIso (pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _)
      (by simp [Cover.pullbackHom]) (by simp))

中文:
定义 OpenCover.pullbackCoverAffineRefinementObjIso
  签名: (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i)
  定义体: pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso _ _ _).symm ≪≫
    pullbackSymmetry _ _ ≪≫ asIso (pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _)
      (by simp [Cover.pullbackHom]) (by simp))

Depends on / 依赖: Cover.pullbackHom, pullback, pullback.map, pullbackHom, pullbackRightPullbackFstIso, pullbackSymmetry
-/
def OpenCover.pullbackCoverAffineRefinementObjIso (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.affineRefinement.openCover.pullback₁ f).X i ≅
      ((𝒰.X i.1).affineCover.pullback₁ (𝒰.pullbackHom f i.1)).X i.2 :=
  pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso _ _ _).symm ≪≫
    pullbackSymmetry _ _ ≪≫ asIso (pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _)
      (by simp [Cover.pullbackHom]) (by simp))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `OpenCover.pullbackCoverAffineRefinementObjIso_inv_map` / 引理 `OpenCover.pullbackCoverAffineRefinementObjIso_inv_map`

English:
lemma OpenCover.pullbackCoverAffineRefinementObjIso_inv_map
  given: (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i)
  proof: by
  simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, AffineOpenCover.openCover_X, AffineOpenCover.openCover_f,
    pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv, Iso.symm_inv, Category.assoc,
    PreZeroHypercover.pullback₁_f, p

中文:
引理 OpenCover.pullbackCoverAffineRefinementObjIso_inv_map
  条件: (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i)
  证明: by
  simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, AffineOpenCover.openCover_X, AffineOpenCover.openCover_f,
    pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv, Iso.symm_inv, Category.assoc,
    PreZeroHypercover.pullback₁_f, p

Depends on / 依赖: AffineOpenCover, AffineOpenCover.openCover_X, AffineOpenCover.openCover_f, Category, Category.assoc, IsIso.inv_comp_eq, Iso.symm_inv, Iso.trans_inv, PreZeroHypercover, PreZeroHypercover.pullback, Precoverage, Precoverage.ZeroHypercover.pullback, PullbackCone, PullbackCone.mk_, PullbackCone.mk_pt, ZeroHypercover, asIso_inv, convert, cospan_left, inv_comp_eq
-/
lemma OpenCover.pullbackCoverAffineRefinementObjIso_inv_map (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.pullbackCoverAffineRefinementObjIso f i).inv ≫
      (𝒰.affineRefinement.openCover.pullback₁ f).f i =
      ((𝒰.X i.1).affineCover.pullback₁ (𝒰.pullbackHom f i.1)).f i.2 ≫
        (𝒰.pullback₁ f).f i.1 := by
  simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, AffineOpenCover.openCover_X, AffineOpenCover.openCover_f,
    pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv, Iso.symm_inv, Category.assoc,
    PreZeroHypercover.pullback₁_f, pullbackSymmetry_inv_comp_fst, IsIso.inv_comp_eq,
    limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app,
    pullbackSymmetry_hom_comp_fst]
  convert!
    pullbackSymmetry_inv_comp_snd_assoc ((𝒰.X i.1).affineCover.f i.2) (pullback.fst _ _) _ using 2
  exact pullbackRightPullbackFstIso_hom_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `OpenCover.pullbackCoverAffineRefinementObjIso_inv_pullbackHom` / 引理 `OpenCover.pullbackCoverAffineRefinementObjIso_inv_pullbackHom`

English:
lemma OpenCover.pullbackCoverAffineRefinementObjIso_inv_pullbackHom
  proof: by
  simp only [Cover.pullbackHom, pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv,
    Iso.symm_inv, Category.assoc, pullbackSymmetry_inv_comp_snd, IsIso.inv_comp_eq, limit.lift_π,
    PullbackCone.mk_π_app, Category.comp_id]
  convert! pullbackSymmetry_inv_comp_fst ((𝒰.X i.1).affineC

中文:
引理 OpenCover.pullbackCoverAffineRefinementObjIso_inv_pullbackHom
  证明: by
  simp only [Cover.pullbackHom, pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv,
    Iso.symm_inv, Category.assoc, pullbackSymmetry_inv_comp_snd, IsIso.inv_comp_eq, limit.lift_π,
    PullbackCone.mk_π_app, Category.comp_id]
  convert! pullbackSymmetry_inv_comp_fst ((𝒰.X i.1).affineC

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Cover.pullbackHom, IsIso.inv_comp_eq, Iso.symm_inv, Iso.trans_inv, PullbackCone, PullbackCone.mk_, affineCover, affineCover.f, asIso_inv, comp_id, convert, inv_comp_eq, limit.lift_, pullback, pullback.fst, pullbackCoverAffineRefinementObjIso, pullbackHom
-/
lemma OpenCover.pullbackCoverAffineRefinementObjIso_inv_pullbackHom
    (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.pullbackCoverAffineRefinementObjIso f i).inv ≫
      𝒰.affineRefinement.openCover.pullbackHom f i =
      (𝒰.X i.1).affineCover.pullbackHom (𝒰.pullbackHom f i.1) i.2 := by
  simp only [Cover.pullbackHom, pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv,
    Iso.symm_inv, Category.assoc, pullbackSymmetry_inv_comp_snd, IsIso.inv_comp_eq, limit.lift_π,
    PullbackCone.mk_π_app, Category.comp_id]
  convert! pullbackSymmetry_inv_comp_fst ((𝒰.X i.1).affineCover.f i.2) (pullback.fst _ _)
  exact pullbackRightPullbackFstIso_hom_fst _ _ _

/-- A family of elements spanning the unit ideal of `R` gives an affine open cover of `Spec R`. -/
@[simps]
noncomputable
/--
Definition of `affineOpenCoverOfSpanRangeEqTop` / `affineOpenCoverOfSpanRangeEqTop` 的定义

English:
definition affineOpenCoverOfSpanRangeEqTop
  signature: {R : CommRingCat} {ι : Type*} (s : ι -> R)
  body: ι
  X i := .of (Localization.Away (s i))
  f i := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (s i))))
  idx x := by
    have : exists i, s i ∉ x.asIdeal := by
      by_contra! h; apply x.2.ne_top; rwa [← top_le_iff, ← hs, Ideal.span_le, Set.range_subset_iff]
    exact this.choose
 

中文:
定义 affineOpenCoverOfSpanRangeEqTop
  签名: {R : 交换环范畴} {ι : 类型} (s : ι -> R)
  定义体: ι
  X i := .of (Localization.Away (s i))
  f i := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (s i))))
  idx x := by
    have : exists i, s i ∉ x.asIdeal := by
      by_contra! h; apply x.2.ne_top; rwa [← top_le_iff, ← hs, Ideal.span_le, Set.range_subset_iff]
    exact this.choose
 
-/
def affineOpenCoverOfSpanRangeEqTop {R : CommRingCat} {ι : Type*} (s : ι -> R)
    (hs : Ideal.span (Set.range s) = ⊤) : (Spec R).AffineOpenCover where
  I₀ := ι
  X i := .of (Localization.Away (s i))
  f i := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (s i))))
  idx x := by
    have : exists i, s i ∉ x.asIdeal := by
      by_contra! h; apply x.2.ne_top; rwa [← top_le_iff, ← hs, Ideal.span_le, Set.range_subset_iff]
    exact this.choose
  covers x := by
    generalize_proofs H
    let i := H.choose
    have := PrimeSpectrum.localization_away_comap_range (Localization.Away (s i)) (s i)
    exact (eq_iff_iff.mp congr(x in $this)).mpr H.choose_spec

/--
Definition of `OpenCover.fromAffineRefinement` / `OpenCover.fromAffineRefinement` 的定义

English:
definition OpenCover.fromAffineRefinement
  signature: {X : Scheme.{u}} (𝓤 : X.OpenCover)
  body: j.fst
  h₀ j := (𝓤.X j.fst).affineCover.f _

中文:
定义 OpenCover.fromAffineRefinement
  签名: {X : 概形.{u}} (𝓤 : X.OpenCover)
  定义体: j.fst
  h₀ j := (𝓤.X j.fst).affineCover.f _

Depends on / 依赖: j.fst
-/
def OpenCover.fromAffineRefinement {X : Scheme.{u}} (𝓤 : X.OpenCover) :
    𝓤.affineRefinement.openCover ⟶ 𝓤 where
  s₀ j := j.fst
  h₀ j := (𝓤.X j.fst).affineCover.f _

/--
lemma `OpenCover.ext_elem` / 引理 `OpenCover.ext_elem`

English:
lemma OpenCover.ext_elem
  statement: {X : Scheme.{u}} {U : X.Opens} (f g : Γ(X, U)) (𝒰 : X.OpenCover)
  proof: by
  fapply TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun i => (𝒰.f (𝒰.idx i)).opensRange ⊓ U) _ (fun _ => homOfLE inf_le_right)
  · intro x hx
    simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_inf, Hom.coe_opensRange, Opens.mem_mk,
      Set.mem_iUnion, Set.mem_inter_iff, Set.mem_rang

中文:
引理 OpenCover.ext_elem
  结论: {X : 概形.{u}} {U : X.Opens} (f g : Γ(X, U)) (𝒰 : X.OpenCover)
  证明: by
  fapply TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun i => (𝒰.f (𝒰.idx i)).opensRange ⊓ U) _ (fun _ => homOfLE inf_le_right)
  · intro x hx
    simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_inf, Hom.coe_opensRange, Opens.mem_mk,
      Set.mem_iUnion, Set.mem_inter_iff, Set.mem_rang

Depends on / 依赖: Hom.coe_opensRange, IsOpenImmersion, IsOpenImmersion.map_, Opens.carrier_eq_coe, Opens.coe_inf, Opens.iSup_mk, Opens.mem_mk, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, SetLike, SetLike.mem_coe, TopCat, TopCat.Sheaf.eq_of_locally_eq, X.sheaf, carrier_eq_coe, coe_inf, coe_opensRange, commRingCatIs, covers
-/
lemma OpenCover.ext_elem {X : Scheme.{u}} {U : X.Opens} (f g : Γ(X, U)) (𝒰 : X.OpenCover)
    (h : forall i : 𝒰.I₀, (𝒰.f i).app U f = (𝒰.f i).app U g) : f = g := by
  fapply TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun i => (𝒰.f (𝒰.idx i)).opensRange ⊓ U) _ (fun _ => homOfLE inf_le_right)
  · intro x hx
    simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_inf, Hom.coe_opensRange, Opens.mem_mk,
      Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, SetLike.mem_coe, exists_and_right]
    refine ⟨?_, hx⟩
    simpa using ⟨_, 𝒰.covers x⟩
  · intro x
    replace h := h (𝒰.idx x)
    rw [← IsOpenImmersion.map_ΓIso_inv] at h
    exact (IsOpenImmersion.ΓIso (𝒰.f (𝒰.idx x)) U).commRingCatIsoToRingEquiv.symm.injective h

/--
lemma `zero_of_zero_cover` / 引理 `zero_of_zero_cover`

English:
lemma zero_of_zero_cover
  statement: {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U)) (𝒰 : X.OpenCover)
  proof: 𝒰.ext_elem s 0 (fun i => by rw [map_zero]; exact h i)

中文:
引理 zero_of_zero_cover
  结论: {X : 概形.{u}} {U : X.Opens} (s : Γ(X, U)) (𝒰 : X.OpenCover)
  证明: 𝒰.ext_elem s 0 (fun i => by rw [map_zero]; exact h i)

Depends on / 依赖: ext_elem, map_zero
-/
lemma zero_of_zero_cover {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U)) (𝒰 : X.OpenCover)
    (h : forall i : 𝒰.I₀, (𝒰.f i).app U s = 0) : s = 0 :=
  𝒰.ext_elem s 0 (fun i => by rw [map_zero]; exact h i)

/--
lemma `isNilpotent_of_isNilpotent_cover` / 引理 `isNilpotent_of_isNilpotent_cover`

English:
lemma isNilpotent_of_isNilpotent_cover
  statement: {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U))
  proof: by
  choose fn hfn using h
  have : Fintype 𝒰.I₀ := Fintype.ofFinite 𝒰.I₀
  /- the maximum of all `fn i` (exists, because `𝒰.I₀` is finite) -/
  let N : Nat := Finset.sup Finset.univ fn
  have hfnleN (i : 𝒰.I₀) : fn i <= N := Finset.le_sup (Finset.mem_univ i)
  use N
  apply zero_of_zero_cover (𝒰 :=

中文:
引理 isNilpotent_of_isNilpotent_cover
  结论: {X : 概形.{u}} {U : X.Opens} (s : Γ(X, U))
  证明: by
  choose fn hfn using h
  have : Fintype 𝒰.I₀ := Fintype.ofFinite 𝒰.I₀
  /- the maximum of all `fn i` (exists, because `𝒰.I₀` is finite) -/
  let N : Nat := Finset.sup Finset.univ fn
  have hfnleN (i : 𝒰.I₀) : fn i <= N := Finset.le_sup (Finset.mem_univ i)
  use N
  apply zero_of_zero_cover (𝒰 :=

Depends on / 依赖: Fintype, Fintype.ofFinite, ofFinite
-/
lemma isNilpotent_of_isNilpotent_cover {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U))
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (h : forall i : 𝒰.I₀, IsNilpotent ((𝒰.f i).app U s)) :
    IsNilpotent s := by
  choose fn hfn using h
  have : Fintype 𝒰.I₀ := Fintype.ofFinite 𝒰.I₀
  /- the maximum of all `fn i` (exists, because `𝒰.I₀` is finite) -/
  let N : Nat := Finset.sup Finset.univ fn
  have hfnleN (i : 𝒰.I₀) : fn i <= N := Finset.le_sup (Finset.mem_univ i)
  use N
  apply zero_of_zero_cover (𝒰 := 𝒰)
  on_goal 1 => intro i; simp only [map_pow]
  -- This closes both remaining goals at once.
  exact pow_eq_zero_of_le (hfnleN i) (hfn i)

section deprecated

/--
Definition of `affineBasisCoverOfAffine` / `affineBasisCoverOfAffine` 的定义

English:
definition affineBasisCoverOfAffine
  signature: (R : CommRingCat.{u})
  body: R
X r := Spec .of Localization.Away r
  f r := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ⟨1, ?_⟩, AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway⟩
    rw [Set.range_eq_univ.mpr ((TopCat

中文:
定义 affineBasisCoverOfAffine
  签名: (R : 交换环范畴.{u})
  定义体: R
X r := Spec .of Localization.Away r
  f r := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ⟨1, ?_⟩, AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway⟩
    rw [Set.range_eq_univ.mpr ((TopCat
-/
def affineBasisCoverOfAffine (R : CommRingCat.{u}) : OpenCover (Spec R) where
  I₀ := R
X r := Spec .of Localization.Away r
  f r := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ⟨1, ?_⟩, AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway⟩
    rw [Set.range_eq_univ.mpr ((TopCat.epi_iff_surjective _).mp _)]
    · exact trivial
    · infer_instance

/--
Definition of `affineBasisCover` / `affineBasisCover` 的定义

English:
definition affineBasisCover
  signature: (X : Scheme.{u})
  body: X.affineCover.bind fun _ => affineBasisCoverOfAffine _

中文:
定义 affineBasisCover
  签名: (X : 概形.{u})
  定义体: X.affineCover.bind fun _ => affineBasisCoverOfAffine _

Depends on / 依赖: X.affineCover.bind, affineBasisCoverOfAffine, affineCover
-/
def affineBasisCover (X : Scheme.{u}) : OpenCover X :=
  X.affineCover.bind fun _ => affineBasisCoverOfAffine _

/--
Definition of `affineBasisCoverRing` / `affineBasisCoverRing` 的定义

English:
definition affineBasisCoverRing
  signature: (X : Scheme.{u}) (i : X.affineBasisCover.I₀)
  body: CommRingCat.of @Localization.Away (X.local_affine i.1).choose_spec.choose _ i.2

中文:
定义 affineBasisCoverRing
  签名: (X : 概形.{u}) (i : X.affineBasisCover.I₀)
  定义体: CommRingCat.of @Localization.Away (X.local_affine i.1).choose_spec.choose _ i.2

Depends on / 依赖: CommRingCat, CommRingCat.of, Localization, Localization.Away, X.local_affine, choose_spec, choose_spec.choose, local_affine
-/
def affineBasisCoverRing (X : Scheme.{u}) (i : X.affineBasisCover.I₀) : CommRingCat :=
CommRingCat.of @Localization.Away (X.local_affine i.1).choose_spec.choose _ i.2

/--
theorem `affineBasisCover_obj` / 定理 `affineBasisCover_obj`

English:
theorem affineBasisCover_obj
  given: (X : Scheme.{u}) (i : X.affineBasisCover.I₀)
  proof: rfl

中文:
定理 affineBasisCover_obj
  条件: (X : 概形.{u}) (i : X.affineBasisCover.I₀)
  证明: rfl
-/
theorem affineBasisCover_obj (X : Scheme.{u}) (i : X.affineBasisCover.I₀) :
    X.affineBasisCover.X i = Spec (X.affineBasisCoverRing i) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `affineBasisCover_map_range` / 定理 `affineBasisCover_map_range`

English:
theorem affineBasisCover_map_range
  statement: (X : Scheme.{u}) (x : X)
  proof: by
  simp only [affineBasisCover, Precoverage.ZeroHypercover.bind_toPreZeroHypercover, Set.range_comp,
    PreZeroHypercover.bind_f, Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp]
  congr
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r :)

中文:
定理 affineBasisCover_map_range
  结论: (X : 概形.{u}) (x : X)
  证明: by
  simp only [affineBasisCover, Precoverage.ZeroHypercover.bind_toPreZeroHypercover, Set.range_comp,
    PreZeroHypercover.bind_f, Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp]
  congr
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r :)

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_comp, Hom.comp_base, Localization, Localization.Away, PreZeroHypercover, PreZeroHypercover.bind_f, Precoverage, Precoverage.ZeroHypercover.bind_toPreZeroHypercover, PrimeSpectrum, PrimeSpectrum.localization_away_comap_range, Set.range_comp, TopCat, TopCat.hom_comp, ZeroHypercover, affineBasisCover, bind_f, bind_toPreZeroHypercover, coe_comp, comp_base
-/
theorem affineBasisCover_map_range (X : Scheme.{u}) (x : X)
    (r : (X.local_affine x).choose_spec.choose) :
    Set.range (X.affineBasisCover.f ⟨x, r⟩) =
      (X.affineCover.f x) '' (PrimeSpectrum.basicOpen r).1 := by
  simp only [affineBasisCover, Precoverage.ZeroHypercover.bind_toPreZeroHypercover, Set.range_comp,
    PreZeroHypercover.bind_f, Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp]
  congr
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r :)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `affineBasisCover_is_basis` / 定理 `affineBasisCover_is_basis`

English:
theorem affineBasisCover_is_basis
  given: (X : Scheme.{u})
  proof: by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact IsOpenImmersion.isOpen_range (X.affineBasisCover.f a)
  · rintro a U haU hU
    rcases X.affineCover.covers a with ⟨x, e⟩
    let U' := (X.affineCover.f (X.affineCover.idx a)) ⁻¹' U
    have hxU' : x in 

中文:
定理 affineBasisCover_is_basis
  条件: (X : 概形.{u})
  证明: by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact IsOpenImmersion.isOpen_range (X.affineBasisCover.f a)
  · rintro a U haU hU
    rcases X.affineCover.covers a with ⟨x, e⟩
    let U' := (X.affineCover.f (X.affineCover.idx a)) ⁻¹' U
    have hxU' : x in 

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isOpen_range, PrimeSpectrum, PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open, TopologicalSpace, TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds, X.affineBasisCover.f, X.affineCover.covers, X.affineCover.f, X.affineCover.idx, affineBasisCover, affineCover, continuous, continuous.isOpen_preimage, covers, exists_subset_of_mem_open, isBasis_basic_opens, isOpen_preimage, isOpen_range, isTopologicalBasis_of_isOpen_of_nhds
-/
theorem affineBasisCover_is_basis (X : Scheme.{u}) :
    TopologicalSpace.IsTopologicalBasis
      {x : Set X |
        exists a : X.affineBasisCover.I₀, x = Set.range (X.affineBasisCover.f a)} := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact IsOpenImmersion.isOpen_range (X.affineBasisCover.f a)
  · rintro a U haU hU
    rcases X.affineCover.covers a with ⟨x, e⟩
    let U' := (X.affineCover.f (X.affineCover.idx a)) ⁻¹' U
    have hxU' : x in U' := by rw [← e] at haU; exact haU
    rcases PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU'
        ((X.affineCover.f (X.affineCover.idx a)).continuous.isOpen_preimage _
          hU) with
      ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hxV, hVU⟩
    refine ⟨_, ⟨⟨_, s⟩, rfl⟩, ?_, ?_⟩ <;> rw [affineBasisCover_map_range]
    · exact ⟨x, hxV, e⟩
    · rw [Set.image_subset_iff]; exact hVU

end deprecated

end Scheme

end AlgebraicGeometry
