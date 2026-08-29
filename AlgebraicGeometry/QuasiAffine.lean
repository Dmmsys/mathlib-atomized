/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!

# Quasi-affine schemes

## Main results
- `IsQuasiAffine`:
  A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an immersion.
  This actually implies that `X ⟶ Spec Γ(X, ⊤)` is an open immersion.
- `IsQuasiAffine.of_isImmersion`:
  Any quasi-compact locally closed subscheme of a quasi-affine scheme is quasi-affine.

-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an immersion.
This actually implies that `X ⟶ Spec Γ(X, ⊤)` is an open immersion. -/
@[stacks 01P6]
/--
Definition of `IsQuasiAffine` / `IsQuasiAffine` 的定义

English:
class IsQuasiAffine
  parameters: (X : Scheme.{u})
  (no additional axioms)

中文:
类 是QuasiAffine
  参数: (X : 概形.{u})
  (无附加公理)
-/
class IsQuasiAffine (X : Scheme.{u}) : Prop extends
  CompactSpace X, IsImmersion X.toSpecΓ

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance (priority := low) [IsAffine X] : X.IsQuasiAffine where

instance (priority := low) [X.IsQuasiAffine] : X.IsSeparated where
  isSeparated_terminal_from := by
    rw [← terminal.comp_from X.toSpecΓ]
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.IsQuasiAffine]
  signature: : IsOpenImmersion X.toSpecΓ
  body: by
  have : IsIso X.toSpecΓ.imageι := by delta Hom.imageι Hom.image; rw [X.ker_toSpecΓ]; infer_instance
  rw [← X.toSpecΓ.toImage_imageι]
  infer_instance

中文:
实例 [X.是QuasiAffine]
  签名: : 是开浸入 X.toSpecΓ
  定义体: by
  have : IsIso X.toSpecΓ.imageι := by delta Hom.imageι Hom.image; rw [X.ker_toSpecΓ]; infer_instance
  rw [← X.toSpecΓ.toImage_imageι]
  infer_instance

Depends on / 依赖: Hom.image, X.ker_toSpec, X.toSpec, infer_instance
-/
instance [X.IsQuasiAffine] : IsOpenImmersion X.toSpecΓ := by
  have : IsIso X.toSpecΓ.imageι := by delta Hom.imageι Hom.image; rw [X.ker_toSpecΓ]; infer_instance
  rw [← X.toSpecΓ.toImage_imageι]
  infer_instance

/-- Any quasicompact locally closed subscheme of a quasi-affine scheme is quasi-affine. -/
@[stacks 0BCK]
/--
lemma `IsQuasiAffine.of_isImmersion` / 引理 `IsQuasiAffine.of_isImmersion`

English:
lemma IsQuasiAffine.of_isImmersion
  proof: by
  have : IsImmersion (X.toSpecΓ ≫ Spec.map f.appTop) := by rw [← toSpecΓ_naturality]; infer_instance
  have : IsImmersion X.toSpecΓ := .of_comp _ (Spec.map f.appTop)
  constructor

中文:
引理 是QuasiAffine.of_isImmersion
  证明: by
  have : IsImmersion (X.toSpecΓ ≫ Spec.map f.appTop) := by rw [← toSpecΓ_naturality]; infer_instance
  have : IsImmersion X.toSpecΓ := .of_comp _ (Spec.map f.appTop)
  constructor

Depends on / 依赖: IsImmersion, Spec.map, X.toSpec, appTop, f.appTop, infer_instance, of_comp
-/
lemma IsQuasiAffine.of_isImmersion
    [Y.IsQuasiAffine] [IsImmersion f] [CompactSpace X] : X.IsQuasiAffine := by
  have : IsImmersion (X.toSpecΓ ≫ Spec.map f.appTop) := by rw [← toSpecΓ_naturality]; infer_instance
  have : IsImmersion X.toSpecΓ := .of_comp _ (Spec.map f.appTop)
  constructor

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsQuasiAffine.isBasis_basicOpen` / 引理 `IsQuasiAffine.isBasis_basicOpen`

English:
lemma IsQuasiAffine.isBasis_basicOpen
  given: (X : Scheme.{u}) [IsQuasiAffine X]
  proof: by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hxU => ?_
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU⟩ := (PrimeSpectrum.isBasis_basic_opens
    (R := Γ(X, ⊤))).exists_subset_of_mem_open (Set.mem_image_of_mem _ hxU) (X.toSpecΓ ''ᵁ U).2
  simp_rw [← toSpecΓ_preimage_basicOpen]
  refine ⟨_, ⟨r, ?_, rfl

中文:
引理 是QuasiAffine.isBasis_basicOpen
  条件: (X : 概形.{u}) [是QuasiAffine X]
  证明: by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hxU => ?_
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU⟩ := (PrimeSpectrum.isBasis_basic_opens
    (R := Γ(X, ⊤))).exists_subset_of_mem_open (Set.mem_image_of_mem _ hxU) (X.toSpecΓ ''ᵁ U).2
  simp_rw [← toSpecΓ_preimage_basicOpen]
  refine ⟨_, ⟨r, ?_, rfl

Depends on / 依赖: Hom.isAffineOpen_iff_of_isOpenImmersion, IsAffineOpen, IsAffineOpen.Spec_basicOpen, Opens.isBasis_iff_nbhd.mpr, PrimeSpectrum, PrimeSpectrum.isBasis_basic_opens, Set.mem_image_of_mem, Set.preimage_image_eq, Set.preimage_mono, SetLike, SetLike.co, Spec_basicOpen, X.toSpec, convert, exists_subset_of_mem_open, injective, isAffineOpen_iff_of_isOpenImmersion, isBasis_basic_opens, isBasis_iff_nbhd, isEmbedding
-/
lemma IsQuasiAffine.isBasis_basicOpen (X : Scheme.{u}) [IsQuasiAffine X] :
    Opens.IsBasis { X.basicOpen r | (r : Γ(X, ⊤)) (_ : IsAffineOpen (X.basicOpen r)) } := by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hxU => ?_
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU⟩ := (PrimeSpectrum.isBasis_basic_opens
    (R := Γ(X, ⊤))).exists_subset_of_mem_open (Set.mem_image_of_mem _ hxU) (X.toSpecΓ ''ᵁ U).2
  simp_rw [← toSpecΓ_preimage_basicOpen]
  refine ⟨_, ⟨r, ?_, rfl⟩, hxr, (Set.preimage_mono hrU).trans_eq
    (Set.preimage_image_eq _ X.toSpecΓ.isEmbedding.injective)⟩
  rw [← Hom.isAffineOpen_iff_of_isOpenImmersion X.toSpecΓ]
  convert! IsAffineOpen.Spec_basicOpen r
  exact SetLike.coe_injective (Set.image_preimage_eq_of_subset
    (hrU.trans (Set.image_subset_range _ _)))

/--
lemma `IsQuasiAffine.of_forall_exists_mem_basicOpen` / 引理 `IsQuasiAffine.of_forall_exists_mem_basicOpen`

English:
lemma IsQuasiAffine.of_forall_exists_mem_basicOpen
  statement: (X : Scheme.{u}) [CompactSpace X]
  proof: by
  suffices IsOpenImmersion X.toSpecΓ by constructor
  have : QuasiSeparatedSpace X := by
    choose r hr hxr using H
    exact .of_isOpenCover (U := (X.basicOpen <| r ·))
      (eq_top_iff.mpr fun _ _ => Opens.mem_iSup.mpr ⟨_, hxr _⟩)
      (fun _ => isRetrocompact_basicOpen _) (fun x => (hr _).i

中文:
引理 是QuasiAffine.of_对任意_存在_mem_basicOpen
  结论: (X : 概形.{u}) [紧空间 X]
  证明: by
  suffices IsOpenImmersion X.toSpecΓ by constructor
  have : QuasiSeparatedSpace X := by
    choose r hr hxr using H
    exact .of_isOpenCover (U := (X.basicOpen <| r ·))
      (eq_top_iff.mpr fun _ _ => Opens.mem_iSup.mpr ⟨_, hxr _⟩)
      (fun _ => isRetrocompact_basicOpen _) (fun x => (hr _).i

Depends on / 依赖: IsOpenImmersio, IsOpenImmersion, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.of_forall_source_exists_preimage, Opens.mem_iSup.mpr, PrimeSpectrum, PrimeSpectrum.basicOpen, QuasiSeparatedSpace, X.basicOpen, X.toSpec, basicOpen, eq_top_iff, eq_top_iff.mpr, isQuasiSeparated, isRetrocompact_basicOpen, mem_iSup, of_forall_source_exists_preimage, of_isOpenCover
-/
lemma IsQuasiAffine.of_forall_exists_mem_basicOpen (X : Scheme.{u}) [CompactSpace X]
    (H : forall x : X, exists r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x in X.basicOpen r) :
    IsQuasiAffine X := by
  suffices IsOpenImmersion X.toSpecΓ by constructor
  have : QuasiSeparatedSpace X := by
    choose r hr hxr using H
    exact .of_isOpenCover (U := (X.basicOpen <| r ·))
      (eq_top_iff.mpr fun _ _ => Opens.mem_iSup.mpr ⟨_, hxr _⟩)
      (fun _ => isRetrocompact_basicOpen _) (fun x => (hr _).isQuasiSeparated)
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x => ?_
  obtain ⟨r, hr, hxr⟩ := H x
  refine ⟨PrimeSpectrum.basicOpen r, (X.toSpecΓ_preimage_basicOpen r).ge hxr, ?_⟩
  suffices IsOpenImmersion ((X.basicOpen r).ι ≫ X.toSpecΓ) by
    convert! this <;> rw [toSpecΓ_preimage_basicOpen]
  rw [← Opens.toSpecΓ_SpecMap_presheaf_map_top]
  have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
  exact MorphismProperty.comp_mem _ hr.isoSpec.hom _ inferInstance (.of_isLocalization r)

/--
lemma `IsQuasiAffine.of_isAffineHom` / 引理 `IsQuasiAffine.of_isAffineHom`

English:
lemma IsQuasiAffine.of_isAffineHom
  given: [IsAffineHom f] [Y.IsQuasiAffine]
  statement: X.IsQuasiAffine
  proof: by
  have := QuasiCompact.compactSpace_of_compactSpace f
  refine .of_forall_exists_mem_basicOpen _ fun x => ?_
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ := (IsQuasiAffine.isBasis_basicOpen
    Y).exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  refine ⟨f.appTop r, ?_⟩
  rw [← preimag

中文:
引理 是QuasiAffine.of_isAffineHom
  条件: [是仿射态射 f] [Y.是QuasiAffine]
  结论: X.是QuasiAffine
  证明: by
  have := QuasiCompact.compactSpace_of_compactSpace f
  refine .of_forall_exists_mem_basicOpen _ fun x => ?_
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ := (IsQuasiAffine.isBasis_basicOpen
    Y).exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  refine ⟨f.appTop r, ?_⟩
  rw [← preimag

Depends on / 依赖: IsQuasiAffine, IsQuasiAffine.isBasis_basicOpen, QuasiCompact, QuasiCompact.compactSpace_of_compactSpace, Set.mem_univ, appTop, compactSpace_of_compactSpace, exists_subset_of_mem_open, f.appTop, hr.preimage, isBasis_basicOpen, isOpen_univ, mem_univ, of_forall_exists_mem_basicOpen, preimage, preimage_basicOpen_top
-/
lemma IsQuasiAffine.of_isAffineHom [IsAffineHom f] [Y.IsQuasiAffine] : X.IsQuasiAffine := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  refine .of_forall_exists_mem_basicOpen _ fun x => ?_
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ := (IsQuasiAffine.isBasis_basicOpen
    Y).exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  refine ⟨f.appTop r, ?_⟩
  rw [← preimage_basicOpen_top]
  exact ⟨hr.preimage _, hxr⟩

/--
Definition of `openCoverBasicOpenTop` / `openCoverBasicOpenTop` 的定义

English:
definition openCoverBasicOpenTop
  signature: (X : Scheme.{u}) [X.IsQuasiAffine]
  body: X.openCoverOfIsOpenCover (fun i : { r // IsAffineOpen (X.basicOpen (U := ⊤) r) } =>
    X.basicOpen i.1) <| top_le_iff.mp fun x _ => by
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
    (IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact Opens.mem_iSu

中文:
定义 openCoverBasicOpenTop
  签名: (X : 概形.{u}) [X.是QuasiAffine]
  定义体: X.openCoverOfIsOpenCover (fun i : { r // IsAffineOpen (X.basicOpen (U := ⊤) r) } =>
    X.basicOpen i.1) <| top_le_iff.mp fun x _ => by
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
    (IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact Opens.mem_iSu
-/
@[simps! f] def openCoverBasicOpenTop (X : Scheme.{u}) [X.IsQuasiAffine] :
    X.OpenCover :=
  X.openCoverOfIsOpenCover (fun i : { r // IsAffineOpen (X.basicOpen (U := ⊤) r) } =>
    X.basicOpen i.1) <| top_le_iff.mp fun x _ => by
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
    (IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact Opens.mem_iSup.mpr ⟨⟨r, hr⟩, hxr⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isPullback_toSpecΓ_toSpecΓ` / 引理 `isPullback_toSpecΓ_toSpecΓ`

English:
lemma isPullback_toSpecΓ_toSpecΓ
  given: (f : X ⟶ Y) [IsAffineHom f] [Y.IsQuasiAffine]
  proof: by
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := Scheme.IsQuasiAffine.of_isAffineHom f
  have (r : Γ(Y, ⊤)) :
      IsPushout f.appTop (Y.presheaf.map (homOfLE le_top).op)
        (X.presheaf.map (homOfLE le_top).op) (f.appLE (Y.basicOpen r)
          (X.basicOpen (f.appTop r)) (Sc

中文:
引理 isPullback_toSpecΓ_toSpecΓ
  条件: (f : X ⟶ Y) [是仿射态射 f] [Y.是QuasiAffine]
  证明: by
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := Scheme.IsQuasiAffine.of_isAffineHom f
  have (r : Γ(Y, ⊤)) :
      IsPushout f.appTop (Y.presheaf.map (homOfLE le_top).op)
        (X.presheaf.map (homOfLE le_top).op) (f.appLE (Y.basicOpen r)
          (X.basicOpen (f.appTop r)) (Sc

Depends on / 依赖: CommRingCa, IsPushout, IsQuasiAffine, QuasiCompact, QuasiCompact.compactSpace_of_compactSpace, Scheme, Scheme.IsQuasiAffine.of_isAffineHom, Scheme.preimage_basicOpen_top, X.basicOpen, X.presheaf.map, Y.basicOpen, Y.presheaf.map, appTop, basicOpen, compactSpace_of_compactSpace, f.appLE, f.appTop, homOfLE, isCompact_univ, isLocalization_basicOpen_of_qcqs
-/
lemma isPullback_toSpecΓ_toSpecΓ (f : X ⟶ Y) [IsAffineHom f] [Y.IsQuasiAffine] :
    IsPullback f X.toSpecΓ Y.toSpecΓ (Spec.map f.appTop) := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := Scheme.IsQuasiAffine.of_isAffineHom f
  have (r : Γ(Y, ⊤)) :
      IsPushout f.appTop (Y.presheaf.map (homOfLE le_top).op)
        (X.presheaf.map (homOfLE le_top).op) (f.appLE (Y.basicOpen r)
          (X.basicOpen (f.appTop r)) (Scheme.preimage_basicOpen_top ..).ge) := by
    have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
    have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ (f.appTop r)
    refine CommRingCat.isPushout_of_isLocalization f.appTop.hom (f.appLE (Y.basicOpen r)
      (X.basicOpen (f.appTop r)) (Scheme.preimage_basicOpen_top ..).ge).hom ?_ (.powers r)
    change CommRingCat.Hom.hom (Y.presheaf.map _ ≫ f.appLE _ _ _) =
      CommRingCat.Hom.hom (f.appTop ≫ X.presheaf.map _)
    rw [f.map_appLE]; rw [Scheme.Hom.appLE]
  refine isPullback_of_openCover _ _ _ _ Y.openCoverBasicOpenTop fun r => ?_
  let e : pullback f (Y.basicOpen r.1).ι ≅ Spec Γ(X, X.basicOpen (f.appTop r.1)) :=
    pullbackRestrictIsoRestrict _ _ ≪≫ X.isoOfEq (Scheme.preimage_basicOpen_top f r.1) ≪≫
    IsAffineOpen.isoSpec (by rw [← Scheme.preimage_basicOpen_top]; exact r.2.preimage f)
  refine .of_iso ((this r.1).op.map Scheme.Spec) e.symm r.2.isoSpec.symm (.refl _) (.refl _)
    ?_ ?_ (by simp) (by simp)
  · simp only [Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    dsimp [e, Scheme.Cover.pullbackHom, IsAffineOpen.isoSpec_hom, Scheme.Hom.appLE]
    simp only [homOfLE_leOfHom, Spec.map_comp, Category.assoc,
      Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, Scheme.Opens.toSpecΓ_naturality]
    simp_rw [← Category.assoc]
    congr 1
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp [pullback.condition]
  · simp only [Iso.symm_hom, Iso.eq_inv_comp]
    simp [e, IsAffineOpen.isoSpec_hom]

/--
lemma `preimage_opensRange_toSpecΓ` / 引理 `preimage_opensRange_toSpecΓ`

English:
lemma preimage_opensRange_toSpecΓ
  given: (f : X ⟶ Y) [IsAffineHom f] [X.IsQuasiAffine] [Y.IsQuasiAffine]
  proof: by
  simpa using (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (isPullback_toSpecΓ_toSpecΓ f) ⊤).symm

中文:
引理 preimage_opensRange_toSpecΓ
  条件: (f : X ⟶ Y) [是仿射态射 f] [X.是QuasiAffine] [Y.是QuasiAffine]
  证明: by
  simpa using (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (isPullback_toSpecΓ_toSpecΓ f) ⊤).symm

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback, image_preimage_eq_preimage_image_of_isPullback
-/
lemma preimage_opensRange_toSpecΓ (f : X ⟶ Y) [IsAffineHom f] [X.IsQuasiAffine] [Y.IsQuasiAffine] :
    Spec.map f.appTop ⁻¹ᵁ Y.toSpecΓ.opensRange = X.toSpecΓ.opensRange := by
  simpa using (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (isPullback_toSpecΓ_toSpecΓ f) ⊤).symm

end AlgebraicGeometry.Scheme
