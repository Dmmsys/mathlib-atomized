/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # Functoriality of Proj -/

@[expose] public section

universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj

namespace AlgebraicGeometry

section universe_polymorphic

variable {A B C σ τ ψ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : Nat -> σ} {ℬ : Nat -> τ} {𝒞 : Nat -> ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 ->+*ᵍ ℬ) (g : ℬ ->+*ᵍ 𝒞) (hf : ℬ₊ <= 𝒜₊.map f) (hg : 𝒞₊ <= ℬ₊.map g)

namespace ProjectiveSpectrum

/--
Definition of `comapFun` / `comapFun` 的定义

English:
definition comapFun
  signature: (p : ProjectiveSpectrum ℬ)
  body: p.1.comap f
  isPrime := p.2.comap f
not_irrelevant_le le := p.3 hf.trans map_le_of_le_comap _ le

中文:
定义 comapFun
  签名: (p : ProjectiveSpectrum ℬ)
  定义体: p.1.comap f
  isPrime := p.2.comap f
not_irrelevant_le le := p.3 hf.trans map_le_of_le_comap _ le
-/
@[simps] def comapFun (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
not_irrelevant_le le := p.3 hf.trans map_le_of_le_comap _ le

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  body: comapFun f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s => ⟨f '' s, by ext; simp⟩

中文:
定义 comap
  签名: : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  定义体: comapFun f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s => ⟨f '' s, by ext; simp⟩

Depends on / 依赖: comapFun
-/
def comap : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := comapFun f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s => ⟨f '' s, by ext; simp⟩

end ProjectiveSpectrum

namespace Proj

open StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 subseteq ProjectiveSpectrum.comap f hf ⁻¹' U.1)

/--
Definition of `comapStructureSheafFun` / `comapStructureSheafFun` 的定义

English:
definition comapStructureSheafFun
  body: localRingHom f _ y.1.1.1 rfl s ⟨.comap f hf y.1, hUV y.2⟩

中文:
定义 comapStructureSheafFun
  定义体: localRingHom f _ y.1.1.1 rfl s ⟨.comap f hf y.1, hUV y.2⟩

Depends on / 依赖: localRingHom
-/
noncomputable def comapStructureSheafFun
    (s : forall x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtPrime ℬ y.1.1.1 :=
localRingHom f _ y.1.1.1 rfl s ⟨.comap f hf y.1, hUV y.2⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isLocallyFraction_comapStructureSheafFun` / 引理 `isLocallyFraction_comapStructureSheafFun`

English:
lemma isLocallyFraction_comapStructureSheafFun
  proof: by
  rintro ⟨p, hpV⟩
  rcases hs ⟨.comap f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ => hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ => ?_⟩
  e

中文:
引理 isLocallyFraction_comapStructureSheafFun
  证明: by
  rintro ⟨p, hpV⟩
  rcases hs ⟨.comap f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ => hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ => ?_⟩
  e

Depends on / 依赖: Opens.infLERight, ProjectiveSpectrum, ProjectiveSpectrum.comap, W.comap, comapStructureSheafFun, f.gradedAddHom, gradedAddHom, h_frac, infLERight, specialize
-/
lemma isLocallyFraction_comapStructureSheafFun
    (s : forall x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (comapStructureSheafFun f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨.comap f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ => hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ => ?_⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [comapStructureSheafFun]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `comapStructureSheaf` / `comapStructureSheaf` 的定义

English:
definition comapStructureSheaf
  signature: :
  body: ⟨comapStructureSheafFun _ _ _ _ hUV s.1,
      isLocallyFraction_comapStructureSheafFun _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [comapStructureSheafFun]
  map_zero' := by ext; simp [comapStructureSheafFun]
  map_add' x y := by ext; simp [comapStructureSheafFun]
  map_mul' x y := by ext; simp [

中文:
定义 comapStructureSheaf
  签名: :
  定义体: ⟨comapStructureSheafFun _ _ _ _ hUV s.1,
      isLocallyFraction_comapStructureSheafFun _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [comapStructureSheafFun]
  map_zero' := by ext; simp [comapStructureSheafFun]
  map_add' x y := by ext; simp [comapStructureSheafFun]
  map_mul' x y := by ext; simp [

Depends on / 依赖: comapStructureSheafFun
-/
noncomputable def comapStructureSheaf :
    (Proj.structureSheaf 𝒜).1.obj (.op U) ->+* (Proj.structureSheaf ℬ).1.obj (.op V) where
  toFun s := ⟨comapStructureSheafFun _ _ _ _ hUV s.1,
      isLocallyFraction_comapStructureSheafFun _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [comapStructureSheafFun]
  map_zero' := by ext; simp [comapStructureSheafFun]
  map_add' x y := by ext; simp [comapStructureSheafFun]
  map_mul' x y := by ext; simp [comapStructureSheafFun]

end Proj

end universe_polymorphic

section universe_monomorphic

namespace Proj

variable {A B C σ τ ψ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : Nat -> σ} {ℬ : Nat -> τ} {𝒞 : Nat -> ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 ->+*ᵍ ℬ) (g : ℬ ->+*ᵍ 𝒞) (hf : ℬ₊ <= 𝒜₊.map f) (hg : 𝒞₊ <= ℬ₊.map g)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `sheafedSpaceMap` / `sheafedSpaceMap` 的定义

English:
definition sheafedSpaceMap
  signature: :
  body: { base := TopCat.ofHom <| comap f hf
      c := { app U := CommRingCat.ofHom <| comapStructureSheaf f hf _ _ Set.Subset.rfl } }

中文:
定义 sheafedSpaceMap
  签名: :
  定义体: { base := TopCat.ofHom <| comap f hf
      c := { app U := CommRingCat.ofHom <| comapStructureSheaf f hf _ _ Set.Subset.rfl } }
-/
@[simps! (isSimp := false)] noncomputable def sheafedSpaceMap :
    Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom <| comap f hf
      c := { app U := CommRingCat.ofHom <| comapStructureSheaf f hf _ _ Set.Subset.rfl } }

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `germ_map_sectionInBasicOpen` / 引理 `germ_map_sectionInBasicOpen`

English:
lemma germ_map_sectionInBasicOpen
  statement: {p : ProjectiveSpectrum ℬ}
  proof: rfl

中文:
引理 germ_map_sectionInBasicOpen
  结论: {p : ProjectiveSpectrum ℬ}
  证明: rfl
-/
lemma germ_map_sectionInBasicOpen {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (p.comap f hf).1.toIdeal.primeCompl) :
    (toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (sheafedSpaceMap f hf).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap f hf).hom.c.app _ (sectionInBasicOpen 𝒜 _ c)) =
    (toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen ℬ p (c.map _ le_rfl)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `val_sectionInBasicOpen_apply` / 引理 `val_sectionInBasicOpen_apply`

English:
lemma val_sectionInBasicOpen_apply
  statement: (p : ProjectiveSpectrum.top 𝒜)
  proof: rfl

中文:
引理 val_sectionInBasicOpen_apply
  结论: (p : ProjectiveSpectrum.top 𝒜)
  证明: rfl
-/
@[simp] lemma val_sectionInBasicOpen_apply (p : ProjectiveSpectrum.top 𝒜)
    (c : NumDenSameDeg 𝒜 p.1.toIdeal.primeCompl)
    (q : ProjectiveSpectrum.basicOpen 𝒜 c.den) :
    ((sectionInBasicOpen 𝒜 p c).val q).val = .mk c.num ⟨c.den, q.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `localRingHom_comp_stalkIso` / 定理 `localRingHom_comp_stalkIso`

English:
theorem localRingHom_comp_stalkIso
  given: (p : ProjectiveSpectrum ℬ)
  proof: by
  rw [← Iso.eq_inv_comp]; rw [Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_app

中文:
定理 localRingHom_comp_stalkIso
  条件: (p : ProjectiveSpectrum ℬ)
  证明: by
  rw [← Iso.eq_inv_comp]; rw [Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_app
-/
@[elementwise] theorem localRingHom_comp_stalkIso (p : ProjectiveSpectrum ℬ) :
    (stalkIso 𝒜 (ProjectiveSpectrum.comap f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (stalkIso ℬ p).inv =
      (sheafedSpaceMap f hf).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp]; rw [Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply]
  simp only [GradedRingHom.toRingHom_eq_toRingHom, Localization.localRingHom_mk,
    GradedRingHom.coe_toRingHom]
  -- I sincerely apologise for your eyes.
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_map_sectionInBasicOpen]
  erw [stalkIso'_germ]
  simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : Proj ℬ ⟶ Proj 𝒜 where
  body: (sheafedSpaceMap f hf).hom
  prop p := .mk fun x hx => by
    rw [← localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx :=

中文:
定义 map
  签名: : Proj ℬ ⟶ Proj 𝒜 where
  定义体: (sheafedSpaceMap f hf).hom
  prop p := .mk fun x hx => by
    rw [← localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx :=

Depends on / 依赖: sheafedSpaceMap
-/
noncomputable def map : Proj ℬ ⟶ Proj 𝒜 where
  __ := (sheafedSpaceMap f hf).hom
  prop p := .mk fun x hx => by
    rw [← localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (stalkIso 𝒜 (p.comap f hf)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

/--
theorem `map_preimage_basicOpen` / 定理 `map_preimage_basicOpen`

English:
theorem map_preimage_basicOpen
  given: (s : A)
  proof: rfl

中文:
定理 map_preimage_basicOpen
  条件: (s : A)
  证明: rfl
-/
@[simp] theorem map_preimage_basicOpen (s : A) :
    map f hf ⁻¹ᵁ basicOpen 𝒜 s = basicOpen ℬ (f s) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ι_comp_map` / 定理 `ι_comp_map`

English:
theorem ι_comp_map
  given: (s : A)
  statement: (basicOpen ℬ (f s)).ι ≫ map f hf =
  proof: by simp

中文:
定理 ι_comp_map
  条件: (s : A)
  结论: (basicOpen ℬ (f s)).ι ≫ map f hf =
  证明: by simp
-/
theorem ι_comp_map (s : A) : (basicOpen ℬ (f s)).ι ≫ map f hf =
    (map f hf).resLE _ _ le_rfl ≫ (basicOpen 𝒜 s).ι := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `awayToSection_comp_appLE` / 引理 `awayToSection_comp_appLE`

English:
lemma awayToSection_comp_appLE
  given: {i : Nat} {s : A} (hs : s in 𝒜 i)
  proof: by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hs
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
refine Subtype.ext funext fun p => ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

中文:
引理 awayToSection_comp_appLE
  条件: {i : 自然数} {s : A} (hs : s in 𝒜 i)
  证明: by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hs
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
refine Subtype.ext funext fun p => ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp
-/
@[reassoc] lemma awayToSection_comp_appLE {i : Nat} {s : A} (hs : s in 𝒜 i) :
    awayToSection 𝒜 s ≫
      Scheme.Hom.appLE (map f hf) (basicOpen 𝒜 s) (basicOpen ℬ (f s)) (by rfl) =
    CommRingCat.ofHom (Away.map f s : Away 𝒜 s ->+* Away ℬ (f s)) ≫
      awayToSection ℬ (f s) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hs
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
refine Subtype.ext funext fun p => ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `awayι_comp_map` / 定理 `awayι_comp_map`

English:
theorem awayι_comp_map
  given: {i : Nat} (hi : 0 < i) (s : A) (hs : s in 𝒜 i)
  proof: by
  rw [awayι]; rw [awayι]; rw [Category.assoc]; rw [ι_comp_map]; rw [← Category.assoc]; rw [← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]
refine ext_to_Spec (cancel_mono (basicOpen ℬ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenT

中文:
定理 awayι_comp_map
  条件: {i : 自然数} (hi : 0 < i) (s : A) (hs : s in 𝒜 i)
  证明: by
  rw [awayι]; rw [awayι]; rw [Category.assoc]; rw [ι_comp_map]; rw [← Category.assoc]; rw [← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]
refine ext_to_Spec (cancel_mono (basicOpen ℬ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenT
-/
@[reassoc] theorem awayι_comp_map {i : Nat} (hi : 0 < i) (s : A) (hs : s in 𝒜 i) :
    awayι ℬ (f s) (f.2 hs) hi ≫ map f hf =
    Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ awayι 𝒜 s hs hi := by
  rw [awayι]; rw [awayι]; rw [Category.assoc]; rw [ι_comp_map]; rw [← Category.assoc]; rw [← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq]; rw [← Category.assoc]; rw [Iso.eq_comp_inv]
refine ext_to_Spec (cancel_mono (basicOpen ℬ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, awayToSection_comp_appLE _ _ hs]

/--
Definition of `mapAffineOpenCover` / `mapAffineOpenCover` 的定义

English:
definition mapAffineOpenCover
  signature: : (Proj ℬ).AffineOpenCover
  body: affineOpenCoverOfIrrelevantLESpan _ (fun s : (affineOpenCover 𝒜).I₀ => f s.2) (fun s => f.2 s.2.2)
(fun s => s.1.2) (toIdeal_le_toIdeal_iff.mpr hf).trans
Ideal.map_le_of_le_comap (toIdeal_irrelevant_le _).mpr fun i hi x hx =>
    Ideal.subset_span ⟨⟨⟨i, hi⟩, ⟨x, hx⟩⟩, rfl⟩

中文:
定义 mapAffineOpenCover
  签名: : (Proj ℬ).AffineOpenCover
  定义体: affineOpenCoverOfIrrelevantLESpan _ (fun s : (affineOpenCover 𝒜).I₀ => f s.2) (fun s => f.2 s.2.2)
(fun s => s.1.2) (toIdeal_le_toIdeal_iff.mpr hf).trans
Ideal.map_le_of_le_comap (toIdeal_irrelevant_le _).mpr fun i hi x hx =>
    Ideal.subset_span ⟨⟨⟨i, hi⟩, ⟨x, hx⟩⟩, rfl⟩
-/
@[simps! I₀ f] noncomputable def mapAffineOpenCover : (Proj ℬ).AffineOpenCover :=
  affineOpenCoverOfIrrelevantLESpan _ (fun s : (affineOpenCover 𝒜).I₀ => f s.2) (fun s => f.2 s.2.2)
(fun s => s.1.2) (toIdeal_le_toIdeal_iff.mpr hf).trans
Ideal.map_le_of_le_comap (toIdeal_irrelevant_le _).mpr fun i hi x hx =>
    Ideal.subset_span ⟨⟨⟨i, hi⟩, ⟨x, hx⟩⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: map (g.comp f) (irrelevant_le_map_comp hf hg) = map g hg ≫ map f hf
  proof: by
  refine (mapAffineOpenCover _ <| irrelevant_le_map_comp hf hg).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f,
    awayι_comp_map (g.comp f) _ s.1.2 _ s.2.2]
  simp [awayι_comp_map_assoc _ _ _ _ (map_mem f s.2.2), awayι_comp_map _ _ _ _ s.

中文:
定理 map_comp
  结论: map (g.comp f) (irrelevant_le_map_comp hf hg) = map g hg ≫ map f hf
  证明: by
  refine (mapAffineOpenCover _ <| irrelevant_le_map_comp hf hg).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f,
    awayι_comp_map (g.comp f) _ s.1.2 _ s.2.2]
  simp [awayι_comp_map_assoc _ _ _ _ (map_mem f s.2.2), awayι_comp_map _ _ _ _ s.

Depends on / 依赖: AffineOpenCover, Scheme, Scheme.AffineOpenCover.openCover_f, g.comp, hom_ext, irrelevant_le_map_comp, mapAffineOpenCover, mapAffineOpenCover_f, map_mem, openCover, openCover.hom_ext, openCover_f
-/
theorem map_comp : map (g.comp f) (irrelevant_le_map_comp hf hg) = map g hg ≫ map f hf := by
  refine (mapAffineOpenCover _ <| irrelevant_le_map_comp hf hg).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f,
    awayι_comp_map (g.comp f) _ s.1.2 _ s.2.2]
  simp [awayι_comp_map_assoc _ _ _ _ (map_mem f s.2.2), awayι_comp_map _ _ _ _ s.2.2]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (.id 𝒜) (by simp) = 𝟙 (Proj 𝒜)
  proof: by
  refine (affineOpenCover _).openCover.hom_ext _ _ fun s => ?_
  convert! awayι_comp_map (.id 𝒜) _ _ _ s.2.2 using 1
  simp

中文:
定理 map_id
  结论: map (.id 𝒜) (by simp) = 𝟙 (Proj 𝒜)
  证明: by
  refine (affineOpenCover _).openCover.hom_ext _ _ fun s => ?_
  convert! awayι_comp_map (.id 𝒜) _ _ _ s.2.2 using 1
  simp

Depends on / 依赖: affineOpenCover, convert, hom_ext, openCover, openCover.hom_ext
-/
theorem map_id : map (.id 𝒜) (by simp) = 𝟙 (Proj 𝒜) := by
  refine (affineOpenCover _).openCover.hom_ext _ _ fun s => ?_
  convert! awayι_comp_map (.id 𝒜) _ _ _ s.2.2 using 1
  simp

end Proj

end universe_monomorphic

end AlgebraicGeometry
