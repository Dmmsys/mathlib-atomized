/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!

# `Π Rᵢ`-Points of Schemes

We show that the canonical map `X(Π Rᵢ) ⟶ Π X(Rᵢ)` (`AlgebraicGeometry.pointsPi`)
is injective and surjective under various assumptions.

-/

@[expose] public section

open CategoryTheory Limits PrimeSpectrum

namespace AlgebraicGeometry

universe u v

variable {ι : Type u} (R : ι -> CommRingCat.{u})

/--
lemma `Ideal.span_eq_top_of_span_image_evalRingHom` / 引理 `Ideal.span_eq_top_of_span_image_evalRingHom`

English:
lemma Ideal.span_eq_top_of_span_image_evalRingHom
  proof: by
  simp only [Ideal.eq_top_iff_one, ← Subtype.range_val (s := s), ← Set.range_comp,
    Finsupp.mem_ideal_span_range_iff_exists_finsupp] at hs' ⊢
  choose f hf using hs'
  have : Fintype s := hs.fintype
  refine ⟨Finsupp.equivFunOnFinite.symm fun i x => f x i, ?_⟩
  ext i
  simpa [Finsupp.sum_fint

中文:
引理 Ideal.span_eq_top_of_span_image_evalRingHom
  证明: by
  simp only [Ideal.eq_top_iff_one, ← Subtype.range_val (s := s), ← Set.range_comp,
    Finsupp.mem_ideal_span_range_iff_exists_finsupp] at hs' ⊢
  choose f hf using hs'
  have : Fintype s := hs.fintype
  refine ⟨Finsupp.equivFunOnFinite.symm fun i x => f x i, ?_⟩
  ext i
  simpa [Finsupp.sum_fint

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite.symm, Finsupp.mem_ideal_span_range_iff_exists_finsupp, Finsupp.sum_fintype, Fintype, Ideal.eq_top_iff_one, Set.range_comp, Subtype, Subtype.range_val, eq_top_iff_one, equivFunOnFinite, fintype, hs.fintype, mem_ideal_span_range_iff_exists_finsupp, range_comp, range_val, sum_fintype
-/
lemma Ideal.span_eq_top_of_span_image_evalRingHom
    {ι} {R : ι -> Type*} [forall i, CommRing (R i)] (s : Set (Π i, R i))
    (hs : s.Finite) (hs' : forall i, Ideal.span (Pi.evalRingHom (R ·) i '' s) = ⊤) :
    Ideal.span s = ⊤ := by
  simp only [Ideal.eq_top_iff_one, ← Subtype.range_val (s := s), ← Set.range_comp,
    Finsupp.mem_ideal_span_range_iff_exists_finsupp] at hs' ⊢
  choose f hf using hs'
  have : Fintype s := hs.fintype
  refine ⟨Finsupp.equivFunOnFinite.symm fun i x => f x i, ?_⟩
  ext i
  simpa [Finsupp.sum_fintype] using hf i

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eq_top_of_sigmaSpec_subset_of_isCompact` / 引理 `eq_top_of_sigmaSpec_subset_of_isCompact`

English:
lemma eq_top_of_sigmaSpec_subset_of_isCompact
  proof: by
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff _).mp U.2
  obtain ⟨t, hts, ht, ht'⟩ : exists t subseteq s, t.Finite ∧ V subseteq ⋃ i in t, (basicOpen i).1 := by
    obtain ⟨t, ht⟩ := hV'.elim_finite_subcover
      (fun i : s => (basicOpen i.1).1) (fun _ => (basicOpen _).2)
      (by simpa [← Set.c

中文:
引理 eq_top_of_sigmaSpec_subset_of_isCompact
  证明: by
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff _).mp U.2
  obtain ⟨t, hts, ht, ht'⟩ : exists t subseteq s, t.Finite ∧ V subseteq ⋃ i in t, (basicOpen i).1 := by
    obtain ⟨t, ht⟩ := hV'.elim_finite_subcover
      (fun i : s => (basicOpen i.1).1) (fun _ => (basicOpen _).2)
      (by simpa [← Set.c
-/
lemma eq_top_of_sigmaSpec_subset_of_isCompact
    (U : (Spec <| .of <| Π i, R i).Opens) (V : Set (Spec <| .of <| Π i, R i))
    (hV : ↑(sigmaSpec R).opensRange subseteq V)
    (hV' : IsCompact (X := Spec (.of <| Π i, R i)) V)
    (hVU : V subseteq U) : U = ⊤ := by
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff _).mp U.2
  obtain ⟨t, hts, ht, ht'⟩ : exists t subseteq s, t.Finite ∧ V subseteq ⋃ i in t, (basicOpen i).1 := by
    obtain ⟨t, ht⟩ := hV'.elim_finite_subcover
      (fun i : s => (basicOpen i.1).1) (fun _ => (basicOpen _).2)
      (by simpa [← Set.compl_iInter, ← zeroLocus_iUnion₂ (κ := (· in s)), ← hs])
    exact ⟨t.map (Function.Embedding.subtype _), by simp, Finset.finite_toSet _, by simpa using ht⟩
  replace ht' : V subseteq (zeroLocus t)ᶜ := by
    simpa [← Set.compl_iInter, ← zeroLocus_iUnion₂ (κ := (· in t))] using ht'
  have (i : _) : Ideal.span (Pi.evalRingHom (R ·) i '' t) = ⊤ := by
    rw [← zeroLocus_empty_iff_eq_top]; rw [zeroLocus_span]; rw [← preimage_comap_zeroLocus]; rw [← Set.compl_univ_iff]; rw [← Set.preimage_compl]; rw [Set.preimage_eq_univ_iff]
    trans (Sigma.ι _ i ≫ sigmaSpec R).opensRange.1
    · simp; rfl
    · rw [Scheme.Hom.opensRange_comp]
      exact (Set.image_subset_range _ _).trans (hV.trans ht')
  have : Ideal.span s = ⊤ := top_le_iff.mp
    ((Ideal.span_eq_top_of_span_image_evalRingHom _ ht this).ge.trans (Ideal.span_mono hts))
  simpa [← zeroLocus_span s, zeroLocus_empty_iff_eq_top.mpr this] using hs

/--
lemma `eq_bot_of_comp_quotientMk_eq_sigmaSpec` / 引理 `eq_bot_of_comp_quotientMk_eq_sigmaSpec`

English:
lemma eq_bot_of_comp_quotientMk_eq_sigmaSpec
  statement: (I : Ideal (Π i, R i))
  proof: by
  refine le_bot_iff.mp fun x hx => ?_
  ext i
  simpa [← Category.assoc, Ideal.Quotient.eq_zero_iff_mem.mpr hx] using
    congr((Spec.preimage (Sigma.ι (Spec <| R ·) i ≫ $hf)).hom x).symm

中文:
引理 eq_bot_of_comp_quotientMk_eq_sigmaSpec
  结论: (I : Ideal (Π i, R i))
  证明: by
  refine le_bot_iff.mp fun x hx => ?_
  ext i
  simpa [← Category.assoc, Ideal.Quotient.eq_zero_iff_mem.mpr hx] using
    congr((Spec.preimage (Sigma.ι (Spec <| R ·) i ≫ $hf)).hom x).symm

Depends on / 依赖: Category, Category.assoc, Ideal.Quotient.eq_zero_iff_mem.mpr, Quotient, Spec.preimage, eq_zero_iff_mem, le_bot_iff, le_bot_iff.mp, preimage
-/
lemma eq_bot_of_comp_quotientMk_eq_sigmaSpec (I : Ideal (Π i, R i))
    (f : (∐ fun i => Spec (R i)) ⟶ Spec (.of <| (Π i, R i) ⧸ I))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = sigmaSpec R) :
    I = ⊥ := by
  refine le_bot_iff.mp fun x hx => ?_
  ext i
  simpa [← Category.assoc, Ideal.Quotient.eq_zero_iff_mem.mpr hx] using
    congr((Spec.preimage (Sigma.ι (Spec <| R ·) i ≫ $hf)).hom x).symm

/--
lemma `isIso_of_comp_eq_sigmaSpec` / 引理 `isIso_of_comp_eq_sigmaSpec`

English:
lemma isIso_of_comp_eq_sigmaSpec
  statement: {V : Scheme}
  proof: by
  have : g.coborderRange = ⊤ := by
    apply eq_top_of_sigmaSpec_subset_of_isCompact (hVU := subset_coborder)
    · simpa only [← hU'] using! Set.range_comp_subset_range f g
    · exact isCompact_range g.continuous
  have : IsClosedImmersion g := by
    have : IsIso g.coborderRange.ι := by rw [th

中文:
引理 isIso_of_comp_eq_sigmaSpec
  结论: {V : Scheme}
  证明: by
  have : g.coborderRange = ⊤ := by
    apply eq_top_of_sigmaSpec_subset_of_isCompact (hVU := subset_coborder)
    · simpa only [← hU'] using! Set.range_comp_subset_range f g
    · exact isCompact_range g.continuous
  have : IsClosedImmersion g := by
    have : IsIso g.coborderRange.ι := by rw [th

Depends on / 依赖: IsClosedImmersion, IsClosedImmersion.Spec_iff.mp, Scheme, Scheme.topIso_hom, Set.range_comp_subset_range, Spec_iff, coborderRange, continuous, e.hom, eq_bot_of_comp_quotientMk_eq_sigmaSpec, eq_top_of_sigmaSpec_subset_of_isCompact, g.coborderRange, g.continuous, g.liftCoborder_, infer_instance, isCompact_range, range_comp_subset_range, subset_coborder, topIso_hom
-/
lemma isIso_of_comp_eq_sigmaSpec {V : Scheme}
    (f : (∐ fun i => Spec (R i)) ⟶ V) (g : V ⟶ Spec (.of <| Π i, R i))
    [IsImmersion g] [CompactSpace V]
    (hU' : f ≫ g = sigmaSpec R) : IsIso g := by
  have : g.coborderRange = ⊤ := by
    apply eq_top_of_sigmaSpec_subset_of_isCompact (hVU := subset_coborder)
    · simpa only [← hU'] using! Set.range_comp_subset_range f g
    · exact isCompact_range g.continuous
  have : IsClosedImmersion g := by
    have : IsIso g.coborderRange.ι := by rw [this, ← Scheme.topIso_hom]; infer_instance
    rw [← g.liftCoborder_ι]
    infer_instance
  obtain ⟨I, e, rfl⟩ := IsClosedImmersion.Spec_iff.mp this
  obtain rfl := eq_bot_of_comp_quotientMk_eq_sigmaSpec R I (f ≫ e.hom) (by rwa [Category.assoc])
  convert_to! IsIso (e.hom ≫ Spec.map (RingEquiv.quotientBot _).toCommRingCatIso.inv)
  infer_instance

variable (X : Scheme)

/-- The canonical map `X(Π Rᵢ) ⟶ Π X(Rᵢ)`.
This is injective if `X` is quasi-separated, surjective if `X` is affine,
or if `X` is compact and each `Rᵢ` is local. -/
noncomputable
/--
Definition of `pointsPi` / `pointsPi` 的定义

English:
definition pointsPi
  signature: : (Spec (.of <| Π i, R i) ⟶ X) -> Π i, Spec (R i) ⟶ X
  body: fun f i => Spec.map (CommRingCat.ofHom (Pi.evalRingHom (R ·) i)) ≫ f

中文:
定义 pointsPi
  签名: : (Spec (.of <| Π i, R i) ⟶ X) -> Π i, Spec (R i) ⟶ X
  定义体: fun f i => Spec.map (CommRingCat.ofHom (Pi.evalRingHom (R ·) i)) ≫ f

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Pi.evalRingHom, Spec.map, evalRingHom
-/
def pointsPi : (Spec (.of <| Π i, R i) ⟶ X) -> Π i, Spec (R i) ⟶ X :=
  fun f i => Spec.map (CommRingCat.ofHom (Pi.evalRingHom (R ·) i)) ≫ f

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pointsPi_injective` / 引理 `pointsPi_injective`

English:
lemma pointsPi_injective
  given: [QuasiSeparatedSpace X]
  statement: Function.Injective (pointsPi R X)
  proof: by
  rintro f g e
  have := isIso_of_comp_eq_sigmaSpec R (V := equalizer f g)
    (equalizer.lift (sigmaSpec R) (by ext1 i; simpa using! congr_fun e i))
    (equalizer.ι f g) (by simp)
  rw [← cancel_epi (equalizer.ι f g)]; rw [equalizer.condition]

中文:
引理 pointsPi_injective
  条件: [QuasiSeparatedSpace X]
  结论: Function.Injective (pointsPi R X)
  证明: by
  rintro f g e
  have := isIso_of_comp_eq_sigmaSpec R (V := equalizer f g)
    (equalizer.lift (sigmaSpec R) (by ext1 i; simpa using! congr_fun e i))
    (equalizer.ι f g) (by simp)
  rw [← cancel_epi (equalizer.ι f g)]; rw [equalizer.condition]

Depends on / 依赖: cancel_epi, condition, congr_fun, equalizer, equalizer.condition, equalizer.lift, isIso_of_comp_eq_sigmaSpec, sigmaSpec
-/
lemma pointsPi_injective [QuasiSeparatedSpace X] : Function.Injective (pointsPi R X) := by
  rintro f g e
  have := isIso_of_comp_eq_sigmaSpec R (V := equalizer f g)
    (equalizer.lift (sigmaSpec R) (by ext1 i; simpa using! congr_fun e i))
    (equalizer.ι f g) (by simp)
  rw [← cancel_epi (equalizer.ι f g)]; rw [equalizer.condition]

/--
lemma `pointsPi_surjective_of_isAffine` / 引理 `pointsPi_surjective_of_isAffine`

English:
lemma pointsPi_surjective_of_isAffine
  given: [IsAffine X]
  statement: Function.Surjective (pointsPi R X)
  proof: by
  rintro f
  refine ⟨Spec.map (CommRingCat.ofHom
    (RingHom.pi fun i => (Spec.preimage (f i ≫ X.isoSpec.hom)).1)) ≫ X.isoSpec.inv, ?_⟩
  ext i : 1
  simp only [pointsPi, ← Spec.map_comp_assoc, Iso.comp_inv_eq]
  exact Spec.map_preimage _

中文:
引理 pointsPi_surjective_of_isAffine
  条件: [IsAffine X]
  结论: Function.Surjective (pointsPi R X)
  证明: by
  rintro f
  refine ⟨Spec.map (CommRingCat.ofHom
    (RingHom.pi fun i => (Spec.preimage (f i ≫ X.isoSpec.hom)).1)) ≫ X.isoSpec.inv, ?_⟩
  ext i : 1
  simp only [pointsPi, ← Spec.map_comp_assoc, Iso.comp_inv_eq]
  exact Spec.map_preimage _

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Iso.comp_inv_eq, RingHom, RingHom.pi, Spec.map, Spec.map_comp_assoc, Spec.map_preimage, Spec.preimage, X.isoSpec.hom, X.isoSpec.inv, comp_inv_eq, isoSpec, map_comp_assoc, map_preimage, pointsPi, preimage
-/
lemma pointsPi_surjective_of_isAffine [IsAffine X] : Function.Surjective (pointsPi R X) := by
  rintro f
  refine ⟨Spec.map (CommRingCat.ofHom
    (RingHom.pi fun i => (Spec.preimage (f i ≫ X.isoSpec.hom)).1)) ≫ X.isoSpec.inv, ?_⟩
  ext i : 1
  simp only [pointsPi, ← Spec.map_comp_assoc, Iso.comp_inv_eq]
  exact Spec.map_preimage _

/--
lemma `pointsPi_surjective` / 引理 `pointsPi_surjective`

English:
lemma pointsPi_surjective
  given: [CompactSpace X] [forall i, IsLocalRing (R i)]
  proof: by
  intro f
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  have (i : _) : exists j, Set.range (f i) subseteq (𝒰.f j).opensRange := by
    refine ⟨𝒰.idx ((f i) (IsLocalRing.closedPoint (R i))), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map (f i).continuous

中文:
引理 pointsPi_surjective
  条件: [CompactSpace X] [对任意 i, IsLocalRing (R i)]
  证明: by
  intro f
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  have (i : _) : exists j, Set.range (f i) subseteq (𝒰.f j).opensRange := by
    refine ⟨𝒰.idx ((f i) (IsLocalRing.closedPoint (R i))), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map (f i).continuous

Depends on / 依赖: IsLocalRing, IsLocalRing.closedPoint, IsLocalRing.specializes_closedPoint, IsOpenImmersion, IsOpenImmersion.lift, OpenCover, Set.range, X.OpenCover, X.affineCover.finiteSubcover, affineCover, closedPoint, continuous, covers, finiteSubcover, mem_open, opensRange, pointsPi_surjective_of_isAffine, specializes_closedPoint, subseteq
-/
lemma pointsPi_surjective [CompactSpace X] [forall i, IsLocalRing (R i)] :
    Function.Surjective (pointsPi R X) := by
  intro f
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  have (i : _) : exists j, Set.range (f i) subseteq (𝒰.f j).opensRange := by
    refine ⟨𝒰.idx ((f i) (IsLocalRing.closedPoint (R i))), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map (f i).continuous).mem_open
      (𝒰.f _).opensRange.2 (𝒰.covers _)
  choose j hj using this
  have (j₀ : _) := pointsPi_surjective_of_isAffine (ι := { i // j i = j₀ }) (R ·) (𝒰.X j₀)
    (fun i => IsOpenImmersion.lift (𝒰.f j₀) (f i.1) (by rcases i with ⟨i, rfl⟩; exact hj i))
  choose g hg using this
  simp_rw [funext_iff, pointsPi] at hg
  let R' (j₀) := CommRingCat.of (Π i : { i // j i = j₀ }, R i)
  let e : (Π i, R i) ≃+* Π j₀, R' j₀ :=
  { toFun f _ i := f i
    invFun f i := f _ ⟨i, rfl⟩
    right_inv _ := funext₂ fun j₀ i => by rcases i with ⟨i, rfl⟩; rfl
    map_mul' _ _ := rfl
    map_add' _ _ := rfl }
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ inv (sigmaSpec R') ≫
    Sigma.desc fun j₀ => g j₀ ≫ 𝒰.f j₀, ?_⟩
  ext i : 1
  have : (Pi.evalRingHom (R ·) i).comp e.symm.toRingHom =
    (Pi.evalRingHom _ ⟨i, rfl⟩).comp (Pi.evalRingHom (R' ·) (j i)) := rfl
  rw [pointsPi]; rw [← Spec.map_comp_assoc]; rw [← CommRingCat.ofHom_comp]; rw [this]; rw [CommRingCat.ofHom_comp]; rw [Spec.map_comp_assoc]; rw [← ι_sigmaSpec R']; rw [Category.assoc]; rw [IsIso.hom_inv_id_assoc]; rw [Sigma.ι_desc]; rw [← Category.assoc]; rw [hg]; rw [IsOpenImmersion.lift_fac]

end AlgebraicGeometry
