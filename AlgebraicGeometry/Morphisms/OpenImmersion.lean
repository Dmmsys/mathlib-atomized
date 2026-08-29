/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!

# Open immersions

A morphism is an open immersion if the underlying map of spaces is an open embedding
`f : X ⟶ U ⊆ Y`, and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Most of the theories are developed in `AlgebraicGeometry/OpenImmersion`, and we provide the
remaining theorems analogous to other lemmas in `AlgebraicGeometry/Morphisms/*`.

-/

public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isOpenImmersion_SpecMap_iff_of_surjective` / 引理 `isOpenImmersion_SpecMap_iff_of_surjective`

English:
lemma isOpenImmersion_SpecMap_iff_of_surjective
  statement: {R S : CommRingCat}
  proof: by
  constructor
  · intro H
    obtain ⟨e, he, he'⟩ := PrimeSpectrum.isClopen_iff_zeroLocus.mp
      ⟨PrimeSpectrum.isClosed_range_comap_of_surjective _ _ hf,
        (Spec.map f).isOpenEmbedding.isOpen_range⟩
    refine ⟨e, he, ?_⟩
    let φ : R ⟶ _ := (CommRingCat.ofHom (Ideal.Quotient.mk (.span {e})))
    have : IsOpenImmersion (Spec.map φ) :=
      have : IsLocalization.Away (1 - e) (↑R ⧸ Ideal.span {e}) :=
        IsLocalization.away_of_isIdempotentElem he.one_sub (by simp) Ideal.Quotient.mk_surjective
      IsOpenImmersion.of_isLocalization (1 - e)
    have H : Set.range (Spec.map φ) = Set.range (Spec.map f) :=
      ((range_comap_of_surjective _ _
        Ideal.Quotient.mk_surjective).trans (by simp)).trans he'.symm
    let i : S ≅ .of _ := (Scheme.Spec.preimageIso
      (IsOpenImmersion.isoOfRangeEq (Spec.map φ) (Spec.map f) H)).unop
    have hi : Function.Injective i.inv.hom := (ConcreteCategory.bijective_of_isIso i.inv).1
    have : f = φ ≫ i.inv := by apply Spec.map_injective; simp [i, ← Scheme.Spec_map]
    rw [this]; rw [CommRingCat.hom_comp]; rw [RingHom.ker_eq_comap_bot]; rw [← Ideal.comap_comap]; rw [← RingHom.ker_eq_comap_bot]; rw [(RingHom.injective_iff_ker_eq_bot i.inv.hom).mp hi]; rw [← RingHom.ker_eq_comap_bot]
    simp [φ]
  · rintro ⟨e, he, he'⟩
    let := f.hom.toAlgebra
    have : IsLocalization.Away (1 - e) S :=
      IsLocalization.away_of_isIdempotentElem he.one_sub (by simpa using! he') hf
    exact IsOpenImmersion.of_isLocalization (1 - e)

中文:
引理 isOpenImmersion_SpecMap_iff_of_surjective
  结论: {R S : 交换环范畴}
  证明: by
  constructor
  · intro H
    obtain ⟨e, he, he'⟩ := PrimeSpectrum.isClopen_iff_zeroLocus.mp
      ⟨PrimeSpectrum.isClosed_range_comap_of_surjective _ _ hf,
        (Spec.map f).isOpenEmbedding.isOpen_range⟩
    refine ⟨e, he, ?_⟩
    let φ : R ⟶ _ := (CommRingCat.ofHom (Ideal.Quotient.mk (.span {e})))
    have : IsOpenImmersion (Spec.map φ) :=
      have : IsLocalization.Away (1 - e) (↑R ⧸ Ideal.span {e}) :=
        IsLocalization.away_of_isIdempotentElem he.one_sub (by simp) Ideal.Quotient.mk_surjective
      IsOpenImmersion.of_isLocalization (1 - e)
    have H : Set.range (Spec.map φ) = Set.range (Spec.map f) :=
      ((range_comap_of_surjective _ _
        Ideal.Quotient.mk_surjective).trans (by simp)).trans he'.symm
    let i : S ≅ .of _ := (Scheme.Spec.preimageIso
      (IsOpenImmersion.isoOfRangeEq (Spec.map φ) (Spec.map f) H)).unop
    have hi : Function.Injective i.inv.hom := (ConcreteCategory.bijective_of_isIso i.inv).1
    have : f = φ ≫ i.inv := by apply Spec.map_injective; simp [i, ← Scheme.Spec_map]
    rw [this]; rw [CommRingCat.hom_comp]; rw [RingHom.ker_eq_comap_bot]; rw [← Ideal.comap_comap]; rw [← RingHom.ker_eq_comap_bot]; rw [(RingHom.injective_iff_ker_eq_bot i.inv.hom).mp hi]; rw [← RingHom.ker_eq_comap_bot]
    simp [φ]
  · rintro ⟨e, he, he'⟩
    let := f.hom.toAlgebra
    have : IsLocalization.Away (1 - e) S :=
      IsLocalization.away_of_isIdempotentElem he.one_sub (by simpa using! he') hf
    exact IsOpenImmersion.of_isLocalization (1 - e)

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.span, IsLocalization, IsLocalization.Away, IsLocalization.away_of_isIdempotentElem, IsOpenImmersion, IsOpenImmersion.of_isLocalization, PrimeSpectrum, PrimeSpectrum.isClopen_iff_zeroLocus.mp, PrimeSpectrum.isClosed_range_comap_of_surjective, Quotient, Spec.map, away_of_isIdempotentElem, he.one_sub, isClopen_iff_zeroLocus, isClosed_range_comap_of_surjective, isOpenEmbedding
-/
lemma isOpenImmersion_SpecMap_iff_of_surjective {R S : CommRingCat}
    (f : R ⟶ S) (hf : Function.Surjective f.hom) :
    IsOpenImmersion (Spec.map f) ↔
    exists e, IsIdempotentElem e ∧ RingHom.ker f.hom = Ideal.span {e} := by
  constructor
  · intro H
    obtain ⟨e, he, he'⟩ := PrimeSpectrum.isClopen_iff_zeroLocus.mp
      ⟨PrimeSpectrum.isClosed_range_comap_of_surjective _ _ hf,
        (Spec.map f).isOpenEmbedding.isOpen_range⟩
    refine ⟨e, he, ?_⟩
    let φ : R ⟶ _ := (CommRingCat.ofHom (Ideal.Quotient.mk (.span {e})))
    have : IsOpenImmersion (Spec.map φ) :=
      have : IsLocalization.Away (1 - e) (↑R ⧸ Ideal.span {e}) :=
        IsLocalization.away_of_isIdempotentElem he.one_sub (by simp) Ideal.Quotient.mk_surjective
      IsOpenImmersion.of_isLocalization (1 - e)
    have H : Set.range (Spec.map φ) = Set.range (Spec.map f) :=
      ((range_comap_of_surjective _ _
        Ideal.Quotient.mk_surjective).trans (by simp)).trans he'.symm
    let i : S ≅ .of _ := (Scheme.Spec.preimageIso
      (IsOpenImmersion.isoOfRangeEq (Spec.map φ) (Spec.map f) H)).unop
    have hi : Function.Injective i.inv.hom := (ConcreteCategory.bijective_of_isIso i.inv).1
    have : f = φ ≫ i.inv := by apply Spec.map_injective; simp [i, ← Scheme.Spec_map]
    rw [this]; rw [CommRingCat.hom_comp]; rw [RingHom.ker_eq_comap_bot]; rw [← Ideal.comap_comap]; rw [← RingHom.ker_eq_comap_bot]; rw [(RingHom.injective_iff_ker_eq_bot i.inv.hom).mp hi]; rw [← RingHom.ker_eq_comap_bot]
    simp [φ]
  · rintro ⟨e, he, he'⟩
    let := f.hom.toAlgebra
    have : IsLocalization.Away (1 - e) S :=
      IsLocalization.away_of_isIdempotentElem he.one_sub (by simpa using! he') hf
    exact IsOpenImmersion.of_isLocalization (1 - e)

variable {X Y : Scheme.{u}}

@[deprecated (since := "2026-01-20")]
alias isOpenImmersion_iff_stalk := IsOpenImmersion.iff_isIso_stalkMap

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsOpenImmersion.of_openCover_source` / 定理 `IsOpenImmersion.of_openCover_source`

English:
theorem IsOpenImmersion.of_openCover_source
  statement: (f : X ⟶ Y)
  proof: by
  refine IsOpenImmersion.iff_isIso_stalkMap.mpr
    ⟨.of_continuous_injective_isOpenMap f.continuous hf ?_, ?_⟩
  · intro U hU
    convert! (⨆ i, ((𝒰.f i ≫ f) ''ᵁ (𝒰.f i ⁻¹ᵁ ⟨U, hU⟩))).2
    ext x
    exact ⟨fun ⟨x, _, _⟩ => by have := 𝒰.exists_eq x; simp; grind, by simp; grind⟩
  · intro x
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    rw [← (IsIso.comp_inv_eq _).mpr (Scheme.Hom.stalkMap_comp (𝒰.f i) f x)]
    infer_instance

中文:
定理 是开浸入.of_openCover_source
  结论: (f : X ⟶ Y)
  证明: by
  refine IsOpenImmersion.iff_isIso_stalkMap.mpr
    ⟨.of_continuous_injective_isOpenMap f.continuous hf ?_, ?_⟩
  · intro U hU
    convert! (⨆ i, ((𝒰.f i ≫ f) ''ᵁ (𝒰.f i ⁻¹ᵁ ⟨U, hU⟩))).2
    ext x
    exact ⟨fun ⟨x, _, _⟩ => by have := 𝒰.exists_eq x; simp; grind, by simp; grind⟩
  · intro x
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    rw [← (IsIso.comp_inv_eq _).mpr (Scheme.Hom.stalkMap_comp (𝒰.f i) f x)]
    infer_instance

Depends on / 依赖: IsIso.comp_inv_eq, IsOpenImmersion, IsOpenImmersion.iff_isIso_stalkMap.mpr, Scheme, Scheme.Hom.stalkMap_comp, comp_inv_eq, continuous, convert, exists_eq, f.continuous, iff_isIso_stalkMap, infer_instance, of_continuous_injective_isOpenMap, stalkMap_comp
-/
theorem IsOpenImmersion.of_openCover_source (f : X ⟶ Y)
    (𝒰 : X.OpenCover) (hf : Function.Injective f) (h𝒰 : forall i, IsOpenImmersion (𝒰.f i ≫ f)) :
    IsOpenImmersion f := by
  refine IsOpenImmersion.iff_isIso_stalkMap.mpr
    ⟨.of_continuous_injective_isOpenMap f.continuous hf ?_, ?_⟩
  · intro U hU
    convert! (⨆ i, ((𝒰.f i ≫ f) ''ᵁ (𝒰.f i ⁻¹ᵁ ⟨U, hU⟩))).2
    ext x
    exact ⟨fun ⟨x, _, _⟩ => by have := 𝒰.exists_eq x; simp; grind, by simp; grind⟩
  · intro x
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    rw [← (IsIso.comp_inv_eq _).mpr (Scheme.Hom.stalkMap_comp (𝒰.f i) f x)]
    infer_instance

/--
lemma `IsOpenImmersion.of_forall_source_exists` / 引理 `IsOpenImmersion.of_forall_source_exists`

English:
lemma IsOpenImmersion.of_forall_source_exists
  statement: (f : X ⟶ Y)
  proof: by
  choose U i _ hxi hi using hX
  let 𝒰 : X.OpenCover := ⟨⟨X, U, i⟩,
    ⟨by simpa using show forall x, exists j y, i j y = x from (⟨_, hxi ·⟩), by simpa⟩⟩
  exact IsOpenImmersion.of_openCover_source f 𝒰 hf hi

中文:
引理 是开浸入.of_对任意_source_存在
  结论: (f : X ⟶ Y)
  证明: by
  choose U i _ hxi hi using hX
  let 𝒰 : X.OpenCover := ⟨⟨X, U, i⟩,
    ⟨by simpa using show forall x, exists j y, i j y = x from (⟨_, hxi ·⟩), by simpa⟩⟩
  exact IsOpenImmersion.of_openCover_source f 𝒰 hf hi

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.of_openCover_source, OpenCover, X.OpenCover, of_openCover_source
-/
lemma IsOpenImmersion.of_forall_source_exists (f : X ⟶ Y)
    (hf : Function.Injective f)
    (hX : forall x, exists (U : Scheme) (i : U ⟶ X) (_ : IsOpenImmersion i),
      x in i.opensRange ∧ IsOpenImmersion (i ≫ f)) :
    IsOpenImmersion f := by
  choose U i _ hxi hi using hX
  let 𝒰 : X.OpenCover := ⟨⟨X, U, i⟩,
    ⟨by simpa using show forall x, exists j y, i j y = x from (⟨_, hxi ·⟩), by simpa⟩⟩
  exact IsOpenImmersion.of_openCover_source f 𝒰 hf hi

/--
theorem `isOpenImmersion_eq_inf` / 定理 `isOpenImmersion_eq_inf`

English:
theorem isOpenImmersion_eq_inf
  proof: by
  ext
  exact IsOpenImmersion.iff_isIso_stalkMap.trans
    (and_congr Iff.rfl (forall_congr' fun x => ConcreteCategory.isIso_iff_bijective _))

中文:
定理 isOpenImmersion_eq_inf
  证明: by
  ext
  exact IsOpenImmersion.iff_isIso_stalkMap.trans
    (and_congr Iff.rfl (forall_congr' fun x => ConcreteCategory.isIso_iff_bijective _))

Depends on / 依赖: ConcreteCategory, ConcreteCategory.isIso_iff_bijective, Iff.rfl, IsOpenImmersion, IsOpenImmersion.iff_isIso_stalkMap.trans, and_congr, forall_congr, iff_isIso_stalkMap, isIso_iff_bijective
-/
theorem isOpenImmersion_eq_inf :
    @IsOpenImmersion = (topologically IsOpenEmbedding) ⊓ stalkwise (Function.Bijective ·) := by
  ext
  exact IsOpenImmersion.iff_isIso_stalkMap.trans
    (and_congr Iff.rfl (forall_congr' fun x => ConcreteCategory.isIso_iff_bijective _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtTarget (stalkwise (Function.Bijective ·))
  body: by
  apply stalkwiseIsZariskiLocalAtTarget_of_respectsIso
  rw [RingHom.toMorphismProperty_respectsIso_iff]
  convert! (inferInstance : (MorphismProperty.isomorphisms CommRingCat).RespectsIso)
  ext
  exact (ConcreteCategory.isIso_iff_bijective _).symm

中文:
实例 :
  签名: IsZariskiLocalAtTarget (stalkwise (函数.双射 ·))
  定义体: by
  apply stalkwiseIsZariskiLocalAtTarget_of_respectsIso
  rw [RingHom.toMorphismProperty_respectsIso_iff]
  convert! (inferInstance : (MorphismProperty.isomorphisms CommRingCat).RespectsIso)
  ext
  exact (ConcreteCategory.isIso_iff_bijective _).symm

Depends on / 依赖: CommRingCat, ConcreteCategory, ConcreteCategory.isIso_iff_bijective, MorphismProperty, MorphismProperty.isomorphisms, RespectsIso, RingHom, RingHom.toMorphismProperty_respectsIso_iff, convert, isIso_iff_bijective, isomorphisms, stalkwiseIsZariskiLocalAtTarget_of_respectsIso, toMorphismProperty_respectsIso_iff
-/
instance : IsZariskiLocalAtTarget (stalkwise (Function.Bijective ·)) := by
  apply stalkwiseIsZariskiLocalAtTarget_of_respectsIso
  rw [RingHom.toMorphismProperty_respectsIso_iff]
  convert! (inferInstance : (MorphismProperty.isomorphisms CommRingCat).RespectsIso)
  ext
  exact (ConcreteCategory.isIso_iff_bijective _).symm

/--
Instance `isOpenImmersion_isZariskiLocalAtTarget` / 实例 `isOpenImmersion_isZariskiLocalAtTarget`

English:
instance isOpenImmersion_isZariskiLocalAtTarget
  signature: : IsZariskiLocalAtTarget @IsOpenImmersion
  body: isOpenImmersion_eq_inf ▸ inferInstance

中文:
实例 isOpenImmersion_isZariskiLocalAtTarget
  签名: : IsZariskiLocalAtTarget @是开浸入
  定义体: isOpenImmersion_eq_inf ▸ inferInstance

Depends on / 依赖: isOpenImmersion_eq_inf
-/
instance isOpenImmersion_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @IsOpenImmersion :=
  isOpenImmersion_eq_inf ▸ inferInstance

instance {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (coprod.map f g) :=
  IsZariskiLocalAtTarget.coprodMap f g ‹_› ‹_›

end AlgebraicGeometry
