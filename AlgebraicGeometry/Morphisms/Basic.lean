/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.Data.List.TFAE

/-!
# Properties of morphisms between Schemes

We provide the basic framework for talking about properties of morphisms between Schemes.

A `MorphismProperty Scheme` is a predicate on morphisms between schemes. For properties local at
the target, its behaviour is entirely determined by its definition on morphisms into affine schemes,
which we call an `AffineTargetMorphismProperty`. In this file, we provide API lemmas for properties
local at the target, and special support for those properties whose `AffineTargetMorphismProperty`
takes on a simpler form. We also provide API lemmas for properties local at the source.
The main interfaces of the API are the typeclasses `IsZariskiLocalAtTarget`,
`IsZariskiLocalAtSource` and `HasAffineProperty`, which we describe in detail below.

## `IsZariskiLocalAtTarget`

- `AlgebraicGeometry.IsZariskiLocalAtTarget`: We say that `IsZariskiLocalAtTarget P` for
  `P : MorphismProperty Scheme` if
  1. `P` respects isomorphisms.
  2. `P` holds for `f ∣_ U` for an open cover `U` of `Y` if and only if `P` holds for `f`.

For a morphism property `P` local at the target and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback`:
    `P` is preserved under pullback along open immersions.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`:
    `P f → P (f ∣_ U)` for an open `U` of `Y`.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, P (f ∣_ U i)` for a family `U` of open sets covering `Y`.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover`:
    `P f ↔ ∀ i, P (𝒰.pullbackHom f i)` for `𝒰 : Y.OpenCover`.

## `IsZariskiLocalAtSource`

- `AlgebraicGeometry.IsZariskiLocalAtSource`: We say that `IsZariskiLocalAtSource P` for
  `P : MorphismProperty Scheme` if
  1. `P` respects isomorphisms.
  2. `P` holds for `𝒰.f i ≫ f` for an open cover `𝒰` of `X` iff `P` holds for `f : X ⟶ Y`.

For a morphism property `P` local at the source and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.IsZariskiLocalAtSource.comp`:
    `P` is preserved under composition with open immersions at the source.
- `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, P ((U i).ι ≫ f)` for a family `U` of open sets covering `X`.
- `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`:
    `P f ↔ ∀ i, P (𝒰.f i ≫ f)` for `𝒰 : X.OpenCover`.
- `AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion`: If `P` contains identities then `P`
    holds for open immersions.

## `AffineTargetMorphismProperty`

- `AlgebraicGeometry.AffineTargetMorphismProperty`:
    The type of predicates on `f : X ⟶ Y` with `Y` affine.
- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal`: We say that `P.IsLocal` if `P`
    satisfies the assumptions of the affine communication lemma
    (`AlgebraicGeometry.of_affine_open_cover`). That is,
    1. `P` respects isomorphisms.
    2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basicOpen r` for any
      global section `r`.
    3. If `P` holds for `f ∣_ Y.basicOpen r` for all `r` in a spanning set of the global sections,
      then `P` holds for `f`.

## `HasAffineProperty`

- `AlgebraicGeometry.HasAffineProperty`:
  `HasAffineProperty P Q` is a type class asserting that `P` is local at the target,
  and over affine schemes, it is equivalent to `Q : AffineTargetMorphismProperty`.

For `HasAffineProperty P Q` and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.HasAffineProperty.of_isPullback`:
    `P` is preserved under pullback along open immersions from affine schemes.
- `AlgebraicGeometry.HasAffineProperty.restrict`:
    `P f → Q (f ∣_ U)` for affine `U` of `Y`.
- `AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, Q (f ∣_ U i)` for a family `U` of affine open sets covering `Y`.
- `AlgebraicGeometry.HasAffineProperty.iff_of_openCover`:
    `P f ↔ ∀ i, Q (𝒰.pullbackHom f i)` for affine open covers `𝒰` of `Y`.
- `AlgebraicGeometry.HasAffineProperty.isStableUnderBaseChange`:
    If `Q` is stable under affine base change, then `P` is stable under arbitrary base change.

## Implementation details

The properties `IsZariskiLocalAtTarget` and `IsZariskiLocalAtSource` are defined as abbreviations
for the respective local property of morphism properties defined generally for categories equipped
with a `Precoverage`.
-/

@[expose] public section


universe u v

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

/--
Definition of `IsZariskiLocalAtTarget` / `IsZariskiLocalAtTarget` 的定义

English:
abbreviation IsZariskiLocalAtTarget
  signature: (P : MorphismProperty Scheme.{u})
  body: P.IsLocalAtTarget Scheme.zariskiPrecoverage

中文:
缩写 IsZariskiLocalAtTarget
  签名: (P : Morphism命题erty Scheme.{u})
  定义体: P.IsLocalAtTarget Scheme.zariskiPrecoverage

Depends on / 依赖: IsLocalAtTarget, P.IsLocalAtTarget, Scheme, Scheme.zariskiPrecoverage, zariskiPrecoverage
-/
abbrev IsZariskiLocalAtTarget (P : MorphismProperty Scheme.{u}) :=
  P.IsLocalAtTarget Scheme.zariskiPrecoverage

namespace IsZariskiLocalAtTarget

/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  statement: {P : MorphismProperty Scheme} [P.RespectsIso]
  proof: by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 => ?_
  refine ⟨fun hf i => (P.arrow_mk_iso_iff (morphismRestrictOpensRange _ _)).mp (restrict _ _ hf),
    fun h => ?_⟩
  refine of_sSup_eq_top f _ (Scheme.OpenCover.iSup_opensRange <| .ulift 𝒰) ?_
  exact fun i => (P.arrow_mk_iso_iff (morphism

中文:
引理 mk'
  结论: {P : Morphism命题erty Scheme} [P.RespectsIso]
  证明: by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 => ?_
  refine ⟨fun hf i => (P.arrow_mk_iso_iff (morphismRestrictOpensRange _ _)).mp (restrict _ _ hf),
    fun h => ?_⟩
  refine of_sSup_eq_top f _ (Scheme.OpenCover.iSup_opensRange <| .ulift 𝒰) ?_
  exact fun i => (P.arrow_mk_iso_iff (morphism
-/
protected lemma mk' {P : MorphismProperty Scheme} [P.RespectsIso]
    (restrict : forall {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens), P f -> P (f ∣_ U))
    (of_sSup_eq_top :
      forall {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι -> Y.Opens), iSup U = ⊤ ->
        (forall i, P (f ∣_ U i)) -> P f) :
    IsZariskiLocalAtTarget P := by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 => ?_
  refine ⟨fun hf i => (P.arrow_mk_iso_iff (morphismRestrictOpensRange _ _)).mp (restrict _ _ hf),
    fun h => ?_⟩
  refine of_sSup_eq_top f _ (Scheme.OpenCover.iSup_opensRange <| .ulift 𝒰) ?_
  exact fun i => (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (h _)

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (𝒰 : Y.OpenCover)

/--
lemma `of_isPullback` / 引理 `of_isPullback`

English:
lemma of_isPullback
  statement: {UX UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY]
  proof: MorphismProperty.IsLocalAtTarget.of_isPullback (Y.affineCover.add iY) .none h H

中文:
引理 of_isPullback
  结论: {UX UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY]
  证明: MorphismProperty.IsLocalAtTarget.of_isPullback (Y.affineCover.add iY) .none h H

Depends on / 依赖: IsLocalAtTarget, MorphismProperty, MorphismProperty.IsLocalAtTarget.of_isPullback, Y.affineCover.add, affineCover, of_isPullback
-/
lemma of_isPullback {UX UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (H : P f) : P f' :=
  MorphismProperty.IsLocalAtTarget.of_isPullback (Y.affineCover.add iY) .none h H

/--
theorem `restrict` / 定理 `restrict`

English:
theorem restrict
  given: (hf : P f) (U : Y.Opens)
  statement: P (f ∣_ U)
  proof: of_isPullback (isPullback_morphismRestrict f U).flip hf

中文:
定理 restrict
  条件: (hf : P f) (U : Y.Opens)
  结论: P (f ∣_ U)
  证明: of_isPullback (isPullback_morphismRestrict f U).flip hf

Depends on / 依赖: isPullback_morphismRestrict, of_isPullback
-/
theorem restrict (hf : P f) (U : Y.Opens) : P (f ∣_ U) :=
  of_isPullback (isPullback_morphismRestrict f U).flip hf

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `of_iSup_eq_top` / 引理 `of_iSup_eq_top`

English:
lemma of_iSup_eq_top
  statement: {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤)
  proof: by
  refine (P.iff_of_zeroHypercover_target
    (Y.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i => ?_
  obtain ⟨_, i, rfl⟩ := i
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mp ?_
  change P (f ∣_ (U i).ι.opensRange)
  rw [Scheme.Opens.open

中文:
引理 of_iSup_eq_top
  结论: {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤)
  证明: by
  refine (P.iff_of_zeroHypercover_target
    (Y.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i => ?_
  obtain ⟨_, i, rfl⟩ := i
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mp ?_
  change P (f ∣_ (U i).ι.opensRange)
  rw [Scheme.Opens.open

Depends on / 依赖: P.arrow_mk_iso_iff, P.iff_of_zeroHypercover_target, Scheme, Scheme.Opens.opensRange_, Set.range, Subtype, Subtype.val, Y.openCoverOfIsOpenCover, arrow_mk_iso_iff, iff_of_zeroHypercover_target, morphismRestrictOpensRange, openCoverOfIsOpenCover, opensRange
-/
lemma of_iSup_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤)
    (H : forall i, P (f ∣_ U i)) : P f := by
  refine (P.iff_of_zeroHypercover_target
    (Y.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i => ?_
  obtain ⟨_, i, rfl⟩ := i
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mp ?_
  change P (f ∣_ (U i).ι.opensRange)
  rw [Scheme.Opens.opensRange_ι]
  exact H i

/--
theorem `iff_of_iSup_eq_top` / 定理 `iff_of_iSup_eq_top`

English:
theorem iff_of_iSup_eq_top
  given: {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤)
  proof: ⟨fun H _ => restrict H _, of_iSup_eq_top U hU⟩

中文:
定理 iff_of_iSup_eq_top
  条件: {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤)
  证明: ⟨fun H _ => restrict H _, of_iSup_eq_top U hU⟩

Depends on / 依赖: of_iSup_eq_top, restrict
-/
theorem iff_of_iSup_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) :
    P f ↔ forall i, P (f ∣_ U i) :=
  ⟨fun H _ => restrict H _, of_iSup_eq_top U hU⟩

/--
lemma `of_openCover` / 引理 `of_openCover`

English:
lemma of_openCover
  given: (H : forall i, P (𝒰.pullbackHom f i))
  statement: P f
  proof: by
  apply of_iSup_eq_top (fun i => (𝒰.f i).opensRange) 𝒰.iSup_opensRange
  exact fun i => (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (H i)

中文:
引理 of_openCover
  条件: (H : 对任意 i, P (𝒰.pullbackHom f i))
  结论: P f
  证明: by
  apply of_iSup_eq_top (fun i => (𝒰.f i).opensRange) 𝒰.iSup_opensRange
  exact fun i => (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (H i)

Depends on / 依赖: P.arrow_mk_iso_iff, arrow_mk_iso_iff, iSup_opensRange, morphismRestrictOpensRange, of_iSup_eq_top, opensRange
-/
lemma of_openCover (H : forall i, P (𝒰.pullbackHom f i)) : P f := by
  apply of_iSup_eq_top (fun i => (𝒰.f i).opensRange) 𝒰.iSup_opensRange
  exact fun i => (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (H i)

/--
theorem `iff_of_openCover` / 定理 `iff_of_openCover`

English:
theorem iff_of_openCover
  given: (𝒰 : Y.OpenCover)
  proof: ⟨fun H _ => of_isPullback (.of_hasPullback _ _) H, of_openCover _⟩

中文:
定理 iff_of_openCover
  条件: (𝒰 : Y.OpenCover)
  证明: ⟨fun H _ => of_isPullback (.of_hasPullback _ _) H, of_openCover _⟩

Depends on / 依赖: of_hasPullback, of_isPullback, of_openCover
-/
theorem iff_of_openCover (𝒰 : Y.OpenCover) :
    P f ↔ forall i, P (𝒰.pullbackHom f i) :=
  ⟨fun H _ => of_isPullback (.of_hasPullback _ _) H, of_openCover _⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `of_range_subset_iSup` / 引理 `of_range_subset_iSup`

English:
lemma of_range_subset_iSup
  statement: [P.RespectsRight @IsOpenImmersion] {ι : Type*} (U : ι -> Y.Opens)
  proof: by
  let g : X ⟶ (⨆ i, U i : Y.Opens) := IsOpenImmersion.lift (Scheme.Opens.ι _) f (by simpa using H)
  rw [← IsOpenImmersion.lift_fac (⨆ i]; rw [U i).ι f (by simpa using H)]
  apply MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) _ inferInstance
  rw [iff_of_iSup_eq_top (P := P) (U 

中文:
引理 of_range_subset_iSup
  结论: [P.RespectsRight @IsOpenImmersion] {ι : 类型} (U : ι -> Y.Opens)
  证明: by
  let g : X ⟶ (⨆ i, U i : Y.Opens) := IsOpenImmersion.lift (Scheme.Opens.ι _) f (by simpa using H)
  rw [← IsOpenImmersion.lift_fac (⨆ i]; rw [U i).ι f (by simpa using H)]
  apply MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) _ inferInstance
  rw [iff_of_iSup_eq_top (P := P) (U 

Depends on / 依赖: Arrow.mk, IsOpenImmersion, IsOpenImmersion.lift, IsOpenImmersion.lift_fac, MorphismProperty, MorphismProperty.RespectsRight.postcomp, RespectsRight, Scheme, Scheme.Opens, Y.Opens, iff_of_iSup_eq_top, lift_fac, postcomp
-/
lemma of_range_subset_iSup [P.RespectsRight @IsOpenImmersion] {ι : Type*} (U : ι -> Y.Opens)
    (H : Set.range f subseteq (⨆ i, U i : Y.Opens)) (hf : forall i, P (f ∣_ U i)) : P f := by
  let g : X ⟶ (⨆ i, U i : Y.Opens) := IsOpenImmersion.lift (Scheme.Opens.ι _) f (by simpa using H)
  rw [← IsOpenImmersion.lift_fac (⨆ i]; rw [U i).ι f (by simpa using H)]
  apply MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) _ inferInstance
  rw [iff_of_iSup_eq_top (P := P) (U := fun i : ι => (⨆ i]; rw [U i).ι ⁻¹ᵁ U i)]
  · intro i
    have heq : g ⁻¹ᵁ (⨆ i, U i).ι ⁻¹ᵁ U i = f ⁻¹ᵁ U i := by
      change (g ≫ (⨆ i, U i).ι) ⁻¹ᵁ U i = _
      simp [g]
    let e : Arrow.mk (g ∣_ (⨆ i, U i).ι ⁻¹ᵁ U i) ≅ Arrow.mk (f ∣_ U i) :=
Arrow.isoMk (X.isoOfEq heq) (Scheme.Opens.isoOfLE (le_iSup U i)) by
      simp [← CategoryTheory.cancel_mono (U i).ι, g]
    rw [P.arrow_mk_iso_iff e]
    exact hf i
  apply (⨆ i, U i).ι.image_injective
  dsimp
  rw [Scheme.Hom.image_iSup]; rw [Scheme.Hom.image_top_eq_opensRange]; rw [Scheme.Opens.opensRange_ι]
  simp [Scheme.Hom.image_preimage_eq_opensRange_inf, le_iSup U]

/--
lemma `of_forall_exists_morphismRestrict` / 引理 `of_forall_exists_morphismRestrict`

English:
lemma of_forall_exists_morphismRestrict
  given: (H : forall x, exists U : Y.Opens, x in U ∧ P (f ∣_ U))
  statement: P f
  proof: by
  choose U hxU hU using H
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U (top_le_iff.mp fun x _ => ?_) hU
  simpa using ⟨x, hxU x⟩

中文:
引理 of_forall_exists_morphismRestrict
  条件: (H : 对任意 x, 存在 U : Y.Opens, x in U ∧ P (f ∣_ U))
  结论: P f
  证明: by
  choose U hxU hU using H
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U (top_le_iff.mp fun x _ => ?_) hU
  simpa using ⟨x, hxU x⟩

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.of_iSup_eq_top, coprodIsCoprod, finite_of_isColimit, infer_instance, of_iSup_eq_top, top_le_iff, top_le_iff.mp
-/
lemma of_forall_exists_morphismRestrict (H : forall x, exists U : Y.Opens, x in U ∧ P (f ∣_ U)) : P f := by
  choose U hxU hU using H
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U (top_le_iff.mp fun x _ => ?_) hU
  simpa using ⟨x, hxU x⟩

/--
lemma `of_forall_source_exists_preimage` / 引理 `of_forall_source_exists_preimage`

English:
lemma of_forall_source_exists_preimage
  proof: by
  choose U h₁ h₂ using hX
  apply IsZariskiLocalAtTarget.of_range_subset_iSup U
  · rintro y ⟨x, rfl⟩
    simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨x, h₁ x⟩
  · intro x
    exact P.of_postcomp (f ∣_ U x) (U x).ι (inferInstance : IsOpenImmersion _) (by simp [h₂])

中文:
引理 of_forall_source_exists_preimage
  证明: by
  choose U h₁ h₂ using hX
  apply IsZariskiLocalAtTarget.of_range_subset_iSup U
  · rintro y ⟨x, rfl⟩
    simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨x, h₁ x⟩
  · intro x
    exact P.of_postcomp (f ∣_ U x) (U x).ι (inferInstance : IsOpenImmersion _) (by simp [h₂])

Depends on / 依赖: Discrete, Discrete.equivalence, Finite, Finite.exists_equiv_fin, HasColimitsOfShape, IsOpenImmersion, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.of_range_subset_iSup, Opens.coe_iSup, P.of_postcomp, Set.mem_iUnion, SetLike, SetLike.mem_coe, coe_iSup, coproductIsCoproduct, e.symm, equivalence, exists_equiv_fin, finite_of_isColimit, hasColimitsOfShape_of_equivalence
-/
lemma of_forall_source_exists_preimage
    [P.RespectsRight IsOpenImmersion] [P.HasOfPostcompProperty IsOpenImmersion]
    (f : X ⟶ Y) (hX : forall x, exists (U : Y.Opens), f x in U ∧ P ((f ⁻¹ᵁ U).ι ≫ f)) :
    P f := by
  choose U h₁ h₂ using hX
  apply IsZariskiLocalAtTarget.of_range_subset_iSup U
  · rintro y ⟨x, rfl⟩
    simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨x, h₁ x⟩
  · intro x
    exact P.of_postcomp (f ∣_ U x) (U x).ι (inferInstance : IsOpenImmersion _) (by simp [h₂])

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coprodMap` / 引理 `coprodMap`

English:
lemma coprodMap
  given: {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (hf : P f) (hg : P g)
  proof: by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{_, 0} _ _) ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · rw [← MorphismProperty.cancel_left_of_respectsIso P
      (isPullback_inl_inl_coprodMap f g).flip.isoPullback.hom]
    convert! hf
    simp [Scheme.Cover.pullbackHom, coprodOpenCover]
  · rw [←

中文:
引理 coprodMap
  条件: {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (hf : P f) (hg : P g)
  证明: by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{_, 0} _ _) ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · rw [← MorphismProperty.cancel_left_of_respectsIso P
      (isPullback_inl_inl_coprodMap f g).flip.isoPullback.hom]
    convert! hf
    simp [Scheme.Cover.pullbackHom, coprodOpenCover]
  · rw [←

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.of_openCover, MorphismProperty, MorphismProperty.cancel_left_of_respectsIso, Scheme, Scheme.Cover.pullbackHom, cancel_left_of_respectsIso, convert, coprodOpenCover, flip.isoPullback.hom, isPullback_inl_inl_coprodMap, isPullback_inr_inr_coprodMap, isoPullback, of_openCover, pullbackHom
-/
lemma coprodMap {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (hf : P f) (hg : P g) :
    P (coprod.map f g) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{_, 0} _ _) ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · rw [← MorphismProperty.cancel_left_of_respectsIso P
      (isPullback_inl_inl_coprodMap f g).flip.isoPullback.hom]
    convert! hf
    simp [Scheme.Cover.pullbackHom, coprodOpenCover]
  · rw [← MorphismProperty.cancel_left_of_respectsIso P
      (isPullback_inr_inr_coprodMap f g).flip.isoPullback.hom]
    convert! hg
    simp [Scheme.Cover.pullbackHom, coprodOpenCover]

end IsZariskiLocalAtTarget

/--
Definition of `IsZariskiLocalAtSource` / `IsZariskiLocalAtSource` 的定义

English:
abbreviation IsZariskiLocalAtSource
  signature: (P : MorphismProperty Scheme.{u})
  body: P.IsLocalAtSource Scheme.zariskiPrecoverage

中文:
缩写 IsZariskiLocalAtSource
  签名: (P : Morphism命题erty Scheme.{u})
  定义体: P.IsLocalAtSource Scheme.zariskiPrecoverage

Depends on / 依赖: IsLocalAtSource, P.IsLocalAtSource, Scheme, Scheme.zariskiPrecoverage, zariskiPrecoverage
-/
abbrev IsZariskiLocalAtSource (P : MorphismProperty Scheme.{u}) :=
  P.IsLocalAtSource Scheme.zariskiPrecoverage

namespace IsZariskiLocalAtSource

set_option backward.defeqAttrib.useBackward true in
/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  statement: {P : MorphismProperty Scheme} [P.RespectsIso]
  proof: by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 => ⟨fun hf i => ?_, fun hf => ?_⟩
  · rw [← IsOpenImmersion.isoOfRangeEq_hom_fac (𝒰.f i) (Scheme.Opens.ι _)
      (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm), Category.assoc,
      P.cancel_left_of_respectsIso]
    exact restr

中文:
引理 mk'
  结论: {P : Morphism命题erty Scheme} [P.RespectsIso]
  证明: by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 => ⟨fun hf i => ?_, fun hf => ?_⟩
  · rw [← IsOpenImmersion.isoOfRangeEq_hom_fac (𝒰.f i) (Scheme.Opens.ι _)
      (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm), Category.assoc,
      P.cancel_left_of_respectsIso]
    exact restr
-/
protected lemma mk' {P : MorphismProperty Scheme} [P.RespectsIso]
    (restrict : forall {X Y : Scheme} (f : X ⟶ Y) (U : X.Opens), P f -> P (U.ι ≫ f))
    (of_sSup_eq_top :
      forall {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι -> X.Opens), iSup U = ⊤ ->
        (forall i, P ((U i).ι ≫ f)) -> P f) :
    IsZariskiLocalAtSource P := by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 => ⟨fun hf i => ?_, fun hf => ?_⟩
  · rw [← IsOpenImmersion.isoOfRangeEq_hom_fac (𝒰.f i) (Scheme.Opens.ι _)
      (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm), Category.assoc,
      P.cancel_left_of_respectsIso]
    exact restrict _ _ hf
  · refine of_sSup_eq_top f _ (Scheme.OpenCover.iSup_opensRange <| .ulift 𝒰) fun i => ?_
    dsimp
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝒰.f _) (Scheme.Opens.ι _)
      (congr_arg Opens.carrier (𝒰.f _).opensRange.opensRange_ι.symm)]; rw [Category.assoc]; rw [P.cancel_left_of_respectsIso]
    exact hf _

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (𝒰 : X.OpenCover)

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  given: {UX : Scheme.{u}} (H : P f) (i : UX ⟶ X) [IsOpenImmersion i]
  proof: (P.iff_of_zeroHypercover_source (X.affineCover.add i)).mp H .none

中文:
引理 comp
  条件: {UX : Scheme.{u}} (H : P f) (i : UX ⟶ X) [IsOpenImmersion i]
  证明: (P.iff_of_zeroHypercover_source (X.affineCover.add i)).mp H .none

Depends on / 依赖: P.iff_of_zeroHypercover_source, X.affineCover.add, affineCover, iff_of_zeroHypercover_source
-/
lemma comp {UX : Scheme.{u}} (H : P f) (i : UX ⟶ X) [IsOpenImmersion i] :
    P (i ≫ f) :=
  (P.iff_of_zeroHypercover_source (X.affineCover.add i)).mp H .none

/--
Instance `respectsLeft_isOpenImmersion` / 实例 `respectsLeft_isOpenImmersion`

English:
instance respectsLeft_isOpenImmersion
  signature: {P : MorphismProperty Scheme}
  body: IsZariskiLocalAtSource.comp hf i

中文:
实例 respectsLeft_isOpenImmersion
  签名: {P : Morphism命题erty Scheme}
  定义体: IsZariskiLocalAtSource.comp hf i

Depends on / 依赖: IsZariskiLocalAtSource, IsZariskiLocalAtSource.comp
-/
instance respectsLeft_isOpenImmersion {P : MorphismProperty Scheme}
    [IsZariskiLocalAtSource P] : P.RespectsLeft @IsOpenImmersion where
  precomp i _ _ hf := IsZariskiLocalAtSource.comp hf i

/--
lemma `of_iSup_eq_top` / 引理 `of_iSup_eq_top`

English:
lemma of_iSup_eq_top
  statement: {ι} (U : ι -> X.Opens) (hU : iSup U = ⊤)
  proof: by
  refine (P.iff_of_zeroHypercover_source
    (X.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i => ?_
  obtain ⟨_, i, rfl⟩ := i
  exact H i

中文:
引理 of_iSup_eq_top
  结论: {ι} (U : ι -> X.Opens) (hU : iSup U = ⊤)
  证明: by
  refine (P.iff_of_zeroHypercover_source
    (X.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i => ?_
  obtain ⟨_, i, rfl⟩ := i
  exact H i

Depends on / 依赖: P.iff_of_zeroHypercover_source, Set.range, Subtype, Subtype.val, X.openCoverOfIsOpenCover, hasDimensionLT_prod, iff_of_zeroHypercover_source, openCoverOfIsOpenCover
-/
lemma of_iSup_eq_top {ι} (U : ι -> X.Opens) (hU : iSup U = ⊤)
    (H : forall i, P ((U i).ι ≫ f)) : P f := by
  refine (P.iff_of_zeroHypercover_source
    (X.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i => ?_
  obtain ⟨_, i, rfl⟩ := i
  exact H i

/--
theorem `iff_of_iSup_eq_top` / 定理 `iff_of_iSup_eq_top`

English:
theorem iff_of_iSup_eq_top
  given: {ι} (U : ι -> X.Opens) (hU : iSup U = ⊤)
  proof: ⟨fun H _ => comp H _, of_iSup_eq_top U hU⟩

中文:
定理 iff_of_iSup_eq_top
  条件: {ι} (U : ι -> X.Opens) (hU : iSup U = ⊤)
  证明: ⟨fun H _ => comp H _, of_iSup_eq_top U hU⟩

Depends on / 依赖: hasDimensionLE_prod, of_iSup_eq_top
-/
theorem iff_of_iSup_eq_top {ι} (U : ι -> X.Opens) (hU : iSup U = ⊤) :
    P f ↔ forall i, P ((U i).ι ≫ f) :=
  ⟨fun H _ => comp H _, of_iSup_eq_top U hU⟩

/--
lemma `of_openCover` / 引理 `of_openCover`

English:
lemma of_openCover
  given: (H : forall i, P (𝒰.f i ≫ f))
  statement: P f
  proof: by
  refine of_iSup_eq_top (fun i => (𝒰.f i).opensRange) 𝒰.iSup_opensRange fun i => ?_
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝒰.f i) (Scheme.Opens.ι _)
    (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm)]; rw [Category.assoc]; rw [P.cancel_left_of_respectsIso]
  exact H i

中文:
引理 of_openCover
  条件: (H : 对任意 i, P (𝒰.f i ≫ f))
  结论: P f
  证明: by
  refine of_iSup_eq_top (fun i => (𝒰.f i).opensRange) 𝒰.iSup_opensRange fun i => ?_
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝒰.f i) (Scheme.Opens.ι _)
    (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm)]; rw [Category.assoc]; rw [P.cancel_left_of_respectsIso]
  exact H i

Depends on / 依赖: Category, Category.assoc, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq_inv_fac, Opens.carrier, P.cancel_left_of_respectsIso, Scheme, Scheme.Opens, cancel_left_of_respectsIso, carrier, congr_arg, iSup_opensRange, isoOfRangeEq_inv_fac, of_iSup_eq_top, opensRange, opensRange.opensRange_
-/
lemma of_openCover (H : forall i, P (𝒰.f i ≫ f)) : P f := by
  refine of_iSup_eq_top (fun i => (𝒰.f i).opensRange) 𝒰.iSup_opensRange fun i => ?_
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝒰.f i) (Scheme.Opens.ι _)
    (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm)]; rw [Category.assoc]; rw [P.cancel_left_of_respectsIso]
  exact H i

/--
theorem `iff_of_openCover` / 定理 `iff_of_openCover`

English:
theorem iff_of_openCover
  proof: ⟨fun H _ => comp H _, of_openCover _⟩

中文:
定理 iff_of_openCover
  证明: ⟨fun H _ => comp H _, of_openCover _⟩

Depends on / 依赖: of_openCover
-/
theorem iff_of_openCover :
    P f ↔ forall i, P (𝒰.f i ≫ f) :=
  ⟨fun H _ => comp H _, of_openCover _⟩

variable (f) in
/--
lemma `of_isOpenImmersion` / 引理 `of_isOpenImmersion`

English:
lemma of_isOpenImmersion
  given: [P.ContainsIdentities] [IsOpenImmersion f]
  statement: P f
  proof: Category.comp_id f ▸ comp (P.id_mem Y) f

中文:
引理 of_isOpenImmersion
  条件: [P.ContainsIdentities] [IsOpenImmersion f]
  结论: P f
  证明: Category.comp_id f ▸ comp (P.id_mem Y) f

Depends on / 依赖: Category, Category.comp_id, P.id_mem, comp_id, id_mem
-/
lemma of_isOpenImmersion [P.ContainsIdentities] [IsOpenImmersion f] : P f :=
  Category.comp_id f ▸ comp (P.id_mem Y) f

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isZariskiLocalAtTarget` / 引理 `isZariskiLocalAtTarget`

English:
lemma isZariskiLocalAtTarget
  statement: [P.IsMultiplicative]
  proof: by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 => ⟨fun hf i => ?_, fun h => ?_⟩
  · apply hP _ (𝒰.f i)
    rw [← pullback.condition]
    exact IsZariskiLocalAtSource.comp hf _
  · rw [P.iff_of_zeroHypercover_source (𝒰.pullback₁ f)]
    intro i
    rw [← Scheme.Cover.pullbackHom_map]
    exac

中文:
引理 isZariskiLocalAtTarget
  结论: [P.IsMultiplicative]
  证明: by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 => ⟨fun hf i => ?_, fun h => ?_⟩
  · apply hP _ (𝒰.f i)
    rw [← pullback.condition]
    exact IsZariskiLocalAtSource.comp hf _
  · rw [P.iff_of_zeroHypercover_source (𝒰.pullback₁ f)]
    intro i
    rw [← Scheme.Cover.pullbackHom_map]
    exac

Depends on / 依赖: IsZariskiLocalAtSource, IsZariskiLocalAtSource.comp, P.comp_mem, P.iff_of_zeroHypercover_source, Scheme, Scheme.Cover.pullbackHom_map, comp_mem, condition, iff_of_zeroHypercover_source, mk_of_iff_of_zeroHypercover, of_isOpenImmersion, pullback, pullback.condition, pullbackHom_map
-/
lemma isZariskiLocalAtTarget [P.IsMultiplicative]
    (hP : forall {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g], P (f ≫ g) -> P f) :
    IsZariskiLocalAtTarget P := by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 => ⟨fun hf i => ?_, fun h => ?_⟩
  · apply hP _ (𝒰.f i)
    rw [← pullback.condition]
    exact IsZariskiLocalAtSource.comp hf _
  · rw [P.iff_of_zeroHypercover_source (𝒰.pullback₁ f)]
    intro i
    rw [← Scheme.Cover.pullbackHom_map]
    exact P.comp_mem _ _ (h i) (of_isOpenImmersion _)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `sigmaDesc` / 引理 `sigmaDesc`

English:
lemma sigmaDesc
  statement: {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] {Y : ι -> Scheme.{u}}
  proof: by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (Scheme.IsLocallyDirected.openCover _)]
  exact fun i => by simp [hf]

中文:
引理 sigmaDesc
  结论: {X : Scheme.{u}} {ι : 类型v} [Small.{u} ι] {Y : ι -> Scheme.{u}}
  证明: by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (Scheme.IsLocallyDirected.openCover _)]
  exact fun i => by simp [hf]

Depends on / 依赖: IsLocallyDirected, IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff_of_openCover, Scheme, Scheme.IsLocallyDirected.openCover, iff_of_openCover, openCover
-/
lemma sigmaDesc {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] {Y : ι -> Scheme.{u}}
    {f : forall i, Y i ⟶ X} (hf : forall i, P (f i)) : P (Sigma.desc f) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (Scheme.IsLocallyDirected.openCover _)]
  exact fun i => by simp [hf]

section IsZariskiLocalAtSourceAndTarget

/--
lemma `resLE` / 引理 `resLE`

English:
lemma resLE
  statement: [IsZariskiLocalAtTarget P] {U : Y.Opens} {V : X.Opens}
  proof: IsZariskiLocalAtSource.comp (IsZariskiLocalAtTarget.restrict hf U) _

中文:
引理 resLE
  结论: [IsZariskiLocalAtTarget P] {U : Y.Opens} {V : X.Opens}
  证明: IsZariskiLocalAtSource.comp (IsZariskiLocalAtTarget.restrict hf U) _

Depends on / 依赖: IsZariskiLocalAtSource, IsZariskiLocalAtSource.comp, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, restrict
-/
lemma resLE [IsZariskiLocalAtTarget P] {U : Y.Opens} {V : X.Opens}
    (e : V <= f ⁻¹ᵁ U)
    (hf : P f) : P (f.resLE U V e) :=
  IsZariskiLocalAtSource.comp (IsZariskiLocalAtTarget.restrict hf U) _

/--
lemma `iff_exists_resLE` / 引理 `iff_exists_resLE`

English:
lemma iff_exists_resLE
  statement: [IsZariskiLocalAtTarget P]
  proof: by
  refine ⟨fun hf x => ⟨⊤, ⊤, trivial, by simp, resLE _ hf⟩, fun hf => ?_⟩
  choose U V hxU e hf using hf
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun x : X => V x) (P := P)]
  · intro x
    rw [← Scheme.Hom.resLE_comp_ι _ (e x)]
    exact MorphismProperty.RespectsRight.postcomp (Q := @IsO

中文:
引理 iff_exists_resLE
  结论: [IsZariskiLocalAtTarget P]
  证明: by
  refine ⟨fun hf x => ⟨⊤, ⊤, trivial, by simp, resLE _ hf⟩, fun hf => ?_⟩
  choose U V hxU e hf using hf
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun x : X => V x) (P := P)]
  · intro x
    rw [← Scheme.Hom.resLE_comp_ι _ (e x)]
    exact MorphismProperty.RespectsRight.postcomp (Q := @IsO

Depends on / 依赖: IsOpenImmersion, IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff_of_iSup_eq_top, MorphismProperty, MorphismProperty.RespectsRight.postcomp, Opens.mem_iSup, RespectsRight, Scheme, Scheme.Hom.resLE_comp_, eq_top_iff, iff_of_iSup_eq_top, mem_iSup, postcomp
-/
lemma iff_exists_resLE [IsZariskiLocalAtTarget P]
    [P.RespectsRight @IsOpenImmersion] :
    P f ↔ forall x : X, exists (U : Y.Opens) (V : X.Opens) (_ : x in V.1) (e : V <= f ⁻¹ᵁ U),
      P (f.resLE U V e) := by
  refine ⟨fun hf x => ⟨⊤, ⊤, trivial, by simp, resLE _ hf⟩, fun hf => ?_⟩
  choose U V hxU e hf using hf
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun x : X => V x) (P := P)]
  · intro x
    rw [← Scheme.Hom.resLE_comp_ι _ (e x)]
    exact MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) _ inferInstance _ (hf x)
  · rw [eq_top_iff]
    rintro x -
    simp only [Opens.mem_iSup]
    use x, hxU x

end IsZariskiLocalAtSourceAndTarget

end IsZariskiLocalAtSource

/--
Definition of `AffineTargetMorphismProperty` / `AffineTargetMorphismProperty` 的定义

English:
definition AffineTargetMorphismProperty
  body: forall ⦃X Y : Scheme⦄ (_ : X ⟶ Y) [IsAffine Y], Prop

中文:
定义 AffineTargetMorphismProperty
  定义体: forall ⦃X Y : Scheme⦄ (_ : X ⟶ Y) [IsAffine Y], Prop

Depends on / 依赖: IsAffine, Scheme
-/
def AffineTargetMorphismProperty :=
  forall ⦃X Y : Scheme⦄ (_ : X ⟶ Y) [IsAffine Y], Prop

namespace AffineTargetMorphismProperty

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {P Q : AffineTargetMorphismProperty}
  proof: by
  delta AffineTargetMorphismProperty; ext; exact H _

中文:
引理 ext
  结论: {P Q : AffineTargetMorphism命题erty}
  证明: by
  delta AffineTargetMorphismProperty; ext; exact H _

Depends on / 依赖: AffineTargetMorphismProperty
-/
lemma ext {P Q : AffineTargetMorphismProperty}
    (H : forall ⦃X Y : Scheme⦄ (f : X ⟶ Y) [IsAffine Y], P f ↔ Q f) : P = Q := by
  delta AffineTargetMorphismProperty; ext; exact H _

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (P : MorphismProperty Scheme)
  body: fun _ _ f _ => P f

中文:
定义 of
  签名: (P : Morphism命题erty Scheme)
  定义体: fun _ _ f _ => P f
-/
def of (P : MorphismProperty Scheme) : AffineTargetMorphismProperty :=
  fun _ _ f _ => P f

/--
Definition of `toProperty` / `toProperty` 的定义

English:
definition toProperty
  signature: (P : AffineTargetMorphismProperty)
  body: fun _ _ f => exists h, @P _ _ f h

中文:
定义 toProperty
  签名: (P : AffineTargetMorphism命题erty)
  定义体: fun _ _ f => exists h, @P _ _ f h
-/
def toProperty (P : AffineTargetMorphismProperty) :
    MorphismProperty Scheme := fun _ _ f => exists h, @P _ _ f h

/--
theorem `toProperty_apply` / 定理 `toProperty_apply`

English:
theorem toProperty_apply
  statement: (P : AffineTargetMorphismProperty)
  proof: by
  delta AffineTargetMorphismProperty.toProperty; simp [*]

中文:
定理 toProperty_apply
  结论: (P : AffineTargetMorphism命题erty)
  证明: by
  delta AffineTargetMorphismProperty.toProperty; simp [*]

Depends on / 依赖: AffineTargetMorphismProperty, AffineTargetMorphismProperty.toProperty, toProperty
-/
theorem toProperty_apply (P : AffineTargetMorphismProperty)
    {X Y : Scheme} (f : X ⟶ Y) [i : IsAffine Y] : P.toProperty f ↔ P f := by
  delta AffineTargetMorphismProperty.toProperty; simp [*]

/--
theorem `cancel_left_of_respectsIso` / 定理 `cancel_left_of_respectsIso`

English:
theorem cancel_left_of_respectsIso
  proof: by
  rw [← P.toProperty_apply]; rw [← P.toProperty_apply]; rw [P.toProperty.cancel_left_of_respectsIso]

中文:
定理 cancel_left_of_respectsIso
  证明: by
  rw [← P.toProperty_apply]; rw [← P.toProperty_apply]; rw [P.toProperty.cancel_left_of_respectsIso]

Depends on / 依赖: P.toProperty.cancel_left_of_respectsIso, P.toProperty_apply, cancel_left_of_respectsIso, toProperty, toProperty_apply
-/
theorem cancel_left_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsAffine Z] : P (f ≫ g) ↔ P g := by
  rw [← P.toProperty_apply]; rw [← P.toProperty_apply]; rw [P.toProperty.cancel_left_of_respectsIso]

/--
theorem `cancel_right_of_respectsIso` / 定理 `cancel_right_of_respectsIso`

English:
theorem cancel_right_of_respectsIso
  proof: by rw [← P.toProperty_apply, ← P.toProperty_apply,
      P.toProperty.cancel_right_of_respectsIso]

中文:
定理 cancel_right_of_respectsIso
  证明: by rw [← P.toProperty_apply, ← P.toProperty_apply,
      P.toProperty.cancel_right_of_respectsIso]

Depends on / 依赖: P.toProperty.cancel_right_of_respectsIso, P.toProperty_apply, Unique, cancel_right_of_respectsIso, toProperty, toProperty_apply
-/
theorem cancel_right_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] [IsAffine Z] [IsAffine Y] :
    P (f ≫ g) ↔ P f := by rw [← P.toProperty_apply, ← P.toProperty_apply,
      P.toProperty.cancel_right_of_respectsIso]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `arrow_mk_iso_iff` / 定理 `arrow_mk_iso_iff`

English:
theorem arrow_mk_iso_iff
  proof: .of_isIso (Y := Y) e.inv.right
    P f ↔ P f' := by
  rw [← P.toProperty_apply]; rw [← P.toProperty_apply]; rw [P.toProperty.arrow_mk_iso_iff e]

中文:
定理 arrow_mk_iso_iff
  证明: .of_isIso (Y := Y) e.inv.right
    P f ↔ P f' := by
  rw [← P.toProperty_apply]; rw [← P.toProperty_apply]; rw [P.toProperty.arrow_mk_iso_iff e]

Depends on / 依赖: e.inv.right, of_isIso
-/
theorem arrow_mk_iso_iff
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk f') {h : IsAffine Y} :
    letI : IsAffine Y' := .of_isIso (Y := Y) e.inv.right
    P f ↔ P f' := by
  rw [← P.toProperty_apply]; rw [← P.toProperty_apply]; rw [P.toProperty.arrow_mk_iso_iff e]

/--
theorem `respectsIso_mk` / 定理 `respectsIso_mk`

English:
theorem respectsIso_mk
  statement: {P : AffineTargetMorphismProperty}
  proof: by
  apply MorphismProperty.RespectsIso.mk
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨a, h₁ e f h⟩
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨.of_isIso e.inv, h₂ e f h⟩

中文:
定理 respectsIso_mk
  结论: {P : AffineTargetMorphism命题erty}
  证明: by
  apply MorphismProperty.RespectsIso.mk
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨a, h₁ e f h⟩
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨.of_isIso e.inv, h₂ e f h⟩

Depends on / 依赖: MorphismProperty, MorphismProperty.RespectsIso.mk, RespectsIso, e.inv, of_isIso
-/
theorem respectsIso_mk {P : AffineTargetMorphismProperty}
    (h₁ : forall {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z) [IsAffine Z], P f -> P (e.hom ≫ f))
    (h₂ : forall {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y) [IsAffine Y],
      P f -> @P _ _ (f ≫ e.hom) (.of_isIso e.inv)) :
    P.toProperty.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨a, h₁ e f h⟩
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨.of_isIso e.inv, h₂ e f h⟩

/--
Instance `respectsIso_of` / 实例 `respectsIso_of`

English:
instance respectsIso_of
  body: by
  apply respectsIso_mk
  · intro _ _ _ _ _ _; apply MorphismProperty.RespectsIso.precomp
  · intro _ _ _ _ _ _; apply MorphismProperty.RespectsIso.postcomp

中文:
实例 respectsIso_of
  定义体: by
  apply respectsIso_mk
  · intro _ _ _ _ _ _; apply MorphismProperty.RespectsIso.precomp
  · intro _ _ _ _ _ _; apply MorphismProperty.RespectsIso.postcomp

Depends on / 依赖: MorphismProperty, MorphismProperty.RespectsIso.postcomp, MorphismProperty.RespectsIso.precomp, RespectsIso, postcomp, precomp, respectsIso_mk
-/
instance respectsIso_of
    (P : MorphismProperty Scheme) [P.RespectsIso] :
    (of P).toProperty.RespectsIso := by
  apply respectsIso_mk
  · intro _ _ _ _ _ _; apply MorphismProperty.RespectsIso.precomp
  · intro _ _ _ _ _ _; apply MorphismProperty.RespectsIso.postcomp

/--
Definition of `IsLocal` / `IsLocal` 的定义

English:
class IsLocal
  parameters: (P : AffineTargetMorphismProperty)
  axioms and operations (3):
    - respectsIso : P.toProperty.RespectsIso
    - to_basicOpen : forall {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (r : Γ(Y, ⊤)), P f -> P (f ∣_ Y.basicOpen r)
    - of_basicOpenCover : forall {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (s : Finset Γ(Y, ⊤)) (_ : Ideal.span (s : Set Γ(Y, ⊤)) = ⊤), (forall r : s, P (f ∣_ Y.basicOpen r.1)) -> P f

中文:
类 IsLocal
  参数: (P : AffineTargetMorphism命题erty)
  公理与运算 (3 个):
    - respectsIso : P.to命题erty.RespectsIso
    - to_basicOpen : 对任意 {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (r : Γ(Y, ⊤)), P f -> P (f ∣_ Y.basicOpen r)
    - of_basicOpenCover : 对任意 {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (s : Finset Γ(Y, ⊤)) (_ : Ideal.span (s : Set Γ(Y, ⊤)) = ⊤), (对任意 r : s, P (f ∣_ Y.basicOpen r.1)) -> P f
-/
class IsLocal (P : AffineTargetMorphismProperty) : Prop where
  /-- `P` as a morphism property respects isomorphisms -/
  respectsIso : P.toProperty.RespectsIso
  /-- `P` is stable under restriction to a basic open set of global sections. -/
  to_basicOpen :
    forall {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (r : Γ(Y, ⊤)), P f -> P (f ∣_ Y.basicOpen r)
  /-- `P` for `f` if `P` holds for `f` restricted to basic sets of a spanning set of the global
  sections -/
  of_basicOpenCover :
    forall {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (s : Finset Γ(Y, ⊤))
      (_ : Ideal.span (s : Set Γ(Y, ⊤)) = ⊤), (forall r : s, P (f ∣_ Y.basicOpen r.1)) -> P f

attribute [instance] AffineTargetMorphismProperty.IsLocal.respectsIso

open AffineTargetMorphismProperty in
instance (P : MorphismProperty Scheme) [IsZariskiLocalAtTarget P] :
    (of P).IsLocal where
  respectsIso := inferInstance
  to_basicOpen _ _ H := IsZariskiLocalAtTarget.restrict H _
  of_basicOpenCover {_ Y} _ _ _ hs := IsZariskiLocalAtTarget.of_iSup_eq_top _
    ((isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs)

/--
Definition of `IsStableUnderBaseChange` / `IsStableUnderBaseChange` 的定义

English:
definition IsStableUnderBaseChange
  signature: (P : AffineTargetMorphismProperty)
  body: forall ⦃Z X Y S : Scheme⦄ [IsAffine S] [IsAffine X] {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Z ⟶ Y} {g' : Z ⟶ X}, IsPullback g' f' f g -> P g -> P g'

中文:
定义 IsStableUnderBaseChange
  签名: (P : AffineTargetMorphism命题erty)
  定义体: forall ⦃Z X Y S : Scheme⦄ [IsAffine S] [IsAffine X] {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Z ⟶ Y} {g' : Z ⟶ X}, IsPullback g' f' f g -> P g -> P g'

Depends on / 依赖: IsAffine, IsPullback, Scheme
-/
def IsStableUnderBaseChange (P : AffineTargetMorphismProperty) : Prop :=
  forall ⦃Z X Y S : Scheme⦄ [IsAffine S] [IsAffine X] {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Z ⟶ Y} {g' : Z ⟶ X}, IsPullback g' f' f g -> P g -> P g'

/--
lemma `IsStableUnderBaseChange.mk` / 引理 `IsStableUnderBaseChange.mk`

English:
lemma IsStableUnderBaseChange.mk
  statement: (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
  proof: by
  intro Z X Y S _ _ f g f' g' h hg
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_fst]
  exact H f g hg

中文:
引理 IsStableUnderBaseChange.mk
  结论: (P : AffineTargetMorphism命题erty) [P.to命题erty.RespectsIso]
  证明: by
  intro Z X Y S _ _ f g f' g' h hg
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_fst]
  exact H f g hg

Depends on / 依赖: P.cancel_left_of_respectsIso, cancel_left_of_respectsIso, h.isoPullback.inv, h.isoPullback_inv_fst, isoPullback, isoPullback_inv_fst
-/
lemma IsStableUnderBaseChange.mk (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    (H : forall ⦃X Y S : Scheme⦄ [IsAffine S] [IsAffine X] (f : X ⟶ S) (g : Y ⟶ S),
      P g -> P (pullback.fst f g)) : P.IsStableUnderBaseChange := by
  intro Z X Y S _ _ f g f' g' h hg
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_fst]
  exact H f g hg

end AffineTargetMorphismProperty

section targetAffineLocally

/--
Definition of `targetAffineLocally` / `targetAffineLocally` 的定义

English:
definition targetAffineLocally
  signature: (P : AffineTargetMorphismProperty)
  body: fun {X Y : Scheme} (f : X ⟶ Y) => forall U : Y.affineOpens, P (f ∣_ U)

中文:
定义 targetAffineLocally
  签名: (P : AffineTargetMorphism命题erty)
  定义体: fun {X Y : Scheme} (f : X ⟶ Y) => forall U : Y.affineOpens, P (f ∣_ U)

Depends on / 依赖: Scheme, Y.affineOpens, affineOpens
-/
def targetAffineLocally (P : AffineTargetMorphismProperty) : MorphismProperty Scheme :=
  fun {X Y : Scheme} (f : X ⟶ Y) => forall U : Y.affineOpens, P (f ∣_ U)

/--
theorem `of_targetAffineLocally_of_isPullback` / 定理 `of_targetAffineLocally_of_isPullback`

English:
theorem of_targetAffineLocally_of_isPullback
  proof: by
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_snd]
  exact (P.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)).mp (hf ⟨_, isAffineOpen_opensRange iY⟩)

中文:
定理 of_targetAffineLocally_of_isPullback
  证明: by
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_snd]
  exact (P.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)).mp (hf ⟨_, isAffineOpen_opensRange iY⟩)

Depends on / 依赖: P.arrow_mk_iso_iff, P.cancel_left_of_respectsIso, arrow_mk_iso_iff, cancel_left_of_respectsIso, h.isoPullback.inv, h.isoPullback_inv_snd, isAffineOpen_opensRange, isoPullback, isoPullback_inv_snd, morphismRestrictOpensRange
-/
theorem of_targetAffineLocally_of_isPullback
    {P : AffineTargetMorphismProperty} [P.IsLocal]
    {X Y UX UY : Scheme.{u}} [IsAffine UY] {f : X ⟶ Y} {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (hf : targetAffineLocally P f) :
    P f' := by
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv]; rw [h.isoPullback_inv_snd]
  exact (P.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)).mp (hf ⟨_, isAffineOpen_opensRange iY⟩)

set_option backward.isDefEq.respectTransparency false in
instance (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso] :
    (targetAffineLocally P).RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · introv H U
    rw [morphismRestrict_comp]; rw [P.cancel_left_of_respectsIso]
    exact H U
  · introv H
    rintro ⟨U, hU : IsAffineOpen U⟩; dsimp
    have : IsAffine _ := hU.preimage_of_isIso e.hom
    rw [morphismRestrict_comp]; rw [P.cancel_right_of_respectsIso]
    exact H ⟨(Opens.map e.hom.base).obj U, hU.preimage_of_isIso e.hom⟩

/--
Definition of `HasAffineProperty` / `HasAffineProperty` 的定义

English:
class HasAffineProperty
  parameters: (P : MorphismProperty Scheme)
  axioms and operations (2):
    - isLocal_affineProperty : Q.IsLocal
    - eq_targetAffineLocally' : P = targetAffineLocally Q

中文:
类 HasAffineProperty
  参数: (P : Morphism命题erty Scheme)
  公理与运算 (2 个):
    - isLocal_affineProperty : Q.IsLocal
    - eq_targetAffineLocally' : P = targetAffineLocally Q
-/
class HasAffineProperty (P : MorphismProperty Scheme)
    (Q : outParam AffineTargetMorphismProperty) : Prop where
  isLocal_affineProperty : Q.IsLocal
  eq_targetAffineLocally' : P = targetAffineLocally Q

namespace HasAffineProperty

variable (P : MorphismProperty Scheme) {Q} [HasAffineProperty P Q]
variable {X Y : Scheme.{u}} {f : X ⟶ Y}

instance (Q : AffineTargetMorphismProperty) [Q.IsLocal] :
    HasAffineProperty (targetAffineLocally Q) Q :=
  ⟨inferInstance, rfl⟩

/--
lemma `eq_targetAffineLocally` / 引理 `eq_targetAffineLocally`

English:
lemma eq_targetAffineLocally
  statement: P = targetAffineLocally Q
  proof: eq_targetAffineLocally'

中文:
引理 eq_targetAffineLocally
  结论: P = targetAffineLocally Q
  证明: eq_targetAffineLocally'

Depends on / 依赖: eq_targetAffineLocally
-/
lemma eq_targetAffineLocally : P = targetAffineLocally Q := eq_targetAffineLocally'

/--
lemma `of_isZariskiLocalAtTarget` / 引理 `of_isZariskiLocalAtTarget`

English:
lemma of_isZariskiLocalAtTarget
  statement: (P : MorphismProperty Scheme.{u})
  proof: inferInstance
  eq_targetAffineLocally' := by
    ext X Y f
    constructor
    · intro hf ⟨U, hU⟩
      exact IsZariskiLocalAtTarget.restrict hf _
    · intro hf
      exact P.of_zeroHypercover_target Y.affineCover
        fun i => of_targetAffineLocally_of_isPullback (.of_hasPullback _ _) hf

中文:
引理 of_isZariskiLocalAtTarget
  结论: (P : Morphism命题erty Scheme.{u})
  证明: inferInstance
  eq_targetAffineLocally' := by
    ext X Y f
    constructor
    · intro hf ⟨U, hU⟩
      exact IsZariskiLocalAtTarget.restrict hf _
    · intro hf
      exact P.of_zeroHypercover_target Y.affineCover
        fun i => of_targetAffineLocally_of_isPullback (.of_hasPullback _ _) hf
-/
lemma of_isZariskiLocalAtTarget (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] :
    HasAffineProperty P (AffineTargetMorphismProperty.of P) where
  isLocal_affineProperty := inferInstance
  eq_targetAffineLocally' := by
    ext X Y f
    constructor
    · intro hf ⟨U, hU⟩
      exact IsZariskiLocalAtTarget.restrict hf _
    · intro hf
      exact P.of_zeroHypercover_target Y.affineCover
        fun i => of_targetAffineLocally_of_isPullback (.of_hasPullback _ _) hf

/--
lemma `copy` / 引理 `copy`

English:
lemma copy
  statement: {P P'} {Q Q'} [HasAffineProperty P Q]
  proof: e' ▸ isLocal_affineProperty P
  eq_targetAffineLocally' := e' ▸ e.symm ▸ eq_targetAffineLocally P

中文:
引理 copy
  结论: {P P'} {Q Q'} [HasAffine命题erty P Q]
  证明: e' ▸ isLocal_affineProperty P
  eq_targetAffineLocally' := e' ▸ e.symm ▸ eq_targetAffineLocally P

Depends on / 依赖: isLocal_affineProperty
-/
lemma copy {P P'} {Q Q'} [HasAffineProperty P Q]
    (e : P = P') (e' : Q = Q') : HasAffineProperty P' Q' where
  isLocal_affineProperty := e' ▸ isLocal_affineProperty P
  eq_targetAffineLocally' := e' ▸ e.symm ▸ eq_targetAffineLocally P

variable {P}

/--
theorem `of_isPullback` / 定理 `of_isPullback`

English:
theorem of_isPullback
  statement: {UX UY : Scheme.{u}} [IsAffine UY] {iY : UY ⟶ Y} [IsOpenImmersion iY]
  proof: letI := isLocal_affineProperty P
  of_targetAffineLocally_of_isPullback h (eq_targetAffineLocally (P := P) ▸ hf)

中文:
定理 of_isPullback
  结论: {UX UY : Scheme.{u}} [IsAffine UY] {iY : UY ⟶ Y} [IsOpenImmersion iY]
  证明: letI := isLocal_affineProperty P
  of_targetAffineLocally_of_isPullback h (eq_targetAffineLocally (P := P) ▸ hf)

Depends on / 依赖: eq_targetAffineLocally, isLocal_affineProperty, of_targetAffineLocally_of_isPullback
-/
theorem of_isPullback {UX UY : Scheme.{u}} [IsAffine UY] {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (hf : P f) :
    Q f' :=
  letI := isLocal_affineProperty P
  of_targetAffineLocally_of_isPullback h (eq_targetAffineLocally (P := P) ▸ hf)

/--
theorem `restrict` / 定理 `restrict`

English:
theorem restrict
  given: (hf : P f) (U : Y.affineOpens)
  proof: of_isPullback (isPullback_morphismRestrict f U).flip hf

中文:
定理 restrict
  条件: (hf : P f) (U : Y.affineOpens)
  证明: of_isPullback (isPullback_morphismRestrict f U).flip hf

Depends on / 依赖: isPullback_morphismRestrict, of_isPullback
-/
theorem restrict (hf : P f) (U : Y.affineOpens) :
    Q (f ∣_ U) :=
  of_isPullback (isPullback_morphismRestrict f U).flip hf

instance (priority := 900) : P.RespectsIso := by
  let := isLocal_affineProperty P
  rw [eq_targetAffineLocally P]
  infer_instance

/--
theorem `of_iSup_eq_top` / 定理 `of_iSup_eq_top`

English:
theorem of_iSup_eq_top
  proof: by
  let := isLocal_affineProperty P
  rw [eq_targetAffineLocally P]
  classical
  intro V
  induction V using of_affine_open_cover U hU with
  | basicOpen U r h =>
    have := AffineTargetMorphismProperty.IsLocal.to_basicOpen (f ∣_ U.1) (U.1.topIso.inv r) h
    exact (Q.arrow_mk_iso_iff
      (morp

中文:
定理 of_iSup_eq_top
  证明: by
  let := isLocal_affineProperty P
  rw [eq_targetAffineLocally P]
  classical
  intro V
  induction V using of_affine_open_cover U hU with
  | basicOpen U r h =>
    have := AffineTargetMorphismProperty.IsLocal.to_basicOpen (f ∣_ U.1) (U.1.topIso.inv r) h
    exact (Q.arrow_mk_iso_iff
      (morp

Depends on / 依赖: AffineTargetMorphismProperty, AffineTargetMorphismProperty.IsLocal.of_basicOpenCover, AffineTargetMorphismProperty.IsLocal.to_basicOpen, Ideal.map_span, Ideal.map_top, IsLocal, Q.arrow_mk_iso_iff, Scheme, Scheme.Opens.topIso, arrow_mk_iso_iff, basicOpen, classical, eq_targetAffineLocally, isLocal_affineProperty, map_span, map_top, morphismRestrictRestrictBasicOpen, of_affine_open_cover, of_basicOpenCover, openCover
-/
theorem of_iSup_eq_top
    {ι} (U : ι -> Y.affineOpens) (hU : ⨆ i, (U i : Y.Opens) = ⊤)
    (hU' : forall i, Q (f ∣_ U i)) :
    P f := by
  let := isLocal_affineProperty P
  rw [eq_targetAffineLocally P]
  classical
  intro V
  induction V using of_affine_open_cover U hU with
  | basicOpen U r h =>
    have := AffineTargetMorphismProperty.IsLocal.to_basicOpen (f ∣_ U.1) (U.1.topIso.inv r) h
    exact (Q.arrow_mk_iso_iff
      (morphismRestrictRestrictBasicOpen f _ r)).mp this
  | openCover U s hs H =>
    apply AffineTargetMorphismProperty.IsLocal.of_basicOpenCover _
      (s.image (Scheme.Opens.topIso _).inv) (by simp [← Ideal.map_span, hs, Ideal.map_top])
    intro ⟨r, hr⟩
    obtain ⟨r, hr', rfl⟩ := Finset.mem_image.mp hr
    exact (Q.arrow_mk_iso_iff
      (morphismRestrictRestrictBasicOpen f _ r).symm).mp (H ⟨r, hr'⟩)
  | hU i => exact hU' i

/--
theorem `iff_of_iSup_eq_top` / 定理 `iff_of_iSup_eq_top`

English:
theorem iff_of_iSup_eq_top
  proof: ⟨fun H _ => restrict H _, fun H => HasAffineProperty.of_iSup_eq_top U hU H⟩

中文:
定理 iff_of_iSup_eq_top
  证明: ⟨fun H _ => restrict H _, fun H => HasAffineProperty.of_iSup_eq_top U hU H⟩

Depends on / 依赖: HasAffineProperty, HasAffineProperty.of_iSup_eq_top, of_iSup_eq_top, restrict
-/
theorem iff_of_iSup_eq_top
    {ι} (U : ι -> Y.affineOpens) (hU : ⨆ i, (U i : Y.Opens) = ⊤) :
    P f ↔ forall i, Q (f ∣_ U i) :=
  ⟨fun H _ => restrict H _, fun H => HasAffineProperty.of_iSup_eq_top U hU H⟩

/--
theorem `of_openCover` / 定理 `of_openCover`

English:
theorem of_openCover
  proof: letI := isLocal_affineProperty P
  of_iSup_eq_top
    (fun i => ⟨_, isAffineOpen_opensRange (𝒰.f i)⟩) 𝒰.iSup_opensRange
    (fun i => (Q.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (h𝒰 i))

中文:
定理 of_openCover
  证明: letI := isLocal_affineProperty P
  of_iSup_eq_top
    (fun i => ⟨_, isAffineOpen_opensRange (𝒰.f i)⟩) 𝒰.iSup_opensRange
    (fun i => (Q.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (h𝒰 i))

Depends on / 依赖: Q.arrow_mk_iso_iff, arrow_mk_iso_iff, iSup_opensRange, isAffineOpen_opensRange, isLocal_affineProperty, morphismRestrictOpensRange, of_iSup_eq_top
-/
theorem of_openCover
    (𝒰 : Y.OpenCover) [forall i, IsAffine (𝒰.X i)] (h𝒰 : forall i, Q (𝒰.pullbackHom f i)) :
    P f :=
  letI := isLocal_affineProperty P
  of_iSup_eq_top
    (fun i => ⟨_, isAffineOpen_opensRange (𝒰.f i)⟩) 𝒰.iSup_opensRange
    (fun i => (Q.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (h𝒰 i))

/--
theorem `iff_of_openCover` / 定理 `iff_of_openCover`

English:
theorem iff_of_openCover
  given: (𝒰 : Y.OpenCover) [forall i, IsAffine (𝒰.X i)]
  proof: by
  let := isLocal_affineProperty P
  rw [iff_of_iSup_eq_top (P := P)
    (fun i => ⟨_]; rw [isAffineOpen_opensRange _⟩) 𝒰.iSup_opensRange]
  exact forall_congr' fun i => Q.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)

中文:
定理 iff_of_openCover
  条件: (𝒰 : Y.OpenCover) [对任意 i, IsAffine (𝒰.X i)]
  证明: by
  let := isLocal_affineProperty P
  rw [iff_of_iSup_eq_top (P := P)
    (fun i => ⟨_]; rw [isAffineOpen_opensRange _⟩) 𝒰.iSup_opensRange]
  exact forall_congr' fun i => Q.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)

Depends on / 依赖: Q.arrow_mk_iso_iff, arrow_mk_iso_iff, forall_congr, iSup_opensRange, iff_of_iSup_eq_top, isAffineOpen_opensRange, isLocal_affineProperty, morphismRestrictOpensRange
-/
theorem iff_of_openCover (𝒰 : Y.OpenCover) [forall i, IsAffine (𝒰.X i)] :
    P f ↔ forall i, Q (𝒰.pullbackHom f i) := by
  let := isLocal_affineProperty P
  rw [iff_of_iSup_eq_top (P := P)
    (fun i => ⟨_]; rw [isAffineOpen_opensRange _⟩) 𝒰.iSup_opensRange]
  exact forall_congr' fun i => Q.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)

/--
theorem `iff_of_isAffine` / 定理 `iff_of_isAffine`

English:
theorem iff_of_isAffine
  given: [IsAffine Y]
  statement: P f ↔ Q f
  proof: by
  let := isLocal_affineProperty P
  rw [iff_of_openCover (P := P) (Scheme.coverOfIsIso.{0} (𝟙 Y))]
  trans Q (pullback.snd f (𝟙 _))
  · exact ⟨fun H => H PUnit.unit, fun H _ => H⟩
  rw [← Category.comp_id (pullback.snd _ _)]; rw [← pullback.condition]; rw [Q.cancel_left_of_respectsIso]

中文:
定理 iff_of_isAffine
  条件: [IsAffine Y]
  结论: P f ↔ Q f
  证明: by
  let := isLocal_affineProperty P
  rw [iff_of_openCover (P := P) (Scheme.coverOfIsIso.{0} (𝟙 Y))]
  trans Q (pullback.snd f (𝟙 _))
  · exact ⟨fun H => H PUnit.unit, fun H _ => H⟩
  rw [← Category.comp_id (pullback.snd _ _)]; rw [← pullback.condition]; rw [Q.cancel_left_of_respectsIso]

Depends on / 依赖: Category, Category.comp_id, PUnit.unit, Q.cancel_left_of_respectsIso, Scheme, Scheme.coverOfIsIso, cancel_left_of_respectsIso, comp_id, condition, coverOfIsIso, iff_of_openCover, isLocal_affineProperty, pullback, pullback.condition, pullback.snd
-/
theorem iff_of_isAffine [IsAffine Y] : P f ↔ Q f := by
  let := isLocal_affineProperty P
  rw [iff_of_openCover (P := P) (Scheme.coverOfIsIso.{0} (𝟙 Y))]
  trans Q (pullback.snd f (𝟙 _))
  · exact ⟨fun H => H PUnit.unit, fun H _ => H⟩
  rw [← Category.comp_id (pullback.snd _ _)]; rw [← pullback.condition]; rw [Q.cancel_left_of_respectsIso]

set_option backward.isDefEq.respectTransparency false in
instance (priority := 900) : IsZariskiLocalAtTarget P := by
  let := isLocal_affineProperty P
  apply IsZariskiLocalAtTarget.mk'
  · rw [eq_targetAffineLocally P]
    intro X Y f U H V
    rw [Q.arrow_mk_iso_iff (morphismRestrictRestrict f _ _)]
    exact H ⟨_, V.2.image_of_isOpenImmersion (Y.ofRestrict _)⟩
  · rintro X Y f ι U hU H
    let 𝒰 := Y.openCoverOfIsOpenCover U hU
    apply of_openCover 𝒰.affineRefinement.openCover
    rintro ⟨i, j⟩
    have : P (𝒰.pullbackHom f i) := by
      refine (P.arrow_mk_iso_iff
        (morphismRestrictEq _ ?_ ≪≫ morphismRestrictOpensRange f (𝒰.f i))).mp (H i)
      exact (Scheme.Opens.opensRange_ι _).symm
    rw [← Q.cancel_left_of_respectsIso (𝒰.pullbackCoverAffineRefinementObjIso f _).inv]; rw [𝒰.pullbackCoverAffineRefinementObjIso_inv_pullbackHom]
    exact of_isPullback (.of_hasPullback _ _) this

open AffineTargetMorphismProperty in
/--
theorem `iff` / 定理 `iff`

English:
theorem iff
  given: {P : MorphismProperty Scheme} {Q : AffineTargetMorphismProperty}
  proof: ⟨fun _ => ⟨inferInstance, ext fun _ _ _ => iff_of_isAffine.symm⟩,
    fun ⟨_, e⟩ => e ▸ of_isZariskiLocalAtTarget P⟩

中文:
定理 iff
  条件: {P : Morphism命题erty Scheme} {Q : AffineTargetMorphism命题erty}
  证明: ⟨fun _ => ⟨inferInstance, ext fun _ _ _ => iff_of_isAffine.symm⟩,
    fun ⟨_, e⟩ => e ▸ of_isZariskiLocalAtTarget P⟩
-/
protected theorem iff {P : MorphismProperty Scheme} {Q : AffineTargetMorphismProperty} :
    HasAffineProperty P Q ↔ IsZariskiLocalAtTarget P ∧ Q = of P :=
  ⟨fun _ => ⟨inferInstance, ext fun _ _ _ => iff_of_isAffine.symm⟩,
    fun ⟨_, e⟩ => e ▸ of_isZariskiLocalAtTarget P⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullback_fst_of_right` / 定理 `pullback_fst_of_right`

English:
theorem pullback_fst_of_right
  statement: (hP' : Q.IsStableUnderBaseChange)
  proof: by
  let := isLocal_affineProperty P
  rw [iff_of_openCover (P := P) X.affineCover]
  intro i
  let e := pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g (X.affineCover.f i)
  have : e.hom ≫ pullback.fst _ _ = X.affineCover.pullbackHom (pullback.fst _ _) i := by
    simp [e, Scheme.Cover.pull

中文:
定理 pullback_fst_of_right
  结论: (hP' : Q.IsStableUnderBaseChange)
  证明: by
  let := isLocal_affineProperty P
  rw [iff_of_openCover (P := P) X.affineCover]
  intro i
  let e := pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g (X.affineCover.f i)
  have : e.hom ≫ pullback.fst _ _ = X.affineCover.pullbackHom (pullback.fst _ _) i := by
    simp [e, Scheme.Cover.pull
-/
private theorem pullback_fst_of_right (hP' : Q.IsStableUnderBaseChange)
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffine S] (H : Q g) :
    P (pullback.fst f g) := by
  let := isLocal_affineProperty P
  rw [iff_of_openCover (P := P) X.affineCover]
  intro i
  let e := pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g (X.affineCover.f i)
  have : e.hom ≫ pullback.fst _ _ = X.affineCover.pullbackHom (pullback.fst _ _) i := by
    simp [e, Scheme.Cover.pullbackHom]
  rw [← this]; rw [Q.cancel_left_of_respectsIso]
  apply hP' (.of_hasPullback _ _)
  exact H

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isStableUnderBaseChange` / 定理 `isStableUnderBaseChange`

English:
theorem isStableUnderBaseChange
  given: (hP' : Q.IsStableUnderBaseChange)
  proof: MorphismProperty.IsStableUnderBaseChange.mk'
    (fun X Y S f g _ H => by
      rw [P.iff_of_zeroHypercover_target (S.affineCover.pullback₁ f)]
      intro i
      let e : pullback (pullback.fst f g) ((S.affineCover.pullback₁ f).f i) ≅
          _ := by
        refine pullbackSymmetry _ _ ≪≫ pullbac

中文:
定理 isStableUnderBaseChange
  条件: (hP' : Q.IsStableUnderBaseChange)
  证明: MorphismProperty.IsStableUnderBaseChange.mk'
    (fun X Y S f g _ H => by
      rw [P.iff_of_zeroHypercover_target (S.affineCover.pullback₁ f)]
      intro i
      let e : pullback (pullback.fst f g) ((S.affineCover.pullback₁ f).f i) ≅
          _ := by
        refine pullbackSymmetry _ _ ≪≫ pullbac

Depends on / 依赖: IsStableUnderBaseChange, MorphismProperty, MorphismProperty.IsStableUnderBaseChange.mk, P.iff_of_zeroHypercover_target, S.affineCover.f, S.affineCover.pullback, affineCover, condition, iff_of_zeroHypercover_target, pullback, pullback.condition, pullback.fst, pullback.map, pullback.snd, pullbackRightPullbackFstIso, pullbackSymmetry
-/
theorem isStableUnderBaseChange (hP' : Q.IsStableUnderBaseChange) :
    P.IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.mk'
    (fun X Y S f g _ H => by
      rw [P.iff_of_zeroHypercover_target (S.affineCover.pullback₁ f)]
      intro i
      let e : pullback (pullback.fst f g) ((S.affineCover.pullback₁ f).f i) ≅
          _ := by
        refine pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g _ ≪≫ ?_ ≪≫
          (pullbackRightPullbackFstIso (S.affineCover.f i) g
            (pullback.snd f (S.affineCover.f i))).symm
        exact asIso
          (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simpa using! pullback.condition) (by simp))
      have : e.hom ≫ pullback.fst _ _ =
          pullback.snd (pullback.fst f g) ((S.affineCover.pullback₁ f).f i) := by
        simp [e]
      rw [← this]; rw [P.cancel_left_of_respectsIso]
      apply HasAffineProperty.pullback_fst_of_right hP'
      let := isLocal_affineProperty P
      rw [← pullbackSymmetry_hom_comp_snd]; rw [Q.cancel_left_of_respectsIso]
      apply of_isPullback (.of_hasPullback _ _) H)

/--
lemma `isZariskiLocalAtSource` / 引理 `isZariskiLocalAtSource`

English:
lemma isZariskiLocalAtSource
  proof: by
  refine .mk_of_small (fun {X Y f} 𝒰 hf => ?_) (fun {X Y f} 𝒰 hf => ?_) <;>
  simp_rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top _ (iSup_affineOpens_eq_top Y),
      HasAffineProperty.iff_of_isAffine, morphismRestrict_comp] at hf ⊢
  · intro i U
    let 𝒰' : X.OpenCover := (Scheme.Cover.ulift 𝒰).

中文:
引理 isZariskiLocalAtSource
  证明: by
  refine .mk_of_small (fun {X Y f} 𝒰 hf => ?_) (fun {X Y f} 𝒰 hf => ?_) <;>
  simp_rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top _ (iSup_affineOpens_eq_top Y),
      HasAffineProperty.iff_of_isAffine, morphismRestrict_comp] at hf ⊢
  · intro i U
    let 𝒰' : X.OpenCover := (Scheme.Cover.ulift 𝒰).

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_iSup_eq_top, OpenCover, Scheme, Scheme.Cover.ulift, Scheme.OpenCover.restrict, X.OpenCover, iSup_affineOpens_eq_top, iff_of_iSup_eq_top, iff_of_isAffine, mk_of_small, morphismRestrict_comp, restrict, simp_rw
-/
lemma isZariskiLocalAtSource
    (H : forall {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] (𝒰 : Scheme.OpenCover.{u} X),
        Q f ↔ forall i, Q (𝒰.f i ≫ f)) : IsZariskiLocalAtSource P := by
  refine .mk_of_small (fun {X Y f} 𝒰 hf => ?_) (fun {X Y f} 𝒰 hf => ?_) <;>
  simp_rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top _ (iSup_affineOpens_eq_top Y),
      HasAffineProperty.iff_of_isAffine, morphismRestrict_comp] at hf ⊢
  · intro i U
    let 𝒰' : X.OpenCover := (Scheme.Cover.ulift 𝒰).add (𝒰.f i)
    exact (H (f ∣_ U.1) (𝒰'.restrict _)).mp (hf _) none
  · intro U
    rw [H (f ∣_ U.1) (Scheme.OpenCover.restrict 𝒰 _)]
    intro i
    exact hf _ _

end HasAffineProperty

end targetAffineLocally

open MorphismProperty

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict` / 引理 `hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict`

English:
lemma hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict
  statement: (P : MorphismProperty Scheme)
  proof: by
    have : (f ≫ g) ⁻¹ᵁ g.opensRange = ⊤ := by simp
    have : f = X.topIso.inv ≫ (X.isoOfEq this).inv ≫ (f ≫ g) ∣_ g.opensRange ≫
        (IsOpenImmersion.isoOfRangeEq g.opensRange.ι g (by simp)).hom := by
      simp [← cancel_mono g]
    simp_rw [this, cancel_left_of_respectsIso (P := P), cancel

中文:
引理 hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict
  结论: (P : Morphism命题erty Scheme)
  证明: by
    have : (f ≫ g) ⁻¹ᵁ g.opensRange = ⊤ := by simp
    have : f = X.topIso.inv ≫ (X.isoOfEq this).inv ≫ (f ≫ g) ∣_ g.opensRange ≫
        (IsOpenImmersion.isoOfRangeEq g.opensRange.ι g (by simp)).hom := by
      simp [← cancel_mono g]
    simp_rw [this, cancel_left_of_respectsIso (P := P), cancel

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, X.isoOfEq, X.topIso.inv, cancel_left_of_respectsIso, cancel_mono, cancel_right_of_respectsIso, g.opensRange, isoOfEq, isoOfRangeEq, opensRange, simp_rw, topIso
-/
lemma hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict (P : MorphismProperty Scheme)
    [P.RespectsIso] (H : forall {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens), P f -> P (f ∣_ U)) :
    P.HasOfPostcompProperty @IsOpenImmersion where
  of_postcomp {X Y Z} f g hg hfg := by
    have : (f ≫ g) ⁻¹ᵁ g.opensRange = ⊤ := by simp
    have : f = X.topIso.inv ≫ (X.isoOfEq this).inv ≫ (f ≫ g) ∣_ g.opensRange ≫
        (IsOpenImmersion.isoOfRangeEq g.opensRange.ι g (by simp)).hom := by
      simp [← cancel_mono g]
    simp_rw [this, cancel_left_of_respectsIso (P := P), cancel_right_of_respectsIso (P := P)]
    exact H _ _ hfg

instance (P : MorphismProperty Scheme) [P.IsStableUnderBaseChange] :
    P.HasOfPostcompProperty @IsOpenImmersion :=
  HasOfPostcompProperty.of_le P (.monomorphisms Scheme) (fun _ _ f _ => inferInstanceAs (Mono f))

end AlgebraicGeometry
