/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.RingHom.Locally

/-!

# Properties of morphisms from properties of ring homs.

We provide the basic framework for talking about properties of morphisms that come from properties
of ring homs. For `P` a property of ring homs, we have two ways of defining a property of scheme
morphisms:

Let `f : X ⟶ Y`,
- `targetAffineLocally (affineAnd P)`: the preimage of an affine open `U = Spec A` is affine
  (`= Spec B`) and `A ⟶ B` satisfies `P`. (in `Mathlib/AlgebraicGeometry/Morphisms/AffineAnd.lean`)
- `affineLocally P`: For each pair of affine open `U = Spec A ⊆ X` and `V = Spec B ⊆ f ⁻¹' U`,
  the ring hom `A ⟶ B` satisfies `P`.

For these notions to be well defined, we require `P` be a sufficient local property. For the former,
`P` should be local on the source (`RingHom.RespectsIso P`, `RingHom.LocalizationPreserves P`,
`RingHom.OfLocalizationSpan`), and `targetAffineLocally (affine_and P)` will be local on
the target.

For the latter `P` should be local on the target (`RingHom.PropertyIsLocal P`), and
`affineLocally P` will be local on both the source and the target.
We also provide the following interface:

## `HasRingHomProperty`

`HasRingHomProperty P Q` is a type class asserting that `P` is local at the target and the source,
and for `f : Spec B ⟶ Spec A`, it is equivalent to the ring hom property `Q` on `Γ(f)`.

For `HasRingHomProperty P Q` and `f : X ⟶ Y`, we provide these API lemmas:
- `AlgebraicGeometry.HasRingHomProperty.iff_appLE`:
    `P f` if and only if `Q (f.appLE U V _)` for all affine `U : Opens Y` and `V : Opens X`.
- `AlgebraicGeometry.HasRingHomProperty.iff_of_source_openCover`:
    If `Y` is affine, `P f ↔ ∀ i, Q ((𝒰.map i ≫ f).appTop)` for an affine open cover `𝒰` of `X`.
- `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`:
    If `X` and `Y` are affine, then `P f ↔ Q (f.appTop)`.
- `AlgebraicGeometry.HasRingHomProperty.Spec_iff`:
    `P (Spec.map φ) ↔ Q φ`
- `AlgebraicGeometry.HasRingHomProperty.iff_of_iSup_eq_top`:
    If `Y` is affine, `P f ↔ ∀ i, Q (f.appLE ⊤ (U i) _)` for a family `U` of affine opens of `X`.
- `AlgebraicGeometry.HasRingHomProperty.of_isOpenImmersion`:
    If `f` is an open immersion then `P f`.
- `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`:
    If `Q` is stable under base change, then so is `P`.

We also provide the instances `P.IsMultiplicative`, `P.IsStableUnderComposition`,
`IsZariskiLocalAtTarget P`, `IsZariskiLocalAtSource P`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe u

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits AlgebraicGeometry

namespace RingHom

variable (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsStableUnderBaseChange.pullback_fst_appTop` / 定理 `IsStableUnderBaseChange.pullback_fst_appTop`

English:
theorem IsStableUnderBaseChange.pullback_fst_appTop
  proof: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
  erw [← PreservesPullback.iso_inv_fst AffineScheme.forgetToScheme (AffineScheme.ofHom f)
      (AffineScheme.ofHom g)]
  rw [Scheme.Hom.comp_appTop]; rw [CommRingCat.hom_comp]; rw [hP'.cancel_

中文:
定理 IsStableUnderBaseChange.pullback_fst_appTop
  证明: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
  erw [← PreservesPullback.iso_inv_fst AffineScheme.forgetToScheme (AffineScheme.ofHom f)
      (AffineScheme.ofHom g)]
  rw [Scheme.Hom.comp_appTop]; rw [CommRingCat.hom_comp]; rw [hP'.cancel_
-/
theorem IsStableUnderBaseChange.pullback_fst_appTop
    (hP : IsStableUnderBaseChange P) (hP' : RespectsIso P)
    {X Y S : Scheme} [IsAffine X] [IsAffine Y] [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    (H : P g.appTop.hom) : P (pullback.fst f g).appTop.hom := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
  erw [← PreservesPullback.iso_inv_fst AffineScheme.forgetToScheme (AffineScheme.ofHom f)
      (AffineScheme.ofHom g)]
  rw [Scheme.Hom.comp_appTop]; rw [CommRingCat.hom_comp]; rw [hP'.cancel_right_isIso]; rw [AffineScheme.forgetToScheme_map]
  have := congr_arg Quiver.Hom.unop
      (PreservesPullback.iso_hom_fst AffineScheme.Γ.rightOp (AffineScheme.ofHom f)
        (AffineScheme.ofHom g))
  simp only [AffineScheme.Γ, Functor.rightOp_obj, Functor.comp_obj, Functor.op_obj, unop_comp,
    AffineScheme.forgetToScheme_obj, Scheme.Γ_obj, Functor.rightOp_map, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op, AffineScheme.forgetToScheme_map, Scheme.Γ_map] at this
  rw [← this]; rw [CommRingCat.hom_comp]; rw [hP'.cancel_right_isIso]; rw [← pushoutIsoUnopPullback_inl_hom]; rw [CommRingCat.hom_comp]; rw [hP'.cancel_right_isIso]
  exact hP.pushout_inl hP' _ _ H

end RingHom

namespace AlgebraicGeometry

section affineLocally

variable (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop)

/--
Definition of `sourceAffineLocally` / `sourceAffineLocally` 的定义

English:
definition sourceAffineLocally
  signature: : AffineTargetMorphismProperty
  body: fun X _ f _ =>
  forall U : X.affineOpens, P (f.appLE ⊤ U le_top).hom

中文:
定义 sourceAffineLocally
  签名: : AffineTargetMorphism命题erty
  定义体: fun X _ f _ =>
  forall U : X.affineOpens, P (f.appLE ⊤ U le_top).hom
-/
def sourceAffineLocally : AffineTargetMorphismProperty := fun X _ f _ =>
  forall U : X.affineOpens, P (f.appLE ⊤ U le_top).hom

/--
Definition of `affineLocally` / `affineLocally` 的定义

English:
abbreviation affineLocally
  signature: : MorphismProperty Scheme.{u}
  body: targetAffineLocally (sourceAffineLocally P)

中文:
缩写 affineLocally
  签名: : Morphism命题erty Scheme.{u}
  定义体: targetAffineLocally (sourceAffineLocally P)

Depends on / 依赖: sourceAffineLocally, targetAffineLocally
-/
abbrev affineLocally : MorphismProperty Scheme.{u} :=
  targetAffineLocally (sourceAffineLocally P)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `sourceAffineLocally_respectsIso` / 定理 `sourceAffineLocally_respectsIso`

English:
theorem sourceAffineLocally_respectsIso
  given: (h₁ : RingHom.RespectsIso P)
  proof: by
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H U
    have : IsIso (e.hom.appLE (e.hom ''ᵁ U) U.1 (e.hom.preimage_image_eq _).ge) :=
      inferInstanceAs (IsIso (e.hom.app _ ≫
        X.presheaf.map (eqToHom (e.hom.preimage_image_eq _).symm).op))
    rw [← Scheme.Hom.appLE_comp_

中文:
定理 sourceAffineLocally_respectsIso
  条件: (h₁ : RingHom.RespectsIso P)
  证明: by
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H U
    have : IsIso (e.hom.appLE (e.hom ''ᵁ U) U.1 (e.hom.preimage_image_eq _).ge) :=
      inferInstanceAs (IsIso (e.hom.app _ ≫
        X.presheaf.map (eqToHom (e.hom.preimage_image_eq _).symm).op))
    rw [← Scheme.Hom.appLE_comp_

Depends on / 依赖: AffineTargetMorphismProperty, AffineTargetMorphismProperty.respectsIso_mk, CommRi, CommRingCat, CommRingCat.hom_comp, Scheme, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.comp_appLE, U.prop.image_of_isOpenImmersion, X.presheaf.map, appLE_comp_appLE, cancel_right_isIso, comp_appLE, e.hom, e.hom.app, e.hom.appLE, e.hom.preimage_image_eq, eqToHom, hom_comp, image_of_isOpenImmersion
-/
theorem sourceAffineLocally_respectsIso (h₁ : RingHom.RespectsIso P) :
    (sourceAffineLocally P).toProperty.RespectsIso := by
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H U
    have : IsIso (e.hom.appLE (e.hom ''ᵁ U) U.1 (e.hom.preimage_image_eq _).ge) :=
      inferInstanceAs (IsIso (e.hom.app _ ≫
        X.presheaf.map (eqToHom (e.hom.preimage_image_eq _).symm).op))
    rw [← Scheme.Hom.appLE_comp_appLE _ _ ⊤ (e.hom ''ᵁ U) U.1 le_top (e.hom.preimage_image_eq _).ge]; rw [CommRingCat.hom_comp]; rw [h₁.cancel_right_isIso]
    exact H ⟨_, U.prop.image_of_isOpenImmersion e.hom⟩
  · introv H U
    rw [Scheme.Hom.comp_appLE]; rw [CommRingCat.hom_comp]; rw [h₁.cancel_left_isIso]
    exact H U

/--
theorem `affineLocally_respectsIso` / 定理 `affineLocally_respectsIso`

English:
theorem affineLocally_respectsIso
  given: (h : RingHom.RespectsIso P)
  statement: (affineLocally P).RespectsIso
  proof: letI := sourceAffineLocally_respectsIso P h
  inferInstance

中文:
定理 affineLocally_respectsIso
  条件: (h : RingHom.RespectsIso P)
  结论: (affineLocally P).RespectsIso
  证明: letI := sourceAffineLocally_respectsIso P h
  inferInstance

Depends on / 依赖: of_mono, sourceAffineLocally_respectsIso
-/
theorem affineLocally_respectsIso (h : RingHom.RespectsIso P) : (affineLocally P).RespectsIso :=
  letI := sourceAffineLocally_respectsIso P h
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
open Scheme in
/--
theorem `sourceAffineLocally_morphismRestrict` / 定理 `sourceAffineLocally_morphismRestrict`

English:
theorem sourceAffineLocally_morphismRestrict
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y)
  proof: by
  dsimp only [sourceAffineLocally]
  simp only [morphismRestrict_appLE]
  rw [(affineOpensRestrict (f ⁻¹ᵁ U)).forall_congr_left]; rw [Subtype.forall]
  refine forall₂_congr fun V h => ?_
  have := (affineOpensRestrict (f ⁻¹ᵁ U)).apply_symm_apply ⟨V, h⟩
  exact f.appLE_congr _ (Opens.ι_image_top _

中文:
定理 sourceAffineLocally_morphismRestrict
  结论: {X Y : Scheme.{u}} (f : X ⟶ Y)
  证明: by
  dsimp only [sourceAffineLocally]
  simp only [morphismRestrict_appLE]
  rw [(affineOpensRestrict (f ⁻¹ᵁ U)).forall_congr_left]; rw [Subtype.forall]
  refine forall₂_congr fun V h => ?_
  have := (affineOpensRestrict (f ⁻¹ᵁ U)).apply_symm_apply ⟨V, h⟩
  exact f.appLE_congr _ (Opens.ι_image_top _

Depends on / 依赖: Functor, Functor.congr_obj, NatTrans, NatTrans.mono_iff_mono_app, PartialOrder, PartialOrder.mem_nerve_nonDegenerate_iff_injective, Subtype, Subtype.forall, affineOpensRestrict, appLE_congr, apply_symm_apply, congr_obj, f.appLE_congr, f.hom, forall_congr_left, mem_nerve_nonDegenerate_iff_injective, mono_iff_injective, mono_iff_mono_app, morphismRestrict_appLE, sourceAffineLocally
-/
theorem sourceAffineLocally_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    @sourceAffineLocally P _ _ (f ∣_ U) hU ↔
      forall (V : X.affineOpens) (e : V.1 <= f ⁻¹ᵁ U), P (f.appLE U V e).hom := by
  dsimp only [sourceAffineLocally]
  simp only [morphismRestrict_appLE]
  rw [(affineOpensRestrict (f ⁻¹ᵁ U)).forall_congr_left]; rw [Subtype.forall]
  refine forall₂_congr fun V h => ?_
  have := (affineOpensRestrict (f ⁻¹ᵁ U)).apply_symm_apply ⟨V, h⟩
  exact f.appLE_congr _ (Opens.ι_image_top _) congr($(this).1.1) (fun f => P f.hom)

/--
theorem `affineLocally_iff_affineOpens_le` / 定理 `affineLocally_iff_affineOpens_le`

English:
theorem affineLocally_iff_affineOpens_le
  given: {X Y : Scheme.{u}} (f : X ⟶ Y)
  proof: forall_congr' fun U => sourceAffineLocally_morphismRestrict P f U U.2

中文:
定理 affineLocally_iff_affineOpens_le
  条件: {X Y : Scheme.{u}} (f : X ⟶ Y)
  证明: forall_congr' fun U => sourceAffineLocally_morphismRestrict P f U U.2

Depends on / 依赖: Nonsingular, Nonsingular.of_iso, forall_congr, isoNerve, of_iso, sourceAffineLocally_morphismRestrict, stdSimplex, stdSimplex.isoNerve
-/
theorem affineLocally_iff_affineOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) :
    affineLocally.{u} P f ↔
      forall (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 <= f ⁻¹ᵁ U.1), P (f.appLE U V e).hom :=
  forall_congr' fun U => sourceAffineLocally_morphismRestrict P f U U.2

/--
theorem `affineLocally_iff_forall_isAffineOpen` / 定理 `affineLocally_iff_forall_isAffineOpen`

English:
theorem affineLocally_iff_forall_isAffineOpen
  given: {X Y : Scheme.{u}} (f : X ⟶ Y)
  proof: by
  simp [affineLocally_iff_affineOpens_le, Scheme.affineOpens]

中文:
定理 affineLocally_iff_forall_isAffineOpen
  条件: {X Y : Scheme.{u}} (f : X ⟶ Y)
  证明: by
  simp [affineLocally_iff_affineOpens_le, Scheme.affineOpens]

Depends on / 依赖: Nonsingular, Nonsingular.of_iso, Scheme, Scheme.affineOpens, affineLocally_iff_affineOpens_le, affineOpens, isoNerve, of_iso, prodStdSimplex, prodStdSimplex.isoNerve
-/
theorem affineLocally_iff_forall_isAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y) :
    affineLocally.{u} P f ↔
      forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U),
      P (f.appLE U V e).hom := by
  simp [affineLocally_iff_affineOpens_le, Scheme.affineOpens]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sourceAffineLocally_isLocal` / 定理 `sourceAffineLocally_isLocal`

English:
theorem sourceAffineLocally_isLocal
  statement: (h₁ : RingHom.RespectsIso P)
  proof: by
  constructor
  · exact sourceAffineLocally_respectsIso P h₁
  · intro X Y _ f r H
    rw [sourceAffineLocally_morphismRestrict]
    intro U hU
    have : X.basicOpen (f.appLE ⊤ U (by simp) r) = U := by
      simp only [Scheme.Hom.appLE, Opens.map_top, CommRingCat.comp_apply]
      rw [Scheme.bas

中文:
定理 sourceAffineLocally_isLocal
  结论: (h₁ : RingHom.RespectsIso P)
  证明: by
  constructor
  · exact sourceAffineLocally_respectsIso P h₁
  · intro X Y _ f r H
    rw [sourceAffineLocally_morphismRestrict]
    intro U hU
    have : X.basicOpen (f.appLE ⊤ U (by simp) r) = U := by
      simp only [Scheme.Hom.appLE, Opens.map_top, CommRingCat.comp_apply]
      rw [Scheme.bas

Depends on / 依赖: CommRingCat, CommRingCat.comp_apply, CommRingCat.hom_ofHom, IsAffineOpen, IsAffineOpen.appLE_eq_away_map, Opens.map_top, Scheme, Scheme.Hom.appLE, Scheme.basicOpen_res, X.basicOpen, allowSynthFailures, appLE_congr, appLE_eq_away_map, basicOpen, basicOpen_res, comp_apply, f.appLE, f.appLE_congr, f.hom, hom_ofHom
-/
theorem sourceAffineLocally_isLocal (h₁ : RingHom.RespectsIso P)
    (h₂ : RingHom.LocalizationAwayPreserves P) (h₃ : RingHom.OfLocalizationSpan P) :
    (sourceAffineLocally P).IsLocal := by
  constructor
  · exact sourceAffineLocally_respectsIso P h₁
  · intro X Y _ f r H
    rw [sourceAffineLocally_morphismRestrict]
    intro U hU
    have : X.basicOpen (f.appLE ⊤ U (by simp) r) = U := by
      simp only [Scheme.Hom.appLE, Opens.map_top, CommRingCat.comp_apply]
      rw [Scheme.basicOpen_res]
      simpa using hU
    rw [← f.appLE_congr (by simp [Scheme.Hom.appLE]) rfl this (fun f => P f.hom),
      IsAffineOpen.appLE_eq_away_map f (isAffineOpen_top Y) U.2 _ r]
    simp only [CommRingCat.hom_ofHom]
    apply +allowSynthFailures h₂
    exact H U
  · introv hs hs' U
    apply h₃ _ _ hs
    intro r
    simp_rw [sourceAffineLocally_morphismRestrict] at hs'
    have := hs' r ⟨X.basicOpen (f.appLE ⊤ U le_top r.1), U.2.basicOpen (f.appLE ⊤ U le_top r.1)⟩
      (by simp [Scheme.Hom.appLE])
    rwa [IsAffineOpen.appLE_eq_away_map f (isAffineOpen_top Y) U.2, CommRingCat.hom_ofHom,
      ← h₁.isLocalization_away_iff] at this

variable {P}

/--
lemma `affineLocally_le` / 引理 `affineLocally_le`

English:
lemma affineLocally_le
  statement: {Q : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}
  proof: fun _ _ _ hf U V => hPQ (hf U V)

中文:
引理 affineLocally_le
  结论: {Q : 对任意 {R S : 类型u} [CommRing R] [CommRing S], (R ->+* S) -> 命题}
  证明: fun _ _ _ hf U V => hPQ (hf U V)
-/
lemma affineLocally_le {Q : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}
    (hPQ : forall {R S : Type u} [CommRing R] [CommRing S] {f : R ->+* S}, P f -> Q f) :
    affineLocally P <= affineLocally Q :=
  fun _ _ _ hf U V => hPQ (hf U V)

open RingHom

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exists_basicOpen_le_appLE_of_appLE_of_isAffine` / 引理 `exists_basicOpen_le_appLE_of_appLE_of_isAffine`

English:
lemma exists_basicOpen_le_appLE_of_appLE_of_isAffine
  proof: by
  obtain ⟨r, r', hBrr', hBfx⟩ := exists_basicOpen_le_affine_inter U₁.2 U₂.2 (f x)
    ⟨hfx₁, e₂ hx₂⟩
  have ha : IsAffineOpen (X.basicOpen (f.appLE U₂ V₂ e₂ r')) := V₂.2.basicOpen _
  have hxa : x in X.basicOpen (f.appLE U₂ V₂ e₂ r') := by
    simpa [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen]

中文:
引理 exists_basicOpen_le_appLE_of_appLE_of_isAffine
  证明: by
  obtain ⟨r, r', hBrr', hBfx⟩ := exists_basicOpen_le_affine_inter U₁.2 U₂.2 (f x)
    ⟨hfx₁, e₂ hx₂⟩
  have ha : IsAffineOpen (X.basicOpen (f.appLE U₂ V₂ e₂ r')) := V₂.2.basicOpen _
  have hxa : x in X.basicOpen (f.appLE U₂ V₂ e₂ r') := by
    simpa [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen]

Depends on / 依赖: And.intro, IsAffineOpen, Scheme, Scheme.Hom.appLE, Scheme.preimage_basicOpen, X.basicOpen, basicOpen, exists_basicOpen_le_affine_inter, f.appLE, isLocalization_basicO, isLocalization_basicOpen, preimage_basicOpen
-/
lemma exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P)
    (x : X) (U₁ : Y.affineOpens) (U₂ : Y.affineOpens) (V₁ : X.affineOpens) (V₂ : X.affineOpens)
    (hx₁ : x in V₁.1) (hx₂ : x in V₂.1) (e₂ : V₂.1 <= f ⁻¹ᵁ U₂.1) (h₂ : P (f.appLE U₂ V₂ e₂).hom)
    (hfx₁ : f x in U₁.1) :
    exists (r : Γ(Y, U₁)) (s : Γ(X, V₁)) (_ : x in X.basicOpen s)
      (e : X.basicOpen s <= f ⁻¹ᵁ Y.basicOpen r),
        P (f.appLE (Y.basicOpen r) (X.basicOpen s) e).hom := by
  obtain ⟨r, r', hBrr', hBfx⟩ := exists_basicOpen_le_affine_inter U₁.2 U₂.2 (f x)
    ⟨hfx₁, e₂ hx₂⟩
  have ha : IsAffineOpen (X.basicOpen (f.appLE U₂ V₂ e₂ r')) := V₂.2.basicOpen _
  have hxa : x in X.basicOpen (f.appLE U₂ V₂ e₂ r') := by
    simpa [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen] using And.intro hx₂ (hBrr' ▸ hBfx)
  obtain ⟨s, s', hBss', hBx⟩ := exists_basicOpen_le_affine_inter V₁.2 ha x ⟨hx₁, hxa⟩
  have := V₂.2.isLocalization_basicOpen (f.appLE U₂ V₂ e₂ r')
  have := U₂.2.isLocalization_basicOpen r'
  have := ha.isLocalization_basicOpen s'
  have ers : X.basicOpen s <= f ⁻¹ᵁ Y.basicOpen r := by
    rw [hBss']; rw [hBrr']
    apply le_trans (X.basicOpen_le _)
    simp [Scheme.Hom.appLE]
  have heq : f.appLE (Y.basicOpen r') (X.basicOpen s') (hBrr' ▸ hBss' ▸ ers) =
      f.appLE (Y.basicOpen r') (X.basicOpen (f.appLE U₂ V₂ e₂ r')) (by simp [Scheme.Hom.appLE]) ≫
        CommRingCat.ofHom (algebraMap _ _) := by
    simp only [Scheme.Hom.appLE, homOfLE_leOfHom, Category.assoc]
    congr
    apply X.presheaf.map_comp
  refine ⟨r, s, hBx, ers, ?_⟩
  · rw [f.appLE_congr _ hBrr' hBss' (fun f => P f.hom), heq]
    apply hPa _ s' _
    rw [U₂.2.appLE_eq_away_map f V₂.2]
    exact hPl _ _ _ _ h₂

/--
lemma `exists_affineOpens_le_appLE_of_appLE` / 引理 `exists_affineOpens_le_appLE_of_appLE`

English:
lemma exists_affineOpens_le_appLE_of_appLE
  proof: by
  obtain ⟨r, hBr, hBfx⟩ := U₂.2.exists_basicOpen_le ⟨f x, hfx₁⟩ (e₂ hx₂)
  obtain ⟨s, hBs, hBx⟩ := V₂.2.exists_basicOpen_le ⟨x, hx₁⟩ hx₂
  obtain ⟨r', s', hBx', e', hf'⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine hPa hPl x
    ⟨Y.basicOpen r, U₂.2.basicOpen _⟩ U₂ ⟨X.basicOpen s, V₂.2.basic

中文:
引理 exists_affineOpens_le_appLE_of_appLE
  证明: by
  obtain ⟨r, hBr, hBfx⟩ := U₂.2.exists_basicOpen_le ⟨f x, hfx₁⟩ (e₂ hx₂)
  obtain ⟨s, hBs, hBx⟩ := V₂.2.exists_basicOpen_le ⟨x, hx₁⟩ hx₂
  obtain ⟨r', s', hBx', e', hf'⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine hPa hPl x
    ⟨Y.basicOpen r, U₂.2.basicOpen _⟩ U₂ ⟨X.basicOpen s, V₂.2.basic

Depends on / 依赖: X.basicOpen, X.basicOpen_le, Y.basicOpen, Y.basicOpen_le, basicOpen, basicOpen_le, exists_basicOpen_le, exists_basicOpen_le_appLE_of_appLE_of_isAffine, le_trans
-/
lemma exists_affineOpens_le_appLE_of_appLE
    (hPa : StableUnderCompositionWithLocalizationAwayTarget P) (hPl : LocalizationAwayPreserves P)
    (x : X) (U₁ : Y.Opens) (U₂ : Y.affineOpens) (V₁ : X.Opens) (V₂ : X.affineOpens)
    (hx₁ : x in V₁) (hx₂ : x in V₂.1) (e₂ : V₂.1 <= f ⁻¹ᵁ U₂.1) (h₂ : P (f.appLE U₂ V₂ e₂).hom)
    (hfx₁ : f x in U₁.1) :
    exists (U' : Y.affineOpens) (V' : X.affineOpens) (_ : U'.1 <= U₁) (_ : V'.1 <= V₁) (_ : x in V'.1)
      (e : V'.1 <= f ⁻¹ᵁ U'.1), P (f.appLE U' V' e).hom := by
  obtain ⟨r, hBr, hBfx⟩ := U₂.2.exists_basicOpen_le ⟨f x, hfx₁⟩ (e₂ hx₂)
  obtain ⟨s, hBs, hBx⟩ := V₂.2.exists_basicOpen_le ⟨x, hx₁⟩ hx₂
  obtain ⟨r', s', hBx', e', hf'⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine hPa hPl x
    ⟨Y.basicOpen r, U₂.2.basicOpen _⟩ U₂ ⟨X.basicOpen s, V₂.2.basicOpen _⟩ V₂ hBx hx₂ e₂ h₂ hBfx
  exact ⟨⟨Y.basicOpen r', (U₂.2.basicOpen _).basicOpen _⟩,
    ⟨X.basicOpen s', (V₂.2.basicOpen _).basicOpen _⟩, le_trans (Y.basicOpen_le _) hBr,
    le_trans (X.basicOpen_le _) hBs, hBx', e', hf'⟩

end affineLocally

/--
Definition of `HasRingHomProperty` / `HasRingHomProperty` 的定义

English:
class HasRingHomProperty
  parameters: (P : MorphismProperty Scheme.{u})
  axioms and operations (2):
    - isLocal_ringHomProperty : RingHom.PropertyIsLocal Q
    - eq_affineLocally' : P = affineLocally Q

中文:
类 HasRingHomProperty
  参数: (P : Morphism命题erty Scheme.{u})
  公理与运算 (2 个):
    - isLocal_ringHomProperty : RingHom.命题ertyIsLocal Q
    - eq_affineLocally' : P = affineLocally Q
-/
class HasRingHomProperty (P : MorphismProperty Scheme.{u})
    (Q : outParam (forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop)) : Prop where
  isLocal_ringHomProperty : RingHom.PropertyIsLocal Q
  eq_affineLocally' : P = affineLocally Q

namespace HasRingHomProperty

variable (P : MorphismProperty Scheme.{u}) {Q} [HasRingHomProperty P Q]
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/--
lemma `copy` / 引理 `copy`

English:
lemma copy
  statement: {P' : MorphismProperty Scheme.{u}}
  proof: by
  subst e
  have heq : @Q = @Q' := by
    ext R S _ _ f
    exact (e' f)
  rw [← heq]
  infer_instance

中文:
引理 copy
  结论: {P' : Morphism命题erty Scheme.{u}}
  证明: by
  subst e
  have heq : @Q = @Q' := by
    ext R S _ _ f
    exact (e' f)
  rw [← heq]
  infer_instance

Depends on / 依赖: infer_instance
-/
lemma copy {P' : MorphismProperty Scheme.{u}}
    {Q' : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}
    (e : P = P') (e' : forall {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S), Q f ↔ Q' f) :
    HasRingHomProperty P' Q' := by
  subst e
  have heq : @Q = @Q' := by
    ext R S _ _ f
    exact (e' f)
  rw [← heq]
  infer_instance

/--
lemma `eq_affineLocally` / 引理 `eq_affineLocally`

English:
lemma eq_affineLocally
  statement: P = affineLocally Q
  proof: eq_affineLocally'

@[local instance]

中文:
引理 eq_affineLocally
  结论: P = affineLocally Q
  证明: eq_affineLocally'

@[local instance]

Depends on / 依赖: eq_affineLocally
-/
lemma eq_affineLocally : P = affineLocally Q := eq_affineLocally'

@[local instance]
/--
lemma `HasAffineProperty` / 引理 `HasAffineProperty`

English:
lemma HasAffineProperty
  statement: HasAffineProperty P (sourceAffineLocally Q) where
  proof: sourceAffineLocally_isLocal _
    (isLocal_ringHomProperty P).respectsIso
    (isLocal_ringHomProperty P).localizationAwayPreserves
    (isLocal_ringHomProperty P).ofLocalizationSpan
  eq_targetAffineLocally' := eq_affineLocally P

中文:
引理 HasAffineProperty
  结论: HasAffine命题erty P (sourceAffineLocally Q) where
  证明: sourceAffineLocally_isLocal _
    (isLocal_ringHomProperty P).respectsIso
    (isLocal_ringHomProperty P).localizationAwayPreserves
    (isLocal_ringHomProperty P).ofLocalizationSpan
  eq_targetAffineLocally' := eq_affineLocally P

Depends on / 依赖: sourceAffineLocally_isLocal
-/
lemma HasAffineProperty : HasAffineProperty P (sourceAffineLocally Q) where
  isLocal_affineProperty := sourceAffineLocally_isLocal _
    (isLocal_ringHomProperty P).respectsIso
    (isLocal_ringHomProperty P).localizationAwayPreserves
    (isLocal_ringHomProperty P).ofLocalizationSpan
  eq_targetAffineLocally' := eq_affineLocally P

/-- This is only `inferInstance` because of the `@[local instance]` on `HasAffineProperty` above. -/
instance (priority := 900) : IsZariskiLocalAtTarget P := inferInstance

/--
theorem `appLE` / 定理 `appLE`

English:
theorem appLE
  given: (H : P f) (U : Y.affineOpens) (V : X.affineOpens) (e)
  statement: Q (f.appLE U V e).hom
  proof: by
  rw [eq_affineLocally P]; rw [affineLocally_iff_affineOpens_le] at H
  exact H _ _ _

中文:
定理 appLE
  条件: (H : P f) (U : Y.affineOpens) (V : X.affineOpens) (e)
  结论: Q (f.appLE U V e).hom
  证明: by
  rw [eq_affineLocally P]; rw [affineLocally_iff_affineOpens_le] at H
  exact H _ _ _

Depends on / 依赖: affineLocally_iff_affineOpens_le, eq_affineLocally
-/
theorem appLE (H : P f) (U : Y.affineOpens) (V : X.affineOpens) (e) : Q (f.appLE U V e).hom := by
  rw [eq_affineLocally P]; rw [affineLocally_iff_affineOpens_le] at H
  exact H _ _ _

/--
theorem `appTop` / 定理 `appTop`

English:
theorem appTop
  given: (H : P f) [IsAffine X] [IsAffine Y]
  statement: Q f.appTop.hom
  proof: by
  rw [Scheme.Hom.appTop]; rw [Scheme.Hom.app_eq_appLE]
  exact appLE P f H ⟨_, isAffineOpen_top _⟩ ⟨_, isAffineOpen_top _⟩ _

include Q in

中文:
定理 appTop
  条件: (H : P f) [IsAffine X] [IsAffine Y]
  结论: Q f.appTop.hom
  证明: by
  rw [Scheme.Hom.appTop]; rw [Scheme.Hom.app_eq_appLE]
  exact appLE P f H ⟨_, isAffineOpen_top _⟩ ⟨_, isAffineOpen_top _⟩ _

include Q in

Depends on / 依赖: Scheme, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, appTop, app_eq_appLE, isAffineOpen_top
-/
theorem appTop (H : P f) [IsAffine X] [IsAffine Y] : Q f.appTop.hom := by
  rw [Scheme.Hom.appTop]; rw [Scheme.Hom.app_eq_appLE]
  exact appLE P f H ⟨_, isAffineOpen_top _⟩ ⟨_, isAffineOpen_top _⟩ _

include Q in
/--
theorem `comp_of_isOpenImmersion` / 定理 `comp_of_isOpenImmersion`

English:
theorem comp_of_isOpenImmersion
  given: [IsOpenImmersion f] (H : P g)
  proof: by
  rw [eq_affineLocally P]; rw [affineLocally_iff_affineOpens_le] at H ⊢
  intro U V e
  have : IsIso (f.appLE (f ''ᵁ V) V.1 (f.preimage_image_eq _).ge) :=
    inferInstanceAs (IsIso (f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq _).symm).op))
  rw [← Scheme.Hom.appLE_comp_appLE _ _

中文:
定理 comp_of_isOpenImmersion
  条件: [IsOpenImmersion f] (H : P g)
  证明: by
  rw [eq_affineLocally P]; rw [affineLocally_iff_affineOpens_le] at H ⊢
  intro U V e
  have : IsIso (f.appLE (f ''ᵁ V) V.1 (f.preimage_image_eq _).ge) :=
    inferInstanceAs (IsIso (f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq _).symm).op))
  rw [← Scheme.Hom.appLE_comp_appLE _ _

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, Scheme, Scheme.Hom.appLE_comp_appLE, Set.image_subset_iff.mpr, X.presheaf.map, affineLocally_iff_affineOpens_le, appLE_comp_appLE, cancel_right_isIso, eqToHom, eq_affineLocally, f.app, f.appLE, f.preimage_image_eq, hom_comp, image_of_isOpenImmersion, image_subset_iff, isLocal_ringHomProperty, preimage_image_eq, presheaf
-/
theorem comp_of_isOpenImmersion [IsOpenImmersion f] (H : P g) :
    P (f ≫ g) := by
  rw [eq_affineLocally P]; rw [affineLocally_iff_affineOpens_le] at H ⊢
  intro U V e
  have : IsIso (f.appLE (f ''ᵁ V) V.1 (f.preimage_image_eq _).ge) :=
    inferInstanceAs (IsIso (f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq _).symm).op))
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ (f ''ᵁ V) V.1
    (Set.image_subset_iff.mpr e) (f.preimage_image_eq _).ge]; rw [CommRingCat.hom_comp]; rw [(isLocal_ringHomProperty P).respectsIso.cancel_right_isIso]
  exact H _ ⟨_, V.2.image_of_isOpenImmersion _⟩ _

variable {P f}

/--
lemma `iff_appLE` / 引理 `iff_appLE`

English:
lemma iff_appLE
  statement: P f ↔ forall (U : Y.affineOpens) (V : X.affineOpens) (e), Q (f.appLE U V e).hom
  proof: by
  rw [eq_affineLocally P]; rw [affineLocally_iff_affineOpens_le]

中文:
引理 iff_appLE
  结论: P f ↔ 对任意 (U : Y.affineOpens) (V : X.affineOpens) (e), Q (f.appLE U V e).hom
  证明: by
  rw [eq_affineLocally P]; rw [affineLocally_iff_affineOpens_le]

Depends on / 依赖: affineLocally_iff_affineOpens_le, eq_affineLocally
-/
lemma iff_appLE : P f ↔ forall (U : Y.affineOpens) (V : X.affineOpens) (e), Q (f.appLE U V e).hom := by
  rw [eq_affineLocally P]; rw [affineLocally_iff_affineOpens_le]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `of_source_openCover` / 定理 `of_source_openCover`

English:
theorem of_source_openCover
  statement: [IsAffine Y]
  proof: by
  rw [HasAffineProperty.iff_of_isAffine (P := P)]
  intro U
  let S i : X.affineOpens := ⟨_, isAffineOpen_opensRange (𝒰.f i)⟩
  induction U using of_affine_open_cover S 𝒰.iSup_opensRange with
  | basicOpen U r H =>
    simp_rw [Scheme.affineBasicOpen_coe,
      ← f.appLE_map (U := ⊤) le_top (homO

中文:
定理 of_source_openCover
  结论: [IsAffine Y]
  证明: by
  rw [HasAffineProperty.iff_of_isAffine (P := P)]
  intro U
  let S i : X.affineOpens := ⟨_, isAffineOpen_opensRange (𝒰.f i)⟩
  induction U using of_affine_open_cover S 𝒰.iSup_opensRange with
  | basicOpen U r H =>
    simp_rw [Scheme.affineBasicOpen_coe,
      ← f.appLE_map (U := ⊤) le_top (homO

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, Scheme, Scheme.affineBasicOpen_coe, StableUnderCompositionWithLocalizationAwayTarget, X.affineOpens, X.basicOpen_le, affineBasicOpen_coe, affineOpens, appLE_map, basicOpen, basicOpen_le, f.appLE_map, homOfLE, iSup_opensRange, iff_of_isAffine, isAffineOpen_opensRange, isLocal_ringHomProperty, isLocalization_basicOpen, le_top
-/
theorem of_source_openCover [IsAffine Y]
    (𝒰 : X.OpenCover) [forall i, IsAffine (𝒰.X i)] (H : forall i, Q ((𝒰.f i ≫ f).appTop.hom)) :
    P f := by
  rw [HasAffineProperty.iff_of_isAffine (P := P)]
  intro U
  let S i : X.affineOpens := ⟨_, isAffineOpen_opensRange (𝒰.f i)⟩
  induction U using of_affine_open_cover S 𝒰.iSup_opensRange with
  | basicOpen U r H =>
    simp_rw [Scheme.affineBasicOpen_coe,
      ← f.appLE_map (U := ⊤) le_top (homOfLE (X.basicOpen_le r)).op]
    have := U.2.isLocalization_basicOpen r
    exact (isLocal_ringHomProperty P).StableUnderCompositionWithLocalizationAwayTarget _ r _ H
  | openCover U s hs H =>
    apply (isLocal_ringHomProperty P).ofLocalizationSpanTarget.ofIsLocalization
      (isLocal_ringHomProperty P).respectsIso _ _ hs
    rintro r
    refine ⟨_, _, _, IsAffineOpen.isLocalization_basicOpen U.2 r, ?_⟩
    rw [RingHom.algebraMap_toAlgebra]; rw [← CommRingCat.hom_comp]; rw [Scheme.Hom.appLE_map]
    exact H r
  | hU i =>
    specialize H i
    rw [← (isLocal_ringHomProperty P).respectsIso.cancel_right_isIso _
      ((IsOpenImmersion.isoOfRangeEq (𝒰.f i) (S i).1.ι
      Subtype.range_coe.symm).inv.app _)]; rw [← CommRingCat.hom_comp]; rw [← Scheme.Hom.comp_appTop]; rw [IsOpenImmersion.isoOfRangeEq_inv_fac_assoc]; rw [Scheme.Hom.comp_appTop]; rw [Scheme.Opens.ι_appTop]; rw [Scheme.Hom.appTop]; rw [Scheme.Hom.app_eq_appLE]; rw [Scheme.Hom.appLE_map] at H
    exact (f.appLE_congr _ rfl (by simp) (fun f => Q f.hom)).mp H

/--
theorem `iff_of_source_openCover` / 定理 `iff_of_source_openCover`

English:
theorem iff_of_source_openCover
  given: [IsAffine Y] (𝒰 : X.OpenCover) [forall i, IsAffine (𝒰.X i)]
  proof: ⟨fun H i => appTop P _ (comp_of_isOpenImmersion P (𝒰.f i) f H), of_source_openCover 𝒰⟩

中文:
定理 iff_of_source_openCover
  条件: [IsAffine Y] (𝒰 : X.OpenCover) [对任意 i, IsAffine (𝒰.X i)]
  证明: ⟨fun H i => appTop P _ (comp_of_isOpenImmersion P (𝒰.f i) f H), of_source_openCover 𝒰⟩

Depends on / 依赖: appTop, comp_of_isOpenImmersion, of_source_openCover
-/
theorem iff_of_source_openCover [IsAffine Y] (𝒰 : X.OpenCover) [forall i, IsAffine (𝒰.X i)] :
    P f ↔ forall i, Q ((𝒰.f i ≫ f).appTop).hom :=
  ⟨fun H i => appTop P _ (comp_of_isOpenImmersion P (𝒰.f i) f H), of_source_openCover 𝒰⟩

set_option backward.defeqAttrib.useBackward true in
/--
theorem `iff_of_isAffine` / 定理 `iff_of_isAffine`

English:
theorem iff_of_isAffine
  given: [IsAffine X] [IsAffine Y]
  proof: by
  rw [iff_of_source_openCover (P := P) (Scheme.coverOfIsIso.{u} (𝟙 _))]
  simp +instances

中文:
定理 iff_of_isAffine
  条件: [IsAffine X] [IsAffine Y]
  证明: by
  rw [iff_of_source_openCover (P := P) (Scheme.coverOfIsIso.{u} (𝟙 _))]
  simp +instances

Depends on / 依赖: Scheme, Scheme.coverOfIsIso, coverOfIsIso, iff_of_source_openCover, instances
-/
theorem iff_of_isAffine [IsAffine X] [IsAffine Y] :
    P f ↔ Q (f.appTop).hom := by
  rw [iff_of_source_openCover (P := P) (Scheme.coverOfIsIso.{u} (𝟙 _))]
  simp +instances

/--
theorem `Spec_iff` / 定理 `Spec_iff`

English:
theorem Spec_iff
  given: {R S : CommRingCat.{u}} {φ : R ⟶ S}
  proof: by
  have H := (isLocal_ringHomProperty P).respectsIso
  rw [iff_of_isAffine (P := P)]; rw [← H.cancel_right_isIso _ (Scheme.ΓSpecIso _).hom]; rw [← CommRingCat.hom_comp]; rw [Scheme.ΓSpecIso_naturality]; rw [CommRingCat.hom_comp]; rw [H.cancel_left_isIso]

中文:
定理 Spec_iff
  条件: {R S : CommRingCat.{u}} {φ : R ⟶ S}
  证明: by
  have H := (isLocal_ringHomProperty P).respectsIso
  rw [iff_of_isAffine (P := P)]; rw [← H.cancel_right_isIso _ (Scheme.ΓSpecIso _).hom]; rw [← CommRingCat.hom_comp]; rw [Scheme.ΓSpecIso_naturality]; rw [CommRingCat.hom_comp]; rw [H.cancel_left_isIso]

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, H.cancel_left_isIso, H.cancel_right_isIso, NatIso, NatIso.ofComponents, Nonsingular, Nonsingular.iso, Scheme, Subcomplex, cancel_left_isIso, cancel_mono, cancel_right_isIso, hom_comp, iff_of_isAffine, isLocal_ringHomProperty, nonDegenerate, ofComponents, respectsIso, x.nonDegenerate
-/
theorem Spec_iff {R S : CommRingCat.{u}} {φ : R ⟶ S} :
    P (Spec.map φ) ↔ Q φ.hom := by
  have H := (isLocal_ringHomProperty P).respectsIso
  rw [iff_of_isAffine (P := P)]; rw [← H.cancel_right_isIso _ (Scheme.ΓSpecIso _).hom]; rw [← CommRingCat.hom_comp]; rw [Scheme.ΓSpecIso_naturality]; rw [CommRingCat.hom_comp]; rw [H.cancel_left_isIso]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `of_iSup_eq_top` / 定理 `of_iSup_eq_top`

English:
theorem of_iSup_eq_top
  statement: [IsAffine Y] {ι : Type*}
  proof: by
  have (i : _) : IsAffine ((X.openCoverOfIsOpenCover _ hU).X i) := (U i).2
  refine of_source_openCover (X.openCoverOfIsOpenCover _ hU) fun i => ?_
  simpa [Scheme.Hom.app_eq_appLE] using (f.appLE_congr _ rfl (by simp) (fun f => Q f.hom)).mp (H i)

中文:
定理 of_iSup_eq_top
  结论: [IsAffine Y] {ι : 类型}
  证明: by
  have (i : _) : IsAffine ((X.openCoverOfIsOpenCover _ hU).X i) := (U i).2
  refine of_source_openCover (X.openCoverOfIsOpenCover _ hU) fun i => ?_
  simpa [Scheme.Hom.app_eq_appLE] using (f.appLE_congr _ rfl (by simp) (fun f => Q f.hom)).mp (H i)

Depends on / 依赖: IsAffine, Scheme, Scheme.Hom.app_eq_appLE, X.openCoverOfIsOpenCover, appLE_congr, app_eq_appLE, f.appLE_congr, f.hom, of_source_openCover, openCoverOfIsOpenCover
-/
theorem of_iSup_eq_top [IsAffine Y] {ι : Type*}
    (U : ι -> X.affineOpens) (hU : ⨆ i, (U i : Opens X) = ⊤)
    (H : forall i, Q (f.appLE ⊤ (U i).1 le_top).hom) :
    P f := by
  have (i : _) : IsAffine ((X.openCoverOfIsOpenCover _ hU).X i) := (U i).2
  refine of_source_openCover (X.openCoverOfIsOpenCover _ hU) fun i => ?_
  simpa [Scheme.Hom.app_eq_appLE] using (f.appLE_congr _ rfl (by simp) (fun f => Q f.hom)).mp (H i)

/--
theorem `iff_of_iSup_eq_top` / 定理 `iff_of_iSup_eq_top`

English:
theorem iff_of_iSup_eq_top
  statement: [IsAffine Y] {ι : Type*}
  proof: ⟨fun H _ => appLE P f H ⟨_, isAffineOpen_top _⟩ _ le_top, of_iSup_eq_top U hU⟩

中文:
定理 iff_of_iSup_eq_top
  结论: [IsAffine Y] {ι : 类型}
  证明: ⟨fun H _ => appLE P f H ⟨_, isAffineOpen_top _⟩ _ le_top, of_iSup_eq_top U hU⟩

Depends on / 依赖: isAffineOpen_top, le_top, of_iSup_eq_top
-/
theorem iff_of_iSup_eq_top [IsAffine Y] {ι : Type*}
    (U : ι -> X.affineOpens) (hU : ⨆ i, (U i : Opens X) = ⊤) :
    P f ↔ forall i, Q (f.appLE ⊤ (U i).1 le_top).hom :=
  ⟨fun H _ => appLE P f H ⟨_, isAffineOpen_top _⟩ _ le_top, of_iSup_eq_top U hU⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtSource P
  body: by
  apply HasAffineProperty.isZariskiLocalAtSource
  intro X Y f _ 𝒰
  simp_rw [← HasAffineProperty.iff_of_isAffine (P := P),
    iff_of_source_openCover 𝒰.affineRefinement.openCover,
    fun i => iff_of_source_openCover (P := P) (f := 𝒰.f i ≫ f) (𝒰.X i).affineCover]
  simp [Scheme.OpenCover.affine

中文:
实例 :
  签名: IsZariskiLocalAtSource P
  定义体: by
  apply HasAffineProperty.isZariskiLocalAtSource
  intro X Y f _ 𝒰
  simp_rw [← HasAffineProperty.iff_of_isAffine (P := P),
    iff_of_source_openCover 𝒰.affineRefinement.openCover,
    fun i => iff_of_source_openCover (P := P) (f := 𝒰.f i ≫ f) (𝒰.X i).affineCover]
  simp [Scheme.OpenCover.affine

Depends on / 依赖: HasAffineProperty, HasAffineProperty.iff_of_isAffine, HasAffineProperty.isZariskiLocalAtSource, OpenCover, Scheme, Scheme.OpenCover.affineRefinement, Sigma.forall, affineCover, affineRefinement, affineRefinement.openCover, iff_of_isAffine, iff_of_source_openCover, isZariskiLocalAtSource, openCover, simp_rw
-/
instance : IsZariskiLocalAtSource P := by
  apply HasAffineProperty.isZariskiLocalAtSource
  intro X Y f _ 𝒰
  simp_rw [← HasAffineProperty.iff_of_isAffine (P := P),
    iff_of_source_openCover 𝒰.affineRefinement.openCover,
    fun i => iff_of_source_openCover (P := P) (f := 𝒰.f i ≫ f) (𝒰.X i).affineCover]
  simp [Scheme.OpenCover.affineRefinement, Sigma.forall]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `containsIdentities` / 引理 `containsIdentities`

English:
lemma containsIdentities
  given: (hP : RingHom.ContainsIdentities Q)
  statement: P.ContainsIdentities where
  proof: by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro U
    have : IsAffine (𝟙 X ⁻¹ᵁ U.1) := U.2
    rw [morphismRestrict_id]; rw [iff_of_isAffine (P := P)]; rw [Scheme.Hom.id_appTop]
    apply hP

中文:
引理 containsIdentities
  条件: (hP : RingHom.ContainsIdentities Q)
  结论: P.ContainsIdentities where
  证明: by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro U
    have : IsAffine (𝟙 X ⁻¹ᵁ U.1) := U.2
    rw [morphismRestrict_id]; rw [iff_of_isAffine (P := P)]; rw [Scheme.Hom.id_appTop]
    apply hP

Depends on / 依赖: IsAffine, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_iSup_eq_top, Scheme, Scheme.Hom.id_appTop, iSup_affineOpens_eq_top, id_appTop, iff_of_iSup_eq_top, iff_of_isAffine, morphismRestrict_id
-/
lemma containsIdentities (hP : RingHom.ContainsIdentities Q) : P.ContainsIdentities where
  id_mem X := by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro U
    have : IsAffine (𝟙 X ⁻¹ᵁ U.1) := U.2
    rw [morphismRestrict_id]; rw [iff_of_isAffine (P := P)]; rw [Scheme.Hom.id_appTop]
    apply hP

set_option backward.isDefEq.respectTransparency false in
variable (P) in
open _root_.PrimeSpectrum in
/--
lemma `isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget` / 引理 `isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget`

English:
lemma isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget
  proof: by
  have hP : RingHom.RespectsIso (fun f => P (Spec.map (CommRingCat.ofHom f))) :=
    RingHom.toMorphismProperty_respectsIso_iff.mpr
      (inferInstanceAs (P.inverseImage Scheme.Spec).unop.RespectsIso)
  constructor
  · intro R S _ _ f r R' S' _ _ _ _ _ _ H
    refine (RingHom.RespectsIso.isLocal

中文:
引理 isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget
  证明: by
  have hP : RingHom.RespectsIso (fun f => P (Spec.map (CommRingCat.ofHom f))) :=
    RingHom.toMorphismProperty_respectsIso_iff.mpr
      (inferInstanceAs (P.inverseImage Scheme.Spec).unop.RespectsIso)
  constructor
  · intro R S _ _ f r R' S' _ _ _ _ _ _ H
    refine (RingHom.RespectsIso.isLocal

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsZarisk, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.restrict, MorphismProperty, MorphismProperty.arrow_mk_iso_iff, P.inverseImage, RespectsIso, RingHom, RingHom.RespectsIso, RingHom.RespectsIso.isLocalization_away_iff, RingHom.toMorphismProperty_respectsIso_iff.mpr, Scheme, Scheme.Spec, Spec.map, SpecMapRestrictBasicOpenIso, arrow_mk_iso_iff, basicOpen, inverseImage
-/
lemma isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget
    [IsZariskiLocalAtTarget P] [IsZariskiLocalAtSource P] :
    RingHom.PropertyIsLocal fun f => P (Spec.map (CommRingCat.ofHom f)) := by
  have hP : RingHom.RespectsIso (fun f => P (Spec.map (CommRingCat.ofHom f))) :=
    RingHom.toMorphismProperty_respectsIso_iff.mpr
      (inferInstanceAs (P.inverseImage Scheme.Spec).unop.RespectsIso)
  constructor
  · intro R S _ _ f r R' S' _ _ _ _ _ _ H
    refine (RingHom.RespectsIso.isLocalization_away_iff hP ..).mp ?_
    exact (MorphismProperty.arrow_mk_iso_iff P (SpecMapRestrictBasicOpenIso
      (CommRingCat.ofHom f) r)).mp (IsZariskiLocalAtTarget.restrict H (basicOpen r))
  · intro R S _ _ f s hs H
    apply IsZariskiLocalAtSource.of_openCover (Scheme.affineOpenCoverOfSpanRangeEqTop
      (fun i : s => (i : S)) (by simpa)).openCover
    intro i
    simp only [CommRingCat.coe_of, ← Spec.map_comp,
      Scheme.AffineOpenCover.openCover_f, Scheme.affineOpenCoverOfSpanRangeEqTop_f]
    exact H i
  · intro R S _ _ f s hs H
    apply IsZariskiLocalAtTarget.of_iSup_eq_top _ (PrimeSpectrum.iSup_basicOpen_eq_top_iff
      (f := fun i : s => (i : R)).mpr (by simpa))
    intro i
    exact (MorphismProperty.arrow_mk_iso_iff P (SpecMapRestrictBasicOpenIso
      (CommRingCat.ofHom f) i.1)).mpr (H i)
  · intro R S T _ _ _ _ r _ f hf
    have := AlgebraicGeometry.IsOpenImmersion.of_isLocalization (S := T) r
    change P (Spec.map (CommRingCat.ofHom f ≫ CommRingCat.ofHom (algebraMap _ _)))
    rw [Spec.map_comp]
    exact IsZariskiLocalAtSource.comp hf ..

open _root_.PrimeSpectrum in
variable (P) in
/--
lemma `of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget` / 引理 `of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget`

English:
lemma of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget
  statement: [IsZariskiLocalAtTarget P]
  proof: isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget P
  eq_affineLocally' := by
    let Q := affineLocally (fun f => P (Spec.map (CommRingCat.ofHom f)))
    have : HasRingHomProperty Q (fun f => P (Spec.map (CommRingCat.ofHom f))) :=
      ⟨isLocal_ringHomProperty_of_isZarisk

中文:
引理 of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget
  结论: [IsZariskiLocalAtTarget P]
  证明: isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget P
  eq_affineLocally' := by
    let Q := affineLocally (fun f => P (Spec.map (CommRingCat.ofHom f)))
    have : HasRingHomProperty Q (fun f => P (Spec.map (CommRingCat.ofHom f))) :=
      ⟨isLocal_ringHomProperty_of_isZarisk

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, HasRingHomProperty, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff, IsZariskiLocalAtTarget.iff_of_openCover, Spec.map, Y.affineCover, affineCover, affineLocally, eq_affineLocally, generalizing, iff_of_openCover, isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget
-/
lemma of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget [IsZariskiLocalAtTarget P]
    [IsZariskiLocalAtSource P] :
    HasRingHomProperty P (fun f => P (Spec.map (CommRingCat.ofHom f))) where
  isLocal_ringHomProperty :=
    isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget P
  eq_affineLocally' := by
    let Q := affineLocally (fun f => P (Spec.map (CommRingCat.ofHom f)))
    have : HasRingHomProperty Q (fun f => P (Spec.map (CommRingCat.ofHom f))) :=
      ⟨isLocal_ringHomProperty_of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget P, rfl⟩
    change P = Q
    ext X Y f
    wlog hY : exists R, Y = Spec R generalizing X Y
    · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) Y.affineCover,
        IsZariskiLocalAtTarget.iff_of_openCover (P := Q) Y.affineCover]
      refine forall_congr' fun _ => this _ ⟨_, rfl⟩
    obtain ⟨S, rfl⟩ := hY
    wlog hX : exists R, X = Spec R generalizing X
    · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) X.affineCover,
        IsZariskiLocalAtSource.iff_of_openCover (P := Q) X.affineCover]
      refine forall_congr' fun _ => this _ ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hX
    obtain ⟨φ, rfl⟩ : exists φ, Spec.map φ = f := ⟨_, Spec.map_preimage _⟩
    rw [HasRingHomProperty.Spec_iff (P := Q)]
    rfl

/--
lemma `inf` / 引理 `inf`

English:
lemma inf
  statement: {P P' : MorphismProperty Scheme.{u}}
  proof: .and (HasRingHomProperty.isLocal_ringHomProperty P)
      (HasRingHomProperty.isLocal_ringHomProperty P')
  eq_affineLocally' := by
    rw [HasRingHomProperty.eq_affineLocally P]; rw [HasRingHomProperty.eq_affineLocally P']
    ext
    change _ ∧ _ ↔ _
    simp_rw [affineLocally_iff_affineOpens_le]


中文:
引理 inf
  结论: {P P' : Morphism命题erty Scheme.{u}}
  证明: .and (HasRingHomProperty.isLocal_ringHomProperty P)
      (HasRingHomProperty.isLocal_ringHomProperty P')
  eq_affineLocally' := by
    rw [HasRingHomProperty.eq_affineLocally P]; rw [HasRingHomProperty.eq_affineLocally P']
    ext
    change _ ∧ _ ↔ _
    simp_rw [affineLocally_iff_affineOpens_le]


Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.eq_affineLocally, HasRingHomProperty.isLocal_ringHomProperty, affineLocally_iff_affineOpens_le, eq_affineLocally, isLocal_ringHomProperty, simp_rw
-/
lemma inf {P P' : MorphismProperty Scheme.{u}}
    {Q Q' : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}
    [HasRingHomProperty P Q] [HasRingHomProperty P' Q'] :
    HasRingHomProperty (P ⊓ P') (fun f => Q f ∧ Q' f) where
  isLocal_ringHomProperty :=
    .and (HasRingHomProperty.isLocal_ringHomProperty P)
      (HasRingHomProperty.isLocal_ringHomProperty P')
  eq_affineLocally' := by
    rw [HasRingHomProperty.eq_affineLocally P]; rw [HasRingHomProperty.eq_affineLocally P']
    ext
    change _ ∧ _ ↔ _
    simp_rw [affineLocally_iff_affineOpens_le]
    grind

/--
lemma `stalkwise` / 引理 `stalkwise`

English:
lemma stalkwise
  given: {P} (hP : RingHom.RespectsIso P)
  proof: by
  have := stalkwiseIsZariskiLocalAtTarget_of_respectsIso hP
  have := stalkwise_isZariskiLocalAtSource_of_respectsIso hP
  convert!
    of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget (P := AlgebraicGeometry.stalkwise P) with R
    S _ _ φ
  exact (stalkwise_SpecMap_iff hP (CommRingCat.ofHom 

中文:
引理 stalkwise
  条件: {P} (hP : RingHom.RespectsIso P)
  证明: by
  have := stalkwiseIsZariskiLocalAtTarget_of_respectsIso hP
  have := stalkwise_isZariskiLocalAtSource_of_respectsIso hP
  convert!
    of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget (P := AlgebraicGeometry.stalkwise P) with R
    S _ _ φ
  exact (stalkwise_SpecMap_iff hP (CommRingCat.ofHom 

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.stalkwise, CommRingCat, CommRingCat.ofHom, convert, of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget, stalkwise, stalkwiseIsZariskiLocalAtTarget_of_respectsIso, stalkwise_SpecMap_iff, stalkwise_isZariskiLocalAtSource_of_respectsIso
-/
lemma stalkwise {P} (hP : RingHom.RespectsIso P) :
    HasRingHomProperty (stalkwise P) fun {_ S _ _} φ =>
      forall (p : Ideal S) (_ : p.IsPrime), P (Localization.localRingHom _ p φ rfl) := by
  have := stalkwiseIsZariskiLocalAtTarget_of_respectsIso hP
  have := stalkwise_isZariskiLocalAtSource_of_respectsIso hP
  convert!
    of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget (P := AlgebraicGeometry.stalkwise P) with R
    S _ _ φ
  exact (stalkwise_SpecMap_iff hP (CommRingCat.ofHom φ)).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `stableUnderComposition` / 引理 `stableUnderComposition`

English:
lemma stableUnderComposition
  given: (hP : RingHom.StableUnderComposition Q)
  proof: by
    wlog hZ : IsAffine Z generalizing X Y Z
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
      intro U
      rw [morphismRestrict_comp]
      exact this _ _ (IsZariskiLocalAtTarget.restrict hf _)
        (IsZariskiLocalAtTarget.restrict hg _) U.2
   

中文:
引理 stableUnderComposition
  条件: (hP : RingHom.StableUnderComposition Q)
  证明: by
    wlog hZ : IsAffine Z generalizing X Y Z
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
      intro U
      rw [morphismRestrict_comp]
      exact this _ _ (IsZariskiLocalAtTarget.restrict hf _)
        (IsZariskiLocalAtTarget.restrict hg _) U.2
   

Depends on / 依赖: IsAffine, IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff_of_openCover, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_iSup_eq_top, IsZariskiLocalAtTarget.of_isPullback, IsZariskiLocalAtTarget.restrict, Scheme, Scheme.Cover.pullbackHom_map_assoc, Y.affineCover.pullback, affineCover, generalizing, iSup_affineOpens_eq_top, iff_of_iSup_eq_top, iff_of_openCover, morphismRestrict_comp, of_hasPull, of_isPullback, pullbackHom_map_assoc, restrict
-/
lemma stableUnderComposition (hP : RingHom.StableUnderComposition Q) :
    P.IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    wlog hZ : IsAffine Z generalizing X Y Z
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
      intro U
      rw [morphismRestrict_comp]
      exact this _ _ (IsZariskiLocalAtTarget.restrict hf _)
        (IsZariskiLocalAtTarget.restrict hg _) U.2
    wlog hY : IsAffine Y generalizing X Y
    · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (Y.affineCover.pullback₁ f)]
      intro i
      rw [← Scheme.Cover.pullbackHom_map_assoc]
      exact this _ _ (IsZariskiLocalAtTarget.of_isPullback (.of_hasPullback _ _) hf)
        (comp_of_isOpenImmersion _ _ _ hg) inferInstance
    wlog hX : IsAffine X generalizing X
    · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) X.affineCover]
      intro i
      rw [← Category.assoc]
      exact this _ (comp_of_isOpenImmersion _ _ _ hf) inferInstance
    rw [iff_of_isAffine (P := P)] at hf hg ⊢
    exact hP _ _ hg hf

/--
theorem `of_comp` / 定理 `of_comp`

English:
theorem of_comp
  proof: by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    exact this H inferInstance
  w

中文:
定理 of_comp
  证明: by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    exact this H inferInstance
  w

Depends on / 依赖: IsAffine, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_iSup_eq_top, IsZariskiLocalAtTarget.restrict, comp_of_isOpenImmersion, g.iSup_preimage_eq_top, generalizing, iSup_affineOpens_eq_top, iSup_preimage_eq_top, iff_of_iSup_eq_top, morphismRestrict_comp, restrict
-/
theorem of_comp
    (H : forall {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      forall (f : R ->+* S) (g : S ->+* T), Q (g.comp f) -> Q g)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (h : P (f ≫ g)) : P f := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    exact this H inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top Y)]
    intro U
    have H := comp_of_isOpenImmersion P (f ⁻¹ᵁ U.1).ι (f ≫ g) h
    rw [← morphismRestrict_ι_assoc] at H
    exact this H inferInstance
  wlog hY : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top X)]
    intro U
    have H := comp_of_isOpenImmersion P U.1.ι (f ≫ g) h
    rw [← Category.assoc] at H
    exact this H inferInstance
  rw [iff_of_isAffine (P := P)] at h ⊢
  exact H _ _ h

/--
lemma `isMultiplicative` / 引理 `isMultiplicative`

English:
lemma isMultiplicative
  statement: (hPc : RingHom.StableUnderComposition Q)
  proof: (stableUnderComposition hPc).comp_mem
  id_mem := (containsIdentities hPi).id_mem

include Q in

中文:
引理 isMultiplicative
  结论: (hPc : RingHom.StableUnderComposition Q)
  证明: (stableUnderComposition hPc).comp_mem
  id_mem := (containsIdentities hPi).id_mem

include Q in

Depends on / 依赖: comp_mem, stableUnderComposition
-/
lemma isMultiplicative (hPc : RingHom.StableUnderComposition Q)
    (hPi : RingHom.ContainsIdentities Q) :
    P.IsMultiplicative where
  comp_mem := (stableUnderComposition hPc).comp_mem
  id_mem := (containsIdentities hPi).id_mem

include Q in
/--
lemma `of_isOpenImmersion` / 引理 `of_isOpenImmersion`

English:
lemma of_isOpenImmersion
  given: (hP : RingHom.ContainsIdentities Q) [IsOpenImmersion f]
  statement: P f
  proof: haveI : P.ContainsIdentities := containsIdentities hP
  IsZariskiLocalAtSource.of_isOpenImmersion f

中文:
引理 of_isOpenImmersion
  条件: (hP : RingHom.ContainsIdentities Q) [IsOpenImmersion f]
  结论: P f
  证明: haveI : P.ContainsIdentities := containsIdentities hP
  IsZariskiLocalAtSource.of_isOpenImmersion f

Depends on / 依赖: ContainsIdentities, IsZariskiLocalAtSource, IsZariskiLocalAtSource.of_isOpenImmersion, P.ContainsIdentities, containsIdentities, of_isOpenImmersion
-/
lemma of_isOpenImmersion (hP : RingHom.ContainsIdentities Q) [IsOpenImmersion f] : P f :=
  haveI : P.ContainsIdentities := containsIdentities hP
  IsZariskiLocalAtSource.of_isOpenImmersion f

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isStableUnderBaseChange` / 引理 `isStableUnderBaseChange`

English:
lemma isStableUnderBaseChange
  given: (hP : RingHom.IsStableUnderBaseChange Q)
  proof: by
  apply HasAffineProperty.isStableUnderBaseChange
  let := HasAffineProperty.isLocal_affineProperty P
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g H
  rw [← HasAffineProperty.iff_of_isAffine (P := P)] at H ⊢
  wlog hX : IsAffine Y generalizing Y
  · rw [Is

中文:
引理 isStableUnderBaseChange
  条件: (hP : RingHom.IsStableUnderBaseChange Q)
  证明: by
  apply HasAffineProperty.isStableUnderBaseChange
  let := HasAffineProperty.isLocal_affineProperty P
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g H
  rw [← HasAffineProperty.iff_of_isAffine (P := P)] at H ⊢
  wlog hX : IsAffine Y generalizing Y
  · rw [Is

Depends on / 依赖: AffineTargetMorphismProperty, AffineTargetMorphismProperty.IsStableUnderBaseChange.mk, Category, Category.comp_id, HasAffineProperty, HasAffineProperty.iff_of_isAffine, HasAffineProperty.isLocal_affineProperty, HasAffineProperty.isStableUnderBaseChange, IsAffine, IsStableUnderBaseChange, IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff_of_openCover, Pullback, PullbackCone, PullbackCone.mk_, Scheme, Scheme.Pullback.openCoverOfRight, Scheme.Pullback.openCoverOfRight_f, Y.affineCover, affineCover
-/
lemma isStableUnderBaseChange (hP : RingHom.IsStableUnderBaseChange Q) :
    P.IsStableUnderBaseChange := by
  apply HasAffineProperty.isStableUnderBaseChange
  let := HasAffineProperty.isLocal_affineProperty P
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g H
  rw [← HasAffineProperty.iff_of_isAffine (P := P)] at H ⊢
  wlog hX : IsAffine Y generalizing Y
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := P)
      (Scheme.Pullback.openCoverOfRight Y.affineCover f g)]
    intro i
    simp only [Scheme.Pullback.openCoverOfRight_f, limit.lift_π, PullbackCone.mk_π_app,
      Category.comp_id]
    apply this _ (comp_of_isOpenImmersion _ _ _ H) inferInstance
  rw [iff_of_isAffine (P := P)] at H ⊢
  exact hP.pullback_fst_appTop _ (isLocal_ringHomProperty P).respectsIso _ _ H

include Q in
/--
lemma `respects_isOpenImmersion_aux` / 引理 `respects_isOpenImmersion_aux`

English:
lemma respects_isOpenImmersion_aux
  proof: by
  wlog hYa : exists (a : Γ(Y, ⊤)), U = Y.basicOpen a generalizing X Y
  · obtain ⟨(Us : Set Y.Opens), hUs, heq⟩ := Opens.isBasis_iff_cover.mp (isBasis_basicOpen Y) U
    let V (s : Us) : X.Opens := f ⁻¹ᵁ U.ι ⁻¹ᵁ s
    rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) V]
    · intro s
      l

中文:
引理 respects_isOpenImmersion_aux
  证明: by
  wlog hYa : exists (a : Γ(Y, ⊤)), U = Y.basicOpen a generalizing X Y
  · obtain ⟨(Us : Set Y.Opens), hUs, heq⟩ := Opens.isBasis_iff_cover.mp (isBasis_basicOpen Y) U
    let V (s : Us) : X.Opens := f ⁻¹ᵁ U.ι ⁻¹ᵁ s
    rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) V]
    · intro s
      l
-/
private lemma respects_isOpenImmersion_aux
    (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q)
    {X Y : Scheme.{u}} [IsAffine Y] {U : Y.Opens}
    (f : X ⟶ U.toScheme) (hf : P f) : P (f ≫ U.ι) := by
  wlog hYa : exists (a : Γ(Y, ⊤)), U = Y.basicOpen a generalizing X Y
  · obtain ⟨(Us : Set Y.Opens), hUs, heq⟩ := Opens.isBasis_iff_cover.mp (isBasis_basicOpen Y) U
    let V (s : Us) : X.Opens := f ⁻¹ᵁ U.ι ⁻¹ᵁ s
    rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) V]
    · intro s
      let f' : (V s).toScheme ⟶ U.ι ⁻¹ᵁ s := f ∣_ U.ι ⁻¹ᵁ s
      have hf' : P f' := IsZariskiLocalAtTarget.restrict hf _
      let e : (U.ι ⁻¹ᵁ s).toScheme ≅ s := IsOpenImmersion.isoOfRangeEq ((U.ι ⁻¹ᵁ s).ι ≫ U.ι) s.1.ι
        (by simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
          Opens.map_coe, Set.image_preimage_eq_iff, heq, Opens.coe_sSup] using! le_sSup s.2)
      have heq : (V s).ι ≫ f ≫ U.ι = f' ≫ e.hom ≫ s.1.ι := by
        simp only [V, IsOpenImmersion.isoOfRangeEq_hom_fac, f', e, morphismRestrict_ι_assoc]
      rw [heq]; rw [← Category.assoc]
      refine this _ ?_ ?_
      · rwa [P.cancel_right_of_respectsIso]
      · obtain ⟨a, ha⟩ := hUs s.2
        use a, ha.symm
    · apply f.iSup_preimage_eq_top
      apply U.ι.image_injective
      simp only [U.ι.image_iSup, U.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      conv_rhs => rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι, heq]
      ext : 1
      have (i : Us) : U ⊓ i.1 = i.1 := by simp [heq, le_sSup i.property]
      simp [this]
  obtain ⟨a, rfl⟩ := hYa
  wlog hX : IsAffine X generalizing X Y
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro V
    rw [← Category.assoc]
    exact this _ _ (IsZariskiLocalAtSource.comp hf _) V.2
  rw [HasRingHomProperty.iff_of_isAffine (P := P)] at hf ⊢
  exact hQ _ a _ hf

/--
lemma `respects_isOpenImmersion` / 引理 `respects_isOpenImmersion`

English:
lemma respects_isOpenImmersion
  given: (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q)
  proof: by
    wlog hZ : IsAffine Z generalizing X Y Z
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
      intro U
      rw [morphismRestrict_comp]
      exact this _ inferInstance _ (IsZariskiLocalAtTarget.restrict hf _) U.2
    let e : Y ≅ i.opensRange.toSchem

中文:
引理 respects_isOpenImmersion
  条件: (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q)
  证明: by
    wlog hZ : IsAffine Z generalizing X Y Z
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
      intro U
      rw [morphismRestrict_comp]
      exact this _ inferInstance _ (IsZariskiLocalAtTarget.restrict hf _) U.2
    let e : Y ≅ i.opensRange.toSchem

Depends on / 依赖: Category, Category.assoc, IsAffine, IsOpenImmersion, IsOpenImmersion.isoOfRangeEq, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_iSup_eq_top, IsZariskiLocalAtTarget.restrict, P.cancel_right_of_respectsIso, cancel_right_of_respectsIso, e.hom, generalizing, i.opensRange, i.opensRange.toScheme, iSup_affineOpens_eq_top, iff_of_iSup_eq_top, isoOfRangeEq, morphismRestrict_comp, opensRange, respects_isOpenImmersion_aux
-/
lemma respects_isOpenImmersion (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q) :
    P.Respects @IsOpenImmersion where
  postcomp {X Y Z} i hi f hf := by
    wlog hZ : IsAffine Z generalizing X Y Z
    · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
      intro U
      rw [morphismRestrict_comp]
      exact this _ inferInstance _ (IsZariskiLocalAtTarget.restrict hf _) U.2
    let e : Y ≅ i.opensRange.toScheme := IsOpenImmersion.isoOfRangeEq i i.opensRange.ι (by simp)
    rw [show f ≫ i = f ≫ e.hom ≫ i.opensRange.ι by simp [e], ← Category.assoc]
    exact respects_isOpenImmersion_aux hQ _ (by rwa [P.cancel_right_of_respectsIso])

open RingHom

omit [HasRingHomProperty P Q] in
/--
lemma `iff_exists_appLE_locally` / 引理 `iff_exists_appLE_locally`

English:
lemma iff_exists_appLE_locally
  proof: by
  have := respects_isOpenImmersion (P := P)
    (RingHom.locally_stableUnderCompositionWithLocalizationAwaySource hQ)
  refine ⟨fun hf x => ?_,
fun hf => (IsZariskiLocalAtSource.iff_exists_resLE (P := P)).mpr fun x => ?_⟩
  · obtain ⟨U, hU, hfx, _⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpe

中文:
引理 iff_exists_appLE_locally
  证明: by
  have := respects_isOpenImmersion (P := P)
    (RingHom.locally_stableUnderCompositionWithLocalizationAwaySource hQ)
  refine ⟨fun hf x => ?_,
fun hf => (IsZariskiLocalAtSource.iff_exists_resLE (P := P)).mpr fun x => ?_⟩
  · obtain ⟨U, hU, hfx, _⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpe

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.iff_appLE, IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff_exists_resLE, Opens.isBasis_iff_nbhd.mp, Opens.mem_top, RingHom, RingHom.locally_stableUnderCompositionWithLocalizationAwaySource, X.isBasis_affineOpens, Y.isBasis_affineOpens, iff_appLE, iff_exists_resLE, isBasis_affineOpens, isBasis_iff_nbhd, locally_iff_isLocalization, locally_stableUnderCompositionWithLocalizationAwaySource, mem_top, respects_isOpenImmersion, simp_rw
-/
lemma iff_exists_appLE_locally
    (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q)
    (hQi : RespectsIso Q) [HasRingHomProperty P (Locally Q)] :
    P f ↔ forall (x : X), exists (U : Y.affineOpens) (V : X.affineOpens) (_ : x in V.1) (e : V.1 <= f ⁻¹ᵁ U.1),
      Q (f.appLE U V e).hom := by
  have := respects_isOpenImmersion (P := P)
    (RingHom.locally_stableUnderCompositionWithLocalizationAwaySource hQ)
  refine ⟨fun hf x => ?_,
fun hf => (IsZariskiLocalAtSource.iff_exists_resLE (P := P)).mpr fun x => ?_⟩
  · obtain ⟨U, hU, hfx, _⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (Opens.mem_top <| f x)
    obtain ⟨V, hV, hx, e⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x in f ⁻¹ᵁ U from hfx)
    simp_rw [HasRingHomProperty.iff_appLE (P := P), locally_iff_isLocalization hQi] at hf
    obtain ⟨s, hs, hfs⟩ := hf ⟨U, hU⟩ ⟨V, hV⟩ e
    apply iSup_basicOpen_of_span_eq_top at hs
    have : x in (⨆ i in s, X.basicOpen i) := hs.symm ▸ hx
    have : exists r in s, x in X.basicOpen r := by simpa using this
    obtain ⟨r, hr, hrs⟩ := this
    refine ⟨⟨U, hU⟩, ⟨X.basicOpen r, hV.basicOpen r⟩, hrs, (X.basicOpen_le r).trans e, ?_⟩
    rw [← f.appLE_map e (homOfLE (X.basicOpen_le r)).op]
    have : IsLocalization.Away r Γ(X, X.basicOpen r) := hV.isLocalization_basicOpen r
    exact hfs r hr _
  · obtain ⟨U, V, hxV, e, hf⟩ := hf x
    use U, V, hxV, e
    simp only [iff_of_isAffine (P := P), Scheme.Hom.appLE, homOfLE_leOfHom] at hf ⊢
have : (toMorphismProperty (Locally Q)).RespectsIso := toMorphismProperty_respectsIso_iff.mp
      (isLocal_ringHomProperty P).respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff (toMorphismProperty (Locally Q))
      (arrowResLEAppIso f U V e)).mpr (locally_of hQi _ hf)

/--
lemma `iff_exists_appLE` / 引理 `iff_exists_appLE`

English:
lemma iff_exists_appLE
  proof: by
  have inst : HasRingHomProperty P Q := inferInstance
  have : HasRingHomProperty P (Locally Q) := by
    apply @copy (P := P) (P' := P) (Q := Q) (Q' := Locally Q)
    · infer_instance
    · rfl
    · intro R S _ _ f
      exact (locally_iff_of_localizationSpanTarget (isLocal_ringHomProperty P).r

中文:
引理 iff_exists_appLE
  证明: by
  have inst : HasRingHomProperty P Q := inferInstance
  have : HasRingHomProperty P (Locally Q) := by
    apply @copy (P := P) (P' := P) (Q := Q) (Q' := Locally Q)
    · infer_instance
    · rfl
    · intro R S _ _ f
      exact (locally_iff_of_localizationSpanTarget (isLocal_ringHomProperty P).r

Depends on / 依赖: HasRingHomProperty, Locally, iff_exists_appLE_locally, infer_instance, isLocal_ringHomProperty, locally_iff_of_localizationSpanTarget, ofLocalizationSpanTarget, respectsIso
-/
lemma iff_exists_appLE
    (hQ : StableUnderCompositionWithLocalizationAwaySource Q) : P f ↔
    forall (x : X), exists (U : Y.affineOpens) (V : X.affineOpens) (_ : x in V.1) (e : V.1 <= f ⁻¹ᵁ U.1),
      Q (f.appLE U V e).hom := by
  have inst : HasRingHomProperty P Q := inferInstance
  have : HasRingHomProperty P (Locally Q) := by
    apply @copy (P := P) (P' := P) (Q := Q) (Q' := Locally Q)
    · infer_instance
    · rfl
    · intro R S _ _ f
      exact (locally_iff_of_localizationSpanTarget (isLocal_ringHomProperty P).respectsIso
        (isLocal_ringHomProperty P).ofLocalizationSpanTarget _).symm
  rw [iff_exists_appLE_locally (P := P) hQ]
  have : HasRingHomProperty P Q := inst
  apply (isLocal_ringHomProperty P (Q := Q)).respectsIso

omit [HasRingHomProperty P Q] in
/--
lemma `locally_of_iff` / 引理 `locally_of_iff`

English:
lemma locally_of_iff
  statement: (hQl : LocalizationAwayPreserves Q)
  proof: locally_propertyIsLocal hQl hQa
  eq_affineLocally' := by
    have : HasRingHomProperty (affineLocally (Locally Q)) (Locally Q) :=
      ⟨locally_propertyIsLocal hQl hQa, rfl⟩
    ext X Y f
    rw [h]; rw [iff_exists_appLE_locally (P := affineLocally (Locally Q)) hQa.left hQa.respectsIso]

中文:
引理 locally_of_iff
  结论: (hQl : LocalizationAwayPreserves Q)
  证明: locally_propertyIsLocal hQl hQa
  eq_affineLocally' := by
    have : HasRingHomProperty (affineLocally (Locally Q)) (Locally Q) :=
      ⟨locally_propertyIsLocal hQl hQa, rfl⟩
    ext X Y f
    rw [h]; rw [iff_exists_appLE_locally (P := affineLocally (Locally Q)) hQa.left hQa.respectsIso]

Depends on / 依赖: locally_propertyIsLocal
-/
lemma locally_of_iff (hQl : LocalizationAwayPreserves Q)
    (hQa : StableUnderCompositionWithLocalizationAway Q)
    (h : forall {X Y : Scheme.{u}} (f : X ⟶ Y), P f ↔
      forall (x : X), exists (U : Y.affineOpens) (V : X.affineOpens) (_ : x in V.1) (e : V.1 <= f ⁻¹ᵁ U.1),
      Q (f.appLE U V e).hom) : HasRingHomProperty P (Locally Q) where
  isLocal_ringHomProperty := locally_propertyIsLocal hQl hQa
  eq_affineLocally' := by
    have : HasRingHomProperty (affineLocally (Locally Q)) (Locally Q) :=
      ⟨locally_propertyIsLocal hQl hQa, rfl⟩
    ext X Y f
    rw [h]; rw [iff_exists_appLE_locally (P := affineLocally (Locally Q)) hQa.left hQa.respectsIso]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `of_stalkMap` / 引理 `of_stalkMap`

English:
lemma of_stalkMap
  given: (hQ : OfLocalizationPrime Q) (H : forall x, Q (f.stalkMap x).hom)
  statement: P f
  proof: by
  have hQi := (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso
  wlog hY : IsAffine Y generalizing X Y f
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro U
    refine this (fun x => ?_) U.2
    exact (hQi.arrow_mk_iso_iff (AlgebraicGeom

中文:
引理 of_stalkMap
  条件: (hQ : OfLocalizationPrime Q) (H : 对任意 x, Q (f.stalkMap x).hom)
  结论: P f
  证明: by
  have hQi := (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso
  wlog hY : IsAffine Y generalizing X Y f
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro U
    refine this (fun x => ?_) U.2
    exact (hQi.arrow_mk_iso_iff (AlgebraicGeom

Depends on / 依赖: AlgebraicGeometry, AlgebraicGeometry.morphismRestrictStalkMap, HasRingHomProperty, HasRingHomProperty.isLocal_ringHomProperty, IsAffine, IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff_of_iSup_eq_top, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_iSup_eq_top, arrow_mk_iso_iff, generalizing, hQi.arrow_mk_iso_iff, iSup_affineOpens_eq_top, iff_of_iSup_eq_top, isLocal_ringHomProperty, morphismRestrictStalkMap, respectsIso, x.val
-/
lemma of_stalkMap (hQ : OfLocalizationPrime Q) (H : forall x, Q (f.stalkMap x).hom) : P f := by
  have hQi := (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso
  wlog hY : IsAffine Y generalizing X Y f
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro U
    refine this (fun x => ?_) U.2
    exact (hQi.arrow_mk_iso_iff (AlgebraicGeometry.morphismRestrictStalkMap f U x)).mpr (H x.val)
  wlog hX : IsAffine X generalizing X f
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro U
    refine this ?_ U.2
    intro x
    rw [Scheme.Hom.stalkMap_comp]; rw [CommRingCat.hom_comp]; rw [hQi.cancel_right_isIso]
    exact H x.val
  wlog hXY : exists R S, Y = Spec R ∧ X = Spec S generalizing X Y
  · rw [← P.cancel_right_of_respectsIso (g := Y.isoSpec.hom)]
    rw [← P.cancel_left_of_respectsIso (f := X.isoSpec.inv)]
    refine this inferInstance (fun x => ?_) inferInstance ?_
    · rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
        hQi.cancel_right_isIso, CommRingCat.hom_comp, hQi.cancel_left_isIso]
      apply H
    · use Γ(Y, ⊤), Γ(X, ⊤)
  obtain ⟨R, S, rfl, rfl⟩ := hXY
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [Spec_iff (P := P)]
  apply hQ
  intro P hP
  specialize H ⟨P, hP⟩
  rwa [hQi.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ _)] at H

set_option backward.isDefEq.respectTransparency false in
/--
lemma `stalkMap_of_respectsIso` / 引理 `stalkMap_of_respectsIso`

English:
lemma stalkMap_of_respectsIso
  proof: by
  wlog h : IsAffine X ∧ IsAffine Y generalizing X Y f
  · obtain ⟨U, hU, hfx, _⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (Opens.mem_top <| f x)
    obtain ⟨V, hV, hx, e⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x in f ⁻¹ᵁ U from hfx)
    rw [← hQ'.arrow_mk_i

中文:
引理 stalkMap_of_respectsIso
  证明: by
  wlog h : IsAffine X ∧ IsAffine Y generalizing X Y f
  · obtain ⟨U, hU, hfx, _⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (Opens.mem_top <| f x)
    obtain ⟨V, hV, hx, e⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x in f ⁻¹ᵁ U from hfx)
    rw [← hQ'.arrow_mk_i

Depends on / 依赖: IsAffine, IsZariskiLocalAtSource, IsZariskiLocalAtSource.resLE, Opens.isBasis_iff_nbhd.mp, Opens.mem_top, Scheme, Scheme.Hom.resLEStalkMap, X.isBasis_affineOpens, X.isoSpec.inv, Y.isBasis_affineOpens, arrow_mk_iso_iff, generalizing, isBasis_affineOpens, isBasis_iff_nbhd, isoSpec, mem_top, resLEStalkMap
-/
lemma stalkMap_of_respectsIso
    {Q' : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}
    (hQ' : RingHom.RespectsIso Q')
    (hQ : forall {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) (_ : Q f)
      (J : Ideal S) (_ : J.IsPrime), Q' (Localization.localRingHom _ J f rfl))
    (hf : P f) (x : X) : Q' (f.stalkMap x).hom := by
  wlog h : IsAffine X ∧ IsAffine Y generalizing X Y f
  · obtain ⟨U, hU, hfx, _⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (Opens.mem_top <| f x)
    obtain ⟨V, hV, hx, e⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x in f ⁻¹ᵁ U from hfx)
    rw [← hQ'.arrow_mk_iso_iff (Scheme.Hom.resLEStalkMap f e ⟨x]; rw [hx⟩)]
    exact this (IsZariskiLocalAtSource.resLE _ hf) _ ⟨hV, hU⟩
  obtain ⟨hX, hY⟩ := h
  wlog hXY : exists R S, Y = Spec R ∧ X = Spec S generalizing X Y
  · have : Q' ((X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom).stalkMap (X.isoSpec.hom x)).hom := by
      refine this ?_ (X.isoSpec.hom x) inferInstance inferInstance ?_
      · rwa [P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
      · use Γ(Y, ⊤), Γ(X, ⊤)
    rw [Scheme.Hom.stalkMap_comp]; rw [Scheme.Hom.stalkMap_comp]; rw [CommRingCat.hom_comp]; rw [hQ'.cancel_right_isIso]; rw [CommRingCat.hom_comp]; rw [hQ'.cancel_left_isIso] at this
    have heq : (X.isoSpec.inv (X.isoSpec.hom x)) = x := by simp
    rwa [hQ'.arrow_mk_iso_iff (f.arrowStalkMapIsoOfEq heq)] at this
  obtain ⟨R, S, rfl, rfl⟩ := hXY
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [hQ'.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ _)]
  rw [Spec_iff (P := P)] at hf
  apply hQ _ hf

/--
lemma `stalkMap` / 引理 `stalkMap`

English:
lemma stalkMap
  statement: (hQ : forall {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) (_ : Q f)
  proof: stalkMap_of_respectsIso (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso hQ hf x

中文:
引理 stalkMap
  结论: (hQ : 对任意 {R S : 类型u} [CommRing R] [CommRing S] (f : R ->+* S) (_ : Q f)
  证明: stalkMap_of_respectsIso (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso hQ hf x

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.isLocal_ringHomProperty, isLocal_ringHomProperty, respectsIso, stalkMap_of_respectsIso
-/
lemma stalkMap (hQ : forall {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) (_ : Q f)
      (J : Ideal S) (_ : J.IsPrime), Q (Localization.localRingHom _ J f rfl))
    (hf : P f) (x : X) : Q (f.stalkMap x).hom :=
  stalkMap_of_respectsIso (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso hQ hf x

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {P' : MorphismProperty Scheme.{u}}
  proof: by
  ext f
  rw [HasRingHomProperty.eq_affineLocally (P := P)]; rw [HasRingHomProperty.eq_affineLocally (P := P')]; rw [affineLocally_iff_affineOpens_le]; rw [affineLocally_iff_affineOpens_le]
  simp only [h]

中文:
引理 ext
  结论: {P' : Morphism命题erty Scheme.{u}}
  证明: by
  ext f
  rw [HasRingHomProperty.eq_affineLocally (P := P)]; rw [HasRingHomProperty.eq_affineLocally (P := P')]; rw [affineLocally_iff_affineOpens_le]; rw [affineLocally_iff_affineOpens_le]
  simp only [h]

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.eq_affineLocally, affineLocally_iff_affineOpens_le, eq_affineLocally
-/
lemma ext {P' : MorphismProperty Scheme.{u}}
    {Q' : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}
    [HasRingHomProperty P' Q']
    (h : forall {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S), Q f ↔ Q' f) :
    P = P' := by
  ext f
  rw [HasRingHomProperty.eq_affineLocally (P := P)]; rw [HasRingHomProperty.eq_affineLocally (P := P')]; rw [affineLocally_iff_affineOpens_le]; rw [affineLocally_iff_affineOpens_le]
  simp only [h]

end HasRingHomProperty

end AlgebraicGeometry
