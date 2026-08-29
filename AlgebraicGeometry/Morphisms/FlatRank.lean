/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Flat.Rank

/-!
# Rank of a finite flat morphism of schemes

In this file we define the rank `AlgebraicGeometry.Scheme.Hom.finrank` of a finite flat morphism of
schemes `f : X ⟶ Y`. It is locally constant and is characterized by the condition that the rank of
`Spec S ⟶ Spec R` at some prime `p` of `R` is the rank of `S` as an `R`-algebra at `p`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.finrank`: For a morphism `f : X ⟶ Y` of schemes, the function
  `Y → ℕ` sending `y` to the rank of `f_* 𝒪_X` over `𝒪_Y` at `y`. Instead of talking about
  sheaves, we define it by choosing an open neighbourhood of `y`.
  This is sometimes also called the degree of a morphism in the literature.

## Main results

- `AlgebraicGeometry.Scheme.Hom.isLocallyConstant_finrank`: The rank function of a finite flat
  locally finitely presented morphism is locally constant.
- `AlgebraicGeometry.Scheme.Hom.one_le_finrank_iff_surjective`: The rank function is at least `1`
  everywhere if and only if the morphism is surjective.
- `AlgebraicGeometry.Scheme.Hom.isIso_iff_finrank_eq`: A finite flat locally finitely presented
  morphism is an isomorphism if and only if its rank is constant equal to `1`.

## TODO

- Relate `Hom.finrank f y` to the rank of `f_* 𝒪_X` over `𝒪_Y` at `y` when the API for
  locally free sheaves of modules is developed.
-/

public section

open CategoryTheory Limits TopologicalSpace TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {X S Y T : Scheme.{u}} (f : X ⟶ S)

/--
Definition of `IsAffine.finrank` / `IsAffine.finrank` 的定义

English:
definition IsAffine.finrank
  signature: [IsAffine S] (f : X ⟶ S) (s : S)
  body: f.appTop.hom.finrank (S.isoSpec.hom s)

中文:
定义 是仿射.finrank
  签名: [是仿射 S] (f : X ⟶ S) (s : S)
  定义体: f.appTop.hom.finrank (S.isoSpec.hom s)
-/
private def IsAffine.finrank [IsAffine S] (f : X ⟶ S) (s : S) : Nat :=
  f.appTop.hom.finrank (S.isoSpec.hom s)

/--
lemma `IsAffine.finrank_of_isPullback` / 引理 `IsAffine.finrank_of_isPullback`

English:
lemma IsAffine.finrank_of_isPullback
  statement: [IsAffine S] [IsAffine T]
  proof: by
  subst hs
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsPushout f.appTop g.appTop g'.appTop f'.appTop := isPushout_appTop_of_isPullback h
  dsimp [finrank]
  rw [CommRingCat.finrank_eq_of_isPushout this f.flat_appTop f.finite_appTop (T.isoSpec.hom t)]; rw [← Scheme.Hom.comp_apply];

中文:
引理 是仿射.finrank_of_isPullback
  结论: [是仿射 S] [是仿射 T]
  证明: by
  subst hs
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsPushout f.appTop g.appTop g'.appTop f'.appTop := isPushout_appTop_of_isPullback h
  dsimp [finrank]
  rw [CommRingCat.finrank_eq_of_isPushout this f.flat_appTop f.finite_appTop (T.isoSpec.hom t)]; rw [← Scheme.Hom.comp_apply];
-/
private lemma IsAffine.finrank_of_isPullback [IsAffine S] [IsAffine T]
    (f' : Y ⟶ T) (g' : Y ⟶ X) (g : T ⟶ S) (h : IsPullback g' f' f g) [Flat f] [IsFinite f]
    (s : S) (t : T) (hs : g t = s) :
    IsAffine.finrank f' t = IsAffine.finrank f s := by
  subst hs
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsPushout f.appTop g.appTop g'.appTop f'.appTop := isPushout_appTop_of_isPullback h
  dsimp [finrank]
  rw [CommRingCat.finrank_eq_of_isPushout this f.flat_appTop f.finite_appTop (T.isoSpec.hom t)]; rw [← Scheme.Hom.comp_apply]; rw [← Scheme.isoSpec_hom_naturality]
  rfl

/--
lemma `IsAffine.finrank_snd` / 引理 `IsAffine.finrank_snd`

English:
lemma IsAffine.finrank_snd
  statement: [IsAffine S] [IsAffine T]
  proof: finrank_of_isPullback f _ _ _ (.of_hasPullback _ _) _ _ rfl

中文:
引理 是仿射.finrank_snd
  结论: [是仿射 S] [是仿射 T]
  证明: finrank_of_isPullback f _ _ _ (.of_hasPullback _ _) _ _ rfl
-/
private lemma IsAffine.finrank_snd [IsAffine S] [IsAffine T]
    (g : T ⟶ S) [Flat f] [IsFinite f] (x : T) :
    IsAffine.finrank (pullback.snd f g) x = IsAffine.finrank f (g x) :=
  finrank_of_isPullback f _ _ _ (.of_hasPullback _ _) _ _ rfl

/--
lemma `IsAffine.finrank_comp_left_of_isIso` / 引理 `IsAffine.finrank_comp_left_of_isIso`

English:
lemma IsAffine.finrank_comp_left_of_isIso
  statement: [IsAffine S]
  proof: by
  ext z
  apply finrank_of_isPullback g (f ≫ g) f (𝟙 _) _ _ _ rfl
  exact IsPullback.of_horiz_isIso (by simp)

中文:
引理 是仿射.finrank_comp_left_of_isIso
  结论: [是仿射 S]
  证明: by
  ext z
  apply finrank_of_isPullback g (f ≫ g) f (𝟙 _) _ _ _ rfl
  exact IsPullback.of_horiz_isIso (by simp)
-/
private lemma IsAffine.finrank_comp_left_of_isIso [IsAffine S]
    (f : X ⟶ Y) (g : Y ⟶ S) [IsIso f] [IsFinite g] [Flat g] :
    IsAffine.finrank (f ≫ g) = IsAffine.finrank g := by
  ext z
  apply finrank_of_isPullback g (f ≫ g) f (𝟙 _) _ _ _ rfl
  exact IsPullback.of_horiz_isIso (by simp)

/-- The rank of a morphism `f : X ⟶ S` of schemes at a point `s : S`. When `f` is finite,
flat and locally of finite presentation, this is a locally constant function (see
`AlgebraicGeometry.isLocallyConstant_finrank`). -/
@[stacks 02KA "second part"]
/--
Definition of `Scheme.Hom.finrank` / `Scheme.Hom.finrank` 的定义

English:
definition Scheme.Hom.finrank
  signature: {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
  body: IsAffine.finrank (pullback.snd f (S.affineOpenCover.f <| S.affineOpenCover.idx s))
    (S.affineOpenCover.covers s).choose

中文:
定义 概形.态射.finrank
  签名: {X S : 概形.{u}} (f : X ⟶ S) (s : S)
  定义体: IsAffine.finrank (pullback.snd f (S.affineOpenCover.f <| S.affineOpenCover.idx s))
    (S.affineOpenCover.covers s).choose

Depends on / 依赖: IsAffine, IsAffine.finrank, S.affineOpenCover.covers, S.affineOpenCover.f, S.affineOpenCover.idx, affineOpenCover, covers, finrank, pullback, pullback.snd
-/
def Scheme.Hom.finrank {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : Nat :=
  IsAffine.finrank (pullback.snd f (S.affineOpenCover.f <| S.affineOpenCover.idx s))
    (S.affineOpenCover.covers s).choose

/--
lemma `Scheme.Hom.finrank_eq_finrank_snd_of_isAffine` / 引理 `Scheme.Hom.finrank_eq_finrank_snd_of_isAffine`

English:
lemma Scheme.Hom.finrank_eq_finrank_snd_of_isAffine
  statement: (g : T ⟶ S) [IsAffine T] (t : T)
  proof: by
  let i := S.affineOpenCover.f (S.affineOpenCover.idx (g t))
  obtain ⟨y, hyl, hyr⟩ := Scheme.Pullback.exists_preimage_pullback
    (S.affineOpenCover.covers <| g t).choose t (S.affineOpenCover.covers <| g t).choose_spec
  obtain ⟨R, u, hu, z, rfl⟩ := (pullback i g).exists_Spec_apply_eq y
  trans

中文:
引理 概形.态射.finrank_eq_finrank_snd_of_isAffine
  结论: (g : T ⟶ S) [是仿射 T] (t : T)
  证明: by
  let i := S.affineOpenCover.f (S.affineOpenCover.idx (g t))
  obtain ⟨y, hyl, hyr⟩ := Scheme.Pullback.exists_preimage_pullback
    (S.affineOpenCover.covers <| g t).choose t (S.affineOpenCover.covers <| g t).choose_spec
  obtain ⟨R, u, hu, z, rfl⟩ := (pullback i g).exists_Spec_apply_eq y
  trans
-/
private lemma Scheme.Hom.finrank_eq_finrank_snd_of_isAffine (g : T ⟶ S) [IsAffine T] (t : T)
    [Flat f] [IsFinite f] :
    f.finrank (g t) = IsAffine.finrank (pullback.snd f g) t := by
  let i := S.affineOpenCover.f (S.affineOpenCover.idx (g t))
  obtain ⟨y, hyl, hyr⟩ := Scheme.Pullback.exists_preimage_pullback
    (S.affineOpenCover.covers <| g t).choose t (S.affineOpenCover.covers <| g t).choose_spec
  obtain ⟨R, u, hu, z, rfl⟩ := (pullback i g).exists_Spec_apply_eq y
  trans IsAffine.finrank (pullback.snd (pullback.snd f g) (u ≫ pullback.snd _ _)) z
  · refine (IsAffine.finrank_of_isPullback _ _ ?_ ?_ ?_ _ _ ?_).symm
    · exact pullback.map _ _ _ _ (pullback.fst f g) (u ≫ pullback.fst _ _) g
        pullback.condition.symm (by simp [← pullback.condition]; rfl)
    · exact u ≫ pullback.fst _ _
    · apply IsPullback.map_fst_comp_fst_snd_comp_fst
    · exact hyl
  · simp_rw [← hyr]
    exact IsAffine.finrank_snd (pullback.snd f g) (u ≫ pullback.snd _ _) z

/--
lemma `Scheme.Hom.finrank_eq_of_isAffine` / 引理 `Scheme.Hom.finrank_eq_of_isAffine`

English:
lemma Scheme.Hom.finrank_eq_of_isAffine
  given: [IsAffine S] [Flat f] [IsFinite f] (s : S)
  proof: by
  rw [show s = (𝟙 S : S ⟶ S) s from rfl]; rw [finrank_eq_finrank_snd_of_isAffine]; rw [IsAffine.finrank_snd]

中文:
引理 概形.态射.finrank_eq_of_isAffine
  条件: [是仿射 S] [平坦 f] [是有限 f] (s : S)
  证明: by
  rw [show s = (𝟙 S : S ⟶ S) s from rfl]; rw [finrank_eq_finrank_snd_of_isAffine]; rw [IsAffine.finrank_snd]
-/
private lemma Scheme.Hom.finrank_eq_of_isAffine [IsAffine S] [Flat f] [IsFinite f] (s : S) :
    f.finrank s = IsAffine.finrank f s := by
  rw [show s = (𝟙 S : S ⟶ S) s from rfl]; rw [finrank_eq_finrank_snd_of_isAffine]; rw [IsAffine.finrank_snd]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `Scheme.Hom.finrank_SpecMap_eq_finrank` / 引理 `Scheme.Hom.finrank_SpecMap_eq_finrank`

English:
lemma Scheme.Hom.finrank_SpecMap_eq_finrank
  statement: {R S : CommRingCat.{u}} {f : R ⟶ S} (hf₁ : f.hom.Finite)
  proof: by
  simp only [← IsFinite.SpecMap_iff, ← Flat.SpecMap_iff] at hf₁ hf₂
  have hf₁ : (Spec.map f).appTop.hom.Finite := (Spec.map f).finite_appTop
  have hf₂ : (Spec.map f).appTop.hom.Flat := (Spec.map f).flat_appTop
  ext
  rw [finrank_eq_of_isAffine]; rw [IsAffine.finrank]
  have : f = (Scheme.ΓSpec

中文:
引理 概形.态射.finrank_SpecMap_eq_finrank
  结论: {R S : 交换环范畴.{u}} {f : R ⟶ S} (hf₁ : f.hom.有限)
  证明: by
  simp only [← IsFinite.SpecMap_iff, ← Flat.SpecMap_iff] at hf₁ hf₂
  have hf₁ : (Spec.map f).appTop.hom.Finite := (Spec.map f).finite_appTop
  have hf₂ : (Spec.map f).appTop.hom.Flat := (Spec.map f).flat_appTop
  ext
  rw [finrank_eq_of_isAffine]; rw [IsAffine.finrank]
  have : f = (Scheme.ΓSpec

Depends on / 依赖: ConcreteCategory, ConcreteCategory.bijective_of_isIso, Finite, Flat.SpecMap_iff, IsAffine, IsAffine.finrank, IsFinite, IsFinite.SpecMap_iff, RingHom, RingHom.finrank_com, RingHom.finrank_comp_right_of_bijective, Scheme, Spec.map, SpecMap_iff, appTop, appTop.hom.Finite, appTop.hom.Flat, bijective_of_isIso, conv_rhs, finite_appTop
-/
lemma Scheme.Hom.finrank_SpecMap_eq_finrank {R S : CommRingCat.{u}} {f : R ⟶ S} (hf₁ : f.hom.Finite)
    (hf₂ : f.hom.Flat) :
    finrank (Spec.map f) = f.hom.finrank := by
  simp only [← IsFinite.SpecMap_iff, ← Flat.SpecMap_iff] at hf₁ hf₂
  have hf₁ : (Spec.map f).appTop.hom.Finite := (Spec.map f).finite_appTop
  have hf₂ : (Spec.map f).appTop.hom.Flat := (Spec.map f).flat_appTop
  ext
  rw [finrank_eq_of_isAffine]; rw [IsAffine.finrank]
  have : f = (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom := by simp
  conv_rhs => rw [this]
  dsimp
  rw [RingHom.finrank_comp_right_of_bijective _ _ (ConcreteCategory.bijective_of_isIso _)]
  · rw [RingHom.finrank_comp_left_of_bijective _ _ (ConcreteCategory.bijective_of_isIso _) hf₁ hf₂]
  · exact .comp (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).surjective) hf₁
  · exact .comp hf₂ (.of_bijective (ConcreteCategory.bijective_of_isIso _))
  · simp [isoSpec_Spec_hom, SpecMap_ΓSpecIso_hom, ← AlgebraicGeometry.Spec.map_apply,
      ← Scheme.Hom.comp_apply, toSpecΓ_SpecMap_ΓSpecIso_inv]

/--
lemma `Scheme.Hom.finrank_SpecMap_algebraMap` / 引理 `Scheme.Hom.finrank_SpecMap_algebraMap`

English:
lemma Scheme.Hom.finrank_SpecMap_algebraMap
  statement: (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  proof: by
  rw [finrank_SpecMap_eq_finrank]
  · simp
  · simpa [RingHom.finite_algebraMap]
  · simpa [RingHom.flat_algebraMap_iff]

中文:
引理 概形.态射.finrank_SpecMap_algebraMap
  结论: (R S : 类型u) [交换环 R] [交换环 S] [代数 R S]
  证明: by
  rw [finrank_SpecMap_eq_finrank]
  · simp
  · simpa [RingHom.finite_algebraMap]
  · simpa [RingHom.flat_algebraMap_iff]

Depends on / 依赖: RingHom, RingHom.finite_algebraMap, RingHom.flat_algebraMap_iff, finite_algebraMap, finrank_SpecMap_eq_finrank, flat_algebraMap_iff
-/
lemma Scheme.Hom.finrank_SpecMap_algebraMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] (x : PrimeSpectrum R) :
    finrank (Spec.map (CommRingCat.ofHom <| algebraMap R S)) x = Module.rankAtStalk S x := by
  rw [finrank_SpecMap_eq_finrank]
  · simp
  · simpa [RingHom.finite_algebraMap]
  · simpa [RingHom.flat_algebraMap_iff]

variable (f : X ⟶ Y) [Flat f] [IsFinite f]

@[simp]
/--
lemma `Scheme.Hom.finrank_comp_left_of_isIso` / 引理 `Scheme.Hom.finrank_comp_left_of_isIso`

English:
lemma Scheme.Hom.finrank_comp_left_of_isIso
  statement: (f : X ⟶ Y) (g : Y ⟶ S)
  proof: by
  ext z
  let e : pullback (f ≫ g) (S.affineOpenCover.f (S.affineOpenCover.idx z)) ≅
      pullback g (S.affineOpenCover.f (S.affineOpenCover.idx z)) :=
    (pullbackRightPullbackFstIso g (S.affineOpenCover.f (S.affineOpenCover.idx z)) f).symm ≪≫
      asIso (pullback.snd f (pullback.fst g (S.aff

中文:
引理 概形.态射.finrank_comp_left_of_isIso
  结论: (f : X ⟶ Y) (g : Y ⟶ S)
  证明: by
  ext z
  let e : pullback (f ≫ g) (S.affineOpenCover.f (S.affineOpenCover.idx z)) ≅
      pullback g (S.affineOpenCover.f (S.affineOpenCover.idx z)) :=
    (pullbackRightPullbackFstIso g (S.affineOpenCover.f (S.affineOpenCover.idx z)) f).symm ≪≫
      asIso (pullback.snd f (pullback.fst g (S.aff

Depends on / 依赖: IsAffine, IsAffine.finrank_comp_left_of_isIso, S.affineOpenCover.f, S.affineOpenCover.idx, affineOpenCover, e.hom, finrank, finrank_comp_left_of_isIso, pullback, pullback.fst, pullback.snd, pullbackRightPullbackFstIso
-/
lemma Scheme.Hom.finrank_comp_left_of_isIso (f : X ⟶ Y) (g : Y ⟶ S)
    [IsIso f] [Flat g] [IsFinite g] :
    finrank (f ≫ g) = finrank g := by
  ext z
  let e : pullback (f ≫ g) (S.affineOpenCover.f (S.affineOpenCover.idx z)) ≅
      pullback g (S.affineOpenCover.f (S.affineOpenCover.idx z)) :=
    (pullbackRightPullbackFstIso g (S.affineOpenCover.f (S.affineOpenCover.idx z)) f).symm ≪≫
      asIso (pullback.snd f (pullback.fst g (S.affineOpenCover.f _)))
  have : e.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [e]
  rw [finrank]; rw [finrank]; rw [← this]; rw [IsAffine.finrank_comp_left_of_isIso]

/--
lemma `Scheme.Hom.finrank_pullback_snd` / 引理 `Scheme.Hom.finrank_pullback_snd`

English:
lemma Scheme.Hom.finrank_pullback_snd
  statement: {Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: by
  obtain ⟨R, i, _, y', rfl⟩ := Y.exists_Spec_apply_eq y
  rw [← Scheme.Hom.comp_apply]; rw [finrank_eq_finrank_snd_of_isAffine]; rw [finrank_eq_finrank_snd_of_isAffine]; rw [← pullbackLeftPullbackSndIso_hom_snd f g i]; rw [← finrank_eq_of_isAffine]; rw [← finrank_eq_of_isAffine]; rw [finrank_comp

中文:
引理 概形.态射.finrank_pullback_snd
  结论: {Z : 概形.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: by
  obtain ⟨R, i, _, y', rfl⟩ := Y.exists_Spec_apply_eq y
  rw [← Scheme.Hom.comp_apply]; rw [finrank_eq_finrank_snd_of_isAffine]; rw [finrank_eq_finrank_snd_of_isAffine]; rw [← pullbackLeftPullbackSndIso_hom_snd f g i]; rw [← finrank_eq_of_isAffine]; rw [← finrank_eq_of_isAffine]; rw [finrank_comp

Depends on / 依赖: Scheme, Scheme.Hom.comp_apply, Y.exists_Spec_apply_eq, comp_apply, exists_Spec_apply_eq, finrank_comp_left_of_isIso, finrank_eq_finrank_snd_of_isAffine, finrank_eq_of_isAffine, pullbackLeftPullbackSndIso_hom_snd
-/
lemma Scheme.Hom.finrank_pullback_snd {Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Flat f] [IsFinite f] (y : Y) :
    finrank (pullback.snd f g) y = finrank f (g y) := by
  obtain ⟨R, i, _, y', rfl⟩ := Y.exists_Spec_apply_eq y
  rw [← Scheme.Hom.comp_apply]; rw [finrank_eq_finrank_snd_of_isAffine]; rw [finrank_eq_finrank_snd_of_isAffine]; rw [← pullbackLeftPullbackSndIso_hom_snd f g i]; rw [← finrank_eq_of_isAffine]; rw [← finrank_eq_of_isAffine]; rw [finrank_comp_left_of_isIso]

/--
lemma `Scheme.Hom.finrank_of_isPullback` / 引理 `Scheme.Hom.finrank_of_isPullback`

English:
lemma Scheme.Hom.finrank_of_isPullback
  statement: {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
  proof: by
  rw [← h.isoPullback_hom_snd]; rw [finrank_comp_left_of_isIso]; rw [finrank_pullback_snd]

中文:
引理 概形.态射.finrank_of_isPullback
  结论: {P X Y Z : 概形.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
  证明: by
  rw [← h.isoPullback_hom_snd]; rw [finrank_comp_left_of_isIso]; rw [finrank_pullback_snd]

Depends on / 依赖: finrank_comp_left_of_isIso, finrank_pullback_snd, h.isoPullback_hom_snd, isoPullback_hom_snd
-/
lemma Scheme.Hom.finrank_of_isPullback {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : IsPullback fst snd f g) [Flat f] [IsFinite f] (y : Y) :
    finrank snd y = finrank f (g y) := by
  rw [← h.isoPullback_hom_snd]; rw [finrank_comp_left_of_isIso]; rw [finrank_pullback_snd]

/--
lemma `Scheme.Hom.finrank_pullback_fst` / 引理 `Scheme.Hom.finrank_pullback_fst`

English:
lemma Scheme.Hom.finrank_pullback_fst
  statement: {Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: finrank_of_isPullback (pullback.snd g f) _ _ _ (.flip <| .of_hasPullback _ _) y

中文:
引理 概形.态射.finrank_pullback_fst
  结论: {Z : 概形.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: finrank_of_isPullback (pullback.snd g f) _ _ _ (.flip <| .of_hasPullback _ _) y

Depends on / 依赖: finrank_of_isPullback, of_hasPullback, pullback, pullback.snd
-/
lemma Scheme.Hom.finrank_pullback_fst {Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Flat f] [IsFinite f] (y : Y) :
    finrank (pullback.fst g f) y = finrank f (g y) :=
  finrank_of_isPullback (pullback.snd g f) _ _ _ (.flip <| .of_hasPullback _ _) y

set_option backward.isDefEq.respectTransparency.types false in
nonrec lemma Scheme.Hom.one_le_finrank_map (x : X) : 1 <= finrank f (f x) := by
  wlog hY : exists R, Y = Spec R
  · obtain ⟨R, g, hg, y, hy⟩ := Y.exists_Spec_apply_eq (f x)
    rw [← hy]; rw [← finrank_pullback_snd]
    obtain ⟨z, hzl, hzr⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y hy.symm
    rw [hzr.symm]
    refine this _ _ ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    have heq : f x = (X.isoSpec.inv ≫ f) (X.isoSpec.hom x) := by simp
    rw [← finrank_comp_left_of_isIso X.isoSpec.inv]; rw [heq]
    exact this _ _ _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
  rw [finrank_SpecMap_eq_finrank ‹_› ‹_›]
  algebraize [φ.hom]
  rw [← RingHom.algebraMap_toAlgebra φ.hom]; rw [RingHom.finrank_algebraMap]; rw [Nat.add_one_le_iff]; rw [PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap]
  use x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A finite flat locally finitely presented morphism is surjective if and only if its rank
function is at least `1` everywhere. -/
nonrec lemma Scheme.Hom.one_le_finrank_iff_surjective : 1 <= finrank f ↔ Surjective f := by
  refine ⟨fun h => ?_, fun _ => ?_⟩
  · wlog hY : exists R, Y = Spec R
    · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Surjective) Y.affineCover]
      intro i
      dsimp only [Scheme.Cover.pullbackHom]
      refine this _ (fun y => ?_) ⟨_, rfl⟩
      rw [finrank_pullback_snd]
      exact h _
    obtain ⟨R, rfl⟩ := hY
    wlog hX : exists S, X = Spec S
    · have _ : IsAffine X := isAffine_of_isAffineHom f
      rw [← MorphismProperty.cancel_left_of_respectsIso @Surjective X.isoSpec.inv]
      refine this _ _ (fun x => ?_) ⟨_, rfl⟩
      rw [finrank_comp_left_of_isIso]
      exact h x
    obtain ⟨S, rfl⟩ := hX
    obtain ⟨φ, rfl⟩ := Spec.map_surjective f
    constructor
    intro x
    specialize h x
    simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
    rw [finrank_SpecMap_eq_finrank ‹_› ‹_›] at h
    algebraize [φ.hom]
    exact (PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap _).mp h
  · intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    exact one_le_finrank_map f x

/-- The rank of a finite flat locally finitely presented morphism is locally constant. -/
nonrec lemma Scheme.Hom.isLocallyConstant_finrank [LocallyOfFinitePresentation f] :
    IsLocallyConstant (finrank f) := by
  wlog hY : exists R, Y = Spec R
  · rw [IsLocallyConstant.iff_exists_open]
    intro y
    obtain ⟨R, g, _, x, rfl⟩ := Y.exists_Spec_apply_eq y
    simp_rw [IsLocallyConstant.iff_exists_open] at this
    obtain ⟨U, hU, hxU, H⟩ := this (pullback.snd f g) ⟨_, rfl⟩ x
    refine ⟨g ''ᵁ ⟨U, hU⟩, (g ''ᵁ ⟨U, hU⟩).2, ⟨x, hxU, rfl⟩, fun y => ?_⟩
    rintro ⟨y', (hyU : y' in U), (rfl : g y' = y)⟩
    rw [← finrank_pullback_snd _ g]; rw [← finrank_pullback_snd _ g]
    exact H y' hyU
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    rw [← finrank_comp_left_of_isIso X.isoSpec.inv]
    exact this _ _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [Flat.SpecMap_iff, IsFinite.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff] at *
  rw [finrank_SpecMap_eq_finrank ‹_› ‹_›]
  algebraize [φ.hom]
  have := Module.FinitePresentation.of_finite_of_finitePresentation
  exact Module.isLocallyConstant_rankAtStalk

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Scheme.Hom.finrank_eq_one_of_isIso` / 引理 `Scheme.Hom.finrank_eq_one_of_isIso`

English:
lemma Scheme.Hom.finrank_eq_one_of_isIso
  given: (f : X ⟶ Y) [IsIso f]
  statement: finrank f = 1
  proof: by
  ext y
  obtain ⟨R, g, _, y, rfl⟩ := Y.exists_Spec_apply_eq y
  have : Nontrivial R := y.nontrivial
  rw [← finrank_pullback_snd]; rw [← Category.comp_id (pullback.snd f g)]; rw [finrank_comp_left_of_isIso]; rw [← Spec.map_id]; rw [finrank_SpecMap_eq_finrank]; rw [CommRingCat.hom_id]; rw [Pi.one

中文:
引理 概形.态射.finrank_eq_one_of_isIso
  条件: (f : X ⟶ Y) [是同构 f]
  结论: finrank f = 1
  证明: by
  ext y
  obtain ⟨R, g, _, y, rfl⟩ := Y.exists_Spec_apply_eq y
  have : Nontrivial R := y.nontrivial
  rw [← finrank_pullback_snd]; rw [← Category.comp_id (pullback.snd f g)]; rw [finrank_comp_left_of_isIso]; rw [← Spec.map_id]; rw [finrank_SpecMap_eq_finrank]; rw [CommRingCat.hom_id]; rw [Pi.one

Depends on / 依赖: Algebra, Algebra.algebraMap_self, Category, Category.comp_id, CommRingCat, CommRingCat.hom_id, Finite, Nontrivial, Pi.one_apply, RingHom, RingHom.Finite.id, RingHom.Flat.id, RingHom.finrank_algebraMap, Spec.map_id, Y.exists_Spec_apply_eq, algebraMap_self, comp_id, exists_Spec_apply_eq, finrank_SpecMap_eq_finrank, finrank_algebraMap
-/
lemma Scheme.Hom.finrank_eq_one_of_isIso (f : X ⟶ Y) [IsIso f] : finrank f = 1 := by
  ext y
  obtain ⟨R, g, _, y, rfl⟩ := Y.exists_Spec_apply_eq y
  have : Nontrivial R := y.nontrivial
  rw [← finrank_pullback_snd]; rw [← Category.comp_id (pullback.snd f g)]; rw [finrank_comp_left_of_isIso]; rw [← Spec.map_id]; rw [finrank_SpecMap_eq_finrank]; rw [CommRingCat.hom_id]; rw [Pi.one_apply]; rw [← Algebra.algebraMap_self]; rw [RingHom.finrank_algebraMap]
  · simp
  · exact RingHom.Finite.id R
  · exact RingHom.Flat.id ↑R

set_option backward.defeqAttrib.useBackward true in
/-- A finite flat locally finitely presented morphism is an isomorphism if and only if
its rank is constant equal to `1`. -/
nonrec lemma Scheme.Hom.isIso_iff_finrank_eq : IsIso f ↔ finrank f = 1 := by
  refine ⟨fun h => finrank_eq_one_of_isIso f, fun h => ?_⟩
  wlog hY : exists R, Y = Spec R
  · rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms Scheme) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    refine this _ ?_ ⟨_, rfl⟩
    ext y
    rw [finrank_pullback_snd]; rw [h]; rw [Pi.one_apply]; rw [Pi.one_apply]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    rw [← isIso_comp_left_iff X.isoSpec.inv]
    refine this _ _ ?_ ⟨_, rfl⟩
    rw [finrank_comp_left_of_isIso]; rw [h]
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
  algebraize [φ.hom]
  have : IsIso φ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    apply Module.algebraMap_bijective_of_rankAtStalk
    rwa [finrank_SpecMap_eq_finrank ‹_› ‹_›] at h
  infer_instance

end

end AlgebraicGeometry
