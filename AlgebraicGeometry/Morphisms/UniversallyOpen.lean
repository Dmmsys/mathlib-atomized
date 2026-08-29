/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Universally open morphism

A morphism of schemes `f : X ⟶ Y` is universally open if `X ×[Y] Y' ⟶ Y'` is an open map
for all base change `Y' ⟶ Y`.

We show that being universally open is local at the target, and is stable under compositions and
base changes.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty

/-- A morphism of schemes `f : X ⟶ Y` is universally open if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) an open map.
-/
@[mk_iff]
/--
Definition of `UniversallyOpen` / `UniversallyOpen` 的定义

English:
class UniversallyOpen
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - universally_isOpenMap : universally (topologically @IsOpenMap) f

中文:
类 UniversallyOpen
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - universally_isOpenMap : universally (topologically @IsOpenMap) f
-/
class UniversallyOpen (f : X ⟶ Y) : Prop where
  universally_isOpenMap : universally (topologically @IsOpenMap) f

@[deprecated (since := "2026-01-20")]
alias UniversallyOpen.out := UniversallyOpen.universally_isOpenMap

/--
lemma `Scheme.Hom.isOpenMap` / 引理 `Scheme.Hom.isOpenMap`

English:
lemma Scheme.Hom.isOpenMap
  given: {X Y : Scheme} (f : X ⟶ Y) [UniversallyOpen f]
  proof: UniversallyOpen.universally_isOpenMap _ _ _ IsPullback.of_id_snd

中文:
引理 Scheme.Hom.isOpenMap
  条件: {X Y : Scheme} (f : X ⟶ Y) [UniversallyOpen f]
  证明: UniversallyOpen.universally_isOpenMap _ _ _ IsPullback.of_id_snd

Depends on / 依赖: IsPullback, IsPullback.of_id_snd, UniversallyOpen, UniversallyOpen.universally_isOpenMap, of_id_snd, universally_isOpenMap
-/
lemma Scheme.Hom.isOpenMap {X Y : Scheme} (f : X ⟶ Y) [UniversallyOpen f] :
    IsOpenMap f := UniversallyOpen.universally_isOpenMap _ _ _ IsPullback.of_id_snd

namespace UniversallyOpen

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  statement: @UniversallyOpen = universally (topologically @IsOpenMap)
  proof: by
  ext X Y f; rw [universallyOpen_iff]

中文:
定理 eq
  结论: @UniversallyOpen = universally (topologically @IsOpenMap)
  证明: by
  ext X Y f; rw [universallyOpen_iff]

Depends on / 依赖: universallyOpen_iff
-/
theorem eq : @UniversallyOpen = universally (topologically @IsOpenMap) := by
  ext X Y f; rw [universallyOpen_iff]

instance (priority := 900) [IsOpenImmersion f] : UniversallyOpen f := by
  rw [eq]
  intro X' Y' i₁ i₂ f' hf
  have hf' : IsOpenImmersion f' := MorphismProperty.of_isPullback hf.flip inferInstance
  exact f'.isOpenEmbedding.isOpenMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RespectsIso @UniversallyOpen
  body: eq.symm ▸ inferInstance

中文:
实例 :
  签名: RespectsIso @UniversallyOpen
  定义体: eq.symm ▸ inferInstance

Depends on / 依赖: eq.symm
-/
instance : RespectsIso @UniversallyOpen :=
  eq.symm ▸ inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderBaseChange @UniversallyOpen
  body: eq.symm ▸ inferInstance

中文:
实例 :
  签名: IsStableUnderBaseChange @UniversallyOpen
  定义体: eq.symm ▸ inferInstance

Depends on / 依赖: eq.symm
-/
instance : IsStableUnderBaseChange @UniversallyOpen :=
  eq.symm ▸ inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderComposition (topologically @IsOpenMap)
  body: IsOpenMap.comp (f := f) (g := g) hg hf

中文:
实例 :
  签名: IsStableUnderComposition (topologically @IsOpenMap)
  定义体: IsOpenMap.comp (f := f) (g := g) hg hf

Depends on / 依赖: IsOpenMap, IsOpenMap.comp
-/
instance : IsStableUnderComposition (topologically @IsOpenMap) where
  comp_mem f g hf hg := IsOpenMap.comp (f := f) (g := g) hg hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderComposition @UniversallyOpen
  body: by
  rw [eq]
  infer_instance

中文:
实例 :
  签名: IsStableUnderComposition @UniversallyOpen
  定义体: by
  rw [eq]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : IsStableUnderComposition @UniversallyOpen := by
  rw [eq]
  infer_instance

instance {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : UniversallyOpen f] [hg : UniversallyOpen g] : UniversallyOpen (f ≫ g) :=
  comp_mem _ _ _ hf hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @UniversallyOpen
  body: inferInstance

中文:
实例 :
  签名: Morphism命题erty.IsMultiplicative @UniversallyOpen
  定义体: inferInstance
-/
instance : MorphismProperty.IsMultiplicative @UniversallyOpen where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `fst` / 实例 `fst`

English:
instance fst
  signature: {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyOpen g]
  body: MorphismProperty.pullback_fst f g hg

中文:
实例 fst
  签名: {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyOpen g]
  定义体: MorphismProperty.pullback_fst f g hg

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
instance fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyOpen g] :
    UniversallyOpen (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g hg

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `snd` / 实例 `snd`

English:
instance snd
  signature: {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyOpen f]
  body: MorphismProperty.pullback_snd f g hf

中文:
实例 snd
  签名: {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyOpen f]
  定义体: MorphismProperty.pullback_snd f g hf

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
instance snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyOpen f] :
    UniversallyOpen (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtTarget @UniversallyOpen
  body: by
  rw [eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isOpenMap_iff_restrictPreimage.mpr H

中文:
实例 :
  签名: IsZariskiLocalAtTarget @UniversallyOpen
  定义体: by
  rw [eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isOpenMap_iff_restrictPreimage.mpr H

Depends on / 依赖: hU.isOpenMap_iff_restrictPreimage.mpr, isOpenMap_iff_restrictPreimage, morphismRestrict_base, simp_rw, topologically, universally_isZariskiLocalAtTarget
-/
instance : IsZariskiLocalAtTarget @UniversallyOpen := by
  rw [eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isOpenMap_iff_restrictPreimage.mpr H

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtSource @UniversallyOpen
  body: by
  rw [eq]
  exact universally_isZariskiLocalAtSource _

中文:
实例 :
  签名: IsZariskiLocalAtSource @UniversallyOpen
  定义体: by
  rw [eq]
  exact universally_isZariskiLocalAtSource _

Depends on / 依赖: universally_isZariskiLocalAtSource
-/
instance : IsZariskiLocalAtSource @UniversallyOpen := by
  rw [eq]
  exact universally_isZariskiLocalAtSource _

end UniversallyOpen

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- A generalizing morphism, locally of finite presentation is open. -/
@[stacks 01U1]
/--
lemma `isOpenMap_of_generalizingMap` / 引理 `isOpenMap_of_generalizingMap`

English:
lemma isOpenMap_of_generalizingMap
  statement: [LocallyOfFinitePresentation f]
  proof: by
  change topologically IsOpenMap f
  wlog hY : exists R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := topologically IsOpenMap) Y.affineCover]
    intro i
    dsimp only [Scheme.Cover.pullbackHom]
    refine this _ ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtTarget.of_isPullback (P :

中文:
引理 isOpenMap_of_generalizingMap
  结论: [LocallyOfFinitePresentation f]
  证明: by
  change topologically IsOpenMap f
  wlog hY : exists R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := topologically IsOpenMap) Y.affineCover]
    intro i
    dsimp only [Scheme.Cover.pullbackHom]
    refine this _ ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtTarget.of_isPullback (P :

Depends on / 依赖: GeneralizingMap, IsOpenMap, IsPullback, IsPullback.of_hasPullback, IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff_of_openCover, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.iff_of_openCover, IsZariskiLocalAtTarget.of_isPullback, Scheme, Scheme.Cover.pullbackHom, Y.affineCover, Y.affineCover.f, affineCover, iff_of_openCover, of_hasPullback, of_isPullback, pullbackHom, topologically
-/
lemma isOpenMap_of_generalizingMap [LocallyOfFinitePresentation f]
    (hf : GeneralizingMap f) : IsOpenMap f := by
  change topologically IsOpenMap f
  wlog hY : exists R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := topologically IsOpenMap) Y.affineCover]
    intro i
    dsimp only [Scheme.Cover.pullbackHom]
    refine this _ ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtTarget.of_isPullback (P := topologically GeneralizingMap)
      (iY := Y.affineCover.f i) (IsPullback.of_hasPullback ..) hf
  obtain ⟨R, rfl⟩ := hY
  wlog hX : exists S, X = Spec S
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := topologically IsOpenMap) X.affineCover]
    intro i
    refine this f _ _ ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtSource.comp (P := topologically GeneralizingMap) hf _
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  convert! PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  · rwa [Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  · apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp inferInstance

/--
lemma `Flat.generalizingMap` / 引理 `Flat.generalizingMap`

English:
lemma Flat.generalizingMap
  given: [Flat f]
  statement: GeneralizingMap f
  proof: by
  have := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget.{u}
    (topologically GeneralizingMap)
  change topologically GeneralizingMap f
  rw [HasRingHomProperty.iff_appLE (P := topologically GeneralizingMap)]
  intro U V e
  algebraize [(f.appLE U V e).hom]
  apply Algeb

中文:
引理 Flat.generalizingMap
  条件: [Flat f]
  结论: GeneralizingMap f
  证明: by
  have := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget.{u}
    (topologically GeneralizingMap)
  change topologically GeneralizingMap f
  rw [HasRingHomProperty.iff_appLE (P := topologically GeneralizingMap)]
  intro U V e
  algebraize [(f.appLE U V e).hom]
  apply Algeb

Depends on / 依赖: Algebra, Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp, Algebra.HasGoingDown.of_flat, GeneralizingMap, HasGoingDown, HasRingHomProperty, HasRingHomProperty.appLE, HasRingHomProperty.iff_appLE, HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget, algebraize, convert, f.appLE, iff_appLE, iff_generalizingMap_primeSpectrumComap, of_flat, of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget, topologically
-/
lemma Flat.generalizingMap [Flat f] : GeneralizingMap f := by
  have := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget.{u}
    (topologically GeneralizingMap)
  change topologically GeneralizingMap f
  rw [HasRingHomProperty.iff_appLE (P := topologically GeneralizingMap)]
  intro U V e
  algebraize [(f.appLE U V e).hom]
  apply Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp
  convert! Algebra.HasGoingDown.of_flat
  exact HasRingHomProperty.appLE @Flat f ‹_› U V e

/-- A flat morphism, locally of finite presentation is universally open. -/
@[stacks 01UA]
instance (priority := low) UniversallyOpen.of_flat [Flat f] [LocallyOfFinitePresentation f] :
    UniversallyOpen f :=
  ⟨universally_mk' _ _ fun _ _ => isOpenMap_of_generalizingMap _ (Flat.generalizingMap _)⟩

nonrec instance (priority := low) [IsIntegral Y] [Subsingleton Y] :
    UniversallyOpen f := by
  wlog hX : exists S, X = Spec S generalizing X
  · refine (IsZariskiLocalAtSource.iff_of_openCover X.affineCover).mpr fun i => this _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  wlog hY : exists K, Y = Spec K ∧ IsField K generalizing Y
  · have inst : Subsingleton (Spec Γ(Y, ⊤)) := Y.isoSpec.inv.homeomorph.subsingleton
    exact (MorphismProperty.cancel_right_of_respectsIso _ _ Y.isoSpec.hom).mp
      (this _ ⟨_, rfl, isField_of_isIntegral_of_subsingleton _⟩)
  obtain ⟨K, rfl, hK⟩ := hY
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ⟨universally_mk' _ _ fun {T} g _ => ?_⟩
  wlog hT : exists R, T = Spec R generalizing T
  · refine (IsZariskiLocalAtTarget.iff_of_openCover T.affineCover).mpr fun i => ?_
    refine (MorphismProperty.cancel_left_of_respectsIso _
      ((pullbackRightPullbackFstIso ..).inv ≫ (pullbackSymmetry ..).hom) _).mp ?_
    simpa [Scheme.Cover.pullbackHom] using! this _ _ ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hT
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom, ψ.hom]
  refine (MorphismProperty.cancel_left_of_respectsIso _ (pullbackSpecIso K R S).inv _).mp ?_
  convert_to! topologically _ (Spec.map <| CommRingCat.ofHom (algebraMap R (TensorProduct K R S)))
  · exact pullbackSpecIso_inv_fst ..
  let := hK.toField
  exact PrimeSpectrum.isOpenMap_comap_algebraMap_tensorProduct_of_field

end AlgebraicGeometry
