/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Stability properties of morphism properties on functor categories

Given `W : MorphismProperty C` and a category `J`, we study the
stability properties of `W.functorCategory J : MorphismProperty (J ⥤ C)`.

Under suitable assumptions, we also show that if monomorphisms
in `C` are stable under transfinite compositions (or coproducts),
then the same holds in the category `J ⥤ C`.

-/

public section

universe v v' v'' u u' u''

namespace CategoryTheory

open Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.IsStableUnderRetracts]
  signature: (J : Type u'') [Category.{v''} J]
  body: W.of_retract (hfg.map ((evaluation _ _).obj j)) (hg j)

中文:
实例 [W.是StableUnderRetracts]
  签名: (J : 类型u'') [范畴.{v''} J]
  定义体: W.of_retract (hfg.map ((evaluation _ _).obj j)) (hg j)

Depends on / 依赖: W.of_retract, evaluation, hfg.map, of_retract
-/
instance [W.IsStableUnderRetracts] (J : Type u'') [Category.{v''} J] :
    (W.functorCategory J).IsStableUnderRetracts where
  of_retract hfg hg j :=
    W.of_retract (hfg.map ((evaluation _ _).obj j)) (hg j)

variable {W}

/--
Instance `IsStableUnderLimitsOfShape.functorCategory` / 实例 `IsStableUnderLimitsOfShape.functorCategory`

English:
instance IsStableUnderLimitsOfShape.functorCategory
  body: MorphismProperty.limitsOfShape_le _
      (limitsOfShape.mk' (X₁ ⋙ (evaluation _ _).obj j) (X₂ ⋙ (evaluation _ _).obj j)
      _ _ (isLimitOfPreserves _ hc₁) (isLimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k => hf k j) (φ.app j) (fun k => congr_app (hφ k) j))

中文:
实例 是StableUnderLimitsOfShape.functorCategory
  定义体: MorphismProperty.limitsOfShape_le _
      (limitsOfShape.mk' (X₁ ⋙ (evaluation _ _).obj j) (X₂ ⋙ (evaluation _ _).obj j)
      _ _ (isLimitOfPreserves _ hc₁) (isLimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k => hf k j) (φ.app j) (fun k => congr_app (hφ k) j))

Depends on / 依赖: Functor, Functor.whiskerRight, MorphismProperty, MorphismProperty.limitsOfShape_le, congr_app, evaluation, isLimitOfPreserves, limitsOfShape, limitsOfShape.mk, limitsOfShape_le, whiskerRight
-/
instance IsStableUnderLimitsOfShape.functorCategory
    {K : Type u'} [Category.{v'} K] [W.IsStableUnderLimitsOfShape K]
    (J : Type u'') [Category.{v''} J] [HasLimitsOfShape K C] :
    (W.functorCategory J).IsStableUnderLimitsOfShape K where
  condition X₁ X₂ _ _ hc₁ hc₂ f hf φ hφ j :=
    MorphismProperty.limitsOfShape_le _
      (limitsOfShape.mk' (X₁ ⋙ (evaluation _ _).obj j) (X₂ ⋙ (evaluation _ _).obj j)
      _ _ (isLimitOfPreserves _ hc₁) (isLimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k => hf k j) (φ.app j) (fun k => congr_app (hφ k) j))

/--
Instance `IsStableUnderColimitsOfShape.functorCategory` / 实例 `IsStableUnderColimitsOfShape.functorCategory`

English:
instance IsStableUnderColimitsOfShape.functorCategory
  body: MorphismProperty.colimitsOfShape_le _
      (colimitsOfShape.mk' (X₁ ⋙ (evaluation _ _).obj j) (X₂ ⋙ (evaluation _ _).obj j)
      _ _ (isColimitOfPreserves _ hc₁) (isColimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k => hf k j) (φ.app j) (fun k => congr_app (hφ k) j))

中文:
实例 是StableUnderColimitsOfShape.functorCategory
  定义体: MorphismProperty.colimitsOfShape_le _
      (colimitsOfShape.mk' (X₁ ⋙ (evaluation _ _).obj j) (X₂ ⋙ (evaluation _ _).obj j)
      _ _ (isColimitOfPreserves _ hc₁) (isColimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k => hf k j) (φ.app j) (fun k => congr_app (hφ k) j))

Depends on / 依赖: Functor, Functor.whiskerRight, MorphismProperty, MorphismProperty.colimitsOfShape_le, colimitsOfShape, colimitsOfShape.mk, colimitsOfShape_le, congr_app, evaluation, isColimitOfPreserves, whiskerRight
-/
instance IsStableUnderColimitsOfShape.functorCategory
    {K : Type u'} [Category.{v'} K] [W.IsStableUnderColimitsOfShape K]
    (J : Type u'') [Category.{v''} J] [HasColimitsOfShape K C] :
    (W.functorCategory J).IsStableUnderColimitsOfShape K where
  condition X₁ X₂ _ _ hc₁ hc₂ f hf φ hφ j :=
    MorphismProperty.colimitsOfShape_le _
      (colimitsOfShape.mk' (X₁ ⋙ (evaluation _ _).obj j) (X₂ ⋙ (evaluation _ _).obj j)
      _ _ (isColimitOfPreserves _ hc₁) (isColimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k => hf k j) (φ.app j) (fun k => congr_app (hφ k) j))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.IsStableUnderBaseChange]
  signature: (J : Type u'') [Category.{v''} J] [HasPullbacks C]
  body: W.of_isPullback (sq.map ((evaluation _ _).obj j)) (hr j)

中文:
实例 [W.是StableUnderBaseChange]
  签名: (J : 类型u'') [范畴.{v''} J] [有Pullbacks C]
  定义体: W.of_isPullback (sq.map ((evaluation _ _).obj j)) (hr j)

Depends on / 依赖: W.of_isPullback, evaluation, of_isPullback, sq.map
-/
instance [W.IsStableUnderBaseChange] (J : Type u'') [Category.{v''} J] [HasPullbacks C] :
    (W.functorCategory J).IsStableUnderBaseChange where
  of_isPullback sq hr j :=
    W.of_isPullback (sq.map ((evaluation _ _).obj j)) (hr j)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.IsStableUnderCobaseChange]
  signature: (J : Type u'') [Category.{v''} J] [HasPushouts C]
  body: W.of_isPushout (sq.map ((evaluation _ _).obj j)) (hr j)

中文:
实例 [W.是StableUnderCobaseChange]
  签名: (J : 类型u'') [范畴.{v''} J] [有Pushouts C]
  定义体: W.of_isPushout (sq.map ((evaluation _ _).obj j)) (hr j)

Depends on / 依赖: W.of_isPushout, evaluation, of_isPushout, sq.map
-/
instance [W.IsStableUnderCobaseChange] (J : Type u'') [Category.{v''} J] [HasPushouts C] :
    (W.functorCategory J).IsStableUnderCobaseChange where
  of_isPushout sq hr j :=
    W.of_isPushout (sq.map ((evaluation _ _).obj j)) (hr j)

instance (K : Type u') [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K]
    [W.IsStableUnderTransfiniteCompositionOfShape K] (J : Type u'') [Category.{v''} J]
    [HasIterationOfShape K C] :
    (W.functorCategory J).IsStableUnderTransfiniteCompositionOfShape K where
  le := by
    rintro X Y f ⟨hf⟩ j
    have : W.functorCategory J <= W.inverseImage ((evaluation _ _).obj j) := fun _ _ _ h => h _
    exact W.transfiniteCompositionsOfShape_le K _ ⟨(hf.ofLE this).map⟩

variable (J : Type u'') [Category.{v''} J]

/--
lemma `functorCategory_isomorphisms` / 引理 `functorCategory_isomorphisms`

English:
lemma functorCategory_isomorphisms
  proof: by
  ext _ _ f
  simp only [functorCategory, isomorphisms.iff, NatTrans.isIso_iff_isIso_app]

中文:
引理 functorCategory_isomorphisms
  证明: by
  ext _ _ f
  simp only [functorCategory, isomorphisms.iff, NatTrans.isIso_iff_isIso_app]

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, functorCategory, isIso_iff_isIso_app, isomorphisms, isomorphisms.iff
-/
lemma functorCategory_isomorphisms :
    (isomorphisms C).functorCategory J = isomorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, isomorphisms.iff, NatTrans.isIso_iff_isIso_app]

/--
lemma `functorCategory_monomorphisms` / 引理 `functorCategory_monomorphisms`

English:
lemma functorCategory_monomorphisms
  given: [HasPullbacks C]
  proof: by
  ext _ _ f
  simp only [functorCategory, monomorphisms.iff, NatTrans.mono_iff_mono_app]

中文:
引理 functorCategory_monomorphisms
  条件: [有Pullbacks C]
  证明: by
  ext _ _ f
  simp only [functorCategory, monomorphisms.iff, NatTrans.mono_iff_mono_app]

Depends on / 依赖: NatTrans, NatTrans.mono_iff_mono_app, functorCategory, mono_iff_mono_app, monomorphisms, monomorphisms.iff
-/
lemma functorCategory_monomorphisms [HasPullbacks C] :
    (monomorphisms C).functorCategory J = monomorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, monomorphisms.iff, NatTrans.mono_iff_mono_app]

/--
lemma `functorCategory_epimorphisms` / 引理 `functorCategory_epimorphisms`

English:
lemma functorCategory_epimorphisms
  given: [HasPushouts C]
  proof: by
  ext _ _ f
  simp only [functorCategory, epimorphisms.iff, NatTrans.epi_iff_epi_app]

中文:
引理 functorCategory_epimorphisms
  条件: [有Pushouts C]
  证明: by
  ext _ _ f
  simp only [functorCategory, epimorphisms.iff, NatTrans.epi_iff_epi_app]

Depends on / 依赖: NatTrans, NatTrans.epi_iff_epi_app, epi_iff_epi_app, epimorphisms, epimorphisms.iff, functorCategory
-/
lemma functorCategory_epimorphisms [HasPushouts C] :
    (epimorphisms C).functorCategory J = epimorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, epimorphisms.iff, NatTrans.epi_iff_epi_app]

instance (K : Type u') [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K]
    [(monomorphisms C).IsStableUnderTransfiniteCompositionOfShape K]
    [HasPullbacks C] [HasIterationOfShape K C] :
    (monomorphisms (J ⥤ C)).IsStableUnderTransfiniteCompositionOfShape K := by
  rw [← functorCategory_monomorphisms]
  infer_instance

instance (K' : Type u') [(monomorphisms C).IsStableUnderCoproductsOfShape K']
    [HasCoproductsOfShape K' C] [HasPullbacks C] :
    (monomorphisms (J ⥤ C)).IsStableUnderCoproductsOfShape K' := by
  rw [← functorCategory_monomorphisms]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStableUnderCoproducts.{u'}
  signature: (monomorphisms C)]

中文:
实例 [是StableUnderCoproducts.{u'}
  签名: (monomorphisms C)]
-/
instance [IsStableUnderCoproducts.{u'} (monomorphisms C)]
    [HasCoproducts.{u'} C] [HasPullbacks C] :
    IsStableUnderCoproducts.{u'} (monomorphisms (J ⥤ C)) where

end MorphismProperty

end CategoryTheory
