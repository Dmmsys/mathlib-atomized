/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.PointwiseRightDerived

/-!
# Deriving functors using a derivability structure

Let `Φ : LocalizerMorphism W₁ W₂` be a localizer morphism between classes
of morphisms on categories `C₁` and `C₂`. Let `F : C₂ ⥤ H`.
When `Φ` is a left or right derivability structure, it allows to derive
the functor `F` (with respect to `W₂`) when `Φ.functor ⋙ F : C₁ ⥤ H`
inverts `W₁` (this is the most favorable case when we can apply the lemma
`hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure`).
We define `Φ.Derives F` as an abbreviation for `W₁.IsInvertedBy (Φ.functor ⋙ F)`.

When `h : Φ.Derives F` holds and `Φ` is a right derivability structure,
we show that `F` has a right derived functor with respect to `W₂`.
Under this assumption, if `L₂ : C₂ ⥤ D₂` is a localization functor
for `W₂`, then a functor `RF : D₂ ⥤ H` equipped with a natural
transformation `α : F ⟶ L₂ ⋙ RF` is the right derived functor of `F` iff
for any `X₁ : C₁`, the map `α.app (Φ.functor.obj X₁)` is an isomorphism.

-/

public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Limits Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {D₂ : Type u₄} [Category.{v₄} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) (F : C₂ ⥤ H)

/--
Definition of `Derives` / `Derives` 的定义

English:
abbreviation Derives
  signature: : Prop
  body: W₁.IsInvertedBy (Φ.functor ⋙ F)

中文:
缩写 Derives
  签名: : 命题
  定义体: W₁.IsInvertedBy (Φ.functor ⋙ F)

Depends on / 依赖: IsInvertedBy, functor
-/
abbrev Derives : Prop := W₁.IsInvertedBy (Φ.functor ⋙ F)

namespace Derives

variable {Φ F} (h : Φ.Derives F) [Φ.IsRightDerivabilityStructure]

include h

/--
lemma `hasPointwiseRightDerivedFunctor` / 引理 `hasPointwiseRightDerivedFunctor`

English:
lemma hasPointwiseRightDerivedFunctor
  statement: F.HasPointwiseRightDerivedFunctor W₂
  proof: by
  rw [hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure Φ F]
  exact Functor.hasPointwiseRightDerivedFunctor_of_inverts _ h

中文:
引理 hasPointwiseRightDerivedFunctor
  结论: F.HasPointwiseRightDerivedFunctor W₂
  证明: by
  rw [hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure Φ F]
  exact Functor.hasPointwiseRightDerivedFunctor_of_inverts _ h

Depends on / 依赖: Functor, Functor.hasPointwiseRightDerivedFunctor_of_inverts, hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure, hasPointwiseRightDerivedFunctor_of_inverts
-/
lemma hasPointwiseRightDerivedFunctor : F.HasPointwiseRightDerivedFunctor W₂ := by
  rw [hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure Φ F]
  exact Functor.hasPointwiseRightDerivedFunctor_of_inverts _ h

section

variable {L₂ : C₂ ⥤ D₂} [L₂.IsLocalization W₂] {RF : D₂ ⥤ H} (α : F ⟶ L₂ ⋙ RF)

/--
lemma `isIso_of_isRightDerivedFunctor` / 引理 `isIso_of_isRightDerivedFunctor`

English:
lemma isIso_of_isRightDerivedFunctor
  given: (X₁ : C₁) [RF.IsRightDerivedFunctor α W₂]
  proof: by
  let G : W₁.Localization ⥤ H := Localization.lift (Φ.functor ⋙ F) h W₁.Q
  let eG := Localization.Lifting.iso W₁.Q W₁ (Φ.functor ⋙ F) G
  have := Functor.isRightDerivedFunctor_of_inverts W₁ G eG
  have := (Φ.functor ⋙ F).hasPointwiseRightDerivedFunctor_of_inverts h
  rw [← Φ.isIso_iff_of_isRight

中文:
引理 isIso_of_isRightDerivedFunctor
  条件: (X₁ : C₁) [RF.是右导出函子 α W₂]
  证明: by
  let G : W₁.Localization ⥤ H := Localization.lift (Φ.functor ⋙ F) h W₁.Q
  let eG := Localization.Lifting.iso W₁.Q W₁ (Φ.functor ⋙ F) G
  have := Functor.isRightDerivedFunctor_of_inverts W₁ G eG
  have := (Φ.functor ⋙ F).hasPointwiseRightDerivedFunctor_of_inverts h
  rw [← Φ.isIso_iff_of_isRight

Depends on / 依赖: Functor, Functor.isRightDerivedFunctor_of_inverts, Lifting, Localization, Localization.Lifting.iso, Localization.lift, eG.inv, functor, hasPointwiseRightDerivedFunctor_of_inverts, infer_instance, isIso_iff_of_isRightDerivabilityStructure, isRightDerivedFunctor_of_inverts
-/
lemma isIso_of_isRightDerivedFunctor (X₁ : C₁) [RF.IsRightDerivedFunctor α W₂] :
    IsIso (α.app (Φ.functor.obj X₁)) := by
  let G : W₁.Localization ⥤ H := Localization.lift (Φ.functor ⋙ F) h W₁.Q
  let eG := Localization.Lifting.iso W₁.Q W₁ (Φ.functor ⋙ F) G
  have := Functor.isRightDerivedFunctor_of_inverts W₁ G eG
  have := (Φ.functor ⋙ F).hasPointwiseRightDerivedFunctor_of_inverts h
  rw [← Φ.isIso_iff_of_isRightDerivabilityStructure W₁.Q L₂ F G eG.inv RF α]
  infer_instance

@[deprecated (since := "2026-06-22")] alias isIso := isIso_of_isRightDerivedFunctor

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isRightDerivedFunctor_of_isIso` / 引理 `isRightDerivedFunctor_of_isIso`

English:
lemma isRightDerivedFunctor_of_isIso
  given: (hα : forall (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁)))
  proof: by
  have := h.hasPointwiseRightDerivedFunctor
  have := h.isIso_of_isRightDerivedFunctor (F.totalRightDerivedUnit L₂ W₂)
  have := Φ.essSurj_of_hasRightResolutions L₂
  let φ := (F.totalRightDerived L₂ W₂).rightDerivedDesc (F.totalRightDerivedUnit L₂ W₂) W₂ RF α
  have hφ : F.totalRightDerivedUnit 

中文:
引理 isRightDerivedFunctor_of_isIso
  条件: (hα : 对任意 (X₁ : C₁), 是同构 (α.app (Φ.functor.obj X₁)))
  证明: by
  have := h.hasPointwiseRightDerivedFunctor
  have := h.isIso_of_isRightDerivedFunctor (F.totalRightDerivedUnit L₂ W₂)
  have := Φ.essSurj_of_hasRightResolutions L₂
  let φ := (F.totalRightDerived L₂ W₂).rightDerivedDesc (F.totalRightDerivedUnit L₂ W₂) W₂ RF α
  have hφ : F.totalRightDerivedUnit 

Depends on / 依赖: F.totalRightDerived, F.totalRightDerivedUnit, Functor, Functor.whiskerLeft, NatTrans, NatTrans.isIso_ap, NatTrans.isIso_iff_isIso_app, essSurj_of_hasRightResolutions, h.hasPointwiseRightDerivedFunctor, h.isIso_of_isRightDerivedFunctor, hasPointwiseRightDerivedFunctor, isIso_ap, isIso_iff_isIso_app, isIso_of_isRightDerivedFunctor, rightDerivedDesc, rightDerived_fac, totalRightDerived, totalRightDerivedUnit, whiskerLeft
-/
lemma isRightDerivedFunctor_of_isIso (hα : forall (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁))) :
    RF.IsRightDerivedFunctor α W₂ := by
  have := h.hasPointwiseRightDerivedFunctor
  have := h.isIso_of_isRightDerivedFunctor (F.totalRightDerivedUnit L₂ W₂)
  have := Φ.essSurj_of_hasRightResolutions L₂
  let φ := (F.totalRightDerived L₂ W₂).rightDerivedDesc (F.totalRightDerivedUnit L₂ W₂) W₂ RF α
  have hφ : F.totalRightDerivedUnit L₂ W₂ ≫ Functor.whiskerLeft L₂ φ = α :=
    (F.totalRightDerived L₂ W₂).rightDerived_fac (F.totalRightDerivedUnit L₂ W₂) W₂ RF α
  have : IsIso φ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Y₂
    rw [NatTrans.isIso_app_iff_of_iso φ ((Φ.functor ⋙ L₂).objObjPreimageIso Y₂).symm]
    dsimp
    simp only [← hφ, NatTrans.comp_app, Functor.whiskerLeft_app, isIso_comp_left_iff] at hα
    infer_instance
  rw [← Functor.isRightDerivedFunctor_iff_of_iso (F.totalRightDerivedUnit L₂ W₂) α W₂
    (asIso φ) (by cat_disch)]
  infer_instance

/--
lemma `isRightDerivedFunctor_iff_isIso` / 引理 `isRightDerivedFunctor_iff_isIso`

English:
lemma isRightDerivedFunctor_iff_isIso
  proof: ⟨fun _ _ => h.isIso_of_isRightDerivedFunctor α _, h.isRightDerivedFunctor_of_isIso α⟩

中文:
引理 isRightDerivedFunctor_iff_isIso
  证明: ⟨fun _ _ => h.isIso_of_isRightDerivedFunctor α _, h.isRightDerivedFunctor_of_isIso α⟩

Depends on / 依赖: h.isIso_of_isRightDerivedFunctor, h.isRightDerivedFunctor_of_isIso, isIso_of_isRightDerivedFunctor, isRightDerivedFunctor_of_isIso
-/
lemma isRightDerivedFunctor_iff_isIso :
    RF.IsRightDerivedFunctor α W₂ ↔ forall (X₁ : C₁), IsIso (α.app (Φ.functor.obj X₁)) :=
  ⟨fun _ _ => h.isIso_of_isRightDerivedFunctor α _, h.isRightDerivedFunctor_of_isIso α⟩

end

end Derives

end LocalizerMorphism

end CategoryTheory
