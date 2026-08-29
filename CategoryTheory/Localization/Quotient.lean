/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.CategoryTheory.Quotient

/-!
# Localization of quotient categories

Given a relation `homRel : HomRel C` on morphisms in a category `C`
and `W : MorphismProperty C`, we introduce a property
`homRel.FactorsThroughLocalization W` expressing that related
morphisms are mapped to the same morphism in the localized
category with respect to `W`. When `W` is compatible with `homRel`
(i.e. there is a class of morphisms `W'` such that
`hW : W = W'.inverseImage (Quotient.functor homRel)`),
we show that `LocalizerMorphism.ofEq hW : LocalizerMorphism W W'`
induces an equivalence on localized categories.

-/

@[expose] public section

namespace HomRel

open CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (homRel : HomRel C)

/--
Definition of `FactorsThroughLocalization` / `FactorsThroughLocalization` 的定义

English:
definition FactorsThroughLocalization
  signature: (W : MorphismProperty C)
  body: forall ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, homRel f g -> AreEqualizedByLocalization W f g

中文:
定义 FactorsThroughLocalization
  签名: (W : MorphismProperty C)
  定义体: forall ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, homRel f g -> AreEqualizedByLocalization W f g

Depends on / 依赖: AreEqualizedByLocalization, F.isoShift, additive_of_iso, homRel, isoShift
-/
def FactorsThroughLocalization (W : MorphismProperty C) : Prop :=
  forall ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, homRel f g -> AreEqualizedByLocalization W f g

variable {homRel} {W : MorphismProperty C}
  (h : homRel.FactorsThroughLocalization W)
  {W' : MorphismProperty (Quotient homRel)}
  (hW : W = W'.inverseImage (Quotient.functor homRel))

namespace FactorsThroughLocalization

open Localization

section

variable {E : Type*} [Category* E]

/--
Definition of `strictUniversalPropertyFixedTarget` / `strictUniversalPropertyFixedTarget` 的定义

English:
definition strictUniversalPropertyFixedTarget
  signature: (L' : Quotient homRel ⥤ D)
  body: univ.inverts _ (by rwa [hW] at hf)
  lift F hF :=
    univ.lift (CategoryTheory.Quotient.lift _ F
        (fun _ _ f g hfg => (h hfg).map_eq_of_isInvertedBy _ hF)) (by
      rintro K L ⟨f⟩ hf
      exact hF _ (by simpa [hW] using! hf))
  fac F hF := by rw [Functor.assoc, univ.fac, Quotient.lift_spec]
  uniq F₁ F₂ h := univ.uniq _ _ (Quotient.lift_unique' _ _ _ h)

中文:
定义 strictUniversalPropertyFixedTarget
  签名: (L' : 商 homRel ⥤ D)
  定义体: univ.inverts _ (by rwa [hW] at hf)
  lift F hF :=
    univ.lift (CategoryTheory.Quotient.lift _ F
        (fun _ _ f g hfg => (h hfg).map_eq_of_isInvertedBy _ hF)) (by
      rintro K L ⟨f⟩ hf
      exact hF _ (by simpa [hW] using! hf))
  fac F hF := by rw [Functor.assoc, univ.fac, Quotient.lift_spec]
  uniq F₁ F₂ h := univ.uniq _ _ (Quotient.lift_unique' _ _ _ h)

Depends on / 依赖: inverts, univ.inverts
-/
def strictUniversalPropertyFixedTarget (L' : Quotient homRel ⥤ D)
    (univ : StrictUniversalPropertyFixedTarget L' W' E) :
      StrictUniversalPropertyFixedTarget
        (Quotient.functor homRel ⋙ L') W E where
  inverts _ _ _ hf := univ.inverts _ (by rwa [hW] at hf)
  lift F hF :=
    univ.lift (CategoryTheory.Quotient.lift _ F
        (fun _ _ f g hfg => (h hfg).map_eq_of_isInvertedBy _ hF)) (by
      rintro K L ⟨f⟩ hf
      exact hF _ (by simpa [hW] using! hf))
  fac F hF := by rw [Functor.assoc, univ.fac, Quotient.lift_spec]
  uniq F₁ F₂ h := univ.uniq _ _ (Quotient.lift_unique' _ _ _ h)

variable (E) in
/--
Definition of `strictUniversalPropertyFixedTarget'` / `strictUniversalPropertyFixedTarget'` 的定义

English:
definition strictUniversalPropertyFixedTarget'
  signature: :
  body: strictUniversalPropertyFixedTarget h hW _ (strictUniversalPropertyFixedTargetQ W' E)

中文:
定义 strictUniversalPropertyFixedTarget'
  签名: :
  定义体: strictUniversalPropertyFixedTarget h hW _ (strictUniversalPropertyFixedTargetQ W' E)

Depends on / 依赖: strictUniversalPropertyFixedTarget, strictUniversalPropertyFixedTargetQ
-/
noncomputable def strictUniversalPropertyFixedTarget' :
    StrictUniversalPropertyFixedTarget
      (Quotient.functor homRel ⋙ W'.Q) W E :=
  strictUniversalPropertyFixedTarget h hW _ (strictUniversalPropertyFixedTargetQ W' E)

end

include h in
/--
lemma `isLocalizedEquivalence` / 引理 `isLocalizedEquivalence`

English:
lemma isLocalizedEquivalence
  proof: have : ((LocalizerMorphism.ofEq hW).functor ⋙ W'.Q).IsLocalization W :=
    Functor.IsLocalization.mk' _ _
      (h.strictUniversalPropertyFixedTarget' hW _)
      (h.strictUniversalPropertyFixedTarget' hW _)
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization _ W'.Q

中文:
引理 isLocalizedEquivalence
  证明: have : ((LocalizerMorphism.ofEq hW).functor ⋙ W'.Q).IsLocalization W :=
    Functor.IsLocalization.mk' _ _
      (h.strictUniversalPropertyFixedTarget' hW _)
      (h.strictUniversalPropertyFixedTarget' hW _)
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization _ W'.Q

Depends on / 依赖: Functor, Functor.IsLocalization.mk, IsLocalization, IsLocalizedEquivalence, LocalizerMorphism, LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization, LocalizerMorphism.ofEq, functor, h.strictUniversalPropertyFixedTarget, of_isLocalization_of_isLocalization, strictUniversalPropertyFixedTarget
-/
lemma isLocalizedEquivalence :
    (LocalizerMorphism.ofEq hW).IsLocalizedEquivalence :=
  have : ((LocalizerMorphism.ofEq hW).functor ⋙ W'.Q).IsLocalization W :=
    Functor.IsLocalization.mk' _ _
      (h.strictUniversalPropertyFixedTarget' hW _)
      (h.strictUniversalPropertyFixedTarget' hW _)
  LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization _ W'.Q

end FactorsThroughLocalization

end HomRel
