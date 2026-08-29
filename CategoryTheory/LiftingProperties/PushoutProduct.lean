/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Lifting properties and pushout-products / pullback-homs

Various equivalent lifting properties involving pushout-products and pullback-homs. For
`f : A ⟶ B`, `g : K ⟶ L`, `h : X ⟶ Y` in a monoidal closed category with pushouts and pullbacks,
`f □ g` lifts against `h` if and only if `g` lifts against `f ⋔ h`.

Special cases are considered when any of `A = ∅`, `K = ∅`, or `Y = ⋆` are true.

## References

* [Charles Rezk, *Introduction to Quasi-categories*, Proposition 21.5][Rezk2022]
-/

public section

universe v u

namespace CategoryTheory

open Limits MonoidalCategory CategoryTheory.Functor PushoutObjObj

variable {C : Type u} [Category.{v} C]

namespace MonoidalCategory.Arrow

namespace PushoutProduct

/--
lemma `hasLiftingProperty_iff` / 引理 `hasLiftingProperty_iff`

English:
lemma hasLiftingProperty_iff
  statement: [HasPushouts C] [HasPullbacks C]
  proof: ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)

中文:
引理 hasLiftingProperty_iff
  结论: [HasPushouts C] [HasPullbacks C]
  证明: ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)

Depends on / 依赖: MonoidalClosed, MonoidalClosed.internalHomAdjunction, ParametrizedAdjunction, ParametrizedAdjunction.hasLiftingProperty_iff, PullbackObjObj, PullbackObjObj.ofHasPullback, PushoutObjObj, PushoutObjObj.ofHasPushout, hasLiftingProperty_iff, ofHasPullback, ofHasPushout
-/
lemma hasLiftingProperty_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C] {X Y Z : Arrow C} :
    HasLiftingProperty (X □ Y).hom Z.hom ↔ HasLiftingProperty Y.hom ((.op X) ⋔ Z).hom :=
  ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)

/--
lemma `hasLiftingProperty_iff'` / 引理 `hasLiftingProperty_iff'`

English:
lemma hasLiftingProperty_iff'
  statement: [HasPushouts C] [HasPullbacks C]
  proof: by
  rw [← hasLiftingProperty_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) _

中文:
引理 hasLiftingProperty_iff'
  结论: [HasPushouts C] [HasPullbacks C]
  证明: by
  rw [← hasLiftingProperty_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) _

Depends on / 依赖: HasLiftingProperty, HasLiftingProperty.iff_of_arrow_iso_left, braiding, hasLiftingProperty_iff, iff_of_arrow_iso_left
-/
lemma hasLiftingProperty_iff' [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C] {X Y Z : Arrow C} :
    HasLiftingProperty (X □ Y).hom Z.hom ↔ HasLiftingProperty X.hom ((.op Y) ⋔ Z).hom := by
  rw [← hasLiftingProperty_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) _

/--
lemma `hasLiftingProperty_mk_iff` / 引理 `hasLiftingProperty_mk_iff`

English:
lemma hasLiftingProperty_mk_iff
  statement: [HasPushouts C] [HasPullbacks C]
  proof: ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)

中文:
引理 hasLiftingProperty_mk_iff
  结论: [HasPushouts C] [HasPullbacks C]
  证明: ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)

Depends on / 依赖: MonoidalClosed, MonoidalClosed.internalHomAdjunction, ParametrizedAdjunction, ParametrizedAdjunction.hasLiftingProperty_iff, PullbackObjObj, PullbackObjObj.ofHasPullback, PushoutObjObj, PushoutObjObj.ofHasPushout, hasLiftingProperty_iff, ofHasPullback, ofHasPushout
-/
lemma hasLiftingProperty_mk_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L} {h : X ⟶ Y} :
    HasLiftingProperty (f □ g).hom h ↔ HasLiftingProperty g ((.op f) ⋔ h).hom :=
  ParametrizedAdjunction.hasLiftingProperty_iff MonoidalClosed.internalHomAdjunction₂
    (PushoutObjObj.ofHasPushout ..) (PullbackObjObj.ofHasPullback ..)

/--
lemma `hasLiftingProperty_mk_iff'` / 引理 `hasLiftingProperty_mk_iff'`

English:
lemma hasLiftingProperty_mk_iff'
  statement: [HasPushouts C] [HasPullbacks C]
  proof: by
  rw [← hasLiftingProperty_mk_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) h

中文:
引理 hasLiftingProperty_mk_iff'
  结论: [HasPushouts C] [HasPullbacks C]
  证明: by
  rw [← hasLiftingProperty_mk_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) h

Depends on / 依赖: HasLiftingProperty, HasLiftingProperty.iff_of_arrow_iso_left, braiding, hasLiftingProperty_mk_iff, iff_of_arrow_iso_left
-/
lemma hasLiftingProperty_mk_iff' [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L} {h : X ⟶ Y} :
    HasLiftingProperty (f □ g).hom h ↔ HasLiftingProperty f ((.op g) ⋔ h).hom := by
  rw [← hasLiftingProperty_mk_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) h

set_option backward.defeqAttrib.useBackward true in
/--
lemma `hasLiftingProperty_mk_isInitial_iff` / 引理 `hasLiftingProperty_mk_isInitial_iff`

English:
lemma hasLiftingProperty_mk_isInitial_iff
  statement: [HasPushouts C]
  proof: by
  dsimp
  have := HasLiftingProperty.iff_of_arrow_iso_left (isInitialIso' g i (W := B)) h
  rw [dsimp% this]
  exact Adjunction.hasLiftingProperty_iff (ihom.adjunction B) g h

中文:
引理 hasLiftingProperty_mk_isInitial_iff
  结论: [HasPushouts C]
  证明: by
  dsimp
  have := HasLiftingProperty.iff_of_arrow_iso_left (isInitialIso' g i (W := B)) h
  rw [dsimp% this]
  exact Adjunction.hasLiftingProperty_iff (ihom.adjunction B) g h

Depends on / 依赖: Adjunction, Adjunction.hasLiftingProperty_iff, HasLiftingProperty, HasLiftingProperty.iff_of_arrow_iso_left, adjunction, hasLiftingProperty_iff, iff_of_arrow_iso_left, ihom.adjunction, isInitialIso
-/
lemma hasLiftingProperty_mk_isInitial_iff [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {g : K ⟶ L} {h : X ⟶ Y}
    (i : IsInitial A) :
    HasLiftingProperty (i.to B □ g).hom h ↔
      HasLiftingProperty g ((ihom B).map h) := by
  dsimp
  have := HasLiftingProperty.iff_of_arrow_iso_left (isInitialIso' g i (W := B)) h
  rw [dsimp% this]
  exact Adjunction.hasLiftingProperty_iff (ihom.adjunction B) g h

/--
lemma `hasLiftingProperty_mk_isInitial_iff'` / 引理 `hasLiftingProperty_mk_isInitial_iff'`

English:
lemma hasLiftingProperty_mk_isInitial_iff'
  statement: [HasPushouts C]
  proof: by
  rw [← hasLiftingProperty_mk_isInitial_iff i]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) h

中文:
引理 hasLiftingProperty_mk_isInitial_iff'
  结论: [HasPushouts C]
  证明: by
  rw [← hasLiftingProperty_mk_isInitial_iff i]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) h

Depends on / 依赖: HasLiftingProperty, HasLiftingProperty.iff_of_arrow_iso_left, braiding, hasLiftingProperty_mk_isInitial_iff, iff_of_arrow_iso_left
-/
lemma hasLiftingProperty_mk_isInitial_iff' [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {f : A ⟶ B} {h : X ⟶ Y}
    (i : IsInitial K) :
    HasLiftingProperty (f □ i.to L).hom h ↔
      HasLiftingProperty f ((ihom L).map h) := by
  rw [← hasLiftingProperty_mk_isInitial_iff i]
  exact HasLiftingProperty.iff_of_arrow_iso_left (braiding _ _) h

/--
lemma `hasLiftingProperty_mk_isTerminal_iff` / 引理 `hasLiftingProperty_mk_isTerminal_iff`

English:
lemma hasLiftingProperty_mk_isTerminal_iff
  statement: [HasPushouts C] [HasPullbacks C]
  proof: by
  rw [hasLiftingProperty_mk_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right g (PullbackHom.isTerminalIso _ t)

中文:
引理 hasLiftingProperty_mk_isTerminal_iff
  结论: [HasPushouts C] [HasPullbacks C]
  证明: by
  rw [hasLiftingProperty_mk_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right g (PullbackHom.isTerminalIso _ t)

Depends on / 依赖: HasLiftingProperty, HasLiftingProperty.iff_of_arrow_iso_right, PullbackHom, PullbackHom.isTerminalIso, hasLiftingProperty_mk_iff, iff_of_arrow_iso_right, isTerminalIso
-/
lemma hasLiftingProperty_mk_isTerminal_iff [HasPushouts C] [HasPullbacks C]
    [MonoidalCategory C] [MonoidalClosed C]
    {A B K L X Y : C} {f : A ⟶ B} {g : K ⟶ L}
    (t : IsTerminal Y) :
    HasLiftingProperty (f □ g).hom (t.from X) ↔
      HasLiftingProperty g ((MonoidalClosed.pre f).app X) := by
  rw [hasLiftingProperty_mk_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right g (PullbackHom.isTerminalIso _ t)

/--
lemma `hasLiftingProperty_mk_isInitial_isTerminal_iff` / 引理 `hasLiftingProperty_mk_isInitial_isTerminal_iff`

English:
lemma hasLiftingProperty_mk_isInitial_isTerminal_iff
  statement: [HasPushouts C]
  proof: by
  rw [hasLiftingProperty_mk_isInitial_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right g
    (Arrow.isoMk' _ _ (Iso.refl _) ((IsTerminal.isTerminalObj (ihom B) _ t).uniqueUpToIso t)
      (t.hom_ext _ _))

中文:
引理 hasLiftingProperty_mk_isInitial_isTerminal_iff
  结论: [HasPushouts C]
  证明: by
  rw [hasLiftingProperty_mk_isInitial_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right g
    (Arrow.isoMk' _ _ (Iso.refl _) ((IsTerminal.isTerminalObj (ihom B) _ t).uniqueUpToIso t)
      (t.hom_ext _ _))

Depends on / 依赖: Arrow.isoMk, HasLiftingProperty, HasLiftingProperty.iff_of_arrow_iso_right, IsTerminal, IsTerminal.isTerminalObj, Iso.refl, hasLiftingProperty_mk_isInitial_iff, hom_ext, iff_of_arrow_iso_right, isTerminalObj, t.hom_ext, uniqueUpToIso
-/
lemma hasLiftingProperty_mk_isInitial_isTerminal_iff [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {g : K ⟶ L}
    (i : IsInitial A) (t : IsTerminal Y) :
    HasLiftingProperty (i.to B □ g).hom (t.from X) ↔
      HasLiftingProperty g (t.from ((ihom B).obj X)) := by
  rw [hasLiftingProperty_mk_isInitial_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right g
    (Arrow.isoMk' _ _ (Iso.refl _) ((IsTerminal.isTerminalObj (ihom B) _ t).uniqueUpToIso t)
      (t.hom_ext _ _))

/--
lemma `hasLiftingProperty_mk_isInitial_isTerminal_iff'` / 引理 `hasLiftingProperty_mk_isInitial_isTerminal_iff'`

English:
lemma hasLiftingProperty_mk_isInitial_isTerminal_iff'
  statement: [HasPushouts C]
  proof: by
  rw [hasLiftingProperty_mk_isInitial_iff']
  exact HasLiftingProperty.iff_of_arrow_iso_right f
    (Arrow.isoMk' _ _ (Iso.refl _) ((IsTerminal.isTerminalObj (ihom L) _ t).uniqueUpToIso t)
      (t.hom_ext _ _))

中文:
引理 hasLiftingProperty_mk_isInitial_isTerminal_iff'
  结论: [HasPushouts C]
  证明: by
  rw [hasLiftingProperty_mk_isInitial_iff']
  exact HasLiftingProperty.iff_of_arrow_iso_right f
    (Arrow.isoMk' _ _ (Iso.refl _) ((IsTerminal.isTerminalObj (ihom L) _ t).uniqueUpToIso t)
      (t.hom_ext _ _))

Depends on / 依赖: Arrow.isoMk, HasLiftingProperty, HasLiftingProperty.iff_of_arrow_iso_right, IsTerminal, IsTerminal.isTerminalObj, Iso.refl, hasLiftingProperty_mk_isInitial_iff, hom_ext, iff_of_arrow_iso_right, isTerminalObj, t.hom_ext, uniqueUpToIso
-/
lemma hasLiftingProperty_mk_isInitial_isTerminal_iff' [HasPushouts C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]
    {A B K L X Y : C} {f : A ⟶ B}
    (i : IsInitial K) (t : IsTerminal Y) :
    HasLiftingProperty (f □ i.to L).hom (t.from X) ↔
      HasLiftingProperty f (t.from ((ihom L).obj X)) := by
  rw [hasLiftingProperty_mk_isInitial_iff']
  exact HasLiftingProperty.iff_of_arrow_iso_right f
    (Arrow.isoMk' _ _ (Iso.refl _) ((IsTerminal.isTerminalObj (ihom L) _ t).uniqueUpToIso t)
      (t.hom_ext _ _))

end PushoutProduct

end MonoidalCategory.Arrow

end CategoryTheory
