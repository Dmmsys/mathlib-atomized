/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!

# The category of type-valued sheaves is a regular epi category

This file proves that when the target category `D` is a regular epi category (i.e. every epimorphism
is regular) and has pushouts and kernel pairs of epimorphisms, the functor category `C ⥤ D` is a
regular epi category. This is an instance that applies directly when `D` is `Type*`.

-/

public section

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category C] [Category D]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: {F G : D} (f : F ⟶ G) [Epi f], HasPullback f f] [HasPushouts D]
  body: ⟨⟨{
.pt W := PullbackCone.combine f f _ (fun k => pullback.isLimit (f.app k) (f.app k))
.fst left := PullbackCone.combine f f _ (fun k => pullback.isLimit (f.app k) (f.app k))
.snd right := PullbackCone.combine f f _ (fun k => pullback.isLimit (f.app k) (f.app k))
.condition w := PullbackCone.combin

中文:
实例 [对任意
  签名: {F G : D} (f : F ⟶ G) [满态射 f], HasPullback f f] [有Pushouts D]
  定义体: ⟨⟨{
.pt W := PullbackCone.combine f f _ (fun k => pullback.isLimit (f.app k) (f.app k))
.fst left := PullbackCone.combine f f _ (fun k => pullback.isLimit (f.app k) (f.app k))
.snd right := PullbackCone.combine f f _ (fun k => pullback.isLimit (f.app k) (f.app k))
.condition w := PullbackCone.combin
-/
instance [forall {F G : D} (f : F ⟶ G) [Epi f], HasPullback f f] [HasPushouts D]
    [IsRegularEpiCategory D] :
    IsRegularEpiCategory (C ⥤ D) where
  regularEpiOfEpi {F G} f := ⟨⟨{
.pt W := PullbackCone.combine f f _ (fun k => pullback.isLimit (f.app k) (f.app k))
.fst left := PullbackCone.combine f f _ (fun k => pullback.isLimit (f.app k) (f.app k))
.snd right := PullbackCone.combine f f _ (fun k => pullback.isLimit (f.app k) (f.app k))
.condition w := PullbackCone.combine f f _ (fun k => pullback.isLimit (f.app k) (f.app k))
    isColimit := evaluationJointlyReflectsColimits _ fun k => by
      have := IsRegularEpiCategory.regularEpiOfEpi (f.app k)
      refine .equivOfNatIsoOfIso ?_ _ _ ?_ (isColimitCoforkOfEffectiveEpi (f.app k)
        (pullback.cone (f.app k) (f.app k))
        (pullback.isLimit (f.app k) (f.app k)))
      · refine NatIso.ofComponents (by rintro (_ | _); exacts [Iso.refl _, Iso.refl _]) ?_
        rintro _ _ (_ | _)
        all_goals cat_disch
· exact Cocone.ext (Iso.refl _) by rintro (_ | _ | _); all_goals cat_disch }⟩⟩

end CategoryTheory.Functor
