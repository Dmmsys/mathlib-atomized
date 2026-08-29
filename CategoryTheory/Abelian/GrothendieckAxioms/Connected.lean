/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# Pulling back connected colimits

If `c` is a cocone over a functor `J ⥤ C` and `f : X ⟶ c.pt`, then for every `j : J` we can take
the pullback of `c.ι.app j` and `f`. This gives a new cocone with cone point `X`. We show that if
`c` is a colimit cocone, then this is again a colimit cocone as long as `J` is connected and `C`
has exact colimits of shape `J`.

From this we deduce a `hom_ext` principle for morphisms factoring through a colimit. Usually, we
only get `hom_ext` for morphisms *from* a colimit, so this is something a bit special.

The connectedness assumption on `J` is necessary: take `C` to be the category of abelian groups,
let `f : ℤ → ℤ ⊕ ℤ` be the diagonal map, and let `g := 𝟙 (ℤ ⊕ ℤ)`. Then the hypotheses of
`IsColimit.pullback_zero_ext` are satisfied, but `f ≫ g` is not zero.

-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.Limits

variable {J : Type w} [Category.{w'} J] [IsConnected J] {C : Type u} [Category.{v} C]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `IsColimit.pullbackOfHasExactColimitsOfShape` / `IsColimit.pullbackOfHasExactColimitsOfShape` 的定义

English:
definition IsColimit.pullbackOfHasExactColimitsOfShape
  signature: [HasPullbacks C]
  body: by
  suffices IsIso (colimMap (pullback.snd c.ι ((Functor.const J).map f))) from
    Cocone.isColimitOfIsIsoColimMapι _
  have hpull := colim.map_isPullback (IsPullback.of_hasPullback c.ι ((Functor.const J).map f))
  dsimp only [colim_obj, colim_map] at hpull
  have := hc.isIso_colimMap_ι
  apply hpull.isIso_snd_of_isIso

中文:
定义 是余极限.pullbackOfHasExactColimitsOfShape
  签名: [有Pullbacks C]
  定义体: by
  suffices IsIso (colimMap (pullback.snd c.ι ((Functor.const J).map f))) from
    Cocone.isColimitOfIsIsoColimMapι _
  have hpull := colim.map_isPullback (IsPullback.of_hasPullback c.ι ((Functor.const J).map f))
  dsimp only [colim_obj, colim_map] at hpull
  have := hc.isIso_colimMap_ι
  apply hpull.isIso_snd_of_isIso

Depends on / 依赖: Cocone, Cocone.isColimitOfIsIsoColimMap, Functor, Functor.const, IsPullback, IsPullback.of_hasPullback, colim.map_isPullback, colimMap, colim_map, colim_obj, hc.isIso_colimMap_, hpull.isIso_snd_of_isIso, isIso_snd_of_isIso, map_isPullback, of_hasPullback, pullback, pullback.snd
-/
noncomputable def IsColimit.pullbackOfHasExactColimitsOfShape [HasPullbacks C]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] {F : J ⥤ C} {c : Cocone F}
    (hc : IsColimit c) {X : C} (f : X ⟶ c.pt) :
    IsColimit (Cocone.mk _ (pullback.snd c.ι ((Functor.const J).map f))) := by
  suffices IsIso (colimMap (pullback.snd c.ι ((Functor.const J).map f))) from
    Cocone.isColimitOfIsIsoColimMapι _
  have hpull := colim.map_isPullback (IsPullback.of_hasPullback c.ι ((Functor.const J).map f))
  dsimp only [colim_obj, colim_map] at hpull
  have := hc.isIso_colimMap_ι
  apply hpull.isIso_snd_of_isIso

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsColimit.pullback_hom_ext` / 定理 `IsColimit.pullback_hom_ext`

English:
theorem IsColimit.pullback_hom_ext
  statement: [HasPullbacks C] [HasColimitsOfShape J C]
  proof: by
  refine (hc.pullbackOfHasExactColimitsOfShape f).hom_ext (fun j => ?_)
  rw [← cancel_epi (pullbackObjIso _ _ _).inv]
  simpa using! hf j

中文:
定理 是余极限.pullback_hom_ext
  结论: [有Pullbacks C] [有形状余极限 J C]
  证明: by
  refine (hc.pullbackOfHasExactColimitsOfShape f).hom_ext (fun j => ?_)
  rw [← cancel_epi (pullbackObjIso _ _ _).inv]
  simpa using! hf j

Depends on / 依赖: cancel_epi, hc.pullbackOfHasExactColimitsOfShape, hom_ext, pullbackObjIso, pullbackOfHasExactColimitsOfShape
-/
theorem IsColimit.pullback_hom_ext [HasPullbacks C] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {X Y : C}
    {f : X ⟶ c.pt} {g h : c.pt ⟶ Y}
    (hf : forall j, pullback.snd (c.ι.app j) f ≫ f ≫ g = pullback.snd (c.ι.app j) f ≫ f ≫ h) :
    f ≫ g = f ≫ h := by
  refine (hc.pullbackOfHasExactColimitsOfShape f).hom_ext (fun j => ?_)
  rw [← cancel_epi (pullbackObjIso _ _ _).inv]
  simpa using! hf j

/--
theorem `IsColimit.pullback_zero_ext` / 定理 `IsColimit.pullback_zero_ext`

English:
theorem IsColimit.pullback_zero_ext
  statement: [HasZeroMorphisms C] [HasPullbacks C] [HasColimitsOfShape J C]
  proof: by
  suffices f ≫ g = f ≫ 0 by simpa
  exact hc.pullback_hom_ext (by simpa using hf)

中文:
定理 是余极限.pullback_zero_ext
  结论: [有ZeroMorphisms C] [有Pullbacks C] [有形状余极限 J C]
  证明: by
  suffices f ≫ g = f ≫ 0 by simpa
  exact hc.pullback_hom_ext (by simpa using hf)

Depends on / 依赖: hc.pullback_hom_ext, pullback_hom_ext
-/
theorem IsColimit.pullback_zero_ext [HasZeroMorphisms C] [HasPullbacks C] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {X Y : C}
    {f : X ⟶ c.pt} {g : c.pt ⟶ Y} (hf : forall j, pullback.snd (c.ι.app j) f ≫ f ≫ g = 0) :
    f ≫ g = 0 := by
  suffices f ≫ g = f ≫ 0 by simpa
  exact hc.pullback_hom_ext (by simpa using hf)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `IsLimit.pushoutOfHasExactLimitsOfShape` / `IsLimit.pushoutOfHasExactLimitsOfShape` 的定义

English:
definition IsLimit.pushoutOfHasExactLimitsOfShape
  signature: [HasPushouts C]
  body: by
  suffices IsIso (limMap (pushout.inr c.π ((Functor.const J).map f))) from
    Cone.isLimitOfIsIsoLimMapπ _
  have hpush := lim.map_isPushout (IsPushout.of_hasPushout c.π ((Functor.const J).map f))
  dsimp only [lim_obj, lim_map] at hpush
  have := hc.isIso_limMap_π
  apply hpush.isIso_inr_of_isIso

中文:
定义 是极限.pushoutOfHasExactLimitsOfShape
  签名: [有Pushouts C]
  定义体: by
  suffices IsIso (limMap (pushout.inr c.π ((Functor.const J).map f))) from
    Cone.isLimitOfIsIsoLimMapπ _
  have hpush := lim.map_isPushout (IsPushout.of_hasPushout c.π ((Functor.const J).map f))
  dsimp only [lim_obj, lim_map] at hpush
  have := hc.isIso_limMap_π
  apply hpush.isIso_inr_of_isIso

Depends on / 依赖: Cone.isLimitOfIsIsoLimMap, Functor, Functor.const, IsPushout, IsPushout.of_hasPushout, hc.isIso_limMap_, hpush.isIso_inr_of_isIso, isIso_inr_of_isIso, lim.map_isPushout, limMap, lim_map, lim_obj, map_isPushout, of_hasPushout, pushout, pushout.inr
-/
noncomputable def IsLimit.pushoutOfHasExactLimitsOfShape [HasPushouts C]
    [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] {F : J ⥤ C} {c : Cone F}
    (hc : IsLimit c) {X : C} (f : c.pt ⟶ X) :
    IsLimit (Cone.mk _ (pushout.inr c.π ((Functor.const J).map f))) := by
  suffices IsIso (limMap (pushout.inr c.π ((Functor.const J).map f))) from
    Cone.isLimitOfIsIsoLimMapπ _
  have hpush := lim.map_isPushout (IsPushout.of_hasPushout c.π ((Functor.const J).map f))
  dsimp only [lim_obj, lim_map] at hpush
  have := hc.isIso_limMap_π
  apply hpush.isIso_inr_of_isIso

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsLimit.pushout_hom_ext` / 定理 `IsLimit.pushout_hom_ext`

English:
theorem IsLimit.pushout_hom_ext
  statement: [HasPushouts C] [HasLimitsOfShape J C]
  proof: by
  refine (hc.pushoutOfHasExactLimitsOfShape f).hom_ext (fun j => ?_)
  rw [← cancel_mono (pushoutObjIso _ _ _).hom]
  simpa using! hf j

中文:
定理 是极限.pushout_hom_ext
  结论: [有Pushouts C] [有形状极限 J C]
  证明: by
  refine (hc.pushoutOfHasExactLimitsOfShape f).hom_ext (fun j => ?_)
  rw [← cancel_mono (pushoutObjIso _ _ _).hom]
  simpa using! hf j

Depends on / 依赖: cancel_mono, hc.pushoutOfHasExactLimitsOfShape, hom_ext, pushoutObjIso, pushoutOfHasExactLimitsOfShape
-/
theorem IsLimit.pushout_hom_ext [HasPushouts C] [HasLimitsOfShape J C]
    [HasExactLimitsOfShape J C] {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) {X Y : C}
    {g h : Y ⟶ c.pt} {f : c.pt ⟶ X}
    (hf : forall j, g ≫ f ≫ pushout.inr (c.π.app j) f = h ≫ f ≫ pushout.inr (c.π.app j) f) :
    g ≫ f = h ≫ f := by
  refine (hc.pushoutOfHasExactLimitsOfShape f).hom_ext (fun j => ?_)
  rw [← cancel_mono (pushoutObjIso _ _ _).hom]
  simpa using! hf j

/--
theorem `IsLimit.pushout_zero_ext` / 定理 `IsLimit.pushout_zero_ext`

English:
theorem IsLimit.pushout_zero_ext
  statement: [HasZeroMorphisms C] [HasPushouts C] [HasLimitsOfShape J C]
  proof: by
  suffices g ≫ f = 0 ≫ f by simpa
  exact hc.pushout_hom_ext (by simpa using hf)

中文:
定理 是极限.pushout_zero_ext
  结论: [有ZeroMorphisms C] [有Pushouts C] [有形状极限 J C]
  证明: by
  suffices g ≫ f = 0 ≫ f by simpa
  exact hc.pushout_hom_ext (by simpa using hf)

Depends on / 依赖: hc.pushout_hom_ext, pushout_hom_ext
-/
theorem IsLimit.pushout_zero_ext [HasZeroMorphisms C] [HasPushouts C] [HasLimitsOfShape J C]
    [HasExactLimitsOfShape J C] {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) {X Y : C}
    {g : Y ⟶ c.pt} {f : c.pt ⟶ X} (hf : forall j, g ≫ f ≫ pushout.inr (c.π.app j) f = 0) :
    g ≫ f = 0 := by
  suffices g ≫ f = 0 ≫ f by simpa
  exact hc.pushout_hom_ext (by simpa using hf)

end CategoryTheory.Limits
