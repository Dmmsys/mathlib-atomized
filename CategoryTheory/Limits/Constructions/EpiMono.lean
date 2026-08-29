/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Relating monomorphisms and epimorphisms to limits and colimits

If `F` preserves (resp. reflects) pullbacks, then it preserves (resp. reflects) monomorphisms.

We also provide the dual version for epimorphisms.

-/

public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (F : C ⥤ D)

/--
theorem `preserves_mono_of_preservesLimit` / 定理 `preserves_mono_of_preservesLimit`

English:
theorem preserves_mono_of_preservesLimit
  statement: {X Y : C} (f : X ⟶ Y) [PreservesLimit (cospan f f) F]
  proof: by
  have := isLimitPullbackConeMapOfIsLimit F _ (PullbackCone.isLimitMkIdId f)
  simp_rw [F.map_id] at this
  apply PullbackCone.mono_of_isLimitMkIdId _ this

中文:
定理 preserves_mono_of_preservesLimit
  结论: {X Y : C} (f : X ⟶ Y) [保持极限 (cospan f f) F]
  证明: by
  have := isLimitPullbackConeMapOfIsLimit F _ (PullbackCone.isLimitMkIdId f)
  simp_rw [F.map_id] at this
  apply PullbackCone.mono_of_isLimitMkIdId _ this

Depends on / 依赖: F.map_id, PullbackCone, PullbackCone.isLimitMkIdId, PullbackCone.mono_of_isLimitMkIdId, isLimitMkIdId, isLimitPullbackConeMapOfIsLimit, map_id, mono_of_isLimitMkIdId, simp_rw
-/
theorem preserves_mono_of_preservesLimit {X Y : C} (f : X ⟶ Y) [PreservesLimit (cospan f f) F]
    [Mono f] : Mono (F.map f) := by
  have := isLimitPullbackConeMapOfIsLimit F _ (PullbackCone.isLimitMkIdId f)
  simp_rw [F.map_id] at this
  apply PullbackCone.mono_of_isLimitMkIdId _ this

instance (priority := 100) preservesMonomorphisms_of_preservesLimitsOfShape
    [PreservesLimitsOfShape WalkingCospan F] : F.PreservesMonomorphisms where
  preserves f _ := preserves_mono_of_preservesLimit F f

/--
theorem `reflects_mono_of_reflectsLimit` / 定理 `reflects_mono_of_reflectsLimit`

English:
theorem reflects_mono_of_reflectsLimit
  statement: {X Y : C} (f : X ⟶ Y) [ReflectsLimit (cospan f f) F]
  proof: by
  have := PullbackCone.isLimitMkIdId (F.map f)
  simp_rw [← F.map_id] at this
  apply PullbackCone.mono_of_isLimitMkIdId _ (isLimitOfIsLimitPullbackConeMap F _ this)

中文:
定理 reflects_mono_of_reflectsLimit
  结论: {X Y : C} (f : X ⟶ Y) [反映极限 (cospan f f) F]
  证明: by
  have := PullbackCone.isLimitMkIdId (F.map f)
  simp_rw [← F.map_id] at this
  apply PullbackCone.mono_of_isLimitMkIdId _ (isLimitOfIsLimitPullbackConeMap F _ this)

Depends on / 依赖: F.map, F.map_id, PullbackCone, PullbackCone.isLimitMkIdId, PullbackCone.mono_of_isLimitMkIdId, isLimitMkIdId, isLimitOfIsLimitPullbackConeMap, map_id, mono_of_isLimitMkIdId, simp_rw
-/
theorem reflects_mono_of_reflectsLimit {X Y : C} (f : X ⟶ Y) [ReflectsLimit (cospan f f) F]
    [Mono (F.map f)] : Mono f := by
  have := PullbackCone.isLimitMkIdId (F.map f)
  simp_rw [← F.map_id] at this
  apply PullbackCone.mono_of_isLimitMkIdId _ (isLimitOfIsLimitPullbackConeMap F _ this)

instance (priority := 100) reflectsMonomorphisms_of_reflectsLimitsOfShape
    [ReflectsLimitsOfShape WalkingCospan F] : F.ReflectsMonomorphisms where
  reflects f _ := reflects_mono_of_reflectsLimit F f

/--
theorem `preserves_epi_of_preservesColimit` / 定理 `preserves_epi_of_preservesColimit`

English:
theorem preserves_epi_of_preservesColimit
  statement: {X Y : C} (f : X ⟶ Y) [PreservesColimit (span f f) F]
  proof: by
  have := isColimitPushoutCoconeMapOfIsColimit F _ (PushoutCocone.isColimitMkIdId f)
  simp_rw [F.map_id] at this
  apply PushoutCocone.epi_of_isColimitMkIdId _ this

中文:
定理 preserves_epi_of_preservesColimit
  结论: {X Y : C} (f : X ⟶ Y) [保持余极限 (span f f) F]
  证明: by
  have := isColimitPushoutCoconeMapOfIsColimit F _ (PushoutCocone.isColimitMkIdId f)
  simp_rw [F.map_id] at this
  apply PushoutCocone.epi_of_isColimitMkIdId _ this

Depends on / 依赖: F.map_id, IsPullback, IsPullback.of_vert_isIso_mono, IsPullback.paste_vert, PushoutCocone, PushoutCocone.epi_of_isColimitMkIdId, PushoutCocone.isColimitMkIdId, epi_of_isColimitMkIdId, hasPullback, isColimitMkIdId, isColimitPushoutCoconeMapOfIsColimit, map_id, of_hasPullback, of_vert_isIso_mono, paste_vert, pullback, pullback.fst, simp_rw
-/
theorem preserves_epi_of_preservesColimit {X Y : C} (f : X ⟶ Y) [PreservesColimit (span f f) F]
    [Epi f] : Epi (F.map f) := by
  have := isColimitPushoutCoconeMapOfIsColimit F _ (PushoutCocone.isColimitMkIdId f)
  simp_rw [F.map_id] at this
  apply PushoutCocone.epi_of_isColimitMkIdId _ this

instance (priority := 100) preservesEpimorphisms_of_preservesColimitsOfShape
    [PreservesColimitsOfShape WalkingSpan F] : F.PreservesEpimorphisms where
  preserves f _ := preserves_epi_of_preservesColimit F f

/--
theorem `reflects_epi_of_reflectsColimit` / 定理 `reflects_epi_of_reflectsColimit`

English:
theorem reflects_epi_of_reflectsColimit
  statement: {X Y : C} (f : X ⟶ Y) [ReflectsColimit (span f f) F]
  proof: by
  have := PushoutCocone.isColimitMkIdId (F.map f)
  simp_rw [← F.map_id] at this
  apply
    PushoutCocone.epi_of_isColimitMkIdId _
      (isColimitOfIsColimitPushoutCoconeMap F _ this)

中文:
定理 reflects_epi_of_reflectsColimit
  结论: {X Y : C} (f : X ⟶ Y) [反映余极限 (span f f) F]
  证明: by
  have := PushoutCocone.isColimitMkIdId (F.map f)
  simp_rw [← F.map_id] at this
  apply
    PushoutCocone.epi_of_isColimitMkIdId _
      (isColimitOfIsColimitPushoutCoconeMap F _ this)

Depends on / 依赖: F.map, F.map_id, PushoutCocone, PushoutCocone.epi_of_isColimitMkIdId, PushoutCocone.isColimitMkIdId, epi_of_isColimitMkIdId, isColimitMkIdId, isColimitOfIsColimitPushoutCoconeMap, map_id, simp_rw
-/
theorem reflects_epi_of_reflectsColimit {X Y : C} (f : X ⟶ Y) [ReflectsColimit (span f f) F]
    [Epi (F.map f)] : Epi f := by
  have := PushoutCocone.isColimitMkIdId (F.map f)
  simp_rw [← F.map_id] at this
  apply
    PushoutCocone.epi_of_isColimitMkIdId _
      (isColimitOfIsColimitPushoutCoconeMap F _ this)

instance (priority := 100) reflectsEpimorphisms_of_reflectsColimitsOfShape
    [ReflectsColimitsOfShape WalkingSpan F] : F.ReflectsEpimorphisms where
  reflects f _ := reflects_epi_of_reflectsColimit F f

end CategoryTheory
