/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Unit
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite

/-!
# Limits and colimits in comma categories

We build limits in the comma category `Comma L R` provided that the two source categories have
limits and `R` preserves them.
This is used to construct limits in the arrow category, structured arrow category and under
category, and show that the appropriate forgetful functors create limits.

The duals of all the above are also given.
-/

@[expose] public section


namespace CategoryTheory

open Category Limits CategoryTheory.Functor

universe w' w v₁ v₂ v₃ u₁ u₂ u₃

variable {J : Type w} [Category.{w'} J]
variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]

namespace Comma

variable {L : A ⥤ T} {R : B ⥤ T}
variable (F : J ⥤ Comma L R)

/-- (Implementation). An auxiliary cone which is useful in order to construct limits
in the comma category. -/
@[simps!]
/--
Definition of `limitAuxiliaryCone` / `limitAuxiliaryCone` 的定义

English:
definition limitAuxiliaryCone
  signature: (c₁ : Cone (F ⋙ fst L R))
  body: (Cone.postcompose (whiskerLeft F (Comma.natTrans L R) :)).obj (L.mapCone c₁)

中文:
定义 limitAuxiliaryCone
  签名: (c₁ : Cone (F ⋙ fst L R))
  定义体: (Cone.postcompose (whiskerLeft F (Comma.natTrans L R) :)).obj (L.mapCone c₁)

Depends on / 依赖: Comma.natTrans, Cone.postcompose, L.mapCone, mapCone, natTrans, postcompose, whiskerLeft
-/
def limitAuxiliaryCone (c₁ : Cone (F ⋙ fst L R)) : Cone ((F ⋙ snd L R) ⋙ R) :=
  (Cone.postcompose (whiskerLeft F (Comma.natTrans L R) :)).obj (L.mapCone c₁)

set_option backward.defeqAttrib.useBackward true in
/-- If `R` preserves the appropriate limit, then given a cone for `F ⋙ fst L R : J ⥤ L` and a
limit cone for `F ⋙ snd L R : J ⥤ R` we can build a cone for `F` which will turn out to be a limit
cone.
-/
@[simps]
/--
Definition of `coneOfPreserves` / `coneOfPreserves` 的定义

English:
definition coneOfPreserves
  signature: [PreservesLimit (F ⋙ snd L R) R] (c₁ : Cone (F ⋙ fst L R))
  body: { left := c₁.pt
      right := c₂.pt
      hom := (isLimitOfPreserves R t₂).lift (limitAuxiliaryCone _ c₁) }
  π :=
    { app := fun j =>
        { left := c₁.π.app j
          right := c₂.π.app j
          w := ((isLimitOfPreserves R t₂).fac (limitAuxiliaryCone F c₁) j).symm }
      naturality := f

中文:
定义 coneOfPreserves
  签名: [PreservesLimit (F ⋙ snd L R) R] (c₁ : Cone (F ⋙ fst L R))
  定义体: { left := c₁.pt
      right := c₂.pt
      hom := (isLimitOfPreserves R t₂).lift (limitAuxiliaryCone _ c₁) }
  π :=
    { app := fun j =>
        { left := c₁.π.app j
          right := c₂.π.app j
          w := ((isLimitOfPreserves R t₂).fac (limitAuxiliaryCone F c₁) j).symm }
      naturality := f

Depends on / 依赖: isLimitOfPreserves, limitAuxiliaryCone, naturality
-/
noncomputable def coneOfPreserves [PreservesLimit (F ⋙ snd L R) R] (c₁ : Cone (F ⋙ fst L R))
    {c₂ : Cone (F ⋙ snd L R)} (t₂ : IsLimit c₂) : Cone F where
  pt :=
    { left := c₁.pt
      right := c₂.pt
      hom := (isLimitOfPreserves R t₂).lift (limitAuxiliaryCone _ c₁) }
  π :=
    { app := fun j =>
        { left := c₁.π.app j
          right := c₂.π.app j
          w := ((isLimitOfPreserves R t₂).fac (limitAuxiliaryCone F c₁) j).symm }
      naturality := fun j₁ j₂ t => by
        ext
        · simp [← c₁.w t]
        · simp [← c₂.w t] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `fstSndJointlyReflectLimit` / `fstSndJointlyReflectLimit` 的定义

English:
definition fstSndJointlyReflectLimit
  signature: {F : J ⥤ Comma L R} {c : Cone F}
  body: { left := h₁.lift ((fst _ _).mapCone s)
      right := h₂.lift ((snd _ _).mapCone s)
      w := (isLimitOfPreserves R h₂).hom_ext (fun j => by
        simp [← Functor.map_comp, ← Functor.map_comp_assoc, ← CommaMorphism.w,
          dsimp% h₂.fac ((snd _ _).mapCone s) j,
          dsimp% h₁.fac ((fst

中文:
定义 fstSndJointlyReflectLimit
  签名: {F : J ⥤ Comma L R} {c : Cone F}
  定义体: { left := h₁.lift ((fst _ _).mapCone s)
      right := h₂.lift ((snd _ _).mapCone s)
      w := (isLimitOfPreserves R h₂).hom_ext (fun j => by
        simp [← Functor.map_comp, ← Functor.map_comp_assoc, ← CommaMorphism.w,
          dsimp% h₂.fac ((snd _ _).mapCone s) j,
          dsimp% h₁.fac ((fst

Depends on / 依赖: CommaMorphism, CommaMorphism.w, Functor, Functor.map_comp, Functor.map_comp_assoc, hom_ext, isLimitOfPreserves, mapCone, map_comp, map_comp_assoc
-/
def fstSndJointlyReflectLimit {F : J ⥤ Comma L R} {c : Cone F}
    [PreservesLimit (F ⋙ snd _ _) R]
    (h₁ : IsLimit ((fst _ _).mapCone c))
    (h₂ : IsLimit ((snd _ _).mapCone c)) :
    IsLimit c where
  lift s :=
    { left := h₁.lift ((fst _ _).mapCone s)
      right := h₂.lift ((snd _ _).mapCone s)
      w := (isLimitOfPreserves R h₂).hom_ext (fun j => by
        simp [← Functor.map_comp, ← Functor.map_comp_assoc, ← CommaMorphism.w,
          dsimp% h₂.fac ((snd _ _).mapCone s) j,
          dsimp% h₁.fac ((fst _ _).mapCone s) j]) }
  fac s j := by
    ext
    · exact h₁.fac ((fst _ _).mapCone s) j
    · exact h₂.fac ((snd _ _).mapCone s) j
  uniq s _ hm := by
    ext
    · exact h₁.uniq ((fst _ _).mapCone s) _ (by simp [← hm])
    · exact h₂.uniq ((snd _ _).mapCone s) _ (by simp [← hm])

/--
Definition of `coneOfPreservesIsLimit` / `coneOfPreservesIsLimit` 的定义

English:
definition coneOfPreservesIsLimit
  signature: [PreservesLimit (F ⋙ snd L R) R] {c₁ : Cone (F ⋙ fst L R)}
  body: fstSndJointlyReflectLimit t₁ t₂

中文:
定义 coneOfPreservesIsLimit
  签名: [PreservesLimit (F ⋙ snd L R) R] {c₁ : Cone (F ⋙ fst L R)}
  定义体: fstSndJointlyReflectLimit t₁ t₂

Depends on / 依赖: fstSndJointlyReflectLimit
-/
noncomputable def coneOfPreservesIsLimit [PreservesLimit (F ⋙ snd L R) R] {c₁ : Cone (F ⋙ fst L R)}
    (t₁ : IsLimit c₁) {c₂ : Cone (F ⋙ snd L R)} (t₂ : IsLimit c₂) :
    IsLimit (coneOfPreserves F c₁ t₂) :=
  fstSndJointlyReflectLimit t₁ t₂

/-- (Implementation). An auxiliary cocone which is useful in order to construct colimits
in the comma category. -/
@[simps!]
/--
Definition of `colimitAuxiliaryCocone` / `colimitAuxiliaryCocone` 的定义

English:
definition colimitAuxiliaryCocone
  signature: (c₂ : Cocone (F ⋙ snd L R))
  body: (Cocone.precompose (whiskerLeft F (Comma.natTrans L R) :)).obj (R.mapCocone c₂)

中文:
定义 colimitAuxiliaryCocone
  签名: (c₂ : Cocone (F ⋙ snd L R))
  定义体: (Cocone.precompose (whiskerLeft F (Comma.natTrans L R) :)).obj (R.mapCocone c₂)

Depends on / 依赖: Cocone, Cocone.precompose, Comma.natTrans, R.mapCocone, mapCocone, natTrans, precompose, whiskerLeft
-/
def colimitAuxiliaryCocone (c₂ : Cocone (F ⋙ snd L R)) : Cocone ((F ⋙ fst L R) ⋙ L) :=
  (Cocone.precompose (whiskerLeft F (Comma.natTrans L R) :)).obj (R.mapCocone c₂)

set_option backward.defeqAttrib.useBackward true in
/--
If `L` preserves the appropriate colimit, then given a colimit cocone for `F ⋙ fst L R : J ⥤ L` and
a cocone for `F ⋙ snd L R : J ⥤ R` we can build a cocone for `F` which will turn out to be a
colimit cocone.
-/
@[simps]
/--
Definition of `coconeOfPreserves` / `coconeOfPreserves` 的定义

English:
definition coconeOfPreserves
  signature: [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst L R)}
  body: { left := c₁.pt
      right := c₂.pt
      hom := (isColimitOfPreserves L t₁).desc (colimitAuxiliaryCocone _ c₂) }
  ι :=
    { app := fun j =>
        { left := c₁.ι.app j
          right := c₂.ι.app j
          w := (isColimitOfPreserves L t₁).fac (colimitAuxiliaryCocone _ c₂) j }
      naturality

中文:
定义 coconeOfPreserves
  签名: [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst L R)}
  定义体: { left := c₁.pt
      right := c₂.pt
      hom := (isColimitOfPreserves L t₁).desc (colimitAuxiliaryCocone _ c₂) }
  ι :=
    { app := fun j =>
        { left := c₁.ι.app j
          right := c₂.ι.app j
          w := (isColimitOfPreserves L t₁).fac (colimitAuxiliaryCocone _ c₂) j }
      naturality

Depends on / 依赖: colimitAuxiliaryCocone, isColimitOfPreserves, naturality
-/
noncomputable def coconeOfPreserves [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst L R)}
    (t₁ : IsColimit c₁) (c₂ : Cocone (F ⋙ snd L R)) : Cocone F where
  pt :=
    { left := c₁.pt
      right := c₂.pt
      hom := (isColimitOfPreserves L t₁).desc (colimitAuxiliaryCocone _ c₂) }
  ι :=
    { app := fun j =>
        { left := c₁.ι.app j
          right := c₂.ι.app j
          w := (isColimitOfPreserves L t₁).fac (colimitAuxiliaryCocone _ c₂) j }
      naturality := fun j₁ j₂ t => by
        ext
        · simp [← c₁.w t]
        · simp [← c₂.w t] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `fstSndJointlyReflectColimit` / `fstSndJointlyReflectColimit` 的定义

English:
definition fstSndJointlyReflectColimit
  signature: {F : J ⥤ Comma L R} {c : Cocone F}
  body: { left := h₁.desc ((fst _ _).mapCocone s)
      right := h₂.desc ((snd _ _).mapCocone s)
      w := (isColimitOfPreserves L h₁).hom_ext (fun j => by
        simp [← Functor.map_comp_assoc, ← Functor.map_comp,
          dsimp% h₁.fac ((fst _ _).mapCocone s) j,
          dsimp% h₂.fac ((snd _ _).mapCo

中文:
定义 fstSndJointlyReflectColimit
  签名: {F : J ⥤ Comma L R} {c : Cocone F}
  定义体: { left := h₁.desc ((fst _ _).mapCocone s)
      right := h₂.desc ((snd _ _).mapCocone s)
      w := (isColimitOfPreserves L h₁).hom_ext (fun j => by
        simp [← Functor.map_comp_assoc, ← Functor.map_comp,
          dsimp% h₁.fac ((fst _ _).mapCocone s) j,
          dsimp% h₂.fac ((snd _ _).mapCo

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_comp_assoc, hom_ext, isColimitOfPreserves, mapCocone, map_comp, map_comp_assoc
-/
def fstSndJointlyReflectColimit {F : J ⥤ Comma L R} {c : Cocone F}
    [PreservesColimit (F ⋙ fst _ _) L]
    (h₁ : IsColimit ((fst _ _).mapCocone c))
    (h₂ : IsColimit ((snd _ _).mapCocone c)) :
    IsColimit c where
  desc s :=
    { left := h₁.desc ((fst _ _).mapCocone s)
      right := h₂.desc ((snd _ _).mapCocone s)
      w := (isColimitOfPreserves L h₁).hom_ext (fun j => by
        simp [← Functor.map_comp_assoc, ← Functor.map_comp,
          dsimp% h₁.fac ((fst _ _).mapCocone s) j,
          dsimp% h₂.fac ((snd _ _).mapCocone s) j]) }
  fac s j := by
    ext
    · exact h₁.fac ((fst _ _).mapCocone s) j
    · exact h₂.fac ((snd _ _).mapCocone s) j
  uniq s _ hm := by
    ext
    · exact h₁.uniq ((fst _ _).mapCocone s) _ (by simp [← hm])
    · exact h₂.uniq ((snd _ _).mapCocone s) _ (by simp [← hm])

/--
Definition of `coconeOfPreservesIsColimit` / `coconeOfPreservesIsColimit` 的定义

English:
definition coconeOfPreservesIsColimit
  signature: [PreservesColimit (F ⋙ fst L R) L]
  body: fstSndJointlyReflectColimit t₁ t₂

中文:
定义 coconeOfPreservesIsColimit
  签名: [PreservesColimit (F ⋙ fst L R) L]
  定义体: fstSndJointlyReflectColimit t₁ t₂

Depends on / 依赖: fstSndJointlyReflectColimit
-/
noncomputable def coconeOfPreservesIsColimit [PreservesColimit (F ⋙ fst L R) L]
    {c₁ : Cocone (F ⋙ fst L R)}
    (t₁ : IsColimit c₁) {c₂ : Cocone (F ⋙ snd L R)} (t₂ : IsColimit c₂) :
    IsColimit (coconeOfPreserves F t₁ c₂) :=
  fstSndJointlyReflectColimit t₁ t₂

/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: (F : J ⥤ Comma L R) [HasLimit (F ⋙ fst L R)] [HasLimit (F ⋙ snd L R)]
  body: HasLimit.mk ⟨_, coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)⟩

中文:
实例 hasLimit
  签名: (F : J ⥤ Comma L R) [HasLimit (F ⋙ fst L R)] [HasLimit (F ⋙ snd L R)]
  定义体: HasLimit.mk ⟨_, coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)⟩

Depends on / 依赖: HasLimit, HasLimit.mk, coneOfPreservesIsLimit, isLimit, limit.isLimit
-/
instance hasLimit (F : J ⥤ Comma L R) [HasLimit (F ⋙ fst L R)] [HasLimit (F ⋙ snd L R)]
    [PreservesLimit (F ⋙ snd L R) R] : HasLimit F :=
  HasLimit.mk ⟨_, coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)⟩

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [HasLimitsOfShape J A] [HasLimitsOfShape J B]

中文:
实例 hasLimitsOfShape
  签名: [HasLimitsOfShape J A] [HasLimitsOfShape J B]
-/
instance hasLimitsOfShape [HasLimitsOfShape J A] [HasLimitsOfShape J B]
    [PreservesLimitsOfShape J R] : HasLimitsOfShape J (Comma L R) where

/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: [HasLimitsOfSize.{w, w'} A] [HasLimitsOfSize.{w, w'} B]
  body: ⟨fun _ _ => inferInstance⟩

中文:
实例 hasLimitsOfSize
  签名: [HasLimitsOfSize.{w, w'} A] [HasLimitsOfSize.{w, w'} B]
  定义体: ⟨fun _ _ => inferInstance⟩
-/
instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} A] [HasLimitsOfSize.{w, w'} B]
    [PreservesLimitsOfSize.{w, w'} R] : HasLimitsOfSize.{w, w'} (Comma L R) :=
  ⟨fun _ _ => inferInstance⟩

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: [HasFiniteLimits A] [HasFiniteLimits B]
  body: inferInstance

中文:
实例 hasFiniteLimits
  签名: [HasFiniteLimits A] [HasFiniteLimits B]
  定义体: inferInstance
-/
instance hasFiniteLimits [HasFiniteLimits A] [HasFiniteLimits B]
    [PreservesFiniteLimits R] : HasFiniteLimits (Comma L R) where
      out _ _ _ := inferInstance

/--
Instance `hasColimit` / 实例 `hasColimit`

English:
instance hasColimit
  signature: (F : J ⥤ Comma L R) [HasColimit (F ⋙ fst L R)] [HasColimit (F ⋙ snd L R)]
  body: HasColimit.mk ⟨_, coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _)⟩

中文:
实例 hasColimit
  签名: (F : J ⥤ Comma L R) [HasColimit (F ⋙ fst L R)] [HasColimit (F ⋙ snd L R)]
  定义体: HasColimit.mk ⟨_, coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _)⟩

Depends on / 依赖: HasColimit, HasColimit.mk, coconeOfPreservesIsColimit, colimit, colimit.isColimit, isColimit
-/
instance hasColimit (F : J ⥤ Comma L R) [HasColimit (F ⋙ fst L R)] [HasColimit (F ⋙ snd L R)]
    [PreservesColimit (F ⋙ fst L R) L] : HasColimit F :=
  HasColimit.mk ⟨_, coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _)⟩

/--
Instance `hasColimitsOfShape` / 实例 `hasColimitsOfShape`

English:
instance hasColimitsOfShape
  signature: [HasColimitsOfShape J A] [HasColimitsOfShape J B]

中文:
实例 hasColimitsOfShape
  签名: [HasColimitsOfShape J A] [HasColimitsOfShape J B]
-/
instance hasColimitsOfShape [HasColimitsOfShape J A] [HasColimitsOfShape J B]
    [PreservesColimitsOfShape J L] : HasColimitsOfShape J (Comma L R) where

/--
Instance `hasColimitsOfSize` / 实例 `hasColimitsOfSize`

English:
instance hasColimitsOfSize
  signature: [HasColimitsOfSize.{w, w'} A] [HasColimitsOfSize.{w, w'} B]
  body: ⟨fun _ _ => inferInstance⟩

中文:
实例 hasColimitsOfSize
  签名: [HasColimitsOfSize.{w, w'} A] [HasColimitsOfSize.{w, w'} B]
  定义体: ⟨fun _ _ => inferInstance⟩
-/
instance hasColimitsOfSize [HasColimitsOfSize.{w, w'} A] [HasColimitsOfSize.{w, w'} B]
    [PreservesColimitsOfSize.{w, w'} L] : HasColimitsOfSize.{w, w'} (Comma L R) :=
  ⟨fun _ _ => inferInstance⟩

/--
Instance `hasFiniteColimits` / 实例 `hasFiniteColimits`

English:
instance hasFiniteColimits
  signature: [HasFiniteColimits A] [HasFiniteColimits B]
  body: inferInstance

中文:
实例 hasFiniteColimits
  签名: [HasFiniteColimits A] [HasFiniteColimits B]
  定义体: inferInstance
-/
instance hasFiniteColimits [HasFiniteColimits A] [HasFiniteColimits B]
    [PreservesFiniteColimits L] : HasFiniteColimits (Comma L R) where
      out _ _ _ := inferInstance

/--
Instance `preservesColimitsOfShape_fst` / 实例 `preservesColimitsOfShape_fst`

English:
instance preservesColimitsOfShape_fst
  signature: [HasColimitsOfShape J A] [HasColimitsOfShape J B]
  body: preservesColimit_of_preserves_colimit_cocone
      (coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _))
      (colimit.isColimit _)

中文:
实例 preservesColimitsOfShape_fst
  签名: [HasColimitsOfShape J A] [HasColimitsOfShape J B]
  定义体: preservesColimit_of_preserves_colimit_cocone
      (coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _))
      (colimit.isColimit _)

Depends on / 依赖: coconeOfPreservesIsColimit, colimit, colimit.isColimit, isColimit, preservesColimit_of_preserves_colimit_cocone
-/
instance preservesColimitsOfShape_fst [HasColimitsOfShape J A] [HasColimitsOfShape J B]
    [PreservesColimitsOfShape J L] : PreservesColimitsOfShape J (Comma.fst L R) where
  preservesColimit :=
    preservesColimit_of_preserves_colimit_cocone
      (coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _))
      (colimit.isColimit _)

/--
Instance `preservesColimitsOfShape_snd` / 实例 `preservesColimitsOfShape_snd`

English:
instance preservesColimitsOfShape_snd
  signature: [HasColimitsOfShape J A] [HasColimitsOfShape J B]
  body: preservesColimit_of_preserves_colimit_cocone
      (coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _))
      (colimit.isColimit _)

中文:
实例 preservesColimitsOfShape_snd
  签名: [HasColimitsOfShape J A] [HasColimitsOfShape J B]
  定义体: preservesColimit_of_preserves_colimit_cocone
      (coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _))
      (colimit.isColimit _)

Depends on / 依赖: coconeOfPreservesIsColimit, colimit, colimit.isColimit, isColimit, preservesColimit_of_preserves_colimit_cocone
-/
instance preservesColimitsOfShape_snd [HasColimitsOfShape J A] [HasColimitsOfShape J B]
    [PreservesColimitsOfShape J L] : PreservesColimitsOfShape J (Comma.snd L R) where
  preservesColimit :=
    preservesColimit_of_preserves_colimit_cocone
      (coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _))
      (colimit.isColimit _)

end Comma

namespace Arrow

set_option backward.isDefEq.respectTransparency false in
/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: (F : J ⥤ Arrow T) [i₁ : HasLimit (F ⋙ leftFunc)] [i₂ : HasLimit (F ⋙ rightFunc)]
  body: by
  have : HasLimit (F ⋙ Comma.fst _ _) := i₁
  have : HasLimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasLimit

中文:
实例 hasLimit
  签名: (F : J ⥤ Arrow T) [i₁ : HasLimit (F ⋙ leftFunc)] [i₂ : HasLimit (F ⋙ rightFunc)]
  定义体: by
  have : HasLimit (F ⋙ Comma.fst _ _) := i₁
  have : HasLimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasLimit

Depends on / 依赖: Comma.fst, Comma.hasLimit, Comma.snd, HasLimit, hasLimit
-/
instance hasLimit (F : J ⥤ Arrow T) [i₁ : HasLimit (F ⋙ leftFunc)] [i₂ : HasLimit (F ⋙ rightFunc)] :
    HasLimit F := by
  have : HasLimit (F ⋙ Comma.fst _ _) := i₁
  have : HasLimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasLimit

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [HasLimitsOfShape J T]

中文:
实例 hasLimitsOfShape
  签名: [HasLimitsOfShape J T]
-/
instance hasLimitsOfShape [HasLimitsOfShape J T] : HasLimitsOfShape J (Arrow T) where

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: [HasFiniteLimits T]
  body: inferInstance

中文:
实例 hasFiniteLimits
  签名: [HasFiniteLimits T]
  定义体: inferInstance
-/
instance hasFiniteLimits [HasFiniteLimits T] : HasFiniteLimits (Arrow T) where
  out _ _ _ := inferInstance

/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: [HasLimits T]
  body: ⟨fun _ _ => inferInstance⟩

中文:
实例 hasLimits
  签名: [HasLimits T]
  定义体: ⟨fun _ _ => inferInstance⟩
-/
instance hasLimits [HasLimits T] : HasLimits (Arrow T) :=
  ⟨fun _ _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `hasColimit` / 实例 `hasColimit`

English:
instance hasColimit
  signature: (F : J ⥤ Arrow T) [i₁ : HasColimit (F ⋙ leftFunc)]
  body: by
  have : HasColimit (F ⋙ Comma.fst _ _) := i₁
  have : HasColimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasColimit

中文:
实例 hasColimit
  签名: (F : J ⥤ Arrow T) [i₁ : HasColimit (F ⋙ leftFunc)]
  定义体: by
  have : HasColimit (F ⋙ Comma.fst _ _) := i₁
  have : HasColimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasColimit

Depends on / 依赖: Comma.fst, Comma.hasColimit, Comma.snd, HasColimit, hasColimit
-/
instance hasColimit (F : J ⥤ Arrow T) [i₁ : HasColimit (F ⋙ leftFunc)]
    [i₂ : HasColimit (F ⋙ rightFunc)] : HasColimit F := by
  have : HasColimit (F ⋙ Comma.fst _ _) := i₁
  have : HasColimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasColimit

/--
Instance `hasColimitsOfShape` / 实例 `hasColimitsOfShape`

English:
instance hasColimitsOfShape
  signature: [HasColimitsOfShape J T]

中文:
实例 hasColimitsOfShape
  签名: [HasColimitsOfShape J T]
-/
instance hasColimitsOfShape [HasColimitsOfShape J T] : HasColimitsOfShape J (Arrow T) where

/--
Instance `hasFiniteColimits` / 实例 `hasFiniteColimits`

English:
instance hasFiniteColimits
  signature: [HasFiniteColimits T]
  body: inferInstance

中文:
实例 hasFiniteColimits
  签名: [HasFiniteColimits T]
  定义体: inferInstance
-/
instance hasFiniteColimits [HasFiniteColimits T] : HasFiniteColimits (Arrow T) where
  out _ _ _ := inferInstance

/--
Instance `hasColimits` / 实例 `hasColimits`

English:
instance hasColimits
  signature: [HasColimits T]
  body: ⟨fun _ _ => inferInstance⟩

中文:
实例 hasColimits
  签名: [HasColimits T]
  定义体: ⟨fun _ _ => inferInstance⟩
-/
instance hasColimits [HasColimits T] : HasColimits (Arrow T) :=
  ⟨fun _ _ => inferInstance⟩

/--
Instance `preservesColimitsOfShape_leftFunc` / 实例 `preservesColimitsOfShape_leftFunc`

English:
instance preservesColimitsOfShape_leftFunc
  signature: [HasColimitsOfShape J T]
  body: by
  apply Comma.preservesColimitsOfShape_fst

中文:
实例 preservesColimitsOfShape_leftFunc
  签名: [HasColimitsOfShape J T]
  定义体: by
  apply Comma.preservesColimitsOfShape_fst

Depends on / 依赖: Comma.preservesColimitsOfShape_fst, preservesColimitsOfShape_fst
-/
instance preservesColimitsOfShape_leftFunc [HasColimitsOfShape J T] :
    PreservesColimitsOfShape J (Arrow.leftFunc : _ ⥤ T) := by
  apply Comma.preservesColimitsOfShape_fst

/--
Instance `preservesColimitsOfShape_rightFunc` / 实例 `preservesColimitsOfShape_rightFunc`

English:
instance preservesColimitsOfShape_rightFunc
  signature: [HasColimitsOfShape J T]
  body: by
  apply Comma.preservesColimitsOfShape_snd

中文:
实例 preservesColimitsOfShape_rightFunc
  签名: [HasColimitsOfShape J T]
  定义体: by
  apply Comma.preservesColimitsOfShape_snd

Depends on / 依赖: Comma.preservesColimitsOfShape_snd, preservesColimitsOfShape_snd
-/
instance preservesColimitsOfShape_rightFunc [HasColimitsOfShape J T] :
    PreservesColimitsOfShape J (Arrow.rightFunc : _ ⥤ T) := by
  apply Comma.preservesColimitsOfShape_snd

end Arrow

namespace StructuredArrow

variable {X : T} {G : A ⥤ T} (F : J ⥤ StructuredArrow X G)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [G.Faithful]
  signature: [G.Full] {Y : A}
  body: StructuredArrow.mkIdInitial.hasInitial

中文:
实例 [G.Faithful]
  签名: [G.Full] {Y : A}
  定义体: StructuredArrow.mkIdInitial.hasInitial

Depends on / 依赖: StructuredArrow, StructuredArrow.mkIdInitial.hasInitial, hasInitial, mkIdInitial
-/
instance [G.Faithful] [G.Full] {Y : A} : HasInitial (StructuredArrow (G.obj Y) G) :=
  StructuredArrow.mkIdInitial.hasInitial

set_option backward.isDefEq.respectTransparency false in
/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: [i₁ : HasLimit (F ⋙ proj X G)] [i₂ : PreservesLimit (F ⋙ proj X G) G]
  body: by
  have : HasLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) := i₁
  have : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) _ := i₂
  apply Comma.hasLimit

中文:
实例 hasLimit
  签名: [i₁ : HasLimit (F ⋙ proj X G)] [i₂ : PreservesLimit (F ⋙ proj X G) G]
  定义体: by
  have : HasLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) := i₁
  have : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) _ := i₂
  apply Comma.hasLimit

Depends on / 依赖: Comma.hasLimit, Comma.snd, Functor, Functor.fromPUnit, HasLimit, PreservesLimit, fromPUnit, hasLimit
-/
instance hasLimit [i₁ : HasLimit (F ⋙ proj X G)] [i₂ : PreservesLimit (F ⋙ proj X G) G] :
    HasLimit F := by
  have : HasLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) := i₁
  have : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) _ := i₂
  apply Comma.hasLimit

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [HasLimitsOfShape J A] [PreservesLimitsOfShape J G]

中文:
实例 hasLimitsOfShape
  签名: [HasLimitsOfShape J A] [PreservesLimitsOfShape J G]
-/
instance hasLimitsOfShape [HasLimitsOfShape J A] [PreservesLimitsOfShape J G] :
    HasLimitsOfShape J (StructuredArrow X G) where

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: [HasFiniteLimits A] [PreservesFiniteLimits G]
  body: inferInstance

中文:
实例 hasFiniteLimits
  签名: [HasFiniteLimits A] [PreservesFiniteLimits G]
  定义体: inferInstance
-/
instance hasFiniteLimits [HasFiniteLimits A] [PreservesFiniteLimits G] :
    HasFiniteLimits (StructuredArrow X G) where
      out _ _ _ := inferInstance

/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: [HasLimitsOfSize.{w, w'} A] [PreservesLimitsOfSize.{w, w'} G]
  body: ⟨fun J hJ => by infer_instance⟩

中文:
实例 hasLimitsOfSize
  签名: [HasLimitsOfSize.{w, w'} A] [PreservesLimitsOfSize.{w, w'} G]
  定义体: ⟨fun J hJ => by infer_instance⟩

Depends on / 依赖: infer_instance
-/
instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} A] [PreservesLimitsOfSize.{w, w'} G] :
    HasLimitsOfSize.{w, w'} (StructuredArrow X G) :=
  ⟨fun J hJ => by infer_instance⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `createsLimit` / 实例 `createsLimit`

English:
instance createsLimit
  signature: [i : PreservesLimit (F ⋙ proj X G) G]
  body: letI : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) G := i
  createsLimitOfReflectsIso fun _ t =>
    { liftedCone := Comma.coneOfPreserves F punitCone t
      makesLimit := Comma.coneOfPreservesIsLimit _ punitConeIsLimit _
      validLift := Cone.ext (Iso.refl _) fun _ => (id_comp _).symm

中文:
实例 createsLimit
  签名: [i : PreservesLimit (F ⋙ proj X G) G]
  定义体: letI : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) G := i
  createsLimitOfReflectsIso fun _ t =>
    { liftedCone := Comma.coneOfPreserves F punitCone t
      makesLimit := Comma.coneOfPreservesIsLimit _ punitConeIsLimit _
      validLift := Cone.ext (Iso.refl _) fun _ => (id_comp _).symm

Depends on / 依赖: Comma.coneOfPreserves, Comma.coneOfPreservesIsLimit, Comma.snd, Cone.ext, Functor, Functor.fromPUnit, Iso.refl, PreservesLimit, coneOfPreserves, coneOfPreservesIsLimit, createsLimitOfReflectsIso, fromPUnit, id_comp, liftedCone, makesLimit, punitCone, punitConeIsLimit, validLift
-/
noncomputable instance createsLimit [i : PreservesLimit (F ⋙ proj X G) G] :
    CreatesLimit F (proj X G) :=
  letI : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) G := i
  createsLimitOfReflectsIso fun _ t =>
    { liftedCone := Comma.coneOfPreserves F punitCone t
      makesLimit := Comma.coneOfPreservesIsLimit _ punitConeIsLimit _
      validLift := Cone.ext (Iso.refl _) fun _ => (id_comp _).symm }

/--
Instance `createsLimitsOfShape` / 实例 `createsLimitsOfShape`

English:
instance createsLimitsOfShape
  signature: [PreservesLimitsOfShape J G]

中文:
实例 createsLimitsOfShape
  签名: [PreservesLimitsOfShape J G]
-/
noncomputable instance createsLimitsOfShape [PreservesLimitsOfShape J G] :
    CreatesLimitsOfShape J (proj X G) where

/--
Instance `createsFiniteLimits` / 实例 `createsFiniteLimits`

English:
instance createsFiniteLimits
  signature: [PreservesFiniteLimits G]
  body: inferInstance

中文:
实例 createsFiniteLimits
  签名: [PreservesFiniteLimits G]
  定义体: inferInstance
-/
noncomputable instance createsFiniteLimits [PreservesFiniteLimits G] :
    CreatesFiniteLimits (proj X G) where
      createsFiniteLimits _ _ _ := inferInstance

/--
Instance `createsLimitsOfSize` / 实例 `createsLimitsOfSize`

English:
instance createsLimitsOfSize
  signature: [PreservesLimitsOfSize.{w, w'} G]

中文:
实例 createsLimitsOfSize
  签名: [PreservesLimitsOfSize.{w, w'} G]
-/
noncomputable instance createsLimitsOfSize [PreservesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (proj X G :) where

/--
Instance `mono_right_of_mono` / 实例 `mono_right_of_mono`

English:
instance mono_right_of_mono
  signature: [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
  body: show Mono ((proj X G).map f) from inferInstance

中文:
实例 mono_right_of_mono
  签名: [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
  定义体: show Mono ((proj X G).map f) from inferInstance
-/
instance mono_right_of_mono [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
    {Y Z : StructuredArrow X G} (f : Y ⟶ Z) [Mono f] : Mono f.right :=
  show Mono ((proj X G).map f) from inferInstance

/--
theorem `mono_iff_mono_right` / 定理 `mono_iff_mono_right`

English:
theorem mono_iff_mono_right
  statement: [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
  proof: ⟨fun _ => inferInstance, fun _ => mono_of_mono_right f⟩

中文:
定理 mono_iff_mono_right
  结论: [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
  证明: ⟨fun _ => inferInstance, fun _ => mono_of_mono_right f⟩

Depends on / 依赖: mono_of_mono_right
-/
theorem mono_iff_mono_right [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
    {Y Z : StructuredArrow X G} (f : Y ⟶ Z) : Mono f ↔ Mono f.right :=
  ⟨fun _ => inferInstance, fun _ => mono_of_mono_right f⟩

end StructuredArrow

namespace CostructuredArrow

variable {G : A ⥤ T} {X : T} (F : J ⥤ CostructuredArrow G X)

/--
Instance `hasTerminal` / 实例 `hasTerminal`

English:
instance hasTerminal
  signature: [G.Faithful] [G.Full] {Y : A}
  body: CostructuredArrow.mkIdTerminal.hasTerminal

中文:
实例 hasTerminal
  签名: [G.Faithful] [G.Full] {Y : A}
  定义体: CostructuredArrow.mkIdTerminal.hasTerminal

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mkIdTerminal.hasTerminal, hasTerminal, mkIdTerminal
-/
instance hasTerminal [G.Faithful] [G.Full] {Y : A} :
    HasTerminal (CostructuredArrow G (G.obj Y)) :=
  CostructuredArrow.mkIdTerminal.hasTerminal

set_option backward.isDefEq.respectTransparency false in
/--
Instance `hasColimit` / 实例 `hasColimit`

English:
instance hasColimit
  signature: [i₁ : HasColimit (F ⋙ proj G X)] [i₂ : PreservesColimit (F ⋙ proj G X) G]
  body: by
  have : HasColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) := i₁
  have : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) _ := i₂
  apply Comma.hasColimit

中文:
实例 hasColimit
  签名: [i₁ : HasColimit (F ⋙ proj G X)] [i₂ : PreservesColimit (F ⋙ proj G X) G]
  定义体: by
  have : HasColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) := i₁
  have : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) _ := i₂
  apply Comma.hasColimit

Depends on / 依赖: Comma.fst, Comma.hasColimit, Functor, Functor.fromPUnit, HasColimit, PreservesColimit, fromPUnit, hasColimit
-/
instance hasColimit [i₁ : HasColimit (F ⋙ proj G X)] [i₂ : PreservesColimit (F ⋙ proj G X) G] :
    HasColimit F := by
  have : HasColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) := i₁
  have : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) _ := i₂
  apply Comma.hasColimit

/--
Instance `hasColimitsOfShape` / 实例 `hasColimitsOfShape`

English:
instance hasColimitsOfShape
  signature: [HasColimitsOfShape J A] [PreservesColimitsOfShape J G]

中文:
实例 hasColimitsOfShape
  签名: [HasColimitsOfShape J A] [PreservesColimitsOfShape J G]
-/
instance hasColimitsOfShape [HasColimitsOfShape J A] [PreservesColimitsOfShape J G] :
    HasColimitsOfShape J (CostructuredArrow G X) where

/--
Instance `hasFiniteColimits` / 实例 `hasFiniteColimits`

English:
instance hasFiniteColimits
  signature: [HasFiniteColimits A] [PreservesFiniteColimits G]
  body: inferInstance

中文:
实例 hasFiniteColimits
  签名: [HasFiniteColimits A] [PreservesFiniteColimits G]
  定义体: inferInstance
-/
instance hasFiniteColimits [HasFiniteColimits A] [PreservesFiniteColimits G] :
    HasFiniteColimits (CostructuredArrow G X) where
      out _ _ _ := inferInstance

/--
Instance `hasColimitsOfSize` / 实例 `hasColimitsOfSize`

English:
instance hasColimitsOfSize
  signature: [HasColimitsOfSize.{w, w'} A] [PreservesColimitsOfSize.{w, w'} G]
  body: ⟨fun _ _ => inferInstance⟩

中文:
实例 hasColimitsOfSize
  签名: [HasColimitsOfSize.{w, w'} A] [PreservesColimitsOfSize.{w, w'} G]
  定义体: ⟨fun _ _ => inferInstance⟩
-/
instance hasColimitsOfSize [HasColimitsOfSize.{w, w'} A] [PreservesColimitsOfSize.{w, w'} G] :
    HasColimitsOfSize.{w, w'} (CostructuredArrow G X) :=
  ⟨fun _ _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `createsColimit` / 实例 `createsColimit`

English:
instance createsColimit
  signature: [i : PreservesColimit (F ⋙ proj G X) G]
  body: letI : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) G := i
  createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := Comma.coconeOfPreserves F t punitCocone
      makesColimit := Comma.coconeOfPreservesIsColimit _ _ punitCoconeIsColimit
      validLift := Cocone.ext (Iso.refl _) fun

中文:
实例 createsColimit
  签名: [i : PreservesColimit (F ⋙ proj G X) G]
  定义体: letI : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) G := i
  createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := Comma.coconeOfPreserves F t punitCocone
      makesColimit := Comma.coconeOfPreservesIsColimit _ _ punitCoconeIsColimit
      validLift := Cocone.ext (Iso.refl _) fun

Depends on / 依赖: Cocone, Cocone.ext, Comma.coconeOfPreserves, Comma.coconeOfPreservesIsColimit, Comma.fst, Functor, Functor.fromPUnit, Iso.refl, PreservesColimit, coconeOfPreserves, coconeOfPreservesIsColimit, comp_id, createsColimitOfReflectsIso, fromPUnit, liftedCocone, makesColimit, punitCocone, punitCoconeIsColimit, validLift
-/
noncomputable instance createsColimit [i : PreservesColimit (F ⋙ proj G X) G] :
    CreatesColimit F (proj G X) :=
  letI : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) G := i
  createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := Comma.coconeOfPreserves F t punitCocone
      makesColimit := Comma.coconeOfPreservesIsColimit _ _ punitCoconeIsColimit
      validLift := Cocone.ext (Iso.refl _) fun _ => comp_id _ }

/--
Instance `createsColimitsOfShape` / 实例 `createsColimitsOfShape`

English:
instance createsColimitsOfShape
  signature: [PreservesColimitsOfShape J G]

中文:
实例 createsColimitsOfShape
  签名: [PreservesColimitsOfShape J G]
-/
noncomputable instance createsColimitsOfShape [PreservesColimitsOfShape J G] :
    CreatesColimitsOfShape J (proj G X) where

/--
Instance `createsFiniteColimits` / 实例 `createsFiniteColimits`

English:
instance createsFiniteColimits
  signature: [PreservesFiniteColimits G]
  body: inferInstance

中文:
实例 createsFiniteColimits
  签名: [PreservesFiniteColimits G]
  定义体: inferInstance
-/
noncomputable instance createsFiniteColimits [PreservesFiniteColimits G] :
    CreatesFiniteColimits (proj G X) where
      createsFiniteColimits _ _ _ := inferInstance

/--
Instance `createsColimitsOfSize` / 实例 `createsColimitsOfSize`

English:
instance createsColimitsOfSize
  signature: [PreservesColimitsOfSize.{w, w'} G]

中文:
实例 createsColimitsOfSize
  签名: [PreservesColimitsOfSize.{w, w'} G]
-/
noncomputable instance createsColimitsOfSize [PreservesColimitsOfSize.{w, w'} G] :
    CreatesColimitsOfSize.{w, w'} (proj G X :) where

/--
Instance `epi_left_of_epi` / 实例 `epi_left_of_epi`

English:
instance epi_left_of_epi
  signature: [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
  body: show Epi ((proj G X).map f) from inferInstance

中文:
实例 epi_left_of_epi
  签名: [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
  定义体: show Epi ((proj G X).map f) from inferInstance
-/
instance epi_left_of_epi [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
    {Y Z : CostructuredArrow G X} (f : Y ⟶ Z) [Epi f] : Epi f.left :=
  show Epi ((proj G X).map f) from inferInstance

/--
theorem `epi_iff_epi_left` / 定理 `epi_iff_epi_left`

English:
theorem epi_iff_epi_left
  statement: [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
  proof: ⟨fun _ => inferInstance, fun _ => epi_of_epi_left f⟩

中文:
定理 epi_iff_epi_left
  结论: [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
  证明: ⟨fun _ => inferInstance, fun _ => epi_of_epi_left f⟩

Depends on / 依赖: epi_of_epi_left
-/
theorem epi_iff_epi_left [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
    {Y Z : CostructuredArrow G X} (f : Y ⟶ Z) : Epi f ↔ Epi f.left :=
  ⟨fun _ => inferInstance, fun _ => epi_of_epi_left f⟩

end CostructuredArrow

namespace Over

instance {X : T} : HasTerminal (Over X) := CostructuredArrow.hasTerminal

end Over

namespace Under

instance {X : T} : HasInitial (Under X) := Under.mkIdInitial.hasInitial

end Under

end CategoryTheory
