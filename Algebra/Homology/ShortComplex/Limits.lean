/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Limits and colimits in the category of short complexes

In this file, it is shown if a category `C` with zero morphisms has limits
of a certain shape `J`, then it is also the case of the category `ShortComplex C`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits CategoryTheory.Functor

variable {J C : Type*} [Category* J] [Category* C] [HasZeroMorphisms C]
  {F : J ⥤ ShortComplex C}

namespace ShortComplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitOfIsLimitπ` / `isLimitOfIsLimitπ` 的定义

English:
definition isLimitOfIsLimitπ
  signature: (c : Cone F)
  body: { τ₁ := h₁.lift (π₁.mapCone s)
      τ₂ := h₂.lift (π₂.mapCone s)
      τ₃ := h₃.lift (π₃.mapCone s)
      comm₁₂ := h₂.hom_ext (fun j => by
        have eq₁ := h₁.fac (π₁.mapCone s)
        have eq₂ := h₂.fac (π₂.mapCone s)
        have eq₁₂ := fun j => (c.π.app j).comm₁₂
        have eq₁₂' := fun j => (s.π.app j).comm₁₂
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        rw [assoc]; rw [assoc]; rw [← eq₁₂]; rw [reassoc_of% eq₁]; rw [eq₂]; rw [eq₁₂'])
      comm₂₃ := h₃.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCone s)
        have eq₃ := h₃.fac (π₃.mapCone s)
        have eq₂₃ := fun j => (c.π.app j).comm₂₃
        have eq₂₃' := fun j => (s.π.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [assoc]; rw [assoc]; rw [← eq₂₃]; rw [reassoc_of% eq₂]; rw [eq₃]; rw [eq₂₃']) }
  fac s j := by ext <;> apply IsLimit.fac
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCone s) _ (fun j => π₁.congr_map (hm j))
    · exact h₂.uniq (π₂.mapCone s) _ (fun j => π₂.congr_map (hm j))
    · exact h₃.uniq (π₃.mapCone s) _ (fun j => π₃.congr_map (hm j))

中文:
定义 isLimitOfIsLimitπ
  签名: (c : 锥 F)
  定义体: { τ₁ := h₁.lift (π₁.mapCone s)
      τ₂ := h₂.lift (π₂.mapCone s)
      τ₃ := h₃.lift (π₃.mapCone s)
      comm₁₂ := h₂.hom_ext (fun j => by
        have eq₁ := h₁.fac (π₁.mapCone s)
        have eq₂ := h₂.fac (π₂.mapCone s)
        have eq₁₂ := fun j => (c.π.app j).comm₁₂
        have eq₁₂' := fun j => (s.π.app j).comm₁₂
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        rw [assoc]; rw [assoc]; rw [← eq₁₂]; rw [reassoc_of% eq₁]; rw [eq₂]; rw [eq₁₂'])
      comm₂₃ := h₃.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCone s)
        have eq₃ := h₃.fac (π₃.mapCone s)
        have eq₂₃ := fun j => (c.π.app j).comm₂₃
        have eq₂₃' := fun j => (s.π.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [assoc]; rw [assoc]; rw [← eq₂₃]; rw [reassoc_of% eq₂]; rw [eq₃]; rw [eq₂₃']) }
  fac s j := by ext <;> apply IsLimit.fac
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCone s) _ (fun j => π₁.congr_map (hm j))
    · exact h₂.uniq (π₂.mapCone s) _ (fun j => π₂.congr_map (hm j))
    · exact h₃.uniq (π₃.mapCone s) _ (fun j => π₃.congr_map (hm j))

Depends on / 依赖: hom_ext, mapCone, reassoc_of
-/
def isLimitOfIsLimitπ (c : Cone F)
    (h₁ : IsLimit (π₁.mapCone c)) (h₂ : IsLimit (π₂.mapCone c))
    (h₃ : IsLimit (π₃.mapCone c)) : IsLimit c where
  lift s :=
    { τ₁ := h₁.lift (π₁.mapCone s)
      τ₂ := h₂.lift (π₂.mapCone s)
      τ₃ := h₃.lift (π₃.mapCone s)
      comm₁₂ := h₂.hom_ext (fun j => by
        have eq₁ := h₁.fac (π₁.mapCone s)
        have eq₂ := h₂.fac (π₂.mapCone s)
        have eq₁₂ := fun j => (c.π.app j).comm₁₂
        have eq₁₂' := fun j => (s.π.app j).comm₁₂
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        rw [assoc]; rw [assoc]; rw [← eq₁₂]; rw [reassoc_of% eq₁]; rw [eq₂]; rw [eq₁₂'])
      comm₂₃ := h₃.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCone s)
        have eq₃ := h₃.fac (π₃.mapCone s)
        have eq₂₃ := fun j => (c.π.app j).comm₂₃
        have eq₂₃' := fun j => (s.π.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [assoc]; rw [assoc]; rw [← eq₂₃]; rw [reassoc_of% eq₂]; rw [eq₃]; rw [eq₂₃']) }
  fac s j := by ext <;> apply IsLimit.fac
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCone s) _ (fun j => π₁.congr_map (hm j))
    · exact h₂.uniq (π₂.mapCone s) _ (fun j => π₂.congr_map (hm j))
    · exact h₃.uniq (π₃.mapCone s) _ (fun j => π₃.congr_map (hm j))

section

variable (F)
variable [HasLimit (F ⋙ π₁)] [HasLimit (F ⋙ π₂)] [HasLimit (F ⋙ π₃)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F
  body: Cone.mk (ShortComplex.mk (limMap (whiskerLeft F π₁Toπ₂)) (limMap (whiskerLeft F π₂Toπ₃))
      (by cat_disch))
    { app := fun j => Hom.mk (limit.π _ _) (limit.π _ _) (limit.π _ _)
        (by simp) (by simp)
      naturality := fun _ _ f => by
        ext <;> simp [← limit.w _ f] }

中文:
定义 limitCone
  签名: : 锥 F
  定义体: Cone.mk (ShortComplex.mk (limMap (whiskerLeft F π₁Toπ₂)) (limMap (whiskerLeft F π₂Toπ₃))
      (by cat_disch))
    { app := fun j => Hom.mk (limit.π _ _) (limit.π _ _) (limit.π _ _)
        (by simp) (by simp)
      naturality := fun _ _ f => by
        ext <;> simp [← limit.w _ f] }

Depends on / 依赖: Cone.mk, Hom.mk, ShortComplex, ShortComplex.mk, cat_disch, limMap, limit.w, naturality, whiskerLeft
-/
noncomputable def limitCone : Cone F :=
  Cone.mk (ShortComplex.mk (limMap (whiskerLeft F π₁Toπ₂)) (limMap (whiskerLeft F π₂Toπ₃))
      (by cat_disch))
    { app := fun j => Hom.mk (limit.π _ _) (limit.π _ _) (limit.π _ _)
        (by simp) (by simp)
      naturality := fun _ _ f => by
        ext <;> simp [← limit.w _ f] }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitπ₁MapConeLimitCone` / `isLimitπ₁MapConeLimitCone` 的定义

English:
definition isLimitπ₁MapConeLimitCone
  signature: : IsLimit (π₁.mapCone (limitCone F))
  body: (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

中文:
定义 isLimitπ₁MapConeLimitCone
  签名: : 是极限 (π₁.mapCone (limitCone F))
  定义体: (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.ofIsoLimit, Iso.refl, cat_disch, isLimit, limit.isLimit, ofIsoLimit
-/
noncomputable def isLimitπ₁MapConeLimitCone : IsLimit (π₁.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitπ₂MapConeLimitCone` / `isLimitπ₂MapConeLimitCone` 的定义

English:
definition isLimitπ₂MapConeLimitCone
  signature: : IsLimit (π₂.mapCone (limitCone F))
  body: (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

中文:
定义 isLimitπ₂MapConeLimitCone
  签名: : 是极限 (π₂.mapCone (limitCone F))
  定义体: (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.ofIsoLimit, Iso.refl, cat_disch, isLimit, limit.isLimit, ofIsoLimit
-/
noncomputable def isLimitπ₂MapConeLimitCone : IsLimit (π₂.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitπ₃MapConeLimitCone` / `isLimitπ₃MapConeLimitCone` 的定义

English:
definition isLimitπ₃MapConeLimitCone
  signature: : IsLimit (π₃.mapCone (limitCone F))
  body: (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

中文:
定义 isLimitπ₃MapConeLimitCone
  签名: : 是极限 (π₃.mapCone (limitCone F))
  定义体: (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.ofIsoLimit, Iso.refl, cat_disch, isLimit, limit.isLimit, ofIsoLimit
-/
noncomputable def isLimitπ₃MapConeLimitCone : IsLimit (π₃.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

/--
Definition of `isLimitLimitCone` / `isLimitLimitCone` 的定义

English:
definition isLimitLimitCone
  signature: : IsLimit (limitCone F)
  body: isLimitOfIsLimitπ _ (isLimitπ₁MapConeLimitCone F)
    (isLimitπ₂MapConeLimitCone F) (isLimitπ₃MapConeLimitCone F)

中文:
定义 isLimitLimitCone
  签名: : 是极限 (limitCone F)
  定义体: isLimitOfIsLimitπ _ (isLimitπ₁MapConeLimitCone F)
    (isLimitπ₂MapConeLimitCone F) (isLimitπ₃MapConeLimitCone F)
-/
noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  isLimitOfIsLimitπ _ (isLimitπ₁MapConeLimitCone F)
    (isLimitπ₂MapConeLimitCone F) (isLimitπ₃MapConeLimitCone F)

/--
Instance `hasLimit_of_hasLimitπ` / 实例 `hasLimit_of_hasLimitπ`

English:
instance hasLimit_of_hasLimitπ
  signature: : HasLimit F
  body: ⟨⟨⟨_, isLimitLimitCone _⟩⟩⟩

中文:
实例 hasLimit_of_hasLimitπ
  签名: : 有极限 F
  定义体: ⟨⟨⟨_, isLimitLimitCone _⟩⟩⟩

Depends on / 依赖: isLimitLimitCone
-/
instance hasLimit_of_hasLimitπ : HasLimit F := ⟨⟨⟨_, isLimitLimitCone _⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimit F π₁
  body: preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₁MapConeLimitCone F)

中文:
实例 :
  签名: 保持极限 F π₁
  定义体: preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₁MapConeLimitCone F)

Depends on / 依赖: isLimitLimitCone, preservesLimit_of_preserves_limit_cone
-/
noncomputable instance : PreservesLimit F π₁ :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₁MapConeLimitCone F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimit F π₂
  body: preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₂MapConeLimitCone F)

中文:
实例 :
  签名: 保持极限 F π₂
  定义体: preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₂MapConeLimitCone F)

Depends on / 依赖: isLimitLimitCone, preservesLimit_of_preserves_limit_cone
-/
noncomputable instance : PreservesLimit F π₂ :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₂MapConeLimitCone F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimit F π₃
  body: preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₃MapConeLimitCone F)

中文:
实例 :
  签名: 保持极限 F π₃
  定义体: preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₃MapConeLimitCone F)

Depends on / 依赖: isLimitLimitCone, preservesLimit_of_preserves_limit_cone
-/
noncomputable instance : PreservesLimit F π₃ :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₃MapConeLimitCone F)

end

section

variable [HasLimitsOfShape J C]

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: :

中文:
实例 hasLimitsOfShape
  签名: :

Depends on / 依赖: H.IsCartanSubalgebra, IsCartanSubalgebra, LieSubalgebra, Nontrivial
-/
instance hasLimitsOfShape :
    HasLimitsOfShape J (ShortComplex C) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfShape J (π₁ : _ ⥤ C)

中文:
实例 :
  签名: 保持形状极限 J (π₁ : _ ⥤ C)
-/
noncomputable instance : PreservesLimitsOfShape J (π₁ : _ ⥤ C) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfShape J (π₂ : _ ⥤ C)

中文:
实例 :
  签名: 保持形状极限 J (π₂ : _ ⥤ C)
-/
noncomputable instance : PreservesLimitsOfShape J (π₂ : _ ⥤ C) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfShape J (π₃ : _ ⥤ C)

中文:
实例 :
  签名: 保持形状极限 J (π₃ : _ ⥤ C)
-/
noncomputable instance : PreservesLimitsOfShape J (π₃ : _ ⥤ C) where

end

section

variable [HasFiniteLimits C]

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: : HasFiniteLimits (ShortComplex C)
  body: ⟨fun _ _ _ => inferInstance⟩

中文:
实例 hasFiniteLimits
  签名: : 有有限极限 (短复形 C)
  定义体: ⟨fun _ _ _ => inferInstance⟩
-/
instance hasFiniteLimits : HasFiniteLimits (ShortComplex C) :=
  ⟨fun _ _ _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (π₁ : _ ⥤ C)
  body: ⟨fun _ _ _ => inferInstance⟩

中文:
实例 :
  签名: 保持FiniteLimits (π₁ : _ ⥤ C)
  定义体: ⟨fun _ _ _ => inferInstance⟩
-/
noncomputable instance : PreservesFiniteLimits (π₁ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (π₂ : _ ⥤ C)
  body: ⟨fun _ _ _ => inferInstance⟩

中文:
实例 :
  签名: 保持FiniteLimits (π₂ : _ ⥤ C)
  定义体: ⟨fun _ _ _ => inferInstance⟩
-/
noncomputable instance : PreservesFiniteLimits (π₂ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (π₃ : _ ⥤ C)
  body: ⟨fun _ _ _ => inferInstance⟩

中文:
实例 :
  签名: 保持FiniteLimits (π₃ : _ ⥤ C)
  定义体: ⟨fun _ _ _ => inferInstance⟩
-/
noncomputable instance : PreservesFiniteLimits (π₃ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

end

section

variable [HasLimitsOfShape WalkingCospan C]

/--
Instance `preservesMonomorphisms_π₁` / 实例 `preservesMonomorphisms_π₁`

English:
instance preservesMonomorphisms_π₁
  signature: :
  body: CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

中文:
实例 preservesMonomorphisms_π₁
  签名: :
  定义体: CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

Depends on / 依赖: CategoryTheory, CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape, preservesMonomorphisms_of_preservesLimitsOfShape
-/
instance preservesMonomorphisms_π₁ :
    Functor.PreservesMonomorphisms (π₁ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

/--
Instance `preservesMonomorphisms_π₂` / 实例 `preservesMonomorphisms_π₂`

English:
instance preservesMonomorphisms_π₂
  signature: :
  body: CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

中文:
实例 preservesMonomorphisms_π₂
  签名: :
  定义体: CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

Depends on / 依赖: CategoryTheory, CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape, preservesMonomorphisms_of_preservesLimitsOfShape
-/
instance preservesMonomorphisms_π₂ :
    Functor.PreservesMonomorphisms (π₂ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

/--
Instance `preservesMonomorphisms_π₃` / 实例 `preservesMonomorphisms_π₃`

English:
instance preservesMonomorphisms_π₃
  signature: :
  body: CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

中文:
实例 preservesMonomorphisms_π₃
  签名: :
  定义体: CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

Depends on / 依赖: CategoryTheory, CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape, preservesMonomorphisms_of_preservesLimitsOfShape
-/
instance preservesMonomorphisms_π₃ :
    Functor.PreservesMonomorphisms (π₃ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitOfIsColimitπ` / `isColimitOfIsColimitπ` 的定义

English:
definition isColimitOfIsColimitπ
  signature: (c : Cocone F)
  body: { τ₁ := h₁.desc (π₁.mapCocone s)
      τ₂ := h₂.desc (π₂.mapCocone s)
      τ₃ := h₃.desc (π₃.mapCocone s)
      comm₁₂ := h₁.hom_ext (fun j => by
        have eq₁ := h₁.fac (π₁.mapCocone s)
        have eq₂ := h₂.fac (π₂.mapCocone s)
        have eq₁₂ := fun j => (c.ι.app j).comm₁₂
        have eq₁₂' := fun j => (s.ι.app j).comm₁₂
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        rw [reassoc_of% (eq₁ j)]; rw [eq₁₂']; rw [reassoc_of% eq₁₂]; rw [eq₂])
      comm₂₃ := h₂.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCocone s)
        have eq₃ := h₃.fac (π₃.mapCocone s)
        have eq₂₃ := fun j => (c.ι.app j).comm₂₃
        have eq₂₃' := fun j => (s.ι.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [reassoc_of% (eq₂ j)]; rw [eq₂₃']; rw [reassoc_of% eq₂₃]; rw [eq₃]) }
  fac s j := by
    ext
    · apply IsColimit.fac h₁
    · apply IsColimit.fac h₂
    · apply IsColimit.fac h₃
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCocone s) _ (fun j => π₁.congr_map (hm j))
    · exact h₂.uniq (π₂.mapCocone s) _ (fun j => π₂.congr_map (hm j))
    · exact h₃.uniq (π₃.mapCocone s) _ (fun j => π₃.congr_map (hm j))

中文:
定义 isColimitOfIsColimitπ
  签名: (c : 余锥 F)
  定义体: { τ₁ := h₁.desc (π₁.mapCocone s)
      τ₂ := h₂.desc (π₂.mapCocone s)
      τ₃ := h₃.desc (π₃.mapCocone s)
      comm₁₂ := h₁.hom_ext (fun j => by
        have eq₁ := h₁.fac (π₁.mapCocone s)
        have eq₂ := h₂.fac (π₂.mapCocone s)
        have eq₁₂ := fun j => (c.ι.app j).comm₁₂
        have eq₁₂' := fun j => (s.ι.app j).comm₁₂
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        rw [reassoc_of% (eq₁ j)]; rw [eq₁₂']; rw [reassoc_of% eq₁₂]; rw [eq₂])
      comm₂₃ := h₂.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCocone s)
        have eq₃ := h₃.fac (π₃.mapCocone s)
        have eq₂₃ := fun j => (c.ι.app j).comm₂₃
        have eq₂₃' := fun j => (s.ι.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [reassoc_of% (eq₂ j)]; rw [eq₂₃']; rw [reassoc_of% eq₂₃]; rw [eq₃]) }
  fac s j := by
    ext
    · apply IsColimit.fac h₁
    · apply IsColimit.fac h₂
    · apply IsColimit.fac h₃
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCocone s) _ (fun j => π₁.congr_map (hm j))
    · exact h₂.uniq (π₂.mapCocone s) _ (fun j => π₂.congr_map (hm j))
    · exact h₃.uniq (π₃.mapCocone s) _ (fun j => π₃.congr_map (hm j))

Depends on / 依赖: hom_ext, mapCocone, reassoc_of
-/
def isColimitOfIsColimitπ (c : Cocone F)
    (h₁ : IsColimit (π₁.mapCocone c)) (h₂ : IsColimit (π₂.mapCocone c))
    (h₃ : IsColimit (π₃.mapCocone c)) : IsColimit c where
  desc s :=
    { τ₁ := h₁.desc (π₁.mapCocone s)
      τ₂ := h₂.desc (π₂.mapCocone s)
      τ₃ := h₃.desc (π₃.mapCocone s)
      comm₁₂ := h₁.hom_ext (fun j => by
        have eq₁ := h₁.fac (π₁.mapCocone s)
        have eq₂ := h₂.fac (π₂.mapCocone s)
        have eq₁₂ := fun j => (c.ι.app j).comm₁₂
        have eq₁₂' := fun j => (s.ι.app j).comm₁₂
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        rw [reassoc_of% (eq₁ j)]; rw [eq₁₂']; rw [reassoc_of% eq₁₂]; rw [eq₂])
      comm₂₃ := h₂.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCocone s)
        have eq₃ := h₃.fac (π₃.mapCocone s)
        have eq₂₃ := fun j => (c.ι.app j).comm₂₃
        have eq₂₃' := fun j => (s.ι.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [reassoc_of% (eq₂ j)]; rw [eq₂₃']; rw [reassoc_of% eq₂₃]; rw [eq₃]) }
  fac s j := by
    ext
    · apply IsColimit.fac h₁
    · apply IsColimit.fac h₂
    · apply IsColimit.fac h₃
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCocone s) _ (fun j => π₁.congr_map (hm j))
    · exact h₂.uniq (π₂.mapCocone s) _ (fun j => π₂.congr_map (hm j))
    · exact h₃.uniq (π₃.mapCocone s) _ (fun j => π₃.congr_map (hm j))

section

variable (F)
variable [HasColimit (F ⋙ π₁)] [HasColimit (F ⋙ π₂)] [HasColimit (F ⋙ π₃)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
definition colimitCocone
  signature: : Cocone F
  body: Cocone.mk (ShortComplex.mk (colimMap (whiskerLeft F π₁Toπ₂)) (colimMap (whiskerLeft F π₂Toπ₃))
      (by cat_disch))
    { app := fun j => Hom.mk (colimit.ι (F ⋙ π₁) _) (colimit.ι (F ⋙ π₂) _)
        (colimit.ι (F ⋙ π₃) _) (by simp) (by simp)
      naturality := fun _ _ f => by
        ext
        · simp [← colimit.w (F ⋙ π₁) f]
        · simp [← colimit.w (F ⋙ π₂) f]
        · simp [← colimit.w (F ⋙ π₃) f] }

中文:
定义 colimitCocone
  签名: : 余锥 F
  定义体: Cocone.mk (ShortComplex.mk (colimMap (whiskerLeft F π₁Toπ₂)) (colimMap (whiskerLeft F π₂Toπ₃))
      (by cat_disch))
    { app := fun j => Hom.mk (colimit.ι (F ⋙ π₁) _) (colimit.ι (F ⋙ π₂) _)
        (colimit.ι (F ⋙ π₃) _) (by simp) (by simp)
      naturality := fun _ _ f => by
        ext
        · simp [← colimit.w (F ⋙ π₁) f]
        · simp [← colimit.w (F ⋙ π₂) f]
        · simp [← colimit.w (F ⋙ π₃) f] }

Depends on / 依赖: Cocone, Cocone.mk, Hom.mk, ShortComplex, ShortComplex.mk, cat_disch, colimMap, colimit, colimit.w, naturality, whiskerLeft
-/
noncomputable def colimitCocone : Cocone F :=
  Cocone.mk (ShortComplex.mk (colimMap (whiskerLeft F π₁Toπ₂)) (colimMap (whiskerLeft F π₂Toπ₃))
      (by cat_disch))
    { app := fun j => Hom.mk (colimit.ι (F ⋙ π₁) _) (colimit.ι (F ⋙ π₂) _)
        (colimit.ι (F ⋙ π₃) _) (by simp) (by simp)
      naturality := fun _ _ f => by
        ext
        · simp [← colimit.w (F ⋙ π₁) f]
        · simp [← colimit.w (F ⋙ π₂) f]
        · simp [← colimit.w (F ⋙ π₃) f] }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitπ₁MapCoconeColimitCocone` / `isColimitπ₁MapCoconeColimitCocone` 的定义

English:
definition isColimitπ₁MapCoconeColimitCocone
  signature: :
  body: (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

中文:
定义 isColimitπ₁MapCoconeColimitCocone
  签名: :
  定义体: (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, cat_disch, colimit, colimit.isColimit, isColimit, ofIsoColimit
-/
noncomputable def isColimitπ₁MapCoconeColimitCocone :
    IsColimit (π₁.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitπ₂MapCoconeColimitCocone` / `isColimitπ₂MapCoconeColimitCocone` 的定义

English:
definition isColimitπ₂MapCoconeColimitCocone
  signature: :
  body: (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

中文:
定义 isColimitπ₂MapCoconeColimitCocone
  签名: :
  定义体: (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, cat_disch, colimit, colimit.isColimit, isColimit, ofIsoColimit
-/
noncomputable def isColimitπ₂MapCoconeColimitCocone :
    IsColimit (π₂.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitπ₃MapCoconeColimitCocone` / `isColimitπ₃MapCoconeColimitCocone` 的定义

English:
definition isColimitπ₃MapCoconeColimitCocone
  signature: :
  body: (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

中文:
定义 isColimitπ₃MapCoconeColimitCocone
  签名: :
  定义体: (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, cat_disch, colimit, colimit.isColimit, isColimit, ofIsoColimit
-/
noncomputable def isColimitπ₃MapCoconeColimitCocone :
    IsColimit (π₃.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

/--
Definition of `isColimitColimitCocone` / `isColimitColimitCocone` 的定义

English:
definition isColimitColimitCocone
  signature: : IsColimit (colimitCocone F)
  body: isColimitOfIsColimitπ _ (isColimitπ₁MapCoconeColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F) (isColimitπ₃MapCoconeColimitCocone F)

中文:
定义 isColimitColimitCocone
  签名: : 是余极限 (colimitCocone F)
  定义体: isColimitOfIsColimitπ _ (isColimitπ₁MapCoconeColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F) (isColimitπ₃MapCoconeColimitCocone F)
-/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) :=
  isColimitOfIsColimitπ _ (isColimitπ₁MapCoconeColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F) (isColimitπ₃MapCoconeColimitCocone F)

/--
Instance `hasColimit_of_hasColimitπ` / 实例 `hasColimit_of_hasColimitπ`

English:
instance hasColimit_of_hasColimitπ
  signature: : HasColimit F
  body: ⟨⟨⟨_, isColimitColimitCocone _⟩⟩⟩

中文:
实例 hasColimit_of_hasColimitπ
  签名: : 有余极限 F
  定义体: ⟨⟨⟨_, isColimitColimitCocone _⟩⟩⟩

Depends on / 依赖: isColimitColimitCocone
-/
instance hasColimit_of_hasColimitπ : HasColimit F := ⟨⟨⟨_, isColimitColimitCocone _⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimit F π₁
  body: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₁MapCoconeColimitCocone F)

中文:
实例 :
  签名: 保持余极限 F π₁
  定义体: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₁MapCoconeColimitCocone F)

Depends on / 依赖: isColimitColimitCocone, preservesColimit_of_preserves_colimit_cocone
-/
noncomputable instance : PreservesColimit F π₁ :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₁MapCoconeColimitCocone F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimit F π₂
  body: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F)

中文:
实例 :
  签名: 保持余极限 F π₂
  定义体: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F)

Depends on / 依赖: isColimitColimitCocone, preservesColimit_of_preserves_colimit_cocone
-/
noncomputable instance : PreservesColimit F π₂ :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimit F π₃
  body: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₃MapCoconeColimitCocone F)

中文:
实例 :
  签名: 保持余极限 F π₃
  定义体: preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₃MapCoconeColimitCocone F)

Depends on / 依赖: isColimitColimitCocone, preservesColimit_of_preserves_colimit_cocone
-/
noncomputable instance : PreservesColimit F π₃ :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₃MapCoconeColimitCocone F)

end

section

variable [HasColimitsOfShape J C]

/--
Instance `hasColimitsOfShape` / 实例 `hasColimitsOfShape`

English:
instance hasColimitsOfShape
  signature: :

中文:
实例 hasColimitsOfShape
  签名: :
-/
instance hasColimitsOfShape :
    HasColimitsOfShape J (ShortComplex C) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape J (π₁ : _ ⥤ C)

中文:
实例 :
  签名: 保持形状余极限 J (π₁ : _ ⥤ C)
-/
noncomputable instance : PreservesColimitsOfShape J (π₁ : _ ⥤ C) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape J (π₂ : _ ⥤ C)

中文:
实例 :
  签名: 保持形状余极限 J (π₂ : _ ⥤ C)
-/
noncomputable instance : PreservesColimitsOfShape J (π₂ : _ ⥤ C) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape J (π₃ : _ ⥤ C)

中文:
实例 :
  签名: 保持形状余极限 J (π₃ : _ ⥤ C)
-/
noncomputable instance : PreservesColimitsOfShape J (π₃ : _ ⥤ C) where

end

section

variable [HasFiniteColimits C]

/--
Instance `hasFiniteColimits` / 实例 `hasFiniteColimits`

English:
instance hasFiniteColimits
  signature: : HasFiniteColimits (ShortComplex C)
  body: ⟨fun _ _ _ => inferInstance⟩

中文:
实例 hasFiniteColimits
  签名: : 有有限余极限 (短复形 C)
  定义体: ⟨fun _ _ _ => inferInstance⟩
-/
instance hasFiniteColimits : HasFiniteColimits (ShortComplex C) :=
  ⟨fun _ _ _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteColimits (π₁ : _ ⥤ C)
  body: ⟨fun _ _ _ => inferInstance⟩

中文:
实例 :
  签名: 保持FiniteColimits (π₁ : _ ⥤ C)
  定义体: ⟨fun _ _ _ => inferInstance⟩
-/
noncomputable instance : PreservesFiniteColimits (π₁ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteColimits (π₂ : _ ⥤ C)
  body: ⟨fun _ _ _ => inferInstance⟩

中文:
实例 :
  签名: 保持FiniteColimits (π₂ : _ ⥤ C)
  定义体: ⟨fun _ _ _ => inferInstance⟩
-/
noncomputable instance : PreservesFiniteColimits (π₂ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteColimits (π₃ : _ ⥤ C)
  body: ⟨fun _ _ _ => inferInstance⟩

中文:
实例 :
  签名: 保持FiniteColimits (π₃ : _ ⥤ C)
  定义体: ⟨fun _ _ _ => inferInstance⟩
-/
noncomputable instance : PreservesFiniteColimits (π₃ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

end

section

variable [HasColimitsOfShape WalkingSpan C]

/--
Instance `preservesEpimorphisms_π₁` / 实例 `preservesEpimorphisms_π₁`

English:
instance preservesEpimorphisms_π₁
  signature: :
  body: CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

中文:
实例 preservesEpimorphisms_π₁
  签名: :
  定义体: CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

Depends on / 依赖: CategoryTheory, CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape, preservesEpimorphisms_of_preservesColimitsOfShape
-/
instance preservesEpimorphisms_π₁ :
    Functor.PreservesEpimorphisms (π₁ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

/--
Instance `preservesEpimorphisms_π₂` / 实例 `preservesEpimorphisms_π₂`

English:
instance preservesEpimorphisms_π₂
  signature: :
  body: CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

中文:
实例 preservesEpimorphisms_π₂
  签名: :
  定义体: CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

Depends on / 依赖: CategoryTheory, CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape, preservesEpimorphisms_of_preservesColimitsOfShape
-/
instance preservesEpimorphisms_π₂ :
    Functor.PreservesEpimorphisms (π₂ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

/--
Instance `preservesEpimorphisms_π₃` / 实例 `preservesEpimorphisms_π₃`

English:
instance preservesEpimorphisms_π₃
  signature: :
  body: CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

中文:
实例 preservesEpimorphisms_π₃
  签名: :
  定义体: CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

Depends on / 依赖: CategoryTheory, CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape, preservesEpimorphisms_of_preservesColimitsOfShape
-/
instance preservesEpimorphisms_π₃ :
    Functor.PreservesEpimorphisms (π₃ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

end

end ShortComplex

end CategoryTheory
