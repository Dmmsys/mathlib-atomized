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
/-- If a cone with values in `ShortComplex C` is such that it becomes limit
when we apply the three projections `ShortComplex C ⥤ C`, then it is limit. -/
/-
**CategoryTheory.ShortComplex.isLimitOfIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a cone with values in `ShortComplex C` is such that it becomes limit
when we apply the three projections `ShortComplex C ⥤ C`, then it is limit.
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
        rw [assoc, assoc, ← eq₁₂, reassoc_of% eq₁, eq₂, eq₁₂'])
      comm₂₃ := h₃.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCone s)
        have eq₃ := h₃.fac (π₃.mapCone s)
        have eq₂₃ := fun j => (c.π.app j).comm₂₃
        have eq₂₃' := fun j => (s.π.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [assoc, assoc, ← eq₂₃, reassoc_of% eq₂, eq₃, eq₂₃']) }
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
/-- Construction of a limit cone for a functor `J ⥤ ShortComplex C` using the limits
of the three components `J ⥤ C`. -/
/-
**CategoryTheory.ShortComplex.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ShortComplex`。
形式化陈述：limitCone : Cone F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construction of a limit cone for a functor `J ⥤ ShortComplex C` using the limits
of the three components `J ⥤ C`.
-/
noncomputable def limitCone : Cone F :=
  Cone.mk (ShortComplex.mk (limMap (whiskerLeft F π₁Toπ₂)) (limMap (whiskerLeft F π₂Toπ₃))
      (by cat_disch))
    { app := fun j => Hom.mk (limit.π _ _) (limit.π _ _) (limit.π _ _)
        (by simp) (by simp)
      naturality := fun _ _ f => by
        ext <;> simp [← limit.w _ f] }

set_option backward.isDefEq.respectTransparency false in
/-- `limitCone F` becomes limit after the application of `π₁ : ShortComplex C ⥤ C`. -/
/-
**CategoryTheory.ShortComplex.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`limitCone F` becomes limit after the application of `π₁ : ShortComplex C ⥤ C`.
-/
noncomputable def isLimitπ₁MapConeLimitCone : IsLimit (π₁.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in
/-- `limitCone F` becomes limit after the application of `π₂ : ShortComplex C ⥤ C`. -/
/-
**CategoryTheory.ShortComplex.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`limitCone F` becomes limit after the application of `π₂ : ShortComplex C ⥤ C`.
-/
noncomputable def isLimitπ₂MapConeLimitCone : IsLimit (π₂.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in
/-- `limitCone F` becomes limit after the application of `π₃ : ShortComplex C ⥤ C`. -/
/-
**CategoryTheory.ShortComplex.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`limitCone F` becomes limit after the application of `π₃ : ShortComplex C ⥤ C`.
-/
noncomputable def isLimitπ₃MapConeLimitCone : IsLimit (π₃.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (by cat_disch)))

/-- `limitCone F` is limit. -/
/-
**CategoryTheory.ShortComplex.isLimitLimitCone** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：isLimitLimitCone : IsLimit (limitCone F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`limitCone F` is limit.
-/
noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  isLimitOfIsLimitπ _ (isLimitπ₁MapConeLimitCone F)
    (isLimitπ₂MapConeLimitCone F) (isLimitπ₃MapConeLimitCone F)
/-
**CategoryTheory.ShortComplex.hasLimit_of_hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasLimit_of_hasLimitπ : HasLimit F := ⟨⟨⟨_, isLimitLimitCone _⟩⟩⟩
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesLimit F π₁ :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₁MapConeLimitCone F)
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesLimit F π₂ :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₂MapConeLimitCone F)
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesLimit F π₃ :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₃MapConeLimitCone F)

end

section

variable [HasLimitsOfShape J C]

/-
**CategoryTheory.ShortComplex.hasLimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：∀ {J : Type u_1} {C : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [CategoryTheory.Limits.HasLimitsOfShape J C], Catego
ryTheory.Limits.HasLimitsOfShape J (CategoryTheory.ShortComplex C)
参数：CategoryTheory.ShortComplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasLimitsOfShape :
    HasLimitsOfShape J (ShortComplex C) where
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesLimitsOfShape J (π₁ : _ ⥤ C) where
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesLimitsOfShape J (π₂ : _ ⥤ C) where
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesLimitsOfShape J (π₃ : _ ⥤ C) where

end

section

variable [HasFiniteLimits C]

/-
**CategoryTheory.ShortComplex.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：hasFiniteLimits : HasFiniteLimits (ShortComplex C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.hasLimitsOfShape`：∀ {J : Type u_1} {C : Type
 u_2} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.C
ategory.{v_2, u_2} C] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
instance hasFiniteLimits : HasFiniteLimits (ShortComplex C) :=
  ⟨fun _ _ _ => inferInstance⟩
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteLimits (π₁ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteLimits (π₂ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteLimits (π₃ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

end

section

variable [HasLimitsOfShape WalkingCospan C]

/-
**CategoryTheory.ShortComplex.preservesMonomorphisms_** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesMonomorphisms_π₁ :
    Functor.PreservesMonomorphisms (π₁ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
/-
**CategoryTheory.ShortComplex.preservesMonomorphisms_** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesMonomorphisms_π₂ :
    Functor.PreservesMonomorphisms (π₂ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
/-
**CategoryTheory.ShortComplex.preservesMonomorphisms_** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesMonomorphisms_π₃ :
    Functor.PreservesMonomorphisms (π₃ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If a cocone with values in `ShortComplex C` is such that it becomes colimit
when we apply the three projections `ShortComplex C ⥤ C`, then it is colimit. -/
/-
**CategoryTheory.ShortComplex.isColimitOfIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a cocone with values in `ShortComplex C` is such that it becomes colimit
when we apply the three projections `ShortComplex C ⥤ C`, then it is colimit.
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
        rw [reassoc_of% (eq₁ j), eq₁₂', reassoc_of% eq₁₂, eq₂])
      comm₂₃ := h₂.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCocone s)
        have eq₃ := h₃.fac (π₃.mapCocone s)
        have eq₂₃ := fun j => (c.ι.app j).comm₂₃
        have eq₂₃' := fun j => (s.ι.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [reassoc_of% (eq₂ j), eq₂₃', reassoc_of% eq₂₃, eq₃]) }
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
/-- Construction of a colimit cocone for a functor `J ⥤ ShortComplex C` using the colimits
of the three components `J ⥤ C`. -/
/-
**CategoryTheory.ShortComplex.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：colimitCocone : Cocone F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construction of a colimit cocone for a functor `J ⥤ ShortComplex C` using the co
limits
of the three components `J ⥤ C`.
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
/-- `colimitCocone F` becomes colimit after the application of `π₁ : ShortComplex C ⥤ C`. -/
/-
**CategoryTheory.ShortComplex.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`colimitCocone F` becomes colimit after the application of `π₁ : ShortComplex C 
⥤ C`.
-/
noncomputable def isColimitπ₁MapCoconeColimitCocone :
    IsColimit (π₁.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in
/-- `colimitCocone F` becomes colimit after the application of `π₂ : ShortComplex C ⥤ C`. -/
/-
**CategoryTheory.ShortComplex.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`colimitCocone F` becomes colimit after the application of `π₂ : ShortComplex C 
⥤ C`.
-/
noncomputable def isColimitπ₂MapCoconeColimitCocone :
    IsColimit (π₂.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

set_option backward.isDefEq.respectTransparency false in
/-- `colimitCocone F` becomes colimit after the application of `π₃ : ShortComplex C ⥤ C`. -/
/-
**CategoryTheory.ShortComplex.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`colimitCocone F` becomes colimit after the application of `π₃ : ShortComplex C 
⥤ C`.
-/
noncomputable def isColimitπ₃MapCoconeColimitCocone :
    IsColimit (π₃.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (by cat_disch)))

/-- `colimitCocone F` is colimit. -/
/-
**CategoryTheory.ShortComplex.isColimitColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：isColimitColimitCocone : IsColimit (colimitCocone F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`colimitCocone F` is colimit.
-/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) :=
  isColimitOfIsColimitπ _ (isColimitπ₁MapCoconeColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F) (isColimitπ₃MapCoconeColimitCocone F)
/-
**CategoryTheory.ShortComplex.hasColimit_of_hasColimit** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasColimit_of_hasColimitπ : HasColimit F := ⟨⟨⟨_, isColimitColimitCocone _⟩⟩⟩
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesColimit F π₁ :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₁MapCoconeColimitCocone F)
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesColimit F π₂ :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F)
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesColimit F π₃ :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₃MapCoconeColimitCocone F)

end

section

variable [HasColimitsOfShape J C]

/-
**CategoryTheory.ShortComplex.hasColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.ShortComplex`。
形式化陈述：∀ {J : Type u_1} {C : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C] [inst_2 : CategoryTheory.L
imits.HasZeroMorphisms C]   [CategoryTheory.Limits.HasColimitsOfShape J C],   Ca
tegoryTheory.Limits.HasColimitsOfShape J (CategoryTheory.ShortComplex C)
参数：CategoryTheory.ShortComplex C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasColimitsOfShape :
    HasColimitsOfShape J (ShortComplex C) where
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesColimitsOfShape J (π₁ : _ ⥤ C) where
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesColimitsOfShape J (π₂ : _ ⥤ C) where
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesColimitsOfShape J (π₃ : _ ⥤ C) where

end

section

variable [HasFiniteColimits C]

/-
**CategoryTheory.ShortComplex.hasFiniteColimits** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.ShortComplex`。
形式化陈述：hasFiniteColimits : HasFiniteColimits (ShortComplex C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.hasColimitsOfShape`：∀ {J : Type u_1} {C : Ty
pe u_2} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory
.Category.{v_2, u_2} C] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
-/
instance hasFiniteColimits : HasFiniteColimits (ShortComplex C) :=
  ⟨fun _ _ _ => inferInstance⟩
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteColimits (π₁ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteColimits (π₂ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteColimits (π₃ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

end

section

variable [HasColimitsOfShape WalkingSpan C]

/-
**CategoryTheory.ShortComplex.preservesEpimorphisms_** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesEpimorphisms_π₁ :
    Functor.PreservesEpimorphisms (π₁ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _
/-
**CategoryTheory.ShortComplex.preservesEpimorphisms_** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesEpimorphisms_π₂ :
    Functor.PreservesEpimorphisms (π₂ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _
/-
**CategoryTheory.ShortComplex.preservesEpimorphisms_** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesEpimorphisms_π₃ :
    Functor.PreservesEpimorphisms (π₃ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

end

end ShortComplex

end CategoryTheory

