/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# API for compositions of three arrows

Given morphisms `f₁ : i ⟶ j`, `f₂ : j ⟶ k`, `f₃ : k ⟶ l`, and their
compositions `f₁₂ : i ⟶ k` and `f₂₃ : j ⟶ l`, we define
maps `ComposableArrows.threeδ₃Toδ₂ : mk₂ f₁ f₂ ⟶ mk₂ f₁ f₂₃`,
`threeδ₂Toδ₁ : mk₂ f₁ f₂₃ ⟶ mk₂ f₁₂ f₃`, and `threeδ₁Toδ₀ : mk₂ f₁₂ f₃ ⟶ mk₂ f₂ f₃`.
The names are justified by the fact that `ComposableArrow.mk₃ f₁ f₂ f₃`
can be thought of as a `3`-simplex in the simplicial set `nerve C`,
and its faces (numbered from `0` to `3`) are respectively
`mk₂ f₂ f₃`, `mk₂ f₁₂ f₃`, `mk₂ f₁ f₂₃`, `mk₂ f₁ f₂`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ComposableArrows

section

variable {C : Type u} [Category.{v} C]
  {i j k l : C} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (f₂₃ : j ⟶ l)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `threeδ₃Toδ₂` / `threeδ₃Toδ₂` 的定义

English:
definition threeδ₃Toδ₂
  signature: (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch)
  body: homMk₂ (𝟙 _) (𝟙 _) f₃

中文:
定义 threeδ₃Toδ₂
  签名: (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch)
  定义体: homMk₂ (𝟙 _) (𝟙 _) f₃

Depends on / 依赖: cat_disch
-/
def threeδ₃Toδ₂ (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) :
    mk₂ f₁ f₂ ⟶ mk₂ f₁ f₂₃ :=
  homMk₂ (𝟙 _) (𝟙 _) f₃

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `threeδ₂Toδ₁` / `threeδ₂Toδ₁` 的定义

English:
definition threeδ₂Toδ₁
  signature: (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch)
  body: homMk₂ (𝟙 _) f₂ (𝟙 _)

中文:
定义 threeδ₂Toδ₁
  签名: (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch)
  定义体: homMk₂ (𝟙 _) f₂ (𝟙 _)

Depends on / 依赖: cat_disch
-/
def threeδ₂Toδ₁ (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) :
    mk₂ f₁ f₂₃ ⟶ mk₂ f₁₂ f₃ :=
  homMk₂ (𝟙 _) f₂ (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `threeδ₁Toδ₀` / `threeδ₁Toδ₀` 的定义

English:
definition threeδ₁Toδ₀
  signature: (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch)
  body: homMk₂ f₁ (𝟙 _) (𝟙 _)

中文:
定义 threeδ₁Toδ₀
  签名: (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch)
  定义体: homMk₂ f₁ (𝟙 _) (𝟙 _)

Depends on / 依赖: cat_disch
-/
def threeδ₁Toδ₀ (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) :
    mk₂ f₁₂ f₃ ⟶ mk₂ f₂ f₃ :=
  homMk₂ f₁ (𝟙 _) (𝟙 _)

variable (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `threeδ₃Toδ₂_app_zero` / 引理 `threeδ₃Toδ₂_app_zero`

English:
lemma threeδ₃Toδ₂_app_zero
  proof: rfl

中文:
引理 threeδ₃Toδ₂_app_zero
  证明: rfl
-/
lemma threeδ₃Toδ₂_app_zero :
    (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃).app 0 = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `threeδ₃Toδ₂_app_one` / 引理 `threeδ₃Toδ₂_app_one`

English:
lemma threeδ₃Toδ₂_app_one
  proof: rfl

中文:
引理 threeδ₃Toδ₂_app_one
  证明: rfl
-/
lemma threeδ₃Toδ₂_app_one :
    (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃).app 1 = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `threeδ₃Toδ₂_app_two` / 引理 `threeδ₃Toδ₂_app_two`

English:
lemma threeδ₃Toδ₂_app_two
  proof: rfl

@[simp]

中文:
引理 threeδ₃Toδ₂_app_two
  证明: rfl

@[simp]

Depends on / 依赖: ReflectsColimits, ReflectsColimits.reflectsFilteredColimits, reflectsFilteredColimits
-/
lemma threeδ₃Toδ₂_app_two :
    (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃).app 2 = f₃ := rfl

@[simp]
/--
lemma `threeδ₂Toδ₁_app_zero` / 引理 `threeδ₂Toδ₁_app_zero`

English:
lemma threeδ₂Toδ₁_app_zero
  proof: rfl

@[simp]

中文:
引理 threeδ₂Toδ₁_app_zero
  证明: rfl

@[simp]
-/
lemma threeδ₂Toδ₁_app_zero :
    (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).app 0 = 𝟙 _ := rfl

@[simp]
/--
lemma `threeδ₂Toδ₁_app_one` / 引理 `threeδ₂Toδ₁_app_one`

English:
lemma threeδ₂Toδ₁_app_one
  proof: rfl

@[simp]

中文:
引理 threeδ₂Toδ₁_app_one
  证明: rfl

@[simp]
-/
lemma threeδ₂Toδ₁_app_one :
    (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).app 1 = f₂ := rfl

@[simp]
/--
lemma `threeδ₂Toδ₁_app_two` / 引理 `threeδ₂Toδ₁_app_two`

English:
lemma threeδ₂Toδ₁_app_two
  proof: rfl

@[simp]

中文:
引理 threeδ₂Toδ₁_app_two
  证明: rfl

@[simp]
-/
lemma threeδ₂Toδ₁_app_two :
    (threeδ₂Toδ₁ f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃).app 2 = 𝟙 _ := rfl

@[simp]
/--
lemma `threeδ₁Toδ₀_app_zero` / 引理 `threeδ₁Toδ₀_app_zero`

English:
lemma threeδ₁Toδ₀_app_zero
  proof: rfl

@[simp]

中文:
引理 threeδ₁Toδ₀_app_zero
  证明: rfl

@[simp]
-/
lemma threeδ₁Toδ₀_app_zero :
    (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 0 = f₁ := rfl

@[simp]
/--
lemma `threeδ₁Toδ₀_app_one` / 引理 `threeδ₁Toδ₀_app_one`

English:
lemma threeδ₁Toδ₀_app_one
  proof: rfl

@[simp]

中文:
引理 threeδ₁Toδ₀_app_one
  证明: rfl

@[simp]
-/
lemma threeδ₁Toδ₀_app_one :
    (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 1 = (𝟙 _) := rfl

@[simp]
/--
lemma `threeδ₁Toδ₀_app_two` / 引理 `threeδ₁Toδ₀_app_two`

English:
lemma threeδ₁Toδ₀_app_two
  proof: rfl

中文:
引理 threeδ₁Toδ₀_app_two
  证明: rfl

Depends on / 依赖: PreservesLimits, PreservesLimits.preservesCofilteredLimits, preservesCofilteredLimits
-/
lemma threeδ₁Toδ₀_app_two :
    (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂).app 2 = (𝟙 _) := rfl

end

section

variable {ι : Type*} [Preorder ι]
    (i₀ i₁ i₂ i₃ : ι) (hi₀₁ : i₀ <= i₁) (hi₁₂ : i₁ <= i₂) (hi₂₃ : i₂ <= i₃)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `threeδ₃Toδ₂'` / `threeδ₃Toδ₂'` 的定义

English:
abbreviation threeδ₃Toδ₂'
  signature: :
  body: threeδ₃Toδ₂ _ _ (homOfLE hi₂₃) _ rfl

中文:
缩写 threeδ₃Toδ₂'
  签名: :
  定义体: threeδ₃Toδ₂ _ _ (homOfLE hi₂₃) _ rfl

Depends on / 依赖: homOfLE
-/
abbrev threeδ₃Toδ₂' :
    mk₂ (homOfLE hi₀₁) (homOfLE hi₁₂) ⟶
      mk₂ (homOfLE hi₀₁) (homOfLE (hi₁₂.trans hi₂₃)) :=
  threeδ₃Toδ₂ _ _ (homOfLE hi₂₃) _ rfl

/--
Definition of `threeδ₂Toδ₁'` / `threeδ₂Toδ₁'` 的定义

English:
abbreviation threeδ₂Toδ₁'
  signature: :
  body: threeδ₂Toδ₁ _ (homOfLE hi₁₂) _ _ _ rfl rfl

中文:
缩写 threeδ₂Toδ₁'
  签名: :
  定义体: threeδ₂Toδ₁ _ (homOfLE hi₁₂) _ _ _ rfl rfl

Depends on / 依赖: homOfLE
-/
abbrev threeδ₂Toδ₁' :
    mk₂ (homOfLE hi₀₁) (homOfLE (hi₁₂.trans hi₂₃)) ⟶
      mk₂ (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) :=
  threeδ₂Toδ₁ _ (homOfLE hi₁₂) _ _ _ rfl rfl

/--
Definition of `threeδ₁Toδ₀'` / `threeδ₁Toδ₀'` 的定义

English:
abbreviation threeδ₁Toδ₀'
  signature: :
  body: threeδ₁Toδ₀ (homOfLE hi₀₁) _ _ _ rfl

中文:
缩写 threeδ₁Toδ₀'
  签名: :
  定义体: threeδ₁Toδ₀ (homOfLE hi₀₁) _ _ _ rfl

Depends on / 依赖: homOfLE
-/
abbrev threeδ₁Toδ₀' :
    mk₂ (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) ⟶
      mk₂ (homOfLE hi₁₂) (homOfLE hi₂₃) :=
  threeδ₁Toδ₀ (homOfLE hi₀₁) _ _ _ rfl

end

end ComposableArrows

end CategoryTheory
