/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# API for compositions of four arrows

Given morphisms `f₁ : i₀ ⟶ i₁`, `f₂ : i₁ ⟶ i₂`, `f₃ : i₂ ⟶ i₃`, `f₄ : i₃ ⟶ i₄`,
and their compositions `f₁₂ : i₀ ⟶ i₂`, `f₂₃ : i₁ ⟶ i₃` and `f₃₄ : i₂ ⟶ i₄`,
we define maps `ComposableArrows.fourδ₄Toδ₃ : mk₃ f₁ f₂ f₃ ⟶ mk₂ f₁ f₂ f₃₄`,
`fourδ₃Toδ₂ : mk₃ f₁ f₂ f₃₄ ⟶ mk₂ f₁ f₂₃ f₄`,
`fourδ₂Toδ₁ : mk₃ f₁ f₂₃ f₄ ⟶ mk₂ f₁₂ f₃ f₄`, and
`fourδ₁Toδ₀ : mk₃ f₁₂ f₃ f₄ ⟶ mk₂ f₂ f₃ f₄`.
The names are justified by the fact that `ComposableArrow.mk₄ f₁ f₂ f₃ f₄`
can be thought of as a `4`-simplex in the simplicial set `nerve C`,
and its faces (numbered from `0` to `4`) are respectively
`mk₂ f₂ f₃ f₄`, `mk₂ f₁₂ f₃ f₄`, `mk₂ f₁ f₂₃ f₄`, `mk₂ f₁ f₂ f₃₄` and
`mk₂ f₁ f₂ f₃`.

-/

@[expose] public section

namespace CategoryTheory

namespace ComposableArrows

section

variable {C : Type*} [Category* C]
  {i₀ i₁ i₂ i₃ i₄ : C} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (f₄ : i₃ ⟶ i₄)
  (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃) (f₃₄ : i₂ ⟶ i₄)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fourδ₄Toδ₃` / `fourδ₄Toδ₃` 的定义

English:
definition fourδ₄Toδ₃
  signature: (h₃₄ : f₃ ≫ f₄ = f₃₄ := by cat_disch)
  body: homMk₃ (𝟙 _) (𝟙 _) (𝟙 _) f₄

中文:
定义 fourδ₄Toδ₃
  签名: (h₃₄ : f₃ ≫ f₄ = f₃₄ := by cat_disch)
  定义体: homMk₃ (𝟙 _) (𝟙 _) (𝟙 _) f₄

Depends on / 依赖: cat_disch
-/
def fourδ₄Toδ₃ (h₃₄ : f₃ ≫ f₄ = f₃₄ := by cat_disch) :
    mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃₄ :=
  homMk₃ (𝟙 _) (𝟙 _) (𝟙 _) f₄

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fourδ₃Toδ₂` / `fourδ₃Toδ₂` 的定义

English:
definition fourδ₃Toδ₂
  signature: (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) (h₃₄ : f₃ ≫ f₄ = f₃₄ := by cat_disch)
  body: homMk₃ (𝟙 _) (𝟙 _) f₃ (𝟙 _)

中文:
定义 fourδ₃Toδ₂
  签名: (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) (h₃₄ : f₃ ≫ f₄ = f₃₄ := by cat_disch)
  定义体: homMk₃ (𝟙 _) (𝟙 _) f₃ (𝟙 _)

Depends on / 依赖: cat_disch
-/
def fourδ₃Toδ₂ (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) (h₃₄ : f₃ ≫ f₄ = f₃₄ := by cat_disch) :
    mk₃ f₁ f₂ f₃₄ ⟶ mk₃ f₁ f₂₃ f₄ :=
  homMk₃ (𝟙 _) (𝟙 _) f₃ (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fourδ₂Toδ₁` / `fourδ₂Toδ₁` 的定义

English:
definition fourδ₂Toδ₁
  signature: (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch)
  body: homMk₃ (𝟙 _) f₂ (𝟙 _) (𝟙 _)

中文:
定义 fourδ₂Toδ₁
  签名: (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch)
  定义体: homMk₃ (𝟙 _) f₂ (𝟙 _) (𝟙 _)

Depends on / 依赖: cat_disch
-/
def fourδ₂Toδ₁ (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) :
    mk₃ f₁ f₂₃ f₄ ⟶ mk₃ f₁₂ f₃ f₄ :=
  homMk₃ (𝟙 _) f₂ (𝟙 _) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fourδ₁Toδ₀` / `fourδ₁Toδ₀` 的定义

English:
definition fourδ₁Toδ₀
  signature: (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch)
  body: homMk₃ f₁ (𝟙 _) (𝟙 _) (𝟙 _)

中文:
定义 fourδ₁Toδ₀
  签名: (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch)
  定义体: homMk₃ f₁ (𝟙 _) (𝟙 _) (𝟙 _)

Depends on / 依赖: cat_disch
-/
def fourδ₁Toδ₀ (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) :
    mk₃ f₁₂ f₃ f₄ ⟶ mk₃ f₂ f₃ f₄ :=
  homMk₃ f₁ (𝟙 _) (𝟙 _) (𝟙 _)

variable (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃) (h₃₄ : f₃ ≫ f₄ = f₃₄)

@[simp]
/--
lemma `fourδ₄Toδ₃_app_zero` / 引理 `fourδ₄Toδ₃_app_zero`

English:
lemma fourδ₄Toδ₃_app_zero
  proof: rfl

@[simp]

中文:
引理 fourδ₄Toδ₃_app_zero
  证明: rfl

@[simp]
-/
lemma fourδ₄Toδ₃_app_zero :
    (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄).app 0 = 𝟙 _ := rfl

@[simp]
/--
lemma `fourδ₄Toδ₃_app_one` / 引理 `fourδ₄Toδ₃_app_one`

English:
lemma fourδ₄Toδ₃_app_one
  proof: rfl

@[simp]

中文:
引理 fourδ₄Toδ₃_app_one
  证明: rfl

@[simp]
-/
lemma fourδ₄Toδ₃_app_one :
    (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄).app 1 = 𝟙 _ := rfl

@[simp]
/--
lemma `fourδ₄Toδ₃_app_two` / 引理 `fourδ₄Toδ₃_app_two`

English:
lemma fourδ₄Toδ₃_app_two
  proof: rfl

@[simp]

中文:
引理 fourδ₄Toδ₃_app_two
  证明: rfl

@[simp]
-/
lemma fourδ₄Toδ₃_app_two :
    (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄).app 2 = 𝟙 _ := rfl

@[simp]
/--
lemma `fourδ₄Toδ₃_app_three` / 引理 `fourδ₄Toδ₃_app_three`

English:
lemma fourδ₄Toδ₃_app_three
  proof: rfl

@[simp]

中文:
引理 fourδ₄Toδ₃_app_three
  证明: rfl

@[simp]
-/
lemma fourδ₄Toδ₃_app_three :
    (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄).app 3 = f₄ := rfl

@[simp]
/--
lemma `fourδ₃Toδ₂_app_zero` / 引理 `fourδ₃Toδ₂_app_zero`

English:
lemma fourδ₃Toδ₂_app_zero
  proof: rfl

@[simp]

中文:
引理 fourδ₃Toδ₂_app_zero
  证明: rfl

@[simp]
-/
lemma fourδ₃Toδ₂_app_zero :
    (fourδ₃Toδ₂ f₁ f₂ f₃ f₄ f₂₃ f₃₄ h₂₃ h₃₄).app 0 = 𝟙 _ := rfl

@[simp]
/--
lemma `fourδ₃Toδ₂_app_one` / 引理 `fourδ₃Toδ₂_app_one`

English:
lemma fourδ₃Toδ₂_app_one
  proof: rfl

@[simp]

中文:
引理 fourδ₃Toδ₂_app_one
  证明: rfl

@[simp]
-/
lemma fourδ₃Toδ₂_app_one :
    (fourδ₃Toδ₂ f₁ f₂ f₃ f₄ f₂₃ f₃₄ h₂₃ h₃₄).app 1 = 𝟙 _ := rfl

@[simp]
/--
lemma `fourδ₃Toδ₂_app_two` / 引理 `fourδ₃Toδ₂_app_two`

English:
lemma fourδ₃Toδ₂_app_two
  proof: rfl

@[simp]

中文:
引理 fourδ₃Toδ₂_app_two
  证明: rfl

@[simp]
-/
lemma fourδ₃Toδ₂_app_two :
    (fourδ₃Toδ₂ f₁ f₂ f₃ f₄ f₂₃ f₃₄ h₂₃ h₃₄).app 2 = f₃ := rfl

@[simp]
/--
lemma `fourδ₃Toδ₂_app_three` / 引理 `fourδ₃Toδ₂_app_three`

English:
lemma fourδ₃Toδ₂_app_three
  proof: rfl

@[simp]

中文:
引理 fourδ₃Toδ₂_app_three
  证明: rfl

@[simp]
-/
lemma fourδ₃Toδ₂_app_three :
    (fourδ₃Toδ₂ f₁ f₂ f₃ f₄ f₂₃ f₃₄ h₂₃ h₃₄).app 3 = 𝟙 _ := rfl

@[simp]
/--
lemma `fourδ₂Toδ₁_app_zero` / 引理 `fourδ₂Toδ₁_app_zero`

English:
lemma fourδ₂Toδ₁_app_zero
  proof: rfl

@[simp]

中文:
引理 fourδ₂Toδ₁_app_zero
  证明: rfl

@[simp]
-/
lemma fourδ₂Toδ₁_app_zero :
    (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ f₂₃ h₁₂ h₂₃).app 0 = 𝟙 _ := rfl

@[simp]
/--
lemma `fourδ₂Toδ₁_app_one` / 引理 `fourδ₂Toδ₁_app_one`

English:
lemma fourδ₂Toδ₁_app_one
  proof: rfl

@[simp]

中文:
引理 fourδ₂Toδ₁_app_one
  证明: rfl

@[simp]
-/
lemma fourδ₂Toδ₁_app_one :
    (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ f₂₃ h₁₂ h₂₃).app 1 = f₂ := rfl

@[simp]
/--
lemma `fourδ₂Toδ₁_app_two` / 引理 `fourδ₂Toδ₁_app_two`

English:
lemma fourδ₂Toδ₁_app_two
  proof: rfl

@[simp]

中文:
引理 fourδ₂Toδ₁_app_two
  证明: rfl

@[simp]
-/
lemma fourδ₂Toδ₁_app_two :
    (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ f₂₃ h₁₂ h₂₃).app 2 = 𝟙 _ := rfl

@[simp]
/--
lemma `fourδ₂Toδ₁_app_three` / 引理 `fourδ₂Toδ₁_app_three`

English:
lemma fourδ₂Toδ₁_app_three
  proof: rfl

@[simp]

中文:
引理 fourδ₂Toδ₁_app_three
  证明: rfl

@[simp]
-/
lemma fourδ₂Toδ₁_app_three :
    (fourδ₂Toδ₁ f₁ f₂ f₃ f₄ f₁₂ f₂₃ h₁₂ h₂₃).app 3 = 𝟙 _ := rfl

@[simp]
/--
lemma `fourδ₁Toδ₀_app_zero` / 引理 `fourδ₁Toδ₀_app_zero`

English:
lemma fourδ₁Toδ₀_app_zero
  proof: rfl

@[simp]

中文:
引理 fourδ₁Toδ₀_app_zero
  证明: rfl

@[simp]
-/
lemma fourδ₁Toδ₀_app_zero :
    (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 0 = f₁ := rfl

@[simp]
/--
lemma `fourδ₁Toδ₀_app_one` / 引理 `fourδ₁Toδ₀_app_one`

English:
lemma fourδ₁Toδ₀_app_one
  proof: rfl

@[simp]

中文:
引理 fourδ₁Toδ₀_app_one
  证明: rfl

@[simp]
-/
lemma fourδ₁Toδ₀_app_one :
    (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 1 = 𝟙 _ := rfl

@[simp]
/--
lemma `fourδ₁Toδ₀_app_two` / 引理 `fourδ₁Toδ₀_app_two`

English:
lemma fourδ₁Toδ₀_app_two
  proof: rfl

@[simp]

中文:
引理 fourδ₁Toδ₀_app_two
  证明: rfl

@[simp]
-/
lemma fourδ₁Toδ₀_app_two :
    (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 2 = 𝟙 _ := rfl

@[simp]
/--
lemma `fourδ₁Toδ₀_app_three` / 引理 `fourδ₁Toδ₀_app_three`

English:
lemma fourδ₁Toδ₀_app_three
  proof: rfl

中文:
引理 fourδ₁Toδ₀_app_three
  证明: rfl
-/
lemma fourδ₁Toδ₀_app_three :
    (fourδ₁Toδ₀ f₁ f₂ f₃ f₄ f₁₂ h₁₂).app 3 = 𝟙 _ := rfl

end

section

variable {ι : Type*} [Preorder ι] (i₀ i₁ i₂ i₃ i₄ : ι)
  (hi₀₁ : i₀ <= i₁) (hi₁₂ : i₁ <= i₂) (hi₂₃ : i₂ <= i₃) (hi₃₄ : i₃ <= i₄)

/--
Definition of `fourδ₄Toδ₃'` / `fourδ₄Toδ₃'` 的定义

English:
abbreviation fourδ₄Toδ₃'
  signature: :
  body: fourδ₄Toδ₃ _ _ _ (homOfLE hi₃₄) _ rfl

中文:
缩写 fourδ₄Toδ₃'
  签名: :
  定义体: fourδ₄Toδ₃ _ _ _ (homOfLE hi₃₄) _ rfl

Depends on / 依赖: homOfLE
-/
abbrev fourδ₄Toδ₃' :
    mk₃ (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃) ⟶
      mk₃ (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE (hi₂₃.trans hi₃₄)) :=
  fourδ₄Toδ₃ _ _ _ (homOfLE hi₃₄) _ rfl

/--
Definition of `fourδ₃Toδ₂'` / `fourδ₃Toδ₂'` 的定义

English:
abbreviation fourδ₃Toδ₂'
  signature: :
  body: fourδ₃Toδ₂ _ (homOfLE hi₁₂) (homOfLE hi₂₃) _ _ _ rfl rfl

中文:
缩写 fourδ₃Toδ₂'
  签名: :
  定义体: fourδ₃Toδ₂ _ (homOfLE hi₁₂) (homOfLE hi₂₃) _ _ _ rfl rfl

Depends on / 依赖: homOfLE
-/
abbrev fourδ₃Toδ₂' :
    mk₃ (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE (hi₂₃.trans hi₃₄)) ⟶
      mk₃ (homOfLE hi₀₁) (homOfLE (hi₁₂.trans hi₂₃)) (homOfLE hi₃₄) :=
  fourδ₃Toδ₂ _ (homOfLE hi₁₂) (homOfLE hi₂₃) _ _ _ rfl rfl

/--
Definition of `fourδ₂Toδ₁'` / `fourδ₂Toδ₁'` 的定义

English:
abbreviation fourδ₂Toδ₁'
  signature: :
  body: fourδ₂Toδ₁ _ (homOfLE hi₁₂) _ _ _ _ rfl rfl

中文:
缩写 fourδ₂Toδ₁'
  签名: :
  定义体: fourδ₂Toδ₁ _ (homOfLE hi₁₂) _ _ _ _ rfl rfl

Depends on / 依赖: homOfLE
-/
abbrev fourδ₂Toδ₁' :
    mk₃ (homOfLE hi₀₁) (homOfLE (hi₁₂.trans hi₂₃)) (homOfLE hi₃₄) ⟶
      mk₃ (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) (homOfLE hi₃₄) :=
  fourδ₂Toδ₁ _ (homOfLE hi₁₂) _ _ _ _ rfl rfl

/--
Definition of `fourδ₁Toδ₀'` / `fourδ₁Toδ₀'` 的定义

English:
abbreviation fourδ₁Toδ₀'
  signature: :
  body: fourδ₁Toδ₀ (homOfLE hi₀₁) _ _ _ _ rfl

中文:
缩写 fourδ₁Toδ₀'
  签名: :
  定义体: fourδ₁Toδ₀ (homOfLE hi₀₁) _ _ _ _ rfl

Depends on / 依赖: homOfLE
-/
abbrev fourδ₁Toδ₀' :
    mk₃ (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) (homOfLE hi₃₄) ⟶
      mk₃ (homOfLE hi₁₂) (homOfLE hi₂₃) (homOfLE hi₃₄) :=
  fourδ₁Toδ₀ (homOfLE hi₀₁) _ _ _ _ rfl

end

end ComposableArrows

end CategoryTheory
