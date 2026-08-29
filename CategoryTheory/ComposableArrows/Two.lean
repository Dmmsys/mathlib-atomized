/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# API for compositions of two arrows

Given morphisms `f : i ⟶ j`, `g : j ⟶ k`, and `fg : i ⟶ k` in a category `C`
such that `f ≫ g = fg`, we define maps `twoδ₂Toδ₁ : mk₁ f ⟶ mk₁ fg` and
`twoδ₁Toδ₀ : mk₁ fg ⟶ mk₁ g` in the category `ComposableArrows C 1`.
The names are justified by the fact that `ComposableArrow.mk₂ f g`
can be thought of as a `2`-simplex in the simplicial set `nerve C`,
and its faces (numbered from `0` to `2`) are respectively `mk₁ g`,
`mk₁ fg` and `mk₁ f`.

-/

@[expose] public section

namespace CategoryTheory

namespace ComposableArrows

section

variable {C : Type*} [Category* C]
  {i j k : C} (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `twoδ₂Toδ₁` / `twoδ₂Toδ₁` 的定义

English:
definition twoδ₂Toδ₁
  signature: (h : f ≫ g = fg := by cat_disch)
  body: homMk₁ (𝟙 _) g

中文:
定义 twoδ₂Toδ₁
  签名: (h : f ≫ g = fg := by cat_disch)
  定义体: homMk₁ (𝟙 _) g

Depends on / 依赖: cat_disch
-/
def twoδ₂Toδ₁ (h : f ≫ g = fg := by cat_disch) :
    mk₁ f ⟶ mk₁ fg :=
  homMk₁ (𝟙 _) g

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `twoδ₁Toδ₀` / `twoδ₁Toδ₀` 的定义

English:
definition twoδ₁Toδ₀
  signature: (h : f ≫ g = fg := by cat_disch)
  body: homMk₁ f (𝟙 _)

中文:
定义 twoδ₁Toδ₀
  签名: (h : f ≫ g = fg := by cat_disch)
  定义体: homMk₁ f (𝟙 _)

Depends on / 依赖: cat_disch
-/
def twoδ₁Toδ₀ (h : f ≫ g = fg := by cat_disch) :
    mk₁ fg ⟶ mk₁ g :=
  homMk₁ f (𝟙 _)

variable (h : f ≫ g = fg)

@[simp]
/--
lemma `twoδ₂Toδ₁_app_zero` / 引理 `twoδ₂Toδ₁_app_zero`

English:
lemma twoδ₂Toδ₁_app_zero
  proof: rfl

@[simp]

中文:
引理 twoδ₂Toδ₁_app_zero
  证明: rfl

@[simp]

Depends on / 依赖: ReflectsLimits, ReflectsLimits.reflectsCofilteredLimits, reflectsCofilteredLimits
-/
lemma twoδ₂Toδ₁_app_zero :
    (twoδ₂Toδ₁ f g fg h).app 0 = 𝟙 _ := rfl

@[simp]
/--
lemma `twoδ₂Toδ₁_app_one` / 引理 `twoδ₂Toδ₁_app_one`

English:
lemma twoδ₂Toδ₁_app_one
  proof: rfl

@[simp]

中文:
引理 twoδ₂Toδ₁_app_one
  证明: rfl

@[simp]
-/
lemma twoδ₂Toδ₁_app_one :
    (twoδ₂Toδ₁ f g fg h).app 1 = g := rfl

@[simp]
/--
lemma `twoδ₁Toδ₀_app_zero` / 引理 `twoδ₁Toδ₀_app_zero`

English:
lemma twoδ₁Toδ₀_app_zero
  proof: rfl

@[simp]

中文:
引理 twoδ₁Toδ₀_app_zero
  证明: rfl

@[simp]
-/
lemma twoδ₁Toδ₀_app_zero :
    (twoδ₁Toδ₀ f g fg h).app 0 = f := rfl

@[simp]
/--
lemma `twoδ₁Toδ₀_app_one` / 引理 `twoδ₁Toδ₀_app_one`

English:
lemma twoδ₁Toδ₀_app_one
  proof: rfl

中文:
引理 twoδ₁Toδ₀_app_one
  证明: rfl
-/
lemma twoδ₁Toδ₀_app_one :
    (twoδ₁Toδ₀ f g fg h).app 1 = 𝟙 _ := rfl

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIso
  signature: g] : IsIso (twoδ₂Toδ₁ f g fg h)
  body: by
  rw [isIso_iff₁]
  constructor <;> dsimp <;> infer_instance

中文:
实例 [IsIso
  签名: g] : IsIso (twoδ₂Toδ₁ f g fg h)
  定义体: by
  rw [isIso_iff₁]
  constructor <;> dsimp <;> infer_instance

Depends on / 依赖: infer_instance
-/
instance [IsIso g] : IsIso (twoδ₂Toδ₁ f g fg h) := by
  rw [isIso_iff₁]
  constructor <;> dsimp <;> infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIso
  signature: f] : IsIso (twoδ₁Toδ₀ f g fg h)
  body: by
  rw [isIso_iff₁]
  constructor <;> dsimp <;> infer_instance

中文:
实例 [IsIso
  签名: f] : IsIso (twoδ₁Toδ₀ f g fg h)
  定义体: by
  rw [isIso_iff₁]
  constructor <;> dsimp <;> infer_instance

Depends on / 依赖: infer_instance
-/
instance [IsIso f] : IsIso (twoδ₁Toδ₀ f g fg h) := by
  rw [isIso_iff₁]
  constructor <;> dsimp <;> infer_instance

end

section

variable {ι : Type*} [Preorder ι] (i₀ i₁ i₂ : ι) (hi₀₁ : i₀ <= i₁) (hi₁₂ : i₁ <= i₂)

/--
Definition of `twoδ₁Toδ₀'` / `twoδ₁Toδ₀'` 的定义

English:
abbreviation twoδ₁Toδ₀'
  signature: :
  body: twoδ₁Toδ₀ (homOfLE hi₀₁) _ _ rfl

中文:
缩写 twoδ₁Toδ₀'
  签名: :
  定义体: twoδ₁Toδ₀ (homOfLE hi₀₁) _ _ rfl

Depends on / 依赖: homOfLE, preservesLimitsOfShapeOfPreservesFiniteLimits
-/
abbrev twoδ₁Toδ₀' :
    mk₁ (homOfLE (hi₀₁.trans hi₁₂)) ⟶ mk₁ (homOfLE hi₁₂) :=
  twoδ₁Toδ₀ (homOfLE hi₀₁) _ _ rfl

/--
Definition of `twoδ₂Toδ₁'` / `twoδ₂Toδ₁'` 的定义

English:
abbreviation twoδ₂Toδ₁'
  signature: :
  body: twoδ₂Toδ₁ _ (homOfLE hi₁₂) _ rfl

中文:
缩写 twoδ₂Toδ₁'
  签名: :
  定义体: twoδ₂Toδ₁ _ (homOfLE hi₁₂) _ rfl

Depends on / 依赖: homOfLE
-/
abbrev twoδ₂Toδ₁' :
     mk₁ (homOfLE hi₀₁) ⟶ mk₁ (homOfLE (hi₀₁.trans hi₁₂)) :=
  twoδ₂Toδ₁ _ (homOfLE hi₁₂) _ rfl

end

end ComposableArrows

end CategoryTheory
