/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Chosen pullbacks

Given two morphisms `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S`, we introduce
a structure `ChosenPullback f₁ f₂` which contains the data of
pullback of `f₁` and `f₂`.

## TODO
* relate this to `ChosenPullbacksAlong` which is defined in
`LocallyCartesianClosed.ChosenPullbacksAlong`.

-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/--
Definition of `ChosenPullback` / `ChosenPullback` 的定义

English:
structure ChosenPullback
  parameters: {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
  axioms and operations (7):
    - pullback : C
    - p₁ : pullback ⟶ X₁
    - p₂ : pullback ⟶ X₂
    - condition : p₁ ≫ f₁ = p₂ ≫ f₂
    - isLimit : IsLimit (PullbackCone.mk _ _ condition)
    - p : pullback ⟶ S  [default: p₁ ≫ f₁]
    - hp₁ : p₁ ≫ f₁ = p  [default: by cat_disch]

中文:
结构 ChosenPullback
  参数: {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
  公理与运算 (7 个):
    - pullback : C
    - p₁ : pullback ⟶ X₁
    - p₂ : pullback ⟶ X₂
    - condition : p₁ ≫ f₁ = p₂ ≫ f₂
    - isLimit : 是极限 (PullbackCone.mk _ _ condition)
    - p : pullback ⟶ S  [默认: p₁ ≫ f₁]
    - hp₁ : p₁ ≫ f₁ = p  [默认: by cat_disch]
-/
structure ChosenPullback {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) where
  /-- the pullback -/
  pullback : C
  /-- the first projection -/
  p₁ : pullback ⟶ X₁
  /-- the second projection -/
  p₂ : pullback ⟶ X₂
  condition : p₁ ≫ f₁ = p₂ ≫ f₂
  /-- `pullback` is a pullback of `f₁` and `f₂` -/
  isLimit : IsLimit (PullbackCone.mk _ _ condition)
  /-- the projection `pullback ⟶ S` -/
  p : pullback ⟶ S := p₁ ≫ f₁
  hp₁ : p₁ ≫ f₁ = p := by cat_disch

namespace ChosenPullback

section

variable {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
  (h : ChosenPullback f₁ f₂)

attribute [reassoc] condition

/--
lemma `isPullback` / 引理 `isPullback`

English:
lemma isPullback
  statement: IsPullback h.p₁ h.p₂ f₁ f₂ where
  proof: h.condition
  isLimit' := ⟨h.isLimit⟩

中文:
引理 isPullback
  结论: 是拉回 h.p₁ h.p₂ f₁ f₂ where
  证明: h.condition
  isLimit' := ⟨h.isLimit⟩

Depends on / 依赖: condition, h.condition
-/
lemma isPullback : IsPullback h.p₁ h.p₂ f₁ f₂ where
  w := h.condition
  isLimit' := ⟨h.isLimit⟩

attribute [reassoc (attr := simp, grind =)] hp₁

@[reassoc (attr := simp, grind =)]
/--
lemma `hp₂` / 引理 `hp₂`

English:
lemma hp₂
  statement: h.p₂ ≫ f₂ = h.p
  proof: by rw [← h.condition, hp₁]

@[ext]

中文:
引理 hp₂
  结论: h.p₂ ≫ f₂ = h.p
  证明: by rw [← h.condition, hp₁]

@[ext]

Depends on / 依赖: condition, h.condition
-/
lemma hp₂ : h.p₂ ≫ f₂ = h.p := by rw [← h.condition, hp₁]

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {Y : C} {f g : Y ⟶ h.pullback}
  proof: h.isPullback.hom_ext h₁ h₂

中文:
引理 hom_ext
  结论: {Y : C} {f g : Y ⟶ h.pullback}
  证明: h.isPullback.hom_ext h₁ h₂

Depends on / 依赖: h.isPullback.hom_ext, hom_ext, isPullback
-/
lemma hom_ext {Y : C} {f g : Y ⟶ h.pullback}
    (h₁ : f ≫ h.p₁ = g ≫ h.p₁) (h₂ : f ≫ h.p₂ = g ≫ h.p₂) :
    f = g :=
  h.isPullback.hom_ext h₁ h₂

/--
Definition of `LiftStruct` / `LiftStruct` 的定义

English:
structure LiftStruct
  parameters: {Y : C} (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (b : Y ⟶ S)
  axioms and operations (4):
    - f : Y ⟶ h.pullback
    - f_p₁ : f ≫ h.p₁ = g₁  [default: by cat_disch]
    - f_p₂ : f ≫ h.p₂ = g₂  [default: by cat_disch]
    - f_p : f ≫ h.p = b  [default: by cat_disch]

中文:
结构 LiftStruct
  参数: {Y : C} (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (b : Y ⟶ S)
  公理与运算 (4 个):
    - f : Y ⟶ h.pullback
    - f_p₁ : f ≫ h.p₁ = g₁  [默认: by cat_disch]
    - f_p₂ : f ≫ h.p₂ = g₂  [默认: by cat_disch]
    - f_p : f ≫ h.p = b  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure LiftStruct {Y : C} (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (b : Y ⟶ S) where
  /-- a lifting to the pullback -/
  f : Y ⟶ h.pullback
  f_p₁ : f ≫ h.p₁ = g₁ := by cat_disch
  f_p₂ : f ≫ h.p₂ = g₂ := by cat_disch
  f_p : f ≫ h.p = b := by cat_disch

namespace LiftStruct

attribute [reassoc (attr := simp, grind =)] f_p₁ f_p₂ f_p

variable {h} {Y : C} {g₁ : Y ⟶ X₁} {g₂ : Y ⟶ X₂} {b : Y ⟶ S}

@[reassoc]
/--
lemma `w` / 引理 `w`

English:
lemma w
  given: (l : h.LiftStruct g₁ g₂ b)
  statement: g₁ ≫ f₁ = g₂ ≫ f₂
  proof: by
  simp only [← l.f_p₁, ← l.f_p₂, Category.assoc, h.condition]

中文:
引理 w
  条件: (l : h.LiftStruct g₁ g₂ b)
  结论: g₁ ≫ f₁ = g₂ ≫ f₂
  证明: by
  simp only [← l.f_p₁, ← l.f_p₂, Category.assoc, h.condition]

Depends on / 依赖: Category, Category.assoc, condition, h.condition, l.f_p
-/
lemma w (l : h.LiftStruct g₁ g₂ b) : g₁ ≫ f₁ = g₂ ≫ f₂ := by
  simp only [← l.f_p₁, ← l.f_p₂, Category.assoc, h.condition]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (h.LiftStruct g₁ g₂ b)
  body: by
    rintro ⟨f, f_p₁, f_p₂, _⟩ ⟨f', f'_p₁, f'_p₂, _⟩
    obtain rfl : f = f' := by cat_disch
    rfl

中文:
实例 :
  签名: 子单例 (h.LiftStruct g₁ g₂ b)
  定义体: by
    rintro ⟨f, f_p₁, f_p₂, _⟩ ⟨f', f'_p₁, f'_p₂, _⟩
    obtain rfl : f = f' := by cat_disch
    rfl

Depends on / 依赖: cat_disch
-/
instance : Subsingleton (h.LiftStruct g₁ g₂ b) where
  allEq := by
    rintro ⟨f, f_p₁, f_p₂, _⟩ ⟨f', f'_p₁, f'_p₂, _⟩
    obtain rfl : f = f' := by cat_disch
    rfl

/--
lemma `nonempty` / 引理 `nonempty`

English:
lemma nonempty
  given: (w : g₁ ≫ f₁ = g₂ ≫ f₂) (hf₁ : g₁ ≫ f₁ = b)
  proof: by
  obtain ⟨l, h₁, h₂⟩ := h.isPullback.exists_lift g₁ g₂ w
  exact ⟨{
    f := l
    f_p₁ := h₁
    f_p₂ := h₂
    f_p := by rw [← h.hp₁, ← hf₁, reassoc_of% h₁] }⟩

中文:
引理 nonempty
  条件: (w : g₁ ≫ f₁ = g₂ ≫ f₂) (hf₁ : g₁ ≫ f₁ = b)
  证明: by
  obtain ⟨l, h₁, h₂⟩ := h.isPullback.exists_lift g₁ g₂ w
  exact ⟨{
    f := l
    f_p₁ := h₁
    f_p₂ := h₂
    f_p := by rw [← h.hp₁, ← hf₁, reassoc_of% h₁] }⟩

Depends on / 依赖: exists_lift, h.hp, h.isPullback.exists_lift, isPullback, reassoc_of
-/
lemma nonempty (w : g₁ ≫ f₁ = g₂ ≫ f₂) (hf₁ : g₁ ≫ f₁ = b) :
    Nonempty (h.LiftStruct g₁ g₂ b) := by
  obtain ⟨l, h₁, h₂⟩ := h.isPullback.exists_lift g₁ g₂ w
  exact ⟨{
    f := l
    f_p₁ := h₁
    f_p₂ := h₂
    f_p := by rw [← h.hp₁, ← hf₁, reassoc_of% h₁] }⟩

end LiftStruct

end

variable {X S : C} {f : X ⟶ S} (h : ChosenPullback f f)

/--
Definition of `Diagonal` / `Diagonal` 的定义

English:
abbreviation Diagonal
  body: h.LiftStruct (𝟙 X) (𝟙 X) f

中文:
缩写 Diagonal
  定义体: h.LiftStruct (𝟙 X) (𝟙 X) f

Depends on / 依赖: LiftStruct, h.LiftStruct
-/
abbrev Diagonal := h.LiftStruct (𝟙 X) (𝟙 X) f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty h.Diagonal
  body: by apply LiftStruct.nonempty <;> cat_disch

中文:
实例 :
  签名: 非空 h.Diagonal
  定义体: by apply LiftStruct.nonempty <;> cat_disch

Depends on / 依赖: LiftStruct, LiftStruct.nonempty, cat_disch, nonempty
-/
instance : Nonempty h.Diagonal := by apply LiftStruct.nonempty <;> cat_disch

end ChosenPullback

variable {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
  (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃) (h₁₃ : ChosenPullback f₁ f₃)

/--
Definition of `ChosenPullback₃` / `ChosenPullback₃` 的定义

English:
structure ChosenPullback₃
  parameters: where
  axioms and operations (7):
    - chosenPullback : ChosenPullback h₁₂.p₂ h₂₃.p₁
    - p : chosenPullback.pullback ⟶ S  [default: chosenPullback.p₁ ≫ h₁₂.p]
    - p₁ : chosenPullback.pullback ⟶ X₁  [default: chosenPullback.p₁ ≫ h₁₂.p₁]
    - p₃ : chosenPullback.pullback ⟶ X₃  [default: chosenPullback.p₂ ≫ h₂₃.p₂]
    - l : h₁₃.LiftStruct p₁ p₃ p
    - hp₁ : chosenPullback.p₁ ≫ h₁₂.p₁ = p₁  [default: by cat_disch]
    - hp₃ : chosenPullback.p₂ ≫ h₂₃.p₂ = p₃  [default: by cat_disch]

中文:
结构 ChosenPullback₃
  参数: where
  公理与运算 (7 个):
    - chosenPullback : ChosenPullback h₁₂.p₂ h₂₃.p₁
    - p : chosenPullback.pullback ⟶ S  [默认: chosenPullback.p₁ ≫ h₁₂.p]
    - p₁ : chosenPullback.pullback ⟶ X₁  [默认: chosenPullback.p₁ ≫ h₁₂.p₁]
    - p₃ : chosenPullback.pullback ⟶ X₃  [默认: chosenPullback.p₂ ≫ h₂₃.p₂]
    - l : h₁₃.LiftStruct p₁ p₃ p
    - hp₁ : chosenPullback.p₁ ≫ h₁₂.p₁ = p₁  [默认: by cat_disch]
    - hp₃ : chosenPullback.p₂ ≫ h₂₃.p₂ = p₃  [默认: by cat_disch]

Depends on / 依赖: chosenPullback, chosenPullback.p
-/
structure ChosenPullback₃ where
  /-- A chosen pullback of `h₁₂.pullback` and `h₂₃.pullback` over `X₂`. -/
  chosenPullback : ChosenPullback h₁₂.p₂ h₂₃.p₁
  /-- The projection from the wide pullback of `(f₁, f₂, f₃)` to `S`. -/
  p : chosenPullback.pullback ⟶ S := chosenPullback.p₁ ≫ h₁₂.p
  /-- The projection from the wide pullback of `(f₁, f₂, f₃)` to `X₁`. -/
  p₁ : chosenPullback.pullback ⟶ X₁ := chosenPullback.p₁ ≫ h₁₂.p₁
  /-- The projection from the wide pullback of `(f₁, f₂, f₃)` to `X₃`. -/
  p₃ : chosenPullback.pullback ⟶ X₃ := chosenPullback.p₂ ≫ h₂₃.p₂
  /-- A morphism from the wide pullback `(f₁, f₂, f₃)` to the pullback of `f₁` and `f₃`
  that is compatible with projections. -/
  l : h₁₃.LiftStruct p₁ p₃ p
  hp₁ : chosenPullback.p₁ ≫ h₁₂.p₁ = p₁ := by cat_disch
  hp₃ : chosenPullback.p₂ ≫ h₂₃.p₂ = p₃ := by cat_disch

namespace ChosenPullback₃

variable {h₁₂ h₂₃ h₁₃} (h : ChosenPullback₃ h₁₂ h₂₃ h₁₃)

/--
Definition of `pullback` / `pullback` 的定义

English:
abbreviation pullback
  body: h.chosenPullback.pullback

中文:
缩写 pullback
  定义体: h.chosenPullback.pullback

Depends on / 依赖: chosenPullback, h.chosenPullback.pullback, pullback
-/
abbrev pullback := h.chosenPullback.pullback

/--
Definition of `p₁₃` / `p₁₃` 的定义

English:
definition p₁₃
  signature: : h.pullback ⟶ h₁₃.pullback
  body: h.l.f

中文:
定义 p₁₃
  签名: : h.pullback ⟶ h₁₃.pullback
  定义体: h.l.f

Depends on / 依赖: h.l.f
-/
def p₁₃ : h.pullback ⟶ h₁₃.pullback := h.l.f

/--
Definition of `p₁₂` / `p₁₂` 的定义

English:
definition p₁₂
  signature: : h.pullback ⟶ h₁₂.pullback
  body: h.chosenPullback.p₁

中文:
定义 p₁₂
  签名: : h.pullback ⟶ h₁₂.pullback
  定义体: h.chosenPullback.p₁

Depends on / 依赖: chosenPullback, h.chosenPullback.p
-/
def p₁₂ : h.pullback ⟶ h₁₂.pullback := h.chosenPullback.p₁

/--
Definition of `p₂₃` / `p₂₃` 的定义

English:
definition p₂₃
  signature: : h.pullback ⟶ h₂₃.pullback
  body: h.chosenPullback.p₂

中文:
定义 p₂₃
  签名: : h.pullback ⟶ h₂₃.pullback
  定义体: h.chosenPullback.p₂

Depends on / 依赖: chosenPullback, h.chosenPullback.p
-/
def p₂₃ : h.pullback ⟶ h₂₃.pullback := h.chosenPullback.p₂

/--
Definition of `p₂` / `p₂` 的定义

English:
definition p₂
  signature: : h.pullback ⟶ X₂
  body: h.chosenPullback.p

@[reassoc (attr := simp)]

中文:
定义 p₂
  签名: : h.pullback ⟶ X₂
  定义体: h.chosenPullback.p

@[reassoc (attr := simp)]

Depends on / 依赖: chosenPullback, h.chosenPullback.p
-/
def p₂ : h.pullback ⟶ X₂ := h.chosenPullback.p

@[reassoc (attr := simp)]
/--
lemma `p₁₂_p₁` / 引理 `p₁₂_p₁`

English:
lemma p₁₂_p₁
  statement: h.p₁₂ ≫ h₁₂.p₁ = h.p₁
  proof: by simp [p₁₂, hp₁]

@[reassoc (attr := simp)]

中文:
引理 p₁₂_p₁
  结论: h.p₁₂ ≫ h₁₂.p₁ = h.p₁
  证明: by simp [p₁₂, hp₁]

@[reassoc (attr := simp)]
-/
lemma p₁₂_p₁ : h.p₁₂ ≫ h₁₂.p₁ = h.p₁ := by simp [p₁₂, hp₁]

@[reassoc (attr := simp)]
/--
lemma `p₁₂_p₂` / 引理 `p₁₂_p₂`

English:
lemma p₁₂_p₂
  statement: h.p₁₂ ≫ h₁₂.p₂ = h.p₂
  proof: by simp [p₁₂, p₂]

@[reassoc (attr := simp)]

中文:
引理 p₁₂_p₂
  结论: h.p₁₂ ≫ h₁₂.p₂ = h.p₂
  证明: by simp [p₁₂, p₂]

@[reassoc (attr := simp)]
-/
lemma p₁₂_p₂ : h.p₁₂ ≫ h₁₂.p₂ = h.p₂ := by simp [p₁₂, p₂]

@[reassoc (attr := simp)]
/--
lemma `p₂₃_p₂` / 引理 `p₂₃_p₂`

English:
lemma p₂₃_p₂
  statement: h.p₂₃ ≫ h₂₃.p₁ = h.p₂
  proof: by simp [p₂₃, p₂]

@[reassoc (attr := simp)]

中文:
引理 p₂₃_p₂
  结论: h.p₂₃ ≫ h₂₃.p₁ = h.p₂
  证明: by simp [p₂₃, p₂]

@[reassoc (attr := simp)]
-/
lemma p₂₃_p₂ : h.p₂₃ ≫ h₂₃.p₁ = h.p₂ := by simp [p₂₃, p₂]

@[reassoc (attr := simp)]
/--
lemma `p₂₃_p₃` / 引理 `p₂₃_p₃`

English:
lemma p₂₃_p₃
  statement: h.p₂₃ ≫ h₂₃.p₂ = h.p₃
  proof: by simp [p₂₃, hp₃]

@[reassoc (attr := simp)]

中文:
引理 p₂₃_p₃
  结论: h.p₂₃ ≫ h₂₃.p₂ = h.p₃
  证明: by simp [p₂₃, hp₃]

@[reassoc (attr := simp)]
-/
lemma p₂₃_p₃ : h.p₂₃ ≫ h₂₃.p₂ = h.p₃ := by simp [p₂₃, hp₃]

@[reassoc (attr := simp)]
/--
lemma `p₁₃_p₁` / 引理 `p₁₃_p₁`

English:
lemma p₁₃_p₁
  statement: h.p₁₃ ≫ h₁₃.p₁ = h.p₁
  proof: by simp [p₁₃]

@[reassoc (attr := simp)]

中文:
引理 p₁₃_p₁
  结论: h.p₁₃ ≫ h₁₃.p₁ = h.p₁
  证明: by simp [p₁₃]

@[reassoc (attr := simp)]
-/
lemma p₁₃_p₁ : h.p₁₃ ≫ h₁₃.p₁ = h.p₁ := by simp [p₁₃]

@[reassoc (attr := simp)]
/--
lemma `p₁₃_p₃` / 引理 `p₁₃_p₃`

English:
lemma p₁₃_p₃
  statement: h.p₁₃ ≫ h₁₃.p₂ = h.p₃
  proof: by simp [p₁₃]

@[reassoc (attr := simp)]

中文:
引理 p₁₃_p₃
  结论: h.p₁₃ ≫ h₁₃.p₂ = h.p₃
  证明: by simp [p₁₃]

@[reassoc (attr := simp)]
-/
lemma p₁₃_p₃ : h.p₁₃ ≫ h₁₃.p₂ = h.p₃ := by simp [p₁₃]

@[reassoc (attr := simp)]
/--
lemma `w₁` / 引理 `w₁`

English:
lemma w₁
  statement: h.p₁ ≫ f₁ = h.p
  proof: by
  simpa only [← hp₁, Category.assoc, h₁₃.hp₁, h.l.f_p] using h.l.f_p₁.symm =≫ f₁

@[reassoc (attr := simp)]

中文:
引理 w₁
  结论: h.p₁ ≫ f₁ = h.p
  证明: by
  simpa only [← hp₁, Category.assoc, h₁₃.hp₁, h.l.f_p] using h.l.f_p₁.symm =≫ f₁

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, h.l.f_p
-/
lemma w₁ : h.p₁ ≫ f₁ = h.p := by
  simpa only [← hp₁, Category.assoc, h₁₃.hp₁, h.l.f_p] using h.l.f_p₁.symm =≫ f₁

@[reassoc (attr := simp)]
/--
lemma `w₃` / 引理 `w₃`

English:
lemma w₃
  statement: h.p₃ ≫ f₃ = h.p
  proof: by
  simpa only [← hp₃, Category.assoc, h₁₃.hp₂, h.l.f_p] using h.l.f_p₂.symm =≫ f₃

@[reassoc (attr := simp)]

中文:
引理 w₃
  结论: h.p₃ ≫ f₃ = h.p
  证明: by
  simpa only [← hp₃, Category.assoc, h₁₃.hp₂, h.l.f_p] using h.l.f_p₂.symm =≫ f₃

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, h.l.f_p
-/
lemma w₃ : h.p₃ ≫ f₃ = h.p := by
  simpa only [← hp₃, Category.assoc, h₁₃.hp₂, h.l.f_p] using h.l.f_p₂.symm =≫ f₃

@[reassoc (attr := simp)]
/--
lemma `w₂` / 引理 `w₂`

English:
lemma w₂
  statement: h.p₂ ≫ f₂ = h.p
  proof: by
  rw [← p₂₃_p₂_assoc]; rw [h₂₃.condition]; rw [← w₃]; rw [p₂₃_p₃_assoc]

@[reassoc (attr := simp)]

中文:
引理 w₂
  结论: h.p₂ ≫ f₂ = h.p
  证明: by
  rw [← p₂₃_p₂_assoc]; rw [h₂₃.condition]; rw [← w₃]; rw [p₂₃_p₃_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: condition
-/
lemma w₂ : h.p₂ ≫ f₂ = h.p := by
  rw [← p₂₃_p₂_assoc]; rw [h₂₃.condition]; rw [← w₃]; rw [p₂₃_p₃_assoc]

@[reassoc (attr := simp)]
/--
lemma `p₁₂_p` / 引理 `p₁₂_p`

English:
lemma p₁₂_p
  statement: h.p₁₂ ≫ h₁₂.p = h.p
  proof: by
  rw [← h₁₂.hp₂]; rw [p₁₂_p₂_assoc]; rw [w₂]

@[reassoc (attr := simp)]

中文:
引理 p₁₂_p
  结论: h.p₁₂ ≫ h₁₂.p = h.p
  证明: by
  rw [← h₁₂.hp₂]; rw [p₁₂_p₂_assoc]; rw [w₂]

@[reassoc (attr := simp)]
-/
lemma p₁₂_p : h.p₁₂ ≫ h₁₂.p = h.p := by
  rw [← h₁₂.hp₂]; rw [p₁₂_p₂_assoc]; rw [w₂]

@[reassoc (attr := simp)]
/--
lemma `p₂₃_p` / 引理 `p₂₃_p`

English:
lemma p₂₃_p
  statement: h.p₂₃ ≫ h₂₃.p = h.p
  proof: by
  rw [← h₂₃.hp₂]; rw [p₂₃_p₃_assoc]; rw [w₃]

@[reassoc (attr := simp)]

中文:
引理 p₂₃_p
  结论: h.p₂₃ ≫ h₂₃.p = h.p
  证明: by
  rw [← h₂₃.hp₂]; rw [p₂₃_p₃_assoc]; rw [w₃]

@[reassoc (attr := simp)]
-/
lemma p₂₃_p : h.p₂₃ ≫ h₂₃.p = h.p := by
  rw [← h₂₃.hp₂]; rw [p₂₃_p₃_assoc]; rw [w₃]

@[reassoc (attr := simp)]
/--
lemma `p₁₃_p` / 引理 `p₁₃_p`

English:
lemma p₁₃_p
  statement: h.p₁₃ ≫ h₁₃.p = h.p
  proof: by
  rw [← h₁₃.hp₁]; rw [p₁₃_p₁_assoc]; rw [w₁]

中文:
引理 p₁₃_p
  结论: h.p₁₃ ≫ h₁₃.p = h.p
  证明: by
  rw [← h₁₃.hp₁]; rw [p₁₃_p₁_assoc]; rw [w₁]
-/
lemma p₁₃_p : h.p₁₃ ≫ h₁₃.p = h.p := by
  rw [← h₁₃.hp₁]; rw [p₁₃_p₁_assoc]; rw [w₁]

/--
lemma `p₁₂_eq_lift` / 引理 `p₁₂_eq_lift`

English:
lemma p₁₂_eq_lift
  statement: h.p₁₂ = h₁₂.isPullback.lift h.p₁ h.p₂ (by simp)
  proof: by
  cat_disch

中文:
引理 p₁₂_eq_lift
  结论: h.p₁₂ = h₁₂.isPullback.lift h.p₁ h.p₂ (by simp)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma p₁₂_eq_lift : h.p₁₂ = h₁₂.isPullback.lift h.p₁ h.p₂ (by simp) := by
  cat_disch

/--
lemma `p₂₃_eq_lift` / 引理 `p₂₃_eq_lift`

English:
lemma p₂₃_eq_lift
  statement: h.p₂₃ = h₂₃.isPullback.lift h.p₂ h.p₃ (by simp)
  proof: by
  cat_disch

中文:
引理 p₂₃_eq_lift
  结论: h.p₂₃ = h₂₃.isPullback.lift h.p₂ h.p₃ (by simp)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma p₂₃_eq_lift : h.p₂₃ = h₂₃.isPullback.lift h.p₂ h.p₃ (by simp) := by
  cat_disch

/--
lemma `p₁₃_eq_lift` / 引理 `p₁₃_eq_lift`

English:
lemma p₁₃_eq_lift
  statement: h.p₁₃ = h₁₃.isPullback.lift h.p₁ h.p₃ (by simp)
  proof: by
  cat_disch

中文:
引理 p₁₃_eq_lift
  结论: h.p₁₃ = h₁₃.isPullback.lift h.p₁ h.p₃ (by simp)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma p₁₃_eq_lift : h.p₁₃ = h₁₃.isPullback.lift h.p₁ h.p₃ (by simp) := by
  cat_disch

/--
lemma `exists_lift` / 引理 `exists_lift`

English:
lemma exists_lift
  statement: {Y : C} (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (g₃ : Y ⟶ X₃) (b : Y ⟶ S)
  proof: by
  obtain ⟨φ₁₂, w₁, w₂⟩ := h₁₂.isPullback.exists_lift g₁ g₂ (by cat_disch)
  obtain ⟨φ₂₃, w₂', w₃⟩ := h₂₃.isPullback.exists_lift g₂ g₃ (by cat_disch)
  obtain ⟨φ, w₁₂, w₂₃⟩ := h.chosenPullback.isPullback.exists_lift φ₁₂ φ₂₃ (by cat_disch)
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [← w₁, ← w₁₂, Category.asso

中文:
引理 存在_lift
  结论: {Y : C} (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (g₃ : Y ⟶ X₃) (b : Y ⟶ S)
  证明: by
  obtain ⟨φ₁₂, w₁, w₂⟩ := h₁₂.isPullback.exists_lift g₁ g₂ (by cat_disch)
  obtain ⟨φ₂₃, w₂', w₃⟩ := h₂₃.isPullback.exists_lift g₂ g₃ (by cat_disch)
  obtain ⟨φ, w₁₂, w₂₃⟩ := h.chosenPullback.isPullback.exists_lift φ₁₂ φ₂₃ (by cat_disch)
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [← w₁, ← w₁₂, Category.asso

Depends on / 依赖: Category, Category.assoc, cat_disch, chosenPullback, exists_lift, h.chosenPullback.isPullback.exists_lift, isPullback, isPullback.exists_lift
-/
lemma exists_lift {Y : C} (g₁ : Y ⟶ X₁) (g₂ : Y ⟶ X₂) (g₃ : Y ⟶ X₃) (b : Y ⟶ S)
    (hg₁ : g₁ ≫ f₁ = b) (hg₂ : g₂ ≫ f₂ = b) (hg₃ : g₃ ≫ f₃ = b) :
    exists (φ : Y ⟶ h.pullback), φ ≫ h.p₁ = g₁ ∧ φ ≫ h.p₂ = g₂ ∧ φ ≫ h.p₃ = g₃ := by
  obtain ⟨φ₁₂, w₁, w₂⟩ := h₁₂.isPullback.exists_lift g₁ g₂ (by cat_disch)
  obtain ⟨φ₂₃, w₂', w₃⟩ := h₂₃.isPullback.exists_lift g₂ g₃ (by cat_disch)
  obtain ⟨φ, w₁₂, w₂₃⟩ := h.chosenPullback.isPullback.exists_lift φ₁₂ φ₂₃ (by cat_disch)
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [← w₁, ← w₁₂, Category.assoc, ← p₁₂, p₁₂_p₁]
  · rw [← w₂, ← w₁₂, Category.assoc, ← p₁₂, p₁₂_p₂]
  · rw [← w₃, ← w₂₃, Category.assoc, ← p₂₃, p₂₃_p₃]

/--
lemma `isPullback₂` / 引理 `isPullback₂`

English:
lemma isPullback₂
  statement: IsPullback h.p₁₂ h.p₂₃ h₁₂.p₂ h₂₃.p₁
  proof: h.chosenPullback.isPullback

@[ext]

中文:
引理 isPullback₂
  结论: 是拉回 h.p₁₂ h.p₂₃ h₁₂.p₂ h₂₃.p₁
  证明: h.chosenPullback.isPullback

@[ext]

Depends on / 依赖: chosenPullback, h.chosenPullback.isPullback, isPullback
-/
lemma isPullback₂ : IsPullback h.p₁₂ h.p₂₃ h₁₂.p₂ h₂₃.p₁ := h.chosenPullback.isPullback

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {Y : C} {φ φ' : Y ⟶ h.pullback}
  proof: by
  apply h.isPullback₂.hom_ext <;> cat_disch

中文:
引理 hom_ext
  结论: {Y : C} {φ φ' : Y ⟶ h.pullback}
  证明: by
  apply h.isPullback₂.hom_ext <;> cat_disch

Depends on / 依赖: cat_disch, h.isPullback, hom_ext
-/
lemma hom_ext {Y : C} {φ φ' : Y ⟶ h.pullback}
    (h₁ : φ ≫ h.p₁ = φ' ≫ h.p₁) (h₂ : φ ≫ h.p₂ = φ' ≫ h.p₂)
    (h₃ : φ ≫ h.p₃ = φ' ≫ h.p₃) : φ = φ' := by
  apply h.isPullback₂.hom_ext <;> cat_disch

/--
lemma `isPullback₁` / 引理 `isPullback₁`

English:
lemma isPullback₁
  statement: IsPullback h.p₁₂ h.p₁₃ h₁₂.p₁ h₁₃.p₁
  proof: .mk' (by simp) (fun _ _ _ h₁ h₂ => h.hom_ext (by simpa using h₁ =≫ h₁₂.p₁)
      (by simpa using h₁ =≫ h₁₂.p₂) (by simpa using h₂ =≫ h₁₃.p₂))
    (fun _ a b w => by
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
        h.exists_lift (a ≫ h₁₂.p₁) (a ≫ h₁₂.p₂) (b ≫ h₁₃.p₂) _ rfl
          (by simp) (by simpa usi

中文:
引理 isPullback₁
  结论: 是拉回 h.p₁₂ h.p₁₃ h₁₂.p₁ h₁₃.p₁
  证明: .mk' (by simp) (fun _ _ _ h₁ h₂ => h.hom_ext (by simpa using h₁ =≫ h₁₂.p₁)
      (by simpa using h₁ =≫ h₁₂.p₂) (by simpa using h₂ =≫ h₁₃.p₂))
    (fun _ a b w => by
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
        h.exists_lift (a ≫ h₁₂.p₁) (a ≫ h₁₂.p₂) (b ≫ h₁₃.p₂) _ rfl
          (by simp) (by simpa usi

Depends on / 依赖: cat_disch, exists_lift, h.exists_lift, h.hom_ext, hom_ext, w.symm
-/
lemma isPullback₁ : IsPullback h.p₁₂ h.p₁₃ h₁₂.p₁ h₁₃.p₁ :=
  .mk' (by simp) (fun _ _ _ h₁ h₂ => h.hom_ext (by simpa using h₁ =≫ h₁₂.p₁)
      (by simpa using h₁ =≫ h₁₂.p₂) (by simpa using h₂ =≫ h₁₃.p₂))
    (fun _ a b w => by
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
        h.exists_lift (a ≫ h₁₂.p₁) (a ≫ h₁₂.p₂) (b ≫ h₁₃.p₂) _ rfl
          (by simp) (by simpa using w.symm =≫ f₁)
      exact ⟨φ, by cat_disch, by cat_disch⟩)

/--
lemma `isPullback₃` / 引理 `isPullback₃`

English:
lemma isPullback₃
  statement: IsPullback h.p₁₃ h.p₂₃ h₁₃.p₂ h₂₃.p₂
  proof: .mk' (by simp) (fun _ _ _ h₁ h₂ => h.hom_ext (by simpa using h₁ =≫ h₁₃.p₁)
      (by simpa using h₂ =≫ h₂₃.p₁) (by simpa using h₁ =≫ h₁₃.p₂))
    (fun _ a b w => by
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
        h.exists_lift (a ≫ h₁₃.p₁) (b ≫ h₂₃.p₁) (a ≫ h₁₃.p₂) _ rfl
          (by simpa using w.symm 

中文:
引理 isPullback₃
  结论: 是拉回 h.p₁₃ h.p₂₃ h₁₃.p₂ h₂₃.p₂
  证明: .mk' (by simp) (fun _ _ _ h₁ h₂ => h.hom_ext (by simpa using h₁ =≫ h₁₃.p₁)
      (by simpa using h₂ =≫ h₂₃.p₁) (by simpa using h₁ =≫ h₁₃.p₂))
    (fun _ a b w => by
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
        h.exists_lift (a ≫ h₁₃.p₁) (b ≫ h₂₃.p₁) (a ≫ h₁₃.p₂) _ rfl
          (by simpa using w.symm 

Depends on / 依赖: cat_disch, exists_lift, h.exists_lift, h.hom_ext, hom_ext, w.symm
-/
lemma isPullback₃ : IsPullback h.p₁₃ h.p₂₃ h₁₃.p₂ h₂₃.p₂ :=
  .mk' (by simp) (fun _ _ _ h₁ h₂ => h.hom_ext (by simpa using h₁ =≫ h₁₃.p₁)
      (by simpa using h₂ =≫ h₂₃.p₁) (by simpa using h₁ =≫ h₁₃.p₂))
    (fun _ a b w => by
      obtain ⟨φ, hφ₁, hφ₂, hφ₃⟩ :=
        h.exists_lift (a ≫ h₁₃.p₁) (b ≫ h₂₃.p₁) (a ≫ h₁₃.p₂) _ rfl
          (by simpa using w.symm =≫ f₃) (by simp)
      exact ⟨φ, by cat_disch, by cat_disch⟩)

end ChosenPullback₃

end CategoryTheory.Limits
