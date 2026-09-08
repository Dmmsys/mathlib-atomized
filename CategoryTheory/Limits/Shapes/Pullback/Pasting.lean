/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pasting lemma

This file proves the pasting lemma for pullbacks. That is, given the following diagram:
```
  X₁ - f₁ -> X₂ - f₂ -> X₃
  |          |          |
  i₁         i₂         i₃
  ∨          ∨          ∨
  Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
if the right square is a pullback, then the left square is a pullback iff the big square is a
pullback.

## Main results
* `pasteHorizIsPullback` shows that the big square is a pullback if both the small squares are.
* `leftSquareIsPullback` shows that the left square is a pullback if the other two are.
* `pullbackRightPullbackFstIso` shows, using the `pullback` API, that
  `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y`.
* `pullbackLeftPullbackSndIso` shows, using the `pullback` API, that
  `(X ×[Z] Y) ×[Y] W ≅ X ×[Z] W`.

-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section PasteLemma
section PastePullbackHoriz

/- Let's consider the following diagram
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
↓          ↓          ↓
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
where `t₁` denotes the cone corresponding to the left square, and `t₂` denotes the cone
corresponding to the right square.
-/

variable {X₃ Y₁ Y₂ Y₃ : C} {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} {i₃ : X₃ ⟶ Y₃}

/-- The `PullbackCone` obtained by pasting two `PullbackCone`'s horizontally -/
/-
**CategoryTheory.Limits.PullbackCone.pasteHoriz** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.PullbackCone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X₃ Y₁ Y₂
 Y₃ : C} →       {g₁ : Y₁ ⟶ Y₂} →         {g₂ : Y₂ ⟶ Y₃} →           {i₃ : X₃ ⟶ 
Y₃} →             (t₂ : CategoryTheory.Limits.PullbackCone g₂ i₃) →             
  {i₂ : t₂.pt ⟶ Y₂} →                 CategoryTheory.Limits.PullbackCone g₁ i₂ →
                   i₂ = t₂.fst → CategoryTheory.Limits.PullbackCone (CategoryThe
ory.CategoryStruct.comp g₁ g₂) i₃
参数：t₂ : CategoryTheory.Limits.PullbackCone g₂ i₃；CategoryTheory.CategoryStruct.c
omp g₁ g₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `PullbackCone` obtained by pasting two `PullbackCone`'s horizontally
-/
abbrev PullbackCone.pasteHoriz
    (t₂ : PullbackCone g₂ i₃) {i₂ : t₂.pt ⟶ Y₂} (t₁ : PullbackCone g₁ i₂) (hi₂ : i₂ = t₂.fst) :
    PullbackCone (g₁ ≫ g₂) i₃ :=
  PullbackCone.mk t₁.fst (t₁.snd ≫ t₂.snd)
    (by rw [reassoc_of% t₁.condition, Category.assoc, ← t₂.condition, ← hi₂])

variable (t₂ : PullbackCone g₂ i₃) {i₂ : t₂.pt ⟶ Y₂} (t₁ : PullbackCone g₁ i₂) (hi₂ : i₂ = t₂.fst)

local notation "f₂" => t₂.snd
local notation "X₁" => t₁.pt
local notation "i₁" => t₁.fst
local notation "f₁" => t₁.snd

variable {t₁} {t₂}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
↓          ↓          ↓
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
Then the big square is a pullback if both the small squares are.
-/
/-
**CategoryTheory.Limits.pasteHorizIsPullback** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：pasteHorizIsPullback (H : IsLimit t₂) (H' : IsLimit t₁) : IsLimit (t₂.past
eHoriz t₁ hi₂)
参数：H : IsLimit t₂；H' : IsLimit t₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
↓          ↓          ↓
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
Then the big square is a pullback if both the small squares are.
-/
def pasteHorizIsPullback (H : IsLimit t₂) (H' : IsLimit t₁) : IsLimit (t₂.pasteHoriz t₁ hi₂) := by
  apply PullbackCone.isLimitAux'
  intro s
  -- Obtain the lift from lifting from both the small squares consecutively.
  obtain ⟨l₂, hl₂, hl₂'⟩ := PullbackCone.IsLimit.lift' H (s.fst ≫ g₁) s.snd
    (by rw [← s.condition, Category.assoc])
  obtain ⟨l₁, hl₁, hl₁'⟩ := PullbackCone.IsLimit.lift' H' s.fst l₂ (by rw [← hl₂, hi₂])
  refine ⟨l₁, hl₁, by simp [reassoc_of% hl₁', hl₂'], ?_⟩
  -- Uniqueness also follows from the universal property of both the small squares.
  intro m hm₁ hm₂
  apply PullbackCone.IsLimit.hom_ext H' (by simpa [hl₁] using hm₁)
  apply PullbackCone.IsLimit.hom_ext H
  · dsimp at hm₁
    rw [Category.assoc, ← hi₂, ← t₁.condition, reassoc_of% hm₁, hl₁', hi₂, hl₂]
  · simpa [hl₁', hl₂'] using hm₂

variable (t₁)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
↓          ↓          ↓
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
Then the left square is a pullback if the right square and the big square are.
-/
/-
**CategoryTheory.Limits.leftSquareIsPullback** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：leftSquareIsPullback (H : IsLimit t₂) (H' : IsLimit (t₂.pasteHoriz t₁ hi₂)
) : IsLimit t₁
参数：H : IsLimit t₂；H' : IsLimit (t₂.pasteHoriz t₁ hi₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
↓          ↓          ↓
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
Then the left square is a pullback if the right square and the big square are.
-/
def leftSquareIsPullback (H : IsLimit t₂) (H' : IsLimit (t₂.pasteHoriz t₁ hi₂)) : IsLimit t₁ := by
  apply PullbackCone.isLimitAux'
  intro s
  -- Obtain the induced morphism from the universal property of the big square
  obtain ⟨l, hl, hl'⟩ := PullbackCone.IsLimit.lift' H' s.fst (s.snd ≫ f₂)
    (by rw [Category.assoc, ← t₂.condition, reassoc_of% s.condition, ← hi₂])
  refine ⟨l, hl, ?_, ?_⟩
  -- To check that `l` is compatible with the projections, we use the universal property of `t₂`
  · apply PullbackCone.IsLimit.hom_ext H
    · simp [← s.condition, ← hl, ← t₁.condition, ← hi₂]
    · simpa using hl'
  -- Uniqueness of the lift follows from the universal property of the big square
  · intro m hm₁ hm₂
    apply PullbackCone.IsLimit.hom_ext H'
    · simpa [hm₁] using hl.symm
    · simpa [← hm₂] using hl'.symm

/-- Given that the right square is a pullback, the pasted square is a pullback iff the left
square is. -/
/-
**CategoryTheory.Limits.pasteHorizIsPullbackEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：pasteHorizIsPullbackEquiv (H : IsLimit t₂) : IsLimit (t₂.pasteHoriz t₁ hi₂
) ≃ IsLimit t₁ where toFun H'
参数：H : IsLimit t₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given that the right square is a pullback, the pasted square is a pullback iff t
he left
square is.
-/
def pasteHorizIsPullbackEquiv (H : IsLimit t₂) : IsLimit (t₂.pasteHoriz t₁ hi₂) ≃ IsLimit t₁ where
  toFun H' := leftSquareIsPullback t₁ _ H H'
  invFun H' := pasteHorizIsPullback _ H H'
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end PastePullbackHoriz

section PastePullbackVert

/- Let's consider the following diagram
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
Let `t₁` denote the cone corresponding to the bottom square, and `t₂` denote the cone corresponding
to the top square.

-/
variable {X₁ X₂ X₃ Y₁ : C} {f₁ : X₂ ⟶ X₁} {f₂ : X₃ ⟶ X₂} {i₁ : Y₁ ⟶ X₁}

/-- The `PullbackCone` obtained by pasting two `PullbackCone`'s vertically -/
/-
**CategoryTheory.Limits.PullbackCone.pasteVert** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.PullbackCone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X₁ X₂ X₃
 Y₁ : C} →       {f₁ : X₂ ⟶ X₁} →         {f₂ : X₃ ⟶ X₂} →           {i₁ : Y₁ ⟶ 
X₁} →             (t₁ : CategoryTheory.Limits.PullbackCone i₁ f₁) →             
  {i₂ : t₁.pt ⟶ X₂} →                 CategoryTheory.Limits.PullbackCone i₂ f₂ →
                   i₂ = t₁.snd → CategoryTheory.Limits.PullbackCone i₁ (Category
Theory.CategoryStruct.comp f₂ f₁)
参数：t₁ : CategoryTheory.Limits.PullbackCone i₁ f₁；CategoryTheory.CategoryStruct.c
omp f₂ f₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `PullbackCone` obtained by pasting two `PullbackCone`'s vertically
-/
abbrev PullbackCone.pasteVert
    (t₁ : PullbackCone i₁ f₁) {i₂ : t₁.pt ⟶ X₂} (t₂ : PullbackCone i₂ f₂) (hi₂ : i₂ = t₁.snd) :
    PullbackCone i₁ (f₂ ≫ f₁) :=
  PullbackCone.mk (t₂.fst ≫ t₁.fst) t₂.snd
    (by rw [← reassoc_of% t₂.condition, Category.assoc, t₁.condition, ← hi₂])

variable (t₁ : PullbackCone i₁ f₁) {i₂ : t₁.pt ⟶ X₂} (t₂ : PullbackCone i₂ f₂) (hi₂ : i₂ = t₁.snd)

local notation "Y₂" => t₁.pt
local notation "g₁" => t₁.fst
local notation "i₂" => t₁.snd
local notation "Y₃" => t₂.pt
local notation "g₂" => t₂.fst
local notation "i₃" => t₂.snd

set_option backward.defeqAttrib.useBackward true in
/-- Pasting two pullback cones vertically is isomorphic to the pullback cone obtained by flipping
them, pasting horizontally, and then flipping the result again. -/
/-
**CategoryTheory.Limits.PullbackCone.pasteVertFlip** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.PullbackCone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X₁ X₂ X₃
 Y₁ : C} →       {f₁ : X₂ ⟶ X₁} →         {f₂ : X₃ ⟶ X₂} →           {i₁ : Y₁ ⟶ 
X₁} →             (t₁ : CategoryTheory.Limits.PullbackCone i₁ f₁) →             
  {i₂ : t₁.pt ⟶ X₂} →                 (t₂ : CategoryTheory.Limits.PullbackCone i
₂ f₂) →                   (hi₂ : i₂ = t₁.snd) → (t₁.pasteVert t₂ hi₂).flip ≅ t₁.
flip.pasteHoriz t₂.flip hi₂
参数：t₁ : CategoryTheory.Limits.PullbackCone i₁ f₁；t₂ : CategoryTheory.Limits.Pull
backCone i₂ f₂；hi₂ : i₂ = t₁.snd；t₁.pasteVert t₂ hi₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pasting two pullback cones vertically is isomorphic to the pullback cone obtaine
d by flipping
them, pasting horizontally, and then flipping the result again.
-/
def PullbackCone.pasteVertFlip : (t₁.pasteVert t₂ hi₂).flip ≅ (t₁.flip.pasteHoriz t₂.flip hi₂) :=
  PullbackCone.ext (Iso.refl _) (by simp) (by simp)

variable {t₁} {t₂}

/-- Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The big square is a pullback if both the small squares are.
-/
/-
**CategoryTheory.Limits.pasteVertIsPullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：pasteVertIsPullback (H₁ : IsLimit t₁) (H₂ : IsLimit t₂) : IsLimit (t₁.past
eVert t₂ hi₂)
参数：H₁ : IsLimit t₁；H₂ : IsLimit t₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The big square is a pullback if both the small squares are.
-/
def pasteVertIsPullback (H₁ : IsLimit t₁) (H₂ : IsLimit t₂) : IsLimit (t₁.pasteVert t₂ hi₂) := by
  apply PullbackCone.isLimitOfFlip <| IsLimit.ofIsoLimit _ (t₁.pasteVertFlip t₂ hi₂).symm
  exact pasteHorizIsPullback hi₂ (PullbackCone.flipIsLimit H₁) (PullbackCone.flipIsLimit H₂)

variable (t₂)

/-- Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The top square is a pullback if the bottom square and the big square are.
-/
/-
**CategoryTheory.Limits.topSquareIsPullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：topSquareIsPullback (H₁ : IsLimit t₁) (H₂ : IsLimit (t₁.pasteVert t₂ hi₂))
 : IsLimit t₂
参数：H₁ : IsLimit t₁；H₂ : IsLimit (t₁.pasteVert t₂ hi₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The top square is a pullback if the bottom square and the big square are.
-/
def topSquareIsPullback (H₁ : IsLimit t₁) (H₂ : IsLimit (t₁.pasteVert t₂ hi₂)) : IsLimit t₂ :=
  PullbackCone.isLimitOfFlip
    (leftSquareIsPullback _ hi₂ (PullbackCone.flipIsLimit H₁) (PullbackCone.flipIsLimit H₂))

/-- Given that the bottom square is a pullback, the pasted square is a pullback iff the top
square is. -/
/-
**CategoryTheory.Limits.pasteVertIsPullbackEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：pasteVertIsPullbackEquiv (H : IsLimit t₁) : IsLimit (t₁.pasteVert t₂ hi₂) 
≃ IsLimit t₂ where toFun H'
参数：H : IsLimit t₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given that the bottom square is a pullback, the pasted square is a pullback iff 
the top
square is.
-/
def pasteVertIsPullbackEquiv (H : IsLimit t₁) : IsLimit (t₁.pasteVert t₂ hi₂) ≃ IsLimit t₂ where
  toFun H' := topSquareIsPullback t₂ _ H H'
  invFun H' := pasteVertIsPullback _ H H'
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end PastePullbackVert

section PastePushoutHoriz

/- Let's consider the following diagram
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
where `t₁` denotes the left pushout cocone, and `t₂` denotes the right pushout cocone.
-/
variable {X₁ X₂ X₃ Y₁ : C} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {i₁ : X₁ ⟶ Y₁}

/-- The pushout cocone obtained by pasting two pushout cocones horizontally. -/
/-
**CategoryTheory.Limits.PushoutCocone.pasteHoriz** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.PushoutCocone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X₁ X₂ X₃
 Y₁ : C} →       {f₁ : X₁ ⟶ X₂} →         {f₂ : X₂ ⟶ X₃} →           {i₁ : X₁ ⟶ 
Y₁} →             (t₁ : CategoryTheory.Limits.PushoutCocone i₁ f₁) →            
   {i₂ : X₂ ⟶ t₁.pt} →                 CategoryTheory.Limits.PushoutCocone i₂ f₂
 →                   i₂ = t₁.inr → CategoryTheory.Limits.PushoutCocone i₁ (Categ
oryTheory.CategoryStruct.comp f₁ f₂)
参数：t₁ : CategoryTheory.Limits.PushoutCocone i₁ f₁；CategoryTheory.CategoryStruct.
comp f₁ f₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushout cocone obtained by pasting two pushout cocones horizontally.
-/
abbrev PushoutCocone.pasteHoriz
    (t₁ : PushoutCocone i₁ f₁) {i₂ : X₂ ⟶ t₁.pt} (t₂ : PushoutCocone i₂ f₂) (hi₂ : i₂ = t₁.inr) :
    PushoutCocone i₁ (f₁ ≫ f₂) :=
  PushoutCocone.mk (t₁.inl ≫ t₂.inl) t₂.inr
    (by rw [reassoc_of% t₁.condition, Category.assoc, ← t₂.condition, ← hi₂])

variable (t₁ : PushoutCocone i₁ f₁) {i₂ : X₂ ⟶ t₁.pt} (t₂ : PushoutCocone i₂ f₂) (hi₂ : i₂ = t₁.inr)

local notation "Y₂" => t₁.pt
local notation "g₁" => t₁.inl
local notation "i₂" => t₁.inr
local notation "Y₃" => t₂.pt
local notation "g₂" => t₂.inl
local notation "i₃" => t₂.inr

variable {t₁} {t₂}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
Then the big square is a pushout if both the small squares are.
-/
/-
**CategoryTheory.Limits.pasteHorizIsPushout** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：pasteHorizIsPushout (H : IsColimit t₁) (H' : IsColimit t₂) : IsColimit (t₁
.pasteHoriz t₂ hi₂)
参数：H : IsColimit t₁；H' : IsColimit t₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given
```
X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃
```
Then the big square is a pushout if both the small squares are.
-/
def pasteHorizIsPushout (H : IsColimit t₁) (H' : IsColimit t₂) :
    IsColimit (t₁.pasteHoriz t₂ hi₂) := by
  apply PushoutCocone.isColimitAux'
  intro s
  -- Obtain the induced map from descending from both the small squares consecutively.
  obtain ⟨l₁, hl₁, hl₁'⟩ := PushoutCocone.IsColimit.desc' H s.inl (f₂ ≫ s.inr)
    (by rw [s.condition, Category.assoc])
  obtain ⟨l₂, hl₂, hl₂'⟩ := PushoutCocone.IsColimit.desc' H' l₁ s.inr (by rw [← hl₁', hi₂])
  refine ⟨l₂, by simp [hl₂, hl₁], hl₂', ?_⟩
  -- Uniqueness also follows from the universal property of both the small squares.
  intro m hm₁ hm₂
  apply PushoutCocone.IsColimit.hom_ext H' _ (by simpa [hl₂'] using hm₂)
  simp only [PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, Category.assoc] at hm₁ hm₂
  apply PushoutCocone.IsColimit.hom_ext H
  · rw [hm₁, ← hl₁, hl₂]
  · rw [← hi₂, reassoc_of% t₂.condition, reassoc_of% t₂.condition, hm₂, hl₂']

variable (t₂)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the right square is a pushout if the left square and the big square are.
-/
/-
**CategoryTheory.Limits.rightSquareIsPushout** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：rightSquareIsPushout (H : IsColimit t₁) (H' : IsColimit (t₁.pasteHoriz t₂ 
hi₂)) : IsColimit t₂
参数：H : IsColimit t₁；H' : IsColimit (t₁.pasteHoriz t₂ hi₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the right square is a pushout if the left square and the big square are.
-/
def rightSquareIsPushout (H : IsColimit t₁) (H' : IsColimit (t₁.pasteHoriz t₂ hi₂)) :
    IsColimit t₂ := by
  apply PushoutCocone.isColimitAux'
  intro s
  -- Obtain the induced morphism from the universal property of the big square
  obtain ⟨l, hl, hl'⟩ := PushoutCocone.IsColimit.desc' H' (g₁ ≫ s.inl) s.inr
    (by rw [reassoc_of% t₁.condition, ← hi₂, s.condition, Category.assoc])
  refine ⟨l, ?_, hl', ?_⟩
  -- To check that `l` is compatible with the projections, we use the universal property of `t₁`
  · simp only [PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, Category.assoc] at hl hl'
    apply PushoutCocone.IsColimit.hom_ext H hl
    rw [← Category.assoc, ← hi₂, t₂.condition, s.condition, Category.assoc, hl']
  -- Uniqueness of the lift follows from the universal property of the big square
  · intro m hm₁ hm₂
    apply PushoutCocone.IsColimit.hom_ext H'
    · simpa [← hm₁] using hl.symm
    · simpa [← hm₂] using hl'.symm

/-- Given that the left square is a pushout, the pasted square is a pushout iff the right square is.
-/
/-
**CategoryTheory.Limits.pasteHorizIsPushoutEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：pasteHorizIsPushoutEquiv (H : IsColimit t₁) : IsColimit (t₁.pasteHoriz t₂ 
hi₂) ≃ IsColimit t₂ where toFun H'
参数：H : IsColimit t₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given that the left square is a pushout, the pasted square is a pushout iff the 
right square is.
-/
def pasteHorizIsPushoutEquiv (H : IsColimit t₁) :
    IsColimit (t₁.pasteHoriz t₂ hi₂) ≃ IsColimit t₂ where
  toFun H' := rightSquareIsPushout t₂ _ H H'
  invFun H' := pasteHorizIsPushout _ H H'
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end PastePushoutHoriz

section PastePushoutVert

/- Let's consider the following diagram
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
Let `t₁` denote the cone corresponding to the bottom square, and `t₂` denote the cone corresponding
to the top square.
-/
variable {Y₃ Y₂ Y₁ X₃ : C} {g₂ : Y₃ ⟶ Y₂} {g₁ : Y₂ ⟶ Y₁} {i₃ : Y₃ ⟶ X₃}
variable (t₁ : PushoutCocone g₂ i₃) {i₂ : Y₂ ⟶ t₁.pt} (t₂ : PushoutCocone g₁ i₂)
  (hi₂ : i₂ = t₁.inl)

/-- The `PullbackCone` obtained by pasting two `PullbackCone`'s vertically -/
/-
**CategoryTheory.Limits.PushoutCocone.pasteVert** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.PushoutCocone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {Y₃ Y₂ Y₁
 X₃ : C} →       {g₂ : Y₃ ⟶ Y₂} →         {g₁ : Y₂ ⟶ Y₁} →           {i₃ : Y₃ ⟶ 
X₃} →             (t₁ : CategoryTheory.Limits.PushoutCocone g₂ i₃) →            
   {i₂ : Y₂ ⟶ t₁.pt} →                 CategoryTheory.Limits.PushoutCocone g₁ i₂
 →                   i₂ = t₁.inl → CategoryTheory.Limits.PushoutCocone (Category
Theory.CategoryStruct.comp g₂ g₁) i₃
参数：t₁ : CategoryTheory.Limits.PushoutCocone g₂ i₃；CategoryTheory.CategoryStruct.
comp g₂ g₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `PullbackCone` obtained by pasting two `PullbackCone`'s vertically
-/
abbrev PushoutCocone.pasteVert
    (t₁ : PushoutCocone g₂ i₃) {i₂ : Y₂ ⟶ t₁.pt} (t₂ : PushoutCocone g₁ i₂) (hi₂ : i₂ = t₁.inl) :
    PushoutCocone (g₂ ≫ g₁) i₃ :=
  PushoutCocone.mk t₂.inl (t₁.inr ≫ t₂.inr)
    (by rw [← reassoc_of% t₁.condition, Category.assoc, t₂.condition, ← hi₂])

local notation "X₂" => t₁.pt
local notation "f₂" => t₁.inr
local notation "i₂" => t₁.inl
local notation "X₁" => t₂.pt
local notation "f₁" => t₂.inr
local notation "i₁" => t₂.inl

set_option backward.defeqAttrib.useBackward true in
/-- Pasting two pushout cocones vertically is isomorphic to the pushout cocone obtained by flipping
them, pasting horizontally, and then flipping the result again. -/
/-
**CategoryTheory.Limits.PushoutCocone.pasteVertFlip** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.PushoutCocone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {Y₃ Y₂ Y₁
 X₃ : C} →       {g₂ : Y₃ ⟶ Y₂} →         {g₁ : Y₂ ⟶ Y₁} →           {i₃ : Y₃ ⟶ 
X₃} →             (t₁ : CategoryTheory.Limits.PushoutCocone g₂ i₃) →            
   {i₂ : Y₂ ⟶ t₁.pt} →                 (t₂ : CategoryTheory.Limits.PushoutCocone
 g₁ i₂) →                   (hi₂ : i₂ = t₁.inl) → (t₁.pasteVert t₂ hi₂).flip ≅ t
₁.flip.pasteHoriz t₂.flip hi₂
参数：t₁ : CategoryTheory.Limits.PushoutCocone g₂ i₃；t₂ : CategoryTheory.Limits.Pus
houtCocone g₁ i₂；hi₂ : i₂ = t₁.inl；t₁.pasteVert t₂ hi₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pasting two pushout cocones vertically is isomorphic to the pushout cocone obtai
ned by flipping
them, pasting horizontally, and then flipping the result again.
-/
def PushoutCocone.pasteVertFlip : (t₁.pasteVert t₂ hi₂).flip ≅ (t₁.flip.pasteHoriz t₂.flip hi₂) :=
  PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

variable {t₁} {t₂}

/-- Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The big square is a pushout if both the small squares are.
-/
/-
**CategoryTheory.Limits.pasteVertIsPushout** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：pasteVertIsPushout (H₁ : IsColimit t₁) (H₂ : IsColimit t₂) : IsColimit (t₁
.pasteVert t₂ hi₂)
参数：H₁ : IsColimit t₁；H₂ : IsColimit t₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The big square is a pushout if both the small squares are.
-/
def pasteVertIsPushout (H₁ : IsColimit t₁) (H₂ : IsColimit t₂) :
    IsColimit (t₁.pasteVert t₂ hi₂) := by
  apply PushoutCocone.isColimitOfFlip <| IsColimit.ofIsoColimit _ (t₁.pasteVertFlip t₂ hi₂).symm
  exact pasteHorizIsPushout hi₂ (PushoutCocone.flipIsColimit H₁) (PushoutCocone.flipIsColimit H₂)

variable (t₂)

/-- Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The bottom square is a pushout if the top square and the big square are.
-/
/-
**CategoryTheory.Limits.botSquareIsPushout** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：botSquareIsPushout (H₁ : IsColimit t₁) (H₂ : IsColimit (t₁.pasteVert t₂ hi
₂)) : IsColimit t₂
参数：H₁ : IsColimit t₁；H₂ : IsColimit (t₁.pasteVert t₂ hi₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given
```
Y₃ - i₃ -> X₃
|          |
g₂         f₂
∨          ∨
Y₂ - i₂ -> X₂
|          |
g₁         f₁
∨          ∨
Y₁ - i₁ -> X₁
```
The bottom square is a pushout if the top square and the big square are.
-/
def botSquareIsPushout (H₁ : IsColimit t₁) (H₂ : IsColimit (t₁.pasteVert t₂ hi₂)) : IsColimit t₂ :=
  PushoutCocone.isColimitOfFlip
    (rightSquareIsPushout _ hi₂ (PushoutCocone.flipIsColimit H₁) (PushoutCocone.flipIsColimit H₂))

/-- Given that the top square is a pushout, the pasted square is a pushout iff the bottom square is.
-/
/-
**CategoryTheory.Limits.pasteVertIsPushoutEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：pasteVertIsPushoutEquiv (H : IsColimit t₁) : IsColimit (t₁.pasteVert t₂ hi
₂) ≃ IsColimit t₂ where toFun H'
参数：H : IsColimit t₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given that the top square is a pushout, the pasted square is a pushout iff the b
ottom square is.
-/
def pasteVertIsPushoutEquiv (H : IsColimit t₁) :
    IsColimit (t₁.pasteVert t₂ hi₂) ≃ IsColimit t₂ where
  toFun H' := botSquareIsPushout t₂ _ H H'
  invFun H' := pasteVertIsPushout _ H H'
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end PastePushoutVert

end PasteLemma

section
/- Let's consider the following diagram of pullbacks
```
W ×[X] (X ×[Z] Y) --snd--> X ×[Z] Y --snd--> Y
  |                           |              |
 fst                         fst             g
  v                           v              v
  W --------- f' --------->   X  ---- f ---> Y
```
In this section we show that `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y`.
-/

variable {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : W ⟶ X)
variable [HasPullback f g] [HasPullback f' (pullback.fst f g)]

/-
**CategoryTheory.Limits.hasPullbackHorizPaste** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：hasPullbackHorizPaste : HasPullback (f' ≫ f) g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasPullbackHorizPaste : HasPullback (f' ≫ f) g :=
  HasLimit.mk {
    cone := (pullback.cone f g).pasteHoriz (pullback.cone f' (pullback.fst f g)) rfl
    isLimit := pasteHorizIsPullback rfl (pullback.isLimit f g)
      (pullback.isLimit f' (pullback.fst f g))
  }

/-- The canonical isomorphism `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y` -/
/-
**CategoryTheory.Limits.pullbackRightPullbackFstIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackRightPullbackFstIso : pullback f' (pullback.fst f g) ≅ pullback (f
' ≫ f) g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y`
-/
noncomputable def pullbackRightPullbackFstIso :
    pullback f' (pullback.fst f g) ≅ pullback (f' ≫ f) g :=
  IsLimit.conePointUniqueUpToIso
    (pasteHorizIsPullback rfl (pullback.isLimit f g) (pullback.isLimit f' (pullback.fst f g)))
    (pullback.isLimit (f' ≫ f) g)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackRightPullbackFstIso_hom_fst : (pullbackRightPullbackFstIso f g f')
.hom ≫ pullback.fst (f' ≫ f) g = pullback.fst f' (pullback.fst f g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem pullbackRightPullbackFstIso_hom_fst :
    (pullbackRightPullbackFstIso f g f').hom ≫ pullback.fst (f' ≫ f) g =
      pullback.fst f' (pullback.fst f g) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_snd** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackRightPullbackFstIso_hom_snd : (pullbackRightPullbackFstIso f g f')
.hom ≫ pullback.snd _ _ = pullback.snd f' (pullback.fst f g) ≫ pullback.snd f g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem pullbackRightPullbackFstIso_hom_snd :
    (pullbackRightPullbackFstIso f g f').hom ≫ pullback.snd _ _ =
      pullback.snd f' (pullback.fst f g) ≫ pullback.snd f g :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackRightPullbackFstIso_inv_fst : (pullbackRightPullbackFstIso f g f')
.inv ≫ pullback.fst f' (pullback.fst f g) = pullback.fst (f' ≫ f) g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
theorem pullbackRightPullbackFstIso_inv_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.fst f' (pullback.fst f g) =
      pullback.fst (f' ≫ f) g :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackRightPullbackFstIso_inv_snd_snd : (pullbackRightPullbackFstIso f g
 f').inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
theorem pullbackRightPullbackFstIso_inv_snd_snd :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.right

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackRightPullbackFstIso_inv_snd_fst : (pullbackRightPullbackFstIso f g
 f').inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
-/
theorem pullbackRightPullbackFstIso_inv_snd_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ f' := by
  rw [← pullback.condition]
  exact pullbackRightPullbackFstIso_inv_fst_assoc f g f' _

end
section
/- Let's consider the following diagram of pullbacks
```
(X ×[Z] Y) ×[Y] W --snd--> W
    |                      |
   fst                     g'
    v                      v
 (X ×[Z] Y) --- snd --->   Y
    |                      |
   fst                     g
    v                      v
    X -------- f --------> Z

```
In this section we show that `(X ×[Z] Y) ×[Y] W ≅ X ×[Z] W`.
-/


variable {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
variable [HasPullback f g] [HasPullback (pullback.snd f g) g']

/-
**CategoryTheory.Limits.hasPullbackVertPaste** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits`。
形式化陈述：hasPullbackVertPaste : HasPullback f (g' ≫ g)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasPullbackVertPaste : HasPullback f (g' ≫ g) :=
  HasLimit.mk {
    cone := (pullback.cone f g).pasteVert (pullback.cone (pullback.snd f g) g') rfl
    isLimit := pasteVertIsPullback rfl (pullback.isLimit f g)
      (pullback.isLimit (pullback.snd f g) g')
  }

/-- The canonical isomorphism `(X ×[Z] Y) ×[Y] W ≅ X ×[Z] W` -/
/-
**CategoryTheory.Limits.pullbackLeftPullbackSndIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：pullbackLeftPullbackSndIso : pullback (pullback.snd f g) g' ≅ pullback f (
g' ≫ g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(X ×[Z] Y) ×[Y] W ≅ X ×[Z] W`
-/
def pullbackLeftPullbackSndIso :
    pullback (pullback.snd f g) g' ≅ pullback f (g' ≫ g) :=
  IsLimit.conePointUniqueUpToIso
      (pasteVertIsPullback rfl (pullback.isLimit f g) (pullback.isLimit (pullback.snd f g) g'))
      (pullback.isLimit f (g' ≫ g))

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackLeftPullbackSndIso_hom_fst** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackLeftPullbackSndIso_hom_fst : (pullbackLeftPullbackSndIso f g g').h
om ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem pullbackLeftPullbackSndIso_hom_fst :
    (pullbackLeftPullbackSndIso f g g').hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackLeftPullbackSndIso_hom_snd** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackLeftPullbackSndIso_hom_snd : (pullbackLeftPullbackSndIso f g g').h
om ≫ pullback.snd _ _ = pullback.snd _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
-/
theorem pullbackLeftPullbackSndIso_hom_snd :
    (pullbackLeftPullbackSndIso f g g').hom ≫ pullback.snd _ _ = pullback.snd _ _ :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackLeftPullbackSndIso_inv_fst** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackLeftPullbackSndIso_inv_fst : (pullbackLeftPullbackSndIso f g g').i
nv ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
theorem pullbackLeftPullbackSndIso_inv_fst :
    (pullbackLeftPullbackSndIso f g g').inv ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackLeftPullbackSndIso_inv_snd_snd** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackLeftPullbackSndIso_inv_snd_snd : (pullbackLeftPullbackSndIso f g g
').inv ≫ pullback.snd _ _ = pullback.snd _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
-/
theorem pullbackLeftPullbackSndIso_inv_snd_snd :
    (pullbackLeftPullbackSndIso f g g').inv ≫ pullback.snd _ _ = pullback.snd _ _ :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.right

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackLeftPullbackSndIso_inv_fst_snd** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackLeftPullbackSndIso_inv_fst_snd : (pullbackLeftPullbackSndIso f g g
').inv ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackLeftPullbackSndIso_inv_snd_snd_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (
g : Y ⟶ Z) (g' : W ⟶ Y)   [inst_1 : CategoryTheory.Limit…
-/
theorem pullbackLeftPullbackSndIso_inv_fst_snd :
    (pullbackLeftPullbackSndIso f g g').inv ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ g' := by
  rw [pullback.condition]
  exact pullbackLeftPullbackSndIso_inv_snd_snd_assoc f g g' g'

end

section

/- Let's consider the following diagram of pushouts
```
X ---- g ----> Z ----- g' -----> W
|              |                 |
f             inr               inr
v              v                 v
Y - inl -> Y ⨿[X] Z --inl--> (Y ⨿[X] Z) ⨿[Z] W
```
In this section we show that `(Y ⨿[X] Z) ⨿[Z] W ≅ Y ⨿[X] W`.
-/
variable {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)
variable [HasPushout f g] [HasPushout (pushout.inr f g) g']

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasPushout f (g ≫ g') :=
  HasColimit.mk {
    cocone := (pushout.cocone f g).pasteHoriz (pushout.cocone (pushout.inr f g) g') rfl
    isColimit := pasteHorizIsPushout rfl (pushout.isColimit f g)
      (pushout.isColimit (pushout.inr f g) g')
  }

/-- The canonical isomorphism `(Y ⨿[X] Z) ⨿[Z] W ≅ Y ⨿[X] W` -/
/-
**CategoryTheory.Limits.pushoutLeftPushoutInrIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：pushoutLeftPushoutInrIso : pushout (pushout.inr f g) g' ≅ pushout f (g ≫ g
')
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPushoutComp`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)   
[inst_1 : CategoryTheory.Limit…

--- 原说明 ---
The canonical isomorphism `(Y ⨿[X] Z) ⨿[Z] W ≅ Y ⨿[X] W`
-/
noncomputable def pushoutLeftPushoutInrIso :
    pushout (pushout.inr f g) g' ≅ pushout f (g ≫ g') :=
  IsColimit.coconePointUniqueUpToIso
    (pasteHorizIsPushout rfl (pushout.isColimit f g) (pushout.isColimit (pushout.inr f g) g'))
    (pushout.isColimit f (g ≫ g'))

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_pushoutLeftPushoutInrIso_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：inl_pushoutLeftPushoutInrIso_inv : (pushout.inl f (g ≫ g')) ≫ (pushoutLeft
PushoutInrIso f g g').inv = (pushout.inl f g) ≫ (pushout.inl (pushout.inr f g) g
')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasPushoutComp`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)   
[inst_1 : CategoryTheory.Limit…
-/
theorem inl_pushoutLeftPushoutInrIso_inv :
    (pushout.inl f (g ≫ g')) ≫ (pushoutLeftPushoutInrIso f g g').inv =
      (pushout.inl f g) ≫ (pushout.inl (pushout.inr f g) g') :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ WalkingSpan.left

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_hom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：inr_pushoutLeftPushoutInrIso_hom : (pushout.inr (pushout.inr f g) g') ≫ (p
ushoutLeftPushoutInrIso f g g').hom = (pushout.inr f (g ≫ g'))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasPushoutComp`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)   
[inst_1 : CategoryTheory.Limit…
-/
theorem inr_pushoutLeftPushoutInrIso_hom :
    (pushout.inr (pushout.inr f g) g') ≫ (pushoutLeftPushoutInrIso f g g').hom =
      (pushout.inr f (g ≫ g')) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (pasteHorizIsPushout _ _ _) _ WalkingSpan.right

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：inr_pushoutLeftPushoutInrIso_inv : (pushout.inr f (g ≫ g')) ≫ (pushoutLeft
PushoutInrIso f g g').inv = (pushout.inr (pushout.inr f g) g')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasPushoutComp`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)   
[inst_1 : CategoryTheory.Limit…
-/
theorem inr_pushoutLeftPushoutInrIso_inv :
    (pushout.inr f (g ≫ g')) ≫ (pushoutLeftPushoutInrIso f g g').inv =
      (pushout.inr (pushout.inr f g) g') :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ WalkingSpan.right

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_inl_pushoutLeftPushoutInrIso_hom** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：inl_inl_pushoutLeftPushoutInrIso_hom : (pushout.inl f g) ≫ (pushout.inl (p
ushout.inr f g) g') ≫ (pushoutLeftPushoutInrIso f g g').hom = (pushout.inl f (g 
≫ g'))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPushoutComp`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)   
[inst_1 : CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem inl_inl_pushoutLeftPushoutInrIso_hom :
    (pushout.inl f g) ≫ (pushout.inl (pushout.inr f g) g') ≫
      (pushoutLeftPushoutInrIso f g g').hom = (pushout.inl f (g ≫ g')) := by
  rw [← Category.assoc]
  apply IsColimit.comp_coconePointUniqueUpToIso_hom (pasteHorizIsPushout _ _ _) _ WalkingSpan.left

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_inl_pushoutLeftPushoutInrIso_hom** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：inr_inl_pushoutLeftPushoutInrIso_hom : pushout.inr f g ≫ pushout.inl (push
out.inr f g) g' ≫ (pushoutLeftPushoutInrIso f g g').hom = g' ≫ pushout.inr f (g 
≫ g')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPushoutComp`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)   
[inst_1 : CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_inv`：inr_pushoutLeftP
ushoutInrIso_inv : (pushout.inr f (g ≫ g')) ≫ (pushoutLeftPushoutInrIso f g g').
inv = (pushout.inr (pushout.inr f g) g')
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
-/
theorem inr_inl_pushoutLeftPushoutInrIso_hom :
    pushout.inr f g ≫ pushout.inl (pushout.inr f g) g' ≫ (pushoutLeftPushoutInrIso f g g').hom =
      g' ≫ pushout.inr f (g ≫ g') := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, Category.assoc, inr_pushoutLeftPushoutInrIso_inv,
    pushout.condition]

end
section

/- Let's consider the diagram of pushouts
```
X ---- g ----> Z
|              |
f             inr
v              v
Y - inl -> Y ⨿[X] Z
|              |
f'            inr
v              v
W - inl -> W ⨿[Y] (Y ⨿[X] Z)
```

In this section we will construct the isomorphism `W ⨿[Y] (Y ⨿[X] Z) ≅ W ⨿[X] Z`.
-/

variable {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (f' : Y ⟶ W)
variable [HasPushout f g] [HasPushout f' (pushout.inl f g)]

/-
**CategoryTheory.Limits.hasPushoutVertPaste** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：hasPushoutVertPaste : HasPushout (f ≫ f') g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasPushoutVertPaste : HasPushout (f ≫ f') g :=
  HasColimit.mk {
    cocone := (pushout.cocone f g).pasteVert (pushout.cocone f' (pushout.inl f g)) rfl
    isColimit := pasteVertIsPushout rfl (pushout.isColimit f g)
      (pushout.isColimit f' (pushout.inl f g))
  }

/-- The canonical isomorphism `W ⨿[Y] (Y ⨿[X] Z) ≅ W ⨿[X] Z` -/
/-
**CategoryTheory.Limits.pushoutRightPushoutInlIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：pushoutRightPushoutInlIso : pushout f' (pushout.inl f g) ≅ pushout (f ≫ f'
) g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `W ⨿[Y] (Y ⨿[X] Z) ≅ W ⨿[X] Z`
-/
noncomputable def pushoutRightPushoutInlIso :
    pushout f' (pushout.inl f g) ≅ pushout (f ≫ f') g :=
  IsColimit.coconePointUniqueUpToIso
    (pasteVertIsPushout rfl (pushout.isColimit f g) (pushout.isColimit f' (pushout.inl f g)))
    (pushout.isColimit (f ≫ f') g)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_pushoutRightPushoutInlIso_inv** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：inl_pushoutRightPushoutInlIso_inv : pushout.inl _ _ ≫ (pushoutRightPushout
InlIso f g f').inv = pushout.inl _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem inl_pushoutRightPushoutInlIso_inv :
    pushout.inl _ _ ≫ (pushoutRightPushoutInlIso f g f').inv = pushout.inl _ _ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ WalkingSpan.left

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_inr_pushoutRightPushoutInlIso_hom** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：inr_inr_pushoutRightPushoutInlIso_hom : pushout.inr _ _ ≫ pushout.inr _ _ 
≫ (pushoutRightPushoutInlIso f g f').hom = pushout.inr _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem inr_inr_pushoutRightPushoutInlIso_hom :
    pushout.inr _ _ ≫ pushout.inr _ _ ≫ (pushoutRightPushoutInlIso f g f').hom =
      pushout.inr _ _ := by
  rw [← Category.assoc]
  apply IsColimit.comp_coconePointUniqueUpToIso_hom (pasteVertIsPushout rfl _ _) _ WalkingSpan.right

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_pushoutRightPushoutInlIso_inv** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：inr_pushoutRightPushoutInlIso_inv : pushout.inr _ _ ≫ (pushoutRightPushout
InlIso f g f').inv = pushout.inr _ _ ≫ pushout.inr _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem inr_pushoutRightPushoutInlIso_inv :
    pushout.inr _ _ ≫ (pushoutRightPushoutInlIso f g f').inv =
      pushout.inr _ _ ≫ pushout.inr _ _ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ WalkingSpan.right

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_pushoutRightPushoutInlIso_hom** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：inl_pushoutRightPushoutInlIso_hom : pushout.inl _ _ ≫ (pushoutRightPushout
InlIso f g f').hom = pushout.inl _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
theorem inl_pushoutRightPushoutInlIso_hom :
    pushout.inl _ _ ≫ (pushoutRightPushoutInlIso f g f').hom = pushout.inl _ _ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (pasteVertIsPushout rfl _ _) _ WalkingSpan.left

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_inl_pushoutRightPushoutInlIso_hom** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：inr_inl_pushoutRightPushoutInlIso_hom : pushout.inl _ _ ≫ pushout.inr _ _ 
≫ (pushoutRightPushoutInlIso f g f').hom = f' ≫ pushout.inl _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.inl_pushoutRightPushoutInlIso_hom`：inl_pushoutRigh
tPushoutInlIso_hom : pushout.inl _ _ ≫ (pushoutRightPushoutInlIso f g f').hom = 
pushout.inl _ _
-/
theorem inr_inl_pushoutRightPushoutInlIso_hom :
    pushout.inl _ _ ≫ pushout.inr _ _ ≫ (pushoutRightPushoutInlIso f g f').hom =
      f' ≫ pushout.inl _ _ := by
  rw [← Category.assoc, ← pushout.condition, Category.assoc, inl_pushoutRightPushoutInlIso_hom]

end

end CategoryTheory.Limits

