/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.WeakLimits.WeakEqualizers

/-!
# Weak pullbacks

These are weak limits for diagrams of shape `WalkingCospan`.

If a category has binary products and weak equalizers, then it has weak pullbacks
(see `hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakEqualizers`).

-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable {W X Y Z : C}

/-- Two morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` have a weak pullback if the diagram
`cospan f g` has a weak limit. -/
/-
**CategoryTheory.Limits.HasWeakPullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：HasWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` have a weak pullback if the diagram
`cospan f g` has a weak limit.
-/
abbrev HasWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasWeakLimit (cospan f g)

/-- `weakPullback f g` computes the weak pullback of a pair of morphisms
with the same target. -/
/-
**CategoryTheory.Limits.weakPullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：weakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`weakPullback f g` computes the weak pullback of a pair of morphisms
with the same target.
-/
abbrev weakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :=
  weakLimit (cospan f g)

/-- The cone associated to the weak pullback of `f` and `g` -/
/-
**CategoryTheory.Limits.weakPullback.cone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.weakPullback`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y Z : C} →       (f : X ⟶ Z) → (g : Y ⟶ Z) → [CategoryTheory.Limits.HasWeakPullb
ack f g] → CategoryTheory.Limits.PullbackCone f g
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone associated to the weak pullback of `f` and `g`
-/
abbrev weakPullback.cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakPullback f g] : PullbackCone f g :=
  weakLimit.cone (cospan f g)

/-- The first projection of the weak pullback of `f` and `g`. -/
/-
**CategoryTheory.Limits.weakPullback.fst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.weakPullback`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y Z : C} →       (f : X ⟶ Z) →         (g : Y ⟶ Z) → [inst_1 : CategoryTheory.Li
mits.HasWeakPullback f g] → CategoryTheory.Limits.weakPullback f g ⟶ X
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection of the weak pullback of `f` and `g`.
-/
abbrev weakPullback.fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    weakPullback f g ⟶ X :=
  weakLimit.π (cospan f g) WalkingCospan.left

/-- The second projection of the weak pullback of `f` and `g`. -/
/-
**CategoryTheory.Limits.weakPullback.snd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.weakPullback`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y Z : C} →       (f : X ⟶ Z) →         (g : Y ⟶ Z) → [inst_1 : CategoryTheory.Li
mits.HasWeakPullback f g] → CategoryTheory.Limits.weakPullback f g ⟶ Y
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection of the weak pullback of `f` and `g`.
-/
abbrev weakPullback.snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    weakPullback f g ⟶ Y :=
  weakLimit.π (cospan f g) WalkingCospan.right

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`weakPullback.lift : W ⟶ weakPullback f g`. -/
/-
**CategoryTheory.Limits.weakPullback.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.weakPullback`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
X Y Z : C} →       {f : X ⟶ Z} →         {g : Y ⟶ Z} →           [inst_1 : Categ
oryTheory.Limits.HasWeakPullback f g] →             (h : W ⟶ X) →               
(k : W ⟶ Y) →                 autoParam (CategoryTheory.CategoryStruct.comp h f 
= CategoryTheory.CategoryStruct.comp k g)                     CategoryTheory.Lim
its.weakPullback.lift._auto_1 →                   (W ⟶ CategoryTheory.Limits.wea
kPullback f g)
参数：h : W ⟶ X；k : W ⟶ Y；CategoryTheory.CategoryStruct.comp h f = CategoryTheory.C
ategoryStruct.comp k g；W ⟶ CategoryTheory.Limits.weakPullback f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induc
es a morphism
`weakPullback.lift : W ⟶ weakPullback f g`.
-/
abbrev weakPullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) : W ⟶ weakPullback f g :=
  weakLimit.lift _ (PullbackCone.mk h k w)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.weakPullback.exists_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.weakPullback`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W X Y Z : 
C} (f : X ⟶ Z) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasWeakPullback f g
] (h : W ⟶ X) (k : W ⟶ Y),   autoParam (CategoryTheory.CategoryStruct.comp h f =
 CategoryTheory.CategoryStruct.comp k g)       CategoryTheory.Limits.weakPullbac
k.exists_lift._auto_1 →     ∃ l,       CategoryTheory.CategoryStruct.comp l (Cat
egoryTheory.Limits.weakPullback.fst f g) = h ∧         CategoryTheory.CategorySt
ruct.comp l (CategoryTheory.Limits.weakPullback.snd f g) = k
参数：f : X ⟶ Z；g : Y ⟶ Z；h : W ⟶ X；k : W ⟶ Y；CategoryTheory.CategoryStruct.comp h 
f = CategoryTheory.CategoryStruct.comp k g；CategoryTheory.Limits.weakPullback.fs
t f g；CategoryTheory.Limits.weakPullback.snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.weakLimit.lift_π`：∀ {J : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} J] {C : Type u_3}   [inst_1 : CategoryTheory.Categor
y.{v_3, u_3} C] {F : Categor…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma weakPullback.exists_lift {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) :
    ∃ (l : W ⟶ weakPullback f g),
    l ≫ weakPullback.fst f g = h ∧ l ≫ weakPullback.snd f g = k :=
  ⟨weakPullback.lift h k, by simp⟩

/-- The cone associated to a weak pullback is a weak limit cone. -/
/-
**CategoryTheory.Limits.weakPullback.isWeakLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.weakPullback`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y Z : C} →       (f : X ⟶ Z) →         (g : Y ⟶ Z) →           [inst_1 : Categor
yTheory.Limits.HasWeakPullback f g] →             CategoryTheory.Limits.IsWeakLi
mit (CategoryTheory.Limits.weakPullback.cone f g)
参数：f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.weakPullback.cone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone associated to a weak pullback is a weak limit cone.
-/
abbrev weakPullback.isWeakLimit {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    IsWeakLimit (weakPullback.cone f g) :=
  weakLimit.isWeakLimit (cospan f g)

@[simp]
/-
**CategoryTheory.Limits.weakLimit.pullbackConeFst_cone_cospan** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.weakLimit`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y Z : C}
 (f : X ⟶ Z) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasWeakLimit (Categor
yTheory.Limits.cospan f g)],   CategoryTheory.Limits.PullbackCone.fst (CategoryT
heory.Limits.weakLimit.cone (CategoryTheory.Limits.cospan f g)) =     CategoryTh
eory.Limits.weakPullback.fst f g
参数：f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.cospan f g；CategoryTheory.Limits.we
akLimit.cone (CategoryTheory.Limits.cospan f g)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakLimit.pullbackConeFst_cone_cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakLimit (cospan f g)] :
    PullbackCone.fst (weakLimit.cone (cospan f g)) = weakPullback.fst f g := rfl

@[simp]
/-
**CategoryTheory.Limits.weakLimit.pullbackConeSnd_cone_cospan** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.weakLimit`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y Z : C}
 (f : X ⟶ Z) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasWeakLimit (Categor
yTheory.Limits.cospan f g)],   CategoryTheory.Limits.PullbackCone.snd (CategoryT
heory.Limits.weakLimit.cone (CategoryTheory.Limits.cospan f g)) =     CategoryTh
eory.Limits.weakPullback.snd f g
参数：f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.cospan f g；CategoryTheory.Limits.we
akLimit.cone (CategoryTheory.Limits.cospan f g)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weakLimit.pullbackConeSnd_cone_cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakLimit (cospan f g)] :
    PullbackCone.snd (weakLimit.cone (cospan f g)) = weakPullback.snd f g := rfl

@[reassoc]
/-
**CategoryTheory.Limits.weakPullback.lift_fst** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.weakPullback`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W X Y Z : 
C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasWeakPullback f g
] (h : W ⟶ X) (k : W ⟶ Y)   (w : CategoryTheory.CategoryStruct.comp h f = Catego
ryTheory.CategoryStruct.comp k g),   CategoryTheory.CategoryStruct.comp (Categor
yTheory.Limits.weakPullback.lift h k w)       (CategoryTheory.Limits.weakPullbac
k.fst f g) =     h
参数：h : W ⟶ X；k : W ⟶ Y；w : CategoryTheory.CategoryStruct.comp h f = CategoryTheo
ry.CategoryStruct.comp k g；CategoryTheory.Limits.weakPullback.lift h k w；Categor
yTheory.Limits.weakPullback.fst f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.weakLimit.lift_π`：∀ {J : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} J] {C : Type u_3}   [inst_1 : CategoryTheory.Categor
y.{v_3, u_3} C] {F : Categor…
-/
theorem weakPullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasWeakPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    weakPullback.lift h k w ≫ weakPullback.fst f g = h :=
  weakLimit.lift_π _ _

@[reassoc]
/-
**CategoryTheory.Limits.weakPullback.lift_snd** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.weakPullback`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W X Y Z : 
C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasWeakPullback f g
] (h : W ⟶ X) (k : W ⟶ Y)   (w : CategoryTheory.CategoryStruct.comp h f = Catego
ryTheory.CategoryStruct.comp k g),   CategoryTheory.CategoryStruct.comp (Categor
yTheory.Limits.weakPullback.lift h k w)       (CategoryTheory.Limits.weakPullbac
k.snd f g) =     k
参数：h : W ⟶ X；k : W ⟶ Y；w : CategoryTheory.CategoryStruct.comp h f = CategoryTheo
ry.CategoryStruct.comp k g；CategoryTheory.Limits.weakPullback.lift h k w；Categor
yTheory.Limits.weakPullback.snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.weakLimit.lift_π`：∀ {J : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} J] {C : Type u_3}   [inst_1 : CategoryTheory.Categor
y.{v_3, u_3} C] {F : Categor…
-/
theorem weakPullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasWeakPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    weakPullback.lift h k w ≫ weakPullback.snd f g = k :=
  weakLimit.lift_π _ _

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`l : W ⟶ weakPullback f g` such that `l ≫ weakPullback.fst = h` and `l ≫ weakPullback.snd = k`. -/
/-
**CategoryTheory.Limits.weakPullback.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.weakPullback`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
X Y Z : C} →       {f : X ⟶ Z} →         {g : Y ⟶ Z} →           [inst_1 : Categ
oryTheory.Limits.HasWeakPullback f g] →             (h : W ⟶ X) →               
(k : W ⟶ Y) →                 CategoryTheory.CategoryStruct.comp h f = CategoryT
heory.CategoryStruct.comp k g →                   { l //                     Cat
egoryTheory.CategoryStruct.comp l (CategoryTheory.Limits.weakPullback.fst f g) =
 h ∧                       CategoryTheory.CategoryStruct.comp l (CategoryTheory.
Limits.weakPullback.snd f g) = k }
参数：h : W ⟶ X；k : W ⟶ Y；CategoryTheory.Limits.weakPullback.fst f g；CategoryTheory
.Limits.weakPullback.snd f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induc
es a morphism
`l : W ⟶ weakPullback f g` such that `l ≫ weakPullback.fst = h` and `l ≫ weakPul
lback.snd = k`.
-/
def weakPullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
      { l : W ⟶ weakPullback f g //
      l ≫ weakPullback.fst f g = h ∧ l ≫ weakPullback.snd f g = k } :=
  ⟨weakPullback.lift h k w, weakPullback.lift_fst _ _ _, weakPullback.lift_snd _ _ _⟩

@[reassoc]
/-
**CategoryTheory.Limits.weakPullback.condition** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.weakPullback`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y Z : C}
 {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasWeakPullback f g],
   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.weakPullback.fst f 
g) f =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.weakPullbac
k.snd f g) g
参数：CategoryTheory.Limits.weakPullback.fst f g；CategoryTheory.Limits.weakPullback
.snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
-/
theorem weakPullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] :
    weakPullback.fst f g ≫ f = weakPullback.snd f g ≫ g :=
  PullbackCone.condition _

/-- Given such a diagram, then there is a natural morphism from the weak pullback of
`W ⟶ S` and `X ⟶ S` to the weak pullback of `Y ⟶ T` and `Z ⟶ T`.

```
W ⟶ Y
  ↘   ↘
  S ⟶ T
  ↗   ↗
X ⟶ Z
```
-/
/-
**CategoryTheory.Limits.weakPullback.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.weakPullback`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
X Y Z S T : C} →       (f₁ : W ⟶ S) →         (f₂ : X ⟶ S) →           [inst_1 :
 CategoryTheory.Limits.HasWeakPullback f₁ f₂] →             (g₁ : Y ⟶ T) →      
         (g₂ : Z ⟶ T) →                 [inst_2 : CategoryTheory.Limits.HasWeakP
ullback g₁ g₂] →                   (i₁ : W ⟶ Y) →                     (i₂ : X ⟶ 
Z) →                       (i₃ : S ⟶ T) →                         CategoryTheory
.CategoryStruct.comp f₁ i₃ = CategoryTheory.CategoryStruct.comp i₁ g₁ →         
                  CategoryTheory.CategoryStruct.comp f₂ i₃ = CategoryTheory.Cate
goryStruct.comp i₂ g₂ →                             (CategoryTheory.Limits.weakP
ullback f₁ f₂ ⟶ CategoryTheory.Limits.weakPullback g₁ g₂)
参数：f₁ : W ⟶ S；f₂ : X ⟶ S；g₁ : Y ⟶ T；g₂ : Z ⟶ T；i₁ : W ⟶ Y；i₂ : X ⟶ Z；i₃ : S ⟶ T；
CategoryTheory.Limits.weakPullback f₁ f₂ ⟶ CategoryTheory.Limits.weakPullback g₁
 g₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given such a diagram, then there is a natural morphism from the weak pullback of
`W ⟶ S` and `X ⟶ S` to the weak pullback of `Y ⟶ T` and `Z ⟶ T`.

```
W ⟶ Y
  ↘   ↘
  S ⟶ T
  ↗   ↗
X ⟶ Z
```
-/
abbrev weakPullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasWeakPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasWeakPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    weakPullback f₁ f₂ ⟶ weakPullback g₁ g₂ :=
  weakPullback.lift (weakPullback.fst f₁ f₂ ≫ i₁) (weakPullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, weakPullback.condition_assoc])

/-- A morphism from the weak pullback of `W ⟶ S` and `X ⟶ S` to the weak pullback of
`Y ⟶ T` and `Z ⟶ T` given `S ⟶ T`. -/
/-
**CategoryTheory.Limits.weakPullback.mapDesc** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.weakPullback`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y S T : C} →       (f : X ⟶ S) →         (g : Y ⟶ S) →           (i : S ⟶ T) →  
           [inst_1 : CategoryTheory.Limits.HasWeakPullback f g] →               
[inst_2 :                   CategoryTheory.Limits.HasWeakPullback (CategoryTheor
y.CategoryStruct.comp f i)                     (CategoryTheory.CategoryStruct.co
mp g i)] →                 CategoryTheory.Limits.weakPullback f g ⟶             
      CategoryTheory.Limits.weakPullback (CategoryTheory.CategoryStruct.comp f i
)                     (CategoryTheory.CategoryStruct.comp g i)
参数：f : X ⟶ S；g : Y ⟶ S；i : S ⟶ T；CategoryTheory.CategoryStruct.comp f i；Category
Theory.CategoryStruct.comp g i；CategoryTheory.CategoryStruct.comp f i；CategoryTh
eory.CategoryStruct.comp g i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism from the weak pullback of `W ⟶ S` and `X ⟶ S` to the weak pullback of
`Y ⟶ T` and `Z ⟶ T` given `S ⟶ T`.
-/
abbrev weakPullback.mapDesc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasWeakPullback f g]
    [HasWeakPullback (f ≫ i) (g ≫ i)] : weakPullback f g ⟶ weakPullback (f ≫ i) (g ≫ i) :=
  weakPullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm
  (Category.id_comp _).symm

namespace PullbackCone

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- This is a slightly more convenient method to verify that a pullback cone is a weak limit cone.
It only asks for a proof of facts that carry any mathematical content -/
/-
**CategoryTheory.Limits.PullbackCone.isWeakLimitAux** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.PullbackCone`。
形式化陈述：isWeakLimitAux (t : PullbackCone f g) (lift : forall s : PullbackCone f g,
 s.pt ⟶ t.pt) (fac_left : forall s : PullbackCone f g, lift s ≫ t.fst = s.fst) (
fac_right : forall s : PullbackCone f g, lift s ≫ t.snd = s.snd) : IsWeakLimit t
参数：t : PullbackCone f g；lift : forall s : PullbackCone f g, s.pt ⟶ t.pt；fac_left
 : forall s : PullbackCone f g, lift s ≫ t.fst = s.fst；fac_right : forall s : Pu
llbackCone f g, lift s ≫ t.snd = s.snd。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a slightly more convenient method to verify that a pullback cone is a we
ak limit cone.
It only asks for a proof of facts that carry any mathematical content
-/
def isWeakLimitAux (t : PullbackCone f g) (lift : ∀ s : PullbackCone f g, s.pt ⟶ t.pt)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ t.fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ t.snd = s.snd) : IsWeakLimit t :=
  { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w WalkingCospan.Hom.inl, ← t.w WalkingCospan.Hom.inl, ← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)}

/-- This is another convenient method to verify that a pullback cone is a weak limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
/-
**CategoryTheory.Limits.PullbackCone.isWeakLimitAux'** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.PullbackCone`。
形式化陈述：isWeakLimitAux' (t : PullbackCone f g) (create : forall s : PullbackCone f
 g, { l // l ≫ t.fst = s.fst ∧ l ≫ t.snd = s.snd}) : Limits.IsWeakLimit t
参数：t : PullbackCone f g；create : forall s : PullbackCone f g, { l // l ≫ t.fst =
 s.fst ∧ l ≫ t.snd = s.snd}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is another convenient method to verify that a pullback cone is a weak limit
 cone. It
only asks for a proof of facts that carry any mathematical content, and allows a
ccess to the
same `s` for all parts.
-/
def isWeakLimitAux' (t : PullbackCone f g)
    (create :
      ∀ s : PullbackCone f g, { l // l ≫ t.fst = s.fst ∧ l ≫ t.snd = s.snd}) :
    Limits.IsWeakLimit t :=
  PullbackCone.isWeakLimitAux t (fun s => (create s).1)
    (fun s => (create s).2.1) (fun s => (create s).2.2)

/-- This is a more convenient formulation to show that a `PullbackCone` constructed using
`PullbackCone.mk` is a weak limit cone.
-/
/-
**CategoryTheory.Limits.PullbackCone.IsWeakLimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.PullbackCone.IsWeakLimit`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y Z : C} →       {f : X ⟶ Z} →         {g : Y ⟶ Z} →           {W : C} →        
     {fst : W ⟶ X} →               {snd : W ⟶ Y} →                 (eq : Categor
yTheory.CategoryStruct.comp fst f = CategoryTheory.CategoryStruct.comp snd g) → 
                  (lift : (s : CategoryTheory.Limits.PullbackCone f g) → s.pt ⟶ 
W) →                     (∀ (s : CategoryTheory.Limits.PullbackCone f g),       
                  CategoryTheory.CategoryStruct.comp (lift s) fst = s.fst) →    
                   (∀ (s : CategoryTheory.Limits.PullbackCone f g),             
              CategoryTheory.CategoryStruct.comp (lift s) snd = s.snd) →        
                 CategoryTheory.Limits.IsWeakLimit (CategoryTheory.Limits.Pullba
ckCone.mk fst snd eq)
参数：eq : CategoryTheory.CategoryStruct.comp fst f = CategoryTheory.CategoryStruct
.comp snd g；lift : (s : CategoryTheory.Limits.PullbackCone f g) → s.pt ⟶ W；∀ (s 
: CategoryTheory.Limits.PullbackCone f g),                         CategoryTheor
y.CategoryStruct.comp (lift s) fst = s.fst；∀ (s : CategoryTheory.Limits.Pullback
Cone f g),                           CategoryTheory.CategoryStruct.comp (lift s)
 snd = s.snd；CategoryTheory.Limits.PullbackCone.mk fst snd eq。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a more convenient formulation to show that a `PullbackCone` constructed 
using
`PullbackCone.mk` is a weak limit cone.
-/
def IsWeakLimit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : ∀ s : PullbackCone f g, s.pt ⟶ W)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ snd = s.snd) :
    IsWeakLimit (PullbackCone.mk fst snd eq) :=
  isWeakLimitAux _ lift fac_left fac_right

/-- If `t` is a weak limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such
that `h ≫ f = k ≫ g`, then we get `l : W ⟶ t.pt`, which satisfies `l ≫ fst t = h`
and `l ≫ snd t = k`, see `IsWeakLimit.lift_fst` and `IsWeakLimit.lift_snd`. -/
/-
**CategoryTheory.Limits.PullbackCone.IsWeakLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.PullbackCone.IsWeakLimit`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y Z : C} →       {f : X ⟶ Z} →         {g : Y ⟶ Z} →           {t : CategoryTheo
ry.Limits.PullbackCone f g} →             CategoryTheory.Limits.IsWeakLimit t → 
              {W : C} →                 (h : W ⟶ X) →                   (k : W ⟶
 Y) →                     CategoryTheory.CategoryStruct.comp h f = CategoryTheor
y.CategoryStruct.comp k g → (W ⟶ t.pt)
参数：h : W ⟶ X；k : W ⟶ Y；W ⟶ t.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t` is a weak limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W
 ⟶ Y` are such
that `h ≫ f = k ≫ g`, then we get `l : W ⟶ t.pt`, which satisfies `l ≫ fst t = h
`
and `l ≫ snd t = k`, see `IsWeakLimit.lift_fst` and `IsWeakLimit.lift_snd`.
-/
def IsWeakLimit.lift {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ t.pt :=
  ht.lift <| PullbackCone.mk _ _ w

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PullbackCone.IsWeakLimit.lift_fst** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.PullbackCone.IsWeakLimit`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y Z : C}
 {f : X ⟶ Z} {g : Y ⟶ Z}   {t : CategoryTheory.Limits.PullbackCone f g} (ht : Ca
tegoryTheory.Limits.IsWeakLimit t) {W : C} (h : W ⟶ X)   (k : W ⟶ Y) (w : Catego
ryTheory.CategoryStruct.comp h f = CategoryTheory.CategoryStruct.comp k g),   Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.Limits.PullbackCone.IsWeakLimit
.lift ht h k w) t.fst = h
参数：ht : CategoryTheory.Limits.IsWeakLimit t；h : W ⟶ X；k : W ⟶ Y；w : CategoryTheo
ry.CategoryStruct.comp h f = CategoryTheory.CategoryStruct.comp k g；CategoryTheo
ry.Limits.PullbackCone.IsWeakLimit.lift ht h k w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsWeakLimit.fac`：∀ {J : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} J] {C : Type u_3}   [inst_1 : CategoryTheory.Category
.{v_3, u_3} C] {F : Categor…
-/
lemma IsWeakLimit.lift_fst {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : IsWeakLimit.lift ht h k w ≫ PullbackCone.fst t = h :=
  ht.fac _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PullbackCone.IsWeakLimit.lift_snd** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.PullbackCone.IsWeakLimit`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y Z : C}
 {f : X ⟶ Z} {g : Y ⟶ Z}   {t : CategoryTheory.Limits.PullbackCone f g} (ht : Ca
tegoryTheory.Limits.IsWeakLimit t) {W : C} (h : W ⟶ X)   (k : W ⟶ Y) (w : Catego
ryTheory.CategoryStruct.comp h f = CategoryTheory.CategoryStruct.comp k g),   Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.Limits.PullbackCone.IsWeakLimit
.lift ht h k w) t.snd = k
参数：ht : CategoryTheory.Limits.IsWeakLimit t；h : W ⟶ X；k : W ⟶ Y；w : CategoryTheo
ry.CategoryStruct.comp h f = CategoryTheory.CategoryStruct.comp k g；CategoryTheo
ry.Limits.PullbackCone.IsWeakLimit.lift ht h k w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsWeakLimit.fac`：∀ {J : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} J] {C : Type u_3}   [inst_1 : CategoryTheory.Category
.{v_3, u_3} C] {F : Categor…
-/
lemma IsWeakLimit.lift_snd {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : IsWeakLimit.lift ht h k w ≫ PullbackCone.snd t = k :=
  ht.fac _ _

/-- If `t` is a weak limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such
that `h ≫ f = k ≫ g`, then we have `l : W ⟶ t.pt` satisfying `l ≫ fst t = h` and `l ≫ snd t = k`.
-/
/-
**CategoryTheory.Limits.PullbackCone.IsWeakLimit.lift'** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.PullbackCone.IsWeakLimit`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y Z : C} →       {f : X ⟶ Z} →         {g : Y ⟶ Z} →           {t : CategoryTheo
ry.Limits.PullbackCone f g} →             CategoryTheory.Limits.IsWeakLimit t → 
              {W : C} →                 (h : W ⟶ X) →                   (k : W ⟶
 Y) →                     CategoryTheory.CategoryStruct.comp h f = CategoryTheor
y.CategoryStruct.comp k g →                       { l //                        
 CategoryTheory.CategoryStruct.comp l t.fst = h ∧                           Cate
goryTheory.CategoryStruct.comp l t.snd = k }
参数：h : W ⟶ X；k : W ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t` is a weak limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W
 ⟶ Y` are such
that `h ≫ f = k ≫ g`, then we have `l : W ⟶ t.pt` satisfying `l ≫ fst t = h` and
 `l ≫ snd t = k`.
-/
def IsWeakLimit.lift' {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) :
    { l : W ⟶ t.pt // l ≫ PullbackCone.fst t = h ∧ l ≫ PullbackCone.snd t = k } :=
  ⟨IsWeakLimit.lift ht h k w, by simp⟩

/-- The pullback cone reconstructed using `PullbackCone.mk` from a pullback cone that is a
weak limit, is also a weak limit. -/
/-
**CategoryTheory.Limits.PullbackCone.mkSelfIsWeakLimit** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.PullbackCone`。
形式化陈述：mkSelfIsWeakLimit {t : PullbackCone f g} (ht : IsWeakLimit t) : IsWeakLimi
t (PullbackCone.mk t.fst t.snd t.condition)
参数：ht : IsWeakLimit t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g

--- 原说明 ---
The pullback cone reconstructed using `PullbackCone.mk` from a pullback cone tha
t is a
weak limit, is also a weak limit.
-/
def mkSelfIsWeakLimit {t : PullbackCone f g} (ht : IsWeakLimit t) :
    IsWeakLimit (PullbackCone.mk t.fst t.snd t.condition) :=
  IsWeakLimit.ofIsoWeakLimit ht (PullbackCone.eta t)

end PullbackCone

/-- The weak pullback cone built from the weak pullback projections is a weak pullback. -/
/-
**CategoryTheory.Limits.weakPullbackIsWeakPullback** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：weakPullbackIsWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPul
lback f g] : IsWeakLimit (PullbackCone.mk (weakPullback.fst f g) (weakPullback.s
nd f g) weakPullback.condition)
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weak pullback cone built from the weak pullback projections is a weak pullba
ck.
-/
def weakPullbackIsWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    IsWeakLimit (PullbackCone.mk (weakPullback.fst f g) (weakPullback.snd f g)
    weakPullback.condition) :=
  PullbackCone.mkSelfIsWeakLimit <| weakPullback.isWeakLimit f g

variable (C)

/-- A category `HasWeakPullbacks` if it has all weak limits of shape `WalkingCospan`, i.e. if it
has a weak pullback for every pair of morphisms with the same codomain. -/
/-
**CategoryTheory.Limits.HasWeakPullbacks** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：HasWeakPullbacks
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasWeakPullbacks` if it has all weak limits of shape `WalkingCospan`
, i.e. if it
has a weak pullback for every pair of morphisms with the same codomain.
-/
abbrev HasWeakPullbacks :=
  HasWeakLimitsOfShape WalkingCospan C
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) HasWeakPullbacksOfHasPullbacks [HasPullbacks C] :
    HasWeakPullbacks C where

variable (f : X ⟶ Z) (g : Y ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/-- If the product `X ⨯ Y` and the weak equalizer of `π₁ ≫ f` and `π₂ ≫ g` exist, then the
weak pullback of `f` and `g` exists: it is given by composing the equalizer with the projections. -/
/-
**CategoryTheory.Limits.hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_par
allelPair** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair [HasLimi
t (pair X Y)] [HasWeakLimit (parallelPair (prod.fst ≫ f) (prod.snd ≫ g))] : HasW
eakLimit (cospan f g)
参数：pair X Y；parallelPair (prod.fst ≫ f) (prod.snd ≫ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasWeakLimit.mk`：∀ {J : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} J] {C : Type u_3}   [inst_1 : CategoryTheory.Category
.{v_3, u_3} C] {F : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.weakEqualizer.condition`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f g : X ⟶ Y)   [inst_1 : Catego
ryTheory.Limits.HasWeakEqualizer f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.weakLimit.lift_π_assoc`：∀ {J : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} J] {C : Type u_3}   [inst_1 : CategoryTheory.C
ategory.{v_3, u_3} C] {F : Categor…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If the product `X ⨯ Y` and the weak equalizer of `π₁ ≫ f` and `π₂ ≫ g` exist, th
en the
weak pullback of `f` and `g` exists: it is given by composing the equalizer with
 the projections.
-/
theorem hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair [HasLimit (pair X Y)]
    [HasWeakLimit (parallelPair (prod.fst ≫ f) (prod.snd ≫ g))] : HasWeakLimit (cospan f g) :=
  HasWeakLimit.mk
    { cone :=
        PullbackCone.mk (weakEqualizer.ι (prod.fst ≫ f) (prod.snd ≫ g) ≫ prod.fst)
          (weakEqualizer.ι _ _ ≫ prod.snd) <| by
          rw [Category.assoc, weakEqualizer.condition]
          simp
      isWeakLimit :=
        PullbackCone.IsWeakLimit.mk _ (fun s ↦ weakEqualizer.lift
          (prod.lift (s.π.app .left) (s.π.app .right)) <| by
            simp [limit.lift_π_assoc, PullbackCone.condition])
          (by simp) (by simp) }

attribute [local instance] hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair in
/-- If a category has all binary products and all weak equalizers, then it also has all
weak pullbacks. As usual, this is not an instance, since there may be a more direct way to
construct weak pullbacks. -/
/-
**CategoryTheory.Limits.hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakEqualize
rs** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakEqualizers [HasBinaryProdu
cts C] [HasWeakEqualizers C] : HasWeakPullbacks C where hasWeakLimit F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasWeakLimit_of_iso`：hasWeakLimit_of_iso {F G : J 
⥤ C} [HasWeakLimit F] (α : F ≅ G) : HasWeakLimit G
· 使用定理 `CategoryTheory.Limits.hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLim
it_parallelPair`：hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPa
ir [HasLimit (pair X Y)] [HasWeakLimit (parallelPair (prod.fst ≫ f) (prod.snd…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.HasWeakLimitsOfShape.hasWeakLimit`：∀ {J : Type u_1
} {inst : CategoryTheory.Category.{v_1, u_1} J} {C : Type u_3}   {inst_1 : Categ
oryTheory.Category.{v_3, u_3} C} [self : Cate…

--- 原说明 ---
If a category has all binary products and all weak equalizers, then it also has 
all
weak pullbacks. As usual, this is not an instance, since there may be a more dir
ect way to
construct weak pullbacks.
-/
theorem hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakEqualizers
    [HasBinaryProducts C] [HasWeakEqualizers C] : HasWeakPullbacks C where
  hasWeakLimit F := hasWeakLimit_of_iso (diagramIsoCospan F).symm

end CategoryTheory.Limits

