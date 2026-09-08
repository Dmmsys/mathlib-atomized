/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang, Emily Riehl, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
# HasPullback

`HasPullback f g` and `pullback f g` provides API for `HasLimit` and `limit` in the case of
pullbacks.

## Main definitions

* `HasPullback f g`: this is an abbreviation for `HasLimit (cospan f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pullback.

* `HasPullbacks`: expresses the fact that `C` admits all pullbacks, it is implemented as an
  abbreviation for `HasLimitsOfShape WalkingCospan C`

* `pullback f g`: Given a `HasPullback f g` instance, this function returns the choice of a limit
  object corresponding to the pullback of `f` and `g`. It fits into the following diagram:
  ```
    pullback f g ---pullback.fst f g---> X
        |                                |
        |                                |
  pullback.snd f g                       f
        |                                |
        v                                v
        Y --------------g--------------> Z
  ```

* `HasPushout f g`: this is an abbreviation for `HasColimit (span f g)`, and is a typeclass used to
  express the fact that a given pair of morphisms has a pushout.
* `HasPushouts`: expresses the fact that `C` admits all pushouts, it is implemented as an
  abbreviation for `HasColimitsOfShape WalkingSpan C`
* `pushout f g`: Given a `HasPushout f g` instance, this function returns the choice of a colimit
  object corresponding to the pushout of `f` and `g`. It fits into the following diagram:
  ```
      X --------------f--------------> Y
      |                                |
      g                          pushout.inl f g
      |                                |
      v                                v
      Z ---pushout.inr f g---> pushout f g
  ```

## Main results & API
* The following API is available for using the universal property of `pullback f g`:
  `lift`, `lift_fst`, `lift_snd`, `lift'`, `hom_ext` (for uniqueness).

* `pullback.map` is the induced map between pullbacks `W ×ₛ X ⟶ Y ×ₜ Z` given pointwise
  (compatible) maps `W ⟶ Y`, `X ⟶ Z` and `S ⟶ T`.

* `pullbackComparison`: Given a functor `G`, this is the natural morphism
  `G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g)`

* `pullbackSymmetry` provides the natural isomorphism `pullback f g ≅ pullback g f`

(The dual results for pushouts are also available)

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

/-- Two morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` have a pullback if the diagram `cospan f g` has a
limit. -/
/-
**CategoryTheory.Limits.HasPullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：HasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` have a pullback if the diagram `cospan
 f g` has a
limit.
-/
abbrev HasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasLimit (cospan f g)

/-- Two morphisms `f : X ⟶ Y` and `g : X ⟶ Z` have a pushout if the diagram `span f g` has a
colimit. -/
/-
**CategoryTheory.Limits.HasPushout** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：HasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
参数：f : X ⟶ Y；g : X ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two morphisms `f : X ⟶ Y` and `g : X ⟶ Z` have a pushout if the diagram `span f 
g` has a
colimit.
-/
abbrev HasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :=
  HasColimit (span f g)

/-- `pullback f g` computes the pullback of a pair of morphisms with the same target. -/
/-
**CategoryTheory.Limits.pullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pullback f g` computes the pullback of a pair of morphisms with the same target
.
-/
abbrev pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :=
  limit (cospan f g)

/-- The cone associated to the pullback of `f` and `g` -/
/-
**CategoryTheory.Limits.pullback.cone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.pullback`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       (f : X ⟶ Z) → (g : Y ⟶ Z) → [CategoryTheory.Limits.HasPullback f g] →
 CategoryTheory.Limits.PullbackCone f g
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone associated to the pullback of `f` and `g`
-/
abbrev pullback.cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : PullbackCone f g :=
  limit.cone (cospan f g)

/-- `pushout f g` computes the pushout of a pair of morphisms with the same source. -/
/-
**CategoryTheory.Limits.pushout** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
参数：f : X ⟶ Y；g : X ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pushout f g` computes the pushout of a pair of morphisms with the same source.
-/
abbrev pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :=
  colimit (span f g)

/-- The cocone associated to the pushout of `f` and `g` -/
/-
**CategoryTheory.Limits.pushout.cocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.pushout`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       (f : X ⟶ Y) → (g : X ⟶ Z) → [CategoryTheory.Limits.HasPushout f g] → 
CategoryTheory.Limits.PushoutCocone f g
参数：f : X ⟶ Y；g : X ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone associated to the pushout of `f` and `g`
-/
abbrev pushout.cocone {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : PushoutCocone f g :=
  colimit.cocone (span f g)

/-- The first projection of the pullback of `f` and `g`. -/
/-
**CategoryTheory.Limits.pullback.fst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.pullback`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       (f : X ⟶ Z) →         (g : Y ⟶ Z) → [inst_1 : CategoryTheory.Limits.H
asPullback f g] → CategoryTheory.Limits.pullback f g ⟶ X
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection of the pullback of `f` and `g`.
-/
abbrev pullback.fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : pullback f g ⟶ X :=
  limit.π (cospan f g) WalkingCospan.left

/-- The second projection of the pullback of `f` and `g`. -/
/-
**CategoryTheory.Limits.pullback.snd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.pullback`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       (f : X ⟶ Z) →         (g : Y ⟶ Z) → [inst_1 : CategoryTheory.Limits.H
asPullback f g] → CategoryTheory.Limits.pullback f g ⟶ Y
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection of the pullback of `f` and `g`.
-/
abbrev pullback.snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : pullback f g ⟶ Y :=
  limit.π (cospan f g) WalkingCospan.right

/-- The first inclusion into the pushout of `f` and `g`. -/
/-
**CategoryTheory.Limits.pushout.inl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.pushout`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       (f : X ⟶ Y) →         (g : X ⟶ Z) → [inst_1 : CategoryTheory.Limits.H
asPushout f g] → Y ⟶ CategoryTheory.Limits.pushout f g
参数：f : X ⟶ Y；g : X ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first inclusion into the pushout of `f` and `g`.
-/
abbrev pushout.inl {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Y ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.left

/-- The second inclusion into the pushout of `f` and `g`. -/
/-
**CategoryTheory.Limits.pushout.inr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.pushout`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       (f : X ⟶ Y) →         (g : X ⟶ Z) → [inst_1 : CategoryTheory.Limits.H
asPushout f g] → Z ⟶ CategoryTheory.Limits.pushout f g
参数：f : X ⟶ Y；g : X ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second inclusion into the pushout of `f` and `g`.
-/
abbrev pushout.inr {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Z ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.right

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`pullback.lift : W ⟶ pullback f g`. -/
/-
**CategoryTheory.Limits.pullback.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.pullback`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y Z 
: C} →       {f : X ⟶ Z} →         {g : Y ⟶ Z} →           [inst_1 : CategoryThe
ory.Limits.HasPullback f g] →             (h : W ⟶ X) →               (k : W ⟶ Y
) →                 autoParam (CategoryTheory.CategoryStruct.comp h f = Category
Theory.CategoryStruct.comp k g)                     CategoryTheory.Limits.pullba
ck.lift._auto_1 →                   (W ⟶ CategoryTheory.Limits.pullback f g)
参数：h : W ⟶ X；k : W ⟶ Y；CategoryTheory.CategoryStruct.comp h f = CategoryTheory.C
ategoryStruct.comp k g；W ⟶ CategoryTheory.Limits.pullback f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induc
es a morphism
`pullback.lift : W ⟶ pullback f g`.
-/
abbrev pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) : W ⟶ pullback f g :=
  limit.lift _ (PullbackCone.mk h k w)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pullback.exists_lift** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f 
: X ⟶ Z) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasPullback f g] (h : W ⟶
 X) (k : W ⟶ Y),   autoParam (CategoryTheory.CategoryStruct.comp h f = CategoryT
heory.CategoryStruct.comp k g)       CategoryTheory.Limits.pullback.exists_lift.
_auto_1 →     ∃ l,       CategoryTheory.CategoryStruct.comp l (CategoryTheory.Li
mits.pullback.fst f g) = h ∧         CategoryTheory.CategoryStruct.comp l (Categ
oryTheory.Limits.pullback.snd f g) = k
参数：f : X ⟶ Z；g : Y ⟶ Z；h : W ⟶ X；k : W ⟶ Y；CategoryTheory.CategoryStruct.comp h 
f = CategoryTheory.CategoryStruct.comp k g；CategoryTheory.Limits.pullback.fst f 
g；CategoryTheory.Limits.pullback.snd f g。
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
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma pullback.exists_lift {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) :
    ∃ (l : W ⟶ pullback f g), l ≫ pullback.fst f g = h ∧ l ≫ pullback.snd f g = k :=
  ⟨pullback.lift h k, by simp⟩

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
`pushout.desc : pushout f g ⟶ W`. -/
/-
**CategoryTheory.Limits.pushout.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.pushout`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y Z 
: C} →       {f : X ⟶ Y} →         {g : X ⟶ Z} →           [inst_1 : CategoryThe
ory.Limits.HasPushout f g] →             (h : Y ⟶ W) →               (k : Z ⟶ W)
 →                 autoParam (CategoryTheory.CategoryStruct.comp f h = CategoryT
heory.CategoryStruct.comp g k)                     CategoryTheory.Limits.pushout
.desc._auto_1 →                   (CategoryTheory.Limits.pushout f g ⟶ W)
参数：h : Y ⟶ W；k : Z ⟶ W；CategoryTheory.CategoryStruct.comp f h = CategoryTheory.C
ategoryStruct.comp g k；CategoryTheory.Limits.pushout f g ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induc
es a morphism
`pushout.desc : pushout f g ⟶ W`.
-/
abbrev pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k := by cat_disch) : pushout f g ⟶ W :=
  colimit.desc _ (PushoutCocone.mk h k w)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pushout.exists_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f 
: X ⟶ Y) (g : X ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasPushout f g] (h : Y ⟶ 
W) (k : Z ⟶ W),   autoParam (CategoryTheory.CategoryStruct.comp f h = CategoryTh
eory.CategoryStruct.comp g k)       CategoryTheory.Limits.pushout.exists_desc._a
uto_1 →     ∃ l,       CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits
.pushout.inl f g) l = h ∧         CategoryTheory.CategoryStruct.comp (CategoryTh
eory.Limits.pushout.inr f g) l = k
参数：f : X ⟶ Y；g : X ⟶ Z；h : Y ⟶ W；k : Z ⟶ W；CategoryTheory.CategoryStruct.comp f 
h = CategoryTheory.CategoryStruct.comp g k；CategoryTheory.Limits.pushout.inl f g
；CategoryTheory.Limits.pushout.inr f g。
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
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma pushout.exists_desc {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k := by cat_disch) :
    ∃ (l : pushout f g ⟶ W), pushout.inl f g ≫ l = h ∧ pushout.inr f g ≫ l = k :=
  ⟨pushout.desc h k, by simp⟩

/-- The cone associated to a pullback is a limit cone. -/
/-
**CategoryTheory.Limits.pullback.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.pullback`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       (f : X ⟶ Z) →         (g : Y ⟶ Z) →           [inst_1 : CategoryTheor
y.Limits.HasPullback f g] →             CategoryTheory.Limits.IsLimit (CategoryT
heory.Limits.pullback.cone f g)
参数：f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.pullback.cone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone associated to a pullback is a limit cone.
-/
abbrev pullback.isLimit {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (pullback.cone f g) :=
  limit.isLimit (cospan f g)

/-- The cocone associated to a pushout is a colimit cone. -/
/-
**CategoryTheory.Limits.pushout.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.pushout`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       (f : X ⟶ Y) →         (g : X ⟶ Z) →           [inst_1 : CategoryTheor
y.Limits.HasPushout f g] →             CategoryTheory.Limits.IsColimit (Category
Theory.Limits.pushout.cocone f g)
参数：f : X ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.pushout.cocone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone associated to a pushout is a colimit cone.
-/
abbrev pushout.isColimit {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (pushout.cocone f g) :=
  colimit.isColimit (span f g)

@[simp]
/-
**CategoryTheory.Limits.PullbackCone.fst_limit_cone** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.PullbackCone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : 
X ⟶ Z) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasLimit (CategoryTheory.Li
mits.cospan f g)],   CategoryTheory.Limits.PullbackCone.fst (CategoryTheory.Limi
ts.limit.cone (CategoryTheory.Limits.cospan f g)) =     CategoryTheory.Limits.pu
llback.fst f g
参数：f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.cospan f g；CategoryTheory.Limits.li
mit.cone (CategoryTheory.Limits.cospan f g)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PullbackCone.fst_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)] :
    PullbackCone.fst (limit.cone (cospan f g)) = pullback.fst f g := rfl

@[simp]
/-
**CategoryTheory.Limits.PullbackCone.snd_limit_cone** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.PullbackCone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : 
X ⟶ Z) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasLimit (CategoryTheory.Li
mits.cospan f g)],   CategoryTheory.Limits.PullbackCone.snd (CategoryTheory.Limi
ts.limit.cone (CategoryTheory.Limits.cospan f g)) =     CategoryTheory.Limits.pu
llback.snd f g
参数：f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.cospan f g；CategoryTheory.Limits.li
mit.cone (CategoryTheory.Limits.cospan f g)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PullbackCone.snd_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (cospan f g)] :
    PullbackCone.snd (limit.cone (cospan f g)) = pullback.snd f g := rfl
/-
**CategoryTheory.Limits.PushoutCocone.inl_colimit_cocone** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : 
Z ⟶ X) (g : Z ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasColimit (CategoryTheory.
Limits.span f g)],   CategoryTheory.Limits.PushoutCocone.inl (CategoryTheory.Lim
its.colimit.cocone (CategoryTheory.Limits.span f g)) =     CategoryTheory.Limits
.pushout.inl f g
参数：f : Z ⟶ X；g : Z ⟶ Y；CategoryTheory.Limits.span f g；CategoryTheory.Limits.coli
mit.cocone (CategoryTheory.Limits.span f g)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PushoutCocone.inl_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inl (colimit.cocone (span f g)) = pushout.inl _ _ := rfl
/-
**CategoryTheory.Limits.PushoutCocone.inr_colimit_cocone** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.PushoutCocone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : 
Z ⟶ X) (g : Z ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasColimit (CategoryTheory.
Limits.span f g)],   CategoryTheory.Limits.PushoutCocone.inr (CategoryTheory.Lim
its.colimit.cocone (CategoryTheory.Limits.span f g)) =     CategoryTheory.Limits
.pushout.inr f g
参数：f : Z ⟶ X；g : Z ⟶ Y；CategoryTheory.Limits.span f g；CategoryTheory.Limits.coli
mit.cocone (CategoryTheory.Limits.span f g)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PushoutCocone.inr_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inr (colimit.cocone (span f g)) = pushout.inr _ _ := rfl

@[reassoc]
/-
**CategoryTheory.Limits.pullback.lift_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPullback f g] (h : W ⟶
 X) (k : W ⟶ Y)   (w : CategoryTheory.CategoryStruct.comp h f = CategoryTheory.C
ategoryStruct.comp k g),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Li
mits.pullback.lift h k w)       (CategoryTheory.Limits.pullback.fst f g) =     h
参数：h : W ⟶ X；k : W ⟶ Y；w : CategoryTheory.CategoryStruct.comp h f = CategoryTheo
ry.CategoryStruct.comp k g；CategoryTheory.Limits.pullback.lift h k w；CategoryThe
ory.Limits.pullback.fst f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
theorem pullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.fst f g = h :=
  limit.lift_π _ _

@[reassoc]
/-
**CategoryTheory.Limits.pullback.lift_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPullback f g] (h : W ⟶
 X) (k : W ⟶ Y)   (w : CategoryTheory.CategoryStruct.comp h f = CategoryTheory.C
ategoryStruct.comp k g),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Li
mits.pullback.lift h k w)       (CategoryTheory.Limits.pullback.snd f g) =     k
参数：h : W ⟶ X；k : W ⟶ Y；w : CategoryTheory.CategoryStruct.comp h f = CategoryTheo
ry.CategoryStruct.comp k g；CategoryTheory.Limits.pullback.lift h k w；CategoryThe
ory.Limits.pullback.snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
-/
theorem pullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.snd f g = k :=
  limit.lift_π _ _

@[reassoc]
/-
**CategoryTheory.Limits.pushout.inl_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: X ⟶ Y} {g : X ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPushout f g] (h : Y ⟶ 
W) (k : Z ⟶ W)   (w : CategoryTheory.CategoryStruct.comp f h = CategoryTheory.Ca
tegoryStruct.comp g k),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Lim
its.pushout.inl f g)       (CategoryTheory.Limits.pushout.desc h k w) =     h
参数：h : Y ⟶ W；k : Z ⟶ W；w : CategoryTheory.CategoryStruct.comp f h = CategoryTheo
ry.CategoryStruct.comp g k；CategoryTheory.Limits.pushout.inl f g；CategoryTheory.
Limits.pushout.desc h k w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
-/
theorem pushout.inl_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inl _ _ ≫ pushout.desc h k w = h :=
  colimit.ι_desc _ _

@[reassoc]
/-
**CategoryTheory.Limits.pushout.inr_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} {f 
: X ⟶ Y} {g : X ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPushout f g] (h : Y ⟶ 
W) (k : Z ⟶ W)   (w : CategoryTheory.CategoryStruct.comp f h = CategoryTheory.Ca
tegoryStruct.comp g k),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Lim
its.pushout.inr f g)       (CategoryTheory.Limits.pushout.desc h k w) =     k
参数：h : Y ⟶ W；k : Z ⟶ W；w : CategoryTheory.CategoryStruct.comp f h = CategoryTheo
ry.CategoryStruct.comp g k；CategoryTheory.Limits.pushout.inr f g；CategoryTheory.
Limits.pushout.desc h k w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
-/
theorem pushout.inr_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inr _ _ ≫ pushout.desc h k w = k :=
  colimit.ι_desc _ _

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`l : W ⟶ pullback f g` such that `l ≫ pullback.fst = h` and `l ≫ pullback.snd = k`. -/
/-
**CategoryTheory.Limits.pullback.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.pullback`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y Z 
: C} →       {f : X ⟶ Z} →         {g : Y ⟶ Z} →           [inst_1 : CategoryThe
ory.Limits.HasPullback f g] →             (h : W ⟶ X) →               (k : W ⟶ Y
) →                 CategoryTheory.CategoryStruct.comp h f = CategoryTheory.Cate
goryStruct.comp k g →                   { l //                     CategoryTheor
y.CategoryStruct.comp l (CategoryTheory.Limits.pullback.fst f g) = h ∧          
             CategoryTheory.CategoryStruct.comp l (CategoryTheory.Limits.pullbac
k.snd f g) = k }
参数：h : W ⟶ X；k : W ⟶ Y；CategoryTheory.Limits.pullback.fst f g；CategoryTheory.Lim
its.pullback.snd f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induc
es a morphism
`l : W ⟶ pullback f g` such that `l ≫ pullback.fst = h` and `l ≫ pullback.snd = 
k`.
-/
def pullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) :
    { l : W ⟶ pullback f g // l ≫ pullback.fst f g = h ∧ l ≫ pullback.snd f g = k } :=
  ⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
`l : pushout f g ⟶ W` such that `pushout.inl _ _ ≫ l = h` and `pushout.inr _ _ ≫ l = k`. -/
/-
**CategoryTheory.Limits.pushout.desc'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.pushout`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y Z 
: C} →       {f : X ⟶ Y} →         {g : X ⟶ Z} →           [inst_1 : CategoryThe
ory.Limits.HasPushout f g] →             (h : Y ⟶ W) →               (k : Z ⟶ W)
 →                 CategoryTheory.CategoryStruct.comp f h = CategoryTheory.Categ
oryStruct.comp g k →                   { l //                     CategoryTheory
.CategoryStruct.comp (CategoryTheory.Limits.pushout.inl f g) l = h ∧            
           CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pushout.inr
 f g) l = k }
参数：h : Y ⟶ W；k : Z ⟶ W；CategoryTheory.Limits.pushout.inl f g；CategoryTheory.Limi
ts.pushout.inr f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induc
es a morphism
`l : pushout f g ⟶ W` such that `pushout.inl _ _ ≫ l = h` and `pushout.inr _ _ ≫
 l = k`.
-/
def pushout.desc' {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) :
    { l : pushout f g ⟶ W // pushout.inl _ _ ≫ l = h ∧ pushout.inr _ _ ≫ l = k } :=
  ⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩

@[deprecated (since := "2026-06-25")] alias pullback.desc' := pushout.desc'

@[reassoc]
/-
**CategoryTheory.Limits.pullback.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPullback f g],   Categor
yTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.fst f g) f =     Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.snd f g) g
参数：CategoryTheory.Limits.pullback.fst f g；CategoryTheory.Limits.pullback.snd f g
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
-/
theorem pullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    pullback.fst f g ≫ f = pullback.snd f g ≫ g :=
  PullbackCone.condition _

@[reassoc]
/-
**CategoryTheory.Limits.pushout.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPushout f g],   Category
Theory.CategoryStruct.comp f (CategoryTheory.Limits.pushout.inl f g) =     Categ
oryTheory.CategoryStruct.comp g (CategoryTheory.Limits.pushout.inr f g)
参数：CategoryTheory.Limits.pushout.inl f g；CategoryTheory.Limits.pushout.inr f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t
-/
theorem pushout.condition {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    f ≫ (pushout.inl f g) = g ≫ pushout.inr _ _ :=
  PushoutCocone.condition _

/-- Two morphisms into a pullback are equal if their compositions with the pullback morphisms are
equal -/
@[ext 1100]
/-
**CategoryTheory.Limits.pullback.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPullback f g] {W : C} {k
 l : W ⟶ CategoryTheory.Limits.pullback f g},   CategoryTheory.CategoryStruct.co
mp k (CategoryTheory.Limits.pullback.fst f g) =       CategoryTheory.CategoryStr
uct.comp l (CategoryTheory.Limits.pullback.fst f g) →     CategoryTheory.Categor
yStruct.comp k (CategoryTheory.Limits.pullback.snd f g) =         CategoryTheory
.CategoryStruct.comp l (CategoryTheory.Limits.pullback.snd f g) →       k = l
参数：CategoryTheory.Limits.pullback.fst f g；CategoryTheory.Limits.pullback.fst f g
；CategoryTheory.Limits.pullback.snd f g；CategoryTheory.Limits.pullback.snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.equalizer_ext`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (t : Ca
tegoryTheory.Limits.PullbackCone f g) …

--- 原说明 ---
Two morphisms into a pullback are equal if their compositions with the pullback 
morphisms are
equal
-/
theorem pullback.hom_ext {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {W : C}
    {k l : W ⟶ pullback f g} (h₀ : k ≫ pullback.fst f g = l ≫ pullback.fst f g)
    (h₁ : k ≫ pullback.snd f g = l ≫ pullback.snd f g) : k = l :=
  limit.hom_ext <| PullbackCone.equalizer_ext _ h₀ h₁

/-- The pullback cone built from the pullback projections is a pullback. -/
/-
**CategoryTheory.Limits.pullbackIsPullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：pullbackIsPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
 IsLimit (PullbackCone.mk (pullback.fst f g) (pullback.snd f g) pullback.conditi
on)
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback cone built from the pullback projections is a pullback.
-/
def pullbackIsPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (PullbackCone.mk (pullback.fst f g) (pullback.snd f g) pullback.condition) :=
  PullbackCone.mkSelfIsLimit <| pullback.isLimit f g

/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
equal -/
@[ext 1100]
/-
**CategoryTheory.Limits.pushout.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPushout f g] {W : C} {k 
l : CategoryTheory.Limits.pushout f g ⟶ W},   CategoryTheory.CategoryStruct.comp
 (CategoryTheory.Limits.pushout.inl f g) k =       CategoryTheory.CategoryStruct
.comp (CategoryTheory.Limits.pushout.inl f g) l →     CategoryTheory.CategoryStr
uct.comp (CategoryTheory.Limits.pushout.inr f g) k =         CategoryTheory.Cate
goryStruct.comp (CategoryTheory.Limits.pushout.inr f g) l →       k = l
参数：CategoryTheory.Limits.pushout.inl f g；CategoryTheory.Limits.pushout.inl f g；C
ategoryTheory.Limits.pushout.inr f g；CategoryTheory.Limits.pushout.inr f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.coequalizer_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   (t :
 CategoryTheory.Limits.PushoutCocone f g)…

--- 原说明 ---
Two morphisms out of a pushout are equal if their compositions with the pushout 
morphisms are
equal
-/
theorem pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] {W : C}
    {k l : pushout f g ⟶ W} (h₀ : pushout.inl _ _ ≫ k = pushout.inl _ _ ≫ l)
    (h₁ : pushout.inr _ _ ≫ k = pushout.inr _ _ ≫ l) : k = l :=
  colimit.hom_ext <| PushoutCocone.coequalizer_ext _ h₀ h₁

set_option backward.isDefEq.respectTransparency false in
/-- The pushout cocone built from the pushout coprojections is a pushout. -/
/-
**CategoryTheory.Limits.pushoutIsPushout** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：pushoutIsPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : Is
Colimit (PushoutCocone.mk (pushout.inl f g) (pushout.inr _ _) pushout.condition)
参数：f : X ⟶ Y；g : X ⟶ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t

--- 原说明 ---
The pushout cocone built from the pushout coprojections is a pushout.
-/
def pushoutIsPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (PushoutCocone.mk (pushout.inl f g) (pushout.inr _ _) pushout.condition) :=
  PushoutCocone.IsColimit.mk _ (fun s => pushout.desc s.inl s.inr s.condition) (by simp) (by simp)
    (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.pullback.lift_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : 
X ⟶ Z) (g : Y ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasPullback f g],   Categor
yTheory.Limits.pullback.lift (CategoryTheory.Limits.pullback.fst f g) (CategoryT
heory.Limits.pullback.snd f g)       ⋯ =     CategoryTheory.CategoryStruct.id (C
ategoryTheory.Limits.pullback f g)
参数：f : X ⟶ Z；g : Y ⟶ Z；CategoryTheory.Limits.pullback.fst f g；CategoryTheory.Lim
its.pullback.snd f g；CategoryTheory.Limits.pullback f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullback.lift_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    lift (fst f g) (snd f g) condition = 𝟙 (pullback f g) := by
  apply hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.pushout.desc_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : 
X ⟶ Y) (g : X ⟶ Z)   [inst_1 : CategoryTheory.Limits.HasPushout f g],   Category
Theory.Limits.pushout.desc (CategoryTheory.Limits.pushout.inl f g) (CategoryTheo
ry.Limits.pushout.inr f g) ⋯ =     CategoryTheory.CategoryStruct.id (CategoryThe
ory.Limits.pushout f g)
参数：f : X ⟶ Y；g : X ⟶ Z；CategoryTheory.Limits.pushout.inl f g；CategoryTheory.Limi
ts.pushout.inr f g；CategoryTheory.Limits.pushout f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pushout.desc_inl_inr {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    desc (inl f g) (inr f g) condition = 𝟙 (pushout f g) := by
  apply hom_ext <;> simp

/-- Given such a diagram, then there is a natural morphism `W ×ₛ X ⟶ Y ×ₜ Z`.

```
W ⟶ Y
  ↘   ↘
  S ⟶ T
  ↗   ↗
X ⟶ Z
```
-/
/-
**CategoryTheory.Limits.pullback.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.pullback`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y Z 
S T : C} →       (f₁ : W ⟶ S) →         (f₂ : X ⟶ S) →           [inst_1 : Categ
oryTheory.Limits.HasPullback f₁ f₂] →             (g₁ : Y ⟶ T) →               (
g₂ : Z ⟶ T) →                 [inst_2 : CategoryTheory.Limits.HasPullback g₁ g₂]
 →                   (i₁ : W ⟶ Y) →                     (i₂ : X ⟶ Z) →          
             (i₃ : S ⟶ T) →                         CategoryTheory.CategoryStruc
t.comp f₁ i₃ = CategoryTheory.CategoryStruct.comp i₁ g₁ →                       
    CategoryTheory.CategoryStruct.comp f₂ i₃ = CategoryTheory.CategoryStruct.com
p i₂ g₂ →                             (CategoryTheory.Limits.pullback f₁ f₂ ⟶ Ca
tegoryTheory.Limits.pullback g₁ g₂)
参数：f₁ : W ⟶ S；f₂ : X ⟶ S；g₁ : Y ⟶ T；g₂ : Z ⟶ T；i₁ : W ⟶ Y；i₂ : X ⟶ Z；i₃ : S ⟶ T；
CategoryTheory.Limits.pullback f₁ f₂ ⟶ CategoryTheory.Limits.pullback g₁ g₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given such a diagram, then there is a natural morphism `W ×ₛ X ⟶ Y ×ₜ Z`.

```
W ⟶ Y
  ↘   ↘
  S ⟶ T
  ↗   ↗
X ⟶ Z
```
-/
abbrev pullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : pullback f₁ f₂ ⟶ pullback g₁ g₂ :=
  pullback.lift (pullback.fst f₁ f₂ ≫ i₁) (pullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, pullback.condition_assoc])

/-- The canonical map `X ×ₛ Y ⟶ X ×ₜ Y` given `S ⟶ T`. -/
/-
**CategoryTheory.Limits.pullback.mapDesc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.pullback`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y S T 
: C} →       (f : X ⟶ S) →         (g : Y ⟶ S) →           (i : S ⟶ T) →        
     [inst_1 : CategoryTheory.Limits.HasPullback f g] →               [inst_2 : 
                  CategoryTheory.Limits.HasPullback (CategoryTheory.CategoryStru
ct.comp f i)                     (CategoryTheory.CategoryStruct.comp g i)] →    
             CategoryTheory.Limits.pullback f g ⟶                   CategoryTheo
ry.Limits.pullback (CategoryTheory.CategoryStruct.comp f i)                     
(CategoryTheory.CategoryStruct.comp g i)
参数：f : X ⟶ S；g : Y ⟶ S；i : S ⟶ T；CategoryTheory.CategoryStruct.comp f i；Category
Theory.CategoryStruct.comp g i；CategoryTheory.CategoryStruct.comp f i；CategoryTh
eory.CategoryStruct.comp g i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `X ×ₛ Y ⟶ X ×ₜ Y` given `S ⟶ T`.
-/
abbrev pullback.mapDesc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasPullback f g]
    [HasPullback (f ≫ i) (g ≫ i)] : pullback f g ⟶ pullback (f ≫ i) (g ≫ i) :=
  pullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.pullback.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z X' Y' Z' X
'' Y'' Z'' : C} {f : X ⟶ Z} {g : Y ⟶ Z}   {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} {f'' : X
'' ⟶ Z''} {g'' : Y'' ⟶ Z''} (i₁ : X ⟶ X') (j₁ : X' ⟶ X'') (i₂ : Y ⟶ Y')   (j₂ : 
Y' ⟶ Y'') (i₃ : Z ⟶ Z') (j₃ : Z' ⟶ Z'') [inst_1 : CategoryTheory.Limits.HasPullb
ack f g]   [inst_2 : CategoryTheory.Limits.HasPullback f' g'] [inst_3 : Category
Theory.Limits.HasPullback f'' g'']   (e₁ : CategoryTheory.CategoryStruct.comp f 
i₃ = CategoryTheory.CategoryStruct.comp i₁ f')   (e₂ : CategoryTheory.CategorySt
ruct.comp g i₃ = CategoryTheory.CategoryStruct.comp i₂ g')   (e₃ : CategoryTheor
y.CategoryStruct.comp f' j₃ = CategoryTheory.CategoryStruct.comp j₁ f'')   (e₄ :
 CategoryTheory.CategoryStruct.comp g' j₃ = CategoryTheory.CategoryStruct.comp j
₂ g''),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.map
 f g f' g' i₁ i₂ i₃ e₁ e₂)       (CategoryTheory.Limits.pullback.map f' g' f'' g
'' j₁ j₂ j₃ e₃ e₄) =     CategoryTheory.Limits.pullback.map f g f'' g'' (Categor
yTheory.CategoryStruct.comp i₁ j₁)       (CategoryTheory.CategoryStruct.comp i₂ 
j₂) (CategoryTheory.CategoryStruct.comp i₃ j₃) ⋯ ⋯
参数：i₁ : X ⟶ X'；j₁ : X' ⟶ X''；i₂ : Y ⟶ Y'；j₂ : Y' ⟶ Y''；i₃ : Z ⟶ Z'；j₃ : Z' ⟶ Z''
；e₁ : CategoryTheory.CategoryStruct.comp f i₃ = CategoryTheory.CategoryStruct.co
mp i₁ f'；e₂ : CategoryTheory.CategoryStruct.comp g i₃ = CategoryTheory.CategoryS
truct.comp i₂ g'；e₃ : CategoryTheory.CategoryStruct.comp f' j₃ = CategoryTheory.
CategoryStruct.comp j₁ f''；e₄ : CategoryTheory.CategoryStruct.comp g' j₃ = Categ
oryTheory.CategoryStruct.comp j₂ g''；CategoryTheory.Limits.pullback.map f g f' g
' i₁ i₂ i₃ e₁ e₂；CategoryTheory.Limits.pullback.map f' g' f'' g'' j₁ j₂ j₃ e₃ e₄
；CategoryTheory.CategoryStruct.comp i₁ j₁；CategoryTheory.CategoryStruct.comp i₂ 
j₂；CategoryTheory.CategoryStruct.comp i₃ j₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullback.map_comp {X Y Z X' Y' Z' X'' Y'' Z'' : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} {f'' : X'' ⟶ Z''} {g'' : Y'' ⟶ Z''}
    (i₁ : X ⟶ X') (j₁ : X' ⟶ X'') (i₂ : Y ⟶ Y') (j₂ : Y' ⟶ Y'') (i₃ : Z ⟶ Z') (j₃ : Z' ⟶ Z'')
    [HasPullback f g] [HasPullback f' g'] [HasPullback f'' g'']
    (e₁ e₂ e₃ e₄) :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ ≫ pullback.map f' g' f'' g'' j₁ j₂ j₃ e₃ e₄ =
      pullback.map f g f'' g'' (i₁ ≫ j₁) (i₂ ≫ j₂) (i₃ ≫ j₃)
        (by rw [reassoc_of% e₁, e₃, Category.assoc])
        (by rw [reassoc_of% e₂, e₄, Category.assoc]) := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.pullback.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPullback f g],   Categor
yTheory.Limits.pullback.map f g f g (CategoryTheory.CategoryStruct.id X) (Catego
ryTheory.CategoryStruct.id Y)       (CategoryTheory.CategoryStruct.id Z) ⋯ ⋯ =  
   CategoryTheory.CategoryStruct.id (CategoryTheory.Limits.pullback f g)
参数：CategoryTheory.CategoryStruct.id X；CategoryTheory.CategoryStruct.id Y；Categor
yTheory.CategoryStruct.id Z；CategoryTheory.Limits.pullback f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullback.map_id {X Y Z : C}
    {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    pullback.map f g f g (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by ext <;> simp

/-- Given such a diagram, then there is a natural morphism `W ⨿ₛ X ⟶ Y ⨿ₜ Z`.

```
  W ⟶ Y
 ↗   ↗
S ⟶ T
 ↘   ↘
  X ⟶ Z
```
-/
/-
**CategoryTheory.Limits.pushout.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.pushout`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {W X Y Z 
S T : C} →       (f₁ : S ⟶ W) →         (f₂ : S ⟶ X) →           [inst_1 : Categ
oryTheory.Limits.HasPushout f₁ f₂] →             (g₁ : T ⟶ Y) →               (g
₂ : T ⟶ Z) →                 [inst_2 : CategoryTheory.Limits.HasPushout g₁ g₂] →
                   (i₁ : W ⟶ Y) →                     (i₂ : X ⟶ Z) →            
           (i₃ : S ⟶ T) →                         CategoryTheory.CategoryStruct.
comp f₁ i₁ = CategoryTheory.CategoryStruct.comp i₃ g₁ →                         
  CategoryTheory.CategoryStruct.comp f₂ i₂ = CategoryTheory.CategoryStruct.comp 
i₃ g₂ →                             (CategoryTheory.Limits.pushout f₁ f₂ ⟶ Categ
oryTheory.Limits.pushout g₁ g₂)
参数：f₁ : S ⟶ W；f₂ : S ⟶ X；g₁ : T ⟶ Y；g₂ : T ⟶ Z；i₁ : W ⟶ Y；i₂ : X ⟶ Z；i₃ : S ⟶ T；
CategoryTheory.Limits.pushout f₁ f₂ ⟶ CategoryTheory.Limits.pushout g₁ g₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given such a diagram, then there is a natural morphism `W ⨿ₛ X ⟶ Y ⨿ₜ Z`.

```
  W ⟶ Y
 ↗   ↗
S ⟶ T
 ↘   ↘
  X ⟶ Z
```
-/
abbrev pushout.map {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y)
    (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁)
    (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) : pushout f₁ f₂ ⟶ pushout g₁ g₂ :=
  pushout.desc (i₁ ≫ pushout.inl _ _) (i₂ ≫ pushout.inr _ _)
    (by simp only [reassoc_of% eq₁, reassoc_of% eq₂, condition])

/-- The canonical map `X ⨿ₛ Y ⟶ X ⨿ₜ Y` given `S ⟶ T`. -/
/-
**CategoryTheory.Limits.pushout.mapLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.pushout`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y S T 
: C} →       (f : T ⟶ X) →         (g : T ⟶ Y) →           (i : S ⟶ T) →        
     [inst_1 : CategoryTheory.Limits.HasPushout f g] →               [inst_2 :  
                 CategoryTheory.Limits.HasPushout (CategoryTheory.CategoryStruct
.comp i f)                     (CategoryTheory.CategoryStruct.comp i g)] →      
           CategoryTheory.Limits.pushout (CategoryTheory.CategoryStruct.comp i f
)                     (CategoryTheory.CategoryStruct.comp i g) ⟶                
   CategoryTheory.Limits.pushout f g
参数：f : T ⟶ X；g : T ⟶ Y；i : S ⟶ T；CategoryTheory.CategoryStruct.comp i f；Category
Theory.CategoryStruct.comp i g；CategoryTheory.CategoryStruct.comp i f；CategoryTh
eory.CategoryStruct.comp i g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `X ⨿ₛ Y ⟶ X ⨿ₜ Y` given `S ⟶ T`.
-/
abbrev pushout.mapLift {X Y S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) [HasPushout f g]
    [HasPushout (i ≫ f) (i ≫ g)] : pushout (i ≫ f) (i ≫ g) ⟶ pushout f g :=
  pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (Category.comp_id _) (Category.comp_id _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.pushout.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z X' Y' Z' X
'' Y'' Z'' : C} {f : X ⟶ Y} {g : X ⟶ Z}   {f' : X' ⟶ Y'} {g' : X' ⟶ Z'} {f'' : X
'' ⟶ Y''} {g'' : X'' ⟶ Z''} (i₁ : X ⟶ X') (j₁ : X' ⟶ X'') (i₂ : Y ⟶ Y')   (j₂ : 
Y' ⟶ Y'') (i₃ : Z ⟶ Z') (j₃ : Z' ⟶ Z'') [inst_1 : CategoryTheory.Limits.HasPusho
ut f g]   [inst_2 : CategoryTheory.Limits.HasPushout f' g'] [inst_3 : CategoryTh
eory.Limits.HasPushout f'' g'']   (e₁ : CategoryTheory.CategoryStruct.comp f i₂ 
= CategoryTheory.CategoryStruct.comp i₁ f')   (e₂ : CategoryTheory.CategoryStruc
t.comp g i₃ = CategoryTheory.CategoryStruct.comp i₁ g')   (e₃ : CategoryTheory.C
ategoryStruct.comp f' j₂ = CategoryTheory.CategoryStruct.comp j₁ f'')   (e₄ : Ca
tegoryTheory.CategoryStruct.comp g' j₃ = CategoryTheory.CategoryStruct.comp j₁ g
''),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pushout.map f g
 f' g' i₂ i₃ i₁ e₁ e₂)       (CategoryTheory.Limits.pushout.map f' g' f'' g'' j₂
 j₃ j₁ e₃ e₄) =     CategoryTheory.Limits.pushout.map f g f'' g'' (CategoryTheor
y.CategoryStruct.comp i₂ j₂)       (CategoryTheory.CategoryStruct.comp i₃ j₃) (C
ategoryTheory.CategoryStruct.comp i₁ j₁) ⋯ ⋯
参数：i₁ : X ⟶ X'；j₁ : X' ⟶ X''；i₂ : Y ⟶ Y'；j₂ : Y' ⟶ Y''；i₃ : Z ⟶ Z'；j₃ : Z' ⟶ Z''
；e₁ : CategoryTheory.CategoryStruct.comp f i₂ = CategoryTheory.CategoryStruct.co
mp i₁ f'；e₂ : CategoryTheory.CategoryStruct.comp g i₃ = CategoryTheory.CategoryS
truct.comp i₁ g'；e₃ : CategoryTheory.CategoryStruct.comp f' j₂ = CategoryTheory.
CategoryStruct.comp j₁ f''；e₄ : CategoryTheory.CategoryStruct.comp g' j₃ = Categ
oryTheory.CategoryStruct.comp j₁ g''；CategoryTheory.Limits.pushout.map f g f' g'
 i₂ i₃ i₁ e₁ e₂；CategoryTheory.Limits.pushout.map f' g' f'' g'' j₂ j₃ j₁ e₃ e₄；C
ategoryTheory.CategoryStruct.comp i₂ j₂；CategoryTheory.CategoryStruct.comp i₃ j₃
；CategoryTheory.CategoryStruct.comp i₁ j₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pushout.map_comp {X Y Z X' Y' Z' X'' Y'' Z'' : C}
    {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'} {f'' : X'' ⟶ Y''} {g'' : X'' ⟶ Z''}
    (i₁ : X ⟶ X') (j₁ : X' ⟶ X'') (i₂ : Y ⟶ Y') (j₂ : Y' ⟶ Y'') (i₃ : Z ⟶ Z') (j₃ : Z' ⟶ Z'')
    [HasPushout f g] [HasPushout f' g'] [HasPushout f'' g'']
    (e₁ e₂ e₃ e₄) :
    pushout.map f g f' g' i₂ i₃ i₁ e₁ e₂ ≫ pushout.map f' g' f'' g'' j₂ j₃ j₁ e₃ e₄ =
      pushout.map f g f'' g'' (i₂ ≫ j₂) (i₃ ≫ j₃) (i₁ ≫ j₁)
        (by rw [reassoc_of% e₁, e₃, Category.assoc])
        (by rw [reassoc_of% e₂, e₄, Category.assoc]) := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.pushout.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   [inst_1 : CategoryTheory.Limits.HasPushout f g],   Category
Theory.Limits.pushout.map f g f g (CategoryTheory.CategoryStruct.id Y) (Category
Theory.CategoryStruct.id Z)       (CategoryTheory.CategoryStruct.id X) ⋯ ⋯ =    
 CategoryTheory.CategoryStruct.id (CategoryTheory.Limits.pushout f g)
参数：CategoryTheory.CategoryStruct.id Y；CategoryTheory.CategoryStruct.id Z；Categor
yTheory.CategoryStruct.id X；CategoryTheory.Limits.pushout f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pushout.map_id {X Y Z : C}
    {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    pushout.map f g f g (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pullback.map_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z S T : C}
 (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [inst_1 : CategoryTheory.Limits.HasPullback f₁ f₂] 
(g₁ : Y ⟶ T) (g₂ : Z ⟶ T)   [inst_2 : CategoryTheory.Limits.HasPullback g₁ g₂] (
i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)   (eq₁ : CategoryTheory.CategoryStruct.com
p f₁ i₃ = CategoryTheory.CategoryStruct.comp i₁ g₁)   (eq₂ : CategoryTheory.Cate
goryStruct.comp f₂ i₃ = CategoryTheory.CategoryStruct.comp i₂ g₂) [CategoryTheor
y.IsIso i₁]   [CategoryTheory.IsIso i₂] [CategoryTheory.IsIso i₃],   CategoryThe
ory.IsIso (CategoryTheory.Limits.pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂)
参数：f₁ : W ⟶ S；f₂ : X ⟶ S；g₁ : Y ⟶ T；g₂ : Z ⟶ T；i₁ : W ⟶ Y；i₂ : X ⟶ Z；i₃ : S ⟶ T；
eq₁ : CategoryTheory.CategoryStruct.comp f₁ i₃ = CategoryTheory.CategoryStruct.c
omp i₁ g₁；eq₂ : CategoryTheory.CategoryStruct.comp f₂ i₃ = CategoryTheory.Catego
ryStruct.comp i₂ g₂；CategoryTheory.Limits.pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ 
eq₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.comp_inv_eq`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
-/
instance pullback.map_isIso {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine ⟨⟨pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · cat_disch
  · cat_disch

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pullback f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps! hom]
/-
**CategoryTheory.Limits.pullback.congrHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.pullback`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f₁ f₂ : X ⟶ Z} →         {g₁ g₂ : Y ⟶ Z} →           f₁ = f₂ →      
       g₁ = g₂ →               [inst_1 : CategoryTheory.Limits.HasPullback f₁ g₁
] →                 [inst_2 : CategoryTheory.Limits.HasPullback f₂ g₂] →        
           CategoryTheory.Limits.pullback f₁ g₁ ≅ CategoryTheory.Limits.pullback
 f₂ g₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pullback f₁ g₁ ≅ pullback f₂ g₂`
-/
def pullback.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] : pullback f₁ g₁ ≅ pullback f₂ g₂ :=
  asIso <| pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.pullback.congrHom_inv** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f
₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1 : CategoryThe
ory.Limits.HasPullback f₁ g₁] [inst_2 : CategoryTheory.Limits.HasPullback f₂ g₂]
,   (CategoryTheory.Limits.pullback.congrHom h₁ h₂).inv =     CategoryTheory.Lim
its.pullback.map f₂ g₂ f₁ g₁ (CategoryTheory.CategoryStruct.id X)       (Categor
yTheory.CategoryStruct.id Y) (CategoryTheory.CategoryStruct.id Z) ⋯ ⋯
参数：h₁ : f₁ = f₂；h₂ : g₁ = g₂；CategoryTheory.Limits.pullback.congrHom h₁ h₂；Categ
oryTheory.CategoryStruct.id X；CategoryTheory.CategoryStruct.id Y；CategoryTheory.
CategoryStruct.id Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullback.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).inv =
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
  ext <;> simp [Iso.inv_comp_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pushout.map_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z S T : C}
 (f₁ : S ⟶ W) (f₂ : S ⟶ X)   [inst_1 : CategoryTheory.Limits.HasPushout f₁ f₂] (
g₁ : T ⟶ Y) (g₂ : T ⟶ Z)   [inst_2 : CategoryTheory.Limits.HasPushout g₁ g₂] (i₁
 : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)   (eq₁ : CategoryTheory.CategoryStruct.comp 
f₁ i₁ = CategoryTheory.CategoryStruct.comp i₃ g₁)   (eq₂ : CategoryTheory.Catego
ryStruct.comp f₂ i₂ = CategoryTheory.CategoryStruct.comp i₃ g₂) [CategoryTheory.
IsIso i₁]   [CategoryTheory.IsIso i₂] [CategoryTheory.IsIso i₃],   CategoryTheor
y.IsIso (CategoryTheory.Limits.pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂)
参数：f₁ : S ⟶ W；f₂ : S ⟶ X；g₁ : T ⟶ Y；g₂ : T ⟶ Z；i₁ : W ⟶ Y；i₂ : X ⟶ Z；i₃ : S ⟶ T；
eq₁ : CategoryTheory.CategoryStruct.comp f₁ i₁ = CategoryTheory.CategoryStruct.c
omp i₃ g₁；eq₂ : CategoryTheory.CategoryStruct.comp f₂ i₂ = CategoryTheory.Catego
ryStruct.comp i₃ g₂；CategoryTheory.Limits.pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ e
q₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.comp_inv_eq`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance pushout.map_isIso {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
    (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine ⟨⟨pushout.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) ?_ ?_, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
  · cat_disch
  · cat_disch

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pullback.mapDesc_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.pullback`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y S T S' : C} 
(f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S)   (i' : S ⟶ S') [inst_1 : CategoryTheory.Lim
its.HasPullback f g]   [inst_2 :     CategoryTheory.Limits.HasPullback (Category
Theory.CategoryStruct.comp f i) (CategoryTheory.CategoryStruct.comp g i)]   [ins
t_3 :     CategoryTheory.Limits.HasPullback (CategoryTheory.CategoryStruct.comp 
f (CategoryTheory.CategoryStruct.comp i i'))       (CategoryTheory.CategoryStruc
t.comp g (CategoryTheory.CategoryStruct.comp i i'))]   [inst_4 :     CategoryThe
ory.Limits.HasPullback (CategoryTheory.CategoryStruct.comp (CategoryTheory.Categ
oryStruct.comp f i) i')       (CategoryTheory.CategoryStruct.comp (CategoryTheor
y.CategoryStruct.comp g i) i')],   CategoryTheory.Limits.pullback.mapDesc f g (C
ategoryTheory.CategoryStruct.comp i i') =     CategoryTheory.CategoryStruct.comp
 (CategoryTheory.Limits.pullback.mapDesc f g i)       (CategoryTheory.CategorySt
ruct.comp         (CategoryTheory.Limits.pullback.mapDesc (CategoryTheory.Catego
ryStruct.comp f i)           (CategoryTheory.CategoryStruct.comp g i) i')       
  (CategoryTheory.Limits.pullback.congrHom ⋯ ⋯).hom)
参数：f : X ⟶ T；g : Y ⟶ T；i : T ⟶ S；i' : S ⟶ S'；CategoryTheory.CategoryStruct.comp 
f i；CategoryTheory.CategoryStruct.comp g i；CategoryTheory.CategoryStruct.comp f 
(CategoryTheory.CategoryStruct.comp i i')；CategoryTheory.CategoryStruct.comp g (
CategoryTheory.CategoryStruct.comp i i')；CategoryTheory.CategoryStruct.comp (Cat
egoryTheory.CategoryStruct.comp f i) i'；CategoryTheory.CategoryStruct.comp (Cate
goryTheory.CategoryStruct.comp g i) i'；CategoryTheory.CategoryStruct.comp i i'；C
ategoryTheory.Limits.pullback.mapDesc f g i；CategoryTheory.CategoryStruct.comp  
       (CategoryTheory.Limits.pullback.mapDesc (CategoryTheory.CategoryStruct.co
mp f i)           (CategoryTheory.CategoryStruct.comp g i) i')         (Category
Theory.Limits.pullback.congrHom ⋯ ⋯).hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullback.mapDesc_comp {X Y S T S' : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S) (i' : S ⟶ S')
    [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] [HasPullback (f ≫ i ≫ i') (g ≫ i ≫ i')]
    [HasPullback ((f ≫ i) ≫ i') ((g ≫ i) ≫ i')] :
    pullback.mapDesc f g (i ≫ i') = pullback.mapDesc f g i ≫ pullback.mapDesc _ _ i' ≫
    (pullback.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom := by
  cat_disch

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pushout f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps! hom]
/-
**CategoryTheory.Limits.pushout.congrHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.pushout`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f₁ f₂ : X ⟶ Y} →         {g₁ g₂ : X ⟶ Z} →           f₁ = f₂ →      
       g₁ = g₂ →               [inst_1 : CategoryTheory.Limits.HasPushout f₁ g₁]
 →                 [inst_2 : CategoryTheory.Limits.HasPushout f₂ g₂] →          
         CategoryTheory.Limits.pushout f₁ g₁ ≅ CategoryTheory.Limits.pushout f₂ 
g₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pushout f₁ g₁ ≅ pullback f₂ g₂`
-/
def pushout.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPushout f₁ g₁] [HasPushout f₂ g₂] : pushout f₁ g₁ ≅ pushout f₂ g₂ :=
  asIso <| pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.pushout.congrHom_inv** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f
₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1 : CategoryThe
ory.Limits.HasPushout f₁ g₁] [inst_2 : CategoryTheory.Limits.HasPushout f₂ g₂], 
  (CategoryTheory.Limits.pushout.congrHom h₁ h₂).inv =     CategoryTheory.Limits
.pushout.map f₂ g₂ f₁ g₁ (CategoryTheory.CategoryStruct.id Y)       (CategoryThe
ory.CategoryStruct.id Z) (CategoryTheory.CategoryStruct.id X) ⋯ ⋯
参数：h₁ : f₁ = f₂；h₂ : g₁ = g₂；CategoryTheory.Limits.pushout.congrHom h₁ h₂；Catego
ryTheory.CategoryStruct.id Y；CategoryTheory.CategoryStruct.id Z；CategoryTheory.C
ategoryStruct.id X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.pushout.congrHom_hom`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f
₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushout.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPushout f₁ g₁] [HasPushout f₂ g₂] :
    (pushout.congrHom h₁ h₂).inv =
      pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
  ext <;> simp [Iso.comp_inv_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pushout.mapLift_comp** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y S T S' : C} 
(f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T)   (i' : S' ⟶ S) [inst_1 : CategoryTheory.Lim
its.HasPushout f g]   [inst_2 :     CategoryTheory.Limits.HasPushout (CategoryTh
eory.CategoryStruct.comp i f) (CategoryTheory.CategoryStruct.comp i g)]   [inst_
3 :     CategoryTheory.Limits.HasPushout (CategoryTheory.CategoryStruct.comp i' 
(CategoryTheory.CategoryStruct.comp i f))       (CategoryTheory.CategoryStruct.c
omp i' (CategoryTheory.CategoryStruct.comp i g))]   [inst_4 :     CategoryTheory
.Limits.HasPushout (CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryS
truct.comp i' i) f)       (CategoryTheory.CategoryStruct.comp (CategoryTheory.Ca
tegoryStruct.comp i' i) g)],   CategoryTheory.Limits.pushout.mapLift f g (Catego
ryTheory.CategoryStruct.comp i' i) =     CategoryTheory.CategoryStruct.comp (Cat
egoryTheory.Limits.pushout.congrHom ⋯ ⋯).hom       (CategoryTheory.CategoryStruc
t.comp         (CategoryTheory.Limits.pushout.mapLift (CategoryTheory.CategorySt
ruct.comp i f)           (CategoryTheory.CategoryStruct.comp i g) i')         (C
ategoryTheory.Limits.pushout.mapLift f g i))
参数：f : T ⟶ X；g : T ⟶ Y；i : S ⟶ T；i' : S' ⟶ S；CategoryTheory.CategoryStruct.comp 
i f；CategoryTheory.CategoryStruct.comp i g；CategoryTheory.CategoryStruct.comp i'
 (CategoryTheory.CategoryStruct.comp i f)；CategoryTheory.CategoryStruct.comp i' 
(CategoryTheory.CategoryStruct.comp i g)；CategoryTheory.CategoryStruct.comp (Cat
egoryTheory.CategoryStruct.comp i' i) f；CategoryTheory.CategoryStruct.comp (Cate
goryTheory.CategoryStruct.comp i' i) g；CategoryTheory.CategoryStruct.comp i' i；C
ategoryTheory.Limits.pushout.congrHom ⋯ ⋯；CategoryTheory.CategoryStruct.comp    
     (CategoryTheory.Limits.pushout.mapLift (CategoryTheory.CategoryStruct.comp 
i f)           (CategoryTheory.CategoryStruct.comp i g) i')         (CategoryThe
ory.Limits.pushout.mapLift f g i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pushout.congrHom_hom`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f
₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushout.mapLift_comp {X Y S T S' : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) (i' : S' ⟶ S)
    [HasPushout f g] [HasPushout (i ≫ f) (i ≫ g)] [HasPushout (i' ≫ i ≫ f) (i' ≫ i ≫ g)]
    [HasPushout ((i' ≫ i) ≫ f) ((i' ≫ i) ≫ g)] :
    pushout.mapLift f g (i' ≫ i) =
      (pushout.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom ≫
        pushout.mapLift _ _ i' ≫ pushout.mapLift f g i := by
  cat_disch

section

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/-- The comparison morphism for the pullback of `f,g`.
This is an isomorphism iff `G` preserves the pullback of `f,g`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean`
-/
/-
**CategoryTheory.Limits.pullbackComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback 
(G.map f) (G.map g)] : G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g)
参数：f : X ⟶ Z；g : Y ⟶ Z；G.map f；G.map g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison morphism for the pullback of `f,g`.
This is an isomorphism iff `G` preserves the pullback of `f,g`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean`
-/
def pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)] :
    G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g) :=
  pullback.lift (G.map (pullback.fst f g)) (G.map (pullback.snd f g))
    (by simp only [← G.map_comp, pullback.condition])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackComparison_comp_fst** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackComparison_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [Has
Pullback (G.map f) (G.map g)] : pullbackComparison G f g ≫ pullback.fst _ _ = G.
map (pullback.fst f g)
参数：f : X ⟶ Z；g : Y ⟶ Z；G.map f；G.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem pullbackComparison_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.fst _ _ = G.map (pullback.fst f g) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackComparison_comp_snd** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackComparison_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [Has
Pullback (G.map f) (G.map g)] : pullbackComparison G f g ≫ pullback.snd _ _ = G.
map (pullback.snd f g)
参数：f : X ⟶ Z；g : Y ⟶ Z；G.map f；G.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem pullbackComparison_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.snd _ _ = G.map (pullback.snd f g) :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.map_lift_pullbackComparison** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：map_lift_pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [Has
Pullback (G.map f) (G.map g)] {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g
) : G.map (pullback.lift _ _ w) ≫ pullbackComparison G f g = pullback.lift (G.ma
p h) (G.map k) (by simp only [← G.map_comp, w])
参数：f : X ⟶ Z；g : Y ⟶ Z；G.map f；G.map g；w : h ≫ f = k ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackComparison_comp_fst`：pullbackComparison_co
mp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g
)] : pullbackComparison G f g ≫ pullbac…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullbackComparison_comp_snd`：pullbackComparison_co
mp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g
)] : pullbackComparison G f g ≫ pullbac…
-/
theorem map_lift_pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) :
    G.map (pullback.lift _ _ w) ≫ pullbackComparison G f g =
      pullback.lift (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
  ext <;> simp [← G.map_comp]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Limits.pullbackComparison_comp** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：pullbackComparison_comp {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) 
{X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [HasPullback (F.map f) (F.
map g)] [HasPullback (G.map (F.map f)) (G.map (F.map g))] [HasPullback ((F ⋙ G).
map f) ((F ⋙ G).map g)] : pullbackComparison (F ⋙ G) f g = G.map (pullbackCompar
ison F f g) ≫ pullbackComparison G (F.map f) (F.map g)
参数：F : C ⥤ D；G : D ⥤ E；f : X ⟶ S；g : Y ⟶ S；F.map f；F.map g；G.map (F.map f)；G.map
 (F.map g)；(F ⋙ G).map f；(F ⋙ G).map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullbackComparison_comp_fst`：pullbackComparison_co
mp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g
)] : pullbackComparison G f g ≫ pullbac…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullbackComparison_comp_snd`：pullbackComparison_co
mp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g
)] : pullbackComparison G f g ≫ pullbac…
-/
lemma pullbackComparison_comp {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E) {X Y S : C}
    (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [HasPullback (F.map f) (F.map g)]
    [HasPullback (G.map (F.map f)) (G.map (F.map g))]
    [HasPullback ((F ⋙ G).map f) ((F ⋙ G).map g)] :
    pullbackComparison (F ⋙ G) f g = G.map (pullbackComparison F f g) ≫
      pullbackComparison G (F.map f) (F.map g) := by
  ext
  · rw [pullbackComparison_comp_fst]
    simp [← Functor.map_comp]
  · rw [pullbackComparison_comp_snd]
    simp [← Functor.map_comp]

/-- The comparison morphism for the pushout of `f,g`.
This is an isomorphism iff `G` preserves the pushout of `f,g`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean`
-/
/-
**CategoryTheory.Limits.pushoutComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.
map f) (G.map g)] : pushout (G.map f) (G.map g) ⟶ G.obj (pushout f g)
参数：f : X ⟶ Y；g : X ⟶ Z；G.map f；G.map g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison morphism for the pushout of `f,g`.
This is an isomorphism iff `G` preserves the pushout of `f,g`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean`
-/
def pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
    pushout (G.map f) (G.map g) ⟶ G.obj (pushout f g) :=
  pushout.desc (G.map (pushout.inl _ _)) (G.map (pushout.inr _ _))
    (by simp only [← G.map_comp, pushout.condition])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_comp_pushoutComparison** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inl_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPu
shout (G.map f) (G.map g)] : pushout.inl _ _ ≫ pushoutComparison G f g = G.map (
pushout.inl _ _)
参数：f : X ⟶ Y；g : X ⟶ Z；G.map f；G.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.inl_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
-/
theorem inl_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inl _ _ ≫ pushoutComparison G f g =
      G.map (pushout.inl _ _) :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_comp_pushoutComparison** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inr_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPu
shout (G.map f) (G.map g)] : pushout.inr _ _ ≫ pushoutComparison G f g = G.map (
pushout.inr _ _)
参数：f : X ⟶ Y；g : X ⟶ Z；G.map f；G.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.inr_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
-/
theorem inr_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inr _ _ ≫ pushoutComparison G f g =
      G.map (pushout.inr _ _) :=
  pushout.inr_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pushoutComparison_map_desc** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：pushoutComparison_map_desc (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPu
shout (G.map f) (G.map g)] {W : C} {h : Y ⟶ W} {k : Z ⟶ W} (w : f ≫ h = g ≫ k) :
 pushoutComparison G f g ≫ G.map (pushout.desc _ _ w) = pushout.desc (G.map h) (
G.map k) (by simp only [← G.map_comp, w])
参数：f : X ⟶ Y；g : X ⟶ Z；G.map f；G.map g；w : f ≫ h = g ≫ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutComparison_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {D : Type u₂}   [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D] (G : Cate…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.inr_comp_pushoutComparison_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {D : Type u₂}   [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D] (G : Cate…
-/
theorem pushoutComparison_map_desc (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] {W : C} {h : Y ⟶ W} {k : Z ⟶ W} (w : f ≫ h = g ≫ k) :
    pushoutComparison G f g ≫ G.map (pushout.desc _ _ w) =
      pushout.desc (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
  ext <;> simp [← G.map_comp]

end

section PullbackSymmetry

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z)

/-- Making this a global instance would make the typeclass search go in an infinite loop. -/
/-
**CategoryTheory.Limits.hasPullback_symmetry** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：hasPullback_symmetry [HasPullback f g] : HasPullback g f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…

--- 原说明 ---
Making this a global instance would make the typeclass search go in an infinite 
loop.
-/
theorem hasPullback_symmetry [HasPullback f g] : HasPullback g f :=
  ⟨⟨⟨_, PullbackCone.flipIsLimit (pullbackIsPullback f g)⟩⟩⟩

attribute [local instance] hasPullback_symmetry

/-- The isomorphism `X ×[Z] Y ≅ Y ×[Z] X`. -/
/-
**CategoryTheory.Limits.pullbackSymmetry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：pullbackSymmetry [HasPullback f g] : pullback f g ≅ pullback g f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f

--- 原说明 ---
The isomorphism `X ×[Z] Y ≅ Y ×[Z] X`.
-/
def pullbackSymmetry [HasPullback f g] : pullback f g ≅ pullback g f :=
  IsLimit.conePointUniqueUpToIso
    (PullbackCone.flipIsLimit (pullbackIsPullback f g)) (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：pullbackSymmetry_hom_comp_fst [HasPullback f g] : (pullbackSymmetry f g).h
om ≫ pullback.fst g f = pullback.snd f g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackSymmetry_hom_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.fst g f = pullback.snd f g := by simp [pullbackSymmetry]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：pullbackSymmetry_hom_comp_snd [HasPullback f g] : (pullbackSymmetry f g).h
om ≫ pullback.snd g f = pullback.fst f g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp`：∀ {J : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : Category
Theory.Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackSymmetry_hom_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.snd g f = pullback.fst f g := by simp [pullbackSymmetry]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackSymmetry_inv_comp_fst** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：pullbackSymmetry_inv_comp_fst [HasPullback f g] : (pullbackSymmetry f g).i
nv ≫ pullback.fst f g = pullback.snd g f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd`：pullbackSymmetry_ho
m_comp_snd [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.snd g f = p
ullback.fst f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackSymmetry_inv_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.fst f g = pullback.snd g f := by simp [Iso.inv_comp_eq]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：pullbackSymmetry_inv_comp_snd [HasPullback f g] : (pullbackSymmetry f g).i
nv ≫ pullback.snd f g = pullback.fst g f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst`：pullbackSymmetry_ho
m_comp_fst [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.fst g f = p
ullback.snd f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackSymmetry_inv_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.snd f g = pullback.fst g f := by simp [Iso.inv_comp_eq]

end PullbackSymmetry

section PushoutSymmetry

open WalkingCospan

variable (f : X ⟶ Y) (g : X ⟶ Z)

/-- Making this a global instance would make the typeclass search go in an infinite loop. -/
/-
**CategoryTheory.Limits.hasPushout_symmetry** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：hasPushout_symmetry [HasPushout f g] : HasPushout g f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …

--- 原说明 ---
Making this a global instance would make the typeclass search go in an infinite 
loop.
-/
theorem hasPushout_symmetry [HasPushout f g] : HasPushout g f :=
  ⟨⟨⟨_, PushoutCocone.flipIsColimit (pushoutIsPushout f g)⟩⟩⟩

attribute [local instance] hasPushout_symmetry

/-- The isomorphism `Y ⨿[X] Z ≅ Z ⨿[X] Y`. -/
/-
**CategoryTheory.Limits.pushoutSymmetry** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：pushoutSymmetry [HasPushout f g] : pushout f g ≅ pushout g f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f

--- 原说明 ---
The isomorphism `Y ⨿[X] Z ≅ Z ⨿[X] Y`.
-/
def pushoutSymmetry [HasPushout f g] : pushout f g ≅ pushout g f :=
  IsColimit.coconePointUniqueUpToIso
    (PushoutCocone.flipIsColimit (pushoutIsPushout f g)) (colimit.isColimit _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：inl_comp_pushoutSymmetry_hom [HasPushout f g] : pushout.inl _ _ ≫ (pushout
Symmetry f g).hom = pushout.inr _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
-/
theorem inl_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutSymmetry f g).hom = pushout.inr _ _ :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：inr_comp_pushoutSymmetry_hom [HasPushout f g] : pushout.inr _ _ ≫ (pushout
Symmetry f g).hom = pushout.inl _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
-/
theorem inr_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutSymmetry f g).hom = pushout.inl _ _ :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_comp_pushoutSymmetry_inv** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：inl_comp_pushoutSymmetry_inv [HasPushout f g] : pushout.inl _ _ ≫ (pushout
Symmetry f g).inv = pushout.inr _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom`：inr_comp_pushoutSymm
etry_hom [HasPushout f g] : pushout.inr _ _ ≫ (pushoutSymmetry f g).hom = pushou
t.inl _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inl _ _ ≫ (pushoutSymmetry f g).inv = pushout.inr _ _ := by simp [Iso.comp_inv_eq]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_comp_pushoutSymmetry_inv** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：inr_comp_pushoutSymmetry_inv [HasPushout f g] : pushout.inr _ _ ≫ (pushout
Symmetry f g).inv = pushout.inl _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom`：inl_comp_pushoutSymm
etry_hom [HasPushout f g] : pushout.inl _ _ ≫ (pushoutSymmetry f g).hom = pushou
t.inr _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inr _ _ ≫ (pushoutSymmetry f g).inv = pushout.inl _ _ := by simp [Iso.comp_inv_eq]

end PushoutSymmetry

/-- `HasPullbacksAlong f` states that pullbacks of all morphisms into `Y`
along `f : X ⟶ Y` exist. -/
/-
**CategoryTheory.Limits.HasPullbacksAlong** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：HasPullbacksAlong (f : X ⟶ Y) : Prop
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasPullbacksAlong f` states that pullbacks of all morphisms into `Y`
along `f : X ⟶ Y` exist.
-/
abbrev HasPullbacksAlong (f : X ⟶ Y) : Prop := ∀ {W} (h : W ⟶ Y), HasPullback h f

/-- `HasPushoutsAlong f` states that pushouts of all morphisms out of `X`
along `f : X ⟶ Y` exist. -/
/-
**CategoryTheory.Limits.HasPushoutsAlong** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：HasPushoutsAlong (f : X ⟶ Y) : Prop
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasPushoutsAlong f` states that pushouts of all morphisms out of `X`
along `f : X ⟶ Y` exist.
-/
abbrev HasPushoutsAlong (f : X ⟶ Y) : Prop := ∀ {W} (h : X ⟶ W), HasPushout h f

variable (C)

/-- A category `HasPullbacks` if it has all limits of shape `WalkingCospan`, i.e. if it has a
pullback for every pair of morphisms with the same codomain. -/
@[stacks 001W]
/-
**CategoryTheory.Limits.HasPullbacks** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：HasPullbacks
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasPullbacks` if it has all limits of shape `WalkingCospan`, i.e. if
 it has a
pullback for every pair of morphisms with the same codomain.
-/
abbrev HasPullbacks :=
  HasLimitsOfShape WalkingCospan C

/-- A category `HasPushouts` if it has all colimits of shape `WalkingSpan`, i.e. if it has a
pushout for every pair of morphisms with the same domain. -/
/-
**CategoryTheory.Limits.HasPushouts** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：HasPushouts
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasPushouts` if it has all colimits of shape `WalkingSpan`, i.e. if 
it has a
pushout for every pair of morphisms with the same domain.
-/
abbrev HasPushouts :=
  HasColimitsOfShape WalkingSpan C

/-- If `C` has all limits of diagrams `cospan f g`, then it has all pullbacks -/
/-
**CategoryTheory.Limits.hasPullbacks_of_hasLimit_cospan** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasPullbacks_of_hasLimit_cospan [forall {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z
}, HasLimit (cospan f g)] : HasPullbacks C
参数：cospan f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G

--- 原说明 ---
If `C` has all limits of diagrams `cospan f g`, then it has all pullbacks
-/
theorem hasPullbacks_of_hasLimit_cospan
    [∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g)] : HasPullbacks C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoCospan F).symm }

/-- If `C` has all colimits of diagrams `span f g`, then it has all pushouts -/
/-
**CategoryTheory.Limits.hasPushouts_of_hasColimit_span** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasPushouts_of_hasColimit_span [forall {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
, HasColimit (span f g)] : HasPushouts C
参数：span f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G

--- 原说明 ---
If `C` has all colimits of diagrams `span f g`, then it has all pushouts
-/
theorem hasPushouts_of_hasColimit_span
    [∀ {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, HasColimit (span f g)] : HasPushouts C :=
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoSpan F) }

/-- The duality equivalence `WalkingSpanᵒᵖ ≌ WalkingCospan` -/
@[simps!]
/-
**CategoryTheory.Limits.walkingSpanOpEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：walkingSpanOpEquiv : WalkingSpanᵒᵖ ≌ WalkingCospan
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The duality equivalence `WalkingSpanᵒᵖ ≌ WalkingCospan`
-/
def walkingSpanOpEquiv : WalkingSpanᵒᵖ ≌ WalkingCospan :=
  widePushoutShapeOpEquiv _

/-- The duality equivalence `WalkingCospanᵒᵖ ≌ WalkingSpan` -/
@[simps!]
/-
**CategoryTheory.Limits.walkingCospanOpEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：walkingCospanOpEquiv : WalkingCospanᵒᵖ ≌ WalkingSpan
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The duality equivalence `WalkingCospanᵒᵖ ≌ WalkingSpan`
-/
def walkingCospanOpEquiv : WalkingCospanᵒᵖ ≌ WalkingSpan :=
  widePullbackShapeOpEquiv _

-- see Note [lower instance priority]
/-- Having wide pullback at any universe level implies having binary pullbacks. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Having wide pullback at any universe level implies having binary pullbacks.
-/
instance (priority := 100) hasPullbacks_of_hasWidePullbacks (D : Type u) [Category.{v} D]
    [HasWidePullbacks.{w} D] : HasPullbacks.{v, u} D :=
  hasWidePullbacks_shrink WalkingPair

-- see Note [lower instance priority]
/-- Having wide pushout at any universe level implies having binary pushouts. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Having wide pushout at any universe level implies having binary pushouts.
-/
instance (priority := 100) hasPushouts_of_hasWidePushouts (D : Type u) [Category.{v} D]
    [HasWidePushouts.{w} D] : HasPushouts.{v, u} D :=
  hasWidePushouts_shrink WalkingPair
/-
**CategoryTheory.Limits.hasPullback_symmetry_of_hasPullbacksAlong** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasPullback_symmetry_of_hasPullbacksAlong {S X Y : C} {f : X ⟶ S} [HasPull
backsAlong f] {g : Y ⟶ S} : HasPullback f g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
-/
theorem hasPullback_symmetry_of_hasPullbacksAlong {S X Y : C} {f : X ⟶ S} [HasPullbacksAlong f]
    {g : Y ⟶ S} : HasPullback f g :=
  hasPullback_symmetry g f
/-
**CategoryTheory.Limits.hasPushouts_symmetry_of_hasPushoutsAlong** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasPushouts_symmetry_of_hasPushoutsAlong {S X Y : C} {f : S ⟶ X} [HasPusho
utsAlong f] {g : S ⟶ Y} : HasPushout f g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
-/
theorem hasPushouts_symmetry_of_hasPushoutsAlong {S X Y : C} {f : S ⟶ X} [HasPushoutsAlong f]
    {g : S ⟶ Y} : HasPushout f g :=
  hasPushout_symmetry g f

section Products

variable {C}

set_option backward.isDefEq.respectTransparency false in
/-- `X ×[Y] (Y ⨯ Z) ≅ X ⨯ Z` -/
/-
**CategoryTheory.Limits.pullbackProdFstIsoProd** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：pullbackProdFstIsoProd {X Y : C} (f : X ⟶ Y) (Z : C) [HasBinaryProduct Y Z
] [HasBinaryProduct X Z] [HasPullback f (prod.fst : Y ⨯ Z ⟶ _)] : pullback f (pr
od.fst : Y ⨯ Z ⟶ _) ≅ X ⨯ Z where hom
参数：f : X ⟶ Y；Z : C；prod.fst : Y ⨯ Z ⟶ _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X ×[Y] (Y ⨯ Z) ≅ X ⨯ Z`
-/
noncomputable def pullbackProdFstIsoProd {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryProduct Y Z] [HasBinaryProduct X Z] [HasPullback f (prod.fst : Y ⨯ Z ⟶ _)] :
    pullback f (prod.fst : Y ⨯ Z ⟶ _) ≅ X ⨯ Z where
  hom := prod.lift (pullback.fst _ _) (pullback.snd _ _ ≫ prod.snd)
  inv := pullback.lift prod.fst (prod.map f (𝟙 Z))
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · apply prod.hom_ext <;> simp [pullback.condition]

section

variable {X Y : C} (f : X ⟶ Y) (Z : C) [HasBinaryProduct Y Z] [HasBinaryProduct X Z]
  [HasPullback f (prod.fst : Y ⨯ Z ⟶ _)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackProdFstIsoProd_hom_fst** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pullbackProdFstIsoProd_hom_fst : (pullbackProdFstIsoProd f Z).hom ≫ prod.f
st = pullback.fst _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackProdFstIsoProd_hom_fst :
    (pullbackProdFstIsoProd f Z).hom ≫ prod.fst = pullback.fst _ _ := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackProdFstIsoProd_hom_snd** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pullbackProdFstIsoProd_hom_snd : (pullbackProdFstIsoProd f Z).hom ≫ prod.s
nd = pullback.snd _ _ ≫ prod.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackProdFstIsoProd_hom_snd :
    (pullbackProdFstIsoProd f Z).hom ≫ prod.snd = pullback.snd _ _ ≫ prod.snd := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackProdFstIsoProd_inv_fst** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pullbackProdFstIsoProd_inv_fst : (pullbackProdFstIsoProd f Z).inv ≫ pullba
ck.fst _ _ = prod.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackProdFstIsoProd_inv_fst :
    (pullbackProdFstIsoProd f Z).inv ≫ pullback.fst _ _ = prod.fst := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackProdFstIsoProd_inv_snd_fst** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackProdFstIsoProd_inv_snd_fst : (pullbackProdFstIsoProd f Z).inv ≫ pu
llback.snd _ _ ≫ prod.fst = prod.fst ≫ f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackProdFstIsoProd_inv_snd_fst :
    (pullbackProdFstIsoProd f Z).inv ≫ pullback.snd _ _ ≫ prod.fst = prod.fst ≫ f := by
  simp [pullbackProdFstIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackProdFstIsoProd_inv_snd_snd** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackProdFstIsoProd_inv_snd_snd : (pullbackProdFstIsoProd f Z).inv ≫ pu
llback.snd _ _ ≫ prod.snd = prod.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackProdFstIsoProd_inv_snd_snd :
    (pullbackProdFstIsoProd f Z).inv ≫ pullback.snd _ _ ≫ prod.snd = prod.snd := by
  simp [pullbackProdFstIsoProd]

end

section

set_option backward.isDefEq.respectTransparency false in
/-- `(Z ⨯ Y) ×[Y] X ≅ Z ⨯ X` -/
/-
**CategoryTheory.Limits.pullbackProdSndIsoProd** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：pullbackProdSndIsoProd {X Y : C} (f : X ⟶ Y) (Z : C) [HasBinaryProduct Z Y
] [HasBinaryProduct Z X] [HasPullback (prod.snd : Z ⨯ Y ⟶ Y) f] : pullback (prod
.snd : Z ⨯ Y ⟶ Y) f ≅ Z ⨯ X where hom
参数：f : X ⟶ Y；Z : C；prod.snd : Z ⨯ Y ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(Z ⨯ Y) ×[Y] X ≅ Z ⨯ X`
-/
noncomputable def pullbackProdSndIsoProd {X Y : C} (f : X ⟶ Y) (Z : C)
    [HasBinaryProduct Z Y] [HasBinaryProduct Z X] [HasPullback (prod.snd : Z ⨯ Y ⟶ Y) f] :
    pullback (prod.snd : Z ⨯ Y ⟶ Y) f ≅ Z ⨯ X where
  hom := prod.lift (pullback.fst _ _ ≫ prod.fst) (pullback.snd _ _)
  inv := pullback.lift (prod.map (𝟙 Z) f) prod.snd
  hom_inv_id := by
    apply pullback.hom_ext
    · apply prod.hom_ext <;> simp [pullback.condition]
    · simp

variable {X Y : C} (f : X ⟶ Y) (Z : C) [HasBinaryProduct Z Y] [HasBinaryProduct Z X]
  [HasPullback (prod.snd : Z ⨯ Y ⟶ Y) f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackProdSndIsoProd_hom_fst** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pullbackProdSndIsoProd_hom_fst : (pullbackProdSndIsoProd f Z).hom ≫ prod.f
st = pullback.fst _ _ ≫ prod.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackProdSndIsoProd_hom_fst :
    (pullbackProdSndIsoProd f Z).hom ≫ prod.fst = pullback.fst _ _ ≫ prod.fst := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackProdSndIsoProd_hom_snd** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pullbackProdSndIsoProd_hom_snd : (pullbackProdSndIsoProd f Z).hom ≫ prod.s
nd = pullback.snd _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackProdSndIsoProd_hom_snd :
    (pullbackProdSndIsoProd f Z).hom ≫ prod.snd = pullback.snd _ _ := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackProdSndIsoProd_inv_fst_fst** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackProdSndIsoProd_inv_fst_fst : (pullbackProdSndIsoProd f Z).inv ≫ pu
llback.fst _ _ ≫ prod.fst = prod.fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackProdSndIsoProd_inv_fst_fst :
    (pullbackProdSndIsoProd f Z).inv ≫ pullback.fst _ _ ≫ prod.fst = prod.fst := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackProdSndIsoProd_inv_fst_snd** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackProdSndIsoProd_inv_fst_snd : (pullbackProdSndIsoProd f Z).inv ≫ pu
llback.fst _ _ ≫ prod.snd = prod.snd ≫ f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.prod.map_snd`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackProdSndIsoProd_inv_fst_snd :
    (pullbackProdSndIsoProd f Z).inv ≫ pullback.fst _ _ ≫ prod.snd = prod.snd ≫ f := by
  simp [pullbackProdSndIsoProd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackProdSndIsoProd_inv_snd** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pullbackProdSndIsoProd_inv_snd : (pullbackProdSndIsoProd f Z).inv ≫ pullba
ck.snd _ _ = prod.snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackProdSndIsoProd_inv_snd :
    (pullbackProdSndIsoProd f Z).inv ≫ pullback.snd _ _ = prod.snd := by
  simp [pullbackProdSndIsoProd]

end

end Products

end CategoryTheory.Limits

