/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Pullbacks and pushouts in a monoidal category

For numerous simp lemmas of the form `f ≫ g = h`, we add accompanying simp lemmas of the form
`Q ◁ f ≫ Q ◁ g = Q ◁ h` and `f ▷ Q ≫ g ▷ Q = h ▷ Q`. This file and
`Mathlib.CategoryTheory.Monoidal.Limits.HasLimits` are needed to define a monoidal category
structure in `Mathlib.CategoryTheory.Monoidal.Arrow`.

## TODO
An attribute should be developed to automatically generate lemmas of this form.
-/

public section

universe v u

namespace CategoryTheory.MonoidalCategory

open Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace IsPushout

variable {Z X Y P W : C} {f : Z ⟶ X} {g : Z ⟶ Y}
    {inl : X ⟶ P} {inr : Y ⟶ P} (hP : IsPushout f g inl inr)
    {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k)

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.whiskerLeft_inl_desc** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：whiskerLeft_inl_desc {Q : C} : Q ◁ inl ≫ Q ◁ hP.desc h k w = Q ◁ h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用引理 `CategoryTheory.IsPushout.inl_desc`：inl_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
-/
lemma whiskerLeft_inl_desc {Q : C} :
    Q ◁ inl ≫ Q ◁ hP.desc h k w = Q ◁ h := by
  rw [← MonoidalCategory.whiskerLeft_comp, IsPushout.inl_desc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.whiskerLeft_inr_desc** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：whiskerLeft_inr_desc {Q : C} : Q ◁ inr ≫ Q ◁ hP.desc h k w = Q ◁ k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
· 使用引理 `CategoryTheory.IsPushout.inr_desc`：inr_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k
-/
lemma whiskerLeft_inr_desc {Q : C} :
    Q ◁ inr ≫ Q ◁ hP.desc h k w = Q ◁ k := by
  rw [← MonoidalCategory.whiskerLeft_comp, IsPushout.inr_desc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.inl_desc_whiskerRight** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：inl_desc_whiskerRight {Q : C} : inl ▷ Q ≫ hP.desc h k w ▷ Q = h ▷ Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用引理 `CategoryTheory.IsPushout.inl_desc`：inl_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inl ≫ hP.desc h k w = h
-/
lemma inl_desc_whiskerRight {Q : C} :
    inl ▷ Q ≫ hP.desc h k w ▷ Q = h ▷ Q := by
  rw [← comp_whiskerRight, IsPushout.inl_desc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.inr_desc_whiskerRight** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：inr_desc_whiskerRight {Q : C} : inr ▷ Q ≫ hP.desc h k w ▷ Q = k ▷ Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight`：comp_whiskerRight {W 
X Y : C} (f : W ⟶ X) (g : X ⟶ Y) (Z : C) : (f ≫ g) ▷ Z = f ▷ Z ≫ g ▷ Z
· 使用引理 `CategoryTheory.IsPushout.inr_desc`：inr_desc (hP : IsPushout f g inl inr)
 {W : C} (h : X ⟶ W) (k : Y ⟶ W) (w : f ≫ h = g ≫ k) : inr ≫ hP.desc h k w = k
-/
lemma inr_desc_whiskerRight {Q : C} :
    inr ▷ Q ≫ hP.desc h k w ▷ Q = k ▷ Q := by
  rw [← comp_whiskerRight, IsPushout.inr_desc]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.IsPushout.whiskerLeft_w** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：whiskerLeft_w (hP : IsPushout f g inl inr) {Q : C} : Q ◁ f ≫ Q ◁ inl = Q ◁
 g ≫ Q ◁ inr
参数：hP : IsPushout f g inl inr。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_w (hP : IsPushout f g inl inr) {Q : C} :
    Q ◁ f ≫ Q ◁ inl = Q ◁ g ≫ Q ◁ inr := by
  simp [← MonoidalCategory.whiskerLeft_comp, hP.w]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.IsPushout.w_whiskerRight** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：w_whiskerRight (hP : IsPushout f g inl inr) {Q : C} : f ▷ Q ≫ inl ▷ Q = g 
▷ Q ≫ inr ▷ Q
参数：hP : IsPushout f g inl inr。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma w_whiskerRight (hP : IsPushout f g inl inr) {Q : C} :
    f ▷ Q ≫ inl ▷ Q = g ▷ Q ≫ inr ▷ Q := by
  simp [← MonoidalCategory.comp_whiskerRight, hP.w]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.whiskerLeft_inl_isoPushout_inv** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：whiskerLeft_inl_isoPushout_inv [HasPushout f g] {Q : C} : Q ◁ pushout.inl 
_ _ ≫ Q ◁ hP.isoPushout.inv = Q ◁ inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_inv`：inl_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inl _ _ ≫ h.isoPushout.inv = inl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_inl_isoPushout_inv [HasPushout f g] {Q : C} :
    Q ◁ pushout.inl _ _ ≫ Q ◁ hP.isoPushout.inv = Q ◁ inl := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.whiskerLeft_inr_isoPushout_inv** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：whiskerLeft_inr_isoPushout_inv [HasPushout f g] {Q : C} : Q ◁ pushout.inr 
_ _ ≫ Q ◁ hP.isoPushout.inv = Q ◁ inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.inr_isoPushout_inv`：inr_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inr _ _ ≫ h.isoPushout.inv = inr
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_inr_isoPushout_inv [HasPushout f g] {Q : C} :
    Q ◁ pushout.inr _ _ ≫ Q ◁ hP.isoPushout.inv = Q ◁ inr := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.whiskerLeft_inl_isoPushout_hom** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：whiskerLeft_inl_isoPushout_hom [HasPushout f g] {Q : C} : Q ◁ inl ≫ Q ◁ hP
.isoPushout.hom = Q ◁ pushout.inl _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_hom`：inl_isoPushout_hom (h : IsP
ushout f g inl inr) [HasPushout f g] : inl ≫ h.isoPushout.hom = pushout.inl _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_inl_isoPushout_hom [HasPushout f g] {Q : C} :
    Q ◁ inl ≫ Q ◁ hP.isoPushout.hom = Q ◁ pushout.inl _ _ := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.whiskerLeft_inr_isoPushout_hom** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：whiskerLeft_inr_isoPushout_hom [HasPushout f g] {Q : C} : Q ◁ inr ≫ Q ◁ hP
.isoPushout.hom = Q ◁ pushout.inr _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.inr_isoPushout_hom`：inr_isoPushout_hom (h : IsP
ushout f g inl inr) [HasPushout f g] : inr ≫ h.isoPushout.hom = pushout.inr _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_inr_isoPushout_hom [HasPushout f g] {Q : C} :
    Q ◁ inr ≫ Q ◁ hP.isoPushout.hom = Q ◁ pushout.inr _ _ := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.inl_isoPushout_inv_whiskerRight** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：inl_isoPushout_inv_whiskerRight [HasPushout f g] {Q : C} : pushout.inl _ _
 ▷ Q ≫ hP.isoPushout.inv ▷ Q = inl ▷ Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_inv`：inl_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inl _ _ ≫ h.isoPushout.inv = inl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_isoPushout_inv_whiskerRight [HasPushout f g] {Q : C} :
    pushout.inl _ _ ▷ Q ≫ hP.isoPushout.inv ▷ Q = inl ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.inr_isoPushout_inv_whiskerRight** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：inr_isoPushout_inv_whiskerRight [HasPushout f g] {Q : C} : pushout.inr _ _
 ▷ Q ≫ hP.isoPushout.inv ▷ Q = inr ▷ Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsPushout.inr_isoPushout_inv`：inr_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inr _ _ ≫ h.isoPushout.inv = inr
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_isoPushout_inv_whiskerRight [HasPushout f g] {Q : C} :
    pushout.inr _ _ ▷ Q ≫ hP.isoPushout.inv ▷ Q = inr ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.inl_isoPushout_hom_whiskerRight** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：inl_isoPushout_hom_whiskerRight [HasPushout f g] {Q : C} : inl ▷ Q ≫ hP.is
oPushout.hom ▷ Q = pushout.inl _ _ ▷ Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_hom`：inl_isoPushout_hom (h : IsP
ushout f g inl inr) [HasPushout f g] : inl ≫ h.isoPushout.hom = pushout.inl _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_isoPushout_hom_whiskerRight [HasPushout f g] {Q : C} :
    inl ▷ Q ≫ hP.isoPushout.hom ▷ Q = pushout.inl _ _ ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.IsPushout.inr_isoPushout_hom_whiskerRight** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.IsPushout`。
形式化陈述：inr_isoPushout_hom_whiskerRight [HasPushout f g] {Q : C} : inr ▷ Q ≫ hP.is
oPushout.hom ▷ Q = pushout.inr _ _ ▷ Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsPushout.inr_isoPushout_hom`：inr_isoPushout_hom (h : IsP
ushout f g inl inr) [HasPushout f g] : inr ≫ h.isoPushout.hom = pushout.inr _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_isoPushout_hom_whiskerRight [HasPushout f g] {Q : C} :
    inr ▷ Q ≫ hP.isoPushout.hom ▷ Q = pushout.inr _ _ ▷ Q := by
  simp [← comp_whiskerRight]

end IsPushout

section Pushout

variable [HasPushouts C]
  {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
  (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) {Q : C}

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.Limits.pushout.whiskerLeft_condition** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasPushouts C] {X 
Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {Q : C},   CategoryTheory.CategoryStruct.comp (
CategoryTheory.MonoidalCategoryStruct.whiskerLeft Q f)       (CategoryTheory.Mon
oidalCategoryStruct.whiskerLeft Q (CategoryTheory.Limits.pushout.inl f g)) =    
 CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.whisk
erLeft Q g)       (CategoryTheory.MonoidalCategoryStruct.whiskerLeft Q (Category
Theory.Limits.pushout.inr f g))
参数：CategoryTheory.MonoidalCategoryStruct.whiskerLeft Q f；CategoryTheory.Monoidal
CategoryStruct.whiskerLeft Q (CategoryTheory.Limits.pushout.inl f g)；CategoryThe
ory.MonoidalCategoryStruct.whiskerLeft Q g；CategoryTheory.MonoidalCategoryStruct
.whiskerLeft Q (CategoryTheory.Limits.pushout.inr f g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Limits.pushout.whiskerLeft_condition :
    Q ◁ f ≫ Q ◁ pushout.inl f g = Q ◁ g ≫ Q ◁ pushout.inr f g := by
  simp [← MonoidalCategory.whiskerLeft_comp, pushout.condition]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.Limits.pushout.condition_whiskerRight** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.Limits.pushout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasPushouts C] {X 
Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {Q : C},   CategoryTheory.CategoryStruct.comp (
CategoryTheory.MonoidalCategoryStruct.whiskerRight f Q)       (CategoryTheory.Mo
noidalCategoryStruct.whiskerRight (CategoryTheory.Limits.pushout.inl f g) Q) =  
   CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.whi
skerRight g Q)       (CategoryTheory.MonoidalCategoryStruct.whiskerRight (Catego
ryTheory.Limits.pushout.inr f g) Q)
参数：CategoryTheory.MonoidalCategoryStruct.whiskerRight f Q；CategoryTheory.Monoida
lCategoryStruct.whiskerRight (CategoryTheory.Limits.pushout.inl f g) Q；CategoryT
heory.MonoidalCategoryStruct.whiskerRight g Q；CategoryTheory.MonoidalCategoryStr
uct.whiskerRight (CategoryTheory.Limits.pushout.inr f g) Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Limits.pushout.condition_whiskerRight :
    f ▷ Q ≫ pushout.inl f g ▷ Q = g ▷ Q ≫ pushout.inr f g ▷ Q := by
  simp [← comp_whiskerRight, pushout.condition]

variable {A B X Y Z W : C} {f : A ⟶ B} {g : X ⟶ Y}

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.Limits.pushout.associator_naturality_left_cond
ition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.Limits.pushout`
。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasPushouts C] {A 
B X Y Z W : C} {f : A ⟶ B} {g : X ⟶ Y}   {h : CategoryTheory.MonoidalCategoryStr
uct.tensorObj Z W ⟶ X},   CategoryTheory.CategoryStruct.comp       (CategoryTheo
ry.MonoidalCategoryStruct.whiskerRight (CategoryTheory.MonoidalCategoryStruct.wh
iskerRight f Z) W)       (CategoryTheory.CategoryStruct.comp (CategoryTheory.Mon
oidalCategoryStruct.associator B Z W).hom         (CategoryTheory.CategoryStruct
.comp (CategoryTheory.MonoidalCategoryStruct.whiskerLeft B h)           (Categor
yTheory.Limits.pushout.inl (CategoryTheory.MonoidalCategoryStruct.whiskerRight f
 X)             (CategoryTheory.MonoidalCategoryStruct.whiskerLeft A g)))) =    
 CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.assoc
iator A Z W).hom       (CategoryTheory.CategoryStruct.comp         (CategoryTheo
ry.MonoidalCategoryStruct.whiskerLeft A (CategoryTheory.CategoryStruct.comp h g)
)         (CategoryTheory.Limits.pushout.inr (CategoryTheory.MonoidalCategoryStr
uct.whiskerRight f X)           (CategoryTheory.MonoidalCategoryStruct.whiskerLe
ft A g)))
参数：CategoryTheory.MonoidalCategoryStruct.whiskerRight (CategoryTheory.MonoidalCa
tegoryStruct.whiskerRight f Z) W；CategoryTheory.CategoryStruct.comp (CategoryThe
ory.MonoidalCategoryStruct.associator B Z W).hom         (CategoryTheory.Categor
yStruct.comp (CategoryTheory.MonoidalCategoryStruct.whiskerLeft B h)           (
CategoryTheory.Limits.pushout.inl (CategoryTheory.MonoidalCategoryStruct.whisker
Right f X)             (CategoryTheory.MonoidalCategoryStruct.whiskerLeft A g)))
；CategoryTheory.MonoidalCategoryStruct.associator A Z W；CategoryTheory.CategoryS
truct.comp         (CategoryTheory.MonoidalCategoryStruct.whiskerLeft A (Categor
yTheory.CategoryStruct.comp h g))         (CategoryTheory.Limits.pushout.inr (Ca
tegoryTheory.MonoidalCategoryStruct.whiskerRight f X)           (CategoryTheory.
MonoidalCategoryStruct.whiskerLeft A g))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.associator_naturality_left_assoc`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Mono
idalCategory C] {X X' : C}   (f : X ⟶ X') (Y Z : C) {Z…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
-/
lemma Limits.pushout.associator_naturality_left_condition {h : Z ⊗ W ⟶ X} :
    f ▷ Z ▷ W ≫ (α_ B Z W).hom ≫ B ◁ h ≫ pushout.inl (f ▷ X) (A ◁ g) =
      (α_ A Z W).hom ≫ A ◁ (h ≫ g) ≫ pushout.inr (f ▷ X) (A ◁ g) := by
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, pushout.condition,
    ← MonoidalCategory.whiskerLeft_comp_assoc]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.Limits.pushout.associator_inv_naturality_right
_condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.Limits.pus
hout`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasPushouts C] {A 
B X Y Z W : C} {f : A ⟶ B} {g : X ⟶ Y}   {h : CategoryTheory.MonoidalCategoryStr
uct.tensorObj Z W ⟶ A},   CategoryTheory.CategoryStruct.comp       (CategoryTheo
ry.MonoidalCategoryStruct.whiskerLeft Z (CategoryTheory.MonoidalCategoryStruct.w
hiskerLeft W g))       (CategoryTheory.CategoryStruct.comp (CategoryTheory.Monoi
dalCategoryStruct.associator Z W Y).inv         (CategoryTheory.CategoryStruct.c
omp (CategoryTheory.MonoidalCategoryStruct.whiskerRight h Y)           (Category
Theory.Limits.pushout.inr (CategoryTheory.MonoidalCategoryStruct.whiskerRight f 
X)             (CategoryTheory.MonoidalCategoryStruct.whiskerLeft A g)))) =     
CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.associ
ator Z W X).inv       (CategoryTheory.CategoryStruct.comp         (CategoryTheor
y.MonoidalCategoryStruct.whiskerRight (CategoryTheory.CategoryStruct.comp h f) X
)         (CategoryTheory.Limits.pushout.inl (CategoryTheory.MonoidalCategoryStr
uct.whiskerRight f X)           (CategoryTheory.MonoidalCategoryStruct.whiskerLe
ft A g)))
参数：CategoryTheory.MonoidalCategoryStruct.whiskerLeft Z (CategoryTheory.MonoidalC
ategoryStruct.whiskerLeft W g)；CategoryTheory.CategoryStruct.comp (CategoryTheor
y.MonoidalCategoryStruct.associator Z W Y).inv         (CategoryTheory.CategoryS
truct.comp (CategoryTheory.MonoidalCategoryStruct.whiskerRight h Y)           (C
ategoryTheory.Limits.pushout.inr (CategoryTheory.MonoidalCategoryStruct.whiskerR
ight f X)             (CategoryTheory.MonoidalCategoryStruct.whiskerLeft A g)))；
CategoryTheory.MonoidalCategoryStruct.associator Z W X；CategoryTheory.CategorySt
ruct.comp         (CategoryTheory.MonoidalCategoryStruct.whiskerRight (CategoryT
heory.CategoryStruct.comp h f) X)         (CategoryTheory.Limits.pushout.inl (Ca
tegoryTheory.MonoidalCategoryStruct.whiskerRight f X)           (CategoryTheory.
MonoidalCategoryStruct.whiskerLeft A g))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_right_assoc`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.MonoidalCategory C] (X Y : C)   {Z Z' : C} (f : Z ⟶ Z') {Z…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
-/
lemma Limits.pushout.associator_inv_naturality_right_condition {h : Z ⊗ W ⟶ A} :
    Z ◁ W ◁ g ≫ (α_ Z W Y).inv ≫ h ▷ Y ≫ pushout.inr (f ▷ X) (A ◁ g) =
      (α_ Z W X).inv ≫ (h ≫ f) ▷ X ≫ pushout.inl (f ▷ X) (A ◁ g) := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, ← pushout.condition,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.Limits.whiskerLeft_inl_comp_pushoutSymmetry_ho
m** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.Limits`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasPushouts C] {Q 
X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z),   CategoryTheory.CategoryStruct.comp       (
CategoryTheory.MonoidalCategoryStruct.whiskerLeft Q (CategoryTheory.Limits.pusho
ut.inl f g))       (CategoryTheory.MonoidalCategoryStruct.whiskerLeft Q (Categor
yTheory.Limits.pushoutSymmetry f g).hom) =     CategoryTheory.MonoidalCategorySt
ruct.whiskerLeft Q (CategoryTheory.Limits.pushout.inr g f)
参数：f : X ⟶ Y；g : X ⟶ Z；CategoryTheory.MonoidalCategoryStruct.whiskerLeft Q (Cate
goryTheory.Limits.pushout.inl f g)；CategoryTheory.MonoidalCategoryStruct.whisker
Left Q (CategoryTheory.Limits.pushoutSymmetry f g).hom；CategoryTheory.Limits.pus
hout.inr g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom`：inl_comp_pushoutSymm
etry_hom [HasPushout f g] : pushout.inl _ _ ≫ (pushoutSymmetry f g).hom = pushou
t.inr _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Limits.whiskerLeft_inl_comp_pushoutSymmetry_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    Q ◁ pushout.inl f g ≫ Q ◁ (pushoutSymmetry f g).hom = Q ◁ pushout.inr g f := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.Limits.whiskerLeft_inr_comp_pushoutSymmetry_ho
m** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.Limits`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasPushouts C] {Q 
X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z),   CategoryTheory.CategoryStruct.comp       (
CategoryTheory.MonoidalCategoryStruct.whiskerLeft Q (CategoryTheory.Limits.pusho
ut.inr f g))       (CategoryTheory.MonoidalCategoryStruct.whiskerLeft Q (Categor
yTheory.Limits.pushoutSymmetry f g).hom) =     CategoryTheory.MonoidalCategorySt
ruct.whiskerLeft Q (CategoryTheory.Limits.pushout.inl g f)
参数：f : X ⟶ Y；g : X ⟶ Z；CategoryTheory.MonoidalCategoryStruct.whiskerLeft Q (Cate
goryTheory.Limits.pushout.inr f g)；CategoryTheory.MonoidalCategoryStruct.whisker
Left Q (CategoryTheory.Limits.pushoutSymmetry f g).hom；CategoryTheory.Limits.pus
hout.inl g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom`：inr_comp_pushoutSymm
etry_hom [HasPushout f g] : pushout.inr _ _ ≫ (pushoutSymmetry f g).hom = pushou
t.inl _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Limits.whiskerLeft_inr_comp_pushoutSymmetry_hom (f : X ⟶ Y) (g : X ⟶ Z) :
    Q ◁ pushout.inr f g ≫ Q ◁ (pushoutSymmetry f g).hom = Q ◁ pushout.inl g f := by
  simp [← MonoidalCategory.whiskerLeft_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.Limits.inl_comp_pushoutSymmetry_hom_whiskerRig
ht** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.Limits`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasPushouts C] {Q 
X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z),   CategoryTheory.CategoryStruct.comp       (
CategoryTheory.MonoidalCategoryStruct.whiskerRight (CategoryTheory.Limits.pushou
t.inl f g) Q)       (CategoryTheory.MonoidalCategoryStruct.whiskerRight (Categor
yTheory.Limits.pushoutSymmetry f g).hom Q) =     CategoryTheory.MonoidalCategory
Struct.whiskerRight (CategoryTheory.Limits.pushout.inr g f) Q
参数：f : X ⟶ Y；g : X ⟶ Z；CategoryTheory.MonoidalCategoryStruct.whiskerRight (Categ
oryTheory.Limits.pushout.inl f g) Q；CategoryTheory.MonoidalCategoryStruct.whiske
rRight (CategoryTheory.Limits.pushoutSymmetry f g).hom Q；CategoryTheory.Limits.p
ushout.inr g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom`：inl_comp_pushoutSymm
etry_hom [HasPushout f g] : pushout.inl _ _ ≫ (pushoutSymmetry f g).hom = pushou
t.inr _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Limits.inl_comp_pushoutSymmetry_hom_whiskerRight (f : X ⟶ Y) (g : X ⟶ Z) :
    pushout.inl f g ▷ Q ≫ (pushoutSymmetry f g).hom ▷ Q = pushout.inr g f ▷ Q := by
  simp [← comp_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.Limits.inr_comp_pushoutSymmetry_hom_whiskerRig
ht** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.Limits`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasPushouts C] {Q 
X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z),   CategoryTheory.CategoryStruct.comp       (
CategoryTheory.MonoidalCategoryStruct.whiskerRight (CategoryTheory.Limits.pushou
t.inr f g) Q)       (CategoryTheory.MonoidalCategoryStruct.whiskerRight (Categor
yTheory.Limits.pushoutSymmetry f g).hom Q) =     CategoryTheory.MonoidalCategory
Struct.whiskerRight (CategoryTheory.Limits.pushout.inl g f) Q
参数：f : X ⟶ Y；g : X ⟶ Z；CategoryTheory.MonoidalCategoryStruct.whiskerRight (Categ
oryTheory.Limits.pushout.inr f g) Q；CategoryTheory.MonoidalCategoryStruct.whiske
rRight (CategoryTheory.Limits.pushoutSymmetry f g).hom Q；CategoryTheory.Limits.p
ushout.inl g f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.hasPushout_symmetry`：hasPushout_symmetry [HasPusho
ut f g] : HasPushout g f
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom`：inr_comp_pushoutSymm
etry_hom [HasPushout f g] : pushout.inr _ _ ≫ (pushoutSymmetry f g).hom = pushou
t.inl _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Limits.inr_comp_pushoutSymmetry_hom_whiskerRight (f : X ⟶ Y) (g : X ⟶ Z) :
    pushout.inr f g ▷ Q ≫ (pushoutSymmetry f g).hom ▷ Q = pushout.inl g f ▷ Q := by
  simp [← comp_whiskerRight]

end Pushout

end CategoryTheory.MonoidalCategory

