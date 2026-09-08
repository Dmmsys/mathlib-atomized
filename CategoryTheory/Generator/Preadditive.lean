/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Separators in preadditive categories

This file contains characterizations of separating sets and objects that are valid in all
preadditive categories.

-/

public section


universe v u

open CategoryTheory Opposite ObjectProperty

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-
**CategoryTheory.Preadditive.isSeparating_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Preadditive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   (P : CategoryTheory.ObjectProperty C),   P.IsSeparating
 ↔     ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G : C), P G → ∀ (h : G ⟶ X), CategoryTheory.
CategoryStruct.comp h f = 0) → f = 0
参数：P : CategoryTheory.ObjectProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
-/
theorem Preadditive.isSeparating_iff (P : ObjectProperty C) :
    P.IsSeparating ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G : C) (_ : P G), ∀ (h : G ⟶ X), h ≫ f = 0) → f = 0 :=
  ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [Limits.comp_zero] using hf), fun h𝒢 X Y f g hfg =>
    sub_eq_zero.1 <| h𝒢 _ (by simpa only [Preadditive.comp_sub, sub_eq_zero] using hfg)⟩
/-
**CategoryTheory.Preadditive.isCoseparating_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Preadditive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C]   (P : CategoryTheory.ObjectProperty C),   P.IsCoseparati
ng ↔     ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G : C), P G → ∀ (h : Y ⟶ G), CategoryTheor
y.CategoryStruct.comp f h = 0) → f = 0
参数：P : CategoryTheory.ObjectProperty C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
-/
theorem Preadditive.isCoseparating_iff (P : ObjectProperty C) :
    P.IsCoseparating ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G : C) (_ : P G), ∀ (h : Y ⟶ G), f ≫ h = 0) → f = 0 :=
  ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [Limits.zero_comp] using hf), fun h𝒢 X Y f g hfg =>
    sub_eq_zero.1 <| h𝒢 _ (by simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)⟩
/-
**CategoryTheory.Preadditive.isSeparator_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Preadditive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] (G : C),   CategoryTheory.IsSeparator G ↔     ∀ ⦃X Y : C⦄
 (f : X ⟶ Y), (∀ (h : G ⟶ X), CategoryTheory.CategoryStruct.comp h f = 0) → f = 
0
参数：G : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSeparator.def`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {G : C},   CategoryTheory.IsSeparator G →     ∀ ⦃X Y : C⦄ (f
 g : X ⟶ Y),       (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isSeparator_def`：isSeparator_def (G : C) : IsSeparator G 
↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : G ⟶ X, h ≫ f = h ≫ g) -> f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
-/
theorem Preadditive.isSeparator_iff (G : C) :
    IsSeparator G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = 0) → f = 0 :=
  ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [Limits.comp_zero] using hf), fun hG =>
    (isSeparator_def _).2 fun X Y f g hfg =>
      sub_eq_zero.1 <| hG _ (by simpa only [Preadditive.comp_sub, sub_eq_zero] using hfg)⟩
/-
**CategoryTheory.Preadditive.isCoseparator_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Preadditive`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Preadditive C] (G : C),   CategoryTheory.IsCoseparator G ↔     ∀ ⦃X Y : 
C⦄ (f : X ⟶ Y), (∀ (h : Y ⟶ G), CategoryTheory.CategoryStruct.comp f h = 0) → f 
= 0
参数：G : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCoseparator.def`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {G : C},   CategoryTheory.IsCoseparator G →     ∀ ⦃X Y : C
⦄ (f g : X ⟶ Y),      …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isCoseparator_def`：isCoseparator_def (G : C) : IsCosepara
tor G ↔ forall ⦃X Y : C⦄ (f g : X ⟶ Y), (forall h : Y ⟶ G, f ≫ h = g ≫ h) -> f =
 g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
-/
theorem Preadditive.isCoseparator_iff (G : C) :
    IsCoseparator G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = 0) → f = 0 :=
  ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [Limits.zero_comp] using hf), fun hG =>
    (isCoseparator_def _).2 fun X Y f g hfg =>
      sub_eq_zero.1 <| hG _ (by simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)⟩
/-
**CategoryTheory.isSeparator_iff_faithful_preadditiveCoyoneda** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory`。
形式化陈述：isSeparator_iff_faithful_preadditiveCoyoneda (G : C) : IsSeparator G ↔ (pr
eadditiveCoyoneda.obj (op G)).Faithful
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isSeparator_iff_faithful_coyoneda_obj`：isSeparator_iff_fa
ithful_coyoneda_obj (G : C) : IsSeparator G ↔ (coyoneda.obj (op G)).Faithful
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.whiskering_preadditiveCoyoneda`：whiskering_preadditiveCoy
oneda : preadditiveCoyoneda ⋙ (whiskeringRight C AddCommGrpCat (Type v)).obj (fo
rget AddCommGrpCat) = coyoneda
· 使用定理 `CategoryTheory.Functor.comp_obj`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.whiskeringRight_obj_obj`：∀ (C : Type u₁) [inst : 
CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (E : Type u₃) [ins…
· 使用定理 `CategoryTheory.Functor.Faithful.of_comp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.Faithful.comp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
-/
theorem isSeparator_iff_faithful_preadditiveCoyoneda (G : C) :
    IsSeparator G ↔ (preadditiveCoyoneda.obj (op G)).Faithful := by
  rw [isSeparator_iff_faithful_coyoneda_obj, ← whiskering_preadditiveCoyoneda, Functor.comp_obj,
    Functor.whiskeringRight_obj_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget AddCommGrpCat),
    fun h => Functor.Faithful.comp _ _⟩
/-
**CategoryTheory.isSeparator_iff_faithful_preadditiveCoyonedaObj** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isSeparator_iff_faithful_preadditiveCoyonedaObj (G : C) : IsSeparator G ↔ 
(preadditiveCoyonedaObj G).Faithful
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isSeparator_iff_faithful_preadditiveCoyoneda`：isSeparator
_iff_faithful_preadditiveCoyoneda (G : C) : IsSeparator G ↔ (preadditiveCoyoneda
.obj (op G)).Faithful
· 使用定理 `CategoryTheory.preadditiveCoyoneda_obj`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (X : Cᵒᵖ),   Ca
tegoryTheory.preadditiveCoyo…
· 使用定理 `CategoryTheory.Functor.Faithful.of_comp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.Faithful.comp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {E : Type u₃} [ins…
-/
theorem isSeparator_iff_faithful_preadditiveCoyonedaObj (G : C) :
    IsSeparator G ↔ (preadditiveCoyonedaObj G).Faithful := by
  rw [isSeparator_iff_faithful_preadditiveCoyoneda, preadditiveCoyoneda_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget₂ _ AddCommGrpCat.{v}),
    fun h => Functor.Faithful.comp _ _⟩
/-
**CategoryTheory.isCoseparator_iff_faithful_preadditiveYoneda** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory`。
形式化陈述：isCoseparator_iff_faithful_preadditiveYoneda (G : C) : IsCoseparator G ↔ (
preadditiveYoneda.obj G).Faithful
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isCoseparator_iff_faithful_yoneda_obj`：isCoseparator_iff_
faithful_yoneda_obj (G : C) : IsCoseparator G ↔ (yoneda.obj G).Faithful
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.whiskering_preadditiveYoneda`：whiskering_preadditiveYoned
a : preadditiveYoneda ⋙ (whiskeringRight Cᵒᵖ AddCommGrpCat (Type v)).obj (forget
 AddCommGrpCat) = yoneda
· 使用定理 `CategoryTheory.Functor.comp_obj`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.whiskeringRight_obj_obj`：∀ (C : Type u₁) [inst : 
CategoryTheory.Category.{v₁, u₁} C] (D : Type u₂) [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (E : Type u₃) [ins…
· 使用定理 `CategoryTheory.Functor.Faithful.of_comp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.Faithful.comp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
-/
theorem isCoseparator_iff_faithful_preadditiveYoneda (G : C) :
    IsCoseparator G ↔ (preadditiveYoneda.obj G).Faithful := by
  rw [isCoseparator_iff_faithful_yoneda_obj, ← whiskering_preadditiveYoneda, Functor.comp_obj,
    Functor.whiskeringRight_obj_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget AddCommGrpCat),
    fun h => Functor.Faithful.comp _ _⟩
/-
**CategoryTheory.isCoseparator_iff_faithful_preadditiveYonedaObj** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isCoseparator_iff_faithful_preadditiveYonedaObj (G : C) : IsCoseparator G 
↔ (preadditiveYonedaObj G).Faithful
参数：G : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.isCoseparator_iff_faithful_preadditiveYoneda`：isCoseparat
or_iff_faithful_preadditiveYoneda (G : C) : IsCoseparator G ↔ (preadditiveYoneda
.obj G).Faithful
· 使用定理 `CategoryTheory.preadditiveYoneda_obj`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (Y : C),   Catego
ryTheory.preadditiveYoneda…
· 使用定理 `CategoryTheory.Functor.Faithful.of_comp`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.Faithful.comp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} D]   {E : Type u₃} [ins…
-/
theorem isCoseparator_iff_faithful_preadditiveYonedaObj (G : C) :
    IsCoseparator G ↔ (preadditiveYonedaObj G).Faithful := by
  rw [isCoseparator_iff_faithful_preadditiveYoneda, preadditiveYoneda_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget₂ _ AddCommGrpCat.{v}),
    fun h => Functor.Faithful.comp _ _⟩

end CategoryTheory

