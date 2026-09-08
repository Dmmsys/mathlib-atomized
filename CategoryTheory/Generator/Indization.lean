/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Preadditive.Indization

/-!
# Separating set in the category of ind-objects

We construct a separating set in the category of ind-objects and conclude that if `C` is small
and additive, then `Ind C` has a separator.

-/

public section

universe v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C]

/-
**CategoryTheory.Ind.isSeparating_range_yoneda** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Ind`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheor
y.ObjectProperty.ofObj CategoryTheory.Ind.yoneda.obj).IsSeparating
参数：CategoryTheory.ObjectProperty.ofObj CategoryTheory.Ind.yoneda.obj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.instHasFilteredColimitsInd`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C],   CategoryTheory.Limits.HasFilteredColimits (Catego
ryTheory.Ind C)
· 使用定理 `CategoryTheory.Limits.IndObjectPresentation.instIsFilteredI`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {A : CategoryTheory.Functor Cᵒᵖ (T
ype v)}   (P : CategoryTheory.Limits.IndObjectPre…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ind.isSeparating_range_yoneda :
    ObjectProperty.IsSeparating (.ofObj (Ind.yoneda : C ⥤ _).obj) := by
  refine fun X Y f g h => (cancel_epi (Ind.colimitPresentationCompYoneda X).hom).1 ?_
  exact colimit.hom_ext (fun i => by simp [← Category.assoc, h])

end

section

variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteColimits C]

/-
**CategoryTheory.Ind.isSeparator_range_yoneda** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Ind`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.SmallCategory C] [CategoryTheory.Pre
additive C]   [inst_2 : CategoryTheory.Limits.HasFiniteColimits C], CategoryTheo
ry.IsSeparator (∐ CategoryTheory.Ind.yoneda.obj)
参数：∐ CategoryTheory.Ind.yoneda.obj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsSeparating.isSeparator_coproduct`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.Limits.Has
ZeroMorphisms C] {β : Type w}   {f : β → C} [inst_2 : …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.instHasCoproductsIndOfHasFiniteCoproducts`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteCopro
ducts C],   CategoryTheory.Limits.HasCoproduct…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Ind.isSeparating_range_yoneda`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C],   (CategoryTheory.ObjectProperty.ofObj CategoryT
heory.Ind.yoneda.obj).IsSeparating
-/
theorem Ind.isSeparator_range_yoneda : IsSeparator (∐ (Ind.yoneda : C ⥤ _).obj) :=
  Ind.isSeparating_range_yoneda.isSeparator_coproduct

end

end CategoryTheory

