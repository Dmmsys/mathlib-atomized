/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Functor.Category

/-!
# Natural isomorphisms

For the most part, natural isomorphisms are just another sort of isomorphism.

We provide some special support for extracting components:
* if `α : F ≅ G`, then `α.app X : F.obj X ≅ G.obj X`,

and building natural isomorphisms from components:
* ```
  NatIso.ofComponents
    (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f) :
  F ≅ G
  ```
  only needing to check naturality in one direction.

## Implementation

Note that `NatIso` is a namespace without a corresponding definition;
we put some declarations that are specifically about natural isomorphisms in the `Iso`
namespace so that they are available using dot notation.
-/

@[expose] public section

set_option mathlib.tactic.category.grind true

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

namespace Iso

/-- The application of a natural isomorphism to an object. We put this definition in a different
namespace, so that we can use `α.app` -/
@[implicit_reducible, simps (attr := grind =)]
/-
**CategoryTheory.Iso.app** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G : C
ategoryTheory.Functor C D} → (F ≅ G) → (X : C) → F.obj X ≅ G.obj X
参数：F ≅ G；X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The application of a natural isomorphism to an object. We put this definition in
 a different
namespace, so that we can use `α.app`
-/
def app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    F.obj X ≅ G.obj X where
  hom := α.hom.app X
  inv := α.inv.app X

attribute [to_dual existing app_inv] app_hom

@[reassoc +to_dual (attr := simp), grind =]
/-
**CategoryTheory.Iso.hom_inv_id_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ≅ G) (X : C),   CategoryTheory.CategoryStruct.comp (α.hom.app X) (α.in
v.app X) = CategoryTheory.CategoryStruct.id (F.obj X)
参数：α : F ≅ G；X : C；α.hom.app X；α.inv.app X；F.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hom_inv_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    α.hom.app X ≫ α.inv.app X = 𝟙 (F.obj X) := by cat_disch

@[reassoc +to_dual (attr := simp), grind =]
/-
**CategoryTheory.Iso.inv_hom_id_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
o`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ≅ G) (X : C),   CategoryTheory.CategoryStruct.comp (α.inv.app X) (α.ho
m.app X) = CategoryTheory.CategoryStruct.id (G.obj X)
参数：α : F ≅ G；X : C；α.inv.app X；α.hom.app X；G.obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_hom_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    α.inv.app X ≫ α.hom.app X = 𝟙 (G.obj X) := by cat_disch

@[reassoc +to_dual (attr := simp)]
/-
**CategoryTheory.Iso.hom_inv_id_app_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Iso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E]   {F G : CategoryTheory.Functor C (CategoryTheory.Fu
nctor D E)} (e : F ≅ G) (X₁ : C) (X₂ : D),   CategoryTheory.CategoryStruct.comp 
((e.hom.app X₁).app X₂) ((e.inv.app X₁).app X₂) =     CategoryTheory.CategoryStr
uct.id ((F.obj X₁).obj X₂)
参数：CategoryTheory.Functor D E；e : F ≅ G；X₁ : C；X₂ : D；(e.hom.app X₁).app X₂；(e.i
nv.app X₁).app X₂；(F.obj X₁).obj X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_inv_id_app_app {F G : C ⥤ D ⥤ E} (e : F ≅ G) (X₁ : C) (X₂ : D) :
    (e.hom.app X₁).app X₂ ≫ (e.inv.app X₁).app X₂ = 𝟙 _ := by cat_disch

@[reassoc +to_dual (attr := simp)]
/-
**CategoryTheory.Iso.inv_hom_id_app_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Iso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E]   {F G : CategoryTheory.Functor C (CategoryTheory.Fu
nctor D E)} (e : F ≅ G) (X₁ : C) (X₂ : D),   CategoryTheory.CategoryStruct.comp 
((e.inv.app X₁).app X₂) ((e.hom.app X₁).app X₂) =     CategoryTheory.CategoryStr
uct.id ((G.obj X₁).obj X₂)
参数：CategoryTheory.Functor D E；e : F ≅ G；X₁ : C；X₂ : D；(e.inv.app X₁).app X₂；(e.h
om.app X₁).app X₂；(G.obj X₁).obj X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_hom_id_app_app {F G : C ⥤ D ⥤ E} (e : F ≅ G) (X₁ : C) (X₂ : D) :
    (e.inv.app X₁).app X₂ ≫ (e.hom.app X₁).app X₂ = 𝟙 _ := by cat_disch

@[reassoc +to_dual (attr := simp)]
/-
**CategoryTheory.Iso.hom_inv_id_app_app_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Iso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] {E' : Type u₄}   [inst_3 : CategoryTheory.Category.{
v₄, u₄} E']   {F G : CategoryTheory.Functor C (CategoryTheory.Functor D (Categor
yTheory.Functor E E'))} (e : F ≅ G) (X₁ : C)   (X₂ : D) (X₃ : E),   CategoryTheo
ry.CategoryStruct.comp (((e.hom.app X₁).app X₂).app X₃) (((e.inv.app X₁).app X₂)
.app X₃) =     CategoryTheory.CategoryStruct.id (((F.obj X₁).obj X₂).obj X₃)
参数：CategoryTheory.Functor D (CategoryTheory.Functor E E')；e : F ≅ G；X₁ : C；X₂ : 
D；X₃ : E；((e.hom.app X₁).app X₂).app X₃；((e.inv.app X₁).app X₂).app X₃；((F.obj X
₁).obj X₂).obj X₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_inv_id_app_app_app {F G : C ⥤ D ⥤ E ⥤ E'} (e : F ≅ G)
    (X₁ : C) (X₂ : D) (X₃ : E) :
    ((e.hom.app X₁).app X₂).app X₃ ≫ ((e.inv.app X₁).app X₂).app X₃ = 𝟙 _ := by cat_disch

@[reassoc +to_dual (attr := simp)]
/-
**CategoryTheory.Iso.inv_hom_id_app_app_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Iso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] {E' : Type u₄}   [inst_3 : CategoryTheory.Category.{
v₄, u₄} E']   {F G : CategoryTheory.Functor C (CategoryTheory.Functor D (Categor
yTheory.Functor E E'))} (e : F ≅ G) (X₁ : C)   (X₂ : D) (X₃ : E),   CategoryTheo
ry.CategoryStruct.comp (((e.inv.app X₁).app X₂).app X₃) (((e.hom.app X₁).app X₂)
.app X₃) =     CategoryTheory.CategoryStruct.id (((G.obj X₁).obj X₂).obj X₃)
参数：CategoryTheory.Functor D (CategoryTheory.Functor E E')；e : F ≅ G；X₁ : C；X₂ : 
D；X₃ : E；((e.inv.app X₁).app X₂).app X₃；((e.hom.app X₁).app X₂).app X₃；((G.obj X
₁).obj X₂).obj X₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_hom_id_app_app_app {F G : C ⥤ D ⥤ E ⥤ E'} (e : F ≅ G)
    (X₁ : C) (X₂ : D) (X₃ : E) :
    ((e.inv.app X₁).app X₂).app X₃ ≫ ((e.hom.app X₁).app X₂).app X₃ = 𝟙 _ := by cat_disch

end Iso

namespace NatIso

open CategoryTheory.Category CategoryTheory.Functor

@[simp]
/-
**CategoryTheory.NatIso.trans_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatI
so`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G H : CategoryTheory.Functor 
C D} (α : F ≅ G) (β : G ≅ H) (X : C), (α ≪≫ β).app X = α.app X ≪≫ β.app X
参数：α : F ≅ G；β : G ≅ H；X : C；α ≪≫ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_app {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (X : C) :
    (α ≪≫ β).app X = α.app X ≪≫ β.app X :=
  rfl

variable {F G : C ⥤ D}

@[to_dual inv_app_isIso]
/-
**CategoryTheory.NatIso.hom_app_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ≅ G) (X : C), CategoryTheory.IsIso (α.hom.app X)
参数：α : F ≅ G；X : C；α.hom.app X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hom_app_isIso (α : F ≅ G) (X : C) : IsIso (α.hom.app X) :=
  ⟨⟨α.inv.app X, ⟨by grind, by grind⟩⟩⟩

section

/-!
Unfortunately we need a separate set of cancellation lemmas for components of natural isomorphisms,
because the `simp` normal form is `α.hom.app X`, rather than `α.app.hom X`.

(With the latter, the morphism would be visibly part of an isomorphism, so general lemmas about
isomorphisms would apply.)

In the future, we should consider a redesign that changes this simp normal form,
but for now it breaks too many proofs.
-/


variable (α : F ≅ G)

@[to_dual (attr := simp) cancel_natIso_inv_right]
/-
**CategoryTheory.NatIso.cancel_natIso_hom_left** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ≅ G) {X : C} {Y : D} (g g' : G.obj X ⟶ Y),   CategoryTheory.CategorySt
ruct.comp (α.hom.app X) g = CategoryTheory.CategoryStruct.comp (α.hom.app X) g' 
↔ g = g'
参数：α : F ≅ G；g g' : G.obj X ⟶ Y；α.hom.app X；α.hom.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
-/
theorem cancel_natIso_hom_left {X : C} {Y : D} (g g' : G.obj X ⟶ Y) :
    α.hom.app X ≫ g = α.hom.app X ≫ g' ↔ g = g' := by simp only [cancel_epi, refl]

@[to_dual (attr := simp) cancel_natIso_hom_right]
/-
**CategoryTheory.NatIso.cancel_natIso_inv_left** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ≅ G) {X : C} {Y : D} (g g' : F.obj X ⟶ Y),   CategoryTheory.CategorySt
ruct.comp (α.inv.app X) g = CategoryTheory.CategoryStruct.comp (α.inv.app X) g' 
↔ g = g'
参数：α : F ≅ G；g g' : F.obj X ⟶ Y；α.inv.app X；α.inv.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
-/
theorem cancel_natIso_inv_left {X : C} {Y : D} (g g' : F.obj X ⟶ Y) :
    α.inv.app X ≫ g = α.inv.app X ≫ g' ↔ g = g' := by simp only [cancel_epi, refl]

@[simp, to_dual none]
/-
**CategoryTheory.NatIso.cancel_natIso_hom_right_assoc** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ≅ G) {W X X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ F.obj Y) (f' : W ⟶ X') 
  (g' : X' ⟶ F.obj Y),   CategoryTheory.CategoryStruct.comp f (CategoryTheory.Ca
tegoryStruct.comp g (α.hom.app Y)) =       CategoryTheory.CategoryStruct.comp f'
 (CategoryTheory.CategoryStruct.comp g' (α.hom.app Y)) ↔     CategoryTheory.Cate
goryStruct.comp f g = CategoryTheory.CategoryStruct.comp f' g'
参数：α : F ≅ G；f : W ⟶ X；g : X ⟶ F.obj Y；f' : W ⟶ X'；g' : X' ⟶ F.obj Y；CategoryThe
ory.CategoryStruct.comp g (α.hom.app Y)；CategoryTheory.CategoryStruct.comp g' (α
.hom.app Y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
-/
theorem cancel_natIso_hom_right_assoc {W X X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ F.obj Y)
    (f' : W ⟶ X') (g' : X' ⟶ F.obj Y) :
    f ≫ g ≫ α.hom.app Y = f' ≫ g' ≫ α.hom.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono, refl]

@[simp, to_dual none]
/-
**CategoryTheory.NatIso.cancel_natIso_inv_right_assoc** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ≅ G) {W X X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ G.obj Y) (f' : W ⟶ X') 
  (g' : X' ⟶ G.obj Y),   CategoryTheory.CategoryStruct.comp f (CategoryTheory.Ca
tegoryStruct.comp g (α.inv.app Y)) =       CategoryTheory.CategoryStruct.comp f'
 (CategoryTheory.CategoryStruct.comp g' (α.inv.app Y)) ↔     CategoryTheory.Cate
goryStruct.comp f g = CategoryTheory.CategoryStruct.comp f' g'
参数：α : F ≅ G；f : W ⟶ X；g : X ⟶ G.obj Y；f' : W ⟶ X'；g' : X' ⟶ G.obj Y；CategoryThe
ory.CategoryStruct.comp g (α.inv.app Y)；CategoryTheory.CategoryStruct.comp g' (α
.inv.app Y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsIso.mono_of_iso`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   CategoryThe
ory.Mono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
-/
theorem cancel_natIso_inv_right_assoc {W X X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ G.obj Y)
    (f' : W ⟶ X') (g' : X' ⟶ G.obj Y) :
    f ≫ g ≫ α.inv.app Y = f' ≫ g' ≫ α.inv.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono, refl]

@[to_dual (attr := simp) inv_hom_app]
/-
**CategoryTheory.NatIso.inv_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Na
tIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (e : F ≅ G) (X : C), CategoryTheory.inv (e.inv.app X) = e.hom.app X
参数：e : F ≅ G；X : C；e.inv.app X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_inv_app {F G : C ⥤ D} (e : F ≅ G) (X : C) : inv (e.inv.app X) = e.hom.app X := by
  cat_disch

end

variable {X Y : C}

@[to_dual none, reassoc]
/-
**CategoryTheory.NatIso.naturality_1** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.N
atIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} {X Y : C} (α : F ≅ G) (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (α.in
v.app X) (CategoryTheory.CategoryStruct.comp (F.map f) (α.hom.app Y)) =     G.ma
p f
参数：α : F ≅ G；f : X ⟶ Y；α.inv.app X；CategoryTheory.CategoryStruct.comp (F.map f) 
(α.hom.app Y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_1 (α : F ≅ G) (f : X ⟶ Y) : α.inv.app X ≫ F.map f ≫ α.hom.app Y = G.map f := by
  simp

@[to_dual none, reassoc]
/-
**CategoryTheory.NatIso.naturality_2** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.N
atIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} {X Y : C} (α : F ≅ G) (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (α.ho
m.app X) (CategoryTheory.CategoryStruct.comp (G.map f) (α.inv.app Y)) =     F.ma
p f
参数：α : F ≅ G；f : X ⟶ Y；α.hom.app X；CategoryTheory.CategoryStruct.comp (G.map f) 
(α.inv.app Y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_2 (α : F ≅ G) (f : X ⟶ Y) : α.hom.app X ≫ G.map f ≫ α.inv.app Y = F.map f := by
  simp

@[to_dual none, reassoc]
/-
**CategoryTheory.NatIso.naturality_1'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} {X Y : C} (α : F ⟶ G) (f : X ⟶ Y) {x : CategoryTheory.IsIso (α.app X)},   Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.inv (α.app X))       (CategoryTh
eory.CategoryStruct.comp (F.map f) (α.app Y)) =     G.map f
参数：α : F ⟶ G；f : X ⟶ Y；α.app X；CategoryTheory.inv (α.app X)；CategoryTheory.Categ
oryStruct.comp (F.map f) (α.app Y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_1' (α : F ⟶ G) (f : X ⟶ Y) {_ : IsIso (α.app X)} :
    inv (α.app X) ≫ F.map f ≫ α.app Y = G.map f := by simp

@[to_dual none, reassoc (attr := simp)]
/-
**CategoryTheory.NatIso.naturality_2'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} {X Y : C} (α : F ⟶ G) (f : X ⟶ Y) {x : CategoryTheory.IsIso (α.app Y)},   Cat
egoryTheory.CategoryStruct.comp (α.app X)       (CategoryTheory.CategoryStruct.c
omp (G.map f) (CategoryTheory.inv (α.app Y))) =     F.map f
参数：α : F ⟶ G；f : X ⟶ Y；α.app Y；α.app X；CategoryTheory.CategoryStruct.comp (G.map
 f) (CategoryTheory.inv (α.app Y))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem naturality_2' (α : F ⟶ G) (f : X ⟶ Y) {_ : IsIso (α.app Y)} :
    α.app X ≫ G.map f ≫ inv (α.app Y) = F.map f := by cat_disch

/-- The components of a natural isomorphism are isomorphisms. -/
@[to_dual self]
/-
**CategoryTheory.NatIso.isIso_app_of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ⟶ G) [CategoryTheory.IsIso α] (X : C), CategoryTheory.IsIso (α.app X)
参数：α : F ⟶ G；X : C；α.app X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The components of a natural isomorphism are isomorphisms.
-/
instance isIso_app_of_isIso (α : F ⟶ G) [IsIso α] (X) : IsIso (α.app X) :=
  ⟨⟨(inv α).app X, ⟨by grind, by grind⟩⟩⟩

@[simp, push ←, to_dual self]
/-
**CategoryTheory.NatIso.isIso_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ⟶ G) [inst_2 : CategoryTheory.IsIso α] (X : C),   (CategoryTheory.inv 
α).app X = CategoryTheory.inv (α.app X)
参数：α : F ⟶ G；X : C；CategoryTheory.inv α；α.app X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isIso_inv_app (α : F ⟶ G) [IsIso α] (X) : (inv α).app X = inv (α.app X) := by cat_disch

@[to_dual (attr := simp) inv_map_hom_app]
/-
**CategoryTheory.NatIso.inv_map_inv_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E]   (F : CategoryTheory.Functor C (CategoryTheory.Func
tor D E)) {X Y : C} (e : X ≅ Y) (Z : D),   CategoryTheory.inv ((F.map e.inv).app
 Z) = (F.map e.hom).app Z
参数：F : CategoryTheory.Functor C (CategoryTheory.Functor D E)；e : X ≅ Y；Z : D；(F.
map e.inv).app Z；F.map e.hom。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_map_inv_app (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
    inv ((F.map e.inv).app Z) = (F.map e.hom).app Z := by cat_disch

set_option linter.translate.warnInvalid false in
/-- Construct a natural isomorphism between functors by giving object level isomorphisms,
and checking naturality only in the forward direction.
-/
@[implicit_reducible, to_dual (attr := simps (attr := grind =)) ofComponents'
/-- The dual of `ofComponents` -/]
/-
**CategoryTheory.NatIso.ofComponents** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.N
atIso`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G : C
ategoryTheory.Functor C D} →           (app : (X : C) → F.obj X ≅ G.obj X) →    
         autoParam                 (∀ {X Y : C} (f : X ⟶ Y),                   C
ategoryTheory.CategoryStruct.comp (F.map f) (app Y).hom =                     Ca
tegoryTheory.CategoryStruct.comp (app X).hom (G.map f))                 Category
Theory.NatIso.ofComponents._auto_1 →               (F ≅ G)
参数：app : (X : C) → F.obj X ≅ G.obj X；∀ {X Y : C} (f : X ⟶ Y),                   
CategoryTheory.CategoryStruct.comp (F.map f) (app Y).hom =                     C
ategoryTheory.CategoryStruct.comp (app X).hom (G.map f)；F ≅ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f := by cat_disch) :
    F ≅ G where
  hom := { app := fun X => (app X).hom }
  inv :=
    { app := fun X => (app X).inv,
      naturality := fun X Y f => by
        have h := congr_arg (fun f => (app X).inv ≫ f ≫ (app Y).inv) (naturality f).symm
        simp only [Iso.inv_hom_id_assoc, Iso.hom_inv_id, assoc, comp_id] at h
        exact h }

attribute [to_dual existing ofComponents'_inv_app] ofComponents_hom_app

attribute [to_dual existing ofComponents'_hom_app] ofComponents_inv_app

@[to_dual (attr := simp)]
/-
**CategoryTheory.NatIso.ofComponents.app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.NatIso.ofComponents`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (app' : (X : C) → F.obj X ≅ G.obj X)   (naturality :     ∀ {X Y : C} (f : X ⟶
 Y),       CategoryTheory.CategoryStruct.comp (F.map f) (app' Y).hom =         C
ategoryTheory.CategoryStruct.comp (app' X).hom (G.map f))   (X : C), (CategoryTh
eory.NatIso.ofComponents app' naturality).app X = app' X
参数：app' : (X : C) → F.obj X ≅ G.obj X；naturality :     ∀ {X Y : C} (f : X ⟶ Y), 
      CategoryTheory.CategoryStruct.comp (F.map f) (app' Y).hom =         Catego
ryTheory.CategoryStruct.comp (app' X).hom (G.map f)；X : C；CategoryTheory.NatIso.
ofComponents app' naturality。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
-/
theorem ofComponents.app (app' : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
    (ofComponents app' naturality).app X = app' X := by cat_disch

-- Making this an instance would cause a typeclass inference loop with `isIso_app_of_isIso`.
/-- A natural transformation is an isomorphism if all its components are isomorphisms.
-/
/-
**CategoryTheory.NatIso.isIso_of_isIso_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ⟶ G) [∀ (X : C), CategoryTheory.IsIso (α.app X)], CategoryTheory.IsIso
 α
参数：α : F ⟶ G；X : C；α.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A natural transformation is an isomorphism if all its components are isomorphism
s.
-/
theorem isIso_of_isIso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  (ofComponents (fun X => asIso (α.app X)) (by simp)).isIso_hom

/-- Horizontal composition of natural isomorphisms. -/
@[simps]
/-
**CategoryTheory.NatIso.hcomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatIso`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {E : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             {F
 G : CategoryTheory.Functor C D} →               {H I : CategoryTheory.Functor D
 E} → (F ≅ G) → (H ≅ I) → (F.comp H ≅ G.comp I)
参数：F ≅ G；H ≅ I；F.comp H ≅ G.comp I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Horizontal composition of natural isomorphisms.
-/
def hcomp {F G : C ⥤ D} {H I : D ⥤ E} (α : F ≅ G) (β : H ≅ I) : F ⋙ H ≅ G ⋙ I where
  hom := α.hom ◫ β.hom
  inv := α.inv ◫ β.inv

attribute [to_dual existing hcomp_inv] hcomp_hom

@[to_dual self]
/-
**CategoryTheory.NatIso.isIso_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
NatIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F₁ F₂ : CategoryTheory.Functor 
C D} (e : F₁ ≅ F₂) {X Y : C} (f : X ⟶ Y),   CategoryTheory.IsIso (F₁.map f) ↔ Ca
tegoryTheory.IsIso (F₂.map f)
参数：e : F₁ ≅ F₂；f : X ⟶ Y；F₁.map f；F₂.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isIso_map_iff {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) {X Y : C} (f : X ⟶ Y) :
    IsIso (F₁.map f) ↔ IsIso (F₂.map f) := by
  revert F₁ F₂
  suffices ∀ {F₁ F₂ : C ⥤ D} (_ : F₁ ≅ F₂) (_ : IsIso (F₁.map f)), IsIso (F₂.map f) from
    fun F₁ F₂ e => ⟨this e, this e.symm⟩
  intro F₁ F₂ e hf
  exact IsIso.mk ⟨e.inv.app Y ≫ inv (F₁.map f) ≫ e.hom.app X, by cat_disch⟩

end NatIso

@[to_dual self]
/-
**CategoryTheory.NatTrans.isIso_iff_isIso_app** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.NatTrans`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (τ : F ⟶ G), CategoryTheory.IsIso τ ↔ ∀ (X : C), CategoryTheory.IsIso (τ.app 
X)
参数：τ : F ⟶ G；X : C；τ.app X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
lemma NatTrans.isIso_iff_isIso_app {F G : C ⥤ D} (τ : F ⟶ G) :
    IsIso τ ↔ ∀ X, IsIso (τ.app X) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ NatIso.isIso_of_isIso_app _⟩

namespace Functor

variable (F : C ⥤ D) (obj : C → D) (e : ∀ X, F.obj X ≅ obj X)

/-- Constructor for a functor that is isomorphic to a given functor `F : C ⥤ D`,
while being definitionally equal on objects to a given map `obj : C → D`
such that for all `X : C`, we have an isomorphism `F.obj X ≅ obj X`. -/
@[simps obj]
/-
**CategoryTheory.Functor.copyObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) → (obj : C → D) → ((X : C) → F.obj X ≅ obj X) → Categor
yTheory.Functor C D
参数：F : CategoryTheory.Functor C D；obj : C → D；(X : C) → F.obj X ≅ obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for a functor that is isomorphic to a given functor `F : C ⥤ D`,
while being definitionally equal on objects to a given map `obj : C → D`
such that for all `X : C`, we have an isomorphism `F.obj X ≅ obj X`.
-/
def copyObj : C ⥤ D where
  obj := obj
  map f := (e _).inv ≫ F.map f ≫ (e _).hom

/-- The functor constructed with `copyObj` is isomorphic to the given functor. -/
@[simps!]
/-
**CategoryTheory.Functor.isoCopyObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) → (obj : C → D) → (e : (X : C) → F.obj X ≅ obj X) → F ≅
 F.copyObj obj e
参数：F : CategoryTheory.Functor C D；obj : C → D；e : (X : C) → F.obj X ≅ obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor constructed with `copyObj` is isomorphic to the given functor.
-/
def isoCopyObj : F ≅ F.copyObj obj e :=
  NatIso.ofComponents e (by simp [Functor.copyObj])

end Functor

@[to_dual none, reassoc]
/-
**CategoryTheory.NatTrans.naturality_1** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y),   CategoryTheory.CategoryStruct.comp (F.ma
p e.inv) (CategoryTheory.CategoryStruct.comp (α.app X) (G.map e.hom)) =     α.ap
p Y
参数：α : F ⟶ G；e : X ≅ Y；F.map e.inv；CategoryTheory.CategoryStruct.comp (α.app X) 
(G.map e.hom)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Iso.map_inv_hom_id`：map_inv_hom_id (F : C ⥤ D) : F.map e.
inv ≫ F.map e.hom = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma NatTrans.naturality_1 {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    F.map e.inv ≫ α.app X ≫ G.map e.hom = α.app Y := by
  simp

@[to_dual none, reassoc]
/-
**CategoryTheory.NatTrans.naturality_2** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y),   CategoryTheory.CategoryStruct.comp (F.ma
p e.hom) (CategoryTheory.CategoryStruct.comp (α.app Y) (G.map e.inv)) =     α.ap
p X
参数：α : F ⟶ G；e : X ≅ Y；F.map e.hom；CategoryTheory.CategoryStruct.comp (α.app Y) 
(G.map e.inv)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Iso.map_hom_inv_id`：map_hom_inv_id (F : C ⥤ D) : F.map e.
hom ≫ F.map e.inv = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma NatTrans.naturality_2 {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    F.map e.hom ≫ α.app Y ≫ G.map e.inv = α.app X := by
  simp

end CategoryTheory

