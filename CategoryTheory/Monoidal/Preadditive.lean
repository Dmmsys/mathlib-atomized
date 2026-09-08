/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Preadditive monoidal categories

A monoidal category is `MonoidalPreadditive` if it is preadditive and tensor product of morphisms
is linear in both factors.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (C : Type*) [Category* C] [Preadditive C] [MonoidalCategory C]

/-- A category is `MonoidalPreadditive` if tensoring is additive in both factors.

Note we don't `extend Preadditive C` here, as `Abelian C` already extends it,
and we'll need to have both typeclasses sometimes.
-/
/-
**CategoryTheory.MonoidalPreadditive** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：MonoidalPreadditive : Prop where whiskerLeft_zero : forall {X Y Z : C}, X 
◁ (0 : Y ⟶ Z) = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category is `MonoidalPreadditive` if tensoring is additive in both factors.

Note we don't `extend Preadditive C` here, as `Abelian C` already extends it,
and we'll need to have both typeclasses sometimes.
-/
class MonoidalPreadditive : Prop where
  whiskerLeft_zero : ∀ {X Y Z : C}, X ◁ (0 : Y ⟶ Z) = 0 := by cat_disch
  zero_whiskerRight : ∀ {X Y Z : C}, (0 : Y ⟶ Z) ▷ X = 0 := by cat_disch
  whiskerLeft_add : ∀ {X Y Z : C} (f g : Y ⟶ Z), X ◁ (f + g) = X ◁ f + X ◁ g := by cat_disch
  add_whiskerRight : ∀ {X Y Z : C} (f g : Y ⟶ Z), (f + g) ▷ X = f ▷ X + g ▷ X := by cat_disch

attribute [simp] MonoidalPreadditive.whiskerLeft_zero MonoidalPreadditive.zero_whiskerRight
attribute [simp] MonoidalPreadditive.whiskerLeft_add MonoidalPreadditive.add_whiskerRight

variable {C}
variable [MonoidalPreadditive C]

namespace MonoidalPreadditive

-- The priority setting will not be needed when we replace `𝟙 X ⊗ₘ f` by `X ◁ f`.
@[simp (low)]
/-
**CategoryTheory.MonoidalPreadditive.tensor_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalPreadditive`。
形式化陈述：tensor_zero {W X Y Z : C} (f : W ⟶ X) : f otimesₘ (0 : Y ⟶ Z) = 0
参数：f : W ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalPreadditive.whiskerLeft_zero`：∀ {C : Type u_1} {i
nst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive
 C}   {inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensor_zero {W X Y Z : C} (f : W ⟶ X) : f ⊗ₘ (0 : Y ⟶ Z) = 0 := by
  simp [tensorHom_def]

-- The priority setting will not be needed when we replace `f ⊗ₘ 𝟙 X` by `f ▷ X`.
@[simp (low)]
/-
**CategoryTheory.MonoidalPreadditive.zero_tensor** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MonoidalPreadditive`。
形式化陈述：zero_tensor {W X Y Z : C} (f : Y ⟶ Z) : (0 : W ⟶ X) otimesₘ f = 0
参数：f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalPreadditive.zero_whiskerRight`：∀ {C : Type u_1} {
inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditiv
e C}   {inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_tensor {W X Y Z : C} (f : Y ⟶ Z) : (0 : W ⟶ X) ⊗ₘ f = 0 := by
  simp [tensorHom_def]
/-
**CategoryTheory.MonoidalPreadditive.tensor_add** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalPreadditive`。
形式化陈述：tensor_add {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z) : f otimesₘ (g + h) = f
 otimesₘ g + f otimesₘ h
参数：f : W ⟶ X；g h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalPreadditive.whiskerLeft_add`：∀ {C : Type u_1} {in
st : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive 
C}   {inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensor_add {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z) : f ⊗ₘ (g + h) = f ⊗ₘ g + f ⊗ₘ h := by
  simp [tensorHom_def]
/-
**CategoryTheory.MonoidalPreadditive.add_tensor** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalPreadditive`。
形式化陈述：add_tensor {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z) : (f + g) otimesₘ h = f
 otimesₘ h + g otimesₘ h
参数：f g : W ⟶ X；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalPreadditive.add_whiskerRight`：∀ {C : Type u_1} {i
nst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive
 C}   {inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_tensor {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z) : (f + g) ⊗ₘ h = f ⊗ₘ h + g ⊗ₘ h := by
  simp [tensorHom_def]
/-
**CategoryTheory.MonoidalPreadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
MonoidalPreadditive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : (tensorLeft X).Additive where
/-
**CategoryTheory.MonoidalPreadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
MonoidalPreadditive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : (tensorRight X).Additive where
/-
**CategoryTheory.MonoidalPreadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
MonoidalPreadditive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (curriedTensor C).Additive where
/-
**CategoryTheory.MonoidalPreadditive.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
MonoidalPreadditive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (curriedTensor C).flip.Additive where

end MonoidalPreadditive

/-
**CategoryTheory.tensorLeft_additive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.MonoidalCategory C] [Cat
egoryTheory.MonoidalPreadditive C] (X : C),   (CategoryTheory.MonoidalCategory.t
ensorLeft X).Additive
参数：X : C；CategoryTheory.MonoidalCategory.tensorLeft X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalPreadditive.whiskerLeft_add`：∀ {C : Type u_1} {in
st : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive 
C}   {inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance tensorLeft_additive (X : C) : (tensorLeft X).Additive where
/-
**CategoryTheory.tensorRight_additive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.MonoidalCategory C] [Cat
egoryTheory.MonoidalPreadditive C] (X : C),   (CategoryTheory.MonoidalCategory.t
ensorRight X).Additive
参数：X : C；CategoryTheory.MonoidalCategory.tensorRight X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `CategoryTheory.MonoidalPreadditive.instAdditiveFunctorCurriedTensor`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Preadditive C]   [inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance tensorRight_additive (X : C) : (tensorRight X).Additive where
/-
**CategoryTheory.tensoringLeft_additive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.MonoidalCategory C] [Cat
egoryTheory.MonoidalPreadditive C] (X : C),   ((CategoryTheory.MonoidalCategory.
tensoringLeft C).obj X).Additive
参数：X : C；(CategoryTheory.MonoidalCategory.tensoringLeft C).obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalPreadditive.whiskerLeft_add`：∀ {C : Type u_1} {in
st : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive 
C}   {inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance tensoringLeft_additive (X : C) : ((tensoringLeft C).obj X).Additive where
/-
**CategoryTheory.tensoringRight_additive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.MonoidalCategory C] [Cat
egoryTheory.MonoidalPreadditive C] (X : C),   ((CategoryTheory.MonoidalCategory.
tensoringRight C).obj X).Additive
参数：X : C；(CategoryTheory.MonoidalCategory.tensoringRight C).obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `CategoryTheory.MonoidalPreadditive.instAdditiveFunctorCurriedTensor`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Preadditive C]   [inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance tensoringRight_additive (X : C) : ((tensoringRight C).obj X).Additive where

/-- A faithful additive monoidal functor to a monoidal preadditive category
ensures that the domain is monoidal preadditive. -/
/-
**CategoryTheory.monoidalPreadditive_of_faithful** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory`。
形式化陈述：monoidalPreadditive_of_faithful {D} [Category* D] [Preadditive D] [Monoida
lCategory D] (F : D ⥤ C) [F.Monoidal] [F.Faithful] [F.Additive] : MonoidalPreadd
itive D
参数：F : D ⥤ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.Monoidal.map_whiskerLeft`：map_whiskerLeft (X : C)
 {Y Z : C} (f : Y ⟶ Z) : F.map (X ◁ f) = δ F X Y ≫ F.obj X ◁ F.map f ≫ μ F X Z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.MonoidalPreadditive.whiskerLeft_zero`：∀ {C : Type u_1} {i
nst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive
 C}   {inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.Monoidal.map_whiskerRight`：map_whiskerRight {X Y 
: C} (f : X ⟶ Y) (Z : C) : F.map (f ▷ Z) = δ F X Z ≫ F.map f ▷ F.obj Z ≫ μ F Y Z
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.MonoidalPreadditive.zero_whiskerRight`：∀ {C : Type u_1} {
inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditiv
e C}   {inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `CategoryTheory.MonoidalPreadditive.whiskerLeft_add`：∀ {C : Type u_1} {in
st : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive 
C}   {inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.MonoidalPreadditive.add_whiskerRight`：∀ {C : Type u_1} {i
nst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive
 C}   {inst_2 : CategoryTheory.MonoidalCa…

--- 原说明 ---
A faithful additive monoidal functor to a monoidal preadditive category
ensures that the domain is monoidal preadditive.
-/
theorem monoidalPreadditive_of_faithful {D} [Category* D] [Preadditive D] [MonoidalCategory D]
    (F : D ⥤ C) [F.Monoidal] [F.Faithful] [F.Additive] :
    MonoidalPreadditive D :=
  { whiskerLeft_zero := by
      intros
      apply F.map_injective
      simp [Functor.Monoidal.map_whiskerLeft]
    zero_whiskerRight := by
      intros
      apply F.map_injective
      simp [Functor.Monoidal.map_whiskerRight]
    whiskerLeft_add := by
      intros
      apply F.map_injective
      simp only [Functor.Monoidal.map_whiskerLeft, Functor.map_add, Preadditive.comp_add,
        Preadditive.add_comp, MonoidalPreadditive.whiskerLeft_add]
    add_whiskerRight := by
      intros
      apply F.map_injective
      simp only [Functor.Monoidal.map_whiskerRight, Functor.map_add, Preadditive.comp_add,
        Preadditive.add_comp, MonoidalPreadditive.add_whiskerRight] }
/-
**CategoryTheory.whiskerLeft_sum** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：whiskerLeft_sum (P : C) {Q R : C} {J : Type*} (s : Finset J) (g : J -> (Q 
⟶ R)) : P ◁ ∑ j in s, g j = ∑ j in s, P ◁ g j
参数：P : C；s : Finset J；g : J -> (Q ⟶ R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `CategoryTheory.tensoringLeft_additive`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2 
: CategoryTheory.MonoidalCa…
-/
theorem whiskerLeft_sum (P : C) {Q R : C} {J : Type*} (s : Finset J) (g : J → (Q ⟶ R)) :
    P ◁ ∑ j ∈ s, g j = ∑ j ∈ s, P ◁ g j :=
  map_sum ((tensoringLeft C).obj P).mapAddHom g s
/-
**CategoryTheory.sum_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：sum_whiskerRight {Q R : C} {J : Type*} (s : Finset J) (g : J -> (Q ⟶ R)) (
P : C) : (∑ j in s, g j) ▷ P = ∑ j in s, g j ▷ P
参数：s : Finset J；g : J -> (Q ⟶ R)；P : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `CategoryTheory.tensoringRight_additive`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2
 : CategoryTheory.MonoidalCa…
-/
theorem sum_whiskerRight {Q R : C} {J : Type*} (s : Finset J) (g : J → (Q ⟶ R)) (P : C) :
    (∑ j ∈ s, g j) ▷ P = ∑ j ∈ s, g j ▷ P :=
  map_sum ((tensoringRight C).obj P).mapAddHom g s
/-
**CategoryTheory.tensor_sum** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：tensor_sum {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J -> 
(R ⟶ S)) : (f otimesₘ ∑ j in s, g j) = ∑ j in s, f otimesₘ g j
参数：s : Finset J；f : P ⟶ Q；g : J -> (R ⟶ S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.whiskerLeft_sum`：whiskerLeft_sum (P : C) {Q R : C} {J : T
ype*} (s : Finset J) (g : J -> (Q ⟶ R)) : P ◁ ∑ j in s, g j = ∑ j in s, P ◁ g j
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensor_sum {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
    (f ⊗ₘ ∑ j ∈ s, g j) = ∑ j ∈ s, f ⊗ₘ g j := by
  simp only [tensorHom_def, whiskerLeft_sum, Preadditive.comp_sum]
/-
**CategoryTheory.sum_tensor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：sum_tensor {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J -> 
(R ⟶ S)) : (∑ j in s, g j) otimesₘ f = ∑ j in s, g j otimesₘ f
参数：s : Finset J；f : P ⟶ Q；g : J -> (R ⟶ S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.sum_whiskerRight`：sum_whiskerRight {Q R : C} {J : Type*} 
(s : Finset J) (g : J -> (Q ⟶ R)) (P : C) : (∑ j in s, g j) ▷ P = ∑ j in s, g j 
▷ P
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_tensor {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J → (R ⟶ S)) :
    (∑ j ∈ s, g j) ⊗ₘ f = ∑ j ∈ s, g j ⊗ₘ f := by
  simp only [tensorHom_def, sum_whiskerRight, Preadditive.sum_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- In a closed monoidal category, this would hold because
-- `tensorLeft X` is a left adjoint and hence preserves all colimits.
-- In any case it is true in any preadditive category.
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : PreservesFiniteBiproducts (tensorLeft X) where
  preserves {J} :=
    let ⟨_⟩ := nonempty_fintype J
    { preserves := fun {f} =>
        { preserves := fun {b} i => ⟨isBilimitOfTotal _ (by
            dsimp
            simp_rw [← id_tensorHom]
            simp only [tensorHom_comp_tensorHom, Category.comp_id, ← tensor_sum, ← id_tensorHom_id,
              IsBilimit.total i])⟩ } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : PreservesFiniteBiproducts (tensorRight X) where
  preserves {J} :=
    let ⟨_⟩ := nonempty_fintype J
    { preserves := fun {f} =>
        { preserves := fun {b} i => ⟨isBilimitOfTotal _ (by
            dsimp
            simp_rw [← tensorHom_id]
            simp only [tensorHom_comp_tensorHom, Category.comp_id, ← sum_tensor, ← id_tensorHom_id,
               IsBilimit.total i])⟩ } }

variable [HasFiniteBiproducts C]

/-- The isomorphism showing how tensor product on the left distributes over direct sums. -/
/-
**CategoryTheory.leftDistributor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：leftDistributor {J : Type} [Finite J] (X : C) (f : J -> C) : X otimes ⨁ f 
≅ ⨁ fun j => X otimes f j
参数：X : C；f : J -> C。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism showing how tensor product on the left distributes over direct s
ums.
-/
def leftDistributor {J : Type} [Finite J] (X : C) (f : J → C) : X ⊗ ⨁ f ≅ ⨁ fun j => X ⊗ f j :=
  (tensorLeft X).mapBiproduct f

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.leftDistributor_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：leftDistributor_hom {J : Type} [Fintype J] (X : C) (f : J -> C) : (leftDis
tributor X f).hom = ∑ j : J, (X ◁ biproduct.π f j) ≫ biproduct.ι (fun j => X oti
mes f j) j
参数：X : C；f : J -> C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π`：∀ {J : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.comp_dite`：comp_dite {P : Prop} [Decidable P] {X Y Z : C}
 (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f ≫ if h : P then g h el
se g' h) = if …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftDistributor_hom {J : Type} [Fintype J] (X : C) (f : J → C) :
    (leftDistributor X f).hom =
      ∑ j : J, (X ◁ biproduct.π f j) ≫ biproduct.ι (fun j => X ⊗ f j) j := by
  classical
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.leftDistributor_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：leftDistributor_inv {J : Type} [Fintype J] (X : C) (f : J -> C) : (leftDis
tributor X f).inv = ∑ j : J, biproduct.π _ j ≫ (X ◁ biproduct.ι f j)
参数：X : C；f : J -> C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_assoc`：∀ {J : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.dite_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {P : Prop} [inst_1 : Decidable P] {X Y Z : C} (g : P → (Z ⟶ Y))   (g'
 : ¬P → (Z ⟶ Y…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → a = x → M)
, (∑ x ∈…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftDistributor_inv {J : Type} [Fintype J] (X : C) (f : J → C) :
    (leftDistributor X f).inv = ∑ j : J, biproduct.π _ j ≫ (X ◁ biproduct.ι f j) := by
  classical
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp, zero_comp,
    Finset.sum_dite_eq, Finset.mem_univ, ite_true, eqToHom_refl, Category.id_comp,
    biproduct.ι_desc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.leftDistributor_hom_comp_biproduct_** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftDistributor_hom_comp_biproduct_π {J : Type} [Finite J] (X : C) (f : J → C) (j : J) :
    (leftDistributor X f).hom ≫ biproduct.π _ j = X ◁ biproduct.π _ j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]

@[reassoc (attr := simp)]
/-
**CategoryTheory.biproduct_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct_ι_comp_leftDistributor_hom {J : Type} [Finite J] (X : C) (f : J → C) (j : J) :
    (X ◁ biproduct.ι _ j) ≫ (leftDistributor X f).hom = biproduct.ι (fun j => X ⊗ f j) j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_hom, Preadditive.comp_sum, ← whiskerLeft_comp_assoc,
    biproduct.ι_π, whiskerLeft_dite, dite_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.leftDistributor_inv_comp_biproduct_** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftDistributor_inv_comp_biproduct_π {J : Type} [Finite J] (X : C) (f : J → C) (j : J) :
    (leftDistributor X f).inv ≫ (X ◁ biproduct.π _ j) = biproduct.π _ j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_inv, Preadditive.sum_comp, ← whiskerLeft_comp,
    biproduct.ι_π, whiskerLeft_dite, comp_dite]

@[reassoc (attr := simp)]
/-
**CategoryTheory.biproduct_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct_ι_comp_leftDistributor_inv {J : Type} [Finite J] (X : C) (f : J → C) (j : J) :
    biproduct.ι _ j ≫ (leftDistributor X f).inv = X ◁ biproduct.ι _ j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_inv, Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp]
/-
**CategoryTheory.leftDistributor_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：leftDistributor_assoc {J : Type} [Finite J] (X Y : C) (f : J -> C) : (asIs
o (𝟙 X) otimesᵢ leftDistributor Y f) ≪≫ leftDistributor X _ = (α_ X Y (⨁ f)).sym
m ≪≫ leftDistributor (X otimes Y) f ≪≫ biproduct.mapIso fun _ => α_ X Y _
参数：X Y : C；f : J -> C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorIso_hom`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] {X 
Y X' Y' : C}   (f : X ≅ Y) (g : X' …
· 使用定理 `CategoryTheory.leftDistributor_hom`：leftDistributor_hom {J : Type} [Fint
ype J] (X : C) (f : J -> C) : (leftDistributor X f).hom = ∑ j : J, (X ◁ biproduc
t.π f j) ≫ biproduct.ι (…
· 使用定理 `CategoryTheory.tensor_sum`：tensor_sum {P Q R S : C} {J : Type*} (s : Fin
set J) (f : P ⟶ Q) (g : J -> (R ⟶ S)) : (f otimesₘ ∑ j in s, g j) = ∑ j in s, f 
otimesₘ g j
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensor_comp`：id_tensor_comp (f : W ⟶ 
X) (g : X ⟶ Y) : 𝟙 Z otimesₘ f ≫ g = (𝟙 Z otimesₘ f) ≫ (𝟙 Z otimesₘ g)
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π`：∀ {J : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.comp_dite`：comp_dite {P : Prop} [Decidable P] {X Y Z : C}
 (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f ≫ if h : P then g h el
se g' h) = if …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_irrel`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] (p : Prop) [inst_1 : Decidable p] (s : Finset ι)   (f : p → ι → M) (g : 
¬p → ι → M)…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.biproduct.mapIso_hom`：∀ {J : Type w} {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C] {f g : J → C} [i…
（共 42 条，此处仅展示前 30 条）
-/
theorem leftDistributor_assoc {J : Type} [Finite J] (X Y : C) (f : J → C) :
    (asIso (𝟙 X) ⊗ᵢ leftDistributor Y f) ≪≫ leftDistributor X _ =
      (α_ X Y (⨁ f)).symm ≪≫ leftDistributor (X ⊗ Y) f ≪≫ biproduct.mapIso fun _ => α_ X Y _ := by
  classical
  cases nonempty_fintype J
  ext
  simp only [Category.comp_id, Category.assoc, eqToHom_refl, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, comp_zero, comp_dite, Preadditive.sum_comp, Preadditive.comp_sum, tensor_sum,
    id_tensor_comp, tensorIso_hom, leftDistributor_hom, biproduct.mapIso_hom, biproduct.ι_map,
    biproduct.ι_π, Finset.sum_dite_irrel, Finset.sum_dite_eq', Finset.sum_const_zero]
  simp_rw [← id_tensorHom]
  simp only [← id_tensor_comp, biproduct.ι_π]
  simp only [id_tensor_comp, tensor_dite, comp_dite]
  simp

/-- The isomorphism showing how tensor product on the right distributes over direct sums. -/
/-
**CategoryTheory.rightDistributor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：rightDistributor {J : Type} [Finite J] (f : J -> C) (X : C) : (⨁ f) otimes
 X ≅ ⨁ fun j => f j otimes X
参数：f : J -> C；X : C。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism showing how tensor product on the right distributes over direct 
sums.
-/
def rightDistributor {J : Type} [Finite J] (f : J → C) (X : C) : (⨁ f) ⊗ X ≅ ⨁ fun j => f j ⊗ X :=
  (tensorRight X).mapBiproduct f

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.rightDistributor_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：rightDistributor_hom {J : Type} [Fintype J] (f : J -> C) (X : C) : (rightD
istributor f X).hom = ∑ j : J, (biproduct.π f j ▷ X) ≫ biproduct.ι (fun j => f j
 otimes X) j
参数：f : J -> C；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.lift_π`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π`：∀ {J : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.comp_dite`：comp_dite {P : Prop} [Decidable P] {X Y Z : C}
 (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f ≫ if h : P then g h el
se g' h) = if …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightDistributor_hom {J : Type} [Fintype J] (f : J → C) (X : C) :
    (rightDistributor f X).hom =
      ∑ j : J, (biproduct.π f j ▷ X) ≫ biproduct.ι (fun j => f j ⊗ X) j := by
  classical
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, ite_true]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.rightDistributor_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：rightDistributor_inv {J : Type} [Fintype J] (f : J -> C) (X : C) : (rightD
istributor f X).inv = ∑ j : J, biproduct.π _ j ≫ (biproduct.ι f j ▷ X)
参数：f : J -> C；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biproduct.ι_desc`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {f : J → C} [ins…
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π_assoc`：∀ {J : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZe
roMorphisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.dite_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {P : Prop} [inst_1 : Decidable P] {X Y Z : C} (g : P → (Z ⟶ Y))   (g'
 : ¬P → (Z ⟶ Y…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → a = x → M)
, (∑ x ∈…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightDistributor_inv {J : Type} [Fintype J] (f : J → C) (X : C) :
    (rightDistributor f X).inv = ∑ j : J, biproduct.π _ j ≫ (biproduct.ι f j ▷ X) := by
  classical
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp,
    zero_comp, Finset.sum_dite_eq, Finset.mem_univ, eqToHom_refl, Category.id_comp, ite_true]

@[reassoc (attr := simp)]
/-
**CategoryTheory.rightDistributor_hom_comp_biproduct_** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightDistributor_hom_comp_biproduct_π {J : Type} [Finite J] (f : J → C) (X : C) (j : J) :
    (rightDistributor f X).hom ≫ biproduct.π _ j = biproduct.π _ j ▷ X := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]

@[reassoc (attr := simp)]
/-
**CategoryTheory.biproduct_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct_ι_comp_rightDistributor_hom {J : Type} [Finite J] (f : J → C) (X : C) (j : J) :
    (biproduct.ι _ j ▷ X) ≫ (rightDistributor f X).hom = biproduct.ι (fun j => f j ⊗ X) j := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_hom, Preadditive.comp_sum, ← comp_whiskerRight_assoc, biproduct.ι_π,
    dite_whiskerRight, dite_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.rightDistributor_inv_comp_biproduct_** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightDistributor_inv_comp_biproduct_π {J : Type} [Finite J] (f : J → C) (X : C) (j : J) :
    (rightDistributor f X).inv ≫ (biproduct.π _ j ▷ X) = biproduct.π _ j := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_inv, Preadditive.sum_comp, ← comp_whiskerRight,
    biproduct.ι_π, dite_whiskerRight, comp_dite]

@[reassoc (attr := simp)]
/-
**CategoryTheory.biproduct_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biproduct_ι_comp_rightDistributor_inv {J : Type} [Finite J] (f : J → C) (X : C) (j : J) :
    biproduct.ι _ j ≫ (rightDistributor f X).inv = biproduct.ι _ j ▷ X := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_inv, Preadditive.comp_sum, biproduct.ι_π_assoc,
    dite_comp]
/-
**CategoryTheory.rightDistributor_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：rightDistributor_assoc {J : Type} [Finite J] (f : J -> C) (X Y : C) : (rig
htDistributor f X otimesᵢ asIso (𝟙 Y)) ≪≫ rightDistributor _ Y = α_ (⨁ f) X Y ≪≫
 rightDistributor f (X otimes Y) ≪≫ biproduct.mapIso fun _ => (α_ _ X Y).symm
参数：f : J -> C；X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorIso_hom`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] {X 
Y X' Y' : C}   (f : X ≅ Y) (g : X' …
· 使用定理 `CategoryTheory.rightDistributor_hom`：rightDistributor_hom {J : Type} [Fi
ntype J] (f : J -> C) (X : C) : (rightDistributor f X).hom = ∑ j : J, (biproduct
.π f j ▷ X) ≫ biproduct.ι…
· 使用定理 `CategoryTheory.sum_tensor`：sum_tensor {P Q R S : C} {J : Type*} (s : Fin
set J) (f : P ⟶ Q) (g : J -> (R ⟶ S)) : (∑ j in s, g j) otimesₘ f = ∑ j in s, g 
j otimesₘ f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.MonoidalCategory.comp_tensor_id`：comp_tensor_id (f : W ⟶ 
X) (g : X ⟶ Y) : f ≫ g otimesₘ 𝟙 Z = (f otimesₘ 𝟙 Z) ≫ (g otimesₘ 𝟙 Z)
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π`：∀ {J : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.comp_dite`：comp_dite {P : Prop} [Decidable P] {X Y Z : C}
 (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f ≫ if h : P then g h el
se g' h) = if …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_irrel`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] (p : Prop) [inst_1 : Decidable p] (s : Finset ι)   (f : p → ι → M) (g : 
¬p → ι → M)…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
（共 44 条，此处仅展示前 30 条）
-/
theorem rightDistributor_assoc {J : Type} [Finite J] (f : J → C) (X Y : C) :
    (rightDistributor f X ⊗ᵢ asIso (𝟙 Y)) ≪≫ rightDistributor _ Y =
      α_ (⨁ f) X Y ≪≫ rightDistributor f (X ⊗ Y) ≪≫ biproduct.mapIso fun _ => (α_ _ X Y).symm := by
  classical
  cases nonempty_fintype J
  ext
  simp only [Category.comp_id, Category.assoc, eqToHom_refl, Iso.symm_hom, Iso.trans_hom,
    asIso_hom, comp_zero, comp_dite, Preadditive.sum_comp, Preadditive.comp_sum, sum_tensor,
    comp_tensor_id, tensorIso_hom, rightDistributor_hom, biproduct.mapIso_hom, biproduct.ι_map,
    biproduct.ι_π, Finset.sum_dite_irrel, Finset.sum_dite_eq', Finset.sum_const_zero,
    Finset.mem_univ, if_true]
  simp_rw [← tensorHom_id]
  simp only [← comp_tensor_id, biproduct.ι_π, dite_tensor, comp_dite]
  simp
/-
**CategoryTheory.leftDistributor_rightDistributor_assoc** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory`。
形式化陈述：leftDistributor_rightDistributor_assoc {J : Type _} [Finite J] (X : C) (f 
: J -> C) (Y : C) : (leftDistributor X f otimesᵢ asIso (𝟙 Y)) ≪≫ rightDistributo
r _ Y = α_ X (⨁ f) Y ≪≫ (asIso (𝟙 X) otimesᵢ rightDistributor _ Y) ≪≫ leftDistri
butor X _ ≪≫ biproduct.mapIso fun _ => (α_ _ _ _).symm
参数：X : C；f : J -> C；Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorIso_hom`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] {X 
Y X' Y' : C}   (f : X ≅ Y) (g : X' …
· 使用定理 `CategoryTheory.leftDistributor_hom`：leftDistributor_hom {J : Type} [Fint
ype J] (X : C) (f : J -> C) : (leftDistributor X f).hom = ∑ j : J, (X ◁ biproduc
t.π f j) ≫ biproduct.ι (…
· 使用定理 `CategoryTheory.sum_tensor`：sum_tensor {P Q R S : C} {J : Type*} (s : Fin
set J) (f : P ⟶ Q) (g : J -> (R ⟶ S)) : (∑ j in s, g j) otimesₘ f = ∑ j in s, g 
j otimesₘ f
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `CategoryTheory.MonoidalCategory.comp_tensor_id`：comp_tensor_id (f : W ⟶ 
X) (g : X ⟶ Y) : f ≫ g otimesₘ 𝟙 Z = (f otimesₘ 𝟙 Z) ≫ (g otimesₘ 𝟙 Z)
· 使用定理 `CategoryTheory.rightDistributor_hom`：rightDistributor_hom {J : Type} [Fi
ntype J] (f : J -> C) (X : C) : (rightDistributor f X).hom = ∑ j : J, (biproduct
.π f j ▷ X) ≫ biproduct.ι…
· 使用定理 `CategoryTheory.Preadditive.comp_sum`：comp_sum {P Q R : C} {J : Type*} (s
 : Finset J) (f : P ⟶ Q) (g : J -> (Q ⟶ R)) : (f ≫ ∑ j in s, g j) = ∑ j in s, f 
≫ g j
· 使用定理 `CategoryTheory.Preadditive.sum_comp`：sum_comp {P Q R : C} {J : Type*} (s
 : Finset J) (f : J -> (P ⟶ Q)) (g : Q ⟶ R) : (∑ j in s, f j) ≫ g = ∑ j in s, f 
j ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `CategoryTheory.Limits.biproduct.ι_π`：∀ {J : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C] [inst_2 : Decida…
· 使用定理 `CategoryTheory.comp_dite`：comp_dite {P : Prop} [Decidable P] {X Y Z : C}
 (f : X ⟶ Y) (g : P -> (Y ⟶ Z)) (g' : ¬P -> (Y ⟶ Z)) : (f ≫ if h : P then g h el
se g' h) = if …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `Finset.sum_dite_irrel`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] (p : Prop) [inst_1 : Decidable p] (s : Finset ι)   (f : p → ι → M) (g : 
¬p → ι → M)…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
（共 52 条，此处仅展示前 30 条）
-/
theorem leftDistributor_rightDistributor_assoc {J : Type _} [Finite J]
    (X : C) (f : J → C) (Y : C) :
    (leftDistributor X f ⊗ᵢ asIso (𝟙 Y)) ≪≫ rightDistributor _ Y =
      α_ X (⨁ f) Y ≪≫
        (asIso (𝟙 X) ⊗ᵢ rightDistributor _ Y) ≪≫
          leftDistributor X _ ≪≫ biproduct.mapIso fun _ => (α_ _ _ _).symm := by
  classical
  cases nonempty_fintype J
  ext
  simp only [Category.comp_id, Category.assoc, eqToHom_refl, Iso.symm_hom, Iso.trans_hom,
    asIso_hom, comp_zero, comp_dite, Preadditive.sum_comp, Preadditive.comp_sum, sum_tensor,
    tensor_sum, comp_tensor_id, tensorIso_hom, leftDistributor_hom, rightDistributor_hom,
    biproduct.mapIso_hom, biproduct.ι_map, biproduct.ι_π, Finset.sum_dite_irrel,
    Finset.sum_dite_eq', Finset.sum_const_zero, Finset.mem_univ, if_true]
  simp_rw [← tensorHom_id, ← id_tensorHom]
  simp only [← comp_tensor_id, ← id_tensor_comp_assoc, Category.assoc, biproduct.ι_π, comp_dite,
    dite_comp, tensor_dite, dite_tensor]
  simp

@[ext]
/-
**CategoryTheory.leftDistributor_ext_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：leftDistributor_ext_left {J : Type} [Finite J] {X Y : C} {f : J -> C} {g h
 : X otimes ⨁ f ⟶ Y} (w : forall j, (X ◁ biproduct.ι f j) ≫ g = (X ◁ biproduct.ι
 f j) ≫ h) : g = h
参数：w : forall j, (X ◁ biproduct.ι f j) ≫ g = (X ◁ biproduct.ι f j) ≫ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.biproduct_ι_comp_leftDistributor_inv_assoc`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pread
ditive C]   [inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftDistributor_ext_left {J : Type} [Finite J] {X Y : C} {f : J → C} {g h : X ⊗ ⨁ f ⟶ Y}
    (w : ∀ j, (X ◁ biproduct.ι f j) ≫ g = (X ◁ biproduct.ι f j) ≫ h) : g = h := by
  cases nonempty_fintype J
  apply (cancel_epi (leftDistributor X f).inv).mp
  ext
  simp [w]

@[ext]
/-
**CategoryTheory.leftDistributor_ext_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：leftDistributor_ext_right {J : Type} [Finite J] {X Y : C} {f : J -> C} {g 
h : X ⟶ Y otimes ⨁ f} (w : forall j, g ≫ (Y ◁ biproduct.π f j) = h ≫ (Y ◁ biprod
uct.π f j)) : g = h
参数：w : forall j, g ≫ (Y ◁ biproduct.π f j) = h ≫ (Y ◁ biproduct.π f j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.leftDistributor_hom_comp_biproduct_π`：leftDistributor_hom
_comp_biproduct_π {J : Type} [Finite J] (X : C) (f : J -> C) (j : J) : (leftDist
ributor X f).hom ≫ biproduct.π _ j = X ◁ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftDistributor_ext_right {J : Type} [Finite J] {X Y : C} {f : J → C} {g h : X ⟶ Y ⊗ ⨁ f}
    (w : ∀ j, g ≫ (Y ◁ biproduct.π f j) = h ≫ (Y ◁ biproduct.π f j)) : g = h := by
  cases nonempty_fintype J
  apply (cancel_mono (leftDistributor Y f).hom).mp
  ext
  simp [w]

-- One might wonder how many iterated tensor products we need simp lemmas for.
-- The answer is two: this lemma is needed to verify the pentagon identity.
@[ext]
/-
**CategoryTheory.leftDistributor_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftDistributor_ext₂_left {J : Type} [Finite J]
    {X Y Z : C} {f : J → C} {g h : X ⊗ (Y ⊗ ⨁ f) ⟶ Z}
    (w : ∀ j, (X ◁ (Y ◁ biproduct.ι f j)) ≫ g = (X ◁ (Y ◁ biproduct.ι f j)) ≫ h) :
    g = h := by
  apply (cancel_epi (α_ _ _ _).hom).mp
  ext
  simp [w]

@[ext]
/-
**CategoryTheory.leftDistributor_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftDistributor_ext₂_right {J : Type} [Finite J]
    {X Y Z : C} {f : J → C} {g h : X ⟶ Y ⊗ (Z ⊗ ⨁ f)}
    (w : ∀ j, g ≫ (Y ◁ (Z ◁ biproduct.π f j)) = h ≫ (Y ◁ (Z ◁ biproduct.π f j))) :
    g = h := by
  apply (cancel_mono (α_ _ _ _).inv).mp
  ext
  simp [w]

@[ext]
/-
**CategoryTheory.rightDistributor_ext_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：rightDistributor_ext_left {J : Type} [Finite J] {f : J -> C} {X Y : C} {g 
h : (⨁ f) otimes X ⟶ Y} (w : forall j, (biproduct.ι f j ▷ X) ≫ g = (biproduct.ι 
f j ▷ X) ≫ h) : g = h
参数：⨁ f；w : forall j, (biproduct.ι f j ▷ X) ≫ g = (biproduct.ι f j ▷ X) ≫ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext'`：∀ {J : Type w} {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZer
oMorphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.biproduct_ι_comp_rightDistributor_inv_assoc`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Prea
dditive C]   [inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightDistributor_ext_left {J : Type} [Finite J]
    {f : J → C} {X Y : C} {g h : (⨁ f) ⊗ X ⟶ Y}
    (w : ∀ j, (biproduct.ι f j ▷ X) ≫ g = (biproduct.ι f j ▷ X) ≫ h) : g = h := by
  cases nonempty_fintype J
  apply (cancel_epi (rightDistributor f X).inv).mp
  ext
  simp [w]

@[ext]
/-
**CategoryTheory.rightDistributor_ext_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：rightDistributor_ext_right {J : Type} [Finite J] {f : J -> C} {X Y : C} {g
 h : X ⟶ (⨁ f) otimes Y} (w : forall j, g ≫ (biproduct.π f j ▷ Y) = h ≫ (biprodu
ct.π f j ▷ Y)) : g = h
参数：⨁ f；w : forall j, g ≫ (biproduct.π f j ▷ Y) = h ≫ (biproduct.π f j ▷ Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBiproductsOfShape.has_biproduct`：∀ {J : Type w}
 {C : Type uC} {inst : CategoryTheory.Category.{uC', uC} C}   {inst_1 : Category
Theory.Limits.HasZeroMorphisms C} [self : Cate…
· 使用定理 `CategoryTheory.Limits.hasBiproductsOfShape_finite`：∀ {J : Type w} (C : T
ype uC) [inst : CategoryTheory.Category.{uC', uC} C]   [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C] [CategoryThe…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.biproduct.hom_ext`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.Limits.HasZero
Morphisms C] {f : J → C} [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.rightDistributor_hom_comp_biproduct_π`：rightDistributor_h
om_comp_biproduct_π {J : Type} [Finite J] (f : J -> C) (X : C) (j : J) : (rightD
istributor f X).hom ≫ biproduct.π _ j = bi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightDistributor_ext_right {J : Type} [Finite J]
    {f : J → C} {X Y : C} {g h : X ⟶ (⨁ f) ⊗ Y}
    (w : ∀ j, g ≫ (biproduct.π f j ▷ Y) = h ≫ (biproduct.π f j ▷ Y)) : g = h := by
  cases nonempty_fintype J
  apply (cancel_mono (rightDistributor f Y).hom).mp
  ext
  simp [w]

@[ext]
/-
**CategoryTheory.rightDistributor_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightDistributor_ext₂_left {J : Type} [Finite J]
    {f : J → C} {X Y Z : C} {g h : ((⨁ f) ⊗ X) ⊗ Y ⟶ Z}
    (w : ∀ j, ((biproduct.ι f j ▷ X) ▷ Y) ≫ g = ((biproduct.ι f j ▷ X) ▷ Y) ≫ h) :
    g = h := by
  apply (cancel_epi (α_ _ _ _).inv).mp
  ext
  simp [w]

@[ext]
/-
**CategoryTheory.rightDistributor_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightDistributor_ext₂_right {J : Type} [Finite J]
    {f : J → C} {X Y Z : C} {g h : X ⟶ ((⨁ f) ⊗ Y) ⊗ Z}
    (w : ∀ j, g ≫ ((biproduct.π f j ▷ Y) ▷ Z) = h ≫ ((biproduct.π f j ▷ Y) ▷ Z)) :
    g = h := by
  apply (cancel_mono (α_ _ _ _).hom).mp
  ext
  simp [w]

end CategoryTheory

