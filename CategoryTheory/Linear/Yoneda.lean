/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# The Yoneda embedding for `R`-linear categories

The Yoneda embedding for `R`-linear categories `C`,
sends an object `X : C` to the `ModuleCat R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `ModuleCat.of R (unop Y ⟶ X)`.

TODO: `linearYoneda R C` is `R`-linear.
TODO: In fact, `linearYoneda` itself is additive and `R`-linear.
-/

@[expose] public section


universe w v u

open Opposite CategoryTheory.Functor

namespace CategoryTheory

variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
variable (C)

/-- The Yoneda embedding for `R`-linear categories `C`
sending an object `X : C` to the `ModuleCat R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `ModuleCat.of R (unop Y ⟶ X)`. -/
@[simps]
/-
**CategoryTheory.linearYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：linearYoneda : C ⥤ Cᵒᵖ ⥤ ModuleCat R where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Yoneda embedding for `R`-linear categories `C`
sending an object `X : C` to the `ModuleCat R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `ModuleCat.of R (unop Y ⟶ X)`.
-/
def linearYoneda : C ⥤ Cᵒᵖ ⥤ ModuleCat R where
  obj X :=
    { obj := fun Y => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.leftComp R _ f.unop) }
  map {X₁ X₂} f :=
    { app := fun Y => @ModuleCat.ofHom R _ (Y.unop ⟶ X₁) (Y.unop ⟶ X₂) _ _ _ _
        (Linear.rightComp R _ f) }

/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `Y : Cᵒᵖ` to the `ModuleCat R`-valued copresheaf on `C`,
with value on `X : C` given by `ModuleCat.of R (unop Y ⟶ X)`. -/
@[simps]
/-
**CategoryTheory.linearCoyoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：linearCoyoneda : Cᵒᵖ ⥤ C ⥤ ModuleCat R where obj Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Yoneda embedding for `R`-linear categories `C`,
sending an object `Y : Cᵒᵖ` to the `ModuleCat R`-valued copresheaf on `C`,
with value on `X : C` given by `ModuleCat.of R (unop Y ⟶ X)`.
-/
def linearCoyoneda : Cᵒᵖ ⥤ C ⥤ ModuleCat R where
  obj Y :=
    { obj := fun X => ModuleCat.of R (unop Y ⟶ X)
      map := fun f => ModuleCat.ofHom (Linear.rightComp R _ f) }
  map {Y₁ Y₂} f :=
    { app := fun X => @ModuleCat.ofHom R _ (unop Y₁ ⟶ X) (unop Y₂ ⟶ X) _ _ _ _
        (Linear.leftComp _ _ f.unop) }
/-
**CategoryTheory.linearYoneda_obj_additive** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：∀ (R : Type w) [inst : Ring R] (C : Type u) [inst_1 : CategoryTheory.Categ
ory.{v, u} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : CategoryTheory
.Linear R C] (X : C),   ((CategoryTheory.linearYoneda R C).obj X).Additive
参数：R : Type w；C : Type u；X : C；(CategoryTheory.linearYoneda R C).obj X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.linearYoneda_obj_map`：∀ (R : Type w) [inst : Ring R] (C :
 Type u) [inst_1 : CategoryTheory.Category.{v, u} C]   [inst_2 : CategoryTheory.
Preadditive C] [inst_3 : …
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Linear.leftComp_apply`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (R : Type w)   [i
nst_2 : Semiring R] [inst_…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
-/
instance linearYoneda_obj_additive (X : C) : ((linearYoneda R C).obj X).Additive where
/-
**CategoryTheory.linearCoyoneda_obj_additive** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：∀ (R : Type w) [inst : Ring R] (C : Type u) [inst_1 : CategoryTheory.Categ
ory.{v, u} C]   [inst_2 : CategoryTheory.Preadditive C] [inst_3 : CategoryTheory
.Linear R C] (Y : Cᵒᵖ),   ((CategoryTheory.linearCoyoneda R C).obj Y).Additive
参数：R : Type w；C : Type u；Y : Cᵒᵖ；(CategoryTheory.linearCoyoneda R C).obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.linearCoyoneda_obj_map`：∀ (R : Type w) [inst : Ring R] (C
 : Type u) [inst_1 : CategoryTheory.Category.{v, u} C]   [inst_2 : CategoryTheor
y.Preadditive C] [inst_3 : …
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.Linear.rightComp_apply`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (R : Type w)   [
inst_2 : Semiring R] [inst_…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
-/
instance linearCoyoneda_obj_additive (Y : Cᵒᵖ) : ((linearCoyoneda R C).obj Y).Additive where

@[simp]
/-
**CategoryTheory.whiskering_linearYoneda** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：whiskering_linearYoneda : linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (
forget (ModuleCat.{v} R)) = yoneda
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskering_linearYoneda :
    linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = yoneda :=
  rfl

@[simp]
/-
**CategoryTheory.whiskering_linearYoneda** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：whiskering_linearYoneda : linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (
forget (ModuleCat.{v} R)) = yoneda
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskering_linearYoneda₂ :
    linearYoneda R C ⋙ (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) =
      preadditiveYoneda :=
  rfl

@[simp]
/-
**CategoryTheory.whiskering_linearCoyoneda** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：whiskering_linearCoyoneda : linearCoyoneda R C ⋙ (whiskeringRight _ _ _).o
bj (forget (ModuleCat.{v} R)) = coyoneda
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskering_linearCoyoneda :
    linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = coyoneda :=
  rfl

@[simp]
/-
**CategoryTheory.whiskering_linearCoyoneda** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：whiskering_linearCoyoneda : linearCoyoneda R C ⋙ (whiskeringRight _ _ _).o
bj (forget (ModuleCat.{v} R)) = coyoneda
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskering_linearCoyoneda₂ :
    linearCoyoneda R C ⋙
        (whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) =
      preadditiveCoyoneda :=
  rfl
/-
**CategoryTheory.full_linearYoneda** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：full_linearYoneda : (linearYoneda R C).Full
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Full.of_comp_faithful`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
-/
instance full_linearYoneda : (linearYoneda R C).Full :=
  let _ : Functor.Full (linearYoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Yoneda.yoneda_full
  Functor.Full.of_comp_faithful (linearYoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))
/-
**CategoryTheory.full_linearCoyoneda** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：full_linearCoyoneda : (linearCoyoneda R C).Full
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Full.of_comp_faithful`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
-/
instance full_linearCoyoneda : (linearCoyoneda R C).Full :=
  let _ : Functor.Full (linearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj
    (forget (ModuleCat.{v} R))) := Coyoneda.coyoneda_full
  Functor.Full.of_comp_faithful (linearCoyoneda R C)
    ((whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)))
/-
**CategoryTheory.faithful_linearYoneda** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：faithful_linearYoneda : (linearYoneda R C).Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Faithful.of_comp_eq`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.whiskering_linearYoneda`：whiskering_linearYoneda : linear
Yoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = yoneda
-/
instance faithful_linearYoneda : (linearYoneda R C).Faithful :=
  Functor.Faithful.of_comp_eq (whiskering_linearYoneda R C)
/-
**CategoryTheory.faithful_linearCoyoneda** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry`。
形式化陈述：faithful_linearCoyoneda : (linearCoyoneda R C).Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Faithful.of_comp_eq`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.whiskering_linearCoyoneda`：whiskering_linearCoyoneda : li
nearCoyoneda R C ⋙ (whiskeringRight _ _ _).obj (forget (ModuleCat.{v} R)) = coyo
neda
-/
instance faithful_linearCoyoneda : (linearCoyoneda R C).Faithful :=
  Functor.Faithful.of_comp_eq (whiskering_linearCoyoneda R C)

end CategoryTheory

