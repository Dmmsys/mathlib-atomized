/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Products.Basic

/-!
The associator functor `((C × D) × E) ⥤ (C × (D × E))` and its inverse form an equivalence.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory

namespace CategoryTheory.prod

open scoped CategoryTheory.Prod

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] (E : Type u₃)
  [Category.{v₃} E]

/-- The associator functor `(C × D) × E ⥤ C × (D × E)`.
-/
@[simps]
/-
**CategoryTheory.prod.associator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.prod`
。
形式化陈述：associator : (C × D) × E ⥤ C × D × E where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator functor `(C × D) × E ⥤ C × (D × E)`.
-/
def associator : (C × D) × E ⥤ C × D × E where
  obj X := (X.1.1, (X.1.2, X.2))
  map := @fun _ _ f => f.1.1 ×ₘ (f.1.2 ×ₘ f.2)

/-- The inverse associator functor `C × (D × E) ⥤ (C × D) × E `.
-/
@[simps]
/-
**CategoryTheory.prod.inverseAssociator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.prod`。
形式化陈述：inverseAssociator : C × D × E ⥤ (C × D) × E where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse associator functor `C × (D × E) ⥤ (C × D) × E `.
-/
def inverseAssociator : C × D × E ⥤ (C × D) × E where
  obj X := ((X.1, X.2.1), X.2.2)
  map := @fun _ _ f => (f.1 ×ₘ f.2.1) ×ₘ f.2.2

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories expressing associativity of products of categories.
-/
@[simps]
/-
**CategoryTheory.prod.associativity** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.pr
od`。
形式化陈述：associativity : (C × D) × E ≌ C × D × E where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories expressing associativity of products of categories
.
-/
def associativity : (C × D) × E ≌ C × D × E where
  functor := associator C D E
  inverse := inverseAssociator C D E
  unitIso := Iso.refl _
  counitIso := Iso.refl _
/-
**CategoryTheory.prod.associatorIsEquivalence** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.prod`。
形式化陈述：associatorIsEquivalence : (associator C D E).IsEquivalence
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance associatorIsEquivalence : (associator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).functor.IsEquivalence)
/-
**CategoryTheory.prod.inverseAssociatorIsEquivalence** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.prod`。
形式化陈述：inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
instance inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).inverse.IsEquivalence)

-- TODO pentagon natural transformation? ...satisfying?

variable (A : Type u₄) [Category.{v₄} A]

/-- The associator isomorphism is compatible with `prodFunctorToFunctorProd`. -/
@[simps!]
/-
**CategoryTheory.prod.prodFunctorToFunctorProdAssociator** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.prod`。
形式化陈述：prodFunctorToFunctorProdAssociator : (associativity _ _ _).functor ⋙ ((𝟭 _
).prod (prodFunctorToFunctorProd A D E) ⋙ (prodFunctorToFunctorProd A C (D × E))
) ≅ (prodFunctorToFunctorProd A C D).prod (𝟭 _) ⋙ (prodFunctorToFunctorProd A (C
 × D) E) ⋙ (associativity C D E).congrRight.functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator isomorphism is compatible with `prodFunctorToFunctorProd`.
-/
def prodFunctorToFunctorProdAssociator :
    (associativity _ _ _).functor ⋙ ((𝟭 _).prod (prodFunctorToFunctorProd A D E) ⋙
      (prodFunctorToFunctorProd A C (D × E))) ≅
        (prodFunctorToFunctorProd A C D).prod (𝟭 _) ⋙ (prodFunctorToFunctorProd A (C × D) E) ⋙
          (associativity C D E).congrRight.functor :=
  Iso.refl _

/-- The associator isomorphism is compatible with `functorProdToProdFunctor`. -/
@[simps!]
/-
**CategoryTheory.prod.functorProdToProdFunctorAssociator** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.prod`。
形式化陈述：functorProdToProdFunctorAssociator : (associativity _ _ _).congrRight.func
tor ⋙ functorProdToProdFunctor A C (D × E) ⋙ (𝟭 _).prod (functorProdToProdFuncto
r A D E) ≅ functorProdToProdFunctor A (C × D) E ⋙ (functorProdToProdFunctor A C 
D).prod (𝟭 _) ⋙ (associativity _ _ _).functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator isomorphism is compatible with `functorProdToProdFunctor`.
-/
def functorProdToProdFunctorAssociator :
    (associativity _ _ _).congrRight.functor ⋙ functorProdToProdFunctor A C (D × E) ⋙
      (𝟭 _).prod (functorProdToProdFunctor A D E) ≅
        functorProdToProdFunctor A (C × D) E ⋙ (functorProdToProdFunctor A C D).prod (𝟭 _) ⋙
          (associativity _ _ _).functor :=
  Iso.refl _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence swapping the second and third categories in `(A × C) × (D × E)`. This follows
the definition of `MonoidalCategory.tensorμ`. -/
@[simps!]
/-
**CategoryTheory.prod.prod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence swapping the second and third categories in `(A × C) × (D × E)`.
 This follows
the definition of `MonoidalCategory.tensorμ`.
-/
def prodμ : (A × C) × (D × E) ≌ (A × D) × (C × E) :=
  (associativity ..).trans <|
    (Equivalence.refl.prod (associativity ..).symm).trans <|
      (Equivalence.refl.prod <| (Prod.braiding C D).prod (Equivalence.refl)).trans <|
        (Equivalence.refl.prod (associativity ..)).trans <| (associativity ..).symm

end CategoryTheory.prod

