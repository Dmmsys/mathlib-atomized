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
/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: : (C × D) × E ⥤ C × D × E where
  body: (X.1.1, (X.1.2, X.2))
  map := @fun _ _ f => f.1.1 ×ₘ (f.1.2 ×ₘ f.2)

中文:
定义 associator
  签名: : (C × D) × E ⥤ C × D × E where
  定义体: (X.1.1, (X.1.2, X.2))
  map := @fun _ _ f => f.1.1 ×ₘ (f.1.2 ×ₘ f.2)
-/
def associator : (C × D) × E ⥤ C × D × E where
  obj X := (X.1.1, (X.1.2, X.2))
  map := @fun _ _ f => f.1.1 ×ₘ (f.1.2 ×ₘ f.2)

/-- The inverse associator functor `C × (D × E) ⥤ (C × D) × E `.
-/
@[simps]
/--
Definition of `inverseAssociator` / `inverseAssociator` 的定义

English:
definition inverseAssociator
  signature: : C × D × E ⥤ (C × D) × E where
  body: ((X.1, X.2.1), X.2.2)
  map := @fun _ _ f => (f.1 ×ₘ f.2.1) ×ₘ f.2.2

中文:
定义 inverseAssociator
  签名: : C × D × E ⥤ (C × D) × E where
  定义体: ((X.1, X.2.1), X.2.2)
  map := @fun _ _ f => (f.1 ×ₘ f.2.1) ×ₘ f.2.2
-/
def inverseAssociator : C × D × E ⥤ (C × D) × E where
  obj X := ((X.1, X.2.1), X.2.2)
  map := @fun _ _ f => (f.1 ×ₘ f.2.1) ×ₘ f.2.2

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories expressing associativity of products of categories.
-/
@[simps]
/--
Definition of `associativity` / `associativity` 的定义

English:
definition associativity
  signature: : (C × D) × E ≌ C × D × E where
  body: associator C D E
  inverse := inverseAssociator C D E
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 associativity
  签名: : (C × D) × E ≌ C × D × E where
  定义体: associator C D E
  inverse := inverseAssociator C D E
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: associator
-/
def associativity : (C × D) × E ≌ C × D × E where
  functor := associator C D E
  inverse := inverseAssociator C D E
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/--
Instance `associatorIsEquivalence` / 实例 `associatorIsEquivalence`

English:
instance associatorIsEquivalence
  signature: : (associator C D E).IsEquivalence
  body: (by infer_instance : (associativity C D E).functor.IsEquivalence)

中文:
实例 associatorIsEquivalence
  签名: : (associator C D E).IsEquivalence
  定义体: (by infer_instance : (associativity C D E).functor.IsEquivalence)

Depends on / 依赖: IsEquivalence, associativity, functor, functor.IsEquivalence, infer_instance
-/
instance associatorIsEquivalence : (associator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).functor.IsEquivalence)

/--
Instance `inverseAssociatorIsEquivalence` / 实例 `inverseAssociatorIsEquivalence`

English:
instance inverseAssociatorIsEquivalence
  signature: : (inverseAssociator C D E).IsEquivalence
  body: (by infer_instance : (associativity C D E).inverse.IsEquivalence)

中文:
实例 inverseAssociatorIsEquivalence
  签名: : (inverseAssociator C D E).IsEquivalence
  定义体: (by infer_instance : (associativity C D E).inverse.IsEquivalence)

Depends on / 依赖: IsEquivalence, associativity, infer_instance, inverse, inverse.IsEquivalence
-/
instance inverseAssociatorIsEquivalence : (inverseAssociator C D E).IsEquivalence :=
  (by infer_instance : (associativity C D E).inverse.IsEquivalence)

-- TODO pentagon natural transformation? ...satisfying?

variable (A : Type u₄) [Category.{v₄} A]

/-- The associator isomorphism is compatible with `prodFunctorToFunctorProd`. -/
@[simps!]
/--
Definition of `prodFunctorToFunctorProdAssociator` / `prodFunctorToFunctorProdAssociator` 的定义

English:
definition prodFunctorToFunctorProdAssociator
  signature: :
  body: Iso.refl _

中文:
定义 prodFunctorToFunctorProdAssociator
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def prodFunctorToFunctorProdAssociator :
    (associativity _ _ _).functor ⋙ ((𝟭 _).prod (prodFunctorToFunctorProd A D E) ⋙
      (prodFunctorToFunctorProd A C (D × E))) ≅
        (prodFunctorToFunctorProd A C D).prod (𝟭 _) ⋙ (prodFunctorToFunctorProd A (C × D) E) ⋙
          (associativity C D E).congrRight.functor :=
  Iso.refl _

/-- The associator isomorphism is compatible with `functorProdToProdFunctor`. -/
@[simps!]
/--
Definition of `functorProdToProdFunctorAssociator` / `functorProdToProdFunctorAssociator` 的定义

English:
definition functorProdToProdFunctorAssociator
  signature: :
  body: Iso.refl _

#adaptation_note

中文:
定义 functorProdToProdFunctorAssociator
  签名: :
  定义体: Iso.refl _

#adaptation_note

Depends on / 依赖: Iso.refl
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
/--
Definition of `prodμ` / `prodμ` 的定义

English:
definition prodμ
  signature: : (A × C) × (D × E) ≌ (A × D) × (C × E)
  body: (associativity ..).trans
(Equivalence.refl.prod (associativity ..).symm).trans
(Equivalence.refl.prod <| (Prod.braiding C D).prod (Equivalence.refl)).trans
(Equivalence.refl.prod (associativity ..)).trans (associativity ..).symm

中文:
定义 prodμ
  签名: : (A × C) × (D × E) ≌ (A × D) × (C × E)
  定义体: (associativity ..).trans
(Equivalence.refl.prod (associativity ..).symm).trans
(Equivalence.refl.prod <| (Prod.braiding C D).prod (Equivalence.refl)).trans
(Equivalence.refl.prod (associativity ..)).trans (associativity ..).symm

Depends on / 依赖: Equivalence, Equivalence.refl, Equivalence.refl.prod, Prod.braiding, associativity, braiding
-/
def prodμ : (A × C) × (D × E) ≌ (A × D) × (C × E) :=
(associativity ..).trans
(Equivalence.refl.prod (associativity ..).symm).trans
(Equivalence.refl.prod <| (Prod.braiding C D).prod (Equivalence.refl)).trans
(Equivalence.refl.prod (associativity ..)).trans (associativity ..).symm

end CategoryTheory.prod
