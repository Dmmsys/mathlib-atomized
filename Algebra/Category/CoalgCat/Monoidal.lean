/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.CoalgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# The monoidal category structure on `R`-coalgebras

In `Mathlib/RingTheory/Coalgebra/TensorProduct.lean`, given two `R`-coalgebras `M, N`, we define a
coalgebra instance on `M ⊗[R] N`, as well as the tensor product of two `CoalgHom`s as a
`CoalgHom`, and the associator and left/right unitors for coalgebras as `CoalgEquiv`s.

In this file, we declare a `MonoidalCategory` instance on the category of coalgebras, with data
fields given by the definitions in `Mathlib/RingTheory/Coalgebra/TensorProduct.lean`, and Prop
fields proved by pulling back the `MonoidalCategory` instance on the category of modules,
using `Monoidal.induced`.

-/

@[expose] public section

universe v u

namespace CoalgCat
variable (R : Type u) [CommRing R]

open CategoryTheory Coalgebra
open scoped TensorProduct MonoidalCategory

@[simps]
/--
Instance `instMonoidalCategoryStruct` / 实例 `instMonoidalCategoryStruct`

English:
instance instMonoidalCategoryStruct
  signature: :
  body: of R (X otimes[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Coalgebra.TensorProduct.map f.1 g.1)
  tensorUnit := CoalgCat.of R R
  associator X Y Z := (Coalgebra.TensorProduct.assoc R R X Y Z).toCoalgIso
  leftUnitor X := 

中文:
实例 instMonoidalCategoryStruct
  签名: :
  定义体: of R (X otimes[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Coalgebra.TensorProduct.map f.1 g.1)
  tensorUnit := CoalgCat.of R R
  associator X Y Z := (Coalgebra.TensorProduct.assoc R R X Y Z).toCoalgIso
  leftUnitor X := 

Depends on / 依赖: otimes
-/
noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (CoalgCat R) where
  tensorObj X Y := of R (X otimes[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Coalgebra.TensorProduct.map f.1 g.1)
  tensorUnit := CoalgCat.of R R
  associator X Y Z := (Coalgebra.TensorProduct.assoc R R X Y Z).toCoalgIso
  leftUnitor X := (Coalgebra.TensorProduct.lid R X).toCoalgIso
  rightUnitor X := (Coalgebra.TensorProduct.rid R R X).toCoalgIso

/-- The data needed to induce a `MonoidalCategory` structure via
`CoalgCat.instMonoidalCategoryStruct` and the forgetful functor to modules. -/
@[simps]
/--
Definition of `MonoidalCategory.inducingFunctorData` / `MonoidalCategory.inducingFunctorData` 的定义

English:
definition MonoidalCategory.inducingFunctorData
  signature: :
  body: Iso.refl _
  whiskerLeft_eq X Y Z f := by ext; rfl
  whiskerRight_eq X f := by ext; rfl
  tensorHom_eq f g := by ext; rfl
  εIso := Iso.refl _
associator_eq X Y Z := ModuleCat.hom_ext TensorProduct.ext TensorProduct.ext by ext; rfl
leftUnitor_eq X := ModuleCat.hom_ext TensorProduct.ext by ext; rfl
r

中文:
定义 幺半群范畴.inducingFunctorData
  签名: :
  定义体: Iso.refl _
  whiskerLeft_eq X Y Z f := by ext; rfl
  whiskerRight_eq X f := by ext; rfl
  tensorHom_eq f g := by ext; rfl
  εIso := Iso.refl _
associator_eq X Y Z := ModuleCat.hom_ext TensorProduct.ext TensorProduct.ext by ext; rfl
leftUnitor_eq X := ModuleCat.hom_ext TensorProduct.ext by ext; rfl
r
-/
noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (CoalgCat R) (ModuleCat R)) where
  μIso _ _ := Iso.refl _
  whiskerLeft_eq X Y Z f := by ext; rfl
  whiskerRight_eq X f := by ext; rfl
  tensorHom_eq f g := by ext; rfl
  εIso := Iso.refl _
associator_eq X Y Z := ModuleCat.hom_ext TensorProduct.ext TensorProduct.ext by ext; rfl
leftUnitor_eq X := ModuleCat.hom_ext TensorProduct.ext by ext; rfl
rightUnitor_eq X := ModuleCat.hom_ext TensorProduct.ext by ext; rfl

/--
Instance `instMonoidalCategory` / 实例 `instMonoidalCategory`

English:
instance instMonoidalCategory
  signature: : MonoidalCategory (CoalgCat R)
  body: Monoidal.induced (forget₂ _ (ModuleCat R)) (MonoidalCategory.inducingFunctorData R)

中文:
实例 instMonoidalCategory
  签名: : 幺半群范畴 (余alg范畴 R)
  定义体: Monoidal.induced (forget₂ _ (ModuleCat R)) (MonoidalCategory.inducingFunctorData R)

Depends on / 依赖: ModuleCat, Monoidal, Monoidal.induced, MonoidalCategory, MonoidalCategory.inducingFunctorData, induced, inducingFunctorData
-/
noncomputable instance instMonoidalCategory : MonoidalCategory (CoalgCat R) :=
  Monoidal.induced (forget₂ _ (ModuleCat R)) (MonoidalCategory.inducingFunctorData R)

end CoalgCat
