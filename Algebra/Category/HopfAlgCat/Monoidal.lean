/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.BialgCat.Monoidal
public import Mathlib.Algebra.Category.HopfAlgCat.Basic
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# The monoidal structure on the category of Hopf algebras

In `Mathlib/RingTheory/HopfAlgebra/TensorProduct.lean`, given two Hopf `R`-algebras `A, B`, we
define a Hopf `R`-algebra instance on `A ⊗[R] B`.

Here, we use this to declare a `MonoidalCategory` instance on the category of Hopf algebras, via
the existing monoidal structure on `BialgCat`.
-/

@[expose] public section

universe u

namespace HopfAlgCat
open CategoryTheory MonoidalCategory TensorProduct

variable (R : Type u) [CommRing R]

/--
Instance `instMonoidalCategoryStruct` / 实例 `instMonoidalCategoryStruct`

English:
instance instMonoidalCategoryStruct
  signature: :
  body: of R (X otimes[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Bialgebra.TensorProduct.map f.1 g.1)
  tensorUnit := of R R
  associator X Y Z := (Bialgebra.TensorProduct.assoc R R X Y Z).toHopfAlgIso
  leftUnitor X := (Bialgebra.TensorProduct.lid R X).toHopfAlgIso
  rightUnitor X := (Bialgebra.TensorProduct.rid R R X).toHopfAlgIso

中文:
实例 instMonoidalCategoryStruct
  签名: :
  定义体: of R (X otimes[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Bialgebra.TensorProduct.map f.1 g.1)
  tensorUnit := of R R
  associator X Y Z := (Bialgebra.TensorProduct.assoc R R X Y Z).toHopfAlgIso
  leftUnitor X := (Bialgebra.TensorProduct.lid R X).toHopfAlgIso
  rightUnitor X := (Bialgebra.TensorProduct.rid R R X).toHopfAlgIso
-/
@[simps] noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (HopfAlgCat R) where
  tensorObj X Y := of R (X otimes[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Bialgebra.TensorProduct.map f.1 g.1)
  tensorUnit := of R R
  associator X Y Z := (Bialgebra.TensorProduct.assoc R R X Y Z).toHopfAlgIso
  leftUnitor X := (Bialgebra.TensorProduct.lid R X).toHopfAlgIso
  rightUnitor X := (Bialgebra.TensorProduct.rid R R X).toHopfAlgIso

/-- The data needed to induce a `MonoidalCategory` structure via
`HopfAlgCat.instMonoidalCategoryStruct` and the forgetful functor to bialgebras. -/
@[simps]
/--
Definition of `MonoidalCategory.inducingFunctorData` / `MonoidalCategory.inducingFunctorData` 的定义

English:
definition MonoidalCategory.inducingFunctorData
  signature: :
  body: Iso.refl _
  whiskerLeft_eq _ _ _ _ := by ext; rfl
  whiskerRight_eq _ _ := by ext; rfl
  tensorHom_eq _ _ := by ext; rfl
  εIso := Iso.refl _
associator_eq _ _ _ := BialgCat.Hom.ext BialgHom.coe_linearMap_injective
TensorProduct.ext TensorProduct.ext (by ext; rfl)
leftUnitor_eq _ := BialgCat.Hom.ext BialgHom.coe_linearMap_injective
    TensorProduct.ext (by ext; rfl)
rightUnitor_eq _ := BialgCat.Hom.ext BialgHom.coe_linearMap_injective
    TensorProduct.ext (by ext; rfl)

中文:
定义 幺半群范畴.inducingFunctorData
  签名: :
  定义体: Iso.refl _
  whiskerLeft_eq _ _ _ _ := by ext; rfl
  whiskerRight_eq _ _ := by ext; rfl
  tensorHom_eq _ _ := by ext; rfl
  εIso := Iso.refl _
associator_eq _ _ _ := BialgCat.Hom.ext BialgHom.coe_linearMap_injective
TensorProduct.ext TensorProduct.ext (by ext; rfl)
leftUnitor_eq _ := BialgCat.Hom.ext BialgHom.coe_linearMap_injective
    TensorProduct.ext (by ext; rfl)
rightUnitor_eq _ := BialgCat.Hom.ext BialgHom.coe_linearMap_injective
    TensorProduct.ext (by ext; rfl)
-/
noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (HopfAlgCat R) (BialgCat R)) where
  μIso _ _ := Iso.refl _
  whiskerLeft_eq _ _ _ _ := by ext; rfl
  whiskerRight_eq _ _ := by ext; rfl
  tensorHom_eq _ _ := by ext; rfl
  εIso := Iso.refl _
associator_eq _ _ _ := BialgCat.Hom.ext BialgHom.coe_linearMap_injective
TensorProduct.ext TensorProduct.ext (by ext; rfl)
leftUnitor_eq _ := BialgCat.Hom.ext BialgHom.coe_linearMap_injective
    TensorProduct.ext (by ext; rfl)
rightUnitor_eq _ := BialgCat.Hom.ext BialgHom.coe_linearMap_injective
    TensorProduct.ext (by ext; rfl)

/--
Instance `instMonoidalCategory` / 实例 `instMonoidalCategory`

English:
instance instMonoidalCategory
  signature: : MonoidalCategory (HopfAlgCat R)
  body: Monoidal.induced (forget₂ _ (BialgCat R)) (MonoidalCategory.inducingFunctorData R)

中文:
实例 instMonoidalCategory
  签名: : 幺半群范畴 (HopfAlg范畴 R)
  定义体: Monoidal.induced (forget₂ _ (BialgCat R)) (MonoidalCategory.inducingFunctorData R)

Depends on / 依赖: BialgCat, Monoidal, Monoidal.induced, MonoidalCategory, MonoidalCategory.inducingFunctorData, induced, inducingFunctorData
-/
noncomputable instance instMonoidalCategory : MonoidalCategory (HopfAlgCat R) :=
  Monoidal.induced (forget₂ _ (BialgCat R)) (MonoidalCategory.inducingFunctorData R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (HopfAlgCat R) (BialgCat R)).Monoidal

中文:
实例 :
  签名: (forget₂ (HopfAlg范畴 R) (Bialg范畴 R)).幺半群
-/
noncomputable instance : (forget₂ (HopfAlgCat R) (BialgCat R)).Monoidal where

end HopfAlgCat
