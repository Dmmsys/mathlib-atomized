/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Category.AlgCat.Monoidal
public import Mathlib.Algebra.Category.BialgCat.Basic
public import Mathlib.Algebra.Category.CoalgCat.Monoidal
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# The monoidal structure on the category of bialgebras

In `Mathlib/RingTheory/Bialgebra/TensorProduct.lean`, given two `R`-bialgebras `A, B`, we define a
bialgebra instance on `A ⊗[R] B` as well as the tensor product of two `BialgHom`s as a
`BialgHom`, and the associator and left/right unitors for bialgebras as `BialgEquiv`s.
In this file, we declare a `MonoidalCategory` instance on the category of bialgebras, with data
fields given by the definitions in `Mathlib/RingTheory/Bialgebra/TensorProduct.lean`, and Prop
fields proved by pulling back the `MonoidalCategory` instance on the category of algebras,
using `Monoidal.induced`.

-/

@[expose] public section

universe u

namespace BialgCat
open CategoryTheory MonoidalCategory TensorProduct

variable (R : Type u) [CommRing R]

@[simps]
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
  associator X Y Z := (Bialgebra.TensorProduct.assoc R R X Y Z).toBialgIso
  leftUnitor X := (Bialgebra.TensorProduct.lid R X).toBialgIso
  rightUnitor X := (Bialgebra.TensorProduct.rid R R X).toBialgIso

中文:
实例 instMonoidalCategoryStruct
  签名: :
  定义体: of R (X otimes[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Bialgebra.TensorProduct.map f.1 g.1)
  tensorUnit := of R R
  associator X Y Z := (Bialgebra.TensorProduct.assoc R R X Y Z).toBialgIso
  leftUnitor X := (Bialgebra.TensorProduct.lid R X).toBialgIso
  rightUnitor X := (Bialgebra.TensorProduct.rid R R X).toBialgIso

Depends on / 依赖: otimes
-/
noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (BialgCat R) where
  tensorObj X Y := of R (X otimes[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Bialgebra.TensorProduct.map f.1 g.1)
  tensorUnit := of R R
  associator X Y Z := (Bialgebra.TensorProduct.assoc R R X Y Z).toBialgIso
  leftUnitor X := (Bialgebra.TensorProduct.lid R X).toBialgIso
  rightUnitor X := (Bialgebra.TensorProduct.rid R R X).toBialgIso

/-- The data needed to induce a `MonoidalCategory` structure via
`BialgCat.instMonoidalCategoryStruct` and the forgetful functor to algebras. -/
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
associator_eq _ _ _ := AlgCat.hom_ext _ Algebra.TensorProduct.ext
    (Algebra.TensorProduct.ext (by ext; rfl) (by ext; rfl)) (by ext; rfl)
leftUnitor_eq _ := AlgCat.hom_ext _ Algebra.TensorProduct.ext rfl (by ext; rfl)
rightUnitor_eq _ := AlgCat.hom_ext _ Algebra.TensorProduct.ext (by ext; rfl) rfl

中文:
定义 幺半群范畴.inducingFunctorData
  签名: :
  定义体: Iso.refl _
  whiskerLeft_eq _ _ _ _ := by ext; rfl
  whiskerRight_eq _ _ := by ext; rfl
  tensorHom_eq _ _ := by ext; rfl
  εIso := Iso.refl _
associator_eq _ _ _ := AlgCat.hom_ext _ Algebra.TensorProduct.ext
    (Algebra.TensorProduct.ext (by ext; rfl) (by ext; rfl)) (by ext; rfl)
leftUnitor_eq _ := AlgCat.hom_ext _ Algebra.TensorProduct.ext rfl (by ext; rfl)
rightUnitor_eq _ := AlgCat.hom_ext _ Algebra.TensorProduct.ext (by ext; rfl) rfl

Depends on / 依赖: Iso.refl
-/
noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (BialgCat R) (AlgCat R)) where
  μIso _ _ := Iso.refl _
  whiskerLeft_eq _ _ _ _ := by ext; rfl
  whiskerRight_eq _ _ := by ext; rfl
  tensorHom_eq _ _ := by ext; rfl
  εIso := Iso.refl _
associator_eq _ _ _ := AlgCat.hom_ext _ Algebra.TensorProduct.ext
    (Algebra.TensorProduct.ext (by ext; rfl) (by ext; rfl)) (by ext; rfl)
leftUnitor_eq _ := AlgCat.hom_ext _ Algebra.TensorProduct.ext rfl (by ext; rfl)
rightUnitor_eq _ := AlgCat.hom_ext _ Algebra.TensorProduct.ext (by ext; rfl) rfl

/--
Instance `instMonoidalCategory` / 实例 `instMonoidalCategory`

English:
instance instMonoidalCategory
  signature: : MonoidalCategory (BialgCat R)
  body: Monoidal.induced (forget₂ _ (AlgCat R)) (MonoidalCategory.inducingFunctorData R)

中文:
实例 instMonoidalCategory
  签名: : 幺半群范畴 (Bialg范畴 R)
  定义体: Monoidal.induced (forget₂ _ (AlgCat R)) (MonoidalCategory.inducingFunctorData R)

Depends on / 依赖: AlgCat, Monoidal, Monoidal.induced, MonoidalCategory, MonoidalCategory.inducingFunctorData, induced, inducingFunctorData
-/
noncomputable instance instMonoidalCategory : MonoidalCategory (BialgCat R) :=
  Monoidal.induced (forget₂ _ (AlgCat R)) (MonoidalCategory.inducingFunctorData R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (BialgCat R) (AlgCat R)).Monoidal

中文:
实例 :
  签名: (forget₂ (Bialg范畴 R) (Alg范畴 R)).幺半群
-/
noncomputable instance : (forget₂ (BialgCat R) (AlgCat R)).Monoidal where

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (BialgCat R) (CoalgCat R)).Monoidal
  body: Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _ }

中文:
实例 :
  签名: (forget₂ (Bialg范畴 R) (余alg范畴 R)).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _ }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
noncomputable instance : (forget₂ (BialgCat R) (CoalgCat R)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _ }

end BialgCat
