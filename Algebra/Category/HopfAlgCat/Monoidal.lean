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

/-
**HopfAlgCat.instMonoidalCategoryStruct** 是 Mathlib 中的一个定义，位于命名空间 `HopfAlgCat`。
形式化陈述：(R : Type u) → [inst : CommRing R] → CategoryTheory.MonoidalCategoryStruct
 (HopfAlgCat R)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simps] noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (HopfAlgCat R) where
  tensorObj X Y := of R (X ⊗[R] Y)
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
/-
**HopfAlgCat.MonoidalCategory.inducingFunctorData** 是 Mathlib 中的一个定义，位于命名空间 `Hop
fAlgCat.MonoidalCategory`。
形式化陈述：(R : Type u) →   [inst : CommRing R] → CategoryTheory.Monoidal.InducingFun
ctorData (CategoryTheory.forget₂ (HopfAlgCat R) (BialgCat R))
参数：HopfAlgCat R；BialgCat R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data needed to induce a `MonoidalCategory` structure via
`HopfAlgCat.instMonoidalCategoryStruct` and the forgetful functor to bialgebras.
-/
noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (HopfAlgCat R) (BialgCat R)) where
  μIso _ _ := Iso.refl _
  whiskerLeft_eq _ _ _ _ := by ext; rfl
  whiskerRight_eq _ _ := by ext; rfl
  tensorHom_eq _ _ := by ext; rfl
  εIso := Iso.refl _
  associator_eq _ _ _ := BialgCat.Hom.ext <| BialgHom.coe_linearMap_injective <|
    TensorProduct.ext <| TensorProduct.ext (by ext; rfl)
  leftUnitor_eq _ := BialgCat.Hom.ext <| BialgHom.coe_linearMap_injective <|
    TensorProduct.ext (by ext; rfl)
  rightUnitor_eq _ := BialgCat.Hom.ext <| BialgHom.coe_linearMap_injective <|
    TensorProduct.ext (by ext; rfl)
/-
**HopfAlgCat.instMonoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `HopfAlgCat`。
形式化陈述：instMonoidalCategory : MonoidalCategory (HopfAlgCat R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instMonoidalCategory : MonoidalCategory (HopfAlgCat R) :=
  Monoidal.induced (forget₂ _ (BialgCat R)) (MonoidalCategory.inducingFunctorData R)

/-- `forget₂ (HopfAlgCat R) (BialgCat R)` is a monoidal functor. -/
/-
**HopfAlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `HopfAlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`forget₂ (HopfAlgCat R) (BialgCat R)` is a monoidal functor.
-/
noncomputable instance : (forget₂ (HopfAlgCat R) (BialgCat R)).Monoidal where

end HopfAlgCat

