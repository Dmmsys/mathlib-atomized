/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The monoidal category structure on R-algebras
-/

public section

open CategoryTheory
open scoped MonoidalCategory

universe v u

variable {R : Type u} [CommRing R]

namespace AlgCat

noncomputable section

namespace instMonoidalCategory

open scoped TensorProduct

/-- Auxiliary definition used to fight a timeout when building
`AlgCat.instMonoidalCategory`. -/
@[simps!]
/--
Definition of `tensorObj` / `tensorObj` 的定义

English:
abbreviation tensorObj
  signature: (X Y : AlgCat.{u} R)
  body: of R (X otimes[R] Y)

中文:
缩写 tensorObj
  签名: (X Y : Alg范畴.{u} R)
  定义体: of R (X otimes[R] Y)

Depends on / 依赖: otimes
-/
noncomputable abbrev tensorObj (X Y : AlgCat.{u} R) : AlgCat.{u} R :=
  of R (X otimes[R] Y)

/--
Definition of `tensorHom` / `tensorHom` 的定义

English:
abbreviation tensorHom
  signature: {W X Y Z : AlgCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z)
  body: ofHom Algebra.TensorProduct.map f.hom g.hom

中文:
缩写 tensorHom
  签名: {W X Y Z : Alg范畴.{u} R} (f : W ⟶ X) (g : Y ⟶ Z)
  定义体: ofHom Algebra.TensorProduct.map f.hom g.hom

Depends on / 依赖: Algebra, Algebra.TensorProduct.map, TensorProduct, f.hom, g.hom
-/
noncomputable abbrev tensorHom {W X Y Z : AlgCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
ofHom Algebra.TensorProduct.map f.hom g.hom

end instMonoidalCategory

open instMonoidalCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategoryStruct (AlgCat.{u} R)
  body: instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of R R
  associator X Y Z := (Algebra.TensorProduct.assoc R R R X Y Z).toAlgebraIso
  leftUnitor X := (Algebra.TensorProduct.lid R X).toAlgebraIso
  rightUnitor X := (Algebra.TensorProduct.rid R R X).toAlgebraIso

中文:
实例 :
  签名: 幺半群范畴结构 (Alg范畴.{u} R)
  定义体: instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of R R
  associator X Y Z := (Algebra.TensorProduct.assoc R R R X Y Z).toAlgebraIso
  leftUnitor X := (Algebra.TensorProduct.lid R X).toAlgebraIso
  rightUnitor X := (Algebra.TensorProduct.rid R R X).toAlgebraIso

Depends on / 依赖: instMonoidalCategory, instMonoidalCategory.tensorObj, tensorObj
-/
instance : MonoidalCategoryStruct (AlgCat.{u} R) where
  tensorObj := instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of R R
  associator X Y Z := (Algebra.TensorProduct.assoc R R R X Y Z).toAlgebraIso
  leftUnitor X := (Algebra.TensorProduct.lid R X).toAlgebraIso
  rightUnitor X := (Algebra.TensorProduct.rid R R X).toAlgebraIso

/--
theorem `hom_tensorHom` / 定理 `hom_tensorHom`

English:
theorem hom_tensorHom
  given: {K L M N : AlgCat.{u} R} (f : K ⟶ L) (g : M ⟶ N)
  proof: rfl

中文:
定理 hom_tensorHom
  条件: {K L M N : Alg范畴.{u} R} (f : K ⟶ L) (g : M ⟶ N)
  证明: rfl
-/
theorem hom_tensorHom {K L M N : AlgCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f otimesₘ g).hom = Algebra.TensorProduct.map f.hom g.hom :=
  rfl

/--
theorem `hom_whiskerLeft` / 定理 `hom_whiskerLeft`

English:
theorem hom_whiskerLeft
  given: (L : AlgCat.{u} R) {M N : AlgCat.{u} R} (f : M ⟶ N)
  proof: rfl

中文:
定理 hom_whiskerLeft
  条件: (L : Alg范畴.{u} R) {M N : Alg范畴.{u} R} (f : M ⟶ N)
  证明: rfl
-/
theorem hom_whiskerLeft (L : AlgCat.{u} R) {M N : AlgCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = Algebra.TensorProduct.map (.id _ _) f.hom :=
  rfl

/--
theorem `hom_whiskerRight` / 定理 `hom_whiskerRight`

English:
theorem hom_whiskerRight
  given: {L M : AlgCat.{u} R} (f : L ⟶ M) (N : AlgCat.{u} R)
  proof: rfl

中文:
定理 hom_whiskerRight
  条件: {L M : Alg范畴.{u} R} (f : L ⟶ M) (N : Alg范畴.{u} R)
  证明: rfl
-/
theorem hom_whiskerRight {L M : AlgCat.{u} R} (f : L ⟶ M) (N : AlgCat.{u} R) :
    (f ▷ N).hom = Algebra.TensorProduct.map f.hom (.id _ _) :=
  rfl

/--
theorem `hom_hom_leftUnitor` / 定理 `hom_hom_leftUnitor`

English:
theorem hom_hom_leftUnitor
  given: {M : AlgCat.{u} R}
  proof: rfl

中文:
定理 hom_hom_leftUnitor
  条件: {M : Alg范畴.{u} R}
  证明: rfl
-/
theorem hom_hom_leftUnitor {M : AlgCat.{u} R} :
    (fun_ M).hom.hom = (Algebra.TensorProduct.lid _ _).toAlgHom :=
  rfl

/--
theorem `hom_inv_leftUnitor` / 定理 `hom_inv_leftUnitor`

English:
theorem hom_inv_leftUnitor
  given: {M : AlgCat.{u} R}
  proof: rfl

中文:
定理 hom_inv_leftUnitor
  条件: {M : Alg范畴.{u} R}
  证明: rfl
-/
theorem hom_inv_leftUnitor {M : AlgCat.{u} R} :
    (fun_ M).inv.hom = (Algebra.TensorProduct.lid _ _).symm.toAlgHom :=
  rfl

/--
theorem `hom_hom_rightUnitor` / 定理 `hom_hom_rightUnitor`

English:
theorem hom_hom_rightUnitor
  given: {M : AlgCat.{u} R}
  proof: rfl

中文:
定理 hom_hom_rightUnitor
  条件: {M : Alg范畴.{u} R}
  证明: rfl
-/
theorem hom_hom_rightUnitor {M : AlgCat.{u} R} :
    (ρ_ M).hom.hom = (Algebra.TensorProduct.rid _ _ _).toAlgHom :=
  rfl

/--
theorem `hom_inv_rightUnitor` / 定理 `hom_inv_rightUnitor`

English:
theorem hom_inv_rightUnitor
  given: {M : AlgCat.{u} R}
  proof: rfl

中文:
定理 hom_inv_rightUnitor
  条件: {M : Alg范畴.{u} R}
  证明: rfl
-/
theorem hom_inv_rightUnitor {M : AlgCat.{u} R} :
    (ρ_ M).inv.hom = (Algebra.TensorProduct.rid _ _ _).symm.toAlgHom :=
  rfl

/--
theorem `hom_hom_associator` / 定理 `hom_hom_associator`

English:
theorem hom_hom_associator
  given: {M N K : AlgCat.{u} R}
  proof: rfl

中文:
定理 hom_hom_associator
  条件: {M N K : Alg范畴.{u} R}
  证明: rfl
-/
theorem hom_hom_associator {M N K : AlgCat.{u} R} :
    (α_ M N K).hom.hom = (Algebra.TensorProduct.assoc R R R M N K).toAlgHom :=
  rfl

/--
theorem `hom_inv_associator` / 定理 `hom_inv_associator`

English:
theorem hom_inv_associator
  given: {M N K : AlgCat.{u} R}
  proof: rfl

中文:
定理 hom_inv_associator
  条件: {M N K : Alg范畴.{u} R}
  证明: rfl
-/
theorem hom_inv_associator {M N K : AlgCat.{u} R} :
    (α_ M N K).inv.hom = (Algebra.TensorProduct.assoc R R R M N K).symm.toAlgHom :=
  rfl

/--
Instance `instMonoidalCategory` / 实例 `instMonoidalCategory`

English:
instance instMonoidalCategory
  signature: : MonoidalCategory (AlgCat.{u} R)
  body: Monoidal.induced
    (forget₂ (AlgCat R) (ModuleCat R))
    { μIso := fun _ _ => Iso.refl _
      εIso := Iso.refl _
      associator_eq := fun _ _ _ =>
ModuleCat.hom_ext TensorProduct.ext_threefold (fun _ _ _ => rfl)
leftUnitor_eq := fun _ => ModuleCat.hom_ext TensorProduct.ext' (fun _ _ => rfl)
rightUnitor_eq := fun _ => ModuleCat.hom_ext TensorProduct.ext' (fun _ _ => rfl) }

中文:
实例 instMonoidalCategory
  签名: : 幺半群范畴 (Alg范畴.{u} R)
  定义体: Monoidal.induced
    (forget₂ (AlgCat R) (ModuleCat R))
    { μIso := fun _ _ => Iso.refl _
      εIso := Iso.refl _
      associator_eq := fun _ _ _ =>
ModuleCat.hom_ext TensorProduct.ext_threefold (fun _ _ _ => rfl)
leftUnitor_eq := fun _ => ModuleCat.hom_ext TensorProduct.ext' (fun _ _ => rfl)
rightUnitor_eq := fun _ => ModuleCat.hom_ext TensorProduct.ext' (fun _ _ => rfl) }

Depends on / 依赖: AlgCat, Iso.refl, ModuleCat, ModuleCat.hom_ext, Monoidal, Monoidal.induced, TensorProduct, TensorProduct.ext, TensorProduct.ext_threefold, associator_eq, ext_threefold, hom_ext, induced, leftUnitor_eq, rightUnitor_eq
-/
noncomputable instance instMonoidalCategory : MonoidalCategory (AlgCat.{u} R) :=
  Monoidal.induced
    (forget₂ (AlgCat R) (ModuleCat R))
    { μIso := fun _ _ => Iso.refl _
      εIso := Iso.refl _
      associator_eq := fun _ _ _ =>
ModuleCat.hom_ext TensorProduct.ext_threefold (fun _ _ _ => rfl)
leftUnitor_eq := fun _ => ModuleCat.hom_ext TensorProduct.ext' (fun _ _ => rfl)
rightUnitor_eq := fun _ => ModuleCat.hom_ext TensorProduct.ext' (fun _ _ => rfl) }

/-- `forget₂ (AlgCat R) (ModuleCat R)` as a monoidal functor. -/
example : (forget₂ (AlgCat R) (ModuleCat R)).Monoidal := inferInstance

end

end AlgCat
