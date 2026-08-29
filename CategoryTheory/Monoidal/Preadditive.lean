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

/--
Definition of `MonoidalPreadditive` / `MonoidalPreadditive` 的定义

English:
class MonoidalPreadditive
  parameters: : Prop where
  axioms and operations (4):
    - whiskerLeft_zero : forall {X Y Z : C}, X ◁ (0 : Y ⟶ Z) = 0  [default: by cat_disch]
    - zero_whiskerRight : forall {X Y Z : C}, (0 : Y ⟶ Z) ▷ X = 0  [default: by cat_disch]
    - whiskerLeft_add : forall {X Y Z : C} (f g : Y ⟶ Z), X ◁ (f + g) = X ◁ f + X ◁ g  [default: by cat_disch]
    - add_whiskerRight : forall {X Y Z : C} (f g : Y ⟶ Z), (f + g) ▷ X = f ▷ X + g ▷ X  [default: by cat_disch]

中文:
类 幺半群预加性
  参数: : 命题 where
  公理与运算 (4 个):
    - whiskerLeft_zero : 对任意 {X Y Z : C}, X ◁ (0 : Y ⟶ Z) = 0  [默认: by cat_disch]
    - zero_whiskerRight : 对任意 {X Y Z : C}, (0 : Y ⟶ Z) ▷ X = 0  [默认: by cat_disch]
    - whiskerLeft_add : 对任意 {X Y Z : C} (f g : Y ⟶ Z), X ◁ (f + g) = X ◁ f + X ◁ g  [默认: by cat_disch]
    - add_whiskerRight : 对任意 {X Y Z : C} (f g : Y ⟶ Z), (f + g) ▷ X = f ▷ X + g ▷ X  [默认: by cat_disch]

Depends on / 依赖: MonoOver, PartialOrder, ThinSkeleton, add_whiskerRight, cat_disch, whiskerLeft_add, zero_whiskerRight
-/
class MonoidalPreadditive : Prop where
  whiskerLeft_zero : forall {X Y Z : C}, X ◁ (0 : Y ⟶ Z) = 0 := by cat_disch
  zero_whiskerRight : forall {X Y Z : C}, (0 : Y ⟶ Z) ▷ X = 0 := by cat_disch
  whiskerLeft_add : forall {X Y Z : C} (f g : Y ⟶ Z), X ◁ (f + g) = X ◁ f + X ◁ g := by cat_disch
  add_whiskerRight : forall {X Y Z : C} (f g : Y ⟶ Z), (f + g) ▷ X = f ▷ X + g ▷ X := by cat_disch

attribute [simp] MonoidalPreadditive.whiskerLeft_zero MonoidalPreadditive.zero_whiskerRight
attribute [simp] MonoidalPreadditive.whiskerLeft_add MonoidalPreadditive.add_whiskerRight

variable {C}
variable [MonoidalPreadditive C]

namespace MonoidalPreadditive

-- The priority setting will not be needed when we replace `𝟙 X ⊗ₘ f` by `X ◁ f`.
@[simp (low)]
/--
theorem `tensor_zero` / 定理 `tensor_zero`

English:
theorem tensor_zero
  given: {W X Y Z : C} (f : W ⟶ X)
  statement: f otimesₘ (0 : Y ⟶ Z) = 0
  proof: by
  simp [tensorHom_def]

中文:
定理 tensor_zero
  条件: {W X Y Z : C} (f : W ⟶ X)
  结论: f otimesₘ (0 : Y ⟶ Z) = 0
  证明: by
  simp [tensorHom_def]

Depends on / 依赖: tensorHom_def
-/
theorem tensor_zero {W X Y Z : C} (f : W ⟶ X) : f otimesₘ (0 : Y ⟶ Z) = 0 := by
  simp [tensorHom_def]

-- The priority setting will not be needed when we replace `f ⊗ₘ 𝟙 X` by `f ▷ X`.
@[simp (low)]
/--
theorem `zero_tensor` / 定理 `zero_tensor`

English:
theorem zero_tensor
  given: {W X Y Z : C} (f : Y ⟶ Z)
  statement: (0 : W ⟶ X) otimesₘ f = 0
  proof: by
  simp [tensorHom_def]

中文:
定理 zero_tensor
  条件: {W X Y Z : C} (f : Y ⟶ Z)
  结论: (0 : W ⟶ X) otimesₘ f = 0
  证明: by
  simp [tensorHom_def]

Depends on / 依赖: tensorHom_def
-/
theorem zero_tensor {W X Y Z : C} (f : Y ⟶ Z) : (0 : W ⟶ X) otimesₘ f = 0 := by
  simp [tensorHom_def]

/--
theorem `tensor_add` / 定理 `tensor_add`

English:
theorem tensor_add
  given: {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z)
  statement: f otimesₘ (g + h) = f otimesₘ g + f otimesₘ h
  proof: by
  simp [tensorHom_def]

中文:
定理 tensor_add
  条件: {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z)
  结论: f otimesₘ (g + h) = f otimesₘ g + f otimesₘ h
  证明: by
  simp [tensorHom_def]

Depends on / 依赖: tensorHom_def
-/
theorem tensor_add {W X Y Z : C} (f : W ⟶ X) (g h : Y ⟶ Z) : f otimesₘ (g + h) = f otimesₘ g + f otimesₘ h := by
  simp [tensorHom_def]

/--
theorem `add_tensor` / 定理 `add_tensor`

English:
theorem add_tensor
  given: {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z)
  statement: (f + g) otimesₘ h = f otimesₘ h + g otimesₘ h
  proof: by
  simp [tensorHom_def]

中文:
定理 add_tensor
  条件: {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z)
  结论: (f + g) otimesₘ h = f otimesₘ h + g otimesₘ h
  证明: by
  simp [tensorHom_def]

Depends on / 依赖: tensorHom_def
-/
theorem add_tensor {W X Y Z : C} (f g : W ⟶ X) (h : Y ⟶ Z) : (f + g) otimesₘ h = f otimesₘ h + g otimesₘ h := by
  simp [tensorHom_def]

instance (X : C) : (tensorLeft X).Additive where
instance (X : C) : (tensorRight X).Additive where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (curriedTensor C).Additive

中文:
实例 :
  签名: (curriedTensor C).加性
-/
instance : (curriedTensor C).Additive where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (curriedTensor C).flip.Additive

中文:
实例 :
  签名: (curriedTensor C).flip.加性
-/
instance : (curriedTensor C).flip.Additive where

end MonoidalPreadditive

/--
Instance `tensorLeft_additive` / 实例 `tensorLeft_additive`

English:
instance tensorLeft_additive
  signature: (X : C)

中文:
实例 tensorLeft_additive
  签名: (X : C)
-/
instance tensorLeft_additive (X : C) : (tensorLeft X).Additive where

/--
Instance `tensorRight_additive` / 实例 `tensorRight_additive`

English:
instance tensorRight_additive
  signature: (X : C)

中文:
实例 tensorRight_additive
  签名: (X : C)
-/
instance tensorRight_additive (X : C) : (tensorRight X).Additive where

/--
Instance `tensoringLeft_additive` / 实例 `tensoringLeft_additive`

English:
instance tensoringLeft_additive
  signature: (X : C)

中文:
实例 tensoringLeft_additive
  签名: (X : C)
-/
instance tensoringLeft_additive (X : C) : ((tensoringLeft C).obj X).Additive where

/--
Instance `tensoringRight_additive` / 实例 `tensoringRight_additive`

English:
instance tensoringRight_additive
  signature: (X : C)

中文:
实例 tensoringRight_additive
  签名: (X : C)
-/
instance tensoringRight_additive (X : C) : ((tensoringRight C).obj X).Additive where

/--
theorem `monoidalPreadditive_of_faithful` / 定理 `monoidalPreadditive_of_faithful`

English:
theorem monoidalPreadditive_of_faithful
  statement: {D} [Category* D] [Preadditive D] [MonoidalCategory D]
  proof: { whiskerLeft_zero := by
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

中文:
定理 monoidalPreadditive_of_faithful
  结论: {D} [范畴* D] [预加性 D] [幺半群范畴 D]
  证明: { whiskerLeft_zero := by
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

Depends on / 依赖: F.map_injective, Functor, Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_whiskerRight, Functor.map_add, Monoidal, MonoidalPreadditive, MonoidalPreadditive.whiskerLeft_add, Preadditive, Preadditive.add_comp, Preadditive.comp_add, add_comp, add_whiskerRight, comp_add, intros, map_add, map_injective, map_whiskerLeft, map_whiskerRight, whiskerLeft_add
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

/--
theorem `whiskerLeft_sum` / 定理 `whiskerLeft_sum`

English:
theorem whiskerLeft_sum
  given: (P : C) {Q R : C} {J : Type*} (s : Finset J) (g : J -> (Q ⟶ R))
  proof: map_sum ((tensoringLeft C).obj P).mapAddHom g s

中文:
定理 whiskerLeft_sum
  条件: (P : C) {Q R : C} {J : 类型} (s : 有限集 J) (g : J -> (Q ⟶ R))
  证明: map_sum ((tensoringLeft C).obj P).mapAddHom g s

Depends on / 依赖: mapAddHom, map_sum, tensoringLeft
-/
theorem whiskerLeft_sum (P : C) {Q R : C} {J : Type*} (s : Finset J) (g : J -> (Q ⟶ R)) :
    P ◁ ∑ j in s, g j = ∑ j in s, P ◁ g j :=
  map_sum ((tensoringLeft C).obj P).mapAddHom g s

/--
theorem `sum_whiskerRight` / 定理 `sum_whiskerRight`

English:
theorem sum_whiskerRight
  given: {Q R : C} {J : Type*} (s : Finset J) (g : J -> (Q ⟶ R)) (P : C)
  proof: map_sum ((tensoringRight C).obj P).mapAddHom g s

中文:
定理 sum_whiskerRight
  条件: {Q R : C} {J : 类型} (s : 有限集 J) (g : J -> (Q ⟶ R)) (P : C)
  证明: map_sum ((tensoringRight C).obj P).mapAddHom g s

Depends on / 依赖: mapAddHom, map_sum, tensoringRight
-/
theorem sum_whiskerRight {Q R : C} {J : Type*} (s : Finset J) (g : J -> (Q ⟶ R)) (P : C) :
    (∑ j in s, g j) ▷ P = ∑ j in s, g j ▷ P :=
  map_sum ((tensoringRight C).obj P).mapAddHom g s

/--
theorem `tensor_sum` / 定理 `tensor_sum`

English:
theorem tensor_sum
  given: {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J -> (R ⟶ S))
  proof: by
  simp only [tensorHom_def, whiskerLeft_sum, Preadditive.comp_sum]

中文:
定理 tensor_sum
  条件: {P Q R S : C} {J : 类型} (s : 有限集 J) (f : P ⟶ Q) (g : J -> (R ⟶ S))
  证明: by
  simp only [tensorHom_def, whiskerLeft_sum, Preadditive.comp_sum]

Depends on / 依赖: Preadditive, Preadditive.comp_sum, comp_sum, tensorHom_def, whiskerLeft_sum
-/
theorem tensor_sum {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J -> (R ⟶ S)) :
    (f otimesₘ ∑ j in s, g j) = ∑ j in s, f otimesₘ g j := by
  simp only [tensorHom_def, whiskerLeft_sum, Preadditive.comp_sum]

/--
theorem `sum_tensor` / 定理 `sum_tensor`

English:
theorem sum_tensor
  given: {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J -> (R ⟶ S))
  proof: by
  simp only [tensorHom_def, sum_whiskerRight, Preadditive.sum_comp]

中文:
定理 sum_tensor
  条件: {P Q R S : C} {J : 类型} (s : 有限集 J) (f : P ⟶ Q) (g : J -> (R ⟶ S))
  证明: by
  simp only [tensorHom_def, sum_whiskerRight, Preadditive.sum_comp]

Depends on / 依赖: Preadditive, Preadditive.sum_comp, sum_comp, sum_whiskerRight, tensorHom_def
-/
theorem sum_tensor {P Q R S : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J -> (R ⟶ S)) :
    (∑ j in s, g j) otimesₘ f = ∑ j in s, g j otimesₘ f := by
  simp only [tensorHom_def, sum_whiskerRight, Preadditive.sum_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- In a closed monoidal category, this would hold because
-- `tensorLeft X` is a left adjoint and hence preserves all colimits.
-- In any case it is true in any preadditive category.
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

/--
Definition of `leftDistributor` / `leftDistributor` 的定义

English:
definition leftDistributor
  signature: {J : Type} [Finite J] (X : C) (f : J -> C)
  body: (tensorLeft X).mapBiproduct f

中文:
定义 leftDistributor
  签名: {J : 类型} [有限 J] (X : C) (f : J -> C)
  定义体: (tensorLeft X).mapBiproduct f

Depends on / 依赖: mapBiproduct, tensorLeft
-/
def leftDistributor {J : Type} [Finite J] (X : C) (f : J -> C) : X otimes ⨁ f ≅ ⨁ fun j => X otimes f j :=
  (tensorLeft X).mapBiproduct f

set_option backward.defeqAttrib.useBackward true in
/--
theorem `leftDistributor_hom` / 定理 `leftDistributor_hom`

English:
theorem leftDistributor_hom
  given: {J : Type} [Fintype J] (X : C) (f : J -> C)
  proof: by
  classical
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]

中文:
定理 leftDistributor_hom
  条件: {J : 类型} [有限类型 J] (X : C) (f : J -> C)
  证明: by
  classical
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Finset, Finset.mem_univ, Finset.sum_dite_eq, Functor, Functor.mapBicone, Functor.mapBiproduct, Preadditive, Preadditive.sum_comp, biproduct, biproduct.lift_, classical, comp_dite, comp_id, comp_zero, eqToHom_refl, ite_true, leftDistributor
-/
theorem leftDistributor_hom {J : Type} [Fintype J] (X : C) (f : J -> C) :
    (leftDistributor X f).hom =
      ∑ j : J, (X ◁ biproduct.π f j) ≫ biproduct.ι (fun j => X otimes f j) j := by
  classical
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `leftDistributor_inv` / 定理 `leftDistributor_inv`

English:
theorem leftDistributor_inv
  given: {J : Type} [Fintype J] (X : C) (f : J -> C)
  proof: by
  classical
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp, zero_comp,
    Finset.sum_dite_eq, Finset.mem_univ, ite_true, eqToHom_refl, Category.id_comp,
    biproduct.ι_desc]

@[reassoc (attr := simp)]

中文:
定理 leftDistributor_inv
  条件: {J : 类型} [有限类型 J] (X : C) (f : J -> C)
  证明: by
  classical
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp, zero_comp,
    Finset.sum_dite_eq, Finset.mem_univ, ite_true, eqToHom_refl, Category.id_comp,
    biproduct.ι_desc]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.id_comp, Finset, Finset.mem_univ, Finset.sum_dite_eq, Functor, Functor.mapBicone, Functor.mapBiproduct, Preadditive, Preadditive.comp_sum, biproduct, classical, comp_sum, dite_comp, eqToHom_refl, id_comp, ite_true, leftDistributor, mapBicone, mapBiproduct
-/
theorem leftDistributor_inv {J : Type} [Fintype J] (X : C) (f : J -> C) :
    (leftDistributor X f).inv = ∑ j : J, biproduct.π _ j ≫ (X ◁ biproduct.ι f j) := by
  classical
  ext
  dsimp [leftDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp, zero_comp,
    Finset.sum_dite_eq, Finset.mem_univ, ite_true, eqToHom_refl, Category.id_comp,
    biproduct.ι_desc]

@[reassoc (attr := simp)]
/--
theorem `leftDistributor_hom_comp_biproduct_π` / 定理 `leftDistributor_hom_comp_biproduct_π`

English:
theorem leftDistributor_hom_comp_biproduct_π
  given: {J : Type} [Finite J] (X : C) (f : J -> C) (j : J)
  proof: by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]

@[reassoc (attr := simp)]

中文:
定理 leftDistributor_hom_comp_biproduct_π
  条件: {J : 类型} [有限 J] (X : C) (f : J -> C) (j : J)
  证明: by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]

@[reassoc (attr := simp)]

Depends on / 依赖: Preadditive, Preadditive.sum_comp, biproduct, classical, comp_dite, leftDistributor_hom, nonempty_fintype, sum_comp
-/
theorem leftDistributor_hom_comp_biproduct_π {J : Type} [Finite J] (X : C) (f : J -> C) (j : J) :
    (leftDistributor X f).hom ≫ biproduct.π _ j = X ◁ biproduct.π _ j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]

@[reassoc (attr := simp)]
/--
theorem `biproduct_ι_comp_leftDistributor_hom` / 定理 `biproduct_ι_comp_leftDistributor_hom`

English:
theorem biproduct_ι_comp_leftDistributor_hom
  given: {J : Type} [Finite J] (X : C) (f : J -> C) (j : J)
  proof: by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_hom, Preadditive.comp_sum, ← whiskerLeft_comp_assoc,
    biproduct.ι_π, whiskerLeft_dite, dite_comp]

@[reassoc (attr := simp)]

中文:
定理 biproduct_ι_comp_leftDistributor_hom
  条件: {J : 类型} [有限 J] (X : C) (f : J -> C) (j : J)
  证明: by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_hom, Preadditive.comp_sum, ← whiskerLeft_comp_assoc,
    biproduct.ι_π, whiskerLeft_dite, dite_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: Preadditive, Preadditive.comp_sum, biproduct, classical, comp_sum, dite_comp, leftDistributor_hom, nonempty_fintype, whiskerLeft_comp_assoc, whiskerLeft_dite
-/
theorem biproduct_ι_comp_leftDistributor_hom {J : Type} [Finite J] (X : C) (f : J -> C) (j : J) :
    (X ◁ biproduct.ι _ j) ≫ (leftDistributor X f).hom = biproduct.ι (fun j => X otimes f j) j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_hom, Preadditive.comp_sum, ← whiskerLeft_comp_assoc,
    biproduct.ι_π, whiskerLeft_dite, dite_comp]

@[reassoc (attr := simp)]
/--
theorem `leftDistributor_inv_comp_biproduct_π` / 定理 `leftDistributor_inv_comp_biproduct_π`

English:
theorem leftDistributor_inv_comp_biproduct_π
  given: {J : Type} [Finite J] (X : C) (f : J -> C) (j : J)
  proof: by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_inv, Preadditive.sum_comp, ← whiskerLeft_comp,
    biproduct.ι_π, whiskerLeft_dite, comp_dite]

@[reassoc (attr := simp)]

中文:
定理 leftDistributor_inv_comp_biproduct_π
  条件: {J : 类型} [有限 J] (X : C) (f : J -> C) (j : J)
  证明: by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_inv, Preadditive.sum_comp, ← whiskerLeft_comp,
    biproduct.ι_π, whiskerLeft_dite, comp_dite]

@[reassoc (attr := simp)]

Depends on / 依赖: Preadditive, Preadditive.sum_comp, biproduct, classical, comp_dite, leftDistributor_inv, nonempty_fintype, sum_comp, whiskerLeft_comp, whiskerLeft_dite
-/
theorem leftDistributor_inv_comp_biproduct_π {J : Type} [Finite J] (X : C) (f : J -> C) (j : J) :
    (leftDistributor X f).inv ≫ (X ◁ biproduct.π _ j) = biproduct.π _ j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_inv, Preadditive.sum_comp, ← whiskerLeft_comp,
    biproduct.ι_π, whiskerLeft_dite, comp_dite]

@[reassoc (attr := simp)]
/--
theorem `biproduct_ι_comp_leftDistributor_inv` / 定理 `biproduct_ι_comp_leftDistributor_inv`

English:
theorem biproduct_ι_comp_leftDistributor_inv
  given: {J : Type} [Finite J] (X : C) (f : J -> C) (j : J)
  proof: by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_inv, Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp]

中文:
定理 biproduct_ι_comp_leftDistributor_inv
  条件: {J : 类型} [有限 J] (X : C) (f : J -> C) (j : J)
  证明: by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_inv, Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp]

Depends on / 依赖: Preadditive, Preadditive.comp_sum, biproduct, classical, comp_sum, dite_comp, leftDistributor_inv, nonempty_fintype
-/
theorem biproduct_ι_comp_leftDistributor_inv {J : Type} [Finite J] (X : C) (f : J -> C) (j : J) :
    biproduct.ι _ j ≫ (leftDistributor X f).inv = X ◁ biproduct.ι _ j := by
  classical
  cases nonempty_fintype J
  simp [leftDistributor_inv, Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp]

/--
theorem `leftDistributor_assoc` / 定理 `leftDistributor_assoc`

English:
theorem leftDistributor_assoc
  given: {J : Type} [Finite J] (X Y : C) (f : J -> C)
  proof: by
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

中文:
定理 leftDistributor_assoc
  条件: {J : 类型} [有限 J] (X Y : C) (f : J -> C)
  证明: by
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

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Finset, Finset.sum_const_zero, Finset.sum_dite_eq, Finset.sum_dite_irrel, Iso.symm_hom, Iso.trans_hom, Preadditive, Preadditive.comp_sum, Preadditive.sum_comp, asIso_hom, biproduct, biproduct.mapIso_hom, classical, comp_dite, comp_id, comp_sum, comp_zero
-/
theorem leftDistributor_assoc {J : Type} [Finite J] (X Y : C) (f : J -> C) :
    (asIso (𝟙 X) otimesᵢ leftDistributor Y f) ≪≫ leftDistributor X _ =
      (α_ X Y (⨁ f)).symm ≪≫ leftDistributor (X otimes Y) f ≪≫ biproduct.mapIso fun _ => α_ X Y _ := by
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

/--
Definition of `rightDistributor` / `rightDistributor` 的定义

English:
definition rightDistributor
  signature: {J : Type} [Finite J] (f : J -> C) (X : C)
  body: (tensorRight X).mapBiproduct f

中文:
定义 rightDistributor
  签名: {J : 类型} [有限 J] (f : J -> C) (X : C)
  定义体: (tensorRight X).mapBiproduct f

Depends on / 依赖: mapBiproduct, tensorRight
-/
def rightDistributor {J : Type} [Finite J] (f : J -> C) (X : C) : (⨁ f) otimes X ≅ ⨁ fun j => f j otimes X :=
  (tensorRight X).mapBiproduct f

set_option backward.defeqAttrib.useBackward true in
/--
theorem `rightDistributor_hom` / 定理 `rightDistributor_hom`

English:
theorem rightDistributor_hom
  given: {J : Type} [Fintype J] (f : J -> C) (X : C)
  proof: by
  classical
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, ite_true]

中文:
定理 rightDistributor_hom
  条件: {J : 类型} [有限类型 J] (f : J -> C) (X : C)
  证明: by
  classical
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, ite_true]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Finset, Finset.mem_univ, Finset.sum_dite_eq, Functor, Functor.mapBicone, Functor.mapBiproduct, Preadditive, Preadditive.sum_comp, biproduct, biproduct.lift_, classical, comp_dite, comp_id, comp_zero, eqToHom_refl, ite_true, mapBicone
-/
theorem rightDistributor_hom {J : Type} [Fintype J] (f : J -> C) (X : C) :
    (rightDistributor f X).hom =
      ∑ j : J, (biproduct.π f j ▷ X) ≫ biproduct.ι (fun j => f j otimes X) j := by
  classical
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  erw [biproduct.lift_π]
  simp only [Preadditive.sum_comp, Category.assoc, biproduct.ι_π, comp_dite, comp_zero,
    Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, ite_true]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `rightDistributor_inv` / 定理 `rightDistributor_inv`

English:
theorem rightDistributor_inv
  given: {J : Type} [Fintype J] (f : J -> C) (X : C)
  proof: by
  classical
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp,
    zero_comp, Finset.sum_dite_eq, Finset.mem_univ, eqToHom_refl, Category.id_comp, ite_true]

@[reassoc (attr := simp)]

中文:
定理 rightDistributor_inv
  条件: {J : 类型} [有限类型 J] (f : J -> C) (X : C)
  证明: by
  classical
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp,
    zero_comp, Finset.sum_dite_eq, Finset.mem_univ, eqToHom_refl, Category.id_comp, ite_true]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.id_comp, Finset, Finset.mem_univ, Finset.sum_dite_eq, Functor, Functor.mapBicone, Functor.mapBiproduct, Preadditive, Preadditive.comp_sum, biproduct, classical, comp_sum, dite_comp, eqToHom_refl, id_comp, ite_true, mapBicone, mapBiproduct, mem_univ
-/
theorem rightDistributor_inv {J : Type} [Fintype J] (f : J -> C) (X : C) :
    (rightDistributor f X).inv = ∑ j : J, biproduct.π _ j ≫ (biproduct.ι f j ▷ X) := by
  classical
  ext
  dsimp [rightDistributor, Functor.mapBiproduct, Functor.mapBicone]
  simp only [biproduct.ι_desc, Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp,
    zero_comp, Finset.sum_dite_eq, Finset.mem_univ, eqToHom_refl, Category.id_comp, ite_true]

@[reassoc (attr := simp)]
/--
theorem `rightDistributor_hom_comp_biproduct_π` / 定理 `rightDistributor_hom_comp_biproduct_π`

English:
theorem rightDistributor_hom_comp_biproduct_π
  given: {J : Type} [Finite J] (f : J -> C) (X : C) (j : J)
  proof: by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]

@[reassoc (attr := simp)]

中文:
定理 rightDistributor_hom_comp_biproduct_π
  条件: {J : 类型} [有限 J] (f : J -> C) (X : C) (j : J)
  证明: by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]

@[reassoc (attr := simp)]

Depends on / 依赖: Preadditive, Preadditive.sum_comp, biproduct, classical, comp_dite, nonempty_fintype, rightDistributor_hom, sum_comp
-/
theorem rightDistributor_hom_comp_biproduct_π {J : Type} [Finite J] (f : J -> C) (X : C) (j : J) :
    (rightDistributor f X).hom ≫ biproduct.π _ j = biproduct.π _ j ▷ X := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_hom, Preadditive.sum_comp, biproduct.ι_π, comp_dite]

@[reassoc (attr := simp)]
/--
theorem `biproduct_ι_comp_rightDistributor_hom` / 定理 `biproduct_ι_comp_rightDistributor_hom`

English:
theorem biproduct_ι_comp_rightDistributor_hom
  given: {J : Type} [Finite J] (f : J -> C) (X : C) (j : J)
  proof: by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_hom, Preadditive.comp_sum, ← comp_whiskerRight_assoc, biproduct.ι_π,
    dite_whiskerRight, dite_comp]

@[reassoc (attr := simp)]

中文:
定理 biproduct_ι_comp_rightDistributor_hom
  条件: {J : 类型} [有限 J] (f : J -> C) (X : C) (j : J)
  证明: by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_hom, Preadditive.comp_sum, ← comp_whiskerRight_assoc, biproduct.ι_π,
    dite_whiskerRight, dite_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: Preadditive, Preadditive.comp_sum, biproduct, classical, comp_sum, comp_whiskerRight_assoc, dite_comp, dite_whiskerRight, nonempty_fintype, rightDistributor_hom
-/
theorem biproduct_ι_comp_rightDistributor_hom {J : Type} [Finite J] (f : J -> C) (X : C) (j : J) :
    (biproduct.ι _ j ▷ X) ≫ (rightDistributor f X).hom = biproduct.ι (fun j => f j otimes X) j := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_hom, Preadditive.comp_sum, ← comp_whiskerRight_assoc, biproduct.ι_π,
    dite_whiskerRight, dite_comp]

@[reassoc (attr := simp)]
/--
theorem `rightDistributor_inv_comp_biproduct_π` / 定理 `rightDistributor_inv_comp_biproduct_π`

English:
theorem rightDistributor_inv_comp_biproduct_π
  given: {J : Type} [Finite J] (f : J -> C) (X : C) (j : J)
  proof: by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_inv, Preadditive.sum_comp, ← comp_whiskerRight,
    biproduct.ι_π, dite_whiskerRight, comp_dite]

@[reassoc (attr := simp)]

中文:
定理 rightDistributor_inv_comp_biproduct_π
  条件: {J : 类型} [有限 J] (f : J -> C) (X : C) (j : J)
  证明: by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_inv, Preadditive.sum_comp, ← comp_whiskerRight,
    biproduct.ι_π, dite_whiskerRight, comp_dite]

@[reassoc (attr := simp)]

Depends on / 依赖: Preadditive, Preadditive.sum_comp, biproduct, classical, comp_dite, comp_whiskerRight, dite_whiskerRight, nonempty_fintype, rightDistributor_inv, sum_comp
-/
theorem rightDistributor_inv_comp_biproduct_π {J : Type} [Finite J] (f : J -> C) (X : C) (j : J) :
    (rightDistributor f X).inv ≫ (biproduct.π _ j ▷ X) = biproduct.π _ j := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_inv, Preadditive.sum_comp, ← comp_whiskerRight,
    biproduct.ι_π, dite_whiskerRight, comp_dite]

@[reassoc (attr := simp)]
/--
theorem `biproduct_ι_comp_rightDistributor_inv` / 定理 `biproduct_ι_comp_rightDistributor_inv`

English:
theorem biproduct_ι_comp_rightDistributor_inv
  given: {J : Type} [Finite J] (f : J -> C) (X : C) (j : J)
  proof: by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_inv, Preadditive.comp_sum, biproduct.ι_π_assoc,
    dite_comp]

中文:
定理 biproduct_ι_comp_rightDistributor_inv
  条件: {J : 类型} [有限 J] (f : J -> C) (X : C) (j : J)
  证明: by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_inv, Preadditive.comp_sum, biproduct.ι_π_assoc,
    dite_comp]

Depends on / 依赖: Preadditive, Preadditive.comp_sum, biproduct, classical, comp_sum, dite_comp, nonempty_fintype, rightDistributor_inv
-/
theorem biproduct_ι_comp_rightDistributor_inv {J : Type} [Finite J] (f : J -> C) (X : C) (j : J) :
    biproduct.ι _ j ≫ (rightDistributor f X).inv = biproduct.ι _ j ▷ X := by
  classical
  cases nonempty_fintype J
  simp [rightDistributor_inv, Preadditive.comp_sum, biproduct.ι_π_assoc,
    dite_comp]

/--
theorem `rightDistributor_assoc` / 定理 `rightDistributor_assoc`

English:
theorem rightDistributor_assoc
  given: {J : Type} [Finite J] (f : J -> C) (X Y : C)
  proof: by
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

中文:
定理 rightDistributor_assoc
  条件: {J : 类型} [有限 J] (f : J -> C) (X Y : C)
  证明: by
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

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Finset, Finset.mem_univ, Finset.sum_const_zero, Finset.sum_dite_eq, Finset.sum_dite_irrel, Iso.symm_hom, Iso.trans_hom, Preadditive, Preadditive.comp_sum, Preadditive.sum_comp, asIso_hom, biproduct, biproduct.mapIso_hom, classical, comp_dite, comp_id, comp_sum
-/
theorem rightDistributor_assoc {J : Type} [Finite J] (f : J -> C) (X Y : C) :
    (rightDistributor f X otimesᵢ asIso (𝟙 Y)) ≪≫ rightDistributor _ Y =
      α_ (⨁ f) X Y ≪≫ rightDistributor f (X otimes Y) ≪≫ biproduct.mapIso fun _ => (α_ _ X Y).symm := by
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

/--
theorem `leftDistributor_rightDistributor_assoc` / 定理 `leftDistributor_rightDistributor_assoc`

English:
theorem leftDistributor_rightDistributor_assoc
  statement: {J : Type _} [Finite J]
  proof: by
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

中文:
定理 leftDistributor_rightDistributor_assoc
  结论: {J : 类型 _} [有限 J]
  证明: by
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

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Finset, Finset.mem_univ, Finset.sum_const_zero, Finset.sum_dite_eq, Finset.sum_dite_irrel, Iso.symm_hom, Iso.trans_hom, Preadditive, Preadditive.comp_sum, Preadditive.sum_comp, Y.arrow, asIso_hom, biproduct, biproduct.mapIso_hom, classical, comp_dite, comp_id
-/
theorem leftDistributor_rightDistributor_assoc {J : Type _} [Finite J]
    (X : C) (f : J -> C) (Y : C) :
    (leftDistributor X f otimesᵢ asIso (𝟙 Y)) ≪≫ rightDistributor _ Y =
      α_ X (⨁ f) Y ≪≫
        (asIso (𝟙 X) otimesᵢ rightDistributor _ Y) ≪≫
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
/--
theorem `leftDistributor_ext_left` / 定理 `leftDistributor_ext_left`

English:
theorem leftDistributor_ext_left
  statement: {J : Type} [Finite J] {X Y : C} {f : J -> C} {g h : X otimes ⨁ f ⟶ Y}
  proof: by
  cases nonempty_fintype J
  apply (cancel_epi (leftDistributor X f).inv).mp
  ext
  simp [w]

@[ext]

中文:
定理 leftDistributor_ext_left
  结论: {J : 类型} [有限 J] {X Y : C} {f : J -> C} {g h : X otimes ⨁ f ⟶ Y}
  证明: by
  cases nonempty_fintype J
  apply (cancel_epi (leftDistributor X f).inv).mp
  ext
  simp [w]

@[ext]

Depends on / 依赖: cancel_epi, leftDistributor, nonempty_fintype
-/
theorem leftDistributor_ext_left {J : Type} [Finite J] {X Y : C} {f : J -> C} {g h : X otimes ⨁ f ⟶ Y}
    (w : forall j, (X ◁ biproduct.ι f j) ≫ g = (X ◁ biproduct.ι f j) ≫ h) : g = h := by
  cases nonempty_fintype J
  apply (cancel_epi (leftDistributor X f).inv).mp
  ext
  simp [w]

@[ext]
/--
theorem `leftDistributor_ext_right` / 定理 `leftDistributor_ext_right`

English:
theorem leftDistributor_ext_right
  statement: {J : Type} [Finite J] {X Y : C} {f : J -> C} {g h : X ⟶ Y otimes ⨁ f}
  proof: by
  cases nonempty_fintype J
  apply (cancel_mono (leftDistributor Y f).hom).mp
  ext
  simp [w]

中文:
定理 leftDistributor_ext_right
  结论: {J : 类型} [有限 J] {X Y : C} {f : J -> C} {g h : X ⟶ Y otimes ⨁ f}
  证明: by
  cases nonempty_fintype J
  apply (cancel_mono (leftDistributor Y f).hom).mp
  ext
  simp [w]

Depends on / 依赖: cancel_mono, leftDistributor, nonempty_fintype
-/
theorem leftDistributor_ext_right {J : Type} [Finite J] {X Y : C} {f : J -> C} {g h : X ⟶ Y otimes ⨁ f}
    (w : forall j, g ≫ (Y ◁ biproduct.π f j) = h ≫ (Y ◁ biproduct.π f j)) : g = h := by
  cases nonempty_fintype J
  apply (cancel_mono (leftDistributor Y f).hom).mp
  ext
  simp [w]

-- One might wonder how many iterated tensor products we need simp lemmas for.
-- The answer is two: this lemma is needed to verify the pentagon identity.
@[ext]
/--
theorem `leftDistributor_ext₂_left` / 定理 `leftDistributor_ext₂_left`

English:
theorem leftDistributor_ext₂_left
  statement: {J : Type} [Finite J]
  proof: by
  apply (cancel_epi (α_ _ _ _).hom).mp
  ext
  simp [w]

@[ext]

中文:
定理 leftDistributor_ext₂_left
  结论: {J : 类型} [有限 J]
  证明: by
  apply (cancel_epi (α_ _ _ _).hom).mp
  ext
  simp [w]

@[ext]

Depends on / 依赖: cancel_epi, infer_instance, ofLEMk
-/
theorem leftDistributor_ext₂_left {J : Type} [Finite J]
    {X Y Z : C} {f : J -> C} {g h : X otimes (Y otimes ⨁ f) ⟶ Z}
    (w : forall j, (X ◁ (Y ◁ biproduct.ι f j)) ≫ g = (X ◁ (Y ◁ biproduct.ι f j)) ≫ h) :
    g = h := by
  apply (cancel_epi (α_ _ _ _).hom).mp
  ext
  simp [w]

@[ext]
/--
theorem `leftDistributor_ext₂_right` / 定理 `leftDistributor_ext₂_right`

English:
theorem leftDistributor_ext₂_right
  statement: {J : Type} [Finite J]
  proof: by
  apply (cancel_mono (α_ _ _ _).inv).mp
  ext
  simp [w]

@[ext]

中文:
定理 leftDistributor_ext₂_right
  结论: {J : 类型} [有限 J]
  证明: by
  apply (cancel_mono (α_ _ _ _).inv).mp
  ext
  simp [w]

@[ext]

Depends on / 依赖: cancel_mono
-/
theorem leftDistributor_ext₂_right {J : Type} [Finite J]
    {X Y Z : C} {f : J -> C} {g h : X ⟶ Y otimes (Z otimes ⨁ f)}
    (w : forall j, g ≫ (Y ◁ (Z ◁ biproduct.π f j)) = h ≫ (Y ◁ (Z ◁ biproduct.π f j))) :
    g = h := by
  apply (cancel_mono (α_ _ _ _).inv).mp
  ext
  simp [w]

@[ext]
/--
theorem `rightDistributor_ext_left` / 定理 `rightDistributor_ext_left`

English:
theorem rightDistributor_ext_left
  statement: {J : Type} [Finite J]
  proof: by
  cases nonempty_fintype J
  apply (cancel_epi (rightDistributor f X).inv).mp
  ext
  simp [w]

@[ext]

中文:
定理 rightDistributor_ext_left
  结论: {J : 类型} [有限 J]
  证明: by
  cases nonempty_fintype J
  apply (cancel_epi (rightDistributor f X).inv).mp
  ext
  simp [w]

@[ext]

Depends on / 依赖: cancel_epi, nonempty_fintype, rightDistributor
-/
theorem rightDistributor_ext_left {J : Type} [Finite J]
    {f : J -> C} {X Y : C} {g h : (⨁ f) otimes X ⟶ Y}
    (w : forall j, (biproduct.ι f j ▷ X) ≫ g = (biproduct.ι f j ▷ X) ≫ h) : g = h := by
  cases nonempty_fintype J
  apply (cancel_epi (rightDistributor f X).inv).mp
  ext
  simp [w]

@[ext]
/--
theorem `rightDistributor_ext_right` / 定理 `rightDistributor_ext_right`

English:
theorem rightDistributor_ext_right
  statement: {J : Type} [Finite J]
  proof: by
  cases nonempty_fintype J
  apply (cancel_mono (rightDistributor f Y).hom).mp
  ext
  simp [w]

@[ext]

中文:
定理 rightDistributor_ext_right
  结论: {J : 类型} [有限 J]
  证明: by
  cases nonempty_fintype J
  apply (cancel_mono (rightDistributor f Y).hom).mp
  ext
  simp [w]

@[ext]

Depends on / 依赖: cancel_mono, infer_instance, nonempty_fintype, ofMkLE, rightDistributor
-/
theorem rightDistributor_ext_right {J : Type} [Finite J]
    {f : J -> C} {X Y : C} {g h : X ⟶ (⨁ f) otimes Y}
    (w : forall j, g ≫ (biproduct.π f j ▷ Y) = h ≫ (biproduct.π f j ▷ Y)) : g = h := by
  cases nonempty_fintype J
  apply (cancel_mono (rightDistributor f Y).hom).mp
  ext
  simp [w]

@[ext]
/--
theorem `rightDistributor_ext₂_left` / 定理 `rightDistributor_ext₂_left`

English:
theorem rightDistributor_ext₂_left
  statement: {J : Type} [Finite J]
  proof: by
  apply (cancel_epi (α_ _ _ _).inv).mp
  ext
  simp [w]

@[ext]

中文:
定理 rightDistributor_ext₂_left
  结论: {J : 类型} [有限 J]
  证明: by
  apply (cancel_epi (α_ _ _ _).inv).mp
  ext
  simp [w]

@[ext]

Depends on / 依赖: cancel_epi
-/
theorem rightDistributor_ext₂_left {J : Type} [Finite J]
    {f : J -> C} {X Y Z : C} {g h : ((⨁ f) otimes X) otimes Y ⟶ Z}
    (w : forall j, ((biproduct.ι f j ▷ X) ▷ Y) ≫ g = ((biproduct.ι f j ▷ X) ▷ Y) ≫ h) :
    g = h := by
  apply (cancel_epi (α_ _ _ _).inv).mp
  ext
  simp [w]

@[ext]
/--
theorem `rightDistributor_ext₂_right` / 定理 `rightDistributor_ext₂_right`

English:
theorem rightDistributor_ext₂_right
  statement: {J : Type} [Finite J]
  proof: by
  apply (cancel_mono (α_ _ _ _).hom).mp
  ext
  simp [w]

中文:
定理 rightDistributor_ext₂_right
  结论: {J : 类型} [有限 J]
  证明: by
  apply (cancel_mono (α_ _ _ _).hom).mp
  ext
  simp [w]

Depends on / 依赖: cancel_mono
-/
theorem rightDistributor_ext₂_right {J : Type} [Finite J]
    {f : J -> C} {X Y Z : C} {g h : X ⟶ ((⨁ f) otimes Y) otimes Z}
    (w : forall j, g ≫ ((biproduct.π f j ▷ Y) ▷ Z) = h ≫ ((biproduct.π f j ▷ Y) ▷ Z)) :
    g = h := by
  apply (cancel_mono (α_ _ _ _).hom).mp
  ext
  simp [w]

end CategoryTheory
