/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Linear monoidal categories

A monoidal category is `MonoidalLinear R` if it is monoidal preadditive and
tensor product of morphisms is `R`-linear in both factors.
-/

public section


namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (R : Type*) [Semiring R]
variable (C : Type*) [Category* C] [Preadditive C] [Linear R C]
variable [MonoidalCategory C]

/--
Definition of `MonoidalLinear` / `MonoidalLinear` 的定义

English:
class MonoidalLinear
  parameters: [MonoidalPreadditive C]
  axioms and operations (2):
    - whiskerLeft_smul : forall (X : C) {Y Z : C} (r : R) (f : Y ⟶ Z), X ◁ (r • f) = r • (X ◁ f)  [default: by cat_disch]
    - smul_whiskerRight : forall (r : R) {Y Z : C} (f : Y ⟶ Z) (X : C), (r • f) ▷ X = r • (f ▷ X)  [default: by cat_disch]

中文:
类 幺半群线性
  参数: [幺半群预加性 C]
  公理与运算 (2 个):
    - whiskerLeft_smul : 对任意 (X : C) {Y Z : C} (r : R) (f : Y ⟶ Z), X ◁ (r • f) = r • (X ◁ f)  [默认: by cat_disch]
    - smul_whiskerRight : 对任意 (r : R) {Y Z : C} (f : Y ⟶ Z) (X : C), (r • f) ▷ X = r • (f ▷ X)  [默认: by cat_disch]

Depends on / 依赖: cat_disch, smul_whiskerRight
-/
class MonoidalLinear [MonoidalPreadditive C] : Prop where
  whiskerLeft_smul : forall (X : C) {Y Z : C} (r : R) (f : Y ⟶ Z), X ◁ (r • f) = r • (X ◁ f) := by
    cat_disch
  smul_whiskerRight : forall (r : R) {Y Z : C} (f : Y ⟶ Z) (X : C), (r • f) ▷ X = r • (f ▷ X) := by
    cat_disch

attribute [simp] MonoidalLinear.whiskerLeft_smul MonoidalLinear.smul_whiskerRight

variable {C}
variable [MonoidalPreadditive C] [MonoidalLinear R C]

/--
Instance `tensorLeft_linear` / 实例 `tensorLeft_linear`

English:
instance tensorLeft_linear
  signature: (X : C)

中文:
实例 tensorLeft_linear
  签名: (X : C)
-/
instance tensorLeft_linear (X : C) : (tensorLeft X).Linear R where

/--
Instance `tensorRight_linear` / 实例 `tensorRight_linear`

English:
instance tensorRight_linear
  signature: (X : C)

中文:
实例 tensorRight_linear
  签名: (X : C)
-/
instance tensorRight_linear (X : C) : (tensorRight X).Linear R where

/--
Instance `tensoringLeft_linear` / 实例 `tensoringLeft_linear`

English:
instance tensoringLeft_linear
  signature: (X : C)

中文:
实例 tensoringLeft_linear
  签名: (X : C)
-/
instance tensoringLeft_linear (X : C) : ((tensoringLeft C).obj X).Linear R where

/--
Instance `tensoringRight_linear` / 实例 `tensoringRight_linear`

English:
instance tensoringRight_linear
  signature: (X : C)

中文:
实例 tensoringRight_linear
  签名: (X : C)
-/
instance tensoringRight_linear (X : C) : ((tensoringRight C).obj X).Linear R where

/--
theorem `MonoidalLinear.ofFaithful` / 定理 `MonoidalLinear.ofFaithful`

English:
theorem MonoidalLinear.ofFaithful
  statement: {D : Type*} [Category* D] [Preadditive D] [Linear R D]
  proof: { whiskerLeft_smul := by
      intro X Y Z r f
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerLeft]
      simp
    smul_whiskerRight := by
      intro r X Y f Z
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerRight]
      simp }

中文:
定理 幺半群线性.ofFaithful
  结论: {D : 类型} [范畴* D] [预加性 D] [线性 R D]
  证明: { whiskerLeft_smul := by
      intro X Y Z r f
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerLeft]
      simp
    smul_whiskerRight := by
      intro r X Y f Z
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerRight]
      simp }

Depends on / 依赖: F.map_injective, Functor, Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_whiskerRight, Monoidal, map_injective, map_whiskerLeft, map_whiskerRight, smul_whiskerRight, whiskerLeft_smul
-/
theorem MonoidalLinear.ofFaithful {D : Type*} [Category* D] [Preadditive D] [Linear R D]
    [MonoidalCategory D] [MonoidalPreadditive D] (F : D ⥤ C) [F.Monoidal] [F.Faithful]
    [F.Linear R] : MonoidalLinear R D :=
  { whiskerLeft_smul := by
      intro X Y Z r f
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerLeft]
      simp
    smul_whiskerRight := by
      intro r X Y f Z
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerRight]
      simp }

end CategoryTheory
