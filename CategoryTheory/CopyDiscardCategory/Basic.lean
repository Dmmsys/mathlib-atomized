/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Copy-Discard Categories

Symmetric monoidal categories where every object has a commutative
comonoid structure compatible with tensor products.

## Main definitions

* `CopyDiscardCategory` - Category with coherent copy and delete

## Notations

* `Δ[X]` - Copy morphism for X (from `ComonObj`)
* `ε[X]` - Delete morphism for X (from `ComonObj`)

## Implementation notes

We use `ComonObj` instances to provide the comonoid structure.
The key axioms ensure tensor products respect the comonoid structure.

## References

* [Cho and Jacobs, *Disintegration and Bayesian inversion via string diagrams*][cho_jacobs_2019]
* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

copy-discard, comonoid, symmetric monoidal
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/--
Definition of `CopyDiscardCategory` / `CopyDiscardCategory` 的定义

English:
class CopyDiscardCategory
  parameters: (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
  extends: SymmetricCategory C
  axioms and operations (6):
    - [comonObj : (X : C) -> ComonObj X]
    - [isCommComonObj : (X : C) -> IsCommComonObj X]
    - copy_tensor((X Y : C)) : Δ[X otimes Y] = (Δ[X] otimesₘ Δ[Y]) ≫ tensorμ X X Y Y  [default: by cat_disch]
    - discard_tensor((X Y : C)) : ε[X otimes Y] = (ε[X] otimesₘ ε[Y]) ≫ (fun_ (𝟙_ C)).hom  [default: by cat_disch]
    - copy_unit : Δ[𝟙_ C] = (fun_ (𝟙_ C)).inv  [default: by cat_disch]
    - discard_unit : ε[𝟙_ C] = 𝟙 (𝟙_ C)  [default: by cat_disch]

中文:
类 CopyDiscardCategory
  参数: (C : 类型u) [Category.{v} C] [MonoidalCategory.{v} C]
  继承: SymmetricCategory C
  公理与运算 (6 个):
    - [comonObj : (X : C) -> ComonObj X]
    - [isCommComonObj : (X : C) -> IsCommComonObj X]
    - copy_tensor((X Y : C)) : Δ[X otimes Y] = (Δ[X] otimesₘ Δ[Y]) ≫ tensorμ X X Y Y  [默认: by cat_disch]
    - discard_tensor((X Y : C)) : ε[X otimes Y] = (ε[X] otimesₘ ε[Y]) ≫ (fun_ (𝟙_ C)).hom  [默认: by cat_disch]
    - copy_unit : Δ[𝟙_ C] = (fun_ (𝟙_ C)).inv  [默认: by cat_disch]
    - discard_unit : ε[𝟙_ C] = 𝟙 (𝟙_ C)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class CopyDiscardCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    extends SymmetricCategory C where
  /-- Every object has commutative comonoid structure. -/
  [comonObj : (X : C) -> ComonObj X]
  /-- Every object's comonoid structure is commutative. -/
  [isCommComonObj : (X : C) -> IsCommComonObj X]
  /-- Tensor products of copies equal copies of tensor products. -/
  copy_tensor (X Y : C) : Δ[X otimes Y] = (Δ[X] otimesₘ Δ[Y]) ≫ tensorμ X X Y Y := by cat_disch
  /-- Discard distributes over tensor. -/
  discard_tensor (X Y : C) : ε[X otimes Y] = (ε[X] otimesₘ ε[Y]) ≫ (fun_ (𝟙_ C)).hom := by cat_disch
    /-- Copy on the unit object. -/
  copy_unit : Δ[𝟙_ C] = (fun_ (𝟙_ C)).inv := by cat_disch
    /-- Discard on the unit object. -/
  discard_unit : ε[𝟙_ C] = 𝟙 (𝟙_ C) := by cat_disch

attribute [instance_reducible] CopyDiscardCategory.comonObj
attribute [instance] CopyDiscardCategory.comonObj CopyDiscardCategory.isCommComonObj

end CategoryTheory
