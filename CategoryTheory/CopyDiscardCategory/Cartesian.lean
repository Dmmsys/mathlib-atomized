/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
public import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Comon_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Cartesian Categories as Copy-Discard Categories

Every cartesian monoidal category is a copy-discard category where:
- Copy is the diagonal map
- Discard is the unique map to terminal

## Main results

* `CopyDiscardCategory` instance for cartesian monoidal categories
* All morphisms in cartesian categories are deterministic

## Tags

cartesian, copy-discard, comonoid, symmetric monoidal
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory.{v} C]

namespace CartesianCopyDiscard

/--
Definition of `instComonObjOfCartesian` / `instComonObjOfCartesian` 的定义

English:
abbreviation instComonObjOfCartesian
  signature: (X : C)
  body: ((cartesianComon C).obj X).comon

中文:
缩写 instComonObjOfCartesian
  签名: (X : C)
  定义体: ((cartesianComon C).obj X).comon

Depends on / 依赖: cartesianComon
-/
abbrev instComonObjOfCartesian (X : C) : ComonObj X :=
  ((cartesianComon C).obj X).comon

attribute [local instance] instComonObjOfCartesian

variable [BraidedCategory C]

/--
Instance `instIsCommComonObjOfCartesian` / 实例 `instIsCommComonObjOfCartesian`

English:
instance instIsCommComonObjOfCartesian
  signature: (X : C)

中文:
实例 instIsCommComonObjOfCartesian
  签名: (X : C)
-/
instance instIsCommComonObjOfCartesian (X : C) : IsCommComonObj X where

/--
Definition of `ofCartesianMonoidalCategory` / `ofCartesianMonoidalCategory` 的定义

English:
abbreviation ofCartesianMonoidalCategory
  signature: : CopyDiscardCategory C where

中文:
缩写 ofCartesianMonoidalCategory
  签名: : 余pyDiscard范畴 C where
-/
abbrev ofCartesianMonoidalCategory : CopyDiscardCategory C where

attribute [local instance] ofCartesianMonoidalCategory

/--
Instance `instDeterministic` / 实例 `instDeterministic`

English:
instance instDeterministic
  signature: {X Y : C} (f : X ⟶ Y)

中文:
实例 instDeterministic
  签名: {X Y : C} (f : X ⟶ Y)
-/
instance instDeterministic {X Y : C} (f : X ⟶ Y) : Deterministic f where

end CartesianCopyDiscard

end CategoryTheory
