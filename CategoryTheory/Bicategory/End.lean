/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Endomorphisms of an object in a bicategory, as a monoidal category.
-/

public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Bicategory.{w, v} C]

/--
Definition of `EndMonoidal` / `EndMonoidal` 的定义

English:
abbreviation EndMonoidal
  signature: (X : C)
  body: X ⟶ X

中文:
缩写 EndMonoidal
  签名: (X : C)
  定义体: X ⟶ X
-/
abbrev EndMonoidal (X : C) :=
  X ⟶ X
-- The `Category` instance should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

instance (X : C) : Category (EndMonoidal X) :=
  show Category (X ⟶ X) from inferInstance

instance (X : C) : Inhabited (EndMonoidal X) :=
  ⟨𝟙 X⟩

open Bicategory

open MonoidalCategory

@[simps]
instance (X : C) : MonoidalCategory (X ⟶ X) where
  tensorObj f g := f ≫ g
  whiskerLeft {f _ _} η := f ◁ η
  whiskerRight {_ _} η h := η ▷ h
  tensorUnit := 𝟙 _
  associator f g h := α_ f g h
  leftUnitor f := fun_ f
  rightUnitor f := ρ_ f
  tensorHom_comp_tensorHom := by
    intros
    dsimp only
    rw [Bicategory.whiskerLeft_comp]; rw [Bicategory.comp_whiskerRight]; rw [Category.assoc]; rw [Category.assoc]; rw [Bicategory.whisker_exchange_assoc]

end CategoryTheory
