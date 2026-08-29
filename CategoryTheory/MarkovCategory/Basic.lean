/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Markov Categories

Copy-discard categories where deletion is natural for all morphisms.

## Main definitions

* `MarkovCategory` - Copy-discard category with natural deletion

## Main results

* `eq_discard` - Any morphism to the unit equals discard
* `isTerminalUnit` - The monoidal unit is terminal

## Implementation notes

Natural discard forces probabilistic interpretation: morphisms preserve normalization. The unit
being terminal follows from naturality of discard.

The key property `discard_natural : f ≫ ε[Y] = ε[X]` means discard "erases" any preceding
morphism, a distinguishing feature of Markov categories in categorical probability.

## References

* [Cho and Jacobs, *Disintegration and Bayesian inversion via string diagrams*][cho_jacobs_2019]
* [Fritz, *A synthetic approach to Markov kernels, conditional independence
  and theorems on sufficient statistics*][fritz2020]

## Tags

Markov category, probability, categorical probability
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory CopyDiscardCategory ComonObj Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/--
Definition of `MarkovCategory` / `MarkovCategory` 的定义

English:
class MarkovCategory
  parameters: (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
  extends: CopyDiscardCategory C
  axioms and operations (1):
    - discard_natural({X Y : C} (f : X ⟶ Y)) : f ≫ ε[Y] = ε[X]

中文:
类 MarkovCategory
  参数: (C : 类型u) [Category.{v} C] [MonoidalCategory.{v} C]
  继承: CopyDiscardCategory C
  公理与运算 (1 个):
    - discard_natural({X Y : C} (f : X ⟶ Y)) : f ≫ ε[Y] = ε[X]
-/
class MarkovCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C]
    extends CopyDiscardCategory C where
  /-- Process then discard equals discard directly. -/
  discard_natural {X Y : C} (f : X ⟶ Y) : f ≫ ε[Y] = ε[X]

namespace MarkovCategory

variable [MarkovCategory C]

attribute [reassoc (attr := simp)] discard_natural

/--
theorem `eq_discard` / 定理 `eq_discard`

English:
theorem eq_discard
  given: (X : C) (f : X ⟶ 𝟙_ C)
  statement: f = ε[X]
  proof: by
  rw [← Category.comp_id f]; rw [← discard_unit]; rw [discard_natural]

中文:
定理 eq_discard
  条件: (X : C) (f : X ⟶ 𝟙_ C)
  结论: f = ε[X]
  证明: by
  rw [← Category.comp_id f]; rw [← discard_unit]; rw [discard_natural]

Depends on / 依赖: Category, Category.comp_id, comp_id, discard_natural, discard_unit
-/
theorem eq_discard (X : C) (f : X ⟶ 𝟙_ C) : f = ε[X] := by
  rw [← Category.comp_id f]; rw [← discard_unit]; rw [discard_natural]

/--
Definition of `isTerminalUnit` / `isTerminalUnit` 的定义

English:
definition isTerminalUnit
  signature: : IsTerminal (𝟙_ C)
  body: IsTerminal.ofUniqueHom _ eq_discard

中文:
定义 isTerminalUnit
  签名: : IsTerminal (𝟙_ C)
  定义体: IsTerminal.ofUniqueHom _ eq_discard

Depends on / 依赖: IsTerminal, IsTerminal.ofUniqueHom, eq_discard, ofUniqueHom
-/
def isTerminalUnit : IsTerminal (𝟙_ C) :=
  IsTerminal.ofUniqueHom _ eq_discard

/-- There is a unique morphism to the unit (it is terminal). -/
instance (X : C) : Subsingleton (X ⟶ 𝟙_ C) where
  allEq := isTerminalUnit.hom_ext

end MarkovCategory

end CategoryTheory
