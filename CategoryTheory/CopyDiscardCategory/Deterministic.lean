/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic

/-!
# Deterministic Morphisms in Copy-Discard Categories

Morphisms that preserve the copy operation perfectly.

A morphism `f : X → Y` is deterministic if copying then applying `f` to both copies equals applying
`f` then copying: `f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ f)`.

In probabilistic settings, these are morphisms without randomness. In cartesian categories, all
morphisms are deterministic.

## Main definitions

* `Deterministic` - Type class for morphisms that preserve copying

## Main results

* Identity morphisms are deterministic
* Composition of deterministic morphisms is deterministic

## Tags

deterministic, copy-discard category, comonoid morphism
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory.{v} C]

/--
Definition of `Deterministic` / `Deterministic` 的定义

English:
abbreviation Deterministic
  signature: {X Y : C} (f : X ⟶ Y)
  body: IsComonHom f

中文:
缩写 Deterministic
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: IsComonHom f

Depends on / 依赖: IsComonHom
-/
abbrev Deterministic {X Y : C} (f : X ⟶ Y) := IsComonHom f

namespace Deterministic

variable {X Y Z : C}

/--
lemma `copy_natural` / 引理 `copy_natural`

English:
lemma copy_natural
  given: (f : X ⟶ Y) [Deterministic f]
  statement: f ≫ Δ[Y] = Δ[X] ≫ (f otimesₘ f)
  proof: IsComonHom.hom_comul f

中文:
引理 copy_natural
  条件: (f : X ⟶ Y) [Deterministic f]
  结论: f ≫ Δ[Y] = Δ[X] ≫ (f otimesₘ f)
  证明: IsComonHom.hom_comul f

Depends on / 依赖: IsComonHom, IsComonHom.hom_comul, hom_comul
-/
lemma copy_natural (f : X ⟶ Y) [Deterministic f] : f ≫ Δ[Y] = Δ[X] ≫ (f otimesₘ f) :=
  IsComonHom.hom_comul f

/--
lemma `discard_natural` / 引理 `discard_natural`

English:
lemma discard_natural
  given: (f : X ⟶ Y) [Deterministic f]
  statement: f ≫ ε[Y] = ε[X]
  proof: IsComonHom.hom_counit f

中文:
引理 discard_natural
  条件: (f : X ⟶ Y) [Deterministic f]
  结论: f ≫ ε[Y] = ε[X]
  证明: IsComonHom.hom_counit f

Depends on / 依赖: IsComonHom, IsComonHom.hom_counit, hom_counit
-/
lemma discard_natural (f : X ⟶ Y) [Deterministic f] : f ≫ ε[Y] = ε[X] :=
  IsComonHom.hom_counit f

end Deterministic

end CategoryTheory
