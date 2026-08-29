/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits

/-!
# Existence of conical pullbacks
-/

public section

universe w v' v u u'

namespace CategoryTheory.Enriched

open Limits

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/--
Definition of `HasConicalPullback` / `HasConicalPullback` 的定义

English:
abbreviation HasConicalPullback
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  body: HasConicalLimit V (cospan f g)

中文:
缩写 HasConicalPullback
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: HasConicalLimit V (cospan f g)

Depends on / 依赖: HasConicalLimit, cospan
-/
abbrev HasConicalPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasConicalLimit V (cospan f g)

/-- ensure conical pullbacks are pullbacks -/
example {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasConicalPullback V f g] : HasPullback f g :=
  inferInstance

variable (C)

/--
Definition of `HasConicalPullbacks` / `HasConicalPullbacks` 的定义

English:
abbreviation HasConicalPullbacks
  signature: : Prop
  body: HasConicalLimitsOfShape WalkingCospan V C

中文:
缩写 HasConicalPullbacks
  签名: : 命题
  定义体: HasConicalLimitsOfShape WalkingCospan V C

Depends on / 依赖: HasConicalLimitsOfShape, WalkingCospan
-/
abbrev HasConicalPullbacks : Prop := HasConicalLimitsOfShape WalkingCospan V C

/-- Ensure pullbacks exist from the existence of conical pullbacks. -/
example [HasConicalPullbacks V C] : HasPullbacks C := inferInstance

end CategoryTheory.Enriched
