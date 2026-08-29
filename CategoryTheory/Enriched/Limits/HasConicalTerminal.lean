/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Enriched.Limits.HasConicalProducts

/-!
# Existence of conical terminal objects
-/

public section

universe w v' v u u'

namespace CategoryTheory.Enriched

open Limits HasConicalLimit

/--
Definition of `HasConicalTerminal` / `HasConicalTerminal` 的定义

English:
abbreviation HasConicalTerminal
  body: HasConicalLimitsOfShape (Discrete.{0} PEmpty)

中文:
缩写 HasConicalTerminal
  定义体: HasConicalLimitsOfShape (Discrete.{0} PEmpty)

Depends on / 依赖: Discrete, HasConicalLimitsOfShape, PEmpty
-/
abbrev HasConicalTerminal := HasConicalLimitsOfShape (Discrete.{0} PEmpty)

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

example [HasConicalTerminal V C] : HasTerminal C := inferInstance

/--
Instance `HasConicalProducts.hasConicalTerminal` / 实例 `HasConicalProducts.hasConicalTerminal`

English:
instance HasConicalProducts.hasConicalTerminal
  signature: [HasConicalProducts.{w} V C]
  body: HasConicalLimitsOfShape.of_equiv V C emptyEquivalence.functor

中文:
实例 有余nicalProducts.hasConicalTerminal
  签名: [有余nicalProducts.{w} V C]
  定义体: HasConicalLimitsOfShape.of_equiv V C emptyEquivalence.functor

Depends on / 依赖: HasConicalLimitsOfShape, HasConicalLimitsOfShape.of_equiv, emptyEquivalence, emptyEquivalence.functor, functor, of_equiv
-/
instance HasConicalProducts.hasConicalTerminal [HasConicalProducts.{w} V C] :
    HasConicalTerminal V C :=
  HasConicalLimitsOfShape.of_equiv V C emptyEquivalence.functor

end CategoryTheory.Enriched
