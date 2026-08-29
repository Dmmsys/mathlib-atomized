/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Enriched.Limits.HasConicalLimits

/-!
# Existence of conical products
-/

public section

universe w v' v u u'

namespace CategoryTheory.Enriched

open Limits

/--
Definition of `HasConicalProducts` / `HasConicalProducts` 的定义

English:
class HasConicalProducts
  axioms and operations (1):
    - hasConicalLimitsOfShape : forall J : Type w, HasConicalLimitsOfShape (Discrete J) V C  [default: by infer_instance]

中文:
类 有余nicalProducts
  公理与运算 (1 个):
    - hasConicalLimitsOfShape : 对任意 J : 类型 w, 有余nicalLimitsOfShape (离散 J) V C  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasConicalProducts
    (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
    (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] : Prop where
  /-- A family of objects (parametrized by any `J : Type w`) has a conical product. -/
  hasConicalLimitsOfShape : forall J : Type w, HasConicalLimitsOfShape (Discrete J) V C := by
    infer_instance

attribute [instance] HasConicalProducts.hasConicalLimitsOfShape

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/--
Definition of `HasConicalProduct` / `HasConicalProduct` 的定义

English:
abbreviation HasConicalProduct
  signature: {I : Type w} (f : I -> C)
  body: HasConicalLimit V (Discrete.functor f)

中文:
缩写 HasConicalProduct
  签名: {I : 类型 w} (f : I -> C)
  定义体: HasConicalLimit V (Discrete.functor f)

Depends on / 依赖: Discrete, Discrete.functor, HasConicalLimit, functor
-/
abbrev HasConicalProduct {I : Type w} (f : I -> C) :=
  HasConicalLimit V (Discrete.functor f)

/-- ensure products exists from the existence of conical products -/
example [HasConicalProducts.{w} V C] : HasProducts.{w} C := inferInstance

end CategoryTheory.Enriched
