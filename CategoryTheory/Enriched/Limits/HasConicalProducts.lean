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

/-- Has conical products if all discrete diagrams of bounded size have conical products. -/
/-
**CategoryTheory.Enriched.HasConicalProducts** 是 Mathlib 中的一个类，位于命名空间 `CategoryT
heory.Enriched`。
形式化陈述：HasConicalProducts (V : outParam <| Type u') [Category.{v'} V] [MonoidalCa
tegory V] (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] : Prop wh
ere /-- A family of objects (parametrized by any `J : Type w`) has a conical pro
duct. -/ hasConicalLimitsOfShape : forall J : Type w, HasConicalLimitsOfShape (D
iscrete J) V C
参数：V : outParam <| Type u'；C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Has conical products if all discrete diagrams of bounded size have conical produ
cts.
-/
class HasConicalProducts
    (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
    (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] : Prop where
  /-- A family of objects (parametrized by any `J : Type w`) has a conical product. -/
  hasConicalLimitsOfShape : ∀ J : Type w, HasConicalLimitsOfShape (Discrete J) V C := by
    infer_instance

attribute [instance] HasConicalProducts.hasConicalLimitsOfShape

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- An abbreviation for `HasConicalLimit V (Discrete.functor f)`. -/
/-
**CategoryTheory.Enriched.HasConicalProduct** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Enriched`。
形式化陈述：HasConicalProduct {I : Type w} (f : I -> C)
参数：f : I -> C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `HasConicalLimit V (Discrete.functor f)`.
-/
abbrev HasConicalProduct {I : Type w} (f : I → C) :=
  HasConicalLimit V (Discrete.functor f)

/-- ensure products exists from the existence of conical products -/
/-
**CategoryTheory.Enriched.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Enriched`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
ensure products exists from the existence of conical products
-/
example [HasConicalProducts.{w} V C] : HasProducts.{w} C := inferInstance

end CategoryTheory.Enriched

