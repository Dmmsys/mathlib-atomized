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

/-- `HasConicalPullback f g` represents the mere existence of a conical limit cone for the pair
of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` -/
/-
**CategoryTheory.Enriched.HasConicalPullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.Enriched`。
形式化陈述：HasConicalPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasConicalPullback f g` represents the mere existence of a conical limit cone f
or the pair
of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`
-/
abbrev HasConicalPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasConicalLimit V (cospan f g)

/-- ensure conical pullbacks are pullbacks -/
/-
**CategoryTheory.Enriched.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Enriched`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
ensure conical pullbacks are pullbacks
-/
example {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasConicalPullback V f g] : HasPullback f g :=
  inferInstance

variable (C)

/--
`HasConicalPullbacks` represents the existence of conical pullbacks for every pair of
morphisms.
-/
/-
**CategoryTheory.Enriched.HasConicalPullbacks** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Enriched`。
形式化陈述：HasConicalPullbacks : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasConicalPullbacks` represents the existence of conical pullbacks for every pa
ir of
morphisms.
-/
abbrev HasConicalPullbacks : Prop := HasConicalLimitsOfShape WalkingCospan V C

/-- Ensure pullbacks exist from the existence of conical pullbacks. -/
/-
**CategoryTheory.Enriched.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Enriched`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ensure pullbacks exist from the existence of conical pullbacks.
-/
example [HasConicalPullbacks V C] : HasPullbacks C := inferInstance

end CategoryTheory.Enriched

