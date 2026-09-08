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

/-- A category has a conical terminal object
if it has a conical limit over the empty diagram. -/
/-
**CategoryTheory.Enriched.HasConicalTerminal** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.Enriched`。
形式化陈述：HasConicalTerminal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has a conical terminal object
if it has a conical limit over the empty diagram.
-/
abbrev HasConicalTerminal := HasConicalLimitsOfShape (Discrete.{0} PEmpty)

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]
/-
**CategoryTheory.Enriched.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Enriched`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [HasConicalTerminal V C] : HasTerminal C := inferInstance
/-
**CategoryTheory.Enriched.HasConicalProducts.hasConicalTerminal** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Enriched.HasConicalProducts`。
形式化陈述：∀ (V : Type u') [inst : CategoryTheory.Category.{v', u'} V] [inst_1 : Cate
goryTheory.MonoidalCategory V] (C : Type u)   [inst_2 : CategoryTheory.Category.
{v, u} C] [inst_3 : CategoryTheory.EnrichedOrdinaryCategory V C]   [CategoryTheo
ry.Enriched.HasConicalProducts V C], CategoryTheory.Enriched.HasConicalTerminal 
V C
参数：V : Type u'；C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Enriched.HasConicalLimitsOfShape.of_equiv`：∀ {J : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} J] {J' : Type u₂}   [inst_1 : Categor
yTheory.Category.{v₂, u₂} J'] (V : Type u') [i…
· 使用定理 `CategoryTheory.Enriched.HasConicalProducts.hasConicalLimitsOfShape`：∀ {V
 : outParam (Type u')} {inst : CategoryTheory.Category.{v', u'} V} {inst_1 : Cat
egoryTheory.MonoidalCategory V}   {C : Type u} {inst_2 :…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance HasConicalProducts.hasConicalTerminal [HasConicalProducts.{w} V C] :
    HasConicalTerminal V C :=
  HasConicalLimitsOfShape.of_equiv V C emptyEquivalence.functor

end CategoryTheory.Enriched

