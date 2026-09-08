/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Additional typeclass for modules over an algebra

For an object in `M : ModuleCat A`, where `A` is a `k`-algebra,
we provide additional typeclasses on the underlying type `M`,
namely `Module k M` and `IsScalarTower k A M`.
These are not made into instances by default.

We provide the `Linear k (ModuleCat A)` instance.

## Note

If you begin with a `[Module k M] [Module A M] [IsScalarTower k A M]`,
and build a bundled module via `ModuleCat.of A M`,
these instances will not necessarily agree with the original ones.

It seems without making a parallel version `ModuleCat' k A`, for modules over a `k`-algebra `A`,
that carries these typeclasses, this seems hard to achieve.
(An alternative would be to always require these typeclasses, and remove the original `ModuleCat`,
requiring users to write `ModuleCat' ℤ A` when `A` is merely a ring.)
-/

@[expose] public section


universe v u w

open CategoryTheory

namespace ModuleCat

variable {k : Type u} [Field k]
variable {A : Type w} [Ring A] [Algebra k A]

/-- Type synonym for considering a module over a `k`-algebra as a `k`-module. -/
@[instance_reducible]
/-
**ModuleCat.moduleOfAlgebraModule** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：moduleOfAlgebraModule (M : ModuleCat.{v} A) : Module k M
参数：M : ModuleCat.{v} A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym for considering a module over a `k`-algebra as a `k`-module.
-/
def moduleOfAlgebraModule (M : ModuleCat.{v} A) : Module k M :=
  Module.restrictScalars k A M

attribute [scoped instance] ModuleCat.moduleOfAlgebraModule
/-
**ModuleCat.isScalarTower_of_algebra_moduleCat** 是 Mathlib 中的一个定理，位于命名空间 `Module
Cat`。
形式化陈述：isScalarTower_of_algebra_moduleCat (M : ModuleCat.{v} A) : IsScalarTower k
 A M
参数：M : ModuleCat.{v} A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.restrictScalars`：IsScalarTower.restrictScalars [Module S M
] : letI
-/
theorem isScalarTower_of_algebra_moduleCat (M : ModuleCat.{v} A) : IsScalarTower k A M :=
  IsScalarTower.restrictScalars k A M

attribute [scoped instance] ModuleCat.isScalarTower_of_algebra_moduleCat

-- We verify that the morphism spaces become `k`-modules.
/-
**ModuleCat.** 是 Mathlib 中的一个示例，位于命名空间 `ModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (M N : ModuleCat.{v} A) : Module k (M ⟶ N) := inferInstance
/-
**ModuleCat.linearOverField** 是 Mathlib 中的一个实例，位于命名空间 `ModuleCat`。
形式化陈述：linearOverField : Linear k (ModuleCat.{v} A) where homModule _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOverField : Linear k (ModuleCat.{v} A) where
  homModule _ _ := inferInstance

end ModuleCat

