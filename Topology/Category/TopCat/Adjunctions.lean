/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro
-/
module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions regarding the category of topological spaces

This file shows that the forgetful functor from topological spaces to types has a left and right
adjoint, given by `TopCat.discrete`, resp. `TopCat.trivial`, the functors which equip a type with
the discrete, resp. trivial, topology.
-/

@[expose] public section


universe u

open CategoryTheory

open TopCat

namespace TopCat

/-- Equipping a type with the discrete topology is left adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps! unit counit]
/-
**TopCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equipping a type with the discrete topology is left adjoint to the forgetful fun
ctor
`Top ⥤ Type`.
-/
def adj₁ : discrete ⊣ forget TopCat.{u} where
  unit := 𝟙 _
  counit := { app := fun X => TopCat.ofHom (X := discrete.obj X) ⟨id, continuous_bot⟩ }

/-- Equipping a type with the trivial topology is right adjoint to the forgetful functor
`Top ⥤ Type`. -/
@[simps! unit counit]
/-
**TopCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equipping a type with the trivial topology is right adjoint to the forgetful fun
ctor
`Top ⥤ Type`.
-/
def adj₂ : forget TopCat.{u} ⊣ trivial where
  unit := { app := fun X => TopCat.ofHom (Y := trivial.obj X) ⟨id, continuous_top⟩ }
  counit := 𝟙 _
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget TopCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj₁⟩⟩
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget TopCat.{u}).IsLeftAdjoint :=
  ⟨_, ⟨adj₂⟩⟩

end TopCat

