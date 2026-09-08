/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Set.Basic

/-!
# The functor from `Set X` to types

Given `X : Type u`, we define the functor `Set.functorToTypes : Set X ⥤ Type u`
which sends `A : Set X` to its underlying type.

-/

@[expose] public section

universe u

open CategoryTheory

namespace Set

/-- Given `X : Type u`, this is the functor `Set X ⥤ Type u` which sends `A`
to its underlying type. -/
@[simps obj map]
/-
**Set.functorToTypes** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：functorToTypes {X : Type u} : Set X ⥤ Type u where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : Type u`, this is the functor `Set X ⥤ Type u` which sends `A`
to its underlying type.
-/
def functorToTypes {X : Type u} : Set X ⥤ Type u where
  obj S := S
  map {S T} f := ↾fun ⟨x, hx⟩ ↦ ⟨x, leOfHom f hx⟩

end Set

