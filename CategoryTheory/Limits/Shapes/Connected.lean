/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!

# Connected shapes

In this file we prove that various shapes are connected.

-/

public section

namespace CategoryTheory

open Limits

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J} : IsConnected (WidePullbackShape J) := by
  apply IsConnected.of_constant_of_preserves_morphisms
  intro α F H
  suffices ∀ i, F i = F none from fun j j' ↦ (this j).trans (this j').symm
  rintro ⟨⟩
  exacts [rfl, H (.term _)]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J} : IsConnected (WidePushoutShape J) := by
  apply IsConnected.of_constant_of_preserves_morphisms
  intro α F H
  suffices ∀ i, F i = F none from fun j j' ↦ (this j).trans (this j').symm
  rintro ⟨⟩
  exacts [rfl, (H (.init _)).symm]

end CategoryTheory

