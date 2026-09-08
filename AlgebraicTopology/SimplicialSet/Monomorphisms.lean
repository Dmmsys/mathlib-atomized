/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.Types.Monomorphisms

/-!
# Monomorphisms of simplicial sets

In this file, we show that the class of monomorphisms in `SSet` is stable
under coproducts, pushouts, filtered colimits and transfinite compositions.

-/

public section

universe v' u' u

open CategoryTheory Limits MorphismProperty

namespace SSet

/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasCoproducts.{v'} (Type u)] :
    IsStableUnderCoproducts.{v'} (monomorphisms SSet.{u}) :=
  inferInstanceAs (IsStableUnderCoproducts.{v'} (monomorphisms (_ ⥤ _)))
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (monomorphisms SSet).IsStableUnderCobaseChange := by
  change (monomorphisms (_ ⥤ _)).IsStableUnderCobaseChange
  rw [← functorCategory_monomorphisms]
  infer_instance
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsStableUnderFilteredColimits.{u, u} (monomorphisms SSet.{u}) where
  isStableUnderColimitsOfShape J _ _ := by
    change (monomorphisms (_ ⥤ _)).IsStableUnderColimitsOfShape J
    rw [← functorCategory_monomorphisms]
    infer_instance
/-
**SSet.** 是 Mathlib 中的一个示例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (K : Type u) [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K] :
    (monomorphisms SSet.{u}).IsStableUnderTransfiniteCompositionOfShape K := by
  infer_instance

end SSet

