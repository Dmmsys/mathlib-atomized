/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# The opposite of a model category structure

-/

public section

universe v u

open CategoryTheory

namespace HomotopicalAlgebra

variable (C : Type u) [Category.{v} C] [ModelCategory C]

/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences Cᵒᵖ).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_op]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences Cᵒᵖ).IsStableUnderRetracts := by
  rw [weakEquivalences_op]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(cofibrations C).IsStableUnderRetracts] :
    (fibrations Cᵒᵖ).IsStableUnderRetracts := by
  rw [fibrations_op]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(fibrations C).IsStableUnderRetracts] :
    (cofibrations Cᵒᵖ).IsStableUnderRetracts := by
  rw [cofibrations_op]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(trivialCofibrations C).HasFactorization (fibrations C)] :
    (cofibrations Cᵒᵖ).HasFactorization (trivialFibrations Cᵒᵖ) := by
  rw [cofibrations_op, trivialFibrations_op]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(cofibrations C).HasFactorization (trivialFibrations C)] :
    (trivialCofibrations Cᵒᵖ).HasFactorization (fibrations Cᵒᵖ) := by
  rw [trivialCofibrations_op, fibrations_op, ]
  infer_instance
/-
**HomotopicalAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ModelCategory Cᵒᵖ where
  cm4a i p _ _ _ := (HasLiftingProperty.iff_unop i p).2 inferInstance
  cm4b i p _ _ _ := (HasLiftingProperty.iff_unop i p).2 inferInstance

end HomotopicalAlgebra

