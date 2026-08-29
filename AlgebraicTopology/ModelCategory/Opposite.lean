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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(weakEquivalences
  signature: C).HasTwoOutOfThreeProperty] :
  body: by
  rw [weakEquivalences_op]
  infer_instance

中文:
实例 [(weakEquivalences
  签名: C).有TwoOutOfThreeProperty] :
  定义体: by
  rw [weakEquivalences_op]
  infer_instance

Depends on / 依赖: infer_instance, weakEquivalences_op
-/
instance [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences Cᵒᵖ).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_op]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(weakEquivalences
  signature: C).IsStableUnderRetracts] :
  body: by
  rw [weakEquivalences_op]
  infer_instance

中文:
实例 [(weakEquivalences
  签名: C).是StableUnderRetracts] :
  定义体: by
  rw [weakEquivalences_op]
  infer_instance

Depends on / 依赖: infer_instance, weakEquivalences_op
-/
instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences Cᵒᵖ).IsStableUnderRetracts := by
  rw [weakEquivalences_op]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(cofibrations
  signature: C).IsStableUnderRetracts] :
  body: by
  rw [fibrations_op]
  infer_instance

中文:
实例 [(cofibrations
  签名: C).是StableUnderRetracts] :
  定义体: by
  rw [fibrations_op]
  infer_instance

Depends on / 依赖: fibrations_op, infer_instance
-/
instance [(cofibrations C).IsStableUnderRetracts] :
    (fibrations Cᵒᵖ).IsStableUnderRetracts := by
  rw [fibrations_op]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(fibrations
  signature: C).IsStableUnderRetracts] :
  body: by
  rw [cofibrations_op]
  infer_instance

中文:
实例 [(fibrations
  签名: C).是StableUnderRetracts] :
  定义体: by
  rw [cofibrations_op]
  infer_instance

Depends on / 依赖: cofibrations_op, infer_instance
-/
instance [(fibrations C).IsStableUnderRetracts] :
    (cofibrations Cᵒᵖ).IsStableUnderRetracts := by
  rw [cofibrations_op]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(trivialCofibrations
  signature: C).HasFactorization (fibrations C)] :
  body: by
  rw [cofibrations_op]; rw [trivialFibrations_op]
  infer_instance

中文:
实例 [(trivialCofibrations
  签名: C).有分解 (fibrations C)] :
  定义体: by
  rw [cofibrations_op]; rw [trivialFibrations_op]
  infer_instance

Depends on / 依赖: cofibrations_op, infer_instance, trivialFibrations_op
-/
instance [(trivialCofibrations C).HasFactorization (fibrations C)] :
    (cofibrations Cᵒᵖ).HasFactorization (trivialFibrations Cᵒᵖ) := by
  rw [cofibrations_op]; rw [trivialFibrations_op]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(cofibrations
  signature: C).HasFactorization (trivialFibrations C)] :
  body: by
  rw [trivialCofibrations_op]; rw [fibrations_op]
  infer_instance

中文:
实例 [(cofibrations
  签名: C).有分解 (trivialFibrations C)] :
  定义体: by
  rw [trivialCofibrations_op]; rw [fibrations_op]
  infer_instance

Depends on / 依赖: fibrations_op, infer_instance, trivialCofibrations_op
-/
instance [(cofibrations C).HasFactorization (trivialFibrations C)] :
    (trivialCofibrations Cᵒᵖ).HasFactorization (fibrations Cᵒᵖ) := by
  rw [trivialCofibrations_op]; rw [fibrations_op]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ModelCategory Cᵒᵖ
  body: (HasLiftingProperty.iff_unop i p).2 inferInstance
  cm4b i p _ _ _ := (HasLiftingProperty.iff_unop i p).2 inferInstance

中文:
实例 :
  签名: 模型范畴 Cᵒᵖ
  定义体: (HasLiftingProperty.iff_unop i p).2 inferInstance
  cm4b i p _ _ _ := (HasLiftingProperty.iff_unop i p).2 inferInstance

Depends on / 依赖: HasLiftingProperty, HasLiftingProperty.iff_unop, iff_unop
-/
instance : ModelCategory Cᵒᵖ where
  cm4a i p _ _ _ := (HasLiftingProperty.iff_unop i p).2 inferInstance
  cm4b i p _ _ _ := (HasLiftingProperty.iff_unop i p).2 inferInstance

end HomotopicalAlgebra
