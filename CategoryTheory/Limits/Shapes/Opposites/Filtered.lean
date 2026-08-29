/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Filtered

/-!
# Filtered colimits and cofiltered limits in `C` and `Cᵒᵖ`

We construct filtered colimits and cofiltered limits in the opposite categories.

-/

public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]

/--
Instance `has_cofiltered_limits_op_of_has_filtered_colimits` / 实例 `has_cofiltered_limits_op_of_has_filtered_colimits`

English:
instance has_cofiltered_limits_op_of_has_filtered_colimits
  signature: [HasFilteredColimitsOfSize.{v₂, u₂} C]
  body: hasLimitsOfShape_op_of_hasColimitsOfShape

中文:
实例 has_cofiltered_limits_op_of_has_filtered_colimits
  签名: [有FilteredColimitsOfSize.{v₂, u₂} C]
  定义体: hasLimitsOfShape_op_of_hasColimitsOfShape

Depends on / 依赖: hasLimitsOfShape_op_of_hasColimitsOfShape
-/
instance has_cofiltered_limits_op_of_has_filtered_colimits [HasFilteredColimitsOfSize.{v₂, u₂} C] :
    HasCofilteredLimitsOfSize.{v₂, u₂} Cᵒᵖ where
  HasLimitsOfShape _ _ _ := hasLimitsOfShape_op_of_hasColimitsOfShape

/--
theorem `has_cofiltered_limits_of_has_filtered_colimits_op` / 定理 `has_cofiltered_limits_of_has_filtered_colimits_op`

English:
theorem has_cofiltered_limits_of_has_filtered_colimits_op
  given: [HasFilteredColimitsOfSize.{v₂, u₂} Cᵒᵖ]
  proof: { HasLimitsOfShape := fun _ _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }

中文:
定理 has_cofiltered_limits_of_has_filtered_colimits_op
  条件: [有FilteredColimitsOfSize.{v₂, u₂} Cᵒᵖ]
  证明: { HasLimitsOfShape := fun _ _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }

Depends on / 依赖: HasLimitsOfShape, hasLimitsOfShape_of_hasColimitsOfShape_op
-/
theorem has_cofiltered_limits_of_has_filtered_colimits_op [HasFilteredColimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasCofilteredLimitsOfSize.{v₂, u₂} C :=
  { HasLimitsOfShape := fun _ _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }

/--
Instance `has_filtered_colimits_op_of_has_cofiltered_limits` / 实例 `has_filtered_colimits_op_of_has_cofiltered_limits`

English:
instance has_filtered_colimits_op_of_has_cofiltered_limits
  signature: [HasCofilteredLimitsOfSize.{v₂, u₂} C]
  body: inferInstance

中文:
实例 has_filtered_colimits_op_of_has_cofiltered_limits
  签名: [有余filteredLimitsOfSize.{v₂, u₂} C]
  定义体: inferInstance
-/
instance has_filtered_colimits_op_of_has_cofiltered_limits [HasCofilteredLimitsOfSize.{v₂, u₂} C] :
    HasFilteredColimitsOfSize.{v₂, u₂} Cᵒᵖ where HasColimitsOfShape _ _ _ := inferInstance

/--
theorem `has_filtered_colimits_of_has_cofiltered_limits_op` / 定理 `has_filtered_colimits_of_has_cofiltered_limits_op`

English:
theorem has_filtered_colimits_of_has_cofiltered_limits_op
  given: [HasCofilteredLimitsOfSize.{v₂, u₂} Cᵒᵖ]
  proof: { HasColimitsOfShape := fun _ _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op }

中文:
定理 has_filtered_colimits_of_has_cofiltered_limits_op
  条件: [有余filteredLimitsOfSize.{v₂, u₂} Cᵒᵖ]
  证明: { HasColimitsOfShape := fun _ _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op }

Depends on / 依赖: HasColimitsOfShape, hasColimitsOfShape_of_hasLimitsOfShape_op
-/
theorem has_filtered_colimits_of_has_cofiltered_limits_op [HasCofilteredLimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasFilteredColimitsOfSize.{v₂, u₂} C :=
  { HasColimitsOfShape := fun _ _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op }

end CategoryTheory.Limits
