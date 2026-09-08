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

/-
**CategoryTheory.Limits.has_cofiltered_limits_op_of_has_filtered_colimits** 是 Ma
thlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：has_cofiltered_limits_op_of_has_filtered_colimits [HasFilteredColimitsOfSi
ze.{v₂, u₂} C] : HasCofilteredLimitsOfSize.{v₂, u₂} Cᵒᵖ where HasLimitsOfShape _
 _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_op_of_hasColimitsOfShape`：hasLimi
tsOfShape_op_of_hasColimitsOfShape [HasColimitsOfShape Jᵒᵖ C] : HasLimitsOfShape
 J Cᵒᵖ
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
-/
instance has_cofiltered_limits_op_of_has_filtered_colimits [HasFilteredColimitsOfSize.{v₂, u₂} C] :
    HasCofilteredLimitsOfSize.{v₂, u₂} Cᵒᵖ where
  HasLimitsOfShape _ _ _ := hasLimitsOfShape_op_of_hasColimitsOfShape
/-
**CategoryTheory.Limits.has_cofiltered_limits_of_has_filtered_colimits_op** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：has_cofiltered_limits_of_has_filtered_colimits_op [HasFilteredColimitsOfSi
ze.{v₂, u₂} Cᵒᵖ] : HasCofilteredLimitsOfSize.{v₂, u₂} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasColimitsOfShape_op`：hasLimi
tsOfShape_of_hasColimitsOfShape_op [HasColimitsOfShape Jᵒᵖ Cᵒᵖ] : HasLimitsOfSha
pe J C
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
-/
theorem has_cofiltered_limits_of_has_filtered_colimits_op [HasFilteredColimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasCofilteredLimitsOfSize.{v₂, u₂} C :=
  { HasLimitsOfShape := fun _ _ _ => hasLimitsOfShape_of_hasColimitsOfShape_op }
/-
**CategoryTheory.Limits.has_filtered_colimits_op_of_has_cofiltered_limits** 是 Ma
thlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：has_filtered_colimits_op_of_has_cofiltered_limits [HasCofilteredLimitsOfSi
ze.{v₂, u₂} C] : HasFilteredColimitsOfSize.{v₂, u₂} Cᵒᵖ where HasColimitsOfShape
 _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_has_cofiltered_limits`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.HasCo
filteredLimitsOfSize.{w', w, v, u} C] (I : Type w)   …
-/
instance has_filtered_colimits_op_of_has_cofiltered_limits [HasCofilteredLimitsOfSize.{v₂, u₂} C] :
    HasFilteredColimitsOfSize.{v₂, u₂} Cᵒᵖ where HasColimitsOfShape _ _ _ := inferInstance
/-
**CategoryTheory.Limits.has_filtered_colimits_of_has_cofiltered_limits_op** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：has_filtered_colimits_of_has_cofiltered_limits_op [HasCofilteredLimitsOfSi
ze.{v₂, u₂} Cᵒᵖ] : HasFilteredColimitsOfSize.{v₂, u₂} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasLimitsOfShape_op`：hasColi
mitsOfShape_of_hasLimitsOfShape_op [HasLimitsOfShape Jᵒᵖ Cᵒᵖ] : HasColimitsOfSha
pe J C
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_has_cofiltered_limits`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.HasCo
filteredLimitsOfSize.{w', w, v, u} C] (I : Type w)   …
-/
theorem has_filtered_colimits_of_has_cofiltered_limits_op [HasCofilteredLimitsOfSize.{v₂, u₂} Cᵒᵖ] :
    HasFilteredColimitsOfSize.{v₂, u₂} C :=
  { HasColimitsOfShape := fun _ _ _ => hasColimitsOfShape_of_hasLimitsOfShape_op }

end CategoryTheory.Limits

