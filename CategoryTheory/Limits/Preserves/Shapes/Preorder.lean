/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.HasIterationOfShape
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preservation of well order continuous functors

Given a well-ordered type `J` and a functor `G : C ⥤ D`,
we define a type class `PreservesWellOrderContinuousOfShape J G`
saying that `G` preserves colimits of shape `Set.Iio j`
for any limit element `j : J`. It follows that if
`F : J ⥤ C` is well order continuous, then so is `F ⋙ G`.

-/

public section

universe w w' v v' v'' u' u u''

namespace CategoryTheory

namespace Limits

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  (J : Type w) [LinearOrder J]

/-- A functor `G : C ⥤ D` satisfies `PreservesWellOrderContinuousOfShape J G`
if for any limit element `j` in the preordered type `J`, the functor `G`
preserves colimits of shape `Set.Iio j`. -/
/-
**CategoryTheory.Limits.PreservesWellOrderContinuousOfShape** 是 Mathlib 中的一个类，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：PreservesWellOrderContinuousOfShape (G : C ⥤ D) : Prop where preservesColi
mitsOfShape (j : J) (hj : Order.IsSuccLimit j) : PreservesColimitsOfShape (Set.I
io j) G
参数：G : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `G : C ⥤ D` satisfies `PreservesWellOrderContinuousOfShape J G`
if for any limit element `j` in the preordered type `J`, the functor `G`
preserves colimits of shape `Set.Iio j`.
-/
class PreservesWellOrderContinuousOfShape (G : C ⥤ D) : Prop where
  preservesColimitsOfShape (j : J) (hj : Order.IsSuccLimit j) :
    PreservesColimitsOfShape (Set.Iio j) G := by infer_instance

variable {J} in
/-
**CategoryTheory.Limits.preservesColimitsOfShape_of_preservesWellOrderContinuous
OfShape** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape (G : C ⥤ D
) [PreservesWellOrderContinuousOfShape J G] (j : J) (hj : Order.IsSuccLimit j) :
 PreservesColimitsOfShape (Set.Iio j) G
参数：G : C ⥤ D；j : J；hj : Order.IsSuccLimit j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesWellOrderContinuousOfShape.preservesColim
itsOfShape`：∀ {C : Type u} {D : Type u'} {inst : CategoryTheory.Category.{v, u} 
C} {inst_1 : CategoryTheory.Category.{v', u'} D}   {J : Type w} {inst_2 …
-/
lemma preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape (G : C ⥤ D)
    [PreservesWellOrderContinuousOfShape J G]
    (j : J) (hj : Order.IsSuccLimit j) :
    PreservesColimitsOfShape (Set.Iio j) G :=
  PreservesWellOrderContinuousOfShape.preservesColimitsOfShape j hj
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : J ⥤ C) (G : C ⥤ D) [F.IsWellOrderContinuous]
    [PreservesWellOrderContinuousOfShape J G] :
    (F ⋙ G).IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨by
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G j hj
    exact isColimitOfPreserves G (F.isColimitOfIsWellOrderContinuous j hj)⟩
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G₁ : C ⥤ D) (G₂ : D ⥤ E)
    [PreservesWellOrderContinuousOfShape J G₁]
    [PreservesWellOrderContinuousOfShape J G₂] :
    PreservesWellOrderContinuousOfShape J (G₁ ⋙ G₂) where
  preservesColimitsOfShape j hj := by
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G₁ j hj
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G₂ j hj
    infer_instance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasIterationOfShape J C] (K : Type*) [Category* K] (X : K) :
    PreservesWellOrderContinuousOfShape J ((evaluation K C).obj X) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasIterationOfShape J C] :
    PreservesWellOrderContinuousOfShape J (Arrow.leftFunc : _ ⥤ C) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasIterationOfShape J C] :
    PreservesWellOrderContinuousOfShape J (Arrow.rightFunc : _ ⥤ C) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

end Limits

end CategoryTheory

