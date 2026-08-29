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

/--
Definition of `PreservesWellOrderContinuousOfShape` / `PreservesWellOrderContinuousOfShape` 的定义

English:
class PreservesWellOrderContinuousOfShape
  parameters: (G : C ⥤ D)
  axioms and operations (1):
    - preservesColimitsOfShape((j : J) (hj : Order.IsSuccLimit j)) : PreservesColimitsOfShape (Set.Iio j) G  [default: by infer_instance]

中文:
类 PreservesWellOrderContinuousOfShape
  参数: (G : C ⥤ D)
  公理与运算 (1 个):
    - preservesColimitsOfShape((j : J) (hj : Order.IsSuccLimit j)) : PreservesColimitsOfShape (Set.Iio j) G  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class PreservesWellOrderContinuousOfShape (G : C ⥤ D) : Prop where
  preservesColimitsOfShape (j : J) (hj : Order.IsSuccLimit j) :
    PreservesColimitsOfShape (Set.Iio j) G := by infer_instance

variable {J} in
/--
lemma `preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape` / 引理 `preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape`

English:
lemma preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape
  statement: (G : C ⥤ D)
  proof: PreservesWellOrderContinuousOfShape.preservesColimitsOfShape j hj

中文:
引理 preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape
  结论: (G : C ⥤ D)
  证明: PreservesWellOrderContinuousOfShape.preservesColimitsOfShape j hj

Depends on / 依赖: Iso.inv_comp_eq, PreservesWellOrderContinuousOfShape, PreservesWellOrderContinuousOfShape.preservesColimitsOfShape, hom_comul, inv_comp_eq, preservesColimitsOfShape
-/
lemma preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape (G : C ⥤ D)
    [PreservesWellOrderContinuousOfShape J G]
    (j : J) (hj : Order.IsSuccLimit j) :
    PreservesColimitsOfShape (Set.Iio j) G :=
  PreservesWellOrderContinuousOfShape.preservesColimitsOfShape j hj

instance (F : J ⥤ C) (G : C ⥤ D) [F.IsWellOrderContinuous]
    [PreservesWellOrderContinuousOfShape J G] :
    (F ⋙ G).IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨by
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G j hj
    exact isColimitOfPreserves G (F.isColimitOfIsWellOrderContinuous j hj)⟩

instance (G₁ : C ⥤ D) (G₂ : D ⥤ E)
    [PreservesWellOrderContinuousOfShape J G₁]
    [PreservesWellOrderContinuousOfShape J G₂] :
    PreservesWellOrderContinuousOfShape J (G₁ ⋙ G₂) where
  preservesColimitsOfShape j hj := by
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G₁ j hj
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G₂ j hj
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasIterationOfShape
  signature: J C] (K
  body: by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

中文:
实例 [HasIterationOfShape
  签名: J C] (K
  定义体: by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

Depends on / 依赖: hasColimitsOfShape_of_isSuccLimit, infer_instance
-/
instance [HasIterationOfShape J C] (K : Type*) [Category* K] (X : K) :
    PreservesWellOrderContinuousOfShape J ((evaluation K C).obj X) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasIterationOfShape
  signature: J C] :
  body: by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

中文:
实例 [HasIterationOfShape
  签名: J C] :
  定义体: by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

Depends on / 依赖: hasColimitsOfShape_of_isSuccLimit, infer_instance
-/
instance [HasIterationOfShape J C] :
    PreservesWellOrderContinuousOfShape J (Arrow.leftFunc : _ ⥤ C) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasIterationOfShape
  signature: J C] :
  body: by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

中文:
实例 [HasIterationOfShape
  签名: J C] :
  定义体: by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

Depends on / 依赖: hasColimitsOfShape_of_isSuccLimit, infer_instance
-/
instance [HasIterationOfShape J C] :
    PreservesWellOrderContinuousOfShape J (Arrow.rightFunc : _ ⥤ C) where
  preservesColimitsOfShape j hj := by
    have := hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

end Limits

end CategoryTheory
