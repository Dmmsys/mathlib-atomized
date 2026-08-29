/-
Copyright (c) 2025 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Skeletal

/-!
# (Co)limits of the skeleton of a category

The skeleton of a category inherits all (co)limits the category has.

## Implementation notes

Because the category instance of `ThinSkeleton C` comes from its `Preorder` instance, it is not the
case that `HasLimits C` iff `HasLimits (ThinSkeleton C)`, as the homs live in different universes.
If this is something we really want, we should consider changing the category instance of
`ThinSkeleton C`.
-/

public section

noncomputable section

open CategoryTheory ThinSkeleton

namespace CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ w w'

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]
  {D : Type u₃} [Category.{v₃} D]

/--
Instance `hasLimitsOfShape_skeleton` / 实例 `hasLimitsOfShape_skeleton`

English:
instance hasLimitsOfShape_skeleton
  signature: [HasLimitsOfShape J C]
  body: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromSkeleton C)

中文:
实例 hasLimitsOfShape_skeleton
  签名: [有形状极限 J C]
  定义体: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromSkeleton C)

Depends on / 依赖: fromSkeleton, hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
-/
instance hasLimitsOfShape_skeleton [HasLimitsOfShape J C] : HasLimitsOfShape J (Skeleton C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromSkeleton C)

/--
Instance `hasLimitsOfSize_skeleton` / 实例 `hasLimitsOfSize_skeleton`

English:
instance hasLimitsOfSize_skeleton
  signature: [HasLimitsOfSize.{w, w'} C]
  body: hasLimits_of_hasLimits_createsLimits (fromSkeleton C)

example [HasLimits C] : HasLimits (Skeleton C) := by infer_instance

中文:
实例 hasLimitsOfSize_skeleton
  签名: [有LimitsOfSize.{w, w'} C]
  定义体: hasLimits_of_hasLimits_createsLimits (fromSkeleton C)

example [HasLimits C] : HasLimits (Skeleton C) := by infer_instance

Depends on / 依赖: fromSkeleton, hasLimits_of_hasLimits_createsLimits
-/
instance hasLimitsOfSize_skeleton [HasLimitsOfSize.{w, w'} C] :
    HasLimitsOfSize.{w, w'} (Skeleton C) :=
  hasLimits_of_hasLimits_createsLimits (fromSkeleton C)

example [HasLimits C] : HasLimits (Skeleton C) := by infer_instance

/--
Instance `hasColimitsOfShape_skeleton` / 实例 `hasColimitsOfShape_skeleton`

English:
instance hasColimitsOfShape_skeleton
  signature: [HasColimitsOfShape J C]
  body: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromSkeleton C)

中文:
实例 hasColimitsOfShape_skeleton
  签名: [有形状余极限 J C]
  定义体: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromSkeleton C)

Depends on / 依赖: fromSkeleton, hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
-/
instance hasColimitsOfShape_skeleton [HasColimitsOfShape J C] : HasColimitsOfShape J (Skeleton C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromSkeleton C)

/--
Instance `hasColimitsOfSize_skeleton` / 实例 `hasColimitsOfSize_skeleton`

English:
instance hasColimitsOfSize_skeleton
  signature: [HasColimitsOfSize.{w, w'} C]
  body: hasColimits_of_hasColimits_createsColimits (fromSkeleton C)

example [HasColimits C] : HasColimits (Skeleton C) := by infer_instance

中文:
实例 hasColimitsOfSize_skeleton
  签名: [有余limitsOfSize.{w, w'} C]
  定义体: hasColimits_of_hasColimits_createsColimits (fromSkeleton C)

example [HasColimits C] : HasColimits (Skeleton C) := by infer_instance

Depends on / 依赖: fromSkeleton, hasColimits_of_hasColimits_createsColimits
-/
instance hasColimitsOfSize_skeleton [HasColimitsOfSize.{w, w'} C] :
    HasColimitsOfSize.{w, w'} (Skeleton C) :=
  hasColimits_of_hasColimits_createsColimits (fromSkeleton C)

example [HasColimits C] : HasColimits (Skeleton C) := by infer_instance

variable [Quiver.IsThin C]

/--
Instance `hasLimitsOfShape_thinSkeleton` / 实例 `hasLimitsOfShape_thinSkeleton`

English:
instance hasLimitsOfShape_thinSkeleton
  signature: [HasLimitsOfShape J C]
  body: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromThinSkeleton C)

中文:
实例 hasLimitsOfShape_thinSkeleton
  签名: [有形状极限 J C]
  定义体: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromThinSkeleton C)

Depends on / 依赖: fromThinSkeleton, hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
-/
instance hasLimitsOfShape_thinSkeleton [HasLimitsOfShape J C] :
    HasLimitsOfShape J (ThinSkeleton C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromThinSkeleton C)

/--
Instance `hasLimitsOfSize_thinSkeleton` / 实例 `hasLimitsOfSize_thinSkeleton`

English:
instance hasLimitsOfSize_thinSkeleton
  signature: [HasLimitsOfSize.{w, w'} C]
  body: hasLimits_of_hasLimits_createsLimits (fromThinSkeleton C)

中文:
实例 hasLimitsOfSize_thinSkeleton
  签名: [有LimitsOfSize.{w, w'} C]
  定义体: hasLimits_of_hasLimits_createsLimits (fromThinSkeleton C)

Depends on / 依赖: fromThinSkeleton, hasLimits_of_hasLimits_createsLimits
-/
instance hasLimitsOfSize_thinSkeleton [HasLimitsOfSize.{w, w'} C] :
    HasLimitsOfSize.{w, w'} (ThinSkeleton C) :=
  hasLimits_of_hasLimits_createsLimits (fromThinSkeleton C)

/--
Instance `hasColimitsOfShape_thinSkeleton` / 实例 `hasColimitsOfShape_thinSkeleton`

English:
instance hasColimitsOfShape_thinSkeleton
  signature: [HasColimitsOfShape J C]
  body: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromThinSkeleton C)

中文:
实例 hasColimitsOfShape_thinSkeleton
  签名: [有形状余极限 J C]
  定义体: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromThinSkeleton C)

Depends on / 依赖: fromThinSkeleton, hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
-/
instance hasColimitsOfShape_thinSkeleton [HasColimitsOfShape J C] :
    HasColimitsOfShape J (ThinSkeleton C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromThinSkeleton C)

/--
Instance `hasColimitsOfSize_thinSkeleton` / 实例 `hasColimitsOfSize_thinSkeleton`

English:
instance hasColimitsOfSize_thinSkeleton
  signature: [HasColimitsOfSize.{w, w'} C]
  body: hasColimits_of_hasColimits_createsColimits (fromThinSkeleton C)

中文:
实例 hasColimitsOfSize_thinSkeleton
  签名: [有余limitsOfSize.{w, w'} C]
  定义体: hasColimits_of_hasColimits_createsColimits (fromThinSkeleton C)

Depends on / 依赖: fromThinSkeleton, hasColimits_of_hasColimits_createsColimits
-/
instance hasColimitsOfSize_thinSkeleton [HasColimitsOfSize.{w, w'} C] :
    HasColimitsOfSize.{w, w'} (ThinSkeleton C) :=
  hasColimits_of_hasColimits_createsColimits (fromThinSkeleton C)

end CategoryTheory.Limits
