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

/-
**CategoryTheory.Limits.hasLimitsOfShape_skeleton** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_skeleton [HasLimitsOfShape J C] : HasLimitsOfShape J (Ske
leton C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
`：hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [HasLimi
tsOfShape J D] [CreatesLimitsOfShape J F] : HasLimitsOfShape J…
· 使用定理 `CategoryTheory.fromSkeleton.isEquivalence`：∀ (C : Type u₁) [inst : Categ
oryTheory.Category.{v₁, u₁} C], (CategoryTheory.fromSkeleton C).IsEquivalence
-/
instance hasLimitsOfShape_skeleton [HasLimitsOfShape J C] : HasLimitsOfShape J (Skeleton C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromSkeleton C)
/-
**CategoryTheory.Limits.hasLimitsOfSize_skeleton** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：hasLimitsOfSize_skeleton [HasLimitsOfSize.{w, w'} C] : HasLimitsOfSize.{w,
 w'} (Skeleton C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimits_of_hasLimits_createsLimits`：hasLimits_of_hasLim
its_createsLimits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D] [CreatesLimitsOfSize.{
w, w'} F] : HasLimitsOfSize.{w, w'} C
· 使用定理 `CategoryTheory.fromSkeleton.isEquivalence`：∀ (C : Type u₁) [inst : Categ
oryTheory.Category.{v₁, u₁} C], (CategoryTheory.fromSkeleton C).IsEquivalence
-/
instance hasLimitsOfSize_skeleton [HasLimitsOfSize.{w, w'} C] :
    HasLimitsOfSize.{w, w'} (Skeleton C) :=
  hasLimits_of_hasLimits_createsLimits (fromSkeleton C)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [HasLimits C] : HasLimits (Skeleton C) := by infer_instance
/-
**CategoryTheory.Limits.hasColimitsOfShape_skeleton** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_skeleton [HasColimitsOfShape J C] : HasColimitsOfShape 
J (Skeleton C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsO
fShape`：hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤
 D) [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColim…
· 使用定理 `CategoryTheory.fromSkeleton.isEquivalence`：∀ (C : Type u₁) [inst : Categ
oryTheory.Category.{v₁, u₁} C], (CategoryTheory.fromSkeleton C).IsEquivalence
-/
instance hasColimitsOfShape_skeleton [HasColimitsOfShape J C] : HasColimitsOfShape J (Skeleton C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromSkeleton C)
/-
**CategoryTheory.Limits.hasColimitsOfSize_skeleton** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：hasColimitsOfSize_skeleton [HasColimitsOfSize.{w, w'} C] : HasColimitsOfSi
ze.{w, w'} (Skeleton C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimits_of_hasColimits_createsColimits`：hasColimits_o
f_hasColimits_createsColimits (F : C ⥤ D) [HasColimitsOfSize.{w, w'} D] [Creates
ColimitsOfSize.{w, w'} F] : HasColimitsOfSize.{…
· 使用定理 `CategoryTheory.fromSkeleton.isEquivalence`：∀ (C : Type u₁) [inst : Categ
oryTheory.Category.{v₁, u₁} C], (CategoryTheory.fromSkeleton C).IsEquivalence
-/
instance hasColimitsOfSize_skeleton [HasColimitsOfSize.{w, w'} C] :
    HasColimitsOfSize.{w, w'} (Skeleton C) :=
  hasColimits_of_hasColimits_createsColimits (fromSkeleton C)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [HasColimits C] : HasColimits (Skeleton C) := by infer_instance

variable [Quiver.IsThin C]
/-
**CategoryTheory.Limits.hasLimitsOfShape_thinSkeleton** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasLimitsOfShape_thinSkeleton [HasLimitsOfShape J C] : HasLimitsOfShape J 
(ThinSkeleton C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
`：hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (F : C ⥤ D) [HasLimi
tsOfShape J D] [CreatesLimitsOfShape J F] : HasLimitsOfShape J…
-/
instance hasLimitsOfShape_thinSkeleton [HasLimitsOfShape J C] :
    HasLimitsOfShape J (ThinSkeleton C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromThinSkeleton C)
/-
**CategoryTheory.Limits.hasLimitsOfSize_thinSkeleton** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasLimitsOfSize_thinSkeleton [HasLimitsOfSize.{w, w'} C] : HasLimitsOfSize
.{w, w'} (ThinSkeleton C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimits_of_hasLimits_createsLimits`：hasLimits_of_hasLim
its_createsLimits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D] [CreatesLimitsOfSize.{
w, w'} F] : HasLimitsOfSize.{w, w'} C
-/
instance hasLimitsOfSize_thinSkeleton [HasLimitsOfSize.{w, w'} C] :
    HasLimitsOfSize.{w, w'} (ThinSkeleton C) :=
  hasLimits_of_hasLimits_createsLimits (fromThinSkeleton C)
/-
**CategoryTheory.Limits.hasColimitsOfShape_thinSkeleton** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfShape_thinSkeleton [HasColimitsOfShape J C] : HasColimitsOfSh
ape J (ThinSkeleton C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsO
fShape`：hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (F : C ⥤
 D) [HasColimitsOfShape J D] [CreatesColimitsOfShape J F] : HasColim…
-/
instance hasColimitsOfShape_thinSkeleton [HasColimitsOfShape J C] :
    HasColimitsOfShape J (ThinSkeleton C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromThinSkeleton C)
/-
**CategoryTheory.Limits.hasColimitsOfSize_thinSkeleton** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasColimitsOfSize_thinSkeleton [HasColimitsOfSize.{w, w'} C] : HasColimits
OfSize.{w, w'} (ThinSkeleton C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimits_of_hasColimits_createsColimits`：hasColimits_o
f_hasColimits_createsColimits (F : C ⥤ D) [HasColimitsOfSize.{w, w'} D] [Creates
ColimitsOfSize.{w, w'} F] : HasColimitsOfSize.{…
-/
instance hasColimitsOfSize_thinSkeleton [HasColimitsOfSize.{w, w'} C] :
    HasColimitsOfSize.{w, w'} (ThinSkeleton C) :=
  hasColimits_of_hasColimits_createsColimits (fromThinSkeleton C)

end CategoryTheory.Limits

