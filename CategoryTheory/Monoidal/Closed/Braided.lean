/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Closed braided monoidal categories

Interactions between monoidal closed and braided category structures.

-/

public section

namespace CategoryTheory

open Category MonoidalCategory Limits

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]

namespace ihom

/-
**CategoryTheory.ihom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ihom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : C) [Closed A] :
    (tensorRight A).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight A)
/-
**CategoryTheory.ihom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ihom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : C) [MonoidalClosed C] (J : Type*) [Category* J] :
    PreservesLimitsOfShape J (MonoidalClosed.internalHom.flip.obj A) :=
  MonoidalClosed.internalHomAdjunction₂.preservesLimitsOfShape_flip_obj _ _

end ihom

end CategoryTheory

