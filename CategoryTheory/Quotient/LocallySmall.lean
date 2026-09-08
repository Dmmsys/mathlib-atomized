/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Quotient

/-!
# Quotient categories are locally small

-/

public section

universe w v u

namespace CategoryTheory.Quotient

/-
**CategoryTheory.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type u} [Category.{v} C] (r : HomRel C) [LocallySmall.{w} C] :
    LocallySmall.{w} (Quotient r) where
  hom_small _ _ := small_of_surjective (functor r).map_surjective

end CategoryTheory.Quotient

