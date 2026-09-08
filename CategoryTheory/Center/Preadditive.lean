/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Center.Basic

/-!
# The center of an additive category

-/

public section

universe v u

namespace CategoryTheory

namespace CatCenter

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[simp]
/-
**CategoryTheory.CatCenter.app_add** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cat
Center`。
形式化陈述：app_add (z₁ z₂ : CatCenter C) (X : C) : (z₁ + z₂).app X = z₁.app X + z₂.ap
p X
参数：z₁ z₂ : CatCenter C；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma app_add (z₁ z₂ : CatCenter C) (X : C) :
    (z₁ + z₂).app X = z₁.app X + z₂.app X := rfl

@[simp]
/-
**CategoryTheory.CatCenter.app_sub** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cat
Center`。
形式化陈述：app_sub (z₁ z₂ : CatCenter C) (X : C) : (z₁ - z₂).app X = z₁.app X - z₂.ap
p X
参数：z₁ z₂ : CatCenter C；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma app_sub (z₁ z₂ : CatCenter C) (X : C) :
    (z₁ - z₂).app X = z₁.app X - z₂.app X := rfl

@[simp]
/-
**CategoryTheory.CatCenter.app_neg** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cat
Center`。
形式化陈述：app_neg (z : CatCenter C) (X : C) : (-z).app X = - z.app X
参数：z : CatCenter C；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma app_neg (z : CatCenter C) (X : C) :
    (-z).app X = - z.app X := rfl

end CatCenter

end CategoryTheory

