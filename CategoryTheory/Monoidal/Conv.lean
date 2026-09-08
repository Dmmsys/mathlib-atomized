/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# The convolution monoid.

When `M : Comon C` and `N : Mon C`, the morphisms `M.X ⟶ N.X` form a monoid (in Type).
-/

@[expose] public section

universe v₁ u₁
namespace CategoryTheory
open MonoidalCategory
open MonObj ComonObj
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/--
The morphisms in `C` between the underlying objects of a pair of bimonoids in `C` naturally have a
(set-theoretic) monoid structure. -/
/-
**CategoryTheory.Conv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Conv (M N : C) : Type v₁
参数：M N : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphisms in `C` between the underlying objects of a pair of bimonoids in `C
` naturally have a
(set-theoretic) monoid structure.
-/
def Conv (M N : C) : Type v₁ := M ⟶ N

namespace Conv

variable {M : C} {N : C} [ComonObj M] [MonObj N]

/-
**CategoryTheory.Conv.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Conv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (Conv M N) where
  one := ε[M] ≫ η[N]
/-
**CategoryTheory.Conv.one_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Conv`。
形式化陈述：one_eq : (1 : Conv M N) = ε[M] ≫ η[N]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_eq : (1 : Conv M N) = ε[M] ≫ η[N] := rfl
/-
**CategoryTheory.Conv.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Conv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (Conv M N) where
  mul := fun f g => Δ[M] ≫ f ▷ M ≫ N ◁ g ≫ μ[N]
/-
**CategoryTheory.Conv.mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Conv`。
形式化陈述：mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷ M ≫ N ◁ g ≫ μ[N]
参数：f g : Conv M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷ M ≫ N ◁ g ≫ μ[N] := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Conv.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Conv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (Conv M N) where
  one_mul f := by simp [one_eq, mul_eq, ← whisker_exchange_assoc]
  mul_one f := by simp [one_eq, mul_eq, ← whisker_exchange_assoc]
  mul_assoc f g h := by
    simp only [mul_eq]
    simp only [comp_whiskerRight, whisker_assoc, Category.assoc,
      MonoidalCategory.whiskerLeft_comp]
    slice_lhs 7 8 =>
      rw [← whisker_exchange]
    slice_rhs 2 3 =>
      rw [← whisker_exchange]
    simp

end Conv

end CategoryTheory

