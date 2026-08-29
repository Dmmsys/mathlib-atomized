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
Definition of `Conv` / `Conv` 的定义

English:
definition Conv
  signature: (M N : C)
  body: M ⟶ N

中文:
定义 Conv
  签名: (M N : C)
  定义体: M ⟶ N
-/
def Conv (M N : C) : Type v₁ := M ⟶ N

namespace Conv

variable {M : C} {N : C} [ComonObj M] [MonObj N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (Conv M N)
  body: ε[M] ≫ η[N]

中文:
实例 :
  签名: 幺 (Conv M N)
  定义体: ε[M] ≫ η[N]
-/
instance : One (Conv M N) where
  one := ε[M] ≫ η[N]

/--
theorem `one_eq` / 定理 `one_eq`

English:
theorem one_eq
  statement: (1 : Conv M N) = ε[M] ≫ η[N]
  proof: rfl

中文:
定理 one_eq
  结论: (1 : Conv M N) = ε[M] ≫ η[N]
  证明: rfl
-/
theorem one_eq : (1 : Conv M N) = ε[M] ≫ η[N] := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (Conv M N)
  body: fun f g => Δ[M] ≫ f ▷ M ≫ N ◁ g ≫ μ[N]

中文:
实例 :
  签名: 乘法 (Conv M N)
  定义体: fun f g => Δ[M] ≫ f ▷ M ≫ N ◁ g ≫ μ[N]
-/
instance : Mul (Conv M N) where
  mul := fun f g => Δ[M] ≫ f ▷ M ≫ N ◁ g ≫ μ[N]

/--
theorem `mul_eq` / 定理 `mul_eq`

English:
theorem mul_eq
  given: (f g : Conv M N)
  statement: f * g = Δ[M] ≫ f ▷ M ≫ N ◁ g ≫ μ[N]
  proof: rfl

中文:
定理 mul_eq
  条件: (f g : Conv M N)
  结论: f * g = Δ[M] ≫ f ▷ M ≫ N ◁ g ≫ μ[N]
  证明: rfl
-/
theorem mul_eq (f g : Conv M N) : f * g = Δ[M] ≫ f ▷ M ≫ N ◁ g ≫ μ[N] := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (Conv M N)
  body: by simp [one_eq, mul_eq, ← whisker_exchange_assoc]
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

中文:
实例 :
  签名: 幺半群 (Conv M N)
  定义体: by simp [one_eq, mul_eq, ← whisker_exchange_assoc]
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

Depends on / 依赖: Category, Category.assoc, MonoidalCategory, MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, mul_assoc, mul_eq, mul_one, one_eq, slice_lhs, slice_rhs, whiskerLeft_comp, whisker_assoc, whisker_exchange, whisker_exchange_assoc
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
