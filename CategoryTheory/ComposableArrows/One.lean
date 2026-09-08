/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Functors to `ComposableArrows C 1`

-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ComposableArrows

variable (C : Type u) [Category.{v} C]

/-- The functor `ComposableArrows C n ⥤ ComposableArrows C 1`
which sends `S` to `mk₁ (S.map' i j)` when `i`, `j` and `n`
are such that `i ≤ j` and `j ≤ n`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.functorArrows** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.ComposableArrows`。
形式化陈述：functorArrows (i j n : Nat) (hij : i <= j
参数：i j n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ComposableArrows C n ⥤ ComposableArrows C 1`
which sends `S` to `mk₁ (S.map' i j)` when `i`, `j` and `n`
are such that `i ≤ j` and `j ≤ n`.
-/
def functorArrows (i j n : ℕ) (hij : i ≤ j := by lia) (hj : j ≤ n := by lia) :
    ComposableArrows C n ⥤ ComposableArrows C 1 where
  obj S := mk₁ (S.map' i j)
  map {S S'} φ := homMk₁ (φ.app _) (φ.app _) (φ.naturality _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `functorArrows C i j n ⟶ functorArrows C i' j' n`
when `i ≤ i'` and `j ≤ j'`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.mapFunctorArrows** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ComposableArrows`。
形式化陈述：mapFunctorArrows (i j i' j' n : Nat) (_ : i <= j
参数：i j i' j' n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `functorArrows C i j n ⟶ functorArrows C i' j' n`
when `i ≤ i'` and `j ≤ j'`.
-/
def mapFunctorArrows (i j i' j' n : ℕ)
    (_ : i ≤ j := by lia) (_ : i' ≤ j' := by lia)
    (_ : i ≤ i' := by lia) (_ : j ≤ j' := by lia)
    (_ : j' ≤ n := by lia) :
    functorArrows C i j n ⟶ functorArrows C i' j' n where
  app S := homMk₁ (S.map' i i') (S.map' j j')
    (by simp [← Functor.map_comp])

end ComposableArrows

end CategoryTheory

