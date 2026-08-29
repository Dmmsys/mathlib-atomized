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
/--
Definition of `functorArrows` / `functorArrows` 的定义

English:
definition functorArrows
  signature: (i j n : Nat) (hij : i <= j := by lia) (hj : j <= n := by lia)
  body: mk₁ (S.map' i j)
  map {S S'} φ := homMk₁ (φ.app _) (φ.app _) (φ.naturality _)

中文:
定义 functorArrows
  签名: (i j n : 自然数) (hij : i <= j := by lia) (hj : j <= n := by lia)
  定义体: mk₁ (S.map' i j)
  map {S S'} φ := homMk₁ (φ.app _) (φ.app _) (φ.naturality _)

Depends on / 依赖: ComposableArrows, S.map, naturality
-/
def functorArrows (i j n : Nat) (hij : i <= j := by lia) (hj : j <= n := by lia) :
    ComposableArrows C n ⥤ ComposableArrows C 1 where
  obj S := mk₁ (S.map' i j)
  map {S S'} φ := homMk₁ (φ.app _) (φ.app _) (φ.naturality _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `functorArrows C i j n ⟶ functorArrows C i' j' n`
when `i ≤ i'` and `j ≤ j'`. -/
@[simps]
/--
Definition of `mapFunctorArrows` / `mapFunctorArrows` 的定义

English:
definition mapFunctorArrows
  signature: (i j i' j' n : Nat)
  body: homMk₁ (S.map' i i') (S.map' j j')
    (by simp [← Functor.map_comp])

中文:
定义 mapFunctorArrows
  签名: (i j i' j' n : 自然数)
  定义体: homMk₁ (S.map' i i') (S.map' j j')
    (by simp [← Functor.map_comp])

Depends on / 依赖: Functor, Functor.map_comp, PreservesColimits, PreservesColimits.preservesFilteredColimits, S.map, functorArrows, map_comp, preservesFilteredColimits
-/
def mapFunctorArrows (i j i' j' n : Nat)
    (_ : i <= j := by lia) (_ : i' <= j' := by lia)
    (_ : i <= i' := by lia) (_ : j <= j' := by lia)
    (_ : j' <= n := by lia) :
    functorArrows C i j n ⟶ functorArrows C i' j' n where
  app S := homMk₁ (S.map' i i') (S.map' j j')
    (by simp [← Functor.map_comp])

end ComposableArrows

end CategoryTheory
