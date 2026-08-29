/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Affine homotopy between two continuous maps

In this file we define `ContinuousMap.Homotopy.affine f g`
to be the homotopy between `f` and `g`
such that `affine f g (t, x) = AffineMap.lineMap (f x) (g x) t`.
-/

@[expose] public section

variable {X E : Type*} [TopologicalSpace X]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module Real E] [ContinuousSMul Real E]

namespace ContinuousMap.Homotopy

set_option backward.defeqAttrib.useBackward true in
/-- The homotopy between `f` and `g`
such that `affine f g (t, x) = AffineMap.lineMap (f x) (g x) t`. -/
@[simps +simpRhs]
/--
Definition of `affine` / `affine` 的定义

English:
definition affine
  signature: (f g : C(X, E))
  body: Path.segment (f x.2) (g x.2) x.1
  continuous_toFun := by dsimp [AffineMap.lineMap_apply]; fun_prop
  map_zero_left := by simp
  map_one_left := by simp

@[simp]

中文:
定义 affine
  签名: (f g : C(X, E))
  定义体: Path.segment (f x.2) (g x.2) x.1
  continuous_toFun := by dsimp [AffineMap.lineMap_apply]; fun_prop
  map_zero_left := by simp
  map_one_left := by simp

@[simp]

Depends on / 依赖: Path.segment, segment
-/
def affine (f g : C(X, E)) : f.Homotopy g where
  toFun x := Path.segment (f x.2) (g x.2) x.1
  continuous_toFun := by dsimp [AffineMap.lineMap_apply]; fun_prop
  map_zero_left := by simp
  map_one_left := by simp

@[simp]
/--
theorem `evalAt_affine` / 定理 `evalAt_affine`

English:
theorem evalAt_affine
  given: (f g : C(X, E)) (x : X)
  statement: (affine f g).evalAt x = .segment (f x) (g x)
  proof: rfl

中文:
定理 evalAt_affine
  条件: (f g : C(X, E)) (x : X)
  结论: (affine f g).evalAt x = .segment (f x) (g x)
  证明: rfl
-/
theorem evalAt_affine (f g : C(X, E)) (x : X) : (affine f g).evalAt x = .segment (f x) (g x) := rfl

end ContinuousMap.Homotopy
