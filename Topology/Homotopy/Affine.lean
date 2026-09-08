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
  [Module ℝ E] [ContinuousSMul ℝ E]

namespace ContinuousMap.Homotopy

set_option backward.defeqAttrib.useBackward true in
/-- The homotopy between `f` and `g`
such that `affine f g (t, x) = AffineMap.lineMap (f x) (g x) t`. -/
@[simps +simpRhs]
/-
**ContinuousMap.Homotopy.affine** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotop
y`。
形式化陈述：affine (f g : C(X, E)) : f.Homotopy g where toFun x
参数：f g : C(X, E)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy between `f` and `g`
such that `affine f g (t, x) = AffineMap.lineMap (f x) (g x) t`.
-/
def affine (f g : C(X, E)) : f.Homotopy g where
  toFun x := Path.segment (f x.2) (g x.2) x.1
  continuous_toFun := by dsimp [AffineMap.lineMap_apply]; fun_prop
  map_zero_left := by simp
  map_one_left := by simp

@[simp]
/-
**ContinuousMap.Homotopy.evalAt_affine** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.
Homotopy`。
形式化陈述：evalAt_affine (f g : C(X, E)) (x : X) : (affine f g).evalAt x = .segment (
f x) (g x)
参数：f g : C(X, E)；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalAt_affine (f g : C(X, E)) (x : X) : (affine f g).evalAt x = .segment (f x) (g x) := rfl

end ContinuousMap.Homotopy

