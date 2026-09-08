/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric structure on continuous maps
-/

public section

/-- Continuous maps from a compact space to an ultrametric space are an ultrametric space. -/
/-
**ContinuousMap.isUltrametricDist** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousMap.isUltrametricDist {X Y : Type*} [TopologicalSpace X] [Compac
tSpace X] [MetricSpace Y] [IsUltrametricDist Y] : IsUltrametricDist C(X, Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist f g <= C ↔ 
forall x : α, dist (f x) (g x) <= C
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `dist_triangle_max`：dist_triangle_max : dist x z <= max (dist x y) (dist 
y z)
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d
· 使用定理 `ContinuousMap.dist_apply_le_dist`：dist_apply_le_dist (x : α) : dist (f x
) (g x) <= dist f g

--- 原说明 ---
Continuous maps from a compact space to an ultrametric space are an ultrametric 
space.
-/
instance ContinuousMap.isUltrametricDist {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [MetricSpace Y] [IsUltrametricDist Y] :
    IsUltrametricDist C(X, Y) := by
  constructor
  intro f g h
  rw [ContinuousMap.dist_le (by positivity)]
  refine fun x ↦ (dist_triangle_max (f x) (g x) (h x)).trans (max_le_max ?_ ?_) <;>
  exact ContinuousMap.dist_apply_le_dist x
