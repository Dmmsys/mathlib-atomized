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

/--
Instance `ContinuousMap.isUltrametricDist` / 实例 `ContinuousMap.isUltrametricDist`

English:
instance ContinuousMap.isUltrametricDist
  signature: {X Y : Type*}
  body: by
  constructor
  intro f g h
  rw [ContinuousMap.dist_le (by positivity)]
  refine fun x => (dist_triangle_max (f x) (g x) (h x)).trans (max_le_max ?_ ?_) <;>
  exact ContinuousMap.dist_apply_le_dist x

中文:
实例 连续映射.isUltrametricDist
  签名: {X Y : 类型}
  定义体: by
  constructor
  intro f g h
  rw [ContinuousMap.dist_le (by positivity)]
  refine fun x => (dist_triangle_max (f x) (g x) (h x)).trans (max_le_max ?_ ?_) <;>
  exact ContinuousMap.dist_apply_le_dist x

Depends on / 依赖: ContinuousMap, ContinuousMap.dist_apply_le_dist, ContinuousMap.dist_le, dist_apply_le_dist, dist_le, dist_triangle_max, max_le_max
-/
instance ContinuousMap.isUltrametricDist {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [MetricSpace Y] [IsUltrametricDist Y] :
    IsUltrametricDist C(X, Y) := by
  constructor
  intro f g h
  rw [ContinuousMap.dist_le (by positivity)]
  refine fun x => (dist_triangle_max (f x) (g x) (h x)).trans (max_le_max ?_ ?_) <;>
  exact ContinuousMap.dist_apply_le_dist x
