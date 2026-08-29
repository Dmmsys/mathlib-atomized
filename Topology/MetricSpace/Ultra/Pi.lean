/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Ultrametric distances on pi types

This file contains results on the behavior of ultrametrics in products of ultrametric spaces.

## Main results

* `Pi.instIsUltrametricDist`: a product of ultrametric spaces is ultrametric.


ultrametric, nonarchimedean
-/

public section

/--
Instance `Pi.instIsUltrametricDist` / 实例 `Pi.instIsUltrametricDist`

English:
instance Pi.instIsUltrametricDist
  signature: {ι : Type*} {X : ι -> Type*} [Fintype ι]
  body: by
  constructor
  intro f g h
  simp only [dist_pi_def, ← NNReal.coe_max, NNReal.coe_le_coe, ← Finset.sup_sup]
  exact Finset.sup_mono_fun fun i _ => IsUltrametricDist.dist_triangle_max (f i) (g i) (h i)

中文:
实例 依赖函数类型.instIsUltrametricDist
  签名: {ι : 类型} {X : ι -> 类型} [有限类型 ι]
  定义体: by
  constructor
  intro f g h
  simp only [dist_pi_def, ← NNReal.coe_max, NNReal.coe_le_coe, ← Finset.sup_sup]
  exact Finset.sup_mono_fun fun i _ => IsUltrametricDist.dist_triangle_max (f i) (g i) (h i)

Depends on / 依赖: Finset, Finset.sup_mono_fun, Finset.sup_sup, IsUltrametricDist, IsUltrametricDist.dist_triangle_max, NNReal, NNReal.coe_le_coe, NNReal.coe_max, coe_le_coe, coe_max, dist_pi_def, dist_triangle_max, sup_mono_fun, sup_sup
-/
instance Pi.instIsUltrametricDist {ι : Type*} {X : ι -> Type*} [Fintype ι]
    [(i : ι) -> PseudoMetricSpace (X i)] [(i : ι) -> IsUltrametricDist (X i)] :
    IsUltrametricDist ((i : ι) -> X i) := by
  constructor
  intro f g h
  simp only [dist_pi_def, ← NNReal.coe_max, NNReal.coe_le_coe, ← Finset.sup_sup]
  exact Finset.sup_mono_fun fun i _ => IsUltrametricDist.dist_triangle_max (f i) (g i) (h i)
