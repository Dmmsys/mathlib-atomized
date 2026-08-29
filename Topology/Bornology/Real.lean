/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Bornology

/-!
# The reals are equipped with their order bornology

This file contains results related to the order bornology on (non-negative) real numbers.
We prove that `ℝ` and `ℝ≥0` are equipped with the order topology and bornology.
-/

public section

assert_not_exists IsTopologicalRing UniformContinuousConstSMul UniformOnFun

open Metric Set

/--
Instance `Real.instIsOrderBornology` / 实例 `Real.instIsOrderBornology`

English:
instance Real.instIsOrderBornology
  signature: : IsOrderBornology Real
  body: .of_isCompactIcc 0 (by simp [closedBall_eq_Icc]) (by simp [closedBall_eq_Icc])

中文:
实例 Real.instIsOrderBornology
  签名: : IsOrderBornology 实数
  定义体: .of_isCompactIcc 0 (by simp [closedBall_eq_Icc]) (by simp [closedBall_eq_Icc])

Depends on / 依赖: closedBall_eq_Icc, of_isCompactIcc
-/
instance Real.instIsOrderBornology : IsOrderBornology Real :=
  .of_isCompactIcc 0 (by simp [closedBall_eq_Icc]) (by simp [closedBall_eq_Icc])

namespace NNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTopology Real>=0
  body: orderTopology_of_ordConnected (t := Ici 0)

中文:
实例 :
  签名: OrderTopology 实数>=0
  定义体: orderTopology_of_ordConnected (t := Ici 0)

Depends on / 依赖: orderTopology_of_ordConnected
-/
instance : OrderTopology Real>=0 :=
  orderTopology_of_ordConnected (t := Ici 0)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderBornology Real>=0
  body: .of_isCompactIcc 0 (by simp) fun r => by
  obtain hr | hr := le_or_gt 0 r <;> simp [closedBall_zero_eq_Icc, *]

中文:
实例 :
  签名: IsOrderBornology 实数>=0
  定义体: .of_isCompactIcc 0 (by simp) fun r => by
  obtain hr | hr := le_or_gt 0 r <;> simp [closedBall_zero_eq_Icc, *]

Depends on / 依赖: closedBall_zero_eq_Icc, le_or_gt, of_isCompactIcc
-/
instance : IsOrderBornology Real>=0 := .of_isCompactIcc 0 (by simp) fun r => by
  obtain hr | hr := le_or_gt 0 r <;> simp [closedBall_zero_eq_Icc, *]

end NNReal
