/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Order.Real

/-!
# `ENNReal` is metrizable

## Implementation details

This file currently only contains results on `ENNReal` but is named `Real.lean`
to make it clear we can accept more `(E)(NN)Real` results.
-/

public section

namespace ENNReal

open NNReal TopologicalSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetrizableSpace ENNReal
  body: orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.metrizableSpace

中文:
实例 :
  签名: Metrizable空间 广义非负实数
  定义体: orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.metrizableSpace

Depends on / 依赖: isEmbedding, metrizableSpace, orderIsoUnitIntervalBirational, orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.metrizableSpace, toHomeomorph
-/
instance : MetrizableSpace ENNReal :=
  orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.metrizableSpace

end ENNReal
