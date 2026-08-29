/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Rat.Encodable
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Real

/-!
# Second countability of the reals

We prove that `EReal`, `ℝ≥0` and `ℝ≥0∞` are second countable.
In the process, we also provide the instance `ProperSpace ℝ≥0`.
-/

public section

assert_not_exists IsTopologicalRing UniformContinuousConstSMul UniformOnFun

noncomputable section

open Set Topology TopologicalSpace

namespace EReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SecondCountableTopology EReal
  body: have : SeparableSpace EReal := ⟨⟨_, countable_range _, denseRange_ratCast⟩⟩
  .of_separableSpace_orderTopology _

中文:
实例 :
  签名: SecondCountableTopology E实数
  定义体: have : SeparableSpace EReal := ⟨⟨_, countable_range _, denseRange_ratCast⟩⟩
  .of_separableSpace_orderTopology _

Depends on / 依赖: SeparableSpace, countable_range, denseRange_ratCast, of_separableSpace_orderTopology
-/
instance : SecondCountableTopology EReal :=
  have : SeparableSpace EReal := ⟨⟨_, countable_range _, denseRange_ratCast⟩⟩
  .of_separableSpace_orderTopology _

end EReal

namespace NNReal


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SecondCountableTopology Real>=0
  body: inferInstanceAs (SecondCountableTopology { x : Real | 0 <= x })

中文:
实例 :
  签名: SecondCountableTopology 实数>=0
  定义体: inferInstanceAs (SecondCountableTopology { x : Real | 0 <= x })

Depends on / 依赖: SecondCountableTopology
-/
instance : SecondCountableTopology Real>=0 :=
  inferInstanceAs (SecondCountableTopology { x : Real | 0 <= x })

/--
Instance `instProperSpace` / 实例 `instProperSpace`

English:
instance instProperSpace
  signature: : ProperSpace Real>=0 where
  body: by
    have emb : IsClosedEmbedding ((↑) : Real>=0 -> Real) := Isometry.isClosedEmbedding fun _ => congrFun rfl
    exact emb.isCompact_preimage (K := Metric.closedBall x r) (isCompact_closedBall _ _)

中文:
实例 instProperSpace
  签名: : 命题erSpace 实数>=0 where
  定义体: by
    have emb : IsClosedEmbedding ((↑) : Real>=0 -> Real) := Isometry.isClosedEmbedding fun _ => congrFun rfl
    exact emb.isCompact_preimage (K := Metric.closedBall x r) (isCompact_closedBall _ _)

Depends on / 依赖: IsClosedEmbedding, Isometry, Isometry.isClosedEmbedding, Metric, Metric.closedBall, closedBall, emb.isCompact_preimage, isClosedEmbedding, isCompact_closedBall, isCompact_preimage
-/
instance instProperSpace : ProperSpace Real>=0 where
  isCompact_closedBall x r := by
    have emb : IsClosedEmbedding ((↑) : Real>=0 -> Real) := Isometry.isClosedEmbedding fun _ => congrFun rfl
    exact emb.isCompact_preimage (K := Metric.closedBall x r) (isCompact_closedBall _ _)

end NNReal

namespace ENNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SecondCountableTopology Real>=0∞
  body: orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.secondCountableTopology

中文:
实例 :
  签名: SecondCountableTopology 实数>=0∞
  定义体: orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.secondCountableTopology

Depends on / 依赖: isEmbedding, orderIsoUnitIntervalBirational, orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.secondCountableTopology, secondCountableTopology, toHomeomorph
-/
instance : SecondCountableTopology Real>=0∞ :=
  orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.secondCountableTopology

end ENNReal
