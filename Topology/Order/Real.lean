/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.Order.T5

/-!
# The reals are equipped with their order topology

This file contains results related to the order topology on (extended) (non-negative) real numbers.
We
- prove that `ℝ` and `ℝ≥0` are equipped with the order topology and bornology,
- endow `EReal` with the order topology (and prove some very basic lemmas),
- define the topology `ℝ≥0∞` (which is the order topology, *not* the `EMetricSpace` topology)
-/

public section

assert_not_exists IsTopologicalRing UniformSpace

open Set

namespace EReal


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace EReal
  body: Preorder.topology EReal

中文:
实例 :
  签名: TopologicalSpace E实数
  定义体: Preorder.topology EReal

Depends on / 依赖: Preorder, Preorder.topology, topology
-/
noncomputable instance : TopologicalSpace EReal := Preorder.topology EReal
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTopology EReal
  body: ⟨rfl⟩

中文:
实例 :
  签名: OrderTopology E实数
  定义体: ⟨rfl⟩
-/
instance : OrderTopology EReal := ⟨rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T5Space EReal
  body: inferInstance

中文:
实例 :
  签名: T5Space E实数
  定义体: inferInstance
-/
instance : T5Space EReal := inferInstance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T2Space EReal
  body: inferInstance

中文:
实例 :
  签名: T2Space E实数
  定义体: inferInstance
-/
instance : T2Space EReal := inferInstance

/--
lemma `denseRange_ratCast` / 引理 `denseRange_ratCast`

English:
lemma denseRange_ratCast
  statement: DenseRange (fun r : Rat => ((r : Real) : EReal))
  proof: dense_of_exists_between fun _ _ h => exists_range_iff.2 exists_rat_btwn_of_lt h

中文:
引理 denseRange_ratCast
  结论: DenseRange (fun r : Rat => ((r : 实数) : E实数))
  证明: dense_of_exists_between fun _ _ h => exists_range_iff.2 exists_rat_btwn_of_lt h

Depends on / 依赖: dense_of_exists_between, exists_range_iff, exists_rat_btwn_of_lt
-/
lemma denseRange_ratCast : DenseRange (fun r : Rat => ((r : Real) : EReal)) :=
dense_of_exists_between fun _ _ h => exists_range_iff.2 exists_rat_btwn_of_lt h

end EReal

namespace ENNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace Real>=0∞
  body: Preorder.topology Real>=0∞

中文:
实例 :
  签名: TopologicalSpace 实数>=0∞
  定义体: Preorder.topology Real>=0∞

Depends on / 依赖: Preorder, Preorder.topology, topology
-/
instance : TopologicalSpace Real>=0∞ := Preorder.topology Real>=0∞

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTopology Real>=0∞
  body: ⟨rfl⟩

中文:
实例 :
  签名: OrderTopology 实数>=0∞
  定义体: ⟨rfl⟩
-/
instance : OrderTopology Real>=0∞ := ⟨rfl⟩

-- short-circuit type class inference
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T2Space Real>=0∞
  body: inferInstance

中文:
实例 :
  签名: T2Space 实数>=0∞
  定义体: inferInstance
-/
instance : T2Space Real>=0∞ := inferInstance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T5Space Real>=0∞
  body: inferInstance

中文:
实例 :
  签名: T5Space 实数>=0∞
  定义体: inferInstance
-/
instance : T5Space Real>=0∞ := inferInstance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T4Space Real>=0∞
  body: inferInstance

中文:
实例 :
  签名: T4Space 实数>=0∞
  定义体: inferInstance
-/
instance : T4Space Real>=0∞ := inferInstance

end ENNReal
