/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.NNReal.Star
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Topological properties of conjugation on ℝ
-/

public section

assert_not_exists IsTopologicalRing UniformContinuousConstSMul UniformOnFun

noncomputable section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousStar Real
  body: ⟨continuous_id⟩

中文:
实例 :
  签名: ContinuousStar 实数
  定义体: ⟨continuous_id⟩

Depends on / 依赖: continuous_id
-/
instance : ContinuousStar Real := ⟨continuous_id⟩

namespace NNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousStar Real>=0
  body: continuous_id

中文:
实例 :
  签名: ContinuousStar 实数>=0
  定义体: continuous_id

Depends on / 依赖: continuous_id
-/
instance : ContinuousStar Real>=0 where
  continuous_star := continuous_id

end NNReal
