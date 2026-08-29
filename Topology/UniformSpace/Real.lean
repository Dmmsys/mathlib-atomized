/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# The reals are complete

This file provides the instances `CompleteSpace ℝ` and `CompleteSpace ℝ≥0`.
Along the way, we add a shortcut instance for the natural topology on `ℝ≥0`
(the one induced from `ℝ`), and add some basic API.
-/

@[expose] public section

assert_not_exists IsTopologicalRing UniformContinuousConstSMul UniformOnFun

noncomputable section

open Filter Metric Set

/--
Instance `Real.instCompleteSpace` / 实例 `Real.instCompleteSpace`

English:
instance Real.instCompleteSpace
  signature: : CompleteSpace Real
  body: by
  apply complete_of_cauchySeq_tendsto
  intro u hu
  let c : CauSeq Real abs := ⟨u, Metric.cauchySeq_iff'.1 hu⟩
  refine ⟨c.lim, fun s h => ?_⟩
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  have := c.equiv_lim ε ε0
  simp only [mem_map, mem_atTop_sets]
  exact this.imp fun N hN n hn => hε (

中文:
实例 实数.instCompleteSpace
  签名: : 完备空间 实数
  定义体: by
  apply complete_of_cauchySeq_tendsto
  intro u hu
  let c : CauSeq Real abs := ⟨u, Metric.cauchySeq_iff'.1 hu⟩
  refine ⟨c.lim, fun s h => ?_⟩
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  have := c.equiv_lim ε ε0
  simp only [mem_map, mem_atTop_sets]
  exact this.imp fun N hN n hn => hε (

Depends on / 依赖: CauSeq, Metric, Metric.cauchySeq_iff, Metric.mem_nhds_iff, c.equiv_lim, c.lim, cauchySeq_iff, complete_of_cauchySeq_tendsto, equiv_lim, mem_atTop_sets, mem_map, mem_nhds_iff, this.imp
-/
instance Real.instCompleteSpace : CompleteSpace Real := by
  apply complete_of_cauchySeq_tendsto
  intro u hu
  let c : CauSeq Real abs := ⟨u, Metric.cauchySeq_iff'.1 hu⟩
  refine ⟨c.lim, fun s h => ?_⟩
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  have := c.equiv_lim ε ε0
  simp only [mem_map, mem_atTop_sets]
  exact this.imp fun N hN n hn => hε (hN n hn)

namespace NNReal


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace Real>=0
  body: inferInstance

中文:
实例 :
  签名: 拓扑空间 实数>=0
  定义体: inferInstance
-/
instance : TopologicalSpace Real>=0 := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSpace Real>=0
  body: isClosed_Ici.completeSpace_coe

@[fun_prop]

中文:
实例 :
  签名: 完备空间 实数>=0
  定义体: isClosed_Ici.completeSpace_coe

@[fun_prop]

Depends on / 依赖: completeSpace_coe, isClosed_Ici, isClosed_Ici.completeSpace_coe
-/
instance : CompleteSpace Real>=0 :=
  isClosed_Ici.completeSpace_coe

@[fun_prop]
/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous ((↑) : Real>=0 -> Real)
  proof: continuous_subtype_val

中文:
定理 continuous_coe
  结论: 连续 ((↑) : 实数>=0 -> 实数)
  证明: continuous_subtype_val

Depends on / 依赖: continuous_subtype_val
-/
theorem continuous_coe : Continuous ((↑) : Real>=0 -> Real) :=
  continuous_subtype_val

/-- Embedding of `ℝ≥0` to `ℝ` as a bundled continuous map. -/
@[simps -fullyApplied]
/--
Definition of `_root_.ContinuousMap.coeNNRealReal` / `_root_.ContinuousMap.coeNNRealReal` 的定义

English:
definition _root_.ContinuousMap.coeNNRealReal
  signature: : C(Real>=0, Real)
  body: ⟨(↑), continuous_coe⟩

@[simp]

中文:
定义 _root_.连续映射.coeNN实数实数
  签名: : C(实数>=0, 实数)
  定义体: ⟨(↑), continuous_coe⟩

@[simp]

Depends on / 依赖: continuous_coe
-/
def _root_.ContinuousMap.coeNNRealReal : C(Real>=0, Real) :=
  ⟨(↑), continuous_coe⟩

@[simp]
/--
lemma `coeNNRealReal_zero` / 引理 `coeNNRealReal_zero`

English:
lemma coeNNRealReal_zero
  statement: ContinuousMap.coeNNRealReal 0 = 0
  proof: rfl

中文:
引理 coeNN实数实数_zero
  结论: 连续映射.coeNN实数实数 0 = 0
  证明: rfl
-/
lemma coeNNRealReal_zero : ContinuousMap.coeNNRealReal 0 = 0 := rfl

/--
Instance `ContinuousMap.canLift` / 实例 `ContinuousMap.canLift`

English:
instance ContinuousMap.canLift
  signature: {X : Type*} [TopologicalSpace X]
  body: ⟨⟨fun x => .mk (f x) (hf x), f.2.subtype_mk _⟩, DFunLike.ext' rfl⟩

中文:
实例 连续映射.canLift
  签名: {X : 类型} [拓扑空间 X]
  定义体: ⟨⟨fun x => .mk (f x) (hf x), f.2.subtype_mk _⟩, DFunLike.ext' rfl⟩
-/
instance ContinuousMap.canLift {X : Type*} [TopologicalSpace X] :
    CanLift C(X, Real) C(X, Real>=0) ContinuousMap.coeNNRealReal.comp fun f => forall x, 0 <= f x where
  prf f hf := ⟨⟨fun x => .mk (f x) (hf x), f.2.subtype_mk _⟩, DFunLike.ext' rfl⟩

end NNReal
