/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Bornology.Real
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Real

/-!
# Topological algebra properties of ℝ

This file defines topological field/(semi)ring structures on the
(extended) (nonnegative) reals and shows the algebraic operations are
(uniformly) continuous.

It also includes a bit of more general topological theory of the reals,
needed to define the structures and prove continuity.
-/

public section

assert_not_exists StarRing UniformContinuousConstSMul UniformOnFun

noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoncompactSpace Real
  body: Int.isClosedEmbedding_coe_real.noncompactSpace

中文:
实例 :
  签名: Noncompact空间 实数
  定义体: Int.isClosedEmbedding_coe_real.noncompactSpace

Depends on / 依赖: Int.isClosedEmbedding_coe_real.noncompactSpace, isClosedEmbedding_coe_real, noncompactSpace
-/
instance : NoncompactSpace Real := Int.isClosedEmbedding_coe_real.noncompactSpace

/--
theorem `Real.uniformContinuous_add` / 定理 `Real.uniformContinuous_add`

English:
theorem Real.uniformContinuous_add
  statement: UniformContinuous fun p : Real × Real => p.1 + p.2
  proof: Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0
    ⟨δ, δ0, fun _ _ h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ h₁ h₂⟩

中文:
定理 实数.uniformContinuous_add
  结论: 一致连续 fun p : 实数 × 实数 => p.1 + p.2
  证明: Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0
    ⟨δ, δ0, fun _ _ h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ h₁ h₂⟩

Depends on / 依赖: Metric, Metric.uniformContinuous_iff, max_lt_iff, rat_add_continuous_lemma, uniformContinuous_iff
-/
theorem Real.uniformContinuous_add : UniformContinuous fun p : Real × Real => p.1 + p.2 :=
  Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0
    ⟨δ, δ0, fun _ _ h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ h₁ h₂⟩

/--
theorem `Real.uniformContinuous_neg` / 定理 `Real.uniformContinuous_neg`

English:
theorem Real.uniformContinuous_neg
  statement: UniformContinuous (@Neg.neg Real _)
  proof: Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by simpa only [abs_sub_comm, Real.dist_eq, neg_sub_neg] using h⟩

中文:
定理 实数.uniformContinuous_neg
  结论: 一致连续 (@取负.neg 实数 _)
  证明: Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by simpa only [abs_sub_comm, Real.dist_eq, neg_sub_neg] using h⟩

Depends on / 依赖: Metric, Metric.uniformContinuous_iff, Real.dist_eq, abs_sub_comm, dist_eq, neg_sub_neg, uniformContinuous_iff
-/
theorem Real.uniformContinuous_neg : UniformContinuous (@Neg.neg Real _) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by simpa only [abs_sub_comm, Real.dist_eq, neg_sub_neg] using h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsUniformAddGroup Real
  body: IsUniformAddGroup.mk' Real.uniformContinuous_add Real.uniformContinuous_neg

中文:
实例 :
  签名: 是UniformAdd群 实数
  定义体: IsUniformAddGroup.mk' Real.uniformContinuous_add Real.uniformContinuous_neg

Depends on / 依赖: IsUniformAddGroup, IsUniformAddGroup.mk, Real.uniformContinuous_add, Real.uniformContinuous_neg, uniformContinuous_add, uniformContinuous_neg
-/
instance : IsUniformAddGroup Real :=
  IsUniformAddGroup.mk' Real.uniformContinuous_add Real.uniformContinuous_neg

/--
theorem `Real.uniformContinuous_const_mul` / 定理 `Real.uniformContinuous_const_mul`

English:
theorem Real.uniformContinuous_const_mul
  given: {x : Real}
  statement: UniformContinuous (x * ·)
  proof: uniformContinuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom Real x)
    (continuous_const_smul x).continuousAt

中文:
定理 实数.uniformContinuous_const_mul
  条件: {x : 实数}
  结论: 一致连续 (x * ·)
  证明: uniformContinuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom Real x)
    (continuous_const_smul x).continuousAt

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, continuousAt, continuous_const_smul, toAddMonoidHom, uniformContinuous_of_continuousAt_zero
-/
theorem Real.uniformContinuous_const_mul {x : Real} : UniformContinuous (x * ·) :=
  uniformContinuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom Real x)
    (continuous_const_smul x).continuousAt

-- short-circuit type class inference
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalAddGroup Real
  body: by infer_instance

中文:
实例 :
  签名: 是拓扑加群 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : IsTopologicalAddGroup Real := by infer_instance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalRing Real
  body: inferInstance

中文:
实例 :
  签名: 是拓扑环 实数
  定义体: inferInstance
-/
instance : IsTopologicalRing Real := inferInstance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalDivisionRing Real
  body: inferInstance

中文:
实例 :
  签名: 是TopologicalDivision环 实数
  定义体: inferInstance
-/
instance : IsTopologicalDivisionRing Real := inferInstance

namespace EReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousNeg EReal
  body: ⟨negOrderIso.continuous⟩

中文:
实例 :
  签名: 连续取负 E实数
  定义体: ⟨negOrderIso.continuous⟩

Depends on / 依赖: continuous, negOrderIso, negOrderIso.continuous
-/
instance : ContinuousNeg EReal := ⟨negOrderIso.continuous⟩

end EReal

namespace NNReal

-- short-circuit type class inference
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalSemiring Real>=0
  body: continuousAdd_induced toRealHom
  toContinuousMul := continuousMul_induced toRealHom

中文:
实例 :
  签名: 是TopologicalSemiring 实数>=0
  定义体: continuousAdd_induced toRealHom
  toContinuousMul := continuousMul_induced toRealHom

Depends on / 依赖: continuousAdd_induced, toRealHom
-/
instance : IsTopologicalSemiring Real>=0 where
  toContinuousAdd := continuousAdd_induced toRealHom
  toContinuousMul := continuousMul_induced toRealHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSub Real>=0
  body: ⟨((continuous_coe.fst'.sub continuous_coe.snd').max continuous_const).subtype_mk _⟩

中文:
实例 :
  签名: 余ntinuousSub 实数>=0
  定义体: ⟨((continuous_coe.fst'.sub continuous_coe.snd').max continuous_const).subtype_mk _⟩

Depends on / 依赖: continuous_coe, continuous_coe.fst, continuous_coe.snd, continuous_const, subtype_mk
-/
instance : ContinuousSub Real>=0 :=
  ⟨((continuous_coe.fst'.sub continuous_coe.snd').max continuous_const).subtype_mk _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousInv₀ Real>=0
  body: inferInstance

中文:
实例 :
  签名: 余ntinuousInv₀ 实数>=0
  定义体: inferInstance
-/
instance : ContinuousInv₀ Real>=0 := inferInstance

variable {α : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [MulAction Real α] [ContinuousSMul Real α] :
  body: continuous_induced_dom.fst'.smul continuous_snd

中文:
实例 [拓扑空间
  签名: α] [乘法作用 实数 α] [连续标量乘法 实数 α] :
  定义体: continuous_induced_dom.fst'.smul continuous_snd

Depends on / 依赖: continuous_induced_dom, continuous_induced_dom.fst, continuous_snd
-/
instance [TopologicalSpace α] [MulAction Real α] [ContinuousSMul Real α] :
    ContinuousSMul Real>=0 α where
  continuous_smul := continuous_induced_dom.fst'.smul continuous_snd

end NNReal

namespace ENNReal

open Filter NNReal Set Topology

/--
theorem `isEmbedding_coe` / 定理 `isEmbedding_coe`

English:
theorem isEmbedding_coe
  statement: IsEmbedding ((↑) : Real>=0 -> Real>=0∞)
  proof: coe_strictMono.isEmbedding_of_ordConnected by rw [range_coe']; exact ordConnected_Iio

@[simp, norm_cast]

中文:
定理 isEmbedding_coe
  结论: 是嵌入 ((↑) : 实数>=0 -> 实数>=0∞)
  证明: coe_strictMono.isEmbedding_of_ordConnected by rw [range_coe']; exact ordConnected_Iio

@[simp, norm_cast]

Depends on / 依赖: coe_strictMono, coe_strictMono.isEmbedding_of_ordConnected, isEmbedding_of_ordConnected, ordConnected_Iio, range_coe
-/
theorem isEmbedding_coe : IsEmbedding ((↑) : Real>=0 -> Real>=0∞) :=
coe_strictMono.isEmbedding_of_ordConnected by rw [range_coe']; exact ordConnected_Iio

@[simp, norm_cast]
/--
theorem `tendsto_coe` / 定理 `tendsto_coe`

English:
theorem tendsto_coe
  given: {f : Filter α} {m : α -> Real>=0} {a : Real>=0}
  proof: isEmbedding_coe.tendsto_nhds_iff.symm

中文:
定理 tendsto_coe
  条件: {f : 滤子 α} {m : α -> 实数>=0} {a : 实数>=0}
  证明: isEmbedding_coe.tendsto_nhds_iff.symm

Depends on / 依赖: isEmbedding_coe, isEmbedding_coe.tendsto_nhds_iff.symm, tendsto_nhds_iff
-/
theorem tendsto_coe {f : Filter α} {m : α -> Real>=0} {a : Real>=0} :
    Tendsto (fun a => (m a : Real>=0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  isEmbedding_coe.tendsto_nhds_iff.symm

/--
theorem `isOpenEmbedding_coe` / 定理 `isOpenEmbedding_coe`

English:
theorem isOpenEmbedding_coe
  statement: IsOpenEmbedding ((↑) : Real>=0 -> Real>=0∞)
  proof: ⟨isEmbedding_coe, by rw [range_coe']; exact isOpen_Iio⟩

中文:
定理 isOpenEmbedding_coe
  结论: 是开嵌入 ((↑) : 实数>=0 -> 实数>=0∞)
  证明: ⟨isEmbedding_coe, by rw [range_coe']; exact isOpen_Iio⟩

Depends on / 依赖: isEmbedding_coe, isOpen_Iio, range_coe
-/
theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : Real>=0 -> Real>=0∞) :=
  ⟨isEmbedding_coe, by rw [range_coe']; exact isOpen_Iio⟩

/--
theorem `nhds_coe_coe` / 定理 `nhds_coe_coe`

English:
theorem nhds_coe_coe
  given: {r p : Real>=0}
  proof: ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm

中文:
定理 nhds_coe_coe
  条件: {r p : 实数>=0}
  证明: ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.prodMap, map_nhds_eq, prodMap
-/
theorem nhds_coe_coe {r p : Real>=0} :
    𝓝 ((r : Real>=0∞), (p : Real>=0∞)) = (𝓝 (r, p)).map fun p : Real>=0 × Real>=0 => (↑p.1, ↑p.2) :=
  ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousAdd Real>=0∞
  body: by
  refine ⟨continuous_iff_continuousAt.2 ?_⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  simp only [ContinuousAt, some_eq_coe, nhds_coe_coe

中文:
实例 :
  签名: 连续加法 实数>=0∞
  定义体: by
  refine ⟨continuous_iff_continuousAt.2 ?_⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  simp only [ContinuousAt, some_eq_coe, nhds_coe_coe

Depends on / 依赖: ContinuousAt, Function, Function.comp_def, _iff, coe_add, comp_def, continuousAt_fst, continuousAt_snd, continuous_iff_continuousAt, le_add_left, le_add_right, le_rfl, nhds_coe_coe, some_eq_coe, tendsto_add, tendsto_coe, tendsto_map, tendsto_nhds_top_mono
-/
instance : ContinuousAdd Real>=0∞ := by
  refine ⟨continuous_iff_continuousAt.2 ?_⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  simp only [ContinuousAt, some_eq_coe, nhds_coe_coe, ← coe_add, tendsto_map'_iff,
    Function.comp_def, tendsto_coe, tendsto_add]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousInv Real>=0∞
  body: ⟨OrderIso.invENNReal.continuous⟩

中文:
实例 :
  签名: 连续取逆 实数>=0∞
  定义体: ⟨OrderIso.invENNReal.continuous⟩

Depends on / 依赖: OrderIso, OrderIso.invENNReal.continuous, continuous, invENNReal
-/
instance : ContinuousInv Real>=0∞ := ⟨OrderIso.invENNReal.continuous⟩

end ENNReal
