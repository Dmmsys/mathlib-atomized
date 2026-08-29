/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Topology on extended non-negative reals
-/

@[expose] public section

noncomputable section

open Filter Function Metric Set Topology
open scoped Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : Real>=0∞} {r : Real>=0} {x : Real>=0∞} {ε : Real>=0∞}

section TopologicalSpace

open TopologicalSpace

/--
theorem `isOpen_ne_top` / 定理 `isOpen_ne_top`

English:
theorem isOpen_ne_top
  statement: IsOpen { a : Real>=0∞ | a != ∞ }
  proof: isOpen_ne

中文:
定理 isOpen_ne_top
  结论: IsOpen { a : 实数>=0∞ | a != ∞ }
  证明: isOpen_ne

Depends on / 依赖: isOpen_ne
-/
theorem isOpen_ne_top : IsOpen { a : Real>=0∞ | a != ∞ } := isOpen_ne

/--
theorem `isOpen_Ico_zero` / 定理 `isOpen_Ico_zero`

English:
theorem isOpen_Ico_zero
  statement: IsOpen (Ico 0 b)
  proof: by
  rw [ENNReal.Ico_eq_Iio]
  exact isOpen_Iio

中文:
定理 isOpen_Ico_zero
  结论: IsOpen (Ico 0 b)
  证明: by
  rw [ENNReal.Ico_eq_Iio]
  exact isOpen_Iio

Depends on / 依赖: ENNReal, ENNReal.Ico_eq_Iio, Ico_eq_Iio, isOpen_Iio
-/
theorem isOpen_Ico_zero : IsOpen (Ico 0 b) := by
  rw [ENNReal.Ico_eq_Iio]
  exact isOpen_Iio

/--
theorem `coe_range_mem_nhds` / 定理 `coe_range_mem_nhds`

English:
theorem coe_range_mem_nhds
  statement: range ((↑) : Real>=0 -> Real>=0∞) in 𝓝 (r : Real>=0∞)
  proof: IsOpen.mem_nhds isOpenEmbedding_coe.isOpen_range mem_range_self _

@[fun_prop]

中文:
定理 coe_range_mem_nhds
  结论: range ((↑) : 实数>=0 -> 实数>=0∞) in 𝓝 (r : 实数>=0∞)
  证明: IsOpen.mem_nhds isOpenEmbedding_coe.isOpen_range mem_range_self _

@[fun_prop]

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, isOpenEmbedding_coe, isOpenEmbedding_coe.isOpen_range, isOpen_range, mem_nhds, mem_range_self
-/
theorem coe_range_mem_nhds : range ((↑) : Real>=0 -> Real>=0∞) in 𝓝 (r : Real>=0∞) :=
IsOpen.mem_nhds isOpenEmbedding_coe.isOpen_range mem_range_self _

@[fun_prop]
/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous ((↑) : Real>=0 -> Real>=0∞)
  proof: isEmbedding_coe.continuous

中文:
定理 continuous_coe
  结论: Continuous ((↑) : 实数>=0 -> 实数>=0∞)
  证明: isEmbedding_coe.continuous

Depends on / 依赖: continuous, isEmbedding_coe, isEmbedding_coe.continuous
-/
theorem continuous_coe : Continuous ((↑) : Real>=0 -> Real>=0∞) :=
  isEmbedding_coe.continuous

/--
lemma `tendsto_coe_toNNReal` / 引理 `tendsto_coe_toNNReal`

English:
lemma tendsto_coe_toNNReal
  given: {a : Real>=0∞} (ha : a != ⊤)
  statement: Tendsto (↑) (𝓝 a.toNNReal) (𝓝 a)
  proof: by
  nth_rewrite 2 [← coe_toNNReal ha]
  exact continuous_coe.tendsto _

中文:
引理 tendsto_coe_toNNReal
  条件: {a : 实数>=0∞} (ha : a != ⊤)
  结论: Tendsto (↑) (𝓝 a.toNN实数) (𝓝 a)
  证明: by
  nth_rewrite 2 [← coe_toNNReal ha]
  exact continuous_coe.tendsto _

Depends on / 依赖: coe_toNNReal, continuous_coe, continuous_coe.tendsto, nth_rewrite, tendsto
-/
lemma tendsto_coe_toNNReal {a : Real>=0∞} (ha : a != ⊤) : Tendsto (↑) (𝓝 a.toNNReal) (𝓝 a) := by
  nth_rewrite 2 [← coe_toNNReal ha]
  exact continuous_coe.tendsto _

/--
theorem `continuous_coe_iff` / 定理 `continuous_coe_iff`

English:
theorem continuous_coe_iff
  given: {α} [TopologicalSpace α] {f : α -> Real>=0}
  proof: isEmbedding_coe.continuous_iff.symm

中文:
定理 continuous_coe_iff
  条件: {α} [TopologicalSpace α] {f : α -> 实数>=0}
  证明: isEmbedding_coe.continuous_iff.symm

Depends on / 依赖: continuous_iff, isEmbedding_coe, isEmbedding_coe.continuous_iff.symm
-/
theorem continuous_coe_iff {α} [TopologicalSpace α] {f : α -> Real>=0} :
    (Continuous fun a => (f a : Real>=0∞)) ↔ Continuous f :=
  isEmbedding_coe.continuous_iff.symm

/--
theorem `nhds_coe` / 定理 `nhds_coe`

English:
theorem nhds_coe
  given: {r : Real>=0}
  statement: 𝓝 (r : Real>=0∞) = (𝓝 r).map (↑)
  proof: (isOpenEmbedding_coe.map_nhds_eq r).symm

中文:
定理 nhds_coe
  条件: {r : 实数>=0}
  结论: 𝓝 (r : 实数>=0∞) = (𝓝 r).map (↑)
  证明: (isOpenEmbedding_coe.map_nhds_eq r).symm

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.map_nhds_eq, map_nhds_eq
-/
theorem nhds_coe {r : Real>=0} : 𝓝 (r : Real>=0∞) = (𝓝 r).map (↑) :=
  (isOpenEmbedding_coe.map_nhds_eq r).symm

/--
theorem `tendsto_nhds_coe_iff` / 定理 `tendsto_nhds_coe_iff`

English:
theorem tendsto_nhds_coe_iff
  given: {α : Type*} {l : Filter α} {x : Real>=0} {f : Real>=0∞ -> α}
  proof: by
  rw [nhds_coe]; rw [tendsto_map'_iff]

中文:
定理 tendsto_nhds_coe_iff
  条件: {α : 类型} {l : Filter α} {x : 实数>=0} {f : 实数>=0∞ -> α}
  证明: by
  rw [nhds_coe]; rw [tendsto_map'_iff]

Depends on / 依赖: _iff, nhds_coe, tendsto_map
-/
theorem tendsto_nhds_coe_iff {α : Type*} {l : Filter α} {x : Real>=0} {f : Real>=0∞ -> α} :
    Tendsto f (𝓝 ↑x) l ↔ Tendsto (f ∘ (↑) : Real>=0 -> α) (𝓝 x) l := by
  rw [nhds_coe]; rw [tendsto_map'_iff]

/--
theorem `continuousAt_coe_iff` / 定理 `continuousAt_coe_iff`

English:
theorem continuousAt_coe_iff
  given: {α : Type*} [TopologicalSpace α] {x : Real>=0} {f : Real>=0∞ -> α}
  proof: tendsto_nhds_coe_iff

中文:
定理 continuousAt_coe_iff
  条件: {α : 类型} [TopologicalSpace α] {x : 实数>=0} {f : 实数>=0∞ -> α}
  证明: tendsto_nhds_coe_iff

Depends on / 依赖: tendsto_nhds_coe_iff
-/
theorem continuousAt_coe_iff {α : Type*} [TopologicalSpace α] {x : Real>=0} {f : Real>=0∞ -> α} :
    ContinuousAt f ↑x ↔ ContinuousAt (f ∘ (↑) : Real>=0 -> α) x :=
  tendsto_nhds_coe_iff

/--
theorem `continuous_ofReal` / 定理 `continuous_ofReal`

English:
theorem continuous_ofReal
  statement: Continuous ENNReal.ofReal
  proof: (continuous_coe_iff.2 continuous_id).comp continuous_real_toNNReal

中文:
定理 continuous_ofReal
  结论: Continuous ENN实数.of实数
  证明: (continuous_coe_iff.2 continuous_id).comp continuous_real_toNNReal

Depends on / 依赖: continuous_coe_iff, continuous_id, continuous_real_toNNReal
-/
theorem continuous_ofReal : Continuous ENNReal.ofReal :=
  (continuous_coe_iff.2 continuous_id).comp continuous_real_toNNReal

/--
theorem `tendsto_ofReal` / 定理 `tendsto_ofReal`

English:
theorem tendsto_ofReal
  given: {f : Filter α} {m : α -> Real} {a : Real} (h : Tendsto m f (𝓝 a))
  proof: (continuous_ofReal.tendsto a).comp h

中文:
定理 tendsto_ofReal
  条件: {f : Filter α} {m : α -> 实数} {a : 实数} (h : Tendsto m f (𝓝 a))
  证明: (continuous_ofReal.tendsto a).comp h

Depends on / 依赖: continuous_ofReal, continuous_ofReal.tendsto, tendsto
-/
theorem tendsto_ofReal {f : Filter α} {m : α -> Real} {a : Real} (h : Tendsto m f (𝓝 a)) :
    Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 (ENNReal.ofReal a)) :=
  (continuous_ofReal.tendsto a).comp h

/--
theorem `tendsto_toNNReal` / 定理 `tendsto_toNNReal`

English:
theorem tendsto_toNNReal
  given: {a : Real>=0∞} (ha : a != ∞)
  proof: by
  lift a to Real>=0 using ha
  rw [nhds_coe]; rw [tendsto_map'_iff]
  exact tendsto_id

中文:
定理 tendsto_toNNReal
  条件: {a : 实数>=0∞} (ha : a != ∞)
  证明: by
  lift a to Real>=0 using ha
  rw [nhds_coe]; rw [tendsto_map'_iff]
  exact tendsto_id

Depends on / 依赖: _iff, nhds_coe, tendsto_id, tendsto_map
-/
theorem tendsto_toNNReal {a : Real>=0∞} (ha : a != ∞) :
    Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal) := by
  lift a to Real>=0 using ha
  rw [nhds_coe]; rw [tendsto_map'_iff]
  exact tendsto_id

/--
theorem `tendsto_toNNReal_iff` / 定理 `tendsto_toNNReal_iff`

English:
theorem tendsto_toNNReal_iff
  given: {f : α -> Real>=0∞} {u : Filter α} (ha : a != ∞) (hf : forall x, f x != ∞)
  proof: by
  refine ⟨fun h => ?_, fun h => (ENNReal.tendsto_toNNReal ha).comp h⟩
  rw [← coe_comp_toNNReal_comp hf]
  exact (tendsto_coe_toNNReal ha).comp h

中文:
定理 tendsto_toNNReal_iff
  条件: {f : α -> 实数>=0∞} {u : Filter α} (ha : a != ∞) (hf : 对任意 x, f x != ∞)
  证明: by
  refine ⟨fun h => ?_, fun h => (ENNReal.tendsto_toNNReal ha).comp h⟩
  rw [← coe_comp_toNNReal_comp hf]
  exact (tendsto_coe_toNNReal ha).comp h

Depends on / 依赖: ENNReal, ENNReal.tendsto_toNNReal, coe_comp_toNNReal_comp, tendsto_coe_toNNReal, tendsto_toNNReal
-/
theorem tendsto_toNNReal_iff {f : α -> Real>=0∞} {u : Filter α} (ha : a != ∞) (hf : forall x, f x != ∞) :
    Tendsto (ENNReal.toNNReal ∘ f) u (𝓝 (a.toNNReal)) ↔ Tendsto f u (𝓝 a) := by
  refine ⟨fun h => ?_, fun h => (ENNReal.tendsto_toNNReal ha).comp h⟩
  rw [← coe_comp_toNNReal_comp hf]
  exact (tendsto_coe_toNNReal ha).comp h

/--
theorem `tendsto_toNNReal_iff'` / 定理 `tendsto_toNNReal_iff'`

English:
theorem tendsto_toNNReal_iff'
  given: {f : α -> Real>=0∞} {u : Filter α} {a : Real>=0} (hf : forall x, f x != ∞)
  proof: by
  rw [← toNNReal_coe a]
  exact tendsto_toNNReal_iff coe_ne_top hf

中文:
定理 tendsto_toNNReal_iff'
  条件: {f : α -> 实数>=0∞} {u : Filter α} {a : 实数>=0} (hf : 对任意 x, f x != ∞)
  证明: by
  rw [← toNNReal_coe a]
  exact tendsto_toNNReal_iff coe_ne_top hf

Depends on / 依赖: coe_ne_top, tendsto_toNNReal_iff, toNNReal_coe
-/
theorem tendsto_toNNReal_iff' {f : α -> Real>=0∞} {u : Filter α} {a : Real>=0} (hf : forall x, f x != ∞) :
    Tendsto (ENNReal.toNNReal ∘ f) u (𝓝 a) ↔ Tendsto f u (𝓝 a) := by
  rw [← toNNReal_coe a]
  exact tendsto_toNNReal_iff coe_ne_top hf

/--
theorem `eventuallyEq_of_toReal_eventuallyEq` / 定理 `eventuallyEq_of_toReal_eventuallyEq`

English:
theorem eventuallyEq_of_toReal_eventuallyEq
  statement: {l : Filter α} {f g : α -> Real>=0∞}
  proof: by
  filter_upwards [hfi, hgi, hfg] with _ hfx hgx _
  rwa [← ENNReal.toReal_eq_toReal_iff' hfx hgx]

中文:
定理 eventuallyEq_of_toReal_eventuallyEq
  结论: {l : Filter α} {f g : α -> 实数>=0∞}
  证明: by
  filter_upwards [hfi, hgi, hfg] with _ hfx hgx _
  rwa [← ENNReal.toReal_eq_toReal_iff' hfx hgx]

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_toReal_iff, filter_upwards, toReal_eq_toReal_iff
-/
theorem eventuallyEq_of_toReal_eventuallyEq {l : Filter α} {f g : α -> Real>=0∞}
    (hfi : forallᶠ x in l, f x != ∞) (hgi : forallᶠ x in l, g x != ∞)
    (hfg : (fun x => (f x).toReal) =ᶠ[l] fun x => (g x).toReal) : f =ᶠ[l] g := by
  filter_upwards [hfi, hgi, hfg] with _ hfx hgx _
  rwa [← ENNReal.toReal_eq_toReal_iff' hfx hgx]

/--
theorem `continuousOn_toNNReal` / 定理 `continuousOn_toNNReal`

English:
theorem continuousOn_toNNReal
  statement: ContinuousOn ENNReal.toNNReal { a | a != ∞ }
  proof: fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toNNReal ha)

中文:
定理 continuousOn_toNNReal
  结论: ContinuousOn ENN实数.toNN实数 { a | a != ∞ }
  证明: fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toNNReal ha)
-/
theorem continuousOn_toNNReal : ContinuousOn ENNReal.toNNReal { a | a != ∞ } := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toNNReal ha)

/--
theorem `tendsto_toReal` / 定理 `tendsto_toReal`

English:
theorem tendsto_toReal
  given: {a : Real>=0∞} (ha : a != ∞)
  statement: Tendsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal)
  proof: NNReal.tendsto_coe.2 tendsto_toNNReal ha

中文:
定理 tendsto_toReal
  条件: {a : 实数>=0∞} (ha : a != ∞)
  结论: Tendsto ENN实数.to实数 (𝓝 a) (𝓝 a.to实数)
  证明: NNReal.tendsto_coe.2 tendsto_toNNReal ha

Depends on / 依赖: NNReal, NNReal.tendsto_coe, tendsto_coe, tendsto_toNNReal
-/
theorem tendsto_toReal {a : Real>=0∞} (ha : a != ∞) : Tendsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal) :=
NNReal.tendsto_coe.2 tendsto_toNNReal ha

/--
lemma `continuousOn_toReal` / 引理 `continuousOn_toReal`

English:
lemma continuousOn_toReal
  statement: ContinuousOn ENNReal.toReal { a | a != ∞ }
  proof: NNReal.continuous_coe.comp_continuousOn continuousOn_toNNReal

中文:
引理 continuousOn_toReal
  结论: ContinuousOn ENN实数.to实数 { a | a != ∞ }
  证明: NNReal.continuous_coe.comp_continuousOn continuousOn_toNNReal

Depends on / 依赖: NNReal, NNReal.continuous_coe.comp_continuousOn, comp_continuousOn, continuousOn_toNNReal, continuous_coe
-/
lemma continuousOn_toReal : ContinuousOn ENNReal.toReal { a | a != ∞ } :=
  NNReal.continuous_coe.comp_continuousOn continuousOn_toNNReal

/--
lemma `continuousAt_toReal` / 引理 `continuousAt_toReal`

English:
lemma continuousAt_toReal
  given: (hx : x != ∞)
  statement: ContinuousAt ENNReal.toReal x
  proof: continuousOn_toReal.continuousAt (isOpen_ne_top.mem_nhds_iff.mpr hx)

中文:
引理 continuousAt_toReal
  条件: (hx : x != ∞)
  结论: ContinuousAt ENN实数.to实数 x
  证明: continuousOn_toReal.continuousAt (isOpen_ne_top.mem_nhds_iff.mpr hx)

Depends on / 依赖: continuousAt, continuousOn_toReal, continuousOn_toReal.continuousAt, isOpen_ne_top, isOpen_ne_top.mem_nhds_iff.mpr, mem_nhds_iff
-/
lemma continuousAt_toReal (hx : x != ∞) : ContinuousAt ENNReal.toReal x :=
  continuousOn_toReal.continuousAt (isOpen_ne_top.mem_nhds_iff.mpr hx)

/--
Definition of `neTopHomeomorphNNReal` / `neTopHomeomorphNNReal` 的定义

English:
definition neTopHomeomorphNNReal
  signature: : { a | a != ∞ } ≃ₜ Real>=0 where
  body: neTopEquivNNReal
  continuous_toFun := continuousOn_iff_continuous_domRestrict.1 continuousOn_toNNReal
  continuous_invFun := continuous_coe.subtype_mk _

中文:
定义 neTopHomeomorphNNReal
  签名: : { a | a != ∞ } ≃ₜ 实数>=0 where
  定义体: neTopEquivNNReal
  continuous_toFun := continuousOn_iff_continuous_domRestrict.1 continuousOn_toNNReal
  continuous_invFun := continuous_coe.subtype_mk _

Depends on / 依赖: neTopEquivNNReal
-/
def neTopHomeomorphNNReal : { a | a != ∞ } ≃ₜ Real>=0 where
  toEquiv := neTopEquivNNReal
  continuous_toFun := continuousOn_iff_continuous_domRestrict.1 continuousOn_toNNReal
  continuous_invFun := continuous_coe.subtype_mk _

/--
Definition of `ltTopHomeomorphNNReal` / `ltTopHomeomorphNNReal` 的定义

English:
definition ltTopHomeomorphNNReal
  signature: : { a | a < ∞ } ≃ₜ Real>=0
  body: by
  refine (Homeomorph.setCongr ?_).trans neTopHomeomorphNNReal
  simp only [lt_top_iff_ne_top]

中文:
定义 ltTopHomeomorphNNReal
  签名: : { a | a < ∞ } ≃ₜ 实数>=0
  定义体: by
  refine (Homeomorph.setCongr ?_).trans neTopHomeomorphNNReal
  simp only [lt_top_iff_ne_top]

Depends on / 依赖: Homeomorph, Homeomorph.setCongr, lt_top_iff_ne_top, neTopHomeomorphNNReal, setCongr
-/
def ltTopHomeomorphNNReal : { a | a < ∞ } ≃ₜ Real>=0 := by
  refine (Homeomorph.setCongr ?_).trans neTopHomeomorphNNReal
  simp only [lt_top_iff_ne_top]

/--
theorem `nhds_top` / 定理 `nhds_top`

English:
theorem nhds_top
  statement: 𝓝 ∞ = ⨅ (a) (_ : a != ∞), 𝓟 (Ioi a)
  proof: nhds_top_order.trans by simp [lt_top_iff_ne_top, Ioi]

中文:
定理 nhds_top
  结论: 𝓝 ∞ = ⨅ (a) (_ : a != ∞), 𝓟 (Ioi a)
  证明: nhds_top_order.trans by simp [lt_top_iff_ne_top, Ioi]

Depends on / 依赖: lt_top_iff_ne_top, nhds_top_order, nhds_top_order.trans
-/
theorem nhds_top : 𝓝 ∞ = ⨅ (a) (_ : a != ∞), 𝓟 (Ioi a) :=
nhds_top_order.trans by simp [lt_top_iff_ne_top, Ioi]

/--
theorem `nhds_top'` / 定理 `nhds_top'`

English:
theorem nhds_top'
  statement: 𝓝 ∞ = ⨅ r : Real>=0, 𝓟 (Ioi ↑r)
  proof: nhds_top.trans iInf_ne_top _

中文:
定理 nhds_top'
  结论: 𝓝 ∞ = ⨅ r : 实数>=0, 𝓟 (Ioi ↑r)
  证明: nhds_top.trans iInf_ne_top _

Depends on / 依赖: iInf_ne_top, nhds_top, nhds_top.trans
-/
theorem nhds_top' : 𝓝 ∞ = ⨅ r : Real>=0, 𝓟 (Ioi ↑r) :=
nhds_top.trans iInf_ne_top _

/--
theorem `nhds_top_basis` / 定理 `nhds_top_basis`

English:
theorem nhds_top_basis
  statement: (𝓝 ∞).HasBasis (fun a => a < ∞) fun a => Ioi a
  proof: _root_.nhds_top_basis

中文:
定理 nhds_top_basis
  结论: (𝓝 ∞).HasBasis (fun a => a < ∞) fun a => Ioi a
  证明: _root_.nhds_top_basis

Depends on / 依赖: _root_, _root_.nhds_top_basis, nhds_top_basis
-/
theorem nhds_top_basis : (𝓝 ∞).HasBasis (fun a => a < ∞) fun a => Ioi a :=
  _root_.nhds_top_basis

/--
theorem `tendsto_nhds_top_iff_nnreal` / 定理 `tendsto_nhds_top_iff_nnreal`

English:
theorem tendsto_nhds_top_iff_nnreal
  given: {m : α -> Real>=0∞} {f : Filter α}
  proof: by
  simp only [nhds_top', tendsto_iInf, tendsto_principal, mem_Ioi]

中文:
定理 tendsto_nhds_top_iff_nnreal
  条件: {m : α -> 实数>=0∞} {f : Filter α}
  证明: by
  simp only [nhds_top', tendsto_iInf, tendsto_principal, mem_Ioi]

Depends on / 依赖: mem_Ioi, nhds_top, tendsto_iInf, tendsto_principal
-/
theorem tendsto_nhds_top_iff_nnreal {m : α -> Real>=0∞} {f : Filter α} :
    Tendsto m f (𝓝 ∞) ↔ forall x : Real>=0, forallᶠ a in f, ↑x < m a := by
  simp only [nhds_top', tendsto_iInf, tendsto_principal, mem_Ioi]

/--
theorem `tendsto_nhds_top_iff_nat` / 定理 `tendsto_nhds_top_iff_nat`

English:
theorem tendsto_nhds_top_iff_nat
  given: {m : α -> Real>=0∞} {f : Filter α}
  proof: tendsto_nhds_top_iff_nnreal.trans
    ⟨fun h n => by simpa only [ENNReal.coe_natCast] using h n, fun h x =>
      let ⟨n, hn⟩ := exists_nat_gt x
(h n).mono fun _ => lt_trans by rwa [← ENNReal.coe_natCast, coe_lt_coe]⟩

中文:
定理 tendsto_nhds_top_iff_nat
  条件: {m : α -> 实数>=0∞} {f : Filter α}
  证明: tendsto_nhds_top_iff_nnreal.trans
    ⟨fun h n => by simpa only [ENNReal.coe_natCast] using h n, fun h x =>
      let ⟨n, hn⟩ := exists_nat_gt x
(h n).mono fun _ => lt_trans by rwa [← ENNReal.coe_natCast, coe_lt_coe]⟩

Depends on / 依赖: ENNReal, ENNReal.coe_natCast, coe_lt_coe, coe_natCast, exists_nat_gt, lt_trans, tendsto_nhds_top_iff_nnreal, tendsto_nhds_top_iff_nnreal.trans
-/
theorem tendsto_nhds_top_iff_nat {m : α -> Real>=0∞} {f : Filter α} :
    Tendsto m f (𝓝 ∞) ↔ forall n : Nat, forallᶠ a in f, ↑n < m a :=
  tendsto_nhds_top_iff_nnreal.trans
    ⟨fun h n => by simpa only [ENNReal.coe_natCast] using h n, fun h x =>
      let ⟨n, hn⟩ := exists_nat_gt x
(h n).mono fun _ => lt_trans by rwa [← ENNReal.coe_natCast, coe_lt_coe]⟩

/--
theorem `tendsto_nhds_top` / 定理 `tendsto_nhds_top`

English:
theorem tendsto_nhds_top
  given: {m : α -> Real>=0∞} {f : Filter α} (h : forall n : Nat, forallᶠ a in f, ↑n < m a)
  proof: tendsto_nhds_top_iff_nat.2 h

中文:
定理 tendsto_nhds_top
  条件: {m : α -> 实数>=0∞} {f : Filter α} (h : 对任意 n : 自然数, 对任意ᶠ a in f, ↑n < m a)
  证明: tendsto_nhds_top_iff_nat.2 h

Depends on / 依赖: tendsto_nhds_top_iff_nat
-/
theorem tendsto_nhds_top {m : α -> Real>=0∞} {f : Filter α} (h : forall n : Nat, forallᶠ a in f, ↑n < m a) :
    Tendsto m f (𝓝 ∞) :=
  tendsto_nhds_top_iff_nat.2 h

/--
theorem `tendsto_nat_nhds_top` / 定理 `tendsto_nat_nhds_top`

English:
theorem tendsto_nat_nhds_top
  statement: Tendsto (fun n : Nat => ↑n) atTop (𝓝 ∞)
  proof: tendsto_nhds_top fun n =>
mem_atTop_sets.2 ⟨n + 1, fun _m hm => mem_ofPred.2 Nat.cast_lt.2 Nat.lt_of_succ_le hm⟩

@[simp, norm_cast]

中文:
定理 tendsto_nat_nhds_top
  结论: Tendsto (fun n : 自然数 => ↑n) atTop (𝓝 ∞)
  证明: tendsto_nhds_top fun n =>
mem_atTop_sets.2 ⟨n + 1, fun _m hm => mem_ofPred.2 Nat.cast_lt.2 Nat.lt_of_succ_le hm⟩

@[simp, norm_cast]

Depends on / 依赖: Nat.cast_lt, Nat.lt_of_succ_le, cast_lt, lt_of_succ_le, mem_atTop_sets, mem_ofPred, tendsto_nhds_top
-/
theorem tendsto_nat_nhds_top : Tendsto (fun n : Nat => ↑n) atTop (𝓝 ∞) :=
  tendsto_nhds_top fun n =>
mem_atTop_sets.2 ⟨n + 1, fun _m hm => mem_ofPred.2 Nat.cast_lt.2 Nat.lt_of_succ_le hm⟩

@[simp, norm_cast]
/--
theorem `tendsto_coe_nhds_top` / 定理 `tendsto_coe_nhds_top`

English:
theorem tendsto_coe_nhds_top
  given: {f : α -> Real>=0} {l : Filter α}
  proof: by
  rw [tendsto_nhds_top_iff_nnreal]; rw [atTop_basis_Ioi.tendsto_right_iff]; simp

@[simp]

中文:
定理 tendsto_coe_nhds_top
  条件: {f : α -> 实数>=0} {l : Filter α}
  证明: by
  rw [tendsto_nhds_top_iff_nnreal]; rw [atTop_basis_Ioi.tendsto_right_iff]; simp

@[simp]

Depends on / 依赖: atTop_basis_Ioi, atTop_basis_Ioi.tendsto_right_iff, tendsto_nhds_top_iff_nnreal, tendsto_right_iff
-/
theorem tendsto_coe_nhds_top {f : α -> Real>=0} {l : Filter α} :
    Tendsto (fun x => (f x : Real>=0∞)) l (𝓝 ∞) ↔ Tendsto f l atTop := by
  rw [tendsto_nhds_top_iff_nnreal]; rw [atTop_basis_Ioi.tendsto_right_iff]; simp

@[simp]
/--
theorem `tendsto_ofReal_nhds_top` / 定理 `tendsto_ofReal_nhds_top`

English:
theorem tendsto_ofReal_nhds_top
  given: {f : α -> Real} {l : Filter α}
  proof: tendsto_coe_nhds_top.trans Real.tendsto_toNNReal_atTop_iff

中文:
定理 tendsto_ofReal_nhds_top
  条件: {f : α -> 实数} {l : Filter α}
  证明: tendsto_coe_nhds_top.trans Real.tendsto_toNNReal_atTop_iff

Depends on / 依赖: Real.tendsto_toNNReal_atTop_iff, tendsto_coe_nhds_top, tendsto_coe_nhds_top.trans, tendsto_toNNReal_atTop_iff
-/
theorem tendsto_ofReal_nhds_top {f : α -> Real} {l : Filter α} :
    Tendsto (fun x => ENNReal.ofReal (f x)) l (𝓝 ∞) ↔ Tendsto f l atTop :=
  tendsto_coe_nhds_top.trans Real.tendsto_toNNReal_atTop_iff

/--
theorem `tendsto_ofReal_atTop` / 定理 `tendsto_ofReal_atTop`

English:
theorem tendsto_ofReal_atTop
  statement: Tendsto ENNReal.ofReal atTop (𝓝 ∞)
  proof: tendsto_ofReal_nhds_top.2 tendsto_id

中文:
定理 tendsto_ofReal_atTop
  结论: Tendsto ENN实数.of实数 atTop (𝓝 ∞)
  证明: tendsto_ofReal_nhds_top.2 tendsto_id

Depends on / 依赖: tendsto_id, tendsto_ofReal_nhds_top
-/
theorem tendsto_ofReal_atTop : Tendsto ENNReal.ofReal atTop (𝓝 ∞) :=
  tendsto_ofReal_nhds_top.2 tendsto_id

/--
theorem `nhds_zero` / 定理 `nhds_zero`

English:
theorem nhds_zero
  statement: 𝓝 (0 : Real>=0∞) = ⨅ (a) (_ : a != 0), 𝓟 (Iio a)
  proof: nhds_bot_order.trans by simp [pos_iff_ne_zero, Iio]

中文:
定理 nhds_zero
  结论: 𝓝 (0 : 实数>=0∞) = ⨅ (a) (_ : a != 0), 𝓟 (Iio a)
  证明: nhds_bot_order.trans by simp [pos_iff_ne_zero, Iio]

Depends on / 依赖: nhds_bot_order, nhds_bot_order.trans, pos_iff_ne_zero
-/
theorem nhds_zero : 𝓝 (0 : Real>=0∞) = ⨅ (a) (_ : a != 0), 𝓟 (Iio a) :=
nhds_bot_order.trans by simp [pos_iff_ne_zero, Iio]

/--
theorem `nhds_zero_basis` / 定理 `nhds_zero_basis`

English:
theorem nhds_zero_basis
  statement: (𝓝 (0 : Real>=0∞)).HasBasis (fun a : Real>=0∞ => 0 < a) fun a => Iio a
  proof: nhds_bot_basis

中文:
定理 nhds_zero_basis
  结论: (𝓝 (0 : 实数>=0∞)).HasBasis (fun a : 实数>=0∞ => 0 < a) fun a => Iio a
  证明: nhds_bot_basis

Depends on / 依赖: nhds_bot_basis
-/
theorem nhds_zero_basis : (𝓝 (0 : Real>=0∞)).HasBasis (fun a : Real>=0∞ => 0 < a) fun a => Iio a :=
  nhds_bot_basis

/--
theorem `nhds_zero_basis_Iic` / 定理 `nhds_zero_basis_Iic`

English:
theorem nhds_zero_basis_Iic
  statement: (𝓝 (0 : Real>=0∞)).HasBasis (fun a : Real>=0∞ => 0 < a) Iic
  proof: nhds_bot_basis_Iic

中文:
定理 nhds_zero_basis_Iic
  结论: (𝓝 (0 : 实数>=0∞)).HasBasis (fun a : 实数>=0∞ => 0 < a) Iic
  证明: nhds_bot_basis_Iic

Depends on / 依赖: nhds_bot_basis_Iic
-/
theorem nhds_zero_basis_Iic : (𝓝 (0 : Real>=0∞)).HasBasis (fun a : Real>=0∞ => 0 < a) Iic :=
  nhds_bot_basis_Iic

-- TODO: add a TC for `≠ ∞`?
@[instance]
/--
theorem `nhdsGT_coe_neBot` / 定理 `nhdsGT_coe_neBot`

English:
theorem nhdsGT_coe_neBot
  given: {r : Real>=0}
  statement: (𝓝[>] (r : Real>=0∞)).NeBot
  proof: nhdsGT_neBot_of_exists_gt ⟨∞, ENNReal.coe_lt_top⟩

中文:
定理 nhdsGT_coe_neBot
  条件: {r : 实数>=0}
  结论: (𝓝[>] (r : 实数>=0∞)).NeBot
  证明: nhdsGT_neBot_of_exists_gt ⟨∞, ENNReal.coe_lt_top⟩

Depends on / 依赖: ENNReal, ENNReal.coe_lt_top, coe_lt_top, nhdsGT_neBot_of_exists_gt
-/
theorem nhdsGT_coe_neBot {r : Real>=0} : (𝓝[>] (r : Real>=0∞)).NeBot :=
  nhdsGT_neBot_of_exists_gt ⟨∞, ENNReal.coe_lt_top⟩

/--
theorem `nhdsGT_zero_neBot` / 定理 `nhdsGT_zero_neBot`

English:
theorem nhdsGT_zero_neBot
  statement: (𝓝[>] (0 : Real>=0∞)).NeBot
  proof: nhdsGT_coe_neBot

中文:
定理 nhdsGT_zero_neBot
  结论: (𝓝[>] (0 : 实数>=0∞)).NeBot
  证明: nhdsGT_coe_neBot
-/
@[instance] theorem nhdsGT_zero_neBot : (𝓝[>] (0 : Real>=0∞)).NeBot := nhdsGT_coe_neBot

/--
theorem `nhdsGT_one_neBot` / 定理 `nhdsGT_one_neBot`

English:
theorem nhdsGT_one_neBot
  statement: (𝓝[>] (1 : Real>=0∞)).NeBot
  proof: nhdsGT_coe_neBot

中文:
定理 nhdsGT_one_neBot
  结论: (𝓝[>] (1 : 实数>=0∞)).NeBot
  证明: nhdsGT_coe_neBot
-/
@[instance] theorem nhdsGT_one_neBot : (𝓝[>] (1 : Real>=0∞)).NeBot := nhdsGT_coe_neBot

/--
theorem `nhdsGT_nat_neBot` / 定理 `nhdsGT_nat_neBot`

English:
theorem nhdsGT_nat_neBot
  given: (n : Nat)
  statement: (𝓝[>] (n : Real>=0∞)).NeBot
  proof: nhdsGT_coe_neBot

@[instance]

中文:
定理 nhdsGT_nat_neBot
  条件: (n : 自然数)
  结论: (𝓝[>] (n : 实数>=0∞)).NeBot
  证明: nhdsGT_coe_neBot

@[instance]
-/
@[instance] theorem nhdsGT_nat_neBot (n : Nat) : (𝓝[>] (n : Real>=0∞)).NeBot := nhdsGT_coe_neBot

@[instance]
/--
theorem `nhdsGT_ofNat_neBot` / 定理 `nhdsGT_ofNat_neBot`

English:
theorem nhdsGT_ofNat_neBot
  given: (n : Nat) [n.AtLeastTwo]
  statement: (𝓝[>] (OfNat.ofNat n : Real>=0∞)).NeBot
  proof: nhdsGT_coe_neBot

@[instance]

中文:
定理 nhdsGT_ofNat_neBot
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: (𝓝[>] (Of自然数.of自然数 n : 实数>=0∞)).NeBot
  证明: nhdsGT_coe_neBot

@[instance]

Depends on / 依赖: nhdsGT_coe_neBot
-/
theorem nhdsGT_ofNat_neBot (n : Nat) [n.AtLeastTwo] : (𝓝[>] (OfNat.ofNat n : Real>=0∞)).NeBot :=
  nhdsGT_coe_neBot

@[instance]
/--
theorem `nhdsLT_neBot` / 定理 `nhdsLT_neBot`

English:
theorem nhdsLT_neBot
  given: [NeZero x]
  statement: (𝓝[<] x).NeBot
  proof: nhdsLT_neBot_of_exists_lt ⟨0, NeZero.pos x⟩

中文:
定理 nhdsLT_neBot
  条件: [NeZero x]
  结论: (𝓝[<] x).NeBot
  证明: nhdsLT_neBot_of_exists_lt ⟨0, NeZero.pos x⟩

Depends on / 依赖: NeZero, NeZero.pos, nhdsLT_neBot_of_exists_lt
-/
theorem nhdsLT_neBot [NeZero x] : (𝓝[<] x).NeBot :=
  nhdsLT_neBot_of_exists_lt ⟨0, NeZero.pos x⟩

/--
theorem `hasBasis_nhds_of_ne_top'` / 定理 `hasBasis_nhds_of_ne_top'`

English:
theorem hasBasis_nhds_of_ne_top'
  given: (xt : x != ∞)
  proof: by
  rcases eq_zero_or_pos x with rfl | x0
  · simp_rw [zero_tsub, zero_add, ← bot_eq_zero, Icc_bot, ← bot_lt_iff_ne_bot]
    exact nhds_bot_basis_Iic
  · refine (nhds_basis_Ioo' ⟨_, x0⟩ ⟨_, xt.lt_top⟩).to_hasBasis ?_ fun ε ε0 => ?_
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      rcases exists_between (tsub_pos_

中文:
定理 hasBasis_nhds_of_ne_top'
  条件: (xt : x != ∞)
  证明: by
  rcases eq_zero_or_pos x with rfl | x0
  · simp_rw [zero_tsub, zero_add, ← bot_eq_zero, Icc_bot, ← bot_lt_iff_ne_bot]
    exact nhds_bot_basis_Iic
  · refine (nhds_basis_Ioo' ⟨_, x0⟩ ⟨_, xt.lt_top⟩).to_hasBasis ?_ fun ε ε0 => ?_
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      rcases exists_between (tsub_pos_

Depends on / 依赖: Icc_bot, Icc_subset_Ioo, bot_eq_zero, bot_lt_iff_ne_bot, coe_pos, eq_zero_or_pos, exists_between, lt_iff_exists_add_pos_lt, lt_min, lt_top, lt_tsub_comm, min_le, min_le_left, nhds_basis_Ioo, nhds_bot_basis_Iic, simp_rw, to_hasBasis, trans_lt, tsub_pos_of_lt, xt.lt_top
-/
theorem hasBasis_nhds_of_ne_top' (xt : x != ∞) :
    (𝓝 x).HasBasis (· != 0) (fun ε => Icc (x - ε) (x + ε)) := by
  rcases eq_zero_or_pos x with rfl | x0
  · simp_rw [zero_tsub, zero_add, ← bot_eq_zero, Icc_bot, ← bot_lt_iff_ne_bot]
    exact nhds_bot_basis_Iic
  · refine (nhds_basis_Ioo' ⟨_, x0⟩ ⟨_, xt.lt_top⟩).to_hasBasis ?_ fun ε ε0 => ?_
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      rcases exists_between (tsub_pos_of_lt ha) with ⟨ε, ε0, hε⟩
      rcases lt_iff_exists_add_pos_lt.1 hb with ⟨δ, δ0, hδ⟩
      refine ⟨min ε δ, (lt_min ε0 (coe_pos.2 δ0)).ne', Icc_subset_Ioo ?_ ?_⟩
      · exact lt_tsub_comm.2 ((min_le_left _ _).trans_lt hε)
      · grw [min_le_right]
        exact hδ
    · exact ⟨(x - ε, x + ε), ⟨ENNReal.sub_lt_self xt x0.ne' ε0,
        lt_add_right xt ε0⟩, Ioo_subset_Icc_self⟩

/--
theorem `hasBasis_nhds_of_ne_top` / 定理 `hasBasis_nhds_of_ne_top`

English:
theorem hasBasis_nhds_of_ne_top
  given: (xt : x != ∞)
  proof: by
  simpa only [pos_iff_ne_zero] using hasBasis_nhds_of_ne_top' xt

中文:
定理 hasBasis_nhds_of_ne_top
  条件: (xt : x != ∞)
  证明: by
  simpa only [pos_iff_ne_zero] using hasBasis_nhds_of_ne_top' xt

Depends on / 依赖: hasBasis_nhds_of_ne_top, pos_iff_ne_zero
-/
theorem hasBasis_nhds_of_ne_top (xt : x != ∞) :
    (𝓝 x).HasBasis (0 < ·) (fun ε => Icc (x - ε) (x + ε)) := by
  simpa only [pos_iff_ne_zero] using hasBasis_nhds_of_ne_top' xt

/--
theorem `Icc_mem_nhds` / 定理 `Icc_mem_nhds`

English:
theorem Icc_mem_nhds
  given: (xt : x != ∞) (ε0 : ε != 0)
  statement: Icc (x - ε) (x + ε) in 𝓝 x
  proof: (hasBasis_nhds_of_ne_top' xt).mem_of_mem ε0

中文:
定理 Icc_mem_nhds
  条件: (xt : x != ∞) (ε0 : ε != 0)
  结论: Icc (x - ε) (x + ε) in 𝓝 x
  证明: (hasBasis_nhds_of_ne_top' xt).mem_of_mem ε0

Depends on / 依赖: hasBasis_nhds_of_ne_top, mem_of_mem
-/
theorem Icc_mem_nhds (xt : x != ∞) (ε0 : ε != 0) : Icc (x - ε) (x + ε) in 𝓝 x :=
  (hasBasis_nhds_of_ne_top' xt).mem_of_mem ε0

/--
theorem `nhds_of_ne_top` / 定理 `nhds_of_ne_top`

English:
theorem nhds_of_ne_top
  given: (xt : x != ∞)
  statement: 𝓝 x = ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε))
  proof: (hasBasis_nhds_of_ne_top xt).eq_biInf

中文:
定理 nhds_of_ne_top
  条件: (xt : x != ∞)
  结论: 𝓝 x = ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε))
  证明: (hasBasis_nhds_of_ne_top xt).eq_biInf

Depends on / 依赖: eq_biInf, hasBasis_nhds_of_ne_top
-/
theorem nhds_of_ne_top (xt : x != ∞) : 𝓝 x = ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) :=
  (hasBasis_nhds_of_ne_top xt).eq_biInf

/--
theorem `biInf_le_nhds` / 定理 `biInf_le_nhds`

English:
theorem biInf_le_nhds
  statement: forall x : Real>=0∞, ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) <= 𝓝 x

中文:
定理 biInf_le_nhds
  结论: 对任意 x : 实数>=0∞, ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) <= 𝓝 x

Depends on / 依赖: Tendsto, Tendsto.mono_right, biInf_le_nhds, mono_right, tendsto_iInf, tendsto_principal
-/
theorem biInf_le_nhds : forall x : Real>=0∞, ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) <= 𝓝 x
| ∞ => iInf₂_le_of_le 1 one_pos by
    simpa only [← coe_one, top_sub_coe, top_add, Icc_self, principal_singleton] using pure_le_nhds _
  | (x : Real>=0) => (nhds_of_ne_top coe_ne_top).ge

/--
theorem `tendsto_nhds_of_Icc` / 定理 `tendsto_nhds_of_Icc`

English:
theorem tendsto_nhds_of_Icc
  statement: {f : Filter α} {u : α -> Real>=0∞} {a : Real>=0∞}
  proof: by
  refine Tendsto.mono_right ?_ (biInf_le_nhds _)
  simpa only [tendsto_iInf, tendsto_principal]

中文:
定理 tendsto_nhds_of_Icc
  结论: {f : Filter α} {u : α -> 实数>=0∞} {a : 实数>=0∞}
  证明: by
  refine Tendsto.mono_right ?_ (biInf_le_nhds _)
  simpa only [tendsto_iInf, tendsto_principal]
-/
protected theorem tendsto_nhds_of_Icc {f : Filter α} {u : α -> Real>=0∞} {a : Real>=0∞}
    (h : forall ε > 0, forallᶠ x in f, u x in Icc (a - ε) (a + ε)) : Tendsto u f (𝓝 a) := by
  refine Tendsto.mono_right ?_ (biInf_le_nhds _)
  simpa only [tendsto_iInf, tendsto_principal]

/--
theorem `tendsto_nhds` / 定理 `tendsto_nhds`

English:
theorem tendsto_nhds
  given: {f : Filter α} {u : α -> Real>=0∞} {a : Real>=0∞} (ha : a != ∞)
  proof: by
  simp only [nhds_of_ne_top ha, tendsto_iInf, tendsto_principal]

中文:
定理 tendsto_nhds
  条件: {f : Filter α} {u : α -> 实数>=0∞} {a : 实数>=0∞} (ha : a != ∞)
  证明: by
  simp only [nhds_of_ne_top ha, tendsto_iInf, tendsto_principal]
-/
protected theorem tendsto_nhds {f : Filter α} {u : α -> Real>=0∞} {a : Real>=0∞} (ha : a != ∞) :
    Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, u x in Icc (a - ε) (a + ε) := by
  simp only [nhds_of_ne_top ha, tendsto_iInf, tendsto_principal]

/--
theorem `tendsto_nhds_zero` / 定理 `tendsto_nhds_zero`

English:
theorem tendsto_nhds_zero
  given: {f : Filter α} {u : α -> Real>=0∞}
  proof: nhds_zero_basis_Iic.tendsto_right_iff

中文:
定理 tendsto_nhds_zero
  条件: {f : Filter α} {u : α -> 实数>=0∞}
  证明: nhds_zero_basis_Iic.tendsto_right_iff
-/
protected theorem tendsto_nhds_zero {f : Filter α} {u : α -> Real>=0∞} :
    Tendsto u f (𝓝 0) ↔ forall ε > 0, forallᶠ x in f, u x <= ε :=
  nhds_zero_basis_Iic.tendsto_right_iff

/--
theorem `tendsto_const_sub_nhds_zero_iff` / 定理 `tendsto_const_sub_nhds_zero_iff`

English:
theorem tendsto_const_sub_nhds_zero_iff
  statement: {l : Filter α} {f : α -> Real>=0∞} {a : Real>=0∞} (ha : a != ∞)
  proof: by
  rw [ENNReal.tendsto_nhds_zero]; rw [ENNReal.tendsto_nhds ha]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · filter_upwards [h ε hε] with n hn
    refine ⟨?_, (hfa n).trans (le_add_right le_rfl)⟩
    rw [tsub_le_iff_right] at hn ⊢
    rwa [add_comm]
  · filter_upwards [h ε hε] with n hn
    h

中文:
定理 tendsto_const_sub_nhds_zero_iff
  结论: {l : Filter α} {f : α -> 实数>=0∞} {a : 实数>=0∞} (ha : a != ∞)
  证明: by
  rw [ENNReal.tendsto_nhds_zero]; rw [ENNReal.tendsto_nhds ha]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · filter_upwards [h ε hε] with n hn
    refine ⟨?_, (hfa n).trans (le_add_right le_rfl)⟩
    rw [tsub_le_iff_right] at hn ⊢
    rwa [add_comm]
  · filter_upwards [h ε hε] with n hn
    h

Depends on / 依赖: ENNReal, ENNReal.tendsto_nhds, ENNReal.tendsto_nhds_zero, add_comm, filter_upwards, hN_left, le_add_right, le_rfl, tendsto_nhds, tendsto_nhds_zero, tsub_le_iff_right
-/
theorem tendsto_const_sub_nhds_zero_iff {l : Filter α} {f : α -> Real>=0∞} {a : Real>=0∞} (ha : a != ∞)
    (hfa : forall n, f n <= a) :
    Tendsto (fun n => a - f n) l (𝓝 0) ↔ Tendsto (fun n => f n) l (𝓝 a) := by
  rw [ENNReal.tendsto_nhds_zero]; rw [ENNReal.tendsto_nhds ha]
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · filter_upwards [h ε hε] with n hn
    refine ⟨?_, (hfa n).trans (le_add_right le_rfl)⟩
    rw [tsub_le_iff_right] at hn ⊢
    rwa [add_comm]
  · filter_upwards [h ε hε] with n hn
    have hN_left := hn.1
    rw [tsub_le_iff_right] at hN_left ⊢
    rwa [add_comm]

/--
theorem `tendsto_atTop` / 定理 `tendsto_atTop`

English:
theorem tendsto_atTop
  statement: [Nonempty β] [SemilatticeSup β] {f : β -> Real>=0∞} {a : Real>=0∞}
  proof: .trans (atTop_basis.tendsto_iff (hasBasis_nhds_of_ne_top ha)) (by simp only [true_and]; rfl)

中文:
定理 tendsto_atTop
  结论: [Nonempty β] [SemilatticeSup β] {f : β -> 实数>=0∞} {a : 实数>=0∞}
  证明: .trans (atTop_basis.tendsto_iff (hasBasis_nhds_of_ne_top ha)) (by simp only [true_and]; rfl)
-/
protected theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {f : β -> Real>=0∞} {a : Real>=0∞}
    (ha : a != ∞) : Tendsto f atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N, f n in Icc (a - ε) (a + ε) :=
  .trans (atTop_basis.tendsto_iff (hasBasis_nhds_of_ne_top ha)) (by simp only [true_and]; rfl)

/--
theorem `tendsto_atTop_zero` / 定理 `tendsto_atTop_zero`

English:
theorem tendsto_atTop_zero
  given: [Nonempty β] [SemilatticeSup β] {f : β -> Real>=0∞}
  proof: .trans (atTop_basis.tendsto_iff nhds_zero_basis_Iic) (by simp only [true_and]; rfl)

中文:
定理 tendsto_atTop_zero
  条件: [Nonempty β] [SemilatticeSup β] {f : β -> 实数>=0∞}
  证明: .trans (atTop_basis.tendsto_iff nhds_zero_basis_Iic) (by simp only [true_and]; rfl)
-/
protected theorem tendsto_atTop_zero [Nonempty β] [SemilatticeSup β] {f : β -> Real>=0∞} :
    Tendsto f atTop (𝓝 0) ↔ forall ε > 0, exists N, forall n >= N, f n <= ε :=
  .trans (atTop_basis.tendsto_iff nhds_zero_basis_Iic) (by simp only [true_and]; rfl)

/--
theorem `tendsto_atTop_zero_iff_le_of_antitone` / 定理 `tendsto_atTop_zero_iff_le_of_antitone`

English:
theorem tendsto_atTop_zero_iff_le_of_antitone
  statement: {β : Type*} [Nonempty β] [SemilatticeSup β]
  proof: by
  rw [ENNReal.tendsto_atTop_zero]
  refine ⟨fun h => fun ε hε => ?_, fun h => fun ε hε => ?_⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn n le_rfl⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, fun m hm => (hf hm).trans hn⟩

中文:
定理 tendsto_atTop_zero_iff_le_of_antitone
  结论: {β : 类型} [Nonempty β] [SemilatticeSup β]
  证明: by
  rw [ENNReal.tendsto_atTop_zero]
  refine ⟨fun h => fun ε hε => ?_, fun h => fun ε hε => ?_⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn n le_rfl⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, fun m hm => (hf hm).trans hn⟩

Depends on / 依赖: ENNReal, ENNReal.tendsto_atTop_zero, le_rfl, tendsto_atTop_zero
-/
theorem tendsto_atTop_zero_iff_le_of_antitone {β : Type*} [Nonempty β] [SemilatticeSup β]
    {f : β -> Real>=0∞} (hf : Antitone f) :
    Filter.Tendsto f Filter.atTop (𝓝 0) ↔ forall ε, 0 < ε -> exists n : β, f n <= ε := by
  rw [ENNReal.tendsto_atTop_zero]
  refine ⟨fun h => fun ε hε => ?_, fun h => fun ε hε => ?_⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn n le_rfl⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, fun m hm => (hf hm).trans hn⟩

/--
theorem `tendsto_atTop_zero_iff_lt_of_antitone` / 定理 `tendsto_atTop_zero_iff_lt_of_antitone`

English:
theorem tendsto_atTop_zero_iff_lt_of_antitone
  statement: {β : Type*} [Nonempty β] [SemilatticeSup β]
  proof: by
  rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone hf]
  constructor <;> intro h ε hε
  · obtain ⟨n, hn⟩ := h (min 1 (ε / 2))
      (lt_min_iff.mpr ⟨zero_lt_one, (ENNReal.div_pos_iff.mpr ⟨hε.ne', by finiteness⟩)⟩)
    · refine ⟨n, hn.trans_lt ?_⟩
      by_cases hε_top : ε = ∞
      · simp [hε_to

中文:
定理 tendsto_atTop_zero_iff_lt_of_antitone
  结论: {β : 类型} [Nonempty β] [SemilatticeSup β]
  证明: by
  rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone hf]
  constructor <;> intro h ε hε
  · obtain ⟨n, hn⟩ := h (min 1 (ε / 2))
      (lt_min_iff.mpr ⟨zero_lt_one, (ENNReal.div_pos_iff.mpr ⟨hε.ne', by finiteness⟩)⟩)
    · refine ⟨n, hn.trans_lt ?_⟩
      by_cases hε_top : ε = ∞
      · simp [hε_to

Depends on / 依赖: ENNReal, ENNReal.div_lt_iff, ENNReal.div_pos_iff.mpr, ENNReal.tendsto_atTop_zero_iff_le_of_antitone, Or.inr, conv_lhs, div_lt_iff, div_pos_iff, finiteness, hn.le, hn.trans_lt, lt_min_iff, lt_min_iff.mpr, min_le_right, mul_one, tendsto_atTop_zero_iff_le_of_antitone, trans_lt, zero_lt_one
-/
theorem tendsto_atTop_zero_iff_lt_of_antitone {β : Type*} [Nonempty β] [SemilatticeSup β]
    {f : β -> Real>=0∞} (hf : Antitone f) :
    Filter.Tendsto f Filter.atTop (𝓝 0) ↔ forall ε, 0 < ε -> exists n : β, f n < ε := by
  rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone hf]
  constructor <;> intro h ε hε
  · obtain ⟨n, hn⟩ := h (min 1 (ε / 2))
      (lt_min_iff.mpr ⟨zero_lt_one, (ENNReal.div_pos_iff.mpr ⟨hε.ne', by finiteness⟩)⟩)
    · refine ⟨n, hn.trans_lt ?_⟩
      by_cases hε_top : ε = ∞
      · simp [hε_top]
      refine (min_le_right _ _).trans_lt ?_
      rw [ENNReal.div_lt_iff (Or.inr hε.ne') (Or.inr hε_top)]
      conv_lhs => rw [← mul_one ε]
      gcongr; simp
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn.le⟩

/--
theorem `tendsto_sub` / 定理 `tendsto_sub`

English:
theorem tendsto_sub
  statement: forall {a b : Real>=0∞}, (a != ∞ ∨ b != ∞) ->

中文:
定理 tendsto_sub
  结论: 对任意 {a b : 实数>=0∞}, (a != ∞ ∨ b != ∞) ->

Depends on / 依赖: ENNReal, ENNReal.tendsto_sub, Tendsto, Tendsto.comp, hma.prodMk_nhds, prodMk_nhds, tendsto_sub
-/
theorem tendsto_sub : forall {a b : Real>=0∞}, (a != ∞ ∨ b != ∞) ->
    Tendsto (fun p : Real>=0∞ × Real>=0∞ => p.1 - p.2) (𝓝 (a, b)) (𝓝 (a - b))
  | ∞, ∞, h => by simp only [ne_eq, not_true_eq_false, or_self] at h
  | ∞, (b : Real>=0), _ => by
    rw [top_sub_coe]; rw [tendsto_nhds_top_iff_nnreal]
    refine fun x => ((lt_mem_nhds <| @coe_lt_top (b + 1 + x)).prod_nhds
      (ge_mem_nhds <| coe_lt_coe.2 <| lt_add_one b)).mono fun y hy => ?_
    grw [lt_tsub_iff_left, hy.2]
    exact hy.1
  | (a : Real>=0), ∞, _ => by
    rw [sub_top]
    refine (tendsto_pure.2 ?_).mono_right (pure_le_nhds _)
    exact ((gt_mem_nhds <| coe_lt_coe.2 <| lt_add_one a).prod_nhds
      (lt_mem_nhds <| @coe_lt_top (a + 1))).mono fun x hx =>
        tsub_eq_zero_iff_le.2 (hx.1.trans hx.2).le
  | (a : Real>=0), (b : Real>=0), _ => by
    simp only [nhds_coe_coe, tendsto_map'_iff, ← ENNReal.coe_sub, Function.comp_def, tendsto_coe]
    exact continuous_sub.tendsto (a, b)

/--
theorem `Tendsto.sub` / 定理 `Tendsto.sub`

English:
theorem Tendsto.sub
  statement: {f : Filter α} {ma : α -> Real>=0∞} {mb : α -> Real>=0∞} {a b : Real>=0∞}
  proof: show Tendsto ((fun p : Real>=0∞ × Real>=0∞ => p.1 - p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a - b)) from
    Tendsto.comp (ENNReal.tendsto_sub h) (hma.prodMk_nhds hmb)

中文:
定理 Tendsto.sub
  结论: {f : Filter α} {ma : α -> 实数>=0∞} {mb : α -> 实数>=0∞} {a b : 实数>=0∞}
  证明: show Tendsto ((fun p : Real>=0∞ × Real>=0∞ => p.1 - p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a - b)) from
    Tendsto.comp (ENNReal.tendsto_sub h) (hma.prodMk_nhds hmb)
-/
protected theorem Tendsto.sub {f : Filter α} {ma : α -> Real>=0∞} {mb : α -> Real>=0∞} {a b : Real>=0∞}
    (hma : Tendsto ma f (𝓝 a)) (hmb : Tendsto mb f (𝓝 b)) (h : a != ∞ ∨ b != ∞) :
    Tendsto (fun a => ma a - mb a) f (𝓝 (a - b)) :=
  show Tendsto ((fun p : Real>=0∞ × Real>=0∞ => p.1 - p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a - b)) from
    Tendsto.comp (ENNReal.tendsto_sub h) (hma.prodMk_nhds hmb)

/--
theorem `tendsto_mul` / 定理 `tendsto_mul`

English:
theorem tendsto_mul
  given: (ha : a != 0 ∨ b != ∞) (hb : b != 0 ∨ a != ∞)
  proof: by
  have ht : forall b : Real>=0∞, b != 0 ->
      Tendsto (fun p : Real>=0∞ × Real>=0∞ => p.1 * p.2) (𝓝 (∞, b)) (𝓝 ∞) := fun b hb => by
    refine tendsto_nhds_top_iff_nnreal.2 fun n => ?_
    rcases lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hb) with ⟨ε, hε, hεb⟩
    have : forallᶠ c : Real>=

中文:
定理 tendsto_mul
  条件: (ha : a != 0 ∨ b != ∞) (hb : b != 0 ∨ a != ∞)
  证明: by
  have ht : forall b : Real>=0∞, b != 0 ->
      Tendsto (fun p : Real>=0∞ × Real>=0∞ => p.1 * p.2) (𝓝 (∞, b)) (𝓝 ∞) := fun b hb => by
    refine tendsto_nhds_top_iff_nnreal.2 fun n => ?_
    rcases lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hb) with ⟨ε, hε, hεb⟩
    have : forallᶠ c : Real>=
-/
protected theorem tendsto_mul (ha : a != 0 ∨ b != ∞) (hb : b != 0 ∨ a != ∞) :
    Tendsto (fun p : Real>=0∞ × Real>=0∞ => p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) := by
  have ht : forall b : Real>=0∞, b != 0 ->
      Tendsto (fun p : Real>=0∞ × Real>=0∞ => p.1 * p.2) (𝓝 (∞, b)) (𝓝 ∞) := fun b hb => by
    refine tendsto_nhds_top_iff_nnreal.2 fun n => ?_
    rcases lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hb) with ⟨ε, hε, hεb⟩
    have : forallᶠ c : Real>=0∞ × Real>=0∞ in 𝓝 (∞, b), ↑n / ↑ε < c.1 ∧ ↑ε < c.2 :=
      (lt_mem_nhds <| div_lt_top coe_ne_top hε.ne').prod_nhds (lt_mem_nhds hεb)
    refine this.mono fun c hc => ?_
    exact (ENNReal.div_mul_cancel hε.ne' coe_ne_top).symm.trans_lt (mul_lt_mul hc.1 hc.2)
  induction a with
  | top => simp only [ne_eq, or_false, not_true_eq_false] at hb; simp [ht b hb, top_mul hb]
  | coe a =>
    induction b with
    | top =>
      simp only [ne_eq, or_false, not_true_eq_false] at ha
      simpa [Function.comp_def, mul_comm, mul_top ha]
        using (ht a ha).comp (continuous_swap.tendsto (ofNNReal a, ∞))
    | coe b =>
      simp only [nhds_coe_coe, ← coe_mul, tendsto_coe, tendsto_map'_iff, Function.comp_def,
        tendsto_mul]

/--
theorem `Tendsto.mul` / 定理 `Tendsto.mul`

English:
theorem Tendsto.mul
  statement: {f : Filter α} {ma : α -> Real>=0∞} {mb : α -> Real>=0∞} {a b : Real>=0∞}
  proof: show Tendsto ((fun p : Real>=0∞ × Real>=0∞ => p.1 * p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a * b)) from
    Tendsto.comp (ENNReal.tendsto_mul ha hb) (hma.prodMk_nhds hmb)

中文:
定理 Tendsto.mul
  结论: {f : Filter α} {ma : α -> 实数>=0∞} {mb : α -> 实数>=0∞} {a b : 实数>=0∞}
  证明: show Tendsto ((fun p : Real>=0∞ × Real>=0∞ => p.1 * p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a * b)) from
    Tendsto.comp (ENNReal.tendsto_mul ha hb) (hma.prodMk_nhds hmb)
-/
protected theorem Tendsto.mul {f : Filter α} {ma : α -> Real>=0∞} {mb : α -> Real>=0∞} {a b : Real>=0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a != 0 ∨ b != ∞) (hmb : Tendsto mb f (𝓝 b))
    (hb : b != 0 ∨ a != ∞) : Tendsto (fun a => ma a * mb a) f (𝓝 (a * b)) :=
  show Tendsto ((fun p : Real>=0∞ × Real>=0∞ => p.1 * p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a * b)) from
    Tendsto.comp (ENNReal.tendsto_mul ha hb) (hma.prodMk_nhds hmb)

/--
theorem `_root_.ContinuousOn.ennreal_mul` / 定理 `_root_.ContinuousOn.ennreal_mul`

English:
theorem _root_.ContinuousOn.ennreal_mul
  statement: [TopologicalSpace α] {f g : α -> Real>=0∞} {s : Set α}
  proof: fun x hx =>
  ENNReal.Tendsto.mul (hf x hx) (h₁ x hx) (hg x hx) (h₂ x hx)

中文:
定理 _root_.ContinuousOn.ennreal_mul
  结论: [TopologicalSpace α] {f g : α -> 实数>=0∞} {s : Set α}
  证明: fun x hx =>
  ENNReal.Tendsto.mul (hf x hx) (h₁ x hx) (hg x hx) (h₂ x hx)
-/
theorem _root_.ContinuousOn.ennreal_mul [TopologicalSpace α] {f g : α -> Real>=0∞} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₁ : forall x in s, f x != 0 ∨ g x != ∞)
    (h₂ : forall x in s, g x != 0 ∨ f x != ∞) : ContinuousOn (fun x => f x * g x) s := fun x hx =>
  ENNReal.Tendsto.mul (hf x hx) (h₁ x hx) (hg x hx) (h₂ x hx)

/--
theorem `_root_.Continuous.ennreal_mul` / 定理 `_root_.Continuous.ennreal_mul`

English:
theorem _root_.Continuous.ennreal_mul
  statement: [TopologicalSpace α] {f g : α -> Real>=0∞} (hf : Continuous f)
  proof: continuous_iff_continuousAt.2 fun x =>
    ENNReal.Tendsto.mul hf.continuousAt (h₁ x) hg.continuousAt (h₂ x)

中文:
定理 _root_.Continuous.ennreal_mul
  结论: [TopologicalSpace α] {f g : α -> 实数>=0∞} (hf : Continuous f)
  证明: continuous_iff_continuousAt.2 fun x =>
    ENNReal.Tendsto.mul hf.continuousAt (h₁ x) hg.continuousAt (h₂ x)

Depends on / 依赖: ENNReal, ENNReal.Tendsto.mul, Tendsto, continuousAt, continuous_iff_continuousAt, hf.continuousAt, hg.continuousAt
-/
theorem _root_.Continuous.ennreal_mul [TopologicalSpace α] {f g : α -> Real>=0∞} (hf : Continuous f)
    (hg : Continuous g) (h₁ : forall x, f x != 0 ∨ g x != ∞) (h₂ : forall x, g x != 0 ∨ f x != ∞) :
    Continuous fun x => f x * g x :=
  continuous_iff_continuousAt.2 fun x =>
    ENNReal.Tendsto.mul hf.continuousAt (h₁ x) hg.continuousAt (h₂ x)

/--
theorem `Tendsto.const_mul` / 定理 `Tendsto.const_mul`

English:
theorem Tendsto.const_mul
  statement: {f : Filter α} {m : α -> Real>=0∞} {a b : Real>=0∞}
  proof: by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds]) fun ha : a != 0 =>
    ENNReal.Tendsto.mul tendsto_const_nhds (Or.inl ha) hm hb

中文:
定理 Tendsto.const_mul
  结论: {f : Filter α} {m : α -> 实数>=0∞} {a b : 实数>=0∞}
  证明: by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds]) fun ha : a != 0 =>
    ENNReal.Tendsto.mul tendsto_const_nhds (Or.inl ha) hm hb
-/
protected theorem Tendsto.const_mul {f : Filter α} {m : α -> Real>=0∞} {a b : Real>=0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b != 0 ∨ a != ∞) : Tendsto (fun b => a * m b) f (𝓝 (a * b)) :=
  by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds]) fun ha : a != 0 =>
    ENNReal.Tendsto.mul tendsto_const_nhds (Or.inl ha) hm hb

/--
theorem `Tendsto.mul_const` / 定理 `Tendsto.mul_const`

English:
theorem Tendsto.mul_const
  statement: {f : Filter α} {m : α -> Real>=0∞} {a b : Real>=0∞}
  proof: by
  simpa only [mul_comm] using ENNReal.Tendsto.const_mul hm ha

中文:
定理 Tendsto.mul_const
  结论: {f : Filter α} {m : α -> 实数>=0∞} {a b : 实数>=0∞}
  证明: by
  simpa only [mul_comm] using ENNReal.Tendsto.const_mul hm ha
-/
protected theorem Tendsto.mul_const {f : Filter α} {m : α -> Real>=0∞} {a b : Real>=0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a != 0 ∨ b != ∞) : Tendsto (fun x => m x * b) f (𝓝 (a * b)) := by
  simpa only [mul_comm] using ENNReal.Tendsto.const_mul hm ha

/--
theorem `tendsto_finsetProd_of_ne_top` / 定理 `tendsto_finsetProd_of_ne_top`

English:
theorem tendsto_finsetProd_of_ne_top
  statement: {ι : Type*} {f : ι -> α -> Real>=0∞} {x : Filter α} {a : ι -> Real>=0∞}
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp [tendsto_const_nhds]
  | insert _ _ has IH =>
    simp only [Finset.prod_insert has]
    apply Tendsto.mul (h _ (Finset.mem_insert_self _ _))
    · right
      exact prod_ne_top fun i hi => h' _ (Finset.mem_insert_of_mem hi)


中文:
定理 tendsto_finsetProd_of_ne_top
  结论: {ι : 类型} {f : ι -> α -> 实数>=0∞} {x : Filter α} {a : ι -> 实数>=0∞}
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp [tendsto_const_nhds]
  | insert _ _ has IH =>
    simp only [Finset.prod_insert has]
    apply Tendsto.mul (h _ (Finset.mem_insert_self _ _))
    · right
      exact prod_ne_top fun i hi => h' _ (Finset.mem_insert_of_mem hi)


Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.prod_insert, Or.inr, Tendsto, Tendsto.mul, classical, insert, mem_insert_of_mem, mem_insert_self, prod_insert, prod_ne_top, tendsto_const_nhds
-/
theorem tendsto_finsetProd_of_ne_top {ι : Type*} {f : ι -> α -> Real>=0∞} {x : Filter α} {a : ι -> Real>=0∞}
    (s : Finset ι) (h : forall i in s, Tendsto (f i) x (𝓝 (a i))) (h' : forall i in s, a i != ∞) :
    Tendsto (fun b => ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) := by
  classical
  induction s using Finset.induction with
  | empty => simp [tendsto_const_nhds]
  | insert _ _ has IH =>
    simp only [Finset.prod_insert has]
    apply Tendsto.mul (h _ (Finset.mem_insert_self _ _))
    · right
      exact prod_ne_top fun i hi => h' _ (Finset.mem_insert_of_mem hi)
    · exact IH (fun i hi => h _ (Finset.mem_insert_of_mem hi)) fun i hi =>
        h' _ (Finset.mem_insert_of_mem hi)
    · exact Or.inr (h' _ (Finset.mem_insert_self _ _))

@[deprecated (since := "2026-04-08")]
alias tendsto_finset_prod_of_ne_top := tendsto_finsetProd_of_ne_top

/--
theorem `continuousAt_const_mul` / 定理 `continuousAt_const_mul`

English:
theorem continuousAt_const_mul
  given: {a b : Real>=0∞} (h : a != ∞ ∨ b != 0)
  proof: Tendsto.const_mul tendsto_id h.symm

中文:
定理 continuousAt_const_mul
  条件: {a b : 实数>=0∞} (h : a != ∞ ∨ b != 0)
  证明: Tendsto.const_mul tendsto_id h.symm
-/
protected theorem continuousAt_const_mul {a b : Real>=0∞} (h : a != ∞ ∨ b != 0) :
    ContinuousAt (a * ·) b :=
  Tendsto.const_mul tendsto_id h.symm

/--
theorem `continuousAt_mul_const` / 定理 `continuousAt_mul_const`

English:
theorem continuousAt_mul_const
  given: {a b : Real>=0∞} (h : a != ∞ ∨ b != 0)
  proof: Tendsto.mul_const tendsto_id h.symm

@[fun_prop]

中文:
定理 continuousAt_mul_const
  条件: {a b : 实数>=0∞} (h : a != ∞ ∨ b != 0)
  证明: Tendsto.mul_const tendsto_id h.symm

@[fun_prop]
-/
protected theorem continuousAt_mul_const {a b : Real>=0∞} (h : a != ∞ ∨ b != 0) :
    ContinuousAt (fun x => x * a) b :=
  Tendsto.mul_const tendsto_id h.symm

@[fun_prop]
/--
theorem `continuous_const_mul` / 定理 `continuous_const_mul`

English:
theorem continuous_const_mul
  given: {a : Real>=0∞} (ha : a != ∞)
  statement: Continuous (a * ·)
  proof: continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_const_mul (Or.inl ha)

@[fun_prop]

中文:
定理 continuous_const_mul
  条件: {a : 实数>=0∞} (ha : a != ∞)
  结论: Continuous (a * ·)
  证明: continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_const_mul (Or.inl ha)

@[fun_prop]
-/
protected theorem continuous_const_mul {a : Real>=0∞} (ha : a != ∞) : Continuous (a * ·) :=
  continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_const_mul (Or.inl ha)

@[fun_prop]
/--
theorem `continuous_mul_const` / 定理 `continuous_mul_const`

English:
theorem continuous_mul_const
  given: {a : Real>=0∞} (ha : a != ∞)
  statement: Continuous fun x => x * a
  proof: continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_mul_const (Or.inl ha)

@[fun_prop]

中文:
定理 continuous_mul_const
  条件: {a : 实数>=0∞} (ha : a != ∞)
  结论: Continuous fun x => x * a
  证明: continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_mul_const (Or.inl ha)

@[fun_prop]
-/
protected theorem continuous_mul_const {a : Real>=0∞} (ha : a != ∞) : Continuous fun x => x * a :=
  continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_mul_const (Or.inl ha)

@[fun_prop]
/--
theorem `continuous_div_const` / 定理 `continuous_div_const`

English:
theorem continuous_div_const
  given: (c : Real>=0∞) (c_ne_zero : c != 0)
  proof: ENNReal.continuous_mul_const ENNReal.inv_ne_top.2 c_ne_zero

@[continuity, fun_prop]

中文:
定理 continuous_div_const
  条件: (c : 实数>=0∞) (c_ne_zero : c != 0)
  证明: ENNReal.continuous_mul_const ENNReal.inv_ne_top.2 c_ne_zero

@[continuity, fun_prop]
-/
protected theorem continuous_div_const (c : Real>=0∞) (c_ne_zero : c != 0) :
    Continuous fun x : Real>=0∞ => x / c :=
ENNReal.continuous_mul_const ENNReal.inv_ne_top.2 c_ne_zero

@[continuity, fun_prop]
/--
theorem `continuous_pow` / 定理 `continuous_pow`

English:
theorem continuous_pow
  given: (n : Nat)
  statement: Continuous fun a : Real>=0∞ => a ^ n
  proof: by
  induction n with
  | zero => simp [continuous_const]
  | succ n IH =>
    simp_rw [pow_add, pow_one, continuous_iff_continuousAt]
    intro x
    refine ENNReal.Tendsto.mul (IH.tendsto _) ?_ tendsto_id ?_ <;> by_cases H : x = 0
    · simp only [H, zero_ne_top, Ne, or_true, not_false_iff]
    · 

中文:
定理 continuous_pow
  条件: (n : 自然数)
  结论: Continuous fun a : 实数>=0∞ => a ^ n
  证明: by
  induction n with
  | zero => simp [continuous_const]
  | succ n IH =>
    simp_rw [pow_add, pow_one, continuous_iff_continuousAt]
    intro x
    refine ENNReal.Tendsto.mul (IH.tendsto _) ?_ tendsto_id ?_ <;> by_cases H : x = 0
    · simp only [H, zero_ne_top, Ne, or_true, not_false_iff]
    · 
-/
protected theorem continuous_pow (n : Nat) : Continuous fun a : Real>=0∞ => a ^ n := by
  induction n with
  | zero => simp [continuous_const]
  | succ n IH =>
    simp_rw [pow_add, pow_one, continuous_iff_continuousAt]
    intro x
    refine ENNReal.Tendsto.mul (IH.tendsto _) ?_ tendsto_id ?_ <;> by_cases H : x = 0
    · simp only [H, zero_ne_top, Ne, or_true, not_false_iff]
    · exact Or.inl fun h => H (eq_zero_of_pow_eq_zero h)
    · simp only [H, pow_eq_top_iff, zero_ne_top, false_or, not_true, Ne,
        not_false_iff, false_and]
    · simp only [H, true_or, Ne, not_false_iff]

/--
theorem `continuousOn_sub` / 定理 `continuousOn_sub`

English:
theorem continuousOn_sub
  proof: by
  rw [ContinuousOn]
  rintro ⟨x, y⟩ hp
  simp only [Ne, Set.mem_ofPred_eq, Prod.mk_inj] at hp
  exact tendsto_nhdsWithin_of_tendsto_nhds (tendsto_sub (not_and_or.mp hp))

中文:
定理 continuousOn_sub
  证明: by
  rw [ContinuousOn]
  rintro ⟨x, y⟩ hp
  simp only [Ne, Set.mem_ofPred_eq, Prod.mk_inj] at hp
  exact tendsto_nhdsWithin_of_tendsto_nhds (tendsto_sub (not_and_or.mp hp))

Depends on / 依赖: ContinuousOn, Prod.mk_inj, Set.mem_ofPred_eq, mem_ofPred_eq, mk_inj, not_and_or, not_and_or.mp, tendsto_nhdsWithin_of_tendsto_nhds, tendsto_sub
-/
theorem continuousOn_sub :
    ContinuousOn (fun p : Real>=0∞ × Real>=0∞ => p.fst - p.snd) { p : Real>=0∞ × Real>=0∞ | p != ⟨∞, ∞⟩ } := by
  rw [ContinuousOn]
  rintro ⟨x, y⟩ hp
  simp only [Ne, Set.mem_ofPred_eq, Prod.mk_inj] at hp
  exact tendsto_nhdsWithin_of_tendsto_nhds (tendsto_sub (not_and_or.mp hp))

/--
theorem `continuous_sub_left` / 定理 `continuous_sub_left`

English:
theorem continuous_sub_left
  given: {a : Real>=0∞} (a_ne_top : a != ∞)
  statement: Continuous (a - ·)
  proof: by
  change Continuous (Function.uncurry Sub.sub ∘ (a, ·))
  refine continuousOn_sub.comp_continuous (.prodMk_right a) fun x => ?_
  simp only [a_ne_top, Ne, mem_ofPred_eq, Prod.mk_inj, false_and, not_false_iff]

中文:
定理 continuous_sub_left
  条件: {a : 实数>=0∞} (a_ne_top : a != ∞)
  结论: Continuous (a - ·)
  证明: by
  change Continuous (Function.uncurry Sub.sub ∘ (a, ·))
  refine continuousOn_sub.comp_continuous (.prodMk_right a) fun x => ?_
  simp only [a_ne_top, Ne, mem_ofPred_eq, Prod.mk_inj, false_and, not_false_iff]

Depends on / 依赖: Continuous, Function, Function.uncurry, Prod.mk_inj, Sub.sub, a_ne_top, comp_continuous, continuousOn_sub, continuousOn_sub.comp_continuous, false_and, mem_ofPred_eq, mk_inj, not_false_iff, prodMk_right, uncurry
-/
theorem continuous_sub_left {a : Real>=0∞} (a_ne_top : a != ∞) : Continuous (a - ·) := by
  change Continuous (Function.uncurry Sub.sub ∘ (a, ·))
  refine continuousOn_sub.comp_continuous (.prodMk_right a) fun x => ?_
  simp only [a_ne_top, Ne, mem_ofPred_eq, Prod.mk_inj, false_and, not_false_iff]

/--
theorem `continuous_nnreal_sub` / 定理 `continuous_nnreal_sub`

English:
theorem continuous_nnreal_sub
  given: {a : Real>=0}
  statement: Continuous fun x : Real>=0∞ => (a : Real>=0∞) - x
  proof: continuous_sub_left coe_ne_top

中文:
定理 continuous_nnreal_sub
  条件: {a : 实数>=0}
  结论: Continuous fun x : 实数>=0∞ => (a : 实数>=0∞) - x
  证明: continuous_sub_left coe_ne_top

Depends on / 依赖: coe_ne_top, continuous_sub_left
-/
theorem continuous_nnreal_sub {a : Real>=0} : Continuous fun x : Real>=0∞ => (a : Real>=0∞) - x :=
  continuous_sub_left coe_ne_top

/--
theorem `continuousOn_sub_left` / 定理 `continuousOn_sub_left`

English:
theorem continuousOn_sub_left
  given: (a : Real>=0∞)
  statement: ContinuousOn (a - ·) { x : Real>=0∞ | x != ∞ }
  proof: by
  rw [show (fun x => a - x) = (fun p : Real>=0∞ × Real>=0∞ => p.fst - p.snd) ∘ fun x => ⟨a]; rw [x⟩ by rfl]
  apply continuousOn_sub.comp (by fun_prop)
  rintro _ h (_ | _)
  exact h none_eq_top

中文:
定理 continuousOn_sub_left
  条件: (a : 实数>=0∞)
  结论: ContinuousOn (a - ·) { x : 实数>=0∞ | x != ∞ }
  证明: by
  rw [show (fun x => a - x) = (fun p : Real>=0∞ × Real>=0∞ => p.fst - p.snd) ∘ fun x => ⟨a]; rw [x⟩ by rfl]
  apply continuousOn_sub.comp (by fun_prop)
  rintro _ h (_ | _)
  exact h none_eq_top

Depends on / 依赖: continuousOn_sub, continuousOn_sub.comp, fun_prop, none_eq_top, p.fst, p.snd
-/
theorem continuousOn_sub_left (a : Real>=0∞) : ContinuousOn (a - ·) { x : Real>=0∞ | x != ∞ } := by
  rw [show (fun x => a - x) = (fun p : Real>=0∞ × Real>=0∞ => p.fst - p.snd) ∘ fun x => ⟨a]; rw [x⟩ by rfl]
  apply continuousOn_sub.comp (by fun_prop)
  rintro _ h (_ | _)
  exact h none_eq_top

/--
theorem `continuous_sub_right` / 定理 `continuous_sub_right`

English:
theorem continuous_sub_right
  given: (a : Real>=0∞)
  statement: Continuous fun x : Real>=0∞ => x - a
  proof: by
  by_cases a_infty : a = ∞
  · simp [a_infty, continuous_const, tsub_eq_zero_of_le]
  · rw [show (fun x => x - a) = (fun p : Real>=0∞ × Real>=0∞ => p.fst - p.snd) ∘ fun x => ⟨x, a⟩ by rfl]
    apply continuousOn_sub.comp_continuous (by fun_prop)
    intro x
    simp only [a_infty, Ne, mem_ofPred_

中文:
定理 continuous_sub_right
  条件: (a : 实数>=0∞)
  结论: Continuous fun x : 实数>=0∞ => x - a
  证明: by
  by_cases a_infty : a = ∞
  · simp [a_infty, continuous_const, tsub_eq_zero_of_le]
  · rw [show (fun x => x - a) = (fun p : Real>=0∞ × Real>=0∞ => p.fst - p.snd) ∘ fun x => ⟨x, a⟩ by rfl]
    apply continuousOn_sub.comp_continuous (by fun_prop)
    intro x
    simp only [a_infty, Ne, mem_ofPred_

Depends on / 依赖: Prod.mk_inj, a_infty, and_false, comp_continuous, continuousOn_sub, continuousOn_sub.comp_continuous, continuous_const, fun_prop, mem_ofPred_eq, mk_inj, not_false_iff, p.fst, p.snd, tsub_eq_zero_of_le
-/
theorem continuous_sub_right (a : Real>=0∞) : Continuous fun x : Real>=0∞ => x - a := by
  by_cases a_infty : a = ∞
  · simp [a_infty, continuous_const, tsub_eq_zero_of_le]
  · rw [show (fun x => x - a) = (fun p : Real>=0∞ × Real>=0∞ => p.fst - p.snd) ∘ fun x => ⟨x, a⟩ by rfl]
    apply continuousOn_sub.comp_continuous (by fun_prop)
    intro x
    simp only [a_infty, Ne, mem_ofPred_eq, Prod.mk_inj, and_false, not_false_iff]

/--
theorem `Tendsto.pow` / 定理 `Tendsto.pow`

English:
theorem Tendsto.pow
  statement: {f : Filter α} {m : α -> Real>=0∞} {a : Real>=0∞} {n : Nat}
  proof: ((ENNReal.continuous_pow n).tendsto a).comp hm

中文:
定理 Tendsto.pow
  结论: {f : Filter α} {m : α -> 实数>=0∞} {a : 实数>=0∞} {n : 自然数}
  证明: ((ENNReal.continuous_pow n).tendsto a).comp hm
-/
protected theorem Tendsto.pow {f : Filter α} {m : α -> Real>=0∞} {a : Real>=0∞} {n : Nat}
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ n) f (𝓝 (a ^ n)) :=
  ((ENNReal.continuous_pow n).tendsto a).comp hm

/--
theorem `le_of_forall_lt_one_mul_le` / 定理 `le_of_forall_lt_one_mul_le`

English:
theorem le_of_forall_lt_one_mul_le
  given: {x y : Real>=0∞} (h : forall a < 1, a * x <= y)
  statement: x <= y
  proof: by
  have : Tendsto (· * x) (𝓝[<] 1) (𝓝 (1 * x)) :=
    (ENNReal.continuousAt_mul_const (Or.inr one_ne_zero)).mono_left inf_le_left
  rw [one_mul] at this
  exact le_of_tendsto this (eventually_nhdsWithin_iff.2 <| Eventually.of_forall h)

中文:
定理 le_of_forall_lt_one_mul_le
  条件: {x y : 实数>=0∞} (h : 对任意 a < 1, a * x <= y)
  结论: x <= y
  证明: by
  have : Tendsto (· * x) (𝓝[<] 1) (𝓝 (1 * x)) :=
    (ENNReal.continuousAt_mul_const (Or.inr one_ne_zero)).mono_left inf_le_left
  rw [one_mul] at this
  exact le_of_tendsto this (eventually_nhdsWithin_iff.2 <| Eventually.of_forall h)

Depends on / 依赖: ENNReal, ENNReal.continuousAt_mul_const, Eventually, Eventually.of_forall, Or.inr, Tendsto, continuousAt_mul_const, eventually_nhdsWithin_iff, inf_le_left, le_of_tendsto, mono_left, of_forall, one_mul, one_ne_zero
-/
theorem le_of_forall_lt_one_mul_le {x y : Real>=0∞} (h : forall a < 1, a * x <= y) : x <= y := by
  have : Tendsto (· * x) (𝓝[<] 1) (𝓝 (1 * x)) :=
    (ENNReal.continuousAt_mul_const (Or.inr one_ne_zero)).mono_left inf_le_left
  rw [one_mul] at this
  exact le_of_tendsto this (eventually_nhdsWithin_iff.2 <| Eventually.of_forall h)

/--
theorem `inv_limsup` / 定理 `inv_limsup`

English:
theorem inv_limsup
  given: {ι : Sort _} {x : ι -> Real>=0∞} {l : Filter ι}
  proof: OrderIso.invENNReal.limsup_apply

中文:
定理 inv_limsup
  条件: {ι : Sort _} {x : ι -> 实数>=0∞} {l : Filter ι}
  证明: OrderIso.invENNReal.limsup_apply

Depends on / 依赖: OrderIso, OrderIso.invENNReal.limsup_apply, invENNReal, limsup_apply
-/
theorem inv_limsup {ι : Sort _} {x : ι -> Real>=0∞} {l : Filter ι} :
    (limsup x l)⁻¹ = liminf (fun i => (x i)⁻¹) l :=
  OrderIso.invENNReal.limsup_apply

/--
theorem `inv_liminf` / 定理 `inv_liminf`

English:
theorem inv_liminf
  given: {ι : Sort _} {x : ι -> Real>=0∞} {l : Filter ι}
  proof: OrderIso.invENNReal.liminf_apply

@[fun_prop]

中文:
定理 inv_liminf
  条件: {ι : Sort _} {x : ι -> 实数>=0∞} {l : Filter ι}
  证明: OrderIso.invENNReal.liminf_apply

@[fun_prop]

Depends on / 依赖: OrderIso, OrderIso.invENNReal.liminf_apply, invENNReal, liminf_apply
-/
theorem inv_liminf {ι : Sort _} {x : ι -> Real>=0∞} {l : Filter ι} :
    (liminf x l)⁻¹ = limsup (fun i => (x i)⁻¹) l :=
  OrderIso.invENNReal.liminf_apply

@[fun_prop]
/--
theorem `continuous_zpow` / 定理 `continuous_zpow`

English:
theorem continuous_zpow
  statement: forall n : Int, Continuous (· ^ n : Real>=0∞ -> Real>=0∞)
  proof: tendsto_inv_iff

中文:
定理 continuous_zpow
  结论: 对任意 n : 整数, Continuous (· ^ n : 实数>=0∞ -> 实数>=0∞)
  证明: tendsto_inv_iff
-/
protected theorem continuous_zpow : forall n : Int, Continuous (· ^ n : Real>=0∞ -> Real>=0∞)
  | (n : Nat) => mod_cast ENNReal.continuous_pow n
  | .negSucc n => by simpa using (ENNReal.continuous_pow _).fun_inv

@[deprecated (since := "2026-01-15")] protected alias tendsto_inv_iff := tendsto_inv_iff

/--
theorem `Tendsto.div` / 定理 `Tendsto.div`

English:
theorem Tendsto.div
  statement: {f : Filter α} {ma : α -> Real>=0∞} {mb : α -> Real>=0∞} {a b : Real>=0∞}
  proof: by
  apply Tendsto.mul hma _ (tendsto_inv_iff.2 hmb) _ <;> simp [ha, hb]

中文:
定理 Tendsto.div
  结论: {f : Filter α} {ma : α -> 实数>=0∞} {mb : α -> 实数>=0∞} {a b : 实数>=0∞}
  证明: by
  apply Tendsto.mul hma _ (tendsto_inv_iff.2 hmb) _ <;> simp [ha, hb]
-/
protected theorem Tendsto.div {f : Filter α} {ma : α -> Real>=0∞} {mb : α -> Real>=0∞} {a b : Real>=0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a != 0 ∨ b != 0) (hmb : Tendsto mb f (𝓝 b))
    (hb : b != ∞ ∨ a != ∞) : Tendsto (fun a => ma a / mb a) f (𝓝 (a / b)) := by
  apply Tendsto.mul hma _ (tendsto_inv_iff.2 hmb) _ <;> simp [ha, hb]

/--
theorem `Tendsto.const_div` / 定理 `Tendsto.const_div`

English:
theorem Tendsto.const_div
  statement: {f : Filter α} {m : α -> Real>=0∞} {a b : Real>=0∞}
  proof: by
  apply Tendsto.const_mul (tendsto_inv_iff.2 hm)
  simp [hb]

中文:
定理 Tendsto.const_div
  结论: {f : Filter α} {m : α -> 实数>=0∞} {a b : 实数>=0∞}
  证明: by
  apply Tendsto.const_mul (tendsto_inv_iff.2 hm)
  simp [hb]
-/
protected theorem Tendsto.const_div {f : Filter α} {m : α -> Real>=0∞} {a b : Real>=0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b != ∞ ∨ a != ∞) : Tendsto (fun b => a / m b) f (𝓝 (a / b)) := by
  apply Tendsto.const_mul (tendsto_inv_iff.2 hm)
  simp [hb]

/--
theorem `Tendsto.div_const` / 定理 `Tendsto.div_const`

English:
theorem Tendsto.div_const
  statement: {f : Filter α} {m : α -> Real>=0∞} {a b : Real>=0∞}
  proof: by
  apply Tendsto.mul_const hm
  simp [ha]

中文:
定理 Tendsto.div_const
  结论: {f : Filter α} {m : α -> 实数>=0∞} {a b : 实数>=0∞}
  证明: by
  apply Tendsto.mul_const hm
  simp [ha]
-/
protected theorem Tendsto.div_const {f : Filter α} {m : α -> Real>=0∞} {a b : Real>=0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a != 0 ∨ b != 0) : Tendsto (fun x => m x / b) f (𝓝 (a / b)) := by
  apply Tendsto.mul_const hm
  simp [ha]

/--
theorem `tendsto_inv_nat_nhds_zero` / 定理 `tendsto_inv_nat_nhds_zero`

English:
theorem tendsto_inv_nat_nhds_zero
  statement: Tendsto (fun n : Nat => (n : Real>=0∞)⁻¹) atTop (𝓝 0)
  proof: ENNReal.inv_top ▸ tendsto_inv_iff.2 tendsto_nat_nhds_top

中文:
定理 tendsto_inv_nat_nhds_zero
  结论: Tendsto (fun n : 自然数 => (n : 实数>=0∞)⁻¹) atTop (𝓝 0)
  证明: ENNReal.inv_top ▸ tendsto_inv_iff.2 tendsto_nat_nhds_top
-/
protected theorem tendsto_inv_nat_nhds_zero : Tendsto (fun n : Nat => (n : Real>=0∞)⁻¹) atTop (𝓝 0) :=
  ENNReal.inv_top ▸ tendsto_inv_iff.2 tendsto_nat_nhds_top

/--
theorem `tendsto_coe_sub` / 定理 `tendsto_coe_sub`

English:
theorem tendsto_coe_sub
  given: {b : Real>=0∞}
  proof: continuous_nnreal_sub.tendsto _

中文:
定理 tendsto_coe_sub
  条件: {b : 实数>=0∞}
  证明: continuous_nnreal_sub.tendsto _
-/
protected theorem tendsto_coe_sub {b : Real>=0∞} :
    Tendsto (fun b : Real>=0∞ => ↑r - b) (𝓝 b) (𝓝 (↑r - b)) :=
  continuous_nnreal_sub.tendsto _

/--
theorem `exists_countable_dense_no_zero_top` / 定理 `exists_countable_dense_no_zero_top`

English:
theorem exists_countable_dense_no_zero_top
  proof: by
  obtain ⟨s, s_count, s_dense, hs⟩ :
    exists s : Set Real>=0∞, s.Countable ∧ Dense s ∧ (forall x, IsBot x -> x ∉ s) ∧ forall x, IsTop x -> x ∉ s :=
    exists_countable_dense_no_bot_top Real>=0∞
  exact ⟨s, s_count, s_dense, fun h => hs.1 0 (by simp) h, fun h => hs.2 ∞ (by simp) h⟩

中文:
定理 exists_countable_dense_no_zero_top
  证明: by
  obtain ⟨s, s_count, s_dense, hs⟩ :
    exists s : Set Real>=0∞, s.Countable ∧ Dense s ∧ (forall x, IsBot x -> x ∉ s) ∧ forall x, IsTop x -> x ∉ s :=
    exists_countable_dense_no_bot_top Real>=0∞
  exact ⟨s, s_count, s_dense, fun h => hs.1 0 (by simp) h, fun h => hs.2 ∞ (by simp) h⟩

Depends on / 依赖: Countable, exists_countable_dense_no_bot_top, s.Countable, s_count, s_dense
-/
theorem exists_countable_dense_no_zero_top :
    exists s : Set Real>=0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s := by
  obtain ⟨s, s_count, s_dense, hs⟩ :
    exists s : Set Real>=0∞, s.Countable ∧ Dense s ∧ (forall x, IsBot x -> x ∉ s) ∧ forall x, IsTop x -> x ∉ s :=
    exists_countable_dense_no_bot_top Real>=0∞
  exact ⟨s, s_count, s_dense, fun h => hs.1 0 (by simp) h, fun h => hs.2 ∞ (by simp) h⟩

end TopologicalSpace

section Liminf

/--
theorem `exists_frequently_lt_of_liminf_ne_top` / 定理 `exists_frequently_lt_of_liminf_ne_top`

English:
theorem exists_frequently_lt_of_liminf_ne_top
  statement: {ι : Type*} {l : Filter ι} {x : ι -> Real}
  proof: by
  by_contra! h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h r] with i hi using hi.trans (le_abs_self (x i))

中文:
定理 exists_frequently_lt_of_liminf_ne_top
  结论: {ι : 类型} {l : Filter ι} {x : ι -> 实数}
  证明: by
  by_contra! h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h r] with i hi using hi.trans (le_abs_self (x i))

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.eq_top_of_forall_nnreal_le, coe_le_coe, eq_top_of_forall_nnreal_le, eventually_map, filter_upwards, hi.trans, isBoundedDefault, le_abs_self, le_limsInf_of_le
-/
theorem exists_frequently_lt_of_liminf_ne_top {ι : Type*} {l : Filter ι} {x : ι -> Real}
    (hx : liminf (fun n => (Real.nnabs (x n) : Real>=0∞)) l != ∞) : exists R, existsᶠ n in l, x n < R := by
  by_contra! h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h r] with i hi using hi.trans (le_abs_self (x i))

/--
theorem `exists_frequently_lt_of_liminf_ne_top'` / 定理 `exists_frequently_lt_of_liminf_ne_top'`

English:
theorem exists_frequently_lt_of_liminf_ne_top'
  statement: {ι : Type*} {l : Filter ι} {x : ι -> Real}
  proof: by
  by_contra! h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h (-r)] with i hi using (le_neg.1 hi).trans (neg_le_abs _)

中文:
定理 exists_frequently_lt_of_liminf_ne_top'
  结论: {ι : 类型} {l : Filter ι} {x : ι -> 实数}
  证明: by
  by_contra! h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h (-r)] with i hi using (le_neg.1 hi).trans (neg_le_abs _)

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.eq_top_of_forall_nnreal_le, coe_le_coe, eq_top_of_forall_nnreal_le, eventually_map, filter_upwards, isBoundedDefault, le_limsInf_of_le, le_neg, neg_le_abs
-/
theorem exists_frequently_lt_of_liminf_ne_top' {ι : Type*} {l : Filter ι} {x : ι -> Real}
    (hx : liminf (fun n => (Real.nnabs (x n) : Real>=0∞)) l != ∞) : exists R, existsᶠ n in l, R < x n := by
  by_contra! h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h (-r)] with i hi using (le_neg.1 hi).trans (neg_le_abs _)

/--
theorem `exists_upcrossings_of_not_bounded_under` / 定理 `exists_upcrossings_of_not_bounded_under`

English:
theorem exists_upcrossings_of_not_bounded_under
  statement: {ι : Type*} {l : Filter ι} {x : ι -> Real}
  proof: by
  rw [isBoundedUnder_le_abs]; rw [not_and_or] at hbdd
  obtain hbdd | hbdd := hbdd
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top hf
    obtain ⟨q, hq⟩ := exists_rat_gt R
    refine ⟨q, q + 1, (lt_add_iff_pos_right _).2 zero_lt_one, ?_, ?_⟩
    · refine fun hcon => hR ?_
      filter

中文:
定理 exists_upcrossings_of_not_bounded_under
  结论: {ι : 类型} {l : Filter ι} {x : ι -> 实数}
  证明: by
  rw [isBoundedUnder_le_abs]; rw [not_and_or] at hbdd
  obtain hbdd | hbdd := hbdd
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top hf
    obtain ⟨q, hq⟩ := exists_rat_gt R
    refine ⟨q, q + 1, (lt_add_iff_pos_right _).2 zero_lt_one, ?_, ?_⟩
    · refine fun hcon => hR ?_
      filter

Depends on / 依赖: IsBounded, IsBoundedUnder, eventually_map, exists_frequently_lt_of_liminf_ne_top, exists_rat_gt, filter_upwards, isBoundedUnder_le_abs, lt_add_iff_pos_right, lt_of_lt_of_le, not_and_or, not_exists, not_lt, zero_lt_one
-/
theorem exists_upcrossings_of_not_bounded_under {ι : Type*} {l : Filter ι} {x : ι -> Real}
    (hf : liminf (fun i => (Real.nnabs (x i) : Real>=0∞)) l != ∞)
    (hbdd : ¬IsBoundedUnder (· <= ·) l fun i => |x i|) :
    exists a b : Rat, a < b ∧ (existsᶠ i in l, x i < a) ∧ existsᶠ i in l, ↑b < x i := by
  rw [isBoundedUnder_le_abs]; rw [not_and_or] at hbdd
  obtain hbdd | hbdd := hbdd
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top hf
    obtain ⟨q, hq⟩ := exists_rat_gt R
    refine ⟨q, q + 1, (lt_add_iff_pos_right _).2 zero_lt_one, ?_, ?_⟩
    · refine fun hcon => hR ?_
      filter_upwards [hcon] with x hx using not_lt.2 (lt_of_lt_of_le hq (not_lt.1 hx)).le
    · simp only [IsBoundedUnder, IsBounded, eventually_map, not_exists] at hbdd
      refine fun hcon => hbdd ↑(q + 1) ?_
      filter_upwards [hcon] with x hx using not_lt.1 hx
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top' hf
    obtain ⟨q, hq⟩ := exists_rat_lt R
    refine ⟨q - 1, q, (sub_lt_self_iff _).2 zero_lt_one, ?_, ?_⟩
    · simp only [IsBoundedUnder, IsBounded, eventually_map, not_exists] at hbdd
      refine fun hcon => hbdd ↑(q - 1) ?_
      filter_upwards [hcon] with x hx using not_lt.1 hx
    · refine fun hcon => hR ?_
      filter_upwards [hcon] with x hx using not_lt.2 ((not_lt.1 hx).trans hq.le)

end Liminf

/--
theorem `tendsto_toReal_iff` / 定理 `tendsto_toReal_iff`

English:
theorem tendsto_toReal_iff
  statement: {ι} {fi : Filter ι} {f : ι -> Real>=0∞} (hf : forall i, f i != ∞) {x : Real>=0∞}
  proof: by
  lift f to ι -> Real>=0 using hf
  lift x to Real>=0 using hx
  simp [tendsto_coe]

中文:
定理 tendsto_toReal_iff
  结论: {ι} {fi : Filter ι} {f : ι -> 实数>=0∞} (hf : 对任意 i, f i != ∞) {x : 实数>=0∞}
  证明: by
  lift f to ι -> Real>=0 using hf
  lift x to Real>=0 using hx
  simp [tendsto_coe]

Depends on / 依赖: tendsto_coe
-/
theorem tendsto_toReal_iff {ι} {fi : Filter ι} {f : ι -> Real>=0∞} (hf : forall i, f i != ∞) {x : Real>=0∞}
    (hx : x != ∞) : Tendsto (fun n => (f n).toReal) fi (𝓝 x.toReal) ↔ Tendsto f fi (𝓝 x) := by
  lift f to ι -> Real>=0 using hf
  lift x to Real>=0 using hx
  simp [tendsto_coe]

/--
theorem `tendsto_toReal_zero_iff` / 定理 `tendsto_toReal_zero_iff`

English:
theorem tendsto_toReal_zero_iff
  statement: {ι} {fi : Filter ι} {f : ι -> Real>=0∞}
  proof: by
  rw [← ENNReal.toReal_zero]; rw [tendsto_toReal_iff hf ENNReal.zero_ne_top]

中文:
定理 tendsto_toReal_zero_iff
  结论: {ι} {fi : Filter ι} {f : ι -> 实数>=0∞}
  证明: by
  rw [← ENNReal.toReal_zero]; rw [tendsto_toReal_iff hf ENNReal.zero_ne_top]

Depends on / 依赖: ENNReal, ENNReal.toReal_zero, ENNReal.zero_ne_top, Tendsto, finiteness, tendsto_toReal_iff, toReal, toReal_zero, zero_ne_top
-/
theorem tendsto_toReal_zero_iff {ι} {fi : Filter ι} {f : ι -> Real>=0∞}
    (hf : forall i, f i != ∞ := by finiteness) :
    Tendsto (fun n => (f n).toReal) fi (𝓝 0) ↔ Tendsto f fi (𝓝 0) := by
  rw [← ENNReal.toReal_zero]; rw [tendsto_toReal_iff hf ENNReal.zero_ne_top]

end ENNReal

section

variable [EMetricSpace β]

open ENNReal Filter

/--
theorem `edist_ne_top_of_mem_ball` / 定理 `edist_ne_top_of_mem_ball`

English:
theorem edist_ne_top_of_mem_ball
  given: {a : β} {r : Real>=0∞} (x y : eball a r)
  statement: edist x.1 y.1 != ∞
  proof: ne_of_lt
    calc
      edist x y <= edist a x + edist a y := edist_triangle_left x.1 y.1 a
      _ < r + r := by rw [edist_comm a x, edist_comm a y]; exact ENNReal.add_lt_add x.2 y.2
      _ <= ∞ := le_top

中文:
定理 edist_ne_top_of_mem_ball
  条件: {a : β} {r : 实数>=0∞} (x y : eball a r)
  结论: edist x.1 y.1 != ∞
  证明: ne_of_lt
    calc
      edist x y <= edist a x + edist a y := edist_triangle_left x.1 y.1 a
      _ < r + r := by rw [edist_comm a x, edist_comm a y]; exact ENNReal.add_lt_add x.2 y.2
      _ <= ∞ := le_top

Depends on / 依赖: ENNReal, ENNReal.add_lt_add, add_lt_add, edist_comm, edist_triangle_left, le_top, ne_of_lt
-/
theorem edist_ne_top_of_mem_ball {a : β} {r : Real>=0∞} (x y : eball a r) : edist x.1 y.1 != ∞ :=
ne_of_lt
    calc
      edist x y <= edist a x + edist a y := edist_triangle_left x.1 y.1 a
      _ < r + r := by rw [edist_comm a x, edist_comm a y]; exact ENNReal.add_lt_add x.2 y.2
      _ <= ∞ := le_top

/-- Each ball in an extended metric space gives us a metric space, as the edist
is everywhere finite. -/
@[instance_reducible]
/--
Definition of `metricSpaceEMetricBall` / `metricSpaceEMetricBall` 的定义

English:
definition metricSpaceEMetricBall
  signature: (a : β) (r : Real>=0∞)
  body: EMetricSpace.toMetricSpace edist_ne_top_of_mem_ball

中文:
定义 metricSpaceEMetricBall
  签名: (a : β) (r : 实数>=0∞)
  定义体: EMetricSpace.toMetricSpace edist_ne_top_of_mem_ball

Depends on / 依赖: EMetricSpace, EMetricSpace.toMetricSpace, edist_ne_top_of_mem_ball, toMetricSpace
-/
def metricSpaceEMetricBall (a : β) (r : Real>=0∞) : MetricSpace (eball a r) :=
  EMetricSpace.toMetricSpace edist_ne_top_of_mem_ball

/--
theorem `nhds_eq_nhds_emetric_ball` / 定理 `nhds_eq_nhds_emetric_ball`

English:
theorem nhds_eq_nhds_emetric_ball
  given: (a x : β) (r : Real>=0∞) (h : x in eball a r)
  proof: (map_nhds_subtype_coe_eq_nhds _ <| isOpen_eball.mem_nhds h).symm

中文:
定理 nhds_eq_nhds_emetric_ball
  条件: (a x : β) (r : 实数>=0∞) (h : x in eball a r)
  证明: (map_nhds_subtype_coe_eq_nhds _ <| isOpen_eball.mem_nhds h).symm

Depends on / 依赖: isOpen_eball, isOpen_eball.mem_nhds, map_nhds_subtype_coe_eq_nhds, mem_nhds
-/
theorem nhds_eq_nhds_emetric_ball (a x : β) (r : Real>=0∞) (h : x in eball a r) :
    𝓝 x = map ((↑) : eball a r -> β) (𝓝 ⟨x, h⟩) :=
  (map_nhds_subtype_coe_eq_nhds _ <| isOpen_eball.mem_nhds h).symm

end

section

variable [PseudoEMetricSpace α]

open EMetric

/--
theorem `tendsto_iff_edist_tendsto_0` / 定理 `tendsto_iff_edist_tendsto_0`

English:
theorem tendsto_iff_edist_tendsto_0
  given: {l : Filter β} {f : β -> α} {y : α}
  proof: by
  simp only [Metric.nhds_basis_eball.tendsto_right_iff, Metric.mem_eball,
    @tendsto_order Real>=0∞ β _ _, forall_prop_of_false ENNReal.not_lt_zero, forall_const, true_and]

中文:
定理 tendsto_iff_edist_tendsto_0
  条件: {l : Filter β} {f : β -> α} {y : α}
  证明: by
  simp only [Metric.nhds_basis_eball.tendsto_right_iff, Metric.mem_eball,
    @tendsto_order Real>=0∞ β _ _, forall_prop_of_false ENNReal.not_lt_zero, forall_const, true_and]

Depends on / 依赖: ENNReal, ENNReal.not_lt_zero, Metric, Metric.mem_eball, Metric.nhds_basis_eball.tendsto_right_iff, forall_const, forall_prop_of_false, mem_eball, nhds_basis_eball, not_lt_zero, tendsto_order, tendsto_right_iff, true_and
-/
theorem tendsto_iff_edist_tendsto_0 {l : Filter β} {f : β -> α} {y : α} :
    Tendsto f l (𝓝 y) ↔ Tendsto (fun x => edist (f x) y) l (𝓝 0) := by
  simp only [Metric.nhds_basis_eball.tendsto_right_iff, Metric.mem_eball,
    @tendsto_order Real>=0∞ β _ _, forall_prop_of_false ENNReal.not_lt_zero, forall_const, true_and]

/--
theorem `EMetric.cauchySeq_iff_le_tendsto_0` / 定理 `EMetric.cauchySeq_iff_le_tendsto_0`

English:
theorem EMetric.cauchySeq_iff_le_tendsto_0
  given: [Nonempty β] [SemilatticeSup β] {s : β -> α}
  proof: EMetric.cauchySeq_iff.trans by
  constructor
  · intro hs
    /- `s` is Cauchy sequence. Let `b n` be the diameter of the set `s '' Set.Ici n`. -/
    refine ⟨fun N => Metric.ediam (s '' Ici N), fun n m N hn hm => ?_, ?_⟩
    -- Prove that it bounds the distances of points in the Cauchy sequence
   

中文:
定理 EMetric.cauchySeq_iff_le_tendsto_0
  条件: [Nonempty β] [SemilatticeSup β] {s : β -> α}
  证明: EMetric.cauchySeq_iff.trans by
  constructor
  · intro hs
    /- `s` is Cauchy sequence. Let `b n` be the diameter of the set `s '' Set.Ici n`. -/
    refine ⟨fun N => Metric.ediam (s '' Ici N), fun n m N hn hm => ?_, ?_⟩
    -- Prove that it bounds the distances of points in the Cauchy sequence
   

Depends on / 依赖: EMetric, EMetric.cauchySeq_iff.trans, cauchySeq_iff
-/
theorem EMetric.cauchySeq_iff_le_tendsto_0 [Nonempty β] [SemilatticeSup β] {s : β -> α} :
    CauchySeq s ↔ exists b : β -> Real>=0∞, (forall n m N : β, N <= n -> N <= m -> edist (s n) (s m) <= b N) ∧
Tendsto b atTop (𝓝 0) := EMetric.cauchySeq_iff.trans by
  constructor
  · intro hs
    /- `s` is Cauchy sequence. Let `b n` be the diameter of the set `s '' Set.Ici n`. -/
    refine ⟨fun N => Metric.ediam (s '' Ici N), fun n m N hn hm => ?_, ?_⟩
    -- Prove that it bounds the distances of points in the Cauchy sequence
    · exact Metric.edist_le_ediam_of_mem (mem_image_of_mem _ hn) (mem_image_of_mem _ hm)
    -- Prove that it tends to `0`, by using the Cauchy property of `s`
    · refine ENNReal.tendsto_nhds_zero.2 fun ε ε0 => ?_
      rcases hs ε ε0 with ⟨N, hN⟩
      refine (eventually_ge_atTop N).mono fun n hn => Metric.ediam_le ?_
      rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
      exact (hN _ (hn.trans hk) _ (hn.trans hl)).le
  · rintro ⟨b, ⟨b_bound, b_lim⟩⟩ ε εpos
    have : forallᶠ n in atTop, b n < ε := b_lim.eventually (gt_mem_nhds εpos)
    rcases this.exists with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    calc edist (s m) (s n) <= b N := b_bound m n N hm hn
    _ < ε := hN

/--
theorem `continuous_of_le_add_edist` / 定理 `continuous_of_le_add_edist`

English:
theorem continuous_of_le_add_edist
  statement: {f : α -> Real>=0∞} (C : Real>=0∞) (hC : C != ∞)
  proof: by
  refine continuous_iff_continuousAt.2 fun x => ENNReal.tendsto_nhds_of_Icc fun ε ε0 => ?_
  rcases ENNReal.exists_nnreal_pos_mul_lt hC ε0.ne' with ⟨δ, δ0, hδ⟩
  rw [mul_comm] at hδ
  filter_upwards [Metric.closedEBall_mem_nhds x (ENNReal.coe_pos.2 δ0)] with y hy
refine ⟨tsub_le_iff_right.2 (h x 

中文:
定理 continuous_of_le_add_edist
  结论: {f : α -> 实数>=0∞} (C : 实数>=0∞) (hC : C != ∞)
  证明: by
  refine continuous_iff_continuousAt.2 fun x => ENNReal.tendsto_nhds_of_Icc fun ε ε0 => ?_
  rcases ENNReal.exists_nnreal_pos_mul_lt hC ε0.ne' with ⟨δ, δ0, hδ⟩
  rw [mul_comm] at hδ
  filter_upwards [Metric.closedEBall_mem_nhds x (ENNReal.coe_pos.2 δ0)] with y hy
refine ⟨tsub_le_iff_right.2 (h x 

Depends on / 依赖: ENNReal, ENNReal.coe_pos, ENNReal.exists_nnreal_pos_mul_lt, ENNReal.tendsto_nhds_of_Icc, Metric, Metric.closedEBall_mem_nhds, Metric.mem_closedEBall, closedEBall_mem_nhds, coe_pos, continuous_iff_continuousAt, exacts, exists_nnreal_pos_mul_lt, filter_upwards, mem_closedEBall, mul_comm, tendsto_nhds_of_Icc, tsub_le_iff_right
-/
theorem continuous_of_le_add_edist {f : α -> Real>=0∞} (C : Real>=0∞) (hC : C != ∞)
    (h : forall x y, f x <= f y + C * edist x y) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ENNReal.tendsto_nhds_of_Icc fun ε ε0 => ?_
  rcases ENNReal.exists_nnreal_pos_mul_lt hC ε0.ne' with ⟨δ, δ0, hδ⟩
  rw [mul_comm] at hδ
  filter_upwards [Metric.closedEBall_mem_nhds x (ENNReal.coe_pos.2 δ0)] with y hy
refine ⟨tsub_le_iff_right.2 (h x y).trans ?_, (h y x).trans ?_⟩ <;> grw [← hδ.le] <;> gcongr
  exacts [Metric.mem_closedEBall'.1 hy, Metric.mem_closedEBall.1 hy]

/--
theorem `continuous_edist` / 定理 `continuous_edist`

English:
theorem continuous_edist
  statement: Continuous fun p : α × α => edist p.1 p.2
  proof: by
  apply continuous_of_le_add_edist 2 (by decide)
  rintro ⟨x, y⟩ ⟨x', y'⟩
  calc
    edist x y <= edist x x' + edist x' y' + edist y' y := edist_triangle4 _ _ _ _
    _ = edist x' y' + (edist x x' + edist y y') := by rw [edist_comm y y']; abel
    _ <= edist x' y' + (edist (x, y) (x', y') + edist

中文:
定理 continuous_edist
  结论: Continuous fun p : α × α => edist p.1 p.2
  证明: by
  apply continuous_of_le_add_edist 2 (by decide)
  rintro ⟨x, y⟩ ⟨x', y'⟩
  calc
    edist x y <= edist x x' + edist x' y' + edist y' y := edist_triangle4 _ _ _ _
    _ = edist x' y' + (edist x x' + edist y y') := by rw [edist_comm y y']; abel
    _ <= edist x' y' + (edist (x, y) (x', y') + edist

Depends on / 依赖: apply_rules, continuous_of_le_add_edist, edist_comm, edist_triangle4, le_max_left, le_max_right, mul_comm, mul_two
-/
theorem continuous_edist : Continuous fun p : α × α => edist p.1 p.2 := by
  apply continuous_of_le_add_edist 2 (by decide)
  rintro ⟨x, y⟩ ⟨x', y'⟩
  calc
    edist x y <= edist x x' + edist x' y' + edist y' y := edist_triangle4 _ _ _ _
    _ = edist x' y' + (edist x x' + edist y y') := by rw [edist_comm y y']; abel
    _ <= edist x' y' + (edist (x, y) (x', y') + edist (x, y) (x', y')) := by
      gcongr <;> apply_rules [le_max_left, le_max_right]
    _ = edist x' y' + 2 * edist (x, y) (x', y') := by rw [← mul_two, mul_comm]

@[continuity, fun_prop]
/--
theorem `Continuous.edist` / 定理 `Continuous.edist`

English:
theorem Continuous.edist
  statement: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f)
  proof: continuous_edist.comp (hf.prodMk hg :)

中文:
定理 Continuous.edist
  结论: [TopologicalSpace β] {f g : β -> α} (hf : Continuous f)
  证明: continuous_edist.comp (hf.prodMk hg :)

Depends on / 依赖: continuous_edist, continuous_edist.comp, hf.prodMk, prodMk
-/
theorem Continuous.edist [TopologicalSpace β] {f g : β -> α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => edist (f b) (g b) :=
  continuous_edist.comp (hf.prodMk hg :)

/--
theorem `Filter.Tendsto.edist` / 定理 `Filter.Tendsto.edist`

English:
theorem Filter.Tendsto.edist
  statement: {f g : β -> α} {x : Filter β} {a b : α} (hf : Tendsto f x (𝓝 a))
  proof: (continuous_edist.tendsto (a, b)).comp (hf.prodMk_nhds hg)

中文:
定理 Filter.Tendsto.edist
  结论: {f g : β -> α} {x : Filter β} {a b : α} (hf : Tendsto f x (𝓝 a))
  证明: (continuous_edist.tendsto (a, b)).comp (hf.prodMk_nhds hg)

Depends on / 依赖: continuous_edist, continuous_edist.tendsto, hf.prodMk_nhds, prodMk_nhds, tendsto
-/
theorem Filter.Tendsto.edist {f g : β -> α} {x : Filter β} {a b : α} (hf : Tendsto f x (𝓝 a))
    (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => edist (f x) (g x)) x (𝓝 (edist a b)) :=
  (continuous_edist.tendsto (a, b)).comp (hf.prodMk_nhds hg)

/--
theorem `Metric.isClosed_closedEBall` / 定理 `Metric.isClosed_closedEBall`

English:
theorem Metric.isClosed_closedEBall
  given: {a : α} {r : Real>=0∞}
  statement: IsClosed (closedEBall a r)
  proof: isClosed_le (by fun_prop) continuous_const

@[deprecated (since := "2026-01-24")]
alias EMetric.isClosed_closedBall := Metric.isClosed_closedEBall

@[simp]

中文:
定理 Metric.isClosed_closedEBall
  条件: {a : α} {r : 实数>=0∞}
  结论: IsClosed (closedEBall a r)
  证明: isClosed_le (by fun_prop) continuous_const

@[deprecated (since := "2026-01-24")]
alias EMetric.isClosed_closedBall := Metric.isClosed_closedEBall

@[simp]

Depends on / 依赖: continuous_const, fun_prop, isClosed_le
-/
theorem Metric.isClosed_closedEBall {a : α} {r : Real>=0∞} : IsClosed (closedEBall a r) :=
  isClosed_le (by fun_prop) continuous_const

@[deprecated (since := "2026-01-24")]
alias EMetric.isClosed_closedBall := Metric.isClosed_closedEBall

@[simp]
/--
theorem `Metric.ediam_closure` / 定理 `Metric.ediam_closure`

English:
theorem Metric.ediam_closure
  given: (s : Set α)
  statement: ediam (closure s) = ediam s
  proof: by
  refine le_antisymm (ediam_le fun x hx y hy => ?_) (ediam_mono subset_closure)
  have : edist x y in closure (Iic (ediam s)) :=
    map_mem_closure₂ continuous_edist hx hy fun x hx y hy => edist_le_ediam_of_mem hx hy
  rwa [closure_Iic] at this

@[deprecated (since := "2026-01-04")] alias EMetri

中文:
定理 Metric.ediam_closure
  条件: (s : Set α)
  结论: ediam (closure s) = ediam s
  证明: by
  refine le_antisymm (ediam_le fun x hx y hy => ?_) (ediam_mono subset_closure)
  have : edist x y in closure (Iic (ediam s)) :=
    map_mem_closure₂ continuous_edist hx hy fun x hx y hy => edist_le_ediam_of_mem hx hy
  rwa [closure_Iic] at this

@[deprecated (since := "2026-01-04")] alias EMetri

Depends on / 依赖: closure, closure_Iic, continuous_edist, ediam_le, ediam_mono, edist_le_ediam_of_mem, le_antisymm, subset_closure
-/
theorem Metric.ediam_closure (s : Set α) : ediam (closure s) = ediam s := by
  refine le_antisymm (ediam_le fun x hx y hy => ?_) (ediam_mono subset_closure)
  have : edist x y in closure (Iic (ediam s)) :=
    map_mem_closure₂ continuous_edist hx hy fun x hx y hy => edist_le_ediam_of_mem hx hy
  rwa [closure_Iic] at this

@[deprecated (since := "2026-01-04")] alias EMetric.diam_closure := Metric.ediam_closure

@[simp]
/--
theorem `Metric.diam_closure` / 定理 `Metric.diam_closure`

English:
theorem Metric.diam_closure
  given: {α : Type*} [PseudoMetricSpace α] (s : Set α)
  proof: by simp only [Metric.diam, Metric.ediam_closure]

中文:
定理 Metric.diam_closure
  条件: {α : 类型} [PseudoMetricSpace α] (s : Set α)
  证明: by simp only [Metric.diam, Metric.ediam_closure]

Depends on / 依赖: Metric, Metric.diam, Metric.ediam_closure, ediam_closure
-/
theorem Metric.diam_closure {α : Type*} [PseudoMetricSpace α] (s : Set α) :
    Metric.diam (closure s) = diam s := by simp only [Metric.diam, Metric.ediam_closure]

/--
theorem `isClosed_setOfPred_lipschitzOnWith` / 定理 `isClosed_setOfPred_lipschitzOnWith`

English:
theorem isClosed_setOfPred_lipschitzOnWith
  statement: {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: by
  simp only [LipschitzOnWith, ofPred_forall]
  refine isClosed_biInter fun x _ => isClosed_biInter fun y _ => isClosed_le ?_ ?_
  exacts [.edist (continuous_apply x) (continuous_apply y), continuous_const]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_lipschitzOnWith := isClosed_set

中文:
定理 isClosed_setOfPred_lipschitzOnWith
  结论: {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: by
  simp only [LipschitzOnWith, ofPred_forall]
  refine isClosed_biInter fun x _ => isClosed_biInter fun y _ => isClosed_le ?_ ?_
  exacts [.edist (continuous_apply x) (continuous_apply y), continuous_const]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_lipschitzOnWith := isClosed_set

Depends on / 依赖: LipschitzOnWith, continuous_apply, continuous_const, exacts, isClosed_biInter, isClosed_le, ofPred_forall
-/
theorem isClosed_setOfPred_lipschitzOnWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (K : Real>=0)
    (s : Set α) : IsClosed { f : α -> β | LipschitzOnWith K f s } := by
  simp only [LipschitzOnWith, ofPred_forall]
  refine isClosed_biInter fun x _ => isClosed_biInter fun y _ => isClosed_le ?_ ?_
  exacts [.edist (continuous_apply x) (continuous_apply y), continuous_const]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_lipschitzOnWith := isClosed_setOfPred_lipschitzOnWith

/--
theorem `isClosed_setOfPred_lipschitzWith` / 定理 `isClosed_setOfPred_lipschitzWith`

English:
theorem isClosed_setOfPred_lipschitzWith
  statement: {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  proof: by
  simp only [← lipschitzOnWith_univ, isClosed_setOfPred_lipschitzOnWith]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_lipschitzWith := isClosed_setOfPred_lipschitzWith

中文:
定理 isClosed_setOfPred_lipschitzWith
  结论: {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
  证明: by
  simp only [← lipschitzOnWith_univ, isClosed_setOfPred_lipschitzOnWith]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_lipschitzWith := isClosed_setOfPred_lipschitzWith

Depends on / 依赖: isClosed_setOfPred_lipschitzOnWith, lipschitzOnWith_univ
-/
theorem isClosed_setOfPred_lipschitzWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (K : Real>=0) :
    IsClosed { f : α -> β | LipschitzWith K f } := by
  simp only [← lipschitzOnWith_univ, isClosed_setOfPred_lipschitzOnWith]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_lipschitzWith := isClosed_setOfPred_lipschitzWith

/--
lemma `LipschitzOnWith.closure` / 引理 `LipschitzOnWith.closure`

English:
lemma LipschitzOnWith.closure
  statement: [PseudoEMetricSpace β] {f : α -> β} {s : Set α} {K : Real>=0}
  proof: by
  have := ENNReal.continuous_const_mul (ENNReal.coe_ne_top (r := K))
  refine fun x hx => le_on_closure (fun y hy => le_on_closure (fun x hx => hf hx hy) ?_ ?_ hx) ?_ ?_
  all_goals fun_prop

中文:
引理 LipschitzOnWith.closure
  结论: [PseudoEMetricSpace β] {f : α -> β} {s : Set α} {K : 实数>=0}
  证明: by
  have := ENNReal.continuous_const_mul (ENNReal.coe_ne_top (r := K))
  refine fun x hx => le_on_closure (fun y hy => le_on_closure (fun x hx => hf hx hy) ?_ ?_ hx) ?_ ?_
  all_goals fun_prop
-/
protected lemma LipschitzOnWith.closure [PseudoEMetricSpace β] {f : α -> β} {s : Set α} {K : Real>=0}
    (hcont : ContinuousOn f (closure s)) (hf : LipschitzOnWith K f s) :
    LipschitzOnWith K f (closure s) := by
  have := ENNReal.continuous_const_mul (ENNReal.coe_ne_top (r := K))
  refine fun x hx => le_on_closure (fun y hy => le_on_closure (fun x hx => hf hx hy) ?_ ?_ hx) ?_ ?_
  all_goals fun_prop

/--
lemma `lipschitzOnWith_closure_iff` / 引理 `lipschitzOnWith_closure_iff`

English:
lemma lipschitzOnWith_closure_iff
  statement: [PseudoEMetricSpace β] {f : α -> β} {s : Set α} {K : Real>=0}
  proof: ⟨fun hf => hf.mono subset_closure, LipschitzOnWith.closure hcont⟩

中文:
引理 lipschitzOnWith_closure_iff
  结论: [PseudoEMetricSpace β] {f : α -> β} {s : Set α} {K : 实数>=0}
  证明: ⟨fun hf => hf.mono subset_closure, LipschitzOnWith.closure hcont⟩

Depends on / 依赖: LipschitzOnWith, LipschitzOnWith.closure, closure, hf.mono, subset_closure
-/
lemma lipschitzOnWith_closure_iff [PseudoEMetricSpace β] {f : α -> β} {s : Set α} {K : Real>=0}
    (hcont : ContinuousOn f (closure s)) :
    LipschitzOnWith K f (closure s) ↔ LipschitzOnWith K f s :=
  ⟨fun hf => hf.mono subset_closure, LipschitzOnWith.closure hcont⟩

namespace Real

/--
theorem `ediam_eq` / 定理 `ediam_eq`

English:
theorem ediam_eq
  given: {s : Set Real} (h : Bornology.IsBounded s)
  proof: by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp
  refine le_antisymm (Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_) ?_
  · exact Real.dist_le_of_mem_Icc (h.subset_Icc_sInf_sSup hx) (h.subset_Icc_sInf_sSup hy)
  · apply ENNReal.ofReal_le_of_le_toReal
    rw [← Metric.diam]; rw [

中文:
定理 ediam_eq
  条件: {s : Set 实数} (h : Bornology.IsBounded s)
  证明: by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp
  refine le_antisymm (Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_) ?_
  · exact Real.dist_le_of_mem_Icc (h.subset_Icc_sInf_sSup hx) (h.subset_Icc_sInf_sSup hy)
  · apply ENNReal.ofReal_le_of_le_toReal
    rw [← Metric.diam]; rw [

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_of_le_toReal, Metric, Metric.diam, Metric.diam_closure, Metric.ediam_le_of_forall_dist_le, Real.dist_le_of_mem_Icc, bddAbove, closure, csInf_mem_closure, csSup_mem_closure, diam_closure, dist_le_diam_of_mem, dist_le_of_mem_Icc, ediam_le_of_forall_dist_le, eq_empty_or_nonempty, h.bddAbove, h.bddBe, h.closure, h.subset_Icc_sInf_sSup
-/
theorem ediam_eq {s : Set Real} (h : Bornology.IsBounded s) :
    Metric.ediam s = ENNReal.ofReal (sSup s - sInf s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp
  refine le_antisymm (Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_) ?_
  · exact Real.dist_le_of_mem_Icc (h.subset_Icc_sInf_sSup hx) (h.subset_Icc_sInf_sSup hy)
  · apply ENNReal.ofReal_le_of_le_toReal
    rw [← Metric.diam]; rw [← Metric.diam_closure]
    calc sSup s - sInf s <= dist (sSup s) (sInf s) := le_abs_self _
    _ <= Metric.diam (closure s) := dist_le_diam_of_mem h.closure (csSup_mem_closure hne h.bddAbove)
        (csInf_mem_closure hne h.bddBelow)

/--
theorem `diam_eq` / 定理 `diam_eq`

English:
theorem diam_eq
  given: {s : Set Real} (h : Bornology.IsBounded s)
  statement: Metric.diam s = sSup s - sInf s
  proof: by
  rw [Metric.diam]; rw [Real.ediam_eq h]; rw [ENNReal.toReal_ofReal]
  exact sub_nonneg.2 (Real.sInf_le_sSup s h.bddBelow h.bddAbove)

@[simp]

中文:
定理 diam_eq
  条件: {s : Set 实数} (h : Bornology.IsBounded s)
  结论: Metric.diam s = sSup s - sInf s
  证明: by
  rw [Metric.diam]; rw [Real.ediam_eq h]; rw [ENNReal.toReal_ofReal]
  exact sub_nonneg.2 (Real.sInf_le_sSup s h.bddBelow h.bddAbove)

@[simp]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, Metric, Metric.diam, Real.ediam_eq, Real.sInf_le_sSup, bddAbove, bddBelow, ediam_eq, h.bddAbove, h.bddBelow, sInf_le_sSup, sub_nonneg, toReal_ofReal
-/
theorem diam_eq {s : Set Real} (h : Bornology.IsBounded s) : Metric.diam s = sSup s - sInf s := by
  rw [Metric.diam]; rw [Real.ediam_eq h]; rw [ENNReal.toReal_ofReal]
  exact sub_nonneg.2 (Real.sInf_le_sSup s h.bddBelow h.bddAbove)

@[simp]
/--
theorem `ediam_Ioo` / 定理 `ediam_Ioo`

English:
theorem ediam_Ioo
  given: (a b : Real)
  statement: Metric.ediam (Ioo a b) = ENNReal.ofReal (b - a)
  proof: by
  rcases le_or_gt b a with (h | h)
  · simp [h]
  · rw [Real.ediam_eq (isBounded_Ioo _ _), csSup_Ioo h, csInf_Ioo h]

@[simp]

中文:
定理 ediam_Ioo
  条件: (a b : 实数)
  结论: Metric.ediam (Ioo a b) = ENN实数.of实数 (b - a)
  证明: by
  rcases le_or_gt b a with (h | h)
  · simp [h]
  · rw [Real.ediam_eq (isBounded_Ioo _ _), csSup_Ioo h, csInf_Ioo h]

@[simp]

Depends on / 依赖: Real.ediam_eq, csInf_Ioo, csSup_Ioo, ediam_eq, isBounded_Ioo, le_or_gt
-/
theorem ediam_Ioo (a b : Real) : Metric.ediam (Ioo a b) = ENNReal.ofReal (b - a) := by
  rcases le_or_gt b a with (h | h)
  · simp [h]
  · rw [Real.ediam_eq (isBounded_Ioo _ _), csSup_Ioo h, csInf_Ioo h]

@[simp]
/--
theorem `ediam_Icc` / 定理 `ediam_Icc`

English:
theorem ediam_Icc
  given: (a b : Real)
  statement: Metric.ediam (Icc a b) = ENNReal.ofReal (b - a)
  proof: by
  rcases le_or_gt a b with (h | h)
  · rw [Real.ediam_eq (isBounded_Icc _ _), csSup_Icc h, csInf_Icc h]
  · simp [h, h.le]

@[simp]

中文:
定理 ediam_Icc
  条件: (a b : 实数)
  结论: Metric.ediam (Icc a b) = ENN实数.of实数 (b - a)
  证明: by
  rcases le_or_gt a b with (h | h)
  · rw [Real.ediam_eq (isBounded_Icc _ _), csSup_Icc h, csInf_Icc h]
  · simp [h, h.le]

@[simp]

Depends on / 依赖: Real.ediam_eq, csInf_Icc, csSup_Icc, ediam_eq, h.le, isBounded_Icc, le_or_gt
-/
theorem ediam_Icc (a b : Real) : Metric.ediam (Icc a b) = ENNReal.ofReal (b - a) := by
  rcases le_or_gt a b with (h | h)
  · rw [Real.ediam_eq (isBounded_Icc _ _), csSup_Icc h, csInf_Icc h]
  · simp [h, h.le]

@[simp]
/--
theorem `ediam_Ico` / 定理 `ediam_Ico`

English:
theorem ediam_Ico
  given: (a b : Real)
  statement: Metric.ediam (Ico a b) = ENNReal.ofReal (b - a)
  proof: le_antisymm (ediam_Icc a b ▸ ediam_mono Ico_subset_Icc_self)
    (ediam_Ioo a b ▸ ediam_mono Ioo_subset_Ico_self)

@[simp]

中文:
定理 ediam_Ico
  条件: (a b : 实数)
  结论: Metric.ediam (Ico a b) = ENN实数.of实数 (b - a)
  证明: le_antisymm (ediam_Icc a b ▸ ediam_mono Ico_subset_Icc_self)
    (ediam_Ioo a b ▸ ediam_mono Ioo_subset_Ico_self)

@[simp]

Depends on / 依赖: Ico_subset_Icc_self, Ioo_subset_Ico_self, ediam_Icc, ediam_Ioo, ediam_mono, le_antisymm
-/
theorem ediam_Ico (a b : Real) : Metric.ediam (Ico a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ ediam_mono Ico_subset_Icc_self)
    (ediam_Ioo a b ▸ ediam_mono Ioo_subset_Ico_self)

@[simp]
/--
theorem `ediam_Ioc` / 定理 `ediam_Ioc`

English:
theorem ediam_Ioc
  given: (a b : Real)
  statement: Metric.ediam (Ioc a b) = ENNReal.ofReal (b - a)
  proof: le_antisymm (ediam_Icc a b ▸ ediam_mono Ioc_subset_Icc_self)
    (ediam_Ioo a b ▸ ediam_mono Ioo_subset_Ioc_self)

中文:
定理 ediam_Ioc
  条件: (a b : 实数)
  结论: Metric.ediam (Ioc a b) = ENN实数.of实数 (b - a)
  证明: le_antisymm (ediam_Icc a b ▸ ediam_mono Ioc_subset_Icc_self)
    (ediam_Ioo a b ▸ ediam_mono Ioo_subset_Ioc_self)

Depends on / 依赖: Ioc_subset_Icc_self, Ioo_subset_Ioc_self, ediam_Icc, ediam_Ioo, ediam_mono, le_antisymm
-/
theorem ediam_Ioc (a b : Real) : Metric.ediam (Ioc a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ ediam_mono Ioc_subset_Icc_self)
    (ediam_Ioo a b ▸ ediam_mono Ioo_subset_Ioc_self)

/--
theorem `diam_Icc` / 定理 `diam_Icc`

English:
theorem diam_Icc
  given: {a b : Real} (h : a <= b)
  statement: Metric.diam (Icc a b) = b - a
  proof: by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

中文:
定理 diam_Icc
  条件: {a b : 实数} (h : a <= b)
  结论: Metric.diam (Icc a b) = b - a
  证明: by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, Metric, Metric.diam, sub_nonneg, toReal_ofReal
-/
theorem diam_Icc {a b : Real} (h : a <= b) : Metric.diam (Icc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

/--
theorem `diam_Ico` / 定理 `diam_Ico`

English:
theorem diam_Ico
  given: {a b : Real} (h : a <= b)
  statement: Metric.diam (Ico a b) = b - a
  proof: by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

中文:
定理 diam_Ico
  条件: {a b : 实数} (h : a <= b)
  结论: Metric.diam (Ico a b) = b - a
  证明: by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, Metric, Metric.diam, sub_nonneg, toReal_ofReal
-/
theorem diam_Ico {a b : Real} (h : a <= b) : Metric.diam (Ico a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

/--
theorem `diam_Ioc` / 定理 `diam_Ioc`

English:
theorem diam_Ioc
  given: {a b : Real} (h : a <= b)
  statement: Metric.diam (Ioc a b) = b - a
  proof: by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

中文:
定理 diam_Ioc
  条件: {a b : 实数} (h : a <= b)
  结论: Metric.diam (Ioc a b) = b - a
  证明: by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, Metric, Metric.diam, sub_nonneg, toReal_ofReal
-/
theorem diam_Ioc {a b : Real} (h : a <= b) : Metric.diam (Ioc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

/--
theorem `diam_Ioo` / 定理 `diam_Ioo`

English:
theorem diam_Ioo
  given: {a b : Real} (h : a <= b)
  statement: Metric.diam (Ioo a b) = b - a
  proof: by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

中文:
定理 diam_Ioo
  条件: {a b : 实数} (h : a <= b)
  结论: Metric.diam (Ioo a b) = b - a
  证明: by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, Metric, Metric.diam, sub_nonneg, toReal_ofReal
-/
theorem diam_Ioo {a b : Real} (h : a <= b) : Metric.diam (Ioo a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

end Real

end

namespace ENNReal

section truncateToReal

/--
Definition of `truncateToReal` / `truncateToReal` 的定义

English:
definition truncateToReal
  signature: (t x : Real>=0∞)
  body: (min t x).toReal

中文:
定义 truncateToReal
  签名: (t x : 实数>=0∞)
  定义体: (min t x).toReal

Depends on / 依赖: toReal
-/
noncomputable def truncateToReal (t x : Real>=0∞) : Real := (min t x).toReal

/--
lemma `truncateToReal_eq_toReal` / 引理 `truncateToReal_eq_toReal`

English:
lemma truncateToReal_eq_toReal
  given: {t x : Real>=0∞} (t_ne_top : t != ∞) (x_le : x <= t)
  proof: by
  have x_lt_top : x < ∞ := lt_of_le_of_lt x_le t_ne_top.lt_top
  have obs : min t x != ∞ := by
    simp_all only [ne_eq, min_eq_top, false_and, not_false_eq_true]
  exact (ENNReal.toReal_eq_toReal_iff' obs x_lt_top.ne).mpr (min_eq_right x_le)

中文:
引理 truncateToReal_eq_toReal
  条件: {t x : 实数>=0∞} (t_ne_top : t != ∞) (x_le : x <= t)
  证明: by
  have x_lt_top : x < ∞ := lt_of_le_of_lt x_le t_ne_top.lt_top
  have obs : min t x != ∞ := by
    simp_all only [ne_eq, min_eq_top, false_and, not_false_eq_true]
  exact (ENNReal.toReal_eq_toReal_iff' obs x_lt_top.ne).mpr (min_eq_right x_le)

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_toReal_iff, false_and, lt_of_le_of_lt, lt_top, min_eq_right, min_eq_top, ne_eq, not_false_eq_true, t_ne_top, t_ne_top.lt_top, toReal_eq_toReal_iff, x_le, x_lt_top, x_lt_top.ne
-/
lemma truncateToReal_eq_toReal {t x : Real>=0∞} (t_ne_top : t != ∞) (x_le : x <= t) :
    truncateToReal t x = x.toReal := by
  have x_lt_top : x < ∞ := lt_of_le_of_lt x_le t_ne_top.lt_top
  have obs : min t x != ∞ := by
    simp_all only [ne_eq, min_eq_top, false_and, not_false_eq_true]
  exact (ENNReal.toReal_eq_toReal_iff' obs x_lt_top.ne).mpr (min_eq_right x_le)

/--
lemma `truncateToReal_le` / 引理 `truncateToReal_le`

English:
lemma truncateToReal_le
  given: {t : Real>=0∞} (t_ne_top : t != ∞) {x : Real>=0∞}
  proof: by
  rw [truncateToReal]
  gcongr
  exact min_le_left t x

中文:
引理 truncateToReal_le
  条件: {t : 实数>=0∞} (t_ne_top : t != ∞) {x : 实数>=0∞}
  证明: by
  rw [truncateToReal]
  gcongr
  exact min_le_left t x

Depends on / 依赖: min_le_left, truncateToReal
-/
lemma truncateToReal_le {t : Real>=0∞} (t_ne_top : t != ∞) {x : Real>=0∞} :
    truncateToReal t x <= t.toReal := by
  rw [truncateToReal]
  gcongr
  exact min_le_left t x

/--
lemma `truncateToReal_nonneg` / 引理 `truncateToReal_nonneg`

English:
lemma truncateToReal_nonneg
  given: {t x : Real>=0∞}
  statement: 0 <= truncateToReal t x
  proof: toReal_nonneg

中文:
引理 truncateToReal_nonneg
  条件: {t x : 实数>=0∞}
  结论: 0 <= truncateTo实数 t x
  证明: toReal_nonneg

Depends on / 依赖: toReal_nonneg
-/
lemma truncateToReal_nonneg {t x : Real>=0∞} : 0 <= truncateToReal t x := toReal_nonneg

/--
lemma `monotone_truncateToReal` / 引理 `monotone_truncateToReal`

English:
lemma monotone_truncateToReal
  given: {t : Real>=0∞} (t_ne_top : t != ∞)
  statement: Monotone (truncateToReal t)
  proof: by
  intro x y x_le_y
  simp only [truncateToReal]
  gcongr
  exact ne_top_of_le_ne_top t_ne_top (min_le_left _ _)

中文:
引理 monotone_truncateToReal
  条件: {t : 实数>=0∞} (t_ne_top : t != ∞)
  结论: Monotone (truncateTo实数 t)
  证明: by
  intro x y x_le_y
  simp only [truncateToReal]
  gcongr
  exact ne_top_of_le_ne_top t_ne_top (min_le_left _ _)

Depends on / 依赖: min_le_left, ne_top_of_le_ne_top, t_ne_top, truncateToReal, x_le_y
-/
lemma monotone_truncateToReal {t : Real>=0∞} (t_ne_top : t != ∞) : Monotone (truncateToReal t) := by
  intro x y x_le_y
  simp only [truncateToReal]
  gcongr
  exact ne_top_of_le_ne_top t_ne_top (min_le_left _ _)

/-- The truncated cast `ENNReal.truncateToReal t : ℝ≥0∞ → ℝ` is continuous when `t ≠ ∞`. -/
@[fun_prop]
/--
lemma `continuous_truncateToReal` / 引理 `continuous_truncateToReal`

English:
lemma continuous_truncateToReal
  given: {t : Real>=0∞} (t_ne_top : t != ∞)
  statement: Continuous (truncateToReal t)
  proof: by
  apply continuousOn_toReal.comp_continuous (by fun_prop)
  simp [t_ne_top]

中文:
引理 continuous_truncateToReal
  条件: {t : 实数>=0∞} (t_ne_top : t != ∞)
  结论: Continuous (truncateTo实数 t)
  证明: by
  apply continuousOn_toReal.comp_continuous (by fun_prop)
  simp [t_ne_top]

Depends on / 依赖: comp_continuous, continuousOn_toReal, continuousOn_toReal.comp_continuous, fun_prop, t_ne_top
-/
lemma continuous_truncateToReal {t : Real>=0∞} (t_ne_top : t != ∞) : Continuous (truncateToReal t) := by
  apply continuousOn_toReal.comp_continuous (by fun_prop)
  simp [t_ne_top]

end truncateToReal

section LimsupLiminf

variable {ι : Type*} {f : Filter ι} {u v : ι -> Real>=0∞}

/--
lemma `limsup_sub_const` / 引理 `limsup_sub_const`

English:
lemma limsup_sub_const
  given: (F : Filter ι) (f : ι -> Real>=0∞) (c : Real>=0∞)
  proof: by
  rcases F.eq_or_neBot with rfl | _
  · simp
  · exact (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => x - c)
    (fun _ _ h => tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt).symm

中文:
引理 limsup_sub_const
  条件: (F : Filter ι) (f : ι -> 实数>=0∞) (c : 实数>=0∞)
  证明: by
  rcases F.eq_or_neBot with rfl | _
  · simp
  · exact (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => x - c)
    (fun _ _ h => tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt).symm

Depends on / 依赖: F.eq_or_neBot, F.map, Monotone, Monotone.map_limsSup_of_continuousAt, continuousAt, continuous_sub_right, eq_or_neBot, map_limsSup_of_continuousAt, tsub_le_tsub_right
-/
lemma limsup_sub_const (F : Filter ι) (f : ι -> Real>=0∞) (c : Real>=0∞) :
    Filter.limsup (fun i => f i - c) F = Filter.limsup f F - c := by
  rcases F.eq_or_neBot with rfl | _
  · simp
  · exact (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => x - c)
    (fun _ _ h => tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt).symm

/--
lemma `liminf_sub_const` / 引理 `liminf_sub_const`

English:
lemma liminf_sub_const
  given: (F : Filter ι) [NeBot F] (f : ι -> Real>=0∞) (c : Real>=0∞)
  proof: (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => x - c)
    (fun _ _ h => tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt).symm

中文:
引理 liminf_sub_const
  条件: (F : Filter ι) [NeBot F] (f : ι -> 实数>=0∞) (c : 实数>=0∞)
  证明: (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => x - c)
    (fun _ _ h => tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt).symm

Depends on / 依赖: F.map, Monotone, Monotone.map_limsInf_of_continuousAt, continuousAt, continuous_sub_right, map_limsInf_of_continuousAt, tsub_le_tsub_right
-/
lemma liminf_sub_const (F : Filter ι) [NeBot F] (f : ι -> Real>=0∞) (c : Real>=0∞) :
    Filter.liminf (fun i => f i - c) F = Filter.liminf f F - c :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => x - c)
    (fun _ _ h => tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt).symm

/--
lemma `limsup_const_sub` / 引理 `limsup_const_sub`

English:
lemma limsup_const_sub
  given: (F : Filter ι) (f : ι -> Real>=0∞) {c : Real>=0∞} (c_ne_top : c != ∞)
  proof: by
  rcases F.eq_or_neBot with rfl | _
  · simp
  · exact (Antitone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => c - x)
    (fun _ _ h => tsub_le_tsub_left h c) (continuous_sub_left c_ne_top).continuousAt).symm

中文:
引理 limsup_const_sub
  条件: (F : Filter ι) (f : ι -> 实数>=0∞) {c : 实数>=0∞} (c_ne_top : c != ∞)
  证明: by
  rcases F.eq_or_neBot with rfl | _
  · simp
  · exact (Antitone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => c - x)
    (fun _ _ h => tsub_le_tsub_left h c) (continuous_sub_left c_ne_top).continuousAt).symm

Depends on / 依赖: Antitone, Antitone.map_limsInf_of_continuousAt, F.eq_or_neBot, F.map, c_ne_top, continuousAt, continuous_sub_left, eq_or_neBot, map_limsInf_of_continuousAt, tsub_le_tsub_left
-/
lemma limsup_const_sub (F : Filter ι) (f : ι -> Real>=0∞) {c : Real>=0∞} (c_ne_top : c != ∞) :
    Filter.limsup (fun i => c - f i) F = c - Filter.liminf f F := by
  rcases F.eq_or_neBot with rfl | _
  · simp
  · exact (Antitone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => c - x)
    (fun _ _ h => tsub_le_tsub_left h c) (continuous_sub_left c_ne_top).continuousAt).symm

/--
lemma `liminf_const_sub` / 引理 `liminf_const_sub`

English:
lemma liminf_const_sub
  given: (F : Filter ι) [NeBot F] (f : ι -> Real>=0∞) {c : Real>=0∞} (c_ne_top : c != ∞)
  proof: (Antitone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => c - x)
    (fun _ _ h => tsub_le_tsub_left h c) (continuous_sub_left c_ne_top).continuousAt).symm

中文:
引理 liminf_const_sub
  条件: (F : Filter ι) [NeBot F] (f : ι -> 实数>=0∞) {c : 实数>=0∞} (c_ne_top : c != ∞)
  证明: (Antitone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => c - x)
    (fun _ _ h => tsub_le_tsub_left h c) (continuous_sub_left c_ne_top).continuousAt).symm

Depends on / 依赖: Antitone, Antitone.map_limsSup_of_continuousAt, F.map, c_ne_top, continuousAt, continuous_sub_left, map_limsSup_of_continuousAt, tsub_le_tsub_left
-/
lemma liminf_const_sub (F : Filter ι) [NeBot F] (f : ι -> Real>=0∞) {c : Real>=0∞} (c_ne_top : c != ∞) :
    Filter.liminf (fun i => c - f i) F = c - Filter.limsup f F :=
  (Antitone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : Real>=0∞) => c - x)
    (fun _ _ h => tsub_le_tsub_left h c) (continuous_sub_left c_ne_top).continuousAt).symm

/--
lemma `le_limsup_mul` / 引理 `le_limsup_mul`

English:
lemma le_limsup_mul
  statement: limsup u f * liminf v f <= limsup (u * v) f
  proof: mul_le_of_forall_lt fun a a_u b b_v => (le_limsup_iff).2 fun c c_ab =>
    Frequently.mono (Frequently.and_eventually ((frequently_lt_of_lt_limsup) a_u)
    ((eventually_lt_of_lt_liminf) b_v)) fun _ ab_x => c_ab.trans (mul_lt_mul ab_x.1 ab_x.2)

中文:
引理 le_limsup_mul
  结论: limsup u f * liminf v f <= limsup (u * v) f
  证明: mul_le_of_forall_lt fun a a_u b b_v => (le_limsup_iff).2 fun c c_ab =>
    Frequently.mono (Frequently.and_eventually ((frequently_lt_of_lt_limsup) a_u)
    ((eventually_lt_of_lt_liminf) b_v)) fun _ ab_x => c_ab.trans (mul_lt_mul ab_x.1 ab_x.2)

Depends on / 依赖: Frequently, Frequently.and_eventually, Frequently.mono, ab_x, and_eventually, c_ab, c_ab.trans, eventually_lt_of_lt_liminf, frequently_lt_of_lt_limsup, le_limsup_iff, mul_le_of_forall_lt, mul_lt_mul
-/
lemma le_limsup_mul : limsup u f * liminf v f <= limsup (u * v) f :=
  mul_le_of_forall_lt fun a a_u b b_v => (le_limsup_iff).2 fun c c_ab =>
    Frequently.mono (Frequently.and_eventually ((frequently_lt_of_lt_limsup) a_u)
    ((eventually_lt_of_lt_liminf) b_v)) fun _ ab_x => c_ab.trans (mul_lt_mul ab_x.1 ab_x.2)

/--
lemma `limsup_mul_le'` / 引理 `limsup_mul_le'`

English:
lemma limsup_mul_le'
  given: (h : limsup u f != 0 ∨ limsup v f != ∞) (h' : limsup u f != ∞ ∨ limsup v f != 0)
  proof: by
  refine le_mul_of_forall_lt h h' fun a a_u b b_v => (limsup_le_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (mul_lt_mul a_x b_x).trans c_ab

中文:
引理 limsup_mul_le'
  条件: (h : limsup u f != 0 ∨ limsup v f != ∞) (h' : limsup u f != ∞ ∨ limsup v f != 0)
  证明: by
  refine le_mul_of_forall_lt h h' fun a a_u b b_v => (limsup_le_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (mul_lt_mul a_x b_x).trans c_ab

Depends on / 依赖: c_ab, eventually_lt_of_limsup_lt, filter_upwards, le_mul_of_forall_lt, limsup_le_iff, mul_lt_mul
-/
lemma limsup_mul_le' (h : limsup u f != 0 ∨ limsup v f != ∞) (h' : limsup u f != ∞ ∨ limsup v f != 0) :
    limsup (u * v) f <= limsup u f * limsup v f := by
  refine le_mul_of_forall_lt h h' fun a a_u b b_v => (limsup_le_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (mul_lt_mul a_x b_x).trans c_ab

/--
lemma `le_liminf_mul` / 引理 `le_liminf_mul`

English:
lemma le_liminf_mul
  statement: liminf u f * liminf v f <= liminf (u * v) f
  proof: by
  refine mul_le_of_forall_lt fun a a_u b b_v => (le_liminf_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (mul_lt_mul a_x b_x)

中文:
引理 le_liminf_mul
  结论: liminf u f * liminf v f <= liminf (u * v) f
  证明: by
  refine mul_le_of_forall_lt fun a a_u b b_v => (le_liminf_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (mul_lt_mul a_x b_x)

Depends on / 依赖: c_ab, c_ab.trans, eventually_lt_of_lt_liminf, filter_upwards, le_liminf_iff, mul_le_of_forall_lt, mul_lt_mul
-/
lemma le_liminf_mul : liminf u f * liminf v f <= liminf (u * v) f := by
  refine mul_le_of_forall_lt fun a a_u b b_v => (le_liminf_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (mul_lt_mul a_x b_x)

/--
lemma `liminf_mul_le` / 引理 `liminf_mul_le`

English:
lemma liminf_mul_le
  given: (h : limsup u f != 0 ∨ liminf v f != ∞) (h' : limsup u f != ∞ ∨ liminf v f != 0)
  proof: le_mul_of_forall_lt h h' fun a a_u b b_v => (liminf_le_iff).2 fun c c_ab =>
    Frequently.mono (((frequently_lt_of_liminf_lt) b_v).and_eventually
    ((eventually_lt_of_limsup_lt) a_u)) fun _ ab_x => (mul_lt_mul ab_x.2 ab_x.1).trans c_ab

中文:
引理 liminf_mul_le
  条件: (h : limsup u f != 0 ∨ liminf v f != ∞) (h' : limsup u f != ∞ ∨ liminf v f != 0)
  证明: le_mul_of_forall_lt h h' fun a a_u b b_v => (liminf_le_iff).2 fun c c_ab =>
    Frequently.mono (((frequently_lt_of_liminf_lt) b_v).and_eventually
    ((eventually_lt_of_limsup_lt) a_u)) fun _ ab_x => (mul_lt_mul ab_x.2 ab_x.1).trans c_ab

Depends on / 依赖: Frequently, Frequently.mono, ab_x, and_eventually, c_ab, eventually_lt_of_limsup_lt, frequently_lt_of_liminf_lt, le_mul_of_forall_lt, liminf_le_iff, mul_lt_mul
-/
lemma liminf_mul_le (h : limsup u f != 0 ∨ liminf v f != ∞) (h' : limsup u f != ∞ ∨ liminf v f != 0) :
    liminf (u * v) f <= limsup u f * liminf v f :=
  le_mul_of_forall_lt h h' fun a a_u b b_v => (liminf_le_iff).2 fun c c_ab =>
    Frequently.mono (((frequently_lt_of_liminf_lt) b_v).and_eventually
    ((eventually_lt_of_limsup_lt) a_u)) fun _ ab_x => (mul_lt_mul ab_x.2 ab_x.1).trans c_ab

/--
lemma `liminf_toReal_eq` / 引理 `liminf_toReal_eq`

English:
lemma liminf_toReal_eq
  given: [NeBot f] {b : Real>=0∞} (b_ne_top : b != ∞) (le_b : forallᶠ i in f, u i <= b)
  proof: by
  have liminf_le : f.liminf u <= b := by
    apply liminf_le_of_le ⟨0, by simp⟩
    intro y h
    obtain ⟨i, hi⟩ := (Eventually.and h le_b).exists
    exact hi.1.trans hi.2
  have aux : forallᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
   

中文:
引理 liminf_toReal_eq
  条件: [NeBot f] {b : 实数>=0∞} (b_ne_top : b != ∞) (le_b : 对任意ᶠ i in f, u i <= b)
  证明: by
  have liminf_le : f.liminf u <= b := by
    apply liminf_le_of_le ⟨0, by simp⟩
    intro y h
    obtain ⟨i, hi⟩ := (Eventually.and h le_b).exists
    exact hi.1.trans hi.2
  have aux : forallᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
   

Depends on / 依赖: ENNReal, ENNReal.truncateToReal, Eventually, Eventually.and, b_ne_top, f.liminf, filter_upwards, i_le_b, le_b, liminf, liminf_congr, liminf_le, liminf_le_of_le, simp_rw, toReal, truncateToReal, truncateToReal_eq_toReal
-/
lemma liminf_toReal_eq [NeBot f] {b : Real>=0∞} (b_ne_top : b != ∞) (le_b : forallᶠ i in f, u i <= b) :
    f.liminf (fun i => (u i).toReal) = (f.liminf u).toReal := by
  have liminf_le : f.liminf u <= b := by
    apply liminf_le_of_le ⟨0, by simp⟩
    intro y h
    obtain ⟨i, hi⟩ := (Eventually.and h le_b).exists
    exact hi.1.trans hi.2
  have aux : forallᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
    simp only [truncateToReal_eq_toReal b_ne_top i_le_b]
  have aux' : (f.liminf u).toReal = ENNReal.truncateToReal b (f.liminf u) := by
    rw [truncateToReal_eq_toReal b_ne_top liminf_le]
  simp_rw [liminf_congr aux, aux']
  have key := Monotone.map_liminf_of_continuousAt (F := f) (monotone_truncateToReal b_ne_top) u
          (continuous_truncateToReal b_ne_top).continuousAt
          (IsBoundedUnder.isCoboundedUnder_ge ⟨b, by simpa only [eventually_map] using le_b⟩)
          ⟨0, Eventually.of_forall (by simp)⟩
  rw [key]
  rfl

/--
lemma `limsup_toReal_eq` / 引理 `limsup_toReal_eq`

English:
lemma limsup_toReal_eq
  given: [NeBot f] {b : Real>=0∞} (b_ne_top : b != ∞) (le_b : forallᶠ i in f, u i <= b)
  proof: by
  have aux : forallᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
    simp only [truncateToReal_eq_toReal b_ne_top i_le_b]
  have aux' : (f.limsup u).toReal = ENNReal.truncateToReal b (f.limsup u) := by
    rw [truncateToReal_eq_toReal b_ne_t

中文:
引理 limsup_toReal_eq
  条件: [NeBot f] {b : 实数>=0∞} (b_ne_top : b != ∞) (le_b : 对任意ᶠ i in f, u i <= b)
  证明: by
  have aux : forallᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
    simp only [truncateToReal_eq_toReal b_ne_top i_le_b]
  have aux' : (f.limsup u).toReal = ENNReal.truncateToReal b (f.limsup u) := by
    rw [truncateToReal_eq_toReal b_ne_t

Depends on / 依赖: ENNReal, ENNReal.truncateToReal, Monotone, Monotone.map_limsup_of_continuousAt, b_ne_top, continu, continuous_truncateToReal, f.limsup, filter_upwards, i_le_b, le_b, limsup, limsup_congr, limsup_le_of_le, map_limsup_of_continuousAt, monotone_truncateToReal, simp_rw, toReal, truncateToReal, truncateToReal_eq_toReal
-/
lemma limsup_toReal_eq [NeBot f] {b : Real>=0∞} (b_ne_top : b != ∞) (le_b : forallᶠ i in f, u i <= b) :
    f.limsup (fun i => (u i).toReal) = (f.limsup u).toReal := by
  have aux : forallᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
    simp only [truncateToReal_eq_toReal b_ne_top i_le_b]
  have aux' : (f.limsup u).toReal = ENNReal.truncateToReal b (f.limsup u) := by
    rw [truncateToReal_eq_toReal b_ne_top (limsup_le_of_le ⟨0]; rw [by simp⟩ le_b)]
  simp_rw [limsup_congr aux, aux']
  have key := Monotone.map_limsup_of_continuousAt (F := f) (monotone_truncateToReal b_ne_top) u
          (continuous_truncateToReal b_ne_top).continuousAt
          ⟨b, by simpa only [eventually_map] using le_b⟩
          (IsBoundedUnder.isCoboundedUnder_le ⟨0, Eventually.of_forall (by simp)⟩)
  rw [key]
  rfl

@[simp, norm_cast]
/--
lemma `ofNNReal_limsup` / 引理 `ofNNReal_limsup`

English:
lemma ofNNReal_limsup
  given: {u : ι -> Real>=0} (hf : f.IsBoundedUnder (· <= ·) u)
  proof: by
  refine eq_of_forall_nnreal_le_iff fun r => ?_
  rw [coe_le_coe]; rw [le_limsup_iff]; rw [le_limsup_iff]
  simp [forall_ennreal]

@[simp, norm_cast]

中文:
引理 ofNNReal_limsup
  条件: {u : ι -> 实数>=0} (hf : f.IsBoundedUnder (· <= ·) u)
  证明: by
  refine eq_of_forall_nnreal_le_iff fun r => ?_
  rw [coe_le_coe]; rw [le_limsup_iff]; rw [le_limsup_iff]
  simp [forall_ennreal]

@[simp, norm_cast]

Depends on / 依赖: coe_le_coe, eq_of_forall_nnreal_le_iff, forall_ennreal, le_limsup_iff
-/
lemma ofNNReal_limsup {u : ι -> Real>=0} (hf : f.IsBoundedUnder (· <= ·) u) :
    limsup u f = limsup (fun i => (u i : Real>=0∞)) f := by
  refine eq_of_forall_nnreal_le_iff fun r => ?_
  rw [coe_le_coe]; rw [le_limsup_iff]; rw [le_limsup_iff]
  simp [forall_ennreal]

@[simp, norm_cast]
/--
lemma `ofNNReal_liminf` / 引理 `ofNNReal_liminf`

English:
lemma ofNNReal_liminf
  given: {u : ι -> Real>=0} (hf : f.IsCoboundedUnder (· >= ·) u)
  proof: by
  refine eq_of_forall_nnreal_le_iff fun r => ?_
  rw [coe_le_coe]; rw [le_liminf_iff]; rw [le_liminf_iff]
  simp [forall_ennreal]

中文:
引理 ofNNReal_liminf
  条件: {u : ι -> 实数>=0} (hf : f.IsCoboundedUnder (· >= ·) u)
  证明: by
  refine eq_of_forall_nnreal_le_iff fun r => ?_
  rw [coe_le_coe]; rw [le_liminf_iff]; rw [le_liminf_iff]
  simp [forall_ennreal]

Depends on / 依赖: coe_le_coe, eq_of_forall_nnreal_le_iff, forall_ennreal, le_liminf_iff
-/
lemma ofNNReal_liminf {u : ι -> Real>=0} (hf : f.IsCoboundedUnder (· >= ·) u) :
    liminf u f = liminf (fun i => (u i : Real>=0∞)) f := by
  refine eq_of_forall_nnreal_le_iff fun r => ?_
  rw [coe_le_coe]; rw [le_liminf_iff]; rw [le_liminf_iff]
  simp [forall_ennreal]

/--
theorem `liminf_add_of_right_tendsto_zero` / 定理 `liminf_add_of_right_tendsto_zero`

English:
theorem liminf_add_of_right_tendsto_zero
  statement: {u : Filter ι} {g : ι -> Real>=0∞} (hg : u.Tendsto g (𝓝 0))
  proof: by
refine le_antisymm ?_ liminf_le_liminf .of_forall by simp
  refine liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
  rw [Filter.le_liminf_iff']
  rintro a hab
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| lt_min (tsub_pos_of_lt hab) one_pos]
    with i hfg hg
exact ENNReal.le_of_

中文:
定理 liminf_add_of_right_tendsto_zero
  结论: {u : Filter ι} {g : ι -> 实数>=0∞} (hg : u.Tendsto g (𝓝 0))
  证明: by
refine le_antisymm ?_ liminf_le_liminf .of_forall by simp
  refine liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
  rw [Filter.le_liminf_iff']
  rintro a hab
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| lt_min (tsub_pos_of_lt hab) one_pos]
    with i hfg hg
exact ENNReal.le_of_

Depends on / 依赖: ENNReal, ENNReal.le_of_add_le_add_right, ENNReal.tendsto_nhds_zero, Filter, Filter.le_liminf_iff, add_le_of_le_tsub_left_of_le, filter_upwards, hab.le, hg.trans, hg.trans_lt, isBoundedDefault, le_antisymm, le_liminf_iff, le_of_add_le_add_right, liminf_le_liminf, liminf_le_of_le, lt_min, min_le_left, of_forall, one_pos
-/
theorem liminf_add_of_right_tendsto_zero {u : Filter ι} {g : ι -> Real>=0∞} (hg : u.Tendsto g (𝓝 0))
    (f : ι -> Real>=0∞) : u.liminf (f + g) = u.liminf f := by
refine le_antisymm ?_ liminf_le_liminf .of_forall by simp
  refine liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
  rw [Filter.le_liminf_iff']
  rintro a hab
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| lt_min (tsub_pos_of_lt hab) one_pos]
    with i hfg hg
exact ENNReal.le_of_add_le_add_right (hg.trans_lt <| by simp).ne
    (add_le_of_le_tsub_left_of_le hab.le <| hg.trans <| min_le_left ..).trans hfg

/--
theorem `liminf_add_of_left_tendsto_zero` / 定理 `liminf_add_of_left_tendsto_zero`

English:
theorem liminf_add_of_left_tendsto_zero
  statement: {u : Filter ι} {f : ι -> Real>=0∞} (hf : u.Tendsto f (𝓝 0))
  proof: by
  rw [add_comm]; rw [liminf_add_of_right_tendsto_zero hf]

中文:
定理 liminf_add_of_left_tendsto_zero
  结论: {u : Filter ι} {f : ι -> 实数>=0∞} (hf : u.Tendsto f (𝓝 0))
  证明: by
  rw [add_comm]; rw [liminf_add_of_right_tendsto_zero hf]

Depends on / 依赖: add_comm, liminf_add_of_right_tendsto_zero
-/
theorem liminf_add_of_left_tendsto_zero {u : Filter ι} {f : ι -> Real>=0∞} (hf : u.Tendsto f (𝓝 0))
    (g : ι -> Real>=0∞) : u.liminf (f + g) = u.liminf g := by
  rw [add_comm]; rw [liminf_add_of_right_tendsto_zero hf]

/--
theorem `limsup_add_of_right_tendsto_zero` / 定理 `limsup_add_of_right_tendsto_zero`

English:
theorem limsup_add_of_right_tendsto_zero
  statement: {u : Filter ι} {g : ι -> Real>=0∞} (hg : u.Tendsto g (𝓝 0))
  proof: by
refine le_antisymm ?_ limsup_le_limsup .of_forall by simp
  refine le_limsup_of_le (by isBoundedDefault) fun b hb => ?_
  rw [Filter.limsup_le_iff']
  rintro a hba
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| tsub_pos_of_lt hba] with i hf hg
  calc f i + g i
    _ <= b + g i := by gc

中文:
定理 limsup_add_of_right_tendsto_zero
  结论: {u : Filter ι} {g : ι -> 实数>=0∞} (hg : u.Tendsto g (𝓝 0))
  证明: by
refine le_antisymm ?_ limsup_le_limsup .of_forall by simp
  refine le_limsup_of_le (by isBoundedDefault) fun b hb => ?_
  rw [Filter.limsup_le_iff']
  rintro a hba
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| tsub_pos_of_lt hba] with i hf hg
  calc f i + g i
    _ <= b + g i := by gc

Depends on / 依赖: ENNReal, ENNReal.tendsto_nhds_zero, Filter, Filter.limsup_le_iff, add_le_of_le_tsub_left_of_le, filter_upwards, hba.le, isBoundedDefault, le_antisymm, le_limsup_of_le, limsup_le_iff, limsup_le_limsup, of_forall, tendsto_nhds_zero, tsub_pos_of_lt
-/
theorem limsup_add_of_right_tendsto_zero {u : Filter ι} {g : ι -> Real>=0∞} (hg : u.Tendsto g (𝓝 0))
    (f : ι -> Real>=0∞) : u.limsup (f + g) = u.limsup f := by
refine le_antisymm ?_ limsup_le_limsup .of_forall by simp
  refine le_limsup_of_le (by isBoundedDefault) fun b hb => ?_
  rw [Filter.limsup_le_iff']
  rintro a hba
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| tsub_pos_of_lt hba] with i hf hg
  calc f i + g i
    _ <= b + g i := by gcongr
    _ <= a := add_le_of_le_tsub_left_of_le hba.le hg

/--
theorem `limsup_add_of_left_tendsto_zero` / 定理 `limsup_add_of_left_tendsto_zero`

English:
theorem limsup_add_of_left_tendsto_zero
  statement: {u : Filter ι} {f : ι -> Real>=0∞} (hf : u.Tendsto f (𝓝 0))
  proof: by
  rw [add_comm]; rw [limsup_add_of_right_tendsto_zero hf]

中文:
定理 limsup_add_of_left_tendsto_zero
  结论: {u : Filter ι} {f : ι -> 实数>=0∞} (hf : u.Tendsto f (𝓝 0))
  证明: by
  rw [add_comm]; rw [limsup_add_of_right_tendsto_zero hf]

Depends on / 依赖: add_comm, limsup_add_of_right_tendsto_zero
-/
theorem limsup_add_of_left_tendsto_zero {u : Filter ι} {f : ι -> Real>=0∞} (hf : u.Tendsto f (𝓝 0))
    (g : ι -> Real>=0∞) : u.limsup (f + g) = u.limsup g := by
  rw [add_comm]; rw [limsup_add_of_right_tendsto_zero hf]

end LimsupLiminf

end ENNReal -- namespace

/--
lemma `Dense.lipschitzWith_extend` / 引理 `Dense.lipschitzWith_extend`

English:
lemma Dense.lipschitzWith_extend
  statement: {α β : Type*}
  proof: by
  have : IsClosed {p : α × α | edist (hs.extend f p.1) (hs.extend f p.2) <= K * edist p.1 p.2} := by
    have : Continuous (hs.extend f) := (hs.uniformContinuous_extend hf.uniformContinuous).continuous
    apply isClosed_le (by fun_prop)
    exact (ENNReal.continuous_const_mul (by simp)).comp (by

中文:
引理 Dense.lipschitzWith_extend
  结论: {α β : 类型}
  证明: by
  have : IsClosed {p : α × α | edist (hs.extend f p.1) (hs.extend f p.2) <= K * edist p.1 p.2} := by
    have : Continuous (hs.extend f) := (hs.uniformContinuous_extend hf.uniformContinuous).continuous
    apply isClosed_le (by fun_prop)
    exact (ENNReal.continuous_const_mul (by simp)).comp (by

Depends on / 依赖: Continuous, ENNReal, ENNReal.continuous_const_mul, IsClosed, continuous, continuous_const_mul, extend, extend_eq, fun_prop, hf.conti, hf.uniformContinuous, hs.extend, hs.extend_eq, hs.prod, hs.uniformContinuous_extend, isClosed_le, uniformContinuous, uniformContinuous_extend
-/
lemma Dense.lipschitzWith_extend {α β : Type*}
    [PseudoEMetricSpace α] [EMetricSpace β] [CompleteSpace β]
    {s : Set α} (hs : Dense s) {f : s -> β} {K : Real>=0} (hf : LipschitzWith K f) :
    LipschitzWith K (hs.extend f) := by
  have : IsClosed {p : α × α | edist (hs.extend f p.1) (hs.extend f p.2) <= K * edist p.1 p.2} := by
    have : Continuous (hs.extend f) := (hs.uniformContinuous_extend hf.uniformContinuous).continuous
    apply isClosed_le (by fun_prop)
    exact (ENNReal.continuous_const_mul (by simp)).comp (by fun_prop)
  have : Dense {p : α × α | edist (hs.extend f p.1) (hs.extend f p.2) <= K * edist p.1 p.2} := by
    apply (hs.prod hs).mono
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have Ax : hs.extend f x = f ⟨x, hx⟩ := hs.extend_eq hf.continuous ⟨x, hx⟩
    have Ay : hs.extend f y = f ⟨y, hy⟩ := hs.extend_eq hf.continuous ⟨y, hy⟩
    simp only [Set.mem_ofPred_eq, Ax, Ay]
    exact hf ⟨x, hx⟩ ⟨y, hy⟩
  simpa only [Dense, IsClosed.closure_eq, Set.mem_ofPred_eq, Prod.forall] using! this
