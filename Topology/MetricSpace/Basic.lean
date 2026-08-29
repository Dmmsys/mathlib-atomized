/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.MetricSpace.Defs

/-!
# Basic properties of metric spaces, and instances.

-/

public section

open Set Filter Bornology Topology
open scoped NNReal Uniformity

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}
variable [PseudoMetricSpace α]
variable {γ : Type w} [MetricSpace γ]

namespace Metric

variable {x : γ} {s : Set γ}

-- see Note [lower instance priority]
instance (priority := 100) _root_.MetricSpace.instT0Space : T0Space γ where
t0 _ _ h := eq_of_dist_eq_zero Metric.inseparable_iff.1 h

/--
theorem `isUniformEmbedding_iff'` / 定理 `isUniformEmbedding_iff'`

English:
theorem isUniformEmbedding_iff'
  given: [PseudoMetricSpace β] {f : γ -> β}
  proof: by
  rw [isUniformEmbedding_iff_isUniformInducing]; rw [isUniformInducing_iff]; rw [uniformContinuous_iff]

中文:
定理 isUniformEmbedding_iff'
  条件: [伪度量空间 β] {f : γ -> β}
  证明: by
  rw [isUniformEmbedding_iff_isUniformInducing]; rw [isUniformInducing_iff]; rw [uniformContinuous_iff]

Depends on / 依赖: isUniformEmbedding_iff_isUniformInducing, isUniformInducing_iff, uniformContinuous_iff
-/
theorem isUniformEmbedding_iff' [PseudoMetricSpace β] {f : γ -> β} :
    IsUniformEmbedding f ↔
      (forall ε > 0, exists δ > 0, forall {a b : γ}, dist a b < δ -> dist (f a) (f b) < ε) ∧
        forall δ > 0, exists ε > 0, forall {a b : γ}, dist (f a) (f b) < ε -> dist a b < δ := by
  rw [isUniformEmbedding_iff_isUniformInducing]; rw [isUniformInducing_iff]; rw [uniformContinuous_iff]

/--
Definition of `_root_.MetricSpace.ofT0PseudoMetricSpace` / `_root_.MetricSpace.ofT0PseudoMetricSpace` 的定义

English:
abbreviation _root_.MetricSpace.ofT0PseudoMetricSpace
  signature: (α : Type*) [PseudoMetricSpace α] [T0Space α]
  body: ‹_›
  eq_of_dist_eq_zero hdist := (Metric.inseparable_iff.2 hdist).eq

中文:
缩写 _root_.度量空间.ofT0PseudoMetricSpace
  签名: (α : 类型) [伪度量空间 α] [T0空间 α]
  定义体: ‹_›
  eq_of_dist_eq_zero hdist := (Metric.inseparable_iff.2 hdist).eq
-/
abbrev _root_.MetricSpace.ofT0PseudoMetricSpace (α : Type*) [PseudoMetricSpace α] [T0Space α] :
    MetricSpace α where
  toPseudoMetricSpace := ‹_›
  eq_of_dist_eq_zero hdist := (Metric.inseparable_iff.2 hdist).eq

-- see Note [lower instance priority]
/-- A metric space induces an emetric space -/
instance (priority := 100) _root_.MetricSpace.toEMetricSpace : EMetricSpace γ :=
  .ofT0PseudoEMetricSpace γ

/--
theorem `isClosed_of_pairwise_le_dist` / 定理 `isClosed_of_pairwise_le_dist`

English:
theorem isClosed_of_pairwise_le_dist
  statement: {s : Set γ} {ε : Real} (hε : 0 < ε)
  proof: isClosed_of_spaced_out (dist_mem_uniformity hε) by simpa using hs

中文:
定理 isClosed_of_pairwise_le_dist
  结论: {s : 集合 γ} {ε : 实数} (hε : 0 < ε)
  证明: isClosed_of_spaced_out (dist_mem_uniformity hε) by simpa using hs

Depends on / 依赖: dist_mem_uniformity, isClosed_of_spaced_out
-/
theorem isClosed_of_pairwise_le_dist {s : Set γ} {ε : Real} (hε : 0 < ε)
    (hs : s.Pairwise fun x y => ε <= dist x y) : IsClosed s :=
isClosed_of_spaced_out (dist_mem_uniformity hε) by simpa using hs

/--
theorem `isClosedEmbedding_of_pairwise_le_dist` / 定理 `isClosedEmbedding_of_pairwise_le_dist`

English:
theorem isClosedEmbedding_of_pairwise_le_dist
  statement: {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
  proof: isClosedEmbedding_of_spaced_out (dist_mem_uniformity hε) by simpa using hf

中文:
定理 isClosedEmbedding_of_pairwise_le_dist
  结论: {α : 类型} [拓扑空间 α] [离散拓扑 α]
  证明: isClosedEmbedding_of_spaced_out (dist_mem_uniformity hε) by simpa using hf

Depends on / 依赖: dist_mem_uniformity, isClosedEmbedding_of_spaced_out
-/
theorem isClosedEmbedding_of_pairwise_le_dist {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    {ε : Real} (hε : 0 < ε) {f : α -> γ} (hf : Pairwise fun x y => ε <= dist (f x) (f y)) :
    IsClosedEmbedding f :=
isClosedEmbedding_of_spaced_out (dist_mem_uniformity hε) by simpa using hf

/--
theorem `isUniformEmbedding_bot_of_pairwise_le_dist` / 定理 `isUniformEmbedding_bot_of_pairwise_le_dist`

English:
theorem isUniformEmbedding_bot_of_pairwise_le_dist
  statement: {β : Type*} {ε : Real} (hε : 0 < ε) {f : β -> α}
  proof: isUniformEmbedding_of_spaced_out (dist_mem_uniformity hε) by simpa using hf

中文:
定理 isUniformEmbedding_bot_of_pairwise_le_dist
  结论: {β : 类型} {ε : 实数} (hε : 0 < ε) {f : β -> α}
  证明: isUniformEmbedding_of_spaced_out (dist_mem_uniformity hε) by simpa using hf

Depends on / 依赖: dist_mem_uniformity, isUniformEmbedding_of_spaced_out
-/
theorem isUniformEmbedding_bot_of_pairwise_le_dist {β : Type*} {ε : Real} (hε : 0 < ε) {f : β -> α}
    (hf : Pairwise fun x y => ε <= dist (f x) (f y)) :
    @IsUniformEmbedding _ _ ⊥ (by infer_instance) f :=
isUniformEmbedding_of_spaced_out (dist_mem_uniformity hε) by simpa using hf

end Metric

/--
Definition of `EMetricSpace.toMetricSpaceOfDist` / `EMetricSpace.toMetricSpaceOfDist` 的定义

English:
abbreviation EMetricSpace.toMetricSpaceOfDist
  signature: {α : Type u} [EMetricSpace α] (dist : α -> α -> Real)
  body: letI := PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist dist_nonneg h
  MetricSpace.ofT0PseudoMetricSpace _

中文:
缩写 广义度量空间.toMetricSpaceOfDist
  签名: {α : 类型u} [广义度量空间 α] (dist : α -> α -> 实数)
  定义体: letI := PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist dist_nonneg h
  MetricSpace.ofT0PseudoMetricSpace _

Depends on / 依赖: MetricSpace, MetricSpace.ofT0PseudoMetricSpace, PseudoEMetricSpace, PseudoEMetricSpace.toPseudoMetricSpaceOfDist, dist_nonneg, ofT0PseudoMetricSpace, toPseudoMetricSpaceOfDist
-/
abbrev EMetricSpace.toMetricSpaceOfDist {α : Type u} [EMetricSpace α] (dist : α -> α -> Real)
    (dist_nonneg : forall x y, 0 <= dist x y) (h : forall x y, edist x y = .ofReal (dist x y)) :
    MetricSpace α :=
  letI := PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist dist_nonneg h
  MetricSpace.ofT0PseudoMetricSpace _

/--
Definition of `EMetricSpace.toMetricSpace` / `EMetricSpace.toMetricSpace` 的定义

English:
abbreviation EMetricSpace.toMetricSpace
  signature: {α : Type u} [EMetricSpace α] (h : forall x y : α, edist x y != ⊤)
  body: EMetricSpace.toMetricSpaceOfDist (ENNReal.toReal <| edist · ·) (by simp) (by simp [h])

中文:
缩写 广义度量空间.toMetricSpace
  签名: {α : 类型u} [广义度量空间 α] (h : 对任意 x y : α, edist x y != ⊤)
  定义体: EMetricSpace.toMetricSpaceOfDist (ENNReal.toReal <| edist · ·) (by simp) (by simp [h])

Depends on / 依赖: EMetricSpace, EMetricSpace.toMetricSpaceOfDist, ENNReal, ENNReal.toReal, toMetricSpaceOfDist, toReal
-/
abbrev EMetricSpace.toMetricSpace {α : Type u} [EMetricSpace α] (h : forall x y : α, edist x y != ⊤) :
    MetricSpace α :=
  EMetricSpace.toMetricSpaceOfDist (ENNReal.toReal <| edist · ·) (by simp) (by simp [h])

/--
Definition of `MetricSpace.induced` / `MetricSpace.induced` 的定义

English:
abbreviation MetricSpace.induced
  signature: {γ β} (f : γ -> β) (hf : Function.Injective f) (m : MetricSpace β)
  body: { PseudoMetricSpace.induced f m.toPseudoMetricSpace with
    eq_of_dist_eq_zero := fun h => hf (dist_eq_zero.1 h) }

中文:
缩写 度量空间.induced
  签名: {γ β} (f : γ -> β) (hf : 函数.单射 f) (m : 度量空间 β)
  定义体: { PseudoMetricSpace.induced f m.toPseudoMetricSpace with
    eq_of_dist_eq_zero := fun h => hf (dist_eq_zero.1 h) }

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.induced, dist_eq_zero, eq_of_dist_eq_zero, induced, m.toPseudoMetricSpace, toPseudoMetricSpace
-/
abbrev MetricSpace.induced {γ β} (f : γ -> β) (hf : Function.Injective f) (m : MetricSpace β) :
    MetricSpace γ :=
  { PseudoMetricSpace.induced f m.toPseudoMetricSpace with
    eq_of_dist_eq_zero := fun h => hf (dist_eq_zero.1 h) }

/--
Definition of `IsUniformEmbedding.comapMetricSpace` / `IsUniformEmbedding.comapMetricSpace` 的定义

English:
abbreviation IsUniformEmbedding.comapMetricSpace
  signature: {α β} [UniformSpace α] [m : MetricSpace β] (f : α -> β)
  body: .replaceUniformity (.induced f h.injective m) h.comap_uniformity.symm

中文:
缩写 是一致嵌入.comapMetricSpace
  签名: {α β} [一致空间 α] [m : 度量空间 β] (f : α -> β)
  定义体: .replaceUniformity (.induced f h.injective m) h.comap_uniformity.symm

Depends on / 依赖: comap_uniformity, h.comap_uniformity.symm, h.injective, induced, injective, replaceUniformity
-/
abbrev IsUniformEmbedding.comapMetricSpace {α β} [UniformSpace α] [m : MetricSpace β] (f : α -> β)
    (h : IsUniformEmbedding f) : MetricSpace α :=
  .replaceUniformity (.induced f h.injective m) h.comap_uniformity.symm

/--
Definition of `Topology.IsEmbedding.comapMetricSpace` / `Topology.IsEmbedding.comapMetricSpace` 的定义

English:
abbreviation Topology.IsEmbedding.comapMetricSpace
  signature: {α β} [TopologicalSpace α] [m : MetricSpace β]
  body: .replaceTopology (.induced f h.injective m) h.eq_induced

中文:
缩写 拓扑.是嵌入.comapMetricSpace
  签名: {α β} [拓扑空间 α] [m : 度量空间 β]
  定义体: .replaceTopology (.induced f h.injective m) h.eq_induced

Depends on / 依赖: eq_induced, h.eq_induced, h.injective, induced, injective, replaceTopology
-/
abbrev Topology.IsEmbedding.comapMetricSpace {α β} [TopologicalSpace α] [m : MetricSpace β]
    (f : α -> β) (h : IsEmbedding f) : MetricSpace α :=
  .replaceTopology (.induced f h.injective m) h.eq_induced

/--
Instance `Subtype.metricSpace` / 实例 `Subtype.metricSpace`

English:
instance Subtype.metricSpace
  signature: {α : Type*} {p : α -> Prop} [MetricSpace α]
  body: .induced Subtype.val Subtype.coe_injective ‹_›

@[to_additive]

中文:
实例 子类型.metricSpace
  签名: {α : 类型} {p : α -> 命题} [度量空间 α]
  定义体: .induced Subtype.val Subtype.coe_injective ‹_›

@[to_additive]

Depends on / 依赖: Subtype, Subtype.coe_injective, Subtype.val, coe_injective, induced
-/
instance Subtype.metricSpace {α : Type*} {p : α -> Prop} [MetricSpace α] :
    MetricSpace (Subtype p) :=
  .induced Subtype.val Subtype.coe_injective ‹_›

@[to_additive]
/--
Instance `MulOpposite.instMetricSpace` / 实例 `MulOpposite.instMetricSpace`

English:
instance MulOpposite.instMetricSpace
  signature: {α : Type*} [MetricSpace α]
  body: MetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

中文:
实例 MulOpposite.instMetricSpace
  签名: {α : 类型} [度量空间 α]
  定义体: MetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

Depends on / 依赖: MetricSpace, MetricSpace.induced, MulOpposite, MulOpposite.unop, MulOpposite.unop_injective, induced, unop_injective
-/
instance MulOpposite.instMetricSpace {α : Type*} [MetricSpace α] : MetricSpace αᵐᵒᵖ :=
  MetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

section Real

/--
Instance `Real.metricSpace` / 实例 `Real.metricSpace`

English:
instance Real.metricSpace
  signature: : MetricSpace Real
  body: .ofT0PseudoMetricSpace Real

中文:
实例 实数.metricSpace
  签名: : 度量空间 实数
  定义体: .ofT0PseudoMetricSpace Real

Depends on / 依赖: ofT0PseudoMetricSpace
-/
instance Real.metricSpace : MetricSpace Real := .ofT0PseudoMetricSpace Real

end Real

section NNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace Real>=0
  body: inferInstanceAs MetricSpace (Subtype _)

中文:
实例 :
  签名: 度量空间 实数>=0
  定义体: inferInstanceAs MetricSpace (Subtype _)
-/
instance : MetricSpace Real>=0 :=
inferInstanceAs MetricSpace (Subtype _)

/--
theorem `NNReal.isUniformEmbedding_coe` / 定理 `NNReal.isUniformEmbedding_coe`

English:
theorem NNReal.isUniformEmbedding_coe
  statement: IsUniformEmbedding NNReal.toReal
  proof: isUniformEmbedding_subtype_val

中文:
定理 非负实数.isUniformEmbedding_coe
  结论: 是一致嵌入 非负实数.to实数
  证明: isUniformEmbedding_subtype_val

Depends on / 依赖: isUniformEmbedding_subtype_val
-/
theorem NNReal.isUniformEmbedding_coe : IsUniformEmbedding NNReal.toReal :=
  isUniformEmbedding_subtype_val

/--
theorem `NNReal.isEmbedding_coe` / 定理 `NNReal.isEmbedding_coe`

English:
theorem NNReal.isEmbedding_coe
  statement: Topology.IsEmbedding NNReal.toReal
  proof: isUniformEmbedding_coe.isEmbedding

中文:
定理 非负实数.isEmbedding_coe
  结论: 拓扑.是嵌入 非负实数.to实数
  证明: isUniformEmbedding_coe.isEmbedding

Depends on / 依赖: isEmbedding, isUniformEmbedding_coe, isUniformEmbedding_coe.isEmbedding
-/
theorem NNReal.isEmbedding_coe : Topology.IsEmbedding NNReal.toReal :=
  isUniformEmbedding_coe.isEmbedding

/--
theorem `NNReal.isClosedEmbedding_coe` / 定理 `NNReal.isClosedEmbedding_coe`

English:
theorem NNReal.isClosedEmbedding_coe
  statement: Topology.IsClosedEmbedding NNReal.toReal
  proof: isClosed_Ici.isClosedEmbedding_subtypeVal

中文:
定理 非负实数.isClosedEmbedding_coe
  结论: 拓扑.是闭嵌入 非负实数.to实数
  证明: isClosed_Ici.isClosedEmbedding_subtypeVal

Depends on / 依赖: isClosedEmbedding_subtypeVal, isClosed_Ici, isClosed_Ici.isClosedEmbedding_subtypeVal
-/
theorem NNReal.isClosedEmbedding_coe : Topology.IsClosedEmbedding NNReal.toReal :=
  isClosed_Ici.isClosedEmbedding_subtypeVal

end NNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MetricSpace
  signature: β] : MetricSpace (ULift β)
  body: fast_instance% MetricSpace.induced ULift.down ULift.down_injective ‹_›

中文:
实例 [度量空间
  签名: β] : 度量空间 (类型层提升 β)
  定义体: fast_instance% MetricSpace.induced ULift.down ULift.down_injective ‹_›

Depends on / 依赖: MetricSpace, MetricSpace.induced, ULift.down, ULift.down_injective, down_injective, fast_instance, induced
-/
instance [MetricSpace β] : MetricSpace (ULift β) :=
  fast_instance% MetricSpace.induced ULift.down ULift.down_injective ‹_›

section Prod

/--
Instance `Prod.metricSpaceMax` / 实例 `Prod.metricSpaceMax`

English:
instance Prod.metricSpaceMax
  signature: [MetricSpace β]
  body: .ofT0PseudoMetricSpace _

中文:
实例 积类型.metricSpaceMax
  签名: [度量空间 β]
  定义体: .ofT0PseudoMetricSpace _

Depends on / 依赖: ofT0PseudoMetricSpace
-/
instance Prod.metricSpaceMax [MetricSpace β] : MetricSpace (γ × β) :=
  .ofT0PseudoMetricSpace _

end Prod

section Pi

open Finset

variable {X : β -> Type*} [Fintype β] [forall b, MetricSpace (X b)]

/--
Instance `metricSpacePi` / 实例 `metricSpacePi`

English:
instance metricSpacePi
  signature: : MetricSpace (forall b, X b)
  body: .ofT0PseudoMetricSpace _

中文:
实例 metricSpacePi
  签名: : 度量空间 (对任意 b, X b)
  定义体: .ofT0PseudoMetricSpace _

Depends on / 依赖: ofT0PseudoMetricSpace
-/
instance metricSpacePi : MetricSpace (forall b, X b) := .ofT0PseudoMetricSpace _

end Pi

namespace Metric

section SecondCountable

open TopologicalSpace

-- TODO: use `Countable` instead of `Encodable`
/--
theorem `secondCountable_of_countable_discretization` / 定理 `secondCountable_of_countable_discretization`

English:
theorem secondCountable_of_countable_discretization
  statement: {α : Type u} [PseudoMetricSpace α]
  proof: by
  refine secondCountable_of_almost_dense_set fun ε ε0 => ?_
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := rangeSplitting F
  refine ⟨range Finv, ⟨countable_range _, fun x => ?_⟩⟩
  let x' := Finv ⟨F x, mem_range_self _⟩
  have : F x' = F x := apply_rangeSplitting F _
  exact ⟨x', mem_range_se

中文:
定理 secondCountable_of_countable_discretization
  结论: {α : 类型u} [伪度量空间 α]
  证明: by
  refine secondCountable_of_almost_dense_set fun ε ε0 => ?_
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := rangeSplitting F
  refine ⟨range Finv, ⟨countable_range _, fun x => ?_⟩⟩
  let x' := Finv ⟨F x, mem_range_self _⟩
  have : F x' = F x := apply_rangeSplitting F _
  exact ⟨x', mem_range_se

Depends on / 依赖: apply_rangeSplitting, countable_range, mem_range_self, rangeSplitting, secondCountable_of_almost_dense_set, this.symm
-/
theorem secondCountable_of_countable_discretization {α : Type u} [PseudoMetricSpace α]
    (H : forall ε > (0 : Real), exists (β : Type*) (_ : Encodable β) (F : α -> β),
      forall x y, F x = F y -> dist x y <= ε) :
    SecondCountableTopology α := by
  refine secondCountable_of_almost_dense_set fun ε ε0 => ?_
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := rangeSplitting F
  refine ⟨range Finv, ⟨countable_range _, fun x => ?_⟩⟩
  let x' := Finv ⟨F x, mem_range_self _⟩
  have : F x' = F x := apply_rangeSplitting F _
  exact ⟨x', mem_range_self _, hF _ _ this.symm⟩

end SecondCountable

end Metric

section EqRel

-- TODO: add `dist_congr` similar to `edist_congr`?
/--
Instance `SeparationQuotient.instDist` / 实例 `SeparationQuotient.instDist`

English:
instance SeparationQuotient.instDist
  signature: {α : Type u} [PseudoMetricSpace α]
  body: lift₂ dist fun x y x' y' hx hy => by rw [dist_edist, dist_edist, ← edist_mk x,
    ← edist_mk x', mk_eq_mk.2 hx, mk_eq_mk.2 hy]

中文:
实例 SeparationQuotient.instDist
  签名: {α : 类型u} [伪度量空间 α]
  定义体: lift₂ dist fun x y x' y' hx hy => by rw [dist_edist, dist_edist, ← edist_mk x,
    ← edist_mk x', mk_eq_mk.2 hx, mk_eq_mk.2 hy]

Depends on / 依赖: dist_edist, edist_mk
-/
instance SeparationQuotient.instDist {α : Type u} [PseudoMetricSpace α] :
    Dist (SeparationQuotient α) where
  dist := lift₂ dist fun x y x' y' hx hy => by rw [dist_edist, dist_edist, ← edist_mk x,
    ← edist_mk x', mk_eq_mk.2 hx, mk_eq_mk.2 hy]

/--
theorem `SeparationQuotient.dist_mk` / 定理 `SeparationQuotient.dist_mk`

English:
theorem SeparationQuotient.dist_mk
  given: {α : Type u} [PseudoMetricSpace α] (p q : α)
  proof: rfl

中文:
定理 SeparationQuotient.dist_mk
  条件: {α : 类型u} [伪度量空间 α] (p q : α)
  证明: rfl
-/
theorem SeparationQuotient.dist_mk {α : Type u} [PseudoMetricSpace α] (p q : α) :
    dist (mk p) (mk q) = dist p q :=
  rfl

/--
Instance `SeparationQuotient.instMetricSpace` / 实例 `SeparationQuotient.instMetricSpace`

English:
instance SeparationQuotient.instMetricSpace
  signature: {α : Type u} [PseudoMetricSpace α]
  body: EMetricSpace.toMetricSpaceOfDist dist (surjective_mk.forall₂.2 fun _ _ => dist_nonneg)
    surjective_mk.forall₂.2 edist_dist

中文:
实例 SeparationQuotient.instMetricSpace
  签名: {α : 类型u} [伪度量空间 α]
  定义体: EMetricSpace.toMetricSpaceOfDist dist (surjective_mk.forall₂.2 fun _ _ => dist_nonneg)
    surjective_mk.forall₂.2 edist_dist

Depends on / 依赖: EMetricSpace, EMetricSpace.toMetricSpaceOfDist, dist_nonneg, edist_dist, surjective_mk, surjective_mk.forall, toMetricSpaceOfDist
-/
instance SeparationQuotient.instMetricSpace {α : Type u} [PseudoMetricSpace α] :
    MetricSpace (SeparationQuotient α) :=
EMetricSpace.toMetricSpaceOfDist dist (surjective_mk.forall₂.2 fun _ _ => dist_nonneg)
    surjective_mk.forall₂.2 edist_dist

end EqRel

namespace PseudoEMetricSpace

open ENNReal

variable {X : Type*} (m : PseudoEMetricSpace X) (d : X -> X -> Real>=0∞) (hd : d = edist)

-- See note [forgetful inheritance]
-- See note [reducible non-instances]
/--
Definition of `replaceEDist` / `replaceEDist` 的定义

English:
abbreviation replaceEDist
  signature: : PseudoEMetricSpace X where
  body: d
  edist_self := by simp [hd]
  edist_comm := by simp [hd, edist_comm]
  edist_triangle := by simp [hd, edist_triangle]
  uniformity_edist := by simp [hd, uniformity_edist]
  __ := m

中文:
缩写 replaceEDist
  签名: : PseudoEMetric空间 X where
  定义体: d
  edist_self := by simp [hd]
  edist_comm := by simp [hd, edist_comm]
  edist_triangle := by simp [hd, edist_triangle]
  uniformity_edist := by simp [hd, uniformity_edist]
  __ := m
-/
abbrev replaceEDist : PseudoEMetricSpace X where
  edist := d
  edist_self := by simp [hd]
  edist_comm := by simp [hd, edist_comm]
  edist_triangle := by simp [hd, edist_triangle]
  uniformity_edist := by simp [hd, uniformity_edist]
  __ := m

/--
lemma `replaceEDist_eq` / 引理 `replaceEDist_eq`

English:
lemma replaceEDist_eq
  statement: m.replaceEDist d hd = m
  proof: by ext : 2; exact hd

中文:
引理 replaceEDist_eq
  结论: m.replaceEDist d hd = m
  证明: by ext : 2; exact hd
-/
lemma replaceEDist_eq : m.replaceEDist d hd = m := by ext : 2; exact hd

-- Check uniformity is unchanged
example : (replaceEDist m d hd).toUniformSpace = m.toUniformSpace := by
  dsimp +instances [replaceEDist]

end PseudoEMetricSpace

namespace PseudoMetricSpace
variable {X : Type*} (m : PseudoMetricSpace X) (d : X -> X -> Real) (hd : d = dist)

-- See note [forgetful inheritance]
-- See note [reducible non-instances]
/--
Definition of `replaceDist` / `replaceDist` 的定义

English:
abbreviation replaceDist
  signature: : PseudoMetricSpace X where
  body: d
  dist_self := by simp [hd]
  dist_comm := by simp [hd, dist_comm]
  dist_triangle := by simp [hd, dist_triangle]
  edist_dist := by simp [hd, edist_dist]
  uniformity_dist := by simp [hd, uniformity_dist]
  cobounded_sets := by simp [hd, cobounded_sets]
  __ := m

中文:
缩写 replaceDist
  签名: : 伪度量空间 X where
  定义体: d
  dist_self := by simp [hd]
  dist_comm := by simp [hd, dist_comm]
  dist_triangle := by simp [hd, dist_triangle]
  edist_dist := by simp [hd, edist_dist]
  uniformity_dist := by simp [hd, uniformity_dist]
  cobounded_sets := by simp [hd, cobounded_sets]
  __ := m
-/
abbrev replaceDist : PseudoMetricSpace X where
  dist := d
  dist_self := by simp [hd]
  dist_comm := by simp [hd, dist_comm]
  dist_triangle := by simp [hd, dist_triangle]
  edist_dist := by simp [hd, edist_dist]
  uniformity_dist := by simp [hd, uniformity_dist]
  cobounded_sets := by simp [hd, cobounded_sets]
  __ := m

/--
lemma `replaceDist_eq` / 引理 `replaceDist_eq`

English:
lemma replaceDist_eq
  statement: m.replaceDist d hd = m
  proof: by ext : 2; exact hd

中文:
引理 replaceDist_eq
  结论: m.replaceDist d hd = m
  证明: by ext : 2; exact hd
-/
lemma replaceDist_eq : m.replaceDist d hd = m := by ext : 2; exact hd

-- Check uniformity is unchanged
example : (replaceDist m d hd).toUniformSpace = m.toUniformSpace := by
  dsimp +instances [replaceDist]

-- Check Bornology is unchanged
example : (replaceDist m d hd).toBornology = m.toBornology := by
  dsimp +instances [replaceDist]

end PseudoMetricSpace

namespace EMetricSpace

open ENNReal

variable {X : Type*} (m : EMetricSpace X) (d : X -> X -> Real>=0∞) (hd : d = edist)

-- See note [forgetful inheritance]
-- See note [reducible non-instances]
/--
Definition of `replaceEDist` / `replaceEDist` 的定义

English:
abbreviation replaceEDist
  signature: : EMetricSpace X where
  body: d
  edist_self := by simp [hd]
  edist_comm := by simp [hd, edist_comm]
  edist_triangle := by simp [hd, edist_triangle]
  eq_of_edist_eq_zero := by simp [hd]

中文:
缩写 replaceEDist
  签名: : 广义度量空间 X where
  定义体: d
  edist_self := by simp [hd]
  edist_comm := by simp [hd, edist_comm]
  edist_triangle := by simp [hd, edist_triangle]
  eq_of_edist_eq_zero := by simp [hd]
-/
noncomputable abbrev replaceEDist : EMetricSpace X where
  edist := d
  edist_self := by simp [hd]
  edist_comm := by simp [hd, edist_comm]
  edist_triangle := by simp [hd, edist_triangle]
  eq_of_edist_eq_zero := by simp [hd]

/--
lemma `replaceEDist_eq` / 引理 `replaceEDist_eq`

English:
lemma replaceEDist_eq
  statement: m.replaceEDist d hd = m
  proof: by ext : 2; exact hd

中文:
引理 replaceEDist_eq
  结论: m.replaceEDist d hd = m
  证明: by ext : 2; exact hd
-/
lemma replaceEDist_eq : m.replaceEDist d hd = m := by ext : 2; exact hd

-- Check uniformity is unchanged
example : (replaceEDist m d hd).toUniformSpace = m.toUniformSpace := by
  simp +instances [replaceEDist_eq]

end EMetricSpace

namespace MetricSpace
variable {X : Type*} (m : MetricSpace X) (d : X -> X -> Real) (hd : d = dist)

-- See note [forgetful inheritance]
-- See note [reducible non-instances]
/--
Definition of `replaceDist` / `replaceDist` 的定义

English:
abbreviation replaceDist
  signature: : MetricSpace X where
  body: d
  dist_self := by simp [hd]
  dist_comm := by simp [hd, dist_comm]
  dist_triangle := by simp [hd, dist_triangle]
  eq_of_dist_eq_zero := by simp [hd]

中文:
缩写 replaceDist
  签名: : 度量空间 X where
  定义体: d
  dist_self := by simp [hd]
  dist_comm := by simp [hd, dist_comm]
  dist_triangle := by simp [hd, dist_triangle]
  eq_of_dist_eq_zero := by simp [hd]
-/
abbrev replaceDist : MetricSpace X where
  dist := d
  dist_self := by simp [hd]
  dist_comm := by simp [hd, dist_comm]
  dist_triangle := by simp [hd, dist_triangle]
  eq_of_dist_eq_zero := by simp [hd]

/--
lemma `replaceDist_eq` / 引理 `replaceDist_eq`

English:
lemma replaceDist_eq
  statement: m.replaceDist d hd = m
  proof: by ext : 2; exact hd

中文:
引理 replaceDist_eq
  结论: m.replaceDist d hd = m
  证明: by ext : 2; exact hd
-/
lemma replaceDist_eq : m.replaceDist d hd = m := by ext : 2; exact hd

-- Check uniformity is unchanged
example : (replaceDist m d hd).toUniformSpace = m.toUniformSpace := by
  simp +instances [replaceDist_eq]

-- Check Bornology is unchanged
example : (replaceDist m d hd).toBornology = m.toBornology := by
  simp +instances [replaceDist_eq]

end MetricSpace
