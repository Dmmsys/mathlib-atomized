/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Sets.Opens

/-!
# Polish spaces

A topological space is Polish if its topology is second-countable and there exists a compatible
complete metric. This is the class of spaces that is well-behaved with respect to measure theory.
In this file, we establish the basic properties of Polish spaces.

## Main definitions and results

* `PolishSpace α` is a mixin typeclass on a topological space, requiring that the topology is
  second-countable and compatible with a complete metric. To endow the space with such a metric,
  use in a proof `letI := upgradeIsCompletelyMetrizable α`.
* `IsClosed.polishSpace`: a closed subset of a Polish space is Polish.
* `IsOpen.polishSpace`: an open subset of a Polish space is Polish.
* `exists_nat_nat_continuous_surjective`: any nonempty Polish space is the continuous image
  of the fundamental Polish space `ℕ → ℕ`.

A fundamental property of Polish spaces is that one can put finer topologies, still Polish,
with additional properties:

* `exists_polishSpace_forall_le`: on a topological space, consider countably many topologies
  `t n`, all Polish and finer than the original topology. Then there exists another Polish
  topology which is finer than all the `t n`.
* `IsClopenable s` is a property of a subset `s` of a topological space, requiring that there
  exists a finer topology, which is Polish, for which `s` becomes open and closed. We show that
  this property is satisfied for open sets, closed sets, for complements, and for countable unions.
  Once Borel-measurable sets are defined in later files, it will follow that any Borel-measurable
  set is clopenable. Once the Lusin-Souslin theorem is proved using analytic sets, we will even
  show that a set is clopenable if and only if it is Borel-measurable, see
  `isClopenable_iff_measurableSet`.
-/

@[expose] public section

noncomputable section

open Filter Function Metric TopologicalSpace Set Topology
open scoped Uniformity

variable {α : Type*} {β : Type*}

/-! ### Basic properties of Polish spaces -/


/--
Definition of `PolishSpace` / `PolishSpace` 的定义

English:
class PolishSpace
  parameters: (α : Type*) [h : TopologicalSpace α]
  extends: SecondCountableTopology α, IsCompletelyMetrizableSpace α
  (no additional axioms)

中文:
类 PolishSpace
  参数: (α : 类型) [h : TopologicalSpace α]
  继承: SecondCountableTopology α, IsCompletelyMetrizableSpace α
  (无附加公理)
-/
class PolishSpace (α : Type*) [h : TopologicalSpace α] : Prop
    extends SecondCountableTopology α, IsCompletelyMetrizableSpace α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [SeparableSpace α] [IsCompletelyMetrizableSpace α] :
  body: by
  let := upgradeIsCompletelyMetrizable α
  have := UniformSpace.secondCountable_of_separable α
  constructor

中文:
实例 [TopologicalSpace
  签名: α] [SeparableSpace α] [IsCompletelyMetrizableSpace α] :
  定义体: by
  let := upgradeIsCompletelyMetrizable α
  have := UniformSpace.secondCountable_of_separable α
  constructor

Depends on / 依赖: UniformSpace, UniformSpace.secondCountable_of_separable, secondCountable_of_separable, upgradeIsCompletelyMetrizable
-/
instance [TopologicalSpace α] [SeparableSpace α] [IsCompletelyMetrizableSpace α] :
    PolishSpace α := by
  let := upgradeIsCompletelyMetrizable α
  have := UniformSpace.secondCountable_of_separable α
  constructor

namespace PolishSpace

/--
theorem `exists_nat_nat_continuous_surjective` / 定理 `exists_nat_nat_continuous_surjective`

English:
theorem exists_nat_nat_continuous_surjective
  statement: (α : Type*) [TopologicalSpace α] [PolishSpace α]
  proof: letI := upgradeIsCompletelyMetrizable α
  exists_nat_nat_continuous_surjective_of_completeSpace α

中文:
定理 exists_nat_nat_continuous_surjective
  结论: (α : 类型) [TopologicalSpace α] [PolishSpace α]
  证明: letI := upgradeIsCompletelyMetrizable α
  exists_nat_nat_continuous_surjective_of_completeSpace α

Depends on / 依赖: exists_nat_nat_continuous_surjective_of_completeSpace, upgradeIsCompletelyMetrizable
-/
theorem exists_nat_nat_continuous_surjective (α : Type*) [TopologicalSpace α] [PolishSpace α]
    [Nonempty α] : exists f : (Nat -> Nat) -> α, Continuous f ∧ Surjective f :=
  letI := upgradeIsCompletelyMetrizable α
  exists_nat_nat_continuous_surjective_of_completeSpace α

/--
theorem `_root_.Topology.IsClosedEmbedding.polishSpace` / 定理 `_root_.Topology.IsClosedEmbedding.polishSpace`

English:
theorem _root_.Topology.IsClosedEmbedding.polishSpace
  statement: [TopologicalSpace α] [TopologicalSpace β]
  proof: by
  let := upgradeIsCompletelyMetrizable β
  let : MetricSpace α := hf.isEmbedding.comapMetricSpace f
  have : SecondCountableTopology α := hf.isEmbedding.secondCountableTopology
  have : CompleteSpace α := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]


中文:
定理 _root_.Topology.IsClosedEmbedding.polishSpace
  结论: [TopologicalSpace α] [TopologicalSpace β]
  证明: by
  let := upgradeIsCompletelyMetrizable β
  let : MetricSpace α := hf.isEmbedding.comapMetricSpace f
  have : SecondCountableTopology α := hf.isEmbedding.secondCountableTopology
  have : CompleteSpace α := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]


Depends on / 依赖: CompleteSpace, MetricSpace, SecondCountableTopology, comapMetricSpace, completeSpace_iff_isComplete_range, hf.isClosed_range.isComplete, hf.isEmbedding.comapMetricSpace, hf.isEmbedding.secondCountableTopology, hf.isEmbedding.to_isometry.isUniformInducing, infer_instance, isClosed_range, isComplete, isEmbedding, isUniformInducing, secondCountableTopology, to_isometry, upgradeIsCompletelyMetrizable
-/
theorem _root_.Topology.IsClosedEmbedding.polishSpace [TopologicalSpace α] [TopologicalSpace β]
    [PolishSpace β] {f : α -> β} (hf : IsClosedEmbedding f) : PolishSpace α := by
  let := upgradeIsCompletelyMetrizable β
  let : MetricSpace α := hf.isEmbedding.comapMetricSpace f
  have : SecondCountableTopology α := hf.isEmbedding.secondCountableTopology
  have : CompleteSpace α := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

/--
theorem `_root_.Equiv.polishSpace_induced` / 定理 `_root_.Equiv.polishSpace_induced`

English:
theorem _root_.Equiv.polishSpace_induced
  given: [t : TopologicalSpace β] [PolishSpace β] (f : α ≃ β)
  proof: letI : TopologicalSpace α := t.induced f
  (f.toHomeomorphOfIsInducing ⟨rfl⟩).isClosedEmbedding.polishSpace

中文:
定理 _root_.Equiv.polishSpace_induced
  条件: [t : TopologicalSpace β] [PolishSpace β] (f : α ≃ β)
  证明: letI : TopologicalSpace α := t.induced f
  (f.toHomeomorphOfIsInducing ⟨rfl⟩).isClosedEmbedding.polishSpace

Depends on / 依赖: TopologicalSpace, f.toHomeomorphOfIsInducing, induced, isClosedEmbedding, isClosedEmbedding.polishSpace, polishSpace, t.induced, toHomeomorphOfIsInducing
-/
theorem _root_.Equiv.polishSpace_induced [t : TopologicalSpace β] [PolishSpace β] (f : α ≃ β) :
    @PolishSpace α (t.induced f) :=
  letI : TopologicalSpace α := t.induced f
  (f.toHomeomorphOfIsInducing ⟨rfl⟩).isClosedEmbedding.polishSpace

/--
theorem `_root_.IsClosed.polishSpace` / 定理 `_root_.IsClosed.polishSpace`

English:
theorem _root_.IsClosed.polishSpace
  statement: [TopologicalSpace α] [PolishSpace α] {s : Set α}
  proof: hs.isClosedEmbedding_subtypeVal.polishSpace

中文:
定理 _root_.IsClosed.polishSpace
  结论: [TopologicalSpace α] [PolishSpace α] {s : Set α}
  证明: hs.isClosedEmbedding_subtypeVal.polishSpace

Depends on / 依赖: hs.isClosedEmbedding_subtypeVal.polishSpace, isClosedEmbedding_subtypeVal, polishSpace
-/
theorem _root_.IsClosed.polishSpace [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsClosed s) : PolishSpace s :=
  hs.isClosedEmbedding_subtypeVal.polishSpace

/--
theorem `_root_.CompletePseudometrizable.iInf` / 定理 `_root_.CompletePseudometrizable.iInf`

English:
theorem _root_.CompletePseudometrizable.iInf
  statement: {ι : Type*} [Countable ι]
  proof: by
  choose u hcomp hcount hut using ht
  obtain rfl : t = fun i => (u i).toTopologicalSpace := (funext hut).symm
  refine ⟨⨅ i, u i, .iInf hcomp ht₀, ?_, UniformSpace.toTopologicalSpace_iInf⟩
  rw [iInf_uniformity]
  infer_instance

中文:
定理 _root_.CompletePseudometrizable.iInf
  结论: {ι : 类型} [Countable ι]
  证明: by
  choose u hcomp hcount hut using ht
  obtain rfl : t = fun i => (u i).toTopologicalSpace := (funext hut).symm
  refine ⟨⨅ i, u i, .iInf hcomp ht₀, ?_, UniformSpace.toTopologicalSpace_iInf⟩
  rw [iInf_uniformity]
  infer_instance
-/
protected theorem _root_.CompletePseudometrizable.iInf {ι : Type*} [Countable ι]
    {t : ι -> TopologicalSpace α} (ht₀ : exists t₀, @T2Space α t₀ ∧ forall i, t i <= t₀)
    (ht : forall i, exists u : UniformSpace α, CompleteSpace α ∧ 𝓤[u].IsCountablyGenerated ∧
      u.toTopologicalSpace = t i) :
    exists u : UniformSpace α, CompleteSpace α ∧
      𝓤[u].IsCountablyGenerated ∧ u.toTopologicalSpace = ⨅ i, t i := by
  choose u hcomp hcount hut using ht
  obtain rfl : t = fun i => (u i).toTopologicalSpace := (funext hut).symm
  refine ⟨⨅ i, u i, .iInf hcomp ht₀, ?_, UniformSpace.toTopologicalSpace_iInf⟩
  rw [iInf_uniformity]
  infer_instance

/--
theorem `iInf` / 定理 `iInf`

English:
theorem iInf
  statement: {ι : Type*} [Countable ι] {t : ι -> TopologicalSpace α}
  proof: by
  rcases ht₀ with ⟨i₀, hi₀⟩
  rcases CompletePseudometrizable.iInf ⟨t i₀, letI := t i₀; haveI := ht i₀; inferInstance, hi₀⟩
    fun i =>
      letI := t i; haveI := ht i; letI := upgradeIsCompletelyMetrizable α
      ⟨inferInstance, inferInstance, inferInstance, rfl⟩
    with ⟨u, hcomp, hcount, h

中文:
定理 iInf
  结论: {ι : 类型} [Countable ι] {t : ι -> TopologicalSpace α}
  证明: by
  rcases ht₀ with ⟨i₀, hi₀⟩
  rcases CompletePseudometrizable.iInf ⟨t i₀, letI := t i₀; haveI := ht i₀; inferInstance, hi₀⟩
    fun i =>
      letI := t i; haveI := ht i; letI := upgradeIsCompletelyMetrizable α
      ⟨inferInstance, inferInstance, inferInstance, rfl⟩
    with ⟨u, hcomp, hcount, h
-/
protected theorem iInf {ι : Type*} [Countable ι] {t : ι -> TopologicalSpace α}
    (ht₀ : exists i₀, forall i, t i <= t i₀) (ht : forall i, @PolishSpace α (t i)) : @PolishSpace α (⨅ i, t i) := by
  rcases ht₀ with ⟨i₀, hi₀⟩
  rcases CompletePseudometrizable.iInf ⟨t i₀, letI := t i₀; haveI := ht i₀; inferInstance, hi₀⟩
    fun i =>
      letI := t i; haveI := ht i; letI := upgradeIsCompletelyMetrizable α
      ⟨inferInstance, inferInstance, inferInstance, rfl⟩
    with ⟨u, hcomp, hcount, htop⟩
  rw [← htop]
  have : @SecondCountableTopology α u.toTopologicalSpace :=
    htop.symm ▸ secondCountableTopology_iInf fun i => letI := t i; (ht i).toSecondCountableTopology
  have : @T1Space α u.toTopologicalSpace :=
    htop.symm ▸ t1Space_antitone (iInf_le _ i₀) (by let := t i₀; have := ht i₀; infer_instance)
  infer_instance

/--
theorem `exists_polishSpace_forall_le` / 定理 `exists_polishSpace_forall_le`

English:
theorem exists_polishSpace_forall_le
  statement: {ι : Type*} [Countable ι] [t : TopologicalSpace α]
  proof: ⟨⨅ i : Option ι, i.elim t m, fun i => iInf_le _ (some i), iInf_le _ none,
.iInf ⟨none, Option.forall.2 ⟨le_rfl, hm⟩⟩ Option.forall.2 ⟨p, h'm⟩⟩

中文:
定理 exists_polishSpace_forall_le
  结论: {ι : 类型} [Countable ι] [t : TopologicalSpace α]
  证明: ⟨⨅ i : Option ι, i.elim t m, fun i => iInf_le _ (some i), iInf_le _ none,
.iInf ⟨none, Option.forall.2 ⟨le_rfl, hm⟩⟩ Option.forall.2 ⟨p, h'm⟩⟩

Depends on / 依赖: Option.forall, i.elim, iInf_le, le_rfl
-/
theorem exists_polishSpace_forall_le {ι : Type*} [Countable ι] [t : TopologicalSpace α]
    [p : PolishSpace α] (m : ι -> TopologicalSpace α) (hm : forall n, m n <= t)
    (h'm : forall n, @PolishSpace α (m n)) :
    exists t' : TopologicalSpace α, (forall n, t' <= m n) ∧ t' <= t ∧ @PolishSpace α t' :=
  ⟨⨅ i : Option ι, i.elim t m, fun i => iInf_le _ (some i), iInf_le _ none,
.iInf ⟨none, Option.forall.2 ⟨le_rfl, hm⟩⟩ Option.forall.2 ⟨p, h'm⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PolishSpace ENNReal
  body: ENNReal.orderIsoUnitIntervalBirational.toHomeomorph.isClosedEmbedding.polishSpace

中文:
实例 :
  签名: PolishSpace ENN实数
  定义体: ENNReal.orderIsoUnitIntervalBirational.toHomeomorph.isClosedEmbedding.polishSpace

Depends on / 依赖: ENNReal, ENNReal.orderIsoUnitIntervalBirational.toHomeomorph.isClosedEmbedding.polishSpace, isClosedEmbedding, orderIsoUnitIntervalBirational, polishSpace, toHomeomorph
-/
instance : PolishSpace ENNReal :=
  ENNReal.orderIsoUnitIntervalBirational.toHomeomorph.isClosedEmbedding.polishSpace

end PolishSpace

/-!
### An open subset of a Polish space is Polish

To prove this fact, one needs to construct another metric, giving rise to the same topology,
for which the open subset is complete. This is not obvious, as for instance `(0,1) ⊆ ℝ` is not
complete for the usual metric of `ℝ`: one should build a new metric that blows up close to the
boundary.
-/

namespace TopologicalSpace.Opens

variable [MetricSpace α] {s : Opens α}

/--
Definition of `CompleteCopy` / `CompleteCopy` 的定义

English:
definition CompleteCopy
  signature: {α : Type*} [MetricSpace α] (s : Opens α)
  body: s

中文:
定义 CompleteCopy
  签名: {α : 类型} [MetricSpace α] (s : Opens α)
  定义体: s
-/
def CompleteCopy {α : Type*} [MetricSpace α] (s : Opens α) : Type _ := s

namespace CompleteCopy

/--
Instance `instDist` / 实例 `instDist`

English:
instance instDist
  signature: : Dist (CompleteCopy s) where
  body: dist x.1 y.1 + abs (1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ)

中文:
实例 instDist
  签名: : Dist (CompleteCopy s) where
  定义体: dist x.1 y.1 + abs (1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ)

Depends on / 依赖: infDist
-/
instance instDist : Dist (CompleteCopy s) where
  dist x y := dist x.1 y.1 + abs (1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ)

/--
theorem `dist_eq` / 定理 `dist_eq`

English:
theorem dist_eq
  given: (x y : CompleteCopy s)
  proof: rfl

中文:
定理 dist_eq
  条件: (x y : CompleteCopy s)
  证明: rfl
-/
theorem dist_eq (x y : CompleteCopy s) :
    dist x y = dist x.1 y.1 + abs (1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ) :=
  rfl

/--
theorem `dist_val_le_dist` / 定理 `dist_val_le_dist`

English:
theorem dist_val_le_dist
  given: (x y : CompleteCopy s)
  statement: dist x.1 y.1 <= dist x y
  proof: le_add_of_nonneg_right (abs_nonneg _)

中文:
定理 dist_val_le_dist
  条件: (x y : CompleteCopy s)
  结论: dist x.1 y.1 <= dist x y
  证明: le_add_of_nonneg_right (abs_nonneg _)

Depends on / 依赖: abs_nonneg, le_add_of_nonneg_right
-/
theorem dist_val_le_dist (x y : CompleteCopy s) : dist x.1 y.1 <= dist x y :=
  le_add_of_nonneg_right (abs_nonneg _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (CompleteCopy s)
  body: inferInstanceAs (TopologicalSpace s)

中文:
实例 :
  签名: TopologicalSpace (CompleteCopy s)
  定义体: inferInstanceAs (TopologicalSpace s)

Depends on / 依赖: TopologicalSpace
-/
instance : TopologicalSpace (CompleteCopy s) := inferInstanceAs (TopologicalSpace s)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SecondCountableTopology
  signature: α] : SecondCountableTopology (CompleteCopy s)
  body: inferInstanceAs (SecondCountableTopology s)

中文:
实例 [SecondCountableTopology
  签名: α] : SecondCountableTopology (CompleteCopy s)
  定义体: inferInstanceAs (SecondCountableTopology s)

Depends on / 依赖: SecondCountableTopology
-/
instance [SecondCountableTopology α] : SecondCountableTopology (CompleteCopy s) :=
  inferInstanceAs (SecondCountableTopology s)
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T0Space (CompleteCopy s)
  body: inferInstanceAs (T0Space s)

中文:
实例 :
  签名: T0Space (CompleteCopy s)
  定义体: inferInstanceAs (T0Space s)

Depends on / 依赖: T0Space
-/
instance : T0Space (CompleteCopy s) := inferInstanceAs (T0Space s)

/--
Instance `instMetricSpace` / 实例 `instMetricSpace`

English:
instance instMetricSpace
  signature: : MetricSpace (CompleteCopy s)
  body: by
  refine @MetricSpace.ofT0PseudoMetricSpace (CompleteCopy s)
    (.ofDistTopology dist (fun _ => ?_) (fun _ _ => ?_) (fun x y z => ?_) fun t => ?_) _
  · simp only [dist_eq, dist_self, one_div, sub_self, abs_zero, add_zero]
  · simp only [dist_eq, dist_comm, abs_sub_comm]
  · calc
      dist x z 

中文:
实例 instMetricSpace
  签名: : MetricSpace (CompleteCopy s)
  定义体: by
  refine @MetricSpace.ofT0PseudoMetricSpace (CompleteCopy s)
    (.ofDistTopology dist (fun _ => ?_) (fun _ _ => ?_) (fun x y z => ?_) fun t => ?_) _
  · simp only [dist_eq, dist_self, one_div, sub_self, abs_zero, add_zero]
  · simp only [dist_eq, dist_comm, abs_sub_comm]
  · calc
      dist x z 

Depends on / 依赖: CompleteCopy, MetricSpace, MetricSpace.ofT0PseudoMetricSpace, abs_sub_comm, abs_zero, add_le_add, add_zero, dist_comm, dist_eq, dist_self, dist_triangle, infDist, ofDistTopology, ofT0PseudoMetricSpace, one_div, sub_self
-/
instance instMetricSpace : MetricSpace (CompleteCopy s) := by
  refine @MetricSpace.ofT0PseudoMetricSpace (CompleteCopy s)
    (.ofDistTopology dist (fun _ => ?_) (fun _ _ => ?_) (fun x y z => ?_) fun t => ?_) _
  · simp only [dist_eq, dist_self, one_div, sub_self, abs_zero, add_zero]
  · simp only [dist_eq, dist_comm, abs_sub_comm]
  · calc
      dist x z = dist x.1 z.1 + |1 / infDist x.1 sᶜ - 1 / infDist z.1 sᶜ| := rfl
      _ <= dist x.1 y.1 + dist y.1 z.1 + (|1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ| +
            |1 / infDist y.1 sᶜ - 1 / infDist z.1 sᶜ|) :=
        add_le_add (dist_triangle _ _ _) (dist_triangle (1 / infDist _ _) _ _)
      _ = dist x y + dist y z := add_add_add_comm ..
  · refine ⟨fun h x hx => ?_, fun h => isOpen_iff_mem_nhds.2 fun x hx => ?_⟩
    · rcases (Metric.isOpen_iff (α := s)).1 h x hx with ⟨ε, ε0, hε⟩
exact ⟨ε, ε0, fun y hy => hε (dist_comm _ _).trans_lt (dist_val_le_dist _ _).trans_lt hy⟩
    · rcases h x hx with ⟨ε, ε0, hε⟩
      simp only [dist_eq, one_div] at hε
      have : Tendsto (fun y : s => dist x.1 y.1 + |(infDist x.1 sᶜ)⁻¹ - (infDist y.1 sᶜ)⁻¹|)
          (𝓝 x) (𝓝 (dist x.1 x.1 + |(infDist x.1 sᶜ)⁻¹ - (infDist x.1 sᶜ)⁻¹|)) := by
        refine (tendsto_const_nhds.dist continuous_subtype_val.continuousAt).add
          (tendsto_const_nhds.sub <| ?_).abs
        refine (continuousAt_inv_infDist_pt ?_).comp continuous_subtype_val.continuousAt
        rw [s.isOpen.isClosed_compl.closure_eq]; rw [mem_compl_iff]; rw [not_not]
        exact x.2
      simp only [dist_self, sub_self, abs_zero, zero_add] at this
      exact mem_of_superset (this <| gt_mem_nhds ε0) hε

/--
Instance `instCompleteSpace` / 实例 `instCompleteSpace`

English:
instance instCompleteSpace
  signature: [CompleteSpace α]
  body: by
  refine Metric.complete_of_convergent_controlled_sequences ((1 / 2) ^ ·) (by simp) fun u hu => ?_
  have A : CauchySeq fun n => (u n).1 := by
    refine cauchySeq_of_le_tendsto_0 (fun n : Nat => (1 / 2) ^ n) (fun n m N hNn hNm => ?_) ?_
    · exact (dist_val_le_dist (u n) (u m)).trans (hu N n m 

中文:
实例 instCompleteSpace
  签名: [CompleteSpace α]
  定义体: by
  refine Metric.complete_of_convergent_controlled_sequences ((1 / 2) ^ ·) (by simp) fun u hu => ?_
  have A : CauchySeq fun n => (u n).1 := by
    refine cauchySeq_of_le_tendsto_0 (fun n : Nat => (1 / 2) ^ n) (fun n m N hNn hNm => ?_) ?_
    · exact (dist_val_le_dist (u n) (u m)).trans (hu N n m 

Depends on / 依赖: CauchySeq, Metric, Metric.complete_of_convergent_controlled_sequences, Tendsto, cauchySeq_of_le_tendsto_0, cauchySeq_tendsto_of_complete, complete_of_convergent_controlled_sequences, dist_val_le_dist, tendsto_pow_atTop_nhds_zero_of_lt_one
-/
instance instCompleteSpace [CompleteSpace α] : CompleteSpace (CompleteCopy s) := by
  refine Metric.complete_of_convergent_controlled_sequences ((1 / 2) ^ ·) (by simp) fun u hu => ?_
  have A : CauchySeq fun n => (u n).1 := by
    refine cauchySeq_of_le_tendsto_0 (fun n : Nat => (1 / 2) ^ n) (fun n m N hNn hNm => ?_) ?_
    · exact (dist_val_le_dist (u n) (u m)).trans (hu N n m hNn hNm).le
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by simp) (by norm_num)
  obtain ⟨x, xlim⟩ : exists x, Tendsto (fun n => (u n).1) atTop (𝓝 x) := cauchySeq_tendsto_of_complete A
  by_cases xs : x in s
  · exact ⟨⟨x, xs⟩, tendsto_subtype_rng.2 xlim⟩
  obtain ⟨C, hC⟩ : exists C, forall n, 1 / infDist (u n).1 sᶜ < C := by
    refine ⟨(1 / 2) ^ 0 + 1 / infDist (u 0).1 sᶜ, fun n => ?_⟩
    rw [← sub_lt_iff_lt_add]
    calc
      _ <= |1 / infDist (u n).1 sᶜ - 1 / infDist (u 0).1 sᶜ| := le_abs_self _
      _ = |1 / infDist (u 0).1 sᶜ - 1 / infDist (u n).1 sᶜ| := abs_sub_comm _ _
      _ <= dist (u 0) (u n) := le_add_of_nonneg_left dist_nonneg
      _ < (1 / 2) ^ 0 := hu 0 0 n le_rfl n.zero_le
  have Cpos : 0 < C := lt_of_le_of_lt (div_nonneg zero_le_one infDist_nonneg) (hC 0)
  have Hmem : forall {y}, y in s ↔ 0 < infDist y sᶜ := fun {y} => by
    rw [← s.isOpen.isClosed_compl.notMem_iff_infDist_pos ⟨x]; rw [xs⟩]; exact not_not.symm
  have I : forall n, 1 / C <= infDist (u n).1 sᶜ := fun n => by
    have : 0 < infDist (u n).1 sᶜ := Hmem.1 (u n).2
    rw [div_le_iff₀' Cpos]
    exact (div_le_iff₀ this).1 (hC n).le
  have I' : 1 / C <= infDist x sᶜ :=
    have : Tendsto (fun n => infDist (u n).1 sᶜ) atTop (𝓝 (infDist x sᶜ)) :=
      ((continuous_infDist_pt (sᶜ : Set α)).tendsto x).comp xlim
    ge_of_tendsto' this I
  exact absurd (Hmem.2 <| lt_of_lt_of_le (div_pos one_pos Cpos) I') xs

/--
theorem `_root_.IsOpen.polishSpace` / 定理 `_root_.IsOpen.polishSpace`

English:
theorem _root_.IsOpen.polishSpace
  statement: {α : Type*} [TopologicalSpace α] [PolishSpace α] {s : Set α}
  proof: by
  let := upgradeIsCompletelyMetrizable α
  lift s to Opens α using hs
  exact inferInstanceAs (PolishSpace s.CompleteCopy)

中文:
定理 _root_.IsOpen.polishSpace
  结论: {α : 类型} [TopologicalSpace α] [PolishSpace α] {s : Set α}
  证明: by
  let := upgradeIsCompletelyMetrizable α
  lift s to Opens α using hs
  exact inferInstanceAs (PolishSpace s.CompleteCopy)

Depends on / 依赖: CompleteCopy, PolishSpace, s.CompleteCopy, upgradeIsCompletelyMetrizable
-/
theorem _root_.IsOpen.polishSpace {α : Type*} [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsOpen s) : PolishSpace s := by
  let := upgradeIsCompletelyMetrizable α
  lift s to Opens α using hs
  exact inferInstanceAs (PolishSpace s.CompleteCopy)

end CompleteCopy

end TopologicalSpace.Opens

namespace PolishSpace

/-! ### Clopenable sets in Polish spaces -/

/--
Definition of `IsClopenable` / `IsClopenable` 的定义

English:
definition IsClopenable
  signature: [t : TopologicalSpace α] (s : Set α)
  body: exists t' : TopologicalSpace α, t' <= t ∧ @PolishSpace α t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s

中文:
定义 IsClopenable
  签名: [t : TopologicalSpace α] (s : Set α)
  定义体: exists t' : TopologicalSpace α, t' <= t ∧ @PolishSpace α t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s

Depends on / 依赖: IsClosed, IsOpen, PolishSpace, TopologicalSpace
-/
def IsClopenable [t : TopologicalSpace α] (s : Set α) : Prop :=
  exists t' : TopologicalSpace α, t' <= t ∧ @PolishSpace α t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s

/--
theorem `_root_.IsClosed.isClopenable` / 定理 `_root_.IsClosed.isClopenable`

English:
theorem _root_.IsClosed.isClopenable
  statement: [TopologicalSpace α] [PolishSpace α] {s : Set α}
  proof: by
  /- Both sets `s` and `sᶜ` admit a Polish topology. So does their disjoint union `s ⊕ sᶜ`.
    Pulling back this topology by the canonical bijection with `α` gives the desired Polish
    topology in which `s` is both open and closed. -/
  classical
  have : PolishSpace s := hs.polishSpace
  let 

中文:
定理 _root_.IsClosed.isClopenable
  结论: [TopologicalSpace α] [PolishSpace α] {s : Set α}
  证明: by
  /- Both sets `s` and `sᶜ` admit a Polish topology. So does their disjoint union `s ⊕ sᶜ`.
    Pulling back this topology by the canonical bijection with `α` gives the desired Polish
    topology in which `s` is both open and closed. -/
  classical
  have : PolishSpace s := hs.polishSpace
  let 
-/
theorem _root_.IsClosed.isClopenable [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsClosed s) : IsClopenable s := by
  /- Both sets `s` and `sᶜ` admit a Polish topology. So does their disjoint union `s ⊕ sᶜ`.
    Pulling back this topology by the canonical bijection with `α` gives the desired Polish
    topology in which `s` is both open and closed. -/
  classical
  have : PolishSpace s := hs.polishSpace
  let t : Set α := sᶜ
  have : PolishSpace t := hs.isOpen_compl.polishSpace
  let f : s oplus t ≃ α := Equiv.Set.sumCompl s
  have hle : TopologicalSpace.coinduced f instTopologicalSpaceSum <= ‹_› := by
    simp only [instTopologicalSpaceSum, coinduced_sup, coinduced_compose, sup_le_iff,
      ← continuous_iff_coinduced_le]
    exact ⟨continuous_subtype_val, continuous_subtype_val⟩
  refine ⟨.coinduced f instTopologicalSpaceSum, hle, ?_, hs.mono hle, ?_⟩
  · rw [← f.induced_symm]
    exact f.symm.polishSpace_induced
  · rw [isOpen_coinduced, isOpen_sum_iff]
    simp [preimage_preimage, f, t]

/--
theorem `IsClopenable.compl` / 定理 `IsClopenable.compl`

English:
theorem IsClopenable.compl
  given: [TopologicalSpace α] {s : Set α} (hs : IsClopenable s)
  proof: by
  rcases hs with ⟨t, t_le, t_polish, h, h'⟩
  exact ⟨t, t_le, t_polish, @IsOpen.isClosed_compl α t s h', @IsClosed.isOpen_compl α t s h⟩

中文:
定理 IsClopenable.compl
  条件: [TopologicalSpace α] {s : Set α} (hs : IsClopenable s)
  证明: by
  rcases hs with ⟨t, t_le, t_polish, h, h'⟩
  exact ⟨t, t_le, t_polish, @IsOpen.isClosed_compl α t s h', @IsClosed.isOpen_compl α t s h⟩

Depends on / 依赖: IsClosed, IsClosed.isOpen_compl, IsOpen, IsOpen.isClosed_compl, isClosed_compl, isOpen_compl, t_le, t_polish
-/
theorem IsClopenable.compl [TopologicalSpace α] {s : Set α} (hs : IsClopenable s) :
    IsClopenable sᶜ := by
  rcases hs with ⟨t, t_le, t_polish, h, h'⟩
  exact ⟨t, t_le, t_polish, @IsOpen.isClosed_compl α t s h', @IsClosed.isOpen_compl α t s h⟩

/--
theorem `_root_.IsOpen.isClopenable` / 定理 `_root_.IsOpen.isClopenable`

English:
theorem _root_.IsOpen.isClopenable
  statement: [TopologicalSpace α] [PolishSpace α] {s : Set α}
  proof: by
  simpa using hs.isClosed_compl.isClopenable.compl

中文:
定理 _root_.IsOpen.isClopenable
  结论: [TopologicalSpace α] [PolishSpace α] {s : Set α}
  证明: by
  simpa using hs.isClosed_compl.isClopenable.compl

Depends on / 依赖: hs.isClosed_compl.isClopenable.compl, isClopenable, isClosed_compl
-/
theorem _root_.IsOpen.isClopenable [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsOpen s) : IsClopenable s := by
  simpa using hs.isClosed_compl.isClopenable.compl

-- TODO: generalize for free to `[Countable ι] {s : ι → Set α}`
/--
theorem `IsClopenable.iUnion` / 定理 `IsClopenable.iUnion`

English:
theorem IsClopenable.iUnion
  statement: [t : TopologicalSpace α] [PolishSpace α] {s : Nat -> Set α}
  proof: by
  choose m mt m_polish _ m_open using hs
  obtain ⟨t', t'm, -, t'_polish⟩ :
      exists t' : TopologicalSpace α, (forall n : Nat, t' <= m n) ∧ t' <= t ∧ @PolishSpace α t' :=
    exists_polishSpace_forall_le m mt m_polish
  have A : IsOpen[t'] (⋃ n, s n) := by
    apply isOpen_iUnion
    intro n


中文:
定理 IsClopenable.iUnion
  结论: [t : TopologicalSpace α] [PolishSpace α] {s : 自然数 -> Set α}
  证明: by
  choose m mt m_polish _ m_open using hs
  obtain ⟨t', t'm, -, t'_polish⟩ :
      exists t' : TopologicalSpace α, (forall n : Nat, t' <= m n) ∧ t' <= t ∧ @PolishSpace α t' :=
    exists_polishSpace_forall_le m mt m_polish
  have A : IsOpen[t'] (⋃ n, s n) := by
    apply isOpen_iUnion
    intro n


Depends on / 依赖: IsClosed, IsOpen, IsOpen.isClopenable, PolishSpace, TopologicalSpace, _polish, exists_polishSpace_forall_le, isClopenable, isOpen_iUnion, m_open, m_polish
-/
theorem IsClopenable.iUnion [t : TopologicalSpace α] [PolishSpace α] {s : Nat -> Set α}
    (hs : forall n, IsClopenable (s n)) : IsClopenable (⋃ n, s n) := by
  choose m mt m_polish _ m_open using hs
  obtain ⟨t', t'm, -, t'_polish⟩ :
      exists t' : TopologicalSpace α, (forall n : Nat, t' <= m n) ∧ t' <= t ∧ @PolishSpace α t' :=
    exists_polishSpace_forall_le m mt m_polish
  have A : IsOpen[t'] (⋃ n, s n) := by
    apply isOpen_iUnion
    intro n
    apply t'm n
    exact m_open n
  obtain ⟨t'', t''_le, t''_polish, h1, h2⟩ : exists t'' : TopologicalSpace α,
      t'' <= t' ∧ @PolishSpace α t'' ∧ IsClosed[t''] (⋃ n, s n) ∧ IsOpen[t''] (⋃ n, s n) :=
    @IsOpen.isClopenable α t' t'_polish _ A
  exact ⟨t'', t''_le.trans ((t'm 0).trans (mt 0)), t''_polish, h1, h2⟩

end PolishSpace
