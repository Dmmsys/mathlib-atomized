/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Topology.MetricSpace.Gluing
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Completely (pseudo)metrizable spaces

A topological space is completely (pseudo)metrizable if one can endow it with a
`(Pseudo)MetricSpace` structure which makes it complete and gives the same topology. This typeclass
allows to state theorems which do not require a `(Pseudo)MetricSpace` structure to make sense
without introducing such a structure.
It is in particular useful in measure theory, where one often assumes that a space is a
`PolishSpace`, i.e. a separable and completely metrizable space. Sometimes the separability
hypothesis is not needed and the right assumption is then `IsCompletelyMetrizableSpace`.

## Main definition

* `IsCompletelyPseudoMetrizableSpace X`: A topological space is completely pseudometrizable if
  there exists a pseudometric space structure compatible with the topology which makes the space
  complete. To endow such a space with a compatible distance, use
  `letI := upgradeIsCompletelyPseudoMetrizable X`.

* `IsCompletelyMetrizableSpace X`: A topological space is completely metrizable if
  there exists a metric space structure compatible with the topology which makes the space
  complete. To endow such a space with a compatible distance, use
  `letI := upgradeIsCompletelyMetrizable X`.

## Implementation note

Given a `IsCompletely(Pseudo)MetrizableSpace X` instance, one may want to endow `X` with a complete
(pseudo)metric. This can be done by writing `letI := upgradeIsCompletely(Pseudo)Metrizable X`,
which will endow `X` with an `UpgradedIsCompletely(Pseudo)MetrizableSpace X` instance. This class
is a convenience class and no instance should be registered for it.
-/

@[expose] public section

open Filter Function Set Topology

variable {X Y : Type*}

namespace TopologicalSpace

/--
Definition of `IsCompletelyPseudoMetrizableSpace` / `IsCompletelyPseudoMetrizableSpace` 的定义

English:
class IsCompletelyPseudoMetrizableSpace
  parameters: (X : Type*) [t : TopologicalSpace X]
  axioms and operations (1):
    - complete : exists m : PseudoMetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧ @CompleteSpace X m.toUniformSpace

中文:
类 IsCompletelyPseudoMetrizableSpace
  参数: (X : 类型) [t : TopologicalSpace X]
  公理与运算 (1 个):
    - complete : 存在 m : PseudoMetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧ @CompleteSpace X m.toUniformSpace
-/
class IsCompletelyPseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : exists m : PseudoMetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace

instance (priority := 100) _root_.PseudoMetricSpace.toIsCompletelPseudoMetrizableSpace
    [PseudoMetricSpace X] [CompleteSpace X] : IsCompletelyPseudoMetrizableSpace X :=
  ⟨⟨‹_›, rfl, ‹_›⟩⟩

/--
Definition of `UpgradedIsCompletelyPseudoMetrizableSpace` / `UpgradedIsCompletelyPseudoMetrizableSpace` 的定义

English:
class UpgradedIsCompletelyPseudoMetrizableSpace
  parameters: (X : Type*)
  (no additional axioms)

中文:
类 UpgradedIsCompletelyPseudoMetrizableSpace
  参数: (X : 类型)
  (无附加公理)
-/
class UpgradedIsCompletelyPseudoMetrizableSpace (X : Type*) extends
  PseudoMetricSpace X, CompleteSpace X

open scoped Uniformity in
instance (priority := 100) IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable
    [UniformSpace X] [CompleteSpace X] [(𝓤 X).IsCountablyGenerated] :
    IsCompletelyPseudoMetrizableSpace X where
  complete := ⟨UniformSpace.pseudoMetricSpace X, rfl, ‹_›⟩

/-- Construct on a completely pseudometrizable space a pseudometric (compatible with the topology)
which is complete. -/
@[instance_reducible]
/--
Definition of `completelyPseudoMetrizableMetric` / `completelyPseudoMetrizableMetric` 的定义

English:
definition completelyPseudoMetrizableMetric
  signature: (X : Type*) [TopologicalSpace X]
  body: h.complete.choose.replaceTopology h.complete.choose_spec.1.symm

中文:
定义 completelyPseudoMetrizableMetric
  签名: (X : 类型) [TopologicalSpace X]
  定义体: h.complete.choose.replaceTopology h.complete.choose_spec.1.symm

Depends on / 依赖: choose_spec, complete, h.complete.choose.replaceTopology, h.complete.choose_spec, replaceTopology
-/
noncomputable def completelyPseudoMetrizableMetric (X : Type*) [TopologicalSpace X]
    [h : IsCompletelyPseudoMetrizableSpace X] : PseudoMetricSpace X :=
  h.complete.choose.replaceTopology h.complete.choose_spec.1.symm

/--
theorem `complete_completelyPseudoMetrizableMetric` / 定理 `complete_completelyPseudoMetrizableMetric`

English:
theorem complete_completelyPseudoMetrizableMetric
  statement: (X : Type*) [ht : TopologicalSpace X]
  proof: by
  convert! h.complete.choose_spec.2
  exact PseudoMetricSpace.replaceTopology_eq _ _

中文:
定理 complete_completelyPseudoMetrizableMetric
  结论: (X : 类型) [ht : TopologicalSpace X]
  证明: by
  convert! h.complete.choose_spec.2
  exact PseudoMetricSpace.replaceTopology_eq _ _

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.replaceTopology_eq, choose_spec, complete, convert, h.complete.choose_spec, replaceTopology_eq
-/
theorem complete_completelyPseudoMetrizableMetric (X : Type*) [ht : TopologicalSpace X]
    [h : IsCompletelyPseudoMetrizableSpace X] :
    @CompleteSpace X (completelyPseudoMetrizableMetric X).toUniformSpace := by
  convert! h.complete.choose_spec.2
  exact PseudoMetricSpace.replaceTopology_eq _ _

/-- This definition endows a completely pseudometrizable space with a complete pseudometric.
Use it as: `letI := upgradeIsCompletelyPseudoMetrizable X`. -/
@[instance_reducible]
noncomputable
/--
Definition of `upgradeIsCompletelyPseudoMetrizable` / `upgradeIsCompletelyPseudoMetrizable` 的定义

English:
definition upgradeIsCompletelyPseudoMetrizable
  signature: (X : Type*) [TopologicalSpace X]
  body: letI := completelyPseudoMetrizableMetric X
  { complete_completelyPseudoMetrizableMetric X with }

中文:
定义 upgradeIsCompletelyPseudoMetrizable
  签名: (X : 类型) [TopologicalSpace X]
  定义体: letI := completelyPseudoMetrizableMetric X
  { complete_completelyPseudoMetrizableMetric X with }

Depends on / 依赖: complete_completelyPseudoMetrizableMetric, completelyPseudoMetrizableMetric
-/
def upgradeIsCompletelyPseudoMetrizable (X : Type*) [TopologicalSpace X]
    [IsCompletelyPseudoMetrizableSpace X] :
    UpgradedIsCompletelyPseudoMetrizableSpace X :=
  letI := completelyPseudoMetrizableMetric X
  { complete_completelyPseudoMetrizableMetric X with }

namespace IsCompletelyPseudoMetrizableSpace

/-- Note: the priority is set to 90 to ensure that this instance is only applied after
`PseudoEMetricSpace.pseudoMetrizableSpace`. This prevents unnecessary attempts to infer
completeness. -/
instance (priority := 90) PseudoMetrizableSpace [TopologicalSpace X]
    [IsCompletelyPseudoMetrizableSpace X] : PseudoMetrizableSpace X := by
  let := upgradeIsCompletelyPseudoMetrizable X
  infer_instance

/--
Instance `pi_countable` / 实例 `pi_countable`

English:
instance pi_countable
  signature: {ι : Type*} [Countable ι] {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  body: by
  let := fun i => upgradeIsCompletelyPseudoMetrizable (X i)
  infer_instance

中文:
实例 pi_countable
  签名: {ι : 类型} [Countable ι] {X : ι -> 类型} [对任意 i, TopologicalSpace (X i)]
  定义体: by
  let := fun i => upgradeIsCompletelyPseudoMetrizable (X i)
  infer_instance

Depends on / 依赖: infer_instance, upgradeIsCompletelyPseudoMetrizable
-/
instance pi_countable {ι : Type*} [Countable ι] {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    [forall i, IsCompletelyPseudoMetrizableSpace (X i)] :
    IsCompletelyPseudoMetrizableSpace (Π i, X i) := by
  let := fun i => upgradeIsCompletelyPseudoMetrizable (X i)
  infer_instance

/--
Instance `prod` / 实例 `prod`

English:
instance prod
  signature: [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [TopologicalSpace Y]
  body: letI := upgradeIsCompletelyPseudoMetrizable X
  letI := upgradeIsCompletelyPseudoMetrizable Y
  inferInstance

中文:
实例 prod
  签名: [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [TopologicalSpace Y]
  定义体: letI := upgradeIsCompletelyPseudoMetrizable X
  letI := upgradeIsCompletelyPseudoMetrizable Y
  inferInstance

Depends on / 依赖: upgradeIsCompletelyPseudoMetrizable
-/
instance prod [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyPseudoMetrizableSpace Y] : IsCompletelyPseudoMetrizableSpace (X × Y) :=
  letI := upgradeIsCompletelyPseudoMetrizable X
  letI := upgradeIsCompletelyPseudoMetrizable Y
  inferInstance

/--
Instance `sum` / 实例 `sum`

English:
instance sum
  signature: [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [TopologicalSpace Y]
  body: letI := upgradeIsCompletelyPseudoMetrizable X
  letI := upgradeIsCompletelyPseudoMetrizable Y
  inferInstance

中文:
实例 sum
  签名: [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [TopologicalSpace Y]
  定义体: letI := upgradeIsCompletelyPseudoMetrizable X
  letI := upgradeIsCompletelyPseudoMetrizable Y
  inferInstance

Depends on / 依赖: upgradeIsCompletelyPseudoMetrizable
-/
instance sum [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyPseudoMetrizableSpace Y] : IsCompletelyPseudoMetrizableSpace (X oplus Y) :=
  letI := upgradeIsCompletelyPseudoMetrizable X
  letI := upgradeIsCompletelyPseudoMetrizable Y
  inferInstance

/--
theorem `_root_.Topology.IsClosedEmbedding.IsCompletelyPseudoMetrizableSpace` / 定理 `_root_.Topology.IsClosedEmbedding.IsCompletelyPseudoMetrizableSpace`

English:
theorem _root_.Topology.IsClosedEmbedding.IsCompletelyPseudoMetrizableSpace
  statement: [TopologicalSpace X]
  proof: by
  let := upgradeIsCompletelyPseudoMetrizable Y
  let : PseudoMetricSpace X := hf.isEmbedding.comapPseudoMetricSpace
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

中文:
定理 _root_.Topology.IsClosedEmbedding.IsCompletelyPseudoMetrizableSpace
  结论: [TopologicalSpace X]
  证明: by
  let := upgradeIsCompletelyPseudoMetrizable Y
  let : PseudoMetricSpace X := hf.isEmbedding.comapPseudoMetricSpace
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

Depends on / 依赖: CompleteSpace, PseudoMetricSpace, comapPseudoMetricSpace, completeSpace_iff_isComplete_range, hf.isClosed_range.isComplete, hf.isEmbedding.comapPseudoMetricSpace, hf.isEmbedding.to_isometry.isUniformInducing, infer_instance, isClosed_range, isComplete, isEmbedding, isUniformInducing, to_isometry, upgradeIsCompletelyPseudoMetrizable
-/
theorem _root_.Topology.IsClosedEmbedding.IsCompletelyPseudoMetrizableSpace [TopologicalSpace X]
    [TopologicalSpace Y] [IsCompletelyPseudoMetrizableSpace Y] {f : X -> Y}
    (hf : IsClosedEmbedding f) :
    IsCompletelyPseudoMetrizableSpace X := by
  let := upgradeIsCompletelyPseudoMetrizable Y
  let : PseudoMetricSpace X := hf.isEmbedding.comapPseudoMetricSpace
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

/--
theorem `_root_.IsClosed.isCompletelyPseudoMetrizableSpace` / 定理 `_root_.IsClosed.isCompletelyPseudoMetrizableSpace`

English:
theorem _root_.IsClosed.isCompletelyPseudoMetrizableSpace
  proof: hs.isClosedEmbedding_subtypeVal.IsCompletelyPseudoMetrizableSpace

中文:
定理 _root_.IsClosed.isCompletelyPseudoMetrizableSpace
  证明: hs.isClosedEmbedding_subtypeVal.IsCompletelyPseudoMetrizableSpace

Depends on / 依赖: IsCompletelyPseudoMetrizableSpace, hs.isClosedEmbedding_subtypeVal.IsCompletelyPseudoMetrizableSpace, isClosedEmbedding_subtypeVal
-/
theorem _root_.IsClosed.isCompletelyPseudoMetrizableSpace
    [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X]
    {s : Set X} (hs : IsClosed s) : IsCompletelyPseudoMetrizableSpace s :=
  hs.isClosedEmbedding_subtypeVal.IsCompletelyPseudoMetrizableSpace

end IsCompletelyPseudoMetrizableSpace

/--
Definition of `IsCompletelyMetrizableSpace` / `IsCompletelyMetrizableSpace` 的定义

English:
class IsCompletelyMetrizableSpace
  parameters: (X : Type*) [t : TopologicalSpace X]
  axioms and operations (1):
    - complete : exists m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧ @CompleteSpace X m.toUniformSpace

中文:
类 IsCompletelyMetrizableSpace
  参数: (X : 类型) [t : TopologicalSpace X]
  公理与运算 (1 个):
    - complete : 存在 m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧ @CompleteSpace X m.toUniformSpace
-/
class IsCompletelyMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : exists m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace

/--
Instance `IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetrizableSpace` / 实例 `IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetrizableSpace`

English:
instance IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetrizableSpace
  signature: [TopologicalSpace X]
  body: by
  obtain ⟨m, _⟩ := ‹_›
  use m.toPseudoMetricSpace

中文:
实例 IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetrizableSpace
  签名: [TopologicalSpace X]
  定义体: by
  obtain ⟨m, _⟩ := ‹_›
  use m.toPseudoMetricSpace

Depends on / 依赖: m.toPseudoMetricSpace, toPseudoMetricSpace
-/
instance IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetrizableSpace [TopologicalSpace X]
    [IsCompletelyMetrizableSpace X] : IsCompletelyPseudoMetrizableSpace X := by
  obtain ⟨m, _⟩ := ‹_›
  use m.toPseudoMetricSpace

/--
lemma `IsCompletelyMetrizableSpace_of_isCompletelyPseudoMetrizableSpace` / 引理 `IsCompletelyMetrizableSpace_of_isCompletelyPseudoMetrizableSpace`

English:
lemma IsCompletelyMetrizableSpace_of_isCompletelyPseudoMetrizableSpace
  statement: [TopologicalSpace X]
  proof: by
  let := upgradeIsCompletelyPseudoMetrizable X
  use MetricSpace.ofT0PseudoMetricSpace X
  exact ⟨rfl, by infer_instance⟩

中文:
引理 IsCompletelyMetrizableSpace_of_isCompletelyPseudoMetrizableSpace
  结论: [TopologicalSpace X]
  证明: by
  let := upgradeIsCompletelyPseudoMetrizable X
  use MetricSpace.ofT0PseudoMetricSpace X
  exact ⟨rfl, by infer_instance⟩

Depends on / 依赖: MetricSpace, MetricSpace.ofT0PseudoMetricSpace, infer_instance, ofT0PseudoMetricSpace, upgradeIsCompletelyPseudoMetrizable
-/
lemma IsCompletelyMetrizableSpace_of_isCompletelyPseudoMetrizableSpace [TopologicalSpace X]
    [IsCompletelyPseudoMetrizableSpace X] [T0Space X] :
    IsCompletelyMetrizableSpace X := by
  let := upgradeIsCompletelyPseudoMetrizable X
  use MetricSpace.ofT0PseudoMetricSpace X
  exact ⟨rfl, by infer_instance⟩

instance (priority := 100) _root_.MetricSpace.toIsCompletelyMetrizableSpace
    [MetricSpace X] [CompleteSpace X] : IsCompletelyMetrizableSpace X :=
  ⟨⟨‹_›, rfl, ‹_›⟩⟩

/--
Definition of `UpgradedIsCompletelyMetrizableSpace` / `UpgradedIsCompletelyMetrizableSpace` 的定义

English:
class UpgradedIsCompletelyMetrizableSpace
  parameters: (X : Type*)
  extends: MetricSpace X, CompleteSpace X
  (no additional axioms)

中文:
类 UpgradedIsCompletelyMetrizableSpace
  参数: (X : 类型)
  继承: MetricSpace X, CompleteSpace X
  (无附加公理)
-/
class UpgradedIsCompletelyMetrizableSpace (X : Type*) extends MetricSpace X, CompleteSpace X

open scoped Uniformity in
instance (priority := 100) IsCompletelyMetrizableSpace.of_completeSpace_metrizable [UniformSpace X]
    [CompleteSpace X] [(𝓤 X).IsCountablyGenerated] [T0Space X] :
    IsCompletelyMetrizableSpace X where
  complete := ⟨UniformSpace.metricSpace X, rfl, ‹_›⟩

/-- Construct on a completely metrizable space a metric (compatible with the topology)
which is complete. -/
@[instance_reducible]
/--
Definition of `completelyMetrizableMetric` / `completelyMetrizableMetric` 的定义

English:
definition completelyMetrizableMetric
  signature: (X : Type*) [TopologicalSpace X]
  body: h.complete.choose.replaceTopology h.complete.choose_spec.1.symm

中文:
定义 completelyMetrizableMetric
  签名: (X : 类型) [TopologicalSpace X]
  定义体: h.complete.choose.replaceTopology h.complete.choose_spec.1.symm

Depends on / 依赖: choose_spec, complete, h.complete.choose.replaceTopology, h.complete.choose_spec, replaceTopology
-/
noncomputable def completelyMetrizableMetric (X : Type*) [TopologicalSpace X]
    [h : IsCompletelyMetrizableSpace X] : MetricSpace X :=
  h.complete.choose.replaceTopology h.complete.choose_spec.1.symm

/--
theorem `complete_completelyMetrizableMetric` / 定理 `complete_completelyMetrizableMetric`

English:
theorem complete_completelyMetrizableMetric
  statement: (X : Type*) [ht : TopologicalSpace X]
  proof: by
  convert! h.complete.choose_spec.2
  exact MetricSpace.replaceTopology_eq _ _

中文:
定理 complete_completelyMetrizableMetric
  结论: (X : 类型) [ht : TopologicalSpace X]
  证明: by
  convert! h.complete.choose_spec.2
  exact MetricSpace.replaceTopology_eq _ _

Depends on / 依赖: MetricSpace, MetricSpace.replaceTopology_eq, choose_spec, complete, convert, h.complete.choose_spec, replaceTopology_eq
-/
theorem complete_completelyMetrizableMetric (X : Type*) [ht : TopologicalSpace X]
    [h : IsCompletelyMetrizableSpace X] :
    @CompleteSpace X (completelyMetrizableMetric X).toUniformSpace := by
  convert! h.complete.choose_spec.2
  exact MetricSpace.replaceTopology_eq _ _

/-- This definition endows a completely metrizable space with a complete metric. Use it as:
`letI := upgradeIsCompletelyMetrizable X`. -/
@[instance_reducible]
noncomputable
/--
Definition of `upgradeIsCompletelyMetrizable` / `upgradeIsCompletelyMetrizable` 的定义

English:
definition upgradeIsCompletelyMetrizable
  signature: (X : Type*) [TopologicalSpace X] [IsCompletelyMetrizableSpace X]
  body: letI := completelyMetrizableMetric X
  { complete_completelyMetrizableMetric X with }

中文:
定义 upgradeIsCompletelyMetrizable
  签名: (X : 类型) [TopologicalSpace X] [IsCompletelyMetrizableSpace X]
  定义体: letI := completelyMetrizableMetric X
  { complete_completelyMetrizableMetric X with }

Depends on / 依赖: complete_completelyMetrizableMetric, completelyMetrizableMetric
-/
def upgradeIsCompletelyMetrizable (X : Type*) [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    UpgradedIsCompletelyMetrizableSpace X :=
  letI := completelyMetrizableMetric X
  { complete_completelyMetrizableMetric X with }

namespace IsCompletelyMetrizableSpace

/-- Note: the priority is set to 90 to ensure that this instance is only applied after
`EMetricSpace.metrizableSpace`. This prevents unnecessary attempts to infer completeness. -/
instance (priority := 90) MetrizableSpace [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    MetrizableSpace X := by
  let := upgradeIsCompletelyMetrizable X
  infer_instance

/--
Instance `pi_countable` / 实例 `pi_countable`

English:
instance pi_countable
  signature: {ι : Type*} [Countable ι] {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
  body: by
  let := fun i => upgradeIsCompletelyMetrizable (X i)
  infer_instance

中文:
实例 pi_countable
  签名: {ι : 类型} [Countable ι] {X : ι -> 类型} [对任意 i, TopologicalSpace (X i)]
  定义体: by
  let := fun i => upgradeIsCompletelyMetrizable (X i)
  infer_instance

Depends on / 依赖: infer_instance, upgradeIsCompletelyMetrizable
-/
instance pi_countable {ι : Type*} [Countable ι] {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    [forall i, IsCompletelyMetrizableSpace (X i)] : IsCompletelyMetrizableSpace (Π i, X i) := by
  let := fun i => upgradeIsCompletelyMetrizable (X i)
  infer_instance

/--
Instance `sigma` / 实例 `sigma`

English:
instance sigma
  signature: {ι : Type*} {X : ι -> Type*} [forall n, TopologicalSpace (X n)]
  body: letI := fun n => upgradeIsCompletelyMetrizable (X n)
  letI : MetricSpace (Σ n, X n) := Metric.Sigma.metricSpace
  haveI : CompleteSpace (Σ n, X n) := Metric.Sigma.completeSpace
  inferInstance

中文:
实例 sigma
  签名: {ι : 类型} {X : ι -> 类型} [对任意 n, TopologicalSpace (X n)]
  定义体: letI := fun n => upgradeIsCompletelyMetrizable (X n)
  letI : MetricSpace (Σ n, X n) := Metric.Sigma.metricSpace
  haveI : CompleteSpace (Σ n, X n) := Metric.Sigma.completeSpace
  inferInstance

Depends on / 依赖: CompleteSpace, Metric, Metric.Sigma.completeSpace, Metric.Sigma.metricSpace, MetricSpace, completeSpace, metricSpace, upgradeIsCompletelyMetrizable
-/
instance sigma {ι : Type*} {X : ι -> Type*} [forall n, TopologicalSpace (X n)]
    [forall n, IsCompletelyMetrizableSpace (X n)] : IsCompletelyMetrizableSpace (Σ n, X n) :=
  letI := fun n => upgradeIsCompletelyMetrizable (X n)
  letI : MetricSpace (Σ n, X n) := Metric.Sigma.metricSpace
  haveI : CompleteSpace (Σ n, X n) := Metric.Sigma.completeSpace
  inferInstance

/--
Instance `prod` / 实例 `prod`

English:
instance prod
  signature: [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpace Y]
  body: letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  inferInstance

中文:
实例 prod
  签名: [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpace Y]
  定义体: letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  inferInstance

Depends on / 依赖: upgradeIsCompletelyMetrizable
-/
instance prod [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyMetrizableSpace Y] : IsCompletelyMetrizableSpace (X × Y) :=
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  inferInstance

/--
Instance `sum` / 实例 `sum`

English:
instance sum
  signature: [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpace Y]
  body: letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  inferInstance

中文:
实例 sum
  签名: [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpace Y]
  定义体: letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  inferInstance

Depends on / 依赖: upgradeIsCompletelyMetrizable
-/
instance sum [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyMetrizableSpace Y] : IsCompletelyMetrizableSpace (X oplus Y) :=
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  inferInstance

/--
theorem `_root_.Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace` / 定理 `_root_.Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace`

English:
theorem _root_.Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace
  statement: [TopologicalSpace X]
  proof: by
  let := upgradeIsCompletelyMetrizable Y
  let : MetricSpace X := hf.isEmbedding.comapMetricSpace f
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

中文:
定理 _root_.Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace
  结论: [TopologicalSpace X]
  证明: by
  let := upgradeIsCompletelyMetrizable Y
  let : MetricSpace X := hf.isEmbedding.comapMetricSpace f
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

Depends on / 依赖: CompleteSpace, MetricSpace, comapMetricSpace, completeSpace_iff_isComplete_range, hf.isClosed_range.isComplete, hf.isEmbedding.comapMetricSpace, hf.isEmbedding.to_isometry.isUniformInducing, infer_instance, isClosed_range, isComplete, isEmbedding, isUniformInducing, to_isometry, upgradeIsCompletelyMetrizable
-/
theorem _root_.Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace [TopologicalSpace X]
    [TopologicalSpace Y] [IsCompletelyMetrizableSpace Y] {f : X -> Y} (hf : IsClosedEmbedding f) :
    IsCompletelyMetrizableSpace X := by
  let := upgradeIsCompletelyMetrizable Y
  let : MetricSpace X := hf.isEmbedding.comapMetricSpace f
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

/-- Any discrete space is completely metrizable. -/
instance (priority := 50) discrete [TopologicalSpace X] [DiscreteTopology X] :
    IsCompletelyMetrizableSpace X := by
  classical
  let m : MetricSpace X :=
    { dist x y := if x = y then 0 else 1
      dist_self x := by simp
      dist_comm x y := by
        obtain h | h := eq_or_ne x y
        · simp [h]
        · simp [h, h.symm]
      dist_triangle x y z := by
        by_cases x = y <;> by_cases x = z <;> by_cases y = z <;> simp_all
      eq_of_dist_eq_zero := by simp }
  refine ⟨m, ?_, ?_⟩
  · rw [DiscreteTopology.eq_bot (α := X)]
    refine eq_bot_of_singletons_open fun x => ?_
    convert! @Metric.isOpen_ball _ _ x 1
    refine subset_antisymm (singleton_subset_iff.2 (Metric.mem_ball_self (by simp)))
      fun y hy => ?_
    simp only [Metric.mem_ball, mem_singleton_iff] at *
    by_contra
    change (if y = x then 0 else 1) < 1 at hy
    simp_all
  · refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    rw [Metric.cauchySeq_iff'] at hu
    obtain ⟨N, hN⟩ := hu 1 (by simp)
    refine ⟨u N, @tendsto_atTop_of_eventually_const X UniformSpace.toTopologicalSpace (u N) _ _ _ N
      fun n hn => ?_⟩
    specialize hN n hn
    by_contra
    change (if u n = u N then 0 else 1) < 1 at hN
    simp_all

/--
theorem `_root_.IsClosed.isCompletelyMetrizableSpace` / 定理 `_root_.IsClosed.isCompletelyMetrizableSpace`

English:
theorem _root_.IsClosed.isCompletelyMetrizableSpace
  proof: hs.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace

中文:
定理 _root_.IsClosed.isCompletelyMetrizableSpace
  证明: hs.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace

Depends on / 依赖: IsCompletelyMetrizableSpace, hs.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace, isClosedEmbedding_subtypeVal
-/
theorem _root_.IsClosed.isCompletelyMetrizableSpace
    [TopologicalSpace X] [IsCompletelyMetrizableSpace X]
    {s : Set X} (hs : IsClosed s) : IsCompletelyMetrizableSpace s :=
  hs.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace

/--
Instance `univ` / 实例 `univ`

English:
instance univ
  signature: [TopologicalSpace X] [IsCompletelyMetrizableSpace X]
  body: isClosed_univ.isCompletelyMetrizableSpace

中文:
实例 univ
  签名: [TopologicalSpace X] [IsCompletelyMetrizableSpace X]
  定义体: isClosed_univ.isCompletelyMetrizableSpace

Depends on / 依赖: isClosed_univ, isClosed_univ.isCompletelyMetrizableSpace, isCompletelyMetrizableSpace
-/
instance univ [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    IsCompletelyMetrizableSpace (univ : Set X) :=
  isClosed_univ.isCompletelyMetrizableSpace

end IsCompletelyMetrizableSpace

end TopologicalSpace
