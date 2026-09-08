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

/-- A topological space is completely pseudometrizable if there exists a pseudometric space
structure compatible with the topology which makes the space complete.
To endow such a space with a compatible distance, use
`letI := upgradeIsCompletelyPseudoMetrizable X`. -/
/-
**TopologicalSpace.IsCompletelyPseudoMetrizableSpace** 是 Mathlib 中的一个归纳类型，位于命名空间
 `TopologicalSpace`。
形式化陈述：(X : Type u_3) → [t : TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is completely pseudometrizable if there exists a pseudometri
c space
structure compatible with the topology which makes the space complete.
To endow such a space with a compatible distance, use
`letI := upgradeIsCompletelyPseudoMetrizable X`.
-/
class IsCompletelyPseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : ∃ m : PseudoMetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) _root_.PseudoMetricSpace.toIsCompletelPseudoMetrizableSpace
    [PseudoMetricSpace X] [CompleteSpace X] : IsCompletelyPseudoMetrizableSpace X :=
  ⟨⟨‹_›, rfl, ‹_›⟩⟩

/-- A convenience class, for a completely pseudometrizable space endowed with a complete
pseudometric. No instance of this class should be registered: It should be used as
`letI := upgradeIsCompletelyPseudoMetrizable X` to endow a completely pseudometrizable
space with a complete pseudometric. -/
/-
**TopologicalSpace.UpgradedIsCompletelyPseudoMetrizableSpace** 是 Mathlib 中的一个归纳类
型，位于命名空间 `TopologicalSpace`。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenience class, for a completely pseudometrizable space endowed with a comp
lete
pseudometric. No instance of this class should be registered: It should be used 
as
`letI := upgradeIsCompletelyPseudoMetrizable X` to endow a completely pseudometr
izable
space with a complete pseudometric.
-/
class UpgradedIsCompletelyPseudoMetrizableSpace (X : Type*) extends
  PseudoMetricSpace X, CompleteSpace X

open scoped Uniformity in
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable
    [UniformSpace X] [CompleteSpace X] [(𝓤 X).IsCountablyGenerated] :
    IsCompletelyPseudoMetrizableSpace X where
  complete := ⟨UniformSpace.pseudoMetricSpace X, rfl, ‹_›⟩

/-- Construct on a completely pseudometrizable space a pseudometric (compatible with the topology)
which is complete. -/
@[instance_reducible]
/-
**TopologicalSpace.completelyPseudoMetrizableMetric** 是 Mathlib 中的一个定义，位于命名空间 `T
opologicalSpace`。
形式化陈述：completelyPseudoMetrizableMetric (X : Type*) [TopologicalSpace X] [h : IsC
ompletelyPseudoMetrizableSpace X] : PseudoMetricSpace X
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.complete`：∀ {X : Type
 u_3} {t : TopologicalSpace X} [self : TopologicalSpace.IsCompletelyPseudoMetriz
ableSpace X],   ∃ m, PseudoMetricSpace.toUniformS…

--- 原说明 ---
Construct on a completely pseudometrizable space a pseudometric (compatible with
 the topology)
which is complete.
-/
noncomputable def completelyPseudoMetrizableMetric (X : Type*) [TopologicalSpace X]
    [h : IsCompletelyPseudoMetrizableSpace X] : PseudoMetricSpace X :=
  h.complete.choose.replaceTopology h.complete.choose_spec.1.symm
/-
**TopologicalSpace.complete_completelyPseudoMetrizableMetric** 是 Mathlib 中的一个定理，
位于命名空间 `TopologicalSpace`。
形式化陈述：complete_completelyPseudoMetrizableMetric (X : Type*) [ht : TopologicalSpa
ce X] [h : IsCompletelyPseudoMetrizableSpace X] : @CompleteSpace X (completelyPs
eudoMetrizableMetric X).toUniformSpace
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.complete`：∀ {X : Type
 u_3} {t : TopologicalSpace X} [self : TopologicalSpace.IsCompletelyPseudoMetriz
ableSpace X],   ∃ m, PseudoMetricSpace.toUniformS…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PseudoMetricSpace.replaceTopology_eq`：PseudoMetricSpace.replaceTopology_
eq {γ} [U : TopologicalSpace γ] (m : PseudoMetricSpace γ) (H : U = m.toUniformSp
ace.toTopologicalSpace) : …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
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
/-
**TopologicalSpace.upgradeIsCompletelyPseudoMetrizable** 是 Mathlib 中的一个定义，位于命名空间
 `TopologicalSpace`。
形式化陈述：upgradeIsCompletelyPseudoMetrizable (X : Type*) [TopologicalSpace X] [IsCo
mpletelyPseudoMetrizableSpace X] : UpgradedIsCompletelyPseudoMetrizableSpace X
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.complete_completelyPseudoMetrizableMetric`：complete_com
pletelyPseudoMetrizableMetric (X : Type*) [ht : TopologicalSpace X] [h : IsCompl
etelyPseudoMetrizableSpace X] : @CompleteSpace X…
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
/-
**TopologicalSpace.IsCompletelyPseudoMetrizableSpace.** 是 Mathlib 中的一个实例，位于命名空间 
`TopologicalSpace.IsCompletelyPseudoMetrizableSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note: the priority is set to 90 to ensure that this instance is only applied aft
er
`PseudoEMetricSpace.pseudoMetrizableSpace`. This prevents unnecessary attempts t
o infer
completeness.
-/
instance (priority := 90) PseudoMetrizableSpace [TopologicalSpace X]
    [IsCompletelyPseudoMetrizableSpace X] : PseudoMetrizableSpace X := by
  let := upgradeIsCompletelyPseudoMetrizable X
  infer_instance

/-- A countable product of completely pseudometrizable spaces is completely pseudometrizable. -/
/-
**TopologicalSpace.IsCompletelyPseudoMetrizableSpace.pi_countable** 是 Mathlib 中的
一个实例，位于命名空间 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace`。
形式化陈述：pi_countable {ι : Type*} [Countable ι] {X : ι -> Type*} [forall i, Topolog
icalSpace (X i)] [forall i, IsCompletelyPseudoMetrizableSpace (X i)] : IsComplet
elyPseudoMetrizableSpace (Π i, X i)
参数：X i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseu
dometrizable`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(unifo
rmity X).IsCountablyGenerated],   TopologicalSpace.IsCompletelyPseudoMetri…
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyPseudoMetrizableSpace.toCompleteSpa
ce`：∀ {X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyPseudoMetrizab
leSpace X], CompleteSpace X
· 使用定理 `instIsCountablyGeneratedProdForallUniformityOfCountable`：∀ {ι : Type u_1
} {α : ι → Type u} [U : (i : ι) → UniformSpace (α i)] [Countable ι]   [∀ (i : ι)
, (uniformity (α i)).IsCountablyGenerated], (…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated

--- 原说明 ---
A countable product of completely pseudometrizable spaces is completely pseudome
trizable.
-/
instance pi_countable {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, IsCompletelyPseudoMetrizableSpace (X i)] :
    IsCompletelyPseudoMetrizableSpace (Π i, X i) := by
  let := fun i ↦ upgradeIsCompletelyPseudoMetrizable (X i)
  infer_instance

/-- The product of two completely pseudometrizable spaces is completely pseudometrizable. -/
/-
**TopologicalSpace.IsCompletelyPseudoMetrizableSpace.prod** 是 Mathlib 中的一个实例，位于命
名空间 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace`。
形式化陈述：prod [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [Topologic
alSpace Y] [IsCompletelyPseudoMetrizableSpace Y] : IsCompletelyPseudoMetrizableS
pace (X × Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseu
dometrizable`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(unifo
rmity X).IsCountablyGenerated],   TopologicalSpace.IsCompletelyPseudoMetri…
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyPseudoMetrizableSpace.toCompleteSpa
ce`：∀ {X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyPseudoMetrizab
leSpace X], CompleteSpace X
· 使用定理 `instIsCountablyGeneratedProdUniformity`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [(uniformity α).IsCountablyGenerated] [inst_2 : UniformSpa
ce β]   [(uniformity β).IsCo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated

--- 原说明 ---
The product of two completely pseudometrizable spaces is completely pseudometriz
able.
-/
instance prod [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyPseudoMetrizableSpace Y] : IsCompletelyPseudoMetrizableSpace (X × Y) :=
  letI := upgradeIsCompletelyPseudoMetrizable X
  letI := upgradeIsCompletelyPseudoMetrizable Y
  inferInstance

/-- The disjoint union of two completely pseudometrizable spaces is completely pseudometrizable. -/
/-
**TopologicalSpace.IsCompletelyPseudoMetrizableSpace.sum** 是 Mathlib 中的一个实例，位于命名
空间 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace`。
形式化陈述：sum [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [Topologica
lSpace Y] [IsCompletelyPseudoMetrizableSpace Y] : IsCompletelyPseudoMetrizableSp
ace (X oplus Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseu
dometrizable`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(unifo
rmity X).IsCountablyGenerated],   TopologicalSpace.IsCompletelyPseudoMetri…
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyPseudoMetrizableSpace.toCompleteSpa
ce`：∀ {X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyPseudoMetrizab
leSpace X], CompleteSpace X
· 使用定理 `instIsCountablyGeneratedProdSumUniformity`：∀ {α : Type ua} {β : Type ub}
 [inst : UniformSpace α] [inst_1 : UniformSpace β] [(uniformity α).IsCountablyGe
nerated]   [(uniformity β).IsCo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated

--- 原说明 ---
The disjoint union of two completely pseudometrizable spaces is completely pseud
ometrizable.
-/
instance sum [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyPseudoMetrizableSpace Y] : IsCompletelyPseudoMetrizableSpace (X ⊕ Y) :=
  letI := upgradeIsCompletelyPseudoMetrizable X
  letI := upgradeIsCompletelyPseudoMetrizable Y
  inferInstance

/-- Given a closed embedding into a completely pseudometrizable space,
the source space is also completely pseudometrizable. -/
/-
**TopologicalSpace.IsCompletelyPseudoMetrizableSpace._root_.Topology.IsClosedEmb
edding.IsCompletelyPseudoMetrizableSpace** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.IsCompletelyPseudoMetrizableSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a closed embedding into a completely pseudometrizable space,
the source space is also completely pseudometrizable.
-/
theorem _root_.Topology.IsClosedEmbedding.IsCompletelyPseudoMetrizableSpace [TopologicalSpace X]
    [TopologicalSpace Y] [IsCompletelyPseudoMetrizableSpace Y] {f : X → Y}
    (hf : IsClosedEmbedding f) :
    IsCompletelyPseudoMetrizableSpace X := by
  let := upgradeIsCompletelyPseudoMetrizable Y
  let : PseudoMetricSpace X := hf.isEmbedding.comapPseudoMetricSpace
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

/-- A closed subset of a completely pseudometrizable space is also completely pseudometrizable. -/
/-
**TopologicalSpace.IsCompletelyPseudoMetrizableSpace._root_.IsClosed.isCompletel
yPseudoMetrizableSpace** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.IsCompletelyP
seudoMetrizableSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A closed subset of a completely pseudometrizable space is also completely pseudo
metrizable.
-/
theorem _root_.IsClosed.isCompletelyPseudoMetrizableSpace
    [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X]
    {s : Set X} (hs : IsClosed s) : IsCompletelyPseudoMetrizableSpace s :=
  hs.isClosedEmbedding_subtypeVal.IsCompletelyPseudoMetrizableSpace

end IsCompletelyPseudoMetrizableSpace

/-- A topological space is completely metrizable if there exists a metric space structure
compatible with the topology which makes the space complete.
To endow such a space with a compatible distance, use
`letI := upgradeIsCompletelyMetrizable X`. -/
/-
**TopologicalSpace.IsCompletelyMetrizableSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topo
logicalSpace`。
形式化陈述：(X : Type u_3) → [t : TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is completely metrizable if there exists a metric space stru
cture
compatible with the topology which makes the space complete.
To endow such a space with a compatible distance, use
`letI := upgradeIsCompletelyMetrizable X`.
-/
class IsCompletelyMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace

/-- A completely metrizable space is completely pseudometrizable. -/
/-
**TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetrizableSpa
ce** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.IsCompletelyMetrizableSpace`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletel
yMetrizableSpace X],   TopologicalSpace.IsCompletelyPseudoMetrizableSpace X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A completely metrizable space is completely pseudometrizable.
-/
instance IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetrizableSpace [TopologicalSpace X]
    [IsCompletelyMetrizableSpace X] : IsCompletelyPseudoMetrizableSpace X := by
  obtain ⟨m, _⟩ := ‹_›
  use m.toPseudoMetricSpace

/-- A completely pseudometrizable T0 space is completely metrizable. -/
/-
**TopologicalSpace.IsCompletelyMetrizableSpace_of_isCompletelyPseudoMetrizableSp
ace** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace`。
形式化陈述：IsCompletelyMetrizableSpace_of_isCompletelyPseudoMetrizableSpace [Topologi
calSpace X] [IsCompletelyPseudoMetrizableSpace X] [T0Space X] : IsCompletelyMetr
izableSpace X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyPseudoMetrizableSpace.toCompleteSpa
ce`：∀ {X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyPseudoMetrizab
leSpace X], CompleteSpace X

--- 原说明 ---
A completely pseudometrizable T0 space is completely metrizable.
-/
lemma IsCompletelyMetrizableSpace_of_isCompletelyPseudoMetrizableSpace [TopologicalSpace X]
    [IsCompletelyPseudoMetrizableSpace X] [T0Space X] :
    IsCompletelyMetrizableSpace X := by
  let := upgradeIsCompletelyPseudoMetrizable X
  use MetricSpace.ofT0PseudoMetricSpace X
  exact ⟨rfl, by infer_instance⟩
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) _root_.MetricSpace.toIsCompletelyMetrizableSpace
    [MetricSpace X] [CompleteSpace X] : IsCompletelyMetrizableSpace X :=
  ⟨⟨‹_›, rfl, ‹_›⟩⟩

/-- A convenience class, for a completely metrizable space endowed with a complete metric.
No instance of this class should be registered: It should be used as
`letI := upgradeIsCompletelyMetrizable X` to endow a completely metrizable
space with a complete metric. -/
/-
**TopologicalSpace.UpgradedIsCompletelyMetrizableSpace** 是 Mathlib 中的一个归纳类型，位于命名
空间 `TopologicalSpace`。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenience class, for a completely metrizable space endowed with a complete m
etric.
No instance of this class should be registered: It should be used as
`letI := upgradeIsCompletelyMetrizable X` to endow a completely metrizable
space with a complete metric.
-/
class UpgradedIsCompletelyMetrizableSpace (X : Type*) extends MetricSpace X, CompleteSpace X

open scoped Uniformity in
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsCompletelyMetrizableSpace.of_completeSpace_metrizable [UniformSpace X]
    [CompleteSpace X] [(𝓤 X).IsCountablyGenerated] [T0Space X] :
    IsCompletelyMetrizableSpace X where
  complete := ⟨UniformSpace.metricSpace X, rfl, ‹_›⟩

/-- Construct on a completely metrizable space a metric (compatible with the topology)
which is complete. -/
@[instance_reducible]
/-
**TopologicalSpace.completelyMetrizableMetric** 是 Mathlib 中的一个定义，位于命名空间 `Topolog
icalSpace`。
形式化陈述：completelyMetrizableMetric (X : Type*) [TopologicalSpace X] [h : IsComplet
elyMetrizableSpace X] : MetricSpace X
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.complete`：∀ {X : Type u_3} 
{t : TopologicalSpace X} [self : TopologicalSpace.IsCompletelyMetrizableSpace X]
,   ∃ m, PseudoMetricSpace.toUniformSpace.t…

--- 原说明 ---
Construct on a completely metrizable space a metric (compatible with the topolog
y)
which is complete.
-/
noncomputable def completelyMetrizableMetric (X : Type*) [TopologicalSpace X]
    [h : IsCompletelyMetrizableSpace X] : MetricSpace X :=
  h.complete.choose.replaceTopology h.complete.choose_spec.1.symm
/-
**TopologicalSpace.complete_completelyMetrizableMetric** 是 Mathlib 中的一个定理，位于命名空间
 `TopologicalSpace`。
形式化陈述：complete_completelyMetrizableMetric (X : Type*) [ht : TopologicalSpace X] 
[h : IsCompletelyMetrizableSpace X] : @CompleteSpace X (completelyMetrizableMetr
ic X).toUniformSpace
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.complete`：∀ {X : Type u_3} 
{t : TopologicalSpace X} [self : TopologicalSpace.IsCompletelyMetrizableSpace X]
,   ∃ m, PseudoMetricSpace.toUniformSpace.t…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MetricSpace.replaceTopology_eq`：MetricSpace.replaceTopology_eq {γ} [U : 
TopologicalSpace γ] (m : MetricSpace γ) (H : U = m.toPseudoMetricSpace.toUniform
Space.toTopologicalS…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
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
/-
**TopologicalSpace.upgradeIsCompletelyMetrizable** 是 Mathlib 中的一个定义，位于命名空间 `Topo
logicalSpace`。
形式化陈述：upgradeIsCompletelyMetrizable (X : Type*) [TopologicalSpace X] [IsComplete
lyMetrizableSpace X] : UpgradedIsCompletelyMetrizableSpace X
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.complete_completelyMetrizableMetric`：complete_completel
yMetrizableMetric (X : Type*) [ht : TopologicalSpace X] [h : IsCompletelyMetriza
bleSpace X] : @CompleteSpace X (completely…
-/
def upgradeIsCompletelyMetrizable (X : Type*) [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    UpgradedIsCompletelyMetrizableSpace X :=
  letI := completelyMetrizableMetric X
  { complete_completelyMetrizableMetric X with }

namespace IsCompletelyMetrizableSpace

/-- Note: the priority is set to 90 to ensure that this instance is only applied after
`EMetricSpace.metrizableSpace`. This prevents unnecessary attempts to infer completeness. -/
/-
**TopologicalSpace.IsCompletelyMetrizableSpace.** 是 Mathlib 中的一个实例，位于命名空间 `Topol
ogicalSpace.IsCompletelyMetrizableSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note: the priority is set to 90 to ensure that this instance is only applied aft
er
`EMetricSpace.metrizableSpace`. This prevents unnecessary attempts to infer comp
leteness.
-/
instance (priority := 90) MetrizableSpace [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    MetrizableSpace X := by
  let := upgradeIsCompletelyMetrizable X
  infer_instance

/-- A countable product of completely metrizable spaces is completely metrizable. -/
/-
**TopologicalSpace.IsCompletelyMetrizableSpace.pi_countable** 是 Mathlib 中的一个实例，位
于命名空间 `TopologicalSpace.IsCompletelyMetrizableSpace`。
形式化陈述：pi_countable {ι : Type*} [Countable ι] {X : ι -> Type*} [forall i, Topolog
icalSpace (X i)] [forall i, IsCompletelyMetrizableSpace (X i)] : IsCompletelyMet
rizableSpace (Π i, X i)
参数：X i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyMetrizableSpace.toCompleteSpace`：∀ 
{X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyMetrizableSpace X], 
CompleteSpace X
· 使用定理 `instIsCountablyGeneratedProdForallUniformityOfCountable`：∀ {ι : Type u_1
} {α : ι → Type u} [U : (i : ι) → UniformSpace (α i)] [Countable ι]   [∀ (i : ι)
, (uniformity (α i)).IsCountablyGenerated], (…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α

--- 原说明 ---
A countable product of completely metrizable spaces is completely metrizable.
-/
instance pi_countable {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, IsCompletelyMetrizableSpace (X i)] : IsCompletelyMetrizableSpace (Π i, X i) := by
  let := fun i ↦ upgradeIsCompletelyMetrizable (X i)
  infer_instance

/-- A disjoint union of completely metrizable spaces is completely metrizable. -/
/-
**TopologicalSpace.IsCompletelyMetrizableSpace.sigma** 是 Mathlib 中的一个实例，位于命名空间 `
TopologicalSpace.IsCompletelyMetrizableSpace`。
形式化陈述：sigma {ι : Type*} {X : ι -> Type*} [forall n, TopologicalSpace (X n)] [for
all n, IsCompletelyMetrizableSpace (X n)] : IsCompletelyMetrizableSpace (Σ n, X 
n)
参数：X n；X n。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `Metric.Sigma.completeSpace`：∀ {ι : Type u_1} {E : ι → Type u_2} [inst : 
(i : ι) → MetricSpace (E i)] [∀ (i : ι), CompleteSpace (E i)],   CompleteSpace (
(i : ι) × E i)
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyMetrizableSpace.toCompleteSpace`：∀ 
{X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyMetrizableSpace X], 
CompleteSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α

--- 原说明 ---
A disjoint union of completely metrizable spaces is completely metrizable.
-/
instance sigma {ι : Type*} {X : ι → Type*} [∀ n, TopologicalSpace (X n)]
    [∀ n, IsCompletelyMetrizableSpace (X n)] : IsCompletelyMetrizableSpace (Σ n, X n) :=
  letI := fun n ↦ upgradeIsCompletelyMetrizable (X n)
  letI : MetricSpace (Σ n, X n) := Metric.Sigma.metricSpace
  haveI : CompleteSpace (Σ n, X n) := Metric.Sigma.completeSpace
  inferInstance

/-- The product of two completely metrizable spaces is completely metrizable. -/
/-
**TopologicalSpace.IsCompletelyMetrizableSpace.prod** 是 Mathlib 中的一个实例，位于命名空间 `T
opologicalSpace.IsCompletelyMetrizableSpace`。
形式化陈述：prod [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpac
e Y] [IsCompletelyMetrizableSpace Y] : IsCompletelyMetrizableSpace (X × Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyMetrizableSpace.toCompleteSpace`：∀ 
{X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyMetrizableSpace X], 
CompleteSpace X
· 使用定理 `instIsCountablyGeneratedProdUniformity`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [(uniformity α).IsCountablyGenerated] [inst_2 : UniformSpa
ce β]   [(uniformity β).IsCo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α

--- 原说明 ---
The product of two completely metrizable spaces is completely metrizable.
-/
instance prod [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyMetrizableSpace Y] : IsCompletelyMetrizableSpace (X × Y) :=
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  inferInstance

/-- The disjoint union of two completely metrizable spaces is completely metrizable. -/
/-
**TopologicalSpace.IsCompletelyMetrizableSpace.sum** 是 Mathlib 中的一个实例，位于命名空间 `To
pologicalSpace.IsCompletelyMetrizableSpace`。
形式化陈述：sum [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpace
 Y] [IsCompletelyMetrizableSpace Y] : IsCompletelyMetrizableSpace (X oplus Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyMetrizableSpace.toCompleteSpace`：∀ 
{X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyMetrizableSpace X], 
CompleteSpace X
· 使用定理 `instIsCountablyGeneratedProdSumUniformity`：∀ {α : Type ua} {β : Type ub}
 [inst : UniformSpace α] [inst_1 : UniformSpace β] [(uniformity α).IsCountablyGe
nerated]   [(uniformity β).IsCo…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `instT2SpaceSum`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace
 X] [T2Space X] [inst_2 : TopologicalSpace Y] [T2Space Y],   T2Space (X ⊕ Y)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α

--- 原说明 ---
The disjoint union of two completely metrizable spaces is completely metrizable.
-/
instance sum [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyMetrizableSpace Y] : IsCompletelyMetrizableSpace (X ⊕ Y) :=
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  inferInstance

/-- Given a closed embedding into a completely metrizable space,
the source space is also completely metrizable. -/
/-
**TopologicalSpace.IsCompletelyMetrizableSpace._root_.Topology.IsClosedEmbedding
.IsCompletelyMetrizableSpace** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.IsCompl
etelyMetrizableSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a closed embedding into a completely metrizable space,
the source space is also completely metrizable.
-/
theorem _root_.Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace [TopologicalSpace X]
    [TopologicalSpace Y] [IsCompletelyMetrizableSpace Y] {f : X → Y} (hf : IsClosedEmbedding f) :
    IsCompletelyMetrizableSpace X := by
  let := upgradeIsCompletelyMetrizable Y
  let : MetricSpace X := hf.isEmbedding.comapMetricSpace f
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

/-- Any discrete space is completely metrizable. -/
/-
**TopologicalSpace.IsCompletelyMetrizableSpace.** 是 Mathlib 中的一个实例，位于命名空间 `Topol
ogicalSpace.IsCompletelyMetrizableSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any discrete space is completely metrizable.
-/
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
    refine eq_bot_of_singletons_open fun x ↦ ?_
    convert! @Metric.isOpen_ball _ _ x 1
    refine subset_antisymm (singleton_subset_iff.2 (Metric.mem_ball_self (by simp)))
      fun y hy ↦ ?_
    simp only [Metric.mem_ball, mem_singleton_iff] at *
    by_contra
    change (if y = x then 0 else 1) < 1 at hy
    simp_all
  · refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
    rw [Metric.cauchySeq_iff'] at hu
    obtain ⟨N, hN⟩ := hu 1 (by simp)
    refine ⟨u N, @tendsto_atTop_of_eventually_const X UniformSpace.toTopologicalSpace (u N) _ _ _ N
      fun n hn ↦ ?_⟩
    specialize hN n hn
    by_contra
    change (if u n = u N then 0 else 1) < 1 at hN
    simp_all

/-- A closed subset of a completely metrizable space is also completely metrizable. -/
/-
**TopologicalSpace.IsCompletelyMetrizableSpace._root_.IsClosed.isCompletelyMetri
zableSpace** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.IsCompletelyMetrizableSpa
ce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A closed subset of a completely metrizable space is also completely metrizable.
-/
theorem _root_.IsClosed.isCompletelyMetrizableSpace
    [TopologicalSpace X] [IsCompletelyMetrizableSpace X]
    {s : Set X} (hs : IsClosed s) : IsCompletelyMetrizableSpace s :=
  hs.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace
/-
**TopologicalSpace.IsCompletelyMetrizableSpace.univ** 是 Mathlib 中的一个实例，位于命名空间 `T
opologicalSpace.IsCompletelyMetrizableSpace`。
形式化陈述：univ [TopologicalSpace X] [IsCompletelyMetrizableSpace X] : IsCompletelyMe
trizableSpace (univ : Set X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.isCompletelyMetrizableSpace`：∀ {X : Type u_1} [inst : Topologic
alSpace X] [TopologicalSpace.IsCompletelyMetrizableSpace X] {s : Set X},   IsClo
sed s → TopologicalSpace.I…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
-/
instance univ [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    IsCompletelyMetrizableSpace (univ : Set X) :=
  isClosed_univ.isCompletelyMetrizableSpace

end IsCompletelyMetrizableSpace

end TopologicalSpace

