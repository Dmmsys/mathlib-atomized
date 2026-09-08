/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.UniformSpace.Pi

/-!
# Metrizable Spaces

In this file we define metrizable topological spaces, i.e., topological spaces for which there
exists a metric space structure that generates the same topology.
We define it without any reference to metric spaces in order to avoid importing the real numbers.
For the proof that metrizable spaces admit a compatible metric,
see `Mathlib/Topology/Metrizable/Uniformity.lean`.
-/

-- don't import the real numbers
assert_not_exists AddMonoidWithOne

public section

open Filter Set Topology Uniformity UniformSpace SetRel

namespace TopologicalSpace

variable {ι X Y : Type*} {A : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
  [∀ i, TopologicalSpace (A i)]

/-- A topological space is *pseudometrizable* if there exists a pseudometric space structure
compatible with the topology. To minimize imports, we implement this class in terms of the
existence of a countably generated uniformity inducing the topology, which is mathematically
equivalent.
To endow such a space with a compatible uniformity, use
`letI : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X`.
To endow such a space with a compatible distance, use
`letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X`. -/
/-
**TopologicalSpace.PseudoMetrizableSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topologica
lSpace`。
形式化陈述：(X : Type u_5) → [t : TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is *pseudometrizable* if there exists a pseudometric space s
tructure
compatible with the topology. To minimize imports, we implement this class in te
rms of the
existence of a countably generated uniformity inducing the topology, which is ma
thematically
equivalent.
To endow such a space with a compatible uniformity, use
`letI : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X`.
To endow such a space with a compatible distance, use
`letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetri
c X`.
-/
class PseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_countably_generated :
    ∃ u : UniformSpace X, u.toTopologicalSpace = t ∧ (uniformity X).IsCountablyGenerated

/-- A uniform space with countably generated `𝓤 X` is pseudometrizable. -/
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A uniform space with countably generated `𝓤 X` is pseudometrizable.
-/
instance (priority := 100) _root_.UniformSpace.pseudoMetrizableSpace {X : Type*}
    [u : UniformSpace X] [hu : IsCountablyGenerated (uniformity X)] : PseudoMetrizableSpace X :=
  ⟨⟨u, rfl, hu⟩⟩

/-- Construct on a pseudometrizable space a countably generated uniformity
compatible with the topology. Use `pseudoMetrizableSpaceUniformity_countably_generated` for a proof
that this uniformity is countably generated. -/
-- see note [reducible non-instances]
/-
**TopologicalSpace.pseudoMetrizableSpaceUniformity** 是 Mathlib 中的一个缩写定义，位于命名空间 `
TopologicalSpace`。
形式化陈述：pseudoMetrizableSpaceUniformity (X : Type*) [TopologicalSpace X] [h : Pseu
doMetrizableSpace X] : UniformSpace X
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.exists_countably_generated`：∀ {X 
: Type u_5} {t : TopologicalSpace X} [self : TopologicalSpace.PseudoMetrizableSp
ace X],   ∃ u, u.toTopologicalSpace = t ∧ (uniformity X…
-/
noncomputable abbrev pseudoMetrizableSpaceUniformity (X : Type*) [TopologicalSpace X]
    [h : PseudoMetrizableSpace X] : UniformSpace X :=
  h.exists_countably_generated.choose.replaceTopology
    h.exists_countably_generated.choose_spec.1.symm
/-
**TopologicalSpace.** 是 Mathlib 中的一个示例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {X : Type*} [t : TopologicalSpace X] [PseudoMetrizableSpace X] :
    (pseudoMetrizableSpaceUniformity X).toTopologicalSpace = t := by
  with_reducible_and_instances rfl

/-- The uniformity coming from `pseudoMetrizableSpaceUniformity` is countably generated.. -/
/-
**TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated** 是 Mathl
ib 中的一个定理，位于命名空间 `TopologicalSpace`。
形式化陈述：pseudoMetrizableSpaceUniformity_countably_generated (X : Type*) [Topologic
alSpace X] [h : PseudoMetrizableSpace X] : 𝓤[pseudoMetrizableSpaceUniformity X].
IsCountablyGenerated
参数：X : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.exists_countably_generated`：∀ {X 
: Type u_5} {t : TopologicalSpace X} [self : TopologicalSpace.PseudoMetrizableSp
ace X],   ∃ u, u.toTopologicalSpace = t ∧ (uniformity X…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
The uniformity coming from `pseudoMetrizableSpaceUniformity` is countably genera
ted..
-/
theorem pseudoMetrizableSpaceUniformity_countably_generated
    (X : Type*) [TopologicalSpace X] [h : PseudoMetrizableSpace X] :
    𝓤[pseudoMetrizableSpaceUniformity X].IsCountablyGenerated :=
  h.exists_countably_generated.choose_spec.2
/-
**TopologicalSpace.pseudoMetrizableSpace_prod** 是 Mathlib 中的一个实例，位于命名空间 `Topolog
icalSpace`。
形式化陈述：pseudoMetrizableSpace_prod [PseudoMetrizableSpace X] [PseudoMetrizableSpac
e Y] : PseudoMetrizableSpace (X × Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated`：ps
eudoMetrizableSpaceUniformity_countably_generated (X : Type*) [TopologicalSpace 
X] [h : PseudoMetrizableSpace X] : 𝓤[pseudoMetrizableSpace…
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `instIsCountablyGeneratedProdUniformity`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [(uniformity α).IsCountablyGenerated] [inst_2 : UniformSpa
ce β]   [(uniformity β).IsCo…
-/
instance pseudoMetrizableSpace_prod [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y] :
    PseudoMetrizableSpace (X × Y) :=
  let : UniformSpace X := pseudoMetrizableSpaceUniformity X
  have : (uniformity X).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated X
  let : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (uniformity Y).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated Y
  inferInstance

/-- Given an inducing map of a topological space into a pseudometrizable space, the source space
is also pseudometrizable. -/
/-
**TopologicalSpace._root_.Topology.IsInducing.pseudoMetrizableSpace** 是 Mathlib 
中的一个定理，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an inducing map of a topological space into a pseudometrizable space, the 
source space
is also pseudometrizable.
-/
theorem _root_.Topology.IsInducing.pseudoMetrizableSpace [PseudoMetrizableSpace Y] {f : X → Y}
    (hf : IsInducing f) : PseudoMetrizableSpace X :=
  let u : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
  have : (uniformity Y).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated Y
  ⟨⟨u.comap f, u.toTopologicalSpace_comap.trans hf.eq_induced.symm,
    Filter.comap.isCountablyGenerated (uniformity Y) (Prod.map f f)⟩⟩

/-- Every pseudo-metrizable space is first countable. -/
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every pseudo-metrizable space is first countable.
-/
instance (priority := 100) PseudoMetrizableSpace.firstCountableTopology
    [h : PseudoMetrizableSpace X] : FirstCountableTopology X :=
  let : UniformSpace X := pseudoMetrizableSpaceUniformity X
  have : (uniformity X).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated X
  inferInstance
/-
**TopologicalSpace.PseudoMetrizableSpace.subtype** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace.PseudoMetrizableSpace`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X] (s : Set X),   TopologicalSpace.PseudoMetrizableSpace ↑s
参数：s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.pseudoMetrizableSpace`：∀ {X : Type u_2} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [TopologicalSpace
.PseudoMetrizableSpace Y] {f : …
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
-/
instance PseudoMetrizableSpace.subtype [PseudoMetrizableSpace X] (s : Set X) :
    PseudoMetrizableSpace s :=
  IsInducing.subtypeVal.pseudoMetrizableSpace
/-
**TopologicalSpace.pseudoMetrizableSpace_pi** 是 Mathlib 中的一个实例，位于命名空间 `Topologic
alSpace`。
形式化陈述：pseudoMetrizableSpace_pi [forall i, PseudoMetrizableSpace (A i)] : PseudoM
etrizableSpace (forall i, A i)
参数：A i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated`：ps
eudoMetrizableSpaceUniformity_countably_generated (X : Type*) [TopologicalSpace 
X] [h : PseudoMetrizableSpace X] : 𝓤[pseudoMetrizableSpace…
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `instIsCountablyGeneratedProdForallUniformityOfCountable`：∀ {ι : Type u_1
} {α : ι → Type u} [U : (i : ι) → UniformSpace (α i)] [Countable ι]   [∀ (i : ι)
, (uniformity (α i)).IsCountablyGenerated], (…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
-/
instance pseudoMetrizableSpace_pi [∀ i, PseudoMetrizableSpace (A i)] :
    PseudoMetrizableSpace (∀ i, A i) :=
  let := fun i => pseudoMetrizableSpaceUniformity (A i)
  have := fun i => pseudoMetrizableSpaceUniformity_countably_generated (A i)
  inferInstance
/-
**TopologicalSpace.PseudoMetrizableSpace.regularSpace** 是 Mathlib 中的一个定理，位于命名空间 
`TopologicalSpace.PseudoMetrizableSpace`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X], RegularSpace X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
-/
instance PseudoMetrizableSpace.regularSpace [PseudoMetrizableSpace X] : RegularSpace X :=
  let := pseudoMetrizableSpaceUniformity X
  inferInstance
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IndiscreteTopology.pseudoMetrizableSpace [IndiscreteTopology X] :
    PseudoMetrizableSpace X where
  exists_countably_generated :=
    ⟨⊤, (IndiscreteTopology.eq_top X).symm, isCountablyGenerated_top⟩

/-- A topological space is metrizable if there exists a metric space structure compatible with the
topology. To minimize imports, we implement this class in terms of the existence of a
countably generated uniformity inducing the topology, which is mathematically
equivalent.
To endow such a space with a compatible uniformity, use
`letI : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X`.
To endow such a space with a compatible distance, use
`letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X`. -/
/-
**TopologicalSpace.MetrizableSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalSpace
`。
形式化陈述：(X : Type u_5) → [t : TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space is metrizable if there exists a metric space structure compa
tible with the
topology. To minimize imports, we implement this class in terms of the existence
 of a
countably generated uniformity inducing the topology, which is mathematically
equivalent.
To endow such a space with a compatible uniformity, use
`letI : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X`.
To endow such a space with a compatible distance, use
`letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X`.
-/
class MetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop extends
    PseudoMetrizableSpace X, T0Space X

-- See note [lower instance priority]
attribute [instance 100] MetrizableSpace.toT0Space
attribute [instance 100] MetrizableSpace.toPseudoMetrizableSpace
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PseudoMetrizableSpace.toMetrizableSpace
    [T0Space X] [h : PseudoMetrizableSpace X] : MetrizableSpace X where
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) t2Space_of_metrizableSpace [MetrizableSpace X] : T2Space X :=
  letI : UniformSpace X := pseudoMetrizableSpaceUniformity X
  inferInstance
/-
**TopologicalSpace.metrizableSpace_prod** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace`。
形式化陈述：∀ {X : Type u_2} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y]   [TopologicalSpace.MetrizableSpace X] [TopologicalSpace.Metriza
bleSpace Y], TopologicalSpace.MetrizableSpace (X × Y)
参数：X × Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `TopologicalSpace.MetrizableSpace.toT0Space`：∀ {X : Type u_5} {t : Topolo
gicalSpace X} [self : TopologicalSpace.MetrizableSpace X], T0Space X
-/
instance metrizableSpace_prod [MetrizableSpace X] [MetrizableSpace Y] :
    MetrizableSpace (X × Y) where

/-- Given an embedding of a topological space into a metrizable space, the source space is also
metrizable. -/
/-
**TopologicalSpace._root_.Topology.IsEmbedding.metrizableSpace** 是 Mathlib 中的一个定
理，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an embedding of a topological space into a metrizable space, the source sp
ace is also
metrizable.
-/
theorem _root_.Topology.IsEmbedding.metrizableSpace [MetrizableSpace Y] {f : X → Y}
    (hf : IsEmbedding f) : MetrizableSpace X where
  toPseudoMetrizableSpace := hf.toIsInducing.pseudoMetrizableSpace
  toT0Space := hf.t0Space
/-
**TopologicalSpace.MetrizableSpace.subtype** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.MetrizableSpace`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] [TopologicalSpace.MetrizableS
pace X] (s : Set X),   TopologicalSpace.MetrizableSpace ↑s
参数：s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.metrizableSpace`：∀ {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [TopologicalSpace.Metr
izableSpace Y] {f : X → Y}…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
instance MetrizableSpace.subtype [MetrizableSpace X] (s : Set X) : MetrizableSpace s :=
  IsEmbedding.subtypeVal.metrizableSpace
/-
**TopologicalSpace.metrizableSpace_pi** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e`。
形式化陈述：∀ {ι : Type u_1} {A : ι → Type u_4} [Finite ι] [inst : (i : ι) → Topologic
alSpace (A i)]   [∀ (i : ι), TopologicalSpace.MetrizableSpace (A i)], Topologica
lSpace.MetrizableSpace ((i : ι) → A i)
参数：i : ι；A i；i : ι；A i；(i : ι) → A i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `TopologicalSpace.MetrizableSpace.toT0Space`：∀ {X : Type u_5} {t : Topolo
gicalSpace X} [self : TopologicalSpace.MetrizableSpace X], T0Space X
-/
instance metrizableSpace_pi [∀ i, MetrizableSpace (A i)] : MetrizableSpace (∀ i, A i) where
/-
**TopologicalSpace.IsSeparable.secondCountableTopology** 是 Mathlib 中的一个定理，位于命名空间
 `TopologicalSpace.IsSeparable`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X] {s : Set X},   TopologicalSpace.IsSeparable s → SecondCountableTop
ology ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.dense_iff`：Subtype.dense_iff {s : Set X} {t : Set s} : Dense t ↔
 s subseteq closure ((↑) '' t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.val_comp_inclusion`：val_comp_inclusion (h : s subseteq t) : Subtype.
val ∘ inclusion h = Subtype.val
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.subtype`：∀ {X : Type u_2} [inst :
 TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] (s : Set X),   T
opologicalSpace.PseudoMetrizableSpac…
· 使用定理 `TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated`：ps
eudoMetrizableSpaceUniformity_countably_generated (X : Type*) [TopologicalSpace 
X] [h : PseudoMetrizableSpace X] : 𝓤[pseudoMetrizableSpace…
· 使用定理 `Topology.IsEmbedding.secondCountableTopology`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace α] {f : α → β} [inst_1 : TopologicalSpace β]   [S
econdCountableTopology β], Topolog…
· 使用定理 `Topology.IsEmbedding.inclusion`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s t : Set X} (h : s ⊆ t), Topology.IsEmbedding (Set.inclusion h)
-/
theorem IsSeparable.secondCountableTopology [PseudoMetrizableSpace X] {s : Set X}
    (hs : IsSeparable s) : SecondCountableTopology s :=
  let ⟨u, hu, hs⟩ := hs
  have := hu.to_subtype
  have : SeparableSpace (closure u) :=
    ⟨Set.range (u.inclusion subset_closure), Set.countable_range (u.inclusion subset_closure),
      Subtype.dense_iff.2 <| by rw [← Set.range_comp, Set.val_comp_inclusion, Subtype.range_coe]⟩
  let := pseudoMetrizableSpaceUniformity (closure u)
  have := pseudoMetrizableSpaceUniformity_countably_generated (closure u)
  have := secondCountable_of_separable (closure u)
  (Topology.IsEmbedding.inclusion hs).secondCountableTopology
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type*) [TopologicalSpace X] [LindelofSpace X] [PseudoMetrizableSpace X] :
    SecondCountableTopology X := by
  let := pseudoMetrizableSpaceUniformity X
  have := pseudoMetrizableSpaceUniformity_countably_generated X
  suffices _ : SeparableSpace X from secondCountable_of_separable X
  obtain ⟨V, hVb, hVs⟩ := has_seq_basis X
  choose U hUc hUu using fun n =>
    LindelofSpace.elim_nhds_subcover (fun x => ball x (V n))
      (fun x => ball_mem_nhds x (hVb.mem n))
  refine ⟨Set.iUnion U, Set.countable_iUnion hUc, fun x => ?_⟩
  rw [mem_closure_iff_frequently, nhds_eq_comap_uniformity, frequently_comap, hVb.frequently_iff]
  intro n _
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (Set.eq_univ_iff_forall.1 (hUu n) x)
  rw [ball_eq_of_symmetry] at hx
  exact ⟨(x, i), hx, i, rfl, Set.mem_iUnion_of_mem n hi⟩

/-- If a set `s` is separable in a pseudo metrizable space, then it admits a countable dense
subset. This is not obvious, as the countable set whose closure covers `s` given by the definition
of separability does not need in general to be contained in `s`. -/
/-
**TopologicalSpace.IsSeparable.exists_countable_dense_subset** 是 Mathlib 中的一个定理，
位于命名空间 `TopologicalSpace.IsSeparable`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X] {s : Set X},   TopologicalSpace.IsSeparable s → ∃ t ⊆ s, t.Countab
le ∧ s ⊆ closure t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated`：ps
eudoMetrizableSpaceUniformity_countably_generated (X : Type*) [TopologicalSpace 
X] [h : PseudoMetrizableSpace X] : 𝓤[pseudoMetrizableSpace…
· 使用定理 `UniformSpace.subset_countable_closure_of_almost_dense_set`：subset_counta
ble_closure_of_almost_dense_set (s : Set α) (hs : forall U in 𝓤 α, exists t : Se
t α, t.Countable ∧ s subseteq ⋃ x in t, ball x …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniformSpace.mem_closure_iff_ball`：UniformSpace.mem_closure_iff_ball {s 
: Set α} {x} : x in closure s ↔ forall {V}, V in 𝓤 α -> (ball x V inter s).Nonem
pty
· 使用定理 `symmetrize_mem_uniformity`：symmetrize_mem_uniformity {V : SetRel α α} (h
 : V in 𝓤 α) : SetRel.symmetrize V in 𝓤 α
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用引理 `SetRel.symmetrize_subset_inv`：symmetrize_subset_inv : R.symmetrize subse
teq R.inv

--- 原说明 ---
If a set `s` is separable in a pseudo metrizable space, then it admits a countab
le dense
subset. This is not obvious, as the countable set whose closure covers `s` given
 by the definition
of separability does not need in general to be contained in `s`.
-/
theorem IsSeparable.exists_countable_dense_subset [PseudoMetrizableSpace X]
    {s : Set X} (hs : IsSeparable s) : ∃ t, t ⊆ s ∧ t.Countable ∧ s ⊆ closure t := by
  let := pseudoMetrizableSpaceUniformity X
  have := pseudoMetrizableSpaceUniformity_countably_generated X
  apply subset_countable_closure_of_almost_dense_set
  intro U hU
  obtain ⟨t, htc, hst⟩ := hs
  refine ⟨t, htc, fun x hx => ?_⟩
  obtain ⟨y, hyx, hyt⟩ := mem_closure_iff_ball.1 (hst hx) (symmetrize_mem_uniformity hU)
  exact mem_biUnion hyt (ball_mono SetRel.symmetrize_subset_inv x hyx)

/-- If a set `s` is separable, then the corresponding subtype is separable in a
pseudo metrizable space.
This is not obvious, as the countable set whose closure covers `s` does not need in
general to be contained in `s`. -/
/-
**TopologicalSpace.IsSeparable.separableSpace** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace.IsSeparable`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X] {s : Set X},   TopologicalSpace.IsSeparable s → TopologicalSpace.S
eparableSpace ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsSeparable.exists_countable_dense_subset`：∀ {X : Type 
u_2} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] {s :
 Set X},   TopologicalSpace.IsSeparable s → ∃ t …
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.countable_of_injective_of_countable_image`：countable_of_injective_of
_countable_image {s : Set α} {f : α -> β} (hf : InjOn f s) (hs : (f '' s).Counta
ble) : s.Countable
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsInducing.dense_iff`：dense_iff (hf : IsInducing f) {s : Set X}
 : Dense s ↔ forall x, f x in closure (f '' s)
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩

--- 原说明 ---
If a set `s` is separable, then the corresponding subtype is separable in a
pseudo metrizable space.
This is not obvious, as the countable set whose closure covers `s` does not need
 in
general to be contained in `s`.
-/
theorem IsSeparable.separableSpace [PseudoMetrizableSpace X] {s : Set X} (hs : IsSeparable s) :
    SeparableSpace s := by
  rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, hst⟩
  lift t to Set s using hts
  refine ⟨⟨t, countable_of_injective_of_countable_image Subtype.coe_injective.injOn htc, ?_⟩⟩
  rwa [IsInducing.subtypeVal.dense_iff, Subtype.forall]
/-
**TopologicalSpace.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DiscreteTopology.metrizableSpace [DiscreteTopology X] :
    MetrizableSpace X where
  exists_countably_generated :=
    ⟨⊥, DiscreteTopology.eq_bot.symm, Filter.isCountablyGenerated_principal SetRel.id⟩

end TopologicalSpace

