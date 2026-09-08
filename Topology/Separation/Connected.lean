/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Interaction of separation properties with connectedness properties
-/

public section

variable {X : Type*} [TopologicalSpace X]

open Filter Set
open scoped Topology

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) TotallyDisconnectedSpace.t1Space [h : TotallyDisconnectedSpace X] :
    T1Space X := by
  rw [((t1Space_TFAE X).out 0 1 :)]
  intro x
  rw [← totallyDisconnectedSpace_iff_connectedComponent_singleton.mp h x]
  exact isClosed_connectedComponent
/-
**PreconnectedSpace.trivial_of_discrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PreconnectedSpace.trivial_of_discrete [PreconnectedSpace X] [DiscreteTopol
ogy X] : Subsingleton X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClopen.eq_univ`：IsClopen.eq_univ [PreconnectedSpace α] {s : Set α} (h'
 : IsClopen s) (h : s.Nonempty) : s = univ
· 使用定理 `isClopen_discrete`：isClopen_discrete [DiscreteTopology X] (s : Set X) : 
IsClopen s
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem PreconnectedSpace.trivial_of_discrete [PreconnectedSpace X] [DiscreteTopology X] :
    Subsingleton X := by
  by_contra! ⟨x, y, hxy⟩
  rw [Ne, ← mem_singleton_iff, (isClopen_discrete _).eq_univ <| singleton_nonempty y] at hxy
  exact hxy (mem_univ x)
/-
**IsPreconnected.infinite_of_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.infinite_of_nontrivial [T1Space X] {s : Set X} (h : IsPreco
nnected s) (hs : s.Nontrivial) : s.Infinite
参数：h : IsPreconnected s；hs : s.Nontrivial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subsingleton_coe`：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.
Subsingleton
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `PreconnectedSpace.trivial_of_discrete`：PreconnectedSpace.trivial_of_disc
rete [PreconnectedSpace X] [DiscreteTopology X] : Subsingleton X
· 使用定理 `Subtype.preconnectedSpace`：Subtype.preconnectedSpace {s : Set α} (h : Is
Preconnected s) : PreconnectedSpace s where isPreconnected_univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.not_subsingleton_iff`：not_subsingleton_iff : ¬s.Subsingleton ↔ s.Non
trivial
-/
theorem IsPreconnected.infinite_of_nontrivial [T1Space X] {s : Set X} (h : IsPreconnected s)
    (hs : s.Nontrivial) : s.Infinite := by
  refine mt (fun hf => (subsingleton_coe s).mp ?_) (not_subsingleton_iff.mpr hs)
  have := @Finite.instDiscreteTopology s _ _ hf.to_subtype
  exact @PreconnectedSpace.trivial_of_discrete _ _ (Subtype.preconnectedSpace h) _
/-
**PreconnectedSpace.infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PreconnectedSpace.infinite [PreconnectedSpace X] [Nontrivial X] [T1Space X
] : Infinite X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.infinite_univ_iff`：infinite_univ_iff : (@univ α).Infinite ↔ Infinite
 α
· 使用定理 `IsPreconnected.infinite_of_nontrivial`：IsPreconnected.infinite_of_nontri
vial [T1Space X] {s : Set X} (h : IsPreconnected s) (hs : s.Nontrivial) : s.Infi
nite
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `Set.nontrivial_univ`：nontrivial_univ [Nontrivial α] : (univ : Set α).Non
trivial
-/
theorem PreconnectedSpace.infinite [PreconnectedSpace X] [Nontrivial X] [T1Space X] : Infinite X :=
  infinite_univ_iff.mp <| isPreconnected_univ.infinite_of_nontrivial nontrivial_univ
/-
**subsingleton_iff_discrete_and_indiscrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subsingleton_iff_discrete_and_indiscrete : Subsingleton X ↔ DiscreteTopolo
gy X ∧ IndiscreteTopology X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `instIndiscreteTopologyOfSubsingleton`：∀ {α : Type u} [inst : Topological
Space α] [Subsingleton α], IndiscreteTopology α
· 使用定理 `PreconnectedSpace.trivial_of_discrete`：PreconnectedSpace.trivial_of_disc
rete [PreconnectedSpace X] [DiscreteTopology X] : Subsingleton X
· 使用定理 `PreirreducibleSpace.preconnectedSpace`：∀ (α : Type u) [inst : Topologica
lSpace α] [PreirreducibleSpace α], PreconnectedSpace α
· 使用定理 `instPreirreducibleSpaceOfIndiscreteTopology`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [IndiscreteTopology X], PreirreducibleSpace X
-/
theorem subsingleton_iff_discrete_and_indiscrete :
    Subsingleton X ↔ DiscreteTopology X ∧ IndiscreteTopology X :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ PreconnectedSpace.trivial_of_discrete⟩

/-- A non-trivial connected T1 space has no isolated points. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-trivial connected T1 space has no isolated points.
-/
instance (priority := 100) ConnectedSpace.neBot_nhdsWithin_compl_of_nontrivial_of_t1space
    [ConnectedSpace X] [Nontrivial X] [T1Space X] (x : X) :
    NeBot (𝓝[≠] x) := by
  by_contra contra
  rw [not_neBot, ← isOpen_singleton_iff_punctured_nhds] at contra
  replace contra := nonempty_inter isOpen_compl_singleton
    contra (compl_union_self _) (Set.nonempty_compl_of_nontrivial _) (singleton_nonempty _)
  simp [compl_inter_self {x}] at contra
