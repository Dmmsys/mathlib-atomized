/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.GroupTheory.Commensurable
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Discrete subgroups of topological groups

Note that the instance `Subgroup.isClosed_of_discrete` does not live here, in order that it can
be used in other files without requiring lots of group-theoretic imports.
-/

@[expose] public section

open Filter Topology Uniformity

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- If `G` has a topology, and `H ≤ K` are subgroups, then `H` as a subgroup of `K` is isomorphic,
as a topological group, to `H` as a subgroup of `G`. This is `subgroupOfEquivOfLe` upgraded to a
`ContinuousMulEquiv`. -/
@[to_additive (attr := simps! apply) /-- If `G` has a topology, and `H ≤ K` are
subgroups, then `H` as a subgroup of `K` is isomorphic, as a topological group, to `H` as a subgroup
of `G`. This is `addSubgroupOfEquivOfLe` upgraded to a `ContinuousAddEquiv`.-/]
/-
**Subgroup.subgroupOfContinuousMulEquivOfLe** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subgroup.subgroupOfContinuousMulEquivOfLe {H K : Subgroup G} (hHK : H <= K
) : (H.subgroupOf K) ≃ₜ* H
参数：hHK : H <= K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Subgroup.subgroupOfContinuousMulEquivOfLe {H K : Subgroup G} (hHK : H ≤ K) :
    (H.subgroupOf K) ≃ₜ* H :=
  (subgroupOfEquivOfLe hHK).toContinuousMulEquiv (by
    simp only [subgroupOfEquivOfLe, Topology.IsInducing.subtypeVal.isOpen_iff,
      exists_exists_and_eq_and]
    simpa [Set.ext_iff] using fun s ↦ exists_congr
      fun t ↦ and_congr_right fun _ ↦ ⟨fun aux g hgh ↦ aux g (hHK hgh) hgh, by grind⟩)

@[to_additive (attr := simp)]
/-
**Subgroup.subgroupOfContinuousMulEquivOfLe_symm_apply** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：Subgroup.subgroupOfContinuousMulEquivOfLe_symm_apply {H K : Subgroup G} (h
HK : H <= K) (g : H) : (subgroupOfContinuousMulEquivOfLe hHK).symm g = ⟨⟨g.1, hH
K g.2⟩, g.2⟩
参数：hHK : H <= K；g : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Subgroup.subgroupOfContinuousMulEquivOfLe_symm_apply
    {H K : Subgroup G} (hHK : H ≤ K) (g : H) :
    (subgroupOfContinuousMulEquivOfLe hHK).symm g = ⟨⟨g.1, hHK g.2⟩, g.2⟩ :=
  rfl

@[to_additive (attr := simp)]
/-
**Subgroup.subgroupOfContinuousMulEquivOfLe_toMulEquiv** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：Subgroup.subgroupOfContinuousMulEquivOfLe_toMulEquiv {H K : Subgroup G} (h
HK : H <= K) : (subgroupOfContinuousMulEquivOfLe hHK : H.subgroupOf K ≃* H) = su
bgroupOfEquivOfLe hHK
参数：hHK : H <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMulEquiv.instMulEquivClass`：∀ {M : Type u_1} {N : Type u_2} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace N] [inst_2 : Mul M]   [inst
_3 : Mul N], MulEquivClass…
-/
lemma Subgroup.subgroupOfContinuousMulEquivOfLe_toMulEquiv {H K : Subgroup G} (hHK : H ≤ K) :
    (subgroupOfContinuousMulEquivOfLe hHK : H.subgroupOf K ≃* H) = subgroupOfEquivOfLe hHK := by
  rfl

variable [IsTopologicalGroup G] [T2Space G]

/-- If `G` is a topological group and `H` a finite-index subgroup, then `G` is topologically
discrete iff `H` is. -/
@[to_additive]
/-
**Subgroup.discreteTopology_iff_of_finiteIndex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.discreteTopology_iff_of_finiteIndex {H : Subgroup G} [H.FiniteInd
ex] : DiscreteTopology H ↔ DiscreteTopology G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.isOpen_of_isClosed_of_finiteIndex`：isOpen_of_isClosed_of_finite
Index (H : Subgroup G) [H.FiniteIndex] (h : IsClosed (H : Set G)) : IsOpen (H : 
Set G)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `discreteTopology_iff_isOpen_singleton_one`：discreteTopology_iff_isOpen_s
ingleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G)
· 使用定理 `isOpen_singleton_iff_nhds_eq_pure`：isOpen_singleton_iff_nhds_eq_pure (x 
: X) : IsOpen ({x} : Set X) ↔ 𝓝 x = pure x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.coe_one`：coe_one : ((1 : H) : G) = 1
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `Filter.map_pure`：map_pure (f : α -> β) (a : α) : map f (pure a) = pure (
f a)
· 使用定理 `instDiscreteTopologySubtype`：∀ {X : Type u} {p : X → Prop} [inst : Topol
ogicalSpace X] [DiscreteTopology X], DiscreteTopology (Subtype p)

--- 原说明 ---
If `G` is a topological group and `H` a finite-index subgroup, then `G` is topol
ogically
discrete iff `H` is.
-/
lemma Subgroup.discreteTopology_iff_of_finiteIndex {H : Subgroup G} [H.FiniteIndex] :
    DiscreteTopology H ↔ DiscreteTopology G := by
  refine ⟨fun hH ↦ ?_, fun hG ↦ inferInstance⟩
  suffices IsOpen (H : Set G) by
    rw [discreteTopology_iff_isOpen_singleton_one, isOpen_singleton_iff_nhds_eq_pure,
        ← H.coe_one, ← this.isOpenEmbedding_subtypeVal.map_nhds_eq, nhds_discrete, map_pure]
  exact H.isOpen_of_isClosed_of_finiteIndex Subgroup.isClosed_of_discrete

@[to_additive]
/-
**Subgroup.discreteTopology_iff_of_isFiniteRelIndex** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：Subgroup.discreteTopology_iff_of_isFiniteRelIndex {H K : Subgroup G} (hHK 
: H <= K) [IsFiniteRelIndex H K] : DiscreteTopology H ↔ DiscreteTopology K
参数：hHK : H <= K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.IsFiniteRelIndex.to_finiteIndex_subgroupOf`：∀ {G : Type u_1} [i
nst : Group G] {H K : Subgroup G} [H.IsFiniteRelIndex K], (H.subgroupOf K).Finit
eIndex
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.discreteTopology_iff`：discreteTopology_iff (h : X ≃ₜ Y) : Dis
creteTopology X ↔ DiscreteTopology Y
· 使用引理 `Subgroup.discreteTopology_iff_of_finiteIndex`：Subgroup.discreteTopology_
iff_of_finiteIndex {H : Subgroup G} [H.FiniteIndex] : DiscreteTopology H ↔ Discr
eteTopology G
· 使用定理 `Subgroup.instIsTopologicalGroupSubtypeMem`：∀ {G : Type w} [inst : Topolo
gicalSpace G] [inst_1 : Group G] [IsTopologicalGroup G] (S : Subgroup G),   IsTo
pologicalGroup ↥S
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Subgroup.discreteTopology_iff_of_isFiniteRelIndex {H K : Subgroup G} (hHK : H ≤ K)
    [IsFiniteRelIndex H K] : DiscreteTopology H ↔ DiscreteTopology K := by
  have : (H.subgroupOf K).FiniteIndex := IsFiniteRelIndex.to_finiteIndex_subgroupOf
  rw [← (subgroupOfContinuousMulEquivOfLe hHK).discreteTopology_iff,
    discreteTopology_iff_of_finiteIndex]

@[to_additive]
/-
**Subgroup.Commensurable.discreteTopology_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.Commensurable.discreteTopology_iff {G : Type*} [Group G] [Topolog
icalSpace G] [IsTopologicalGroup G] [T2Space G] {H K : Subgroup G} (h : Commensu
rable H K) : DiscreteTopology H ↔ DiscreteTopology K
参数：h : Commensurable H K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Subgroup.discreteTopology_iff_of_isFiniteRelIndex`：Subgroup.discreteTopo
logy_iff_of_isFiniteRelIndex {H K : Subgroup G} (hHK : H <= K) [IsFiniteRelIndex
 H K] : DiscreteTopology H ↔ DiscreteTo…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.inf_relIndex_left`：inf_relIndex_left : (H ⊓ K).relIndex H = K.r
elIndex H
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subgroup.inf_relIndex_right`：inf_relIndex_right : (H ⊓ K).relIndex K = H
.relIndex K
-/
lemma Subgroup.Commensurable.discreteTopology_iff
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {H K : Subgroup G} (h : Commensurable H K) :
    DiscreteTopology H ↔ DiscreteTopology K :=
  calc DiscreteTopology H ↔ DiscreteTopology ↑(H ⊓ K) :=
    haveI : IsFiniteRelIndex (H ⊓ K) H := ⟨Subgroup.inf_relIndex_left H K ▸ h.2⟩
    (Subgroup.discreteTopology_iff_of_isFiniteRelIndex inf_le_left).symm
  _ ↔ DiscreteTopology K :=
    haveI : IsFiniteRelIndex (H ⊓ K) K := ⟨Subgroup.inf_relIndex_right H K ▸ h.1⟩
    Subgroup.discreteTopology_iff_of_isFiniteRelIndex inf_le_right
