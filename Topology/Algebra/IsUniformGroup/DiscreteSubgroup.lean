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
/--
Definition of `Subgroup.subgroupOfContinuousMulEquivOfLe` / `Subgroup.subgroupOfContinuousMulEquivOfLe` 的定义

English:
definition Subgroup.subgroupOfContinuousMulEquivOfLe
  signature: {H K : Subgroup G} (hHK : H <= K)
  body: (subgroupOfEquivOfLe hHK).toContinuousMulEquiv (by
    simp only [subgroupOfEquivOfLe, Topology.IsInducing.subtypeVal.isOpen_iff,
      exists_exists_and_eq_and]
    simpa [Set.ext_iff] using fun s => exists_congr
      fun t => and_congr_right fun _ => ⟨fun aux g hgh => aux g (hHK hgh) hgh, by grin

中文:
定义 子群.subgroupOfContinuousMulEquivOfLe
  签名: {H K : 子群 G} (hHK : H <= K)
  定义体: (subgroupOfEquivOfLe hHK).toContinuousMulEquiv (by
    simp only [subgroupOfEquivOfLe, Topology.IsInducing.subtypeVal.isOpen_iff,
      exists_exists_and_eq_and]
    simpa [Set.ext_iff] using fun s => exists_congr
      fun t => and_congr_right fun _ => ⟨fun aux g hgh => aux g (hHK hgh) hgh, by grin

Depends on / 依赖: IsInducing, Set.ext_iff, Topology, Topology.IsInducing.subtypeVal.isOpen_iff, and_congr_right, exists_congr, exists_exists_and_eq_and, ext_iff, isOpen_iff, subgroupOfEquivOfLe, subtypeVal, toContinuousMulEquiv
-/
def Subgroup.subgroupOfContinuousMulEquivOfLe {H K : Subgroup G} (hHK : H <= K) :
    (H.subgroupOf K) ≃ₜ* H :=
  (subgroupOfEquivOfLe hHK).toContinuousMulEquiv (by
    simp only [subgroupOfEquivOfLe, Topology.IsInducing.subtypeVal.isOpen_iff,
      exists_exists_and_eq_and]
    simpa [Set.ext_iff] using fun s => exists_congr
      fun t => and_congr_right fun _ => ⟨fun aux g hgh => aux g (hHK hgh) hgh, by grind⟩)

@[to_additive (attr := simp)]
/--
lemma `Subgroup.subgroupOfContinuousMulEquivOfLe_symm_apply` / 引理 `Subgroup.subgroupOfContinuousMulEquivOfLe_symm_apply`

English:
lemma Subgroup.subgroupOfContinuousMulEquivOfLe_symm_apply
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 子群.subgroupOfContinuousMulEquivOfLe_symm_apply
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma Subgroup.subgroupOfContinuousMulEquivOfLe_symm_apply
    {H K : Subgroup G} (hHK : H <= K) (g : H) :
    (subgroupOfContinuousMulEquivOfLe hHK).symm g = ⟨⟨g.1, hHK g.2⟩, g.2⟩ :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `Subgroup.subgroupOfContinuousMulEquivOfLe_toMulEquiv` / 引理 `Subgroup.subgroupOfContinuousMulEquivOfLe_toMulEquiv`

English:
lemma Subgroup.subgroupOfContinuousMulEquivOfLe_toMulEquiv
  given: {H K : Subgroup G} (hHK : H <= K)
  proof: by
  rfl

中文:
引理 子群.subgroupOfContinuousMulEquivOfLe_toMulEquiv
  条件: {H K : 子群 G} (hHK : H <= K)
  证明: by
  rfl
-/
lemma Subgroup.subgroupOfContinuousMulEquivOfLe_toMulEquiv {H K : Subgroup G} (hHK : H <= K) :
    (subgroupOfContinuousMulEquivOfLe hHK : H.subgroupOf K ≃* H) = subgroupOfEquivOfLe hHK := by
  rfl

variable [IsTopologicalGroup G] [T2Space G]

/-- If `G` is a topological group and `H` a finite-index subgroup, then `G` is topologically
discrete iff `H` is. -/
@[to_additive]
/--
lemma `Subgroup.discreteTopology_iff_of_finiteIndex` / 引理 `Subgroup.discreteTopology_iff_of_finiteIndex`

English:
lemma Subgroup.discreteTopology_iff_of_finiteIndex
  given: {H : Subgroup G} [H.FiniteIndex]
  proof: by
  refine ⟨fun hH => ?_, fun hG => inferInstance⟩
  suffices IsOpen (H : Set G) by
    rw [discreteTopology_iff_isOpen_singleton_one]; rw [isOpen_singleton_iff_nhds_eq_pure]; rw [← H.coe_one]; rw [← this.isOpenEmbedding_subtypeVal.map_nhds_eq]; rw [nhds_discrete]; rw [map_pure]
  exact H.isOpen_of

中文:
引理 子群.discreteTopology_iff_of_finiteIndex
  条件: {H : 子群 G} [H.FiniteIndex]
  证明: by
  refine ⟨fun hH => ?_, fun hG => inferInstance⟩
  suffices IsOpen (H : Set G) by
    rw [discreteTopology_iff_isOpen_singleton_one]; rw [isOpen_singleton_iff_nhds_eq_pure]; rw [← H.coe_one]; rw [← this.isOpenEmbedding_subtypeVal.map_nhds_eq]; rw [nhds_discrete]; rw [map_pure]
  exact H.isOpen_of

Depends on / 依赖: H.coe_one, H.isOpen_of_isClosed_of_finiteIndex, IsOpen, Subgroup, Subgroup.isClosed_of_discrete, coe_one, discreteTopology_iff_isOpen_singleton_one, isClosed_of_discrete, isOpenEmbedding_subtypeVal, isOpen_of_isClosed_of_finiteIndex, isOpen_singleton_iff_nhds_eq_pure, map_nhds_eq, map_pure, nhds_discrete, this.isOpenEmbedding_subtypeVal.map_nhds_eq
-/
lemma Subgroup.discreteTopology_iff_of_finiteIndex {H : Subgroup G} [H.FiniteIndex] :
    DiscreteTopology H ↔ DiscreteTopology G := by
  refine ⟨fun hH => ?_, fun hG => inferInstance⟩
  suffices IsOpen (H : Set G) by
    rw [discreteTopology_iff_isOpen_singleton_one]; rw [isOpen_singleton_iff_nhds_eq_pure]; rw [← H.coe_one]; rw [← this.isOpenEmbedding_subtypeVal.map_nhds_eq]; rw [nhds_discrete]; rw [map_pure]
  exact H.isOpen_of_isClosed_of_finiteIndex Subgroup.isClosed_of_discrete

@[to_additive]
/--
lemma `Subgroup.discreteTopology_iff_of_isFiniteRelIndex` / 引理 `Subgroup.discreteTopology_iff_of_isFiniteRelIndex`

English:
lemma Subgroup.discreteTopology_iff_of_isFiniteRelIndex
  statement: {H K : Subgroup G} (hHK : H <= K)
  proof: by
  have : (H.subgroupOf K).FiniteIndex := IsFiniteRelIndex.to_finiteIndex_subgroupOf
  rw [← (subgroupOfContinuousMulEquivOfLe hHK).discreteTopology_iff]; rw [discreteTopology_iff_of_finiteIndex]

@[to_additive]

中文:
引理 子群.discreteTopology_iff_of_isFiniteRelIndex
  结论: {H K : 子群 G} (hHK : H <= K)
  证明: by
  have : (H.subgroupOf K).FiniteIndex := IsFiniteRelIndex.to_finiteIndex_subgroupOf
  rw [← (subgroupOfContinuousMulEquivOfLe hHK).discreteTopology_iff]; rw [discreteTopology_iff_of_finiteIndex]

@[to_additive]

Depends on / 依赖: FiniteIndex, H.subgroupOf, IsFiniteRelIndex, IsFiniteRelIndex.to_finiteIndex_subgroupOf, discreteTopology_iff, discreteTopology_iff_of_finiteIndex, subgroupOf, subgroupOfContinuousMulEquivOfLe, to_finiteIndex_subgroupOf
-/
lemma Subgroup.discreteTopology_iff_of_isFiniteRelIndex {H K : Subgroup G} (hHK : H <= K)
    [IsFiniteRelIndex H K] : DiscreteTopology H ↔ DiscreteTopology K := by
  have : (H.subgroupOf K).FiniteIndex := IsFiniteRelIndex.to_finiteIndex_subgroupOf
  rw [← (subgroupOfContinuousMulEquivOfLe hHK).discreteTopology_iff]; rw [discreteTopology_iff_of_finiteIndex]

@[to_additive]
/--
lemma `Subgroup.Commensurable.discreteTopology_iff` / 引理 `Subgroup.Commensurable.discreteTopology_iff`

English:
lemma Subgroup.Commensurable.discreteTopology_iff
  proof: calc DiscreteTopology H ↔ DiscreteTopology ↑(H ⊓ K) :=
    haveI : IsFiniteRelIndex (H ⊓ K) H := ⟨Subgroup.inf_relIndex_left H K ▸ h.2⟩
    (Subgroup.discreteTopology_iff_of_isFiniteRelIndex inf_le_left).symm
  _ ↔ DiscreteTopology K :=
    haveI : IsFiniteRelIndex (H ⊓ K) K := ⟨Subgroup.inf_relInde

中文:
引理 子群.Commensurable.discreteTopology_iff
  证明: calc DiscreteTopology H ↔ DiscreteTopology ↑(H ⊓ K) :=
    haveI : IsFiniteRelIndex (H ⊓ K) H := ⟨Subgroup.inf_relIndex_left H K ▸ h.2⟩
    (Subgroup.discreteTopology_iff_of_isFiniteRelIndex inf_le_left).symm
  _ ↔ DiscreteTopology K :=
    haveI : IsFiniteRelIndex (H ⊓ K) K := ⟨Subgroup.inf_relInde

Depends on / 依赖: DiscreteTopology, IsFiniteRelIndex, Subgroup, Subgroup.discreteTopology_iff_of_isFiniteRelIndex, Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_right, discreteTopology_iff_of_isFiniteRelIndex, inf_le_left, inf_le_right, inf_relIndex_left, inf_relIndex_right
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
