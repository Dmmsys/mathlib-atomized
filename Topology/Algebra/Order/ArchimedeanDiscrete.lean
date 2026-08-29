/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Discreteness of subgroups in archimedean ordered groups

This file contains some supplements to the results in
`Mathlib/Topology/Algebra/Order/Archimedean.lean`, involving discreteness of subgroups, which
require heavier imports.
-/

public section

namespace Subgroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
  [TopologicalSpace G] [OrderTopology G]

/-- In a linearly ordered group with the order topology, the powers of a single element form a
discrete subgroup. -/
@[to_additive /-- In a linearly ordered additive group with the order topology, the multiples of a
single element form a discrete subgroup. -/]
/--
Instance `instDiscreteTopologyZMultiples` / 实例 `instDiscreteTopologyZMultiples`

English:
instance instDiscreteTopologyZMultiples
  signature: (g : G)
  body: by
  wlog ha : 1 <= g
  · specialize this g⁻¹ (one_le_inv'.mpr (le_of_not_ge ha))
    rwa [zpowers_inv] at this
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [zpowers_one_eq_bot]
    exact Subsingleton.discreteTopology
  rw [discreteTopology_iff_isOpen_singleton_one]; rw [isOpen_induced_iff]
  ref

中文:
实例 instDiscreteTopologyZMultiples
  签名: (g : G)
  定义体: by
  wlog ha : 1 <= g
  · specialize this g⁻¹ (one_le_inv'.mpr (le_of_not_ge ha))
    rwa [zpowers_inv] at this
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [zpowers_one_eq_bot]
    exact Subsingleton.discreteTopology
  rw [discreteTopology_iff_isOpen_singleton_one]; rw [isOpen_induced_iff]
  ref

Depends on / 依赖: Set.Ioo, Set.mem_Ioo, Set.mem_preimage, Set.mem_singleton_iff, Subsingleton, Subsingleton.discreteTopology, and_imp, discreteTopology, discreteTopology_iff_isOpen_singleton_one, eq_or_lt_of_le, isOpen_Ioo, isOpen_induced_iff, le_of_not_ge, mem_Ioo, mem_preimage, mem_singleton_iff, one_le_inv, specialize, zpow_lt_zpow_iff_right, zpowers_inv
-/
instance instDiscreteTopologyZMultiples (g : G) : DiscreteTopology (zpowers g) := by
  wlog ha : 1 <= g
  · specialize this g⁻¹ (one_le_inv'.mpr (le_of_not_ge ha))
    rwa [zpowers_inv] at this
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [zpowers_one_eq_bot]
    exact Subsingleton.discreteTopology
  rw [discreteTopology_iff_isOpen_singleton_one]; rw [isOpen_induced_iff]
  refine ⟨Set.Ioo (g ^ (-1 : Int)) (g ^ (1 : Int)), isOpen_Ioo, ?_⟩
  ext ⟨_, ⟨n, rfl⟩⟩
  constructor
  · simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_singleton_iff, and_imp]
    intro hn hn'
    rw [zpow_lt_zpow_iff_right ha] at hn hn'
    simp only [Subtype.ext_iff, show n = 0 by lia, zpow_zero, coe_one]
  · simp_all

variable [MulArchimedean G]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DiscreteTopology
  signature: G] : IsCyclic G
  body: by
  nontriviality G
  exact LinearOrderedCommGroup.isCyclic_iff_not_denselyOrdered.mpr fun h =>
    have := h.subsingleton_of_discreteTopology; false_of_nontrivial_of_subsingleton G

中文:
实例 [离散拓扑
  签名: G] : 是循环 G
  定义体: by
  nontriviality G
  exact LinearOrderedCommGroup.isCyclic_iff_not_denselyOrdered.mpr fun h =>
    have := h.subsingleton_of_discreteTopology; false_of_nontrivial_of_subsingleton G

Depends on / 依赖: LinearOrderedCommGroup, LinearOrderedCommGroup.isCyclic_iff_not_denselyOrdered.mpr, false_of_nontrivial_of_subsingleton, h.subsingleton_of_discreteTopology, isCyclic_iff_not_denselyOrdered, nontriviality, subsingleton_of_discreteTopology
-/
instance [DiscreteTopology G] : IsCyclic G := by
  nontriviality G
  exact LinearOrderedCommGroup.isCyclic_iff_not_denselyOrdered.mpr fun h =>
    have := h.subsingleton_of_discreteTopology; false_of_nontrivial_of_subsingleton G

/-- In an Archimedean linearly ordered group (with the order topology), a subgroup is
discrete iff it is cyclic. -/
@[to_additive /-- In an Archimedean linearly ordered additive group (with the order topology), a
subgroup is discrete iff it is cyclic. -/]
/--
lemma `discrete_iff_cyclic` / 引理 `discrete_iff_cyclic`

English:
lemma discrete_iff_cyclic
  given: {H : Subgroup G}
  statement: IsCyclic H ↔ DiscreteTopology H
  proof: by
  nontriviality G using isCyclic_of_subsingleton, Subsingleton.discreteTopology
  rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  constructor
  · rintro ⟨g, rfl⟩
    infer_instance
  · have := H.dense_or_cyclic
    simp only [← Subgroup.zpowers_eq_closure, Eq.comm (a := H)] at this
    refine 

中文:
引理 discrete_iff_cyclic
  条件: {H : 子群 G}
  结论: 是循环 H ↔ 离散拓扑 H
  证明: by
  nontriviality G using isCyclic_of_subsingleton, Subsingleton.discreteTopology
  rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  constructor
  · rintro ⟨g, rfl⟩
    infer_instance
  · have := H.dense_or_cyclic
    simp only [← Subgroup.zpowers_eq_closure, Eq.comm (a := H)] at this
    refine 

Depends on / 依赖: Eq.comm, H.dense_or_cyclic, Subgroup, Subgroup.isCyclic_iff_exists_zpowers_eq_top, Subgroup.zpowers_eq_closure, Subsingleton, Subsingleton.discreteTopology, dense_or_cyclic, discreteTopology, infer_instance, isCyclic_iff_exists_zpowers_eq_top, isCyclic_of_subsingleton, nontriviality, this.elim, zpowers_eq_closure
-/
lemma discrete_iff_cyclic {H : Subgroup G} : IsCyclic H ↔ DiscreteTopology H := by
  nontriviality G using isCyclic_of_subsingleton, Subsingleton.discreteTopology
  rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  constructor
  · rintro ⟨g, rfl⟩
    infer_instance
  · have := H.dense_or_cyclic
    simp only [← Subgroup.zpowers_eq_closure, Eq.comm (a := H)] at this
    refine fun hA => this.elim (fun h => ?_) id
    -- remains to show a contradiction assuming `H` is both dense and discrete
    obtain rfl : H = ⊤ := by
      rw [← coe_eq_univ]; rw [← (dense_iff_closure_eq.mp h)]; rw [H.isClosed_of_discrete.closure_eq]
    have : DiscreteTopology G := by rwa [← (Homeomorph.Set.univ G).discreteTopology_iff]
    exact isCyclic_iff_exists_zpowers_eq_top.mp inferInstance

end Subgroup
