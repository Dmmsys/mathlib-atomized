/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# The topological abelianization of a group.

This file defines the topological abelianization of a topological group.

## Main definitions

* `TopologicalAbelianization`: defines the topological abelianization of a group `G` as the quotient
  of `G` by the topological closure of its commutator subgroup..

## Main results
- `instNormalCommutatorClosure` : the topological closure of the commutator of a topological group
  `G` is a normal subgroup.

## Tags
group, topological abelianization

-/

public section

open scoped commutatorElement

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
Instance `instNormalCommutatorClosure` / 实例 `instNormalCommutatorClosure`

English:
instance instNormalCommutatorClosure
  signature: : (commutator G).topologicalClosure.Normal
  body: Subgroup.is_normal_topologicalClosure (commutator G)

中文:
实例 instNormalCommutatorClosure
  签名: : (commutator G).topologicalClosure.正规
  定义体: Subgroup.is_normal_topologicalClosure (commutator G)

Depends on / 依赖: Subgroup, Subgroup.is_normal_topologicalClosure, commutator, is_normal_topologicalClosure
-/
instance instNormalCommutatorClosure : (commutator G).topologicalClosure.Normal :=
  Subgroup.is_normal_topologicalClosure (commutator G)

/--
Definition of `TopologicalAbelianization` / `TopologicalAbelianization` 的定义

English:
abbreviation TopologicalAbelianization
  body: G ⧸ Subgroup.topologicalClosure (commutator G)

local notation "G_ab" => TopologicalAbelianization

中文:
缩写 TopologicalAbelianization
  定义体: G ⧸ Subgroup.topologicalClosure (commutator G)

local notation "G_ab" => TopologicalAbelianization

Depends on / 依赖: Subgroup, Subgroup.topologicalClosure, commutator, topologicalClosure
-/
abbrev TopologicalAbelianization := G ⧸ Subgroup.topologicalClosure (commutator G)

local notation "G_ab" => TopologicalAbelianization

namespace TopologicalAbelianization

/--
Instance `commGroup` / 实例 `commGroup`

English:
instance commGroup
  signature: : CommGroup (G_ab G) where
  body: fun x y =>
    Quotient.inductionOn₂' x y fun a b =>
Quotient.sound'
QuotientGroup.leftRel_apply.mpr by
          have h : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by group
          rw [h]
          exact Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator
            (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹))
  __ : Group (G_ab G) := inferInstance

中文:
实例 commGroup
  签名: : 交换群 (G_ab G) where
  定义体: fun x y =>
    Quotient.inductionOn₂' x y fun a b =>
Quotient.sound'
QuotientGroup.leftRel_apply.mpr by
          have h : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by group
          rw [h]
          exact Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator
            (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹))
  __ : Group (G_ab G) := inferInstance
-/
instance commGroup : CommGroup (G_ab G) where
  mul_comm := fun x y =>
    Quotient.inductionOn₂' x y fun a b =>
Quotient.sound'
QuotientGroup.leftRel_apply.mpr by
          have h : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by group
          rw [h]
          exact Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator
            (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹))
  __ : Group (G_ab G) := inferInstance

end TopologicalAbelianization
