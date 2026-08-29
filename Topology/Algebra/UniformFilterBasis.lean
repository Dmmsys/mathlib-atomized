/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Uniform properties of neighborhood bases in topological algebra

This file contains properties of filter bases on algebraic structures that also require the theory
of uniform spaces.

The only result so far is a characterization of Cauchy filters in topological groups.

-/

@[expose] public section


open uniformity Filter

open Filter

namespace AddGroupFilterBasis

variable {G : Type*} [AddCommGroup G] (B : AddGroupFilterBasis G)

/-- The uniform space structure associated to an abelian group filter basis via the associated
topological abelian group structure. -/
@[instance_reducible]
/--
Definition of `uniformSpace` / `uniformSpace` 的定义

English:
definition uniformSpace
  signature: : UniformSpace G
  body: @IsTopologicalAddGroup.rightUniformSpace G _ B.topology B.isTopologicalAddGroup

中文:
定义 uniformSpace
  签名: : 一致空间 G
  定义体: @IsTopologicalAddGroup.rightUniformSpace G _ B.topology B.isTopologicalAddGroup
-/
protected def uniformSpace : UniformSpace G :=
  @IsTopologicalAddGroup.rightUniformSpace G _ B.topology B.isTopologicalAddGroup

/--
theorem `isUniformAddGroup` / 定理 `isUniformAddGroup`

English:
theorem isUniformAddGroup
  statement: @IsUniformAddGroup G B.uniformSpace _
  proof: @isUniformAddGroup_of_addCommGroup G _ B.topology B.isTopologicalAddGroup

中文:
定理 isUniformAddGroup
  结论: @是UniformAdd群 G B.uniformSpace _
  证明: @isUniformAddGroup_of_addCommGroup G _ B.topology B.isTopologicalAddGroup
-/
protected theorem isUniformAddGroup : @IsUniformAddGroup G B.uniformSpace _ :=
  @isUniformAddGroup_of_addCommGroup G _ B.topology B.isTopologicalAddGroup

/--
theorem `cauchy_iff` / 定理 `cauchy_iff`

English:
theorem cauchy_iff
  given: {F : Filter G}
  proof: by
  let := B.uniformSpace
  have := B.isUniformAddGroup
  suffices F ×ˢ F <= uniformity G ↔ forall U in B, exists M in F, forallᵉ (x in M) (y in M), y - x in U by
    constructor <;> rintro ⟨h', h⟩ <;> refine ⟨h', ?_⟩ <;> [rwa [← this]; rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G]; rw [← map_le_iff_le_comap]
  change Tendsto _ _ _ ↔ _
  simp [(basis_sets F).prod_self.tendsto_iff B.nhds_zero_hasBasis, @forall_comm (_ in _) G]

中文:
定理 cauchy_iff
  条件: {F : 滤子 G}
  证明: by
  let := B.uniformSpace
  have := B.isUniformAddGroup
  suffices F ×ˢ F <= uniformity G ↔ forall U in B, exists M in F, forallᵉ (x in M) (y in M), y - x in U by
    constructor <;> rintro ⟨h', h⟩ <;> refine ⟨h', ?_⟩ <;> [rwa [← this]; rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G]; rw [← map_le_iff_le_comap]
  change Tendsto _ _ _ ↔ _
  simp [(basis_sets F).prod_self.tendsto_iff B.nhds_zero_hasBasis, @forall_comm (_ in _) G]

Depends on / 依赖: B.isUniformAddGroup, B.nhds_zero_hasBasis, B.uniformSpace, Tendsto, basis_sets, forall_comm, isUniformAddGroup, map_le_iff_le_comap, nhds_zero_hasBasis, prod_self, prod_self.tendsto_iff, tendsto_iff, uniformSpace, uniformity, uniformity_eq_comap_nhds_zero
-/
theorem cauchy_iff {F : Filter G} :
    @Cauchy G B.uniformSpace F ↔
      F.NeBot ∧ forall U in B, exists M in F, forallᵉ (x in M) (y in M), y - x in U := by
  let := B.uniformSpace
  have := B.isUniformAddGroup
  suffices F ×ˢ F <= uniformity G ↔ forall U in B, exists M in F, forallᵉ (x in M) (y in M), y - x in U by
    constructor <;> rintro ⟨h', h⟩ <;> refine ⟨h', ?_⟩ <;> [rwa [← this]; rwa [this]]
  rw [uniformity_eq_comap_nhds_zero G]; rw [← map_le_iff_le_comap]
  change Tendsto _ _ _ ↔ _
  simp [(basis_sets F).prod_self.tendsto_iff B.nhds_zero_hasBasis, @forall_comm (_ in _) G]

end AddGroupFilterBasis
