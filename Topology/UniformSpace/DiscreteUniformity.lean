/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Antoine Chambert-Loir, María Inés de Frutos Fernández
-/
module

public import Mathlib.Topology.UniformSpace.Basic

/-! # Discrete uniformity

The discrete uniformity is the smallest possible uniformity, the one for which
the diagonal is an entourage of itself.

It induces the discrete topology.

It is complete.

-/

public section

open Filter UniformSpace

/-- The discrete uniformity -/
@[mk_iff discreteUniformity_iff_eq_bot]
/--
Definition of `DiscreteUniformity` / `DiscreteUniformity` 的定义

English:
class DiscreteUniformity
  parameters: (X : Type*) [u : UniformSpace X]
  axioms and operations (1):
    - eq_bot : u = ⊥

中文:
类 DiscreteUniformity
  参数: (X : 类型) [u : UniformSpace X]
  公理与运算 (1 个):
    - eq_bot : u = ⊥
-/
class DiscreteUniformity (X : Type*) [u : UniformSpace X] : Prop where
  eq_bot : u = ⊥

namespace DiscreteUniformity

/-- The bot uniformity is the discrete uniformity. -/
instance (X : Type*) : @DiscreteUniformity X ⊥ :=
  @DiscreteUniformity.mk X ⊥ rfl

variable (X : Type*) [u : UniformSpace X] [DiscreteUniformity X]

/--
theorem `_root_.discreteUniformity_iff_eq_principal_setRelId` / 定理 `_root_.discreteUniformity_iff_eq_principal_setRelId`

English:
theorem _root_.discreteUniformity_iff_eq_principal_setRelId
  given: {X : Type*} [UniformSpace X]
  proof: by
  rw [discreteUniformity_iff_eq_bot]; rw [UniformSpace.ext_iff]; rw [Filter.ext_iff]; rw [bot_uniformity]

中文:
定理 _root_.discreteUniformity_iff_eq_principal_setRelId
  条件: {X : 类型} [UniformSpace X]
  证明: by
  rw [discreteUniformity_iff_eq_bot]; rw [UniformSpace.ext_iff]; rw [Filter.ext_iff]; rw [bot_uniformity]

Depends on / 依赖: Filter, Filter.ext_iff, UniformSpace, UniformSpace.ext_iff, bot_uniformity, discreteUniformity_iff_eq_bot, ext_iff
-/
theorem _root_.discreteUniformity_iff_eq_principal_setRelId {X : Type*} [UniformSpace X] :
    DiscreteUniformity X ↔ uniformity X = 𝓟 SetRel.id := by
  rw [discreteUniformity_iff_eq_bot]; rw [UniformSpace.ext_iff]; rw [Filter.ext_iff]; rw [bot_uniformity]

/--
theorem `eq_principal_setRelId` / 定理 `eq_principal_setRelId`

English:
theorem eq_principal_setRelId
  statement: uniformity X = 𝓟 SetRel.id
  proof: discreteUniformity_iff_eq_principal_setRelId.mp inferInstance

中文:
定理 eq_principal_setRelId
  结论: uniformity X = 𝓟 SetRel.id
  证明: discreteUniformity_iff_eq_principal_setRelId.mp inferInstance

Depends on / 依赖: discreteUniformity_iff_eq_principal_setRelId, discreteUniformity_iff_eq_principal_setRelId.mp
-/
theorem eq_principal_setRelId : uniformity X = 𝓟 SetRel.id :=
  discreteUniformity_iff_eq_principal_setRelId.mp inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology X
  body: by
    rw [DiscreteUniformity.eq_bot (X := X)]; rw [UniformSpace.toTopologicalSpace_bot]

中文:
实例 :
  签名: DiscreteTopology X
  定义体: by
    rw [DiscreteUniformity.eq_bot (X := X)]; rw [UniformSpace.toTopologicalSpace_bot]

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.eq_bot, UniformSpace, UniformSpace.toTopologicalSpace_bot, eq_bot, toTopologicalSpace_bot
-/
instance : DiscreteTopology X where
  eq_bot := by
    rw [DiscreteUniformity.eq_bot (X := X)]; rw [UniformSpace.toTopologicalSpace_bot]

/--
theorem `_root_.discreteUniformity_iff_setRelId_mem_uniformity` / 定理 `_root_.discreteUniformity_iff_setRelId_mem_uniformity`

English:
theorem _root_.discreteUniformity_iff_setRelId_mem_uniformity
  given: {X : Type*} [UniformSpace X]
  proof: by
  rw [← uniformSpace_eq_bot]; rw [discreteUniformity_iff_eq_bot]

中文:
定理 _root_.discreteUniformity_iff_setRelId_mem_uniformity
  条件: {X : 类型} [UniformSpace X]
  证明: by
  rw [← uniformSpace_eq_bot]; rw [discreteUniformity_iff_eq_bot]

Depends on / 依赖: discreteUniformity_iff_eq_bot, uniformSpace_eq_bot
-/
theorem _root_.discreteUniformity_iff_setRelId_mem_uniformity {X : Type*} [UniformSpace X] :
    DiscreteUniformity X ↔ SetRel.id in uniformity X := by
  rw [← uniformSpace_eq_bot]; rw [discreteUniformity_iff_eq_bot]

/--
theorem `relId_mem_uniformity` / 定理 `relId_mem_uniformity`

English:
theorem relId_mem_uniformity
  statement: SetRel.id in uniformity X
  proof: discreteUniformity_iff_setRelId_mem_uniformity.mp inferInstance

中文:
定理 relId_mem_uniformity
  结论: SetRel.id in uniformity X
  证明: discreteUniformity_iff_setRelId_mem_uniformity.mp inferInstance

Depends on / 依赖: discreteUniformity_iff_setRelId_mem_uniformity, discreteUniformity_iff_setRelId_mem_uniformity.mp
-/
theorem relId_mem_uniformity : SetRel.id in uniformity X :=
  discreteUniformity_iff_setRelId_mem_uniformity.mp inferInstance

instance {Y : Type*} [Finite Y] [UniformSpace Y] [DiscreteTopology Y] :
    DiscreteUniformity Y := by
  have h : SetRel.id = ⋂ y : Y, {p | p.2 = y -> p.1 in ({y} : Set Y)} := by
    ext x
    simp [SetRel.id]
  simp_rw [discreteUniformity_iff_setRelId_mem_uniformity, h, Filter.iInter_mem,
    ← mem_nhds_uniformity_iff_left, nhds_discrete, Filter.mem_pure, Set.mem_singleton_iff,
    implies_true]

variable {X} in
/-- A product of spaces with discrete uniformity has a discrete uniformity. -/
instance {Y : Type*} [UniformSpace Y] [DiscreteUniformity Y] :
    DiscreteUniformity (X × Y) := by
  simp [discreteUniformity_iff_eq_principal_setRelId, uniformity_prod_eq_comap_prod,
    eq_principal_setRelId, SetRel.id, Set.prod_eq, Prod.ext_iff, Set.ofPred_and]

variable {x} in
/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  given: {Y : Type*} [UniformSpace Y] (f : X -> Y)
  proof: by
  simp only [uniformContinuous_iff_le_comap, DiscreteUniformity.eq_bot, bot_le]

中文:
定理 uniformContinuous
  条件: {Y : 类型} [UniformSpace Y] (f : X -> Y)
  证明: by
  simp only [uniformContinuous_iff_le_comap, DiscreteUniformity.eq_bot, bot_le]

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.eq_bot, bot_le, eq_bot, uniformContinuous_iff_le_comap
-/
theorem uniformContinuous {Y : Type*} [UniformSpace Y] (f : X -> Y) :
    UniformContinuous f := by
  simp only [uniformContinuous_iff_le_comap, DiscreteUniformity.eq_bot, bot_le]

end DiscreteUniformity
