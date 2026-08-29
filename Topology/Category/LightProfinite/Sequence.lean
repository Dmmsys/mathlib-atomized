/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Category.LightProfinite.Basic
/-!

# The light profinite set classifying convergent sequences

This file defines the light profinite set `ℕ∪{∞}`, defined as the one point compactification of
`ℕ`.
-/

@[expose] public section

open CategoryTheory OnePoint TopologicalSpace Topology

namespace LightProfinite

/--
Definition of `natUnionInftyEmbedding` / `natUnionInftyEmbedding` 的定义

English:
definition natUnionInftyEmbedding
  signature: : C(OnePoint Nat, Real) where
  body: OnePoint.continuous_iff_from_nat _
    tendsto_one_div_add_atTop_nhds_zero_nat

中文:
定义 natUnionInftyEmbedding
  签名: : C(OnePoint 自然数, 实数) where
  定义体: OnePoint.continuous_iff_from_nat _
    tendsto_one_div_add_atTop_nhds_zero_nat

Depends on / 依赖: OnePoint, OnePoint.continuous_iff_from_nat, continuous_iff_from_nat
-/
noncomputable def natUnionInftyEmbedding : C(OnePoint Nat, Real) where
  toFun
    | ∞ => 0
    | OnePoint.some n => 1 / (n + 1 : Real)
.mpr continuous_toFun := OnePoint.continuous_iff_from_nat _
    tendsto_one_div_add_atTop_nhds_zero_nat

/--
lemma `isClosedEmbedding_natUnionInftyEmbedding` / 引理 `isClosedEmbedding_natUnionInftyEmbedding`

English:
lemma isClosedEmbedding_natUnionInftyEmbedding
  statement: IsClosedEmbedding natUnionInftyEmbedding
  proof: by
  refine .of_continuous_injective_isClosedMap
    natUnionInftyEmbedding.continuous ?_ ?_
  · rintro (_ | n) (_ | m) h
    · rfl
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, zero_eq_inv] at h
      assumption_mod_cast
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_eq_zero] at h
      assumption_mod_cast
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_inj, add_left_inj,
        Nat.cast_inj] at h
      rw [h]
  · exact fun _ hC => (hC.isCompact.image natUnionInftyEmbedding.continuous).isClosed

中文:
引理 isClosedEmbedding_natUnionInftyEmbedding
  结论: 是闭嵌入 natUnionInftyEmbedding
  证明: by
  refine .of_continuous_injective_isClosedMap
    natUnionInftyEmbedding.continuous ?_ ?_
  · rintro (_ | n) (_ | m) h
    · rfl
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, zero_eq_inv] at h
      assumption_mod_cast
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_eq_zero] at h
      assumption_mod_cast
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_inj, add_left_inj,
        Nat.cast_inj] at h
      rw [h]
  · exact fun _ hC => (hC.isCompact.image natUnionInftyEmbedding.continuous).isClosed

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, Nat.cast_inj, add_left_inj, assumption_mod_cast, cast_inj, coe_mk, continuous, hC.isCompact.image, inv_eq_zero, inv_inj, isCompact, natUnionInf, natUnionInftyEmbedding, natUnionInftyEmbedding.continuous, of_continuous_injective_isClosedMap, one_div, zero_eq_inv
-/
lemma isClosedEmbedding_natUnionInftyEmbedding : IsClosedEmbedding natUnionInftyEmbedding := by
  refine .of_continuous_injective_isClosedMap
    natUnionInftyEmbedding.continuous ?_ ?_
  · rintro (_ | n) (_ | m) h
    · rfl
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, zero_eq_inv] at h
      assumption_mod_cast
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_eq_zero] at h
      assumption_mod_cast
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_inj, add_left_inj,
        Nat.cast_inj] at h
      rw [h]
  · exact fun _ hC => (hC.isCompact.image natUnionInftyEmbedding.continuous).isClosed

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetrizableSpace (OnePoint Nat)
  body: isClosedEmbedding_natUnionInftyEmbedding.metrizableSpace

中文:
实例 :
  签名: Metrizable空间 (OnePoint 自然数)
  定义体: isClosedEmbedding_natUnionInftyEmbedding.metrizableSpace

Depends on / 依赖: isClosedEmbedding_natUnionInftyEmbedding, isClosedEmbedding_natUnionInftyEmbedding.metrizableSpace, metrizableSpace
-/
instance : MetrizableSpace (OnePoint Nat) := isClosedEmbedding_natUnionInftyEmbedding.metrizableSpace

/--
Definition of `NatUnionInfty` / `NatUnionInfty` 的定义

English:
abbreviation NatUnionInfty
  signature: : LightProfinite
  body: of (OnePoint Nat)

@[inherit_doc]
scoped notation "Natunion{∞}" => NatUnionInfty

中文:
缩写 自然数UnionInfty
  签名: : LightProfinite
  定义体: of (OnePoint Nat)

@[inherit_doc]
scoped notation "Natunion{∞}" => NatUnionInfty

Depends on / 依赖: OnePoint
-/
abbrev NatUnionInfty : LightProfinite := of (OnePoint Nat)

@[inherit_doc]
scoped notation "Natunion{∞}" => NatUnionInfty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable Natunion{∞}
  body: (inferInstance : Countable <| Option _)

中文:
实例 :
  签名: 可数 自然数union{∞}
  定义体: (inferInstance : Countable <| Option _)

Depends on / 依赖: Countable
-/
instance : Countable Natunion{∞} := (inferInstance : Countable <| Option _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Nat Natunion{∞}
  body: optionCoe

中文:
实例 :
  签名: Coe 自然数 自然数union{∞}
  定义体: optionCoe

Depends on / 依赖: optionCoe
-/
instance : Coe Nat Natunion{∞} := optionCoe

open Filter Topology

/--
lemma `continuous_iff_convergent` / 引理 `continuous_iff_convergent`

English:
lemma continuous_iff_convergent
  given: {Y : Type*} [TopologicalSpace Y] (f : Natunion{∞} -> Y)
  proof: continuous_iff_from_nat f

中文:
引理 continuous_iff_convergent
  条件: {Y : 类型} [拓扑空间 Y] (f : 自然数union{∞} -> Y)
  证明: continuous_iff_from_nat f

Depends on / 依赖: continuous_iff_from_nat
-/
lemma continuous_iff_convergent {Y : Type*} [TopologicalSpace Y] (f : Natunion{∞} -> Y) :
    Continuous f ↔ Tendsto (fun x : Nat => f x) atTop (𝓝 (f ∞)) :=
  continuous_iff_from_nat f

end LightProfinite
