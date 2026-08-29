/-
Copyright (c) 2021 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Ashwin Iyengar, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Nonarchimedean Topology

In this file we set up the theory of nonarchimedean topological groups and rings.

A nonarchimedean group is a topological group whose topology admits a basis of
open neighborhoods of the identity element in the group consisting of open subgroups.
A nonarchimedean ring is a topological ring whose underlying topological (additive)
group is nonarchimedean.

## Definitions

- `NonarchimedeanAddGroup`: nonarchimedean additive group.
- `NonarchimedeanGroup`: nonarchimedean multiplicative group.
- `NonarchimedeanRing`: nonarchimedean ring.

-/

public section

open Topology
open scoped Pointwise

/--
Definition of `NonarchimedeanAddGroup` / `NonarchimedeanAddGroup` 的定义

English:
class NonarchimedeanAddGroup
  parameters: (G : Type*) [AddGroup G] [TopologicalSpace G]
  extends: IsTopologicalAddGroup G
  axioms and operations (1):
    - is_nonarchimedean : forall U in 𝓝 (0 : G), exists V : OpenAddSubgroup G, (V : Set G) subseteq U

中文:
类 NonarchimedeanAdd群
  参数: (G : 类型) [加法群 G] [拓扑空间 G]
  继承: 是拓扑加群 G
  公理与运算 (1 个):
    - is_nonarchimedean : 对任意 U in 𝓝 (0 : G), 存在 V : OpenAdd子群 G, (V : 集合 G) subseteq U
-/
class NonarchimedeanAddGroup (G : Type*) [AddGroup G] [TopologicalSpace G] : Prop
  extends IsTopologicalAddGroup G where
  is_nonarchimedean : forall U in 𝓝 (0 : G), exists V : OpenAddSubgroup G, (V : Set G) subseteq U

/-- A topological group is nonarchimedean if every neighborhood of 1 contains an open subgroup. -/
@[to_additive]
/--
Definition of `NonarchimedeanGroup` / `NonarchimedeanGroup` 的定义

English:
class NonarchimedeanGroup
  parameters: (G : Type*) [Group G] [TopologicalSpace G]
  extends: IsTopologicalGroup G
  axioms and operations (1):
    - is_nonarchimedean : forall U in 𝓝 (1 : G), exists V : OpenSubgroup G, (V : Set G) subseteq U

中文:
类 Nonarchimedean群
  参数: (G : 类型) [群 G] [拓扑空间 G]
  继承: 是拓扑群 G
  公理与运算 (1 个):
    - is_nonarchimedean : 对任意 U in 𝓝 (1 : G), 存在 V : 开子群 G, (V : 集合 G) subseteq U
-/
class NonarchimedeanGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop
  extends IsTopologicalGroup G where
  is_nonarchimedean : forall U in 𝓝 (1 : G), exists V : OpenSubgroup G, (V : Set G) subseteq U

/--
Definition of `NonarchimedeanRing` / `NonarchimedeanRing` 的定义

English:
class NonarchimedeanRing
  parameters: (R : Type*) [Ring R] [TopologicalSpace R]
  extends: IsTopologicalRing R
  axioms and operations (1):
    - is_nonarchimedean : forall U in 𝓝 (0 : R), exists V : OpenAddSubgroup R, (V : Set R) subseteq U

中文:
类 Nonarchimedean环
  参数: (R : 类型) [环 R] [拓扑空间 R]
  继承: 是拓扑环 R
  公理与运算 (1 个):
    - is_nonarchimedean : 对任意 U in 𝓝 (0 : R), 存在 V : OpenAdd子群 R, (V : 集合 R) subseteq U
-/
class NonarchimedeanRing (R : Type*) [Ring R] [TopologicalSpace R] : Prop
  extends IsTopologicalRing R where
  is_nonarchimedean : forall U in 𝓝 (0 : R), exists V : OpenAddSubgroup R, (V : Set R) subseteq U

-- see Note [lower instance priority]
/-- Every nonarchimedean ring is naturally a nonarchimedean additive group. -/
instance (priority := 100) NonarchimedeanRing.to_nonarchimedeanAddGroup (R : Type*) [Ring R]
    [TopologicalSpace R] [t : NonarchimedeanRing R] : NonarchimedeanAddGroup R :=
  { t with }

namespace NonarchimedeanGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {K : Type*} [Group K] [TopologicalSpace K] [NonarchimedeanGroup K]

/-- If a topological group embeds into a nonarchimedean group, then it is nonarchimedean. -/
@[to_additive]
/--
theorem `nonarchimedean_of_emb` / 定理 `nonarchimedean_of_emb`

English:
theorem nonarchimedean_of_emb
  given: (f : G ->* H) (emb : IsOpenEmbedding f)
  statement: NonarchimedeanGroup H
  proof: { is_nonarchimedean := fun U hU =>
      have h₁ : f ⁻¹' U in 𝓝 (1 : G) := by
        apply emb.continuous.tendsto
        rwa [f.map_one]
      let ⟨V, hV⟩ := is_nonarchimedean (f ⁻¹' U) h₁
      ⟨{ Subgroup.map f V with isOpen' := emb.isOpenMap _ V.isOpen }, Set.image_subset_iff.2 hV⟩ }

中文:
定理 nonarchimedean_of_emb
  条件: (f : G ->* H) (emb : 是开嵌入 f)
  结论: Nonarchimedean群 H
  证明: { is_nonarchimedean := fun U hU =>
      have h₁ : f ⁻¹' U in 𝓝 (1 : G) := by
        apply emb.continuous.tendsto
        rwa [f.map_one]
      let ⟨V, hV⟩ := is_nonarchimedean (f ⁻¹' U) h₁
      ⟨{ Subgroup.map f V with isOpen' := emb.isOpenMap _ V.isOpen }, Set.image_subset_iff.2 hV⟩ }

Depends on / 依赖: Set.image_subset_iff, Subgroup, Subgroup.map, V.isOpen, continuous, emb.continuous.tendsto, emb.isOpenMap, f.map_one, image_subset_iff, isOpen, isOpenMap, is_nonarchimedean, map_one, tendsto
-/
theorem nonarchimedean_of_emb (f : G ->* H) (emb : IsOpenEmbedding f) : NonarchimedeanGroup H :=
  { is_nonarchimedean := fun U hU =>
      have h₁ : f ⁻¹' U in 𝓝 (1 : G) := by
        apply emb.continuous.tendsto
        rwa [f.map_one]
      let ⟨V, hV⟩ := is_nonarchimedean (f ⁻¹' U) h₁
      ⟨{ Subgroup.map f V with isOpen' := emb.isOpenMap _ V.isOpen }, Set.image_subset_iff.2 hV⟩ }

/-- An open neighborhood of the identity in the Cartesian product of two nonarchimedean groups
contains the Cartesian product of an open neighborhood in each group. -/
@[to_additive NonarchimedeanAddGroup.prod_subset /-- An open neighborhood of the identity in
the Cartesian product of two nonarchimedean groups contains the Cartesian product of
an open neighborhood in each group. -/]
/--
theorem `prod_subset` / 定理 `prod_subset`

English:
theorem prod_subset
  given: {U} (hU : U in 𝓝 (1 : G × K))
  proof: by
  rw [nhds_prod_eq]; rw [Filter.mem_prod_iff] at hU
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩
  obtain ⟨V, hV⟩ := is_nonarchimedean _ hU₁
  obtain ⟨W, hW⟩ := is_nonarchimedean _ hU₂
  use V
  grind

中文:
定理 prod_subset
  条件: {U} (hU : U in 𝓝 (1 : G × K))
  证明: by
  rw [nhds_prod_eq]; rw [Filter.mem_prod_iff] at hU
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩
  obtain ⟨V, hV⟩ := is_nonarchimedean _ hU₁
  obtain ⟨W, hW⟩ := is_nonarchimedean _ hU₂
  use V
  grind

Depends on / 依赖: Filter, Filter.mem_prod_iff, is_nonarchimedean, mem_prod_iff, nhds_prod_eq
-/
theorem prod_subset {U} (hU : U in 𝓝 (1 : G × K)) :
    exists (V : OpenSubgroup G) (W : OpenSubgroup K), (V : Set G) ×ˢ (W : Set K) subseteq U := by
  rw [nhds_prod_eq]; rw [Filter.mem_prod_iff] at hU
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩
  obtain ⟨V, hV⟩ := is_nonarchimedean _ hU₁
  obtain ⟨W, hW⟩ := is_nonarchimedean _ hU₂
  use V
  grind

/-- An open neighborhood of the identity in the Cartesian square of a nonarchimedean group
contains the Cartesian square of an open neighborhood in the group. -/
@[to_additive NonarchimedeanAddGroup.prod_self_subset /-- An open neighborhood of the identity in
the Cartesian square of a nonarchimedean group contains the Cartesian square of
an open neighborhood in the group. -/]
/--
theorem `prod_self_subset` / 定理 `prod_self_subset`

English:
theorem prod_self_subset
  given: {U} (hU : U in 𝓝 (1 : G × G))
  proof: let ⟨V, W, h⟩ := prod_subset hU
  ⟨V ⊓ W, by refine Set.Subset.trans (Set.prod_mono ?_ ?_) ‹_› <;> simp⟩

中文:
定理 prod_self_subset
  条件: {U} (hU : U in 𝓝 (1 : G × G))
  证明: let ⟨V, W, h⟩ := prod_subset hU
  ⟨V ⊓ W, by refine Set.Subset.trans (Set.prod_mono ?_ ?_) ‹_› <;> simp⟩

Depends on / 依赖: Set.Subset.trans, Set.prod_mono, Subset, prod_mono, prod_subset
-/
theorem prod_self_subset {U} (hU : U in 𝓝 (1 : G × G)) :
    exists V : OpenSubgroup G, (V : Set G) ×ˢ (V : Set G) subseteq U :=
  let ⟨V, W, h⟩ := prod_subset hU
  ⟨V ⊓ W, by refine Set.Subset.trans (Set.prod_mono ?_ ?_) ‹_› <;> simp⟩

/-- The Cartesian product of two nonarchimedean groups is nonarchimedean. -/
@[to_additive /-- The Cartesian product of two nonarchimedean groups is nonarchimedean. -/]
/--
Instance `Prod.instNonarchimedeanGroup` / 实例 `Prod.instNonarchimedeanGroup`

English:
instance Prod.instNonarchimedeanGroup
  signature: : NonarchimedeanGroup (G × K) where
  body: let ⟨V, W, h⟩ := prod_subset hU
    ⟨V.prod W, ‹_›⟩

中文:
实例 积类型.instNonarchimedeanGroup
  签名: : Nonarchimedean群 (G × K) where
  定义体: let ⟨V, W, h⟩ := prod_subset hU
    ⟨V.prod W, ‹_›⟩

Depends on / 依赖: V.prod, prod_subset
-/
instance Prod.instNonarchimedeanGroup : NonarchimedeanGroup (G × K) where
  is_nonarchimedean _ hU :=
    let ⟨V, W, h⟩ := prod_subset hU
    ⟨V.prod W, ‹_›⟩

end NonarchimedeanGroup

namespace NonarchimedeanRing

open NonarchimedeanAddGroup

variable {R S : Type*}
variable [Ring R] [TopologicalSpace R] [NonarchimedeanRing R]
variable [Ring S] [TopologicalSpace S] [NonarchimedeanRing S]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonarchimedeanRing (R × S)
  body: NonarchimedeanAddGroup.is_nonarchimedean

中文:
实例 :
  签名: Nonarchimedean环 (R × S)
  定义体: NonarchimedeanAddGroup.is_nonarchimedean

Depends on / 依赖: NonarchimedeanAddGroup, NonarchimedeanAddGroup.is_nonarchimedean, is_nonarchimedean
-/
instance : NonarchimedeanRing (R × S) where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/--
theorem `left_mul_subset` / 定理 `left_mul_subset`

English:
theorem left_mul_subset
  given: (U : OpenAddSubgroup R) (r : R)
  proof: ⟨U.comap (AddMonoidHom.mulLeft r) (continuous_const_mul r), (U : Set R).image_preimage_subset _⟩

中文:
定理 left_mul_subset
  条件: (U : OpenAdd子群 R) (r : R)
  证明: ⟨U.comap (AddMonoidHom.mulLeft r) (continuous_const_mul r), (U : Set R).image_preimage_subset _⟩

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, U.comap, continuous_const_mul, image_preimage_subset, mulLeft
-/
theorem left_mul_subset (U : OpenAddSubgroup R) (r : R) :
    exists V : OpenAddSubgroup R, r • (V : Set R) subseteq U :=
  ⟨U.comap (AddMonoidHom.mulLeft r) (continuous_const_mul r), (U : Set R).image_preimage_subset _⟩

/--
theorem `mul_subset` / 定理 `mul_subset`

English:
theorem mul_subset
  given: (U : OpenAddSubgroup R)
  statement: exists V : OpenAddSubgroup R, (V : Set R) * V subseteq U
  proof: by
let ⟨V, H⟩ := prod_self_subset (U.isOpen.preimage continuous_mul).mem_nhds by
    simpa only [Set.mem_preimage, Prod.snd_zero, mul_zero] using! U.zero_mem
  use V
  rintro v ⟨a, ha, b, hb, hv⟩
  have hy := H (Set.mk_mem_prod ha hb)
  simp only [Set.mem_preimage, SetLike.mem_coe, hv] at hy
  rw [S

中文:
定理 mul_subset
  条件: (U : OpenAdd子群 R)
  结论: 存在 V : OpenAdd子群 R, (V : 集合 R) * V subseteq U
  证明: by
let ⟨V, H⟩ := prod_self_subset (U.isOpen.preimage continuous_mul).mem_nhds by
    simpa only [Set.mem_preimage, Prod.snd_zero, mul_zero] using! U.zero_mem
  use V
  rintro v ⟨a, ha, b, hb, hv⟩
  have hy := H (Set.mk_mem_prod ha hb)
  simp only [Set.mem_preimage, SetLike.mem_coe, hv] at hy
  rw [S

Depends on / 依赖: Prod.snd_zero, Set.mem_preimage, Set.mk_mem_prod, SetLike, SetLike.mem_coe, U.isOpen.preimage, U.zero_mem, continuous_mul, isOpen, mem_coe, mem_nhds, mem_preimage, mk_mem_prod, mul_zero, preimage, prod_self_subset, snd_zero, zero_mem
-/
theorem mul_subset (U : OpenAddSubgroup R) : exists V : OpenAddSubgroup R, (V : Set R) * V subseteq U := by
let ⟨V, H⟩ := prod_self_subset (U.isOpen.preimage continuous_mul).mem_nhds by
    simpa only [Set.mem_preimage, Prod.snd_zero, mul_zero] using! U.zero_mem
  use V
  rintro v ⟨a, ha, b, hb, hv⟩
  have hy := H (Set.mk_mem_prod ha hb)
  simp only [Set.mem_preimage, SetLike.mem_coe, hv] at hy
  rw [SetLike.mem_coe]
  exact hy

end NonarchimedeanRing
