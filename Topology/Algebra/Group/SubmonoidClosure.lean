/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Topological closure of the submonoid closure

In this file we prove several versions of the following statement:
if `G` is a compact topological group and `s : Set G`,
then the topological closures of `Submonoid.closure s` and `Subgroup.closure s` are equal.

The proof is based on the following observation, see `mapClusterPt_self_zpow_atTop_pow`:
each `x^m`, `m : ℤ` is a limit point (`MapClusterPt`) of the sequence `x^n`, `n : ℕ`, as `n → ∞`.
-/

public section

open Filter Function Set
open scoped Topology

variable {G : Type*}

@[to_additive]
/--
theorem `mapClusterPt_atTop_zpow_iff_pow` / 定理 `mapClusterPt_atTop_zpow_iff_pow`

English:
theorem mapClusterPt_atTop_zpow_iff_pow
  given: [DivInvMonoid G] [TopologicalSpace G] {x y : G}
  proof: by
  simp_rw [MapClusterPt, ← Nat.map_cast_int_atTop, map_map, comp_def, zpow_natCast]

中文:
定理 mapClusterPt_atTop_zpow_iff_pow
  条件: [除逆幺半群 G] [拓扑空间 G] {x y : G}
  证明: by
  simp_rw [MapClusterPt, ← Nat.map_cast_int_atTop, map_map, comp_def, zpow_natCast]

Depends on / 依赖: MapClusterPt, Nat.map_cast_int_atTop, comp_def, map_cast_int_atTop, map_map, simp_rw, zpow_natCast
-/
theorem mapClusterPt_atTop_zpow_iff_pow [DivInvMonoid G] [TopologicalSpace G] {x y : G} :
    MapClusterPt x atTop (y ^ · : Int -> G) ↔ MapClusterPt x atTop (y ^ · : Nat -> G) := by
  simp_rw [MapClusterPt, ← Nat.map_cast_int_atTop, map_map, comp_def, zpow_natCast]

variable [Group G] [TopologicalSpace G] [CompactSpace G] [IsTopologicalGroup G]

@[to_additive]
/--
theorem `mapClusterPt_self_zpow_atTop_pow` / 定理 `mapClusterPt_self_zpow_atTop_pow`

English:
theorem mapClusterPt_self_zpow_atTop_pow
  given: (x : G) (m : Int)
  proof: by
  obtain ⟨y, hy⟩ : exists y, MapClusterPt y atTop (x ^ · : Int -> G) :=
    exists_clusterPt_of_compactSpace _
  rw [← mapClusterPt_atTop_zpow_iff_pow]
  have H : MapClusterPt (x ^ m) (atTop.curry atTop) ↿(fun a b => x ^ (m + b - a)) := by
    have : ContinuousAt (fun yz => x ^ m * yz.2 / yz.1) (

中文:
定理 mapClusterPt_self_zpow_atTop_pow
  条件: (x : G) (m : 整数)
  证明: by
  obtain ⟨y, hy⟩ : exists y, MapClusterPt y atTop (x ^ · : Int -> G) :=
    exists_clusterPt_of_compactSpace _
  rw [← mapClusterPt_atTop_zpow_iff_pow]
  have H : MapClusterPt (x ^ m) (atTop.curry atTop) ↿(fun a b => x ^ (m + b - a)) := by
    have : ContinuousAt (fun yz => x ^ m * yz.2 / yz.1) (

Depends on / 依赖: ContinuousAt, MapClusterPt, Prod.map, Tendsto, atTop.curry, comp_def, continuousAt_comp, curry_prodMap, div_eq_mul_inv, exists_clusterPt_of_compactSpace, fun_prop, hy.curry_prodMap, mapClusterPt_atTop_zpow_iff_pow, mul_inv_cancel_right, zpow_add, zpow_sub
-/
theorem mapClusterPt_self_zpow_atTop_pow (x : G) (m : Int) :
    MapClusterPt (x ^ m) atTop (x ^ · : Nat -> G) := by
  obtain ⟨y, hy⟩ : exists y, MapClusterPt y atTop (x ^ · : Int -> G) :=
    exists_clusterPt_of_compactSpace _
  rw [← mapClusterPt_atTop_zpow_iff_pow]
  have H : MapClusterPt (x ^ m) (atTop.curry atTop) ↿(fun a b => x ^ (m + b - a)) := by
    have : ContinuousAt (fun yz => x ^ m * yz.2 / yz.1) (y, y) := by fun_prop
    simpa only [comp_def, ← zpow_sub, ← zpow_add, div_eq_mul_inv, Prod.map, mul_inv_cancel_right]
      using! (hy.curry_prodMap hy).continuousAt_comp this
  suffices Tendsto ↿(fun a b => m + b - a) (atTop.curry atTop) atTop from H.of_comp this
refine Tendsto.curry .of_forall fun a => ?_
  simp only [sub_eq_add_neg] -- TODO: add `Tendsto.atTop_sub_const` etc
  exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_left atTop m tendsto_id)

@[to_additive]
/--
theorem `mapClusterPt_one_atTop_pow` / 定理 `mapClusterPt_one_atTop_pow`

English:
theorem mapClusterPt_one_atTop_pow
  given: (x : G)
  statement: MapClusterPt 1 atTop (x ^ · : Nat -> G)
  proof: by
  simpa using mapClusterPt_self_zpow_atTop_pow x 0

@[to_additive]

中文:
定理 mapClusterPt_one_atTop_pow
  条件: (x : G)
  结论: MapClusterPt 1 atTop (x ^ · : 自然数 -> G)
  证明: by
  simpa using mapClusterPt_self_zpow_atTop_pow x 0

@[to_additive]

Depends on / 依赖: mapClusterPt_self_zpow_atTop_pow
-/
theorem mapClusterPt_one_atTop_pow (x : G) : MapClusterPt 1 atTop (x ^ · : Nat -> G) := by
  simpa using mapClusterPt_self_zpow_atTop_pow x 0

@[to_additive]
/--
theorem `mapClusterPt_self_atTop_pow` / 定理 `mapClusterPt_self_atTop_pow`

English:
theorem mapClusterPt_self_atTop_pow
  given: (x : G)
  statement: MapClusterPt x atTop (x ^ · : Nat -> G)
  proof: by
  simpa using mapClusterPt_self_zpow_atTop_pow x 1

@[to_additive]

中文:
定理 mapClusterPt_self_atTop_pow
  条件: (x : G)
  结论: MapClusterPt x atTop (x ^ · : 自然数 -> G)
  证明: by
  simpa using mapClusterPt_self_zpow_atTop_pow x 1

@[to_additive]

Depends on / 依赖: mapClusterPt_self_zpow_atTop_pow
-/
theorem mapClusterPt_self_atTop_pow (x : G) : MapClusterPt x atTop (x ^ · : Nat -> G) := by
  simpa using mapClusterPt_self_zpow_atTop_pow x 1

@[to_additive]
/--
theorem `mapClusterPt_atTop_pow_tfae` / 定理 `mapClusterPt_atTop_pow_tfae`

English:
theorem mapClusterPt_atTop_pow_tfae
  given: (x y : G)
  proof: by
  tfae_have 2 ↔ 1 := mapClusterPt_atTop_zpow_iff_pow
  tfae_have 3 -> 4 := by
    refine fun h => closure_mono (range_subset_iff.2 fun n => ?_) h
    exact ⟨n, zpow_natCast _ _⟩
  tfae_have 4 -> 1 := by
    refine fun h => closure_minimal ?_ isClosed_setOfPred_clusterPt h
    exact range_subset_i

中文:
定理 mapClusterPt_atTop_pow_tfae
  条件: (x y : G)
  证明: by
  tfae_have 2 ↔ 1 := mapClusterPt_atTop_zpow_iff_pow
  tfae_have 3 -> 4 := by
    refine fun h => closure_mono (range_subset_iff.2 fun n => ?_) h
    exact ⟨n, zpow_natCast _ _⟩
  tfae_have 4 -> 1 := by
    refine fun h => closure_minimal ?_ isClosed_setOfPred_clusterPt h
    exact range_subset_i

Depends on / 依赖: ClusterPt, ClusterPt.mono, closure_minimal, closure_mono, isClosed_setOfPred_clusterPt, le_principal_iff, mapClusterPt_atTop_zpow_iff_pow, mapClusterPt_self_zpow_atTop_pow, mem_closure_iff_clusterPt, range_mem_map, range_subset_iff, tfae_finish, tfae_have, zpow_natCast
-/
theorem mapClusterPt_atTop_pow_tfae (x y : G) :
    List.TFAE [
      MapClusterPt x atTop (y ^ · : Nat -> G),
      MapClusterPt x atTop (y ^ · : Int -> G),
      x in closure (range (y ^ · : Nat -> G)),
      x in closure (range (y ^ · : Int -> G)),
    ] := by
  tfae_have 2 ↔ 1 := mapClusterPt_atTop_zpow_iff_pow
  tfae_have 3 -> 4 := by
    refine fun h => closure_mono (range_subset_iff.2 fun n => ?_) h
    exact ⟨n, zpow_natCast _ _⟩
  tfae_have 4 -> 1 := by
    refine fun h => closure_minimal ?_ isClosed_setOfPred_clusterPt h
    exact range_subset_iff.2 (mapClusterPt_self_zpow_atTop_pow _)
  tfae_have 1 -> 3 := by
    rw [mem_closure_iff_clusterPt]
    exact (ClusterPt.mono · (le_principal_iff.2 range_mem_map))
  tfae_finish

@[to_additive]
/--
theorem `mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers` / 定理 `mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers`

English:
theorem mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers
  given: {x y : G}
  proof: (mapClusterPt_atTop_pow_tfae x y).out 0 3

@[to_additive (attr := simp)]

中文:
定理 mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers
  条件: {x y : G}
  证明: (mapClusterPt_atTop_pow_tfae x y).out 0 3

@[to_additive (attr := simp)]

Depends on / 依赖: mapClusterPt_atTop_pow_tfae
-/
theorem mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers {x y : G} :
    MapClusterPt x atTop (y ^ · : Nat -> G) ↔ x in (Subgroup.zpowers y).topologicalClosure :=
  (mapClusterPt_atTop_pow_tfae x y).out 0 3

@[to_additive (attr := simp)]
/--
theorem `mapClusterPt_inv_atTop_pow` / 定理 `mapClusterPt_inv_atTop_pow`

English:
theorem mapClusterPt_inv_atTop_pow
  given: {x y : G}
  proof: by
  simp only [mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers, inv_mem_iff]

@[to_additive]

中文:
定理 mapClusterPt_inv_atTop_pow
  条件: {x y : G}
  证明: by
  simp only [mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers, inv_mem_iff]

@[to_additive]

Depends on / 依赖: inv_mem_iff, mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers
-/
theorem mapClusterPt_inv_atTop_pow {x y : G} :
    MapClusterPt x⁻¹ atTop (y ^ · : Nat -> G) ↔ MapClusterPt x atTop (y ^ · : Nat -> G) := by
  simp only [mapClusterPt_atTop_pow_iff_mem_topologicalClosure_zpowers, inv_mem_iff]

@[to_additive]
/--
theorem `closure_range_zpow_eq_pow` / 定理 `closure_range_zpow_eq_pow`

English:
theorem closure_range_zpow_eq_pow
  given: (x : G)
  proof: by
  ext y
  exact (mapClusterPt_atTop_pow_tfae y x).out 3 2

@[to_additive]

中文:
定理 closure_range_zpow_eq_pow
  条件: (x : G)
  证明: by
  ext y
  exact (mapClusterPt_atTop_pow_tfae y x).out 3 2

@[to_additive]

Depends on / 依赖: mapClusterPt_atTop_pow_tfae
-/
theorem closure_range_zpow_eq_pow (x : G) :
    closure (range (x ^ · : Int -> G)) = closure (range (x ^ · : Nat -> G)) := by
  ext y
  exact (mapClusterPt_atTop_pow_tfae y x).out 3 2

@[to_additive]
/--
theorem `denseRange_zpow_iff_pow` / 定理 `denseRange_zpow_iff_pow`

English:
theorem denseRange_zpow_iff_pow
  given: {x : G}
  proof: by
  simp only [DenseRange, dense_iff_closure_eq, closure_range_zpow_eq_pow]

@[to_additive]

中文:
定理 denseRange_zpow_iff_pow
  条件: {x : G}
  证明: by
  simp only [DenseRange, dense_iff_closure_eq, closure_range_zpow_eq_pow]

@[to_additive]

Depends on / 依赖: DenseRange, closure_range_zpow_eq_pow, dense_iff_closure_eq
-/
theorem denseRange_zpow_iff_pow {x : G} :
    DenseRange (x ^ · : Int -> G) ↔ DenseRange (x ^ · : Nat -> G) := by
  simp only [DenseRange, dense_iff_closure_eq, closure_range_zpow_eq_pow]

@[to_additive]
/--
theorem `topologicalClosure_subgroupClosure_toSubmonoid` / 定理 `topologicalClosure_subgroupClosure_toSubmonoid`

English:
theorem topologicalClosure_subgroupClosure_toSubmonoid
  given: (s : Set G)
  proof: by
  refine le_antisymm ?_ (closure_mono <| Subgroup.le_closure_toSubmonoid _)
  refine Submonoid.topologicalClosure_minimal _ ?_ isClosed_closure
  rw [Subgroup.closure_toSubmonoid]; rw [Submonoid.closure_le]
  refine union_subset (Submonoid.subset_closure.trans subset_closure) fun x hx => ?_
  ref

中文:
定理 topologicalClosure_subgroupClosure_toSubmonoid
  条件: (s : 集合 G)
  证明: by
  refine le_antisymm ?_ (closure_mono <| Subgroup.le_closure_toSubmonoid _)
  refine Submonoid.topologicalClosure_minimal _ ?_ isClosed_closure
  rw [Subgroup.closure_toSubmonoid]; rw [Submonoid.closure_le]
  refine union_subset (Submonoid.subset_closure.trans subset_closure) fun x hx => ?_
  ref

Depends on / 依赖: Set.mem_inv, Subgroup, Subgroup.closure_toSubmonoid, Subgroup.coe_zpowers, Subgroup.le_closure_toSubmonoid, Subgroup.topologicalClo, Submonoid, Submonoid.closure_le, Submonoid.coe_powers, Submonoid.powers_le, Submonoid.subset_closure, Submonoid.subset_closure.trans, Submonoid.topologicalClosure_minimal, closure_le, closure_mono, closure_range_zpow_eq_pow, closure_toSubmonoid, coe_powers, coe_zpowers, isClosed_closure
-/
theorem topologicalClosure_subgroupClosure_toSubmonoid (s : Set G) :
    (Subgroup.closure s).toSubmonoid.topologicalClosure =
      (Submonoid.closure s).topologicalClosure := by
  refine le_antisymm ?_ (closure_mono <| Subgroup.le_closure_toSubmonoid _)
  refine Submonoid.topologicalClosure_minimal _ ?_ isClosed_closure
  rw [Subgroup.closure_toSubmonoid]; rw [Submonoid.closure_le]
  refine union_subset (Submonoid.subset_closure.trans subset_closure) fun x hx => ?_
  refine closure_mono (Submonoid.powers_le.2 (Submonoid.subset_closure <| Set.mem_inv.1 hx)) ?_
  rw [Submonoid.coe_powers]; rw [← closure_range_zpow_eq_pow]; rw [← Subgroup.coe_zpowers]; rw [← Subgroup.topologicalClosure_coe]; rw [SetLike.mem_coe]; rw [← inv_mem_iff]
exact subset_closure Subgroup.mem_zpowers _

@[to_additive]
/--
theorem `closure_submonoidClosure_eq_closure_subgroupClosure` / 定理 `closure_submonoidClosure_eq_closure_subgroupClosure`

English:
theorem closure_submonoidClosure_eq_closure_subgroupClosure
  given: (s : Set G)
  proof: congrArg SetLike.coe (topologicalClosure_subgroupClosure_toSubmonoid s).symm

@[to_additive]

中文:
定理 closure_submonoidClosure_eq_closure_subgroupClosure
  条件: (s : 集合 G)
  证明: congrArg SetLike.coe (topologicalClosure_subgroupClosure_toSubmonoid s).symm

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe, topologicalClosure_subgroupClosure_toSubmonoid
-/
theorem closure_submonoidClosure_eq_closure_subgroupClosure (s : Set G) :
    closure (Submonoid.closure s : Set G) = closure (Subgroup.closure s) :=
  congrArg SetLike.coe (topologicalClosure_subgroupClosure_toSubmonoid s).symm

@[to_additive]
/--
theorem `dense_submonoidClosure_iff_subgroupClosure` / 定理 `dense_submonoidClosure_iff_subgroupClosure`

English:
theorem dense_submonoidClosure_iff_subgroupClosure
  given: {s : Set G}
  proof: by
  simp only [dense_iff_closure_eq, closure_submonoidClosure_eq_closure_subgroupClosure]

中文:
定理 dense_submonoidClosure_iff_subgroupClosure
  条件: {s : 集合 G}
  证明: by
  simp only [dense_iff_closure_eq, closure_submonoidClosure_eq_closure_subgroupClosure]

Depends on / 依赖: closure_submonoidClosure_eq_closure_subgroupClosure, dense_iff_closure_eq
-/
theorem dense_submonoidClosure_iff_subgroupClosure {s : Set G} :
    Dense (Submonoid.closure s : Set G) ↔ Dense (Subgroup.closure s : Set G) := by
  simp only [dense_iff_closure_eq, closure_submonoidClosure_eq_closure_subgroupClosure]
