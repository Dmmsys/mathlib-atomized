/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Analysis.Convex.Combination

/-!
# Partition of unity and convex sets

In this file we prove the following lemma, see `exists_continuous_forall_mem_convex_of_local`. Let
`X` be a normal paracompact topological space (e.g., any extended metric space). Let `E` be a
topological real vector space. Let `t : X → Set E` be a family of convex sets. Suppose that for each
point `x : X`, there exists a neighborhood `U ∈ 𝓝 X` and a function `g : X → E` that is continuous
on `U` and sends each `y ∈ U` to a point of `t y`. Then there exists a continuous map `g : C(X, E)`
such that `g x ∈ t x` for all `x`.

We also formulate a useful corollary, see `exists_continuous_forall_mem_convex_of_local_const`, that
assumes that local functions `g` are constants.

## Tags

partition of unity
-/

public section


open Set Function

open Topology

variable {ι X E : Type*} [TopologicalSpace X] [AddCommGroup E] [Module Real E]

/--
theorem `PartitionOfUnity.finsum_smul_mem_convex` / 定理 `PartitionOfUnity.finsum_smul_mem_convex`

English:
theorem PartitionOfUnity.finsum_smul_mem_convex
  statement: {s : Set X} (f : PartitionOfUnity ι X s)
  proof: ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg

中文:
定理 PartitionOfUnity.finsum_smul_mem_convex
  结论: {s : Set X} (f : PartitionOfUnity ι X s)
  证明: ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg

Depends on / 依赖: f.nonneg, f.sum_eq_one, finsum_mem, ht.finsum_mem, nonneg, sum_eq_one
-/
theorem PartitionOfUnity.finsum_smul_mem_convex {s : Set X} (f : PartitionOfUnity ι X s)
    {g : ι -> X -> E} {t : Set E} {x : X} (hx : x in s) (hg : forall i, f i x != 0 -> g i x in t)
    (ht : Convex Real t) : (∑ᶠ i, f i x • g i x) in t :=
  ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg

variable [NormalSpace X] [ParacompactSpace X] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul Real E] {t : X -> Set E}

/--
theorem `exists_continuous_forall_mem_convex_of_local` / 定理 `exists_continuous_forall_mem_convex_of_local`

English:
theorem exists_continuous_forall_mem_convex_of_local
  statement: (ht : forall x, Convex Real (t x))
  proof: by
  choose U hU g hgc hgt using H
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun x => interior (U x))
    (fun x => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  refine ⟨⟨fun x => ∑ᶠ i, f i x • g i x,
    hf.continuous_finsum_smul (

中文:
定理 exists_continuous_forall_mem_convex_of_local
  结论: (ht : 对任意 x, Convex 实数 (t x))
  证明: by
  choose U hU g hgc hgt using H
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun x => interior (U x))
    (fun x => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  refine ⟨⟨fun x => ∑ᶠ i, f i x • g i x,
    hf.continuous_finsum_smul (

Depends on / 依赖: PartitionOfUnity, PartitionOfUnity.exists_isSubordinate, continuous_finsum_smul, exists_isSubordinate, f.finsum_smul_mem_convex, finsum_smul_mem_convex, hf.continuous_finsum_smul, interior, interior_subset, isClosed_univ, isOpen_interior, mem_iUnion, mem_interior_iff_mem_nhds, mem_univ, subset_closure
-/
theorem exists_continuous_forall_mem_convex_of_local (ht : forall x, Convex Real (t x))
    (H : forall x : X, exists U in 𝓝 x, exists g : X -> E, ContinuousOn g U ∧ forall y in U, g y in t y) :
    exists g : C(X, E), forall x, g x in t x := by
  choose U hU g hgc hgt using H
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun x => interior (U x))
    (fun x => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  refine ⟨⟨fun x => ∑ᶠ i, f i x • g i x,
    hf.continuous_finsum_smul (fun i => isOpen_interior) fun i => (hgc i).mono interior_subset⟩,
    fun x => f.finsum_smul_mem_convex (mem_univ x) (fun i hi => hgt _ _ ?_) (ht _)⟩
  exact interior_subset (hf _ <| subset_closure hi)

/--
theorem `exists_continuous_forall_mem_convex_of_local_const` / 定理 `exists_continuous_forall_mem_convex_of_local_const`

English:
theorem exists_continuous_forall_mem_convex_of_local_const
  statement: (ht : forall x, Convex Real (t x))
  proof: exists_continuous_forall_mem_convex_of_local ht fun x =>
    let ⟨c, hc⟩ := H x
    ⟨_, hc, fun _ => c, continuousOn_const, fun _ => id⟩

中文:
定理 exists_continuous_forall_mem_convex_of_local_const
  结论: (ht : 对任意 x, Convex 实数 (t x))
  证明: exists_continuous_forall_mem_convex_of_local ht fun x =>
    let ⟨c, hc⟩ := H x
    ⟨_, hc, fun _ => c, continuousOn_const, fun _ => id⟩

Depends on / 依赖: continuousOn_const, exists_continuous_forall_mem_convex_of_local
-/
theorem exists_continuous_forall_mem_convex_of_local_const (ht : forall x, Convex Real (t x))
    (H : forall x : X, exists c : E, forallᶠ y in 𝓝 x, c in t y) : exists g : C(X, E), forall x, g x in t x :=
  exists_continuous_forall_mem_convex_of_local ht fun x =>
    let ⟨c, hc⟩ := H x
    ⟨_, hc, fun _ => c, continuousOn_const, fun _ => id⟩
