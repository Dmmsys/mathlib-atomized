/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Kevin Buzzard, David Loeffler, Yongle Hu, Johan Commelin
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Total separatedness of nonarchimedean groups

In this file, we prove that a nonarchimedean group is a totally separated topological space.
The fact that a nonarchimedean group is a totally disconnected topological space
is implied by the fact that a nonarchimedean group is totally separated.

## Main results

- `NonarchimedeanGroup.instTotallySeparated`:
  A nonarchimedean group is a totally separated topological space.

## Notation

- `G` : Is a nonarchimedean group.
- `V` : Is an open subgroup which is a neighbourhood of the identity in `G`.

## References

See Proposition 2.3.9 and Problem 63 in [F. Q. Gouvêa, *p-adic numbers*][gouvea1997].
-/

public section

open scoped Pointwise

variable {G : Type*} [TopologicalSpace G] [Group G] [NonarchimedeanGroup G] [T2Space G]

namespace NonarchimedeanGroup

@[to_additive]
/--
lemma `exists_openSubgroup_separating` / 引理 `exists_openSubgroup_separating`

English:
lemma exists_openSubgroup_separating
  given: {a b : G} (h : a != b)
  proof: by
  obtain ⟨u, v, _, open_v, mem_u, mem_v, dis⟩ := t2_separation (h ∘ inv_mul_eq_one.mp)
  obtain ⟨V, hV⟩ := is_nonarchimedean v (open_v.mem_nhds mem_v)
  use V
  simp only [Disjoint, Set.bot_eq_empty, Set.subset_empty_iff]
  intro x mem_aV mem_bV
  by_contra! ⟨s, hs⟩
  have hsa : s in a • (V : Set G) := mem_aV hs
  have hsb : s in b • (V : Set G) := mem_bV hs
  rw [mem_leftCoset_iff] at hsa hsb
  refine dis.subset_compl_right mem_u (hV ?_)
  simpa [mul_assoc] using mul_mem hsa (inv_mem hsb)

@[to_additive]

中文:
引理 存在_openSubgroup_separating
  条件: {a b : G} (h : a != b)
  证明: by
  obtain ⟨u, v, _, open_v, mem_u, mem_v, dis⟩ := t2_separation (h ∘ inv_mul_eq_one.mp)
  obtain ⟨V, hV⟩ := is_nonarchimedean v (open_v.mem_nhds mem_v)
  use V
  simp only [Disjoint, Set.bot_eq_empty, Set.subset_empty_iff]
  intro x mem_aV mem_bV
  by_contra! ⟨s, hs⟩
  have hsa : s in a • (V : Set G) := mem_aV hs
  have hsb : s in b • (V : Set G) := mem_bV hs
  rw [mem_leftCoset_iff] at hsa hsb
  refine dis.subset_compl_right mem_u (hV ?_)
  simpa [mul_assoc] using mul_mem hsa (inv_mem hsb)

@[to_additive]

Depends on / 依赖: Disjoint, Set.bot_eq_empty, Set.subset_empty_iff, bot_eq_empty, dis.subset_compl_right, inv_mem, inv_mul_eq_one, inv_mul_eq_one.mp, is_nonarchimedean, mem_aV, mem_bV, mem_leftCoset_iff, mem_nhds, mem_u, mem_v, mul_assoc, mul_mem, open_v, open_v.mem_nhds, subset_compl_right
-/
lemma exists_openSubgroup_separating {a b : G} (h : a != b) :
    exists V : OpenSubgroup G, Disjoint (a • (V : Set G)) (b • V) := by
  obtain ⟨u, v, _, open_v, mem_u, mem_v, dis⟩ := t2_separation (h ∘ inv_mul_eq_one.mp)
  obtain ⟨V, hV⟩ := is_nonarchimedean v (open_v.mem_nhds mem_v)
  use V
  simp only [Disjoint, Set.bot_eq_empty, Set.subset_empty_iff]
  intro x mem_aV mem_bV
  by_contra! ⟨s, hs⟩
  have hsa : s in a • (V : Set G) := mem_aV hs
  have hsb : s in b • (V : Set G) := mem_bV hs
  rw [mem_leftCoset_iff] at hsa hsb
  refine dis.subset_compl_right mem_u (hV ?_)
  simpa [mul_assoc] using mul_mem hsa (inv_mem hsb)

@[to_additive]
instance (priority := 100) instTotallySeparated : TotallySeparatedSpace G where
  isTotallySeparated_univ x _ y _ hxy := by
    obtain ⟨V, dxy⟩ := exists_openSubgroup_separating hxy
    exact ⟨_, _, V.isOpen.smul x, (V.isClosed.smul x).isOpen_compl, mem_own_leftCoset ..,
dxy.subset_compl_left mem_own_leftCoset .., by simp, disjoint_compl_right⟩

end NonarchimedeanGroup
