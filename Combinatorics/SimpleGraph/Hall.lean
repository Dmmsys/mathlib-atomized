/-
Copyright (c) 2025 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Hall's Marriage Theorem

This file derives Hall's Marriage Theorem for bipartite graphs from the combinatorial formulation in
`Mathlib/Combinatorics/Hall/Basic.lean`.

## Main statements

* `exists_isMatching_of_forall_ncard_le`: Hall's marriage theorem for a matching on a single
  partition of a bipartite graph.
* `exists_isPerfectMatching_of_forall_ncard_le`: Hall's marriage theorem for a perfect matching on a
  bipartite graph.

## Tags

Hall's Marriage Theorem
-/

public section

open Function

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Given a partition `p` and a function `f` mapping vertices in `p` to the other partition, create
the subgraph including only the edges between `x` and `f x` for all `x` in `p`. -/
private
/--
Definition of `hall_subgraph` / `hall_subgraph` 的定义

English:
abbreviation hall_subgraph
  signature: {p : Set V} [DecidablePred (· in p)] (f : p -> V) (h₁ : forall x : p, f x ∉ p)
  body: p union Set.range f
  Adj v w :=
    if h : v in p then f ⟨v, h⟩ = w
    else if h : w in p then f ⟨w, h⟩ = v
    else False
  adj_sub {v w} h := by
    split_ifs at h
    · exact h ▸ h₂ ⟨v, by assumption⟩
.symm · exact h ▸ h₂ ⟨w, by assumption⟩
  edge_vert := by grind
  symm.symm := by grind

中文:
缩写 hall_subgraph
  签名: {p : Set V} [DecidablePred (· in p)] (f : p -> V) (h₁ : 对任意 x : p, f x ∉ p)
  定义体: p union Set.range f
  Adj v w :=
    if h : v in p then f ⟨v, h⟩ = w
    else if h : w in p then f ⟨w, h⟩ = v
    else False
  adj_sub {v w} h := by
    split_ifs at h
    · exact h ▸ h₂ ⟨v, by assumption⟩
.symm · exact h ▸ h₂ ⟨w, by assumption⟩
  edge_vert := by grind
  symm.symm := by grind

Depends on / 依赖: Set.range
-/
abbrev hall_subgraph {p : Set V} [DecidablePred (· in p)] (f : p -> V) (h₁ : forall x : p, f x ∉ p)
    (h₂ : forall x : p, G.Adj x (f x)) : Subgraph G where
  verts := p union Set.range f
  Adj v w :=
    if h : v in p then f ⟨v, h⟩ = w
    else if h : w in p then f ⟨w, h⟩ = v
    else False
  adj_sub {v w} h := by
    split_ifs at h
    · exact h ▸ h₂ ⟨v, by assumption⟩
.symm · exact h ▸ h₂ ⟨w, by assumption⟩
  edge_vert := by grind
  symm.symm := by grind

variable [G.LocallyFinite] {p₁ p₂ : Set V}

/--
theorem `exists_isMatching_of_forall_ncard_le` / 定理 `exists_isMatching_of_forall_ncard_le`

English:
theorem exists_isMatching_of_forall_ncard_le
  statement: (h₁ : G.IsBipartiteWith p₁ p₂)
  proof: by
  classical
  obtain ⟨f, hf₁, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
.mp fun s => by (fun (x : p₁) => G.neighborFinset x)
    have := h₂ (s.image Subtype.val) (by simp)
    rw [Set.ncard_coe_finset]; rw [Finset.card_image_of_injective _ Subtype.val_injective] at this
    sim

中文:
定理 exists_isMatching_of_forall_ncard_le
  结论: (h₁ : G.IsBipartiteWith p₁ p₂)
  证明: by
  classical
  obtain ⟨f, hf₁, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
.mp fun s => by (fun (x : p₁) => G.neighborFinset x)
    have := h₂ (s.image Subtype.val) (by simp)
    rw [Set.ncard_coe_finset]; rw [Finset.card_image_of_injective _ Subtype.val_injective] at this
    sim

Depends on / 依赖: Finset, Finset.all_card_le_biUnion_card_iff_exists_injective, Finset.card_image_of_injective, G.me, G.neighborFinset, Set.mem_toFinset.mp, Set.ncard_coe_finset, Subtype, Subtype.val, Subtype.val_injective, all_card_le_biUnion_card_iff_exists_injective, card_image_of_injective, classical, disjoint, hall_subgraph, isBipartiteWith_neighborSet_subset, mem_toFinset, ncard_coe_finset, neighborFinset, neighborFinset_def
-/
theorem exists_isMatching_of_forall_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : forall s subseteq p₁, s.ncard <= (⋃ x in s, G.neighborSet x).ncard) :
    exists M : Subgraph G, p₁ subseteq M.verts ∧ M.IsMatching := by
  classical
  obtain ⟨f, hf₁, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
.mp fun s => by (fun (x : p₁) => G.neighborFinset x)
    have := h₂ (s.image Subtype.val) (by simp)
    rw [Set.ncard_coe_finset]; rw [Finset.card_image_of_injective _ Subtype.val_injective] at this
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
.notMem_of_mem_right have (x : p₁) : f x ∉ p₁ := h₁.disjoint
isBipartiteWith_neighborSet_subset h₁ x.2 Set.mem_toFinset.mp hf₂ x
  use hall_subgraph f this (fun v => G.mem_neighborFinset _ _ |>.mp <| hf₂ v)
  refine ⟨by simp, fun v hv => ?_⟩
  simp only [Set.mem_union, Set.mem_range, Subtype.exists] at hv ⊢
  rcases hv with h' | ⟨x, hx₁, hx₂⟩
  · exact ⟨f ⟨v, h'⟩, by simp_all⟩
  · use x
    have := hx₂ ▸ this ⟨x, hx₁⟩
    simp only [this, ↓reduceDIte, hx₁, hx₂, dite_else_false, forall_exists_index, true_and]
exact fun _ _ k => Subtype.ext_iff.mp hf₁ (hx₂ ▸ k)

/--
lemma `union_eq_univ_of_forall_ncard_le` / 引理 `union_eq_univ_of_forall_ncard_le`

English:
lemma union_eq_univ_of_forall_ncard_le
  statement: (h₁ : G.IsBipartiteWith p₁ p₂)
  proof: by
  classical
  obtain ⟨f, _, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
.mp fun s => by (fun x => G.neighborFinset x)
    have := h₂ s
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
have := h₁.mem_of_adj .mp (hf₂ x) G.mem_ne

中文:
引理 union_eq_univ_of_forall_ncard_le
  结论: (h₁ : G.IsBipartiteWith p₁ p₂)
  证明: by
  classical
  obtain ⟨f, _, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
.mp fun s => by (fun x => G.neighborFinset x)
    have := h₂ s
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
have := h₁.mem_of_adj .mp (hf₂ x) G.mem_ne

Depends on / 依赖: Finset, Finset.all_card_le_biUnion_card_iff_exists_injective, G.mem_neighborFinset, G.neighborFinset, Set.eq_univ_iff_forall.mpr, Set.ncard_coe_finset, all_card_le_biUnion_card_iff_exists_injective, classical, eq_univ_iff_forall, mem_neighborFinset, mem_of_adj, ncard_coe_finset, neighborFinset, neighborFinset_def
-/
lemma union_eq_univ_of_forall_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : forall s : Set V, s.ncard <= (⋃ x in s, G.neighborSet x).ncard) : p₁ union p₂ = Set.univ := by
  classical
  obtain ⟨f, _, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
.mp fun s => by (fun x => G.neighborFinset x)
    have := h₂ s
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
have := h₁.mem_of_adj .mp (hf₂ x) G.mem_neighborFinset _ _
  grind

/--
lemma `exists_bijective_of_forall_ncard_le` / 引理 `exists_bijective_of_forall_ncard_le`

English:
lemma exists_bijective_of_forall_ncard_le
  statement: (h₁ : G.IsBipartiteWith p₁ p₂)
  proof: by
  classical
  obtain ⟨f, hf₁, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
.mp fun s => by (fun x => G.neighborFinset x)
    have := h₂ s
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
.notMem_of_mem_right have (x : V) (h : x in p₁) : f x ∉ p₁ := h₁.disjoint
isBipartiteWit

中文:
引理 exists_bijective_of_forall_ncard_le
  结论: (h₁ : G.IsBipartiteWith p₁ p₂)
  证明: by
  classical
  obtain ⟨f, hf₁, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
.mp fun s => by (fun x => G.neighborFinset x)
    have := h₂ s
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
.notMem_of_mem_right have (x : V) (h : x in p₁) : f x ∉ p₁ := h₁.disjoint
isBipartiteWit

Depends on / 依赖: Finset, Finset.all_card_le_biUnion_card_iff_exists_injective, G.neighborFinset, Set.mem_toFinset.mp, Set.ncard_coe_finset, all_card_le_biUnion_card_iff_exists_injective, classical, disjoint, isBipartiteWith_neighborSet_subset, mem_toFinset, ncard_coe_finset, neighborFinset, neighborFinset_def, notMem_of_mem_left, notMem_of_mem_right
-/
lemma exists_bijective_of_forall_ncard_le (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : forall s : Set V, s.ncard <= (⋃ x in s, G.neighborSet x).ncard) :
    exists (h : p₁ -> p₂), Function.Bijective h ∧ forall (a : p₁), G.Adj a (h a) := by
  classical
  obtain ⟨f, hf₁, hf₂⟩ := Finset.all_card_le_biUnion_card_iff_exists_injective
.mp fun s => by (fun x => G.neighborFinset x)
    have := h₂ s
    simpa [← Set.ncard_coe_finset, neighborFinset_def]
.notMem_of_mem_right have (x : V) (h : x in p₁) : f x ∉ p₁ := h₁.disjoint
isBipartiteWith_neighborSet_subset h₁ h Set.mem_toFinset.mp hf₂ x
.notMem_of_mem_left have (x : V) (h : x in p₂) : f x ∉ p₂ := h₁.disjoint
isBipartiteWith_neighborSet_subset h₁.symm h Set.mem_toFinset.mp hf₂ x
  have (x : V) : f x in p₁ ∨ f x in p₂ := by
    simp [union_eq_univ_of_forall_ncard_le h₁ h₂, p₁.mem_union (f x) p₂ |>.mp]
  let f' (x : p₁) : p₂ := ⟨f x, by grind⟩
  let g' (x : p₂) : p₁ := ⟨f x, by grind⟩
  refine Embedding.schroeder_bernstein_of_rel (f := f') (g := g') ?_ ?_ (fun x y => G.Adj x y) ?_ ?_
· exact Injective.of_comp (f := Subtype.val) hf₁.comp Subtype.val_injective
· exact Injective.of_comp (f := Subtype.val) hf₁.comp Subtype.val_injective
.mp (hf₂ v) · exact fun v => mem_neighborFinset _ _ _
.symm .mp (hf₂ v) · exact fun v => mem_neighborFinset _ _ _

/--
theorem `exists_isPerfectMatching_of_forall_ncard_le` / 定理 `exists_isPerfectMatching_of_forall_ncard_le`

English:
theorem exists_isPerfectMatching_of_forall_ncard_le
  proof: by
  classical
  obtain ⟨b, hb₁, hb₂⟩ := exists_bijective_of_forall_ncard_le h₁ h₂
  use hall_subgraph (fun v => b v) (fun v => h₁.disjoint.notMem_of_mem_right (b v).property) hb₂
  have : p₁ union Set.range (fun v => (b v).1) = Set.univ := by
    rw [Set.range_comp']; rw [hb₁.surjective.range_eq]; 

中文:
定理 exists_isPerfectMatching_of_forall_ncard_le
  证明: by
  classical
  obtain ⟨b, hb₁, hb₂⟩ := exists_bijective_of_forall_ncard_le h₁ h₂
  use hall_subgraph (fun v => b v) (fun v => h₁.disjoint.notMem_of_mem_right (b v).property) hb₂
  have : p₁ union Set.range (fun v => (b v).1) = Set.univ := by
    rw [Set.range_comp']; rw [hb₁.surjective.range_eq]; 

Depends on / 依赖: Set.range, Set.range_comp, Set.univ, Subgraph, Subgraph.isSpanning_iff.mpr, Subtype, Subtype.coe_image_univ, classical, coe_image_univ, disjoint, disjoint.notMem_of_mem_right, dite_else_false, existsUnique_eq, exists_bijective_of_forall_ncard_le, hall_subgraph, isSpanning_iff, notMem_of_mem_right, property, range_comp, range_eq
-/
theorem exists_isPerfectMatching_of_forall_ncard_le
    (h₁ : G.IsBipartiteWith p₁ p₂) (h₂ : forall s : Set V, s.ncard <= (⋃ x in s, G.neighborSet x).ncard) :
    exists M : Subgraph G, M.IsPerfectMatching := by
  classical
  obtain ⟨b, hb₁, hb₂⟩ := exists_bijective_of_forall_ncard_le h₁ h₂
  use hall_subgraph (fun v => b v) (fun v => h₁.disjoint.notMem_of_mem_right (b v).property) hb₂
  have : p₁ union Set.range (fun v => (b v).1) = Set.univ := by
    rw [Set.range_comp']; rw [hb₁.surjective.range_eq]; rw [Subtype.coe_image_univ]
    exact union_eq_univ_of_forall_ncard_le h₁ h₂
  refine ⟨fun v _ => ?_, Subgraph.isSpanning_iff.mpr this⟩
  simp only [dite_else_false]
  split
  · exact existsUnique_eq'
  · obtain ⟨x, _⟩ := hb₁.existsUnique ⟨v, by grind⟩
    exact ⟨x, by grind⟩

end SimpleGraph
