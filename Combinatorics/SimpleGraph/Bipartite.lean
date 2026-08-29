/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Bipartite graphs

This file proves results about bipartite simple graphs, including several double-counting arguments.

## Main definitions

* `SimpleGraph.IsBipartiteWith G s t` is the condition that a simple graph `G` is bipartite in sets
  `s`, `t`, that is, `s` and `t` are disjoint and vertices `v`, `w` being adjacent in `G` implies
  that `v ∈ s` and `w ∈ t`, or `v ∈ t` and `w ∈ s`.

  Note that in this implementation, if `G.IsBipartiteWith s t`, `s ∪ t` need not cover the vertices
  of `G`, instead `s ∪ t` is only required to cover the *support* of `G`, that is, the vertices
  that form edges in `G`. This definition is equivalent to the expected definition. If `s` and `t`
  do not cover all the vertices, one recovers a covering of all the vertices by unioning the
  missing vertices `(s ∪ t)ᶜ` to either `s` or `t`.

* `SimpleGraph.IsBipartite`: Predicate for a simple graph to be bipartite.
  `G.IsBipartite` is defined as an abbreviation for `G.Colorable 2`.

* `SimpleGraph.isBipartite_iff_exists_isBipartiteWith` is the proof that `G.IsBipartite` iff
  `G.IsBipartiteWith s t`.

* `SimpleGraph.isBipartiteWith_sum_degrees_eq` is the proof that if `G.IsBipartiteWith s t`, then
  the sum of the degrees of the vertices in `s` is equal to the sum of the degrees of the vertices
  in `t`.

* `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges` is the proof that if
  `G.IsBipartiteWith s t`, then sum of the degrees of the vertices in `s` is equal to the number of
  edges in `G`.

  See `SimpleGraph.sum_degrees_eq_twice_card_edges` for the general version, and
  `SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'` for the version from the "right".

* `SimpleGraph.completeBipartiteGraph_isContained_iff` is the proof that simple graphs contain a
  copy of a `completeBipartiteGraph α β` iff there exists a "left" subset of `card α` vertices and
  a "right" subset of `card β` vertices such that every vertex in the "left" subset is adjacent to
  every vertex in the "right" subset.

* `SimpleGraph.between`; the simple graph `G.between s t` is the subgraph of `G` containing edges
  that connect a vertex in the set `s` to a vertex in the set `t`.

* `SimpleGraph.bipartiteDoubleCover`; the simple graph `G.bipartiteDoubleCover` has two vertices
  `inl v` and `inr v` for each vertex `v` in `G` such that `inl v` (`inr v`) is adjacent to `inr w`
  (`inl w`) iff `v` is adjacent to `w` in `G`.

## Implementation notes

For the formulation of double-counting arguments where a bipartite graph is considered as a
relation `r : α → β → Prop`, see `Mathlib/Combinatorics/Enumerative/DoubleCounting.lean`.

## TODO

* Prove that `G.IsBipartite` iff `G` does not contain an odd cycle.
  I.e., `G.IsBipartite ↔ ∀ n, (cycleGraph (2*n+1)).Free G`.
-/

@[expose] public section


open Finset Fintype

namespace SimpleGraph

variable {V : Type*} {v w : V} {G : SimpleGraph V} {s t : Set V}

section IsBipartiteWith

/--
Definition of `IsBipartiteWith` / `IsBipartiteWith` 的定义

English:
structure IsBipartiteWith
  parameters: (G : SimpleGraph V) (s t : Set V)
  axioms and operations (2):
    - disjoint : Disjoint s t
    - mem_of_adj(⦃v w) : V⦄ : G.Adj v w -> v in s ∧ w in t ∨ v in t ∧ w in s

中文:
结构 是BipartiteWith
  参数: (G : 简单图 V) (s t : 集合 V)
  公理与运算 (2 个):
    - disjoint : Disjoint s t
    - mem_of_adj(⦃v w) : V⦄ : G.伴随 v w -> v in s ∧ w in t ∨ v in t ∧ w in s
-/
structure IsBipartiteWith (G : SimpleGraph V) (s t : Set V) : Prop where
  disjoint : Disjoint s t
  mem_of_adj ⦃v w : V⦄ : G.Adj v w -> v in s ∧ w in t ∨ v in t ∧ w in s

/--
theorem `IsBipartiteWith.symm` / 定理 `IsBipartiteWith.symm`

English:
theorem IsBipartiteWith.symm
  given: (h : G.IsBipartiteWith s t)
  statement: G.IsBipartiteWith t s where
  proof: h.disjoint.symm
  mem_of_adj v w hadj := by
    rw [@and_comm (v in t) (w in s)]; rw [@and_comm (v in s) (w in t)]
    exact h.mem_of_adj hadj.symm

中文:
定理 是BipartiteWith.symm
  条件: (h : G.是BipartiteWith s t)
  结论: G.是BipartiteWith t s where
  证明: h.disjoint.symm
  mem_of_adj v w hadj := by
    rw [@and_comm (v in t) (w in s)]; rw [@and_comm (v in s) (w in t)]
    exact h.mem_of_adj hadj.symm

Depends on / 依赖: disjoint, h.disjoint.symm
-/
theorem IsBipartiteWith.symm (h : G.IsBipartiteWith s t) : G.IsBipartiteWith t s where
  disjoint := h.disjoint.symm
  mem_of_adj v w hadj := by
    rw [@and_comm (v in t) (w in s)]; rw [@and_comm (v in s) (w in t)]
    exact h.mem_of_adj hadj.symm

/--
theorem `isBipartiteWith_comm` / 定理 `isBipartiteWith_comm`

English:
theorem isBipartiteWith_comm
  statement: G.IsBipartiteWith s t ↔ G.IsBipartiteWith t s
  proof: ⟨IsBipartiteWith.symm, IsBipartiteWith.symm⟩

中文:
定理 isBipartiteWith_comm
  结论: G.是BipartiteWith s t ↔ G.是BipartiteWith t s
  证明: ⟨IsBipartiteWith.symm, IsBipartiteWith.symm⟩

Depends on / 依赖: IsBipartiteWith, IsBipartiteWith.symm
-/
theorem isBipartiteWith_comm : G.IsBipartiteWith s t ↔ G.IsBipartiteWith t s :=
  ⟨IsBipartiteWith.symm, IsBipartiteWith.symm⟩

/--
theorem `IsBipartiteWith.mem_of_mem_adj` / 定理 `IsBipartiteWith.mem_of_mem_adj`

English:
theorem IsBipartiteWith.mem_of_mem_adj
  proof: by
  apply h.mem_of_adj at hadj
  have nhv : v ∉ t := Set.disjoint_left.mp h.disjoint hv
  simpa [hv, nhv] using hadj

中文:
定理 是BipartiteWith.mem_of_mem_adj
  证明: by
  apply h.mem_of_adj at hadj
  have nhv : v ∉ t := Set.disjoint_left.mp h.disjoint hv
  simpa [hv, nhv] using hadj

Depends on / 依赖: Set.disjoint_left.mp, disjoint, disjoint_left, h.disjoint, h.mem_of_adj, mem_of_adj
-/
theorem IsBipartiteWith.mem_of_mem_adj
    (h : G.IsBipartiteWith s t) (hv : v in s) (hadj : G.Adj v w) : w in t := by
  apply h.mem_of_adj at hadj
  have nhv : v ∉ t := Set.disjoint_left.mp h.disjoint hv
  simpa [hv, nhv] using hadj

/--
theorem `isBipartiteWith_neighborSet` / 定理 `isBipartiteWith_neighborSet`

English:
theorem isBipartiteWith_neighborSet
  given: (h : G.IsBipartiteWith s t) (hv : v in s)
  proof: by
  ext w
  rw [mem_neighborSet]; rw [Set.mem_ofPred_eq]; rw [iff_and_self]
  exact h.mem_of_mem_adj hv

中文:
定理 isBipartiteWith_neighborSet
  条件: (h : G.是BipartiteWith s t) (hv : v in s)
  证明: by
  ext w
  rw [mem_neighborSet]; rw [Set.mem_ofPred_eq]; rw [iff_and_self]
  exact h.mem_of_mem_adj hv

Depends on / 依赖: Set.mem_ofPred_eq, h.mem_of_mem_adj, iff_and_self, mem_neighborSet, mem_ofPred_eq, mem_of_mem_adj
-/
theorem isBipartiteWith_neighborSet (h : G.IsBipartiteWith s t) (hv : v in s) :
    G.neighborSet v = { w in t | G.Adj v w } := by
  ext w
  rw [mem_neighborSet]; rw [Set.mem_ofPred_eq]; rw [iff_and_self]
  exact h.mem_of_mem_adj hv

/--
theorem `isBipartiteWith_neighborSet_subset` / 定理 `isBipartiteWith_neighborSet_subset`

English:
theorem isBipartiteWith_neighborSet_subset
  given: (h : G.IsBipartiteWith s t) (hv : v in s)
  proof: by
  rw [isBipartiteWith_neighborSet h hv]
  exact Set.sep_subset t (G.Adj v ·)

中文:
定理 isBipartiteWith_neighborSet_subset
  条件: (h : G.是BipartiteWith s t) (hv : v in s)
  证明: by
  rw [isBipartiteWith_neighborSet h hv]
  exact Set.sep_subset t (G.Adj v ·)

Depends on / 依赖: G.Adj, Set.sep_subset, isBipartiteWith_neighborSet, sep_subset
-/
theorem isBipartiteWith_neighborSet_subset (h : G.IsBipartiteWith s t) (hv : v in s) :
    G.neighborSet v subseteq t := by
  rw [isBipartiteWith_neighborSet h hv]
  exact Set.sep_subset t (G.Adj v ·)

/--
theorem `isBipartiteWith_neighborSet_disjoint` / 定理 `isBipartiteWith_neighborSet_disjoint`

English:
theorem isBipartiteWith_neighborSet_disjoint
  given: (h : G.IsBipartiteWith s t) (hv : v in s)
  proof: Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset h hv) h.disjoint.symm

中文:
定理 isBipartiteWith_neighborSet_disjoint
  条件: (h : G.是BipartiteWith s t) (hv : v in s)
  证明: Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset h hv) h.disjoint.symm

Depends on / 依赖: Set.disjoint_of_subset_left, disjoint, disjoint_of_subset_left, h.disjoint.symm, isBipartiteWith_neighborSet_subset
-/
theorem isBipartiteWith_neighborSet_disjoint (h : G.IsBipartiteWith s t) (hv : v in s) :
    Disjoint (G.neighborSet v) s :=
  Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset h hv) h.disjoint.symm

/--
theorem `IsBipartiteWith.mem_of_mem_adj'` / 定理 `IsBipartiteWith.mem_of_mem_adj'`

English:
theorem IsBipartiteWith.mem_of_mem_adj'
  proof: by
  apply h.mem_of_adj at hadj
  have nhw : w ∉ s := Set.disjoint_right.mp h.disjoint hw
  simpa [hw, nhw] using hadj

中文:
定理 是BipartiteWith.mem_of_mem_adj'
  证明: by
  apply h.mem_of_adj at hadj
  have nhw : w ∉ s := Set.disjoint_right.mp h.disjoint hw
  simpa [hw, nhw] using hadj

Depends on / 依赖: Set.disjoint_right.mp, disjoint, disjoint_right, h.disjoint, h.mem_of_adj, mem_of_adj
-/
theorem IsBipartiteWith.mem_of_mem_adj'
    (h : G.IsBipartiteWith s t) (hw : w in t) (hadj : G.Adj v w) : v in s := by
  apply h.mem_of_adj at hadj
  have nhw : w ∉ s := Set.disjoint_right.mp h.disjoint hw
  simpa [hw, nhw] using hadj

/--
theorem `isBipartiteWith_neighborSet'` / 定理 `isBipartiteWith_neighborSet'`

English:
theorem isBipartiteWith_neighborSet'
  given: (h : G.IsBipartiteWith s t) (hw : w in t)
  proof: by
  ext v
  rw [mem_neighborSet]; rw [adj_comm]; rw [Set.mem_ofPred_eq]; rw [iff_and_self]
  exact h.mem_of_mem_adj' hw

中文:
定理 isBipartiteWith_neighborSet'
  条件: (h : G.是BipartiteWith s t) (hw : w in t)
  证明: by
  ext v
  rw [mem_neighborSet]; rw [adj_comm]; rw [Set.mem_ofPred_eq]; rw [iff_and_self]
  exact h.mem_of_mem_adj' hw

Depends on / 依赖: Set.mem_ofPred_eq, adj_comm, h.mem_of_mem_adj, iff_and_self, mem_neighborSet, mem_ofPred_eq, mem_of_mem_adj
-/
theorem isBipartiteWith_neighborSet' (h : G.IsBipartiteWith s t) (hw : w in t) :
    G.neighborSet w = { v in s | G.Adj v w } := by
  ext v
  rw [mem_neighborSet]; rw [adj_comm]; rw [Set.mem_ofPred_eq]; rw [iff_and_self]
  exact h.mem_of_mem_adj' hw

/--
theorem `isBipartiteWith_neighborSet_subset'` / 定理 `isBipartiteWith_neighborSet_subset'`

English:
theorem isBipartiteWith_neighborSet_subset'
  given: (h : G.IsBipartiteWith s t) (hw : w in t)
  proof: by
  rw [isBipartiteWith_neighborSet' h hw]
  exact Set.sep_subset s (G.Adj · w)

中文:
定理 isBipartiteWith_neighborSet_subset'
  条件: (h : G.是BipartiteWith s t) (hw : w in t)
  证明: by
  rw [isBipartiteWith_neighborSet' h hw]
  exact Set.sep_subset s (G.Adj · w)

Depends on / 依赖: G.Adj, Set.sep_subset, isBipartiteWith_neighborSet, sep_subset
-/
theorem isBipartiteWith_neighborSet_subset' (h : G.IsBipartiteWith s t) (hw : w in t) :
    G.neighborSet w subseteq s := by
  rw [isBipartiteWith_neighborSet' h hw]
  exact Set.sep_subset s (G.Adj · w)

/--
theorem `isBipartiteWith_support_subset` / 定理 `isBipartiteWith_support_subset`

English:
theorem isBipartiteWith_support_subset
  given: (h : G.IsBipartiteWith s t)
  statement: G.support subseteq s union t
  proof: by
  intro v ⟨w, hadj⟩
  apply h.mem_of_adj at hadj
  tauto

中文:
定理 isBipartiteWith_support_subset
  条件: (h : G.是BipartiteWith s t)
  结论: G.support subseteq s union t
  证明: by
  intro v ⟨w, hadj⟩
  apply h.mem_of_adj at hadj
  tauto

Depends on / 依赖: h.mem_of_adj, mem_of_adj
-/
theorem isBipartiteWith_support_subset (h : G.IsBipartiteWith s t) : G.support subseteq s union t := by
  intro v ⟨w, hadj⟩
  apply h.mem_of_adj at hadj
  tauto

/--
theorem `isBipartiteWith_neighborSet_disjoint'` / 定理 `isBipartiteWith_neighborSet_disjoint'`

English:
theorem isBipartiteWith_neighborSet_disjoint'
  given: (h : G.IsBipartiteWith s t) (hw : w in t)
  proof: Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset' h hw) h.disjoint

中文:
定理 isBipartiteWith_neighborSet_disjoint'
  条件: (h : G.是BipartiteWith s t) (hw : w in t)
  证明: Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset' h hw) h.disjoint

Depends on / 依赖: Set.disjoint_of_subset_left, disjoint, disjoint_of_subset_left, h.disjoint, isBipartiteWith_neighborSet_subset
-/
theorem isBipartiteWith_neighborSet_disjoint' (h : G.IsBipartiteWith s t) (hw : w in t) :
    Disjoint (G.neighborSet w) t :=
  Set.disjoint_of_subset_left (isBipartiteWith_neighborSet_subset' h hw) h.disjoint

variable {s t : Finset V}

section

variable [Fintype ↑(G.neighborSet v)] [Fintype ↑(G.neighborSet w)]

section decidableRel

variable [DecidableRel G.Adj]

/--
theorem `isBipartiteWith_neighborFinset` / 定理 `isBipartiteWith_neighborFinset`

English:
theorem isBipartiteWith_neighborFinset
  given: (h : G.IsBipartiteWith s t) (hv : v in s)
  proof: by
  ext w
  rw [mem_neighborFinset]; rw [mem_filter]; rw [iff_and_self]
  exact h.mem_of_mem_adj hv

中文:
定理 isBipartiteWith_neighborFinset
  条件: (h : G.是BipartiteWith s t) (hv : v in s)
  证明: by
  ext w
  rw [mem_neighborFinset]; rw [mem_filter]; rw [iff_and_self]
  exact h.mem_of_mem_adj hv

Depends on / 依赖: h.mem_of_mem_adj, iff_and_self, mem_filter, mem_neighborFinset, mem_of_mem_adj
-/
theorem isBipartiteWith_neighborFinset (h : G.IsBipartiteWith s t) (hv : v in s) :
    G.neighborFinset v = { w in t | G.Adj v w } := by
  ext w
  rw [mem_neighborFinset]; rw [mem_filter]; rw [iff_and_self]
  exact h.mem_of_mem_adj hv

/--
theorem `isBipartiteWith_neighborFinset'` / 定理 `isBipartiteWith_neighborFinset'`

English:
theorem isBipartiteWith_neighborFinset'
  given: (h : G.IsBipartiteWith s t) (hw : w in t)
  proof: by
  ext v
  rw [mem_neighborFinset]; rw [adj_comm]; rw [mem_filter]; rw [iff_and_self]
  exact h.mem_of_mem_adj' hw

中文:
定理 isBipartiteWith_neighborFinset'
  条件: (h : G.是BipartiteWith s t) (hw : w in t)
  证明: by
  ext v
  rw [mem_neighborFinset]; rw [adj_comm]; rw [mem_filter]; rw [iff_and_self]
  exact h.mem_of_mem_adj' hw

Depends on / 依赖: adj_comm, h.mem_of_mem_adj, iff_and_self, mem_filter, mem_neighborFinset, mem_of_mem_adj
-/
theorem isBipartiteWith_neighborFinset' (h : G.IsBipartiteWith s t) (hw : w in t) :
    G.neighborFinset w = { v in s | G.Adj v w } := by
  ext v
  rw [mem_neighborFinset]; rw [adj_comm]; rw [mem_filter]; rw [iff_and_self]
  exact h.mem_of_mem_adj' hw

/--
theorem `isBipartiteWith_bipartiteAbove` / 定理 `isBipartiteWith_bipartiteAbove`

English:
theorem isBipartiteWith_bipartiteAbove
  given: (h : G.IsBipartiteWith s t) (hv : v in s)
  proof: by
  rw [isBipartiteWith_neighborFinset h hv]; rw [bipartiteAbove]

中文:
定理 isBipartiteWith_bipartiteAbove
  条件: (h : G.是BipartiteWith s t) (hv : v in s)
  证明: by
  rw [isBipartiteWith_neighborFinset h hv]; rw [bipartiteAbove]

Depends on / 依赖: bipartiteAbove, isBipartiteWith_neighborFinset
-/
theorem isBipartiteWith_bipartiteAbove (h : G.IsBipartiteWith s t) (hv : v in s) :
    G.neighborFinset v = bipartiteAbove G.Adj t v := by
  rw [isBipartiteWith_neighborFinset h hv]; rw [bipartiteAbove]

/--
theorem `isBipartiteWith_bipartiteBelow` / 定理 `isBipartiteWith_bipartiteBelow`

English:
theorem isBipartiteWith_bipartiteBelow
  given: (h : G.IsBipartiteWith s t) (hw : w in t)
  proof: by
  rw [isBipartiteWith_neighborFinset' h hw]; rw [bipartiteBelow]

中文:
定理 isBipartiteWith_bipartiteBelow
  条件: (h : G.是BipartiteWith s t) (hw : w in t)
  证明: by
  rw [isBipartiteWith_neighborFinset' h hw]; rw [bipartiteBelow]

Depends on / 依赖: bipartiteBelow, isBipartiteWith_neighborFinset
-/
theorem isBipartiteWith_bipartiteBelow (h : G.IsBipartiteWith s t) (hw : w in t) :
    G.neighborFinset w = bipartiteBelow G.Adj s w := by
  rw [isBipartiteWith_neighborFinset' h hw]; rw [bipartiteBelow]

end decidableRel

/--
theorem `isBipartiteWith_neighborFinset_subset` / 定理 `isBipartiteWith_neighborFinset_subset`

English:
theorem isBipartiteWith_neighborFinset_subset
  given: (h : G.IsBipartiteWith s t) (hv : v in s)
  proof: by
  classical
  rw [isBipartiteWith_neighborFinset h hv]
  exact filter_subset (G.Adj v ·) t

中文:
定理 isBipartiteWith_neighborFinset_subset
  条件: (h : G.是BipartiteWith s t) (hv : v in s)
  证明: by
  classical
  rw [isBipartiteWith_neighborFinset h hv]
  exact filter_subset (G.Adj v ·) t

Depends on / 依赖: G.Adj, classical, filter_subset, isBipartiteWith_neighborFinset
-/
theorem isBipartiteWith_neighborFinset_subset (h : G.IsBipartiteWith s t) (hv : v in s) :
    G.neighborFinset v subseteq t := by
  classical
  rw [isBipartiteWith_neighborFinset h hv]
  exact filter_subset (G.Adj v ·) t

/--
theorem `isBipartiteWith_neighborFinset_disjoint` / 定理 `isBipartiteWith_neighborFinset_disjoint`

English:
theorem isBipartiteWith_neighborFinset_disjoint
  given: (h : G.IsBipartiteWith s t) (hv : v in s)
  proof: by
  rw [neighborFinset_def]; rw [← disjoint_coe]; rw [Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint h hv

中文:
定理 isBipartiteWith_neighborFinset_disjoint
  条件: (h : G.是BipartiteWith s t) (hv : v in s)
  证明: by
  rw [neighborFinset_def]; rw [← disjoint_coe]; rw [Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint h hv

Depends on / 依赖: Set.coe_toFinset, coe_toFinset, disjoint_coe, isBipartiteWith_neighborSet_disjoint, neighborFinset_def
-/
theorem isBipartiteWith_neighborFinset_disjoint (h : G.IsBipartiteWith s t) (hv : v in s) :
    Disjoint (G.neighborFinset v) s := by
  rw [neighborFinset_def]; rw [← disjoint_coe]; rw [Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint h hv

/--
theorem `isBipartiteWith_degree_le` / 定理 `isBipartiteWith_degree_le`

English:
theorem isBipartiteWith_degree_le
  given: (h : G.IsBipartiteWith s t) (hv : v in s)
  statement: G.degree v <= #t
  proof: by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset h hv)

中文:
定理 isBipartiteWith_degree_le
  条件: (h : G.是BipartiteWith s t) (hv : v in s)
  结论: G.degree v <= #t
  证明: by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset h hv)

Depends on / 依赖: card_le_card, card_neighborFinset_eq_degree, isBipartiteWith_neighborFinset_subset
-/
theorem isBipartiteWith_degree_le (h : G.IsBipartiteWith s t) (hv : v in s) : G.degree v <= #t := by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset h hv)

/--
theorem `isBipartiteWith_neighborFinset_subset'` / 定理 `isBipartiteWith_neighborFinset_subset'`

English:
theorem isBipartiteWith_neighborFinset_subset'
  given: (h : G.IsBipartiteWith s t) (hw : w in t)
  proof: by
  classical
  rw [isBipartiteWith_neighborFinset' h hw]
  exact filter_subset (G.Adj · w) s

中文:
定理 isBipartiteWith_neighborFinset_subset'
  条件: (h : G.是BipartiteWith s t) (hw : w in t)
  证明: by
  classical
  rw [isBipartiteWith_neighborFinset' h hw]
  exact filter_subset (G.Adj · w) s

Depends on / 依赖: G.Adj, classical, filter_subset, isBipartiteWith_neighborFinset
-/
theorem isBipartiteWith_neighborFinset_subset' (h : G.IsBipartiteWith s t) (hw : w in t) :
    G.neighborFinset w subseteq s := by
  classical
  rw [isBipartiteWith_neighborFinset' h hw]
  exact filter_subset (G.Adj · w) s

/--
theorem `isBipartiteWith_neighborFinset_disjoint'` / 定理 `isBipartiteWith_neighborFinset_disjoint'`

English:
theorem isBipartiteWith_neighborFinset_disjoint'
  given: (h : G.IsBipartiteWith s t) (hw : w in t)
  proof: by
  rw [neighborFinset_def]; rw [← disjoint_coe]; rw [Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint' h hw

中文:
定理 isBipartiteWith_neighborFinset_disjoint'
  条件: (h : G.是BipartiteWith s t) (hw : w in t)
  证明: by
  rw [neighborFinset_def]; rw [← disjoint_coe]; rw [Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint' h hw

Depends on / 依赖: Set.coe_toFinset, coe_toFinset, disjoint_coe, isBipartiteWith_neighborSet_disjoint, neighborFinset_def
-/
theorem isBipartiteWith_neighborFinset_disjoint' (h : G.IsBipartiteWith s t) (hw : w in t) :
    Disjoint (G.neighborFinset w) t := by
  rw [neighborFinset_def]; rw [← disjoint_coe]; rw [Set.coe_toFinset]
  exact isBipartiteWith_neighborSet_disjoint' h hw

/--
theorem `isBipartiteWith_degree_le'` / 定理 `isBipartiteWith_degree_le'`

English:
theorem isBipartiteWith_degree_le'
  given: (h : G.IsBipartiteWith s t) (hw : w in t)
  statement: G.degree w <= #s
  proof: by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset' h hw)

中文:
定理 isBipartiteWith_degree_le'
  条件: (h : G.是BipartiteWith s t) (hw : w in t)
  结论: G.degree w <= #s
  证明: by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset' h hw)

Depends on / 依赖: card_le_card, card_neighborFinset_eq_degree, isBipartiteWith_neighborFinset_subset
-/
theorem isBipartiteWith_degree_le' (h : G.IsBipartiteWith s t) (hw : w in t) : G.degree w <= #s := by
  rw [← card_neighborFinset_eq_degree]
  exact card_le_card (isBipartiteWith_neighborFinset_subset' h hw)

end

/--
theorem `isBipartiteWith_sum_degrees_eq` / 定理 `isBipartiteWith_sum_degrees_eq`

English:
theorem isBipartiteWith_sum_degrees_eq
  given: [G.LocallyFinite] (h : G.IsBipartiteWith s t)
  proof: by
  classical
  simp_rw [← sum_attach t, ← sum_attach s, ← card_neighborFinset_eq_degree]
  conv_lhs =>
    rhs; intro v
    rw [isBipartiteWith_bipartiteAbove h v.prop]
  conv_rhs =>
    rhs; intro w
    rw [isBipartiteWith_bipartiteBelow h w.prop]
  simp_rw [sum_attach s fun w => #(bipartiteAbove G.Adj t w),
    sum_attach t fun v => #(bipartiteBelow G.Adj s v)]
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj

中文:
定理 isBipartiteWith_sum_degrees_eq
  条件: [G.局部有限] (h : G.是BipartiteWith s t)
  证明: by
  classical
  simp_rw [← sum_attach t, ← sum_attach s, ← card_neighborFinset_eq_degree]
  conv_lhs =>
    rhs; intro v
    rw [isBipartiteWith_bipartiteAbove h v.prop]
  conv_rhs =>
    rhs; intro w
    rw [isBipartiteWith_bipartiteBelow h w.prop]
  simp_rw [sum_attach s fun w => #(bipartiteAbove G.Adj t w),
    sum_attach t fun v => #(bipartiteBelow G.Adj s v)]
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj

Depends on / 依赖: G.Adj, bipartiteAbove, bipartiteBelow, card_neighborFinset_eq_degree, classical, conv_lhs, conv_rhs, isBipartiteWith_bipartiteAbove, isBipartiteWith_bipartiteBelow, simp_rw, sum_attach, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow, v.prop, w.prop
-/
theorem isBipartiteWith_sum_degrees_eq [G.LocallyFinite] (h : G.IsBipartiteWith s t) :
    ∑ v in s, G.degree v = ∑ w in t, G.degree w := by
  classical
  simp_rw [← sum_attach t, ← sum_attach s, ← card_neighborFinset_eq_degree]
  conv_lhs =>
    rhs; intro v
    rw [isBipartiteWith_bipartiteAbove h v.prop]
  conv_rhs =>
    rhs; intro w
    rw [isBipartiteWith_bipartiteBelow h w.prop]
  simp_rw [sum_attach s fun w => #(bipartiteAbove G.Adj t w),
    sum_attach t fun v => #(bipartiteBelow G.Adj s v)]
  exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj

variable [Fintype V] [DecidableRel G.Adj]

/--
lemma `isBipartiteWith_sum_degrees_eq_twice_card_edges` / 引理 `isBipartiteWith_sum_degrees_eq_twice_card_edges`

English:
lemma isBipartiteWith_sum_degrees_eq_twice_card_edges
  given: [DecidableEq V] (h : G.IsBipartiteWith s t)
  proof: by
  have hsub : G.support subseteq ↑s union ↑t := isBipartiteWith_support_subset h
  rw [← coe_union]; rw [← Set.toFinset_subset] at hsub
  rw [← Finset.sum_subset hsub]; rw [← sum_degrees_support_eq_twice_card_edges]
  intro v _ hv
  rwa [Set.mem_toFinset, ← degree_eq_zero_iff_notMem_support] at hv

中文:
引理 isBipartiteWith_sum_degrees_eq_twice_card_edges
  条件: [DecidableEq V] (h : G.是BipartiteWith s t)
  证明: by
  have hsub : G.support subseteq ↑s union ↑t := isBipartiteWith_support_subset h
  rw [← coe_union]; rw [← Set.toFinset_subset] at hsub
  rw [← Finset.sum_subset hsub]; rw [← sum_degrees_support_eq_twice_card_edges]
  intro v _ hv
  rwa [Set.mem_toFinset, ← degree_eq_zero_iff_notMem_support] at hv

Depends on / 依赖: Finset, Finset.sum_subset, G.support, Set.mem_toFinset, Set.toFinset_subset, coe_union, degree_eq_zero_iff_notMem_support, isBipartiteWith_support_subset, mem_toFinset, subseteq, sum_degrees_support_eq_twice_card_edges, sum_subset, support, toFinset_subset
-/
lemma isBipartiteWith_sum_degrees_eq_twice_card_edges [DecidableEq V] (h : G.IsBipartiteWith s t) :
    ∑ v in s union t, G.degree v = 2 * #G.edgeFinset := by
  have hsub : G.support subseteq ↑s union ↑t := isBipartiteWith_support_subset h
  rw [← coe_union]; rw [← Set.toFinset_subset] at hsub
  rw [← Finset.sum_subset hsub]; rw [← sum_degrees_support_eq_twice_card_edges]
  intro v _ hv
  rwa [Set.mem_toFinset, ← degree_eq_zero_iff_notMem_support] at hv

/--
theorem `isBipartiteWith_sum_degrees_eq_card_edges` / 定理 `isBipartiteWith_sum_degrees_eq_card_edges`

English:
theorem isBipartiteWith_sum_degrees_eq_card_edges
  given: (h : G.IsBipartiteWith s t)
  proof: by
  classical
  rw [← Nat.mul_left_cancel_iff zero_lt_two]; rw [← isBipartiteWith_sum_degrees_eq_twice_card_edges h]; rw [sum_union (disjoint_coe.mp h.disjoint)]; rw [two_mul]; rw [add_right_inj]
  exact isBipartiteWith_sum_degrees_eq h

中文:
定理 isBipartiteWith_sum_degrees_eq_card_edges
  条件: (h : G.是BipartiteWith s t)
  证明: by
  classical
  rw [← Nat.mul_left_cancel_iff zero_lt_two]; rw [← isBipartiteWith_sum_degrees_eq_twice_card_edges h]; rw [sum_union (disjoint_coe.mp h.disjoint)]; rw [two_mul]; rw [add_right_inj]
  exact isBipartiteWith_sum_degrees_eq h

Depends on / 依赖: Nat.mul_left_cancel_iff, add_right_inj, classical, disjoint, disjoint_coe, disjoint_coe.mp, h.disjoint, isBipartiteWith_sum_degrees_eq, isBipartiteWith_sum_degrees_eq_twice_card_edges, mul_left_cancel_iff, sum_union, two_mul, zero_lt_two
-/
theorem isBipartiteWith_sum_degrees_eq_card_edges (h : G.IsBipartiteWith s t) :
    ∑ v in s, G.degree v = #G.edgeFinset := by
  classical
  rw [← Nat.mul_left_cancel_iff zero_lt_two]; rw [← isBipartiteWith_sum_degrees_eq_twice_card_edges h]; rw [sum_union (disjoint_coe.mp h.disjoint)]; rw [two_mul]; rw [add_right_inj]
  exact isBipartiteWith_sum_degrees_eq h

/--
theorem `isBipartiteWith_sum_degrees_eq_card_edges'` / 定理 `isBipartiteWith_sum_degrees_eq_card_edges'`

English:
theorem isBipartiteWith_sum_degrees_eq_card_edges'
  given: (h : G.IsBipartiteWith s t)
  proof: isBipartiteWith_sum_degrees_eq_card_edges h.symm

中文:
定理 isBipartiteWith_sum_degrees_eq_card_edges'
  条件: (h : G.是BipartiteWith s t)
  证明: isBipartiteWith_sum_degrees_eq_card_edges h.symm

Depends on / 依赖: h.symm, isBipartiteWith_sum_degrees_eq_card_edges
-/
theorem isBipartiteWith_sum_degrees_eq_card_edges' (h : G.IsBipartiteWith s t) :
    ∑ v in t, G.degree v = #G.edgeFinset := isBipartiteWith_sum_degrees_eq_card_edges h.symm

end IsBipartiteWith

section IsBipartite

/--
Definition of `IsBipartite` / `IsBipartite` 的定义

English:
abbreviation IsBipartite
  signature: (G : SimpleGraph V)
  body: G.Colorable 2

中文:
缩写 IsBipartite
  签名: (G : 简单图 V)
  定义体: G.Colorable 2

Depends on / 依赖: Colorable, G.Colorable
-/
abbrev IsBipartite (G : SimpleGraph V) : Prop := G.Colorable 2

/--
lemma `IsBipartite.exists_isBipartiteWith` / 引理 `IsBipartite.exists_isBipartiteWith`

English:
lemma IsBipartite.exists_isBipartiteWith
  given: (h : G.IsBipartite)
  statement: exists s t, G.IsBipartiteWith s t
  proof: by
  obtain ⟨c, hc⟩ := h
  refine ⟨{v | c v = 0}, {v | c v = 1}, by aesop (add simp [Set.disjoint_left]), ?_⟩
  rintro v w hvw
  apply hc at hvw
  simp [Set.mem_ofPred_eq] at hvw ⊢
  lia

中文:
引理 IsBipartite.存在_isBipartiteWith
  条件: (h : G.IsBipartite)
  结论: 存在 s t, G.是BipartiteWith s t
  证明: by
  obtain ⟨c, hc⟩ := h
  refine ⟨{v | c v = 0}, {v | c v = 1}, by aesop (add simp [Set.disjoint_left]), ?_⟩
  rintro v w hvw
  apply hc at hvw
  simp [Set.mem_ofPred_eq] at hvw ⊢
  lia

Depends on / 依赖: Set.disjoint_left, Set.mem_ofPred_eq, disjoint_left, mem_ofPred_eq
-/
lemma IsBipartite.exists_isBipartiteWith (h : G.IsBipartite) : exists s t, G.IsBipartiteWith s t := by
  obtain ⟨c, hc⟩ := h
  refine ⟨{v | c v = 0}, {v | c v = 1}, by aesop (add simp [Set.disjoint_left]), ?_⟩
  rintro v w hvw
  apply hc at hvw
  simp [Set.mem_ofPred_eq] at hvw ⊢
  lia

/--
lemma `IsBipartiteWith.isBipartite` / 引理 `IsBipartiteWith.isBipartite`

English:
lemma IsBipartiteWith.isBipartite
  given: {s t : Set V} (h : G.IsBipartiteWith s t)
  statement: G.IsBipartite
  proof: by
  refine ⟨s.indicator 1, fun {v w} hw => ?_⟩
  obtain (⟨hs, ht⟩ | ⟨ht, hs⟩) := h.2 hw <;>
    { replace ht : _ ∉ s := h.1.subset_compl_left ht; simp [hs, ht] }

中文:
引理 是BipartiteWith.isBipartite
  条件: {s t : 集合 V} (h : G.是BipartiteWith s t)
  结论: G.IsBipartite
  证明: by
  refine ⟨s.indicator 1, fun {v w} hw => ?_⟩
  obtain (⟨hs, ht⟩ | ⟨ht, hs⟩) := h.2 hw <;>
    { replace ht : _ ∉ s := h.1.subset_compl_left ht; simp [hs, ht] }

Depends on / 依赖: indicator, replace, s.indicator, subset_compl_left
-/
lemma IsBipartiteWith.isBipartite {s t : Set V} (h : G.IsBipartiteWith s t) : G.IsBipartite := by
  refine ⟨s.indicator 1, fun {v w} hw => ?_⟩
  obtain (⟨hs, ht⟩ | ⟨ht, hs⟩) := h.2 hw <;>
    { replace ht : _ ∉ s := h.1.subset_compl_left ht; simp [hs, ht] }

/--
theorem `isBipartite_iff_exists_isBipartiteWith` / 定理 `isBipartite_iff_exists_isBipartiteWith`

English:
theorem isBipartite_iff_exists_isBipartiteWith
  proof: ⟨IsBipartite.exists_isBipartiteWith, fun ⟨_, _, h⟩ => h.isBipartite⟩

中文:
定理 isBipartite_iff_存在_isBipartiteWith
  证明: ⟨IsBipartite.exists_isBipartiteWith, fun ⟨_, _, h⟩ => h.isBipartite⟩

Depends on / 依赖: IsBipartite, IsBipartite.exists_isBipartiteWith, exists_isBipartiteWith, h.isBipartite, isBipartite
-/
theorem isBipartite_iff_exists_isBipartiteWith :
    G.IsBipartite ↔ exists s t : Set V, G.IsBipartiteWith s t :=
  ⟨IsBipartite.exists_isBipartiteWith, fun ⟨_, _, h⟩ => h.isBipartite⟩

/--
theorem `chromaticNumber_le_two_iff_isBipartite` / 定理 `chromaticNumber_le_two_iff_isBipartite`

English:
theorem chromaticNumber_le_two_iff_isBipartite
  statement: G.chromaticNumber <= 2 ↔ G.IsBipartite
  proof: chromaticNumber_le_iff_colorable

中文:
定理 chromaticNumber_le_two_iff_isBipartite
  结论: G.chromaticNumber <= 2 ↔ G.IsBipartite
  证明: chromaticNumber_le_iff_colorable

Depends on / 依赖: chromaticNumber_le_iff_colorable
-/
theorem chromaticNumber_le_two_iff_isBipartite : G.chromaticNumber <= 2 ↔ G.IsBipartite :=
  chromaticNumber_le_iff_colorable

/--
theorem `chromaticNumber_eq_two_iff` / 定理 `chromaticNumber_eq_two_iff`

English:
theorem chromaticNumber_eq_two_iff
  statement: G.chromaticNumber = 2 ↔ G.IsBipartite ∧ G != ⊥
  proof: ⟨fun h => ⟨chromaticNumber_le_two_iff_isBipartite.mp (by simp [h]),
            two_le_chromaticNumber_iff_ne_bot.mp (by simp [h])⟩,
   fun ⟨h₁, h₂⟩ => ENat.eq_of_forall_natCast_le_iff fun _ =>
⟨fun h => h.trans chromaticNumber_le_two_iff_isBipartite.mpr h₁,
fun h => h.trans two_le_chromaticNumber_iff_ne_bot.mpr h₂⟩⟩

中文:
定理 chromaticNumber_eq_two_iff
  结论: G.chromaticNumber = 2 ↔ G.IsBipartite ∧ G != ⊥
  证明: ⟨fun h => ⟨chromaticNumber_le_two_iff_isBipartite.mp (by simp [h]),
            two_le_chromaticNumber_iff_ne_bot.mp (by simp [h])⟩,
   fun ⟨h₁, h₂⟩ => ENat.eq_of_forall_natCast_le_iff fun _ =>
⟨fun h => h.trans chromaticNumber_le_two_iff_isBipartite.mpr h₁,
fun h => h.trans two_le_chromaticNumber_iff_ne_bot.mpr h₂⟩⟩

Depends on / 依赖: ENat.eq_of_forall_natCast_le_iff, chromaticNumber_le_two_iff_isBipartite, chromaticNumber_le_two_iff_isBipartite.mp, chromaticNumber_le_two_iff_isBipartite.mpr, eq_of_forall_natCast_le_iff, h.trans, two_le_chromaticNumber_iff_ne_bot, two_le_chromaticNumber_iff_ne_bot.mp, two_le_chromaticNumber_iff_ne_bot.mpr
-/
theorem chromaticNumber_eq_two_iff : G.chromaticNumber = 2 ↔ G.IsBipartite ∧ G != ⊥ :=
  ⟨fun h => ⟨chromaticNumber_le_two_iff_isBipartite.mp (by simp [h]),
            two_le_chromaticNumber_iff_ne_bot.mp (by simp [h])⟩,
   fun ⟨h₁, h₂⟩ => ENat.eq_of_forall_natCast_le_iff fun _ =>
⟨fun h => h.trans chromaticNumber_le_two_iff_isBipartite.mpr h₁,
fun h => h.trans two_le_chromaticNumber_iff_ne_bot.mpr h₂⟩⟩

end IsBipartite

section Copy

variable {α β : Type*} [Fintype α] [Fintype β]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `Copy.completeBipartiteGraph` / `Copy.completeBipartiteGraph` 的定义

English:
definition Copy.completeBipartiteGraph
  body: by
  have : Nonempty (α ↪ left) := by
    rw [← card_coe] at card_left
    exact Function.Embedding.nonempty_of_card_le card_left.symm.le
  let fα : α ↪ left := Classical.arbitrary (α ↪ left)
  have : Nonempty (β ↪ right) := by
    rw [← card_coe] at card_right
    exact Function.Embedding.nonempty_of_card_le card_right.symm.le
  let fβ : β ↪ right := Classical.arbitrary (β ↪ right)
  let f : α oplus β ↪ V := by
    refine ⟨Sum.elim (Subtype.val ∘ fα) (Subtype.val ∘ fβ), fun s₁ s₂ => ?_⟩
    match s₁, s₂ with
    | .inl p₁, .inl p₂ => simp
    | .inr p₁, .inl p₂ =>
      simpa using (h (fα p₂).prop (fβ p₁).prop).ne'
    | .inl p₁, .inr p₂ =>
      simpa using (h (fα p₁).prop (fβ p₂).prop).symm.ne'
    | .inr p₁, .inr p₂ => simp
  refine ⟨⟨f.toFun, fun {s₁ s₂} hadj => ?_⟩, f.injective⟩
  rcases hadj with ⟨hs₁, hs₂⟩ | ⟨hs₁, hs₂⟩
  all_goals dsimp [f]
  · rw [← Sum.inl_getLeft s₁ hs₁, ← Sum.inr_getRight s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr]
    exact h (by simp) (by simp)
  · rw [← Sum.inr_getRight s₁ hs₁, ← Sum.inl_getLeft s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr, adj_comm]
    exact h (by simp) (by simp)

中文:
定义 余py.completeBipartiteGraph
  定义体: by
  have : Nonempty (α ↪ left) := by
    rw [← card_coe] at card_left
    exact Function.Embedding.nonempty_of_card_le card_left.symm.le
  let fα : α ↪ left := Classical.arbitrary (α ↪ left)
  have : Nonempty (β ↪ right) := by
    rw [← card_coe] at card_right
    exact Function.Embedding.nonempty_of_card_le card_right.symm.le
  let fβ : β ↪ right := Classical.arbitrary (β ↪ right)
  let f : α oplus β ↪ V := by
    refine ⟨Sum.elim (Subtype.val ∘ fα) (Subtype.val ∘ fβ), fun s₁ s₂ => ?_⟩
    match s₁, s₂ with
    | .inl p₁, .inl p₂ => simp
    | .inr p₁, .inl p₂ =>
      simpa using (h (fα p₂).prop (fβ p₁).prop).ne'
    | .inl p₁, .inr p₂ =>
      simpa using (h (fα p₁).prop (fβ p₂).prop).symm.ne'
    | .inr p₁, .inr p₂ => simp
  refine ⟨⟨f.toFun, fun {s₁ s₂} hadj => ?_⟩, f.injective⟩
  rcases hadj with ⟨hs₁, hs₂⟩ | ⟨hs₁, hs₂⟩
  all_goals dsimp [f]
  · rw [← Sum.inl_getLeft s₁ hs₁, ← Sum.inr_getRight s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr]
    exact h (by simp) (by simp)
  · rw [← Sum.inr_getRight s₁ hs₁, ← Sum.inl_getLeft s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr, adj_comm]
    exact h (by simp) (by simp)

Depends on / 依赖: Classical, Classical.arbitrary, Embedding, Function, Function.Embedding.nonempty_of_card_le, Nonempty, Subtype, Subtype.val, Sum.elim, arbitrary, card_coe, card_left, card_left.symm.le, card_right, card_right.symm.le, nonempty_of_card_le
-/
noncomputable def Copy.completeBipartiteGraph
    (left right : Finset V) (card_left : #left = card α) (card_right : #right = card β)
    (h : G.IsCompleteBetween left right) : Copy (completeBipartiteGraph α β) G := by
  have : Nonempty (α ↪ left) := by
    rw [← card_coe] at card_left
    exact Function.Embedding.nonempty_of_card_le card_left.symm.le
  let fα : α ↪ left := Classical.arbitrary (α ↪ left)
  have : Nonempty (β ↪ right) := by
    rw [← card_coe] at card_right
    exact Function.Embedding.nonempty_of_card_le card_right.symm.le
  let fβ : β ↪ right := Classical.arbitrary (β ↪ right)
  let f : α oplus β ↪ V := by
    refine ⟨Sum.elim (Subtype.val ∘ fα) (Subtype.val ∘ fβ), fun s₁ s₂ => ?_⟩
    match s₁, s₂ with
    | .inl p₁, .inl p₂ => simp
    | .inr p₁, .inl p₂ =>
      simpa using (h (fα p₂).prop (fβ p₁).prop).ne'
    | .inl p₁, .inr p₂ =>
      simpa using (h (fα p₁).prop (fβ p₂).prop).symm.ne'
    | .inr p₁, .inr p₂ => simp
  refine ⟨⟨f.toFun, fun {s₁ s₂} hadj => ?_⟩, f.injective⟩
  rcases hadj with ⟨hs₁, hs₂⟩ | ⟨hs₁, hs₂⟩
  all_goals dsimp [f]
  · rw [← Sum.inl_getLeft s₁ hs₁, ← Sum.inr_getRight s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr]
    exact h (by simp) (by simp)
  · rw [← Sum.inr_getRight s₁ hs₁, ← Sum.inl_getLeft s₂ hs₂,
      Sum.elim_inl, Sum.elim_inr, adj_comm]
    exact h (by simp) (by simp)

/--
theorem `completeBipartiteGraph_isContained_iff` / 定理 `completeBipartiteGraph_isContained_iff`

English:
theorem completeBipartiteGraph_isContained_iff
  proof: by
    refine fun ⟨f⟩ => ⟨univ.map ⟨f ∘ Sum.inl, f.injective.comp Sum.inl_injective⟩,
      univ.map ⟨f ∘ Sum.inr, f.injective.comp Sum.inr_injective⟩, by simp, by simp,
      fun _ hl _ hr => ?_⟩
    rw [mem_coe]; rw [mem_map] at hl hr
    replace ⟨_, _, hl⟩ := hl
    replace ⟨_, _, hr⟩ := hr
    rw [← hl]; rw [← hr]
    exact f.toHom.map_adj (by simp)
  mpr := fun ⟨left, right, card_left, card_right, h⟩ =>
    ⟨.completeBipartiteGraph left right card_left card_right h⟩

中文:
定理 completeBipartiteGraph_isContained_iff
  证明: by
    refine fun ⟨f⟩ => ⟨univ.map ⟨f ∘ Sum.inl, f.injective.comp Sum.inl_injective⟩,
      univ.map ⟨f ∘ Sum.inr, f.injective.comp Sum.inr_injective⟩, by simp, by simp,
      fun _ hl _ hr => ?_⟩
    rw [mem_coe]; rw [mem_map] at hl hr
    replace ⟨_, _, hl⟩ := hl
    replace ⟨_, _, hr⟩ := hr
    rw [← hl]; rw [← hr]
    exact f.toHom.map_adj (by simp)
  mpr := fun ⟨left, right, card_left, card_right, h⟩ =>
    ⟨.completeBipartiteGraph left right card_left card_right h⟩

Depends on / 依赖: Sum.inl, Sum.inl_injective, Sum.inr, Sum.inr_injective, card_left, card_right, completeBipartiteGraph, f.injective.comp, f.toHom.map_adj, injective, inl_injective, inr_injective, map_adj, mem_coe, mem_map, replace, univ.map
-/
theorem completeBipartiteGraph_isContained_iff :
    completeBipartiteGraph α β ⊑ G ↔
      exists (left right : Finset V), #left = card α ∧ #right = card β
        ∧ G.IsCompleteBetween left right where
  mp := by
    refine fun ⟨f⟩ => ⟨univ.map ⟨f ∘ Sum.inl, f.injective.comp Sum.inl_injective⟩,
      univ.map ⟨f ∘ Sum.inr, f.injective.comp Sum.inr_injective⟩, by simp, by simp,
      fun _ hl _ hr => ?_⟩
    rw [mem_coe]; rw [mem_map] at hl hr
    replace ⟨_, _, hl⟩ := hl
    replace ⟨_, _, hr⟩ := hr
    rw [← hl]; rw [← hr]
    exact f.toHom.map_adj (by simp)
  mpr := fun ⟨left, right, card_left, card_right, h⟩ =>
    ⟨.completeBipartiteGraph left right card_left card_right h⟩

end Copy

/--
lemma `IsBipartiteWith.subgraph` / 引理 `IsBipartiteWith.subgraph`

English:
lemma IsBipartiteWith.subgraph
  given: (h : G.IsBipartiteWith s t) (H : Subgraph G)
  proof: ⟨by grind [h.disjoint], fun _ _ hadj' => h.mem_of_adj H.adj_sub hadj'⟩

中文:
引理 是BipartiteWith.subgraph
  条件: (h : G.是BipartiteWith s t) (H : 子图 G)
  证明: ⟨by grind [h.disjoint], fun _ _ hadj' => h.mem_of_adj H.adj_sub hadj'⟩

Depends on / 依赖: H.adj_sub, adj_sub, disjoint, h.disjoint, h.mem_of_adj, mem_of_adj
-/
lemma IsBipartiteWith.subgraph (h : G.IsBipartiteWith s t) (H : Subgraph G) :
    H.coe.IsBipartiteWith {x : H.verts | ↑x in s} {x : H.verts | ↑x in t} :=
⟨by grind [h.disjoint], fun _ _ hadj' => h.mem_of_adj H.adj_sub hadj'⟩

/--
lemma `IsBipartite.subgraph` / 引理 `IsBipartite.subgraph`

English:
lemma IsBipartite.subgraph
  given: (h : G.IsBipartite) (H : Subgraph G)
  statement: H.coe.IsBipartite
  proof: let ⟨_, _, hst⟩ := isBipartite_iff_exists_isBipartiteWith.mp h
  isBipartite_iff_exists_isBipartiteWith.mpr ⟨_, _, IsBipartiteWith.subgraph hst H⟩

中文:
引理 IsBipartite.subgraph
  条件: (h : G.IsBipartite) (H : 子图 G)
  结论: H.coe.IsBipartite
  证明: let ⟨_, _, hst⟩ := isBipartite_iff_exists_isBipartiteWith.mp h
  isBipartite_iff_exists_isBipartiteWith.mpr ⟨_, _, IsBipartiteWith.subgraph hst H⟩

Depends on / 依赖: IsBipartiteWith, IsBipartiteWith.subgraph, isBipartite_iff_exists_isBipartiteWith, isBipartite_iff_exists_isBipartiteWith.mp, isBipartite_iff_exists_isBipartiteWith.mpr, subgraph
-/
lemma IsBipartite.subgraph (h : G.IsBipartite) (H : Subgraph G) : H.coe.IsBipartite :=
  let ⟨_, _, hst⟩ := isBipartite_iff_exists_isBipartiteWith.mp h
  isBipartite_iff_exists_isBipartiteWith.mpr ⟨_, _, IsBipartiteWith.subgraph hst H⟩

section Between

/--
Definition of `between` / `between` 的定义

English:
definition between
  signature: (s t : Set V) (G : SimpleGraph V)
  body: G.Adj v w ∧ (v in s ∧ w in t ∨ v in t ∧ w in s)
  symm.symm v w := by tauto

中文:
定义 between
  签名: (s t : 集合 V) (G : 简单图 V)
  定义体: G.Adj v w ∧ (v in s ∧ w in t ∨ v in t ∧ w in s)
  symm.symm v w := by tauto

Depends on / 依赖: G.Adj
-/
def between (s t : Set V) (G : SimpleGraph V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v in s ∧ w in t ∨ v in t ∧ w in s)
  symm.symm v w := by tauto

/--
lemma `between_adj` / 引理 `between_adj`

English:
lemma between_adj
  statement: (G.between s t).Adj v w ↔ G.Adj v w ∧ (v in s ∧ w in t ∨ v in t ∧ w in s)
  proof: by rfl

中文:
引理 between_adj
  结论: (G.between s t).伴随 v w ↔ G.伴随 v w ∧ (v in s ∧ w in t ∨ v in t ∧ w in s)
  证明: by rfl
-/
lemma between_adj : (G.between s t).Adj v w ↔ G.Adj v w ∧ (v in s ∧ w in t ∨ v in t ∧ w in s) := by rfl

/--
lemma `between_le` / 引理 `between_le`

English:
lemma between_le
  statement: G.between s t <= G
  proof: fun _ _ h => h.1

中文:
引理 between_le
  结论: G.between s t <= G
  证明: fun _ _ h => h.1
-/
lemma between_le : G.between s t <= G := fun _ _ h => h.1

/--
lemma `between_comm` / 引理 `between_comm`

English:
lemma between_comm
  statement: G.between s t = G.between t s
  proof: by simp [between, or_comm]

中文:
引理 between_comm
  结论: G.between s t = G.between t s
  证明: by simp [between, or_comm]

Depends on / 依赖: between, or_comm
-/
lemma between_comm : G.between s t = G.between t s := by simp [between, or_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableRel
  signature: G.Adj] [DecidablePred (· in s)] [DecidablePred (· in t)] :
  body: inferInstanceAs (DecidableRel fun v w => G.Adj v w ∧ (v in s ∧ w in t ∨ v in t ∧ w in s))

中文:
实例 [DecidableRel
  签名: G.伴随] [DecidablePred (· in s)] [DecidablePred (· in t)] :
  定义体: inferInstanceAs (DecidableRel fun v w => G.Adj v w ∧ (v in s ∧ w in t ∨ v in t ∧ w in s))

Depends on / 依赖: DecidableRel, G.Adj
-/
instance [DecidableRel G.Adj] [DecidablePred (· in s)] [DecidablePred (· in t)] :
    DecidableRel (G.between s t).Adj :=
  inferInstanceAs (DecidableRel fun v w => G.Adj v w ∧ (v in s ∧ w in t ∨ v in t ∧ w in s))

/--
theorem `between_isBipartiteWith` / 定理 `between_isBipartiteWith`

English:
theorem between_isBipartiteWith
  given: (h : Disjoint s t)
  statement: (G.between s t).IsBipartiteWith s t where
  proof: h
  mem_of_adj _ _ h := h.2

中文:
定理 between_isBipartiteWith
  条件: (h : Disjoint s t)
  结论: (G.between s t).是BipartiteWith s t where
  证明: h
  mem_of_adj _ _ h := h.2
-/
theorem between_isBipartiteWith (h : Disjoint s t) : (G.between s t).IsBipartiteWith s t where
  disjoint := h
  mem_of_adj _ _ h := h.2

/--
theorem `between_isBipartite` / 定理 `between_isBipartite`

English:
theorem between_isBipartite
  given: (h : Disjoint s t)
  statement: (G.between s t).IsBipartite
  proof: (between_isBipartiteWith h).isBipartite

中文:
定理 between_isBipartite
  条件: (h : Disjoint s t)
  结论: (G.between s t).IsBipartite
  证明: (between_isBipartiteWith h).isBipartite

Depends on / 依赖: between_isBipartiteWith, isBipartite
-/
theorem between_isBipartite (h : Disjoint s t) : (G.between s t).IsBipartite :=
  (between_isBipartiteWith h).isBipartite

/--
lemma `neighborSet_subset_between_union` / 引理 `neighborSet_subset_between_union`

English:
lemma neighborSet_subset_between_union
  given: (hv : v in s)
  proof: by
  intro w hadj
  rw [neighborSet]; rw [Set.mem_union]; rw [Set.mem_ofPred]; rw [between_adj]
  by_cases hw : w in s
  · exact Or.inr hw
  · exact Or.inl ⟨hadj, Or.inl ⟨hv, hw⟩⟩

中文:
引理 neighborSet_subset_between_union
  条件: (hv : v in s)
  证明: by
  intro w hadj
  rw [neighborSet]; rw [Set.mem_union]; rw [Set.mem_ofPred]; rw [between_adj]
  by_cases hw : w in s
  · exact Or.inr hw
  · exact Or.inl ⟨hadj, Or.inl ⟨hv, hw⟩⟩

Depends on / 依赖: Or.inl, Or.inr, Set.mem_ofPred, Set.mem_union, between_adj, mem_ofPred, mem_union, neighborSet
-/
lemma neighborSet_subset_between_union (hv : v in s) :
    G.neighborSet v subseteq (G.between s sᶜ).neighborSet v union s := by
  intro w hadj
  rw [neighborSet]; rw [Set.mem_union]; rw [Set.mem_ofPred]; rw [between_adj]
  by_cases hw : w in s
  · exact Or.inr hw
  · exact Or.inl ⟨hadj, Or.inl ⟨hv, hw⟩⟩

/--
lemma `neighborSet_subset_between_union_compl` / 引理 `neighborSet_subset_between_union_compl`

English:
lemma neighborSet_subset_between_union_compl
  given: (hw : w in sᶜ)
  proof: by
  intro v hadj
  rw [neighborSet]; rw [Set.mem_union]; rw [Set.mem_ofPred]; rw [between_adj]
  by_cases hv : v in s
  · exact Or.inl ⟨hadj, Or.inr ⟨hw, hv⟩⟩
  · exact Or.inr hv

中文:
引理 neighborSet_subset_between_union_compl
  条件: (hw : w in sᶜ)
  证明: by
  intro v hadj
  rw [neighborSet]; rw [Set.mem_union]; rw [Set.mem_ofPred]; rw [between_adj]
  by_cases hv : v in s
  · exact Or.inl ⟨hadj, Or.inr ⟨hw, hv⟩⟩
  · exact Or.inr hv

Depends on / 依赖: Or.inl, Or.inr, Set.mem_ofPred, Set.mem_union, between_adj, mem_ofPred, mem_union, neighborSet
-/
lemma neighborSet_subset_between_union_compl (hw : w in sᶜ) :
    G.neighborSet w subseteq (G.between s sᶜ).neighborSet w union sᶜ := by
  intro v hadj
  rw [neighborSet]; rw [Set.mem_union]; rw [Set.mem_ofPred]; rw [between_adj]
  by_cases hv : v in s
  · exact Or.inl ⟨hadj, Or.inr ⟨hw, hv⟩⟩
  · exact Or.inr hv

variable [DecidableEq V] [Fintype V] {s t : Finset V} [DecidableRel G.Adj]

/--
lemma `neighborFinset_subset_between_union` / 引理 `neighborFinset_subset_between_union`

English:
lemma neighborFinset_subset_between_union
  given: (hv : v in s)
  proof: by
  simpa [neighborFinset_def] using neighborSet_subset_between_union hv

中文:
引理 neighborFinset_subset_between_union
  条件: (hv : v in s)
  证明: by
  simpa [neighborFinset_def] using neighborSet_subset_between_union hv

Depends on / 依赖: neighborFinset_def, neighborSet_subset_between_union
-/
lemma neighborFinset_subset_between_union (hv : v in s) :
    G.neighborFinset v subseteq (G.between s sᶜ).neighborFinset v union s := by
  simpa [neighborFinset_def] using neighborSet_subset_between_union hv

/--
theorem `degree_le_between_add` / 定理 `degree_le_between_add`

English:
theorem degree_le_between_add
  given: (hv : v in s)
  proof: by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint h_bipartite hv)]
  exact card_le_card (neighborFinset_subset_between_union hv)

中文:
定理 degree_le_between_add
  条件: (hv : v in s)
  证明: by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint h_bipartite hv)]
  exact card_le_card (neighborFinset_subset_between_union hv)

Depends on / 依赖: G.between, IsBipartiteWith, between, between_isBipartiteWith, card_le_card, card_neighborFinset_eq_degree, card_union_of_disjoint, disjoint_compl_right, h_bipartite, isBipartiteWith_neighborFinset_disjoint, neighborFinset_subset_between_union, simp_rw
-/
theorem degree_le_between_add (hv : v in s) :
    G.degree v <= (G.between s sᶜ).degree v + s.card := by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint h_bipartite hv)]
  exact card_le_card (neighborFinset_subset_between_union hv)

/--
lemma `neighborFinset_subset_between_union_compl` / 引理 `neighborFinset_subset_between_union_compl`

English:
lemma neighborFinset_subset_between_union_compl
  given: (hw : w in sᶜ)
  proof: by
  simpa [neighborFinset_def] using G.neighborSet_subset_between_union_compl (by simpa using hw)

中文:
引理 neighborFinset_subset_between_union_compl
  条件: (hw : w in sᶜ)
  证明: by
  simpa [neighborFinset_def] using G.neighborSet_subset_between_union_compl (by simpa using hw)

Depends on / 依赖: G.neighborSet_subset_between_union_compl, neighborFinset_def, neighborSet_subset_between_union_compl
-/
lemma neighborFinset_subset_between_union_compl (hw : w in sᶜ) :
    G.neighborFinset w subseteq (G.between s sᶜ).neighborFinset w union sᶜ := by
  simpa [neighborFinset_def] using G.neighborSet_subset_between_union_compl (by simpa using hw)

/--
theorem `degree_le_between_add_compl` / 定理 `degree_le_between_add_compl`

English:
theorem degree_le_between_add_compl
  given: (hw : w in sᶜ)
  proof: by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint' h_bipartite hw)]
  exact card_le_card (neighborFinset_subset_between_union_compl hw)

中文:
定理 degree_le_between_add_compl
  条件: (hw : w in sᶜ)
  证明: by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint' h_bipartite hw)]
  exact card_le_card (neighborFinset_subset_between_union_compl hw)

Depends on / 依赖: G.between, IsBipartiteWith, between, between_isBipartiteWith, card_le_card, card_neighborFinset_eq_degree, card_union_of_disjoint, disjoint_compl_right, h_bipartite, isBipartiteWith_neighborFinset_disjoint, neighborFinset_subset_between_union_compl, simp_rw
-/
theorem degree_le_between_add_compl (hw : w in sᶜ) :
    G.degree w <= (G.between s sᶜ).degree w + sᶜ.card := by
  have h_bipartite : (G.between s sᶜ).IsBipartiteWith s ↑(sᶜ) := by
    simpa using between_isBipartiteWith disjoint_compl_right
  simp_rw [← card_neighborFinset_eq_degree,
    ← card_union_of_disjoint (isBipartiteWith_neighborFinset_disjoint' h_bipartite hw)]
  exact card_le_card (neighborFinset_subset_between_union_compl hw)

end Between

section completeBipartiteGraph

variable {W₁ W₂ : Type*}

/--
theorem `edgeSet_completeBipartiteGraph` / 定理 `edgeSet_completeBipartiteGraph`

English:
theorem edgeSet_completeBipartiteGraph
  proof: by
refine Set.ext Sym2.ind fun u v => ⟨fun h => ?_, fun ⟨⟨a, b⟩, z⟩ => ?_⟩
  · cases u <;> cases v <;> simp_all
  · grind [completeBipartiteGraph_adj, mem_edgeSet]

中文:
定理 edgeSet_completeBipartiteGraph
  证明: by
refine Set.ext Sym2.ind fun u v => ⟨fun h => ?_, fun ⟨⟨a, b⟩, z⟩ => ?_⟩
  · cases u <;> cases v <;> simp_all
  · grind [completeBipartiteGraph_adj, mem_edgeSet]

Depends on / 依赖: Set.ext, Sym2.ind, completeBipartiteGraph_adj, mem_edgeSet
-/
theorem edgeSet_completeBipartiteGraph :
    (completeBipartiteGraph W₁ W₂).edgeSet =
    .range (fun x : W₁ × W₂ => s(.inl x.1, .inr x.2)) := by
refine Set.ext Sym2.ind fun u v => ⟨fun h => ?_, fun ⟨⟨a, b⟩, z⟩ => ?_⟩
  · cases u <;> cases v <;> simp_all
  · grind [completeBipartiteGraph_adj, mem_edgeSet]

/--
theorem `encard_edgeSet_completeBipartiteGraph` / 定理 `encard_edgeSet_completeBipartiteGraph`

English:
theorem encard_edgeSet_completeBipartiteGraph
  proof: by
  rw [edgeSet_completeBipartiteGraph]; rw [← ENat.card_prod]; rw [← Set.encard_univ]; rw [← Set.image_univ]
  exact Function.Injective.encard_image (by grind [Function.Injective]) Set.univ

中文:
定理 encard_edgeSet_completeBipartiteGraph
  证明: by
  rw [edgeSet_completeBipartiteGraph]; rw [← ENat.card_prod]; rw [← Set.encard_univ]; rw [← Set.image_univ]
  exact Function.Injective.encard_image (by grind [Function.Injective]) Set.univ

Depends on / 依赖: ENat.card_prod, Function, Function.Injective, Function.Injective.encard_image, Injective, Set.encard_univ, Set.image_univ, Set.univ, card_prod, edgeSet_completeBipartiteGraph, encard_image, encard_univ, image_univ
-/
theorem encard_edgeSet_completeBipartiteGraph :
    (completeBipartiteGraph W₁ W₂).edgeSet.encard = ENat.card W₁ * ENat.card W₂ := by
  rw [edgeSet_completeBipartiteGraph]; rw [← ENat.card_prod]; rw [← Set.encard_univ]; rw [← Set.image_univ]
  exact Function.Injective.encard_image (by grind [Function.Injective]) Set.univ

/--
Definition of `IsBipartiteWith.edgeSetEmbeddingCompleteBipartiteGraph` / `IsBipartiteWith.edgeSetEmbeddingCompleteBipartiteGraph` 的定义

English:
definition IsBipartiteWith.edgeSetEmbeddingCompleteBipartiteGraph
  signature: [DecidableRel (· in · : V -> Set V -> _)]
  body: fun ⟨e, he⟩ =>
    e.fromRelNdrec he (sym := G.symm) (fun u v h => hG.mem_of_adj h |>.by_cases
      (fun h => ⟨s(.inl ⟨u, h.left⟩, .inr ⟨v, h.right⟩), .inl ⟨rfl, rfl⟩⟩)
      (fun h => ⟨s(.inl ⟨v, h.right⟩, .inr ⟨u, h.left⟩), .inl ⟨rfl, rfl⟩⟩)
    ) <| by grind [Or.by_cases, hG.disjoint]
  inj' := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    change (dite ..) = (dite ..) -> _
    grind

中文:
定义 是BipartiteWith.edgeSetEmbeddingCompleteBipartiteGraph
  签名: [DecidableRel (· in · : V -> 集合 V -> _)]
  定义体: fun ⟨e, he⟩ =>
    e.fromRelNdrec he (sym := G.symm) (fun u v h => hG.mem_of_adj h |>.by_cases
      (fun h => ⟨s(.inl ⟨u, h.left⟩, .inr ⟨v, h.right⟩), .inl ⟨rfl, rfl⟩⟩)
      (fun h => ⟨s(.inl ⟨v, h.right⟩, .inr ⟨u, h.left⟩), .inl ⟨rfl, rfl⟩⟩)
    ) <| by grind [Or.by_cases, hG.disjoint]
  inj' := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    change (dite ..) = (dite ..) -> _
    grind
-/
def IsBipartiteWith.edgeSetEmbeddingCompleteBipartiteGraph [DecidableRel (· in · : V -> Set V -> _)]
    (hG : G.IsBipartiteWith s t) : G.edgeSet ↪ (completeBipartiteGraph s t).edgeSet where
  toFun := fun ⟨e, he⟩ =>
    e.fromRelNdrec he (sym := G.symm) (fun u v h => hG.mem_of_adj h |>.by_cases
      (fun h => ⟨s(.inl ⟨u, h.left⟩, .inr ⟨v, h.right⟩), .inl ⟨rfl, rfl⟩⟩)
      (fun h => ⟨s(.inl ⟨v, h.right⟩, .inr ⟨u, h.left⟩), .inl ⟨rfl, rfl⟩⟩)
    ) <| by grind [Or.by_cases, hG.disjoint]
  inj' := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    change (dite ..) = (dite ..) -> _
    grind

end completeBipartiteGraph

section

/--
theorem `IsBipartiteWith.encard_edgeSet_le` / 定理 `IsBipartiteWith.encard_edgeSet_le`

English:
theorem IsBipartiteWith.encard_edgeSet_le
  given: (hG : G.IsBipartiteWith s t)
  proof: by
  classical
  grw [hG.edgeSetEmbeddingCompleteBipartiteGraph.encard_le]
  simp [encard_edgeSet_completeBipartiteGraph]

中文:
定理 是BipartiteWith.encard_edgeSet_le
  条件: (hG : G.是BipartiteWith s t)
  证明: by
  classical
  grw [hG.edgeSetEmbeddingCompleteBipartiteGraph.encard_le]
  simp [encard_edgeSet_completeBipartiteGraph]

Depends on / 依赖: classical, edgeSetEmbeddingCompleteBipartiteGraph, encard_edgeSet_completeBipartiteGraph, encard_le, hG.edgeSetEmbeddingCompleteBipartiteGraph.encard_le
-/
theorem IsBipartiteWith.encard_edgeSet_le (hG : G.IsBipartiteWith s t) :
    G.edgeSet.encard <= s.encard * t.encard := by
  classical
  grw [hG.edgeSetEmbeddingCompleteBipartiteGraph.encard_le]
  simp [encard_edgeSet_completeBipartiteGraph]

/--
theorem `IsBipartite.four_mul_encard_edgeSet_le` / 定理 `IsBipartite.four_mul_encard_edgeSet_le`

English:
theorem IsBipartite.four_mul_encard_edgeSet_le
  given: (h : G.IsBipartite)
  proof: by
.elim (fun hv => ?_) (fun _ => by simp) refine finite_or_infinite V
  have ⟨s, t, h⟩ := h.exists_isBipartiteWith
  grw [h.encard_edgeSet_le]
  have := Set.encard_union_eq h.disjoint ▸ Set.encard_le_card
  rw [ENat.card_eq_coe_natCard]; rw [← s.toFinite.cast_ncard_eq]; rw [← t.toFinite.cast_ncard_eq] at this ⊢
  norm_cast at this ⊢
  grind [Nat.pow_le_pow_left this 2, four_mul_le_sq_add s.ncard t.ncard]

中文:
定理 IsBipartite.four_mul_encard_edgeSet_le
  条件: (h : G.IsBipartite)
  证明: by
.elim (fun hv => ?_) (fun _ => by simp) refine finite_or_infinite V
  have ⟨s, t, h⟩ := h.exists_isBipartiteWith
  grw [h.encard_edgeSet_le]
  have := Set.encard_union_eq h.disjoint ▸ Set.encard_le_card
  rw [ENat.card_eq_coe_natCard]; rw [← s.toFinite.cast_ncard_eq]; rw [← t.toFinite.cast_ncard_eq] at this ⊢
  norm_cast at this ⊢
  grind [Nat.pow_le_pow_left this 2, four_mul_le_sq_add s.ncard t.ncard]

Depends on / 依赖: ENat.card_eq_coe_natCard, Nat.pow_le_pow_left, Set.encard_le_card, Set.encard_union_eq, card_eq_coe_natCard, cast_ncard_eq, disjoint, encard_edgeSet_le, encard_le_card, encard_union_eq, exists_isBipartiteWith, finite_or_infinite, four_mul_le_sq_add, h.disjoint, h.encard_edgeSet_le, h.exists_isBipartiteWith, pow_le_pow_left, s.ncard, s.toFinite.cast_ncard_eq, t.ncard
-/
theorem IsBipartite.four_mul_encard_edgeSet_le (h : G.IsBipartite) :
    4 * G.edgeSet.encard <= ENat.card V ^ 2 := by
.elim (fun hv => ?_) (fun _ => by simp) refine finite_or_infinite V
  have ⟨s, t, h⟩ := h.exists_isBipartiteWith
  grw [h.encard_edgeSet_le]
  have := Set.encard_union_eq h.disjoint ▸ Set.encard_le_card
  rw [ENat.card_eq_coe_natCard]; rw [← s.toFinite.cast_ncard_eq]; rw [← t.toFinite.cast_ncard_eq] at this ⊢
  norm_cast at this ⊢
  grind [Nat.pow_le_pow_left this 2, four_mul_le_sq_add s.ncard t.ncard]

end

section BipartiteDoubleCover

/--
Definition of `bipartiteDoubleCover` / `bipartiteDoubleCover` 的定义

English:
definition bipartiteDoubleCover
  signature: (G : SimpleGraph V)
  body: by grind [adj_symm]

中文:
定义 bipartiteDoubleCover
  签名: (G : 简单图 V)
  定义体: by grind [adj_symm]
-/
@[simp] def bipartiteDoubleCover (G : SimpleGraph V) : SimpleGraph (V oplus V) where
  Adj
  | .inl v', .inr w' | .inr v', .inl w' => G.Adj v' w'
  | _, _ => False
  symm.symm _ _ := by grind [adj_symm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : DecidableRel G.Adj] : DecidableRel G.bipartiteDoubleCover.Adj

中文:
实例 [h
  签名: : DecidableRel G.伴随] : DecidableRel G.bipartiteDoubleCover.伴随
-/
instance [h : DecidableRel G.Adj] : DecidableRel G.bipartiteDoubleCover.Adj
  | .inl _, .inr _ | .inr _, .inl _ => h _ _
  | .inl _, .inl _ | .inr _, .inr _ => inferInstanceAs (Decidable False)

/--
theorem `bipartiteDoubleCover_le` / 定理 `bipartiteDoubleCover_le`

English:
theorem bipartiteDoubleCover_le
  statement: G.bipartiteDoubleCover <= completeBipartiteGraph V V
  proof: fun v w hadj => match v, w with
  | .inl _, .inr _ | .inr _, .inl _ => by simp
  | .inl _, .inl _ | .inr _, .inr _ => by simp at hadj

中文:
定理 bipartiteDoubleCover_le
  结论: G.bipartiteDoubleCover <= completeBipartiteGraph V V
  证明: fun v w hadj => match v, w with
  | .inl _, .inr _ | .inr _, .inl _ => by simp
  | .inl _, .inl _ | .inr _, .inr _ => by simp at hadj
-/
theorem bipartiteDoubleCover_le : G.bipartiteDoubleCover <= completeBipartiteGraph V V :=
  fun v w hadj => match v, w with
  | .inl _, .inr _ | .inr _, .inl _ => by simp
  | .inl _, .inl _ | .inr _, .inr _ => by simp at hadj

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `card_edgeFinset_bipartiteDoubleCover` / 定理 `card_edgeFinset_bipartiteDoubleCover`

English:
theorem card_edgeFinset_bipartiteDoubleCover
  given: [Fintype V] [DecidableRel G.Adj]
  proof: by
  rw [two_mul_card_edgeFinset]; rw [eq_comm]
  apply card_bij (fun (v, w) _ => s(.inl v, .inr w))
    (fun _ h => by simpa using h) (by grind) (fun e he => ?_)
  induction e with | _ v w
  rw [mem_edgeFinset]; rw [mem_edgeSet] at he
  match v, w with
  | .inl _, .inr _ => simpa using he
  | .inr _, .inl _ => simpa using he.symm
  | .inl _, .inl _ | .inr _, .inr _ => simp at he

中文:
定理 card_edgeFinset_bipartiteDoubleCover
  条件: [有限类型 V] [DecidableRel G.伴随]
  证明: by
  rw [two_mul_card_edgeFinset]; rw [eq_comm]
  apply card_bij (fun (v, w) _ => s(.inl v, .inr w))
    (fun _ h => by simpa using h) (by grind) (fun e he => ?_)
  induction e with | _ v w
  rw [mem_edgeFinset]; rw [mem_edgeSet] at he
  match v, w with
  | .inl _, .inr _ => simpa using he
  | .inr _, .inl _ => simpa using he.symm
  | .inl _, .inl _ | .inr _, .inr _ => simp at he

Depends on / 依赖: card_bij, eq_comm, he.symm, mem_edgeFinset, mem_edgeSet, two_mul_card_edgeFinset
-/
theorem card_edgeFinset_bipartiteDoubleCover [Fintype V] [DecidableRel G.Adj] :
    #G.bipartiteDoubleCover.edgeFinset = 2 * #G.edgeFinset := by
  rw [two_mul_card_edgeFinset]; rw [eq_comm]
  apply card_bij (fun (v, w) _ => s(.inl v, .inr w))
    (fun _ h => by simpa using h) (by grind) (fun e he => ?_)
  induction e with | _ v w
  rw [mem_edgeFinset]; rw [mem_edgeSet] at he
  match v, w with
  | .inl _, .inr _ => simpa using he
  | .inr _, .inl _ => simpa using he.symm
  | .inl _, .inl _ | .inr _, .inr _ => simp at he

/--
theorem `completeBipartiteGraph_isContained_bipartiteDoubleCover` / 定理 `completeBipartiteGraph_isContained_bipartiteDoubleCover`

English:
theorem completeBipartiteGraph_isContained_bipartiteDoubleCover
  proof: by
  have : Fintype α := .ofFinite α
  have : Fintype β := .ofFinite β
  simp_rw [completeBipartiteGraph_isContained_iff]
  refine ⟨fun ⟨left, right, card_left, card_right, h⟩ => ?_,
    fun ⟨left, right, card_left, card_right, h⟩ => ?_⟩
  · simp_rw [← card_left, ← card_right]
obtain ⟨l, hl⟩ : left.Nonempty := card_pos.mp card_pos.trans_le card_left.ge
obtain ⟨r, hr⟩ : right.Nonempty := card_pos.mp card_pos.trans_le card_right.ge
    have hmem_left {l'} (hl' : l' in left) :
        (l.isLeft -> l'.isLeft) ∧ (l.isRight -> l'.isRight) := by
      rcases l with l | l <;> rcases r with r | r <;> rcases l' with l' | l'
      all_goals solve | simp | simpa using h hl hr | simpa using h hl' hr
    have hmem_right {r'} (hr' : r' in right) :
        (r.isLeft -> r'.isLeft) ∧ (r.isRight -> r'.isRight) := by
      rcases l with l | l <;> rcases r with r | r <;> rcases r' with r' | r'
      all_goals solve | simp | simpa using h hl hr | simpa using h hl hr'
    rcases l with l | l <;> rcases r with r | r
    · simpa using h hl hr
    · refine ⟨left.toLeft, right.toRight, ?_, ?_, fun i hi j hj => ?_⟩
      · exact card_bij (fun i _ => .inl i) (fun i hi => by simpa using hi) (fun i hi j hj => by simp)
          (fun i hi => ⟨i.getLeft <| (hmem_left hi).left Sum.isLeft_inl, by simp [hi]⟩)
      · exact card_bij (fun j hj => .inr j) (fun j hj => by simpa using hj) (fun i hi j hj => by simp)
          (fun j hj => ⟨j.getRight <| (hmem_right hj).right Sum.isRight_inr, by simp [hj]⟩)
      · rw [mem_coe, mem_toLeft] at hi
        rw [mem_coe]; rw [mem_toRight] at hj
        simpa using h hi hj
    · refine ⟨left.toRight, right.toLeft, ?_, ?_, fun i hi j hj => ?_⟩
      · exact card_bij (fun i _ => .inr i) (fun i hi => by simpa using hi) (fun i hi j hj => by simp)
          (fun i hi => ⟨i.getRight <| (hmem_left hi).right Sum.isRight_inr, by simp [hi]⟩)
      · exact card_bij (fun j hj => .inl j) (fun j hj => by simpa using hj) (fun i hi j hj => by simp)
          (fun j hj => ⟨j.getLeft <| (hmem_right hj).left Sum.isLeft_inl, by simp [hj]⟩)
      · rw [mem_coe, mem_toRight] at hi
        rw [mem_coe]; rw [mem_toLeft] at hj
        simpa using h hi hj
    · simpa using h hl hr
  · simp_rw [← card_left, ← card_right]
    refine ⟨left.map .inl, right.map .inr, card_map _, card_map _, fun i hi j hj => ?_⟩
    simp_rw [mem_coe, mem_map, Function.Embedding.inl_apply,
      Function.Embedding.inr_apply] at hi hj
    obtain ⟨i', hi', hi⟩ := hi
    obtain ⟨j', hj', hj⟩ := hj
    simpa [← hi, ← hj] using h hi' hj'

中文:
定理 completeBipartiteGraph_isContained_bipartiteDoubleCover
  证明: by
  have : Fintype α := .ofFinite α
  have : Fintype β := .ofFinite β
  simp_rw [completeBipartiteGraph_isContained_iff]
  refine ⟨fun ⟨left, right, card_left, card_right, h⟩ => ?_,
    fun ⟨left, right, card_left, card_right, h⟩ => ?_⟩
  · simp_rw [← card_left, ← card_right]
obtain ⟨l, hl⟩ : left.Nonempty := card_pos.mp card_pos.trans_le card_left.ge
obtain ⟨r, hr⟩ : right.Nonempty := card_pos.mp card_pos.trans_le card_right.ge
    have hmem_left {l'} (hl' : l' in left) :
        (l.isLeft -> l'.isLeft) ∧ (l.isRight -> l'.isRight) := by
      rcases l with l | l <;> rcases r with r | r <;> rcases l' with l' | l'
      all_goals solve | simp | simpa using h hl hr | simpa using h hl' hr
    have hmem_right {r'} (hr' : r' in right) :
        (r.isLeft -> r'.isLeft) ∧ (r.isRight -> r'.isRight) := by
      rcases l with l | l <;> rcases r with r | r <;> rcases r' with r' | r'
      all_goals solve | simp | simpa using h hl hr | simpa using h hl hr'
    rcases l with l | l <;> rcases r with r | r
    · simpa using h hl hr
    · refine ⟨left.toLeft, right.toRight, ?_, ?_, fun i hi j hj => ?_⟩
      · exact card_bij (fun i _ => .inl i) (fun i hi => by simpa using hi) (fun i hi j hj => by simp)
          (fun i hi => ⟨i.getLeft <| (hmem_left hi).left Sum.isLeft_inl, by simp [hi]⟩)
      · exact card_bij (fun j hj => .inr j) (fun j hj => by simpa using hj) (fun i hi j hj => by simp)
          (fun j hj => ⟨j.getRight <| (hmem_right hj).right Sum.isRight_inr, by simp [hj]⟩)
      · rw [mem_coe, mem_toLeft] at hi
        rw [mem_coe]; rw [mem_toRight] at hj
        simpa using h hi hj
    · refine ⟨left.toRight, right.toLeft, ?_, ?_, fun i hi j hj => ?_⟩
      · exact card_bij (fun i _ => .inr i) (fun i hi => by simpa using hi) (fun i hi j hj => by simp)
          (fun i hi => ⟨i.getRight <| (hmem_left hi).right Sum.isRight_inr, by simp [hi]⟩)
      · exact card_bij (fun j hj => .inl j) (fun j hj => by simpa using hj) (fun i hi j hj => by simp)
          (fun j hj => ⟨j.getLeft <| (hmem_right hj).left Sum.isLeft_inl, by simp [hj]⟩)
      · rw [mem_coe, mem_toRight] at hi
        rw [mem_coe]; rw [mem_toLeft] at hj
        simpa using h hi hj
    · simpa using h hl hr
  · simp_rw [← card_left, ← card_right]
    refine ⟨left.map .inl, right.map .inr, card_map _, card_map _, fun i hi j hj => ?_⟩
    simp_rw [mem_coe, mem_map, Function.Embedding.inl_apply,
      Function.Embedding.inr_apply] at hi hj
    obtain ⟨i', hi', hi⟩ := hi
    obtain ⟨j', hj', hj⟩ := hj
    simpa [← hi, ← hj] using h hi' hj'

Depends on / 依赖: Fintype, Nonempty, card_left, card_left.ge, card_pos, card_pos.mp, card_pos.trans_le, card_right, card_right.ge, completeBipartiteGraph_isContained_iff, hmem_left, isLeft, isRight, l.isLeft, l.isRight, left.Nonempty, ofFinite, right.Nonempty, simp_rw, trans_le
-/
theorem completeBipartiteGraph_isContained_bipartiteDoubleCover
    {α β : Type*} [Finite α] [Finite β] [Nonempty α] [Nonempty β] :
    completeBipartiteGraph α β ⊑ G.bipartiteDoubleCover ↔ completeBipartiteGraph α β ⊑ G := by
  have : Fintype α := .ofFinite α
  have : Fintype β := .ofFinite β
  simp_rw [completeBipartiteGraph_isContained_iff]
  refine ⟨fun ⟨left, right, card_left, card_right, h⟩ => ?_,
    fun ⟨left, right, card_left, card_right, h⟩ => ?_⟩
  · simp_rw [← card_left, ← card_right]
obtain ⟨l, hl⟩ : left.Nonempty := card_pos.mp card_pos.trans_le card_left.ge
obtain ⟨r, hr⟩ : right.Nonempty := card_pos.mp card_pos.trans_le card_right.ge
    have hmem_left {l'} (hl' : l' in left) :
        (l.isLeft -> l'.isLeft) ∧ (l.isRight -> l'.isRight) := by
      rcases l with l | l <;> rcases r with r | r <;> rcases l' with l' | l'
      all_goals solve | simp | simpa using h hl hr | simpa using h hl' hr
    have hmem_right {r'} (hr' : r' in right) :
        (r.isLeft -> r'.isLeft) ∧ (r.isRight -> r'.isRight) := by
      rcases l with l | l <;> rcases r with r | r <;> rcases r' with r' | r'
      all_goals solve | simp | simpa using h hl hr | simpa using h hl hr'
    rcases l with l | l <;> rcases r with r | r
    · simpa using h hl hr
    · refine ⟨left.toLeft, right.toRight, ?_, ?_, fun i hi j hj => ?_⟩
      · exact card_bij (fun i _ => .inl i) (fun i hi => by simpa using hi) (fun i hi j hj => by simp)
          (fun i hi => ⟨i.getLeft <| (hmem_left hi).left Sum.isLeft_inl, by simp [hi]⟩)
      · exact card_bij (fun j hj => .inr j) (fun j hj => by simpa using hj) (fun i hi j hj => by simp)
          (fun j hj => ⟨j.getRight <| (hmem_right hj).right Sum.isRight_inr, by simp [hj]⟩)
      · rw [mem_coe, mem_toLeft] at hi
        rw [mem_coe]; rw [mem_toRight] at hj
        simpa using h hi hj
    · refine ⟨left.toRight, right.toLeft, ?_, ?_, fun i hi j hj => ?_⟩
      · exact card_bij (fun i _ => .inr i) (fun i hi => by simpa using hi) (fun i hi j hj => by simp)
          (fun i hi => ⟨i.getRight <| (hmem_left hi).right Sum.isRight_inr, by simp [hi]⟩)
      · exact card_bij (fun j hj => .inl j) (fun j hj => by simpa using hj) (fun i hi j hj => by simp)
          (fun j hj => ⟨j.getLeft <| (hmem_right hj).left Sum.isLeft_inl, by simp [hj]⟩)
      · rw [mem_coe, mem_toRight] at hi
        rw [mem_coe]; rw [mem_toLeft] at hj
        simpa using h hi hj
    · simpa using h hl hr
  · simp_rw [← card_left, ← card_right]
    refine ⟨left.map .inl, right.map .inr, card_map _, card_map _, fun i hi j hj => ?_⟩
    simp_rw [mem_coe, mem_map, Function.Embedding.inl_apply,
      Function.Embedding.inr_apply] at hi hj
    obtain ⟨i', hi', hi⟩ := hi
    obtain ⟨j', hj', hj⟩ := hj
    simpa [← hi, ← hj] using h hi' hj'

/--
theorem `isBipartiteWith_bipartiteDoubleCover` / 定理 `isBipartiteWith_bipartiteDoubleCover`

English:
theorem isBipartiteWith_bipartiteDoubleCover
  proof: by simp [Set.disjoint_iff_forall_ne]
  mem_of_adj := by simp

中文:
定理 isBipartiteWith_bipartiteDoubleCover
  证明: by simp [Set.disjoint_iff_forall_ne]
  mem_of_adj := by simp

Depends on / 依赖: Set.disjoint_iff_forall_ne, disjoint_iff_forall_ne, mem_of_adj
-/
theorem isBipartiteWith_bipartiteDoubleCover :
    G.bipartiteDoubleCover.IsBipartiteWith {v | v.isLeft} {w | w.isRight} where
  disjoint := by simp [Set.disjoint_iff_forall_ne]
  mem_of_adj := by simp

/--
theorem `isBipartite_bipartiteDoubleCover` / 定理 `isBipartite_bipartiteDoubleCover`

English:
theorem isBipartite_bipartiteDoubleCover
  statement: G.bipartiteDoubleCover.IsBipartite
  proof: isBipartiteWith_bipartiteDoubleCover.isBipartite

中文:
定理 isBipartite_bipartiteDoubleCover
  结论: G.bipartiteDoubleCover.IsBipartite
  证明: isBipartiteWith_bipartiteDoubleCover.isBipartite

Depends on / 依赖: isBipartite, isBipartiteWith_bipartiteDoubleCover, isBipartiteWith_bipartiteDoubleCover.isBipartite
-/
theorem isBipartite_bipartiteDoubleCover : G.bipartiteDoubleCover.IsBipartite :=
  isBipartiteWith_bipartiteDoubleCover.isBipartite

end BipartiteDoubleCover

end SimpleGraph
