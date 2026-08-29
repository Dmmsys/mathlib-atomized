/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Order.Partition.Equipartition

/-!
# Turán's theorem

In this file we prove Turán's theorem, the first important result of extremal graph theory,
which states that the `r + 1`-cliquefree graph on `n` vertices with the most edges is the complete
`r`-partite graph with part sizes as equal as possible (`turanGraph n r`).

The forward direction of the proof performs "Zykov symmetrisation", which first shows
constructively that non-adjacency is an equivalence relation in a maximal graph, so it must be
complete multipartite with the parts being the equivalence classes. Then basic manipulations
show that the graph is isomorphic to the Turán graph for the given parameters.

For the reverse direction we first show that a Turán-maximal graph exists, then transfer
the property through `turanGraph n r` using the isomorphism provided by the forward direction.

## Main declarations

* `SimpleGraph.IsTuranMaximal`: `G.IsTuranMaximal r` means that `G` has the most number of edges for
  its number of vertices while still being `r + 1`-cliquefree.
* `SimpleGraph.turanGraph n r`: The canonical `r + 1`-cliquefree Turán graph on `n` vertices.
* `SimpleGraph.IsTuranMaximal.finpartition`: The result of Zykov symmetrisation, a finpartition of
  the vertices such that two vertices are in the same part iff they are non-adjacent.
* `SimpleGraph.IsTuranMaximal.nonempty_iso_turanGraph`: The forward direction, an isomorphism
  between `G` satisfying `G.IsTuranMaximal r` and `turanGraph n r`.
* `isTuranMaximal_of_iso`: the reverse direction, `G.IsTuranMaximal r` given the isomorphism.
* `isTuranMaximal_iff_nonempty_iso_turanGraph`: Turán's theorem in full.

## References

* https://en.wikipedia.org/wiki/Turán%27s_theorem
-/

@[expose] public section

open Finset Fintype

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {n r : Nat}

variable (G) in
/--
Definition of `IsTuranMaximal` / `IsTuranMaximal` 的定义

English:
definition IsTuranMaximal
  signature: (r : Nat)
  body: G.IsExtremal (CliqueFree · (r + 1))

中文:
定义 IsTuranMaximal
  签名: (r : 自然数)
  定义体: G.IsExtremal (CliqueFree · (r + 1))

Depends on / 依赖: CliqueFree, G.IsExtremal, IsExtremal
-/
def IsTuranMaximal (r : Nat) : Prop := G.IsExtremal (CliqueFree · (r + 1))

section Defs

variable {H : SimpleGraph V}

/--
Definition of `turanGraph` / `turanGraph` 的定义

English:
definition turanGraph
  signature: (n r : Nat)
  body: v % r != w % r

中文:
定义 turanGraph
  签名: (n r : 自然数)
  定义体: v % r != w % r
-/
def turanGraph (n r : Nat) : SimpleGraph (Fin n) where Adj v w := v % r != w % r

/--
lemma `turanGraph_adj` / 引理 `turanGraph_adj`

English:
lemma turanGraph_adj
  given: {v w}
  statement: (turanGraph n r).Adj v w ↔ v % r != w % r
  proof: .rfl

中文:
引理 turanGraph_adj
  条件: {v w}
  结论: (turanGraph n r).Adj v w ↔ v % r != w % r
  证明: .rfl
-/
lemma turanGraph_adj {v w} : (turanGraph n r).Adj v w ↔ v % r != w % r :=
  .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableRel (turanGraph n r).Adj
  body: inferInstanceAs (DecidableRel fun v w : Fin n => v % r != w % r)

@[simp]

中文:
实例 :
  签名: DecidableRel (turanGraph n r).Adj
  定义体: inferInstanceAs (DecidableRel fun v w : Fin n => v % r != w % r)

@[simp]

Depends on / 依赖: DecidableRel
-/
instance : DecidableRel (turanGraph n r).Adj :=
  inferInstanceAs (DecidableRel fun v w : Fin n => v % r != w % r)

@[simp]
/--
lemma `turanGraph_zero` / 引理 `turanGraph_zero`

English:
lemma turanGraph_zero
  statement: turanGraph n 0 = ⊤
  proof: by simp [turanGraph, Fin.val_inj, Top.top]

@[simp]

中文:
引理 turanGraph_zero
  结论: turanGraph n 0 = ⊤
  证明: by simp [turanGraph, Fin.val_inj, Top.top]

@[simp]

Depends on / 依赖: Fin.val_inj, Top.top, turanGraph, val_inj
-/
lemma turanGraph_zero : turanGraph n 0 = ⊤ := by simp [turanGraph, Fin.val_inj, Top.top]

@[simp]
/--
theorem `turanGraph_eq_top` / 定理 `turanGraph_eq_top`

English:
theorem turanGraph_eq_top
  statement: turanGraph n r = ⊤ ↔ r = 0 ∨ n <= r
  proof: by
  simp_rw [SimpleGraph.ext_iff, funext_iff, turanGraph, top_adj, eq_iff_iff, not_iff_not]
  refine ⟨fun h => ?_, ?_⟩
  · contrapose! h
    use ⟨0, (Nat.pos_of_ne_zero h.1).trans h.2⟩, ⟨r, h.2⟩
    simp [h.1.symm]
  · rintro (rfl | h) a b
    · simp [Fin.val_inj]
    · rw [Nat.mod_eq_of_lt (a.2.tr

中文:
定理 turanGraph_eq_top
  结论: turanGraph n r = ⊤ ↔ r = 0 ∨ n <= r
  证明: by
  simp_rw [SimpleGraph.ext_iff, funext_iff, turanGraph, top_adj, eq_iff_iff, not_iff_not]
  refine ⟨fun h => ?_, ?_⟩
  · contrapose! h
    use ⟨0, (Nat.pos_of_ne_zero h.1).trans h.2⟩, ⟨r, h.2⟩
    simp [h.1.symm]
  · rintro (rfl | h) a b
    · simp [Fin.val_inj]
    · rw [Nat.mod_eq_of_lt (a.2.tr

Depends on / 依赖: Fin.val_inj, Nat.mod_eq_of_lt, Nat.pos_of_ne_zero, SimpleGraph, SimpleGraph.ext_iff, contrapose, eq_iff_iff, ext_iff, funext_iff, mod_eq_of_lt, not_iff_not, pos_of_ne_zero, simp_rw, top_adj, trans_le, turanGraph, val_inj
-/
theorem turanGraph_eq_top : turanGraph n r = ⊤ ↔ r = 0 ∨ n <= r := by
  simp_rw [SimpleGraph.ext_iff, funext_iff, turanGraph, top_adj, eq_iff_iff, not_iff_not]
  refine ⟨fun h => ?_, ?_⟩
  · contrapose! h
    use ⟨0, (Nat.pos_of_ne_zero h.1).trans h.2⟩, ⟨r, h.2⟩
    simp [h.1.symm]
  · rintro (rfl | h) a b
    · simp [Fin.val_inj]
    · rw [Nat.mod_eq_of_lt (a.2.trans_le h), Nat.mod_eq_of_lt (b.2.trans_le h), Fin.val_inj]

/--
theorem `turanGraph_cliqueFree` / 定理 `turanGraph_cliqueFree`

English:
theorem turanGraph_cliqueFree
  given: (hr : 0 < r)
  statement: (turanGraph n r).CliqueFree (r + 1)
  proof: by
  rw [cliqueFree_iff]
  by_contra! ⟨f⟩
  obtain ⟨x, y, d, c⟩ := exists_ne_map_eq_of_card_lt (fun x =>
    (⟨(f x).1 % r, Nat.mod_lt _ hr⟩ : Fin r)) (by simp)
  rw [Fin.mk.injEq] at c
exact absurd c f.toHom.map_adj d

中文:
定理 turanGraph_cliqueFree
  条件: (hr : 0 < r)
  结论: (turanGraph n r).CliqueFree (r + 1)
  证明: by
  rw [cliqueFree_iff]
  by_contra! ⟨f⟩
  obtain ⟨x, y, d, c⟩ := exists_ne_map_eq_of_card_lt (fun x =>
    (⟨(f x).1 % r, Nat.mod_lt _ hr⟩ : Fin r)) (by simp)
  rw [Fin.mk.injEq] at c
exact absurd c f.toHom.map_adj d

Depends on / 依赖: Fin.mk.injEq, Nat.mod_lt, absurd, cliqueFree_iff, exists_ne_map_eq_of_card_lt, f.toHom.map_adj, map_adj, mod_lt
-/
theorem turanGraph_cliqueFree (hr : 0 < r) : (turanGraph n r).CliqueFree (r + 1) := by
  rw [cliqueFree_iff]
  by_contra! ⟨f⟩
  obtain ⟨x, y, d, c⟩ := exists_ne_map_eq_of_card_lt (fun x =>
    (⟨(f x).1 % r, Nat.mod_lt _ hr⟩ : Fin r)) (by simp)
  rw [Fin.mk.injEq] at c
exact absurd c f.toHom.map_adj d

/--
theorem `not_cliqueFree_of_isTuranMaximal` / 定理 `not_cliqueFree_of_isTuranMaximal`

English:
theorem not_cliqueFree_of_isTuranMaximal
  given: (hn : r <= card V) (hG : G.IsTuranMaximal r)
  proof: by
  rintro h
  obtain ⟨K, _, rfl⟩ := exists_subset_card_eq hn
  obtain ⟨a, -, b, -, hab, hGab⟩ : exists a in K, exists b in K, a != b ∧ ¬ G.Adj a b := by
    simpa only [isNClique_iff, IsClique, Set.Pairwise, mem_coe, ne_eq, and_true, not_forall,
      exists_prop, exists_and_right] using h K
exact

中文:
定理 not_cliqueFree_of_isTuranMaximal
  条件: (hn : r <= card V) (hG : G.IsTuranMaximal r)
  证明: by
  rintro h
  obtain ⟨K, _, rfl⟩ := exists_subset_card_eq hn
  obtain ⟨a, -, b, -, hab, hGab⟩ : exists a in K, exists b in K, a != b ∧ ¬ G.Adj a b := by
    simpa only [isNClique_iff, IsClique, Set.Pairwise, mem_coe, ne_eq, and_true, not_forall,
      exists_prop, exists_and_right] using h K
exact

Depends on / 依赖: G.Adj, IsClique, Or.inl, Pairwise, Set.Pairwise, and_true, edge_adj, exists_and_right, exists_prop, exists_subset_card_eq, h.sup_edge, hG.le_iff_eq, isNClique_iff, le_iff_eq, le_sup_left, le_sup_right, le_sup_right.trans_eq, mem_coe, ne_eq, not_forall
-/
theorem not_cliqueFree_of_isTuranMaximal (hn : r <= card V) (hG : G.IsTuranMaximal r) :
    ¬G.CliqueFree r := by
  rintro h
  obtain ⟨K, _, rfl⟩ := exists_subset_card_eq hn
  obtain ⟨a, -, b, -, hab, hGab⟩ : exists a in K, exists b in K, a != b ∧ ¬ G.Adj a b := by
    simpa only [isNClique_iff, IsClique, Set.Pairwise, mem_coe, ne_eq, and_true, not_forall,
      exists_prop, exists_and_right] using h K
exact hGab le_sup_right.trans_eq ((hG.le_iff_eq <| h.sup_edge _ _).1 le_sup_left).symm
    (edge_adj ..).2 ⟨Or.inl ⟨rfl, rfl⟩, hab⟩

/--
lemma `exists_isTuranMaximal` / 引理 `exists_isTuranMaximal`

English:
lemma exists_isTuranMaximal
  given: (hr : 0 < r)
  proof: by
  simpa [IsTuranMaximal, exists_isExtremal_iff_exists] using ⟨⊥, cliqueFree_bot (by lia)⟩

中文:
引理 exists_isTuranMaximal
  条件: (hr : 0 < r)
  证明: by
  simpa [IsTuranMaximal, exists_isExtremal_iff_exists] using ⟨⊥, cliqueFree_bot (by lia)⟩

Depends on / 依赖: IsTuranMaximal, cliqueFree_bot, exists_isExtremal_iff_exists
-/
lemma exists_isTuranMaximal (hr : 0 < r) :
    exists H : SimpleGraph V, exists _ : DecidableRel H.Adj, H.IsTuranMaximal r := by
  simpa [IsTuranMaximal, exists_isExtremal_iff_exists] using ⟨⊥, cliqueFree_bot (by lia)⟩

end Defs

namespace IsTuranMaximal

variable {s t u : V}

/--
lemma `degree_eq_of_not_adj` / 引理 `degree_eq_of_not_adj`

English:
lemma degree_eq_of_not_adj
  given: (h : G.IsTuranMaximal r) (hn : ¬G.Adj s t)
  proof: by
  rw [IsTuranMaximal]; rw [IsExtremal] at h; contrapose! h; intro cf
  wlog hd : G.degree t < G.degree s generalizing G t s
  · replace hd : G.degree s < G.degree t := lt_of_le_of_ne (le_of_not_gt hd) h
    exact this (by rwa [adj_comm] at hn) hd.ne' cf hd
  classical
  use G.replaceVertex s t, i

中文:
引理 degree_eq_of_not_adj
  条件: (h : G.IsTuranMaximal r) (hn : ¬G.Adj s t)
  证明: by
  rw [IsTuranMaximal]; rw [IsExtremal] at h; contrapose! h; intro cf
  wlog hd : G.degree t < G.degree s generalizing G t s
  · replace hd : G.degree s < G.degree t := lt_of_le_of_ne (le_of_not_gt hd) h
    exact this (by rwa [adj_comm] at hn) hd.ne' cf hd
  classical
  use G.replaceVertex s t, i

Depends on / 依赖: G.card_edgeFinset_replaceVertex_of_not_adj, G.degree, G.replaceVertex, IsExtremal, IsTuranMaximal, adj_comm, card_edgeFinset_replaceVertex_of_not_adj, cf.replaceVertex, classical, contrapose, degree, generalizing, hd.ne, le_of_not_gt, lt_of_le_of_ne, replace, replaceVertex
-/
lemma degree_eq_of_not_adj (h : G.IsTuranMaximal r) (hn : ¬G.Adj s t) :
    G.degree s = G.degree t := by
  rw [IsTuranMaximal]; rw [IsExtremal] at h; contrapose! h; intro cf
  wlog hd : G.degree t < G.degree s generalizing G t s
  · replace hd : G.degree s < G.degree t := lt_of_le_of_ne (le_of_not_gt hd) h
    exact this (by rwa [adj_comm] at hn) hd.ne' cf hd
  classical
  use G.replaceVertex s t, inferInstance, cf.replaceVertex s t
  have := G.card_edgeFinset_replaceVertex_of_not_adj hn
  lia

/--
lemma `not_adj_trans` / 引理 `not_adj_trans`

English:
lemma not_adj_trans
  given: (h : G.IsTuranMaximal r) (hts : ¬G.Adj t s) (hsu : ¬G.Adj s u)
  proof: by
  have hst : ¬G.Adj s t := fun a => hts a.symm
  have dst := h.degree_eq_of_not_adj hst
  have dsu := h.degree_eq_of_not_adj hsu
  rw [IsTuranMaximal]; rw [IsExtremal] at h; contrapose! h; intro cf
  classical
  use (G.replaceVertex s t).replaceVertex s u, inferInstance,
    (cf.replaceVertex s t

中文:
引理 not_adj_trans
  条件: (h : G.IsTuranMaximal r) (hts : ¬G.Adj t s) (hsu : ¬G.Adj s u)
  证明: by
  have hst : ¬G.Adj s t := fun a => hts a.symm
  have dst := h.degree_eq_of_not_adj hst
  have dsu := h.degree_eq_of_not_adj hsu
  rw [IsTuranMaximal]; rw [IsExtremal] at h; contrapose! h; intro cf
  classical
  use (G.replaceVertex s t).replaceVertex s u, inferInstance,
    (cf.replaceVertex s t

Depends on / 依赖: G.Adj, G.adj_replaceVertex_iff_of_ne, G.ne_of_adj, G.replaceVertex, IsExtremal, IsTuranMaximal, a.symm, adj_replaceVertex_iff_of_ne, card_edgeFinset_replaceVertex_of_not_adj, cf.replaceVertex, classical, contrapose, degree_eq_of_not_adj, h.degree_eq_of_not_adj, ne_of_adj, not.mpr, ntu.symm, replaceVertex
-/
lemma not_adj_trans (h : G.IsTuranMaximal r) (hts : ¬G.Adj t s) (hsu : ¬G.Adj s u) :
    ¬G.Adj t u := by
  have hst : ¬G.Adj s t := fun a => hts a.symm
  have dst := h.degree_eq_of_not_adj hst
  have dsu := h.degree_eq_of_not_adj hsu
  rw [IsTuranMaximal]; rw [IsExtremal] at h; contrapose! h; intro cf
  classical
  use (G.replaceVertex s t).replaceVertex s u, inferInstance,
    (cf.replaceVertex s t).replaceVertex s u
  have nst : s != t := fun a => hsu (a ▸ h)
  have ntu : t != u := G.ne_of_adj h
  have := (G.adj_replaceVertex_iff_of_ne s nst ntu.symm).not.mpr hsu
  rw [card_edgeFinset_replaceVertex_of_not_adj _ this]; rw [card_edgeFinset_replaceVertex_of_not_adj _ hst]; rw [dst]; rw [Nat.add_sub_cancel]
  have l1 : (G.replaceVertex s t).degree s = G.degree s := by
    unfold degree; congr 1; ext v
    simp_rw [mem_neighborFinset]
    by_cases eq : v = t
    · simpa only [eq, not_adj_replaceVertex_same, false_iff]
    · rw [G.adj_replaceVertex_iff_of_ne s nst eq]
  have l2 : (G.replaceVertex s t).degree u = G.degree u - 1 := by
    rw [degree]; rw [degree]; rw [← card_singleton t]; rw [← card_sdiff_of_subset (by simp [h.symm])]
    congr 1; ext v
    simp_rw [mem_neighborFinset, mem_sdiff, mem_singleton, replaceVertex]
    split_ifs <;> simp_all [adj_comm]
  have l3 : 0 < G.degree u := by rw [G.degree_pos_iff_exists_adj u]; use t, h.symm
  lia

variable (h : G.IsTuranMaximal r)
include h

/--
theorem `equivalence_not_adj` / 定理 `equivalence_not_adj`

English:
theorem equivalence_not_adj
  statement: Equivalence (¬G.Adj · ·) where
  proof: by simp
  symm := by simp [adj_comm]
  trans := h.not_adj_trans

中文:
定理 equivalence_not_adj
  结论: Equivalence (¬G.Adj · ·) where
  证明: by simp
  symm := by simp [adj_comm]
  trans := h.not_adj_trans

Depends on / 依赖: adj_comm, h.not_adj_trans, not_adj_trans
-/
theorem equivalence_not_adj : Equivalence (¬G.Adj · ·) where
  refl := by simp
  symm := by simp [adj_comm]
  trans := h.not_adj_trans

/-- The non-adjacency setoid over the vertices of a Turán-maximal graph
induced by `equivalence_not_adj`. -/
@[instance_reducible]
/--
Definition of `setoid` / `setoid` 的定义

English:
definition setoid
  signature: : Setoid V
  body: ⟨_, h.equivalence_not_adj⟩

中文:
定义 setoid
  签名: : Setoid V
  定义体: ⟨_, h.equivalence_not_adj⟩

Depends on / 依赖: equivalence_not_adj, h.equivalence_not_adj
-/
def setoid : Setoid V := ⟨_, h.equivalence_not_adj⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableRel h.setoid.r
  body: inferInstanceAs DecidableRel (¬G.Adj · ·)

中文:
实例 :
  签名: DecidableRel h.setoid.r
  定义体: inferInstanceAs DecidableRel (¬G.Adj · ·)

Depends on / 依赖: DecidableRel, G.Adj
-/
instance : DecidableRel h.setoid.r :=
inferInstanceAs DecidableRel (¬G.Adj · ·)

/--
Definition of `finpartition` / `finpartition` 的定义

English:
definition finpartition
  signature: [DecidableEq V]
  body: Finpartition.ofSetoid h.setoid

中文:
定义 finpartition
  签名: [DecidableEq V]
  定义体: Finpartition.ofSetoid h.setoid

Depends on / 依赖: Finpartition, Finpartition.ofSetoid, h.setoid, ofSetoid, setoid
-/
def finpartition [DecidableEq V] : Finpartition (univ : Finset V) := Finpartition.ofSetoid h.setoid

/--
lemma `not_adj_iff_part_eq` / 引理 `not_adj_iff_part_eq`

English:
lemma not_adj_iff_part_eq
  given: [DecidableEq V]
  proof: by
  change h.setoid.r s t ↔ _
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  let fp := h.finpartition
  change t in fp.part s ↔ fp.part s = fp.part t
  rw [fp.mem_part_iff_part_eq_part (mem_univ t) (mem_univ s)]; rw [eq_comm]

中文:
引理 not_adj_iff_part_eq
  条件: [DecidableEq V]
  证明: by
  change h.setoid.r s t ↔ _
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  let fp := h.finpartition
  change t in fp.part s ↔ fp.part s = fp.part t
  rw [fp.mem_part_iff_part_eq_part (mem_univ t) (mem_univ s)]; rw [eq_comm]

Depends on / 依赖: Finpartition, Finpartition.mem_part_ofSetoid_iff_rel, eq_comm, finpartition, fp.mem_part_iff_part_eq_part, fp.part, h.finpartition, h.setoid.r, mem_part_iff_part_eq_part, mem_part_ofSetoid_iff_rel, mem_univ, setoid
-/
lemma not_adj_iff_part_eq [DecidableEq V] :
    ¬G.Adj s t ↔ h.finpartition.part s = h.finpartition.part t := by
  change h.setoid.r s t ↔ _
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  let fp := h.finpartition
  change t in fp.part s ↔ fp.part s = fp.part t
  rw [fp.mem_part_iff_part_eq_part (mem_univ t) (mem_univ s)]; rw [eq_comm]

/--
lemma `degree_eq_card_sub_part_card` / 引理 `degree_eq_card_sub_part_card`

English:
lemma degree_eq_card_sub_part_card
  given: [DecidableEq V]
  proof: calc
    _ = #{t | G.Adj s t} := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = card V - #{t | ¬G.Adj s t} :=
      eq_tsub_of_add_eq (card_filter_add_card_filter_not _)
    _ = _ := by
      congr; ext; rw [mem_filter]
      convert! Finpartition.mem_part_ofSetoid_iff_rel.s

中文:
引理 degree_eq_card_sub_part_card
  条件: [DecidableEq V]
  证明: calc
    _ = #{t | G.Adj s t} := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = card V - #{t | ¬G.Adj s t} :=
      eq_tsub_of_add_eq (card_filter_add_card_filter_not _)
    _ = _ := by
      congr; ext; rw [mem_filter]
      convert! Finpartition.mem_part_ofSetoid_iff_rel.s

Depends on / 依赖: Finpartition, Finpartition.mem_part_ofSetoid_iff_rel.symm, G.Adj, card_filter_add_card_filter_not, card_neighborFinset_eq_degree, convert, eq_tsub_of_add_eq, instances, mem_filter, mem_part_ofSetoid_iff_rel, neighborFinset, setoid
-/
lemma degree_eq_card_sub_part_card [DecidableEq V] :
    G.degree s = card V - #(h.finpartition.part s) :=
  calc
    _ = #{t | G.Adj s t} := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = card V - #{t | ¬G.Adj s t} :=
      eq_tsub_of_add_eq (card_filter_add_card_filter_not _)
    _ = _ := by
      congr; ext; rw [mem_filter]
      convert! Finpartition.mem_part_ofSetoid_iff_rel.symm
      simp +instances [setoid]

/--
theorem `isEquipartition` / 定理 `isEquipartition`

English:
theorem isEquipartition
  given: [DecidableEq V]
  statement: h.finpartition.IsEquipartition
  proof: by
  set fp := h.finpartition
  by_contra hn
  rw [Finpartition.not_isEquipartition] at hn
  obtain ⟨large, hl, small, hs, ineq⟩ := hn
  obtain ⟨w, hw⟩ := fp.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := fp.nonempty_of_mem_parts hs
  apply absurd h
  rw [IsTuranMaximal]; rw [IsExtremal]; push Not; in

中文:
定理 isEquipartition
  条件: [DecidableEq V]
  结论: h.finpartition.IsEquipartition
  证明: by
  set fp := h.finpartition
  by_contra hn
  rw [Finpartition.not_isEquipartition] at hn
  obtain ⟨large, hl, small, hs, ineq⟩ := hn
  obtain ⟨w, hw⟩ := fp.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := fp.nonempty_of_mem_parts hs
  apply absurd h
  rw [IsTuranMaximal]; rw [IsExtremal]; push Not; in

Depends on / 依赖: Finpartition, Finpartition.not_isEquipartition, G.Adj, G.replaceVertex, IsExtremal, IsTuranMaximal, absurd, cf.replaceVertex, finpartition, fp.nonempty_of_mem_parts, fp.part_eq_of_mem, h.finpartition, h.not_adj_iff_part_eq, large_eq, nonempty_of_mem_parts, not_adj_iff_part_eq, not_isEquipartition, part_eq_of_mem, replaceVertex, small_eq
-/
theorem isEquipartition [DecidableEq V] : h.finpartition.IsEquipartition := by
  set fp := h.finpartition
  by_contra hn
  rw [Finpartition.not_isEquipartition] at hn
  obtain ⟨large, hl, small, hs, ineq⟩ := hn
  obtain ⟨w, hw⟩ := fp.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := fp.nonempty_of_mem_parts hs
  apply absurd h
  rw [IsTuranMaximal]; rw [IsExtremal]; push Not; intro cf
  use G.replaceVertex v w, inferInstance, cf.replaceVertex v w
  have large_eq := fp.part_eq_of_mem hl hw
  have small_eq := fp.part_eq_of_mem hs hv
  have ha : G.Adj v w := by
    by_contra hn; rw [h.not_adj_iff_part_eq, small_eq, large_eq] at hn
    rw [hn] at ineq; lia
  rw [G.card_edgeFinset_replaceVertex_of_adj ha]; rw [degree_eq_card_sub_part_card h]; rw [small_eq]; rw [degree_eq_card_sub_part_card h]; rw [large_eq]
  have : #large <= card V := by simpa using card_le_card large.subset_univ
  lia

/--
lemma `card_parts_le` / 引理 `card_parts_le`

English:
lemma card_parts_le
  given: [DecidableEq V]
  statement: #h.finpartition.parts <= r
  proof: by
  by_contra! l
  obtain ⟨z, -, hz⟩ := h.finpartition.exists_subset_part_bijOn
  have ncf : ¬G.CliqueFree #z := by
    refine IsNClique.not_cliqueFree ⟨fun v hv w hw hn => ?_, rfl⟩
    contrapose hn
    exact hz.injOn hv hw (by rwa [← h.not_adj_iff_part_eq])
  rw [Finset.card_eq_of_equiv hz.equiv]

中文:
引理 card_parts_le
  条件: [DecidableEq V]
  结论: #h.finpartition.parts <= r
  证明: by
  by_contra! l
  obtain ⟨z, -, hz⟩ := h.finpartition.exists_subset_part_bijOn
  have ncf : ¬G.CliqueFree #z := by
    refine IsNClique.not_cliqueFree ⟨fun v hv w hw hn => ?_, rfl⟩
    contrapose hn
    exact hz.injOn hv hw (by rwa [← h.not_adj_iff_part_eq])
  rw [Finset.card_eq_of_equiv hz.equiv]

Depends on / 依赖: CliqueFree, Finset, Finset.card_eq_of_equiv, G.CliqueFree, IsNClique, IsNClique.not_cliqueFree, Nat.succ_le_of_lt, absurd, card_eq_of_equiv, contrapose, exists_subset_part_bijOn, finpartition, h.finpartition.exists_subset_part_bijOn, h.not_adj_iff_part_eq, hz.equiv, hz.injOn, not_adj_iff_part_eq, not_cliqueFree, succ_le_of_lt
-/
lemma card_parts_le [DecidableEq V] : #h.finpartition.parts <= r := by
  by_contra! l
  obtain ⟨z, -, hz⟩ := h.finpartition.exists_subset_part_bijOn
  have ncf : ¬G.CliqueFree #z := by
    refine IsNClique.not_cliqueFree ⟨fun v hv w hw hn => ?_, rfl⟩
    contrapose hn
    exact hz.injOn hv hw (by rwa [← h.not_adj_iff_part_eq])
  rw [Finset.card_eq_of_equiv hz.equiv] at ncf
  exact absurd (h.1.mono (Nat.succ_le_of_lt l)) ncf

/--
theorem `card_parts` / 定理 `card_parts`

English:
theorem card_parts
  given: [DecidableEq V]
  statement: #h.finpartition.parts = min (card V) r
  proof: by
  set fp := h.finpartition
  apply le_antisymm (le_min fp.card_parts_le_card h.card_parts_le)
  by_contra! l
  rw [lt_min_iff] at l
  obtain ⟨x, -, y, -, hn, he⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to l.1 fun a _ => fp.part_mem.2 (mem_univ a)
  apply absurd h
  rw [IsTuranMaximal]; rw [IsE

中文:
定理 card_parts
  条件: [DecidableEq V]
  结论: #h.finpartition.parts = min (card V) r
  证明: by
  set fp := h.finpartition
  apply le_antisymm (le_min fp.card_parts_le_card h.card_parts_le)
  by_contra! l
  rw [lt_min_iff] at l
  obtain ⟨x, -, y, -, hn, he⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to l.1 fun a _ => fp.part_mem.2 (mem_univ a)
  apply absurd h
  rw [IsTuranMaximal]; rw [IsE

Depends on / 依赖: CliqueFree, G.CliqueFree, IsExtremal, IsTuranMaximal, Set.Pairw, absurd, and_comm, card_parts_le, card_parts_le_card, cliqueFinset, cliqueFinset_eq_empty_iff, exists_ne_map_eq_of_card_lt_of_maps_to, filter_eq_empty_iff, finpartition, forall_true_left, fp.card_parts_le_card, fp.part_mem, h.card_parts_le, h.finpartition, isClique_iff
-/
theorem card_parts [DecidableEq V] : #h.finpartition.parts = min (card V) r := by
  set fp := h.finpartition
  apply le_antisymm (le_min fp.card_parts_le_card h.card_parts_le)
  by_contra! l
  rw [lt_min_iff] at l
  obtain ⟨x, -, y, -, hn, he⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to l.1 fun a _ => fp.part_mem.2 (mem_univ a)
  apply absurd h
  rw [IsTuranMaximal]; rw [IsExtremal]; push Not; rintro -
  have cf : G.CliqueFree r := by
    simp_rw [← cliqueFinset_eq_empty_iff, cliqueFinset, filter_eq_empty_iff, mem_univ,
      forall_true_left, isNClique_iff, and_comm, not_and, isClique_iff, Set.Pairwise]
    intro z zc; push Not; simp_rw [h.not_adj_iff_part_eq]
    exact exists_ne_map_eq_of_card_lt_of_maps_to (zc.symm ▸ l.2) fun a _ =>
      fp.part_mem.2 (mem_univ a)
  use G ⊔ edge x y, inferInstance, cf.sup_edge x y
  convert! Nat.lt_add_one #G.edgeFinset
  convert! G.card_edgeFinset_sup_edge _ hn
  rwa [h.not_adj_iff_part_eq]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `nonempty_iso_turanGraph` / 定理 `nonempty_iso_turanGraph`

English:
theorem nonempty_iso_turanGraph
  proof: by
  classical
  obtain ⟨zm, zp⟩ := h.isEquipartition.exists_partPreservingEquiv
  use (Equiv.subtypeUnivEquiv mem_univ).symm.trans zm
  intro a b
  simp_rw [turanGraph_adj, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply]
  have := zp ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩
  rw [← h.not_adj_iff_part_

中文:
定理 nonempty_iso_turanGraph
  证明: by
  classical
  obtain ⟨zm, zp⟩ := h.isEquipartition.exists_partPreservingEquiv
  use (Equiv.subtypeUnivEquiv mem_univ).symm.trans zm
  intro a b
  simp_rw [turanGraph_adj, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply]
  have := zp ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩
  rw [← h.not_adj_iff_part_

Depends on / 依赖: Equiv.subtypeUnivEquiv, Equiv.subtypeUnivEquiv_symm_apply, Equiv.trans_apply, card_parts, classical, exists_partPreservingEquiv, h.isEquipartition.exists_partPreservingEquiv, h.not_adj_iff_part_eq, isEquipartition, le_or_gt, mem_univ, min_eq_right, not_adj_iff_part_eq, not_iff_not, not_ne_iff, simp_rw, subtypeUnivEquiv, subtypeUnivEquiv_symm_apply, symm.trans, trans_apply
-/
theorem nonempty_iso_turanGraph :
    Nonempty (G ≃g turanGraph (card V) r) := by
  classical
  obtain ⟨zm, zp⟩ := h.isEquipartition.exists_partPreservingEquiv
  use (Equiv.subtypeUnivEquiv mem_univ).symm.trans zm
  intro a b
  simp_rw [turanGraph_adj, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply]
  have := zp ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩
  rw [← h.not_adj_iff_part_eq] at this
  rw [← not_iff_not]; rw [not_ne_iff]; rw [this]; rw [card_parts]
  rcases le_or_gt r (card V) with c | c
  · rw [min_eq_right c]; rfl
  · have lc : forall x, zm ⟨x, _⟩ < card V := fun x => (zm ⟨x, mem_univ x⟩).2
    rw [min_eq_left c.le]; rw [Nat.mod_eq_of_lt (lc a)]; rw [Nat.mod_eq_of_lt (lc b)]; rw [← Nat.mod_eq_of_lt ((lc a).trans c)]; rw [← Nat.mod_eq_of_lt ((lc b).trans c)]; rfl

end IsTuranMaximal

/--
theorem `isTuranMaximal_of_iso` / 定理 `isTuranMaximal_of_iso`

English:
theorem isTuranMaximal_of_iso
  given: (f : G ≃g turanGraph n r) (hr : 0 < r)
  statement: G.IsTuranMaximal r
  proof: by
  obtain ⟨J, _, j⟩ := exists_isTuranMaximal (V := V) hr
  obtain ⟨g⟩ := j.nonempty_iso_turanGraph
  rw [f.card_eq]; rw [Fintype.card_fin] at g
  use (turanGraph_cliqueFree (n := n) hr).comap f.isContained,
    fun H _ cf => (f.symm.comp g).card_edgeFinset_eq ▸ j.2 cf

中文:
定理 isTuranMaximal_of_iso
  条件: (f : G ≃g turanGraph n r) (hr : 0 < r)
  结论: G.IsTuranMaximal r
  证明: by
  obtain ⟨J, _, j⟩ := exists_isTuranMaximal (V := V) hr
  obtain ⟨g⟩ := j.nonempty_iso_turanGraph
  rw [f.card_eq]; rw [Fintype.card_fin] at g
  use (turanGraph_cliqueFree (n := n) hr).comap f.isContained,
    fun H _ cf => (f.symm.comp g).card_edgeFinset_eq ▸ j.2 cf

Depends on / 依赖: Fintype, Fintype.card_fin, card_edgeFinset_eq, card_eq, card_fin, exists_isTuranMaximal, f.card_eq, f.isContained, f.symm.comp, isContained, j.nonempty_iso_turanGraph, nonempty_iso_turanGraph, turanGraph_cliqueFree
-/
theorem isTuranMaximal_of_iso (f : G ≃g turanGraph n r) (hr : 0 < r) : G.IsTuranMaximal r := by
  obtain ⟨J, _, j⟩ := exists_isTuranMaximal (V := V) hr
  obtain ⟨g⟩ := j.nonempty_iso_turanGraph
  rw [f.card_eq]; rw [Fintype.card_fin] at g
  use (turanGraph_cliqueFree (n := n) hr).comap f.isContained,
    fun H _ cf => (f.symm.comp g).card_edgeFinset_eq ▸ j.2 cf

/--
theorem `IsTuranMaximal.iso` / 定理 `IsTuranMaximal.iso`

English:
theorem IsTuranMaximal.iso
  statement: {W : Type*} [Fintype W] {H : SimpleGraph W}
  proof: isTuranMaximal_of_iso (h.nonempty_iso_turanGraph.some.comp f.symm) hr

中文:
定理 IsTuranMaximal.iso
  结论: {W : 类型} [Fintype W] {H : SimpleGraph W}
  证明: isTuranMaximal_of_iso (h.nonempty_iso_turanGraph.some.comp f.symm) hr

Depends on / 依赖: f.symm, h.nonempty_iso_turanGraph.some.comp, isTuranMaximal_of_iso, nonempty_iso_turanGraph
-/
theorem IsTuranMaximal.iso {W : Type*} [Fintype W] {H : SimpleGraph W}
    [DecidableRel H.Adj] (h : G.IsTuranMaximal r) (f : G ≃g H) (hr : 0 < r) : H.IsTuranMaximal r :=
  isTuranMaximal_of_iso (h.nonempty_iso_turanGraph.some.comp f.symm) hr

/--
theorem `isTuranMaximal_turanGraph` / 定理 `isTuranMaximal_turanGraph`

English:
theorem isTuranMaximal_turanGraph
  given: (hr : 0 < r)
  statement: (turanGraph n r).IsTuranMaximal r
  proof: isTuranMaximal_of_iso Iso.refl hr

中文:
定理 isTuranMaximal_turanGraph
  条件: (hr : 0 < r)
  结论: (turanGraph n r).IsTuranMaximal r
  证明: isTuranMaximal_of_iso Iso.refl hr

Depends on / 依赖: Iso.refl, isTuranMaximal_of_iso
-/
theorem isTuranMaximal_turanGraph (hr : 0 < r) : (turanGraph n r).IsTuranMaximal r :=
  isTuranMaximal_of_iso Iso.refl hr

/--
theorem `isTuranMaximal_iff_nonempty_iso_turanGraph` / 定理 `isTuranMaximal_iff_nonempty_iso_turanGraph`

English:
theorem isTuranMaximal_iff_nonempty_iso_turanGraph
  given: (hr : 0 < r)
  proof: ⟨fun h => h.nonempty_iso_turanGraph, fun h => isTuranMaximal_of_iso h.some hr⟩

中文:
定理 isTuranMaximal_iff_nonempty_iso_turanGraph
  条件: (hr : 0 < r)
  证明: ⟨fun h => h.nonempty_iso_turanGraph, fun h => isTuranMaximal_of_iso h.some hr⟩

Depends on / 依赖: h.nonempty_iso_turanGraph, h.some, isTuranMaximal_of_iso, nonempty_iso_turanGraph
-/
theorem isTuranMaximal_iff_nonempty_iso_turanGraph (hr : 0 < r) :
    G.IsTuranMaximal r ↔ Nonempty (G ≃g turanGraph (card V) r) :=
  ⟨fun h => h.nonempty_iso_turanGraph, fun h => isTuranMaximal_of_iso h.some hr⟩

variable {α : Type*} [Fintype α] [Nontrivial α]

/--
lemma `isExtremal_top_free_iff_isTuranMaximal` / 引理 `isExtremal_top_free_iff_isTuranMaximal`

English:
lemma isExtremal_top_free_iff_isTuranMaximal
  proof: by
  simp_rw [IsTuranMaximal, IsExtremal,
    Nat.sub_one_add_one Fintype.card_ne_zero, cliqueFree_iff_top_free]

中文:
引理 isExtremal_top_free_iff_isTuranMaximal
  证明: by
  simp_rw [IsTuranMaximal, IsExtremal,
    Nat.sub_one_add_one Fintype.card_ne_zero, cliqueFree_iff_top_free]

Depends on / 依赖: Fintype, Fintype.card_ne_zero, IsExtremal, IsTuranMaximal, Nat.sub_one_add_one, card_ne_zero, cliqueFree_iff_top_free, simp_rw, sub_one_add_one
-/
lemma isExtremal_top_free_iff_isTuranMaximal :
    G.IsExtremal (⊤ : SimpleGraph α).Free ↔ G.IsTuranMaximal (card α - 1) := by
  simp_rw [IsTuranMaximal, IsExtremal,
    Nat.sub_one_add_one Fintype.card_ne_zero, cliqueFree_iff_top_free]

/--
lemma `isExtremal_top_free_turanGraph` / 引理 `isExtremal_top_free_turanGraph`

English:
lemma isExtremal_top_free_turanGraph
  proof: by
  rw [isExtremal_top_free_iff_isTuranMaximal]
  exact isTuranMaximal_turanGraph (Nat.sub_pos_iff_lt.mpr Fintype.one_lt_card)

中文:
引理 isExtremal_top_free_turanGraph
  证明: by
  rw [isExtremal_top_free_iff_isTuranMaximal]
  exact isTuranMaximal_turanGraph (Nat.sub_pos_iff_lt.mpr Fintype.one_lt_card)

Depends on / 依赖: Fintype, Fintype.one_lt_card, Nat.sub_pos_iff_lt.mpr, isExtremal_top_free_iff_isTuranMaximal, isTuranMaximal_turanGraph, one_lt_card, sub_pos_iff_lt
-/
lemma isExtremal_top_free_turanGraph :
    (turanGraph n (card α - 1)).IsExtremal (⊤ : SimpleGraph α).Free := by
  rw [isExtremal_top_free_iff_isTuranMaximal]
  exact isTuranMaximal_turanGraph (Nat.sub_pos_iff_lt.mpr Fintype.one_lt_card)

/--
theorem `extremalNumber_top` / 定理 `extremalNumber_top`

English:
theorem extremalNumber_top
  proof: by
  conv =>
    enter [1, 1]
    rw [← Fintype.card_fin n]
  exact (card_edgeFinset_of_isExtremal_free isExtremal_top_free_turanGraph).symm

中文:
定理 extremalNumber_top
  证明: by
  conv =>
    enter [1, 1]
    rw [← Fintype.card_fin n]
  exact (card_edgeFinset_of_isExtremal_free isExtremal_top_free_turanGraph).symm

Depends on / 依赖: Fintype, Fintype.card_fin, card_edgeFinset_of_isExtremal_free, card_fin, isExtremal_top_free_turanGraph
-/
theorem extremalNumber_top :
    extremalNumber n (⊤ : SimpleGraph α) = #(turanGraph n (card α - 1)).edgeFinset := by
  conv =>
    enter [1, 1]
    rw [← Fintype.card_fin n]
  exact (card_edgeFinset_of_isExtremal_free isExtremal_top_free_turanGraph).symm

/--
theorem `card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph` / 定理 `card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph`

English:
theorem card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph
  proof: by
  rw [← isTuranMaximal_iff_nonempty_iso_turanGraph (Nat.sub_pos_iff_lt.mpr one_lt_card)]; rw [← isExtremal_top_free_iff_isTuranMaximal]; rw [isExtremal_free_iff]

中文:
定理 card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph
  证明: by
  rw [← isTuranMaximal_iff_nonempty_iso_turanGraph (Nat.sub_pos_iff_lt.mpr one_lt_card)]; rw [← isExtremal_top_free_iff_isTuranMaximal]; rw [isExtremal_free_iff]

Depends on / 依赖: Nat.sub_pos_iff_lt.mpr, isExtremal_free_iff, isExtremal_top_free_iff_isTuranMaximal, isTuranMaximal_iff_nonempty_iso_turanGraph, one_lt_card, sub_pos_iff_lt
-/
theorem card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph :
    (⊤ : SimpleGraph α).Free G ∧ #G.edgeFinset = extremalNumber (card V) (⊤ : SimpleGraph α)
      ↔ Nonempty (G ≃g turanGraph (card V) (card α - 1)) := by
  rw [← isTuranMaximal_iff_nonempty_iso_turanGraph (Nat.sub_pos_iff_lt.mpr one_lt_card)]; rw [← isExtremal_top_free_iff_isTuranMaximal]; rw [isExtremal_free_iff]


/--
lemma `sum_ne_add_mod_eq_sub_one` / 引理 `sum_ne_add_mod_eq_sub_one`

English:
lemma sum_ne_add_mod_eq_sub_one
  given: {c : Nat}
  proof: by
  rcases r.eq_zero_or_pos with rfl | hr; · simp
  suffices #{i in range r | c % r = (n + i) % r} = 1 by
    rw [← card_filter]; rw [← this]; apply Nat.eq_sub_of_add_eq'
    rw [card_filter_add_card_filter_not]; rw [card_range]
  apply le_antisymm
  · change #{i in range r | _ ≡ _ [MOD r]} <= 1
  

中文:
引理 sum_ne_add_mod_eq_sub_one
  条件: {c : 自然数}
  证明: by
  rcases r.eq_zero_or_pos with rfl | hr; · simp
  suffices #{i in range r | c % r = (n + i) % r} = 1 by
    rw [← card_filter]; rw [← this]; apply Nat.eq_sub_of_add_eq'
    rw [card_filter_add_card_filter_not]; rw [card_range]
  apply le_antisymm
  · change #{i in range r | _ ≡ _ [MOD r]} <= 1
  
-/
private lemma sum_ne_add_mod_eq_sub_one {c : Nat} :
    ∑ w in range r, (if c % r != (n + w) % r then 1 else 0) = r - 1 := by
  rcases r.eq_zero_or_pos with rfl | hr; · simp
  suffices #{i in range r | c % r = (n + i) % r} = 1 by
    rw [← card_filter]; rw [← this]; apply Nat.eq_sub_of_add_eq'
    rw [card_filter_add_card_filter_not]; rw [card_range]
  apply le_antisymm
  · change #{i in range r | _ ≡ _ [MOD r]} <= 1
    rw [card_le_one_iff]; intro w x mw mx
    simp only [mem_filter, mem_range] at mw mx
    have := mw.2.symm.trans mx.2
    rw [Nat.ModEq.add_iff_left rfl] at this
    change w % r = x % r at this
    rwa [Nat.mod_eq_of_lt mw.1, Nat.mod_eq_of_lt mx.1] at this
  · rw [one_le_card]; use ((r - 1) * n + c) % r
    simp only [mem_filter, mem_range]; refine ⟨Nat.mod_lt _ hr, ?_⟩
    rw [Nat.add_mod_mod]; rw [← add_assoc]; rw [← one_add_mul]; rw [show 1 + (r - 1) = r by lia]; rw [Nat.mul_add_mod_self_left]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `card_edgeFinset_turanGraph_add` / 引理 `card_edgeFinset_turanGraph_add`

English:
lemma card_edgeFinset_turanGraph_add
  proof: by
  rw [← mul_right_inj' two_ne_zero]
  simp_rw [mul_add, ← sum_degrees_eq_twice_card_edges,
    degree, neighborFinset_eq_filter, turanGraph, card_filter]
  conv_lhs =>
    enter [2, v]
    rw [Fin.sum_univ_eq_sum_range fun w => if v % r != w % r then 1 else 0]; rw [sum_range_add]
  rw [sum_add_di

中文:
引理 card_edgeFinset_turanGraph_add
  证明: by
  rw [← mul_right_inj' two_ne_zero]
  simp_rw [mul_add, ← sum_degrees_eq_twice_card_edges,
    degree, neighborFinset_eq_filter, turanGraph, card_filter]
  conv_lhs =>
    enter [2, v]
    rw [Fin.sum_univ_eq_sum_range fun w => if v % r != w % r then 1 else 0]; rw [sum_range_add]
  rw [sum_add_di

Depends on / 依赖: Fin.sum_univ_eq_sum_range, card_filter, conv_lhs, degree, mul_add, mul_right_inj, neighborFinset_eq_filter, simp_rw, sum_add_distrib, sum_degrees_eq_twice_card_edges, sum_range_add, sum_univ_eq_sum_range, turanGraph, two_ne_zero
-/
lemma card_edgeFinset_turanGraph_add :
    #(turanGraph (n + r) r).edgeFinset =
    #(turanGraph n r).edgeFinset + n * (r - 1) + r.choose 2 := by
  rw [← mul_right_inj' two_ne_zero]
  simp_rw [mul_add, ← sum_degrees_eq_twice_card_edges,
    degree, neighborFinset_eq_filter, turanGraph, card_filter]
  conv_lhs =>
    enter [2, v]
    rw [Fin.sum_univ_eq_sum_range fun w => if v % r != w % r then 1 else 0]; rw [sum_range_add]
  rw [sum_add_distrib]; rw [Fin.sum_univ_eq_sum_range fun v => ∑ w in range n]; rw [if v % r != w % r then 1 else 0]; rw [Fin.sum_univ_eq_sum_range fun v => ∑ w in range r]; rw [if v % r != (n + w) % r then 1 else 0]; rw [sum_range_add]; rw [sum_range_add]; rw [add_assoc]; rw [add_assoc]
  congr 1; · simp [← Fin.sum_univ_eq_sum_range]
  rw [← add_assoc]; rw [sum_comm]; simp_rw [ne_comm, ← two_mul]; congr
  · conv_rhs => rw [← card_range n, ← smul_eq_mul, ← sum_const]
    congr!; exact sum_ne_add_mod_eq_sub_one
  · rw [mul_comm 2, Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self r)]
    conv_rhs => enter [1]; rw [← card_range r]
    rw [← smul_eq_mul]; rw [← sum_const]
    congr!; exact sum_ne_add_mod_eq_sub_one

/--
theorem `card_edgeFinset_turanGraph` / 定理 `card_edgeFinset_turanGraph`

English:
theorem card_edgeFinset_turanGraph
  given: {n r : Nat}
  proof: by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [Nat.mod_zero, tsub_self, zero_mul, Nat.zero_div, zero_add]
    have := card_edgeFinset_top_eq_card_choose_two (V := Fin n)
    rw [Fintype.card_fin] at this; convert! this; exact turanGraph_zero
  · have ring₁ (n) : (n ^ 2 - (n % r) ^ 2) * (r - 1) /

中文:
定理 card_edgeFinset_turanGraph
  条件: {n r : 自然数}
  证明: by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [Nat.mod_zero, tsub_self, zero_mul, Nat.zero_div, zero_add]
    have := card_edgeFinset_top_eq_card_choose_two (V := Fin n)
    rw [Fintype.card_fin] at this; convert! this; exact turanGraph_zero
  · have ring₁ (n) : (n ^ 2 - (n % r) ^ 2) * (r - 1) /

Depends on / 依赖: Fintype, Fintype.card_fin, Nat.mod_add_div, Nat.mod_zero, Nat.sq_sub_sq, Nat.zero_div, add_tsub_cancel_left, card_edgeFinset_top_eq_card_choose_two, card_fin, convert, eq_zero_or_pos, mod_add_div, mod_zero, nth_rw, r.eq_zero_or_pos, sq_sub_sq, tsub_self, turanGraph_zero, zero_add, zero_div
-/
theorem card_edgeFinset_turanGraph {n r : Nat} :
    #(turanGraph n r).edgeFinset =
    (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [Nat.mod_zero, tsub_self, zero_mul, Nat.zero_div, zero_add]
    have := card_edgeFinset_top_eq_card_choose_two (V := Fin n)
    rw [Fintype.card_fin] at this; convert! this; exact turanGraph_zero
  · have ring₁ (n) : (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) =
        n % r * (n / r) * (r - 1) + r * (r - 1) * (n / r) ^ 2 / 2 := by
      nth_rw 1 [← Nat.mod_add_div n r, Nat.sq_sub_sq, add_tsub_cancel_left,
        show (n % r + r * (n / r) + n % r) * (r * (n / r)) * (r - 1) =
          (2 * ((n % r) * (n / r) * (r - 1)) + r * (r - 1) * (n / r) ^ 2) * r by grind]
      rw [Nat.mul_div_mul_right _ _ hr]; rw [Nat.mul_add_div zero_lt_two]
    rcases lt_or_ge n r with h | h
    · rw [Nat.mod_eq_of_lt h, tsub_self, zero_mul, Nat.zero_div, zero_add]
      have := card_edgeFinset_top_eq_card_choose_two (V := Fin n)
      rw [Fintype.card_fin] at this; convert! this
      rw [turanGraph_eq_top]; exact .inr h.le
    · let n' := n - r
      have n'r : n = n' + r := by lia
      rw [n'r]; rw [card_edgeFinset_turanGraph_add]; rw [card_edgeFinset_turanGraph]; rw [ring₁]; rw [ring₁]; rw [add_rotate]; rw [← add_assoc]; rw [Nat.add_mod_right]; rw [Nat.add_div_right _ hr]
      congr 1
      have rd : 2 ∣ r * (r - 1) := (Nat.even_mul_pred_self _).two_dvd
      rw [← Nat.div_mul_right_comm rd]; rw [← Nat.div_mul_right_comm rd]; rw [← Nat.choose_two_right]
      have ring₂ : n' % r * (n' / r + 1) * (r - 1) + r.choose 2 * (n' / r + 1) ^ 2 =
          n' % r * (n' / r + 1) * (r - 1) + r.choose 2 +
          r.choose 2 * 2 * (n' / r) + r.choose 2 * (n' / r) ^ 2 := by grind
      rw [ring₂]; rw [← add_assoc]; congr 1
      rw [← add_rotate]; rw [← add_rotate _ _ (r.choose 2)]; congr 1
      rw [Nat.choose_two_right]; rw [Nat.div_mul_cancel rd]; rw [mul_add_one]; rw [add_mul]; rw [← add_assoc]; rw [← add_rotate]; rw [add_comm _ (_ * _)]; congr 1
      rw [← mul_rotate]; rw [← add_mul]; rw [add_comm]; rw [mul_comm _ r]; rw [Nat.div_add_mod n' r]

/--
theorem `mul_card_edgeFinset_turanGraph_le` / 定理 `mul_card_edgeFinset_turanGraph_le`

English:
theorem mul_card_edgeFinset_turanGraph_le
  proof: by
  grw [card_edgeFinset_turanGraph, mul_add, Nat.mul_div_le]
  rw [tsub_mul]; rw [← Nat.sub_add_comm]; swap
  · grw [Nat.mod_le]
    exact Nat.zero_le _
  rw [Nat.sub_le_iff_le_add]; rw [mul_comm]; rw [Nat.add_le_add_iff_left]; rw [Nat.choose_two_right]; rw [← Nat.mul_div_assoc _ (Nat.even_mul_pre

中文:
定理 mul_card_edgeFinset_turanGraph_le
  证明: by
  grw [card_edgeFinset_turanGraph, mul_add, Nat.mul_div_le]
  rw [tsub_mul]; rw [← Nat.sub_add_comm]; swap
  · grw [Nat.mod_le]
    exact Nat.zero_le _
  rw [Nat.sub_le_iff_le_add]; rw [mul_comm]; rw [Nat.add_le_add_iff_left]; rw [Nat.choose_two_right]; rw [← Nat.mul_div_assoc _ (Nat.even_mul_pre

Depends on / 依赖: Nat.add_le_add_iff_left, Nat.choose_two_right, Nat.even_mul_pred_self, Nat.mod_le, Nat.mul_div_assoc, Nat.mul_div_le, Nat.sub_add_comm, Nat.sub_le_iff_le_add, Nat.zero_le, add_le_add_iff_left, card_edgeFinset_turanGraph, choose_two_right, eq_zero_or_pos, even_mul_pred_self, mod_le, mul_add, mul_assoc, mul_comm, mul_div_assoc, mul_div_le
-/
theorem mul_card_edgeFinset_turanGraph_le :
    2 * r * #(turanGraph n r).edgeFinset <= (r - 1) * n ^ 2 := by
  grw [card_edgeFinset_turanGraph, mul_add, Nat.mul_div_le]
  rw [tsub_mul]; rw [← Nat.sub_add_comm]; swap
  · grw [Nat.mod_le]
    exact Nat.zero_le _
  rw [Nat.sub_le_iff_le_add]; rw [mul_comm]; rw [Nat.add_le_add_iff_left]; rw [Nat.choose_two_right]; rw [← Nat.mul_div_assoc _ (Nat.even_mul_pred_self _).two_dvd]; rw [mul_assoc]; rw [mul_div_cancel_left₀ _ two_ne_zero]; rw [← mul_assoc]; rw [← mul_rotate]; rw [sq]; rw [← mul_rotate (r - 1)]
  gcongr ?_ * _
  rcases r.eq_zero_or_pos with rfl | hr; · lia
  rw [Nat.sub_one_mul]; rw [Nat.sub_one_mul]; rw [mul_comm]
  exact Nat.sub_le_sub_left (Nat.mod_lt _ hr).le _

/--
theorem `CliqueFree.card_edgeFinset_le` / 定理 `CliqueFree.card_edgeFinset_le`

English:
theorem CliqueFree.card_edgeFinset_le
  given: (cf : G.CliqueFree (r + 1))
  proof: Fintype.card V;
    #G.edgeFinset <= (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [cliqueFree_one, ← Fintype.card_eq_zero_iff] at cf
    simp_rw [zero_tsub, mul_zero, Nat.mod_zero, Nat.div_zero, zero_add]
    exact card_edgeFinset_

中文:
定理 CliqueFree.card_edgeFinset_le
  条件: (cf : G.CliqueFree (r + 1))
  证明: Fintype.card V;
    #G.edgeFinset <= (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [cliqueFree_one, ← Fintype.card_eq_zero_iff] at cf
    simp_rw [zero_tsub, mul_zero, Nat.mod_zero, Nat.div_zero, zero_add]
    exact card_edgeFinset_

Depends on / 依赖: Fintype, Fintype.card
-/
theorem CliqueFree.card_edgeFinset_le (cf : G.CliqueFree (r + 1)) :
    let n := Fintype.card V;
    #G.edgeFinset <= (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by
  rcases r.eq_zero_or_pos with rfl | hr
  · rw [cliqueFree_one, ← Fintype.card_eq_zero_iff] at cf
    simp_rw [zero_tsub, mul_zero, Nat.mod_zero, Nat.div_zero, zero_add]
    exact card_edgeFinset_le_card_choose_two
  · obtain ⟨H, _, maxH⟩ := exists_isTuranMaximal (V := V) hr
    convert! maxH.2 cf
    rw [((isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp maxH).some.card_edgeFinset_eq]; rw [card_edgeFinset_turanGraph]

end SimpleGraph
