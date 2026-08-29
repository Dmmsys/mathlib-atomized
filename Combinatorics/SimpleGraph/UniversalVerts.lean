/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Universal Vertices

This file defines the set of universal vertices: those vertices that are connected
to all others. In addition, it describes results when considering connected components
of the graph where universal vertices are deleted. This particular graph plays a role
in the proof of Tutte's Theorem.

## Main definitions

* `G.universalVerts` is the set of vertices that are connected to all other vertices.
* `G.deleteUniversalVerts` is the subgraph of `G` with the universal vertices removed.
-/

@[expose] public section

assert_not_exists Field TwoSidedIdeal

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/--
Definition of `universalVerts` / `universalVerts` 的定义

English:
definition universalVerts
  signature: (G : SimpleGraph V)
  body: {v : V | G.IsUniversal v}

中文:
定义 universalVerts
  签名: (G : SimpleGraph V)
  定义体: {v : V | G.IsUniversal v}

Depends on / 依赖: G.IsUniversal, IsUniversal
-/
def universalVerts (G : SimpleGraph V) : Set V := {v : V | G.IsUniversal v}

/--
lemma `isClique_universalVerts` / 引理 `isClique_universalVerts`

English:
lemma isClique_universalVerts
  given: (G : SimpleGraph V)
  statement: G.IsClique G.universalVerts
  proof: fun _ hx _ _ hxy => hx hxy

中文:
引理 isClique_universalVerts
  条件: (G : SimpleGraph V)
  结论: G.IsClique G.universalVerts
  证明: fun _ hx _ _ hxy => hx hxy
-/
lemma isClique_universalVerts (G : SimpleGraph V) : G.IsClique G.universalVerts :=
  fun _ hx _ _ hxy => hx hxy

/--
The subgraph of `G` with the universal vertices removed.
-/
@[simps!]
/--
Definition of `deleteUniversalVerts` / `deleteUniversalVerts` 的定义

English:
definition deleteUniversalVerts
  signature: (G : SimpleGraph V)
  body: (⊤ : Subgraph G).deleteVerts G.universalVerts

中文:
定义 deleteUniversalVerts
  签名: (G : SimpleGraph V)
  定义体: (⊤ : Subgraph G).deleteVerts G.universalVerts

Depends on / 依赖: G.universalVerts, Subgraph, deleteVerts, universalVerts
-/
def deleteUniversalVerts (G : SimpleGraph V) : Subgraph G :=
  (⊤ : Subgraph G).deleteVerts G.universalVerts

/--
lemma `Subgraph.IsMatching.exists_of_universalVerts` / 引理 `Subgraph.IsMatching.exists_of_universalVerts`

English:
lemma Subgraph.IsMatching.exists_of_universalVerts
  statement: [Finite V] {s : Set V}
  proof: by
  obtain ⟨t, ht⟩ := Set.exists_subset_card_eq hc
  refine ⟨t, ht.1, ?_⟩
  obtain ⟨f⟩ : Nonempty (s ≃ t) := by
    rw [← Cardinal.eq]; rw [← t.cast_ncard t.toFinite]; rw [← s.cast_ncard s.toFinite]; rw [ht.2]
  let hd := Set.disjoint_of_subset_left ht.1 h
.symm have hadj (v : s) : G.Adj v (f v) :=

中文:
引理 Subgraph.IsMatching.exists_of_universalVerts
  结论: [Finite V] {s : Set V}
  证明: by
  obtain ⟨t, ht⟩ := Set.exists_subset_card_eq hc
  refine ⟨t, ht.1, ?_⟩
  obtain ⟨f⟩ : Nonempty (s ≃ t) := by
    rw [← Cardinal.eq]; rw [← t.cast_ncard t.toFinite]; rw [← s.cast_ncard s.toFinite]; rw [ht.2]
  let hd := Set.disjoint_of_subset_left ht.1 h
.symm have hadj (v : s) : G.Adj v (f v) :=

Depends on / 依赖: Cardinal, Cardinal.eq, G.Adj, IsMatching, Nonempty, Set.disjoint_of_subset_left, Set.exists_subset_card_eq, Subgraph, Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv, cast_ncard, disjoint_of_subset_left, exists_of_disjoint_sets_of_equiv, exists_subset_card_eq, hd.ne_of_mem, hd.symm, ne_of_mem, s.cast_ncard, s.toFinite, t.cast_ncard, t.toFinite
-/
lemma Subgraph.IsMatching.exists_of_universalVerts [Finite V] {s : Set V}
    (h : Disjoint G.universalVerts s) (hc : s.ncard <= G.universalVerts.ncard) :
    exists t subseteq G.universalVerts, exists (M : Subgraph G), M.verts = s union t ∧ M.IsMatching := by
  obtain ⟨t, ht⟩ := Set.exists_subset_card_eq hc
  refine ⟨t, ht.1, ?_⟩
  obtain ⟨f⟩ : Nonempty (s ≃ t) := by
    rw [← Cardinal.eq]; rw [← t.cast_ncard t.toFinite]; rw [← s.cast_ncard s.toFinite]; rw [ht.2]
  let hd := Set.disjoint_of_subset_left ht.1 h
.symm have hadj (v : s) : G.Adj v (f v) := ht.1 (f v).2 (hd.ne_of_mem (f v).2 v.2)
  exact Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hd.symm f hadj

/--
lemma `disjoint_image_val_universalVerts` / 引理 `disjoint_image_val_universalVerts`

English:
lemma disjoint_image_val_universalVerts
  given: (s : Set G.deleteUniversalVerts.verts)
  proof: by
  simpa [← Set.disjoint_compl_right_iff_subset, Set.compl_eq_univ_sdiff] using
    Subtype.coe_image_subset _ s

中文:
引理 disjoint_image_val_universalVerts
  条件: (s : Set G.deleteUniversalVerts.verts)
  证明: by
  simpa [← Set.disjoint_compl_right_iff_subset, Set.compl_eq_univ_sdiff] using
    Subtype.coe_image_subset _ s

Depends on / 依赖: Set.compl_eq_univ_sdiff, Set.disjoint_compl_right_iff_subset, Subtype, Subtype.coe_image_subset, coe_image_subset, compl_eq_univ_sdiff, disjoint_compl_right_iff_subset
-/
lemma disjoint_image_val_universalVerts (s : Set G.deleteUniversalVerts.verts) :
    Disjoint (Subtype.val '' s) G.universalVerts := by
  simpa [← Set.disjoint_compl_right_iff_subset, Set.compl_eq_univ_sdiff] using
    Subtype.coe_image_subset _ s

/--
lemma `even_ncard_image_val_supp_sdiff_image_val_rep_union` / 引理 `even_ncard_image_val_supp_sdiff_image_val_rep_union`

English:
lemma even_ncard_image_val_supp_sdiff_image_val_rep_union
  statement: {t : Set V}
  proof: by
  simp [-deleteUniversalVerts_verts, ← Set.sdiff_inter_sdiff,
    ← Set.image_sdiff Subtype.val_injective,
sdiff_eq_left.mpr Set.disjoint_of_subset_right h (disjoint_image_val_universalVerts _),
    Set.inter_sdiff_distrib_right, ← Set.image_inter Subtype.val_injective,
    Set.ncard_image_of_inj

中文:
引理 even_ncard_image_val_supp_sdiff_image_val_rep_union
  结论: {t : Set V}
  证明: by
  simp [-deleteUniversalVerts_verts, ← Set.sdiff_inter_sdiff,
    ← Set.image_sdiff Subtype.val_injective,
sdiff_eq_left.mpr Set.disjoint_of_subset_right h (disjoint_image_val_universalVerts _),
    Set.inter_sdiff_distrib_right, ← Set.image_inter Subtype.val_injective,
    Set.ncard_image_of_inj

Depends on / 依赖: K.even_ncard_supp_sdiff_rep, Set.disjoint_of_subset_right, Set.image_inter, Set.image_sdiff, Set.inter_sdiff_distrib_right, Set.ncard_image_of_injective, Set.sdiff_inter_sdiff, Subtype, Subtype.val_injective, deleteUniversalVerts_verts, disjoint_image_val_universalVerts, disjoint_of_subset_right, even_ncard_supp_sdiff_rep, image_inter, image_sdiff, inter_sdiff_distrib_right, ncard_image_of_injective, sdiff_eq_left, sdiff_eq_left.mpr, sdiff_inter_sdiff
-/
lemma even_ncard_image_val_supp_sdiff_image_val_rep_union {t : Set V}
    {s : Set G.deleteUniversalVerts.verts} (K : G.deleteUniversalVerts.coe.ConnectedComponent)
    (h : t subseteq G.universalVerts)
    (hrep : ConnectedComponent.Represents s G.deleteUniversalVerts.coe.oddComponents) :
    Even (Subtype.val '' K.supp \ (Subtype.val '' s union t)).ncard := by
  simp [-deleteUniversalVerts_verts, ← Set.sdiff_inter_sdiff,
    ← Set.image_sdiff Subtype.val_injective,
sdiff_eq_left.mpr Set.disjoint_of_subset_right h (disjoint_image_val_universalVerts _),
    Set.inter_sdiff_distrib_right, ← Set.image_inter Subtype.val_injective,
    Set.ncard_image_of_injective _ Subtype.val_injective, K.even_ncard_supp_sdiff_rep hrep]

end SimpleGraph
