/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Int.Cast.Basic

/-!
# Edge deletion

This file defines operations deleting the edges of a simple graph and proves theorems in the finite
case.

## Main definitions

* `SimpleGraph.deleteEdges G s` is the simple graph `G` with the edges `s : Set (Sym2 V)` removed
  from the edge set.

* `SimpleGraph.deleteIncidenceSet G v` is the simple graph `G` with the incidence set of `v`
  removed from the edge set.

* `SimpleGraph.DeleteFar G p r` is the predicate that a graph is `r`-*delete-far* from a property
  `p`, that is, at least `r` edges must be deleted to satisfy `p`.
-/

@[expose] public section


open Finset Fintype

namespace SimpleGraph

variable {V : Type*} {v w : V} (G : SimpleGraph V)

section DeleteEdges

/--
Definition of `deleteEdges` / `deleteEdges` 的定义

English:
definition deleteEdges
  signature: (s : Set (Sym2 V))
  body: G \ fromEdgeSet s

中文:
定义 deleteEdges
  签名: (s : 集合 (Sym2 V))
  定义体: G \ fromEdgeSet s

Depends on / 依赖: fromEdgeSet
-/
def deleteEdges (s : Set (Sym2 V)) : SimpleGraph V := G \ fromEdgeSet s

variable {G} {H : SimpleGraph V} {s s₁ s₂ : Set (Sym2 V)}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableRel
  signature: G.Adj] [DecidablePred (· in s)] [DecidableEq V] :
  body: inferInstanceAs DecidableRel (G \ fromEdgeSet s).Adj

中文:
实例 [DecidableRel
  签名: G.伴随] [DecidablePred (· in s)] [DecidableEq V] :
  定义体: inferInstanceAs DecidableRel (G \ fromEdgeSet s).Adj

Depends on / 依赖: DecidableRel, fromEdgeSet
-/
instance [DecidableRel G.Adj] [DecidablePred (· in s)] [DecidableEq V] :
    DecidableRel (G.deleteEdges s).Adj :=
inferInstanceAs DecidableRel (G \ fromEdgeSet s).Adj

/--
lemma `deleteEdges_adj` / 引理 `deleteEdges_adj`

English:
lemma deleteEdges_adj
  statement: (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s
  proof: and_congr_right fun h => (and_iff_left h.ne).not

中文:
引理 deleteEdges_adj
  结论: (G.deleteEdges s).伴随 v w ↔ G.伴随 v w ∧ s(v, w) ∉ s
  证明: and_congr_right fun h => (and_iff_left h.ne).not
-/
@[simp] lemma deleteEdges_adj : (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s :=
  and_congr_right fun h => (and_iff_left h.ne).not

/--
lemma `deleteEdges_edgeSet` / 引理 `deleteEdges_edgeSet`

English:
lemma deleteEdges_edgeSet
  given: (G G' : SimpleGraph V)
  statement: G.deleteEdges G'.edgeSet = G \ G'
  proof: by
  ext; simp

@[simp]

中文:
引理 deleteEdges_edgeSet
  条件: (G G' : 简单图 V)
  结论: G.deleteEdges G'.edgeSet = G \ G'
  证明: by
  ext; simp

@[simp]
-/
@[simp] lemma deleteEdges_edgeSet (G G' : SimpleGraph V) : G.deleteEdges G'.edgeSet = G \ G' := by
  ext; simp

@[simp]
/--
theorem `deleteEdges_deleteEdges` / 定理 `deleteEdges_deleteEdges`

English:
theorem deleteEdges_deleteEdges
  given: (s s' : Set (Sym2 V))
  proof: by simp [deleteEdges, sdiff_sdiff]

中文:
定理 deleteEdges_deleteEdges
  条件: (s s' : 集合 (Sym2 V))
  证明: by simp [deleteEdges, sdiff_sdiff]

Depends on / 依赖: deleteEdges, sdiff_sdiff
-/
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s union s') := by simp [deleteEdges, sdiff_sdiff]

-- This is not marked `simp` since `deleteEdges_of_subset_diagSet` already proves it
/--
lemma `deleteEdges_empty` / 引理 `deleteEdges_empty`

English:
lemma deleteEdges_empty
  statement: G.deleteEdges ∅ = G
  proof: by simp [deleteEdges]

中文:
引理 deleteEdges_empty
  结论: G.deleteEdges ∅ = G
  证明: by simp [deleteEdges]

Depends on / 依赖: G.deleteEdges, Set.univ, deleteEdges, deleteEdges_univ
-/
lemma deleteEdges_empty : G.deleteEdges ∅ = G := by simp [deleteEdges]
/--
lemma `deleteEdges_univ` / 引理 `deleteEdges_univ`

English:
lemma deleteEdges_univ
  statement: G.deleteEdges Set.univ = ⊥
  proof: by simp [deleteEdges]

@[simp]

中文:
引理 deleteEdges_univ
  结论: G.deleteEdges 集合.univ = ⊥
  证明: by simp [deleteEdges]

@[simp]
-/
@[simp] lemma deleteEdges_univ : G.deleteEdges Set.univ = ⊥ := by simp [deleteEdges]

@[simp]
/--
theorem `deleteEdges_le_iff` / 定理 `deleteEdges_le_iff`

English:
theorem deleteEdges_le_iff
  given: (s : Set (Sym2 V)) (G' : SimpleGraph V)
  proof: by
    rw [deleteEdges]; rw [sdiff_le_iff]

中文:
定理 deleteEdges_le_iff
  条件: (s : 集合 (Sym2 V)) (G' : 简单图 V)
  证明: by
    rw [deleteEdges]; rw [sdiff_le_iff]

Depends on / 依赖: deleteEdges, sdiff_le_iff
-/
theorem deleteEdges_le_iff (s : Set (Sym2 V)) (G' : SimpleGraph V) :
    G.deleteEdges s <= G' ↔ G <= fromEdgeSet s ⊔ G' := by
    rw [deleteEdges]; rw [sdiff_le_iff]

/--
lemma `deleteEdges_le` / 引理 `deleteEdges_le`

English:
lemma deleteEdges_le
  given: (s : Set (Sym2 V))
  statement: G.deleteEdges s <= G
  proof: sdiff_le

中文:
引理 deleteEdges_le
  条件: (s : 集合 (Sym2 V))
  结论: G.deleteEdges s <= G
  证明: sdiff_le

Depends on / 依赖: sdiff_le
-/
lemma deleteEdges_le (s : Set (Sym2 V)) : G.deleteEdges s <= G := sdiff_le

/--
lemma `deleteEdges_anti` / 引理 `deleteEdges_anti`

English:
lemma deleteEdges_anti
  given: (h : s₁ subseteq s₂)
  statement: G.deleteEdges s₂ <= G.deleteEdges s₁
  proof: sdiff_le_sdiff_left fromEdgeSet_mono h

@[gcongr]

中文:
引理 deleteEdges_anti
  条件: (h : s₁ subseteq s₂)
  结论: G.deleteEdges s₂ <= G.deleteEdges s₁
  证明: sdiff_le_sdiff_left fromEdgeSet_mono h

@[gcongr]
-/
@[gcongr] lemma deleteEdges_anti (h : s₁ subseteq s₂) : G.deleteEdges s₂ <= G.deleteEdges s₁ :=
sdiff_le_sdiff_left fromEdgeSet_mono h

@[gcongr]
/--
lemma `deleteEdges_mono` / 引理 `deleteEdges_mono`

English:
lemma deleteEdges_mono
  given: (h : G <= H)
  statement: G.deleteEdges s <= H.deleteEdges s
  proof: sdiff_le_sdiff_right h

中文:
引理 deleteEdges_mono
  条件: (h : G <= H)
  结论: G.deleteEdges s <= H.deleteEdges s
  证明: sdiff_le_sdiff_right h

Depends on / 依赖: sdiff_le_sdiff_right
-/
lemma deleteEdges_mono (h : G <= H) : G.deleteEdges s <= H.deleteEdges s := sdiff_le_sdiff_right h

/--
lemma `deleteEdges_eq_self` / 引理 `deleteEdges_eq_self`

English:
lemma deleteEdges_eq_self
  statement: G.deleteEdges s = G ↔ Disjoint G.edgeSet s
  proof: by
  rw [deleteEdges]; rw [sdiff_eq_left]; rw [disjoint_fromEdgeSet]

中文:
引理 deleteEdges_eq_self
  结论: G.deleteEdges s = G ↔ Disjoint G.edgeSet s
  证明: by
  rw [deleteEdges]; rw [sdiff_eq_left]; rw [disjoint_fromEdgeSet]
-/
@[simp] lemma deleteEdges_eq_self : G.deleteEdges s = G ↔ Disjoint G.edgeSet s := by
  rw [deleteEdges]; rw [sdiff_eq_left]; rw [disjoint_fromEdgeSet]

/--
theorem `deleteEdges_eq_inter_edgeSet` / 定理 `deleteEdges_eq_inter_edgeSet`

English:
theorem deleteEdges_eq_inter_edgeSet
  given: (s : Set (Sym2 V))
  proof: by
  ext
  simp +contextual [imp_false]

中文:
定理 deleteEdges_eq_inter_edgeSet
  条件: (s : 集合 (Sym2 V))
  证明: by
  ext
  simp +contextual [imp_false]

Depends on / 依赖: contextual, imp_false
-/
theorem deleteEdges_eq_inter_edgeSet (s : Set (Sym2 V)) :
    G.deleteEdges s = G.deleteEdges (s inter G.edgeSet) := by
  ext
  simp +contextual [imp_false]

/--
lemma `deleteEdges_of_subset_diagSet` / 引理 `deleteEdges_of_subset_diagSet`

English:
lemma deleteEdges_of_subset_diagSet
  given: (G : SimpleGraph V) (hs : s subseteq Sym2.diagSet)
  proof: by ext u v; simpa using (·.ne <| hs ·)

中文:
引理 deleteEdges_of_subset_diagSet
  条件: (G : 简单图 V) (hs : s subseteq Sym2.diagSet)
  证明: by ext u v; simpa using (·.ne <| hs ·)
-/
@[simp] lemma deleteEdges_of_subset_diagSet (G : SimpleGraph V) (hs : s subseteq Sym2.diagSet) :
    G.deleteEdges s = G := by ext u v; simpa using (·.ne <| hs ·)

/--
theorem `deleteEdges_sdiff_eq_of_le` / 定理 `deleteEdges_sdiff_eq_of_le`

English:
theorem deleteEdges_sdiff_eq_of_le
  given: {H : SimpleGraph V} (h : H <= G)
  proof: by
  rw [← edgeSet_sdiff]; rw [deleteEdges_edgeSet]; rw [sdiff_sdiff_eq_self h]

@[simp]

中文:
定理 deleteEdges_sdiff_eq_of_le
  条件: {H : 简单图 V} (h : H <= G)
  证明: by
  rw [← edgeSet_sdiff]; rw [deleteEdges_edgeSet]; rw [sdiff_sdiff_eq_self h]

@[simp]

Depends on / 依赖: deleteEdges_edgeSet, edgeSet_sdiff, sdiff_sdiff_eq_self
-/
theorem deleteEdges_sdiff_eq_of_le {H : SimpleGraph V} (h : H <= G) :
    G.deleteEdges (G.edgeSet \ H.edgeSet) = H := by
  rw [← edgeSet_sdiff]; rw [deleteEdges_edgeSet]; rw [sdiff_sdiff_eq_self h]

@[simp]
/--
theorem `edgeSet_deleteEdges` / 定理 `edgeSet_deleteEdges`

English:
theorem edgeSet_deleteEdges
  given: (s : Set (Sym2 V))
  statement: (G.deleteEdges s).edgeSet = G.edgeSet \ s
  proof: by
  simp [deleteEdges]

中文:
定理 edgeSet_deleteEdges
  条件: (s : 集合 (Sym2 V))
  结论: (G.deleteEdges s).edgeSet = G.edgeSet \ s
  证明: by
  simp [deleteEdges]

Depends on / 依赖: deleteEdges
-/
theorem edgeSet_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s := by
  simp [deleteEdges]

/--
theorem `edgeFinset_deleteEdges` / 定理 `edgeFinset_deleteEdges`

English:
theorem edgeFinset_deleteEdges
  statement: [DecidableEq V] [Fintype G.edgeSet] (s : Finset (Sym2 V))
  proof: by
  ext e
  simp [edgeSet_deleteEdges]

中文:
定理 edgeFinset_deleteEdges
  结论: [DecidableEq V] [有限类型 G.edgeSet] (s : 有限集 (Sym2 V))
  证明: by
  ext e
  simp [edgeSet_deleteEdges]
-/
@[simp] theorem edgeFinset_deleteEdges [DecidableEq V] [Fintype G.edgeSet] (s : Finset (Sym2 V))
    [Fintype (G.deleteEdges s).edgeSet] :
    (G.deleteEdges s).edgeFinset = G.edgeFinset \ s := by
  ext e
  simp [edgeSet_deleteEdges]

/--
lemma `deleteEdges_sup` / 引理 `deleteEdges_sup`

English:
lemma deleteEdges_sup
  given: (G H : SimpleGraph V) (s : Set (Sym2 V))
  proof: sup_sdiff

中文:
引理 deleteEdges_sup
  条件: (G H : 简单图 V) (s : 集合 (Sym2 V))
  证明: sup_sdiff
-/
@[simp] lemma deleteEdges_sup (G H : SimpleGraph V) (s : Set (Sym2 V)) :
    (G ⊔ H).deleteEdges s = G.deleteEdges s ⊔ H.deleteEdges s := sup_sdiff

/--
lemma `deleteEdges_fromEdgeSet` / 引理 `deleteEdges_fromEdgeSet`

English:
lemma deleteEdges_fromEdgeSet
  given: (s t : Set (Sym2 V))
  proof: by ext; simp +contextual

中文:
引理 deleteEdges_fromEdgeSet
  条件: (s t : 集合 (Sym2 V))
  证明: by ext; simp +contextual
-/
@[simp] lemma deleteEdges_fromEdgeSet (s t : Set (Sym2 V)) :
    (fromEdgeSet s).deleteEdges t = fromEdgeSet (s \ t) := by ext; simp +contextual

/--
lemma `deleteEdges_eq_bot` / 引理 `deleteEdges_eq_bot`

English:
lemma deleteEdges_eq_bot
  statement: G.deleteEdges s = ⊥ ↔ G.edgeSet subseteq s
  proof: by simp [deleteEdges]

中文:
引理 deleteEdges_eq_bot
  结论: G.deleteEdges s = ⊥ ↔ G.edgeSet subseteq s
  证明: by simp [deleteEdges]
-/
@[simp] lemma deleteEdges_eq_bot : G.deleteEdges s = ⊥ ↔ G.edgeSet subseteq s := by simp [deleteEdges]

end DeleteEdges

section DeleteIncidenceSet

/--
Definition of `deleteIncidenceSet` / `deleteIncidenceSet` 的定义

English:
definition deleteIncidenceSet
  signature: (G : SimpleGraph V) (x : V)
  body: G.deleteEdges (G.incidenceSet x)

中文:
定义 deleteIncidenceSet
  签名: (G : 简单图 V) (x : V)
  定义体: G.deleteEdges (G.incidenceSet x)

Depends on / 依赖: G.deleteEdges, G.incidenceSet, deleteEdges, incidenceSet
-/
def deleteIncidenceSet (G : SimpleGraph V) (x : V) : SimpleGraph V :=
  G.deleteEdges (G.incidenceSet x)

/--
lemma `deleteIncidenceSet_adj` / 引理 `deleteIncidenceSet_adj`

English:
lemma deleteIncidenceSet_adj
  given: {G : SimpleGraph V} {x v₁ v₂ : V}
  proof: by
  rw [deleteIncidenceSet]; rw [deleteEdges_adj]; rw [mk'_mem_incidenceSet_iff]
  tauto

中文:
引理 deleteIncidenceSet_adj
  条件: {G : 简单图 V} {x v₁ v₂ : V}
  证明: by
  rw [deleteIncidenceSet]; rw [deleteEdges_adj]; rw [mk'_mem_incidenceSet_iff]
  tauto

Depends on / 依赖: _mem_incidenceSet_iff, deleteEdges_adj, deleteIncidenceSet
-/
lemma deleteIncidenceSet_adj {G : SimpleGraph V} {x v₁ v₂ : V} :
    (G.deleteIncidenceSet x).Adj v₁ v₂ ↔ G.Adj v₁ v₂ ∧ v₁ != x ∧ v₂ != x := by
  rw [deleteIncidenceSet]; rw [deleteEdges_adj]; rw [mk'_mem_incidenceSet_iff]
  tauto

/--
lemma `deleteIncidenceSet_le` / 引理 `deleteIncidenceSet_le`

English:
lemma deleteIncidenceSet_le
  given: (G : SimpleGraph V) (x : V)
  statement: G.deleteIncidenceSet x <= G
  proof: deleteEdges_le (G.incidenceSet x)

中文:
引理 deleteIncidenceSet_le
  条件: (G : 简单图 V) (x : V)
  结论: G.deleteIncidenceSet x <= G
  证明: deleteEdges_le (G.incidenceSet x)

Depends on / 依赖: G.incidenceSet, deleteEdges_le, incidenceSet
-/
lemma deleteIncidenceSet_le (G : SimpleGraph V) (x : V) : G.deleteIncidenceSet x <= G :=
  deleteEdges_le (G.incidenceSet x)

/--
lemma `edgeSet_fromEdgeSet_incidenceSet` / 引理 `edgeSet_fromEdgeSet_incidenceSet`

English:
lemma edgeSet_fromEdgeSet_incidenceSet
  given: (G : SimpleGraph V) (x : V)
  proof: by
  rw [edgeSet_fromEdgeSet]; rw [sdiff_eq_left]; rw [← Set.subset_compl_iff_disjoint_right]
  exact (incidenceSet_subset G x).trans G.edgeSet_subset_compl_diagSet

中文:
引理 edgeSet_fromEdgeSet_incidenceSet
  条件: (G : 简单图 V) (x : V)
  证明: by
  rw [edgeSet_fromEdgeSet]; rw [sdiff_eq_left]; rw [← Set.subset_compl_iff_disjoint_right]
  exact (incidenceSet_subset G x).trans G.edgeSet_subset_compl_diagSet

Depends on / 依赖: G.edgeSet_subset_compl_diagSet, Set.subset_compl_iff_disjoint_right, edgeSet_fromEdgeSet, edgeSet_subset_compl_diagSet, incidenceSet_subset, sdiff_eq_left, subset_compl_iff_disjoint_right
-/
lemma edgeSet_fromEdgeSet_incidenceSet (G : SimpleGraph V) (x : V) :
    (fromEdgeSet (G.incidenceSet x)).edgeSet = G.incidenceSet x := by
  rw [edgeSet_fromEdgeSet]; rw [sdiff_eq_left]; rw [← Set.subset_compl_iff_disjoint_right]
  exact (incidenceSet_subset G x).trans G.edgeSet_subset_compl_diagSet

/--
theorem `edgeSet_deleteIncidenceSet` / 定理 `edgeSet_deleteIncidenceSet`

English:
theorem edgeSet_deleteIncidenceSet
  given: (G : SimpleGraph V) (x : V)
  proof: by
  simp_rw [deleteIncidenceSet, deleteEdges, edgeSet_sdiff, edgeSet_fromEdgeSet_incidenceSet]

中文:
定理 edgeSet_deleteIncidenceSet
  条件: (G : 简单图 V) (x : V)
  证明: by
  simp_rw [deleteIncidenceSet, deleteEdges, edgeSet_sdiff, edgeSet_fromEdgeSet_incidenceSet]

Depends on / 依赖: deleteEdges, deleteIncidenceSet, edgeSet_fromEdgeSet_incidenceSet, edgeSet_sdiff, simp_rw
-/
theorem edgeSet_deleteIncidenceSet (G : SimpleGraph V) (x : V) :
    (G.deleteIncidenceSet x).edgeSet = G.edgeSet \ G.incidenceSet x := by
  simp_rw [deleteIncidenceSet, deleteEdges, edgeSet_sdiff, edgeSet_fromEdgeSet_incidenceSet]

/--
theorem `support_deleteIncidenceSet_subset` / 定理 `support_deleteIncidenceSet_subset`

English:
theorem support_deleteIncidenceSet_subset
  given: (G : SimpleGraph V) (x : V)
  proof: fun _ => by simp_rw [mem_support, deleteIncidenceSet_adj]; tauto

中文:
定理 support_deleteIncidenceSet_subset
  条件: (G : 简单图 V) (x : V)
  证明: fun _ => by simp_rw [mem_support, deleteIncidenceSet_adj]; tauto

Depends on / 依赖: deleteIncidenceSet_adj, mem_support, simp_rw
-/
theorem support_deleteIncidenceSet_subset (G : SimpleGraph V) (x : V) :
    (G.deleteIncidenceSet x).support subseteq G.support \ {x} :=
  fun _ => by simp_rw [mem_support, deleteIncidenceSet_adj]; tauto

/--
theorem `induce_deleteIncidenceSet_of_notMem` / 定理 `induce_deleteIncidenceSet_of_notMem`

English:
theorem induce_deleteIncidenceSet_of_notMem
  given: (G : SimpleGraph V) {s : Set V} {x : V} (h : x ∉ s)
  proof: by
  ext v₁ v₂
  simp_rw [comap_adj, Function.Embedding.coe_subtype, deleteIncidenceSet_adj, and_iff_left_iff_imp]
  exact fun _ => ⟨v₁.prop.ne_of_notMem h, v₂.prop.ne_of_notMem h⟩

中文:
定理 induce_deleteIncidenceSet_of_notMem
  条件: (G : 简单图 V) {s : 集合 V} {x : V} (h : x ∉ s)
  证明: by
  ext v₁ v₂
  simp_rw [comap_adj, Function.Embedding.coe_subtype, deleteIncidenceSet_adj, and_iff_left_iff_imp]
  exact fun _ => ⟨v₁.prop.ne_of_notMem h, v₂.prop.ne_of_notMem h⟩

Depends on / 依赖: Embedding, Function, Function.Embedding.coe_subtype, and_iff_left_iff_imp, coe_subtype, comap_adj, deleteIncidenceSet_adj, ne_of_notMem, prop.ne_of_notMem, simp_rw
-/
theorem induce_deleteIncidenceSet_of_notMem (G : SimpleGraph V) {s : Set V} {x : V} (h : x ∉ s) :
    (G.deleteIncidenceSet x).induce s = G.induce s := by
  ext v₁ v₂
  simp_rw [comap_adj, Function.Embedding.coe_subtype, deleteIncidenceSet_adj, and_iff_left_iff_imp]
  exact fun _ => ⟨v₁.prop.ne_of_notMem h, v₂.prop.ne_of_notMem h⟩

variable [Fintype V] [DecidableEq V]

instance {G : SimpleGraph V} [DecidableRel G.Adj] {x : V} :
    DecidableRel (G.deleteIncidenceSet x).Adj :=
inferInstanceAs DecidableRel (G.deleteEdges (G.incidenceSet x)).Adj

/--
theorem `card_edgeFinset_induce_compl_singleton` / 定理 `card_edgeFinset_induce_compl_singleton`

English:
theorem card_edgeFinset_induce_compl_singleton
  given: (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
  proof: by
  have h_notMem : x ∉ ({x}ᶜ : Set V) := Set.notMem_compl_iff.mpr (Set.mem_singleton x)
  simp_rw [edgeFinset, Set.toFinset_card,
    ← G.induce_deleteIncidenceSet_of_notMem h_notMem, ← Set.toFinset_card]
  apply card_edgeFinset_induce_of_support_subset
  trans G.support \ {x}
  · exact support_deleteIncidenceSet_subset G x
  · rw [Set.compl_eq_univ_sdiff]
    exact Set.sdiff_subset_sdiff_left (Set.subset_univ G.support)

中文:
定理 card_edgeFinset_induce_compl_singleton
  条件: (G : 简单图 V) [DecidableRel G.伴随] (x : V)
  证明: by
  have h_notMem : x ∉ ({x}ᶜ : Set V) := Set.notMem_compl_iff.mpr (Set.mem_singleton x)
  simp_rw [edgeFinset, Set.toFinset_card,
    ← G.induce_deleteIncidenceSet_of_notMem h_notMem, ← Set.toFinset_card]
  apply card_edgeFinset_induce_of_support_subset
  trans G.support \ {x}
  · exact support_deleteIncidenceSet_subset G x
  · rw [Set.compl_eq_univ_sdiff]
    exact Set.sdiff_subset_sdiff_left (Set.subset_univ G.support)

Depends on / 依赖: G.induce_deleteIncidenceSet_of_notMem, G.support, Set.compl_eq_univ_sdiff, Set.mem_singleton, Set.notMem_compl_iff.mpr, Set.sdiff_subset_sdiff_left, Set.subset_univ, Set.toFinset_card, card_edgeFinset_induce_of_support_subset, compl_eq_univ_sdiff, edgeFinset, h_notMem, induce_deleteIncidenceSet_of_notMem, mem_singleton, notMem_compl_iff, sdiff_subset_sdiff_left, simp_rw, subset_univ, support, support_deleteIncidenceSet_subset
-/
theorem card_edgeFinset_induce_compl_singleton (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    #(G.induce {x}ᶜ).edgeFinset = #(G.deleteIncidenceSet x).edgeFinset := by
  have h_notMem : x ∉ ({x}ᶜ : Set V) := Set.notMem_compl_iff.mpr (Set.mem_singleton x)
  simp_rw [edgeFinset, Set.toFinset_card,
    ← G.induce_deleteIncidenceSet_of_notMem h_notMem, ← Set.toFinset_card]
  apply card_edgeFinset_induce_of_support_subset
  trans G.support \ {x}
  · exact support_deleteIncidenceSet_subset G x
  · rw [Set.compl_eq_univ_sdiff]
    exact Set.sdiff_subset_sdiff_left (Set.subset_univ G.support)

/--
theorem `edgeFinset_deleteIncidenceSet_eq_sdiff` / 定理 `edgeFinset_deleteIncidenceSet_eq_sdiff`

English:
theorem edgeFinset_deleteIncidenceSet_eq_sdiff
  given: (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
  proof: by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_deleteIncidenceSet x

中文:
定理 edgeFinset_deleteIncidenceSet_eq_sdiff
  条件: (G : 简单图 V) [DecidableRel G.伴随] (x : V)
  证明: by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_deleteIncidenceSet x

Depends on / 依赖: Finset, Finset.coe_injective, G.edgeSet_deleteIncidenceSet, coe_injective, edgeSet_deleteIncidenceSet
-/
theorem edgeFinset_deleteIncidenceSet_eq_sdiff (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset \ G.incidenceFinset x := by
  apply Finset.coe_injective
  push_cast
  exact G.edgeSet_deleteIncidenceSet x

/--
theorem `card_edgeFinset_deleteIncidenceSet` / 定理 `card_edgeFinset_deleteIncidenceSet`

English:
theorem card_edgeFinset_deleteIncidenceSet
  given: (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
  proof: by
  simp_rw [← card_incidenceFinset_eq_degree, ← card_sdiff_of_subset (G.incidenceFinset_subset x),
    edgeFinset_deleteIncidenceSet_eq_sdiff]

中文:
定理 card_edgeFinset_deleteIncidenceSet
  条件: (G : 简单图 V) [DecidableRel G.伴随] (x : V)
  证明: by
  simp_rw [← card_incidenceFinset_eq_degree, ← card_sdiff_of_subset (G.incidenceFinset_subset x),
    edgeFinset_deleteIncidenceSet_eq_sdiff]

Depends on / 依赖: G.incidenceFinset_subset, card_incidenceFinset_eq_degree, card_sdiff_of_subset, edgeFinset_deleteIncidenceSet_eq_sdiff, incidenceFinset_subset, simp_rw
-/
theorem card_edgeFinset_deleteIncidenceSet (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    #(G.deleteIncidenceSet x).edgeFinset = #G.edgeFinset - G.degree x := by
  simp_rw [← card_incidenceFinset_eq_degree, ← card_sdiff_of_subset (G.incidenceFinset_subset x),
    edgeFinset_deleteIncidenceSet_eq_sdiff]

/--
theorem `edgeFinset_deleteIncidenceSet_eq_filter` / 定理 `edgeFinset_deleteIncidenceSet_eq_filter`

English:
theorem edgeFinset_deleteIncidenceSet_eq_filter
  given: (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
  proof: by
  rw [edgeFinset_deleteIncidenceSet_eq_sdiff]; rw [sdiff_eq_filter]
  apply filter_congr
  intro _ h
  rw [incidenceFinset]; rw [Set.mem_toFinset]; rw [incidenceSet]; rw [Set.mem_ofPred_eq]; rw [not_and]; rw [Classical.imp_iff_right_iff]
  left
  rwa [mem_edgeFinset] at h

中文:
定理 edgeFinset_deleteIncidenceSet_eq_filter
  条件: (G : 简单图 V) [DecidableRel G.伴随] (x : V)
  证明: by
  rw [edgeFinset_deleteIncidenceSet_eq_sdiff]; rw [sdiff_eq_filter]
  apply filter_congr
  intro _ h
  rw [incidenceFinset]; rw [Set.mem_toFinset]; rw [incidenceSet]; rw [Set.mem_ofPred_eq]; rw [not_and]; rw [Classical.imp_iff_right_iff]
  left
  rwa [mem_edgeFinset] at h

Depends on / 依赖: Classical, Classical.imp_iff_right_iff, Set.mem_ofPred_eq, Set.mem_toFinset, edgeFinset_deleteIncidenceSet_eq_sdiff, filter_congr, imp_iff_right_iff, incidenceFinset, incidenceSet, mem_edgeFinset, mem_ofPred_eq, mem_toFinset, not_and, sdiff_eq_filter
-/
theorem edgeFinset_deleteIncidenceSet_eq_filter (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (G.deleteIncidenceSet x).edgeFinset = G.edgeFinset.filter (x ∉ ·) := by
  rw [edgeFinset_deleteIncidenceSet_eq_sdiff]; rw [sdiff_eq_filter]
  apply filter_congr
  intro _ h
  rw [incidenceFinset]; rw [Set.mem_toFinset]; rw [incidenceSet]; rw [Set.mem_ofPred_eq]; rw [not_and]; rw [Classical.imp_iff_right_iff]
  left
  rwa [mem_edgeFinset] at h

/--
theorem `card_support_deleteIncidenceSet` / 定理 `card_support_deleteIncidenceSet`

English:
theorem card_support_deleteIncidenceSet
  proof: by
  rw [← Set.singleton_subset_iff]; rw [← Set.toFinset_subset_toFinset] at hx
  simp_rw [← Set.card_singleton x, ← Set.toFinset_card, ← card_sdiff_of_subset hx,
    ← Set.toFinset_sdiff]
  apply card_le_card
  rw [Set.toFinset_subset_toFinset]
  exact G.support_deleteIncidenceSet_subset x

中文:
定理 card_support_deleteIncidenceSet
  证明: by
  rw [← Set.singleton_subset_iff]; rw [← Set.toFinset_subset_toFinset] at hx
  simp_rw [← Set.card_singleton x, ← Set.toFinset_card, ← card_sdiff_of_subset hx,
    ← Set.toFinset_sdiff]
  apply card_le_card
  rw [Set.toFinset_subset_toFinset]
  exact G.support_deleteIncidenceSet_subset x

Depends on / 依赖: G.support_deleteIncidenceSet_subset, Set.card_singleton, Set.singleton_subset_iff, Set.toFinset_card, Set.toFinset_sdiff, Set.toFinset_subset_toFinset, card_le_card, card_sdiff_of_subset, card_singleton, simp_rw, singleton_subset_iff, support_deleteIncidenceSet_subset, toFinset_card, toFinset_sdiff, toFinset_subset_toFinset
-/
theorem card_support_deleteIncidenceSet
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V} (hx : x in G.support) :
    card (G.deleteIncidenceSet x).support <= card G.support - 1 := by
  rw [← Set.singleton_subset_iff]; rw [← Set.toFinset_subset_toFinset] at hx
  simp_rw [← Set.card_singleton x, ← Set.toFinset_card, ← card_sdiff_of_subset hx,
    ← Set.toFinset_sdiff]
  apply card_le_card
  rw [Set.toFinset_subset_toFinset]
  exact G.support_deleteIncidenceSet_subset x

end DeleteIncidenceSet

section DeleteFar

variable {𝕜 : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [Fintype G.edgeSet] {p : SimpleGraph V -> Prop} {r r₁ r₂ : 𝕜}

/--
Definition of `DeleteFar` / `DeleteFar` 的定义

English:
definition DeleteFar
  signature: (p : SimpleGraph V -> Prop) (r : 𝕜)
  body: forall ⦃s⦄, s subseteq G.edgeFinset -> p (G.deleteEdges s) -> r <= #s

中文:
定义 DeleteFar
  签名: (p : 简单图 V -> 命题) (r : 𝕜)
  定义体: forall ⦃s⦄, s subseteq G.edgeFinset -> p (G.deleteEdges s) -> r <= #s

Depends on / 依赖: G.deleteEdges, G.edgeFinset, deleteEdges, edgeFinset, subseteq
-/
def DeleteFar (p : SimpleGraph V -> Prop) (r : 𝕜) : Prop :=
  forall ⦃s⦄, s subseteq G.edgeFinset -> p (G.deleteEdges s) -> r <= #s

variable {G}

/--
theorem `deleteFar_iff` / 定理 `deleteFar_iff`

English:
theorem deleteFar_iff
  given: [Fintype (Sym2 V)]
  proof: by
  classical
  refine ⟨fun h H _ hHG hH => ?_, fun h s hs hG => ?_⟩
  · have := h (sdiff_subset (t := H.edgeFinset))
    simp only [deleteEdges_sdiff_eq_of_le hHG, edgeFinset_mono hHG, card_sdiff_of_subset,
      card_le_card, coe_sdiff, coe_edgeFinset, Nat.cast_sub] at this
    exact this hH
  · classical
    simpa [card_sdiff_of_subset hs, edgeFinset_deleteEdges, -Set.toFinset_card, Nat.cast_sub,
      card_le_card hs] using h (G.deleteEdges_le s) hG

alias ⟨DeleteFar.le_card_sub_card, _⟩ := deleteFar_iff

中文:
定理 deleteFar_iff
  条件: [有限类型 (Sym2 V)]
  证明: by
  classical
  refine ⟨fun h H _ hHG hH => ?_, fun h s hs hG => ?_⟩
  · have := h (sdiff_subset (t := H.edgeFinset))
    simp only [deleteEdges_sdiff_eq_of_le hHG, edgeFinset_mono hHG, card_sdiff_of_subset,
      card_le_card, coe_sdiff, coe_edgeFinset, Nat.cast_sub] at this
    exact this hH
  · classical
    simpa [card_sdiff_of_subset hs, edgeFinset_deleteEdges, -Set.toFinset_card, Nat.cast_sub,
      card_le_card hs] using h (G.deleteEdges_le s) hG

alias ⟨DeleteFar.le_card_sub_card, _⟩ := deleteFar_iff

Depends on / 依赖: G.deleteEdges_le, H.edgeFinset, Nat.cast_sub, Set.toFinset_card, card_le_card, card_sdiff_of_subset, cast_sub, classical, coe_edgeFinset, coe_sdiff, deleteEdges_le, deleteEdges_sdiff_eq_of_le, edgeFinset, edgeFinset_deleteEdges, edgeFinset_mono, sdiff_subset, toFinset_card
-/
theorem deleteFar_iff [Fintype (Sym2 V)] :
    G.DeleteFar p r ↔ forall ⦃H : SimpleGraph _⦄ [DecidableRel H.Adj],
      H <= G -> p H -> r <= #G.edgeFinset - #H.edgeFinset := by
  classical
  refine ⟨fun h H _ hHG hH => ?_, fun h s hs hG => ?_⟩
  · have := h (sdiff_subset (t := H.edgeFinset))
    simp only [deleteEdges_sdiff_eq_of_le hHG, edgeFinset_mono hHG, card_sdiff_of_subset,
      card_le_card, coe_sdiff, coe_edgeFinset, Nat.cast_sub] at this
    exact this hH
  · classical
    simpa [card_sdiff_of_subset hs, edgeFinset_deleteEdges, -Set.toFinset_card, Nat.cast_sub,
      card_le_card hs] using h (G.deleteEdges_le s) hG

alias ⟨DeleteFar.le_card_sub_card, _⟩ := deleteFar_iff

/--
theorem `DeleteFar.mono` / 定理 `DeleteFar.mono`

English:
theorem DeleteFar.mono
  given: (h : G.DeleteFar p r₂) (hr : r₁ <= r₂)
  statement: G.DeleteFar p r₁
  proof: fun _ hs hG =>
hr.trans h hs hG

中文:
定理 DeleteFar.mono
  条件: (h : G.DeleteFar p r₂) (hr : r₁ <= r₂)
  结论: G.DeleteFar p r₁
  证明: fun _ hs hG =>
hr.trans h hs hG
-/
theorem DeleteFar.mono (h : G.DeleteFar p r₂) (hr : r₁ <= r₂) : G.DeleteFar p r₁ := fun _ hs hG =>
hr.trans h hs hG

/--
lemma `DeleteFar.le_card_edgeFinset` / 引理 `DeleteFar.le_card_edgeFinset`

English:
lemma DeleteFar.le_card_edgeFinset
  given: (h : G.DeleteFar p r) (hp : p ⊥)
  statement: r <= #G.edgeFinset
  proof: h subset_rfl (by simpa)

中文:
引理 DeleteFar.le_card_edgeFinset
  条件: (h : G.DeleteFar p r) (hp : p ⊥)
  结论: r <= #G.edgeFinset
  证明: h subset_rfl (by simpa)

Depends on / 依赖: subset_rfl
-/
lemma DeleteFar.le_card_edgeFinset (h : G.DeleteFar p r) (hp : p ⊥) : r <= #G.edgeFinset :=
  h subset_rfl (by simpa)

end DeleteFar

end SimpleGraph
