/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Deletion of edges and vertices

This file defines the deletion of edges and vertices from a graph.

## Main definitions

- `restrict`: the subgraph of `G` restricted to the edges in `F` without
  removing vertices
- `deleteEdges`: the subgraph of `G` with the edges in `F` deleted
- `induce`: the subgraph of `G` induced by the set `X` of vertices
- `deleteVerts` : the graph obtained from `G` by deleting the set `X` of vertices

## Tags

graphs, edge deletion, vertex deletion
-/

public section

variable {α β : Type*} {x y : α} {e : β} {G H : Graph α β} {F F₀ : Set β} {X : Set α}

open Set Function

namespace Graph

/-- Restrict `G : Graph α β` to the edges in a set `E₀` without removing vertices -/
@[expose, simps (attr := grind =)]
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (G : Graph α β) (E₀ : Set β)
  body: V(G)
  edgeSet := E(G) inter E₀
  IsLink e x y := e in E₀ ∧ G.IsLink e x y
  isLink_symm e he := { symm x y h := ⟨h.1, h.2.symm⟩ }
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.2.left_eq_or_eq h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h => by simp [G.exists_isLink_of_mem_edgeSet h.1, h.2],
  

中文:
定义 restrict
  签名: (G : 图 α β) (E₀ : 集合 β)
  定义体: V(G)
  edgeSet := E(G) inter E₀
  IsLink e x y := e in E₀ ∧ G.IsLink e x y
  isLink_symm e he := { symm x y h := ⟨h.1, h.2.symm⟩ }
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.2.left_eq_or_eq h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h => by simp [G.exists_isLink_of_mem_edgeSet h.1, h.2],
  
-/
def restrict (G : Graph α β) (E₀ : Set β) : Graph α β where
  vertexSet := V(G)
  edgeSet := E(G) inter E₀
  IsLink e x y := e in E₀ ∧ G.IsLink e x y
  isLink_symm e he := { symm x y h := ⟨h.1, h.2.symm⟩ }
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.2.left_eq_or_eq h'.2
  edge_mem_iff_exists_isLink e := ⟨fun h => by simp [G.exists_isLink_of_mem_edgeSet h.1, h.2],
    fun ⟨x, y, h⟩ => ⟨h.2.edge_mem, h.1⟩⟩

@[simp]
/--
lemma `restrict_le` / 引理 `restrict_le`

English:
lemma restrict_le
  given: {E₀ : Set β}
  statement: G.restrict E₀ <= G where
  proof: le_rfl
  isLink_mono := by simp

@[simp]

中文:
引理 restrict_le
  条件: {E₀ : 集合 β}
  结论: G.restrict E₀ <= G where
  证明: le_rfl
  isLink_mono := by simp

@[simp]

Depends on / 依赖: le_rfl
-/
lemma restrict_le {E₀ : Set β} : G.restrict E₀ <= G where
  vertexSet_mono := le_rfl
  isLink_mono := by simp

@[simp]
/--
lemma `restrict_eq_self_iff` / 引理 `restrict_eq_self_iff`

English:
lemma restrict_eq_self_iff
  given: (G : Graph α β) (E₀ : Set β)
  statement: G.restrict E₀ = G ↔ E(G) subseteq E₀
  proof: ⟨fun h => by simpa using h.ge.edgeSet_mono,
    fun h => (Compatible.of_le restrict_le).ext (by simp) (by simpa)⟩

@[simp]

中文:
引理 restrict_eq_self_iff
  条件: (G : 图 α β) (E₀ : 集合 β)
  结论: G.restrict E₀ = G ↔ E(G) subseteq E₀
  证明: ⟨fun h => by simpa using h.ge.edgeSet_mono,
    fun h => (Compatible.of_le restrict_le).ext (by simp) (by simpa)⟩

@[simp]

Depends on / 依赖: Compatible, Compatible.of_le, edgeSet_mono, h.ge.edgeSet_mono, of_le, restrict_le
-/
lemma restrict_eq_self_iff (G : Graph α β) (E₀ : Set β) : G.restrict E₀ = G ↔ E(G) subseteq E₀ :=
  ⟨fun h => by simpa using h.ge.edgeSet_mono,
    fun h => (Compatible.of_le restrict_le).ext (by simp) (by simpa)⟩

@[simp]
/--
lemma `restrict_self` / 引理 `restrict_self`

English:
lemma restrict_self
  given: (G : Graph α β)
  statement: G.restrict E(G) = G
  proof: (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl (by simp)

@[simp]

中文:
引理 restrict_self
  条件: (G : 图 α β)
  结论: G.restrict E(G) = G
  证明: (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl (by simp)

@[simp]

Depends on / 依赖: Compatible, Compatible.of_le_le, of_le_le
-/
lemma restrict_self (G : Graph α β) : G.restrict E(G) = G :=
  (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl (by simp)

@[simp]
/--
lemma `restrict_edgeSet_inter` / 引理 `restrict_edgeSet_inter`

English:
lemma restrict_edgeSet_inter
  given: (G : Graph α β) (F : Set β)
  statement: G.restrict (E(G) inter F) = G.restrict F
  proof: (Compatible.of_le_le (G := G) (by simp) (by simp)).ext (by simp) (by simp)

@[simp]

中文:
引理 restrict_edgeSet_inter
  条件: (G : 图 α β) (F : 集合 β)
  结论: G.restrict (E(G) inter F) = G.restrict F
  证明: (Compatible.of_le_le (G := G) (by simp) (by simp)).ext (by simp) (by simp)

@[simp]

Depends on / 依赖: Compatible, Compatible.of_le_le, of_le_le
-/
lemma restrict_edgeSet_inter (G : Graph α β) (F : Set β) : G.restrict (E(G) inter F) = G.restrict F :=
  (Compatible.of_le_le (G := G) (by simp) (by simp)).ext (by simp) (by simp)

@[simp]
/--
lemma `restrict_inter_edgeSet` / 引理 `restrict_inter_edgeSet`

English:
lemma restrict_inter_edgeSet
  given: (G : Graph α β) (F : Set β)
  proof: by
  rw [inter_comm]; rw [restrict_edgeSet_inter]

@[gcongr]

中文:
引理 restrict_inter_edgeSet
  条件: (G : 图 α β) (F : 集合 β)
  证明: by
  rw [inter_comm]; rw [restrict_edgeSet_inter]

@[gcongr]

Depends on / 依赖: inter_comm, restrict_edgeSet_inter
-/
lemma restrict_inter_edgeSet (G : Graph α β) (F : Set β) :
    G.restrict (F inter E(G)) = G.restrict F := by
  rw [inter_comm]; rw [restrict_edgeSet_inter]

@[gcongr]
/--
lemma `restrict_mono_left` / 引理 `restrict_mono_left`

English:
lemma restrict_mono_left
  given: (h : H <= G) (F : Set β)
  statement: H.restrict F <= G.restrict F
  proof: by
  refine (Compatible.of_le_le (G := G) (restrict_le.trans h) (by simp)).le_iff.mpr ⟨?_, ?_⟩
  · simpa using h.vertexSet_mono
  simp [inter_subset_left.trans h.edgeSet_mono]

@[gcongr]

中文:
引理 restrict_mono_left
  条件: (h : H <= G) (F : 集合 β)
  结论: H.restrict F <= G.restrict F
  证明: by
  refine (Compatible.of_le_le (G := G) (restrict_le.trans h) (by simp)).le_iff.mpr ⟨?_, ?_⟩
  · simpa using h.vertexSet_mono
  simp [inter_subset_left.trans h.edgeSet_mono]

@[gcongr]

Depends on / 依赖: Compatible, Compatible.of_le_le, edgeSet_mono, h.edgeSet_mono, h.vertexSet_mono, inter_subset_left, inter_subset_left.trans, le_iff, le_iff.mpr, of_le_le, restrict_le, restrict_le.trans, vertexSet_mono
-/
lemma restrict_mono_left (h : H <= G) (F : Set β) : H.restrict F <= G.restrict F := by
  refine (Compatible.of_le_le (G := G) (restrict_le.trans h) (by simp)).le_iff.mpr ⟨?_, ?_⟩
  · simpa using h.vertexSet_mono
  simp [inter_subset_left.trans h.edgeSet_mono]

@[gcongr]
/--
lemma `restrict_mono_right` / 引理 `restrict_mono_right`

English:
lemma restrict_mono_right
  given: (G : Graph α β) (hss : F₀ subseteq F)
  statement: G.restrict F₀ <= G.restrict F where
  proof: subset_rfl
  isLink_mono _ _ _ := fun h => ⟨hss h.1, h.2⟩

@[simp, grind =]

中文:
引理 restrict_mono_right
  条件: (G : 图 α β) (hss : F₀ subseteq F)
  结论: G.restrict F₀ <= G.restrict F where
  证明: subset_rfl
  isLink_mono _ _ _ := fun h => ⟨hss h.1, h.2⟩

@[simp, grind =]

Depends on / 依赖: subset_rfl
-/
lemma restrict_mono_right (G : Graph α β) (hss : F₀ subseteq F) : G.restrict F₀ <= G.restrict F where
  vertexSet_mono := subset_rfl
  isLink_mono _ _ _ := fun h => ⟨hss h.1, h.2⟩

@[simp, grind =]
/--
lemma `restrict_inc` / 引理 `restrict_inc`

English:
lemma restrict_inc
  statement: (G.restrict F).Inc e x ↔ G.Inc e x ∧ e in F
  proof: by
  simp [Inc, and_comm]

@[simp, grind =]

中文:
引理 restrict_inc
  结论: (G.restrict F).Inc e x ↔ G.Inc e x ∧ e in F
  证明: by
  simp [Inc, and_comm]

@[simp, grind =]

Depends on / 依赖: and_comm
-/
lemma restrict_inc : (G.restrict F).Inc e x ↔ G.Inc e x ∧ e in F := by
  simp [Inc, and_comm]

@[simp, grind =]
/--
lemma `restrict_isLoopAt` / 引理 `restrict_isLoopAt`

English:
lemma restrict_isLoopAt
  statement: (G.restrict F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e in F
  proof: by
  simp [← isLink_self_iff, and_comm]

@[simp]

中文:
引理 restrict_isLoopAt
  结论: (G.restrict F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e in F
  证明: by
  simp [← isLink_self_iff, and_comm]

@[simp]

Depends on / 依赖: and_comm, isLink_self_iff
-/
lemma restrict_isLoopAt : (G.restrict F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e in F := by
  simp [← isLink_self_iff, and_comm]

@[simp]
/--
lemma `restrict_restrict` / 引理 `restrict_restrict`

English:
lemma restrict_restrict
  given: (G : Graph α β) (F₁ F₂ : Set β)
  proof: by
  refine (Compatible.of_le_le (G := G) (restrict_le.trans (by simp)) (by simp)).ext (by simp) ?_
  simp only [edgeSet_restrict]
  rw [← inter_assoc]; rw [inter_comm _ F₂]

中文:
引理 restrict_restrict
  条件: (G : 图 α β) (F₁ F₂ : 集合 β)
  证明: by
  refine (Compatible.of_le_le (G := G) (restrict_le.trans (by simp)) (by simp)).ext (by simp) ?_
  simp only [edgeSet_restrict]
  rw [← inter_assoc]; rw [inter_comm _ F₂]

Depends on / 依赖: Compatible, Compatible.of_le_le, edgeSet_restrict, inter_assoc, inter_comm, of_le_le, restrict_le, restrict_le.trans
-/
lemma restrict_restrict (G : Graph α β) (F₁ F₂ : Set β) :
    (G.restrict F₁).restrict F₂ = G.restrict (F₁ inter F₂) := by
  refine (Compatible.of_le_le (G := G) (restrict_le.trans (by simp)) (by simp)).ext (by simp) ?_
  simp only [edgeSet_restrict]
  rw [← inter_assoc]; rw [inter_comm _ F₂]

/-- Delete a set `F` of edges from `G`. This is a special case of `restrict`,
but we define it with `copy` so that the edge set is definitionally equal to `E(G) \ F`. -/
@[expose, simps! (attr := grind =)]
/--
Definition of `deleteEdges` / `deleteEdges` 的定义

English:
definition deleteEdges
  signature: (G : Graph α β) (F : Set β)
  body: (G.restrict (E(G) \ F)).copy (edgeSet := E(G) \ F)
  (IsLink := fun e x y => G.IsLink e x y ∧ e ∉ F) rfl (by simp)
  (fun e x y => by
    simp only [restrict_isLink, mem_sdiff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ => h.edge_mem)

@[simp]

中文:
定义 deleteEdges
  签名: (G : 图 α β) (F : 集合 β)
  定义体: (G.restrict (E(G) \ F)).copy (edgeSet := E(G) \ F)
  (IsLink := fun e x y => G.IsLink e x y ∧ e ∉ F) rfl (by simp)
  (fun e x y => by
    simp only [restrict_isLink, mem_sdiff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ => h.edge_mem)

@[simp]

Depends on / 依赖: G.IsLink, G.restrict, IsLink, and_comm, and_congr_left_iff, and_iff_left_iff_imp, edgeSet, edge_mem, h.edge_mem, mem_sdiff, restrict, restrict_isLink
-/
def deleteEdges (G : Graph α β) (F : Set β) : Graph α β :=
  (G.restrict (E(G) \ F)).copy (edgeSet := E(G) \ F)
  (IsLink := fun e x y => G.IsLink e x y ∧ e ∉ F) rfl (by simp)
  (fun e x y => by
    simp only [restrict_isLink, mem_sdiff, and_comm, and_congr_left_iff, and_iff_left_iff_imp]
    exact fun h _ => h.edge_mem)

@[simp]
/--
lemma `restrict_edgeSet_sdiff_eq_deleteEdges` / 引理 `restrict_edgeSet_sdiff_eq_deleteEdges`

English:
lemma restrict_edgeSet_sdiff_eq_deleteEdges
  given: (G : Graph α β) (F : Set β)
  proof: copy_eq ..

@[deprecated (since := "2026-06-03")]
alias restrict_edgeSet_diff_eq_deleteEdges := restrict_edgeSet_sdiff_eq_deleteEdges

@[simp]

中文:
引理 restrict_edgeSet_sdiff_eq_deleteEdges
  条件: (G : 图 α β) (F : 集合 β)
  证明: copy_eq ..

@[deprecated (since := "2026-06-03")]
alias restrict_edgeSet_diff_eq_deleteEdges := restrict_edgeSet_sdiff_eq_deleteEdges

@[simp]

Depends on / 依赖: copy_eq
-/
lemma restrict_edgeSet_sdiff_eq_deleteEdges (G : Graph α β) (F : Set β) :
.symm G.restrict (E(G) \ F) = G.deleteEdges F := copy_eq ..

@[deprecated (since := "2026-06-03")]
alias restrict_edgeSet_diff_eq_deleteEdges := restrict_edgeSet_sdiff_eq_deleteEdges

@[simp]
/--
lemma `deleteEdges_le` / 引理 `deleteEdges_le`

English:
lemma deleteEdges_le
  statement: G.deleteEdges F <= G
  proof: by
  simp [← restrict_edgeSet_sdiff_eq_deleteEdges]

中文:
引理 deleteEdges_le
  结论: G.deleteEdges F <= G
  证明: by
  simp [← restrict_edgeSet_sdiff_eq_deleteEdges]

Depends on / 依赖: restrict_edgeSet_sdiff_eq_deleteEdges
-/
lemma deleteEdges_le : G.deleteEdges F <= G := by
  simp [← restrict_edgeSet_sdiff_eq_deleteEdges]

/--
lemma `restrict_eq_deleteEdges` / 引理 `restrict_eq_deleteEdges`

English:
lemma restrict_eq_deleteEdges
  given: (G : Graph α β) (F : Set β)
  proof: (Compatible.of_le_le restrict_le deleteEdges_le).ext rfl (by simp)

@[simp, grind =]

中文:
引理 restrict_eq_deleteEdges
  条件: (G : 图 α β) (F : 集合 β)
  证明: (Compatible.of_le_le restrict_le deleteEdges_le).ext rfl (by simp)

@[simp, grind =]

Depends on / 依赖: Compatible, Compatible.of_le_le, deleteEdges_le, of_le_le, restrict_le
-/
lemma restrict_eq_deleteEdges (G : Graph α β) (F : Set β) :
    G.restrict F = G.deleteEdges (E(G) \ F) :=
  (Compatible.of_le_le restrict_le deleteEdges_le).ext rfl (by simp)

@[simp, grind =]
/--
lemma `deleteEdges_empty` / 引理 `deleteEdges_empty`

English:
lemma deleteEdges_empty
  statement: G.deleteEdges ∅ = G
  proof: by
  simp [← restrict_edgeSet_sdiff_eq_deleteEdges]

@[gcongr]

中文:
引理 deleteEdges_empty
  结论: G.deleteEdges ∅ = G
  证明: by
  simp [← restrict_edgeSet_sdiff_eq_deleteEdges]

@[gcongr]

Depends on / 依赖: restrict_edgeSet_sdiff_eq_deleteEdges
-/
lemma deleteEdges_empty : G.deleteEdges ∅ = G := by
  simp [← restrict_edgeSet_sdiff_eq_deleteEdges]

@[gcongr]
/--
lemma `deleteEdges_mono_left` / 引理 `deleteEdges_mono_left`

English:
lemma deleteEdges_mono_left
  given: (h : H <= G) (F : Set β)
  statement: H.deleteEdges F <= G.deleteEdges F
  proof: by
  simp_rw [← restrict_edgeSet_sdiff_eq_deleteEdges]
  refine (restrict_mono_left h (E(H) \ F)).trans (G.restrict_mono_right ?_)
  exact sdiff_subset_sdiff_left h.edgeSet_mono

@[simp, grind =]

中文:
引理 deleteEdges_mono_left
  条件: (h : H <= G) (F : 集合 β)
  结论: H.deleteEdges F <= G.deleteEdges F
  证明: by
  simp_rw [← restrict_edgeSet_sdiff_eq_deleteEdges]
  refine (restrict_mono_left h (E(H) \ F)).trans (G.restrict_mono_right ?_)
  exact sdiff_subset_sdiff_left h.edgeSet_mono

@[simp, grind =]

Depends on / 依赖: G.restrict_mono_right, edgeSet_mono, h.edgeSet_mono, restrict_edgeSet_sdiff_eq_deleteEdges, restrict_mono_left, restrict_mono_right, sdiff_subset_sdiff_left, simp_rw
-/
lemma deleteEdges_mono_left (h : H <= G) (F : Set β) : H.deleteEdges F <= G.deleteEdges F := by
  simp_rw [← restrict_edgeSet_sdiff_eq_deleteEdges]
  refine (restrict_mono_left h (E(H) \ F)).trans (G.restrict_mono_right ?_)
  exact sdiff_subset_sdiff_left h.edgeSet_mono

@[simp, grind =]
/--
lemma `deleteEdges_inc` / 引理 `deleteEdges_inc`

English:
lemma deleteEdges_inc
  statement: (G.deleteEdges F).Inc e x ↔ G.Inc e x ∧ e ∉ F
  proof: by
  simp [Inc, and_comm]

@[simp, grind =]

中文:
引理 deleteEdges_inc
  结论: (G.deleteEdges F).Inc e x ↔ G.Inc e x ∧ e ∉ F
  证明: by
  simp [Inc, and_comm]

@[simp, grind =]

Depends on / 依赖: and_comm
-/
lemma deleteEdges_inc : (G.deleteEdges F).Inc e x ↔ G.Inc e x ∧ e ∉ F := by
  simp [Inc, and_comm]

@[simp, grind =]
/--
lemma `deleteEdges_isLoopAt` / 引理 `deleteEdges_isLoopAt`

English:
lemma deleteEdges_isLoopAt
  statement: (G.deleteEdges F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∉ F
  proof: by
  simp only [← restrict_edgeSet_sdiff_eq_deleteEdges, restrict_isLoopAt, mem_sdiff,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ => h.edge_mem

@[simp]

中文:
引理 deleteEdges_isLoopAt
  结论: (G.deleteEdges F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∉ F
  证明: by
  simp only [← restrict_edgeSet_sdiff_eq_deleteEdges, restrict_isLoopAt, mem_sdiff,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ => h.edge_mem

@[simp]

Depends on / 依赖: and_congr_right_iff, and_iff_right_iff_imp, edge_mem, h.edge_mem, mem_sdiff, restrict_edgeSet_sdiff_eq_deleteEdges, restrict_isLoopAt
-/
lemma deleteEdges_isLoopAt : (G.deleteEdges F).IsLoopAt e x ↔ G.IsLoopAt e x ∧ e ∉ F := by
  simp only [← restrict_edgeSet_sdiff_eq_deleteEdges, restrict_isLoopAt, mem_sdiff,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ => h.edge_mem

@[simp]
/--
lemma `deleteEdges_deleteEdges` / 引理 `deleteEdges_deleteEdges`

English:
lemma deleteEdges_deleteEdges
  given: (G : Graph α β) (F₁ F₂ : Set β)
  proof: by
  simp only [← restrict_edgeSet_sdiff_eq_deleteEdges, sdiff_eq_compl_inter, restrict_inter_edgeSet,
    edgeSet_restrict, restrict_restrict, compl_union]
  rw [← inter_comm]; rw [inter_comm F₁ᶜ]; rw [inter_assoc]; rw [inter_assoc]; rw [inter_self]; rw [inter_comm]; rw [inter_assoc]; rw [inter_com

中文:
引理 deleteEdges_deleteEdges
  条件: (G : 图 α β) (F₁ F₂ : 集合 β)
  证明: by
  simp only [← restrict_edgeSet_sdiff_eq_deleteEdges, sdiff_eq_compl_inter, restrict_inter_edgeSet,
    edgeSet_restrict, restrict_restrict, compl_union]
  rw [← inter_comm]; rw [inter_comm F₁ᶜ]; rw [inter_assoc]; rw [inter_assoc]; rw [inter_self]; rw [inter_comm]; rw [inter_assoc]; rw [inter_com

Depends on / 依赖: compl_union, edgeSet_restrict, inter_assoc, inter_comm, inter_self, restrict_edgeSet_sdiff_eq_deleteEdges, restrict_inter_edgeSet, restrict_restrict, sdiff_eq_compl_inter
-/
lemma deleteEdges_deleteEdges (G : Graph α β) (F₁ F₂ : Set β) :
    (G.deleteEdges F₁).deleteEdges F₂ = G.deleteEdges (F₁ union F₂) := by
  simp only [← restrict_edgeSet_sdiff_eq_deleteEdges, sdiff_eq_compl_inter, restrict_inter_edgeSet,
    edgeSet_restrict, restrict_restrict, compl_union]
  rw [← inter_comm]; rw [inter_comm F₁ᶜ]; rw [inter_assoc]; rw [inter_assoc]; rw [inter_self]; rw [inter_comm]; rw [inter_assoc]; rw [inter_comm]; rw [restrict_inter_edgeSet]; rw [inter_comm]

/-- The subgraph of `G` induced by a set `X` of vertices.
The edges are the edges of `G` with both ends in `X`.
(`X` is not required to be a subset of `V(G)` for this definition to work,
even though this is the standard use case) -/
@[expose, simps! (attr := grind =) vertexSet isLink]
/--
Definition of `induce` / `induce` 的定义

English:
definition induce
  signature: (G : Graph α β) (X : Set α)
  body: X
  IsLink e x y := G.IsLink e x y ∧ x in X ∧ y in X
  isLink_symm := by simp +contextual [symm_def, G.isLink_comm]
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1

中文:
定义 induce
  签名: (G : 图 α β) (X : 集合 α)
  定义体: X
  IsLink e x y := G.IsLink e x y ∧ x in X ∧ y in X
  isLink_symm := by simp +contextual [symm_def, G.isLink_comm]
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1
-/
protected def induce (G : Graph α β) (X : Set α) : Graph α β where
  vertexSet := X
  IsLink e x y := G.IsLink e x y ∧ x in X ∧ y in X
  isLink_symm := by simp +contextual [symm_def, G.isLink_comm]
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.1.left_eq_or_eq h'.1

/--
lemma `induce_le` / 引理 `induce_le`

English:
lemma induce_le
  given: (hX : X subseteq V(G))
  statement: G.induce X <= G
  proof: ⟨hX, fun _ _ _ h => h.1⟩

@[simp, grind =]

中文:
引理 induce_le
  条件: (hX : X subseteq V(G))
  结论: G.induce X <= G
  证明: ⟨hX, fun _ _ _ h => h.1⟩

@[simp, grind =]
-/
lemma induce_le (hX : X subseteq V(G)) : G.induce X <= G := ⟨hX, fun _ _ _ h => h.1⟩

@[simp, grind =]
/--
lemma `induce_le_iff` / 引理 `induce_le_iff`

English:
lemma induce_le_iff
  statement: G.induce X <= G ↔ X subseteq V(G)
  proof: ⟨(·.vertexSet_mono), induce_le⟩

中文:
引理 induce_le_iff
  结论: G.induce X <= G ↔ X subseteq V(G)
  证明: ⟨(·.vertexSet_mono), induce_le⟩

Depends on / 依赖: induce_le, vertexSet_mono
-/
lemma induce_le_iff : G.induce X <= G ↔ X subseteq V(G) := ⟨(·.vertexSet_mono), induce_le⟩

/--
lemma `edgeSet_induce` / 引理 `edgeSet_induce`

English:
lemma edgeSet_induce
  given: (G : Graph α β) (X : Set α)
  proof: rfl

@[simp, grind =]

中文:
引理 edgeSet_induce
  条件: (G : 图 α β) (X : 集合 α)
  证明: rfl

@[simp, grind =]
-/
lemma edgeSet_induce (G : Graph α β) (X : Set α) :
    E(G.induce X) = {e | exists x y, G.IsLink e x y ∧ x in X ∧ y in X} := rfl

@[simp, grind =]
/--
lemma `induce_vertexSet` / 引理 `induce_vertexSet`

English:
lemma induce_vertexSet
  given: (G : Graph α β)
  statement: G.induce V(G) = G
  proof: by
refine (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl Set.ext fun e =>
    ⟨fun ⟨_, _, h⟩ => h.1.edge_mem, fun h => ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, h.left_mem, h.right_mem⟩

中文:
引理 induce_vertexSet
  条件: (G : 图 α β)
  结论: G.induce V(G) = G
  证明: by
refine (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl Set.ext fun e =>
    ⟨fun ⟨_, _, h⟩ => h.1.edge_mem, fun h => ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, h.left_mem, h.right_mem⟩

Depends on / 依赖: Compatible, Compatible.of_le_le, Set.ext, edge_mem, exists_isLink_of_mem_edgeSet, h.left_mem, h.right_mem, left_mem, of_le_le, right_mem
-/
lemma induce_vertexSet (G : Graph α β) : G.induce V(G) = G := by
refine (Compatible.of_le_le (G := G) (by simp) (by simp)).ext rfl Set.ext fun e =>
    ⟨fun ⟨_, _, h⟩ => h.1.edge_mem, fun h => ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet h
  exact ⟨x, y, h, h.left_mem, h.right_mem⟩

/--
Definition of `deleteVerts` / `deleteVerts` 的定义

English:
definition deleteVerts
  signature: (G : Graph α β) (X : Set α)
  body: G.induce (V(G) \ X)

@[simp, grind =]

中文:
定义 deleteVerts
  签名: (G : 图 α β) (X : 集合 α)
  定义体: G.induce (V(G) \ X)

@[simp, grind =]

Depends on / 依赖: G.induce, induce
-/
def deleteVerts (G : Graph α β) (X : Set α) : Graph α β := G.induce (V(G) \ X)

@[simp, grind =]
/--
lemma `vertexSet_deleteVerts` / 引理 `vertexSet_deleteVerts`

English:
lemma vertexSet_deleteVerts
  given: (G : Graph α β) (X : Set α)
  statement: V(G.deleteVerts X) = V(G) \ X
  proof: by
  unfold deleteVerts
  rfl

@[simp, grind =]

中文:
引理 vertexSet_deleteVerts
  条件: (G : 图 α β) (X : 集合 α)
  结论: V(G.deleteVerts X) = V(G) \ X
  证明: by
  unfold deleteVerts
  rfl

@[simp, grind =]

Depends on / 依赖: deleteVerts
-/
lemma vertexSet_deleteVerts (G : Graph α β) (X : Set α) : V(G.deleteVerts X) = V(G) \ X := by
  unfold deleteVerts
  rfl

@[simp, grind =]
/--
lemma `deleteVerts_isLink` / 引理 `deleteVerts_isLink`

English:
lemma deleteVerts_isLink
  given: (G : Graph α β) (X : Set α)
  proof: by
  simp only [deleteVerts, induce_isLink, mem_sdiff, and_congr_right_iff]
  exact fun h => by simp [h.left_mem, h.right_mem]

@[simp]

中文:
引理 deleteVerts_isLink
  条件: (G : 图 α β) (X : 集合 α)
  证明: by
  simp only [deleteVerts, induce_isLink, mem_sdiff, and_congr_right_iff]
  exact fun h => by simp [h.left_mem, h.right_mem]

@[simp]

Depends on / 依赖: Equiv.ulift.symm, StateT, StateT.uliftable, and_congr_right_iff, deleteVerts, h.left_mem, h.right_mem, induce_isLink, left_mem, mem_sdiff, right_mem, uliftable
-/
lemma deleteVerts_isLink (G : Graph α β) (X : Set α) :
    (G.deleteVerts X).IsLink e x y ↔ (G.IsLink e x y ∧ x ∉ X ∧ y ∉ X) := by
  simp only [deleteVerts, induce_isLink, mem_sdiff, and_congr_right_iff]
  exact fun h => by simp [h.left_mem, h.right_mem]

@[simp]
/--
lemma `edgeSet_deleteVerts` / 引理 `edgeSet_deleteVerts`

English:
lemma edgeSet_deleteVerts
  given: (G : Graph α β) (X : Set α)
  proof: by
  simp [edgeSet_eq_setOfPred_exists_isLink]

@[simp, grind =]

中文:
引理 edgeSet_deleteVerts
  条件: (G : 图 α β) (X : 集合 α)
  证明: by
  simp [edgeSet_eq_setOfPred_exists_isLink]

@[simp, grind =]

Depends on / 依赖: edgeSet_eq_setOfPred_exists_isLink
-/
lemma edgeSet_deleteVerts (G : Graph α β) (X : Set α) :
    E(G.deleteVerts X) = {e | exists x y, G.IsLink e x y ∧ x ∉ X ∧ y ∉ X} := by
  simp [edgeSet_eq_setOfPred_exists_isLink]

@[simp, grind =]
/--
lemma `deleteVerts_empty` / 引理 `deleteVerts_empty`

English:
lemma deleteVerts_empty
  given: (G : Graph α β)
  statement: G.deleteVerts (∅ : Set α) = G
  proof: by
  simp [deleteVerts]

中文:
引理 deleteVerts_empty
  条件: (G : 图 α β)
  结论: G.deleteVerts (∅ : 集合 α) = G
  证明: by
  simp [deleteVerts]

Depends on / 依赖: deleteVerts
-/
lemma deleteVerts_empty (G : Graph α β) : G.deleteVerts (∅ : Set α) = G := by
  simp [deleteVerts]

/--
lemma `deleteVerts_le` / 引理 `deleteVerts_le`

English:
lemma deleteVerts_le
  statement: G.deleteVerts X <= G
  proof: G.induce_le sdiff_subset

中文:
引理 deleteVerts_le
  结论: G.deleteVerts X <= G
  证明: G.induce_le sdiff_subset

Depends on / 依赖: Equiv.ulift.symm, ReaderT, ReaderT.uliftable, uliftable
-/
@[simp] lemma deleteVerts_le : G.deleteVerts X <= G := G.induce_le sdiff_subset

end Graph
