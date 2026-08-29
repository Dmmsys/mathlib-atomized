/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Lattice.Nat
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Graph cliques

This file defines cliques in simple graphs.
A clique is a set of vertices that are pairwise adjacent.

## Main declarations

* `SimpleGraph.IsClique`: Predicate for a set of vertices to be a clique.
* `SimpleGraph.IsNClique`: Predicate for a set of vertices to be an `n`-clique.
* `SimpleGraph.cliqueFinset`: Finset of `n`-cliques of a graph.
* `SimpleGraph.CliqueFree`: Predicate for a graph to have no `n`-cliques.
-/

@[expose] public section

open Finset Fintype Function SimpleGraph.Walk

namespace SimpleGraph

variable {α β : Type*} (G H : SimpleGraph α)

/-! ### Cliques -/


section Clique

variable {s t : Set α}

/--
Definition of `IsClique` / `IsClique` 的定义

English:
abbreviation IsClique
  signature: (s : Set α)
  body: s.Pairwise G.Adj

中文:
缩写 IsClique
  签名: (s : 集合 α)
  定义体: s.Pairwise G.Adj

Depends on / 依赖: G.Adj, Pairwise, s.Pairwise
-/
abbrev IsClique (s : Set α) : Prop :=
  s.Pairwise G.Adj

/--
theorem `isClique_iff` / 定理 `isClique_iff`

English:
theorem isClique_iff
  statement: G.IsClique s ↔ s.Pairwise G.Adj
  proof: Iff.rfl

中文:
定理 isClique_iff
  结论: G.IsClique s ↔ s.两两 G.伴随
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isClique_iff : G.IsClique s ↔ s.Pairwise G.Adj :=
  Iff.rfl

/--
lemma `not_isClique_iff` / 引理 `not_isClique_iff`

English:
lemma not_isClique_iff
  statement: ¬ G.IsClique s ↔ exists (v w : s), v != w ∧ ¬ G.Adj v w
  proof: by
  aesop (add simp [isClique_iff, Set.Pairwise])

中文:
引理 not_isClique_iff
  结论: ¬ G.IsClique s ↔ 存在 (v w : s), v != w ∧ ¬ G.伴随 v w
  证明: by
  aesop (add simp [isClique_iff, Set.Pairwise])

Depends on / 依赖: Pairwise, Set.Pairwise, isClique_iff
-/
lemma not_isClique_iff : ¬ G.IsClique s ↔ exists (v w : s), v != w ∧ ¬ G.Adj v w := by
  aesop (add simp [isClique_iff, Set.Pairwise])

variable {G} in
@[simp]
/--
theorem `induce_eq_top` / 定理 `induce_eq_top`

English:
theorem induce_eq_top
  statement: G.induce s = ⊤ ↔ G.IsClique s
  proof: by
  rw [isClique_iff]
  refine ⟨fun h u hu v hv hne => ?_, fun h => ?_⟩
  · simpa [← induce_adj (u := ⟨u, hu⟩) (v := ⟨v, hv⟩), h]
  · ext ⟨v, hv⟩ ⟨w, hw⟩
    simpa using ⟨Adj.ne, h hv hw⟩

中文:
定理 induce_eq_top
  结论: G.induce s = ⊤ ↔ G.IsClique s
  证明: by
  rw [isClique_iff]
  refine ⟨fun h u hu v hv hne => ?_, fun h => ?_⟩
  · simpa [← induce_adj (u := ⟨u, hu⟩) (v := ⟨v, hv⟩), h]
  · ext ⟨v, hv⟩ ⟨w, hw⟩
    simpa using ⟨Adj.ne, h hv hw⟩

Depends on / 依赖: Adj.ne, induce_adj, isClique_iff
-/
theorem induce_eq_top : G.induce s = ⊤ ↔ G.IsClique s := by
  rw [isClique_iff]
  refine ⟨fun h u hu v hv hne => ?_, fun h => ?_⟩
  · simpa [← induce_adj (u := ⟨u, hu⟩) (v := ⟨v, hv⟩), h]
  · ext ⟨v, hv⟩ ⟨w, hw⟩
    simpa using ⟨Adj.ne, h hv hw⟩

/-- A clique is a set of vertices whose induced graph is complete. -/
@[deprecated induce_eq_top (since := "2026-04-23")]
/--
theorem `isClique_iff_induce_eq` / 定理 `isClique_iff_induce_eq`

English:
theorem isClique_iff_induce_eq
  statement: G.IsClique s ↔ G.induce s = ⊤
  proof: induce_eq_top.symm

中文:
定理 isClique_iff_induce_eq
  结论: G.IsClique s ↔ G.induce s = ⊤
  证明: induce_eq_top.symm

Depends on / 依赖: induce_eq_top, induce_eq_top.symm
-/
theorem isClique_iff_induce_eq : G.IsClique s ↔ G.induce s = ⊤ :=
  induce_eq_top.symm

/--
theorem `isClique_iff_isChain_adj` / 定理 `isClique_iff_isChain_adj`

English:
theorem isClique_iff_isChain_adj
  statement: G.IsClique s ↔ IsChain G.Adj s
  proof: by
  simp [IsChain, G.symm.iff]

中文:
定理 isClique_iff_isChain_adj
  结论: G.IsClique s ↔ IsChain G.伴随 s
  证明: by
  simp [IsChain, G.symm.iff]

Depends on / 依赖: G.symm.iff, IsChain
-/
theorem isClique_iff_isChain_adj : G.IsClique s ↔ IsChain G.Adj s := by
  simp [IsChain, G.symm.iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] [DecidableRel G.Adj] {s
  body: decidable_of_iff' _ G.isClique_iff

中文:
实例 [DecidableEq
  签名: α] [DecidableRel G.伴随] {s
  定义体: decidable_of_iff' _ G.isClique_iff

Depends on / 依赖: G.isClique_iff, decidable_of_iff, isClique_iff
-/
instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsClique s) :=
  decidable_of_iff' _ G.isClique_iff

variable {G H} {a b : α}

/--
lemma `isClique_empty` / 引理 `isClique_empty`

English:
lemma isClique_empty
  statement: G.IsClique ∅
  proof: by simp

中文:
引理 isClique_empty
  结论: G.IsClique ∅
  证明: by simp
-/
lemma isClique_empty : G.IsClique ∅ := by simp

/--
lemma `isClique_singleton` / 引理 `isClique_singleton`

English:
lemma isClique_singleton
  given: (a : α)
  statement: G.IsClique {a}
  proof: by simp

中文:
引理 isClique_singleton
  条件: (a : α)
  结论: G.IsClique {a}
  证明: by simp
-/
lemma isClique_singleton (a : α) : G.IsClique {a} := by simp

/--
theorem `IsClique.of_subsingleton` / 定理 `IsClique.of_subsingleton`

English:
theorem IsClique.of_subsingleton
  given: {G : SimpleGraph α} (hs : s.Subsingleton)
  statement: G.IsClique s
  proof: hs.pairwise G.Adj

中文:
定理 IsClique.of_subsingleton
  条件: {G : 简单图 α} (hs : s.子单例)
  结论: G.IsClique s
  证明: hs.pairwise G.Adj

Depends on / 依赖: G.Adj, hs.pairwise, pairwise
-/
theorem IsClique.of_subsingleton {G : SimpleGraph α} (hs : s.Subsingleton) : G.IsClique s :=
  hs.pairwise G.Adj

/--
lemma `isClique_pair` / 引理 `isClique_pair`

English:
lemma isClique_pair
  statement: G.IsClique {a, b} ↔ a != b -> G.Adj a b
  proof: have := G.symm
  Set.pairwise_pair_of_symm

@[simp]

中文:
引理 isClique_pair
  结论: G.IsClique {a, b} ↔ a != b -> G.伴随 a b
  证明: have := G.symm
  Set.pairwise_pair_of_symm

@[simp]

Depends on / 依赖: G.symm, Set.pairwise_pair_of_symm, pairwise_pair_of_symm
-/
lemma isClique_pair : G.IsClique {a, b} ↔ a != b -> G.Adj a b :=
  have := G.symm
  Set.pairwise_pair_of_symm

@[simp]
/--
lemma `isClique_insert` / 引理 `isClique_insert`

English:
lemma isClique_insert
  statement: G.IsClique (insert a s) ↔ G.IsClique s ∧ forall b in s, a != b -> G.Adj a b
  proof: have := G.symm
  Set.pairwise_insert_of_symm

中文:
引理 isClique_insert
  结论: G.IsClique (insert a s) ↔ G.IsClique s ∧ 对任意 b in s, a != b -> G.伴随 a b
  证明: have := G.symm
  Set.pairwise_insert_of_symm

Depends on / 依赖: G.symm, Set.pairwise_insert_of_symm, pairwise_insert_of_symm
-/
lemma isClique_insert : G.IsClique (insert a s) ↔ G.IsClique s ∧ forall b in s, a != b -> G.Adj a b :=
  have := G.symm
  Set.pairwise_insert_of_symm

/--
lemma `isClique_insert_of_notMem` / 引理 `isClique_insert_of_notMem`

English:
lemma isClique_insert_of_notMem
  given: (ha : a ∉ s)
  proof: have := G.symm
  Set.pairwise_insert_of_symm_of_notMem ha

中文:
引理 isClique_insert_of_notMem
  条件: (ha : a ∉ s)
  证明: have := G.symm
  Set.pairwise_insert_of_symm_of_notMem ha

Depends on / 依赖: G.symm, Set.pairwise_insert_of_symm_of_notMem, pairwise_insert_of_symm_of_notMem
-/
lemma isClique_insert_of_notMem (ha : a ∉ s) :
    G.IsClique (insert a s) ↔ G.IsClique s ∧ forall b in s, G.Adj a b :=
  have := G.symm
  Set.pairwise_insert_of_symm_of_notMem ha

/--
lemma `IsClique.insert` / 引理 `IsClique.insert`

English:
lemma IsClique.insert
  given: (hs : G.IsClique s) (h : forall b in s, a != b -> G.Adj a b)
  proof: have := G.symm
  hs.insert_of_symm h

@[gcongr]

中文:
引理 IsClique.insert
  条件: (hs : G.IsClique s) (h : 对任意 b in s, a != b -> G.伴随 a b)
  证明: have := G.symm
  hs.insert_of_symm h

@[gcongr]

Depends on / 依赖: G.symm, hs.insert_of_symm, insert_of_symm
-/
lemma IsClique.insert (hs : G.IsClique s) (h : forall b in s, a != b -> G.Adj a b) :
    G.IsClique (insert a s) :=
  have := G.symm
  hs.insert_of_symm h

@[gcongr]
/--
theorem `IsClique.mono` / 定理 `IsClique.mono`

English:
theorem IsClique.mono
  given: (h : G <= H)
  statement: G.IsClique s -> H.IsClique s
  proof: Set.Pairwise.mono' h

@[gcongr]

中文:
定理 IsClique.mono
  条件: (h : G <= H)
  结论: G.IsClique s -> H.IsClique s
  证明: Set.Pairwise.mono' h

@[gcongr]

Depends on / 依赖: Pairwise, Set.Pairwise.mono
-/
theorem IsClique.mono (h : G <= H) : G.IsClique s -> H.IsClique s := Set.Pairwise.mono' h

@[gcongr]
/--
theorem `IsClique.subset` / 定理 `IsClique.subset`

English:
theorem IsClique.subset
  given: (h : t subseteq s)
  statement: G.IsClique s -> G.IsClique t
  proof: Set.Pairwise.mono h

中文:
定理 IsClique.subset
  条件: (h : t subseteq s)
  结论: G.IsClique s -> G.IsClique t
  证明: Set.Pairwise.mono h

Depends on / 依赖: Pairwise, Set.Pairwise.mono
-/
theorem IsClique.subset (h : t subseteq s) : G.IsClique s -> G.IsClique t := Set.Pairwise.mono h

variable (s) in
@[simp]
/--
theorem `IsClique.top` / 定理 `IsClique.top`

English:
theorem IsClique.top
  statement: (⊤ : SimpleGraph α).IsClique s
  proof: fun _ _ _ _ => id

@[simp]

中文:
定理 IsClique.top
  结论: (⊤ : 简单图 α).IsClique s
  证明: fun _ _ _ _ => id

@[simp]
-/
protected theorem IsClique.top : (⊤ : SimpleGraph α).IsClique s :=
  fun _ _ _ _ => id

@[simp]
/--
theorem `isClique_bot_iff` / 定理 `isClique_bot_iff`

English:
theorem isClique_bot_iff
  statement: (⊥ : SimpleGraph α).IsClique s ↔ (s : Set α).Subsingleton
  proof: Set.pairwise_bot_iff

alias ⟨IsClique.subsingleton, _⟩ := isClique_bot_iff

@[simp]

中文:
定理 isClique_bot_iff
  结论: (⊥ : 简单图 α).IsClique s ↔ (s : 集合 α).子单例
  证明: Set.pairwise_bot_iff

alias ⟨IsClique.subsingleton, _⟩ := isClique_bot_iff

@[simp]

Depends on / 依赖: Set.pairwise_bot_iff, pairwise_bot_iff
-/
theorem isClique_bot_iff : (⊥ : SimpleGraph α).IsClique s ↔ (s : Set α).Subsingleton :=
  Set.pairwise_bot_iff

alias ⟨IsClique.subsingleton, _⟩ := isClique_bot_iff

@[simp]
/--
theorem `isClique_univ` / 定理 `isClique_univ`

English:
theorem isClique_univ
  statement: G.IsClique .univ ↔ G = ⊤
  proof: Set.pairwise_univ.trans G.eq_top_iff_forall_ne_adj.symm

中文:
定理 isClique_univ
  结论: G.IsClique .univ ↔ G = ⊤
  证明: Set.pairwise_univ.trans G.eq_top_iff_forall_ne_adj.symm

Depends on / 依赖: G.eq_top_iff_forall_ne_adj.symm, Set.pairwise_univ.trans, eq_top_iff_forall_ne_adj, pairwise_univ
-/
theorem isClique_univ : G.IsClique .univ ↔ G = ⊤ :=
  Set.pairwise_univ.trans G.eq_top_iff_forall_ne_adj.symm

/--
theorem `IsClique.map` / 定理 `IsClique.map`

English:
theorem IsClique.map
  given: (h : G.IsClique s) {f : α ↪ β}
  statement: (G.map f).IsClique (f '' s)
  proof: by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
exact ⟨hab, a, b, h ha hb ne_of_apply_ne _ hab, rfl, rfl⟩

中文:
定理 IsClique.map
  条件: (h : G.IsClique s) {f : α ↪ β}
  结论: (G.map f).IsClique (f '' s)
  证明: by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
exact ⟨hab, a, b, h ha hb ne_of_apply_ne _ hab, rfl, rfl⟩
-/
protected theorem IsClique.map (h : G.IsClique s) {f : α ↪ β} : (G.map f).IsClique (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
exact ⟨hab, a, b, h ha hb ne_of_apply_ne _ hab, rfl, rfl⟩

/--
theorem `IsClique.inter_left` / 定理 `IsClique.inter_left`

English:
theorem IsClique.inter_left
  given: {s : Set α} (hs : G.IsClique s) (t : Set α)
  statement: G.IsClique s inter t
  proof: Set.Pairwise.inter_left hs t

中文:
定理 IsClique.inter_left
  条件: {s : 集合 α} (hs : G.IsClique s) (t : 集合 α)
  结论: G.IsClique s inter t
  证明: Set.Pairwise.inter_left hs t

Depends on / 依赖: Pairwise, Set.Pairwise.inter_left, inter_left
-/
theorem IsClique.inter_left {s : Set α} (hs : G.IsClique s) (t : Set α) : G.IsClique s inter t :=
  Set.Pairwise.inter_left hs t

/--
theorem `IsClique.inter_right` / 定理 `IsClique.inter_right`

English:
theorem IsClique.inter_right
  given: {s : Set α} (hs : G.IsClique s) (t : Set α)
  statement: G.IsClique t inter s
  proof: Set.Pairwise.inter_right hs t

中文:
定理 IsClique.inter_right
  条件: {s : 集合 α} (hs : G.IsClique s) (t : 集合 α)
  结论: G.IsClique t inter s
  证明: Set.Pairwise.inter_right hs t

Depends on / 依赖: Pairwise, Set.Pairwise.inter_right, inter_right
-/
theorem IsClique.inter_right {s : Set α} (hs : G.IsClique s) (t : Set α) : G.IsClique t inter s :=
  Set.Pairwise.inter_right hs t

/--
theorem `isClique_sUnion` / 定理 `isClique_sUnion`

English:
theorem isClique_sUnion
  given: {S : Set (Set α)} (hd : DirectedOn (· subseteq ·) S)
  proof: Set.pairwise_sUnion hd

中文:
定理 isClique_sUnion
  条件: {S : 集合 (集合 α)} (hd : DirectedOn (· subseteq ·) S)
  证明: Set.pairwise_sUnion hd

Depends on / 依赖: Set.pairwise_sUnion, pairwise_sUnion
-/
theorem isClique_sUnion {S : Set (Set α)} (hd : DirectedOn (· subseteq ·) S) :
    G.IsClique (⋃₀ S) ↔ forall s in S, G.IsClique s :=
  Set.pairwise_sUnion hd

/--
theorem `isClique_iUnion` / 定理 `isClique_iUnion`

English:
theorem isClique_iUnion
  given: {ι : Type*} {s : ι -> Set α} (hd : Directed (· subseteq ·) s)
  proof: Set.pairwise_iUnion hd

中文:
定理 isClique_iUnion
  条件: {ι : 类型} {s : ι -> 集合 α} (hd : Directed (· subseteq ·) s)
  证明: Set.pairwise_iUnion hd

Depends on / 依赖: Set.pairwise_iUnion, pairwise_iUnion
-/
theorem isClique_iUnion {ι : Type*} {s : ι -> Set α} (hd : Directed (· subseteq ·) s) :
    G.IsClique (⋃ i, s i) ↔ forall i, G.IsClique (s i) :=
  Set.pairwise_iUnion hd

/--
theorem `isClique_map_iff_of_nontrivial` / 定理 `isClique_map_iff_of_nontrivial`

English:
theorem isClique_map_iff_of_nontrivial
  given: {f : α ↪ β} {t : Set β} (ht : t.Nontrivial)
  proof: by
  refine ⟨fun h => ⟨f ⁻¹' t, ?_, ?_⟩, by rintro ⟨x, hs, rfl⟩; exact hs.map⟩
  · rintro x (hx : f x in t) y (hy : f y in t) hne
    obtain ⟨-, u, v, huv, hux, hvy⟩ := h hx hy (by simpa)
    rw [EmbeddingLike.apply_eq_iff_eq] at hux hvy
    rwa [← hux, ← hvy]
  rw [Set.image_preimage_eq_iff]
  intr

中文:
定理 isClique_map_iff_of_nontrivial
  条件: {f : α ↪ β} {t : 集合 β} (ht : t.非平凡)
  证明: by
  refine ⟨fun h => ⟨f ⁻¹' t, ?_, ?_⟩, by rintro ⟨x, hs, rfl⟩; exact hs.map⟩
  · rintro x (hx : f x in t) y (hy : f y in t) hne
    obtain ⟨-, u, v, huv, hux, hvy⟩ := h hx hy (by simpa)
    rw [EmbeddingLike.apply_eq_iff_eq] at hux hvy
    rwa [← hux, ← hvy]
  rw [Set.image_preimage_eq_iff]
  intr

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Set.image_preimage_eq_iff, Set.mem_range_self, apply_eq_iff_eq, exists_ne, hs.map, ht.exists_ne, image_preimage_eq_iff, mem_range_self
-/
theorem isClique_map_iff_of_nontrivial {f : α ↪ β} {t : Set β} (ht : t.Nontrivial) :
    (G.map f).IsClique t ↔ exists (s : Set α), G.IsClique s ∧ f '' s = t := by
  refine ⟨fun h => ⟨f ⁻¹' t, ?_, ?_⟩, by rintro ⟨x, hs, rfl⟩; exact hs.map⟩
  · rintro x (hx : f x in t) y (hy : f y in t) hne
    obtain ⟨-, u, v, huv, hux, hvy⟩ := h hx hy (by simpa)
    rw [EmbeddingLike.apply_eq_iff_eq] at hux hvy
    rwa [← hux, ← hvy]
  rw [Set.image_preimage_eq_iff]
  intro x hxt
  obtain ⟨y, hyt, hyne⟩ := ht.exists_ne x
  obtain ⟨-, u, v, -, rfl, rfl⟩ := h hyt hxt hyne
  exact Set.mem_range_self _

/--
theorem `isClique_map_iff` / 定理 `isClique_map_iff`

English:
theorem isClique_map_iff
  given: {f : α ↪ β} {t : Set β}
  proof: by
  obtain (ht | ht) := t.subsingleton_or_nontrivial
  · simp [IsClique.of_subsingleton, ht]
  simp [isClique_map_iff_of_nontrivial ht, ht.not_subsingleton]

中文:
定理 isClique_map_iff
  条件: {f : α ↪ β} {t : 集合 β}
  证明: by
  obtain (ht | ht) := t.subsingleton_or_nontrivial
  · simp [IsClique.of_subsingleton, ht]
  simp [isClique_map_iff_of_nontrivial ht, ht.not_subsingleton]

Depends on / 依赖: IsClique, IsClique.of_subsingleton, ht.not_subsingleton, isClique_map_iff_of_nontrivial, not_subsingleton, of_subsingleton, subsingleton_or_nontrivial, t.subsingleton_or_nontrivial
-/
theorem isClique_map_iff {f : α ↪ β} {t : Set β} :
    (G.map f).IsClique t ↔ t.Subsingleton ∨ exists (s : Set α), G.IsClique s ∧ f '' s = t := by
  obtain (ht | ht) := t.subsingleton_or_nontrivial
  · simp [IsClique.of_subsingleton, ht]
  simp [isClique_map_iff_of_nontrivial ht, ht.not_subsingleton]

/--
theorem `isClique_map_image_iff` / 定理 `isClique_map_image_iff`

English:
theorem isClique_map_image_iff
  given: {f : α ↪ β}
  proof: by
  rw [isClique_map_iff]; rw [f.injective.subsingleton_image_iff]
  obtain (hs | hs) := s.subsingleton_or_nontrivial
  · simp [hs, IsClique.of_subsingleton]
  simp [or_iff_right hs.not_subsingleton, Set.image_eq_image f.injective]

中文:
定理 isClique_map_image_iff
  条件: {f : α ↪ β}
  证明: by
  rw [isClique_map_iff]; rw [f.injective.subsingleton_image_iff]
  obtain (hs | hs) := s.subsingleton_or_nontrivial
  · simp [hs, IsClique.of_subsingleton]
  simp [or_iff_right hs.not_subsingleton, Set.image_eq_image f.injective]
-/
@[simp] theorem isClique_map_image_iff {f : α ↪ β} :
    (G.map f).IsClique (f '' s) ↔ G.IsClique s := by
  rw [isClique_map_iff]; rw [f.injective.subsingleton_image_iff]
  obtain (hs | hs) := s.subsingleton_or_nontrivial
  · simp [hs, IsClique.of_subsingleton]
  simp [or_iff_right hs.not_subsingleton, Set.image_eq_image f.injective]

/--
theorem `isClique_induce_iff` / 定理 `isClique_induce_iff`

English:
theorem isClique_induce_iff
  given: {s : Set α} {t : Set s}
  proof: by
  simp [Set.Pairwise]

中文:
定理 isClique_induce_iff
  条件: {s : 集合 α} {t : 集合 s}
  证明: by
  simp [Set.Pairwise]

Depends on / 依赖: Pairwise, Set.Pairwise
-/
theorem isClique_induce_iff {s : Set α} {t : Set s} :
    (G.induce s).IsClique t ↔ G.IsClique (Subtype.val '' t) := by
  simp [Set.Pairwise]

variable {f : α ↪ β} {t : Finset β}

/--
theorem `isClique_map_finset_iff_of_nontrivial` / 定理 `isClique_map_finset_iff_of_nontrivial`

English:
theorem isClique_map_finset_iff_of_nontrivial
  given: (ht : t.Nontrivial)
  proof: by
  constructor
  · rw [isClique_map_iff_of_nontrivial (by simpa)]
    rintro ⟨s, hs, hst⟩
obtain ⟨s, rfl⟩ := Set.Finite.exists_finset_coe
      (show s.Finite from Set.Finite.of_finite_image (by simp [hst]) f.injective.injOn)
    exact ⟨s,hs, Finset.coe_inj.1 (by simpa)⟩
  rintro ⟨s, hs, rfl⟩
  si

中文:
定理 isClique_map_finset_iff_of_nontrivial
  条件: (ht : t.非平凡)
  证明: by
  constructor
  · rw [isClique_map_iff_of_nontrivial (by simpa)]
    rintro ⟨s, hs, hst⟩
obtain ⟨s, rfl⟩ := Set.Finite.exists_finset_coe
      (show s.Finite from Set.Finite.of_finite_image (by simp [hst]) f.injective.injOn)
    exact ⟨s,hs, Finset.coe_inj.1 (by simpa)⟩
  rintro ⟨s, hs, rfl⟩
  si

Depends on / 依赖: Finite, Finset, Finset.coe_inj, Set.Finite.exists_finset_coe, Set.Finite.of_finite_image, coe_inj, exists_finset_coe, f.injective.injOn, hs.map, injective, isClique_map_iff_of_nontrivial, of_finite_image, s.Finite
-/
theorem isClique_map_finset_iff_of_nontrivial (ht : t.Nontrivial) :
    (G.map f).IsClique t ↔ exists (s : Finset α), G.IsClique s ∧ s.map f = t := by
  constructor
  · rw [isClique_map_iff_of_nontrivial (by simpa)]
    rintro ⟨s, hs, hst⟩
obtain ⟨s, rfl⟩ := Set.Finite.exists_finset_coe
      (show s.Finite from Set.Finite.of_finite_image (by simp [hst]) f.injective.injOn)
    exact ⟨s,hs, Finset.coe_inj.1 (by simpa)⟩
  rintro ⟨s, hs, rfl⟩
  simpa using hs.map (f := f)

/--
theorem `isClique_map_finset_iff` / 定理 `isClique_map_finset_iff`

English:
theorem isClique_map_finset_iff
  proof: by
  obtain (ht | ht) := le_or_gt #t 1
  · simp only [ht, true_or, iff_true]
exact IsClique.of_subsingleton card_le_one.1 ht
  rw [isClique_map_finset_iff_of_nontrivial]; rw [← not_lt]
  · simp [ht]
  exact Finset.one_lt_card_iff_nontrivial.mp ht

中文:
定理 isClique_map_finset_iff
  证明: by
  obtain (ht | ht) := le_or_gt #t 1
  · simp only [ht, true_or, iff_true]
exact IsClique.of_subsingleton card_le_one.1 ht
  rw [isClique_map_finset_iff_of_nontrivial]; rw [← not_lt]
  · simp [ht]
  exact Finset.one_lt_card_iff_nontrivial.mp ht

Depends on / 依赖: Finset, Finset.one_lt_card_iff_nontrivial.mp, IsClique, IsClique.of_subsingleton, card_le_one, iff_true, isClique_map_finset_iff_of_nontrivial, le_or_gt, not_lt, of_subsingleton, one_lt_card_iff_nontrivial, true_or
-/
theorem isClique_map_finset_iff :
    (G.map f).IsClique t ↔ #t <= 1 ∨ exists (s : Finset α), G.IsClique s ∧ s.map f = t := by
  obtain (ht | ht) := le_or_gt #t 1
  · simp only [ht, true_or, iff_true]
exact IsClique.of_subsingleton card_le_one.1 ht
  rw [isClique_map_finset_iff_of_nontrivial]; rw [← not_lt]
  · simp [ht]
  exact Finset.one_lt_card_iff_nontrivial.mp ht

/--
theorem `IsClique.finsetMap` / 定理 `IsClique.finsetMap`

English:
theorem IsClique.finsetMap
  given: {f : α ↪ β} {s : Finset α} (h : G.IsClique s)
  proof: by
  simpa

中文:
定理 IsClique.finsetMap
  条件: {f : α ↪ β} {s : 有限集 α} (h : G.IsClique s)
  证明: by
  simpa
-/
protected theorem IsClique.finsetMap {f : α ↪ β} {s : Finset α} (h : G.IsClique s) :
    (G.map f).IsClique (s.map f) := by
  simpa

/--
theorem `IsClique.of_induce` / 定理 `IsClique.of_induce`

English:
theorem IsClique.of_induce
  statement: {S : Subgraph G} {F : Set α} {A : Set F}
  proof: by
  simp only [Set.Pairwise, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  intro _ ⟨_, ainA⟩ _ ⟨_, binA⟩ anb
  exact S.adj_sub (c ainA binA (Subtype.coe_ne_coe.mp anb)).2.2

中文:
定理 IsClique.of_induce
  结论: {S : 子图 G} {F : 集合 α} {A : 集合 F}
  证明: by
  simp only [Set.Pairwise, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  intro _ ⟨_, ainA⟩ _ ⟨_, binA⟩ anb
  exact S.adj_sub (c ainA binA (Subtype.coe_ne_coe.mp anb)).2.2

Depends on / 依赖: Pairwise, S.adj_sub, Set.Pairwise, Set.mem_image, Subtype, Subtype.coe_ne_coe.mp, Subtype.exists, adj_sub, coe_ne_coe, exists_and_right, exists_eq_right, mem_image
-/
theorem IsClique.of_induce {S : Subgraph G} {F : Set α} {A : Set F}
    (c : (S.induce F).coe.IsClique A) : G.IsClique (Subtype.val '' A) := by
  simp only [Set.Pairwise, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
  intro _ ⟨_, ainA⟩ _ ⟨_, binA⟩ anb
  exact S.adj_sub (c ainA binA (Subtype.coe_ne_coe.mp anb)).2.2

/--
lemma `IsClique.sdiff_of_sup_edge` / 引理 `IsClique.sdiff_of_sup_edge`

English:
lemma IsClique.sdiff_of_sup_edge
  given: {v w : α} {s : Set α} (hc : (G ⊔ edge v w).IsClique s)
  proof: by
  intro _ hx _ hy hxy
  have := hc hx.1 hy.1 hxy
  simp_all [sup_adj, edge_adj]

中文:
引理 IsClique.sdiff_of_sup_edge
  条件: {v w : α} {s : 集合 α} (hc : (G ⊔ edge v w).IsClique s)
  证明: by
  intro _ hx _ hy hxy
  have := hc hx.1 hy.1 hxy
  simp_all [sup_adj, edge_adj]

Depends on / 依赖: edge_adj, sup_adj
-/
lemma IsClique.sdiff_of_sup_edge {v w : α} {s : Set α} (hc : (G ⊔ edge v w).IsClique s) :
    G.IsClique (s \ {v}) := by
  intro _ hx _ hy hxy
  have := hc hx.1 hy.1 hxy
  simp_all [sup_adj, edge_adj]

/--
lemma `isClique_sup_edge_of_ne_sdiff` / 引理 `isClique_sup_edge_of_ne_sdiff`

English:
lemma isClique_sup_edge_of_ne_sdiff
  statement: {v w : α} {s : Set α} (h : v != w) (hv : G.IsClique (s \ {v}))
  proof: by
  intro x hx y hy hxy
  by_cases h' : x in s \ {v} ∧ y in s \ {v} ∨ x in s \ {w} ∧ y in s \ {w}
  · obtain (⟨hx, hy⟩ | ⟨hx, hy⟩) := h'
    · exact hv.mono le_sup_left hx hy hxy
    · exact hw.mono le_sup_left hx hy hxy
  · exact Or.inr ⟨by by_cases x = v <;> aesop, hxy⟩

中文:
引理 isClique_sup_edge_of_ne_sdiff
  结论: {v w : α} {s : 集合 α} (h : v != w) (hv : G.IsClique (s \ {v}))
  证明: by
  intro x hx y hy hxy
  by_cases h' : x in s \ {v} ∧ y in s \ {v} ∨ x in s \ {w} ∧ y in s \ {w}
  · obtain (⟨hx, hy⟩ | ⟨hx, hy⟩) := h'
    · exact hv.mono le_sup_left hx hy hxy
    · exact hw.mono le_sup_left hx hy hxy
  · exact Or.inr ⟨by by_cases x = v <;> aesop, hxy⟩

Depends on / 依赖: Or.inr, hv.mono, hw.mono, le_sup_left
-/
lemma isClique_sup_edge_of_ne_sdiff {v w : α} {s : Set α} (h : v != w) (hv : G.IsClique (s \ {v}))
    (hw : G.IsClique (s \ {w})) : (G ⊔ edge v w).IsClique s := by
  intro x hx y hy hxy
  by_cases h' : x in s \ {v} ∧ y in s \ {v} ∨ x in s \ {w} ∧ y in s \ {w}
  · obtain (⟨hx, hy⟩ | ⟨hx, hy⟩) := h'
    · exact hv.mono le_sup_left hx hy hxy
    · exact hw.mono le_sup_left hx hy hxy
  · exact Or.inr ⟨by by_cases x = v <;> aesop, hxy⟩

/--
lemma `isClique_sup_edge_of_ne_iff` / 引理 `isClique_sup_edge_of_ne_iff`

English:
lemma isClique_sup_edge_of_ne_iff
  given: {v w : α} {s : Set α} (h : v != w)
  proof: ⟨fun h' => ⟨h'.sdiff_of_sup_edge, (edge_comm .. ▸ h').sdiff_of_sup_edge⟩,
    fun h' => isClique_sup_edge_of_ne_sdiff h h'.1 h'.2⟩

中文:
引理 isClique_sup_edge_of_ne_iff
  条件: {v w : α} {s : 集合 α} (h : v != w)
  证明: ⟨fun h' => ⟨h'.sdiff_of_sup_edge, (edge_comm .. ▸ h').sdiff_of_sup_edge⟩,
    fun h' => isClique_sup_edge_of_ne_sdiff h h'.1 h'.2⟩

Depends on / 依赖: edge_comm, isClique_sup_edge_of_ne_sdiff, sdiff_of_sup_edge
-/
lemma isClique_sup_edge_of_ne_iff {v w : α} {s : Set α} (h : v != w) :
    (G ⊔ edge v w).IsClique s ↔ G.IsClique (s \ {v}) ∧ G.IsClique (s \ {w}) :=
  ⟨fun h' => ⟨h'.sdiff_of_sup_edge, (edge_comm .. ▸ h').sdiff_of_sup_edge⟩,
    fun h' => isClique_sup_edge_of_ne_sdiff h h'.1 h'.2⟩

/--
theorem `isClique_range_copy_top` / 定理 `isClique_range_copy_top`

English:
theorem isClique_range_copy_top
  given: (f : Copy (⊤ : SimpleGraph β) G)
  proof: by
  intro _ ⟨_, h⟩ _ ⟨_, h'⟩ nh
  rw [← h]; rw [← Copy.topEmbedding_apply]; rw [← h']; rw [← Copy.topEmbedding_apply] at nh ⊢
  rwa [← f.topEmbedding.coe_toEmbedding, (f.topEmbedding.apply_eq_iff_eq _ _).ne,
    ← top_adj, ← f.topEmbedding.map_adj_iff] at nh

中文:
定理 isClique_range_copy_top
  条件: (f : 余py (⊤ : 简单图 β) G)
  证明: by
  intro _ ⟨_, h⟩ _ ⟨_, h'⟩ nh
  rw [← h]; rw [← Copy.topEmbedding_apply]; rw [← h']; rw [← Copy.topEmbedding_apply] at nh ⊢
  rwa [← f.topEmbedding.coe_toEmbedding, (f.topEmbedding.apply_eq_iff_eq _ _).ne,
    ← top_adj, ← f.topEmbedding.map_adj_iff] at nh

Depends on / 依赖: Copy.topEmbedding_apply, apply_eq_iff_eq, coe_toEmbedding, f.topEmbedding.apply_eq_iff_eq, f.topEmbedding.coe_toEmbedding, f.topEmbedding.map_adj_iff, map_adj_iff, topEmbedding, topEmbedding_apply, top_adj
-/
theorem isClique_range_copy_top (f : Copy (⊤ : SimpleGraph β) G) :
    G.IsClique (Set.range f) := by
  intro _ ⟨_, h⟩ _ ⟨_, h'⟩ nh
  rw [← h]; rw [← Copy.topEmbedding_apply]; rw [← h']; rw [← Copy.topEmbedding_apply] at nh ⊢
  rwa [← f.topEmbedding.coe_toEmbedding, (f.topEmbedding.apply_eq_iff_eq _ _).ne,
    ← top_adj, ← f.topEmbedding.map_adj_iff] at nh

end Clique

/-! ### `n`-cliques -/


section NClique

variable {n : Nat} {s : Finset α}

/--
Definition of `IsNClique` / `IsNClique` 的定义

English:
structure IsNClique
  parameters: (n : Nat) (s : Finset α)
  axioms and operations (2):
    - isClique : G.IsClique s
    - card_eq : #s = n

中文:
结构 是NClique
  参数: (n : 自然数) (s : 有限集 α)
  公理与运算 (2 个):
    - isClique : G.IsClique s
    - card_eq : #s = n
-/
structure IsNClique (n : Nat) (s : Finset α) : Prop where
  isClique : G.IsClique s
  card_eq : #s = n

/--
theorem `isNClique_iff` / 定理 `isNClique_iff`

English:
theorem isNClique_iff
  statement: G.IsNClique n s ↔ G.IsClique s ∧ #s = n
  proof: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

中文:
定理 isNClique_iff
  结论: G.是NClique n s ↔ G.IsClique s ∧ #s = n
  证明: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
-/
theorem isNClique_iff : G.IsNClique n s ↔ G.IsClique s ∧ #s = n :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] [DecidableRel G.Adj] {n
  body: decidable_of_iff' _ G.isNClique_iff

中文:
实例 [DecidableEq
  签名: α] [DecidableRel G.伴随] {n
  定义体: decidable_of_iff' _ G.isNClique_iff

Depends on / 依赖: G.isNClique_iff, decidable_of_iff, isNClique_iff
-/
instance [DecidableEq α] [DecidableRel G.Adj] {n : Nat} {s : Finset α} :
    Decidable (G.IsNClique n s) :=
  decidable_of_iff' _ G.isNClique_iff

variable {G H} {a b c : α}

/--
lemma `isNClique_empty` / 引理 `isNClique_empty`

English:
lemma isNClique_empty
  statement: G.IsNClique n ∅ ↔ n = 0
  proof: by simp [isNClique_iff, eq_comm]

@[simp]

中文:
引理 isNClique_empty
  结论: G.是NClique n ∅ ↔ n = 0
  证明: by simp [isNClique_iff, eq_comm]

@[simp]
-/
@[simp] lemma isNClique_empty : G.IsNClique n ∅ ↔ n = 0 := by simp [isNClique_iff, eq_comm]

@[simp]
/--
lemma `isNClique_singleton` / 引理 `isNClique_singleton`

English:
lemma isNClique_singleton
  statement: G.IsNClique n {a} ↔ n = 1
  proof: by simp [isNClique_iff, eq_comm]

中文:
引理 isNClique_singleton
  结论: G.是NClique n {a} ↔ n = 1
  证明: by simp [isNClique_iff, eq_comm]

Depends on / 依赖: eq_comm, isNClique_iff
-/
lemma isNClique_singleton : G.IsNClique n {a} ↔ n = 1 := by simp [isNClique_iff, eq_comm]

/--
theorem `IsNClique.mono` / 定理 `IsNClique.mono`

English:
theorem IsNClique.mono
  given: (h : G <= H)
  statement: G.IsNClique n s -> H.IsNClique n s
  proof: by
  simp_rw [isNClique_iff]
  exact And.imp_left (IsClique.mono h)

中文:
定理 是NClique.mono
  条件: (h : G <= H)
  结论: G.是NClique n s -> H.是NClique n s
  证明: by
  simp_rw [isNClique_iff]
  exact And.imp_left (IsClique.mono h)

Depends on / 依赖: And.imp_left, IsClique, IsClique.mono, imp_left, isNClique_iff, simp_rw
-/
theorem IsNClique.mono (h : G <= H) : G.IsNClique n s -> H.IsNClique n s := by
  simp_rw [isNClique_iff]
  exact And.imp_left (IsClique.mono h)

/--
theorem `IsNClique.map` / 定理 `IsNClique.map`

English:
theorem IsNClique.map
  given: (h : G.IsNClique n s) {f : α ↪ β}
  proof: ⟨by rw [coe_map]; exact h.1.map, (card_map _).trans h.2⟩

中文:
定理 是NClique.map
  条件: (h : G.是NClique n s) {f : α ↪ β}
  证明: ⟨by rw [coe_map]; exact h.1.map, (card_map _).trans h.2⟩
-/
protected theorem IsNClique.map (h : G.IsNClique n s) {f : α ↪ β} :
    (G.map f).IsNClique n (s.map f) :=
  ⟨by rw [coe_map]; exact h.1.map, (card_map _).trans h.2⟩

/--
theorem `isNClique_map_iff` / 定理 `isNClique_map_iff`

English:
theorem isNClique_map_iff
  given: (hn : 1 < n) {t : Finset β} {f : α ↪ β}
  proof: by
  rw [isNClique_iff]; rw [isClique_map_finset_iff]; rw [or_and_right]; rw [or_iff_right (by rintro ⟨h']; rw [rfl⟩; exact h'.not_gt hn)]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, rfl⟩
    simp [isNClique_iff, hs]
  rintro ⟨s, hs, rfl⟩
  simp [hs.card_eq, hs.isClique]

@[simp]

中文:
定理 isNClique_map_iff
  条件: (hn : 1 < n) {t : 有限集 β} {f : α ↪ β}
  证明: by
  rw [isNClique_iff]; rw [isClique_map_finset_iff]; rw [or_and_right]; rw [or_iff_right (by rintro ⟨h']; rw [rfl⟩; exact h'.not_gt hn)]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, rfl⟩
    simp [isNClique_iff, hs]
  rintro ⟨s, hs, rfl⟩
  simp [hs.card_eq, hs.isClique]

@[simp]

Depends on / 依赖: card_eq, hs.card_eq, hs.isClique, isClique, isClique_map_finset_iff, isNClique_iff, not_gt, or_and_right, or_iff_right
-/
theorem isNClique_map_iff (hn : 1 < n) {t : Finset β} {f : α ↪ β} :
    (G.map f).IsNClique n t ↔ exists s : Finset α, G.IsNClique n s ∧ s.map f = t := by
  rw [isNClique_iff]; rw [isClique_map_finset_iff]; rw [or_and_right]; rw [or_iff_right (by rintro ⟨h']; rw [rfl⟩; exact h'.not_gt hn)]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, rfl⟩
    simp [isNClique_iff, hs]
  rintro ⟨s, hs, rfl⟩
  simp [hs.card_eq, hs.isClique]

@[simp]
/--
theorem `isNClique_bot_iff` / 定理 `isNClique_bot_iff`

English:
theorem isNClique_bot_iff
  statement: (⊥ : SimpleGraph α).IsNClique n s ↔ n <= 1 ∧ #s = n
  proof: by
  rw [isNClique_iff]; rw [isClique_bot_iff]
  refine and_congr_left ?_
  rintro rfl
  exact card_le_one.symm

@[simp]

中文:
定理 isNClique_bot_iff
  结论: (⊥ : 简单图 α).是NClique n s ↔ n <= 1 ∧ #s = n
  证明: by
  rw [isNClique_iff]; rw [isClique_bot_iff]
  refine and_congr_left ?_
  rintro rfl
  exact card_le_one.symm

@[simp]

Depends on / 依赖: and_congr_left, card_le_one, card_le_one.symm, isClique_bot_iff, isNClique_iff
-/
theorem isNClique_bot_iff : (⊥ : SimpleGraph α).IsNClique n s ↔ n <= 1 ∧ #s = n := by
  rw [isNClique_iff]; rw [isClique_bot_iff]
  refine and_congr_left ?_
  rintro rfl
  exact card_le_one.symm

@[simp]
/--
theorem `isNClique_zero` / 定理 `isNClique_zero`

English:
theorem isNClique_zero
  statement: G.IsNClique 0 s ↔ s = ∅
  proof: by
  simp only [isNClique_iff, Finset.card_eq_zero, and_iff_right_iff_imp]; rintro rfl; simp

@[simp]

中文:
定理 isNClique_zero
  结论: G.是NClique 0 s ↔ s = ∅
  证明: by
  simp only [isNClique_iff, Finset.card_eq_zero, and_iff_right_iff_imp]; rintro rfl; simp

@[simp]

Depends on / 依赖: Finset, Finset.card_eq_zero, and_iff_right_iff_imp, card_eq_zero, isNClique_iff
-/
theorem isNClique_zero : G.IsNClique 0 s ↔ s = ∅ := by
  simp only [isNClique_iff, Finset.card_eq_zero, and_iff_right_iff_imp]; rintro rfl; simp

@[simp]
/--
theorem `isNClique_one` / 定理 `isNClique_one`

English:
theorem isNClique_one
  statement: G.IsNClique 1 s ↔ exists a, s = {a}
  proof: by
  simp only [isNClique_iff, card_eq_one, and_iff_right_iff_imp]; rintro ⟨a, rfl⟩; simp

中文:
定理 isNClique_one
  结论: G.是NClique 1 s ↔ 存在 a, s = {a}
  证明: by
  simp only [isNClique_iff, card_eq_one, and_iff_right_iff_imp]; rintro ⟨a, rfl⟩; simp

Depends on / 依赖: and_iff_right_iff_imp, card_eq_one, isNClique_iff
-/
theorem isNClique_one : G.IsNClique 1 s ↔ exists a, s = {a} := by
  simp only [isNClique_iff, card_eq_one, and_iff_right_iff_imp]; rintro ⟨a, rfl⟩; simp

section DecidableEq

variable [DecidableEq α]

/--
theorem `IsNClique.insert` / 定理 `IsNClique.insert`

English:
theorem IsNClique.insert
  given: (hs : G.IsNClique n s) (h : forall b in s, G.Adj a b)
  proof: by
  constructor
  · push_cast
    exact hs.1.insert fun b hb _ => h _ hb
  · rw [card_insert_of_notMem fun ha => (h _ ha).ne rfl, hs.2]

中文:
定理 是NClique.insert
  条件: (hs : G.是NClique n s) (h : 对任意 b in s, G.伴随 a b)
  证明: by
  constructor
  · push_cast
    exact hs.1.insert fun b hb _ => h _ hb
  · rw [card_insert_of_notMem fun ha => (h _ ha).ne rfl, hs.2]
-/
protected theorem IsNClique.insert (hs : G.IsNClique n s) (h : forall b in s, G.Adj a b) :
    G.IsNClique (n + 1) (insert a s) := by
  constructor
  · push_cast
    exact hs.1.insert fun b hb _ => h _ hb
  · rw [card_insert_of_notMem fun ha => (h _ ha).ne rfl, hs.2]

/--
lemma `IsNClique.erase_of_mem` / 引理 `IsNClique.erase_of_mem`

English:
lemma IsNClique.erase_of_mem
  given: (hs : G.IsNClique n s) (ha : a in s)
  proof: hs.isClique.subset by simp
  card_eq := by rw [card_erase_of_mem ha, hs.2]

中文:
引理 是NClique.erase_of_mem
  条件: (hs : G.是NClique n s) (ha : a in s)
  证明: hs.isClique.subset by simp
  card_eq := by rw [card_erase_of_mem ha, hs.2]

Depends on / 依赖: hs.isClique.subset, isClique, subset
-/
lemma IsNClique.erase_of_mem (hs : G.IsNClique n s) (ha : a in s) :
    G.IsNClique (n - 1) (s.erase a) where
isClique := hs.isClique.subset by simp
  card_eq := by rw [card_erase_of_mem ha, hs.2]

/--
lemma `IsNClique.insert_erase` / 引理 `IsNClique.insert_erase`

English:
lemma IsNClique.insert_erase
  proof: by
  cases n with
| zero => exact False.elim notMem_empty _ (isNClique_zero.1 hs ▸ hb)
  | succ _ => exact (hs.erase_of_mem hb).insert fun w h => by aesop

中文:
引理 是NClique.insert_erase
  证明: by
  cases n with
| zero => exact False.elim notMem_empty _ (isNClique_zero.1 hs ▸ hb)
  | succ _ => exact (hs.erase_of_mem hb).insert fun w h => by aesop
-/
protected lemma IsNClique.insert_erase
    (hs : G.IsNClique n s) (ha : forall w in s \ {b}, G.Adj a w) (hb : b in s) :
    G.IsNClique n (insert a (erase s b)) := by
  cases n with
| zero => exact False.elim notMem_empty _ (isNClique_zero.1 hs ▸ hb)
  | succ _ => exact (hs.erase_of_mem hb).insert fun w h => by aesop

/--
theorem `is3Clique_triple_iff` / 定理 `is3Clique_triple_iff`

English:
theorem is3Clique_triple_iff
  statement: G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c
  proof: by
  by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;>
    simp [isNClique_iff, and_rotate, *]

中文:
定理 is3Clique_triple_iff
  结论: G.是NClique 3 {a, b, c} ↔ G.伴随 a b ∧ G.伴随 a c ∧ G.伴随 b c
  证明: by
  by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;>
    simp [isNClique_iff, and_rotate, *]

Depends on / 依赖: and_rotate, isNClique_iff
-/
theorem is3Clique_triple_iff : G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;>
    simp [isNClique_iff, and_rotate, *]

/--
theorem `is3Clique_iff` / 定理 `is3Clique_iff`

English:
theorem is3Clique_iff
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, b, c, -, -, -, hs⟩ := card_eq_three.1 h.card_eq
    refine ⟨a, b, c, ?_⟩
    rwa [hs, eq_self_iff_true, and_true, is3Clique_triple_iff.symm, ← hs]
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is3Clique_triple_iff.2 ⟨hab, hbc, hca⟩

中文:
定理 is3Clique_iff
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, b, c, -, -, -, hs⟩ := card_eq_three.1 h.card_eq
    refine ⟨a, b, c, ?_⟩
    rwa [hs, eq_self_iff_true, and_true, is3Clique_triple_iff.symm, ← hs]
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is3Clique_triple_iff.2 ⟨hab, hbc, hca⟩

Depends on / 依赖: and_true, card_eq, card_eq_three, eq_self_iff_true, h.card_eq, is3Clique_triple_iff, is3Clique_triple_iff.symm
-/
theorem is3Clique_iff :
    G.IsNClique 3 s ↔ exists a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c} := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, b, c, -, -, -, hs⟩ := card_eq_three.1 h.card_eq
    refine ⟨a, b, c, ?_⟩
    rwa [hs, eq_self_iff_true, and_true, is3Clique_triple_iff.symm, ← hs]
  · rintro ⟨a, b, c, hab, hbc, hca, rfl⟩
    exact is3Clique_triple_iff.2 ⟨hab, hbc, hca⟩

end DecidableEq

/--
theorem `is3Clique_iff_exists_cycle_length_three` / 定理 `is3Clique_iff_exists_cycle_length_three`

English:
theorem is3Clique_iff_exists_cycle_length_three
  proof: by
  classical
  simp_rw [is3Clique_iff, isCycle_def]
  exact
    ⟨(fun ⟨_, a, _, _, hab, hac, hbc, _⟩ => ⟨a, cons hab (cons hbc (cons hac.symm nil)), by aesop⟩),
    (fun ⟨_, .cons hab (.cons hbc (.cons hca nil)), _, _⟩ => ⟨_, _, _, _, hab, hca.symm, hbc, rfl⟩)⟩

中文:
定理 is3Clique_iff_存在_cycle_length_three
  证明: by
  classical
  simp_rw [is3Clique_iff, isCycle_def]
  exact
    ⟨(fun ⟨_, a, _, _, hab, hac, hbc, _⟩ => ⟨a, cons hab (cons hbc (cons hac.symm nil)), by aesop⟩),
    (fun ⟨_, .cons hab (.cons hbc (.cons hca nil)), _, _⟩ => ⟨_, _, _, _, hab, hca.symm, hbc, rfl⟩)⟩

Depends on / 依赖: classical, hac.symm, hca.symm, is3Clique_iff, isCycle_def, simp_rw
-/
theorem is3Clique_iff_exists_cycle_length_three :
    (exists s : Finset α, G.IsNClique 3 s) ↔ exists (u : α) (w : G.Walk u u), w.IsCycle ∧ w.length = 3 := by
  classical
  simp_rw [is3Clique_iff, isCycle_def]
  exact
    ⟨(fun ⟨_, a, _, _, hab, hac, hbc, _⟩ => ⟨a, cons hab (cons hbc (cons hac.symm nil)), by aesop⟩),
    (fun ⟨_, .cons hab (.cons hbc (.cons hca nil)), _, _⟩ => ⟨_, _, _, _, hab, hca.symm, hbc, rfl⟩)⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsNClique.of_induce` / 定理 `IsNClique.of_induce`

English:
theorem IsNClique.of_induce
  statement: {S : Subgraph G} {F : Set α} {s : Finset { x // x in F }} {n : Nat}
  proof: by
  rw [isNClique_iff] at cc ⊢
  simp only [coe_map, card_map]
  exact ⟨cc.left.of_induce, cc.right⟩

中文:
定理 是NClique.of_induce
  结论: {S : 子图 G} {F : 集合 α} {s : 有限集 { x // x in F }} {n : 自然数}
  证明: by
  rw [isNClique_iff] at cc ⊢
  simp only [coe_map, card_map]
  exact ⟨cc.left.of_induce, cc.right⟩

Depends on / 依赖: card_map, cc.left.of_induce, cc.right, coe_map, isNClique_iff, of_induce
-/
theorem IsNClique.of_induce {S : Subgraph G} {F : Set α} {s : Finset { x // x in F }} {n : Nat}
    (cc : (S.induce F).coe.IsNClique n s) :
    G.IsNClique n (Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s) := by
  rw [isNClique_iff] at cc ⊢
  simp only [coe_map, card_map]
  exact ⟨cc.left.of_induce, cc.right⟩

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
lemma `IsNClique.erase_of_sup_edge_of_mem` / 引理 `IsNClique.erase_of_sup_edge_of_mem`

English:
lemma IsNClique.erase_of_sup_edge_of_mem
  statement: [DecidableEq α] {v w : α} {s : Finset α} {n : Nat}
  proof: coe_erase v _ ▸ hc.1.sdiff_of_sup_edge
  card_eq := by rw [card_erase_of_mem hx, hc.2]

中文:
引理 是NClique.erase_of_sup_edge_of_mem
  结论: [DecidableEq α] {v w : α} {s : 有限集 α} {n : 自然数}
  证明: coe_erase v _ ▸ hc.1.sdiff_of_sup_edge
  card_eq := by rw [card_erase_of_mem hx, hc.2]

Depends on / 依赖: coe_erase, sdiff_of_sup_edge
-/
lemma IsNClique.erase_of_sup_edge_of_mem [DecidableEq α] {v w : α} {s : Finset α} {n : Nat}
    (hc : (G ⊔ edge v w).IsNClique n s) (hx : v in s) : G.IsNClique (n - 1) (s.erase v) where
  isClique := coe_erase v _ ▸ hc.1.sdiff_of_sup_edge
  card_eq := by rw [card_erase_of_mem hx, hc.2]

/--
theorem `isNClique_map_copy_top` / 定理 `isNClique_map_copy_top`

English:
theorem isNClique_map_copy_top
  given: [Fintype β] (f : Copy (⊤ : SimpleGraph β) G)
  proof: by
  rw [isNClique_iff]; rw [card_map]; rw [card_univ]; rw [coe_map]; rw [coe_univ]; rw [Set.image_univ]
  exact ⟨isClique_range_copy_top f, rfl⟩

中文:
定理 isNClique_map_copy_top
  条件: [有限类型 β] (f : 余py (⊤ : 简单图 β) G)
  证明: by
  rw [isNClique_iff]; rw [card_map]; rw [card_univ]; rw [coe_map]; rw [coe_univ]; rw [Set.image_univ]
  exact ⟨isClique_range_copy_top f, rfl⟩

Depends on / 依赖: Set.image_univ, card_map, card_univ, coe_map, coe_univ, image_univ, isClique_range_copy_top, isNClique_iff
-/
theorem isNClique_map_copy_top [Fintype β] (f : Copy (⊤ : SimpleGraph β) G) :
    G.IsNClique (card β) (univ.map f.toEmbedding) := by
  rw [isNClique_iff]; rw [card_map]; rw [card_univ]; rw [coe_map]; rw [coe_univ]; rw [Set.image_univ]
  exact ⟨isClique_range_copy_top f, rfl⟩

/--
theorem `isNClique_induce_iff` / 定理 `isNClique_induce_iff`

English:
theorem isNClique_induce_iff
  given: (s : Set α) (t : Finset s) (n : Nat)
  proof: by
  simp [isNClique_iff, isClique_induce_iff]

中文:
定理 isNClique_induce_iff
  条件: (s : 集合 α) (t : 有限集 s) (n : 自然数)
  证明: by
  simp [isNClique_iff, isClique_induce_iff]

Depends on / 依赖: isClique_induce_iff, isNClique_iff
-/
theorem isNClique_induce_iff (s : Set α) (t : Finset s) (n : Nat) :
    (G.induce s).IsNClique n t ↔ G.IsNClique n (t.map (.subtype _)) := by
  simp [isNClique_iff, isClique_induce_iff]

end NClique

/-! ### Graphs without cliques -/


section CliqueFree

variable {m n : Nat}

/--
Definition of `CliqueFree` / `CliqueFree` 的定义

English:
definition CliqueFree
  signature: (n : Nat)
  body: forall t, ¬G.IsNClique n t

中文:
定义 CliqueFree
  签名: (n : 自然数)
  定义体: forall t, ¬G.IsNClique n t

Depends on / 依赖: G.IsNClique, IsNClique
-/
def CliqueFree (n : Nat) : Prop :=
  forall t, ¬G.IsNClique n t

variable {G H} {s : Finset α}

/--
theorem `IsNClique.not_cliqueFree` / 定理 `IsNClique.not_cliqueFree`

English:
theorem IsNClique.not_cliqueFree
  given: (hG : G.IsNClique n s)
  statement: ¬G.CliqueFree n
  proof: fun h => h _ hG

中文:
定理 是NClique.not_cliqueFree
  条件: (hG : G.是NClique n s)
  结论: ¬G.CliqueFree n
  证明: fun h => h _ hG
-/
theorem IsNClique.not_cliqueFree (hG : G.IsNClique n s) : ¬G.CliqueFree n :=
  fun h => h _ hG

/--
theorem `IsContained.not_cliqueFree` / 定理 `IsContained.not_cliqueFree`

English:
theorem IsContained.not_cliqueFree
  given: {n : Nat} (h : completeGraph (Fin n) ⊑ G)
  statement: ¬G.CliqueFree n
  proof: by
  have := isNClique_map_copy_top h.some
  rw [Fintype.card_fin] at this
  exact (· _ this)

@[deprecated (since := "2026-02-21")]
alias not_cliqueFree_of_top_embedding := IsContained.not_cliqueFree

中文:
定理 IsContained.not_cliqueFree
  条件: {n : 自然数} (h : completeGraph (有限集 n) ⊑ G)
  结论: ¬G.CliqueFree n
  证明: by
  have := isNClique_map_copy_top h.some
  rw [Fintype.card_fin] at this
  exact (· _ this)

@[deprecated (since := "2026-02-21")]
alias not_cliqueFree_of_top_embedding := IsContained.not_cliqueFree

Depends on / 依赖: Fintype, Fintype.card_fin, card_fin, h.some, isNClique_map_copy_top
-/
theorem IsContained.not_cliqueFree {n : Nat} (h : completeGraph (Fin n) ⊑ G) : ¬G.CliqueFree n := by
  have := isNClique_map_copy_top h.some
  rw [Fintype.card_fin] at this
  exact (· _ this)

@[deprecated (since := "2026-02-21")]
alias not_cliqueFree_of_top_embedding := IsContained.not_cliqueFree

/--
Definition of `topEmbeddingOfNotCliqueFree` / `topEmbeddingOfNotCliqueFree` 的定义

English:
definition topEmbeddingOfNotCliqueFree
  signature: {n : Nat} (h : ¬G.CliqueFree n)
  body: by
  unfold CliqueFree at h
  push Not at h
.comp apply Embedding.induce (h.choose : Set α)
  rw [G.induce_eq_top.mpr h.choose_spec.isClique]
exact Embedding.completeGraph .symm.toEmbedding Finset.equivFinOfCardEq h.choose_spec.card_eq

中文:
定义 topEmbeddingOfNotCliqueFree
  签名: {n : 自然数} (h : ¬G.CliqueFree n)
  定义体: by
  unfold CliqueFree at h
  push Not at h
.comp apply Embedding.induce (h.choose : Set α)
  rw [G.induce_eq_top.mpr h.choose_spec.isClique]
exact Embedding.completeGraph .symm.toEmbedding Finset.equivFinOfCardEq h.choose_spec.card_eq

Depends on / 依赖: CliqueFree, Embedding, Embedding.completeGraph, Embedding.induce, Finset, Finset.equivFinOfCardEq, G.induce_eq_top.mpr, card_eq, choose_spec, completeGraph, equivFinOfCardEq, h.choose, h.choose_spec.card_eq, h.choose_spec.isClique, induce, induce_eq_top, isClique, symm.toEmbedding, toEmbedding
-/
noncomputable def topEmbeddingOfNotCliqueFree {n : Nat} (h : ¬G.CliqueFree n) :
    completeGraph (Fin n) ↪g G := by
  unfold CliqueFree at h
  push Not at h
.comp apply Embedding.induce (h.choose : Set α)
  rw [G.induce_eq_top.mpr h.choose_spec.isClique]
exact Embedding.completeGraph .symm.toEmbedding Finset.equivFinOfCardEq h.choose_spec.card_eq

/--
theorem `not_cliqueFree_iff_top_isContained` / 定理 `not_cliqueFree_iff_top_isContained`

English:
theorem not_cliqueFree_iff_top_isContained
  given: (n : Nat)
  statement: ¬G.CliqueFree n ↔ completeGraph (Fin n) ⊑ G
  proof: ⟨(topEmbeddingOfNotCliqueFree · |>.isContained), IsContained.not_cliqueFree⟩

@[deprecated (since := "2026-03-23")] alias not_cliqueFree_iff := not_cliqueFree_iff_top_isContained

中文:
定理 not_cliqueFree_iff_top_isContained
  条件: (n : 自然数)
  结论: ¬G.CliqueFree n ↔ completeGraph (有限集 n) ⊑ G
  证明: ⟨(topEmbeddingOfNotCliqueFree · |>.isContained), IsContained.not_cliqueFree⟩

@[deprecated (since := "2026-03-23")] alias not_cliqueFree_iff := not_cliqueFree_iff_top_isContained

Depends on / 依赖: IsContained, IsContained.not_cliqueFree, isContained, not_cliqueFree, topEmbeddingOfNotCliqueFree
-/
theorem not_cliqueFree_iff_top_isContained (n : Nat) : ¬G.CliqueFree n ↔ completeGraph (Fin n) ⊑ G :=
  ⟨(topEmbeddingOfNotCliqueFree · |>.isContained), IsContained.not_cliqueFree⟩

@[deprecated (since := "2026-03-23")] alias not_cliqueFree_iff := not_cliqueFree_iff_top_isContained

/--
theorem `cliqueFree_iff` / 定理 `cliqueFree_iff`

English:
theorem cliqueFree_iff
  given: {n : Nat}
  statement: G.CliqueFree n ↔ IsEmpty (Copy (completeGraph <| Fin n) G)
  proof: by
  contrapose!
  exact not_cliqueFree_iff_top_isContained n

中文:
定理 cliqueFree_iff
  条件: {n : 自然数}
  结论: G.CliqueFree n ↔ 是空 (余py (completeGraph <| 有限集 n) G)
  证明: by
  contrapose!
  exact not_cliqueFree_iff_top_isContained n

Depends on / 依赖: contrapose, not_cliqueFree_iff_top_isContained
-/
theorem cliqueFree_iff {n : Nat} : G.CliqueFree n ↔ IsEmpty (Copy (completeGraph <| Fin n) G) := by
  contrapose!
  exact not_cliqueFree_iff_top_isContained n

/--
theorem `cliqueFree_iff_top_free` / 定理 `cliqueFree_iff_top_free`

English:
theorem cliqueFree_iff_top_free
  given: {β : Type*} [Fintype β]
  proof: by
  rw [← not_iff_not]; rw [not_free]; rw [not_cliqueFree_iff_top_isContained]; rw [isContained_congr (Iso.completeGraph (equivFin β)) Iso.refl]

中文:
定理 cliqueFree_iff_top_free
  条件: {β : 类型} [有限类型 β]
  证明: by
  rw [← not_iff_not]; rw [not_free]; rw [not_cliqueFree_iff_top_isContained]; rw [isContained_congr (Iso.completeGraph (equivFin β)) Iso.refl]

Depends on / 依赖: Iso.completeGraph, Iso.refl, completeGraph, equivFin, isContained_congr, not_cliqueFree_iff_top_isContained, not_free, not_iff_not
-/
theorem cliqueFree_iff_top_free {β : Type*} [Fintype β] :
    G.CliqueFree (card β) ↔ (⊤ : SimpleGraph β).Free G := by
  rw [← not_iff_not]; rw [not_free]; rw [not_cliqueFree_iff_top_isContained]; rw [isContained_congr (Iso.completeGraph (equivFin β)) Iso.refl]

/--
theorem `IsContained.not_cliqueFree_card` / 定理 `IsContained.not_cliqueFree_card`

English:
theorem IsContained.not_cliqueFree_card
  given: [Fintype α] (f : completeGraph α ⊑ G)
  proof: by
  rw [not_cliqueFree_iff_top_isContained]
  exact (Iso.completeGraph <| equivFin α).isContained'.trans f

@[deprecated (since := "2026-02-21")]
alias not_cliqueFree_card_of_top_embedding := IsContained.not_cliqueFree_card

中文:
定理 IsContained.not_cliqueFree_card
  条件: [有限类型 α] (f : completeGraph α ⊑ G)
  证明: by
  rw [not_cliqueFree_iff_top_isContained]
  exact (Iso.completeGraph <| equivFin α).isContained'.trans f

@[deprecated (since := "2026-02-21")]
alias not_cliqueFree_card_of_top_embedding := IsContained.not_cliqueFree_card

Depends on / 依赖: Iso.completeGraph, completeGraph, equivFin, isContained, not_cliqueFree_iff_top_isContained
-/
theorem IsContained.not_cliqueFree_card [Fintype α] (f : completeGraph α ⊑ G) :
    ¬G.CliqueFree (card α) := by
  rw [not_cliqueFree_iff_top_isContained]
  exact (Iso.completeGraph <| equivFin α).isContained'.trans f

@[deprecated (since := "2026-02-21")]
alias not_cliqueFree_card_of_top_embedding := IsContained.not_cliqueFree_card

/--
lemma `not_cliqueFree_zero` / 引理 `not_cliqueFree_zero`

English:
lemma not_cliqueFree_zero
  statement: ¬ G.CliqueFree 0
  proof: fun h => h ∅ isNClique_empty.mpr rfl

@[simp]

中文:
引理 not_cliqueFree_zero
  结论: ¬ G.CliqueFree 0
  证明: fun h => h ∅ isNClique_empty.mpr rfl

@[simp]
-/
@[simp] lemma not_cliqueFree_zero : ¬ G.CliqueFree 0 :=
fun h => h ∅ isNClique_empty.mpr rfl

@[simp]
/--
theorem `cliqueFree_bot` / 定理 `cliqueFree_bot`

English:
theorem cliqueFree_bot
  given: (h : 2 <= n)
  statement: (⊥ : SimpleGraph α).CliqueFree n
  proof: by
  intro t ht
  have := le_trans h (isNClique_bot_iff.1 ht).1
  contradiction

@[gcongr]

中文:
定理 cliqueFree_bot
  条件: (h : 2 <= n)
  结论: (⊥ : 简单图 α).CliqueFree n
  证明: by
  intro t ht
  have := le_trans h (isNClique_bot_iff.1 ht).1
  contradiction

@[gcongr]

Depends on / 依赖: isNClique_bot_iff, le_trans
-/
theorem cliqueFree_bot (h : 2 <= n) : (⊥ : SimpleGraph α).CliqueFree n := by
  intro t ht
  have := le_trans h (isNClique_bot_iff.1 ht).1
  contradiction

@[gcongr]
/--
theorem `CliqueFree.mono` / 定理 `CliqueFree.mono`

English:
theorem CliqueFree.mono
  given: (h : m <= n)
  statement: G.CliqueFree m -> G.CliqueFree n
  proof: by
  intro hG s hs
  obtain ⟨t, hts, ht⟩ := exists_subset_card_eq (h.trans hs.card_eq.ge)
  exact hG _ ⟨hs.isClique.subset hts, ht⟩

@[gcongr]

中文:
定理 CliqueFree.mono
  条件: (h : m <= n)
  结论: G.CliqueFree m -> G.CliqueFree n
  证明: by
  intro hG s hs
  obtain ⟨t, hts, ht⟩ := exists_subset_card_eq (h.trans hs.card_eq.ge)
  exact hG _ ⟨hs.isClique.subset hts, ht⟩

@[gcongr]

Depends on / 依赖: card_eq, exists_subset_card_eq, h.trans, hs.card_eq.ge, hs.isClique.subset, isClique, subset
-/
theorem CliqueFree.mono (h : m <= n) : G.CliqueFree m -> G.CliqueFree n := by
  intro hG s hs
  obtain ⟨t, hts, ht⟩ := exists_subset_card_eq (h.trans hs.card_eq.ge)
  exact hG _ ⟨hs.isClique.subset hts, ht⟩

@[gcongr]
/--
theorem `CliqueFree.anti` / 定理 `CliqueFree.anti`

English:
theorem CliqueFree.anti
  given: (h : G <= H)
  statement: H.CliqueFree n -> G.CliqueFree n
  proof: forall_imp fun _ => mt IsNClique.mono h

中文:
定理 CliqueFree.anti
  条件: (h : G <= H)
  结论: H.CliqueFree n -> G.CliqueFree n
  证明: forall_imp fun _ => mt IsNClique.mono h

Depends on / 依赖: IsNClique, IsNClique.mono, forall_imp
-/
theorem CliqueFree.anti (h : G <= H) : H.CliqueFree n -> G.CliqueFree n :=
forall_imp fun _ => mt IsNClique.mono h

/-- If a graph is cliquefree, any graph that is contained in it is also cliquefree. -/
@[gcongr only]
/--
theorem `CliqueFree.comap` / 定理 `CliqueFree.comap`

English:
theorem CliqueFree.comap
  given: {H : SimpleGraph β} (hle : H ⊑ G) (h : G.CliqueFree n)
  proof: by
  contrapose h
  rw [not_cliqueFree_iff_top_isContained] at h ⊢
  exact h.trans hle

中文:
定理 CliqueFree.comap
  条件: {H : 简单图 β} (hle : H ⊑ G) (h : G.CliqueFree n)
  证明: by
  contrapose h
  rw [not_cliqueFree_iff_top_isContained] at h ⊢
  exact h.trans hle

Depends on / 依赖: contrapose, h.trans, not_cliqueFree_iff_top_isContained
-/
theorem CliqueFree.comap {H : SimpleGraph β} (hle : H ⊑ G) (h : G.CliqueFree n) :
    H.CliqueFree n := by
  contrapose h
  rw [not_cliqueFree_iff_top_isContained] at h ⊢
  exact h.trans hle

/--
theorem `cliqueFree_map_iff` / 定理 `cliqueFree_map_iff`

English:
theorem cliqueFree_map_iff
  given: {f : α ↪ β} [Nonempty α]
  proof: by
  obtain (hle | hlt) := le_or_gt n 1
  · obtain (rfl | rfl) := Nat.le_one_iff_eq_zero_or_eq_one.1 hle
    · simp [CliqueFree]
    simp [CliqueFree, show exists (_ : β), True from ⟨f (Classical.arbitrary _), trivial⟩]
  simp [CliqueFree, isNClique_map_iff hlt]

中文:
定理 cliqueFree_map_iff
  条件: {f : α ↪ β} [非空 α]
  证明: by
  obtain (hle | hlt) := le_or_gt n 1
  · obtain (rfl | rfl) := Nat.le_one_iff_eq_zero_or_eq_one.1 hle
    · simp [CliqueFree]
    simp [CliqueFree, show exists (_ : β), True from ⟨f (Classical.arbitrary _), trivial⟩]
  simp [CliqueFree, isNClique_map_iff hlt]
-/
@[simp] theorem cliqueFree_map_iff {f : α ↪ β} [Nonempty α] :
    (G.map f).CliqueFree n ↔ G.CliqueFree n := by
  obtain (hle | hlt) := le_or_gt n 1
  · obtain (rfl | rfl) := Nat.le_one_iff_eq_zero_or_eq_one.1 hle
    · simp [CliqueFree]
    simp [CliqueFree, show exists (_ : β), True from ⟨f (Classical.arbitrary _), trivial⟩]
  simp [CliqueFree, isNClique_map_iff hlt]

/--
theorem `cliqueFree_of_card_lt` / 定理 `cliqueFree_of_card_lt`

English:
theorem cliqueFree_of_card_lt
  given: [Fintype α] (hc : card α < n)
  statement: G.CliqueFree n
  proof: by
  rw [cliqueFree_iff]
  contrapose! hc
  simpa only [Fintype.card_fin] using card_le_of_embedding hc.some.toEmbedding

中文:
定理 cliqueFree_of_card_lt
  条件: [有限类型 α] (hc : card α < n)
  结论: G.CliqueFree n
  证明: by
  rw [cliqueFree_iff]
  contrapose! hc
  simpa only [Fintype.card_fin] using card_le_of_embedding hc.some.toEmbedding

Depends on / 依赖: Fintype, Fintype.card_fin, card_fin, card_le_of_embedding, cliqueFree_iff, contrapose, hc.some.toEmbedding, toEmbedding
-/
theorem cliqueFree_of_card_lt [Fintype α] (hc : card α < n) : G.CliqueFree n := by
  rw [cliqueFree_iff]
  contrapose! hc
  simpa only [Fintype.card_fin] using card_le_of_embedding hc.some.toEmbedding

/--
theorem `cliqueFree_completeMultipartiteGraph` / 定理 `cliqueFree_completeMultipartiteGraph`

English:
theorem cliqueFree_completeMultipartiteGraph
  statement: {ι : Type*} [Fintype ι] (V : ι -> Type*)
  proof: by
  rw [cliqueFree_iff]; rw [isEmpty_iff]
  intro f
  obtain ⟨v, w, hn, he⟩ := exists_ne_map_eq_of_card_lt (Sigma.fst ∘ f) (by simp [hc])
  rw [← top_adj]; rw [← f.topEmbedding.map_adj_iff]; rw [comap_adj]; rw [top_adj] at hn
  exact absurd he hn

中文:
定理 cliqueFree_completeMultipartiteGraph
  结论: {ι : 类型} [有限类型 ι] (V : ι -> 类型)
  证明: by
  rw [cliqueFree_iff]; rw [isEmpty_iff]
  intro f
  obtain ⟨v, w, hn, he⟩ := exists_ne_map_eq_of_card_lt (Sigma.fst ∘ f) (by simp [hc])
  rw [← top_adj]; rw [← f.topEmbedding.map_adj_iff]; rw [comap_adj]; rw [top_adj] at hn
  exact absurd he hn

Depends on / 依赖: Sigma.fst, absurd, cliqueFree_iff, comap_adj, exists_ne_map_eq_of_card_lt, f.topEmbedding.map_adj_iff, isEmpty_iff, map_adj_iff, topEmbedding, top_adj
-/
theorem cliqueFree_completeMultipartiteGraph {ι : Type*} [Fintype ι] (V : ι -> Type*)
    (hc : card ι < n) : (completeMultipartiteGraph V).CliqueFree n := by
  rw [cliqueFree_iff]; rw [isEmpty_iff]
  intro f
  obtain ⟨v, w, hn, he⟩ := exists_ne_map_eq_of_card_lt (Sigma.fst ∘ f) (by simp [hc])
  rw [← top_adj]; rw [← f.topEmbedding.map_adj_iff]; rw [comap_adj]; rw [top_adj] at hn
  exact absurd he hn

namespace completeMultipartiteGraph

variable {ι : Type*} (V : ι -> Type*)

set_option backward.isDefEq.respectTransparency.types false in
/-- Embedding of the complete graph on `ι` into `completeMultipartiteGraph` on `ι` nonempty parts -/
@[simps]
/--
Definition of `topEmbedding` / `topEmbedding` 的定义

English:
definition topEmbedding
  signature: (f : forall (i : ι), V i)
  body: fun i => ⟨i, f i⟩
  inj' := fun _ _ h => (Sigma.mk.inj_iff.1 h).1
  map_rel_iff' := by simp

中文:
定义 topEmbedding
  签名: (f : 对任意 (i : ι), V i)
  定义体: fun i => ⟨i, f i⟩
  inj' := fun _ _ h => (Sigma.mk.inj_iff.1 h).1
  map_rel_iff' := by simp
-/
def topEmbedding (f : forall (i : ι), V i) :
    (⊤ : SimpleGraph ι) ↪g completeMultipartiteGraph V where
  toFun := fun i => ⟨i, f i⟩
  inj' := fun _ _ h => (Sigma.mk.inj_iff.1 h).1
  map_rel_iff' := by simp

/--
theorem `not_cliqueFree_of_le_card` / 定理 `not_cliqueFree_of_le_card`

English:
theorem not_cliqueFree_of_le_card
  given: [Fintype ι] (f : forall (i : ι), V i) (hc : n <= card ι)
  proof: fun hf => (cliqueFree_iff.1 <| hf.mono hc).elim'
.toCopy.comp (Iso.completeGraph (equivFin ι).symm).toCopy topEmbedding V f

中文:
定理 not_cliqueFree_of_le_card
  条件: [有限类型 ι] (f : 对任意 (i : ι), V i) (hc : n <= card ι)
  证明: fun hf => (cliqueFree_iff.1 <| hf.mono hc).elim'
.toCopy.comp (Iso.completeGraph (equivFin ι).symm).toCopy topEmbedding V f

Depends on / 依赖: Iso.completeGraph, cliqueFree_iff, completeGraph, equivFin, hf.mono, toCopy, toCopy.comp, topEmbedding
-/
theorem not_cliqueFree_of_le_card [Fintype ι] (f : forall (i : ι), V i) (hc : n <= card ι) :
    ¬ (completeMultipartiteGraph V).CliqueFree n :=
fun hf => (cliqueFree_iff.1 <| hf.mono hc).elim'
.toCopy.comp (Iso.completeGraph (equivFin ι).symm).toCopy topEmbedding V f

/--
theorem `not_cliqueFree_of_infinite` / 定理 `not_cliqueFree_of_infinite`

English:
theorem not_cliqueFree_of_infinite
  given: [Infinite ι] (f : forall (i : ι), V i)
  proof: (topEmbedding V f |>.comp <| .completeGraph <| Fin.valEmbedding.trans <| Infinite.natEmbedding ι)
.isContained.not_cliqueFree

中文:
定理 not_cliqueFree_of_infinite
  条件: [无限 ι] (f : 对任意 (i : ι), V i)
  证明: (topEmbedding V f |>.comp <| .completeGraph <| Fin.valEmbedding.trans <| Infinite.natEmbedding ι)
.isContained.not_cliqueFree

Depends on / 依赖: Fin.valEmbedding.trans, Infinite, Infinite.natEmbedding, completeGraph, isContained, isContained.not_cliqueFree, natEmbedding, not_cliqueFree, topEmbedding, valEmbedding
-/
theorem not_cliqueFree_of_infinite [Infinite ι] (f : forall (i : ι), V i) :
    ¬ (completeMultipartiteGraph V).CliqueFree n :=
  (topEmbedding V f |>.comp <| .completeGraph <| Fin.valEmbedding.trans <| Infinite.natEmbedding ι)
.isContained.not_cliqueFree

/--
theorem `not_cliqueFree_of_le_enatCard` / 定理 `not_cliqueFree_of_le_enatCard`

English:
theorem not_cliqueFree_of_le_enatCard
  given: (f : forall (i : ι), V i) (hc : n <= ENat.card ι)
  proof: by
  by_cases h : Infinite ι
  · exact not_cliqueFree_of_infinite V f
  · have : Fintype ι := fintypeOfNotInfinite h
    rw [ENat.card_eq_coe_fintype_card]; rw [Nat.cast_le] at hc
    exact not_cliqueFree_of_le_card V f hc

中文:
定理 not_cliqueFree_of_le_enatCard
  条件: (f : 对任意 (i : ι), V i) (hc : n <= E自然数.card ι)
  证明: by
  by_cases h : Infinite ι
  · exact not_cliqueFree_of_infinite V f
  · have : Fintype ι := fintypeOfNotInfinite h
    rw [ENat.card_eq_coe_fintype_card]; rw [Nat.cast_le] at hc
    exact not_cliqueFree_of_le_card V f hc

Depends on / 依赖: ENat.card_eq_coe_fintype_card, Fintype, Infinite, Nat.cast_le, card_eq_coe_fintype_card, cast_le, fintypeOfNotInfinite, not_cliqueFree_of_infinite, not_cliqueFree_of_le_card
-/
theorem not_cliqueFree_of_le_enatCard (f : forall (i : ι), V i) (hc : n <= ENat.card ι) :
    ¬ (completeMultipartiteGraph V).CliqueFree n := by
  by_cases h : Infinite ι
  · exact not_cliqueFree_of_infinite V f
  · have : Fintype ι := fintypeOfNotInfinite h
    rw [ENat.card_eq_coe_fintype_card]; rw [Nat.cast_le] at hc
    exact not_cliqueFree_of_le_card V f hc

end completeMultipartiteGraph

/--
theorem `CliqueFree.replaceVertex` / 定理 `CliqueFree.replaceVertex`

English:
theorem CliqueFree.replaceVertex
  given: [DecidableEq α] (h : G.CliqueFree n) (s t : α)
  proof: by
  contrapose h
  have ⟨φ, hφ⟩ := topEmbeddingOfNotCliqueFree h
  rw [not_cliqueFree_iff_top_isContained]
  by_cases mt : t in Set.range φ
  · obtain ⟨x, hx⟩ := mt
    by_cases ms : s in Set.range φ
    · obtain ⟨y, hy⟩ := ms
      have e := @hφ x y
      simp_rw [hx, hy, adj_comm, not_adj_replace

中文:
定理 CliqueFree.replaceVertex
  条件: [DecidableEq α] (h : G.CliqueFree n) (s t : α)
  证明: by
  contrapose h
  have ⟨φ, hφ⟩ := topEmbeddingOfNotCliqueFree h
  rw [not_cliqueFree_iff_top_isContained]
  by_cases mt : t in Set.range φ
  · obtain ⟨x, hx⟩ := mt
    by_cases ms : s in Set.range φ
    · obtain ⟨y, hy⟩ := ms
      have e := @hφ x y
      simp_rw [hx, hy, adj_comm, not_adj_replace
-/
protected theorem CliqueFree.replaceVertex [DecidableEq α] (h : G.CliqueFree n) (s t : α) :
    (G.replaceVertex s t).CliqueFree n := by
  contrapose h
  have ⟨φ, hφ⟩ := topEmbeddingOfNotCliqueFree h
  rw [not_cliqueFree_iff_top_isContained]
  by_cases mt : t in Set.range φ
  · obtain ⟨x, hx⟩ := mt
    by_cases ms : s in Set.range φ
    · obtain ⟨y, hy⟩ := ms
      have e := @hφ x y
      simp_rw [hx, hy, adj_comm, not_adj_replaceVertex_same, top_adj, false_iff, not_ne_iff] at e
      rwa [← hx, e, hy, replaceVertex_self, not_cliqueFree_iff_top_isContained] at h
    · unfold replaceVertex at hφ
      refine Embedding.isContained ⟨φ.setValue x s, fun {a b} => ?_⟩
      simp only [Embedding.coeFn_mk, Embedding.setValue, not_exists.mp ms, ite_false]
      rw [apply_ite (G.Adj · _)]; rw [apply_ite (G.Adj _ ·)]; rw [apply_ite (G.Adj _ ·)]
      convert! @hφ a b <;> simp only [← φ.apply_eq_iff_eq, SimpleGraph.irrefl, hx]
  · refine Embedding.isContained ⟨φ, ?_⟩
    simp_rw [Set.mem_range, not_exists, ← ne_eq] at mt
    conv at hφ => enter [a, b]; rw [G.adj_replaceVertex_iff_of_ne _ (mt a) (mt b)]
    exact hφ

@[simp]
/--
lemma `cliqueFree_one` / 引理 `cliqueFree_one`

English:
lemma cliqueFree_one
  statement: G.CliqueFree 1 ↔ IsEmpty α
  proof: by
  simp [CliqueFree, isEmpty_iff]

@[simp]

中文:
引理 cliqueFree_one
  结论: G.CliqueFree 1 ↔ 是空 α
  证明: by
  simp [CliqueFree, isEmpty_iff]

@[simp]

Depends on / 依赖: CliqueFree, isEmpty_iff
-/
lemma cliqueFree_one : G.CliqueFree 1 ↔ IsEmpty α := by
  simp [CliqueFree, isEmpty_iff]

@[simp]
/--
theorem `cliqueFree_two` / 定理 `cliqueFree_two`

English:
theorem cliqueFree_two
  statement: G.CliqueFree 2 ↔ G = ⊥
  proof: by
  classical
  constructor
  · simp_rw [← edgeSet_eq_empty, Set.eq_empty_iff_forall_notMem, Sym2.forall, mem_edgeSet]
    exact fun h a b hab => h _ ⟨by simpa [hab.ne], card_pair hab.ne⟩
  · rintro rfl
    exact cliqueFree_bot le_rfl

中文:
定理 cliqueFree_two
  结论: G.CliqueFree 2 ↔ G = ⊥
  证明: by
  classical
  constructor
  · simp_rw [← edgeSet_eq_empty, Set.eq_empty_iff_forall_notMem, Sym2.forall, mem_edgeSet]
    exact fun h a b hab => h _ ⟨by simpa [hab.ne], card_pair hab.ne⟩
  · rintro rfl
    exact cliqueFree_bot le_rfl

Depends on / 依赖: Set.eq_empty_iff_forall_notMem, Sym2.forall, card_pair, classical, cliqueFree_bot, edgeSet_eq_empty, eq_empty_iff_forall_notMem, hab.ne, le_rfl, mem_edgeSet, simp_rw
-/
theorem cliqueFree_two : G.CliqueFree 2 ↔ G = ⊥ := by
  classical
  constructor
  · simp_rw [← edgeSet_eq_empty, Set.eq_empty_iff_forall_notMem, Sym2.forall, mem_edgeSet]
    exact fun h a b hab => h _ ⟨by simpa [hab.ne], card_pair hab.ne⟩
  · rintro rfl
    exact cliqueFree_bot le_rfl

/--
lemma `CliqueFree.mem_of_sup_edge_isNClique` / 引理 `CliqueFree.mem_of_sup_edge_isNClique`

English:
lemma CliqueFree.mem_of_sup_edge_isNClique
  statement: {x y : α} {t : Finset α} {n : Nat} (h : G.CliqueFree n)
  proof: by
  by_contra hf
have ht : (t : Set α) \ {x} = t := sdiff_eq_left.mpr Set.disjoint_singleton_right.mpr hf
  exact h t ⟨ht ▸ hc.1.sdiff_of_sup_edge, hc.2⟩

中文:
引理 CliqueFree.mem_of_sup_edge_isNClique
  结论: {x y : α} {t : 有限集 α} {n : 自然数} (h : G.CliqueFree n)
  证明: by
  by_contra hf
have ht : (t : Set α) \ {x} = t := sdiff_eq_left.mpr Set.disjoint_singleton_right.mpr hf
  exact h t ⟨ht ▸ hc.1.sdiff_of_sup_edge, hc.2⟩

Depends on / 依赖: Set.disjoint_singleton_right.mpr, disjoint_singleton_right, sdiff_eq_left, sdiff_eq_left.mpr, sdiff_of_sup_edge
-/
lemma CliqueFree.mem_of_sup_edge_isNClique {x y : α} {t : Finset α} {n : Nat} (h : G.CliqueFree n)
    (hc : (G ⊔ edge x y).IsNClique n t) : x in t := by
  by_contra hf
have ht : (t : Set α) \ {x} = t := sdiff_eq_left.mpr Set.disjoint_singleton_right.mpr hf
  exact h t ⟨ht ▸ hc.1.sdiff_of_sup_edge, hc.2⟩

/--
theorem `CliqueFree.sup_edge` / 定理 `CliqueFree.sup_edge`

English:
theorem CliqueFree.sup_edge
  given: (h : G.CliqueFree n) (v w : α)
  proof: by
  classical
  exact fun _ hs => (hs.erase_of_sup_edge_of_mem <|
    (h.mono n.le_succ).mem_of_sup_edge_isNClique hs).not_cliqueFree h

中文:
定理 CliqueFree.sup_edge
  条件: (h : G.CliqueFree n) (v w : α)
  证明: by
  classical
  exact fun _ hs => (hs.erase_of_sup_edge_of_mem <|
    (h.mono n.le_succ).mem_of_sup_edge_isNClique hs).not_cliqueFree h
-/
protected theorem CliqueFree.sup_edge (h : G.CliqueFree n) (v w : α) :
    (G ⊔ edge v w).CliqueFree (n + 1) := by
  classical
  exact fun _ hs => (hs.erase_of_sup_edge_of_mem <|
    (h.mono n.le_succ).mem_of_sup_edge_isNClique hs).not_cliqueFree h

/--
lemma `IsNClique.exists_not_adj_of_cliqueFree_succ` / 引理 `IsNClique.exists_not_adj_of_cliqueFree_succ`

English:
lemma IsNClique.exists_not_adj_of_cliqueFree_succ
  statement: (hc : G.IsNClique n s)
  proof: by
  classical
  by_contra! hf
  exact (hc.insert hf).not_cliqueFree h

中文:
引理 是NClique.存在_not_adj_of_cliqueFree_succ
  结论: (hc : G.是NClique n s)
  证明: by
  classical
  by_contra! hf
  exact (hc.insert hf).not_cliqueFree h

Depends on / 依赖: classical, hc.insert, insert, not_cliqueFree
-/
lemma IsNClique.exists_not_adj_of_cliqueFree_succ (hc : G.IsNClique n s)
    (h : G.CliqueFree (n + 1)) (x : α) : exists y, y in s ∧ ¬ G.Adj x y := by
  classical
  by_contra! hf
  exact (hc.insert hf).not_cliqueFree h

/--
lemma `exists_of_maximal_cliqueFree_not_adj` / 引理 `exists_of_maximal_cliqueFree_not_adj`

English:
lemma exists_of_maximal_cliqueFree_not_adj
  statement: [DecidableEq α]
  proof: by
obtain ⟨t, hc⟩ := not_forall_not.1 h.not_prop_of_gt G.lt_sup_edge _ _ hne hn
  use (t.erase x).erase y, erase_right_comm (a := x) ▸ (notMem_erase _ _), notMem_erase _ _
  have h1 := h.1.mem_of_sup_edge_isNClique hc
  have h2 := h.1.mem_of_sup_edge_isNClique (edge_comm .. ▸ hc)
  rw [insert_erase 

中文:
引理 存在_of_maximal_cliqueFree_not_adj
  结论: [DecidableEq α]
  证明: by
obtain ⟨t, hc⟩ := not_forall_not.1 h.not_prop_of_gt G.lt_sup_edge _ _ hne hn
  use (t.erase x).erase y, erase_right_comm (a := x) ▸ (notMem_erase _ _), notMem_erase _ _
  have h1 := h.1.mem_of_sup_edge_isNClique hc
  have h2 := h.1.mem_of_sup_edge_isNClique (edge_comm .. ▸ hc)
  rw [insert_erase 

Depends on / 依赖: G.lt_sup_edge, edge_comm, erase_of_sup_edge_of_mem, erase_right_comm, h.not_prop_of_gt, hc.erase_of_sup_edge_of_mem, hne.symm, insert_erase, lt_sup_edge, mem_erase_of_ne_of_mem, mem_of_sup_edge_isNClique, notMem_erase, not_forall_not, not_prop_of_gt, t.erase
-/
lemma exists_of_maximal_cliqueFree_not_adj [DecidableEq α]
    (h : Maximal (fun H => H.CliqueFree (n + 1)) G) {x y : α} (hne : x != y) (hn : ¬ G.Adj x y) :
    exists s, x ∉ s ∧ y ∉ s ∧ G.IsNClique n (insert x s) ∧ G.IsNClique n (insert y s) := by
obtain ⟨t, hc⟩ := not_forall_not.1 h.not_prop_of_gt G.lt_sup_edge _ _ hne hn
  use (t.erase x).erase y, erase_right_comm (a := x) ▸ (notMem_erase _ _), notMem_erase _ _
  have h1 := h.1.mem_of_sup_edge_isNClique hc
  have h2 := h.1.mem_of_sup_edge_isNClique (edge_comm .. ▸ hc)
  rw [insert_erase <| mem_erase_of_ne_of_mem hne.symm h2]; rw [erase_right_comm]; rw [insert_erase mem_erase_of_ne_of_mem hne h1]
  exact ⟨(edge_comm .. ▸ hc).erase_of_sup_edge_of_mem h2, hc.erase_of_sup_edge_of_mem h1⟩

end CliqueFree

section CliqueFreeOn
variable {s s₁ s₂ : Set α} {a : α} {m n : Nat}

/--
Definition of `CliqueFreeOn` / `CliqueFreeOn` 的定义

English:
definition CliqueFreeOn
  signature: (G : SimpleGraph α) (s : Set α) (n : Nat)
  body: forall ⦃t⦄, ↑t subseteq s -> ¬G.IsNClique n t

中文:
定义 CliqueFreeOn
  签名: (G : 简单图 α) (s : 集合 α) (n : 自然数)
  定义体: forall ⦃t⦄, ↑t subseteq s -> ¬G.IsNClique n t

Depends on / 依赖: G.IsNClique, IsNClique, subseteq
-/
def CliqueFreeOn (G : SimpleGraph α) (s : Set α) (n : Nat) : Prop :=
  forall ⦃t⦄, ↑t subseteq s -> ¬G.IsNClique n t

/--
theorem `CliqueFreeOn.subset` / 定理 `CliqueFreeOn.subset`

English:
theorem CliqueFreeOn.subset
  given: (hs : s₁ subseteq s₂) (h₂ : G.CliqueFreeOn s₂ n)
  statement: G.CliqueFreeOn s₁ n
  proof: fun _t hts => h₂ hts.trans hs

中文:
定理 CliqueFreeOn.subset
  条件: (hs : s₁ subseteq s₂) (h₂ : G.CliqueFreeOn s₂ n)
  结论: G.CliqueFreeOn s₁ n
  证明: fun _t hts => h₂ hts.trans hs

Depends on / 依赖: hts.trans
-/
theorem CliqueFreeOn.subset (hs : s₁ subseteq s₂) (h₂ : G.CliqueFreeOn s₂ n) : G.CliqueFreeOn s₁ n :=
fun _t hts => h₂ hts.trans hs

/--
theorem `CliqueFreeOn.mono` / 定理 `CliqueFreeOn.mono`

English:
theorem CliqueFreeOn.mono
  given: (hmn : m <= n) (hG : G.CliqueFreeOn s m)
  statement: G.CliqueFreeOn s n
  proof: by
  rintro t hts ht
  obtain ⟨u, hut, hu⟩ := exists_subset_card_eq (hmn.trans ht.card_eq.ge)
  exact hG ((coe_subset.2 hut).trans hts) ⟨ht.isClique.subset hut, hu⟩

中文:
定理 CliqueFreeOn.mono
  条件: (hmn : m <= n) (hG : G.CliqueFreeOn s m)
  结论: G.CliqueFreeOn s n
  证明: by
  rintro t hts ht
  obtain ⟨u, hut, hu⟩ := exists_subset_card_eq (hmn.trans ht.card_eq.ge)
  exact hG ((coe_subset.2 hut).trans hts) ⟨ht.isClique.subset hut, hu⟩

Depends on / 依赖: card_eq, coe_subset, exists_subset_card_eq, hmn.trans, ht.card_eq.ge, ht.isClique.subset, isClique, subset
-/
theorem CliqueFreeOn.mono (hmn : m <= n) (hG : G.CliqueFreeOn s m) : G.CliqueFreeOn s n := by
  rintro t hts ht
  obtain ⟨u, hut, hu⟩ := exists_subset_card_eq (hmn.trans ht.card_eq.ge)
  exact hG ((coe_subset.2 hut).trans hts) ⟨ht.isClique.subset hut, hu⟩

/--
theorem `CliqueFreeOn.anti` / 定理 `CliqueFreeOn.anti`

English:
theorem CliqueFreeOn.anti
  given: (hGH : G <= H) (hH : H.CliqueFreeOn s n)
  statement: G.CliqueFreeOn s n
  proof: fun _t hts ht => hH hts ht.mono hGH

@[simp]

中文:
定理 CliqueFreeOn.anti
  条件: (hGH : G <= H) (hH : H.CliqueFreeOn s n)
  结论: G.CliqueFreeOn s n
  证明: fun _t hts ht => hH hts ht.mono hGH

@[simp]

Depends on / 依赖: ht.mono
-/
theorem CliqueFreeOn.anti (hGH : G <= H) (hH : H.CliqueFreeOn s n) : G.CliqueFreeOn s n :=
fun _t hts ht => hH hts ht.mono hGH

@[simp]
/--
theorem `cliqueFreeOn_empty` / 定理 `cliqueFreeOn_empty`

English:
theorem cliqueFreeOn_empty
  statement: G.CliqueFreeOn ∅ n ↔ n != 0
  proof: by
  simp [CliqueFreeOn, Set.subset_empty_iff]

@[simp]

中文:
定理 cliqueFreeOn_empty
  结论: G.CliqueFreeOn ∅ n ↔ n != 0
  证明: by
  simp [CliqueFreeOn, Set.subset_empty_iff]

@[simp]

Depends on / 依赖: CliqueFreeOn, Set.subset_empty_iff, subset_empty_iff
-/
theorem cliqueFreeOn_empty : G.CliqueFreeOn ∅ n ↔ n != 0 := by
  simp [CliqueFreeOn, Set.subset_empty_iff]

@[simp]
/--
theorem `cliqueFreeOn_singleton` / 定理 `cliqueFreeOn_singleton`

English:
theorem cliqueFreeOn_singleton
  statement: G.CliqueFreeOn {a} n ↔ 1 < n
  proof: by
  obtain _ | _ | n := n <;>
    simp [CliqueFreeOn, isNClique_iff, ← subset_singleton_iff', (Nat.succ_ne_zero _).symm]

@[simp]

中文:
定理 cliqueFreeOn_singleton
  结论: G.CliqueFreeOn {a} n ↔ 1 < n
  证明: by
  obtain _ | _ | n := n <;>
    simp [CliqueFreeOn, isNClique_iff, ← subset_singleton_iff', (Nat.succ_ne_zero _).symm]

@[simp]

Depends on / 依赖: CliqueFreeOn, Nat.succ_ne_zero, isNClique_iff, subset_singleton_iff, succ_ne_zero
-/
theorem cliqueFreeOn_singleton : G.CliqueFreeOn {a} n ↔ 1 < n := by
  obtain _ | _ | n := n <;>
    simp [CliqueFreeOn, isNClique_iff, ← subset_singleton_iff', (Nat.succ_ne_zero _).symm]

@[simp]
/--
theorem `cliqueFreeOn_univ` / 定理 `cliqueFreeOn_univ`

English:
theorem cliqueFreeOn_univ
  statement: G.CliqueFreeOn Set.univ n ↔ G.CliqueFree n
  proof: by
  simp [CliqueFree, CliqueFreeOn]

中文:
定理 cliqueFreeOn_univ
  结论: G.CliqueFreeOn 集合.univ n ↔ G.CliqueFree n
  证明: by
  simp [CliqueFree, CliqueFreeOn]

Depends on / 依赖: CliqueFree, CliqueFreeOn
-/
theorem cliqueFreeOn_univ : G.CliqueFreeOn Set.univ n ↔ G.CliqueFree n := by
  simp [CliqueFree, CliqueFreeOn]

/--
theorem `CliqueFree.cliqueFreeOn` / 定理 `CliqueFree.cliqueFreeOn`

English:
theorem CliqueFree.cliqueFreeOn
  given: (hG : G.CliqueFree n)
  statement: G.CliqueFreeOn s n
  proof: fun _t _ => hG _

中文:
定理 CliqueFree.cliqueFreeOn
  条件: (hG : G.CliqueFree n)
  结论: G.CliqueFreeOn s n
  证明: fun _t _ => hG _
-/
protected theorem CliqueFree.cliqueFreeOn (hG : G.CliqueFree n) : G.CliqueFreeOn s n :=
  fun _t _ => hG _

/--
theorem `cliqueFreeOn_of_card_lt` / 定理 `cliqueFreeOn_of_card_lt`

English:
theorem cliqueFreeOn_of_card_lt
  given: {s : Finset α} (h : #s < n)
  statement: G.CliqueFreeOn s n
  proof: fun _t hts ht => h.not_ge ht.2.symm.trans_le card_mono hts

中文:
定理 cliqueFreeOn_of_card_lt
  条件: {s : 有限集 α} (h : #s < n)
  结论: G.CliqueFreeOn s n
  证明: fun _t hts ht => h.not_ge ht.2.symm.trans_le card_mono hts

Depends on / 依赖: card_mono, h.not_ge, not_ge, symm.trans_le, trans_le
-/
theorem cliqueFreeOn_of_card_lt {s : Finset α} (h : #s < n) : G.CliqueFreeOn s n :=
fun _t hts ht => h.not_ge ht.2.symm.trans_le card_mono hts

-- TODO: Restate using `SimpleGraph.IndepSet` once we have it
@[simp]
/--
theorem `cliqueFreeOn_two` / 定理 `cliqueFreeOn_two`

English:
theorem cliqueFreeOn_two
  statement: G.CliqueFreeOn s 2 ↔ s.Pairwise (G.Adjᶜ)
  proof: by
  classical
  refine ⟨fun h a ha b hb _ hab => h ?_ ⟨by simpa [hab.ne], card_pair hab.ne⟩, ?_⟩
  · push_cast
    exact Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hb⟩
  simp only [CliqueFreeOn, isNClique_iff, card_eq_two, not_and, not_exists]
  rintro h t hst ht a b hab rfl
  simp onl

中文:
定理 cliqueFreeOn_two
  结论: G.CliqueFreeOn s 2 ↔ s.两两 (G.Adjᶜ)
  证明: by
  classical
  refine ⟨fun h a ha b hb _ hab => h ?_ ⟨by simpa [hab.ne], card_pair hab.ne⟩, ?_⟩
  · push_cast
    exact Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hb⟩
  simp only [CliqueFreeOn, isNClique_iff, card_eq_two, not_and, not_exists]
  rintro h t hst ht a b hab rfl
  simp onl

Depends on / 依赖: CliqueFreeOn, Set.insert_subset_iff, Set.singleton_subset_iff, card_eq_two, card_pair, classical, coe_insert, coe_singleton, hab.ne, insert_subset_iff, isNClique_iff, not_and, not_exists, singleton_subset_iff
-/
theorem cliqueFreeOn_two : G.CliqueFreeOn s 2 ↔ s.Pairwise (G.Adjᶜ) := by
  classical
  refine ⟨fun h a ha b hb _ hab => h ?_ ⟨by simpa [hab.ne], card_pair hab.ne⟩, ?_⟩
  · push_cast
    exact Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hb⟩
  simp only [CliqueFreeOn, isNClique_iff, card_eq_two, not_and, not_exists]
  rintro h t hst ht a b hab rfl
  simp only [coe_insert, coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff] at hst
  refine h hst.1 hst.2 hab (ht ?_ ?_ hab) <;> simp

/--
theorem `CliqueFreeOn.of_succ` / 定理 `CliqueFreeOn.of_succ`

English:
theorem CliqueFreeOn.of_succ
  given: (hs : G.CliqueFreeOn s (n + 1)) (ha : a in s)
  proof: by
  classical
  refine fun t hts ht => hs ?_ (ht.insert fun b hb => (hts hb).2)
  push_cast
  exact Set.insert_subset_iff.2 ⟨ha, hts.trans Set.inter_subset_left⟩

中文:
定理 CliqueFreeOn.of_succ
  条件: (hs : G.CliqueFreeOn s (n + 1)) (ha : a in s)
  证明: by
  classical
  refine fun t hts ht => hs ?_ (ht.insert fun b hb => (hts hb).2)
  push_cast
  exact Set.insert_subset_iff.2 ⟨ha, hts.trans Set.inter_subset_left⟩

Depends on / 依赖: Set.insert_subset_iff, Set.inter_subset_left, classical, ht.insert, hts.trans, insert, insert_subset_iff, inter_subset_left
-/
theorem CliqueFreeOn.of_succ (hs : G.CliqueFreeOn s (n + 1)) (ha : a in s) :
    G.CliqueFreeOn (s inter G.neighborSet a) n := by
  classical
  refine fun t hts ht => hs ?_ (ht.insert fun b hb => (hts hb).2)
  push_cast
  exact Set.insert_subset_iff.2 ⟨ha, hts.trans Set.inter_subset_left⟩

/--
theorem `cliqueFree_induce_iff` / 定理 `cliqueFree_induce_iff`

English:
theorem cliqueFree_induce_iff
  given: (s : Set α) (n : Nat)
  proof: by
  classical
  simp only [CliqueFree, isNClique_induce_iff]
  refine ⟨fun h t ht => ?_, (· <| map_subtype_subset ·)⟩
have := h t.subtype _
  rwa [← filter_eq_self.mpr ht, ← subtype_map]

中文:
定理 cliqueFree_induce_iff
  条件: (s : 集合 α) (n : 自然数)
  证明: by
  classical
  simp only [CliqueFree, isNClique_induce_iff]
  refine ⟨fun h t ht => ?_, (· <| map_subtype_subset ·)⟩
have := h t.subtype _
  rwa [← filter_eq_self.mpr ht, ← subtype_map]

Depends on / 依赖: CliqueFree, classical, filter_eq_self, filter_eq_self.mpr, isNClique_induce_iff, map_subtype_subset, subtype, subtype_map, t.subtype
-/
theorem cliqueFree_induce_iff (s : Set α) (n : Nat) :
    (G.induce s).CliqueFree n ↔ G.CliqueFreeOn s n := by
  classical
  simp only [CliqueFree, isNClique_induce_iff]
  refine ⟨fun h t ht => ?_, (· <| map_subtype_subset ·)⟩
have := h t.subtype _
  rwa [← filter_eq_self.mpr ht, ← subtype_map]

end CliqueFreeOn

/-! ### Set of cliques -/


section CliqueSet

variable {n : Nat} {s : Finset α}

/--
Definition of `cliqueSet` / `cliqueSet` 的定义

English:
definition cliqueSet
  signature: (n : Nat)
  body: { s | G.IsNClique n s }

中文:
定义 cliqueSet
  签名: (n : 自然数)
  定义体: { s | G.IsNClique n s }

Depends on / 依赖: G.IsNClique, IsNClique
-/
def cliqueSet (n : Nat) : Set (Finset α) :=
  { s | G.IsNClique n s }

variable {G H}

@[simp]
/--
theorem `mem_cliqueSet_iff` / 定理 `mem_cliqueSet_iff`

English:
theorem mem_cliqueSet_iff
  statement: s in G.cliqueSet n ↔ G.IsNClique n s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_cliqueSet_iff
  结论: s in G.cliqueSet n ↔ G.是NClique n s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_cliqueSet_iff : s in G.cliqueSet n ↔ G.IsNClique n s :=
  Iff.rfl

@[simp]
/--
theorem `cliqueSet_eq_empty_iff` / 定理 `cliqueSet_eq_empty_iff`

English:
theorem cliqueSet_eq_empty_iff
  statement: G.cliqueSet n = ∅ ↔ G.CliqueFree n
  proof: by
  simp_rw [CliqueFree, Set.eq_empty_iff_forall_notMem, mem_cliqueSet_iff]

protected alias ⟨_, CliqueFree.cliqueSet⟩ := cliqueSet_eq_empty_iff

@[gcongr, mono]

中文:
定理 cliqueSet_eq_empty_iff
  结论: G.cliqueSet n = ∅ ↔ G.CliqueFree n
  证明: by
  simp_rw [CliqueFree, Set.eq_empty_iff_forall_notMem, mem_cliqueSet_iff]

protected alias ⟨_, CliqueFree.cliqueSet⟩ := cliqueSet_eq_empty_iff

@[gcongr, mono]

Depends on / 依赖: CliqueFree, Set.eq_empty_iff_forall_notMem, eq_empty_iff_forall_notMem, mem_cliqueSet_iff, simp_rw
-/
theorem cliqueSet_eq_empty_iff : G.cliqueSet n = ∅ ↔ G.CliqueFree n := by
  simp_rw [CliqueFree, Set.eq_empty_iff_forall_notMem, mem_cliqueSet_iff]

protected alias ⟨_, CliqueFree.cliqueSet⟩ := cliqueSet_eq_empty_iff

@[gcongr, mono]
/--
theorem `cliqueSet_mono` / 定理 `cliqueSet_mono`

English:
theorem cliqueSet_mono
  given: (h : G <= H)
  statement: G.cliqueSet n subseteq H.cliqueSet n
  proof: fun _ => IsNClique.mono h

中文:
定理 cliqueSet_mono
  条件: (h : G <= H)
  结论: G.cliqueSet n subseteq H.cliqueSet n
  证明: fun _ => IsNClique.mono h

Depends on / 依赖: IsNClique, IsNClique.mono
-/
theorem cliqueSet_mono (h : G <= H) : G.cliqueSet n subseteq H.cliqueSet n :=
  fun _ => IsNClique.mono h

/--
theorem `cliqueSet_mono'` / 定理 `cliqueSet_mono'`

English:
theorem cliqueSet_mono'
  given: (h : G <= H)
  statement: G.cliqueSet <= H.cliqueSet
  proof: fun _ => cliqueSet_mono h

@[simp]

中文:
定理 cliqueSet_mono'
  条件: (h : G <= H)
  结论: G.cliqueSet <= H.cliqueSet
  证明: fun _ => cliqueSet_mono h

@[simp]

Depends on / 依赖: cliqueSet_mono
-/
theorem cliqueSet_mono' (h : G <= H) : G.cliqueSet <= H.cliqueSet :=
  fun _ => cliqueSet_mono h

@[simp]
/--
theorem `cliqueSet_zero` / 定理 `cliqueSet_zero`

English:
theorem cliqueSet_zero
  given: (G : SimpleGraph α)
  statement: G.cliqueSet 0 = {∅}
  proof: Set.ext fun s => by simp

@[simp]

中文:
定理 cliqueSet_zero
  条件: (G : 简单图 α)
  结论: G.cliqueSet 0 = {∅}
  证明: Set.ext fun s => by simp

@[simp]

Depends on / 依赖: Set.ext
-/
theorem cliqueSet_zero (G : SimpleGraph α) : G.cliqueSet 0 = {∅} := Set.ext fun s => by simp

@[simp]
/--
theorem `cliqueSet_one` / 定理 `cliqueSet_one`

English:
theorem cliqueSet_one
  given: (G : SimpleGraph α)
  statement: G.cliqueSet 1 = Set.range singleton
  proof: Set.ext fun s => by simp [eq_comm]

@[simp]

中文:
定理 cliqueSet_one
  条件: (G : 简单图 α)
  结论: G.cliqueSet 1 = 集合.range singleton
  证明: Set.ext fun s => by simp [eq_comm]

@[simp]

Depends on / 依赖: Set.ext, eq_comm
-/
theorem cliqueSet_one (G : SimpleGraph α) : G.cliqueSet 1 = Set.range singleton :=
  Set.ext fun s => by simp [eq_comm]

@[simp]
/--
theorem `cliqueSet_bot` / 定理 `cliqueSet_bot`

English:
theorem cliqueSet_bot
  given: (hn : 1 < n)
  statement: (⊥ : SimpleGraph α).cliqueSet n = ∅
  proof: (cliqueFree_bot hn).cliqueSet

@[simp]

中文:
定理 cliqueSet_bot
  条件: (hn : 1 < n)
  结论: (⊥ : 简单图 α).cliqueSet n = ∅
  证明: (cliqueFree_bot hn).cliqueSet

@[simp]

Depends on / 依赖: cliqueFree_bot, cliqueSet
-/
theorem cliqueSet_bot (hn : 1 < n) : (⊥ : SimpleGraph α).cliqueSet n = ∅ :=
  (cliqueFree_bot hn).cliqueSet

@[simp]
/--
theorem `cliqueSet_map` / 定理 `cliqueSet_map`

English:
theorem cliqueSet_map
  given: (hn : n != 1) (G : SimpleGraph α) (f : α ↪ β)
  proof: by
  ext s
  constructor
  · rintro ⟨hs, rfl⟩
    have hs' : (s.preimage f f.injective.injOn).map f = s := by
      classical
      rw [map_eq_image]; rw [image_preimage]; rw [filter_true_of_mem]
      rintro a ha
      obtain ⟨b, hb, hba⟩ := exists_mem_ne (hn.lt_of_le' <| Finset.card_pos.2 ⟨a, ha⟩)

中文:
定理 cliqueSet_map
  条件: (hn : n != 1) (G : 简单图 α) (f : α ↪ β)
  证明: by
  ext s
  constructor
  · rintro ⟨hs, rfl⟩
    have hs' : (s.preimage f f.injective.injOn).map f = s := by
      classical
      rw [map_eq_image]; rw [image_preimage]; rw [filter_true_of_mem]
      rintro a ha
      obtain ⟨b, hb, hba⟩ := exists_mem_ne (hn.lt_of_le' <| Finset.card_pos.2 ⟨a, ha⟩)

Depends on / 依赖: Finset, Finset.card_pos, card_map, card_pos, classical, coe_preimage, exists_mem_ne, f.injective.injOn, f.injective.ne, filter_true_of_mem, hba.symm, hn.lt_of_le, image_preimage, injective, lt_of_le, map_adj_apply, map_eq_image, preimage, s.preimage
-/
theorem cliqueSet_map (hn : n != 1) (G : SimpleGraph α) (f : α ↪ β) :
    (G.map f).cliqueSet n = map f '' G.cliqueSet n := by
  ext s
  constructor
  · rintro ⟨hs, rfl⟩
    have hs' : (s.preimage f f.injective.injOn).map f = s := by
      classical
      rw [map_eq_image]; rw [image_preimage]; rw [filter_true_of_mem]
      rintro a ha
      obtain ⟨b, hb, hba⟩ := exists_mem_ne (hn.lt_of_le' <| Finset.card_pos.2 ⟨a, ha⟩) a
      obtain ⟨-, c, _, _, hc, _⟩ := hs ha hb hba.symm
      exact ⟨c, hc⟩
    refine ⟨s.preimage f f.injective.injOn, ⟨?_, by rw [← card_map f, hs']⟩, hs'⟩
    rw [coe_preimage]
    exact fun a ha b hb hab => map_adj_apply.1 (hs ha hb <| f.injective.ne hab)
  · rintro ⟨s, hs, rfl⟩
    exact hs.map

@[simp]
/--
theorem `cliqueSet_map_of_equiv` / 定理 `cliqueSet_map_of_equiv`

English:
theorem cliqueSet_map_of_equiv
  given: (G : SimpleGraph α) (e : α ≃ β) (n : Nat)
  proof: by
  obtain rfl | hn := eq_or_ne n 1
  · ext
    simp [e.exists_congr_left]
  · simpa using cliqueSet_map hn G e.toEmbedding

中文:
定理 cliqueSet_map_of_equiv
  条件: (G : 简单图 α) (e : α ≃ β) (n : 自然数)
  证明: by
  obtain rfl | hn := eq_or_ne n 1
  · ext
    simp [e.exists_congr_left]
  · simpa using cliqueSet_map hn G e.toEmbedding

Depends on / 依赖: cliqueSet_map, e.exists_congr_left, e.toEmbedding, eq_or_ne, exists_congr_left, toEmbedding
-/
theorem cliqueSet_map_of_equiv (G : SimpleGraph α) (e : α ≃ β) (n : Nat) :
    (G.map e).cliqueSet n = map e.toEmbedding '' G.cliqueSet n := by
  obtain rfl | hn := eq_or_ne n 1
  · ext
    simp [e.exists_congr_left]
  · simpa using cliqueSet_map hn G e.toEmbedding

end CliqueSet

/-! ### Clique number -/


section CliqueNumber

variable {α : Type*} {G : SimpleGraph α}

/--
Definition of `cliqueNum` / `cliqueNum` 的定义

English:
definition cliqueNum
  signature: (G : SimpleGraph α)
  body: sSup {n | exists s, G.IsNClique n s}

中文:
定义 cliqueNum
  签名: (G : 简单图 α)
  定义体: sSup {n | exists s, G.IsNClique n s}

Depends on / 依赖: G.IsNClique, IsNClique
-/
noncomputable def cliqueNum (G : SimpleGraph α) : Nat := sSup {n | exists s, G.IsNClique n s}

/--
lemma `finite_cliqueNum_bddAbove` / 引理 `finite_cliqueNum_bddAbove`

English:
lemma finite_cliqueNum_bddAbove
  given: [Finite α]
  statement: BddAbove {n | exists s, G.IsNClique n s}
  proof: by
  have := ofFinite α
  use card α
  rintro y ⟨s, syc⟩
  rw [isNClique_iff] at syc
  rw [← syc.right]
  exact Finset.card_le_card (Finset.subset_univ s)

中文:
引理 finite_cliqueNum_bddAbove
  条件: [有限 α]
  结论: BddAbove {n | 存在 s, G.是NClique n s}
  证明: by
  have := ofFinite α
  use card α
  rintro y ⟨s, syc⟩
  rw [isNClique_iff] at syc
  rw [← syc.right]
  exact Finset.card_le_card (Finset.subset_univ s)
-/
private lemma finite_cliqueNum_bddAbove [Finite α] : BddAbove {n | exists s, G.IsNClique n s} := by
  have := ofFinite α
  use card α
  rintro y ⟨s, syc⟩
  rw [isNClique_iff] at syc
  rw [← syc.right]
  exact Finset.card_le_card (Finset.subset_univ s)

/--
lemma `IsClique.card_le_cliqueNum` / 引理 `IsClique.card_le_cliqueNum`

English:
lemma IsClique.card_le_cliqueNum
  given: [Finite α] {t : Finset α} {tc : G.IsClique t}
  proof: by
  exact le_csSup G.finite_cliqueNum_bddAbove (Exists.intro t ⟨tc, rfl⟩)

中文:
引理 IsClique.card_le_cliqueNum
  条件: [有限 α] {t : 有限集 α} {tc : G.IsClique t}
  证明: by
  exact le_csSup G.finite_cliqueNum_bddAbove (Exists.intro t ⟨tc, rfl⟩)

Depends on / 依赖: Exists, Exists.intro, G.finite_cliqueNum_bddAbove, finite_cliqueNum_bddAbove, le_csSup
-/
lemma IsClique.card_le_cliqueNum [Finite α] {t : Finset α} {tc : G.IsClique t} :
    #t <= G.cliqueNum := by
  exact le_csSup G.finite_cliqueNum_bddAbove (Exists.intro t ⟨tc, rfl⟩)

/--
lemma `exists_isNClique_cliqueNum` / 引理 `exists_isNClique_cliqueNum`

English:
lemma exists_isNClique_cliqueNum
  statement: exists s, G.IsNClique G.cliqueNum s
  proof: by
  by_cases h : BddAbove {n | exists s, G.IsNClique n s}
  · exact Nat.sSup_mem ⟨0, by simp⟩ h
  · simp [cliqueNum, h]

中文:
引理 存在_isNClique_cliqueNum
  结论: 存在 s, G.是NClique G.cliqueNum s
  证明: by
  by_cases h : BddAbove {n | exists s, G.IsNClique n s}
  · exact Nat.sSup_mem ⟨0, by simp⟩ h
  · simp [cliqueNum, h]

Depends on / 依赖: BddAbove, G.IsNClique, IsNClique, Nat.sSup_mem, cliqueNum, sSup_mem
-/
lemma exists_isNClique_cliqueNum : exists s, G.IsNClique G.cliqueNum s := by
  by_cases h : BddAbove {n | exists s, G.IsNClique n s}
  · exact Nat.sSup_mem ⟨0, by simp⟩ h
  · simp [cliqueNum, h]

/--
theorem `cliqueNum_induce_le` / 定理 `cliqueNum_induce_le`

English:
theorem cliqueNum_induce_le
  given: [Finite α] (s : Set α)
  proof: by
  have ⟨t', tc⟩ := (G.induce s).exists_isNClique_cliqueNum
  rw [isNClique_induce_iff] at tc
  exact tc.card_eq ▸ tc.isClique.card_le_cliqueNum

中文:
定理 cliqueNum_induce_le
  条件: [有限 α] (s : 集合 α)
  证明: by
  have ⟨t', tc⟩ := (G.induce s).exists_isNClique_cliqueNum
  rw [isNClique_induce_iff] at tc
  exact tc.card_eq ▸ tc.isClique.card_le_cliqueNum

Depends on / 依赖: G.induce, card_eq, card_le_cliqueNum, exists_isNClique_cliqueNum, induce, isClique, isNClique_induce_iff, tc.card_eq, tc.isClique.card_le_cliqueNum
-/
theorem cliqueNum_induce_le [Finite α] (s : Set α) :
    (G.induce s).cliqueNum <= G.cliqueNum := by
  have ⟨t', tc⟩ := (G.induce s).exists_isNClique_cliqueNum
  rw [isNClique_induce_iff] at tc
  exact tc.card_eq ▸ tc.isClique.card_le_cliqueNum

-- TODO: replace with `MaximalFor (G.IsClique ∘ (↑)) card s`
/--
Definition of `IsMaximumClique` / `IsMaximumClique` 的定义

English:
structure IsMaximumClique
  parameters: [Finite α] (G : SimpleGraph α) (s : Finset α)
  axioms and operations (2):
    - isClique : G.IsClique s
    - maximum : forall t : Finset α, G.IsClique t -> #t <= #s

中文:
结构 是MaximumClique
  参数: [有限 α] (G : 简单图 α) (s : 有限集 α)
  公理与运算 (2 个):
    - isClique : G.IsClique s
    - maximum : 对任意 t : 有限集 α, G.IsClique t -> #t <= #s
-/
structure IsMaximumClique [Finite α] (G : SimpleGraph α) (s : Finset α) : Prop where
  isClique : G.IsClique s
  maximum : forall t : Finset α, G.IsClique t -> #t <= #s

/--
theorem `isMaximumClique_iff` / 定理 `isMaximumClique_iff`

English:
theorem isMaximumClique_iff
  given: [Finite α] {s : Finset α}
  proof: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

中文:
定理 isMaximumClique_iff
  条件: [有限 α] {s : 有限集 α}
  证明: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
-/
theorem isMaximumClique_iff [Finite α] {s : Finset α} :
    G.IsMaximumClique s ↔ G.IsClique s ∧ forall t : Finset α, G.IsClique t -> #t <= #s :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/--
theorem `isMaximalClique_iff` / 定理 `isMaximalClique_iff`

English:
theorem isMaximalClique_iff
  given: {s : Set α}
  proof: Iff.rfl

中文:
定理 isMaximalClique_iff
  条件: {s : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isMaximalClique_iff {s : Set α} :
    Maximal G.IsClique s ↔ G.IsClique s ∧ forall t : Set α, G.IsClique t -> s subseteq t -> t subseteq s :=
  Iff.rfl

/--
lemma `IsMaximumClique.isMaximalClique` / 引理 `IsMaximumClique.isMaximalClique`

English:
lemma IsMaximumClique.isMaximalClique
  given: [Finite α] (s : Finset α) (M : G.IsMaximumClique s)
  proof: ⟨ M.isClique,
    fun t ht hsub => by
      by_contra hc
      have fint := ofFinite t
      have ne : s != t.toFinset := fun a => by subst a; simp_all[Set.coe_toFinset, not_true_eq_false]
      have hle : #t.toFinset <= #s := M.maximum t.toFinset (by simp [Set.coe_toFinset, ht])
      have hlt : #s

中文:
引理 是MaximumClique.isMaximalClique
  条件: [有限 α] (s : 有限集 α) (M : G.是MaximumClique s)
  证明: ⟨ M.isClique,
    fun t ht hsub => by
      by_contra hc
      have fint := ofFinite t
      have ne : s != t.toFinset := fun a => by subst a; simp_all[Set.coe_toFinset, not_true_eq_false]
      have hle : #t.toFinset <= #s := M.maximum t.toFinset (by simp [Set.coe_toFinset, ht])
      have hlt : #s

Depends on / 依赖: M.isClique, M.maximum, Set.coe_toFinset, Set.subset_toFinset.mpr, card_lt_card, coe_toFinset, isClique, lt_irrefl, lt_of_lt_of_le, maximum, not_true_eq_false, ofFinite, ssubset_of_ne_of_subset, subset_toFinset, t.toFinset, toFinset
-/
lemma IsMaximumClique.isMaximalClique [Finite α] (s : Finset α) (M : G.IsMaximumClique s) :
    Maximal G.IsClique s :=
  ⟨ M.isClique,
    fun t ht hsub => by
      by_contra hc
      have fint := ofFinite t
      have ne : s != t.toFinset := fun a => by subst a; simp_all[Set.coe_toFinset, not_true_eq_false]
      have hle : #t.toFinset <= #s := M.maximum t.toFinset (by simp [Set.coe_toFinset, ht])
      have hlt : #s < #t.toFinset :=
        card_lt_card (ssubset_of_ne_of_subset ne (Set.subset_toFinset.mpr hsub))
      exact lt_irrefl _ (lt_of_lt_of_le hlt hle) ⟩

/--
lemma `maximumClique_card_eq_cliqueNum` / 引理 `maximumClique_card_eq_cliqueNum`

English:
lemma maximumClique_card_eq_cliqueNum
  given: [Finite α] (s : Finset α) (sm : G.IsMaximumClique s)
  proof: by
  obtain ⟨sc, sm⟩ := sm
  obtain ⟨t, tc, tcard⟩ := G.exists_isNClique_cliqueNum
  exact eq_of_le_of_not_lt sc.card_le_cliqueNum (by simp [← tcard, sm t tc])

中文:
引理 maximumClique_card_eq_cliqueNum
  条件: [有限 α] (s : 有限集 α) (sm : G.是MaximumClique s)
  证明: by
  obtain ⟨sc, sm⟩ := sm
  obtain ⟨t, tc, tcard⟩ := G.exists_isNClique_cliqueNum
  exact eq_of_le_of_not_lt sc.card_le_cliqueNum (by simp [← tcard, sm t tc])

Depends on / 依赖: G.exists_isNClique_cliqueNum, card_le_cliqueNum, eq_of_le_of_not_lt, exists_isNClique_cliqueNum, sc.card_le_cliqueNum
-/
lemma maximumClique_card_eq_cliqueNum [Finite α] (s : Finset α) (sm : G.IsMaximumClique s) :
    #s = G.cliqueNum := by
  obtain ⟨sc, sm⟩ := sm
  obtain ⟨t, tc, tcard⟩ := G.exists_isNClique_cliqueNum
  exact eq_of_le_of_not_lt sc.card_le_cliqueNum (by simp [← tcard, sm t tc])

/--
lemma `maximumClique_exists` / 引理 `maximumClique_exists`

English:
lemma maximumClique_exists
  given: [Finite α]
  statement: exists (s : Finset α), G.IsMaximumClique s
  proof: by
  obtain ⟨s, snc⟩ := G.exists_isNClique_cliqueNum
  exact ⟨s, ⟨snc.isClique, fun t ht => snc.card_eq.symm ▸ ht.card_le_cliqueNum⟩⟩

中文:
引理 maximumClique_存在
  条件: [有限 α]
  结论: 存在 (s : 有限集 α), G.是MaximumClique s
  证明: by
  obtain ⟨s, snc⟩ := G.exists_isNClique_cliqueNum
  exact ⟨s, ⟨snc.isClique, fun t ht => snc.card_eq.symm ▸ ht.card_le_cliqueNum⟩⟩

Depends on / 依赖: G.exists_isNClique_cliqueNum, card_eq, card_le_cliqueNum, exists_isNClique_cliqueNum, ht.card_le_cliqueNum, isClique, snc.card_eq.symm, snc.isClique
-/
lemma maximumClique_exists [Finite α] : exists (s : Finset α), G.IsMaximumClique s := by
  obtain ⟨s, snc⟩ := G.exists_isNClique_cliqueNum
  exact ⟨s, ⟨snc.isClique, fun t ht => snc.card_eq.symm ▸ ht.card_le_cliqueNum⟩⟩

end CliqueNumber

/-! ### Finset of cliques -/


section CliqueFinset

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : Nat} {s : Finset α}

/--
Definition of `cliqueFinset` / `cliqueFinset` 的定义

English:
definition cliqueFinset
  signature: (n : Nat)
  body: {s | G.IsNClique n s}

中文:
定义 cliqueFinset
  签名: (n : 自然数)
  定义体: {s | G.IsNClique n s}

Depends on / 依赖: G.IsNClique, IsNClique
-/
def cliqueFinset (n : Nat) : Finset (Finset α) := {s | G.IsNClique n s}

variable {G} in
@[simp]
/--
theorem `mem_cliqueFinset_iff` / 定理 `mem_cliqueFinset_iff`

English:
theorem mem_cliqueFinset_iff
  statement: s in G.cliqueFinset n ↔ G.IsNClique n s
  proof: mem_filter.trans and_iff_right mem_univ _

@[simp, norm_cast]

中文:
定理 mem_cliqueFinset_iff
  结论: s in G.cliqueFinset n ↔ G.是NClique n s
  证明: mem_filter.trans and_iff_right mem_univ _

@[simp, norm_cast]

Depends on / 依赖: and_iff_right, mem_filter, mem_filter.trans, mem_univ
-/
theorem mem_cliqueFinset_iff : s in G.cliqueFinset n ↔ G.IsNClique n s :=
mem_filter.trans and_iff_right mem_univ _

@[simp, norm_cast]
/--
theorem `coe_cliqueFinset` / 定理 `coe_cliqueFinset`

English:
theorem coe_cliqueFinset
  given: (n : Nat)
  statement: (G.cliqueFinset n : Set (Finset α)) = G.cliqueSet n
  proof: Set.ext fun _ => mem_cliqueFinset_iff

中文:
定理 coe_cliqueFinset
  条件: (n : 自然数)
  结论: (G.cliqueFinset n : 集合 (有限集 α)) = G.cliqueSet n
  证明: Set.ext fun _ => mem_cliqueFinset_iff

Depends on / 依赖: Set.ext, mem_cliqueFinset_iff
-/
theorem coe_cliqueFinset (n : Nat) : (G.cliqueFinset n : Set (Finset α)) = G.cliqueSet n :=
  Set.ext fun _ => mem_cliqueFinset_iff

variable {G}

@[simp]
/--
theorem `cliqueFinset_eq_empty_iff` / 定理 `cliqueFinset_eq_empty_iff`

English:
theorem cliqueFinset_eq_empty_iff
  statement: G.cliqueFinset n = ∅ ↔ G.CliqueFree n
  proof: by
  simp_rw [CliqueFree, eq_empty_iff_forall_notMem, mem_cliqueFinset_iff]

protected alias ⟨_, CliqueFree.cliqueFinset⟩ := cliqueFinset_eq_empty_iff

中文:
定理 cliqueFinset_eq_empty_iff
  结论: G.cliqueFinset n = ∅ ↔ G.CliqueFree n
  证明: by
  simp_rw [CliqueFree, eq_empty_iff_forall_notMem, mem_cliqueFinset_iff]

protected alias ⟨_, CliqueFree.cliqueFinset⟩ := cliqueFinset_eq_empty_iff

Depends on / 依赖: CliqueFree, eq_empty_iff_forall_notMem, mem_cliqueFinset_iff, simp_rw
-/
theorem cliqueFinset_eq_empty_iff : G.cliqueFinset n = ∅ ↔ G.CliqueFree n := by
  simp_rw [CliqueFree, eq_empty_iff_forall_notMem, mem_cliqueFinset_iff]

protected alias ⟨_, CliqueFree.cliqueFinset⟩ := cliqueFinset_eq_empty_iff

/--
theorem `card_cliqueFinset_le` / 定理 `card_cliqueFinset_le`

English:
theorem card_cliqueFinset_le
  statement: #(G.cliqueFinset n) <= (card α).choose n
  proof: by
  rw [← card_univ]; rw [← card_powersetCard]
  refine card_mono fun s => ?_
  simpa [mem_powersetCard_univ] using IsNClique.card_eq

中文:
定理 card_cliqueFinset_le
  结论: #(G.cliqueFinset n) <= (card α).choose n
  证明: by
  rw [← card_univ]; rw [← card_powersetCard]
  refine card_mono fun s => ?_
  simpa [mem_powersetCard_univ] using IsNClique.card_eq

Depends on / 依赖: IsNClique, IsNClique.card_eq, card_eq, card_mono, card_powersetCard, card_univ, mem_powersetCard_univ
-/
theorem card_cliqueFinset_le : #(G.cliqueFinset n) <= (card α).choose n := by
  rw [← card_univ]; rw [← card_powersetCard]
  refine card_mono fun s => ?_
  simpa [mem_powersetCard_univ] using IsNClique.card_eq

variable [DecidableRel H.Adj]

@[gcongr, mono]
/--
theorem `cliqueFinset_mono` / 定理 `cliqueFinset_mono`

English:
theorem cliqueFinset_mono
  given: (h : G <= H)
  statement: G.cliqueFinset n subseteq H.cliqueFinset n
  proof: monotone_filter_right _ fun _ _ => IsNClique.mono h

中文:
定理 cliqueFinset_mono
  条件: (h : G <= H)
  结论: G.cliqueFinset n subseteq H.cliqueFinset n
  证明: monotone_filter_right _ fun _ _ => IsNClique.mono h

Depends on / 依赖: IsNClique, IsNClique.mono, monotone_filter_right
-/
theorem cliqueFinset_mono (h : G <= H) : G.cliqueFinset n subseteq H.cliqueFinset n :=
  monotone_filter_right _ fun _ _ => IsNClique.mono h

variable [Fintype β] [DecidableEq β] (G)

@[simp]
/--
theorem `cliqueFinset_map` / 定理 `cliqueFinset_map`

English:
theorem cliqueFinset_map
  given: (f : α ↪ β) (hn : n != 1)
  proof: coe_injective by
    simp_rw [coe_cliqueFinset, cliqueSet_map hn, coe_map, coe_cliqueFinset, Embedding.coeFn_mk]

@[simp]

中文:
定理 cliqueFinset_map
  条件: (f : α ↪ β) (hn : n != 1)
  证明: coe_injective by
    simp_rw [coe_cliqueFinset, cliqueSet_map hn, coe_map, coe_cliqueFinset, Embedding.coeFn_mk]

@[simp]

Depends on / 依赖: Embedding, Embedding.coeFn_mk, cliqueSet_map, coeFn_mk, coe_cliqueFinset, coe_injective, coe_map, simp_rw
-/
theorem cliqueFinset_map (f : α ↪ β) (hn : n != 1) :
    (G.map f).cliqueFinset n = (G.cliqueFinset n).map ⟨map f, Finset.map_injective _⟩ :=
coe_injective by
    simp_rw [coe_cliqueFinset, cliqueSet_map hn, coe_map, coe_cliqueFinset, Embedding.coeFn_mk]

@[simp]
/--
theorem `cliqueFinset_map_of_equiv` / 定理 `cliqueFinset_map_of_equiv`

English:
theorem cliqueFinset_map_of_equiv
  given: (e : α ≃ β) (n : Nat)
  statement: (G.map e).cliqueFinset n =
  proof: coe_injective by push_cast; exact cliqueSet_map_of_equiv _ _ _

中文:
定理 cliqueFinset_map_of_equiv
  条件: (e : α ≃ β) (n : 自然数)
  结论: (G.map e).cliqueFinset n =
  证明: coe_injective by push_cast; exact cliqueSet_map_of_equiv _ _ _

Depends on / 依赖: cliqueSet_map_of_equiv, coe_injective
-/
theorem cliqueFinset_map_of_equiv (e : α ≃ β) (n : Nat) : (G.map e).cliqueFinset n =
      (G.cliqueFinset n).map ⟨map e.toEmbedding, Finset.map_injective _⟩ :=
coe_injective by push_cast; exact cliqueSet_map_of_equiv _ _ _

end CliqueFinset

/-! ### Independent Sets -/

section IndepSet

variable {s : Set α}

/-- An independent set in a graph is a set of vertices that are pairwise not adjacent. -/
@[wikidata Q1060343]
/--
Definition of `IsIndepSet` / `IsIndepSet` 的定义

English:
abbreviation IsIndepSet
  signature: (s : Set α)
  body: s.Pairwise (fun v w => ¬G.Adj v w)

中文:
缩写 IsIndepSet
  签名: (s : 集合 α)
  定义体: s.Pairwise (fun v w => ¬G.Adj v w)

Depends on / 依赖: G.Adj, Pairwise, s.Pairwise
-/
abbrev IsIndepSet (s : Set α) : Prop :=
  s.Pairwise (fun v w => ¬G.Adj v w)

/--
theorem `isIndepSet_iff` / 定理 `isIndepSet_iff`

English:
theorem isIndepSet_iff
  statement: G.IsIndepSet s ↔ s.Pairwise (fun v w => ¬G.Adj v w)
  proof: .rfl

中文:
定理 isIndepSet_iff
  结论: G.IsIndepSet s ↔ s.两两 (fun v w => ¬G.伴随 v w)
  证明: .rfl
-/
theorem isIndepSet_iff : G.IsIndepSet s ↔ s.Pairwise (fun v w => ¬G.Adj v w) :=
  .rfl

/--
theorem `isIndepSet_iff_isAntichain_adj` / 定理 `isIndepSet_iff_isAntichain_adj`

English:
theorem isIndepSet_iff_isAntichain_adj
  statement: G.IsIndepSet s ↔ IsAntichain G.Adj s
  proof: .rfl

中文:
定理 isIndepSet_iff_isAntichain_adj
  结论: G.IsIndepSet s ↔ IsAntichain G.伴随 s
  证明: .rfl
-/
theorem isIndepSet_iff_isAntichain_adj : G.IsIndepSet s ↔ IsAntichain G.Adj s :=
  .rfl

/--
theorem `isClique_compl` / 定理 `isClique_compl`

English:
theorem isClique_compl
  statement: Gᶜ.IsClique s ↔ G.IsIndepSet s
  proof: by
  rw [isIndepSet_iff]; rw [isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]

中文:
定理 isClique_compl
  结论: Gᶜ.IsClique s ↔ G.IsIndepSet s
  证明: by
  rw [isIndepSet_iff]; rw [isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]
-/
@[simp] theorem isClique_compl : Gᶜ.IsClique s ↔ G.IsIndepSet s := by
  rw [isIndepSet_iff]; rw [isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]

/--
theorem `isIndepSet_compl` / 定理 `isIndepSet_compl`

English:
theorem isIndepSet_compl
  statement: Gᶜ.IsIndepSet s ↔ G.IsClique s
  proof: by
  rw [isIndepSet_iff]; rw [isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]

中文:
定理 isIndepSet_compl
  结论: Gᶜ.IsIndepSet s ↔ G.IsClique s
  证明: by
  rw [isIndepSet_iff]; rw [isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]
-/
@[simp] theorem isIndepSet_compl : Gᶜ.IsIndepSet s ↔ G.IsClique s := by
  rw [isIndepSet_iff]; rw [isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] [DecidableRel G.Adj] {s
  body: decidable_of_iff' _ G.isIndepSet_iff

中文:
实例 [DecidableEq
  签名: α] [DecidableRel G.伴随] {s
  定义体: decidable_of_iff' _ G.isIndepSet_iff

Depends on / 依赖: G.isIndepSet_iff, decidable_of_iff, isIndepSet_iff
-/
instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsIndepSet s) :=
  decidable_of_iff' _ G.isIndepSet_iff

/--
lemma `IsIndepSet.nonempty_mem_compl_mem_edge` / 引理 `IsIndepSet.nonempty_mem_compl_mem_edge`

English:
lemma IsIndepSet.nonempty_mem_compl_mem_edge
  statement: {s : Set α} (indA : G.IsIndepSet s) {e}
  proof: by
  obtain ⟨v, w⟩ := e
  by_contra! c
  refine indA ?_ ?_ he.ne he
· exact Set.not_notMem.mp not_and'.mp (c ▸ Set.notMem_empty v) Sym2.mem_mk_left ..
· exact Set.not_notMem.mp not_and'.mp (c ▸ Set.notMem_empty w) Sym2.mem_mk_right ..

中文:
引理 IsIndepSet.nonempty_mem_compl_mem_edge
  结论: {s : 集合 α} (indA : G.IsIndepSet s) {e}
  证明: by
  obtain ⟨v, w⟩ := e
  by_contra! c
  refine indA ?_ ?_ he.ne he
· exact Set.not_notMem.mp not_and'.mp (c ▸ Set.notMem_empty v) Sym2.mem_mk_left ..
· exact Set.not_notMem.mp not_and'.mp (c ▸ Set.notMem_empty w) Sym2.mem_mk_right ..

Depends on / 依赖: Set.notMem_empty, Set.not_notMem.mp, Sym2.mem_mk_left, Sym2.mem_mk_right, he.ne, mem_mk_left, mem_mk_right, notMem_empty, not_and, not_notMem
-/
lemma IsIndepSet.nonempty_mem_compl_mem_edge {s : Set α} (indA : G.IsIndepSet s) {e}
    (he : e in G.edgeSet) : { b in sᶜ | b in e }.Nonempty := by
  obtain ⟨v, w⟩ := e
  by_contra! c
  refine indA ?_ ?_ he.ne he
· exact Set.not_notMem.mp not_and'.mp (c ▸ Set.notMem_empty v) Sym2.mem_mk_left ..
· exact Set.not_notMem.mp not_and'.mp (c ▸ Set.notMem_empty w) Sym2.mem_mk_right ..

/--
theorem `isIndepSet_neighborSet_of_triangleFree` / 定理 `isIndepSet_neighborSet_of_triangleFree`

English:
theorem isIndepSet_neighborSet_of_triangleFree
  given: (h : G.CliqueFree 3) (v : α)
  proof: by
  classical
  by_contra nind
  rw [IsIndepSet]; rw [Set.Pairwise] at nind
  push Not at nind
  simp_rw [mem_neighborSet] at nind
  obtain ⟨j, avj, k, avk, _, ajk⟩ := nind
  exact h {v, j, k} (is3Clique_triple_iff.mpr (by simp [avj, avk, ajk]))

中文:
定理 isIndepSet_neighborSet_of_triangleFree
  条件: (h : G.CliqueFree 3) (v : α)
  证明: by
  classical
  by_contra nind
  rw [IsIndepSet]; rw [Set.Pairwise] at nind
  push Not at nind
  simp_rw [mem_neighborSet] at nind
  obtain ⟨j, avj, k, avk, _, ajk⟩ := nind
  exact h {v, j, k} (is3Clique_triple_iff.mpr (by simp [avj, avk, ajk]))

Depends on / 依赖: IsIndepSet, Pairwise, Set.Pairwise, classical, is3Clique_triple_iff, is3Clique_triple_iff.mpr, mem_neighborSet, simp_rw
-/
theorem isIndepSet_neighborSet_of_triangleFree (h : G.CliqueFree 3) (v : α) :
    G.IsIndepSet (G.neighborSet v) := by
  classical
  by_contra nind
  rw [IsIndepSet]; rw [Set.Pairwise] at nind
  push Not at nind
  simp_rw [mem_neighborSet] at nind
  obtain ⟨j, avj, k, avk, _, ajk⟩ := nind
  exact h {v, j, k} (is3Clique_triple_iff.mpr (by simp [avj, avk, ajk]))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `isIndepSet_induce` / 定理 `isIndepSet_induce`

English:
theorem isIndepSet_induce
  given: {F : Set α} {s : Set F}
  proof: by
  simp [Set.Pairwise]

中文:
定理 isIndepSet_induce
  条件: {F : 集合 α} {s : 集合 F}
  证明: by
  simp [Set.Pairwise]

Depends on / 依赖: Pairwise, Set.Pairwise
-/
theorem isIndepSet_induce {F : Set α} {s : Set F} :
    ((⊤ : Subgraph G).induce F).coe.IsIndepSet s ↔ G.IsIndepSet (Subtype.val '' s) := by
  simp [Set.Pairwise]

end IndepSet

/-! ### N-Independent sets -/


section NIndepSet

variable {n : Nat} {s : Finset α}

/-- An `n`-independent set in a graph is a set of `n` vertices which are pairwise nonadjacent. -/
@[mk_iff]
/--
Definition of `IsNIndepSet` / `IsNIndepSet` 的定义

English:
structure IsNIndepSet
  parameters: (n : Nat) (s : Finset α)
  axioms and operations (2):
    - isIndepSet : G.IsIndepSet s
    - card_eq : s.card = n

中文:
结构 是NIndepSet
  参数: (n : 自然数) (s : 有限集 α)
  公理与运算 (2 个):
    - isIndepSet : G.IsIndepSet s
    - card_eq : s.card = n
-/
structure IsNIndepSet (n : Nat) (s : Finset α) : Prop where
  isIndepSet : G.IsIndepSet s
  card_eq : s.card = n

/--
theorem `isNClique_compl` / 定理 `isNClique_compl`

English:
theorem isNClique_compl
  statement: Gᶜ.IsNClique n s ↔ G.IsNIndepSet n s
  proof: by
  rw [isNIndepSet_iff]
  simp [isNClique_iff]

中文:
定理 isNClique_compl
  结论: Gᶜ.是NClique n s ↔ G.是NIndepSet n s
  证明: by
  rw [isNIndepSet_iff]
  simp [isNClique_iff]
-/
@[simp] theorem isNClique_compl : Gᶜ.IsNClique n s ↔ G.IsNIndepSet n s := by
  rw [isNIndepSet_iff]
  simp [isNClique_iff]

/--
theorem `isNIndepSet_compl` / 定理 `isNIndepSet_compl`

English:
theorem isNIndepSet_compl
  statement: Gᶜ.IsNIndepSet n s ↔ G.IsNClique n s
  proof: by
  rw [isNClique_iff]
  simp [isNIndepSet_iff]

中文:
定理 isNIndepSet_compl
  结论: Gᶜ.是NIndepSet n s ↔ G.是NClique n s
  证明: by
  rw [isNClique_iff]
  simp [isNIndepSet_iff]
-/
@[simp] theorem isNIndepSet_compl : Gᶜ.IsNIndepSet n s ↔ G.IsNClique n s := by
  rw [isNClique_iff]
  simp [isNIndepSet_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] [DecidableRel G.Adj] {n
  body: decidable_of_iff' _ (G.isNIndepSet_iff n s)

中文:
实例 [DecidableEq
  签名: α] [DecidableRel G.伴随] {n
  定义体: decidable_of_iff' _ (G.isNIndepSet_iff n s)

Depends on / 依赖: G.isNIndepSet_iff, decidable_of_iff, isNIndepSet_iff
-/
instance [DecidableEq α] [DecidableRel G.Adj] {n : Nat} {s : Finset α} :
    Decidable (G.IsNIndepSet n s) :=
  decidable_of_iff' _ (G.isNIndepSet_iff n s)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isNIndepSet_induce` / 定理 `isNIndepSet_induce`

English:
theorem isNIndepSet_induce
  given: {F : Set α} {s : Finset { x // x in F }} {n : Nat}
  proof: by
  simp [isNIndepSet_iff, (isIndepSet_induce)]

中文:
定理 isNIndepSet_induce
  条件: {F : 集合 α} {s : 有限集 { x // x in F }} {n : 自然数}
  证明: by
  simp [isNIndepSet_iff, (isIndepSet_induce)]

Depends on / 依赖: isIndepSet_induce, isNIndepSet_iff
-/
theorem isNIndepSet_induce {F : Set α} {s : Finset { x // x in F }} {n : Nat} :
    ((⊤ : Subgraph G).induce F).coe.IsNIndepSet n ↑s ↔
    G.IsNIndepSet n (Finset.map ⟨Subtype.val, Subtype.val_injective⟩ s) := by
  simp [isNIndepSet_iff, (isIndepSet_induce)]

end NIndepSet

/-! ### Graphs without independent sets -/


section IndepSetFree

variable {n : Nat}

/--
Definition of `IndepSetFree` / `IndepSetFree` 的定义

English:
definition IndepSetFree
  signature: (n : Nat)
  body: forall t, ¬G.IsNIndepSet n t

中文:
定义 IndepSetFree
  签名: (n : 自然数)
  定义体: forall t, ¬G.IsNIndepSet n t

Depends on / 依赖: G.IsNIndepSet, IsNIndepSet
-/
def IndepSetFree (n : Nat) : Prop :=
  forall t, ¬G.IsNIndepSet n t

/--
theorem `cliqueFree_compl` / 定理 `cliqueFree_compl`

English:
theorem cliqueFree_compl
  statement: Gᶜ.CliqueFree n ↔ G.IndepSetFree n
  proof: by
  simp [IndepSetFree, CliqueFree]

中文:
定理 cliqueFree_compl
  结论: Gᶜ.CliqueFree n ↔ G.IndepSetFree n
  证明: by
  simp [IndepSetFree, CliqueFree]
-/
@[simp] theorem cliqueFree_compl : Gᶜ.CliqueFree n ↔ G.IndepSetFree n := by
  simp [IndepSetFree, CliqueFree]

/--
theorem `indepSetFree_compl` / 定理 `indepSetFree_compl`

English:
theorem indepSetFree_compl
  statement: Gᶜ.IndepSetFree n ↔ G.CliqueFree n
  proof: by
  simp [IndepSetFree, CliqueFree]

中文:
定理 indepSetFree_compl
  结论: Gᶜ.IndepSetFree n ↔ G.CliqueFree n
  证明: by
  simp [IndepSetFree, CliqueFree]
-/
@[simp] theorem indepSetFree_compl : Gᶜ.IndepSetFree n ↔ G.CliqueFree n := by
  simp [IndepSetFree, CliqueFree]

/--
Definition of `IndepSetFreeOn` / `IndepSetFreeOn` 的定义

English:
definition IndepSetFreeOn
  signature: (G : SimpleGraph α) (s : Set α) (n : Nat)
  body: forall ⦃t⦄, ↑t subseteq s -> ¬G.IsNIndepSet n t

中文:
定义 IndepSetFreeOn
  签名: (G : 简单图 α) (s : 集合 α) (n : 自然数)
  定义体: forall ⦃t⦄, ↑t subseteq s -> ¬G.IsNIndepSet n t

Depends on / 依赖: G.IsNIndepSet, IsNIndepSet, subseteq
-/
def IndepSetFreeOn (G : SimpleGraph α) (s : Set α) (n : Nat) : Prop :=
  forall ⦃t⦄, ↑t subseteq s -> ¬G.IsNIndepSet n t

end IndepSetFree

/-! ### Set of independent sets -/


section IndepSetSet

variable {n : Nat} {s : Finset α}

/--
Definition of `indepSetSet` / `indepSetSet` 的定义

English:
definition indepSetSet
  signature: (n : Nat)
  body: { s | G.IsNIndepSet n s }

中文:
定义 indepSetSet
  签名: (n : 自然数)
  定义体: { s | G.IsNIndepSet n s }

Depends on / 依赖: G.IsNIndepSet, IsNIndepSet
-/
def indepSetSet (n : Nat) : Set (Finset α) :=
  { s | G.IsNIndepSet n s }

variable {G}

@[simp]
/--
theorem `mem_indepSetSet_iff` / 定理 `mem_indepSetSet_iff`

English:
theorem mem_indepSetSet_iff
  statement: s in G.indepSetSet n ↔ G.IsNIndepSet n s
  proof: Iff.rfl

中文:
定理 mem_indepSetSet_iff
  结论: s in G.indepSetSet n ↔ G.是NIndepSet n s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_indepSetSet_iff : s in G.indepSetSet n ↔ G.IsNIndepSet n s :=
  Iff.rfl

end IndepSetSet

/-! ### Independence Number -/


section IndepNumber

variable {α : Type*} {G : SimpleGraph α}

/--
Definition of `indepNum` / `indepNum` 的定义

English:
definition indepNum
  signature: (G : SimpleGraph α)
  body: sSup {n | exists s, G.IsNIndepSet n s}

中文:
定义 indepNum
  签名: (G : 简单图 α)
  定义体: sSup {n | exists s, G.IsNIndepSet n s}

Depends on / 依赖: G.IsNIndepSet, IsNIndepSet
-/
noncomputable def indepNum (G : SimpleGraph α) : Nat := sSup {n | exists s, G.IsNIndepSet n s}

/--
lemma `cliqueNum_compl` / 引理 `cliqueNum_compl`

English:
lemma cliqueNum_compl
  statement: Gᶜ.cliqueNum = G.indepNum
  proof: by
  simp [indepNum, cliqueNum]

中文:
引理 cliqueNum_compl
  结论: Gᶜ.cliqueNum = G.indepNum
  证明: by
  simp [indepNum, cliqueNum]
-/
@[simp] lemma cliqueNum_compl : Gᶜ.cliqueNum = G.indepNum := by
  simp [indepNum, cliqueNum]

/--
lemma `indepNum_compl` / 引理 `indepNum_compl`

English:
lemma indepNum_compl
  statement: Gᶜ.indepNum = G.cliqueNum
  proof: by
  simp [indepNum, cliqueNum]

中文:
引理 indepNum_compl
  结论: Gᶜ.indepNum = G.cliqueNum
  证明: by
  simp [indepNum, cliqueNum]
-/
@[simp] lemma indepNum_compl : Gᶜ.indepNum = G.cliqueNum := by
  simp [indepNum, cliqueNum]

/--
theorem `IsIndepSet.card_le_indepNum` / 定理 `IsIndepSet.card_le_indepNum`

English:
theorem IsIndepSet.card_le_indepNum
  proof: by
  rw [← isClique_compl] at tc
  simp_rw [indepNum, ← isNClique_compl]
  exact tc.card_le_cliqueNum

中文:
定理 IsIndepSet.card_le_indepNum
  证明: by
  rw [← isClique_compl] at tc
  simp_rw [indepNum, ← isNClique_compl]
  exact tc.card_le_cliqueNum

Depends on / 依赖: card_le_cliqueNum, indepNum, isClique_compl, isNClique_compl, simp_rw, tc.card_le_cliqueNum
-/
theorem IsIndepSet.card_le_indepNum
    [Finite α] {t : Finset α} (tc : G.IsIndepSet t) : #t <= G.indepNum := by
  rw [← isClique_compl] at tc
  simp_rw [indepNum, ← isNClique_compl]
  exact tc.card_le_cliqueNum

/--
lemma `exists_isNIndepSet_indepNum` / 引理 `exists_isNIndepSet_indepNum`

English:
lemma exists_isNIndepSet_indepNum
  statement: exists s, G.IsNIndepSet G.indepNum s
  proof: by
  simp_rw [indepNum, ← isNClique_compl]
  exact exists_isNClique_cliqueNum

中文:
引理 存在_isNIndepSet_indepNum
  结论: 存在 s, G.是NIndepSet G.indepNum s
  证明: by
  simp_rw [indepNum, ← isNClique_compl]
  exact exists_isNClique_cliqueNum

Depends on / 依赖: exists_isNClique_cliqueNum, indepNum, isNClique_compl, simp_rw
-/
lemma exists_isNIndepSet_indepNum : exists s, G.IsNIndepSet G.indepNum s := by
  simp_rw [indepNum, ← isNClique_compl]
  exact exists_isNClique_cliqueNum

/-- An independent set in a graph `G` such that there is no independent set with more vertices. -/
-- TODO: replace with `MaximalFor (G.IsIndepSet ∘ (↑)) card s`
@[mk_iff]
/--
Definition of `IsMaximumIndepSet` / `IsMaximumIndepSet` 的定义

English:
structure IsMaximumIndepSet
  parameters: [Finite α] (G : SimpleGraph α) (s : Finset α)
  axioms and operations (2):
    - isIndepSet : G.IsIndepSet s
    - maximum : forall t : Finset α, G.IsIndepSet t -> #t <= #s

中文:
结构 是MaximumIndepSet
  参数: [有限 α] (G : 简单图 α) (s : 有限集 α)
  公理与运算 (2 个):
    - isIndepSet : G.IsIndepSet s
    - maximum : 对任意 t : 有限集 α, G.IsIndepSet t -> #t <= #s
-/
structure IsMaximumIndepSet [Finite α] (G : SimpleGraph α) (s : Finset α) : Prop where
  isIndepSet : G.IsIndepSet s
  maximum : forall t : Finset α, G.IsIndepSet t -> #t <= #s

/--
lemma `isMaximumClique_compl` / 引理 `isMaximumClique_compl`

English:
lemma isMaximumClique_compl
  given: [Finite α] (s : Finset α)
  proof: by
  simp [isMaximumIndepSet_iff, isMaximumClique_iff]

中文:
引理 isMaximumClique_compl
  条件: [有限 α] (s : 有限集 α)
  证明: by
  simp [isMaximumIndepSet_iff, isMaximumClique_iff]
-/
@[simp] lemma isMaximumClique_compl [Finite α] (s : Finset α) :
    Gᶜ.IsMaximumClique s ↔ G.IsMaximumIndepSet s := by
  simp [isMaximumIndepSet_iff, isMaximumClique_iff]

/--
lemma `isMaximumIndepSet_compl` / 引理 `isMaximumIndepSet_compl`

English:
lemma isMaximumIndepSet_compl
  given: [Finite α] (s : Finset α)
  proof: by
  simp [isMaximumIndepSet_iff, isMaximumClique_iff]

中文:
引理 isMaximumIndepSet_compl
  条件: [有限 α] (s : 有限集 α)
  证明: by
  simp [isMaximumIndepSet_iff, isMaximumClique_iff]
-/
@[simp] lemma isMaximumIndepSet_compl [Finite α] (s : Finset α) :
    Gᶜ.IsMaximumIndepSet s ↔ G.IsMaximumClique s := by
  simp [isMaximumIndepSet_iff, isMaximumClique_iff]

/--
theorem `isMaximalIndepSet_iff` / 定理 `isMaximalIndepSet_iff`

English:
theorem isMaximalIndepSet_iff
  given: {s : Set α}
  proof: Iff.rfl

中文:
定理 isMaximalIndepSet_iff
  条件: {s : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isMaximalIndepSet_iff {s : Set α} :
    Maximal G.IsIndepSet s ↔ G.IsIndepSet s ∧ forall t : Set α, G.IsIndepSet t -> s subseteq t -> t subseteq s :=
  Iff.rfl

/--
lemma `isMaximalClique_compl` / 引理 `isMaximalClique_compl`

English:
lemma isMaximalClique_compl
  given: (s : Finset α)
  proof: by
  simp [isMaximalIndepSet_iff, isMaximalClique_iff]

中文:
引理 isMaximalClique_compl
  条件: (s : 有限集 α)
  证明: by
  simp [isMaximalIndepSet_iff, isMaximalClique_iff]
-/
@[simp] lemma isMaximalClique_compl (s : Finset α) :
    Maximal Gᶜ.IsClique s ↔ Maximal G.IsIndepSet s := by
  simp [isMaximalIndepSet_iff, isMaximalClique_iff]

/--
lemma `isMaximalIndepSet_compl` / 引理 `isMaximalIndepSet_compl`

English:
lemma isMaximalIndepSet_compl
  given: (s : Finset α)
  proof: by
  simp [isMaximalIndepSet_iff, isMaximalClique_iff]

中文:
引理 isMaximalIndepSet_compl
  条件: (s : 有限集 α)
  证明: by
  simp [isMaximalIndepSet_iff, isMaximalClique_iff]
-/
@[simp] lemma isMaximalIndepSet_compl (s : Finset α) :
    Maximal Gᶜ.IsIndepSet s ↔ Maximal G.IsClique s := by
  simp [isMaximalIndepSet_iff, isMaximalClique_iff]

/--
lemma `IsMaximumIndepSet.isMaximalIndepSet` / 引理 `IsMaximumIndepSet.isMaximalIndepSet`

English:
lemma IsMaximumIndepSet.isMaximalIndepSet
  proof: by
  rw [← isMaximalClique_compl]
  rw [← isMaximumClique_compl] at M
  exact IsMaximumClique.isMaximalClique s M

中文:
引理 是MaximumIndepSet.isMaximalIndepSet
  证明: by
  rw [← isMaximalClique_compl]
  rw [← isMaximumClique_compl] at M
  exact IsMaximumClique.isMaximalClique s M

Depends on / 依赖: IsMaximumClique, IsMaximumClique.isMaximalClique, isMaximalClique, isMaximalClique_compl, isMaximumClique_compl
-/
lemma IsMaximumIndepSet.isMaximalIndepSet
    [Finite α] (s : Finset α) (M : G.IsMaximumIndepSet s) : Maximal G.IsIndepSet s := by
  rw [← isMaximalClique_compl]
  rw [← isMaximumClique_compl] at M
  exact IsMaximumClique.isMaximalClique s M

/--
theorem `maximumIndepSet_card_eq_indepNum` / 定理 `maximumIndepSet_card_eq_indepNum`

English:
theorem maximumIndepSet_card_eq_indepNum
  proof: by
  rw [← isMaximumClique_compl] at tmc
  simp_rw [indepNum, ← isNClique_compl]
  exact Gᶜ.maximumClique_card_eq_cliqueNum t tmc

中文:
定理 maximumIndepSet_card_eq_indepNum
  证明: by
  rw [← isMaximumClique_compl] at tmc
  simp_rw [indepNum, ← isNClique_compl]
  exact Gᶜ.maximumClique_card_eq_cliqueNum t tmc

Depends on / 依赖: indepNum, isMaximumClique_compl, isNClique_compl, maximumClique_card_eq_cliqueNum, simp_rw
-/
theorem maximumIndepSet_card_eq_indepNum
    [Finite α] (t : Finset α) (tmc : G.IsMaximumIndepSet t) : #t = G.indepNum := by
  rw [← isMaximumClique_compl] at tmc
  simp_rw [indepNum, ← isNClique_compl]
  exact Gᶜ.maximumClique_card_eq_cliqueNum t tmc

/--
lemma `maximumIndepSet_exists` / 引理 `maximumIndepSet_exists`

English:
lemma maximumIndepSet_exists
  given: [Finite α]
  statement: exists (s : Finset α), G.IsMaximumIndepSet s
  proof: by
  simp [← isMaximumClique_compl, maximumClique_exists]

中文:
引理 maximumIndepSet_存在
  条件: [有限 α]
  结论: 存在 (s : 有限集 α), G.是MaximumIndepSet s
  证明: by
  simp [← isMaximumClique_compl, maximumClique_exists]

Depends on / 依赖: isMaximumClique_compl, maximumClique_exists
-/
lemma maximumIndepSet_exists [Finite α] : exists (s : Finset α), G.IsMaximumIndepSet s := by
  simp [← isMaximumClique_compl, maximumClique_exists]

end IndepNumber

/-! ### Finset of independent sets -/


section IndepSetFinset

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : Nat} {s : Finset α}

/--
Definition of `indepSetFinset` / `indepSetFinset` 的定义

English:
definition indepSetFinset
  signature: (n : Nat)
  body: {s | G.IsNIndepSet n s}

中文:
定义 indepSetFinset
  签名: (n : 自然数)
  定义体: {s | G.IsNIndepSet n s}

Depends on / 依赖: G.IsNIndepSet, IsNIndepSet
-/
def indepSetFinset (n : Nat) : Finset (Finset α) := {s | G.IsNIndepSet n s}

variable {G} in
@[simp]
/--
theorem `mem_indepSetFinset_iff` / 定理 `mem_indepSetFinset_iff`

English:
theorem mem_indepSetFinset_iff
  statement: s in G.indepSetFinset n ↔ G.IsNIndepSet n s
  proof: mem_filter.trans and_iff_right mem_univ _

中文:
定理 mem_indepSetFinset_iff
  结论: s in G.indepSetFinset n ↔ G.是NIndepSet n s
  证明: mem_filter.trans and_iff_right mem_univ _

Depends on / 依赖: and_iff_right, mem_filter, mem_filter.trans, mem_univ
-/
theorem mem_indepSetFinset_iff : s in G.indepSetFinset n ↔ G.IsNIndepSet n s :=
mem_filter.trans and_iff_right mem_univ _

end IndepSetFinset

end SimpleGraph
