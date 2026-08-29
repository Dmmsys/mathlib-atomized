/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity

/-!
# Triangles in graphs

A *triangle* in a simple graph is a `3`-clique, namely a set of three vertices that are
pairwise adjacent.

This module defines and proves properties about triangles in simple graphs.

## Main declarations

* `SimpleGraph.FarFromTriangleFree`: Predicate for a graph such that one must remove a lot of edges
  from it for it to become triangle-free. This is the crux of the Triangle Removal Lemma.

## TODO

* Generalise `FarFromTriangleFree` to other graphs, to state and prove the Graph Removal Lemma.
-/

@[expose] public section

open Finset Nat
open Fintype (card)

namespace SimpleGraph

variable {α β 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {G H : SimpleGraph α} {ε δ : 𝕜}

section LocallyLinear

/--
Definition of `EdgeDisjointTriangles` / `EdgeDisjointTriangles` 的定义

English:
definition EdgeDisjointTriangles
  signature: (G : SimpleGraph α)
  body: (G.cliqueSet 3).Pairwise fun x y => (x inter y : Set α).Subsingleton

中文:
定义 EdgeDisjointTriangles
  签名: (G : 简单图 α)
  定义体: (G.cliqueSet 3).Pairwise fun x y => (x inter y : Set α).Subsingleton

Depends on / 依赖: G.cliqueSet, Pairwise, Subsingleton, cliqueSet
-/
def EdgeDisjointTriangles (G : SimpleGraph α) : Prop :=
  (G.cliqueSet 3).Pairwise fun x y => (x inter y : Set α).Subsingleton

/--
Definition of `LocallyLinear` / `LocallyLinear` 的定义

English:
definition LocallyLinear
  signature: (G : SimpleGraph α)
  body: G.EdgeDisjointTriangles ∧ forall ⦃x y⦄, G.Adj x y -> exists s, G.IsNClique 3 s ∧ x in s ∧ y in s

中文:
定义 LocallyLinear
  签名: (G : 简单图 α)
  定义体: G.EdgeDisjointTriangles ∧ forall ⦃x y⦄, G.Adj x y -> exists s, G.IsNClique 3 s ∧ x in s ∧ y in s

Depends on / 依赖: EdgeDisjointTriangles, G.Adj, G.EdgeDisjointTriangles, G.IsNClique, IsNClique
-/
def LocallyLinear (G : SimpleGraph α) : Prop :=
  G.EdgeDisjointTriangles ∧ forall ⦃x y⦄, G.Adj x y -> exists s, G.IsNClique 3 s ∧ x in s ∧ y in s

/--
lemma `LocallyLinear.edgeDisjointTriangles` / 引理 `LocallyLinear.edgeDisjointTriangles`

English:
lemma LocallyLinear.edgeDisjointTriangles
  statement: G.LocallyLinear -> G.EdgeDisjointTriangles
  proof: And.left

nonrec lemma EdgeDisjointTriangles.mono (h : G <= H) (hH : H.EdgeDisjointTriangles) :
G.EdgeDisjointTriangles := hH.mono cliqueSet_mono h

中文:
引理 LocallyLinear.edgeDisjointTriangles
  结论: G.LocallyLinear -> G.EdgeDisjointTriangles
  证明: And.left

nonrec lemma EdgeDisjointTriangles.mono (h : G <= H) (hH : H.EdgeDisjointTriangles) :
G.EdgeDisjointTriangles := hH.mono cliqueSet_mono h
-/
protected lemma LocallyLinear.edgeDisjointTriangles : G.LocallyLinear -> G.EdgeDisjointTriangles :=
  And.left

nonrec lemma EdgeDisjointTriangles.mono (h : G <= H) (hH : H.EdgeDisjointTriangles) :
G.EdgeDisjointTriangles := hH.mono cliqueSet_mono h

/--
lemma `edgeDisjointTriangles_bot` / 引理 `edgeDisjointTriangles_bot`

English:
lemma edgeDisjointTriangles_bot
  statement: (⊥ : SimpleGraph α).EdgeDisjointTriangles
  proof: by
  simp [EdgeDisjointTriangles]

中文:
引理 edgeDisjointTriangles_bot
  结论: (⊥ : 简单图 α).EdgeDisjointTriangles
  证明: by
  simp [EdgeDisjointTriangles]
-/
@[simp] lemma edgeDisjointTriangles_bot : (⊥ : SimpleGraph α).EdgeDisjointTriangles := by
  simp [EdgeDisjointTriangles]

/--
lemma `locallyLinear_bot` / 引理 `locallyLinear_bot`

English:
lemma locallyLinear_bot
  statement: (⊥ : SimpleGraph α).LocallyLinear
  proof: by simp [LocallyLinear]

中文:
引理 locallyLinear_bot
  结论: (⊥ : 简单图 α).LocallyLinear
  证明: by simp [LocallyLinear]
-/
@[simp] lemma locallyLinear_bot : (⊥ : SimpleGraph α).LocallyLinear := by simp [LocallyLinear]

/--
lemma `EdgeDisjointTriangles.map` / 引理 `EdgeDisjointTriangles.map`

English:
lemma EdgeDisjointTriangles.map
  given: (f : α ↪ β) (hG : G.EdgeDisjointTriangles)
  proof: by
  rw [EdgeDisjointTriangles]; rw [cliqueSet_map (by simp : 3 != 1)]; rw [(Finset.map_injective f).injOn.pairwise_image]
  classical
  rintro s hs t ht hst
  dsimp [Function.onFun]
  rw [← coe_inter]; rw [← map_inter]; rw [coe_map]; rw [coe_inter]
  exact (hG hs ht hst).image _

中文:
引理 EdgeDisjointTriangles.map
  条件: (f : α ↪ β) (hG : G.EdgeDisjointTriangles)
  证明: by
  rw [EdgeDisjointTriangles]; rw [cliqueSet_map (by simp : 3 != 1)]; rw [(Finset.map_injective f).injOn.pairwise_image]
  classical
  rintro s hs t ht hst
  dsimp [Function.onFun]
  rw [← coe_inter]; rw [← map_inter]; rw [coe_map]; rw [coe_inter]
  exact (hG hs ht hst).image _

Depends on / 依赖: EdgeDisjointTriangles, Finset, Finset.map_injective, Function, Function.onFun, classical, cliqueSet_map, coe_inter, coe_map, injOn.pairwise_image, map_injective, map_inter, pairwise_image
-/
lemma EdgeDisjointTriangles.map (f : α ↪ β) (hG : G.EdgeDisjointTriangles) :
    (G.map f).EdgeDisjointTriangles := by
  rw [EdgeDisjointTriangles]; rw [cliqueSet_map (by simp : 3 != 1)]; rw [(Finset.map_injective f).injOn.pairwise_image]
  classical
  rintro s hs t ht hst
  dsimp [Function.onFun]
  rw [← coe_inter]; rw [← map_inter]; rw [coe_map]; rw [coe_inter]
  exact (hG hs ht hst).image _

/--
lemma `LocallyLinear.map` / 引理 `LocallyLinear.map`

English:
lemma LocallyLinear.map
  given: (f : α ↪ β) (hG : G.LocallyLinear)
  statement: (G.map f).LocallyLinear
  proof: by
  refine ⟨hG.1.map _, ?_⟩
  rintro _ _ ⟨-, a, b, h, rfl, rfl⟩
  obtain ⟨s, hs, ha, hb⟩ := hG.2 h
  exact ⟨s.map f, hs.map, mem_map_of_mem _ ha, mem_map_of_mem _ hb⟩

中文:
引理 LocallyLinear.map
  条件: (f : α ↪ β) (hG : G.LocallyLinear)
  结论: (G.map f).LocallyLinear
  证明: by
  refine ⟨hG.1.map _, ?_⟩
  rintro _ _ ⟨-, a, b, h, rfl, rfl⟩
  obtain ⟨s, hs, ha, hb⟩ := hG.2 h
  exact ⟨s.map f, hs.map, mem_map_of_mem _ ha, mem_map_of_mem _ hb⟩

Depends on / 依赖: hs.map, mem_map_of_mem, s.map
-/
lemma LocallyLinear.map (f : α ↪ β) (hG : G.LocallyLinear) : (G.map f).LocallyLinear := by
  refine ⟨hG.1.map _, ?_⟩
  rintro _ _ ⟨-, a, b, h, rfl, rfl⟩
  obtain ⟨s, hs, ha, hb⟩ := hG.2 h
  exact ⟨s.map f, hs.map, mem_map_of_mem _ ha, mem_map_of_mem _ hb⟩

/--
lemma `locallyLinear_comap` / 引理 `locallyLinear_comap`

English:
lemma locallyLinear_comap
  given: {G : SimpleGraph β} {e : α ≃ β}
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← comap_map_eq e.symm.toEmbedding G, comap_symm, map_symm]
    exact h.map _
  · rw [← Equiv.coe_toEmbedding, ← map_symm]
    exact LocallyLinear.map _

中文:
引理 locallyLinear_comap
  条件: {G : 简单图 β} {e : α ≃ β}
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← comap_map_eq e.symm.toEmbedding G, comap_symm, map_symm]
    exact h.map _
  · rw [← Equiv.coe_toEmbedding, ← map_symm]
    exact LocallyLinear.map _
-/
@[simp] lemma locallyLinear_comap {G : SimpleGraph β} {e : α ≃ β} :
    (G.comap e).LocallyLinear ↔ G.LocallyLinear := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← comap_map_eq e.symm.toEmbedding G, comap_symm, map_symm]
    exact h.map _
  · rw [← Equiv.coe_toEmbedding, ← map_symm]
    exact LocallyLinear.map _

/--
lemma `edgeDisjointTriangles_iff_mem_sym2_subsingleton` / 引理 `edgeDisjointTriangles_iff_mem_sym2_subsingleton`

English:
lemma edgeDisjointTriangles_iff_mem_sym2_subsingleton
  proof: by
  classical
  have (a b) (hab : a != b) : {s in (G.cliqueSet 3 : Set (Finset α)) | s(a, b) in (s : Finset α).sym2}
    = {s | G.Adj a b ∧ exists c, G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c}} := by
    ext s
    simp only [mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp, forall_eq,
      mem_cliqueSet_if

中文:
引理 edgeDisjointTriangles_iff_mem_sym2_subsingleton
  证明: by
  classical
  have (a b) (hab : a != b) : {s in (G.cliqueSet 3 : Set (Finset α)) | s(a, b) in (s : Finset α).sym2}
    = {s | G.Adj a b ∧ exists c, G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c}} := by
    ext s
    simp only [mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp, forall_eq,
      mem_cliqueSet_if

Depends on / 依赖: Finset, G.Adj, G.cliqueSet, Set.mem_ofPred_eq, Sym2.mem_iff, adj_comm, any_goals, classical, cliqueSet, forall_eq, forall_eq_or_imp, is3Clique_iff, mem_cliqueSet_iff, mem_iff, mem_insert, mem_ofPred_eq, mem_singleton, mem_sym2_iff
-/
lemma edgeDisjointTriangles_iff_mem_sym2_subsingleton :
    G.EdgeDisjointTriangles ↔
      forall ⦃e : Sym2 α⦄, ¬ e.IsDiag -> {s in G.cliqueSet 3 | e in (s : Finset α).sym2}.Subsingleton := by
  classical
  have (a b) (hab : a != b) : {s in (G.cliqueSet 3 : Set (Finset α)) | s(a, b) in (s : Finset α).sym2}
    = {s | G.Adj a b ∧ exists c, G.Adj a c ∧ G.Adj b c ∧ s = {a, b, c}} := by
    ext s
    simp only [mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp, forall_eq,
      mem_cliqueSet_iff, Set.mem_ofPred_eq,
      is3Clique_iff]
    constructor
    · rintro ⟨⟨c, d, e, hcd, hce, hde, rfl⟩, hab⟩
      simp only [mem_insert, mem_singleton] at hab
      obtain ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ := hab
      any_goals
        simp only [*, adj_comm, true_and, Ne, not_true] at *
      any_goals
        first
        | exact ⟨c, by aesop⟩
        | exact ⟨d, by aesop⟩
        | exact ⟨e, by aesop⟩
        | simp only [*, true_and] at *
          exact ⟨c, by aesop⟩
        | simp only [*, true_and] at *
          exact ⟨d, by aesop⟩
        | simp only [*, true_and] at *
          exact ⟨e, by aesop⟩
    · rintro ⟨hab, c, hac, hbc, rfl⟩
      refine ⟨⟨a, b, c, ?_⟩, ?_⟩ <;> simp [*]
  constructor
  · rw [Sym2.forall]
    rintro hG a b hab
    simp only [Sym2.mk_isDiag_iff] at hab
    rw [this _ _ (Sym2.mk_isDiag_iff.not.2 hab)]
    rintro _ ⟨hab, c, hac, hbc, rfl⟩ _ ⟨-, d, had, hbd, rfl⟩
    refine hG.eq ?_ ?_ (Set.Nontrivial.not_subsingleton ⟨a, ?_, b, ?_, hab.ne⟩) <;>
      simp [is3Clique_triple_iff, *]
  · simp only [EdgeDisjointTriangles, is3Clique_iff, Set.Pairwise, mem_cliqueSet_iff, Ne,
      forall_exists_index, and_imp, ← Set.not_nontrivial_iff (s := _ inter _), not_imp_not,
      Set.Nontrivial, Set.mem_inter_iff, mem_coe]
    rintro hG _ a b c hab hac hbc rfl _ d e f hde hdf hef rfl g hg₁ hg₂ h hh₁ hh₂ hgh
    refine hG (Sym2.mk_isDiag_iff.not.2 hgh) ⟨⟨a, b, c, ?_⟩, by simpa using And.intro hg₁ hh₁⟩
      ⟨⟨d, e, f, ?_⟩, by simpa using And.intro hg₂ hh₂⟩ <;> simp [*]

alias ⟨EdgeDisjointTriangles.mem_sym2_subsingleton, _⟩ :=
  edgeDisjointTriangles_iff_mem_sym2_subsingleton

variable [DecidableEq α] [Fintype α] [DecidableRel G.Adj]

/--
Instance `EdgeDisjointTriangles.instDecidable` / 实例 `EdgeDisjointTriangles.instDecidable`

English:
instance EdgeDisjointTriangles.instDecidable
  signature: : Decidable G.EdgeDisjointTriangles
  body: decidable_of_iff ((G.cliqueFinset 3 : Set (Finset α)).Pairwise fun x y => (#(x inter y) <= 1)) by
    simp only [coe_cliqueFinset, EdgeDisjointTriangles, Finset.card_le_one, ← coe_inter]; rfl

中文:
实例 EdgeDisjointTriangles.instDecidable
  签名: : 可判定 G.EdgeDisjointTriangles
  定义体: decidable_of_iff ((G.cliqueFinset 3 : Set (Finset α)).Pairwise fun x y => (#(x inter y) <= 1)) by
    simp only [coe_cliqueFinset, EdgeDisjointTriangles, Finset.card_le_one, ← coe_inter]; rfl

Depends on / 依赖: EdgeDisjointTriangles, Finset, Finset.card_le_one, G.cliqueFinset, Pairwise, card_le_one, cliqueFinset, coe_cliqueFinset, coe_inter, decidable_of_iff
-/
instance EdgeDisjointTriangles.instDecidable : Decidable G.EdgeDisjointTriangles :=
decidable_of_iff ((G.cliqueFinset 3 : Set (Finset α)).Pairwise fun x y => (#(x inter y) <= 1)) by
    simp only [coe_cliqueFinset, EdgeDisjointTriangles, Finset.card_le_one, ← coe_inter]; rfl

/--
Instance `LocallyLinear.instDecidable` / 实例 `LocallyLinear.instDecidable`

English:
instance LocallyLinear.instDecidable
  signature: : Decidable G.LocallyLinear
  body: inferInstanceAs (Decidable (_ ∧ _))

中文:
实例 LocallyLinear.instDecidable
  签名: : 可判定 G.LocallyLinear
  定义体: inferInstanceAs (Decidable (_ ∧ _))

Depends on / 依赖: Decidable
-/
instance LocallyLinear.instDecidable : Decidable G.LocallyLinear :=
  inferInstanceAs (Decidable (_ ∧ _))

/--
lemma `EdgeDisjointTriangles.card_edgeFinset_le` / 引理 `EdgeDisjointTriangles.card_edgeFinset_le`

English:
lemma EdgeDisjointTriangles.card_edgeFinset_le
  given: (hG : G.EdgeDisjointTriangles)
  proof: by
  rw [mul_comm]; rw [← mul_one #G.edgeFinset]
  refine card_mul_le_card_mul (fun s e => e in s.sym2) ?_ (fun e he => ?_)
  · simp only [is3Clique_iff, mem_cliqueFinset_iff, mem_sym2_iff, forall_exists_index, and_imp]
    rintro _ a b c hab hac hbc rfl
    have : #{s(a, b), s(a, c), s(b, c)} = 3 :

中文:
引理 EdgeDisjointTriangles.card_edgeFinset_le
  条件: (hG : G.EdgeDisjointTriangles)
  证明: by
  rw [mul_comm]; rw [← mul_one #G.edgeFinset]
  refine card_mul_le_card_mul (fun s e => e in s.sym2) ?_ (fun e he => ?_)
  · simp only [is3Clique_iff, mem_cliqueFinset_iff, mem_sym2_iff, forall_exists_index, and_imp]
    rintro _ a b c hab hac hbc rfl
    have : #{s(a, b), s(a, c), s(b, c)} = 3 :

Depends on / 依赖: G.edgeFinset, Set.Subsingle, Subsingle, and_imp, card_eq_three, card_le_one, card_mono, card_mul_le_card_mul, edgeFinset, forall_exists_index, hab.ne, hac.ne, hbc.ne, insert_subset, is3Clique_iff, mem_bipartiteBelow, mem_cliqueFinset_iff, mem_sym2_iff, mul_comm, mul_one
-/
lemma EdgeDisjointTriangles.card_edgeFinset_le (hG : G.EdgeDisjointTriangles) :
    3 * #(G.cliqueFinset 3) <= #G.edgeFinset := by
  rw [mul_comm]; rw [← mul_one #G.edgeFinset]
  refine card_mul_le_card_mul (fun s e => e in s.sym2) ?_ (fun e he => ?_)
  · simp only [is3Clique_iff, mem_cliqueFinset_iff, mem_sym2_iff, forall_exists_index, and_imp]
    rintro _ a b c hab hac hbc rfl
    have : #{s(a, b), s(a, c), s(b, c)} = 3 := by
      refine card_eq_three.2 ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> simp [hab.ne, hac.ne, hbc.ne]
    rw [← this]
    refine card_mono ?_
    simp [insert_subset, *]
  · simpa only [card_le_one, mem_bipartiteBelow, and_imp, Set.Subsingleton, Set.mem_ofPred_eq,
      mem_cliqueFinset_iff, mem_cliqueSet_iff]
      using hG.mem_sym2_subsingleton (G.not_isDiag_of_mem_edgeSet <| mem_edgeFinset.1 he)

/--
lemma `LocallyLinear.card_edgeFinset` / 引理 `LocallyLinear.card_edgeFinset`

English:
lemma LocallyLinear.card_edgeFinset
  given: (hG : G.LocallyLinear)
  proof: by
  refine hG.edgeDisjointTriangles.card_edgeFinset_le.antisymm' ?_
  rw [← mul_comm]; rw [← mul_one #_]
  refine card_mul_le_card_mul (fun e s => e in s.sym2) ?_ ?_
  · simpa [Sym2.forall, Nat.one_le_iff_ne_zero, -Finset.card_eq_zero, Finset.card_ne_zero,
        Finset.Nonempty]
      using hG.2


中文:
引理 LocallyLinear.card_edgeFinset
  条件: (hG : G.LocallyLinear)
  证明: by
  refine hG.edgeDisjointTriangles.card_edgeFinset_le.antisymm' ?_
  rw [← mul_comm]; rw [← mul_one #_]
  refine card_mul_le_card_mul (fun e s => e in s.sym2) ?_ ?_
  · simpa [Sym2.forall, Nat.one_le_iff_ne_zero, -Finset.card_eq_zero, Finset.card_ne_zero,
        Finset.Nonempty]
      using hG.2


Depends on / 依赖: Finset, Finset.Nonempty, Finset.card_eq_zero, Finset.card_ne_zero, Nat.one_le_iff_ne_zero, Nonempty, Sym2.forall, and_imp, antisymm, card_edgeFinset_le, card_eq_zero, card_insert_le, card_le_card, card_mul_le_card_mul, card_ne_zero, edgeDisjointTriangles, forall_exists_index, hG.edgeDisjointTriangles.card_edgeFinset_le.antisymm, is3Clique_iff, mem_cliqueFinset_iff
-/
lemma LocallyLinear.card_edgeFinset (hG : G.LocallyLinear) :
    #G.edgeFinset = 3 * #(G.cliqueFinset 3) := by
  refine hG.edgeDisjointTriangles.card_edgeFinset_le.antisymm' ?_
  rw [← mul_comm]; rw [← mul_one #_]
  refine card_mul_le_card_mul (fun e s => e in s.sym2) ?_ ?_
  · simpa [Sym2.forall, Nat.one_le_iff_ne_zero, -Finset.card_eq_zero, Finset.card_ne_zero,
        Finset.Nonempty]
      using hG.2
  simp only [mem_cliqueFinset_iff, is3Clique_iff, forall_exists_index, and_imp]
  rintro _ a b c hab hac hbc rfl
  calc
    _ <= #{s(a, b), s(a, c), s(b, c)} := card_le_card ?_
    _ <= 3 := (card_insert_le _ _).trans (succ_le_succ <| (card_insert_le _ _).trans_eq <| by
      rw [card_singleton])
  simp only [subset_iff, Sym2.forall, mem_sym2_iff, mem_bipartiteBelow, mem_insert,
    mem_edgeFinset, mem_singleton, and_imp, mem_edgeSet, Sym2.mem_iff, forall_eq_or_imp,
    forall_eq]
  rintro d e hde (rfl | rfl | rfl) (rfl | rfl | rfl) <;> simp [*] at *

end LocallyLinear

variable (G ε)
variable [Fintype α] [DecidableRel G.Adj] [DecidableRel H.Adj]

/--
Definition of `FarFromTriangleFree` / `FarFromTriangleFree` 的定义

English:
definition FarFromTriangleFree
  signature: : Prop
  body: G.DeleteFar (fun H => H.CliqueFree 3) ε * (card α ^ 2 : Nat)

中文:
定义 FarFromTriangleFree
  签名: : 命题
  定义体: G.DeleteFar (fun H => H.CliqueFree 3) ε * (card α ^ 2 : Nat)

Depends on / 依赖: CliqueFree, DeleteFar, G.DeleteFar, H.CliqueFree
-/
def FarFromTriangleFree : Prop := G.DeleteFar (fun H => H.CliqueFree 3) ε * (card α ^ 2 : Nat)

variable {G ε}

omit [IsStrictOrderedRing 𝕜] in
/--
theorem `farFromTriangleFree_iff` / 定理 `farFromTriangleFree_iff`

English:
theorem farFromTriangleFree_iff
  proof: deleteFar_iff

alias ⟨farFromTriangleFree.le_card_sub_card, _⟩ := farFromTriangleFree_iff

nonrec theorem FarFromTriangleFree.mono (hε : G.FarFromTriangleFree ε) (h : δ <= ε) :
G.FarFromTriangleFree δ := hε.mono by gcongr

中文:
定理 farFromTriangleFree_iff
  证明: deleteFar_iff

alias ⟨farFromTriangleFree.le_card_sub_card, _⟩ := farFromTriangleFree_iff

nonrec theorem FarFromTriangleFree.mono (hε : G.FarFromTriangleFree ε) (h : δ <= ε) :
G.FarFromTriangleFree δ := hε.mono by gcongr

Depends on / 依赖: deleteFar_iff
-/
theorem farFromTriangleFree_iff :
    G.FarFromTriangleFree ε ↔ forall ⦃H : SimpleGraph α⦄, [DecidableRel H.Adj] -> H <= G -> H.CliqueFree 3 ->
      ε * (card α ^ 2 : Nat) <= #G.edgeFinset - #H.edgeFinset := deleteFar_iff

alias ⟨farFromTriangleFree.le_card_sub_card, _⟩ := farFromTriangleFree_iff

nonrec theorem FarFromTriangleFree.mono (hε : G.FarFromTriangleFree ε) (h : δ <= ε) :
G.FarFromTriangleFree δ := hε.mono by gcongr

section DecidableEq

variable [DecidableEq α]

omit [IsStrictOrderedRing 𝕜] in
/--
theorem `FarFromTriangleFree.cliqueFinset_nonempty'` / 定理 `FarFromTriangleFree.cliqueFinset_nonempty'`

English:
theorem FarFromTriangleFree.cliqueFinset_nonempty'
  statement: (hH : H <= G) (hG : G.FarFromTriangleFree ε)
  proof: nonempty_of_ne_empty
    cliqueFinset_eq_empty_iff.not.2 fun hH' => (hG.le_card_sub_card hH hH').not_gt hcard

中文:
定理 FarFromTriangleFree.cliqueFinset_nonempty'
  结论: (hH : H <= G) (hG : G.FarFromTriangleFree ε)
  证明: nonempty_of_ne_empty
    cliqueFinset_eq_empty_iff.not.2 fun hH' => (hG.le_card_sub_card hH hH').not_gt hcard

Depends on / 依赖: cliqueFinset_eq_empty_iff, cliqueFinset_eq_empty_iff.not, hG.le_card_sub_card, le_card_sub_card, nonempty_of_ne_empty, not_gt
-/
theorem FarFromTriangleFree.cliqueFinset_nonempty' (hH : H <= G) (hG : G.FarFromTriangleFree ε)
    (hcard : #G.edgeFinset - #H.edgeFinset < ε * (card α ^ 2 : Nat)) :
    (H.cliqueFinset 3).Nonempty :=
nonempty_of_ne_empty
    cliqueFinset_eq_empty_iff.not.2 fun hH' => (hG.le_card_sub_card hH hH').not_gt hcard

/--
lemma `farFromTriangleFree_of_disjoint_triangles_aux` / 引理 `farFromTriangleFree_of_disjoint_triangles_aux`

English:
lemma farFromTriangleFree_of_disjoint_triangles_aux
  statement: {tris : Finset (Finset α)}
  proof: by
  rw [← card_sdiff_of_subset (edgeFinset_mono hHG)]; rw [← card_attach]
  by_contra! hG
  have ⦃t⦄ (ht : t in tris) :
    exists x y, x in t ∧ y in t ∧ x != y ∧ s(x, y) in G.edgeFinset \ H.edgeFinset := by
    by_contra! h
    refine hH t ?_
    simp only [not_and, mem_sdiff, not_not, mem_edgeFin

中文:
引理 farFromTriangleFree_of_disjoint_triangles_aux
  结论: {tris : 有限集 (有限集 α)}
  证明: by
  rw [← card_sdiff_of_subset (edgeFinset_mono hHG)]; rw [← card_attach]
  by_contra! hG
  have ⦃t⦄ (ht : t in tris) :
    exists x y, x in t ∧ y in t ∧ x != y ∧ s(x, y) in G.edgeFinset \ H.edgeFinset := by
    by_contra! h
    refine hH t ?_
    simp only [not_and, mem_sdiff, not_not, mem_edgeFin
-/
private lemma farFromTriangleFree_of_disjoint_triangles_aux {tris : Finset (Finset α)}
    (htris : tris subseteq G.cliqueFinset 3)
    (pd : (tris : Set (Finset α)).Pairwise fun x y => (x inter y : Set α).Subsingleton) (hHG : H <= G)
    (hH : H.CliqueFree 3) : #tris <= #G.edgeFinset - #H.edgeFinset := by
  rw [← card_sdiff_of_subset (edgeFinset_mono hHG)]; rw [← card_attach]
  by_contra! hG
  have ⦃t⦄ (ht : t in tris) :
    exists x y, x in t ∧ y in t ∧ x != y ∧ s(x, y) in G.edgeFinset \ H.edgeFinset := by
    by_contra! h
    refine hH t ?_
    simp only [not_and, mem_sdiff, not_not, mem_edgeFinset, mem_edgeSet] at h
    obtain ⟨x, y, z, xy, xz, yz, rfl⟩ := is3Clique_iff.1 (mem_cliqueFinset_iff.1 <| htris ht)
    rw [is3Clique_triple_iff]
    refine ⟨h _ _ ?_ ?_ xy.ne xy, h _ _ ?_ ?_ xz.ne xz, h _ _ ?_ ?_ yz.ne yz⟩ <;> simp
  choose fx fy hfx hfy hfne fmem using this
  let f (t : {x // x in tris}) : Sym2 α := s(fx t.2, fy t.2)
  have hf (x) (_ : x in tris.attach) : f x in G.edgeFinset \ H.edgeFinset := fmem _
  obtain ⟨⟨t₁, ht₁⟩, -, ⟨t₂, ht₂⟩, -, tne, t : s(_, _) = s(_, _)⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to hG hf
  dsimp at t
  have i := pd ht₁ ht₂ (Subtype.val_injective.ne tne)
  rw [Sym2.eq_iff] at t
  obtain t | t := t
  · exact hfne _ (i ⟨hfx ht₁, t.1.symm ▸ hfx ht₂⟩ ⟨hfy ht₁, t.2.symm ▸ hfy ht₂⟩)
  · exact hfne _ (i ⟨hfx ht₁, t.1.symm ▸ hfy ht₂⟩ ⟨hfy ht₁, t.2.symm ▸ hfx ht₂⟩)

/--
lemma `farFromTriangleFree_of_disjoint_triangles` / 引理 `farFromTriangleFree_of_disjoint_triangles`

English:
lemma farFromTriangleFree_of_disjoint_triangles
  statement: (tris : Finset (Finset α))
  proof: by
  rw [farFromTriangleFree_iff]
  intro H _ hG hH
  rw [← Nat.cast_sub (card_le_card <| edgeFinset_mono hG)]
  exact tris_big.trans
    (Nat.cast_le.2 <| farFromTriangleFree_of_disjoint_triangles_aux htris pd hG hH)

中文:
引理 farFromTriangleFree_of_disjoint_triangles
  结论: (tris : 有限集 (有限集 α))
  证明: by
  rw [farFromTriangleFree_iff]
  intro H _ hG hH
  rw [← Nat.cast_sub (card_le_card <| edgeFinset_mono hG)]
  exact tris_big.trans
    (Nat.cast_le.2 <| farFromTriangleFree_of_disjoint_triangles_aux htris pd hG hH)

Depends on / 依赖: Nat.cast_le, Nat.cast_sub, card_le_card, cast_le, cast_sub, edgeFinset_mono, farFromTriangleFree_iff, farFromTriangleFree_of_disjoint_triangles_aux, tris_big, tris_big.trans
-/
lemma farFromTriangleFree_of_disjoint_triangles (tris : Finset (Finset α))
    (htris : tris subseteq G.cliqueFinset 3)
    (pd : (tris : Set (Finset α)).Pairwise fun x y => (x inter y : Set α).Subsingleton)
    (tris_big : ε * (card α ^ 2 : Nat) <= #tris) :
    G.FarFromTriangleFree ε := by
  rw [farFromTriangleFree_iff]
  intro H _ hG hH
  rw [← Nat.cast_sub (card_le_card <| edgeFinset_mono hG)]
  exact tris_big.trans
    (Nat.cast_le.2 <| farFromTriangleFree_of_disjoint_triangles_aux htris pd hG hH)

/--
lemma `EdgeDisjointTriangles.farFromTriangleFree` / 引理 `EdgeDisjointTriangles.farFromTriangleFree`

English:
lemma EdgeDisjointTriangles.farFromTriangleFree
  statement: (hG : G.EdgeDisjointTriangles)
  proof: farFromTriangleFree_of_disjoint_triangles _ Subset.rfl (by simpa using! hG) tris_big

中文:
引理 EdgeDisjointTriangles.farFromTriangleFree
  结论: (hG : G.EdgeDisjointTriangles)
  证明: farFromTriangleFree_of_disjoint_triangles _ Subset.rfl (by simpa using! hG) tris_big
-/
protected lemma EdgeDisjointTriangles.farFromTriangleFree (hG : G.EdgeDisjointTriangles)
    (tris_big : ε * (card α ^ 2 : Nat) <= #(G.cliqueFinset 3)) :
    G.FarFromTriangleFree ε :=
  farFromTriangleFree_of_disjoint_triangles _ Subset.rfl (by simpa using! hG) tris_big

end DecidableEq

variable [Nonempty α]

/--
lemma `FarFromTriangleFree.lt_half` / 引理 `FarFromTriangleFree.lt_half`

English:
lemma FarFromTriangleFree.lt_half
  given: (hε : G.FarFromTriangleFree ε)
  statement: ε < 2⁻¹
  proof: by
  refine lt_of_mul_lt_mul_right (α := 𝕜) (a := Fintype.card α ^ 2) ?_ (by positivity)
  calc
        ε * Fintype.card α ^ 2
    _ <= #G.edgeFinset := by simpa using hε.le_card_edgeFinset (by simp)
    _ <= (Fintype.card α).choose 2 := by gcongr; exact card_edgeFinset_le_card_choose_two
    _ < 2⁻

中文:
引理 FarFromTriangleFree.lt_half
  条件: (hε : G.FarFromTriangleFree ε)
  结论: ε < 2⁻¹
  证明: by
  refine lt_of_mul_lt_mul_right (α := 𝕜) (a := Fintype.card α ^ 2) ?_ (by positivity)
  calc
        ε * Fintype.card α ^ 2
    _ <= #G.edgeFinset := by simpa using hε.le_card_edgeFinset (by simp)
    _ <= (Fintype.card α).choose 2 := by gcongr; exact card_edgeFinset_le_card_choose_two
    _ < 2⁻

Depends on / 依赖: Fintype, Fintype.card, G.edgeFinset, Nat.choose_lt_pow_div, card_edgeFinset_le_card_choose_two, choose_lt_pow_div, div_eq_inv_mul, edgeFinset, le_card_edgeFinset, le_rfl, lt_of_mul_lt_mul_right
-/
lemma FarFromTriangleFree.lt_half (hε : G.FarFromTriangleFree ε) : ε < 2⁻¹ := by
  refine lt_of_mul_lt_mul_right (α := 𝕜) (a := Fintype.card α ^ 2) ?_ (by positivity)
  calc
        ε * Fintype.card α ^ 2
    _ <= #G.edgeFinset := by simpa using hε.le_card_edgeFinset (by simp)
    _ <= (Fintype.card α).choose 2 := by gcongr; exact card_edgeFinset_le_card_choose_two
    _ < 2⁻¹ * Fintype.card α ^ 2 := by
      simpa [← div_eq_inv_mul] using Nat.choose_lt_pow_div (by positivity) le_rfl

/--
lemma `FarFromTriangleFree.lt_one` / 引理 `FarFromTriangleFree.lt_one`

English:
lemma FarFromTriangleFree.lt_one
  given: (hG : G.FarFromTriangleFree ε)
  statement: ε < 1
  proof: hG.lt_half.trans two_inv_lt_one

中文:
引理 FarFromTriangleFree.lt_one
  条件: (hG : G.FarFromTriangleFree ε)
  结论: ε < 1
  证明: hG.lt_half.trans two_inv_lt_one

Depends on / 依赖: hG.lt_half.trans, lt_half, two_inv_lt_one
-/
lemma FarFromTriangleFree.lt_one (hG : G.FarFromTriangleFree ε) : ε < 1 :=
  hG.lt_half.trans two_inv_lt_one

/--
theorem `FarFromTriangleFree.nonpos` / 定理 `FarFromTriangleFree.nonpos`

English:
theorem FarFromTriangleFree.nonpos
  given: (h₀ : G.FarFromTriangleFree ε) (h₁ : G.CliqueFree 3)
  proof: by
  have := h₀ (empty_subset _)
  rw [coe_empty]; rw [Finset.card_empty]; rw [cast_zero]; rw [deleteEdges_empty] at this
  exact nonpos_of_mul_nonpos_left (this h₁) (cast_pos.2 <| sq_pos_of_pos Fintype.card_pos)

中文:
定理 FarFromTriangleFree.nonpos
  条件: (h₀ : G.FarFromTriangleFree ε) (h₁ : G.CliqueFree 3)
  证明: by
  have := h₀ (empty_subset _)
  rw [coe_empty]; rw [Finset.card_empty]; rw [cast_zero]; rw [deleteEdges_empty] at this
  exact nonpos_of_mul_nonpos_left (this h₁) (cast_pos.2 <| sq_pos_of_pos Fintype.card_pos)

Depends on / 依赖: Finset, Finset.card_empty, Fintype, Fintype.card_pos, card_empty, card_pos, cast_pos, cast_zero, coe_empty, deleteEdges_empty, empty_subset, nonpos_of_mul_nonpos_left, sq_pos_of_pos
-/
theorem FarFromTriangleFree.nonpos (h₀ : G.FarFromTriangleFree ε) (h₁ : G.CliqueFree 3) :
    ε <= 0 := by
  have := h₀ (empty_subset _)
  rw [coe_empty]; rw [Finset.card_empty]; rw [cast_zero]; rw [deleteEdges_empty] at this
  exact nonpos_of_mul_nonpos_left (this h₁) (cast_pos.2 <| sq_pos_of_pos Fintype.card_pos)

/--
theorem `CliqueFree.not_farFromTriangleFree` / 定理 `CliqueFree.not_farFromTriangleFree`

English:
theorem CliqueFree.not_farFromTriangleFree
  given: (hG : G.CliqueFree 3) (hε : 0 < ε)
  proof: fun h => (h.nonpos hG).not_gt hε

中文:
定理 CliqueFree.not_farFromTriangleFree
  条件: (hG : G.CliqueFree 3) (hε : 0 < ε)
  证明: fun h => (h.nonpos hG).not_gt hε

Depends on / 依赖: h.nonpos, nonpos, not_gt
-/
theorem CliqueFree.not_farFromTriangleFree (hG : G.CliqueFree 3) (hε : 0 < ε) :
    ¬G.FarFromTriangleFree ε := fun h => (h.nonpos hG).not_gt hε

/--
theorem `FarFromTriangleFree.not_cliqueFree` / 定理 `FarFromTriangleFree.not_cliqueFree`

English:
theorem FarFromTriangleFree.not_cliqueFree
  given: (hG : G.FarFromTriangleFree ε) (hε : 0 < ε)
  proof: fun h => (hG.nonpos h).not_gt hε

中文:
定理 FarFromTriangleFree.not_cliqueFree
  条件: (hG : G.FarFromTriangleFree ε) (hε : 0 < ε)
  证明: fun h => (hG.nonpos h).not_gt hε

Depends on / 依赖: hG.nonpos, nonpos, not_gt
-/
theorem FarFromTriangleFree.not_cliqueFree (hG : G.FarFromTriangleFree ε) (hε : 0 < ε) :
    ¬G.CliqueFree 3 := fun h => (hG.nonpos h).not_gt hε

/--
theorem `FarFromTriangleFree.cliqueFinset_nonempty` / 定理 `FarFromTriangleFree.cliqueFinset_nonempty`

English:
theorem FarFromTriangleFree.cliqueFinset_nonempty
  statement: [DecidableEq α]
  proof: nonempty_of_ne_empty cliqueFinset_eq_empty_iff.not.2 hG.not_cliqueFree hε

中文:
定理 FarFromTriangleFree.cliqueFinset_nonempty
  结论: [DecidableEq α]
  证明: nonempty_of_ne_empty cliqueFinset_eq_empty_iff.not.2 hG.not_cliqueFree hε

Depends on / 依赖: cliqueFinset_eq_empty_iff, cliqueFinset_eq_empty_iff.not, hG.not_cliqueFree, nonempty_of_ne_empty, not_cliqueFree
-/
theorem FarFromTriangleFree.cliqueFinset_nonempty [DecidableEq α]
    (hG : G.FarFromTriangleFree ε) (hε : 0 < ε) : (G.cliqueFinset 3).Nonempty :=
nonempty_of_ne_empty cliqueFinset_eq_empty_iff.not.2 hG.not_cliqueFree hε

end SimpleGraph
