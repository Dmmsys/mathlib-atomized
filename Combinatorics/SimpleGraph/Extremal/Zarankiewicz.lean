/-
Copyright (c) 2026 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Rify

/-!
# The Zarankiewicz function

This file defines the **Zarankiewicz function** in terms of bipartite graphs.
-/

public section

open Finset Fintype

namespace SimpleGraph

/--
Definition of `zarankiewicz` / `zarankiewicz` 的定义

English:
definition zarankiewicz
  signature: (m n s t : Nat)
  body: open Classical in
  sup { G : SimpleGraph (Fin m oplus Fin n) | G <= completeBipartiteGraph (Fin m) (Fin n)
    ∧ (completeBipartiteGraph (Fin s) (Fin t)).Free G} (#·.edgeFinset)

中文:
定义 zarankiewicz
  签名: (m n s t : 自然数)
  定义体: open Classical in
  sup { G : SimpleGraph (Fin m oplus Fin n) | G <= completeBipartiteGraph (Fin m) (Fin n)
    ∧ (completeBipartiteGraph (Fin s) (Fin t)).Free G} (#·.edgeFinset)

Depends on / 依赖: Classical, SimpleGraph, completeBipartiteGraph, edgeFinset
-/
noncomputable def zarankiewicz (m n s t : Nat) : Nat :=
  open Classical in
  sup { G : SimpleGraph (Fin m oplus Fin n) | G <= completeBipartiteGraph (Fin m) (Fin n)
    ∧ (completeBipartiteGraph (Fin s) (Fin t)).Free G} (#·.edgeFinset)

variable {m n s t : Nat} {V W α β : Type*} [Fintype V] [Fintype W] [Fintype α] [Fintype β]

open Classical in
/--
theorem `zarankiewicz_of_fintypeCard_eq` / 定理 `zarankiewicz_of_fintypeCard_eq`

English:
theorem zarankiewicz_of_fintypeCard_eq
  proof: by
  let e₁ := completeBipartiteGraphCongr
    (Fintype.equivFinOfCardEq hm) (Fintype.equivFinOfCardEq hn)
  let K := completeBipartiteGraph (Fin s) (Fin t)
  let e₂ := completeBipartiteGraphCongr
    (Fintype.equivFinOfCardEq hs) (Fintype.equivFinOfCardEq ht)
  rw [zarankiewicz]; rw [le_antisymm_if

中文:
定理 zarankiewicz_of_fintypeCard_eq
  证明: by
  let e₁ := completeBipartiteGraphCongr
    (Fintype.equivFinOfCardEq hm) (Fintype.equivFinOfCardEq hn)
  let K := completeBipartiteGraph (Fin s) (Fin t)
  let e₂ := completeBipartiteGraphCongr
    (Fintype.equivFinOfCardEq hs) (Fintype.equivFinOfCardEq ht)
  rw [zarankiewicz]; rw [le_antisymm_if

Depends on / 依赖: Finset, Finset.sup_le_iff, Fintype, Fintype.equivFinOfCardEq, Iso.card_edgeFi, all_goals, and_intros, card_edgeFi, completeBipartiteGraph, completeBipartiteGraphCongr, equivFinOfCardEq, h_free, h_le, le_antisymm_iff, mem_filter, mem_univ, on_goal, simp_rw, sup_le_iff, true_and
-/
theorem zarankiewicz_of_fintypeCard_eq
    (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) :
    zarankiewicz m n s t =
      sup { G : SimpleGraph (V oplus W) | G <= completeBipartiteGraph V W
        ∧ (completeBipartiteGraph α β).Free G} (#·.edgeFinset) := by
  let e₁ := completeBipartiteGraphCongr
    (Fintype.equivFinOfCardEq hm) (Fintype.equivFinOfCardEq hn)
  let K := completeBipartiteGraph (Fin s) (Fin t)
  let e₂ := completeBipartiteGraphCongr
    (Fintype.equivFinOfCardEq hs) (Fintype.equivFinOfCardEq ht)
  rw [zarankiewicz]; rw [le_antisymm_iff]
  and_intros
  on_goal 1 =>
    let e₁ := e₁.symm
    let K := completeBipartiteGraph α β
    let e₂ := e₂.symm
  all_goals
    simp_rw [Finset.sup_le_iff, mem_filter, mem_univ, true_and]
    intro G ⟨h_le, h_free⟩
    simp_rw [Iso.card_edgeFinset_eq (.map e₁.toEquiv G)]
    have h' : G.map e₁.toEquiv.toEmbedding in univ.filter fun G =>
        G <= completeBipartiteGraph _ _ ∧ K.Free G := by
      rw [mem_filter_univ]; rw [map_le_iff_le_comap]
      refine ⟨fun _ _ hadj => ?_, ?_⟩
      · replace h_le := h_le hadj
        rw [← Embedding.map_adj_iff e₁.toEmbedding]; rw [← comap_adj] at h_le
        exact h_le
      · rw [Function.Embedding.coeFn_mk, ← free_congr e₂ (.map e₁.toEquiv G)]
        exact h_free
    have h_le_sup := @le_sup _ _ _ _ _ (#·.edgeFinset) (G.map e₁.toEquiv.toEmbedding) h'
    simp_rw [← card_coe, mem_edgeFinset] at h_le_sup ⊢
    exact h_le_sup

/--
theorem `zarankiewicz_le_iff` / 定理 `zarankiewicz_le_iff`

English:
theorem zarankiewicz_le_iff
  proof: by
  simp_rw [zarankiewicz_of_fintypeCard_eq hm hn hs ht,
    Finset.sup_le_iff, mem_filter, mem_univ, true_and]
exact ⟨fun h _ _ h_le h_free => (h _ ⟨h_le, h_free⟩).trans_eq' by convert rfl,
    fun h _ ⟨h_le, h_free⟩ => by convert h h_le h_free⟩

中文:
定理 zarankiewicz_le_iff
  证明: by
  simp_rw [zarankiewicz_of_fintypeCard_eq hm hn hs ht,
    Finset.sup_le_iff, mem_filter, mem_univ, true_and]
exact ⟨fun h _ _ h_le h_free => (h _ ⟨h_le, h_free⟩).trans_eq' by convert rfl,
    fun h _ ⟨h_le, h_free⟩ => by convert h h_le h_free⟩

Depends on / 依赖: Finset, Finset.sup_le_iff, convert, h_free, h_le, mem_filter, mem_univ, simp_rw, sup_le_iff, trans_eq, true_and, zarankiewicz_of_fintypeCard_eq
-/
theorem zarankiewicz_le_iff
    (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) (x : Nat) :
    zarankiewicz m n s t <= x ↔
      forall ⦃G : SimpleGraph (V oplus W)⦄ [DecidableRel G.Adj], G <= completeBipartiteGraph V W ->
        (completeBipartiteGraph α β).Free G -> #G.edgeFinset <= x := by
  simp_rw [zarankiewicz_of_fintypeCard_eq hm hn hs ht,
    Finset.sup_le_iff, mem_filter, mem_univ, true_and]
exact ⟨fun h _ _ h_le h_free => (h _ ⟨h_le, h_free⟩).trans_eq' by convert rfl,
    fun h _ ⟨h_le, h_free⟩ => by convert h h_le h_free⟩

/--
theorem `lt_zarankiewicz_iff` / 定理 `lt_zarankiewicz_iff`

English:
theorem lt_zarankiewicz_iff
  proof: by
  simp_rw [zarankiewicz_of_fintypeCard_eq hm hn hs ht,
    Finset.lt_sup_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨_, ⟨h_le, h_free⟩, h_lt⟩ => ⟨_, _, h_le, h_free, by convert h_lt⟩,
fun ⟨_, _, ⟨h_le, h_free, h_lt⟩⟩ => ⟨_, ⟨h_le, h_free⟩, h_lt.trans_eq by convert rfl⟩⟩

中文:
定理 lt_zarankiewicz_iff
  证明: by
  simp_rw [zarankiewicz_of_fintypeCard_eq hm hn hs ht,
    Finset.lt_sup_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨_, ⟨h_le, h_free⟩, h_lt⟩ => ⟨_, _, h_le, h_free, by convert h_lt⟩,
fun ⟨_, _, ⟨h_le, h_free, h_lt⟩⟩ => ⟨_, ⟨h_le, h_free⟩, h_lt.trans_eq by convert rfl⟩⟩

Depends on / 依赖: Finset, Finset.lt_sup_iff, convert, h_free, h_le, h_lt, h_lt.trans_eq, lt_sup_iff, mem_filter, mem_univ, simp_rw, trans_eq, true_and, zarankiewicz_of_fintypeCard_eq
-/
theorem lt_zarankiewicz_iff
    (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) (x : Nat) :
    x < zarankiewicz m n s t ↔
      exists G : SimpleGraph (V oplus W), exists _ : DecidableRel G.Adj, G <= completeBipartiteGraph V W ∧
        (completeBipartiteGraph α β).Free G ∧ x < #G.edgeFinset := by
  simp_rw [zarankiewicz_of_fintypeCard_eq hm hn hs ht,
    Finset.lt_sup_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨_, ⟨h_le, h_free⟩, h_lt⟩ => ⟨_, _, h_le, h_free, by convert h_lt⟩,
fun ⟨_, _, ⟨h_le, h_free, h_lt⟩⟩ => ⟨_, ⟨h_le, h_free⟩, h_lt.trans_eq by convert rfl⟩⟩

variable {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]

@[inherit_doc zarankiewicz_le_iff]
/--
theorem `zarankiewicz_le_iff_of_nonneg` / 定理 `zarankiewicz_le_iff_of_nonneg`

English:
theorem zarankiewicz_le_iff_of_nonneg
  proof: by
  simp_rw [← Nat.le_floor_iff h]
  exact zarankiewicz_le_iff hm hn hs ht ⌊x⌋₊

@[inherit_doc lt_zarankiewicz_iff]

中文:
定理 zarankiewicz_le_iff_of_nonneg
  证明: by
  simp_rw [← Nat.le_floor_iff h]
  exact zarankiewicz_le_iff hm hn hs ht ⌊x⌋₊

@[inherit_doc lt_zarankiewicz_iff]

Depends on / 依赖: Nat.le_floor_iff, le_floor_iff, simp_rw, zarankiewicz_le_iff
-/
theorem zarankiewicz_le_iff_of_nonneg
    (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) {x : R} (h : 0 <= x) :
    zarankiewicz m n s t <= x ↔
      forall ⦃G : SimpleGraph (V oplus W)⦄ [DecidableRel G.Adj], G <= completeBipartiteGraph V W ->
        (completeBipartiteGraph α β).Free G -> #G.edgeFinset <= x := by
  simp_rw [← Nat.le_floor_iff h]
  exact zarankiewicz_le_iff hm hn hs ht ⌊x⌋₊

@[inherit_doc lt_zarankiewicz_iff]
/--
theorem `lt_zarankiewicz_iff_of_nonneg` / 定理 `lt_zarankiewicz_iff_of_nonneg`

English:
theorem lt_zarankiewicz_iff_of_nonneg
  proof: by
  simp_rw [← Nat.floor_lt h]
  exact lt_zarankiewicz_iff hm hn hs ht ⌊x⌋₊

中文:
定理 lt_zarankiewicz_iff_of_nonneg
  证明: by
  simp_rw [← Nat.floor_lt h]
  exact lt_zarankiewicz_iff hm hn hs ht ⌊x⌋₊

Depends on / 依赖: Nat.floor_lt, floor_lt, lt_zarankiewicz_iff, simp_rw
-/
theorem lt_zarankiewicz_iff_of_nonneg
    (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) {x : R} (h : 0 <= x) :
    x < zarankiewicz m n s t ↔
      exists G : SimpleGraph (V oplus W), exists _ : DecidableRel G.Adj, G <= completeBipartiteGraph V W ∧
        (completeBipartiteGraph α β).Free G ∧ x < #G.edgeFinset := by
  simp_rw [← Nat.floor_lt h]
  exact lt_zarankiewicz_iff hm hn hs ht ⌊x⌋₊

open Classical in
/--
theorem `zarankiewicz_le_extremalNumber` / 定理 `zarankiewicz_le_extremalNumber`

English:
theorem zarankiewicz_le_extremalNumber
  given: (hs : card α = s) (ht : card β = t)
  proof: by
  conv =>
    enter [2, 1]
    rw [← Fintype.card_fin (m + n)]
  simp_rw [zarankiewicz, Finset.sup_le_iff, mem_filter, mem_univ, true_and]
  intro B ⟨_, h⟩
  rw [(Iso.map finSumFinEquiv B).card_edgeFinset_eq]
refine card_edgeFinset_le_extremalNumber
    (h.congr_left ?_).congr_right (Iso.map finS

中文:
定理 zarankiewicz_le_extremalNumber
  条件: (hs : card α = s) (ht : card β = t)
  证明: by
  conv =>
    enter [2, 1]
    rw [← Fintype.card_fin (m + n)]
  simp_rw [zarankiewicz, Finset.sup_le_iff, mem_filter, mem_univ, true_and]
  intro B ⟨_, h⟩
  rw [(Iso.map finSumFinEquiv B).card_edgeFinset_eq]
refine card_edgeFinset_le_extremalNumber
    (h.congr_left ?_).congr_right (Iso.map finS

Depends on / 依赖: Finset, Finset.sup_le_iff, Fintype, Fintype.card_fin, Fintype.equivFinOfCardEq, Iso.map, card_edgeFinset_eq, card_edgeFinset_le_extremalNumber, card_fin, completeBipartiteGraphCongr, congr_left, congr_right, equivFinOfCardEq, finSumFinEquiv, h.congr_left, mem_filter, mem_univ, simp_rw, sup_le_iff, true_and
-/
theorem zarankiewicz_le_extremalNumber (hs : card α = s) (ht : card β = t) :
    zarankiewicz m n s t <= extremalNumber (m + n) (completeBipartiteGraph α β) := by
  conv =>
    enter [2, 1]
    rw [← Fintype.card_fin (m + n)]
  simp_rw [zarankiewicz, Finset.sup_le_iff, mem_filter, mem_univ, true_and]
  intro B ⟨_, h⟩
  rw [(Iso.map finSumFinEquiv B).card_edgeFinset_eq]
refine card_edgeFinset_le_extremalNumber
    (h.congr_left ?_).congr_right (Iso.map finSumFinEquiv B).symm
  exact completeBipartiteGraphCongr
    (Fintype.equivFinOfCardEq hs) (Fintype.equivFinOfCardEq ht)

/--
theorem `two_mul_extremalNumber_le_zarankiewicz_symm` / 定理 `two_mul_extremalNumber_le_zarankiewicz_symm`

English:
theorem two_mul_extremalNumber_le_zarankiewicz_symm
  proof: by
  conv =>
    enter [1, 2, 1]
    rw [← Fintype.card_fin n]
  rify
  rw [← le_div_iff₀' (by positivity)]; rw [extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro G _ h
  rw [le_div_iff₀' (by positivity)]; rw [← Nat.cast_two]; rw [← Nat.cast_mul]; rw [Nat.cast_le]
  apply Finset.le_sup_of_l

中文:
定理 two_mul_extremalNumber_le_zarankiewicz_symm
  证明: by
  conv =>
    enter [1, 2, 1]
    rw [← Fintype.card_fin n]
  rify
  rw [← le_div_iff₀' (by positivity)]; rw [extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro G _ h
  rw [le_div_iff₀' (by positivity)]; rw [← Nat.cast_two]; rw [← Nat.cast_mul]; rw [Nat.cast_le]
  apply Finset.le_sup_of_l

Depends on / 依赖: Finset, Finset.le_sup_of_le, Fintype, Fintype.card_fin, G.bipartiteDoubleCover, Iso.toCopy, Nat.cast_le, Nat.cast_mul, Nat.cast_two, bipartiteDoubleCover, bipartiteDoubleCover_le, card_fin, cast_le, cast_mul, cast_two, completeBipartiteGraph_isContained_bipartiteDoubleCover, completeBipartiteGraph_isContained_bipartiteDoubleCover.mp, contrapose, extremalNumber_le_iff_of_nonneg, h.trans
-/
theorem two_mul_extremalNumber_le_zarankiewicz_symm
    [Nonempty α] [Nonempty β] (hs : card α = s) (ht : card β = t) :
    2 * extremalNumber n (completeBipartiteGraph α β) <= zarankiewicz n n s t := by
  conv =>
    enter [1, 2, 1]
    rw [← Fintype.card_fin n]
  rify
  rw [← le_div_iff₀' (by positivity)]; rw [extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro G _ h
  rw [le_div_iff₀' (by positivity)]; rw [← Nat.cast_two]; rw [← Nat.cast_mul]; rw [Nat.cast_le]
  apply Finset.le_sup_of_le (b := G.bipartiteDoubleCover)
  · simp_rw [mem_filter, mem_univ, true_and]
    refine ⟨bipartiteDoubleCover_le, ?_⟩
    contrapose! h
refine completeBipartiteGraph_isContained_bipartiteDoubleCover.mp
      h.trans' ⟨Iso.toCopy ?_⟩
    exact completeBipartiteGraphCongr
      (Fintype.equivFinOfCardEq hs) (Fintype.equivFinOfCardEq ht)
  · convert card_edgeFinset_bipartiteDoubleCover.symm.le

end SimpleGraph
