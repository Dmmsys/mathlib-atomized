/-
Copyright (c) 2025 Youheng Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youheng Luo
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card

/-!
# Edge Connectivity

This file defines k-edge-connectivity for simple graphs.

## Main definitions

* `SimpleGraph.IsEdgeReachable`: Two vertices are `k`-edge-reachable if they remain reachable after
  removing strictly fewer than `k` edges.
* `SimpleGraph.IsEdgeConnected`: A graph is `k`-edge-connected if any two vertices are
  `k`-edge-reachable.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {k l : Nat} {u v w x y : V}

variable (G k u v) in
/--
Definition of `IsEdgeReachable` / `IsEdgeReachable` 的定义

English:
definition IsEdgeReachable
  signature: : Prop
  body: forall ⦃s : Set (Sym2 V)⦄, s.encard < k -> (G.deleteEdges s).Reachable u v

中文:
定义 IsEdgeReachable
  签名: : 命题
  定义体: forall ⦃s : Set (Sym2 V)⦄, s.encard < k -> (G.deleteEdges s).Reachable u v

Depends on / 依赖: G.deleteEdges, Reachable, deleteEdges, encard, s.encard
-/
def IsEdgeReachable : Prop :=
  forall ⦃s : Set (Sym2 V)⦄, s.encard < k -> (G.deleteEdges s).Reachable u v

variable (G k) in
/--
Definition of `IsEdgeConnected` / `IsEdgeConnected` 的定义

English:
definition IsEdgeConnected
  signature: : Prop
  body: forall u v, G.IsEdgeReachable k u v

@[refl, simp]

中文:
定义 IsEdgeConnected
  签名: : 命题
  定义体: forall u v, G.IsEdgeReachable k u v

@[refl, simp]

Depends on / 依赖: G.IsEdgeReachable, IsEdgeReachable
-/
def IsEdgeConnected : Prop := forall u v, G.IsEdgeReachable k u v

@[refl, simp]
/--
lemma `IsEdgeReachable.rfl` / 引理 `IsEdgeReachable.rfl`

English:
lemma IsEdgeReachable.rfl
  given: {u : V}
  statement: G.IsEdgeReachable k u u
  proof: fun _ _ => .rfl

中文:
引理 IsEdgeReachable.rfl
  条件: {u : V}
  结论: G.IsEdgeReachable k u u
  证明: fun _ _ => .rfl
-/
protected lemma IsEdgeReachable.rfl {u : V} : G.IsEdgeReachable k u u := fun _ _ => .rfl

/--
lemma `IsEdgeReachable.refl` / 引理 `IsEdgeReachable.refl`

English:
lemma IsEdgeReachable.refl
  given: (u : V)
  statement: G.IsEdgeReachable k u u
  proof: .rfl

@[symm]

中文:
引理 IsEdgeReachable.refl
  条件: (u : V)
  结论: G.IsEdgeReachable k u u
  证明: .rfl

@[symm]
-/
protected lemma IsEdgeReachable.refl (u : V) : G.IsEdgeReachable k u u := .rfl

@[symm]
/--
lemma `IsEdgeReachable.symm` / 引理 `IsEdgeReachable.symm`

English:
lemma IsEdgeReachable.symm
  given: (h : G.IsEdgeReachable k u v)
  statement: G.IsEdgeReachable k v u
  proof: fun _ hk => (h hk).symm

中文:
引理 IsEdgeReachable.symm
  条件: (h : G.IsEdgeReachable k u v)
  结论: G.IsEdgeReachable k v u
  证明: fun _ hk => (h hk).symm
-/
lemma IsEdgeReachable.symm (h : G.IsEdgeReachable k u v) : G.IsEdgeReachable k v u :=
  fun _ hk => (h hk).symm

/--
lemma `isEdgeReachable_comm` / 引理 `isEdgeReachable_comm`

English:
lemma isEdgeReachable_comm
  statement: G.IsEdgeReachable k u v ↔ G.IsEdgeReachable k v u
  proof: ⟨.symm, .symm⟩

@[trans]

中文:
引理 isEdgeReachable_comm
  结论: G.IsEdgeReachable k u v ↔ G.IsEdgeReachable k v u
  证明: ⟨.symm, .symm⟩

@[trans]
-/
lemma isEdgeReachable_comm : G.IsEdgeReachable k u v ↔ G.IsEdgeReachable k v u :=
  ⟨.symm, .symm⟩

@[trans]
/--
lemma `IsEdgeReachable.trans` / 引理 `IsEdgeReachable.trans`

English:
lemma IsEdgeReachable.trans
  given: (h1 : G.IsEdgeReachable k u v) (h2 : G.IsEdgeReachable k v w)
  proof: fun _ hk => (h1 hk).trans (h2 hk)

@[gcongr]

中文:
引理 IsEdgeReachable.trans
  条件: (h1 : G.IsEdgeReachable k u v) (h2 : G.IsEdgeReachable k v w)
  证明: fun _ hk => (h1 hk).trans (h2 hk)

@[gcongr]
-/
lemma IsEdgeReachable.trans (h1 : G.IsEdgeReachable k u v) (h2 : G.IsEdgeReachable k v w) :
    G.IsEdgeReachable k u w := fun _ hk => (h1 hk).trans (h2 hk)

@[gcongr]
/--
lemma `IsEdgeReachable.mono` / 引理 `IsEdgeReachable.mono`

English:
lemma IsEdgeReachable.mono
  given: (hGH : G <= H) (h : G.IsEdgeReachable k u v)
  statement: H.IsEdgeReachable k u v
  proof: .mono deleteEdges_mono hGH fun _ hk => h hk

@[gcongr]

中文:
引理 IsEdgeReachable.mono
  条件: (hGH : G <= H) (h : G.IsEdgeReachable k u v)
  结论: H.IsEdgeReachable k u v
  证明: .mono deleteEdges_mono hGH fun _ hk => h hk

@[gcongr]

Depends on / 依赖: deleteEdges_mono
-/
lemma IsEdgeReachable.mono (hGH : G <= H) (h : G.IsEdgeReachable k u v) : H.IsEdgeReachable k u v :=
.mono deleteEdges_mono hGH fun _ hk => h hk

@[gcongr]
/--
lemma `IsEdgeReachable.anti` / 引理 `IsEdgeReachable.anti`

English:
lemma IsEdgeReachable.anti
  given: (hkl : k <= l) (h : G.IsEdgeReachable l u v)
  statement: G.IsEdgeReachable k u v
  proof: fun _ hk => h by grw [← hkl]; exact hk

@[simp]

中文:
引理 IsEdgeReachable.anti
  条件: (hkl : k <= l) (h : G.IsEdgeReachable l u v)
  结论: G.IsEdgeReachable k u v
  证明: fun _ hk => h by grw [← hkl]; exact hk

@[simp]
-/
lemma IsEdgeReachable.anti (hkl : k <= l) (h : G.IsEdgeReachable l u v) : G.IsEdgeReachable k u v :=
fun _ hk => h by grw [← hkl]; exact hk

@[simp]
/--
lemma `IsEdgeReachable.zero` / 引理 `IsEdgeReachable.zero`

English:
lemma IsEdgeReachable.zero
  statement: G.IsEdgeReachable 0 u v
  proof: by simp [IsEdgeReachable]

中文:
引理 IsEdgeReachable.zero
  结论: G.IsEdgeReachable 0 u v
  证明: by simp [IsEdgeReachable]
-/
protected lemma IsEdgeReachable.zero : G.IsEdgeReachable 0 u v := by simp [IsEdgeReachable]

/--
lemma `IsEdgeConnected.zero` / 引理 `IsEdgeConnected.zero`

English:
lemma IsEdgeConnected.zero
  statement: G.IsEdgeConnected 0
  proof: fun _ _ => .zero

@[simp]

中文:
引理 IsEdgeConnected.zero
  结论: G.IsEdgeConnected 0
  证明: fun _ _ => .zero

@[simp]
-/
@[simp] protected lemma IsEdgeConnected.zero : G.IsEdgeConnected 0 := fun _ _ => .zero

@[simp]
/--
lemma `isEdgeReachable_one` / 引理 `isEdgeReachable_one`

English:
lemma isEdgeReachable_one
  statement: G.IsEdgeReachable 1 u v ↔ G.Reachable u v
  proof: by
  simp [IsEdgeReachable, Order.lt_one_iff]

@[simp]

中文:
引理 isEdgeReachable_one
  结论: G.IsEdgeReachable 1 u v ↔ G.Reachable u v
  证明: by
  simp [IsEdgeReachable, Order.lt_one_iff]

@[simp]

Depends on / 依赖: IsEdgeReachable, Order.lt_one_iff, lt_one_iff
-/
lemma isEdgeReachable_one : G.IsEdgeReachable 1 u v ↔ G.Reachable u v := by
  simp [IsEdgeReachable, Order.lt_one_iff]

@[simp]
/--
lemma `isEdgeConnected_one` / 引理 `isEdgeConnected_one`

English:
lemma isEdgeConnected_one
  statement: G.IsEdgeConnected 1 ↔ G.Preconnected
  proof: by
  simp [IsEdgeConnected, Preconnected]

中文:
引理 isEdgeConnected_one
  结论: G.IsEdgeConnected 1 ↔ G.预连通
  证明: by
  simp [IsEdgeConnected, Preconnected]

Depends on / 依赖: IsEdgeConnected, Preconnected
-/
lemma isEdgeConnected_one : G.IsEdgeConnected 1 ↔ G.Preconnected := by
  simp [IsEdgeConnected, Preconnected]

/--
lemma `IsEdgeReachable.reachable` / 引理 `IsEdgeReachable.reachable`

English:
lemma IsEdgeReachable.reachable
  given: (hk : k != 0) (huv : G.IsEdgeReachable k u v)
  statement: G.Reachable u v
  proof: isEdgeReachable_one.mp (huv.anti (Nat.one_le_iff_ne_zero.mpr hk))

@[nontriviality]

中文:
引理 IsEdgeReachable.reachable
  条件: (hk : k != 0) (huv : G.IsEdgeReachable k u v)
  结论: G.Reachable u v
  证明: isEdgeReachable_one.mp (huv.anti (Nat.one_le_iff_ne_zero.mpr hk))

@[nontriviality]

Depends on / 依赖: Nat.one_le_iff_ne_zero.mpr, huv.anti, isEdgeReachable_one, isEdgeReachable_one.mp, one_le_iff_ne_zero
-/
lemma IsEdgeReachable.reachable (hk : k != 0) (huv : G.IsEdgeReachable k u v) : G.Reachable u v :=
  isEdgeReachable_one.mp (huv.anti (Nat.one_le_iff_ne_zero.mpr hk))

@[nontriviality]
/--
lemma `IsEdgeReachable.of_subsingleton` / 引理 `IsEdgeReachable.of_subsingleton`

English:
lemma IsEdgeReachable.of_subsingleton
  given: [Subsingleton V]
  statement: G.IsEdgeReachable k u v
  proof: fun _ _ => .of_subsingleton

@[nontriviality]

中文:
引理 IsEdgeReachable.of_subsingleton
  条件: [子单例 V]
  结论: G.IsEdgeReachable k u v
  证明: fun _ _ => .of_subsingleton

@[nontriviality]

Depends on / 依赖: of_subsingleton
-/
lemma IsEdgeReachable.of_subsingleton [Subsingleton V] : G.IsEdgeReachable k u v :=
  fun _ _ => .of_subsingleton

@[nontriviality]
/--
lemma `IsEdgeConnected.of_subsingleton` / 引理 `IsEdgeConnected.of_subsingleton`

English:
lemma IsEdgeConnected.of_subsingleton
  given: [Subsingleton V]
  statement: G.IsEdgeConnected k
  proof: fun _ _ => .of_subsingleton

中文:
引理 IsEdgeConnected.of_subsingleton
  条件: [子单例 V]
  结论: G.IsEdgeConnected k
  证明: fun _ _ => .of_subsingleton

Depends on / 依赖: of_subsingleton
-/
lemma IsEdgeConnected.of_subsingleton [Subsingleton V] : G.IsEdgeConnected k :=
  fun _ _ => .of_subsingleton

/--
lemma `IsEdgeConnected.preconnected` / 引理 `IsEdgeConnected.preconnected`

English:
lemma IsEdgeConnected.preconnected
  given: (hk : k != 0) (h : G.IsEdgeConnected k)
  statement: G.Preconnected
  proof: fun u v => (h u v).reachable hk

中文:
引理 IsEdgeConnected.preconnected
  条件: (hk : k != 0) (h : G.IsEdgeConnected k)
  结论: G.预连通
  证明: fun u v => (h u v).reachable hk

Depends on / 依赖: reachable
-/
lemma IsEdgeConnected.preconnected (hk : k != 0) (h : G.IsEdgeConnected k) : G.Preconnected :=
  fun u v => (h u v).reachable hk

/--
lemma `IsEdgeConnected.connected` / 引理 `IsEdgeConnected.connected`

English:
lemma IsEdgeConnected.connected
  given: [Nonempty V] (hk : k != 0) (h : G.IsEdgeConnected k)
  proof: h.preconnected hk

中文:
引理 IsEdgeConnected.connected
  条件: [非空 V] (hk : k != 0) (h : G.IsEdgeConnected k)
  证明: h.preconnected hk

Depends on / 依赖: h.preconnected, preconnected
-/
lemma IsEdgeConnected.connected [Nonempty V] (hk : k != 0) (h : G.IsEdgeConnected k) :
    G.Connected where
  preconnected := h.preconnected hk

/--
lemma `IsEdgeReachable.le_degree` / 引理 `IsEdgeReachable.le_degree`

English:
lemma IsEdgeReachable.le_degree
  statement: [Fintype (G.neighborSet u)] (h : G.IsEdgeReachable k u v)
  proof: by
  classical
  by_contra! hh
  rw [← card_incidenceSet_eq_degree]; rw [← ENat.natCast_lt_natCast]; rw [Set.coe_fintypeCard] at hh
.exists_isPath obtain ⟨w, _⟩ := h hh
simpa using w.adj_snd mt Walk.Nil.eq huv

中文:
引理 IsEdgeReachable.le_degree
  结论: [有限类型 (G.neighborSet u)] (h : G.IsEdgeReachable k u v)
  证明: by
  classical
  by_contra! hh
  rw [← card_incidenceSet_eq_degree]; rw [← ENat.natCast_lt_natCast]; rw [Set.coe_fintypeCard] at hh
.exists_isPath obtain ⟨w, _⟩ := h hh
simpa using w.adj_snd mt Walk.Nil.eq huv

Depends on / 依赖: ENat.natCast_lt_natCast, Set.coe_fintypeCard, Walk.Nil.eq, adj_snd, card_incidenceSet_eq_degree, classical, coe_fintypeCard, exists_isPath, natCast_lt_natCast, w.adj_snd
-/
lemma IsEdgeReachable.le_degree [Fintype (G.neighborSet u)] (h : G.IsEdgeReachable k u v)
    (huv : u != v) : k <= G.degree u := by
  classical
  by_contra! hh
  rw [← card_incidenceSet_eq_degree]; rw [← ENat.natCast_lt_natCast]; rw [Set.coe_fintypeCard] at hh
.exists_isPath obtain ⟨w, _⟩ := h hh
simpa using w.adj_snd mt Walk.Nil.eq huv

/--
lemma `IsEdgeConnected.le_degree` / 引理 `IsEdgeConnected.le_degree`

English:
lemma IsEdgeConnected.le_degree
  statement: [Fintype (G.neighborSet u)] [Nontrivial V]
  proof: by
  obtain ⟨v, hv⟩ := exists_ne u
  exact (h u v).le_degree hv.symm

中文:
引理 IsEdgeConnected.le_degree
  结论: [有限类型 (G.neighborSet u)] [非平凡 V]
  证明: by
  obtain ⟨v, hv⟩ := exists_ne u
  exact (h u v).le_degree hv.symm

Depends on / 依赖: exists_ne, hv.symm, le_degree
-/
lemma IsEdgeConnected.le_degree [Fintype (G.neighborSet u)] [Nontrivial V]
    (h : G.IsEdgeConnected k) : k <= G.degree u := by
  obtain ⟨v, hv⟩ := exists_ne u
  exact (h u v).le_degree hv.symm

/--
lemma `isEdgeReachable_add_one` / 引理 `isEdgeReachable_add_one`

English:
lemma isEdgeReachable_add_one
  given: (hk : k != 0)
  proof: by
  refine ⟨fun h e s hk => ?_, fun h s hs => ?_⟩
  · rw [deleteEdges_deleteEdges, Set.union_comm]
    apply h
    grw [Set.encard_union_le, Set.encard_singleton]
.mpr hk exact ENat.add_lt_add_iff_right ENat.one_ne_top
  obtain rfl | ⟨e, he⟩ := s.eq_empty_or_nonempty
  · simpa using (h s(u, u)).reachable hk
  · rw [← Set.insert_sdiff_self_of_mem he, Set.insert_eq, ← deleteEdges_deleteEdges]
refine h e .mp ?_ ENat.add_lt_add_iff_right ENat.one_ne_top
    rwa [Set.encard_sdiff_singleton_add_one he]

中文:
引理 isEdgeReachable_add_one
  条件: (hk : k != 0)
  证明: by
  refine ⟨fun h e s hk => ?_, fun h s hs => ?_⟩
  · rw [deleteEdges_deleteEdges, Set.union_comm]
    apply h
    grw [Set.encard_union_le, Set.encard_singleton]
.mpr hk exact ENat.add_lt_add_iff_right ENat.one_ne_top
  obtain rfl | ⟨e, he⟩ := s.eq_empty_or_nonempty
  · simpa using (h s(u, u)).reachable hk
  · rw [← Set.insert_sdiff_self_of_mem he, Set.insert_eq, ← deleteEdges_deleteEdges]
refine h e .mp ?_ ENat.add_lt_add_iff_right ENat.one_ne_top
    rwa [Set.encard_sdiff_singleton_add_one he]

Depends on / 依赖: ENat.add_lt_add_iff_right, ENat.one_ne_top, Set.encard_sdiff_singleton_add_one, Set.encard_singleton, Set.encard_union_le, Set.insert_eq, Set.insert_sdiff_self_of_mem, Set.union_comm, add_lt_add_iff_right, deleteEdges_deleteEdges, encard_sdiff_singleton_add_one, encard_singleton, encard_union_le, eq_empty_or_nonempty, insert_eq, insert_sdiff_self_of_mem, one_ne_top, reachable, s.eq_empty_or_nonempty, union_comm
-/
lemma isEdgeReachable_add_one (hk : k != 0) :
    G.IsEdgeReachable (k + 1) u v ↔ forall e, (G.deleteEdges {e}).IsEdgeReachable k u v := by
  refine ⟨fun h e s hk => ?_, fun h s hs => ?_⟩
  · rw [deleteEdges_deleteEdges, Set.union_comm]
    apply h
    grw [Set.encard_union_le, Set.encard_singleton]
.mpr hk exact ENat.add_lt_add_iff_right ENat.one_ne_top
  obtain rfl | ⟨e, he⟩ := s.eq_empty_or_nonempty
  · simpa using (h s(u, u)).reachable hk
  · rw [← Set.insert_sdiff_self_of_mem he, Set.insert_eq, ← deleteEdges_deleteEdges]
refine h e .mp ?_ ENat.add_lt_add_iff_right ENat.one_ne_top
    rwa [Set.encard_sdiff_singleton_add_one he]

/--
lemma `isEdgeConnected_add_one` / 引理 `isEdgeConnected_add_one`

English:
lemma isEdgeConnected_add_one
  given: (hk : k != 0)
  proof: by
  simp [IsEdgeConnected, isEdgeReachable_add_one hk, forall_comm (α := Sym2 _)]

中文:
引理 isEdgeConnected_add_one
  条件: (hk : k != 0)
  证明: by
  simp [IsEdgeConnected, isEdgeReachable_add_one hk, forall_comm (α := Sym2 _)]

Depends on / 依赖: IsEdgeConnected, forall_comm, isEdgeReachable_add_one
-/
lemma isEdgeConnected_add_one (hk : k != 0) :
    G.IsEdgeConnected (k + 1) ↔ forall e, (G.deleteEdges {e}).IsEdgeConnected k := by
  simp [IsEdgeConnected, isEdgeReachable_add_one hk, forall_comm (α := Sym2 _)]

/--
lemma `IsBridge.not_isEdgeReachable_two` / 引理 `IsBridge.not_isEdgeReachable_two`

English:
lemma IsBridge.not_isEdgeReachable_two
  given: (huv : G.IsBridge s(u, v))
  statement: ¬ G.IsEdgeReachable 2 u v
  proof: fun hc => huv hc .trans_lt Nat.one_lt_ofNat Set.encard_singleton _

中文:
引理 IsBridge.not_isEdgeReachable_two
  条件: (huv : G.IsBridge s(u, v))
  结论: ¬ G.IsEdgeReachable 2 u v
  证明: fun hc => huv hc .trans_lt Nat.one_lt_ofNat Set.encard_singleton _

Depends on / 依赖: Nat.one_lt_ofNat, Set.encard_singleton, encard_singleton, one_lt_ofNat, trans_lt
-/
lemma IsBridge.not_isEdgeReachable_two (huv : G.IsBridge s(u, v)) : ¬ G.IsEdgeReachable 2 u v :=
fun hc => huv hc .trans_lt Nat.one_lt_ofNat Set.encard_singleton _

/--
lemma `isBridge_iff_not_isEdgeReachable_two` / 引理 `isBridge_iff_not_isEdgeReachable_two`

English:
lemma isBridge_iff_not_isEdgeReachable_two
  given: (huv : G.Adj u v)
  proof: by
  refine ⟨fun h => h.not_isEdgeReachable_two, fun hc hr => hc fun s hs₂ => ?_⟩
  by_cases! hs₁ : s.encard != (1 : Nat)
  · apply G.isEdgeReachable_one.mpr huv.reachable
    exact lt_of_le_of_ne (ENat.lt_natCast_add_one_iff.mp hs₂) hs₁
  obtain ⟨x, rfl⟩ := s.encard_eq_one.mp hs₁
  obtain rfl | hx := eq_or_ne s(u, v) x
  · exact hr
.reachable · exact deleteEdges_adj.mpr ⟨huv, hx⟩

@[deprecated (since := "2026-05-16")]
alias isBridge_iff_adj_and_not_isEdgeConnected_two := isBridge_iff_not_isEdgeReachable_two

中文:
引理 isBridge_iff_not_isEdgeReachable_two
  条件: (huv : G.伴随 u v)
  证明: by
  refine ⟨fun h => h.not_isEdgeReachable_two, fun hc hr => hc fun s hs₂ => ?_⟩
  by_cases! hs₁ : s.encard != (1 : Nat)
  · apply G.isEdgeReachable_one.mpr huv.reachable
    exact lt_of_le_of_ne (ENat.lt_natCast_add_one_iff.mp hs₂) hs₁
  obtain ⟨x, rfl⟩ := s.encard_eq_one.mp hs₁
  obtain rfl | hx := eq_or_ne s(u, v) x
  · exact hr
.reachable · exact deleteEdges_adj.mpr ⟨huv, hx⟩

@[deprecated (since := "2026-05-16")]
alias isBridge_iff_adj_and_not_isEdgeConnected_two := isBridge_iff_not_isEdgeReachable_two

Depends on / 依赖: ENat.lt_natCast_add_one_iff.mp, G.isEdgeReachable_one.mpr, deleteEdges_adj, deleteEdges_adj.mpr, encard, encard_eq_one, eq_or_ne, h.not_isEdgeReachable_two, huv.reachable, isEdgeReachable_one, lt_natCast_add_one_iff, lt_of_le_of_ne, not_isEdgeReachable_two, reachable, s.encard, s.encard_eq_one.mp
-/
lemma isBridge_iff_not_isEdgeReachable_two (huv : G.Adj u v) :
    G.IsBridge s(u, v) ↔ ¬G.IsEdgeReachable 2 u v := by
  refine ⟨fun h => h.not_isEdgeReachable_two, fun hc hr => hc fun s hs₂ => ?_⟩
  by_cases! hs₁ : s.encard != (1 : Nat)
  · apply G.isEdgeReachable_one.mpr huv.reachable
    exact lt_of_le_of_ne (ENat.lt_natCast_add_one_iff.mp hs₂) hs₁
  obtain ⟨x, rfl⟩ := s.encard_eq_one.mp hs₁
  obtain rfl | hx := eq_or_ne s(u, v) x
  · exact hr
.reachable · exact deleteEdges_adj.mpr ⟨huv, hx⟩

@[deprecated (since := "2026-05-16")]
alias isBridge_iff_adj_and_not_isEdgeConnected_two := isBridge_iff_not_isEdgeReachable_two

/--
lemma `isEdgeReachable_two` / 引理 `isEdgeReachable_two`

English:
lemma isEdgeReachable_two
  statement: G.IsEdgeReachable 2 u v ↔ forall e, (G.deleteEdges {e}).Reachable u v
  proof: by
  simp [isEdgeReachable_add_one]

中文:
引理 isEdgeReachable_two
  结论: G.IsEdgeReachable 2 u v ↔ 对任意 e, (G.deleteEdges {e}).Reachable u v
  证明: by
  simp [isEdgeReachable_add_one]

Depends on / 依赖: isEdgeReachable_add_one
-/
lemma isEdgeReachable_two : G.IsEdgeReachable 2 u v ↔ forall e, (G.deleteEdges {e}).Reachable u v := by
  simp [isEdgeReachable_add_one]

-- TODO: This should be `G.IsEdgeConnected 2 ↔ ∀ e, ¬G.IsBridge e` after
-- https://github.com/leanprover-community/mathlib4/pull/32583
/--
lemma `isEdgeConnected_two` / 引理 `isEdgeConnected_two`

English:
lemma isEdgeConnected_two
  statement: G.IsEdgeConnected 2 ↔ forall e, (G.deleteEdges {e}).Preconnected
  proof: by
  simp [isEdgeConnected_add_one]

中文:
引理 isEdgeConnected_two
  结论: G.IsEdgeConnected 2 ↔ 对任意 e, (G.deleteEdges {e}).预连通
  证明: by
  simp [isEdgeConnected_add_one]

Depends on / 依赖: isEdgeConnected_add_one
-/
lemma isEdgeConnected_two : G.IsEdgeConnected 2 ↔ forall e, (G.deleteEdges {e}).Preconnected := by
  simp [isEdgeConnected_add_one]

/--
lemma `exists_adj_isEdgeReachable_two` / 引理 `exists_adj_isEdgeReachable_two`

English:
lemma exists_adj_isEdgeReachable_two
  given: (hne : u != v) (h : G.IsEdgeReachable 2 u v)
  proof: by
.exists_isPath obtain ⟨w, hw⟩ := h.reachable (by simp)
  have : G.Adj u w.snd := Walk.adj_snd (by grind [Walk.not_nil_of_ne])
  refine ⟨w.snd, this, fun s hs => ?_⟩
  by_cases! h' : s = {s(u, w.snd)}
  · subst h'
refine Reachable.trans (h hs) .reachable.symm w.tail.toDeleteEdge _ (fun hh => ?_)
    have := hw.tail.eq_snd_of_mem_edges (Sym2.eq_swap ▸ hh)
    simp only [Walk.getVert_tail, Nat.reduceAdd] at this
.mp this.symm simpa using hw.getVert_eq_start_iff_of_not_nil (Walk.not_nil_of_ne hne)
· refine Walk.reachable Walk.cons (deleteEdges_adj.mpr ⟨this, ?_⟩) Walk.nil
    contrapose h'
    refine (Set.subsingleton_iff_singleton h').mp ?_
    exact Set.encard_le_one_iff_subsingleton.mp (Order.le_of_lt_succ hs)

中文:
引理 存在_adj_isEdgeReachable_two
  条件: (hne : u != v) (h : G.IsEdgeReachable 2 u v)
  证明: by
.exists_isPath obtain ⟨w, hw⟩ := h.reachable (by simp)
  have : G.Adj u w.snd := Walk.adj_snd (by grind [Walk.not_nil_of_ne])
  refine ⟨w.snd, this, fun s hs => ?_⟩
  by_cases! h' : s = {s(u, w.snd)}
  · subst h'
refine Reachable.trans (h hs) .reachable.symm w.tail.toDeleteEdge _ (fun hh => ?_)
    have := hw.tail.eq_snd_of_mem_edges (Sym2.eq_swap ▸ hh)
    simp only [Walk.getVert_tail, Nat.reduceAdd] at this
.mp this.symm simpa using hw.getVert_eq_start_iff_of_not_nil (Walk.not_nil_of_ne hne)
· refine Walk.reachable Walk.cons (deleteEdges_adj.mpr ⟨this, ?_⟩) Walk.nil
    contrapose h'
    refine (Set.subsingleton_iff_singleton h').mp ?_
    exact Set.encard_le_one_iff_subsingleton.mp (Order.le_of_lt_succ hs)

Depends on / 依赖: G.Adj, Nat.reduceAdd, Reachable, Reachable.trans, Sym2.eq_swap, Walk.adj_snd, Walk.getVert_tail, Walk.not_nil_of_ne, adj_snd, eq_snd_of_mem_edges, eq_swap, exists_isPath, getVert_eq_start_iff_of_not_nil, getVert_tail, h.reachable, hw.getVert_eq_start_iff_of_not_nil, hw.tail.eq_snd_of_mem_edges, not_nil_of_ne, reachable, reachable.symm
-/
lemma exists_adj_isEdgeReachable_two (hne : u != v) (h : G.IsEdgeReachable 2 u v) :
    exists w : V, G.Adj u w ∧ G.IsEdgeReachable 2 u w := by
.exists_isPath obtain ⟨w, hw⟩ := h.reachable (by simp)
  have : G.Adj u w.snd := Walk.adj_snd (by grind [Walk.not_nil_of_ne])
  refine ⟨w.snd, this, fun s hs => ?_⟩
  by_cases! h' : s = {s(u, w.snd)}
  · subst h'
refine Reachable.trans (h hs) .reachable.symm w.tail.toDeleteEdge _ (fun hh => ?_)
    have := hw.tail.eq_snd_of_mem_edges (Sym2.eq_swap ▸ hh)
    simp only [Walk.getVert_tail, Nat.reduceAdd] at this
.mp this.symm simpa using hw.getVert_eq_start_iff_of_not_nil (Walk.not_nil_of_ne hne)
· refine Walk.reachable Walk.cons (deleteEdges_adj.mpr ⟨this, ?_⟩) Walk.nil
    contrapose h'
    refine (Set.subsingleton_iff_singleton h').mp ?_
    exact Set.encard_le_one_iff_subsingleton.mp (Order.le_of_lt_succ hs)

/-!
### 2-reachability

In this section, we prove results about 2-connected components of a graph, but without naming them.
-/

namespace Walk
variable {w : G.Walk u v}

/--
lemma `IsTrail.isEdgeReachable_two_of_isEdgeReachable_two_aux` / 引理 `IsTrail.isEdgeReachable_two_of_isEdgeReachable_two_aux`

English:
lemma IsTrail.isEdgeReachable_two_of_isEdgeReachable_two_aux
  statement: (hw : w.IsTrail)
  proof: by
  classical
  contrapose huy
  obtain ⟨e, he⟩ := by simpa [isEdgeReachable_two] using huy
  have he' : ¬ (G.deleteEdges {e}).Reachable v x := fun hvy =>
he (isEdgeReachable_two.1 huv _).trans hvy
  exact fun hy => hw.disjoint_edges_takeUntil_dropUntil hy
    ((w.takeUntil x _).mem_edges_of_not_reachable_deleteEdges he)
    (by simpa using (w.dropUntil x _).reverse.mem_edges_of_not_reachable_deleteEdges he')

中文:
引理 是Trail.isEdgeReachable_two_of_isEdgeReachable_two_aux
  结论: (hw : w.是Trail)
  证明: by
  classical
  contrapose huy
  obtain ⟨e, he⟩ := by simpa [isEdgeReachable_two] using huy
  have he' : ¬ (G.deleteEdges {e}).Reachable v x := fun hvy =>
he (isEdgeReachable_two.1 huv _).trans hvy
  exact fun hy => hw.disjoint_edges_takeUntil_dropUntil hy
    ((w.takeUntil x _).mem_edges_of_not_reachable_deleteEdges he)
    (by simpa using (w.dropUntil x _).reverse.mem_edges_of_not_reachable_deleteEdges he')
-/
private lemma IsTrail.isEdgeReachable_two_of_isEdgeReachable_two_aux (hw : w.IsTrail)
    (huv : G.IsEdgeReachable 2 u v) (huy : x in w.support) : G.IsEdgeReachable 2 u x := by
  classical
  contrapose huy
  obtain ⟨e, he⟩ := by simpa [isEdgeReachable_two] using huy
  have he' : ¬ (G.deleteEdges {e}).Reachable v x := fun hvy =>
he (isEdgeReachable_two.1 huv _).trans hvy
  exact fun hy => hw.disjoint_edges_takeUntil_dropUntil hy
    ((w.takeUntil x _).mem_edges_of_not_reachable_deleteEdges he)
    (by simpa using (w.dropUntil x _).reverse.mem_edges_of_not_reachable_deleteEdges he')

/--
lemma `IsTrail.isEdgeReachable_two_of_isEdgeReachable_two` / 引理 `IsTrail.isEdgeReachable_two_of_isEdgeReachable_two`

English:
lemma IsTrail.isEdgeReachable_two_of_isEdgeReachable_two
  statement: (hw : w.IsTrail)
  proof: (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv hx).symm.trans
    (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv hy)

中文:
引理 是Trail.isEdgeReachable_two_of_isEdgeReachable_two
  结论: (hw : w.是Trail)
  证明: (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv hx).symm.trans
    (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv hy)

Depends on / 依赖: hw.isEdgeReachable_two_of_isEdgeReachable_two_aux, isEdgeReachable_two_of_isEdgeReachable_two_aux, symm.trans
-/
lemma IsTrail.isEdgeReachable_two_of_isEdgeReachable_two (hw : w.IsTrail)
    (huv : G.IsEdgeReachable 2 u v) (hx : x in w.support) (hy : y in w.support) :
    G.IsEdgeReachable 2 x y :=
  (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv hx).symm.trans
    (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv hy)

/-- A trail doesn't go through a vertex that is not 2-edge-reachable from its 2-edge-reachable
endpoints. -/
@[deprecated IsTrail.isEdgeReachable_two_of_isEdgeReachable_two (since := "2026-04-01")]
/--
lemma `IsTrail.not_mem_edges_of_not_isEdgeReachable_two` / 引理 `IsTrail.not_mem_edges_of_not_isEdgeReachable_two`

English:
lemma IsTrail.not_mem_edges_of_not_isEdgeReachable_two
  statement: (hw : w.IsTrail)
  proof: mt (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv) huy

中文:
引理 是Trail.not_mem_edges_of_not_isEdgeReachable_two
  结论: (hw : w.是Trail)
  证明: mt (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv) huy

Depends on / 依赖: hw.isEdgeReachable_two_of_isEdgeReachable_two_aux, isEdgeReachable_two_of_isEdgeReachable_two_aux
-/
lemma IsTrail.not_mem_edges_of_not_isEdgeReachable_two (hw : w.IsTrail)
    (huv : G.IsEdgeReachable 2 u v) (huy : ¬ G.IsEdgeReachable 2 u x) : x ∉ w.support :=
  mt (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv) huy

/--
lemma `IsTrail.isEdgeReachable_two` / 引理 `IsTrail.isEdgeReachable_two`

English:
lemma IsTrail.isEdgeReachable_two
  statement: {w : G.Walk u u} (hw : w.IsTrail) (hx : x in w.support)
  proof: hw.isEdgeReachable_two_of_isEdgeReachable_two .rfl hx hy

中文:
引理 是Trail.isEdgeReachable_two
  结论: {w : G.途径 u u} (hw : w.是Trail) (hx : x in w.support)
  证明: hw.isEdgeReachable_two_of_isEdgeReachable_two .rfl hx hy

Depends on / 依赖: hw.isEdgeReachable_two_of_isEdgeReachable_two, isEdgeReachable_two_of_isEdgeReachable_two
-/
lemma IsTrail.isEdgeReachable_two {w : G.Walk u u} (hw : w.IsTrail) (hx : x in w.support)
    (hy : y in w.support) : G.IsEdgeReachable 2 x y :=
  hw.isEdgeReachable_two_of_isEdgeReachable_two .rfl hx hy

end SimpleGraph.Walk
