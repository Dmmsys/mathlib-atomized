/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara, Rida Hamadani, Nelson Spence
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.ENat.Lattice

/-!
# Graph metric

This module defines the `SimpleGraph.edist` function, which takes pairs of vertices to the length of
the shortest walk between them, or `⊤` if they are disconnected. It also defines `SimpleGraph.dist`
which is the `ℕ`-valued version of `SimpleGraph.edist`, and `SimpleGraph.ball` which is the open
ball in the graph extended metric.

## Main definitions

- `SimpleGraph.edist` is the graph extended metric.
- `SimpleGraph.dist` is the graph metric.
- `SimpleGraph.ball` is the open ball of a given radius around a vertex.

## TODO

- Provide an additional computable version of `SimpleGraph.dist`
  for when `G` is connected.

- When directed graphs exist, a directed notion of distance,
  likely `ENat`-valued.

## Tags

graph metric, distance, ball

-/

@[expose] public section

assert_not_exists Field

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ## Metric -/

section edist

/--
Definition of `edist` / `edist` 的定义

English:
definition edist
  signature: (u v : V)
  body: ⨅ w : G.Walk u v, w.length

中文:
定义 edist
  签名: (u v : V)
  定义体: ⨅ w : G.Walk u v, w.length

Depends on / 依赖: G.Walk, length, w.length
-/
noncomputable def edist (u v : V) : Nat∞ :=
  ⨅ w : G.Walk u v, w.length

variable {G} {u v w : V}

/--
theorem `edist_eq_sInf` / 定理 `edist_eq_sInf`

English:
theorem edist_eq_sInf
  statement: G.edist u v = sInf (Set.range fun w : G.Walk u v => (w.length : Nat∞))
  proof: rfl

中文:
定理 edist_eq_sInf
  结论: G.edist u v = sInf (集合.range fun w : G.途径 u v => (w.length : 自然数∞))
  证明: rfl
-/
theorem edist_eq_sInf : G.edist u v = sInf (Set.range fun w : G.Walk u v => (w.length : Nat∞)) := rfl

/--
theorem `Reachable.exists_walk_length_eq_edist` / 定理 `Reachable.exists_walk_length_eq_edist`

English:
theorem Reachable.exists_walk_length_eq_edist
  given: (hr : G.Reachable u v)
  proof: csInf_mem Set.range_nonempty_iff_nonempty.mpr hr

中文:
定理 Reachable.存在_walk_length_eq_edist
  条件: (hr : G.Reachable u v)
  证明: csInf_mem Set.range_nonempty_iff_nonempty.mpr hr
-/
protected theorem Reachable.exists_walk_length_eq_edist (hr : G.Reachable u v) :
    exists p : G.Walk u v, p.length = G.edist u v :=
csInf_mem Set.range_nonempty_iff_nonempty.mpr hr

/--
theorem `Connected.exists_walk_length_eq_edist` / 定理 `Connected.exists_walk_length_eq_edist`

English:
theorem Connected.exists_walk_length_eq_edist
  given: (hconn : G.Connected) (u v : V)
  proof: (hconn u v).exists_walk_length_eq_edist

中文:
定理 连通.存在_walk_length_eq_edist
  条件: (hconn : G.连通) (u v : V)
  证明: (hconn u v).exists_walk_length_eq_edist
-/
protected theorem Connected.exists_walk_length_eq_edist (hconn : G.Connected) (u v : V) :
    exists p : G.Walk u v, p.length = G.edist u v :=
  (hconn u v).exists_walk_length_eq_edist

/--
theorem `edist_le` / 定理 `edist_le`

English:
theorem edist_le
  given: (p : G.Walk u v)
  proof: sInf_le ⟨p, rfl⟩
protected alias Walk.edist_le := edist_le

@[simp]

中文:
定理 edist_le
  条件: (p : G.途径 u v)
  证明: sInf_le ⟨p, rfl⟩
protected alias Walk.edist_le := edist_le

@[simp]

Depends on / 依赖: Walk.edist_le, edist_le, protected, sInf_le
-/
theorem edist_le (p : G.Walk u v) :
    G.edist u v <= p.length :=
  sInf_le ⟨p, rfl⟩
protected alias Walk.edist_le := edist_le

@[simp]
/--
theorem `edist_eq_zero_iff` / 定理 `edist_eq_zero_iff`

English:
theorem edist_eq_zero_iff
  statement: G.edist u v = 0 ↔ u = v
  proof: by
  simp [edist]

@[simp]

中文:
定理 edist_eq_zero_iff
  结论: G.edist u v = 0 ↔ u = v
  证明: by
  simp [edist]

@[simp]
-/
theorem edist_eq_zero_iff : G.edist u v = 0 ↔ u = v := by
  simp [edist]

@[simp]
/--
theorem `edist_self` / 定理 `edist_self`

English:
theorem edist_self
  statement: edist G v v = 0
  proof: edist_eq_zero_iff.mpr rfl

中文:
定理 edist_self
  结论: edist G v v = 0
  证明: edist_eq_zero_iff.mpr rfl

Depends on / 依赖: edist_eq_zero_iff, edist_eq_zero_iff.mpr
-/
theorem edist_self : edist G v v = 0 :=
  edist_eq_zero_iff.mpr rfl

/--
theorem `edist_pos_of_ne` / 定理 `edist_pos_of_ne`

English:
theorem edist_pos_of_ne
  given: (hne : u != v)
  proof: pos_iff_ne_zero.mpr edist_eq_zero_iff.ne.mpr hne

中文:
定理 edist_pos_of_ne
  条件: (hne : u != v)
  证明: pos_iff_ne_zero.mpr edist_eq_zero_iff.ne.mpr hne

Depends on / 依赖: edist_eq_zero_iff, edist_eq_zero_iff.ne.mpr, pos_iff_ne_zero, pos_iff_ne_zero.mpr
-/
theorem edist_pos_of_ne (hne : u != v) :
    0 < G.edist u v :=
pos_iff_ne_zero.mpr edist_eq_zero_iff.ne.mpr hne

/--
lemma `edist_eq_top_of_not_reachable` / 引理 `edist_eq_top_of_not_reachable`

English:
lemma edist_eq_top_of_not_reachable
  given: (h : ¬G.Reachable u v)
  proof: by
  simp [edist, not_reachable_iff_isEmpty_walk.mp h]

中文:
引理 edist_eq_top_of_not_reachable
  条件: (h : ¬G.Reachable u v)
  证明: by
  simp [edist, not_reachable_iff_isEmpty_walk.mp h]

Depends on / 依赖: not_reachable_iff_isEmpty_walk, not_reachable_iff_isEmpty_walk.mp
-/
lemma edist_eq_top_of_not_reachable (h : ¬G.Reachable u v) :
    G.edist u v = ⊤ := by
  simp [edist, not_reachable_iff_isEmpty_walk.mp h]

/--
theorem `reachable_of_edist_ne_top` / 定理 `reachable_of_edist_ne_top`

English:
theorem reachable_of_edist_ne_top
  given: (h : G.edist u v != ⊤)
  proof: not_not.mp edist_eq_top_of_not_reachable.mt h

中文:
定理 reachable_of_edist_ne_top
  条件: (h : G.edist u v != ⊤)
  证明: not_not.mp edist_eq_top_of_not_reachable.mt h

Depends on / 依赖: edist_eq_top_of_not_reachable, edist_eq_top_of_not_reachable.mt, not_not, not_not.mp
-/
theorem reachable_of_edist_ne_top (h : G.edist u v != ⊤) :
    G.Reachable u v :=
not_not.mp edist_eq_top_of_not_reachable.mt h

/--
lemma `exists_walk_of_edist_ne_top` / 引理 `exists_walk_of_edist_ne_top`

English:
lemma exists_walk_of_edist_ne_top
  given: (h : G.edist u v != ⊤)
  proof: (reachable_of_edist_ne_top h).exists_walk_length_eq_edist

中文:
引理 存在_walk_of_edist_ne_top
  条件: (h : G.edist u v != ⊤)
  证明: (reachable_of_edist_ne_top h).exists_walk_length_eq_edist

Depends on / 依赖: exists_walk_length_eq_edist, reachable_of_edist_ne_top
-/
lemma exists_walk_of_edist_ne_top (h : G.edist u v != ⊤) :
    exists p : G.Walk u v, p.length = G.edist u v :=
  (reachable_of_edist_ne_top h).exists_walk_length_eq_edist

/--
theorem `edist_triangle` / 定理 `edist_triangle`

English:
theorem edist_triangle
  statement: G.edist u w <= G.edist u v + G.edist v w
  proof: by
  cases eq_or_ne (G.edist u v) ⊤ with
  | inl huv => simp [huv]
  | inr huv =>
    cases eq_or_ne (G.edist v w) ⊤ with
    | inl hvw => simp [hvw]
    | inr hvw =>
      obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top huv
      obtain ⟨q, hq⟩ := exists_walk_of_edist_ne_top hvw
      rw [← hp]; rw [← hq]; rw [← Nat.cast_add]; rw [← Walk.length_append]
      exact edist_le _

中文:
定理 edist_triangle
  结论: G.edist u w <= G.edist u v + G.edist v w
  证明: by
  cases eq_or_ne (G.edist u v) ⊤ with
  | inl huv => simp [huv]
  | inr huv =>
    cases eq_or_ne (G.edist v w) ⊤ with
    | inl hvw => simp [hvw]
    | inr hvw =>
      obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top huv
      obtain ⟨q, hq⟩ := exists_walk_of_edist_ne_top hvw
      rw [← hp]; rw [← hq]; rw [← Nat.cast_add]; rw [← Walk.length_append]
      exact edist_le _
-/
protected theorem edist_triangle : G.edist u w <= G.edist u v + G.edist v w := by
  cases eq_or_ne (G.edist u v) ⊤ with
  | inl huv => simp [huv]
  | inr huv =>
    cases eq_or_ne (G.edist v w) ⊤ with
    | inl hvw => simp [hvw]
    | inr hvw =>
      obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top huv
      obtain ⟨q, hq⟩ := exists_walk_of_edist_ne_top hvw
      rw [← hp]; rw [← hq]; rw [← Nat.cast_add]; rw [← Walk.length_append]
      exact edist_le _

/--
theorem `edist_comm` / 定理 `edist_comm`

English:
theorem edist_comm
  statement: G.edist u v = G.edist v u
  proof: by
  rw [edist_eq_sInf]; rw [← Set.image_univ]; rw [← Set.image_univ_of_surjective Walk.reverse_surjective]; rw [← Set.image_comp]; rw [Set.image_univ]; rw [Function.comp_def]
  simp_rw [Walk.length_reverse, ← edist_eq_sInf]

中文:
定理 edist_comm
  结论: G.edist u v = G.edist v u
  证明: by
  rw [edist_eq_sInf]; rw [← Set.image_univ]; rw [← Set.image_univ_of_surjective Walk.reverse_surjective]; rw [← Set.image_comp]; rw [Set.image_univ]; rw [Function.comp_def]
  simp_rw [Walk.length_reverse, ← edist_eq_sInf]

Depends on / 依赖: Function, Function.comp_def, Set.image_comp, Set.image_univ, Set.image_univ_of_surjective, Walk.length_reverse, Walk.reverse_surjective, comp_def, edist_eq_sInf, image_comp, image_univ, image_univ_of_surjective, length_reverse, reverse_surjective, simp_rw
-/
theorem edist_comm : G.edist u v = G.edist v u := by
  rw [edist_eq_sInf]; rw [← Set.image_univ]; rw [← Set.image_univ_of_surjective Walk.reverse_surjective]; rw [← Set.image_comp]; rw [Set.image_univ]; rw [Function.comp_def]
  simp_rw [Walk.length_reverse, ← edist_eq_sInf]

/--
lemma `exists_walk_of_edist_eq_coe` / 引理 `exists_walk_of_edist_eq_coe`

English:
lemma exists_walk_of_edist_eq_coe
  given: {k : Nat} (h : G.edist u v = k)
  proof: have : G.edist u v != ⊤ := by rw [h]; exact ENat.natCast_ne_top _
  have ⟨p, hp⟩ := exists_walk_of_edist_ne_top this
  ⟨p, Nat.cast_injective (hp.trans h)⟩

中文:
引理 存在_walk_of_edist_eq_coe
  条件: {k : 自然数} (h : G.edist u v = k)
  证明: have : G.edist u v != ⊤ := by rw [h]; exact ENat.natCast_ne_top _
  have ⟨p, hp⟩ := exists_walk_of_edist_ne_top this
  ⟨p, Nat.cast_injective (hp.trans h)⟩

Depends on / 依赖: ENat.natCast_ne_top, G.edist, Nat.cast_injective, cast_injective, exists_walk_of_edist_ne_top, hp.trans, natCast_ne_top
-/
lemma exists_walk_of_edist_eq_coe {k : Nat} (h : G.edist u v = k) :
    exists p : G.Walk u v, p.length = k :=
  have : G.edist u v != ⊤ := by rw [h]; exact ENat.natCast_ne_top _
  have ⟨p, hp⟩ := exists_walk_of_edist_ne_top this
  ⟨p, Nat.cast_injective (hp.trans h)⟩

/--
lemma `edist_ne_top_iff_reachable` / 引理 `edist_ne_top_iff_reachable`

English:
lemma edist_ne_top_iff_reachable
  statement: G.edist u v != ⊤ ↔ G.Reachable u v
  proof: by
  refine ⟨reachable_of_edist_ne_top, fun h => ?_⟩
  by_contra hx
  simp only [edist, iInf_eq_top, ENat.natCast_ne_top] at hx
  exact h.elim hx

中文:
引理 edist_ne_top_iff_reachable
  结论: G.edist u v != ⊤ ↔ G.Reachable u v
  证明: by
  refine ⟨reachable_of_edist_ne_top, fun h => ?_⟩
  by_contra hx
  simp only [edist, iInf_eq_top, ENat.natCast_ne_top] at hx
  exact h.elim hx

Depends on / 依赖: ENat.natCast_ne_top, h.elim, iInf_eq_top, natCast_ne_top, reachable_of_edist_ne_top
-/
lemma edist_ne_top_iff_reachable : G.edist u v != ⊤ ↔ G.Reachable u v := by
  refine ⟨reachable_of_edist_ne_top, fun h => ?_⟩
  by_contra hx
  simp only [edist, iInf_eq_top, ENat.natCast_ne_top] at hx
  exact h.elim hx

/--
The extended distance between vertices is equal to `1` if and only if these vertices are adjacent.
-/
@[simp]
/--
theorem `edist_eq_one_iff_adj` / 定理 `edist_eq_one_iff_adj`

English:
theorem edist_eq_one_iff_adj
  statement: G.edist u v = 1 ↔ G.Adj u v
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
· obtain ⟨w, hw⟩ := exists_walk_of_edist_ne_top by rw [h]; simp
exact w.adj_of_length_eq_one Nat.cast_eq_one.mp h ▸ hw
  · exact le_antisymm (edist_le h.toWalk) (Order.one_le_iff_pos.mpr <| edist_pos_of_ne h.ne)

中文:
定理 edist_eq_one_iff_adj
  结论: G.edist u v = 1 ↔ G.伴随 u v
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
· obtain ⟨w, hw⟩ := exists_walk_of_edist_ne_top by rw [h]; simp
exact w.adj_of_length_eq_one Nat.cast_eq_one.mp h ▸ hw
  · exact le_antisymm (edist_le h.toWalk) (Order.one_le_iff_pos.mpr <| edist_pos_of_ne h.ne)

Depends on / 依赖: Nat.cast_eq_one.mp, Order.one_le_iff_pos.mpr, adj_of_length_eq_one, cast_eq_one, edist_le, edist_pos_of_ne, exists_walk_of_edist_ne_top, h.ne, h.toWalk, le_antisymm, one_le_iff_pos, toWalk, w.adj_of_length_eq_one
-/
theorem edist_eq_one_iff_adj : G.edist u v = 1 ↔ G.Adj u v := by
  refine ⟨fun h => ?_, fun h => ?_⟩
· obtain ⟨w, hw⟩ := exists_walk_of_edist_ne_top by rw [h]; simp
exact w.adj_of_length_eq_one Nat.cast_eq_one.mp h ▸ hw
  · exact le_antisymm (edist_le h.toWalk) (Order.one_le_iff_pos.mpr <| edist_pos_of_ne h.ne)

/--
lemma `edist_le_one_iff_adj_or_eq` / 引理 `edist_le_one_iff_adj_or_eq`

English:
lemma edist_le_one_iff_adj_or_eq
  statement: G.edist u v <= 1 ↔ G.Adj u v ∨ u = v
  proof: by
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, or_false]
    have h : 0 < G.edist u v := edist_pos_of_ne huv
    rw [(Order.one_le_iff_pos.mpr h).ge_iff_eq']
    exact edist_eq_one_iff_adj

中文:
引理 edist_le_one_iff_adj_or_eq
  结论: G.edist u v <= 1 ↔ G.伴随 u v ∨ u = v
  证明: by
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, or_false]
    have h : 0 < G.edist u v := edist_pos_of_ne huv
    rw [(Order.one_le_iff_pos.mpr h).ge_iff_eq']
    exact edist_eq_one_iff_adj

Depends on / 依赖: G.edist, Order.one_le_iff_pos.mpr, edist_eq_one_iff_adj, edist_pos_of_ne, ge_iff_eq, one_le_iff_pos, or_false
-/
lemma edist_le_one_iff_adj_or_eq : G.edist u v <= 1 ↔ G.Adj u v ∨ u = v := by
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, or_false]
    have h : 0 < G.edist u v := edist_pos_of_ne huv
    rw [(Order.one_le_iff_pos.mpr h).ge_iff_eq']
    exact edist_eq_one_iff_adj

/--
lemma `edist_eq_two_iff` / 引理 `edist_eq_two_iff`

English:
lemma edist_eq_two_iff
  given: {u v : V}
  proof: by
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun h => le_antisymm ?_ ?_⟩
  · simp +decide [← G.edist_eq_zero_iff.not (b := u = v), h]
  · simp +decide [← edist_eq_one_iff_adj, h]
  · obtain ⟨w, hw⟩ := exists_walk_of_edist_eq_coe h
    use w.getVert 1
    suffices w.getVert 1 in G.commonNeighbors (w.getVert 0) (w.getVert w.length) by simpa
    refine hw ▸ G.mem_commonNeighbors.mp ?_
    exact ⟨w.adj_getVert_succ (by simp [hw]), (w.adj_getVert_succ (by simp [hw])).symm⟩
  · obtain ⟨w, hw⟩ := h.2.2
    rw [mem_commonNeighbors] at hw
    have := (Walk.cons hw.1 <| .cons hw.2.symm .nil).edist_le
    simp_all
  · by_contra
    simp_all [Order.le_one_iff]

中文:
引理 edist_eq_two_iff
  条件: {u v : V}
  证明: by
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun h => le_antisymm ?_ ?_⟩
  · simp +decide [← G.edist_eq_zero_iff.not (b := u = v), h]
  · simp +decide [← edist_eq_one_iff_adj, h]
  · obtain ⟨w, hw⟩ := exists_walk_of_edist_eq_coe h
    use w.getVert 1
    suffices w.getVert 1 in G.commonNeighbors (w.getVert 0) (w.getVert w.length) by simpa
    refine hw ▸ G.mem_commonNeighbors.mp ?_
    exact ⟨w.adj_getVert_succ (by simp [hw]), (w.adj_getVert_succ (by simp [hw])).symm⟩
  · obtain ⟨w, hw⟩ := h.2.2
    rw [mem_commonNeighbors] at hw
    have := (Walk.cons hw.1 <| .cons hw.2.symm .nil).edist_le
    simp_all
  · by_contra
    simp_all [Order.le_one_iff]

Depends on / 依赖: G.commonNeighbors, G.edist_eq_zero_iff.not, G.mem_commonNeighbors.mp, adj_getVert_succ, commonNeighbors, edist_eq_one_iff_adj, edist_eq_zero_iff, exists_walk_of_edist_eq_coe, getVert, le_antisymm, length, mem_commonNeighbors, w.adj_getVert_succ, w.getVert, w.length
-/
lemma edist_eq_two_iff {u v : V} :
    G.edist u v = 2 ↔ u != v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v).Nonempty := by
  refine ⟨fun h => ⟨?_, ?_, ?_⟩, fun h => le_antisymm ?_ ?_⟩
  · simp +decide [← G.edist_eq_zero_iff.not (b := u = v), h]
  · simp +decide [← edist_eq_one_iff_adj, h]
  · obtain ⟨w, hw⟩ := exists_walk_of_edist_eq_coe h
    use w.getVert 1
    suffices w.getVert 1 in G.commonNeighbors (w.getVert 0) (w.getVert w.length) by simpa
    refine hw ▸ G.mem_commonNeighbors.mp ?_
    exact ⟨w.adj_getVert_succ (by simp [hw]), (w.adj_getVert_succ (by simp [hw])).symm⟩
  · obtain ⟨w, hw⟩ := h.2.2
    rw [mem_commonNeighbors] at hw
    have := (Walk.cons hw.1 <| .cons hw.2.symm .nil).edist_le
    simp_all
  · by_contra
    simp_all [Order.le_one_iff]

/--
lemma `two_lt_edist_iff` / 引理 `two_lt_edist_iff`

English:
lemma two_lt_edist_iff
  given: {u v : V}
  proof: by
  refine ⟨fun h => ?_, fun h => lt_of_le_of_ne ?_ (Ne.symm ?_)⟩
  · have hn : u != v := fun hc => by simp [hc] at h
    have : ¬ G.Adj u v := fun hc => by simp +decide [edist_eq_one_iff_adj.mpr hc] at h
    use hn, this
    by_contra! hc
    simp [edist_eq_two_iff.mpr ⟨hn, this, hc⟩] at h
  · rw [← one_add_one_eq_two]
refine Order.add_one_le_of_lt lt_of_le_of_ne ?_ ?_
    <;> grind [Order.one_le_iff_pos, pos_iff_ne_zero, edist_eq_zero_iff, edist_eq_one_iff_adj]
  · simp_all [edist_eq_two_iff]

中文:
引理 two_lt_edist_iff
  条件: {u v : V}
  证明: by
  refine ⟨fun h => ?_, fun h => lt_of_le_of_ne ?_ (Ne.symm ?_)⟩
  · have hn : u != v := fun hc => by simp [hc] at h
    have : ¬ G.Adj u v := fun hc => by simp +decide [edist_eq_one_iff_adj.mpr hc] at h
    use hn, this
    by_contra! hc
    simp [edist_eq_two_iff.mpr ⟨hn, this, hc⟩] at h
  · rw [← one_add_one_eq_two]
refine Order.add_one_le_of_lt lt_of_le_of_ne ?_ ?_
    <;> grind [Order.one_le_iff_pos, pos_iff_ne_zero, edist_eq_zero_iff, edist_eq_one_iff_adj]
  · simp_all [edist_eq_two_iff]

Depends on / 依赖: G.Adj, Ne.symm, Order.add_one_le_of_lt, Order.one_le_iff_pos, add_one_le_of_lt, edist_eq_one_iff_adj, edist_eq_one_iff_adj.mpr, edist_eq_two_iff, edist_eq_two_iff.mpr, edist_eq_zero_iff, lt_of_le_of_ne, one_add_one_eq_two, one_le_iff_pos, pos_iff_ne_zero
-/
lemma two_lt_edist_iff {u v : V} :
    2 < G.edist u v ↔ u != v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v) = ∅ := by
  refine ⟨fun h => ?_, fun h => lt_of_le_of_ne ?_ (Ne.symm ?_)⟩
  · have hn : u != v := fun hc => by simp [hc] at h
    have : ¬ G.Adj u v := fun hc => by simp +decide [edist_eq_one_iff_adj.mpr hc] at h
    use hn, this
    by_contra! hc
    simp [edist_eq_two_iff.mpr ⟨hn, this, hc⟩] at h
  · rw [← one_add_one_eq_two]
refine Order.add_one_le_of_lt lt_of_le_of_ne ?_ ?_
    <;> grind [Order.one_le_iff_pos, pos_iff_ne_zero, edist_eq_zero_iff, edist_eq_one_iff_adj]
  · simp_all [edist_eq_two_iff]

/--
lemma `edist_bot_of_ne` / 引理 `edist_bot_of_ne`

English:
lemma edist_bot_of_ne
  given: (h : u != v)
  statement: (⊥ : SimpleGraph V).edist u v = ⊤
  proof: by
  rwa [ne_eq, ← reachable_bot.not, ← edist_ne_top_iff_reachable.not, not_not] at h

中文:
引理 edist_bot_of_ne
  条件: (h : u != v)
  结论: (⊥ : 简单图 V).edist u v = ⊤
  证明: by
  rwa [ne_eq, ← reachable_bot.not, ← edist_ne_top_iff_reachable.not, not_not] at h

Depends on / 依赖: edist_ne_top_iff_reachable, edist_ne_top_iff_reachable.not, ne_eq, not_not, reachable_bot, reachable_bot.not
-/
lemma edist_bot_of_ne (h : u != v) : (⊥ : SimpleGraph V).edist u v = ⊤ := by
  rwa [ne_eq, ← reachable_bot.not, ← edist_ne_top_iff_reachable.not, not_not] at h

/--
lemma `edist_bot` / 引理 `edist_bot`

English:
lemma edist_bot
  given: [DecidableEq V]
  statement: (⊥ : SimpleGraph V).edist u v = (if u = v then 0 else ⊤)
  proof: by
  by_cases h : u = v <;> simp [h, edist_bot_of_ne]

中文:
引理 edist_bot
  条件: [DecidableEq V]
  结论: (⊥ : 简单图 V).edist u v = (if u = v then 0 else ⊤)
  证明: by
  by_cases h : u = v <;> simp [h, edist_bot_of_ne]

Depends on / 依赖: edist_bot_of_ne
-/
lemma edist_bot [DecidableEq V] : (⊥ : SimpleGraph V).edist u v = (if u = v then 0 else ⊤) := by
  by_cases h : u = v <;> simp [h, edist_bot_of_ne]

/--
lemma `edist_top_of_ne` / 引理 `edist_top_of_ne`

English:
lemma edist_top_of_ne
  given: (h : u != v)
  statement: (⊤ : SimpleGraph V).edist u v = 1
  proof: by
  simp [h]

中文:
引理 edist_top_of_ne
  条件: (h : u != v)
  结论: (⊤ : 简单图 V).edist u v = 1
  证明: by
  simp [h]
-/
lemma edist_top_of_ne (h : u != v) : (⊤ : SimpleGraph V).edist u v = 1 := by
  simp [h]

/--
lemma `edist_top` / 引理 `edist_top`

English:
lemma edist_top
  given: [DecidableEq V]
  statement: (⊤ : SimpleGraph V).edist u v = (if u = v then 0 else 1)
  proof: by
  by_cases h : u = v <;> simp [h]

中文:
引理 edist_top
  条件: [DecidableEq V]
  结论: (⊤ : 简单图 V).edist u v = (if u = v then 0 else 1)
  证明: by
  by_cases h : u = v <;> simp [h]
-/
lemma edist_top [DecidableEq V] : (⊤ : SimpleGraph V).edist u v = (if u = v then 0 else 1) := by
  by_cases h : u = v <;> simp [h]

/-- Supergraphs have smaller or equal extended distances to their subgraphs. -/
@[gcongr]
/--
theorem `edist_anti` / 定理 `edist_anti`

English:
theorem edist_anti
  given: {G' : SimpleGraph V} (h : G <= G')
  proof: by
  by_cases hr : G.Reachable u v
  · obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_edist
    rw [← hw]; rw [← Walk.length_map (.ofLE h)]
    apply edist_le
  · exact edist_eq_top_of_not_reachable hr ▸ le_top

中文:
定理 edist_anti
  条件: {G' : 简单图 V} (h : G <= G')
  证明: by
  by_cases hr : G.Reachable u v
  · obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_edist
    rw [← hw]; rw [← Walk.length_map (.ofLE h)]
    apply edist_le
  · exact edist_eq_top_of_not_reachable hr ▸ le_top

Depends on / 依赖: G.Reachable, Reachable, Walk.length_map, edist_eq_top_of_not_reachable, edist_le, exists_walk_length_eq_edist, hr.exists_walk_length_eq_edist, le_top, length_map
-/
theorem edist_anti {G' : SimpleGraph V} (h : G <= G') :
    G'.edist u v <= G.edist u v := by
  by_cases hr : G.Reachable u v
  · obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_edist
    rw [← hw]; rw [← Walk.length_map (.ofLE h)]
    apply edist_le
  · exact edist_eq_top_of_not_reachable hr ▸ le_top

end edist

section dist

/--
Definition of `dist` / `dist` 的定义

English:
definition dist
  signature: (u v : V)
  body: (G.edist u v).toNat

中文:
定义 dist
  签名: (u v : V)
  定义体: (G.edist u v).toNat

Depends on / 依赖: G.edist
-/
noncomputable def dist (u v : V) : Nat :=
  (G.edist u v).toNat

variable {G} {u v w : V}

/--
theorem `dist_eq_sInf` / 定理 `dist_eq_sInf`

English:
theorem dist_eq_sInf
  statement: G.dist u v = sInf (Set.range (Walk.length : G.Walk u v -> Nat))
  proof: ENat.iInf_toNat

@[grind =]

中文:
定理 dist_eq_sInf
  结论: G.dist u v = sInf (集合.range (途径.length : G.途径 u v -> 自然数))
  证明: ENat.iInf_toNat

@[grind =]

Depends on / 依赖: ENat.iInf_toNat, iInf_toNat
-/
theorem dist_eq_sInf : G.dist u v = sInf (Set.range (Walk.length : G.Walk u v -> Nat)) :=
  ENat.iInf_toNat

@[grind =]
/--
lemma `Reachable.coe_dist_eq_edist` / 引理 `Reachable.coe_dist_eq_edist`

English:
lemma Reachable.coe_dist_eq_edist
  given: (h : G.Reachable u v)
  statement: G.dist u v = G.edist u v
  proof: ENat.natCast_toNat edist_ne_top_iff_reachable.mpr h

中文:
引理 Reachable.coe_dist_eq_edist
  条件: (h : G.Reachable u v)
  结论: G.dist u v = G.edist u v
  证明: ENat.natCast_toNat edist_ne_top_iff_reachable.mpr h

Depends on / 依赖: ENat.natCast_toNat, edist_ne_top_iff_reachable, edist_ne_top_iff_reachable.mpr, natCast_toNat
-/
lemma Reachable.coe_dist_eq_edist (h : G.Reachable u v) : G.dist u v = G.edist u v :=
ENat.natCast_toNat edist_ne_top_iff_reachable.mpr h

/--
theorem `Reachable.exists_walk_length_eq_dist` / 定理 `Reachable.exists_walk_length_eq_dist`

English:
theorem Reachable.exists_walk_length_eq_dist
  given: (hr : G.Reachable u v)
  proof: dist_eq_sInf ▸ Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr hr)

中文:
定理 Reachable.存在_walk_length_eq_dist
  条件: (hr : G.Reachable u v)
  证明: dist_eq_sInf ▸ Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr hr)
-/
protected theorem Reachable.exists_walk_length_eq_dist (hr : G.Reachable u v) :
    exists p : G.Walk u v, p.length = G.dist u v :=
  dist_eq_sInf ▸ Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr hr)

/--
theorem `Connected.exists_walk_length_eq_dist` / 定理 `Connected.exists_walk_length_eq_dist`

English:
theorem Connected.exists_walk_length_eq_dist
  given: (hconn : G.Connected) (u v : V)
  proof: dist_eq_sInf ▸ (hconn u v).exists_walk_length_eq_dist

中文:
定理 连通.存在_walk_length_eq_dist
  条件: (hconn : G.连通) (u v : V)
  证明: dist_eq_sInf ▸ (hconn u v).exists_walk_length_eq_dist
-/
protected theorem Connected.exists_walk_length_eq_dist (hconn : G.Connected) (u v : V) :
    exists p : G.Walk u v, p.length = G.dist u v :=
  dist_eq_sInf ▸ (hconn u v).exists_walk_length_eq_dist

/--
theorem `dist_le` / 定理 `dist_le`

English:
theorem dist_le
  given: (p : G.Walk u v)
  statement: G.dist u v <= p.length
  proof: dist_eq_sInf ▸ Nat.sInf_le ⟨p, rfl⟩

@[simp]

中文:
定理 dist_le
  条件: (p : G.途径 u v)
  结论: G.dist u v <= p.length
  证明: dist_eq_sInf ▸ Nat.sInf_le ⟨p, rfl⟩

@[simp]

Depends on / 依赖: Nat.sInf_le, dist_eq_sInf, sInf_le
-/
theorem dist_le (p : G.Walk u v) : G.dist u v <= p.length :=
  dist_eq_sInf ▸ Nat.sInf_le ⟨p, rfl⟩

@[simp]
/--
theorem `dist_eq_zero_iff_eq_or_not_reachable` / 定理 `dist_eq_zero_iff_eq_or_not_reachable`

English:
theorem dist_eq_zero_iff_eq_or_not_reachable
  proof: by simp [dist_eq_sInf, Nat.sInf_eq_zero, Reachable]

@[simp, grind =]

中文:
定理 dist_eq_zero_iff_eq_or_not_reachable
  证明: by simp [dist_eq_sInf, Nat.sInf_eq_zero, Reachable]

@[simp, grind =]

Depends on / 依赖: Nat.sInf_eq_zero, Reachable, dist_eq_sInf, sInf_eq_zero
-/
theorem dist_eq_zero_iff_eq_or_not_reachable :
    G.dist u v = 0 ↔ u = v ∨ ¬G.Reachable u v := by simp [dist_eq_sInf, Nat.sInf_eq_zero, Reachable]

@[simp, grind =]
/--
theorem `dist_self` / 定理 `dist_self`

English:
theorem dist_self
  statement: dist G v v = 0
  proof: by simp

中文:
定理 dist_self
  结论: dist G v v = 0
  证明: by simp
-/
theorem dist_self : dist G v v = 0 := by simp

/--
theorem `Reachable.dist_eq_zero_iff` / 定理 `Reachable.dist_eq_zero_iff`

English:
theorem Reachable.dist_eq_zero_iff
  given: (hr : G.Reachable u v)
  proof: by simp [hr]

中文:
定理 Reachable.dist_eq_zero_iff
  条件: (hr : G.Reachable u v)
  证明: by simp [hr]
-/
protected theorem Reachable.dist_eq_zero_iff (hr : G.Reachable u v) :
    G.dist u v = 0 ↔ u = v := by simp [hr]

/--
theorem `Reachable.pos_dist_of_ne` / 定理 `Reachable.pos_dist_of_ne`

English:
theorem Reachable.pos_dist_of_ne
  given: (h : G.Reachable u v) (hne : u != v)
  proof: Nat.pos_of_ne_zero (by simp [h, hne])

中文:
定理 Reachable.pos_dist_of_ne
  条件: (h : G.Reachable u v) (hne : u != v)
  证明: Nat.pos_of_ne_zero (by simp [h, hne])
-/
protected theorem Reachable.pos_dist_of_ne (h : G.Reachable u v) (hne : u != v) :
    0 < G.dist u v :=
  Nat.pos_of_ne_zero (by simp [h, hne])

/--
theorem `Reachable.one_lt_dist_of_ne_of_not_adj` / 定理 `Reachable.one_lt_dist_of_ne_of_not_adj`

English:
theorem Reachable.one_lt_dist_of_ne_of_not_adj
  statement: (h : G.Reachable u v) (hne : u != v)
  proof: Nat.lt_of_le_of_ne (h.pos_dist_of_ne hne) (by
    by_contra hc
    obtain ⟨p, hp⟩ := Reachable.exists_walk_length_eq_dist h
    exact hnadj (Walk.exists_length_eq_one_iff.mp ⟨p, hc ▸ hp⟩))

中文:
定理 Reachable.one_lt_dist_of_ne_of_not_adj
  结论: (h : G.Reachable u v) (hne : u != v)
  证明: Nat.lt_of_le_of_ne (h.pos_dist_of_ne hne) (by
    by_contra hc
    obtain ⟨p, hp⟩ := Reachable.exists_walk_length_eq_dist h
    exact hnadj (Walk.exists_length_eq_one_iff.mp ⟨p, hc ▸ hp⟩))
-/
protected theorem Reachable.one_lt_dist_of_ne_of_not_adj (h : G.Reachable u v) (hne : u != v)
    (hnadj : ¬G.Adj u v) : 1 < G.dist u v :=
  Nat.lt_of_le_of_ne (h.pos_dist_of_ne hne) (by
    by_contra hc
    obtain ⟨p, hp⟩ := Reachable.exists_walk_length_eq_dist h
    exact hnadj (Walk.exists_length_eq_one_iff.mp ⟨p, hc ▸ hp⟩))

/--
theorem `Connected.dist_eq_zero_iff` / 定理 `Connected.dist_eq_zero_iff`

English:
theorem Connected.dist_eq_zero_iff
  given: (hconn : G.Connected)
  proof: by simp [hconn u v]

中文:
定理 连通.dist_eq_zero_iff
  条件: (hconn : G.连通)
  证明: by simp [hconn u v]
-/
protected theorem Connected.dist_eq_zero_iff (hconn : G.Connected) :
    G.dist u v = 0 ↔ u = v := by simp [hconn u v]

/--
theorem `Connected.pos_dist_of_ne` / 定理 `Connected.pos_dist_of_ne`

English:
theorem Connected.pos_dist_of_ne
  given: (hconn : G.Connected) (hne : u != v)
  proof: Nat.pos_of_ne_zero fun h => False.elim hne (hconn.dist_eq_zero_iff).mp h

中文:
定理 连通.pos_dist_of_ne
  条件: (hconn : G.连通) (hne : u != v)
  证明: Nat.pos_of_ne_zero fun h => False.elim hne (hconn.dist_eq_zero_iff).mp h
-/
protected theorem Connected.pos_dist_of_ne (hconn : G.Connected) (hne : u != v) :
    0 < G.dist u v :=
Nat.pos_of_ne_zero fun h => False.elim hne (hconn.dist_eq_zero_iff).mp h

/--
theorem `Connected.one_lt_dist_of_ne_of_not_adj` / 定理 `Connected.one_lt_dist_of_ne_of_not_adj`

English:
theorem Connected.one_lt_dist_of_ne_of_not_adj
  statement: (h : G.Connected) (hne : u != v)
  proof: Reachable.one_lt_dist_of_ne_of_not_adj (h u v) hne hnadj

中文:
定理 连通.one_lt_dist_of_ne_of_not_adj
  结论: (h : G.连通) (hne : u != v)
  证明: Reachable.one_lt_dist_of_ne_of_not_adj (h u v) hne hnadj
-/
protected theorem Connected.one_lt_dist_of_ne_of_not_adj (h : G.Connected) (hne : u != v)
    (hnadj : ¬G.Adj u v) : 1 < G.dist u v :=
  Reachable.one_lt_dist_of_ne_of_not_adj (h u v) hne hnadj

/--
theorem `dist_eq_zero_of_not_reachable` / 定理 `dist_eq_zero_of_not_reachable`

English:
theorem dist_eq_zero_of_not_reachable
  given: (h : ¬G.Reachable u v)
  statement: G.dist u v = 0
  proof: by
  simp [h]

中文:
定理 dist_eq_zero_of_not_reachable
  条件: (h : ¬G.Reachable u v)
  结论: G.dist u v = 0
  证明: by
  simp [h]
-/
theorem dist_eq_zero_of_not_reachable (h : ¬G.Reachable u v) : G.dist u v = 0 := by
  simp [h]

/--
theorem `nonempty_of_pos_dist` / 定理 `nonempty_of_pos_dist`

English:
theorem nonempty_of_pos_dist
  given: (h : 0 < G.dist u v)
  proof: by
  rw [dist_eq_sInf] at h
  simpa [Set.range_nonempty_iff_nonempty, Set.nonempty_iff_univ_nonempty] using
    Nat.nonempty_of_pos_sInf h

中文:
定理 nonempty_of_pos_dist
  条件: (h : 0 < G.dist u v)
  证明: by
  rw [dist_eq_sInf] at h
  simpa [Set.range_nonempty_iff_nonempty, Set.nonempty_iff_univ_nonempty] using
    Nat.nonempty_of_pos_sInf h

Depends on / 依赖: Nat.nonempty_of_pos_sInf, Set.nonempty_iff_univ_nonempty, Set.range_nonempty_iff_nonempty, dist_eq_sInf, nonempty_iff_univ_nonempty, nonempty_of_pos_sInf, range_nonempty_iff_nonempty
-/
theorem nonempty_of_pos_dist (h : 0 < G.dist u v) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  rw [dist_eq_sInf] at h
  simpa [Set.range_nonempty_iff_nonempty, Set.nonempty_iff_univ_nonempty] using
    Nat.nonempty_of_pos_sInf h

/--
theorem `Connected.dist_triangle` / 定理 `Connected.dist_triangle`

English:
theorem Connected.dist_triangle
  given: (hconn : G.Connected)
  proof: by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist v w
  rw [← hp]; rw [← hq]; rw [← Walk.length_append]
  apply dist_le

中文:
定理 连通.dist_triangle
  条件: (hconn : G.连通)
  证明: by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist v w
  rw [← hp]; rw [← hq]; rw [← Walk.length_append]
  apply dist_le
-/
protected theorem Connected.dist_triangle (hconn : G.Connected) :
    G.dist u w <= G.dist u v + G.dist v w := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist v w
  rw [← hp]; rw [← hq]; rw [← Walk.length_append]
  apply dist_le

/--
lemma `Reachable.dist_triangle_left` / 引理 `Reachable.dist_triangle_left`

English:
lemma Reachable.dist_triangle_left
  given: (h : G.Reachable u v) (w)
  proof: by
  by_cases! h' : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable]
  rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_add]
  grind [SimpleGraph.edist_triangle, Reachable.trans, Reachable.symm]

中文:
引理 Reachable.dist_triangle_left
  条件: (h : G.Reachable u v) (w)
  证明: by
  by_cases! h' : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable]
  rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_add]
  grind [SimpleGraph.edist_triangle, Reachable.trans, Reachable.symm]

Depends on / 依赖: ENat.natCast_add, ENat.natCast_le_natCast, G.Reachable, Reachable, Reachable.symm, Reachable.trans, SimpleGraph, SimpleGraph.edist_triangle, dist_eq_zero_iff_eq_or_not_reachable, edist_triangle, natCast_add, natCast_le_natCast
-/
lemma Reachable.dist_triangle_left (h : G.Reachable u v) (w) :
    G.dist u w <= G.dist u v + G.dist v w := by
  by_cases! h' : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable]
  rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_add]
  grind [SimpleGraph.edist_triangle, Reachable.trans, Reachable.symm]

/--
lemma `Reachable.dist_triangle_right` / 引理 `Reachable.dist_triangle_right`

English:
lemma Reachable.dist_triangle_right
  given: (h : G.Reachable v w) (u)
  proof: by
  by_cases! h' : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable]
  rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_add]
  grind [SimpleGraph.edist_triangle, Reachable.trans, Reachable.symm]

中文:
引理 Reachable.dist_triangle_right
  条件: (h : G.Reachable v w) (u)
  证明: by
  by_cases! h' : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable]
  rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_add]
  grind [SimpleGraph.edist_triangle, Reachable.trans, Reachable.symm]

Depends on / 依赖: ENat.natCast_add, ENat.natCast_le_natCast, G.Reachable, Reachable, Reachable.symm, Reachable.trans, SimpleGraph, SimpleGraph.edist_triangle, dist_eq_zero_iff_eq_or_not_reachable, edist_triangle, natCast_add, natCast_le_natCast
-/
lemma Reachable.dist_triangle_right (h : G.Reachable v w) (u) :
    G.dist u w <= G.dist u v + G.dist v w := by
  by_cases! h' : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable]
  rw [← ENat.natCast_le_natCast]; rw [ENat.natCast_add]
  grind [SimpleGraph.edist_triangle, Reachable.trans, Reachable.symm]

/--
theorem `dist_comm` / 定理 `dist_comm`

English:
theorem dist_comm
  statement: G.dist u v = G.dist v u
  proof: by
  rw [dist]; rw [dist]; rw [edist_comm]

中文:
定理 dist_comm
  结论: G.dist u v = G.dist v u
  证明: by
  rw [dist]; rw [dist]; rw [edist_comm]

Depends on / 依赖: edist_comm
-/
theorem dist_comm : G.dist u v = G.dist v u := by
  rw [dist]; rw [dist]; rw [edist_comm]

/--
lemma `dist_ne_zero_iff_ne_and_reachable` / 引理 `dist_ne_zero_iff_ne_and_reachable`

English:
lemma dist_ne_zero_iff_ne_and_reachable
  statement: G.dist u v != 0 ↔ u != v ∧ G.Reachable u v
  proof: by
  simp

中文:
引理 dist_ne_zero_iff_ne_and_reachable
  结论: G.dist u v != 0 ↔ u != v ∧ G.Reachable u v
  证明: by
  simp
-/
lemma dist_ne_zero_iff_ne_and_reachable : G.dist u v != 0 ↔ u != v ∧ G.Reachable u v := by
  simp

/--
lemma `Reachable.of_dist_ne_zero` / 引理 `Reachable.of_dist_ne_zero`

English:
lemma Reachable.of_dist_ne_zero
  given: (h : G.dist u v != 0)
  statement: G.Reachable u v
  proof: (dist_ne_zero_iff_ne_and_reachable.mp h).2

中文:
引理 Reachable.of_dist_ne_zero
  条件: (h : G.dist u v != 0)
  结论: G.Reachable u v
  证明: (dist_ne_zero_iff_ne_and_reachable.mp h).2

Depends on / 依赖: dist_ne_zero_iff_ne_and_reachable, dist_ne_zero_iff_ne_and_reachable.mp
-/
lemma Reachable.of_dist_ne_zero (h : G.dist u v != 0) : G.Reachable u v :=
  (dist_ne_zero_iff_ne_and_reachable.mp h).2

/--
lemma `exists_walk_of_dist_ne_zero` / 引理 `exists_walk_of_dist_ne_zero`

English:
lemma exists_walk_of_dist_ne_zero
  given: (h : G.dist u v != 0)
  proof: (Reachable.of_dist_ne_zero h).exists_walk_length_eq_dist

中文:
引理 存在_walk_of_dist_ne_zero
  条件: (h : G.dist u v != 0)
  证明: (Reachable.of_dist_ne_zero h).exists_walk_length_eq_dist

Depends on / 依赖: Reachable, Reachable.of_dist_ne_zero, exists_walk_length_eq_dist, of_dist_ne_zero
-/
lemma exists_walk_of_dist_ne_zero (h : G.dist u v != 0) :
    exists p : G.Walk u v, p.length = G.dist u v :=
  (Reachable.of_dist_ne_zero h).exists_walk_length_eq_dist

/--
The distance between vertices is equal to `1` if and only if these vertices are adjacent.
-/
@[simp]
/--
theorem `dist_eq_one_iff_adj` / 定理 `dist_eq_one_iff_adj`

English:
theorem dist_eq_one_iff_adj
  statement: G.dist u v = 1 ↔ G.Adj u v
  proof: by
  rw [dist]; rw [ENat.toNat_eq_iff]; rw [ENat.natCast_one]; rw [edist_eq_one_iff_adj]
  decide

中文:
定理 dist_eq_one_iff_adj
  结论: G.dist u v = 1 ↔ G.伴随 u v
  证明: by
  rw [dist]; rw [ENat.toNat_eq_iff]; rw [ENat.natCast_one]; rw [edist_eq_one_iff_adj]
  decide

Depends on / 依赖: ENat.natCast_one, ENat.toNat_eq_iff, edist_eq_one_iff_adj, natCast_one, toNat_eq_iff
-/
theorem dist_eq_one_iff_adj : G.dist u v = 1 ↔ G.Adj u v := by
  rw [dist]; rw [ENat.toNat_eq_iff]; rw [ENat.natCast_one]; rw [edist_eq_one_iff_adj]
  decide

/--
theorem `Adj.diff_dist_adj` / 定理 `Adj.diff_dist_adj`

English:
theorem Adj.diff_dist_adj
  given: (hadj : G.Adj v w)
  proof: by
  by_cases! huw : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable, Reachable.trans, Adj.reachable]
  have : G.dist v w = 1 := dist_eq_one_iff_adj.mpr hadj
  have : G.dist w v = 1 := dist_eq_one_iff_adj.mpr hadj.symm
  have : G.dist u w <= G.dist u v + G.dist v w := hadj.reachable.dist_triangle_right u
  have : G.dist u v <= G.dist u w + G.dist w v := huw.dist_triangle_left v
  lia

中文:
定理 伴随.diff_dist_adj
  条件: (hadj : G.伴随 v w)
  证明: by
  by_cases! huw : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable, Reachable.trans, Adj.reachable]
  have : G.dist v w = 1 := dist_eq_one_iff_adj.mpr hadj
  have : G.dist w v = 1 := dist_eq_one_iff_adj.mpr hadj.symm
  have : G.dist u w <= G.dist u v + G.dist v w := hadj.reachable.dist_triangle_right u
  have : G.dist u v <= G.dist u w + G.dist w v := huw.dist_triangle_left v
  lia

Depends on / 依赖: Adj.reachable, G.Reachable, G.dist, Reachable, Reachable.trans, dist_eq_one_iff_adj, dist_eq_one_iff_adj.mpr, dist_eq_zero_iff_eq_or_not_reachable, dist_triangle_left, dist_triangle_right, hadj.reachable.dist_triangle_right, hadj.symm, huw.dist_triangle_left, reachable
-/
theorem Adj.diff_dist_adj (hadj : G.Adj v w) :
    G.dist u w = G.dist u v ∨ G.dist u w = G.dist u v + 1 ∨ G.dist u w = G.dist u v - 1 := by
  by_cases! huw : ¬G.Reachable u w
  · grind [dist_eq_zero_iff_eq_or_not_reachable, Reachable.trans, Adj.reachable]
  have : G.dist v w = 1 := dist_eq_one_iff_adj.mpr hadj
  have : G.dist w v = 1 := dist_eq_one_iff_adj.mpr hadj.symm
  have : G.dist u w <= G.dist u v + G.dist v w := hadj.reachable.dist_triangle_right u
  have : G.dist u v <= G.dist u w + G.dist w v := huw.dist_triangle_left v
  lia

/--
theorem `Walk.isPath_of_length_eq_dist` / 定理 `Walk.isPath_of_length_eq_dist`

English:
theorem Walk.isPath_of_length_eq_dist
  given: (p : G.Walk u v) (hp : p.length = G.dist u v)
  proof: by
  classical
  have : p.bypass = p := by
    apply bypass_eq_self_of_length_le_length_bypass
    calc p.length
      _ = G.dist u v := hp
      _ <= p.bypass.length := dist_le p.bypass
  rw [← this]
  apply Walk.bypass_isPath

中文:
定理 途径.isPath_of_length_eq_dist
  条件: (p : G.途径 u v) (hp : p.length = G.dist u v)
  证明: by
  classical
  have : p.bypass = p := by
    apply bypass_eq_self_of_length_le_length_bypass
    calc p.length
      _ = G.dist u v := hp
      _ <= p.bypass.length := dist_le p.bypass
  rw [← this]
  apply Walk.bypass_isPath

Depends on / 依赖: G.dist, Walk.bypass_isPath, bypass, bypass_eq_self_of_length_le_length_bypass, bypass_isPath, classical, dist_le, length, p.bypass, p.bypass.length, p.length
-/
theorem Walk.isPath_of_length_eq_dist (p : G.Walk u v) (hp : p.length = G.dist u v) :
    p.IsPath := by
  classical
  have : p.bypass = p := by
    apply bypass_eq_self_of_length_le_length_bypass
    calc p.length
      _ = G.dist u v := hp
      _ <= p.bypass.length := dist_le p.bypass
  rw [← this]
  apply Walk.bypass_isPath

/--
lemma `Reachable.exists_path_of_dist` / 引理 `Reachable.exists_path_of_dist`

English:
lemma Reachable.exists_path_of_dist
  given: (hr : G.Reachable u v)
  proof: by
  obtain ⟨p, h⟩ := hr.exists_walk_length_eq_dist
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

中文:
引理 Reachable.存在_path_of_dist
  条件: (hr : G.Reachable u v)
  证明: by
  obtain ⟨p, h⟩ := hr.exists_walk_length_eq_dist
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

Depends on / 依赖: exists_walk_length_eq_dist, hr.exists_walk_length_eq_dist, isPath_of_length_eq_dist, p.isPath_of_length_eq_dist
-/
lemma Reachable.exists_path_of_dist (hr : G.Reachable u v) :
    exists (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v := by
  obtain ⟨p, h⟩ := hr.exists_walk_length_eq_dist
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

/--
lemma `Connected.exists_path_of_dist` / 引理 `Connected.exists_path_of_dist`

English:
lemma Connected.exists_path_of_dist
  given: (hconn : G.Connected) (u v : V)
  proof: by
  obtain ⟨p, h⟩ := hconn.exists_walk_length_eq_dist u v
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

@[simp]

中文:
引理 连通.存在_path_of_dist
  条件: (hconn : G.连通) (u v : V)
  证明: by
  obtain ⟨p, h⟩ := hconn.exists_walk_length_eq_dist u v
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

@[simp]

Depends on / 依赖: exists_walk_length_eq_dist, hconn.exists_walk_length_eq_dist, isPath_of_length_eq_dist, p.isPath_of_length_eq_dist
-/
lemma Connected.exists_path_of_dist (hconn : G.Connected) (u v : V) :
    exists (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v := by
  obtain ⟨p, h⟩ := hconn.exists_walk_length_eq_dist u v
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

@[simp]
/--
lemma `dist_bot` / 引理 `dist_bot`

English:
lemma dist_bot
  statement: (⊥ : SimpleGraph V).dist u v = 0
  proof: by
  by_cases h : u = v <;> simp [h]

中文:
引理 dist_bot
  结论: (⊥ : 简单图 V).dist u v = 0
  证明: by
  by_cases h : u = v <;> simp [h]
-/
lemma dist_bot : (⊥ : SimpleGraph V).dist u v = 0 := by
  by_cases h : u = v <;> simp [h]

/--
lemma `dist_top_of_ne` / 引理 `dist_top_of_ne`

English:
lemma dist_top_of_ne
  given: (h : u != v)
  statement: (⊤ : SimpleGraph V).dist u v = 1
  proof: by
  simp [h]

中文:
引理 dist_top_of_ne
  条件: (h : u != v)
  结论: (⊤ : 简单图 V).dist u v = 1
  证明: by
  simp [h]
-/
lemma dist_top_of_ne (h : u != v) : (⊤ : SimpleGraph V).dist u v = 1 := by
  simp [h]

/--
lemma `dist_top` / 引理 `dist_top`

English:
lemma dist_top
  given: [DecidableEq V]
  statement: (⊤ : SimpleGraph V).dist u v = (if u = v then 0 else 1)
  proof: by
  by_cases h : u = v <;> simp [h]

中文:
引理 dist_top
  条件: [DecidableEq V]
  结论: (⊤ : 简单图 V).dist u v = (if u = v then 0 else 1)
  证明: by
  by_cases h : u = v <;> simp [h]
-/
lemma dist_top [DecidableEq V] : (⊤ : SimpleGraph V).dist u v = (if u = v then 0 else 1) := by
  by_cases h : u = v <;> simp [h]

/--
lemma `length_eq_dist_of_subwalk` / 引理 `length_eq_dist_of_subwalk`

English:
lemma length_eq_dist_of_subwalk
  statement: {u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
  proof: by
  refine (dist_le _).eq_of_not_lt' fun hh => ?_
  obtain ⟨ru, rv, h⟩ := h₂
  obtain ⟨s, _⟩ := p₂.reachable.exists_path_of_dist
.append rv let r := ru.append s
  have : p₁.length = ru.length + p₂.length + rv.length := by simp [h]
  have : r.length = ru.length + s.length + rv.length := by simp [r]
  have := dist_le r
  lia

中文:
引理 length_eq_dist_of_subwalk
  结论: {u' v' : V} {p₁ : G.途径 u v} {p₂ : G.途径 u' v'}
  证明: by
  refine (dist_le _).eq_of_not_lt' fun hh => ?_
  obtain ⟨ru, rv, h⟩ := h₂
  obtain ⟨s, _⟩ := p₂.reachable.exists_path_of_dist
.append rv let r := ru.append s
  have : p₁.length = ru.length + p₂.length + rv.length := by simp [h]
  have : r.length = ru.length + s.length + rv.length := by simp [r]
  have := dist_le r
  lia

Depends on / 依赖: append, dist_le, eq_of_not_lt, exists_path_of_dist, length, r.length, reachable, reachable.exists_path_of_dist, ru.append, ru.length, rv.length, s.length
-/
lemma length_eq_dist_of_subwalk {u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h₁ : p₁.length = G.dist u v) (h₂ : p₂.IsSubwalk p₁) : p₂.length = G.dist u' v' := by
  refine (dist_le _).eq_of_not_lt' fun hh => ?_
  obtain ⟨ru, rv, h⟩ := h₂
  obtain ⟨s, _⟩ := p₂.reachable.exists_path_of_dist
.append rv let r := ru.append s
  have : p₁.length = ru.length + p₂.length + rv.length := by simp [h]
  have : r.length = ru.length + s.length + rv.length := by simp [r]
  have := dist_le r
  lia

/-- Supergraphs have smaller or equal distances to their subgraphs. -/
@[gcongr]
/--
theorem `Reachable.dist_anti` / 定理 `Reachable.dist_anti`

English:
theorem Reachable.dist_anti
  given: {G' : SimpleGraph V} (h : G <= G') (hr : G.Reachable u v)
  proof: by
  obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_dist
  rw [← hw]; rw [← Walk.length_map (.ofLE h)]
  apply dist_le

中文:
定理 Reachable.dist_anti
  条件: {G' : 简单图 V} (h : G <= G') (hr : G.Reachable u v)
  证明: by
  obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_dist
  rw [← hw]; rw [← Walk.length_map (.ofLE h)]
  apply dist_le
-/
protected theorem Reachable.dist_anti {G' : SimpleGraph V} (h : G <= G') (hr : G.Reachable u v) :
    G'.dist u v <= G.dist u v := by
  obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_dist
  rw [← hw]; rw [← Walk.length_map (.ofLE h)]
  apply dist_le

/--
lemma `Walk.exists_adj_adj_not_adj_ne` / 引理 `Walk.exists_adj_adj_not_adj_ne`

English:
lemma Walk.exists_adj_adj_not_adj_ne
  statement: {p : G.Walk v w} (hp : p.length = G.dist v w)
  proof: by
  use v, p.getVert 1, p.getVert 2
  have hnp : ¬p.Nil := by grind [Nil.length_eq_zero]
  have : p.tail.tail.length < p.tail.length := by
    rw [← p.tail.length_tail_add_one (by
      simp only [not_nil_iff_lt_length]; rw [← p.length_tail_add_one hnp] at hp ⊢
      lia)]
    lia
  have : p.tail.length < p.length := by rw [← p.length_tail_add_one hnp]; lia
  by_cases hv : v = p.getVert 2
  · have : G.dist v w <= p.tail.tail.length := by
      simpa [hv, p.getVert_tail] using dist_le p.tail.tail
    lia
  by_cases hadj : G.Adj v (p.getVert 2)
  · have : G.dist v w <= p.tail.tail.length + 1 :=
dist_le p.tail.tail.cons p.getVert_tail ▸ hadj
    lia
  exact ⟨p.adj_snd hnp, p.adj_getVert_succ (hp ▸ hl), hadj, hv⟩

中文:
引理 途径.存在_adj_adj_not_adj_ne
  结论: {p : G.途径 v w} (hp : p.length = G.dist v w)
  证明: by
  use v, p.getVert 1, p.getVert 2
  have hnp : ¬p.Nil := by grind [Nil.length_eq_zero]
  have : p.tail.tail.length < p.tail.length := by
    rw [← p.tail.length_tail_add_one (by
      simp only [not_nil_iff_lt_length]; rw [← p.length_tail_add_one hnp] at hp ⊢
      lia)]
    lia
  have : p.tail.length < p.length := by rw [← p.length_tail_add_one hnp]; lia
  by_cases hv : v = p.getVert 2
  · have : G.dist v w <= p.tail.tail.length := by
      simpa [hv, p.getVert_tail] using dist_le p.tail.tail
    lia
  by_cases hadj : G.Adj v (p.getVert 2)
  · have : G.dist v w <= p.tail.tail.length + 1 :=
dist_le p.tail.tail.cons p.getVert_tail ▸ hadj
    lia
  exact ⟨p.adj_snd hnp, p.adj_getVert_succ (hp ▸ hl), hadj, hv⟩

Depends on / 依赖: G.Adj, G.dist, Nil.length_eq_zero, dist_le, getVert, getVert_tail, length, length_eq_zero, length_tail_add_one, not_nil_iff_lt_length, p.Nil, p.getVe, p.getVert, p.getVert_tail, p.length, p.length_tail_add_one, p.tail.length, p.tail.length_tail_add_one, p.tail.tail, p.tail.tail.length
-/
lemma Walk.exists_adj_adj_not_adj_ne {p : G.Walk v w} (hp : p.length = G.dist v w)
    (hl : 1 < G.dist v w) : exists (x a b : V), G.Adj x a ∧ G.Adj a b ∧ ¬ G.Adj x b ∧ x != b := by
  use v, p.getVert 1, p.getVert 2
  have hnp : ¬p.Nil := by grind [Nil.length_eq_zero]
  have : p.tail.tail.length < p.tail.length := by
    rw [← p.tail.length_tail_add_one (by
      simp only [not_nil_iff_lt_length]; rw [← p.length_tail_add_one hnp] at hp ⊢
      lia)]
    lia
  have : p.tail.length < p.length := by rw [← p.length_tail_add_one hnp]; lia
  by_cases hv : v = p.getVert 2
  · have : G.dist v w <= p.tail.tail.length := by
      simpa [hv, p.getVert_tail] using dist_le p.tail.tail
    lia
  by_cases hadj : G.Adj v (p.getVert 2)
  · have : G.dist v w <= p.tail.tail.length + 1 :=
dist_le p.tail.tail.cons p.getVert_tail ▸ hadj
    lia
  exact ⟨p.adj_snd hnp, p.adj_getVert_succ (hp ▸ hl), hadj, hv⟩

end dist

/-! ## Ball -/

section ball

/--
Definition of `ball` / `ball` 的定义

English:
definition ball
  signature: (c : V) (r : Nat∞)
  body: {v | G.edist v c < r}

中文:
定义 ball
  签名: (c : V) (r : 自然数∞)
  定义体: {v | G.edist v c < r}

Depends on / 依赖: G.edist
-/
def ball (c : V) (r : Nat∞) : Set V :=
  {v | G.edist v c < r}

variable {G} {c v : V} {r r₁ r₂ : Nat∞}

@[simp]
/--
theorem `mem_ball` / 定理 `mem_ball`

English:
theorem mem_ball
  statement: v in G.ball c r ↔ G.edist v c < r
  proof: .rfl

中文:
定理 mem_ball
  结论: v in G.ball c r ↔ G.edist v c < r
  证明: .rfl
-/
theorem mem_ball : v in G.ball c r ↔ G.edist v c < r := .rfl

/-- The ball of radius zero is empty. -/
@[simp]
/--
theorem `ball_zero` / 定理 `ball_zero`

English:
theorem ball_zero
  statement: G.ball c 0 = ∅
  proof: by simp [ball]

中文:
定理 ball_zero
  结论: G.ball c 0 = ∅
  证明: by simp [ball]
-/
theorem ball_zero : G.ball c 0 = ∅ := by simp [ball]

/-- The ball of radius one consists of just the center. -/
@[simp]
/--
theorem `ball_one` / 定理 `ball_one`

English:
theorem ball_one
  statement: G.ball c 1 = {c}
  proof: by
  simp [ball]

中文:
定理 ball_one
  结论: G.ball c 1 = {c}
  证明: by
  simp [ball]
-/
theorem ball_one : G.ball c 1 = {c} := by
  simp [ball]

/-- The ball of radius two consists of the center and its neighbors. -/
@[simp]
/--
theorem `ball_two` / 定理 `ball_two`

English:
theorem ball_two
  statement: G.ball c 2 = insert c (G.neighborSet c)
  proof: by
  ext v
  simp [one_add_one_eq_two.symm, ENat.lt_add_one_iff ENat.one_ne_top,
    edist_le_one_iff_adj_or_eq, adj_comm, or_comm]

中文:
定理 ball_two
  结论: G.ball c 2 = insert c (G.neighborSet c)
  证明: by
  ext v
  simp [one_add_one_eq_two.symm, ENat.lt_add_one_iff ENat.one_ne_top,
    edist_le_one_iff_adj_or_eq, adj_comm, or_comm]

Depends on / 依赖: ENat.lt_add_one_iff, ENat.one_ne_top, adj_comm, edist_le_one_iff_adj_or_eq, lt_add_one_iff, one_add_one_eq_two, one_add_one_eq_two.symm, one_ne_top, or_comm
-/
theorem ball_two : G.ball c 2 = insert c (G.neighborSet c) := by
  ext v
  simp [one_add_one_eq_two.symm, ENat.lt_add_one_iff ENat.one_ne_top,
    edist_le_one_iff_adj_or_eq, adj_comm, or_comm]

/--
theorem `ball_top` / 定理 `ball_top`

English:
theorem ball_top
  proof: by
  simp [Set.ext_iff, lt_top_iff_ne_top, edist_ne_top_iff_reachable]

中文:
定理 ball_top
  证明: by
  simp [Set.ext_iff, lt_top_iff_ne_top, edist_ne_top_iff_reachable]

Depends on / 依赖: Set.ext_iff, edist_ne_top_iff_reachable, ext_iff, lt_top_iff_ne_top
-/
theorem ball_top :
    G.ball c ⊤ = (G.connectedComponentMk c).supp := by
  simp [Set.ext_iff, lt_top_iff_ne_top, edist_ne_top_iff_reachable]

/--
theorem `mem_ball_top` / 定理 `mem_ball_top`

English:
theorem mem_ball_top
  statement: v in G.ball c ⊤ ↔ G.Reachable v c
  proof: by
  simp [lt_top_iff_ne_top, edist_ne_top_iff_reachable]

中文:
定理 mem_ball_top
  结论: v in G.ball c ⊤ ↔ G.Reachable v c
  证明: by
  simp [lt_top_iff_ne_top, edist_ne_top_iff_reachable]

Depends on / 依赖: edist_ne_top_iff_reachable, lt_top_iff_ne_top
-/
theorem mem_ball_top : v in G.ball c ⊤ ↔ G.Reachable v c := by
  simp [lt_top_iff_ne_top, edist_ne_top_iff_reachable]

/-- Balls are monotone in the radius. -/
@[gcongr]
/--
theorem `ball_mono` / 定理 `ball_mono`

English:
theorem ball_mono
  given: (h : r₁ <= r₂)
  statement: G.ball c r₁ subseteq G.ball c r₂
  proof: fun _ hv => lt_of_lt_of_le hv h

中文:
定理 ball_mono
  条件: (h : r₁ <= r₂)
  结论: G.ball c r₁ subseteq G.ball c r₂
  证明: fun _ hv => lt_of_lt_of_le hv h

Depends on / 依赖: lt_of_lt_of_le
-/
theorem ball_mono (h : r₁ <= r₂) : G.ball c r₁ subseteq G.ball c r₂ :=
  fun _ hv => lt_of_lt_of_le hv h

/--
theorem `mem_ball_self` / 定理 `mem_ball_self`

English:
theorem mem_ball_self
  given: (hr : 0 < r)
  statement: c in G.ball c r
  proof: by
  simp [ball, hr]

中文:
定理 mem_ball_self
  条件: (hr : 0 < r)
  结论: c in G.ball c r
  证明: by
  simp [ball, hr]
-/
theorem mem_ball_self (hr : 0 < r) : c in G.ball c r := by
  simp [ball, hr]

/--
theorem `mem_ball_comm` / 定理 `mem_ball_comm`

English:
theorem mem_ball_comm
  statement: v in G.ball c r ↔ c in G.ball v r
  proof: by
  simp [ball, edist_comm]

中文:
定理 mem_ball_comm
  结论: v in G.ball c r ↔ c in G.ball v r
  证明: by
  simp [ball, edist_comm]

Depends on / 依赖: edist_comm
-/
theorem mem_ball_comm : v in G.ball c r ↔ c in G.ball v r := by
  simp [ball, edist_comm]

end ball

end SimpleGraph
