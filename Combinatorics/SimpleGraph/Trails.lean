/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!

# Trails and Eulerian trails

This module contains additional theory about trails, including Eulerian trails (also known
as Eulerian circuits).

## Main definitions

* `SimpleGraph.Walk.IsEulerian` is the predicate that a trail is an Eulerian trail.
* `SimpleGraph.Walk.IsTrail.even_countP_edges_iff` gives a condition on the number of edges
  in a trail that can be incident to a given vertex.
* `SimpleGraph.Walk.IsEulerian.even_degree_iff` gives a condition on the degrees of vertices
  when there exists an Eulerian trail.
* `SimpleGraph.Walk.IsEulerian.card_odd_degree` gives the possible numbers of odd-degree
  vertices when there exists an Eulerian trail.

## TODO

* Prove that there exists an Eulerian trail when the conclusion to
  `SimpleGraph.Walk.IsEulerian.card_odd_degree` holds.

## Tags

Eulerian trails

-/

@[expose] public section


namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace Walk

/--
Definition of `IsTrail.edgesFinset` / `IsTrail.edgesFinset` 的定义

English:
abbreviation IsTrail.edgesFinset
  signature: {u v : V} {p : G.Walk u v} (h : p.IsTrail)
  body: ⟨p.edges, h.edges_nodup⟩

中文:
缩写 是Trail.edgesFinset
  签名: {u v : V} {p : G.途径 u v} (h : p.是Trail)
  定义体: ⟨p.edges, h.edges_nodup⟩

Depends on / 依赖: edges_nodup, h.edges_nodup, p.edges
-/
abbrev IsTrail.edgesFinset {u v : V} {p : G.Walk u v} (h : p.IsTrail) : Finset (Sym2 V) :=
  ⟨p.edges, h.edges_nodup⟩

variable [DecidableEq V]

/--
theorem `IsTrail.even_countP_edges_iff` / 定理 `IsTrail.even_countP_edges_iff`

English:
theorem IsTrail.even_countP_edges_iff
  given: {u v : V} {p : G.Walk u v} (ht : p.IsTrail) (x : V)
  proof: by
  induction p with
  | nil => simp
  | cons huv p ih =>
    rw [isTrail_cons] at ht
    specialize ih ht.1
    simp only [List.countP_cons, Ne, edges_cons, Sym2.mem_iff]
    split_ifs with h
    · rw [decide_eq_true_eq] at h
      obtain (rfl | rfl) := h
      · rw [Nat.even_add_one, ih]
        simp only [huv.ne, imp_false, Ne, not_false_iff, true_and, not_forall,
          Classical.not_not, exists_prop, not_true, false_and,
          and_iff_right_iff_imp]
        rintro rfl rfl
        exact G.loopless.irrefl _ huv
      · have := huv.ne; grind
    · grind

中文:
定理 是Trail.even_countP_edges_iff
  条件: {u v : V} {p : G.途径 u v} (ht : p.是Trail) (x : V)
  证明: by
  induction p with
  | nil => simp
  | cons huv p ih =>
    rw [isTrail_cons] at ht
    specialize ih ht.1
    simp only [List.countP_cons, Ne, edges_cons, Sym2.mem_iff]
    split_ifs with h
    · rw [decide_eq_true_eq] at h
      obtain (rfl | rfl) := h
      · rw [Nat.even_add_one, ih]
        simp only [huv.ne, imp_false, Ne, not_false_iff, true_and, not_forall,
          Classical.not_not, exists_prop, not_true, false_and,
          and_iff_right_iff_imp]
        rintro rfl rfl
        exact G.loopless.irrefl _ huv
      · have := huv.ne; grind
    · grind

Depends on / 依赖: Classical, Classical.not_not, G.loopless.irrefl, List.countP_cons, Nat.even_add_one, Sym2.mem_iff, and_iff_right_iff_imp, countP_cons, decide_eq_true_eq, edges_cons, even_add_one, exists_prop, false_and, huv.ne, imp_false, irrefl, isTrail_cons, loopless, mem_iff, not_false_iff
-/
theorem IsTrail.even_countP_edges_iff {u v : V} {p : G.Walk u v} (ht : p.IsTrail) (x : V) :
    Even (p.edges.countP fun e => x in e) ↔ u != v -> x != u ∧ x != v := by
  induction p with
  | nil => simp
  | cons huv p ih =>
    rw [isTrail_cons] at ht
    specialize ih ht.1
    simp only [List.countP_cons, Ne, edges_cons, Sym2.mem_iff]
    split_ifs with h
    · rw [decide_eq_true_eq] at h
      obtain (rfl | rfl) := h
      · rw [Nat.even_add_one, ih]
        simp only [huv.ne, imp_false, Ne, not_false_iff, true_and, not_forall,
          Classical.not_not, exists_prop, not_true, false_and,
          and_iff_right_iff_imp]
        rintro rfl rfl
        exact G.loopless.irrefl _ huv
      · have := huv.ne; grind
    · grind

/--
Definition of `IsEulerian` / `IsEulerian` 的定义

English:
definition IsEulerian
  signature: {u v : V} (p : G.Walk u v)
  body: forall e, e in G.edgeSet -> p.edges.count e = 1

中文:
定义 IsEulerian
  签名: {u v : V} (p : G.途径 u v)
  定义体: forall e, e in G.edgeSet -> p.edges.count e = 1

Depends on / 依赖: G.edgeSet, edgeSet, p.edges.count
-/
def IsEulerian {u v : V} (p : G.Walk u v) : Prop :=
  forall e, e in G.edgeSet -> p.edges.count e = 1

/--
theorem `IsEulerian.isTrail` / 定理 `IsEulerian.isTrail`

English:
theorem IsEulerian.isTrail
  given: {u v : V} {p : G.Walk u v} (h : p.IsEulerian)
  statement: p.IsTrail
  proof: by
  rw [isTrail_def]; rw [List.nodup_iff_count_le_one]
  intro e
  by_cases he : e in p.edges
  · exact (h e (edges_subset_edgeSet _ he)).le
  · simp [List.count_eq_zero_of_not_mem he]

中文:
定理 IsEulerian.isTrail
  条件: {u v : V} {p : G.途径 u v} (h : p.IsEulerian)
  结论: p.是Trail
  证明: by
  rw [isTrail_def]; rw [List.nodup_iff_count_le_one]
  intro e
  by_cases he : e in p.edges
  · exact (h e (edges_subset_edgeSet _ he)).le
  · simp [List.count_eq_zero_of_not_mem he]

Depends on / 依赖: List.count_eq_zero_of_not_mem, List.nodup_iff_count_le_one, count_eq_zero_of_not_mem, edges_subset_edgeSet, isTrail_def, nodup_iff_count_le_one, p.edges
-/
theorem IsEulerian.isTrail {u v : V} {p : G.Walk u v} (h : p.IsEulerian) : p.IsTrail := by
  rw [isTrail_def]; rw [List.nodup_iff_count_le_one]
  intro e
  by_cases he : e in p.edges
  · exact (h e (edges_subset_edgeSet _ he)).le
  · simp [List.count_eq_zero_of_not_mem he]

/--
theorem `IsEulerian.mem_edges_iff` / 定理 `IsEulerian.mem_edges_iff`

English:
theorem IsEulerian.mem_edges_iff
  given: {u v : V} {p : G.Walk u v} (h : p.IsEulerian) {e : Sym2 V}
  proof: ⟨fun h => p.edges_subset_edgeSet h,
   fun he => by simpa [Nat.succ_le_iff] using (h e he).ge⟩

中文:
定理 IsEulerian.mem_edges_iff
  条件: {u v : V} {p : G.途径 u v} (h : p.IsEulerian) {e : Sym2 V}
  证明: ⟨fun h => p.edges_subset_edgeSet h,
   fun he => by simpa [Nat.succ_le_iff] using (h e he).ge⟩

Depends on / 依赖: Nat.succ_le_iff, edges_subset_edgeSet, p.edges_subset_edgeSet, succ_le_iff
-/
theorem IsEulerian.mem_edges_iff {u v : V} {p : G.Walk u v} (h : p.IsEulerian) {e : Sym2 V} :
    e in p.edges ↔ e in G.edgeSet :=
  ⟨fun h => p.edges_subset_edgeSet h,
   fun he => by simpa [Nat.succ_le_iff] using (h e he).ge⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The edge set of an Eulerian graph is finite. -/
@[instance_reducible]
/--
Definition of `IsEulerian.fintypeEdgeSet` / `IsEulerian.fintypeEdgeSet` 的定义

English:
definition IsEulerian.fintypeEdgeSet
  signature: {u v : V} {p : G.Walk u v} (h : p.IsEulerian)
  body: Fintype.ofFinset h.isTrail.edgesFinset fun e => by
    simp only [Finset.mem_mk, Multiset.mem_coe, h.mem_edges_iff]

中文:
定义 IsEulerian.fintypeEdgeSet
  签名: {u v : V} {p : G.途径 u v} (h : p.IsEulerian)
  定义体: Fintype.ofFinset h.isTrail.edgesFinset fun e => by
    simp only [Finset.mem_mk, Multiset.mem_coe, h.mem_edges_iff]

Depends on / 依赖: Finset, Finset.mem_mk, Fintype, Fintype.ofFinset, Multiset, Multiset.mem_coe, edgesFinset, h.isTrail.edgesFinset, h.mem_edges_iff, isTrail, mem_coe, mem_edges_iff, mem_mk, ofFinset
-/
def IsEulerian.fintypeEdgeSet {u v : V} {p : G.Walk u v} (h : p.IsEulerian) :
    Fintype G.edgeSet :=
  Fintype.ofFinset h.isTrail.edgesFinset fun e => by
    simp only [Finset.mem_mk, Multiset.mem_coe, h.mem_edges_iff]

/--
theorem `IsTrail.isEulerian_of_forall_mem` / 定理 `IsTrail.isEulerian_of_forall_mem`

English:
theorem IsTrail.isEulerian_of_forall_mem
  statement: {u v : V} {p : G.Walk u v} (h : p.IsTrail)
  proof: fun e he =>
  List.count_eq_one_of_mem h.edges_nodup (hc e he)

中文:
定理 是Trail.isEulerian_of_对任意_mem
  结论: {u v : V} {p : G.途径 u v} (h : p.是Trail)
  证明: fun e he =>
  List.count_eq_one_of_mem h.edges_nodup (hc e he)
-/
theorem IsTrail.isEulerian_of_forall_mem {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (hc : forall e, e in G.edgeSet -> e in p.edges) : p.IsEulerian := fun e he =>
  List.count_eq_one_of_mem h.edges_nodup (hc e he)

/--
theorem `isEulerian_iff` / 定理 `isEulerian_iff`

English:
theorem isEulerian_iff
  given: {u v : V} (p : G.Walk u v)
  proof: by
  constructor
  · intro h
    exact ⟨h.isTrail, fun _ => h.mem_edges_iff.mpr⟩
  · rintro ⟨h, hl⟩
    exact h.isEulerian_of_forall_mem hl

中文:
定理 isEulerian_iff
  条件: {u v : V} (p : G.途径 u v)
  证明: by
  constructor
  · intro h
    exact ⟨h.isTrail, fun _ => h.mem_edges_iff.mpr⟩
  · rintro ⟨h, hl⟩
    exact h.isEulerian_of_forall_mem hl

Depends on / 依赖: h.isEulerian_of_forall_mem, h.isTrail, h.mem_edges_iff.mpr, isEulerian_of_forall_mem, isTrail, mem_edges_iff
-/
theorem isEulerian_iff {u v : V} (p : G.Walk u v) :
    p.IsEulerian ↔ p.IsTrail ∧ forall e, e in G.edgeSet -> e in p.edges := by
  constructor
  · intro h
    exact ⟨h.isTrail, fun _ => h.mem_edges_iff.mpr⟩
  · rintro ⟨h, hl⟩
    exact h.isEulerian_of_forall_mem hl

/--
theorem `IsTrail.isEulerian_iff` / 定理 `IsTrail.isEulerian_iff`

English:
theorem IsTrail.isEulerian_iff
  given: {u v : V} {p : G.Walk u v} (hp : p.IsTrail)
  proof: ⟨fun h => Set.Subset.antisymm p.edges_subset_edgeSet (p.isEulerian_iff.mp h).2,
   fun h => p.isEulerian_iff.mpr ⟨hp, by simp [← h]⟩⟩

中文:
定理 是Trail.isEulerian_iff
  条件: {u v : V} {p : G.途径 u v} (hp : p.是Trail)
  证明: ⟨fun h => Set.Subset.antisymm p.edges_subset_edgeSet (p.isEulerian_iff.mp h).2,
   fun h => p.isEulerian_iff.mpr ⟨hp, by simp [← h]⟩⟩

Depends on / 依赖: Set.Subset.antisymm, Subset, antisymm, edges_subset_edgeSet, isEulerian_iff, p.edges_subset_edgeSet, p.isEulerian_iff.mp, p.isEulerian_iff.mpr
-/
theorem IsTrail.isEulerian_iff {u v : V} {p : G.Walk u v} (hp : p.IsTrail) :
    p.IsEulerian ↔ p.edgeSet = G.edgeSet :=
  ⟨fun h => Set.Subset.antisymm p.edges_subset_edgeSet (p.isEulerian_iff.mp h).2,
   fun h => p.isEulerian_iff.mpr ⟨hp, by simp [← h]⟩⟩

/--
theorem `IsEulerian.edgeSet_eq` / 定理 `IsEulerian.edgeSet_eq`

English:
theorem IsEulerian.edgeSet_eq
  given: {u v : V} {p : G.Walk u v} (h : p.IsEulerian)
  proof: by
  rwa [← h.isTrail.isEulerian_iff]

中文:
定理 IsEulerian.edgeSet_eq
  条件: {u v : V} {p : G.途径 u v} (h : p.IsEulerian)
  证明: by
  rwa [← h.isTrail.isEulerian_iff]

Depends on / 依赖: h.isTrail.isEulerian_iff, isEulerian_iff, isTrail
-/
theorem IsEulerian.edgeSet_eq {u v : V} {p : G.Walk u v} (h : p.IsEulerian) :
    p.edgeSet = G.edgeSet := by
  rwa [← h.isTrail.isEulerian_iff]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsEulerian.edgesFinset_eq` / 定理 `IsEulerian.edgesFinset_eq`

English:
theorem IsEulerian.edgesFinset_eq
  statement: [Fintype G.edgeSet] {u v : V} {p : G.Walk u v}
  proof: by
  ext e
  simp [h.mem_edges_iff]

中文:
定理 IsEulerian.edgesFinset_eq
  结论: [有限类型 G.edgeSet] {u v : V} {p : G.途径 u v}
  证明: by
  ext e
  simp [h.mem_edges_iff]

Depends on / 依赖: h.mem_edges_iff, mem_edges_iff
-/
theorem IsEulerian.edgesFinset_eq [Fintype G.edgeSet] {u v : V} {p : G.Walk u v}
    (h : p.IsEulerian) : h.isTrail.edgesFinset = G.edgeFinset := by
  ext e
  simp [h.mem_edges_iff]

/--
theorem `IsEulerian.even_degree_iff` / 定理 `IsEulerian.even_degree_iff`

English:
theorem IsEulerian.even_degree_iff
  statement: {x u v : V} {p : G.Walk u v} (ht : p.IsEulerian) [Fintype V]
  proof: by
  convert! ht.isTrail.even_countP_edges_iff x
  rw [← Multiset.coe_countP]; rw [Multiset.countP_eq_card_filter]; rw [← card_incidenceFinset_eq_degree]
  change Multiset.card _ = _
  congr 1
  convert_to! _ = (ht.isTrail.edgesFinset.filter (x in ·)).val
  rw [ht.edgesFinset_eq]; rw [G.incidenceFinset_eq_filter x]

中文:
定理 IsEulerian.even_degree_iff
  结论: {x u v : V} {p : G.途径 u v} (ht : p.IsEulerian) [有限类型 V]
  证明: by
  convert! ht.isTrail.even_countP_edges_iff x
  rw [← Multiset.coe_countP]; rw [Multiset.countP_eq_card_filter]; rw [← card_incidenceFinset_eq_degree]
  change Multiset.card _ = _
  congr 1
  convert_to! _ = (ht.isTrail.edgesFinset.filter (x in ·)).val
  rw [ht.edgesFinset_eq]; rw [G.incidenceFinset_eq_filter x]

Depends on / 依赖: G.incidenceFinset_eq_filter, Multiset, Multiset.card, Multiset.coe_countP, Multiset.countP_eq_card_filter, card_incidenceFinset_eq_degree, coe_countP, convert, convert_to, countP_eq_card_filter, edgesFinset, edgesFinset_eq, even_countP_edges_iff, filter, ht.edgesFinset_eq, ht.isTrail.edgesFinset.filter, ht.isTrail.even_countP_edges_iff, incidenceFinset_eq_filter, isTrail
-/
theorem IsEulerian.even_degree_iff {x u v : V} {p : G.Walk u v} (ht : p.IsEulerian) [Fintype V]
    [DecidableRel G.Adj] : Even (G.degree x) ↔ u != v -> x != u ∧ x != v := by
  convert! ht.isTrail.even_countP_edges_iff x
  rw [← Multiset.coe_countP]; rw [Multiset.countP_eq_card_filter]; rw [← card_incidenceFinset_eq_degree]
  change Multiset.card _ = _
  congr 1
  convert_to! _ = (ht.isTrail.edgesFinset.filter (x in ·)).val
  rw [ht.edgesFinset_eq]; rw [G.incidenceFinset_eq_filter x]

/--
theorem `IsEulerian.card_filter_odd_degree` / 定理 `IsEulerian.card_filter_odd_degree`

English:
theorem IsEulerian.card_filter_odd_degree
  statement: [Fintype V] [DecidableRel G.Adj] {u v : V}
  proof: by
  subst s
  simp only [← Nat.not_even_iff_odd, Finset.card_eq_zero]
  simp only [ht.even_degree_iff, Ne, not_forall, not_and, Classical.not_not, exists_prop]
  obtain rfl | hn := eq_or_ne u v
  · simp
  · right
    convert_to _ = ({u, v} : Finset V).card
    · simp [hn]
    · congr
      ext x
      simp [hn, imp_iff_not_or]

中文:
定理 IsEulerian.card_filter_odd_degree
  结论: [有限类型 V] [DecidableRel G.伴随] {u v : V}
  证明: by
  subst s
  simp only [← Nat.not_even_iff_odd, Finset.card_eq_zero]
  simp only [ht.even_degree_iff, Ne, not_forall, not_and, Classical.not_not, exists_prop]
  obtain rfl | hn := eq_or_ne u v
  · simp
  · right
    convert_to _ = ({u, v} : Finset V).card
    · simp [hn]
    · congr
      ext x
      simp [hn, imp_iff_not_or]

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.card_eq_zero, Nat.not_even_iff_odd, card_eq_zero, convert_to, eq_or_ne, even_degree_iff, exists_prop, ht.even_degree_iff, imp_iff_not_or, not_and, not_even_iff_odd, not_forall, not_not
-/
theorem IsEulerian.card_filter_odd_degree [Fintype V] [DecidableRel G.Adj] {u v : V}
    {p : G.Walk u v} (ht : p.IsEulerian) {s} (h : s = ({ v | Odd (G.degree v) } : Finset V)) :
    s.card = 0 ∨ s.card = 2 := by
  subst s
  simp only [← Nat.not_even_iff_odd, Finset.card_eq_zero]
  simp only [ht.even_degree_iff, Ne, not_forall, not_and, Classical.not_not, exists_prop]
  obtain rfl | hn := eq_or_ne u v
  · simp
  · right
    convert_to _ = ({u, v} : Finset V).card
    · simp [hn]
    · congr
      ext x
      simp [hn, imp_iff_not_or]

/--
theorem `IsEulerian.card_odd_degree` / 定理 `IsEulerian.card_odd_degree`

English:
theorem IsEulerian.card_odd_degree
  statement: [Fintype V] [DecidableRel G.Adj] {u v : V} {p : G.Walk u v}
  proof: by
  rw [← Set.toFinset_card]
  apply IsEulerian.card_filter_odd_degree ht
  simp

中文:
定理 IsEulerian.card_odd_degree
  结论: [有限类型 V] [DecidableRel G.伴随] {u v : V} {p : G.途径 u v}
  证明: by
  rw [← Set.toFinset_card]
  apply IsEulerian.card_filter_odd_degree ht
  simp

Depends on / 依赖: IsEulerian, IsEulerian.card_filter_odd_degree, Set.toFinset_card, card_filter_odd_degree, toFinset_card
-/
theorem IsEulerian.card_odd_degree [Fintype V] [DecidableRel G.Adj] {u v : V} {p : G.Walk u v}
    (ht : p.IsEulerian) :
    Fintype.card { v | Odd (G.degree v) } = 0 ∨ Fintype.card { v | Odd (G.degree v) } = 2 := by
  rw [← Set.toFinset_card]
  apply IsEulerian.card_filter_odd_degree ht
  simp

end Walk

end SimpleGraph
