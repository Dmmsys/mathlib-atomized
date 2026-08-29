/-
Copyright (c) 2026 Justin Lai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Lai
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!

# Star Graphs

## Main definitions

* `SimpleGraph.starGraph r` is the star graph on V centered at r. Every non-center vertex is
  adjacent to r.

## Main statements

* `SimpleGraph.isTree_starGraph` proves the star graph is a tree.


## Tags

star graph
-/

@[expose] public section

namespace SimpleGraph

variable {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')

/--
Definition of `starGraph` / `starGraph` 的定义

English:
definition starGraph
  signature: (r : V)
  body: .fromRel fun v _ => v = r

中文:
定义 starGraph
  签名: (r : V)
  定义体: .fromRel fun v _ => v = r

Depends on / 依赖: fromRel
-/
def starGraph (r : V) : SimpleGraph V :=
  .fromRel fun v _ => v = r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: V] (r
  body: inferInstanceAs (DecidableRel fun x y => x != y ∧ (x = r ∨ y = r))

@[simp]

中文:
实例 [DecidableEq
  签名: V] (r
  定义体: inferInstanceAs (DecidableRel fun x y => x != y ∧ (x = r ∨ y = r))

@[simp]

Depends on / 依赖: DecidableRel
-/
instance [DecidableEq V] (r : V) : DecidableRel (starGraph r).Adj :=
  inferInstanceAs (DecidableRel fun x y => x != y ∧ (x = r ∨ y = r))

@[simp]
/--
lemma `starGraph_adj` / 引理 `starGraph_adj`

English:
lemma starGraph_adj
  given: {r x y : V}
  statement: (starGraph r).Adj x y ↔ x != y ∧ (x = r ∨ y = r)
  proof: by
  simp [starGraph, fromRel]

@[simp]

中文:
引理 starGraph_adj
  条件: {r x y : V}
  结论: (starGraph r).Adj x y ↔ x != y ∧ (x = r ∨ y = r)
  证明: by
  simp [starGraph, fromRel]

@[simp]

Depends on / 依赖: fromRel, starGraph
-/
lemma starGraph_adj {r x y : V} : (starGraph r).Adj x y ↔ x != y ∧ (x = r ∨ y = r) := by
  simp [starGraph, fromRel]

@[simp]
/--
lemma `isUniversal_starGraph_self` / 引理 `isUniversal_starGraph_self`

English:
lemma isUniversal_starGraph_self
  given: {r : V}
  statement: (starGraph r).IsUniversal r
  proof: by
  intro _ _
  simpa

中文:
引理 isUniversal_starGraph_self
  条件: {r : V}
  结论: (starGraph r).IsUniversal r
  证明: by
  intro _ _
  simpa
-/
lemma isUniversal_starGraph_self {r : V} : (starGraph r).IsUniversal r := by
  intro _ _
  simpa

/--
lemma `starGraph_adj_center_iff` / 引理 `starGraph_adj_center_iff`

English:
lemma starGraph_adj_center_iff
  given: {r v : V}
  statement: (starGraph r).Adj r v ↔ r != v
  proof: by simp

中文:
引理 starGraph_adj_center_iff
  条件: {r v : V}
  结论: (starGraph r).Adj r v ↔ r != v
  证明: by simp
-/
lemma starGraph_adj_center_iff {r v : V} : (starGraph r).Adj r v ↔ r != v := by simp

/--
lemma `starGraph_center_adj` / 引理 `starGraph_center_adj`

English:
lemma starGraph_center_adj
  given: {r v : V} (h : r != v)
  statement: (starGraph r).Adj r v
  proof: starGraph_adj_center_iff.mpr h

中文:
引理 starGraph_center_adj
  条件: {r v : V} (h : r != v)
  结论: (starGraph r).Adj r v
  证明: starGraph_adj_center_iff.mpr h

Depends on / 依赖: starGraph_adj_center_iff, starGraph_adj_center_iff.mpr
-/
lemma starGraph_center_adj {r v : V} (h : r != v) : (starGraph r).Adj r v :=
  starGraph_adj_center_iff.mpr h

/--
lemma `starGraph_center_adj'` / 引理 `starGraph_center_adj'`

English:
lemma starGraph_center_adj'
  given: {r v : V} (h : r != v)
  statement: (starGraph r).Adj v r
  proof: (starGraph_center_adj h).symm

中文:
引理 starGraph_center_adj'
  条件: {r v : V} (h : r != v)
  结论: (starGraph r).Adj v r
  证明: (starGraph_center_adj h).symm

Depends on / 依赖: Finset, Finset.coe_nonempty.mpr, coe_nonempty, insert_nonempty, s.insert_nonempty, starGraph_center_adj, to_subtype
-/
lemma starGraph_center_adj' {r v : V} (h : r != v) : (starGraph r).Adj v r :=
  (starGraph_center_adj h).symm

/--
lemma `connected_starGraph` / 引理 `connected_starGraph`

English:
lemma connected_starGraph
  given: (r : V)
  statement: (starGraph r).Connected
  proof: .of_isUniversal isUniversal_starGraph_self

中文:
引理 connected_starGraph
  条件: (r : V)
  结论: (starGraph r).Connected
  证明: .of_isUniversal isUniversal_starGraph_self

Depends on / 依赖: isUniversal_starGraph_self, of_isUniversal
-/
lemma connected_starGraph (r : V) : (starGraph r).Connected :=
  .of_isUniversal isUniversal_starGraph_self

/--
lemma `isAcyclic_starGraph` / 引理 `isAcyclic_starGraph`

English:
lemma isAcyclic_starGraph
  given: (r : V)
  statement: (starGraph r).IsAcyclic
  proof: by
  refine isAcyclic_iff_forall_adj_isBridge.mpr fun v w hadj => ?_
  rw [starGraph_adj] at hadj
  wlog! h : v = r
  · rw [Sym2.eq_swap]
    exact this r w v ⟨hadj.1.symm, hadj.2.symm⟩ (hadj.2.resolve_left h)
  · subst h
    apply not_reachable_of_neighborSet_right_eq_empty hadj.1
    ext x
    aes

中文:
引理 isAcyclic_starGraph
  条件: (r : V)
  结论: (starGraph r).IsAcyclic
  证明: by
  refine isAcyclic_iff_forall_adj_isBridge.mpr fun v w hadj => ?_
  rw [starGraph_adj] at hadj
  wlog! h : v = r
  · rw [Sym2.eq_swap]
    exact this r w v ⟨hadj.1.symm, hadj.2.symm⟩ (hadj.2.resolve_left h)
  · subst h
    apply not_reachable_of_neighborSet_right_eq_empty hadj.1
    ext x
    aes

Depends on / 依赖: Sym2.eq_swap, eq_swap, isAcyclic_iff_forall_adj_isBridge, isAcyclic_iff_forall_adj_isBridge.mpr, not_reachable_of_neighborSet_right_eq_empty, resolve_left, starGraph_adj
-/
lemma isAcyclic_starGraph (r : V) : (starGraph r).IsAcyclic := by
  refine isAcyclic_iff_forall_adj_isBridge.mpr fun v w hadj => ?_
  rw [starGraph_adj] at hadj
  wlog! h : v = r
  · rw [Sym2.eq_swap]
    exact this r w v ⟨hadj.1.symm, hadj.2.symm⟩ (hadj.2.resolve_left h)
  · subst h
    apply not_reachable_of_neighborSet_right_eq_empty hadj.1
    ext x
    aesop

/--
lemma `isTree_starGraph` / 引理 `isTree_starGraph`

English:
lemma isTree_starGraph
  given: (r : V)
  statement: (starGraph r).IsTree
  proof: ⟨connected_starGraph r, isAcyclic_starGraph r⟩

中文:
引理 isTree_starGraph
  条件: (r : V)
  结论: (starGraph r).IsTree
  证明: ⟨connected_starGraph r, isAcyclic_starGraph r⟩

Depends on / 依赖: connected_starGraph, isAcyclic_starGraph
-/
lemma isTree_starGraph (r : V) : (starGraph r).IsTree :=
  ⟨connected_starGraph r, isAcyclic_starGraph r⟩

/--
lemma `degree_starGraph_of_ne_center` / 引理 `degree_starGraph_of_ne_center`

English:
lemma degree_starGraph_of_ne_center
  given: [Fintype V] [DecidableEq V] {r v : V} (h : v != r)
  proof: degree_eq_one_iff_existsUnique_adj.mpr ⟨r, by simp [h], by grind [starGraph_adj]⟩

中文:
引理 degree_starGraph_of_ne_center
  条件: [Fintype V] [DecidableEq V] {r v : V} (h : v != r)
  证明: degree_eq_one_iff_existsUnique_adj.mpr ⟨r, by simp [h], by grind [starGraph_adj]⟩

Depends on / 依赖: degree_eq_one_iff_existsUnique_adj, degree_eq_one_iff_existsUnique_adj.mpr, starGraph_adj
-/
lemma degree_starGraph_of_ne_center [Fintype V] [DecidableEq V] {r v : V} (h : v != r) :
    (starGraph r).degree v = 1 :=
  degree_eq_one_iff_existsUnique_adj.mpr ⟨r, by simp [h], by grind [starGraph_adj]⟩

/--
lemma `degree_starGraph_center` / 引理 `degree_starGraph_center`

English:
lemma degree_starGraph_center
  given: [Fintype V] [DecidableEq V] {r : V}
  proof: by
  simp

中文:
引理 degree_starGraph_center
  条件: [Fintype V] [DecidableEq V] {r : V}
  证明: by
  simp
-/
lemma degree_starGraph_center [Fintype V] [DecidableEq V] {r : V} :
    (starGraph r).degree r = Fintype.card V - 1 := by
  simp

end SimpleGraph
