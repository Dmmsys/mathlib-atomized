/-
Copyright (c) 2026 Tianyi Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianyi Zhao
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Chords of walks

This file defines chords and chordless walks in a simple graph.

## Main definitions

* `SimpleGraph.Walk.IsChord`: an edge of the ambient graph between two vertices of a walk
  which is not an edge of the walk itself
* `SimpleGraph.Walk.IsChordless`: a walk with no chords

## Tags
walks, chords
-/

public section

namespace SimpleGraph
namespace Walk

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

/-- A chord of a walk `p` is an edge of `G` between two vertices of `p` which is not one
of the edges of `p`. -/
@[expose]
/--
Definition of `IsChord` / `IsChord` 的定义

English:
definition IsChord
  signature: (p : G.Walk u v) (e : Sym2 V)
  body: e in G.edgeSet ∧ e ∉ p.edges ∧
    e.lift ⟨fun v w => v in p.support ∧ w in p.support, by grind⟩

中文:
定义 IsChord
  签名: (p : G.Walk u v) (e : Sym2 V)
  定义体: e in G.edgeSet ∧ e ∉ p.edges ∧
    e.lift ⟨fun v w => v in p.support ∧ w in p.support, by grind⟩

Depends on / 依赖: G.edgeSet, e.lift, edgeSet, p.edges, p.support, support
-/
def IsChord (p : G.Walk u v) (e : Sym2 V) : Prop :=
  e in G.edgeSet ∧ e ∉ p.edges ∧
    e.lift ⟨fun v w => v in p.support ∧ w in p.support, by grind⟩

/--
theorem `isChord_sym2Mk` / 定理 `isChord_sym2Mk`

English:
theorem isChord_sym2Mk
  given: {p : G.Walk u v} {u' v' : V}
  proof: .rfl

中文:
定理 isChord_sym2Mk
  条件: {p : G.Walk u v} {u' v' : V}
  证明: .rfl
-/
theorem isChord_sym2Mk {p : G.Walk u v} {u' v' : V} :
    p.IsChord s(u', v') ↔ G.Adj u' v' ∧ s(u', v') ∉ p.edges ∧ u' in p.support ∧ v' in p.support :=
  .rfl

/-- A walk is chordless if it has no chords. -/
@[expose]
/--
Definition of `IsChordless` / `IsChordless` 的定义

English:
definition IsChordless
  signature: (p : G.Walk u v)
  body: forall ⦃e : Sym2 V⦄, ¬ p.IsChord e

中文:
定义 IsChordless
  签名: (p : G.Walk u v)
  定义体: forall ⦃e : Sym2 V⦄, ¬ p.IsChord e

Depends on / 依赖: IsChord, p.IsChord
-/
def IsChordless (p : G.Walk u v) : Prop :=
  forall ⦃e : Sym2 V⦄, ¬ p.IsChord e

/--
theorem `isChordless_iff_forall_mem_edges` / 定理 `isChordless_iff_forall_mem_edges`

English:
theorem isChordless_iff_forall_mem_edges
  given: {p : G.Walk u v}
  proof: by
  simp [IsChordless, Sym2.forall, isChord_sym2Mk]; grind

中文:
定理 isChordless_iff_forall_mem_edges
  条件: {p : G.Walk u v}
  证明: by
  simp [IsChordless, Sym2.forall, isChord_sym2Mk]; grind

Depends on / 依赖: IsChordless, Sym2.forall, isChord_sym2Mk
-/
theorem isChordless_iff_forall_mem_edges {p : G.Walk u v} :
    p.IsChordless ↔
      forall ⦃u' v' : V⦄, u' in p.support -> v' in p.support -> G.Adj u' v' -> s(u', v') in p.edges := by
  simp [IsChordless, Sym2.forall, isChord_sym2Mk]; grind

/--
theorem `IsChordless.mem_edges` / 定理 `IsChordless.mem_edges`

English:
theorem IsChordless.mem_edges
  statement: {p : G.Walk u v} (h : p.IsChordless) {u' v' : V}
  proof: isChordless_iff_forall_mem_edges.mp h hu' hv' hadj

中文:
定理 IsChordless.mem_edges
  结论: {p : G.Walk u v} (h : p.IsChordless) {u' v' : V}
  证明: isChordless_iff_forall_mem_edges.mp h hu' hv' hadj

Depends on / 依赖: isChordless_iff_forall_mem_edges, isChordless_iff_forall_mem_edges.mp
-/
theorem IsChordless.mem_edges {p : G.Walk u v} (h : p.IsChordless) {u' v' : V}
    (hu' : u' in p.support) (hv' : v' in p.support) (hadj : G.Adj u' v') : s(u', v') in p.edges :=
  isChordless_iff_forall_mem_edges.mp h hu' hv' hadj

/--
theorem `_root_.SimpleGraph.Adj.isChordless_toWalk` / 定理 `_root_.SimpleGraph.Adj.isChordless_toWalk`

English:
theorem _root_.SimpleGraph.Adj.isChordless_toWalk
  given: (h : G.Adj u v)
  statement: h.toWalk.IsChordless
  proof: by
  grind [isChordless_iff_forall_mem_edges, h.support_toWalk, h.edges_toWalk, Adj.ne]

中文:
定理 _root_.SimpleGraph.Adj.isChordless_toWalk
  条件: (h : G.Adj u v)
  结论: h.toWalk.IsChordless
  证明: by
  grind [isChordless_iff_forall_mem_edges, h.support_toWalk, h.edges_toWalk, Adj.ne]

Depends on / 依赖: Adj.ne, edges_toWalk, h.edges_toWalk, h.support_toWalk, isChordless_iff_forall_mem_edges, support_toWalk
-/
theorem _root_.SimpleGraph.Adj.isChordless_toWalk (h : G.Adj u v) : h.toWalk.IsChordless := by
  grind [isChordless_iff_forall_mem_edges, h.support_toWalk, h.edges_toWalk, Adj.ne]

end Walk
end SimpleGraph
