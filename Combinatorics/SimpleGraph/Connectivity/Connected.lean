/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
## Main definitions

* `SimpleGraph.Reachable` for the relation of whether there exists
  a walk between a given pair of vertices

* `SimpleGraph.Preconnected` and `SimpleGraph.Connected` are predicates
  on simple graphs for whether every vertex can be reached from every other,
  and in the latter case, whether the vertex type is nonempty.

* `SimpleGraph.ConnectedComponent` is the type of connected components of
  a given graph.

* `SimpleGraph.IsBridge` for whether an edge is a bridge edge

## Main statements

* `SimpleGraph.isBridge_iff_forall_cycle_notMem` characterizes bridges as the edges not
  contained in any cycle.

## Tags
trails, paths, cycles, bridge edges
-/

@[expose] public section

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

/-! ## `Reachable` and `Connected` -/

/--
Definition of `Reachable` / `Reachable` 的定义

English:
definition Reachable
  signature: (u v : V)
  body: Nonempty (G.Walk u v)

中文:
定义 Reachable
  签名: (u v : V)
  定义体: Nonempty (G.Walk u v)

Depends on / 依赖: G.Walk, Nonempty
-/
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)

variable {G}

/--
theorem `reachable_iff_nonempty_univ` / 定理 `reachable_iff_nonempty_univ`

English:
theorem reachable_iff_nonempty_univ
  given: {u v : V}
  proof: Set.nonempty_iff_univ_nonempty

中文:
定理 reachable_iff_nonempty_univ
  条件: {u v : V}
  证明: Set.nonempty_iff_univ_nonempty

Depends on / 依赖: Set.nonempty_iff_univ_nonempty, nonempty_iff_univ_nonempty
-/
theorem reachable_iff_nonempty_univ {u v : V} :
    G.Reachable u v ↔ (Set.univ : Set (G.Walk u v)).Nonempty :=
  Set.nonempty_iff_univ_nonempty

/--
lemma `not_reachable_iff_isEmpty_walk` / 引理 `not_reachable_iff_isEmpty_walk`

English:
lemma not_reachable_iff_isEmpty_walk
  given: {u v : V}
  statement: ¬G.Reachable u v ↔ IsEmpty (G.Walk u v)
  proof: not_nonempty_iff

中文:
引理 not_reachable_iff_isEmpty_walk
  条件: {u v : V}
  结论: ¬G.Reachable u v ↔ IsEmpty (G.Walk u v)
  证明: not_nonempty_iff

Depends on / 依赖: not_nonempty_iff
-/
lemma not_reachable_iff_isEmpty_walk {u v : V} : ¬G.Reachable u v ↔ IsEmpty (G.Walk u v) :=
  not_nonempty_iff

/--
theorem `Reachable.elim` / 定理 `Reachable.elim`

English:
theorem Reachable.elim
  statement: {p : Prop} {u v : V} (h : G.Reachable u v)
  proof: Nonempty.elim h hp

中文:
定理 Reachable.elim
  结论: {p : 命题} {u v : V} (h : G.Reachable u v)
  证明: Nonempty.elim h hp
-/
protected theorem Reachable.elim {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Walk u v -> p) : p :=
  Nonempty.elim h hp

/--
theorem `Reachable.elim_path` / 定理 `Reachable.elim_path`

English:
theorem Reachable.elim_path
  statement: {p : Prop} {u v : V} (h : G.Reachable u v)
  proof: by classical exact h.elim fun q => hp q.toPath

中文:
定理 Reachable.elim_path
  结论: {p : 命题} {u v : V} (h : G.Reachable u v)
  证明: by classical exact h.elim fun q => hp q.toPath
-/
protected theorem Reachable.elim_path {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Path u v -> p) : p := by classical exact h.elim fun q => hp q.toPath

/--
theorem `Walk.reachable` / 定理 `Walk.reachable`

English:
theorem Walk.reachable
  given: {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
  statement: G.Reachable u v
  proof: ⟨p⟩

中文:
定理 Walk.reachable
  条件: {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
  结论: G.Reachable u v
  证明: ⟨p⟩
-/
protected theorem Walk.reachable {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : G.Reachable u v :=
  ⟨p⟩

/--
theorem `Adj.reachable` / 定理 `Adj.reachable`

English:
theorem Adj.reachable
  given: {u v : V} (h : G.Adj u v)
  statement: G.Reachable u v
  proof: h.toWalk.reachable

中文:
定理 Adj.reachable
  条件: {u v : V} (h : G.Adj u v)
  结论: G.Reachable u v
  证明: h.toWalk.reachable
-/
protected theorem Adj.reachable {u v : V} (h : G.Adj u v) : G.Reachable u v :=
  h.toWalk.reachable

/--
theorem `adj_le_reachable` / 定理 `adj_le_reachable`

English:
theorem adj_le_reachable
  given: (G : SimpleGraph V)
  statement: G.Adj <= G.Reachable
  proof: fun _ _ => Adj.reachable

@[refl]

中文:
定理 adj_le_reachable
  条件: (G : SimpleGraph V)
  结论: G.Adj <= G.Reachable
  证明: fun _ _ => Adj.reachable

@[refl]

Depends on / 依赖: Adj.reachable, reachable
-/
theorem adj_le_reachable (G : SimpleGraph V) : G.Adj <= G.Reachable :=
  fun _ _ => Adj.reachable

@[refl]
/--
theorem `Reachable.refl` / 定理 `Reachable.refl`

English:
theorem Reachable.refl
  given: (u : V)
  statement: G.Reachable u u
  proof: ⟨Walk.nil⟩

中文:
定理 Reachable.refl
  条件: (u : V)
  结论: G.Reachable u u
  证明: ⟨Walk.nil⟩
-/
protected theorem Reachable.refl (u : V) : G.Reachable u u := ⟨Walk.nil⟩

/--
theorem `Reachable.rfl` / 定理 `Reachable.rfl`

English:
theorem Reachable.rfl
  given: {u : V}
  statement: G.Reachable u u
  proof: Reachable.refl _

@[symm]

中文:
定理 Reachable.rfl
  条件: {u : V}
  结论: G.Reachable u u
  证明: Reachable.refl _

@[symm]
-/
@[simp] protected theorem Reachable.rfl {u : V} : G.Reachable u u := Reachable.refl _

@[symm]
/--
theorem `Reachable.symm` / 定理 `Reachable.symm`

English:
theorem Reachable.symm
  given: {u v : V} (huv : G.Reachable u v)
  statement: G.Reachable v u
  proof: huv.elim fun p => ⟨p.reverse⟩

中文:
定理 Reachable.symm
  条件: {u v : V} (huv : G.Reachable u v)
  结论: G.Reachable v u
  证明: huv.elim fun p => ⟨p.reverse⟩
-/
protected theorem Reachable.symm {u v : V} (huv : G.Reachable u v) : G.Reachable v u :=
  huv.elim fun p => ⟨p.reverse⟩

/--
theorem `reachable_comm` / 定理 `reachable_comm`

English:
theorem reachable_comm
  given: {u v : V}
  statement: G.Reachable u v ↔ G.Reachable v u
  proof: ⟨Reachable.symm, Reachable.symm⟩

@[trans]

中文:
定理 reachable_comm
  条件: {u v : V}
  结论: G.Reachable u v ↔ G.Reachable v u
  证明: ⟨Reachable.symm, Reachable.symm⟩

@[trans]

Depends on / 依赖: Reachable, Reachable.symm
-/
theorem reachable_comm {u v : V} : G.Reachable u v ↔ G.Reachable v u :=
  ⟨Reachable.symm, Reachable.symm⟩

@[trans]
/--
theorem `Reachable.trans` / 定理 `Reachable.trans`

English:
theorem Reachable.trans
  given: {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w)
  proof: huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩

中文:
定理 Reachable.trans
  条件: {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w)
  证明: huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩
-/
protected theorem Reachable.trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w :=
  huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩

/--
theorem `reachable_iff_reflTransGen` / 定理 `reachable_iff_reflTransGen`

English:
theorem reachable_iff_reflTransGen
  given: (u v : V)
  proof: by
  constructor
  · rintro ⟨h⟩
    induction h with
    | nil => rfl
    | cons h' _ ih => exact (Relation.ReflTransGen.single h').trans ih
  · intro h
    induction h with
    | refl => rfl
    | tail _ ha hr => exact Reachable.trans hr ⟨Walk.cons ha Walk.nil⟩

中文:
定理 reachable_iff_reflTransGen
  条件: (u v : V)
  证明: by
  constructor
  · rintro ⟨h⟩
    induction h with
    | nil => rfl
    | cons h' _ ih => exact (Relation.ReflTransGen.single h').trans ih
  · intro h
    induction h with
    | refl => rfl
    | tail _ ha hr => exact Reachable.trans hr ⟨Walk.cons ha Walk.nil⟩

Depends on / 依赖: Reachable, Reachable.trans, ReflTransGen, Relation, Relation.ReflTransGen.single, Walk.cons, Walk.nil, single
-/
theorem reachable_iff_reflTransGen (u v : V) :
    G.Reachable u v ↔ Relation.ReflTransGen G.Adj u v := by
  constructor
  · rintro ⟨h⟩
    induction h with
    | nil => rfl
    | cons h' _ ih => exact (Relation.ReflTransGen.single h').trans ih
  · intro h
    induction h with
    | refl => rfl
    | tail _ ha hr => exact Reachable.trans hr ⟨Walk.cons ha Walk.nil⟩

/--
theorem `reachable_eq_reflTransGen` / 定理 `reachable_eq_reflTransGen`

English:
theorem reachable_eq_reflTransGen
  statement: G.Reachable = Relation.ReflTransGen G.Adj
  proof: by
  ext
  exact reachable_iff_reflTransGen ..

中文:
定理 reachable_eq_reflTransGen
  结论: G.Reachable = Relation.ReflTransGen G.Adj
  证明: by
  ext
  exact reachable_iff_reflTransGen ..

Depends on / 依赖: reachable_iff_reflTransGen
-/
theorem reachable_eq_reflTransGen : G.Reachable = Relation.ReflTransGen G.Adj := by
  ext
  exact reachable_iff_reflTransGen ..

/--
theorem `reachable_fromEdgeSet_eq_reflTransGen_toRel` / 定理 `reachable_fromEdgeSet_eq_reflTransGen_toRel`

English:
theorem reachable_fromEdgeSet_eq_reflTransGen_toRel
  given: {s : Set (Sym2 V)}
  proof: by
  rw [reachable_eq_reflTransGen]; rw [← Relation.transGen_reflGen]; rw [← Relation.transGen_reflGen]
  congr 1
  ext
  simpa [Relation.reflGen_iff] using by tauto

中文:
定理 reachable_fromEdgeSet_eq_reflTransGen_toRel
  条件: {s : Set (Sym2 V)}
  证明: by
  rw [reachable_eq_reflTransGen]; rw [← Relation.transGen_reflGen]; rw [← Relation.transGen_reflGen]
  congr 1
  ext
  simpa [Relation.reflGen_iff] using by tauto

Depends on / 依赖: Relation, Relation.reflGen_iff, Relation.transGen_reflGen, reachable_eq_reflTransGen, reflGen_iff, transGen_reflGen
-/
theorem reachable_fromEdgeSet_eq_reflTransGen_toRel {s : Set (Sym2 V)} :
    (fromEdgeSet s).Reachable = Relation.ReflTransGen (Sym2.ToRel s) := by
  rw [reachable_eq_reflTransGen]; rw [← Relation.transGen_reflGen]; rw [← Relation.transGen_reflGen]
  congr 1
  ext
  simpa [Relation.reflGen_iff] using by tauto

/--
theorem `reachable_fromEdgeSet_fromRel_eq_reflTransGen` / 定理 `reachable_fromEdgeSet_fromRel_eq_reflTransGen`

English:
theorem reachable_fromEdgeSet_fromRel_eq_reflTransGen
  given: {r : V -> V -> Prop} (sym : Std.Symm r)
  proof: reachable_fromEdgeSet_eq_reflTransGen_toRel

中文:
定理 reachable_fromEdgeSet_fromRel_eq_reflTransGen
  条件: {r : V -> V -> 命题} (sym : Std.Symm r)
  证明: reachable_fromEdgeSet_eq_reflTransGen_toRel

Depends on / 依赖: reachable_fromEdgeSet_eq_reflTransGen_toRel
-/
theorem reachable_fromEdgeSet_fromRel_eq_reflTransGen {r : V -> V -> Prop} (sym : Std.Symm r) :
    (fromEdgeSet <| Sym2.fromRel sym).Reachable = Relation.ReflTransGen r :=
  reachable_fromEdgeSet_eq_reflTransGen_toRel

/--
theorem `Reachable.map` / 定理 `Reachable.map`

English:
theorem Reachable.map
  statement: {u v : V} {G : SimpleGraph V} {G' : SimpleGraph V'} (f : G ->g G')
  proof: h.elim fun p => ⟨p.map f⟩

@[gcongr, mono]

中文:
定理 Reachable.map
  结论: {u v : V} {G : SimpleGraph V} {G' : SimpleGraph V'} (f : G ->g G')
  证明: h.elim fun p => ⟨p.map f⟩

@[gcongr, mono]
-/
protected theorem Reachable.map {u v : V} {G : SimpleGraph V} {G' : SimpleGraph V'} (f : G ->g G')
    (h : G.Reachable u v) : G'.Reachable (f u) (f v) :=
  h.elim fun p => ⟨p.map f⟩

@[gcongr, mono]
/--
lemma `Reachable.mono` / 引理 `Reachable.mono`

English:
lemma Reachable.mono
  statement: {u v : V} {G G' : SimpleGraph V}
  proof: Guv.map (.ofLE h)

@[gcongr, mono]

中文:
引理 Reachable.mono
  结论: {u v : V} {G G' : SimpleGraph V}
  证明: Guv.map (.ofLE h)

@[gcongr, mono]
-/
protected lemma Reachable.mono {u v : V} {G G' : SimpleGraph V}
    (h : G <= G') (Guv : G.Reachable u v) : G'.Reachable u v := Guv.map (.ofLE h)

@[gcongr, mono]
/--
theorem `Reachable.mono'` / 定理 `Reachable.mono'`

English:
theorem Reachable.mono'
  given: {G G' : SimpleGraph V} (h : G <= G')
  statement: G.Reachable <= G'.Reachable
  proof: fun _ _ => Reachable.mono h

中文:
定理 Reachable.mono'
  条件: {G G' : SimpleGraph V} (h : G <= G')
  结论: G.Reachable <= G'.Reachable
  证明: fun _ _ => Reachable.mono h

Depends on / 依赖: Reachable, Reachable.mono
-/
theorem Reachable.mono' {G G' : SimpleGraph V} (h : G <= G') : G.Reachable <= G'.Reachable :=
  fun _ _ => Reachable.mono h

/--
theorem `Reachable.exists_isPath` / 定理 `Reachable.exists_isPath`

English:
theorem Reachable.exists_isPath
  given: {u v} (hr : G.Reachable u v)
  statement: exists p : G.Walk u v, p.IsPath
  proof: by
  classical
  obtain ⟨W⟩ := hr
  exact ⟨_, Path.isPath W.toPath⟩

中文:
定理 Reachable.exists_isPath
  条件: {u v} (hr : G.Reachable u v)
  结论: 存在 p : G.Walk u v, p.IsPath
  证明: by
  classical
  obtain ⟨W⟩ := hr
  exact ⟨_, Path.isPath W.toPath⟩

Depends on / 依赖: Path.isPath, W.toPath, classical, isPath, toPath
-/
theorem Reachable.exists_isPath {u v} (hr : G.Reachable u v) : exists p : G.Walk u v, p.IsPath := by
  classical
  obtain ⟨W⟩ := hr
  exact ⟨_, Path.isPath W.toPath⟩

/--
theorem `Iso.reachable_iff` / 定理 `Iso.reachable_iff`

English:
theorem Iso.reachable_iff
  given: {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u v : V}
  proof: ⟨fun r => φ.left_inv u ▸ φ.left_inv v ▸ r.map φ.symm.toHom, Reachable.map φ.toHom⟩

中文:
定理 Iso.reachable_iff
  条件: {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u v : V}
  证明: ⟨fun r => φ.left_inv u ▸ φ.left_inv v ▸ r.map φ.symm.toHom, Reachable.map φ.toHom⟩

Depends on / 依赖: Reachable, Reachable.map, left_inv, r.map, symm.toHom
-/
theorem Iso.reachable_iff {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u v : V} :
    G'.Reachable (φ u) (φ v) ↔ G.Reachable u v :=
  ⟨fun r => φ.left_inv u ▸ φ.left_inv v ▸ r.map φ.symm.toHom, Reachable.map φ.toHom⟩

/--
theorem `Iso.symm_apply_reachable` / 定理 `Iso.symm_apply_reachable`

English:
theorem Iso.symm_apply_reachable
  statement: {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u : V}
  proof: by
  rw [← Iso.reachable_iff]; rw [RelIso.apply_symm_apply]

中文:
定理 Iso.symm_apply_reachable
  结论: {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u : V}
  证明: by
  rw [← Iso.reachable_iff]; rw [RelIso.apply_symm_apply]

Depends on / 依赖: Iso.reachable_iff, RelIso, RelIso.apply_symm_apply, apply_symm_apply, reachable_iff
-/
theorem Iso.symm_apply_reachable {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u : V}
    {v : V'} : G.Reachable (φ.symm v) u ↔ G'.Reachable v (φ u) := by
  rw [← Iso.reachable_iff]; rw [RelIso.apply_symm_apply]

/--
lemma `Reachable.mem_subgraphVerts` / 引理 `Reachable.mem_subgraphVerts`

English:
lemma Reachable.mem_subgraphVerts
  statement: {u v} {H : G.Subgraph} (hr : G.Reachable u v)
  proof: by
  let rec aux {v' : V} (hv' : v' in H.verts) (p : G.Walk v' v) : v in H.verts := by
    by_cases hnp : p.Nil
    · exact hnp.eq ▸ hv'
    exact aux (H.edge_vert (h _ hv' _ (Walk.adj_snd hnp)).symm) p.tail
  termination_by p.length
  decreasing_by {
    rw [← Walk.length_tail_add_one hnp]
    lia


中文:
引理 Reachable.mem_subgraphVerts
  结论: {u v} {H : G.Subgraph} (hr : G.Reachable u v)
  证明: by
  let rec aux {v' : V} (hv' : v' in H.verts) (p : G.Walk v' v) : v in H.verts := by
    by_cases hnp : p.Nil
    · exact hnp.eq ▸ hv'
    exact aux (H.edge_vert (h _ hv' _ (Walk.adj_snd hnp)).symm) p.tail
  termination_by p.length
  decreasing_by {
    rw [← Walk.length_tail_add_one hnp]
    lia


Depends on / 依赖: G.Walk, H.edge_vert, H.verts, Walk.adj_snd, Walk.length_tail_add_one, adj_snd, decreasing_by, edge_vert, hnp.eq, hr.some, length, length_tail_add_one, p.Nil, p.length, p.tail, termination_by
-/
lemma Reachable.mem_subgraphVerts {u v} {H : G.Subgraph} (hr : G.Reachable u v)
    (h : forall v in H.verts, forall w, G.Adj v w -> H.Adj v w)
    (hu : u in H.verts) : v in H.verts := by
  let rec aux {v' : V} (hv' : v' in H.verts) (p : G.Walk v' v) : v in H.verts := by
    by_cases hnp : p.Nil
    · exact hnp.eq ▸ hv'
    exact aux (H.edge_vert (h _ hv' _ (Walk.adj_snd hnp)).symm) p.tail
  termination_by p.length
  decreasing_by {
    rw [← Walk.length_tail_add_one hnp]
    lia
  }
  exact aux hu hr.some

variable (G)

/--
theorem `reachable_is_equivalence` / 定理 `reachable_is_equivalence`

English:
theorem reachable_is_equivalence
  statement: Equivalence G.Reachable
  proof: Equivalence.mk (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)

中文:
定理 reachable_is_equivalence
  结论: Equivalence G.Reachable
  证明: Equivalence.mk (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)

Depends on / 依赖: Equivalence, Equivalence.mk, Reachable, Reachable.refl, Reachable.symm, Reachable.trans
-/
theorem reachable_is_equivalence : Equivalence G.Reachable :=
  Equivalence.mk (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)

/-- Distinct vertices are not reachable in the empty graph. -/
@[simp]
/--
lemma `reachable_bot` / 引理 `reachable_bot`

English:
lemma reachable_bot
  given: {u v : V}
  statement: (⊥ : SimpleGraph V).Reachable u v ↔ u = v
  proof: ⟨fun h => h.elim fun p => match p with | .nil => rfl, fun h => h ▸ .rfl⟩

中文:
引理 reachable_bot
  条件: {u v : V}
  结论: (⊥ : SimpleGraph V).Reachable u v ↔ u = v
  证明: ⟨fun h => h.elim fun p => match p with | .nil => rfl, fun h => h ▸ .rfl⟩

Depends on / 依赖: h.elim
-/
lemma reachable_bot {u v : V} : (⊥ : SimpleGraph V).Reachable u v ↔ u = v :=
  ⟨fun h => h.elim fun p => match p with | .nil => rfl, fun h => h ▸ .rfl⟩

/--
lemma `reachable_top` / 引理 `reachable_top`

English:
lemma reachable_top
  given: {u v : V}
  statement: (completeGraph V).Reachable u v
  proof: by
  obtain rfl | huv := eq_or_ne u v
  · simp
  · exact ⟨.cons huv .nil⟩

@[nontriviality]

中文:
引理 reachable_top
  条件: {u v : V}
  结论: (completeGraph V).Reachable u v
  证明: by
  obtain rfl | huv := eq_or_ne u v
  · simp
  · exact ⟨.cons huv .nil⟩

@[nontriviality]
-/
@[simp] lemma reachable_top {u v : V} : (completeGraph V).Reachable u v := by
  obtain rfl | huv := eq_or_ne u v
  · simp
  · exact ⟨.cons huv .nil⟩

@[nontriviality]
/--
lemma `Reachable.of_subsingleton` / 引理 `Reachable.of_subsingleton`

English:
lemma Reachable.of_subsingleton
  given: {G : SimpleGraph V} [Subsingleton V] {u v : V}
  proof: by
  rw [Subsingleton.allEq u v]

中文:
引理 Reachable.of_subsingleton
  条件: {G : SimpleGraph V} [Subsingleton V] {u v : V}
  证明: by
  rw [Subsingleton.allEq u v]

Depends on / 依赖: Subsingleton, Subsingleton.allEq
-/
lemma Reachable.of_subsingleton {G : SimpleGraph V} [Subsingleton V] {u v : V} :
    G.Reachable u v := by
  rw [Subsingleton.allEq u v]

/--
lemma `Reachable.nonempty_neighborSet_left` / 引理 `Reachable.nonempty_neighborSet_left`

English:
lemma Reachable.nonempty_neighborSet_left
  statement: {G : SimpleGraph V} {u v : V} (huv : u != v)
  proof: by
  obtain ⟨_ | @⟨u, x, v, hadj, w'⟩⟩ := hreach
  · contradiction
  · exact ⟨x, hadj⟩

中文:
引理 Reachable.nonempty_neighborSet_left
  结论: {G : SimpleGraph V} {u v : V} (huv : u != v)
  证明: by
  obtain ⟨_ | @⟨u, x, v, hadj, w'⟩⟩ := hreach
  · contradiction
  · exact ⟨x, hadj⟩

Depends on / 依赖: hreach
-/
lemma Reachable.nonempty_neighborSet_left {G : SimpleGraph V} {u v : V} (huv : u != v)
    (hreach : G.Reachable u v) : (G.neighborSet u).Nonempty := by
  obtain ⟨_ | @⟨u, x, v, hadj, w'⟩⟩ := hreach
  · contradiction
  · exact ⟨x, hadj⟩

/--
lemma `Reachable.nonempty_neighborSet_right` / 引理 `Reachable.nonempty_neighborSet_right`

English:
lemma Reachable.nonempty_neighborSet_right
  statement: {G : SimpleGraph V} {u v : V} (huv : u != v)
  proof: hreach.symm.nonempty_neighborSet_left huv.symm

中文:
引理 Reachable.nonempty_neighborSet_right
  结论: {G : SimpleGraph V} {u v : V} (huv : u != v)
  证明: hreach.symm.nonempty_neighborSet_left huv.symm

Depends on / 依赖: hreach, hreach.symm.nonempty_neighborSet_left, huv.symm, nonempty_neighborSet_left
-/
lemma Reachable.nonempty_neighborSet_right {G : SimpleGraph V} {u v : V} (huv : u != v)
    (hreach : G.Reachable u v) : (G.neighborSet v).Nonempty :=
  hreach.symm.nonempty_neighborSet_left huv.symm

/--
lemma `Reachable.degree_pos_left` / 引理 `Reachable.degree_pos_left`

English:
lemma Reachable.degree_pos_left
  statement: {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet u)]
  proof: degree_pos_iff_nonempty.mpr (hreach.nonempty_neighborSet_left huv)

中文:
引理 Reachable.degree_pos_left
  结论: {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet u)]
  证明: degree_pos_iff_nonempty.mpr (hreach.nonempty_neighborSet_left huv)

Depends on / 依赖: degree_pos_iff_nonempty, degree_pos_iff_nonempty.mpr, hreach, hreach.nonempty_neighborSet_left, nonempty_neighborSet_left
-/
lemma Reachable.degree_pos_left {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet u)]
    (huv : u != v) (hreach : G.Reachable u v) : 0 < G.degree u :=
  degree_pos_iff_nonempty.mpr (hreach.nonempty_neighborSet_left huv)

/--
lemma `Reachable.degree_pos_right` / 引理 `Reachable.degree_pos_right`

English:
lemma Reachable.degree_pos_right
  statement: {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet v)]
  proof: hreach.symm.degree_pos_left huv.symm

中文:
引理 Reachable.degree_pos_right
  结论: {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet v)]
  证明: hreach.symm.degree_pos_left huv.symm

Depends on / 依赖: degree_pos_left, hreach, hreach.symm.degree_pos_left, huv.symm
-/
lemma Reachable.degree_pos_right {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet v)]
    (huv : u != v) (hreach : G.Reachable u v) : 0 < G.degree v :=
  hreach.symm.degree_pos_left huv.symm

/--
lemma `Reachable.of_isUniversal` / 引理 `Reachable.of_isUniversal`

English:
lemma Reachable.of_isUniversal
  given: {G : SimpleGraph V} {u : V} (v : V) (h : G.IsUniversal u)
  proof: by
  by_cases! h' : u = v
  · exact h' ▸ Reachable.rfl
  · exact (h h').reachable

中文:
引理 Reachable.of_isUniversal
  条件: {G : SimpleGraph V} {u : V} (v : V) (h : G.IsUniversal u)
  证明: by
  by_cases! h' : u = v
  · exact h' ▸ Reachable.rfl
  · exact (h h').reachable

Depends on / 依赖: Reachable, Reachable.rfl, reachable
-/
lemma Reachable.of_isUniversal {G : SimpleGraph V} {u : V} (v : V) (h : G.IsUniversal u) :
    G.Reachable u v := by
  by_cases! h' : u = v
  · exact h' ▸ Reachable.rfl
  · exact (h h').reachable

/--
lemma `not_reachable_of_neighborSet_left_eq_empty` / 引理 `not_reachable_of_neighborSet_left_eq_empty`

English:
lemma not_reachable_of_neighborSet_left_eq_empty
  statement: {G : SimpleGraph V} {u v : V} (huv : u != v)
  proof: (Reachable.nonempty_neighborSet_left huv).mt (Set.not_nonempty_iff_eq_empty.mpr hu)

中文:
引理 not_reachable_of_neighborSet_left_eq_empty
  结论: {G : SimpleGraph V} {u v : V} (huv : u != v)
  证明: (Reachable.nonempty_neighborSet_left huv).mt (Set.not_nonempty_iff_eq_empty.mpr hu)

Depends on / 依赖: Reachable, Reachable.nonempty_neighborSet_left, Set.not_nonempty_iff_eq_empty.mpr, nonempty_neighborSet_left, not_nonempty_iff_eq_empty
-/
lemma not_reachable_of_neighborSet_left_eq_empty {G : SimpleGraph V} {u v : V} (huv : u != v)
    (hu : G.neighborSet u = ∅) : ¬G.Reachable u v :=
  (Reachable.nonempty_neighborSet_left huv).mt (Set.not_nonempty_iff_eq_empty.mpr hu)

/--
lemma `not_reachable_of_neighborSet_right_eq_empty` / 引理 `not_reachable_of_neighborSet_right_eq_empty`

English:
lemma not_reachable_of_neighborSet_right_eq_empty
  statement: {G : SimpleGraph V} {u v : V} (huv : u != v)
  proof: fun r => not_reachable_of_neighborSet_left_eq_empty huv.symm hv r.symm

中文:
引理 not_reachable_of_neighborSet_right_eq_empty
  结论: {G : SimpleGraph V} {u v : V} (huv : u != v)
  证明: fun r => not_reachable_of_neighborSet_left_eq_empty huv.symm hv r.symm

Depends on / 依赖: huv.symm, not_reachable_of_neighborSet_left_eq_empty, r.symm
-/
lemma not_reachable_of_neighborSet_right_eq_empty {G : SimpleGraph V} {u v : V} (huv : u != v)
    (hv : G.neighborSet v = ∅) : ¬G.Reachable u v :=
  fun r => not_reachable_of_neighborSet_left_eq_empty huv.symm hv r.symm

/--
lemma `not_reachable_of_left_degree_zero` / 引理 `not_reachable_of_left_degree_zero`

English:
lemma not_reachable_of_left_degree_zero
  statement: {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet u)]
  proof: (Reachable.degree_pos_left huv).mt (by simp [hu])

中文:
引理 not_reachable_of_left_degree_zero
  结论: {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet u)]
  证明: (Reachable.degree_pos_left huv).mt (by simp [hu])

Depends on / 依赖: Reachable, Reachable.degree_pos_left, degree_pos_left
-/
lemma not_reachable_of_left_degree_zero {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet u)]
    (huv : u != v) (hu : G.degree u = 0) : ¬G.Reachable u v :=
  (Reachable.degree_pos_left huv).mt (by simp [hu])

/--
lemma `not_reachable_of_right_degree_zero` / 引理 `not_reachable_of_right_degree_zero`

English:
lemma not_reachable_of_right_degree_zero
  statement: {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet v)]
  proof: by
  rw [reachable_comm]
  exact not_reachable_of_left_degree_zero huv.symm hu

中文:
引理 not_reachable_of_right_degree_zero
  结论: {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet v)]
  证明: by
  rw [reachable_comm]
  exact not_reachable_of_left_degree_zero huv.symm hu

Depends on / 依赖: huv.symm, not_reachable_of_left_degree_zero, reachable_comm
-/
lemma not_reachable_of_right_degree_zero {G : SimpleGraph V} {u v : V} [Fintype (G.neighborSet v)]
    (huv : u != v) (hu : G.degree v = 0) : ¬G.Reachable u v := by
  rw [reachable_comm]
  exact not_reachable_of_left_degree_zero huv.symm hu

/-- The equivalence relation on vertices given by `SimpleGraph.Reachable`. -/
@[instance_reducible]
/--
Definition of `reachableSetoid` / `reachableSetoid` 的定义

English:
definition reachableSetoid
  signature: : Setoid V
  body: Setoid.mk _ G.reachable_is_equivalence

中文:
定义 reachableSetoid
  签名: : Setoid V
  定义体: Setoid.mk _ G.reachable_is_equivalence

Depends on / 依赖: G.reachable_is_equivalence, Setoid, Setoid.mk, reachable_is_equivalence
-/
def reachableSetoid : Setoid V := Setoid.mk _ G.reachable_is_equivalence

/--
Definition of `Preconnected` / `Preconnected` 的定义

English:
definition Preconnected
  signature: : Prop
  body: forall u v : V, G.Reachable u v

中文:
定义 Preconnected
  签名: : 命题
  定义体: forall u v : V, G.Reachable u v

Depends on / 依赖: G.Reachable, Reachable
-/
def Preconnected : Prop := forall u v : V, G.Reachable u v

/--
theorem `Preconnected.map` / 定理 `Preconnected.map`

English:
theorem Preconnected.map
  statement: {G : SimpleGraph V} {H : SimpleGraph V'} (f : G ->g H) (hf : Surjective f)
  proof: hf.forall₂.2 fun _ _ => Nonempty.map (Walk.map _) hG _ _

@[gcongr, mono]

中文:
定理 Preconnected.map
  结论: {G : SimpleGraph V} {H : SimpleGraph V'} (f : G ->g H) (hf : Surjective f)
  证明: hf.forall₂.2 fun _ _ => Nonempty.map (Walk.map _) hG _ _

@[gcongr, mono]

Depends on / 依赖: Nonempty, Nonempty.map, Walk.map, hf.forall
-/
theorem Preconnected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G ->g H) (hf : Surjective f)
    (hG : G.Preconnected) : H.Preconnected :=
hf.forall₂.2 fun _ _ => Nonempty.map (Walk.map _) hG _ _

@[gcongr, mono]
/--
lemma `Preconnected.mono` / 引理 `Preconnected.mono`

English:
lemma Preconnected.mono
  given: {G G' : SimpleGraph V} (h : G <= G') (hG : G.Preconnected)
  proof: fun u v => (hG u v).mono h

中文:
引理 Preconnected.mono
  条件: {G G' : SimpleGraph V} (h : G <= G') (hG : G.Preconnected)
  证明: fun u v => (hG u v).mono h
-/
protected lemma Preconnected.mono {G G' : SimpleGraph V} (h : G <= G') (hG : G.Preconnected) :
    G'.Preconnected := fun u v => (hG u v).mono h

/--
lemma `preconnected_iff_reachable_eq_top` / 引理 `preconnected_iff_reachable_eq_top`

English:
lemma preconnected_iff_reachable_eq_top
  statement: G.Preconnected ↔ G.Reachable = ⊤
  proof: by
  aesop (add simp Preconnected)

中文:
引理 preconnected_iff_reachable_eq_top
  结论: G.Preconnected ↔ G.Reachable = ⊤
  证明: by
  aesop (add simp Preconnected)

Depends on / 依赖: Preconnected
-/
lemma preconnected_iff_reachable_eq_top : G.Preconnected ↔ G.Reachable = ⊤ := by
  aesop (add simp Preconnected)

/--
lemma `preconnected_bot_iff_subsingleton` / 引理 `preconnected_bot_iff_subsingleton`

English:
lemma preconnected_bot_iff_subsingleton
  statement: (⊥ : SimpleGraph V).Preconnected ↔ Subsingleton V
  proof: by
  refine ⟨fun h => ?_, fun h => by simp [Preconnected]⟩
  contrapose! h
  simp [nontrivial_iff.mp h, Preconnected, reachable_bot]

中文:
引理 preconnected_bot_iff_subsingleton
  结论: (⊥ : SimpleGraph V).Preconnected ↔ Subsingleton V
  证明: by
  refine ⟨fun h => ?_, fun h => by simp [Preconnected]⟩
  contrapose! h
  simp [nontrivial_iff.mp h, Preconnected, reachable_bot]

Depends on / 依赖: Preconnected, contrapose, nontrivial_iff, nontrivial_iff.mp, reachable_bot
-/
lemma preconnected_bot_iff_subsingleton : (⊥ : SimpleGraph V).Preconnected ↔ Subsingleton V := by
  refine ⟨fun h => ?_, fun h => by simp [Preconnected]⟩
  contrapose! h
  simp [nontrivial_iff.mp h, Preconnected, reachable_bot]

/--
lemma `preconnected_bot` / 引理 `preconnected_bot`

English:
lemma preconnected_bot
  given: [Subsingleton V]
  statement: (⊥ : SimpleGraph V).Preconnected
  proof: preconnected_bot_iff_subsingleton.mpr ‹_›

中文:
引理 preconnected_bot
  条件: [Subsingleton V]
  结论: (⊥ : SimpleGraph V).Preconnected
  证明: preconnected_bot_iff_subsingleton.mpr ‹_›

Depends on / 依赖: preconnected_bot_iff_subsingleton, preconnected_bot_iff_subsingleton.mpr
-/
lemma preconnected_bot [Subsingleton V] : (⊥ : SimpleGraph V).Preconnected :=
  preconnected_bot_iff_subsingleton.mpr ‹_›

/--
lemma `not_preconnected_bot` / 引理 `not_preconnected_bot`

English:
lemma not_preconnected_bot
  given: [Nontrivial V]
  statement: ¬(⊥ : SimpleGraph V).Preconnected
  proof: preconnected_bot_iff_subsingleton.not.mpr not_subsingleton_iff_nontrivial.mpr ‹_›

中文:
引理 not_preconnected_bot
  条件: [Nontrivial V]
  结论: ¬(⊥ : SimpleGraph V).Preconnected
  证明: preconnected_bot_iff_subsingleton.not.mpr not_subsingleton_iff_nontrivial.mpr ‹_›

Depends on / 依赖: not_subsingleton_iff_nontrivial, not_subsingleton_iff_nontrivial.mpr, preconnected_bot_iff_subsingleton, preconnected_bot_iff_subsingleton.not.mpr
-/
lemma not_preconnected_bot [Nontrivial V] : ¬(⊥ : SimpleGraph V).Preconnected :=
preconnected_bot_iff_subsingleton.not.mpr not_subsingleton_iff_nontrivial.mpr ‹_›

/--
lemma `preconnected_top` / 引理 `preconnected_top`

English:
lemma preconnected_top
  statement: (⊤ : SimpleGraph V).Preconnected
  proof: fun x y => by
  if h : x = y then rw [h] else exact Adj.reachable h

@[nontriviality]

中文:
引理 preconnected_top
  结论: (⊤ : SimpleGraph V).Preconnected
  证明: fun x y => by
  if h : x = y then rw [h] else exact Adj.reachable h

@[nontriviality]
-/
@[simp] lemma preconnected_top : (⊤ : SimpleGraph V).Preconnected := fun x y => by
  if h : x = y then rw [h] else exact Adj.reachable h

@[nontriviality]
/--
lemma `Preconnected.of_subsingleton` / 引理 `Preconnected.of_subsingleton`

English:
lemma Preconnected.of_subsingleton
  given: {G : SimpleGraph V} [Subsingleton V]
  statement: G.Preconnected
  proof: fun _ _ => .of_subsingleton

中文:
引理 Preconnected.of_subsingleton
  条件: {G : SimpleGraph V} [Subsingleton V]
  结论: G.Preconnected
  证明: fun _ _ => .of_subsingleton

Depends on / 依赖: of_subsingleton
-/
lemma Preconnected.of_subsingleton {G : SimpleGraph V} [Subsingleton V] : G.Preconnected :=
  fun _ _ => .of_subsingleton

/--
theorem `Iso.preconnected_iff` / 定理 `Iso.preconnected_iff`

English:
theorem Iso.preconnected_iff
  given: {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H)
  proof: ⟨Preconnected.map e.toHom e.toEquiv.surjective,
    Preconnected.map e.symm.toHom e.symm.toEquiv.surjective⟩

@[simp]

中文:
定理 Iso.preconnected_iff
  条件: {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H)
  证明: ⟨Preconnected.map e.toHom e.toEquiv.surjective,
    Preconnected.map e.symm.toHom e.symm.toEquiv.surjective⟩

@[simp]

Depends on / 依赖: Preconnected, Preconnected.map, e.symm.toEquiv.surjective, e.symm.toHom, e.toEquiv.surjective, e.toHom, surjective, toEquiv
-/
theorem Iso.preconnected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Preconnected ↔ H.Preconnected :=
  ⟨Preconnected.map e.toHom e.toEquiv.surjective,
    Preconnected.map e.symm.toHom e.symm.toEquiv.surjective⟩

@[simp]
/--
lemma `Preconnected.support_eq_univ` / 引理 `Preconnected.support_eq_univ`

English:
lemma Preconnected.support_eq_univ
  statement: [Nontrivial V] {G : SimpleGraph V}
  proof: by
  simp only [Set.eq_univ_iff_forall]
  intro v
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨p⟩ := h v w
  cases p with
  | nil => contradiction
  | @cons _ w => exact ⟨w, ‹_›⟩

@[simp]

中文:
引理 Preconnected.support_eq_univ
  结论: [Nontrivial V] {G : SimpleGraph V}
  证明: by
  simp only [Set.eq_univ_iff_forall]
  intro v
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨p⟩ := h v w
  cases p with
  | nil => contradiction
  | @cons _ w => exact ⟨w, ‹_›⟩

@[simp]

Depends on / 依赖: Set.eq_univ_iff_forall, eq_univ_iff_forall, exists_ne
-/
lemma Preconnected.support_eq_univ [Nontrivial V] {G : SimpleGraph V}
    (h : G.Preconnected) : G.support = Set.univ := by
  simp only [Set.eq_univ_iff_forall]
  intro v
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨p⟩ := h v w
  cases p with
  | nil => contradiction
  | @cons _ w => exact ⟨w, ‹_›⟩

@[simp]
/--
lemma `Preconnected.not_isIsolated` / 引理 `Preconnected.not_isIsolated`

English:
lemma Preconnected.not_isIsolated
  given: [Nontrivial V] {G : SimpleGraph V} (hG : G.Preconnected) (v : V)
  proof: by simp [← mem_support_iff_not_isIsolated, hG]

中文:
引理 Preconnected.not_isIsolated
  条件: [Nontrivial V] {G : SimpleGraph V} (hG : G.Preconnected) (v : V)
  证明: by simp [← mem_support_iff_not_isIsolated, hG]

Depends on / 依赖: mem_support_iff_not_isIsolated
-/
lemma Preconnected.not_isIsolated [Nontrivial V] {G : SimpleGraph V} (hG : G.Preconnected) (v : V) :
    ¬ G.IsIsolated v := by simp [← mem_support_iff_not_isIsolated, hG]

/--
lemma `Preconnected.degree_pos_of_nontrivial` / 引理 `Preconnected.degree_pos_of_nontrivial`

English:
lemma Preconnected.degree_pos_of_nontrivial
  statement: [Nontrivial V] {G : SimpleGraph V} (h : G.Preconnected)
  proof: by
  simp [degree_pos_iff_mem_support, h.support_eq_univ]

中文:
引理 Preconnected.degree_pos_of_nontrivial
  结论: [Nontrivial V] {G : SimpleGraph V} (h : G.Preconnected)
  证明: by
  simp [degree_pos_iff_mem_support, h.support_eq_univ]

Depends on / 依赖: degree_pos_iff_mem_support, h.support_eq_univ, support_eq_univ
-/
lemma Preconnected.degree_pos_of_nontrivial [Nontrivial V] {G : SimpleGraph V} (h : G.Preconnected)
    (v : V) [Fintype (G.neighborSet v)] : 0 < G.degree v := by
  simp [degree_pos_iff_mem_support, h.support_eq_univ]

/--
lemma `Preconnected.minDegree_pos_of_nontrivial` / 引理 `Preconnected.minDegree_pos_of_nontrivial`

English:
lemma Preconnected.minDegree_pos_of_nontrivial
  statement: [Nontrivial V] [Fintype V] {G : SimpleGraph V}
  proof: by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  exact h.degree_pos_of_nontrivial v

中文:
引理 Preconnected.minDegree_pos_of_nontrivial
  结论: [Nontrivial V] [Fintype V] {G : SimpleGraph V}
  证明: by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  exact h.degree_pos_of_nontrivial v

Depends on / 依赖: G.exists_minimal_degree_vertex, degree_pos_of_nontrivial, exists_minimal_degree_vertex, h.degree_pos_of_nontrivial
-/
lemma Preconnected.minDegree_pos_of_nontrivial [Nontrivial V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (h : G.Preconnected) : 0 < G.minDegree := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  exact h.degree_pos_of_nontrivial v

/--
lemma `adj_of_mem_walk_support` / 引理 `adj_of_mem_walk_support`

English:
lemma adj_of_mem_walk_support
  statement: {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) {x : V}
  proof: by
  induction p with grind [Walk.nil_iff_support_eq, Walk.cons_tail_support, adj_comm]

中文:
引理 adj_of_mem_walk_support
  结论: {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) {x : V}
  证明: by
  induction p with grind [Walk.nil_iff_support_eq, Walk.cons_tail_support, adj_comm]

Depends on / 依赖: Walk.cons_tail_support, Walk.nil_iff_support_eq, adj_comm, cons_tail_support, nil_iff_support_eq
-/
lemma adj_of_mem_walk_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) {x : V}
    (hx : x in p.support) : exists y in p.support, G.Adj x y := by
  induction p with grind [Walk.nil_iff_support_eq, Walk.cons_tail_support, adj_comm]

/--
lemma `mem_support_of_mem_walk_support` / 引理 `mem_support_of_mem_walk_support`

English:
lemma mem_support_of_mem_walk_support
  statement: {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil)
  proof: by
  obtain ⟨y, hy⟩ := adj_of_mem_walk_support p hp hw
  exact (mem_support G).mpr ⟨y, hy.right⟩

中文:
引理 mem_support_of_mem_walk_support
  结论: {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil)
  证明: by
  obtain ⟨y, hy⟩ := adj_of_mem_walk_support p hp hw
  exact (mem_support G).mpr ⟨y, hy.right⟩

Depends on / 依赖: adj_of_mem_walk_support, hy.right, mem_support
-/
lemma mem_support_of_mem_walk_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil)
    {w : V} (hw : w in p.support) : w in G.support := by
  obtain ⟨y, hy⟩ := adj_of_mem_walk_support p hp hw
  exact (mem_support G).mpr ⟨y, hy.right⟩

/--
lemma `mem_support_of_reachable` / 引理 `mem_support_of_reachable`

English:
lemma mem_support_of_reachable
  given: {G : SimpleGraph V} {u v : V} (huv : u != v) (h : G.Reachable u v)
  proof: by
  let p : G.Walk u v := Classical.choice h
  have hp : ¬p.Nil := Walk.not_nil_of_ne huv
  exact mem_support_of_mem_walk_support p hp p.start_mem_support

中文:
引理 mem_support_of_reachable
  条件: {G : SimpleGraph V} {u v : V} (huv : u != v) (h : G.Reachable u v)
  证明: by
  let p : G.Walk u v := Classical.choice h
  have hp : ¬p.Nil := Walk.not_nil_of_ne huv
  exact mem_support_of_mem_walk_support p hp p.start_mem_support

Depends on / 依赖: Classical, Classical.choice, G.Walk, Walk.not_nil_of_ne, choice, mem_support_of_mem_walk_support, not_nil_of_ne, p.Nil, p.start_mem_support, start_mem_support
-/
lemma mem_support_of_reachable {G : SimpleGraph V} {u v : V} (huv : u != v) (h : G.Reachable u v) :
    u in G.support := by
  let p : G.Walk u v := Classical.choice h
  have hp : ¬p.Nil := Walk.not_nil_of_ne huv
  exact mem_support_of_mem_walk_support p hp p.start_mem_support

/--
theorem `Preconnected.exists_isPath` / 定理 `Preconnected.exists_isPath`

English:
theorem Preconnected.exists_isPath
  given: {G : SimpleGraph V} (h : G.Preconnected) (u v : V)
  proof: (h u v).exists_isPath

中文:
定理 Preconnected.exists_isPath
  条件: {G : SimpleGraph V} (h : G.Preconnected) (u v : V)
  证明: (h u v).exists_isPath

Depends on / 依赖: exists_isPath
-/
theorem Preconnected.exists_isPath {G : SimpleGraph V} (h : G.Preconnected) (u v : V) :
    exists p : G.Walk u v, p.IsPath :=
  (h u v).exists_isPath

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
/--
Definition of `Connected` / `Connected` 的定义

English:
structure Connected
  parameters: : Prop where
  axioms and operations (2):
    - preconnected : G.Preconnected
    - [nonempty : Nonempty V]

中文:
结构 Connected
  参数: : 命题 where
  公理与运算 (2 个):
    - preconnected : G.Preconnected
    - [nonempty : Nonempty V]
-/
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V]

/--
lemma `connected_iff_exists_forall_reachable` / 引理 `connected_iff_exists_forall_reachable`

English:
lemma connected_iff_exists_forall_reachable
  statement: G.Connected ↔ exists v, forall w, G.Reachable v w
  proof: by
  rw [connected_iff]
  constructor
  · rintro ⟨hp, ⟨v⟩⟩
    exact ⟨v, fun w => hp v w⟩
  · rintro ⟨v, h⟩
    exact ⟨fun u w => (h u).symm.trans (h w), ⟨v⟩⟩

中文:
引理 connected_iff_exists_forall_reachable
  结论: G.Connected ↔ 存在 v, 对任意 w, G.Reachable v w
  证明: by
  rw [connected_iff]
  constructor
  · rintro ⟨hp, ⟨v⟩⟩
    exact ⟨v, fun w => hp v w⟩
  · rintro ⟨v, h⟩
    exact ⟨fun u w => (h u).symm.trans (h w), ⟨v⟩⟩

Depends on / 依赖: connected_iff, symm.trans
-/
lemma connected_iff_exists_forall_reachable : G.Connected ↔ exists v, forall w, G.Reachable v w := by
  rw [connected_iff]
  constructor
  · rintro ⟨hp, ⟨v⟩⟩
    exact ⟨v, fun w => hp v w⟩
  · rintro ⟨v, h⟩
    exact ⟨fun u w => (h u).symm.trans (h w), ⟨v⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun G.Connected fun _ => forall u v
  body: ⟨fun h => h.preconnected⟩

中文:
实例 :
  签名: CoeFun G.Connected fun _ => 对任意 u v
  定义体: ⟨fun h => h.preconnected⟩

Depends on / 依赖: h.preconnected, preconnected
-/
instance : CoeFun G.Connected fun _ => forall u v : V, G.Reachable u v := ⟨fun h => h.preconnected⟩

/--
theorem `Connected.map` / 定理 `Connected.map`

English:
theorem Connected.map
  statement: {G : SimpleGraph V} {H : SimpleGraph V'} (f : G ->g H) (hf : Surjective f)
  proof: haveI := hG.nonempty.map f
  ⟨hG.preconnected.map f hf⟩

@[gcongr, mono]

中文:
定理 Connected.map
  结论: {G : SimpleGraph V} {H : SimpleGraph V'} (f : G ->g H) (hf : Surjective f)
  证明: haveI := hG.nonempty.map f
  ⟨hG.preconnected.map f hf⟩

@[gcongr, mono]

Depends on / 依赖: hG.nonempty.map, hG.preconnected.map, nonempty, preconnected
-/
theorem Connected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G ->g H) (hf : Surjective f)
    (hG : G.Connected) : H.Connected :=
  haveI := hG.nonempty.map f
  ⟨hG.preconnected.map f hf⟩

@[gcongr, mono]
/--
lemma `Connected.mono` / 引理 `Connected.mono`

English:
lemma Connected.mono
  statement: {G G' : SimpleGraph V} (h : G <= G')
  proof: hG.preconnected.mono h
  nonempty := hG.nonempty

中文:
引理 Connected.mono
  结论: {G G' : SimpleGraph V} (h : G <= G')
  证明: hG.preconnected.mono h
  nonempty := hG.nonempty
-/
protected lemma Connected.mono {G G' : SimpleGraph V} (h : G <= G')
    (hG : G.Connected) : G'.Connected where
  preconnected := hG.preconnected.mono h
  nonempty := hG.nonempty

/--
theorem `Connected.exists_isPath` / 定理 `Connected.exists_isPath`

English:
theorem Connected.exists_isPath
  given: {G : SimpleGraph V} (h : G.Connected) (u v : V)
  proof: (h u v).exists_isPath

中文:
定理 Connected.exists_isPath
  条件: {G : SimpleGraph V} (h : G.Connected) (u v : V)
  证明: (h u v).exists_isPath

Depends on / 依赖: exists_isPath
-/
theorem Connected.exists_isPath {G : SimpleGraph V} (h : G.Connected) (u v : V) :
    exists p : G.Walk u v, p.IsPath :=
  (h u v).exists_isPath

/--
lemma `connected_bot_iff` / 引理 `connected_bot_iff`

English:
lemma connected_bot_iff
  statement: (⊥ : SimpleGraph V).Connected ↔ Subsingleton V ∧ Nonempty V
  proof: by
  simp [preconnected_bot_iff_subsingleton, connected_iff]

中文:
引理 connected_bot_iff
  结论: (⊥ : SimpleGraph V).Connected ↔ Subsingleton V ∧ Nonempty V
  证明: by
  simp [preconnected_bot_iff_subsingleton, connected_iff]

Depends on / 依赖: connected_iff, preconnected_bot_iff_subsingleton
-/
lemma connected_bot_iff : (⊥ : SimpleGraph V).Connected ↔ Subsingleton V ∧ Nonempty V := by
  simp [preconnected_bot_iff_subsingleton, connected_iff]

/--
lemma `not_connected_bot` / 引理 `not_connected_bot`

English:
lemma not_connected_bot
  given: [Nontrivial V]
  statement: ¬(⊥ : SimpleGraph V).Connected
  proof: by
  simp [not_preconnected_bot, connected_iff]

中文:
引理 not_connected_bot
  条件: [Nontrivial V]
  结论: ¬(⊥ : SimpleGraph V).Connected
  证明: by
  simp [not_preconnected_bot, connected_iff]

Depends on / 依赖: connected_iff, not_preconnected_bot
-/
lemma not_connected_bot [Nontrivial V] : ¬(⊥ : SimpleGraph V).Connected := by
  simp [not_preconnected_bot, connected_iff]

/--
lemma `connected_top_iff` / 引理 `connected_top_iff`

English:
lemma connected_top_iff
  statement: (completeGraph V).Connected ↔ Nonempty V
  proof: by simp [connected_iff]

中文:
引理 connected_top_iff
  结论: (completeGraph V).Connected ↔ Nonempty V
  证明: by simp [connected_iff]

Depends on / 依赖: connected_iff
-/
lemma connected_top_iff : (completeGraph V).Connected ↔ Nonempty V := by simp [connected_iff]

/--
lemma `connected_top` / 引理 `connected_top`

English:
lemma connected_top
  given: [Nonempty V]
  statement: (completeGraph V).Connected
  proof: by rwa [connected_top_iff]

@[nontriviality]

中文:
引理 connected_top
  条件: [Nonempty V]
  结论: (completeGraph V).Connected
  证明: by rwa [connected_top_iff]

@[nontriviality]
-/
@[simp] lemma connected_top [Nonempty V] : (completeGraph V).Connected := by rwa [connected_top_iff]

@[nontriviality]
/--
lemma `Connected.of_subsingleton` / 引理 `Connected.of_subsingleton`

English:
lemma Connected.of_subsingleton
  given: {G : SimpleGraph V} [Nonempty V] [Subsingleton V]
  proof: ⟨.of_subsingleton⟩

中文:
引理 Connected.of_subsingleton
  条件: {G : SimpleGraph V} [Nonempty V] [Subsingleton V]
  证明: ⟨.of_subsingleton⟩

Depends on / 依赖: of_subsingleton
-/
lemma Connected.of_subsingleton {G : SimpleGraph V} [Nonempty V] [Subsingleton V] :
    G.Connected :=
  ⟨.of_subsingleton⟩

/--
theorem `Iso.connected_iff` / 定理 `Iso.connected_iff`

English:
theorem Iso.connected_iff
  given: {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H)
  proof: ⟨Connected.map e.toHom e.toEquiv.surjective, Connected.map e.symm.toHom e.symm.toEquiv.surjective⟩

中文:
定理 Iso.connected_iff
  条件: {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H)
  证明: ⟨Connected.map e.toHom e.toEquiv.surjective, Connected.map e.symm.toHom e.symm.toEquiv.surjective⟩

Depends on / 依赖: Connected, Connected.map, e.symm.toEquiv.surjective, e.symm.toHom, e.toEquiv.surjective, e.toHom, surjective, toEquiv
-/
theorem Iso.connected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Connected ↔ H.Connected :=
  ⟨Connected.map e.toHom e.toEquiv.surjective, Connected.map e.symm.toHom e.symm.toEquiv.surjective⟩

/--
lemma `reachable_or_compl_adj` / 引理 `reachable_or_compl_adj`

English:
lemma reachable_or_compl_adj
  given: (u v : V)
  statement: G.Reachable u v ∨ Gᶜ.Adj u v
  proof: or_iff_not_imp_left.mpr fun huv => ⟨fun heq => huv heq ▸ Reachable.rfl, mt Adj.reachable huv⟩

中文:
引理 reachable_or_compl_adj
  条件: (u v : V)
  结论: G.Reachable u v ∨ Gᶜ.Adj u v
  证明: or_iff_not_imp_left.mpr fun huv => ⟨fun heq => huv heq ▸ Reachable.rfl, mt Adj.reachable huv⟩

Depends on / 依赖: Adj.reachable, Reachable, Reachable.rfl, or_iff_not_imp_left, or_iff_not_imp_left.mpr, reachable
-/
lemma reachable_or_compl_adj (u v : V) : G.Reachable u v ∨ Gᶜ.Adj u v :=
or_iff_not_imp_left.mpr fun huv => ⟨fun heq => huv heq ▸ Reachable.rfl, mt Adj.reachable huv⟩

/--
theorem `reachable_or_reachable_compl` / 定理 `reachable_or_reachable_compl`

English:
theorem reachable_or_reachable_compl
  given: (u v w : V)
  statement: G.Reachable u v ∨ Gᶜ.Reachable u w
  proof: by
  refine or_iff_not_imp_left.mpr fun huv => ?_
  by_cases huw : G.Reachable u w
.resolve_left huv · have huv' := G.reachable_or_compl_adj ..
.resolve_left fun hvw => huv huw.trans hvw.symm have hvw' := G.reachable_or_compl_adj ..
    exact huv'.reachable.trans hvw'.reachable
.reachable .resolve_l

中文:
定理 reachable_or_reachable_compl
  条件: (u v w : V)
  结论: G.Reachable u v ∨ Gᶜ.Reachable u w
  证明: by
  refine or_iff_not_imp_left.mpr fun huv => ?_
  by_cases huw : G.Reachable u w
.resolve_left huv · have huv' := G.reachable_or_compl_adj ..
.resolve_left fun hvw => huv huw.trans hvw.symm have hvw' := G.reachable_or_compl_adj ..
    exact huv'.reachable.trans hvw'.reachable
.reachable .resolve_l

Depends on / 依赖: G.Reachable, G.reachable_or_compl_adj, Reachable, huw.trans, hvw.symm, or_iff_not_imp_left, or_iff_not_imp_left.mpr, reachable, reachable.trans, reachable_or_compl_adj, resolve_left
-/
theorem reachable_or_reachable_compl (u v w : V) : G.Reachable u v ∨ Gᶜ.Reachable u w := by
  refine or_iff_not_imp_left.mpr fun huv => ?_
  by_cases huw : G.Reachable u w
.resolve_left huv · have huv' := G.reachable_or_compl_adj ..
.resolve_left fun hvw => huv huw.trans hvw.symm have hvw' := G.reachable_or_compl_adj ..
    exact huv'.reachable.trans hvw'.reachable
.reachable .resolve_left huw exact G.reachable_or_compl_adj ..

/--
theorem `connected_or_preconnected_compl` / 定理 `connected_or_preconnected_compl`

English:
theorem connected_or_preconnected_compl
  statement: G.Connected ∨ Gᶜ.Preconnected
  proof: by
  rw [or_iff_not_imp_left]; rw [G.connected_iff_exists_forall_reachable]
  intro h u v
  push Not at h
  have ⟨w, huw⟩ := h u
.resolve_left huw exact reachable_or_reachable_compl ..

中文:
定理 connected_or_preconnected_compl
  结论: G.Connected ∨ Gᶜ.Preconnected
  证明: by
  rw [or_iff_not_imp_left]; rw [G.connected_iff_exists_forall_reachable]
  intro h u v
  push Not at h
  have ⟨w, huw⟩ := h u
.resolve_left huw exact reachable_or_reachable_compl ..

Depends on / 依赖: G.connected_iff_exists_forall_reachable, connected_iff_exists_forall_reachable, or_iff_not_imp_left, reachable_or_reachable_compl, resolve_left
-/
theorem connected_or_preconnected_compl : G.Connected ∨ Gᶜ.Preconnected := by
  rw [or_iff_not_imp_left]; rw [G.connected_iff_exists_forall_reachable]
  intro h u v
  push Not at h
  have ⟨w, huw⟩ := h u
.resolve_left huw exact reachable_or_reachable_compl ..

/--
theorem `connected_or_connected_compl` / 定理 `connected_or_connected_compl`

English:
theorem connected_or_connected_compl
  given: [Nonempty V]
  statement: G.Connected ∨ Gᶜ.Connected
  proof: G.connected_or_preconnected_compl.elim .inl (.inr ⟨·⟩)

中文:
定理 connected_or_connected_compl
  条件: [Nonempty V]
  结论: G.Connected ∨ Gᶜ.Connected
  证明: G.connected_or_preconnected_compl.elim .inl (.inr ⟨·⟩)

Depends on / 依赖: G.connected_or_preconnected_compl.elim, connected_or_preconnected_compl
-/
theorem connected_or_connected_compl [Nonempty V] : G.Connected ∨ Gᶜ.Connected :=
  G.connected_or_preconnected_compl.elim .inl (.inr ⟨·⟩)

variable {G v} in
/--
lemma `Connected.of_isUniversal` / 引理 `Connected.of_isUniversal`

English:
lemma Connected.of_isUniversal
  given: (h : G.IsUniversal v)
  statement: G.Connected
  proof: by
.mpr ⟨fun u w => ?_, ⟨v⟩⟩ refine connected_iff _
  exact (Reachable.of_isUniversal u h).symm.trans (Reachable.of_isUniversal w h)

中文:
引理 Connected.of_isUniversal
  条件: (h : G.IsUniversal v)
  结论: G.Connected
  证明: by
.mpr ⟨fun u w => ?_, ⟨v⟩⟩ refine connected_iff _
  exact (Reachable.of_isUniversal u h).symm.trans (Reachable.of_isUniversal w h)

Depends on / 依赖: Reachable, Reachable.of_isUniversal, connected_iff, of_isUniversal, symm.trans
-/
lemma Connected.of_isUniversal (h : G.IsUniversal v) : G.Connected := by
.mpr ⟨fun u w => ?_, ⟨v⟩⟩ refine connected_iff _
  exact (Reachable.of_isUniversal u h).symm.trans (Reachable.of_isUniversal w h)

/--
Definition of `ConnectedComponent` / `ConnectedComponent` 的定义

English:
definition ConnectedComponent
  body: Quot G.Reachable

中文:
定义 ConnectedComponent
  定义体: Quot G.Reachable

Depends on / 依赖: G.Reachable, Reachable
-/
def ConnectedComponent := Quot G.Reachable

/--
Definition of `connectedComponentMk` / `connectedComponentMk` 的定义

English:
definition connectedComponentMk
  signature: (v : V)
  body: Quot.mk G.Reachable v

中文:
定义 connectedComponentMk
  签名: (v : V)
  定义体: Quot.mk G.Reachable v

Depends on / 依赖: G.Reachable, Quot.mk, Reachable
-/
def connectedComponentMk (v : V) : G.ConnectedComponent := Quot.mk G.Reachable v

variable {G G' G''}

namespace ConnectedComponent

@[simps]
/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: [Inhabited V]
  body: ⟨G.connectedComponentMk default⟩

中文:
实例 inhabited
  签名: [Inhabited V]
  定义体: ⟨G.connectedComponentMk default⟩

Depends on / 依赖: G.connectedComponentMk, connectedComponentMk
-/
instance inhabited [Inhabited V] : Inhabited G.ConnectedComponent :=
  ⟨G.connectedComponentMk default⟩

/--
Instance `isEmpty` / 实例 `isEmpty`

English:
instance isEmpty
  signature: [IsEmpty V]
  body: Quot.instIsEmpty

中文:
实例 isEmpty
  签名: [IsEmpty V]
  定义体: Quot.instIsEmpty

Depends on / 依赖: Quot.instIsEmpty, instIsEmpty
-/
instance isEmpty [IsEmpty V] : IsEmpty G.ConnectedComponent := Quot.instIsEmpty
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: V] : Subsingleton G.ConnectedComponent
  body: Quot.Subsingleton

中文:
实例 [Subsingleton
  签名: V] : Subsingleton G.ConnectedComponent
  定义体: Quot.Subsingleton

Depends on / 依赖: Quot.Subsingleton, Subsingleton
-/
instance [Subsingleton V] : Subsingleton G.ConnectedComponent := Quot.Subsingleton
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: V] : Unique G.ConnectedComponent
  body: Quot.instUnique

中文:
实例 [Unique
  签名: V] : Unique G.ConnectedComponent
  定义体: Quot.instUnique

Depends on / 依赖: Quot.instUnique, instUnique
-/
instance [Unique V] : Unique G.ConnectedComponent := Quot.instUnique
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: V] : Nonempty G.ConnectedComponent
  body: Nonempty.map G.connectedComponentMk ‹_›

中文:
实例 [Nonempty
  签名: V] : Nonempty G.ConnectedComponent
  定义体: Nonempty.map G.connectedComponentMk ‹_›

Depends on / 依赖: G.connectedComponentMk, Nonempty, Nonempty.map, connectedComponentMk
-/
instance [Nonempty V] : Nonempty G.ConnectedComponent := Nonempty.map G.connectedComponentMk ‹_›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: V] : Finite G.ConnectedComponent
  body: Quot.finite _

@[elab_as_elim]

中文:
实例 [Finite
  签名: V] : Finite G.ConnectedComponent
  定义体: Quot.finite _

@[elab_as_elim]

Depends on / 依赖: Quot.finite, finite
-/
instance [Finite V] : Finite G.ConnectedComponent := Quot.finite _

@[elab_as_elim]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  statement: {β : G.ConnectedComponent -> Prop}
  proof: Quot.ind h c

@[elab_as_elim]

中文:
定理 ind
  结论: {β : G.ConnectedComponent -> 命题}
  证明: Quot.ind h c

@[elab_as_elim]
-/
protected theorem ind {β : G.ConnectedComponent -> Prop}
    (h : forall v : V, β (G.connectedComponentMk v)) (c : G.ConnectedComponent) : β c :=
  Quot.ind h c

@[elab_as_elim]
/--
theorem `ind₂` / 定理 `ind₂`

English:
theorem ind₂
  statement: {β : G.ConnectedComponent -> G.ConnectedComponent -> Prop}
  proof: Quot.induction_on₂ c d h

中文:
定理 ind₂
  结论: {β : G.ConnectedComponent -> G.ConnectedComponent -> 命题}
  证明: Quot.induction_on₂ c d h
-/
protected theorem ind₂ {β : G.ConnectedComponent -> G.ConnectedComponent -> Prop}
    (h : forall v w : V, β (G.connectedComponentMk v) (G.connectedComponentMk w))
    (c d : G.ConnectedComponent) : β c d :=
  Quot.induction_on₂ c d h

/--
theorem `sound` / 定理 `sound`

English:
theorem sound
  given: {v w : V}
  proof: Quot.sound

中文:
定理 sound
  条件: {v w : V}
  证明: Quot.sound
-/
protected theorem sound {v w : V} :
    G.Reachable v w -> G.connectedComponentMk v = G.connectedComponentMk w :=
  Quot.sound

/--
theorem `exact` / 定理 `exact`

English:
theorem exact
  given: {v w : V}
  proof: @Quotient.exact _ G.reachableSetoid _ _

@[simp]

中文:
定理 exact
  条件: {v w : V}
  证明: @Quotient.exact _ G.reachableSetoid _ _

@[simp]
-/
protected theorem exact {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w -> G.Reachable v w :=
  @Quotient.exact _ G.reachableSetoid _ _

@[simp]
/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {v w : V}
  proof: @Quotient.eq' _ G.reachableSetoid _ _

中文:
定理 eq
  条件: {v w : V}
  证明: @Quotient.eq' _ G.reachableSetoid _ _
-/
protected theorem eq {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w :=
  @Quotient.eq' _ G.reachableSetoid _ _

/--
theorem `connectedComponentMk_eq_of_adj` / 定理 `connectedComponentMk_eq_of_adj`

English:
theorem connectedComponentMk_eq_of_adj
  given: {v w : V} (a : G.Adj v w)
  proof: ConnectedComponent.sound a.reachable

中文:
定理 connectedComponentMk_eq_of_adj
  条件: {v w : V} (a : G.Adj v w)
  证明: ConnectedComponent.sound a.reachable

Depends on / 依赖: ConnectedComponent, ConnectedComponent.sound, a.reachable, reachable
-/
theorem connectedComponentMk_eq_of_adj {v w : V} (a : G.Adj v w) :
    G.connectedComponentMk v = G.connectedComponentMk w :=
  ConnectedComponent.sound a.reachable

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {β : Sort*} (f : V -> β)
  body: Quot.lift f fun v w (h' : G.Reachable v w) => h'.elim_path fun hp => h v w hp hp.2

@[simp]

中文:
定义 lift
  签名: {β : Sort*} (f : V -> β)
  定义体: Quot.lift f fun v w (h' : G.Reachable v w) => h'.elim_path fun hp => h v w hp hp.2

@[simp]
-/
protected def lift {β : Sort*} (f : V -> β)
    (h : forall (v w : V) (p : G.Walk v w), p.IsPath -> f v = f w) : G.ConnectedComponent -> β :=
  Quot.lift f fun v w (h' : G.Reachable v w) => h'.elim_path fun hp => h v w hp hp.2

@[simp]
/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  statement: {β : Sort*} {f : V -> β}
  proof: rfl

中文:
定理 lift_mk
  结论: {β : Sort*} {f : V -> β}
  证明: rfl
-/
protected theorem lift_mk {β : Sort*} {f : V -> β}
    {h : forall (v w : V) (p : G.Walk v w), p.IsPath -> f v = f w} {v : V} :
    ConnectedComponent.lift f h (G.connectedComponentMk v) = f v :=
  rfl

/--
theorem `«exists»` / 定理 `«exists»`

English:
theorem «exists»
  given: {p : G.ConnectedComponent -> Prop}
  proof: Quot.mk_surjective.exists

中文:
定理 «exists»
  条件: {p : G.ConnectedComponent -> 命题}
  证明: Quot.mk_surjective.exists
-/
protected theorem «exists» {p : G.ConnectedComponent -> Prop} :
    (exists c : G.ConnectedComponent, p c) ↔ exists v, p (G.connectedComponentMk v) :=
  Quot.mk_surjective.exists

/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: {p : G.ConnectedComponent -> Prop}
  proof: Quot.mk_surjective.forall

中文:
定理 «forall»
  条件: {p : G.ConnectedComponent -> 命题}
  证明: Quot.mk_surjective.forall
-/
protected theorem «forall» {p : G.ConnectedComponent -> Prop} :
    (forall c : G.ConnectedComponent, p c) ↔ forall v, p (G.connectedComponentMk v) :=
  Quot.mk_surjective.forall

/--
theorem `_root_.SimpleGraph.Preconnected.subsingleton_connectedComponent` / 定理 `_root_.SimpleGraph.Preconnected.subsingleton_connectedComponent`

English:
theorem _root_.SimpleGraph.Preconnected.subsingleton_connectedComponent
  given: (h : G.Preconnected)
  proof: ⟨ConnectedComponent.ind₂ fun v w => ConnectedComponent.sound (h v w)⟩

中文:
定理 _root_.SimpleGraph.Preconnected.subsingleton_connectedComponent
  条件: (h : G.Preconnected)
  证明: ⟨ConnectedComponent.ind₂ fun v w => ConnectedComponent.sound (h v w)⟩

Depends on / 依赖: ConnectedComponent, ConnectedComponent.ind, ConnectedComponent.sound
-/
theorem _root_.SimpleGraph.Preconnected.subsingleton_connectedComponent (h : G.Preconnected) :
    Subsingleton G.ConnectedComponent :=
  ⟨ConnectedComponent.ind₂ fun v w => ConnectedComponent.sound (h v w)⟩

/-- This is `Quot.recOn` specialized to connected components.
For convenience, it strengthens the assumptions in the hypothesis
to provide a path between the vertices. -/
@[elab_as_elim]
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  body: Quot.recOn c f fun u v r => r.elim_path fun p => h u v p p.2

中文:
定义 recOn
  定义体: Quot.recOn c f fun u v r => r.elim_path fun p => h u v p p.2

Depends on / 依赖: Quot.recOn, elim_path, r.elim_path
-/
def recOn
    {motive : G.ConnectedComponent -> Sort*}
    (c : G.ConnectedComponent)
    (f : (v : V) -> motive (G.connectedComponentMk v))
    (h : forall (u v : V) (p : G.Walk u v) (_ : p.IsPath),
      ConnectedComponent.sound p.reachable ▸ f u = f v) :
    motive c :=
  Quot.recOn c f fun u v r => r.elim_path fun p => h u v p p.2

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (φ : G ->g G') (C : G.ConnectedComponent)
  body: C.lift (fun v => G'.connectedComponentMk (φ v)) fun _ _ p _ =>
    ConnectedComponent.eq.mpr (p.map φ).reachable

@[simp]

中文:
定义 map
  签名: (φ : G ->g G') (C : G.ConnectedComponent)
  定义体: C.lift (fun v => G'.connectedComponentMk (φ v)) fun _ _ p _ =>
    ConnectedComponent.eq.mpr (p.map φ).reachable

@[simp]

Depends on / 依赖: C.lift, ConnectedComponent, ConnectedComponent.eq.mpr, connectedComponentMk, p.map, reachable
-/
def map (φ : G ->g G') (C : G.ConnectedComponent) : G'.ConnectedComponent :=
  C.lift (fun v => G'.connectedComponentMk (φ v)) fun _ _ p _ =>
    ConnectedComponent.eq.mpr (p.map φ).reachable

@[simp]
/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: (φ : G ->g G') (v : V)
  proof: rfl

@[simp]

中文:
定理 map_mk
  条件: (φ : G ->g G') (v : V)
  证明: rfl

@[simp]
-/
theorem map_mk (φ : G ->g G') (v : V) :
    (G.connectedComponentMk v).map φ = G'.connectedComponentMk (φ v) :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (C : ConnectedComponent G)
  statement: C.map Hom.id = C
  proof: C.ind (fun _ => rfl)

@[simp]

中文:
定理 map_id
  条件: (C : ConnectedComponent G)
  结论: C.map Hom.id = C
  证明: C.ind (fun _ => rfl)

@[simp]

Depends on / 依赖: C.ind
-/
theorem map_id (C : ConnectedComponent G) : C.map Hom.id = C := C.ind (fun _ => rfl)

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (C : G.ConnectedComponent) (φ : G ->g G') (ψ : G' ->g G'')
  proof: C.ind (fun _ => rfl)

@[simp]

中文:
定理 map_comp
  条件: (C : G.ConnectedComponent) (φ : G ->g G') (ψ : G' ->g G'')
  证明: C.ind (fun _ => rfl)

@[simp]

Depends on / 依赖: C.ind
-/
theorem map_comp (C : G.ConnectedComponent) (φ : G ->g G') (ψ : G' ->g G'') :
    (C.map φ).map ψ = C.map (ψ.comp φ) :=
  C.ind (fun _ => rfl)

@[simp]
/--
theorem `surjective_map_ofLE` / 定理 `surjective_map_ofLE`

English:
theorem surjective_map_ofLE
  given: {G' : SimpleGraph V} (h : G <= G')
  statement: (map <| Hom.ofLE h).Surjective
  proof: Quot.ind fun v => ⟨G.connectedComponentMk v, rfl⟩

中文:
定理 surjective_map_ofLE
  条件: {G' : SimpleGraph V} (h : G <= G')
  结论: (map <| Hom.ofLE h).Surjective
  证明: Quot.ind fun v => ⟨G.connectedComponentMk v, rfl⟩

Depends on / 依赖: G.connectedComponentMk, Quot.ind, connectedComponentMk
-/
theorem surjective_map_ofLE {G' : SimpleGraph V} (h : G <= G') : (map <| Hom.ofLE h).Surjective :=
  Quot.ind fun v => ⟨G.connectedComponentMk v, rfl⟩

variable {φ : G ≃g G'} {v : V} {v' : V'}

@[simp]
/--
theorem `iso_image_comp_eq_map_iff_eq_comp` / 定理 `iso_image_comp_eq_map_iff_eq_comp`

English:
theorem iso_image_comp_eq_map_iff_eq_comp
  given: {C : G.ConnectedComponent}
  proof: by
  refine C.ind fun u => ?_
  simp only [Iso.reachable_iff, ConnectedComponent.map_mk, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding, ConnectedComponent.eq]

@[simp]

中文:
定理 iso_image_comp_eq_map_iff_eq_comp
  条件: {C : G.ConnectedComponent}
  证明: by
  refine C.ind fun u => ?_
  simp only [Iso.reachable_iff, ConnectedComponent.map_mk, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding, ConnectedComponent.eq]

@[simp]

Depends on / 依赖: C.ind, ConnectedComponent, ConnectedComponent.eq, ConnectedComponent.map_mk, Iso.reachable_iff, RelEmbedding, RelEmbedding.coe_toRelHom, RelIso, RelIso.coe_toRelEmbedding, coe_toRelEmbedding, coe_toRelHom, map_mk, reachable_iff
-/
theorem iso_image_comp_eq_map_iff_eq_comp {C : G.ConnectedComponent} :
    G'.connectedComponentMk (φ v) = C.map ↑(↑φ : G ↪g G') ↔ G.connectedComponentMk v = C := by
  refine C.ind fun u => ?_
  simp only [Iso.reachable_iff, ConnectedComponent.map_mk, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding, ConnectedComponent.eq]

@[simp]
/--
theorem `iso_inv_image_comp_eq_iff_eq_map` / 定理 `iso_inv_image_comp_eq_iff_eq_map`

English:
theorem iso_inv_image_comp_eq_iff_eq_map
  given: {C : G.ConnectedComponent}
  proof: by
  refine C.ind fun u => ?_
  simp only [Iso.symm_apply_reachable, ConnectedComponent.eq, ConnectedComponent.map_mk,
    RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding]

中文:
定理 iso_inv_image_comp_eq_iff_eq_map
  条件: {C : G.ConnectedComponent}
  证明: by
  refine C.ind fun u => ?_
  simp only [Iso.symm_apply_reachable, ConnectedComponent.eq, ConnectedComponent.map_mk,
    RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding]

Depends on / 依赖: C.ind, ConnectedComponent, ConnectedComponent.eq, ConnectedComponent.map_mk, Iso.symm_apply_reachable, RelEmbedding, RelEmbedding.coe_toRelHom, RelIso, RelIso.coe_toRelEmbedding, coe_toRelEmbedding, coe_toRelHom, map_mk, symm_apply_reachable
-/
theorem iso_inv_image_comp_eq_iff_eq_map {C : G.ConnectedComponent} :
    G.connectedComponentMk (φ.symm v') = C ↔ G'.connectedComponentMk v' = C.map φ := by
  refine C.ind fun u => ?_
  simp only [Iso.symm_apply_reachable, ConnectedComponent.eq, ConnectedComponent.map_mk,
    RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding]

end ConnectedComponent

namespace Iso

/-- An isomorphism of graphs induces a bijection of connected components. -/
@[simps]
/--
Definition of `connectedComponentEquiv` / `connectedComponentEquiv` 的定义

English:
definition connectedComponentEquiv
  signature: (φ : G ≃g G')
  body: ConnectedComponent.map φ
  invFun := ConnectedComponent.map φ.symm
  left_inv C := C.ind (fun v => congr_arg G.connectedComponentMk (Equiv.left_inv φ.toEquiv v))
  right_inv C := C.ind (fun v => congr_arg G'.connectedComponentMk (Equiv.right_inv φ.toEquiv v))

@[simp]

中文:
定义 connectedComponentEquiv
  签名: (φ : G ≃g G')
  定义体: ConnectedComponent.map φ
  invFun := ConnectedComponent.map φ.symm
  left_inv C := C.ind (fun v => congr_arg G.connectedComponentMk (Equiv.left_inv φ.toEquiv v))
  right_inv C := C.ind (fun v => congr_arg G'.connectedComponentMk (Equiv.right_inv φ.toEquiv v))

@[simp]

Depends on / 依赖: ConnectedComponent, ConnectedComponent.map
-/
def connectedComponentEquiv (φ : G ≃g G') : G.ConnectedComponent ≃ G'.ConnectedComponent where
  toFun := ConnectedComponent.map φ
  invFun := ConnectedComponent.map φ.symm
  left_inv C := C.ind (fun v => congr_arg G.connectedComponentMk (Equiv.left_inv φ.toEquiv v))
  right_inv C := C.ind (fun v => congr_arg G'.connectedComponentMk (Equiv.right_inv φ.toEquiv v))

@[simp]
/--
theorem `connectedComponentEquiv_refl` / 定理 `connectedComponentEquiv_refl`

English:
theorem connectedComponentEquiv_refl
  proof: by
  ext ⟨v⟩
  rfl

@[simp]

中文:
定理 connectedComponentEquiv_refl
  证明: by
  ext ⟨v⟩
  rfl

@[simp]
-/
theorem connectedComponentEquiv_refl :
    (Iso.refl : G ≃g G).connectedComponentEquiv = Equiv.refl _ := by
  ext ⟨v⟩
  rfl

@[simp]
/--
theorem `connectedComponentEquiv_symm` / 定理 `connectedComponentEquiv_symm`

English:
theorem connectedComponentEquiv_symm
  given: (φ : G ≃g G')
  proof: by
  ext ⟨_⟩
  rfl

@[simp]

中文:
定理 connectedComponentEquiv_symm
  条件: (φ : G ≃g G')
  证明: by
  ext ⟨_⟩
  rfl

@[simp]
-/
theorem connectedComponentEquiv_symm (φ : G ≃g G') :
    φ.symm.connectedComponentEquiv = φ.connectedComponentEquiv.symm := by
  ext ⟨_⟩
  rfl

@[simp]
/--
theorem `connectedComponentEquiv_trans` / 定理 `connectedComponentEquiv_trans`

English:
theorem connectedComponentEquiv_trans
  given: (φ : G ≃g G') (φ' : G' ≃g G'')
  proof: by
  ext ⟨_⟩
  rfl

中文:
定理 connectedComponentEquiv_trans
  条件: (φ : G ≃g G') (φ' : G' ≃g G'')
  证明: by
  ext ⟨_⟩
  rfl
-/
theorem connectedComponentEquiv_trans (φ : G ≃g G') (φ' : G' ≃g G'') :
    connectedComponentEquiv (φ.trans φ') =
    φ.connectedComponentEquiv.trans φ'.connectedComponentEquiv := by
  ext ⟨_⟩
  rfl

end Iso

namespace ConnectedComponent

/--
Definition of `supp` / `supp` 的定义

English:
definition supp
  signature: (C : G.ConnectedComponent)
  body: { v | G.connectedComponentMk v = C }

@[ext]

中文:
定义 supp
  签名: (C : G.ConnectedComponent)
  定义体: { v | G.connectedComponentMk v = C }

@[ext]

Depends on / 依赖: G.connectedComponentMk, connectedComponentMk
-/
def supp (C : G.ConnectedComponent) :=
  { v | G.connectedComponentMk v = C }

@[ext]
/--
theorem `supp_injective` / 定理 `supp_injective`

English:
theorem supp_injective
  proof: by
  refine ConnectedComponent.ind₂ ?_
  simp only [ConnectedComponent.supp, Set.ext_iff, ConnectedComponent.eq, Set.mem_ofPred_eq]
  intro v w h
  rw [reachable_comm]; rw [h]

@[simp]

中文:
定理 supp_injective
  证明: by
  refine ConnectedComponent.ind₂ ?_
  simp only [ConnectedComponent.supp, Set.ext_iff, ConnectedComponent.eq, Set.mem_ofPred_eq]
  intro v w h
  rw [reachable_comm]; rw [h]

@[simp]

Depends on / 依赖: ConnectedComponent, ConnectedComponent.eq, ConnectedComponent.ind, ConnectedComponent.supp, Set.ext_iff, Set.mem_ofPred_eq, ext_iff, mem_ofPred_eq, reachable_comm
-/
theorem supp_injective :
    Function.Injective (ConnectedComponent.supp : G.ConnectedComponent -> Set V) := by
  refine ConnectedComponent.ind₂ ?_
  simp only [ConnectedComponent.supp, Set.ext_iff, ConnectedComponent.eq, Set.mem_ofPred_eq]
  intro v w h
  rw [reachable_comm]; rw [h]

@[simp]
/--
theorem `supp_inj` / 定理 `supp_inj`

English:
theorem supp_inj
  given: {C D : G.ConnectedComponent}
  statement: C.supp = D.supp ↔ C = D
  proof: ConnectedComponent.supp_injective.eq_iff

中文:
定理 supp_inj
  条件: {C D : G.ConnectedComponent}
  结论: C.supp = D.supp ↔ C = D
  证明: ConnectedComponent.supp_injective.eq_iff

Depends on / 依赖: ConnectedComponent, ConnectedComponent.supp_injective.eq_iff, eq_iff, supp_injective
-/
theorem supp_inj {C D : G.ConnectedComponent} : C.supp = D.supp ↔ C = D :=
  ConnectedComponent.supp_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike G.ConnectedComponent V
  body: ConnectedComponent.supp
  coe_injective := ConnectedComponent.supp_injective

@[simp]

中文:
实例 :
  签名: SetLike G.ConnectedComponent V
  定义体: ConnectedComponent.supp
  coe_injective := ConnectedComponent.supp_injective

@[simp]

Depends on / 依赖: ConnectedComponent, ConnectedComponent.supp
-/
instance : SetLike G.ConnectedComponent V where
  coe := ConnectedComponent.supp
  coe_injective := ConnectedComponent.supp_injective

@[simp]
/--
theorem `mem_supp_iff` / 定理 `mem_supp_iff`

English:
theorem mem_supp_iff
  given: (C : G.ConnectedComponent) (v : V)
  proof: Iff.rfl

中文:
定理 mem_supp_iff
  条件: (C : G.ConnectedComponent) (v : V)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_supp_iff (C : G.ConnectedComponent) (v : V) :
    v in C.supp ↔ G.connectedComponentMk v = C :=
  Iff.rfl

/--
lemma `mem_supp_congr_adj` / 引理 `mem_supp_congr_adj`

English:
lemma mem_supp_congr_adj
  given: {v w : V} (c : G.ConnectedComponent) (hadj : G.Adj v w)
  proof: by
  simp only [ConnectedComponent.mem_supp_iff] at *
  constructor <;> intro h <;> simp only [← h] <;> apply connectedComponentMk_eq_of_adj
  · exact hadj.symm
  · exact hadj

中文:
引理 mem_supp_congr_adj
  条件: {v w : V} (c : G.ConnectedComponent) (hadj : G.Adj v w)
  证明: by
  simp only [ConnectedComponent.mem_supp_iff] at *
  constructor <;> intro h <;> simp only [← h] <;> apply connectedComponentMk_eq_of_adj
  · exact hadj.symm
  · exact hadj

Depends on / 依赖: ConnectedComponent, ConnectedComponent.mem_supp_iff, connectedComponentMk_eq_of_adj, hadj.symm, mem_supp_iff
-/
lemma mem_supp_congr_adj {v w : V} (c : G.ConnectedComponent) (hadj : G.Adj v w) :
    v in c.supp ↔ w in c.supp := by
  simp only [ConnectedComponent.mem_supp_iff] at *
  constructor <;> intro h <;> simp only [← h] <;> apply connectedComponentMk_eq_of_adj
  · exact hadj.symm
  · exact hadj

/--
theorem `connectedComponentMk_mem` / 定理 `connectedComponentMk_mem`

English:
theorem connectedComponentMk_mem
  given: {v : V}
  statement: v in G.connectedComponentMk v
  proof: rfl

中文:
定理 connectedComponentMk_mem
  条件: {v : V}
  结论: v in G.connectedComponentMk v
  证明: rfl
-/
theorem connectedComponentMk_mem {v : V} : v in G.connectedComponentMk v :=
  rfl

/--
theorem `nonempty_supp` / 定理 `nonempty_supp`

English:
theorem nonempty_supp
  given: (C : G.ConnectedComponent)
  statement: C.supp.Nonempty
  proof: C.exists_rep

中文:
定理 nonempty_supp
  条件: (C : G.ConnectedComponent)
  结论: C.supp.Nonempty
  证明: C.exists_rep

Depends on / 依赖: C.exists_rep, exists_rep
-/
theorem nonempty_supp (C : G.ConnectedComponent) : C.supp.Nonempty := C.exists_rep

/--
Definition of `isoEquivSupp` / `isoEquivSupp` 的定义

English:
definition isoEquivSupp
  signature: (φ : G ≃g G') (C : G.ConnectedComponent)
  body: ⟨φ v, ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr v.prop⟩
  invFun v' := ⟨φ.symm v', ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map.mpr v'.prop⟩
  left_inv v := Subtype.ext (φ.toEquiv.left_inv ↑v)
  right_inv v := Subtype.ext (φ.toEquiv.right_inv ↑v)

中文:
定义 isoEquivSupp
  签名: (φ : G ≃g G') (C : G.ConnectedComponent)
  定义体: ⟨φ v, ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr v.prop⟩
  invFun v' := ⟨φ.symm v', ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map.mpr v'.prop⟩
  left_inv v := Subtype.ext (φ.toEquiv.left_inv ↑v)
  right_inv v := Subtype.ext (φ.toEquiv.right_inv ↑v)

Depends on / 依赖: ConnectedComponent, ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr, iso_image_comp_eq_map_iff_eq_comp, v.prop
-/
def isoEquivSupp (φ : G ≃g G') (C : G.ConnectedComponent) :
    C.supp ≃ (φ.connectedComponentEquiv C).supp where
  toFun v := ⟨φ v, ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr v.prop⟩
  invFun v' := ⟨φ.symm v', ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map.mpr v'.prop⟩
  left_inv v := Subtype.ext (φ.toEquiv.left_inv ↑v)
  right_inv v := Subtype.ext (φ.toEquiv.right_inv ↑v)

/--
lemma `mem_coe_supp_of_adj` / 引理 `mem_coe_supp_of_adj`

English:
lemma mem_coe_supp_of_adj
  statement: {v w : V} {H : Subgraph G} {c : ConnectedComponent H.coe}
  proof: by
  obtain ⟨_, h⟩ := hv
  use ⟨w, hw⟩
  rw [← (mem_supp_iff _ _).mp h.1]
exact ⟨connectedComponentMk_eq_of_adj Subgraph.Adj.coe h.2 ▸ hadj.symm, rfl⟩

中文:
引理 mem_coe_supp_of_adj
  结论: {v w : V} {H : Subgraph G} {c : ConnectedComponent H.coe}
  证明: by
  obtain ⟨_, h⟩ := hv
  use ⟨w, hw⟩
  rw [← (mem_supp_iff _ _).mp h.1]
exact ⟨connectedComponentMk_eq_of_adj Subgraph.Adj.coe h.2 ▸ hadj.symm, rfl⟩

Depends on / 依赖: Subgraph, Subgraph.Adj.coe, connectedComponentMk_eq_of_adj, hadj.symm, mem_supp_iff
-/
lemma mem_coe_supp_of_adj {v w : V} {H : Subgraph G} {c : ConnectedComponent H.coe}
    (hv : v in (↑) '' (c : Set H.verts)) (hw : w in H.verts)
    (hadj : H.Adj v w) : w in (↑) '' (c : Set H.verts) := by
  obtain ⟨_, h⟩ := hv
  use ⟨w, hw⟩
  rw [← (mem_supp_iff _ _).mp h.1]
exact ⟨connectedComponentMk_eq_of_adj Subgraph.Adj.coe h.2 ▸ hadj.symm, rfl⟩

/--
lemma `eq_of_common_vertex` / 引理 `eq_of_common_vertex`

English:
lemma eq_of_common_vertex
  statement: {v : V} {c c' : ConnectedComponent G} (hc : v in c.supp)
  proof: by
  simp only [mem_supp_iff] at *
  rw [← hc]; rw [← hc']

中文:
引理 eq_of_common_vertex
  结论: {v : V} {c c' : ConnectedComponent G} (hc : v in c.supp)
  证明: by
  simp only [mem_supp_iff] at *
  rw [← hc]; rw [← hc']

Depends on / 依赖: mem_supp_iff
-/
lemma eq_of_common_vertex {v : V} {c c' : ConnectedComponent G} (hc : v in c.supp)
    (hc' : v in c'.supp) : c = c' := by
  simp only [mem_supp_iff] at *
  rw [← hc]; rw [← hc']

/--
lemma `connectedComponentMk_supp_subset_supp` / 引理 `connectedComponentMk_supp_subset_supp`

English:
lemma connectedComponentMk_supp_subset_supp
  statement: {G'} {v : V} (h : G <= G') (c' : G'.ConnectedComponent)
  proof: by
  intro v' hv'
  simp only [mem_supp_iff, ConnectedComponent.eq] at hv' ⊢
  rw [ConnectedComponent.sound (hv'.mono h)]
  exact hc'

中文:
引理 connectedComponentMk_supp_subset_supp
  结论: {G'} {v : V} (h : G <= G') (c' : G'.ConnectedComponent)
  证明: by
  intro v' hv'
  simp only [mem_supp_iff, ConnectedComponent.eq] at hv' ⊢
  rw [ConnectedComponent.sound (hv'.mono h)]
  exact hc'

Depends on / 依赖: ConnectedComponent, ConnectedComponent.eq, ConnectedComponent.sound, mem_supp_iff
-/
lemma connectedComponentMk_supp_subset_supp {G'} {v : V} (h : G <= G') (c' : G'.ConnectedComponent)
    (hc' : v in c'.supp) : (G.connectedComponentMk v).supp subseteq c'.supp := by
  intro v' hv'
  simp only [mem_supp_iff, ConnectedComponent.eq] at hv' ⊢
  rw [ConnectedComponent.sound (hv'.mono h)]
  exact hc'

/--
lemma `biUnion_supp_eq_supp` / 引理 `biUnion_supp_eq_supp`

English:
lemma biUnion_supp_eq_supp
  given: {G G' : SimpleGraph V} (h : G <= G') (c' : ConnectedComponent G')
  proof: by
  ext v
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨_, ⟨hi, hi'⟩⟩ => hi hi', ?_⟩
  intro hv
  use G.connectedComponentMk v
  use c'.connectedComponentMk_supp_subset_supp h hv
  simp only [mem_supp_iff]

中文:
引理 biUnion_supp_eq_supp
  条件: {G G' : SimpleGraph V} (h : G <= G') (c' : ConnectedComponent G')
  证明: by
  ext v
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨_, ⟨hi, hi'⟩⟩ => hi hi', ?_⟩
  intro hv
  use G.connectedComponentMk v
  use c'.connectedComponentMk_supp_subset_supp h hv
  simp only [mem_supp_iff]

Depends on / 依赖: G.connectedComponentMk, Set.mem_iUnion, connectedComponentMk, connectedComponentMk_supp_subset_supp, mem_iUnion, mem_supp_iff, simp_rw
-/
lemma biUnion_supp_eq_supp {G G' : SimpleGraph V} (h : G <= G') (c' : ConnectedComponent G') :
    ⋃ (c : ConnectedComponent G) (_ : c.supp subseteq c'.supp), c.supp = c'.supp := by
  ext v
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨_, ⟨hi, hi'⟩⟩ => hi hi', ?_⟩
  intro hv
  use G.connectedComponentMk v
  use c'.connectedComponentMk_supp_subset_supp h hv
  simp only [mem_supp_iff]

/--
lemma `top_supp_eq_univ` / 引理 `top_supp_eq_univ`

English:
lemma top_supp_eq_univ
  given: (c : ConnectedComponent (⊤ : SimpleGraph V))
  proof: by
  obtain ⟨w, rfl⟩ := c.exists_rep
  ext v
  simpa [-ConnectedComponent.eq] using! ConnectedComponent.sound (G := ⊤)

中文:
引理 top_supp_eq_univ
  条件: (c : ConnectedComponent (⊤ : SimpleGraph V))
  证明: by
  obtain ⟨w, rfl⟩ := c.exists_rep
  ext v
  simpa [-ConnectedComponent.eq] using! ConnectedComponent.sound (G := ⊤)

Depends on / 依赖: ConnectedComponent, ConnectedComponent.eq, ConnectedComponent.sound, c.exists_rep, exists_rep
-/
lemma top_supp_eq_univ (c : ConnectedComponent (⊤ : SimpleGraph V)) :
    c.supp = (Set.univ : Set V) := by
  obtain ⟨w, rfl⟩ := c.exists_rep
  ext v
  simpa [-ConnectedComponent.eq] using! ConnectedComponent.sound (G := ⊤)

/--
lemma `reachable_of_mem_supp` / 引理 `reachable_of_mem_supp`

English:
lemma reachable_of_mem_supp
  statement: {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
  proof: by
  rw [mem_supp_iff] at hu hv
  exact ConnectedComponent.exact (hv ▸ hu)

中文:
引理 reachable_of_mem_supp
  结论: {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
  证明: by
  rw [mem_supp_iff] at hu hv
  exact ConnectedComponent.exact (hv ▸ hu)

Depends on / 依赖: ConnectedComponent, ConnectedComponent.exact, mem_supp_iff
-/
lemma reachable_of_mem_supp {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u in C.supp) (hv : v in C.supp) : G.Reachable u v := by
  rw [mem_supp_iff] at hu hv
  exact ConnectedComponent.exact (hv ▸ hu)

/--
lemma `mem_supp_of_adj_mem_supp` / 引理 `mem_supp_of_adj_mem_supp`

English:
lemma mem_supp_of_adj_mem_supp
  statement: {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
  proof: (mem_supp_congr_adj C hadj).mp hu

中文:
引理 mem_supp_of_adj_mem_supp
  结论: {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
  证明: (mem_supp_congr_adj C hadj).mp hu

Depends on / 依赖: mem_supp_congr_adj
-/
lemma mem_supp_of_adj_mem_supp {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u in C.supp) (hadj : G.Adj u v) : v in C.supp := (mem_supp_congr_adj C hadj).mp hu

/--
Definition of `toSimpleGraph` / `toSimpleGraph` 的定义

English:
definition toSimpleGraph
  signature: {G : SimpleGraph V} (C : G.ConnectedComponent)
  body: G.induce C.supp

中文:
定义 toSimpleGraph
  签名: {G : SimpleGraph V} (C : G.ConnectedComponent)
  定义体: G.induce C.supp

Depends on / 依赖: C.supp, G.induce, induce
-/
def toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) : SimpleGraph C := G.induce C.supp

/--
Definition of `toSimpleGraph_hom` / `toSimpleGraph_hom` 的定义

English:
definition toSimpleGraph_hom
  signature: {G : SimpleGraph V} (C : G.ConnectedComponent)
  body: u.val
  map_rel' := id

中文:
定义 toSimpleGraph_hom
  签名: {G : SimpleGraph V} (C : G.ConnectedComponent)
  定义体: u.val
  map_rel' := id

Depends on / 依赖: u.val
-/
def toSimpleGraph_hom {G : SimpleGraph V} (C : G.ConnectedComponent) : C.toSimpleGraph ->g G where
  toFun u := u.val
  map_rel' := id

/--
lemma `toSimpleGraph_hom_apply` / 引理 `toSimpleGraph_hom_apply`

English:
lemma toSimpleGraph_hom_apply
  given: {G : SimpleGraph V} (C : G.ConnectedComponent) (u : C)
  proof: rfl

中文:
引理 toSimpleGraph_hom_apply
  条件: {G : SimpleGraph V} (C : G.ConnectedComponent) (u : C)
  证明: rfl
-/
lemma toSimpleGraph_hom_apply {G : SimpleGraph V} (C : G.ConnectedComponent) (u : C) :
    C.toSimpleGraph_hom u = u.val := rfl

/--
lemma `toSimpleGraph_adj` / 引理 `toSimpleGraph_adj`

English:
lemma toSimpleGraph_adj
  statement: {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V} (hu : u in C)
  proof: by
  simp [toSimpleGraph]

中文:
引理 toSimpleGraph_adj
  结论: {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V} (hu : u in C)
  证明: by
  simp [toSimpleGraph]

Depends on / 依赖: toSimpleGraph
-/
lemma toSimpleGraph_adj {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V} (hu : u in C)
    (hv : v in C) : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨v, hv⟩ ↔ G.Adj u v := by
  simp [toSimpleGraph]

/--
lemma `adj_spanningCoe_toSimpleGraph` / 引理 `adj_spanningCoe_toSimpleGraph`

English:
lemma adj_spanningCoe_toSimpleGraph
  given: {v w : V} (C : G.ConnectedComponent)
  proof: by
  apply Iff.intro
  · intro h
    simp_all only [map_adj, SetLike.coe_sort_coe, Subtype.exists, mem_supp_iff]
    obtain ⟨_, a, _, _, h₁, rfl, rfl⟩ := h
    exact ⟨a, h₁⟩
  · simp only [toSimpleGraph, map_adj, comap_adj, Embedding.subtype_apply, Subtype.exists,
      exists_and_left, and_imp]
   

中文:
引理 adj_spanningCoe_toSimpleGraph
  条件: {v w : V} (C : G.ConnectedComponent)
  证明: by
  apply Iff.intro
  · intro h
    simp_all only [map_adj, SetLike.coe_sort_coe, Subtype.exists, mem_supp_iff]
    obtain ⟨_, a, _, _, h₁, rfl, rfl⟩ := h
    exact ⟨a, h₁⟩
  · simp only [toSimpleGraph, map_adj, comap_adj, Embedding.subtype_apply, Subtype.exists,
      exists_and_left, and_imp]
   

Depends on / 依赖: C.mem_supp_congr_adj, Embedding, Embedding.subtype_apply, Iff.intro, SetLike, SetLike.coe_sort_coe, Subtype, Subtype.exists, and_imp, coe_sort_coe, comap_adj, exists_and_left, map_adj, mem_supp_congr_adj, mem_supp_iff, subtype_apply, toSimpleGraph
-/
lemma adj_spanningCoe_toSimpleGraph {v w : V} (C : G.ConnectedComponent) :
    C.toSimpleGraph.spanningCoe.Adj v w ↔ v in C.supp ∧ G.Adj v w := by
  apply Iff.intro
  · intro h
    simp_all only [map_adj, SetLike.coe_sort_coe, Subtype.exists, mem_supp_iff]
    obtain ⟨_, a, _, _, h₁, rfl, rfl⟩ := h
    exact ⟨a, h₁⟩
  · simp only [toSimpleGraph, map_adj, comap_adj, Embedding.subtype_apply, Subtype.exists,
      exists_and_left, and_imp]
    intro h hadj
    exact ⟨v, h, w, hadj, rfl, (C.mem_supp_congr_adj hadj).mp h, rfl⟩

/--
Definition of `walk_toSimpleGraph` / `walk_toSimpleGraph` 的定义

English:
definition walk_toSimpleGraph
  signature: {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
  body: by
  cases p with
  | nil => exact Walk.nil
  | @cons v w u h p =>
    have hw : w in C := C.mem_supp_of_adj_mem_supp hu h
    have h' : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨w, hw⟩ := h
    exact Walk.cons h' (C.walk_toSimpleGraph hw hv p)

中文:
定义 walk_toSimpleGraph
  签名: {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
  定义体: by
  cases p with
  | nil => exact Walk.nil
  | @cons v w u h p =>
    have hw : w in C := C.mem_supp_of_adj_mem_supp hu h
    have h' : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨w, hw⟩ := h
    exact Walk.cons h' (C.walk_toSimpleGraph hw hv p)
-/
private def walk_toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u in C) (hv : v in C) (p : G.Walk u v) : C.toSimpleGraph.Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  cases p with
  | nil => exact Walk.nil
  | @cons v w u h p =>
    have hw : w in C := C.mem_supp_of_adj_mem_supp hu h
    have h' : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨w, hw⟩ := h
    exact Walk.cons h' (C.walk_toSimpleGraph hw hv p)

/--
lemma `reachable_toSimpleGraph` / 引理 `reachable_toSimpleGraph`

English:
lemma reachable_toSimpleGraph
  statement: {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
  proof: Walk.reachable (C.walk_toSimpleGraph hu hv (C.reachable_of_mem_supp hu hv).some)

中文:
引理 reachable_toSimpleGraph
  结论: {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
  证明: Walk.reachable (C.walk_toSimpleGraph hu hv (C.reachable_of_mem_supp hu hv).some)

Depends on / 依赖: C.reachable_of_mem_supp, C.walk_toSimpleGraph, Walk.reachable, reachable, reachable_of_mem_supp, walk_toSimpleGraph
-/
lemma reachable_toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u in C) (hv : v in C) : C.toSimpleGraph.Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
  Walk.reachable (C.walk_toSimpleGraph hu hv (C.reachable_of_mem_supp hu hv).some)

/--
lemma `connected_toSimpleGraph` / 引理 `connected_toSimpleGraph`

English:
lemma connected_toSimpleGraph
  given: (C : ConnectedComponent G)
  statement: (C.toSimpleGraph).Connected where
  proof: by
    intro ⟨u, hu⟩ ⟨v, hv⟩
    exact C.reachable_toSimpleGraph hu hv
  nonempty := ⟨C.out, C.out_eq⟩

中文:
引理 connected_toSimpleGraph
  条件: (C : ConnectedComponent G)
  结论: (C.toSimpleGraph).Connected where
  证明: by
    intro ⟨u, hu⟩ ⟨v, hv⟩
    exact C.reachable_toSimpleGraph hu hv
  nonempty := ⟨C.out, C.out_eq⟩

Depends on / 依赖: C.out, C.out_eq, C.reachable_toSimpleGraph, nonempty, out_eq, reachable_toSimpleGraph
-/
lemma connected_toSimpleGraph (C : ConnectedComponent G) : (C.toSimpleGraph).Connected where
  preconnected := by
    intro ⟨u, hu⟩ ⟨v, hv⟩
    exact C.reachable_toSimpleGraph hu hv
  nonempty := ⟨C.out, C.out_eq⟩

/--
theorem `maximal_connected_induce_supp` / 定理 `maximal_connected_induce_supp`

English:
theorem maximal_connected_induce_supp
  given: (C : G.ConnectedComponent)
  proof: by
  refine C.ind fun v => ?_
  refine ⟨connected_toSimpleGraph _, fun s hconn hle u hu => ConnectedComponent.sound ?_⟩
.map .toHom Embedding.induce s exact hconn.preconnected ⟨u, hu⟩ ⟨v, hle rfl⟩

中文:
定理 maximal_connected_induce_supp
  条件: (C : G.ConnectedComponent)
  证明: by
  refine C.ind fun v => ?_
  refine ⟨connected_toSimpleGraph _, fun s hconn hle u hu => ConnectedComponent.sound ?_⟩
.map .toHom Embedding.induce s exact hconn.preconnected ⟨u, hu⟩ ⟨v, hle rfl⟩

Depends on / 依赖: C.ind, ConnectedComponent, ConnectedComponent.sound, Embedding, Embedding.induce, connected_toSimpleGraph, hconn.preconnected, induce, measure, preconnected
-/
theorem maximal_connected_induce_supp (C : G.ConnectedComponent) :
    Maximal (G.induce · |>.Connected) C.supp := by
  refine C.ind fun v => ?_
  refine ⟨connected_toSimpleGraph _, fun s hconn hle u hu => ConnectedComponent.sound ?_⟩
.map .toHom Embedding.induce s exact hconn.preconnected ⟨u, hu⟩ ⟨v, hle rfl⟩

/--
theorem `maximal_connected_induce_iff` / 定理 `maximal_connected_induce_iff`

English:
theorem maximal_connected_induce_iff
  given: (s : Set V)
  proof: by
  refine ⟨fun ⟨hconn, h⟩ => ?_, fun ⟨C, h⟩ => ?_⟩
  · have ⟨v, hv⟩ := hconn.nonempty
    suffices s <= (G.connectedComponentMk v).supp from
      ⟨G.connectedComponentMk v, le_antisymm (h (connected_toSimpleGraph _) this) this⟩
exact fun u hu => ConnectedComponent.sound
.map .toHom Embedding.indu

中文:
定理 maximal_connected_induce_iff
  条件: (s : Set V)
  证明: by
  refine ⟨fun ⟨hconn, h⟩ => ?_, fun ⟨C, h⟩ => ?_⟩
  · have ⟨v, hv⟩ := hconn.nonempty
    suffices s <= (G.connectedComponentMk v).supp from
      ⟨G.connectedComponentMk v, le_antisymm (h (connected_toSimpleGraph _) this) this⟩
exact fun u hu => ConnectedComponent.sound
.map .toHom Embedding.indu

Depends on / 依赖: ConnectedComponent, ConnectedComponent.sound, Embedding, Embedding.induce, G.connectedComponentMk, connectedComponentMk, connected_toSimpleGraph, hconn.nonempty, hconn.preconnected, induce, le_antisymm, maximal_connected_induce_supp, nonempty, preconnected
-/
theorem maximal_connected_induce_iff (s : Set V) :
    Maximal (G.induce · |>.Connected) s ↔ exists C : G.ConnectedComponent, C.supp = s := by
  refine ⟨fun ⟨hconn, h⟩ => ?_, fun ⟨C, h⟩ => ?_⟩
  · have ⟨v, hv⟩ := hconn.nonempty
    suffices s <= (G.connectedComponentMk v).supp from
      ⟨G.connectedComponentMk v, le_antisymm (h (connected_toSimpleGraph _) this) this⟩
exact fun u hu => ConnectedComponent.sound
.map .toHom Embedding.induce s hconn.preconnected ⟨u, hu⟩ ⟨v, hv⟩
  · exact h ▸ maximal_connected_induce_supp _

end ConnectedComponent

/-- Given graph homomorphisms from each connected component of `G` to `H`, this is the graph
homomorphism from `G` to `H`. -/
@[simps]
/--
Definition of `homOfConnectedComponents` / `homOfConnectedComponents` 的定义

English:
definition homOfConnectedComponents
  signature: (G : SimpleGraph V) {H : SimpleGraph V'}
  body: fun x => (C (G.connectedComponentMk x)) ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
  map_rel' := fun hab => by
    have h : (G.connectedComponentMk _).toSimpleGraph.Adj ⟨_, rfl⟩
        ⟨_, ((G.connectedComponentMk _).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using! hab
    convert (C (G.conn

中文:
定义 homOfConnectedComponents
  签名: (G : SimpleGraph V) {H : SimpleGraph V'}
  定义体: fun x => (C (G.connectedComponentMk x)) ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
  map_rel' := fun hab => by
    have h : (G.connectedComponentMk _).toSimpleGraph.Adj ⟨_, rfl⟩
        ⟨_, ((G.connectedComponentMk _).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using! hab
    convert (C (G.conn

Depends on / 依赖: ConnectedComponent, ConnectedComponent.connectedComponentMk_mem, G.connectedComponentMk, connectedComponentMk, connectedComponentMk_mem
-/
def homOfConnectedComponents (G : SimpleGraph V) {H : SimpleGraph V'}
    (C : (c : G.ConnectedComponent) -> c.toSimpleGraph ->g H) : G ->g H where
  toFun := fun x => (C (G.connectedComponentMk x)) ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
  map_rel' := fun hab => by
    have h : (G.connectedComponentMk _).toSimpleGraph.Adj ⟨_, rfl⟩
        ⟨_, ((G.connectedComponentMk _).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using! hab
    convert (C (G.connectedComponentMk _)).map_rel h using 3 <;>
      rw [ConnectedComponent.connectedComponentMk_eq_of_adj hab]

-- TODO: Extract as lemma about general equivalence relation
/--
lemma `pairwise_disjoint_supp_connectedComponent` / 引理 `pairwise_disjoint_supp_connectedComponent`

English:
lemma pairwise_disjoint_supp_connectedComponent
  given: (G : SimpleGraph V)
  proof: by
  simp_rw [Set.disjoint_left]
  intro _ _ h a hsx hsy
  rw [ConnectedComponent.mem_supp_iff] at hsx hsy
  rw [hsx] at hsy
  exact h hsy

中文:
引理 pairwise_disjoint_supp_connectedComponent
  条件: (G : SimpleGraph V)
  证明: by
  simp_rw [Set.disjoint_left]
  intro _ _ h a hsx hsy
  rw [ConnectedComponent.mem_supp_iff] at hsx hsy
  rw [hsx] at hsy
  exact h hsy

Depends on / 依赖: ConnectedComponent, ConnectedComponent.mem_supp_iff, Set.disjoint_left, disjoint_left, mem_supp_iff, simp_rw
-/
lemma pairwise_disjoint_supp_connectedComponent (G : SimpleGraph V) :
    Pairwise fun c c' : ConnectedComponent G => Disjoint c.supp c'.supp := by
  simp_rw [Set.disjoint_left]
  intro _ _ h a hsx hsy
  rw [ConnectedComponent.mem_supp_iff] at hsx hsy
  rw [hsx] at hsy
  exact h hsy

-- TODO: Extract as lemma about general equivalence relation
/--
lemma `iUnion_connectedComponentSupp` / 引理 `iUnion_connectedComponentSupp`

English:
lemma iUnion_connectedComponentSupp
  given: (G : SimpleGraph V)
  proof: by
  refine Set.eq_univ_of_forall fun v => ⟨G.connectedComponentMk v, ?_⟩
  simp only [Set.mem_range, SetLike.mem_coe]
  exact ⟨⟨G.connectedComponentMk v, rfl⟩, rfl⟩

中文:
引理 iUnion_connectedComponentSupp
  条件: (G : SimpleGraph V)
  证明: by
  refine Set.eq_univ_of_forall fun v => ⟨G.connectedComponentMk v, ?_⟩
  simp only [Set.mem_range, SetLike.mem_coe]
  exact ⟨⟨G.connectedComponentMk v, rfl⟩, rfl⟩

Depends on / 依赖: G.connectedComponentMk, Set.eq_univ_of_forall, Set.mem_range, SetLike, SetLike.mem_coe, connectedComponentMk, eq_univ_of_forall, mem_coe, mem_range
-/
lemma iUnion_connectedComponentSupp (G : SimpleGraph V) :
    ⋃ c : G.ConnectedComponent, c.supp = Set.univ := by
  refine Set.eq_univ_of_forall fun v => ⟨G.connectedComponentMk v, ?_⟩
  simp only [Set.mem_range, SetLike.mem_coe]
  exact ⟨⟨G.connectedComponentMk v, rfl⟩, rfl⟩

/--
theorem `Preconnected.set_univ_walk_nonempty` / 定理 `Preconnected.set_univ_walk_nonempty`

English:
theorem Preconnected.set_univ_walk_nonempty
  given: (hconn : G.Preconnected) (u v : V)
  proof: by
  rw [← Set.nonempty_iff_univ_nonempty]
  exact hconn u v

中文:
定理 Preconnected.set_univ_walk_nonempty
  条件: (hconn : G.Preconnected) (u v : V)
  证明: by
  rw [← Set.nonempty_iff_univ_nonempty]
  exact hconn u v

Depends on / 依赖: Set.nonempty_iff_univ_nonempty, nonempty_iff_univ_nonempty
-/
theorem Preconnected.set_univ_walk_nonempty (hconn : G.Preconnected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  rw [← Set.nonempty_iff_univ_nonempty]
  exact hconn u v

/--
theorem `Connected.set_univ_walk_nonempty` / 定理 `Connected.set_univ_walk_nonempty`

English:
theorem Connected.set_univ_walk_nonempty
  given: (hconn : G.Connected) (u v : V)
  proof: hconn.preconnected.set_univ_walk_nonempty u v

中文:
定理 Connected.set_univ_walk_nonempty
  条件: (hconn : G.Connected) (u v : V)
  证明: hconn.preconnected.set_univ_walk_nonempty u v

Depends on / 依赖: hconn.preconnected.set_univ_walk_nonempty, preconnected, set_univ_walk_nonempty
-/
theorem Connected.set_univ_walk_nonempty (hconn : G.Connected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty :=
  hconn.preconnected.set_univ_walk_nonempty u v

/--
lemma `Preconnected.exists_adj_of_nontrivial` / 引理 `Preconnected.exists_adj_of_nontrivial`

English:
lemma Preconnected.exists_adj_of_nontrivial
  statement: [Nontrivial V] {G : SimpleGraph V} (h : G.Preconnected)
  proof: by
  have ⟨u, huv⟩ := exists_ne v
  have ⟨w⟩ := h v u
exact ⟨_, w.adj_snd w.not_nil_of_ne huv.symm⟩

中文:
引理 Preconnected.exists_adj_of_nontrivial
  结论: [Nontrivial V] {G : SimpleGraph V} (h : G.Preconnected)
  证明: by
  have ⟨u, huv⟩ := exists_ne v
  have ⟨w⟩ := h v u
exact ⟨_, w.adj_snd w.not_nil_of_ne huv.symm⟩

Depends on / 依赖: adj_snd, exists_ne, huv.symm, not_nil_of_ne, w.adj_snd, w.not_nil_of_ne
-/
lemma Preconnected.exists_adj_of_nontrivial [Nontrivial V] {G : SimpleGraph V} (h : G.Preconnected)
    (v : V) : exists u, G.Adj v u := by
  have ⟨u, huv⟩ := exists_ne v
  have ⟨w⟩ := h v u
exact ⟨_, w.adj_snd w.not_nil_of_ne huv.symm⟩

/-! ### Bridge edges -/

section BridgeEdges
variable {u v : V}

/--
Definition of `IsBridge` / `IsBridge` 的定义

English:
definition IsBridge
  signature: (G : SimpleGraph V) (e : Sym2 V)
  body: Sym2.lift ⟨fun v w => ¬ (G.deleteEdges {e}).Reachable v w, by simp [reachable_comm]⟩ e

中文:
定义 IsBridge
  签名: (G : SimpleGraph V) (e : Sym2 V)
  定义体: Sym2.lift ⟨fun v w => ¬ (G.deleteEdges {e}).Reachable v w, by simp [reachable_comm]⟩ e

Depends on / 依赖: G.deleteEdges, Reachable, Sym2.lift, deleteEdges, reachable_comm
-/
def IsBridge (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun v w => ¬ (G.deleteEdges {e}).Reachable v w, by simp [reachable_comm]⟩ e

/--
theorem `isBridge_iff` / 定理 `isBridge_iff`

English:
theorem isBridge_iff
  given: {u v : V}
  proof: .rfl

中文:
定理 isBridge_iff
  条件: {u v : V}
  证明: .rfl
-/
theorem isBridge_iff {u v : V} :
    G.IsBridge s(u, v) ↔ ¬ (G.deleteEdges {s(u, v)}).Reachable u v := .rfl

/--
lemma `IsBridge.of_not_reachable` / 引理 `IsBridge.of_not_reachable`

English:
lemma IsBridge.of_not_reachable
  given: (huv : ¬ G.Reachable u v)
  proof: fun h => huv h.mono deleteEdges_le _

中文:
引理 IsBridge.of_not_reachable
  条件: (huv : ¬ G.Reachable u v)
  证明: fun h => huv h.mono deleteEdges_le _
-/
@[simp] lemma IsBridge.of_not_reachable (huv : ¬ G.Reachable u v) :
G.IsBridge s(u, v) := fun h => huv h.mono deleteEdges_le _

/--
theorem `IsBridge.reachable_iff_adj` / 定理 `IsBridge.reachable_iff_adj`

English:
theorem IsBridge.reachable_iff_adj
  given: (h : G.IsBridge s(u, v))
  statement: G.Reachable u v ↔ G.Adj u v
  proof: by
  refine ⟨fun hreach => G.mem_edgeSet.mp ?_, Adj.reachable⟩
.lt_of_ne by grind [isBridge_iff] have : G.deleteEdges {s(u, v)} < G := deleteEdges_le _
  grind [edgeSet_strict_mono this, edgeSet_deleteEdges]

中文:
定理 IsBridge.reachable_iff_adj
  条件: (h : G.IsBridge s(u, v))
  结论: G.Reachable u v ↔ G.Adj u v
  证明: by
  refine ⟨fun hreach => G.mem_edgeSet.mp ?_, Adj.reachable⟩
.lt_of_ne by grind [isBridge_iff] have : G.deleteEdges {s(u, v)} < G := deleteEdges_le _
  grind [edgeSet_strict_mono this, edgeSet_deleteEdges]

Depends on / 依赖: Adj.reachable, G.deleteEdges, G.mem_edgeSet.mp, deleteEdges, deleteEdges_le, edgeSet_deleteEdges, edgeSet_strict_mono, hreach, isBridge_iff, lt_of_ne, mem_edgeSet, reachable
-/
theorem IsBridge.reachable_iff_adj (h : G.IsBridge s(u, v)) : G.Reachable u v ↔ G.Adj u v := by
  refine ⟨fun hreach => G.mem_edgeSet.mp ?_, Adj.reachable⟩
.lt_of_ne by grind [isBridge_iff] have : G.deleteEdges {s(u, v)} < G := deleteEdges_le _
  grind [edgeSet_strict_mono this, edgeSet_deleteEdges]

/--
lemma `IsBridge.nontrivial` / 引理 `IsBridge.nontrivial`

English:
lemma IsBridge.nontrivial
  given: {e : Sym2 V} (he : G.IsBridge e)
  statement: Nontrivial V
  proof: by
  cases e with | h u v; exact ⟨u, v, by rintro rfl; simp [IsBridge] at he⟩

中文:
引理 IsBridge.nontrivial
  条件: {e : Sym2 V} (he : G.IsBridge e)
  结论: Nontrivial V
  证明: by
  cases e with | h u v; exact ⟨u, v, by rintro rfl; simp [IsBridge] at he⟩

Depends on / 依赖: IsBridge
-/
lemma IsBridge.nontrivial {e : Sym2 V} (he : G.IsBridge e) : Nontrivial V := by
  cases e with | h u v; exact ⟨u, v, by rintro rfl; simp [IsBridge] at he⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `reachable_deleteEdges_iff_exists_walk` / 定理 `reachable_deleteEdges_iff_exists_walk`

English:
theorem reachable_deleteEdges_iff_exists_walk
  given: {v w v' w' : V}
  proof: by
  constructor
  · rintro ⟨p⟩
    use p.map (.ofLE (by simp))
    simp_rw [Walk.edges_map, List.mem_map, Hom.ofLE_apply, Sym2.map_id', id]
    rintro ⟨e, h, rfl⟩
    simpa using p.edges_subset_edgeSet h
  · rintro ⟨p, h⟩
    refine ⟨p.transfer _ fun e ep => ?_⟩
    rw [edgeSet_deleteEdges]
    exa

中文:
定理 reachable_deleteEdges_iff_exists_walk
  条件: {v w v' w' : V}
  证明: by
  constructor
  · rintro ⟨p⟩
    use p.map (.ofLE (by simp))
    simp_rw [Walk.edges_map, List.mem_map, Hom.ofLE_apply, Sym2.map_id', id]
    rintro ⟨e, h, rfl⟩
    simpa using p.edges_subset_edgeSet h
  · rintro ⟨p, h⟩
    refine ⟨p.transfer _ fun e ep => ?_⟩
    rw [edgeSet_deleteEdges]
    exa

Depends on / 依赖: Hom.ofLE_apply, List.mem_map, Sym2.map_id, Walk.edges_map, edgeSet_deleteEdges, edges_map, edges_subset_edgeSet, map_id, mem_map, ofLE_apply, p.edges_subset_edgeSet, p.map, p.transfer, simp_rw, transfer
-/
theorem reachable_deleteEdges_iff_exists_walk {v w v' w' : V} :
    (G.deleteEdges {s(v, w)}).Reachable v' w' ↔ exists p : G.Walk v' w', s(v, w) ∉ p.edges := by
  constructor
  · rintro ⟨p⟩
    use p.map (.ofLE (by simp))
    simp_rw [Walk.edges_map, List.mem_map, Hom.ofLE_apply, Sym2.map_id', id]
    rintro ⟨e, h, rfl⟩
    simpa using p.edges_subset_edgeSet h
  · rintro ⟨p, h⟩
    refine ⟨p.transfer _ fun e ep => ?_⟩
    rw [edgeSet_deleteEdges]
    exact ⟨p.edges_subset_edgeSet ep, fun h' => h (h' ▸ ep)⟩

@[deprecated (since := "2026-03-18")]
alias reachable_delete_edges_iff_exists_walk := reachable_deleteEdges_iff_exists_walk

/--
theorem `isBridge_iff_forall_walk_mem_edges` / 定理 `isBridge_iff_forall_walk_mem_edges`

English:
theorem isBridge_iff_forall_walk_mem_edges
  given: {v w : V}
  proof: by
  rw [isBridge_iff]; rw [reachable_deleteEdges_iff_exists_walk]; rw [not_exists_not]

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_adj_and_forall_walk_mem_edges := isBridge_iff_forall_walk_mem_edges

中文:
定理 isBridge_iff_forall_walk_mem_edges
  条件: {v w : V}
  证明: by
  rw [isBridge_iff]; rw [reachable_deleteEdges_iff_exists_walk]; rw [not_exists_not]

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_adj_and_forall_walk_mem_edges := isBridge_iff_forall_walk_mem_edges

Depends on / 依赖: isBridge_iff, not_exists_not, reachable_deleteEdges_iff_exists_walk
-/
theorem isBridge_iff_forall_walk_mem_edges {v w : V} :
    G.IsBridge s(v, w) ↔ forall p : G.Walk v w, s(v, w) in p.edges := by
  rw [isBridge_iff]; rw [reachable_deleteEdges_iff_exists_walk]; rw [not_exists_not]

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_adj_and_forall_walk_mem_edges := isBridge_iff_forall_walk_mem_edges

/--
theorem `reachable_deleteEdges_iff_exists_cycle.aux` / 定理 `reachable_deleteEdges_iff_exists_cycle.aux`

English:
theorem reachable_deleteEdges_iff_exists_cycle.aux
  statement: [DecidableEq V] {u v w : V}
  proof: by
  have hv := c.fst_mem_support_of_mem_edges he
  -- decompose c into
  -- puw pwv pvu
  -- u ----> w ----> v ----> u
  let puw := (c.takeUntil v hv).takeUntil w hw
  let pwv := (c.takeUntil v hv).dropUntil w hw
  let pvu := c.dropUntil v hv
  have : c = (puw.append pwv).append pvu := by simp [puw

中文:
定理 reachable_deleteEdges_iff_exists_cycle.aux
  结论: [DecidableEq V] {u v w : V}
  证明: by
  have hv := c.fst_mem_support_of_mem_edges he
  -- decompose c into
  -- puw pwv pvu
  -- u ----> w ----> v ----> u
  let puw := (c.takeUntil v hv).takeUntil w hw
  let pwv := (c.takeUntil v hv).dropUntil w hw
  let pvu := c.dropUntil v hv
  have : c = (puw.append pwv).append pvu := by simp [puw

Depends on / 依赖: c.fst_mem_support_of_mem_edges, fst_mem_support_of_mem_edges
-/
theorem reachable_deleteEdges_iff_exists_cycle.aux [DecidableEq V] {u v w : V}
    (hb : forall p : G.Walk v w, s(v, w) in p.edges) (c : G.Walk u u) (hc : c.IsTrail)
    (he : s(v, w) in c.edges)
    (hw : w in (c.takeUntil v (c.fst_mem_support_of_mem_edges he)).support) : False := by
  have hv := c.fst_mem_support_of_mem_edges he
  -- decompose c into
  -- puw pwv pvu
  -- u ----> w ----> v ----> u
  let puw := (c.takeUntil v hv).takeUntil w hw
  let pwv := (c.takeUntil v hv).dropUntil w hw
  let pvu := c.dropUntil v hv
  have : c = (puw.append pwv).append pvu := by simp [puw, pwv, pvu]
  -- We have two walks from v to w
  -- pvu puw
  -- v ----> u ----> w
  -- | ^
  -- `-------------'
  -- pwv.reverse
  -- so they both contain the edge s(v, w), but that's a contradiction since c is a trail.
  have hbq := hb (pvu.append puw)
  have hpq' := hb pwv.reverse
  rw [Walk.edges_reverse]; rw [List.mem_reverse] at hpq'
  rw [Walk.isTrail_def]; rw [this]; rw [Walk.edges_append]; rw [Walk.edges_append]; rw [List.nodup_append_comm]; rw [← List.append_assoc]; rw [← Walk.edges_append] at hc
  exact List.disjoint_of_nodup_append hc hbq hpq'

/--
theorem `adj_and_reachable_delete_edges_iff_exists_cycle` / 定理 `adj_and_reachable_delete_edges_iff_exists_cycle`

English:
theorem adj_and_reachable_delete_edges_iff_exists_cycle
  given: {v w : V}
  proof: by
  classical
  rw [reachable_deleteEdges_iff_exists_walk]
  constructor
  · rintro ⟨h, p, hp⟩
    refine ⟨w, Walk.cons h.symm p.toPath, ?_, ?_⟩
    · apply Path.cons_isCycle
      rw [Sym2.eq_swap]
      intro h
      cases hp (Walk.edges_toPath_subset_edges p h)
    · simp
  · rintro ⟨u, c, hc, h

中文:
定理 adj_and_reachable_delete_edges_iff_exists_cycle
  条件: {v w : V}
  证明: by
  classical
  rw [reachable_deleteEdges_iff_exists_walk]
  constructor
  · rintro ⟨h, p, hp⟩
    refine ⟨w, Walk.cons h.symm p.toPath, ?_, ?_⟩
    · apply Path.cons_isCycle
      rw [Sym2.eq_swap]
      intro h
      cases hp (Walk.edges_toPath_subset_edges p h)
    · simp
  · rintro ⟨u, c, hc, h

Depends on / 依赖: G.Walk, Path.cons_isCycle, Sym2.eq_swap, Walk.cons, Walk.edges_toPath_subset_edges, Walk.fst_mem_support_of_mem_edges, adj_of_mem_edges, c.adj_of_mem_edges, c.support, classical, cons_isCycle, edges_toPath_subset_edges, eq_swap, fst_mem_support_of_mem_edges, h.symm, p.edges, p.reverse, p.toPath, reacha, reachable_deleteEdges_iff_exists_walk
-/
theorem adj_and_reachable_delete_edges_iff_exists_cycle {v w : V} :
    G.Adj v w ∧ (G.deleteEdges {s(v, w)}).Reachable v w ↔
      exists (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) in p.edges := by
  classical
  rw [reachable_deleteEdges_iff_exists_walk]
  constructor
  · rintro ⟨h, p, hp⟩
    refine ⟨w, Walk.cons h.symm p.toPath, ?_, ?_⟩
    · apply Path.cons_isCycle
      rw [Sym2.eq_swap]
      intro h
      cases hp (Walk.edges_toPath_subset_edges p h)
    · simp
  · rintro ⟨u, c, hc, he⟩
    refine ⟨c.adj_of_mem_edges he, ?_⟩
    by_contra! hb
    have hb' : forall p : G.Walk w v, s(w, v) in p.edges := by
      intro p
      simpa [Sym2.eq_swap] using hb p.reverse
    have hvc : v in c.support := Walk.fst_mem_support_of_mem_edges c he
    refine reachable_deleteEdges_iff_exists_cycle.aux hb' (c.rotate v hvc) (hc.isTrail.rotate hvc)
      ?_ (Walk.start_mem_support _)
    rwa [(c.rotate_edges v hvc).mem_iff, Sym2.eq_swap]

/--
theorem `isBridge_iff_forall_cycle_notMem` / 定理 `isBridge_iff_forall_cycle_notMem`

English:
theorem isBridge_iff_forall_cycle_notMem
  given: {e : Sym2 V} (he : e in G.edgeSet)
  proof: by
  obtain ⟨v, w⟩ := e
  contrapose
  simp_all [isBridge_iff, ← adj_and_reachable_delete_edges_iff_exists_cycle]

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_adj_and_forall_cycle_notMem := isBridge_iff_forall_cycle_notMem

中文:
定理 isBridge_iff_forall_cycle_notMem
  条件: {e : Sym2 V} (he : e in G.edgeSet)
  证明: by
  obtain ⟨v, w⟩ := e
  contrapose
  simp_all [isBridge_iff, ← adj_and_reachable_delete_edges_iff_exists_cycle]

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_adj_and_forall_cycle_notMem := isBridge_iff_forall_cycle_notMem

Depends on / 依赖: adj_and_reachable_delete_edges_iff_exists_cycle, contrapose, isBridge_iff
-/
theorem isBridge_iff_forall_cycle_notMem {e : Sym2 V} (he : e in G.edgeSet) :
    G.IsBridge e ↔ forall ⦃u : V⦄ (p : G.Walk u u), p.IsCycle -> e ∉ p.edges := by
  obtain ⟨v, w⟩ := e
  contrapose
  simp_all [isBridge_iff, ← adj_and_reachable_delete_edges_iff_exists_cycle]

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_adj_and_forall_cycle_notMem := isBridge_iff_forall_cycle_notMem

/--
lemma `IsBridge.notMem_edges_of_isCycle` / 引理 `IsBridge.notMem_edges_of_isCycle`

English:
lemma IsBridge.notMem_edges_of_isCycle
  statement: {e : Sym2 V} {u : V} {p : G.Walk u u}
  proof: fun hep => (isBridge_iff_forall_cycle_notMem <| p.edges_subset_edgeSet hep).mp he _ hp hep

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_mem_and_forall_cycle_notMem := isBridge_iff_forall_cycle_notMem

中文:
引理 IsBridge.notMem_edges_of_isCycle
  结论: {e : Sym2 V} {u : V} {p : G.Walk u u}
  证明: fun hep => (isBridge_iff_forall_cycle_notMem <| p.edges_subset_edgeSet hep).mp he _ hp hep

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_mem_and_forall_cycle_notMem := isBridge_iff_forall_cycle_notMem

Depends on / 依赖: edges_subset_edgeSet, isBridge_iff_forall_cycle_notMem, p.edges_subset_edgeSet
-/
lemma IsBridge.notMem_edges_of_isCycle {e : Sym2 V} {u : V} {p : G.Walk u u}
    (he : G.IsBridge e) (hp : p.IsCycle) : e ∉ p.edges :=
  fun hep => (isBridge_iff_forall_cycle_notMem <| p.edges_subset_edgeSet hep).mp he _ hp hep

@[deprecated (since := "2026-06-04")]
alias isBridge_iff_mem_and_forall_cycle_notMem := isBridge_iff_forall_cycle_notMem

/--
lemma `Connected.connected_delete_edge_of_not_isBridge` / 引理 `Connected.connected_delete_edge_of_not_isBridge`

English:
lemma Connected.connected_delete_edge_of_not_isBridge
  statement: (hG : G.Connected) {x y : V}
  proof: by
  classical
  simp only [isBridge_iff, not_not] at h
obtain hxy | hxy := em' G.Adj x y
  · rwa [deleteEdges, Disjoint.sdiff_eq_left (by simpa)]
  refine (connected_iff_exists_forall_reachable _).2 ⟨x, fun w => ?_⟩
  obtain ⟨P, hP⟩ := hG.exists_isPath w x
obtain heP | heP := em' s(x, y) in P.edges

中文:
引理 Connected.connected_delete_edge_of_not_isBridge
  结论: (hG : G.Connected) {x y : V}
  证明: by
  classical
  simp only [isBridge_iff, not_not] at h
obtain hxy | hxy := em' G.Adj x y
  · rwa [deleteEdges, Disjoint.sdiff_eq_left (by simpa)]
  refine (connected_iff_exists_forall_reachable _).2 ⟨x, fun w => ?_⟩
  obtain ⟨P, hP⟩ := hG.exists_isPath w x
obtain heP | heP := em' s(x, y) in P.edges

Depends on / 依赖: Disjoint, Disjoint.sdiff_eq_left, G.Adj, P.edges, P.snd_mem_support_of_mem_edges, P.takeUntil, P.toDeleteEdges, Walk.endpoint_notMem_support_takeUntil, classical, connected_iff_exists_forall_reachable, deleteEdges, endpoint_notMem_support_takeUntil, exists_isPath, hG.exists_isPath, hxy.ne, isBridge_iff, not_not, reverse, sdiff_eq_left, snd_mem_support_of_mem_edges
-/
lemma Connected.connected_delete_edge_of_not_isBridge (hG : G.Connected) {x y : V}
    (h : ¬ G.IsBridge s(x, y)) : (G.deleteEdges {s(x, y)}).Connected := by
  classical
  simp only [isBridge_iff, not_not] at h
obtain hxy | hxy := em' G.Adj x y
  · rwa [deleteEdges, Disjoint.sdiff_eq_left (by simpa)]
  refine (connected_iff_exists_forall_reachable _).2 ⟨x, fun w => ?_⟩
  obtain ⟨P, hP⟩ := hG.exists_isPath w x
obtain heP | heP := em' s(x, y) in P.edges
  · exact ⟨(P.toDeleteEdges {s(x, y)} (by grind)).reverse⟩
  have hyP := P.snd_mem_support_of_mem_edges heP
  let P₁ := P.takeUntil y hyP
  have hxP₁ := Walk.endpoint_notMem_support_takeUntil hP hyP hxy.ne
have heP₁ : s(x, y) ∉ P₁.edges := fun h => hxP₁ P₁.fst_mem_support_of_mem_edges h
  exact h.trans (.symm ⟨P₁.toDeleteEdges {s(x, y)} (by grind)⟩)

/--
theorem `IsBridge.anti` / 定理 `IsBridge.anti`

English:
theorem IsBridge.anti
  given: {G' : SimpleGraph V} {e : Sym2 V} (hG : G <= G') (h : G'.IsBridge e)
  proof: by obtain ⟨a, b⟩ := e; rw [isBridge_iff] at ⊢ h; grw [hG]; assumption

@[deprecated (since := "2026-05-16")] alias IsBridge.anti_of_mem_edgeSet := IsBridge.anti

中文:
定理 IsBridge.anti
  条件: {G' : SimpleGraph V} {e : Sym2 V} (hG : G <= G') (h : G'.IsBridge e)
  证明: by obtain ⟨a, b⟩ := e; rw [isBridge_iff] at ⊢ h; grw [hG]; assumption

@[deprecated (since := "2026-05-16")] alias IsBridge.anti_of_mem_edgeSet := IsBridge.anti

Depends on / 依赖: isBridge_iff
-/
theorem IsBridge.anti {G' : SimpleGraph V} {e : Sym2 V} (hG : G <= G') (h : G'.IsBridge e) :
    G.IsBridge e := by obtain ⟨a, b⟩ := e; rw [isBridge_iff] at ⊢ h; grw [hG]; assumption

@[deprecated (since := "2026-05-16")] alias IsBridge.anti_of_mem_edgeSet := IsBridge.anti

/--
lemma `isBridge_sup_edge` / 引理 `isBridge_sup_edge`

English:
lemma isBridge_sup_edge
  statement: (G ⊔ edge u v).IsBridge s(u, v) ↔ G.IsBridge s(u, v)
  proof: by
  simp [isBridge_iff, deleteEdges_sup]

中文:
引理 isBridge_sup_edge
  结论: (G ⊔ edge u v).IsBridge s(u, v) ↔ G.IsBridge s(u, v)
  证明: by
  simp [isBridge_iff, deleteEdges_sup]
-/
@[simp] lemma isBridge_sup_edge : (G ⊔ edge u v).IsBridge s(u, v) ↔ G.IsBridge s(u, v) := by
  simp [isBridge_iff, deleteEdges_sup]

/--
lemma `isBridge_deleteEdges_singleton` / 引理 `isBridge_deleteEdges_singleton`

English:
lemma isBridge_deleteEdges_singleton
  given: {e : Sym2 V}
  proof: by
  induction e with | h u v; simp [isBridge_iff]

@[deprecated "Use `isBridge_sup_edge` and `IsBridge.of_not_reachable`" (since := "2026-06-04")]

中文:
引理 isBridge_deleteEdges_singleton
  条件: {e : Sym2 V}
  证明: by
  induction e with | h u v; simp [isBridge_iff]

@[deprecated "Use `isBridge_sup_edge` and `IsBridge.of_not_reachable`" (since := "2026-06-04")]
-/
@[simp] lemma isBridge_deleteEdges_singleton {e : Sym2 V} :
    (G.deleteEdges {e}).IsBridge e ↔ G.IsBridge e := by
  induction e with | h u v; simp [isBridge_iff]

@[deprecated "Use `isBridge_sup_edge` and `IsBridge.of_not_reachable`" (since := "2026-06-04")]
/--
theorem `IsBridge.sup_edge_of_not_reachable` / 定理 `IsBridge.sup_edge_of_not_reachable`

English:
theorem IsBridge.sup_edge_of_not_reachable
  given: {u v : V} (h : ¬G.Reachable u v)
  proof: isBridge_sup_edge.mpr (of_not_reachable h)

@[deprecated (since := "2026-03-18")]
alias IsBridge.sup_fromEdgeSet_of_not_reachable := IsBridge.sup_edge_of_not_reachable

中文:
定理 IsBridge.sup_edge_of_not_reachable
  条件: {u v : V} (h : ¬G.Reachable u v)
  证明: isBridge_sup_edge.mpr (of_not_reachable h)

@[deprecated (since := "2026-03-18")]
alias IsBridge.sup_fromEdgeSet_of_not_reachable := IsBridge.sup_edge_of_not_reachable

Depends on / 依赖: isBridge_sup_edge, isBridge_sup_edge.mpr, of_not_reachable
-/
theorem IsBridge.sup_edge_of_not_reachable {u v : V} (h : ¬G.Reachable u v) :
    (G ⊔ edge u v).IsBridge s(u, v) := isBridge_sup_edge.mpr (of_not_reachable h)

@[deprecated (since := "2026-03-18")]
alias IsBridge.sup_fromEdgeSet_of_not_reachable := IsBridge.sup_edge_of_not_reachable

/--
theorem `IsBridge.sup_edge_of_not_reachable_of_isBridge` / 定理 `IsBridge.sup_edge_of_not_reachable_of_isBridge`

English:
theorem IsBridge.sup_edge_of_not_reachable_of_isBridge
  statement: {u v : V} {e : Sym2 V}
  proof: by
  refine (isBridge_iff_forall_cycle_notMem (edgeSet_mono le_sup_left he)).mpr ?_
  refine fun w p hp hpe => (isBridge_iff_forall_cycle_notMem he).mp hb
    (p.transfer G fun e' he' => ?_) (hp.transfer _) (Walk.edges_transfer p _ ▸ hpe)
.elim .elim id fun h' => h ?_ refine edgeSet_sup .. ▸ Walk.ed

中文:
定理 IsBridge.sup_edge_of_not_reachable_of_isBridge
  结论: {u v : V} {e : Sym2 V}
  证明: by
  refine (isBridge_iff_forall_cycle_notMem (edgeSet_mono le_sup_left he)).mpr ?_
  refine fun w p hp hpe => (isBridge_iff_forall_cycle_notMem he).mp hb
    (p.transfer G fun e' he' => ?_) (hp.transfer _) (Walk.edges_transfer p _ ▸ hpe)
.elim .elim id fun h' => h ?_ refine edgeSet_sup .. ▸ Walk.ed

Depends on / 依赖: Walk.edges_subset_edgeSet, Walk.edges_transfer, adj_and_reachable_delete_edges_iff_exists_cycle, adj_and_reachable_delete_edges_iff_exists_cycle.mpr, edgeSet_mono, edgeSet_sup, edges_subset_edgeSet, edges_transfer, hp.transfer, isBridge_iff_forall_cycle_notMem, le_rfl, le_sup_left, p.transfer, sdiff_le_iff, transfer
-/
theorem IsBridge.sup_edge_of_not_reachable_of_isBridge {u v : V} {e : Sym2 V}
    (h : ¬G.Reachable u v) (hb : G.IsBridge e) (he : e in G.edgeSet) :
    (G ⊔ edge u v).IsBridge e := by
  refine (isBridge_iff_forall_cycle_notMem (edgeSet_mono le_sup_left he)).mpr ?_
  refine fun w p hp hpe => (isBridge_iff_forall_cycle_notMem he).mp hb
    (p.transfer G fun e' he' => ?_) (hp.transfer _) (Walk.edges_transfer p _ ▸ hpe)
.elim .elim id fun h' => h ?_ refine edgeSet_sup .. ▸ Walk.edges_subset_edgeSet _ he'
exact .mono (sdiff_le_iff'.mpr le_rfl)
.right adj_and_reachable_delete_edges_iff_exists_cycle.mpr ⟨_, p, by simp_all⟩

@[deprecated (since := "2026-03-18")]
alias IsBridge.sup_fromEdgeSet_of_not_reachable_of_isBridge :=
  IsBridge.sup_edge_of_not_reachable_of_isBridge

end BridgeEdges

/-!
### 2-reachability

In this section, we prove results about 2-connected components of a graph, but without naming them.
-/

namespace Walk
variable {u v x y : V} {w : G.Walk u v}

/--
lemma `exists_mem_edges_of_not_reachable_deleteEdges` / 引理 `exists_mem_edges_of_not_reachable_deleteEdges`

English:
lemma exists_mem_edges_of_not_reachable_deleteEdges
  statement: (w : G.Walk u v) {s : Set (Sym2 V)}
  proof: by
contrapose! huv; exact ⟨w.toDeleteEdges _ fun _ => imp_not_comm.1 huv _⟩

中文:
引理 exists_mem_edges_of_not_reachable_deleteEdges
  结论: (w : G.Walk u v) {s : Set (Sym2 V)}
  证明: by
contrapose! huv; exact ⟨w.toDeleteEdges _ fun _ => imp_not_comm.1 huv _⟩

Depends on / 依赖: contrapose, imp_not_comm, toDeleteEdges, w.toDeleteEdges
-/
lemma exists_mem_edges_of_not_reachable_deleteEdges (w : G.Walk u v) {s : Set (Sym2 V)}
    (huv : ¬ (G.deleteEdges s).Reachable u v) : exists e in s, e in w.edges := by
contrapose! huv; exact ⟨w.toDeleteEdges _ fun _ => imp_not_comm.1 huv _⟩

/--
lemma `mem_edges_of_not_reachable_deleteEdges` / 引理 `mem_edges_of_not_reachable_deleteEdges`

English:
lemma mem_edges_of_not_reachable_deleteEdges
  statement: (w : G.Walk u v) {e : Sym2 V}
  proof: by
  simpa using w.exists_mem_edges_of_not_reachable_deleteEdges huv

中文:
引理 mem_edges_of_not_reachable_deleteEdges
  结论: (w : G.Walk u v) {e : Sym2 V}
  证明: by
  simpa using w.exists_mem_edges_of_not_reachable_deleteEdges huv

Depends on / 依赖: exists_mem_edges_of_not_reachable_deleteEdges, w.exists_mem_edges_of_not_reachable_deleteEdges
-/
lemma mem_edges_of_not_reachable_deleteEdges (w : G.Walk u v) {e : Sym2 V}
    (huv : ¬ (G.deleteEdges {e}).Reachable u v) : e in w.edges := by
  simpa using w.exists_mem_edges_of_not_reachable_deleteEdges huv

/--
lemma `IsTrail.not_mem_edges_of_not_reachable` / 引理 `IsTrail.not_mem_edges_of_not_reachable`

English:
lemma IsTrail.not_mem_edges_of_not_reachable
  statement: (hw : w.IsTrail)
  proof: by
  classical
  exact fun hxy => hw.disjoint_edges_takeUntil_dropUntil (w.snd_mem_support_of_mem_edges hxy)
    ((w.takeUntil y _).mem_edges_of_not_reachable_deleteEdges huy)
    (by simpa using (w.dropUntil y _).reverse.mem_edges_of_not_reachable_deleteEdges hvy)

中文:
引理 IsTrail.not_mem_edges_of_not_reachable
  结论: (hw : w.IsTrail)
  证明: by
  classical
  exact fun hxy => hw.disjoint_edges_takeUntil_dropUntil (w.snd_mem_support_of_mem_edges hxy)
    ((w.takeUntil y _).mem_edges_of_not_reachable_deleteEdges huy)
    (by simpa using (w.dropUntil y _).reverse.mem_edges_of_not_reachable_deleteEdges hvy)

Depends on / 依赖: classical, disjoint_edges_takeUntil_dropUntil, dropUntil, hw.disjoint_edges_takeUntil_dropUntil, mem_edges_of_not_reachable_deleteEdges, reverse, reverse.mem_edges_of_not_reachable_deleteEdges, snd_mem_support_of_mem_edges, takeUntil, w.dropUntil, w.snd_mem_support_of_mem_edges, w.takeUntil
-/
lemma IsTrail.not_mem_edges_of_not_reachable (hw : w.IsTrail)
    (huy : ¬ (G.deleteEdges {s(x, y)}).Reachable u y)
    (hvy : ¬ (G.deleteEdges {s(x, y)}).Reachable v y) : s(x, y) ∉ w.edges := by
  classical
  exact fun hxy => hw.disjoint_edges_takeUntil_dropUntil (w.snd_mem_support_of_mem_edges hxy)
    ((w.takeUntil y _).mem_edges_of_not_reachable_deleteEdges huy)
    (by simpa using (w.dropUntil y _).reverse.mem_edges_of_not_reachable_deleteEdges hvy)

/--
lemma `IsTrail.not_mem_support_of_not_reachable` / 引理 `IsTrail.not_mem_support_of_not_reachable`

English:
lemma IsTrail.not_mem_support_of_not_reachable
  statement: (hw : w.IsTrail)
  proof: by
  classical
exact fun hy => hw.not_mem_edges_of_not_reachable huy hvy w.edges_takeUntil_subset_edges hy
    mem_edges_of_not_reachable_deleteEdges (w.takeUntil y hy) huy

中文:
引理 IsTrail.not_mem_support_of_not_reachable
  结论: (hw : w.IsTrail)
  证明: by
  classical
exact fun hy => hw.not_mem_edges_of_not_reachable huy hvy w.edges_takeUntil_subset_edges hy
    mem_edges_of_not_reachable_deleteEdges (w.takeUntil y hy) huy

Depends on / 依赖: classical, edges_takeUntil_subset_edges, hw.not_mem_edges_of_not_reachable, mem_edges_of_not_reachable_deleteEdges, not_mem_edges_of_not_reachable, takeUntil, w.edges_takeUntil_subset_edges, w.takeUntil
-/
lemma IsTrail.not_mem_support_of_not_reachable (hw : w.IsTrail)
    (huy : ¬ (G.deleteEdges {s(x, y)}).Reachable u y)
    (hvy : ¬ (G.deleteEdges {s(x, y)}).Reachable v y) : y ∉ w.support := by
  classical
exact fun hy => hw.not_mem_edges_of_not_reachable huy hvy w.edges_takeUntil_subset_edges hy
    mem_edges_of_not_reachable_deleteEdges (w.takeUntil y hy) huy

/--
lemma `IsTrail.not_mem_support_of_subsingleton_neighborSet` / 引理 `IsTrail.not_mem_support_of_subsingleton_neighborSet`

English:
lemma IsTrail.not_mem_support_of_subsingleton_neighborSet
  statement: (hw : w.IsTrail) (hxu : x != u)
  proof: by
  rintro hxw
  obtain ⟨y, -, hxy⟩ := adj_of_mem_walk_support w (by rintro ⟨⟩; simp_all) hxw
  refine hw.not_mem_support_of_not_reachable (x := y) ?_ ?_ hxw <;>
  · rintro ⟨p⟩
    obtain ⟨hx₂, -, hy₂⟩ : G.Adj x p.penultimate ∧ _ ∧ ¬p.penultimate = y := by
      simpa using p.reverse.adj_snd (not_n

中文:
引理 IsTrail.not_mem_support_of_subsingleton_neighborSet
  结论: (hw : w.IsTrail) (hxu : x != u)
  证明: by
  rintro hxw
  obtain ⟨y, -, hxy⟩ := adj_of_mem_walk_support w (by rintro ⟨⟩; simp_all) hxw
  refine hw.not_mem_support_of_not_reachable (x := y) ?_ ?_ hxw <;>
  · rintro ⟨p⟩
    obtain ⟨hx₂, -, hy₂⟩ : G.Adj x p.penultimate ∧ _ ∧ ¬p.penultimate = y := by
      simpa using p.reverse.adj_snd (not_n

Depends on / 依赖: G.Adj, adj_of_mem_walk_support, adj_snd, hw.not_mem_support_of_not_reachable, not_mem_support_of_not_reachable, not_nil_of_ne, p.penultimate, p.reverse.adj_snd, penultimate, reverse
-/
lemma IsTrail.not_mem_support_of_subsingleton_neighborSet (hw : w.IsTrail) (hxu : x != u)
    (hxv : x != v) (hx : (G.neighborSet x).Subsingleton) : x ∉ w.support := by
  rintro hxw
  obtain ⟨y, -, hxy⟩ := adj_of_mem_walk_support w (by rintro ⟨⟩; simp_all) hxw
  refine hw.not_mem_support_of_not_reachable (x := y) ?_ ?_ hxw <;>
  · rintro ⟨p⟩
    obtain ⟨hx₂, -, hy₂⟩ : G.Adj x p.penultimate ∧ _ ∧ ¬p.penultimate = y := by
      simpa using p.reverse.adj_snd (not_nil_of_ne ‹_›)
exact hy₂ hx hx₂ hxy

end Walk

/--
lemma `Preconnected.induce_of_degree_eq_one` / 引理 `Preconnected.induce_of_degree_eq_one`

English:
lemma Preconnected.induce_of_degree_eq_one
  statement: (hG : G.Preconnected) {s : Set V}
  proof: by
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨p, hp⟩ := hG.exists_isPath u v
  constructor
  convert! p.induce s _
  rintro w hwp
  by_contra hws
  exact hp.not_mem_support_of_subsingleton_neighborSet (by grind) (by grind) (hs _ hws) hwp

中文:
引理 Preconnected.induce_of_degree_eq_one
  结论: (hG : G.Preconnected) {s : Set V}
  证明: by
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨p, hp⟩ := hG.exists_isPath u v
  constructor
  convert! p.induce s _
  rintro w hwp
  by_contra hws
  exact hp.not_mem_support_of_subsingleton_neighborSet (by grind) (by grind) (hs _ hws) hwp

Depends on / 依赖: convert, exists_isPath, hG.exists_isPath, hp.not_mem_support_of_subsingleton_neighborSet, induce, not_mem_support_of_subsingleton_neighborSet, p.induce
-/
lemma Preconnected.induce_of_degree_eq_one (hG : G.Preconnected) {s : Set V}
    (hs : forall v ∉ s, (G.neighborSet v).Subsingleton) : (G.induce s).Preconnected := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨p, hp⟩ := hG.exists_isPath u v
  constructor
  convert! p.induce s _
  rintro w hwp
  by_contra hws
  exact hp.not_mem_support_of_subsingleton_neighborSet (by grind) (by grind) (hs _ hws) hwp

end SimpleGraph
