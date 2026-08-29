/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rémi Bottinelli, Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Mapping walks between graphs

Functions that map walks between different graphs.

## Main definitions

* `SimpleGraph.Walk.map`: The map on walks induced by a graph homomorphism
* `SimpleGraph.Walk.mapLe`: Map a walk to a supergraph
* `SimpleGraph.Walk.transfer`: Map a walk to another graph that contains its edges
* `SimpleGraph.Walk.induce`:
  Map a walk that's fully contained in a set of vertices to the subgraph induced by that set
* `SimpleGraph.Walk.toDeleteEdges`:
  Map a walk that avoids a set of edges to the subgraph with those edges deleted
* `SimpleGraph.Walk.toDeleteEdge`:
  Map a walk that avoids an edge to the subgraph with that edge deleted

## Tags
walks
-/

@[expose] public section

namespace SimpleGraph

namespace Walk

universe u v w
variable {V : Type u} {V' : Type v} {V'' : Type w}
variable {G : SimpleGraph V} {G' : SimpleGraph V'} {G'' : SimpleGraph V''}

/-! ### Mapping walks -/

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : G ->g G') {u v : V}

中文:
定义 map
  签名: (f : G ->g G') {u v : V}
-/
protected def map (f : G ->g G') {u v : V} : G.Walk u v -> G'.Walk (f u) (f v)
  | nil => nil
  | cons h p => cons (f.map_adj h) (p.map f)

variable (f : G ->g G') (f' : G' ->g G'') {u v u' v' w : V} (p : G.Walk u v)

@[simp]
/--
theorem `map_nil` / 定理 `map_nil`

English:
theorem map_nil
  statement: (nil : G.Walk u u).map f = nil
  proof: rfl

@[simp]

中文:
定理 map_nil
  结论: (nil : G.Walk u u).map f = nil
  证明: rfl

@[simp]
-/
theorem map_nil : (nil : G.Walk u u).map f = nil := rfl

@[simp]
/--
theorem `map_cons` / 定理 `map_cons`

English:
theorem map_cons
  given: {w : V} (h : G.Adj w u)
  statement: (cons h p).map f = cons (f.map_adj h) (p.map f)
  proof: rfl

@[simp]

中文:
定理 map_cons
  条件: {w : V} (h : G.Adj w u)
  结论: (cons h p).map f = cons (f.map_adj h) (p.map f)
  证明: rfl

@[simp]
-/
theorem map_cons {w : V} (h : G.Adj w u) : (cons h p).map f = cons (f.map_adj h) (p.map f) := rfl

@[simp]
/--
theorem `map_copy` / 定理 `map_copy`

English:
theorem map_copy
  given: (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 map_copy
  条件: (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem map_copy (hu : u = u') (hv : v = v') :
    (p.copy hu hv).map f = (p.map f).copy (hu ▸ rfl) (hv ▸ rfl) := by
  subst_vars
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (p : G.Walk u v)
  statement: p.map Hom.id = p
  proof: by
  induction p <;> simp [*]

@[simp]

中文:
定理 map_id
  条件: (p : G.Walk u v)
  结论: p.map Hom.id = p
  证明: by
  induction p <;> simp [*]

@[simp]
-/
theorem map_id (p : G.Walk u v) : p.map Hom.id = p := by
  induction p <;> simp [*]

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: (p.map f).map f' = p.map (f'.comp f)
  proof: by
  induction p <;> simp [*]

中文:
定理 map_map
  结论: (p.map f).map f' = p.map (f'.comp f)
  证明: by
  induction p <;> simp [*]
-/
theorem map_map : (p.map f).map f' = p.map (f'.comp f) := by
  induction p <;> simp [*]

/--
theorem `map_eq_of_eq` / 定理 `map_eq_of_eq`

English:
theorem map_eq_of_eq
  given: {f : G ->g G'} (f' : G ->g G') (h : f = f')
  proof: by
  subst_vars
  rfl

中文:
定理 map_eq_of_eq
  条件: {f : G ->g G'} (f' : G ->g G') (h : f = f')
  证明: by
  subst_vars
  rfl
-/
theorem map_eq_of_eq {f : G ->g G'} (f' : G ->g G') (h : f = f') :
    p.map f = (p.map f').copy (h ▸ rfl) (h ▸ rfl) := by
  subst_vars
  rfl

variable {p} in
@[simp]
/--
theorem `nil_map_iff` / 定理 `nil_map_iff`

English:
theorem nil_map_iff
  statement: (p.map f).Nil ↔ p.Nil
  proof: by
  cases p <;> simp

@[deprecated nil_map_iff (since := "2026-05-12")]

中文:
定理 nil_map_iff
  结论: (p.map f).Nil ↔ p.Nil
  证明: by
  cases p <;> simp

@[deprecated nil_map_iff (since := "2026-05-12")]
-/
theorem nil_map_iff : (p.map f).Nil ↔ p.Nil := by
  cases p <;> simp

@[deprecated nil_map_iff (since := "2026-05-12")]
/--
theorem `map_eq_nil_iff` / 定理 `map_eq_nil_iff`

English:
theorem map_eq_nil_iff
  given: {p : G.Walk u u}
  statement: p.map f = nil ↔ p = nil
  proof: by cases p <;> simp

@[simp]

中文:
定理 map_eq_nil_iff
  条件: {p : G.Walk u u}
  结论: p.map f = nil ↔ p = nil
  证明: by cases p <;> simp

@[simp]
-/
theorem map_eq_nil_iff {p : G.Walk u u} : p.map f = nil ↔ p = nil := by cases p <;> simp

@[simp]
/--
theorem `length_map` / 定理 `length_map`

English:
theorem length_map
  statement: (p.map f).length = p.length
  proof: by induction p <;> simp [*]

@[simp]

中文:
定理 length_map
  结论: (p.map f).length = p.length
  证明: by induction p <;> simp [*]

@[simp]
-/
theorem length_map : (p.map f).length = p.length := by induction p <;> simp [*]

@[simp]
/--
theorem `map_append` / 定理 `map_append`

English:
theorem map_append
  given: {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  proof: by induction p <;> simp [*]

@[simp]

中文:
定理 map_append
  条件: {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  证明: by induction p <;> simp [*]

@[simp]
-/
theorem map_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).map f = (p.map f).append (q.map f) := by induction p <;> simp [*]

@[simp]
/--
theorem `reverse_map` / 定理 `reverse_map`

English:
theorem reverse_map
  statement: (p.map f).reverse = p.reverse.map f
  proof: by induction p <;> simp [map_append, *]

@[simp]

中文:
定理 reverse_map
  结论: (p.map f).reverse = p.reverse.map f
  证明: by induction p <;> simp [map_append, *]

@[simp]

Depends on / 依赖: map_append
-/
theorem reverse_map : (p.map f).reverse = p.reverse.map f := by induction p <;> simp [map_append, *]

@[simp]
/--
theorem `support_map` / 定理 `support_map`

English:
theorem support_map
  statement: (p.map f).support = p.support.map f
  proof: by induction p <;> simp [*]

@[simp]

中文:
定理 support_map
  结论: (p.map f).support = p.support.map f
  证明: by induction p <;> simp [*]

@[simp]
-/
theorem support_map : (p.map f).support = p.support.map f := by induction p <;> simp [*]

@[simp]
/--
theorem `darts_map` / 定理 `darts_map`

English:
theorem darts_map
  statement: (p.map f).darts = p.darts.map f.mapDart
  proof: by induction p <;> simp [*]

@[simp]

中文:
定理 darts_map
  结论: (p.map f).darts = p.darts.map f.mapDart
  证明: by induction p <;> simp [*]

@[simp]
-/
theorem darts_map : (p.map f).darts = p.darts.map f.mapDart := by induction p <;> simp [*]

@[simp]
/--
theorem `edges_map` / 定理 `edges_map`

English:
theorem edges_map
  statement: (p.map f).edges = p.edges.map (Sym2.map f)
  proof: by
  induction p <;> simp [*]

@[simp]

中文:
定理 edges_map
  结论: (p.map f).edges = p.edges.map (Sym2.map f)
  证明: by
  induction p <;> simp [*]

@[simp]
-/
theorem edges_map : (p.map f).edges = p.edges.map (Sym2.map f) := by
  induction p <;> simp [*]

@[simp]
/--
theorem `edgeSet_map` / 定理 `edgeSet_map`

English:
theorem edgeSet_map
  statement: (p.map f).edgeSet = Sym2.map f '' p.edgeSet
  proof: by ext; simp

@[simp]

中文:
定理 edgeSet_map
  结论: (p.map f).edgeSet = Sym2.map f '' p.edgeSet
  证明: by ext; simp

@[simp]
-/
theorem edgeSet_map : (p.map f).edgeSet = Sym2.map f '' p.edgeSet := by ext; simp

@[simp]
/--
theorem `getVert_map` / 定理 `getVert_map`

English:
theorem getVert_map
  given: (n : Nat)
  statement: (p.map f).getVert n = f (p.getVert n)
  proof: by
  induction p generalizing n <;> cases n <;> simp [*]

中文:
定理 getVert_map
  条件: (n : 自然数)
  结论: (p.map f).getVert n = f (p.getVert n)
  证明: by
  induction p generalizing n <;> cases n <;> simp [*]

Depends on / 依赖: generalizing
-/
theorem getVert_map (n : Nat) : (p.map f).getVert n = f (p.getVert n) := by
  induction p generalizing n <;> cases n <;> simp [*]

/--
theorem `map_injective_of_injective` / 定理 `map_injective_of_injective`

English:
theorem map_injective_of_injective
  given: {f : G ->g G'} (hinj : Function.Injective f) (u v : V)
  proof: by
  intro p p' h
  induction p with
  | nil => cases p' <;> simp at h ⊢
  | cons _ _ ih =>
    cases p' with
    | nil => simp at h
    | cons _ _ =>
      simp only [map_cons, cons.injEq] at h
      grind

中文:
定理 map_injective_of_injective
  条件: {f : G ->g G'} (hinj : Function.Injective f) (u v : V)
  证明: by
  intro p p' h
  induction p with
  | nil => cases p' <;> simp at h ⊢
  | cons _ _ ih =>
    cases p' with
    | nil => simp at h
    | cons _ _ =>
      simp only [map_cons, cons.injEq] at h
      grind

Depends on / 依赖: cons.injEq, map_cons
-/
theorem map_injective_of_injective {f : G ->g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Walk.map f : G.Walk u v -> G'.Walk (f u) (f v)) := by
  intro p p' h
  induction p with
  | nil => cases p' <;> simp at h ⊢
  | cons _ _ ih =>
    cases p' with
    | nil => simp at h
    | cons _ _ =>
      simp only [map_cons, cons.injEq] at h
      grind

section mapLe

variable {G' : SimpleGraph V} (h : G <= G') {u v : V} (p : G.Walk u v)

/--
Definition of `mapLe` / `mapLe` 的定义

English:
abbreviation mapLe
  signature: : G'.Walk u v
  body: p.map (.ofLE h)

中文:
缩写 mapLe
  签名: : G'.Walk u v
  定义体: p.map (.ofLE h)

Depends on / 依赖: p.map
-/
abbrev mapLe : G'.Walk u v :=
  p.map (.ofLE h)

/--
theorem `length_mapLe` / 定理 `length_mapLe`

English:
theorem length_mapLe
  statement: (p.mapLe h).length = p.length
  proof: by
  simp

中文:
定理 length_mapLe
  结论: (p.mapLe h).length = p.length
  证明: by
  simp
-/
theorem length_mapLe : (p.mapLe h).length = p.length := by
  simp

/--
lemma `support_mapLe_eq_support` / 引理 `support_mapLe_eq_support`

English:
lemma support_mapLe_eq_support
  statement: (p.mapLe h).support = p.support
  proof: by
  simp

中文:
引理 support_mapLe_eq_support
  结论: (p.mapLe h).support = p.support
  证明: by
  simp
-/
lemma support_mapLe_eq_support : (p.mapLe h).support = p.support := by
  simp

/--
lemma `edges_mapLe_eq_edges` / 引理 `edges_mapLe_eq_edges`

English:
lemma edges_mapLe_eq_edges
  statement: (p.mapLe h).edges = p.edges
  proof: by
  simp

中文:
引理 edges_mapLe_eq_edges
  结论: (p.mapLe h).edges = p.edges
  证明: by
  simp
-/
lemma edges_mapLe_eq_edges : (p.mapLe h).edges = p.edges := by
  simp

/--
lemma `edgeSet_mapLe_eq_edgeSet` / 引理 `edgeSet_mapLe_eq_edgeSet`

English:
lemma edgeSet_mapLe_eq_edgeSet
  statement: (p.mapLe h).edgeSet = p.edgeSet
  proof: by
  simp

中文:
引理 edgeSet_mapLe_eq_edgeSet
  结论: (p.mapLe h).edgeSet = p.edgeSet
  证明: by
  simp
-/
lemma edgeSet_mapLe_eq_edgeSet : (p.mapLe h).edgeSet = p.edgeSet := by
  simp

/--
theorem `reverse_mapLe` / 定理 `reverse_mapLe`

English:
theorem reverse_mapLe
  statement: (p.mapLe h).reverse = p.reverse.mapLe h
  proof: by
  simp

中文:
定理 reverse_mapLe
  结论: (p.mapLe h).reverse = p.reverse.mapLe h
  证明: by
  simp
-/
theorem reverse_mapLe : (p.mapLe h).reverse = p.reverse.mapLe h := by
  simp

/--
theorem `mapLe_append` / 定理 `mapLe_append`

English:
theorem mapLe_append
  given: {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  proof: by
  simp

中文:
定理 mapLe_append
  条件: {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  证明: by
  simp
-/
theorem mapLe_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).mapLe h = (p.mapLe h).append (q.mapLe h) := by
  simp

end mapLe

/-! ### Transferring between graphs -/

/-- The walk `p` transferred to lie in `H`, given that `H` contains its edges. -/
@[simp]
/--
Definition of `transfer` / `transfer` 的定义

English:
definition transfer
  signature: {u v : V} (p : G.Walk u v)
  body: match p with
  | nil => nil
  | cons' u v w _ p =>
    cons (h s(u, v) (by simp)) (p.transfer H fun e he => h e (by simp [he]))

中文:
定义 transfer
  签名: {u v : V} (p : G.Walk u v)
  定义体: match p with
  | nil => nil
  | cons' u v w _ p =>
    cons (h s(u, v) (by simp)) (p.transfer H fun e he => h e (by simp [he]))
-/
protected def transfer {u v : V} (p : G.Walk u v)
    (H : SimpleGraph V) (h : forall e, e in p.edges -> e in H.edgeSet) : H.Walk u v :=
  match p with
  | nil => nil
  | cons' u v w _ p =>
    cons (h s(u, v) (by simp)) (p.transfer H fun e he => h e (by simp [he]))

/--
theorem `transfer_self` / 定理 `transfer_self`

English:
theorem transfer_self
  statement: p.transfer G p.edges_subset_edgeSet = p
  proof: by
  induction p <;> simp [*]

中文:
定理 transfer_self
  结论: p.transfer G p.edges_subset_edgeSet = p
  证明: by
  induction p <;> simp [*]
-/
theorem transfer_self : p.transfer G p.edges_subset_edgeSet = p := by
  induction p <;> simp [*]

variable {H : SimpleGraph V}

/--
theorem `transfer_eq_map_ofLE` / 定理 `transfer_eq_map_ofLE`

English:
theorem transfer_eq_map_ofLE
  given: (hp) (GH : G <= H)
  statement: p.transfer H hp = p.map (.ofLE GH)
  proof: by
  induction p <;> simp [*]

中文:
定理 transfer_eq_map_ofLE
  条件: (hp) (GH : G <= H)
  结论: p.transfer H hp = p.map (.ofLE GH)
  证明: by
  induction p <;> simp [*]
-/
theorem transfer_eq_map_ofLE (hp) (GH : G <= H) : p.transfer H hp = p.map (.ofLE GH) := by
  induction p <;> simp [*]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `edges_transfer` / 定理 `edges_transfer`

English:
theorem edges_transfer
  given: (hp)
  statement: (p.transfer H hp).edges = p.edges
  proof: by
  induction p <;> simp [*]

@[simp]

中文:
定理 edges_transfer
  条件: (hp)
  结论: (p.transfer H hp).edges = p.edges
  证明: by
  induction p <;> simp [*]

@[simp]
-/
theorem edges_transfer (hp) : (p.transfer H hp).edges = p.edges := by
  induction p <;> simp [*]

@[simp]
/--
theorem `edgeSet_transfer` / 定理 `edgeSet_transfer`

English:
theorem edgeSet_transfer
  given: (hp)
  statement: (p.transfer H hp).edgeSet = p.edgeSet
  proof: by ext; simp

中文:
定理 edgeSet_transfer
  条件: (hp)
  结论: (p.transfer H hp).edgeSet = p.edgeSet
  证明: by ext; simp
-/
theorem edgeSet_transfer (hp) : (p.transfer H hp).edgeSet = p.edgeSet := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `support_transfer` / 定理 `support_transfer`

English:
theorem support_transfer
  given: (hp)
  statement: (p.transfer H hp).support = p.support
  proof: by
  induction p <;> simp [*]

中文:
定理 support_transfer
  条件: (hp)
  结论: (p.transfer H hp).support = p.support
  证明: by
  induction p <;> simp [*]
-/
theorem support_transfer (hp) : (p.transfer H hp).support = p.support := by
  induction p <;> simp [*]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `length_transfer` / 定理 `length_transfer`

English:
theorem length_transfer
  given: (hp)
  statement: (p.transfer H hp).length = p.length
  proof: by
  induction p <;> simp [*]

@[simp]

中文:
定理 length_transfer
  条件: (hp)
  结论: (p.transfer H hp).length = p.length
  证明: by
  induction p <;> simp [*]

@[simp]
-/
theorem length_transfer (hp) : (p.transfer H hp).length = p.length := by
  induction p <;> simp [*]

@[simp]
/--
theorem `transfer_transfer` / 定理 `transfer_transfer`

English:
theorem transfer_transfer
  given: (hp) {K : SimpleGraph V} (hp')
  proof: by
  induction p <;> simp [*]

中文:
定理 transfer_transfer
  条件: (hp) {K : SimpleGraph V} (hp')
  证明: by
  induction p <;> simp [*]
-/
theorem transfer_transfer (hp) {K : SimpleGraph V} (hp') :
    (p.transfer H hp).transfer K hp' = p.transfer K (p.edges_transfer hp ▸ hp') := by
  induction p <;> simp [*]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `transfer_append` / 定理 `transfer_append`

English:
theorem transfer_append
  given: {w : V} (q : G.Walk v w) (hpq)
  proof: by
  induction p <;> simp [*]

中文:
定理 transfer_append
  条件: {w : V} (q : G.Walk v w) (hpq)
  证明: by
  induction p <;> simp [*]
-/
theorem transfer_append {w : V} (q : G.Walk v w) (hpq) :
    (p.append q).transfer H hpq =
      (p.transfer H fun e he => hpq _ (by simp [he])).append
        (q.transfer H fun e he => hpq _ (by simp [he])) := by
  induction p <;> simp [*]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `reverse_transfer` / 定理 `reverse_transfer`

English:
theorem reverse_transfer
  given: (hp)
  proof: by
  induction p <;> simp [*]

中文:
定理 reverse_transfer
  条件: (hp)
  证明: by
  induction p <;> simp [*]
-/
theorem reverse_transfer (hp) :
    (p.transfer H hp).reverse =
      p.reverse.transfer H (by simp only [edges_reverse, List.mem_reverse]; exact hp) := by
  induction p <;> simp [*]

/-! ### Inducing a walk -/

variable {s s' : Set V}

variable (s) in
/--
Definition of `induce` / `induce` 的定义

English:
definition induce
  signature: {u v : V}

中文:
定义 induce
  签名: {u v : V}
-/
protected def induce {u v : V} :
    forall (w : G.Walk u v) (hw : forall x in w.support, x in s),
      (G.induce s).Walk ⟨u, hw _ w.start_mem_support⟩ ⟨v, hw _ w.end_mem_support⟩
  | nil, hw => nil
| cons (v := u') huu' w, hw => .cons (induce_adj.2 huu') w.induce by simp_all

/--
lemma `induce_nil` / 引理 `induce_nil`

English:
lemma induce_nil
  given: (hw)
  statement: (.nil : G.Walk u u).induce s hw = .nil
  proof: rfl

中文:
引理 induce_nil
  条件: (hw)
  结论: (.nil : G.Walk u u).induce s hw = .nil
  证明: rfl
-/
@[simp] lemma induce_nil (hw) : (.nil : G.Walk u u).induce s hw = .nil := rfl

/--
lemma `induce_cons` / 引理 `induce_cons`

English:
lemma induce_cons
  given: (huu' : G.Adj u u') (w : G.Walk u' v) (hw)
  proof: rfl

中文:
引理 induce_cons
  条件: (huu' : G.Adj u u') (w : G.Walk u' v) (hw)
  证明: rfl
-/
@[simp] lemma induce_cons (huu' : G.Adj u u') (w : G.Walk u' v) (hw) :
    (w.cons huu').induce s hw = .cons (induce_adj.2 huu') (w.induce s <| by simp_all) := rfl

/--
lemma `support_induce` / 引理 `support_induce`

English:
lemma support_induce
  given: {u v : V}

中文:
引理 support_induce
  条件: {u v : V}
-/
@[simp] lemma support_induce {u v : V} :
    forall (w : G.Walk u v) (hw), (w.induce s hw).support = w.support.attachWith _ hw
  | .nil, hw => rfl
  | .cons (v := u') hu w, hw => by simp [support_induce]

/--
lemma `map_induce` / 引理 `map_induce`

English:
lemma map_induce
  given: {u v : V}

中文:
引理 map_induce
  条件: {u v : V}
-/
@[simp] lemma map_induce {u v : V} :
    forall (w : G.Walk u v) (hw), (w.induce s hw).map (Embedding.induce _).toHom = w
  | .nil, hw => rfl
  | .cons (v := u') huu' w, hw => by simp [map_induce]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `map_induce_induceHomOfLE` / 引理 `map_induce_induceHomOfLE`

English:
lemma map_induce_induceHomOfLE
  given: (hs : s subseteq s') {u v : V}
  statement: forall (w : G.Walk u v) (hw),

中文:
引理 map_induce_induceHomOfLE
  条件: (hs : s subseteq s') {u v : V}
  结论: 对任意 (w : G.Walk u v) (hw),

Depends on / 依赖: map_induce_induceHomOfLE
-/
lemma map_induce_induceHomOfLE (hs : s subseteq s') {u v : V} : forall (w : G.Walk u v) (hw),
    (w.induce s hw).map (G.induceHomOfLE hs).toHom = w.induce s' (subset_trans hw hs)
  | .nil, hw => rfl
  | .cons (v := u') huu' w, hw => by simp [map_induce_induceHomOfLE]

/-! ## Deleting edges -/

/--
Definition of `toDeleteEdges` / `toDeleteEdges` 的定义

English:
abbreviation toDeleteEdges
  signature: (s : Set (Sym2 V)) {v w : V} (p : G.Walk v w)
  body: p.transfer _ by
    simp only [edgeSet_deleteEdges, Set.mem_sdiff]
    exact fun e ep => ⟨edges_subset_edgeSet p ep, hp e ep⟩

@[simp]

中文:
缩写 toDeleteEdges
  签名: (s : Set (Sym2 V)) {v w : V} (p : G.Walk v w)
  定义体: p.transfer _ by
    simp only [edgeSet_deleteEdges, Set.mem_sdiff]
    exact fun e ep => ⟨edges_subset_edgeSet p ep, hp e ep⟩

@[simp]

Depends on / 依赖: Set.mem_sdiff, edgeSet_deleteEdges, edges_subset_edgeSet, mem_sdiff, p.transfer, transfer
-/
abbrev toDeleteEdges (s : Set (Sym2 V)) {v w : V} (p : G.Walk v w)
    (hp : forall e, e in p.edges -> e ∉ s) : (G.deleteEdges s).Walk v w :=
p.transfer _ by
    simp only [edgeSet_deleteEdges, Set.mem_sdiff]
    exact fun e ep => ⟨edges_subset_edgeSet p ep, hp e ep⟩

@[simp]
/--
theorem `toDeleteEdges_nil` / 定理 `toDeleteEdges_nil`

English:
theorem toDeleteEdges_nil
  given: (s : Set (Sym2 V)) {v : V} (hp)
  proof: rfl

@[simp]

中文:
定理 toDeleteEdges_nil
  条件: (s : Set (Sym2 V)) {v : V} (hp)
  证明: rfl

@[simp]
-/
theorem toDeleteEdges_nil (s : Set (Sym2 V)) {v : V} (hp) :
    (Walk.nil : G.Walk v v).toDeleteEdges s hp = Walk.nil := rfl

@[simp]
/--
theorem `toDeleteEdges_cons` / 定理 `toDeleteEdges_cons`

English:
theorem toDeleteEdges_cons
  given: (s : Set (Sym2 V)) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) (hp)
  proof: rfl

中文:
定理 toDeleteEdges_cons
  条件: (s : Set (Sym2 V)) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) (hp)
  证明: rfl
-/
theorem toDeleteEdges_cons (s : Set (Sym2 V)) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) (hp) :
    (Walk.cons h p).toDeleteEdges s hp =
      Walk.cons (deleteEdges_adj.mpr ⟨h, hp _ (List.Mem.head _)⟩)
        (p.toDeleteEdges s fun _ he => hp _ <| List.Mem.tail _ he) :=
  rfl

/--
Definition of `toDeleteEdge` / `toDeleteEdge` 的定义

English:
abbreviation toDeleteEdge
  signature: (e : Sym2 V) (p : G.Walk v w) (hp : e ∉ p.edges)
  body: p.toDeleteEdges {e} (fun _ => by contrapose; simp +contextual [hp])

@[simp]

中文:
缩写 toDeleteEdge
  签名: (e : Sym2 V) (p : G.Walk v w) (hp : e ∉ p.edges)
  定义体: p.toDeleteEdges {e} (fun _ => by contrapose; simp +contextual [hp])

@[simp]

Depends on / 依赖: contextual, contrapose, p.toDeleteEdges, toDeleteEdges
-/
abbrev toDeleteEdge (e : Sym2 V) (p : G.Walk v w) (hp : e ∉ p.edges) :
    (G.deleteEdges {e}).Walk v w :=
  p.toDeleteEdges {e} (fun _ => by contrapose; simp +contextual [hp])

@[simp]
/--
theorem `map_toDeleteEdges_eq` / 定理 `map_toDeleteEdges_eq`

English:
theorem map_toDeleteEdges_eq
  given: (s : Set (Sym2 V)) {p : G.Walk v w} (hp)
  proof: by
  rw [← transfer_eq_map_ofLE]; rw [transfer_transfer]; rw [transfer_self]
  apply edges_transfer _ _ ▸ p.edges_subset_edgeSet

中文:
定理 map_toDeleteEdges_eq
  条件: (s : Set (Sym2 V)) {p : G.Walk v w} (hp)
  证明: by
  rw [← transfer_eq_map_ofLE]; rw [transfer_transfer]; rw [transfer_self]
  apply edges_transfer _ _ ▸ p.edges_subset_edgeSet

Depends on / 依赖: edges_subset_edgeSet, edges_transfer, p.edges_subset_edgeSet, transfer_eq_map_ofLE, transfer_self, transfer_transfer
-/
theorem map_toDeleteEdges_eq (s : Set (Sym2 V)) {p : G.Walk v w} (hp) :
    Walk.map (.ofLE (G.deleteEdges_le s)) (p.toDeleteEdges s hp) = p := by
  rw [← transfer_eq_map_ofLE]; rw [transfer_transfer]; rw [transfer_self]
  apply edges_transfer _ _ ▸ p.edges_subset_edgeSet

end Walk

end SimpleGraph
