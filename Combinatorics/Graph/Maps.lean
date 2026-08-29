/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Peter Nelson
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Maps between graphs

This file defines vertex map between graphs `Graph α β`. Morphisms between graphs will also be
defined in this file in the future.

## Main definitions

* `map`: the map on graphs induced by a function on vertices `f : α → α'`

## TODO

* Morphisms between graphs

-/

public section

variable {α α' α'' β : Type*} {G H : Graph α β} {f g : α -> α'} {u v : α} {e : β} {x y : α'}

open Set Relation

namespace Graph

section Map

/-- Map `G : Graph α β` to a `Graph α' β` with the same edge set by applying a function `f : α → α'`
  to each vertex. Edges between identified vertices become loops. -/
@[expose, simps! (attr := grind =)]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> α') (G : Graph α β)
  body: f '' V(G)
  edgeSet := E(G)
  IsLink e := Relation.Map (G.IsLink e) f f
  isLink_symm _ he := have := G.isLink_symm he; .map f
  eq_or_eq_of_isLink_of_isLink := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq hzw <;> simp
  edge_mem_iff_e

中文:
定义 map
  签名: (f : α -> α') (G : 图 α β)
  定义体: f '' V(G)
  edgeSet := E(G)
  IsLink e := Relation.Map (G.IsLink e) f f
  isLink_symm _ he := have := G.isLink_symm he; .map f
  eq_or_eq_of_isLink_of_isLink := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq hzw <;> simp
  edge_mem_iff_e
-/
def map (f : α -> α') (G : Graph α β) : Graph α' β where
  vertexSet := f '' V(G)
  edgeSet := E(G)
  IsLink e := Relation.Map (G.IsLink e) f f
  isLink_symm _ he := have := G.isLink_symm he; .map f
  eq_or_eq_of_isLink_of_isLink := by
    rintro e - - - - ⟨x, y, hxy, rfl, rfl⟩ ⟨z, w, hzw, rfl, rfl⟩
    obtain rfl | rfl := hxy.left_eq_or_eq hzw <;> simp
  edge_mem_iff_exists_isLink e := by
    refine ⟨fun h => ?_, fun ⟨_, _, _, _, h, _, _⟩ => h.edge_mem⟩
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h
    exact ⟨_, _, _, _, hxy, rfl, rfl⟩
  left_mem_of_isLink := by
    rintro e - - ⟨x, y, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ h.left_mem

/--
lemma `IsLink.map` / 引理 `IsLink.map`

English:
lemma IsLink.map
  given: (f : α -> α') (h : G.IsLink e u v)
  statement: (G.map f).IsLink e (f u) (f v)
  proof: ⟨u, v, h, rfl, rfl⟩

@[simp]

中文:
引理 IsLink.map
  条件: (f : α -> α') (h : G.IsLink e u v)
  结论: (G.map f).IsLink e (f u) (f v)
  证明: ⟨u, v, h, rfl, rfl⟩

@[simp]
-/
protected lemma IsLink.map (f : α -> α') (h : G.IsLink e u v) : (G.map f).IsLink e (f u) (f v) :=
  ⟨u, v, h, rfl, rfl⟩

@[simp]
/--
lemma `map_inc` / 引理 `map_inc`

English:
lemma map_inc
  given: (f : α -> α')
  statement: (G.map f).Inc e x ↔ exists v, G.Inc e v ∧ x = f v
  proof: by
  simp only [Inc, map_isLink, map_apply]
  tauto

中文:
引理 map_inc
  条件: (f : α -> α')
  结论: (G.map f).Inc e x ↔ 存在 v, G.Inc e v ∧ x = f v
  证明: by
  simp only [Inc, map_isLink, map_apply]
  tauto

Depends on / 依赖: map_apply, map_isLink
-/
lemma map_inc (f : α -> α') : (G.map f).Inc e x ↔ exists v, G.Inc e v ∧ x = f v := by
  simp only [Inc, map_isLink, map_apply]
  tauto

/--
lemma `Inc.map` / 引理 `Inc.map`

English:
lemma Inc.map
  given: (f : α -> α') (h : G.Inc e v)
  statement: (G.map f).Inc e (f v)
  proof: by
  obtain ⟨w, hw⟩ := h
  exact ⟨f w, hw.map f⟩

@[simp]

中文:
引理 Inc.map
  条件: (f : α -> α') (h : G.Inc e v)
  结论: (G.map f).Inc e (f v)
  证明: by
  obtain ⟨w, hw⟩ := h
  exact ⟨f w, hw.map f⟩

@[simp]
-/
protected lemma Inc.map (f : α -> α') (h : G.Inc e v) : (G.map f).Inc e (f v) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨f w, hw.map f⟩

@[simp]
/--
lemma `map_isLoopAt` / 引理 `map_isLoopAt`

English:
lemma map_isLoopAt
  given: (f : α -> α')
  proof: Iff.rfl

中文:
引理 map_isLoopAt
  条件: (f : α -> α')
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma map_isLoopAt (f : α -> α') :
    (G.map f).IsLoopAt e x ↔ exists u v, G.IsLink e u v ∧ f u = x ∧ f v = x := Iff.rfl

/--
lemma `IsLoopAt.map` / 引理 `IsLoopAt.map`

English:
lemma IsLoopAt.map
  given: (f : α -> α') (h : G.IsLoopAt e v)
  statement: (G.map f).IsLoopAt e (f v)
  proof: IsLink.map f h

@[simp]

中文:
引理 IsLoopAt.map
  条件: (f : α -> α') (h : G.IsLoopAt e v)
  结论: (G.map f).IsLoopAt e (f v)
  证明: IsLink.map f h

@[simp]
-/
protected lemma IsLoopAt.map (f : α -> α') (h : G.IsLoopAt e v) : (G.map f).IsLoopAt e (f v) :=
  IsLink.map f h

@[simp]
/--
lemma `map_adj` / 引理 `map_adj`

English:
lemma map_adj
  given: (f : α -> α')
  statement: (G.map f).Adj x y ↔ Relation.Map G.Adj f f x y
  proof: by
  simp only [Adj, map_isLink, map_apply]
  tauto

中文:
引理 map_adj
  条件: (f : α -> α')
  结论: (G.map f).伴随 x y ↔ 关系.Map G.伴随 f f x y
  证明: by
  simp only [Adj, map_isLink, map_apply]
  tauto

Depends on / 依赖: map_apply, map_isLink
-/
lemma map_adj (f : α -> α') : (G.map f).Adj x y ↔ Relation.Map G.Adj f f x y := by
  simp only [Adj, map_isLink, map_apply]
  tauto

/--
lemma `Adj.map` / 引理 `Adj.map`

English:
lemma Adj.map
  given: (f : α -> α') (h : G.Adj u v)
  statement: (G.map f).Adj (f u) (f v)
  proof: by
  obtain ⟨e, h⟩ := h
  exact ⟨e, h.map f⟩

中文:
引理 伴随.map
  条件: (f : α -> α') (h : G.伴随 u v)
  结论: (G.map f).伴随 (f u) (f v)
  证明: by
  obtain ⟨e, h⟩ := h
  exact ⟨e, h.map f⟩
-/
protected lemma Adj.map (f : α -> α') (h : G.Adj u v) : (G.map f).Adj (f u) (f v) := by
  obtain ⟨e, h⟩ := h
  exact ⟨e, h.map f⟩

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: G.map id = G
  proof: by ext a b c <;> simp

@[simp]

中文:
引理 map_id
  结论: G.map id = G
  证明: by ext a b c <;> simp

@[simp]
-/
@[simp] lemma map_id : G.map id = G := by ext a b c <;> simp

@[simp]
/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: (f : α -> α') (f' : α' -> α'')
  statement: (G.map f).map f' = G.map (f' ∘ f)
  proof: by
  ext a b c <;> simp [map_apply]

@[gcongr]

中文:
引理 map_map
  条件: (f : α -> α') (f' : α' -> α'')
  结论: (G.map f).map f' = G.map (f' ∘ f)
  证明: by
  ext a b c <;> simp [map_apply]

@[gcongr]

Depends on / 依赖: map_apply
-/
lemma map_map (f : α -> α') (f' : α' -> α'') : (G.map f).map f' = G.map (f' ∘ f) := by
  ext a b c <;> simp [map_apply]

@[gcongr]
/--
lemma `IsSubgraph.map` / 引理 `IsSubgraph.map`

English:
lemma IsSubgraph.map
  given: (f : α -> α') (h : G <= H)
  statement: G.map f <= H.map f where
  proof: by grind [h.vertexSet_mono]
isLink_mono e := map_mono h.isLink_mono (e := e)
alias map_mono := IsSubgraph.map

@[gcongr]

中文:
引理 是子图.map
  条件: (f : α -> α') (h : G <= H)
  结论: G.map f <= H.map f where
  证明: by grind [h.vertexSet_mono]
isLink_mono e := map_mono h.isLink_mono (e := e)
alias map_mono := IsSubgraph.map

@[gcongr]
-/
protected lemma IsSubgraph.map (f : α -> α') (h : G <= H) : G.map f <= H.map f where
  vertexSet_mono v := by grind [h.vertexSet_mono]
isLink_mono e := map_mono h.isLink_mono (e := e)
alias map_mono := IsSubgraph.map

@[gcongr]
/--
lemma `IsSpanningSubgraph.map` / 引理 `IsSpanningSubgraph.map`

English:
lemma IsSpanningSubgraph.map
  given: (f : α -> α') (hsle : G <=s H)
  statement: G.map f <=s H.map f where
  proof: hsle.le.map f
  vertexSet_eq := by simp [hsle.vertexSet_eq]

@[gcongr only]

中文:
引理 是SpanningSubgraph.map
  条件: (f : α -> α') (hsle : G <=s H)
  结论: G.map f <=s H.map f where
  证明: hsle.le.map f
  vertexSet_eq := by simp [hsle.vertexSet_eq]

@[gcongr only]
-/
protected lemma IsSpanningSubgraph.map (f : α -> α') (hsle : G <=s H) : G.map f <=s H.map f where
  le := hsle.le.map f
  vertexSet_eq := by simp [hsle.vertexSet_eq]

@[gcongr only]
/--
lemma `map_eq_of_eqOn` / 引理 `map_eq_of_eqOn`

English:
lemma map_eq_of_eqOn
  given: (h : EqOn f g V(G))
  statement: G.map f = G.map g
  proof: by
  refine Graph.ext (by grind) fun _ _ _ => ⟨fun ⟨_, _, hvw, _, _⟩ => ?_, fun ⟨_, _, hvw, _, _⟩ => ?_⟩
  <;> grind [h hvw.left_mem, h hvw.right_mem, hvw.map]

中文:
引理 map_eq_of_eqOn
  条件: (h : EqOn f g V(G))
  结论: G.map f = G.map g
  证明: by
  refine Graph.ext (by grind) fun _ _ _ => ⟨fun ⟨_, _, hvw, _, _⟩ => ?_, fun ⟨_, _, hvw, _, _⟩ => ?_⟩
  <;> grind [h hvw.left_mem, h hvw.right_mem, hvw.map]

Depends on / 依赖: Bitraversable, Bitraversable.traversable, Graph.ext, Traversable, hvw.left_mem, hvw.map, hvw.right_mem, left_mem, right_mem, traversable
-/
lemma map_eq_of_eqOn (h : EqOn f g V(G)) : G.map f = G.map g := by
  refine Graph.ext (by grind) fun _ _ _ => ⟨fun ⟨_, _, hvw, _, _⟩ => ?_, fun ⟨_, _, hvw, _, _⟩ => ?_⟩
  <;> grind [h hvw.left_mem, h hvw.right_mem, hvw.map]

end Map

end Graph
