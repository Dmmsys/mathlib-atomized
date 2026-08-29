/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.Logic.Embedding.Set

/-!
# Maps between graphs

This file defines two functions and three structures relating graphs.
The structures directly correspond to the classification of functions as
injective, surjective and bijective, and have corresponding notation.

## Main definitions

* `SimpleGraph.map`: the graph obtained by pushing the adjacency relation through
  an injective function between vertex types.
* `SimpleGraph.comap`: the graph obtained by pulling the adjacency relation behind
  an arbitrary function between vertex types.
* `SimpleGraph.induce`: the subgraph induced by the given vertex set, a wrapper around `comap`.
* `SimpleGraph.spanningCoe`: the supergraph without any additional edges, a wrapper around `map`.
* `SimpleGraph.Hom`, `G →g H`: a graph homomorphism from `G` to `H`.
* `SimpleGraph.Embedding`, `G ↪g H`: a graph embedding of `G` in `H`.
* `SimpleGraph.Iso`, `G ≃g H`: a graph isomorphism between `G` and `H`.

Note that a graph embedding is a stronger notion than an injective graph homomorphism,
since its image is an induced subgraph.

## Implementation notes

Morphisms of graphs are abbreviations for `RelHom`, `RelEmbedding` and `RelIso`.
To make use of pre-existing simp lemmas, definitions involving morphisms are
abbreviations as well.
-/

@[expose] public section


open Function

namespace SimpleGraph

variable {V W X Y : Type*} (G : SimpleGraph V) (G' : SimpleGraph W) {u v : V}

/-! ## Map and comap -/


/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : V -> W) (G : SimpleGraph V)
  body: Ne ⊓ Relation.Map G.Adj f f
  symm.symm a b := by aesop (add norm unfold Relation.Map) (add forward safe Adj.symm)

中文:
定义 map
  签名: (f : V -> W) (G : 简单图 V)
  定义体: Ne ⊓ Relation.Map G.Adj f f
  symm.symm a b := by aesop (add norm unfold Relation.Map) (add forward safe Adj.symm)
-/
protected def map (f : V -> W) (G : SimpleGraph V) : SimpleGraph W where
  Adj := Ne ⊓ Relation.Map G.Adj f f
  symm.symm a b := by aesop (add norm unfold Relation.Map) (add forward safe Adj.symm)

/--
Instance `instDecidableMapAdj` / 实例 `instDecidableMapAdj`

English:
instance instDecidableMapAdj
  signature: [DecidableEq W] {f : V -> W} {a b}
  body: inferInstanceAs Decidable (_ ∧ _)

@[simp]

中文:
实例 instDecidableMapAdj
  签名: [DecidableEq W] {f : V -> W} {a b}
  定义体: inferInstanceAs Decidable (_ ∧ _)

@[simp]

Depends on / 依赖: Decidable
-/
instance instDecidableMapAdj [DecidableEq W] {f : V -> W} {a b}
    [Decidable (Relation.Map G.Adj f f a b)] : Decidable ((G.map f).Adj a b) :=
inferInstanceAs Decidable (_ ∧ _)

@[simp]
/--
theorem `map_adj` / 定理 `map_adj`

English:
theorem map_adj
  given: (f : V ↪ W) (G : SimpleGraph V) (u v : W)
  proof: by
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]

中文:
定理 map_adj
  条件: (f : V ↪ W) (G : 简单图 V) (u v : W)
  证明: by
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]

Depends on / 依赖: Relation, Relation.Map, SimpleGraph, SimpleGraph.Adj.ne, SimpleGraph.map
-/
theorem map_adj (f : V ↪ W) (G : SimpleGraph V) (u v : W) :
    (G.map f).Adj u v ↔ exists u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v := by
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]

/--
theorem `map_adj'` / 定理 `map_adj'`

English:
theorem map_adj'
  given: (f : V -> W) (G : SimpleGraph V) (u v : W)
  proof: Iff.rfl

中文:
定理 map_adj'
  条件: (f : V -> W) (G : 简单图 V) (u v : W)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem map_adj' (f : V -> W) (G : SimpleGraph V) (u v : W) :
    (G.map f).Adj u v ↔ u != v ∧ exists u' v' : V, G.Adj u' v' ∧ f u' = u ∧ f v' = v :=
  Iff.rfl

/--
theorem `edgeSet_map` / 定理 `edgeSet_map`

English:
theorem edgeSet_map
  given: (f : V ↪ W) (G : SimpleGraph V)
  proof: by
  ext v
  induction v
  rw [mem_edgeSet]; rw [map_adj]; rw [Set.mem_image]
  constructor
  · intro ⟨a, b, hadj, ha, hb⟩
    use s(a, b), hadj
    rw [Embedding.sym2Map_apply]; rw [Sym2.map_mk]; rw [ha]; rw [hb]
  · intro ⟨e, hadj, he⟩
    induction e
    rw [Embedding.sym2Map_apply]; rw [Sym2.map

中文:
定理 edgeSet_map
  条件: (f : V ↪ W) (G : 简单图 V)
  证明: by
  ext v
  induction v
  rw [mem_edgeSet]; rw [map_adj]; rw [Set.mem_image]
  constructor
  · intro ⟨a, b, hadj, ha, hb⟩
    use s(a, b), hadj
    rw [Embedding.sym2Map_apply]; rw [Sym2.map_mk]; rw [ha]; rw [hb]
  · intro ⟨e, hadj, he⟩
    induction e
    rw [Embedding.sym2Map_apply]; rw [Sym2.map

Depends on / 依赖: Embedding, Embedding.sym2Map_apply, Set.mem_image, Sym2.eq_iff, Sym2.map_mk, eq_iff, hadj.symm, he.elim, map_adj, map_mk, mem_edgeSet, mem_image, sym2Map_apply
-/
theorem edgeSet_map (f : V ↪ W) (G : SimpleGraph V) :
    (G.map f).edgeSet = f.sym2Map '' G.edgeSet := by
  ext v
  induction v
  rw [mem_edgeSet]; rw [map_adj]; rw [Set.mem_image]
  constructor
  · intro ⟨a, b, hadj, ha, hb⟩
    use s(a, b), hadj
    rw [Embedding.sym2Map_apply]; rw [Sym2.map_mk]; rw [ha]; rw [hb]
  · intro ⟨e, hadj, he⟩
    induction e
    rw [Embedding.sym2Map_apply]; rw [Sym2.map_mk]; rw [Sym2.eq_iff] at he
    exact he.elim (fun ⟨h, h'⟩ => ⟨_, _, hadj, h, h'⟩) (fun ⟨h', h⟩ => ⟨_, _, hadj.symm, h, h'⟩)

@[simp]
/--
theorem `neighborSet_map` / 定理 `neighborSet_map`

English:
theorem neighborSet_map
  given: (f : V ↪ W) (v : V)
  proof: by
  refine Set.ext fun u => ⟨?_, ?_⟩
  · exact fun ⟨hne, v', u', hadj, hv, hu⟩ => ⟨u', f.injective hv ▸ hadj, hu⟩
  · exact fun ⟨u', hadj, hu⟩ => ⟨hu ▸ f.injective.ne hadj.ne, v, u', hadj, rfl, hu⟩

中文:
定理 neighborSet_map
  条件: (f : V ↪ W) (v : V)
  证明: by
  refine Set.ext fun u => ⟨?_, ?_⟩
  · exact fun ⟨hne, v', u', hadj, hv, hu⟩ => ⟨u', f.injective hv ▸ hadj, hu⟩
  · exact fun ⟨u', hadj, hu⟩ => ⟨hu ▸ f.injective.ne hadj.ne, v, u', hadj, rfl, hu⟩

Depends on / 依赖: Set.ext, f.injective, f.injective.ne, hadj.ne, injective
-/
theorem neighborSet_map (f : V ↪ W) (v : V) :
    (G.map f).neighborSet (f v) = f '' G.neighborSet v := by
  refine Set.ext fun u => ⟨?_, ?_⟩
  · exact fun ⟨hne, v', u', hadj, hv, hu⟩ => ⟨u', f.injective hv ▸ hadj, hu⟩
  · exact fun ⟨u', hadj, hu⟩ => ⟨hu ▸ f.injective.ne hadj.ne, v, u', hadj, rfl, hu⟩

/--
lemma `map_adj_apply` / 引理 `map_adj_apply`

English:
lemma map_adj_apply
  given: {G : SimpleGraph V} {f : V ↪ W} {a b : V}
  proof: by simp

中文:
引理 map_adj_apply
  条件: {G : 简单图 V} {f : V ↪ W} {a b : V}
  证明: by simp
-/
lemma map_adj_apply {G : SimpleGraph V} {f : V ↪ W} {a b : V} :
    (G.map f).Adj (f a) (f b) ↔ G.Adj a b := by simp

variable {G} in
/--
theorem `map_adj_apply'` / 定理 `map_adj_apply'`

English:
theorem map_adj_apply'
  given: {f : V -> W} (hadj : G.Adj u v) (hne : f u != f v)
  proof: ⟨hne, u, v, hadj, rfl, rfl⟩

@[gcongr]

中文:
定理 map_adj_apply'
  条件: {f : V -> W} (hadj : G.伴随 u v) (hne : f u != f v)
  证明: ⟨hne, u, v, hadj, rfl, rfl⟩

@[gcongr]
-/
theorem map_adj_apply' {f : V -> W} (hadj : G.Adj u v) (hne : f u != f v) :
    (G.map f).Adj (f u) (f v) :=
  ⟨hne, u, v, hadj, rfl, rfl⟩

@[gcongr]
/--
theorem `map_monotone` / 定理 `map_monotone`

English:
theorem map_monotone
  given: (f : V -> W)
  statement: Monotone (SimpleGraph.map f)
  proof: by
  rintro G G' h z1 z2 ⟨huv, u, v, ha, rfl, rfl⟩
  exact ⟨huv, _, _, h ha, rfl, rfl⟩

中文:
定理 map_monotone
  条件: (f : V -> W)
  结论: 递增 (简单图.map f)
  证明: by
  rintro G G' h z1 z2 ⟨huv, u, v, ha, rfl, rfl⟩
  exact ⟨huv, _, _, h ha, rfl, rfl⟩
-/
theorem map_monotone (f : V -> W) : Monotone (SimpleGraph.map f) := by
  rintro G G' h z1 z2 ⟨huv, u, v, ha, rfl, rfl⟩
  exact ⟨huv, _, _, h ha, rfl, rfl⟩

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: G.map id = G
  proof: by
  ext
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]

中文:
引理 map_id
  结论: G.map id = G
  证明: by
  ext
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]
-/
@[simp] lemma map_id : G.map id = G := by
  ext
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]

/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: (f : V -> W) (g : W -> X)
  statement: (G.map f).map g = G.map (g ∘ f)
  proof: by
  ext
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]

中文:
引理 map_map
  条件: (f : V -> W) (g : W -> X)
  结论: (G.map f).map g = G.map (g ∘ f)
  证明: by
  ext
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]
-/
@[simp] lemma map_map (f : V -> W) (g : W -> X) : (G.map f).map g = G.map (g ∘ f) := by
  ext
  dsimp [SimpleGraph.map, Relation.Map]
  grind [SimpleGraph.Adj.ne]

/--
theorem `support_map` / 定理 `support_map`

English:
theorem support_map
  given: (f : V ↪ W) (G : SimpleGraph V)
  proof: by
  ext; simp [mem_support]

中文:
定理 support_map
  条件: (f : V ↪ W) (G : 简单图 V)
  证明: by
  ext; simp [mem_support]

Depends on / 依赖: mem_support
-/
theorem support_map (f : V ↪ W) (G : SimpleGraph V) :
    (G.map f).support = f '' G.support := by
  ext; simp [mem_support]

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : V -> W) (G : SimpleGraph W)
  body: G.Adj (f u) (f v)
  symm.symm _ _ h := h.symm

中文:
定义 comap
  签名: (f : V -> W) (G : 简单图 W)
  定义体: G.Adj (f u) (f v)
  symm.symm _ _ h := h.symm
-/
protected def comap (f : V -> W) (G : SimpleGraph W) : SimpleGraph V where
  Adj u v := G.Adj (f u) (f v)
  symm.symm _ _ h := h.symm

/--
lemma `comap_adj` / 引理 `comap_adj`

English:
lemma comap_adj
  given: {G : SimpleGraph W} {f : V -> W}
  proof: Iff.rfl

中文:
引理 comap_adj
  条件: {G : 简单图 W} {f : V -> W}
  证明: Iff.rfl
-/
@[simp] lemma comap_adj {G : SimpleGraph W} {f : V -> W} :
    (G.comap f).Adj u v ↔ G.Adj (f u) (f v) := Iff.rfl

/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  given: {G : SimpleGraph V}
  statement: G.comap id = G
  proof: SimpleGraph.ext rfl

中文:
引理 comap_id
  条件: {G : 简单图 V}
  结论: G.comap id = G
  证明: SimpleGraph.ext rfl
-/
@[simp] lemma comap_id {G : SimpleGraph V} : G.comap id = G := SimpleGraph.ext rfl

/--
lemma `comap_comap` / 引理 `comap_comap`

English:
lemma comap_comap
  given: {G : SimpleGraph X} (f : V -> W) (g : W -> X)
  proof: rfl

中文:
引理 comap_comap
  条件: {G : 简单图 X} (f : V -> W) (g : W -> X)
  证明: rfl
-/
@[simp] lemma comap_comap {G : SimpleGraph X} (f : V -> W) (g : W -> X) :
    (G.comap g).comap f = G.comap (g ∘ f) := rfl

/--
theorem `support_comap_subset` / 定理 `support_comap_subset`

English:
theorem support_comap_subset
  given: (f : V -> W) (G : SimpleGraph W)
  proof: fun _ ⟨v, h⟩ => ⟨f v, h⟩

中文:
定理 support_comap_subset
  条件: (f : V -> W) (G : 简单图 W)
  证明: fun _ ⟨v, h⟩ => ⟨f v, h⟩
-/
theorem support_comap_subset (f : V -> W) (G : SimpleGraph W) :
    (G.comap f).support subseteq f ⁻¹' G.support :=
  fun _ ⟨v, h⟩ => ⟨f v, h⟩

/--
Instance `instDecidableComapAdj` / 实例 `instDecidableComapAdj`

English:
instance instDecidableComapAdj
  signature: (f : V -> W) (G : SimpleGraph W) [DecidableRel G.Adj]
  body: fun _ _ => ‹DecidableRel G.Adj› _ _

中文:
实例 instDecidableComapAdj
  签名: (f : V -> W) (G : 简单图 W) [DecidableRel G.伴随]
  定义体: fun _ _ => ‹DecidableRel G.Adj› _ _

Depends on / 依赖: DecidableRel, G.Adj
-/
instance instDecidableComapAdj (f : V -> W) (G : SimpleGraph W) [DecidableRel G.Adj] :
    DecidableRel (G.comap f).Adj := fun _ _ => ‹DecidableRel G.Adj› _ _

/--
lemma `comap_symm` / 引理 `comap_symm`

English:
lemma comap_symm
  given: (G : SimpleGraph V) (e : V ≃ W)
  proof: by
  ext; simp only [← Equiv.eq_symm_apply, comap_adj, map_adj, Equiv.toEmbedding_apply,
    exists_eq_right_right, exists_eq_right]

中文:
引理 comap_symm
  条件: (G : 简单图 V) (e : V ≃ W)
  证明: by
  ext; simp only [← Equiv.eq_symm_apply, comap_adj, map_adj, Equiv.toEmbedding_apply,
    exists_eq_right_right, exists_eq_right]

Depends on / 依赖: Equiv.eq_symm_apply, Equiv.toEmbedding_apply, comap_adj, eq_symm_apply, exists_eq_right, exists_eq_right_right, map_adj, toEmbedding_apply
-/
lemma comap_symm (G : SimpleGraph V) (e : V ≃ W) :
    G.comap e.symm.toEmbedding = G.map e.toEmbedding := by
  ext; simp only [← Equiv.eq_symm_apply, comap_adj, map_adj, Equiv.toEmbedding_apply,
    exists_eq_right_right, exists_eq_right]

/--
lemma `map_symm` / 引理 `map_symm`

English:
lemma map_symm
  given: (G : SimpleGraph W) (e : V ≃ W)
  proof: by rw [← comap_symm, e.symm_symm]

@[gcongr]

中文:
引理 map_symm
  条件: (G : 简单图 W) (e : V ≃ W)
  证明: by rw [← comap_symm, e.symm_symm]

@[gcongr]

Depends on / 依赖: comap_symm, e.symm_symm, symm_symm
-/
lemma map_symm (G : SimpleGraph W) (e : V ≃ W) :
    G.map e.symm.toEmbedding = G.comap e.toEmbedding := by rw [← comap_symm, e.symm_symm]

@[gcongr]
/--
theorem `comap_monotone` / 定理 `comap_monotone`

English:
theorem comap_monotone
  given: (f : V ↪ W)
  statement: Monotone (SimpleGraph.comap f)
  proof: fun _ _ h _ _ ha => h ha

中文:
定理 comap_monotone
  条件: (f : V ↪ W)
  结论: 递增 (简单图.comap f)
  证明: fun _ _ h _ _ ha => h ha
-/
theorem comap_monotone (f : V ↪ W) : Monotone (SimpleGraph.comap f) :=
  fun _ _ h _ _ ha => h ha

/--
lemma `comap_bot` / 引理 `comap_bot`

English:
lemma comap_bot
  given: (f : V -> W)
  statement: (emptyGraph W).comap f = emptyGraph V
  proof: rfl

中文:
引理 comap_bot
  条件: (f : V -> W)
  结论: (emptyGraph W).comap f = emptyGraph V
  证明: rfl
-/
@[simp] lemma comap_bot (f : V -> W) : (emptyGraph W).comap f = emptyGraph V := rfl

/--
lemma `comap_top` / 引理 `comap_top`

English:
lemma comap_top
  given: {f : V -> W} (hf : f.Injective)
  statement: (completeGraph W).comap f = completeGraph V
  proof: by
  ext; simp [hf.eq_iff]

@[simp]

中文:
引理 comap_top
  条件: {f : V -> W} (hf : f.单射)
  结论: (completeGraph W).comap f = completeGraph V
  证明: by
  ext; simp [hf.eq_iff]

@[simp]

Depends on / 依赖: eq_iff, hf.eq_iff
-/
lemma comap_top {f : V -> W} (hf : f.Injective) : (completeGraph W).comap f = completeGraph V := by
  ext; simp [hf.eq_iff]

@[simp]
/--
theorem `comap_map_eq` / 定理 `comap_map_eq`

English:
theorem comap_map_eq
  given: (f : V ↪ W) (G : SimpleGraph V)
  statement: (G.map f).comap f = G
  proof: by
  ext
  simp

中文:
定理 comap_map_eq
  条件: (f : V ↪ W) (G : 简单图 V)
  结论: (G.map f).comap f = G
  证明: by
  ext
  simp
-/
theorem comap_map_eq (f : V ↪ W) (G : SimpleGraph V) : (G.map f).comap f = G := by
  ext
  simp

/--
theorem `leftInverse_comap_map` / 定理 `leftInverse_comap_map`

English:
theorem leftInverse_comap_map
  given: (f : V ↪ W)
  proof: comap_map_eq f

中文:
定理 leftInverse_comap_map
  条件: (f : V ↪ W)
  证明: comap_map_eq f

Depends on / 依赖: comap_map_eq
-/
theorem leftInverse_comap_map (f : V ↪ W) :
    Function.LeftInverse (SimpleGraph.comap f) (SimpleGraph.map f) :=
  comap_map_eq f

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (f : V ↪ W)
  statement: Function.Injective (SimpleGraph.map f)
  proof: (leftInverse_comap_map f).injective

中文:
定理 map_injective
  条件: (f : V ↪ W)
  结论: 函数.单射 (简单图.map f)
  证明: (leftInverse_comap_map f).injective

Depends on / 依赖: injective, leftInverse_comap_map
-/
theorem map_injective (f : V ↪ W) : Function.Injective (SimpleGraph.map f) :=
  (leftInverse_comap_map f).injective

/--
theorem `comap_surjective` / 定理 `comap_surjective`

English:
theorem comap_surjective
  given: (f : V ↪ W)
  statement: Function.Surjective (SimpleGraph.comap f)
  proof: (leftInverse_comap_map f).surjective

中文:
定理 comap_surjective
  条件: (f : V ↪ W)
  结论: 函数.满射 (简单图.comap f)
  证明: (leftInverse_comap_map f).surjective

Depends on / 依赖: leftInverse_comap_map, surjective
-/
theorem comap_surjective (f : V ↪ W) : Function.Surjective (SimpleGraph.comap f) :=
  (leftInverse_comap_map f).surjective

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: (f : V ↪ W) (G : SimpleGraph V) (G' : SimpleGraph W)
  proof: ⟨fun h _ _ ha => h ⟨f.injective.ne ha.ne, _, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨-, u, v, ha, rfl, rfl⟩
    exact h ha⟩

中文:
定理 map_le_iff_le_comap
  条件: (f : V ↪ W) (G : 简单图 V) (G' : 简单图 W)
  证明: ⟨fun h _ _ ha => h ⟨f.injective.ne ha.ne, _, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨-, u, v, ha, rfl, rfl⟩
    exact h ha⟩

Depends on / 依赖: f.injective.ne, ha.ne, injective
-/
theorem map_le_iff_le_comap (f : V ↪ W) (G : SimpleGraph V) (G' : SimpleGraph W) :
    G.map f <= G' ↔ G <= G'.comap f :=
  ⟨fun h _ _ ha => h ⟨f.injective.ne ha.ne, _, _, ha, rfl, rfl⟩, by
    rintro h _ _ ⟨-, u, v, ha, rfl, rfl⟩
    exact h ha⟩

/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  given: (f : V ↪ W) (G : SimpleGraph W)
  statement: (G.comap f).map f <= G
  proof: by
  rw [map_le_iff_le_comap]

中文:
定理 map_comap_le
  条件: (f : V ↪ W) (G : 简单图 W)
  结论: (G.comap f).map f <= G
  证明: by
  rw [map_le_iff_le_comap]

Depends on / 依赖: map_le_iff_le_comap
-/
theorem map_comap_le (f : V ↪ W) (G : SimpleGraph W) : (G.comap f).map f <= G := by
  rw [map_le_iff_le_comap]

/--
lemma `le_comap_of_subsingleton` / 引理 `le_comap_of_subsingleton`

English:
lemma le_comap_of_subsingleton
  given: (f : V -> W) [Subsingleton V]
  statement: G <= G'.comap f
  proof: by
  intro v w; simp [Subsingleton.elim v w]

中文:
引理 le_comap_of_subsingleton
  条件: (f : V -> W) [子单例 V]
  结论: G <= G'.comap f
  证明: by
  intro v w; simp [Subsingleton.elim v w]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
lemma le_comap_of_subsingleton (f : V -> W) [Subsingleton V] : G <= G'.comap f := by
  intro v w; simp [Subsingleton.elim v w]

/--
lemma `map_le_of_subsingleton` / 引理 `map_le_of_subsingleton`

English:
lemma map_le_of_subsingleton
  given: (f : V ↪ W) [Subsingleton V]
  statement: G.map f <= G'
  proof: by
  rw [map_le_iff_le_comap]; apply le_comap_of_subsingleton

中文:
引理 map_le_of_subsingleton
  条件: (f : V ↪ W) [子单例 V]
  结论: G.map f <= G'
  证明: by
  rw [map_le_iff_le_comap]; apply le_comap_of_subsingleton

Depends on / 依赖: le_comap_of_subsingleton, map_le_iff_le_comap
-/
lemma map_le_of_subsingleton (f : V ↪ W) [Subsingleton V] : G.map f <= G' := by
  rw [map_le_iff_le_comap]; apply le_comap_of_subsingleton

/--
Definition of `completeMultipartiteGraph` / `completeMultipartiteGraph` 的定义

English:
abbreviation completeMultipartiteGraph
  signature: {ι : Type*} (V : ι -> Type*)
  body: .comap Sigma.fst ⊤

中文:
缩写 completeMultipartiteGraph
  签名: {ι : 类型} (V : ι -> 类型)
  定义体: .comap Sigma.fst ⊤

Depends on / 依赖: Sigma.fst
-/
abbrev completeMultipartiteGraph {ι : Type*} (V : ι -> Type*) : SimpleGraph (Σ i, V i) :=
  .comap Sigma.fst ⊤

/-- Equivalent types have equivalent simple graphs. -/
@[simps apply]
/--
Definition of `_root_.Equiv.simpleGraph` / `_root_.Equiv.simpleGraph` 的定义

English:
definition _root_.Equiv.simpleGraph
  signature: (e : V ≃ W)
  body: .comap e.symm
  invFun := .comap e
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 _root_.等价.simpleGraph
  签名: (e : V ≃ W)
  定义体: .comap e.symm
  invFun := .comap e
  left_inv _ := by simp
  right_inv _ := by simp
-/
protected def _root_.Equiv.simpleGraph (e : V ≃ W) : SimpleGraph V ≃ SimpleGraph W where
  toFun := .comap e.symm
  invFun := .comap e
  left_inv _ := by simp
  right_inv _ := by simp

/--
lemma `_root_.Equiv.simpleGraph_refl` / 引理 `_root_.Equiv.simpleGraph_refl`

English:
lemma _root_.Equiv.simpleGraph_refl
  statement: (Equiv.refl V).simpleGraph = Equiv.refl _
  proof: by
  ext; rfl

中文:
引理 _root_.等价.simpleGraph_refl
  结论: (等价.refl V).simpleGraph = 等价.refl _
  证明: by
  ext; rfl
-/
@[simp] lemma _root_.Equiv.simpleGraph_refl : (Equiv.refl V).simpleGraph = Equiv.refl _ := by
  ext; rfl

/--
lemma `_root_.Equiv.simpleGraph_trans` / 引理 `_root_.Equiv.simpleGraph_trans`

English:
lemma _root_.Equiv.simpleGraph_trans
  given: (e₁ : V ≃ W) (e₂ : W ≃ X)
  proof: rfl

@[simp]

中文:
引理 _root_.等价.simpleGraph_trans
  条件: (e₁ : V ≃ W) (e₂ : W ≃ X)
  证明: rfl

@[simp]
-/
@[simp] lemma _root_.Equiv.simpleGraph_trans (e₁ : V ≃ W) (e₂ : W ≃ X) :
    (e₁.trans e₂).simpleGraph = e₁.simpleGraph.trans e₂.simpleGraph := rfl

@[simp]
/--
lemma `_root_.Equiv.symm_simpleGraph` / 引理 `_root_.Equiv.symm_simpleGraph`

English:
lemma _root_.Equiv.symm_simpleGraph
  given: (e : V ≃ W)
  statement: e.simpleGraph.symm = e.symm.simpleGraph
  proof: rfl

中文:
引理 _root_.等价.symm_simpleGraph
  条件: (e : V ≃ W)
  结论: e.simpleGraph.symm = e.symm.simpleGraph
  证明: rfl
-/
lemma _root_.Equiv.symm_simpleGraph (e : V ≃ W) : e.simpleGraph.symm = e.symm.simpleGraph := rfl

/-! ## Induced graphs -/


/- Given a set `s` of vertices, we can restrict a graph to those vertices by restricting its
adjacency relation. This gives a map between `SimpleGraph V` and `SimpleGraph s`.

There is also a notion of induced subgraphs (see `SimpleGraph.Subgraph.induce`). -/
/--
Definition of `induce` / `induce` 的定义

English:
abbreviation induce
  signature: (s : Set V) (G : SimpleGraph V)
  body: G.comap (Function.Embedding.subtype _)

中文:
缩写 induce
  签名: (s : 集合 V) (G : 简单图 V)
  定义体: G.comap (Function.Embedding.subtype _)

Depends on / 依赖: Embedding, Function, Function.Embedding.subtype, G.comap, subtype
-/
abbrev induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)

variable {G} in
/--
lemma `induce_adj` / 引理 `induce_adj`

English:
lemma induce_adj
  given: {s : Set V} {u v : s}
  statement: (G.induce s).Adj u v ↔ G.Adj u v
  proof: .rfl

中文:
引理 induce_adj
  条件: {s : 集合 V} {u v : s}
  结论: (G.induce s).伴随 u v ↔ G.伴随 u v
  证明: .rfl
-/
lemma induce_adj {s : Set V} {u v : s} : (G.induce s).Adj u v ↔ G.Adj u v := .rfl

/--
lemma `induce_top` / 引理 `induce_top`

English:
lemma induce_top
  given: (s : Set V)
  statement: (completeGraph V).induce s = completeGraph s
  proof: comap_top Subtype.val_injective

中文:
引理 induce_top
  条件: (s : 集合 V)
  结论: (completeGraph V).induce s = completeGraph s
  证明: comap_top Subtype.val_injective
-/
@[simp] lemma induce_top (s : Set V) : (completeGraph V).induce s = completeGraph s :=
  comap_top Subtype.val_injective

/--
lemma `induce_bot` / 引理 `induce_bot`

English:
lemma induce_bot
  given: (s : Set V)
  statement: (⊥ : SimpleGraph V).induce s = ⊥
  proof: by
  dsimp

中文:
引理 induce_bot
  条件: (s : 集合 V)
  结论: (⊥ : 简单图 V).induce s = ⊥
  证明: by
  dsimp
-/
lemma induce_bot (s : Set V) : (⊥ : SimpleGraph V).induce s = ⊥ := by
  dsimp

/--
lemma `support_induce_subset_coe_preimage` / 引理 `support_induce_subset_coe_preimage`

English:
lemma support_induce_subset_coe_preimage
  given: (s : Set V)
  statement: (G.induce s).support subseteq (↑) ⁻¹' s
  proof: fun v _ => v.prop

中文:
引理 support_induce_subset_coe_preimage
  条件: (s : 集合 V)
  结论: (G.induce s).support subseteq (↑) ⁻¹' s
  证明: fun v _ => v.prop

Depends on / 依赖: v.prop
-/
lemma support_induce_subset_coe_preimage (s : Set V) : (G.induce s).support subseteq (↑) ⁻¹' s :=
  fun v _ => v.prop

/--
lemma `support_induce_subset_coe_preimage_support` / 引理 `support_induce_subset_coe_preimage_support`

English:
lemma support_induce_subset_coe_preimage_support
  given: (s : Set V)
  proof: fun _ ⟨v, hadj⟩ => ⟨v, hadj⟩

中文:
引理 support_induce_subset_coe_preimage_support
  条件: (s : 集合 V)
  证明: fun _ ⟨v, hadj⟩ => ⟨v, hadj⟩
-/
lemma support_induce_subset_coe_preimage_support (s : Set V) :
    (G.induce s).support subseteq (↑) ⁻¹' G.support :=
  fun _ ⟨v, hadj⟩ => ⟨v, hadj⟩

/--
lemma `induce_singleton_eq_top` / 引理 `induce_singleton_eq_top`

English:
lemma induce_singleton_eq_top
  given: (v : V)
  statement: G.induce {v} = ⊤
  proof: by
  rw [eq_top_iff]; apply le_comap_of_subsingleton

中文:
引理 induce_singleton_eq_top
  条件: (v : V)
  结论: G.induce {v} = ⊤
  证明: by
  rw [eq_top_iff]; apply le_comap_of_subsingleton
-/
@[simp] lemma induce_singleton_eq_top (v : V) : G.induce {v} = ⊤ := by
  rw [eq_top_iff]; apply le_comap_of_subsingleton

/--
Definition of `spanningCoe` / `spanningCoe` 的定义

English:
abbreviation spanningCoe
  signature: {s : Set V} (G : SimpleGraph s)
  body: G.map (Function.Embedding.subtype _)

中文:
缩写 spanningCoe
  签名: {s : 集合 V} (G : 简单图 s)
  定义体: G.map (Function.Embedding.subtype _)

Depends on / 依赖: Embedding, Function, Function.Embedding.subtype, G.map, subtype
-/
abbrev spanningCoe {s : Set V} (G : SimpleGraph s) : SimpleGraph V :=
  G.map (Function.Embedding.subtype _)

/--
theorem `support_spanningCoe` / 定理 `support_spanningCoe`

English:
theorem support_spanningCoe
  given: {s : Set V} (G : SimpleGraph s)
  proof: G.support_map _

中文:
定理 support_spanningCoe
  条件: {s : 集合 V} (G : 简单图 s)
  证明: G.support_map _

Depends on / 依赖: G.support_map, support_map
-/
theorem support_spanningCoe {s : Set V} (G : SimpleGraph s) :
    G.spanningCoe.support = (↑) '' G.support :=
  G.support_map _

/--
theorem `induce_spanningCoe` / 定理 `induce_spanningCoe`

English:
theorem induce_spanningCoe
  given: {s : Set V} {G : SimpleGraph s}
  statement: G.spanningCoe.induce s = G
  proof: comap_map_eq _ _

中文:
定理 induce_spanningCoe
  条件: {s : 集合 V} {G : 简单图 s}
  结论: G.spanningCoe.induce s = G
  证明: comap_map_eq _ _

Depends on / 依赖: comap_map_eq
-/
theorem induce_spanningCoe {s : Set V} {G : SimpleGraph s} : G.spanningCoe.induce s = G :=
  comap_map_eq _ _

/--
theorem `spanningCoe_induce_le` / 定理 `spanningCoe_induce_le`

English:
theorem spanningCoe_induce_le
  given: (s : Set V)
  statement: (G.induce s).spanningCoe <= G
  proof: map_comap_le _ _

中文:
定理 spanningCoe_induce_le
  条件: (s : 集合 V)
  结论: (G.induce s).spanningCoe <= G
  证明: map_comap_le _ _

Depends on / 依赖: map_comap_le
-/
theorem spanningCoe_induce_le (s : Set V) : (G.induce s).spanningCoe <= G :=
  map_comap_le _ _

/--
theorem `spanningCoe_induce_eq_self` / 定理 `spanningCoe_induce_eq_self`

English:
theorem spanningCoe_induce_eq_self
  given: (s : Set V)
  statement: (G.induce s).spanningCoe = G ↔ G.support subseteq s
  proof: by
  refine ⟨fun h v hv => ?_, fun h => le_antisymm (G.spanningCoe_induce_le s) fun u v hadj => ?_⟩
  · rw [← h, support_spanningCoe] at hv
    have ⟨u, _, hvu⟩ := hv
    exact hvu ▸ u.prop
  · exact ⟨hadj.ne, ⟨u, h hadj.left_mem_support⟩, ⟨v, h hadj.right_mem_support⟩, hadj, rfl, rfl⟩

@[simp]

中文:
定理 spanningCoe_induce_eq_self
  条件: (s : 集合 V)
  结论: (G.induce s).spanningCoe = G ↔ G.support subseteq s
  证明: by
  refine ⟨fun h v hv => ?_, fun h => le_antisymm (G.spanningCoe_induce_le s) fun u v hadj => ?_⟩
  · rw [← h, support_spanningCoe] at hv
    have ⟨u, _, hvu⟩ := hv
    exact hvu ▸ u.prop
  · exact ⟨hadj.ne, ⟨u, h hadj.left_mem_support⟩, ⟨v, h hadj.right_mem_support⟩, hadj, rfl, rfl⟩

@[simp]

Depends on / 依赖: G.spanningCoe_induce_le, hadj.left_mem_support, hadj.ne, hadj.right_mem_support, le_antisymm, left_mem_support, right_mem_support, spanningCoe_induce_le, support_spanningCoe, u.prop
-/
theorem spanningCoe_induce_eq_self (s : Set V) : (G.induce s).spanningCoe = G ↔ G.support subseteq s := by
  refine ⟨fun h v hv => ?_, fun h => le_antisymm (G.spanningCoe_induce_le s) fun u v hadj => ?_⟩
  · rw [← h, support_spanningCoe] at hv
    have ⟨u, _, hvu⟩ := hv
    exact hvu ▸ u.prop
  · exact ⟨hadj.ne, ⟨u, h hadj.left_mem_support⟩, ⟨v, h hadj.right_mem_support⟩, hadj, rfl, rfl⟩

@[simp]
/--
theorem `spanningCoe_induce_support` / 定理 `spanningCoe_induce_support`

English:
theorem spanningCoe_induce_support
  statement: (G.induce G.support).spanningCoe = G
  proof: .mpr .rfl G.spanningCoe_induce_eq_self _

@[simp]

中文:
定理 spanningCoe_induce_support
  结论: (G.induce G.support).spanningCoe = G
  证明: .mpr .rfl G.spanningCoe_induce_eq_self _

@[simp]

Depends on / 依赖: G.spanningCoe_induce_eq_self, spanningCoe_induce_eq_self
-/
theorem spanningCoe_induce_support : (G.induce G.support).spanningCoe = G :=
.mpr .rfl G.spanningCoe_induce_eq_self _

@[simp]
/--
theorem `spanningCoe_induce_univ` / 定理 `spanningCoe_induce_univ`

English:
theorem spanningCoe_induce_univ
  statement: (G.induce .univ).spanningCoe = G
  proof: .mpr G.support.subset_univ G.spanningCoe_induce_eq_self _

中文:
定理 spanningCoe_induce_univ
  结论: (G.induce .univ).spanningCoe = G
  证明: .mpr G.support.subset_univ G.spanningCoe_induce_eq_self _

Depends on / 依赖: G.spanningCoe_induce_eq_self, G.support.subset_univ, spanningCoe_induce_eq_self, subset_univ, support
-/
theorem spanningCoe_induce_univ : (G.induce .univ).spanningCoe = G :=
.mpr G.support.subset_univ G.spanningCoe_induce_eq_self _

open Set.Notation in
/--
theorem `IsCompleteBetween.induce` / 定理 `IsCompleteBetween.induce`

English:
theorem IsCompleteBetween.induce
  given: {s t : Set V} (h : G.IsCompleteBetween s t) (u : Set V)
  proof: by
  intro _ hs _ ht
  rw [comap_adj]; rw [Embedding.coe_subtype]
  exact h hs ht

中文:
定理 IsCompleteBetween.induce
  条件: {s t : 集合 V} (h : G.IsCompleteBetween s t) (u : 集合 V)
  证明: by
  intro _ hs _ ht
  rw [comap_adj]; rw [Embedding.coe_subtype]
  exact h hs ht

Depends on / 依赖: Embedding, Embedding.coe_subtype, coe_subtype, comap_adj
-/
theorem IsCompleteBetween.induce {s t : Set V} (h : G.IsCompleteBetween s t) (u : Set V) :
    (G.induce u).IsCompleteBetween (u ↓inter s) (u ↓inter t) := by
  intro _ hs _ ht
  rw [comap_adj]; rw [Embedding.coe_subtype]
  exact h hs ht

/-! ## Homomorphisms, embeddings and isomorphisms -/


/--
Definition of `Hom` / `Hom` 的定义

English:
abbreviation Hom
  body: RelHom G.Adj G'.Adj

中文:
缩写 态射
  定义体: RelHom G.Adj G'.Adj

Depends on / 依赖: G.Adj, RelHom
-/
abbrev Hom :=
  RelHom G.Adj G'.Adj

/--
Definition of `Embedding` / `Embedding` 的定义

English:
abbreviation Embedding
  body: RelEmbedding G.Adj G'.Adj

中文:
缩写 嵌入
  定义体: RelEmbedding G.Adj G'.Adj

Depends on / 依赖: G.Adj, RelEmbedding
-/
abbrev Embedding :=
  RelEmbedding G.Adj G'.Adj

/--
Definition of `Iso` / `Iso` 的定义

English:
abbreviation Iso
  body: RelIso G.Adj G'.Adj

@[inherit_doc] infixl:50 " ->g " => Hom
@[inherit_doc] infixl:50 " ↪g " => Embedding
@[inherit_doc] infixl:50 " ≃g " => Iso

中文:
缩写 同构
  定义体: RelIso G.Adj G'.Adj

@[inherit_doc] infixl:50 " ->g " => Hom
@[inherit_doc] infixl:50 " ↪g " => Embedding
@[inherit_doc] infixl:50 " ≃g " => Iso

Depends on / 依赖: G.Adj, RelIso
-/
abbrev Iso :=
  RelIso G.Adj G'.Adj

@[inherit_doc] infixl:50 " ->g " => Hom
@[inherit_doc] infixl:50 " ↪g " => Embedding
@[inherit_doc] infixl:50 " ≃g " => Iso

/--
Definition of `HomClass` / `HomClass` 的定义

English:
abbreviation HomClass
  signature: (F : Type*) (G : SimpleGraph V) (H : SimpleGraph W) [FunLike F V W]
  body: RelHomClass F G.Adj H.Adj

中文:
缩写 态射类
  签名: (F : 类型) (G : 简单图 V) (H : 简单图 W) [函数状 F V W]
  定义体: RelHomClass F G.Adj H.Adj

Depends on / 依赖: G.Adj, H.Adj, RelHomClass
-/
abbrev HomClass (F : Type*) (G : SimpleGraph V) (H : SimpleGraph W) [FunLike F V W] :=
  RelHomClass F G.Adj H.Adj

namespace Hom

variable {G G'} {G₁ G₂ : SimpleGraph V} {H : SimpleGraph W} (f : G ->g G')

/--
Definition of `id` / `id` 的定义

English:
abbreviation id
  signature: : G ->g G
  body: RelHom.id _

中文:
缩写 id
  签名: : G ->g G
  定义体: RelHom.id _
-/
protected abbrev id : G ->g G :=
  RelHom.id _

/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  statement: ⇑(Hom.id : G ->g G) = id
  proof: rfl

中文:
引理 coe_id
  结论: ⇑(态射.id : G ->g G) = id
  证明: rfl
-/
@[simp, norm_cast] lemma coe_id : ⇑(Hom.id : G ->g G) = id := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: (V -> W)] : IsEmpty (G ->g H)
  body: DFunLike.coe.isEmpty

中文:
实例 [是空
  签名: (V -> W)] : 是空 (G ->g H)
  定义体: DFunLike.coe.isEmpty

Depends on / 依赖: DFunLike, DFunLike.coe.isEmpty, isEmpty
-/
instance [IsEmpty (V -> W)] : IsEmpty (G ->g H) := DFunLike.coe.isEmpty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: (V -> W)] : Subsingleton (G ->g H)
  body: DFunLike.coe_injective.subsingleton

中文:
实例 [子单例
  签名: (V -> W)] : 子单例 (G ->g H)
  定义体: DFunLike.coe_injective.subsingleton

Depends on / 依赖: DFunLike, DFunLike.coe_injective.subsingleton, coe_injective, subsingleton
-/
instance [Subsingleton (V -> W)] : Subsingleton (G ->g H) := DFunLike.coe_injective.subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: V] : Unique (G ->g H) where
  body: ⟨isEmptyElim, fun {a} => isEmptyElim a⟩
  uniq _ := Subsingleton.elim _ _

中文:
实例 [是空
  签名: V] : 唯一 (G ->g H) where
  定义体: ⟨isEmptyElim, fun {a} => isEmptyElim a⟩
  uniq _ := Subsingleton.elim _ _

Depends on / 依赖: isEmptyElim
-/
instance [IsEmpty V] : Unique (G ->g H) where
  default := ⟨isEmptyElim, fun {a} => isEmptyElim a⟩
  uniq _ := Subsingleton.elim _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: V] [Finite W] : Finite (G ->g H)
  body: DFunLike.finite _

中文:
实例 [有限
  签名: V] [有限 W] : 有限 (G ->g H)
  定义体: DFunLike.finite _

Depends on / 依赖: DFunLike, DFunLike.finite, finite
-/
instance [Finite V] [Finite W] : Finite (G ->g H) := DFunLike.finite _

/--
theorem `map_adj` / 定理 `map_adj`

English:
theorem map_adj
  given: {v w : V} (h : G.Adj v w)
  statement: G'.Adj (f v) (f w)
  proof: f.map_rel' h

中文:
定理 map_adj
  条件: {v w : V} (h : G.伴随 v w)
  结论: G'.伴随 (f v) (f w)
  证明: f.map_rel' h

Depends on / 依赖: f.map_rel, map_rel
-/
theorem map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v) (f w) :=
  f.map_rel' h

/--
theorem `map_mem_edgeSet` / 定理 `map_mem_edgeSet`

English:
theorem map_mem_edgeSet
  given: {e : Sym2 V} (h : e in G.edgeSet)
  statement: e.map f in G'.edgeSet
  proof: Sym2.ind (fun _ _ => f.map_rel') e h

中文:
定理 map_mem_edgeSet
  条件: {e : Sym2 V} (h : e in G.edgeSet)
  结论: e.map f in G'.edgeSet
  证明: Sym2.ind (fun _ _ => f.map_rel') e h

Depends on / 依赖: Sym2.ind, f.map_rel, map_rel
-/
theorem map_mem_edgeSet {e : Sym2 V} (h : e in G.edgeSet) : e.map f in G'.edgeSet :=
  Sym2.ind (fun _ _ => f.map_rel') e h

/--
theorem `subset_preimage_edgeSet` / 定理 `subset_preimage_edgeSet`

English:
theorem subset_preimage_edgeSet
  statement: G.edgeSet subseteq Sym2.map f ⁻¹' G'.edgeSet
  proof: fun _ => f.map_mem_edgeSet

中文:
定理 subset_preimage_edgeSet
  结论: G.edgeSet subseteq Sym2.map f ⁻¹' G'.edgeSet
  证明: fun _ => f.map_mem_edgeSet

Depends on / 依赖: f.map_mem_edgeSet, map_mem_edgeSet
-/
theorem subset_preimage_edgeSet : G.edgeSet subseteq Sym2.map f ⁻¹' G'.edgeSet :=
  fun _ => f.map_mem_edgeSet

/--
theorem `image_edgeSet_subset` / 定理 `image_edgeSet_subset`

English:
theorem image_edgeSet_subset
  statement: Sym2.map f '' G.edgeSet subseteq G'.edgeSet
  proof: Set.image_subset_iff.mpr f.subset_preimage_edgeSet

中文:
定理 image_edgeSet_subset
  结论: Sym2.map f '' G.edgeSet subseteq G'.edgeSet
  证明: Set.image_subset_iff.mpr f.subset_preimage_edgeSet

Depends on / 依赖: Set.image_subset_iff.mpr, f.subset_preimage_edgeSet, image_subset_iff, subset_preimage_edgeSet
-/
theorem image_edgeSet_subset : Sym2.map f '' G.edgeSet subseteq G'.edgeSet :=
  Set.image_subset_iff.mpr f.subset_preimage_edgeSet

/--
theorem `apply_mem_neighborSet` / 定理 `apply_mem_neighborSet`

English:
theorem apply_mem_neighborSet
  given: {v w : V} (h : w in G.neighborSet v)
  statement: f w in G'.neighborSet (f v)
  proof: map_adj f h

中文:
定理 apply_mem_neighborSet
  条件: {v w : V} (h : w in G.neighborSet v)
  结论: f w in G'.neighborSet (f v)
  证明: map_adj f h

Depends on / 依赖: map_adj
-/
theorem apply_mem_neighborSet {v w : V} (h : w in G.neighborSet v) : f w in G'.neighborSet (f v) :=
  map_adj f h

variable (v) in
/--
theorem `subset_preimage_neighborSet` / 定理 `subset_preimage_neighborSet`

English:
theorem subset_preimage_neighborSet
  statement: G.neighborSet v subseteq f ⁻¹' G'.neighborSet (f v)
  proof: fun _ => f.apply_mem_neighborSet

中文:
定理 subset_preimage_neighborSet
  结论: G.neighborSet v subseteq f ⁻¹' G'.neighborSet (f v)
  证明: fun _ => f.apply_mem_neighborSet

Depends on / 依赖: apply_mem_neighborSet, f.apply_mem_neighborSet
-/
theorem subset_preimage_neighborSet : G.neighborSet v subseteq f ⁻¹' G'.neighborSet (f v) :=
  fun _ => f.apply_mem_neighborSet

variable (v) in
/--
theorem `image_neighborSet_subset` / 定理 `image_neighborSet_subset`

English:
theorem image_neighborSet_subset
  statement: f '' G.neighborSet v subseteq G'.neighborSet (f v)
  proof: Set.image_subset_iff.mpr f.subset_preimage_neighborSet v

中文:
定理 image_neighborSet_subset
  结论: f '' G.neighborSet v subseteq G'.neighborSet (f v)
  证明: Set.image_subset_iff.mpr f.subset_preimage_neighborSet v

Depends on / 依赖: Set.image_subset_iff.mpr, f.subset_preimage_neighborSet, image_subset_iff, subset_preimage_neighborSet
-/
theorem image_neighborSet_subset : f '' G.neighborSet v subseteq G'.neighborSet (f v) :=
Set.image_subset_iff.mpr f.subset_preimage_neighborSet v

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `Sym2.map`. -/
@[simps]
/--
Definition of `mapEdgeSet` / `mapEdgeSet` 的定义

English:
definition mapEdgeSet
  signature: (e : G.edgeSet)
  body: ⟨Sym2.map f e, f.map_mem_edgeSet e.property⟩

中文:
定义 mapEdgeSet
  签名: (e : G.edgeSet)
  定义体: ⟨Sym2.map f e, f.map_mem_edgeSet e.property⟩

Depends on / 依赖: Sym2.map, e.property, f.map_mem_edgeSet, map_mem_edgeSet, property
-/
def mapEdgeSet (e : G.edgeSet) : G'.edgeSet :=
  ⟨Sym2.map f e, f.map_mem_edgeSet e.property⟩

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps]
/--
Definition of `mapNeighborSet` / `mapNeighborSet` 的定义

English:
definition mapNeighborSet
  signature: (v : V) (w : G.neighborSet v)
  body: ⟨f w, f.apply_mem_neighborSet w.property⟩

中文:
定义 mapNeighborSet
  签名: (v : V) (w : G.neighborSet v)
  定义体: ⟨f w, f.apply_mem_neighborSet w.property⟩

Depends on / 依赖: apply_mem_neighborSet, f.apply_mem_neighborSet, property, w.property
-/
def mapNeighborSet (v : V) (w : G.neighborSet v) : G'.neighborSet (f v) :=
  ⟨f w, f.apply_mem_neighborSet w.property⟩

/--
Definition of `mapDart` / `mapDart` 的定义

English:
definition mapDart
  signature: (d : G.Dart)
  body: ⟨d.1.map f f, f.map_adj d.2⟩

@[simp]

中文:
定义 mapDart
  签名: (d : G.Dart)
  定义体: ⟨d.1.map f f, f.map_adj d.2⟩

@[simp]

Depends on / 依赖: f.map_adj, map_adj
-/
def mapDart (d : G.Dart) : G'.Dart :=
  ⟨d.1.map f f, f.map_adj d.2⟩

@[simp]
/--
theorem `mapDart_apply` / 定理 `mapDart_apply`

English:
theorem mapDart_apply
  given: (d : G.Dart)
  statement: f.mapDart d = ⟨d.1.map f f, f.map_adj d.2⟩
  proof: rfl

中文:
定理 mapDart_apply
  条件: (d : G.Dart)
  结论: f.mapDart d = ⟨d.1.map f f, f.map_adj d.2⟩
  证明: rfl
-/
theorem mapDart_apply (d : G.Dart) : f.mapDart d = ⟨d.1.map f f, f.map_adj d.2⟩ :=
  rfl

/-- The graph homomorphism from a smaller graph to a bigger one. -/
@[implicit_reducible]
/--
Definition of `ofLE` / `ofLE` 的定义

English:
definition ofLE
  signature: (h : G₁ <= G₂)
  body: ⟨id, @h⟩

中文:
定义 ofLE
  签名: (h : G₁ <= G₂)
  定义体: ⟨id, @h⟩
-/
def ofLE (h : G₁ <= G₂) : G₁ ->g G₂ := ⟨id, @h⟩

/--
lemma `coe_ofLE` / 引理 `coe_ofLE`

English:
lemma coe_ofLE
  given: (h : G₁ <= G₂)
  statement: ⇑(ofLE h) = id
  proof: rfl

中文:
引理 coe_ofLE
  条件: (h : G₁ <= G₂)
  结论: ⇑(ofLE h) = id
  证明: rfl
-/
@[simp, norm_cast] lemma coe_ofLE (h : G₁ <= G₂) : ⇑(ofLE h) = id := rfl

/--
lemma `ofLE_apply` / 引理 `ofLE_apply`

English:
lemma ofLE_apply
  given: (h : G₁ <= G₂) (v : V)
  statement: ofLE h v = v
  proof: rfl

中文:
引理 ofLE_apply
  条件: (h : G₁ <= G₂) (v : V)
  结论: ofLE h v = v
  证明: rfl
-/
lemma ofLE_apply (h : G₁ <= G₂) (v : V) : ofLE h v = v := rfl

/--
theorem `mapEdgeSet.injective` / 定理 `mapEdgeSet.injective`

English:
theorem mapEdgeSet.injective
  given: (hinj : Function.Injective f)
  statement: Function.Injective f.mapEdgeSet
  proof: by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [Hom.mapEdgeSet]
  repeat rw [Subtype.mk_eq_mk]
  apply Sym2.map.injective hinj

中文:
定理 mapEdgeSet.injective
  条件: (hinj : 函数.单射 f)
  结论: 函数.单射 f.mapEdgeSet
  证明: by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [Hom.mapEdgeSet]
  repeat rw [Subtype.mk_eq_mk]
  apply Sym2.map.injective hinj

Depends on / 依赖: Hom.mapEdgeSet, Subtype, Subtype.mk_eq_mk, Sym2.map.injective, injective, mapEdgeSet, mk_eq_mk, repeat
-/
theorem mapEdgeSet.injective (hinj : Function.Injective f) : Function.Injective f.mapEdgeSet := by
  rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
  dsimp [Hom.mapEdgeSet]
  repeat rw [Subtype.mk_eq_mk]
  apply Sym2.map.injective hinj

/--
theorem `injective_of_top_hom` / 定理 `injective_of_top_hom`

English:
theorem injective_of_top_hom
  given: (f : (⊤ : SimpleGraph V) ->g G')
  statement: Function.Injective f
  proof: by
  intro v w h
  contrapose! h
  exact G'.ne_of_adj (map_adj _ ((top_adj _ _).mpr h))

中文:
定理 injective_of_top_hom
  条件: (f : (⊤ : 简单图 V) ->g G')
  结论: 函数.单射 f
  证明: by
  intro v w h
  contrapose! h
  exact G'.ne_of_adj (map_adj _ ((top_adj _ _).mpr h))

Depends on / 依赖: contrapose, map_adj, ne_of_adj, top_adj
-/
theorem injective_of_top_hom (f : (⊤ : SimpleGraph V) ->g G') : Function.Injective f := by
  intro v w h
  contrapose! h
  exact G'.ne_of_adj (map_adj _ ((top_adj _ _).mpr h))

/-- A function `f` that is injective on adjacent vertices in a graph `G`
(equivalently `f` is a valid `W`-coloring of `G`, or `G ≤ comap ⊤ f`)
is a homomorphism from `G` to the mapped graph. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : V -> W) (G : SimpleGraph V) (h : forall {u v}, G.Adj u v -> f u != f v)
  body: f
  map_rel' {u v} hadj := ⟨h hadj, u, v, hadj, rfl, rfl⟩

中文:
定义 map
  签名: (f : V -> W) (G : 简单图 V) (h : 对任意 {u v}, G.伴随 u v -> f u != f v)
  定义体: f
  map_rel' {u v} hadj := ⟨h hadj, u, v, hadj, rfl, rfl⟩
-/
protected def map (f : V -> W) (G : SimpleGraph V) (h : forall {u v}, G.Adj u v -> f u != f v) :
    G ->g G.map f where
  toFun := f
  map_rel' {u v} hadj := ⟨h hadj, u, v, hadj, rfl, rfl⟩

/-- There is a homomorphism to a graph from a comapped graph.
When the function is injective, this is an embedding (see `SimpleGraph.Embedding.comap`). -/
@[simps]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : V -> W) (G : SimpleGraph W)
  body: f
  map_rel' := by simp

中文:
定义 comap
  签名: (f : V -> W) (G : 简单图 W)
  定义体: f
  map_rel' := by simp
-/
protected def comap (f : V -> W) (G : SimpleGraph W) : G.comap f ->g G where
  toFun := f
  map_rel' := by simp

/--
theorem `le_comap` / 定理 `le_comap`

English:
theorem le_comap
  given: (f : H ->g G)
  statement: H <= G.comap f
  proof: fun _ _ => f.map_adj

中文:
定理 le_comap
  条件: (f : H ->g G)
  结论: H <= G.comap f
  证明: fun _ _ => f.map_adj

Depends on / 依赖: f.map_adj, map_adj
-/
theorem le_comap (f : H ->g G) : H <= G.comap f :=
  fun _ _ => f.map_adj

/--
theorem `nonempty_hom_iff_exists_le_comap` / 定理 `nonempty_hom_iff_exists_le_comap`

English:
theorem nonempty_hom_iff_exists_le_comap
  statement: Nonempty (H ->g G) ↔ exists f, H <= G.comap f
  proof: ⟨fun ⟨f⟩ => ⟨f, f.le_comap⟩, fun ⟨f, h⟩ => ⟨f, (h ·)⟩⟩

中文:
定理 nonempty_hom_iff_存在_le_comap
  结论: 非空 (H ->g G) ↔ 存在 f, H <= G.comap f
  证明: ⟨fun ⟨f⟩ => ⟨f, f.le_comap⟩, fun ⟨f, h⟩ => ⟨f, (h ·)⟩⟩

Depends on / 依赖: f.le_comap, le_comap
-/
theorem nonempty_hom_iff_exists_le_comap : Nonempty (H ->g G) ↔ exists f, H <= G.comap f :=
  ⟨fun ⟨f⟩ => ⟨f, f.le_comap⟩, fun ⟨f, h⟩ => ⟨f, (h ·)⟩⟩

variable {G'' : SimpleGraph X} {G''' : SimpleGraph Y}

/--
Definition of `comp` / `comp` 的定义

English:
abbreviation comp
  signature: (f' : G' ->g G'') (f : G ->g G')
  body: RelHom.comp f' f

@[simp]

中文:
缩写 comp
  签名: (f' : G' ->g G'') (f : G ->g G')
  定义体: RelHom.comp f' f

@[simp]

Depends on / 依赖: RelHom, RelHom.comp
-/
abbrev comp (f' : G' ->g G'') (f : G ->g G') : G ->g G'' :=
  RelHom.comp f' f

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f' : G' ->g G'') (f : G ->g G')
  statement: ⇑(f'.comp f) = f' ∘ f
  proof: rfl

中文:
定理 coe_comp
  条件: (f' : G' ->g G'') (f : G ->g G')
  结论: ⇑(f'.comp f) = f' ∘ f
  证明: rfl
-/
theorem coe_comp (f' : G' ->g G'') (f : G ->g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : G'' ->g G''') (g : G' ->g G'') (h : G ->g G')
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : G'' ->g G''') (g : G' ->g G'') (h : G ->g G')
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : G'' ->g G''') (g : G' ->g G'') (h : G ->g G') :
    f.comp (g.comp h) = (f.comp g).comp h := rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : G ->g G')
  statement: f.comp .id = f
  proof: rfl

@[simp]

中文:
定理 comp_id
  条件: (f : G ->g G')
  结论: f.comp .id = f
  证明: rfl

@[simp]
-/
theorem comp_id (f : G ->g G') : f.comp .id = f := rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : G ->g G')
  statement: .comp .id f = f
  proof: rfl

@[simp]

中文:
定理 id_comp
  条件: (f : G ->g G')
  结论: .comp .id f = f
  证明: rfl

@[simp]
-/
theorem id_comp (f : G ->g G') : .comp .id f = f := rfl

@[simp]
/--
theorem `comp_comap_ofLE` / 定理 `comp_comap_ofLE`

English:
theorem comp_comap_ofLE
  given: (f : H ->g G)
  statement: .comp (.comap f G) (.ofLE f.le_comap) = f
  proof: rfl

中文:
定理 comp_comap_ofLE
  条件: (f : H ->g G)
  结论: .comp (.comap f G) (.ofLE f.le_comap) = f
  证明: rfl
-/
theorem comp_comap_ofLE (f : H ->g G) : .comp (.comap f G) (.ofLE f.le_comap) = f :=
  rfl

end Hom

namespace Embedding

variable {G G'} {H : SimpleGraph W} (f : G ↪g G')

/--
Definition of `refl` / `refl` 的定义

English:
abbreviation refl
  signature: : G ↪g G
  body: RelEmbedding.refl _

中文:
缩写 refl
  签名: : G ↪g G
  定义体: RelEmbedding.refl _

Depends on / 依赖: RelEmbedding, RelEmbedding.refl
-/
abbrev refl : G ↪g G :=
  RelEmbedding.refl _

/--
Definition of `toHom` / `toHom` 的定义

English:
abbreviation toHom
  signature: : G ->g G'
  body: f.toRelHom

中文:
缩写 toHom
  签名: : G ->g G'
  定义体: f.toRelHom

Depends on / 依赖: f.toRelHom, toRelHom
-/
abbrev toHom : G ->g G' :=
  f.toRelHom

/--
lemma `coe_toHom` / 引理 `coe_toHom`

English:
lemma coe_toHom
  given: (f : G ↪g H)
  statement: ⇑f.toHom = f
  proof: rfl

中文:
引理 coe_toHom
  条件: (f : G ↪g H)
  结论: ⇑f.toHom = f
  证明: rfl
-/
@[simp] lemma coe_toHom (f : G ↪g H) : ⇑f.toHom = f := rfl

/--
theorem `map_adj_iff` / 定理 `map_adj_iff`

English:
theorem map_adj_iff
  given: {v w : V}
  statement: G'.Adj (f v) (f w) ↔ G.Adj v w
  proof: f.map_rel_iff

中文:
定理 map_adj_iff
  条件: {v w : V}
  结论: G'.伴随 (f v) (f w) ↔ G.伴随 v w
  证明: f.map_rel_iff
-/
@[simp] theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff

/--
theorem `map_mem_edgeSet_iff` / 定理 `map_mem_edgeSet_iff`

English:
theorem map_mem_edgeSet_iff
  given: {e : Sym2 V}
  statement: e.map f in G'.edgeSet ↔ e in G.edgeSet
  proof: Sym2.ind (fun _ _ => f.map_adj_iff) e

@[simp]

中文:
定理 map_mem_edgeSet_iff
  条件: {e : Sym2 V}
  结论: e.map f in G'.edgeSet ↔ e in G.edgeSet
  证明: Sym2.ind (fun _ _ => f.map_adj_iff) e

@[simp]

Depends on / 依赖: Sym2.ind, f.map_adj_iff, map_adj_iff
-/
theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f in G'.edgeSet ↔ e in G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e

@[simp]
/--
theorem `preimage_edgeSet` / 定理 `preimage_edgeSet`

English:
theorem preimage_edgeSet
  statement: Sym2.map f ⁻¹' G'.edgeSet = G.edgeSet
  proof: Set.ext fun _ => map_mem_edgeSet_iff f

中文:
定理 preimage_edgeSet
  结论: Sym2.map f ⁻¹' G'.edgeSet = G.edgeSet
  证明: Set.ext fun _ => map_mem_edgeSet_iff f

Depends on / 依赖: Set.ext, map_mem_edgeSet_iff
-/
theorem preimage_edgeSet : Sym2.map f ⁻¹' G'.edgeSet = G.edgeSet :=
  Set.ext fun _ => map_mem_edgeSet_iff f

/--
theorem `apply_mem_neighborSet_iff` / 定理 `apply_mem_neighborSet_iff`

English:
theorem apply_mem_neighborSet_iff
  given: {v w : V}
  statement: f w in G'.neighborSet (f v) ↔ w in G.neighborSet v
  proof: map_adj_iff f

中文:
定理 apply_mem_neighborSet_iff
  条件: {v w : V}
  结论: f w in G'.neighborSet (f v) ↔ w in G.neighborSet v
  证明: map_adj_iff f

Depends on / 依赖: map_adj_iff
-/
theorem apply_mem_neighborSet_iff {v w : V} : f w in G'.neighborSet (f v) ↔ w in G.neighborSet v :=
  map_adj_iff f

variable (v) in
@[simp]
/--
theorem `preimage_neighborSet` / 定理 `preimage_neighborSet`

English:
theorem preimage_neighborSet
  statement: f ⁻¹' G'.neighborSet (f v) = G.neighborSet v
  proof: Set.ext fun _ => apply_mem_neighborSet_iff f

中文:
定理 preimage_neighborSet
  结论: f ⁻¹' G'.neighborSet (f v) = G.neighborSet v
  证明: Set.ext fun _ => apply_mem_neighborSet_iff f

Depends on / 依赖: Set.ext, apply_mem_neighborSet_iff
-/
theorem preimage_neighborSet : f ⁻¹' G'.neighborSet (f v) = G.neighborSet v :=
  Set.ext fun _ => apply_mem_neighborSet_iff f

/-- A graph embedding induces an embedding of edge sets. -/
@[simps]
/--
Definition of `mapEdgeSet` / `mapEdgeSet` 的定义

English:
definition mapEdgeSet
  signature: : G.edgeSet ↪ G'.edgeSet where
  body: Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f.toRelHom f.injective

中文:
定义 mapEdgeSet
  签名: : G.edgeSet ↪ G'.edgeSet where
  定义体: Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f.toRelHom f.injective

Depends on / 依赖: Hom.mapEdgeSet, mapEdgeSet
-/
def mapEdgeSet : G.edgeSet ↪ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  inj' := Hom.mapEdgeSet.injective f.toRelHom f.injective

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps]
/--
Definition of `mapNeighborSet` / `mapNeighborSet` 的定义

English:
definition mapNeighborSet
  signature: (v : V)
  body: ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.inj' h

中文:
定义 mapNeighborSet
  签名: (v : V)
  定义体: ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.inj' h

Depends on / 依赖: apply_mem_neighborSet_iff, f.apply_mem_neighborSet_iff.mpr
-/
def mapNeighborSet (v : V) : G.neighborSet v ↪ G'.neighborSet (f v) where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  inj' := by
    rintro ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h
    rw [Subtype.mk_eq_mk] at h ⊢
    exact f.inj' h

/--
Definition of `isoInduceRange` / `isoInduceRange` 的定义

English:
definition isoInduceRange
  signature: : G ≃g G'.induce (Set.range f) where
  body: Equiv.ofInjective f f.injective
  map_rel_iff' := by simp

中文:
定义 isoInduceRange
  签名: : G ≃g G'.induce (集合.range f) where
  定义体: Equiv.ofInjective f f.injective
  map_rel_iff' := by simp

Depends on / 依赖: Equiv.ofInjective, f.injective, injective, ofInjective
-/
noncomputable def isoInduceRange : G ≃g G'.induce (Set.range f) where
  __ := Equiv.ofInjective f f.injective
  map_rel_iff' := by simp

-- Porting note: `@[simps]` does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : V ↪ W) (G : SimpleGraph W)
  body: f
  map_rel_iff' := by simp

@[simp]

中文:
定义 comap
  签名: (f : V ↪ W) (G : 简单图 W)
  定义体: f
  map_rel_iff' := by simp

@[simp]
-/
protected def comap (f : V ↪ W) (G : SimpleGraph W) : G.comap f ↪g G where
  __ := f
  map_rel_iff' := by simp

@[simp]
/--
theorem `comap_apply` / 定理 `comap_apply`

English:
theorem comap_apply
  given: (f : V ↪ W) (G : SimpleGraph W) (v : V)
  proof: rfl

中文:
定理 comap_apply
  条件: (f : V ↪ W) (G : 简单图 W) (v : V)
  证明: rfl
-/
theorem comap_apply (f : V ↪ W) (G : SimpleGraph W) (v : V) :
    SimpleGraph.Embedding.comap f G v = f v := rfl

/--
theorem `comap_eq` / 定理 `comap_eq`

English:
theorem comap_eq
  given: (f : H ↪g G)
  statement: G.comap f = H
  proof: by
  ext
  exact f.map_adj_iff

中文:
定理 comap_eq
  条件: (f : H ↪g G)
  结论: G.comap f = H
  证明: by
  ext
  exact f.map_adj_iff

Depends on / 依赖: f.map_adj_iff, map_adj_iff
-/
theorem comap_eq (f : H ↪g G) : G.comap f = H := by
  ext
  exact f.map_adj_iff

-- Porting note: `@[simps]` does not work here since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : V ↪ W) (G : SimpleGraph V)
  body: f
  map_rel_iff' := by simp

@[simp]

中文:
定义 map
  签名: (f : V ↪ W) (G : 简单图 V)
  定义体: f
  map_rel_iff' := by simp

@[simp]
-/
protected def map (f : V ↪ W) (G : SimpleGraph V) : G ↪g G.map f where
  __ := f
  map_rel_iff' := by simp

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: (f : V ↪ W) (G : SimpleGraph V) (v : V)
  statement: Embedding.map f G v = f v
  proof: rfl

中文:
定理 map_apply
  条件: (f : V ↪ W) (G : 简单图 V) (v : V)
  结论: 嵌入.map f G v = f v
  证明: rfl
-/
theorem map_apply (f : V ↪ W) (G : SimpleGraph V) (v : V) : Embedding.map f G v = f v :=
  rfl

/--
Definition of `induce` / `induce` 的定义

English:
abbreviation induce
  signature: (s : Set V)
  body: .comap (.subtype _) G

中文:
缩写 induce
  签名: (s : 集合 V)
  定义体: .comap (.subtype _) G
-/
protected abbrev induce (s : Set V) : G.induce s ↪g G :=
  .comap (.subtype _) G

/--
Definition of `spanningCoe` / `spanningCoe` 的定义

English:
abbreviation spanningCoe
  signature: {s : Set V} (G : SimpleGraph s)
  body: .map (.subtype _) G

中文:
缩写 spanningCoe
  签名: {s : 集合 V} (G : 简单图 s)
  定义体: .map (.subtype _) G
-/
protected abbrev spanningCoe {s : Set V} (G : SimpleGraph s) : G ↪g G.spanningCoe :=
  .map (.subtype _) G

/--
Definition of `completeGraph` / `completeGraph` 的定义

English:
definition completeGraph
  signature: {α β : Type*} (f : α ↪ β)
  body: f
  map_rel_iff' := by simp

中文:
定义 completeGraph
  签名: {α β : 类型} (f : α ↪ β)
  定义体: f
  map_rel_iff' := by simp
-/
protected def completeGraph {α β : Type*} (f : α ↪ β) : completeGraph α ↪g completeGraph β where
  __ := f
  map_rel_iff' := by simp

/--
lemma `coe_completeGraph` / 引理 `coe_completeGraph`

English:
lemma coe_completeGraph
  given: {α β : Type*} (f : α ↪ β)
  statement: ⇑(Embedding.completeGraph f) = f
  proof: rfl

中文:
引理 coe_completeGraph
  条件: {α β : 类型} (f : α ↪ β)
  结论: ⇑(嵌入.completeGraph f) = f
  证明: rfl
-/
@[simp] lemma coe_completeGraph {α β : Type*} (f : α ↪ β) : ⇑(Embedding.completeGraph f) = f := rfl

variable {G'' : SimpleGraph X} {G''' : SimpleGraph Y}

/--
Definition of `comp` / `comp` 的定义

English:
abbreviation comp
  signature: (f' : G' ↪g G'') (f : G ↪g G')
  body: f.trans f'

@[simp]

中文:
缩写 comp
  签名: (f' : G' ↪g G'') (f : G ↪g G')
  定义体: f.trans f'

@[simp]

Depends on / 依赖: f.trans
-/
abbrev comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' :=
  f.trans f'

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f' : G' ↪g G'') (f : G ↪g G')
  statement: ⇑(f'.comp f) = f' ∘ f
  proof: rfl

中文:
定理 coe_comp
  条件: (f' : G' ↪g G'') (f : G ↪g G')
  结论: ⇑(f'.comp f) = f' ∘ f
  证明: rfl
-/
theorem coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : G'' ↪g G''') (g : G' ↪g G'') (h : G ↪g G')
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : G'' ↪g G''') (g : G' ↪g G'') (h : G ↪g G')
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : G'' ↪g G''') (g : G' ↪g G'') (h : G ↪g G') :
    f.comp (g.comp h) = (f.comp g).comp h := rfl

@[simp]
/--
theorem `comp_refl` / 定理 `comp_refl`

English:
theorem comp_refl
  given: (f : G ↪g G')
  statement: f.comp .refl = f
  proof: rfl

@[simp]

中文:
定理 comp_refl
  条件: (f : G ↪g G')
  结论: f.comp .refl = f
  证明: rfl

@[simp]
-/
theorem comp_refl (f : G ↪g G') : f.comp .refl = f := rfl

@[simp]
/--
theorem `refl_comp` / 定理 `refl_comp`

English:
theorem refl_comp
  given: (f : G ↪g G')
  statement: .comp .refl f = f
  proof: rfl

中文:
定理 refl_comp
  条件: (f : G ↪g G')
  结论: .comp .refl f = f
  证明: rfl
-/
theorem refl_comp (f : G ↪g G') : .comp .refl f = f := rfl

/--
Definition of `complEquiv` / `complEquiv` 的定义

English:
definition complEquiv
  signature: : G ↪g H ≃ Gᶜ ↪g Hᶜ where
  body: ⟨f.toEmbedding, by simp⟩
  invFun f := ⟨f.toEmbedding, fun {v w} => by
    obtain rfl | hvw := eq_or_ne v w
    · simp
    · simpa [hvw, not_iff_not] using f.map_adj_iff (v := v) (w := w)⟩

中文:
定义 complEquiv
  签名: : G ↪g H ≃ Gᶜ ↪g Hᶜ where
  定义体: ⟨f.toEmbedding, by simp⟩
  invFun f := ⟨f.toEmbedding, fun {v w} => by
    obtain rfl | hvw := eq_or_ne v w
    · simp
    · simpa [hvw, not_iff_not] using f.map_adj_iff (v := v) (w := w)⟩

Depends on / 依赖: f.toEmbedding, toEmbedding
-/
def complEquiv : G ↪g H ≃ Gᶜ ↪g Hᶜ where
  toFun f := ⟨f.toEmbedding, by simp⟩
  invFun f := ⟨f.toEmbedding, fun {v w} => by
    obtain rfl | hvw := eq_or_ne v w
    · simp
    · simpa [hvw, not_iff_not] using f.map_adj_iff (v := v) (w := w)⟩

end Embedding

section induceHom

variable {G G'} {G'' : SimpleGraph X} {s : Set V} {t : Set W} {r : Set X}
         (φ : G ->g G') (φst : Set.MapsTo φ s t) (ψ : G' ->g G'') (ψtr : Set.MapsTo ψ t r)

/--
Definition of `induceHom` / `induceHom` 的定义

English:
definition induceHom
  signature: : G.induce s ->g G'.induce t where
  body: Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'

中文:
定义 induceHom
  签名: : G.induce s ->g G'.induce t where
  定义体: Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'

Depends on / 依赖: MapsTo, Set.MapsTo.restrict, restrict
-/
def induceHom : G.induce s ->g G'.induce t where
  toFun := Set.MapsTo.restrict φ s t φst
  map_rel' := φ.map_rel'

/--
lemma `coe_induceHom` / 引理 `coe_induceHom`

English:
lemma coe_induceHom
  statement: ⇑(induceHom φ φst) = Set.MapsTo.restrict φ s t φst
  proof: rfl

中文:
引理 coe_induceHom
  结论: ⇑(induceHom φ φst) = 集合.映射到.restrict φ s t φst
  证明: rfl
-/
@[simp, norm_cast] lemma coe_induceHom : ⇑(induceHom φ φst) = Set.MapsTo.restrict φ s t φst :=
  rfl

/--
lemma `induceHom_id` / 引理 `induceHom_id`

English:
lemma induceHom_id
  given: (G : SimpleGraph V) (s)
  proof: by
  ext x
  rfl

中文:
引理 induceHom_id
  条件: (G : 简单图 V) (s)
  证明: by
  ext x
  rfl
-/
@[simp] lemma induceHom_id (G : SimpleGraph V) (s) :
    induceHom (Hom.id : G ->g G) (Set.mapsTo_id s) = Hom.id := by
  ext x
  rfl

/--
lemma `induceHom_comp` / 引理 `induceHom_comp`

English:
lemma induceHom_comp
  proof: by
  ext x
  rfl

中文:
引理 induceHom_comp
  证明: by
  ext x
  rfl
-/
@[simp] lemma induceHom_comp :
    (induceHom ψ ψtr).comp (induceHom φ φst) = induceHom (ψ.comp φ) (ψtr.comp φst) := by
  ext x
  rfl

/--
lemma `induceHom_injective` / 引理 `induceHom_injective`

English:
lemma induceHom_injective
  given: (hi : Set.InjOn φ s)
  proof: by
  simpa [Set.MapsTo.restrict_inj]

中文:
引理 induceHom_injective
  条件: (hi : 集合.单射限制 φ s)
  证明: by
  simpa [Set.MapsTo.restrict_inj]

Depends on / 依赖: MapsTo, Set.MapsTo.restrict_inj, restrict_inj
-/
lemma induceHom_injective (hi : Set.InjOn φ s) :
    Function.Injective (induceHom φ φst) := by
  simpa [Set.MapsTo.restrict_inj]

end induceHom

section induceHomLE
variable {s s' : Set V} (h : s <= s')

/--
Definition of `induceHomOfLE` / `induceHomOfLE` 的定义

English:
definition induceHomOfLE
  signature: (h : s <= s')
  body: Set.embeddingOfSubset s s' h
  map_rel_iff' := by simp

中文:
定义 induceHomOfLE
  签名: (h : s <= s')
  定义体: Set.embeddingOfSubset s s' h
  map_rel_iff' := by simp

Depends on / 依赖: Set.embeddingOfSubset, embeddingOfSubset
-/
def induceHomOfLE (h : s <= s') : G.induce s ↪g G.induce s' where
  toEmbedding := Set.embeddingOfSubset s s' h
  map_rel_iff' := by simp

/--
lemma `induceHomOfLE_apply` / 引理 `induceHomOfLE_apply`

English:
lemma induceHomOfLE_apply
  given: (v : s)
  statement: (G.induceHomOfLE h) v = Set.inclusion h v
  proof: rfl

中文:
引理 induceHomOfLE_apply
  条件: (v : s)
  结论: (G.induceHomOfLE h) v = 集合.inclusion h v
  证明: rfl
-/
@[simp] lemma induceHomOfLE_apply (v : s) : (G.induceHomOfLE h) v = Set.inclusion h v := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `induceHomOfLE_toHom` / 引理 `induceHomOfLE_toHom`

English:
lemma induceHomOfLE_toHom
  proof: by
  ext; simp

中文:
引理 induceHomOfLE_toHom
  证明: by
  ext; simp
-/
@[simp] lemma induceHomOfLE_toHom :
    (G.induceHomOfLE h).toHom = induceHom (.id : G ->g G) ((Set.mapsTo_id s).mono_right h) := by
  ext; simp

end induceHomLE

namespace Iso

variable {G G'} (f : G ≃g G')

/--
Definition of `refl` / `refl` 的定义

English:
abbreviation refl
  signature: : G ≃g G
  body: RelIso.refl _

中文:
缩写 refl
  签名: : G ≃g G
  定义体: RelIso.refl _

Depends on / 依赖: RelIso, RelIso.refl
-/
abbrev refl : G ≃g G :=
  RelIso.refl _

/--
Definition of `toEmbedding` / `toEmbedding` 的定义

English:
abbreviation toEmbedding
  signature: : G ↪g G'
  body: f.toRelEmbedding

中文:
缩写 toEmbedding
  签名: : G ↪g G'
  定义体: f.toRelEmbedding

Depends on / 依赖: f.toRelEmbedding, toRelEmbedding
-/
abbrev toEmbedding : G ↪g G' :=
  f.toRelEmbedding

/--
Definition of `toHom` / `toHom` 的定义

English:
abbreviation toHom
  signature: : G ->g G'
  body: f.toEmbedding.toHom

中文:
缩写 toHom
  签名: : G ->g G'
  定义体: f.toEmbedding.toHom

Depends on / 依赖: f.toEmbedding.toHom, toEmbedding
-/
abbrev toHom : G ->g G' :=
  f.toEmbedding.toHom

/--
Definition of `symm` / `symm` 的定义

English:
abbreviation symm
  signature: : G' ≃g G
  body: RelIso.symm f

中文:
缩写 symm
  签名: : G' ≃g G
  定义体: RelIso.symm f

Depends on / 依赖: RelIso, RelIso.symm
-/
abbrev symm : G' ≃g G :=
  RelIso.symm f

/--
theorem `map_adj_iff` / 定理 `map_adj_iff`

English:
theorem map_adj_iff
  given: {v w : V}
  statement: G'.Adj (f v) (f w) ↔ G.Adj v w
  proof: f.map_rel_iff

中文:
定理 map_adj_iff
  条件: {v w : V}
  结论: G'.伴随 (f v) (f w) ↔ G.伴随 v w
  证明: f.map_rel_iff

Depends on / 依赖: f.map_rel_iff, map_rel_iff
-/
theorem map_adj_iff {v w : V} : G'.Adj (f v) (f w) ↔ G.Adj v w :=
  f.map_rel_iff

/--
theorem `map_mem_edgeSet_iff` / 定理 `map_mem_edgeSet_iff`

English:
theorem map_mem_edgeSet_iff
  given: {e : Sym2 V}
  statement: e.map f in G'.edgeSet ↔ e in G.edgeSet
  proof: Sym2.ind (fun _ _ => f.map_adj_iff) e

中文:
定理 map_mem_edgeSet_iff
  条件: {e : Sym2 V}
  结论: e.map f in G'.edgeSet ↔ e in G.edgeSet
  证明: Sym2.ind (fun _ _ => f.map_adj_iff) e

Depends on / 依赖: Sym2.ind, f.map_adj_iff, map_adj_iff
-/
theorem map_mem_edgeSet_iff {e : Sym2 V} : e.map f in G'.edgeSet ↔ e in G.edgeSet :=
  Sym2.ind (fun _ _ => f.map_adj_iff) e

/--
theorem `apply_mem_neighborSet_iff` / 定理 `apply_mem_neighborSet_iff`

English:
theorem apply_mem_neighborSet_iff
  given: {v w : V}
  statement: f w in G'.neighborSet (f v) ↔ w in G.neighborSet v
  proof: map_adj_iff f

中文:
定理 apply_mem_neighborSet_iff
  条件: {v w : V}
  结论: f w in G'.neighborSet (f v) ↔ w in G.neighborSet v
  证明: map_adj_iff f

Depends on / 依赖: map_adj_iff
-/
theorem apply_mem_neighborSet_iff {v w : V} : f w in G'.neighborSet (f v) ↔ w in G.neighborSet v :=
  map_adj_iff f

/--
theorem `image_neighborSet` / 定理 `image_neighborSet`

English:
theorem image_neighborSet
  statement: f '' G.neighborSet v = G'.neighborSet (f v)
  proof: by
  rw [← f.toEmbedding.preimage_neighborSet]
  apply Equiv.image_preimage

@[simp]

中文:
定理 image_neighborSet
  结论: f '' G.neighborSet v = G'.neighborSet (f v)
  证明: by
  rw [← f.toEmbedding.preimage_neighborSet]
  apply Equiv.image_preimage

@[simp]

Depends on / 依赖: Equiv.image_preimage, f.toEmbedding.preimage_neighborSet, image_preimage, preimage_neighborSet, toEmbedding
-/
theorem image_neighborSet : f '' G.neighborSet v = G'.neighborSet (f v) := by
  rw [← f.toEmbedding.preimage_neighborSet]
  apply Equiv.image_preimage

@[simp]
/--
theorem `symm_toHom_comp_toHom` / 定理 `symm_toHom_comp_toHom`

English:
theorem symm_toHom_comp_toHom
  statement: f.symm.toHom.comp f.toHom = Hom.id
  proof: by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.symm_apply_apply, RelHom.id_apply]

@[simp]

中文:
定理 symm_toHom_comp_toHom
  结论: f.symm.toHom.comp f.toHom = 态射.id
  证明: by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.symm_apply_apply, RelHom.id_apply]

@[simp]

Depends on / 依赖: RelEmbedding, RelEmbedding.coe_toRelHom, RelHom, RelHom.comp_apply, RelHom.id_apply, RelIso, RelIso.coe_toRelEmbedding, RelIso.symm_apply_apply, coe_toRelEmbedding, coe_toRelHom, comp_apply, id_apply, symm_apply_apply
-/
theorem symm_toHom_comp_toHom : f.symm.toHom.comp f.toHom = Hom.id := by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.symm_apply_apply, RelHom.id_apply]

@[simp]
/--
theorem `toHom_comp_symm_toHom` / 定理 `toHom_comp_symm_toHom`

English:
theorem toHom_comp_symm_toHom
  statement: f.toHom.comp f.symm.toHom = Hom.id
  proof: by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.apply_symm_apply, RelHom.id_apply]

中文:
定理 toHom_comp_symm_toHom
  结论: f.toHom.comp f.symm.toHom = 态射.id
  证明: by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.apply_symm_apply, RelHom.id_apply]

Depends on / 依赖: RelEmbedding, RelEmbedding.coe_toRelHom, RelHom, RelHom.comp_apply, RelHom.id_apply, RelIso, RelIso.apply_symm_apply, RelIso.coe_toRelEmbedding, apply_symm_apply, coe_toRelEmbedding, coe_toRelHom, comp_apply, id_apply
-/
theorem toHom_comp_symm_toHom : f.toHom.comp f.symm.toHom = Hom.id := by
  ext v
  simp only [RelHom.comp_apply, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding,
    RelIso.apply_symm_apply, RelHom.id_apply]

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps]
/--
Definition of `mapEdgeSet` / `mapEdgeSet` 的定义

English:
definition mapEdgeSet
  signature: : G.edgeSet ≃ G'.edgeSet where
  body: Hom.mapEdgeSet f
  invFun := Hom.mapEdgeSet f.symm
  left_inv := by
    rintro ⟨e, h⟩
    simp only [Hom.mapEdgeSet, RelEmbedding.toRelHom, Sym2.map_map, comp_apply, Subtype.mk.injEq]
    convert! congr_fun Sym2.map_id e
    exact RelIso.symm_apply_apply _ _
  right_inv := by
    rintro ⟨e, h⟩
    s

中文:
定义 mapEdgeSet
  签名: : G.edgeSet ≃ G'.edgeSet where
  定义体: Hom.mapEdgeSet f
  invFun := Hom.mapEdgeSet f.symm
  left_inv := by
    rintro ⟨e, h⟩
    simp only [Hom.mapEdgeSet, RelEmbedding.toRelHom, Sym2.map_map, comp_apply, Subtype.mk.injEq]
    convert! congr_fun Sym2.map_id e
    exact RelIso.symm_apply_apply _ _
  right_inv := by
    rintro ⟨e, h⟩
    s

Depends on / 依赖: Hom.mapEdgeSet, mapEdgeSet
-/
def mapEdgeSet : G.edgeSet ≃ G'.edgeSet where
  toFun := Hom.mapEdgeSet f
  invFun := Hom.mapEdgeSet f.symm
  left_inv := by
    rintro ⟨e, h⟩
    simp only [Hom.mapEdgeSet, RelEmbedding.toRelHom, Sym2.map_map, comp_apply, Subtype.mk.injEq]
    convert! congr_fun Sym2.map_id e
    exact RelIso.symm_apply_apply _ _
  right_inv := by
    rintro ⟨e, h⟩
    simp only [Hom.mapEdgeSet, RelEmbedding.toRelHom, Sym2.map_map, comp_apply, Subtype.mk.injEq]
    convert! congr_fun Sym2.map_id e
    exact RelIso.apply_symm_apply _ _

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps]
/--
Definition of `mapNeighborSet` / `mapNeighborSet` 的定义

English:
definition mapNeighborSet
  signature: (v : V)
  body: ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using f.symm.apply_mem_neighborSet_iff.mpr w.2⟩
  left_inv w := by simp
  right_inv w := by simp

include f in

中文:
定义 mapNeighborSet
  签名: (v : V)
  定义体: ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using f.symm.apply_mem_neighborSet_iff.mpr w.2⟩
  left_inv w := by simp
  right_inv w := by simp

include f in

Depends on / 依赖: apply_mem_neighborSet_iff, f.apply_mem_neighborSet_iff.mpr
-/
def mapNeighborSet (v : V) : G.neighborSet v ≃ G'.neighborSet (f v) where
  toFun w := ⟨f w, f.apply_mem_neighborSet_iff.mpr w.2⟩
  invFun w :=
    ⟨f.symm w, by
      simpa [RelIso.symm_apply_apply] using f.symm.apply_mem_neighborSet_iff.mpr w.2⟩
  left_inv w := by simp
  right_inv w := by simp

include f in
/--
theorem `card_eq` / 定理 `card_eq`

English:
theorem card_eq
  given: [Fintype V] [Fintype W]
  statement: Fintype.card V = Fintype.card W
  proof: by
  rw [← Fintype.ofEquiv_card f.toEquiv]
  convert! rfl

中文:
定理 card_eq
  条件: [有限类型 V] [有限类型 W]
  结论: 有限类型.card V = 有限类型.card W
  证明: by
  rw [← Fintype.ofEquiv_card f.toEquiv]
  convert! rfl

Depends on / 依赖: Fintype, Fintype.ofEquiv_card, convert, f.toEquiv, ofEquiv_card, toEquiv
-/
theorem card_eq [Fintype V] [Fintype W] : Fintype.card V = Fintype.card W := by
  rw [← Fintype.ofEquiv_card f.toEquiv]
  convert! rfl

-- Porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `comap_apply` for now.
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : V ≃ W) (G : SimpleGraph W)
  body: f
  map_rel_iff' := by simp

@[simp]

中文:
定义 comap
  签名: (f : V ≃ W) (G : 简单图 W)
  定义体: f
  map_rel_iff' := by simp

@[simp]
-/
protected def comap (f : V ≃ W) (G : SimpleGraph W) : G.comap f ≃g G where
  __ := f
  map_rel_iff' := by simp

@[simp]
/--
lemma `comap_apply` / 引理 `comap_apply`

English:
lemma comap_apply
  given: (f : V ≃ W) (G : SimpleGraph W) (v : V)
  statement: Iso.comap f G v = f v
  proof: rfl

中文:
引理 comap_apply
  条件: (f : V ≃ W) (G : 简单图 W) (v : V)
  结论: 同构.comap f G v = f v
  证明: rfl
-/
lemma comap_apply (f : V ≃ W) (G : SimpleGraph W) (v : V) : Iso.comap f G v = f v := rfl

-- Porting note: `@[simps]` does not work here anymore since `f` is not a constructor application.
-- `@[simps toEmbedding]` could work, but Floris suggested writing `map_apply` for now.
@[simp]
/--
lemma `comap_symm_apply` / 引理 `comap_symm_apply`

English:
lemma comap_symm_apply
  given: (f : V ≃ W) (G : SimpleGraph W) (w : W)
  proof: rfl

中文:
引理 comap_symm_apply
  条件: (f : V ≃ W) (G : 简单图 W) (w : W)
  证明: rfl
-/
lemma comap_symm_apply (f : V ≃ W) (G : SimpleGraph W) (w : W) :
    (Iso.comap f G).symm w = f.symm w := rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : V ≃ W) (G : SimpleGraph V)
  body: f
  map_rel_iff' := by aesop (add simp map_adj')

@[simp]

中文:
定义 map
  签名: (f : V ≃ W) (G : 简单图 V)
  定义体: f
  map_rel_iff' := by aesop (add simp map_adj')

@[simp]
-/
protected def map (f : V ≃ W) (G : SimpleGraph V) : G ≃g G.map f where
  __ := f
  map_rel_iff' := by aesop (add simp map_adj')

@[simp]
/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  given: (f : V ≃ W) (G : SimpleGraph V) (v : V)
  statement: Iso.map f G v = f v
  proof: rfl

@[simp]

中文:
引理 map_apply
  条件: (f : V ≃ W) (G : 简单图 V) (v : V)
  结论: 同构.map f G v = f v
  证明: rfl

@[simp]
-/
lemma map_apply (f : V ≃ W) (G : SimpleGraph V) (v : V) : Iso.map f G v = f v := rfl

@[simp]
/--
lemma `map_symm_apply` / 引理 `map_symm_apply`

English:
lemma map_symm_apply
  given: (f : V ≃ W) (G : SimpleGraph V) (w : W)
  proof: rfl

中文:
引理 map_symm_apply
  条件: (f : V ≃ W) (G : 简单图 V) (w : W)
  证明: rfl
-/
lemma map_symm_apply (f : V ≃ W) (G : SimpleGraph V) (w : W) :
    (Iso.map f G).symm w = f.symm w := rfl

/--
Definition of `completeGraph` / `completeGraph` 的定义

English:
definition completeGraph
  signature: {α β : Type*} (f : α ≃ β)
  body: f
  map_rel_iff' := by simp

中文:
定义 completeGraph
  签名: {α β : 类型} (f : α ≃ β)
  定义体: f
  map_rel_iff' := by simp
-/
protected def completeGraph {α β : Type*} (f : α ≃ β) : completeGraph α ≃g completeGraph β where
  __ := f
  map_rel_iff' := by simp

/--
theorem `toEmbedding_completeGraph` / 定理 `toEmbedding_completeGraph`

English:
theorem toEmbedding_completeGraph
  given: {α β : Type*} (f : α ≃ β)
  proof: rfl

中文:
定理 toEmbedding_completeGraph
  条件: {α β : 类型} (f : α ≃ β)
  证明: rfl
-/
theorem toEmbedding_completeGraph {α β : Type*} (f : α ≃ β) :
    (Iso.completeGraph f).toEmbedding = Embedding.completeGraph f.toEmbedding :=
  rfl

variable {G'' : SimpleGraph X} {G''' : SimpleGraph Y}

/--
Definition of `homCongr` / `homCongr` 的定义

English:
abbreviation homCongr
  signature: (f' : G'' ≃g G''')
  body: RelIso.relHomCongr f f'

中文:
缩写 homCongr
  签名: (f' : G'' ≃g G''')
  定义体: RelIso.relHomCongr f f'

Depends on / 依赖: RelIso, RelIso.relHomCongr, relHomCongr
-/
abbrev homCongr (f' : G'' ≃g G''') : G ->g G'' ≃ G' ->g G''' := RelIso.relHomCongr f f'

/--
Definition of `comp` / `comp` 的定义

English:
abbreviation comp
  signature: (f' : G' ≃g G'') (f : G ≃g G')
  body: f.trans f'

@[simp]

中文:
缩写 comp
  签名: (f' : G' ≃g G'') (f : G ≃g G')
  定义体: f.trans f'

@[simp]

Depends on / 依赖: f.trans
-/
abbrev comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' :=
  f.trans f'

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f' : G' ≃g G'') (f : G ≃g G')
  statement: ⇑(f'.comp f) = f' ∘ f
  proof: rfl

中文:
定理 coe_comp
  条件: (f' : G' ≃g G'') (f : G ≃g G')
  结论: ⇑(f'.comp f) = f' ∘ f
  证明: rfl
-/
theorem coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : G'' ≃g G''') (g : G' ≃g G'') (h : G ≃g G')
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : G'' ≃g G''') (g : G' ≃g G'') (h : G ≃g G')
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : G'' ≃g G''') (g : G' ≃g G'') (h : G ≃g G') :
    f.comp (g.comp h) = (f.comp g).comp h := rfl

@[simp]
/--
theorem `comp_refl` / 定理 `comp_refl`

English:
theorem comp_refl
  given: (f : G ≃g G')
  statement: f.comp .refl = f
  proof: rfl

@[simp]

中文:
定理 comp_refl
  条件: (f : G ≃g G')
  结论: f.comp .refl = f
  证明: rfl

@[simp]
-/
theorem comp_refl (f : G ≃g G') : f.comp .refl = f := rfl

@[simp]
/--
theorem `refl_comp` / 定理 `refl_comp`

English:
theorem refl_comp
  given: (f : G ≃g G')
  statement: .comp .refl f = f
  proof: rfl

中文:
定理 refl_comp
  条件: (f : G ≃g G')
  结论: .comp .refl f = f
  证明: rfl
-/
theorem refl_comp (f : G ≃g G') : .comp .refl f = f := rfl

section induce

variable {s : Set V} {t : Set W} {r : Set X}
         (φ : G ≃g G') (φst : Set.BijOn φ s t) (ψ : G' ≃g G'') (ψtr : Set.BijOn ψ t r)

/--
Definition of `induce` / `induce` 的定义

English:
definition induce
  signature: : G.induce s ≃g G'.induce t where
  body: ⟨φ v.val, φst.mapsTo v.property⟩
  invFun w := ⟨φ.symm w.val, (φ.bijOn_symm.mpr φst).mapsTo w.property⟩
  left_inv v := by simp
  right_inv w := by simp
  map_rel_iff' := by simp [map_adj_iff φ]

@[simp, norm_cast]

中文:
定义 induce
  签名: : G.induce s ≃g G'.induce t where
  定义体: ⟨φ v.val, φst.mapsTo v.property⟩
  invFun w := ⟨φ.symm w.val, (φ.bijOn_symm.mpr φst).mapsTo w.property⟩
  left_inv v := by simp
  right_inv w := by simp
  map_rel_iff' := by simp [map_adj_iff φ]

@[simp, norm_cast]
-/
protected def induce : G.induce s ≃g G'.induce t where
  toFun v := ⟨φ v.val, φst.mapsTo v.property⟩
  invFun w := ⟨φ.symm w.val, (φ.bijOn_symm.mpr φst).mapsTo w.property⟩
  left_inv v := by simp
  right_inv w := by simp
  map_rel_iff' := by simp [map_adj_iff φ]

@[simp, norm_cast]
/--
lemma `coe_induce` / 引理 `coe_induce`

English:
lemma coe_induce
  proof: rfl

@[simp]

中文:
引理 coe_induce
  证明: rfl

@[simp]
-/
protected lemma coe_induce :
    ⇑(φ.induce φst) = φst.mapsTo.restrict φ s t := rfl

@[simp]
/--
lemma `induce_refl` / 引理 `induce_refl`

English:
lemma induce_refl
  given: (G : SimpleGraph V) (s : Set V)
  proof: rfl

@[simp]

中文:
引理 induce_refl
  条件: (G : 简单图 V) (s : 集合 V)
  证明: rfl

@[simp]
-/
protected lemma induce_refl (G : SimpleGraph V) (s : Set V) :
    (.refl : G ≃g G).induce (Set.bijOn_id s) = .refl := rfl

@[simp]
/--
lemma `induce_comp_induce` / 引理 `induce_comp_induce`

English:
lemma induce_comp_induce
  proof: by
  rfl

中文:
引理 induce_comp_induce
  证明: by
  rfl
-/
protected lemma induce_comp_induce :
    (ψ.induce ψtr).comp (φ.induce φst) = (ψ.comp φ).induce (ψtr.comp φst) := by
  rfl

end induce

end Iso

/--
theorem `neighborSet_comap` / 定理 `neighborSet_comap`

English:
theorem neighborSet_comap
  given: (f : V -> W) (v : V)
  proof: rfl

中文:
定理 neighborSet_comap
  条件: (f : V -> W) (v : V)
  证明: rfl
-/
theorem neighborSet_comap (f : V -> W) (v : V) :
    (G'.comap f).neighborSet v = f ⁻¹' G'.neighborSet (f v) :=
  rfl

/--
theorem `neighborSet_induce` / 定理 `neighborSet_induce`

English:
theorem neighborSet_induce
  given: (s : Set V) (v : s)
  proof: G.neighborSet_comap _ v

中文:
定理 neighborSet_induce
  条件: (s : 集合 V) (v : s)
  证明: G.neighborSet_comap _ v

Depends on / 依赖: G.neighborSet_comap, neighborSet_comap
-/
theorem neighborSet_induce (s : Set V) (v : s) :
    (G.induce s).neighborSet v = (↑) ⁻¹' G.neighborSet v :=
  G.neighborSet_comap _ v

/--
theorem `neighborSet_map_equiv` / 定理 `neighborSet_map_equiv`

English:
theorem neighborSet_map_equiv
  given: (e : V ≃ W) (w : W)
  proof: .symm .symm.toEmbedding.preimage_neighborSet w Iso.map e G

中文:
定理 neighborSet_map_equiv
  条件: (e : V ≃ W) (w : W)
  证明: .symm .symm.toEmbedding.preimage_neighborSet w Iso.map e G

Depends on / 依赖: Iso.map, preimage_neighborSet, symm.toEmbedding.preimage_neighborSet, toEmbedding
-/
theorem neighborSet_map_equiv (e : V ≃ W) (w : W) :
    (G.map e).neighborSet w = e.symm ⁻¹' G.neighborSet (e.symm w) :=
.symm .symm.toEmbedding.preimage_neighborSet w Iso.map e G

set_option backward.isDefEq.respectTransparency false in
/-- The graph induced on `Set.univ` is isomorphic to the original graph. -/
@[simps!]
/--
Definition of `induceUnivIso` / `induceUnivIso` 的定义

English:
definition induceUnivIso
  signature: (G : SimpleGraph V)
  body: Equiv.Set.univ V
  map_rel_iff' := by simp only [Equiv.Set.univ, Equiv.coe_fn_mk, comap_adj, Embedding.coe_subtype,
                                implies_true]

中文:
定义 induceUnivIso
  签名: (G : 简单图 V)
  定义体: Equiv.Set.univ V
  map_rel_iff' := by simp only [Equiv.Set.univ, Equiv.coe_fn_mk, comap_adj, Embedding.coe_subtype,
                                implies_true]

Depends on / 依赖: Equiv.Set.univ
-/
def induceUnivIso (G : SimpleGraph V) : G.induce Set.univ ≃g G where
  toEquiv := Equiv.Set.univ V
  map_rel_iff' := by simp only [Equiv.Set.univ, Equiv.coe_fn_mk, comap_adj, Embedding.coe_subtype,
                                implies_true]

/-- The isomorphism between `completeBipartiteGraph V₁ W₁` and
`completeBipartiteGraph V₂ W₂` where `V₁ ≃ V₂` and `W₁ ≃ W₂`. -/
@[simps!]
/--
Definition of `completeBipartiteGraphCongr` / `completeBipartiteGraphCongr` 的定义

English:
definition completeBipartiteGraphCongr
  signature: {V₁ V₂ W₁ W₂ : Type*} (hV : V₁ ≃ V₂) (hW : W₁ ≃ W₂)
  body: hV.sumCongr hW
  map_rel_iff' := by simp

中文:
定义 completeBipartiteGraphCongr
  签名: {V₁ V₂ W₁ W₂ : 类型} (hV : V₁ ≃ V₂) (hW : W₁ ≃ W₂)
  定义体: hV.sumCongr hW
  map_rel_iff' := by simp

Depends on / 依赖: hV.sumCongr, sumCongr
-/
def completeBipartiteGraphCongr {V₁ V₂ W₁ W₂ : Type*} (hV : V₁ ≃ V₂) (hW : W₁ ≃ W₂) :
    completeBipartiteGraph V₁ W₁ ≃g completeBipartiteGraph V₂ W₂ where
  __ := hV.sumCongr hW
  map_rel_iff' := by simp

section Finite

variable [Fintype V] {n : Nat}

/--
Definition of `overFin` / `overFin` 的定义

English:
definition overFin
  signature: (hc : Fintype.card V = n)
  body: G.comap (Fintype.equivFinOfCardEq hc).symm

中文:
定义 overFin
  签名: (hc : 有限类型.card V = n)
  定义体: G.comap (Fintype.equivFinOfCardEq hc).symm

Depends on / 依赖: Fintype, Fintype.equivFinOfCardEq, G.comap, equivFinOfCardEq
-/
noncomputable def overFin (hc : Fintype.card V = n) : SimpleGraph (Fin n) :=
  G.comap (Fintype.equivFinOfCardEq hc).symm

/--
Definition of `overFinIso` / `overFinIso` 的定义

English:
definition overFinIso
  signature: (hc : Fintype.card V = n)
  body: .symm .comap ..

中文:
定义 overFinIso
  签名: (hc : 有限类型.card V = n)
  定义体: .symm .comap ..
-/
noncomputable def overFinIso (hc : Fintype.card V = n) : G ≃g G.overFin hc :=
.symm .comap ..

end Finite

end SimpleGraph
