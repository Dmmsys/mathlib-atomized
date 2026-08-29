/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Snir Broshi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# LineGraph

## Main definitions

* `SimpleGraph.lineGraph` is the line graph of a simple graph `G`, with vertices as the edges of `G`
  and two vertices of the line graph adjacent if the corresponding edges share a vertex in `G`.

## Tags

line graph
-/

@[expose] public section

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}

variable (G) in
/--
Definition of `lineGraph` / `lineGraph` 的定义

English:
definition lineGraph
  signature: : SimpleGraph G.edgeSet where
  body: e₁ != e₂ ∧ (e₁ inter e₂ : Set V).Nonempty
  symm.symm e₁ e₂ hadj := by rwa [ne_comm, Set.inter_comm]

中文:
定义 lineGraph
  签名: : 简单图 G.edgeSet where
  定义体: e₁ != e₂ ∧ (e₁ inter e₂ : Set V).Nonempty
  symm.symm e₁ e₂ hadj := by rwa [ne_comm, Set.inter_comm]

Depends on / 依赖: Nonempty
-/
def lineGraph : SimpleGraph G.edgeSet where
  Adj e₁ e₂ := e₁ != e₂ ∧ (e₁ inter e₂ : Set V).Nonempty
  symm.symm e₁ e₂ hadj := by rwa [ne_comm, Set.inter_comm]

/--
lemma `lineGraph_adj_iff_exists` / 引理 `lineGraph_adj_iff_exists`

English:
lemma lineGraph_adj_iff_exists
  given: {e₁ e₂ : G.edgeSet}
  proof: by
  simp [Set.Nonempty, lineGraph]

中文:
引理 lineGraph_adj_iff_存在
  条件: {e₁ e₂ : G.edgeSet}
  证明: by
  simp [Set.Nonempty, lineGraph]

Depends on / 依赖: Nonempty, Set.Nonempty, lineGraph
-/
lemma lineGraph_adj_iff_exists {e₁ e₂ : G.edgeSet} :
    (G.lineGraph).Adj e₁ e₂ ↔ e₁ != e₂ ∧ exists v, v in (e₁ : Sym2 V) ∧ v in (e₂ : Sym2 V) := by
  simp [Set.Nonempty, lineGraph]

/--
lemma `lineGraph_bot` / 引理 `lineGraph_bot`

English:
lemma lineGraph_bot
  statement: (⊥ : SimpleGraph V).lineGraph = ⊥
  proof: by aesop (add simp lineGraph)

中文:
引理 lineGraph_bot
  结论: (⊥ : 简单图 V).lineGraph = ⊥
  证明: by aesop (add simp lineGraph)
-/
@[simp] lemma lineGraph_bot : (⊥ : SimpleGraph V).lineGraph = ⊥ := by aesop (add simp lineGraph)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Copy.toLineGraphEmbedding` / `Copy.toLineGraphEmbedding` 的定义

English:
definition Copy.toLineGraphEmbedding
  signature: (f : Copy G G')
  body: ⟨e.val.map f, by rcases e with ⟨⟨⟩, h⟩; exact f.toHom.map_adj h⟩
inj' _ _ h := SetCoe.ext Sym2.map.injective f.injective Subtype.mk.inj h
  map_rel_iff' := by
    simp only [lineGraph, Function.Embedding.coeFn_mk, Sym2.coe_map, ne_eq]
refine .and ?_ Set.image_inter f.injective ▸ Set.image_nonempty
 

中文:
定义 余py.toLineGraphEmbedding
  签名: (f : 余py G G')
  定义体: ⟨e.val.map f, by rcases e with ⟨⟨⟩, h⟩; exact f.toHom.map_adj h⟩
inj' _ _ h := SetCoe.ext Sym2.map.injective f.injective Subtype.mk.inj h
  map_rel_iff' := by
    simp only [lineGraph, Function.Embedding.coeFn_mk, Sym2.coe_map, ne_eq]
refine .and ?_ Set.image_inter f.injective ▸ Set.image_nonempty
 

Depends on / 依赖: e.val.map, f.toHom.map_adj, map_adj
-/
def Copy.toLineGraphEmbedding (f : Copy G G') : G.lineGraph ↪g G'.lineGraph where
  toFun e := ⟨e.val.map f, by rcases e with ⟨⟨⟩, h⟩; exact f.toHom.map_adj h⟩
inj' _ _ h := SetCoe.ext Sym2.map.injective f.injective Subtype.mk.inj h
  map_rel_iff' := by
    simp only [lineGraph, Function.Embedding.coeFn_mk, Sym2.coe_map, ne_eq]
refine .and ?_ Set.image_inter f.injective ▸ Set.image_nonempty
    rw [Subtype.mk.injEq]; rw [Subtype.mk.injEq]
.eq_iff.not exact Sym2.map.injective f.injective

/--
theorem `IsIndContained.lineGraph` / 定理 `IsIndContained.lineGraph`

English:
theorem IsIndContained.lineGraph
  given: (h : G ⊴ G')
  statement: G.lineGraph ⊴ G'.lineGraph
  proof: ⟨h.some.toCopy.toLineGraphEmbedding⟩

中文:
定理 IsIndContained.lineGraph
  条件: (h : G ⊴ G')
  结论: G.lineGraph ⊴ G'.lineGraph
  证明: ⟨h.some.toCopy.toLineGraphEmbedding⟩

Depends on / 依赖: h.some.toCopy.toLineGraphEmbedding, toCopy, toLineGraphEmbedding
-/
theorem IsIndContained.lineGraph (h : G ⊴ G') : G.lineGraph ⊴ G'.lineGraph :=
  ⟨h.some.toCopy.toLineGraphEmbedding⟩

/--
theorem `IsContained.isIndContained_lineGraph` / 定理 `IsContained.isIndContained_lineGraph`

English:
theorem IsContained.isIndContained_lineGraph
  given: (h : G ⊑ G')
  statement: G.lineGraph ⊴ G'.lineGraph
  proof: ⟨h.some.toLineGraphEmbedding⟩

中文:
定理 IsContained.isIndContained_lineGraph
  条件: (h : G ⊑ G')
  结论: G.lineGraph ⊴ G'.lineGraph
  证明: ⟨h.some.toLineGraphEmbedding⟩

Depends on / 依赖: h.some.toLineGraphEmbedding, toLineGraphEmbedding
-/
theorem IsContained.isIndContained_lineGraph (h : G ⊑ G') : G.lineGraph ⊴ G'.lineGraph :=
  ⟨h.some.toLineGraphEmbedding⟩

/--
Definition of `Copy.lineGraph` / `Copy.lineGraph` 的定义

English:
definition Copy.lineGraph
  signature: (f : Copy G G')
  body: f.toLineGraphEmbedding.toCopy

中文:
定义 余py.lineGraph
  签名: (f : 余py G G')
  定义体: f.toLineGraphEmbedding.toCopy

Depends on / 依赖: f.toLineGraphEmbedding.toCopy, toCopy, toLineGraphEmbedding
-/
def Copy.lineGraph (f : Copy G G') : Copy G.lineGraph G'.lineGraph :=
  f.toLineGraphEmbedding.toCopy

/--
theorem `IsContained.lineGraph` / 定理 `IsContained.lineGraph`

English:
theorem IsContained.lineGraph
  given: (h : G ⊑ G')
  statement: G.lineGraph ⊑ G'.lineGraph
  proof: ⟨h.some.lineGraph⟩

中文:
定理 IsContained.lineGraph
  条件: (h : G ⊑ G')
  结论: G.lineGraph ⊑ G'.lineGraph
  证明: ⟨h.some.lineGraph⟩

Depends on / 依赖: h.some.lineGraph, lineGraph
-/
theorem IsContained.lineGraph (h : G ⊑ G') : G.lineGraph ⊑ G'.lineGraph :=
  ⟨h.some.lineGraph⟩

/--
Definition of `Iso.lineGraph` / `Iso.lineGraph` 的定义

English:
definition Iso.lineGraph
  signature: (f : G ≃g G')
  body: f.toCopy.lineGraph
  invFun := f.symm.toCopy.lineGraph
  left_inv _ := by simp [Copy.lineGraph, Copy.toLineGraphEmbedding, Sym2.map_map]
  right_inv _ := by simp [Copy.lineGraph, Copy.toLineGraphEmbedding, Sym2.map_map]
.map_rel_iff map_rel_iff' := Copy.toLineGraphEmbedding f.toCopy

中文:
定义 同构.lineGraph
  签名: (f : G ≃g G')
  定义体: f.toCopy.lineGraph
  invFun := f.symm.toCopy.lineGraph
  left_inv _ := by simp [Copy.lineGraph, Copy.toLineGraphEmbedding, Sym2.map_map]
  right_inv _ := by simp [Copy.lineGraph, Copy.toLineGraphEmbedding, Sym2.map_map]
.map_rel_iff map_rel_iff' := Copy.toLineGraphEmbedding f.toCopy

Depends on / 依赖: f.toCopy.lineGraph, lineGraph, toCopy
-/
def Iso.lineGraph (f : G ≃g G') : G.lineGraph ≃g G'.lineGraph where
  toFun := f.toCopy.lineGraph
  invFun := f.symm.toCopy.lineGraph
  left_inv _ := by simp [Copy.lineGraph, Copy.toLineGraphEmbedding, Sym2.map_map]
  right_inv _ := by simp [Copy.lineGraph, Copy.toLineGraphEmbedding, Sym2.map_map]
.map_rel_iff map_rel_iff' := Copy.toLineGraphEmbedding f.toCopy

open Function.Embedding in
/--
theorem `map_lineGraph_le_of_le` / 定理 `map_lineGraph_le_of_le`

English:
theorem map_lineGraph_le_of_le
  given: {G' : SimpleGraph V} (h : G <= G')
  proof: by
  rintro _ _ ⟨hne', ⟨⟨⟩, h₁⟩, ⟨⟨⟩, h₂⟩, ⟨hne, hinter⟩, rfl, rfl⟩
  exact ⟨hne', ⟨⟨_, h h₁⟩, ⟨_, h h₂⟩, ⟨(hne <| Subtype.ext <| Subtype.mk.inj ·), hinter⟩, rfl, rfl⟩⟩

@[deprecated (since := "2026-03-26")] alias IsSubgraph.lineGraph := map_lineGraph_le_of_le

中文:
定理 map_lineGraph_le_of_le
  条件: {G' : 简单图 V} (h : G <= G')
  证明: by
  rintro _ _ ⟨hne', ⟨⟨⟩, h₁⟩, ⟨⟨⟩, h₂⟩, ⟨hne, hinter⟩, rfl, rfl⟩
  exact ⟨hne', ⟨⟨_, h h₁⟩, ⟨_, h h₂⟩, ⟨(hne <| Subtype.ext <| Subtype.mk.inj ·), hinter⟩, rfl, rfl⟩⟩

@[deprecated (since := "2026-03-26")] alias IsSubgraph.lineGraph := map_lineGraph_le_of_le

Depends on / 依赖: Subtype, Subtype.ext, Subtype.mk.inj, hinter
-/
theorem map_lineGraph_le_of_le {G' : SimpleGraph V} (h : G <= G') :
    G.lineGraph.map (subtype _) <= G'.lineGraph.map (subtype _) := by
  rintro _ _ ⟨hne', ⟨⟨⟩, h₁⟩, ⟨⟨⟩, h₂⟩, ⟨hne, hinter⟩, rfl, rfl⟩
  exact ⟨hne', ⟨⟨_, h h₁⟩, ⟨_, h h₂⟩, ⟨(hne <| Subtype.ext <| Subtype.mk.inj ·), hinter⟩, rfl, rfl⟩⟩

@[deprecated (since := "2026-03-26")] alias IsSubgraph.lineGraph := map_lineGraph_le_of_le

end SimpleGraph
