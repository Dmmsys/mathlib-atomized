/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Complete Multipartite Graphs

A graph is complete multipartite iff non-adjacency is transitive.

## Main declarations

* `SimpleGraph.IsCompleteMultipartite`: predicate for a graph to be complete multipartite.

* `SimpleGraph.IsCompleteMultipartite.setoid`: the `Setoid` given by non-adjacency.

* `SimpleGraph.IsCompleteMultipartite.iso`: the graph isomorphism from a graph that
  `IsCompleteMultipartite` to the corresponding `completeMultipartiteGraph`.

* `SimpleGraph.IsPathGraph3Compl`: predicate for three vertices to witness the
  non-complete-multipartiteness of a graph `G`. (The name refers to the fact that the three
  vertices form the complement of `pathGraph 3`.)

* See also: `Mathlib/Combinatorics/SimpleGraph/FiveWheelLike.lean`.
  The lemma `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree` states that a maximally
  `r + 1`-cliquefree graph is `r`-colorable iff it is complete multipartite.

* `SimpleGraph.completeEquipartiteGraph`: the **complete equipartite graph** in parts of *equal*
  size such that two vertices are adjacent if and only if they are in different parts.

* `SimpleGraph.CompleteEquipartiteSubgraph G r t` is a complete equipartite subgraph, that is,
  `r` subsets of vertices each of size `t` such that the vertices in distinct subsets are
  adjacent.

## Implementation Notes

The definition of `completeEquipartiteGraph` is similar to `completeMultipartiteGraph`
except that `Sigma.fst` is replaced by `Prod.fst` in the definition. The difference is that the
former vertices are a product type whereas the latter vertices are a *dependent* product type.

While `completeEquipartiteGraph r t` could have been defined as the specialisation
`completeMultipartiteGraph (const (Fin r) (Fin t))` (or `turanGraph (r * t) r`), it is convenient
to instead have a *non-dependent* *product* type for the vertices.

See `completeEquipartiteGraph.completeMultipartiteGraph`, `completeEquipartiteGraph.turanGraph`
for the isomorphisms between a `completeEquipartiteGraph` and a corresponding
`completeMultipartiteGraph`, `turanGraph`.
-/

@[expose] public section

open Finset Fintype Function

universe u
namespace SimpleGraph
variable {α : Type u} {G : SimpleGraph α} {s : Set α}

/--
Definition of `IsCompleteMultipartite` / `IsCompleteMultipartite` 的定义

English:
definition IsCompleteMultipartite
  signature: (G : SimpleGraph α)
  body: IsTrans α (¬ G.Adj · ·)

中文:
定义 IsCompleteMultipartite
  签名: (G : 简单图 α)
  定义体: IsTrans α (¬ G.Adj · ·)

Depends on / 依赖: G.Adj, IsTrans
-/
def IsCompleteMultipartite (G : SimpleGraph α) : Prop := IsTrans α (¬ G.Adj · ·)

/--
theorem `bot_isCompleteMultipartite` / 定理 `bot_isCompleteMultipartite`

English:
theorem bot_isCompleteMultipartite
  statement: (⊥ : SimpleGraph α).IsCompleteMultipartite
  proof: ⟨by simp⟩

中文:
定理 bot_isCompleteMultipartite
  结论: (⊥ : 简单图 α).IsCompleteMultipartite
  证明: ⟨by simp⟩
-/
theorem bot_isCompleteMultipartite : (⊥ : SimpleGraph α).IsCompleteMultipartite :=
  ⟨by simp⟩

/--
lemma `IsCompleteMultipartite.induce` / 引理 `IsCompleteMultipartite.induce`

English:
lemma IsCompleteMultipartite.induce
  given: (hG : G.IsCompleteMultipartite)
  proof: hG.trans _ _ _

中文:
引理 IsCompleteMultipartite.induce
  条件: (hG : G.IsCompleteMultipartite)
  证明: hG.trans _ _ _
-/
protected lemma IsCompleteMultipartite.induce (hG : G.IsCompleteMultipartite) :
    (G.induce s).IsCompleteMultipartite where trans _u _v _w := hG.trans _ _ _

/-- The setoid given by non-adjacency -/
@[instance_reducible]
/--
Definition of `IsCompleteMultipartite.setoid` / `IsCompleteMultipartite.setoid` 的定义

English:
definition IsCompleteMultipartite.setoid
  signature: (h : G.IsCompleteMultipartite)
  body: ⟨(¬ G.Adj · ·), ⟨G.loopless.irrefl, fun h' => by rwa [adj_comm] at h', h.trans _ _ _⟩⟩

中文:
定义 IsCompleteMultipartite.setoid
  签名: (h : G.IsCompleteMultipartite)
  定义体: ⟨(¬ G.Adj · ·), ⟨G.loopless.irrefl, fun h' => by rwa [adj_comm] at h', h.trans _ _ _⟩⟩

Depends on / 依赖: G.Adj, G.loopless.irrefl, adj_comm, h.trans, irrefl, loopless
-/
def IsCompleteMultipartite.setoid (h : G.IsCompleteMultipartite) : Setoid α :=
    ⟨(¬ G.Adj · ·), ⟨G.loopless.irrefl, fun h' => by rwa [adj_comm] at h', h.trans _ _ _⟩⟩

/--
lemma `completeMultipartiteGraph.isCompleteMultipartite` / 引理 `completeMultipartiteGraph.isCompleteMultipartite`

English:
lemma completeMultipartiteGraph.isCompleteMultipartite
  given: {ι : Type*} (V : ι -> Type*)
  proof: ⟨by simp_all⟩

中文:
引理 completeMultipartiteGraph.isCompleteMultipartite
  条件: {ι : 类型} (V : ι -> 类型)
  证明: ⟨by simp_all⟩
-/
lemma completeMultipartiteGraph.isCompleteMultipartite {ι : Type*} (V : ι -> Type*) :
    (completeMultipartiteGraph V).IsCompleteMultipartite :=
  ⟨by simp_all⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `IsCompleteMultipartite.iso` / `IsCompleteMultipartite.iso` 的定义

English:
definition IsCompleteMultipartite.iso
  signature: (h : G.IsCompleteMultipartite)
  body: fun x => ⟨_, ⟨_, Quotient.mk_out x⟩⟩
  invFun := fun ⟨_, x⟩ => x.1
  right_inv := fun ⟨_, x⟩ => Sigma.subtype_ext (Quotient.mk_eq_iff_out.2 <| h.setoid.symm x.2) rfl
  map_rel_iff' := by
    simp_rw [Equiv.coe_fn_mk, comap_adj, top_adj, ne_eq, Quotient.eq]
    intros
    change ¬¬ G.Adj _ _ ↔ _
    rw [not_not]

中文:
定义 IsCompleteMultipartite.iso
  签名: (h : G.IsCompleteMultipartite)
  定义体: fun x => ⟨_, ⟨_, Quotient.mk_out x⟩⟩
  invFun := fun ⟨_, x⟩ => x.1
  right_inv := fun ⟨_, x⟩ => Sigma.subtype_ext (Quotient.mk_eq_iff_out.2 <| h.setoid.symm x.2) rfl
  map_rel_iff' := by
    simp_rw [Equiv.coe_fn_mk, comap_adj, top_adj, ne_eq, Quotient.eq]
    intros
    change ¬¬ G.Adj _ _ ↔ _
    rw [not_not]

Depends on / 依赖: Quotient, Quotient.mk_out, mk_out
-/
def IsCompleteMultipartite.iso (h : G.IsCompleteMultipartite) :
    G ≃g completeMultipartiteGraph (fun (c : Quotient h.setoid) => {x // h.setoid.r c.out x}) where
  toFun := fun x => ⟨_, ⟨_, Quotient.mk_out x⟩⟩
  invFun := fun ⟨_, x⟩ => x.1
  right_inv := fun ⟨_, x⟩ => Sigma.subtype_ext (Quotient.mk_eq_iff_out.2 <| h.setoid.symm x.2) rfl
  map_rel_iff' := by
    simp_rw [Equiv.coe_fn_mk, comap_adj, top_adj, ne_eq, Quotient.eq]
    intros
    change ¬¬ G.Adj _ _ ↔ _
    rw [not_not]

/--
lemma `isCompleteMultipartite_iff` / 引理 `isCompleteMultipartite_iff`

English:
lemma isCompleteMultipartite_iff
  statement: G.IsCompleteMultipartite ↔ exists (ι : Type u) (V : ι -> Type u)
  proof: by
  constructor <;> intro h
  · exact ⟨_, _, fun _ => ⟨_, h.setoid.refl _⟩, ⟨h.iso⟩⟩
  · obtain ⟨_, _, _, ⟨e⟩⟩ := h
    refine ⟨fun _ _ _ h1 h2 => ?_⟩
    rw [← e.map_rel_iff] at *
.trans _ _ _ h1 h2 exact completeMultipartiteGraph.isCompleteMultipartite _

中文:
引理 isCompleteMultipartite_iff
  结论: G.IsCompleteMultipartite ↔ 存在 (ι : 类型u) (V : ι -> 类型u)
  证明: by
  constructor <;> intro h
  · exact ⟨_, _, fun _ => ⟨_, h.setoid.refl _⟩, ⟨h.iso⟩⟩
  · obtain ⟨_, _, _, ⟨e⟩⟩ := h
    refine ⟨fun _ _ _ h1 h2 => ?_⟩
    rw [← e.map_rel_iff] at *
.trans _ _ _ h1 h2 exact completeMultipartiteGraph.isCompleteMultipartite _

Depends on / 依赖: completeMultipartiteGraph, completeMultipartiteGraph.isCompleteMultipartite, e.map_rel_iff, h.iso, h.setoid.refl, isCompleteMultipartite, map_rel_iff, setoid
-/
lemma isCompleteMultipartite_iff : G.IsCompleteMultipartite ↔ exists (ι : Type u) (V : ι -> Type u)
    (_ : forall i, Nonempty (V i)), Nonempty (G ≃g completeMultipartiteGraph V) := by
  constructor <;> intro h
  · exact ⟨_, _, fun _ => ⟨_, h.setoid.refl _⟩, ⟨h.iso⟩⟩
  · obtain ⟨_, _, _, ⟨e⟩⟩ := h
    refine ⟨fun _ _ _ h1 h2 => ?_⟩
    rw [← e.map_rel_iff] at *
.trans _ _ _ h1 h2 exact completeMultipartiteGraph.isCompleteMultipartite _

/--
lemma `IsCompleteMultipartite.colorable_of_cliqueFree` / 引理 `IsCompleteMultipartite.colorable_of_cliqueFree`

English:
lemma IsCompleteMultipartite.colorable_of_cliqueFree
  statement: {n : Nat} (h : G.IsCompleteMultipartite)
  proof: (completeMultipartiteGraph.colorable_of_cliqueFree _ (fun _ => ⟨_, h.setoid.refl _⟩) <|
    hc.comap h.iso.symm.isContained).of_hom h.iso

中文:
引理 IsCompleteMultipartite.colorable_of_cliqueFree
  结论: {n : 自然数} (h : G.IsCompleteMultipartite)
  证明: (completeMultipartiteGraph.colorable_of_cliqueFree _ (fun _ => ⟨_, h.setoid.refl _⟩) <|
    hc.comap h.iso.symm.isContained).of_hom h.iso

Depends on / 依赖: colorable_of_cliqueFree, completeMultipartiteGraph, completeMultipartiteGraph.colorable_of_cliqueFree, h.iso, h.iso.symm.isContained, h.setoid.refl, hc.comap, isContained, of_hom, setoid
-/
lemma IsCompleteMultipartite.colorable_of_cliqueFree {n : Nat} (h : G.IsCompleteMultipartite)
    (hc : G.CliqueFree n) : G.Colorable (n - 1) :=
  (completeMultipartiteGraph.colorable_of_cliqueFree _ (fun _ => ⟨_, h.setoid.refl _⟩) <|
    hc.comap h.iso.symm.isContained).of_hom h.iso

variable (G) in
/--
Definition of `IsPathGraph3Compl` / `IsPathGraph3Compl` 的定义

English:
structure IsPathGraph3Compl
  parameters: (v w₁ w₂ : α)
  axioms and operations (3):
    - adj : G.Adj w₁ w₂
    - not_adj_fst : ¬ G.Adj v w₁
    - not_adj_snd : ¬ G.Adj v w₂

中文:
结构 是PathGraph3Compl
  参数: (v w₁ w₂ : α)
  公理与运算 (3 个):
    - adj : G.伴随 w₁ w₂
    - not_adj_fst : ¬ G.伴随 v w₁
    - not_adj_snd : ¬ G.伴随 v w₂
-/
structure IsPathGraph3Compl (v w₁ w₂ : α) : Prop where
  adj : G.Adj w₁ w₂
  not_adj_fst : ¬ G.Adj v w₁
  not_adj_snd : ¬ G.Adj v w₂

namespace IsPathGraph3Compl

variable {v w₁ w₂ : α}

@[grind ->]
/--
lemma `ne_fst` / 引理 `ne_fst`

English:
lemma ne_fst
  given: (h2 : G.IsPathGraph3Compl v w₁ w₂)
  statement: v != w₁
  proof: fun h => h2.not_adj_snd (h.symm ▸ h2.adj)

@[grind ->]

中文:
引理 ne_fst
  条件: (h2 : G.是PathGraph3Compl v w₁ w₂)
  结论: v != w₁
  证明: fun h => h2.not_adj_snd (h.symm ▸ h2.adj)

@[grind ->]

Depends on / 依赖: h.symm, h2.adj, h2.not_adj_snd, not_adj_snd
-/
lemma ne_fst (h2 : G.IsPathGraph3Compl v w₁ w₂) : v != w₁ :=
  fun h => h2.not_adj_snd (h.symm ▸ h2.adj)

@[grind ->]
/--
lemma `ne_snd` / 引理 `ne_snd`

English:
lemma ne_snd
  given: (h2 : G.IsPathGraph3Compl v w₁ w₂)
  statement: v != w₂
  proof: fun h => h2.not_adj_fst (h ▸ h2.adj.symm)

@[grind ->]

中文:
引理 ne_snd
  条件: (h2 : G.是PathGraph3Compl v w₁ w₂)
  结论: v != w₂
  证明: fun h => h2.not_adj_fst (h ▸ h2.adj.symm)

@[grind ->]

Depends on / 依赖: h2.adj.symm, h2.not_adj_fst, not_adj_fst
-/
lemma ne_snd (h2 : G.IsPathGraph3Compl v w₁ w₂) : v != w₂ :=
  fun h => h2.not_adj_fst (h ▸ h2.adj.symm)

@[grind ->]
/--
lemma `fst_ne_snd` / 引理 `fst_ne_snd`

English:
lemma fst_ne_snd
  given: (h2 : G.IsPathGraph3Compl v w₁ w₂)
  statement: w₁ != w₂
  proof: h2.adj.ne

中文:
引理 fst_ne_snd
  条件: (h2 : G.是PathGraph3Compl v w₁ w₂)
  结论: w₁ != w₂
  证明: h2.adj.ne

Depends on / 依赖: h2.adj.ne
-/
lemma fst_ne_snd (h2 : G.IsPathGraph3Compl v w₁ w₂) : w₁ != w₂ := h2.adj.ne

/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: (h : G.IsPathGraph3Compl v w₁ w₂)
  statement: G.IsPathGraph3Compl v w₂ w₁
  proof: by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.symm, h3, h2⟩

中文:
引理 symm
  条件: (h : G.是PathGraph3Compl v w₁ w₂)
  结论: G.是PathGraph3Compl v w₂ w₁
  证明: by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.symm, h3, h2⟩
-/
@[symm] lemma symm (h : G.IsPathGraph3Compl v w₁ w₂) : G.IsPathGraph3Compl v w₂ w₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.symm, h3, h2⟩

end IsPathGraph3Compl

/--
lemma `exists_isPathGraph3Compl_of_not_isCompleteMultipartite` / 引理 `exists_isPathGraph3Compl_of_not_isCompleteMultipartite`

English:
lemma exists_isPathGraph3Compl_of_not_isCompleteMultipartite
  given: (h : ¬ IsCompleteMultipartite G)
  proof: by
  apply mt IsTrans.mk at h
  push Not at h
  obtain ⟨_, _, _, h1, h2, h3⟩ := h
  rw [adj_comm] at h1
  exact ⟨_, _, _, h3, h1, h2⟩

中文:
引理 存在_isPathGraph3Compl_of_not_isCompleteMultipartite
  条件: (h : ¬ IsCompleteMultipartite G)
  证明: by
  apply mt IsTrans.mk at h
  push Not at h
  obtain ⟨_, _, _, h1, h2, h3⟩ := h
  rw [adj_comm] at h1
  exact ⟨_, _, _, h3, h1, h2⟩

Depends on / 依赖: IsTrans, IsTrans.mk, adj_comm
-/
lemma exists_isPathGraph3Compl_of_not_isCompleteMultipartite (h : ¬ IsCompleteMultipartite G) :
    exists v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂ := by
  apply mt IsTrans.mk at h
  push Not at h
  obtain ⟨_, _, _, h1, h2, h3⟩ := h
  rw [adj_comm] at h1
  exact ⟨_, _, _, h3, h1, h2⟩

/--
lemma `not_isCompleteMultipartite_iff_exists_isPathGraph3Compl` / 引理 `not_isCompleteMultipartite_iff_exists_isPathGraph3Compl`

English:
lemma not_isCompleteMultipartite_iff_exists_isPathGraph3Compl
  proof: ⟨fun h => G.exists_isPathGraph3Compl_of_not_isCompleteMultipartite h,
   fun ⟨_, _, _, h1, h2, h3⟩ => fun h => h.trans _ _ _ (by rwa [adj_comm] at h2) h3 h1⟩

中文:
引理 not_isCompleteMultipartite_iff_存在_isPathGraph3Compl
  证明: ⟨fun h => G.exists_isPathGraph3Compl_of_not_isCompleteMultipartite h,
   fun ⟨_, _, _, h1, h2, h3⟩ => fun h => h.trans _ _ _ (by rwa [adj_comm] at h2) h3 h1⟩

Depends on / 依赖: G.exists_isPathGraph3Compl_of_not_isCompleteMultipartite, adj_comm, exists_isPathGraph3Compl_of_not_isCompleteMultipartite, h.trans
-/
lemma not_isCompleteMultipartite_iff_exists_isPathGraph3Compl :
    ¬ IsCompleteMultipartite G ↔ exists v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂ :=
  ⟨fun h => G.exists_isPathGraph3Compl_of_not_isCompleteMultipartite h,
   fun ⟨_, _, _, h1, h2, h3⟩ => fun h => h.trans _ _ _ (by rwa [adj_comm] at h2) h3 h1⟩

/--
Definition of `IsPathGraph3Compl.pathGraph3ComplEmbedding` / `IsPathGraph3Compl.pathGraph3ComplEmbedding` 的定义

English:
definition IsPathGraph3Compl.pathGraph3ComplEmbedding
  signature: {v w₁ w₂ : α} (h : G.IsPathGraph3Compl v w₁ w₂)
  body: fun x =>
    match x with
    | 0 => w₁
    | 1 => v
    | 2 => w₂
  inj' := by
    intro _ _ _
    have := h.ne_fst
    have := h.ne_snd
    have := h.adj.ne
    aesop
  map_rel_iff' := by
    intro _ _
    simp_rw [Embedding.coeFn_mk, compl_adj, ne_eq, pathGraph_adj, not_or]
    have := h.adj
    have := h.adj.symm
    have h1 := h.not_adj_fst
    have h2 := h.not_adj_snd
    have ⟨_, _⟩ : ¬ G.Adj w₁ v ∧ ¬ G.Adj w₂ v := by rw [adj_comm] at h1 h2; exact ⟨h1, h2⟩
    aesop

中文:
定义 是PathGraph3Compl.pathGraph3ComplEmbedding
  签名: {v w₁ w₂ : α} (h : G.是PathGraph3Compl v w₁ w₂)
  定义体: fun x =>
    match x with
    | 0 => w₁
    | 1 => v
    | 2 => w₂
  inj' := by
    intro _ _ _
    have := h.ne_fst
    have := h.ne_snd
    have := h.adj.ne
    aesop
  map_rel_iff' := by
    intro _ _
    simp_rw [Embedding.coeFn_mk, compl_adj, ne_eq, pathGraph_adj, not_or]
    have := h.adj
    have := h.adj.symm
    have h1 := h.not_adj_fst
    have h2 := h.not_adj_snd
    have ⟨_, _⟩ : ¬ G.Adj w₁ v ∧ ¬ G.Adj w₂ v := by rw [adj_comm] at h1 h2; exact ⟨h1, h2⟩
    aesop
-/
def IsPathGraph3Compl.pathGraph3ComplEmbedding {v w₁ w₂ : α} (h : G.IsPathGraph3Compl v w₁ w₂) :
    (pathGraph 3)ᶜ ↪g G where
  toFun := fun x =>
    match x with
    | 0 => w₁
    | 1 => v
    | 2 => w₂
  inj' := by
    intro _ _ _
    have := h.ne_fst
    have := h.ne_snd
    have := h.adj.ne
    aesop
  map_rel_iff' := by
    intro _ _
    simp_rw [Embedding.coeFn_mk, compl_adj, ne_eq, pathGraph_adj, not_or]
    have := h.adj
    have := h.adj.symm
    have h1 := h.not_adj_fst
    have h2 := h.not_adj_snd
    have ⟨_, _⟩ : ¬ G.Adj w₁ v ∧ ¬ G.Adj w₂ v := by rw [adj_comm] at h1 h2; exact ⟨h1, h2⟩
    aesop

/--
Definition of `pathGraph3ComplEmbeddingOf` / `pathGraph3ComplEmbeddingOf` 的定义

English:
definition pathGraph3ComplEmbeddingOf
  signature: (h : ¬ G.IsCompleteMultipartite)
  body: IsPathGraph3Compl.pathGraph3ComplEmbedding
    (exists_isPathGraph3Compl_of_not_isCompleteMultipartite h).choose_spec.choose_spec.choose_spec

中文:
定义 pathGraph3ComplEmbeddingOf
  签名: (h : ¬ G.IsCompleteMultipartite)
  定义体: IsPathGraph3Compl.pathGraph3ComplEmbedding
    (exists_isPathGraph3Compl_of_not_isCompleteMultipartite h).choose_spec.choose_spec.choose_spec

Depends on / 依赖: IsPathGraph3Compl, IsPathGraph3Compl.pathGraph3ComplEmbedding, choose_spec, choose_spec.choose_spec.choose_spec, exists_isPathGraph3Compl_of_not_isCompleteMultipartite, pathGraph3ComplEmbedding
-/
noncomputable def pathGraph3ComplEmbeddingOf (h : ¬ G.IsCompleteMultipartite) :
    (pathGraph 3)ᶜ ↪g G :=
  IsPathGraph3Compl.pathGraph3ComplEmbedding
    (exists_isPathGraph3Compl_of_not_isCompleteMultipartite h).choose_spec.choose_spec.choose_spec

/--
lemma `not_isCompleteMultipartite_of_pathGraph3ComplEmbedding` / 引理 `not_isCompleteMultipartite_of_pathGraph3ComplEmbedding`

English:
lemma not_isCompleteMultipartite_of_pathGraph3ComplEmbedding
  given: (e : (pathGraph 3)ᶜ ↪g G)
  proof: by
  intro h
  have h0 : ¬ G.Adj (e 0) (e 1) := by simp [pathGraph_adj]
  have h1 : ¬ G.Adj (e 1) (e 2) := by simp [pathGraph_adj]
  have h2 : G.Adj (e 0) (e 2) := by simp [pathGraph_adj]
  exact h.trans _ _ _ h0 h1 h2

中文:
引理 not_isCompleteMultipartite_of_pathGraph3ComplEmbedding
  条件: (e : (pathGraph 3)ᶜ ↪g G)
  证明: by
  intro h
  have h0 : ¬ G.Adj (e 0) (e 1) := by simp [pathGraph_adj]
  have h1 : ¬ G.Adj (e 1) (e 2) := by simp [pathGraph_adj]
  have h2 : G.Adj (e 0) (e 2) := by simp [pathGraph_adj]
  exact h.trans _ _ _ h0 h1 h2

Depends on / 依赖: G.Adj, h.trans, pathGraph_adj
-/
lemma not_isCompleteMultipartite_of_pathGraph3ComplEmbedding (e : (pathGraph 3)ᶜ ↪g G) :
    ¬ IsCompleteMultipartite G := by
  intro h
  have h0 : ¬ G.Adj (e 0) (e 1) := by simp [pathGraph_adj]
  have h1 : ¬ G.Adj (e 1) (e 2) := by simp [pathGraph_adj]
  have h2 : G.Adj (e 0) (e 2) := by simp [pathGraph_adj]
  exact h.trans _ _ _ h0 h1 h2

/--
theorem `IsCompleteMultipartite.comap` / 定理 `IsCompleteMultipartite.comap`

English:
theorem IsCompleteMultipartite.comap
  given: {β : Type*} {H : SimpleGraph β} (f : H ↪g G)
  proof: by
  intro h; contrapose h
  exact not_isCompleteMultipartite_of_pathGraph3ComplEmbedding
 f.comp (pathGraph3ComplEmbeddingOf h)

中文:
定理 IsCompleteMultipartite.comap
  条件: {β : 类型} {H : 简单图 β} (f : H ↪g G)
  证明: by
  intro h; contrapose h
  exact not_isCompleteMultipartite_of_pathGraph3ComplEmbedding
 f.comp (pathGraph3ComplEmbeddingOf h)

Depends on / 依赖: contrapose, f.comp, not_isCompleteMultipartite_of_pathGraph3ComplEmbedding, pathGraph3ComplEmbeddingOf
-/
theorem IsCompleteMultipartite.comap {β : Type*} {H : SimpleGraph β} (f : H ↪g G) :
    G.IsCompleteMultipartite -> H.IsCompleteMultipartite := by
  intro h; contrapose h
  exact not_isCompleteMultipartite_of_pathGraph3ComplEmbedding
 f.comp (pathGraph3ComplEmbeddingOf h)

section CompleteEquipartiteGraph

variable {r t : Nat}

/--
Definition of `completeEquipartiteGraph` / `completeEquipartiteGraph` 的定义

English:
abbreviation completeEquipartiteGraph
  signature: (r t : Nat)
  body: SimpleGraph.comap Prod.fst ⊤

中文:
缩写 completeEquipartiteGraph
  签名: (r t : 自然数)
  定义体: SimpleGraph.comap Prod.fst ⊤

Depends on / 依赖: Prod.fst, SimpleGraph, SimpleGraph.comap
-/
abbrev completeEquipartiteGraph (r t : Nat) : SimpleGraph (Fin r × Fin t) :=
  SimpleGraph.comap Prod.fst ⊤

/--
lemma `completeEquipartiteGraph_adj` / 引理 `completeEquipartiteGraph_adj`

English:
lemma completeEquipartiteGraph_adj
  given: {v w}
  proof: by rfl

中文:
引理 completeEquipartiteGraph_adj
  条件: {v w}
  证明: by rfl
-/
lemma completeEquipartiteGraph_adj {v w} :
  (completeEquipartiteGraph r t).Adj v w ↔ v.1 != w.1 := by rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `completeEquipartiteGraph.completeMultipartiteGraph` / `completeEquipartiteGraph.completeMultipartiteGraph` 的定义

English:
definition completeEquipartiteGraph.completeMultipartiteGraph
  signature: :
  body: { (Equiv.sigmaEquivProd (Fin r) (Fin t)).symm with map_rel_iff' := by simp }

中文:
定义 completeEquipartiteGraph.completeMultipartiteGraph
  签名: :
  定义体: { (Equiv.sigmaEquivProd (Fin r) (Fin t)).symm with map_rel_iff' := by simp }

Depends on / 依赖: Equiv.sigmaEquivProd, map_rel_iff, sigmaEquivProd
-/
def completeEquipartiteGraph.completeMultipartiteGraph :
    completeEquipartiteGraph r t ≃g completeMultipartiteGraph (const (Fin r) (Fin t)) :=
  { (Equiv.sigmaEquivProd (Fin r) (Fin t)).symm with map_rel_iff' := by simp }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `completeEquipartiteGraph.turanGraph` / `completeEquipartiteGraph.turanGraph` 的定义

English:
definition completeEquipartiteGraph.turanGraph
  signature: :
  body: by
    refine fun v => ⟨v.2 * r + v.1, ?_⟩
    conv_rhs =>
      rw [← Nat.sub_one_add_one_eq_of_pos v.2.pos]; rw [Nat.mul_add_one]; rw [mul_comm r (t - 1)]
    exact add_lt_add_of_le_of_lt (Nat.mul_le_mul_right r (Nat.le_pred_of_lt v.2.prop)) v.1.prop
  invFun := by
    refine fun v => (⟨v % r, ?_⟩, ⟨v / r, ?_⟩)
    · have ⟨hr, _⟩ := CanonicallyOrderedAdd.mul_pos.mp v.pos
      exact Nat.mod_lt v hr
    · exact Nat.div_lt_of_lt_mul v.prop
  left_inv v := by
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · conv =>
        enter [1, 1, 1, 1, 1]
        rw [Nat.mul_add_mod_self_right]
      exact Nat.mod_eq_of_lt v.1.prop
    · apply le_antisymm
      · rw [Nat.div_le_iff_le_mul_add_pred v.1.pos, mul_comm r ↑v.2]
        exact Nat.add_le_add_left (Nat.le_pred_of_lt v.1.prop) (↑v.2 * r)
      · rw [Nat.le_div_iff_mul_le v.1.pos]
        exact Nat.le_add_right (↑v.2 * r) ↑v.1
  right_inv v := Fin.ext (Nat.div_add_mod' v r)
  map_rel_iff' {v w} := by
    rw [turanGraph_adj]; rw [Equiv.coe_fn_mk]; rw [Nat.mul_add_mod_self_right]; rw [Nat.mod_eq_of_lt v.1.prop]; rw [Nat.mul_add_mod_self_right]; rw [Nat.mod_eq_of_lt w.1.prop]; rw [← Fin.ext_iff.ne]; rw [← completeEquipartiteGraph_adj]

中文:
定义 completeEquipartiteGraph.turanGraph
  签名: :
  定义体: by
    refine fun v => ⟨v.2 * r + v.1, ?_⟩
    conv_rhs =>
      rw [← Nat.sub_one_add_one_eq_of_pos v.2.pos]; rw [Nat.mul_add_one]; rw [mul_comm r (t - 1)]
    exact add_lt_add_of_le_of_lt (Nat.mul_le_mul_right r (Nat.le_pred_of_lt v.2.prop)) v.1.prop
  invFun := by
    refine fun v => (⟨v % r, ?_⟩, ⟨v / r, ?_⟩)
    · have ⟨hr, _⟩ := CanonicallyOrderedAdd.mul_pos.mp v.pos
      exact Nat.mod_lt v hr
    · exact Nat.div_lt_of_lt_mul v.prop
  left_inv v := by
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · conv =>
        enter [1, 1, 1, 1, 1]
        rw [Nat.mul_add_mod_self_right]
      exact Nat.mod_eq_of_lt v.1.prop
    · apply le_antisymm
      · rw [Nat.div_le_iff_le_mul_add_pred v.1.pos, mul_comm r ↑v.2]
        exact Nat.add_le_add_left (Nat.le_pred_of_lt v.1.prop) (↑v.2 * r)
      · rw [Nat.le_div_iff_mul_le v.1.pos]
        exact Nat.le_add_right (↑v.2 * r) ↑v.1
  right_inv v := Fin.ext (Nat.div_add_mod' v r)
  map_rel_iff' {v w} := by
    rw [turanGraph_adj]; rw [Equiv.coe_fn_mk]; rw [Nat.mul_add_mod_self_right]; rw [Nat.mod_eq_of_lt v.1.prop]; rw [Nat.mul_add_mod_self_right]; rw [Nat.mod_eq_of_lt w.1.prop]; rw [← Fin.ext_iff.ne]; rw [← completeEquipartiteGraph_adj]

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.mul_pos.mp, Fin.ext, Nat.div_lt_of_lt_mul, Nat.le_pred_of_lt, Nat.mod_lt, Nat.mul_add_one, Nat.mul_le_mul_right, Nat.sub_one_add_one_eq_of_pos, Prod.ext, add_lt_add_of_le_of_lt, conv_rhs, div_lt_of_lt_mul, invFun, le_pred_of_lt, left_inv, mod_lt, mul_add_one, mul_comm, mul_le_mul_right
-/
def completeEquipartiteGraph.turanGraph :
    completeEquipartiteGraph r t ≃g turanGraph (r * t) r where
  toFun := by
    refine fun v => ⟨v.2 * r + v.1, ?_⟩
    conv_rhs =>
      rw [← Nat.sub_one_add_one_eq_of_pos v.2.pos]; rw [Nat.mul_add_one]; rw [mul_comm r (t - 1)]
    exact add_lt_add_of_le_of_lt (Nat.mul_le_mul_right r (Nat.le_pred_of_lt v.2.prop)) v.1.prop
  invFun := by
    refine fun v => (⟨v % r, ?_⟩, ⟨v / r, ?_⟩)
    · have ⟨hr, _⟩ := CanonicallyOrderedAdd.mul_pos.mp v.pos
      exact Nat.mod_lt v hr
    · exact Nat.div_lt_of_lt_mul v.prop
  left_inv v := by
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · conv =>
        enter [1, 1, 1, 1, 1]
        rw [Nat.mul_add_mod_self_right]
      exact Nat.mod_eq_of_lt v.1.prop
    · apply le_antisymm
      · rw [Nat.div_le_iff_le_mul_add_pred v.1.pos, mul_comm r ↑v.2]
        exact Nat.add_le_add_left (Nat.le_pred_of_lt v.1.prop) (↑v.2 * r)
      · rw [Nat.le_div_iff_mul_le v.1.pos]
        exact Nat.le_add_right (↑v.2 * r) ↑v.1
  right_inv v := Fin.ext (Nat.div_add_mod' v r)
  map_rel_iff' {v w} := by
    rw [turanGraph_adj]; rw [Equiv.coe_fn_mk]; rw [Nat.mul_add_mod_self_right]; rw [Nat.mod_eq_of_lt v.1.prop]; rw [Nat.mul_add_mod_self_right]; rw [Nat.mod_eq_of_lt w.1.prop]; rw [← Fin.ext_iff.ne]; rw [← completeEquipartiteGraph_adj]

/--
lemma `completeEquipartiteGraph_eq_bot_iff` / 引理 `completeEquipartiteGraph_eq_bot_iff`

English:
lemma completeEquipartiteGraph_eq_bot_iff
  proof: by
  contrapose!
  rw [← edgeSet_nonempty]; rw [← Nat.succ_le_iff]; rw [← Fin.nontrivial_iff_two_le]; rw [← Nat.pos_iff_ne_zero]; rw [Fin.pos_iff_nonempty]
  refine ⟨fun ⟨e, he⟩ => ?_, fun ⟨⟨i₁, i₂, hv⟩, ⟨x⟩⟩ => ?_⟩
  · induction e with | _ v₁ v₂
    rw [mem_edgeSet]; rw [completeEquipartiteGraph_adj] at he
    exact ⟨⟨v₁.1, v₂.1, he⟩, ⟨v₁.2⟩⟩
  · use s((i₁, x), (i₂, x))
    rw [mem_edgeSet]; rw [completeEquipartiteGraph_adj]
    exact hv

中文:
引理 completeEquipartiteGraph_eq_bot_iff
  证明: by
  contrapose!
  rw [← edgeSet_nonempty]; rw [← Nat.succ_le_iff]; rw [← Fin.nontrivial_iff_two_le]; rw [← Nat.pos_iff_ne_zero]; rw [Fin.pos_iff_nonempty]
  refine ⟨fun ⟨e, he⟩ => ?_, fun ⟨⟨i₁, i₂, hv⟩, ⟨x⟩⟩ => ?_⟩
  · induction e with | _ v₁ v₂
    rw [mem_edgeSet]; rw [completeEquipartiteGraph_adj] at he
    exact ⟨⟨v₁.1, v₂.1, he⟩, ⟨v₁.2⟩⟩
  · use s((i₁, x), (i₂, x))
    rw [mem_edgeSet]; rw [completeEquipartiteGraph_adj]
    exact hv

Depends on / 依赖: Fin.nontrivial_iff_two_le, Fin.pos_iff_nonempty, Nat.pos_iff_ne_zero, Nat.succ_le_iff, completeEquipartiteGraph_adj, contrapose, edgeSet_nonempty, mem_edgeSet, nontrivial_iff_two_le, pos_iff_ne_zero, pos_iff_nonempty, succ_le_iff
-/
lemma completeEquipartiteGraph_eq_bot_iff :
    completeEquipartiteGraph r t = ⊥ ↔ r <= 1 ∨ t = 0 := by
  contrapose!
  rw [← edgeSet_nonempty]; rw [← Nat.succ_le_iff]; rw [← Fin.nontrivial_iff_two_le]; rw [← Nat.pos_iff_ne_zero]; rw [Fin.pos_iff_nonempty]
  refine ⟨fun ⟨e, he⟩ => ?_, fun ⟨⟨i₁, i₂, hv⟩, ⟨x⟩⟩ => ?_⟩
  · induction e with | _ v₁ v₂
    rw [mem_edgeSet]; rw [completeEquipartiteGraph_adj] at he
    exact ⟨⟨v₁.1, v₂.1, he⟩, ⟨v₁.2⟩⟩
  · use s((i₁, x), (i₂, x))
    rw [mem_edgeSet]; rw [completeEquipartiteGraph_adj]
    exact hv

/--
theorem `completeEquipartiteGraph.isCompleteMultipartite` / 定理 `completeEquipartiteGraph.isCompleteMultipartite`

English:
theorem completeEquipartiteGraph.isCompleteMultipartite
  proof: by
  rcases t.eq_zero_or_pos with ht_eq0 | ht_pos
  · rw [completeEquipartiteGraph_eq_bot_iff.mpr (Or.inr ht_eq0)]
    exact bot_isCompleteMultipartite
  · rw [isCompleteMultipartite_iff]
    use (Fin r), const (Fin r) (Fin t)
    simp_rw [const_apply, exists_prop]
    exact ⟨const (Fin r) (Fin.pos_iff_nonempty.mp ht_pos),
      ⟨completeEquipartiteGraph.completeMultipartiteGraph⟩⟩

中文:
定理 completeEquipartiteGraph.isCompleteMultipartite
  证明: by
  rcases t.eq_zero_or_pos with ht_eq0 | ht_pos
  · rw [completeEquipartiteGraph_eq_bot_iff.mpr (Or.inr ht_eq0)]
    exact bot_isCompleteMultipartite
  · rw [isCompleteMultipartite_iff]
    use (Fin r), const (Fin r) (Fin t)
    simp_rw [const_apply, exists_prop]
    exact ⟨const (Fin r) (Fin.pos_iff_nonempty.mp ht_pos),
      ⟨completeEquipartiteGraph.completeMultipartiteGraph⟩⟩

Depends on / 依赖: Fin.pos_iff_nonempty.mp, Or.inr, bot_isCompleteMultipartite, completeEquipartiteGraph, completeEquipartiteGraph.completeMultipartiteGraph, completeEquipartiteGraph_eq_bot_iff, completeEquipartiteGraph_eq_bot_iff.mpr, completeMultipartiteGraph, const_apply, eq_zero_or_pos, exists_prop, ht_eq0, ht_pos, isCompleteMultipartite_iff, pos_iff_nonempty, simp_rw, t.eq_zero_or_pos
-/
theorem completeEquipartiteGraph.isCompleteMultipartite :
    (completeEquipartiteGraph r t).IsCompleteMultipartite := by
  rcases t.eq_zero_or_pos with ht_eq0 | ht_pos
  · rw [completeEquipartiteGraph_eq_bot_iff.mpr (Or.inr ht_eq0)]
    exact bot_isCompleteMultipartite
  · rw [isCompleteMultipartite_iff]
    use (Fin r), const (Fin r) (Fin t)
    simp_rw [const_apply, exists_prop]
    exact ⟨const (Fin r) (Fin.pos_iff_nonempty.mp ht_pos),
      ⟨completeEquipartiteGraph.completeMultipartiteGraph⟩⟩

/--
theorem `neighborSet_completeEquipartiteGraph` / 定理 `neighborSet_completeEquipartiteGraph`

English:
theorem neighborSet_completeEquipartiteGraph
  given: (v)
  proof: by
  ext; simp [ne_comm]

中文:
定理 neighborSet_completeEquipartiteGraph
  条件: (v)
  证明: by
  ext; simp [ne_comm]

Depends on / 依赖: ne_comm
-/
theorem neighborSet_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).neighborSet v = {v.1}ᶜ ×ˢ Set.univ := by
  ext; simp [ne_comm]

/--
theorem `neighborFinset_completeEquipartiteGraph` / 定理 `neighborFinset_completeEquipartiteGraph`

English:
theorem neighborFinset_completeEquipartiteGraph
  given: (v)
  proof: by
  ext; simp [ne_comm]

中文:
定理 neighborFinset_completeEquipartiteGraph
  条件: (v)
  证明: by
  ext; simp [ne_comm]

Depends on / 依赖: ne_comm
-/
theorem neighborFinset_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).neighborFinset v = {v.1}ᶜ ×ˢ univ := by
  ext; simp [ne_comm]

/--
theorem `degree_completeEquipartiteGraph` / 定理 `degree_completeEquipartiteGraph`

English:
theorem degree_completeEquipartiteGraph
  given: (v)
  proof: by
  rw [← card_neighborFinset_eq_degree]; rw [neighborFinset_completeEquipartiteGraph v]; rw [card_product]; rw [card_compl]; rw [card_singleton]; rw [Fintype.card_fin]; rw [card_univ]; rw [Fintype.card_fin]

中文:
定理 degree_completeEquipartiteGraph
  条件: (v)
  证明: by
  rw [← card_neighborFinset_eq_degree]; rw [neighborFinset_completeEquipartiteGraph v]; rw [card_product]; rw [card_compl]; rw [card_singleton]; rw [Fintype.card_fin]; rw [card_univ]; rw [Fintype.card_fin]

Depends on / 依赖: Fintype, Fintype.card_fin, card_compl, card_fin, card_neighborFinset_eq_degree, card_product, card_singleton, card_univ, neighborFinset_completeEquipartiteGraph
-/
theorem degree_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).degree v = (r - 1) * t := by
  rw [← card_neighborFinset_eq_degree]; rw [neighborFinset_completeEquipartiteGraph v]; rw [card_product]; rw [card_compl]; rw [card_singleton]; rw [Fintype.card_fin]; rw [card_univ]; rw [Fintype.card_fin]

/--
theorem `card_edgeFinset_completeEquipartiteGraph` / 定理 `card_edgeFinset_completeEquipartiteGraph`

English:
theorem card_edgeFinset_completeEquipartiteGraph
  proof: by
  rw [← mul_right_inj' two_ne_zero]; rw [← sum_degrees_eq_twice_card_edges]
  conv_lhs =>
    rhs; intro v
    rw [degree_completeEquipartiteGraph v]
  rw [sum_const]; rw [smul_eq_mul]; rw [card_univ]; rw [card_prod]; rw [Fintype.card_fin]; rw [Fintype.card_fin]
  conv_rhs =>
    rw [← Nat.mul_assoc]; rw [Nat.choose_two_right]; rw [Nat.mul_div_cancel' r.even_mul_pred_self.two_dvd]
  rw [← mul_assoc]; rw [mul_comm r _]; rw [mul_assoc t _ _]; rw [mul_comm t]; rw [mul_assoc _ t]; rw [← pow_two]

中文:
定理 card_edgeFinset_completeEquipartiteGraph
  证明: by
  rw [← mul_right_inj' two_ne_zero]; rw [← sum_degrees_eq_twice_card_edges]
  conv_lhs =>
    rhs; intro v
    rw [degree_completeEquipartiteGraph v]
  rw [sum_const]; rw [smul_eq_mul]; rw [card_univ]; rw [card_prod]; rw [Fintype.card_fin]; rw [Fintype.card_fin]
  conv_rhs =>
    rw [← Nat.mul_assoc]; rw [Nat.choose_two_right]; rw [Nat.mul_div_cancel' r.even_mul_pred_self.two_dvd]
  rw [← mul_assoc]; rw [mul_comm r _]; rw [mul_assoc t _ _]; rw [mul_comm t]; rw [mul_assoc _ t]; rw [← pow_two]

Depends on / 依赖: Fintype, Fintype.card_fin, Nat.choose_two_right, Nat.mul_assoc, Nat.mul_div_cancel, card_fin, card_prod, card_univ, choose_two_right, conv_lhs, conv_rhs, degree_completeEquipartiteGraph, even_mul_pred_self, mul_assoc, mul_comm, mul_div_cancel, mul_right_inj, pow_two, r.even_mul_pred_self.two_dvd, smul_eq_mul
-/
theorem card_edgeFinset_completeEquipartiteGraph :
    #(completeEquipartiteGraph r t).edgeFinset = r.choose 2 * t ^ 2 := by
  rw [← mul_right_inj' two_ne_zero]; rw [← sum_degrees_eq_twice_card_edges]
  conv_lhs =>
    rhs; intro v
    rw [degree_completeEquipartiteGraph v]
  rw [sum_const]; rw [smul_eq_mul]; rw [card_univ]; rw [card_prod]; rw [Fintype.card_fin]; rw [Fintype.card_fin]
  conv_rhs =>
    rw [← Nat.mul_assoc]; rw [Nat.choose_two_right]; rw [Nat.mul_div_cancel' r.even_mul_pred_self.two_dvd]
  rw [← mul_assoc]; rw [mul_comm r _]; rw [mul_assoc t _ _]; rw [mul_comm t]; rw [mul_assoc _ t]; rw [← pow_two]

variable [Fintype α]

/--
theorem `isContained_completeEquipartiteGraph_of_colorable` / 定理 `isContained_completeEquipartiteGraph_of_colorable`

English:
theorem isContained_completeEquipartiteGraph_of_colorable
  statement: {n : Nat} (C : G.Coloring (Fin n))
  proof: by
  have (c : Fin n) : Nonempty (C.colorClass c ↪ Fin t) := by
    rw [Embedding.nonempty_iff_card_le]; rw [Fintype.card_fin]
    exact h c
  have F (c : Fin n) := Classical.arbitrary (C.colorClass c ↪ Fin t)
  have hF {c₁ c₂ v₁ v₂} (hc : c₁ = c₂) (hv : F c₁ v₁ = F c₂ v₂) : v₁.val = v₂.val := by
    let v₁' : C.colorClass c₂ := ⟨v₁, by simp [← hc]⟩
    have hv' : F c₁ v₁ = F c₂ v₁' := by
      apply congr_heq
      · rw [hc]
      · rw [Subtype.heq_iff_coe_eq]
        simp [hc]
    rw [hv'] at hv
    simpa [Subtype.ext_iff] using (F c₂).injective hv
  use ⟨fun v => (C v, F (C v) ⟨v, C.mem_colorClass v⟩), C.valid⟩
  intro v w h
  rw [Prod.mk.injEq] at h
  exact hF h.1 h.2

中文:
定理 isContained_completeEquipartiteGraph_of_colorable
  结论: {n : 自然数} (C : G.染色 (有限集 n))
  证明: by
  have (c : Fin n) : Nonempty (C.colorClass c ↪ Fin t) := by
    rw [Embedding.nonempty_iff_card_le]; rw [Fintype.card_fin]
    exact h c
  have F (c : Fin n) := Classical.arbitrary (C.colorClass c ↪ Fin t)
  have hF {c₁ c₂ v₁ v₂} (hc : c₁ = c₂) (hv : F c₁ v₁ = F c₂ v₂) : v₁.val = v₂.val := by
    let v₁' : C.colorClass c₂ := ⟨v₁, by simp [← hc]⟩
    have hv' : F c₁ v₁ = F c₂ v₁' := by
      apply congr_heq
      · rw [hc]
      · rw [Subtype.heq_iff_coe_eq]
        simp [hc]
    rw [hv'] at hv
    simpa [Subtype.ext_iff] using (F c₂).injective hv
  use ⟨fun v => (C v, F (C v) ⟨v, C.mem_colorClass v⟩), C.valid⟩
  intro v w h
  rw [Prod.mk.injEq] at h
  exact hF h.1 h.2

Depends on / 依赖: C.colorClass, Classical, Classical.arbitrary, Embedding, Embedding.nonempty_iff_card_le, Fintype, Fintype.card_fin, Nonempty, Subtype, Subtype.ext_iff, Subtype.heq_iff_coe_eq, arbitrary, card_fin, colorClass, congr_heq, ext_iff, heq_iff_coe_eq, injective, nonempty_iff_card_le
-/
theorem isContained_completeEquipartiteGraph_of_colorable {n : Nat} (C : G.Coloring (Fin n))
    (t : Nat) (h : forall c, card (C.colorClass c) <= t) : G ⊑ completeEquipartiteGraph n t := by
  have (c : Fin n) : Nonempty (C.colorClass c ↪ Fin t) := by
    rw [Embedding.nonempty_iff_card_le]; rw [Fintype.card_fin]
    exact h c
  have F (c : Fin n) := Classical.arbitrary (C.colorClass c ↪ Fin t)
  have hF {c₁ c₂ v₁ v₂} (hc : c₁ = c₂) (hv : F c₁ v₁ = F c₂ v₂) : v₁.val = v₂.val := by
    let v₁' : C.colorClass c₂ := ⟨v₁, by simp [← hc]⟩
    have hv' : F c₁ v₁ = F c₂ v₁' := by
      apply congr_heq
      · rw [hc]
      · rw [Subtype.heq_iff_coe_eq]
        simp [hc]
    rw [hv'] at hv
    simpa [Subtype.ext_iff] using (F c₂).injective hv
  use ⟨fun v => (C v, F (C v) ⟨v, C.mem_colorClass v⟩), C.valid⟩
  intro v w h
  rw [Prod.mk.injEq] at h
  exact hF h.1 h.2

end CompleteEquipartiteGraph

section CompleteEquipartiteSubgraph

variable {V : Type*} {G : SimpleGraph V}

/-- A complete equipartite subgraph in `r > 0` parts each of size `t ≠ 0` in `G` is `r` subsets
of vertices each of size `t` such that vertices in distinct subsets are adjacent.

If `r > 0` but `t = 0`, then `parts = {{}}`. If `r = 0`, then `parts = {}`. These are the two
*distinct* "empty" complete equipartite subgraphs, that is, the complete equipartite subgraphs
having no vertices. -/
@[ext]
/--
Definition of `CompleteEquipartiteSubgraph` / `CompleteEquipartiteSubgraph` 的定义

English:
structure CompleteEquipartiteSubgraph
  parameters: (G : SimpleGraph V) (r t : Nat)
  axioms and operations (4):
    - parts : Finset (Finset V)
    - card_parts : #parts = r ∨ t = 0
    - card_mem_parts({p}) : p in parts -> #p = t
    - isCompleteBetween : (parts : Set (Finset V)).Pairwise (G.IsCompleteBetween · ·)

中文:
结构 余mpleteEquipartiteSubgraph
  参数: (G : 简单图 V) (r t : 自然数)
  公理与运算 (4 个):
    - parts : 有限集 (有限集 V)
    - card_parts : #parts = r ∨ t = 0
    - card_mem_parts({p}) : p in parts -> #p = t
    - isCompleteBetween : (parts : 集合 (有限集 V)).两两 (G.IsCompleteBetween · ·)
-/
structure CompleteEquipartiteSubgraph (G : SimpleGraph V) (r t : Nat) where
  /-- The parts in a complete equipartite subgraph. -/
  parts : Finset (Finset V)
  /-- There are `r` parts or `t = 0`. -/
  card_parts : #parts = r ∨ t = 0
  /-- There are `t` vertices in each part. -/
  card_mem_parts {p} : p in parts -> #p = t
  /-- The vertices in distinct parts are adjacent. -/
  isCompleteBetween : (parts : Set (Finset V)).Pairwise (G.IsCompleteBetween · ·)

variable {r t : Nat} (K : G.CompleteEquipartiteSubgraph r t)

namespace CompleteEquipartiteSubgraph

/--
theorem `nonempty_of_eq_zero_or_eq_zero` / 定理 `nonempty_of_eq_zero_or_eq_zero`

English:
theorem nonempty_of_eq_zero_or_eq_zero
  given: (h : r = 0 ∨ t = 0)
  proof: ⟨{}, h.elim (fun hr => by simp [hr]) (fun ht => by simp [ht]), by simp, by simp⟩

中文:
定理 nonempty_of_eq_zero_or_eq_zero
  条件: (h : r = 0 ∨ t = 0)
  证明: ⟨{}, h.elim (fun hr => by simp [hr]) (fun ht => by simp [ht]), by simp, by simp⟩

Depends on / 依赖: h.elim
-/
theorem nonempty_of_eq_zero_or_eq_zero (h : r = 0 ∨ t = 0) :
    Nonempty (G.CompleteEquipartiteSubgraph r t) :=
  ⟨{}, h.elim (fun hr => by simp [hr]) (fun ht => by simp [ht]), by simp, by simp⟩

/--
theorem `disjoint` / 定理 `disjoint`

English:
theorem disjoint
  statement: (K.parts : Set (Finset V)).Pairwise Disjoint
  proof: fun _ h₁ _ h₂ hne => Finset.disjoint_left.mpr fun _ h₁' h₂' =>
G.irrefl K.isCompleteBetween h₁ h₂ hne h₁' h₂'

中文:
定理 disjoint
  结论: (K.parts : 集合 (有限集 V)).两两 Disjoint
  证明: fun _ h₁ _ h₂ hne => Finset.disjoint_left.mpr fun _ h₁' h₂' =>
G.irrefl K.isCompleteBetween h₁ h₂ hne h₁' h₂'

Depends on / 依赖: Finset, Finset.disjoint_left.mpr, G.irrefl, K.isCompleteBetween, disjoint_left, irrefl, isCompleteBetween
-/
theorem disjoint : (K.parts : Set (Finset V)).Pairwise Disjoint :=
  fun _ h₁ _ h₂ hne => Finset.disjoint_left.mpr fun _ h₁' h₂' =>
G.irrefl K.isCompleteBetween h₁ h₂ hne h₁' h₂'

/--
Definition of `verts` / `verts` 的定义

English:
definition verts
  signature: : Finset V
  body: K.parts.disjiUnion id K.disjoint

中文:
定义 verts
  签名: : 有限集 V
  定义体: K.parts.disjiUnion id K.disjoint

Depends on / 依赖: K.disjoint, K.parts.disjiUnion, disjiUnion, disjoint
-/
def verts : Finset V := K.parts.disjiUnion id K.disjoint

set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/--
lemma `verts_eq_biUnion` / 引理 `verts_eq_biUnion`

English:
lemma verts_eq_biUnion
  statement: K.verts = K.parts.biUnion id
  proof: by rw [verts, disjiUnion_eq_biUnion]

中文:
引理 verts_eq_biUnion
  结论: K.verts = K.parts.biUnion id
  证明: by rw [verts, disjiUnion_eq_biUnion]

Depends on / 依赖: disjiUnion_eq_biUnion
-/
lemma verts_eq_biUnion : K.verts = K.parts.biUnion id := by rw [verts, disjiUnion_eq_biUnion]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `card_verts` / 定理 `card_verts`

English:
theorem card_verts
  statement: #K.verts = r * t
  proof: by
  simp_rw [verts, card_disjiUnion, id_eq, sum_congr rfl fun _ => K.card_mem_parts, sum_const,
    smul_eq_mul, mul_eq_mul_right_iff]
  exact K.card_parts

中文:
定理 card_verts
  结论: #K.verts = r * t
  证明: by
  simp_rw [verts, card_disjiUnion, id_eq, sum_congr rfl fun _ => K.card_mem_parts, sum_const,
    smul_eq_mul, mul_eq_mul_right_iff]
  exact K.card_parts

Depends on / 依赖: K.card_mem_parts, K.card_parts, card_disjiUnion, card_mem_parts, card_parts, id_eq, mul_eq_mul_right_iff, simp_rw, smul_eq_mul, sum_congr, sum_const
-/
theorem card_verts : #K.verts = r * t := by
  simp_rw [verts, card_disjiUnion, id_eq, sum_congr rfl fun _ => K.card_mem_parts, sum_const,
    smul_eq_mul, mul_eq_mul_right_iff]
  exact K.card_parts

/--
Definition of `toCopy` / `toCopy` 的定义

English:
definition toCopy
  signature: : Copy (completeEquipartiteGraph r t) G
  body: by
  by_cases ht : t = 0
  · rw [completeEquipartiteGraph_eq_bot_iff.mpr <| .inr ht]
    have : IsEmpty (Fin r × Fin t) := by simp [ht, Fin.isEmpty]
    exact Copy.bot .ofIsEmpty
  · have : Nonempty (Fin r ↪ K.parts) := by
      rw [Embedding.nonempty_iff_card_le]; rw [Fintype.card_fin]; rw [card_coe]; rw [K.card_parts.resolve_right ht]
    let fᵣ : Fin r ↪ K.parts := Classical.arbitrary (Fin r ↪ K.parts)
    have (p : K.parts) : Nonempty (Fin t ↪ p) := by
      rw [Embedding.nonempty_iff_card_le]; rw [Fintype.card_fin]; rw [card_coe]; rw [K.card_mem_parts p.prop]
    let fₜ (p : K.parts) : Fin t ↪ p :=
      Classical.arbitrary (Fin t ↪ p)
    let f : (Fin r) × (Fin t) ↪ V := by
      use fun (i, j) => fₜ (fᵣ i) j
      intro (i₁, j₁) (i₂, j₂) heq
      rw [Prod.mk.injEq]
      contrapose! heq with hne
      rcases eq_or_ne i₁ i₂ with heq | hne
      · rw [heq, ← Subtype.ext_iff.ne]
        exact (fₜ _).injective.ne (hne heq)
      · refine (K.isCompleteBetween (fᵣ _).prop (fᵣ _).prop ?_ (fₜ _ _).prop (fₜ _ _).prop).ne
exact Subtype.ext_iff.ne.mp fᵣ.injective.ne hne
    refine ⟨⟨f, fun hne => ?_⟩, f.injective⟩
    refine K.isCompleteBetween (fᵣ _).prop (fᵣ _).prop ?_ (fₜ _ _).prop (fₜ _ _).prop
exact Subtype.ext_iff.ne.mp fᵣ.injective.ne hne

中文:
定义 toCopy
  签名: : 余py (completeEquipartiteGraph r t) G
  定义体: by
  by_cases ht : t = 0
  · rw [completeEquipartiteGraph_eq_bot_iff.mpr <| .inr ht]
    have : IsEmpty (Fin r × Fin t) := by simp [ht, Fin.isEmpty]
    exact Copy.bot .ofIsEmpty
  · have : Nonempty (Fin r ↪ K.parts) := by
      rw [Embedding.nonempty_iff_card_le]; rw [Fintype.card_fin]; rw [card_coe]; rw [K.card_parts.resolve_right ht]
    let fᵣ : Fin r ↪ K.parts := Classical.arbitrary (Fin r ↪ K.parts)
    have (p : K.parts) : Nonempty (Fin t ↪ p) := by
      rw [Embedding.nonempty_iff_card_le]; rw [Fintype.card_fin]; rw [card_coe]; rw [K.card_mem_parts p.prop]
    let fₜ (p : K.parts) : Fin t ↪ p :=
      Classical.arbitrary (Fin t ↪ p)
    let f : (Fin r) × (Fin t) ↪ V := by
      use fun (i, j) => fₜ (fᵣ i) j
      intro (i₁, j₁) (i₂, j₂) heq
      rw [Prod.mk.injEq]
      contrapose! heq with hne
      rcases eq_or_ne i₁ i₂ with heq | hne
      · rw [heq, ← Subtype.ext_iff.ne]
        exact (fₜ _).injective.ne (hne heq)
      · refine (K.isCompleteBetween (fᵣ _).prop (fᵣ _).prop ?_ (fₜ _ _).prop (fₜ _ _).prop).ne
exact Subtype.ext_iff.ne.mp fᵣ.injective.ne hne
    refine ⟨⟨f, fun hne => ?_⟩, f.injective⟩
    refine K.isCompleteBetween (fᵣ _).prop (fᵣ _).prop ?_ (fₜ _ _).prop (fₜ _ _).prop
exact Subtype.ext_iff.ne.mp fᵣ.injective.ne hne

Depends on / 依赖: Classical, Classical.arbitrary, Copy.bot, Embedding, Embedding.nonempty_iff_card_le, Fin.isEmpty, Fintype, Fintype.card_fin, IsEmpty, K.card_parts.resolve_right, K.parts, Nonempty, arbitrary, card_coe, card_fin, card_parts, completeEquipartiteGraph_eq_bot_iff, completeEquipartiteGraph_eq_bot_iff.mpr, isEmpty, nonempty_iff_card_le
-/
noncomputable def toCopy : Copy (completeEquipartiteGraph r t) G := by
  by_cases ht : t = 0
  · rw [completeEquipartiteGraph_eq_bot_iff.mpr <| .inr ht]
    have : IsEmpty (Fin r × Fin t) := by simp [ht, Fin.isEmpty]
    exact Copy.bot .ofIsEmpty
  · have : Nonempty (Fin r ↪ K.parts) := by
      rw [Embedding.nonempty_iff_card_le]; rw [Fintype.card_fin]; rw [card_coe]; rw [K.card_parts.resolve_right ht]
    let fᵣ : Fin r ↪ K.parts := Classical.arbitrary (Fin r ↪ K.parts)
    have (p : K.parts) : Nonempty (Fin t ↪ p) := by
      rw [Embedding.nonempty_iff_card_le]; rw [Fintype.card_fin]; rw [card_coe]; rw [K.card_mem_parts p.prop]
    let fₜ (p : K.parts) : Fin t ↪ p :=
      Classical.arbitrary (Fin t ↪ p)
    let f : (Fin r) × (Fin t) ↪ V := by
      use fun (i, j) => fₜ (fᵣ i) j
      intro (i₁, j₁) (i₂, j₂) heq
      rw [Prod.mk.injEq]
      contrapose! heq with hne
      rcases eq_or_ne i₁ i₂ with heq | hne
      · rw [heq, ← Subtype.ext_iff.ne]
        exact (fₜ _).injective.ne (hne heq)
      · refine (K.isCompleteBetween (fᵣ _).prop (fᵣ _).prop ?_ (fₜ _ _).prop (fₜ _ _).prop).ne
exact Subtype.ext_iff.ne.mp fᵣ.injective.ne hne
    refine ⟨⟨f, fun hne => ?_⟩, f.injective⟩
    refine K.isCompleteBetween (fᵣ _).prop (fᵣ _).prop ?_ (fₜ _ _).prop (fₜ _ _).prop
exact Subtype.ext_iff.ne.mp fᵣ.injective.ne hne

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `ofCopy` / `ofCopy` 的定义

English:
definition ofCopy
  signature: (f : Copy (completeEquipartiteGraph r t) G)
  body: by
  by_cases ht : t = 0
  · exact ⟨∅, .inr ht, by simp, by simp⟩
  · refine ⟨univ.map ⟨fun i => univ.map ⟨fun j => f (i, j), fun _ _ h => ?_⟩, fun i₁ i₂ h => ?_⟩,
      ?_, fun h => ?_, fun _ h₁ _ h₂ hne _ h₁' _ h₂' => ?_⟩
    · simpa using f.injective h
    · simp_rw [Finset.ext_iff] at h
      have : NeZero t := ⟨ht⟩
obtain ⟨_, heq⟩ : exists j, f (i₁, j) = f (i₂, 0) := by simpa using h f (i₂, 0)
      apply f.injective at heq
      rw [Prod.mk.injEq] at heq
      exact heq.left
    · simp
    · simp_rw [mem_map, mem_univ, Embedding.coeFn_mk, true_and] at h
      replace ⟨_, h⟩ := h
      simp [← h]
    · simp_rw [coe_map, Embedding.coeFn_mk, coe_univ, Set.image_univ, Set.mem_range] at h₁ h₂
      replace ⟨_, h₁⟩ := h₁
      replace ⟨_, h₂⟩ := h₂
      rw [← h₁] at h₁'
      rw [← h₂] at h₂'
      simp_rw [coe_map, Embedding.coeFn_mk, coe_univ, Set.image_univ, Set.mem_range] at h₁' h₂'
      replace ⟨_, h₁'⟩ := h₁'
      replace ⟨_, h₂'⟩ := h₂'
      rw [← h₁']; rw [← h₂']
      apply f.toHom.map_adj
      simp_rw [completeEquipartiteGraph_adj]
      contrapose hne with heq
      simp_rw [← h₁, ← h₂, heq]

中文:
定义 ofCopy
  签名: (f : 余py (completeEquipartiteGraph r t) G)
  定义体: by
  by_cases ht : t = 0
  · exact ⟨∅, .inr ht, by simp, by simp⟩
  · refine ⟨univ.map ⟨fun i => univ.map ⟨fun j => f (i, j), fun _ _ h => ?_⟩, fun i₁ i₂ h => ?_⟩,
      ?_, fun h => ?_, fun _ h₁ _ h₂ hne _ h₁' _ h₂' => ?_⟩
    · simpa using f.injective h
    · simp_rw [Finset.ext_iff] at h
      have : NeZero t := ⟨ht⟩
obtain ⟨_, heq⟩ : exists j, f (i₁, j) = f (i₂, 0) := by simpa using h f (i₂, 0)
      apply f.injective at heq
      rw [Prod.mk.injEq] at heq
      exact heq.left
    · simp
    · simp_rw [mem_map, mem_univ, Embedding.coeFn_mk, true_and] at h
      replace ⟨_, h⟩ := h
      simp [← h]
    · simp_rw [coe_map, Embedding.coeFn_mk, coe_univ, Set.image_univ, Set.mem_range] at h₁ h₂
      replace ⟨_, h₁⟩ := h₁
      replace ⟨_, h₂⟩ := h₂
      rw [← h₁] at h₁'
      rw [← h₂] at h₂'
      simp_rw [coe_map, Embedding.coeFn_mk, coe_univ, Set.image_univ, Set.mem_range] at h₁' h₂'
      replace ⟨_, h₁'⟩ := h₁'
      replace ⟨_, h₂'⟩ := h₂'
      rw [← h₁']; rw [← h₂']
      apply f.toHom.map_adj
      simp_rw [completeEquipartiteGraph_adj]
      contrapose hne with heq
      simp_rw [← h₁, ← h₂, heq]

Depends on / 依赖: Embedding, Embedding.coeFn_mk, Finset, Finset.ext_iff, NeZero, Prod.mk.injEq, coeFn_mk, ext_iff, f.injective, heq.left, injective, mem_map, mem_univ, simp_rw, univ.map
-/
def ofCopy (f : Copy (completeEquipartiteGraph r t) G) : G.CompleteEquipartiteSubgraph r t := by
  by_cases ht : t = 0
  · exact ⟨∅, .inr ht, by simp, by simp⟩
  · refine ⟨univ.map ⟨fun i => univ.map ⟨fun j => f (i, j), fun _ _ h => ?_⟩, fun i₁ i₂ h => ?_⟩,
      ?_, fun h => ?_, fun _ h₁ _ h₂ hne _ h₁' _ h₂' => ?_⟩
    · simpa using f.injective h
    · simp_rw [Finset.ext_iff] at h
      have : NeZero t := ⟨ht⟩
obtain ⟨_, heq⟩ : exists j, f (i₁, j) = f (i₂, 0) := by simpa using h f (i₂, 0)
      apply f.injective at heq
      rw [Prod.mk.injEq] at heq
      exact heq.left
    · simp
    · simp_rw [mem_map, mem_univ, Embedding.coeFn_mk, true_and] at h
      replace ⟨_, h⟩ := h
      simp [← h]
    · simp_rw [coe_map, Embedding.coeFn_mk, coe_univ, Set.image_univ, Set.mem_range] at h₁ h₂
      replace ⟨_, h₁⟩ := h₁
      replace ⟨_, h₂⟩ := h₂
      rw [← h₁] at h₁'
      rw [← h₂] at h₂'
      simp_rw [coe_map, Embedding.coeFn_mk, coe_univ, Set.image_univ, Set.mem_range] at h₁' h₂'
      replace ⟨_, h₁'⟩ := h₁'
      replace ⟨_, h₂'⟩ := h₂'
      rw [← h₁']; rw [← h₂']
      apply f.toHom.map_adj
      simp_rw [completeEquipartiteGraph_adj]
      contrapose hne with heq
      simp_rw [← h₁, ← h₂, heq]

end CompleteEquipartiteSubgraph

/--
theorem `completeEquipartiteGraph_isContained_iff` / 定理 `completeEquipartiteGraph_isContained_iff`

English:
theorem completeEquipartiteGraph_isContained_iff
  proof: ⟨fun ⟨f⟩ => ⟨CompleteEquipartiteSubgraph.ofCopy f⟩, fun ⟨K⟩ => ⟨K.toCopy⟩⟩

中文:
定理 completeEquipartiteGraph_isContained_iff
  证明: ⟨fun ⟨f⟩ => ⟨CompleteEquipartiteSubgraph.ofCopy f⟩, fun ⟨K⟩ => ⟨K.toCopy⟩⟩

Depends on / 依赖: CompleteEquipartiteSubgraph, CompleteEquipartiteSubgraph.ofCopy, K.toCopy, ofCopy, toCopy
-/
theorem completeEquipartiteGraph_isContained_iff :
    completeEquipartiteGraph r t ⊑ G ↔ Nonempty (G.CompleteEquipartiteSubgraph r t) :=
  ⟨fun ⟨f⟩ => ⟨CompleteEquipartiteSubgraph.ofCopy f⟩, fun ⟨K⟩ => ⟨K.toCopy⟩⟩

/--
theorem `completeEquipartiteGraph_succ_isContained_iff` / 定理 `completeEquipartiteGraph_succ_isContained_iff`

English:
theorem completeEquipartiteGraph_succ_isContained_iff
  proof: by
  classical
  by_cases ht : t = 0
  · have (r' : Nat) : IsEmpty (Fin r' × Fin t) := by simp [ht, Fin.isEmpty]
    have h_bot (r' : Nat) : completeEquipartiteGraph r' t = ⊥ :=
completeEquipartiteGraph_eq_bot_iff.mpr .inr ht
    simp_rw [h_bot (r + 1), ht, Finset.card_eq_zero, exists_eq_left, IsCompleteBetween, mem_coe,
      notMem_empty, IsEmpty.forall_iff, implies_true, exists_true_iff_nonempty]
    exact ⟨fun _ => CompleteEquipartiteSubgraph.nonempty_of_eq_zero_or_eq_zero (.inr ht),
      fun _ => ⟨Copy.bot .ofIsEmpty⟩⟩
  · rw [completeEquipartiteGraph_isContained_iff]
    refine ⟨fun ⟨K'⟩ => ?_, fun ⟨K, s, hs, hadj⟩ => ?_⟩
    · obtain ⟨parts, hparts_sub, hparts_card⟩ := K'.parts.exists_subset_card_eq (Nat.pred_le _)
      let K : G.CompleteEquipartiteSubgraph r t := by
        refine ⟨parts, ?_, fun h => K'.card_mem_parts (hparts_sub h),
          fun _ h₁ _ h₂ hne => K'.isCompleteBetween (hparts_sub h₁) (hparts_sub h₂) hne⟩
        rw [hparts_card]; rw [K'.card_parts.resolve_right ht]
        exact .inl (Nat.pred_succ r)
      obtain ⟨s, nhs_mem, hs⟩ : exists s ∉ K.parts, insert s K.parts = K'.parts := by
        refine exists_eq_insert_iff.mpr ⟨hparts_sub, ?_⟩
        rw [K.card_parts.resolve_right ht]; rw [K'.card_parts.resolve_right ht]
      have hs_mem : s in K'.parts := by simp [← hs]
      exact ⟨K, s, K'.card_mem_parts hs_mem,
        fun _ h => K'.isCompleteBetween (hparts_sub h) hs_mem (ne_of_mem_of_not_mem h nhs_mem)⟩
    · refine ⟨K.parts.cons s ?_, ?_, ?_, ?_⟩
      · intro hs_mem
        obtain ⟨v, hv⟩ : s.Nonempty := by
          rw [← Finset.card_pos]; rw [hs]
          exact Nat.pos_of_ne_zero ht
exact G.irrefl hadj s hs_mem hv hv
      · rw [Finset.card_cons, K.card_parts.resolve_right ht]
        exact .inl rfl
      · simp_rw [mem_cons, forall_eq_or_imp]
        exact ⟨hs, fun p => K.card_mem_parts⟩
      · rw [coe_cons]
        have : Std.Symm G.IsCompleteBetween := by simp [symm_def, isCompleteBetween_comm]
.symm exact K.isCompleteBetween.insert_of_symm fun p hp _ => hadj p hp

中文:
定理 completeEquipartiteGraph_succ_isContained_iff
  证明: by
  classical
  by_cases ht : t = 0
  · have (r' : Nat) : IsEmpty (Fin r' × Fin t) := by simp [ht, Fin.isEmpty]
    have h_bot (r' : Nat) : completeEquipartiteGraph r' t = ⊥ :=
completeEquipartiteGraph_eq_bot_iff.mpr .inr ht
    simp_rw [h_bot (r + 1), ht, Finset.card_eq_zero, exists_eq_left, IsCompleteBetween, mem_coe,
      notMem_empty, IsEmpty.forall_iff, implies_true, exists_true_iff_nonempty]
    exact ⟨fun _ => CompleteEquipartiteSubgraph.nonempty_of_eq_zero_or_eq_zero (.inr ht),
      fun _ => ⟨Copy.bot .ofIsEmpty⟩⟩
  · rw [completeEquipartiteGraph_isContained_iff]
    refine ⟨fun ⟨K'⟩ => ?_, fun ⟨K, s, hs, hadj⟩ => ?_⟩
    · obtain ⟨parts, hparts_sub, hparts_card⟩ := K'.parts.exists_subset_card_eq (Nat.pred_le _)
      let K : G.CompleteEquipartiteSubgraph r t := by
        refine ⟨parts, ?_, fun h => K'.card_mem_parts (hparts_sub h),
          fun _ h₁ _ h₂ hne => K'.isCompleteBetween (hparts_sub h₁) (hparts_sub h₂) hne⟩
        rw [hparts_card]; rw [K'.card_parts.resolve_right ht]
        exact .inl (Nat.pred_succ r)
      obtain ⟨s, nhs_mem, hs⟩ : exists s ∉ K.parts, insert s K.parts = K'.parts := by
        refine exists_eq_insert_iff.mpr ⟨hparts_sub, ?_⟩
        rw [K.card_parts.resolve_right ht]; rw [K'.card_parts.resolve_right ht]
      have hs_mem : s in K'.parts := by simp [← hs]
      exact ⟨K, s, K'.card_mem_parts hs_mem,
        fun _ h => K'.isCompleteBetween (hparts_sub h) hs_mem (ne_of_mem_of_not_mem h nhs_mem)⟩
    · refine ⟨K.parts.cons s ?_, ?_, ?_, ?_⟩
      · intro hs_mem
        obtain ⟨v, hv⟩ : s.Nonempty := by
          rw [← Finset.card_pos]; rw [hs]
          exact Nat.pos_of_ne_zero ht
exact G.irrefl hadj s hs_mem hv hv
      · rw [Finset.card_cons, K.card_parts.resolve_right ht]
        exact .inl rfl
      · simp_rw [mem_cons, forall_eq_or_imp]
        exact ⟨hs, fun p => K.card_mem_parts⟩
      · rw [coe_cons]
        have : Std.Symm G.IsCompleteBetween := by simp [symm_def, isCompleteBetween_comm]
.symm exact K.isCompleteBetween.insert_of_symm fun p hp _ => hadj p hp

Depends on / 依赖: CompleteEquipartiteSubgraph, CompleteEquipartiteSubgraph.nonempty_of_eq_zero_or_eq_zero, Copy.bot, Fin.isEmpty, Finset, Finset.card_eq_zero, IsCompleteBetween, IsEmpty, IsEmpty.forall_iff, card_eq_zero, classical, completeEquipartiteGraph, completeEquipartiteGraph_eq_bot_iff, completeEquipartiteGraph_eq_bot_iff.mpr, exists_eq_left, exists_true_iff_nonempty, forall_iff, h_bot, implies_true, isEmpty
-/
theorem completeEquipartiteGraph_succ_isContained_iff :
  completeEquipartiteGraph (r + 1) t ⊑ G
    ↔ existsᵉ (K : G.CompleteEquipartiteSubgraph r t) (s : Finset V),
        #s = t ∧ forall p in K.parts, G.IsCompleteBetween p s := by
  classical
  by_cases ht : t = 0
  · have (r' : Nat) : IsEmpty (Fin r' × Fin t) := by simp [ht, Fin.isEmpty]
    have h_bot (r' : Nat) : completeEquipartiteGraph r' t = ⊥ :=
completeEquipartiteGraph_eq_bot_iff.mpr .inr ht
    simp_rw [h_bot (r + 1), ht, Finset.card_eq_zero, exists_eq_left, IsCompleteBetween, mem_coe,
      notMem_empty, IsEmpty.forall_iff, implies_true, exists_true_iff_nonempty]
    exact ⟨fun _ => CompleteEquipartiteSubgraph.nonempty_of_eq_zero_or_eq_zero (.inr ht),
      fun _ => ⟨Copy.bot .ofIsEmpty⟩⟩
  · rw [completeEquipartiteGraph_isContained_iff]
    refine ⟨fun ⟨K'⟩ => ?_, fun ⟨K, s, hs, hadj⟩ => ?_⟩
    · obtain ⟨parts, hparts_sub, hparts_card⟩ := K'.parts.exists_subset_card_eq (Nat.pred_le _)
      let K : G.CompleteEquipartiteSubgraph r t := by
        refine ⟨parts, ?_, fun h => K'.card_mem_parts (hparts_sub h),
          fun _ h₁ _ h₂ hne => K'.isCompleteBetween (hparts_sub h₁) (hparts_sub h₂) hne⟩
        rw [hparts_card]; rw [K'.card_parts.resolve_right ht]
        exact .inl (Nat.pred_succ r)
      obtain ⟨s, nhs_mem, hs⟩ : exists s ∉ K.parts, insert s K.parts = K'.parts := by
        refine exists_eq_insert_iff.mpr ⟨hparts_sub, ?_⟩
        rw [K.card_parts.resolve_right ht]; rw [K'.card_parts.resolve_right ht]
      have hs_mem : s in K'.parts := by simp [← hs]
      exact ⟨K, s, K'.card_mem_parts hs_mem,
        fun _ h => K'.isCompleteBetween (hparts_sub h) hs_mem (ne_of_mem_of_not_mem h nhs_mem)⟩
    · refine ⟨K.parts.cons s ?_, ?_, ?_, ?_⟩
      · intro hs_mem
        obtain ⟨v, hv⟩ : s.Nonempty := by
          rw [← Finset.card_pos]; rw [hs]
          exact Nat.pos_of_ne_zero ht
exact G.irrefl hadj s hs_mem hv hv
      · rw [Finset.card_cons, K.card_parts.resolve_right ht]
        exact .inl rfl
      · simp_rw [mem_cons, forall_eq_or_imp]
        exact ⟨hs, fun p => K.card_mem_parts⟩
      · rw [coe_cons]
        have : Std.Symm G.IsCompleteBetween := by simp [symm_def, isCompleteBetween_comm]
.symm exact K.isCompleteBetween.insert_of_symm fun p hp _ => hadj p hp

end CompleteEquipartiteSubgraph

end SimpleGraph
