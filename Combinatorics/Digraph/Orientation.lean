/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!

# Graph Orientation

This module introduces conversion operations between `Digraph`s and `SimpleGraph`s, by forgetting
the edge orientations of `Digraph`.

## Main Definitions

- `Digraph.toSimpleGraphInclusive`: Converts a `Digraph` to a `SimpleGraph` by creating an
  undirected edge if either orientation exists in the digraph.
- `Digraph.toSimpleGraphStrict`: Converts a `Digraph` to a `SimpleGraph` by creating an undirected
  edge only if both orientations exist in the digraph.

## TODO

- Show that there is an isomorphism between loopless complete digraphs and oriented graphs.
- Define more ways to orient a `SimpleGraph`.
- Provide lemmas on how `toSimpleGraphInclusive` and `toSimpleGraphStrict` relate to other lattice
  structures on `SimpleGraph`s and `Digraph`s.

## Tags

digraph, simple graph, oriented graphs
-/

@[expose] public section

variable {V : Type*}

namespace Digraph

section toSimpleGraph

/-! ### Orientation-forgetting maps on digraphs -/

/--
Definition of `toSimpleGraphInclusive` / `toSimpleGraphInclusive` 的定义

English:
definition toSimpleGraphInclusive
  signature: (G : Digraph V)
  body: SimpleGraph.fromRel G.Adj

中文:
定义 toSimpleGraphInclusive
  签名: (G : Digraph V)
  定义体: SimpleGraph.fromRel G.Adj

Depends on / 依赖: G.Adj, SimpleGraph, SimpleGraph.fromRel, fromRel
-/
def toSimpleGraphInclusive (G : Digraph V) : SimpleGraph V := SimpleGraph.fromRel G.Adj

/--
Definition of `toSimpleGraphStrict` / `toSimpleGraphStrict` 的定义

English:
definition toSimpleGraphStrict
  signature: (G : Digraph V)
  body: v != w ∧ G.Adj v w ∧ G.Adj w v

中文:
定义 toSimpleGraphStrict
  签名: (G : Digraph V)
  定义体: v != w ∧ G.Adj v w ∧ G.Adj w v

Depends on / 依赖: G.Adj
-/
def toSimpleGraphStrict (G : Digraph V) : SimpleGraph V where
  Adj v w := v != w ∧ G.Adj v w ∧ G.Adj w v

/--
lemma `toSimpleGraphStrict_subgraph_toSimpleGraphInclusive` / 引理 `toSimpleGraphStrict_subgraph_toSimpleGraphInclusive`

English:
lemma toSimpleGraphStrict_subgraph_toSimpleGraphInclusive
  given: (G : Digraph V)
  proof: fun _ _ h => ⟨h.1, Or.inl h.2.1⟩

@[gcongr, mono]

中文:
引理 toSimpleGraphStrict_subgraph_toSimpleGraphInclusive
  条件: (G : Digraph V)
  证明: fun _ _ h => ⟨h.1, Or.inl h.2.1⟩

@[gcongr, mono]

Depends on / 依赖: Or.inl
-/
lemma toSimpleGraphStrict_subgraph_toSimpleGraphInclusive (G : Digraph V) :
    G.toSimpleGraphStrict <= G.toSimpleGraphInclusive :=
  fun _ _ h => ⟨h.1, Or.inl h.2.1⟩

@[gcongr, mono]
/--
lemma `toSimpleGraphInclusive_mono` / 引理 `toSimpleGraphInclusive_mono`

English:
lemma toSimpleGraphInclusive_mono
  statement: Monotone (toSimpleGraphInclusive : _ -> SimpleGraph V)
  proof: fun _ _ h₁ _ _ h₂ => ⟨h₂.1, h₂.2.imp (@h₁ _ _) (@h₁ _ _)⟩

@[gcongr, mono]

中文:
引理 toSimpleGraphInclusive_mono
  结论: Monotone (toSimpleGraphInclusive : _ -> SimpleGraph V)
  证明: fun _ _ h₁ _ _ h₂ => ⟨h₂.1, h₂.2.imp (@h₁ _ _) (@h₁ _ _)⟩

@[gcongr, mono]
-/
lemma toSimpleGraphInclusive_mono : Monotone (toSimpleGraphInclusive : _ -> SimpleGraph V) :=
  fun _ _ h₁ _ _ h₂ => ⟨h₂.1, h₂.2.imp (@h₁ _ _) (@h₁ _ _)⟩

@[gcongr, mono]
/--
lemma `toSimpleGraphStrict_mono` / 引理 `toSimpleGraphStrict_mono`

English:
lemma toSimpleGraphStrict_mono
  statement: Monotone (toSimpleGraphStrict : _ -> SimpleGraph V)
  proof: fun _ _ h₁ _ _ h₂ => ⟨h₂.1, h₁ h₂.2.1, h₁ h₂.2.2⟩

@[simp]

中文:
引理 toSimpleGraphStrict_mono
  结论: Monotone (toSimpleGraphStrict : _ -> SimpleGraph V)
  证明: fun _ _ h₁ _ _ h₂ => ⟨h₂.1, h₁ h₂.2.1, h₁ h₂.2.2⟩

@[simp]
-/
lemma toSimpleGraphStrict_mono : Monotone (toSimpleGraphStrict : _ -> SimpleGraph V) :=
  fun _ _ h₁ _ _ h₂ => ⟨h₂.1, h₁ h₂.2.1, h₁ h₂.2.2⟩

@[simp]
/--
lemma `toSimpleGraphInclusive_top` / 引理 `toSimpleGraphInclusive_top`

English:
lemma toSimpleGraphInclusive_top
  statement: (⊤ : Digraph V).toSimpleGraphInclusive = ⊤
  proof: by
  ext; exact ⟨And.left, fun h => ⟨h.ne, Or.inl trivial⟩⟩

@[simp]

中文:
引理 toSimpleGraphInclusive_top
  结论: (⊤ : Digraph V).toSimpleGraphInclusive = ⊤
  证明: by
  ext; exact ⟨And.left, fun h => ⟨h.ne, Or.inl trivial⟩⟩

@[simp]

Depends on / 依赖: And.left, Or.inl, h.ne
-/
lemma toSimpleGraphInclusive_top : (⊤ : Digraph V).toSimpleGraphInclusive = ⊤ := by
  ext; exact ⟨And.left, fun h => ⟨h.ne, Or.inl trivial⟩⟩

@[simp]
/--
lemma `toSimpleGraphStrict_top` / 引理 `toSimpleGraphStrict_top`

English:
lemma toSimpleGraphStrict_top
  statement: (⊤ : Digraph V).toSimpleGraphStrict = ⊤
  proof: by
  ext; exact ⟨And.left, fun h => ⟨h.ne, trivial, trivial⟩⟩

@[simp]

中文:
引理 toSimpleGraphStrict_top
  结论: (⊤ : Digraph V).toSimpleGraphStrict = ⊤
  证明: by
  ext; exact ⟨And.left, fun h => ⟨h.ne, trivial, trivial⟩⟩

@[simp]

Depends on / 依赖: And.left, h.ne
-/
lemma toSimpleGraphStrict_top : (⊤ : Digraph V).toSimpleGraphStrict = ⊤ := by
  ext; exact ⟨And.left, fun h => ⟨h.ne, trivial, trivial⟩⟩

@[simp]
/--
lemma `toSimpleGraphInclusive_bot` / 引理 `toSimpleGraphInclusive_bot`

English:
lemma toSimpleGraphInclusive_bot
  statement: (⊥ : Digraph V).toSimpleGraphInclusive = ⊥
  proof: by
  ext; exact ⟨fun ⟨_, h⟩ => by tauto, False.elim⟩

@[simp]

中文:
引理 toSimpleGraphInclusive_bot
  结论: (⊥ : Digraph V).toSimpleGraphInclusive = ⊥
  证明: by
  ext; exact ⟨fun ⟨_, h⟩ => by tauto, False.elim⟩

@[simp]

Depends on / 依赖: False.elim
-/
lemma toSimpleGraphInclusive_bot : (⊥ : Digraph V).toSimpleGraphInclusive = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ => by tauto, False.elim⟩

@[simp]
/--
lemma `toSimpleGraphStrict_bot` / 引理 `toSimpleGraphStrict_bot`

English:
lemma toSimpleGraphStrict_bot
  statement: (⊥ : Digraph V).toSimpleGraphStrict = ⊥
  proof: by
  ext; exact ⟨fun ⟨_, h⟩ => by tauto, False.elim⟩

中文:
引理 toSimpleGraphStrict_bot
  结论: (⊥ : Digraph V).toSimpleGraphStrict = ⊥
  证明: by
  ext; exact ⟨fun ⟨_, h⟩ => by tauto, False.elim⟩

Depends on / 依赖: False.elim
-/
lemma toSimpleGraphStrict_bot : (⊥ : Digraph V).toSimpleGraphStrict = ⊥ := by
  ext; exact ⟨fun ⟨_, h⟩ => by tauto, False.elim⟩

end toSimpleGraph

end Digraph
