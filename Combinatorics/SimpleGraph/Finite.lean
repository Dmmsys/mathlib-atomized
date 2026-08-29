/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Sym.Card
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Definitions for finite and locally finite graphs

This file defines finite versions of `edgeSet`, `neighborSet` and `incidenceSet` and proves some
of their basic properties. It also defines the notion of a locally finite graph, which is one
whose vertices have finite degree.

The design for finiteness is that each definition takes the smallest finiteness assumption
necessary. For example, `SimpleGraph.neighborFinset v` only requires that `v` have
finitely many neighbors.

## Main definitions

* `SimpleGraph.edgeFinset` is the `Finset` of edges in a graph, if `edgeSet` is finite
* `SimpleGraph.neighborFinset` is the `Finset` of vertices adjacent to a given vertex,
  if `neighborSet` is finite
* `SimpleGraph.incidenceFinset` is the `Finset` of edges containing a given vertex,
  if `incidenceSet` is finite

## Naming conventions

If the vertex type of a graph is finite, we refer to its cardinality as `CardVerts`
or `card_verts`.

## Implementation notes

* A locally finite graph is one with instances `Π v, Fintype (G.neighborSet v)`.
* Given instances `DecidableRel G.Adj` and `Fintype V`, then the graph
  is locally finite, too.
-/

@[expose] public section


open Finset Function

namespace SimpleGraph

variable {V : Type*} (G H : SimpleGraph V) {e : Sym2 V}

section EdgeFinset

variable {G₁ G₂ : SimpleGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

/--
Definition of `edgeFinset` / `edgeFinset` 的定义

English:
definition edgeFinset
  signature: : Finset (Sym2 V)
  body: Set.toFinset G.edgeSet

@[simp, norm_cast]

中文:
定义 edgeFinset
  签名: : Finset (Sym2 V)
  定义体: Set.toFinset G.edgeSet

@[simp, norm_cast]

Depends on / 依赖: G.edgeSet, Set.toFinset, edgeSet, toFinset
-/
def edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet

@[simp, norm_cast]
/--
theorem `coe_edgeFinset` / 定理 `coe_edgeFinset`

English:
theorem coe_edgeFinset
  statement: (G.edgeFinset : Set (Sym2 V)) = G.edgeSet
  proof: Set.coe_toFinset _

中文:
定理 coe_edgeFinset
  结论: (G.edgeFinset : Set (Sym2 V)) = G.edgeSet
  证明: Set.coe_toFinset _

Depends on / 依赖: Set.coe_toFinset, coe_toFinset
-/
theorem coe_edgeFinset : (G.edgeFinset : Set (Sym2 V)) = G.edgeSet :=
  Set.coe_toFinset _

variable {G}

@[simp]
/--
theorem `mem_edgeFinset` / 定理 `mem_edgeFinset`

English:
theorem mem_edgeFinset
  statement: e in G.edgeFinset ↔ e in G.edgeSet
  proof: Set.mem_toFinset

中文:
定理 mem_edgeFinset
  结论: e in G.edgeFinset ↔ e in G.edgeSet
  证明: Set.mem_toFinset

Depends on / 依赖: Set.mem_toFinset, mem_toFinset
-/
theorem mem_edgeFinset : e in G.edgeFinset ↔ e in G.edgeSet :=
  Set.mem_toFinset

/--
theorem `not_isDiag_of_mem_edgeFinset` / 定理 `not_isDiag_of_mem_edgeFinset`

English:
theorem not_isDiag_of_mem_edgeFinset
  statement: e in G.edgeFinset -> ¬e.IsDiag
  proof: not_isDiag_of_mem_edgeSet _ ∘ mem_edgeFinset.1

中文:
定理 not_isDiag_of_mem_edgeFinset
  结论: e in G.edgeFinset -> ¬e.IsDiag
  证明: not_isDiag_of_mem_edgeSet _ ∘ mem_edgeFinset.1

Depends on / 依赖: mem_edgeFinset, not_isDiag_of_mem_edgeSet
-/
theorem not_isDiag_of_mem_edgeFinset : e in G.edgeFinset -> ¬e.IsDiag :=
  not_isDiag_of_mem_edgeSet _ ∘ mem_edgeFinset.1

/--
theorem `card_toFinset_mem_edgeFinset` / 定理 `card_toFinset_mem_edgeFinset`

English:
theorem card_toFinset_mem_edgeFinset
  given: [DecidableEq V] (e : G.edgeFinset)
  proof: Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeFinset e.prop)

@[simp]

中文:
定理 card_toFinset_mem_edgeFinset
  条件: [DecidableEq V] (e : G.edgeFinset)
  证明: Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeFinset e.prop)

@[simp]

Depends on / 依赖: G.not_isDiag_of_mem_edgeFinset, Sym2.card_toFinset_of_not_isDiag, card_toFinset_of_not_isDiag, e.prop, e.val, not_isDiag_of_mem_edgeFinset
-/
theorem card_toFinset_mem_edgeFinset [DecidableEq V] (e : G.edgeFinset) :
    (e : Sym2 V).toFinset.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeFinset e.prop)

@[simp]
/--
theorem `edgeFinset_inj` / 定理 `edgeFinset_inj`

English:
theorem edgeFinset_inj
  statement: G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂
  proof: by simp [edgeFinset]

@[simp]

中文:
定理 edgeFinset_inj
  结论: G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂
  证明: by simp [edgeFinset]

@[simp]

Depends on / 依赖: edgeFinset
-/
theorem edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂ := by simp [edgeFinset]

@[simp]
/--
theorem `edgeFinset_subset_edgeFinset` / 定理 `edgeFinset_subset_edgeFinset`

English:
theorem edgeFinset_subset_edgeFinset
  statement: G₁.edgeFinset subseteq G₂.edgeFinset ↔ G₁ <= G₂
  proof: by
  simp [edgeFinset]

@[simp]

中文:
定理 edgeFinset_subset_edgeFinset
  结论: G₁.edgeFinset subseteq G₂.edgeFinset ↔ G₁ <= G₂
  证明: by
  simp [edgeFinset]

@[simp]

Depends on / 依赖: edgeFinset
-/
theorem edgeFinset_subset_edgeFinset : G₁.edgeFinset subseteq G₂.edgeFinset ↔ G₁ <= G₂ := by
  simp [edgeFinset]

@[simp]
/--
theorem `edgeFinset_ssubset_edgeFinset` / 定理 `edgeFinset_ssubset_edgeFinset`

English:
theorem edgeFinset_ssubset_edgeFinset
  statement: G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂
  proof: by
  simp [edgeFinset]

@[mono, gcongr] alias ⟨_, edgeFinset_mono⟩ := edgeFinset_subset_edgeFinset

@[mono, gcongr]
alias ⟨_, edgeFinset_strict_mono⟩ := edgeFinset_ssubset_edgeFinset

@[simp]

中文:
定理 edgeFinset_ssubset_edgeFinset
  结论: G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂
  证明: by
  simp [edgeFinset]

@[mono, gcongr] alias ⟨_, edgeFinset_mono⟩ := edgeFinset_subset_edgeFinset

@[mono, gcongr]
alias ⟨_, edgeFinset_strict_mono⟩ := edgeFinset_ssubset_edgeFinset

@[simp]

Depends on / 依赖: edgeFinset
-/
theorem edgeFinset_ssubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂ := by
  simp [edgeFinset]

@[mono, gcongr] alias ⟨_, edgeFinset_mono⟩ := edgeFinset_subset_edgeFinset

@[mono, gcongr]
alias ⟨_, edgeFinset_strict_mono⟩ := edgeFinset_ssubset_edgeFinset

@[simp]
/--
theorem `edgeFinset_bot` / 定理 `edgeFinset_bot`

English:
theorem edgeFinset_bot
  statement: (⊥ : SimpleGraph V).edgeFinset = ∅
  proof: by simp [edgeFinset]

@[simp]

中文:
定理 edgeFinset_bot
  结论: (⊥ : SimpleGraph V).edgeFinset = ∅
  证明: by simp [edgeFinset]

@[simp]

Depends on / 依赖: edgeFinset
-/
theorem edgeFinset_bot : (⊥ : SimpleGraph V).edgeFinset = ∅ := by simp [edgeFinset]

@[simp]
/--
theorem `edgeFinset_sup` / 定理 `edgeFinset_sup`

English:
theorem edgeFinset_sup
  given: [Fintype (edgeSet (G₁ ⊔ G₂))] [DecidableEq V]
  proof: by simp [edgeFinset]

@[simp]

中文:
定理 edgeFinset_sup
  条件: [Fintype (edgeSet (G₁ ⊔ G₂))] [DecidableEq V]
  证明: by simp [edgeFinset]

@[simp]

Depends on / 依赖: edgeFinset
-/
theorem edgeFinset_sup [Fintype (edgeSet (G₁ ⊔ G₂))] [DecidableEq V] :
    (G₁ ⊔ G₂).edgeFinset = G₁.edgeFinset union G₂.edgeFinset := by simp [edgeFinset]

@[simp]
/--
theorem `edgeFinset_inf` / 定理 `edgeFinset_inf`

English:
theorem edgeFinset_inf
  given: [Fintype (G₁ ⊓ G₂).edgeSet] [DecidableEq V]
  proof: by
  simp [edgeFinset]

@[simp]

中文:
定理 edgeFinset_inf
  条件: [Fintype (G₁ ⊓ G₂).edgeSet] [DecidableEq V]
  证明: by
  simp [edgeFinset]

@[simp]

Depends on / 依赖: edgeFinset
-/
theorem edgeFinset_inf [Fintype (G₁ ⊓ G₂).edgeSet] [DecidableEq V] :
    (G₁ ⊓ G₂).edgeFinset = G₁.edgeFinset inter G₂.edgeFinset := by
  simp [edgeFinset]

@[simp]
/--
theorem `edgeFinset_sdiff` / 定理 `edgeFinset_sdiff`

English:
theorem edgeFinset_sdiff
  given: [DecidableEq V]
  proof: by simp [edgeFinset]

@[simp]

中文:
定理 edgeFinset_sdiff
  条件: [DecidableEq V]
  证明: by simp [edgeFinset]

@[simp]

Depends on / 依赖: edgeFinset
-/
theorem edgeFinset_sdiff [DecidableEq V] :
    (G₁ \ G₂).edgeFinset = G₁.edgeFinset \ G₂.edgeFinset := by simp [edgeFinset]

@[simp]
/--
lemma `disjoint_edgeFinset` / 引理 `disjoint_edgeFinset`

English:
lemma disjoint_edgeFinset
  statement: Disjoint G₁.edgeFinset G₂.edgeFinset ↔ Disjoint G₁ G₂
  proof: by
  simp_rw [← Finset.disjoint_coe, coe_edgeFinset, disjoint_edgeSet]

@[simp]

中文:
引理 disjoint_edgeFinset
  结论: Disjoint G₁.edgeFinset G₂.edgeFinset ↔ Disjoint G₁ G₂
  证明: by
  simp_rw [← Finset.disjoint_coe, coe_edgeFinset, disjoint_edgeSet]

@[simp]

Depends on / 依赖: Finset, Finset.disjoint_coe, coe_edgeFinset, disjoint_coe, disjoint_edgeSet, simp_rw
-/
lemma disjoint_edgeFinset : Disjoint G₁.edgeFinset G₂.edgeFinset ↔ Disjoint G₁ G₂ := by
  simp_rw [← Finset.disjoint_coe, coe_edgeFinset, disjoint_edgeSet]

@[simp]
/--
lemma `edgeFinset_eq_empty` / 引理 `edgeFinset_eq_empty`

English:
lemma edgeFinset_eq_empty
  statement: G.edgeFinset = ∅ ↔ G = ⊥
  proof: by
  rw [← edgeFinset_bot]; rw [edgeFinset_inj]

@[simp]

中文:
引理 edgeFinset_eq_empty
  结论: G.edgeFinset = ∅ ↔ G = ⊥
  证明: by
  rw [← edgeFinset_bot]; rw [edgeFinset_inj]

@[simp]

Depends on / 依赖: edgeFinset_bot, edgeFinset_inj
-/
lemma edgeFinset_eq_empty : G.edgeFinset = ∅ ↔ G = ⊥ := by
  rw [← edgeFinset_bot]; rw [edgeFinset_inj]

@[simp]
/--
lemma `edgeFinset_nonempty` / 引理 `edgeFinset_nonempty`

English:
lemma edgeFinset_nonempty
  statement: G.edgeFinset.Nonempty ↔ G != ⊥
  proof: by
  rw [Finset.nonempty_iff_ne_empty]; rw [edgeFinset_eq_empty.ne]

中文:
引理 edgeFinset_nonempty
  结论: G.edgeFinset.Nonempty ↔ G != ⊥
  证明: by
  rw [Finset.nonempty_iff_ne_empty]; rw [edgeFinset_eq_empty.ne]

Depends on / 依赖: Finset, Finset.nonempty_iff_ne_empty, edgeFinset_eq_empty, edgeFinset_eq_empty.ne, nonempty_iff_ne_empty
-/
lemma edgeFinset_nonempty : G.edgeFinset.Nonempty ↔ G != ⊥ := by
  rw [Finset.nonempty_iff_ne_empty]; rw [edgeFinset_eq_empty.ne]

/--
theorem `edgeFinset_card` / 定理 `edgeFinset_card`

English:
theorem edgeFinset_card
  statement: #G.edgeFinset = Fintype.card G.edgeSet
  proof: Set.toFinset_card _

中文:
定理 edgeFinset_card
  结论: #G.edgeFinset = Fintype.card G.edgeSet
  证明: Set.toFinset_card _

Depends on / 依赖: Set.toFinset_card, toFinset_card
-/
theorem edgeFinset_card : #G.edgeFinset = Fintype.card G.edgeSet :=
  Set.toFinset_card _

/--
theorem `card_edgeSet` / 定理 `card_edgeSet`

English:
theorem card_edgeSet
  statement: Fintype.card G.edgeSet = #G.edgeFinset
  proof: .symm Set.toFinset_card _

中文:
定理 card_edgeSet
  结论: Fintype.card G.edgeSet = #G.edgeFinset
  证明: .symm Set.toFinset_card _

Depends on / 依赖: Set.toFinset_card, toFinset_card
-/
theorem card_edgeSet : Fintype.card G.edgeSet = #G.edgeFinset :=
.symm Set.toFinset_card _

/--
theorem `edgeSet_univ_card` / 定理 `edgeSet_univ_card`

English:
theorem edgeSet_univ_card
  statement: #(univ : Finset G.edgeSet) = #G.edgeFinset
  proof: by
  simp [card_edgeSet]

中文:
定理 edgeSet_univ_card
  结论: #(univ : Finset G.edgeSet) = #G.edgeFinset
  证明: by
  simp [card_edgeSet]

Depends on / 依赖: card_edgeSet
-/
theorem edgeSet_univ_card : #(univ : Finset G.edgeSet) = #G.edgeFinset := by
  simp [card_edgeSet]

variable [Fintype V]

@[simp]
/--
theorem `edgeFinset_top` / 定理 `edgeFinset_top`

English:
theorem edgeFinset_top
  given: [DecidableEq V]
  proof: by simp [← coe_inj]

中文:
定理 edgeFinset_top
  条件: [DecidableEq V]
  证明: by simp [← coe_inj]

Depends on / 依赖: coe_inj
-/
theorem edgeFinset_top [DecidableEq V] :
    (⊤ : SimpleGraph V).edgeFinset = Sym2.diagSetᶜ.toFinset := by simp [← coe_inj]

/--
theorem `card_edgeFinset_top_eq_card_choose_two` / 定理 `card_edgeFinset_top_eq_card_choose_two`

English:
theorem card_edgeFinset_top_eq_card_choose_two
  given: [DecidableEq V]
  proof: by
  simp_rw [edgeFinset, Set.toFinset_card, edgeSet_top, ← Sym2.card_diagSet_compl]

中文:
定理 card_edgeFinset_top_eq_card_choose_two
  条件: [DecidableEq V]
  证明: by
  simp_rw [edgeFinset, Set.toFinset_card, edgeSet_top, ← Sym2.card_diagSet_compl]

Depends on / 依赖: Set.toFinset_card, Sym2.card_diagSet_compl, card_diagSet_compl, edgeFinset, edgeSet_top, simp_rw, toFinset_card
-/
theorem card_edgeFinset_top_eq_card_choose_two [DecidableEq V] :
    #(⊤ : SimpleGraph V).edgeFinset = (Fintype.card V).choose 2 := by
  simp_rw [edgeFinset, Set.toFinset_card, edgeSet_top, ← Sym2.card_diagSet_compl]

/--
theorem `card_edgeFinset_le_card_choose_two` / 定理 `card_edgeFinset_le_card_choose_two`

English:
theorem card_edgeFinset_le_card_choose_two
  statement: #G.edgeFinset <= (Fintype.card V).choose 2
  proof: by
  classical
  rw [← card_edgeFinset_top_eq_card_choose_two]
  exact card_le_card (edgeFinset_mono le_top)

中文:
定理 card_edgeFinset_le_card_choose_two
  结论: #G.edgeFinset <= (Fintype.card V).choose 2
  证明: by
  classical
  rw [← card_edgeFinset_top_eq_card_choose_two]
  exact card_le_card (edgeFinset_mono le_top)

Depends on / 依赖: card_edgeFinset_top_eq_card_choose_two, card_le_card, classical, edgeFinset_mono, le_top
-/
theorem card_edgeFinset_le_card_choose_two : #G.edgeFinset <= (Fintype.card V).choose 2 := by
  classical
  rw [← card_edgeFinset_top_eq_card_choose_two]
  exact card_le_card (edgeFinset_mono le_top)

end EdgeFinset

section FiniteAt

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices. We denote this condition by
`Fintype (G.neighborSet v)`.

We define `G.neighborFinset v` to be the `Finset` version of `G.neighborSet v`.
Use `neighborFinset_eq_filter` to rewrite this definition as a `Finset.filter` expression.
-/

variable (v) [Fintype (G.neighborSet v)]

/--
Definition of `neighborFinset` / `neighborFinset` 的定义

English:
definition neighborFinset
  signature: : Finset V
  body: (G.neighborSet v).toFinset

中文:
定义 neighborFinset
  签名: : Finset V
  定义体: (G.neighborSet v).toFinset

Depends on / 依赖: G.neighborSet, neighborSet, toFinset
-/
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset

/--
theorem `neighborFinset_def` / 定理 `neighborFinset_def`

English:
theorem neighborFinset_def
  statement: G.neighborFinset v = (G.neighborSet v).toFinset
  proof: rfl

@[simp, norm_cast]

中文:
定理 neighborFinset_def
  结论: G.neighborFinset v = (G.neighborSet v).toFinset
  证明: rfl

@[simp, norm_cast]
-/
theorem neighborFinset_def : G.neighborFinset v = (G.neighborSet v).toFinset :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_neighborFinset` / 定理 `coe_neighborFinset`

English:
theorem coe_neighborFinset
  statement: (G.neighborFinset v : Set V) = G.neighborSet v
  proof: Set.coe_toFinset _

@[simp]

中文:
定理 coe_neighborFinset
  结论: (G.neighborFinset v : Set V) = G.neighborSet v
  证明: Set.coe_toFinset _

@[simp]

Depends on / 依赖: Set.coe_toFinset, coe_toFinset
-/
theorem coe_neighborFinset : (G.neighborFinset v : Set V) = G.neighborSet v :=
  Set.coe_toFinset _

@[simp]
/--
theorem `mem_neighborFinset` / 定理 `mem_neighborFinset`

English:
theorem mem_neighborFinset
  given: (w : V)
  statement: w in G.neighborFinset v ↔ G.Adj v w
  proof: Set.mem_toFinset

中文:
定理 mem_neighborFinset
  条件: (w : V)
  结论: w in G.neighborFinset v ↔ G.Adj v w
  证明: Set.mem_toFinset

Depends on / 依赖: Set.mem_toFinset, mem_toFinset
-/
theorem mem_neighborFinset (w : V) : w in G.neighborFinset v ↔ G.Adj v w :=
  Set.mem_toFinset

/--
theorem `notMem_neighborFinset_self` / 定理 `notMem_neighborFinset_self`

English:
theorem notMem_neighborFinset_self
  statement: v ∉ G.neighborFinset v
  proof: by simp

中文:
定理 notMem_neighborFinset_self
  结论: v ∉ G.neighborFinset v
  证明: by simp
-/
theorem notMem_neighborFinset_self : v ∉ G.neighborFinset v := by simp

/--
theorem `neighborFinset_disjoint_singleton` / 定理 `neighborFinset_disjoint_singleton`

English:
theorem neighborFinset_disjoint_singleton
  statement: Disjoint (G.neighborFinset v) {v}
  proof: Finset.disjoint_singleton_right.mpr notMem_neighborFinset_self _ _

中文:
定理 neighborFinset_disjoint_singleton
  结论: Disjoint (G.neighborFinset v) {v}
  证明: Finset.disjoint_singleton_right.mpr notMem_neighborFinset_self _ _

Depends on / 依赖: Finset, Finset.disjoint_singleton_right.mpr, disjoint_singleton_right, notMem_neighborFinset_self
-/
theorem neighborFinset_disjoint_singleton : Disjoint (G.neighborFinset v) {v} :=
Finset.disjoint_singleton_right.mpr notMem_neighborFinset_self _ _

/--
theorem `singleton_disjoint_neighborFinset` / 定理 `singleton_disjoint_neighborFinset`

English:
theorem singleton_disjoint_neighborFinset
  statement: Disjoint {v} (G.neighborFinset v)
  proof: Finset.disjoint_singleton_left.mpr notMem_neighborFinset_self _ _

中文:
定理 singleton_disjoint_neighborFinset
  结论: Disjoint {v} (G.neighborFinset v)
  证明: Finset.disjoint_singleton_left.mpr notMem_neighborFinset_self _ _

Depends on / 依赖: Finset, Finset.disjoint_singleton_left.mpr, disjoint_singleton_left, notMem_neighborFinset_self
-/
theorem singleton_disjoint_neighborFinset : Disjoint {v} (G.neighborFinset v) :=
Finset.disjoint_singleton_left.mpr notMem_neighborFinset_self _ _

/--
theorem `neighborFinset_bot` / 定理 `neighborFinset_bot`

English:
theorem neighborFinset_bot
  given: [Fintype ((⊥ : SimpleGraph V).neighborSet v)]
  proof: by
  ext; simp

@[simp]

中文:
定理 neighborFinset_bot
  条件: [Fintype ((⊥ : SimpleGraph V).neighborSet v)]
  证明: by
  ext; simp

@[simp]
-/
theorem neighborFinset_bot [Fintype ((⊥ : SimpleGraph V).neighborSet v)] :
    (⊥ : SimpleGraph V).neighborFinset v = ∅ := by
  ext; simp

@[simp]
/--
theorem `neighborFinset_top` / 定理 `neighborFinset_top`

English:
theorem neighborFinset_top
  given: [Fintype V] [DecidableEq V]
  proof: by
  simp [← Finset.coe_inj]

@[simp]

中文:
定理 neighborFinset_top
  条件: [Fintype V] [DecidableEq V]
  证明: by
  simp [← Finset.coe_inj]

@[simp]

Depends on / 依赖: Finset, Finset.coe_inj, coe_inj
-/
theorem neighborFinset_top [Fintype V] [DecidableEq V] :
    (⊤ : SimpleGraph V).neighborFinset v = {v}ᶜ := by
  simp [← Finset.coe_inj]

@[simp]
/--
theorem `neighborFinset_sup` / 定理 `neighborFinset_sup`

English:
theorem neighborFinset_sup
  statement: [DecidableEq V] {G₁ G₂ : SimpleGraph V}
  proof: by
  simp [← Finset.coe_inj]

@[simp]

中文:
定理 neighborFinset_sup
  结论: [DecidableEq V] {G₁ G₂ : SimpleGraph V}
  证明: by
  simp [← Finset.coe_inj]

@[simp]

Depends on / 依赖: Finset, Finset.coe_inj, coe_inj
-/
theorem neighborFinset_sup [DecidableEq V] {G₁ G₂ : SimpleGraph V}
    [Fintype ((G₁ ⊔ G₂).neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)] :
    (G₁ ⊔ G₂).neighborFinset v = G₁.neighborFinset v union G₂.neighborFinset v := by
  simp [← Finset.coe_inj]

@[simp]
/--
theorem `neighborFinset_inf` / 定理 `neighborFinset_inf`

English:
theorem neighborFinset_inf
  statement: [DecidableEq V] {G₁ G₂ : SimpleGraph V}
  proof: by
  simp [← Finset.coe_inj]

@[simp]

中文:
定理 neighborFinset_inf
  结论: [DecidableEq V] {G₁ G₂ : SimpleGraph V}
  证明: by
  simp [← Finset.coe_inj]

@[simp]

Depends on / 依赖: Finset, Finset.coe_inj, coe_inj
-/
theorem neighborFinset_inf [DecidableEq V] {G₁ G₂ : SimpleGraph V}
    [Fintype ((G₁ ⊓ G₂).neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)] :
    (G₁ ⊓ G₂).neighborFinset v = G₁.neighborFinset v inter G₂.neighborFinset v := by
  simp [← Finset.coe_inj]

@[simp]
/--
theorem `neighborFinset_sdiff` / 定理 `neighborFinset_sdiff`

English:
theorem neighborFinset_sdiff
  statement: [DecidableEq V] {G₁ G₂ : SimpleGraph V}
  proof: by
  simp [← Finset.coe_inj]

中文:
定理 neighborFinset_sdiff
  结论: [DecidableEq V] {G₁ G₂ : SimpleGraph V}
  证明: by
  simp [← Finset.coe_inj]

Depends on / 依赖: Finset, Finset.coe_inj, coe_inj
-/
theorem neighborFinset_sdiff [DecidableEq V] {G₁ G₂ : SimpleGraph V}
    [Fintype ((G₁ \ G₂).neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)] :
    (G₁ \ G₂).neighborFinset v = G₁.neighborFinset v \ G₂.neighborFinset v := by
  simp [← Finset.coe_inj]

/--
theorem `disjoint_neighborFinset_of_disjoint` / 定理 `disjoint_neighborFinset_of_disjoint`

English:
theorem disjoint_neighborFinset_of_disjoint
  given: [Fintype <| H.neighborSet v] (h : Disjoint G H)
  proof: by
  simp [← Finset.disjoint_coe, disjoint_neighborSet.mpr h v]

中文:
定理 disjoint_neighborFinset_of_disjoint
  条件: [Fintype <| H.neighborSet v] (h : Disjoint G H)
  证明: by
  simp [← Finset.disjoint_coe, disjoint_neighborSet.mpr h v]

Depends on / 依赖: Finset, Finset.disjoint_coe, disjoint_coe, disjoint_neighborSet, disjoint_neighborSet.mpr
-/
theorem disjoint_neighborFinset_of_disjoint [Fintype <| H.neighborSet v] (h : Disjoint G H) :
    Disjoint (G.neighborFinset v) (H.neighborFinset v) := by
  simp [← Finset.disjoint_coe, disjoint_neighborSet.mpr h v]

/--
theorem `neighborFinset_sup_of_disjoint` / 定理 `neighborFinset_sup_of_disjoint`

English:
theorem neighborFinset_sup_of_disjoint
  statement: {G₁ G₂ : SimpleGraph V}
  proof: by
  simp [← Finset.coe_inj, Finset.coe_disjUnion]

中文:
定理 neighborFinset_sup_of_disjoint
  结论: {G₁ G₂ : SimpleGraph V}
  证明: by
  simp [← Finset.coe_inj, Finset.coe_disjUnion]

Depends on / 依赖: Finset, Finset.coe_disjUnion, Finset.coe_inj, coe_disjUnion, coe_inj
-/
theorem neighborFinset_sup_of_disjoint {G₁ G₂ : SimpleGraph V}
    [Fintype ((G₁ ⊔ G₂).neighborSet v)] [Fintype (G₁.neighborSet v)] [Fintype (G₂.neighborSet v)]
    (h : Disjoint G₁ G₂) :
    (G₁ ⊔ G₂).neighborFinset v =
      (G₁.neighborFinset v).disjUnion (G₂.neighborFinset v)
        (disjoint_neighborFinset_of_disjoint G₁ G₂ v h) := by
  simp [← Finset.coe_inj, Finset.coe_disjUnion]

/--
lemma `neighborFinset_eq_empty` / 引理 `neighborFinset_eq_empty`

English:
lemma neighborFinset_eq_empty
  statement: G.neighborFinset v = ∅ ↔ G.IsIsolated v
  proof: by
  simp [neighborFinset, IsIsolated, Set.ext_iff]

中文:
引理 neighborFinset_eq_empty
  结论: G.neighborFinset v = ∅ ↔ G.IsIsolated v
  证明: by
  simp [neighborFinset, IsIsolated, Set.ext_iff]
-/
@[simp] lemma neighborFinset_eq_empty : G.neighborFinset v = ∅ ↔ G.IsIsolated v := by
  simp [neighborFinset, IsIsolated, Set.ext_iff]

/--
lemma `neighborFinset_nonempty` / 引理 `neighborFinset_nonempty`

English:
lemma neighborFinset_nonempty
  statement: (G.neighborFinset v).Nonempty ↔ ¬ G.IsIsolated v
  proof: by
  simp [nonempty_iff_ne_empty]

protected alias ⟨IsIsolated.of_neighborFinset_eq_empty, IsIsolated.neighborFinset_eq_empty⟩
    := neighborFinset_eq_empty

中文:
引理 neighborFinset_nonempty
  结论: (G.neighborFinset v).Nonempty ↔ ¬ G.IsIsolated v
  证明: by
  simp [nonempty_iff_ne_empty]

protected alias ⟨IsIsolated.of_neighborFinset_eq_empty, IsIsolated.neighborFinset_eq_empty⟩
    := neighborFinset_eq_empty

Depends on / 依赖: Equiv.ulift.symm, Finite, Finite.of_equiv, of_equiv
-/
@[simp] lemma neighborFinset_nonempty : (G.neighborFinset v).Nonempty ↔ ¬ G.IsIsolated v := by
  simp [nonempty_iff_ne_empty]

protected alias ⟨IsIsolated.of_neighborFinset_eq_empty, IsIsolated.neighborFinset_eq_empty⟩
    := neighborFinset_eq_empty

attribute [simp] IsIsolated.neighborFinset_eq_empty

/--
Definition of `degree` / `degree` 的定义

English:
definition degree
  signature: : Nat
  body: #(G.neighborFinset v)

@[simp]

中文:
定义 degree
  签名: : 自然数
  定义体: #(G.neighborFinset v)

@[simp]

Depends on / 依赖: G.neighborFinset, neighborFinset
-/
def degree : Nat := #(G.neighborFinset v)

@[simp]
/--
theorem `card_neighborFinset_eq_degree` / 定理 `card_neighborFinset_eq_degree`

English:
theorem card_neighborFinset_eq_degree
  statement: #(G.neighborFinset v) = G.degree v
  proof: rfl

中文:
定理 card_neighborFinset_eq_degree
  结论: #(G.neighborFinset v) = G.degree v
  证明: rfl
-/
theorem card_neighborFinset_eq_degree : #(G.neighborFinset v) = G.degree v := rfl

/--
theorem `card_neighborSet_eq_degree` / 定理 `card_neighborSet_eq_degree`

English:
theorem card_neighborSet_eq_degree
  statement: Fintype.card (G.neighborSet v) = G.degree v
  proof: (Set.toFinset_card _).symm

中文:
定理 card_neighborSet_eq_degree
  结论: Fintype.card (G.neighborSet v) = G.degree v
  证明: (Set.toFinset_card _).symm

Depends on / 依赖: Set.toFinset_card, toFinset_card
-/
theorem card_neighborSet_eq_degree : Fintype.card (G.neighborSet v) = G.degree v :=
  (Set.toFinset_card _).symm

/--
lemma `degree_eq_zero` / 引理 `degree_eq_zero`

English:
lemma degree_eq_zero
  statement: G.degree v = 0 ↔ G.IsIsolated v
  proof: by simp [← card_neighborFinset_eq_degree]

中文:
引理 degree_eq_zero
  结论: G.degree v = 0 ↔ G.IsIsolated v
  证明: by simp [← card_neighborFinset_eq_degree]

Depends on / 依赖: card_neighborFinset_eq_degree
-/
lemma degree_eq_zero : G.degree v = 0 ↔ G.IsIsolated v := by simp [← card_neighborFinset_eq_degree]
/--
lemma `degree_pos` / 引理 `degree_pos`

English:
lemma degree_pos
  statement: 0 < G.degree v ↔ ¬ G.IsIsolated v
  proof: by simp [← card_neighborFinset_eq_degree]

protected alias ⟨IsIsolated.of_degree_eq_zero, IsIsolated.degree_eq_zero⟩ := degree_eq_zero

中文:
引理 degree_pos
  结论: 0 < G.degree v ↔ ¬ G.IsIsolated v
  证明: by simp [← card_neighborFinset_eq_degree]

protected alias ⟨IsIsolated.of_degree_eq_zero, IsIsolated.degree_eq_zero⟩ := degree_eq_zero

Depends on / 依赖: Equiv.ulift.infinite_iff, card_neighborFinset_eq_degree, infinite_iff
-/
lemma degree_pos : 0 < G.degree v ↔ ¬ G.IsIsolated v := by simp [← card_neighborFinset_eq_degree]

protected alias ⟨IsIsolated.of_degree_eq_zero, IsIsolated.degree_eq_zero⟩ := degree_eq_zero

attribute [simp] IsIsolated.degree_eq_zero

/--
theorem `degree_pos_iff_exists_adj` / 定理 `degree_pos_iff_exists_adj`

English:
theorem degree_pos_iff_exists_adj
  statement: 0 < G.degree v ↔ exists w, G.Adj v w
  proof: by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighborFinset]

中文:
定理 degree_pos_iff_exists_adj
  结论: 0 < G.degree v ↔ 存在 w, G.Adj v w
  证明: by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighborFinset]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty, card_pos, degree, mem_neighborFinset
-/
theorem degree_pos_iff_exists_adj : 0 < G.degree v ↔ exists w, G.Adj v w := by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighborFinset]

variable {G v} in
/--
theorem `degree_pos_iff_nonempty` / 定理 `degree_pos_iff_nonempty`

English:
theorem degree_pos_iff_nonempty
  statement: 0 < G.degree v ↔ (G.neighborSet v).Nonempty
  proof: G.degree_pos_iff_exists_adj v

中文:
定理 degree_pos_iff_nonempty
  结论: 0 < G.degree v ↔ (G.neighborSet v).Nonempty
  证明: G.degree_pos_iff_exists_adj v

Depends on / 依赖: G.degree_pos_iff_exists_adj, degree_pos_iff_exists_adj
-/
theorem degree_pos_iff_nonempty : 0 < G.degree v ↔ (G.neighborSet v).Nonempty :=
  G.degree_pos_iff_exists_adj v

variable {G v} in
/--
theorem `Adj.degree_pos_left` / 定理 `Adj.degree_pos_left`

English:
theorem Adj.degree_pos_left
  given: {w : V} (h : G.Adj v w)
  statement: 0 < G.degree v
  proof: G.degree_pos_iff_nonempty.mpr ⟨_, h⟩

中文:
定理 Adj.degree_pos_left
  条件: {w : V} (h : G.Adj v w)
  结论: 0 < G.degree v
  证明: G.degree_pos_iff_nonempty.mpr ⟨_, h⟩

Depends on / 依赖: G.degree_pos_iff_nonempty.mpr, degree_pos_iff_nonempty
-/
theorem Adj.degree_pos_left {w : V} (h : G.Adj v w) : 0 < G.degree v :=
  G.degree_pos_iff_nonempty.mpr ⟨_, h⟩

variable {G v} in
/--
theorem `Adj.degree_pos_right` / 定理 `Adj.degree_pos_right`

English:
theorem Adj.degree_pos_right
  given: {w : V} (h : G.Adj w v)
  statement: 0 < G.degree v
  proof: h.symm.degree_pos_left

中文:
定理 Adj.degree_pos_right
  条件: {w : V} (h : G.Adj w v)
  结论: 0 < G.degree v
  证明: h.symm.degree_pos_left

Depends on / 依赖: degree_pos_left, h.symm.degree_pos_left
-/
theorem Adj.degree_pos_right {w : V} (h : G.Adj w v) : 0 < G.degree v :=
  h.symm.degree_pos_left

/--
theorem `degree_pos_iff_mem_support` / 定理 `degree_pos_iff_mem_support`

English:
theorem degree_pos_iff_mem_support
  statement: 0 < G.degree v ↔ v in G.support
  proof: by
  rw [G.degree_pos_iff_exists_adj v]; rw [mem_support]

中文:
定理 degree_pos_iff_mem_support
  结论: 0 < G.degree v ↔ v in G.support
  证明: by
  rw [G.degree_pos_iff_exists_adj v]; rw [mem_support]

Depends on / 依赖: G.degree_pos_iff_exists_adj, degree_pos_iff_exists_adj, mem_support
-/
theorem degree_pos_iff_mem_support : 0 < G.degree v ↔ v in G.support := by
  rw [G.degree_pos_iff_exists_adj v]; rw [mem_support]

/--
theorem `degree_eq_zero_iff_notMem_support` / 定理 `degree_eq_zero_iff_notMem_support`

English:
theorem degree_eq_zero_iff_notMem_support
  statement: G.degree v = 0 ↔ v ∉ G.support
  proof: by
  rw [← G.degree_pos_iff_mem_support v]; rw [Nat.pos_iff_ne_zero]; rw [not_ne_iff]

中文:
定理 degree_eq_zero_iff_notMem_support
  结论: G.degree v = 0 ↔ v ∉ G.support
  证明: by
  rw [← G.degree_pos_iff_mem_support v]; rw [Nat.pos_iff_ne_zero]; rw [not_ne_iff]

Depends on / 依赖: G.degree_pos_iff_mem_support, Nat.pos_iff_ne_zero, degree_pos_iff_mem_support, not_ne_iff, pos_iff_ne_zero
-/
theorem degree_eq_zero_iff_notMem_support : G.degree v = 0 ↔ v ∉ G.support := by
  rw [← G.degree_pos_iff_mem_support v]; rw [Nat.pos_iff_ne_zero]; rw [not_ne_iff]

/--
theorem `degree_eq_zero_of_subsingleton` / 定理 `degree_eq_zero_of_subsingleton`

English:
theorem degree_eq_zero_of_subsingleton
  statement: {G : SimpleGraph V} (v : V) [Fintype (G.neighborSet v)]
  proof: by
  simp

中文:
定理 degree_eq_zero_of_subsingleton
  结论: {G : SimpleGraph V} (v : V) [Fintype (G.neighborSet v)]
  证明: by
  simp
-/
theorem degree_eq_zero_of_subsingleton {G : SimpleGraph V} (v : V) [Fintype (G.neighborSet v)]
    [Subsingleton V] : G.degree v = 0 := by
  simp

/--
theorem `nontrivial_of_degree_ne_zero` / 定理 `nontrivial_of_degree_ne_zero`

English:
theorem nontrivial_of_degree_ne_zero
  statement: {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)]
  proof: nontrivial_of_not_isIsolated .not.mp h G.degree_eq_zero v

中文:
定理 nontrivial_of_degree_ne_zero
  结论: {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)]
  证明: nontrivial_of_not_isIsolated .not.mp h G.degree_eq_zero v

Depends on / 依赖: G.degree_eq_zero, degree_eq_zero, nontrivial_of_not_isIsolated, not.mp
-/
theorem nontrivial_of_degree_ne_zero {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)]
    (h : G.degree v != 0) : Nontrivial V :=
nontrivial_of_not_isIsolated .not.mp h G.degree_eq_zero v

/--
theorem `degree_eq_one_iff_existsUnique_adj` / 定理 `degree_eq_one_iff_existsUnique_adj`

English:
theorem degree_eq_one_iff_existsUnique_adj
  given: {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)]
  proof: by
  rw [degree]; rw [Finset.card_eq_one]; rw [Finset.singleton_iff_unique_mem]
  simp only [mem_neighborFinset]

中文:
定理 degree_eq_one_iff_existsUnique_adj
  条件: {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)]
  证明: by
  rw [degree]; rw [Finset.card_eq_one]; rw [Finset.singleton_iff_unique_mem]
  simp only [mem_neighborFinset]

Depends on / 依赖: Finset, Finset.card_eq_one, Finset.singleton_iff_unique_mem, card_eq_one, degree, mem_neighborFinset, singleton_iff_unique_mem
-/
theorem degree_eq_one_iff_existsUnique_adj {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)] :
    G.degree v = 1 ↔ exists! w : V, G.Adj v w := by
  rw [degree]; rw [Finset.card_eq_one]; rw [Finset.singleton_iff_unique_mem]
  simp only [mem_neighborFinset]

/--
theorem `degree_compl` / 定理 `degree_compl`

English:
theorem degree_compl
  given: [Fintype (Gᶜ.neighborSet v)] [Fintype V]
  proof: by
  classical
    rw [← card_neighborSet_union_compl_neighborSet G v]; rw [Set.toFinset_union]
    simp [card_union_of_disjoint (Set.disjoint_toFinset.mpr (compl_neighborSet_disjoint G v)),
      card_neighborSet_eq_degree]

中文:
定理 degree_compl
  条件: [Fintype (Gᶜ.neighborSet v)] [Fintype V]
  证明: by
  classical
    rw [← card_neighborSet_union_compl_neighborSet G v]; rw [Set.toFinset_union]
    simp [card_union_of_disjoint (Set.disjoint_toFinset.mpr (compl_neighborSet_disjoint G v)),
      card_neighborSet_eq_degree]

Depends on / 依赖: Set.disjoint_toFinset.mpr, Set.toFinset_union, card_neighborSet_eq_degree, card_neighborSet_union_compl_neighborSet, card_union_of_disjoint, classical, compl_neighborSet_disjoint, disjoint_toFinset, toFinset_union
-/
theorem degree_compl [Fintype (Gᶜ.neighborSet v)] [Fintype V] :
    Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  classical
    rw [← card_neighborSet_union_compl_neighborSet G v]; rw [Set.toFinset_union]
    simp [card_union_of_disjoint (Set.disjoint_toFinset.mpr (compl_neighborSet_disjoint G v)),
      card_neighborSet_eq_degree]

/--
Instance `incidenceSetFintype` / 实例 `incidenceSetFintype`

English:
instance incidenceSetFintype
  signature: [DecidableEq V]
  body: Fintype.ofEquiv (G.neighborSet v) (G.incidenceSetEquivNeighborSet v).symm

中文:
实例 incidenceSetFintype
  签名: [DecidableEq V]
  定义体: Fintype.ofEquiv (G.neighborSet v) (G.incidenceSetEquivNeighborSet v).symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, G.incidenceSetEquivNeighborSet, G.neighborSet, incidenceSetEquivNeighborSet, neighborSet, ofEquiv
-/
instance incidenceSetFintype [DecidableEq V] : Fintype (G.incidenceSet v) :=
  Fintype.ofEquiv (G.neighborSet v) (G.incidenceSetEquivNeighborSet v).symm

/--
Definition of `incidenceFinset` / `incidenceFinset` 的定义

English:
definition incidenceFinset
  signature: [DecidableEq V]
  body: (G.incidenceSet v).toFinset

中文:
定义 incidenceFinset
  签名: [DecidableEq V]
  定义体: (G.incidenceSet v).toFinset

Depends on / 依赖: G.incidenceSet, incidenceSet, toFinset
-/
def incidenceFinset [DecidableEq V] : Finset (Sym2 V) :=
  (G.incidenceSet v).toFinset

/--
theorem `card_incidenceSet_eq_degree` / 定理 `card_incidenceSet_eq_degree`

English:
theorem card_incidenceSet_eq_degree
  given: [DecidableEq V]
  proof: by
  rw [Fintype.card_congr (G.incidenceSetEquivNeighborSet v)]; rw [card_neighborSet_eq_degree]

@[simp, norm_cast]

中文:
定理 card_incidenceSet_eq_degree
  条件: [DecidableEq V]
  证明: by
  rw [Fintype.card_congr (G.incidenceSetEquivNeighborSet v)]; rw [card_neighborSet_eq_degree]

@[simp, norm_cast]

Depends on / 依赖: Fintype, Fintype.card_congr, G.incidenceSetEquivNeighborSet, card_congr, card_neighborSet_eq_degree, incidenceSetEquivNeighborSet
-/
theorem card_incidenceSet_eq_degree [DecidableEq V] :
    Fintype.card (G.incidenceSet v) = G.degree v := by
  rw [Fintype.card_congr (G.incidenceSetEquivNeighborSet v)]; rw [card_neighborSet_eq_degree]

@[simp, norm_cast]
/--
theorem `coe_incidenceFinset` / 定理 `coe_incidenceFinset`

English:
theorem coe_incidenceFinset
  given: [DecidableEq V]
  proof: by
  simp [incidenceFinset]

@[simp]

中文:
定理 coe_incidenceFinset
  条件: [DecidableEq V]
  证明: by
  simp [incidenceFinset]

@[simp]

Depends on / 依赖: incidenceFinset
-/
theorem coe_incidenceFinset [DecidableEq V] :
    (G.incidenceFinset v : Set (Sym2 V)) = G.incidenceSet v := by
  simp [incidenceFinset]

@[simp]
/--
theorem `card_incidenceFinset_eq_degree` / 定理 `card_incidenceFinset_eq_degree`

English:
theorem card_incidenceFinset_eq_degree
  given: [DecidableEq V]
  statement: #(G.incidenceFinset v) = G.degree v
  proof: by
  rw [← G.card_incidenceSet_eq_degree]
  apply Set.toFinset_card

@[simp]

中文:
定理 card_incidenceFinset_eq_degree
  条件: [DecidableEq V]
  结论: #(G.incidenceFinset v) = G.degree v
  证明: by
  rw [← G.card_incidenceSet_eq_degree]
  apply Set.toFinset_card

@[simp]

Depends on / 依赖: G.card_incidenceSet_eq_degree, Set.toFinset_card, card_incidenceSet_eq_degree, toFinset_card
-/
theorem card_incidenceFinset_eq_degree [DecidableEq V] : #(G.incidenceFinset v) = G.degree v := by
  rw [← G.card_incidenceSet_eq_degree]
  apply Set.toFinset_card

@[simp]
/--
theorem `mem_incidenceFinset` / 定理 `mem_incidenceFinset`

English:
theorem mem_incidenceFinset
  given: [DecidableEq V] (e : Sym2 V)
  proof: Set.mem_toFinset

中文:
定理 mem_incidenceFinset
  条件: [DecidableEq V] (e : Sym2 V)
  证明: Set.mem_toFinset

Depends on / 依赖: Equiv.pprodEquivProdPLift.symm, Set.mem_toFinset, mem_toFinset, of_equiv, pprodEquivProdPLift
-/
theorem mem_incidenceFinset [DecidableEq V] (e : Sym2 V) :
    e in G.incidenceFinset v ↔ e in G.incidenceSet v :=
  Set.mem_toFinset

/--
theorem `incidenceFinset_eq_filter` / 定理 `incidenceFinset_eq_filter`

English:
theorem incidenceFinset_eq_filter
  given: [DecidableEq V] [Fintype G.edgeSet]
  proof: by
  ext ⟨⟨⟩⟩
  simp [mk'_mem_incidenceSet_iff]

中文:
定理 incidenceFinset_eq_filter
  条件: [DecidableEq V] [Fintype G.edgeSet]
  证明: by
  ext ⟨⟨⟩⟩
  simp [mk'_mem_incidenceSet_iff]

Depends on / 依赖: _mem_incidenceSet_iff
-/
theorem incidenceFinset_eq_filter [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v = {e in G.edgeFinset | v in e} := by
  ext ⟨⟨⟩⟩
  simp [mk'_mem_incidenceSet_iff]

/--
theorem `incidenceFinset_subset` / 定理 `incidenceFinset_subset`

English:
theorem incidenceFinset_subset
  given: [DecidableEq V] [Fintype G.edgeSet]
  proof: Set.toFinset_subset_toFinset.mpr (G.incidenceSet_subset v)

中文:
定理 incidenceFinset_subset
  条件: [DecidableEq V] [Fintype G.edgeSet]
  证明: Set.toFinset_subset_toFinset.mpr (G.incidenceSet_subset v)

Depends on / 依赖: G.incidenceSet_subset, Set.toFinset_subset_toFinset.mpr, incidenceSet_subset, toFinset_subset_toFinset
-/
theorem incidenceFinset_subset [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v subseteq G.edgeFinset :=
  Set.toFinset_subset_toFinset.mpr (G.incidenceSet_subset v)

/--
theorem `disjoint_incidenceFinset_of_disjoint` / 定理 `disjoint_incidenceFinset_of_disjoint`

English:
theorem disjoint_incidenceFinset_of_disjoint
  statement: [DecidableEq V] [Fintype <| H.neighborSet v]
  proof: by
  simp [← Finset.disjoint_coe, disjoint_incidenceSet.mpr h v]

中文:
定理 disjoint_incidenceFinset_of_disjoint
  结论: [DecidableEq V] [Fintype <| H.neighborSet v]
  证明: by
  simp [← Finset.disjoint_coe, disjoint_incidenceSet.mpr h v]

Depends on / 依赖: Finset, Finset.disjoint_coe, disjoint_coe, disjoint_incidenceSet, disjoint_incidenceSet.mpr
-/
theorem disjoint_incidenceFinset_of_disjoint [DecidableEq V] [Fintype <| H.neighborSet v]
    (h : Disjoint G H) : Disjoint (G.incidenceFinset v) (H.incidenceFinset v) := by
  simp [← Finset.disjoint_coe, disjoint_incidenceSet.mpr h v]

/--
theorem `degree_le_card_edgeFinset` / 定理 `degree_le_card_edgeFinset`

English:
theorem degree_le_card_edgeFinset
  given: [Fintype G.edgeSet]
  proof: by
  classical
  rw [← card_incidenceFinset_eq_degree]
  exact card_le_card (G.incidenceFinset_subset v)

中文:
定理 degree_le_card_edgeFinset
  条件: [Fintype G.edgeSet]
  证明: by
  classical
  rw [← card_incidenceFinset_eq_degree]
  exact card_le_card (G.incidenceFinset_subset v)

Depends on / 依赖: G.incidenceFinset_subset, card_incidenceFinset_eq_degree, card_le_card, classical, incidenceFinset_subset
-/
theorem degree_le_card_edgeFinset [Fintype G.edgeSet] :
    G.degree v <= #G.edgeFinset := by
  classical
  rw [← card_incidenceFinset_eq_degree]
  exact card_le_card (G.incidenceFinset_subset v)

variable {G v}

/--
lemma `degree_le_of_le` / 引理 `degree_le_of_le`

English:
lemma degree_le_of_le
  given: {H : SimpleGraph V} [Fintype (H.neighborSet v)] (hle : G <= H)
  proof: by
  simp_rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card fun v hv => hle hv

中文:
引理 degree_le_of_le
  条件: {H : SimpleGraph V} [Fintype (H.neighborSet v)] (hle : G <= H)
  证明: by
  simp_rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card fun v hv => hle hv

Depends on / 依赖: Set.card_le_card, card_le_card, card_neighborSet_eq_degree, simp_rw
-/
lemma degree_le_of_le {H : SimpleGraph V} [Fintype (H.neighborSet v)] (hle : G <= H) :
    G.degree v <= H.degree v := by
  simp_rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card fun v hv => hle hv

/--
theorem `degree_lt_card_verts` / 定理 `degree_lt_card_verts`

English:
theorem degree_lt_card_verts
  given: [Fintype V] [DecidableRel G.Adj] (v : V)
  proof: Finset.card_lt_univ_of_notMem G.notMem_neighborFinset_self v

中文:
定理 degree_lt_card_verts
  条件: [Fintype V] [DecidableRel G.Adj] (v : V)
  证明: Finset.card_lt_univ_of_notMem G.notMem_neighborFinset_self v

Depends on / 依赖: Finset, Finset.card_lt_univ_of_notMem, G.notMem_neighborFinset_self, card_lt_univ_of_notMem, notMem_neighborFinset_self
-/
theorem degree_lt_card_verts [Fintype V] [DecidableRel G.Adj] (v : V) :
    G.degree v < Fintype.card V :=
Finset.card_lt_univ_of_notMem G.notMem_neighborFinset_self v

end FiniteAt

section LocallyFinite

/--
Definition of `LocallyFinite` / `LocallyFinite` 的定义

English:
abbreviation LocallyFinite
  body: forall v : V, Fintype (G.neighborSet v)

中文:
缩写 LocallyFinite
  定义体: forall v : V, Fintype (G.neighborSet v)

Depends on / 依赖: Fintype, G.neighborSet, neighborSet
-/
abbrev LocallyFinite :=
  forall v : V, Fintype (G.neighborSet v)

variable [LocallyFinite G]

/-- A locally finite simple graph is regular of degree `d` if every vertex has degree `d`. -/
@[wikidata Q826467]
/--
Definition of `IsRegularOfDegree` / `IsRegularOfDegree` 的定义

English:
definition IsRegularOfDegree
  signature: (d : Nat)
  body: forall v : V, G.degree v = d

中文:
定义 IsRegularOfDegree
  签名: (d : 自然数)
  定义体: forall v : V, G.degree v = d

Depends on / 依赖: G.degree, degree
-/
def IsRegularOfDegree (d : Nat) : Prop :=
  forall v : V, G.degree v = d

variable {G}

/--
theorem `IsRegularOfDegree.degree_eq` / 定理 `IsRegularOfDegree.degree_eq`

English:
theorem IsRegularOfDegree.degree_eq
  given: {d : Nat} (h : G.IsRegularOfDegree d) (v : V)
  statement: G.degree v = d
  proof: h v

中文:
定理 IsRegularOfDegree.degree_eq
  条件: {d : 自然数} (h : G.IsRegularOfDegree d) (v : V)
  结论: G.degree v = d
  证明: h v
-/
theorem IsRegularOfDegree.degree_eq {d : Nat} (h : G.IsRegularOfDegree d) (v : V) : G.degree v = d :=
  h v

/-- The empty graph is regular of any degree `d` -/
@[simp]
/--
theorem `IsRegularOfDegree.of_isEmpty` / 定理 `IsRegularOfDegree.of_isEmpty`

English:
theorem IsRegularOfDegree.of_isEmpty
  given: [IsEmpty V] {d : Nat}
  statement: G.IsRegularOfDegree d
  proof: IsEmpty.elim ‹_›

中文:
定理 IsRegularOfDegree.of_isEmpty
  条件: [IsEmpty V] {d : 自然数}
  结论: G.IsRegularOfDegree d
  证明: IsEmpty.elim ‹_›

Depends on / 依赖: IsEmpty, IsEmpty.elim
-/
theorem IsRegularOfDegree.of_isEmpty [IsEmpty V] {d : Nat} : G.IsRegularOfDegree d :=
  IsEmpty.elim ‹_›

/--
theorem `IsRegularOfDegree.compl` / 定理 `IsRegularOfDegree.compl`

English:
theorem IsRegularOfDegree.compl
  statement: [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  proof: by
  intro v
  rw [degree_compl]; rw [h v]

中文:
定理 IsRegularOfDegree.compl
  结论: [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  证明: by
  intro v
  rw [degree_compl]; rw [h v]

Depends on / 依赖: degree_compl
-/
theorem IsRegularOfDegree.compl [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : Nat} (h : G.IsRegularOfDegree k) : Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k) := by
  intro v
  rw [degree_compl]; rw [h v]

end LocallyFinite

section Finite

variable [Fintype V]

/-- `Fintype` for `neighborSet` -/
@[deprecated inferInstance (since := "2026-04-29")]
/--
Definition of `neighborSetFintype` / `neighborSetFintype` 的定义

English:
abbreviation neighborSetFintype
  signature: [DecidableRel G.Adj] (v : V)
  body: inferInstance

中文:
缩写 neighborSetFintype
  签名: [DecidableRel G.Adj] (v : V)
  定义体: inferInstance
-/
abbrev neighborSetFintype [DecidableRel G.Adj] (v : V) : Fintype (G.neighborSet v) :=
  inferInstance

/--
theorem `neighborFinset_eq_filter` / 定理 `neighborFinset_eq_filter`

English:
theorem neighborFinset_eq_filter
  given: {v : V} [DecidableRel G.Adj]
  proof: by ext; simp

中文:
定理 neighborFinset_eq_filter
  条件: {v : V} [DecidableRel G.Adj]
  证明: by ext; simp
-/
theorem neighborFinset_eq_filter {v : V} [DecidableRel G.Adj] :
    G.neighborFinset v = ({w | G.Adj v w} : Finset _) := by ext; simp

/--
theorem `neighborFinset_compl` / 定理 `neighborFinset_compl`

English:
theorem neighborFinset_compl
  given: [DecidableEq V] [DecidableRel G.Adj] (v : V)
  proof: by
  simp only [neighborFinset, neighborSet_compl, Set.toFinset_sdiff, Set.toFinset_compl,
    Set.toFinset_singleton]

@[simp]

中文:
定理 neighborFinset_compl
  条件: [DecidableEq V] [DecidableRel G.Adj] (v : V)
  证明: by
  simp only [neighborFinset, neighborSet_compl, Set.toFinset_sdiff, Set.toFinset_compl,
    Set.toFinset_singleton]

@[simp]

Depends on / 依赖: Set.toFinset_compl, Set.toFinset_sdiff, Set.toFinset_singleton, neighborFinset, neighborSet_compl, toFinset_compl, toFinset_sdiff, toFinset_singleton
-/
theorem neighborFinset_compl [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    Gᶜ.neighborFinset v = (G.neighborFinset v)ᶜ \ {v} := by
  simp only [neighborFinset, neighborSet_compl, Set.toFinset_sdiff, Set.toFinset_compl,
    Set.toFinset_singleton]

@[simp]
/--
theorem `complete_graph_degree` / 定理 `complete_graph_degree`

English:
theorem complete_graph_degree
  given: [DecidableEq V] (v : V)
  proof: by
  simp_rw [degree, neighborFinset_eq_filter, top_adj, filter_ne]
  rw [card_erase_of_mem (mem_univ v)]; rw [card_univ]

中文:
定理 complete_graph_degree
  条件: [DecidableEq V] (v : V)
  证明: by
  simp_rw [degree, neighborFinset_eq_filter, top_adj, filter_ne]
  rw [card_erase_of_mem (mem_univ v)]; rw [card_univ]

Depends on / 依赖: card_erase_of_mem, card_univ, degree, filter_ne, mem_univ, neighborFinset_eq_filter, simp_rw, top_adj
-/
theorem complete_graph_degree [DecidableEq V] (v : V) :
    (completeGraph V).degree v = Fintype.card V - 1 := by
  simp_rw [degree, neighborFinset_eq_filter, top_adj, filter_ne]
  rw [card_erase_of_mem (mem_univ v)]; rw [card_univ]

/--
theorem `bot_degree` / 定理 `bot_degree`

English:
theorem bot_degree
  given: (v : V)
  statement: (⊥ : SimpleGraph V).degree v = 0
  proof: by
  simp

中文:
定理 bot_degree
  条件: (v : V)
  结论: (⊥ : SimpleGraph V).degree v = 0
  证明: by
  simp
-/
theorem bot_degree (v : V) : (⊥ : SimpleGraph V).degree v = 0 := by
  simp

/--
theorem `IsRegularOfDegree.top` / 定理 `IsRegularOfDegree.top`

English:
theorem IsRegularOfDegree.top
  given: [DecidableEq V]
  proof: by
  simp [IsRegularOfDegree]

@[simp]

中文:
定理 IsRegularOfDegree.top
  条件: [DecidableEq V]
  证明: by
  simp [IsRegularOfDegree]

@[simp]

Depends on / 依赖: IsRegularOfDegree
-/
theorem IsRegularOfDegree.top [DecidableEq V] :
    (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) := by
  simp [IsRegularOfDegree]

@[simp]
/--
theorem `IsRegularOfDegree.bot` / 定理 `IsRegularOfDegree.bot`

English:
theorem IsRegularOfDegree.bot
  statement: (⊥ : SimpleGraph V).IsRegularOfDegree 0
  proof: bot_degree

中文:
定理 IsRegularOfDegree.bot
  结论: (⊥ : SimpleGraph V).IsRegularOfDegree 0
  证明: bot_degree

Depends on / 依赖: bot_degree
-/
theorem IsRegularOfDegree.bot : (⊥ : SimpleGraph V).IsRegularOfDegree 0 :=
  bot_degree

/--
Definition of `minDegree` / `minDegree` 的定义

English:
definition minDegree
  signature: [DecidableRel G.Adj]
  body: WithTop.untopD 0 (univ.image fun v => G.degree v).min

中文:
定义 minDegree
  签名: [DecidableRel G.Adj]
  定义体: WithTop.untopD 0 (univ.image fun v => G.degree v).min

Depends on / 依赖: G.degree, WithTop, WithTop.untopD, degree, univ.image, untopD
-/
def minDegree [DecidableRel G.Adj] : Nat :=
  WithTop.untopD 0 (univ.image fun v => G.degree v).min

/--
theorem `exists_minimal_degree_vertex` / 定理 `exists_minimal_degree_vertex`

English:
theorem exists_minimal_degree_vertex
  given: [DecidableRel G.Adj] [Nonempty V]
  proof: by
  grind [minDegree, WithTop.untopD_coe, min_mem_image_coe <| univ_nonempty.image (G.degree ·)]

中文:
定理 exists_minimal_degree_vertex
  条件: [DecidableRel G.Adj] [Nonempty V]
  证明: by
  grind [minDegree, WithTop.untopD_coe, min_mem_image_coe <| univ_nonempty.image (G.degree ·)]

Depends on / 依赖: G.degree, WithTop, WithTop.untopD_coe, degree, minDegree, min_mem_image_coe, univ_nonempty, univ_nonempty.image, untopD_coe
-/
theorem exists_minimal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    exists v, G.minDegree = G.degree v := by
  grind [minDegree, WithTop.untopD_coe, min_mem_image_coe <| univ_nonempty.image (G.degree ·)]

/--
theorem `minDegree_le_degree` / 定理 `minDegree_le_degree`

English:
theorem minDegree_le_degree
  given: [DecidableRel G.Adj] (v : V)
  statement: G.minDegree <= G.degree v
  proof: WithTop.untopD_le Finset.min_le mem_image_of_mem (G.degree ·) mem_univ v

中文:
定理 minDegree_le_degree
  条件: [DecidableRel G.Adj] (v : V)
  结论: G.minDegree <= G.degree v
  证明: WithTop.untopD_le Finset.min_le mem_image_of_mem (G.degree ·) mem_univ v

Depends on / 依赖: Finset, Finset.min_le, G.degree, WithTop, WithTop.untopD_le, degree, mem_image_of_mem, mem_univ, min_le, untopD_le
-/
theorem minDegree_le_degree [DecidableRel G.Adj] (v : V) : G.minDegree <= G.degree v :=
WithTop.untopD_le Finset.min_le mem_image_of_mem (G.degree ·) mem_univ v

/--
theorem `le_minDegree_of_forall_le_degree` / 定理 `le_minDegree_of_forall_le_degree`

English:
theorem le_minDegree_of_forall_le_degree
  statement: [DecidableRel G.Adj] [Nonempty V] (k : Nat)
  proof: by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  rw [hv]
  apply h

@[simp]

中文:
定理 le_minDegree_of_forall_le_degree
  结论: [DecidableRel G.Adj] [Nonempty V] (k : 自然数)
  证明: by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  rw [hv]
  apply h

@[simp]

Depends on / 依赖: G.exists_minimal_degree_vertex, exists_minimal_degree_vertex
-/
theorem le_minDegree_of_forall_le_degree [DecidableRel G.Adj] [Nonempty V] (k : Nat)
    (h : forall v, k <= G.degree v) : k <= G.minDegree := by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  rw [hv]
  apply h

@[simp]
/--
lemma `minDegree_of_subsingleton` / 引理 `minDegree_of_subsingleton`

English:
lemma minDegree_of_subsingleton
  given: [DecidableRel G.Adj] [Subsingleton V]
  statement: G.minDegree = 0
  proof: by
  cases isEmpty_or_nonempty V <;>
    simp [minDegree, Finset.image_const]

@[deprecated (since := "2026-06-15")] alias minDegree_of_isEmpty := minDegree_of_subsingleton

中文:
引理 minDegree_of_subsingleton
  条件: [DecidableRel G.Adj] [Subsingleton V]
  结论: G.minDegree = 0
  证明: by
  cases isEmpty_or_nonempty V <;>
    simp [minDegree, Finset.image_const]

@[deprecated (since := "2026-06-15")] alias minDegree_of_isEmpty := minDegree_of_subsingleton

Depends on / 依赖: Finset, Finset.image_const, image_const, isEmpty_or_nonempty, minDegree
-/
lemma minDegree_of_subsingleton [DecidableRel G.Adj] [Subsingleton V] : G.minDegree = 0 := by
  cases isEmpty_or_nonempty V <;>
    simp [minDegree, Finset.image_const]

@[deprecated (since := "2026-06-15")] alias minDegree_of_isEmpty := minDegree_of_subsingleton

variable {G} in
/-- If `G` is a subgraph of `H` then `G.minDegree ≤ H.minDegree`. -/
@[gcongr]
/--
lemma `minDegree_le_minDegree` / 引理 `minDegree_le_minDegree`

English:
lemma minDegree_le_minDegree
  statement: {H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
  proof: by
  cases isEmpty_or_nonempty V
  · simp
  · apply le_minDegree_of_forall_le_degree
    exact fun v => (G.minDegree_le_degree v).trans (G.degree_le_of_le hle)

中文:
引理 minDegree_le_minDegree
  结论: {H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
  证明: by
  cases isEmpty_or_nonempty V
  · simp
  · apply le_minDegree_of_forall_le_degree
    exact fun v => (G.minDegree_le_degree v).trans (G.degree_le_of_le hle)

Depends on / 依赖: G.degree_le_of_le, G.minDegree_le_degree, degree_le_of_le, isEmpty_or_nonempty, le_minDegree_of_forall_le_degree, minDegree_le_degree
-/
lemma minDegree_le_minDegree {H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G <= H) : G.minDegree <= H.minDegree := by
  cases isEmpty_or_nonempty V
  · simp
  · apply le_minDegree_of_forall_le_degree
    exact fun v => (G.minDegree_le_degree v).trans (G.degree_le_of_le hle)

/--
theorem `minDegree_lt_card` / 定理 `minDegree_lt_card`

English:
theorem minDegree_lt_card
  given: [DecidableRel G.Adj] [Nonempty V]
  proof: by
  have ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  apply degree_lt_card_verts

中文:
定理 minDegree_lt_card
  条件: [DecidableRel G.Adj] [Nonempty V]
  证明: by
  have ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  apply degree_lt_card_verts

Depends on / 依赖: Fintype, Fintype.ofFinite, G.exists_minimal_degree_vertex, degree_lt_card_verts, exists_minimal_degree_vertex, infer_instance, ofFinite
-/
theorem minDegree_lt_card [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree < Fintype.card V := by
  have ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  apply degree_lt_card_verts

/--
Definition of `maxDegree` / `maxDegree` 的定义

English:
definition maxDegree
  signature: [DecidableRel G.Adj]
  body: WithBot.unbotD 0 (univ.image fun v => G.degree v).max

中文:
定义 maxDegree
  签名: [DecidableRel G.Adj]
  定义体: WithBot.unbotD 0 (univ.image fun v => G.degree v).max

Depends on / 依赖: Equiv.psigmaEquivSigmaPLift, G.degree, WithBot, WithBot.unbotD, degree, of_equiv, psigmaEquivSigmaPLift, unbotD, univ.image
-/
def maxDegree [DecidableRel G.Adj] : Nat :=
  WithBot.unbotD 0 (univ.image fun v => G.degree v).max

/--
theorem `exists_maximal_degree_vertex` / 定理 `exists_maximal_degree_vertex`

English:
theorem exists_maximal_degree_vertex
  given: [DecidableRel G.Adj] [Nonempty V]
  proof: by
  grind [maxDegree, WithBot.unbotD_coe, max_mem_image_coe <| univ_nonempty.image (G.degree ·)]

中文:
定理 exists_maximal_degree_vertex
  条件: [DecidableRel G.Adj] [Nonempty V]
  证明: by
  grind [maxDegree, WithBot.unbotD_coe, max_mem_image_coe <| univ_nonempty.image (G.degree ·)]

Depends on / 依赖: G.degree, WithBot, WithBot.unbotD_coe, degree, maxDegree, max_mem_image_coe, unbotD_coe, univ_nonempty, univ_nonempty.image
-/
theorem exists_maximal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    exists v, G.maxDegree = G.degree v := by
  grind [maxDegree, WithBot.unbotD_coe, max_mem_image_coe <| univ_nonempty.image (G.degree ·)]

/--
theorem `degree_le_maxDegree` / 定理 `degree_le_maxDegree`

English:
theorem degree_le_maxDegree
  given: [DecidableRel G.Adj] (v : V)
  statement: G.degree v <= G.maxDegree
  proof: WithBot.le_unbotD Finset.le_max mem_image_of_mem (G.degree ·) mem_univ v

@[simp]

中文:
定理 degree_le_maxDegree
  条件: [DecidableRel G.Adj] (v : V)
  结论: G.degree v <= G.maxDegree
  证明: WithBot.le_unbotD Finset.le_max mem_image_of_mem (G.degree ·) mem_univ v

@[simp]

Depends on / 依赖: Finset, Finset.le_max, G.degree, WithBot, WithBot.le_unbotD, degree, le_max, le_unbotD, mem_image_of_mem, mem_univ
-/
theorem degree_le_maxDegree [DecidableRel G.Adj] (v : V) : G.degree v <= G.maxDegree :=
WithBot.le_unbotD Finset.le_max mem_image_of_mem (G.degree ·) mem_univ v

@[simp]
/--
lemma `maxDegree_of_subsingleton` / 引理 `maxDegree_of_subsingleton`

English:
lemma maxDegree_of_subsingleton
  given: [DecidableRel G.Adj] [Subsingleton V]
  statement: G.maxDegree = 0
  proof: by
  cases isEmpty_or_nonempty V <;>
    simp [maxDegree, Finset.image_const]

@[deprecated (since := "2026-06-15")] alias maxDegree_of_isEmpty := maxDegree_of_subsingleton

中文:
引理 maxDegree_of_subsingleton
  条件: [DecidableRel G.Adj] [Subsingleton V]
  结论: G.maxDegree = 0
  证明: by
  cases isEmpty_or_nonempty V <;>
    simp [maxDegree, Finset.image_const]

@[deprecated (since := "2026-06-15")] alias maxDegree_of_isEmpty := maxDegree_of_subsingleton

Depends on / 依赖: Finset, Finset.image_const, image_const, isEmpty_or_nonempty, maxDegree
-/
lemma maxDegree_of_subsingleton [DecidableRel G.Adj] [Subsingleton V] : G.maxDegree = 0 := by
  cases isEmpty_or_nonempty V <;>
    simp [maxDegree, Finset.image_const]

@[deprecated (since := "2026-06-15")] alias maxDegree_of_isEmpty := maxDegree_of_subsingleton

/--
theorem `maxDegree_le_of_forall_degree_le` / 定理 `maxDegree_le_of_forall_degree_le`

English:
theorem maxDegree_le_of_forall_degree_le
  given: [DecidableRel G.Adj] (k : Nat) (h : forall v, G.degree v <= k)
  proof: by
  cases isEmpty_or_nonempty V
  · simp
  · obtain ⟨_, hv⟩ := G.exists_maximal_degree_vertex
    exact hv ▸ h _

中文:
定理 maxDegree_le_of_forall_degree_le
  条件: [DecidableRel G.Adj] (k : 自然数) (h : 对任意 v, G.degree v <= k)
  证明: by
  cases isEmpty_or_nonempty V
  · simp
  · obtain ⟨_, hv⟩ := G.exists_maximal_degree_vertex
    exact hv ▸ h _

Depends on / 依赖: Equiv.plift, Equiv.plift.psumCongr, Equiv.psumEquivSum, G.exists_maximal_degree_vertex, exists_maximal_degree_vertex, isEmpty_or_nonempty, of_equiv, psumCongr, psumEquivSum, symm.trans
-/
theorem maxDegree_le_of_forall_degree_le [DecidableRel G.Adj] (k : Nat) (h : forall v, G.degree v <= k) :
    G.maxDegree <= k := by
  cases isEmpty_or_nonempty V
  · simp
  · obtain ⟨_, hv⟩ := G.exists_maximal_degree_vertex
    exact hv ▸ h _

/--
theorem `IsRegularOfDegree.maxDegree_eq` / 定理 `IsRegularOfDegree.maxDegree_eq`

English:
theorem IsRegularOfDegree.maxDegree_eq
  statement: [Nonempty V] [DecidableRel G.Adj] {d : Nat}
  proof: by
  simp [maxDegree, h.degree_eq, Finset.image_const]

@[simp]

中文:
定理 IsRegularOfDegree.maxDegree_eq
  结论: [Nonempty V] [DecidableRel G.Adj] {d : 自然数}
  证明: by
  simp [maxDegree, h.degree_eq, Finset.image_const]

@[simp]

Depends on / 依赖: Finset, Finset.image_const, degree_eq, h.degree_eq, image_const, maxDegree
-/
theorem IsRegularOfDegree.maxDegree_eq [Nonempty V] [DecidableRel G.Adj] {d : Nat}
    (h : G.IsRegularOfDegree d) : G.maxDegree = d := by
  simp [maxDegree, h.degree_eq, Finset.image_const]

@[simp]
/--
lemma `maxDegree_bot_eq_zero` / 引理 `maxDegree_bot_eq_zero`

English:
lemma maxDegree_bot_eq_zero
  statement: (⊥ : SimpleGraph V).maxDegree = 0
  proof: Nat.le_zero.1 maxDegree_le_of_forall_degree_le _ _ (by simp)

中文:
引理 maxDegree_bot_eq_zero
  结论: (⊥ : SimpleGraph V).maxDegree = 0
  证明: Nat.le_zero.1 maxDegree_le_of_forall_degree_le _ _ (by simp)

Depends on / 依赖: Nat.le_zero, le_zero, maxDegree_le_of_forall_degree_le
-/
lemma maxDegree_bot_eq_zero : (⊥ : SimpleGraph V).maxDegree = 0 :=
Nat.le_zero.1 maxDegree_le_of_forall_degree_le _ _ (by simp)

variable {G} in
@[simp]
/--
theorem `maxDegree_eq_zero_iff` / 定理 `maxDegree_eq_zero_iff`

English:
theorem maxDegree_eq_zero_iff
  given: [DecidableRel G.Adj]
  statement: G.maxDegree = 0 ↔ G = ⊥
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [eq_bot_iff_isIsolated]
    intro v
    grind [degree_eq_zero, G.degree_le_maxDegree v]
  · convert maxDegree_bot_eq_zero
    assumption

@[simp]

中文:
定理 maxDegree_eq_zero_iff
  条件: [DecidableRel G.Adj]
  结论: G.maxDegree = 0 ↔ G = ⊥
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [eq_bot_iff_isIsolated]
    intro v
    grind [degree_eq_zero, G.degree_le_maxDegree v]
  · convert maxDegree_bot_eq_zero
    assumption

@[simp]

Depends on / 依赖: G.degree_le_maxDegree, convert, degree_eq_zero, degree_le_maxDegree, eq_bot_iff_isIsolated, maxDegree_bot_eq_zero
-/
theorem maxDegree_eq_zero_iff [DecidableRel G.Adj] : G.maxDegree = 0 ↔ G = ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [eq_bot_iff_isIsolated]
    intro v
    grind [degree_eq_zero, G.degree_le_maxDegree v]
  · convert maxDegree_bot_eq_zero
    assumption

@[simp]
/--
lemma `maxDegree_top` / 引理 `maxDegree_top`

English:
lemma maxDegree_top
  given: [DecidableEq V]
  statement: (⊤ : SimpleGraph V).maxDegree = Fintype.card V - 1
  proof: by
  cases isEmpty_or_nonempty V
  · simp
  exact IsRegularOfDegree.top.maxDegree_eq

@[simp]

中文:
引理 maxDegree_top
  条件: [DecidableEq V]
  结论: (⊤ : SimpleGraph V).maxDegree = Fintype.card V - 1
  证明: by
  cases isEmpty_or_nonempty V
  · simp
  exact IsRegularOfDegree.top.maxDegree_eq

@[simp]

Depends on / 依赖: IsRegularOfDegree, IsRegularOfDegree.top.maxDegree_eq, isEmpty_or_nonempty, maxDegree_eq
-/
lemma maxDegree_top [DecidableEq V] : (⊤ : SimpleGraph V).maxDegree = Fintype.card V - 1 := by
  cases isEmpty_or_nonempty V
  · simp
  exact IsRegularOfDegree.top.maxDegree_eq

@[simp]
/--
lemma `minDegree_le_maxDegree` / 引理 `minDegree_le_maxDegree`

English:
lemma minDegree_le_maxDegree
  given: [DecidableRel G.Adj]
  statement: G.minDegree <= G.maxDegree
  proof: by
  by_cases! he : IsEmpty V
  · simp
  · exact he.elim fun v => (minDegree_le_degree _ v).trans (degree_le_maxDegree _ v)

中文:
引理 minDegree_le_maxDegree
  条件: [DecidableRel G.Adj]
  结论: G.minDegree <= G.maxDegree
  证明: by
  by_cases! he : IsEmpty V
  · simp
  · exact he.elim fun v => (minDegree_le_degree _ v).trans (degree_le_maxDegree _ v)

Depends on / 依赖: IsEmpty, degree_le_maxDegree, he.elim, minDegree_le_degree
-/
lemma minDegree_le_maxDegree [DecidableRel G.Adj] : G.minDegree <= G.maxDegree := by
  by_cases! he : IsEmpty V
  · simp
  · exact he.elim fun v => (minDegree_le_degree _ v).trans (degree_le_maxDegree _ v)

/--
theorem `IsRegularOfDegree.minDegree_eq` / 定理 `IsRegularOfDegree.minDegree_eq`

English:
theorem IsRegularOfDegree.minDegree_eq
  statement: [Nonempty V] [DecidableRel G.Adj] {d : Nat}
  proof: by
  simp [minDegree, h.degree_eq, Finset.image_const]

@[simp]

中文:
定理 IsRegularOfDegree.minDegree_eq
  结论: [Nonempty V] [DecidableRel G.Adj] {d : 自然数}
  证明: by
  simp [minDegree, h.degree_eq, Finset.image_const]

@[simp]

Depends on / 依赖: Finset, Finset.image_const, degree_eq, h.degree_eq, image_const, minDegree
-/
theorem IsRegularOfDegree.minDegree_eq [Nonempty V] [DecidableRel G.Adj] {d : Nat}
    (h : G.IsRegularOfDegree d) : G.minDegree = d := by
  simp [minDegree, h.degree_eq, Finset.image_const]

@[simp]
/--
lemma `minDegree_bot_eq_zero` / 引理 `minDegree_bot_eq_zero`

English:
lemma minDegree_bot_eq_zero
  statement: (⊥ : SimpleGraph V).minDegree = 0
  proof: Nat.le_zero.1 (minDegree_le_maxDegree _).trans (by simp)

中文:
引理 minDegree_bot_eq_zero
  结论: (⊥ : SimpleGraph V).minDegree = 0
  证明: Nat.le_zero.1 (minDegree_le_maxDegree _).trans (by simp)

Depends on / 依赖: Nat.le_zero, le_zero, minDegree_le_maxDegree
-/
lemma minDegree_bot_eq_zero : (⊥ : SimpleGraph V).minDegree = 0 :=
Nat.le_zero.1 (minDegree_le_maxDegree _).trans (by simp)

variable {G} in
/--
theorem `minDegree_eq_zero_iff` / 定理 `minDegree_eq_zero_iff`

English:
theorem minDegree_eq_zero_iff
  given: [DecidableRel G.Adj] [Nonempty V]
  proof: by
  refine ⟨fun h => ?_, fun ⟨v, hv⟩ => ?_⟩
  · grind [G.exists_minimal_degree_vertex, degree_eq_zero]
  · grind [G.minDegree_le_degree v, degree_eq_zero]

中文:
定理 minDegree_eq_zero_iff
  条件: [DecidableRel G.Adj] [Nonempty V]
  证明: by
  refine ⟨fun h => ?_, fun ⟨v, hv⟩ => ?_⟩
  · grind [G.exists_minimal_degree_vertex, degree_eq_zero]
  · grind [G.minDegree_le_degree v, degree_eq_zero]

Depends on / 依赖: G.exists_minimal_degree_vertex, G.minDegree_le_degree, degree_eq_zero, exists_minimal_degree_vertex, minDegree_le_degree
-/
theorem minDegree_eq_zero_iff [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree = 0 ↔ exists v, G.IsIsolated v := by
  refine ⟨fun h => ?_, fun ⟨v, hv⟩ => ?_⟩
  · grind [G.exists_minimal_degree_vertex, degree_eq_zero]
  · grind [G.minDegree_le_degree v, degree_eq_zero]

variable {G} in
/--
theorem `minDegree_eq_zero_iff_support_ne` / 定理 `minDegree_eq_zero_iff_support_ne`

English:
theorem minDegree_eq_zero_iff_support_ne
  given: [DecidableRel G.Adj] [Nonempty V]
  proof: by
  simp [Set.ne_univ_iff_exists_notMem, minDegree_eq_zero_iff]

@[simp]

中文:
定理 minDegree_eq_zero_iff_support_ne
  条件: [DecidableRel G.Adj] [Nonempty V]
  证明: by
  simp [Set.ne_univ_iff_exists_notMem, minDegree_eq_zero_iff]

@[simp]

Depends on / 依赖: Set.ne_univ_iff_exists_notMem, minDegree_eq_zero_iff, ne_univ_iff_exists_notMem
-/
theorem minDegree_eq_zero_iff_support_ne [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree = 0 ↔ G.support != .univ := by
  simp [Set.ne_univ_iff_exists_notMem, minDegree_eq_zero_iff]

@[simp]
/--
lemma `minDegree_top` / 引理 `minDegree_top`

English:
lemma minDegree_top
  given: [DecidableEq V]
  statement: (⊤ : SimpleGraph V).minDegree = Fintype.card V - 1
  proof: by
  cases isEmpty_or_nonempty V
  · simp
  exact IsRegularOfDegree.top.minDegree_eq

中文:
引理 minDegree_top
  条件: [DecidableEq V]
  结论: (⊤ : SimpleGraph V).minDegree = Fintype.card V - 1
  证明: by
  cases isEmpty_or_nonempty V
  · simp
  exact IsRegularOfDegree.top.minDegree_eq

Depends on / 依赖: IsRegularOfDegree, IsRegularOfDegree.top.minDegree_eq, isEmpty_or_nonempty, minDegree_eq
-/
lemma minDegree_top [DecidableEq V] : (⊤ : SimpleGraph V).minDegree = Fintype.card V - 1 := by
  cases isEmpty_or_nonempty V
  · simp
  exact IsRegularOfDegree.top.minDegree_eq

/--
theorem `maxDegree_lt_card_verts` / 定理 `maxDegree_lt_card_verts`

English:
theorem maxDegree_lt_card_verts
  given: [DecidableRel G.Adj] [Nonempty V]
  proof: by
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  rw [hv]
  apply G.degree_lt_card_verts v

中文:
定理 maxDegree_lt_card_verts
  条件: [DecidableRel G.Adj] [Nonempty V]
  证明: by
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  rw [hv]
  apply G.degree_lt_card_verts v

Depends on / 依赖: G.degree_lt_card_verts, G.exists_maximal_degree_vertex, degree_lt_card_verts, exists_maximal_degree_vertex
-/
theorem maxDegree_lt_card_verts [DecidableRel G.Adj] [Nonempty V] :
    G.maxDegree < Fintype.card V := by
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  rw [hv]
  apply G.degree_lt_card_verts v

/--
theorem `card_commonNeighbors_le_degree_left` / 定理 `card_commonNeighbors_le_degree_left`

English:
theorem card_commonNeighbors_le_degree_left
  given: [DecidableRel G.Adj] (v w : V)
  proof: by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card Set.inter_subset_left

中文:
定理 card_commonNeighbors_le_degree_left
  条件: [DecidableRel G.Adj] (v w : V)
  证明: by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card Set.inter_subset_left

Depends on / 依赖: Set.card_le_card, Set.inter_subset_left, card_le_card, card_neighborSet_eq_degree, inter_subset_left
-/
theorem card_commonNeighbors_le_degree_left [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) <= G.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card Set.inter_subset_left

/--
theorem `card_commonNeighbors_le_degree_right` / 定理 `card_commonNeighbors_le_degree_right`

English:
theorem card_commonNeighbors_le_degree_right
  given: [DecidableRel G.Adj] (v w : V)
  proof: by
  simp_rw [commonNeighbors_symm _ v w, card_commonNeighbors_le_degree_left]

中文:
定理 card_commonNeighbors_le_degree_right
  条件: [DecidableRel G.Adj] (v w : V)
  证明: by
  simp_rw [commonNeighbors_symm _ v w, card_commonNeighbors_le_degree_left]

Depends on / 依赖: card_commonNeighbors_le_degree_left, commonNeighbors_symm, simp_rw
-/
theorem card_commonNeighbors_le_degree_right [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) <= G.degree w := by
  simp_rw [commonNeighbors_symm _ v w, card_commonNeighbors_le_degree_left]

/--
theorem `card_commonNeighbors_lt_card_verts` / 定理 `card_commonNeighbors_lt_card_verts`

English:
theorem card_commonNeighbors_lt_card_verts
  given: [DecidableRel G.Adj] (v w : V)
  proof: Nat.lt_of_le_of_lt (G.card_commonNeighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

中文:
定理 card_commonNeighbors_lt_card_verts
  条件: [DecidableRel G.Adj] (v w : V)
  证明: Nat.lt_of_le_of_lt (G.card_commonNeighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

Depends on / 依赖: G.card_commonNeighbors_le_degree_left, G.degree_lt_card_verts, Nat.lt_of_le_of_lt, card_commonNeighbors_le_degree_left, degree_lt_card_verts, lt_of_le_of_lt
-/
theorem card_commonNeighbors_lt_card_verts [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) < Fintype.card V :=
  Nat.lt_of_le_of_lt (G.card_commonNeighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

/--
theorem `Adj.card_commonNeighbors_lt_degree` / 定理 `Adj.card_commonNeighbors_lt_degree`

English:
theorem Adj.card_commonNeighbors_lt_degree
  statement: {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V}
  proof: by
  classical
  rw [← Set.toFinset_card]
refine Finset.card_lt_card Finset.ssubset_iff.mpr ⟨w, ?_, ?_⟩
  · rw [Set.mem_toFinset]
    apply notMem_commonNeighbors_right
  · simpa [Finset.insert_subset_iff, G.commonNeighbors_subset_neighborSet_left v w]

中文:
定理 Adj.card_commonNeighbors_lt_degree
  结论: {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V}
  证明: by
  classical
  rw [← Set.toFinset_card]
refine Finset.card_lt_card Finset.ssubset_iff.mpr ⟨w, ?_, ?_⟩
  · rw [Set.mem_toFinset]
    apply notMem_commonNeighbors_right
  · simpa [Finset.insert_subset_iff, G.commonNeighbors_subset_neighborSet_left v w]

Depends on / 依赖: Finset, Finset.card_lt_card, Finset.insert_subset_iff, Finset.ssubset_iff.mpr, G.commonNeighbors_subset_neighborSet_left, Set.mem_toFinset, Set.toFinset_card, card_lt_card, classical, commonNeighbors_subset_neighborSet_left, insert_subset_iff, mem_toFinset, notMem_commonNeighbors_right, ssubset_iff, toFinset_card
-/
theorem Adj.card_commonNeighbors_lt_degree {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V}
    (h : G.Adj v w) : Fintype.card (G.commonNeighbors v w) < G.degree v := by
  classical
  rw [← Set.toFinset_card]
refine Finset.card_lt_card Finset.ssubset_iff.mpr ⟨w, ?_, ?_⟩
  · rw [Set.mem_toFinset]
    apply notMem_commonNeighbors_right
  · simpa [Finset.insert_subset_iff, G.commonNeighbors_subset_neighborSet_left v w]

/--
theorem `card_commonNeighbors_top` / 定理 `card_commonNeighbors_top`

English:
theorem card_commonNeighbors_top
  given: [DecidableEq V] {v w : V} (h : v != w)
  proof: by
  simp [commonNeighbors_top_eq, ← Set.toFinset_card, Finset.card_sdiff, h]

中文:
定理 card_commonNeighbors_top
  条件: [DecidableEq V] {v w : V} (h : v != w)
  证明: by
  simp [commonNeighbors_top_eq, ← Set.toFinset_card, Finset.card_sdiff, h]

Depends on / 依赖: Finset, Finset.card_sdiff, Set.toFinset_card, card_sdiff, commonNeighbors_top_eq, toFinset_card
-/
theorem card_commonNeighbors_top [DecidableEq V] {v w : V} (h : v != w) :
    Fintype.card (commonNeighbors ⊤ v w) = Fintype.card V - 2 := by
  simp [commonNeighbors_top_eq, ← Set.toFinset_card, Finset.card_sdiff, h]

/--
lemma `insert_neighborFinset_eq_univ` / 引理 `insert_neighborFinset_eq_univ`

English:
lemma insert_neighborFinset_eq_univ
  given: [DecidableEq V] [DecidableRel G.Adj] (v : V)
  proof: by
  simp only [Finset.ext_iff, mem_insert, mem_neighborFinset, IsUniversal]
  grind

中文:
引理 insert_neighborFinset_eq_univ
  条件: [DecidableEq V] [DecidableRel G.Adj] (v : V)
  证明: by
  simp only [Finset.ext_iff, mem_insert, mem_neighborFinset, IsUniversal]
  grind
-/
@[simp] lemma insert_neighborFinset_eq_univ [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    insert v (G.neighborFinset v) = univ ↔ G.IsUniversal v := by
  simp only [Finset.ext_iff, mem_insert, mem_neighborFinset, IsUniversal]
  grind

/--
lemma `neighborFinset_eq_erase_univ` / 引理 `neighborFinset_eq_erase_univ`

English:
lemma neighborFinset_eq_erase_univ
  given: [DecidableEq V] [DecidableRel G.Adj] (v : V)
  proof: by
  grind [insert_neighborFinset_eq_univ, notMem_neighborFinset_self]

@[simp]

中文:
引理 neighborFinset_eq_erase_univ
  条件: [DecidableEq V] [DecidableRel G.Adj] (v : V)
  证明: by
  grind [insert_neighborFinset_eq_univ, notMem_neighborFinset_self]

@[simp]
-/
@[simp] lemma neighborFinset_eq_erase_univ [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    G.neighborFinset v = univ.erase v ↔ G.IsUniversal v := by
  grind [insert_neighborFinset_eq_univ, notMem_neighborFinset_self]

@[simp]
/--
lemma `degree_eq_card_sub_one` / 引理 `degree_eq_card_sub_one`

English:
lemma degree_eq_card_sub_one
  given: [DecidableRel G.Adj] (v : V)
  proof: by
  classical
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← G.insert_neighborFinset_eq_univ v, ← Finset.card_eq_iff_eq_univ]
    simp [h, Nat.sub_add_cancel <| Fintype.card_pos_iff.mpr ⟨v⟩]
  · simp [← card_neighborFinset_eq_degree, (G.neighborFinset_eq_erase_univ v).mpr h]

中文:
引理 degree_eq_card_sub_one
  条件: [DecidableRel G.Adj] (v : V)
  证明: by
  classical
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← G.insert_neighborFinset_eq_univ v, ← Finset.card_eq_iff_eq_univ]
    simp [h, Nat.sub_add_cancel <| Fintype.card_pos_iff.mpr ⟨v⟩]
  · simp [← card_neighborFinset_eq_degree, (G.neighborFinset_eq_erase_univ v).mpr h]

Depends on / 依赖: Finset, Finset.card_eq_iff_eq_univ, Fintype, Fintype.card_pos_iff.mpr, G.insert_neighborFinset_eq_univ, G.neighborFinset_eq_erase_univ, Nat.sub_add_cancel, card_eq_iff_eq_univ, card_neighborFinset_eq_degree, card_pos_iff, classical, insert_neighborFinset_eq_univ, neighborFinset_eq_erase_univ, sub_add_cancel
-/
lemma degree_eq_card_sub_one [DecidableRel G.Adj] (v : V) :
    G.degree v = Fintype.card V - 1 ↔ G.IsUniversal v := by
  classical
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← G.insert_neighborFinset_eq_univ v, ← Finset.card_eq_iff_eq_univ]
    simp [h, Nat.sub_add_cancel <| Fintype.card_pos_iff.mpr ⟨v⟩]
  · simp [← card_neighborFinset_eq_degree, (G.neighborFinset_eq_erase_univ v).mpr h]

/--
lemma `degree_lt_card_sub_one` / 引理 `degree_lt_card_sub_one`

English:
lemma degree_lt_card_sub_one
  given: [DecidableRel G.Adj] (v : V)
  proof: by
  grind [degree_eq_card_sub_one, Nat.le_sub_one_of_lt <| G.degree_lt_card_verts v]

中文:
引理 degree_lt_card_sub_one
  条件: [DecidableRel G.Adj] (v : V)
  证明: by
  grind [degree_eq_card_sub_one, Nat.le_sub_one_of_lt <| G.degree_lt_card_verts v]

Depends on / 依赖: G.degree_lt_card_verts, Nat.le_sub_one_of_lt, degree_eq_card_sub_one, degree_lt_card_verts, le_sub_one_of_lt
-/
lemma degree_lt_card_sub_one [DecidableRel G.Adj] (v : V) :
    G.degree v < Fintype.card V - 1 ↔ ¬ G.IsUniversal v := by
  grind [degree_eq_card_sub_one, Nat.le_sub_one_of_lt <| G.degree_lt_card_verts v]

end Finite

namespace Iso

variable {G} {W : Type*} {G' : SimpleGraph W}

/--
theorem `card_edgeFinset_eq` / 定理 `card_edgeFinset_eq`

English:
theorem card_edgeFinset_eq
  given: (f : G ≃g G') [Fintype G.edgeSet] [Fintype G'.edgeSet]
  proof: by
  apply Finset.card_eq_of_equiv
  simpa using f.mapEdgeSet

中文:
定理 card_edgeFinset_eq
  条件: (f : G ≃g G') [Fintype G.edgeSet] [Fintype G'.edgeSet]
  证明: by
  apply Finset.card_eq_of_equiv
  simpa using f.mapEdgeSet

Depends on / 依赖: Finset, Finset.card_eq_of_equiv, card_eq_of_equiv, f.mapEdgeSet, mapEdgeSet
-/
theorem card_edgeFinset_eq (f : G ≃g G') [Fintype G.edgeSet] [Fintype G'.edgeSet] :
    #G.edgeFinset = #G'.edgeFinset := by
  apply Finset.card_eq_of_equiv
  simpa using f.mapEdgeSet

/--
theorem `degree_eq` / 定理 `degree_eq`

English:
theorem degree_eq
  statement: (f : G ≃g G') (x : V)
  proof: by
  rw [← card_neighborSet_eq_degree]; rw [← card_neighborSet_eq_degree]; rw [← Fintype.card_congr (mapNeighborSet f x).symm]

中文:
定理 degree_eq
  结论: (f : G ≃g G') (x : V)
  证明: by
  rw [← card_neighborSet_eq_degree]; rw [← card_neighborSet_eq_degree]; rw [← Fintype.card_congr (mapNeighborSet f x).symm]
-/
@[simp] theorem degree_eq (f : G ≃g G') (x : V)
    [Fintype ↑(G.neighborSet x)] [Fintype ↑(G'.neighborSet (f x))] :
    G'.degree (f x) = G.degree x := by
  rw [← card_neighborSet_eq_degree]; rw [← card_neighborSet_eq_degree]; rw [← Fintype.card_congr (mapNeighborSet f x).symm]

variable [Fintype V] [DecidableRel G.Adj] [Fintype W] [DecidableRel G'.Adj]

/--
theorem `minDegree_eq` / 定理 `minDegree_eq`

English:
theorem minDegree_eq
  given: (f : G ≃g G')
  statement: G.minDegree = G'.minDegree
  proof: by
  classical
  have : (G'.degree ·) ∘ f = (G.degree ·) := funext (f.degree_eq ·)
  rw [minDegree]; rw [minDegree]; rw [← this]; rw [← image_image]; rw [Finset.image_univ_of_surjective f.surjective]

中文:
定理 minDegree_eq
  条件: (f : G ≃g G')
  结论: G.minDegree = G'.minDegree
  证明: by
  classical
  have : (G'.degree ·) ∘ f = (G.degree ·) := funext (f.degree_eq ·)
  rw [minDegree]; rw [minDegree]; rw [← this]; rw [← image_image]; rw [Finset.image_univ_of_surjective f.surjective]

Depends on / 依赖: Finset, Finset.image_univ_of_surjective, G.degree, classical, degree, degree_eq, f.degree_eq, f.surjective, image_image, image_univ_of_surjective, minDegree, surjective
-/
theorem minDegree_eq (f : G ≃g G') : G.minDegree = G'.minDegree := by
  classical
  have : (G'.degree ·) ∘ f = (G.degree ·) := funext (f.degree_eq ·)
  rw [minDegree]; rw [minDegree]; rw [← this]; rw [← image_image]; rw [Finset.image_univ_of_surjective f.surjective]

/--
theorem `maxDegree_eq` / 定理 `maxDegree_eq`

English:
theorem maxDegree_eq
  given: (f : G ≃g G')
  statement: G.maxDegree = G'.maxDegree
  proof: by
  classical
  have : (G'.degree ·) ∘ f = (G.degree ·) := funext (f.degree_eq ·)
  rw [maxDegree]; rw [maxDegree]; rw [← this]; rw [← image_image]; rw [Finset.image_univ_of_surjective f.surjective]

中文:
定理 maxDegree_eq
  条件: (f : G ≃g G')
  结论: G.maxDegree = G'.maxDegree
  证明: by
  classical
  have : (G'.degree ·) ∘ f = (G.degree ·) := funext (f.degree_eq ·)
  rw [maxDegree]; rw [maxDegree]; rw [← this]; rw [← image_image]; rw [Finset.image_univ_of_surjective f.surjective]

Depends on / 依赖: Finset, Finset.image_univ_of_surjective, G.degree, classical, degree, degree_eq, f.degree_eq, f.surjective, image_image, image_univ_of_surjective, maxDegree, surjective
-/
theorem maxDegree_eq (f : G ≃g G') : G.maxDegree = G'.maxDegree := by
  classical
  have : (G'.degree ·) ∘ f = (G.degree ·) := funext (f.degree_eq ·)
  rw [maxDegree]; rw [maxDegree]; rw [← this]; rw [← image_image]; rw [Finset.image_univ_of_surjective f.surjective]

end Iso

section Support

variable {s : Set V} [DecidablePred (· in s)] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/--
lemma `edgeFinset_subset_sym2_of_support_subset` / 引理 `edgeFinset_subset_sym2_of_support_subset`

English:
lemma edgeFinset_subset_sym2_of_support_subset
  given: (h : G.support subseteq s)
  proof: by
  rw [← coe_subset]; rw [coe_sym2]; rw [edgeFinset]; rw [Set.coe_toFinset]; rw [Set.coe_toFinset]
  exact edgeSet_subset_sym2_iff.mpr h

中文:
引理 edgeFinset_subset_sym2_of_support_subset
  条件: (h : G.support subseteq s)
  证明: by
  rw [← coe_subset]; rw [coe_sym2]; rw [edgeFinset]; rw [Set.coe_toFinset]; rw [Set.coe_toFinset]
  exact edgeSet_subset_sym2_iff.mpr h

Depends on / 依赖: Set.coe_toFinset, coe_subset, coe_sym2, coe_toFinset, edgeFinset, edgeSet_subset_sym2_iff, edgeSet_subset_sym2_iff.mpr
-/
lemma edgeFinset_subset_sym2_of_support_subset (h : G.support subseteq s) :
    G.edgeFinset subseteq s.toFinset.sym2 := by
  rw [← coe_subset]; rw [coe_sym2]; rw [edgeFinset]; rw [Set.coe_toFinset]; rw [Set.coe_toFinset]
  exact edgeSet_subset_sym2_iff.mpr h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred (· in G.support)
  body: inferInstanceAs DecidablePred (· in { v | exists w, G.Adj v w })

中文:
实例 :
  签名: DecidablePred (· in G.support)
  定义体: inferInstanceAs DecidablePred (· in { v | exists w, G.Adj v w })

Depends on / 依赖: DecidablePred, G.Adj
-/
instance : DecidablePred (· in G.support) :=
inferInstanceAs DecidablePred (· in { v | exists w, G.Adj v w })

/--
theorem `map_edgeFinset_induce` / 定理 `map_edgeFinset_induce`

English:
theorem map_edgeFinset_induce
  given: [DecidableEq V]
  proof: by
  aesop (add simp [Finset.ext_iff, Sym2.exists, Sym2.forall, adj_comm])

中文:
定理 map_edgeFinset_induce
  条件: [DecidableEq V]
  证明: by
  aesop (add simp [Finset.ext_iff, Sym2.exists, Sym2.forall, adj_comm])

Depends on / 依赖: Finset, Finset.ext_iff, Sym2.exists, Sym2.forall, adj_comm, ext_iff
-/
theorem map_edgeFinset_induce [DecidableEq V] :
    (G.induce s).edgeFinset.map (Embedding.subtype (· in s)).sym2Map
      = G.edgeFinset inter s.toFinset.sym2 := by
  aesop (add simp [Finset.ext_iff, Sym2.exists, Sym2.forall, adj_comm])

/--
theorem `map_edgeFinset_induce_of_support_subset` / 定理 `map_edgeFinset_induce_of_support_subset`

English:
theorem map_edgeFinset_induce_of_support_subset
  given: (h : G.support subseteq s)
  proof: by
  classical
  simpa [map_edgeFinset_induce] using edgeFinset_subset_sym2_of_support_subset h

中文:
定理 map_edgeFinset_induce_of_support_subset
  条件: (h : G.support subseteq s)
  证明: by
  classical
  simpa [map_edgeFinset_induce] using edgeFinset_subset_sym2_of_support_subset h

Depends on / 依赖: classical, edgeFinset_subset_sym2_of_support_subset, map_edgeFinset_induce
-/
theorem map_edgeFinset_induce_of_support_subset (h : G.support subseteq s) :
    (G.induce s).edgeFinset.map (Embedding.subtype (· in s)).sym2Map = G.edgeFinset := by
  classical
  simpa [map_edgeFinset_induce] using edgeFinset_subset_sym2_of_support_subset h

/--
theorem `card_edgeFinset_induce_of_support_subset` / 定理 `card_edgeFinset_induce_of_support_subset`

English:
theorem card_edgeFinset_induce_of_support_subset
  given: (h : G.support subseteq s)
  proof: by
  rw [← map_edgeFinset_induce_of_support_subset h]; rw [card_map]

中文:
定理 card_edgeFinset_induce_of_support_subset
  条件: (h : G.support subseteq s)
  证明: by
  rw [← map_edgeFinset_induce_of_support_subset h]; rw [card_map]

Depends on / 依赖: card_map, map_edgeFinset_induce_of_support_subset
-/
theorem card_edgeFinset_induce_of_support_subset (h : G.support subseteq s) :
    #(G.induce s).edgeFinset = #G.edgeFinset := by
  rw [← map_edgeFinset_induce_of_support_subset h]; rw [card_map]

/--
theorem `card_edgeFinset_induce_support` / 定理 `card_edgeFinset_induce_support`

English:
theorem card_edgeFinset_induce_support
  proof: card_edgeFinset_induce_of_support_subset subset_rfl

中文:
定理 card_edgeFinset_induce_support
  证明: card_edgeFinset_induce_of_support_subset subset_rfl

Depends on / 依赖: card_edgeFinset_induce_of_support_subset, subset_rfl
-/
theorem card_edgeFinset_induce_support :
    #(G.induce G.support).edgeFinset = #G.edgeFinset :=
  card_edgeFinset_induce_of_support_subset subset_rfl

/--
theorem `map_neighborFinset_induce` / 定理 `map_neighborFinset_induce`

English:
theorem map_neighborFinset_induce
  given: [DecidableEq V] (v : s)
  proof: by
  ext; simp

中文:
定理 map_neighborFinset_induce
  条件: [DecidableEq V] (v : s)
  证明: by
  ext; simp
-/
theorem map_neighborFinset_induce [DecidableEq V] (v : s) :
    ((G.induce s).neighborFinset v).map (.subtype (· in s)) = G.neighborFinset v inter s.toFinset := by
  ext; simp

/--
theorem `map_neighborFinset_induce_of_neighborSet_subset` / 定理 `map_neighborFinset_induce_of_neighborSet_subset`

English:
theorem map_neighborFinset_induce_of_neighborSet_subset
  given: {v : s} (h : G.neighborSet v subseteq s)
  proof: by
  classical
  rwa [← Set.toFinset_subset_toFinset, ← neighborFinset_def, ← inter_eq_left,
    ← map_neighborFinset_induce v] at h

中文:
定理 map_neighborFinset_induce_of_neighborSet_subset
  条件: {v : s} (h : G.neighborSet v subseteq s)
  证明: by
  classical
  rwa [← Set.toFinset_subset_toFinset, ← neighborFinset_def, ← inter_eq_left,
    ← map_neighborFinset_induce v] at h

Depends on / 依赖: Set.toFinset_subset_toFinset, classical, inter_eq_left, map_neighborFinset_induce, neighborFinset_def, toFinset_subset_toFinset
-/
theorem map_neighborFinset_induce_of_neighborSet_subset {v : s} (h : G.neighborSet v subseteq s) :
    ((G.induce s).neighborFinset v).map (.subtype (· in s)) = G.neighborFinset v := by
  classical
  rwa [← Set.toFinset_subset_toFinset, ← neighborFinset_def, ← inter_eq_left,
    ← map_neighborFinset_induce v] at h

/--
theorem `degree_induce_of_neighborSet_subset` / 定理 `degree_induce_of_neighborSet_subset`

English:
theorem degree_induce_of_neighborSet_subset
  given: {v : s} (h : G.neighborSet v subseteq s)
  proof: by
  simp_rw [← card_neighborFinset_eq_degree,
    ← map_neighborFinset_induce_of_neighborSet_subset h, card_map]

中文:
定理 degree_induce_of_neighborSet_subset
  条件: {v : s} (h : G.neighborSet v subseteq s)
  证明: by
  simp_rw [← card_neighborFinset_eq_degree,
    ← map_neighborFinset_induce_of_neighborSet_subset h, card_map]

Depends on / 依赖: card_map, card_neighborFinset_eq_degree, map_neighborFinset_induce_of_neighborSet_subset, simp_rw
-/
theorem degree_induce_of_neighborSet_subset {v : s} (h : G.neighborSet v subseteq s) :
    (G.induce s).degree v = G.degree v := by
  simp_rw [← card_neighborFinset_eq_degree,
    ← map_neighborFinset_induce_of_neighborSet_subset h, card_map]

/--
theorem `degree_induce_of_support_subset` / 定理 `degree_induce_of_support_subset`

English:
theorem degree_induce_of_support_subset
  given: (h : G.support subseteq s) (v : s)
  proof: degree_induce_of_neighborSet_subset (G.neighborSet_subset_support v).trans h

@[simp]

中文:
定理 degree_induce_of_support_subset
  条件: (h : G.support subseteq s) (v : s)
  证明: degree_induce_of_neighborSet_subset (G.neighborSet_subset_support v).trans h

@[simp]

Depends on / 依赖: G.neighborSet_subset_support, degree_induce_of_neighborSet_subset, neighborSet_subset_support
-/
theorem degree_induce_of_support_subset (h : G.support subseteq s) (v : s) :
    (G.induce s).degree v = G.degree v :=
degree_induce_of_neighborSet_subset (G.neighborSet_subset_support v).trans h

@[simp]
/--
theorem `degree_induce_support` / 定理 `degree_induce_support`

English:
theorem degree_induce_support
  given: (v : G.support)
  proof: degree_induce_of_support_subset subset_rfl v

中文:
定理 degree_induce_support
  条件: (v : G.support)
  证明: degree_induce_of_support_subset subset_rfl v

Depends on / 依赖: degree_induce_of_support_subset, subset_rfl
-/
theorem degree_induce_support (v : G.support) :
    (G.induce G.support).degree v = G.degree v :=
  degree_induce_of_support_subset subset_rfl v

/--
theorem `le_minDegree_induce_of_support_subset` / 定理 `le_minDegree_induce_of_support_subset`

English:
theorem le_minDegree_induce_of_support_subset
  given: (h : G.support subseteq s)
  proof: by
  cases isEmpty_or_nonempty V
  · simp
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp [minDegree_eq_zero_iff_support_ne, Set.subset_empty_iff.mp h, Set.empty_ne_univ]
  have := hs.to_subtype
  refine le_minDegree_of_forall_le_degree _ _ fun v => ?_
  grw [G.minDegree_le_degree v, degree

中文:
定理 le_minDegree_induce_of_support_subset
  条件: (h : G.support subseteq s)
  证明: by
  cases isEmpty_or_nonempty V
  · simp
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp [minDegree_eq_zero_iff_support_ne, Set.subset_empty_iff.mp h, Set.empty_ne_univ]
  have := hs.to_subtype
  refine le_minDegree_of_forall_le_degree _ _ fun v => ?_
  grw [G.minDegree_le_degree v, degree

Depends on / 依赖: G.minDegree_le_degree, Set.empty_ne_univ, Set.subset_empty_iff.mp, degree_induce_of_neighborSet_subset, empty_ne_univ, eq_empty_or_nonempty, hs.to_subtype, isEmpty_or_nonempty, le_minDegree_of_forall_le_degree, minDegree_eq_zero_iff_support_ne, minDegree_le_degree, neighborSet_subset_support, s.eq_empty_or_nonempty, subset_empty_iff, to_subtype
-/
theorem le_minDegree_induce_of_support_subset (h : G.support subseteq s) :
    G.minDegree <= (G.induce s).minDegree := by
  cases isEmpty_or_nonempty V
  · simp
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp [minDegree_eq_zero_iff_support_ne, Set.subset_empty_iff.mp h, Set.empty_ne_univ]
  have := hs.to_subtype
  refine le_minDegree_of_forall_le_degree _ _ fun v => ?_
  grw [G.minDegree_le_degree v, degree_induce_of_neighborSet_subset]
  grw [neighborSet_subset_support, h]

/--
theorem `filter_edgeFinset_toFinset_subset` / 定理 `filter_edgeFinset_toFinset_subset`

English:
theorem filter_edgeFinset_toFinset_subset
  given: [DecidableEq V] (s : Finset V)
  proof: by
  simp [subset_iff, ← mem_sym2_iff, filter_mem_eq_inter]

中文:
定理 filter_edgeFinset_toFinset_subset
  条件: [DecidableEq V] (s : Finset V)
  证明: by
  simp [subset_iff, ← mem_sym2_iff, filter_mem_eq_inter]

Depends on / 依赖: filter_mem_eq_inter, mem_sym2_iff, subset_iff
-/
theorem filter_edgeFinset_toFinset_subset [DecidableEq V] (s : Finset V) :
    {e in G.edgeFinset | e.toFinset subseteq s} = G.edgeFinset inter s.sym2 := by
  simp [subset_iff, ← mem_sym2_iff, filter_mem_eq_inter]

/--
theorem `card_filter_edgeFinset_toFinset_subset` / 定理 `card_filter_edgeFinset_toFinset_subset`

English:
theorem card_filter_edgeFinset_toFinset_subset
  given: [DecidableEq V] (s : Finset V)
  proof: by
  have h := congrArg Finset.card (map_edgeFinset_induce (s := (↑s : Set V)) (G := G))
  rw [card_map]; rw [toFinset_coe] at h
  rw [filter_edgeFinset_toFinset_subset]
  convert h.symm using 1
  congr!

中文:
定理 card_filter_edgeFinset_toFinset_subset
  条件: [DecidableEq V] (s : Finset V)
  证明: by
  have h := congrArg Finset.card (map_edgeFinset_induce (s := (↑s : Set V)) (G := G))
  rw [card_map]; rw [toFinset_coe] at h
  rw [filter_edgeFinset_toFinset_subset]
  convert h.symm using 1
  congr!

Depends on / 依赖: Finset, Finset.card, card_map, convert, filter_edgeFinset_toFinset_subset, h.symm, map_edgeFinset_induce, toFinset_coe
-/
theorem card_filter_edgeFinset_toFinset_subset [DecidableEq V] (s : Finset V) :
    #{e in G.edgeFinset | e.toFinset subseteq s} = #(G.induce ↑s).edgeFinset := by
  have h := congrArg Finset.card (map_edgeFinset_induce (s := (↑s : Set V)) (G := G))
  rw [card_map]; rw [toFinset_coe] at h
  rw [filter_edgeFinset_toFinset_subset]
  convert h.symm using 1
  congr!

end Support

section Map

variable [Fintype V] {W : Type*} [Fintype W] [DecidableEq W]

@[simp]
/--
theorem `edgeFinset_map` / 定理 `edgeFinset_map`

English:
theorem edgeFinset_map
  given: (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj]
  proof: by
  rw [← Finset.coe_inj]
  push_cast
  exact G.edgeSet_map f

中文:
定理 edgeFinset_map
  条件: (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj]
  证明: by
  rw [← Finset.coe_inj]
  push_cast
  exact G.edgeSet_map f

Depends on / 依赖: Finset, Finset.coe_inj, G.edgeSet_map, coe_inj, edgeSet_map
-/
theorem edgeFinset_map (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.map f).edgeFinset = G.edgeFinset.map f.sym2Map := by
  rw [← Finset.coe_inj]
  push_cast
  exact G.edgeSet_map f

/--
theorem `card_edgeFinset_map` / 定理 `card_edgeFinset_map`

English:
theorem card_edgeFinset_map
  given: (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj]
  proof: by
  rw [edgeFinset_map]
  exact G.edgeFinset.card_map f.sym2Map

中文:
定理 card_edgeFinset_map
  条件: (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj]
  证明: by
  rw [edgeFinset_map]
  exact G.edgeFinset.card_map f.sym2Map

Depends on / 依赖: G.edgeFinset.card_map, card_map, edgeFinset, edgeFinset_map, f.sym2Map, sym2Map
-/
theorem card_edgeFinset_map (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    #(G.map f).edgeFinset = #G.edgeFinset := by
  rw [edgeFinset_map]
  exact G.edgeFinset.card_map f.sym2Map

end Map

end SimpleGraph
