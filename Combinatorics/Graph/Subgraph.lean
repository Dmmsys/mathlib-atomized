/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Jun Kwon
-/
module

public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Tactic.TFAE

/-!
# Subgraphs of multigraphs

This file develops the basic theory of subgraphs for multigraphs `Graph α β`:
the subgraph relation, standard classes of subgraphs (spanning, induced, closed),
and the bottom element `⊥`.

## Main definitions

- `H ≤ G`: the subgraph relation as a partial order on graphs. This is the preferred spelling over
  `H.IsSubgraph G` which it is definitionally equal to.
- `H ≤s G` (`Graph.IsSpanningSubgraph`): `H` has the same vertex set as `G`.
- `H ≤i G` (`Graph.IsInducedSubgraph`): `H` contains every ambient link between its vertices.
- `H ≤c G` (`Graph.IsClosedSubgraph`): `H` is a union of components of `G`.
- `⊥`: empty graph with no vertices or edges as its bottom element.

## Implementation notes

Following the overall design of `Graph`, subgraphs are terms of the same type `Graph α β`
rather than a separate `Subgraph` structure. This allows us to reuse notation and lemmas
uniformly and to express the subgraph order directly as a partial order on `Graph α β`.

`G ≤ H` is the canonical spelling for "G is a subgraph of H". This is definitionally equal to
`G.IsSubgraph H` which exists only for implementation reasons.
The explicit `IsSubgraph` structure is defined so that stronger subgraph notions
(such as `IsSpanningSubgraph`, `IsInducedSubgraph`, and `IsClosedSubgraph`) can extend it.
This allows them to inherit fundamental fields and lemmas like `vertexSet_mono` and `edgeSet_mono`
without lemma duplication. However, in statements and proofs, users use `G ≤ H` instead.
The relation `≤` is the `simp` normal form, and the API is developed entirely in terms of it.

## Tags

graphs, subgraph, induced subgraph, spanning subgraph, closed subgraph
-/

public section

variable {α β : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ K : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set α}

open Set

open scoped Sym2

namespace Graph

section Subgraph

/-- `IsSubgraph H G` is NOT the preferred spelling for the subgraph relation. Please use
`H ≤ G` instead. -/
@[mk_iff]
/--
Definition of `IsSubgraph` / `IsSubgraph` 的定义

English:
structure IsSubgraph
  parameters: (H G : Graph α β)
  axioms and operations (2):
    - vertexSet_mono : V(H) subseteq V(G)  [default: by aesop]
    - isLink_mono : forall ⦃e x y⦄, H.IsLink e x y -> G.IsLink e x y  [default: by aesop]

中文:
结构 IsSubgraph
  参数: (H G : Graph α β)
  公理与运算 (2 个):
    - vertexSet_mono : V(H) subseteq V(G)  [默认: by aesop]
    - isLink_mono : 对任意 ⦃e x y⦄, H.IsLink e x y -> G.IsLink e x y  [默认: by aesop]

Depends on / 依赖: G.IsLink, H.IsLink, IsLink, isLink_mono
-/
structure IsSubgraph (H G : Graph α β) : Prop where
  vertexSet_mono : V(H) subseteq V(G) := by aesop
  isLink_mono : forall ⦃e x y⦄, H.IsLink e x y -> G.IsLink e x y := by aesop

attribute [gcongr, grind ->] IsSubgraph.vertexSet_mono

/--
lemma `IsSubgraph.trans` / 引理 `IsSubgraph.trans`

English:
lemma IsSubgraph.trans
  given: (h₁ : H.IsSubgraph G) (h₂ : G.IsSubgraph G₁)
  statement: H.IsSubgraph G₁
  proof: ⟨h₁.1.trans h₂.1, fun _ _ _ h => h₂.2 (h₁.2 h)⟩

中文:
引理 IsSubgraph.trans
  条件: (h₁ : H.IsSubgraph G) (h₂ : G.IsSubgraph G₁)
  结论: H.IsSubgraph G₁
  证明: ⟨h₁.1.trans h₂.1, fun _ _ _ h => h₂.2 (h₁.2 h)⟩
-/
lemma IsSubgraph.trans (h₁ : H.IsSubgraph G) (h₂ : G.IsSubgraph G₁) : H.IsSubgraph G₁ :=
  ⟨h₁.1.trans h₂.1, fun _ _ _ h => h₂.2 (h₁.2 h)⟩

/--
lemma `IsSubgraph.antisymm` / 引理 `IsSubgraph.antisymm`

English:
lemma IsSubgraph.antisymm
  given: (h₁ : H.IsSubgraph G) (h₂ : G.IsSubgraph H)
  statement: H = G
  proof: Graph.ext (h₁.1.antisymm h₂.1) fun _ _ _ => ⟨(h₁.2 ·), (h₂.2 ·)⟩

中文:
引理 IsSubgraph.antisymm
  条件: (h₁ : H.IsSubgraph G) (h₂ : G.IsSubgraph H)
  结论: H = G
  证明: Graph.ext (h₁.1.antisymm h₂.1) fun _ _ _ => ⟨(h₁.2 ·), (h₂.2 ·)⟩

Depends on / 依赖: Graph.ext, antisymm
-/
lemma IsSubgraph.antisymm (h₁ : H.IsSubgraph G) (h₂ : G.IsSubgraph H) : H = G :=
  Graph.ext (h₁.1.antisymm h₂.1) fun _ _ _ => ⟨(h₁.2 ·), (h₂.2 ·)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Graph α β)
  body: IsSubgraph
  le_refl _ := ⟨le_rfl, fun _ _ _ h => h⟩
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm G H h₁ h₂ := h₁.antisymm h₂

@[simp]

中文:
实例 :
  签名: PartialOrder (Graph α β)
  定义体: IsSubgraph
  le_refl _ := ⟨le_rfl, fun _ _ _ h => h⟩
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm G H h₁ h₂ := h₁.antisymm h₂

@[simp]

Depends on / 依赖: IsSubgraph
-/
instance : PartialOrder (Graph α β) where
  le := IsSubgraph
  le_refl _ := ⟨le_rfl, fun _ _ _ h => h⟩
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm G H h₁ h₂ := h₁.antisymm h₂

@[simp]
/--
lemma `isSubgraph_iff_le` / 引理 `isSubgraph_iff_le`

English:
lemma isSubgraph_iff_le
  statement: H.IsSubgraph G ↔ H <= G
  proof: .rfl

@[gcongr]

中文:
引理 isSubgraph_iff_le
  结论: H.IsSubgraph G ↔ H <= G
  证明: .rfl

@[gcongr]
-/
lemma isSubgraph_iff_le : H.IsSubgraph G ↔ H <= G := .rfl

@[gcongr]
/--
lemma `IsLink.mono` / 引理 `IsLink.mono`

English:
lemma IsLink.mono
  given: (hHG : H <= G) (h : H.IsLink e x y)
  statement: G.IsLink e x y
  proof: hHG.2 h

@[gcongr, grind ->]

中文:
引理 IsLink.mono
  条件: (hHG : H <= G) (h : H.IsLink e x y)
  结论: G.IsLink e x y
  证明: hHG.2 h

@[gcongr, grind ->]
-/
lemma IsLink.mono (hHG : H <= G) (h : H.IsLink e x y) : G.IsLink e x y := hHG.2 h

@[gcongr, grind ->]
/--
lemma `IsSubgraph.edgeSet_mono` / 引理 `IsSubgraph.edgeSet_mono`

English:
lemma IsSubgraph.edgeSet_mono
  given: (h : H <= G)
  statement: E(H) subseteq E(G)
  proof: by
  intro e he
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.mono h).edge_mem

中文:
引理 IsSubgraph.edgeSet_mono
  条件: (h : H <= G)
  结论: E(H) subseteq E(G)
  证明: by
  intro e he
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.mono h).edge_mem

Depends on / 依赖: edge_mem, exists_isLink_of_mem_edgeSet
-/
lemma IsSubgraph.edgeSet_mono (h : H <= G) : E(H) subseteq E(G) := by
  intro e he
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.mono h).edge_mem

/--
lemma `IsLink.anti_of_mem` / 引理 `IsLink.anti_of_mem`

English:
lemma IsLink.anti_of_mem
  given: (h : G.IsLink e x y) (hHG : H <= G) (he : e in E(H))
  proof: by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (huv.mono hHG).eq_and_eq_or_eq_and_eq h
  · assumption
  exact huv.symm

中文:
引理 IsLink.anti_of_mem
  条件: (h : G.IsLink e x y) (hHG : H <= G) (he : e in E(H))
  证明: by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (huv.mono hHG).eq_and_eq_or_eq_and_eq h
  · assumption
  exact huv.symm
-/
private lemma IsLink.anti_of_mem (h : G.IsLink e x y) (hHG : H <= G) (he : e in E(H)) :
    H.IsLink e x y := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (huv.mono hHG).eq_and_eq_or_eq_and_eq h
  · assumption
  exact huv.symm

/--
lemma `IsSubgraph.isLink_iff` / 引理 `IsSubgraph.isLink_iff`

English:
lemma IsSubgraph.isLink_iff
  given: (hHG : H <= G) (he : e in E(H))
  statement: H.IsLink e x y ↔ G.IsLink e x y
  proof: ⟨fun h => h.mono hHG, fun h => h.anti_of_mem hHG he⟩

中文:
引理 IsSubgraph.isLink_iff
  条件: (hHG : H <= G) (he : e in E(H))
  结论: H.IsLink e x y ↔ G.IsLink e x y
  证明: ⟨fun h => h.mono hHG, fun h => h.anti_of_mem hHG he⟩

Depends on / 依赖: anti_of_mem, h.anti_of_mem, h.mono
-/
lemma IsSubgraph.isLink_iff (hHG : H <= G) (he : e in E(H)) : H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨fun h => h.mono hHG, fun h => h.anti_of_mem hHG he⟩

/--
lemma `IsSubgraph.isLink_eqOn` / 引理 `IsSubgraph.isLink_eqOn`

English:
lemma IsSubgraph.isLink_eqOn
  given: (hHG : H <= G)
  statement: EqOn H.IsLink G.IsLink E(H)
  proof: by
  rintro e he
  ext x y
  exact isLink_iff hHG he

中文:
引理 IsSubgraph.isLink_eqOn
  条件: (hHG : H <= G)
  结论: EqOn H.IsLink G.IsLink E(H)
  证明: by
  rintro e he
  ext x y
  exact isLink_iff hHG he

Depends on / 依赖: isLink_iff
-/
lemma IsSubgraph.isLink_eqOn (hHG : H <= G) : EqOn H.IsLink G.IsLink E(H) := by
  rintro e he
  ext x y
  exact isLink_iff hHG he

/--
lemma `Compatible.of_le_le` / 引理 `Compatible.of_le_le`

English:
lemma Compatible.of_le_le
  given: (hH₁G : H₁ <= G) (hH₂G : H₂ <= G)
  statement: H₁.Compatible H₂
  proof: .trans (hH₂G.isLink_iff he₂).symm fun _ he₁ he₂ _ _ => hH₁G.isLink_iff he₁

中文:
引理 Compatible.of_le_le
  条件: (hH₁G : H₁ <= G) (hH₂G : H₂ <= G)
  结论: H₁.Compatible H₂
  证明: .trans (hH₂G.isLink_iff he₂).symm fun _ he₁ he₂ _ _ => hH₁G.isLink_iff he₁

Depends on / 依赖: G.isLink_iff, isLink_iff
-/
lemma Compatible.of_le_le (hH₁G : H₁ <= G) (hH₂G : H₂ <= G) : H₁.Compatible H₂ :=
.trans (hH₂G.isLink_iff he₂).symm fun _ he₁ he₂ _ _ => hH₁G.isLink_iff he₁

/--
lemma `Compatible.of_le` / 引理 `Compatible.of_le`

English:
lemma Compatible.of_le
  given: (hHG : H <= G)
  statement: H.Compatible G
  proof: .of_le_le hHG le_rfl

中文:
引理 Compatible.of_le
  条件: (hHG : H <= G)
  结论: H.Compatible G
  证明: .of_le_le hHG le_rfl

Depends on / 依赖: le_rfl, of_le_le
-/
lemma Compatible.of_le (hHG : H <= G) : H.Compatible G := .of_le_le hHG le_rfl
/--
lemma `Compatible.of_ge` / 引理 `Compatible.of_ge`

English:
lemma Compatible.of_ge
  given: (hHG : G <= H)
  statement: H.Compatible G
  proof: .of_le_le le_rfl hHG

alias IsSubgraph.compatible := Compatible.of_le
alias IsSubgraph.compatible' := Compatible.of_ge

中文:
引理 Compatible.of_ge
  条件: (hHG : G <= H)
  结论: H.Compatible G
  证明: .of_le_le le_rfl hHG

alias IsSubgraph.compatible := Compatible.of_le
alias IsSubgraph.compatible' := Compatible.of_ge

Depends on / 依赖: le_rfl, of_le_le
-/
lemma Compatible.of_ge (hHG : G <= H) : H.Compatible G := .of_le_le le_rfl hHG

alias IsSubgraph.compatible := Compatible.of_le
alias IsSubgraph.compatible' := Compatible.of_ge

/--
lemma `Compatible.anti_left` / 引理 `Compatible.anti_left`

English:
lemma Compatible.anti_left
  given: (hG₁G : G₁ <= G) (h : Compatible G H)
  statement: Compatible G₁ H
  proof: .trans h (hG₁G.edgeSet_mono he₁) he₂ .. fun _ he₁ he₂ _ _ => hG₁G.isLink_iff he₁

中文:
引理 Compatible.anti_left
  条件: (hG₁G : G₁ <= G) (h : Compatible G H)
  结论: Compatible G₁ H
  证明: .trans h (hG₁G.edgeSet_mono he₁) he₂ .. fun _ he₁ he₂ _ _ => hG₁G.isLink_iff he₁

Depends on / 依赖: G.edgeSet_mono, G.isLink_iff, edgeSet_mono, isLink_iff
-/
lemma Compatible.anti_left (hG₁G : G₁ <= G) (h : Compatible G H) : Compatible G₁ H :=
.trans h (hG₁G.edgeSet_mono he₁) he₂ .. fun _ he₁ he₂ _ _ => hG₁G.isLink_iff he₁

/--
lemma `Compatible.anti_right` / 引理 `Compatible.anti_right`

English:
lemma Compatible.anti_right
  given: (hH₁H : H₁ <= H) (h : Compatible G H)
  statement: Compatible G H₁
  proof: (h.symm.anti_left hH₁H).symm

中文:
引理 Compatible.anti_right
  条件: (hH₁H : H₁ <= H) (h : Compatible G H)
  结论: Compatible G H₁
  证明: (h.symm.anti_left hH₁H).symm

Depends on / 依赖: anti_left, h.symm.anti_left
-/
lemma Compatible.anti_right (hH₁H : H₁ <= H) (h : Compatible G H) : Compatible G H₁ :=
  (h.symm.anti_left hH₁H).symm

/--
lemma `Compatible.anti` / 引理 `Compatible.anti`

English:
lemma Compatible.anti
  given: (hG₁G : G₁ <= G) (hH₁H : H₁ <= H) (h : G.Compatible H)
  statement: G₁.Compatible H₁
  proof: (h.anti_left hG₁G).anti_right hH₁H

@[gcongr]

中文:
引理 Compatible.anti
  条件: (hG₁G : G₁ <= G) (hH₁H : H₁ <= H) (h : G.Compatible H)
  结论: G₁.Compatible H₁
  证明: (h.anti_left hG₁G).anti_right hH₁H

@[gcongr]

Depends on / 依赖: anti_left, anti_right, h.anti_left
-/
lemma Compatible.anti (hG₁G : G₁ <= G) (hH₁H : H₁ <= H) (h : G.Compatible H) : G₁.Compatible H₁ :=
  (h.anti_left hG₁G).anti_right hH₁H

@[gcongr]
/--
lemma `Inc.mono` / 引理 `Inc.mono`

English:
lemma Inc.mono
  given: (hHG : H <= G) (h : H.Inc e x)
  statement: G.Inc e x
  proof: (h.choose_spec.mono hHG).inc_left

中文:
引理 Inc.mono
  条件: (hHG : H <= G) (h : H.Inc e x)
  结论: G.Inc e x
  证明: (h.choose_spec.mono hHG).inc_left

Depends on / 依赖: choose_spec, h.choose_spec.mono, inc_left
-/
lemma Inc.mono (hHG : H <= G) (h : H.Inc e x) : G.Inc e x :=
  (h.choose_spec.mono hHG).inc_left

/--
lemma `IsSubgraph.inc_congr` / 引理 `IsSubgraph.inc_congr`

English:
lemma IsSubgraph.inc_congr
  given: (hHG : H <= G) (he : e in E(H))
  statement: H.Inc e x ↔ G.Inc e x
  proof: by
  simp_rw [Graph.Inc, hHG.isLink_iff he]

中文:
引理 IsSubgraph.inc_congr
  条件: (hHG : H <= G) (he : e in E(H))
  结论: H.Inc e x ↔ G.Inc e x
  证明: by
  simp_rw [Graph.Inc, hHG.isLink_iff he]

Depends on / 依赖: Graph.Inc, hHG.isLink_iff, isLink_iff, simp_rw
-/
lemma IsSubgraph.inc_congr (hHG : H <= G) (he : e in E(H)) : H.Inc e x ↔ G.Inc e x := by
  simp_rw [Graph.Inc, hHG.isLink_iff he]

/--
lemma `IsSubgraph.inc_eqOn` / 引理 `IsSubgraph.inc_eqOn`

English:
lemma IsSubgraph.inc_eqOn
  given: (hHG : H <= G)
  statement: EqOn H.Inc G.Inc E(H)
  proof: by
  rintro e he
  ext x
  exact hHG.inc_congr he

中文:
引理 IsSubgraph.inc_eqOn
  条件: (hHG : H <= G)
  结论: EqOn H.Inc G.Inc E(H)
  证明: by
  rintro e he
  ext x
  exact hHG.inc_congr he

Depends on / 依赖: hHG.inc_congr, inc_congr
-/
lemma IsSubgraph.inc_eqOn (hHG : H <= G) : EqOn H.Inc G.Inc E(H) := by
  rintro e he
  ext x
  exact hHG.inc_congr he

/--
lemma `IsLoopAt.mono` / 引理 `IsLoopAt.mono`

English:
lemma IsLoopAt.mono
  given: (hHG : H <= G) (h : H.IsLoopAt e x)
  statement: G.IsLoopAt e x
  proof: IsLink.mono hHG h

中文:
引理 IsLoopAt.mono
  条件: (hHG : H <= G) (h : H.IsLoopAt e x)
  结论: G.IsLoopAt e x
  证明: IsLink.mono hHG h

Depends on / 依赖: IsLink, IsLink.mono
-/
lemma IsLoopAt.mono (hHG : H <= G) (h : H.IsLoopAt e x) : G.IsLoopAt e x :=
  IsLink.mono hHG h

/--
lemma `IsSubgraph.isLoopAt_congr` / 引理 `IsSubgraph.isLoopAt_congr`

English:
lemma IsSubgraph.isLoopAt_congr
  given: (hHG : H <= G) (he : e in E(H))
  proof: by
  unfold Graph.IsLoopAt
  rw [hHG.isLink_iff he]

中文:
引理 IsSubgraph.isLoopAt_congr
  条件: (hHG : H <= G) (he : e in E(H))
  证明: by
  unfold Graph.IsLoopAt
  rw [hHG.isLink_iff he]

Depends on / 依赖: Graph.IsLoopAt, IsLoopAt, hHG.isLink_iff, isLink_iff
-/
lemma IsSubgraph.isLoopAt_congr (hHG : H <= G) (he : e in E(H)) :
    H.IsLoopAt e x ↔ G.IsLoopAt e x := by
  unfold Graph.IsLoopAt
  rw [hHG.isLink_iff he]

/--
lemma `IsSubgraph.isLoopAt_eqOn` / 引理 `IsSubgraph.isLoopAt_eqOn`

English:
lemma IsSubgraph.isLoopAt_eqOn
  given: (hHG : H <= G)
  statement: EqOn H.IsLoopAt G.IsLoopAt E(H)
  proof: by
  rintro e he
  ext x
  exact hHG.isLoopAt_congr he

中文:
引理 IsSubgraph.isLoopAt_eqOn
  条件: (hHG : H <= G)
  结论: EqOn H.IsLoopAt G.IsLoopAt E(H)
  证明: by
  rintro e he
  ext x
  exact hHG.isLoopAt_congr he

Depends on / 依赖: hHG.isLoopAt_congr, isLoopAt_congr
-/
lemma IsSubgraph.isLoopAt_eqOn (hHG : H <= G) : EqOn H.IsLoopAt G.IsLoopAt E(H) := by
  rintro e he
  ext x
  exact hHG.isLoopAt_congr he

/--
lemma `IsNonloopAt.mono` / 引理 `IsNonloopAt.mono`

English:
lemma IsNonloopAt.mono
  given: (hHG : H <= G) (h : H.IsNonloopAt e x)
  statement: G.IsNonloopAt e x
  proof: by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, hxy, he.mono hHG⟩

中文:
引理 IsNonloopAt.mono
  条件: (hHG : H <= G) (h : H.IsNonloopAt e x)
  结论: G.IsNonloopAt e x
  证明: by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, hxy, he.mono hHG⟩

Depends on / 依赖: he.mono
-/
lemma IsNonloopAt.mono (hHG : H <= G) (h : H.IsNonloopAt e x) : G.IsNonloopAt e x := by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, hxy, he.mono hHG⟩

/--
lemma `IsSubgraph.isNonloopAt_congr` / 引理 `IsSubgraph.isNonloopAt_congr`

English:
lemma IsSubgraph.isNonloopAt_congr
  given: (hHG : H <= G) (he : e in E(H))
  proof: by
  simp_rw [Graph.IsNonloopAt, hHG.isLink_iff he]

中文:
引理 IsSubgraph.isNonloopAt_congr
  条件: (hHG : H <= G) (he : e in E(H))
  证明: by
  simp_rw [Graph.IsNonloopAt, hHG.isLink_iff he]

Depends on / 依赖: Graph.IsNonloopAt, IsNonloopAt, hHG.isLink_iff, isLink_iff, simp_rw
-/
lemma IsSubgraph.isNonloopAt_congr (hHG : H <= G) (he : e in E(H)) :
    H.IsNonloopAt e x ↔ G.IsNonloopAt e x := by
  simp_rw [Graph.IsNonloopAt, hHG.isLink_iff he]

/--
lemma `IsSubgraph.isNonloopAt_eqOn` / 引理 `IsSubgraph.isNonloopAt_eqOn`

English:
lemma IsSubgraph.isNonloopAt_eqOn
  given: (hHG : H <= G)
  statement: EqOn H.IsNonloopAt G.IsNonloopAt E(H)
  proof: by
  rintro e he
  ext x
  exact hHG.isNonloopAt_congr he

@[gcongr]

中文:
引理 IsSubgraph.isNonloopAt_eqOn
  条件: (hHG : H <= G)
  结论: EqOn H.IsNonloopAt G.IsNonloopAt E(H)
  证明: by
  rintro e he
  ext x
  exact hHG.isNonloopAt_congr he

@[gcongr]

Depends on / 依赖: hHG.isNonloopAt_congr, isNonloopAt_congr
-/
lemma IsSubgraph.isNonloopAt_eqOn (hHG : H <= G) : EqOn H.IsNonloopAt G.IsNonloopAt E(H) := by
  rintro e he
  ext x
  exact hHG.isNonloopAt_congr he

@[gcongr]
/--
lemma `Adj.mono` / 引理 `Adj.mono`

English:
lemma Adj.mono
  given: (hHG : H <= G) (h : H.Adj x y)
  statement: G.Adj x y
  proof: (h.choose_spec.mono hHG).adj

中文:
引理 Adj.mono
  条件: (hHG : H <= G) (h : H.Adj x y)
  结论: G.Adj x y
  证明: (h.choose_spec.mono hHG).adj

Depends on / 依赖: choose_spec, h.choose_spec.mono
-/
lemma Adj.mono (hHG : H <= G) (h : H.Adj x y) : G.Adj x y :=
  (h.choose_spec.mono hHG).adj

/--
lemma `le_iff_compatible_subset_subset` / 引理 `le_iff_compatible_subset_subset`

English:
lemma le_iff_compatible_subset_subset
  statement: G <= H ↔ Compatible G H ∧ V(G) subseteq V(H) ∧ E(G) subseteq E(H)
  proof: ⟨fun h => ⟨.of_le h, h.1, h.edgeSet_mono⟩, fun ⟨h, hV, hE⟩ =>
.mp hxy⟩⟩ ⟨hV, fun _ _ _ hxy => h hxy.edge_mem (hE hxy.edge_mem) ..

中文:
引理 le_iff_compatible_subset_subset
  结论: G <= H ↔ Compatible G H ∧ V(G) subseteq V(H) ∧ E(G) subseteq E(H)
  证明: ⟨fun h => ⟨.of_le h, h.1, h.edgeSet_mono⟩, fun ⟨h, hV, hE⟩ =>
.mp hxy⟩⟩ ⟨hV, fun _ _ _ hxy => h hxy.edge_mem (hE hxy.edge_mem) ..

Depends on / 依赖: edgeSet_mono, edge_mem, h.edgeSet_mono, hxy.edge_mem, of_le
-/
lemma le_iff_compatible_subset_subset : G <= H ↔ Compatible G H ∧ V(G) subseteq V(H) ∧ E(G) subseteq E(H) :=
  ⟨fun h => ⟨.of_le h, h.1, h.edgeSet_mono⟩, fun ⟨h, hV, hE⟩ =>
.mp hxy⟩⟩ ⟨hV, fun _ _ _ hxy => h hxy.edge_mem (hE hxy.edge_mem) ..

/--
lemma `Compatible.le_iff` / 引理 `Compatible.le_iff`

English:
lemma Compatible.le_iff
  given: (hH : Compatible H₁ H₂)
  statement: H₁ <= H₂ ↔ V(H₁) subseteq V(H₂) ∧ E(H₁) subseteq E(H₂)
  proof: le_iff_compatible_subset_subset.trans (by tauto)

中文:
引理 Compatible.le_iff
  条件: (hH : Compatible H₁ H₂)
  结论: H₁ <= H₂ ↔ V(H₁) subseteq V(H₂) ∧ E(H₁) subseteq E(H₂)
  证明: le_iff_compatible_subset_subset.trans (by tauto)

Depends on / 依赖: le_iff_compatible_subset_subset, le_iff_compatible_subset_subset.trans
-/
lemma Compatible.le_iff (hH : Compatible H₁ H₂) : H₁ <= H₂ ↔ V(H₁) subseteq V(H₂) ∧ E(H₁) subseteq E(H₂) :=
  le_iff_compatible_subset_subset.trans (by tauto)

/--
lemma `Compatible.ext` / 引理 `Compatible.ext`

English:
lemma Compatible.ext
  given: (hV : V(H₁) = V(H₂)) (hE : E(H₁) = E(H₂)) (h : Compatible H₁ H₂)
  statement: H₁ = H₂
  proof: (h.le_iff.mpr ⟨hV.subset, hE.subset⟩).antisymm h.symm.le_iff.mpr ⟨hV.superset, hE.superset⟩

中文:
引理 Compatible.ext
  条件: (hV : V(H₁) = V(H₂)) (hE : E(H₁) = E(H₂)) (h : Compatible H₁ H₂)
  结论: H₁ = H₂
  证明: (h.le_iff.mpr ⟨hV.subset, hE.subset⟩).antisymm h.symm.le_iff.mpr ⟨hV.superset, hE.superset⟩

Depends on / 依赖: antisymm, h.le_iff.mpr, h.symm.le_iff.mpr, hE.subset, hE.superset, hV.subset, hV.superset, le_iff, subset, superset
-/
lemma Compatible.ext (hV : V(H₁) = V(H₂)) (hE : E(H₁) = E(H₂)) (h : Compatible H₁ H₂) : H₁ = H₂ :=
(h.le_iff.mpr ⟨hV.subset, hE.subset⟩).antisymm h.symm.le_iff.mpr ⟨hV.superset, hE.superset⟩

/--
lemma `vertexSet_ssubset_or_edgeSet_ssubset_of_lt` / 引理 `vertexSet_ssubset_or_edgeSet_ssubset_of_lt`

English:
lemma vertexSet_ssubset_or_edgeSet_ssubset_of_lt
  given: (hGH : G < H)
  statement: V(G) ⊂ V(H) ∨ E(G) ⊂ E(H)
  proof: by
  rw [lt_iff_le_and_ne] at hGH
  simp only [ssubset_iff_subset_ne, hGH.1.vertexSet_mono, ne_eq, true_and, hGH.1.edgeSet_mono]
  by_contra! heq
exact hGH.2 hGH.1.compatible.ext heq.1 heq.2

@[simp]

中文:
引理 vertexSet_ssubset_or_edgeSet_ssubset_of_lt
  条件: (hGH : G < H)
  结论: V(G) ⊂ V(H) ∨ E(G) ⊂ E(H)
  证明: by
  rw [lt_iff_le_and_ne] at hGH
  simp only [ssubset_iff_subset_ne, hGH.1.vertexSet_mono, ne_eq, true_and, hGH.1.edgeSet_mono]
  by_contra! heq
exact hGH.2 hGH.1.compatible.ext heq.1 heq.2

@[simp]

Depends on / 依赖: compatible, compatible.ext, edgeSet_mono, lt_iff_le_and_ne, ne_eq, ssubset_iff_subset_ne, true_and, vertexSet_mono
-/
lemma vertexSet_ssubset_or_edgeSet_ssubset_of_lt (hGH : G < H) : V(G) ⊂ V(H) ∨ E(G) ⊂ E(H) := by
  rw [lt_iff_le_and_ne] at hGH
  simp only [ssubset_iff_subset_ne, hGH.1.vertexSet_mono, ne_eq, true_and, hGH.1.edgeSet_mono]
  by_contra! heq
exact hGH.2 hGH.1.compatible.ext heq.1 heq.2

@[simp]
/--
lemma `noEdge_le_iff` / 引理 `noEdge_le_iff`

English:
lemma noEdge_le_iff
  statement: noEdge X β <= G ↔ X subseteq V(G)
  proof: ⟨(·.vertexSet_mono), fun h => ⟨h, by simp⟩⟩

@[simp]

中文:
引理 noEdge_le_iff
  结论: noEdge X β <= G ↔ X subseteq V(G)
  证明: ⟨(·.vertexSet_mono), fun h => ⟨h, by simp⟩⟩

@[simp]

Depends on / 依赖: vertexSet_mono
-/
lemma noEdge_le_iff : noEdge X β <= G ↔ X subseteq V(G) := ⟨(·.vertexSet_mono), fun h => ⟨h, by simp⟩⟩

@[simp]
/--
lemma `le_noEdge_iff` / 引理 `le_noEdge_iff`

English:
lemma le_noEdge_iff
  statement: G <= noEdge X β ↔ V(G) subseteq X ∧ E(G) = ∅
  proof: ⟨fun h => ⟨h.vertexSet_mono, subset_empty_iff.1 h.edgeSet_mono⟩,
    fun h => ⟨h.1, fun e x y he => by simpa [h] using he.edge_mem⟩⟩

中文:
引理 le_noEdge_iff
  结论: G <= noEdge X β ↔ V(G) subseteq X ∧ E(G) = ∅
  证明: ⟨fun h => ⟨h.vertexSet_mono, subset_empty_iff.1 h.edgeSet_mono⟩,
    fun h => ⟨h.1, fun e x y he => by simpa [h] using he.edge_mem⟩⟩

Depends on / 依赖: edgeSet_mono, edge_mem, h.edgeSet_mono, h.vertexSet_mono, he.edge_mem, subset_empty_iff, vertexSet_mono
-/
lemma le_noEdge_iff : G <= noEdge X β ↔ V(G) subseteq X ∧ E(G) = ∅ :=
  ⟨fun h => ⟨h.vertexSet_mono, subset_empty_iff.1 h.edgeSet_mono⟩,
    fun h => ⟨h.1, fun e x y he => by simpa [h] using he.edge_mem⟩⟩

end Subgraph

section SpanningSubgraph

/-! ### Spanning Subgraphs -/

/-- `H ≤s G` (`Graph.IsSpanningSubgraph`) is a subgraph of `G` with the same vertex set. -/
@[mk_iff]
/--
Definition of `IsSpanningSubgraph` / `IsSpanningSubgraph` 的定义

English:
structure IsSpanningSubgraph
  parameters: (H G : Graph α β)
  extends: le : H <= G
  axioms and operations (1):
    - vertexSet_eq : V(H) = V(G)

中文:
结构 IsSpanningSubgraph
  参数: (H G : Graph α β)
  继承: le : H <= G
  公理与运算 (1 个):
    - vertexSet_eq : V(H) = V(G)
-/
structure IsSpanningSubgraph (H G : Graph α β) : Prop extends le : H <= G where
  vertexSet_eq : V(H) = V(G)

@[inherit_doc IsSpanningSubgraph]
infixl:50 " <=s " => Graph.IsSpanningSubgraph

namespace IsSpanningSubgraph

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: (h₁ : G <=s G₁) (h₂ : G₁ <=s G₂)
  statement: G <=s G₂
  proof: ⟨h₁.le.trans h₂.le, h₁.vertexSet_eq.trans h₂.vertexSet_eq⟩

中文:
引理 trans
  条件: (h₁ : G <=s G₁) (h₂ : G₁ <=s G₂)
  结论: G <=s G₂
  证明: ⟨h₁.le.trans h₂.le, h₁.vertexSet_eq.trans h₂.vertexSet_eq⟩
-/
protected lemma trans (h₁ : G <=s G₁) (h₂ : G₁ <=s G₂) : G <=s G₂ :=
  ⟨h₁.le.trans h₂.le, h₁.vertexSet_eq.trans h₂.vertexSet_eq⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPartialOrder (Graph α β) (· <=s ·)
  body: ⟨le_refl G, rfl⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.1.antisymm h₂.1

中文:
实例 :
  签名: IsPartialOrder (Graph α β) (· <=s ·)
  定义体: ⟨le_refl G, rfl⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.1.antisymm h₂.1

Depends on / 依赖: le_refl
-/
instance : IsPartialOrder (Graph α β) (· <=s ·) where
  refl G := ⟨le_refl G, rfl⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.1.antisymm h₂.1

/--
lemma `rfl` / 引理 `rfl`

English:
lemma rfl
  statement: G <=s G
  proof: refl G

中文:
引理 rfl
  结论: G <=s G
  证明: refl G
-/
@[simp] protected lemma rfl : G <=s G := refl G

/--
lemma `anti_right` / 引理 `anti_right`

English:
lemma anti_right
  given: (hHK : H <= K) (hKG : K <= G) (h : H <=s G)
  statement: H <=s K where
  proof: hHK
vertexSet_eq := hHK.vertexSet_mono.antisymm hKG.vertexSet_mono.trans_eq h.vertexSet_eq.symm

中文:
引理 anti_right
  条件: (hHK : H <= K) (hKG : K <= G) (h : H <=s G)
  结论: H <=s K where
  证明: hHK
vertexSet_eq := hHK.vertexSet_mono.antisymm hKG.vertexSet_mono.trans_eq h.vertexSet_eq.symm
-/
lemma anti_right (hHK : H <= K) (hKG : K <= G) (h : H <=s G) : H <=s K where
  le := hHK
vertexSet_eq := hHK.vertexSet_mono.antisymm hKG.vertexSet_mono.trans_eq h.vertexSet_eq.symm

/--
lemma `mono_left` / 引理 `mono_left`

English:
lemma mono_left
  given: (hHK : H <= K) (hKG : K <= G) (h : H <=s G)
  statement: K <=s G where
  proof: hKG
vertexSet_eq := hKG.vertexSet_mono.antisymm h.vertexSet_eq.symm.le.trans hHK.vertexSet_mono

中文:
引理 mono_left
  条件: (hHK : H <= K) (hKG : K <= G) (h : H <=s G)
  结论: K <=s G where
  证明: hKG
vertexSet_eq := hKG.vertexSet_mono.antisymm h.vertexSet_eq.symm.le.trans hHK.vertexSet_mono
-/
lemma mono_left (hHK : H <= K) (hKG : K <= G) (h : H <=s G) : K <=s G where
  le := hKG
vertexSet_eq := hKG.vertexSet_mono.antisymm h.vertexSet_eq.symm.le.trans hHK.vertexSet_mono

/--
lemma `ext_of_edgeSet` / 引理 `ext_of_edgeSet`

English:
lemma ext_of_edgeSet
  given: (hE : E(H) = E(G)) (h : H <=s G)
  statement: H = G
  proof: h.compatible.ext h.vertexSet_eq hE

@[gcongr]

中文:
引理 ext_of_edgeSet
  条件: (hE : E(H) = E(G)) (h : H <=s G)
  结论: H = G
  证明: h.compatible.ext h.vertexSet_eq hE

@[gcongr]

Depends on / 依赖: compatible, h.compatible.ext, h.vertexSet_eq, vertexSet_eq
-/
lemma ext_of_edgeSet (hE : E(H) = E(G)) (h : H <=s G) : H = G :=
  h.compatible.ext h.vertexSet_eq hE

@[gcongr]
/--
lemma `banana_mono` / 引理 `banana_mono`

English:
lemma banana_mono
  given: (hF : F₁ subseteq F₂)
  statement: banana u v F₁ <=s banana u v F₂ where
  proof: rfl

中文:
引理 banana_mono
  条件: (hF : F₁ subseteq F₂)
  结论: banana u v F₁ <=s banana u v F₂ where
  证明: rfl
-/
lemma banana_mono (hF : F₁ subseteq F₂) : banana u v F₁ <=s banana u v F₂ where
  vertexSet_eq := rfl

end IsSpanningSubgraph

end SpanningSubgraph

section InducedSubgraph

/-! ### Induced Subgraphs -/

/-- `H ≤i G` (`Graph.IsInducedSubgraph`) is a subgraph of `G` such that every link of `G`
involving two vertices of `H` is also a link of `H`. -/
@[mk_iff]
/--
Definition of `IsInducedSubgraph` / `IsInducedSubgraph` 的定义

English:
structure IsInducedSubgraph
  parameters: (H G : Graph α β)
  extends: le : H <= G
  axioms and operations (1):
    - isLink_of_mem_mem : forall ⦃e x y⦄, G.IsLink e x y -> x in V(H) -> y in V(H) -> H.IsLink e x y

中文:
结构 IsInducedSubgraph
  参数: (H G : Graph α β)
  继承: le : H <= G
  公理与运算 (1 个):
    - isLink_of_mem_mem : 对任意 ⦃e x y⦄, G.IsLink e x y -> x in V(H) -> y in V(H) -> H.IsLink e x y
-/
structure IsInducedSubgraph (H G : Graph α β) : Prop extends le : H <= G where
  isLink_of_mem_mem : forall ⦃e x y⦄, G.IsLink e x y -> x in V(H) -> y in V(H) -> H.IsLink e x y

@[inherit_doc IsInducedSubgraph]
scoped infixl:50 " <=i " => Graph.IsInducedSubgraph

namespace IsInducedSubgraph

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: (h₁ : G <=i G₁) (h₂ : G₁ <=i G₂)
  statement: G <=i G₂
  proof: ⟨h₁.le.trans h₂.le, fun _ _ _ h hx hy => h₁.isLink_of_mem_mem
    (h₂.isLink_of_mem_mem h (h₁.vertexSet_mono hx) (h₁.vertexSet_mono hy)) hx hy⟩

中文:
引理 trans
  条件: (h₁ : G <=i G₁) (h₂ : G₁ <=i G₂)
  结论: G <=i G₂
  证明: ⟨h₁.le.trans h₂.le, fun _ _ _ h hx hy => h₁.isLink_of_mem_mem
    (h₂.isLink_of_mem_mem h (h₁.vertexSet_mono hx) (h₁.vertexSet_mono hy)) hx hy⟩
-/
protected lemma trans (h₁ : G <=i G₁) (h₂ : G₁ <=i G₂) : G <=i G₂ :=
  ⟨h₁.le.trans h₂.le, fun _ _ _ h hx hy => h₁.isLink_of_mem_mem
    (h₂.isLink_of_mem_mem h (h₁.vertexSet_mono hx) (h₁.vertexSet_mono hy)) hx hy⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPartialOrder (Graph α β) (· <=i ·)
  body: ⟨le_refl G, by tauto⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.1.antisymm h₂.1

中文:
实例 :
  签名: IsPartialOrder (Graph α β) (· <=i ·)
  定义体: ⟨le_refl G, by tauto⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.1.antisymm h₂.1

Depends on / 依赖: le_refl
-/
instance : IsPartialOrder (Graph α β) (· <=i ·) where
  refl G := ⟨le_refl G, by tauto⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.1.antisymm h₂.1

/--
lemma `rfl` / 引理 `rfl`

English:
lemma rfl
  statement: G <=i G
  proof: refl G

中文:
引理 rfl
  结论: G <=i G
  证明: refl G
-/
@[simp] protected lemma rfl : G <=i G := refl G

/--
lemma `isLink_congr` / 引理 `isLink_congr`

English:
lemma isLink_congr
  given: (hx : x in V(H)) (hy : y in V(H)) (h : H <=i G)
  proof: ⟨(·.mono h.le), fun hxy => h.isLink_of_mem_mem hxy hx hy⟩

中文:
引理 isLink_congr
  条件: (hx : x in V(H)) (hy : y in V(H)) (h : H <=i G)
  证明: ⟨(·.mono h.le), fun hxy => h.isLink_of_mem_mem hxy hx hy⟩

Depends on / 依赖: h.isLink_of_mem_mem, h.le, isLink_of_mem_mem
-/
lemma isLink_congr (hx : x in V(H)) (hy : y in V(H)) (h : H <=i G) :
    H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨(·.mono h.le), fun hxy => h.isLink_of_mem_mem hxy hx hy⟩

/--
lemma `adj_congr` / 引理 `adj_congr`

English:
lemma adj_congr
  given: (hx : x in V(H)) (hy : y in V(H)) (h : H <=i G)
  statement: H.Adj x y ↔ G.Adj x y
  proof: ⟨(·.mono h.le), fun ⟨_, hxy⟩ => (h.isLink_of_mem_mem hxy hx hy).adj⟩

中文:
引理 adj_congr
  条件: (hx : x in V(H)) (hy : y in V(H)) (h : H <=i G)
  结论: H.Adj x y ↔ G.Adj x y
  证明: ⟨(·.mono h.le), fun ⟨_, hxy⟩ => (h.isLink_of_mem_mem hxy hx hy).adj⟩

Depends on / 依赖: h.isLink_of_mem_mem, h.le, isLink_of_mem_mem
-/
lemma adj_congr (hx : x in V(H)) (hy : y in V(H)) (h : H <=i G) : H.Adj x y ↔ G.Adj x y :=
  ⟨(·.mono h.le), fun ⟨_, hxy⟩ => (h.isLink_of_mem_mem hxy hx hy).adj⟩

/--
lemma `anti_right` / 引理 `anti_right`

English:
lemma anti_right
  given: (hHK : H <= K) (hKG : K <= G) (h : H <=i G)
  statement: H <=i K where
  proof: hHK
  isLink_of_mem_mem _ _ _ hxy hx hy := h.isLink_of_mem_mem (hxy.mono hKG) hx hy

中文:
引理 anti_right
  条件: (hHK : H <= K) (hKG : K <= G) (h : H <=i G)
  结论: H <=i K where
  证明: hHK
  isLink_of_mem_mem _ _ _ hxy hx hy := h.isLink_of_mem_mem (hxy.mono hKG) hx hy
-/
lemma anti_right (hHK : H <= K) (hKG : K <= G) (h : H <=i G) : H <=i K where
  le := hHK
  isLink_of_mem_mem _ _ _ hxy hx hy := h.isLink_of_mem_mem (hxy.mono hKG) hx hy

/--
lemma `le_of_le_subset` / 引理 `le_of_le_subset`

English:
lemma le_of_le_subset
  given: (h' : K <= G) (hsu : V(K) subseteq V(H)) (h : H <=i G)
  statement: K <= H
  proof: by
  refine (Compatible.of_le_le h' h.le).le_iff.mpr ⟨hsu, fun e he => ?_⟩
  obtain ⟨u, v, huv⟩ := K.exists_isLink_of_mem_edgeSet he
.edge_mem exact h.2 (huv.mono h') (hsu huv.left_mem) (hsu huv.right_mem)

中文:
引理 le_of_le_subset
  条件: (h' : K <= G) (hsu : V(K) subseteq V(H)) (h : H <=i G)
  结论: K <= H
  证明: by
  refine (Compatible.of_le_le h' h.le).le_iff.mpr ⟨hsu, fun e he => ?_⟩
  obtain ⟨u, v, huv⟩ := K.exists_isLink_of_mem_edgeSet he
.edge_mem exact h.2 (huv.mono h') (hsu huv.left_mem) (hsu huv.right_mem)

Depends on / 依赖: Compatible, Compatible.of_le_le, K.exists_isLink_of_mem_edgeSet, edge_mem, exists_isLink_of_mem_edgeSet, h.le, huv.left_mem, huv.mono, huv.right_mem, le_iff, le_iff.mpr, left_mem, of_le_le, right_mem
-/
lemma le_of_le_subset (h' : K <= G) (hsu : V(K) subseteq V(H)) (h : H <=i G) : K <= H := by
  refine (Compatible.of_le_le h' h.le).le_iff.mpr ⟨hsu, fun e he => ?_⟩
  obtain ⟨u, v, huv⟩ := K.exists_isLink_of_mem_edgeSet he
.edge_mem exact h.2 (huv.mono h') (hsu huv.left_mem) (hsu huv.right_mem)

/--
lemma `ext_of_vertexSet` / 引理 `ext_of_vertexSet`

English:
lemma ext_of_vertexSet
  given: (hV : V(H) = V(G)) (h : H <=i G)
  statement: H = G
  proof: h.compatible.ext hV antisymm h.edgeSet_mono fun e he => by
    obtain ⟨_, _, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
.edge_mem exact h.isLink_of_mem_mem hxy (hV ▸ hxy.left_mem) (hV ▸ hxy.right_mem)

中文:
引理 ext_of_vertexSet
  条件: (hV : V(H) = V(G)) (h : H <=i G)
  结论: H = G
  证明: h.compatible.ext hV antisymm h.edgeSet_mono fun e he => by
    obtain ⟨_, _, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
.edge_mem exact h.isLink_of_mem_mem hxy (hV ▸ hxy.left_mem) (hV ▸ hxy.right_mem)

Depends on / 依赖: ExceptT, ExceptT.callCC, G.exists_isLink_of_mem_edgeSet, antisymm, callCC, compatible, edgeSet_mono, edge_mem, exists_isLink_of_mem_edgeSet, h.compatible.ext, h.edgeSet_mono, h.isLink_of_mem_mem, hxy.left_mem, hxy.right_mem, isLink_of_mem_mem, left_mem, right_mem
-/
lemma ext_of_vertexSet (hV : V(H) = V(G)) (h : H <=i G) : H = G :=
h.compatible.ext hV antisymm h.edgeSet_mono fun e he => by
    obtain ⟨_, _, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
.edge_mem exact h.isLink_of_mem_mem hxy (hV ▸ hxy.left_mem) (hV ▸ hxy.right_mem)

end IsInducedSubgraph

/--
lemma `IsSubgraph.not_isInducedSubgraph_iff` / 引理 `IsSubgraph.not_isInducedSubgraph_iff`

English:
lemma IsSubgraph.not_isInducedSubgraph_iff
  given: (hHG : H <= G)
  proof: by
  contrapose!; symm
  exact ⟨fun hnind => ⟨hHG, fun e x y hxy hx hy => hxy.anti_of_mem hHG (hnind e x y hxy hx hy)⟩,
.edge_mem⟩ fun hind _ _ _ hexy hx hy => hind.isLink_of_mem_mem hexy hx hy

中文:
引理 IsSubgraph.not_isInducedSubgraph_iff
  条件: (hHG : H <= G)
  证明: by
  contrapose!; symm
  exact ⟨fun hnind => ⟨hHG, fun e x y hxy hx hy => hxy.anti_of_mem hHG (hnind e x y hxy hx hy)⟩,
.edge_mem⟩ fun hind _ _ _ hexy hx hy => hind.isLink_of_mem_mem hexy hx hy

Depends on / 依赖: ExceptT, ExceptT.callCC, ExceptT.goto_mkLabel, ExceptT.run_bind, ExceptT.run_mk, Function, Function.comp, anti_of_mem, bind_assoc, callCC, callCC_bind_left, callCC_bind_right, callCC_dummy, contrapose, edge_mem, goto_mkLabel, hind.isLink_of_mem_mem, hxy.anti_of_mem, intros, isLink_of_mem_mem
-/
lemma IsSubgraph.not_isInducedSubgraph_iff (hHG : H <= G) :
    ¬ H <=i G ↔ exists e x y, G.IsLink e x y ∧ x in V(H) ∧ y in V(H) ∧ e ∉ E(H) := by
  contrapose!; symm
  exact ⟨fun hnind => ⟨hHG, fun e x y hxy hx hy => hxy.anti_of_mem hHG (hnind e x y hxy hx hy)⟩,
.edge_mem⟩ fun hind _ _ _ hexy hx hy => hind.isLink_of_mem_mem hexy hx hy

end InducedSubgraph

section ClosedSubgraph

/-! ### Closed Subgraphs -/

/-- `H ≤c G` (`Graph.IsClosedSubgraph`) is a union of components of `G`. -/
@[mk_iff]
/--
Definition of `IsClosedSubgraph` / `IsClosedSubgraph` 的定义

English:
structure IsClosedSubgraph
  parameters: (H G : Graph α β)
  axioms and operations (1):
    - closed : forall ⦃e x⦄, G.Inc e x -> x in V(H) -> e in E(H)

中文:
结构 IsClosedSubgraph
  参数: (H G : Graph α β)
  公理与运算 (1 个):
    - closed : 对任意 ⦃e x⦄, G.Inc e x -> x in V(H) -> e in E(H)
-/
structure IsClosedSubgraph (H G : Graph α β) : Prop extends
  isInducedSubgraph : IsInducedSubgraph H G where
  closed : forall ⦃e x⦄, G.Inc e x -> x in V(H) -> e in E(H)

@[inherit_doc IsClosedSubgraph]
scoped infixl:50 " <=c " => Graph.IsClosedSubgraph

namespace IsClosedSubgraph

/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  given: (hHG : H <= G) (hclosed : forall ⦃e x⦄, G.Inc e x -> x in V(H) -> e in E(H))
  statement: H <=c G where
  proof: hHG
  isLink_of_mem_mem _ _ _ he hx _ := he.anti_of_mem hHG (hclosed he.inc_left hx)
  closed _ _ he hx := hclosed he hx

中文:
引理 mk'
  条件: (hHG : H <= G) (hclosed : 对任意 ⦃e x⦄, G.Inc e x -> x in V(H) -> e in E(H))
  结论: H <=c G where
  证明: hHG
  isLink_of_mem_mem _ _ _ he hx _ := he.anti_of_mem hHG (hclosed he.inc_left hx)
  closed _ _ he hx := hclosed he hx
-/
lemma mk' (hHG : H <= G) (hclosed : forall ⦃e x⦄, G.Inc e x -> x in V(H) -> e in E(H)) : H <=c G where
  le := hHG
  isLink_of_mem_mem _ _ _ he hx _ := he.anti_of_mem hHG (hclosed he.inc_left hx)
  closed _ _ he hx := hclosed he hx

/--
lemma `trans` / 引理 `trans`

English:
lemma trans
  given: (h₁ : G <=c G₁) (h₂ : G₁ <=c G₂)
  statement: G <=c G₂
  proof: mk' (h₁.le.trans h₂.le) fun _ _ h hx => h₁.closed (h.of_compatible h₂.compatible'
    (h₂.closed h (h₁.vertexSet_mono hx))) hx

中文:
引理 trans
  条件: (h₁ : G <=c G₁) (h₂ : G₁ <=c G₂)
  结论: G <=c G₂
  证明: mk' (h₁.le.trans h₂.le) fun _ _ h hx => h₁.closed (h.of_compatible h₂.compatible'
    (h₂.closed h (h₁.vertexSet_mono hx))) hx
-/
protected lemma trans (h₁ : G <=c G₁) (h₂ : G₁ <=c G₂) : G <=c G₂ :=
  mk' (h₁.le.trans h₂.le) fun _ _ h hx => h₁.closed (h.of_compatible h₂.compatible'
    (h₂.closed h (h₁.vertexSet_mono hx))) hx

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPartialOrder (Graph α β) (· <=c ·)
  body: mk' le_rfl fun _ _ h _ => h.edge_mem
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.le.antisymm h₂.le

中文:
实例 :
  签名: IsPartialOrder (Graph α β) (· <=c ·)
  定义体: mk' le_rfl fun _ _ h _ => h.edge_mem
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.le.antisymm h₂.le

Depends on / 依赖: edge_mem, h.edge_mem, le_rfl
-/
instance : IsPartialOrder (Graph α β) (· <=c ·) where
  refl _ := mk' le_rfl fun _ _ h _ => h.edge_mem
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.le.antisymm h₂.le

/--
lemma `rfl` / 引理 `rfl`

English:
lemma rfl
  statement: G <=c G
  proof: refl G

中文:
引理 rfl
  结论: G <=c G
  证明: refl G
-/
@[simp] protected lemma rfl : G <=c G := refl G

/--
lemma `inc_congr` / 引理 `inc_congr`

English:
lemma inc_congr
  given: (hx : x in V(H)) (hHG : H <=c G)
  statement: H.Inc e x ↔ G.Inc e x
  proof: ⟨(·.mono hHG.le), fun he => he.of_compatible hHG.compatible' (hHG.closed he hx)⟩

中文:
引理 inc_congr
  条件: (hx : x in V(H)) (hHG : H <=c G)
  结论: H.Inc e x ↔ G.Inc e x
  证明: ⟨(·.mono hHG.le), fun he => he.of_compatible hHG.compatible' (hHG.closed he hx)⟩

Depends on / 依赖: closed, compatible, hHG.closed, hHG.compatible, hHG.le, he.of_compatible, of_compatible
-/
lemma inc_congr (hx : x in V(H)) (hHG : H <=c G) : H.Inc e x ↔ G.Inc e x :=
  ⟨(·.mono hHG.le), fun he => he.of_compatible hHG.compatible' (hHG.closed he hx)⟩

/--
lemma `isLink_congr` / 引理 `isLink_congr`

English:
lemma isLink_congr
  given: (hx : x in V(H)) (hHG : H <=c G)
  statement: H.IsLink e x y ↔ G.IsLink e x y
  proof: ⟨(·.mono hHG.le), fun h => h.anti_of_mem hHG.le ((hHG.inc_congr hx).mpr h.inc_left).edge_mem⟩

中文:
引理 isLink_congr
  条件: (hx : x in V(H)) (hHG : H <=c G)
  结论: H.IsLink e x y ↔ G.IsLink e x y
  证明: ⟨(·.mono hHG.le), fun h => h.anti_of_mem hHG.le ((hHG.inc_congr hx).mpr h.inc_left).edge_mem⟩

Depends on / 依赖: anti_of_mem, edge_mem, h.anti_of_mem, h.inc_left, hHG.inc_congr, hHG.le, inc_congr, inc_left
-/
lemma isLink_congr (hx : x in V(H)) (hHG : H <=c G) : H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨(·.mono hHG.le), fun h => h.anti_of_mem hHG.le ((hHG.inc_congr hx).mpr h.inc_left).edge_mem⟩

/--
lemma `mem_iff_of_isLink` / 引理 `mem_iff_of_isLink`

English:
lemma mem_iff_of_isLink
  given: (he : G.IsLink e x y) (hHG : H <=c G)
  statement: x in V(H) ↔ y in V(H)
  proof: by
  refine ⟨fun hin => ?_, fun hin => ?_⟩
  on_goal 2 => rw [isLink_comm] at he
  all_goals rw [← hHG.isLink_congr hin] at he; exact he.right_mem

中文:
引理 mem_iff_of_isLink
  条件: (he : G.IsLink e x y) (hHG : H <=c G)
  结论: x in V(H) ↔ y in V(H)
  证明: by
  refine ⟨fun hin => ?_, fun hin => ?_⟩
  on_goal 2 => rw [isLink_comm] at he
  all_goals rw [← hHG.isLink_congr hin] at he; exact he.right_mem

Depends on / 依赖: WriterT, WriterT.callCC, all_goals, callCC, hHG.isLink_congr, he.right_mem, isLink_comm, isLink_congr, on_goal, right_mem
-/
lemma mem_iff_of_isLink (he : G.IsLink e x y) (hHG : H <=c G) : x in V(H) ↔ y in V(H) := by
  refine ⟨fun hin => ?_, fun hin => ?_⟩
  on_goal 2 => rw [isLink_comm] at he
  all_goals rw [← hHG.isLink_congr hin] at he; exact he.right_mem

/--
lemma `mem_tfae_of_isLink` / 引理 `mem_tfae_of_isLink`

English:
lemma mem_tfae_of_isLink
  given: (he : G.IsLink e x y) (hHG : H <=c G)
  proof: by
  tfae_have 1 -> 2 := (hHG.mem_iff_of_isLink he).mp
  tfae_have 2 -> 3 := (hHG.isLink_congr · |>.mpr he.symm |>.edge_mem)
  tfae_have 3 -> 1 := (he.anti_of_mem hHG.le · |>.left_mem)
  tfae_finish

中文:
引理 mem_tfae_of_isLink
  条件: (he : G.IsLink e x y) (hHG : H <=c G)
  证明: by
  tfae_have 1 -> 2 := (hHG.mem_iff_of_isLink he).mp
  tfae_have 2 -> 3 := (hHG.isLink_congr · |>.mpr he.symm |>.edge_mem)
  tfae_have 3 -> 1 := (he.anti_of_mem hHG.le · |>.left_mem)
  tfae_finish

Depends on / 依赖: WriterT, WriterT.callCC, anti_of_mem, callCC, edge_mem, hHG.isLink_congr, hHG.le, hHG.mem_iff_of_isLink, he.anti_of_mem, he.symm, isLink_congr, left_mem, mem_iff_of_isLink, tfae_finish, tfae_have
-/
lemma mem_tfae_of_isLink (he : G.IsLink e x y) (hHG : H <=c G) :
    List.TFAE [x in V(H), y in V(H), e in E(H)] := by
  tfae_have 1 -> 2 := (hHG.mem_iff_of_isLink he).mp
  tfae_have 2 -> 3 := (hHG.isLink_congr · |>.mpr he.symm |>.edge_mem)
  tfae_have 3 -> 1 := (he.anti_of_mem hHG.le · |>.left_mem)
  tfae_finish

/--
lemma `adj_congr` / 引理 `adj_congr`

English:
lemma adj_congr
  given: (hx : x in V(H)) (hHG : H <=c G)
  statement: H.Adj x y ↔ G.Adj x y
  proof: ⟨(·.mono hHG.le), fun ⟨_, hxy⟩ => (hHG.isLink_congr hx |>.mpr hxy).adj⟩

中文:
引理 adj_congr
  条件: (hx : x in V(H)) (hHG : H <=c G)
  结论: H.Adj x y ↔ G.Adj x y
  证明: ⟨(·.mono hHG.le), fun ⟨_, hxy⟩ => (hHG.isLink_congr hx |>.mpr hxy).adj⟩

Depends on / 依赖: hHG.isLink_congr, hHG.le, isLink_congr
-/
lemma adj_congr (hx : x in V(H)) (hHG : H <=c G) : H.Adj x y ↔ G.Adj x y :=
  ⟨(·.mono hHG.le), fun ⟨_, hxy⟩ => (hHG.isLink_congr hx |>.mpr hxy).adj⟩

/--
lemma `mem_iff_of_adj` / 引理 `mem_iff_of_adj`

English:
lemma mem_iff_of_adj
  given: (hxy : G.Adj x y) (hHG : H <=c G)
  statement: x in V(H) ↔ y in V(H)
  proof: hHG.mem_iff_of_isLink hxy.choose_spec

中文:
引理 mem_iff_of_adj
  条件: (hxy : G.Adj x y) (hHG : H <=c G)
  结论: x in V(H) ↔ y in V(H)
  证明: hHG.mem_iff_of_isLink hxy.choose_spec

Depends on / 依赖: StateT, StateT.callCC, callCC, choose_spec, hHG.mem_iff_of_isLink, hxy.choose_spec, mem_iff_of_isLink
-/
lemma mem_iff_of_adj (hxy : G.Adj x y) (hHG : H <=c G) : x in V(H) ↔ y in V(H) :=
  hHG.mem_iff_of_isLink hxy.choose_spec

/--
lemma `anti_right` / 引理 `anti_right`

English:
lemma anti_right
  given: (hHG₁ : H <= G₁) (hG₁ : G₁ <= G) (hHG : H <=c G)
  statement: H <=c G₁
  proof: .edge_mem .mpr (he.mono hG₁) mk' hHG₁ fun _ _ he hx => hHG.inc_congr hx

中文:
引理 anti_right
  条件: (hHG₁ : H <= G₁) (hG₁ : G₁ <= G) (hHG : H <=c G)
  结论: H <=c G₁
  证明: .edge_mem .mpr (he.mono hG₁) mk' hHG₁ fun _ _ he hx => hHG.inc_congr hx

Depends on / 依赖: StateT, StateT.callCC, StateT.goto_mkLabel, StateT.run_bind, StateT.run_mk, callCC, callCC_bind_left, callCC_bind_right, callCC_dummy, edge_mem, goto_mkLabel, hHG.inc_congr, he.mono, inc_congr, intros, run_bind, run_mk
-/
lemma anti_right (hHG₁ : H <= G₁) (hG₁ : G₁ <= G) (hHG : H <=c G) : H <=c G₁ :=
.edge_mem .mpr (he.mono hG₁) mk' hHG₁ fun _ _ he hx => hHG.inc_congr hx

end IsClosedSubgraph

/--
lemma `IsInducedSubgraph.not_isClosedSubgraph_iff_exists_adj` / 引理 `IsInducedSubgraph.not_isClosedSubgraph_iff_exists_adj`

English:
lemma IsInducedSubgraph.not_isClosedSubgraph_iff_exists_adj
  given: (hHG : H <=i G)
  proof: by
  contrapose!; symm
  exact ⟨fun hncl => ⟨hHG, fun e x ⟨y, hexy⟩ hxH =>
.edge_mem⟩, hHG.isLink_of_mem_mem hexy hxH (hncl x y ⟨e, hexy⟩ hxH)
    fun hcl _ _ hexy => (hcl.mem_iff_of_adj hexy).mp⟩

中文:
引理 IsInducedSubgraph.not_isClosedSubgraph_iff_exists_adj
  条件: (hHG : H <=i G)
  证明: by
  contrapose!; symm
  exact ⟨fun hncl => ⟨hHG, fun e x ⟨y, hexy⟩ hxH =>
.edge_mem⟩, hHG.isLink_of_mem_mem hexy hxH (hncl x y ⟨e, hexy⟩ hxH)
    fun hcl _ _ hexy => (hcl.mem_iff_of_adj hexy).mp⟩

Depends on / 依赖: contrapose, edge_mem, hHG.isLink_of_mem_mem, hcl.mem_iff_of_adj, isLink_of_mem_mem, mem_iff_of_adj
-/
lemma IsInducedSubgraph.not_isClosedSubgraph_iff_exists_adj (hHG : H <=i G) :
    ¬ H <=c G ↔ exists x y, G.Adj x y ∧ x in V(H) ∧ y ∉ V(H) := by
  contrapose!; symm
  exact ⟨fun hncl => ⟨hHG, fun e x ⟨y, hexy⟩ hxH =>
.edge_mem⟩, hHG.isLink_of_mem_mem hexy hxH (hncl x y ⟨e, hexy⟩ hxH)
    fun hcl _ _ hexy => (hcl.mem_iff_of_adj hexy).mp⟩

/--
lemma `IsInducedSubgraph.not_isClosedSubgraph_iff_exists_isLink` / 引理 `IsInducedSubgraph.not_isClosedSubgraph_iff_exists_isLink`

English:
lemma IsInducedSubgraph.not_isClosedSubgraph_iff_exists_isLink
  given: (hHG : H <=i G)
  proof: by
  rw [hHG.not_isClosedSubgraph_iff_exists_adj]
  unfold Adj
  tauto

中文:
引理 IsInducedSubgraph.not_isClosedSubgraph_iff_exists_isLink
  条件: (hHG : H <=i G)
  证明: by
  rw [hHG.not_isClosedSubgraph_iff_exists_adj]
  unfold Adj
  tauto

Depends on / 依赖: ReaderT, ReaderT.callCC, callCC, hHG.not_isClosedSubgraph_iff_exists_adj, not_isClosedSubgraph_iff_exists_adj
-/
lemma IsInducedSubgraph.not_isClosedSubgraph_iff_exists_isLink (hHG : H <=i G) :
    ¬ H <=c G ↔ exists e x y, G.IsLink e x y ∧ x in V(H) ∧ y ∉ V(H) := by
  rw [hHG.not_isClosedSubgraph_iff_exists_adj]
  unfold Adj
  tauto

end ClosedSubgraph

section OrderBot

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (Graph α β)
  body: noEdge ∅ β
  bot_le G := by constructor <;> simp

中文:
实例 :
  签名: OrderBot (Graph α β)
  定义体: noEdge ∅ β
  bot_le G := by constructor <;> simp

Depends on / 依赖: ReaderT, ReaderT.callCC, ReaderT.goto_mkLabel, ReaderT.run_bind, ReaderT.run_monadLift, callCC, callCC_bind_left, callCC_bind_right, callCC_dummy, goto_mkLabel, intros, monadLift_self, noEdge, run_bind, run_monadLift
-/
instance : OrderBot (Graph α β) where
  bot := noEdge ∅ β
  bot_le G := by constructor <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Graph α β)
  body: ⊥

中文:
实例 :
  签名: Inhabited (Graph α β)
  定义体: ⊥
-/
instance : Inhabited (Graph α β) where
  default := ⊥

/--
lemma `noEdge_empty` / 引理 `noEdge_empty`

English:
lemma noEdge_empty
  statement: Graph.noEdge (∅ : Set α) β = ⊥
  proof: rfl

中文:
引理 noEdge_empty
  结论: Graph.noEdge (∅ : Set α) β = ⊥
  证明: rfl
-/
@[simp, grind =] lemma noEdge_empty : Graph.noEdge (∅ : Set α) β = ⊥ := rfl

/--
lemma `vertexSet_bot` / 引理 `vertexSet_bot`

English:
lemma vertexSet_bot
  statement: V((⊥ : Graph α β)) = ∅
  proof: rfl

中文:
引理 vertexSet_bot
  结论: V((⊥ : Graph α β)) = ∅
  证明: rfl
-/
@[simp] lemma vertexSet_bot : V((⊥ : Graph α β)) = ∅ := rfl

/--
lemma `edgeSet_bot` / 引理 `edgeSet_bot`

English:
lemma edgeSet_bot
  statement: E((⊥ : Graph α β)) = ∅
  proof: rfl

中文:
引理 edgeSet_bot
  结论: E((⊥ : Graph α β)) = ∅
  证明: rfl
-/
@[simp] lemma edgeSet_bot : E((⊥ : Graph α β)) = ∅ := rfl

/--
lemma `bot_isClosedSubgraph` / 引理 `bot_isClosedSubgraph`

English:
lemma bot_isClosedSubgraph
  given: (G : Graph α β)
  statement: ⊥ <=c G
  proof: IsClosedSubgraph.mk' bot_le (by simp)

中文:
引理 bot_isClosedSubgraph
  条件: (G : Graph α β)
  结论: ⊥ <=c G
  证明: IsClosedSubgraph.mk' bot_le (by simp)
-/
@[simp] lemma bot_isClosedSubgraph (G : Graph α β) : ⊥ <=c G := IsClosedSubgraph.mk' bot_le (by simp)

/--
lemma `eq_bot_or_vertexSet_nonempty` / 引理 `eq_bot_or_vertexSet_nonempty`

English:
lemma eq_bot_or_vertexSet_nonempty
  given: (G : Graph α β)
  statement: G = ⊥ ∨ V(G).Nonempty
  proof: by
  refine (em (V(G) = ∅)).elim (fun he => .inl (Graph.ext he fun e x y => ?_)) (Or.inr ∘
    nonempty_iff_ne_empty.mpr)
  simp only [edgeSet_bot, mem_empty_iff_false, not_false_eq_true, not_isLink_of_notMem_edgeSet,
    iff_false]
  exact fun h => by simpa [he] using h.left_mem

中文:
引理 eq_bot_or_vertexSet_nonempty
  条件: (G : Graph α β)
  结论: G = ⊥ ∨ V(G).Nonempty
  证明: by
  refine (em (V(G) = ∅)).elim (fun he => .inl (Graph.ext he fun e x y => ?_)) (Or.inr ∘
    nonempty_iff_ne_empty.mpr)
  simp only [edgeSet_bot, mem_empty_iff_false, not_false_eq_true, not_isLink_of_notMem_edgeSet,
    iff_false]
  exact fun h => by simpa [he] using h.left_mem

Depends on / 依赖: Graph.ext, Or.inr, edgeSet_bot, h.left_mem, iff_false, left_mem, mem_empty_iff_false, nonempty_iff_ne_empty, nonempty_iff_ne_empty.mpr, not_false_eq_true, not_isLink_of_notMem_edgeSet
-/
lemma eq_bot_or_vertexSet_nonempty (G : Graph α β) : G = ⊥ ∨ V(G).Nonempty := by
  refine (em (V(G) = ∅)).elim (fun he => .inl (Graph.ext he fun e x y => ?_)) (Or.inr ∘
    nonempty_iff_ne_empty.mpr)
  simp only [edgeSet_bot, mem_empty_iff_false, not_false_eq_true, not_isLink_of_notMem_edgeSet,
    iff_false]
  exact fun h => by simpa [he] using h.left_mem

/--
lemma `vertexSet_eq_empty_iff` / 引理 `vertexSet_eq_empty_iff`

English:
lemma vertexSet_eq_empty_iff
  statement: V(G) = ∅ ↔ G = ⊥
  proof: by
  refine ⟨fun h => bot_le.antisymm' ⟨by simp [h], fun e x y he => ?_⟩, fun h => by simp [h]⟩
  simpa [h] using he.left_mem

@[push, simp]

中文:
引理 vertexSet_eq_empty_iff
  结论: V(G) = ∅ ↔ G = ⊥
  证明: by
  refine ⟨fun h => bot_le.antisymm' ⟨by simp [h], fun e x y he => ?_⟩, fun h => by simp [h]⟩
  simpa [h] using he.left_mem

@[push, simp]

Depends on / 依赖: antisymm, bot_le, bot_le.antisymm, he.left_mem, left_mem
-/
lemma vertexSet_eq_empty_iff : V(G) = ∅ ↔ G = ⊥ := by
  refine ⟨fun h => bot_le.antisymm' ⟨by simp [h], fun e x y he => ?_⟩, fun h => by simp [h]⟩
  simpa [h] using he.left_mem

@[push, simp]
/--
lemma `ne_bot_iff` / 引理 `ne_bot_iff`

English:
lemma ne_bot_iff
  statement: G != ⊥ ↔ V(G).Nonempty
  proof: not_iff_not.mp by simp [vertexSet_eq_empty_iff, not_nonempty_iff_eq_empty]

@[push, simp]

中文:
引理 ne_bot_iff
  结论: G != ⊥ ↔ V(G).Nonempty
  证明: not_iff_not.mp by simp [vertexSet_eq_empty_iff, not_nonempty_iff_eq_empty]

@[push, simp]

Depends on / 依赖: not_iff_not, not_iff_not.mp, not_nonempty_iff_eq_empty, vertexSet_eq_empty_iff
-/
lemma ne_bot_iff : G != ⊥ ↔ V(G).Nonempty :=
not_iff_not.mp by simp [vertexSet_eq_empty_iff, not_nonempty_iff_eq_empty]

@[push, simp]
/--
lemma `vertexSet_not_nonempty_iff` / 引理 `vertexSet_not_nonempty_iff`

English:
lemma vertexSet_not_nonempty_iff
  statement: ¬ V(G).Nonempty ↔ G = ⊥
  proof: by
  simp [vertexSet_eq_empty_iff, not_nonempty_iff_eq_empty]

中文:
引理 vertexSet_not_nonempty_iff
  结论: ¬ V(G).Nonempty ↔ G = ⊥
  证明: by
  simp [vertexSet_eq_empty_iff, not_nonempty_iff_eq_empty]

Depends on / 依赖: not_nonempty_iff_eq_empty, vertexSet_eq_empty_iff
-/
lemma vertexSet_not_nonempty_iff : ¬ V(G).Nonempty ↔ G = ⊥ := by
  simp [vertexSet_eq_empty_iff, not_nonempty_iff_eq_empty]

/--
lemma `ne_bot_of_mem_vertexSet` / 引理 `ne_bot_of_mem_vertexSet`

English:
lemma ne_bot_of_mem_vertexSet
  given: (h : x in V(G))
  statement: G != ⊥
  proof: ne_bot_iff.mpr ⟨x, h⟩

@[simp]

中文:
引理 ne_bot_of_mem_vertexSet
  条件: (h : x in V(G))
  结论: G != ⊥
  证明: ne_bot_iff.mpr ⟨x, h⟩

@[simp]

Depends on / 依赖: ne_bot_iff, ne_bot_iff.mpr
-/
lemma ne_bot_of_mem_vertexSet (h : x in V(G)) : G != ⊥ := ne_bot_iff.mpr ⟨x, h⟩

@[simp]
/--
lemma `isSpanningSubgraph_bot_iff` / 引理 `isSpanningSubgraph_bot_iff`

English:
lemma isSpanningSubgraph_bot_iff
  statement: G <=s ⊥ ↔ G = ⊥
  proof: ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

@[simp]

中文:
引理 isSpanningSubgraph_bot_iff
  结论: G <=s ⊥ ↔ G = ⊥
  证明: ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

@[simp]

Depends on / 依赖: h.le, le_bot_iff, le_bot_iff.mp
-/
lemma isSpanningSubgraph_bot_iff : G <=s ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

@[simp]
/--
lemma `isInducedSubgraph_bot_iff` / 引理 `isInducedSubgraph_bot_iff`

English:
lemma isInducedSubgraph_bot_iff
  statement: G <=i ⊥ ↔ G = ⊥
  proof: ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

@[simp]

中文:
引理 isInducedSubgraph_bot_iff
  结论: G <=i ⊥ ↔ G = ⊥
  证明: ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

@[simp]

Depends on / 依赖: h.le, le_bot_iff, le_bot_iff.mp
-/
lemma isInducedSubgraph_bot_iff : G <=i ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

@[simp]
/--
lemma `isClosedSubgraph_bot_iff` / 引理 `isClosedSubgraph_bot_iff`

English:
lemma isClosedSubgraph_bot_iff
  statement: G <=c ⊥ ↔ G = ⊥
  proof: ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

中文:
引理 isClosedSubgraph_bot_iff
  结论: G <=c ⊥ ↔ G = ⊥
  证明: ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

Depends on / 依赖: h.le, le_bot_iff, le_bot_iff.mp
-/
lemma isClosedSubgraph_bot_iff : G <=c ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

/--
lemma `not_disjoint_of_mem_mem` / 引理 `not_disjoint_of_mem_mem`

English:
lemma not_disjoint_of_mem_mem
  given: (h : x in V(G)) (h' : x in V(H))
  statement: ¬ Disjoint G H
  proof: by
  simp only [Disjoint, le_bot_iff, not_forall, ne_eq, ne_bot_iff]
  use noEdge {x} β
  simp [h, h']

中文:
引理 not_disjoint_of_mem_mem
  条件: (h : x in V(G)) (h' : x in V(H))
  结论: ¬ Disjoint G H
  证明: by
  simp only [Disjoint, le_bot_iff, not_forall, ne_eq, ne_bot_iff]
  use noEdge {x} β
  simp [h, h']

Depends on / 依赖: Disjoint, le_bot_iff, ne_bot_iff, ne_eq, noEdge, not_forall
-/
lemma not_disjoint_of_mem_mem (h : x in V(G)) (h' : x in V(H)) : ¬ Disjoint G H := by
  simp only [Disjoint, le_bot_iff, not_forall, ne_eq, ne_bot_iff]
  use noEdge {x} β
  simp [h, h']

end OrderBot

end Graph
