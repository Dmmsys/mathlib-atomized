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
/-
**Graph.IsSubgraph** 是 Mathlib 中的一个结构，位于命名空间 `Graph`。
形式化陈述：IsSubgraph (H G : Graph α β) : Prop where vertexSet_mono : V(H) subseteq V
(G)
参数：H G : Graph α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSubgraph H G` is NOT the preferred spelling for the subgraph relation. Please
 use
`H ≤ G` instead.
-/
structure IsSubgraph (H G : Graph α β) : Prop where
  vertexSet_mono : V(H) ⊆ V(G) := by aesop
  isLink_mono : ∀ ⦃e x y⦄, H.IsLink e x y → G.IsLink e x y := by aesop

attribute [gcongr, grind →] IsSubgraph.vertexSet_mono
/-
**Graph.IsSubgraph.trans** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G G₁ H : Graph α β}, H.IsSubgraph G → G.I
sSubgraph G₁ → H.IsSubgraph G₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
· 使用定理 `Graph.IsSubgraph.isLink_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : Gra
ph α β}, H.IsSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, H.IsLink e x y → G.IsLink e x y
-/
lemma IsSubgraph.trans (h₁ : H.IsSubgraph G) (h₂ : G.IsSubgraph G₁) : H.IsSubgraph G₁ :=
  ⟨h₁.1.trans h₂.1, fun _ _ _ h ↦ h₂.2 (h₁.2 h)⟩
/-
**Graph.IsSubgraph.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, H.IsSubgraph G → G.IsSu
bgraph H → H = G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.ext`：∀ {α : Type u_1} {β : Type u_2} {G₁ G₂ : Graph α β},   G₁.ver
texSet = G₂.vertexSet → (∀ (e : β) (x y : α), G₁.IsLink e x y ↔ G₂.IsLink e x y…
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
· 使用定理 `Graph.IsSubgraph.isLink_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : Gra
ph α β}, H.IsSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, H.IsLink e x y → G.IsLink e x y
-/
lemma IsSubgraph.antisymm (h₁ : H.IsSubgraph G) (h₂ : G.IsSubgraph H) : H = G :=
  Graph.ext (h₁.1.antisymm h₂.1) fun _ _ _ ↦ ⟨(h₁.2 ·), (h₂.2 ·)⟩

/-- `H ≤ G` means `H` is a subgraph of `G`. It is defined as `V(H) ⊆ V(G)` and every link of `H`
being a link of `G`. -/
/-
**Graph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`H ≤ G` means `H` is a subgraph of `G`. It is defined as `V(H) ⊆ V(G)` and every
 link of `H`
being a link of `G`.
-/
instance : PartialOrder (Graph α β) where
  le := IsSubgraph
  le_refl _ := ⟨le_rfl, fun _ _ _ h ↦ h⟩
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm G H h₁ h₂ := h₁.antisymm h₂

@[simp]
/-
**Graph.isSubgraph_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：isSubgraph_iff_le : H.IsSubgraph G ↔ H <= G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isSubgraph_iff_le : H.IsSubgraph G ↔ H ≤ G := .rfl

@[gcongr]
/-
**Graph.IsLink.mono** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G H : Graph α β}, H ≤ G
 → H.IsLink e x y → G.IsLink e x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsSubgraph.isLink_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : Gra
ph α β}, H.IsSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, H.IsLink e x y → G.IsLink e x y
-/
lemma IsLink.mono (hHG : H ≤ G) (h : H.IsLink e x y) : G.IsLink e x y := hHG.2 h

@[gcongr, grind →]
/-
**Graph.IsSubgraph.edgeSet_mono** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, H ≤ G → H.edgeSet ⊆ G.e
dgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Graph.exists_isLink_of_mem_edgeSet`：exists_isLink_of_mem_edgeSet (h : e 
in E(G)) : exists x y, G.IsLink e x y
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
· 使用定理 `Graph.IsLink.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
H : Graph α β}, H ≤ G → H.IsLink e x y → G.IsLink e x y
-/
lemma IsSubgraph.edgeSet_mono (h : H ≤ G) : E(H) ⊆ E(G) := by
  intro e he
  obtain ⟨x, y, h'⟩ := exists_isLink_of_mem_edgeSet he
  exact (h'.mono h).edge_mem
/-
**Graph.IsLink.anti_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsLink.anti_of_mem (h : G.IsLink e x y) (hHG : H ≤ G) (he : e ∈ E(H)) :
    H.IsLink e x y := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (huv.mono hHG).eq_and_eq_or_eq_and_eq h
  · assumption
  exact huv.symm
/-
**Graph.IsSubgraph.isLink_iff** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G H : Graph α β},   H ≤
 G → e ∈ H.edgeSet → (H.IsLink e x y ↔ G.IsLink e x y)
参数：H.IsLink e x y ↔ G.IsLink e x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
H : Graph α β}, H ≤ G → H.IsLink e x y → G.IsLink e x y
· 使用定理 `_private.Mathlib.Combinatorics.Graph.Subgraph.0.Graph.IsLink.anti_of_mem
`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G H : Graph α β},   G.IsLin
k e x y → H ≤ G → e ∈ H.edgeSet → H.IsLink e x y
-/
lemma IsSubgraph.isLink_iff (hHG : H ≤ G) (he : e ∈ E(H)) : H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨fun h ↦ h.mono hHG, fun h ↦ h.anti_of_mem hHG he⟩
/-
**Graph.IsSubgraph.isLink_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, H ≤ G → Set.EqOn H.IsLi
nk G.IsLink H.edgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Graph.IsSubgraph.isLink_iff`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {
e : β} {G H : Graph α β},   H ≤ G → e ∈ H.edgeSet → (H.IsLink e x y ↔ G.IsLink e
 x y)
-/
lemma IsSubgraph.isLink_eqOn (hHG : H ≤ G) : EqOn H.IsLink G.IsLink E(H) := by
  rintro e he
  ext x y
  exact isLink_iff hHG he

/-- Two subgraphs of the same graph are compatible. -/
/-
**Graph.Compatible.of_le_le** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H₁ H₂ : Graph α β}, H₁ ≤ G → H₂ ≤ G → H
₁.Compatible H₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Graph.IsSubgraph.isLink_iff`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {
e : β} {G H : Graph α β},   H ≤ G → e ∈ H.edgeSet → (H.IsLink e x y ↔ G.IsLink e
 x y)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)

--- 原说明 ---
Two subgraphs of the same graph are compatible.
-/
lemma Compatible.of_le_le (hH₁G : H₁ ≤ G) (hH₂G : H₂ ≤ G) : H₁.Compatible H₂ :=
  fun _ he₁ he₂ _ _ ↦ hH₁G.isLink_iff he₁ |>.trans <| (hH₂G.isLink_iff he₂).symm
/-
**Graph.Compatible.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, H ≤ G → H.Compatible G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.of_le_le`：∀ {α : Type u_1} {β : Type u_2} {G H₁ H₂ : Gr
aph α β}, H₁ ≤ G → H₂ ≤ G → H₁.Compatible H₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma Compatible.of_le (hHG : H ≤ G) : H.Compatible G := .of_le_le hHG le_rfl
/-
**Graph.Compatible.of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, G ≤ H → H.Compatible G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.of_le_le`：∀ {α : Type u_1} {β : Type u_2} {G H₁ H₂ : Gr
aph α β}, H₁ ≤ G → H₂ ≤ G → H₁.Compatible H₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma Compatible.of_ge (hHG : G ≤ H) : H.Compatible G := .of_le_le le_rfl hHG

alias IsSubgraph.compatible := Compatible.of_le
alias IsSubgraph.compatible' := Compatible.of_ge
/-
**Graph.Compatible.anti_left** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G G₁ H : Graph α β}, G₁ ≤ G → G.Compatibl
e H → G₁.Compatible H
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Graph.IsSubgraph.isLink_iff`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {
e : β} {G H : Graph α β},   H ≤ G → e ∈ H.edgeSet → (H.IsLink e x y ↔ G.IsLink e
 x y)
· 使用定理 `Graph.IsSubgraph.edgeSet_mono`：∀ {α : Type u_1} {β : Type u_2} {G H : Gr
aph α β}, H ≤ G → H.edgeSet ⊆ G.edgeSet
-/
lemma Compatible.anti_left (hG₁G : G₁ ≤ G) (h : Compatible G H) : Compatible G₁ H :=
  fun _ he₁ he₂ _ _ ↦ hG₁G.isLink_iff he₁ |>.trans <| h (hG₁G.edgeSet_mono he₁) he₂ ..
/-
**Graph.Compatible.anti_right** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H H₁ : Graph α β}, H₁ ≤ H → G.Compatibl
e H → G.Compatible H₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.symm`：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}
, G.Compatible H → H.Compatible G
· 使用定理 `Graph.Compatible.anti_left`：∀ {α : Type u_1} {β : Type u_2} {G G₁ H : Gr
aph α β}, G₁ ≤ G → G.Compatible H → G₁.Compatible H
-/
lemma Compatible.anti_right (hH₁H : H₁ ≤ H) (h : Compatible G H) : Compatible G H₁ :=
  (h.symm.anti_left hH₁H).symm
/-
**Graph.Compatible.anti** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G G₁ H H₁ : Graph α β}, G₁ ≤ G → H₁ ≤ H →
 G.Compatible H → G₁.Compatible H₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.anti_right`：∀ {α : Type u_1} {β : Type u_2} {G H H₁ : G
raph α β}, H₁ ≤ H → G.Compatible H → G.Compatible H₁
· 使用定理 `Graph.Compatible.anti_left`：∀ {α : Type u_1} {β : Type u_2} {G G₁ H : Gr
aph α β}, G₁ ≤ G → G.Compatible H → G₁.Compatible H
-/
lemma Compatible.anti (hG₁G : G₁ ≤ G) (hH₁H : H₁ ≤ H) (h : G.Compatible H) : G₁.Compatible H₁ :=
  (h.anti_left hG₁G).anti_right hH₁H

@[gcongr]
/-
**Graph.Inc.mono** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G H : Graph α β}, H ≤ G →
 H.Inc e x → G.Inc e x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.inc_left`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → G.Inc e x
· 使用定理 `Graph.IsLink.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
H : Graph α β}, H ≤ G → H.IsLink e x y → G.IsLink e x y
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma Inc.mono (hHG : H ≤ G) (h : H.Inc e x) : G.Inc e x :=
  (h.choose_spec.mono hHG).inc_left
/-
**Graph.IsSubgraph.inc_congr** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G H : Graph α β}, H ≤ G →
 e ∈ H.edgeSet → (H.Inc e x ↔ G.Inc e x)
参数：H.Inc e x ↔ G.Inc e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Graph.IsSubgraph.isLink_iff`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {
e : β} {G H : Graph α β},   H ≤ G → e ∈ H.edgeSet → (H.IsLink e x y ↔ G.IsLink e
 x y)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsSubgraph.inc_congr (hHG : H ≤ G) (he : e ∈ E(H)) : H.Inc e x ↔ G.Inc e x := by
  simp_rw [Graph.Inc, hHG.isLink_iff he]
/-
**Graph.IsSubgraph.inc_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, H ≤ G → Set.EqOn H.Inc 
G.Inc H.edgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Graph.IsSubgraph.inc_congr`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e :
 β} {G H : Graph α β}, H ≤ G → e ∈ H.edgeSet → (H.Inc e x ↔ G.Inc e x)
-/
lemma IsSubgraph.inc_eqOn (hHG : H ≤ G) : EqOn H.Inc G.Inc E(H) := by
  rintro e he
  ext x
  exact hHG.inc_congr he
/-
**Graph.IsLoopAt.mono** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLoopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G H : Graph α β}, H ≤ G →
 H.IsLoopAt e x → G.IsLoopAt e x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
H : Graph α β}, H ≤ G → H.IsLink e x y → G.IsLink e x y
-/
lemma IsLoopAt.mono (hHG : H ≤ G) (h : H.IsLoopAt e x) : G.IsLoopAt e x :=
  IsLink.mono hHG h
/-
**Graph.IsSubgraph.isLoopAt_congr** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G H : Graph α β},   H ≤ G
 → e ∈ H.edgeSet → (H.IsLoopAt e x ↔ G.IsLoopAt e x)
参数：H.IsLoopAt e x ↔ G.IsLoopAt e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.IsSubgraph.isLink_iff`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {
e : β} {G H : Graph α β},   H ≤ G → e ∈ H.edgeSet → (H.IsLink e x y ↔ G.IsLink e
 x y)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsSubgraph.isLoopAt_congr (hHG : H ≤ G) (he : e ∈ E(H)) :
    H.IsLoopAt e x ↔ G.IsLoopAt e x := by
  unfold Graph.IsLoopAt
  rw [hHG.isLink_iff he]
/-
**Graph.IsSubgraph.isLoopAt_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, H ≤ G → Set.EqOn H.IsLo
opAt G.IsLoopAt H.edgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Graph.IsSubgraph.isLoopAt_congr`：∀ {α : Type u_1} {β : Type u_2} {x : α}
 {e : β} {G H : Graph α β},   H ≤ G → e ∈ H.edgeSet → (H.IsLoopAt e x ↔ G.IsLoop
At e x)
-/
lemma IsSubgraph.isLoopAt_eqOn (hHG : H ≤ G) : EqOn H.IsLoopAt G.IsLoopAt E(H) := by
  rintro e he
  ext x
  exact hHG.isLoopAt_congr he
/-
**Graph.IsNonloopAt.mono** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsNonloopAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G H : Graph α β}, H ≤ G →
 H.IsNonloopAt e x → G.IsNonloopAt e x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
H : Graph α β}, H ≤ G → H.IsLink e x y → G.IsLink e x y
-/
lemma IsNonloopAt.mono (hHG : H ≤ G) (h : H.IsNonloopAt e x) : G.IsNonloopAt e x := by
  obtain ⟨y, hxy, he⟩ := h
  exact ⟨y, hxy, he.mono hHG⟩
/-
**Graph.IsSubgraph.isNonloopAt_congr** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G H : Graph α β},   H ≤ G
 → e ∈ H.edgeSet → (H.IsNonloopAt e x ↔ G.IsNonloopAt e x)
参数：H.IsNonloopAt e x ↔ G.IsNonloopAt e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Graph.IsSubgraph.isLink_iff`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {
e : β} {G H : Graph α β},   H ≤ G → e ∈ H.edgeSet → (H.IsLink e x y ↔ G.IsLink e
 x y)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsSubgraph.isNonloopAt_congr (hHG : H ≤ G) (he : e ∈ E(H)) :
    H.IsNonloopAt e x ↔ G.IsNonloopAt e x := by
  simp_rw [Graph.IsNonloopAt, hHG.isLink_iff he]
/-
**Graph.IsSubgraph.isNonloopAt_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSubgraph`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}, H ≤ G → Set.EqOn H.IsNo
nloopAt G.IsNonloopAt H.edgeSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Graph.IsSubgraph.isNonloopAt_congr`：∀ {α : Type u_1} {β : Type u_2} {x :
 α} {e : β} {G H : Graph α β},   H ≤ G → e ∈ H.edgeSet → (H.IsNonloopAt e x ↔ G.
IsNonloopAt e x)
-/
lemma IsSubgraph.isNonloopAt_eqOn (hHG : H ≤ G) : EqOn H.IsNonloopAt G.IsNonloopAt E(H) := by
  rintro e he
  ext x
  exact hHG.isNonloopAt_congr he

@[gcongr]
/-
**Graph.Adj.mono** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Adj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {x y : α} {G H : Graph α β}, H ≤ G → H.Adj
 x y → G.Adj x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.adj`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G :
 Graph α β}, G.IsLink e x y → G.Adj x y
· 使用定理 `Graph.IsLink.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
H : Graph α β}, H ≤ G → H.IsLink e x y → G.IsLink e x y
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma Adj.mono (hHG : H ≤ G) (h : H.Adj x y) : G.Adj x y :=
  (h.choose_spec.mono hHG).adj
/-
**Graph.le_iff_compatible_subset_subset** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：le_iff_compatible_subset_subset : G <= H ↔ Compatible G H ∧ V(G) subseteq 
V(H) ∧ E(G) subseteq E(H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.of_le`：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β
}, H ≤ G → H.Compatible G
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
· 使用定理 `Graph.IsSubgraph.edgeSet_mono`：∀ {α : Type u_1} {β : Type u_2} {G H : Gr
aph α β}, H ≤ G → H.edgeSet ⊆ G.edgeSet
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
-/
lemma le_iff_compatible_subset_subset : G ≤ H ↔ Compatible G H ∧ V(G) ⊆ V(H) ∧ E(G) ⊆ E(H) :=
  ⟨fun h ↦ ⟨.of_le h, h.1, h.edgeSet_mono⟩, fun ⟨h, hV, hE⟩ ↦
    ⟨hV, fun _ _ _ hxy ↦ h hxy.edge_mem (hE hxy.edge_mem) .. |>.mp hxy⟩⟩
/-
**Graph.Compatible.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph α β},   H₁.Compatible H₂ → 
(H₁ ≤ H₂ ↔ H₁.vertexSet ⊆ H₂.vertexSet ∧ H₁.edgeSet ⊆ H₂.edgeSet)
参数：H₁ ≤ H₂ ↔ H₁.vertexSet ⊆ H₂.vertexSet ∧ H₁.edgeSet ⊆ H₂.edgeSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `Graph.le_iff_compatible_subset_subset`：le_iff_compatible_subset_subset :
 G <= H ↔ Compatible G H ∧ V(G) subseteq V(H) ∧ E(G) subseteq E(H)
-/
lemma Compatible.le_iff (hH : Compatible H₁ H₂) : H₁ ≤ H₂ ↔ V(H₁) ⊆ V(H₂) ∧ E(H₁) ⊆ E(H₂) :=
  le_iff_compatible_subset_subset.trans (by tauto)
/-
**Graph.Compatible.ext** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Compatible`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph α β},   H₁.vertexSet = H₂.v
ertexSet → H₁.edgeSet = H₂.edgeSet → H₁.Compatible H₂ → H₁ = H₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Graph.Compatible.le_iff`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph 
α β},   H₁.Compatible H₂ → (H₁ ≤ H₂ ↔ H₁.vertexSet ⊆ H₂.vertexSet ∧ H₁.edgeSet ⊆
 H₂.edgeSet)
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Graph.Compatible.symm`：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β}
, G.Compatible H → H.Compatible G
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
-/
lemma Compatible.ext (hV : V(H₁) = V(H₂)) (hE : E(H₁) = E(H₂)) (h : Compatible H₁ H₂) : H₁ = H₂ :=
  (h.le_iff.mpr ⟨hV.subset, hE.subset⟩).antisymm <| h.symm.le_iff.mpr ⟨hV.superset, hE.superset⟩
/-
**Graph.vertexSet_ssubset_or_edgeSet_ssubset_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Gr
aph`。
形式化陈述：vertexSet_ssubset_or_edgeSet_ssubset_of_lt (hGH : G < H) : V(G) ⊂ V(H) ∨ E
(G) ⊂ E(H)
参数：hGH : G < H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Graph.IsSubgraph.edgeSet_mono`：∀ {α : Type u_1} {β : Type u_2} {G H : Gr
aph α β}, H ≤ G → H.edgeSet ⊆ G.edgeSet
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Graph.Compatible.ext`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph α β
},   H₁.vertexSet = H₂.vertexSet → H₁.edgeSet = H₂.edgeSet → H₁.Compatible H₂ → 
H₁ = H₂
· 使用定理 `Graph.IsSubgraph.compatible`：∀ {α : Type u_1} {β : Type u_2} {G H : Grap
h α β}, H ≤ G → H.Compatible G
-/
lemma vertexSet_ssubset_or_edgeSet_ssubset_of_lt (hGH : G < H) : V(G) ⊂ V(H) ∨ E(G) ⊂ E(H) := by
  rw [lt_iff_le_and_ne] at hGH
  simp only [ssubset_iff_subset_ne, hGH.1.vertexSet_mono, ne_eq, true_and, hGH.1.edgeSet_mono]
  by_contra! heq
  exact hGH.2 <| hGH.1.compatible.ext heq.1 heq.2

@[simp]
/-
**Graph.noEdge_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：noEdge_le_iff : noEdge X β <= G ↔ X subseteq V(G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Graph.edgeSet_noEdge`：∀ {α : Type u_1} (vertexSet : Set α) (β : Type u_3
), (Graph.noEdge vertexSet β).edgeSet = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma noEdge_le_iff : noEdge X β ≤ G ↔ X ⊆ V(G) := ⟨(·.vertexSet_mono), fun h ↦ ⟨h, by simp⟩⟩

@[simp]
/-
**Graph.le_noEdge_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：le_noEdge_iff : G <= noEdge X β ↔ V(G) subseteq X ∧ E(G) = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `Graph.IsSubgraph.edgeSet_mono`：∀ {α : Type u_1} {β : Type u_2} {G H : Gr
aph α β}, H ≤ G → H.edgeSet ⊆ G.edgeSet
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Graph.edgeSet_noEdge`：∀ {α : Type u_1} (vertexSet : Set α) (β : Type u_3
), (Graph.noEdge vertexSet β).edgeSet = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
-/
lemma le_noEdge_iff : G ≤ noEdge X β ↔ V(G) ⊆ X ∧ E(G) = ∅ :=
  ⟨fun h ↦ ⟨h.vertexSet_mono, subset_empty_iff.1 h.edgeSet_mono⟩,
    fun h ↦ ⟨h.1, fun e x y he ↦ by simpa [h] using he.edge_mem⟩⟩

end Subgraph

section SpanningSubgraph

/-! ### Spanning Subgraphs -/

/-- `H ≤s G` (`Graph.IsSpanningSubgraph`) is a subgraph of `G` with the same vertex set. -/
@[mk_iff]
/-
**Graph.IsSpanningSubgraph** 是 Mathlib 中的一个归纳类型，位于命名空间 `Graph`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Graph α β → Graph α β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`H ≤s G` (`Graph.IsSpanningSubgraph`) is a subgraph of `G` with the same vertex 
set.
-/
structure IsSpanningSubgraph (H G : Graph α β) : Prop extends le : H ≤ G where
  vertexSet_eq : V(H) = V(G)

@[inherit_doc IsSpanningSubgraph]
infixl:50 " ≤s " => Graph.IsSpanningSubgraph

namespace IsSpanningSubgraph

/-
**Graph.IsSpanningSubgraph.trans** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSpanningSubg
raph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G G₁ G₂ : Graph α β}, G ≤s G₁ → G₁ ≤s G₂ 
→ G ≤s G₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsSubgraph.trans`：∀ {α : Type u_1} {β : Type u_2} {G G₁ H : Graph 
α β}, H.IsSubgraph G → G.IsSubgraph G₁ → H.IsSubgraph G₁
· 使用定理 `Graph.IsSpanningSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Grap
h α β}, H ≤s G → H.IsSubgraph G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Graph.IsSpanningSubgraph.vertexSet_eq`：∀ {α : Type u_1} {β : Type u_2} {
H G : Graph α β}, H ≤s G → H.vertexSet = G.vertexSet
-/
protected lemma trans (h₁ : G ≤s G₁) (h₂ : G₁ ≤s G₂) : G ≤s G₂ :=
  ⟨h₁.le.trans h₂.le, h₁.vertexSet_eq.trans h₂.vertexSet_eq⟩
/-
**Graph.IsSpanningSubgraph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph.IsSpanningSubgraph`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPartialOrder (Graph α β) (· ≤s ·) where
  refl G := ⟨le_refl G, rfl⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.1.antisymm h₂.1
/-
**Graph.IsSpanningSubgraph.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsSpanningSubgra
ph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β}, G ≤s G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsPartialOrder.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self :
 IsPartialOrder α r], IsPreorder α r
· 使用定理 `Graph.IsSpanningSubgraph.instIsPartialOrder`：∀ {α : Type u_1} {β : Type 
u_2}, IsPartialOrder (Graph α β) fun x1 x2 => x1 ≤s x2
-/
@[simp] protected lemma rfl : G ≤s G := refl G
/-
**Graph.IsSpanningSubgraph.anti_right** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsSpannin
gSubgraph`。
形式化陈述：anti_right (hHK : H <= K) (hKG : K <= G) (h : H <=s G) : H <=s K where le
参数：hHK : H <= K；hKG : K <= G；h : H <=s G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Graph.IsSpanningSubgraph.vertexSet_eq`：∀ {α : Type u_1} {β : Type u_2} {
H G : Graph α β}, H ≤s G → H.vertexSet = G.vertexSet
-/
lemma anti_right (hHK : H ≤ K) (hKG : K ≤ G) (h : H ≤s G) : H ≤s K where
  le := hHK
  vertexSet_eq := hHK.vertexSet_mono.antisymm <| hKG.vertexSet_mono.trans_eq h.vertexSet_eq.symm
/-
**Graph.IsSpanningSubgraph.mono_left** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsSpanning
Subgraph`。
形式化陈述：mono_left (hHK : H <= K) (hKG : K <= G) (h : H <=s G) : K <=s G where le
参数：hHK : H <= K；hKG : K <= G；h : H <=s G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Graph.IsSpanningSubgraph.vertexSet_eq`：∀ {α : Type u_1} {β : Type u_2} {
H G : Graph α β}, H ≤s G → H.vertexSet = G.vertexSet
-/
lemma mono_left (hHK : H ≤ K) (hKG : K ≤ G) (h : H ≤s G) : K ≤s G where
  le := hKG
  vertexSet_eq := hKG.vertexSet_mono.antisymm <| h.vertexSet_eq.symm.le.trans hHK.vertexSet_mono
/-
**Graph.IsSpanningSubgraph.ext_of_edgeSet** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsSpa
nningSubgraph`。
形式化陈述：ext_of_edgeSet (hE : E(H) = E(G)) (h : H <=s G) : H = G
参数：hE : E(H) = E(G)；h : H <=s G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.ext`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph α β
},   H₁.vertexSet = H₂.vertexSet → H₁.edgeSet = H₂.edgeSet → H₁.Compatible H₂ → 
H₁ = H₂
· 使用定理 `Graph.IsSpanningSubgraph.vertexSet_eq`：∀ {α : Type u_1} {β : Type u_2} {
H G : Graph α β}, H ≤s G → H.vertexSet = G.vertexSet
· 使用定理 `Graph.IsSubgraph.compatible`：∀ {α : Type u_1} {β : Type u_2} {G H : Grap
h α β}, H ≤ G → H.Compatible G
· 使用定理 `Graph.IsSpanningSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Grap
h α β}, H ≤s G → H.IsSubgraph G
-/
lemma ext_of_edgeSet (hE : E(H) = E(G)) (h : H ≤s G) : H = G :=
  h.compatible.ext h.vertexSet_eq hE

@[gcongr]
/-
**Graph.IsSpanningSubgraph.banana_mono** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsSpanni
ngSubgraph`。
形式化陈述：banana_mono (hF : F₁ subseteq F₂) : banana u v F₁ <=s banana u v F₂ where 
vertexSet_eq
参数：hF : F₁ subseteq F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.vertexSet_banana`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeS
et : Set β), (Graph.banana u v edgeSet).vertexSet = {u, v}
· 使用定理 `Graph.banana_isLink`：∀ {α : Type u_1} {β : Type u_2} (u v : α) (edgeSet 
: Set β) (e : β) (x y : α),   (Graph.banana u v edgeSet).IsLink e x y = (e ∈ edg
eSet ∧ (x…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma banana_mono (hF : F₁ ⊆ F₂) : banana u v F₁ ≤s banana u v F₂ where
  vertexSet_eq := rfl

end IsSpanningSubgraph

end SpanningSubgraph

section InducedSubgraph

/-! ### Induced Subgraphs -/

/-- `H ≤i G` (`Graph.IsInducedSubgraph`) is a subgraph of `G` such that every link of `G`
involving two vertices of `H` is also a link of `H`. -/
@[mk_iff]
/-
**Graph.IsInducedSubgraph** 是 Mathlib 中的一个归纳类型，位于命名空间 `Graph`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Graph α β → Graph α β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`H ≤i G` (`Graph.IsInducedSubgraph`) is a subgraph of `G` such that every link o
f `G`
involving two vertices of `H` is also a link of `H`.
-/
structure IsInducedSubgraph (H G : Graph α β) : Prop extends le : H ≤ G where
  isLink_of_mem_mem : ∀ ⦃e x y⦄, G.IsLink e x y → x ∈ V(H) → y ∈ V(H) → H.IsLink e x y

@[inherit_doc IsInducedSubgraph]
scoped infixl:50 " ≤i " => Graph.IsInducedSubgraph

namespace IsInducedSubgraph

/-
**Graph.IsInducedSubgraph.trans** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsInducedSubgra
ph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G G₁ G₂ : Graph α β},   G.IsInducedSubgra
ph G₁ → G₁.IsInducedSubgraph G₂ → G.IsInducedSubgraph G₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsSubgraph.trans`：∀ {α : Type u_1} {β : Type u_2} {G G₁ H : Graph 
α β}, H.IsSubgraph G → G.IsSubgraph G₁ → H.IsSubgraph G₁
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用定理 `Graph.IsInducedSubgraph.isLink_of_mem_mem`：∀ {α : Type u_1} {β : Type u_
2} {H G : Graph α β},   H.IsInducedSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, G.IsLink e 
x y → x ∈ H.vertexSet → y ∈ H.v…
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
-/
protected lemma trans (h₁ : G ≤i G₁) (h₂ : G₁ ≤i G₂) : G ≤i G₂ :=
  ⟨h₁.le.trans h₂.le, fun _ _ _ h hx hy ↦ h₁.isLink_of_mem_mem
    (h₂.isLink_of_mem_mem h (h₁.vertexSet_mono hx) (h₁.vertexSet_mono hy)) hx hy⟩
/-
**Graph.IsInducedSubgraph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph.IsInducedSubgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPartialOrder (Graph α β) (· ≤i ·) where
  refl G := ⟨le_refl G, by tauto⟩
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.1.antisymm h₂.1
/-
**Graph.IsInducedSubgraph.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsInducedSubgraph
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β}, G.IsInducedSubgraph G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsPartialOrder.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self :
 IsPartialOrder α r], IsPreorder α r
· 使用定理 `Graph.IsInducedSubgraph.instIsPartialOrder`：∀ {α : Type u_1} {β : Type u
_2}, IsPartialOrder (Graph α β) fun x1 x2 => x1.IsInducedSubgraph x2
-/
@[simp] protected lemma rfl : G ≤i G := refl G
/-
**Graph.IsInducedSubgraph.isLink_congr** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsInduce
dSubgraph`。
形式化陈述：isLink_congr (hx : x in V(H)) (hy : y in V(H)) (h : H <=i G) : H.IsLink e 
x y ↔ G.IsLink e x y
参数：hx : x in V(H)；hy : y in V(H)；h : H <=i G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
H : Graph α β}, H ≤ G → H.IsLink e x y → G.IsLink e x y
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用定理 `Graph.IsInducedSubgraph.isLink_of_mem_mem`：∀ {α : Type u_1} {β : Type u_
2} {H G : Graph α β},   H.IsInducedSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, G.IsLink e 
x y → x ∈ H.vertexSet → y ∈ H.v…
-/
lemma isLink_congr (hx : x ∈ V(H)) (hy : y ∈ V(H)) (h : H ≤i G) :
    H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨(·.mono h.le), fun hxy ↦ h.isLink_of_mem_mem hxy hx hy⟩
/-
**Graph.IsInducedSubgraph.adj_congr** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsInducedSu
bgraph`。
形式化陈述：adj_congr (hx : x in V(H)) (hy : y in V(H)) (h : H <=i G) : H.Adj x y ↔ G.
Adj x y
参数：hx : x in V(H)；hy : y in V(H)；h : H <=i G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Adj.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {G H : Graph α
 β}, H ≤ G → H.Adj x y → G.Adj x y
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用定理 `Graph.IsLink.adj`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G :
 Graph α β}, G.IsLink e x y → G.Adj x y
· 使用定理 `Graph.IsInducedSubgraph.isLink_of_mem_mem`：∀ {α : Type u_1} {β : Type u_
2} {H G : Graph α β},   H.IsInducedSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, G.IsLink e 
x y → x ∈ H.vertexSet → y ∈ H.v…
-/
lemma adj_congr (hx : x ∈ V(H)) (hy : y ∈ V(H)) (h : H ≤i G) : H.Adj x y ↔ G.Adj x y :=
  ⟨(·.mono h.le), fun ⟨_, hxy⟩ ↦ (h.isLink_of_mem_mem hxy hx hy).adj⟩
/-
**Graph.IsInducedSubgraph.anti_right** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsInducedS
ubgraph`。
形式化陈述：anti_right (hHK : H <= K) (hKG : K <= G) (h : H <=i G) : H <=i K where le
参数：hHK : H <= K；hKG : K <= G；h : H <=i G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsInducedSubgraph.isLink_of_mem_mem`：∀ {α : Type u_1} {β : Type u_
2} {H G : Graph α β},   H.IsInducedSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, G.IsLink e 
x y → x ∈ H.vertexSet → y ∈ H.v…
· 使用定理 `Graph.IsLink.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
H : Graph α β}, H ≤ G → H.IsLink e x y → G.IsLink e x y
-/
lemma anti_right (hHK : H ≤ K) (hKG : K ≤ G) (h : H ≤i G) : H ≤i K where
  le := hHK
  isLink_of_mem_mem _ _ _ hxy hx hy := h.isLink_of_mem_mem (hxy.mono hKG) hx hy
/-
**Graph.IsInducedSubgraph.le_of_le_subset** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsInd
ucedSubgraph`。
形式化陈述：le_of_le_subset (h' : K <= G) (hsu : V(K) subseteq V(H)) (h : H <=i G) : K
 <= H
参数：h' : K <= G；hsu : V(K) subseteq V(H)；h : H <=i G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Graph.Compatible.le_iff`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph 
α β},   H₁.Compatible H₂ → (H₁ ≤ H₂ ↔ H₁.vertexSet ⊆ H₂.vertexSet ∧ H₁.edgeSet ⊆
 H₂.edgeSet)
· 使用定理 `Graph.Compatible.of_le_le`：∀ {α : Type u_1} {β : Type u_2} {G H₁ H₂ : Gr
aph α β}, H₁ ≤ G → H₂ ≤ G → H₁.Compatible H₂
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用引理 `Graph.exists_isLink_of_mem_edgeSet`：exists_isLink_of_mem_edgeSet (h : e 
in E(G)) : exists x y, G.IsLink e x y
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
· 使用定理 `Graph.IsInducedSubgraph.isLink_of_mem_mem`：∀ {α : Type u_1} {β : Type u_
2} {H G : Graph α β},   H.IsInducedSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, G.IsLink e 
x y → x ∈ H.vertexSet → y ∈ H.v…
· 使用定理 `Graph.IsLink.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
H : Graph α β}, H ≤ G → H.IsLink e x y → G.IsLink e x y
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `Graph.IsLink.right_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β
} {G : Graph α β}, G.IsLink e x y → y ∈ G.vertexSet
-/
lemma le_of_le_subset (h' : K ≤ G) (hsu : V(K) ⊆ V(H)) (h : H ≤i G) : K ≤ H := by
  refine (Compatible.of_le_le h' h.le).le_iff.mpr ⟨hsu, fun e he ↦ ?_⟩
  obtain ⟨u, v, huv⟩ := K.exists_isLink_of_mem_edgeSet he
  exact h.2 (huv.mono h') (hsu huv.left_mem) (hsu huv.right_mem) |>.edge_mem
/-
**Graph.IsInducedSubgraph.ext_of_vertexSet** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsIn
ducedSubgraph`。
形式化陈述：ext_of_vertexSet (hV : V(H) = V(G)) (h : H <=i G) : H = G
参数：hV : V(H) = V(G)；h : H <=i G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Compatible.ext`：∀ {α : Type u_1} {β : Type u_2} {H₁ H₂ : Graph α β
},   H₁.vertexSet = H₂.vertexSet → H₁.edgeSet = H₂.edgeSet → H₁.Compatible H₂ → 
H₁ = H₂
· 使用引理 `antisymm`：antisymm [Std.Antisymm r] : a ≺ b -> b ≺ a -> a = b
· 使用定理 `Graph.IsSubgraph.edgeSet_mono`：∀ {α : Type u_1} {β : Type u_2} {G H : Gr
aph α β}, H ≤ G → H.edgeSet ⊆ G.edgeSet
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用引理 `Graph.exists_isLink_of_mem_edgeSet`：exists_isLink_of_mem_edgeSet (h : e 
in E(G)) : exists x y, G.IsLink e x y
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
· 使用定理 `Graph.IsInducedSubgraph.isLink_of_mem_mem`：∀ {α : Type u_1} {β : Type u_
2} {H G : Graph α β},   H.IsInducedSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, G.IsLink e 
x y → x ∈ H.vertexSet → y ∈ H.v…
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Graph.IsLink.right_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β
} {G : Graph α β}, G.IsLink e x y → y ∈ G.vertexSet
· 使用定理 `Graph.IsSubgraph.compatible`：∀ {α : Type u_1} {β : Type u_2} {G H : Grap
h α β}, H ≤ G → H.Compatible G
-/
lemma ext_of_vertexSet (hV : V(H) = V(G)) (h : H ≤i G) : H = G :=
  h.compatible.ext hV <| antisymm h.edgeSet_mono <| fun e he ↦ by
    obtain ⟨_, _, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
    exact h.isLink_of_mem_mem hxy (hV ▸ hxy.left_mem) (hV ▸ hxy.right_mem) |>.edge_mem

end IsInducedSubgraph

/-
**Graph.IsSubgraph.not_isInducedSubgraph_iff** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Is
Subgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β},   H ≤ G → (¬H.IsInduced
Subgraph G ↔ ∃ e x y, G.IsLink e x y ∧ x ∈ H.vertexSet ∧ y ∈ H.vertexSet ∧ e ∉ H
.edgeSet)
参数：¬H.IsInducedSubgraph G ↔ ∃ e x y, G.IsLink e x y ∧ x ∈ H.vertexSet ∧ y ∈ H.ve
rtexSet ∧ e ∉ H.edgeSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₂`：contrapose_iff₂ {p q : Prop} 
: (p ↔ ¬ q) -> (¬ p ↔ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `_private.Mathlib.Combinatorics.Graph.Subgraph.0.Graph.IsLink.anti_of_mem
`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G H : Graph α β},   G.IsLin
k e x y → H ≤ G → e ∈ H.edgeSet → H.IsLink e x y
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
· 使用定理 `Graph.IsInducedSubgraph.isLink_of_mem_mem`：∀ {α : Type u_1} {β : Type u_
2} {H G : Graph α β},   H.IsInducedSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, G.IsLink e 
x y → x ∈ H.vertexSet → y ∈ H.v…
-/
lemma IsSubgraph.not_isInducedSubgraph_iff (hHG : H ≤ G) :
    ¬ H ≤i G ↔ ∃ e x y, G.IsLink e x y ∧ x ∈ V(H) ∧ y ∈ V(H) ∧ e ∉ E(H) := by
  contrapose!; symm
  exact ⟨fun hnind ↦ ⟨hHG, fun e x y hxy hx hy => hxy.anti_of_mem hHG (hnind e x y hxy hx hy)⟩,
    fun hind _ _ _ hexy hx hy ↦ hind.isLink_of_mem_mem hexy hx hy |>.edge_mem⟩

end InducedSubgraph

section ClosedSubgraph

/-! ### Closed Subgraphs -/

/-- `H ≤c G` (`Graph.IsClosedSubgraph`) is a union of components of `G`. -/
@[mk_iff]
/-
**Graph.IsClosedSubgraph** 是 Mathlib 中的一个归纳类型，位于命名空间 `Graph`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Graph α β → Graph α β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`H ≤c G` (`Graph.IsClosedSubgraph`) is a union of components of `G`.
-/
structure IsClosedSubgraph (H G : Graph α β) : Prop extends
  isInducedSubgraph : IsInducedSubgraph H G where
  closed : ∀ ⦃e x⦄, G.Inc e x → x ∈ V(H) → e ∈ E(H)

@[inherit_doc IsClosedSubgraph]
scoped infixl:50 " ≤c " => Graph.IsClosedSubgraph

namespace IsClosedSubgraph

/-
**Graph.IsClosedSubgraph.mk'** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsClosedSubgraph`。
形式化陈述：mk' (hHG : H <= G) (hclosed : forall ⦃e x⦄, G.Inc e x -> x in V(H) -> e in
 E(H)) : H <=c G where le
参数：hHG : H <= G；hclosed : forall ⦃e x⦄, G.Inc e x -> x in V(H) -> e in E(H)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Combinatorics.Graph.Subgraph.0.Graph.IsLink.anti_of_mem
`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G H : Graph α β},   G.IsLin
k e x y → H ≤ G → e ∈ H.edgeSet → H.IsLink e x y
· 使用定理 `Graph.IsLink.inc_left`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → G.Inc e x
-/
lemma mk' (hHG : H ≤ G) (hclosed : ∀ ⦃e x⦄, G.Inc e x → x ∈ V(H) → e ∈ E(H)) : H ≤c G where
  le := hHG
  isLink_of_mem_mem _ _ _ he hx _ := he.anti_of_mem hHG (hclosed he.inc_left hx)
  closed _ _ he hx := hclosed he hx
/-
**Graph.IsClosedSubgraph.trans** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsClosedSubgraph
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G G₁ G₂ : Graph α β},   G.IsClosedSubgrap
h G₁ → G₁.IsClosedSubgraph G₂ → G.IsClosedSubgraph G₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Graph.IsClosedSubgraph.mk'`：mk' (hHG : H <= G) (hclosed : forall ⦃e x⦄, 
G.Inc e x -> x in V(H) -> e in E(H)) : H <=c G where le
· 使用定理 `Graph.IsSubgraph.trans`：∀ {α : Type u_1} {β : Type u_2} {G G₁ H : Graph 
α β}, H.IsSubgraph G → G.IsSubgraph G₁ → H.IsSubgraph G₁
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用定理 `Graph.IsClosedSubgraph.isInducedSubgraph`：∀ {α : Type u_1} {β : Type u_2
} {H G : Graph α β}, H.IsClosedSubgraph G → H.IsInducedSubgraph G
· 使用定理 `Graph.IsClosedSubgraph.closed`：∀ {α : Type u_1} {β : Type u_2} {H G : Gr
aph α β},   H.IsClosedSubgraph G → ∀ ⦃e : β⦄ ⦃x : α⦄, G.Inc e x → x ∈ H.vertexSe
t → e ∈ H.edgeSet
· 使用定理 `Graph.Inc.of_compatible`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β}
 {G H : Graph α β},   G.Compatible H → e ∈ H.edgeSet → G.Inc e x → H.Inc e x
· 使用定理 `Graph.IsSubgraph.compatible'`：∀ {α : Type u_1} {β : Type u_2} {G H : Gra
ph α β}, G ≤ H → H.Compatible G
· 使用定理 `Graph.IsSubgraph.vertexSet_mono`：∀ {α : Type u_1} {β : Type u_2} {H G : 
Graph α β}, H.IsSubgraph G → H.vertexSet ⊆ G.vertexSet
-/
protected lemma trans (h₁ : G ≤c G₁) (h₂ : G₁ ≤c G₂) : G ≤c G₂ :=
  mk' (h₁.le.trans h₂.le) fun _ _ h hx ↦ h₁.closed (h.of_compatible h₂.compatible'
    (h₂.closed h (h₁.vertexSet_mono hx))) hx
/-
**Graph.IsClosedSubgraph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph.IsClosedSubgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPartialOrder (Graph α β) (· ≤c ·) where
  refl _ := mk' le_rfl fun _ _ h _ ↦ h.edge_mem
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h₁ h₂ := h₁.le.antisymm h₂.le
/-
**Graph.IsClosedSubgraph.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsClosedSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β}, G.IsClosedSubgraph G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsPartialOrder.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self :
 IsPartialOrder α r], IsPreorder α r
· 使用定理 `Graph.IsClosedSubgraph.instIsPartialOrder`：∀ {α : Type u_1} {β : Type u_
2}, IsPartialOrder (Graph α β) fun x1 x2 => x1.IsClosedSubgraph x2
-/
@[simp] protected lemma rfl : G ≤c G := refl G
/-
**Graph.IsClosedSubgraph.inc_congr** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsClosedSubg
raph`。
形式化陈述：inc_congr (hx : x in V(H)) (hHG : H <=c G) : H.Inc e x ↔ G.Inc e x
参数：hx : x in V(H)；hHG : H <=c G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Inc.mono`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G H : G
raph α β}, H ≤ G → H.Inc e x → G.Inc e x
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用定理 `Graph.IsClosedSubgraph.isInducedSubgraph`：∀ {α : Type u_1} {β : Type u_2
} {H G : Graph α β}, H.IsClosedSubgraph G → H.IsInducedSubgraph G
· 使用定理 `Graph.Inc.of_compatible`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β}
 {G H : Graph α β},   G.Compatible H → e ∈ H.edgeSet → G.Inc e x → H.Inc e x
· 使用定理 `Graph.IsSubgraph.compatible'`：∀ {α : Type u_1} {β : Type u_2} {G H : Gra
ph α β}, G ≤ H → H.Compatible G
· 使用定理 `Graph.IsClosedSubgraph.closed`：∀ {α : Type u_1} {β : Type u_2} {H G : Gr
aph α β},   H.IsClosedSubgraph G → ∀ ⦃e : β⦄ ⦃x : α⦄, G.Inc e x → x ∈ H.vertexSe
t → e ∈ H.edgeSet
-/
lemma inc_congr (hx : x ∈ V(H)) (hHG : H ≤c G) : H.Inc e x ↔ G.Inc e x :=
  ⟨(·.mono hHG.le), fun he ↦ he.of_compatible hHG.compatible' (hHG.closed he hx)⟩
/-
**Graph.IsClosedSubgraph.isLink_congr** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsClosedS
ubgraph`。
形式化陈述：isLink_congr (hx : x in V(H)) (hHG : H <=c G) : H.IsLink e x y ↔ G.IsLink 
e x y
参数：hx : x in V(H)；hHG : H <=c G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
H : Graph α β}, H ≤ G → H.IsLink e x y → G.IsLink e x y
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用定理 `Graph.IsClosedSubgraph.isInducedSubgraph`：∀ {α : Type u_1} {β : Type u_2
} {H G : Graph α β}, H.IsClosedSubgraph G → H.IsInducedSubgraph G
· 使用定理 `_private.Mathlib.Combinatorics.Graph.Subgraph.0.Graph.IsLink.anti_of_mem
`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G H : Graph α β},   G.IsLin
k e x y → H ≤ G → e ∈ H.edgeSet → H.IsLink e x y
· 使用定理 `Graph.Inc.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G :
 Graph α β}, G.Inc e x → e ∈ G.edgeSet
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Graph.IsClosedSubgraph.inc_congr`：inc_congr (hx : x in V(H)) (hHG : H <=
c G) : H.Inc e x ↔ G.Inc e x
· 使用定理 `Graph.IsLink.inc_left`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → G.Inc e x
-/
lemma isLink_congr (hx : x ∈ V(H)) (hHG : H ≤c G) : H.IsLink e x y ↔ G.IsLink e x y :=
  ⟨(·.mono hHG.le), fun h ↦ h.anti_of_mem hHG.le ((hHG.inc_congr hx).mpr h.inc_left).edge_mem⟩
/-
**Graph.IsClosedSubgraph.mem_iff_of_isLink** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsCl
osedSubgraph`。
形式化陈述：mem_iff_of_isLink (he : G.IsLink e x y) (hHG : H <=c G) : x in V(H) ↔ y in
 V(H)
参数：he : G.IsLink e x y；hHG : H <=c G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.IsLink.right_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β
} {G : Graph α β}, G.IsLink e x y → y ∈ G.vertexSet
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Graph.IsClosedSubgraph.isLink_congr`：isLink_congr (hx : x in V(H)) (hHG 
: H <=c G) : H.IsLink e x y ↔ G.IsLink e x y
· 使用引理 `Graph.isLink_comm`：isLink_comm : G.IsLink e x y ↔ G.IsLink e y x
-/
lemma mem_iff_of_isLink (he : G.IsLink e x y) (hHG : H ≤c G) : x ∈ V(H) ↔ y ∈ V(H) := by
  refine ⟨fun hin ↦ ?_, fun hin ↦ ?_⟩
  on_goal 2 => rw [isLink_comm] at he
  all_goals rw [← hHG.isLink_congr hin] at he; exact he.right_mem
/-
**Graph.IsClosedSubgraph.mem_tfae_of_isLink** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsC
losedSubgraph`。
形式化陈述：mem_tfae_of_isLink (he : G.IsLink e x y) (hHG : H <=c G) : List.TFAE [x in
 V(H), y in V(H), e in E(H)]
参数：he : G.IsLink e x y；hHG : H <=c G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Graph.IsClosedSubgraph.mem_iff_of_isLink`：mem_iff_of_isLink (he : G.IsLi
nk e x y) (hHG : H <=c G) : x in V(H) ↔ y in V(H)
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Graph.IsClosedSubgraph.isLink_congr`：isLink_congr (hx : x in V(H)) (hHG 
: H <=c G) : H.IsLink e x y ↔ G.IsLink e x y
· 使用定理 `Graph.IsLink.symm`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
: Graph α β}, G.IsLink e x y → G.IsLink e y x
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `_private.Mathlib.Combinatorics.Graph.Subgraph.0.Graph.IsLink.anti_of_mem
`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G H : Graph α β},   G.IsLin
k e x y → H ≤ G → e ∈ H.edgeSet → H.IsLink e x y
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用定理 `Graph.IsClosedSubgraph.isInducedSubgraph`：∀ {α : Type u_1} {β : Type u_2
} {H G : Graph α β}, H.IsClosedSubgraph G → H.IsInducedSubgraph G
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
-/
lemma mem_tfae_of_isLink (he : G.IsLink e x y) (hHG : H ≤c G) :
    List.TFAE [x ∈ V(H), y ∈ V(H), e ∈ E(H)] := by
  tfae_have 1 → 2 := (hHG.mem_iff_of_isLink he).mp
  tfae_have 2 → 3 := (hHG.isLink_congr · |>.mpr he.symm |>.edge_mem)
  tfae_have 3 → 1 := (he.anti_of_mem hHG.le · |>.left_mem)
  tfae_finish
/-
**Graph.IsClosedSubgraph.adj_congr** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsClosedSubg
raph`。
形式化陈述：adj_congr (hx : x in V(H)) (hHG : H <=c G) : H.Adj x y ↔ G.Adj x y
参数：hx : x in V(H)；hHG : H <=c G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Adj.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {G H : Graph α
 β}, H ≤ G → H.Adj x y → G.Adj x y
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用定理 `Graph.IsClosedSubgraph.isInducedSubgraph`：∀ {α : Type u_1} {β : Type u_2
} {H G : Graph α β}, H.IsClosedSubgraph G → H.IsInducedSubgraph G
· 使用定理 `Graph.IsLink.adj`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G :
 Graph α β}, G.IsLink e x y → G.Adj x y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Graph.IsClosedSubgraph.isLink_congr`：isLink_congr (hx : x in V(H)) (hHG 
: H <=c G) : H.IsLink e x y ↔ G.IsLink e x y
-/
lemma adj_congr (hx : x ∈ V(H)) (hHG : H ≤c G) : H.Adj x y ↔ G.Adj x y :=
  ⟨(·.mono hHG.le), fun ⟨_, hxy⟩ ↦ (hHG.isLink_congr hx |>.mpr hxy).adj⟩
/-
**Graph.IsClosedSubgraph.mem_iff_of_adj** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsClose
dSubgraph`。
形式化陈述：mem_iff_of_adj (hxy : G.Adj x y) (hHG : H <=c G) : x in V(H) ↔ y in V(H)
参数：hxy : G.Adj x y；hHG : H <=c G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Graph.IsClosedSubgraph.mem_iff_of_isLink`：mem_iff_of_isLink (he : G.IsLi
nk e x y) (hHG : H <=c G) : x in V(H) ↔ y in V(H)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma mem_iff_of_adj (hxy : G.Adj x y) (hHG : H ≤c G) : x ∈ V(H) ↔ y ∈ V(H) :=
  hHG.mem_iff_of_isLink hxy.choose_spec
/-
**Graph.IsClosedSubgraph.anti_right** 是 Mathlib 中的一个引理，位于命名空间 `Graph.IsClosedSub
graph`。
形式化陈述：anti_right (hHG₁ : H <= G₁) (hG₁ : G₁ <= G) (hHG : H <=c G) : H <=c G₁
参数：hHG₁ : H <= G₁；hG₁ : G₁ <= G；hHG : H <=c G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Graph.IsClosedSubgraph.mk'`：mk' (hHG : H <= G) (hclosed : forall ⦃e x⦄, 
G.Inc e x -> x in V(H) -> e in E(H)) : H <=c G where le
· 使用定理 `Graph.Inc.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G :
 Graph α β}, G.Inc e x → e ∈ G.edgeSet
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Graph.IsClosedSubgraph.inc_congr`：inc_congr (hx : x in V(H)) (hHG : H <=
c G) : H.Inc e x ↔ G.Inc e x
· 使用定理 `Graph.Inc.mono`：∀ {α : Type u_1} {β : Type u_2} {x : α} {e : β} {G H : G
raph α β}, H ≤ G → H.Inc e x → G.Inc e x
-/
lemma anti_right (hHG₁ : H ≤ G₁) (hG₁ : G₁ ≤ G) (hHG : H ≤c G) : H ≤c G₁ :=
  mk' hHG₁ fun _ _ he hx ↦ hHG.inc_congr hx |>.mpr (he.mono hG₁) |>.edge_mem

end IsClosedSubgraph

/-
**Graph.IsInducedSubgraph.not_isClosedSubgraph_iff_exists_adj** 是 Mathlib 中的一个定理
，位于命名空间 `Graph.IsInducedSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β},   H.IsInducedSubgraph G
 → (¬H.IsClosedSubgraph G ↔ ∃ x y, G.Adj x y ∧ x ∈ H.vertexSet ∧ y ∉ H.vertexSet
)
参数：¬H.IsClosedSubgraph G ↔ ∃ x y, G.Adj x y ∧ x ∈ H.vertexSet ∧ y ∉ H.vertexSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₂`：contrapose_iff₂ {p q : Prop} 
: (p ↔ ¬ q) -> (¬ p ↔ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Graph.IsLink.edge_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → e ∈ G.edgeSet
· 使用定理 `Graph.IsInducedSubgraph.isLink_of_mem_mem`：∀ {α : Type u_1} {β : Type u_
2} {H G : Graph α β},   H.IsInducedSubgraph G → ∀ ⦃e : β⦄ ⦃x y : α⦄, G.IsLink e 
x y → x ∈ H.vertexSet → y ∈ H.v…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Graph.IsClosedSubgraph.mem_iff_of_adj`：mem_iff_of_adj (hxy : G.Adj x y) 
(hHG : H <=c G) : x in V(H) ↔ y in V(H)
-/
lemma IsInducedSubgraph.not_isClosedSubgraph_iff_exists_adj (hHG : H ≤i G) :
    ¬ H ≤c G ↔ ∃ x y, G.Adj x y ∧ x ∈ V(H) ∧ y ∉ V(H) := by
  contrapose!; symm
  exact ⟨fun hncl ↦ ⟨hHG, fun e x ⟨y, hexy⟩ hxH =>
    hHG.isLink_of_mem_mem hexy hxH (hncl x y ⟨e, hexy⟩ hxH) |>.edge_mem⟩,
    fun hcl _ _ hexy ↦ (hcl.mem_iff_of_adj hexy).mp⟩
/-
**Graph.IsInducedSubgraph.not_isClosedSubgraph_iff_exists_isLink** 是 Mathlib 中的一
个定理，位于命名空间 `Graph.IsInducedSubgraph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β},   H.IsInducedSubgraph G
 → (¬H.IsClosedSubgraph G ↔ ∃ e x y, G.IsLink e x y ∧ x ∈ H.vertexSet ∧ y ∉ H.ve
rtexSet)
参数：¬H.IsClosedSubgraph G ↔ ∃ e x y, G.IsLink e x y ∧ x ∈ H.vertexSet ∧ y ∉ H.ver
texSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.IsInducedSubgraph.not_isClosedSubgraph_iff_exists_adj`：∀ {α : Type
 u_1} {β : Type u_2} {G H : Graph α β},   H.IsInducedSubgraph G → (¬H.IsClosedSu
bgraph G ↔ ∃ x y, G.Adj x y ∧ x ∈ H.vertexSet ∧ y…
-/
lemma IsInducedSubgraph.not_isClosedSubgraph_iff_exists_isLink (hHG : H ≤i G) :
    ¬ H ≤c G ↔ ∃ e x y, G.IsLink e x y ∧ x ∈ V(H) ∧ y ∉ V(H) := by
  rw [hHG.not_isClosedSubgraph_iff_exists_adj]
  unfold Adj
  tauto

end ClosedSubgraph

section OrderBot

/-
**Graph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (Graph α β) where
  bot := noEdge ∅ β
  bot_le G := by constructor <;> simp
/-
**Graph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Graph α β) where
  default := ⊥
/-
**Graph.noEdge_empty** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2}, Graph.noEdge ∅ β = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] lemma noEdge_empty : Graph.noEdge (∅ : Set α) β = ⊥ := rfl
/-
**Graph.vertexSet_bot** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2}, ⊥.vertexSet = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma vertexSet_bot : V((⊥ : Graph α β)) = ∅ := rfl
/-
**Graph.edgeSet_bot** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2}, ⊥.edgeSet = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma edgeSet_bot : E((⊥ : Graph α β)) = ∅ := rfl
/-
**Graph.bot_isClosedSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `Graph`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β), ⊥.IsClosedSubgraph G
参数：G : Graph α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Graph.IsClosedSubgraph.mk'`：mk' (hHG : H <= G) (hclosed : forall ⦃e x⦄, 
G.Inc e x -> x in V(H) -> e in E(H)) : H <=c G where le
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma bot_isClosedSubgraph (G : Graph α β) : ⊥ ≤c G := IsClosedSubgraph.mk' bot_le (by simp)
/-
**Graph.eq_bot_or_vertexSet_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：eq_bot_or_vertexSet_nonempty (G : Graph α β) : G = ⊥ ∨ V(G).Nonempty
参数：G : Graph α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Graph.ext`：∀ {α : Type u_1} {β : Type u_2} {G₁ G₂ : Graph α β},   G₁.ver
texSet = G₂.vertexSet → (∀ (e : β) (x y : α), G₁.IsLink e x y ↔ G₂.IsLink e x y…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
lemma eq_bot_or_vertexSet_nonempty (G : Graph α β) : G = ⊥ ∨ V(G).Nonempty := by
  refine (em (V(G) = ∅)).elim (fun he ↦ .inl (Graph.ext he fun e x y ↦ ?_)) (Or.inr ∘
    nonempty_iff_ne_empty.mpr)
  simp only [edgeSet_bot, mem_empty_iff_false, not_false_eq_true, not_isLink_of_notMem_edgeSet,
    iff_false]
  exact fun h ↦ by simpa [he] using h.left_mem
/-
**Graph.vertexSet_eq_empty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：vertexSet_eq_empty_iff : V(G) = ∅ ↔ G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma vertexSet_eq_empty_iff : V(G) = ∅ ↔ G = ⊥ := by
  refine ⟨fun h ↦ bot_le.antisymm' ⟨by simp [h], fun e x y he ↦ ?_⟩, fun h ↦ by simp [h]⟩
  simpa [h] using he.left_mem

@[push, simp]
/-
**Graph.ne_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：ne_bot_iff : G != ⊥ ↔ V(G).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ne_bot_iff : G ≠ ⊥ ↔ V(G).Nonempty :=
  not_iff_not.mp <| by simp [vertexSet_eq_empty_iff, not_nonempty_iff_eq_empty]

@[push, simp]
/-
**Graph.vertexSet_not_nonempty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：vertexSet_not_nonempty_iff : ¬ V(G).Nonempty ↔ G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma vertexSet_not_nonempty_iff : ¬ V(G).Nonempty ↔ G = ⊥ := by
  simp [vertexSet_eq_empty_iff, not_nonempty_iff_eq_empty]
/-
**Graph.ne_bot_of_mem_vertexSet** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：ne_bot_of_mem_vertexSet (h : x in V(G)) : G != ⊥
参数：h : x in V(G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Graph.ne_bot_iff`：ne_bot_iff : G != ⊥ ↔ V(G).Nonempty
-/
lemma ne_bot_of_mem_vertexSet (h : x ∈ V(G)) : G ≠ ⊥ := ne_bot_iff.mpr ⟨x, h⟩

@[simp]
/-
**Graph.isSpanningSubgraph_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：isSpanningSubgraph_bot_iff : G <=s ⊥ ↔ G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Graph.IsSpanningSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Grap
h α β}, H ≤s G → H.IsSubgraph G
· 使用定理 `Graph.IsSpanningSubgraph.rfl`：∀ {α : Type u_1} {β : Type u_2} {G : Graph
 α β}, G ≤s G
-/
lemma isSpanningSubgraph_bot_iff : G ≤s ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

@[simp]
/-
**Graph.isInducedSubgraph_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：isInducedSubgraph_bot_iff : G <=i ⊥ ↔ G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用定理 `Graph.IsInducedSubgraph.rfl`：∀ {α : Type u_1} {β : Type u_2} {G : Graph 
α β}, G.IsInducedSubgraph G
-/
lemma isInducedSubgraph_bot_iff : G ≤i ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩

@[simp]
/-
**Graph.isClosedSubgraph_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：isClosedSubgraph_bot_iff : G <=c ⊥ ↔ G = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Graph.IsInducedSubgraph.le`：∀ {α : Type u_1} {β : Type u_2} {H G : Graph
 α β}, H.IsInducedSubgraph G → H.IsSubgraph G
· 使用定理 `Graph.IsClosedSubgraph.isInducedSubgraph`：∀ {α : Type u_1} {β : Type u_2
} {H G : Graph α β}, H.IsClosedSubgraph G → H.IsInducedSubgraph G
· 使用定理 `Graph.IsClosedSubgraph.rfl`：∀ {α : Type u_1} {β : Type u_2} {G : Graph α
 β}, G.IsClosedSubgraph G
-/
lemma isClosedSubgraph_bot_iff : G ≤c ⊥ ↔ G = ⊥ :=
  ⟨fun h => le_bot_iff.mp h.le, fun h => h ▸ .rfl⟩
/-
**Graph.not_disjoint_of_mem_mem** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：not_disjoint_of_mem_mem (h : x in V(G)) (h' : x in V(H)) : ¬ Disjoint G H
参数：h : x in V(G)；h' : x in V(H)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Graph.vertexSet_noEdge`：∀ {α : Type u_1} (vertexSet : Set α) (β : Type u
_3), (Graph.noEdge vertexSet β).vertexSet = vertexSet
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma not_disjoint_of_mem_mem (h : x ∈ V(G)) (h' : x ∈ V(H)) : ¬ Disjoint G H := by
  simp only [Disjoint, le_bot_iff, not_forall, ne_eq, ne_bot_iff]
  use noEdge {x} β
  simp [h, h']

end OrderBot

end Graph

