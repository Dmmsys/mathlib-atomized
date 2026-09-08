/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Tactic.Linarith
/-!
# Five-wheel like graphs

This file defines an `IsFiveWheelLike` structure in a graph, and describes properties of these
structures as well as graphs which avoid this structure. These have two key uses:
* We use them to prove that a maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is
  complete-multipartite: `colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree`.
* They play a key role in Brandt's proof of the Andrásfai-Erdős-Sós theorem, which is where they
  first appeared. We give this proof below, see `colorable_of_cliqueFree_lt_minDegree`.

If `G` is maximally `Kᵣ₊₂`-free and `¬ G.Adj x y` (with `x ≠ y`) then there exists an `r`-set `s`
such that `s ∪ {x}` and `s ∪ {y}` are both `r + 1`-cliques.

If `¬ G.IsCompleteMultipartite` then it contains a `G.IsPathGraph3Compl v w₁ w₂` consisting of
an edge `w₁w₂` and a vertex `v` such that `vw₁` and `vw₂` are non-edges.

Hence any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite must contain distinct
vertices `v, w₁, w₂`, together with `r`-sets `s` and `t`, such that `{v, w₁, w₂}` induces the
single edge `w₁w₂`, `s ∪ t` is disjoint from `{v, w₁, w₂}`, and `s ∪ {v}`, `t ∪ {v}`, `s ∪ {w₁}` and
`t ∪ {w₂}` are all `r + 1`-cliques.

This leads to the definition of an `IsFiveWheelLike` structure which can be found in any maximally
`Kᵣ₊₂`-free graph that is not complete-multipartite (see
`exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`).

One key parameter in any such structure is the number of vertices common to all of the cliques: we
denote this quantity by `k = #(s ∩ t)` (and we will refer to such a structure as `Wᵣ,ₖ` below.)

The first interesting cases of such structures are `W₁,₀` and `W₂,₁`: `W₁,₀` is a 5-cycle,
while `W₂,₁` is a 5-cycle with an extra central hub vertex adjacent to all other vertices
(i.e. `W₂,₁` resembles a wheel with five spokes).

```
                 `W₁,₀`       v                 `W₂,₁`      v
                           /     \                       /  |  \
                          s       t                     s ─ u ─ t
                           \     /                       \ / \ /
                           w₁ ─ w₂                       w₁ ─ w₂
```

## Main definitions

* `SimpleGraph.IsFiveWheelLike`: predicate for `v w₁ w₂ s t` to form a 5-wheel-like subgraph of
  `G` with `r`-sets `s` and `t`, and vertices `v w₁ w₂` forming an `IsPathGraph3Compl` and
  `#(s ∩ t) = k`.

* `SimpleGraph.FiveWheelLikeFree`: predicate for `G` to have no `IsFiveWheelLike r k` subgraph.

## Implementation notes
The definitions of `IsFiveWheelLike` and `IsFiveWheelLikeFree` in this file have `r` shifted by two
compared to the definitions in Brandt **On the structure of graphs with bounded clique number**

The definition of `IsFiveWheelLike` does not contain the facts that `#s = r` and `#t = r` but we
deduce these later as `card_left` and `card_right`.

Although `#(s ∩ t)` can easily be derived from `s` and `t` we include the `IsFiveWheelLike` field
`card_inter : #(s ∩ t) = k` to match the informal / paper definitions and to simplify some
statements of results and match our definition of `IsFiveWheelLikeFree`.

The vertex set of an `IsFiveWheel` structure `Wᵣ,ₖ` is `{v, w₁, w₂} ∪ s ∪ t : Finset α`.
We will need to refer to this consistently and choose the following formulation:
`{v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t)))` which is definitionally equal to
`insert v <| insert w₁ <| insert w₂ <| s ∪ t`.

## References

* [B. Andrásfai, P Erdős, V. T. Sós
  **On the connection between chromatic number, maximal clique, and minimal degree of a graph**
  https://doi.org/10.1016/0012-365X(74)90133-2][andrasfaiErdosSos1974]

* [S. Brandt **On the structure of graphs with bounded clique number**
  https://doi.org/10.1007/s00493-003-0042-z][brandt2003]
-/

@[expose] public section

local notation "‖" x "‖" => Fintype.card x

open Finset SimpleGraph

variable {α : Type*} {a b c : α} {s : Finset α} {G : SimpleGraph α} {r k : ℕ}

namespace SimpleGraph

section withDecEq
variable [DecidableEq α]

/-
**SimpleGraph.IsNClique.insert_insert** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsNClique.insert_insert (h1 : G.IsNClique r (insert a s))
    (h2 : G.IsNClique r (insert b s)) (h3 : b ∉ s) (ha : G.Adj a b) :
    G.IsNClique (r + 1) (insert b (insert a s)) := by
  apply h1.insert (fun b hb ↦ ?_)
  obtain (rfl | h) := mem_insert.1 hb
  · exact ha.symm
  · exact h2.1 (mem_insert_self _ s) (mem_insert_of_mem h) <| fun h' ↦ (h3 (h' ▸ h)).elim
/-
**SimpleGraph.IsNClique.insert_insert_erase** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsNClique.insert_insert_erase (hs : G.IsNClique r (insert a s)) (hc : c ∈ s)
    (ha : a ∉ s) (hd : ∀ w ∈ insert a s, w ≠ c → G.Adj w b) :
    G.IsNClique r (insert a (insert b (erase s c))) := by
  rw [insert_comm, ← erase_insert_of_ne (fun h : a = c ↦ ha (h ▸ hc) |>.elim)]
  simp_rw [adj_comm, ← notMem_singleton] at hd
  exact hs.insert_erase (fun _ h ↦ hd _ (mem_sdiff.1 h).1 (mem_sdiff.1 h).2) (mem_insert_of_mem hc)

/--
An `IsFiveWheelLike r k v w₁ w₂ s t` structure in `G` consists of vertices `v w₁ w₂` and `r`-sets
`s` and `t` such that `{v, w₁, w₂}` induces the single edge `w₁w₂` (i.e. they form an
`IsPathGraph3Compl`), `v, w₁, w₂ ∉ s ∪ t`, `s ∪ {v}, t ∪ {v}, s ∪ {w₁}, t ∪ {w₂}` are all
`(r + 1)`-cliques and `#(s ∩ t) = k`. (If `G` is maximally `(r + 2)`-cliquefree and not complete
multipartite then `G` will contain such a structure: see
`exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`.)
-/
@[grind]
/-
**SimpleGraph.IsFiveWheelLike** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → SimpleGraph α → ℕ → ℕ → α → α → α → Fin
set α → Finset α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `IsFiveWheelLike r k v w₁ w₂ s t` structure in `G` consists of vertices `v w₁
 w₂` and `r`-sets
`s` and `t` such that `{v, w₁, w₂}` induces the single edge `w₁w₂` (i.e. they fo
rm an
`IsPathGraph3Compl`), `v, w₁, w₂ ∉ s ∪ t`, `s ∪ {v}, t ∪ {v}, s ∪ {w₁}, t ∪ {w₂}
` are all
`(r + 1)`-cliques and `#(s ∩ t) = k`. (If `G` is maximally `(r + 2)`-cliquefree 
and not complete
multipartite then `G` will contain such a structure: see
`exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite`.)
-/
structure IsFiveWheelLike (G : SimpleGraph α) (r k : ℕ) (v w₁ w₂ : α) (s t : Finset α) :
    Prop where
  /-- `{v, w₁, w₂}` induces the single edge `w₁w₂` -/
  isPathGraph3Compl : G.IsPathGraph3Compl v w₁ w₂
  notMem_left : v ∉ s
  notMem_right : v ∉ t
  fst_notMem : w₁ ∉ s
  snd_notMem : w₂ ∉ t
  isNClique_left : G.IsNClique (r + 1) (insert v s)
  isNClique_fst_left : G.IsNClique (r + 1) (insert w₁ s)
  isNClique_right : G.IsNClique (r + 1) (insert v t)
  isNClique_snd_right : G.IsNClique (r + 1) (insert w₂ t)
  card_inter : #(s ∩ t) = k
/-
**SimpleGraph.exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipa
rtite** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite (h
 : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipartite)
 : exists v w₁ w₂ s t, G.IsFiveWheelLike r #(s inter t) v w₁ w₂ s t
参数：h : Maximal (fun H => H.CliqueFree (r + 2)) G；hnc : ¬ G.IsCompleteMultipartit
e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_isPathGraph3Compl_of_not_isCompleteMultipartite`：exis
ts_isPathGraph3Compl_of_not_isCompleteMultipartite (h : ¬ IsCompleteMultipartite
 G) : exists v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂
· 使用引理 `SimpleGraph.exists_of_maximal_cliqueFree_not_adj`：exists_of_maximal_cliq
ueFree_not_adj [DecidableEq α] (h : Maximal (fun H => H.CliqueFree (n + 1)) G) {
x y : α} (hne : x != y) (hn : ¬ G.Adj …
· 使用引理 `SimpleGraph.IsPathGraph3Compl.ne_fst`：ne_fst (h2 : G.IsPathGraph3Compl v
 w₁ w₂) : v != w₁
· 使用定理 `SimpleGraph.IsPathGraph3Compl.not_adj_fst`：∀ {α : Type u} {G : SimpleGra
ph α} {v w₁ w₂ : α}, G.IsPathGraph3Compl v w₁ w₂ → ¬G.Adj v w₁
· 使用引理 `SimpleGraph.IsPathGraph3Compl.ne_snd`：ne_snd (h2 : G.IsPathGraph3Compl v
 w₁ w₂) : v != w₂
· 使用定理 `SimpleGraph.IsPathGraph3Compl.not_adj_snd`：∀ {α : Type u} {G : SimpleGra
ph α} {v w₁ w₂ : α}, G.IsPathGraph3Compl v w₁ w₂ → ¬G.Adj v w₂
-/
lemma exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite
    (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipartite) :
    ∃ v w₁ w₂ s t, G.IsFiveWheelLike r #(s ∩ t) v w₁ w₂ s t := by
  obtain ⟨v, w₁, w₂, p3⟩ := exists_isPathGraph3Compl_of_not_isCompleteMultipartite hnc
  obtain ⟨s, h1, h2, h3, h4⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_fst p3.not_adj_fst
  obtain ⟨t, h5, h6, h7, h8⟩ := exists_of_maximal_cliqueFree_not_adj h p3.ne_snd p3.not_adj_snd
  exact ⟨_, _, _, _, _, p3, h1, h5, h2, h6, h3, h4, h7, h8, rfl⟩

/-- `G.FiveWheelLikeFree r k` means there is no `IsFiveWheelLike r k` structure in `G`. -/
/-
**SimpleGraph.FiveWheelLikeFree** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：FiveWheelLikeFree (G : SimpleGraph α) (r k : Nat) : Prop
参数：G : SimpleGraph α；r k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G.FiveWheelLikeFree r k` means there is no `IsFiveWheelLike r k` structure in `
G`.
-/
def FiveWheelLikeFree (G : SimpleGraph α) (r k : ℕ) : Prop :=
  ∀ {v w₁ w₂ s t}, ¬ G.IsFiveWheelLike r k v w₁ w₂ s t

namespace IsFiveWheelLike

variable {v w₁ w₂ : α} {t : Finset α} (hw : G.IsFiveWheelLike r k v w₁ w₂ s t)

include hw

/-
**SimpleGraph.IsFiveWheelLike.symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsFive
WheelLike`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} {G : SimpleGraph α} {r k : ℕ} [inst : Deci
dableEq α] {v w₁ w₂ : α} {t : Finset α},   G.IsFiveWheelLike r k v w₁ w₂ s t → G
.IsFiveWheelLike r k v w₂ w₁ t s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsPathGraph3Compl.symm`：∀ {α : Type u} {G : SimpleGraph α} {
v w₁ w₂ : α}, G.IsPathGraph3Compl v w₁ w₂ → G.IsPathGraph3Compl v w₂ w₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
-/
@[symm] lemma symm : G.IsFiveWheelLike r k v w₂ w₁ t s :=
  let ⟨p2, d1, d2, d3, d4, c1, c2, c3, c4, hk⟩ := hw
  ⟨p2.symm, d2, d1, d4, d3, c3, c4, c1, c2, by rwa [inter_comm]⟩

@[grind →]
/-
**SimpleGraph.IsFiveWheelLike.fst_notMem_right** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.IsFiveWheelLike`。
形式化陈述：fst_notMem_right : w₁ ∉ t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsPathGraph3Compl.not_adj_fst`：∀ {α : Type u} {G : SimpleGra
ph α} {v w₁ w₂ : α}, G.IsPathGraph3Compl v w₁ w₂ → ¬G.Adj v w₁
· 使用定理 `SimpleGraph.IsFiveWheelLike.isPathGraph3Compl`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G
.IsFiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_right`：∀ {α : Type u_1} [inst : De
cidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G.I
sFiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用引理 `SimpleGraph.IsPathGraph3Compl.ne_fst`：ne_fst (h2 : G.IsPathGraph3Compl v
 w₁ w₂) : v != w₁
-/
lemma fst_notMem_right : w₁ ∉ t :=
  fun h ↦ hw.isPathGraph3Compl.not_adj_fst <| hw.isNClique_right.1 (mem_insert_self ..)
    (mem_insert_of_mem h) hw.isPathGraph3Compl.ne_fst

@[grind →]
/-
**SimpleGraph.IsFiveWheelLike.snd_notMem_left** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph.IsFiveWheelLike`。
形式化陈述：snd_notMem_left : w₂ ∉ s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.IsFiveWheelLike.fst_notMem_right`：fst_notMem_right : w₁ ∉ t
· 使用定理 `SimpleGraph.IsFiveWheelLike.symm`：∀ {α : Type u_1} {s : Finset α} {G : S
impleGraph α} {r k : ℕ} [inst : DecidableEq α] {v w₁ w₂ : α} {t : Finset α},   G
.IsFiveWheelLike r k v…
-/
lemma snd_notMem_left : w₂ ∉ s := hw.symm.fst_notMem_right

/--
Any graph containing an `IsFiveWheelLike r k` structure is not `(r + 1)`-colorable.
-/
/-
**SimpleGraph.IsFiveWheelLike.not_colorable_succ** 是 Mathlib 中的一个引理，位于命名空间 `Simp
leGraph.IsFiveWheelLike`。
形式化陈述：not_colorable_succ : ¬ G.Colorable (r + 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Coloring.surjOn_of_card_le_isClique`：∀ {V : Type u} {G : Sim
pleGraph V} {α : Type u_2} [inst : Fintype α] {s : Finset V},   G.IsClique ↑s → 
Fintype.card α ≤ s.card → ∀ (C : G.Co…
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_fst_left`：∀ {α : Type u_1} [inst :
 DecidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   
G.IsFiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_snd_right`：∀ {α : Type u_1} [inst 
: DecidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},  
 G.IsFiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `trivial`：True
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `SimpleGraph.Coloring.valid`：∀ {V : Type u} {G : SimpleGraph V} {α : Type
 u_2} (C : G.Coloring α) {v w : V}, G.Adj v w → C v ≠ C w
· 使用定理 `SimpleGraph.IsPathGraph3Compl.adj`：∀ {α : Type u} {G : SimpleGraph α} {v
 w₁ w₂ : α}, G.IsPathGraph3Compl v w₁ w₂ → G.Adj w₁ w₂
· 使用定理 `SimpleGraph.IsFiveWheelLike.isPathGraph3Compl`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G
.IsFiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_right`：∀ {α : Type u_1} [inst : De
cidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G.I
sFiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `SimpleGraph.IsFiveWheelLike.notMem_right`：∀ {α : Type u_1} [inst : Decid
ableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G.IsFi
veWheelLike r k v w₁ w₂ s t → …
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_left`：∀ {α : Type u_1} [inst : Dec
idableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G.Is
FiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `SimpleGraph.IsFiveWheelLike.notMem_left`：∀ {α : Type u_1} [inst : Decida
bleEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G.IsFiv
eWheelLike r k v w₁ w₂ s t → …

--- 原说明 ---
Any graph containing an `IsFiveWheelLike r k` structure is not `(r + 1)`-colorab
le.
-/
lemma not_colorable_succ : ¬ G.Colorable (r + 1) := by
  intro ⟨C⟩
  have h := C.surjOn_of_card_le_isClique hw.isNClique_fst_left.1 (by simp [hw.isNClique_fst_left.2])
  have := C.surjOn_of_card_le_isClique hw.isNClique_snd_right.1 (by simp [hw.isNClique_snd_right.2])
  -- Since `C` is an `r + 1`-coloring and `insert w₁ s` is an `r + 1`-clique, it contains a vertex
  -- `x` which shares its color with `v`
  obtain ⟨x, hx, hcx⟩ := h (a := C v) trivial
  -- Similarly there is a vertex `y` in `insert w₂ t` which shares its color with `v`.
  obtain ⟨y, hy, hcy⟩ := this (a := C v) trivial
  rw [coe_insert] at *
  -- However since `insert v s` and `insert v t` are cliques, we must have `x = w₁` and `y = w₂`.
  cases hx with
  | inl hx =>
    cases hy with
    | inl hy =>
    -- But this is a contradiction since `w₁` and `w₂` are adjacent.
      subst_vars; exact C.valid hw.isPathGraph3Compl.adj (hcy ▸ hcx)
    | inr hy =>
      apply (C.valid _ hcy.symm).elim
      exact hw.isNClique_right.1 (by simp) (by simp [hy]) fun h ↦ hw.notMem_right (h ▸ hy)
  | inr hx =>
    apply (C.valid _ hcx.symm).elim
    exact hw.isNClique_left.1 (by simp) (by simp [hx]) fun h ↦ hw.notMem_left (h ▸ hx)

@[grind →]
/-
**SimpleGraph.IsFiveWheelLike.card_left** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.I
sFiveWheelLike`。
形式化陈述：card_left : s.card = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.IsNClique.card_eq`：∀ {α : Type u_1} {G : SimpleGraph α} {n :
 ℕ} {s : Finset α}, G.IsNClique n s → s.card = n
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_left`：∀ {α : Type u_1} [inst : Dec
idableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G.Is
FiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SimpleGraph.IsFiveWheelLike.notMem_left`：∀ {α : Type u_1} [inst : Decida
bleEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G.IsFiv
eWheelLike r k v w₁ w₂ s t → …
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_left : s.card = r := by
  simp [← Nat.succ_inj, ← hw.isNClique_left.2, hw.notMem_left]

@[grind →]
/-
**SimpleGraph.IsFiveWheelLike.card_right** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.
IsFiveWheelLike`。
形式化陈述：card_right : t.card = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.IsFiveWheelLike.card_left`：card_left : s.card = r
· 使用定理 `SimpleGraph.IsFiveWheelLike.symm`：∀ {α : Type u_1} {s : Finset α} {G : S
impleGraph α} {r k : ℕ} [inst : DecidableEq α] {v w₁ w₂ : α} {t : Finset α},   G
.IsFiveWheelLike r k v…
-/
lemma card_right : t.card = r := hw.symm.card_left
/-
**SimpleGraph.IsFiveWheelLike.card_inter_lt_of_cliqueFree** 是 Mathlib 中的一个引理，位于命
名空间 `SimpleGraph.IsFiveWheelLike`。
形式化陈述：card_inter_lt_of_cliqueFree (h : G.CliqueFree (r + 2)) : k < r
参数：h : G.CliqueFree (r + 2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.IsFiveWheelLike.card_left`：card_left : s.card = r
· 使用定理 `SimpleGraph.IsFiveWheelLike.card_inter`：∀ {α : Type u_1} [inst : Decidab
leEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G.IsFive
WheelLike r k v w₁ w₂ s t → …
· 使用定理 `Finset.inter_subset_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
· 使用引理 `SimpleGraph.IsFiveWheelLike.card_right`：card_right : t.card = r
· 使用定理 `SimpleGraph.IsNClique.not_cliqueFree`：∀ {α : Type u_1} {G : SimpleGraph 
α} {n : ℕ} {s : Finset α}, G.IsNClique n s → ¬G.CliqueFree n
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.FiveWheelLike.0.SimpleGraph.I
sNClique.insert_insert`：∀ {α : Type u_1} {a b : α} {s : Finset α} {G : SimpleGra
ph α} {r : ℕ} [inst : DecidableEq α],   G.IsNClique r (insert a s) →     G.IsNCl
ique…
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_fst_left`：∀ {α : Type u_1} [inst :
 DecidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   
G.IsFiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_snd_right`：∀ {α : Type u_1} [inst 
: DecidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},  
 G.IsFiveWheelLike r k v w₁ w₂ s t → …
· 使用引理 `SimpleGraph.IsFiveWheelLike.snd_notMem_left`：snd_notMem_left : w₂ ∉ s
· 使用定理 `SimpleGraph.IsPathGraph3Compl.adj`：∀ {α : Type u} {G : SimpleGraph α} {v
 w₁ w₂ : α}, G.IsPathGraph3Compl v w₁ w₂ → G.Adj w₁ w₂
· 使用定理 `SimpleGraph.IsFiveWheelLike.isPathGraph3Compl`：∀ {α : Type u_1} [inst : 
DecidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G
.IsFiveWheelLike r k v w₁ w₂ s t → …
-/
lemma card_inter_lt_of_cliqueFree (h : G.CliqueFree (r + 2)) : k < r := by
  contrapose! h
  -- If `r ≤ k` then `s = t` and so `s ∪ {w₁, w₂}` is an `r + 2`-clique, a contradiction.
  have hs := eq_of_subset_of_card_le inter_subset_left (hw.card_inter ▸ hw.card_left ▸ h)
  have := eq_of_subset_of_card_le inter_subset_right (hw.card_inter ▸ hw.card_right ▸ h)
  exact (hw.isNClique_fst_left.insert_insert (hs ▸ this.symm ▸ hw.isNClique_snd_right)
    hw.snd_notMem_left hw.isPathGraph3Compl.adj).not_cliqueFree

end IsFiveWheelLike

/--
Any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite contains a maximal
`IsFiveWheelLike` structure `Wᵣ,ₖ` for some `k < r`. (It is maximal in terms of `k`.)
-/
/-
**SimpleGraph.exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMul
tipartite** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartit
e (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipart
ite) : exists k v w₁ w₂ s t, G.IsFiveWheelLike r k v w₁ w₂ s t ∧ k < r ∧ forall 
j, k < j -> G.FiveWheelLikeFree r j
参数：h : Maximal (fun H => H.CliqueFree (r + 2)) G；hnc : ¬ G.IsCompleteMultipartit
e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteM
ultipartite`：exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipar
tite (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsComplet…
· 使用引理 `Nat.findGreatest_spec`：findGreatest_spec (hmb : m <= n) (hm : P m) : P (
Nat.findGreatest P n)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `SimpleGraph.IsFiveWheelLike.card_inter_lt_of_cliqueFree`：card_inter_lt_o
f_cliqueFree (h : G.CliqueFree (r + 2)) : k < r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `Nat.le_findGreatest`：le_findGreatest (hmb : m <= n) (hm : P m) : m <= Na
t.findGreatest P n

--- 原说明 ---
Any maximally `Kᵣ₊₂`-free graph that is not complete-multipartite contains a max
imal
`IsFiveWheelLike` structure `Wᵣ,ₖ` for some `k < r`. (It is maximal in terms of 
`k`.)
-/
lemma exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite
    (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCompleteMultipartite) :
    ∃ k v w₁ w₂ s t, G.IsFiveWheelLike r k v w₁ w₂ s t ∧ k < r ∧
      ∀ j, k < j → G.FiveWheelLikeFree r j := by
  obtain ⟨_, _, _, s, t, hw⟩ :=
    exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite h hnc
  let P : ℕ → Prop := fun k ↦ ∃ v w₁ w₂ s t, G.IsFiveWheelLike r k v w₁ w₂ s t
  have hk : P #(s ∩ t) := ⟨_, _, _, _, _, hw⟩
  classical
  obtain ⟨_, _, _, _, _, hw⟩ := Nat.findGreatest_spec (hw.card_inter_lt_of_cliqueFree h.1).le hk
  exact ⟨_, _, _, _, _, _, hw, hw.card_inter_lt_of_cliqueFree h.1,
         fun _ hj _ _ _ _ _ hv ↦ hj.not_ge <| Nat.le_findGreatest
           (hv.card_inter_lt_of_cliqueFree h.1).le ⟨_, _, _, _, _, hv⟩⟩
/-
**SimpleGraph.CliqueFree.fiveWheelLikeFree_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.CliqueFree`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} {r k : ℕ} [inst : DecidableEq α],   G
.CliqueFree (r + 2) → r ≤ k → G.FiveWheelLikeFree r k
参数：r + 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `SimpleGraph.IsFiveWheelLike.card_inter_lt_of_cliqueFree`：card_inter_lt_o
f_cliqueFree (h : G.CliqueFree (r + 2)) : k < r
-/
lemma CliqueFree.fiveWheelLikeFree_of_le (h : G.CliqueFree (r + 2)) (hk : r ≤ k) :
    G.FiveWheelLikeFree r k := fun hw ↦ (hw.card_inter_lt_of_cliqueFree h).not_ge hk

end withDecEq

/-- A maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is complete-multipartite. -/
/-
**SimpleGraph.colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree** 是 Mat
hlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree (h : Maximal (f
un H => H.CliqueFree (r + 1)) G) : G.Colorable r ↔ G.IsCompleteMultipartite
参数：h : Maximal (fun H => H.CliqueFree (r + 1)) G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.cliqueFree_one`：cliqueFree_one : G.CliqueFree 1 ↔ IsEmpty α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.colorable_zero_iff`：colorable_zero_iff : G.Colorable 0 ↔ IsE
mpty V
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `SimpleGraph.exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteM
ultipartite`：exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipar
tite (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsComplet…
· 使用引理 `SimpleGraph.IsFiveWheelLike.not_colorable_succ`：not_colorable_succ : ¬ G
.Colorable (r + 1)
· 使用定理 `SimpleGraph.IsCompleteMultipartite.colorable_of_cliqueFree`：∀ {α : Type 
u} {G : SimpleGraph α} {n : ℕ}, G.IsCompleteMultipartite → G.CliqueFree n → G.Co
lorable (n - 1)

--- 原说明 ---
A maximally `Kᵣ₊₁`-free graph is `r`-colorable iff it is complete-multipartite.
-/
theorem colorable_iff_isCompleteMultipartite_of_maximal_cliqueFree
    (h : Maximal (fun H => H.CliqueFree (r + 1)) G) : G.Colorable r ↔ G.IsCompleteMultipartite := by
  classical
  match r with
  | 0 => exact ⟨fun _ ↦ ⟨fun x ↦ cliqueFree_one.1 h.1 |>.elim' x⟩,
                fun _ ↦ G.colorable_zero_iff.2 <| cliqueFree_one.1 h.1⟩
  | r + 1 =>
    refine ⟨fun hc ↦ ?_, fun hc ↦ hc.colorable_of_cliqueFree h.1⟩
    contrapose hc
    obtain ⟨_, _, _, _, _, hw⟩ :=
      exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite h hc
    exact hw.not_colorable_succ

section AES
variable {i j n : ℕ} {d x v w₁ w₂ : α} {s t : Finset α}

section Counting

/--
Given lower bounds on non-adjacencies from `W` into `X`,`Xᶜ` we can bound the degree sum over `W`.
-/
/-
**SimpleGraph.sum_degree_le_of_le_not_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given lower bounds on non-adjacencies from `W` into `X`,`Xᶜ` we can bound the de
gree sum over `W`.
-/
private lemma sum_degree_le_of_le_not_adj [Fintype α] [DecidableEq α] [DecidableRel G.Adj]
    {W X : Finset α} (hx : ∀ x ∈ X, i ≤ #{z ∈ W | ¬ G.Adj x z})
    (hxc : ∀ y ∈ Xᶜ, j ≤ #{z ∈ W | ¬ G.Adj y z}) :
    ∑ w ∈ W, G.degree w ≤ #X * (#W - i) + #Xᶜ * (#W - j) := calc
  _ = ∑ v, #(G.neighborFinset v ∩ W) := by
    simp_rw [degree, card_eq_sum_ones]
    exact sum_comm' (by simp [and_comm, adj_comm])
  _ ≤ _ := by
    simp_rw [← union_compl X, sum_union disjoint_compl_right (s₁ := X), neighborFinset_eq_filter,
             filter_inter, univ_inter, card_eq_sum_ones X, card_eq_sum_ones Xᶜ, sum_mul, one_mul]
    gcongr <;> grind [card_filter_add_card_filter_not]

end Counting

namespace IsFiveWheelLike

variable [DecidableEq α] (hw : G.IsFiveWheelLike r k v w₁ w₂ s t) (hcf : G.CliqueFree (r + 2))

include hw hcf

/--
If `G` is `Kᵣ₊₂`-free and contains a `Wᵣ,ₖ` together with a vertex `x` adjacent to all of its common
clique vertices then there exist (not necessarily distinct) vertices `a, b, c, d`, one from each of
the four `r + 1`-cliques of `Wᵣ,ₖ`, none of which are adjacent to `x`.
-/
/-
**SimpleGraph.IsFiveWheelLike.exist_not_adj_of_adj_inter** 是 Mathlib 中的一个引理，位于命名
空间 `SimpleGraph.IsFiveWheelLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is `Kᵣ₊₂`-free and contains a `Wᵣ,ₖ` together with a vertex `x` adjacent 
to all of its common
clique vertices then there exist (not necessarily distinct) vertices `a, b, c, d
`, one from each of
the four `r + 1`-cliques of `Wᵣ,ₖ`, none of which are adjacent to `x`.
-/
private lemma exist_not_adj_of_adj_inter (hW : ∀ ⦃y⦄, y ∈ s ∩ t → G.Adj x y) :
    ∃ a b c d, a ∈ insert w₁ s ∧ ¬ G.Adj x a ∧ b ∈ insert w₂ t ∧ ¬ G.Adj x b ∧ c ∈ insert v s ∧
    ¬ G.Adj x c ∧ d ∈ insert v t ∧ ¬ G.Adj x d ∧ a ≠ b ∧ a ≠ d ∧ b ≠ c ∧ a ∉ t ∧ b ∉ s := by
  obtain ⟨a, ha, haj⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨b, hb, hbj⟩ := hw.isNClique_snd_right.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨c, hc, hcj⟩ := hw.isNClique_left.exists_not_adj_of_cliqueFree_succ hcf x
  obtain ⟨d, hd, hdj⟩ := hw.isNClique_right.exists_not_adj_of_cliqueFree_succ hcf x
  exact ⟨_, _, _, _, ha, haj, hb, hbj, hc, hcj, hd, hdj, by grind⟩

variable [DecidableRel G.Adj]

/--
If `G` is `Kᵣ₊₂`-free and contains a `Wᵣ,ₖ` together with a vertex `x` adjacent to all but at most
two vertices of `Wᵣ,ₖ`, including all of its common clique vertices, then `G` contains a `Wᵣ,ₖ₊₁`.
-/
/-
**SimpleGraph.IsFiveWheelLike.exists_isFiveWheelLike_succ_of_not_adj_le_two** 是 
Mathlib 中的一个引理，位于命名空间 `SimpleGraph.IsFiveWheelLike`。
形式化陈述：exists_isFiveWheelLike_succ_of_not_adj_le_two (hW : forall ⦃y⦄, y in s int
er t -> G.Adj x y) (h2 : #{z in {v} union ({w₁} union ({w₂} union (s union t))) 
| ¬ G.Adj x z} <= 2) : exists a b, G.IsFiveWheelLike r (k + 1) v w₁ w₂ (insert x
 (s.erase a)) (insert x (t.erase b))
参数：hW : forall ⦃y⦄, y in s inter t -> G.Adj x y；h2 : #{z in {v} union ({w₁} unio
n ({w₂} union (s union t))) | ¬ G.Adj x z} <= 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.FiveWheelLike.0.SimpleGraph.I
sFiveWheelLike.exist_not_adj_of_adj_inter`：∀ {α : Type u_1} {G : SimpleGraph α} 
{r k : ℕ} {x v w₁ w₂ : α} {s t : Finset α} [inst : DecidableEq α],   G.IsFiveWhe
elLike r k v w₁ w₂ s t …
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.two_lt_card_iff`：two_lt_card_iff : 2 < #s ↔ exists a b c, a in s 
∧ b in s ∧ c in s ∧ a != b ∧ a != c ∧ b != c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.IsNClique.isClique`：∀ {α : Type u_1} {G : SimpleGraph α} {n 
: ℕ} {s : Finset α}, G.IsNClique n s → G.IsClique ↑s
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_left`：∀ {α : Type u_1} [inst : Dec
idableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   G.Is
FiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_fst_left`：∀ {α : Type u_1} [inst :
 DecidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   
G.IsFiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_snd_right`：∀ {α : Type u_1} [inst 
: DecidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},  
 G.IsFiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `Finset.two_lt_card`：two_lt_card : 2 < #s ↔ exists a in s, exists b in s,
 exists c in s, a != b ∧ a != c ∧ b != c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `SimpleGraph.adj_comm`：adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.FiveWheelLike.0.SimpleGraph.I
sNClique.insert_insert_erase`：∀ {α : Type u_1} {a b c : α} {s : Finset α} {G : S
impleGraph α} {r : ℕ} [inst : DecidableEq α],   G.IsNClique r (insert a s) →    
 c ∈ s → a…
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
If `G` is `Kᵣ₊₂`-free and contains a `Wᵣ,ₖ` together with a vertex `x` adjacent 
to all but at most
two vertices of `Wᵣ,ₖ`, including all of its common clique vertices, then `G` co
ntains a `Wᵣ,ₖ₊₁`.
-/
lemma exists_isFiveWheelLike_succ_of_not_adj_le_two (hW : ∀ ⦃y⦄, y ∈ s ∩ t → G.Adj x y)
    (h2 : #{z ∈ {v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t))) | ¬ G.Adj x z} ≤ 2) :
    ∃ a b, G.IsFiveWheelLike r (k + 1) v w₁ w₂ (insert x (s.erase a)) (insert x (t.erase b)) := by
  obtain ⟨a, b, c, d, ha, haj, hb, hbj, hc, hcj, hd, hdj, hab, had, hbc, hat, hbs⟩ :=
    hw.exist_not_adj_of_adj_inter hcf hW
  -- Let `W` denote the vertices of the copy of `Wᵣ,ₖ` in `G`
  let W := {v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t)))
  have ⟨hca, hdb⟩ : c = a ∧ d = b := by
    by_contra! hf
    apply h2.not_gt <| two_lt_card_iff.2 _
    by_cases h : a = c
    · exact ⟨a, b, d, by grind⟩
    · exact ⟨a, b, c, by grind⟩
  simp_rw [hca, hdb, mem_insert] at *
  have ⟨has, hbt, hav, hbv, haw, hbw⟩ : a ∈ s ∧ b ∈ t ∧ a ≠ v ∧ b ≠ v ∧ a ≠ w₂ ∧ b ≠ w₁ := by grind
  have ⟨hxv, hxw₁, hxw₂⟩ : v ≠ x ∧ w₁ ≠ x ∧ w₂ ≠ x := by
    refine ⟨?_, ?_, ?_⟩
    · by_cases hax : x = a <;> rintro rfl
      · grind
      · exact haj <| hw.isNClique_left.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hax : x = a <;> rintro rfl
      · grind
      · exact haj <| hw.isNClique_fst_left.1 (mem_insert_self ..) (mem_insert_of_mem has) hax
    · by_cases hbx : x = b <;> rintro rfl
      · grind
      · exact hbj <| hw.isNClique_snd_right.1 (mem_insert_self ..) (mem_insert_of_mem hbt) hbx
  -- Since `x` is not adjacent to `a` and `b` but is adjacent to all but at most two vertices
  -- from `W` we have `∀ w ∈ W, w ≠ a → w ≠ b → G.Adj w x`
  have wa : ∀ ⦃w⦄, w ∈ W → w ≠ a → w ≠ b → G.Adj w x := by
    intro _ hz haz hbz
    by_contra! hf
    apply h2.not_gt
    exact two_lt_card.2 ⟨_, by simp [has, hcj], _, by simp [hbt, hdj], _,
                         mem_filter.2 ⟨hz, by rwa [adj_comm] at hf⟩, hab, haz.symm, hbz.symm⟩
  have ⟨h1s, h2t⟩ : insert w₁ s ⊆ W ∧ insert w₂ t ⊆ W := by grind
  -- We now check that we can build a `Wᵣ,ₖ₊₁` by inserting `x` and erasing `a` and `b`
  refine ⟨a, b, ⟨by grind, by grind, by grind, by grind, by grind, ?h5, ?h6, ?h7, ?h8, ?h9⟩⟩
  -- Check that the new cliques are indeed cliques
  case h5 => exact hw.isNClique_left.insert_insert_erase has hw.notMem_left fun _ hz hZ ↦
               wa ((insert_subset_insert _ fun _ hx ↦ (by simp [hx])) hz) hZ
                 fun h ↦ hbv <| (mem_insert.1 (h ▸ hz)).resolve_right hbs
  case h6 => exact hw.isNClique_fst_left.insert_insert_erase has hw.fst_notMem fun _ hz hZ ↦
               wa (h1s hz) hZ fun h ↦ hbw <| (mem_insert.1 (h ▸ hz)).resolve_right hbs
  case h7 => exact hw.isNClique_right.insert_insert_erase hbt hw.notMem_right fun _ hz hZ ↦
               wa ((insert_subset_insert _ fun _ hx ↦ (by simp [hx])) hz)
                 (fun h ↦ hav <| (mem_insert.1 (h ▸ hz)).resolve_right hat) hZ
  case h8 => exact hw.isNClique_snd_right.insert_insert_erase hbt hw.snd_notMem fun _ hz hZ ↦
               wa (h2t hz) (fun h ↦ haw <| (mem_insert.1 (h ▸ hz)).resolve_right hat) hZ
  case h9 =>
    -- Finally check that this new `IsFiveWheelLike` structure has `k + 1` common clique
    -- vertices i.e. `#((insert x (s.erase a)) ∩ (insert x (s.erase b))) = k + 1`.
    rw [← insert_inter_distrib, erase_inter, inter_erase, erase_eq_of_notMem <|
        notMem_mono inter_subset_left hbs, erase_eq_of_notMem <| notMem_mono inter_subset_right hat,
        card_insert_of_notMem (fun h ↦ G.irrefl (hW h)), hw.card_inter]

/--
If `G` is a `Kᵣ₊₂`-free graph with `n` vertices containing a `Wᵣ,ₖ` but no `Wᵣ,ₖ₊₁`
then `G.minDegree ≤ (2 * r + k) * n / (2 * r + k + 3)`
-/
/-
**SimpleGraph.IsFiveWheelLike.minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ*
* 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.IsFiveWheelLike`。
形式化陈述：minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ [Fintype α] (hm : G.Five
WheelLikeFree r (k + 1)) : G.minDegree <= (2 * r + k) * ‖α‖ / (2 * r + k + 3)
参数：hm : G.FiveWheelLikeFree r (k + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `SimpleGraph.IsFiveWheelLike.exists_isFiveWheelLike_succ_of_not_adj_le_tw
o`：exists_isFiveWheelLike_succ_of_not_adj_le_two (hW : forall ⦃y⦄, y in s inter 
t -> G.Adj x y) (h2 : #{z in {v} union ({w₁} union ({w₂} union …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Nat.le_of_succ_le_succ`：∀ {n m : ℕ}, n.succ ≤ m.succ → n ≤ m
· 使用定理 `SimpleGraph.IsNClique.exists_not_adj_of_cliqueFree_succ`：∀ {α : Type u_1
} {G : SimpleGraph α} {n : ℕ} {s : Finset α},   G.IsNClique n s → G.CliqueFree (
n + 1) → ∀ (x : α), ∃ y ∈ s, ¬G.Adj x y
· 使用定理 `SimpleGraph.IsFiveWheelLike.isNClique_fst_left`：∀ {α : Type u_1} [inst :
 DecidableEq α] {G : SimpleGraph α} {r k : ℕ} {v w₁ w₂ : α} {s t : Finset α},   
G.IsFiveWheelLike r k v w₁ w₂ s t → …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.FiveWheelLike.0.SimpleGraph.s
um_degree_le_of_le_not_adj`：∀ {α : Type u_1} {G : SimpleGraph α} {i j : ℕ} [inst
 : Fintype α] [inst_1 : DecidableEq α] [inst_2 : DecidableRel G.Adj]   {W X : Fi
nset α},…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Finset.compl_filter`：compl_filter (p : α -> Prop) [DecidablePred p] [for
all x, Decidable ¬p x] : (univ.filter p)ᶜ = univ.filter fun x => ¬p x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.le_div_iff_mul_le`：∀ {k x y : ℕ}, 0 < k → (x ≤ y / k ↔ x * k ≤ y)
· 使用定理 `Nat.add_pos_right`：∀ {b : ℕ} (a : ℕ), 0 < b → 0 < a + b
· 使用定理 `zero_lt_three`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Pa
rtialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 3
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
（共 76 条，此处仅展示前 30 条）

--- 原说明 ---
If `G` is a `Kᵣ₊₂`-free graph with `n` vertices containing a `Wᵣ,ₖ` but no `Wᵣ,ₖ
₊₁`
then `G.minDegree ≤ (2 * r + k) * n / (2 * r + k + 3)`
-/
lemma minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ [Fintype α]
    (hm : G.FiveWheelLikeFree r (k + 1)) : G.minDegree ≤ (2 * r + k) * ‖α‖ / (2 * r + k + 3) := by
  let X : Finset α := {x | ∀ ⦃y⦄, y ∈ s ∩ t → G.Adj x y}
  let W := {v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t)))
  -- Any vertex in `X` has at least 3 non-neighbors in `W` (otherwise we could build a bigger wheel)
  have dXle : ∀ x ∈ X, 3 ≤ #{z ∈ W | ¬ G.Adj x z} := by
    intro _ hx
    by_contra! h
    obtain ⟨_, _, hW⟩ := hw.exists_isFiveWheelLike_succ_of_not_adj_le_two hcf
      (by simpa [X] using hx) <| Nat.le_of_succ_le_succ h
    exact hm hW
  -- Since `G` is `Kᵣ₊₂`-free and contains a `Wᵣ,ₖ`, every vertex is not adjacent to at least one
  -- wheel vertex.
  have one_le (x : α) : 1 ≤ #{z ∈ {v} ∪ ({w₁} ∪ ({w₂} ∪ (s ∪ t))) | ¬ G.Adj x z} :=
    let ⟨_, hz⟩ := hw.isNClique_fst_left.exists_not_adj_of_cliqueFree_succ hcf x
    card_pos.2 ⟨_, mem_filter.2 ⟨by grind, hz.2⟩⟩
  -- Since every vertex has at least one non-neighbor in `W` we now have the following upper bound
  -- `∑ w ∈ W, H.degree w ≤ #X * (#W - 3) + #Xᶜ * (#W - 1)`
  have bdW := sum_degree_le_of_le_not_adj dXle (fun y _ ↦ one_le y)
  -- By the definition of `X`, any `x ∈ Xᶜ` has at least one non-neighbour in `X`.
  have xcle : ∀ x ∈ Xᶜ, 1 ≤ #{z ∈ s ∩ t | ¬ G.Adj x z} := by
    intro x hx
    apply card_pos.2
    obtain ⟨_, hy⟩ : ∃ y ∈ s ∩ t, ¬ G.Adj x y := by
      contrapose! hx
      simpa [X] using hx
    exact ⟨_, mem_filter.2 hy⟩
  -- So we also have an upper bound on the degree sum over `s ∩ t`
  -- `∑ w ∈ s ∩ t, H.degree w ≤ #Xᶜ * (#(s ∩ t) - 1) + #X * #(s ∩ t)`
  have bdX := sum_degree_le_of_le_not_adj xcle (fun _ _ ↦ Nat.zero_le _)
  rw [compl_compl, tsub_zero, add_comm] at bdX
  rw [Nat.le_div_iff_mul_le <| Nat.add_pos_right _ zero_lt_three]
  have Wc : #W + k = 2 * r + 3 := by grind
  -- The sum of the degree sum over `W` and twice the degree sum over `s ∩ t`
  -- is at least `G.minDegree * (#W + 2 * #(s ∩ t))` which implies the result
  calc
    _ ≤ ∑ w ∈ W, G.degree w + 2 * ∑ w ∈ s ∩ t, G.degree w := by
      simp_rw [add_assoc, add_comm k, ← add_assoc, ← Wc, add_assoc, ← two_mul, mul_add,
               ← hw.card_inter, card_eq_sum_ones, ← mul_assoc, mul_sum, mul_one, mul_comm 2]
      gcongr with i <;> exact minDegree_le_degree ..
    _ ≤ (#X * (#W - 3) + #Xᶜ * (#W - 1)) + 2 * (#X * #(s ∩ t) + #Xᶜ * (#(s ∩ t) - 1)) := by gcongr
    _ = #X * (#W - 3 + 2 * k) + #Xᶜ * ((#W - 1) + 2 * (k - 1)) := by grind
    _ ≤ _ := by
        by_cases hk : k = 0 -- so `s ∩ t = ∅` and hence `Xᶜ = ∅`
        · have Xu : X = univ := by
            rw [← hw.card_inter, card_eq_zero] at hk
            exact eq_univ_of_forall fun _ ↦ by simp [X, hk]
          subst k
          rw [add_zero] at Wc
          simp [Xu, Wc, mul_comm]
        have w3 : 3 ≤ #W := two_lt_card.2 ⟨_, mem_insert_self .., _, by simp [W], _, by simp [W],
          hw.isPathGraph3Compl.ne_fst, hw.isPathGraph3Compl.ne_snd, hw.isPathGraph3Compl.fst_ne_snd⟩
        have hap : #W - 1 + 2 * (k - 1) = #W - 3 + 2 * k := by lia
        rw [hap, ← add_mul, card_add_card_compl, mul_comm, two_mul, ← add_assoc]
        gcongr
        lia

end IsFiveWheelLike

/-- **Andrásfai-Erdős-Sós** theorem

If `G` is a `Kᵣ₊₁`-free graph with `n` vertices and `(3 * r - 4) * n / (3 * r - 1) < G.minDegree`
then `G` is `r + 1`-colorable, e.g. if `G` is `K₃`-free and `2 * n / 5 < G.minDegree` then `G`
is `2`-colorable.
-/
/-
**SimpleGraph.colorable_of_cliqueFree_lt_minDegree** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：colorable_of_cliqueFree_lt_minDegree [Fintype α] [DecidableRel G.Adj] (hf 
: G.CliqueFree (r + 1)) (hd : (3 * r - 4) * ‖α‖ / (3 * r - 1) < G.minDegree) : G
.Colorable r
参数：hf : G.CliqueFree (r + 1)；hd : (3 * r - 4) * ‖α‖ / (3 * r - 1) < G.minDegree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `SimpleGraph.minDegree.congr_simp`：∀ {V : Type u_1} (G G_1 : SimpleGraph 
V),   G = G_1 →     ∀ [inst : Fintype V] {inst_1 : DecidableRel G.Adj} [inst_2 :
 DecidableRel G_1.Adj]…
· 使用引理 `SimpleGraph.minDegree_bot_eq_zero`：minDegree_bot_eq_zero : (⊥ : SimpleGr
aph V).minDegree = 0
· 使用引理 `Finite.exists_le_maximal`：Finite.exists_le_maximal (hs : s.Finite) (ha :
 a in s) : exists b, a <= b ∧ Maximal (· in s) b
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SimpleGraph.Colorable.mono_left`：∀ {V : Type u} {G G' : SimpleGraph V}, 
G ≤ G' → ∀ {n : ℕ}, G'.Colorable n → G.Colorable n
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `SimpleGraph.IsCompleteMultipartite.colorable_of_cliqueFree`：∀ {α : Type 
u} {G : SimpleGraph α} {n : ℕ}, G.IsCompleteMultipartite → G.CliqueFree n → G.Co
lorable (n - 1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `SimpleGraph.exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompl
eteMultipartite`：exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isComplete
Multipartite (h : Maximal (fun H => H.CliqueFree (r + 2)) G) (hnc : ¬ G.IsCom…
· 使用引理 `SimpleGraph.IsFiveWheelLike.minDegree_le_of_cliqueFree_fiveWheelLikeFree
_succ`：minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ [Fintype α] (hm : G.Fiv
eWheelLikeFree r (k + 1)) : G.minDegree <= (2 * r + k) * ‖α‖ / (2 *…
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.le_div_iff_mul_le`：∀ {k x y : ℕ}, 0 < k → (x ≤ y / k ↔ x * k ≤ y)
（共 107 条，此处仅展示前 30 条）

--- 原说明 ---
**Andrásfai-Erdős-Sós** theorem

If `G` is a `Kᵣ₊₁`-free graph with `n` vertices and `(3 * r - 4) * n / (3 * r - 
1) < G.minDegree`
then `G` is `r + 1`-colorable, e.g. if `G` is `K₃`-free and `2 * n / 5 < G.minDe
gree` then `G`
is `2`-colorable.
-/
theorem colorable_of_cliqueFree_lt_minDegree [Fintype α] [DecidableRel G.Adj]
    (hf : G.CliqueFree (r + 1)) (hd : (3 * r - 4) * ‖α‖ / (3 * r - 1) < G.minDegree) :
    G.Colorable r := by
  match r with
  | 0 | 1 => aesop
  | r + 2 =>
    classical
    -- There is an edge maximal `Kᵣ₊₃`-free supergraph `H` of `G`
    obtain ⟨H, hle, hmcf⟩ := @Finite.exists_le_maximal _ _ _ (fun H ↦ H.CliqueFree (r + 3)) G hf
    -- If `H` is `r + 2`-colorable then so is `G`
    apply Colorable.mono_left hle
    -- Suppose, for a contradiction, that `H` is not `r + 2`-colorable
    by_contra! hnotcol
    -- so `H` is not complete-multipartite
    have hn : ¬ H.IsCompleteMultipartite := fun hc ↦ hnotcol <| hc.colorable_of_cliqueFree hmcf.1
    -- Hence `H` contains `Wᵣ₊₁,ₖ` but not `Wᵣ₊₁,ₖ₊₁`, for some `k < r + 1`
    obtain ⟨k, _, _, _, _, _, hw, hlt, hm⟩ :=
      exists_max_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite hmcf hn
    -- But the minimum degree of `G`, and hence of `H`, is too large for it to be `Wᵣ₊₁,ₖ₊₁`-free,
    -- a contradiction.
    have hD := hw.minDegree_le_of_cliqueFree_fiveWheelLikeFree_succ hmcf.1 <| hm _ <| lt_add_one _
    have : (2 * (r + 1) + k) * ‖α‖ / (2 * (r + 1) + k + 3) ≤ (3 * r + 2) * ‖α‖ / (3 * r + 5) := by
      apply (Nat.le_div_iff_mul_le <| Nat.succ_pos _).2
              <| (mul_le_mul_iff_right₀ (_ + 2).succ_pos).1 _
      rw [← mul_assoc, mul_comm (2 * r + 2 + k + 3), mul_comm _ (_ * ‖α‖)]
      apply (Nat.mul_le_mul_right _ (Nat.div_mul_le_self ..)).trans
      nlinarith
    exact (hd.trans_le <| minDegree_le_minDegree hle).not_ge <| hD.trans <| this

end AES
end SimpleGraph

