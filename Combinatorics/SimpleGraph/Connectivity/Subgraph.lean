/-
Copyright (c) 2023 Kyle Miller, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
public import Mathlib.Data.Set.Card

/-!
# Connectivity of subgraphs and induced graphs

## Main definitions

* `SimpleGraph.Subgraph.Preconnected` and `SimpleGraph.Subgraph.Connected` give subgraphs
  connectivity predicates via `SimpleGraph.Subgraph.coe`.

-/

@[expose] public section

namespace SimpleGraph

universe u v
variable {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'}

namespace Subgraph

/-- A subgraph is preconnected if it is preconnected when coerced to be a simple graph.

Note: This is a structure to make it so one can be precise about how dot notation resolves. -/
/-
**SimpleGraph.Subgraph.Preconnected** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph.Sub
graph`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → G.Subgraph → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgraph is preconnected if it is preconnected when coerced to be a simple gra
ph.

Note: This is a structure to make it so one can be precise about how dot notatio
n resolves.
-/
protected structure Preconnected (H : G.Subgraph) : Prop where
  protected coe : H.coe.Preconnected
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {H : G.Subgraph} : Coe H.Preconnected H.coe.Preconnected := ⟨Preconnected.coe⟩
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {H : G.Subgraph} : CoeFun H.Preconnected (fun _ => ∀ u v : H.verts, H.coe.Reachable u v) :=
  ⟨fun h => h.coe⟩
/-
**SimpleGraph.Subgraph.preconnected_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.S
ubgraph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}, H.Preconnected ↔ H.co
e.Preconnected
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma preconnected_iff {H : G.Subgraph} :
    H.Preconnected ↔ H.coe.Preconnected := ⟨fun ⟨h⟩ => h, .mk⟩

/-- A subgraph is connected if it is connected when coerced to be a simple graph.

Note: This is a structure to make it so one can be precise about how dot notation resolves. -/
/-
**SimpleGraph.Subgraph.Connected** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph.Subgra
ph`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → G.Subgraph → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgraph is connected if it is connected when coerced to be a simple graph.

Note: This is a structure to make it so one can be precise about how dot notatio
n resolves.
-/
protected structure Connected (H : G.Subgraph) : Prop where
  protected coe : H.coe.Connected
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {H : G.Subgraph} : Coe H.Connected H.coe.Connected := ⟨Connected.coe⟩
/-
**SimpleGraph.Subgraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {H : G.Subgraph} : CoeFun H.Connected (fun _ => ∀ u v : H.verts, H.coe.Reachable u v) :=
  ⟨fun h => h.coe⟩
/-
**SimpleGraph.Subgraph.connected_iff'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Sub
graph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}, H.Connected ↔ H.coe.C
onnected
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma connected_iff' {H : G.Subgraph} :
    H.Connected ↔ H.coe.Connected := ⟨fun ⟨h⟩ => h, .mk⟩
/-
**SimpleGraph.Subgraph.connected_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subg
raph`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}, H.Connected ↔ H.Preco
nnected ∧ H.verts.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.connected_iff'`：∀ {V : Type u} {G : SimpleGraph V} 
{H : G.Subgraph}, H.Connected ↔ H.coe.Connected
· 使用定理 `SimpleGraph.connected_iff`：∀ {V : Type u} (G : SimpleGraph V), G.Connect
ed ↔ G.Preconnected ∧ Nonempty V
· 使用定理 `SimpleGraph.Subgraph.preconnected_iff`：∀ {V : Type u} {G : SimpleGraph V
} {H : G.Subgraph}, H.Preconnected ↔ H.coe.Preconnected
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma connected_iff {H : G.Subgraph} :
    H.Connected ↔ H.Preconnected ∧ H.verts.Nonempty := by
  rw [H.connected_iff', connected_iff, H.preconnected_iff, Set.nonempty_coe_sort]
/-
**SimpleGraph.Subgraph.Connected.preconnected** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Subgraph.Connected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}, H.Connected → H.Preco
nnected
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.connected_iff`：∀ {V : Type u} {G : SimpleGraph V} {
H : G.Subgraph}, H.Connected ↔ H.Preconnected ∧ H.verts.Nonempty
-/
protected lemma Connected.preconnected {H : G.Subgraph} (h : H.Connected) : H.Preconnected := by
  rw [H.connected_iff] at h; exact h.1
/-
**SimpleGraph.Subgraph.Connected.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Subgraph.Connected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}, H.Connected → H.verts
.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.connected_iff`：∀ {V : Type u} {G : SimpleGraph V} {
H : G.Subgraph}, H.Connected ↔ H.Preconnected ∧ H.verts.Nonempty
-/
protected lemma Connected.nonempty {H : G.Subgraph} (h : H.Connected) : H.verts.Nonempty := by
  rw [H.connected_iff] at h; exact h.2
/-
**SimpleGraph.Subgraph.singletonSubgraph_connected** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Subgraph`。
形式化陈述：singletonSubgraph_connected {v : V} : (G.singletonSubgraph v).Connected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Preconnected.of_subsingleton`：∀ {V : Type u} {G : SimpleGrap
h V} [Subsingleton V], G.Preconnected
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem singletonSubgraph_connected {v : V} : (G.singletonSubgraph v).Connected :=
  ⟨⟨Preconnected.of_subsingleton⟩⟩

@[simp]
/-
**SimpleGraph.Subgraph.subgraphOfAdj_connected** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Subgraph`。
形式化陈述：subgraphOfAdj_connected {v w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw
).Connected
参数：hvw : G.Adj v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.subgraphOfAdj_verts`：∀ {V : Type u} (G : SimpleGraph V) {v w
 : V} (hvw : G.Adj v w), (G.subgraphOfAdj hvw).verts = {v, w}
· 使用定理 `SimpleGraph.Reachable.refl`：∀ {V : Type u} {G : SimpleGraph V} (u : V), 
G.Reachable u u
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.Subgraph.coe_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' : G
.Subgraph) (v w : ↑G'.verts), G'.coe.Adj v w = G'.Adj ↑v ↑w
· 使用定理 `SimpleGraph.subgraphOfAdj_adj`：∀ {V : Type u} (G : SimpleGraph V) {v w :
 V} (hvw : G.Adj v w) (a b : V),   (G.subgraphOfAdj hvw).Adj a b = (s(v, w) = s(
a, b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem subgraphOfAdj_connected {v w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).Connected := by
  refine ⟨⟨?_⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  obtain rfl | rfl := ha <;> obtain rfl | rfl := hb <;>
    first | rfl | (apply Adj.reachable; simp)
/-
**SimpleGraph.Subgraph.top_induce_pair_connected_of_adj** 是 Mathlib 中的一个引理，位于命名空
间 `SimpleGraph.Subgraph`。
形式化陈述：top_induce_pair_connected_of_adj {u v : V} (huv : G.Adj u v) : ((⊤ : G.Sub
graph).induce {u, v}).Connected
参数：huv : G.Adj u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Subgraph.subgraphOfAdj_eq_induce`：subgraphOfAdj_eq_induce {v
 w : V} (hvw : G.Adj v w) : G.subgraphOfAdj hvw = (⊤ : G.Subgraph).induce {v, w}
· 使用定理 `SimpleGraph.Subgraph.subgraphOfAdj_connected`：subgraphOfAdj_connected {v
 w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).Connected
-/
lemma top_induce_pair_connected_of_adj {u v : V} (huv : G.Adj u v) :
    ((⊤ : G.Subgraph).induce {u, v}).Connected := by
  rw [← subgraphOfAdj_eq_induce huv]
  exact subgraphOfAdj_connected huv

@[gcongr, mono]
/-
**SimpleGraph.Subgraph.Connected.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Sub
graph.Connected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H H' : G.Subgraph}, H ≤ H' → H.verts =
 H'.verts → H.Connected → H'.Connected
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Subgraph.copy_eq`：copy_eq (G' : Subgraph G) (V'' : Set V) (h
V : V'' = G'.verts) (adj' : V -> V -> Prop) (hadj : adj' = G'.Adj) : G'.copy V''
 hV adj' hadj = G'
· 使用定理 `SimpleGraph.Connected.mono`：∀ {V : Type u} {G G' : SimpleGraph V}, G ≤ G
' → G.Connected → G'.Connected
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.Subgraph.Connected.coe`：∀ {V : Type u} {G : SimpleGraph V} {
H : G.Subgraph}, H.Connected → H.coe.Connected
-/
protected lemma Connected.mono {H H' : G.Subgraph} (hle : H ≤ H') (hv : H.verts = H'.verts)
    (h : H.Connected) : H'.Connected := by
  rw [← Subgraph.copy_eq H' H.verts hv H'.Adj rfl]
  refine ⟨h.coe.mono ?_⟩
  rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
  exact hle.2 hvw
/-
**SimpleGraph.Subgraph.Connected.mono'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Su
bgraph.Connected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H H' : G.Subgraph},   (∀ (v w : V), H.
Adj v w → H'.Adj v w) → H.verts = H'.verts → H.Connected → H'.Connected
参数：∀ (v w : V), H.Adj v w → H'.Adj v w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.Connected.mono`：∀ {V : Type u} {G : SimpleGraph V} 
{H H' : G.Subgraph}, H ≤ H' → H.verts = H'.verts → H.Connected → H'.Connected
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
protected lemma Connected.mono' {H H' : G.Subgraph}
    (hle : ∀ v w, H.Adj v w → H'.Adj v w) (hv : H.verts = H'.verts)
    (h : H.Connected) : H'.Connected := by
  exact h.mono ⟨hv.le, hle⟩ hv
/-
**SimpleGraph.Subgraph.connected_sup** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Subg
raph`。
形式化陈述：connected_sup {H K : G.Subgraph} (hH : H.Preconnected) (hK : K.Preconnecte
d) (hn : (H ⊓ K).verts.Nonempty) : (H ⊔ K).Connected
参数：hH : H.Preconnected；hK : K.Preconnected；hn : (H ⊓ K).verts.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.connected_iff'`：∀ {V : Type u} {G : SimpleGraph V} 
{H : G.Subgraph}, H.Connected ↔ H.coe.Connected
· 使用引理 `SimpleGraph.connected_iff_exists_forall_reachable`：connected_iff_exists_
forall_reachable : G.Connected ↔ exists v, forall w, G.Reachable v w
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `SimpleGraph.Subgraph.Preconnected.coe`：∀ {V : Type u} {G : SimpleGraph V
} {H : G.Subgraph}, H.Preconnected → H.coe.Preconnected
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma connected_sup {H K : G.Subgraph}
    (hH : H.Preconnected) (hK : K.Preconnected) (hn : (H ⊓ K).verts.Nonempty) :
    (H ⊔ K).Connected := by
  rw [Subgraph.connected_iff', connected_iff_exists_forall_reachable]
  obtain ⟨u, hu, hu'⟩ := hn
  exists ⟨u, Or.inl hu⟩
  rintro ⟨v, (hv | hv)⟩
  · exact Reachable.map (Subgraph.inclusion (le_sup_left : H ≤ H ⊔ K)) (hH ⟨u, hu⟩ ⟨v, hv⟩)
  · exact Reachable.map (Subgraph.inclusion (le_sup_right : K ≤ H ⊔ K)) (hK ⟨u, hu'⟩ ⟨v, hv⟩)
/-
**SimpleGraph.Subgraph.Preconnected.degree_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Subgraph.Preconnected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph},   H.Preconnected → ∀ 
(v : ↑H.verts) [inst : Fintype ↑(H.neighborSet ↑v)], H.degree ↑v = 0 ↔ H.verts.S
ubsingleton
参数：v : ↑H.verts；H.neighborSet ↑v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_nontrivial_iff`：not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingle
ton
· 使用定理 `Set.Nontrivial.coe_sort`：∀ {α : Type u} {s : Set α}, s.Nontrivial → Nont
rivial ↑s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.coe_degree`：coe_degree (G' : Subgraph G) (v : G'.ve
rts) [Fintype (G'.coe.neighborSet v)] [Fintype (G'.neighborSet v)] : G'.coe.degr
ee v = G'.degree v
· 使用定理 `SimpleGraph.Preconnected.degree_pos_of_nontrivial`：∀ {V : Type u} [Nontr
ivial V] {G : SimpleGraph V},   G.Preconnected → ∀ (v : V) [inst : Fintype ↑(G.n
eighborSet v)], 0 < G.degree v
· 使用定理 `SimpleGraph.Subgraph.Preconnected.coe`：∀ {V : Type u} {G : SimpleGraph V
} {H : G.Subgraph}, H.Preconnected → H.coe.Preconnected
· 使用定理 `SimpleGraph.Subgraph.degree_eq_zero_of_subsingleton`：degree_eq_zero_of_s
ubsingleton (G' : Subgraph G) (v : V) [Fintype (G'.neighborSet v)] (hG : G'.vert
s.Subsingleton) : G'.degree v = 0
-/
lemma Preconnected.degree_zero_iff {H : G.Subgraph} (h : H.Preconnected) (v : H.verts)
    [Fintype (H.neighborSet v)] : H.degree v = 0 ↔ H.verts.Subsingleton := by
  refine ⟨fun hv ↦ Set.not_nontrivial_iff.mp fun hn ↦ ?_, (degree_eq_zero_of_subsingleton H _ ·)⟩
  have := hn.coe_sort
  simpa [hv] using h.coe.degree_pos_of_nontrivial v
/-
**SimpleGraph.Subgraph.Preconnected.exists_adj_of_nontrivial** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph.Subgraph.Preconnected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph} [Nontrivial ↑H.verts],
   H.Preconnected → ∀ (v : ↑H.verts), ∃ u, H.Adj (↑v) u
参数：v : ↑H.verts；↑v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Preconnected.exists_adj_of_nontrivial`：∀ {V : Type u} [Nontr
ivial V] {G : SimpleGraph V}, G.Preconnected → ∀ (v : V), ∃ u, G.Adj v u
· 使用定理 `SimpleGraph.Subgraph.Preconnected.coe`：∀ {V : Type u} {G : SimpleGraph V
} {H : G.Subgraph}, H.Preconnected → H.coe.Preconnected
-/
lemma Preconnected.exists_adj_of_nontrivial {H : G.Subgraph} [Nontrivial H.verts]
    (h : H.Preconnected) (v : H.verts) : ∃ u, H.Adj v u := by
  have := h.coe.exists_adj_of_nontrivial v
  tauto

/--
This lemma establishes a condition under which a subgraph is the same as a connected component.
Note the asymmetry in the hypothesis `h`: `v` is in `H.verts`, but `w` is not required to be.
-/
/-
**SimpleGraph.Subgraph.Connected.exists_verts_eq_connectedComponentSupp** 是 Math
lib 中的一个定理，位于命名空间 `SimpleGraph.Subgraph.Connected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph},   H.Connected → (∀ v 
∈ H.verts, ∀ (w : V), G.Adj v w → H.Adj v w) → ∃ c, H.verts = c.supp
参数：∀ v ∈ H.verts, ∀ (w : V), G.Adj v w → H.Adj v w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.ConnectedComponent.exists`：∀ {V : Type u} {G : SimpleGraph V
} {p : G.ConnectedComponent → Prop}, (∃ c, p c) ↔ ∃ v, p (G.connectedComponentMk
 v)
· 使用定理 `SimpleGraph.Subgraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph
 V} {H : G.Subgraph}, H.Connected → H.verts.Nonempty
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Subgraph.hom_apply`：∀ {V : Type u} {G : SimpleGraph V} (x : 
G.Subgraph) (v : ↑x.verts), x.hom v = ↑v
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用定理 `SimpleGraph.Reachable.mem_subgraphVerts`：∀ {V : Type u} {G : SimpleGraph
 V} {u v : V} {H : G.Subgraph},   G.Reachable u v → (∀ v ∈ H.verts, ∀ (w : V), G
.Adj v w → H.Adj v w) → u ∈ H…
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u

--- 原说明 ---
This lemma establishes a condition under which a subgraph is the same as a conne
cted component.
Note the asymmetry in the hypothesis `h`: `v` is in `H.verts`, but `w` is not re
quired to be.
-/
lemma Connected.exists_verts_eq_connectedComponentSupp {H : Subgraph G}
    (hc : H.Connected) (h : ∀ v ∈ H.verts, ∀ w, G.Adj v w → H.Adj v w) :
    ∃ c : G.ConnectedComponent, H.verts = c.supp := by
  rw [SimpleGraph.ConnectedComponent.exists]
  obtain ⟨v, hv⟩ := hc.nonempty
  use v
  ext w
  simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  exact ⟨fun hw ↦ by simpa using (hc ⟨w, hw⟩ ⟨v, hv⟩).map H.hom,
    fun a ↦ a.symm.mem_subgraphVerts h hv⟩

end Subgraph

namespace ConnectedComponent

variable (C : G.ConnectedComponent)

/-- The induced subgraph of a connected component. -/
/-
**SimpleGraph.ConnectedComponent.toSubgraph** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleG
raph.ConnectedComponent`。
形式化陈述：toSubgraph : G.Subgraph
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced subgraph of a connected component.
-/
abbrev toSubgraph : G.Subgraph :=
  .induce ⊤ C.supp

@[simp]
/-
**SimpleGraph.ConnectedComponent.coe_toSubgraph** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph.ConnectedComponent`。
形式化陈述：coe_toSubgraph : C.toSubgraph.coe = C.toSimpleGraph
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.induce_eq_coe_induce_top`：∀ {V : Type u} {G : SimpleGraph V}
 (s : Set V), SimpleGraph.induce s G = (⊤.induce s).coe
-/
lemma coe_toSubgraph : C.toSubgraph.coe = C.toSimpleGraph :=
  induce_eq_coe_induce_top C.supp |>.symm

@[simp]
/-
**SimpleGraph.ConnectedComponent.spanningCoe_toSubgraph** 是 Mathlib 中的一个引理，位于命名空
间 `SimpleGraph.ConnectedComponent`。
形式化陈述：spanningCoe_toSubgraph : C.toSubgraph.spanningCoe = C.toSimpleGraph.spanni
ngCoe
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.spanningCoe_induce_top`：∀ {V : Type u} {G : SimpleGraph V} (
s : Set V), (⊤.induce s).spanningCoe = (SimpleGraph.induce s G).spanningCoe
-/
lemma spanningCoe_toSubgraph : C.toSubgraph.spanningCoe = C.toSimpleGraph.spanningCoe :=
  spanningCoe_induce_top _
/-
**SimpleGraph.ConnectedComponent.connected_toSubgraph** 是 Mathlib 中的一个引理，位于命名空间 
`SimpleGraph.ConnectedComponent`。
形式化陈述：connected_toSubgraph : C.toSubgraph.Connected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.ConnectedComponent.connected_toSimpleGraph`：connected_toSimp
leGraph (C : ConnectedComponent G) : (C.toSimpleGraph).Connected where preconnec
ted
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.ConnectedComponent.coe_toSubgraph`：coe_toSubgraph : C.toSubg
raph.coe = C.toSimpleGraph
-/
lemma connected_toSubgraph : C.toSubgraph.Connected :=
  ⟨C.coe_toSubgraph ▸ C.connected_toSimpleGraph⟩
/-
**SimpleGraph.ConnectedComponent.maximal_connected_toSubgraph** 是 Mathlib 中的一个定理
，位于命名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：maximal_connected_toSubgraph (C : G.ConnectedComponent) : Maximal Subgraph
.Connected C.toSubgraph
参数：C : G.ConnectedComponent。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ConnectedComponent.ind`：∀ {V : Type u} {G : SimpleGraph V} {
β : G.ConnectedComponent → Prop},   (∀ (v : V), β (G.connectedComponentMk v)) → 
∀ (c : G.ConnectedCompon…
· 使用引理 `SimpleGraph.ConnectedComponent.connected_toSubgraph`：connected_toSubgrap
h : C.toSubgraph.Connected
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `SimpleGraph.Subgraph.le_induce_top_verts`：le_induce_top_verts : G' <= (⊤
 : G.Subgraph).induce G'.verts
· 使用定理 `SimpleGraph.Subgraph.induce_mono_right`：induce_mono_right (hs : s subset
eq s') : G'.induce s <= G'.induce s'
· 使用定理 `SimpleGraph.ConnectedComponent.sound`：∀ {V : Type u} {G : SimpleGraph V}
 {v w : V}, G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk 
w
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `SimpleGraph.Subgraph.Connected.coe`：∀ {V : Type u} {G : SimpleGraph V} {
H : G.Subgraph}, H.Connected → H.coe.Connected
-/
theorem maximal_connected_toSubgraph (C : G.ConnectedComponent) :
    Maximal Subgraph.Connected C.toSubgraph := by
  refine C.ind fun v ↦ ⟨connected_toSubgraph _, fun G' hconn hle ↦ ?_⟩
  refine le_trans Subgraph.le_induce_top_verts <| Subgraph.induce_mono_right fun u hu ↦ ?_
  exact ConnectedComponent.sound <| hconn.coe.preconnected ⟨u, hu⟩ ⟨v, hle.left rfl⟩ |>.map G'.hom
/-
**SimpleGraph.ConnectedComponent.maximal_subgraph_connected_iff** 是 Mathlib 中的一个
定理，位于命名空间 `SimpleGraph.ConnectedComponent`。
形式化陈述：maximal_subgraph_connected_iff (G' : G.Subgraph) : Maximal Subgraph.Connec
ted G' ↔ exists C : G.ConnectedComponent, C.toSubgraph = G'
参数：G' : G.Subgraph。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph
 V} {H : G.Subgraph}, H.Connected → H.verts.Nonempty
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `SimpleGraph.Subgraph.le_induce_top_verts`：le_induce_top_verts : G' <= (⊤
 : G.Subgraph).induce G'.verts
· 使用定理 `SimpleGraph.Subgraph.induce_mono_right`：induce_mono_right (hs : s subset
eq s') : G'.induce s <= G'.induce s'
· 使用定理 `SimpleGraph.ConnectedComponent.sound`：∀ {V : Type u} {G : SimpleGraph V}
 {v w : V}, G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk 
w
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `SimpleGraph.Subgraph.Connected.coe`：∀ {V : Type u} {G : SimpleGraph V} {
H : G.Subgraph}, H.Connected → H.coe.Connected
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `SimpleGraph.ConnectedComponent.connected_toSubgraph`：connected_toSubgrap
h : C.toSubgraph.Connected
· 使用定理 `SimpleGraph.ConnectedComponent.maximal_connected_toSubgraph`：maximal_con
nected_toSubgraph (C : G.ConnectedComponent) : Maximal Subgraph.Connected C.toSu
bgraph
-/
theorem maximal_subgraph_connected_iff (G' : G.Subgraph) :
    Maximal Subgraph.Connected G' ↔ ∃ C : G.ConnectedComponent, C.toSubgraph = G' := by
  refine ⟨fun ⟨hconn, h⟩ ↦ ?_, fun ⟨C, h⟩ ↦ ?_⟩
  · have ⟨v, hv⟩ := hconn.nonempty
    suffices G' ≤ (G.connectedComponentMk v).toSubgraph from
      ⟨G.connectedComponentMk v, le_antisymm (h (connected_toSubgraph _) this) this⟩
    exact le_trans Subgraph.le_induce_top_verts <| Subgraph.induce_mono_right fun u hu ↦
      ConnectedComponent.sound <| hconn.coe.preconnected ⟨u, hu⟩ ⟨v, hv⟩ |>.map G'.hom
  · exact h ▸ maximal_connected_toSubgraph _

end ConnectedComponent

/-! ### Walks as subgraphs -/

namespace Walk

variable {u v w : V}

/-- The subgraph consisting of the vertices and edges of the walk. -/
@[simp]
/-
**SimpleGraph.Walk.toSubgraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u v : V} → G.Walk u v → G.Subgraph
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgraph consisting of the vertices and edges of the walk.
-/
protected def toSubgraph {u v : V} : G.Walk u v → G.Subgraph
  | nil => G.singletonSubgraph u
  | cons h p => G.subgraphOfAdj h ⊔ p.toSubgraph
/-
**SimpleGraph.Walk.toSubgraph_cons_nil_eq_subgraphOfAdj** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.Walk`。
形式化陈述：toSubgraph_cons_nil_eq_subgraphOfAdj (h : G.Adj u v) : (cons h nil).toSubg
raph = G.subgraphOfAdj h
参数：h : G.Adj u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `SimpleGraph.subgraphOfAdj_verts`：∀ {V : Type u} (G : SimpleGraph V) {v w
 : V} (hvw : G.Adj v w), (G.subgraphOfAdj hvw).verts = {v, w}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem toSubgraph_cons_nil_eq_subgraphOfAdj (h : G.Adj u v) :
    (cons h nil).toSubgraph = G.subgraphOfAdj h := by simp
/-
**SimpleGraph.Walk.mem_verts_toSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：mem_verts_toSubgraph (p : G.Walk u v) : w in p.toSubgraph.verts ↔ w in p.s
upport
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.singletonSubgraph_verts`：∀ {V : Type u} (G : SimpleGraph V) 
(v : V), (G.singletonSubgraph v).verts = {v}
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `SimpleGraph.subgraphOfAdj_verts`：∀ {V : Type u} (G : SimpleGraph V) {v w
 : V} (hvw : G.Adj v w), (G.subgraphOfAdj hvw).verts = {v, w}
-/
theorem mem_verts_toSubgraph (p : G.Walk u v) : w ∈ p.toSubgraph.verts ↔ w ∈ p.support := by
  induction p with
  | nil => simp
  | cons h p' ih =>
    rename_i x y z
    have : w = y ∨ w ∈ p'.support ↔ w ∈ p'.support :=
      ⟨by rintro (rfl | h) <;> simp [*], by simp +contextual⟩
    simp [ih, or_assoc, this]
/-
**SimpleGraph.Walk.not_nil_of_adj_toSubgraph** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：not_nil_of_adj_toSubgraph {u v} {x : V} {p : G.Walk u v} (hadj : p.toSubgr
aph.Adj w x) : ¬p.Nil
参数：hadj : p.toSubgraph.Adj w x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.singletonSubgraph_adj`：∀ {V : Type u} (G : SimpleGraph V) (v
 a a_1 : V), (G.singletonSubgraph v).Adj a a_1 = ⊥ a a_1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_nil_of_adj_toSubgraph {u v} {x : V} {p : G.Walk u v} (hadj : p.toSubgraph.Adj w x) :
    ¬p.Nil := by
  cases p <;> simp_all
/-
**SimpleGraph.Walk.start_mem_verts_toSubgraph** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：start_mem_verts_toSubgraph (p : G.Walk u v) : u in p.toSubgraph.verts
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma start_mem_verts_toSubgraph (p : G.Walk u v) : u ∈ p.toSubgraph.verts := by
  simp [mem_verts_toSubgraph]
/-
**SimpleGraph.Walk.end_mem_verts_toSubgraph** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：end_mem_verts_toSubgraph (p : G.Walk u v) : v in p.toSubgraph.verts
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma end_mem_verts_toSubgraph (p : G.Walk u v) : v ∈ p.toSubgraph.verts := by
  simp [mem_verts_toSubgraph]

@[simp]
/-
**SimpleGraph.Walk.verts_toSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：verts_toSubgraph (p : G.Walk u v) : p.toSubgraph.verts = { w | w in p.supp
ort }
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SimpleGraph.Walk.mem_verts_toSubgraph`：mem_verts_toSubgraph (p : G.Walk 
u v) : w in p.toSubgraph.verts ↔ w in p.support
-/
theorem verts_toSubgraph (p : G.Walk u v) : p.toSubgraph.verts = { w | w ∈ p.support } :=
  Set.ext fun _ => p.mem_verts_toSubgraph
/-
**SimpleGraph.Walk.mem_edges_toSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：mem_edges_toSubgraph (p : G.Walk u v) {e : Sym2 V} : e in p.toSubgraph.edg
eSet ↔ e in p.edges
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.edgeSet_singletonSubgraph`：edgeSet_singletonSubgraph (v : V)
 : (G.singletonSubgraph v).edgeSet = ∅
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `SimpleGraph.Subgraph.edgeSet_sup`：edgeSet_sup {H₁ H₂ : Subgraph G} : (H₁
 ⊔ H₂).edgeSet = H₁.edgeSet union H₂.edgeSet
· 使用定理 `SimpleGraph.edgeSet_subgraphOfAdj`：edgeSet_subgraphOfAdj {v w : V} (hvw 
: G.Adj v w) : (G.subgraphOfAdj hvw).edgeSet = {s(v, w)}
-/
theorem mem_edges_toSubgraph (p : G.Walk u v) {e : Sym2 V} :
    e ∈ p.toSubgraph.edgeSet ↔ e ∈ p.edges := by induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.edgeSet_toSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：edgeSet_toSubgraph (p : G.Walk u v) : p.toSubgraph.edgeSet = p.edgeSet
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `SimpleGraph.Walk.mem_edges_toSubgraph`：mem_edges_toSubgraph (p : G.Walk 
u v) {e : Sym2 V} : e in p.toSubgraph.edgeSet ↔ e in p.edges
-/
theorem edgeSet_toSubgraph (p : G.Walk u v) : p.toSubgraph.edgeSet = p.edgeSet :=
  Set.ext fun _ => p.mem_edges_toSubgraph
/-
**SimpleGraph.Walk._root_.SimpleGraph.Adj.toSubgraph_toWalk** 是 Mathlib 中的一个定理，位
于命名空间 `SimpleGraph.Walk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.Adj.toSubgraph_toWalk (h : G.Adj u v) :
    h.toWalk.toSubgraph = G.subgraphOfAdj h := by
  ext <;> simp

@[simp]
/-
**SimpleGraph.Walk.toSubgraph_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：toSubgraph_append (p : G.Walk u v) (q : G.Walk v w) : (p.append q).toSubgr
aph = p.toSubgraph ⊔ q.toSubgraph
参数：p : G.Walk u v；q : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.verts_toSubgraph`：verts_toSubgraph (p : G.Walk u v) : p
.toSubgraph.verts = { w | w in p.support }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.toSubgraph.eq_2`：∀ {V : Type u} {G : SimpleGraph V} {u 
v : V} (v_3 : V) (h : G.Adj u v_3) (p : G.Walk v_3 v),   (SimpleGraph.Walk.cons 
h p).toSubgraph = G.su…
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
-/
theorem toSubgraph_append (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).toSubgraph = p.toSubgraph ⊔ q.toSubgraph := by induction p <;> simp [*, sup_assoc]

@[simp]
/-
**SimpleGraph.Walk.toSubgraph_reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：toSubgraph_reverse (p : G.Walk u v) : p.reverse.toSubgraph = p.toSubgraph
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.toSubgraph.eq_1`：∀ {V : Type u} {G : SimpleGraph V} {u 
: V}, SimpleGraph.Walk.nil.toSubgraph = G.singletonSubgraph u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Walk.reverse_cons`：reverse_cons {u v w : V} (h : G.Adj u v) 
(p : G.Walk v w) : (cons h p).reverse = p.reverse.append (cons h.symm nil)
· 使用定理 `SimpleGraph.Walk.toSubgraph_append`：toSubgraph_append (p : G.Walk u v) (
q : G.Walk v w) : (p.append q).toSubgraph = p.toSubgraph ⊔ q.toSubgraph
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.subgraphOfAdj_symm`：subgraphOfAdj_symm {v w : V} (hvw : G.Ad
j v w) : G.subgraphOfAdj hvw.symm = G.subgraphOfAdj hvw
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `SimpleGraph.Subgraph.ext`：∀ {V : Type u} {G : SimpleGraph V} {x y : G.Su
bgraph}, x.verts = y.verts → x.Adj = y.Adj → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `SimpleGraph.subgraphOfAdj_verts`：∀ {V : Type u} (G : SimpleGraph V) {v w
 : V} (hvw : G.Adj v w), (G.subgraphOfAdj hvw).verts = {v, w}
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.subgraphOfAdj_adj`：∀ {V : Type u} (G : SimpleGraph V) {v w :
 V} (hvw : G.Adj v w) (a b : V),   (G.subgraphOfAdj hvw).Adj a b = (s(v, w) = s(
a, b))
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
-/
theorem toSubgraph_reverse (p : G.Walk u v) : p.reverse.toSubgraph = p.toSubgraph := by
  induction p with
  | nil => simp
  | cons _ _ _ =>
    simp only [*, Walk.toSubgraph, reverse_cons, toSubgraph_append, subgraphOfAdj_symm]
    rw [sup_comm]
    congr
    ext <;> simp [-Set.bot_eq_empty]

@[simp]
/-
**SimpleGraph.Walk.toSubgraph_rotate** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：toSubgraph_rotate [DecidableEq V] (c : G.Walk v v) (h : u in c.support) : 
(c.rotate u h).toSubgraph = c.toSubgraph
参数：c : G.Walk v v；h : u in c.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.rotate.eq_1`：∀ {V : Type u} {G : SimpleGraph V} {v : V}
 [inst : DecidableEq V] (c : G.Walk v v) (u : V) (h : u ∈ c.support),   c.rotate
 u h = (c.dropUnti…
· 使用定理 `SimpleGraph.Walk.toSubgraph_append`：toSubgraph_append (p : G.Walk u v) (
q : G.Walk v w) : (p.append q).toSubgraph = p.toSubgraph ⊔ q.toSubgraph
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
-/
theorem toSubgraph_rotate [DecidableEq V] (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate u h).toSubgraph = c.toSubgraph := by
  rw [rotate, toSubgraph_append, sup_comm, ← toSubgraph_append, take_spec]

@[simp]
/-
**SimpleGraph.Walk.toSubgraph_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：toSubgraph_map (f : G ->g G') (p : G.Walk u v) : (p.map f).toSubgraph = p.
toSubgraph.map f
参数：f : G ->g G'；p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.toSubgraph.eq_1`：∀ {V : Type u} {G : SimpleGraph V} {u 
: V}, SimpleGraph.Walk.nil.toSubgraph = G.singletonSubgraph u
· 使用定理 `SimpleGraph.map_singletonSubgraph`：map_singletonSubgraph (f : G ->g G') 
{v : V} : Subgraph.map f (G.singletonSubgraph v) = G'.singletonSubgraph (f v)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Hom.map_adj`：map_adj {v w : V} (h : G.Adj v w) : G'.Adj (f v
) (f w)
· 使用定理 `SimpleGraph.Walk.toSubgraph.eq_2`：∀ {V : Type u} {G : SimpleGraph V} {u 
v : V} (v_3 : V) (h : G.Adj u v_3) (p : G.Walk v_3 v),   (SimpleGraph.Walk.cons 
h p).toSubgraph = G.su…
· 使用定理 `SimpleGraph.Subgraph.map_sup`：map_sup (f : G ->g G') (H₁ H₂ : G.Subgraph
) : (H₁ ⊔ H₂).map f = H₁.map f ⊔ H₂.map f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.map_subgraphOfAdj`：map_subgraphOfAdj (f : G ->g G') {v w : V
} (hvw : G.Adj v w) : Subgraph.map f (G.subgraphOfAdj hvw) = G'.subgraphOfAdj (f
.map_adj hvw)
-/
theorem toSubgraph_map (f : G →g G') (p : G.Walk u v) :
    (p.map f).toSubgraph = p.toSubgraph.map f := by induction p <;> simp [*, Subgraph.map_sup]

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.Walk.adj_toSubgraph_mapLe** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：adj_toSubgraph_mapLe {G' : SimpleGraph V} {w x : V} {p : G.Walk u v} (h : 
G <= G') : (p.mapLe h).toSubgraph.Adj w x ↔ p.toSubgraph.Adj w x
参数：h : G <= G'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.toSubgraph_map`：toSubgraph_map (f : G ->g G') (p : G.Wa
lk u v) : (p.map f).toSubgraph = p.toSubgraph.map f
· 使用定理 `SimpleGraph.Subgraph.map_adj`：∀ {V : Type u} {W : Type v} {G : SimpleGra
ph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (a a_1 : W),   (Simple
Graph.Subgraph.map…
· 使用定理 `Relation.map_id_id`：∀ {α : Type u_1} {β : Type u_2} (r : α → β → Prop), 
Relation.Map r id id = r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma adj_toSubgraph_mapLe {G' : SimpleGraph V} {w x : V} {p : G.Walk u v} (h : G ≤ G') :
    (p.mapLe h).toSubgraph.Adj w x ↔ p.toSubgraph.Adj w x := by
  simp

@[simp]
/-
**SimpleGraph.Walk.finite_neighborSet_toSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：finite_neighborSet_toSubgraph (p : G.Walk u v) : (p.toSubgraph.neighborSet
 w).Finite
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.toSubgraph.eq_1`：∀ {V : Type u} {G : SimpleGraph V} {u 
: V}, SimpleGraph.Walk.nil.toSubgraph = G.singletonSubgraph u
· 使用定理 `SimpleGraph.neighborSet_singletonSubgraph`：neighborSet_singletonSubgraph
 (v w : V) : (G.singletonSubgraph v).neighborSet w = ∅
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `SimpleGraph.Walk.toSubgraph.eq_2`：∀ {V : Type u} {G : SimpleGraph V} {u 
v : V} (v_3 : V) (h : G.Adj u v_3) (p : G.Walk v_3 v),   (SimpleGraph.Walk.cons 
h p).toSubgraph = G.su…
· 使用定理 `SimpleGraph.Subgraph.neighborSet_sup`：neighborSet_sup {H H' : G.Subgraph
} (v : V) : (H ⊔ H').neighborSet v = H.neighborSet v union H'.neighborSet v
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `SimpleGraph.neighborSet_subgraphOfAdj_subset`：neighborSet_subgraphOfAdj_
subset {u v w : V} (hvw : G.Adj v w) : (G.subgraphOfAdj hvw).neighborSet u subse
teq {v, w}
-/
theorem finite_neighborSet_toSubgraph (p : G.Walk u v) : (p.toSubgraph.neighborSet w).Finite := by
  induction p with
  | nil =>
    rw [Walk.toSubgraph, neighborSet_singletonSubgraph]
    apply Set.toFinite
  | cons ha _ ih =>
    rw [Walk.toSubgraph, Subgraph.neighborSet_sup]
    refine Set.Finite.union ?_ ih
    refine Set.Finite.subset ?_ (neighborSet_subgraphOfAdj_subset ha)
    apply Set.toFinite
/-
**SimpleGraph.Walk.toSubgraph_le_induce_support** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：toSubgraph_le_induce_support (p : G.Walk u v) : p.toSubgraph <= (⊤ : G.Sub
graph).induce {v | v in p.support}
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.verts_toSubgraph`：verts_toSubgraph (p : G.Walk u v) : p
.toSubgraph.verts = { w | w in p.support }
· 使用引理 `SimpleGraph.Subgraph.le_induce_top_verts`：le_induce_top_verts : G' <= (⊤
 : G.Subgraph).induce G'.verts
-/
lemma toSubgraph_le_induce_support (p : G.Walk u v) :
    p.toSubgraph ≤ (⊤ : G.Subgraph).induce {v | v ∈ p.support} := by
  convert! Subgraph.le_induce_top_verts
  exact p.verts_toSubgraph.symm
/-
**SimpleGraph.Walk.toSubgraph_adj_getVert** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Walk`。
形式化陈述：toSubgraph_adj_getVert {u v} (w : G.Walk u v) {i : Nat} (hi : i < w.length
) : w.toSubgraph.Adj (w.getVert i) (w.getVert (i + 1))
参数：w : G.Walk u v；hi : i < w.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.subgraphOfAdj_adj`：∀ {V : Type u} (G : SimpleGraph V) {v w :
 V} (hvw : G.Adj v w) (a b : V),   (G.subgraphOfAdj hvw).Adj a b = (s(v, w) = s(
a, b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_lt_succ_iff`：∀ {a b : ℕ}, a.succ < b.succ ↔ a < b
-/
theorem toSubgraph_adj_getVert {u v} (w : G.Walk u v) {i : ℕ} (hi : i < w.length) :
    w.toSubgraph.Adj (w.getVert i) (w.getVert (i + 1)) := by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy i' ih =>
    cases i
    · simp
    · simp only [Walk.toSubgraph, getVert_cons_succ, Subgraph.sup_adj, subgraphOfAdj_adj, Sym2.eq,
        Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      right
      exact ih (Nat.succ_lt_succ_iff.mp hi)
/-
**SimpleGraph.Walk.toSubgraph_adj_snd** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：toSubgraph_adj_snd {u v} (w : G.Walk u v) (h : ¬ w.Nil) : w.toSubgraph.Adj
 u w.snd
参数：w : G.Walk u v；h : ¬ w.Nil。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `SimpleGraph.Walk.toSubgraph_adj_getVert`：toSubgraph_adj_getVert {u v} (w
 : G.Walk u v) {i : Nat} (hi : i < w.length) : w.toSubgraph.Adj (w.getVert i) (w
.getVert (i + 1))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.Walk.not_nil_iff_lt_length`：not_nil_iff_lt_length {p : G.Wal
k v w} : ¬ p.Nil ↔ 0 < p.length
-/
theorem toSubgraph_adj_snd {u v} (w : G.Walk u v) (h : ¬ w.Nil) : w.toSubgraph.Adj u w.snd := by
  simpa using w.toSubgraph_adj_getVert (not_nil_iff_lt_length.mp h)
/-
**SimpleGraph.Walk.toSubgraph_adj_penultimate** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：toSubgraph_adj_penultimate {u v} (w : G.Walk u v) (h : ¬ w.Nil) : w.toSubg
raph.Adj w.penultimate v
参数：w : G.Walk u v；h : ¬ w.Nil。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `SimpleGraph.Walk.not_nil_iff_lt_length`：not_nil_iff_lt_length {p : G.Wal
k v w} : ¬ p.Nil ↔ 0 < p.length
· 使用定理 `SimpleGraph.Walk.getVert_length`：getVert_length {u v} (w : G.Walk u v) :
 w.getVert w.length = v
· 使用定理 `SimpleGraph.Walk.toSubgraph_adj_getVert`：toSubgraph_adj_getVert {u v} (w
 : G.Walk u v) {i : Nat} (hi : i < w.length) : w.toSubgraph.Adj (w.getVert i) (w
.getVert (i + 1))
-/
theorem toSubgraph_adj_penultimate {u v} (w : G.Walk u v) (h : ¬ w.Nil) :
    w.toSubgraph.Adj w.penultimate v := by
  rw [not_nil_iff_lt_length] at h
  simpa [show w.length - 1 + 1 = w.length by lia]
    using w.toSubgraph_adj_getVert (by lia : w.length - 1 < w.length)
/-
**SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：adj_toSubgraph_iff_mem_edges {u v u' v' : V} {p : G.Walk u v} : p.toSubgra
ph.Adj u' v' ↔ s(u', v') in p.edges
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.mem_edges_toSubgraph`：mem_edges_toSubgraph (p : G.Walk 
u v) {e : Sym2 V} : e in p.toSubgraph.edgeSet ↔ e in p.edges
· 使用定理 `SimpleGraph.Subgraph.mem_edgeSet`：∀ {V : Type u} {G : SimpleGraph V} {G'
 : G.Subgraph} {v w : V}, s(v, w) ∈ G'.edgeSet ↔ G'.Adj v w
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma adj_toSubgraph_iff_mem_edges {u v u' v' : V} {p : G.Walk u v} :
    p.toSubgraph.Adj u' v' ↔ s(u', v') ∈ p.edges := by
  rw [← mem_edges_toSubgraph, Subgraph.mem_edgeSet]
/-
**SimpleGraph.Walk.toSubgraph_adj_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：toSubgraph_adj_iff {u v u' v'} (w : G.Walk u v) : w.toSubgraph.Adj u' v' ↔
 exists i, s(w.getVert i, w.getVert (i + 1)) = s(u', v') ∧ i < w.length
参数：w : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgraph_adj_iff {u v u' v'} (w : G.Walk u v) :
    w.toSubgraph.Adj u' v' ↔ ∃ i, s(w.getVert i, w.getVert (i + 1)) =
      s(u', v') ∧ i < w.length := by
  grind [adj_toSubgraph_iff_mem_edges, mk_mem_edges_iff_exists]
/-
**SimpleGraph.Walk.mem_support_of_adj_toSubgraph** 是 Mathlib 中的一个引理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：mem_support_of_adj_toSubgraph {u v u' v' : V} {p : G.Walk u v} (hp : p.toS
ubgraph.Adj u' v') : u' in p.support
参数：hp : p.toSubgraph.Adj u' v'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.mem_verts_toSubgraph`：mem_verts_toSubgraph (p : G.Walk 
u v) : w in p.toSubgraph.verts ↔ w in p.support
· 使用定理 `SimpleGraph.Subgraph.edge_vert`：∀ {V : Type u} {G : SimpleGraph V} (self
 : G.Subgraph) {v w : V}, self.Adj v w → v ∈ self.verts
-/
lemma mem_support_of_adj_toSubgraph {u v u' v' : V} {p : G.Walk u v} (hp : p.toSubgraph.Adj u' v') :
    u' ∈ p.support := p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hp)
/-
**SimpleGraph.Walk.toSubgraph_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：toSubgraph_le_iff {w : G.Walk u v} (hnil : ¬w.Nil) {G' : G.Subgraph} : w.t
oSubgraph <= G' ↔ w.edgeSet subseteq G'.edgeSet
参数：hnil : ¬w.Nil。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.edgeSet_mono`：edgeSet_mono {H₁ H₂ : Subgraph G} (h 
: H₁ <= H₂) : H₁.edgeSet <= H₂.edgeSet
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.mem_edges_toSubgraph`：mem_edges_toSubgraph (p : G.Walk 
u v) {e : Sym2 V} : e in p.toSubgraph.edgeSet ↔ e in p.edges
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil`：mem_suppor
t_iff_exists_mem_edges_of_not_nil {u v w : V} {p : G.Walk u v} (hnil : ¬p.Nil) :
 w in p.support ↔ exists e in p.edges, w in e
· 使用定理 `SimpleGraph.Walk.mem_verts_toSubgraph`：mem_verts_toSubgraph (p : G.Walk 
u v) : w in p.toSubgraph.verts ↔ w in p.support
· 使用定理 `SimpleGraph.Subgraph.mem_verts_of_mem_edge`：mem_verts_of_mem_edge {G' : 
Subgraph G} {e : Sym2 V} {v : V} (he : e in G'.edgeSet) (hv : v in e) : v in G'.
verts
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem toSubgraph_le_iff {w : G.Walk u v} (hnil : ¬w.Nil) {G' : G.Subgraph} :
    w.toSubgraph ≤ G' ↔ w.edgeSet ⊆ G'.edgeSet := by
  refine ⟨fun hw e he ↦ Subgraph.edgeSet_mono hw <| w.mem_edges_toSubgraph.mpr he, fun hw ↦ ?_⟩
  refine ⟨fun v' hv' ↦ ?_, fun u' v' hadj ↦ hw <| w.mem_edges_toSubgraph.mp (hadj : s(_, _) ∈ _)⟩
  rw [mem_verts_toSubgraph, mem_support_iff_exists_mem_edges_of_not_nil hnil] at hv'
  have ⟨e, he, hv'e⟩ := hv'
  exact G'.mem_verts_of_mem_edge (hw he) hv'e
/-
**SimpleGraph.Walk.toSubgraph_bypass_le_toSubgraph** 是 Mathlib 中的一个引理，位于命名空间 `Si
mpleGraph.Walk`。
形式化陈述：toSubgraph_bypass_le_toSubgraph {u v : V} {p : G.Walk u v} [DecidableEq V]
 : p.bypass.toSubgraph <= p.toSubgraph
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.verts_toSubgraph`：verts_toSubgraph (p : G.Walk u v) : p
.toSubgraph.verts = { w | w in p.support }
· 使用定理 `SimpleGraph.Walk.support_bypass_subset_support`：support_bypass_subset_su
pport (p : G.Walk u v) : p.bypass.support subseteq p.support
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Walk.edges_toPath_subset_edges`：edges_toPath_subset_edges (p
 : G.Walk u v) : (p.toPath : G.Walk u v).edges subseteq p.edges
-/
lemma toSubgraph_bypass_le_toSubgraph {u v : V} {p : G.Walk u v} [DecidableEq V] :
    p.bypass.toSubgraph ≤ p.toSubgraph := by
  constructor
  · simpa using! p.support_bypass_subset_support
  · simpa [adj_toSubgraph_iff_mem_edges] using! fun _ _ h ↦ p.edges_toPath_subset_edges h

/-- Map a walk to its own subgraph. -/
/-
**SimpleGraph.Walk.mapToSubgraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：mapToSubgraph {u v : V} : forall w : G.Walk u v, w.toSubgraph.coe.Walk ⟨_,
 w.start_mem_verts_toSubgraph⟩ ⟨_, w.end_mem_verts_toSubgraph⟩ | nil => nil | co
ns .. => .toSubgraph.Adj ..
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.start_mem_verts_toSubgraph`：start_mem_verts_toSubgraph 
(p : G.Walk u v) : u in p.toSubgraph.verts
· 使用引理 `SimpleGraph.Walk.end_mem_verts_toSubgraph`：end_mem_verts_toSubgraph (p :
 G.Walk u v) : v in p.toSubgraph.verts

--- 原说明 ---
Map a walk to its own subgraph.
-/
def mapToSubgraph {u v : V} : ∀ w : G.Walk u v, w.toSubgraph.coe.Walk
    ⟨_, w.start_mem_verts_toSubgraph⟩ ⟨_, w.end_mem_verts_toSubgraph⟩
  | nil => nil
  | cons .. =>
    let h : cons .. |>.toSubgraph.Adj .. := (le_sup_left : _ ≤ Walk.toSubgraph _).right rfl
    let h : cons .. |>.toSubgraph.coe.Adj ⟨_, h.fst_mem⟩ ⟨_, h.snd_mem⟩ := h
    cons h <| mapToSubgraph _ |>.map <| Subgraph.inclusion le_sup_right

set_option backward.isDefEq.respectTransparency false in
/-- Mapping a walk to its own subgraph and then to the original graph produces the same walk. -/
/-
**SimpleGraph.Walk.map_mapToSubgraph_hom** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (w : G.Walk u v), SimpleGraph
.Walk.map w.toSubgraph.hom w.mapToSubgraph = w
参数：w : G.Walk u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.start_mem_verts_toSubgraph`：start_mem_verts_toSubgraph 
(p : G.Walk u v) : u in p.toSubgraph.verts
· 使用引理 `SimpleGraph.Walk.end_mem_verts_toSubgraph`：end_mem_verts_toSubgraph (p :
 G.Walk u v) : v in p.toSubgraph.verts

--- 原说明 ---
Mapping a walk to its own subgraph and then to the original graph produces the s
ame walk.
-/
theorem map_mapToSubgraph_hom {u v : V} : ∀ w : G.Walk u v, w.mapToSubgraph.map w.toSubgraph.hom = w
  | nil => rfl
  | cons _ w => by
    rw [mapToSubgraph, Walk.map, map_map]
    exact congrArg₂ _ rfl w.map_mapToSubgraph_hom

set_option backward.isDefEq.respectTransparency false in
/-- Mapping a walk to its own subgraph and then to `G[s]` where `s` contains the walk's support is
the same as inducing the walk to `s`. -/
/-
**SimpleGraph.Walk.map_mapToSubgraph_eq_induce** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} (s : Set V) {u v : V} (w : G.Walk u v) 
(hs : ∀ x ∈ w.support, x ∈ s),   SimpleGraph.Walk.map { toFun := fun x => ⟨↑x, ⋯
⟩, map_rel' := ⋯ } w.mapToSubgraph = SimpleGraph.Walk.induce s w hs
参数：s : Set V；w : G.Walk u v；hs : ∀ x ∈ w.support, x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.adj_sub`：∀ {V : Type u} {G : SimpleGraph V} (self :
 G.Subgraph) {v w : V}, self.Adj v w → G.Adj v w
· 使用引理 `SimpleGraph.Walk.start_mem_verts_toSubgraph`：start_mem_verts_toSubgraph 
(p : G.Walk u v) : u in p.toSubgraph.verts
· 使用引理 `SimpleGraph.Walk.end_mem_verts_toSubgraph`：end_mem_verts_toSubgraph (p :
 G.Walk u v) : v in p.toSubgraph.verts

--- 原说明 ---
Mapping a walk to its own subgraph and then to `G[s]` where `s` contains the wal
k's support is
the same as inducing the walk to `s`.
-/
theorem map_mapToSubgraph_eq_induce (s : Set V) {u v : V} :
    ∀ (w : G.Walk u v) (hs : ∀ x ∈ w.support, x ∈ s),
      w.mapToSubgraph.map (⟨(⟨·, by grind [mem_verts_toSubgraph]⟩), w.toSubgraph.adj_sub⟩ :
        w.toSubgraph.coe →g G.induce s) = w.induce s hs
  | nil, hs => rfl
  | cons hadj w, hs => by
    rw [mapToSubgraph, map_cons, map_map]
    exact congrArg _ <| w.map_mapToSubgraph_eq_induce s (hs · <| List.mem_of_mem_tail ·)

/-- Mapping a walk to its own subgraph and then to `G[w.support]` is the same as inducing the walk
to its support. -/
/-
**SimpleGraph.Walk.map_mapToSubgraph_eq_induce_id** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk`。
形式化陈述：map_mapToSubgraph_eq_induce_id {u v : V} (w : G.Walk u v) : w.mapToSubgrap
h.map (⟨fun v => ⟨v, w.mem_verts_toSubgraph.mp v.prop⟩, w.toSubgraph.adj_sub⟩ : 
w.toSubgraph.coe ->g G.induce _) = w.induce _ (fun _ => id)
参数：w : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.map_mapToSubgraph_eq_induce`：∀ {V : Type u} {G : Simple
Graph V} (s : Set V) {u v : V} (w : G.Walk u v) (hs : ∀ x ∈ w.support, x ∈ s),  
 SimpleGraph.Walk.map { toFun := f…

--- 原说明 ---
Mapping a walk to its own subgraph and then to `G[w.support]` is the same as ind
ucing the walk
to its support.
-/
theorem map_mapToSubgraph_eq_induce_id {u v : V} (w : G.Walk u v) :
    w.mapToSubgraph.map (⟨fun v ↦ ⟨v, w.mem_verts_toSubgraph.mp v.prop⟩, w.toSubgraph.adj_sub⟩ :
      w.toSubgraph.coe →g G.induce _) = w.induce _ (fun _ ↦ id) :=
  w.map_mapToSubgraph_eq_induce ..
/-
**SimpleGraph.Walk.isInduced_toSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：isInduced_toSubgraph {w : G.Walk u v} : w.toSubgraph.IsInduced ↔ w.IsChord
less
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.mem_edgeSet`：mem_edgeSet : s(v, w) in G.edgeSet ↔ G.Adj v w
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem isInduced_toSubgraph {w : G.Walk u v} : w.toSubgraph.IsInduced ↔ w.IsChordless := by
  simp_rw [Subgraph.IsInduced, IsChordless, IsChord, Sym2.forall, Sym2.lift_mk, G.mem_edgeSet,
    mem_verts_toSubgraph, adj_toSubgraph_iff_mem_edges]
  grind only

namespace IsPath

/-
**SimpleGraph.Walk.IsPath.neighborSet_toSubgraph_startpoint** 是 Mathlib 中的一个引理，位
于命名空间 `SimpleGraph.Walk.IsPath`。
形式化陈述：neighborSet_toSubgraph_startpoint {u v} {p : G.Walk u v} (hp : p.IsPath) (
hnp : ¬ p.Nil) : p.toSubgraph.neighborSet u = {p.snd}
参数：hp : p.IsPath；hnp : ¬ p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.toSubgraph_adj_snd`：toSubgraph_adj_snd {u v} (w : G.Wal
k u v) (h : ¬ w.Nil) : w.toSubgraph.Adj u w.snd
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
-/
lemma neighborSet_toSubgraph_startpoint {u v} {p : G.Walk u v}
    (hp : p.IsPath) (hnp : ¬ p.Nil) : p.toSubgraph.neighborSet u = {p.snd} := by
  have hadj1 := p.toSubgraph_adj_snd hnp
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  grind [getVert_eq_start_iff]
/-
**SimpleGraph.Walk.IsPath.neighborSet_toSubgraph_endpoint** 是 Mathlib 中的一个引理，位于命
名空间 `SimpleGraph.Walk.IsPath`。
形式化陈述：neighborSet_toSubgraph_endpoint {u v} {p : G.Walk u v} (hp : p.IsPath) (hn
p : ¬ p.Nil) : p.toSubgraph.neighborSet v = {p.penultimate}
参数：hp : p.IsPath；hnp : ¬ p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.toSubgraph_reverse`：toSubgraph_reverse (p : G.Walk u v)
 : p.reverse.toSubgraph = p.toSubgraph
· 使用引理 `SimpleGraph.Walk.snd_reverse`：snd_reverse (p : G.Walk u v) : p.reverse.s
nd = p.penultimate
· 使用引理 `SimpleGraph.Walk.IsPath.neighborSet_toSubgraph_startpoint`：neighborSet_t
oSubgraph_startpoint {u v} {p : G.Walk u v} (hp : p.IsPath) (hnp : ¬ p.Nil) : p.
toSubgraph.neighborSet u = {p.snd}
· 使用定理 `SimpleGraph.Walk.IsPath.reverse`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.reverse.IsPath
· 使用引理 `SimpleGraph.Walk.not_nil_iff_lt_length`：not_nil_iff_lt_length {p : G.Wal
k v w} : ¬ p.Nil ↔ 0 < p.length
· 使用定理 `SimpleGraph.Walk.length_reverse`：length_reverse {u v : V} (p : G.Walk u 
v) : p.reverse.length = p.length
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma neighborSet_toSubgraph_endpoint {u v} {p : G.Walk u v}
    (hp : p.IsPath) (hnp : ¬ p.Nil) : p.toSubgraph.neighborSet v = {p.penultimate} := by
  simpa using IsPath.neighborSet_toSubgraph_startpoint hp.reverse
      (by rw [Walk.not_nil_iff_lt_length, Walk.length_reverse]; exact
        Walk.not_nil_iff_lt_length.mp hnp)
/-
**SimpleGraph.Walk.IsPath.neighborSet_toSubgraph_internal** 是 Mathlib 中的一个引理，位于命
名空间 `SimpleGraph.Walk.IsPath`。
形式化陈述：neighborSet_toSubgraph_internal {u} {i : Nat} {p : G.Walk u v} (hp : p.IsP
ath) (h : i != 0) (h' : i < p.length) : p.toSubgraph.neighborSet (p.getVert i) =
 {p.getVert (i - 1), p.getVert (i + 1)}
参数：hp : p.IsPath；h : i != 0；h' : i < p.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {G' : 
G.Subgraph} {u v : V}, G'.Adj u v → G'.Adj v u
· 使用定理 `SimpleGraph.Walk.toSubgraph_adj_getVert`：toSubgraph_adj_getVert {u v} (w
 : G.Walk u v) {i : Nat} (hi : i < w.length) : w.toSubgraph.Adj (w.getVert i) (w
.getVert (i + 1))
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `SimpleGraph.Walk.IsPath.getVert_injOn`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → Set.InjOn p.getVert {i | i ≤ p.length}
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma neighborSet_toSubgraph_internal {u} {i : ℕ} {p : G.Walk u v} (hp : p.IsPath)
    (h : i ≠ 0) (h' : i < p.length) :
    p.toSubgraph.neighborSet (p.getVert i) = {p.getVert (i - 1), p.getVert (i + 1)} := by
  have hadj1 := ((show i - 1 + 1 = i by lia) ▸
    p.toSubgraph_adj_getVert (by lia : (i - 1) < p.length)).symm
  ext v
  simp_all only [ne_eq, Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk]
  refine ⟨?_, by aesop⟩
  rintro ⟨i', ⟨hl, _⟩ | ⟨_, hl⟩⟩ <;>
    apply hp.getVert_injOn (by rw [Set.mem_ofPred_eq]; lia)
      (by rw [Set.mem_ofPred_eq]; lia) at hl <;> aesop
/-
**SimpleGraph.Walk.IsPath.ncard_neighborSet_toSubgraph_internal_eq_two** 是 Mathl
ib 中的一个引理，位于命名空间 `SimpleGraph.Walk.IsPath`。
形式化陈述：ncard_neighborSet_toSubgraph_internal_eq_two {u} {i : Nat} {p : G.Walk u v
} (hp : p.IsPath) (h : i != 0) (h' : i < p.length) : (p.toSubgraph.neighborSet (
p.getVert i)).ncard = 2
参数：hp : p.IsPath；h : i != 0；h' : i < p.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.IsPath.neighborSet_toSubgraph_internal`：neighborSet_toS
ubgraph_internal {u} {i : Nat} {p : G.Walk u v} (hp : p.IsPath) (h : i != 0) (h'
 : i < p.length) : p.toSubgraph.neighborSet (…
· 使用定理 `SimpleGraph.Walk.IsPath.getVert_injOn`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → Set.InjOn p.getVert {i | i ≤ p.length}
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.ncard_insert_of_notMem`：∀ {α : Type u_1} {s : Set α} {a : α},   a ∉ 
s → autoParam s.Finite Set.ncard_insert_of_notMem._auto_1 → (insert a s).ncard =
 s.ncard + 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.ncard_singleton`：∀ {α : Type u_1} (a : α), {a}.ncard = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ncard_neighborSet_toSubgraph_internal_eq_two {u} {i : ℕ} {p : G.Walk u v} (hp : p.IsPath)
    (h : i ≠ 0) (h' : i < p.length) :
    (p.toSubgraph.neighborSet (p.getVert i)).ncard = 2 := by
  rw [hp.neighborSet_toSubgraph_internal h h']
  have : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro h
    have := hp.getVert_injOn (by rw [Set.mem_ofPred_eq]; lia) (by rw [Set.mem_ofPred_eq]; lia) h
    lia
  simp_all
/-
**SimpleGraph.Walk.IsPath.snd_of_toSubgraph_adj** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph.Walk.IsPath`。
形式化陈述：snd_of_toSubgraph_adj {u v v'} {p : G.Walk u v} (hp : p.IsPath) (hadj : p.
toSubgraph.Adj u v') : p.snd = v'
参数：hp : p.IsPath；hadj : p.toSubgraph.Adj u v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.toSubgraph_adj_iff`：toSubgraph_adj_iff {u v u' v'} (w :
 G.Walk u v) : w.toSubgraph.Adj u' v' ↔ exists i, s(w.getVert i, w.getVert (i + 
1)) = s(u', v') ∧ i < w.l…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `SimpleGraph.Walk.IsPath.getVert_injOn`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → Set.InjOn p.getVert {i | i ≤ p.length}
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma snd_of_toSubgraph_adj {u v v'} {p : G.Walk u v} (hp : p.IsPath)
    (hadj : p.toSubgraph.Adj u v') : p.snd = v' := by
  have ⟨i, hi⟩ := p.toSubgraph_adj_iff.mp hadj
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hi
  rcases hi.1 with ⟨hl1, rfl⟩ | ⟨hr1, hr2⟩
  · have : i = 0 := by
      apply hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by rw [Set.mem_ofPred]; lia)
      rw [p.getVert_zero, hl1]
    simp [this]
  · have : i + 1 = 0 := by
      apply hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by rw [Set.mem_ofPred]; lia)
      rw [p.getVert_zero, hr2]
    contradiction

end IsPath

namespace IsCycle

/-
**SimpleGraph.Walk.IsCycle.neighborSet_toSubgraph_endpoint** 是 Mathlib 中的一个引理，位于
命名空间 `SimpleGraph.Walk.IsCycle`。
形式化陈述：neighborSet_toSubgraph_endpoint {u} {p : G.Walk u u} (hpc : p.IsCycle) : p
.toSubgraph.neighborSet u = {p.snd, p.penultimate}
参数：hpc : p.IsCycle。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.toSubgraph_adj_snd`：toSubgraph_adj_snd {u v} (w : G.Wal
k u v) (h : ¬ w.Nil) : w.toSubgraph.Adj u w.snd
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
-/
lemma neighborSet_toSubgraph_endpoint {u} {p : G.Walk u u} (hpc : p.IsCycle) :
    p.toSubgraph.neighborSet u = {p.snd, p.penultimate} := by
  have hadj1 := p.toSubgraph_adj_snd hpc.not_nil
  ext v
  simp_all only [Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
  grind [getVert_endpoint_iff, add_tsub_cancel_right]
/-
**SimpleGraph.Walk.IsCycle.neighborSet_toSubgraph_internal** 是 Mathlib 中的一个引理，位于
命名空间 `SimpleGraph.Walk.IsCycle`。
形式化陈述：neighborSet_toSubgraph_internal {u} {i : Nat} {p : G.Walk u u} (hpc : p.Is
Cycle) (h : i != 0) (h' : i < p.length) : p.toSubgraph.neighborSet (p.getVert i)
 = {p.getVert (i - 1), p.getVert (i + 1)}
参数：hpc : p.IsCycle；h : i != 0；h' : i < p.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {G' : 
G.Subgraph} {u v : V}, G'.Adj u v → G'.Adj v u
· 使用定理 `SimpleGraph.Walk.toSubgraph_adj_getVert`：toSubgraph_adj_getVert {u v} (w
 : G.Walk u v) {i : Nat} (hi : i < w.length) : w.toSubgraph.Adj (w.getVert i) (w
.getVert (i + 1))
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.Walk.IsCycle.getVert_injOn'`：∀ {V : Type u} {G : SimpleGraph
 V} {u : V} {p : G.Walk u u}, p.IsCycle → Set.InjOn p.getVert {i | i ≤ p.length 
- 1}
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `SimpleGraph.Walk.IsCycle.getVert_injOn`：∀ {V : Type u} {G : SimpleGraph 
V} {u : V} {p : G.Walk u u}, p.IsCycle → Set.InjOn p.getVert {i | 1 ≤ i ∧ i ≤ p.
length}
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma neighborSet_toSubgraph_internal {u} {i : ℕ} {p : G.Walk u u} (hpc : p.IsCycle)
    (h : i ≠ 0) (h' : i < p.length) :
    p.toSubgraph.neighborSet (p.getVert i) = {p.getVert (i - 1), p.getVert (i + 1)} := by
  have hadj1 := ((show i - 1 + 1 = i by lia) ▸
    p.toSubgraph_adj_getVert (by lia : (i - 1) < p.length)).symm
  ext v
  simp_all only [ne_eq, Subgraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    SimpleGraph.Walk.toSubgraph_adj_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
    Prod.swap_prod_mk]
  refine ⟨?_, by aesop⟩
  rintro ⟨i', ⟨hl1, hl2⟩ | ⟨hr1, hr2⟩⟩
  · apply hpc.getVert_injOn' (by rw [Set.mem_ofPred_eq]; lia)
      (by rw [Set.mem_ofPred_eq]; lia) at hl1
    simp_all
  · apply hpc.getVert_injOn (by rw [Set.mem_ofPred_eq]; lia)
      (by rw [Set.mem_ofPred_eq]; lia) at hr2
    aesop
/-
**SimpleGraph.Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two** 是 Mathlib 中的一个引
理，位于命名空间 `SimpleGraph.Walk.IsCycle`。
形式化陈述：ncard_neighborSet_toSubgraph_eq_two {u v} {p : G.Walk u u} (hpc : p.IsCycl
e) (h : v in p.support) : (p.toSubgraph.neighborSet v).ncard = 2
参数：hpc : p.IsCycle；h : v in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_length`：getVert_length {u v} (w : G.Walk u v) :
 w.getVert w.length = v
· 使用引理 `SimpleGraph.Walk.IsCycle.neighborSet_toSubgraph_endpoint`：neighborSet_to
Subgraph_endpoint {u} {p : G.Walk u u} (hpc : p.IsCycle) : p.toSubgraph.neighbor
Set u = {p.snd, p.penultimate}
· 使用定理 `Set.ncard_pair`：ncard_pair {a b : α} (h : a != b) : ({a, b} : Set α).nca
rd = 2
· 使用定理 `SimpleGraph.Walk.IsCycle.snd_ne_penultimate`：∀ {V : Type u} {G : SimpleG
raph V} {u : V} {p : G.Walk u u}, p.IsCycle → p.snd ≠ p.penultimate
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `SimpleGraph.Walk.IsCycle.neighborSet_toSubgraph_internal`：neighborSet_to
Subgraph_internal {u} {i : Nat} {p : G.Walk u u} (hpc : p.IsCycle) (h : i != 0) 
(h' : i < p.length) : p.toSubgraph.neighborSet…
· 使用定理 `SimpleGraph.Walk.IsCycle.getVert_sub_one_ne_getVert_add_one`：∀ {V : Type
 u} {G : SimpleGraph V} {u : V} {i : ℕ} {p : G.Walk u u},   p.IsCycle → i ≤ p.le
ngth → p.getVert (i - 1) ≠ p.getVert (i + 1)
-/
lemma ncard_neighborSet_toSubgraph_eq_two {u v} {p : G.Walk u u} (hpc : p.IsCycle)
    (h : v ∈ p.support) : (p.toSubgraph.neighborSet v).ncard = 2 := by
  simp only [SimpleGraph.Walk.mem_support_iff_exists_getVert] at h ⊢
  obtain ⟨i, hi⟩ := h
  by_cases! he : i = 0 ∨ i = p.length
  · have huv : u = v := by aesop
    rw [← huv, hpc.neighborSet_toSubgraph_endpoint]
    exact Set.ncard_pair hpc.snd_ne_penultimate
  rw [← hi.1, hpc.neighborSet_toSubgraph_internal he.1 (by lia)]
  exact Set.ncard_pair (hpc.getVert_sub_one_ne_getVert_add_one (by lia))
/-
**SimpleGraph.Walk.IsCycle.exists_isCycle_snd_verts_eq** 是 Mathlib 中的一个引理，位于命名空间
 `SimpleGraph.Walk.IsCycle`。
形式化陈述：exists_isCycle_snd_verts_eq {p : G.Walk v v} (h : p.IsCycle) (hadj : p.toS
ubgraph.Adj v w) : exists (p' : G.Walk v v), p'.IsCycle ∧ p'.snd = w ∧ p'.toSubg
raph.verts = p.toSubgraph.verts
参数：h : p.IsCycle；hadj : p.toSubgraph.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.IsCycle.neighborSet_toSubgraph_endpoint`：neighborSet_to
Subgraph_endpoint {u} {p : G.Walk u u} (hpc : p.IsCycle) : p.toSubgraph.neighbor
Set u = {p.snd, p.penultimate}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.IsCycle.reverse`：∀ {V : Type u} {G : SimpleGraph V} {u 
: V} {p : G.Walk u u}, p.IsCycle → p.reverse.IsCycle
· 使用定理 `SimpleGraph.Walk.getVert_reverse`：getVert_reverse {u v : V} (p : G.Walk 
u v) (i : Nat) : p.reverse.getVert i = p.getVert (p.length - i)
· 使用定理 `SimpleGraph.Walk.penultimate.eq_1`：∀ {V : Type u} {G : SimpleGraph V} {u
 v : V} (p : G.Walk u v), p.penultimate = p.getVert (p.length - 1)
· 使用定理 `SimpleGraph.Walk.toSubgraph_reverse`：toSubgraph_reverse (p : G.Walk u v)
 : p.reverse.toSubgraph = p.toSubgraph
-/
lemma exists_isCycle_snd_verts_eq {p : G.Walk v v} (h : p.IsCycle) (hadj : p.toSubgraph.Adj v w) :
    ∃ (p' : G.Walk v v), p'.IsCycle ∧ p'.snd = w ∧ p'.toSubgraph.verts = p.toSubgraph.verts := by
  have : w ∈ p.toSubgraph.neighborSet v := hadj
  rw [h.neighborSet_toSubgraph_endpoint] at this
  push _ ∈ _ at this
  obtain hl | hr := this
  · exact ⟨p, ⟨h, hl.symm, rfl⟩⟩
  · use p.reverse
    rw [penultimate, ← getVert_reverse] at hr
    exact ⟨h.reverse, hr.symm, by rw [toSubgraph_reverse _]⟩

end IsCycle

open Finset

variable [DecidableEq V] {u v : V} {p : G.Walk u v}

/-- This lemma states that given some finite set of vertices, of which at least one is in the
support of a given walk, one of them is the first to be encountered. This consequence is encoded
as the set of vertices, restricted to those in the support, except for the first, being empty.
You could interpret this as being `takeUntilSet`, but defining this is slightly involved due to
not knowing what the final vertex is. This could be done by defining a function to obtain the
first encountered vertex and then use that to define `takeUntilSet`. That direction could be
worthwhile if this concept is used more widely. -/
/-
**SimpleGraph.Walk.exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty**
 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty (s : Finset V)
 (h : {x in s | x in p.support}.Nonempty) : exists x in s, exists hx : x in p.su
pport, {t in s.erase x | t in (p.takeUntil x hx).support} = ∅
参数：s : Finset V；h : {x in s | x in p.support}.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `SimpleGraph.Walk.length_takeUntil_le_length`：length_takeUntil_le_length 
{u v w : V} (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).length <= 
p.length
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_erase_add_one`：card_erase_add_one : a in s -> #(s.erase a) +
 1 = #s
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
· 使用定理 `SimpleGraph.Walk.support_takeUntil_subset_support`：support_takeUntil_sub
set_support (p : G.Walk v w) (h : u in p.support) : (p.takeUntil u h).support su
bseteq p.support
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SimpleGraph.Walk.notMem_support_takeUntil_support_takeUntil_subset`：notM
em_support_takeUntil_support_takeUntil_subset {p : G.Walk u v} {x : V} (h : x !=
 w) (hw : w in p.support) (hx : x in (p.takeUntil w hw).…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.filter_erase`：filter_erase (a : α) (s : Finset α) : (s.erase a).f
ilter p = (s.filter p).erase a
· 使用定理 `Finset.erase_right_comm`：erase_right_comm {a b : α} {s : Finset α} : era
se (erase s a) b = erase (erase s b) a
· 使用引理 `SimpleGraph.Walk.takeUntil_takeUntil`：takeUntil_takeUntil {w x : V} (p :
 G.Walk u v) (hw : w in p.support) (hx : x in (p.takeUntil w hw).support) : (p.t
akeUntil w hw).takeUntil x…

--- 原说明 ---
This lemma states that given some finite set of vertices, of which at least one 
is in the
support of a given walk, one of them is the first to be encountered. This conseq
uence is encoded
as the set of vertices, restricted to those in the support, except for the first
, being empty.
You could interpret this as being `takeUntilSet`, but defining this is slightly 
involved due to
not knowing what the final vertex is. This could be done by defining a function 
to obtain the
first encountered vertex and then use that to define `takeUntilSet`. That direct
ion could be
worthwhile if this concept is used more widely.
-/
lemma exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty (s : Finset V)
    (h : {x ∈ s | x ∈ p.support}.Nonempty) :
    ∃ x ∈ s, ∃ hx : x ∈ p.support, {t ∈ s.erase x | t ∈ (p.takeUntil x hx).support} = ∅ := by
  simp only [← Finset.subset_empty]
  induction hp : p.length + #s using Nat.strong_induction_on generalizing s v with | _ n ih
  simp only [Finset.Nonempty, mem_filter] at h
  obtain ⟨x, hxs, hx⟩ := h
  obtain h | h := Finset.eq_empty_or_nonempty {t ∈ s.erase x | t ∈ (p.takeUntil x hx).support}
  · use x, hxs, hx, h.le
  have : (p.takeUntil x hx).length + #(s.erase x) < n := by
    rw [← card_erase_add_one hxs] at hp
    have := p.length_takeUntil_le_length hx
    lia
  obtain ⟨y, hys, hyp, h⟩ := ih _ this (s.erase x) h rfl
  use y, mem_of_mem_erase hys, support_takeUntil_subset_support p hx hyp
  rwa [takeUntil_takeUntil, erase_right_comm, filter_erase, erase_eq_of_notMem] at h
  simp only [mem_filter, mem_erase, ne_eq, not_and, and_imp]
  rintro hxy -
  exact notMem_support_takeUntil_support_takeUntil_subset (Ne.symm hxy) hx hyp
/-
**SimpleGraph.Walk.exists_mem_support_forall_mem_support_imp_eq** 是 Mathlib 中的一个
引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：exists_mem_support_forall_mem_support_imp_eq (s : Finset V) (h : {x in s |
 x in p.support}.Nonempty) : exists x in s, exists (hx : x in p.support), forall
 t in s, t in (p.takeUntil x hx).support -> t = x
参数：s : Finset V；h : {x in s | x in p.support}.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用引理 `SimpleGraph.Walk.exists_mem_support_mem_erase_mem_support_takeUntil_eq_e
mpty`：exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty (s : Finset V)
 (h : {x in s | x in p.support}.Nonempty) : exists x in s, exists …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.subset_insert_iff`：subset_insert_iff {a : α} {s t : Finset α} : s
 subseteq insert a t ↔ s.erase a subseteq t
· 使用定理 `Finset.subset_empty`：∀ {α : Type u_1} {s : Finset α}, s ⊆ ∅ ↔ s = ∅
· 使用定理 `Finset.filter_erase`：filter_erase (a : α) (s : Finset α) : (s.erase a).f
ilter p = (s.filter p).erase a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma exists_mem_support_forall_mem_support_imp_eq (s : Finset V)
    (h : {x ∈ s | x ∈ p.support}.Nonempty) :
    ∃ x ∈ s, ∃ (hx : x ∈ p.support),
      ∀ t ∈ s, t ∈ (p.takeUntil x hx).support → t = x := by
  obtain ⟨x, hxs, hx, h⟩ := p.exists_mem_support_mem_erase_mem_support_takeUntil_eq_empty s h
  use x, hxs, hx
  suffices {t ∈ s | t ∈ (p.takeUntil x hx).support} ⊆ {x} by simpa [Finset.subset_iff] using this
  rwa [Finset.filter_erase, ← Finset.subset_empty, ← Finset.subset_insert_iff,
    LawfulSingleton.insert_empty_eq] at h

end Walk

namespace Subgraph

/-
**SimpleGraph.Subgraph._root_.SimpleGraph.Walk.toSubgraph_connected** 是 Mathlib 
中的一个引理，位于命名空间 `SimpleGraph.Subgraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.SimpleGraph.Walk.toSubgraph_connected {u v : V} (p : G.Walk u v) :
    p.toSubgraph.Connected := by
  induction p with
  | nil => apply singletonSubgraph_connected
  | @cons _ w _ h p ih =>
    apply Subgraph.connected_sup (subgraphOfAdj_connected h).preconnected ih.preconnected
    exists w
    simp
/-
**SimpleGraph.Subgraph.induce_union_connected** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph.Subgraph`。
形式化陈述：induce_union_connected {H : G.Subgraph} {s t : Set V} (sconn : (H.induce s
).Preconnected) (tconn : (H.induce t).Preconnected) (sintert : (s ⊓ t).Nonempty)
 : (H.induce (s union t)).Connected
参数：sconn : (H.induce s).Preconnected；tconn : (H.induce t).Preconnected；sintert :
 (s ⊓ t).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.Connected.mono`：∀ {V : Type u} {G : SimpleGraph V} 
{H H' : G.Subgraph}, H ≤ H' → H.verts = H'.verts → H.Connected → H'.Connected
· 使用引理 `SimpleGraph.Subgraph.le_induce_union`：le_induce_union : G'.induce s ⊔ G'
.induce s' <= G'.induce (s union s')
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SimpleGraph.Subgraph.connected_sup`：connected_sup {H K : G.Subgraph} (hH
 : H.Preconnected) (hK : K.Preconnected) (hn : (H ⊓ K).verts.Nonempty) : (H ⊔ K)
.Connected
-/
lemma induce_union_connected {H : G.Subgraph} {s t : Set V}
    (sconn : (H.induce s).Preconnected) (tconn : (H.induce t).Preconnected)
    (sintert : (s ⊓ t).Nonempty) :
    (H.induce (s ∪ t)).Connected :=
  (Subgraph.connected_sup sconn tconn sintert).mono le_induce_union <| by simp
/-
**SimpleGraph.Subgraph.connected_induce_top_sup** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph.Subgraph`。
形式化陈述：connected_induce_top_sup {H K : G.Subgraph} (Hconn : H.Preconnected) (Kcon
n : K.Preconnected) {u v : V} (uH : u in H.verts) (vK : v in K.verts) (huv : G.A
dj u v) : ((⊤ : G.Subgraph).induce {u, v} ⊔ H ⊔ K).Connected
参数：Hconn : H.Preconnected；Kconn : K.Preconnected；uH : u in H.verts；vK : v in K.v
erts；huv : G.Adj u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Subgraph.connected_sup`：connected_sup {H K : G.Subgraph} (hH
 : H.Preconnected) (hK : K.Preconnected) (hn : (H ⊓ K).verts.Nonempty) : (H ⊔ K)
.Connected
· 使用定理 `SimpleGraph.Subgraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleG
raph V} {H : G.Subgraph}, H.Connected → H.Preconnected
· 使用引理 `SimpleGraph.Subgraph.top_induce_pair_connected_of_adj`：top_induce_pair_c
onnected_of_adj {u v : V} (huv : G.Adj u v) : ((⊤ : G.Subgraph).induce {u, v}).C
onnected
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma connected_induce_top_sup {H K : G.Subgraph} (Hconn : H.Preconnected) (Kconn : K.Preconnected)
    {u v : V} (uH : u ∈ H.verts) (vK : v ∈ K.verts) (huv : G.Adj u v) :
    ((⊤ : G.Subgraph).induce {u, v} ⊔ H ⊔ K).Connected := by
  refine Subgraph.connected_sup (Subgraph.connected_sup ?_ Hconn ?_).preconnected Kconn ?_
  · exact (top_induce_pair_connected_of_adj huv).preconnected
  · exact ⟨u, by simp [uH]⟩
  · exact ⟨v, by simp [vK]⟩

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.Subgraph.preconnected_iff_forall_exists_walk_subgraph** 是 Mathlib 
中的一个引理，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：preconnected_iff_forall_exists_walk_subgraph (H : G.Subgraph) : H.Preconne
cted ↔ forall {u v}, u in H.verts -> v in H.verts -> exists p : G.Walk u v, p.to
Subgraph <= H
参数：H : G.Subgraph。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.elim`：∀ {V : Type u} {G : SimpleGraph V} {p : Prop
} {u v : V}, G.Reachable u v → (∀ (a : G.Walk u v), p) → p
· 使用定理 `SimpleGraph.Subgraph.Preconnected.coe`：∀ {V : Type u} {G : SimpleGraph V
} {H : G.Subgraph}, H.Preconnected → H.coe.Preconnected
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.toSubgraph_map`：toSubgraph_map (f : G ->g G') (p : G.Wa
lk u v) : (p.map f).toSubgraph = p.toSubgraph.map f
· 使用定理 `SimpleGraph.Subgraph.preconnected_iff`：∀ {V : Type u} {G : SimpleGraph V
} {H : G.Subgraph}, H.Preconnected ↔ H.coe.Preconnected
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用引理 `SimpleGraph.Walk.start_mem_verts_toSubgraph`：start_mem_verts_toSubgraph 
(p : G.Walk u v) : u in p.toSubgraph.verts
· 使用引理 `SimpleGraph.Walk.end_mem_verts_toSubgraph`：end_mem_verts_toSubgraph (p :
 G.Walk u v) : v in p.toSubgraph.verts
· 使用定理 `SimpleGraph.Walk.toSubgraph_connected`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v), p.toSubgraph.Connected
-/
lemma preconnected_iff_forall_exists_walk_subgraph (H : G.Subgraph) :
    H.Preconnected ↔ ∀ {u v}, u ∈ H.verts → v ∈ H.verts → ∃ p : G.Walk u v, p.toSubgraph ≤ H := by
  constructor
  · intro hc u v hu hv
    refine (hc ⟨_, hu⟩ ⟨_, hv⟩).elim fun p => ?_
    exists p.map (Subgraph.hom _)
    simp [coeSubgraph_le]
  · intro hw
    rw [Subgraph.preconnected_iff]
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨p, h⟩ := hw hu hv
    exact Reachable.map (Subgraph.inclusion h)
      (p.toSubgraph_connected ⟨_, p.start_mem_verts_toSubgraph⟩ ⟨_, p.end_mem_verts_toSubgraph⟩)
/-
**SimpleGraph.Subgraph.connected_iff_forall_exists_walk_subgraph** 是 Mathlib 中的一
个引理，位于命名空间 `SimpleGraph.Subgraph`。
形式化陈述：connected_iff_forall_exists_walk_subgraph (H : G.Subgraph) : H.Connected ↔
 H.verts.Nonempty ∧ forall {u v}, u in H.verts -> v in H.verts -> exists p : G.W
alk u v, p.toSubgraph <= H
参数：H : G.Subgraph。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.connected_iff`：∀ {V : Type u} {G : SimpleGraph V} {
H : G.Subgraph}, H.Connected ↔ H.Preconnected ∧ H.verts.Nonempty
· 使用引理 `SimpleGraph.Subgraph.preconnected_iff_forall_exists_walk_subgraph`：preco
nnected_iff_forall_exists_walk_subgraph (H : G.Subgraph) : H.Preconnected ↔ fora
ll {u v}, u in H.verts -> v in H.verts -> exists p : G.…
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma connected_iff_forall_exists_walk_subgraph (H : G.Subgraph) :
    H.Connected ↔
      H.verts.Nonempty ∧
        ∀ {u v}, u ∈ H.verts → v ∈ H.verts → ∃ p : G.Walk u v, p.toSubgraph ≤ H := by
  rw [H.connected_iff, preconnected_iff_forall_exists_walk_subgraph, and_comm]

end Subgraph

section induced_subgraphs

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.preconnected_induce_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：preconnected_induce_iff {s : Set V} : (G.induce s).Preconnected ↔ ((⊤ : G.
Subgraph).induce s).Preconnected
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.induce_eq_coe_induce_top`：∀ {V : Type u} {G : SimpleGraph V}
 (s : Set V), SimpleGraph.induce s G = (⊤.induce s).coe
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Subgraph.preconnected_iff`：∀ {V : Type u} {G : SimpleGraph V
} {H : G.Subgraph}, H.Preconnected ↔ H.coe.Preconnected
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma preconnected_induce_iff {s : Set V} :
    (G.induce s).Preconnected ↔ ((⊤ : G.Subgraph).induce s).Preconnected := by
  rw [induce_eq_coe_induce_top, ← Subgraph.preconnected_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.connected_induce_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：connected_induce_iff {s : Set V} : (G.induce s).Connected ↔ ((⊤ : G.Subgra
ph).induce s).Connected
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.induce_eq_coe_induce_top`：∀ {V : Type u} {G : SimpleGraph V}
 (s : Set V), SimpleGraph.induce s G = (⊤.induce s).coe
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Subgraph.connected_iff'`：∀ {V : Type u} {G : SimpleGraph V} 
{H : G.Subgraph}, H.Connected ↔ H.coe.Connected
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma connected_induce_iff {s : Set V} :
    (G.induce s).Connected ↔ ((⊤ : G.Subgraph).induce s).Connected := by
  rw [induce_eq_coe_induce_top, ← Subgraph.connected_iff']
/-
**SimpleGraph.induce_union_connected** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：induce_union_connected {s t : Set V} (sconn : (G.induce s).Preconnected) (
tconn : (G.induce t).Preconnected) (sintert : (s inter t).Nonempty) : (G.induce 
(s union t)).Connected
参数：sconn : (G.induce s).Preconnected；tconn : (G.induce t).Preconnected；sintert :
 (s inter t).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.connected_induce_iff`：connected_induce_iff {s : Set V} : (G.
induce s).Connected ↔ ((⊤ : G.Subgraph).induce s).Connected
· 使用引理 `SimpleGraph.Subgraph.induce_union_connected`：induce_union_connected {H :
 G.Subgraph} {s t : Set V} (sconn : (H.induce s).Preconnected) (tconn : (H.induc
e t).Preconnected) (sintert : (s …
· 使用引理 `SimpleGraph.preconnected_induce_iff`：preconnected_induce_iff {s : Set V}
 : (G.induce s).Preconnected ↔ ((⊤ : G.Subgraph).induce s).Preconnected
-/
lemma induce_union_connected {s t : Set V}
    (sconn : (G.induce s).Preconnected) (tconn : (G.induce t).Preconnected)
    (sintert : (s ∩ t).Nonempty) :
    (G.induce (s ∪ t)).Connected := by
  rw [connected_induce_iff]
  rw [preconnected_induce_iff] at sconn tconn
  exact Subgraph.induce_union_connected sconn tconn sintert
/-
**SimpleGraph.induce_pair_connected_of_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h`。
形式化陈述：induce_pair_connected_of_adj {u v : V} (huv : G.Adj u v) : (G.induce {u, v
}).Connected
参数：huv : G.Adj u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.connected_induce_iff`：connected_induce_iff {s : Set V} : (G.
induce s).Connected ↔ ((⊤ : G.Subgraph).induce s).Connected
· 使用引理 `SimpleGraph.Subgraph.top_induce_pair_connected_of_adj`：top_induce_pair_c
onnected_of_adj {u v : V} (huv : G.Adj u v) : ((⊤ : G.Subgraph).induce {u, v}).C
onnected
-/
lemma induce_pair_connected_of_adj {u v : V} (huv : G.Adj u v) :
    (G.induce {u, v}).Connected := by
  rw [connected_induce_iff]
  exact Subgraph.top_induce_pair_connected_of_adj huv
/-
**SimpleGraph.Subgraph.Connected.induce_verts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Subgraph.Connected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}, H.Connected → (Simple
Graph.induce H.verts G).Connected
参数：SimpleGraph.induce H.verts G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.connected_induce_iff`：connected_induce_iff {s : Set V} : (G.
induce s).Connected ↔ ((⊤ : G.Subgraph).induce s).Connected
· 使用定理 `SimpleGraph.Subgraph.Connected.mono`：∀ {V : Type u} {G : SimpleGraph V} 
{H H' : G.Subgraph}, H ≤ H' → H.verts = H'.verts → H.Connected → H'.Connected
· 使用引理 `SimpleGraph.Subgraph.le_induce_top_verts`：le_induce_top_verts : G' <= (⊤
 : G.Subgraph).induce G'.verts
-/
lemma Subgraph.Connected.induce_verts {H : G.Subgraph} (h : H.Connected) :
    (G.induce H.verts).Connected := by
  rw [connected_induce_iff]
  exact h.mono le_induce_top_verts (by exact rfl)
/-
**SimpleGraph.Walk.connected_induce_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Walk u v), (SimpleGrap
h.induce {v_1 | v_1 ∈ p.support} G).Connected
参数：p : G.Walk u v；SimpleGraph.induce {v_1 | v_1 ∈ p.support} G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.verts_toSubgraph`：verts_toSubgraph (p : G.Walk u v) : p
.toSubgraph.verts = { w | w in p.support }
· 使用定理 `SimpleGraph.Subgraph.Connected.induce_verts`：∀ {V : Type u} {G : SimpleG
raph V} {H : G.Subgraph}, H.Connected → (SimpleGraph.induce H.verts G).Connected
· 使用定理 `SimpleGraph.Walk.toSubgraph_connected`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v), p.toSubgraph.Connected
-/
lemma Walk.connected_induce_support {u v : V} (p : G.Walk u v) :
    (G.induce {v | v ∈ p.support}).Connected := by
  rw [← p.verts_toSubgraph]
  exact p.toSubgraph_connected.induce_verts
/-
**SimpleGraph.connected_induce_union** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：connected_induce_union {v w : V} {s t : Set V} (sconn : (G.induce s).Preco
nnected) (tconn : (G.induce t).Preconnected) (hv : v in s) (hw : w in t) (ha : G
.Adj v w) : (G.induce (s union t)).Connected
参数：sconn : (G.induce s).Preconnected；tconn : (G.induce t).Preconnected；hv : v in
 s；hw : w in t；ha : G.Adj v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.connected_induce_iff`：connected_induce_iff {s : Set V} : (G.
induce s).Connected ↔ ((⊤ : G.Subgraph).induce s).Connected
· 使用定理 `SimpleGraph.Subgraph.Connected.mono`：∀ {V : Type u} {G : SimpleGraph V} 
{H H' : G.Subgraph}, H ≤ H' → H.verts = H'.verts → H.Connected → H'.Connected
· 使用引理 `SimpleGraph.Subgraph.connected_induce_top_sup`：connected_induce_top_sup 
{H K : G.Subgraph} (Hconn : H.Preconnected) (Kconn : K.Preconnected) {u v : V} (
uH : u in H.verts) (vK : v in K.ver…
· 使用引理 `SimpleGraph.preconnected_induce_iff`：preconnected_induce_iff {s : Set V}
 : (G.induce s).Preconnected ↔ ((⊤ : G.Subgraph).induce s).Preconnected
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Subgraph.subgraphOfAdj_eq_induce`：subgraphOfAdj_eq_induce {v
 w : V} (hvw : G.Adj v w) : G.subgraphOfAdj hvw = (⊤ : G.Subgraph).induce {v, w}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `SimpleGraph.subgraphOfAdj_le_of_adj`：subgraphOfAdj_le_of_adj {v w : V} (
H : G.Subgraph) (h : H.Adj v w) : G.subgraphOfAdj (H.adj_sub h) <= H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.Subgraph.induce_adj`：∀ {V : Type u} {G : SimpleGraph V} (G' 
: G.Subgraph) (s : Set V) (u v : V),   (G'.induce s).Adj u v = (u ∈ s ∧ v ∈ s ∧ 
G'.Adj u v)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `SimpleGraph.Subgraph.induce_verts`：∀ {V : Type u} {G : SimpleGraph V} (G
' : G.Subgraph) (s : Set V), (G'.induce s).verts = s
· 使用定理 `Set.union_assoc`：union_assoc (a b c : Set α) : a union b union c = a uni
on (b union c)
-/
lemma connected_induce_union {v w : V} {s t : Set V}
    (sconn : (G.induce s).Preconnected) (tconn : (G.induce t).Preconnected)
    (hv : v ∈ s) (hw : w ∈ t) (ha : G.Adj v w) :
    (G.induce (s ∪ t)).Connected := by
  rw [connected_induce_iff]
  rw [preconnected_induce_iff] at sconn tconn
  apply (Subgraph.connected_induce_top_sup sconn tconn hv hw ha).mono
  · simp only [sup_le_iff, Subgraph.le_induce_union_left,
      Subgraph.le_induce_union_right, and_true, ← Subgraph.subgraphOfAdj_eq_induce ha]
    apply subgraphOfAdj_le_of_adj
    simp [hv, hw, ha]
  · simp only [Subgraph.verts_sup, Subgraph.induce_verts]
    rw [Set.union_assoc]
    simp [Set.insert_subset_iff, Set.singleton_subset_iff, hv, hw]
/-
**SimpleGraph.induce_connected_of_patches** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
`。
形式化陈述：induce_connected_of_patches {s : Set V} (u : V) (hu : u in s) (patches : f
orall {v}, v in s -> exists s' subseteq s, exists (hu' : u in s') (hv' : v in s'
), (G.induce s').Reachable ⟨u, hu'⟩ ⟨v, hv'⟩) : (G.induce s).Connected
参数：u : V；hu : u in s；patches : forall {v}, v in s -> exists s' subseteq s, exist
s (hu' : u in s') (hv' : v in s'), (G.induce s').Reachable ⟨u, hu'⟩ ⟨v, hv'⟩。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.connected_iff_exists_forall_reachable`：connected_iff_exists_
forall_reachable : G.Connected ↔ exists v, forall w, G.Reachable v w
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
-/
lemma induce_connected_of_patches {s : Set V} (u : V) (hu : u ∈ s)
    (patches : ∀ {v}, v ∈ s → ∃ s' ⊆ s, ∃ (hu' : u ∈ s') (hv' : v ∈ s'),
                  (G.induce s').Reachable ⟨u, hu'⟩ ⟨v, hv'⟩) : (G.induce s).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨sv, svs, hu', hv', uv⟩ := patches hv
  exact uv.map (induceHomOfLE _ svs).toHom
/-
**SimpleGraph.induce_sUnion_connected_of_pairwise_not_disjoint** 是 Mathlib 中的一个引
理，位于命名空间 `SimpleGraph`。
形式化陈述：induce_sUnion_connected_of_pairwise_not_disjoint {S : Set (Set V)} (Sn : S
.Nonempty) (Snd : forall {s t}, s in S -> t in S -> (s inter t).Nonempty) (Sc : 
forall {s}, s in S -> (G.induce s).Connected) : (G.induce (⋃₀ S)).Connected
参数：Set V；Sn : S.Nonempty；Snd : forall {s t}, s in S -> t in S -> (s inter t).Non
empty；Sc : forall {s}, s in S -> (G.induce s).Connected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
· 使用引理 `SimpleGraph.induce_connected_of_patches`：induce_connected_of_patches {s 
: Set V} (u : V) (hu : u in s) (patches : forall {v}, v in s -> exists s' subset
eq s, exists (hu' : u in s') …
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用引理 `SimpleGraph.induce_union_connected`：induce_union_connected {s t : Set V}
 (sconn : (G.induce s).Preconnected) (tconn : (G.induce t).Preconnected) (sinter
t : (s inter t).Nonempty…
-/
lemma induce_sUnion_connected_of_pairwise_not_disjoint {S : Set (Set V)} (Sn : S.Nonempty)
    (Snd : ∀ {s t}, s ∈ S → t ∈ S → (s ∩ t).Nonempty)
    (Sc : ∀ {s}, s ∈ S → (G.induce s).Connected) :
    (G.induce (⋃₀ S)).Connected := by
  obtain ⟨s, sS⟩ := Sn
  obtain ⟨v, vs⟩ := (Sc sS).nonempty
  apply G.induce_connected_of_patches _ (Set.subset_sUnion_of_mem sS vs)
  rintro w hw
  simp only [Set.mem_sUnion] at hw
  obtain ⟨t, tS, wt⟩ := hw
  refine ⟨s ∪ t, Set.union_subset (Set.subset_sUnion_of_mem sS) (Set.subset_sUnion_of_mem tS),
          Or.inl vs, Or.inr wt,
          induce_union_connected (Sc sS).preconnected (Sc tS).preconnected (Snd sS tS) _ _⟩
/-
**SimpleGraph.extend_finset_to_connected** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：extend_finset_to_connected (Gpc : G.Preconnected) {t : Finset V} (tn : t.N
onempty) : exists (t' : Finset V), t subseteq t' ∧ (G.induce (t' : Set V)).Conne
cted
参数：Gpc : G.Preconnected；tn : t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Walk.end_mem_support`：end_mem_support {u v : V} (p : G.Walk 
u v) : v in p.support
· 使用引理 `SimpleGraph.induce_connected_of_patches`：induce_connected_of_patches {s 
: Set V} (u : V) (hu : u in s) (patches : forall {v}, v in s -> exists s' subset
eq s, exists (hu' : u in s') …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `SimpleGraph.Walk.connected_induce_support`：∀ {V : Type u} {G : SimpleGra
ph V} {u v : V} (p : G.Walk u v), (SimpleGraph.induce {v_1 | v_1 ∈ p.support} G)
.Connected
-/
lemma extend_finset_to_connected (Gpc : G.Preconnected) {t : Finset V} (tn : t.Nonempty) :
    ∃ (t' : Finset V), t ⊆ t' ∧ (G.induce (t' : Set V)).Connected := by
  classical
  obtain ⟨u, ut⟩ := tn
  refine ⟨t.biUnion (fun v => (Gpc u v).some.support.toFinset), fun v vt => ?_, ?_⟩
  · simp only [Finset.mem_biUnion, List.mem_toFinset]
    exact ⟨v, vt, Walk.end_mem_support _⟩
  · apply G.induce_connected_of_patches u
    · simp only [Finset.coe_biUnion, Finset.mem_coe, List.coe_toFinset, Set.mem_iUnion,
                 Set.mem_ofPred_eq, Walk.start_mem_support, exists_prop, and_true]
      exact ⟨u, ut⟩
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_biUnion, List.mem_toFinset] at hv
    obtain ⟨w, wt, hw⟩ := hv
    refine ⟨{x | x ∈ (Gpc u w).some.support}, ?_, ?_⟩
    · simp only [Finset.coe_biUnion, Finset.mem_coe, List.coe_toFinset]
      exact fun x xw => Set.mem_iUnion₂.mpr ⟨w, wt, xw⟩
    · simp only [Set.mem_ofPred_eq, Walk.start_mem_support, exists_true_left]
      refine ⟨hw, Walk.connected_induce_support _ _ _⟩

end induced_subgraphs

/-
**SimpleGraph.Reachable.coe_toSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Re
achable`。
形式化陈述：∀ {V : Type u} {G H : SimpleGraph V} {u v : V} (h : H ≤ G),   H.Reachable 
u v → (SimpleGraph.toSubgraph H h).coe.Reachable ⟨u, trivial⟩ ⟨v, trivial⟩
参数：h : H ≤ G；SimpleGraph.toSubgraph H h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用定理 `trivial`：True
-/
protected lemma Reachable.coe_toSubgraph {H : SimpleGraph V} {u v : V} (h : H ≤ G)
    (hreachable : H.Reachable u v) :
    (toSubgraph H h).coe.Reachable ⟨u, trivial⟩ ⟨v, trivial⟩ :=
  hreachable.map ⟨((toSubgraph H h).vert · _), (·)⟩
/-
**SimpleGraph.Preconnected.toSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Pre
connected`。
形式化陈述：∀ {V : Type u} {G H : SimpleGraph V} (h : H ≤ G), H.Preconnected → (Simple
Graph.toSubgraph H h).Preconnected
参数：h : H ≤ G；SimpleGraph.toSubgraph H h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Subgraph.preconnected_iff`：∀ {V : Type u} {G : SimpleGraph V
} {H : G.Subgraph}, H.Preconnected ↔ H.coe.Preconnected
· 使用定理 `SimpleGraph.Reachable.coe_toSubgraph`：∀ {V : Type u} {G H : SimpleGraph 
V} {u v : V} (h : H ≤ G),   H.Reachable u v → (SimpleGraph.toSubgraph H h).coe.R
eachable ⟨u, trivial⟩ ⟨v, …
-/
protected lemma Preconnected.toSubgraph {H : SimpleGraph V} (h : H ≤ G)
    (hpreconn : H.Preconnected) : (toSubgraph H h).Preconnected :=
  Subgraph.preconnected_iff.mpr (fun u v ↦ (hpreconn u v).coe_toSubgraph h)
/-
**SimpleGraph.Connected.toSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Connec
ted`。
形式化陈述：∀ {V : Type u} {G H : SimpleGraph V} (h : H ≤ G), H.Connected → (SimpleGra
ph.toSubgraph H h).Connected
参数：h : H ≤ G；SimpleGraph.toSubgraph H h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Subgraph.connected_iff`：∀ {V : Type u} {G : SimpleGraph V} {
H : G.Subgraph}, H.Connected ↔ H.Preconnected ∧ H.verts.Nonempty
· 使用定理 `SimpleGraph.Preconnected.toSubgraph`：∀ {V : Type u} {G H : SimpleGraph V
} (h : H ≤ G), H.Preconnected → (SimpleGraph.toSubgraph H h).Preconnected
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.toSubgraph_verts`：∀ {V : Type u} {G : SimpleGraph V} (H : Si
mpleGraph V) (h : H ≤ G), (SimpleGraph.toSubgraph H h).verts = Set.univ
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
-/
protected lemma Connected.toSubgraph {H : SimpleGraph V} (h : H ≤ G) (hconn : H.Connected) :
    (toSubgraph H h).Connected :=
  Subgraph.connected_iff.mpr ⟨hconn.preconnected.toSubgraph h, by simp [hconn.nonempty]⟩
/-
**SimpleGraph.Reachable.coe_subgraphMap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.R
eachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph} {G'' : G'.coe.Subgrap
h} (f : G'.coe →g G) {u v : ↑G''.verts},   G''.coe.Reachable u v → (SimpleGraph.
Subgraph.map f G'').coe.Reachable ⟨f ↑u, ⋯⟩ ⟨f ↑v, ⋯⟩
参数：f : G'.coe →g G；SimpleGraph.Subgraph.map f G''。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.map`：∀ {V : Type u} {V' : Type v} {u v : V} {G : S
impleGraph V} {G' : SimpleGraph V'} (f : G →g G'),   G.Reachable u v → G'.Reacha
ble (f u) (f v)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Relation.map_apply`：map_apply : Relation.Map r f g c d ↔ exists a b, r a
 b ∧ f a = c ∧ g b = d
-/
protected lemma Reachable.coe_subgraphMap {G' : G.Subgraph} {G'' : G'.coe.Subgraph}
    (f : G'.coe →g G) {u v : G''.verts} (hreachable : G''.coe.Reachable u v) :
    (G''.map f).coe.Reachable ⟨f u, Set.mem_image_of_mem _ u.prop⟩
      ⟨f v, Set.mem_image_of_mem _ v.prop⟩ :=
  hreachable.map {
    toFun v := (G''.map f).vert _ (Set.mem_image_of_mem f v.prop)
    map_rel' r := Relation.map_apply.mpr (by tauto)
  }
/-
**SimpleGraph.Reachable.coe_coeSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.R
eachable`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph} (G'' : G'.coe.Subgrap
h) {u v : ↑G''.verts},   G''.coe.Reachable u v →     (SimpleGraph.Subgraph.coeSu
bgraph G'').coe.Reachable ((SimpleGraph.Subgraph.coeSubgraph G'').vert ↑↑u ⋯)   
    ((SimpleGraph.Subgraph.coeSubgraph G'').vert ↑↑v ⋯)
参数：G'' : G'.coe.Subgraph；SimpleGraph.Subgraph.coeSubgraph G''；(SimpleGraph.Subgr
aph.coeSubgraph G'').vert ↑↑u ⋯；(SimpleGraph.Subgraph.coeSubgraph G'').vert ↑↑v 
⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.coe_subgraphMap`：∀ {V : Type u} {G : SimpleGraph V
} {G' : G.Subgraph} {G'' : G'.coe.Subgraph} (f : G'.coe →g G) {u v : ↑G''.verts}
,   G''.coe.Reachable u v →…
-/
protected lemma Reachable.coe_coeSubgraph {G' : G.Subgraph} (G'' : G'.coe.Subgraph)
    {u v : G''.verts} (hreachable : G''.coe.Reachable u v) :
    (Subgraph.coeSubgraph G'').coe.Reachable (Subgraph.vert _ u (by simp_all))
      (Subgraph.vert _ v (by simp_all)) :=
  hreachable.coe_subgraphMap G'.hom

namespace Subgraph

/-
**SimpleGraph.Subgraph.Preconnected.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.S
ubgraph.Preconnected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph} {G'' : G'.coe.Subgrap
h} (f : G'.coe →g G),   G''.Preconnected → (SimpleGraph.Subgraph.map f G'').Prec
onnected
参数：f : G'.coe →g G；SimpleGraph.Subgraph.map f G''。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.preconnected_iff`：∀ {V : Type u} {G : SimpleGraph V
} {H : G.Subgraph}, H.Preconnected ↔ H.coe.Preconnected
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `SimpleGraph.Reachable.coe_subgraphMap`：∀ {V : Type u} {G : SimpleGraph V
} {G' : G.Subgraph} {G'' : G'.coe.Subgraph} (f : G'.coe →g G) {u v : ↑G''.verts}
,   G''.coe.Reachable u v →…
· 使用定理 `SimpleGraph.Subgraph.Preconnected.coe`：∀ {V : Type u} {G : SimpleGraph V
} {H : G.Subgraph}, H.Preconnected → H.coe.Preconnected
-/
protected lemma Preconnected.map {G' : G.Subgraph} {G'' : G'.coe.Subgraph}
    (f : G'.coe →g G) (hpreconn : G''.Preconnected) : (G''.map f).Preconnected := by
  rw [Subgraph.preconnected_iff]
  intro ⟨u', u, hu, hfu⟩ ⟨v', v, hv, hfv⟩
  simp_rw [← hfu, ← hfv]
  exact (hpreconn.coe ⟨u, hu⟩ ⟨v, hv⟩).coe_subgraphMap f
/-
**SimpleGraph.Subgraph.Connected.map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Subg
raph.Connected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph} {G'' : G'.coe.Subgrap
h} (f : G'.coe →g G),   G''.Connected → (SimpleGraph.Subgraph.map f G'').Connect
ed
参数：f : G'.coe →g G；SimpleGraph.Subgraph.map f G''。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Subgraph.connected_iff`：∀ {V : Type u} {G : SimpleGraph V} {
H : G.Subgraph}, H.Connected ↔ H.Preconnected ∧ H.verts.Nonempty
· 使用定理 `SimpleGraph.Subgraph.Preconnected.map`：∀ {V : Type u} {G : SimpleGraph V
} {G' : G.Subgraph} {G'' : G'.coe.Subgraph} (f : G'.coe →g G),   G''.Preconnecte
d → (SimpleGraph.Subgraph.m…
· 使用定理 `SimpleGraph.Subgraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleG
raph V} {H : G.Subgraph}, H.Connected → H.Preconnected
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Subgraph.map_verts`：∀ {V : Type u} {W : Type v} {G : SimpleG
raph V} {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph),   (SimpleGraph.Subg
raph.map f H).verts …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SimpleGraph.Subgraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph
 V} {H : G.Subgraph}, H.Connected → H.verts.Nonempty
-/
protected lemma Connected.map {G' : G.Subgraph} {G'' : G'.coe.Subgraph}
    (f : G'.coe →g G) (hconn : G''.Connected) : (G''.map f).Connected :=
  Subgraph.connected_iff.mpr ⟨hconn.preconnected.map f, by simp [hconn.nonempty]⟩
/-
**SimpleGraph.Subgraph.Preconnected.coeSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Subgraph.Preconnected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph} (G'' : G'.coe.Subgrap
h),   G''.Preconnected → (SimpleGraph.Subgraph.coeSubgraph G'').Preconnected
参数：G'' : G'.coe.Subgraph；SimpleGraph.Subgraph.coeSubgraph G''。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.Preconnected.map`：∀ {V : Type u} {G : SimpleGraph V
} {G' : G.Subgraph} {G'' : G'.coe.Subgraph} (f : G'.coe →g G),   G''.Preconnecte
d → (SimpleGraph.Subgraph.m…
-/
protected lemma Preconnected.coeSubgraph {G' : G.Subgraph} (G'' : G'.coe.Subgraph)
    (hpreconn : G''.Preconnected) : (Subgraph.coeSubgraph G'').Preconnected :=
  hpreconn.map G'.hom
/-
**SimpleGraph.Subgraph.Connected.coeSubgraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Subgraph.Connected`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {G' : G.Subgraph} (G'' : G'.coe.Subgrap
h),   G''.Connected → (SimpleGraph.Subgraph.coeSubgraph G'').Connected
参数：G'' : G'.coe.Subgraph；SimpleGraph.Subgraph.coeSubgraph G''。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Subgraph.Connected.map`：∀ {V : Type u} {G : SimpleGraph V} {
G' : G.Subgraph} {G'' : G'.coe.Subgraph} (f : G'.coe →g G),   G''.Connected → (S
impleGraph.Subgraph.map …
-/
protected lemma Connected.coeSubgraph {G' : G.Subgraph} (G'' : G'.coe.Subgraph)
    (hconn : G''.Connected) : (Subgraph.coeSubgraph G'').Connected :=
  hconn.map G'.hom

end Subgraph

end SimpleGraph

