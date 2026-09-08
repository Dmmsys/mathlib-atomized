/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon, Peter Nelson
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Simple graphs

This file defines two type classes for graphs `Graph α β`: `Loopless` and `Simple`.

## Main definitions
- `Loopless`: a graph is loopless if it has no loops
- `Simple`: a graph is simple if it has no multiple edges between the same pair of vertices
- `toSimpleGraph`: a function that constructs a `SimpleGraph V(G)` from a Graph `G`
- `ofSimpleGraph`: a function that constructs a `Graph α (Sym2 α)` from a `SimpleGraph α`

TODO: Show `ofSimpleGraph (toSimpleGraph G)` is isomorphic to `G` when isomorphism on `Graph` is
defined.
-/

public section

variable {α β : Type*} {G H : Graph α β} {u v : α} {e f : β} {X Y : Set α}

open Set SimpleGraph

namespace Graph

section Loopless

/-- A loopless graph is one where the ends of every edge are distinct. -/
@[mk_iff]
/-
**Graph.Loopless** 是 Mathlib 中的一个归纳类型，位于命名空间 `Graph`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Graph α β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A loopless graph is one where the ends of every edge are distinct.
-/
protected class Loopless (G : Graph α β) : Prop where
  not_isLoopAt : ∀ e x, ¬ G.IsLoopAt e x

@[simp]
/-
**Graph.not_isLoopAt** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：not_isLoopAt (G : Graph α β) [G.Loopless] (e : β) (x : α) : ¬ G.IsLoopAt e
 x
参数：G : Graph α β；e : β；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Loopless.not_isLoopAt`：∀ {α : Type u_1} {β : Type u_2} {G : Graph 
α β} [self : G.Loopless] (e : β) (x : α), ¬G.IsLoopAt e x
-/
lemma not_isLoopAt (G : Graph α β) [G.Loopless] (e : β) (x : α) : ¬ G.IsLoopAt e x :=
  Loopless.not_isLoopAt e x
/-
**Graph.not_adj_self** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：not_adj_self (G : Graph α β) [G.Loopless] (x : α) : ¬ G.Adj x x
参数：G : Graph α β；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Loopless.not_isLoopAt`：∀ {α : Type u_1} {β : Type u_2} {G : Graph 
α β} [self : G.Loopless] (e : β) (x : α), ¬G.IsLoopAt e x
-/
lemma not_adj_self (G : Graph α β) [G.Loopless] (x : α) : ¬ G.Adj x x :=
  fun ⟨e, he⟩ ↦ Loopless.not_isLoopAt e x he
/-
**Graph.Adj.ne** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Adj`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β} {u v : α} [G.Loopless], G.
Adj u v → u ≠ v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Graph.not_adj_self`：not_adj_self (G : Graph α β) [G.Loopless] (x : α) : 
¬ G.Adj x x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Adj.ne [G.Loopless] (hxy : G.Adj u v) : u ≠ v := fun h ↦ G.not_adj_self u <| h ▸ hxy
/-
**Graph.IsLink.ne** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β} {u v : α} {e : β} [G.Loopl
ess], G.IsLink e u v → u ≠ v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Adj.ne`：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β} {u v : α} 
[G.Loopless], G.Adj u v → u ≠ v
-/
lemma IsLink.ne [G.Loopless] (he : G.IsLink e u v) : u ≠ v := Adj.ne ⟨e, he⟩
/-
**Graph.loopless_iff_forall_ne_of_adj** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：loopless_iff_forall_ne_of_adj : G.Loopless ↔ forall u v, G.Adj u v -> u !=
 v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Adj.ne`：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β} {u v : α} 
[G.Loopless], G.Adj u v → u ≠ v
· 使用定理 `Graph.IsLink.adj`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G :
 Graph α β}, G.IsLink e x y → G.Adj x y
-/
lemma loopless_iff_forall_ne_of_adj : G.Loopless ↔ ∀ u v, G.Adj u v → u ≠ v :=
  ⟨fun _ _ _ h ↦ h.ne, fun h ↦ ⟨fun _ x hex ↦ h x x hex.adj rfl⟩⟩
/-
**Graph.vertexSet_nontrivial_of_edgeSet_nonempty_of_loopless** 是 Mathlib 中的一个引理，
位于命名空间 `Graph`。
形式化陈述：vertexSet_nontrivial_of_edgeSet_nonempty_of_loopless [G.Loopless] (hE : E(
G).Nonempty) : V(G).Nontrivial
参数：hE : E(G).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Graph.exists_isLink_of_mem_edgeSet`：exists_isLink_of_mem_edgeSet (h : e 
in E(G)) : exists x y, G.IsLink e x y
· 使用定理 `Graph.IsLink.left_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β}
 {G : Graph α β}, G.IsLink e x y → x ∈ G.vertexSet
· 使用定理 `Graph.IsLink.right_mem`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β
} {G : Graph α β}, G.IsLink e x y → y ∈ G.vertexSet
· 使用定理 `Graph.Adj.ne`：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β} {u v : α} 
[G.Loopless], G.Adj u v → u ≠ v
· 使用定理 `Graph.IsLink.adj`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G :
 Graph α β}, G.IsLink e x y → G.Adj x y
-/
lemma vertexSet_nontrivial_of_edgeSet_nonempty_of_loopless [G.Loopless] (hE : E(G).Nonempty) :
    V(G).Nontrivial := by
  obtain ⟨e, he⟩ := hE
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨x, hxy.left_mem, y, hxy.right_mem, hxy.adj.ne⟩
/-
**Graph.Loopless.anti** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Loopless`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β} [hG : G.Loopless], H ≤ G
 → H.Loopless
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Graph.loopless_iff_forall_ne_of_adj`：loopless_iff_forall_ne_of_adj : G.L
oopless ↔ forall u v, G.Adj u v -> u != v
· 使用定理 `Graph.Adj.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {G H : Graph α
 β}, H ≤ G → H.Adj x y → G.Adj x y
-/
lemma Loopless.anti [hG : G.Loopless] (hle : H ≤ G) : H.Loopless := by
  rw [loopless_iff_forall_ne_of_adj] at hG ⊢
  exact fun x y hxy ↦ hG x y <| hxy.mono hle

@[simp]
/-
**Graph.Inc.isNonloopAt** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Inc`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β} {u : α} {e : β} [G.Looples
s], G.Inc e u → G.IsNonloopAt e u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Graph.Inc.isLoopAt_or_isNonloopAt`：∀ {α : Type u_1} {β : Type u_2} {x : 
α} {e : β} {G : Graph α β}, G.Inc e x → G.IsLoopAt e x ∨ G.IsNonloopAt e x
· 使用定理 `Graph.Loopless.not_isLoopAt`：∀ {α : Type u_1} {β : Type u_2} {G : Graph 
α β} [self : G.Loopless] (e : β) (x : α), ¬G.IsLoopAt e x
-/
lemma Inc.isNonloopAt [G.Loopless] (h : G.Inc e u) : G.IsNonloopAt e u :=
  h.isLoopAt_or_isNonloopAt.resolve_left (Loopless.not_isLoopAt _ _)

end Loopless

section Simple

/-- A `Simple` graph is a `Loopless` graph where no pair of vertices are the ends of more than one
edge. -/
@[mk_iff]
/-
**Graph.Simple** 是 Mathlib 中的一个归纳类型，位于命名空间 `Graph`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → Graph α β → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Simple` graph is a `Loopless` graph where no pair of vertices are the ends of
 more than one
edge.
-/
class Simple (G : Graph α β) : Prop extends G.Loopless where
  eq_of_isLink : ∀ ⦃e f x y⦄, G.IsLink e x y → G.IsLink f x y → e = f

variable [G.Simple]
/-
**Graph.IsLink.eq** 是 Mathlib 中的一个定理，位于命名空间 `Graph.IsLink`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β} {u v : α} {e f : β} [G.Sim
ple], G.IsLink e u v → G.IsLink f u v → e = f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Graph.Simple.eq_of_isLink`：∀ {α : Type u_1} {β : Type u_2} {G : Graph α 
β} [self : G.Simple] ⦃e f : β⦄ ⦃x y : α⦄,   G.IsLink e x y → G.IsLink f x y → e 
= f
-/
lemma IsLink.eq (h : G.IsLink e u v) (h' : G.IsLink f u v) : e = f :=
  Simple.eq_of_isLink h h'
/-
**Graph.Simple.anti** 是 Mathlib 中的一个定理，位于命名空间 `Graph.Simple`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β} [G.Simple], H ≤ G → H.Si
mple
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Graph.Loopless.anti`：∀ {α : Type u_1} {β : Type u_2} {G H : Graph α β} [
hG : G.Loopless], H ≤ G → H.Loopless
· 使用定理 `Graph.Simple.toLoopless`：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β}
 [self : G.Simple], G.Loopless
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Graph.IsLink.eq`：∀ {α : Type u_1} {β : Type u_2} {G : Graph α β} {u v : 
α} {e f : β} [G.Simple], G.IsLink e u v → G.IsLink f u v → e = f
· 使用定理 `Graph.IsLink.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {e : β} {G 
H : Graph α β}, H ≤ G → H.IsLink e x y → G.IsLink e x y
-/
lemma Simple.anti (hle : H ≤ G) : H.Simple where
  not_isLoopAt e x := by simp [toLoopless.anti hle]
  eq_of_isLink e f x y he hf := (he.mono hle).eq (hf.mono hle)
/-
**Graph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : Set α) : (Graph.noEdge V β).Simple where
  not_isLoopAt := by simp [IsLoopAt]
  eq_of_isLink := by simp
/-
**Graph.** 是 Mathlib 中的一个实例，位于命名空间 `Graph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (⊥ : Graph α β).Simple := inferInstanceAs (Graph.noEdge _ β).Simple

end Simple

section toSimpleGraph

/-- Construct a simple graph from a graph. -/
@[expose, simps (attr := grind =)]
/-
**Graph.toSimpleGraph** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：toSimpleGraph (G : Graph α β) : SimpleGraph V(G) where Adj u v
参数：G : Graph α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a simple graph from a graph.
-/
def toSimpleGraph (G : Graph α β) : SimpleGraph V(G) where
  Adj u v := u ≠ v ∧ G.Adj u v
  symm := ⟨fun u v ↦ by grind [adj_comm]⟩
/-
**Graph.toSimpleGraph_adj_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：toSimpleGraph_adj_iff [G.Loopless] (u v : V(G)) : G.toSimpleGraph.Adj u v 
↔ G.Adj u v
参数：u v : V(G)。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSimpleGraph_adj_iff [G.Loopless] (u v : V(G)) : G.toSimpleGraph.Adj u v ↔ G.Adj u v := by
  grind [Adj.ne]
/-
**Graph.toSimpleGraph_mono** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：toSimpleGraph_mono (h : G <=s H) : G.toSimpleGraph <= h.vertexSet_eq ▸ H.t
oSimpleGraph
参数：h : G <=s H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Graph.IsSpanningSubgraph.vertexSet_eq`：∀ {α : Type u_1} {β : Type u_2} {
H G : Graph α β}, H ≤s G → H.vertexSet = G.vertexSet
· 使用定理 `Graph.toSimpleGraph_adj`：∀ {α : Type u_1} {β : Type u_2} (G : Graph α β)
 (u v : ↑G.vertexSet), G.toSimpleGraph.Adj u v = (u ≠ v ∧ G.Adj ↑u ↑v)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Graph.Adj.mono`：∀ {α : Type u_1} {β : Type u_2} {x y : α} {G H : Graph α
 β}, H ≤ G → H.Adj x y → G.Adj x y
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma toSimpleGraph_mono (h : G ≤s H) : G.toSimpleGraph ≤ h.vertexSet_eq ▸ H.toSimpleGraph := by
  rintro u v hadj
  match G, H with
  | ⟨GV, GL, GE, _, _, _, _⟩, ⟨HV, HL, HE, _, _, _, _⟩ =>
    obtain ⟨hne, hadj⟩ := toSimpleGraph_adj .. ▸ hadj
    obtain ⟨hle, h⟩ := h
    simp only at h
    subst GV
    simp [toSimpleGraph_adj, hne, hadj.mono hle]

/-- Construct a graph from a simple graph. It has every element of the vertex type as a vertex. -/
@[expose, simps (attr := grind =)]
/-
**Graph.ofSimpleGraph** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：ofSimpleGraph (G : SimpleGraph α) : Graph α (Sym2 α) where vertexSet
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a graph from a simple graph. It has every element of the vertex type a
s a vertex.
-/
def ofSimpleGraph (G : SimpleGraph α) : Graph α (Sym2 α) where
  vertexSet := Set.univ
  edgeSet := G.edgeSet
  IsLink e x y := e = s(x, y) ∧ e ∈ G.edgeSet
  isLink_symm e he := ⟨fun u v ↦ by simp [Sym2.eq_swap]⟩
  eq_or_eq_of_isLink_of_isLink e u v x y he hf := by grind
  edge_mem_iff_exists_isLink e := by induction e with | h u v => grind

@[simp]
/-
**Graph.ofSimpleGraph_adj_iff** 是 Mathlib 中的一个引理，位于命名空间 `Graph`。
形式化陈述：ofSimpleGraph_adj_iff {G : SimpleGraph α} (u v : α) : (ofSimpleGraph G).Ad
j u v ↔ G.Adj u v
参数：u v : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Graph.ofSimpleGraph_isLink`：∀ {α : Type u_1} (G : SimpleGraph α) (e : Sy
m2 α) (x y : α),   (Graph.ofSimpleGraph G).IsLink e x y = (e = s(x, y) ∧ e ∈ G.e
dgeSet)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ofSimpleGraph_adj_iff {G : SimpleGraph α} (u v : α) :
    (ofSimpleGraph G).Adj u v ↔ G.Adj u v := by simp [Adj]

/-- The isomorphism between `toSimpleGraph (ofSimpleGraph G)` and `G`. -/
/-
**Graph.toSimpleGraphOfSimpleGraphIso** 是 Mathlib 中的一个定义，位于命名空间 `Graph`。
形式化陈述：toSimpleGraphOfSimpleGraphIso (G : SimpleGraph α) : (toSimpleGraph (ofSimp
leGraph G)) ≃g G
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `toSimpleGraph (ofSimpleGraph G)` and `G`.
-/
def toSimpleGraphOfSimpleGraphIso (G : SimpleGraph α) :
    (toSimpleGraph (ofSimpleGraph G)) ≃g G := by
  use Equiv.Set.univ α
  refine ⟨fun h ↦ ⟨fun h' ↦ h.ne (congrArg Subtype.val h'), ?_⟩, fun ⟨_, h⟩ ↦ ?_⟩ <;>
    revert h <;> rw [ofSimpleGraph_adj_iff] <;> exact id

end toSimpleGraph

end Graph

