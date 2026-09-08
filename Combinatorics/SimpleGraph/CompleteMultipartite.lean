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

/-- `G` is `IsCompleteMultipartite` iff non-adjacency is transitive -/
/-
**SimpleGraph.IsCompleteMultipartite** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsCompleteMultipartite (G : SimpleGraph α) : Prop
参数：G : SimpleGraph α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G` is `IsCompleteMultipartite` iff non-adjacency is transitive
-/
def IsCompleteMultipartite (G : SimpleGraph α) : Prop := IsTrans α (¬ G.Adj · ·)
/-
**SimpleGraph.bot_isCompleteMultipartite** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：bot_isCompleteMultipartite : (⊥ : SimpleGraph α).IsCompleteMultipartite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bot_isCompleteMultipartite : (⊥ : SimpleGraph α).IsCompleteMultipartite :=
  ⟨by simp⟩
/-
**SimpleGraph.IsCompleteMultipartite.induce** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.IsCompleteMultipartite`。
形式化陈述：∀ {α : Type u} {G : SimpleGraph α} {s : Set α},   G.IsCompleteMultipartite
 → (SimpleGraph.induce s G).IsCompleteMultipartite
参数：SimpleGraph.induce s G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
-/
protected lemma IsCompleteMultipartite.induce (hG : G.IsCompleteMultipartite) :
    (G.induce s).IsCompleteMultipartite where trans _u _v _w := hG.trans _ _ _

/-- The setoid given by non-adjacency -/
@[instance_reducible]
/-
**SimpleGraph.IsCompleteMultipartite.setoid** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGra
ph.IsCompleteMultipartite`。
形式化陈述：{α : Type u} → {G : SimpleGraph α} → G.IsCompleteMultipartite → Setoid α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid given by non-adjacency
-/
def IsCompleteMultipartite.setoid (h : G.IsCompleteMultipartite) : Setoid α :=
    ⟨(¬ G.Adj · ·), ⟨G.loopless.irrefl, fun h' ↦ by rwa [adj_comm] at h', h.trans _ _ _⟩⟩
/-
**SimpleGraph.completeMultipartiteGraph.isCompleteMultipartite** 是 Mathlib 中的一个定
理，位于命名空间 `SimpleGraph.completeMultipartiteGraph`。
形式化陈述：∀ {ι : Type u_1} (V : ι → Type u_2), (SimpleGraph.completeMultipartiteGrap
h V).IsCompleteMultipartite
参数：V : ι → Type u_2；SimpleGraph.completeMultipartiteGraph V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma completeMultipartiteGraph.isCompleteMultipartite {ι : Type*} (V : ι → Type*) :
    (completeMultipartiteGraph V).IsCompleteMultipartite :=
  ⟨by simp_all⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The graph isomorphism from a graph `G` that `IsCompleteMultipartite` to the corresponding
`completeMultipartiteGraph` (see also `isCompleteMultipartite_iff`) -/
/-
**SimpleGraph.IsCompleteMultipartite.iso** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.
IsCompleteMultipartite`。
形式化陈述：{α : Type u} →   {G : SimpleGraph α} →     (h : G.IsCompleteMultipartite) 
→ G ≃g SimpleGraph.completeMultipartiteGraph fun c => { x // h.setoid c.out x }
参数：h : G.IsCompleteMultipartite。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The graph isomorphism from a graph `G` that `IsCompleteMultipartite` to the corr
esponding
`completeMultipartiteGraph` (see also `isCompleteMultipartite_iff`)
-/
def IsCompleteMultipartite.iso (h : G.IsCompleteMultipartite) :
    G ≃g completeMultipartiteGraph (fun (c : Quotient h.setoid) ↦ {x // h.setoid.r c.out x}) where
  toFun := fun x ↦ ⟨_, ⟨_, Quotient.mk_out x⟩⟩
  invFun := fun ⟨_, x⟩ ↦ x.1
  right_inv := fun ⟨_, x⟩ ↦ Sigma.subtype_ext (Quotient.mk_eq_iff_out.2 <| h.setoid.symm x.2) rfl
  map_rel_iff' := by
    simp_rw [Equiv.coe_fn_mk, comap_adj, top_adj, ne_eq, Quotient.eq]
    intros
    change ¬¬ G.Adj _ _ ↔ _
    rw [not_not]
/-
**SimpleGraph.isCompleteMultipartite_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：isCompleteMultipartite_iff : G.IsCompleteMultipartite ↔ exists (ι : Type u
) (V : ι -> Type u) (_ : forall i, Nonempty (V i)), Nonempty (G ≃g completeMulti
partiteGraph V)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用定理 `SimpleGraph.completeMultipartiteGraph.isCompleteMultipartite`：∀ {ι : Typ
e u_1} (V : ι → Type u_2), (SimpleGraph.completeMultipartiteGraph V).IsCompleteM
ultipartite
-/
lemma isCompleteMultipartite_iff : G.IsCompleteMultipartite ↔ ∃ (ι : Type u) (V : ι → Type u)
    (_ : ∀ i, Nonempty (V i)), Nonempty (G ≃g completeMultipartiteGraph V) := by
  constructor <;> intro h
  · exact ⟨_, _, fun _ ↦ ⟨_, h.setoid.refl _⟩, ⟨h.iso⟩⟩
  · obtain ⟨_, _, _, ⟨e⟩⟩ := h
    refine ⟨fun _ _ _ h1 h2 ↦ ?_⟩
    rw [← e.map_rel_iff] at *
    exact completeMultipartiteGraph.isCompleteMultipartite _ |>.trans _ _ _ h1 h2
/-
**SimpleGraph.IsCompleteMultipartite.colorable_of_cliqueFree** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph.IsCompleteMultipartite`。
形式化陈述：∀ {α : Type u} {G : SimpleGraph α} {n : ℕ}, G.IsCompleteMultipartite → G.C
liqueFree n → G.Colorable (n - 1)
参数：n - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Colorable.of_hom`：∀ {V : Type u} {G : SimpleGraph V} {V' : T
ype u_4} {G' : SimpleGraph V'} {n : ℕ} (f : G →g G'),   G'.Colorable n → G.Color
able n
· 使用定理 `SimpleGraph.completeMultipartiteGraph.colorable_of_cliqueFree`：colorable
_of_cliqueFree (f : forall (i : ι), V i) (hc : (completeMultipartiteGraph V).Cli
queFree n) : (completeMultipartiteGraph V).Colorabl…
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用定理 `SimpleGraph.CliqueFree.comap`：∀ {α : Type u_1} {β : Type u_2} {G : Simpl
eGraph α} {n : ℕ} {H : SimpleGraph β},   H.IsContained G → G.CliqueFree n → H.Cl
iqueFree n
· 使用定理 `SimpleGraph.Iso.isContained`：∀ {V : Type u_1} {W : Type u_2} {G : Simple
Graph V} {H : SimpleGraph W} (e : G ≃g H), G.IsContained H
-/
lemma IsCompleteMultipartite.colorable_of_cliqueFree {n : ℕ} (h : G.IsCompleteMultipartite)
    (hc : G.CliqueFree n) : G.Colorable (n - 1) :=
  (completeMultipartiteGraph.colorable_of_cliqueFree _ (fun _ ↦ ⟨_, h.setoid.refl _⟩) <|
    hc.comap h.iso.symm.isContained).of_hom h.iso

variable (G) in
/--
The vertices `v, w₁, w₂` form an `IsPathGraph3Compl` in `G` iff `w₁w₂` is the only edge present
between these three vertices. It is a witness to the non-complete-multipartite-ness of `G` (see
`not_isCompleteMultipartite_iff_exists_isPathGraph3Compl`). This structure is an explicit way of
saying that the induced graph on `{v, w₁, w₂}` is the complement of `P3`.
-/
/-
**SimpleGraph.IsPathGraph3Compl** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{α : Type u} → SimpleGraph α → α → α → α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertices `v, w₁, w₂` form an `IsPathGraph3Compl` in `G` iff `w₁w₂` is the on
ly edge present
between these three vertices. It is a witness to the non-complete-multipartite-n
ess of `G` (see
`not_isCompleteMultipartite_iff_exists_isPathGraph3Compl`). This structure is an
 explicit way of
saying that the induced graph on `{v, w₁, w₂}` is the complement of `P3`.
-/
structure IsPathGraph3Compl (v w₁ w₂ : α) : Prop where
  adj : G.Adj w₁ w₂
  not_adj_fst : ¬ G.Adj v w₁
  not_adj_snd : ¬ G.Adj v w₂

namespace IsPathGraph3Compl

variable {v w₁ w₂ : α}

@[grind →]
/-
**SimpleGraph.IsPathGraph3Compl.ne_fst** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Is
PathGraph3Compl`。
形式化陈述：ne_fst (h2 : G.IsPathGraph3Compl v w₁ w₂) : v != w₁
参数：h2 : G.IsPathGraph3Compl v w₁ w₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsPathGraph3Compl.not_adj_snd`：∀ {α : Type u} {G : SimpleGra
ph α} {v w₁ w₂ : α}, G.IsPathGraph3Compl v w₁ w₂ → ¬G.Adj v w₂
· 使用定理 `SimpleGraph.IsPathGraph3Compl.adj`：∀ {α : Type u} {G : SimpleGraph α} {v
 w₁ w₂ : α}, G.IsPathGraph3Compl v w₁ w₂ → G.Adj w₁ w₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_fst (h2 : G.IsPathGraph3Compl v w₁ w₂) : v ≠ w₁ :=
  fun h ↦ h2.not_adj_snd (h.symm ▸ h2.adj)

@[grind →]
/-
**SimpleGraph.IsPathGraph3Compl.ne_snd** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Is
PathGraph3Compl`。
形式化陈述：ne_snd (h2 : G.IsPathGraph3Compl v w₁ w₂) : v != w₂
参数：h2 : G.IsPathGraph3Compl v w₁ w₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsPathGraph3Compl.not_adj_fst`：∀ {α : Type u} {G : SimpleGra
ph α} {v w₁ w₂ : α}, G.IsPathGraph3Compl v w₁ w₂ → ¬G.Adj v w₁
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.IsPathGraph3Compl.adj`：∀ {α : Type u} {G : SimpleGraph α} {v
 w₁ w₂ : α}, G.IsPathGraph3Compl v w₁ w₂ → G.Adj w₁ w₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_snd (h2 : G.IsPathGraph3Compl v w₁ w₂) : v ≠ w₂ :=
  fun h ↦ h2.not_adj_fst (h ▸ h2.adj.symm)

@[grind →]
/-
**SimpleGraph.IsPathGraph3Compl.fst_ne_snd** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h.IsPathGraph3Compl`。
形式化陈述：fst_ne_snd (h2 : G.IsPathGraph3Compl v w₁ w₂) : w₁ != w₂
参数：h2 : G.IsPathGraph3Compl v w₁ w₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `SimpleGraph.IsPathGraph3Compl.adj`：∀ {α : Type u} {G : SimpleGraph α} {v
 w₁ w₂ : α}, G.IsPathGraph3Compl v w₁ w₂ → G.Adj w₁ w₂
-/
lemma fst_ne_snd (h2 : G.IsPathGraph3Compl v w₁ w₂) : w₁ ≠ w₂ := h2.adj.ne
/-
**SimpleGraph.IsPathGraph3Compl.symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsPa
thGraph3Compl`。
形式化陈述：∀ {α : Type u} {G : SimpleGraph α} {v w₁ w₂ : α}, G.IsPathGraph3Compl v w₁
 w₂ → G.IsPathGraph3Compl v w₂ w₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
-/
@[symm] lemma symm (h : G.IsPathGraph3Compl v w₁ w₂) : G.IsPathGraph3Compl v w₂ w₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.symm, h3, h2⟩

end IsPathGraph3Compl

/-
**SimpleGraph.exists_isPathGraph3Compl_of_not_isCompleteMultipartite** 是 Mathlib
 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：exists_isPathGraph3Compl_of_not_isCompleteMultipartite (h : ¬ IsCompleteMu
ltipartite G) : exists v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂
参数：h : ¬ IsCompleteMultipartite G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.adj_comm`：adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u
-/
lemma exists_isPathGraph3Compl_of_not_isCompleteMultipartite (h : ¬ IsCompleteMultipartite G) :
    ∃ v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂ := by
  apply mt IsTrans.mk at h
  push Not at h
  obtain ⟨_, _, _, h1, h2, h3⟩ := h
  rw [adj_comm] at h1
  exact ⟨_, _, _, h3, h1, h2⟩
/-
**SimpleGraph.not_isCompleteMultipartite_iff_exists_isPathGraph3Compl** 是 Mathli
b 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：not_isCompleteMultipartite_iff_exists_isPathGraph3Compl : ¬ IsCompleteMult
ipartite G ↔ exists v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_isPathGraph3Compl_of_not_isCompleteMultipartite`：exis
ts_isPathGraph3Compl_of_not_isCompleteMultipartite (h : ¬ IsCompleteMultipartite
 G) : exists v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.adj_comm`：adj_comm (u v : V) : G.Adj u v ↔ G.Adj v u
-/
lemma not_isCompleteMultipartite_iff_exists_isPathGraph3Compl :
    ¬ IsCompleteMultipartite G ↔ ∃ v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂ :=
  ⟨fun h ↦ G.exists_isPathGraph3Compl_of_not_isCompleteMultipartite h,
   fun ⟨_, _, _, h1, h2, h3⟩ ↦ fun h ↦ h.trans _ _ _ (by rwa [adj_comm] at h2) h3 h1⟩

/--
Any `IsPathGraph3Compl` in `G` gives rise to a graph embedding of the complement of the path graph
-/
/-
**SimpleGraph.IsPathGraph3Compl.pathGraph3ComplEmbedding** 是 Mathlib 中的一个定义，位于命名
空间 `SimpleGraph.IsPathGraph3Compl`。
形式化陈述：{α : Type u} → {G : SimpleGraph α} → {v w₁ w₂ : α} → G.IsPathGraph3Compl v
 w₁ w₂ → (SimpleGraph.pathGraph 3)ᶜ ↪g G
参数：SimpleGraph.pathGraph 3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any `IsPathGraph3Compl` in `G` gives rise to a graph embedding of the complement
 of the path graph
-/
def IsPathGraph3Compl.pathGraph3ComplEmbedding {v w₁ w₂ : α} (h : G.IsPathGraph3Compl v w₁ w₂) :
    (pathGraph 3)ᶜ ↪g G where
  toFun := fun x ↦
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

/-- Embedding of `(pathGraph 3)ᶜ` into `G` that is not complete-multipartite. -/
/-
**SimpleGraph.pathGraph3ComplEmbeddingOf** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`
。
形式化陈述：pathGraph3ComplEmbeddingOf (h : ¬ G.IsCompleteMultipartite) : (pathGraph 3
)ᶜ ↪g G
参数：h : ¬ G.IsCompleteMultipartite。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.exists_isPathGraph3Compl_of_not_isCompleteMultipartite`：exis
ts_isPathGraph3Compl_of_not_isCompleteMultipartite (h : ¬ IsCompleteMultipartite
 G) : exists v w₁ w₂, G.IsPathGraph3Compl v w₁ w₂

--- 原说明 ---
Embedding of `(pathGraph 3)ᶜ` into `G` that is not complete-multipartite.
-/
noncomputable def pathGraph3ComplEmbeddingOf (h : ¬ G.IsCompleteMultipartite) :
    (pathGraph 3)ᶜ ↪g G :=
  IsPathGraph3Compl.pathGraph3ComplEmbedding
    (exists_isPathGraph3Compl_of_not_isCompleteMultipartite h).choose_spec.choose_spec.choose_spec
/-
**SimpleGraph.not_isCompleteMultipartite_of_pathGraph3ComplEmbedding** 是 Mathlib
 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：not_isCompleteMultipartite_of_pathGraph3ComplEmbedding (e : (pathGraph 3)ᶜ
 ↪g G) : ¬ IsCompleteMultipartite G
参数：e : (pathGraph 3)ᶜ ↪g G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
-/
lemma not_isCompleteMultipartite_of_pathGraph3ComplEmbedding (e : (pathGraph 3)ᶜ ↪g G) :
    ¬ IsCompleteMultipartite G := by
  intro h
  have h0 : ¬ G.Adj (e 0) (e 1) := by simp [pathGraph_adj]
  have h1 : ¬ G.Adj (e 1) (e 2) := by simp [pathGraph_adj]
  have h2 : G.Adj (e 0) (e 2) := by simp [pathGraph_adj]
  exact h.trans _ _ _ h0 h1 h2
/-
**SimpleGraph.IsCompleteMultipartite.comap** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.IsCompleteMultipartite`。
形式化陈述：∀ {α : Type u} {G : SimpleGraph α} {β : Type u_1} {H : SimpleGraph β} (f :
 H ↪g G),   G.IsCompleteMultipartite → H.IsCompleteMultipartite
参数：f : H ↪g G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `SimpleGraph.not_isCompleteMultipartite_of_pathGraph3ComplEmbedding`：not_
isCompleteMultipartite_of_pathGraph3ComplEmbedding (e : (pathGraph 3)ᶜ ↪g G) : ¬
 IsCompleteMultipartite G
-/
theorem IsCompleteMultipartite.comap {β : Type*} {H : SimpleGraph β} (f : H ↪g G) :
    G.IsCompleteMultipartite → H.IsCompleteMultipartite := by
  intro h; contrapose h
  exact not_isCompleteMultipartite_of_pathGraph3ComplEmbedding
          <| f.comp (pathGraph3ComplEmbeddingOf h)

section CompleteEquipartiteGraph

variable {r t : ℕ}

/-- The **complete equipartite graph** in `r` parts each of *equal* size `t` such that two
vertices are adjacent if and only if they are in different parts, often denoted $K_r(t)$.

This is isomorphic to a corresponding `completeMultipartiteGraph` and `turanGraph`. The difference
is that the former vertices are a product type.

See `completeEquipartiteGraph.completeMultipartiteGraph`, `completeEquipartiteGraph.turanGraph`. -/
/-
**SimpleGraph.completeEquipartiteGraph** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`
。
形式化陈述：completeEquipartiteGraph (r t : Nat) : SimpleGraph (Fin r × Fin t)
参数：r t : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **complete equipartite graph** in `r` parts each of *equal* size `t` such th
at two
vertices are adjacent if and only if they are in different parts, often denoted 
$K_r(t)$.

This is isomorphic to a corresponding `completeMultipartiteGraph` and `turanGrap
h`. The difference
is that the former vertices are a product type.

See `completeEquipartiteGraph.completeMultipartiteGraph`, `completeEquipartiteGr
aph.turanGraph`.
-/
abbrev completeEquipartiteGraph (r t : ℕ) : SimpleGraph (Fin r × Fin t) :=
  SimpleGraph.comap Prod.fst ⊤
/-
**SimpleGraph.completeEquipartiteGraph_adj** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h`。
形式化陈述：completeEquipartiteGraph_adj {v w} : (completeEquipartiteGraph r t).Adj v 
w ↔ v.1 != w.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma completeEquipartiteGraph_adj {v w} :
  (completeEquipartiteGraph r t).Adj v w ↔ v.1 ≠ w.1 := by rfl

set_option backward.isDefEq.respectTransparency false in
/-- A `completeEquipartiteGraph` is isomorphic to a corresponding `completeMultipartiteGraph`.

The difference is that the former vertices are a product type whereas the latter vertices are a
*dependent* product type. -/
/-
**SimpleGraph.completeEquipartiteGraph.completeMultipartiteGraph** 是 Mathlib 中的一
个定义，位于命名空间 `SimpleGraph.completeEquipartiteGraph`。
形式化陈述：{r t : ℕ} →   SimpleGraph.completeEquipartiteGraph r t ≃g SimpleGraph.comp
leteMultipartiteGraph (Function.const (Fin r) (Fin t))
参数：Function.const (Fin r) (Fin t)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A `completeEquipartiteGraph` is isomorphic to a corresponding `completeMultipart
iteGraph`.

The difference is that the former vertices are a product type whereas the latter
 vertices are a
*dependent* product type.
-/
def completeEquipartiteGraph.completeMultipartiteGraph :
    completeEquipartiteGraph r t ≃g completeMultipartiteGraph (const (Fin r) (Fin t)) :=
  { (Equiv.sigmaEquivProd (Fin r) (Fin t)).symm with map_rel_iff' := by simp }

set_option backward.isDefEq.respectTransparency.types false in
/-- A `completeEquipartiteGraph` is isomorphic to a corresponding `turanGraph`.

The difference is that the former vertices are a product type whereas the latter vertices are
not. -/
/-
**SimpleGraph.completeEquipartiteGraph.turanGraph** 是 Mathlib 中的一个定义，位于命名空间 `Sim
pleGraph.completeEquipartiteGraph`。
形式化陈述：{r t : ℕ} → SimpleGraph.completeEquipartiteGraph r t ≃g SimpleGraph.turanG
raph (r * t) r
参数：r * t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `completeEquipartiteGraph` is isomorphic to a corresponding `turanGraph`.

The difference is that the former vertices are a product type whereas the latter
 vertices are
not.
-/
def completeEquipartiteGraph.turanGraph :
    completeEquipartiteGraph r t ≃g turanGraph (r * t) r where
  toFun := by
    refine fun v ↦ ⟨v.2 * r + v.1, ?_⟩
    conv_rhs =>
      rw [← Nat.sub_one_add_one_eq_of_pos v.2.pos, Nat.mul_add_one, mul_comm r (t - 1)]
    exact add_lt_add_of_le_of_lt (Nat.mul_le_mul_right r (Nat.le_pred_of_lt v.2.prop)) v.1.prop
  invFun := by
    refine fun v ↦ (⟨v % r, ?_⟩, ⟨v / r, ?_⟩)
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
    rw [turanGraph_adj, Equiv.coe_fn_mk, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt v.1.prop,
      Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt w.1.prop, ← Fin.ext_iff.ne,
      ← completeEquipartiteGraph_adj]

/-- `completeEquipartiteGraph r t` contains no edges when `r ≤ 1` or `t = 0`. -/
/-
**SimpleGraph.completeEquipartiteGraph_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Sim
pleGraph`。
形式化陈述：completeEquipartiteGraph_eq_bot_iff : completeEquipartiteGraph r t = ⊥ ↔ r
 <= 1 ∨ t = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.edgeSet_nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.edge
Set.Nonempty ↔ G ≠ ⊥
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Fin.nontrivial_iff_two_le`：nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 
2 <= n
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Fin.pos_iff_nonempty`：∀ {n : ℕ}, 0 < n ↔ Nonempty (Fin n)
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用引理 `SimpleGraph.completeEquipartiteGraph_adj`：completeEquipartiteGraph_adj {
v w} : (completeEquipartiteGraph r t).Adj v w ↔ v.1 != w.1
· 使用定理 `SimpleGraph.mem_edgeSet`：mem_edgeSet : s(v, w) in G.edgeSet ↔ G.Adj v w

--- 原说明 ---
`completeEquipartiteGraph r t` contains no edges when `r ≤ 1` or `t = 0`.
-/
lemma completeEquipartiteGraph_eq_bot_iff :
    completeEquipartiteGraph r t = ⊥ ↔ r ≤ 1 ∨ t = 0 := by
  contrapose!
  rw [← edgeSet_nonempty, ← Nat.succ_le_iff, ← Fin.nontrivial_iff_two_le, ← Nat.pos_iff_ne_zero,
    Fin.pos_iff_nonempty]
  refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨⟨i₁, i₂, hv⟩, ⟨x⟩⟩ ↦ ?_⟩
  · induction e with | _ v₁ v₂
    rw [mem_edgeSet, completeEquipartiteGraph_adj] at he
    exact ⟨⟨v₁.1, v₂.1, he⟩, ⟨v₁.2⟩⟩
  · use s((i₁, x), (i₂, x))
    rw [mem_edgeSet, completeEquipartiteGraph_adj]
    exact hv
/-
**SimpleGraph.completeEquipartiteGraph.isCompleteMultipartite** 是 Mathlib 中的一个定理
，位于命名空间 `SimpleGraph.completeEquipartiteGraph`。
形式化陈述：∀ {r t : ℕ}, (SimpleGraph.completeEquipartiteGraph r t).IsCompleteMultipar
tite
参数：SimpleGraph.completeEquipartiteGraph r t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.completeEquipartiteGraph_eq_bot_iff`：completeEquipartiteGrap
h_eq_bot_iff : completeEquipartiteGraph r t = ⊥ ↔ r <= 1 ∨ t = 0
· 使用定理 `SimpleGraph.bot_isCompleteMultipartite`：bot_isCompleteMultipartite : (⊥ 
: SimpleGraph α).IsCompleteMultipartite
· 使用引理 `SimpleGraph.isCompleteMultipartite_iff`：isCompleteMultipartite_iff : G.I
sCompleteMultipartite ↔ exists (ι : Type u) (V : ι -> Type u) (_ : forall i, Non
empty (V i)), Nonempty (G ≃g…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.pos_iff_nonempty`：∀ {n : ℕ}, 0 < n ↔ Nonempty (Fin n)
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
/-
**SimpleGraph.neighborSet_completeEquipartiteGraph** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph`。
形式化陈述：neighborSet_completeEquipartiteGraph (v) : (completeEquipartiteGraph r t).
neighborSet v = {v.1}ᶜ ×ˢ Set.univ
参数：v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neighborSet_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).neighborSet v = {v.1}ᶜ ×ˢ Set.univ := by
  ext; simp [ne_comm]
/-
**SimpleGraph.neighborFinset_completeEquipartiteGraph** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph`。
形式化陈述：neighborFinset_completeEquipartiteGraph (v) : (completeEquipartiteGraph r 
t).neighborFinset v = {v.1}ᶜ ×ˢ univ
参数：v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neighborFinset_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).neighborFinset v = {v.1}ᶜ ×ˢ univ := by
  ext; simp [ne_comm]
/-
**SimpleGraph.degree_completeEquipartiteGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：degree_completeEquipartiteGraph (v) : (completeEquipartiteGraph r t).degre
e v = (r - 1) * t
参数：v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_neighborFinset_eq_degree`：card_neighborFinset_eq_degree
 : #(G.neighborFinset v) = G.degree v
· 使用定理 `SimpleGraph.neighborFinset_completeEquipartiteGraph`：neighborFinset_comp
leteEquipartiteGraph (v) : (completeEquipartiteGraph r t).neighborFinset v = {v.
1}ᶜ ×ˢ univ
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
-/
theorem degree_completeEquipartiteGraph (v) :
    (completeEquipartiteGraph r t).degree v = (r - 1) * t := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_completeEquipartiteGraph v,
    card_product, card_compl, card_singleton, Fintype.card_fin, card_univ, Fintype.card_fin]
/-
**SimpleGraph.card_edgeFinset_completeEquipartiteGraph** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph`。
形式化陈述：card_edgeFinset_completeEquipartiteGraph : #(completeEquipartiteGraph r t)
.edgeFinset = r.choose 2 * t ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.sum_degrees_eq_twice_card_edges`：sum_degrees_eq_twice_card_e
dges : ∑ v, G.degree v = 2 * #G.edgeFinset
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.degree_completeEquipartiteGraph`：degree_completeEquipartiteG
raph (v) : (completeEquipartiteGraph r t).degree v = (r - 1) * t
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Nat.mul_assoc`：∀ (n m k : ℕ), n * m * k = n * (m * k)
· 使用定理 `Nat.choose_two_right`：choose_two_right (n : Nat) : choose n 2 = n * (n -
 1) / 2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Even.two_dvd`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → 2 ∣
 a
· 使用引理 `Nat.even_mul_pred_self`：even_mul_pred_self (n : Nat) : Even (n * (n - 1)
)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem card_edgeFinset_completeEquipartiteGraph :
    #(completeEquipartiteGraph r t).edgeFinset = r.choose 2 * t ^ 2 := by
  rw [← mul_right_inj' two_ne_zero, ← sum_degrees_eq_twice_card_edges]
  conv_lhs =>
    rhs; intro v
    rw [degree_completeEquipartiteGraph v]
  rw [sum_const, smul_eq_mul, card_univ, card_prod, Fintype.card_fin, Fintype.card_fin]
  conv_rhs =>
    rw [← Nat.mul_assoc, Nat.choose_two_right, Nat.mul_div_cancel' r.even_mul_pred_self.two_dvd]
  rw [← mul_assoc, mul_comm r _, mul_assoc t _ _, mul_comm t, mul_assoc _ t, ← pow_two]

variable [Fintype α]

/-- Every `n`-colorable graph is contained in a `completeEquipartiteGraph` in `n` parts (as long
  as the parts are at least as large as the largest color class). -/
/-
**SimpleGraph.isContained_completeEquipartiteGraph_of_colorable** 是 Mathlib 中的一个
定理，位于命名空间 `SimpleGraph`。
形式化陈述：isContained_completeEquipartiteGraph_of_colorable {n : Nat} (C : G.Colorin
g (Fin n)) (t : Nat) (h : forall c, card (C.colorClass c) <= t) : G ⊑ completeEq
uipartiteGraph n t
参数：C : G.Coloring (Fin n)；t : Nat；h : forall c, card (C.colorClass c) <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Embedding.nonempty_iff_card_le`：nonempty_iff_card_le [Fintype α
] [Fintype β] : Nonempty (α ↪ β) ↔ Fintype.card α <= Fintype.card β
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_heq`：congr_heq {α β γ : Sort _} {f : α -> γ} {g : β -> γ} {x : α} 
{y : β} (h₁ : f ≍ g) (h₂ : x ≍ y) : f x = g y
· 使用定理 `Subtype.heq_iff_coe_eq`：heq_iff_coe_eq (h : forall x, p x ↔ q x) {a1 : {
 x // p x }} {a2 : { x // q x }} : a1 ≍ a2 ↔ (a1 : α) = (a2 : α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `SimpleGraph.Coloring.mem_colorClass`：∀ {V : Type u} {G : SimpleGraph V} 
{α : Type u_2} (C : G.Coloring α) (v : V), v ∈ C.colorClass (C v)
· 使用定理 `SimpleGraph.Coloring.valid`：∀ {V : Type u} {G : SimpleGraph V} {α : Type
 u_2} (C : G.Coloring α) {v w : V}, G.Adj v w → C v ≠ C w
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Every `n`-colorable graph is contained in a `completeEquipartiteGraph` in `n` pa
rts (as long
  as the parts are at least as large as the largest color class).
-/
theorem isContained_completeEquipartiteGraph_of_colorable {n : ℕ} (C : G.Coloring (Fin n))
    (t : ℕ) (h : ∀ c, card (C.colorClass c) ≤ t) : G ⊑ completeEquipartiteGraph n t := by
  have (c : Fin n) : Nonempty (C.colorClass c ↪ Fin t) := by
    rw [Embedding.nonempty_iff_card_le, Fintype.card_fin]
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
  use ⟨fun v ↦ (C v, F (C v) ⟨v, C.mem_colorClass v⟩), C.valid⟩
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
/-
**SimpleGraph.CompleteEquipartiteSubgraph** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGra
ph`。
形式化陈述：{V : Type u_1} → SimpleGraph V → ℕ → ℕ → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete equipartite subgraph in `r > 0` parts each of size `t ≠ 0` in `G` is 
`r` subsets
of vertices each of size `t` such that vertices in distinct subsets are adjacent
.

If `r > 0` but `t = 0`, then `parts = {{}}`. If `r = 0`, then `parts = {}`. Thes
e are the two
*distinct* "empty" complete equipartite subgraphs, that is, the complete equipar
tite subgraphs
having no vertices.
-/
structure CompleteEquipartiteSubgraph (G : SimpleGraph V) (r t : ℕ) where
  /-- The parts in a complete equipartite subgraph. -/
  parts : Finset (Finset V)
  /-- There are `r` parts or `t = 0`. -/
  card_parts : #parts = r ∨ t = 0
  /-- There are `t` vertices in each part. -/
  card_mem_parts {p} : p ∈ parts → #p = t
  /-- The vertices in distinct parts are adjacent. -/
  isCompleteBetween : (parts : Set (Finset V)).Pairwise (G.IsCompleteBetween · ·)

variable {r t : ℕ} (K : G.CompleteEquipartiteSubgraph r t)

namespace CompleteEquipartiteSubgraph

/-- At least one of the "empty" complete equipartite subgraphs is contained in a simple graph. -/
/-
**SimpleGraph.CompleteEquipartiteSubgraph.nonempty_of_eq_zero_or_eq_zero** 是 Mat
hlib 中的一个定理，位于命名空间 `SimpleGraph.CompleteEquipartiteSubgraph`。
形式化陈述：nonempty_of_eq_zero_or_eq_zero (h : r = 0 ∨ t = 0) : Nonempty (G.CompleteE
quipartiteSubgraph r t)
参数：h : r = 0 ∨ t = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅

--- 原说明 ---
At least one of the "empty" complete equipartite subgraphs is contained in a sim
ple graph.
-/
theorem nonempty_of_eq_zero_or_eq_zero (h : r = 0 ∨ t = 0) :
    Nonempty (G.CompleteEquipartiteSubgraph r t) :=
  ⟨{}, h.elim (fun hr ↦ by simp [hr]) (fun ht ↦ by simp [ht]), by simp, by simp⟩

/-- The parts in a complete equipartite subgraph are pairwise disjoint. -/
/-
**SimpleGraph.CompleteEquipartiteSubgraph.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.CompleteEquipartiteSubgraph`。
形式化陈述：disjoint : (K.parts : Set (Finset V)).Pairwise Disjoint
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `SimpleGraph.irrefl`：∀ {V : Type u} (G : SimpleGraph V) {v : V}, ¬G.Adj v
 v
· 使用定理 `SimpleGraph.CompleteEquipartiteSubgraph.isCompleteBetween`：∀ {V : Type u
_1} {G : SimpleGraph V} {r t : ℕ} (self : G.CompleteEquipartiteSubgraph r t),   
(↑self.parts).Pairwise fun x1 x2 => G.IsComplet…

--- 原说明 ---
The parts in a complete equipartite subgraph are pairwise disjoint.
-/
theorem disjoint : (K.parts : Set (Finset V)).Pairwise Disjoint :=
  fun _ h₁ _ h₂ hne ↦ Finset.disjoint_left.mpr fun _ h₁' h₂' ↦
    G.irrefl <| K.isCompleteBetween h₁ h₂ hne h₁' h₂'

/-- The finset of vertices in a complete equipartite subgraph. -/
/-
**SimpleGraph.CompleteEquipartiteSubgraph.verts** 是 Mathlib 中的一个定义，位于命名空间 `Simpl
eGraph.CompleteEquipartiteSubgraph`。
形式化陈述：verts : Finset V
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.CompleteEquipartiteSubgraph.disjoint`：disjoint : (K.parts : 
Set (Finset V)).Pairwise Disjoint

--- 原说明 ---
The finset of vertices in a complete equipartite subgraph.
-/
def verts : Finset V := K.parts.disjiUnion id K.disjoint

set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-- The finset of vertices in a complete equipartite subgraph as a `biUnion`. -/
/-
**SimpleGraph.CompleteEquipartiteSubgraph.verts_eq_biUnion** 是 Mathlib 中的一个引理，位于
命名空间 `SimpleGraph.CompleteEquipartiteSubgraph`。
形式化陈述：verts_eq_biUnion : K.verts = K.parts.biUnion id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.CompleteEquipartiteSubgraph.disjoint`：disjoint : (K.parts : 
Set (Finset V)).Pairwise Disjoint
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.CompleteEquipartiteSubgraph.verts.eq_1`：∀ {V : Type u_1} {G 
: SimpleGraph V} {r t : ℕ} (K : G.CompleteEquipartiteSubgraph r t),   K.verts = 
K.parts.disjiUnion id ⋯
· 使用引理 `Finset.disjiUnion_eq_biUnion`：disjiUnion_eq_biUnion (s : Finset α) (f : 
α -> Finset β) (hf) : s.disjiUnion f hf = s.biUnion f

--- 原说明 ---
The finset of vertices in a complete equipartite subgraph as a `biUnion`.
-/
lemma verts_eq_biUnion : K.verts = K.parts.biUnion id := by rw [verts, disjiUnion_eq_biUnion]

set_option backward.isDefEq.respectTransparency.types false in
/-- There are `r * t` vertices in a complete equipartite subgraph with `r` parts of size `t`. -/
/-
**SimpleGraph.CompleteEquipartiteSubgraph.card_verts** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.CompleteEquipartiteSubgraph`。
形式化陈述：card_verts : #K.verts = r * t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.CompleteEquipartiteSubgraph.disjoint`：disjoint : (K.parts : 
Set (Finset V)).Pairwise Disjoint
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_disjiUnion`：card_disjiUnion (s : Finset ι) (t : ι -> Finset 
M) (h) : #(s.disjiUnion t h) = ∑ a in s, #(t a)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SimpleGraph.CompleteEquipartiteSubgraph.card_mem_parts`：∀ {V : Type u_1}
 {G : SimpleGraph V} {r t : ℕ} (self : G.CompleteEquipartiteSubgraph r t) {p : F
inset V},   p ∈ self.parts → p.card = t
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `SimpleGraph.CompleteEquipartiteSubgraph.card_parts`：∀ {V : Type u_1} {G 
: SimpleGraph V} {r t : ℕ} (self : G.CompleteEquipartiteSubgraph r t), self.part
s.card = r ∨ t = 0

--- 原说明 ---
There are `r * t` vertices in a complete equipartite subgraph with `r` parts of 
size `t`.
-/
theorem card_verts : #K.verts = r * t := by
  simp_rw [verts, card_disjiUnion, id_eq, sum_congr rfl fun _ ↦ K.card_mem_parts, sum_const,
    smul_eq_mul, mul_eq_mul_right_iff]
  exact K.card_parts

/-- A complete equipartite subgraph gives rise to a copy of a complete equipartite graph. -/
/-
**SimpleGraph.CompleteEquipartiteSubgraph.toCopy** 是 Mathlib 中的一个定义，位于命名空间 `Simp
leGraph.CompleteEquipartiteSubgraph`。
形式化陈述：toCopy : Copy (completeEquipartiteGraph r t) G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete equipartite subgraph gives rise to a copy of a complete equipartite g
raph.
-/
noncomputable def toCopy : Copy (completeEquipartiteGraph r t) G := by
  by_cases ht : t = 0
  · rw [completeEquipartiteGraph_eq_bot_iff.mpr <| .inr ht]
    have : IsEmpty (Fin r × Fin t) := by simp [ht, Fin.isEmpty]
    exact Copy.bot .ofIsEmpty
  · have : Nonempty (Fin r ↪ K.parts) := by
      rw [Embedding.nonempty_iff_card_le,
        Fintype.card_fin, card_coe, K.card_parts.resolve_right ht]
    let fᵣ : Fin r ↪ K.parts := Classical.arbitrary (Fin r ↪ K.parts)
    have (p : K.parts) : Nonempty (Fin t ↪ p) := by
      rw [Embedding.nonempty_iff_card_le, Fintype.card_fin, card_coe, K.card_mem_parts p.prop]
    let fₜ (p : K.parts) : Fin t ↪ p :=
      Classical.arbitrary (Fin t ↪ p)
    let f : (Fin r) × (Fin t) ↪ V := by
      use fun (i, j) ↦ fₜ (fᵣ i) j
      intro (i₁, j₁) (i₂, j₂) heq
      rw [Prod.mk.injEq]
      contrapose! heq with hne
      rcases eq_or_ne i₁ i₂ with heq | hne
      · rw [heq, ← Subtype.ext_iff.ne]
        exact (fₜ _).injective.ne (hne heq)
      · refine (K.isCompleteBetween (fᵣ _).prop (fᵣ _).prop ?_ (fₜ _ _).prop (fₜ _ _).prop).ne
        exact Subtype.ext_iff.ne.mp <| fᵣ.injective.ne hne
    refine ⟨⟨f, fun hne ↦ ?_⟩, f.injective⟩
    refine K.isCompleteBetween (fᵣ _).prop (fᵣ _).prop ?_ (fₜ _ _).prop (fₜ _ _).prop
    exact Subtype.ext_iff.ne.mp <| fᵣ.injective.ne hne

set_option backward.isDefEq.respectTransparency.types false in
/-- A copy of a complete equipartite graph identifies a complete equipartite subgraph. -/
/-
**SimpleGraph.CompleteEquipartiteSubgraph.ofCopy** 是 Mathlib 中的一个定义，位于命名空间 `Simp
leGraph.CompleteEquipartiteSubgraph`。
形式化陈述：ofCopy (f : Copy (completeEquipartiteGraph r t) G) : G.CompleteEquipartite
Subgraph r t
参数：f : Copy (completeEquipartiteGraph r t) G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A copy of a complete equipartite graph identifies a complete equipartite subgrap
h.
-/
def ofCopy (f : Copy (completeEquipartiteGraph r t) G) : G.CompleteEquipartiteSubgraph r t := by
  by_cases ht : t = 0
  · exact ⟨∅, .inr ht, by simp, by simp⟩
  · refine ⟨univ.map ⟨fun i ↦ univ.map ⟨fun j ↦ f (i, j), fun _ _ h ↦ ?_⟩, fun i₁ i₂ h ↦ ?_⟩,
      ?_, fun h ↦ ?_, fun _ h₁ _ h₂ hne _ h₁' _ h₂' ↦ ?_⟩
    · simpa using f.injective h
    · simp_rw [Finset.ext_iff] at h
      have : NeZero t := ⟨ht⟩
      obtain ⟨_, heq⟩ : ∃ j, f (i₁, j) = f (i₂, 0) := by simpa using h <| f (i₂, 0)
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
      rw [← h₁', ← h₂']
      apply f.toHom.map_adj
      simp_rw [completeEquipartiteGraph_adj]
      contrapose hne with heq
      simp_rw [← h₁, ← h₂, heq]

end CompleteEquipartiteSubgraph

/-- Simple graphs contain a copy of a `completeEquipartiteGraph r t` iff the type
`G.CompleteEquipartiteSubgraph r t` is nonempty. -/
/-
**SimpleGraph.completeEquipartiteGraph_isContained_iff** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph`。
形式化陈述：completeEquipartiteGraph_isContained_iff : completeEquipartiteGraph r t ⊑ 
G ↔ Nonempty (G.CompleteEquipartiteSubgraph r t)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Simple graphs contain a copy of a `completeEquipartiteGraph r t` iff the type
`G.CompleteEquipartiteSubgraph r t` is nonempty.
-/
theorem completeEquipartiteGraph_isContained_iff :
    completeEquipartiteGraph r t ⊑ G ↔ Nonempty (G.CompleteEquipartiteSubgraph r t) :=
  ⟨fun ⟨f⟩ ↦ ⟨CompleteEquipartiteSubgraph.ofCopy f⟩, fun ⟨K⟩ ↦ ⟨K.toCopy⟩⟩

/-- Simple graphs contain a copy of a `completeEquipartiteGraph (r + 1) t` iff there exists
`s : Finset V` of size `#s = t` and `K : G.CompleteEquipartiteSubgraph r t` such that the
vertices in `s` are adjacent to the vertices in `K`. -/
/-
**SimpleGraph.completeEquipartiteGraph_succ_isContained_iff** 是 Mathlib 中的一个定理，位
于命名空间 `SimpleGraph`。
形式化陈述：completeEquipartiteGraph_succ_isContained_iff : completeEquipartiteGraph (
r + 1) t ⊑ G ↔ existsᵉ (K : G.CompleteEquipartiteSubgraph r t) (s : Finset V), #
s = t ∧ forall p in K.parts, G.IsCompleteBetween p s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.completeEquipartiteGraph_eq_bot_iff`：completeEquipartiteGrap
h_eq_bot_iff : completeEquipartiteGraph r t = ⊥ ↔ r <= 1 ∨ t = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `SimpleGraph.CompleteEquipartiteSubgraph.nonempty_of_eq_zero_or_eq_zero`：
nonempty_of_eq_zero_or_eq_zero (h : r = 0 ∨ t = 0) : Nonempty (G.CompleteEquipar
titeSubgraph r t)
· 使用定理 `SimpleGraph.completeEquipartiteGraph_isContained_iff`：completeEquipartit
eGraph_isContained_iff : completeEquipartiteGraph r t ⊑ G ↔ Nonempty (G.Complete
EquipartiteSubgraph r t)
· 使用引理 `Finset.exists_subset_card_eq`：exists_subset_card_eq (hns : n <= #s) : ex
ists t subseteq s, #t = n
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `SimpleGraph.CompleteEquipartiteSubgraph.card_parts`：∀ {V : Type u_1} {G 
: SimpleGraph V} {r t : ℕ} (self : G.CompleteEquipartiteSubgraph r t), self.part
s.card = r ∨ t = 0
· 使用定理 `Nat.pred_succ`：∀ (n : ℕ), n.succ.pred = n
· 使用定理 `SimpleGraph.CompleteEquipartiteSubgraph.card_mem_parts`：∀ {V : Type u_1}
 {G : SimpleGraph V} {r t : ℕ} (self : G.CompleteEquipartiteSubgraph r t) {p : F
inset V},   p ∈ self.parts → p.card = t
· 使用定理 `SimpleGraph.CompleteEquipartiteSubgraph.isCompleteBetween`：∀ {V : Type u
_1} {G : SimpleGraph V} {r t : ℕ} (self : G.CompleteEquipartiteSubgraph r t),   
(↑self.parts).Pairwise fun x1 x2 => G.IsComplet…
· 使用定理 `Finset.exists_eq_insert_iff`：exists_eq_insert_iff [DecidableEq α] : (exi
sts a ∉ s, insert a s = t) ↔ s subseteq t ∧ #s + 1 = #t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `SimpleGraph.irrefl`：∀ {V : Type u} (G : SimpleGraph V) {v : V}, ¬G.Adj v
 v
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Simple graphs contain a copy of a `completeEquipartiteGraph (r + 1) t` iff there
 exists
`s : Finset V` of size `#s = t` and `K : G.CompleteEquipartiteSubgraph r t` such
 that the
vertices in `s` are adjacent to the vertices in `K`.
-/
theorem completeEquipartiteGraph_succ_isContained_iff :
  completeEquipartiteGraph (r + 1) t ⊑ G
    ↔ ∃ᵉ (K : G.CompleteEquipartiteSubgraph r t) (s : Finset V),
        #s = t ∧ ∀ p ∈ K.parts, G.IsCompleteBetween p s := by
  classical
  by_cases ht : t = 0
  · have (r' : ℕ) : IsEmpty (Fin r' × Fin t) := by simp [ht, Fin.isEmpty]
    have h_bot (r' : ℕ) : completeEquipartiteGraph r' t = ⊥ :=
      completeEquipartiteGraph_eq_bot_iff.mpr <| .inr ht
    simp_rw [h_bot (r + 1), ht, Finset.card_eq_zero, exists_eq_left, IsCompleteBetween, mem_coe,
      notMem_empty, IsEmpty.forall_iff, implies_true, exists_true_iff_nonempty]
    exact ⟨fun _ ↦ CompleteEquipartiteSubgraph.nonempty_of_eq_zero_or_eq_zero (.inr ht),
      fun _ ↦ ⟨Copy.bot .ofIsEmpty⟩⟩
  · rw [completeEquipartiteGraph_isContained_iff]
    refine ⟨fun ⟨K'⟩ ↦ ?_, fun ⟨K, s, hs, hadj⟩ ↦ ?_⟩
    · obtain ⟨parts, hparts_sub, hparts_card⟩ := K'.parts.exists_subset_card_eq (Nat.pred_le _)
      let K : G.CompleteEquipartiteSubgraph r t := by
        refine ⟨parts, ?_, fun h ↦ K'.card_mem_parts (hparts_sub h),
          fun _ h₁ _ h₂ hne ↦ K'.isCompleteBetween (hparts_sub h₁) (hparts_sub h₂) hne⟩
        rw [hparts_card, K'.card_parts.resolve_right ht]
        exact .inl (Nat.pred_succ r)
      obtain ⟨s, nhs_mem, hs⟩ : ∃ s ∉ K.parts, insert s K.parts = K'.parts := by
        refine exists_eq_insert_iff.mpr ⟨hparts_sub, ?_⟩
        rw [K.card_parts.resolve_right ht, K'.card_parts.resolve_right ht]
      have hs_mem : s ∈ K'.parts := by simp [← hs]
      exact ⟨K, s, K'.card_mem_parts hs_mem,
        fun _ h ↦ K'.isCompleteBetween (hparts_sub h) hs_mem (ne_of_mem_of_not_mem h nhs_mem)⟩
    · refine ⟨K.parts.cons s ?_, ?_, ?_, ?_⟩
      · intro hs_mem
        obtain ⟨v, hv⟩ : s.Nonempty := by
          rw [← Finset.card_pos, hs]
          exact Nat.pos_of_ne_zero ht
        exact G.irrefl <| hadj s hs_mem hv hv
      · rw [Finset.card_cons, K.card_parts.resolve_right ht]
        exact .inl rfl
      · simp_rw [mem_cons, forall_eq_or_imp]
        exact ⟨hs, fun p ↦ K.card_mem_parts⟩
      · rw [coe_cons]
        have : Std.Symm G.IsCompleteBetween := by simp [symm_def, isCompleteBetween_comm]
        exact K.isCompleteBetween.insert_of_symm fun p hp _ ↦ hadj p hp |>.symm

end CompleteEquipartiteSubgraph

end SimpleGraph

