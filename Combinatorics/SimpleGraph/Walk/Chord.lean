/-
Copyright (c) 2026 Tianyi Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianyi Zhao
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Chords of walks

This file defines chords and chordless walks in a simple graph.

## Main definitions

* `SimpleGraph.Walk.IsChord`: an edge of the ambient graph between two vertices of a walk
  which is not an edge of the walk itself
* `SimpleGraph.Walk.IsChordless`: a walk with no chords

## Tags
walks, chords
-/

public section

namespace SimpleGraph
namespace Walk

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

/-- A chord of a walk `p` is an edge of `G` between two vertices of `p` which is not one
of the edges of `p`. -/
@[expose]
/-
**SimpleGraph.Walk.IsChord** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：IsChord (p : G.Walk u v) (e : Sym2 V) : Prop
参数：p : G.Walk u v；e : Sym2 V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A chord of a walk `p` is an edge of `G` between two vertices of `p` which is not
 one
of the edges of `p`.
-/
def IsChord (p : G.Walk u v) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ e ∉ p.edges ∧
    e.lift ⟨fun v w => v ∈ p.support ∧ w ∈ p.support, by grind⟩
/-
**SimpleGraph.Walk.isChord_sym2Mk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isChord_sym2Mk {p : G.Walk u v} {u' v' : V} : p.IsChord s(u', v') ↔ G.Adj 
u' v' ∧ s(u', v') ∉ p.edges ∧ u' in p.support ∧ v' in p.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isChord_sym2Mk {p : G.Walk u v} {u' v' : V} :
    p.IsChord s(u', v') ↔ G.Adj u' v' ∧ s(u', v') ∉ p.edges ∧ u' ∈ p.support ∧ v' ∈ p.support :=
  .rfl

/-- A walk is chordless if it has no chords. -/
@[expose]
/-
**SimpleGraph.Walk.IsChordless** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：IsChordless (p : G.Walk u v) : Prop
参数：p : G.Walk u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A walk is chordless if it has no chords.
-/
def IsChordless (p : G.Walk u v) : Prop :=
  ∀ ⦃e : Sym2 V⦄, ¬ p.IsChord e
/-
**SimpleGraph.Walk.isChordless_iff_forall_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Walk`。
形式化陈述：isChordless_iff_forall_mem_edges {p : G.Walk u v} : p.IsChordless ↔ forall
 ⦃u' v' : V⦄, u' in p.support -> v' in p.support -> G.Adj u' v' -> s(u', v') in 
p.edges
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem isChordless_iff_forall_mem_edges {p : G.Walk u v} :
    p.IsChordless ↔
      ∀ ⦃u' v' : V⦄, u' ∈ p.support → v' ∈ p.support → G.Adj u' v' → s(u', v') ∈ p.edges := by
  simp [IsChordless, Sym2.forall, isChord_sym2Mk]; grind
/-
**SimpleGraph.Walk.IsChordless.mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk.IsChordless`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V} {p : G.Walk u v},   p.IsCho
rdless → ∀ {u' v' : V}, u' ∈ p.support → v' ∈ p.support → G.Adj u' v' → s(u', v'
) ∈ p.edges
参数：u', v'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isChordless_iff_forall_mem_edges`：isChordless_iff_foral
l_mem_edges {p : G.Walk u v} : p.IsChordless ↔ forall ⦃u' v' : V⦄, u' in p.suppo
rt -> v' in p.support -> G.Adj u' v' ->…
-/
theorem IsChordless.mem_edges {p : G.Walk u v} (h : p.IsChordless) {u' v' : V}
    (hu' : u' ∈ p.support) (hv' : v' ∈ p.support) (hadj : G.Adj u' v') : s(u', v') ∈ p.edges :=
  isChordless_iff_forall_mem_edges.mp h hu' hv' hadj
/-
**SimpleGraph.Walk._root_.SimpleGraph.Adj.isChordless_toWalk** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph.Walk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.Adj.isChordless_toWalk (h : G.Adj u v) : h.toWalk.IsChordless := by
  grind [isChordless_iff_forall_mem_edges, h.support_toWalk, h.edges_toWalk, Adj.ne]

end Walk
end SimpleGraph

