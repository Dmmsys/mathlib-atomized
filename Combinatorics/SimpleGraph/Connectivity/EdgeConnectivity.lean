/-
Copyright (c) 2025 Youheng Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youheng Luo
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card

/-!
# Edge Connectivity

This file defines k-edge-connectivity for simple graphs.

## Main definitions

* `SimpleGraph.IsEdgeReachable`: Two vertices are `k`-edge-reachable if they remain reachable after
  removing strictly fewer than `k` edges.
* `SimpleGraph.IsEdgeConnected`: A graph is `k`-edge-connected if any two vertices are
  `k`-edge-reachable.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {k l : ℕ} {u v w x y : V}

variable (G k u v) in
/-- Two vertices are `k`-edge-reachable if they remain reachable after removing strictly fewer than
`k` edges. -/
/-
**SimpleGraph.IsEdgeReachable** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsEdgeReachable : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two vertices are `k`-edge-reachable if they remain reachable after removing stri
ctly fewer than
`k` edges.
-/
def IsEdgeReachable : Prop :=
  ∀ ⦃s : Set (Sym2 V)⦄, s.encard < k → (G.deleteEdges s).Reachable u v

variable (G k) in
/-- A graph is `k`-edge-connected if any two vertices are `k`-edge-reachable. -/
/-
**SimpleGraph.IsEdgeConnected** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsEdgeConnected : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph is `k`-edge-connected if any two vertices are `k`-edge-reachable.
-/
def IsEdgeConnected : Prop := ∀ u v, G.IsEdgeReachable k u v

@[refl, simp]
/-
**SimpleGraph.IsEdgeReachable.rfl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsEdgeR
eachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k : ℕ} {u : V}, G.IsEdgeReachable k 
u u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.rfl`：∀ {V : Type u} {G : SimpleGraph V} {u : V}, G
.Reachable u u
-/
protected lemma IsEdgeReachable.rfl {u : V} : G.IsEdgeReachable k u u := fun _ _ ↦ .rfl
/-
**SimpleGraph.IsEdgeReachable.refl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsEdge
Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k : ℕ} (u : V), G.IsEdgeReachable k 
u u
参数：u : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsEdgeReachable.rfl`：∀ {V : Type u_1} {G : SimpleGraph V} {k
 : ℕ} {u : V}, G.IsEdgeReachable k u u
-/
protected lemma IsEdgeReachable.refl (u : V) : G.IsEdgeReachable k u u := .rfl

@[symm]
/-
**SimpleGraph.IsEdgeReachable.symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsEdge
Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k : ℕ} {u v : V}, G.IsEdgeReachable 
k u v → G.IsEdgeReachable k v u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
-/
lemma IsEdgeReachable.symm (h : G.IsEdgeReachable k u v) : G.IsEdgeReachable k v u :=
  fun _ hk ↦ (h hk).symm
/-
**SimpleGraph.isEdgeReachable_comm** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isEdgeReachable_comm : G.IsEdgeReachable k u v ↔ G.IsEdgeReachable k v u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsEdgeReachable.symm`：∀ {V : Type u_1} {G : SimpleGraph V} {
k : ℕ} {u v : V}, G.IsEdgeReachable k u v → G.IsEdgeReachable k v u
-/
lemma isEdgeReachable_comm : G.IsEdgeReachable k u v ↔ G.IsEdgeReachable k v u :=
  ⟨.symm, .symm⟩

@[trans]
/-
**SimpleGraph.IsEdgeReachable.trans** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsEdg
eReachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k : ℕ} {u v w : V},   G.IsEdgeReacha
ble k u v → G.IsEdgeReachable k v w → G.IsEdgeReachable k u w
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.trans`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V}, G.Reachable u v → G.Reachable v w → G.Reachable u w
-/
lemma IsEdgeReachable.trans (h1 : G.IsEdgeReachable k u v) (h2 : G.IsEdgeReachable k v w) :
    G.IsEdgeReachable k u w := fun _ hk ↦ (h1 hk).trans (h2 hk)

@[gcongr]
/-
**SimpleGraph.IsEdgeReachable.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsEdge
Reachable`。
形式化陈述：∀ {V : Type u_1} {G H : SimpleGraph V} {k : ℕ} {u v : V}, G ≤ H → G.IsEdge
Reachable k u v → H.IsEdgeReachable k u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.mono`：∀ {V : Type u} {u v : V} {G G' : SimpleGraph
 V}, G ≤ G' → G.Reachable u v → G'.Reachable u v
· 使用引理 `SimpleGraph.deleteEdges_mono`：deleteEdges_mono (h : G <= H) : G.deleteEd
ges s <= H.deleteEdges s
-/
lemma IsEdgeReachable.mono (hGH : G ≤ H) (h : G.IsEdgeReachable k u v) : H.IsEdgeReachable k u v :=
  fun _ hk ↦ h hk |>.mono <| deleteEdges_mono hGH

@[gcongr]
/-
**SimpleGraph.IsEdgeReachable.anti** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsEdge
Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k l : ℕ} {u v : V}, k ≤ l → G.IsEdge
Reachable l u v → G.IsEdgeReachable k u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
-/
lemma IsEdgeReachable.anti (hkl : k ≤ l) (h : G.IsEdgeReachable l u v) : G.IsEdgeReachable k u v :=
  fun _ hk ↦ h <| by grw [← hkl]; exact hk

@[simp]
/-
**SimpleGraph.IsEdgeReachable.zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsEdge
Reachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.IsEdgeReachable 0 u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma IsEdgeReachable.zero : G.IsEdgeReachable 0 u v := by simp [IsEdgeReachable]
/-
**SimpleGraph.IsEdgeConnected.zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsEdge
Connected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, G.IsEdgeConnected 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsEdgeReachable.zero`：∀ {V : Type u_1} {G : SimpleGraph V} {
u v : V}, G.IsEdgeReachable 0 u v
-/
@[simp] protected lemma IsEdgeConnected.zero : G.IsEdgeConnected 0 := fun _ _ ↦ .zero

@[simp]
/-
**SimpleGraph.isEdgeReachable_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isEdgeReachable_one : G.IsEdgeReachable 1 u v ↔ G.Reachable u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `SimpleGraph.deleteEdges_of_subset_diagSet`：∀ {V : Type u_1} {s : Set (Sy
m2 V)} (G : SimpleGraph V), s ⊆ Sym2.diagSet → G.deleteEdges s = G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isEdgeReachable_one : G.IsEdgeReachable 1 u v ↔ G.Reachable u v := by
  simp [IsEdgeReachable, Order.lt_one_iff]

@[simp]
/-
**SimpleGraph.isEdgeConnected_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isEdgeConnected_one : G.IsEdgeConnected 1 ↔ G.Preconnected
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isEdgeConnected_one : G.IsEdgeConnected 1 ↔ G.Preconnected := by
  simp [IsEdgeConnected, Preconnected]
/-
**SimpleGraph.IsEdgeReachable.reachable** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.I
sEdgeReachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k : ℕ} {u v : V}, k ≠ 0 → G.IsEdgeRe
achable k u v → G.Reachable u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.isEdgeReachable_one`：isEdgeReachable_one : G.IsEdgeReachable
 1 u v ↔ G.Reachable u v
· 使用定理 `SimpleGraph.IsEdgeReachable.anti`：∀ {V : Type u_1} {G : SimpleGraph V} {
k l : ℕ} {u v : V}, k ≤ l → G.IsEdgeReachable l u v → G.IsEdgeReachable k u v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
lemma IsEdgeReachable.reachable (hk : k ≠ 0) (huv : G.IsEdgeReachable k u v) : G.Reachable u v :=
  isEdgeReachable_one.mp (huv.anti (Nat.one_le_iff_ne_zero.mpr hk))

@[nontriviality]
/-
**SimpleGraph.IsEdgeReachable.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.IsEdgeReachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k : ℕ} {u v : V} [Subsingleton V], G
.IsEdgeReachable k u v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.of_subsingleton`：∀ {V : Type u} {G : SimpleGraph V
} [Subsingleton V] {u v : V}, G.Reachable u v
-/
lemma IsEdgeReachable.of_subsingleton [Subsingleton V] : G.IsEdgeReachable k u v :=
  fun _ _ ↦ .of_subsingleton

@[nontriviality]
/-
**SimpleGraph.IsEdgeConnected.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.IsEdgeConnected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k : ℕ} [Subsingleton V], G.IsEdgeCon
nected k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsEdgeReachable.of_subsingleton`：∀ {V : Type u_1} {G : Simpl
eGraph V} {k : ℕ} {u v : V} [Subsingleton V], G.IsEdgeReachable k u v
-/
lemma IsEdgeConnected.of_subsingleton [Subsingleton V] : G.IsEdgeConnected k :=
  fun _ _ ↦ .of_subsingleton
/-
**SimpleGraph.IsEdgeConnected.preconnected** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.IsEdgeConnected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k : ℕ}, k ≠ 0 → G.IsEdgeConnected k 
→ G.Preconnected
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsEdgeReachable.reachable`：∀ {V : Type u_1} {G : SimpleGraph
 V} {k : ℕ} {u v : V}, k ≠ 0 → G.IsEdgeReachable k u v → G.Reachable u v
-/
lemma IsEdgeConnected.preconnected (hk : k ≠ 0) (h : G.IsEdgeConnected k) : G.Preconnected :=
  fun u v ↦ (h u v).reachable hk
/-
**SimpleGraph.IsEdgeConnected.connected** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.I
sEdgeConnected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k : ℕ} [Nonempty V], k ≠ 0 → G.IsEdg
eConnected k → G.Connected
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsEdgeConnected.preconnected`：∀ {V : Type u_1} {G : SimpleGr
aph V} {k : ℕ}, k ≠ 0 → G.IsEdgeConnected k → G.Preconnected
-/
lemma IsEdgeConnected.connected [Nonempty V] (hk : k ≠ 0) (h : G.IsEdgeConnected k) :
    G.Connected where
  preconnected := h.preconnected hk
/-
**SimpleGraph.IsEdgeReachable.le_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.I
sEdgeReachable`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k : ℕ} {u v : V} [inst : Fintype ↑(G
.neighborSet u)],   G.IsEdgeReachable k u v → u ≠ v → k ≤ G.degree u
参数：G.neighborSet u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `SimpleGraph.Reachable.exists_isPath`：∀ {V : Type u} {G : SimpleGraph V} 
{u v : V}, G.Reachable u v → ∃ p, p.IsPath
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.coe_fintypeCard`：coe_fintypeCard [Fintype s] : Fintype.card s = s.en
card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.natCast_lt_natCast`：natCast_lt_natCast {n m : Nat} : (n : Nat∞) < (
m : Nat∞) ↔ n < m
· 使用定理 `SimpleGraph.card_incidenceSet_eq_degree`：card_incidenceSet_eq_degree [De
cidableEq V] : Fintype.card (G.incidenceSet v) = G.degree v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.Walk.Nil.eq`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {p
 : G.Walk v w}, p.Nil → v = w
-/
lemma IsEdgeReachable.le_degree [Fintype (G.neighborSet u)] (h : G.IsEdgeReachable k u v)
    (huv : u ≠ v) : k ≤ G.degree u := by
  classical
  by_contra! hh
  rw [← card_incidenceSet_eq_degree, ← ENat.natCast_lt_natCast, Set.coe_fintypeCard] at hh
  obtain ⟨w, _⟩ := h hh |>.exists_isPath
  simpa using w.adj_snd <| mt Walk.Nil.eq huv
/-
**SimpleGraph.IsEdgeConnected.le_degree** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.I
sEdgeConnected`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {k : ℕ} {u : V} [inst : Fintype ↑(G.n
eighborSet u)] [Nontrivial V],   G.IsEdgeConnected k → k ≤ G.degree u
参数：G.neighborSet u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `SimpleGraph.IsEdgeReachable.le_degree`：∀ {V : Type u_1} {G : SimpleGraph
 V} {k : ℕ} {u v : V} [inst : Fintype ↑(G.neighborSet u)],   G.IsEdgeReachable k
 u v → u ≠ v → k ≤ G.degree…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma IsEdgeConnected.le_degree [Fintype (G.neighborSet u)] [Nontrivial V]
    (h : G.IsEdgeConnected k) : k ≤ G.degree u := by
  obtain ⟨v, hv⟩ := exists_ne u
  exact (h u v).le_degree hv.symm
/-
**SimpleGraph.isEdgeReachable_add_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isEdgeReachable_add_one (hk : k != 0) : G.IsEdgeReachable (k + 1) u v ↔ fo
rall e, (G.deleteEdges {e}).IsEdgeReachable k u v
参数：hk : k != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.deleteEdges_deleteEdges`：deleteEdges_deleteEdges (s s' : Set
 (Sym2 V)) : (G.deleteEdges s).deleteEdges s' = G.deleteEdges (s union s')
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `Set.encard_union_le`：encard_union_le (s t : Set α) : (s union t).encard 
<= s.encard + t.encard
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.add_lt_add_iff_right`：add_lt_add_iff_right {k : Nat∞} (h : k != ⊤) 
: n + k < m + k ↔ n < m
· 使用定理 `ENat.one_ne_top`：1 ≠ ⊤
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.deleteEdges_of_subset_diagSet`：∀ {V : Type u_1} {s : Set (Sy
m2 V)} (G : SimpleGraph V), s ⊆ Sym2.diagSet → G.deleteEdges s = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.IsEdgeReachable.reachable`：∀ {V : Type u_1} {G : SimpleGraph
 V} {k : ℕ} {u v : V}, k ≠ 0 → G.IsEdgeReachable k u v → G.Reachable u v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_sdiff_self_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ 
s → insert a (s \ {a}) = s
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.encard_sdiff_singleton_add_one`：encard_sdiff_singleton_add_one (h : 
a in s) : (s \ {a}).encard + 1 = s.encard
-/
lemma isEdgeReachable_add_one (hk : k ≠ 0) :
    G.IsEdgeReachable (k + 1) u v ↔ ∀ e, (G.deleteEdges {e}).IsEdgeReachable k u v := by
  refine ⟨fun h e s hk ↦ ?_, fun h s hs ↦ ?_⟩
  · rw [deleteEdges_deleteEdges, Set.union_comm]
    apply h
    grw [Set.encard_union_le, Set.encard_singleton]
    exact ENat.add_lt_add_iff_right ENat.one_ne_top |>.mpr hk
  obtain rfl | ⟨e, he⟩ := s.eq_empty_or_nonempty
  · simpa using (h s(u, u)).reachable hk
  · rw [← Set.insert_sdiff_self_of_mem he, Set.insert_eq, ← deleteEdges_deleteEdges]
    refine h e <| ENat.add_lt_add_iff_right ENat.one_ne_top |>.mp ?_
    rwa [Set.encard_sdiff_singleton_add_one he]
/-
**SimpleGraph.isEdgeConnected_add_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isEdgeConnected_add_one (hk : k != 0) : G.IsEdgeConnected (k + 1) ↔ forall
 e, (G.deleteEdges {e}).IsEdgeConnected k
参数：hk : k != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `SimpleGraph.isEdgeReachable_add_one`：isEdgeReachable_add_one (hk : k != 
0) : G.IsEdgeReachable (k + 1) u v ↔ forall e, (G.deleteEdges {e}).IsEdgeReachab
le k u v
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isEdgeConnected_add_one (hk : k ≠ 0) :
    G.IsEdgeConnected (k + 1) ↔ ∀ e, (G.deleteEdges {e}).IsEdgeConnected k := by
  simp [IsEdgeConnected, isEdgeReachable_add_one hk, forall_comm (α := Sym2 _)]
/-
**SimpleGraph.IsBridge.not_isEdgeReachable_two** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.IsBridge`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v : V}, G.IsBridge s(u, v) → ¬G.Is
EdgeReachable 2 u v
参数：u, v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Set.encard_singleton`：∀ {α : Type u_1} (e : α), {e}.encard = 1
· 使用定理 `Nat.one_lt_ofNat`：one_lt_ofNat : 1 < (ofNat(n) : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma IsBridge.not_isEdgeReachable_two (huv : G.IsBridge s(u, v)) : ¬ G.IsEdgeReachable 2 u v :=
  fun hc ↦ huv <| hc <| Set.encard_singleton _ |>.trans_lt Nat.one_lt_ofNat

/-- An edge is a bridge iff its endpoints are not 2-edge-reachable.

The forward direction of this is true without assuming `u` and `v` are adjacent.
See `IsBridge.not_isEdgeReachable_two`. -/
/-
**SimpleGraph.isBridge_iff_not_isEdgeReachable_two** 是 Mathlib 中的一个引理，位于命名空间 `Si
mpleGraph`。
形式化陈述：isBridge_iff_not_isEdgeReachable_two (huv : G.Adj u v) : G.IsBridge s(u, v
) ↔ ¬G.IsEdgeReachable 2 u v
参数：huv : G.Adj u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsBridge.not_isEdgeReachable_two`：∀ {V : Type u_1} {G : Simp
leGraph V} {u v : V}, G.IsBridge s(u, v) → ¬G.IsEdgeReachable 2 u v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SimpleGraph.isEdgeReachable_one`：isEdgeReachable_one : G.IsEdgeReachable
 1 u v ↔ G.Reachable u v
· 使用定理 `SimpleGraph.Adj.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V},
 G.Adj u v → G.Reachable u v
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENat.lt_natCast_add_one_iff`：lt_natCast_add_one_iff {m : Nat∞} {n : Nat}
 : m < n + 1 ↔ m <= n
· 使用定理 `Set.encard_eq_one`：encard_eq_one : s.encard = 1 ↔ exists x, s = {x}
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `SimpleGraph.deleteEdges_adj`：∀ {V : Type u_1} {v w : V} {G : SimpleGraph
 V} {s : Set (Sym2 V)}, (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
An edge is a bridge iff its endpoints are not 2-edge-reachable.

The forward direction of this is true without assuming `u` and `v` are adjacent.
See `IsBridge.not_isEdgeReachable_two`.
-/
lemma isBridge_iff_not_isEdgeReachable_two (huv : G.Adj u v) :
    G.IsBridge s(u, v) ↔ ¬G.IsEdgeReachable 2 u v := by
  refine ⟨fun h ↦ h.not_isEdgeReachable_two, fun hc hr ↦ hc fun s hs₂ ↦ ?_⟩
  by_cases! hs₁ : s.encard ≠ (1 : ℕ)
  · apply G.isEdgeReachable_one.mpr huv.reachable
    exact lt_of_le_of_ne (ENat.lt_natCast_add_one_iff.mp hs₂) hs₁
  obtain ⟨x, rfl⟩ := s.encard_eq_one.mp hs₁
  obtain rfl | hx := eq_or_ne s(u, v) x
  · exact hr
  · exact deleteEdges_adj.mpr ⟨huv, hx⟩ |>.reachable

@[deprecated (since := "2026-05-16")]
alias isBridge_iff_adj_and_not_isEdgeConnected_two := isBridge_iff_not_isEdgeReachable_two
/-
**SimpleGraph.isEdgeReachable_two** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isEdgeReachable_two : G.IsEdgeReachable 2 u v ↔ forall e, (G.deleteEdges {
e}).Reachable u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isEdgeReachable_two : G.IsEdgeReachable 2 u v ↔ ∀ e, (G.deleteEdges {e}).Reachable u v := by
  simp [isEdgeReachable_add_one]

/-- A graph is 2-edge-connected iff it has no bridge. -/
-- TODO: This should be `G.IsEdgeConnected 2 ↔ ∀ e, ¬G.IsBridge e` after
-- https://github.com/leanprover-community/mathlib4/pull/32583
/-
**SimpleGraph.isEdgeConnected_two** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：isEdgeConnected_two : G.IsEdgeConnected 2 ↔ forall e, (G.deleteEdges {e}).
Preconnected
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isEdgeConnected_two : G.IsEdgeConnected 2 ↔ ∀ e, (G.deleteEdges {e}).Preconnected := by
  simp [isEdgeConnected_add_one]
/-
**SimpleGraph.exists_adj_isEdgeReachable_two** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGr
aph`。
形式化陈述：exists_adj_isEdgeReachable_two (hne : u != v) (h : G.IsEdgeReachable 2 u v
) : exists w : V, G.Adj u w ∧ G.IsEdgeReachable 2 u w
参数：hne : u != v；h : G.IsEdgeReachable 2 u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Reachable.exists_isPath`：∀ {V : Type u} {G : SimpleGraph V} 
{u v : V}, G.Reachable u v → ∃ p, p.IsPath
· 使用定理 `SimpleGraph.IsEdgeReachable.reachable`：∀ {V : Type u_1} {G : SimpleGraph
 V} {k : ℕ} {u v : V}, k ≠ 0 → G.IsEdgeReachable k u v → G.Reachable u v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `SimpleGraph.Reachable.trans`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V}, G.Reachable u v → G.Reachable v w → G.Reachable u w
· 使用定理 `SimpleGraph.Reachable.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
, G.Reachable u v → G.Reachable v u
· 使用定理 `SimpleGraph.Walk.reachable`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}
 (p : G.Walk u v), G.Reachable u v
· 使用定理 `SimpleGraph.Walk.IsPath.eq_snd_of_mem_edges`：∀ {V : Type u} {G : SimpleG
raph V} {u v w : V} {p : G.Walk u v}, p.IsPath → s(u, w) ∈ p.edges → w = p.snd
· 使用定理 `SimpleGraph.Walk.IsPath.tail`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} {p : G.Walk u v}, p.IsPath → p.tail.IsPath
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.IsPath.getVert_eq_start_iff_of_not_nil`：∀ {V : Type u} 
{G : SimpleGraph V} {u w : V} {i : ℕ} {p : G.Walk u w}, p.IsPath → ¬p.Nil → (p.g
etVert i = u ↔ i = 0)
· 使用引理 `SimpleGraph.Walk.not_nil_of_ne`：not_nil_of_ne {p : G.Walk v w} : v != w 
-> ¬ p.Nil
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_tail`：∀ {V : Type u} {G : SimpleGraph V} {u v :
 V} {n : ℕ} (p : G.Walk u v), p.tail.getVert n = p.getVert (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.deleteEdges_adj`：∀ {V : Type u_1} {v w : V} {G : SimpleGraph
 V} {s : Set (Sym2 V)}, (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Set.subsingleton_iff_singleton`：subsingleton_iff_singleton {x} (hx : x i
n s) : s.Subsingleton ↔ s = {x}
· 使用定理 `Set.encard_le_one_iff_subsingleton`：encard_le_one_iff_subsingleton : s.e
ncard <= 1 ↔ s.Subsingleton
· 使用定理 `Order.le_of_lt_succ`：le_of_lt_succ {a b : α} : a < succ b -> a <= b
-/
lemma exists_adj_isEdgeReachable_two (hne : u ≠ v) (h : G.IsEdgeReachable 2 u v) :
    ∃ w : V, G.Adj u w ∧ G.IsEdgeReachable 2 u w := by
  obtain ⟨w, hw⟩ := h.reachable (by simp) |>.exists_isPath
  have : G.Adj u w.snd := Walk.adj_snd (by grind [Walk.not_nil_of_ne])
  refine ⟨w.snd, this, fun s hs ↦ ?_⟩
  by_cases! h' : s = {s(u, w.snd)}
  · subst h'
    refine Reachable.trans (h hs) <| w.tail.toDeleteEdge _ (fun hh ↦ ?_) |>.reachable.symm
    have := hw.tail.eq_snd_of_mem_edges (Sym2.eq_swap ▸ hh)
    simp only [Walk.getVert_tail, Nat.reduceAdd] at this
    simpa using hw.getVert_eq_start_iff_of_not_nil (Walk.not_nil_of_ne hne) |>.mp this.symm
  · refine Walk.reachable <| Walk.cons (deleteEdges_adj.mpr ⟨this, ?_⟩) Walk.nil
    contrapose h'
    refine (Set.subsingleton_iff_singleton h').mp ?_
    exact Set.encard_le_one_iff_subsingleton.mp (Order.le_of_lt_succ hs)

/-!
### 2-reachability

In this section, we prove results about 2-connected components of a graph, but without naming them.
-/

namespace Walk
variable {w : G.Walk u v}

/-
**SimpleGraph.Walk.IsTrail.isEdgeReachable_two_of_isEdgeReachable_two_aux** 是 Ma
thlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsTrail.isEdgeReachable_two_of_isEdgeReachable_two_aux (hw : w.IsTrail)
    (huv : G.IsEdgeReachable 2 u v) (huy : x ∈ w.support) : G.IsEdgeReachable 2 u x := by
  classical
  contrapose huy
  obtain ⟨e, he⟩ := by simpa [isEdgeReachable_two] using huy
  have he' : ¬ (G.deleteEdges {e}).Reachable v x := fun hvy ↦
    he <| (isEdgeReachable_two.1 huv _).trans hvy
  exact fun hy ↦ hw.disjoint_edges_takeUntil_dropUntil hy
    ((w.takeUntil x _).mem_edges_of_not_reachable_deleteEdges he)
    (by simpa using (w.dropUntil x _).reverse.mem_edges_of_not_reachable_deleteEdges he')

/-- Vertices of a trail with 2-edge reachable endpoints are 2-edge reachable. -/
/-
**SimpleGraph.Walk.IsTrail.isEdgeReachable_two_of_isEdgeReachable_two** 是 Mathli
b 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v x y : V} {w : G.Walk u v},   w.I
sTrail → G.IsEdgeReachable 2 u v → x ∈ w.support → y ∈ w.support → G.IsEdgeReach
able 2 x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsEdgeReachable.trans`：∀ {V : Type u_1} {G : SimpleGraph V} 
{k : ℕ} {u v w : V},   G.IsEdgeReachable k u v → G.IsEdgeReachable k v w → G.IsE
dgeReachable k u w
· 使用定理 `SimpleGraph.IsEdgeReachable.symm`：∀ {V : Type u_1} {G : SimpleGraph V} {
k : ℕ} {u v : V}, G.IsEdgeReachable k u v → G.IsEdgeReachable k v u
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
.0.SimpleGraph.Walk.IsTrail.isEdgeReachable_two_of_isEdgeReachable_two_aux`：∀ {V
 : Type u_1} {G : SimpleGraph V} {u v x : V} {w : G.Walk u v},   w.IsTrail → G.I
sEdgeReachable 2 u v → x ∈ w.support → G.IsEdgeReachable…

--- 原说明 ---
Vertices of a trail with 2-edge reachable endpoints are 2-edge reachable.
-/
lemma IsTrail.isEdgeReachable_two_of_isEdgeReachable_two (hw : w.IsTrail)
    (huv : G.IsEdgeReachable 2 u v) (hx : x ∈ w.support) (hy : y ∈ w.support) :
    G.IsEdgeReachable 2 x y :=
  (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv hx).symm.trans
    (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv hy)

/-- A trail doesn't go through a vertex that is not 2-edge-reachable from its 2-edge-reachable
endpoints. -/
@[deprecated IsTrail.isEdgeReachable_two_of_isEdgeReachable_two (since := "2026-04-01")]
/-
**SimpleGraph.Walk.IsTrail.not_mem_edges_of_not_isEdgeReachable_two** 是 Mathlib 
中的一个定理，位于命名空间 `SimpleGraph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u v x : V} {w : G.Walk u v},   w.IsT
rail → G.IsEdgeReachable 2 u v → ¬G.IsEdgeReachable 2 u x → x ∉ w.support
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
.0.SimpleGraph.Walk.IsTrail.isEdgeReachable_two_of_isEdgeReachable_two_aux`：∀ {V
 : Type u_1} {G : SimpleGraph V} {u v x : V} {w : G.Walk u v},   w.IsTrail → G.I
sEdgeReachable 2 u v → x ∈ w.support → G.IsEdgeReachable…

--- 原说明 ---
A trail doesn't go through a vertex that is not 2-edge-reachable from its 2-edge
-reachable
endpoints.
-/
lemma IsTrail.not_mem_edges_of_not_isEdgeReachable_two (hw : w.IsTrail)
    (huv : G.IsEdgeReachable 2 u v) (huy : ¬ G.IsEdgeReachable 2 u x) : x ∉ w.support :=
  mt (hw.isEdgeReachable_two_of_isEdgeReachable_two_aux huv) huy

/-- Vertices of a closed trail are 2-edge reachable. -/
/-
**SimpleGraph.Walk.IsTrail.isEdgeReachable_two** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {u x y : V} {w : G.Walk u u},   w.IsT
rail → x ∈ w.support → y ∈ w.support → G.IsEdgeReachable 2 x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsTrail.isEdgeReachable_two_of_isEdgeReachable_two`：∀ {
V : Type u_1} {G : SimpleGraph V} {u v x y : V} {w : G.Walk u v},   w.IsTrail → 
G.IsEdgeReachable 2 u v → x ∈ w.support → y ∈ w.support →…
· 使用定理 `SimpleGraph.IsEdgeReachable.rfl`：∀ {V : Type u_1} {G : SimpleGraph V} {k
 : ℕ} {u : V}, G.IsEdgeReachable k u u

--- 原说明 ---
Vertices of a closed trail are 2-edge reachable.
-/
lemma IsTrail.isEdgeReachable_two {w : G.Walk u u} (hw : w.IsTrail) (hx : x ∈ w.support)
    (hy : y ∈ w.support) : G.IsEdgeReachable 2 x y :=
  hw.isEdgeReachable_two_of_isEdgeReachable_two .rfl hx hy

end SimpleGraph.Walk

