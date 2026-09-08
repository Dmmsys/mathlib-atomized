/-
Copyright (c) 2026 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Rify

/-!
# The Zarankiewicz function

This file defines the **Zarankiewicz function** in terms of bipartite graphs.
-/

public section

open Finset Fintype

namespace SimpleGraph

/-- The **Zarankiewicz function** of natural numbers `m`, `n`, `s`, and `t` is the maximum
number of edges in a `completeBipartiteGraph (Fin s) (Fin t)`-free bipartite graph with parts of
size `m` and `n`.

This is the *extremal graph theory* version of the **Zarankiewicz function**. -/
/-
**SimpleGraph.zarankiewicz** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：zarankiewicz (m n s t : Nat) : Nat
参数：m n s t : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Zarankiewicz function** of natural numbers `m`, `n`, `s`, and `t` is the m
aximum
number of edges in a `completeBipartiteGraph (Fin s) (Fin t)`-free bipartite gra
ph with parts of
size `m` and `n`.

This is the *extremal graph theory* version of the **Zarankiewicz function**.
-/
noncomputable def zarankiewicz (m n s t : ℕ) : ℕ :=
  open Classical in
  sup { G : SimpleGraph (Fin m ⊕ Fin n) | G ≤ completeBipartiteGraph (Fin m) (Fin n)
    ∧ (completeBipartiteGraph (Fin s) (Fin t)).Free G} (#·.edgeFinset)

variable {m n s t : ℕ} {V W α β : Type*} [Fintype V] [Fintype W] [Fintype α] [Fintype β]

open Classical in
/-
**SimpleGraph.zarankiewicz_of_fintypeCard_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：zarankiewicz_of_fintypeCard_eq (hm : card V = m) (hn : card W = n) (hs : c
ard α = s) (ht : card β = t) : zarankiewicz m n s t = sup { G : SimpleGraph (V o
plus W) | G <= completeBipartiteGraph V W ∧ (completeBipartiteGraph α β).Free G}
 (#·.edgeFinset)
参数：hm : card V = m；hn : card W = n；hs : card α = s；ht : card β = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz.0.Simpl
eGraph.zarankiewicz.eq_1`：∀ (m n s t : ℕ),   SimpleGraph.zarankiewicz m n s t = 
    {G | G ≤ completeBipartiteGraph (Fin m) (Fin n) ∧ (completeBipartiteGraph (F
in s) …
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `SimpleGraph.Iso.card_edgeFinset_eq`：card_edgeFinset_eq (f : G ≃g G') [Fi
ntype G.edgeSet] [Fintype G'.edgeSet] : #G.edgeFinset = #G'.edgeFinset
· 使用定理 `Finset.mem_filter_univ`：mem_filter_univ {p : α -> Prop} [DecidablePred p
] : forall x, x in univ.filter p ↔ p x
· 使用定理 `SimpleGraph.map_le_iff_le_comap`：map_le_iff_le_comap (f : V ↪ W) (G : Si
mpleGraph V) (G' : SimpleGraph W) : G.map f <= G' ↔ G <= G'.comap f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.comap_adj`：∀ {V : Type u_1} {W : Type u_2} {u v : V} {G : Si
mpleGraph W} {f : V → W},   (SimpleGraph.comap f G).Adj u v ↔ G.Adj (f u) (f v)
· 使用定理 `SimpleGraph.Embedding.map_adj_iff`：∀ {V : Type u_1} {W : Type u_2} {G : 
SimpleGraph V} {G' : SimpleGraph W} (f : G ↪g G') {v w : V},   G'.Adj (f v) (f w
) ↔ G.Adj v w
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
· 使用定理 `SimpleGraph.free_congr`：free_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A.Free 
B ↔ H.Free G
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
-/
theorem zarankiewicz_of_fintypeCard_eq
    (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) :
    zarankiewicz m n s t =
      sup { G : SimpleGraph (V ⊕ W) | G ≤ completeBipartiteGraph V W
        ∧ (completeBipartiteGraph α β).Free G} (#·.edgeFinset) := by
  let e₁ := completeBipartiteGraphCongr
    (Fintype.equivFinOfCardEq hm) (Fintype.equivFinOfCardEq hn)
  let K := completeBipartiteGraph (Fin s) (Fin t)
  let e₂ := completeBipartiteGraphCongr
    (Fintype.equivFinOfCardEq hs) (Fintype.equivFinOfCardEq ht)
  rw [zarankiewicz, le_antisymm_iff]
  and_intros
  on_goal 1 =>
    let e₁ := e₁.symm
    let K := completeBipartiteGraph α β
    let e₂ := e₂.symm
  all_goals
    simp_rw [Finset.sup_le_iff, mem_filter, mem_univ, true_and]
    intro G ⟨h_le, h_free⟩
    simp_rw [Iso.card_edgeFinset_eq (.map e₁.toEquiv G)]
    have h' : G.map e₁.toEquiv.toEmbedding ∈ univ.filter fun G ↦
        G ≤ completeBipartiteGraph _ _ ∧ K.Free G := by
      rw [mem_filter_univ, map_le_iff_le_comap]
      refine ⟨fun _ _ hadj ↦ ?_, ?_⟩
      · replace h_le := h_le hadj
        rw [← Embedding.map_adj_iff e₁.toEmbedding, ← comap_adj] at h_le
        exact h_le
      · rw [Function.Embedding.coeFn_mk, ← free_congr e₂ (.map e₁.toEquiv G)]
        exact h_free
    have h_le_sup := @le_sup _ _ _ _ _ (#·.edgeFinset) (G.map e₁.toEquiv.toEmbedding) h'
    simp_rw [← card_coe, mem_edgeFinset] at h_le_sup ⊢
    exact h_le_sup

/-- `zarankiewicz m n s t` is at most `x` if and only if every
`completeBipartiteGraph α β`-free bipartite graph `G` has at most `x` edges. -/
/-
**SimpleGraph.zarankiewicz_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：zarankiewicz_le_iff (hm : card V = m) (hn : card W = n) (hs : card α = s) 
(ht : card β = t) (x : Nat) : zarankiewicz m n s t <= x ↔ forall ⦃G : SimpleGrap
h (V oplus W)⦄ [DecidableRel G.Adj], G <= completeBipartiteGraph V W -> (complet
eBipartiteGraph α β).Free G -> #G.edgeFinset <= x
参数：hm : card V = m；hn : card W = n；hs : card α = s；ht : card β = t；x : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.zarankiewicz_of_fintypeCard_eq`：zarankiewicz_of_fintypeCard_
eq (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) : zar
ankiewicz m n s t = sup { G : Si…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LE.le.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LE α], b ≤ a → b =
 c → c ≤ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)

--- 原说明 ---
`zarankiewicz m n s t` is at most `x` if and only if every
`completeBipartiteGraph α β`-free bipartite graph `G` has at most `x` edges.
-/
theorem zarankiewicz_le_iff
    (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) (x : ℕ) :
    zarankiewicz m n s t ≤ x ↔
      ∀ ⦃G : SimpleGraph (V ⊕ W)⦄ [DecidableRel G.Adj], G ≤ completeBipartiteGraph V W →
        (completeBipartiteGraph α β).Free G → #G.edgeFinset ≤ x := by
  simp_rw [zarankiewicz_of_fintypeCard_eq hm hn hs ht,
    Finset.sup_le_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun h _ _ h_le h_free ↦ (h _ ⟨h_le, h_free⟩).trans_eq' <| by convert rfl,
    fun h _ ⟨h_le, h_free⟩ ↦ by convert h h_le h_free⟩

/-- `zarankiewicz m n s t` is greater than `x` if and only if there
exists a `completeBipartiteGraph α β`-free bipartite graph `G` with more than `x` edges. -/
/-
**SimpleGraph.lt_zarankiewicz_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：lt_zarankiewicz_iff (hm : card V = m) (hn : card W = n) (hs : card α = s) 
(ht : card β = t) (x : Nat) : x < zarankiewicz m n s t ↔ exists G : SimpleGraph 
(V oplus W), exists _ : DecidableRel G.Adj, G <= completeBipartiteGraph V W ∧ (c
ompleteBipartiteGraph α β).Free G ∧ x < #G.edgeFinset
参数：hm : card V = m；hn : card W = n；hs : card α = s；ht : card β = t；x : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.zarankiewicz_of_fintypeCard_eq`：zarankiewicz_of_fintypeCard_
eq (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) : zar
ankiewicz m n s t = sup { G : Si…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)

--- 原说明 ---
`zarankiewicz m n s t` is greater than `x` if and only if there
exists a `completeBipartiteGraph α β`-free bipartite graph `G` with more than `x
` edges.
-/
theorem lt_zarankiewicz_iff
    (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) (x : ℕ) :
    x < zarankiewicz m n s t ↔
      ∃ G : SimpleGraph (V ⊕ W), ∃ _ : DecidableRel G.Adj, G ≤ completeBipartiteGraph V W ∧
        (completeBipartiteGraph α β).Free G ∧  x < #G.edgeFinset := by
  simp_rw [zarankiewicz_of_fintypeCard_eq hm hn hs ht,
    Finset.lt_sup_iff, mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨_, ⟨h_le, h_free⟩, h_lt⟩ ↦ ⟨_, _, h_le, h_free, by convert h_lt⟩,
    fun ⟨_, _, ⟨h_le, h_free, h_lt⟩⟩ ↦ ⟨_, ⟨h_le, h_free⟩, h_lt.trans_eq <| by convert rfl⟩⟩

variable {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]

@[inherit_doc zarankiewicz_le_iff]
/-
**SimpleGraph.zarankiewicz_le_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：zarankiewicz_le_iff_of_nonneg (hm : card V = m) (hn : card W = n) (hs : ca
rd α = s) (ht : card β = t) {x : R} (h : 0 <= x) : zarankiewicz m n s t <= x ↔ f
orall ⦃G : SimpleGraph (V oplus W)⦄ [DecidableRel G.Adj], G <= completeBipartite
Graph V W -> (completeBipartiteGraph α β).Free G -> #G.edgeFinset <= x
参数：hm : card V = m；hn : card W = n；hs : card α = s；ht : card β = t；h : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.zarankiewicz_le_iff`：zarankiewicz_le_iff (hm : card V = m) (
hn : card W = n) (hs : card α = s) (ht : card β = t) (x : Nat) : zarankiewicz m 
n s t <= x ↔ forall ⦃…
-/
theorem zarankiewicz_le_iff_of_nonneg
    (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) {x : R} (h : 0 ≤ x) :
    zarankiewicz m n s t ≤ x ↔
      ∀ ⦃G : SimpleGraph (V ⊕ W)⦄ [DecidableRel G.Adj], G ≤ completeBipartiteGraph V W →
        (completeBipartiteGraph α β).Free G → #G.edgeFinset ≤ x := by
  simp_rw [← Nat.le_floor_iff h]
  exact zarankiewicz_le_iff hm hn hs ht ⌊x⌋₊

@[inherit_doc lt_zarankiewicz_iff]
/-
**SimpleGraph.lt_zarankiewicz_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph`。
形式化陈述：lt_zarankiewicz_iff_of_nonneg (hm : card V = m) (hn : card W = n) (hs : ca
rd α = s) (ht : card β = t) {x : R} (h : 0 <= x) : x < zarankiewicz m n s t ↔ ex
ists G : SimpleGraph (V oplus W), exists _ : DecidableRel G.Adj, G <= completeBi
partiteGraph V W ∧ (completeBipartiteGraph α β).Free G ∧ x < #G.edgeFinset
参数：hm : card V = m；hn : card W = n；hs : card α = s；ht : card β = t；h : 0 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.floor_lt`：floor_lt (ha : 0 <= a) : ⌊a⌋₊ < n ↔ a < n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.lt_zarankiewicz_iff`：lt_zarankiewicz_iff (hm : card V = m) (
hn : card W = n) (hs : card α = s) (ht : card β = t) (x : Nat) : x < zarankiewic
z m n s t ↔ exists G …
-/
theorem lt_zarankiewicz_iff_of_nonneg
    (hm : card V = m) (hn : card W = n) (hs : card α = s) (ht : card β = t) {x : R} (h : 0 ≤ x) :
    x < zarankiewicz m n s t ↔
      ∃ G : SimpleGraph (V ⊕ W), ∃ _ : DecidableRel G.Adj, G ≤ completeBipartiteGraph V W ∧
        (completeBipartiteGraph α β).Free G ∧  x < #G.edgeFinset := by
  simp_rw [← Nat.floor_lt h]
  exact lt_zarankiewicz_iff hm hn hs ht ⌊x⌋₊

open Classical in
/-- The Zarankiewicz function is at most the corresponding extremal number. -/
/-
**SimpleGraph.zarankiewicz_le_extremalNumber** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：zarankiewicz_le_extremalNumber (hs : card α = s) (ht : card β = t) : zaran
kiewicz m n s t <= extremalNumber (m + n) (completeBipartiteGraph α β)
参数：hs : card α = s；ht : card β = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `SimpleGraph.Iso.card_edgeFinset_eq`：card_edgeFinset_eq (f : G ≃g G') [Fi
ntype G.edgeSet] [Fintype G'.edgeSet] : #G.edgeFinset = #G'.edgeFinset
· 使用定理 `SimpleGraph.card_edgeFinset_le_extremalNumber`：card_edgeFinset_le_extrem
alNumber (h : H.Free G) : #G.edgeFinset <= extremalNumber (card V) H
· 使用定理 `SimpleGraph.Free.congr_right`：∀ {α : Type u_4} {β : Type u_5} {γ : Type 
u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}   (e₂ : B ≃g C)
, A.Free C → A.Fre…
· 使用定理 `SimpleGraph.Free.congr_left`：∀ {α : Type u_4} {β : Type u_5} {γ : Type u
_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}   (e₁ : A ≃g B),
 B.Free C → A.Fre…

--- 原说明 ---
The Zarankiewicz function is at most the corresponding extremal number.
-/
theorem zarankiewicz_le_extremalNumber (hs : card α = s) (ht : card β = t) :
    zarankiewicz m n s t ≤ extremalNumber (m + n) (completeBipartiteGraph α β) := by
  conv =>
    enter [2, 1]
    rw [← Fintype.card_fin (m + n)]
  simp_rw [zarankiewicz, Finset.sup_le_iff, mem_filter, mem_univ, true_and]
  intro B ⟨_, h⟩
  rw [(Iso.map finSumFinEquiv B).card_edgeFinset_eq]
  refine card_edgeFinset_le_extremalNumber <|
    (h.congr_left ?_).congr_right (Iso.map finSumFinEquiv B).symm
  exact completeBipartiteGraphCongr
    (Fintype.equivFinOfCardEq hs) (Fintype.equivFinOfCardEq ht)

/-- The symmetric Zarankiewicz function is at least twice a corresponding extremal number. -/
/-
**SimpleGraph.two_mul_extremalNumber_le_zarankiewicz_symm** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph`。
形式化陈述：two_mul_extremalNumber_le_zarankiewicz_symm [Nonempty α] [Nonempty β] (hs 
: card α = s) (ht : card β = t) : 2 * extremalNumber n (completeBipartiteGraph α
 β) <= zarankiewicz n n s t
参数：hs : card α = s；ht : card β = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `SimpleGraph.extremalNumber_le_iff_of_nonneg`：extremalNumber_le_iff_of_no
nneg (H : SimpleGraph W) {m : R} (h : 0 <= m) : extremalNumber (card V) H <= m ↔
 forall ⦃G : SimpleGraph V⦄ [Deci…
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Finset.le_sup_of_le`：le_sup_of_le {b : β} (hb : b in s) (h : a <= f b) :
 a <= s.sup f
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The symmetric Zarankiewicz function is at least twice a corresponding extremal n
umber.
-/
theorem two_mul_extremalNumber_le_zarankiewicz_symm
    [Nonempty α] [Nonempty β] (hs : card α = s) (ht : card β = t) :
    2 * extremalNumber n (completeBipartiteGraph α β) ≤ zarankiewicz n n s t := by
  conv =>
    enter [1, 2, 1]
    rw [← Fintype.card_fin n]
  rify
  rw [← le_div_iff₀' (by positivity), extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro G _ h
  rw [le_div_iff₀' (by positivity), ← Nat.cast_two, ← Nat.cast_mul, Nat.cast_le]
  apply Finset.le_sup_of_le (b := G.bipartiteDoubleCover)
  · simp_rw [mem_filter, mem_univ, true_and]
    refine ⟨bipartiteDoubleCover_le, ?_⟩
    contrapose! h
    refine completeBipartiteGraph_isContained_bipartiteDoubleCover.mp <|
      h.trans' ⟨Iso.toCopy ?_⟩
    exact completeBipartiteGraphCongr
      (Fintype.equivFinOfCardEq hs) (Fintype.equivFinOfCardEq ht)
  · convert card_edgeFinset_bipartiteDoubleCover.symm.le

end SimpleGraph

