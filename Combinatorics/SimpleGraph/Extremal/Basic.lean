/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Extremal graph theory

This file introduces basic definitions for extremal graph theory, including extremal numbers.

## Main definitions

* `SimpleGraph.IsExtremal` is the predicate that `G` has the maximum number of edges of any simple
  graph, with fixed vertices, satisfying `p`.

* `SimpleGraph.extremalNumber` is the maximum number of edges in a `H`-free simple graph on `n`
  vertices.

  If `H` is contained in all simple graphs on `n` vertices, then this is `0`.
-/

@[expose] public section

assert_not_exists Field

open Finset Fintype

namespace SimpleGraph

section IsExtremal

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `G` is an extremal graph satisfying `p` if `G` has the maximum number of edges of any simple
graph, with fixed vertices, satisfying `p`. -/
/-
**SimpleGraph.IsExtremal** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：IsExtremal (G : SimpleGraph V) [DecidableRel G.Adj] (p : SimpleGraph V -> 
Prop)
参数：G : SimpleGraph V；p : SimpleGraph V -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G` is an extremal graph satisfying `p` if `G` has the maximum number of edges o
f any simple
graph, with fixed vertices, satisfying `p`.
-/
def IsExtremal (G : SimpleGraph V) [DecidableRel G.Adj] (p : SimpleGraph V → Prop) :=
  p G ∧ ∀ ⦃G' : SimpleGraph V⦄ [DecidableRel G'.Adj], p G' → #G'.edgeFinset ≤ #G.edgeFinset
/-
**SimpleGraph.IsExtremal.prop** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsExtremal`
。
形式化陈述：∀ {V : Type u_1} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : Decidabl
eRel G.Adj] {p : SimpleGraph V → Prop},   G.IsExtremal p → p G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsExtremal.prop {p : SimpleGraph V → Prop} (h : G.IsExtremal p) : p G := h.1

/-- If one simple graph satisfies `p`, then there exists an extremal graph satisfying `p`. -/
/-
**SimpleGraph.exists_isExtremal_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：exists_isExtremal_iff_exists (p : SimpleGraph V -> Prop) : (exists G : Sim
pleGraph V, exists _ : DecidableRel G.Adj, G.IsExtremal p) ↔ exists G, p G
参数：p : SimpleGraph V -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.exists_max_image`：exists_max_image (s : Finset β) (f : β -> α) (h
 : s.Nonempty) : exists x in s, forall x' in s, f x' <= f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)

--- 原说明 ---
If one simple graph satisfies `p`, then there exists an extremal graph satisfyin
g `p`.
-/
theorem exists_isExtremal_iff_exists (p : SimpleGraph V → Prop) :
    (∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj, G.IsExtremal p) ↔ ∃ G, p G := by
  classical
  refine ⟨fun ⟨_, _, h⟩ ↦ ⟨_, h.1⟩, fun ⟨G, hp⟩ ↦ ?_⟩
  obtain ⟨G', hp', h⟩ := by
    apply exists_max_image { G | p G } (#·.edgeFinset)
    use G, by simpa using hp
  use G', inferInstanceAs (DecidableRel G'.Adj)
  exact ⟨by simpa using hp', fun _ _ hp ↦ by convert! h _ (by simpa using hp)⟩

/-- If `H` has at least one edge, then there exists an extremal `H.Free` graph. -/
/-
**SimpleGraph.exists_isExtremal_free** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：exists_isExtremal_free {W : Type*} {H : SimpleGraph W} (h : H != ⊥) : exis
ts G : SimpleGraph V, exists _ : DecidableRel G.Adj, G.IsExtremal H.Free
参数：h : H != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.exists_isExtremal_iff_exists`：exists_isExtremal_iff_exists (
p : SimpleGraph V -> Prop) : (exists G : SimpleGraph V, exists _ : DecidableRel 
G.Adj, G.IsExtremal p) ↔ exist…
· 使用引理 `SimpleGraph.free_bot`：free_bot (h : A != ⊥) : A.Free (⊥ : SimpleGraph β)

--- 原说明 ---
If `H` has at least one edge, then there exists an extremal `H.Free` graph.
-/
theorem exists_isExtremal_free {W : Type*} {H : SimpleGraph W} (h : H ≠ ⊥) :
    ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj, G.IsExtremal H.Free :=
  (exists_isExtremal_iff_exists H.Free).mpr ⟨⊥, free_bot h⟩

open scoped Classical in
/-
**SimpleGraph.IsExtremal.le_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsExtr
emal`。
形式化陈述：∀ {V : Type u_1} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : Decidabl
eRel G.Adj] {p : SimpleGraph V → Prop},   G.IsExtremal p → ∀ {H : SimpleGraph V}
, p H → (G ≤ H ↔ G = H)
参数：G ≤ H ↔ G = H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.edgeFinset_inj`：edgeFinset_inj : G₁.edgeFinset = G₂.edgeFins
et ↔ G₁ = G₂
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.edgeFinset_subset_edgeFinset`：edgeFinset_subset_edgeFinset :
 G₁.edgeFinset subseteq G₂.edgeFinset ↔ G₁ <= G₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem IsExtremal.le_iff_eq
    {p : SimpleGraph V → Prop} (hG : G.IsExtremal p) {H : SimpleGraph V} (hH : p H) :
    G ≤ H ↔ G = H :=
  ⟨fun hGH ↦ edgeFinset_inj.1 <|
    eq_of_subset_of_card_le (edgeFinset_subset_edgeFinset.2 hGH) (hG.2 hH), le_of_eq⟩

end IsExtremal

section ExtremalNumber

open scoped Classical in
/-- The extremal number of a natural number `n` and a simple graph `H` is the maximum number of
edges in a `H`-free simple graph on `n` vertices.

If `H` is contained in all simple graphs on `n` vertices, then this is `0`. -/
/-
**SimpleGraph.extremalNumber** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：extremalNumber (n : Nat) {W : Type*} (H : SimpleGraph W) : Nat
参数：n : Nat；H : SimpleGraph W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extremal number of a natural number `n` and a simple graph `H` is the maximu
m number of
edges in a `H`-free simple graph on `n` vertices.

If `H` is contained in all simple graphs on `n` vertices, then this is `0`.
-/
noncomputable def extremalNumber (n : ℕ) {W : Type*} (H : SimpleGraph W) : ℕ :=
  sup { G : SimpleGraph (Fin n) | H.Free G } (#·.edgeFinset)

variable {n : ℕ} {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

open scoped Classical in
/-
**SimpleGraph.extremalNumber_of_fintypeCard_eq** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph`。
形式化陈述：extremalNumber_of_fintypeCard_eq [Fintype V] (hc : card V = n) : extremalN
umber n H = sup { G : SimpleGraph V | H.Free G } (#·.edgeFinset)
参数：hc : card V = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.extremalNumber.eq_1`：∀ (n : ℕ) {W : Type u_1} (H : SimpleGra
ph W),   SimpleGraph.extremalNumber n H = {G | H.Free G}.sup fun x => x.edgeFins
et.card
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.free_congr`：free_congr (e₁ : A ≃g H) (e₂ : B ≃g G) : A.Free 
B ↔ H.Free G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SimpleGraph.Iso.card_edgeFinset_eq`：card_edgeFinset_eq (f : G ≃g G') [Fi
ntype G.edgeSet] [Fintype G'.edgeSet] : #G.edgeFinset = #G'.edgeFinset
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem extremalNumber_of_fintypeCard_eq [Fintype V] (hc : card V = n) :
    extremalNumber n H = sup { G : SimpleGraph V | H.Free G } (#·.edgeFinset) := by
  let e := Fintype.equivFinOfCardEq hc
  rw [extremalNumber, le_antisymm_iff]
  and_intros
  on_goal 1 =>
    replace e := e.symm
  all_goals
  rw [Finset.sup_le_iff]
  intro G h
  have h' : G.map e ∈ univ.filter (H.Free ·) := by
    rw [mem_filter, ← free_congr .refl (.map e G)]
    simpa using h
  rw [Iso.card_edgeFinset_eq (.map e G)]
  convert! @le_sup _ _ _ _ {G | H.Free G} (#·.edgeFinset) _ h'

variable [Fintype V] [DecidableRel G.Adj]

/-- If `G` is `H`-free, then `G` has at most `extremalNumber (card V) H` edges. -/
/-
**SimpleGraph.card_edgeFinset_le_extremalNumber** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph`。
形式化陈述：card_edgeFinset_le_extremalNumber (h : H.Free G) : #G.edgeFinset <= extrem
alNumber (card V) H
参数：h : H.Free G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.extremalNumber_of_fintypeCard_eq`：extremalNumber_of_fintypeC
ard_eq [Fintype V] (hc : card V = n) : extremalNumber n H = sup { G : SimpleGrap
h V | H.Free G } (#·.edgeFinset)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p

--- 原说明 ---
If `G` is `H`-free, then `G` has at most `extremalNumber (card V) H` edges.
-/
theorem card_edgeFinset_le_extremalNumber (h : H.Free G) :
    #G.edgeFinset ≤ extremalNumber (card V) H := by
  rw [extremalNumber_of_fintypeCard_eq rfl]
  convert! @le_sup _ _ _ _ {G | H.Free G} (#·.edgeFinset) G (by simpa using h)

/-- If `G` has more than `extremalNumber (card V) H` edges, then `G` contains a copy of `H`. -/
/-
**SimpleGraph.IsContained.of_extremalNumber_lt_card_edgeFinset** 是 Mathlib 中的一个定
理，位于命名空间 `SimpleGraph.IsContained`。
形式化陈述：∀ {V : Type u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} [i
nst : Fintype V]   [inst_1 : DecidableRel G.Adj], SimpleGraph.extremalNumber (Fi
ntype.card V) H < G.edgeFinset.card → H.IsContained G
参数：Fintype.card V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `SimpleGraph.card_edgeFinset_le_extremalNumber`：card_edgeFinset_le_extrem
alNumber (h : H.Free G) : #G.edgeFinset <= extremalNumber (card V) H

--- 原说明 ---
If `G` has more than `extremalNumber (card V) H` edges, then `G` contains a copy
 of `H`.
-/
theorem IsContained.of_extremalNumber_lt_card_edgeFinset
    (h : extremalNumber (card V) H < #G.edgeFinset) : H ⊑ G := by
  contrapose h; push Not
  exact card_edgeFinset_le_extremalNumber h

/-- `extremalNumber (card V) H` is at most `x` if and only if every `H`-free simple graph `G` has
at most `x` edges. -/
/-
**SimpleGraph.extremalNumber_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：extremalNumber_le_iff (H : SimpleGraph W) (m : Nat) : extremalNumber (card
 V) H <= m ↔ forall ⦃G : SimpleGraph V⦄ [DecidableRel G.Adj], H.Free G -> #G.edg
eFinset <= m
参数：H : SimpleGraph W；m : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.extremalNumber_of_fintypeCard_eq`：extremalNumber_of_fintypeC
ard_eq [Fintype V] (hc : card V = n) : extremalNumber n H = sup { G : SimpleGrap
h V | H.Free G } (#·.edgeFinset)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)

--- 原说明 ---
`extremalNumber (card V) H` is at most `x` if and only if every `H`-free simple 
graph `G` has
at most `x` edges.
-/
theorem extremalNumber_le_iff (H : SimpleGraph W) (m : ℕ) :
    extremalNumber (card V) H ≤ m ↔
      ∀ ⦃G : SimpleGraph V⦄ [DecidableRel G.Adj], H.Free G → #G.edgeFinset ≤ m := by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.sup_le_iff, mem_filter_univ]
  exact ⟨fun h _ _ h' ↦ by convert! h _ h', fun h _ h' ↦ by convert! h h'⟩

/-- `extremalNumber (card V) H` is greater than `x` if and only if there exists a `H`-free simple
graph `G` with more than `x` edges. -/
/-
**SimpleGraph.lt_extremalNumber_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：lt_extremalNumber_iff (H : SimpleGraph W) (m : Nat) : m < extremalNumber (
card V) H ↔ exists G : SimpleGraph V, exists _ : DecidableRel G.Adj, H.Free G ∧ 
m < #G.edgeFinset
参数：H : SimpleGraph W；m : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.extremalNumber_of_fintypeCard_eq`：extremalNumber_of_fintypeC
ard_eq [Fintype V] (hc : card V = n) : extremalNumber n H = sup { G : SimpleGrap
h V | H.Free G } (#·.edgeFinset)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)

--- 原说明 ---
`extremalNumber (card V) H` is greater than `x` if and only if there exists a `H
`-free simple
graph `G` with more than `x` edges.
-/
theorem lt_extremalNumber_iff (H : SimpleGraph W) (m : ℕ) :
    m < extremalNumber (card V) H ↔
      ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj, H.Free G ∧ m < #G.edgeFinset := by
  simp_rw [extremalNumber_of_fintypeCard_eq rfl, Finset.lt_sup_iff, mem_filter_univ]
  exact ⟨fun ⟨_, h, h'⟩ ↦ ⟨_, _, h, h'⟩, fun ⟨_, _, h, h'⟩ ↦ ⟨_, h, by convert!
    h'⟩⟩

variable {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]

@[inherit_doc extremalNumber_le_iff]
/-
**SimpleGraph.extremalNumber_le_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：extremalNumber_le_iff_of_nonneg (H : SimpleGraph W) {m : R} (h : 0 <= m) :
 extremalNumber (card V) H <= m ↔ forall ⦃G : SimpleGraph V⦄ [DecidableRel G.Adj
], H.Free G -> #G.edgeFinset <= m
参数：H : SimpleGraph W；h : 0 <= m。
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
· 使用定理 `SimpleGraph.extremalNumber_le_iff`：extremalNumber_le_iff (H : SimpleGrap
h W) (m : Nat) : extremalNumber (card V) H <= m ↔ forall ⦃G : SimpleGraph V⦄ [De
cidableRel G.Adj], H.Fr…
-/
theorem extremalNumber_le_iff_of_nonneg (H : SimpleGraph W) {m : R} (h : 0 ≤ m) :
    extremalNumber (card V) H ≤ m ↔
      ∀ ⦃G : SimpleGraph V⦄ [DecidableRel G.Adj], H.Free G → #G.edgeFinset ≤ m := by
  simp_rw [← Nat.le_floor_iff h]
  exact extremalNumber_le_iff H ⌊m⌋₊

@[inherit_doc lt_extremalNumber_iff]
/-
**SimpleGraph.lt_extremalNumber_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph`。
形式化陈述：lt_extremalNumber_iff_of_nonneg (H : SimpleGraph W) {m : R} (h : 0 <= m) :
 m < extremalNumber (card V) H ↔ exists G : SimpleGraph V, exists _ : DecidableR
el G.Adj, H.Free G ∧ m < #G.edgeFinset
参数：H : SimpleGraph W；h : 0 <= m。
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
· 使用定理 `SimpleGraph.lt_extremalNumber_iff`：lt_extremalNumber_iff (H : SimpleGrap
h W) (m : Nat) : m < extremalNumber (card V) H ↔ exists G : SimpleGraph V, exist
s _ : DecidableRel G.Ad…
-/
theorem lt_extremalNumber_iff_of_nonneg (H : SimpleGraph W) {m : R} (h : 0 ≤ m) :
    m < extremalNumber (card V) H ↔
      ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj, H.Free G ∧ m < #G.edgeFinset := by
  simp_rw [← Nat.floor_lt h]
  exact lt_extremalNumber_iff H ⌊m⌋₊

/-- If `H` contains a copy of `H'`, then `extremalNumber n H` is at most `extremalNumber n H`. -/
/-
**SimpleGraph.IsContained.extremalNumber_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.IsContained`。
形式化陈述：∀ {n : ℕ} {W : Type u_2} {H : SimpleGraph W} {W' : Type u_4} {H' : SimpleG
raph W'},   H'.IsContained H → SimpleGraph.extremalNumber n H' ≤ SimpleGraph.ext
remalNumber n H
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `SimpleGraph.extremalNumber_le_iff`：extremalNumber_le_iff (H : SimpleGrap
h W) (m : Nat) : extremalNumber (card V) H <= m ↔ forall ⦃G : SimpleGraph V⦄ [De
cidableRel G.Adj], H.Fr…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.IsContained.trans`：∀ {α : Type u_4} {β : Type u_5} {γ : Type
 u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   A.IsContain
ed B → B.IsContaine…
· 使用定理 `SimpleGraph.IsContained.of_extremalNumber_lt_card_edgeFinset`：∀ {V : Typ
e u_1} {W : Type u_2} {G : SimpleGraph V} {H : SimpleGraph W} [inst : Fintype V]
   [inst_1 : DecidableRel G.Adj], SimpleGraph.extr…

--- 原说明 ---
If `H` contains a copy of `H'`, then `extremalNumber n H` is at most `extremalNu
mber n H`.
-/
theorem IsContained.extremalNumber_le {W' : Type*} {H' : SimpleGraph W'} (h : H' ⊑ H) :
    extremalNumber n H' ≤ extremalNumber n H := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro _ _ h'
  contrapose! h'
  exact h.trans (IsContained.of_extremalNumber_lt_card_edgeFinset h')

/-- If `H₁ ≃g H₂`, then `extremalNumber n H₁` equals `extremalNumber n H₂`. -/
@[congr]
/-
**SimpleGraph.extremalNumber_congr** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：extremalNumber_congr {n₁ n₂ : Nat} {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {
H₂ : SimpleGraph W₂} (h : n₁ = n₂) (e : H₁ ≃g H₂) : extremalNumber n₁ H₁ = extre
malNumber n₂ H₂
参数：h : n₁ = n₂；e : H₁ ≃g H₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `SimpleGraph.extremalNumber_le_iff`：extremalNumber_le_iff (H : SimpleGrap
h W) (m : Nat) : extremalNumber (card V) H <= m ↔ forall ⦃G : SimpleGraph V⦄ [De
cidableRel G.Adj], H.Fr…
· 使用定理 `SimpleGraph.card_edgeFinset_le_extremalNumber`：card_edgeFinset_le_extrem
alNumber (h : H.Free G) : #G.edgeFinset <= extremalNumber (card V) H
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `SimpleGraph.IsContained.trans'`：∀ {α : Type u_4} {β : Type u_5} {γ : Typ
e u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   B.IsContai
ned C → A.IsContaine…

--- 原说明 ---
If `H₁ ≃g H₂`, then `extremalNumber n H₁` equals `extremalNumber n H₂`.
-/
theorem extremalNumber_congr {n₁ n₂ : ℕ} {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁}
    {H₂ : SimpleGraph W₂} (h : n₁ = n₂) (e : H₁ ≃g H₂) :
    extremalNumber n₁ H₁ = extremalNumber n₂ H₂ := by
  rw [h, le_antisymm_iff]
  and_intros
  on_goal 2 =>
    replace e := e.symm
  all_goals
    rw [← Fintype.card_fin n₂, extremalNumber_le_iff]
    intro G _ h
    apply card_edgeFinset_le_extremalNumber
    contrapose h
    exact h.trans' ⟨e.toCopy⟩

/-- If `H₁ ≃g H₂`, then `extremalNumber n H₁` equals `extremalNumber n H₂`. -/
/-
**SimpleGraph.extremalNumber_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：extremalNumber_congr_right {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : Sim
pleGraph W₂} (e : H₁ ≃g H₂) : extremalNumber n H₁ = extremalNumber n H₂
参数：e : H₁ ≃g H₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.extremalNumber_congr`：extremalNumber_congr {n₁ n₂ : Nat} {W₁
 W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂} (h : n₁ = n₂) (e : H₁ ≃
g H₂) : extremalNumber…

--- 原说明 ---
If `H₁ ≃g H₂`, then `extremalNumber n H₁` equals `extremalNumber n H₂`.
-/
theorem extremalNumber_congr_right {W₁ W₂ : Type*} {H₁ : SimpleGraph W₁} {H₂ : SimpleGraph W₂}
    (e : H₁ ≃g H₂) : extremalNumber n H₁ = extremalNumber n H₂ := extremalNumber_congr rfl e

/-- `H`-free extremal graphs are `H`-free simple graphs having `extremalNumber (card V) H` many
edges. -/
/-
**SimpleGraph.isExtremal_free_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isExtremal_free_iff : G.IsExtremal H.Free ↔ H.Free G ∧ #G.edgeFinset = ext
remalNumber (card V) H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.IsExtremal.eq_1`：∀ {V : Type u_1} [inst : Fintype V] (G : Si
mpleGraph V) [inst_1 : DecidableRel G.Adj] (p : SimpleGraph V → Prop),   G.IsExt
remal p =     (p …
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.extremalNumber_le_iff`：extremalNumber_le_iff (H : SimpleGrap
h W) (m : Nat) : extremalNumber (card V) H <= m ↔ forall ⦃G : SimpleGraph V⦄ [De
cidableRel G.Adj], H.Fr…
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `SimpleGraph.card_edgeFinset_le_extremalNumber`：card_edgeFinset_le_extrem
alNumber (h : H.Free G) : #G.edgeFinset <= extremalNumber (card V) H
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
`H`-free extremal graphs are `H`-free simple graphs having `extremalNumber (card
 V) H` many
edges.
-/
theorem isExtremal_free_iff :
    G.IsExtremal H.Free ↔ H.Free G ∧ #G.edgeFinset = extremalNumber (card V) H := by
  rw [IsExtremal, and_congr_right_iff, ← extremalNumber_le_iff]
  exact fun h ↦ ⟨eq_of_le_of_ge (card_edgeFinset_le_extremalNumber h), ge_of_eq⟩
/-
**SimpleGraph.card_edgeFinset_of_isExtremal_free** 是 Mathlib 中的一个引理，位于命名空间 `Simp
leGraph`。
形式化陈述：card_edgeFinset_of_isExtremal_free (h : G.IsExtremal H.Free) : #G.edgeFins
et = extremalNumber (card V) H
参数：h : G.IsExtremal H.Free。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.isExtremal_free_iff`：isExtremal_free_iff : G.IsExtremal H.Fr
ee ↔ H.Free G ∧ #G.edgeFinset = extremalNumber (card V) H
-/
lemma card_edgeFinset_of_isExtremal_free (h : G.IsExtremal H.Free) :
    #G.edgeFinset = extremalNumber (card V) H := (isExtremal_free_iff.mp h).2

/-- If `G` is `H.Free`, then `G.deleteIncidenceSet v` is also `H.Free` and has at most
`extremalNumber (card V-1) H` many edges. -/
/-
**SimpleGraph.card_edgeFinset_deleteIncidenceSet_le_extremalNumber** 是 Mathlib 中
的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：card_edgeFinset_deleteIncidenceSet_le_extremalNumber [DecidableEq V] (h : 
H.Free G) (v : V) : #(G.deleteIncidenceSet v).edgeFinset <= extremalNumber (card
 V - 1) H
参数：h : H.Free G；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.card_edgeFinset_induce_compl_singleton`：card_edgeFinset_indu
ce_compl_singleton (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : #(G.induce
 {x}ᶜ).edgeFinset = #(G.deleteIncidenceS…
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Fintype.card_compl_set`：Fintype.card_compl_set [Fintype α] (s : Set α) [
Fintype s] [Fintype (↥sᶜ : Sort _)] : Fintype.card (↥sᶜ : Sort _) = Fintype.card
 α - Fintype…
· 使用定理 `SimpleGraph.card_edgeFinset_le_extremalNumber`：card_edgeFinset_le_extrem
alNumber (h : H.Free G) : #G.edgeFinset <= extremalNumber (card V) H
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `SimpleGraph.IsContained.trans`：∀ {α : Type u_4} {β : Type u_5} {γ : Type
 u_6} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ},   A.IsContain
ed B → B.IsContaine…

--- 原说明 ---
If `G` is `H.Free`, then `G.deleteIncidenceSet v` is also `H.Free` and has at mo
st
`extremalNumber (card V-1) H` many edges.
-/
theorem card_edgeFinset_deleteIncidenceSet_le_extremalNumber
    [DecidableEq V] (h : H.Free G) (v : V) :
    #(G.deleteIncidenceSet v).edgeFinset ≤ extremalNumber (card V - 1) H := by
  rw [← card_edgeFinset_induce_compl_singleton, ← @card_unique ({v} : Set V), ← card_compl_set]
  apply card_edgeFinset_le_extremalNumber
  contrapose h
  exact h.trans ⟨Copy.induce G {v}ᶜ⟩

end ExtremalNumber

end SimpleGraph

