/-
Copyright (c) 2021 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Jeremy Tan
-/
module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# Strongly regular graphs

## Main definitions

* `G.IsSRGWith n k ℓ μ` (see `SimpleGraph.IsSRGWith`) is a structure for
  a `SimpleGraph` satisfying the following conditions:
  * The cardinality of the vertex set is `n`
  * `G` is a regular graph with degree `k`
  * The number of common neighbors between any two adjacent vertices in `G` is `ℓ`
  * The number of common neighbors between any two nonadjacent vertices in `G` is `μ`

## Main theorems

* `IsSRGWith.compl`: the complement of a strongly regular graph is strongly regular.
* `IsSRGWith.param_eq`: `k * (k - ℓ - 1) = (n - k - 1) * μ` when `0 < n`.
* `IsSRGWith.matrix_eq`: let `A` and `C` be `G`'s and `Gᶜ`'s adjacency matrices respectively and
  `I` be the identity matrix, then `A ^ 2 = k • I + ℓ • A + μ • C`.
-/

public section


open Finset

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A graph is strongly regular with parameters `n k ℓ μ` if
* its vertex set has cardinality `n`
* it is regular with degree `k`
* every pair of adjacent vertices has `ℓ` common neighbors
* every pair of nonadjacent vertices has `μ` common neighbors
-/
/-
**SimpleGraph.IsSRGWith** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u} → [Fintype V] → (G : SimpleGraph V) → [DecidableRel G.Adj] → 
ℕ → ℕ → ℕ → ℕ → Prop
参数：G : SimpleGraph V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graph is strongly regular with parameters `n k ℓ μ` if
* its vertex set has cardinality `n`
* it is regular with degree `k`
* every pair of adjacent vertices has `ℓ` common neighbors
* every pair of nonadjacent vertices has `μ` common neighbors
-/
structure IsSRGWith (n k ℓ μ : ℕ) : Prop where
  card : Fintype.card V = n
  regular : G.IsRegularOfDegree k
  of_adj : ∀ v w, G.Adj v w → Fintype.card (G.commonNeighbors v w) = ℓ
  of_not_adj : Pairwise fun v w ↦ ¬G.Adj v w → Fintype.card (G.commonNeighbors v w) = μ

variable {G} {n k ℓ μ : ℕ}

/-- Empty graphs are strongly regular. Note that `ℓ` can take any value
for empty graphs, since there are no pairs of adjacent vertices. -/
/-
**SimpleGraph.bot_strongly_regular** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：bot_strongly_regular : (⊥ : SimpleGraph V).IsSRGWith (Fintype.card V) 0 ℓ 
0 where card
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsRegularOfDegree.bot`：∀ {V : Type u_1} [inst : Fintype V], 
⊥.IsRegularOfDegree 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SimpleGraph.commonNeighbors_bot_eq`：commonNeighbors_bot_eq : commonNeigh
bors ⊥ u v = ∅
· 使用定理 `Finset.filter_false`：∀ {α : Type u_1} {h : DecidablePred fun x => False}
 (s : Finset α), {x ∈ s | False} = ∅
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Empty graphs are strongly regular. Note that `ℓ` can take any value
for empty graphs, since there are no pairs of adjacent vertices.
-/
theorem bot_strongly_regular : (⊥ : SimpleGraph V).IsSRGWith (Fintype.card V) 0 ℓ 0 where
  card := rfl
  regular := .bot
  of_adj _ _ h := h.elim
  of_not_adj v w _ := by
    simp only [card_eq_zero, Fintype.card_ofFinset, forall_true_left, not_false_iff, bot_adj]
    ext
    simp
/-
**SimpleGraph.IsSRGWith.ediam_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsSR
GWith`。
形式化陈述：∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableR
el G.Adj] {n k ℓ μ : ℕ} [Nontrivial V],   G.IsSRGWith n k ℓ μ → G ≠ ⊤ → μ ≠ 0 → 
G.ediam = 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.ediam_le_iff`：ediam_le_iff {k : Nat∞} : G.ediam <= k ↔ foral
l u v, G.edist u v <= k
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.two_lt_edist_iff`：two_lt_edist_iff {u v : V} : 2 < G.edist u
 v ↔ u != v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v) = ∅
· 使用定理 `SimpleGraph.IsSRGWith.of_not_adj`：∀ {V : Type u} [inst : Fintype V] {G :
 SimpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ
 μ → Pairwise fun v w …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem IsSRGWith.ediam_eq_two [Nontrivial V] (h : G.IsSRGWith n k ℓ μ) (ht : G ≠ ⊤) (hm : μ ≠ 0) :
    G.ediam = 2 := by
  apply le_antisymm
  · rw [ediam_le_iff]
    intro u v
    by_contra! hc
    obtain ⟨hn, ha, he⟩ := two_lt_edist_iff.mp hc
    have h := h.of_not_adj hn ha
    simp_all
  · by_contra
    have := not_subsingleton V
    simp_all [Order.le_one_iff]

/-- **Conway's 99-graph problem** (from https://oeis.org/A248380/a248380.pdf)
can be reformulated as the existence of a strongly regular graph with params (99, 14, 1, 2).
This is an open problem, and has no known proof of existence. -/
proof_wanted conway_99 : ∃ (α : Type) (_ : Fintype α) (g : SimpleGraph α) (_ : DecidableRel g.Adj),
    IsSRGWith g 99 14 1 2

variable [DecidableEq V]

/-- Complete graphs are strongly regular. Note that `μ` can take any value
for complete graphs, since there are no distinct pairs of non-adjacent vertices. -/
/-
**SimpleGraph.IsSRGWith.top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsSRGWith`。
形式化陈述：∀ {V : Type u} [inst : Fintype V] {μ : ℕ} [inst_1 : DecidableEq V],   ⊤.Is
SRGWith (Fintype.card V) (Fintype.card V - 1) (Fintype.card V - 2) μ
参数：Fintype.card V；Fintype.card V - 1；Fintype.card V - 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsRegularOfDegree.top`：∀ {V : Type u_1} [inst : Fintype V] [
inst_1 : DecidableEq V], ⊤.IsRegularOfDegree (Fintype.card V - 1)
· 使用定理 `SimpleGraph.card_commonNeighbors_top`：card_commonNeighbors_top [Decidabl
eEq V] {v w : V} (h : v != w) : Fintype.card (commonNeighbors ⊤ v w) = Fintype.c
ard V - 2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.top_adj`：top_adj (v w : V) : (⊤ : SimpleGraph V).Adj v w ↔ v
 != w

--- 原说明 ---
Complete graphs are strongly regular. Note that `μ` can take any value
for complete graphs, since there are no distinct pairs of non-adjacent vertices.
-/
theorem IsSRGWith.top :
    (⊤ : SimpleGraph V).IsSRGWith (Fintype.card V) (Fintype.card V - 1) (Fintype.card V - 2) μ where
  card := rfl
  regular := IsRegularOfDegree.top
  of_adj _ _ := card_commonNeighbors_top
  of_not_adj v w h h' := (h' ((top_adj v w).2 h)).elim

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.IsSRGWith.card_neighborFinset_union_eq** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.IsSRGWith`。
形式化陈述：∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableR
el G.Adj] {n k ℓ μ : ℕ}   [inst_2 : DecidableEq V] {v w : V},   G.IsSRGWith n k 
ℓ μ → (G.neighborFinset v ∪ G.neighborFinset w).card = 2 * k - Fintype.card ↑(G.
commonNeighbors v w)
参数：G.neighborFinset v ∪ G.neighborFinset w；G.commonNeighbors v w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_right_cancel`：∀ {n m k : ℕ}, n + m = k + m → n = k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `SimpleGraph.card_commonNeighbors_le_degree_left`：card_commonNeighbors_le
_degree_left [DecidableRel G.Adj] (v w : V) : Fintype.card (G.commonNeighbors v 
w) <= G.degree v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.IsRegularOfDegree.degree_eq`：∀ {V : Type u_1} {G : SimpleGra
ph V} [inst : G.LocallyFinite] {d : ℕ}, G.IsRegularOfDegree d → ∀ (v : V), G.deg
ree v = d
· 使用定理 `SimpleGraph.IsSRGWith.regular`：∀ {V : Type u} [inst : Fintype V] {G : Si
mpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ μ 
→ G.IsRegularOfDegr…
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Set.toFinset_inter`：toFinset_inter [Fintype (s inter t : Set _)] : (s in
ter t).toFinset = s.toFinset inter t.toFinset
· 使用定理 `Finset.card_union_add_card_inter`：card_union_add_card_inter (s t : Finse
t α) : #(s union t) + #(s inter t) = #s + #t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsSRGWith.card_neighborFinset_union_eq {v w : V} (h : G.IsSRGWith n k ℓ μ) :
    #(G.neighborFinset v ∪ G.neighborFinset w) =
      2 * k - Fintype.card (G.commonNeighbors v w) := by
  apply Nat.add_right_cancel (m := Fintype.card (G.commonNeighbors v w))
  rw [Nat.sub_add_cancel, ← Set.toFinset_card]
  · simp [commonNeighbors, ← neighborFinset_def, Finset.card_union_add_card_inter,
      h.regular.degree_eq, two_mul]
  · apply le_trans (card_commonNeighbors_le_degree_left _ _ _)
    simp [h.regular.degree_eq, two_mul]

/-- Assuming `G` is strongly regular, `2*(k + 1) - m` in `G` is the number of vertices that are
adjacent to either `v` or `w` when `¬G.Adj v w`. So it's the cardinality of
`G.neighborSet v ∪ G.neighborSet w`. -/
/-
**SimpleGraph.IsSRGWith.card_neighborFinset_union_of_not_adj** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph.IsSRGWith`。
形式化陈述：∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableR
el G.Adj] {n k ℓ μ : ℕ}   [inst_2 : DecidableEq V] {v w : V},   G.IsSRGWith n k 
ℓ μ → v ≠ w → ¬G.Adj v w → (G.neighborFinset v ∪ G.neighborFinset w).card = 2 * 
k - μ
参数：G.neighborFinset v ∪ G.neighborFinset w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.IsSRGWith.of_not_adj`：∀ {V : Type u} [inst : Fintype V] {G :
 SimpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ
 μ → Pairwise fun v w …
· 使用定理 `SimpleGraph.IsSRGWith.card_neighborFinset_union_eq`：∀ {V : Type u} [inst
 : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ}   
[inst_2 : DecidableEq V] {v w : V},   G.…

--- 原说明 ---
Assuming `G` is strongly regular, `2*(k + 1) - m` in `G` is the number of vertic
es that are
adjacent to either `v` or `w` when `¬G.Adj v w`. So it's the cardinality of
`G.neighborSet v ∪ G.neighborSet w`.
-/
theorem IsSRGWith.card_neighborFinset_union_of_not_adj {v w : V} (h : G.IsSRGWith n k ℓ μ)
    (hne : v ≠ w) (ha : ¬G.Adj v w) :
    #(G.neighborFinset v ∪ G.neighborFinset w) = 2 * k - μ := by
  rw [← h.of_not_adj hne ha]
  exact h.card_neighborFinset_union_eq
/-
**SimpleGraph.IsSRGWith.card_neighborFinset_union_of_adj** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph.IsSRGWith`。
形式化陈述：∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableR
el G.Adj] {n k ℓ μ : ℕ}   [inst_2 : DecidableEq V] {v w : V},   G.IsSRGWith n k 
ℓ μ → G.Adj v w → (G.neighborFinset v ∪ G.neighborFinset w).card = 2 * k - ℓ
参数：G.neighborFinset v ∪ G.neighborFinset w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.IsSRGWith.of_adj`：∀ {V : Type u} [inst : Fintype V] {G : Sim
pleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ μ →
 ∀ (v w : V), G.Ad…
· 使用定理 `SimpleGraph.IsSRGWith.card_neighborFinset_union_eq`：∀ {V : Type u} [inst
 : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ}   
[inst_2 : DecidableEq V] {v w : V},   G.…
-/
theorem IsSRGWith.card_neighborFinset_union_of_adj {v w : V} (h : G.IsSRGWith n k ℓ μ)
    (ha : G.Adj v w) : #(G.neighborFinset v ∪ G.neighborFinset w) = 2 * k - ℓ := by
  rw [← h.of_adj v w ha]
  exact h.card_neighborFinset_union_eq
/-
**SimpleGraph.compl_neighborFinset_sdiff_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：compl_neighborFinset_sdiff_inter_eq {v w : V} : (G.neighborFinset v)ᶜ \ {v
} inter ((G.neighborFinset w)ᶜ \ {w}) = ((G.neighborFinset v)ᶜ inter (G.neighbor
Finset w)ᶜ) \ ({w} union {v})
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compl_neighborFinset_sdiff_inter_eq {v w : V} :
    (G.neighborFinset v)ᶜ \ {v} ∩ ((G.neighborFinset w)ᶜ \ {w}) =
      ((G.neighborFinset v)ᶜ ∩ (G.neighborFinset w)ᶜ) \ ({w} ∪ {v}) := by
  grind
/-
**SimpleGraph.sdiff_compl_neighborFinset_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph`。
形式化陈述：sdiff_compl_neighborFinset_inter_eq {v w : V} (h : G.Adj v w) : ((G.neighb
orFinset v)ᶜ inter (G.neighborFinset w)ᶜ) \ ({w} union {v}) = (G.neighborFinset 
v)ᶜ inter (G.neighborFinset w)ᶜ
参数：h : G.Adj v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `SimpleGraph.adj_symm`：adj_symm (h : G.Adj u v) : G.Adj v u
-/
theorem sdiff_compl_neighborFinset_inter_eq {v w : V} (h : G.Adj v w) :
    ((G.neighborFinset v)ᶜ ∩ (G.neighborFinset w)ᶜ) \ ({w} ∪ {v}) =
      (G.neighborFinset v)ᶜ ∩ (G.neighborFinset w)ᶜ := by
  simpa using ⟨h, adj_symm _ h⟩
/-
**SimpleGraph.IsSRGWith.compl_is_regular** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
IsSRGWith`。
形式化陈述：∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableR
el G.Adj] {n k ℓ μ : ℕ}   [inst_2 : DecidableEq V], G.IsSRGWith n k ℓ μ → Gᶜ.IsR
egularOfDegree (n - k - 1)
参数：n - k - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.IsSRGWith.card`：∀ {V : Type u} [inst : Fintype V] {G : Simpl
eGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ μ → F
intype.card V = …
· 使用定理 `Nat.sub_sub`：∀ (n m k : ℕ), n - m - k = n - (m + k)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `SimpleGraph.IsRegularOfDegree.compl`：∀ {V : Type u_1} [inst : Fintype V]
 [inst_1 : DecidableEq V] {G : SimpleGraph V} [inst_2 : DecidableRel G.Adj] {k :
 ℕ},   G.IsRegularOfDegre…
· 使用定理 `SimpleGraph.IsSRGWith.regular`：∀ {V : Type u} [inst : Fintype V] {G : Si
mpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ μ 
→ G.IsRegularOfDegr…
-/
theorem IsSRGWith.compl_is_regular (h : G.IsSRGWith n k ℓ μ) :
    Gᶜ.IsRegularOfDegree (n - k - 1) := by
  rw [← h.card, Nat.sub_sub, add_comm, ← Nat.sub_sub]
  exact h.regular.compl
/-
**SimpleGraph.IsSRGWith.card_commonNeighbors_eq_of_adj_compl** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph.IsSRGWith`。
形式化陈述：∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableR
el G.Adj] {n k ℓ μ : ℕ}   [inst_2 : DecidableEq V],   G.IsSRGWith n k ℓ μ → ∀ {v
 w : V}, Gᶜ.Adj v w → Fintype.card ↑(Gᶜ.commonNeighbors v w) = n - (2 * k - μ) -
 2
参数：Gᶜ.commonNeighbors v w；2 * k - μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.neighborSet_compl`：neighborSet_compl (G : SimpleGraph V) (v 
: V) : Gᶜ.neighborSet v = (G.neighborSet v)ᶜ \ {v}
· 使用定理 `Set.toFinset_inter`：toFinset_inter [Fintype (s inter t : Set _)] : (s in
ter t).toFinset = s.toFinset inter t.toFinset
· 使用定理 `Set.toFinset_sdiff`：toFinset_sdiff [Fintype (s \ t : Set _)] : (s \ t).t
oFinset = s.toFinset \ t.toFinset
· 使用定理 `Set.toFinset_compl`：toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : 
sᶜ.toFinset = s.toFinsetᶜ
· 使用定理 `Set.toFinset_singleton`：toFinset_singleton (a : α) [Fintype ({a} : Set α
)] : ({a} : Set α).toFinset = {a}
· 使用定理 `SimpleGraph.compl_neighborFinset_sdiff_inter_eq`：compl_neighborFinset_sd
iff_inter_eq {v w : V} : (G.neighborFinset v)ᶜ \ {v} inter ((G.neighborFinset w)
ᶜ \ {w}) = ((G.neighborFinset v)ᶜ int…
· 使用定理 `SimpleGraph.ne_of_adj`：ne_of_adj (h : G.Adj a b) : a != b
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.compl_adj`：compl_adj (G : SimpleGraph V) (v w : V) : Gᶜ.Adj 
v w ↔ v != w ∧ ¬G.Adj v w
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_eq`：insert_eq (a : α) (s : Finset α) : insert a s = {a} un
ion s
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Finset.compl_union`：compl_union (s t : Finset α) : (s union t)ᶜ = sᶜ int
er tᶜ
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `SimpleGraph.IsSRGWith.card_neighborFinset_union_of_not_adj`：∀ {V : Type 
u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ
 : ℕ}   [inst_2 : DecidableEq V] {v w : V},   G.…
· 使用定理 `SimpleGraph.IsSRGWith.card`：∀ {V : Type u} [inst : Fintype V] {G : Simpl
eGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ μ → F
intype.card V = …
-/
theorem IsSRGWith.card_commonNeighbors_eq_of_adj_compl (h : G.IsSRGWith n k ℓ μ) {v w : V}
    (ha : Gᶜ.Adj v w) : Fintype.card (Gᶜ.commonNeighbors v w) = n - (2 * k - μ) - 2 := by
  simp only [← Set.toFinset_card, commonNeighbors, Set.toFinset_inter, neighborSet_compl,
    Set.toFinset_sdiff, Set.toFinset_singleton, Set.toFinset_compl, ← neighborFinset_def]
  simp_rw [compl_neighborFinset_sdiff_inter_eq]
  have hne : v ≠ w := ne_of_adj _ ha
  rw [compl_adj] at ha
  rw [card_sdiff_of_subset, ← insert_eq, card_insert_of_notMem, card_singleton,
    ← Finset.compl_union]
  · rw [card_compl, h.card_neighborFinset_union_of_not_adj hne ha.2, ← h.card]
  · simp only [hne.symm, not_false_iff, mem_singleton]
  · intro u
    simp only [mem_union, mem_compl, mem_neighborFinset, mem_inter, mem_singleton]
    rintro (rfl | rfl) <;> simpa [adj_comm] using ha.2
/-
**SimpleGraph.IsSRGWith.card_commonNeighbors_eq_of_not_adj_compl** 是 Mathlib 中的一
个定理，位于命名空间 `SimpleGraph.IsSRGWith`。
形式化陈述：∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableR
el G.Adj] {n k ℓ μ : ℕ}   [inst_2 : DecidableEq V],   G.IsSRGWith n k ℓ μ → ∀ {v
 w : V}, v ≠ w → ¬Gᶜ.Adj v w → Fintype.card ↑(Gᶜ.commonNeighbors v w) = n - (2 *
 k - ℓ)
参数：Gᶜ.commonNeighbors v w；2 * k - ℓ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.neighborSet_compl`：neighborSet_compl (G : SimpleGraph V) (v 
: V) : Gᶜ.neighborSet v = (G.neighborSet v)ᶜ \ {v}
· 使用定理 `Set.toFinset_inter`：toFinset_inter [Fintype (s inter t : Set _)] : (s in
ter t).toFinset = s.toFinset inter t.toFinset
· 使用定理 `Set.toFinset_sdiff`：toFinset_sdiff [Fintype (s \ t : Set _)] : (s \ t).t
oFinset = s.toFinset \ t.toFinset
· 使用定理 `Set.toFinset_compl`：toFinset_compl [Fintype α] [Fintype (sᶜ : Set _)] : 
sᶜ.toFinset = s.toFinsetᶜ
· 使用定理 `Set.toFinset_singleton`：toFinset_singleton (a : α) [Fintype ({a} : Set α
)] : ({a} : Set α).toFinset = {a}
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.compl_neighborFinset_sdiff_inter_eq`：compl_neighborFinset_sd
iff_inter_eq {v w : V} : (G.neighborFinset v)ᶜ \ {v} inter ((G.neighborFinset w)
ᶜ \ {w}) = ((G.neighborFinset v)ᶜ int…
· 使用定理 `SimpleGraph.sdiff_compl_neighborFinset_inter_eq`：sdiff_compl_neighborFin
set_inter_eq {v w : V} (h : G.Adj v w) : ((G.neighborFinset v)ᶜ inter (G.neighbo
rFinset w)ᶜ) \ ({w} union {v}) = (G.n…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.compl_union`：compl_union (s t : Finset α) : (s union t)ᶜ = sᶜ int
er tᶜ
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `SimpleGraph.IsSRGWith.card_neighborFinset_union_of_adj`：∀ {V : Type u} [
inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ
}   [inst_2 : DecidableEq V] {v w : V},   G.…
· 使用定理 `SimpleGraph.IsSRGWith.card`：∀ {V : Type u} [inst : Fintype V] {G : Simpl
eGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ μ → F
intype.card V = …
-/
theorem IsSRGWith.card_commonNeighbors_eq_of_not_adj_compl (h : G.IsSRGWith n k ℓ μ) {v w : V}
    (hn : v ≠ w) (hna : ¬Gᶜ.Adj v w) :
    Fintype.card (Gᶜ.commonNeighbors v w) = n - (2 * k - ℓ) := by
  simp only [← Set.toFinset_card, commonNeighbors, Set.toFinset_inter, neighborSet_compl,
    Set.toFinset_sdiff, Set.toFinset_singleton, Set.toFinset_compl, ← neighborFinset_def]
  simp only [not_and, Classical.not_not, compl_adj] at hna
  have h2' := hna hn
  simp_rw [compl_neighborFinset_sdiff_inter_eq, sdiff_compl_neighborFinset_inter_eq h2']
  rwa [← Finset.compl_union, card_compl, h.card_neighborFinset_union_of_adj, ← h.card]

/-- The complement of a strongly regular graph is strongly regular. -/
/-
**SimpleGraph.IsSRGWith.compl** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsSRGWith`。
形式化陈述：∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableR
el G.Adj] {n k ℓ μ : ℕ}   [inst_2 : DecidableEq V], G.IsSRGWith n k ℓ μ → Gᶜ.IsS
RGWith n (n - k - 1) (n - (2 * k - μ) - 2) (n - (2 * k - ℓ))
参数：n - k - 1；n - (2 * k - μ) - 2；n - (2 * k - ℓ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.IsSRGWith.card`：∀ {V : Type u} [inst : Fintype V] {G : Simpl
eGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ μ → F
intype.card V = …
· 使用定理 `SimpleGraph.IsSRGWith.compl_is_regular`：∀ {V : Type u} [inst : Fintype V
] {G : SimpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ}   [inst_2 : De
cidableEq V], G.IsSRGWith n …
· 使用定理 `SimpleGraph.IsSRGWith.card_commonNeighbors_eq_of_adj_compl`：∀ {V : Type 
u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ
 : ℕ}   [inst_2 : DecidableEq V],   G.IsSRGWith …
· 使用定理 `SimpleGraph.IsSRGWith.card_commonNeighbors_eq_of_not_adj_compl`：∀ {V : T
ype u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableRel G.Adj] {n k
 ℓ μ : ℕ}   [inst_2 : DecidableEq V],   G.IsSRGWith …

--- 原说明 ---
The complement of a strongly regular graph is strongly regular.
-/
theorem IsSRGWith.compl (h : G.IsSRGWith n k ℓ μ) :
    Gᶜ.IsSRGWith n (n - k - 1) (n - (2 * k - μ) - 2) (n - (2 * k - ℓ)) where
  card := h.card
  regular := h.compl_is_regular
  of_adj _ _ := h.card_commonNeighbors_eq_of_adj_compl
  of_not_adj _ _ := h.card_commonNeighbors_eq_of_not_adj_compl

/-- The parameters of a strongly regular graph with at least one vertex satisfy
`k * (k - ℓ - 1) = (n - k - 1) * μ`. -/
/-
**SimpleGraph.IsSRGWith.param_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsSRGWit
h`。
形式化陈述：∀ {n k ℓ μ : ℕ} {V : Type u} [inst : Fintype V] (G : SimpleGraph V) [inst_
1 : DecidableRel G.Adj],   G.IsSRGWith n k ℓ μ → 0 < n → k * (k - ℓ - 1) = (n - 
k - 1) * μ
参数：G : SimpleGraph V；k - ℓ - 1；n - k - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.IsSRGWith.card`：∀ {V : Type u} [inst : Fintype V] {G : Simpl
eGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ μ → F
intype.card V = …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.IsSRGWith.regular`：∀ {V : Type u} [inst : Fintype V] {G : Si
mpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ μ 
→ G.IsRegularOfDegr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.IsSRGWith.compl`：∀ {V : Type u} [inst : Fintype V] {G : Simp
leGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ}   [inst_2 : DecidableEq V
], G.IsSRGWith n …
· 使用定理 `Finset.card_mul_eq_card_mul`：card_mul_eq_card_mul [forall a b, Decidable
 (r a b)] (hm : forall a in s, #(t.bipartiteAbove r a) = m) (hn : forall b in t,
 #(s.bipartiteBel…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_mem_eq_inter`：filter_mem_eq_inter {s t : Finset α} [forall
 i, Decidable (i in t)] : (s.filter fun i => i in t) = s inter t
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `SimpleGraph.mem_neighborFinset`：mem_neighborFinset (w : V) : w in G.neig
hborFinset v ↔ G.Adj v w
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.notMem_neighborFinset_self`：notMem_neighborFinset_self : v ∉
 G.neighborFinset v
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `SimpleGraph.neighborFinset_compl`：neighborFinset_compl [DecidableEq V] [
DecidableRel G.Adj] (v : V) : Gᶜ.neighborFinset v = (G.neighborFinset v)ᶜ \ {v}
· 使用引理 `Finset.inter_sdiff_assoc`：inter_sdiff_assoc (s t u : Finset α) : (s inte
r t) \ u = s inter (t \ u)
· 使用定理 `Finset.sdiff_eq_inter_compl`：sdiff_eq_inter_compl (s t : Finset α) : s \
 t = s inter tᶜ
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Finset.sdiff_inter_self_left`：sdiff_inter_self_left (s t : Finset α) : s
 \ (s inter t) = s \ t
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
· 使用定理 `SimpleGraph.IsSRGWith.of_adj`：∀ {V : Type u} [inst : Fintype V] {G : Sim
pleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ μ →
 ∀ (v w : V), G.Ad…
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The parameters of a strongly regular graph with at least one vertex satisfy
`k * (k - ℓ - 1) = (n - k - 1) * μ`.
-/
theorem IsSRGWith.param_eq
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith n k ℓ μ) (hn : 0 < n) :
    k * (k - ℓ - 1) = (n - k - 1) * μ := by
  let := Classical.decEq V
  rw [← h.card, Fintype.card_pos_iff] at hn
  obtain ⟨v⟩ := hn
  convert! card_mul_eq_card_mul G.Adj (s := G.neighborFinset v) (t := Gᶜ.neighborFinset v) _ _
  · simp [h.regular v]
  · simp [h.compl.regular v]
  · intro w hw
    rw [mem_neighborFinset] at hw
    simp_rw [bipartiteAbove, ← mem_neighborFinset, filter_mem_eq_inter]
    have s : {v} ⊆ G.neighborFinset w \ G.neighborFinset v := by
      rw [singleton_subset_iff, mem_sdiff, mem_neighborFinset]
      exact ⟨hw.symm, G.notMem_neighborFinset_self v⟩
    rw [inter_comm, neighborFinset_compl, ← inter_sdiff_assoc, ← sdiff_eq_inter_compl,
      card_sdiff_of_subset s, card_singleton, ← sdiff_inter_self_left,
      card_sdiff_of_subset inter_subset_left]
    congr
    · simp [h.regular w]
    · simp_rw [inter_comm, neighborFinset_def, ← Set.toFinset_inter, ← h.of_adj v w hw,
        ← Set.toFinset_card]
      congr!
  · intro w hw
    simp_rw [neighborFinset_compl, mem_sdiff, mem_compl, mem_singleton, mem_neighborFinset,
      ← Ne.eq_def] at hw
    simp_rw [bipartiteBelow, adj_comm, ← mem_neighborFinset, filter_mem_eq_inter,
      neighborFinset_def, ← Set.toFinset_inter, ← h.of_not_adj hw.2.symm hw.1,
      ← Set.toFinset_card]
    congr!

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `A` and `C` be the adjacency matrices of a strongly regular graph with parameters `n k ℓ μ`
and its complement respectively and `I` be the identity matrix,
then `A ^ 2 = k • I + ℓ • A + μ • C`. `C` is equivalent to the expression `J - I - A`
more often found in the literature, where `J` is the all-ones matrix. -/
/-
**SimpleGraph.IsSRGWith.matrix_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.IsSRGWi
th`。
形式化陈述：∀ {V : Type u} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableR
el G.Adj] {n k ℓ μ : ℕ}   [inst_2 : DecidableEq V] {α : Type u_1} [inst_3 : Semi
ring α],   G.IsSRGWith n k ℓ μ →     SimpleGraph.adjMatrix α G ^ 2 = k • 1 + ℓ •
 SimpleGraph.adjMatrix α G + μ • SimpleGraph.adjMatrix α Gᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`：adjMatrix_pow_apply_eq_car
d_walk [DecidableEq V] [Semiring α] (n : Nat) (u v : V) : (G.adjMatrix α ^ n) u 
v = Fintype.card { p : G.Walk u v …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `SimpleGraph.IsSRGWith.regular`：∀ {V : Type u} [inst : Fintype V] {G : Si
mpleGraph V} [inst_1 : DecidableRel G.Adj] {n k ℓ μ : ℕ},   G.IsSRGWith n k ℓ μ 
→ G.IsRegularOfDegr…
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.one_apply_ne'`：one_apply_ne' {i j} : j != i -> (1 : Matrix n n α)
 i j = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Let `A` and `C` be the adjacency matrices of a strongly regular graph with param
eters `n k ℓ μ`
and its complement respectively and `I` be the identity matrix,
then `A ^ 2 = k • I + ℓ • A + μ • C`. `C` is equivalent to the expression `J - I
 - A`
more often found in the literature, where `J` is the all-ones matrix.
-/
theorem IsSRGWith.matrix_eq {α : Type*} [Semiring α] (h : G.IsSRGWith n k ℓ μ) :
    G.adjMatrix α ^ 2 = k • (1 : Matrix V V α) + ℓ • G.adjMatrix α + μ • Gᶜ.adjMatrix α := by
  ext v w
  simp only [adjMatrix_pow_apply_eq_card_walk, Matrix.add_apply, Matrix.smul_apply,
    adjMatrix_apply, compl_adj]
  rw [@Fintype.card_congr _ _ (G.fintypeSetWalkLength v w 2) _
    (G.walkLengthTwoEquivCommonNeighbors v w)]
  obtain rfl | hn := eq_or_ne v w
  · rw [← Set.toFinset_card]
    simp [commonNeighbors, ← neighborFinset_def, h.regular v]
  · simp only [Matrix.one_apply_ne' hn.symm, ne_eq, hn]
    by_cases ha : G.Adj v w <;>
      simp only [ha, ite_true, ite_false, add_zero, zero_add, nsmul_eq_mul, smul_zero, mul_one,
        not_true_eq_false, not_false_eq_true, and_false, and_self]
    · rw [h.of_adj v w ha]
    · rw [h.of_not_adj hn ha]

end SimpleGraph

