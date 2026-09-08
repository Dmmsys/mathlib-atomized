/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Central

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Field


/-!
## Main results
* `treesOfNumNodesEq_card_eq_catalan`: The number of binary trees with `n` internal nodes
  is `catalan n`

-/

@[expose] public section

open Finset

open Finset.HasAntidiagonal.antidiagonal (fst_le snd_le)

namespace BinaryTree

/-- Given two finsets, find all trees that can be formed with
  left child in `a` and right child in `b` -/
/-
**BinaryTree.pairwiseNode** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
形式化陈述：pairwiseNode (a b : Finset (BinaryTree Unit)) : Finset (BinaryTree Unit)
参数：a b : Finset (BinaryTree Unit)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two finsets, find all trees that can be formed with
  left child in `a` and right child in `b`
-/
abbrev pairwiseNode (a b : Finset (BinaryTree Unit)) : Finset (BinaryTree Unit) :=
  (a ×ˢ b).map ⟨fun x => x.1 △ x.2, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ => fun h => by simpa using h⟩

/-- A Finset of all trees with `n` nodes. See `mem_treesOfNodesEq` -/
/-
**BinaryTree.treesOfNumNodesEq** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：treesOfNumNodesEq : Nat -> Finset (BinaryTree Unit) | 0 => {nil} | n + 1 =
> (antidiagonal n).attach.biUnion fun ijh => pairwiseNode (treesOfNumNodesEq ijh
.1.1) (treesOfNumNodesEq ijh.1.2) decreasing_by · simp_wf; have
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Finset of all trees with `n` nodes. See `mem_treesOfNodesEq`
-/
def treesOfNumNodesEq : ℕ → Finset (BinaryTree Unit)
  | 0 => {nil}
  | n + 1 =>
    (antidiagonal n).attach.biUnion fun ijh =>
      pairwiseNode (treesOfNumNodesEq ijh.1.1) (treesOfNumNodesEq ijh.1.2)
  decreasing_by
    · simp_wf; have := fst_le ijh.2; lia
    · simp_wf; have := snd_le ijh.2; lia

/-- **Alias** of `BinaryTree.treesOfNumNodesEq`. -/
@[deprecated BinaryTree.treesOfNumNodesEq (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.treesOfNumNodesEq** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTr
ee`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.treesOfNumNodesEq`.
-/
abbrev _root_.Tree.treesOfNumNodesEq : ℕ → Finset (Tree Unit) :=
  BinaryTree.treesOfNumNodesEq

@[simp]
/-
**BinaryTree.treesOfNumNodesEq_zero** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTree`。
形式化陈述：treesOfNumNodesEq_zero : treesOfNumNodesEq 0 = {nil}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BinaryTree.treesOfNumNodesEq.eq_1`：BinaryTree.treesOfNumNodesEq 0 = {Bin
aryTree.nil}
-/
theorem treesOfNumNodesEq_zero : treesOfNumNodesEq 0 = {nil} := by rw [treesOfNumNodesEq]
/-
**BinaryTree.treesOfNumNodesEq_succ** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTree`。
形式化陈述：treesOfNumNodesEq_succ (n : Nat) : treesOfNumNodesEq (n + 1) = (antidiagon
al n).biUnion fun ij => pairwiseNode (treesOfNumNodesEq ij.1) (treesOfNumNodesEq
 ij.2)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BinaryTree.treesOfNumNodesEq.eq_2`：∀ (n : ℕ),   BinaryTree.treesOfNumNod
esEq n.succ =     (Finset.HasAntidiagonal.antidiagonal n).attach.biUnion fun ijh
 =>       BinaryTree.pa…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem treesOfNumNodesEq_succ (n : ℕ) :
    treesOfNumNodesEq (n + 1) =
      (antidiagonal n).biUnion fun ij =>
        pairwiseNode (treesOfNumNodesEq ij.1) (treesOfNumNodesEq ij.2) := by
  rw [treesOfNumNodesEq]
  ext
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**BinaryTree.mem_treesOfNumNodesEq** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTree`。
形式化陈述：mem_treesOfNumNodesEq {x : BinaryTree Unit} {n : Nat} : x in treesOfNumNod
esEq n ↔ x.numNodes = n
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
· 使用定理 `BinaryTree.treesOfNumNodesEq_zero`：treesOfNumNodesEq_zero : treesOfNumNo
desEq 0 = {nil}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BinaryTree.treesOfNumNodesEq_succ`：treesOfNumNodesEq_succ (n : Nat) : tr
eesOfNumNodesEq (n + 1) = (antidiagonal n).biUnion fun ij => pairwiseNode (trees
OfNumNodesEq ij.1) (tre…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `BinaryTree.node.injEq`：∀ {α : Type u} (value : α) (left right : BinaryTr
ee α) (value_1 : α) (left_1 right_1 : BinaryTree α),   (BinaryTree.node value le
ft right = …
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem mem_treesOfNumNodesEq {x : BinaryTree Unit} {n : ℕ} :
    x ∈ treesOfNumNodesEq n ↔ x.numNodes = n := by
  induction x using BinaryTree.unitRecOn generalizing n <;> cases n <;>
    simp [treesOfNumNodesEq_succ, *]
/-
**BinaryTree.mem_treesOfNumNodesEq_numNodes** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTre
e`。
形式化陈述：mem_treesOfNumNodesEq_numNodes (x : BinaryTree Unit) : x in treesOfNumNode
sEq x.numNodes
参数：x : BinaryTree Unit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BinaryTree.mem_treesOfNumNodesEq`：mem_treesOfNumNodesEq {x : BinaryTree 
Unit} {n : Nat} : x in treesOfNumNodesEq n ↔ x.numNodes = n
-/
theorem mem_treesOfNumNodesEq_numNodes (x : BinaryTree Unit) : x ∈ treesOfNumNodesEq x.numNodes :=
  mem_treesOfNumNodesEq.mpr rfl

@[simp, norm_cast]
/-
**BinaryTree.coe_treesOfNumNodesEq** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTree`。
形式化陈述：coe_treesOfNumNodesEq (n : Nat) : ↑(treesOfNumNodesEq n) = { x : BinaryTre
e Unit | x.numNodes = n }
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem coe_treesOfNumNodesEq (n : ℕ) :
    ↑(treesOfNumNodesEq n) = { x : BinaryTree Unit | x.numNodes = n } :=
  Set.ext (by simp)
/-
**BinaryTree.treesOfNumNodesEq_card_eq_catalan** 是 Mathlib 中的一个定理，位于命名空间 `Binary
Tree`。
形式化陈述：treesOfNumNodesEq_card_eq_catalan (n : Nat) : #(treesOfNumNodesEq n) = cat
alan n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.case_strong_induction_on`：∀ {p : ℕ → Prop} (a : ℕ), p 0 → (∀ (n : ℕ)
, (∀ m ≤ n, p m) → p (n + 1)) → p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BinaryTree.treesOfNumNodesEq_zero`：treesOfNumNodesEq_zero : treesOfNumNo
desEq 0 = {nil}
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `catalan_zero`：catalan_zero : catalan 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `BinaryTree.treesOfNumNodesEq_succ`：treesOfNumNodesEq_succ (n : Nat) : tr
eesOfNumNodesEq (n + 1) = (antidiagonal n).biUnion fun ij => pairwiseNode (trees
OfNumNodesEq ij.1) (tre…
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `catalan_succ'`：catalan_succ' (n : Nat) : catalan (n + 1) = ∑ ij in antid
iagonal n, catalan ij.1 * catalan ij.2
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Finset.HasAntidiagonal.antidiagonal.fst_le`：∀ {A : Type u_1} [inst : Add
CommMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fi
nset.HasAntidiagonal A] {n : A} …
· 使用定理 `Finset.HasAntidiagonal.antidiagonal.snd_le`：∀ {A : Type u_1} [inst : Add
CommMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fi
nset.HasAntidiagonal A] {n : A} …
-/
theorem treesOfNumNodesEq_card_eq_catalan (n : ℕ) : #(treesOfNumNodesEq n) = catalan n := by
  induction n using Nat.case_strong_induction_on with
  | hz => simp
  | hi n ih =>
    rw [treesOfNumNodesEq_succ, card_biUnion, catalan_succ']
    · apply sum_congr rfl
      rintro ⟨i, j⟩ H
      rw [card_map, card_product, ih _ (fst_le H), ih _ (snd_le H)]
    · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left]
      aesop

end BinaryTree

