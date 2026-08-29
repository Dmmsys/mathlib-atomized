/-
Copyright (c) 2024 Iván Renison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Definition of circulant graphs

This file defines and proves several fact about circulant graphs.
A circulant graph over type `G` with jumps `s : Set G` is a graph in which two vertices `u` and `v`
are adjacent if and only if `u - v ∈ s` or `v - u ∈ s`. The elements of `s` are called jumps.

## Main declarations

* `SimpleGraph.circulantGraph s`: the circulant graph over `G` with jumps `s`.
-/

@[expose] public section

namespace SimpleGraph

/-- Circulant graph over additive group `G` with jumps `s` -/
@[simps!]
/--
Definition of `circulantGraph` / `circulantGraph` 的定义

English:
definition circulantGraph
  signature: {G : Type*} [AddGroup G] (s : Set G)
  body: fromRel (· - · in s)

中文:
定义 circulantGraph
  签名: {G : 类型} [加法群 G] (s : 集合 G)
  定义体: fromRel (· - · in s)

Depends on / 依赖: fromRel
-/
def circulantGraph {G : Type*} [AddGroup G] (s : Set G) : SimpleGraph G :=
  fromRel (· - · in s)

variable {G : Type*} [AddGroup G] (s : Set G)

/--
theorem `circulantGraph_eq_erase_zero` / 定理 `circulantGraph_eq_erase_zero`

English:
theorem circulantGraph_eq_erase_zero
  statement: circulantGraph s = circulantGraph (s \ {0})
  proof: by
  ext (u v : G)
  simp only [circulantGraph, fromRel_adj, and_congr_right_iff]
  intro (h : u != v)
  apply Iff.intro
  · intro h1
    cases h1 with
      | inl h1 => exact Or.inl ⟨h1, sub_ne_zero_of_ne h⟩
      | inr h1 => exact Or.inr ⟨h1, sub_ne_zero_of_ne h.symm⟩
  · intro h1
    cases h1 wit

中文:
定理 circulantGraph_eq_erase_zero
  结论: circulantGraph s = circulantGraph (s \ {0})
  证明: by
  ext (u v : G)
  simp only [circulantGraph, fromRel_adj, and_congr_right_iff]
  intro (h : u != v)
  apply Iff.intro
  · intro h1
    cases h1 with
      | inl h1 => exact Or.inl ⟨h1, sub_ne_zero_of_ne h⟩
      | inr h1 => exact Or.inr ⟨h1, sub_ne_zero_of_ne h.symm⟩
  · intro h1
    cases h1 wit

Depends on / 依赖: Iff.intro, Or.inl, Or.inr, and_congr_right_iff, circulantGraph, fromRel_adj, h.symm, h1.left, sub_ne_zero_of_ne
-/
theorem circulantGraph_eq_erase_zero : circulantGraph s = circulantGraph (s \ {0}) := by
  ext (u v : G)
  simp only [circulantGraph, fromRel_adj, and_congr_right_iff]
  intro (h : u != v)
  apply Iff.intro
  · intro h1
    cases h1 with
      | inl h1 => exact Or.inl ⟨h1, sub_ne_zero_of_ne h⟩
      | inr h1 => exact Or.inr ⟨h1, sub_ne_zero_of_ne h.symm⟩
  · intro h1
    cases h1 with
      | inl h1 => exact Or.inl h1.left
      | inr h1 => exact Or.inr h1.left

/--
theorem `circulantGraph_eq_symm` / 定理 `circulantGraph_eq_symm`

English:
theorem circulantGraph_eq_symm
  statement: circulantGraph s = circulantGraph (s union (-s))
  proof: by
  ext
  simp only [circulantGraph_adj, Set.mem_union, Set.mem_neg, neg_sub]
  grind

中文:
定理 circulantGraph_eq_symm
  结论: circulantGraph s = circulantGraph (s union (-s))
  证明: by
  ext
  simp only [circulantGraph_adj, Set.mem_union, Set.mem_neg, neg_sub]
  grind

Depends on / 依赖: Set.mem_neg, Set.mem_union, circulantGraph_adj, mem_neg, mem_union, neg_sub
-/
theorem circulantGraph_eq_symm : circulantGraph s = circulantGraph (s union (-s)) := by
  ext
  simp only [circulantGraph_adj, Set.mem_union, Set.mem_neg, neg_sub]
  grind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: G] [DecidablePred (· in s)] : DecidableRel (circulantGraph s).Adj
  body: fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

中文:
实例 [DecidableEq
  签名: G] [DecidablePred (· in s)] : DecidableRel (circulantGraph s).伴随
  定义体: fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

Depends on / 依赖: Decidable
-/
instance [DecidableEq G] [DecidablePred (· in s)] : DecidableRel (circulantGraph s).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/--
theorem `circulantGraph_adj_translate` / 定理 `circulantGraph_adj_translate`

English:
theorem circulantGraph_adj_translate
  given: {s : Set G} {u v d : G}
  proof: by simp

中文:
定理 circulantGraph_adj_translate
  条件: {s : 集合 G} {u v d : G}
  证明: by simp
-/
theorem circulantGraph_adj_translate {s : Set G} {u v d : G} :
    (circulantGraph s).Adj (u + d) (v + d) ↔ (circulantGraph s).Adj u v := by simp

/--
theorem `cycleGraph_eq_circulantGraph` / 定理 `cycleGraph_eq_circulantGraph`

English:
theorem cycleGraph_eq_circulantGraph
  given: (n : Nat)
  statement: cycleGraph (n + 1) = circulantGraph {1}
  proof: by
  cases n
  · exact edgeFinset_inj.mp rfl
  · aesop

中文:
定理 cycleGraph_eq_circulantGraph
  条件: (n : 自然数)
  结论: cycleGraph (n + 1) = circulantGraph {1}
  证明: by
  cases n
  · exact edgeFinset_inj.mp rfl
  · aesop

Depends on / 依赖: edgeFinset_inj, edgeFinset_inj.mp
-/
theorem cycleGraph_eq_circulantGraph (n : Nat) : cycleGraph (n + 1) = circulantGraph {1} := by
  cases n
  · exact edgeFinset_inj.mp rfl
  · aesop

end SimpleGraph
