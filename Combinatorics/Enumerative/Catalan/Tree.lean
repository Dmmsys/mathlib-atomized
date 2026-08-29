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

/--
Definition of `pairwiseNode` / `pairwiseNode` 的定义

English:
abbreviation pairwiseNode
  signature: (a b : Finset (BinaryTree Unit))
  body: (a ×ˢ b).map ⟨fun x => x.1 △ x.2, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ => fun h => by simpa using h⟩

中文:
缩写 pairwiseNode
  签名: (a b : Finset (BinaryTree Unit))
  定义体: (a ×ˢ b).map ⟨fun x => x.1 △ x.2, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ => fun h => by simpa using h⟩
-/
abbrev pairwiseNode (a b : Finset (BinaryTree Unit)) : Finset (BinaryTree Unit) :=
  (a ×ˢ b).map ⟨fun x => x.1 △ x.2, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ => fun h => by simpa using h⟩

/--
Definition of `treesOfNumNodesEq` / `treesOfNumNodesEq` 的定义

English:
definition treesOfNumNodesEq
  signature: : Nat -> Finset (BinaryTree Unit)
  body: fst_le ijh.2; lia
    · simp_wf; have := snd_le ijh.2; lia

中文:
定义 treesOfNumNodesEq
  签名: : 自然数 -> Finset (BinaryTree Unit)
  定义体: fst_le ijh.2; lia
    · simp_wf; have := snd_le ijh.2; lia

Depends on / 依赖: fst_le
-/
def treesOfNumNodesEq : Nat -> Finset (BinaryTree Unit)
  | 0 => {nil}
  | n + 1 =>
    (antidiagonal n).attach.biUnion fun ijh =>
      pairwiseNode (treesOfNumNodesEq ijh.1.1) (treesOfNumNodesEq ijh.1.2)
  decreasing_by
    · simp_wf; have := fst_le ijh.2; lia
    · simp_wf; have := snd_le ijh.2; lia

/-- **Alias** of `BinaryTree.treesOfNumNodesEq`. -/
@[deprecated BinaryTree.treesOfNumNodesEq (since := "2026-06-07")]
/--
Definition of `_root_.Tree.treesOfNumNodesEq` / `_root_.Tree.treesOfNumNodesEq` 的定义

English:
abbreviation _root_.Tree.treesOfNumNodesEq
  signature: : Nat -> Finset (Tree Unit)
  body: BinaryTree.treesOfNumNodesEq

@[simp]

中文:
缩写 _root_.Tree.treesOfNumNodesEq
  签名: : 自然数 -> Finset (Tree Unit)
  定义体: BinaryTree.treesOfNumNodesEq

@[simp]

Depends on / 依赖: BinaryTree, BinaryTree.treesOfNumNodesEq, treesOfNumNodesEq
-/
abbrev _root_.Tree.treesOfNumNodesEq : Nat -> Finset (Tree Unit) :=
  BinaryTree.treesOfNumNodesEq

@[simp]
/--
theorem `treesOfNumNodesEq_zero` / 定理 `treesOfNumNodesEq_zero`

English:
theorem treesOfNumNodesEq_zero
  statement: treesOfNumNodesEq 0 = {nil}
  proof: by rw [treesOfNumNodesEq]

中文:
定理 treesOfNumNodesEq_zero
  结论: treesOfNumNodesEq 0 = {nil}
  证明: by rw [treesOfNumNodesEq]

Depends on / 依赖: treesOfNumNodesEq
-/
theorem treesOfNumNodesEq_zero : treesOfNumNodesEq 0 = {nil} := by rw [treesOfNumNodesEq]

/--
theorem `treesOfNumNodesEq_succ` / 定理 `treesOfNumNodesEq_succ`

English:
theorem treesOfNumNodesEq_succ
  given: (n : Nat)
  proof: by
  rw [treesOfNumNodesEq]
  ext
  simp

中文:
定理 treesOfNumNodesEq_succ
  条件: (n : 自然数)
  证明: by
  rw [treesOfNumNodesEq]
  ext
  simp

Depends on / 依赖: treesOfNumNodesEq
-/
theorem treesOfNumNodesEq_succ (n : Nat) :
    treesOfNumNodesEq (n + 1) =
      (antidiagonal n).biUnion fun ij =>
        pairwiseNode (treesOfNumNodesEq ij.1) (treesOfNumNodesEq ij.2) := by
  rw [treesOfNumNodesEq]
  ext
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `mem_treesOfNumNodesEq` / 定理 `mem_treesOfNumNodesEq`

English:
theorem mem_treesOfNumNodesEq
  given: {x : BinaryTree Unit} {n : Nat}
  proof: by
  induction x using BinaryTree.unitRecOn generalizing n <;> cases n <;>
    simp [treesOfNumNodesEq_succ, *]

中文:
定理 mem_treesOfNumNodesEq
  条件: {x : BinaryTree Unit} {n : 自然数}
  证明: by
  induction x using BinaryTree.unitRecOn generalizing n <;> cases n <;>
    simp [treesOfNumNodesEq_succ, *]

Depends on / 依赖: BinaryTree, BinaryTree.unitRecOn, generalizing, treesOfNumNodesEq_succ, unitRecOn
-/
theorem mem_treesOfNumNodesEq {x : BinaryTree Unit} {n : Nat} :
    x in treesOfNumNodesEq n ↔ x.numNodes = n := by
  induction x using BinaryTree.unitRecOn generalizing n <;> cases n <;>
    simp [treesOfNumNodesEq_succ, *]

/--
theorem `mem_treesOfNumNodesEq_numNodes` / 定理 `mem_treesOfNumNodesEq_numNodes`

English:
theorem mem_treesOfNumNodesEq_numNodes
  given: (x : BinaryTree Unit)
  statement: x in treesOfNumNodesEq x.numNodes
  proof: mem_treesOfNumNodesEq.mpr rfl

@[simp, norm_cast]

中文:
定理 mem_treesOfNumNodesEq_numNodes
  条件: (x : BinaryTree Unit)
  结论: x in treesOfNumNodesEq x.numNodes
  证明: mem_treesOfNumNodesEq.mpr rfl

@[simp, norm_cast]

Depends on / 依赖: mem_treesOfNumNodesEq, mem_treesOfNumNodesEq.mpr
-/
theorem mem_treesOfNumNodesEq_numNodes (x : BinaryTree Unit) : x in treesOfNumNodesEq x.numNodes :=
  mem_treesOfNumNodesEq.mpr rfl

@[simp, norm_cast]
/--
theorem `coe_treesOfNumNodesEq` / 定理 `coe_treesOfNumNodesEq`

English:
theorem coe_treesOfNumNodesEq
  given: (n : Nat)
  proof: Set.ext (by simp)

中文:
定理 coe_treesOfNumNodesEq
  条件: (n : 自然数)
  证明: Set.ext (by simp)

Depends on / 依赖: Set.ext
-/
theorem coe_treesOfNumNodesEq (n : Nat) :
    ↑(treesOfNumNodesEq n) = { x : BinaryTree Unit | x.numNodes = n } :=
  Set.ext (by simp)

/--
theorem `treesOfNumNodesEq_card_eq_catalan` / 定理 `treesOfNumNodesEq_card_eq_catalan`

English:
theorem treesOfNumNodesEq_card_eq_catalan
  given: (n : Nat)
  statement: #(treesOfNumNodesEq n) = catalan n
  proof: by
  induction n using Nat.case_strong_induction_on with
  | hz => simp
  | hi n ih =>
    rw [treesOfNumNodesEq_succ]; rw [card_biUnion]; rw [catalan_succ']
    · apply sum_congr rfl
      rintro ⟨i, j⟩ H
      rw [card_map]; rw [card_product]; rw [ih _ (fst_le H)]; rw [ih _ (snd_le H)]
    · simp_

中文:
定理 treesOfNumNodesEq_card_eq_catalan
  条件: (n : 自然数)
  结论: #(treesOfNumNodesEq n) = catalan n
  证明: by
  induction n using Nat.case_strong_induction_on with
  | hz => simp
  | hi n ih =>
    rw [treesOfNumNodesEq_succ]; rw [card_biUnion]; rw [catalan_succ']
    · apply sum_congr rfl
      rintro ⟨i, j⟩ H
      rw [card_map]; rw [card_product]; rw [ih _ (fst_le H)]; rw [ih _ (snd_le H)]
    · simp_

Depends on / 依赖: Nat.case_strong_induction_on, Pairwise, PairwiseDisjoint, Set.Pairwise, Set.PairwiseDisjoint, card_biUnion, card_map, card_product, case_strong_induction_on, catalan_succ, disjoint_left, fst_le, simp_rw, snd_le, sum_congr, treesOfNumNodesEq_succ
-/
theorem treesOfNumNodesEq_card_eq_catalan (n : Nat) : #(treesOfNumNodesEq n) = catalan n := by
  induction n using Nat.case_strong_induction_on with
  | hz => simp
  | hi n ih =>
    rw [treesOfNumNodesEq_succ]; rw [card_biUnion]; rw [catalan_succ']
    · apply sum_congr rfl
      rintro ⟨i, j⟩ H
      rw [card_map]; rw [card_product]; rw [ih _ (fst_le H)]; rw [ih _ (snd_le H)]
    · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left]
      aesop

end BinaryTree
