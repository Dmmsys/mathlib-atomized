/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Disjointed
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify

/-!
# Decomposing a locally finite ordered ring into boxes

This file proves that any locally finite ordered ring can be decomposed into "boxes", namely
differences of consecutive intervals.

## Implementation notes

We don't need the full ring structure, only that there is an order embedding `ℤ → `
-/

@[expose] public section

/-! ### General locally finite ordered ring -/

namespace Finset
variable {α : Type*} [Ring α] [PartialOrder α] [IsOrderedRing α] [LocallyFiniteOrder α] {n : Nat}

/--
lemma `Icc_neg_mono` / 引理 `Icc_neg_mono`

English:
lemma Icc_neg_mono
  statement: Monotone fun n : Nat => Icc (-n : α) n
  proof: by
  refine fun m n hmn => by apply Icc_subset_Icc <;> simpa using Nat.mono_cast hmn

中文:
引理 Icc_neg_mono
  结论: Monotone fun n : 自然数 => Icc (-n : α) n
  证明: by
  refine fun m n hmn => by apply Icc_subset_Icc <;> simpa using Nat.mono_cast hmn
-/
private lemma Icc_neg_mono : Monotone fun n : Nat => Icc (-n : α) n := by
  refine fun m n hmn => by apply Icc_subset_Icc <;> simpa using Nat.mono_cast hmn

variable [DecidableEq α]

/--
Definition of `box` / `box` 的定义

English:
definition box
  signature: : Nat -> Finset α
  body: disjointed fun n => Icc (-n : α) n

omit [IsOrderedRing α] in

中文:
定义 box
  签名: : 自然数 -> Finset α
  定义体: disjointed fun n => Icc (-n : α) n

omit [IsOrderedRing α] in

Depends on / 依赖: disjointed
-/
def box : Nat -> Finset α := disjointed fun n => Icc (-n : α) n

omit [IsOrderedRing α] in
/--
lemma `box_zero` / 引理 `box_zero`

English:
lemma box_zero
  statement: (box 0 : Finset α) = {0}
  proof: by simp [box]

中文:
引理 box_zero
  结论: (box 0 : Finset α) = {0}
  证明: by simp [box]
-/
@[simp] lemma box_zero : (box 0 : Finset α) = {0} := by simp [box]

/--
lemma `box_succ_eq_sdiff` / 引理 `box_succ_eq_sdiff`

English:
lemma box_succ_eq_sdiff
  given: (n : Nat)
  proof: by
  rw [box]; rw [Icc_neg_mono.disjointed_add_one]
  simp only [Nat.cast_add_one, Nat.succ_eq_add_one]

中文:
引理 box_succ_eq_sdiff
  条件: (n : 自然数)
  证明: by
  rw [box]; rw [Icc_neg_mono.disjointed_add_one]
  simp only [Nat.cast_add_one, Nat.succ_eq_add_one]

Depends on / 依赖: Icc_neg_mono, Icc_neg_mono.disjointed_add_one, Nat.cast_add_one, Nat.succ_eq_add_one, cast_add_one, disjointed_add_one, succ_eq_add_one
-/
lemma box_succ_eq_sdiff (n : Nat) :
    box (n + 1) = Icc (-n.succ : α) n.succ \ Icc (-n) n := by
  rw [box]; rw [Icc_neg_mono.disjointed_add_one]
  simp only [Nat.cast_add_one, Nat.succ_eq_add_one]

/--
lemma `disjoint_box_succ_prod` / 引理 `disjoint_box_succ_prod`

English:
lemma disjoint_box_succ_prod
  given: (n : Nat)
  statement: Disjoint (box (n + 1)) (Icc (-n : α) n)
  proof: by
  rw [box_succ_eq_sdiff]; exact disjoint_sdiff_self_left

中文:
引理 disjoint_box_succ_prod
  条件: (n : 自然数)
  结论: Disjoint (box (n + 1)) (Icc (-n : α) n)
  证明: by
  rw [box_succ_eq_sdiff]; exact disjoint_sdiff_self_left

Depends on / 依赖: box_succ_eq_sdiff, disjoint_sdiff_self_left
-/
lemma disjoint_box_succ_prod (n : Nat) : Disjoint (box (n + 1)) (Icc (-n : α) n) := by
  rw [box_succ_eq_sdiff]; exact disjoint_sdiff_self_left

/--
lemma `box_succ_union_prod` / 引理 `box_succ_union_prod`

English:
lemma box_succ_union_prod
  given: (n : Nat)
  proof: Icc_neg_mono.disjointed_add_one_sup _

中文:
引理 box_succ_union_prod
  条件: (n : 自然数)
  证明: Icc_neg_mono.disjointed_add_one_sup _
-/
@[simp] lemma box_succ_union_prod (n : Nat) :
    box (n + 1) union Icc (-n : α) n = Icc (-n.succ : α) n.succ :=
  Icc_neg_mono.disjointed_add_one_sup _

/--
lemma `box_succ_disjUnion` / 引理 `box_succ_disjUnion`

English:
lemma box_succ_disjUnion
  given: (n : Nat)
  proof: by rw [disjUnion_eq_union, box_succ_union_prod]

中文:
引理 box_succ_disjUnion
  条件: (n : 自然数)
  证明: by rw [disjUnion_eq_union, box_succ_union_prod]

Depends on / 依赖: box_succ_union_prod, disjUnion_eq_union
-/
lemma box_succ_disjUnion (n : Nat) :
    (box (n + 1)).disjUnion (Icc (-n : α) n) (disjoint_box_succ_prod _) =
      Icc (-n.succ : α) n.succ := by rw [disjUnion_eq_union, box_succ_union_prod]

/--
lemma `zero_mem_box` / 引理 `zero_mem_box`

English:
lemma zero_mem_box
  statement: (0 : α) in box n ↔ n = 0
  proof: by cases n <;> simp [box_succ_eq_sdiff]

中文:
引理 zero_mem_box
  结论: (0 : α) in box n ↔ n = 0
  证明: by cases n <;> simp [box_succ_eq_sdiff]
-/
@[simp] lemma zero_mem_box : (0 : α) in box n ↔ n = 0 := by cases n <;> simp [box_succ_eq_sdiff]

/--
lemma `eq_zero_iff_eq_zero_of_mem_box` / 引理 `eq_zero_iff_eq_zero_of_mem_box`

English:
lemma eq_zero_iff_eq_zero_of_mem_box
  given: {x : α} (hx : x in box n)
  statement: x = 0 ↔ n = 0
  proof: ⟨zero_mem_box.mp ∘ (· ▸ hx), fun hn => by rwa [hn, box_zero, mem_singleton] at hx⟩

中文:
引理 eq_zero_iff_eq_zero_of_mem_box
  条件: {x : α} (hx : x in box n)
  结论: x = 0 ↔ n = 0
  证明: ⟨zero_mem_box.mp ∘ (· ▸ hx), fun hn => by rwa [hn, box_zero, mem_singleton] at hx⟩

Depends on / 依赖: box_zero, mem_singleton, zero_mem_box, zero_mem_box.mp
-/
lemma eq_zero_iff_eq_zero_of_mem_box {x : α} (hx : x in box n) : x = 0 ↔ n = 0 :=
  ⟨zero_mem_box.mp ∘ (· ▸ hx), fun hn => by rwa [hn, box_zero, mem_singleton] at hx⟩

end Finset

open Finset

/-! ### Product of locally finite ordered rings -/

namespace Prod
variable {α β : Type*} [Ring α] [PartialOrder α] [IsOrderedRing α]
  [Ring β] [PartialOrder β] [IsOrderedRing β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableEq α] [DecidableEq β] [DecidableLE (α × β)]

/--
lemma `card_box_succ` / 引理 `card_box_succ`

English:
lemma card_box_succ
  given: (n : Nat)
  proof: by
  rw [box_succ_eq_sdiff]; rw [card_sdiff_of_subset (Icc_neg_mono n.le_succ)]; rw [Finset.card_Icc_prod]; rw [Finset.card_Icc_prod]
  simp_rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, neg_add_rev, fst_add, fst_neg,
    fst_one, fst_natCast, snd_add, snd_neg, snd_one, snd_natCast]

中文:
引理 card_box_succ
  条件: (n : 自然数)
  证明: by
  rw [box_succ_eq_sdiff]; rw [card_sdiff_of_subset (Icc_neg_mono n.le_succ)]; rw [Finset.card_Icc_prod]; rw [Finset.card_Icc_prod]
  simp_rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, neg_add_rev, fst_add, fst_neg,
    fst_one, fst_natCast, snd_add, snd_neg, snd_one, snd_natCast]
-/
@[simp] lemma card_box_succ (n : Nat) :
    #(box (n + 1) : Finset (α × β)) =
      #(Icc (-n.succ : α) n.succ) * #(Icc (-n.succ : β) n.succ) -
        #(Icc (-n : α) n) * #(Icc (-n : β) n) := by
  rw [box_succ_eq_sdiff]; rw [card_sdiff_of_subset (Icc_neg_mono n.le_succ)]; rw [Finset.card_Icc_prod]; rw [Finset.card_Icc_prod]
  simp_rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, neg_add_rev, fst_add, fst_neg,
    fst_one, fst_natCast, snd_add, snd_neg, snd_one, snd_natCast]

end Prod

/-! ### `ℤ × ℤ` -/

namespace Int
variable {x : Int × Int}

attribute [norm_cast] toNat_natCast

/--
lemma `card_box` / 引理 `card_box`

English:
lemma card_box
  statement: forall {n}, n != 0 -> #(box n : Finset (Int × Int)) = 8 * n

中文:
引理 card_box
  结论: 对任意 {n}, n != 0 -> #(box n : Finset (整数 × 整数)) = 8 * n
-/
lemma card_box : forall {n}, n != 0 -> #(box n : Finset (Int × Int)) = 8 * n
  | n + 1, _ => by
    simp_rw [Prod.card_box_succ, card_Icc, sub_neg_eq_add]
    norm_cast
    refine tsub_eq_of_eq_add ?_
    zify
    ring

/--
lemma `mem_box` / 引理 `mem_box`

English:
lemma mem_box
  statement: forall {n}, x in box n ↔ max x.1.natAbs x.2.natAbs = n

中文:
引理 mem_box
  结论: 对任意 {n}, x in box n ↔ max x.1.natAbs x.2.natAbs = n
-/
@[simp] lemma mem_box : forall {n}, x in box n ↔ max x.1.natAbs x.2.natAbs = n
  | 0 => by simp [Prod.ext_iff]
  | n + 1 => by
    simp [box_succ_eq_sdiff, Prod.le_def]
    omega

-- TODO: Can this be generalised to locally finite archimedean ordered rings?
/--
lemma `existsUnique_mem_box` / 引理 `existsUnique_mem_box`

English:
lemma existsUnique_mem_box
  given: (x : Int × Int)
  statement: exists! n : Nat, x in box n
  proof: by
  use max x.1.natAbs x.2.natAbs; simp only [mem_box, and_self_iff, forall_eq']

中文:
引理 existsUnique_mem_box
  条件: (x : 整数 × 整数)
  结论: 存在! n : 自然数, x in box n
  证明: by
  use max x.1.natAbs x.2.natAbs; simp only [mem_box, and_self_iff, forall_eq']

Depends on / 依赖: and_self_iff, forall_eq, mem_box, natAbs
-/
lemma existsUnique_mem_box (x : Int × Int) : exists! n : Nat, x in box n := by
  use max x.1.natAbs x.2.natAbs; simp only [mem_box, and_self_iff, forall_eq']

end Int
