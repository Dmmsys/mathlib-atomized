/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Basic

/-!
# Split a box along one or more hyperplanes

## Main definitions

A hyperplane `{x : ι → ℝ | x i = a}` splits a rectangular box `I : BoxIntegral.Box ι` into two
smaller boxes. If `a ∉ Ioo (I.lower i, I.upper i)`, then one of these boxes is empty, so it is not a
box in the sense of `BoxIntegral.Box`.

We introduce the following definitions.

* `BoxIntegral.Box.splitLower I i a` and `BoxIntegral.Box.splitUpper I i a` are these boxes (as
  `WithBot (BoxIntegral.Box ι)`);
* `BoxIntegral.Prepartition.split I i a` is the partition of `I` made of these two boxes (or of one
  box `I` if one of these boxes is empty);
* `BoxIntegral.Prepartition.splitMany I s`, where `s : Finset (ι × ℝ)` is a finite set of
  hyperplanes `{x : ι → ℝ | x i = a}` encoded as pairs `(i, a)`, is the partition of `I` made by
  cutting it along all the hyperplanes in `s`.

## Main results

The main result `BoxIntegral.Prepartition.exists_iUnion_eq_sdiff` says that any prepartition `π` of
`I` admits a prepartition `π'` of `I` that covers exactly `I \ π.iUnion`. One of these prepartitions
is available as `BoxIntegral.Prepartition.compl`.

## Tags

rectangular box, partition, hyperplane
-/

@[expose] public section

noncomputable section

open Function Set Filter

namespace BoxIntegral

variable {ι M : Type*} {n : Nat}

namespace Box

variable {I : Box ι} {i : ι} {x : Real} {y : ι -> Real}

open scoped Classical in
/--
Definition of `splitLower` / `splitLower` 的定义

English:
definition splitLower
  signature: (I : Box ι) (i : ι) (x : Real)
  body: mk' I.lower (update I.upper i (min x (I.upper i)))

@[simp]

中文:
定义 splitLower
  签名: (I : Box ι) (i : ι) (x : 实数)
  定义体: mk' I.lower (update I.upper i (min x (I.upper i)))

@[simp]

Depends on / 依赖: I.lower, I.upper, update
-/
def splitLower (I : Box ι) (i : ι) (x : Real) : WithBot (Box ι) :=
  mk' I.lower (update I.upper i (min x (I.upper i)))

@[simp]
/--
theorem `coe_splitLower` / 定理 `coe_splitLower`

English:
theorem coe_splitLower
  statement: (splitLower I i x : Set (ι -> Real)) = ↑I inter { y | y i <= x }
  proof: by
  rw [splitLower]; rw [coe_mk']
  ext y
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_ofPred_eq, forall_and, ← Pi.le_def,
    le_update_iff, le_min_iff, and_assoc, and_forall_ne (p := fun j => y j <= upper I j) i, mem_def]
  rw [and_comm (a := y i <= x)]

中文:
定理 coe_splitLower
  结论: (splitLower I i x : 集合 (ι -> 实数)) = ↑I inter { y | y i <= x }
  证明: by
  rw [splitLower]; rw [coe_mk']
  ext y
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_ofPred_eq, forall_and, ← Pi.le_def,
    le_update_iff, le_min_iff, and_assoc, and_forall_ne (p := fun j => y j <= upper I j) i, mem_def]
  rw [and_comm (a := y i <= x)]

Depends on / 依赖: Pi.le_def, and_assoc, and_comm, and_forall_ne, coe_mk, forall_and, le_def, le_min_iff, le_update_iff, mem_Ioc, mem_coe, mem_def, mem_inter_iff, mem_ofPred_eq, mem_univ_pi, splitLower
-/
theorem coe_splitLower : (splitLower I i x : Set (ι -> Real)) = ↑I inter { y | y i <= x } := by
  rw [splitLower]; rw [coe_mk']
  ext y
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_ofPred_eq, forall_and, ← Pi.le_def,
    le_update_iff, le_min_iff, and_assoc, and_forall_ne (p := fun j => y j <= upper I j) i, mem_def]
  rw [and_comm (a := y i <= x)]

/--
theorem `splitLower_le` / 定理 `splitLower_le`

English:
theorem splitLower_le
  statement: I.splitLower i x <= I
  proof: withBotCoe_subset_iff.1 by simp

@[simp]

中文:
定理 splitLower_le
  结论: I.splitLower i x <= I
  证明: withBotCoe_subset_iff.1 by simp

@[simp]

Depends on / 依赖: withBotCoe_subset_iff
-/
theorem splitLower_le : I.splitLower i x <= I :=
withBotCoe_subset_iff.1 by simp

@[simp]
/--
theorem `splitLower_eq_bot` / 定理 `splitLower_eq_bot`

English:
theorem splitLower_eq_bot
  given: {i x}
  statement: I.splitLower i x = ⊥ ↔ x <= I.lower i
  proof: by
  classical
  rw [splitLower]; rw [mk'_eq_bot]; rw [exists_update_iff I.upper fun j y => y <= I.lower j]
  simp [(I.lower_lt_upper _).not_ge]

@[simp]

中文:
定理 splitLower_eq_bot
  条件: {i x}
  结论: I.splitLower i x = ⊥ ↔ x <= I.lower i
  证明: by
  classical
  rw [splitLower]; rw [mk'_eq_bot]; rw [exists_update_iff I.upper fun j y => y <= I.lower j]
  simp [(I.lower_lt_upper _).not_ge]

@[simp]

Depends on / 依赖: I.lower, I.lower_lt_upper, I.upper, _eq_bot, classical, exists_update_iff, lower_lt_upper, not_ge, splitLower
-/
theorem splitLower_eq_bot {i x} : I.splitLower i x = ⊥ ↔ x <= I.lower i := by
  classical
  rw [splitLower]; rw [mk'_eq_bot]; rw [exists_update_iff I.upper fun j y => y <= I.lower j]
  simp [(I.lower_lt_upper _).not_ge]

@[simp]
/--
theorem `splitLower_eq_self` / 定理 `splitLower_eq_self`

English:
theorem splitLower_eq_self
  statement: I.splitLower i x = I ↔ I.upper i <= x
  proof: by
  simp [splitLower]

中文:
定理 splitLower_eq_self
  结论: I.splitLower i x = I ↔ I.upper i <= x
  证明: by
  simp [splitLower]

Depends on / 依赖: splitLower
-/
theorem splitLower_eq_self : I.splitLower i x = I ↔ I.upper i <= x := by
  simp [splitLower]

/--
theorem `splitLower_def` / 定理 `splitLower_def`

English:
theorem splitLower_def
  statement: [DecidableEq ι] {i x} (h : x in Ioo (I.lower i) (I.upper i))
  proof: by
  simp +unfoldPartialApp only [splitLower, mk'_eq_coe, min_eq_left h.2.le,
    update, and_self]

中文:
定理 splitLower_def
  结论: [DecidableEq ι] {i x} (h : x in 开区间 (I.lower i) (I.upper i))
  证明: by
  simp +unfoldPartialApp only [splitLower, mk'_eq_coe, min_eq_left h.2.le,
    update, and_self]

Depends on / 依赖: I.lower, I.lower_lt_upper, I.splitLower, I.upper, _eq_coe, and_self, forall_update_iff, lower_lt_upper, min_eq_left, splitLower, unfoldPartialApp, update
-/
theorem splitLower_def [DecidableEq ι] {i x} (h : x in Ioo (I.lower i) (I.upper i))
    (h' : forall j, I.lower j < update I.upper i x j :=
      (forall_update_iff I.upper fun j y => I.lower j < y).2
        ⟨h.1, fun _ _ => I.lower_lt_upper _⟩) :
    I.splitLower i x = (⟨I.lower, update I.upper i x, h'⟩ : Box ι) := by
  simp +unfoldPartialApp only [splitLower, mk'_eq_coe, min_eq_left h.2.le,
    update, and_self]

open scoped Classical in
/--
Definition of `splitUpper` / `splitUpper` 的定义

English:
definition splitUpper
  signature: (I : Box ι) (i : ι) (x : Real)
  body: mk' (update I.lower i (max x (I.lower i))) I.upper

@[simp]

中文:
定义 splitUpper
  签名: (I : Box ι) (i : ι) (x : 实数)
  定义体: mk' (update I.lower i (max x (I.lower i))) I.upper

@[simp]

Depends on / 依赖: I.lower, I.upper, update
-/
def splitUpper (I : Box ι) (i : ι) (x : Real) : WithBot (Box ι) :=
  mk' (update I.lower i (max x (I.lower i))) I.upper

@[simp]
/--
theorem `coe_splitUpper` / 定理 `coe_splitUpper`

English:
theorem coe_splitUpper
  statement: (splitUpper I i x : Set (ι -> Real)) = ↑I inter { y | x < y i }
  proof: by
  classical
  rw [splitUpper]; rw [coe_mk']
  ext y
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_ofPred_eq, forall_and,
    forall_update_iff I.lower fun j z => z < y j, max_lt_iff, and_assoc (a := x < y i),
    and_forall_ne (p := fun j => lower I j < y j) i, mem_def]
  exact a

中文:
定理 coe_splitUpper
  结论: (splitUpper I i x : 集合 (ι -> 实数)) = ↑I inter { y | x < y i }
  证明: by
  classical
  rw [splitUpper]; rw [coe_mk']
  ext y
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_ofPred_eq, forall_and,
    forall_update_iff I.lower fun j z => z < y j, max_lt_iff, and_assoc (a := x < y i),
    and_forall_ne (p := fun j => lower I j < y j) i, mem_def]
  exact a

Depends on / 依赖: I.lower, and_assoc, and_comm, and_forall_ne, classical, coe_mk, forall_and, forall_update_iff, max_lt_iff, mem_Ioc, mem_coe, mem_def, mem_inter_iff, mem_ofPred_eq, mem_univ_pi, splitUpper
-/
theorem coe_splitUpper : (splitUpper I i x : Set (ι -> Real)) = ↑I inter { y | x < y i } := by
  classical
  rw [splitUpper]; rw [coe_mk']
  ext y
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_ofPred_eq, forall_and,
    forall_update_iff I.lower fun j z => z < y j, max_lt_iff, and_assoc (a := x < y i),
    and_forall_ne (p := fun j => lower I j < y j) i, mem_def]
  exact and_comm

/--
theorem `splitUpper_le` / 定理 `splitUpper_le`

English:
theorem splitUpper_le
  statement: I.splitUpper i x <= I
  proof: withBotCoe_subset_iff.1 by simp

@[simp]

中文:
定理 splitUpper_le
  结论: I.splitUpper i x <= I
  证明: withBotCoe_subset_iff.1 by simp

@[simp]

Depends on / 依赖: withBotCoe_subset_iff
-/
theorem splitUpper_le : I.splitUpper i x <= I :=
withBotCoe_subset_iff.1 by simp

@[simp]
/--
theorem `splitUpper_eq_bot` / 定理 `splitUpper_eq_bot`

English:
theorem splitUpper_eq_bot
  given: {i x}
  statement: I.splitUpper i x = ⊥ ↔ I.upper i <= x
  proof: by
  classical
  rw [splitUpper]; rw [mk'_eq_bot]; rw [exists_update_iff I.lower fun j y => I.upper j <= y]
  simp [(I.lower_lt_upper _).not_ge]

@[simp]

中文:
定理 splitUpper_eq_bot
  条件: {i x}
  结论: I.splitUpper i x = ⊥ ↔ I.upper i <= x
  证明: by
  classical
  rw [splitUpper]; rw [mk'_eq_bot]; rw [exists_update_iff I.lower fun j y => I.upper j <= y]
  simp [(I.lower_lt_upper _).not_ge]

@[simp]

Depends on / 依赖: I.lower, I.lower_lt_upper, I.upper, _eq_bot, classical, exists_update_iff, lower_lt_upper, not_ge, splitUpper
-/
theorem splitUpper_eq_bot {i x} : I.splitUpper i x = ⊥ ↔ I.upper i <= x := by
  classical
  rw [splitUpper]; rw [mk'_eq_bot]; rw [exists_update_iff I.lower fun j y => I.upper j <= y]
  simp [(I.lower_lt_upper _).not_ge]

@[simp]
/--
theorem `splitUpper_eq_self` / 定理 `splitUpper_eq_self`

English:
theorem splitUpper_eq_self
  statement: I.splitUpper i x = I ↔ x <= I.lower i
  proof: by
  simp [splitUpper]

中文:
定理 splitUpper_eq_self
  结论: I.splitUpper i x = I ↔ x <= I.lower i
  证明: by
  simp [splitUpper]

Depends on / 依赖: splitUpper
-/
theorem splitUpper_eq_self : I.splitUpper i x = I ↔ x <= I.lower i := by
  simp [splitUpper]

/--
theorem `splitUpper_def` / 定理 `splitUpper_def`

English:
theorem splitUpper_def
  statement: [DecidableEq ι] {i x} (h : x in Ioo (I.lower i) (I.upper i))
  proof: by
  simp +unfoldPartialApp only [splitUpper, mk'_eq_coe, max_eq_left h.1.le,
    update, and_self]

中文:
定理 splitUpper_def
  结论: [DecidableEq ι] {i x} (h : x in 开区间 (I.lower i) (I.upper i))
  证明: by
  simp +unfoldPartialApp only [splitUpper, mk'_eq_coe, max_eq_left h.1.le,
    update, and_self]

Depends on / 依赖: I.lower, I.lower_lt_upper, I.splitUpper, I.upper, _eq_coe, and_self, forall_update_iff, lower_lt_upper, max_eq_left, splitUpper, unfoldPartialApp, update
-/
theorem splitUpper_def [DecidableEq ι] {i x} (h : x in Ioo (I.lower i) (I.upper i))
    (h' : forall j, update I.lower i x j < I.upper j :=
      (forall_update_iff I.lower fun j y => y < I.upper j).2
        ⟨h.2, fun _ _ => I.lower_lt_upper _⟩) :
    I.splitUpper i x = (⟨update I.lower i x, I.upper, h'⟩ : Box ι) := by
  simp +unfoldPartialApp only [splitUpper, mk'_eq_coe, max_eq_left h.1.le,
    update, and_self]

/--
theorem `disjoint_splitLower_splitUpper` / 定理 `disjoint_splitLower_splitUpper`

English:
theorem disjoint_splitLower_splitUpper
  given: (I : Box ι) (i : ι) (x : Real)
  proof: by
  rw [← disjoint_withBotCoe]; rw [coe_splitLower]; rw [coe_splitUpper]
  refine (Disjoint.inf_left' _ ?_).inf_right' _
  rw [Set.disjoint_left]
  exact fun y (hle : y i <= x) hlt => not_lt_of_ge hle hlt

中文:
定理 disjoint_splitLower_splitUpper
  条件: (I : Box ι) (i : ι) (x : 实数)
  证明: by
  rw [← disjoint_withBotCoe]; rw [coe_splitLower]; rw [coe_splitUpper]
  refine (Disjoint.inf_left' _ ?_).inf_right' _
  rw [Set.disjoint_left]
  exact fun y (hle : y i <= x) hlt => not_lt_of_ge hle hlt

Depends on / 依赖: Disjoint, Disjoint.inf_left, Set.disjoint_left, coe_splitLower, coe_splitUpper, disjoint_left, disjoint_withBotCoe, inf_left, inf_right, not_lt_of_ge
-/
theorem disjoint_splitLower_splitUpper (I : Box ι) (i : ι) (x : Real) :
    Disjoint (I.splitLower i x) (I.splitUpper i x) := by
  rw [← disjoint_withBotCoe]; rw [coe_splitLower]; rw [coe_splitUpper]
  refine (Disjoint.inf_left' _ ?_).inf_right' _
  rw [Set.disjoint_left]
  exact fun y (hle : y i <= x) hlt => not_lt_of_ge hle hlt

/--
theorem `splitLower_ne_splitUpper` / 定理 `splitLower_ne_splitUpper`

English:
theorem splitLower_ne_splitUpper
  given: (I : Box ι) (i : ι) (x : Real)
  proof: by
  rcases le_or_gt x (I.lower i) with h | _
  · rw [splitUpper_eq_self.2 h, splitLower_eq_bot.2 h]
    exact WithBot.bot_ne_coe
  · refine (disjoint_splitLower_splitUpper I i x).ne ?_
    rwa [Ne, splitLower_eq_bot, not_le]

中文:
定理 splitLower_ne_splitUpper
  条件: (I : Box ι) (i : ι) (x : 实数)
  证明: by
  rcases le_or_gt x (I.lower i) with h | _
  · rw [splitUpper_eq_self.2 h, splitLower_eq_bot.2 h]
    exact WithBot.bot_ne_coe
  · refine (disjoint_splitLower_splitUpper I i x).ne ?_
    rwa [Ne, splitLower_eq_bot, not_le]

Depends on / 依赖: I.lower, WithBot, WithBot.bot_ne_coe, bot_ne_coe, disjoint_splitLower_splitUpper, le_or_gt, not_le, splitLower_eq_bot, splitUpper_eq_self
-/
theorem splitLower_ne_splitUpper (I : Box ι) (i : ι) (x : Real) :
    I.splitLower i x != I.splitUpper i x := by
  rcases le_or_gt x (I.lower i) with h | _
  · rw [splitUpper_eq_self.2 h, splitLower_eq_bot.2 h]
    exact WithBot.bot_ne_coe
  · refine (disjoint_splitLower_splitUpper I i x).ne ?_
    rwa [Ne, splitLower_eq_bot, not_le]

end Box

namespace Prepartition

variable {I J : Box ι} {i : ι} {x : Real}

open scoped Classical in
/--
Definition of `split` / `split` 的定义

English:
definition split
  signature: (I : Box ι) (i : ι) (x : Real)
  body: ofWithBot {I.splitLower i x, I.splitUpper i x}
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro J (rfl | rfl)
      exacts [Box.splitLower_le, Box.splitUpper_le])
    (by
      simp only [Finset.coe_insert, Finset.coe_singleton, true_and, Set.mem_singleton_iff,
        

中文:
定义 split
  签名: (I : Box ι) (i : ι) (x : 实数)
  定义体: ofWithBot {I.splitLower i x, I.splitUpper i x}
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro J (rfl | rfl)
      exacts [Box.splitLower_le, Box.splitUpper_le])
    (by
      simp only [Finset.coe_insert, Finset.coe_singleton, true_and, Set.mem_singleton_iff,
        

Depends on / 依赖: Box.splitLower_le, Box.splitUpper_le, Finset, Finset.coe_insert, Finset.coe_singleton, Finset.mem_insert, Finset.mem_singleton, I.disjoint_splitLower_splitUpper, I.splitLower, I.splitUpper, Set.mem_singleton_iff, coe_insert, coe_singleton, disjoint_splitLower_splitUpper, exacts, mem_insert, mem_singleton, mem_singleton_iff, ofWithBot, pairwise_insert_of_symm
-/
def split (I : Box ι) (i : ι) (x : Real) : Prepartition I :=
  ofWithBot {I.splitLower i x, I.splitUpper i x}
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro J (rfl | rfl)
      exacts [Box.splitLower_le, Box.splitUpper_le])
    (by
      simp only [Finset.coe_insert, Finset.coe_singleton, true_and, Set.mem_singleton_iff,
        pairwise_insert_of_symm, pairwise_singleton]
      rintro J rfl -
      exact I.disjoint_splitLower_splitUpper i x)

@[simp]
/--
theorem `mem_split_iff` / 定理 `mem_split_iff`

English:
theorem mem_split_iff
  statement: J in split I i x ↔ ↑J = I.splitLower i x ∨ ↑J = I.splitUpper i x
  proof: by
  simp [split]

中文:
定理 mem_split_iff
  结论: J in split I i x ↔ ↑J = I.splitLower i x ∨ ↑J = I.splitUpper i x
  证明: by
  simp [split]
-/
theorem mem_split_iff : J in split I i x ↔ ↑J = I.splitLower i x ∨ ↑J = I.splitUpper i x := by
  simp [split]

/--
theorem `mem_split_iff'` / 定理 `mem_split_iff'`

English:
theorem mem_split_iff'
  statement: J in split I i x ↔
  proof: by
  simp [mem_split_iff, ← Box.withBotCoe_inj]

@[simp]

中文:
定理 mem_split_iff'
  结论: J in split I i x ↔
  证明: by
  simp [mem_split_iff, ← Box.withBotCoe_inj]

@[simp]

Depends on / 依赖: Box.withBotCoe_inj, mem_split_iff, withBotCoe_inj
-/
theorem mem_split_iff' : J in split I i x ↔
    (J : Set (ι -> Real)) = ↑I inter { y | y i <= x } ∨ (J : Set (ι -> Real)) = ↑I inter { y | x < y i } := by
  simp [mem_split_iff, ← Box.withBotCoe_inj]

@[simp]
/--
theorem `iUnion_split` / 定理 `iUnion_split`

English:
theorem iUnion_split
  given: (I : Box ι) (i : ι) (x : Real)
  statement: (split I i x).iUnion = I
  proof: by
  simp [split, ← inter_union_distrib_left, ← ofPred_or, le_or_gt]

中文:
定理 iUnion_split
  条件: (I : Box ι) (i : ι) (x : 实数)
  结论: (split I i x).iUnion = I
  证明: by
  simp [split, ← inter_union_distrib_left, ← ofPred_or, le_or_gt]

Depends on / 依赖: inter_union_distrib_left, le_or_gt, ofPred_or
-/
theorem iUnion_split (I : Box ι) (i : ι) (x : Real) : (split I i x).iUnion = I := by
  simp [split, ← inter_union_distrib_left, ← ofPred_or, le_or_gt]

/--
theorem `isPartitionSplit` / 定理 `isPartitionSplit`

English:
theorem isPartitionSplit
  given: (I : Box ι) (i : ι) (x : Real)
  statement: IsPartition (split I i x)
  proof: isPartition_iff_iUnion_eq.2 iUnion_split I i x

中文:
定理 isPartitionSplit
  条件: (I : Box ι) (i : ι) (x : 实数)
  结论: IsPartition (split I i x)
  证明: isPartition_iff_iUnion_eq.2 iUnion_split I i x

Depends on / 依赖: iUnion_split, isPartition_iff_iUnion_eq
-/
theorem isPartitionSplit (I : Box ι) (i : ι) (x : Real) : IsPartition (split I i x) :=
isPartition_iff_iUnion_eq.2 iUnion_split I i x

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sum_split_boxes` / 定理 `sum_split_boxes`

English:
theorem sum_split_boxes
  given: {M : Type*} [AddCommMonoid M] (I : Box ι) (i : ι) (x : Real) (f : Box ι -> M)
  proof: by
  classical
  rw [split]; rw [sum_ofWithBot]; rw [Finset.sum_pair (I.splitLower_ne_splitUpper i x)]

中文:
定理 sum_split_boxes
  条件: {M : 类型} [加法交换幺半群 M] (I : Box ι) (i : ι) (x : 实数) (f : Box ι -> M)
  证明: by
  classical
  rw [split]; rw [sum_ofWithBot]; rw [Finset.sum_pair (I.splitLower_ne_splitUpper i x)]

Depends on / 依赖: Finset, Finset.sum_pair, I.splitLower_ne_splitUpper, classical, splitLower_ne_splitUpper, sum_ofWithBot, sum_pair
-/
theorem sum_split_boxes {M : Type*} [AddCommMonoid M] (I : Box ι) (i : ι) (x : Real) (f : Box ι -> M) :
    (∑ J in (split I i x).boxes, f J) =
      (I.splitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f := by
  classical
  rw [split]; rw [sum_ofWithBot]; rw [Finset.sum_pair (I.splitLower_ne_splitUpper i x)]

/--
theorem `split_of_notMem_Ioo` / 定理 `split_of_notMem_Ioo`

English:
theorem split_of_notMem_Ioo
  given: (h : x ∉ Ioo (I.lower i) (I.upper i))
  statement: split I i x = ⊤
  proof: by
  refine ((isPartitionTop I).eq_of_boxes_subset fun J hJ => ?_).symm
  rcases mem_top.1 hJ with rfl; clear hJ
  rw [mem_boxes]; rw [mem_split_iff]
  rw [mem_Ioo]; rw [not_and_or]; rw [not_lt]; rw [not_lt] at h
  cases h <;> [right; left]
  · rwa [eq_comm, Box.splitUpper_eq_self]
  · rwa [eq_comm,

中文:
定理 split_of_notMem_Ioo
  条件: (h : x ∉ 开区间 (I.lower i) (I.upper i))
  结论: split I i x = ⊤
  证明: by
  refine ((isPartitionTop I).eq_of_boxes_subset fun J hJ => ?_).symm
  rcases mem_top.1 hJ with rfl; clear hJ
  rw [mem_boxes]; rw [mem_split_iff]
  rw [mem_Ioo]; rw [not_and_or]; rw [not_lt]; rw [not_lt] at h
  cases h <;> [right; left]
  · rwa [eq_comm, Box.splitUpper_eq_self]
  · rwa [eq_comm,

Depends on / 依赖: Box.splitLower_eq_self, Box.splitUpper_eq_self, eq_comm, eq_of_boxes_subset, isPartitionTop, mem_Ioo, mem_boxes, mem_split_iff, mem_top, not_and_or, not_lt, splitLower_eq_self, splitUpper_eq_self
-/
theorem split_of_notMem_Ioo (h : x ∉ Ioo (I.lower i) (I.upper i)) : split I i x = ⊤ := by
  refine ((isPartitionTop I).eq_of_boxes_subset fun J hJ => ?_).symm
  rcases mem_top.1 hJ with rfl; clear hJ
  rw [mem_boxes]; rw [mem_split_iff]
  rw [mem_Ioo]; rw [not_and_or]; rw [not_lt]; rw [not_lt] at h
  cases h <;> [right; left]
  · rwa [eq_comm, Box.splitUpper_eq_self]
  · rwa [eq_comm, Box.splitLower_eq_self]

/--
theorem `coe_eq_of_mem_split_of_mem_le` / 定理 `coe_eq_of_mem_split_of_mem_le`

English:
theorem coe_eq_of_mem_split_of_mem_le
  statement: {y : ι -> Real} (h₁ : J in split I i x) (h₂ : y in J)
  proof: by
  refine (mem_split_iff'.1 h₁).resolve_right fun H => ?_
  rw [← Box.mem_coe]; rw [H] at h₂
  exact h₃.not_gt h₂.2

中文:
定理 coe_eq_of_mem_split_of_mem_le
  结论: {y : ι -> 实数} (h₁ : J in split I i x) (h₂ : y in J)
  证明: by
  refine (mem_split_iff'.1 h₁).resolve_right fun H => ?_
  rw [← Box.mem_coe]; rw [H] at h₂
  exact h₃.not_gt h₂.2

Depends on / 依赖: Box.mem_coe, mem_coe, mem_split_iff, not_gt, resolve_right
-/
theorem coe_eq_of_mem_split_of_mem_le {y : ι -> Real} (h₁ : J in split I i x) (h₂ : y in J)
    (h₃ : y i <= x) : (J : Set (ι -> Real)) = ↑I inter { y | y i <= x } := by
  refine (mem_split_iff'.1 h₁).resolve_right fun H => ?_
  rw [← Box.mem_coe]; rw [H] at h₂
  exact h₃.not_gt h₂.2

/--
theorem `coe_eq_of_mem_split_of_lt_mem` / 定理 `coe_eq_of_mem_split_of_lt_mem`

English:
theorem coe_eq_of_mem_split_of_lt_mem
  statement: {y : ι -> Real} (h₁ : J in split I i x) (h₂ : y in J)
  proof: by
  refine (mem_split_iff'.1 h₁).resolve_left fun H => ?_
  rw [← Box.mem_coe]; rw [H] at h₂
  exact h₃.not_ge h₂.2

@[simp]

中文:
定理 coe_eq_of_mem_split_of_lt_mem
  结论: {y : ι -> 实数} (h₁ : J in split I i x) (h₂ : y in J)
  证明: by
  refine (mem_split_iff'.1 h₁).resolve_left fun H => ?_
  rw [← Box.mem_coe]; rw [H] at h₂
  exact h₃.not_ge h₂.2

@[simp]

Depends on / 依赖: Box.mem_coe, mem_coe, mem_split_iff, not_ge, resolve_left
-/
theorem coe_eq_of_mem_split_of_lt_mem {y : ι -> Real} (h₁ : J in split I i x) (h₂ : y in J)
    (h₃ : x < y i) : (J : Set (ι -> Real)) = ↑I inter { y | x < y i } := by
  refine (mem_split_iff'.1 h₁).resolve_left fun H => ?_
  rw [← Box.mem_coe]; rw [H] at h₂
  exact h₃.not_ge h₂.2

@[simp]
/--
theorem `restrict_split` / 定理 `restrict_split`

English:
theorem restrict_split
  given: (h : I <= J) (i : ι) (x : Real)
  statement: (split J i x).restrict I = split I i x
  proof: by
  refine ((isPartitionSplit J i x).restrict h).eq_of_boxes_subset ?_
  simp only [Finset.subset_iff, mem_boxes, mem_restrict', mem_split_iff']
  have : forall s, (I inter s : Set (ι -> Real)) subseteq J := fun s => inter_subset_left.trans h
  rintro J₁ ⟨J₂, H₂ | H₂, H₁⟩ <;> [left; right] <;>
    

中文:
定理 restrict_split
  条件: (h : I <= J) (i : ι) (x : 实数)
  结论: (split J i x).restrict I = split I i x
  证明: by
  refine ((isPartitionSplit J i x).restrict h).eq_of_boxes_subset ?_
  simp only [Finset.subset_iff, mem_boxes, mem_restrict', mem_split_iff']
  have : forall s, (I inter s : Set (ι -> Real)) subseteq J := fun s => inter_subset_left.trans h
  rintro J₁ ⟨J₂, H₂ | H₂, H₁⟩ <;> [left; right] <;>
    

Depends on / 依赖: Finset, Finset.subset_iff, eq_of_boxes_subset, inter_left_comm, inter_subset_left, inter_subset_left.trans, isPartitionSplit, mem_boxes, mem_restrict, mem_split_iff, restrict, subset_iff, subseteq
-/
theorem restrict_split (h : I <= J) (i : ι) (x : Real) : (split J i x).restrict I = split I i x := by
  refine ((isPartitionSplit J i x).restrict h).eq_of_boxes_subset ?_
  simp only [Finset.subset_iff, mem_boxes, mem_restrict', mem_split_iff']
  have : forall s, (I inter s : Set (ι -> Real)) subseteq J := fun s => inter_subset_left.trans h
  rintro J₁ ⟨J₂, H₂ | H₂, H₁⟩ <;> [left; right] <;>
    simp [H₁, H₂, inter_left_comm (I : Set (ι -> Real)), this]

/--
theorem `inf_split` / 定理 `inf_split`

English:
theorem inf_split
  given: (π : Prepartition I) (i : ι) (x : Real)
  proof: biUnion_congr_of_le rfl fun _ hJ => restrict_split hJ i x

中文:
定理 inf_split
  条件: (π : 预分拆 I) (i : ι) (x : 实数)
  证明: biUnion_congr_of_le rfl fun _ hJ => restrict_split hJ i x

Depends on / 依赖: biUnion_congr_of_le, restrict_split
-/
theorem inf_split (π : Prepartition I) (i : ι) (x : Real) :
    π ⊓ split I i x = π.biUnion fun J => split J i x :=
  biUnion_congr_of_le rfl fun _ hJ => restrict_split hJ i x

/--
Definition of `splitMany` / `splitMany` 的定义

English:
definition splitMany
  signature: (I : Box ι) (s : Finset (ι × Real))
  body: s.inf fun p => split I p.1 p.2

@[simp]

中文:
定义 splitMany
  签名: (I : Box ι) (s : 有限集 (ι × 实数))
  定义体: s.inf fun p => split I p.1 p.2

@[simp]

Depends on / 依赖: s.inf
-/
def splitMany (I : Box ι) (s : Finset (ι × Real)) : Prepartition I :=
  s.inf fun p => split I p.1 p.2

@[simp]
/--
theorem `splitMany_empty` / 定理 `splitMany_empty`

English:
theorem splitMany_empty
  given: (I : Box ι)
  statement: splitMany I ∅ = ⊤
  proof: rfl

中文:
定理 splitMany_empty
  条件: (I : Box ι)
  结论: splitMany I ∅ = ⊤
  证明: rfl
-/
theorem splitMany_empty (I : Box ι) : splitMany I ∅ = ⊤ :=
  rfl

open scoped Classical in
@[simp]
/--
theorem `splitMany_insert` / 定理 `splitMany_insert`

English:
theorem splitMany_insert
  given: (I : Box ι) (s : Finset (ι × Real)) (p : ι × Real)
  proof: by
  rw [splitMany]; rw [Finset.inf_insert]; rw [inf_comm]; rw [splitMany]

中文:
定理 splitMany_insert
  条件: (I : Box ι) (s : 有限集 (ι × 实数)) (p : ι × 实数)
  证明: by
  rw [splitMany]; rw [Finset.inf_insert]; rw [inf_comm]; rw [splitMany]

Depends on / 依赖: Finset, Finset.inf_insert, inf_comm, inf_insert, splitMany
-/
theorem splitMany_insert (I : Box ι) (s : Finset (ι × Real)) (p : ι × Real) :
    splitMany I (insert p s) = splitMany I s ⊓ split I p.1 p.2 := by
  rw [splitMany]; rw [Finset.inf_insert]; rw [inf_comm]; rw [splitMany]

/--
theorem `splitMany_le_split` / 定理 `splitMany_le_split`

English:
theorem splitMany_le_split
  given: (I : Box ι) {s : Finset (ι × Real)} {p : ι × Real} (hp : p in s)
  proof: Finset.inf_le hp

中文:
定理 splitMany_le_split
  条件: (I : Box ι) {s : 有限集 (ι × 实数)} {p : ι × 实数} (hp : p in s)
  证明: Finset.inf_le hp

Depends on / 依赖: Finset, Finset.inf_le, inf_le
-/
theorem splitMany_le_split (I : Box ι) {s : Finset (ι × Real)} {p : ι × Real} (hp : p in s) :
    splitMany I s <= split I p.1 p.2 :=
  Finset.inf_le hp

/--
theorem `isPartition_splitMany` / 定理 `isPartition_splitMany`

English:
theorem isPartition_splitMany
  given: (I : Box ι) (s : Finset (ι × Real))
  statement: IsPartition (splitMany I s)
  proof: by
  classical
  exact Finset.induction_on s (by simp only [splitMany_empty, isPartitionTop]) fun a s _ hs => by
    simpa only [splitMany_insert, inf_split] using hs.biUnion fun J _ => isPartitionSplit _ _ _

@[simp]

中文:
定理 isPartition_splitMany
  条件: (I : Box ι) (s : 有限集 (ι × 实数))
  结论: IsPartition (splitMany I s)
  证明: by
  classical
  exact Finset.induction_on s (by simp only [splitMany_empty, isPartitionTop]) fun a s _ hs => by
    simpa only [splitMany_insert, inf_split] using hs.biUnion fun J _ => isPartitionSplit _ _ _

@[simp]

Depends on / 依赖: Finset, Finset.induction_on, biUnion, classical, hs.biUnion, induction_on, inf_split, isPartitionSplit, isPartitionTop, splitMany_empty, splitMany_insert
-/
theorem isPartition_splitMany (I : Box ι) (s : Finset (ι × Real)) : IsPartition (splitMany I s) := by
  classical
  exact Finset.induction_on s (by simp only [splitMany_empty, isPartitionTop]) fun a s _ hs => by
    simpa only [splitMany_insert, inf_split] using hs.biUnion fun J _ => isPartitionSplit _ _ _

@[simp]
/--
theorem `iUnion_splitMany` / 定理 `iUnion_splitMany`

English:
theorem iUnion_splitMany
  given: (I : Box ι) (s : Finset (ι × Real))
  statement: (splitMany I s).iUnion = I
  proof: (isPartition_splitMany I s).iUnion_eq

中文:
定理 iUnion_splitMany
  条件: (I : Box ι) (s : 有限集 (ι × 实数))
  结论: (splitMany I s).iUnion = I
  证明: (isPartition_splitMany I s).iUnion_eq

Depends on / 依赖: iUnion_eq, isPartition_splitMany
-/
theorem iUnion_splitMany (I : Box ι) (s : Finset (ι × Real)) : (splitMany I s).iUnion = I :=
  (isPartition_splitMany I s).iUnion_eq

/--
theorem `inf_splitMany` / 定理 `inf_splitMany`

English:
theorem inf_splitMany
  given: {I : Box ι} (π : Prepartition I) (s : Finset (ι × Real))
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s _ ihp => simp_rw [splitMany_insert, ← inf_assoc, ihp, inf_split, biUnion_assoc]

中文:
定理 inf_splitMany
  条件: {I : Box ι} (π : 预分拆 I) (s : 有限集 (ι × 实数))
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s _ ihp => simp_rw [splitMany_insert, ← inf_assoc, ihp, inf_split, biUnion_assoc]

Depends on / 依赖: Finset, Finset.induction_on, biUnion_assoc, classical, induction_on, inf_assoc, inf_split, insert, simp_rw, splitMany_insert
-/
theorem inf_splitMany {I : Box ι} (π : Prepartition I) (s : Finset (ι × Real)) :
    π ⊓ splitMany I s = π.biUnion fun J => splitMany J s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s _ ihp => simp_rw [splitMany_insert, ← inf_assoc, ihp, inf_split, biUnion_assoc]

open scoped Classical in
/--
theorem `not_disjoint_imp_le_of_subset_of_mem_splitMany` / 定理 `not_disjoint_imp_le_of_subset_of_mem_splitMany`

English:
theorem not_disjoint_imp_le_of_subset_of_mem_splitMany
  statement: {I J Js : Box ι} {s : Finset (ι × Real)}
  proof: by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at H
  rcases Box.not_disjoint_coe_iff_nonempty_inter.mp Hn with ⟨x, hx, hxs⟩
  refine fun y hy i => ⟨?_, ?_⟩
  · rcases splitMany_le_split I (H i).1 HJs with ⟨Jl, Hmem : Jl in split I i (J.lower i), Hle⟩
    have := Hle hxs
    

中文:
定理 not_disjoint_imp_le_of_subset_of_mem_splitMany
  结论: {I J Js : Box ι} {s : 有限集 (ι × 实数)}
  证明: by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at H
  rcases Box.not_disjoint_coe_iff_nonempty_inter.mp Hn with ⟨x, hx, hxs⟩
  refine fun y hy i => ⟨?_, ?_⟩
  · rcases splitMany_le_split I (H i).1 HJs with ⟨Jl, Hmem : Jl in split I i (J.lower i), Hle⟩
    have := Hle hxs
    

Depends on / 依赖: Box.coe_subset_coe, Box.not_disjoint_coe_iff_nonempty_inter.mp, Finset, Finset.insert_subset_iff, Finset.singleton_subset_iff, J.lower, J.upper, coe_eq_of_mem_split_of_lt_mem, coe_subset_coe, insert_subset_iff, not_disjoint_coe_iff_nonempty_inter, singleton_subset_iff, splitMany_le_split
-/
theorem not_disjoint_imp_le_of_subset_of_mem_splitMany {I J Js : Box ι} {s : Finset (ι × Real)}
    (H : forall i, {(i, J.lower i), (i, J.upper i)} subseteq s) (HJs : Js in splitMany I s)
    (Hn : ¬Disjoint (J : WithBot (Box ι)) Js) : Js <= J := by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at H
  rcases Box.not_disjoint_coe_iff_nonempty_inter.mp Hn with ⟨x, hx, hxs⟩
  refine fun y hy i => ⟨?_, ?_⟩
  · rcases splitMany_le_split I (H i).1 HJs with ⟨Jl, Hmem : Jl in split I i (J.lower i), Hle⟩
    have := Hle hxs
    rw [← Box.coe_subset_coe]; rw [coe_eq_of_mem_split_of_lt_mem Hmem this (hx i).1] at Hle
    exact (Hle hy).2
  · rcases splitMany_le_split I (H i).2 HJs with ⟨Jl, Hmem : Jl in split I i (J.upper i), Hle⟩
    have := Hle hxs
    rw [← Box.coe_subset_coe]; rw [coe_eq_of_mem_split_of_mem_le Hmem this (hx i).2] at Hle
    exact (Hle hy).2

section Finite

variable [Finite ι]

/--
theorem `eventually_not_disjoint_imp_le_of_mem_splitMany` / 定理 `eventually_not_disjoint_imp_le_of_mem_splitMany`

English:
theorem eventually_not_disjoint_imp_le_of_mem_splitMany
  given: (s : Finset (Box ι))
  proof: by
  classical
  cases nonempty_fintype ι
  refine eventually_atTop.2
    ⟨s.biUnion fun J => Finset.univ.biUnion fun i => {(i, J.lower i), (i, J.upper i)},
      fun t ht I J hJ J' hJ' => not_disjoint_imp_le_of_subset_of_mem_splitMany (fun i => ?_) hJ'⟩
  exact fun p hp =>
    ht (Finset.mem_biUnio

中文:
定理 eventually_not_disjoint_imp_le_of_mem_splitMany
  条件: (s : 有限集 (Box ι))
  证明: by
  classical
  cases nonempty_fintype ι
  refine eventually_atTop.2
    ⟨s.biUnion fun J => Finset.univ.biUnion fun i => {(i, J.lower i), (i, J.upper i)},
      fun t ht I J hJ J' hJ' => not_disjoint_imp_le_of_subset_of_mem_splitMany (fun i => ?_) hJ'⟩
  exact fun p hp =>
    ht (Finset.mem_biUnio

Depends on / 依赖: Finset, Finset.mem_biUnion, Finset.mem_univ, Finset.univ.biUnion, J.lower, J.upper, biUnion, classical, eventually_atTop, mem_biUnion, mem_univ, nonempty_fintype, not_disjoint_imp_le_of_subset_of_mem_splitMany, s.biUnion
-/
theorem eventually_not_disjoint_imp_le_of_mem_splitMany (s : Finset (Box ι)) :
    forallᶠ t : Finset (ι × Real) in atTop, forall (I : Box ι), forall J in s, forall J' in splitMany I t,
      ¬Disjoint (J : WithBot (Box ι)) J' -> J' <= J := by
  classical
  cases nonempty_fintype ι
  refine eventually_atTop.2
    ⟨s.biUnion fun J => Finset.univ.biUnion fun i => {(i, J.lower i), (i, J.upper i)},
      fun t ht I J hJ J' hJ' => not_disjoint_imp_le_of_subset_of_mem_splitMany (fun i => ?_) hJ'⟩
  exact fun p hp =>
    ht (Finset.mem_biUnion.2 ⟨J, hJ, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hp⟩⟩)

/--
theorem `eventually_splitMany_inf_eq_filter` / 定理 `eventually_splitMany_inf_eq_filter`

English:
theorem eventually_splitMany_inf_eq_filter
  given: (π : Prepartition I)
  proof: by
  refine (eventually_not_disjoint_imp_le_of_mem_splitMany π.boxes).mono fun t ht => ?_
  refine le_antisymm ((biUnion_le_iff _).2 fun J hJ => ?_) (le_inf (fun J hJ => ?_) (filter_le _ _))
  · refine ofWithBot_mono ?_
    simp only [Finset.mem_image, mem_boxes, mem_filter]
    rintro _ ⟨J₁, h₁, rf

中文:
定理 eventually_splitMany_inf_eq_filter
  条件: (π : 预分拆 I)
  证明: by
  refine (eventually_not_disjoint_imp_le_of_mem_splitMany π.boxes).mono fun t ht => ?_
  refine le_antisymm ((biUnion_le_iff _).2 fun J hJ => ?_) (le_inf (fun J hJ => ?_) (filter_le _ _))
  · refine ofWithBot_mono ?_
    simp only [Finset.mem_image, mem_boxes, mem_filter]
    rintro _ ⟨J₁, h₁, rf

Depends on / 依赖: Finset, Finset.mem_image, J.upper_mem, Set.mem_iUnion, Subset, Subset.trans, biUnion_le_iff, disjoint_iff, eventually_not_disjoint_imp_le_of_mem_splitMany, filter_le, le_antisymm, le_inf, le_rfl, mem_boxes, mem_filter, mem_image, ofWithBot_mono, subset_iUnion, upper_mem
-/
theorem eventually_splitMany_inf_eq_filter (π : Prepartition I) :
    forallᶠ t : Finset (ι × Real) in atTop,
      π ⊓ splitMany I t = (splitMany I t).filter fun J => ↑J subseteq π.iUnion := by
  refine (eventually_not_disjoint_imp_le_of_mem_splitMany π.boxes).mono fun t ht => ?_
  refine le_antisymm ((biUnion_le_iff _).2 fun J hJ => ?_) (le_inf (fun J hJ => ?_) (filter_le _ _))
  · refine ofWithBot_mono ?_
    simp only [Finset.mem_image, mem_boxes, mem_filter]
    rintro _ ⟨J₁, h₁, rfl⟩ hne
    refine ⟨_, ⟨J₁, ⟨h₁, Subset.trans ?_ (π.subset_iUnion hJ)⟩, rfl⟩, le_rfl⟩
    exact ht I J hJ J₁ h₁ (mt disjoint_iff.1 hne)
  · rw [mem_filter] at hJ
    rcases Set.mem_iUnion₂.1 (hJ.2 J.upper_mem) with ⟨J', hJ', hmem⟩
refine ⟨J', hJ', ht I _ hJ' _ hJ.1 Box.not_disjoint_coe_iff_nonempty_inter.2 ?_⟩
    exact ⟨J.upper, hmem, J.upper_mem⟩

/--
theorem `exists_splitMany_inf_eq_filter_of_finite` / 定理 `exists_splitMany_inf_eq_filter_of_finite`

English:
theorem exists_splitMany_inf_eq_filter_of_finite
  given: (s : Set (Prepartition I)) (hs : s.Finite)
  proof: haveI := fun π (_ : π in s) => eventually_splitMany_inf_eq_filter π
  (hs.eventually_all.2 this).exists

中文:
定理 存在_splitMany_inf_eq_filter_of_finite
  条件: (s : 集合 (预分拆 I)) (hs : s.有限)
  证明: haveI := fun π (_ : π in s) => eventually_splitMany_inf_eq_filter π
  (hs.eventually_all.2 this).exists

Depends on / 依赖: eventually_all, eventually_splitMany_inf_eq_filter, hs.eventually_all
-/
theorem exists_splitMany_inf_eq_filter_of_finite (s : Set (Prepartition I)) (hs : s.Finite) :
    exists t : Finset (ι × Real),
      forall π in s, π ⊓ splitMany I t = (splitMany I t).filter fun J => ↑J subseteq π.iUnion :=
  haveI := fun π (_ : π in s) => eventually_splitMany_inf_eq_filter π
  (hs.eventually_all.2 this).exists

/--
theorem `IsPartition.exists_splitMany_le` / 定理 `IsPartition.exists_splitMany_le`

English:
theorem IsPartition.exists_splitMany_le
  given: {I : Box ι} {π : Prepartition I} (h : IsPartition π)
  proof: by
  refine (eventually_splitMany_inf_eq_filter π).exists.imp fun s hs => ?_
  rwa [h.iUnion_eq, filter_of_true, inf_eq_right] at hs
  exact fun J hJ => le_of_mem _ hJ

中文:
定理 IsPartition.存在_splitMany_le
  条件: {I : Box ι} {π : 预分拆 I} (h : IsPartition π)
  证明: by
  refine (eventually_splitMany_inf_eq_filter π).exists.imp fun s hs => ?_
  rwa [h.iUnion_eq, filter_of_true, inf_eq_right] at hs
  exact fun J hJ => le_of_mem _ hJ

Depends on / 依赖: eventually_splitMany_inf_eq_filter, exists.imp, filter_of_true, h.iUnion_eq, iUnion_eq, inf_eq_right, le_of_mem
-/
theorem IsPartition.exists_splitMany_le {I : Box ι} {π : Prepartition I} (h : IsPartition π) :
    exists s, splitMany I s <= π := by
  refine (eventually_splitMany_inf_eq_filter π).exists.imp fun s hs => ?_
  rwa [h.iUnion_eq, filter_of_true, inf_eq_right] at hs
  exact fun J hJ => le_of_mem _ hJ

/--
theorem `exists_iUnion_eq_sdiff` / 定理 `exists_iUnion_eq_sdiff`

English:
theorem exists_iUnion_eq_sdiff
  given: (π : Prepartition I)
  proof: by
  rcases π.eventually_splitMany_inf_eq_filter.exists with ⟨s, hs⟩
  use (splitMany I s).filter fun J => ¬(J : Set (ι -> Real)) subseteq π.iUnion
  simp [← hs]

@[deprecated (since := "2026-06-03")] alias exists_iUnion_eq_diff := exists_iUnion_eq_sdiff

中文:
定理 存在_iUnion_eq_sdiff
  条件: (π : 预分拆 I)
  证明: by
  rcases π.eventually_splitMany_inf_eq_filter.exists with ⟨s, hs⟩
  use (splitMany I s).filter fun J => ¬(J : Set (ι -> Real)) subseteq π.iUnion
  simp [← hs]

@[deprecated (since := "2026-06-03")] alias exists_iUnion_eq_diff := exists_iUnion_eq_sdiff

Depends on / 依赖: eventually_splitMany_inf_eq_filter, eventually_splitMany_inf_eq_filter.exists, filter, iUnion, splitMany, subseteq
-/
theorem exists_iUnion_eq_sdiff (π : Prepartition I) :
    exists π' : Prepartition I, π'.iUnion = ↑I \ π.iUnion := by
  rcases π.eventually_splitMany_inf_eq_filter.exists with ⟨s, hs⟩
  use (splitMany I s).filter fun J => ¬(J : Set (ι -> Real)) subseteq π.iUnion
  simp [← hs]

@[deprecated (since := "2026-06-03")] alias exists_iUnion_eq_diff := exists_iUnion_eq_sdiff

/--
Definition of `compl` / `compl` 的定义

English:
definition compl
  signature: (π : Prepartition I)
  body: π.exists_iUnion_eq_sdiff.choose

@[simp]

中文:
定义 compl
  签名: (π : 预分拆 I)
  定义体: π.exists_iUnion_eq_sdiff.choose

@[simp]

Depends on / 依赖: exists_iUnion_eq_sdiff, exists_iUnion_eq_sdiff.choose
-/
def compl (π : Prepartition I) : Prepartition I :=
  π.exists_iUnion_eq_sdiff.choose

@[simp]
/--
theorem `iUnion_compl` / 定理 `iUnion_compl`

English:
theorem iUnion_compl
  given: (π : Prepartition I)
  statement: π.compl.iUnion = ↑I \ π.iUnion
  proof: π.exists_iUnion_eq_sdiff.choose_spec

中文:
定理 iUnion_compl
  条件: (π : 预分拆 I)
  结论: π.compl.iUnion = ↑I \ π.iUnion
  证明: π.exists_iUnion_eq_sdiff.choose_spec

Depends on / 依赖: choose_spec, exists_iUnion_eq_sdiff, exists_iUnion_eq_sdiff.choose_spec
-/
theorem iUnion_compl (π : Prepartition I) : π.compl.iUnion = ↑I \ π.iUnion :=
  π.exists_iUnion_eq_sdiff.choose_spec

/--
theorem `compl_congr` / 定理 `compl_congr`

English:
theorem compl_congr
  given: {π₁ π₂ : Prepartition I} (h : π₁.iUnion = π₂.iUnion)
  statement: π₁.compl = π₂.compl
  proof: by
  dsimp only [compl]
  congr 1
  rw [h]

中文:
定理 compl_congr
  条件: {π₁ π₂ : 预分拆 I} (h : π₁.iUnion = π₂.iUnion)
  结论: π₁.compl = π₂.compl
  证明: by
  dsimp only [compl]
  congr 1
  rw [h]
-/
theorem compl_congr {π₁ π₂ : Prepartition I} (h : π₁.iUnion = π₂.iUnion) : π₁.compl = π₂.compl := by
  dsimp only [compl]
  congr 1
  rw [h]

/--
theorem `IsPartition.compl_eq_bot` / 定理 `IsPartition.compl_eq_bot`

English:
theorem IsPartition.compl_eq_bot
  given: {π : Prepartition I} (h : IsPartition π)
  statement: π.compl = ⊥
  proof: by
  rw [← iUnion_eq_empty]; rw [iUnion_compl]; rw [h.iUnion_eq]; rw [sdiff_self]

@[simp]

中文:
定理 IsPartition.compl_eq_bot
  条件: {π : 预分拆 I} (h : IsPartition π)
  结论: π.compl = ⊥
  证明: by
  rw [← iUnion_eq_empty]; rw [iUnion_compl]; rw [h.iUnion_eq]; rw [sdiff_self]

@[simp]

Depends on / 依赖: h.iUnion_eq, iUnion_compl, iUnion_eq, iUnion_eq_empty, sdiff_self
-/
theorem IsPartition.compl_eq_bot {π : Prepartition I} (h : IsPartition π) : π.compl = ⊥ := by
  rw [← iUnion_eq_empty]; rw [iUnion_compl]; rw [h.iUnion_eq]; rw [sdiff_self]

@[simp]
/--
theorem `compl_top` / 定理 `compl_top`

English:
theorem compl_top
  statement: (⊤ : Prepartition I).compl = ⊥
  proof: (isPartitionTop I).compl_eq_bot

中文:
定理 compl_top
  结论: (⊤ : 预分拆 I).compl = ⊥
  证明: (isPartitionTop I).compl_eq_bot

Depends on / 依赖: compl_eq_bot, isPartitionTop
-/
theorem compl_top : (⊤ : Prepartition I).compl = ⊥ :=
  (isPartitionTop I).compl_eq_bot

end Finite

end Prepartition

end BoxIntegral
