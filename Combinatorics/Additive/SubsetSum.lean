/-
Copyright (c) 2025 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Finset.Powerset

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max

/-!
# Subset sums

This file defines the subset sum of a finite subset of a commutative monoid.

## References

* [Melvyn B. Nathanson, *Inverse theorems for subset sums*][Nathanson1995]
-/

public section

open scoped Pointwise

namespace Finset
variable {M : Type*} [DecidableEq M] [AddCommMonoid M] {A : Finset M} {a : M}

/--
Definition of `subsetSum` / `subsetSum` 的定义

English:
definition subsetSum
  signature: (A : Finset M)
  body: A.powerset.image fun B => B.sum id

中文:
定义 subsetSum
  签名: (A : 有限集 M)
  定义体: A.powerset.image fun B => B.sum id

Depends on / 依赖: A.powerset.image, B.sum, powerset
-/
def subsetSum (A : Finset M) : Finset M := A.powerset.image fun B => B.sum id

/--
lemma `mem_subsetSum_iff` / 引理 `mem_subsetSum_iff`

English:
lemma mem_subsetSum_iff
  statement: a in A.subsetSum ↔ exists B subseteq A, ∑ b in B, b = a
  proof: by simp [subsetSum]

@[simp]

中文:
引理 mem_subsetSum_iff
  结论: a in A.subsetSum ↔ 存在 B subseteq A, ∑ b in B, b = a
  证明: by simp [subsetSum]

@[simp]

Depends on / 依赖: subsetSum
-/
lemma mem_subsetSum_iff : a in A.subsetSum ↔ exists B subseteq A, ∑ b in B, b = a := by simp [subsetSum]

@[simp]
/--
lemma `zero_mem_subsetSum` / 引理 `zero_mem_subsetSum`

English:
lemma zero_mem_subsetSum
  statement: 0 in A.subsetSum
  proof: mem_subsetSum_iff.mpr ⟨∅, empty_subset _, sum_empty⟩

中文:
引理 zero_mem_subsetSum
  结论: 0 in A.subsetSum
  证明: mem_subsetSum_iff.mpr ⟨∅, empty_subset _, sum_empty⟩

Depends on / 依赖: empty_subset, mem_subsetSum_iff, mem_subsetSum_iff.mpr, sum_empty
-/
lemma zero_mem_subsetSum : 0 in A.subsetSum := mem_subsetSum_iff.mpr ⟨∅, empty_subset _, sum_empty⟩

/--
lemma `subsetSum_nonempty` / 引理 `subsetSum_nonempty`

English:
lemma subsetSum_nonempty
  statement: A.subsetSum.Nonempty
  proof: ⟨0, by simp⟩

中文:
引理 subsetSum_nonempty
  结论: A.subsetSum.非空
  证明: ⟨0, by simp⟩
-/
@[simp] lemma subsetSum_nonempty : A.subsetSum.Nonempty := ⟨0, by simp⟩

/--
lemma `subset_subsetSum` / 引理 `subset_subsetSum`

English:
lemma subset_subsetSum
  statement: A subseteq A.subsetSum
  proof: fun a ha => mem_subsetSum_iff.mpr ⟨{a}, by simp [ha]⟩

@[gcongr]

中文:
引理 subset_subsetSum
  结论: A subseteq A.subsetSum
  证明: fun a ha => mem_subsetSum_iff.mpr ⟨{a}, by simp [ha]⟩

@[gcongr]

Depends on / 依赖: mem_subsetSum_iff, mem_subsetSum_iff.mpr
-/
lemma subset_subsetSum : A subseteq A.subsetSum :=
  fun a ha => mem_subsetSum_iff.mpr ⟨{a}, by simp [ha]⟩

@[gcongr]
/--
lemma `subsetSum_mono` / 引理 `subsetSum_mono`

English:
lemma subsetSum_mono
  given: {B : Finset M} (hAB : A subseteq B)
  statement: A.subsetSum subseteq B.subsetSum
  proof: image_mono _ powerset_mono.mpr hAB

中文:
引理 subsetSum_mono
  条件: {B : 有限集 M} (hAB : A subseteq B)
  结论: A.subsetSum subseteq B.subsetSum
  证明: image_mono _ powerset_mono.mpr hAB

Depends on / 依赖: image_mono, powerset_mono, powerset_mono.mpr
-/
lemma subsetSum_mono {B : Finset M} (hAB : A subseteq B) : A.subsetSum subseteq B.subsetSum :=
image_mono _ powerset_mono.mpr hAB

/--
lemma `subsetSum_erase_zero` / 引理 `subsetSum_erase_zero`

English:
lemma subsetSum_erase_zero
  statement: (A.erase 0).subsetSum = A.subsetSum
  proof: by
  refine le_antisymm (subsetSum_mono (erase_subset _ _)) fun x hx => ?_
  obtain ⟨B, hB, rfl⟩ := mem_subsetSum_iff.mp hx
  refine mem_subsetSum_iff.mpr ⟨B.erase 0, ?_, sum_erase _ (by simp)⟩
  exact fun i hi => mem_erase.mpr ⟨(mem_erase.mp hi).1, hB (mem_of_mem_erase hi)⟩

中文:
引理 subsetSum_erase_zero
  结论: (A.erase 0).subsetSum = A.subsetSum
  证明: by
  refine le_antisymm (subsetSum_mono (erase_subset _ _)) fun x hx => ?_
  obtain ⟨B, hB, rfl⟩ := mem_subsetSum_iff.mp hx
  refine mem_subsetSum_iff.mpr ⟨B.erase 0, ?_, sum_erase _ (by simp)⟩
  exact fun i hi => mem_erase.mpr ⟨(mem_erase.mp hi).1, hB (mem_of_mem_erase hi)⟩
-/
@[simp] lemma subsetSum_erase_zero : (A.erase 0).subsetSum = A.subsetSum := by
  refine le_antisymm (subsetSum_mono (erase_subset _ _)) fun x hx => ?_
  obtain ⟨B, hB, rfl⟩ := mem_subsetSum_iff.mp hx
  refine mem_subsetSum_iff.mpr ⟨B.erase 0, ?_, sum_erase _ (by simp)⟩
  exact fun i hi => mem_erase.mpr ⟨(mem_erase.mp hi).1, hB (mem_of_mem_erase hi)⟩

/--
lemma `vadd_finset_subsetSum_subset_subsetSum_insert` / 引理 `vadd_finset_subsetSum_subset_subsetSum_insert`

English:
lemma vadd_finset_subsetSum_subset_subsetSum_insert
  given: (a_notin_A : a ∉ A)
  proof: by
  simp_rw [subset_iff, mem_vadd_finset, mem_subsetSum_iff]
  rintro _ ⟨_, ⟨B, hB, rfl⟩, rfl⟩
  exact ⟨insert a B, by aesop, by rw [sum_insert (fun h => a_notin_A (hB h))]; simp⟩

中文:
引理 vadd_finset_subsetSum_subset_subsetSum_insert
  条件: (a_notin_A : a ∉ A)
  证明: by
  simp_rw [subset_iff, mem_vadd_finset, mem_subsetSum_iff]
  rintro _ ⟨_, ⟨B, hB, rfl⟩, rfl⟩
  exact ⟨insert a B, by aesop, by rw [sum_insert (fun h => a_notin_A (hB h))]; simp⟩

Depends on / 依赖: a_notin_A, insert, mem_subsetSum_iff, mem_vadd_finset, simp_rw, subset_iff, sum_insert
-/
lemma vadd_finset_subsetSum_subset_subsetSum_insert (a_notin_A : a ∉ A) :
    a +ᵥ A.subsetSum subseteq (insert a A).subsetSum := by
  simp_rw [subset_iff, mem_vadd_finset, mem_subsetSum_iff]
  rintro _ ⟨_, ⟨B, hB, rfl⟩, rfl⟩
  exact ⟨insert a B, by aesop, by rw [sum_insert (fun h => a_notin_A (hB h))]; simp⟩

variable [LinearOrder M] [IsOrderedCancelAddMonoid M]

/--
lemma `nonneg_of_mem_subsetSum` / 引理 `nonneg_of_mem_subsetSum`

English:
lemma nonneg_of_mem_subsetSum
  given: (A_nonneg : forall x in A, 0 <= x)
  statement: forall x in A.subsetSum, 0 <= x
  proof: by
simpa [mem_subsetSum_iff] using fun B hB => Finset.sum_nonneg fun x hx => A_nonneg _ hB hx

中文:
引理 nonneg_of_mem_subsetSum
  条件: (A_nonneg : 对任意 x in A, 0 <= x)
  结论: 对任意 x in A.subsetSum, 0 <= x
  证明: by
simpa [mem_subsetSum_iff] using fun B hB => Finset.sum_nonneg fun x hx => A_nonneg _ hB hx

Depends on / 依赖: A_nonneg, Finset, Finset.sum_nonneg, mem_subsetSum_iff, sum_nonneg
-/
lemma nonneg_of_mem_subsetSum (A_nonneg : forall x in A, 0 <= x) : forall x in A.subsetSum, 0 <= x := by
simpa [mem_subsetSum_iff] using fun B hB => Finset.sum_nonneg fun x hx => A_nonneg _ hB hx

/--
lemma `card_add_card_subsetSum_lt_card_subsetSum_insert_max` / 引理 `card_add_card_subsetSum_lt_card_subsetSum_insert_max`

English:
lemma card_add_card_subsetSum_lt_card_subsetSum_insert_max
  statement: (hA : forall x in A, 0 < x)
  proof: by
  -- We show that `insert 0 A` and `a +ᵥ A.subsetSum` are disjoint subsets of
  -- `(insert a A).subsetSum`, and their combined cardinality gives the result.
  -- The sets are disjoint.
  have disjoint : Disjoint (insert 0 A) (a +ᵥ A.subsetSum) := by
    have := nonneg_of_mem_subsetSum (fun y hy => (hA y hy).le)
    simpa [disjoint_left, mem_insert, mem_vadd_finset] using
      ⟨fun x hx => (add_pos_of_pos_of_nonneg ha <| this _ hx).ne',
        fun x hx y hy => (lt_add_of_lt_of_nonneg (hAa x hx) <| this _ hy).ne'⟩
  -- Both sets are subsets of `(insert a A).subsetSum`.
  have insert_subset : insert 0 A subseteq (insert a A).subsetSum := by
    grw [insert_subset_iff, ← subset_insert]; exact ⟨zero_mem_subsetSum, subset_subsetSum⟩
  have vadd_subset : a +ᵥ A.subsetSum subseteq (insert a A).subsetSum :=
    vadd_finset_subsetSum_subset_subsetSum_insert fun ha => (hAa a ha).false
  -- Count the sizes.
  calc #A + #A.subsetSum
    _ < #A + 1 + #A.subsetSum := by gcongr; exact Nat.lt_add_one _
    _ = #(insert 0 A) + #A.subsetSum := by rw [card_insert_of_notMem fun h => (hA 0 h).false]
    _ = #(insert 0 A) + #(a +ᵥ A.subsetSum) := by simp [vadd_finset_def, card_image_of_injOn]
    _ = #((insert 0 A) union (a +ᵥ A.subsetSum)) := by rw [card_union_of_disjoint disjoint]
    _ <= #(insert a A).subsetSum := by grw [union_subset insert_subset vadd_subset]

中文:
引理 card_add_card_subsetSum_lt_card_subsetSum_insert_max
  结论: (hA : 对任意 x in A, 0 < x)
  证明: by
  -- We show that `insert 0 A` and `a +ᵥ A.subsetSum` are disjoint subsets of
  -- `(insert a A).subsetSum`, and their combined cardinality gives the result.
  -- The sets are disjoint.
  have disjoint : Disjoint (insert 0 A) (a +ᵥ A.subsetSum) := by
    have := nonneg_of_mem_subsetSum (fun y hy => (hA y hy).le)
    simpa [disjoint_left, mem_insert, mem_vadd_finset] using
      ⟨fun x hx => (add_pos_of_pos_of_nonneg ha <| this _ hx).ne',
        fun x hx y hy => (lt_add_of_lt_of_nonneg (hAa x hx) <| this _ hy).ne'⟩
  -- Both sets are subsets of `(insert a A).subsetSum`.
  have insert_subset : insert 0 A subseteq (insert a A).subsetSum := by
    grw [insert_subset_iff, ← subset_insert]; exact ⟨zero_mem_subsetSum, subset_subsetSum⟩
  have vadd_subset : a +ᵥ A.subsetSum subseteq (insert a A).subsetSum :=
    vadd_finset_subsetSum_subset_subsetSum_insert fun ha => (hAa a ha).false
  -- Count the sizes.
  calc #A + #A.subsetSum
    _ < #A + 1 + #A.subsetSum := by gcongr; exact Nat.lt_add_one _
    _ = #(insert 0 A) + #A.subsetSum := by rw [card_insert_of_notMem fun h => (hA 0 h).false]
    _ = #(insert 0 A) + #(a +ᵥ A.subsetSum) := by simp [vadd_finset_def, card_image_of_injOn]
    _ = #((insert 0 A) union (a +ᵥ A.subsetSum)) := by rw [card_union_of_disjoint disjoint]
    _ <= #(insert a A).subsetSum := by grw [union_subset insert_subset vadd_subset]
-/
lemma card_add_card_subsetSum_lt_card_subsetSum_insert_max (hA : forall x in A, 0 < x)
    (hAa : forall x in A, x < a) (ha : 0 < a) :
    #A + #A.subsetSum < #(insert a A).subsetSum := by
  -- We show that `insert 0 A` and `a +ᵥ A.subsetSum` are disjoint subsets of
  -- `(insert a A).subsetSum`, and their combined cardinality gives the result.
  -- The sets are disjoint.
  have disjoint : Disjoint (insert 0 A) (a +ᵥ A.subsetSum) := by
    have := nonneg_of_mem_subsetSum (fun y hy => (hA y hy).le)
    simpa [disjoint_left, mem_insert, mem_vadd_finset] using
      ⟨fun x hx => (add_pos_of_pos_of_nonneg ha <| this _ hx).ne',
        fun x hx y hy => (lt_add_of_lt_of_nonneg (hAa x hx) <| this _ hy).ne'⟩
  -- Both sets are subsets of `(insert a A).subsetSum`.
  have insert_subset : insert 0 A subseteq (insert a A).subsetSum := by
    grw [insert_subset_iff, ← subset_insert]; exact ⟨zero_mem_subsetSum, subset_subsetSum⟩
  have vadd_subset : a +ᵥ A.subsetSum subseteq (insert a A).subsetSum :=
    vadd_finset_subsetSum_subset_subsetSum_insert fun ha => (hAa a ha).false
  -- Count the sizes.
  calc #A + #A.subsetSum
    _ < #A + 1 + #A.subsetSum := by gcongr; exact Nat.lt_add_one _
    _ = #(insert 0 A) + #A.subsetSum := by rw [card_insert_of_notMem fun h => (hA 0 h).false]
    _ = #(insert 0 A) + #(a +ᵥ A.subsetSum) := by simp [vadd_finset_def, card_image_of_injOn]
    _ = #((insert 0 A) union (a +ᵥ A.subsetSum)) := by rw [card_union_of_disjoint disjoint]
    _ <= #(insert a A).subsetSum := by grw [union_subset insert_subset vadd_subset]

-- The proof follows Theorem 3 in [Nathanson1995].
/--
theorem `card_succ_choose_two_lt_card_subsetSum_of_pos` / 定理 `card_succ_choose_two_lt_card_subsetSum_of_pos`

English:
theorem card_succ_choose_two_lt_card_subsetSum_of_pos
  given: (A_pos : forall x in A, 0 < x)
  proof: by
  induction A using induction_on_max with
  | empty => simp
  | insert a A A_lt_a ih =>
    have A_pos' : forall x in A, 0 < x := fun x hx => A_pos x (mem_insert_of_mem hx)
    grw [card_insert_of_notMem fun ha => (A_lt_a a ha).false, Nat.choose_succ_left _ _ (by lia),
      Nat.choose_one_right, add_right_comm, add_assoc, Nat.add_one_le_iff.2 (ih A_pos')]
exact card_add_card_subsetSum_lt_card_subsetSum_insert_max A_pos' A_lt_a A_pos a
      mem_insert_self a A

中文:
定理 card_succ_choose_two_lt_card_subsetSum_of_pos
  条件: (A_pos : 对任意 x in A, 0 < x)
  证明: by
  induction A using induction_on_max with
  | empty => simp
  | insert a A A_lt_a ih =>
    have A_pos' : forall x in A, 0 < x := fun x hx => A_pos x (mem_insert_of_mem hx)
    grw [card_insert_of_notMem fun ha => (A_lt_a a ha).false, Nat.choose_succ_left _ _ (by lia),
      Nat.choose_one_right, add_right_comm, add_assoc, Nat.add_one_le_iff.2 (ih A_pos')]
exact card_add_card_subsetSum_lt_card_subsetSum_insert_max A_pos' A_lt_a A_pos a
      mem_insert_self a A

Depends on / 依赖: A_lt_a, A_pos, Nat.add_one_le_iff, Nat.choose_one_right, Nat.choose_succ_left, add_assoc, add_one_le_iff, add_right_comm, card_add_card_subsetSum_lt_card_subsetSum_insert_max, card_insert_of_notMem, choose_one_right, choose_succ_left, induction_on_max, insert, mem_insert_of_mem, mem_insert_self
-/
theorem card_succ_choose_two_lt_card_subsetSum_of_pos (A_pos : forall x in A, 0 < x) :
    (#A + 1).choose 2 < #A.subsetSum := by
  induction A using induction_on_max with
  | empty => simp
  | insert a A A_lt_a ih =>
    have A_pos' : forall x in A, 0 < x := fun x hx => A_pos x (mem_insert_of_mem hx)
    grw [card_insert_of_notMem fun ha => (A_lt_a a ha).false, Nat.choose_succ_left _ _ (by lia),
      Nat.choose_one_right, add_right_comm, add_assoc, Nat.add_one_le_iff.2 (ih A_pos')]
exact card_add_card_subsetSum_lt_card_subsetSum_insert_max A_pos' A_lt_a A_pos a
      mem_insert_self a A

/--
theorem `card_choose_two_lt_card_subsetSum_of_nonneg` / 定理 `card_choose_two_lt_card_subsetSum_of_nonneg`

English:
theorem card_choose_two_lt_card_subsetSum_of_nonneg
  given: (A_pos : forall x in A, 0 <= x)
  proof: by
  calc (#A).choose 2
    _ <= (#(A.erase 0) + 1).choose 2 := by grw [tsub_le_iff_right.1 <| pred_card_le_card_erase]
    _ < #(A.erase 0).subsetSum :=
        card_succ_choose_two_lt_card_subsetSum_of_pos fun x hx =>
          (A_pos x (mem_of_mem_erase hx)).lt_of_ne (ne_of_mem_erase hx).symm
    _ = #A.subsetSum := by rw [subsetSum_erase_zero]

中文:
定理 card_choose_two_lt_card_subsetSum_of_nonneg
  条件: (A_pos : 对任意 x in A, 0 <= x)
  证明: by
  calc (#A).choose 2
    _ <= (#(A.erase 0) + 1).choose 2 := by grw [tsub_le_iff_right.1 <| pred_card_le_card_erase]
    _ < #(A.erase 0).subsetSum :=
        card_succ_choose_two_lt_card_subsetSum_of_pos fun x hx =>
          (A_pos x (mem_of_mem_erase hx)).lt_of_ne (ne_of_mem_erase hx).symm
    _ = #A.subsetSum := by rw [subsetSum_erase_zero]

Depends on / 依赖: A.erase, A.subsetSum, A_pos, card_succ_choose_two_lt_card_subsetSum_of_pos, lt_of_ne, mem_of_mem_erase, ne_of_mem_erase, pred_card_le_card_erase, subsetSum, subsetSum_erase_zero, tsub_le_iff_right
-/
theorem card_choose_two_lt_card_subsetSum_of_nonneg (A_pos : forall x in A, 0 <= x) :
    (#A).choose 2 < #A.subsetSum := by
  calc (#A).choose 2
    _ <= (#(A.erase 0) + 1).choose 2 := by grw [tsub_le_iff_right.1 <| pred_card_le_card_erase]
    _ < #(A.erase 0).subsetSum :=
        card_succ_choose_two_lt_card_subsetSum_of_pos fun x hx =>
          (A_pos x (mem_of_mem_erase hx)).lt_of_ne (ne_of_mem_erase hx).symm
    _ = #A.subsetSum := by rw [subsetSum_erase_zero]

end Finset
