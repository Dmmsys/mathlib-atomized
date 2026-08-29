/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Results about big operators over intervals

We prove results about big operators over intervals.
-/

public section

open Nat Finset

variable {α G M : Type*}

namespace Finset

section Generic
variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α -> M}

@[to_additive]
/--
theorem `prod_Ico_add'` / 定理 `prod_Ico_add'`

English:
theorem prod_Ico_add'
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  proof: by
  rw [← map_add_right_Ico]; rw [prod_map]
  rfl

@[to_additive]

中文:
定理 prod_Ico_add'
  结论: [加法交换幺半群 α] [偏序 α] [是OrderedCancelAdd幺半群 α]
  证明: by
  rw [← map_add_right_Ico]; rw [prod_map]
  rfl

@[to_additive]

Depends on / 依赖: map_add_right_Ico, prod_map
-/
theorem prod_Ico_add' [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α -> M) (a b c : α) : (∏ x in Ico a b, f (x + c)) = ∏ x in Ico (a + c) (b + c), f x := by
  rw [← map_add_right_Ico]; rw [prod_map]
  rfl

@[to_additive]
/--
theorem `prod_Ico_add` / 定理 `prod_Ico_add`

English:
theorem prod_Ico_add
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  proof: by
  convert! prod_Ico_add' f a b c using 2
  rw [add_comm]

@[to_additive (attr := simp)]

中文:
定理 prod_Ico_add
  结论: [加法交换幺半群 α] [偏序 α] [是OrderedCancelAdd幺半群 α]
  证明: by
  convert! prod_Ico_add' f a b c using 2
  rw [add_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: add_comm, convert, prod_Ico_add
-/
theorem prod_Ico_add [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α -> M) (a b c : α) : (∏ x in Ico a b, f (c + x)) = ∏ x in Ico (a + c) (b + c), f x := by
  convert! prod_Ico_add' f a b c using 2
  rw [add_comm]

@[to_additive (attr := simp)]
/--
theorem `prod_Ico_add_right_sub_eq` / 定理 `prod_Ico_add_right_sub_eq`

English:
theorem prod_Ico_add_right_sub_eq
  statement: [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  proof: by
  simp only [← map_add_right_Ico, prod_map, addRightEmbedding_apply, add_tsub_cancel_right]

@[to_additive]

中文:
定理 prod_Ico_add_right_sub_eq
  结论: [加法交换幺半群 α] [偏序 α] [是OrderedCancelAdd幺半群 α]
  证明: by
  simp only [← map_add_right_Ico, prod_map, addRightEmbedding_apply, add_tsub_cancel_right]

@[to_additive]

Depends on / 依赖: addRightEmbedding_apply, add_tsub_cancel_right, map_add_right_Ico, prod_map
-/
theorem prod_Ico_add_right_sub_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [ExistsAddOfLE α] [LocallyFiniteOrder α] [Sub α] [OrderedSub α] (a b c : α) :
    ∏ x in Ico (a + c) (b + c), f (x - c) = ∏ x in Ico a b, f x := by
  simp only [← map_add_right_Ico, prod_map, addRightEmbedding_apply, add_tsub_cancel_right]

@[to_additive]
/--
theorem `prod_Ico_succ_top` / 定理 `prod_Ico_succ_top`

English:
theorem prod_Ico_succ_top
  given: {a b : Nat} (hab : a <= b) (f : Nat -> M)
  proof: by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab]; rw [prod_insert right_notMem_Ico]; rw [mul_comm]

@[to_additive]

中文:
定理 prod_Ico_succ_top
  条件: {a b : 自然数} (hab : a <= b) (f : 自然数 -> M)
  证明: by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab]; rw [prod_insert right_notMem_Ico]; rw [mul_comm]

@[to_additive]

Depends on / 依赖: Finset, Finset.insert_Ico_right_eq_Ico_add_one, insert_Ico_right_eq_Ico_add_one, mul_comm, prod_insert, right_notMem_Ico
-/
theorem prod_Ico_succ_top {a b : Nat} (hab : a <= b) (f : Nat -> M) :
    (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b := by
  rw [← Finset.insert_Ico_right_eq_Ico_add_one hab]; rw [prod_insert right_notMem_Ico]; rw [mul_comm]

@[to_additive]
/--
theorem `prod_Ico_consecutive` / 定理 `prod_Ico_consecutive`

English:
theorem prod_Ico_consecutive
  given: (f : Nat -> M) {m n k : Nat} (hmn : m <= n) (hnk : n <= k)
  proof: Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm (prod_union (Ico_disjoint_Ico_consecutive m n k))

@[to_additive]

中文:
定理 prod_Ico_consecutive
  条件: (f : 自然数 -> M) {m n k : 自然数} (hmn : m <= n) (hnk : n <= k)
  证明: Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm (prod_union (Ico_disjoint_Ico_consecutive m n k))

@[to_additive]

Depends on / 依赖: Eq.symm, Ico_disjoint_Ico_consecutive, Ico_union_Ico_eq_Ico, prod_union
-/
theorem prod_Ico_consecutive (f : Nat -> M) {m n k : Nat} (hmn : m <= n) (hnk : n <= k) :
    ((∏ i in Ico m n, f i) * ∏ i in Ico n k, f i) = ∏ i in Ico m k, f i :=
  Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm (prod_union (Ico_disjoint_Ico_consecutive m n k))

@[to_additive]
/--
theorem `prod_Ioc_consecutive` / 定理 `prod_Ioc_consecutive`

English:
theorem prod_Ioc_consecutive
  given: (f : Nat -> M) {m n k : Nat} (hmn : m <= n) (hnk : n <= k)
  proof: by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk]; rw [prod_union]
  apply disjoint_left.2 fun x hx h'x => _
  intro x hx h'x
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)

@[to_additive]

中文:
定理 prod_Ioc_consecutive
  条件: (f : 自然数 -> M) {m n k : 自然数} (hmn : m <= n) (hnk : n <= k)
  证明: by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk]; rw [prod_union]
  apply disjoint_left.2 fun x hx h'x => _
  intro x hx h'x
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)

@[to_additive]

Depends on / 依赖: Ioc_union_Ioc_eq_Ioc, disjoint_left, lt_irrefl, mem_Ioc, prod_union, trans_le
-/
theorem prod_Ioc_consecutive (f : Nat -> M) {m n k : Nat} (hmn : m <= n) (hnk : n <= k) :
    ((∏ i in Ioc m n, f i) * ∏ i in Ioc n k, f i) = ∏ i in Ioc m k, f i := by
  rw [← Ioc_union_Ioc_eq_Ioc hmn hnk]; rw [prod_union]
  apply disjoint_left.2 fun x hx h'x => _
  intro x hx h'x
  exact lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2)

@[to_additive]
/--
theorem `prod_Ioc_succ_top` / 定理 `prod_Ioc_succ_top`

English:
theorem prod_Ioc_succ_top
  given: {a b : Nat} (hab : a <= b) (f : Nat -> M)
  proof: by
  rw [← prod_Ioc_consecutive _ hab (Nat.le_succ b)]; rw [Nat.Ioc_succ_singleton]; rw [prod_singleton]

@[to_additive]

中文:
定理 prod_Ioc_succ_top
  条件: {a b : 自然数} (hab : a <= b) (f : 自然数 -> M)
  证明: by
  rw [← prod_Ioc_consecutive _ hab (Nat.le_succ b)]; rw [Nat.Ioc_succ_singleton]; rw [prod_singleton]

@[to_additive]

Depends on / 依赖: Ioc_succ_singleton, Nat.Ioc_succ_singleton, Nat.le_succ, le_succ, prod_Ioc_consecutive, prod_singleton
-/
theorem prod_Ioc_succ_top {a b : Nat} (hab : a <= b) (f : Nat -> M) :
    (∏ k in Ioc a (b + 1), f k) = (∏ k in Ioc a b, f k) * f (b + 1) := by
  rw [← prod_Ioc_consecutive _ hab (Nat.le_succ b)]; rw [Nat.Ioc_succ_singleton]; rw [prod_singleton]

@[to_additive]
/--
theorem `prod_Icc_succ_top` / 定理 `prod_Icc_succ_top`

English:
theorem prod_Icc_succ_top
  given: {a b : Nat} (hab : a <= b + 1) (f : Nat -> M)
  proof: by
  rw [← Ico_add_one_right_eq_Icc]; rw [prod_Ico_succ_top hab]; rw [Ico_add_one_right_eq_Icc]

@[to_additive]

中文:
定理 prod_Icc_succ_top
  条件: {a b : 自然数} (hab : a <= b + 1) (f : 自然数 -> M)
  证明: by
  rw [← Ico_add_one_right_eq_Icc]; rw [prod_Ico_succ_top hab]; rw [Ico_add_one_right_eq_Icc]

@[to_additive]

Depends on / 依赖: Ico_add_one_right_eq_Icc, prod_Ico_succ_top
-/
theorem prod_Icc_succ_top {a b : Nat} (hab : a <= b + 1) (f : Nat -> M) :
    (∏ k in Icc a (b + 1), f k) = (∏ k in Icc a b, f k) * f (b + 1) := by
  rw [← Ico_add_one_right_eq_Icc]; rw [prod_Ico_succ_top hab]; rw [Ico_add_one_right_eq_Icc]

@[to_additive]
/--
theorem `prod_range_mul_prod_Ico` / 定理 `prod_range_mul_prod_Ico`

English:
theorem prod_range_mul_prod_Ico
  given: (f : Nat -> M) {m n : Nat} (h : m <= n)
  proof: Nat.Ico_zero_eq_range m ▸ Nat.Ico_zero_eq_range n ▸ prod_Ico_consecutive f m.zero_le h

@[to_additive]

中文:
定理 prod_range_mul_prod_Ico
  条件: (f : 自然数 -> M) {m n : 自然数} (h : m <= n)
  证明: Nat.Ico_zero_eq_range m ▸ Nat.Ico_zero_eq_range n ▸ prod_Ico_consecutive f m.zero_le h

@[to_additive]

Depends on / 依赖: Ico_zero_eq_range, Nat.Ico_zero_eq_range, m.zero_le, prod_Ico_consecutive, zero_le
-/
theorem prod_range_mul_prod_Ico (f : Nat -> M) {m n : Nat} (h : m <= n) :
    ((∏ k in range m, f k) * ∏ k in Ico m n, f k) = ∏ k in range n, f k :=
  Nat.Ico_zero_eq_range m ▸ Nat.Ico_zero_eq_range n ▸ prod_Ico_consecutive f m.zero_le h

@[to_additive]
/--
theorem `prod_range_eq_mul_Ico` / 定理 `prod_range_eq_mul_Ico`

English:
theorem prod_range_eq_mul_Ico
  given: (f : Nat -> M) {n : Nat} (hn : 0 < n)
  proof: Finset.range_eq_Ico n ▸ Finset.prod_eq_prod_Ico_succ_bot hn f

@[to_additive]

中文:
定理 prod_range_eq_mul_Ico
  条件: (f : 自然数 -> M) {n : 自然数} (hn : 0 < n)
  证明: Finset.range_eq_Ico n ▸ Finset.prod_eq_prod_Ico_succ_bot hn f

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_eq_prod_Ico_succ_bot, Finset.range_eq_Ico, prod_eq_prod_Ico_succ_bot, range_eq_Ico
-/
theorem prod_range_eq_mul_Ico (f : Nat -> M) {n : Nat} (hn : 0 < n) :
    ∏ x in Finset.range n, f x = f 0 * ∏ x in Ico 1 n, f x :=
  Finset.range_eq_Ico n ▸ Finset.prod_eq_prod_Ico_succ_bot hn f

@[to_additive]
/--
theorem `prod_Ico_eq_mul_inv` / 定理 `prod_Ico_eq_mul_inv`

English:
theorem prod_Ico_eq_mul_inv
  given: {δ : Type*} [CommGroup δ] (f : Nat -> δ) {m n : Nat} (h : m <= n)
  proof: eq_mul_inv_iff_mul_eq.2 by (rw [mul_comm]; exact prod_range_mul_prod_Ico f h)

@[to_additive]

中文:
定理 prod_Ico_eq_mul_inv
  条件: {δ : 类型} [交换群 δ] (f : 自然数 -> δ) {m n : 自然数} (h : m <= n)
  证明: eq_mul_inv_iff_mul_eq.2 by (rw [mul_comm]; exact prod_range_mul_prod_Ico f h)

@[to_additive]

Depends on / 依赖: eq_mul_inv_iff_mul_eq, mul_comm, prod_range_mul_prod_Ico
-/
theorem prod_Ico_eq_mul_inv {δ : Type*} [CommGroup δ] (f : Nat -> δ) {m n : Nat} (h : m <= n) :
    ∏ k in Ico m n, f k = (∏ k in range n, f k) * (∏ k in range m, f k)⁻¹ :=
eq_mul_inv_iff_mul_eq.2 by (rw [mul_comm]; exact prod_range_mul_prod_Ico f h)

@[to_additive]
/--
theorem `prod_Ico_eq_div` / 定理 `prod_Ico_eq_div`

English:
theorem prod_Ico_eq_div
  given: {δ : Type*} [CommGroup δ] (f : Nat -> δ) {m n : Nat} (h : m <= n)
  proof: by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h

@[to_additive]

中文:
定理 prod_Ico_eq_div
  条件: {δ : 类型} [交换群 δ] (f : 自然数 -> δ) {m n : 自然数} (h : m <= n)
  证明: by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, prod_Ico_eq_mul_inv
-/
theorem prod_Ico_eq_div {δ : Type*} [CommGroup δ] (f : Nat -> δ) {m n : Nat} (h : m <= n) :
    ∏ k in Ico m n, f k = (∏ k in range n, f k) / ∏ k in range m, f k := by
  simpa only [div_eq_mul_inv] using prod_Ico_eq_mul_inv f h

@[to_additive]
/--
theorem `prod_range_div_prod_range` / 定理 `prod_range_div_prod_range`

English:
theorem prod_range_div_prod_range
  given: {G : Type*} [CommGroup G] {f : Nat -> G} {n m : Nat} (hnm : n <= m)
  proof: by
  rw [← prod_Ico_eq_div f hnm]
  congr
  apply Finset.ext
  simp only [mem_Ico, mem_filter, mem_range, *]
  tauto

中文:
定理 prod_range_div_prod_range
  条件: {G : 类型} [交换群 G] {f : 自然数 -> G} {n m : 自然数} (hnm : n <= m)
  证明: by
  rw [← prod_Ico_eq_div f hnm]
  congr
  apply Finset.ext
  simp only [mem_Ico, mem_filter, mem_range, *]
  tauto

Depends on / 依赖: Finset, Finset.ext, mem_Ico, mem_filter, mem_range, prod_Ico_eq_div
-/
theorem prod_range_div_prod_range {G : Type*} [CommGroup G] {f : Nat -> G} {n m : Nat} (hnm : n <= m) :
    ((∏ k in range m, f k) / ∏ k in range n, f k) = ∏ k in range m with n <= k, f k := by
  rw [← prod_Ico_eq_div f hnm]
  congr
  apply Finset.ext
  simp only [mem_Ico, mem_filter, mem_range, *]
  tauto

/--
theorem `sum_Ico_Ico_comm` / 定理 `sum_Ico_Ico_comm`

English:
theorem sum_Ico_Ico_comm
  given: {M : Type*} [AddCommMonoid M] (a b : Nat) (f : Nat -> Nat -> M)
  proof: by
  rw [Finset.sum_sigma']; rw [Finset.sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  lia

中文:
定理 sum_Ico_Ico_comm
  条件: {M : 类型} [加法交换幺半群 M] (a b : 自然数) (f : 自然数 -> 自然数 -> M)
  证明: by
  rw [Finset.sum_sigma']; rw [Finset.sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  lia

Depends on / 依赖: Finset, Finset.mem_Ico, Finset.mem_sigma, Finset.sum_sigma, Sigma.forall, mem_Ico, mem_sigma, sum_nbij, sum_sigma
-/
theorem sum_Ico_Ico_comm {M : Type*} [AddCommMonoid M] (a b : Nat) (f : Nat -> Nat -> M) :
    (∑ i in Finset.Ico a b, ∑ j in Finset.Ico i b, f i j) =
      ∑ j in Finset.Ico a b, ∑ i in Finset.Ico a (j + 1), f i j := by
  rw [Finset.sum_sigma']; rw [Finset.sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  lia

/--
theorem `sum_Ico_Ico_comm'` / 定理 `sum_Ico_Ico_comm'`

English:
theorem sum_Ico_Ico_comm'
  given: {M : Type*} [AddCommMonoid M] (a b : Nat) (f : Nat -> Nat -> M)
  proof: by
  rw [Finset.sum_sigma']; rw [Finset.sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  lia

@[to_additive]

中文:
定理 sum_Ico_Ico_comm'
  条件: {M : 类型} [加法交换幺半群 M] (a b : 自然数) (f : 自然数 -> 自然数 -> M)
  证明: by
  rw [Finset.sum_sigma']; rw [Finset.sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  lia

@[to_additive]

Depends on / 依赖: Finset, Finset.mem_Ico, Finset.mem_sigma, Finset.sum_sigma, Sigma.forall, mem_Ico, mem_sigma, sum_nbij, sum_sigma
-/
theorem sum_Ico_Ico_comm' {M : Type*} [AddCommMonoid M] (a b : Nat) (f : Nat -> Nat -> M) :
    (∑ i in Finset.Ico a b, ∑ j in Finset.Ico (i + 1) b, f i j) =
      ∑ j in Finset.Ico a b, ∑ i in Finset.Ico a j, f i j := by
  rw [Finset.sum_sigma']; rw [Finset.sum_sigma']
  refine sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) <;>
  simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
  lia

@[to_additive]
/--
theorem `prod_Ico_eq_prod_range` / 定理 `prod_Ico_eq_prod_range`

English:
theorem prod_Ico_eq_prod_range
  given: (f : Nat -> M) (m n : Nat)
  proof: by
  by_cases! h : m <= n
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h := h.le
    rw [Ico_eq_empty_of_le h]; rw [tsub_eq_zero_iff_le.mpr h]; rw [range_zero]; rw [prod_empty]; rw [prod_empty]

中文:
定理 prod_Ico_eq_prod_range
  条件: (f : 自然数 -> M) (m n : 自然数)
  证明: by
  by_cases! h : m <= n
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h := h.le
    rw [Ico_eq_empty_of_le h]; rw [tsub_eq_zero_iff_le.mpr h]; rw [range_zero]; rw [prod_empty]; rw [prod_empty]

Depends on / 依赖: Ico_eq_empty_of_le, Ico_zero_eq_range, Nat.Ico_zero_eq_range, h.le, prod_Ico_add, prod_empty, range_zero, replace, tsub_add_cancel_of_le, tsub_eq_zero_iff_le, tsub_eq_zero_iff_le.mpr, zero_add
-/
theorem prod_Ico_eq_prod_range (f : Nat -> M) (m n : Nat) :
    ∏ k in Ico m n, f k = ∏ k in range (n - m), f (m + k) := by
  by_cases! h : m <= n
  · rw [← Nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h := h.le
    rw [Ico_eq_empty_of_le h]; rw [tsub_eq_zero_iff_le.mpr h]; rw [range_zero]; rw [prod_empty]; rw [prod_empty]

/--
theorem `prod_Ico_reflect` / 定理 `prod_Ico_reflect`

English:
theorem prod_Ico_reflect
  given: (f : Nat -> M) (k : Nat) {m n : Nat} (h : m <= n + 1)
  proof: by
  have : forall i < m, i <= n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  rcases lt_or_ge k m with hkm | hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine (prod_image ?_).symm
    simp only [mem_Ico, Set.InjOn, mem_coe]
    rintro i ⟨_, im⟩ j ⟨_, jm⟩ Hij
    rw [← tsub_tsub_cancel_of_le (this _ im)]; rw [Hij]; rw [tsub_tsub_cancel_of_le (this _ jm)]
  · have : n + 1 - k <= n + 1 - m := by
      rw [tsub_le_tsub_iff_left h]
      exact hkm
    simp only [hkm, Ico_eq_empty_of_le, prod_empty, Ico_eq_empty_of_le this]

中文:
定理 prod_Ico_reflect
  条件: (f : 自然数 -> M) (k : 自然数) {m n : 自然数} (h : m <= n + 1)
  证明: by
  have : forall i < m, i <= n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  rcases lt_or_ge k m with hkm | hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine (prod_image ?_).symm
    simp only [mem_Ico, Set.InjOn, mem_coe]
    rintro i ⟨_, im⟩ j ⟨_, jm⟩ Hij
    rw [← tsub_tsub_cancel_of_le (this _ im)]; rw [Hij]; rw [tsub_tsub_cancel_of_le (this _ jm)]
  · have : n + 1 - k <= n + 1 - m := by
      rw [tsub_le_tsub_iff_left h]
      exact hkm
    simp only [hkm, Ico_eq_empty_of_le, prod_empty, Ico_eq_empty_of_le this]

Depends on / 依赖: Ico_, Ico_image_const_sub_eq_Ico, Nat.Ico_image_const_sub_eq_Ico, Nat.lt_iff_add_one_le, Set.InjOn, add_le_add_iff_right, le_trans, lt_iff_add_one_le, lt_or_ge, mem_Ico, mem_coe, prod_image, tsub_le_tsub_iff_left, tsub_tsub_cancel_of_le
-/
theorem prod_Ico_reflect (f : Nat -> M) (k : Nat) {m n : Nat} (h : m <= n + 1) :
    (∏ j in Ico k m, f (n - j)) = ∏ j in Ico (n + 1 - m) (n + 1 - k), f j := by
  have : forall i < m, i <= n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  rcases lt_or_ge k m with hkm | hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine (prod_image ?_).symm
    simp only [mem_Ico, Set.InjOn, mem_coe]
    rintro i ⟨_, im⟩ j ⟨_, jm⟩ Hij
    rw [← tsub_tsub_cancel_of_le (this _ im)]; rw [Hij]; rw [tsub_tsub_cancel_of_le (this _ jm)]
  · have : n + 1 - k <= n + 1 - m := by
      rw [tsub_le_tsub_iff_left h]
      exact hkm
    simp only [hkm, Ico_eq_empty_of_le, prod_empty, Ico_eq_empty_of_le this]

/--
theorem `sum_Ico_reflect` / 定理 `sum_Ico_reflect`

English:
theorem sum_Ico_reflect
  statement: {δ : Type*} [AddCommMonoid δ] (f : Nat -> δ) (k : Nat) {m n : Nat}
  proof: @prod_Ico_reflect (Multiplicative δ) _ f k m n h

中文:
定理 sum_Ico_reflect
  结论: {δ : 类型} [加法交换幺半群 δ] (f : 自然数 -> δ) (k : 自然数) {m n : 自然数}
  证明: @prod_Ico_reflect (Multiplicative δ) _ f k m n h

Depends on / 依赖: Multiplicative, prod_Ico_reflect
-/
theorem sum_Ico_reflect {δ : Type*} [AddCommMonoid δ] (f : Nat -> δ) (k : Nat) {m n : Nat}
    (h : m <= n + 1) : (∑ j in Ico k m, f (n - j)) = ∑ j in Ico (n + 1 - m) (n + 1 - k), f j :=
  @prod_Ico_reflect (Multiplicative δ) _ f k m n h

/--
theorem `prod_range_reflect` / 定理 `prod_range_reflect`

English:
theorem prod_range_reflect
  given: (f : Nat -> M) (n : Nat)
  proof: by
  cases n
  · simp
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [prod_Ico_reflect _ _ le_rfl]
    simp

中文:
定理 prod_range_reflect
  条件: (f : 自然数 -> M) (n : 自然数)
  证明: by
  cases n
  · simp
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [prod_Ico_reflect _ _ le_rfl]
    simp

Depends on / 依赖: Ico_zero_eq_range, Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, le_rfl, prod_Ico_reflect, succ_sub_succ_eq_sub, tsub_zero
-/
theorem prod_range_reflect (f : Nat -> M) (n : Nat) :
    (∏ j in range n, f (n - 1 - j)) = ∏ j in range n, f j := by
  cases n
  · simp
  · simp only [← Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
    rw [prod_Ico_reflect _ _ le_rfl]
    simp

/--
theorem `sum_range_reflect` / 定理 `sum_range_reflect`

English:
theorem sum_range_reflect
  given: {δ : Type*} [AddCommMonoid δ] (f : Nat -> δ) (n : Nat)
  proof: @prod_range_reflect (Multiplicative δ) _ f n

@[simp]

中文:
定理 sum_range_reflect
  条件: {δ : 类型} [加法交换幺半群 δ] (f : 自然数 -> δ) (n : 自然数)
  证明: @prod_range_reflect (Multiplicative δ) _ f n

@[simp]

Depends on / 依赖: Multiplicative, prod_range_reflect
-/
theorem sum_range_reflect {δ : Type*} [AddCommMonoid δ] (f : Nat -> δ) (n : Nat) :
    (∑ j in range n, f (n - 1 - j)) = ∑ j in range n, f j :=
  @prod_range_reflect (Multiplicative δ) _ f n

@[simp]
/--
theorem `prod_Ico_id_eq_factorial` / 定理 `prod_Ico_id_eq_factorial`

English:
theorem prod_Ico_id_eq_factorial
  statement: forall n : Nat, (∏ x in Ico 1 (n + 1), x) = n !

中文:
定理 prod_Ico_id_eq_factorial
  结论: 对任意 n : 自然数, (∏ x in 左闭右开区间 1 (n + 1), x) = n !
-/
theorem prod_Ico_id_eq_factorial : forall n : Nat, (∏ x in Ico 1 (n + 1), x) = n !
  | 0 => rfl
  | n + 1 => by
    rw [prod_Ico_succ_top <| Nat.succ_le_succ <| Nat.zero_le n]; rw [Nat.factorial_succ]; rw [prod_Ico_id_eq_factorial n]; rw [Nat.succ_eq_add_one]; rw [mul_comm]

section GaussSum

/--
theorem `sum_range_id_mul_two` / 定理 `sum_range_id_mul_two`

English:
theorem sum_range_id_mul_two
  given: (n : Nat)
  statement: (∑ i in range n, i) * 2 = n * (n - 1)
  proof: calc
    (∑ i in range n, i) * 2 = (∑ i in range n, i) + ∑ i in range n, (n - 1 - i) := by
      rw [sum_range_reflect (fun i => i) n]; rw [mul_two]
    _ = ∑ i in range n, (i + (n - 1 - i)) := sum_add_distrib.symm
    _ = ∑ _ in range n, (n - 1) :=
sum_congr rfl fun _ hi => add_tsub_cancel_of_le Nat.le_sub_one_of_lt mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]

中文:
定理 sum_range_id_mul_two
  条件: (n : 自然数)
  结论: (∑ i in range n, i) * 2 = n * (n - 1)
  证明: calc
    (∑ i in range n, i) * 2 = (∑ i in range n, i) + ∑ i in range n, (n - 1 - i) := by
      rw [sum_range_reflect (fun i => i) n]; rw [mul_two]
    _ = ∑ i in range n, (i + (n - 1 - i)) := sum_add_distrib.symm
    _ = ∑ _ in range n, (n - 1) :=
sum_congr rfl fun _ hi => add_tsub_cancel_of_le Nat.le_sub_one_of_lt mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]

Depends on / 依赖: Nat.le_sub_one_of_lt, Nat.nsmul_eq_mul, add_tsub_cancel_of_le, card_range, le_sub_one_of_lt, mem_range, mul_two, nsmul_eq_mul, sum_add_distrib, sum_add_distrib.symm, sum_congr, sum_const, sum_range_reflect
-/
theorem sum_range_id_mul_two (n : Nat) : (∑ i in range n, i) * 2 = n * (n - 1) :=
  calc
    (∑ i in range n, i) * 2 = (∑ i in range n, i) + ∑ i in range n, (n - 1 - i) := by
      rw [sum_range_reflect (fun i => i) n]; rw [mul_two]
    _ = ∑ i in range n, (i + (n - 1 - i)) := sum_add_distrib.symm
    _ = ∑ _ in range n, (n - 1) :=
sum_congr rfl fun _ hi => add_tsub_cancel_of_le Nat.le_sub_one_of_lt mem_range.1 hi
    _ = n * (n - 1) := by rw [sum_const, card_range, Nat.nsmul_eq_mul]

/--
theorem `sum_range_id` / 定理 `sum_range_id`

English:
theorem sum_range_id
  given: (n : Nat)
  statement: ∑ i in range n, i = n * (n - 1) / 2
  proof: by
  rw [← sum_range_id_mul_two n]; rw [Nat.mul_div_cancel _ Nat.zero_lt_two]

中文:
定理 sum_range_id
  条件: (n : 自然数)
  结论: ∑ i in range n, i = n * (n - 1) / 2
  证明: by
  rw [← sum_range_id_mul_two n]; rw [Nat.mul_div_cancel _ Nat.zero_lt_two]

Depends on / 依赖: Nat.mul_div_cancel, Nat.zero_lt_two, mul_div_cancel, sum_range_id_mul_two, zero_lt_two
-/
theorem sum_range_id (n : Nat) : ∑ i in range n, i = n * (n - 1) / 2 := by
  rw [← sum_range_id_mul_two n]; rw [Nat.mul_div_cancel _ Nat.zero_lt_two]

end GaussSum

@[to_additive]
/--
lemma `prod_range_diag_flip` / 引理 `prod_range_diag_flip`

English:
lemma prod_range_diag_flip
  given: (n : Nat) (f : Nat -> Nat -> M)
  proof: by
  rw [prod_sigma']; rw [prod_sigma']
  refine prod_nbij' (fun a => ⟨a.2, a.1 - a.2⟩) (fun a => ⟨a.1 + a.2, a.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp +contextual only [mem_sigma, mem_range, lt_tsub_iff_left,
      Nat.lt_succ_iff, le_add_iff_nonneg_right, Nat.zero_le, and_true, and_imp, implies_true,
      Sigma.forall, add_tsub_cancel_of_le, add_tsub_cancel_left]
  exact fun a b han hba => lt_of_le_of_lt hba han

中文:
引理 prod_range_diag_flip
  条件: (n : 自然数) (f : 自然数 -> 自然数 -> M)
  证明: by
  rw [prod_sigma']; rw [prod_sigma']
  refine prod_nbij' (fun a => ⟨a.2, a.1 - a.2⟩) (fun a => ⟨a.1 + a.2, a.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp +contextual only [mem_sigma, mem_range, lt_tsub_iff_left,
      Nat.lt_succ_iff, le_add_iff_nonneg_right, Nat.zero_le, and_true, and_imp, implies_true,
      Sigma.forall, add_tsub_cancel_of_le, add_tsub_cancel_left]
  exact fun a b han hba => lt_of_le_of_lt hba han

Depends on / 依赖: Nat.lt_succ_iff, Nat.zero_le, Sigma.forall, add_tsub_cancel_left, add_tsub_cancel_of_le, and_imp, and_true, contextual, implies_true, le_add_iff_nonneg_right, lt_of_le_of_lt, lt_succ_iff, lt_tsub_iff_left, mem_range, mem_sigma, prod_nbij, prod_sigma, zero_le
-/
lemma prod_range_diag_flip (n : Nat) (f : Nat -> Nat -> M) :
    (∏ m in range n, ∏ k in range (m + 1), f k (m - k)) =
      ∏ m in range n, ∏ k in range (n - m), f m k := by
  rw [prod_sigma']; rw [prod_sigma']
  refine prod_nbij' (fun a => ⟨a.2, a.1 - a.2⟩) (fun a => ⟨a.1 + a.2, a.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp +contextual only [mem_sigma, mem_range, lt_tsub_iff_left,
      Nat.lt_succ_iff, le_add_iff_nonneg_right, Nat.zero_le, and_true, and_imp, implies_true,
      Sigma.forall, add_tsub_cancel_of_le, add_tsub_cancel_left]
  exact fun a b han hba => lt_of_le_of_lt hba han

end Generic

section Nat

variable {M : Type*}
variable (f g : Nat -> M) {m n : Nat}

section Group

variable [CommGroup M]

@[to_additive]
/--
theorem `prod_range_succ_div_prod` / 定理 `prod_range_succ_div_prod`

English:
theorem prod_range_succ_div_prod
  statement: ((∏ i in range (n + 1), f i) / ∏ i in range n, f i) = f n
  proof: div_eq_iff_eq_mul'.mpr prod_range_succ f n

@[to_additive]

中文:
定理 prod_range_succ_div_prod
  结论: ((∏ i in range (n + 1), f i) / ∏ i in range n, f i) = f n
  证明: div_eq_iff_eq_mul'.mpr prod_range_succ f n

@[to_additive]

Depends on / 依赖: div_eq_iff_eq_mul, prod_range_succ
-/
theorem prod_range_succ_div_prod : ((∏ i in range (n + 1), f i) / ∏ i in range n, f i) = f n :=
div_eq_iff_eq_mul'.mpr prod_range_succ f n

@[to_additive]
/--
theorem `prod_range_succ_div_top` / 定理 `prod_range_succ_div_top`

English:
theorem prod_range_succ_div_top
  statement: (∏ i in range (n + 1), f i) / f n = ∏ i in range n, f i
  proof: div_eq_iff_eq_mul.mpr prod_range_succ f n

@[to_additive]

中文:
定理 prod_range_succ_div_top
  结论: (∏ i in range (n + 1), f i) / f n = ∏ i in range n, f i
  证明: div_eq_iff_eq_mul.mpr prod_range_succ f n

@[to_additive]

Depends on / 依赖: div_eq_iff_eq_mul, div_eq_iff_eq_mul.mpr, prod_range_succ
-/
theorem prod_range_succ_div_top : (∏ i in range (n + 1), f i) / f n = ∏ i in range n, f i :=
div_eq_iff_eq_mul.mpr prod_range_succ f n

@[to_additive]
/--
theorem `prod_Ico_div_bot` / 定理 `prod_Ico_div_bot`

English:
theorem prod_Ico_div_bot
  given: (hmn : m < n)
  statement: (∏ i in Ico m n, f i) / f m = ∏ i in Ico (m + 1) n, f i
  proof: div_eq_iff_eq_mul'.mpr prod_eq_prod_Ico_succ_bot hmn _

@[to_additive]

中文:
定理 prod_Ico_div_bot
  条件: (hmn : m < n)
  结论: (∏ i in 左闭右开区间 m n, f i) / f m = ∏ i in 左闭右开区间 (m + 1) n, f i
  证明: div_eq_iff_eq_mul'.mpr prod_eq_prod_Ico_succ_bot hmn _

@[to_additive]

Depends on / 依赖: div_eq_iff_eq_mul, prod_eq_prod_Ico_succ_bot
-/
theorem prod_Ico_div_bot (hmn : m < n) : (∏ i in Ico m n, f i) / f m = ∏ i in Ico (m + 1) n, f i :=
div_eq_iff_eq_mul'.mpr prod_eq_prod_Ico_succ_bot hmn _

@[to_additive]
/--
theorem `prod_Ico_succ_div_top` / 定理 `prod_Ico_succ_div_top`

English:
theorem prod_Ico_succ_div_top
  given: (hmn : m <= n)
  proof: div_eq_iff_eq_mul.mpr prod_Ico_succ_top hmn _

@[to_additive]

中文:
定理 prod_Ico_succ_div_top
  条件: (hmn : m <= n)
  证明: div_eq_iff_eq_mul.mpr prod_Ico_succ_top hmn _

@[to_additive]

Depends on / 依赖: div_eq_iff_eq_mul, div_eq_iff_eq_mul.mpr, prod_Ico_succ_top
-/
theorem prod_Ico_succ_div_top (hmn : m <= n) :
    (∏ i in Ico m (n + 1), f i) / f n = ∏ i in Ico m n, f i :=
div_eq_iff_eq_mul.mpr prod_Ico_succ_top hmn _

@[to_additive]
/--
theorem `prod_Ico_div` / 定理 `prod_Ico_div`

English:
theorem prod_Ico_div
  given: (hmn : m <= n)
  statement: ∏ i in Ico m n, f (i + 1) / f i = f n / f m
  proof: by
  rw [prod_Ico_eq_div _ hmn]; rw [prod_range_div]; rw [prod_range_div]; rw [div_div_div_cancel_right]

@[to_additive]

中文:
定理 prod_Ico_div
  条件: (hmn : m <= n)
  结论: ∏ i in 左闭右开区间 m n, f (i + 1) / f i = f n / f m
  证明: by
  rw [prod_Ico_eq_div _ hmn]; rw [prod_range_div]; rw [prod_range_div]; rw [div_div_div_cancel_right]

@[to_additive]

Depends on / 依赖: div_div_div_cancel_right, prod_Ico_eq_div, prod_range_div
-/
theorem prod_Ico_div (hmn : m <= n) : ∏ i in Ico m n, f (i + 1) / f i = f n / f m := by
  rw [prod_Ico_eq_div _ hmn]; rw [prod_range_div]; rw [prod_range_div]; rw [div_div_div_cancel_right]

@[to_additive]
/--
theorem `prod_Icc_div` / 定理 `prod_Icc_div`

English:
theorem prod_Icc_div
  given: (hmn : m <= n) (f : Nat -> M)
  proof: by
  rw [← Finset.Ico_add_one_right_eq_Icc]; rw [prod_Ico_div]
  omega

中文:
定理 prod_Icc_div
  条件: (hmn : m <= n) (f : 自然数 -> M)
  证明: by
  rw [← Finset.Ico_add_one_right_eq_Icc]; rw [prod_Ico_div]
  omega

Depends on / 依赖: Finset, Finset.Ico_add_one_right_eq_Icc, Ico_add_one_right_eq_Icc, prod_Ico_div
-/
theorem prod_Icc_div (hmn : m <= n) (f : Nat -> M) :
    ∏ i in Icc m n, f (i + 1) / f i = f (n + 1) / f m := by
  rw [← Finset.Ico_add_one_right_eq_Icc]; rw [prod_Ico_div]
  omega

end Group

end Nat
end Finset

section Fin

@[to_additive]
/--
lemma `Finset.prod_fin_Icc_eq_prod_nat_Icc` / 引理 `Finset.prod_fin_Icc_eq_prod_nat_Icc`

English:
lemma Finset.prod_fin_Icc_eq_prod_nat_Icc
  given: [CommMonoid α] {n : Nat} (a b : Fin n) (f : Fin n -> α)
  proof: by
  rw [← prod_ite_mem_eq]; rw [prod_fin_eq_prod_range]
  apply prod_congr_of_eq_on_inter <;> grind

中文:
引理 有限集.prod_fin_Icc_eq_prod_nat_Icc
  条件: [交换幺半群 α] {n : 自然数} (a b : 有限集 n) (f : 有限集 n -> α)
  证明: by
  rw [← prod_ite_mem_eq]; rw [prod_fin_eq_prod_range]
  apply prod_congr_of_eq_on_inter <;> grind

Depends on / 依赖: prod_congr_of_eq_on_inter, prod_fin_eq_prod_range, prod_ite_mem_eq
-/
lemma Finset.prod_fin_Icc_eq_prod_nat_Icc [CommMonoid α] {n : Nat} (a b : Fin n) (f : Fin n -> α) :
    ∏ i in Icc a b, f i = ∏ i in Icc (a : Nat) b, if h : i < n then f ⟨i, h⟩ else 1 := by
  rw [← prod_ite_mem_eq]; rw [prod_fin_eq_prod_range]
  apply prod_congr_of_eq_on_inter <;> grind

/-- Telescopic product over `Fin`. -/
@[to_additive /-- Telescopic sum over `Fin`. -/]
/--
lemma `Fin.prod_Iic_div` / 引理 `Fin.prod_Iic_div`

English:
lemma Fin.prod_Iic_div
  given: [CommGroup M] {n : Nat} (a : Fin n) (f : Fin (n + 1) -> M)
  proof: by
  rw [← prod_ite_mem_eq]; rw [prod_fin_eq_prod_range]
  convert! prod_range_div (fun i => if hi : i < n + 1 then f ⟨i, hi⟩ else 1) (a + 1) using 1 with k
    hk
  · exact prod_congr_of_eq_on_inter (by grind) (by grind) (by simp_all; grind)
  · grind

中文:
引理 有限集.prod_Iic_div
  条件: [交换群 M] {n : 自然数} (a : 有限集 n) (f : 有限集 (n + 1) -> M)
  证明: by
  rw [← prod_ite_mem_eq]; rw [prod_fin_eq_prod_range]
  convert! prod_range_div (fun i => if hi : i < n + 1 then f ⟨i, hi⟩ else 1) (a + 1) using 1 with k
    hk
  · exact prod_congr_of_eq_on_inter (by grind) (by grind) (by simp_all; grind)
  · grind

Depends on / 依赖: convert, prod_congr_of_eq_on_inter, prod_fin_eq_prod_range, prod_ite_mem_eq, prod_range_div
-/
lemma Fin.prod_Iic_div [CommGroup M] {n : Nat} (a : Fin n) (f : Fin (n + 1) -> M) :
    ∏ i in Iic a, (f i.succ / f i.castSucc) = f a.succ / f 0 := by
  rw [← prod_ite_mem_eq]; rw [prod_fin_eq_prod_range]
  convert! prod_range_div (fun i => if hi : i < n + 1 then f ⟨i, hi⟩ else 1) (a + 1) using 1 with k
    hk
  · exact prod_congr_of_eq_on_inter (by grind) (by grind) (by simp_all; grind)
  · grind

/-- Telescopic product over `Fin`. -/
@[to_additive /-- Telescopic sum over `Fin`. -/]
/--
lemma `Fin.prod_Icc_div` / 引理 `Fin.prod_Icc_div`

English:
lemma Fin.prod_Icc_div
  statement: [CommGroup M] {n : Nat} {a b : Fin n} (hab : a <= b)
  proof: by
  rw [prod_fin_Icc_eq_prod_nat_Icc]
  convert! Finset.prod_Icc_div (Fin.le_def.1 hab) (fun i => if hi : i < n + 1 then f ⟨i, hi⟩ else 1)
  · simp_all
    grind
  · grind
  · simp only [Order.lt_add_one_iff, is_le', ↓reduceDIte]
    rfl

中文:
引理 有限集.prod_Icc_div
  结论: [交换群 M] {n : 自然数} {a b : 有限集 n} (hab : a <= b)
  证明: by
  rw [prod_fin_Icc_eq_prod_nat_Icc]
  convert! Finset.prod_Icc_div (Fin.le_def.1 hab) (fun i => if hi : i < n + 1 then f ⟨i, hi⟩ else 1)
  · simp_all
    grind
  · grind
  · simp only [Order.lt_add_one_iff, is_le', ↓reduceDIte]
    rfl

Depends on / 依赖: Fin.le_def, Finset, Finset.prod_Icc_div, Order.lt_add_one_iff, convert, is_le, le_def, lt_add_one_iff, prod_Icc_div, prod_fin_Icc_eq_prod_nat_Icc, reduceDIte
-/
lemma Fin.prod_Icc_div [CommGroup M] {n : Nat} {a b : Fin n} (hab : a <= b)
    (f : Fin (n + 1) -> M) :
    ∏ i in Icc a b, (f i.succ / f i.castSucc) = f b.succ / f a.castSucc := by
  rw [prod_fin_Icc_eq_prod_nat_Icc]
  convert! Finset.prod_Icc_div (Fin.le_def.1 hab) (fun i => if hi : i < n + 1 then f ⟨i, hi⟩ else 1)
  · simp_all
    grind
  · grind
  · simp only [Order.lt_add_one_iff, is_le', ↓reduceDIte]
    rfl

end Fin
