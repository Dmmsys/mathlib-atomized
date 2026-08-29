/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Flatten
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Range
public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Algebra.Group.Opposite

/-!
# Sums and products from lists

This file provides further results about `List.prod`, `List.sum`,
which calculate the product and sum of elements of a list
and `List.alternatingProd`, `List.alternatingSum`, their alternating counterparts.
-/

public section
assert_not_imported Mathlib.Algebra.Order.Group.Nat

variable {ι α β M N P G : Type*}

namespace List

section Monoid

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

@[to_additive]
/--
theorem `prod_isUnit` / 定理 `prod_isUnit`

English:
theorem prod_isUnit
  statement: forall {L : List M}, (forall m in L, IsUnit m) -> IsUnit L.prod

中文:
定理 prod_isUnit
  结论: 对任意 {L : 列表 M}, (对任意 m in L, 是单位 m) -> 是单位 L.乘积
-/
theorem prod_isUnit : forall {L : List M}, (forall m in L, IsUnit m) -> IsUnit L.prod
  | [], _ => by simp
  | h :: t, u => by
    simp only [List.prod_cons]
    exact IsUnit.mul (u h mem_cons_self) (prod_isUnit fun m mt => u m (mem_cons_of_mem h mt))

@[to_additive]
/--
theorem `prod_isUnit_iff` / 定理 `prod_isUnit_iff`

English:
theorem prod_isUnit_iff
  given: {M : Type*} [CommMonoid M] {L : List M}
  proof: by
  refine ⟨fun h => ?_, prod_isUnit⟩
  induction L with
  | nil => exact fun m' h' => False.elim (not_mem_nil h')
  | cons m L ih =>
    rw [prod_cons]; rw [IsUnit.mul_iff] at h
    exact fun m' h' => Or.elim (eq_or_mem_of_mem_cons h') (fun H => H.substr h.1) fun H => ih h.2 _ H

中文:
定理 prod_isUnit_iff
  条件: {M : 类型} [交换幺半群 M] {L : 列表 M}
  证明: by
  refine ⟨fun h => ?_, prod_isUnit⟩
  induction L with
  | nil => exact fun m' h' => False.elim (not_mem_nil h')
  | cons m L ih =>
    rw [prod_cons]; rw [IsUnit.mul_iff] at h
    exact fun m' h' => Or.elim (eq_or_mem_of_mem_cons h') (fun H => H.substr h.1) fun H => ih h.2 _ H

Depends on / 依赖: False.elim, H.substr, IsUnit, IsUnit.mul_iff, Or.elim, eq_or_mem_of_mem_cons, mul_iff, not_mem_nil, prod_cons, prod_isUnit, substr
-/
theorem prod_isUnit_iff {M : Type*} [CommMonoid M] {L : List M} :
    IsUnit L.prod ↔ forall m in L, IsUnit m := by
  refine ⟨fun h => ?_, prod_isUnit⟩
  induction L with
  | nil => exact fun m' h' => False.elim (not_mem_nil h')
  | cons m L ih =>
    rw [prod_cons]; rw [IsUnit.mul_iff] at h
    exact fun m' h' => Or.elim (eq_or_mem_of_mem_cons h') (fun H => H.substr h.1) fun H => ih h.2 _ H

/-- If elements of a list commute with each other, then their product does not
depend on the order of elements. -/
@[to_additive /-- If elements of a list additively commute with each other, then their sum does not
depend on the order of elements. -/]
/--
lemma `Perm.prod_eq'` / 引理 `Perm.prod_eq'`

English:
lemma Perm.prod_eq'
  given: (h : l₁ ~ l₂) (hc : l₁.Pairwise Commute)
  statement: l₁.prod = l₂.prod
  proof: by
  have : Std.Symm fun x y => forall z : M, y * (x * z) = x * (y * z) := { symm x y h z := h z |>.symm }
  refine h.foldr_eq' (Pairwise.forall_of_forall (fun _ _ _ => rfl) <| hc.imp fun {a b} h z => ?_) 1
  rw [← mul_assoc]; rw [← mul_assoc]; rw [h]

中文:
引理 置换.prod_eq'
  条件: (h : l₁ ~ l₂) (hc : l₁.两两 Commute)
  结论: l₁.乘积 = l₂.乘积
  证明: by
  have : Std.Symm fun x y => forall z : M, y * (x * z) = x * (y * z) := { symm x y h z := h z |>.symm }
  refine h.foldr_eq' (Pairwise.forall_of_forall (fun _ _ _ => rfl) <| hc.imp fun {a b} h z => ?_) 1
  rw [← mul_assoc]; rw [← mul_assoc]; rw [h]

Depends on / 依赖: Pairwise, Pairwise.forall_of_forall, Std.Symm, foldr_eq, forall_of_forall, h.foldr_eq, hc.imp, mul_assoc
-/
lemma Perm.prod_eq' (h : l₁ ~ l₂) (hc : l₁.Pairwise Commute) : l₁.prod = l₂.prod := by
  have : Std.Symm fun x y => forall z : M, y * (x * z) = x * (y * z) := { symm x y h z := h z |>.symm }
  refine h.foldr_eq' (Pairwise.forall_of_forall (fun _ _ _ => rfl) <| hc.imp fun {a b} h z => ?_) 1
  rw [← mul_assoc]; rw [← mul_assoc]; rw [h]

end Monoid

section Group

variable [Group G]

/--
lemma `prod_rotate_eq_one_of_prod_eq_one` / 引理 `prod_rotate_eq_one_of_prod_eq_one`

English:
lemma prod_rotate_eq_one_of_prod_eq_one
  proof: le_of_lt (Nat.mod_lt _ (by simp))
    rw [← List.take_append_drop (n % List.length (a :: l)) (a :: l)] at hl
    rw [← rotate_mod]; rw [rotate_eq_drop_append_take this]; rw [List.prod_append]; rw [mul_eq_one_iff_inv_eq]; rw [← one_mul (List.prod _)⁻¹]; rw [← hl]; rw [List.prod_append]; rw [mul_assoc]; rw [mul_inv_cancel]; rw [mul_one]

中文:
引理 prod_rotate_eq_one_of_prod_eq_one
  证明: le_of_lt (Nat.mod_lt _ (by simp))
    rw [← List.take_append_drop (n % List.length (a :: l)) (a :: l)] at hl
    rw [← rotate_mod]; rw [rotate_eq_drop_append_take this]; rw [List.prod_append]; rw [mul_eq_one_iff_inv_eq]; rw [← one_mul (List.prod _)⁻¹]; rw [← hl]; rw [List.prod_append]; rw [mul_assoc]; rw [mul_inv_cancel]; rw [mul_one]

Depends on / 依赖: Nat.mod_lt, le_of_lt, mod_lt
-/
lemma prod_rotate_eq_one_of_prod_eq_one :
    forall {l : List G} (_ : l.prod = 1) (n : Nat), (l.rotate n).prod = 1
  | [], _, _ => by simp
  | a :: l, hl, n => by
    have : n % List.length (a :: l) <= List.length (a :: l) := le_of_lt (Nat.mod_lt _ (by simp))
    rw [← List.take_append_drop (n % List.length (a :: l)) (a :: l)] at hl
    rw [← rotate_mod]; rw [rotate_eq_drop_append_take this]; rw [List.prod_append]; rw [mul_eq_one_iff_inv_eq]; rw [← one_mul (List.prod _)⁻¹]; rw [← hl]; rw [List.prod_append]; rw [mul_assoc]; rw [mul_inv_cancel]; rw [mul_one]

end Group

variable [DecidableEq α]

/--
theorem `sum_map_count_dedup_filter_eq_countP` / 定理 `sum_map_count_dedup_filter_eq_countP`

English:
theorem sum_map_count_dedup_filter_eq_countP
  given: (p : α -> Bool) (l : List α)
  proof: by
  induction l with
  | nil => simp
  | cons a as h =>
    simp_rw [List.countP_cons, List.count_cons, List.sum_map_add]
    congr 1
    · refine _root_.trans ?_ h
      by_cases ha : a in as
      · simp [dedup_cons_of_mem ha]
      · simp only [dedup_cons_of_notMem ha, List.filter]
        match p a with
        | true => simp only [List.map_cons, List.sum_cons, List.count_eq_zero.2 ha, zero_add]
        | false => simp only
    · simp only [beq_iff_eq]
      by_cases hp : p a
      · refine _root_.trans (sum_map_eq_nsmul_single a _ fun _ h _ => by simp [h.symm]) ?_
        simp [hp, count_dedup]
      · exact _root_.trans (List.sum_eq_zero fun n hn => by grind) (by simp [hp])

中文:
定理 sum_map_count_dedup_filter_eq_countP
  条件: (p : α -> 布尔值) (l : 列表 α)
  证明: by
  induction l with
  | nil => simp
  | cons a as h =>
    simp_rw [List.countP_cons, List.count_cons, List.sum_map_add]
    congr 1
    · refine _root_.trans ?_ h
      by_cases ha : a in as
      · simp [dedup_cons_of_mem ha]
      · simp only [dedup_cons_of_notMem ha, List.filter]
        match p a with
        | true => simp only [List.map_cons, List.sum_cons, List.count_eq_zero.2 ha, zero_add]
        | false => simp only
    · simp only [beq_iff_eq]
      by_cases hp : p a
      · refine _root_.trans (sum_map_eq_nsmul_single a _ fun _ h _ => by simp [h.symm]) ?_
        simp [hp, count_dedup]
      · exact _root_.trans (List.sum_eq_zero fun n hn => by grind) (by simp [hp])

Depends on / 依赖: List.countP_cons, List.count_cons, List.count_eq_zero, List.filter, List.map_cons, List.sum_cons, List.sum_map_add, _root_, _root_.trans, beq_iff_eq, countP_cons, count_cons, count_eq_zero, dedup_cons_of_mem, dedup_cons_of_notMem, filter, h.symm, map_cons, simp_rw, sum_cons
-/
theorem sum_map_count_dedup_filter_eq_countP (p : α -> Bool) (l : List α) :
    ((l.dedup.filter p).map fun x => l.count x).sum = l.countP p := by
  induction l with
  | nil => simp
  | cons a as h =>
    simp_rw [List.countP_cons, List.count_cons, List.sum_map_add]
    congr 1
    · refine _root_.trans ?_ h
      by_cases ha : a in as
      · simp [dedup_cons_of_mem ha]
      · simp only [dedup_cons_of_notMem ha, List.filter]
        match p a with
        | true => simp only [List.map_cons, List.sum_cons, List.count_eq_zero.2 ha, zero_add]
        | false => simp only
    · simp only [beq_iff_eq]
      by_cases hp : p a
      · refine _root_.trans (sum_map_eq_nsmul_single a _ fun _ h _ => by simp [h.symm]) ?_
        simp [hp, count_dedup]
      · exact _root_.trans (List.sum_eq_zero fun n hn => by grind) (by simp [hp])

/--
theorem `sum_map_count_dedup_eq_length` / 定理 `sum_map_count_dedup_eq_length`

English:
theorem sum_map_count_dedup_eq_length
  given: (l : List α)
  proof: by
  simpa using sum_map_count_dedup_filter_eq_countP (fun _ => True) l

中文:
定理 sum_map_count_dedup_eq_length
  条件: (l : 列表 α)
  证明: by
  simpa using sum_map_count_dedup_filter_eq_countP (fun _ => True) l

Depends on / 依赖: sum_map_count_dedup_filter_eq_countP
-/
theorem sum_map_count_dedup_eq_length (l : List α) :
    (l.dedup.map fun x => l.count x).sum = l.length := by
  simpa using sum_map_count_dedup_filter_eq_countP (fun _ => True) l

end List

namespace List

/--
lemma `length_sigma` / 引理 `length_sigma`

English:
lemma length_sigma
  given: {σ : α -> Type*} (l₁ : List α) (l₂ : forall a, List (σ a))
  proof: by
  induction l₁ with
  | nil => rfl
  | cons x l₁ IH => simp only [sigma_cons, length_append, length_map, IH, map, sum_cons]

中文:
引理 length_sigma
  条件: {σ : α -> 类型} (l₁ : 列表 α) (l₂ : 对任意 a, 列表 (σ a))
  证明: by
  induction l₁ with
  | nil => rfl
  | cons x l₁ IH => simp only [sigma_cons, length_append, length_map, IH, map, sum_cons]

Depends on / 依赖: length_append, length_map, sigma_cons, sum_cons
-/
lemma length_sigma {σ : α -> Type*} (l₁ : List α) (l₂ : forall a, List (σ a)) :
    length (l₁.sigma l₂) = (l₁.map fun a => length (l₂ a)).sum := by
  induction l₁ with
  | nil => rfl
  | cons x l₁ IH => simp only [sigma_cons, length_append, length_map, IH, map, sum_cons]

/--
lemma `ranges_flatten` / 引理 `ranges_flatten`

English:
lemma ranges_flatten
  statement: forall (l : List Nat), l.ranges.flatten = range l.sum

中文:
引理 ranges_flatten
  结论: 对任意 (l : 列表 自然数), l.ranges.flatten = range l.求和
-/
lemma ranges_flatten : forall (l : List Nat), l.ranges.flatten = range l.sum
  | [] => rfl
  | a :: l => by simp [ranges, ← map_flatten, ranges_flatten, range_add]

/--
theorem `ranges_nodup` / 定理 `ranges_nodup`

English:
theorem ranges_nodup
  given: {l s : List Nat} (hs : s in ranges l)
  statement: s.Nodup
  proof: (List.pairwise_flatten.mp <| by rw [ranges_flatten]; exact nodup_range).1 s hs

中文:
定理 ranges_nodup
  条件: {l s : 列表 自然数} (hs : s in ranges l)
  结论: s.Nodup
  证明: (List.pairwise_flatten.mp <| by rw [ranges_flatten]; exact nodup_range).1 s hs

Depends on / 依赖: List.pairwise_flatten.mp, nodup_range, pairwise_flatten, ranges_flatten
-/
theorem ranges_nodup {l s : List Nat} (hs : s in ranges l) : s.Nodup :=
  (List.pairwise_flatten.mp <| by rw [ranges_flatten]; exact nodup_range).1 s hs

/--
lemma `mem_mem_ranges_iff_lt_sum` / 引理 `mem_mem_ranges_iff_lt_sum`

English:
lemma mem_mem_ranges_iff_lt_sum
  given: (l : List Nat) {n : Nat}
  proof: by
  rw [← mem_range]; rw [← ranges_flatten]; rw [mem_flatten]

中文:
引理 mem_mem_ranges_iff_lt_sum
  条件: (l : 列表 自然数) {n : 自然数}
  证明: by
  rw [← mem_range]; rw [← ranges_flatten]; rw [mem_flatten]

Depends on / 依赖: mem_flatten, mem_range, ranges_flatten
-/
lemma mem_mem_ranges_iff_lt_sum (l : List Nat) {n : Nat} :
    (exists s in l.ranges, n in s) ↔ n < l.sum := by
  rw [← mem_range]; rw [← ranges_flatten]; rw [mem_flatten]

/--
lemma `drop_take_succ_flatten_eq_getElem` / 引理 `drop_take_succ_flatten_eq_getElem`

English:
lemma drop_take_succ_flatten_eq_getElem
  given: (L : List (List α)) (i : Nat) (h : i < L.length)
  proof: by
  have : (L.map length).take i = ((L.take (i + 1)).map length).take i := by
    simp [map_take, take_take, Nat.min_eq_left]
  simp only [this, take_sum_flatten, drop_sum_flatten,
    drop_take_succ_eq_cons_getElem, h, flatten_nil, flatten_cons, append_nil]

中文:
引理 drop_take_succ_flatten_eq_getElem
  条件: (L : 列表 (列表 α)) (i : 自然数) (h : i < L.length)
  证明: by
  have : (L.map length).take i = ((L.take (i + 1)).map length).take i := by
    simp [map_take, take_take, Nat.min_eq_left]
  simp only [this, take_sum_flatten, drop_sum_flatten,
    drop_take_succ_eq_cons_getElem, h, flatten_nil, flatten_cons, append_nil]

Depends on / 依赖: L.map, L.take, Nat.min_eq_left, append_nil, drop_sum_flatten, drop_take_succ_eq_cons_getElem, flatten_cons, flatten_nil, length, map_take, min_eq_left, take_sum_flatten, take_take
-/
lemma drop_take_succ_flatten_eq_getElem (L : List (List α)) (i : Nat) (h : i < L.length) :
    (L.flatten.take ((L.map length).take (i + 1)).sum).drop ((L.map length).take i).sum = L[i] := by
  have : (L.map length).take i = ((L.take (i + 1)).map length).take i := by
    simp [map_take, take_take, Nat.min_eq_left]
  simp only [this, take_sum_flatten, drop_sum_flatten,
    drop_take_succ_eq_cons_getElem, h, flatten_nil, flatten_cons, append_nil]

end List


namespace List

/--
theorem `neg_one_mem_of_prod_eq_neg_one` / 定理 `neg_one_mem_of_prod_eq_neg_one`

English:
theorem neg_one_mem_of_prod_eq_neg_one
  given: {l : List Int} (h : l.prod = -1)
  statement: (-1 : Int) in l
  proof: by
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h (by decide))
  exact Or.resolve_left
    (Int.isUnit_iff.mp (prod_isUnit_iff.mp
      (h.symm ▸ ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩ : IsUnit l.prod) x h₁)) h₂ ▸ h₁

中文:
定理 neg_one_mem_of_prod_eq_neg_one
  条件: {l : 列表 整数} (h : l.乘积 = -1)
  结论: (-1 : 整数) in l
  证明: by
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h (by decide))
  exact Or.resolve_left
    (Int.isUnit_iff.mp (prod_isUnit_iff.mp
      (h.symm ▸ ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩ : IsUnit l.prod) x h₁)) h₂ ▸ h₁

Depends on / 依赖: Int.isUnit_iff.mp, IsUnit, Or.resolve_left, exists_mem_ne_one_of_prod_ne_one, h.symm, isUnit_iff, l.prod, ne_of_eq_of_ne, prod_isUnit_iff, prod_isUnit_iff.mp, resolve_left
-/
theorem neg_one_mem_of_prod_eq_neg_one {l : List Int} (h : l.prod = -1) : (-1 : Int) in l := by
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h (by decide))
  exact Or.resolve_left
    (Int.isUnit_iff.mp (prod_isUnit_iff.mp
      (h.symm ▸ ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩ : IsUnit l.prod) x h₁)) h₂ ▸ h₁

/--
theorem `dvd_prod` / 定理 `dvd_prod`

English:
theorem dvd_prod
  given: [CommMonoid M] {a} {l : List M} (ha : a in l)
  statement: a ∣ l.prod
  proof: by
  let ⟨s, t, h⟩ := append_of_mem ha
  rw [h]; rw [prod_append]; rw [prod_cons]; rw [mul_left_comm]
  exact dvd_mul_right _ _

中文:
定理 dvd_prod
  条件: [交换幺半群 M] {a} {l : 列表 M} (ha : a in l)
  结论: a ∣ l.乘积
  证明: by
  let ⟨s, t, h⟩ := append_of_mem ha
  rw [h]; rw [prod_append]; rw [prod_cons]; rw [mul_left_comm]
  exact dvd_mul_right _ _

Depends on / 依赖: append_of_mem, dvd_mul_right, mul_left_comm, prod_append, prod_cons
-/
theorem dvd_prod [CommMonoid M] {a} {l : List M} (ha : a in l) : a ∣ l.prod := by
  let ⟨s, t, h⟩ := append_of_mem ha
  rw [h]; rw [prod_append]; rw [prod_cons]; rw [mul_left_comm]
  exact dvd_mul_right _ _

/--
theorem `Sublist.prod_dvd_prod` / 定理 `Sublist.prod_dvd_prod`

English:
theorem Sublist.prod_dvd_prod
  given: [CommMonoid M] {l₁ l₂ : List M} (h : l₁ <+ l₂)
  proof: by
  obtain ⟨l, hl⟩ := h.exists_perm_append
  rw [hl.prod_eq]; rw [prod_append]
  exact dvd_mul_right _ _

中文:
定理 子表.prod_dvd_prod
  条件: [交换幺半群 M] {l₁ l₂ : 列表 M} (h : l₁ <+ l₂)
  证明: by
  obtain ⟨l, hl⟩ := h.exists_perm_append
  rw [hl.prod_eq]; rw [prod_append]
  exact dvd_mul_right _ _

Depends on / 依赖: dvd_mul_right, exists_perm_append, h.exists_perm_append, hl.prod_eq, prod_append, prod_eq
-/
theorem Sublist.prod_dvd_prod [CommMonoid M] {l₁ l₂ : List M} (h : l₁ <+ l₂) :
    l₁.prod ∣ l₂.prod := by
  obtain ⟨l, hl⟩ := h.exists_perm_append
  rw [hl.prod_eq]; rw [prod_append]
  exact dvd_mul_right _ _

section Alternating

variable [CommGroup G]

@[to_additive]
/--
theorem `alternatingProd_append` / 定理 `alternatingProd_append`

English:
theorem alternatingProd_append

中文:
定理 alternatingProd_append
-/
theorem alternatingProd_append :
    forall l₁ l₂ : List G,
      alternatingProd (l₁ ++ l₂) = alternatingProd l₁ * alternatingProd l₂ ^ (-1 : Int) ^ length l₁
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp_rw [cons_append, alternatingProd_cons, alternatingProd_append, length_cons, pow_succ',
      Int.neg_mul, one_mul, zpow_neg, ← div_eq_mul_inv, div_div]

@[to_additive]
/--
theorem `alternatingProd_reverse` / 定理 `alternatingProd_reverse`

English:
theorem alternatingProd_reverse

中文:
定理 alternatingProd_reverse
-/
theorem alternatingProd_reverse :
    forall l : List G, alternatingProd (reverse l) = alternatingProd l ^ (-1 : Int) ^ (length l + 1)
  | [] => by simp only [alternatingProd_nil, one_zpow, reverse_nil]
  | a :: l => by
    simp_rw [reverse_cons, alternatingProd_append, alternatingProd_reverse,
      alternatingProd_singleton, alternatingProd_cons, length_reverse, length, pow_succ',
      Int.neg_mul, one_mul, zpow_neg, inv_inv]
    rw [mul_comm]; rw [← div_eq_mul_inv]; rw [div_zpow]

end Alternating

end List

open List

namespace MulOpposite
variable [Monoid M]

/--
lemma `op_list_prod` / 引理 `op_list_prod`

English:
lemma op_list_prod
  statement: forall l : List M, op l.prod = (l.map op).reverse.prod
  proof: by
  intro l; induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.prod_cons]; rw [List.map_cons]; rw [List.reverse_cons']; rw [List.prod_concat]; rw [op_mul]; rw [ih]

中文:
引理 op_list_prod
  结论: 对任意 l : 列表 M, op l.乘积 = (l.map op).reverse.乘积
  证明: by
  intro l; induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.prod_cons]; rw [List.map_cons]; rw [List.reverse_cons']; rw [List.prod_concat]; rw [op_mul]; rw [ih]

Depends on / 依赖: List.map_cons, List.prod_concat, List.prod_cons, List.reverse_cons, map_cons, op_mul, prod_concat, prod_cons, reverse_cons
-/
lemma op_list_prod : forall l : List M, op l.prod = (l.map op).reverse.prod := by
  intro l; induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.prod_cons]; rw [List.map_cons]; rw [List.reverse_cons']; rw [List.prod_concat]; rw [op_mul]; rw [ih]

/--
lemma `unop_list_prod` / 引理 `unop_list_prod`

English:
lemma unop_list_prod
  given: (l : List Mᵐᵒᵖ)
  statement: l.prod.unop = (l.map unop).reverse.prod
  proof: by
  rw [← op_inj]; rw [op_unop]; rw [MulOpposite.op_list_prod]; rw [map_reverse]; rw [map_map]; rw [reverse_reverse]; rw [op_comp_unop]; rw [map_id]

中文:
引理 unop_list_prod
  条件: (l : 列表 Mᵐᵒᵖ)
  结论: l.乘积.unop = (l.map unop).reverse.乘积
  证明: by
  rw [← op_inj]; rw [op_unop]; rw [MulOpposite.op_list_prod]; rw [map_reverse]; rw [map_map]; rw [reverse_reverse]; rw [op_comp_unop]; rw [map_id]

Depends on / 依赖: MulOpposite, MulOpposite.op_list_prod, map_id, map_map, map_reverse, op_comp_unop, op_inj, op_list_prod, op_unop, reverse_reverse
-/
lemma unop_list_prod (l : List Mᵐᵒᵖ) : l.prod.unop = (l.map unop).reverse.prod := by
  rw [← op_inj]; rw [op_unop]; rw [MulOpposite.op_list_prod]; rw [map_reverse]; rw [map_map]; rw [reverse_reverse]; rw [op_comp_unop]; rw [map_id]

end MulOpposite

section MonoidHom
variable [Monoid M] [Monoid N]

/--
lemma `unop_map_list_prod` / 引理 `unop_map_list_prod`

English:
lemma unop_map_list_prod
  statement: {F : Type*} [FunLike F M Nᵐᵒᵖ] [MonoidHomClass F M Nᵐᵒᵖ]
  proof: by
  rw [map_list_prod f l]; rw [MulOpposite.unop_list_prod]; rw [List.map_map]

中文:
引理 unop_map_list_prod
  结论: {F : 类型} [函数状 F M Nᵐᵒᵖ] [幺半群态射类 F M Nᵐᵒᵖ]
  证明: by
  rw [map_list_prod f l]; rw [MulOpposite.unop_list_prod]; rw [List.map_map]

Depends on / 依赖: List.map_map, MulOpposite, MulOpposite.unop_list_prod, map_list_prod, map_map, unop_list_prod
-/
lemma unop_map_list_prod {F : Type*} [FunLike F M Nᵐᵒᵖ] [MonoidHomClass F M Nᵐᵒᵖ]
    (f : F) (l : List M) :
    (f l.prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.prod := by
  rw [map_list_prod f l]; rw [MulOpposite.unop_list_prod]; rw [List.map_map]

end MonoidHom
