/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Divisor Finsets

This file defines sets of divisors of a natural number. This is particularly useful as background
for defining Dirichlet convolution.

## Main Definitions
Let `n : ℕ`. All of the following definitions are in the `Nat` namespace:
* `divisors n` is the `Finset` of natural numbers that divide `n`.
* `properDivisors n` is the `Finset` of natural numbers that divide `n`, other than `n`.
* `divisorsAntidiagonal n` is the `Finset` of pairs `(x,y)` such that `x * y = n`.
* `Perfect n` is true when `n` is positive and the sum of `properDivisors n` is `n`.

## Conventions

Since `0` has infinitely many divisors, none of the definitions in this file make sense for it.
Therefore we adopt the convention that `Nat.divisors 0`, `Nat.properDivisors 0`,
`Nat.divisorsAntidiagonal 0` and `Int.divisorsAntidiag 0` are all `∅`.

## Tags
divisors, perfect numbers

-/

@[expose] public section

open Finset

namespace Nat

variable (n : Nat)

/--
Definition of `divisors` / `divisors` 的定义

English:
definition divisors
  signature: : Finset Nat
  body: {d in Ico 1 (n + 1) | d ∣ n}

中文:
定义 divisors
  签名: : 有限集 自然数
  定义体: {d in Ico 1 (n + 1) | d ∣ n}
-/
def divisors : Finset Nat := {d in Ico 1 (n + 1) | d ∣ n}

/--
Definition of `properDivisors` / `properDivisors` 的定义

English:
definition properDivisors
  signature: : Finset Nat
  body: {d in Ico 1 n | d ∣ n}

中文:
定义 properDivisors
  签名: : 有限集 自然数
  定义体: {d in Ico 1 n | d ∣ n}
-/
def properDivisors : Finset Nat := {d in Ico 1 n | d ∣ n}

/--
Definition of `divisorsAntidiagonal` / `divisorsAntidiagonal` 的定义

English:
definition divisorsAntidiagonal
  signature: : Finset (Nat × Nat)
  body: (Icc 1 n).filterMap (fun x => let y := n / x; if x * y = n then some (x, y) else none)
    fun x₁ x₂ (x, y) hx₁ hx₂ => by aesop

中文:
定义 divisorsAntidiagonal
  签名: : 有限集 (自然数 × 自然数)
  定义体: (Icc 1 n).filterMap (fun x => let y := n / x; if x * y = n then some (x, y) else none)
    fun x₁ x₂ (x, y) hx₁ hx₂ => by aesop

Depends on / 依赖: filterMap
-/
def divisorsAntidiagonal : Finset (Nat × Nat) :=
  (Icc 1 n).filterMap (fun x => let y := n / x; if x * y = n then some (x, y) else none)
    fun x₁ x₂ (x, y) hx₁ hx₂ => by aesop

/--
Definition of `divisorsAntidiagonalList` / `divisorsAntidiagonalList` 的定义

English:
definition divisorsAntidiagonalList
  signature: (n : Nat)
  body: (List.range' 1 n).filterMap
    (fun x => let y := n / x; if x * y = n then some (x, y) else none)

中文:
定义 divisorsAntidiagonalList
  签名: (n : 自然数)
  定义体: (List.range' 1 n).filterMap
    (fun x => let y := n / x; if x * y = n then some (x, y) else none)

Depends on / 依赖: List.range, filterMap
-/
def divisorsAntidiagonalList (n : Nat) : List (Nat × Nat) :=
  (List.range' 1 n).filterMap
    (fun x => let y := n / x; if x * y = n then some (x, y) else none)

variable {n}

@[simp]
/--
theorem `filter_dvd_eq_divisors` / 定理 `filter_dvd_eq_divisors`

English:
theorem filter_dvd_eq_divisors
  given: (h : n != 0)
  statement: {d in range n.succ | d ∣ n} = n.divisors
  proof: by
  ext
  simp only [divisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)

@[simp]

中文:
定理 filter_dvd_eq_divisors
  条件: (h : n != 0)
  结论: {d in range n.succ | d ∣ n} = n.divisors
  证明: by
  ext
  simp only [divisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)

@[simp]

Depends on / 依赖: and_congr_left_iff, bot_lt, divisors, h.bot_lt, iff_and_self, mem_Ico, mem_filter, mem_range, pos_of_dvd_of_pos, succ_le_iff, succ_le_iff.mpr
-/
theorem filter_dvd_eq_divisors (h : n != 0) : {d in range n.succ | d ∣ n} = n.divisors := by
  ext
  simp only [divisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)

@[simp]
/--
theorem `filter_dvd_eq_properDivisors` / 定理 `filter_dvd_eq_properDivisors`

English:
theorem filter_dvd_eq_properDivisors
  given: (h : n != 0)
  statement: {d in range n | d ∣ n} = n.properDivisors
  proof: by
  ext
  simp only [properDivisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)

中文:
定理 filter_dvd_eq_properDivisors
  条件: (h : n != 0)
  结论: {d in range n | d ∣ n} = n.properDivisors
  证明: by
  ext
  simp only [properDivisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)

Depends on / 依赖: and_congr_left_iff, bot_lt, h.bot_lt, iff_and_self, mem_Ico, mem_filter, mem_range, pos_of_dvd_of_pos, properDivisors, succ_le_iff, succ_le_iff.mpr
-/
theorem filter_dvd_eq_properDivisors (h : n != 0) : {d in range n | d ∣ n} = n.properDivisors := by
  ext
  simp only [properDivisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)

/--
theorem `self_notMem_properDivisors` / 定理 `self_notMem_properDivisors`

English:
theorem self_notMem_properDivisors
  statement: n ∉ properDivisors n
  proof: by simp [properDivisors]

@[simp]

中文:
定理 self_notMem_properDivisors
  结论: n ∉ properDivisors n
  证明: by simp [properDivisors]

@[simp]

Depends on / 依赖: properDivisors
-/
theorem self_notMem_properDivisors : n ∉ properDivisors n := by simp [properDivisors]

@[simp]
/--
theorem `mem_properDivisors` / 定理 `mem_properDivisors`

English:
theorem mem_properDivisors
  given: {m : Nat}
  statement: n in properDivisors m ↔ n ∣ m ∧ n < m
  proof: by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [properDivisors]
  simp only [and_comm, ← filter_dvd_eq_properDivisors hm, mem_filter, mem_range]

中文:
定理 mem_properDivisors
  条件: {m : 自然数}
  结论: n in properDivisors m ↔ n ∣ m ∧ n < m
  证明: by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [properDivisors]
  simp only [and_comm, ← filter_dvd_eq_properDivisors hm, mem_filter, mem_range]

Depends on / 依赖: BoundedOrderHomClass, BoundedOrderHomClass.toTopHomClass, and_comm, eq_or_ne, filter_dvd_eq_properDivisors, mem_filter, mem_range, properDivisors, toTopHomClass
-/
theorem mem_properDivisors {m : Nat} : n in properDivisors m ↔ n ∣ m ∧ n < m := by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [properDivisors]
  simp only [and_comm, ← filter_dvd_eq_properDivisors hm, mem_filter, mem_range]

/--
theorem `insert_self_properDivisors` / 定理 `insert_self_properDivisors`

English:
theorem insert_self_properDivisors
  given: (h : n != 0)
  statement: insert n (properDivisors n) = divisors n
  proof: by
  rw [divisors]; rw [properDivisors]; rw [← Finset.insert_Ico_right_eq_Ico_add_one (one_le_iff_ne_zero.2 h)]; rw [Finset.filter_insert]; rw [if_pos (dvd_refl n)]

中文:
定理 insert_self_properDivisors
  条件: (h : n != 0)
  结论: insert n (properDivisors n) = divisors n
  证明: by
  rw [divisors]; rw [properDivisors]; rw [← Finset.insert_Ico_right_eq_Ico_add_one (one_le_iff_ne_zero.2 h)]; rw [Finset.filter_insert]; rw [if_pos (dvd_refl n)]

Depends on / 依赖: Finset, Finset.filter_insert, Finset.insert_Ico_right_eq_Ico_add_one, OrderIsoClass, OrderIsoClass.toTopHomClass, OrderTop, divisors, dvd_refl, filter_insert, if_pos, insert_Ico_right_eq_Ico_add_one, one_le_iff_ne_zero, properDivisors, toTopHomClass
-/
theorem insert_self_properDivisors (h : n != 0) : insert n (properDivisors n) = divisors n := by
  rw [divisors]; rw [properDivisors]; rw [← Finset.insert_Ico_right_eq_Ico_add_one (one_le_iff_ne_zero.2 h)]; rw [Finset.filter_insert]; rw [if_pos (dvd_refl n)]

/--
theorem `cons_self_properDivisors` / 定理 `cons_self_properDivisors`

English:
theorem cons_self_properDivisors
  given: (h : n != 0)
  proof: by
  rw [cons_eq_insert]; rw [insert_self_properDivisors h]

@[simp, grind =]

中文:
定理 cons_self_properDivisors
  条件: (h : n != 0)
  证明: by
  rw [cons_eq_insert]; rw [insert_self_properDivisors h]

@[simp, grind =]

Depends on / 依赖: BoundedOrder, OrderIsoClass, OrderIsoClass.toBoundedOrderHomClass, cons_eq_insert, insert_self_properDivisors, toBoundedOrderHomClass
-/
theorem cons_self_properDivisors (h : n != 0) :
    cons n (properDivisors n) self_notMem_properDivisors = divisors n := by
  rw [cons_eq_insert]; rw [insert_self_properDivisors h]

@[simp, grind =]
/--
theorem `mem_divisors` / 定理 `mem_divisors`

English:
theorem mem_divisors
  given: {m : Nat}
  statement: n in divisors m ↔ n ∣ m ∧ m != 0
  proof: by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [divisors]
  simp only [hm, Ne, not_false_iff, and_true, ← filter_dvd_eq_divisors hm, mem_filter,
    mem_range, and_iff_right_iff_imp, Nat.lt_succ_iff]
  exact le_of_dvd hm.bot_lt

中文:
定理 mem_divisors
  条件: {m : 自然数}
  结论: n in divisors m ↔ n ∣ m ∧ m != 0
  证明: by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [divisors]
  simp only [hm, Ne, not_false_iff, and_true, ← filter_dvd_eq_divisors hm, mem_filter,
    mem_range, and_iff_right_iff_imp, Nat.lt_succ_iff]
  exact le_of_dvd hm.bot_lt

Depends on / 依赖: Nat.lt_succ_iff, and_iff_right_iff_imp, and_true, bot_lt, divisors, eq_or_ne, filter_dvd_eq_divisors, hm.bot_lt, le_of_dvd, lt_succ_iff, mem_filter, mem_range, not_false_iff
-/
theorem mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m != 0 := by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [divisors]
  simp only [hm, Ne, not_false_iff, and_true, ← filter_dvd_eq_divisors hm, mem_filter,
    mem_range, and_iff_right_iff_imp, Nat.lt_succ_iff]
  exact le_of_dvd hm.bot_lt

/--
theorem `dvd_of_mem_divisors` / 定理 `dvd_of_mem_divisors`

English:
theorem dvd_of_mem_divisors
  given: {m : Nat} (h : n in divisors m)
  statement: n ∣ m
  proof: (mem_divisors.mp h).1

中文:
定理 dvd_of_mem_divisors
  条件: {m : 自然数} (h : n in divisors m)
  结论: n ∣ m
  证明: (mem_divisors.mp h).1

Depends on / 依赖: mem_divisors, mem_divisors.mp
-/
theorem dvd_of_mem_divisors {m : Nat} (h : n in divisors m) : n ∣ m := (mem_divisors.mp h).1

/--
theorem `ne_zero_of_mem_divisors` / 定理 `ne_zero_of_mem_divisors`

English:
theorem ne_zero_of_mem_divisors
  given: {m : Nat} (h : n in divisors m)
  statement: m != 0
  proof: (mem_divisors.mp h).2

中文:
定理 ne_zero_of_mem_divisors
  条件: {m : 自然数} (h : n in divisors m)
  结论: m != 0
  证明: (mem_divisors.mp h).2

Depends on / 依赖: mem_divisors, mem_divisors.mp
-/
theorem ne_zero_of_mem_divisors {m : Nat} (h : n in divisors m) : m != 0 := (mem_divisors.mp h).2

/--
theorem `one_mem_divisors` / 定理 `one_mem_divisors`

English:
theorem one_mem_divisors
  statement: 1 in divisors n ↔ n != 0
  proof: by simp

中文:
定理 one_mem_divisors
  结论: 1 in divisors n ↔ n != 0
  证明: by simp
-/
theorem one_mem_divisors : 1 in divisors n ↔ n != 0 := by simp

/--
theorem `mem_divisors_self` / 定理 `mem_divisors_self`

English:
theorem mem_divisors_self
  given: (n : Nat) (h : n != 0)
  statement: n in n.divisors
  proof: mem_divisors.2 ⟨dvd_rfl, h⟩

@[simp]

中文:
定理 mem_divisors_self
  条件: (n : 自然数) (h : n != 0)
  结论: n in n.divisors
  证明: mem_divisors.2 ⟨dvd_rfl, h⟩

@[simp]

Depends on / 依赖: dvd_rfl, mem_divisors
-/
theorem mem_divisors_self (n : Nat) (h : n != 0) : n in n.divisors :=
  mem_divisors.2 ⟨dvd_rfl, h⟩

@[simp]
/--
theorem `mem_divisorsAntidiagonal` / 定理 `mem_divisorsAntidiagonal`

English:
theorem mem_divisorsAntidiagonal
  given: {x : Nat × Nat}
  proof: by
  obtain ⟨a, b⟩ := x
  simp only [divisorsAntidiagonal, mul_div_eq_iff_dvd, mem_filterMap, mem_Icc, one_le_iff_ne_zero,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.ext_iff, and_left_comm, exists_eq_left]
  constructor
  · rintro ⟨han, ⟨ha, han'⟩, rfl⟩
    simp [Nat.mul_div_eq_iff_d

中文:
定理 mem_divisorsAntidiagonal
  条件: {x : 自然数 × 自然数}
  证明: by
  obtain ⟨a, b⟩ := x
  simp only [divisorsAntidiagonal, mul_div_eq_iff_dvd, mem_filterMap, mem_Icc, one_le_iff_ne_zero,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.ext_iff, and_left_comm, exists_eq_left]
  constructor
  · rintro ⟨han, ⟨ha, han'⟩, rfl⟩
    simp [Nat.mul_div_eq_iff_d

Depends on / 依赖: Nat.le_mul_of_pos_right, Nat.mul_div_eq_iff_dvd, Option.ite_none_right_eq_some, Option.some.injEq, Prod.ext_iff, and_left_comm, bot_lt, divisorsAntidiagonal, exists_eq_left, ext_iff, ite_none_right_eq_some, le_mul_of_pos_right, mem_Icc, mem_filterMap, mul_div_eq_iff_dvd, mul_ne_zero_iff, one_le_iff_ne_zero
-/
theorem mem_divisorsAntidiagonal {x : Nat × Nat} :
    x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0 := by
  obtain ⟨a, b⟩ := x
  simp only [divisorsAntidiagonal, mul_div_eq_iff_dvd, mem_filterMap, mem_Icc, one_le_iff_ne_zero,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.ext_iff, and_left_comm, exists_eq_left]
  constructor
  · rintro ⟨han, ⟨ha, han'⟩, rfl⟩
    simp [Nat.mul_div_eq_iff_dvd, han]
    lia
  · rintro ⟨rfl, hab⟩
    rw [mul_ne_zero_iff] at hab
    simpa [hab.1, hab.2] using Nat.le_mul_of_pos_right _ hab.2.bot_lt

/--
lemma `divisorsAntidiagonalList_zero` / 引理 `divisorsAntidiagonalList_zero`

English:
lemma divisorsAntidiagonalList_zero
  statement: divisorsAntidiagonalList 0 = []
  proof: rfl

中文:
引理 divisorsAntidiagonalList_zero
  结论: divisorsAntidiagonalList 0 = []
  证明: rfl
-/
@[simp] lemma divisorsAntidiagonalList_zero : divisorsAntidiagonalList 0 = [] := rfl
/--
lemma `divisorsAntidiagonalList_one` / 引理 `divisorsAntidiagonalList_one`

English:
lemma divisorsAntidiagonalList_one
  statement: divisorsAntidiagonalList 1 = [(1, 1)]
  proof: rfl

@[simp]

中文:
引理 divisorsAntidiagonalList_one
  结论: divisorsAntidiagonalList 1 = [(1, 1)]
  证明: rfl

@[simp]
-/
@[simp] lemma divisorsAntidiagonalList_one : divisorsAntidiagonalList 1 = [(1, 1)] := rfl

@[simp]
/--
lemma `toFinset_divisorsAntidiagonalList` / 引理 `toFinset_divisorsAntidiagonalList`

English:
lemma toFinset_divisorsAntidiagonalList
  given: {n : Nat}
  proof: by
  rw [divisorsAntidiagonalList]; rw [divisorsAntidiagonal]; rw [List.toFinset_filterMap
    (f_inj := by simp_all)]; rw [List.toFinset_range'_1_1]

中文:
引理 toFinset_divisorsAntidiagonalList
  条件: {n : 自然数}
  证明: by
  rw [divisorsAntidiagonalList]; rw [divisorsAntidiagonal]; rw [List.toFinset_filterMap
    (f_inj := by simp_all)]; rw [List.toFinset_range'_1_1]

Depends on / 依赖: List.toFinset_filterMap, List.toFinset_range, _1_1, divisorsAntidiagonal, divisorsAntidiagonalList, f_inj, toFinset_filterMap, toFinset_range
-/
lemma toFinset_divisorsAntidiagonalList {n : Nat} :
    n.divisorsAntidiagonalList.toFinset = n.divisorsAntidiagonal := by
  rw [divisorsAntidiagonalList]; rw [divisorsAntidiagonal]; rw [List.toFinset_filterMap
    (f_inj := by simp_all)]; rw [List.toFinset_range'_1_1]

/--
lemma `pairwise_divisorsAntidiagonalList_fst` / 引理 `pairwise_divisorsAntidiagonalList_fst`

English:
lemma pairwise_divisorsAntidiagonalList_fst
  given: {n : Nat}
  proof: by
  refine (List.sortedLT_range' _ _ Nat.one_ne_zero).pairwise.filterMap _ fun a b c d h ha h' => ?_
  rw [Option.ite_none_right_eq_some]; rw [Option.some.injEq] at h h'
  simpa [← h.right, ← h'.right]

中文:
引理 pairwise_divisorsAntidiagonalList_fst
  条件: {n : 自然数}
  证明: by
  refine (List.sortedLT_range' _ _ Nat.one_ne_zero).pairwise.filterMap _ fun a b c d h ha h' => ?_
  rw [Option.ite_none_right_eq_some]; rw [Option.some.injEq] at h h'
  simpa [← h.right, ← h'.right]

Depends on / 依赖: List.sortedLT_range, Nat.one_ne_zero, Option.ite_none_right_eq_some, Option.some.injEq, filterMap, h.right, ite_none_right_eq_some, one_ne_zero, pairwise, pairwise.filterMap, sortedLT_range
-/
lemma pairwise_divisorsAntidiagonalList_fst {n : Nat} :
    n.divisorsAntidiagonalList.Pairwise (·.fst < ·.fst) := by
  refine (List.sortedLT_range' _ _ Nat.one_ne_zero).pairwise.filterMap _ fun a b c d h ha h' => ?_
  rw [Option.ite_none_right_eq_some]; rw [Option.some.injEq] at h h'
  simpa [← h.right, ← h'.right]

/--
lemma `pairwise_divisorsAntidiagonalList_snd` / 引理 `pairwise_divisorsAntidiagonalList_snd`

English:
lemma pairwise_divisorsAntidiagonalList_snd
  given: {n : Nat}
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  refine (List.sortedLT_range' _ _ Nat.one_ne_zero).pairwise.filterMap _ ?_
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, gt_iff_lt,
    and_imp, Prod.forall, Prod.mk.injEq]
  rintro a b hab _ _ ha rfl rfl _ _ hb rfl rfl
  rwa [Nat.div_l

中文:
引理 pairwise_divisorsAntidiagonalList_snd
  条件: {n : 自然数}
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  refine (List.sortedLT_range' _ _ Nat.one_ne_zero).pairwise.filterMap _ ?_
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, gt_iff_lt,
    and_imp, Prod.forall, Prod.mk.injEq]
  rintro a b hab _ _ ha rfl rfl _ _ hb rfl rfl
  rwa [Nat.div_l

Depends on / 依赖: List.sortedLT_range, Nat.div_lt_div_left, Nat.one_ne_zero, Option.ite_none_right_eq_some, Option.some.injEq, Prod.forall, Prod.mk.injEq, and_imp, div_lt_div_left, eq_or_ne, filterMap, gt_iff_lt, ha.symm, hb.symm, ite_none_right_eq_some, one_ne_zero, pairwise, pairwise.filterMap, sortedLT_range
-/
lemma pairwise_divisorsAntidiagonalList_snd {n : Nat} :
    n.divisorsAntidiagonalList.Pairwise (·.snd > ·.snd) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  refine (List.sortedLT_range' _ _ Nat.one_ne_zero).pairwise.filterMap _ ?_
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, gt_iff_lt,
    and_imp, Prod.forall, Prod.mk.injEq]
  rintro a b hab _ _ ha rfl rfl _ _ hb rfl rfl
  rwa [Nat.div_lt_div_left hn ⟨_, hb.symm⟩ ⟨_, ha.symm⟩]

/--
lemma `sortedLT_map_fst_divisorsAntidiagonalList` / 引理 `sortedLT_map_fst_divisorsAntidiagonalList`

English:
lemma sortedLT_map_fst_divisorsAntidiagonalList
  given: {n : Nat}
  proof: (List.pairwise_map.mpr <| pairwise_divisorsAntidiagonalList_fst).sortedLT

中文:
引理 sortedLT_map_fst_divisorsAntidiagonalList
  条件: {n : 自然数}
  证明: (List.pairwise_map.mpr <| pairwise_divisorsAntidiagonalList_fst).sortedLT

Depends on / 依赖: List.pairwise_map.mpr, pairwise_divisorsAntidiagonalList_fst, pairwise_map, sortedLT
-/
lemma sortedLT_map_fst_divisorsAntidiagonalList {n : Nat} :
    (n.divisorsAntidiagonalList.map Prod.fst).SortedLT :=
  (List.pairwise_map.mpr <| pairwise_divisorsAntidiagonalList_fst).sortedLT

/--
lemma `sortedGT_map_snd_divisorsAntidiagonalList` / 引理 `sortedGT_map_snd_divisorsAntidiagonalList`

English:
lemma sortedGT_map_snd_divisorsAntidiagonalList
  given: {n : Nat}
  proof: (List.pairwise_map.mpr <| pairwise_divisorsAntidiagonalList_snd).sortedGT

中文:
引理 sortedGT_map_snd_divisorsAntidiagonalList
  条件: {n : 自然数}
  证明: (List.pairwise_map.mpr <| pairwise_divisorsAntidiagonalList_snd).sortedGT

Depends on / 依赖: List.pairwise_map.mpr, pairwise_divisorsAntidiagonalList_snd, pairwise_map, sortedGT
-/
lemma sortedGT_map_snd_divisorsAntidiagonalList {n : Nat} :
    (n.divisorsAntidiagonalList.map Prod.snd).SortedGT :=
  (List.pairwise_map.mpr <| pairwise_divisorsAntidiagonalList_snd).sortedGT

/--
lemma `nodup_divisorsAntidiagonalList` / 引理 `nodup_divisorsAntidiagonalList`

English:
lemma nodup_divisorsAntidiagonalList
  given: {n : Nat}
  statement: n.divisorsAntidiagonalList.Nodup
  proof: have : @Std.Irrefl (Nat × Nat) (·.fst < ·.fst) := ⟨by simp⟩
  pairwise_divisorsAntidiagonalList_fst.nodup

中文:
引理 nodup_divisorsAntidiagonalList
  条件: {n : 自然数}
  结论: n.divisorsAntidiagonalList.Nodup
  证明: have : @Std.Irrefl (Nat × Nat) (·.fst < ·.fst) := ⟨by simp⟩
  pairwise_divisorsAntidiagonalList_fst.nodup

Depends on / 依赖: Irrefl, Std.Irrefl, pairwise_divisorsAntidiagonalList_fst, pairwise_divisorsAntidiagonalList_fst.nodup
-/
lemma nodup_divisorsAntidiagonalList {n : Nat} : n.divisorsAntidiagonalList.Nodup :=
  have : @Std.Irrefl (Nat × Nat) (·.fst < ·.fst) := ⟨by simp⟩
  pairwise_divisorsAntidiagonalList_fst.nodup

/-- The `Finset` and `List` versions agree by definition. -/
@[simp]
/--
theorem `val_divisorsAntidiagonal` / 定理 `val_divisorsAntidiagonal`

English:
theorem val_divisorsAntidiagonal
  given: (n : Nat)
  proof: rfl

@[simp]

中文:
定理 val_divisorsAntidiagonal
  条件: (n : 自然数)
  证明: rfl

@[simp]
-/
theorem val_divisorsAntidiagonal (n : Nat) :
    (divisorsAntidiagonal n).val = divisorsAntidiagonalList n :=
  rfl

@[simp]
/--
lemma `mem_divisorsAntidiagonalList` / 引理 `mem_divisorsAntidiagonalList`

English:
lemma mem_divisorsAntidiagonalList
  given: {n : Nat} {a : Nat × Nat}
  proof: by
  rw [← List.mem_toFinset]; rw [toFinset_divisorsAntidiagonalList]; rw [mem_divisorsAntidiagonal]

@[simp high]

中文:
引理 mem_divisorsAntidiagonalList
  条件: {n : 自然数} {a : 自然数 × 自然数}
  证明: by
  rw [← List.mem_toFinset]; rw [toFinset_divisorsAntidiagonalList]; rw [mem_divisorsAntidiagonal]

@[simp high]

Depends on / 依赖: List.mem_toFinset, mem_divisorsAntidiagonal, mem_toFinset, toFinset_divisorsAntidiagonalList
-/
lemma mem_divisorsAntidiagonalList {n : Nat} {a : Nat × Nat} :
    a in n.divisorsAntidiagonalList ↔ a.1 * a.2 = n ∧ n != 0 := by
  rw [← List.mem_toFinset]; rw [toFinset_divisorsAntidiagonalList]; rw [mem_divisorsAntidiagonal]

@[simp high]
/--
lemma `swap_mem_divisorsAntidiagonalList` / 引理 `swap_mem_divisorsAntidiagonalList`

English:
lemma swap_mem_divisorsAntidiagonalList
  given: {a : Nat × Nat}
  proof: by simp [mul_comm]

中文:
引理 swap_mem_divisorsAntidiagonalList
  条件: {a : 自然数 × 自然数}
  证明: by simp [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma swap_mem_divisorsAntidiagonalList {a : Nat × Nat} :
    a.swap in n.divisorsAntidiagonalList ↔ a in n.divisorsAntidiagonalList := by simp [mul_comm]

/--
lemma `reverse_divisorsAntidiagonalList` / 引理 `reverse_divisorsAntidiagonalList`

English:
lemma reverse_divisorsAntidiagonalList
  given: (n : Nat)
  proof: by
  have : Std.Asymm (α := Nat × Nat) (·.snd < ·.snd) := ⟨fun _ _ => lt_asymm⟩
  refine List.Perm.eq_of_pairwise' pairwise_divisorsAntidiagonalList_snd.reverse
    (pairwise_divisorsAntidiagonalList_fst.map _ fun _ _ => id) ?_
  simp [List.reverse_perm', List.perm_ext_iff_of_nodup nodup_divisorsAnt

中文:
引理 reverse_divisorsAntidiagonalList
  条件: (n : 自然数)
  证明: by
  have : Std.Asymm (α := Nat × Nat) (·.snd < ·.snd) := ⟨fun _ _ => lt_asymm⟩
  refine List.Perm.eq_of_pairwise' pairwise_divisorsAntidiagonalList_snd.reverse
    (pairwise_divisorsAntidiagonalList_fst.map _ fun _ _ => id) ?_
  simp [List.reverse_perm', List.perm_ext_iff_of_nodup nodup_divisorsAnt

Depends on / 依赖: List.Perm.eq_of_pairwise, List.perm_ext_iff_of_nodup, List.reverse_perm, Prod.swap_injective, Std.Asymm, eq_of_pairwise, lt_asymm, mul_comm, nodup_divisorsAntidiagonalList, nodup_divisorsAntidiagonalList.map, pairwise_divisorsAntidiagonalList_fst, pairwise_divisorsAntidiagonalList_fst.map, pairwise_divisorsAntidiagonalList_snd, pairwise_divisorsAntidiagonalList_snd.reverse, perm_ext_iff_of_nodup, reverse, reverse_perm, swap_injective
-/
lemma reverse_divisorsAntidiagonalList (n : Nat) :
    n.divisorsAntidiagonalList.reverse = n.divisorsAntidiagonalList.map .swap := by
  have : Std.Asymm (α := Nat × Nat) (·.snd < ·.snd) := ⟨fun _ _ => lt_asymm⟩
  refine List.Perm.eq_of_pairwise' pairwise_divisorsAntidiagonalList_snd.reverse
    (pairwise_divisorsAntidiagonalList_fst.map _ fun _ _ => id) ?_
  simp [List.reverse_perm', List.perm_ext_iff_of_nodup nodup_divisorsAntidiagonalList
    (nodup_divisorsAntidiagonalList.map Prod.swap_injective), mul_comm]

/--
lemma `ne_zero_of_mem_divisorsAntidiagonal` / 引理 `ne_zero_of_mem_divisorsAntidiagonal`

English:
lemma ne_zero_of_mem_divisorsAntidiagonal
  given: {p : Nat × Nat} (hp : p in n.divisorsAntidiagonal)
  proof: by
  obtain ⟨hp₁, hp₂⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  exact mul_ne_zero_iff.mp (hp₁.symm ▸ hp₂)

中文:
引理 ne_zero_of_mem_divisorsAntidiagonal
  条件: {p : 自然数 × 自然数} (hp : p in n.divisorsAntidiagonal)
  证明: by
  obtain ⟨hp₁, hp₂⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  exact mul_ne_zero_iff.mp (hp₁.symm ▸ hp₂)

Depends on / 依赖: Nat.mem_divisorsAntidiagonal.mp, mem_divisorsAntidiagonal, mul_ne_zero_iff, mul_ne_zero_iff.mp
-/
lemma ne_zero_of_mem_divisorsAntidiagonal {p : Nat × Nat} (hp : p in n.divisorsAntidiagonal) :
    p.1 != 0 ∧ p.2 != 0 := by
  obtain ⟨hp₁, hp₂⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  exact mul_ne_zero_iff.mp (hp₁.symm ▸ hp₂)

/--
lemma `left_ne_zero_of_mem_divisorsAntidiagonal` / 引理 `left_ne_zero_of_mem_divisorsAntidiagonal`

English:
lemma left_ne_zero_of_mem_divisorsAntidiagonal
  given: {p : Nat × Nat} (hp : p in n.divisorsAntidiagonal)
  proof: (ne_zero_of_mem_divisorsAntidiagonal hp).1

中文:
引理 left_ne_zero_of_mem_divisorsAntidiagonal
  条件: {p : 自然数 × 自然数} (hp : p in n.divisorsAntidiagonal)
  证明: (ne_zero_of_mem_divisorsAntidiagonal hp).1

Depends on / 依赖: ne_zero_of_mem_divisorsAntidiagonal
-/
lemma left_ne_zero_of_mem_divisorsAntidiagonal {p : Nat × Nat} (hp : p in n.divisorsAntidiagonal) :
    p.1 != 0 :=
  (ne_zero_of_mem_divisorsAntidiagonal hp).1

/--
lemma `right_ne_zero_of_mem_divisorsAntidiagonal` / 引理 `right_ne_zero_of_mem_divisorsAntidiagonal`

English:
lemma right_ne_zero_of_mem_divisorsAntidiagonal
  given: {p : Nat × Nat} (hp : p in n.divisorsAntidiagonal)
  proof: (ne_zero_of_mem_divisorsAntidiagonal hp).2

中文:
引理 right_ne_zero_of_mem_divisorsAntidiagonal
  条件: {p : 自然数 × 自然数} (hp : p in n.divisorsAntidiagonal)
  证明: (ne_zero_of_mem_divisorsAntidiagonal hp).2

Depends on / 依赖: ne_zero_of_mem_divisorsAntidiagonal
-/
lemma right_ne_zero_of_mem_divisorsAntidiagonal {p : Nat × Nat} (hp : p in n.divisorsAntidiagonal) :
    p.2 != 0 :=
  (ne_zero_of_mem_divisorsAntidiagonal hp).2

/--
theorem `divisor_le` / 定理 `divisor_le`

English:
theorem divisor_le
  given: {m : Nat}
  statement: n in divisors m -> n <= m
  proof: by
  rcases m with - | m
  · simp
  · simp only [mem_divisors, Nat.succ_ne_zero m, and_true, Ne, not_false_iff]
    exact Nat.le_of_dvd (Nat.succ_pos m)

@[gcongr]

中文:
定理 divisor_le
  条件: {m : 自然数}
  结论: n in divisors m -> n <= m
  证明: by
  rcases m with - | m
  · simp
  · simp only [mem_divisors, Nat.succ_ne_zero m, and_true, Ne, not_false_iff]
    exact Nat.le_of_dvd (Nat.succ_pos m)

@[gcongr]

Depends on / 依赖: Nat.le_of_dvd, Nat.succ_ne_zero, Nat.succ_pos, and_true, le_of_dvd, mem_divisors, not_false_iff, succ_ne_zero, succ_pos
-/
theorem divisor_le {m : Nat} : n in divisors m -> n <= m := by
  rcases m with - | m
  · simp
  · simp only [mem_divisors, Nat.succ_ne_zero m, and_true, Ne, not_false_iff]
    exact Nat.le_of_dvd (Nat.succ_pos m)

@[gcongr]
/--
theorem `divisors_subset_of_dvd` / 定理 `divisors_subset_of_dvd`

English:
theorem divisors_subset_of_dvd
  given: {m : Nat} (hzero : n != 0) (h : m ∣ n)
  statement: divisors m subseteq divisors n
  proof: Finset.subset_iff.2 fun _x hx => Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hx).1.trans h, hzero⟩

中文:
定理 divisors_subset_of_dvd
  条件: {m : 自然数} (hzero : n != 0) (h : m ∣ n)
  结论: divisors m subseteq divisors n
  证明: Finset.subset_iff.2 fun _x hx => Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hx).1.trans h, hzero⟩

Depends on / 依赖: Finset, Finset.subset_iff, Nat.mem_divisors.mp, Nat.mem_divisors.mpr, mem_divisors, subset_iff
-/
theorem divisors_subset_of_dvd {m : Nat} (hzero : n != 0) (h : m ∣ n) : divisors m subseteq divisors n :=
  Finset.subset_iff.2 fun _x hx => Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hx).1.trans h, hzero⟩

/--
theorem `card_divisors_le_self` / 定理 `card_divisors_le_self`

English:
theorem card_divisors_le_self
  given: (n : Nat)
  statement: #n.divisors <= n
  proof: calc
  _ <= #(Ico 1 (n + 1)) := by
    apply card_le_card
    simp only [divisors, filter_subset]
  _ = n := by rw [card_Ico, add_tsub_cancel_right]

中文:
定理 card_divisors_le_self
  条件: (n : 自然数)
  结论: #n.divisors <= n
  证明: calc
  _ <= #(Ico 1 (n + 1)) := by
    apply card_le_card
    simp only [divisors, filter_subset]
  _ = n := by rw [card_Ico, add_tsub_cancel_right]
-/
theorem card_divisors_le_self (n : Nat) : #n.divisors <= n := calc
  _ <= #(Ico 1 (n + 1)) := by
    apply card_le_card
    simp only [divisors, filter_subset]
  _ = n := by rw [card_Ico, add_tsub_cancel_right]

/--
theorem `divisors_subset_properDivisors` / 定理 `divisors_subset_properDivisors`

English:
theorem divisors_subset_properDivisors
  given: {m : Nat} (hzero : n != 0) (h : m ∣ n) (hdiff : m != n)
  proof: by
  apply Finset.subset_iff.2
  intro x hx
  exact
    Nat.mem_properDivisors.2
      ⟨(Nat.mem_divisors.1 hx).1.trans h,
        lt_of_le_of_lt (divisor_le hx)
          (lt_of_le_of_ne (divisor_le (Nat.mem_divisors.2 ⟨h, hzero⟩)) hdiff)⟩

中文:
定理 divisors_subset_properDivisors
  条件: {m : 自然数} (hzero : n != 0) (h : m ∣ n) (hdiff : m != n)
  证明: by
  apply Finset.subset_iff.2
  intro x hx
  exact
    Nat.mem_properDivisors.2
      ⟨(Nat.mem_divisors.1 hx).1.trans h,
        lt_of_le_of_lt (divisor_le hx)
          (lt_of_le_of_ne (divisor_le (Nat.mem_divisors.2 ⟨h, hzero⟩)) hdiff)⟩

Depends on / 依赖: Finset, Finset.subset_iff, Nat.mem_divisors, Nat.mem_properDivisors, divisor_le, lt_of_le_of_lt, lt_of_le_of_ne, mem_divisors, mem_properDivisors, subset_iff
-/
theorem divisors_subset_properDivisors {m : Nat} (hzero : n != 0) (h : m ∣ n) (hdiff : m != n) :
    divisors m subseteq properDivisors n := by
  apply Finset.subset_iff.2
  intro x hx
  exact
    Nat.mem_properDivisors.2
      ⟨(Nat.mem_divisors.1 hx).1.trans h,
        lt_of_le_of_lt (divisor_le hx)
          (lt_of_le_of_ne (divisor_le (Nat.mem_divisors.2 ⟨h, hzero⟩)) hdiff)⟩

/--
lemma `divisors_filter_dvd_of_dvd` / 引理 `divisors_filter_dvd_of_dvd`

English:
lemma divisors_filter_dvd_of_dvd
  given: {n m : Nat} (hn : n != 0) (hm : m ∣ n)
  proof: by
  ext k
  simp_rw [mem_filter, mem_divisors]
  exact ⟨fun ⟨_, hkm⟩ => ⟨hkm, ne_zero_of_dvd_ne_zero hn hm⟩, fun ⟨hk, _⟩ => ⟨⟨hk.trans hm, hn⟩, hk⟩⟩

@[simp]

中文:
引理 divisors_filter_dvd_of_dvd
  条件: {n m : 自然数} (hn : n != 0) (hm : m ∣ n)
  证明: by
  ext k
  simp_rw [mem_filter, mem_divisors]
  exact ⟨fun ⟨_, hkm⟩ => ⟨hkm, ne_zero_of_dvd_ne_zero hn hm⟩, fun ⟨hk, _⟩ => ⟨⟨hk.trans hm, hn⟩, hk⟩⟩

@[simp]

Depends on / 依赖: hk.trans, mem_divisors, mem_filter, ne_zero_of_dvd_ne_zero, simp_rw
-/
lemma divisors_filter_dvd_of_dvd {n m : Nat} (hn : n != 0) (hm : m ∣ n) :
    {d in n.divisors | d ∣ m} = m.divisors := by
  ext k
  simp_rw [mem_filter, mem_divisors]
  exact ⟨fun ⟨_, hkm⟩ => ⟨hkm, ne_zero_of_dvd_ne_zero hn hm⟩, fun ⟨hk, _⟩ => ⟨⟨hk.trans hm, hn⟩, hk⟩⟩

@[simp]
/--
theorem `divisors_zero` / 定理 `divisors_zero`

English:
theorem divisors_zero
  statement: divisors 0 = ∅
  proof: by
  ext
  simp

@[simp]

中文:
定理 divisors_zero
  结论: divisors 0 = ∅
  证明: by
  ext
  simp

@[simp]
-/
theorem divisors_zero : divisors 0 = ∅ := by
  ext
  simp

@[simp]
/--
theorem `properDivisors_zero` / 定理 `properDivisors_zero`

English:
theorem properDivisors_zero
  statement: properDivisors 0 = ∅
  proof: by
  ext
  simp

@[simp]

中文:
定理 properDivisors_zero
  结论: properDivisors 0 = ∅
  证明: by
  ext
  simp

@[simp]
-/
theorem properDivisors_zero : properDivisors 0 = ∅ := by
  ext
  simp

@[simp]
/--
lemma `nonempty_divisors` / 引理 `nonempty_divisors`

English:
lemma nonempty_divisors
  statement: (divisors n).Nonempty ↔ n != 0
  proof: ⟨fun ⟨m, hm⟩ hn => by simp [hn] at hm, fun hn => ⟨1, one_mem_divisors.2 hn⟩⟩

@[simp]

中文:
引理 nonempty_divisors
  结论: (divisors n).非空 ↔ n != 0
  证明: ⟨fun ⟨m, hm⟩ hn => by simp [hn] at hm, fun hn => ⟨1, one_mem_divisors.2 hn⟩⟩

@[simp]

Depends on / 依赖: one_mem_divisors
-/
lemma nonempty_divisors : (divisors n).Nonempty ↔ n != 0 :=
  ⟨fun ⟨m, hm⟩ hn => by simp [hn] at hm, fun hn => ⟨1, one_mem_divisors.2 hn⟩⟩

@[simp]
/--
lemma `divisors_eq_empty` / 引理 `divisors_eq_empty`

English:
lemma divisors_eq_empty
  statement: divisors n = ∅ ↔ n = 0
  proof: by
  contrapose!
  exact nonempty_divisors

中文:
引理 divisors_eq_empty
  结论: divisors n = ∅ ↔ n = 0
  证明: by
  contrapose!
  exact nonempty_divisors

Depends on / 依赖: contrapose, nonempty_divisors
-/
lemma divisors_eq_empty : divisors n = ∅ ↔ n = 0 := by
  contrapose!
  exact nonempty_divisors

/--
theorem `properDivisors_subset_divisors` / 定理 `properDivisors_subset_divisors`

English:
theorem properDivisors_subset_divisors
  statement: properDivisors n subseteq divisors n
  proof: filter_subset_filter _ Ico_subset_Ico_right n.le_succ

@[simp]

中文:
定理 properDivisors_subset_divisors
  结论: properDivisors n subseteq divisors n
  证明: filter_subset_filter _ Ico_subset_Ico_right n.le_succ

@[simp]

Depends on / 依赖: Ico_subset_Ico_right, filter_subset_filter, le_succ, n.le_succ
-/
theorem properDivisors_subset_divisors : properDivisors n subseteq divisors n :=
filter_subset_filter _ Ico_subset_Ico_right n.le_succ

@[simp]
/--
theorem `divisors_one` / 定理 `divisors_one`

English:
theorem divisors_one
  statement: divisors 1 = {1}
  proof: by
  ext
  simp

@[simp]

中文:
定理 divisors_one
  结论: divisors 1 = {1}
  证明: by
  ext
  simp

@[simp]
-/
theorem divisors_one : divisors 1 = {1} := by
  ext
  simp

@[simp]
/--
theorem `properDivisors_one` / 定理 `properDivisors_one`

English:
theorem properDivisors_one
  statement: properDivisors 1 = ∅
  proof: by rw [properDivisors, Ico_self, filter_empty]

中文:
定理 properDivisors_one
  结论: properDivisors 1 = ∅
  证明: by rw [properDivisors, Ico_self, filter_empty]

Depends on / 依赖: Ico_self, filter_empty, properDivisors
-/
theorem properDivisors_one : properDivisors 1 = ∅ := by rw [properDivisors, Ico_self, filter_empty]

/--
theorem `pos_of_mem_divisors` / 定理 `pos_of_mem_divisors`

English:
theorem pos_of_mem_divisors
  given: {m : Nat} (h : m in n.divisors)
  statement: 0 < m
  proof: by
  cases m
  · rw [mem_divisors, zero_dvd_iff (a := n)] at h
    cases h.2 h.1
  apply Nat.succ_pos

中文:
定理 pos_of_mem_divisors
  条件: {m : 自然数} (h : m in n.divisors)
  结论: 0 < m
  证明: by
  cases m
  · rw [mem_divisors, zero_dvd_iff (a := n)] at h
    cases h.2 h.1
  apply Nat.succ_pos

Depends on / 依赖: Nat.succ_pos, mem_divisors, succ_pos, zero_dvd_iff
-/
theorem pos_of_mem_divisors {m : Nat} (h : m in n.divisors) : 0 < m := by
  cases m
  · rw [mem_divisors, zero_dvd_iff (a := n)] at h
    cases h.2 h.1
  apply Nat.succ_pos

/--
theorem `pos_of_mem_properDivisors` / 定理 `pos_of_mem_properDivisors`

English:
theorem pos_of_mem_properDivisors
  given: {m : Nat} (h : m in n.properDivisors)
  statement: 0 < m
  proof: pos_of_mem_divisors (properDivisors_subset_divisors h)

中文:
定理 pos_of_mem_properDivisors
  条件: {m : 自然数} (h : m in n.properDivisors)
  结论: 0 < m
  证明: pos_of_mem_divisors (properDivisors_subset_divisors h)

Depends on / 依赖: pos_of_mem_divisors, properDivisors_subset_divisors
-/
theorem pos_of_mem_properDivisors {m : Nat} (h : m in n.properDivisors) : 0 < m :=
  pos_of_mem_divisors (properDivisors_subset_divisors h)

/--
theorem `one_mem_properDivisors_iff_one_lt` / 定理 `one_mem_properDivisors_iff_one_lt`

English:
theorem one_mem_properDivisors_iff_one_lt
  statement: 1 in n.properDivisors ↔ 1 < n
  proof: by
  rw [mem_properDivisors]; rw [and_iff_right (one_dvd _)]

@[simp]

中文:
定理 one_mem_properDivisors_iff_one_lt
  结论: 1 in n.properDivisors ↔ 1 < n
  证明: by
  rw [mem_properDivisors]; rw [and_iff_right (one_dvd _)]

@[simp]

Depends on / 依赖: and_iff_right, mem_properDivisors, one_dvd
-/
theorem one_mem_properDivisors_iff_one_lt : 1 in n.properDivisors ↔ 1 < n := by
  rw [mem_properDivisors]; rw [and_iff_right (one_dvd _)]

@[simp]
/--
lemma `sup_divisors_id` / 引理 `sup_divisors_id`

English:
lemma sup_divisors_id
  given: (n : Nat)
  statement: n.divisors.sup id = n
  proof: by
  refine le_antisymm (Finset.sup_le fun _ => divisor_le) ?_
  rcases Decidable.eq_or_ne n 0 with rfl | hn
  · apply zero_le
· exact Finset.le_sup (f := id) mem_divisors_self n hn

中文:
引理 sup_divisors_id
  条件: (n : 自然数)
  结论: n.divisors.上确界 id = n
  证明: by
  refine le_antisymm (Finset.sup_le fun _ => divisor_le) ?_
  rcases Decidable.eq_or_ne n 0 with rfl | hn
  · apply zero_le
· exact Finset.le_sup (f := id) mem_divisors_self n hn

Depends on / 依赖: Decidable, Decidable.eq_or_ne, Finset, Finset.le_sup, Finset.sup_le, divisor_le, eq_or_ne, le_antisymm, le_sup, mem_divisors_self, sup_le, zero_le
-/
lemma sup_divisors_id (n : Nat) : n.divisors.sup id = n := by
  refine le_antisymm (Finset.sup_le fun _ => divisor_le) ?_
  rcases Decidable.eq_or_ne n 0 with rfl | hn
  · apply zero_le
· exact Finset.le_sup (f := id) mem_divisors_self n hn

/--
lemma `one_lt_of_mem_properDivisors` / 引理 `one_lt_of_mem_properDivisors`

English:
lemma one_lt_of_mem_properDivisors
  given: {m n : Nat} (h : m in n.properDivisors)
  statement: 1 < n
  proof: lt_of_le_of_lt (pos_of_mem_properDivisors h) (mem_properDivisors.1 h).2

中文:
引理 one_lt_of_mem_properDivisors
  条件: {m n : 自然数} (h : m in n.properDivisors)
  结论: 1 < n
  证明: lt_of_le_of_lt (pos_of_mem_properDivisors h) (mem_properDivisors.1 h).2

Depends on / 依赖: lt_of_le_of_lt, mem_properDivisors, pos_of_mem_properDivisors
-/
lemma one_lt_of_mem_properDivisors {m n : Nat} (h : m in n.properDivisors) : 1 < n :=
  lt_of_le_of_lt (pos_of_mem_properDivisors h) (mem_properDivisors.1 h).2

/--
lemma `one_lt_div_of_mem_properDivisors` / 引理 `one_lt_div_of_mem_properDivisors`

English:
lemma one_lt_div_of_mem_properDivisors
  given: {m n : Nat} (h : m in n.properDivisors)
  proof: by
  obtain ⟨h_dvd, h_lt⟩ := mem_properDivisors.mp h
  rwa [Nat.lt_div_iff_mul_lt' h_dvd, mul_one]

中文:
引理 one_lt_div_of_mem_properDivisors
  条件: {m n : 自然数} (h : m in n.properDivisors)
  证明: by
  obtain ⟨h_dvd, h_lt⟩ := mem_properDivisors.mp h
  rwa [Nat.lt_div_iff_mul_lt' h_dvd, mul_one]

Depends on / 依赖: Nat.lt_div_iff_mul_lt, h_dvd, h_lt, lt_div_iff_mul_lt, mem_properDivisors, mem_properDivisors.mp, mul_one
-/
lemma one_lt_div_of_mem_properDivisors {m n : Nat} (h : m in n.properDivisors) :
    1 < n / m := by
  obtain ⟨h_dvd, h_lt⟩ := mem_properDivisors.mp h
  rwa [Nat.lt_div_iff_mul_lt' h_dvd, mul_one]

/--
lemma `mem_properDivisors_iff_exists` / 引理 `mem_properDivisors_iff_exists`

English:
lemma mem_properDivisors_iff_exists
  given: {m n : Nat} (hn : n != 0)
  proof: by
  refine ⟨fun h => ⟨n / m, one_lt_div_of_mem_properDivisors h, ?_⟩, ?_⟩
  · exact (Nat.mul_div_cancel' (mem_properDivisors.mp h).1).symm
  · rintro ⟨k, hk, rfl⟩
    rw [mul_ne_zero_iff] at hn
    exact mem_properDivisors.mpr ⟨⟨k, rfl⟩, lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hn.1) hk⟩

@[simp]

中文:
引理 mem_properDivisors_iff_存在
  条件: {m n : 自然数} (hn : n != 0)
  证明: by
  refine ⟨fun h => ⟨n / m, one_lt_div_of_mem_properDivisors h, ?_⟩, ?_⟩
  · exact (Nat.mul_div_cancel' (mem_properDivisors.mp h).1).symm
  · rintro ⟨k, hk, rfl⟩
    rw [mul_ne_zero_iff] at hn
    exact mem_properDivisors.mpr ⟨⟨k, rfl⟩, lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hn.1) hk⟩

@[simp]

Depends on / 依赖: Nat.mul_div_cancel, Nat.pos_of_ne_zero, lt_mul_of_one_lt_right, mem_properDivisors, mem_properDivisors.mp, mem_properDivisors.mpr, mul_div_cancel, mul_ne_zero_iff, one_lt_div_of_mem_properDivisors, pos_of_ne_zero
-/
lemma mem_properDivisors_iff_exists {m n : Nat} (hn : n != 0) :
    m in n.properDivisors ↔ exists k > 1, n = m * k := by
  refine ⟨fun h => ⟨n / m, one_lt_div_of_mem_properDivisors h, ?_⟩, ?_⟩
  · exact (Nat.mul_div_cancel' (mem_properDivisors.mp h).1).symm
  · rintro ⟨k, hk, rfl⟩
    rw [mul_ne_zero_iff] at hn
    exact mem_properDivisors.mpr ⟨⟨k, rfl⟩, lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hn.1) hk⟩

@[simp]
/--
lemma `nonempty_properDivisors` / 引理 `nonempty_properDivisors`

English:
lemma nonempty_properDivisors
  statement: n.properDivisors.Nonempty ↔ 1 < n
  proof: ⟨fun ⟨_m, hm⟩ => one_lt_of_mem_properDivisors hm, fun hn =>
    ⟨1, one_mem_properDivisors_iff_one_lt.2 hn⟩⟩

@[simp]

中文:
引理 nonempty_properDivisors
  结论: n.properDivisors.非空 ↔ 1 < n
  证明: ⟨fun ⟨_m, hm⟩ => one_lt_of_mem_properDivisors hm, fun hn =>
    ⟨1, one_mem_properDivisors_iff_one_lt.2 hn⟩⟩

@[simp]

Depends on / 依赖: one_lt_of_mem_properDivisors, one_mem_properDivisors_iff_one_lt
-/
lemma nonempty_properDivisors : n.properDivisors.Nonempty ↔ 1 < n :=
  ⟨fun ⟨_m, hm⟩ => one_lt_of_mem_properDivisors hm, fun hn =>
    ⟨1, one_mem_properDivisors_iff_one_lt.2 hn⟩⟩

@[simp]
/--
lemma `properDivisors_eq_empty` / 引理 `properDivisors_eq_empty`

English:
lemma properDivisors_eq_empty
  statement: n.properDivisors = ∅ ↔ n <= 1
  proof: by
  contrapose!
  exact nonempty_properDivisors

@[simp]

中文:
引理 properDivisors_eq_empty
  结论: n.properDivisors = ∅ ↔ n <= 1
  证明: by
  contrapose!
  exact nonempty_properDivisors

@[simp]

Depends on / 依赖: contrapose, nonempty_properDivisors
-/
lemma properDivisors_eq_empty : n.properDivisors = ∅ ↔ n <= 1 := by
  contrapose!
  exact nonempty_properDivisors

@[simp]
/--
theorem `divisorsAntidiagonal_zero` / 定理 `divisorsAntidiagonal_zero`

English:
theorem divisorsAntidiagonal_zero
  statement: divisorsAntidiagonal 0 = ∅
  proof: by
  ext
  simp

@[simp]

中文:
定理 divisorsAntidiagonal_zero
  结论: divisorsAntidiagonal 0 = ∅
  证明: by
  ext
  simp

@[simp]
-/
theorem divisorsAntidiagonal_zero : divisorsAntidiagonal 0 = ∅ := by
  ext
  simp

@[simp]
/--
theorem `divisorsAntidiagonal_one` / 定理 `divisorsAntidiagonal_one`

English:
theorem divisorsAntidiagonal_one
  statement: divisorsAntidiagonal 1 = {(1, 1)}
  proof: by
  ext
  simp [mul_eq_one, Prod.ext_iff]

@[simp high]

中文:
定理 divisorsAntidiagonal_one
  结论: divisorsAntidiagonal 1 = {(1, 1)}
  证明: by
  ext
  simp [mul_eq_one, Prod.ext_iff]

@[simp high]

Depends on / 依赖: Prod.ext_iff, ext_iff, mul_eq_one
-/
theorem divisorsAntidiagonal_one : divisorsAntidiagonal 1 = {(1, 1)} := by
  ext
  simp [mul_eq_one, Prod.ext_iff]

@[simp high]
/--
theorem `swap_mem_divisorsAntidiagonal` / 定理 `swap_mem_divisorsAntidiagonal`

English:
theorem swap_mem_divisorsAntidiagonal
  given: {x : Nat × Nat}
  proof: by
  rw [mem_divisorsAntidiagonal]; rw [mem_divisorsAntidiagonal]; rw [mul_comm]; rw [Prod.swap]

中文:
定理 swap_mem_divisorsAntidiagonal
  条件: {x : 自然数 × 自然数}
  证明: by
  rw [mem_divisorsAntidiagonal]; rw [mem_divisorsAntidiagonal]; rw [mul_comm]; rw [Prod.swap]

Depends on / 依赖: Prod.swap, mem_divisorsAntidiagonal, mul_comm
-/
theorem swap_mem_divisorsAntidiagonal {x : Nat × Nat} :
    x.swap in divisorsAntidiagonal n ↔ x in divisorsAntidiagonal n := by
  rw [mem_divisorsAntidiagonal]; rw [mem_divisorsAntidiagonal]; rw [mul_comm]; rw [Prod.swap]

/--
lemma `prodMk_mem_divisorsAntidiag` / 引理 `prodMk_mem_divisorsAntidiag`

English:
lemma prodMk_mem_divisorsAntidiag
  given: {x y : Nat} (hn : n != 0)
  proof: by simp [hn]

中文:
引理 prodMk_mem_divisorsAntidiag
  条件: {x y : 自然数} (hn : n != 0)
  证明: by simp [hn]
-/
lemma prodMk_mem_divisorsAntidiag {x y : Nat} (hn : n != 0) :
    (x, y) in n.divisorsAntidiagonal ↔ x * y = n := by simp [hn]

/--
theorem `fst_mem_divisors_of_mem_antidiagonal` / 定理 `fst_mem_divisors_of_mem_antidiagonal`

English:
theorem fst_mem_divisors_of_mem_antidiagonal
  given: {x : Nat × Nat} (h : x in divisorsAntidiagonal n)
  proof: by
  rw [mem_divisorsAntidiagonal] at h
  simp [Dvd.intro _ h.1, h.2]

中文:
定理 fst_mem_divisors_of_mem_antidiagonal
  条件: {x : 自然数 × 自然数} (h : x in divisorsAntidiagonal n)
  证明: by
  rw [mem_divisorsAntidiagonal] at h
  simp [Dvd.intro _ h.1, h.2]

Depends on / 依赖: Dvd.intro, mem_divisorsAntidiagonal
-/
theorem fst_mem_divisors_of_mem_antidiagonal {x : Nat × Nat} (h : x in divisorsAntidiagonal n) :
    x.fst in divisors n := by
  rw [mem_divisorsAntidiagonal] at h
  simp [Dvd.intro _ h.1, h.2]

/--
theorem `snd_mem_divisors_of_mem_antidiagonal` / 定理 `snd_mem_divisors_of_mem_antidiagonal`

English:
theorem snd_mem_divisors_of_mem_antidiagonal
  given: {x : Nat × Nat} (h : x in divisorsAntidiagonal n)
  proof: by
  rw [mem_divisorsAntidiagonal] at h
  simp [Dvd.intro_left _ h.1, h.2]

@[simp]

中文:
定理 snd_mem_divisors_of_mem_antidiagonal
  条件: {x : 自然数 × 自然数} (h : x in divisorsAntidiagonal n)
  证明: by
  rw [mem_divisorsAntidiagonal] at h
  simp [Dvd.intro_left _ h.1, h.2]

@[simp]

Depends on / 依赖: Dvd.intro_left, intro_left, mem_divisorsAntidiagonal
-/
theorem snd_mem_divisors_of_mem_antidiagonal {x : Nat × Nat} (h : x in divisorsAntidiagonal n) :
    x.snd in divisors n := by
  rw [mem_divisorsAntidiagonal] at h
  simp [Dvd.intro_left _ h.1, h.2]

@[simp]
/--
theorem `map_swap_divisorsAntidiagonal` / 定理 `map_swap_divisorsAntidiagonal`

English:
theorem map_swap_divisorsAntidiagonal
  proof: by
  rw [← coe_inj]; rw [coe_map]; rw [Equiv.coe_toEmbedding]; rw [Equiv.coe_prodComm]; rw [Set.image_swap_eq_preimage_swap]
  ext
  exact swap_mem_divisorsAntidiagonal

@[simp]

中文:
定理 map_swap_divisorsAntidiagonal
  证明: by
  rw [← coe_inj]; rw [coe_map]; rw [Equiv.coe_toEmbedding]; rw [Equiv.coe_prodComm]; rw [Set.image_swap_eq_preimage_swap]
  ext
  exact swap_mem_divisorsAntidiagonal

@[simp]

Depends on / 依赖: Equiv.coe_prodComm, Equiv.coe_toEmbedding, Set.image_swap_eq_preimage_swap, coe_inj, coe_map, coe_prodComm, coe_toEmbedding, image_swap_eq_preimage_swap, swap_mem_divisorsAntidiagonal
-/
theorem map_swap_divisorsAntidiagonal :
    (divisorsAntidiagonal n).map (Equiv.prodComm _ _).toEmbedding = divisorsAntidiagonal n := by
  rw [← coe_inj]; rw [coe_map]; rw [Equiv.coe_toEmbedding]; rw [Equiv.coe_prodComm]; rw [Set.image_swap_eq_preimage_swap]
  ext
  exact swap_mem_divisorsAntidiagonal

@[simp]
/--
theorem `image_fst_divisorsAntidiagonal` / 定理 `image_fst_divisorsAntidiagonal`

English:
theorem image_fst_divisorsAntidiagonal
  statement: (divisorsAntidiagonal n).image Prod.fst = divisors n
  proof: by
  ext
  simp [Dvd.dvd, @eq_comm _ n (_ * _)]

@[simp]

中文:
定理 image_fst_divisorsAntidiagonal
  结论: (divisorsAntidiagonal n).像 积类型.fst = divisors n
  证明: by
  ext
  simp [Dvd.dvd, @eq_comm _ n (_ * _)]

@[simp]

Depends on / 依赖: Dvd.dvd, eq_comm
-/
theorem image_fst_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.fst = divisors n := by
  ext
  simp [Dvd.dvd, @eq_comm _ n (_ * _)]

@[simp]
/--
theorem `image_snd_divisorsAntidiagonal` / 定理 `image_snd_divisorsAntidiagonal`

English:
theorem image_snd_divisorsAntidiagonal
  statement: (divisorsAntidiagonal n).image Prod.snd = divisors n
  proof: by
  rw [← map_swap_divisorsAntidiagonal]; rw [map_eq_image]; rw [image_image]
  exact image_fst_divisorsAntidiagonal

中文:
定理 image_snd_divisorsAntidiagonal
  结论: (divisorsAntidiagonal n).像 积类型.snd = divisors n
  证明: by
  rw [← map_swap_divisorsAntidiagonal]; rw [map_eq_image]; rw [image_image]
  exact image_fst_divisorsAntidiagonal

Depends on / 依赖: image_fst_divisorsAntidiagonal, image_image, map_eq_image, map_swap_divisorsAntidiagonal
-/
theorem image_snd_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.snd = divisors n := by
  rw [← map_swap_divisorsAntidiagonal]; rw [map_eq_image]; rw [image_image]
  exact image_fst_divisorsAntidiagonal

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_div_right_divisors` / 定理 `map_div_right_divisors`

English:
theorem map_div_right_divisors
  proof: by
  ext ⟨d, nd⟩
  simp only [mem_map, mem_divisorsAntidiagonal, Function.Embedding.coeFn_mk, mem_divisors,
    Prod.ext_iff, and_left_comm, exists_eq_left]
  constructor
  · rintro ⟨⟨⟨k, rfl⟩, hn⟩, rfl⟩
    rw [Nat.mul_div_cancel_left _ (left_ne_zero_of_mul hn).bot_lt]
    exact ⟨rfl, hn⟩
  · rintr

中文:
定理 map_div_right_divisors
  证明: by
  ext ⟨d, nd⟩
  simp only [mem_map, mem_divisorsAntidiagonal, Function.Embedding.coeFn_mk, mem_divisors,
    Prod.ext_iff, and_left_comm, exists_eq_left]
  constructor
  · rintro ⟨⟨⟨k, rfl⟩, hn⟩, rfl⟩
    rw [Nat.mul_div_cancel_left _ (left_ne_zero_of_mul hn).bot_lt]
    exact ⟨rfl, hn⟩
  · rintr

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, Nat.mul_div_cancel_left, Prod.ext_iff, and_left_comm, bot_lt, coeFn_mk, dvd_mul_right, exists_eq_left, ext_iff, left_ne_zero_of_mul, mem_divisors, mem_divisorsAntidiagonal, mem_map, mul_div_cancel_left
-/
theorem map_div_right_divisors :
    n.divisors.map ⟨fun d => (d, n / d), fun _ _ => congr_arg Prod.fst⟩ =
      n.divisorsAntidiagonal := by
  ext ⟨d, nd⟩
  simp only [mem_map, mem_divisorsAntidiagonal, Function.Embedding.coeFn_mk, mem_divisors,
    Prod.ext_iff, and_left_comm, exists_eq_left]
  constructor
  · rintro ⟨⟨⟨k, rfl⟩, hn⟩, rfl⟩
    rw [Nat.mul_div_cancel_left _ (left_ne_zero_of_mul hn).bot_lt]
    exact ⟨rfl, hn⟩
  · rintro ⟨rfl, hn⟩
    exact ⟨⟨dvd_mul_right _ _, hn⟩, Nat.mul_div_cancel_left _ (left_ne_zero_of_mul hn).bot_lt⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_div_left_divisors` / 定理 `map_div_left_divisors`

English:
theorem map_div_left_divisors
  proof: by
  apply Finset.map_injective (Equiv.prodComm _ _).toEmbedding
  ext
  rw [map_swap_divisorsAntidiagonal]; rw [← map_div_right_divisors]; rw [Finset.map_map]
  simp

中文:
定理 map_div_left_divisors
  证明: by
  apply Finset.map_injective (Equiv.prodComm _ _).toEmbedding
  ext
  rw [map_swap_divisorsAntidiagonal]; rw [← map_div_right_divisors]; rw [Finset.map_map]
  simp

Depends on / 依赖: Equiv.prodComm, Finset, Finset.map_injective, Finset.map_map, map_div_right_divisors, map_injective, map_map, map_swap_divisorsAntidiagonal, prodComm, toEmbedding
-/
theorem map_div_left_divisors :
    n.divisors.map ⟨fun d => (n / d, d), fun _ _ => congr_arg Prod.snd⟩ =
      n.divisorsAntidiagonal := by
  apply Finset.map_injective (Equiv.prodComm _ _).toEmbedding
  ext
  rw [map_swap_divisorsAntidiagonal]; rw [← map_div_right_divisors]; rw [Finset.map_map]
  simp

/--
theorem `sum_divisors_eq_sum_properDivisors_add_self` / 定理 `sum_divisors_eq_sum_properDivisors_add_self`

English:
theorem sum_divisors_eq_sum_properDivisors_add_self
  proof: by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  · rw [← cons_self_properDivisors hn, Finset.sum_cons, add_comm]

中文:
定理 sum_divisors_eq_sum_properDivisors_add_self
  证明: by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  · rw [← cons_self_properDivisors hn, Finset.sum_cons, add_comm]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, Finset, Finset.sum_cons, add_comm, cons_self_properDivisors, eq_or_ne, sum_cons
-/
theorem sum_divisors_eq_sum_properDivisors_add_self :
    ∑ i in divisors n, i = (∑ i in properDivisors n, i) + n := by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  · rw [← cons_self_properDivisors hn, Finset.sum_cons, add_comm]

/--
Definition of `Perfect` / `Perfect` 的定义

English:
definition Perfect
  signature: (n : Nat)
  body: ∑ i in properDivisors n, i = n ∧ 0 < n

中文:
定义 完美
  签名: (n : 自然数)
  定义体: ∑ i in properDivisors n, i = n ∧ 0 < n

Depends on / 依赖: properDivisors
-/
def Perfect (n : Nat) : Prop :=
  ∑ i in properDivisors n, i = n ∧ 0 < n

/--
theorem `perfect_iff_sum_properDivisors` / 定理 `perfect_iff_sum_properDivisors`

English:
theorem perfect_iff_sum_properDivisors
  given: (h : 0 < n)
  statement: Perfect n ↔ ∑ i in properDivisors n, i = n
  proof: and_iff_left h

中文:
定理 perfect_iff_sum_properDivisors
  条件: (h : 0 < n)
  结论: 完美 n ↔ ∑ i in properDivisors n, i = n
  证明: and_iff_left h

Depends on / 依赖: and_iff_left
-/
theorem perfect_iff_sum_properDivisors (h : 0 < n) : Perfect n ↔ ∑ i in properDivisors n, i = n :=
  and_iff_left h

/--
theorem `perfect_iff_sum_divisors_eq_two_mul` / 定理 `perfect_iff_sum_divisors_eq_two_mul`

English:
theorem perfect_iff_sum_divisors_eq_two_mul
  given: (h : 0 < n)
  proof: by
  rw [perfect_iff_sum_properDivisors h]; rw [sum_divisors_eq_sum_properDivisors_add_self]; rw [two_mul]
  constructor <;> intro h
  · rw [h]
  · apply add_right_cancel h

中文:
定理 perfect_iff_sum_divisors_eq_two_mul
  条件: (h : 0 < n)
  证明: by
  rw [perfect_iff_sum_properDivisors h]; rw [sum_divisors_eq_sum_properDivisors_add_self]; rw [two_mul]
  constructor <;> intro h
  · rw [h]
  · apply add_right_cancel h

Depends on / 依赖: add_right_cancel, perfect_iff_sum_properDivisors, sum_divisors_eq_sum_properDivisors_add_self, two_mul
-/
theorem perfect_iff_sum_divisors_eq_two_mul (h : 0 < n) :
    Perfect n ↔ ∑ i in divisors n, i = 2 * n := by
  rw [perfect_iff_sum_properDivisors h]; rw [sum_divisors_eq_sum_properDivisors_add_self]; rw [two_mul]
  constructor <;> intro h
  · rw [h]
  · apply add_right_cancel h

/--
theorem `mem_divisors_prime_pow` / 定理 `mem_divisors_prime_pow`

English:
theorem mem_divisors_prime_pow
  given: {p : Nat} (pp : p.Prime) (k : Nat) {x : Nat}
  proof: by
  rw [mem_divisors]; rw [Nat.dvd_prime_pow pp]; rw [and_iff_left (ne_of_gt (pow_pos pp.pos k))]

中文:
定理 mem_divisors_prime_pow
  条件: {p : 自然数} (pp : p.素) (k : 自然数) {x : 自然数}
  证明: by
  rw [mem_divisors]; rw [Nat.dvd_prime_pow pp]; rw [and_iff_left (ne_of_gt (pow_pos pp.pos k))]

Depends on / 依赖: Nat.dvd_prime_pow, and_iff_left, dvd_prime_pow, mem_divisors, ne_of_gt, pow_pos, pp.pos
-/
theorem mem_divisors_prime_pow {p : Nat} (pp : p.Prime) (k : Nat) {x : Nat} :
    x in divisors (p ^ k) ↔ exists j <= k, x = p ^ j := by
  rw [mem_divisors]; rw [Nat.dvd_prime_pow pp]; rw [and_iff_left (ne_of_gt (pow_pos pp.pos k))]

/--
theorem `Prime.divisors` / 定理 `Prime.divisors`

English:
theorem Prime.divisors
  given: {p : Nat} (pp : p.Prime)
  statement: divisors p = {1, p}
  proof: by
  ext
  rw [mem_divisors]; rw [dvd_prime pp]; rw [and_iff_left pp.ne_zero]; rw [Finset.mem_insert]; rw [Finset.mem_singleton]

中文:
定理 素.divisors
  条件: {p : 自然数} (pp : p.素)
  结论: divisors p = {1, p}
  证明: by
  ext
  rw [mem_divisors]; rw [dvd_prime pp]; rw [and_iff_left pp.ne_zero]; rw [Finset.mem_insert]; rw [Finset.mem_singleton]

Depends on / 依赖: Finset, Finset.mem_insert, Finset.mem_singleton, and_iff_left, dvd_prime, mem_divisors, mem_insert, mem_singleton, ne_zero, pp.ne_zero
-/
theorem Prime.divisors {p : Nat} (pp : p.Prime) : divisors p = {1, p} := by
  ext
  rw [mem_divisors]; rw [dvd_prime pp]; rw [and_iff_left pp.ne_zero]; rw [Finset.mem_insert]; rw [Finset.mem_singleton]

/--
theorem `Prime.properDivisors` / 定理 `Prime.properDivisors`

English:
theorem Prime.properDivisors
  given: {p : Nat} (pp : p.Prime)
  statement: properDivisors p = {1}
  proof: by
  rw [← erase_insert self_notMem_properDivisors]; rw [insert_self_properDivisors pp.ne_zero]; rw [pp.divisors]; rw [pair_comm]; rw [erase_insert fun con => pp.ne_one (mem_singleton.1 con)]

中文:
定理 素.properDivisors
  条件: {p : 自然数} (pp : p.素)
  结论: properDivisors p = {1}
  证明: by
  rw [← erase_insert self_notMem_properDivisors]; rw [insert_self_properDivisors pp.ne_zero]; rw [pp.divisors]; rw [pair_comm]; rw [erase_insert fun con => pp.ne_one (mem_singleton.1 con)]

Depends on / 依赖: divisors, erase_insert, insert_self_properDivisors, mem_singleton, ne_one, ne_zero, pair_comm, pp.divisors, pp.ne_one, pp.ne_zero, self_notMem_properDivisors
-/
theorem Prime.properDivisors {p : Nat} (pp : p.Prime) : properDivisors p = {1} := by
  rw [← erase_insert self_notMem_properDivisors]; rw [insert_self_properDivisors pp.ne_zero]; rw [pp.divisors]; rw [pair_comm]; rw [erase_insert fun con => pp.ne_one (mem_singleton.1 con)]

/--
theorem `divisors_prime_pow` / 定理 `divisors_prime_pow`

English:
theorem divisors_prime_pow
  given: {p : Nat} (pp : p.Prime) (k : Nat)
  proof: by
  ext a
  rw [mem_divisors_prime_pow pp]
  simp [eq_comm]

中文:
定理 divisors_prime_pow
  条件: {p : 自然数} (pp : p.素) (k : 自然数)
  证明: by
  ext a
  rw [mem_divisors_prime_pow pp]
  simp [eq_comm]

Depends on / 依赖: eq_comm, mem_divisors_prime_pow
-/
theorem divisors_prime_pow {p : Nat} (pp : p.Prime) (k : Nat) :
    divisors (p ^ k) = (Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_injective pp.two_le⟩ := by
  ext a
  rw [mem_divisors_prime_pow pp]
  simp [eq_comm]

/--
theorem `divisors_injective` / 定理 `divisors_injective`

English:
theorem divisors_injective
  statement: Function.Injective divisors
  proof: Function.LeftInverse.injective sup_divisors_id

@[simp]

中文:
定理 divisors_injective
  结论: 函数.单射 divisors
  证明: Function.LeftInverse.injective sup_divisors_id

@[simp]

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, injective, sup_divisors_id
-/
theorem divisors_injective : Function.Injective divisors :=
  Function.LeftInverse.injective sup_divisors_id

@[simp]
/--
theorem `divisors_inj` / 定理 `divisors_inj`

English:
theorem divisors_inj
  given: {a b : Nat}
  statement: a.divisors = b.divisors ↔ a = b
  proof: divisors_injective.eq_iff

中文:
定理 divisors_inj
  条件: {a b : 自然数}
  结论: a.divisors = b.divisors ↔ a = b
  证明: divisors_injective.eq_iff

Depends on / 依赖: divisors_injective, divisors_injective.eq_iff, eq_iff
-/
theorem divisors_inj {a b : Nat} : a.divisors = b.divisors ↔ a = b :=
  divisors_injective.eq_iff

/--
theorem `eq_properDivisors_of_subset_of_sum_eq_sum` / 定理 `eq_properDivisors_of_subset_of_sum_eq_sum`

English:
theorem eq_properDivisors_of_subset_of_sum_eq_sum
  given: {s : Finset Nat} (hsub : s subseteq n.properDivisors)
  proof: by
  cases n
  · rw [properDivisors_zero, subset_empty] at hsub
    simp [hsub]
  classical
    rw [← sum_sdiff hsub]
    intro h
    apply Subset.antisymm hsub
    rw [← sdiff_eq_empty_iff_subset]
    contrapose! h
    apply ne_of_lt
    rw [← zero_add (∑ x in s]; rw [x)]; rw [← add_assoc]; rw [add

中文:
定理 eq_properDivisors_of_subset_of_sum_eq_sum
  条件: {s : 有限集 自然数} (hsub : s subseteq n.properDivisors)
  证明: by
  cases n
  · rw [properDivisors_zero, subset_empty] at hsub
    simp [hsub]
  classical
    rw [← sum_sdiff hsub]
    intro h
    apply Subset.antisymm hsub
    rw [← sdiff_eq_empty_iff_subset]
    contrapose! h
    apply ne_of_lt
    rw [← zero_add (∑ x in s]; rw [x)]; rw [← add_assoc]; rw [add

Depends on / 依赖: Subset, Subset.antisymm, add_assoc, add_zero, antisymm, classical, contrapose, ne_of_lt, pos_of_mem_properDivisors, properDivisors_zero, sdiff_eq_empty_iff_subset, sdiff_subset, subset_empty, sum_const_zero, sum_lt_sum_of_nonempty, sum_sdiff, zero_add
-/
theorem eq_properDivisors_of_subset_of_sum_eq_sum {s : Finset Nat} (hsub : s subseteq n.properDivisors) :
    ((∑ x in s, x) = ∑ x in n.properDivisors, x) -> s = n.properDivisors := by
  cases n
  · rw [properDivisors_zero, subset_empty] at hsub
    simp [hsub]
  classical
    rw [← sum_sdiff hsub]
    intro h
    apply Subset.antisymm hsub
    rw [← sdiff_eq_empty_iff_subset]
    contrapose! h
    apply ne_of_lt
    rw [← zero_add (∑ x in s]; rw [x)]; rw [← add_assoc]; rw [add_zero]
    gcongr
    have hlt :=
      sum_lt_sum_of_nonempty h fun x hx => pos_of_mem_properDivisors (sdiff_subset hx)
    simp only [sum_const_zero] at hlt
    apply hlt

/--
theorem `sum_properDivisors_dvd` / 定理 `sum_properDivisors_dvd`

English:
theorem sum_properDivisors_dvd
  given: (h : (∑ x in n.properDivisors, x) ∣ n)
  proof: by
  rcases n with - | n
  · simp
  · rcases n with - | n
    · simp at h
    · rw [or_iff_not_imp_right]
      intro ne_n
      have hlt : ∑ x in n.succ.succ.properDivisors, x < n.succ.succ :=
        lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h) ne_n
      symm
      rw [← mem_singleton]; rw [

中文:
定理 sum_properDivisors_dvd
  条件: (h : (∑ x in n.properDivisors, x) ∣ n)
  证明: by
  rcases n with - | n
  · simp
  · rcases n with - | n
    · simp at h
    · rw [or_iff_not_imp_right]
      intro ne_n
      have hlt : ∑ x in n.succ.succ.properDivisors, x < n.succ.succ :=
        lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h) ne_n
      symm
      rw [← mem_singleton]; rw [

Depends on / 依赖: Nat.le_of_dvd, Nat.succ_lt_succ, Nat.succ_pos, eq_properDivisors_of_subset_of_sum_eq_sum, le_of_dvd, lt_of_le_of_ne, mem_properDivisors, mem_singleton, n.succ.succ, n.succ.succ.properDivisors, ne_n, one_dvd, or_iff_not_imp_right, properDivisors, singleton_subset_iff, succ_lt_succ, succ_pos, sum_singleton
-/
theorem sum_properDivisors_dvd (h : (∑ x in n.properDivisors, x) ∣ n) :
    ∑ x in n.properDivisors, x = 1 ∨ ∑ x in n.properDivisors, x = n := by
  rcases n with - | n
  · simp
  · rcases n with - | n
    · simp at h
    · rw [or_iff_not_imp_right]
      intro ne_n
      have hlt : ∑ x in n.succ.succ.properDivisors, x < n.succ.succ :=
        lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h) ne_n
      symm
      rw [← mem_singleton]; rw [eq_properDivisors_of_subset_of_sum_eq_sum (singleton_subset_iff.2
        (mem_properDivisors.2 ⟨h]; rw [hlt⟩)) (sum_singleton _ _)]; rw [mem_properDivisors]
      exact ⟨one_dvd _, Nat.succ_lt_succ (Nat.succ_pos _)⟩

@[to_additive (attr := simp)]
/--
theorem `Prime.prod_properDivisors` / 定理 `Prime.prod_properDivisors`

English:
theorem Prime.prod_properDivisors
  given: {α : Type*} [CommMonoid α] {p : Nat} {f : Nat -> α} (h : p.Prime)
  proof: by simp [h.properDivisors]

@[to_additive (attr := simp)]

中文:
定理 素.prod_properDivisors
  条件: {α : 类型} [交换幺半群 α] {p : 自然数} {f : 自然数 -> α} (h : p.素)
  证明: by simp [h.properDivisors]

@[to_additive (attr := simp)]

Depends on / 依赖: h.properDivisors, properDivisors
-/
theorem Prime.prod_properDivisors {α : Type*} [CommMonoid α] {p : Nat} {f : Nat -> α} (h : p.Prime) :
    ∏ x in p.properDivisors, f x = f 1 := by simp [h.properDivisors]

@[to_additive (attr := simp)]
/--
theorem `Prime.prod_divisors` / 定理 `Prime.prod_divisors`

English:
theorem Prime.prod_divisors
  given: {α : Type*} [CommMonoid α] {p : Nat} {f : Nat -> α} (h : p.Prime)
  proof: by
  rw [← cons_self_properDivisors h.ne_zero]; rw [prod_cons]; rw [h.prod_properDivisors]

中文:
定理 素.prod_divisors
  条件: {α : 类型} [交换幺半群 α] {p : 自然数} {f : 自然数 -> α} (h : p.素)
  证明: by
  rw [← cons_self_properDivisors h.ne_zero]; rw [prod_cons]; rw [h.prod_properDivisors]

Depends on / 依赖: SupBotHomClass, SupBotHomClass.toBotHomClass, cons_self_properDivisors, h.ne_zero, h.prod_properDivisors, ne_zero, prod_cons, prod_properDivisors, toBotHomClass
-/
theorem Prime.prod_divisors {α : Type*} [CommMonoid α] {p : Nat} {f : Nat -> α} (h : p.Prime) :
    ∏ x in p.divisors, f x = f p * f 1 := by
  rw [← cons_self_properDivisors h.ne_zero]; rw [prod_cons]; rw [h.prod_properDivisors]

/--
theorem `properDivisors_eq_singleton_one_iff_prime` / 定理 `properDivisors_eq_singleton_one_iff_prime`

English:
theorem properDivisors_eq_singleton_one_iff_prime
  statement: n.properDivisors = {1} ↔ n.Prime
  proof: by
  refine ⟨fun h => ?_, Prime.properDivisors⟩
  rw [Nat.prime_def_lt]
refine ⟨Nat.succ_le_iff.mpr one_mem_properDivisors_iff_one_lt.mp (by simp [h]), ?_⟩
  intro m hm hdvd
  simpa [h] using mem_properDivisors.mpr ⟨hdvd, hm⟩

中文:
定理 properDivisors_eq_singleton_one_iff_prime
  结论: n.properDivisors = {1} ↔ n.素
  证明: by
  refine ⟨fun h => ?_, Prime.properDivisors⟩
  rw [Nat.prime_def_lt]
refine ⟨Nat.succ_le_iff.mpr one_mem_properDivisors_iff_one_lt.mp (by simp [h]), ?_⟩
  intro m hm hdvd
  simpa [h] using mem_properDivisors.mpr ⟨hdvd, hm⟩

Depends on / 依赖: BoundedLatticeHomClass, BoundedLatticeHomClass.toSupBotHomClass, Lattice, Nat.prime_def_lt, Nat.succ_le_iff.mpr, Prime.properDivisors, mem_properDivisors, mem_properDivisors.mpr, one_mem_properDivisors_iff_one_lt, one_mem_properDivisors_iff_one_lt.mp, prime_def_lt, properDivisors, succ_le_iff, toSupBotHomClass
-/
theorem properDivisors_eq_singleton_one_iff_prime : n.properDivisors = {1} ↔ n.Prime := by
  refine ⟨fun h => ?_, Prime.properDivisors⟩
  rw [Nat.prime_def_lt]
refine ⟨Nat.succ_le_iff.mpr one_mem_properDivisors_iff_one_lt.mp (by simp [h]), ?_⟩
  intro m hm hdvd
  simpa [h] using mem_properDivisors.mpr ⟨hdvd, hm⟩

/--
theorem `sum_properDivisors_eq_one_iff_prime` / 定理 `sum_properDivisors_eq_one_iff_prime`

English:
theorem sum_properDivisors_eq_one_iff_prime
  statement: ∑ x in n.properDivisors, x = 1 ↔ n.Prime
  proof: by
  rcases n with - | n
  · simp [Nat.not_prime_zero]
  · cases n
    · simp [Nat.not_prime_one]
    · rw [← properDivisors_eq_singleton_one_iff_prime]
      refine ⟨fun h => ?_, fun h => h.symm ▸ sum_singleton _ _⟩
      rw [@eq_comm (Finset Nat) _ _]
      apply
        eq_properDivisors_of_subse

中文:
定理 sum_properDivisors_eq_one_iff_prime
  结论: ∑ x in n.properDivisors, x = 1 ↔ n.素
  证明: by
  rcases n with - | n
  · simp [Nat.not_prime_zero]
  · cases n
    · simp [Nat.not_prime_one]
    · rw [← properDivisors_eq_singleton_one_iff_prime]
      refine ⟨fun h => ?_, fun h => h.symm ▸ sum_singleton _ _⟩
      rw [@eq_comm (Finset Nat) _ _]
      apply
        eq_properDivisors_of_subse

Depends on / 依赖: BoundedLatticeHomClass, BoundedLatticeHomClass.toBoundedOrderHomClass, Finset, Lattice, Nat.not_prime_one, Nat.not_prime_zero, Nat.succ_pos, eq_comm, eq_properDivisors_of_subset_of_sum_eq_sum, h.symm, not_prime_one, not_prime_zero, one_mem_properDivisors_iff_one_lt, properDivisors_eq_singleton_one_iff_prime, singleton_subset_iff, succ_lt_succ, succ_pos, sum_singleton, toBoundedOrderHomClass
-/
theorem sum_properDivisors_eq_one_iff_prime : ∑ x in n.properDivisors, x = 1 ↔ n.Prime := by
  rcases n with - | n
  · simp [Nat.not_prime_zero]
  · cases n
    · simp [Nat.not_prime_one]
    · rw [← properDivisors_eq_singleton_one_iff_prime]
      refine ⟨fun h => ?_, fun h => h.symm ▸ sum_singleton _ _⟩
      rw [@eq_comm (Finset Nat) _ _]
      apply
        eq_properDivisors_of_subset_of_sum_eq_sum
          (singleton_subset_iff.2
            (one_mem_properDivisors_iff_one_lt.2 (succ_lt_succ (Nat.succ_pos _))))
          ((sum_singleton _ _).trans h.symm)

/--
theorem `mem_properDivisors_prime_pow` / 定理 `mem_properDivisors_prime_pow`

English:
theorem mem_properDivisors_prime_pow
  given: {p : Nat} (pp : p.Prime) (k : Nat) {x : Nat}
  proof: by
  rw [mem_properDivisors]; rw [Nat.dvd_prime_pow pp]
  constructor
  · rintro ⟨⟨j, hjk, rfl⟩, hlt⟩
    exact ⟨j, (Nat.pow_lt_pow_iff_right pp.one_lt).mp hlt, rfl⟩
  · rintro ⟨j, hjk, rfl⟩
    exact ⟨⟨j, le_of_lt hjk, rfl⟩, Nat.pow_lt_pow_of_lt pp.one_lt hjk⟩

中文:
定理 mem_properDivisors_prime_pow
  条件: {p : 自然数} (pp : p.素) (k : 自然数) {x : 自然数}
  证明: by
  rw [mem_properDivisors]; rw [Nat.dvd_prime_pow pp]
  constructor
  · rintro ⟨⟨j, hjk, rfl⟩, hlt⟩
    exact ⟨j, (Nat.pow_lt_pow_iff_right pp.one_lt).mp hlt, rfl⟩
  · rintro ⟨j, hjk, rfl⟩
    exact ⟨⟨j, le_of_lt hjk, rfl⟩, Nat.pow_lt_pow_of_lt pp.one_lt hjk⟩

Depends on / 依赖: Nat.dvd_prime_pow, Nat.pow_lt_pow_iff_right, Nat.pow_lt_pow_of_lt, OrderBot, OrderIsoClass, OrderIsoClass.toSupBotHomClass, SemilatticeSup, dvd_prime_pow, le_of_lt, mem_properDivisors, one_lt, pow_lt_pow_iff_right, pow_lt_pow_of_lt, pp.one_lt, toSupBotHomClass
-/
theorem mem_properDivisors_prime_pow {p : Nat} (pp : p.Prime) (k : Nat) {x : Nat} :
    x in properDivisors (p ^ k) ↔ exists (j : Nat) (_ : j < k), x = p ^ j := by
  rw [mem_properDivisors]; rw [Nat.dvd_prime_pow pp]
  constructor
  · rintro ⟨⟨j, hjk, rfl⟩, hlt⟩
    exact ⟨j, (Nat.pow_lt_pow_iff_right pp.one_lt).mp hlt, rfl⟩
  · rintro ⟨j, hjk, rfl⟩
    exact ⟨⟨j, le_of_lt hjk, rfl⟩, Nat.pow_lt_pow_of_lt pp.one_lt hjk⟩

/--
theorem `properDivisors_prime_pow` / 定理 `properDivisors_prime_pow`

English:
theorem properDivisors_prime_pow
  given: {p : Nat} (pp : p.Prime) (k : Nat)
  proof: by
  ext a
  simp [mem_properDivisors_prime_pow pp, eq_comm]

@[to_additive (attr := simp)]

中文:
定理 properDivisors_prime_pow
  条件: {p : 自然数} (pp : p.素) (k : 自然数)
  证明: by
  ext a
  simp [mem_properDivisors_prime_pow pp, eq_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Lattice, OrderIsoClass, OrderIsoClass.toBoundedLatticeHomClass, eq_comm, mem_properDivisors_prime_pow, toBoundedLatticeHomClass
-/
theorem properDivisors_prime_pow {p : Nat} (pp : p.Prime) (k : Nat) :
    properDivisors (p ^ k) = (Finset.range k).map ⟨(p ^ ·), Nat.pow_right_injective pp.two_le⟩ := by
  ext a
  simp [mem_properDivisors_prime_pow pp, eq_comm]

@[to_additive (attr := simp)]
/--
theorem `prod_properDivisors_prime_pow` / 定理 `prod_properDivisors_prime_pow`

English:
theorem prod_properDivisors_prime_pow
  statement: {α : Type*} [CommMonoid α] {k p : Nat} {f : Nat -> α}
  proof: by
  simp [h, properDivisors_prime_pow]

@[to_additive (attr := simp) sum_divisors_prime_pow]

中文:
定理 prod_properDivisors_prime_pow
  结论: {α : 类型} [交换幺半群 α] {k p : 自然数} {f : 自然数 -> α}
  证明: by
  simp [h, properDivisors_prime_pow]

@[to_additive (attr := simp) sum_divisors_prime_pow]

Depends on / 依赖: properDivisors_prime_pow
-/
theorem prod_properDivisors_prime_pow {α : Type*} [CommMonoid α] {k p : Nat} {f : Nat -> α}
    (h : p.Prime) : (∏ x in (p ^ k).properDivisors, f x) = ∏ x in range k, f (p ^ x) := by
  simp [h, properDivisors_prime_pow]

@[to_additive (attr := simp) sum_divisors_prime_pow]
/--
theorem `prod_divisors_prime_pow` / 定理 `prod_divisors_prime_pow`

English:
theorem prod_divisors_prime_pow
  given: {α : Type*} [CommMonoid α] {k p : Nat} {f : Nat -> α} (h : p.Prime)
  proof: by
  simp [h, divisors_prime_pow]

@[to_additive]

中文:
定理 prod_divisors_prime_pow
  条件: {α : 类型} [交换幺半群 α] {k p : 自然数} {f : 自然数 -> α} (h : p.素)
  证明: by
  simp [h, divisors_prime_pow]

@[to_additive]

Depends on / 依赖: divisors_prime_pow
-/
theorem prod_divisors_prime_pow {α : Type*} [CommMonoid α] {k p : Nat} {f : Nat -> α} (h : p.Prime) :
    (∏ x in (p ^ k).divisors, f x) = ∏ x in range (k + 1), f (p ^ x) := by
  simp [h, divisors_prime_pow]

@[to_additive]
/--
theorem `prod_divisorsAntidiagonal` / 定理 `prod_divisorsAntidiagonal`

English:
theorem prod_divisorsAntidiagonal
  given: {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M) {n : Nat}
  proof: by
  rw [← map_div_right_divisors]; rw [Finset.prod_map]
  rfl

@[to_additive]

中文:
定理 prod_divisorsAntidiagonal
  条件: {M : 类型} [交换幺半群 M] (f : 自然数 -> 自然数 -> M) {n : 自然数}
  证明: by
  rw [← map_div_right_divisors]; rw [Finset.prod_map]
  rfl

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_map, map_div_right_divisors, prod_map
-/
theorem prod_divisorsAntidiagonal {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M) {n : Nat} :
    ∏ i in n.divisorsAntidiagonal, f i.1 i.2 = ∏ i in n.divisors, f i (n / i) := by
  rw [← map_div_right_divisors]; rw [Finset.prod_map]
  rfl

@[to_additive]
/--
theorem `prod_divisorsAntidiagonal'` / 定理 `prod_divisorsAntidiagonal'`

English:
theorem prod_divisorsAntidiagonal'
  given: {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M) {n : Nat}
  proof: by
  rw [← map_swap_divisorsAntidiagonal]; rw [Finset.prod_map]
  exact prod_divisorsAntidiagonal fun i j => f j i

中文:
定理 prod_divisorsAntidiagonal'
  条件: {M : 类型} [交换幺半群 M] (f : 自然数 -> 自然数 -> M) {n : 自然数}
  证明: by
  rw [← map_swap_divisorsAntidiagonal]; rw [Finset.prod_map]
  exact prod_divisorsAntidiagonal fun i j => f j i

Depends on / 依赖: Finset, Finset.prod_map, map_swap_divisorsAntidiagonal, prod_divisorsAntidiagonal, prod_map
-/
theorem prod_divisorsAntidiagonal' {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M) {n : Nat} :
    ∏ i in n.divisorsAntidiagonal, f i.1 i.2 = ∏ i in n.divisors, f (n / i) i := by
  rw [← map_swap_divisorsAntidiagonal]; rw [Finset.prod_map]
  exact prod_divisorsAntidiagonal fun i j => f j i

/--
theorem `primeFactors_eq_to_filter_divisors_prime` / 定理 `primeFactors_eq_to_filter_divisors_prime`

English:
theorem primeFactors_eq_to_filter_divisors_prime
  given: (n : Nat)
  proof: by
  grind

中文:
定理 primeFactors_eq_to_filter_divisors_prime
  条件: (n : 自然数)
  证明: by
  grind
-/
theorem primeFactors_eq_to_filter_divisors_prime (n : Nat) :
    n.primeFactors = {p in divisors n | p.Prime} := by
  grind

/--
lemma `primeFactors_filter_dvd_of_dvd` / 引理 `primeFactors_filter_dvd_of_dvd`

English:
lemma primeFactors_filter_dvd_of_dvd
  given: {m n : Nat} (hn : n != 0) (hmn : m ∣ n)
  proof: by
  simp_rw [primeFactors_eq_to_filter_divisors_prime, filter_comm,
    divisors_filter_dvd_of_dvd hn hmn]

@[simp]

中文:
引理 primeFactors_filter_dvd_of_dvd
  条件: {m n : 自然数} (hn : n != 0) (hmn : m ∣ n)
  证明: by
  simp_rw [primeFactors_eq_to_filter_divisors_prime, filter_comm,
    divisors_filter_dvd_of_dvd hn hmn]

@[simp]

Depends on / 依赖: divisors_filter_dvd_of_dvd, filter_comm, primeFactors_eq_to_filter_divisors_prime, simp_rw
-/
lemma primeFactors_filter_dvd_of_dvd {m n : Nat} (hn : n != 0) (hmn : m ∣ n) :
    {p in n.primeFactors | p ∣ m} = m.primeFactors := by
  simp_rw [primeFactors_eq_to_filter_divisors_prime, filter_comm,
    divisors_filter_dvd_of_dvd hn hmn]

@[simp]
/--
theorem `image_div_divisors_eq_divisors` / 定理 `image_div_divisors_eq_divisors`

English:
theorem image_div_divisors_eq_divisors
  given: (n : Nat)
  proof: by
  conv_rhs =>
    rw [← image_fst_divisorsAntidiagonal]; rw [← map_div_left_divisors]; rw [map_eq_image]; rw [image_image]
  rfl

@[to_additive (attr := simp) sum_div_divisors]

中文:
定理 image_div_divisors_eq_divisors
  条件: (n : 自然数)
  证明: by
  conv_rhs =>
    rw [← image_fst_divisorsAntidiagonal]; rw [← map_div_left_divisors]; rw [map_eq_image]; rw [image_image]
  rfl

@[to_additive (attr := simp) sum_div_divisors]

Depends on / 依赖: conv_rhs, image_fst_divisorsAntidiagonal, image_image, map_div_left_divisors, map_eq_image
-/
theorem image_div_divisors_eq_divisors (n : Nat) :
    image (fun x : Nat => n / x) n.divisors = n.divisors := by
  conv_rhs =>
    rw [← image_fst_divisorsAntidiagonal]; rw [← map_div_left_divisors]; rw [map_eq_image]; rw [image_image]
  rfl

@[to_additive (attr := simp) sum_div_divisors]
/--
theorem `prod_div_divisors` / 定理 `prod_div_divisors`

English:
theorem prod_div_divisors
  given: {α : Type*} [CommMonoid α] (n : Nat) (f : Nat -> α)
  proof: by
  by_cases hn : n = 0; · simp [hn]
  rw [← prod_image]
  · exact prod_congr (image_div_divisors_eq_divisors n) (by simp)
  · intro x hx y hy h
    rw [mem_coe]; rw [mem_divisors] at hx hy
    exact (div_eq_iff_eq_of_dvd_dvd hn hx.1 hy.1).mp h

中文:
定理 prod_div_divisors
  条件: {α : 类型} [交换幺半群 α] (n : 自然数) (f : 自然数 -> α)
  证明: by
  by_cases hn : n = 0; · simp [hn]
  rw [← prod_image]
  · exact prod_congr (image_div_divisors_eq_divisors n) (by simp)
  · intro x hx y hy h
    rw [mem_coe]; rw [mem_divisors] at hx hy
    exact (div_eq_iff_eq_of_dvd_dvd hn hx.1 hy.1).mp h

Depends on / 依赖: div_eq_iff_eq_of_dvd_dvd, image_div_divisors_eq_divisors, mem_coe, mem_divisors, prod_congr, prod_image
-/
theorem prod_div_divisors {α : Type*} [CommMonoid α] (n : Nat) (f : Nat -> α) :
    (∏ d in n.divisors, f (n / d)) = n.divisors.prod f := by
  by_cases hn : n = 0; · simp [hn]
  rw [← prod_image]
  · exact prod_congr (image_div_divisors_eq_divisors n) (by simp)
  · intro x hx y hy h
    rw [mem_coe]; rw [mem_divisors] at hx hy
    exact (div_eq_iff_eq_of_dvd_dvd hn hx.1 hy.1).mp h

/--
theorem `disjoint_divisors_filter_isPrimePow` / 定理 `disjoint_divisors_filter_isPrimePow`

English:
theorem disjoint_divisors_filter_isPrimePow
  given: {a b : Nat} (hab : a.Coprime b)
  proof: by
  simp only [Finset.disjoint_left, Finset.mem_filter, and_imp, Nat.mem_divisors, not_and]
  rintro n han _ha hn hbn _hb -
  exact hn.ne_one (Nat.eq_one_of_dvd_coprimes hab han hbn)

中文:
定理 disjoint_divisors_filter_isPrimePow
  条件: {a b : 自然数} (hab : a.Coprime b)
  证明: by
  simp only [Finset.disjoint_left, Finset.mem_filter, and_imp, Nat.mem_divisors, not_and]
  rintro n han _ha hn hbn _hb -
  exact hn.ne_one (Nat.eq_one_of_dvd_coprimes hab han hbn)

Depends on / 依赖: Finset, Finset.disjoint_left, Finset.mem_filter, Nat.eq_one_of_dvd_coprimes, Nat.mem_divisors, and_imp, disjoint_left, eq_one_of_dvd_coprimes, hn.ne_one, mem_divisors, mem_filter, ne_one, not_and
-/
theorem disjoint_divisors_filter_isPrimePow {a b : Nat} (hab : a.Coprime b) :
    Disjoint (a.divisors.filter IsPrimePow) (b.divisors.filter IsPrimePow) := by
  simp only [Finset.disjoint_left, Finset.mem_filter, and_imp, Nat.mem_divisors, not_and]
  rintro n han _ha hn hbn _hb -
  exact hn.ne_one (Nat.eq_one_of_dvd_coprimes hab han hbn)

/--
lemma `divisorsAntidiagonal_eq_prod_filter_of_le` / 引理 `divisorsAntidiagonal_eq_prod_filter_of_le`

English:
lemma divisorsAntidiagonal_eq_prod_filter_of_le
  given: {n N : Nat} (n_ne_zero : n != 0) (hn : n <= N)
  proof: by
  ext ⟨n1, n2⟩
  rw [Nat.mem_divisorsAntidiagonal]
  simp only [ne_eq, Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc]
  constructor
  · intro ⟨rfl, hn2⟩
    grw [← hn]
    simp (disch := lia) only [le_mul_iff_one_le_right, le_mul_iff_one_le_left, and_true]
    lia
  · intro ⟨⟨hn1, hn2⟩, h

中文:
引理 divisorsAntidiagonal_eq_prod_filter_of_le
  条件: {n N : 自然数} (n_ne_zero : n != 0) (hn : n <= N)
  证明: by
  ext ⟨n1, n2⟩
  rw [Nat.mem_divisorsAntidiagonal]
  simp only [ne_eq, Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc]
  constructor
  · intro ⟨rfl, hn2⟩
    grw [← hn]
    simp (disch := lia) only [le_mul_iff_one_le_right, le_mul_iff_one_le_left, and_true]
    lia
  · intro ⟨⟨hn1, hn2⟩, h

Depends on / 依赖: Finset, Finset.mem_Ioc, Finset.mem_filter, Finset.mem_product, Nat.mem_divisorsAntidiagonal, and_true, le_mul_iff_one_le_left, le_mul_iff_one_le_right, mem_Ioc, mem_divisorsAntidiagonal, mem_filter, mem_product, n_ne_zero, ne_eq
-/
lemma divisorsAntidiagonal_eq_prod_filter_of_le {n N : Nat} (n_ne_zero : n != 0) (hn : n <= N) :
    n.divisorsAntidiagonal = (Ioc 0 N ×ˢ Ioc 0 N).filter (fun x => x.1 * x.2 = n) := by
  ext ⟨n1, n2⟩
  rw [Nat.mem_divisorsAntidiagonal]
  simp only [ne_eq, Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc]
  constructor
  · intro ⟨rfl, hn2⟩
    grw [← hn]
    simp (disch := lia) only [le_mul_iff_one_le_right, le_mul_iff_one_le_left, and_true]
    lia
  · intro ⟨⟨hn1, hn2⟩, hn3⟩
    exact ⟨hn3, n_ne_zero⟩

/--
theorem `antidiagonal_map_subset_divisorsAntidiagonal_pow` / 定理 `antidiagonal_map_subset_divisorsAntidiagonal_pow`

English:
theorem antidiagonal_map_subset_divisorsAntidiagonal_pow
  given: {q : Nat} (hq : 1 < q) (k : Nat)
  proof: ⟨fun k => q ^ k, Nat.pow_right_injective hq⟩
    (Finset.antidiagonal k).map (.prodMap ι ι) subseteq (q ^ k).divisorsAntidiagonal := by
  intro k hk
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
  simp [Nat.mem_divisorsAntidiagonal, ← Finset.mem_antidiagonal.mp hi, pow_add, ne_zero_of_lt hq]

中文:
定理 antidiagonal_map_subset_divisorsAntidiagonal_pow
  条件: {q : 自然数} (hq : 1 < q) (k : 自然数)
  证明: ⟨fun k => q ^ k, Nat.pow_right_injective hq⟩
    (Finset.antidiagonal k).map (.prodMap ι ι) subseteq (q ^ k).divisorsAntidiagonal := by
  intro k hk
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
  simp [Nat.mem_divisorsAntidiagonal, ← Finset.mem_antidiagonal.mp hi, pow_add, ne_zero_of_lt hq]

Depends on / 依赖: Nat.pow_right_injective, pow_right_injective
-/
theorem antidiagonal_map_subset_divisorsAntidiagonal_pow {q : Nat} (hq : 1 < q) (k : Nat) :
    letI ι : Nat ↪ Nat := ⟨fun k => q ^ k, Nat.pow_right_injective hq⟩
    (Finset.antidiagonal k).map (.prodMap ι ι) subseteq (q ^ k).divisorsAntidiagonal := by
  intro k hk
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
  simp [Nat.mem_divisorsAntidiagonal, ← Finset.mem_antidiagonal.mp hi, pow_add, ne_zero_of_lt hq]

end Nat

namespace Int
variable {xy : Int × Int} {x y z : Int}

-- Local notation for the embeddings `n ↦ n, n ↦ -n : ℕ → ℤ`
local notation "natCast" => Nat.castEmbedding (R := Int)
local notation "negNatCast" =>
  Function.Embedding.trans Nat.castEmbedding (Equiv.toEmbedding (Equiv.neg Int))

/--
Definition of `divisors` / `divisors` 的定义

English:
definition divisors
  signature: (z : Int)
  body: letI s := z.natAbs.divisors
(s.map natCast).disjUnion (s.map negNatCast) by
    simp +contextual [s, disjoint_left, Eq.comm, forall_comm (β := _ = _)]

中文:
定义 divisors
  签名: (z : 整数)
  定义体: letI s := z.natAbs.divisors
(s.map natCast).disjUnion (s.map negNatCast) by
    simp +contextual [s, disjoint_left, Eq.comm, forall_comm (β := _ = _)]

Depends on / 依赖: Eq.comm, contextual, disjUnion, disjoint_left, divisors, forall_comm, natAbs, natCast, negNatCast, s.map, z.natAbs.divisors
-/
def divisors (z : Int) : Finset Int :=
  letI s := z.natAbs.divisors
(s.map natCast).disjUnion (s.map negNatCast) by
    simp +contextual [s, disjoint_left, Eq.comm, forall_comm (β := _ = _)]

/--
Definition of `divisorsAntidiag` / `divisorsAntidiag` 的定义

English:
definition divisorsAntidiag
  signature: : (z : Int) -> Finset (Int × Int)
  body: n.divisorsAntidiagonal
(s.map <| .prodMap natCast natCast).disjUnion (s.map <| .prodMap negNatCast negNatCast) by
      simp +contextual [s, disjoint_left, eq_comm]
  | negSucc n =>
    let s : Finset (Nat × Nat) := (n + 1).divisorsAntidiagonal
(s.map <| .prodMap natCast negNatCast).disjUnion (s.map

中文:
定义 divisorsAntidiag
  签名: : (z : 整数) -> 有限集 (整数 × 整数)
  定义体: n.divisorsAntidiagonal
(s.map <| .prodMap natCast natCast).disjUnion (s.map <| .prodMap negNatCast negNatCast) by
      simp +contextual [s, disjoint_left, eq_comm]
  | negSucc n =>
    let s : Finset (Nat × Nat) := (n + 1).divisorsAntidiagonal
(s.map <| .prodMap natCast negNatCast).disjUnion (s.map

Depends on / 依赖: divisorsAntidiagonal, n.divisorsAntidiagonal
-/
def divisorsAntidiag : (z : Int) -> Finset (Int × Int)
  | (n : Nat) =>
    let s : Finset (Nat × Nat) := n.divisorsAntidiagonal
(s.map <| .prodMap natCast natCast).disjUnion (s.map <| .prodMap negNatCast negNatCast) by
      simp +contextual [s, disjoint_left, eq_comm]
  | negSucc n =>
    let s : Finset (Nat × Nat) := (n + 1).divisorsAntidiagonal
(s.map <| .prodMap natCast negNatCast).disjUnion (s.map <| .prodMap negNatCast natCast) by
      simp +contextual [s, disjoint_left, eq_comm, forall_comm (α := _ * _ = _)]

/--
theorem `mem_divisors_iff_natAbs_mem_divisors_natAbs` / 定理 `mem_divisors_iff_natAbs_mem_divisors_natAbs`

English:
theorem mem_divisors_iff_natAbs_mem_divisors_natAbs
  proof: calc
  _ ↔ exists y in z.natAbs.divisors, ↑y = x ∨ -↑y = x := by
    simp [← exists_or, ← and_or_left, divisors]
  _ ↔ exists y in z.natAbs.divisors, y = x.natAbs := congr(exists y in _, $(by grind))
  _ ↔ x.natAbs in z.natAbs.divisors := exists_eq_right

@[simp, grind =]

中文:
定理 mem_divisors_iff_natAbs_mem_divisors_natAbs
  证明: calc
  _ ↔ exists y in z.natAbs.divisors, ↑y = x ∨ -↑y = x := by
    simp [← exists_or, ← and_or_left, divisors]
  _ ↔ exists y in z.natAbs.divisors, y = x.natAbs := congr(exists y in _, $(by grind))
  _ ↔ x.natAbs in z.natAbs.divisors := exists_eq_right

@[simp, grind =]
-/
theorem mem_divisors_iff_natAbs_mem_divisors_natAbs :
    x in z.divisors ↔ x.natAbs in z.natAbs.divisors := calc
  _ ↔ exists y in z.natAbs.divisors, ↑y = x ∨ -↑y = x := by
    simp [← exists_or, ← and_or_left, divisors]
  _ ↔ exists y in z.natAbs.divisors, y = x.natAbs := congr(exists y in _, $(by grind))
  _ ↔ x.natAbs in z.natAbs.divisors := exists_eq_right

@[simp, grind =]
/--
theorem `mem_divisors` / 定理 `mem_divisors`

English:
theorem mem_divisors
  statement: x in divisors z ↔ x ∣ z ∧ z != 0
  proof: by
  simp [mem_divisors_iff_natAbs_mem_divisors_natAbs]

中文:
定理 mem_divisors
  结论: x in divisors z ↔ x ∣ z ∧ z != 0
  证明: by
  simp [mem_divisors_iff_natAbs_mem_divisors_natAbs]

Depends on / 依赖: mem_divisors_iff_natAbs_mem_divisors_natAbs
-/
theorem mem_divisors : x in divisors z ↔ x ∣ z ∧ z != 0 := by
  simp [mem_divisors_iff_natAbs_mem_divisors_natAbs]

/--
theorem `dvd_of_mem_divisors` / 定理 `dvd_of_mem_divisors`

English:
theorem dvd_of_mem_divisors
  given: (h : x in divisors z)
  statement: x ∣ z
  proof: (mem_divisors.mp h).1

中文:
定理 dvd_of_mem_divisors
  条件: (h : x in divisors z)
  结论: x ∣ z
  证明: (mem_divisors.mp h).1

Depends on / 依赖: mem_divisors, mem_divisors.mp
-/
theorem dvd_of_mem_divisors (h : x in divisors z) : x ∣ z := (mem_divisors.mp h).1

/--
theorem `ne_zero_of_mem_divisors` / 定理 `ne_zero_of_mem_divisors`

English:
theorem ne_zero_of_mem_divisors
  given: (h : x in divisors z)
  statement: z != 0
  proof: (mem_divisors.mp h).2

中文:
定理 ne_zero_of_mem_divisors
  条件: (h : x in divisors z)
  结论: z != 0
  证明: (mem_divisors.mp h).2

Depends on / 依赖: mem_divisors, mem_divisors.mp
-/
theorem ne_zero_of_mem_divisors (h : x in divisors z) : z != 0 := (mem_divisors.mp h).2

/--
theorem `one_mem_divisors` / 定理 `one_mem_divisors`

English:
theorem one_mem_divisors
  statement: 1 in divisors z ↔ z != 0
  proof: by simp

中文:
定理 one_mem_divisors
  结论: 1 in divisors z ↔ z != 0
  证明: by simp
-/
theorem one_mem_divisors : 1 in divisors z ↔ z != 0 := by simp

/--
theorem `neg_one_mem_divisors` / 定理 `neg_one_mem_divisors`

English:
theorem neg_one_mem_divisors
  statement: -1 in divisors z ↔ z != 0
  proof: by simp

@[simp]

中文:
定理 neg_one_mem_divisors
  结论: -1 in divisors z ↔ z != 0
  证明: by simp

@[simp]
-/
theorem neg_one_mem_divisors : -1 in divisors z ↔ z != 0 := by simp

@[simp]
/--
lemma `divisors_zero` / 引理 `divisors_zero`

English:
lemma divisors_zero
  statement: divisors 0 = ∅
  proof: by
  ext
  simp

@[simp]

中文:
引理 divisors_zero
  结论: divisors 0 = ∅
  证明: by
  ext
  simp

@[simp]
-/
lemma divisors_zero : divisors 0 = ∅ := by
  ext
  simp

@[simp]
/--
lemma `nonempty_divisors` / 引理 `nonempty_divisors`

English:
lemma nonempty_divisors
  statement: (divisors z).Nonempty ↔ z != 0
  proof: ⟨fun ⟨z, hz⟩ hx => by simp [hx] at hz, fun hx => ⟨1, one_mem_divisors.mpr hx⟩⟩

@[simp]

中文:
引理 nonempty_divisors
  结论: (divisors z).非空 ↔ z != 0
  证明: ⟨fun ⟨z, hz⟩ hx => by simp [hx] at hz, fun hx => ⟨1, one_mem_divisors.mpr hx⟩⟩

@[simp]

Depends on / 依赖: one_mem_divisors, one_mem_divisors.mpr
-/
lemma nonempty_divisors : (divisors z).Nonempty ↔ z != 0 :=
  ⟨fun ⟨z, hz⟩ hx => by simp [hx] at hz, fun hx => ⟨1, one_mem_divisors.mpr hx⟩⟩

@[simp]
/--
lemma `divisors_eq_empty` / 引理 `divisors_eq_empty`

English:
lemma divisors_eq_empty
  statement: divisors z = ∅ ↔ z = 0
  proof: by
  contrapose!
  exact nonempty_divisors

@[simp]

中文:
引理 divisors_eq_empty
  结论: divisors z = ∅ ↔ z = 0
  证明: by
  contrapose!
  exact nonempty_divisors

@[simp]

Depends on / 依赖: contrapose, nonempty_divisors
-/
lemma divisors_eq_empty : divisors z = ∅ ↔ z = 0 := by
  contrapose!
  exact nonempty_divisors

@[simp]
/--
theorem `divisors_one` / 定理 `divisors_one`

English:
theorem divisors_one
  statement: divisors 1 = {1, -1}
  proof: rfl

中文:
定理 divisors_one
  结论: divisors 1 = {1, -1}
  证明: rfl
-/
theorem divisors_one : divisors 1 = {1, -1} := rfl

/--
lemma `mem_divisors_self` / 引理 `mem_divisors_self`

English:
lemma mem_divisors_self
  given: (hz : z != 0)
  statement: z in divisors z
  proof: mem_divisors.mpr ⟨dvd_rfl, hz⟩

中文:
引理 mem_divisors_self
  条件: (hz : z != 0)
  结论: z in divisors z
  证明: mem_divisors.mpr ⟨dvd_rfl, hz⟩

Depends on / 依赖: dvd_rfl, mem_divisors, mem_divisors.mpr
-/
lemma mem_divisors_self (hz : z != 0) : z in divisors z :=
  mem_divisors.mpr ⟨dvd_rfl, hz⟩

/--
theorem `divisors_neg` / 定理 `divisors_neg`

English:
theorem divisors_neg
  statement: divisors (-z) = divisors z
  proof: by
  ext
  simp

@[simp]

中文:
定理 divisors_neg
  结论: divisors (-z) = divisors z
  证明: by
  ext
  simp

@[simp]
-/
@[simp] theorem divisors_neg : divisors (-z) = divisors z := by
  ext
  simp

@[simp]
/--
lemma `mem_divisorsAntidiag` / 引理 `mem_divisorsAntidiag`

English:
lemma mem_divisorsAntidiag
  statement: xy in divisorsAntidiag z ↔ xy.fst * xy.snd = z ∧ z != 0
  proof: by
  rcases z, xy with ⟨_ | _, ⟨_ | _, _ | _⟩⟩
  -- splitting this case saves about 1770 heartbeats i.e. 12.5% faster
  case ofNat.negSucc.negSucc =>
    simp [divisorsAntidiag]
    grind [Nat.cast_inj]
  all_goals
    simp [divisorsAntidiag]
    grind

中文:
引理 mem_divisorsAntidiag
  结论: xy in divisorsAntidiag z ↔ xy.fst * xy.snd = z ∧ z != 0
  证明: by
  rcases z, xy with ⟨_ | _, ⟨_ | _, _ | _⟩⟩
  -- splitting this case saves about 1770 heartbeats i.e. 12.5% faster
  case ofNat.negSucc.negSucc =>
    simp [divisorsAntidiag]
    grind [Nat.cast_inj]
  all_goals
    simp [divisorsAntidiag]
    grind
-/
lemma mem_divisorsAntidiag : xy in divisorsAntidiag z ↔ xy.fst * xy.snd = z ∧ z != 0 := by
  rcases z, xy with ⟨_ | _, ⟨_ | _, _ | _⟩⟩
  -- splitting this case saves about 1770 heartbeats i.e. 12.5% faster
  case ofNat.negSucc.negSucc =>
    simp [divisorsAntidiag]
    grind [Nat.cast_inj]
  all_goals
    simp [divisorsAntidiag]
    grind

/--
theorem `image_fst_divisorsAntidiag` / 定理 `image_fst_divisorsAntidiag`

English:
theorem image_fst_divisorsAntidiag
  statement: z.divisorsAntidiag.image Prod.fst = z.divisors
  proof: by
  ext
  simp [Eq.comm, dvd_def]

中文:
定理 image_fst_divisorsAntidiag
  结论: z.divisorsAntidiag.像 积类型.fst = z.divisors
  证明: by
  ext
  simp [Eq.comm, dvd_def]

Depends on / 依赖: Eq.comm, dvd_def
-/
theorem image_fst_divisorsAntidiag : z.divisorsAntidiag.image Prod.fst = z.divisors := by
  ext
  simp [Eq.comm, dvd_def]

/--
theorem `image_snd_divisorsAntidiag` / 定理 `image_snd_divisorsAntidiag`

English:
theorem image_snd_divisorsAntidiag
  statement: z.divisorsAntidiag.image Prod.snd = z.divisors
  proof: by
  ext
  simp [Eq.comm, mul_comm, dvd_def]

中文:
定理 image_snd_divisorsAntidiag
  结论: z.divisorsAntidiag.像 积类型.snd = z.divisors
  证明: by
  ext
  simp [Eq.comm, mul_comm, dvd_def]

Depends on / 依赖: Eq.comm, dvd_def, mul_comm
-/
theorem image_snd_divisorsAntidiag : z.divisorsAntidiag.image Prod.snd = z.divisors := by
  ext
  simp [Eq.comm, mul_comm, dvd_def]

/--
lemma `divisorsAntidiag_zero` / 引理 `divisorsAntidiag_zero`

English:
lemma divisorsAntidiag_zero
  statement: divisorsAntidiag 0 = ∅
  proof: rfl

中文:
引理 divisorsAntidiag_zero
  结论: divisorsAntidiag 0 = ∅
  证明: rfl
-/
@[simp] lemma divisorsAntidiag_zero : divisorsAntidiag 0 = ∅ := rfl

-- TODO Write a simproc instead of `divisorsAntidiagonal_one`, ..., `divisorsAntidiagonal_four` ...

@[simp]
/--
theorem `divisorsAntidiagonal_one` / 定理 `divisorsAntidiagonal_one`

English:
theorem divisorsAntidiagonal_one
  proof: rfl

@[simp]

中文:
定理 divisorsAntidiagonal_one
  证明: rfl

@[simp]
-/
theorem divisorsAntidiagonal_one :
    Int.divisorsAntidiag 1 = {(1, 1), (-1, -1)} :=
  rfl

@[simp]
/--
theorem `divisorsAntidiagonal_two` / 定理 `divisorsAntidiagonal_two`

English:
theorem divisorsAntidiagonal_two
  proof: rfl

@[simp]

中文:
定理 divisorsAntidiagonal_two
  证明: rfl

@[simp]
-/
theorem divisorsAntidiagonal_two :
    Int.divisorsAntidiag 2 = {(1, 2), (2, 1), (-1, -2), (-2, -1)} :=
  rfl

@[simp]
/--
theorem `divisorsAntidiagonal_three` / 定理 `divisorsAntidiagonal_three`

English:
theorem divisorsAntidiagonal_three
  proof: rfl

@[simp]

中文:
定理 divisorsAntidiagonal_three
  证明: rfl

@[simp]
-/
theorem divisorsAntidiagonal_three :
    Int.divisorsAntidiag 3 = {(1, 3), (3, 1), (-1, -3), (-3, -1)} :=
  rfl

@[simp]
/--
theorem `divisorsAntidiagonal_four` / 定理 `divisorsAntidiagonal_four`

English:
theorem divisorsAntidiagonal_four
  proof: rfl

中文:
定理 divisorsAntidiagonal_four
  证明: rfl
-/
theorem divisorsAntidiagonal_four :
    Int.divisorsAntidiag 4 = {(1, 4), (2, 2), (4, 1), (-1, -4), (-2, -2), (-4, -1)} :=
  rfl

/--
lemma `prodMk_mem_divisorsAntidiag` / 引理 `prodMk_mem_divisorsAntidiag`

English:
lemma prodMk_mem_divisorsAntidiag
  given: (hz : z != 0)
  statement: (x, y) in z.divisorsAntidiag ↔ x * y = z
  proof: by
  simp [hz]

@[simp high]

中文:
引理 prodMk_mem_divisorsAntidiag
  条件: (hz : z != 0)
  结论: (x, y) in z.divisorsAntidiag ↔ x * y = z
  证明: by
  simp [hz]

@[simp high]
-/
lemma prodMk_mem_divisorsAntidiag (hz : z != 0) : (x, y) in z.divisorsAntidiag ↔ x * y = z := by
  simp [hz]

@[simp high]
/--
lemma `swap_mem_divisorsAntidiag` / 引理 `swap_mem_divisorsAntidiag`

English:
lemma swap_mem_divisorsAntidiag
  statement: xy.swap in z.divisorsAntidiag ↔ xy in z.divisorsAntidiag
  proof: by
  simp [mul_comm]

中文:
引理 swap_mem_divisorsAntidiag
  结论: xy.swap in z.divisorsAntidiag ↔ xy in z.divisorsAntidiag
  证明: by
  simp [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma swap_mem_divisorsAntidiag : xy.swap in z.divisorsAntidiag ↔ xy in z.divisorsAntidiag := by
  simp [mul_comm]

/--
lemma `neg_mem_divisorsAntidiag` / 引理 `neg_mem_divisorsAntidiag`

English:
lemma neg_mem_divisorsAntidiag
  statement: -xy in z.divisorsAntidiag ↔ xy in z.divisorsAntidiag
  proof: by simp

@[simp]

中文:
引理 neg_mem_divisorsAntidiag
  结论: -xy in z.divisorsAntidiag ↔ xy in z.divisorsAntidiag
  证明: by simp

@[simp]
-/
lemma neg_mem_divisorsAntidiag : -xy in z.divisorsAntidiag ↔ xy in z.divisorsAntidiag := by simp

@[simp]
/--
lemma `map_prodComm_divisorsAntidiag` / 引理 `map_prodComm_divisorsAntidiag`

English:
lemma map_prodComm_divisorsAntidiag
  proof: by
  ext; simp [mem_divisorsAntidiag]

@[simp]

中文:
引理 map_prodComm_divisorsAntidiag
  证明: by
  ext; simp [mem_divisorsAntidiag]

@[simp]

Depends on / 依赖: mem_divisorsAntidiag
-/
lemma map_prodComm_divisorsAntidiag :
    z.divisorsAntidiag.map (Equiv.prodComm _ _).toEmbedding = z.divisorsAntidiag := by
  ext; simp [mem_divisorsAntidiag]

@[simp]
/--
lemma `map_neg_divisorsAntidiag` / 引理 `map_neg_divisorsAntidiag`

English:
lemma map_neg_divisorsAntidiag
  proof: by
  ext; simp [mem_divisorsAntidiag, mul_comm]

中文:
引理 map_neg_divisorsAntidiag
  证明: by
  ext; simp [mem_divisorsAntidiag, mul_comm]

Depends on / 依赖: mem_divisorsAntidiag, mul_comm
-/
lemma map_neg_divisorsAntidiag :
    z.divisorsAntidiag.map (Equiv.neg _).toEmbedding = z.divisorsAntidiag := by
  ext; simp [mem_divisorsAntidiag, mul_comm]

/--
lemma `divisorsAntidiag_neg` / 引理 `divisorsAntidiag_neg`

English:
lemma divisorsAntidiag_neg
  proof: by
  ext; simp [mem_divisorsAntidiag, Prod.ext_iff, neg_eq_iff_eq_neg]

中文:
引理 divisorsAntidiag_neg
  证明: by
  ext; simp [mem_divisorsAntidiag, Prod.ext_iff, neg_eq_iff_eq_neg]

Depends on / 依赖: Prod.ext_iff, ext_iff, mem_divisorsAntidiag, neg_eq_iff_eq_neg
-/
lemma divisorsAntidiag_neg :
    (-z).divisorsAntidiag =
      z.divisorsAntidiag.map (.prodMap (.refl _) (Equiv.neg _).toEmbedding) := by
  ext; simp [mem_divisorsAntidiag, Prod.ext_iff, neg_eq_iff_eq_neg]

/--
lemma `divisorsAntidiag_natCast` / 引理 `divisorsAntidiag_natCast`

English:
lemma divisorsAntidiag_natCast
  given: (n : Nat)
  proof: rfl

中文:
引理 divisorsAntidiag_natCast
  条件: (n : 自然数)
  证明: rfl
-/
lemma divisorsAntidiag_natCast (n : Nat) :
    divisorsAntidiag n =
      (n.divisorsAntidiagonal.map <| .prodMap natCast natCast).disjUnion
        (n.divisorsAntidiagonal.map <| .prodMap negNatCast negNatCast) (by
          simp +contextual [disjoint_left, eq_comm]) := rfl

/--
lemma `divisorsAntidiag_neg_natCast` / 引理 `divisorsAntidiag_neg_natCast`

English:
lemma divisorsAntidiag_neg_natCast
  given: (n : Nat)
  proof: by cases n <;> rfl

中文:
引理 divisorsAntidiag_neg_natCast
  条件: (n : 自然数)
  证明: by cases n <;> rfl
-/
lemma divisorsAntidiag_neg_natCast (n : Nat) :
    divisorsAntidiag (-n) =
      (n.divisorsAntidiagonal.map <| .prodMap natCast negNatCast).disjUnion
        (n.divisorsAntidiagonal.map <| .prodMap negNatCast natCast) (by
          simp +contextual [disjoint_left, eq_comm]) := by cases n <;> rfl

/--
lemma `divisorsAntidiag_ofNat` / 引理 `divisorsAntidiag_ofNat`

English:
lemma divisorsAntidiag_ofNat
  given: (n : Nat)
  proof: rfl

中文:
引理 divisorsAntidiag_of自然数
  条件: (n : 自然数)
  证明: rfl
-/
lemma divisorsAntidiag_ofNat (n : Nat) :
    divisorsAntidiag ofNat(n) =
      (n.divisorsAntidiagonal.map <| .prodMap natCast natCast).disjUnion
        (n.divisorsAntidiagonal.map <| .prodMap negNatCast negNatCast) (by
          simp +contextual [disjoint_left, eq_comm]) := rfl

/--
lemma `mul_mem_one_two_three_iff` / 引理 `mul_mem_one_two_three_iff`

English:
lemma mul_mem_one_two_three_iff
  given: {a b : Int}
  proof: by
  simp only [← Int.prodMk_mem_divisorsAntidiag, Set.mem_insert_iff, Set.mem_singleton_iff, ne_eq,
    one_ne_zero, not_false_eq_true, OfNat.ofNat_ne_zero]
  aesop

中文:
引理 mul_mem_one_two_three_iff
  条件: {a b : 整数}
  证明: by
  simp only [← Int.prodMk_mem_divisorsAntidiag, Set.mem_insert_iff, Set.mem_singleton_iff, ne_eq,
    one_ne_zero, not_false_eq_true, OfNat.ofNat_ne_zero]
  aesop

Depends on / 依赖: Int.prodMk_mem_divisorsAntidiag, OfNat.ofNat_ne_zero, Set.mem_insert_iff, Set.mem_singleton_iff, mem_insert_iff, mem_singleton_iff, ne_eq, not_false_eq_true, ofNat_ne_zero, one_ne_zero, prodMk_mem_divisorsAntidiag
-/
lemma mul_mem_one_two_three_iff {a b : Int} :
    a * b in ({1, 2, 3} : Set Int) ↔ (a, b) in ({
      (1, 1), (-1, -1),
      (1, 2), (2, 1), (-1, -2), (-2, -1),
      (1, 3), (3, 1), (-1, -3), (-3, -1)} : Set (Int × Int)) := by
  simp only [← Int.prodMk_mem_divisorsAntidiag, Set.mem_insert_iff, Set.mem_singleton_iff, ne_eq,
    one_ne_zero, not_false_eq_true, OfNat.ofNat_ne_zero]
  aesop

/--
lemma `mul_mem_zero_one_two_three_four_iff` / 引理 `mul_mem_zero_one_two_three_four_iff`

English:
lemma mul_mem_zero_one_two_three_four_iff
  given: {a b : Int} (h₀ : a = 0 ↔ b = 0)
  proof: by
  simp only [← Int.prodMk_mem_divisorsAntidiag, Set.mem_insert_iff, Set.mem_singleton_iff, ne_eq,
    one_ne_zero, not_false_eq_true, OfNat.ofNat_ne_zero]
  aesop

中文:
引理 mul_mem_zero_one_two_three_four_iff
  条件: {a b : 整数} (h₀ : a = 0 ↔ b = 0)
  证明: by
  simp only [← Int.prodMk_mem_divisorsAntidiag, Set.mem_insert_iff, Set.mem_singleton_iff, ne_eq,
    one_ne_zero, not_false_eq_true, OfNat.ofNat_ne_zero]
  aesop

Depends on / 依赖: Int.prodMk_mem_divisorsAntidiag, OfNat.ofNat_ne_zero, Set.mem_insert_iff, Set.mem_singleton_iff, mem_insert_iff, mem_singleton_iff, ne_eq, not_false_eq_true, ofNat_ne_zero, one_ne_zero, prodMk_mem_divisorsAntidiag
-/
lemma mul_mem_zero_one_two_three_four_iff {a b : Int} (h₀ : a = 0 ↔ b = 0) :
    a * b in ({0, 1, 2, 3, 4} : Set Int) ↔ (a, b) in ({
      (0, 0),
      (1, 1), (-1, -1),
      (1, 2), (2, 1), (-1, -2), (-2, -1),
      (1, 3), (3, 1), (-1, -3), (-3, -1),
      (4, 1), (1, 4), (-4, -1), (-1, -4), (2, 2), (-2, -2)} : Set (Int × Int)) := by
  simp only [← Int.prodMk_mem_divisorsAntidiag, Set.mem_insert_iff, Set.mem_singleton_iff, ne_eq,
    one_ne_zero, not_false_eq_true, OfNat.ofNat_ne_zero]
  aesop

end Int
