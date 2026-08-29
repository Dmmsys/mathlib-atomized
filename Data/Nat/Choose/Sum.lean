/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Sums of binomial coefficients

This file includes variants of the binomial theorem and other results on sums of binomial
coefficients. Theorems whose proofs depend on such sums may also go in this file for import
reasons.
-/

public section

open Nat Finset

variable {R : Type*}

namespace Commute

variable [Semiring R] {x y : R}

/--
theorem `add_pow` / 定理 `add_pow`

English:
theorem add_pow
  given: (h : Commute x y) (n : Nat)
  proof: by
  let t : Nat -> Nat -> R := fun n m => x ^ m * y ^ (n - m) * n.choose m
  change (x + y) ^ n = ∑ m in range (n + 1), t n m
  have h_first : forall n, t n 0 = y ^ n := fun n => by
    simp only [t, choose_zero_right, pow_zero, cast_one, mul_one, one_mul, Nat.sub_zero]
  have h_last : forall n, t 

中文:
定理 add_pow
  条件: (h : Commute x y) (n : 自然数)
  证明: by
  let t : Nat -> Nat -> R := fun n m => x ^ m * y ^ (n - m) * n.choose m
  change (x + y) ^ n = ∑ m in range (n + 1), t n m
  have h_first : forall n, t n 0 = y ^ n := fun n => by
    simp only [t, choose_zero_right, pow_zero, cast_one, mul_one, one_mul, Nat.sub_zero]
  have h_last : forall n, t 

Depends on / 依赖: Nat.sub_zero, cast_one, cast_zero, choose_succ_self, choose_zero_right, h_first, h_last, h_mem, h_middle, i.succ, mul_one, mul_zero, n.choose, n.succ, one_mul, pow_zero, sub_zero
-/
theorem add_pow (h : Commute x y) (n : Nat) :
    (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m := by
  let t : Nat -> Nat -> R := fun n m => x ^ m * y ^ (n - m) * n.choose m
  change (x + y) ^ n = ∑ m in range (n + 1), t n m
  have h_first : forall n, t n 0 = y ^ n := fun n => by
    simp only [t, choose_zero_right, pow_zero, cast_one, mul_one, one_mul, Nat.sub_zero]
  have h_last : forall n, t n n.succ = 0 := fun n => by
    simp only [t, choose_succ_self, cast_zero, mul_zero]
  have h_middle :
      forall n i : Nat, i in range n.succ -> (t n.succ i.succ) = x * t n i + y * t n i.succ := by
    intro n i h_mem
    have h_le : i <= n := le_of_lt_succ (mem_range.mp h_mem)
    dsimp only [t]
    rw [choose_succ_succ]; rw [cast_add]; rw [mul_add]
    congr 1
    · rw [pow_succ' x, succ_sub_succ, mul_assoc, mul_assoc, mul_assoc]
    · rw [← mul_assoc y, ← mul_assoc y, (h.symm.pow_right i.succ).eq]
      by_cases h_eq : i = n
      · rw [h_eq, choose_succ_self, cast_zero, mul_zero, mul_zero]
      · rw [succ_sub (lt_of_le_of_ne h_le h_eq)]
        rw [pow_succ' y]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_assoc]; rw [mul_assoc]
  induction n with
  | zero =>
    rw [pow_zero]; rw [sum_range_succ]; rw [range_zero]; rw [sum_empty]; rw [zero_add]
    dsimp only [t]
    rw [pow_zero]; rw [pow_zero]; rw [choose_self]; rw [cast_one]; rw [mul_one]; rw [mul_one]
  | succ n ih =>
    rw [sum_range_succ']; rw [h_first]; rw [sum_congr rfl (h_middle n)]; rw [sum_add_distrib]; rw [add_assoc]; rw [pow_succ' (x + y)]; rw [ih]; rw [add_mul]; rw [mul_sum]; rw [mul_sum]
    congr 1
    rw [sum_range_succ']; rw [sum_range_succ]; rw [h_first]; rw [h_last]; rw [mul_zero]; rw [add_zero]; rw [_root_.pow_succ']

/--
theorem `add_pow'` / 定理 `add_pow'`

English:
theorem add_pow'
  given: (h : Commute x y) (n : Nat)
  proof: by
  simp_rw [Nat.sum_antidiagonal_eq_sum_range_succ fun m p => n.choose m • (x ^ m * y ^ p),
    nsmul_eq_mul, cast_comm, h.add_pow]

中文:
定理 add_pow'
  条件: (h : Commute x y) (n : 自然数)
  证明: by
  simp_rw [Nat.sum_antidiagonal_eq_sum_range_succ fun m p => n.choose m • (x ^ m * y ^ p),
    nsmul_eq_mul, cast_comm, h.add_pow]

Depends on / 依赖: Nat.sum_antidiagonal_eq_sum_range_succ, add_pow, cast_comm, h.add_pow, n.choose, nsmul_eq_mul, simp_rw, sum_antidiagonal_eq_sum_range_succ
-/
theorem add_pow' (h : Commute x y) (n : Nat) :
    (x + y) ^ n = ∑ m in antidiagonal n, n.choose m.1 • (x ^ m.1 * y ^ m.2) := by
  simp_rw [Nat.sum_antidiagonal_eq_sum_range_succ fun m p => n.choose m • (x ^ m * y ^ p),
    nsmul_eq_mul, cast_comm, h.add_pow]

end Commute

/--
theorem `add_pow` / 定理 `add_pow`

English:
theorem add_pow
  given: [CommSemiring R] (x y : R) (n : Nat)
  proof: (Commute.all x y).add_pow n

中文:
定理 add_pow
  条件: [交换半环 R] (x y : R) (n : 自然数)
  证明: (Commute.all x y).add_pow n

Depends on / 依赖: Commute, Commute.all, add_pow
-/
theorem add_pow [CommSemiring R] (x y : R) (n : Nat) :
    (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m :=
  (Commute.all x y).add_pow n

/--
theorem `sub_pow` / 定理 `sub_pow`

English:
theorem sub_pow
  given: [CommRing R] (x y : R) (n : Nat)
  proof: by
  rw [sub_eq_add_neg]; rw [add_pow]
  congr! 1 with m hm
  have : (-1 : R) ^ (n - m) = (-1) ^ (n + m) := by
    rw [mem_range] at hm
    simp [show n + m = n - m + 2 * m by lia, pow_add]
  rw [neg_pow]; rw [this]
  ring

中文:
定理 sub_pow
  条件: [交换环 R] (x y : R) (n : 自然数)
  证明: by
  rw [sub_eq_add_neg]; rw [add_pow]
  congr! 1 with m hm
  have : (-1 : R) ^ (n - m) = (-1) ^ (n + m) := by
    rw [mem_range] at hm
    simp [show n + m = n - m + 2 * m by lia, pow_add]
  rw [neg_pow]; rw [this]
  ring

Depends on / 依赖: add_pow, mem_range, neg_pow, pow_add, sub_eq_add_neg
-/
theorem sub_pow [CommRing R] (x y : R) (n : Nat) :
    (x - y) ^ n = ∑ m in range (n + 1), (-1) ^ (m + n) * x ^ m * y ^ (n - m) * n.choose m := by
  rw [sub_eq_add_neg]; rw [add_pow]
  congr! 1 with m hm
  have : (-1 : R) ^ (n - m) = (-1) ^ (n + m) := by
    rw [mem_range] at hm
    simp [show n + m = n - m + 2 * m by lia, pow_add]
  rw [neg_pow]; rw [this]
  ring

namespace Nat

/--
theorem `sum_range_choose` / 定理 `sum_range_choose`

English:
theorem sum_range_choose
  given: (n : Nat)
  statement: (∑ m in range (n + 1), n.choose m) = 2 ^ n
  proof: by
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this

中文:
定理 sum_range_choose
  条件: (n : 自然数)
  结论: (∑ m in range (n + 1), n.choose m) = 2 ^ n
  证明: by
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this

Depends on / 依赖: add_pow, one_add_one_eq_two
-/
theorem sum_range_choose (n : Nat) : (∑ m in range (n + 1), n.choose m) = 2 ^ n := by
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this

/--
theorem `sum_range_choose_halfway` / 定理 `sum_range_choose_halfway`

English:
theorem sum_range_choose_halfway
  given: (m : Nat)
  statement: (∑ i in range (m + 1), (2 * m + 1).choose i) = 4 ^ m
  proof: have : (∑ i in range (m + 1), (2 * m + 1).choose (2 * m + 1 - i)) =
      ∑ i in range (m + 1), (2 * m + 1).choose i :=
sum_congr rfl fun i hi => choose_symm by linarith [mem_range.1 hi]
mul_right_injective₀ two_ne_zero
    calc
      (2 * ∑ i in range (m + 1), (2 * m + 1).choose i) =
          (∑ i

中文:
定理 sum_range_choose_halfway
  条件: (m : 自然数)
  结论: (∑ i in range (m + 1), (2 * m + 1).choose i) = 4 ^ m
  证明: have : (∑ i in range (m + 1), (2 * m + 1).choose (2 * m + 1 - i)) =
      ∑ i in range (m + 1), (2 * m + 1).choose i :=
sum_congr rfl fun i hi => choose_symm by linarith [mem_range.1 hi]
mul_right_injective₀ two_ne_zero
    calc
      (2 * ∑ i in range (m + 1), (2 * m + 1).choose i) =
          (∑ i

Depends on / 依赖: choose_symm, mem_range, sum_congr, two_mul, two_ne_zero
-/
theorem sum_range_choose_halfway (m : Nat) : (∑ i in range (m + 1), (2 * m + 1).choose i) = 4 ^ m :=
  have : (∑ i in range (m + 1), (2 * m + 1).choose (2 * m + 1 - i)) =
      ∑ i in range (m + 1), (2 * m + 1).choose i :=
sum_congr rfl fun i hi => choose_symm by linarith [mem_range.1 hi]
mul_right_injective₀ two_ne_zero
    calc
      (2 * ∑ i in range (m + 1), (2 * m + 1).choose i) =
          (∑ i in range (m + 1), (2 * m + 1).choose i) +
            ∑ i in range (m + 1), (2 * m + 1).choose (2 * m + 1 - i) := by rw [two_mul, this]
      _ = (∑ i in range (m + 1), (2 * m + 1).choose i) +
            ∑ i in Ico (m + 1) (2 * m + 2), (2 * m + 1).choose i := by
        rw [range_eq_Ico]; rw [sum_Ico_reflect _ _ (by lia)]
        congr
        lia
      _ = ∑ i in range (2 * m + 2), (2 * m + 1).choose i := sum_range_add_sum_Ico _ (by lia)
      _ = 2 ^ (2 * m + 1) := sum_range_choose (2 * m + 1)
      _ = 2 * 4 ^ m := by rw [pow_succ, pow_mul, mul_comm]; rfl

/--
theorem `choose_middle_le_pow` / 定理 `choose_middle_le_pow`

English:
theorem choose_middle_le_pow
  given: (n : Nat)
  statement: (2 * n + 1).choose n <= 4 ^ n
  proof: by
  have t : (2 * n + 1).choose n <= ∑ i in range (n + 1), (2 * n + 1).choose i :=
    single_le_sum (fun x _ => by lia) (self_mem_range_succ n)
  simpa [sum_range_choose_halfway n] using t

中文:
定理 choose_middle_le_pow
  条件: (n : 自然数)
  结论: (2 * n + 1).choose n <= 4 ^ n
  证明: by
  have t : (2 * n + 1).choose n <= ∑ i in range (n + 1), (2 * n + 1).choose i :=
    single_le_sum (fun x _ => by lia) (self_mem_range_succ n)
  simpa [sum_range_choose_halfway n] using t

Depends on / 依赖: self_mem_range_succ, single_le_sum, sum_range_choose_halfway
-/
theorem choose_middle_le_pow (n : Nat) : (2 * n + 1).choose n <= 4 ^ n := by
  have t : (2 * n + 1).choose n <= ∑ i in range (n + 1), (2 * n + 1).choose i :=
    single_le_sum (fun x _ => by lia) (self_mem_range_succ n)
  simpa [sum_range_choose_halfway n] using t

/--
theorem `four_pow_le_two_mul_add_one_mul_central_binom` / 定理 `four_pow_le_two_mul_add_one_mul_central_binom`

English:
theorem four_pow_le_two_mul_add_one_mul_central_binom
  given: (n : Nat)
  proof: calc
    4 ^ n = (1 + 1) ^ (2 * n) := by simp [pow_mul]
    _ = ∑ m in range (2 * n + 1), (2 * n).choose m := by simp [-Nat.reduceAdd, add_pow]
    _ <= ∑ _ in range (2 * n + 1), (2 * n).choose (2 * n / 2) := by gcongr; apply choose_le_middle
    _ = (2 * n + 1) * choose (2 * n) n := by simp

中文:
定理 four_pow_le_two_mul_add_one_mul_central_binom
  条件: (n : 自然数)
  证明: calc
    4 ^ n = (1 + 1) ^ (2 * n) := by simp [pow_mul]
    _ = ∑ m in range (2 * n + 1), (2 * n).choose m := by simp [-Nat.reduceAdd, add_pow]
    _ <= ∑ _ in range (2 * n + 1), (2 * n).choose (2 * n / 2) := by gcongr; apply choose_le_middle
    _ = (2 * n + 1) * choose (2 * n) n := by simp

Depends on / 依赖: Nat.reduceAdd, add_pow, choose_le_middle, pow_mul, reduceAdd
-/
theorem four_pow_le_two_mul_add_one_mul_central_binom (n : Nat) :
    4 ^ n <= (2 * n + 1) * (2 * n).choose n :=
  calc
    4 ^ n = (1 + 1) ^ (2 * n) := by simp [pow_mul]
    _ = ∑ m in range (2 * n + 1), (2 * n).choose m := by simp [-Nat.reduceAdd, add_pow]
    _ <= ∑ _ in range (2 * n + 1), (2 * n).choose (2 * n / 2) := by gcongr; apply choose_le_middle
    _ = (2 * n + 1) * choose (2 * n) n := by simp

/--
theorem `sum_Icc_choose` / 定理 `sum_Icc_choose`

English:
theorem sum_Icc_choose
  given: (n k : Nat)
  statement: ∑ m in Icc k n, m.choose k = (n + 1).choose (k + 1)
  proof: by
  rcases lt_or_ge n k with h | h
  · rw [choose_eq_zero_of_lt (by lia), Icc_eq_empty_of_lt h, sum_empty]
  · induction n, h using le_induction with
    | base => simp
    | succ n _ ih =>
      rw [← Ico_insert_right (by lia)]; rw [sum_insert (by simp)]; rw [Ico_add_one_right_eq_Icc]; rw [ih]; rw

中文:
定理 sum_Icc_choose
  条件: (n k : 自然数)
  结论: ∑ m in 闭区间 k n, m.choose k = (n + 1).choose (k + 1)
  证明: by
  rcases lt_or_ge n k with h | h
  · rw [choose_eq_zero_of_lt (by lia), Icc_eq_empty_of_lt h, sum_empty]
  · induction n, h using le_induction with
    | base => simp
    | succ n _ ih =>
      rw [← Ico_insert_right (by lia)]; rw [sum_insert (by simp)]; rw [Ico_add_one_right_eq_Icc]; rw [ih]; rw

Depends on / 依赖: Icc_eq_empty_of_lt, Ico_add_one_right_eq_Icc, Ico_insert_right, choose_eq_zero_of_lt, choose_succ_succ, le_induction, lt_or_ge, sum_empty, sum_insert
-/
theorem sum_Icc_choose (n k : Nat) : ∑ m in Icc k n, m.choose k = (n + 1).choose (k + 1) := by
  rcases lt_or_ge n k with h | h
  · rw [choose_eq_zero_of_lt (by lia), Icc_eq_empty_of_lt h, sum_empty]
  · induction n, h using le_induction with
    | base => simp
    | succ n _ ih =>
      rw [← Ico_insert_right (by lia)]; rw [sum_insert (by simp)]; rw [Ico_add_one_right_eq_Icc]; rw [ih]; rw [choose_succ_succ' (n + 1)]

/--
lemma `sum_range_add_choose` / 引理 `sum_range_add_choose`

English:
lemma sum_range_add_choose
  given: (n k : Nat)
  proof: by
  rw [← sum_Icc_choose]; rw [range_eq_Ico]
  convert! (sum_map _ (addRightEmbedding k) (·.choose k)).symm using 2
  rw [map_add_right_Ico]; rw [zero_add]; rw [add_right_comm]; rw [Ico_add_one_right_eq_Icc]

中文:
引理 sum_range_add_choose
  条件: (n k : 自然数)
  证明: by
  rw [← sum_Icc_choose]; rw [range_eq_Ico]
  convert! (sum_map _ (addRightEmbedding k) (·.choose k)).symm using 2
  rw [map_add_right_Ico]; rw [zero_add]; rw [add_right_comm]; rw [Ico_add_one_right_eq_Icc]

Depends on / 依赖: Ico_add_one_right_eq_Icc, addRightEmbedding, add_right_comm, convert, map_add_right_Ico, range_eq_Ico, sum_Icc_choose, sum_map, zero_add
-/
lemma sum_range_add_choose (n k : Nat) :
    ∑ i in Finset.range (n + 1), (i + k).choose k = (n + k + 1).choose (k + 1) := by
  rw [← sum_Icc_choose]; rw [range_eq_Ico]
  convert! (sum_map _ (addRightEmbedding k) (·.choose k)).symm using 2
  rw [map_add_right_Ico]; rw [zero_add]; rw [add_right_comm]; rw [Ico_add_one_right_eq_Icc]

/--
theorem `sum_range_mul_choose` / 定理 `sum_range_mul_choose`

English:
theorem sum_range_mul_choose
  given: (n : Nat)
  proof: by
  by_cases h : n = 0
  · simp [h]
  apply (mul_right_inj' two_ne_zero).1
  calc
    2 * ∑ i in Finset.range (n + 1), i * n.choose i
      = ∑ i in Finset.range (n + 1), (n - i) * n.choose (n - i)
        + ∑ i in Finset.range (n + 1), i * n.choose i := by
      rw [two_mul]; rw [← sum_flip]
    _

中文:
定理 sum_range_mul_choose
  条件: (n : 自然数)
  证明: by
  by_cases h : n = 0
  · simp [h]
  apply (mul_right_inj' two_ne_zero).1
  calc
    2 * ∑ i in Finset.range (n + 1), i * n.choose i
      = ∑ i in Finset.range (n + 1), (n - i) * n.choose (n - i)
        + ∑ i in Finset.range (n + 1), i * n.choose i := by
      rw [two_mul]; rw [← sum_flip]
    _

Depends on / 依赖: Finset, Finset.range, choose_symm, mem_range_succ_iff, mem_range_succ_iff.mp, mul_right_inj, n.choose, sum_add_, sum_flip, two_mul, two_ne_zero
-/
theorem sum_range_mul_choose (n : Nat) :
    ∑ i in Finset.range (n + 1), i * (n.choose i) = n * 2 ^ (n - 1) := by
  by_cases h : n = 0
  · simp [h]
  apply (mul_right_inj' two_ne_zero).1
  calc
    2 * ∑ i in Finset.range (n + 1), i * n.choose i
      = ∑ i in Finset.range (n + 1), (n - i) * n.choose (n - i)
        + ∑ i in Finset.range (n + 1), i * n.choose i := by
      rw [two_mul]; rw [← sum_flip]
    _ = ∑ i in Finset.range (n + 1), (n - i) * n.choose i
        + ∑ i in Finset.range (n + 1), i * n.choose i := by
      congr! 2 with _ h'
      rw [choose_symm (mem_range_succ_iff.mp h')]
    _ = ∑ i in Finset.range (n + 1), n * n.choose i := by
      rw [← sum_add_distrib]
      congr! 1 with _ h'
      rw [← add_mul]; rw [Nat.sub_add_cancel (mem_range_succ_iff.mp h')]
    _ = n * 2 ^ n := by
      rw [← mul_sum]; rw [Nat.sum_range_choose]
    _ = 2 * (n * 2 ^ (n - 1)) := by
      rw [← mul_assoc]; rw [mul_comm 2 n]; rw [mul_assoc]; rw [mul_pow_sub_one h]

/--
lemma `sum_range_multichoose` / 引理 `sum_range_multichoose`

English:
lemma sum_range_multichoose
  given: (n k : Nat)
  proof: by
  cases k with
  | zero => simp [Finset.sum_range_succ']
  | succ k => grind [multichoose_eq, choose_symm_of_eq_add, sum_range_add_choose]

中文:
引理 sum_range_multichoose
  条件: (n k : 自然数)
  证明: by
  cases k with
  | zero => simp [Finset.sum_range_succ']
  | succ k => grind [multichoose_eq, choose_symm_of_eq_add, sum_range_add_choose]

Depends on / 依赖: Finset, Finset.sum_range_succ, choose_symm_of_eq_add, multichoose_eq, sum_range_add_choose, sum_range_succ
-/
lemma sum_range_multichoose (n k : Nat) :
    ∑ i in Finset.range (n + 1), k.multichoose i = (n + k).choose k := by
  cases k with
  | zero => simp [Finset.sum_range_succ']
  | succ k => grind [multichoose_eq, choose_symm_of_eq_add, sum_range_add_choose]

end Nat

/--
theorem `Int.alternating_sum_range_choose_eq_choose` / 定理 `Int.alternating_sum_range_choose_eq_choose`

English:
theorem Int.alternating_sum_range_choose_eq_choose
  given: {n m : Nat}
  proof: by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [sum_range_succ]; rw [hm]; rw [choose_succ_succ]
    grind

中文:
定理 整数.alternating_sum_range_choose_eq_choose
  条件: {n m : 自然数}
  证明: by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [sum_range_succ]; rw [hm]; rw [choose_succ_succ]
    grind

Depends on / 依赖: choose_succ_succ, sum_range_succ
-/
theorem Int.alternating_sum_range_choose_eq_choose {n m : Nat} :
    (∑ k in range (m + 1), ((-1) ^ k * (n + 1).choose k : Int)) = (-1) ^ m * n.choose m := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [sum_range_succ]; rw [hm]; rw [choose_succ_succ]
    grind

/--
theorem `Int.alternating_sum_range_choose` / 定理 `Int.alternating_sum_range_choose`

English:
theorem Int.alternating_sum_range_choose
  given: {n : Nat}
  proof: by
  cases n with
  | zero => simp
  | succ n => simp [Int.alternating_sum_range_choose_eq_choose]

中文:
定理 整数.alternating_sum_range_choose
  条件: {n : 自然数}
  证明: by
  cases n with
  | zero => simp
  | succ n => simp [Int.alternating_sum_range_choose_eq_choose]

Depends on / 依赖: Int.alternating_sum_range_choose_eq_choose, alternating_sum_range_choose_eq_choose
-/
theorem Int.alternating_sum_range_choose {n : Nat} :
    (∑ m in range (n + 1), ((-1) ^ m * n.choose m : Int)) = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n => simp [Int.alternating_sum_range_choose_eq_choose]

/--
theorem `Int.alternating_sum_range_choose_of_ne` / 定理 `Int.alternating_sum_range_choose_of_ne`

English:
theorem Int.alternating_sum_range_choose_of_ne
  given: {n : Nat} (h0 : n != 0)
  proof: by
  rw [Int.alternating_sum_range_choose]; rw [if_neg h0]

中文:
定理 整数.alternating_sum_range_choose_of_ne
  条件: {n : 自然数} (h0 : n != 0)
  证明: by
  rw [Int.alternating_sum_range_choose]; rw [if_neg h0]

Depends on / 依赖: Int.alternating_sum_range_choose, alternating_sum_range_choose, if_neg
-/
theorem Int.alternating_sum_range_choose_of_ne {n : Nat} (h0 : n != 0) :
    (∑ m in range (n + 1), ((-1) ^ m * n.choose m : Int)) = 0 := by
  rw [Int.alternating_sum_range_choose]; rw [if_neg h0]

namespace Finset

/--
theorem `sum_powerset_apply_card` / 定理 `sum_powerset_apply_card`

English:
theorem sum_powerset_apply_card
  given: {α β : Type*} [AddCommMonoid α] (f : Nat -> α) {x : Finset β}
  proof: by
  trans ∑ m in range (#x + 1), ∑ j in x.powerset with #j = m, f #j
  · refine (sum_fiberwise_of_maps_to ?_ _).symm
    intro y hy
    rw [mem_range]; rw [Nat.lt_succ_iff]
    rw [mem_powerset] at hy
    exact card_le_card hy
  · refine sum_congr rfl fun y _ => ?_
    rw [← card_powersetCard]; rw 

中文:
定理 sum_powerset_apply_card
  条件: {α β : 类型} [加法交换幺半群 α] (f : 自然数 -> α) {x : 有限集 β}
  证明: by
  trans ∑ m in range (#x + 1), ∑ j in x.powerset with #j = m, f #j
  · refine (sum_fiberwise_of_maps_to ?_ _).symm
    intro y hy
    rw [mem_range]; rw [Nat.lt_succ_iff]
    rw [mem_powerset] at hy
    exact card_le_card hy
  · refine sum_congr rfl fun y _ => ?_
    rw [← card_powersetCard]; rw 

Depends on / 依赖: Nat.lt_succ_iff, card_le_card, card_powersetCard, lt_succ_iff, mem_powerset, mem_powersetCard, mem_range, powerset, powersetCard_eq_filter, powersetCard_eq_filter.symm, sum_congr, sum_const, sum_fiberwise_of_maps_to, x.powerset
-/
theorem sum_powerset_apply_card {α β : Type*} [AddCommMonoid α] (f : Nat -> α) {x : Finset β} :
    ∑ m in x.powerset, f #m = ∑ m in range (#x + 1), (#x).choose m • f m := by
  trans ∑ m in range (#x + 1), ∑ j in x.powerset with #j = m, f #j
  · refine (sum_fiberwise_of_maps_to ?_ _).symm
    intro y hy
    rw [mem_range]; rw [Nat.lt_succ_iff]
    rw [mem_powerset] at hy
    exact card_le_card hy
  · refine sum_congr rfl fun y _ => ?_
    rw [← card_powersetCard]; rw [← sum_const]
    refine sum_congr powersetCard_eq_filter.symm fun z hz => ?_
    rw [(mem_powersetCard.1 hz).2]

/--
theorem `sum_powerset_neg_one_pow_card` / 定理 `sum_powerset_neg_one_pow_card`

English:
theorem sum_powerset_neg_one_pow_card
  given: {α : Type*} [DecidableEq α] {x : Finset α}
  proof: by
  rw [sum_powerset_apply_card]
  simp only [nsmul_eq_mul', ← card_eq_zero, Int.alternating_sum_range_choose]

中文:
定理 sum_powerset_neg_one_pow_card
  条件: {α : 类型} [DecidableEq α] {x : 有限集 α}
  证明: by
  rw [sum_powerset_apply_card]
  simp only [nsmul_eq_mul', ← card_eq_zero, Int.alternating_sum_range_choose]

Depends on / 依赖: Int.alternating_sum_range_choose, alternating_sum_range_choose, card_eq_zero, nsmul_eq_mul, sum_powerset_apply_card
-/
theorem sum_powerset_neg_one_pow_card {α : Type*} [DecidableEq α] {x : Finset α} :
    (∑ m in x.powerset, (-1 : Int) ^ #m) = if x = ∅ then 1 else 0 := by
  rw [sum_powerset_apply_card]
  simp only [nsmul_eq_mul', ← card_eq_zero, Int.alternating_sum_range_choose]

/--
theorem `sum_powerset_neg_one_pow_card_of_nonempty` / 定理 `sum_powerset_neg_one_pow_card_of_nonempty`

English:
theorem sum_powerset_neg_one_pow_card_of_nonempty
  given: {α : Type*} {x : Finset α} (h0 : x.Nonempty)
  proof: by
  classical
  rw [sum_powerset_neg_one_pow_card]
  exact if_neg (nonempty_iff_ne_empty.mp h0)

中文:
定理 sum_powerset_neg_one_pow_card_of_nonempty
  条件: {α : 类型} {x : 有限集 α} (h0 : x.非空)
  证明: by
  classical
  rw [sum_powerset_neg_one_pow_card]
  exact if_neg (nonempty_iff_ne_empty.mp h0)

Depends on / 依赖: classical, if_neg, nonempty_iff_ne_empty, nonempty_iff_ne_empty.mp, sum_powerset_neg_one_pow_card
-/
theorem sum_powerset_neg_one_pow_card_of_nonempty {α : Type*} {x : Finset α} (h0 : x.Nonempty) :
    (∑ m in x.powerset, (-1 : Int) ^ #m) = 0 := by
  classical
  rw [sum_powerset_neg_one_pow_card]
  exact if_neg (nonempty_iff_ne_empty.mp h0)

variable [NonAssocSemiring R]

@[to_additive sum_choose_succ_nsmul]
/--
theorem `prod_pow_choose_succ` / 定理 `prod_pow_choose_succ`

English:
theorem prod_pow_choose_succ
  given: {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M) (n : Nat)
  proof: by
  have A : (∏ i in range (n + 1), f (i + 1) (n - i) ^ (n.choose (i + 1))) * f 0 (n + 1) =
      ∏ i in range (n + 1), f i (n + 1 - i) ^ (n.choose i) := by
    rw [prod_range_succ]; rw [prod_range_succ']; simp
  rw [prod_range_succ']
  simpa [choose_succ_succ, pow_add, prod_mul_distrib, A, mul_ass

中文:
定理 prod_pow_choose_succ
  条件: {M : 类型} [交换幺半群 M] (f : 自然数 -> 自然数 -> M) (n : 自然数)
  证明: by
  have A : (∏ i in range (n + 1), f (i + 1) (n - i) ^ (n.choose (i + 1))) * f 0 (n + 1) =
      ∏ i in range (n + 1), f i (n + 1 - i) ^ (n.choose i) := by
    rw [prod_range_succ]; rw [prod_range_succ']; simp
  rw [prod_range_succ']
  simpa [choose_succ_succ, pow_add, prod_mul_distrib, A, mul_ass

Depends on / 依赖: choose_succ_succ, mul_assoc, mul_comm, n.choose, pow_add, prod_mul_distrib, prod_range_succ
-/
theorem prod_pow_choose_succ {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M) (n : Nat) :
    (∏ i in range (n + 2), f i (n + 1 - i) ^ (n + 1).choose i) =
      (∏ i in range (n + 1), f i (n + 1 - i) ^ n.choose i) *
        ∏ i in range (n + 1), f (i + 1) (n - i) ^ n.choose i := by
  have A : (∏ i in range (n + 1), f (i + 1) (n - i) ^ (n.choose (i + 1))) * f 0 (n + 1) =
      ∏ i in range (n + 1), f i (n + 1 - i) ^ (n.choose i) := by
    rw [prod_range_succ]; rw [prod_range_succ']; simp
  rw [prod_range_succ']
  simpa [choose_succ_succ, pow_add, prod_mul_distrib, A, mul_assoc] using mul_comm _ _

@[to_additive sum_antidiagonal_choose_succ_nsmul]
/--
theorem `prod_antidiagonal_pow_choose_succ` / 定理 `prod_antidiagonal_pow_choose_succ`

English:
theorem prod_antidiagonal_pow_choose_succ
  given: {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M) (n : Nat)
  proof: by
  simp only [Nat.prod_antidiagonal_eq_prod_range_succ_mk, prod_pow_choose_succ]
  have : forall i in range (n + 1), i <= n := fun i hi => by simpa [Nat.lt_succ_iff] using hi
  congr 1
  · refine prod_congr rfl fun i hi => ?_
    rw [tsub_add_eq_add_tsub (this _ hi)]
  · refine prod_congr rfl fun 

中文:
定理 prod_antidiagonal_pow_choose_succ
  条件: {M : 类型} [交换幺半群 M] (f : 自然数 -> 自然数 -> M) (n : 自然数)
  证明: by
  simp only [Nat.prod_antidiagonal_eq_prod_range_succ_mk, prod_pow_choose_succ]
  have : forall i in range (n + 1), i <= n := fun i hi => by simpa [Nat.lt_succ_iff] using hi
  congr 1
  · refine prod_congr rfl fun i hi => ?_
    rw [tsub_add_eq_add_tsub (this _ hi)]
  · refine prod_congr rfl fun 

Depends on / 依赖: Nat.lt_succ_iff, Nat.prod_antidiagonal_eq_prod_range_succ_mk, choose_symm, lt_succ_iff, prod_antidiagonal_eq_prod_range_succ_mk, prod_congr, prod_pow_choose_succ, tsub_add_eq_add_tsub
-/
theorem prod_antidiagonal_pow_choose_succ {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M) (n : Nat) :
    (∏ ij in antidiagonal (n + 1), f ij.1 ij.2 ^ (n + 1).choose ij.1) =
      (∏ ij in antidiagonal n, f ij.1 (ij.2 + 1) ^ n.choose ij.1) *
        ∏ ij in antidiagonal n, f (ij.1 + 1) ij.2 ^ n.choose ij.2 := by
  simp only [Nat.prod_antidiagonal_eq_prod_range_succ_mk, prod_pow_choose_succ]
  have : forall i in range (n + 1), i <= n := fun i hi => by simpa [Nat.lt_succ_iff] using hi
  congr 1
  · refine prod_congr rfl fun i hi => ?_
    rw [tsub_add_eq_add_tsub (this _ hi)]
  · refine prod_congr rfl fun i hi => ?_
    rw [choose_symm (this _ hi)]

/--
theorem `sum_choose_succ_mul` / 定理 `sum_choose_succ_mul`

English:
theorem sum_choose_succ_mul
  given: (f : Nat -> Nat -> R) (n : Nat)
  proof: by
  simpa only [nsmul_eq_mul] using sum_choose_succ_nsmul f n

中文:
定理 sum_choose_succ_mul
  条件: (f : 自然数 -> 自然数 -> R) (n : 自然数)
  证明: by
  simpa only [nsmul_eq_mul] using sum_choose_succ_nsmul f n

Depends on / 依赖: nsmul_eq_mul, sum_choose_succ_nsmul
-/
theorem sum_choose_succ_mul (f : Nat -> Nat -> R) (n : Nat) :
    (∑ i in range (n + 2), ((n + 1).choose i : R) * f i (n + 1 - i)) =
      (∑ i in range (n + 1), (n.choose i : R) * f i (n + 1 - i)) +
        ∑ i in range (n + 1), (n.choose i : R) * f (i + 1) (n - i) := by
  simpa only [nsmul_eq_mul] using sum_choose_succ_nsmul f n

/--
theorem `sum_antidiagonal_choose_succ_mul` / 定理 `sum_antidiagonal_choose_succ_mul`

English:
theorem sum_antidiagonal_choose_succ_mul
  given: (f : Nat -> Nat -> R) (n : Nat)
  proof: by
  simpa only [nsmul_eq_mul] using sum_antidiagonal_choose_succ_nsmul f n

中文:
定理 sum_antidiagonal_choose_succ_mul
  条件: (f : 自然数 -> 自然数 -> R) (n : 自然数)
  证明: by
  simpa only [nsmul_eq_mul] using sum_antidiagonal_choose_succ_nsmul f n

Depends on / 依赖: nsmul_eq_mul, sum_antidiagonal_choose_succ_nsmul
-/
theorem sum_antidiagonal_choose_succ_mul (f : Nat -> Nat -> R) (n : Nat) :
    (∑ ij in antidiagonal (n + 1), ((n + 1).choose ij.1 : R) * f ij.1 ij.2) =
      (∑ ij in antidiagonal n, (n.choose ij.1 : R) * f ij.1 (ij.2 + 1)) +
        ∑ ij in antidiagonal n, (n.choose ij.2 : R) * f (ij.1 + 1) ij.2 := by
  simpa only [nsmul_eq_mul] using sum_antidiagonal_choose_succ_nsmul f n

/--
theorem `sum_antidiagonal_choose_add` / 定理 `sum_antidiagonal_choose_add`

English:
theorem sum_antidiagonal_choose_add
  given: (d n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n hn => rw [Nat.sum_antidiagonal_succ, hn, Nat.choose_succ_succ (d + (n + 1)), ← add_assoc]

中文:
定理 sum_antidiagonal_choose_add
  条件: (d n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n hn => rw [Nat.sum_antidiagonal_succ, hn, Nat.choose_succ_succ (d + (n + 1)), ← add_assoc]

Depends on / 依赖: Nat.choose_succ_succ, Nat.sum_antidiagonal_succ, add_assoc, choose_succ_succ, sum_antidiagonal_succ
-/
theorem sum_antidiagonal_choose_add (d n : Nat) :
    (∑ ij in antidiagonal n, (d + ij.2).choose d) = (d + n + 1).choose (d + 1) := by
  induction n with
  | zero => simp
  | succ n hn => rw [Nat.sum_antidiagonal_succ, hn, Nat.choose_succ_succ (d + (n + 1)), ← add_assoc]

end Finset
