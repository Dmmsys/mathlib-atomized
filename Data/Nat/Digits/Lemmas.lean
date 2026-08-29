/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Digits of a natural number

This provides lemma about the digits of natural numbers.
-/

public section

namespace Nat

variable {n : Nat}

/--
theorem `ofDigits_eq_sum_mapIdx_aux` / 定理 `ofDigits_eq_sum_mapIdx_aux`

English:
theorem ofDigits_eq_sum_mapIdx_aux
  given: (b : Nat) (l : List Nat)
  proof: by
  suffices
    l.zipWith (fun a i : Nat => a * b ^ (i + 1)) (List.range l.length) =
      l.zipWith (fun a i => b * (a * b ^ i)) (List.range l.length)
    by simp [this]
  congr; ext; ring

中文:
定理 ofDigits_eq_sum_mapIdx_aux
  条件: (b : 自然数) (l : List 自然数)
  证明: by
  suffices
    l.zipWith (fun a i : Nat => a * b ^ (i + 1)) (List.range l.length) =
      l.zipWith (fun a i => b * (a * b ^ i)) (List.range l.length)
    by simp [this]
  congr; ext; ring

Depends on / 依赖: List.range, l.length, l.zipWith, length, zipWith
-/
theorem ofDigits_eq_sum_mapIdx_aux (b : Nat) (l : List Nat) :
    (l.zipWith ((fun a i : Nat => a * b ^ (i + 1))) (List.range l.length)).sum =
      b * (l.zipWith (fun a i => a * b ^ i) (List.range l.length)).sum := by
  suffices
    l.zipWith (fun a i : Nat => a * b ^ (i + 1)) (List.range l.length) =
      l.zipWith (fun a i => b * (a * b ^ i)) (List.range l.length)
    by simp [this]
  congr; ext; ring

/--
theorem `ofDigits_eq_sum_mapIdx` / 定理 `ofDigits_eq_sum_mapIdx`

English:
theorem ofDigits_eq_sum_mapIdx
  given: (b : Nat) (L : List Nat)
  proof: by
  rw [List.mapIdx_eq_zipIdx_map]; rw [List.zipIdx_eq_zip_range']; rw [List.map_zip_eq_zipWith]; rw [ofDigits_eq_foldr]; rw [← List.range_eq_range']
  induction L with
  | nil => simp
  | cons hd tl hl =>
    simpa [List.range_succ_eq_map, List.zipWith_map_right, ofDigits_eq_sum_mapIdx_aux] using!

中文:
定理 ofDigits_eq_sum_mapIdx
  条件: (b : 自然数) (L : List 自然数)
  证明: by
  rw [List.mapIdx_eq_zipIdx_map]; rw [List.zipIdx_eq_zip_range']; rw [List.map_zip_eq_zipWith]; rw [ofDigits_eq_foldr]; rw [← List.range_eq_range']
  induction L with
  | nil => simp
  | cons hd tl hl =>
    simpa [List.range_succ_eq_map, List.zipWith_map_right, ofDigits_eq_sum_mapIdx_aux] using!

Depends on / 依赖: List.mapIdx_eq_zipIdx_map, List.map_zip_eq_zipWith, List.range_eq_range, List.range_succ_eq_map, List.zipIdx_eq_zip_range, List.zipWith_map_right, Or.inl, mapIdx_eq_zipIdx_map, map_zip_eq_zipWith, ofDigits_eq_foldr, ofDigits_eq_sum_mapIdx_aux, range_eq_range, range_succ_eq_map, zipIdx_eq_zip_range, zipWith_map_right
-/
theorem ofDigits_eq_sum_mapIdx (b : Nat) (L : List Nat) :
    ofDigits b L = (L.mapIdx fun i a => a * b ^ i).sum := by
  rw [List.mapIdx_eq_zipIdx_map]; rw [List.zipIdx_eq_zip_range']; rw [List.map_zip_eq_zipWith]; rw [ofDigits_eq_foldr]; rw [← List.range_eq_range']
  induction L with
  | nil => simp
  | cons hd tl hl =>
    simpa [List.range_succ_eq_map, List.zipWith_map_right, ofDigits_eq_sum_mapIdx_aux] using!
      Or.inl hl


/--
theorem `length_digits` / 定理 `length_digits`

English:
theorem length_digits
  given: (b n : Nat) (hb : 1 < b) (hn : n != 0)
  proof: by
  induction n using Nat.strong_induction_on with | _ n IH
  rw [digits_eq_cons_digits_div hb hn]; rw [List.length]
  by_cases h : n / b = 0
  · simp [h]
    aesop
  · have : n / b < n := div_lt_self (Nat.pos_of_ne_zero hn) hb
    rw [IH _ this h]; rw [log_div_base]; rw [tsub_add_cancel_of_le]
   

中文:
定理 length_digits
  条件: (b n : 自然数) (hb : 1 < b) (hn : n != 0)
  证明: by
  induction n using Nat.strong_induction_on with | _ n IH
  rw [digits_eq_cons_digits_div hb hn]; rw [List.length]
  by_cases h : n / b = 0
  · simp [h]
    aesop
  · have : n / b < n := div_lt_self (Nat.pos_of_ne_zero hn) hb
    rw [IH _ this h]; rw [log_div_base]; rw [tsub_add_cancel_of_le]
   

Depends on / 依赖: List.length, Nat.pos_of_ne_zero, Nat.strong_induction_on, Nat.succ_le_of_lt, contrapose, digits_eq_cons_digits_div, div_eq_of_lt, div_lt_self, length, log_div_base, log_pos, pos_of_ne_zero, strong_induction_on, succ_le_of_lt, tsub_add_cancel_of_le
-/
theorem length_digits (b n : Nat) (hb : 1 < b) (hn : n != 0) :
    (b.digits n).length = b.log n + 1 := by
  induction n using Nat.strong_induction_on with | _ n IH
  rw [digits_eq_cons_digits_div hb hn]; rw [List.length]
  by_cases h : n / b = 0
  · simp [h]
    aesop
  · have : n / b < n := div_lt_self (Nat.pos_of_ne_zero hn) hb
    rw [IH _ this h]; rw [log_div_base]; rw [tsub_add_cancel_of_le]
    refine Nat.succ_le_of_lt (log_pos hb ?_)
    contrapose! h
    exact div_eq_of_lt h

@[deprecated (since := "2026-03-18")] alias digits_len := length_digits

/--
theorem `digits_length_le_iff` / 定理 `digits_length_le_iff`

English:
theorem digits_length_le_iff
  given: {b k : Nat} (hb : 1 < b) (n : Nat)
  proof: by
  by_cases h : n = 0
  · have : 0 < b ^ k := by positivity
    simpa [h]
  rw [length_digits b n hb h]; rw [← log_lt_iff_lt_pow hb h]
  exact add_one_le_iff

中文:
定理 digits_length_le_iff
  条件: {b k : 自然数} (hb : 1 < b) (n : 自然数)
  证明: by
  by_cases h : n = 0
  · have : 0 < b ^ k := by positivity
    simpa [h]
  rw [length_digits b n hb h]; rw [← log_lt_iff_lt_pow hb h]
  exact add_one_le_iff

Depends on / 依赖: add_one_le_iff, length_digits, log_lt_iff_lt_pow
-/
theorem digits_length_le_iff {b k : Nat} (hb : 1 < b) (n : Nat) :
    (b.digits n).length <= k ↔ n < b ^ k := by
  by_cases h : n = 0
  · have : 0 < b ^ k := by positivity
    simpa [h]
  rw [length_digits b n hb h]; rw [← log_lt_iff_lt_pow hb h]
  exact add_one_le_iff

/--
theorem `lt_digits_length_iff` / 定理 `lt_digits_length_iff`

English:
theorem lt_digits_length_iff
  given: {b k : Nat} (hb : 1 < b) (n : Nat)
  proof: by
  contrapose!
  exact digits_length_le_iff hb n

中文:
定理 lt_digits_length_iff
  条件: {b k : 自然数} (hb : 1 < b) (n : 自然数)
  证明: by
  contrapose!
  exact digits_length_le_iff hb n

Depends on / 依赖: contrapose, digits_length_le_iff
-/
theorem lt_digits_length_iff {b k : Nat} (hb : 1 < b) (n : Nat) :
    k < (b.digits n).length ↔ b ^ k <= n := by
  contrapose!
  exact digits_length_le_iff hb n

/--
theorem `getLast_digit_ne_zero` / 定理 `getLast_digit_ne_zero`

English:
theorem getLast_digit_ne_zero
  given: (b : Nat) {m : Nat} (hm : m != 0)
  proof: by
  rcases b with (_ | _ | b)
  · cases m
    · cases hm rfl
    · simp
  · simp
  revert hm
  induction m using Nat.strongRecOn with | ind n IH => ?_
  intro hn
  by_cases! hnb : n < b + 2
  · simpa only [digits_of_lt (b + 2) n hn hnb]
  · rw [digits_getLast n (le_add_left 2 b)]
    refine IH _ (N

中文:
定理 getLast_digit_ne_zero
  条件: (b : 自然数) {m : 自然数} (hm : m != 0)
  证明: by
  rcases b with (_ | _ | b)
  · cases m
    · cases hm rfl
    · simp
  · simp
  revert hm
  induction m using Nat.strongRecOn with | ind n IH => ?_
  intro hn
  by_cases! hnb : n < b + 2
  · simpa only [digits_of_lt (b + 2) n hn hnb]
  · rw [digits_getLast n (le_add_left 2 b)]
    refine IH _ (N

Depends on / 依赖: Nat.div_lt_self, Nat.div_pos, Nat.strongRecOn, bot_lt, digits_getLast, digits_of_lt, div_lt_self, div_pos, hn.bot_lt, le_add_left, one_lt_succ_succ, pos_iff_ne_zero, revert, strongRecOn, zero_lt_succ
-/
theorem getLast_digit_ne_zero (b : Nat) {m : Nat} (hm : m != 0) :
    (digits b m).getLast (digits_ne_nil_iff_ne_zero.mpr hm) != 0 := by
  rcases b with (_ | _ | b)
  · cases m
    · cases hm rfl
    · simp
  · simp
  revert hm
  induction m using Nat.strongRecOn with | ind n IH => ?_
  intro hn
  by_cases! hnb : n < b + 2
  · simpa only [digits_of_lt (b + 2) n hn hnb]
  · rw [digits_getLast n (le_add_left 2 b)]
    refine IH _ (Nat.div_lt_self hn.bot_lt (one_lt_succ_succ b)) ?_
    rw [← pos_iff_ne_zero]
    exact Nat.div_pos hnb (zero_lt_succ (succ b))

/--
theorem `digits_append_digits` / 定理 `digits_append_digits`

English:
theorem digits_append_digits
  given: {b m n : Nat} (hb : 0 < b)
  proof: by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hb) with (rfl | hb)
  · simp
  rw [← ofDigits_digits_append_digits]
  refine (digits_ofDigits b hb _ (fun l hl => ?_) (fun h_append => ?_)).symm
  · rcases (List.mem_append.mp hl) with (h | h) <;> exact digits_lt_base hb h
  · by_cases h : digits b m = [

中文:
定理 digits_append_digits
  条件: {b m n : 自然数} (hb : 0 < b)
  证明: by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hb) with (rfl | hb)
  · simp
  rw [← ofDigits_digits_append_digits]
  refine (digits_ofDigits b hb _ (fun l hl => ?_) (fun h_append => ?_)).symm
  · rcases (List.mem_append.mp hl) with (h | h) <;> exact digits_lt_base hb h
  · by_cases h : digits b m = [

Depends on / 依赖: List.append_nil, List.getLast_append_of_right_ne_nil, List.mem_append.mp, Nat.succ_le_of_lt, append_nil, digits, digits_lt_base, digits_ne_nil, digits_ne_nil_iff_ne_zero, digits_ne_nil_iff_ne_zero.mp, digits_ofDigits, eq_or_lt_of_le, getLast_append_of_right_ne_nil, getLast_digit_ne_zero, h_append, mem_append, ofDigits_digits_append_digits, succ_le_of_lt
-/
theorem digits_append_digits {b m n : Nat} (hb : 0 < b) :
    digits b n ++ digits b m = digits b (n + b ^ (digits b n).length * m) := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hb) with (rfl | hb)
  · simp
  rw [← ofDigits_digits_append_digits]
  refine (digits_ofDigits b hb _ (fun l hl => ?_) (fun h_append => ?_)).symm
  · rcases (List.mem_append.mp hl) with (h | h) <;> exact digits_lt_base hb h
  · by_cases h : digits b m = []
    · simp only [h, List.append_nil] at h_append ⊢
exact getLast_digit_ne_zero b digits_ne_nil_iff_ne_zero.mp h_append
    · exact (List.getLast_append_of_right_ne_nil _ _ h) ▸
          (getLast_digit_ne_zero _ <| digits_ne_nil_iff_ne_zero.mp h)

/--
theorem `digits_append_zeroes_append_digits` / 定理 `digits_append_zeroes_append_digits`

English:
theorem digits_append_zeroes_append_digits
  given: {b k m n : Nat} (hb : 1 < b) (hm : 0 < m)
  proof: by
  rw [List.append_assoc]; rw [← digits_base_pow_mul hb hm]
  simp only [digits_append_digits (zero_lt_of_lt hb), digits_inj_iff, add_right_inj]
  ring

中文:
定理 digits_append_zeroes_append_digits
  条件: {b k m n : 自然数} (hb : 1 < b) (hm : 0 < m)
  证明: by
  rw [List.append_assoc]; rw [← digits_base_pow_mul hb hm]
  simp only [digits_append_digits (zero_lt_of_lt hb), digits_inj_iff, add_right_inj]
  ring

Depends on / 依赖: List.append_assoc, add_right_inj, append_assoc, digits_append_digits, digits_base_pow_mul, digits_inj_iff, zero_lt_of_lt
-/
theorem digits_append_zeroes_append_digits {b k m n : Nat} (hb : 1 < b) (hm : 0 < m) :
    digits b n ++ List.replicate k 0 ++ digits b m =
    digits b (n + b ^ ((digits b n).length + k) * m) := by
  rw [List.append_assoc]; rw [← digits_base_pow_mul hb hm]
  simp only [digits_append_digits (zero_lt_of_lt hb), digits_inj_iff, add_right_inj]
  ring

/--
theorem `length_digits_le_length_digits_succ` / 定理 `length_digits_le_length_digits_succ`

English:
theorem length_digits_le_length_digits_succ
  given: (b n : Nat)
  proof: by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases le_or_gt b 1 with hb | hb
  · interval_cases b <;> simp +arith [digits_zero_succ', hn]
  simpa [length_digits, hb, hn] using log_mono_right (le_succ _)

@[deprecated (since := "2026-03-18")]
alias digits_len_le_digits_len_succ := l

中文:
定理 length_digits_le_length_digits_succ
  条件: (b n : 自然数)
  证明: by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases le_or_gt b 1 with hb | hb
  · interval_cases b <;> simp +arith [digits_zero_succ', hn]
  simpa [length_digits, hb, hn] using log_mono_right (le_succ _)

@[deprecated (since := "2026-03-18")]
alias digits_len_le_digits_len_succ := l

Depends on / 依赖: Decidable, Decidable.eq_or_ne, digits_zero_succ, eq_or_ne, interval_cases, le_or_gt, le_succ, length_digits, log_mono_right
-/
theorem length_digits_le_length_digits_succ (b n : Nat) :
    (digits b n).length <= (digits b (n + 1)).length := by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases le_or_gt b 1 with hb | hb
  · interval_cases b <;> simp +arith [digits_zero_succ', hn]
  simpa [length_digits, hb, hn] using log_mono_right (le_succ _)

@[deprecated (since := "2026-03-18")]
alias digits_len_le_digits_len_succ := length_digits_le_length_digits_succ

/--
theorem `le_length_digits_le` / 定理 `le_length_digits_le`

English:
theorem le_length_digits_le
  given: (b n m : Nat) (h : n <= m)
  statement: (digits b n).length <= (digits b m).length
  proof: monotone_nat_of_le_succ (length_digits_le_length_digits_succ b) h

@[deprecated (since := "2026-03-18")] alias le_digits_len_le := le_length_digits_le

中文:
定理 le_length_digits_le
  条件: (b n m : 自然数) (h : n <= m)
  结论: (digits b n).length <= (digits b m).length
  证明: monotone_nat_of_le_succ (length_digits_le_length_digits_succ b) h

@[deprecated (since := "2026-03-18")] alias le_digits_len_le := le_length_digits_le

Depends on / 依赖: length_digits_le_length_digits_succ, monotone_nat_of_le_succ
-/
theorem le_length_digits_le (b n m : Nat) (h : n <= m) : (digits b n).length <= (digits b m).length :=
  monotone_nat_of_le_succ (length_digits_le_length_digits_succ b) h

@[deprecated (since := "2026-03-18")] alias le_digits_len_le := le_length_digits_le

/--
theorem `pow_length_le_mul_ofDigits` / 定理 `pow_length_le_mul_ofDigits`

English:
theorem pow_length_le_mul_ofDigits
  given: {b : Nat} {l : List Nat} (hl : l != []) (hl2 : l.getLast hl != 0)
  proof: by
  rw [← List.dropLast_append_getLast hl]
  simp only [List.length_append, List.length, zero_add, List.length_dropLast, ofDigits_append,
    List.length_dropLast, ofDigits_singleton, add_comm (l.length - 1), pow_add, pow_one]
  apply Nat.mul_le_mul_left
  refine le_trans ?_ (Nat.le_add_left _ _)
 

中文:
定理 pow_length_le_mul_ofDigits
  条件: {b : 自然数} {l : List 自然数} (hl : l != []) (hl2 : l.getLast hl != 0)
  证明: by
  rw [← List.dropLast_append_getLast hl]
  simp only [List.length_append, List.length, zero_add, List.length_dropLast, ofDigits_append,
    List.length_dropLast, ofDigits_singleton, add_comm (l.length - 1), pow_add, pow_one]
  apply Nat.mul_le_mul_left
  refine le_trans ?_ (Nat.le_add_left _ _)
 

Depends on / 依赖: List.dropLast_append_getLast, List.length, List.length_append, List.length_dropLast, Nat.le_add_left, Nat.mul_le_mul_left, Nat.mul_one, add_comm, convert, dropLast_append_getLast, getLast, l.getLast, l.length, le_add_left, le_trans, length, length_append, length_dropLast, mul_le_mul_left, mul_one
-/
theorem pow_length_le_mul_ofDigits {b : Nat} {l : List Nat} (hl : l != []) (hl2 : l.getLast hl != 0) :
    (b + 2) ^ l.length <= (b + 2) * ofDigits (b + 2) l := by
  rw [← List.dropLast_append_getLast hl]
  simp only [List.length_append, List.length, zero_add, List.length_dropLast, ofDigits_append,
    List.length_dropLast, ofDigits_singleton, add_comm (l.length - 1), pow_add, pow_one]
  apply Nat.mul_le_mul_left
  refine le_trans ?_ (Nat.le_add_left _ _)
  have : 0 < l.getLast hl := by rwa [pos_iff_ne_zero]
  convert! Nat.mul_le_mul_left ((b + 2) ^ (l.length - 1)) this using 1
  rw [Nat.mul_one]

/--
theorem `base_pow_length_digits_le'` / 定理 `base_pow_length_digits_le'`

English:
theorem base_pow_length_digits_le'
  given: (b m : Nat) (hm : m != 0)
  proof: by
  have : digits (b + 2) m != [] := digits_ne_nil_iff_ne_zero.mpr hm
  convert! @pow_length_le_mul_ofDigits b (digits (b + 2) m) this (getLast_digit_ne_zero _ hm)
  rw [ofDigits_digits]

中文:
定理 base_pow_length_digits_le'
  条件: (b m : 自然数) (hm : m != 0)
  证明: by
  have : digits (b + 2) m != [] := digits_ne_nil_iff_ne_zero.mpr hm
  convert! @pow_length_le_mul_ofDigits b (digits (b + 2) m) this (getLast_digit_ne_zero _ hm)
  rw [ofDigits_digits]

Depends on / 依赖: convert, digits, digits_ne_nil_iff_ne_zero, digits_ne_nil_iff_ne_zero.mpr, getLast_digit_ne_zero, ofDigits_digits, pow_length_le_mul_ofDigits
-/
theorem base_pow_length_digits_le' (b m : Nat) (hm : m != 0) :
    (b + 2) ^ (digits (b + 2) m).length <= (b + 2) * m := by
  have : digits (b + 2) m != [] := digits_ne_nil_iff_ne_zero.mpr hm
  convert! @pow_length_le_mul_ofDigits b (digits (b + 2) m) this (getLast_digit_ne_zero _ hm)
  rw [ofDigits_digits]

/--
theorem `base_pow_length_digits_le` / 定理 `base_pow_length_digits_le`

English:
theorem base_pow_length_digits_le
  given: (b m : Nat) (hb : 1 < b)
  proof: by
  rcases b with (_ | _ | b) <;> simp_all [base_pow_length_digits_le']

中文:
定理 base_pow_length_digits_le
  条件: (b m : 自然数) (hb : 1 < b)
  证明: by
  rcases b with (_ | _ | b) <;> simp_all [base_pow_length_digits_le']

Depends on / 依赖: base_pow_length_digits_le
-/
theorem base_pow_length_digits_le (b m : Nat) (hb : 1 < b) :
    m != 0 -> b ^ (digits b m).length <= b * m := by
  rcases b with (_ | _ | b) <;> simp_all [base_pow_length_digits_le']

open Finset

/--
theorem `sub_one_mul_sum_div_pow_eq_sub_sum_digits` / 定理 `sub_one_mul_sum_div_pow_eq_sub_sum_digits`

English:
theorem sub_one_mul_sum_div_pow_eq_sub_sum_digits
  statement: {p : Nat}
  proof: by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · induction L with
    | nil => simp [ofDigits]
    | cons hd tl ih =>
      simp only [List.length_cons, List.sum_cons, self_div_pow_eq_ofDigits_drop _ _ h,
          digits_ofDigits p h (hd :: tl) h_lt (fun _ => h_ne_zero)]
    

中文:
定理 sub_one_mul_sum_div_pow_eq_sub_sum_digits
  结论: {p : 自然数}
  证明: by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · induction L with
    | nil => simp [ofDigits]
    | cons hd tl ih =>
      simp only [List.length_cons, List.sum_cons, self_div_pow_eq_ofDigits_drop _ _ h,
          digits_ofDigits p h (hd :: tl) h_lt (fun _ => h_ne_zero)]
    

Depends on / 依赖: List.drop, List.drop_length, List.length_cons, List.mem_cons_of_mem, List.sum_cons, Nat.cast_id, cast_id, digits_ofDigits, drop_length, h_lt, h_ne_zero, length_cons, mem_cons_of_mem, ofDigits, self_div_pow_eq_ofDigits_drop, sum_cons, sum_range_succ, trichotomous
-/
theorem sub_one_mul_sum_div_pow_eq_sub_sum_digits {p : Nat}
    (L : List Nat) {h_nonempty} (h_ne_zero : L.getLast h_nonempty != 0) (h_lt : forall l in L, l < p) :
    (p - 1) * ∑ i in range L.length, (ofDigits p L) / p ^ i.succ = (ofDigits p L) - L.sum := by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · induction L with
    | nil => simp [ofDigits]
    | cons hd tl ih =>
      simp only [List.length_cons, List.sum_cons, self_div_pow_eq_ofDigits_drop _ _ h,
          digits_ofDigits p h (hd :: tl) h_lt (fun _ => h_ne_zero)]
      simp only [ofDigits]
      rw [sum_range_succ]; rw [Nat.cast_id]
      simp only [List.drop, List.drop_length]
obtain rfl | h' := em tl = []
      · simp [ofDigits]
· have w₁' := fun l hl => h_lt l List.mem_cons_of_mem hd hl
        have w₂' := fun (h : tl != []) => (List.getLast_cons h) ▸ h_ne_zero
        have ih := ih (w₂' h') w₁'
        simp only [self_div_pow_eq_ofDigits_drop _ _ h, digits_ofDigits p h tl w₁' w₂',
          ← Nat.one_add] at ih
        have := sum_singleton (fun x => ofDigits p <| tl.drop x) tl.length
        rw [← Ico_succ_singleton]; rw [List.drop_length]; rw [ofDigits] at this
        have h₁ : 1 <= tl.length := List.length_pos_iff.mpr h'
        rw [← sum_range_add_sum_Ico _ <| h₁]; rw [← add_zero (∑ x in Ico _ _]; rw [ofDigits p (tl.drop x))]; rw [← this]; rw [sum_Ico_consecutive _ h₁ (le_add_right tl.length 1)]; rw [← sum_Ico_add _ 0 tl.length 1]; rw [Ico_zero_eq_range]; rw [mul_add]; rw [mul_add]; rw [ih]; rw [range_one]; rw [sum_singleton]; rw [List.drop]; rw [ofDigits]; rw [mul_zero]; rw [add_zero]; rw [← Nat.add_sub_assoc sum_le_ofDigits _ Nat.le_of_lt h]
        nth_rw 2 [← one_mul <| ofDigits p tl]
        rw [← add_mul]; rw [Nat.sub_add_cancel (one_le_of_lt h)]; rw [Nat.add_sub_add_left]
  · simp [ofDigits_one]
  · simp [lt_one_iff.mp h]
    cases L
    · rfl
    · simp [ofDigits]

/--
theorem `sub_one_mul_sum_log_div_pow_eq_sub_sum_digits` / 定理 `sub_one_mul_sum_log_div_pow_eq_sub_sum_digits`

English:
theorem sub_one_mul_sum_log_div_pow_eq_sub_sum_digits
  given: {p : Nat} (n : Nat)
  proof: by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · convert!
sub_one_mul_sum_div_pow_eq_sub_sum_digits (p.digits n) (getLast_digit_ne_zero p hn)
        (fun l a => digits_lt_base h a)
      · refine (length_digits p n h hn).symm

中文:
定理 sub_one_mul_sum_log_div_pow_eq_sub_sum_digits
  条件: {p : 自然数} (n : 自然数)
  证明: by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · convert!
sub_one_mul_sum_div_pow_eq_sub_sum_digits (p.digits n) (getLast_digit_ne_zero p hn)
        (fun l a => digits_lt_base h a)
      · refine (length_digits p n h hn).symm

Depends on / 依赖: all_goals, convert, digits, digits_lt_base, eq_or_ne, getLast_digit_ne_zero, length_digits, lt_one_iff, lt_one_iff.mp, ofDigits_digits, p.digits, sub_one_mul_sum_div_pow_eq_sub_sum_digits, trichotomous
-/
theorem sub_one_mul_sum_log_div_pow_eq_sub_sum_digits {p : Nat} (n : Nat) :
    (p - 1) * ∑ i in range (log p n).succ, n / p ^ i.succ = n - (p.digits n).sum := by
  obtain h | rfl | h : 1 < p ∨ 1 = p ∨ p < 1 := trichotomous 1 p
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · convert!
sub_one_mul_sum_div_pow_eq_sub_sum_digits (p.digits n) (getLast_digit_ne_zero p hn)
        (fun l a => digits_lt_base h a)
      · refine (length_digits p n h hn).symm
      all_goals exact (ofDigits_digits p n).symm
  · simp
  · simp [lt_one_iff.mp h]
    cases n
    all_goals simp



/--
theorem `digits_two_eq_bits` / 定理 `digits_two_eq_bits`

English:
theorem digits_two_eq_bits
  given: (n : Nat)
  statement: digits 2 n = n.bits.map fun b => cond b 1 0
  proof: by
  induction n using Nat.binaryRecFromOne with
  | zero => simp
  | one => simp
  | bit b n h ih =>
    rw [bits_append_bit _ _ fun hn => absurd hn h]
    cases b
    · rw [digits_def' one_lt_two]
      · simpa [Nat.bit]
      · simpa [Nat.bit, pos_iff_ne_zero]
    · simpa [Nat.bit, add_comm, digi

中文:
定理 digits_two_eq_bits
  条件: (n : 自然数)
  结论: digits 2 n = n.bits.map fun b => cond b 1 0
  证明: by
  induction n using Nat.binaryRecFromOne with
  | zero => simp
  | one => simp
  | bit b n h ih =>
    rw [bits_append_bit _ _ fun hn => absurd hn h]
    cases b
    · rw [digits_def' one_lt_two]
      · simpa [Nat.bit]
      · simpa [Nat.bit, pos_iff_ne_zero]
    · simpa [Nat.bit, add_comm, digi

Depends on / 依赖: Nat.add_mul_div_left, Nat.binaryRecFromOne, Nat.bit, absurd, add_comm, add_mul_div_left, binaryRecFromOne, bits_append_bit, digits_add, digits_def, one_lt_two, pos_iff_ne_zero
-/
theorem digits_two_eq_bits (n : Nat) : digits 2 n = n.bits.map fun b => cond b 1 0 := by
  induction n using Nat.binaryRecFromOne with
  | zero => simp
  | one => simp
  | bit b n h ih =>
    rw [bits_append_bit _ _ fun hn => absurd hn h]
    cases b
    · rw [digits_def' one_lt_two]
      · simpa [Nat.bit]
      · simpa [Nat.bit, pos_iff_ne_zero]
    · simpa [Nat.bit, add_comm, digits_add 2 one_lt_two 1 n, Nat.add_mul_div_left]



-- This is really a theorem about polynomials.
/--
theorem `dvd_ofDigits_sub_ofDigits` / 定理 `dvd_ofDigits_sub_ofDigits`

English:
theorem dvd_ofDigits_sub_ofDigits
  statement: {α : Type*} [CommRing α] {a b k : α} (h : k ∣ a - b)
  proof: by
  induction L with
  | nil => change k ∣ 0 - 0; simp
  | cons d L ih =>
    simp only [ofDigits, add_sub_add_left_eq_sub]
    exact dvd_mul_sub_mul h ih

中文:
定理 dvd_ofDigits_sub_ofDigits
  结论: {α : 类型} [CommRing α] {a b k : α} (h : k ∣ a - b)
  证明: by
  induction L with
  | nil => change k ∣ 0 - 0; simp
  | cons d L ih =>
    simp only [ofDigits, add_sub_add_left_eq_sub]
    exact dvd_mul_sub_mul h ih

Depends on / 依赖: add_sub_add_left_eq_sub, dvd_mul_sub_mul, ofDigits
-/
theorem dvd_ofDigits_sub_ofDigits {α : Type*} [CommRing α] {a b k : α} (h : k ∣ a - b)
    (L : List Nat) : k ∣ ofDigits a L - ofDigits b L := by
  induction L with
  | nil => change k ∣ 0 - 0; simp
  | cons d L ih =>
    simp only [ofDigits, add_sub_add_left_eq_sub]
    exact dvd_mul_sub_mul h ih

/--
theorem `ofDigits_modEq'` / 定理 `ofDigits_modEq'`

English:
theorem ofDigits_modEq'
  given: (b b' : Nat) (k : Nat) (h : b ≡ b' [MOD k]) (L : List Nat)
  proof: by
  induction L with
  | nil => rfl
  | cons d L ih =>
    dsimp [ofDigits]
    dsimp [Nat.ModEq] at *
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod, h, ih]
    conv_rhs => rw [Nat.add_mod, Nat.mul_mod]

中文:
定理 ofDigits_modEq'
  条件: (b b' : 自然数) (k : 自然数) (h : b ≡ b' [MOD k]) (L : List 自然数)
  证明: by
  induction L with
  | nil => rfl
  | cons d L ih =>
    dsimp [ofDigits]
    dsimp [Nat.ModEq] at *
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod, h, ih]
    conv_rhs => rw [Nat.add_mod, Nat.mul_mod]

Depends on / 依赖: Nat.ModEq, Nat.add_mod, Nat.mul_mod, add_mod, conv_lhs, conv_rhs, mul_mod, ofDigits
-/
theorem ofDigits_modEq' (b b' : Nat) (k : Nat) (h : b ≡ b' [MOD k]) (L : List Nat) :
    ofDigits b L ≡ ofDigits b' L [MOD k] := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    dsimp [ofDigits]
    dsimp [Nat.ModEq] at *
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod, h, ih]
    conv_rhs => rw [Nat.add_mod, Nat.mul_mod]

/--
theorem `ofDigits_modEq` / 定理 `ofDigits_modEq`

English:
theorem ofDigits_modEq
  given: (b k : Nat) (L : List Nat)
  statement: ofDigits b L ≡ ofDigits (b % k) L [MOD k]
  proof: ofDigits_modEq' b (b % k) k (b.mod_modEq k).symm L

中文:
定理 ofDigits_modEq
  条件: (b k : 自然数) (L : List 自然数)
  结论: ofDigits b L ≡ ofDigits (b % k) L [MOD k]
  证明: ofDigits_modEq' b (b % k) k (b.mod_modEq k).symm L

Depends on / 依赖: b.mod_modEq, mod_modEq, ofDigits_modEq
-/
theorem ofDigits_modEq (b k : Nat) (L : List Nat) : ofDigits b L ≡ ofDigits (b % k) L [MOD k] :=
  ofDigits_modEq' b (b % k) k (b.mod_modEq k).symm L

/--
theorem `ofDigits_mod` / 定理 `ofDigits_mod`

English:
theorem ofDigits_mod
  given: (b k : Nat) (L : List Nat)
  statement: ofDigits b L % k = ofDigits (b % k) L % k
  proof: ofDigits_modEq b k L

中文:
定理 ofDigits_mod
  条件: (b k : 自然数) (L : List 自然数)
  结论: ofDigits b L % k = ofDigits (b % k) L % k
  证明: ofDigits_modEq b k L

Depends on / 依赖: ofDigits_modEq
-/
theorem ofDigits_mod (b k : Nat) (L : List Nat) : ofDigits b L % k = ofDigits (b % k) L % k :=
  ofDigits_modEq b k L

/--
theorem `ofDigits_mod_eq_head!` / 定理 `ofDigits_mod_eq_head!`

English:
theorem ofDigits_mod_eq_head!
  given: (b : Nat) (l : List Nat)
  statement: ofDigits b l % b = l.head! % b
  proof: by
  induction l <;> simp [Nat.ofDigits]

中文:
定理 ofDigits_mod_eq_head!
  条件: (b : 自然数) (l : List 自然数)
  结论: ofDigits b l % b = l.head! % b
  证明: by
  induction l <;> simp [Nat.ofDigits]

Depends on / 依赖: Nat.ofDigits, ofDigits
-/
theorem ofDigits_mod_eq_head! (b : Nat) (l : List Nat) : ofDigits b l % b = l.head! % b := by
  induction l <;> simp [Nat.ofDigits]

/--
theorem `head!_digits` / 定理 `head!_digits`

English:
theorem head!_digits
  given: {b n : Nat} (h : b != 1)
  statement: (Nat.digits b n).head! = n % b
  proof: by
  by_cases hb : 1 < b
  · rcases n with _ | n
    · simp
    · nth_rw 2 [← Nat.ofDigits_digits b (n + 1)]
      rw [Nat.ofDigits_mod_eq_head! _ _]
      exact (Nat.mod_eq_of_lt (Nat.digits_lt_base hb <| List.head!_mem_self <|
Nat.digits_ne_nil_iff_ne_zero.mpr Nat.succ_ne_zero n)).symm
  · rcases 

中文:
定理 head!_digits
  条件: {b n : 自然数} (h : b != 1)
  结论: (自然数.digits b n).head! = n % b
  证明: by
  by_cases hb : 1 < b
  · rcases n with _ | n
    · simp
    · nth_rw 2 [← Nat.ofDigits_digits b (n + 1)]
      rw [Nat.ofDigits_mod_eq_head! _ _]
      exact (Nat.mod_eq_of_lt (Nat.digits_lt_base hb <| List.head!_mem_self <|
Nat.digits_ne_nil_iff_ne_zero.mpr Nat.succ_ne_zero n)).symm
  · rcases 

Depends on / 依赖: List.head, Nat.digits_lt_base, Nat.digits_ne_nil_iff_ne_zero.mpr, Nat.mod_eq_of_lt, Nat.ofDigits_digits, Nat.ofDigits_mod_eq_head, Nat.succ_ne_zero, _mem_self, digits_lt_base, digits_ne_nil_iff_ne_zero, mod_eq_of_lt, nth_rw, ofDigits_digits, ofDigits_mod_eq_head, succ_ne_zero
-/
theorem head!_digits {b n : Nat} (h : b != 1) : (Nat.digits b n).head! = n % b := by
  by_cases hb : 1 < b
  · rcases n with _ | n
    · simp
    · nth_rw 2 [← Nat.ofDigits_digits b (n + 1)]
      rw [Nat.ofDigits_mod_eq_head! _ _]
      exact (Nat.mod_eq_of_lt (Nat.digits_lt_base hb <| List.head!_mem_self <|
Nat.digits_ne_nil_iff_ne_zero.mpr Nat.succ_ne_zero n)).symm
  · rcases n with _ | _ <;> simp_all [show b = 0 by lia]

/--
theorem `ofDigits_zmodeq'` / 定理 `ofDigits_zmodeq'`

English:
theorem ofDigits_zmodeq'
  given: (b b' : Int) (k : Nat) (h : b ≡ b' [ZMOD k]) (L : List Nat)
  proof: by
  induction L with
  | nil => rfl
  | cons d L ih =>
    dsimp [ofDigits]
    dsimp [Int.ModEq] at *
    conv_lhs => rw [Int.add_emod, Int.mul_emod, h, ih]
    conv_rhs => rw [Int.add_emod, Int.mul_emod]

中文:
定理 ofDigits_zmodeq'
  条件: (b b' : 整数) (k : 自然数) (h : b ≡ b' [ZMOD k]) (L : List 自然数)
  证明: by
  induction L with
  | nil => rfl
  | cons d L ih =>
    dsimp [ofDigits]
    dsimp [Int.ModEq] at *
    conv_lhs => rw [Int.add_emod, Int.mul_emod, h, ih]
    conv_rhs => rw [Int.add_emod, Int.mul_emod]

Depends on / 依赖: Int.ModEq, Int.add_emod, Int.mul_emod, add_emod, conv_lhs, conv_rhs, mul_emod, ofDigits
-/
theorem ofDigits_zmodeq' (b b' : Int) (k : Nat) (h : b ≡ b' [ZMOD k]) (L : List Nat) :
    ofDigits b L ≡ ofDigits b' L [ZMOD k] := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    dsimp [ofDigits]
    dsimp [Int.ModEq] at *
    conv_lhs => rw [Int.add_emod, Int.mul_emod, h, ih]
    conv_rhs => rw [Int.add_emod, Int.mul_emod]

/--
theorem `ofDigits_zmodeq` / 定理 `ofDigits_zmodeq`

English:
theorem ofDigits_zmodeq
  given: (b : Int) (k : Nat) (L : List Nat)
  statement: ofDigits b L ≡ ofDigits (b % k) L [ZMOD k]
  proof: ofDigits_zmodeq' b (b % k) k (b.mod_modEq ↑k).symm L

中文:
定理 ofDigits_zmodeq
  条件: (b : 整数) (k : 自然数) (L : List 自然数)
  结论: ofDigits b L ≡ ofDigits (b % k) L [ZMOD k]
  证明: ofDigits_zmodeq' b (b % k) k (b.mod_modEq ↑k).symm L

Depends on / 依赖: b.mod_modEq, mod_modEq, ofDigits_zmodeq
-/
theorem ofDigits_zmodeq (b : Int) (k : Nat) (L : List Nat) : ofDigits b L ≡ ofDigits (b % k) L [ZMOD k] :=
  ofDigits_zmodeq' b (b % k) k (b.mod_modEq ↑k).symm L

/--
theorem `ofDigits_zmod` / 定理 `ofDigits_zmod`

English:
theorem ofDigits_zmod
  given: (b : Int) (k : Nat) (L : List Nat)
  statement: ofDigits b L % k = ofDigits (b % k) L % k
  proof: ofDigits_zmodeq b k L

中文:
定理 ofDigits_zmod
  条件: (b : 整数) (k : 自然数) (L : List 自然数)
  结论: ofDigits b L % k = ofDigits (b % k) L % k
  证明: ofDigits_zmodeq b k L

Depends on / 依赖: ofDigits_zmodeq
-/
theorem ofDigits_zmod (b : Int) (k : Nat) (L : List Nat) : ofDigits b L % k = ofDigits (b % k) L % k :=
  ofDigits_zmodeq b k L

/--
theorem `modEq_digits_sum` / 定理 `modEq_digits_sum`

English:
theorem modEq_digits_sum
  given: (b b' : Nat) (h : b' % b = 1) (n : Nat)
  statement: n ≡ (digits b' n).sum [MOD b]
  proof: by
  rw [← ofDigits_one]
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  convert! ofDigits_modEq b' b (digits b' n)
  exact h.symm

中文:
定理 modEq_digits_sum
  条件: (b b' : 自然数) (h : b' % b = 1) (n : 自然数)
  结论: n ≡ (digits b' n).sum [MOD b]
  证明: by
  rw [← ofDigits_one]
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  convert! ofDigits_modEq b' b (digits b' n)
  exact h.symm

Depends on / 依赖: convert, digits, h.symm, ofDigits_digits, ofDigits_modEq, ofDigits_one
-/
theorem modEq_digits_sum (b b' : Nat) (h : b' % b = 1) (n : Nat) : n ≡ (digits b' n).sum [MOD b] := by
  rw [← ofDigits_one]
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  convert! ofDigits_modEq b' b (digits b' n)
  exact h.symm

/--
theorem `zmodeq_ofDigits_digits` / 定理 `zmodeq_ofDigits_digits`

English:
theorem zmodeq_ofDigits_digits
  given: (b b' : Nat) (c : Int) (h : b' ≡ c [ZMOD b]) (n : Nat)
  proof: by
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  rw [coe_ofDigits]
  apply ofDigits_zmodeq' _ _ _ h

中文:
定理 zmodeq_ofDigits_digits
  条件: (b b' : 自然数) (c : 整数) (h : b' ≡ c [ZMOD b]) (n : 自然数)
  证明: by
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  rw [coe_ofDigits]
  apply ofDigits_zmodeq' _ _ _ h

Depends on / 依赖: coe_ofDigits, ofDigits_digits, ofDigits_zmodeq
-/
theorem zmodeq_ofDigits_digits (b b' : Nat) (c : Int) (h : b' ≡ c [ZMOD b]) (n : Nat) :
    n ≡ ofDigits c (digits b' n) [ZMOD b] := by
  conv =>
    congr
    · skip
    · rw [← ofDigits_digits b' n]
  rw [coe_ofDigits]
  apply ofDigits_zmodeq' _ _ _ h

/--
theorem `ofDigits_neg_one` / 定理 `ofDigits_neg_one`

English:
theorem ofDigits_neg_one

中文:
定理 ofDigits_neg_one
-/
theorem ofDigits_neg_one :
    forall L : List Nat, ofDigits (-1 : Int) L = (L.map fun n : Nat => (n : Int)).alternatingSum
  | [] => rfl
  | [n] => by simp [ofDigits, List.alternatingSum]
  | a :: b :: t => by
    simp only [ofDigits, List.alternatingSum, List.map_cons, ofDigits_neg_one t]
    ring

/--
theorem `getD_digits` / 定理 `getD_digits`

English:
theorem getD_digits
  given: (n i : Nat) {b : Nat} (h : 2 <= b)
  statement: (digits b n).getD i 0 = n / b ^ i % b
  proof: by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' h
  clear h
  rw [List.getD_eq_getElem?_getD]
  induction n using Nat.caseStrongRecOn generalizing i with
  | zero => simp
  | ind n IH =>
    rcases i with _ | i
    · rw [← List.head?_eq_getElem?, ← default_eq_zero, ← List.head!_eq_head?_getD,
     

中文:
定理 getD_digits
  条件: (n i : 自然数) {b : 自然数} (h : 2 <= b)
  结论: (digits b n).getD i 0 = n / b ^ i % b
  证明: by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' h
  clear h
  rw [List.getD_eq_getElem?_getD]
  induction n using Nat.caseStrongRecOn generalizing i with
  | zero => simp
  | ind n IH =>
    rcases i with _ | i
    · rw [← List.head?_eq_getElem?, ← default_eq_zero, ← List.head!_eq_head?_getD,
     

Depends on / 依赖: List.getD_eq_getElem, List.head, Nat.caseStrongRecOn, Nat.div_div_eq_div_mul, Nat.exists_eq_add_of_le, _digits, _eq_getElem, _eq_head, _getD, caseStrongRecOn, default_eq_zero, div_div_eq_div_mul, div_lt_self, exists_eq_add_of_le, generalizing, getD_eq_getElem, le_of_lt_succ, pow_succ
-/
theorem getD_digits (n i : Nat) {b : Nat} (h : 2 <= b) : (digits b n).getD i 0 = n / b ^ i % b := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' h
  clear h
  rw [List.getD_eq_getElem?_getD]
  induction n using Nat.caseStrongRecOn generalizing i with
  | zero => simp
  | ind n IH =>
    rcases i with _ | i
    · rw [← List.head?_eq_getElem?, ← default_eq_zero, ← List.head!_eq_head?_getD,
        head!_digits (by grind)]
      simp
    · simp [IH _ (le_of_lt_succ (div_lt_self' n b)), pow_succ', Nat.div_div_eq_div_mul]

/-! ### Bijection -/

open List

/--
Definition of `digitsAppend` / `digitsAppend` 的定义

English:
definition digitsAppend
  signature: (b l n : Nat)
  body: b.digits n ++ replicate (l - (b.digits n).length) 0

中文:
定义 digitsAppend
  签名: (b l n : 自然数)
  定义体: b.digits n ++ replicate (l - (b.digits n).length) 0

Depends on / 依赖: b.digits, digits, length, replicate
-/
def digitsAppend (b l n : Nat) : List Nat :=
  b.digits n ++ replicate (l - (b.digits n).length) 0

/--
theorem `length_digitsAppend` / 定理 `length_digitsAppend`

English:
theorem length_digitsAppend
  given: {b : Nat} (hb : 1 < b) (l : Nat) (hn : n < b ^ l)
  proof: by
  rw [digitsAppend]; rw [length_append]; rw [length_replicate]; rw [Nat.add_sub_cancel']
  rwa [digits_length_le_iff hb]

中文:
定理 length_digitsAppend
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数) (hn : n < b ^ l)
  证明: by
  rw [digitsAppend]; rw [length_append]; rw [length_replicate]; rw [Nat.add_sub_cancel']
  rwa [digits_length_le_iff hb]

Depends on / 依赖: Nat.add_sub_cancel, add_sub_cancel, digitsAppend, digits_length_le_iff, length_append, length_replicate
-/
theorem length_digitsAppend {b : Nat} (hb : 1 < b) (l : Nat) (hn : n < b ^ l) :
    (digitsAppend b l n).length = l := by
  rw [digitsAppend]; rw [length_append]; rw [length_replicate]; rw [Nat.add_sub_cancel']
  rwa [digits_length_le_iff hb]

/--
theorem `lt_of_mem_digitsAppend` / 定理 `lt_of_mem_digitsAppend`

English:
theorem lt_of_mem_digitsAppend
  statement: {b : Nat} (hb : 1 < b) (l i : Nat)
  proof: by
  rw [digitsAppend]; rw [mem_append]; rw [mem_replicate] at hi
  obtain hi | ⟨_, rfl⟩ := hi
  · exact digits_lt_base hb hi
  · linarith

中文:
定理 lt_of_mem_digitsAppend
  结论: {b : 自然数} (hb : 1 < b) (l i : 自然数)
  证明: by
  rw [digitsAppend]; rw [mem_append]; rw [mem_replicate] at hi
  obtain hi | ⟨_, rfl⟩ := hi
  · exact digits_lt_base hb hi
  · linarith

Depends on / 依赖: digitsAppend, digits_lt_base, mem_append, mem_replicate
-/
theorem lt_of_mem_digitsAppend {b : Nat} (hb : 1 < b) (l i : Nat)
    (hi : i in digitsAppend b l n) : i < b := by
  rw [digitsAppend]; rw [mem_append]; rw [mem_replicate] at hi
  obtain hi | ⟨_, rfl⟩ := hi
  · exact digits_lt_base hb hi
  · linarith

/--
theorem `mapsTo_ofDigits` / 定理 `mapsTo_ofDigits`

English:
theorem mapsTo_ofDigits
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: fun _ h => Set.mem_ofPred.mpr h.1 ▸ Nat.ofDigits_lt_base_pow_length hb h.2

中文:
定理 mapsTo_ofDigits
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: fun _ h => Set.mem_ofPred.mpr h.1 ▸ Nat.ofDigits_lt_base_pow_length hb h.2

Depends on / 依赖: Nat.ofDigits_lt_base_pow_length, Set.mem_ofPred.mpr, mem_ofPred, ofDigits_lt_base_pow_length
-/
theorem mapsTo_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) :
    Set.MapsTo (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, x < b} {n | n < b ^ l} :=
  fun _ h => Set.mem_ofPred.mpr h.1 ▸ Nat.ofDigits_lt_base_pow_length hb h.2

/--
theorem `mapsTo_digitsAppend` / 定理 `mapsTo_digitsAppend`

English:
theorem mapsTo_digitsAppend
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: fun _ h => ⟨by rw [length_digitsAppend hb _ h], fun _ hi => lt_of_mem_digitsAppend hb l _ hi⟩

中文:
定理 mapsTo_digitsAppend
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: fun _ h => ⟨by rw [length_digitsAppend hb _ h], fun _ hi => lt_of_mem_digitsAppend hb l _ hi⟩

Depends on / 依赖: length_digitsAppend, lt_of_mem_digitsAppend
-/
theorem mapsTo_digitsAppend {b : Nat} (hb : 1 < b) (l : Nat) :
    Set.MapsTo (digitsAppend b l) {n | n < b ^ l} {L : List Nat | L.length = l ∧ forall x in L, x < b} :=
  fun _ h => ⟨by rw [length_digitsAppend hb _ h], fun _ hi => lt_of_mem_digitsAppend hb l _ hi⟩

/--
theorem `injOn_ofDigits` / 定理 `injOn_ofDigits`

English:
theorem injOn_ofDigits
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: fun _ _ _ _ h => ofDigits_inj_of_len_eq hb (by simp_all) (by simp_all) (by simp_all) h

中文:
定理 injOn_ofDigits
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: fun _ _ _ _ h => ofDigits_inj_of_len_eq hb (by simp_all) (by simp_all) (by simp_all) h

Depends on / 依赖: ofDigits_inj_of_len_eq
-/
theorem injOn_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) :
    Set.InjOn (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, x < b} :=
  fun _ _ _ _ h => ofDigits_inj_of_len_eq hb (by simp_all) (by simp_all) (by simp_all) h

/--
theorem `setInvOn_digitsAppend_ofDigits` / 定理 `setInvOn_digitsAppend_ofDigits`

English:
theorem setInvOn_digitsAppend_ofDigits
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: by
  refine ⟨fun L hL => ?_, fun _ _ => by rw [digitsAppend, ofDigits_append_replicate_zero,
    ofDigits_digits]⟩
  refine (injOn_ofDigits hb l) ⟨?_, ?_⟩ hL
    (by rw [digitsAppend, ofDigits_append_replicate_zero, ofDigits_digits])
  · rw [length_digitsAppend hb _ (mapsTo_ofDigits hb _ hL)]
  · ex

中文:
定理 setInvOn_digitsAppend_ofDigits
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: by
  refine ⟨fun L hL => ?_, fun _ _ => by rw [digitsAppend, ofDigits_append_replicate_zero,
    ofDigits_digits]⟩
  refine (injOn_ofDigits hb l) ⟨?_, ?_⟩ hL
    (by rw [digitsAppend, ofDigits_append_replicate_zero, ofDigits_digits])
  · rw [length_digitsAppend hb _ (mapsTo_ofDigits hb _ hL)]
  · ex

Depends on / 依赖: digitsAppend, injOn_ofDigits, length_digitsAppend, lt_of_mem_digitsAppend, mapsTo_ofDigits, ofDigits_append_replicate_zero, ofDigits_digits
-/
theorem setInvOn_digitsAppend_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) :
    Set.InvOn (digitsAppend b l) (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, x < b}
      {n | n < b ^ l} := by
  refine ⟨fun L hL => ?_, fun _ _ => by rw [digitsAppend, ofDigits_append_replicate_zero,
    ofDigits_digits]⟩
  refine (injOn_ofDigits hb l) ⟨?_, ?_⟩ hL
    (by rw [digitsAppend, ofDigits_append_replicate_zero, ofDigits_digits])
  · rw [length_digitsAppend hb _ (mapsTo_ofDigits hb _ hL)]
  · exact fun x hx => lt_of_mem_digitsAppend hb l x hx

/--
theorem `bijOn_ofDigits` / 定理 `bijOn_ofDigits`

English:
theorem bijOn_ofDigits
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: (setInvOn_digitsAppend_ofDigits hb l).bijOn (mapsTo_ofDigits hb l) (mapsTo_digitsAppend hb l)

中文:
定理 bijOn_ofDigits
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: (setInvOn_digitsAppend_ofDigits hb l).bijOn (mapsTo_ofDigits hb l) (mapsTo_digitsAppend hb l)

Depends on / 依赖: mapsTo_digitsAppend, mapsTo_ofDigits, setInvOn_digitsAppend_ofDigits
-/
theorem bijOn_ofDigits {b : Nat} (hb : 1 < b) (l : Nat) :
    Set.BijOn (ofDigits b) {L : List Nat | L.length = l ∧ forall x in L, x < b} {n | n < b ^ l} :=
  (setInvOn_digitsAppend_ofDigits hb l).bijOn (mapsTo_ofDigits hb l) (mapsTo_digitsAppend hb l)

/--
theorem `bijOn_digitsAppend` / 定理 `bijOn_digitsAppend`

English:
theorem bijOn_digitsAppend
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: (bijOn_ofDigits hb l).symm (setInvOn_digitsAppend_ofDigits hb l).symm

中文:
定理 bijOn_digitsAppend
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: (bijOn_ofDigits hb l).symm (setInvOn_digitsAppend_ofDigits hb l).symm

Depends on / 依赖: bijOn_ofDigits, setInvOn_digitsAppend_ofDigits
-/
theorem bijOn_digitsAppend {b : Nat} (hb : 1 < b) (l : Nat) :
    Set.BijOn (digitsAppend b l) {n | n < b ^ l} {L : List Nat | L.length = l ∧ forall x in L, x < b} :=
  (bijOn_ofDigits hb l).symm (setInvOn_digitsAppend_ofDigits hb l).symm

/--
theorem `sum_digits_ofDigits_eq_sum` / 定理 `sum_digits_ofDigits_eq_sum`

English:
theorem sum_digits_ofDigits_eq_sum
  statement: {b : Nat} (hb : 1 < b) {l : Nat} {L : List Nat}
  proof: by
  nth_rewrite 2 [← (setInvOn_digitsAppend_ofDigits hb l).1 hL]
  rw [digitsAppend]; rw [List.sum_append_nat]; rw [List.sum_replicate]; rw [nsmul_zero]; rw [add_zero]

中文:
定理 sum_digits_ofDigits_eq_sum
  结论: {b : 自然数} (hb : 1 < b) {l : 自然数} {L : List 自然数}
  证明: by
  nth_rewrite 2 [← (setInvOn_digitsAppend_ofDigits hb l).1 hL]
  rw [digitsAppend]; rw [List.sum_append_nat]; rw [List.sum_replicate]; rw [nsmul_zero]; rw [add_zero]

Depends on / 依赖: List.sum_append_nat, List.sum_replicate, add_zero, digitsAppend, nsmul_zero, nth_rewrite, setInvOn_digitsAppend_ofDigits, sum_append_nat, sum_replicate
-/
theorem sum_digits_ofDigits_eq_sum {b : Nat} (hb : 1 < b) {l : Nat} {L : List Nat}
    (hL : L in {L : List Nat | L.length = l ∧ forall x in L, x < b}) :
    (b.digits (ofDigits b L)).sum = L.sum := by
  nth_rewrite 2 [← (setInvOn_digitsAppend_ofDigits hb l).1 hL]
  rw [digitsAppend]; rw [List.sum_append_nat]; rw [List.sum_replicate]; rw [nsmul_zero]; rw [add_zero]

end Nat

namespace List

open Nat

/--
Definition of `fixedLengthDigits` / `fixedLengthDigits` 的定义

English:
definition fixedLengthDigits
  signature: {b : Nat} (hb : 1 < b) (l : Nat)
  body: by
  have : Fintype {L : List Nat | L.length = l ∧ forall x in L, x < b} :=
    Fintype.ofInjective (Set.MapsTo.restrict _ _ _ (mapsTo_ofDigits hb l))
 (Set.MapsTo.restrict_inj (mapsTo_ofDigits hb l)).mpr injOn_ofDigits hb l
  exact {L : List Nat | L.length = l ∧ forall x in L, x < b}.toFinset

中文:
定义 fixedLengthDigits
  签名: {b : 自然数} (hb : 1 < b) (l : 自然数)
  定义体: by
  have : Fintype {L : List Nat | L.length = l ∧ forall x in L, x < b} :=
    Fintype.ofInjective (Set.MapsTo.restrict _ _ _ (mapsTo_ofDigits hb l))
 (Set.MapsTo.restrict_inj (mapsTo_ofDigits hb l)).mpr injOn_ofDigits hb l
  exact {L : List Nat | L.length = l ∧ forall x in L, x < b}.toFinset

Depends on / 依赖: Fintype, Fintype.ofInjective, L.length, MapsTo, Set.MapsTo.restrict, Set.MapsTo.restrict_inj, injOn_ofDigits, length, mapsTo_ofDigits, ofInjective, restrict, restrict_inj, toFinset
-/
noncomputable def fixedLengthDigits {b : Nat} (hb : 1 < b) (l : Nat) : Finset (List Nat) := by
  have : Fintype {L : List Nat | L.length = l ∧ forall x in L, x < b} :=
    Fintype.ofInjective (Set.MapsTo.restrict _ _ _ (mapsTo_ofDigits hb l))
 (Set.MapsTo.restrict_inj (mapsTo_ofDigits hb l)).mpr injOn_ofDigits hb l
  exact {L : List Nat | L.length = l ∧ forall x in L, x < b}.toFinset

/--
theorem `mem_fixedLengthDigits_iff` / 定理 `mem_fixedLengthDigits_iff`

English:
theorem mem_fixedLengthDigits_iff
  given: {b : Nat} (hb : 1 < b) {l : Nat} {L : List Nat}
  proof: by
  simp [fixedLengthDigits]

中文:
定理 mem_fixedLengthDigits_iff
  条件: {b : 自然数} (hb : 1 < b) {l : 自然数} {L : List 自然数}
  证明: by
  simp [fixedLengthDigits]

Depends on / 依赖: fixedLengthDigits
-/
theorem mem_fixedLengthDigits_iff {b : Nat} (hb : 1 < b) {l : Nat} {L : List Nat} :
    L in fixedLengthDigits hb l ↔ L.length = l ∧ forall x in L, x < b := by
  simp [fixedLengthDigits]

/--
theorem `_root_.Nat.bijOn_ofDigits'` / 定理 `_root_.Nat.bijOn_ofDigits'`

English:
theorem _root_.Nat.bijOn_ofDigits'
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: by
  rw [fixedLengthDigits]; rw [Set.coe_toFinset]
  convert! bijOn_ofDigits hb l
  ext; simp

中文:
定理 _root_.Nat.bijOn_ofDigits'
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: by
  rw [fixedLengthDigits]; rw [Set.coe_toFinset]
  convert! bijOn_ofDigits hb l
  ext; simp

Depends on / 依赖: Set.coe_toFinset, bijOn_ofDigits, coe_toFinset, convert, fixedLengthDigits
-/
theorem _root_.Nat.bijOn_ofDigits' {b : Nat} (hb : 1 < b) (l : Nat) :
    Set.BijOn (ofDigits b) (fixedLengthDigits hb l) (Finset.range (b ^ l)) := by
  rw [fixedLengthDigits]; rw [Set.coe_toFinset]
  convert! bijOn_ofDigits hb l
  ext; simp

/--
theorem `_root_.Nat.bijOn_digitsAppend'` / 定理 `_root_.Nat.bijOn_digitsAppend'`

English:
theorem _root_.Nat.bijOn_digitsAppend'
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: by
  rw [fixedLengthDigits]; rw [Set.coe_toFinset]
  convert! bijOn_digitsAppend hb l
  ext; simp

@[simp]

中文:
定理 _root_.Nat.bijOn_digitsAppend'
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: by
  rw [fixedLengthDigits]; rw [Set.coe_toFinset]
  convert! bijOn_digitsAppend hb l
  ext; simp

@[simp]

Depends on / 依赖: Set.coe_toFinset, bijOn_digitsAppend, coe_toFinset, convert, fixedLengthDigits
-/
theorem _root_.Nat.bijOn_digitsAppend' {b : Nat} (hb : 1 < b) (l : Nat) :
    Set.BijOn (digitsAppend b l) (Finset.range (b ^ l)) (fixedLengthDigits hb l) := by
  rw [fixedLengthDigits]; rw [Set.coe_toFinset]
  convert! bijOn_digitsAppend hb l
  ext; simp

@[simp]
/--
theorem `fixedLengthDigits_zero` / 定理 `fixedLengthDigits_zero`

English:
theorem fixedLengthDigits_zero
  given: {b : Nat} (hb : 1 < b)
  proof: by
  ext
  simp [fixedLengthDigits]
  grind

@[simp]

中文:
定理 fixedLengthDigits_zero
  条件: {b : 自然数} (hb : 1 < b)
  证明: by
  ext
  simp [fixedLengthDigits]
  grind

@[simp]

Depends on / 依赖: fixedLengthDigits
-/
theorem fixedLengthDigits_zero {b : Nat} (hb : 1 < b) :
    fixedLengthDigits hb 0 = {[]} := by
  ext
  simp [fixedLengthDigits]
  grind

@[simp]
/--
theorem `fixedLengthDigits_one` / 定理 `fixedLengthDigits_one`

English:
theorem fixedLengthDigits_one
  given: {b : Nat} (hb : 1 < b)
  proof: by
  ext
  rw [mem_fixedLengthDigits_iff]; rw [List.length_eq_one_iff]
  grind

中文:
定理 fixedLengthDigits_one
  条件: {b : 自然数} (hb : 1 < b)
  证明: by
  ext
  rw [mem_fixedLengthDigits_iff]; rw [List.length_eq_one_iff]
  grind

Depends on / 依赖: List.length_eq_one_iff, length_eq_one_iff, mem_fixedLengthDigits_iff
-/
theorem fixedLengthDigits_one {b : Nat} (hb : 1 < b) :
    fixedLengthDigits hb 1 = Finset.image (fun x : Nat => [x]) (Finset.range b) := by
  ext
  rw [mem_fixedLengthDigits_iff]; rw [List.length_eq_one_iff]
  grind

/--
theorem `card_fixedLengthDigits` / 定理 `card_fixedLengthDigits`

English:
theorem card_fixedLengthDigits
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: by
  rw [Set.BijOn.finsetCard_eq (ofDigits b) (bijOn_ofDigits' hb l)]; rw [Finset.card_range]

中文:
定理 card_fixedLengthDigits
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: by
  rw [Set.BijOn.finsetCard_eq (ofDigits b) (bijOn_ofDigits' hb l)]; rw [Finset.card_range]

Depends on / 依赖: Finset, Finset.card_range, Set.BijOn.finsetCard_eq, bijOn_ofDigits, card_range, finsetCard_eq, ofDigits
-/
theorem card_fixedLengthDigits {b : Nat} (hb : 1 < b) (l : Nat) :
    Finset.card (fixedLengthDigits hb l) = b ^ l := by
  rw [Set.BijOn.finsetCard_eq (ofDigits b) (bijOn_ofDigits' hb l)]; rw [Finset.card_range]

/--
Definition of `consFixedLengthDigits` / `consFixedLengthDigits` 的定义

English:
definition consFixedLengthDigits
  signature: {b : Nat} (hb : 1 < b) (l d : Nat)
  body: Finset.image (fun L => d :: L) (fixedLengthDigits hb l)

中文:
定义 consFixedLengthDigits
  签名: {b : 自然数} (hb : 1 < b) (l d : 自然数)
  定义体: Finset.image (fun L => d :: L) (fixedLengthDigits hb l)

Depends on / 依赖: Finset, Finset.image, fixedLengthDigits
-/
noncomputable def consFixedLengthDigits {b : Nat} (hb : 1 < b) (l d : Nat) :
    Finset (List Nat) := Finset.image (fun L => d :: L) (fixedLengthDigits hb l)

/--
theorem `ne_empty_of_mem_consFixedLengthDigits` / 定理 `ne_empty_of_mem_consFixedLengthDigits`

English:
theorem ne_empty_of_mem_consFixedLengthDigits
  statement: {b : Nat} (hb : 1 < b) {l d : Nat} {L : List Nat}
  proof: by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hL
  exact cons_ne_nil d _

中文:
定理 ne_empty_of_mem_consFixedLengthDigits
  结论: {b : 自然数} (hb : 1 < b) {l d : 自然数} {L : List 自然数}
  证明: by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hL
  exact cons_ne_nil d _

Depends on / 依赖: Finset, Finset.mem_image.mp, cons_ne_nil, mem_image
-/
theorem ne_empty_of_mem_consFixedLengthDigits {b : Nat} (hb : 1 < b) {l d : Nat} {L : List Nat}
    (hL : L in consFixedLengthDigits hb l d) : L != [] := by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hL
  exact cons_ne_nil d _

/--
theorem `consFixedLengthDigits_head` / 定理 `consFixedLengthDigits_head`

English:
theorem consFixedLengthDigits_head
  statement: {b : Nat} (hb : 1 < b) {l d : Nat} {L : List Nat}
  proof: by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hL
  rw [head_cons]

中文:
定理 consFixedLengthDigits_head
  结论: {b : 自然数} (hb : 1 < b) {l d : 自然数} {L : List 自然数}
  证明: by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hL
  rw [head_cons]

Depends on / 依赖: Finset, Finset.mem_image.mp, head_cons, mem_image
-/
theorem consFixedLengthDigits_head {b : Nat} (hb : 1 < b) {l d : Nat} {L : List Nat}
    (hL : L in consFixedLengthDigits hb l d) :
    List.head L (ne_empty_of_mem_consFixedLengthDigits hb hL) = d := by
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hL
  rw [head_cons]

/--
theorem `cons_mem_fixedLengthDigits_succ` / 定理 `cons_mem_fixedLengthDigits_succ`

English:
theorem cons_mem_fixedLengthDigits_succ
  statement: {b : Nat} (hb : 1 < b) (l d : Nat) (hd : d < b) {L : List Nat}
  proof: by
  refine (mem_fixedLengthDigits_iff hb).mpr ⟨?_, ?_⟩
  · simpa using ((mem_fixedLengthDigits_iff hb).mp hL).1
  · intro x hx
    obtain rfl | hx := mem_cons.mp hx
    · exact hd
    · exact ((mem_fixedLengthDigits_iff hb).mp hL).2 _ hx

中文:
定理 cons_mem_fixedLengthDigits_succ
  结论: {b : 自然数} (hb : 1 < b) (l d : 自然数) (hd : d < b) {L : List 自然数}
  证明: by
  refine (mem_fixedLengthDigits_iff hb).mpr ⟨?_, ?_⟩
  · simpa using ((mem_fixedLengthDigits_iff hb).mp hL).1
  · intro x hx
    obtain rfl | hx := mem_cons.mp hx
    · exact hd
    · exact ((mem_fixedLengthDigits_iff hb).mp hL).2 _ hx

Depends on / 依赖: mem_cons, mem_cons.mp, mem_fixedLengthDigits_iff
-/
theorem cons_mem_fixedLengthDigits_succ {b : Nat} (hb : 1 < b) (l d : Nat) (hd : d < b) {L : List Nat}
    (hL : L in fixedLengthDigits hb l) :
    d :: L in fixedLengthDigits hb (l + 1) := by
  refine (mem_fixedLengthDigits_iff hb).mpr ⟨?_, ?_⟩
  · simpa using ((mem_fixedLengthDigits_iff hb).mp hL).1
  · intro x hx
    obtain rfl | hx := mem_cons.mp hx
    · exact hd
    · exact ((mem_fixedLengthDigits_iff hb).mp hL).2 _ hx

/--
theorem `pairwiseDisjoint_consFixedLengthDigits` / 定理 `pairwiseDisjoint_consFixedLengthDigits`

English:
theorem pairwiseDisjoint_consFixedLengthDigits
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: by
  refine Finset.pairwiseDisjoint_iff.mpr fun i _ j _ ⟨L, hL⟩ => ?_
  rw [Finset.mem_inter] at hL
  exact (consFixedLengthDigits_head hb hL.1).symm.trans (consFixedLengthDigits_head hb hL.2)

中文:
定理 pairwiseDisjoint_consFixedLengthDigits
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: by
  refine Finset.pairwiseDisjoint_iff.mpr fun i _ j _ ⟨L, hL⟩ => ?_
  rw [Finset.mem_inter] at hL
  exact (consFixedLengthDigits_head hb hL.1).symm.trans (consFixedLengthDigits_head hb hL.2)

Depends on / 依赖: Finset, Finset.mem_inter, Finset.pairwiseDisjoint_iff.mpr, consFixedLengthDigits_head, mem_inter, pairwiseDisjoint_iff, symm.trans
-/
theorem pairwiseDisjoint_consFixedLengthDigits {b : Nat} (hb : 1 < b) (l : Nat) :
    Set.PairwiseDisjoint (Finset.range b : Set Nat) (fun d => consFixedLengthDigits hb l d) := by
  refine Finset.pairwiseDisjoint_iff.mpr fun i _ j _ ⟨L, hL⟩ => ?_
  rw [Finset.mem_inter] at hL
  exact (consFixedLengthDigits_head hb hL.1).symm.trans (consFixedLengthDigits_head hb hL.2)

/--
theorem `fixedLengthDigits_succ_eq_disjiUnion` / 定理 `fixedLengthDigits_succ_eq_disjiUnion`

English:
theorem fixedLengthDigits_succ_eq_disjiUnion
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: by
  ext L
  simp_rw [Finset.disjiUnion_eq_biUnion, Finset.mem_biUnion, Finset.mem_range,
    consFixedLengthDigits, Finset.mem_image]
  refine ⟨fun hL => ?_, ?_⟩
  · have hL₁ : L.length = l + 1 := ((mem_fixedLengthDigits_iff hb).mp hL).1
    have hL₂ : forall x in L, x < b := ((mem_fixedLengthDigit

中文:
定理 fixedLengthDigits_succ_eq_disjiUnion
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: by
  ext L
  simp_rw [Finset.disjiUnion_eq_biUnion, Finset.mem_biUnion, Finset.mem_range,
    consFixedLengthDigits, Finset.mem_image]
  refine ⟨fun hL => ?_, ?_⟩
  · have hL₁ : L.length = l + 1 := ((mem_fixedLengthDigits_iff hb).mp hL).1
    have hL₂ : forall x in L, x < b := ((mem_fixedLengthDigit

Depends on / 依赖: Finset, Finset.disjiUnion_eq_biUnion, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, L.head, L.head_mem, L.length, L.tail, consFixedLengthDigits, cons_head_tail, disjiUnion_eq_biUnion, head_mem, length, mem_biUnion, mem_fixedLengthDigits_iff, mem_image, mem_range, ne_nil_iff_length_pos, simp_rw
-/
theorem fixedLengthDigits_succ_eq_disjiUnion {b : Nat} (hb : 1 < b) (l : Nat) :
    fixedLengthDigits hb (l + 1) = Finset.disjiUnion (Finset.range b)
      (consFixedLengthDigits hb l) (pairwiseDisjoint_consFixedLengthDigits hb l) := by
  ext L
  simp_rw [Finset.disjiUnion_eq_biUnion, Finset.mem_biUnion, Finset.mem_range,
    consFixedLengthDigits, Finset.mem_image]
  refine ⟨fun hL => ?_, ?_⟩
  · have hL₁ : L.length = l + 1 := ((mem_fixedLengthDigits_iff hb).mp hL).1
    have hL₂ : forall x in L, x < b := ((mem_fixedLengthDigits_iff hb).mp hL).2
    have hL₃ : L != [] := by simp [ne_nil_iff_length_pos, hL₁]
    refine ⟨L.head hL₃, hL₂ _ (L.head_mem hL₃), L.tail, ?_, cons_head_tail hL₃⟩
    refine (mem_fixedLengthDigits_iff hb).mpr ⟨?_, ?_⟩
    · rw [length_tail, hL₁, Nat.add_sub_cancel_right]
· exact fun x hx => hL₂ _ mem_of_mem_tail hx
  · rintro ⟨d, hd₁, T, hT, rfl⟩
    exact cons_mem_fixedLengthDigits_succ hb l d hd₁ hT

/--
theorem `sum_fixedLengthDigits_sum` / 定理 `sum_fixedLengthDigits_sum`

English:
theorem sum_fixedLengthDigits_sum
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: by
  induction l with
  | zero => simp
  | succ l hr =>
      by_cases hl : l = 0
      · simp [hl, fixedLengthDigits_one, Finset.sum_range_id, choose_two_right]
      rw [fixedLengthDigits_succ_eq_disjiUnion]; rw [Finset.sum_disjiUnion]
      simp only [consFixedLengthDigits, cons.injEq, true_and, 

中文:
定理 sum_fixedLengthDigits_sum
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: by
  induction l with
  | zero => simp
  | succ l hr =>
      by_cases hl : l = 0
      · simp [hl, fixedLengthDigits_one, Finset.sum_range_id, choose_two_right]
      rw [fixedLengthDigits_succ_eq_disjiUnion]; rw [Finset.sum_disjiUnion]
      simp only [consFixedLengthDigits, cons.injEq, true_and, 

Depends on / 依赖: Finset, Finset.card_range, Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_const, Finset.sum_disjiUnion, Finset.sum_image, Finset.sum_nsmul, Finset.sum_range_id, Set.injOn_of_eq_iff_eq, add_tsub_cancel_, card_range, choose_two_right, cons.injEq, consFixedLengthDigits, fixedLengthDigits_one, fixedLengthDigits_succ_eq_disjiUnion, implies_true, injOn_of_eq_iff_eq, nsmul_eq_mul
-/
theorem sum_fixedLengthDigits_sum {b : Nat} (hb : 1 < b) (l : Nat) :
    ∑ L in fixedLengthDigits hb l, L.sum = l * b ^ (l - 1) * b.choose 2 := by
  induction l with
  | zero => simp
  | succ l hr =>
      by_cases hl : l = 0
      · simp [hl, fixedLengthDigits_one, Finset.sum_range_id, choose_two_right]
      rw [fixedLengthDigits_succ_eq_disjiUnion]; rw [Finset.sum_disjiUnion]
      simp only [consFixedLengthDigits, cons.injEq, true_and, implies_true, Set.injOn_of_eq_iff_eq,
        Finset.sum_image, sum_cons]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_nsmul, Finset.sum_range_id, hr,
        nsmul_eq_mul, Finset.card_range, add_tsub_cancel_right, cast_id, card_fixedLengthDigits,
        choose_two_right]
      rw [show b ^ l = b * b ^ (l - 1) by rw [← Nat.pow_succ']; rw [Nat.sub_one]; rw [Nat.succ_pred hl]]
      ring

end List

/--
theorem `Nat.sum_sum_digits_eq` / 定理 `Nat.sum_sum_digits_eq`

English:
theorem Nat.sum_sum_digits_eq
  given: {b : Nat} (hb : 1 < b) (l : Nat)
  proof: by
  rw [← List.sum_fixedLengthDigits_sum hb]
  refine (Finset.sum_nbij (ofDigits b) (by exact (bijOn_ofDigits' hb l).1)
    (bijOn_ofDigits' hb l).2.1 (bijOn_ofDigits' hb l).2.2 fun L hL => ?_).symm
  rw [sum_digits_ofDigits_eq_sum hb ((List.mem_fixedLengthDigits_iff hb).mp hL)]

中文:
定理 Nat.sum_sum_digits_eq
  条件: {b : 自然数} (hb : 1 < b) (l : 自然数)
  证明: by
  rw [← List.sum_fixedLengthDigits_sum hb]
  refine (Finset.sum_nbij (ofDigits b) (by exact (bijOn_ofDigits' hb l).1)
    (bijOn_ofDigits' hb l).2.1 (bijOn_ofDigits' hb l).2.2 fun L hL => ?_).symm
  rw [sum_digits_ofDigits_eq_sum hb ((List.mem_fixedLengthDigits_iff hb).mp hL)]

Depends on / 依赖: Finset, Finset.sum_nbij, List.mem_fixedLengthDigits_iff, List.sum_fixedLengthDigits_sum, bijOn_ofDigits, mem_fixedLengthDigits_iff, ofDigits, sum_digits_ofDigits_eq_sum, sum_fixedLengthDigits_sum, sum_nbij
-/
theorem Nat.sum_sum_digits_eq {b : Nat} (hb : 1 < b) (l : Nat) :
    ∑ x in Finset.range (b ^ l), (b.digits x).sum = l * b ^ (l - 1) * b.choose 2 := by
  rw [← List.sum_fixedLengthDigits_sum hb]
  refine (Finset.sum_nbij (ofDigits b) (by exact (bijOn_ofDigits' hb l).1)
    (bijOn_ofDigits' hb l).2.1 (bijOn_ofDigits' hb l).2.2 fun L hL => ?_).symm
  rw [sum_digits_ofDigits_eq_sum hb ((List.mem_fixedLengthDigits_iff hb).mp hL)]
