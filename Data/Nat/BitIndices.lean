/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.List.Sort

/-!
# Bit Indices

Given `n : ℕ`, we define `Nat.bitIndices n`, which is the `List` of indices of `1`s in the
binary expansion of `n`. If `s : Finset ℕ` and `n = ∑ i ∈ s, 2 ^ i`, then
`Nat.bitIndices n` is the sorted list of elements of `s`.

The lemma `sum_map_two_pow_bitIndices` proves that summing `2 ^ i` over this list gives `n`.
This is used in `Combinatorics.colex` to construct a bijection `equivBitIndices : ℕ ≃ Finset ℕ`.

## TODO

Relate the material in this file to `Nat.digits` and `Nat.bits`.
-/

@[expose] public section

open List
namespace Nat

variable {a n : Nat}

/--
Definition of `bitIndices` / `bitIndices` 的定义

English:
definition bitIndices
  signature: (n : Nat)
  body: @binaryRec (fun _ => List Nat) [] (fun b _ s => b.casesOn (s.map (· + 1)) (0 :: s.map (· + 1))) n

中文:
定义 bitIndices
  签名: (n : 自然数)
  定义体: @binaryRec (fun _ => List Nat) [] (fun b _ s => b.casesOn (s.map (· + 1)) (0 :: s.map (· + 1))) n

Depends on / 依赖: b.casesOn, binaryRec, casesOn, s.map
-/
def bitIndices (n : Nat) : List Nat :=
  @binaryRec (fun _ => List Nat) [] (fun b _ s => b.casesOn (s.map (· + 1)) (0 :: s.map (· + 1))) n

/--
theorem `bitIndices_zero` / 定理 `bitIndices_zero`

English:
theorem bitIndices_zero
  statement: bitIndices 0 = []
  proof: by simp [bitIndices]

中文:
定理 bitIndices_zero
  结论: bitIndices 0 = []
  证明: by simp [bitIndices]
-/
@[simp] theorem bitIndices_zero : bitIndices 0 = [] := by simp [bitIndices]

/--
theorem `bitIndices_one` / 定理 `bitIndices_one`

English:
theorem bitIndices_one
  statement: bitIndices 1 = [0]
  proof: by simp [bitIndices]

中文:
定理 bitIndices_one
  结论: bitIndices 1 = [0]
  证明: by simp [bitIndices]

Depends on / 依赖: npowRecAuto
-/
@[simp] theorem bitIndices_one : bitIndices 1 = [0] := by simp [bitIndices]

/--
theorem `bitIndices_bit_true` / 定理 `bitIndices_bit_true`

English:
theorem bitIndices_bit_true
  given: (n : Nat)
  proof: binaryRec_eq _ _ (.inl rfl)

中文:
定理 bitIndices_bit_true
  条件: (n : 自然数)
  证明: binaryRec_eq _ _ (.inl rfl)

Depends on / 依赖: binaryRec_eq, npowRecAuto
-/
theorem bitIndices_bit_true (n : Nat) :
    bitIndices (bit true n) = 0 :: ((bitIndices n).map (· + 1)) :=
  binaryRec_eq _ _ (.inl rfl)

/--
theorem `bitIndices_bit_false` / 定理 `bitIndices_bit_false`

English:
theorem bitIndices_bit_false
  given: (n : Nat)
  proof: binaryRec_eq _ _ (.inl rfl)

中文:
定理 bitIndices_bit_false
  条件: (n : 自然数)
  证明: binaryRec_eq _ _ (.inl rfl)

Depends on / 依赖: binaryRec_eq
-/
theorem bitIndices_bit_false (n : Nat) :
    bitIndices (bit false n) = (bitIndices n).map (· + 1) :=
  binaryRec_eq _ _ (.inl rfl)

/--
theorem `bitIndices_two_mul_add_one` / 定理 `bitIndices_two_mul_add_one`

English:
theorem bitIndices_two_mul_add_one
  given: (n : Nat)
  proof: by
  rw [← bitIndices_bit_true]; rw [bit_true]

中文:
定理 bitIndices_two_mul_add_one
  条件: (n : 自然数)
  证明: by
  rw [← bitIndices_bit_true]; rw [bit_true]
-/
@[simp] theorem bitIndices_two_mul_add_one (n : Nat) :
    bitIndices (2 * n + 1) = 0 :: (bitIndices n).map (· + 1) := by
  rw [← bitIndices_bit_true]; rw [bit_true]

/--
theorem `bitIndices_two_mul` / 定理 `bitIndices_two_mul`

English:
theorem bitIndices_two_mul
  given: (n : Nat)
  proof: by
  rw [← bitIndices_bit_false]; rw [bit_false]

中文:
定理 bitIndices_two_mul
  条件: (n : 自然数)
  证明: by
  rw [← bitIndices_bit_false]; rw [bit_false]
-/
@[simp] theorem bitIndices_two_mul (n : Nat) :
    bitIndices (2 * n) = (bitIndices n).map (· + 1) := by
  rw [← bitIndices_bit_false]; rw [bit_false]

/--
theorem `bitIndices_sorted` / 定理 `bitIndices_sorted`

English:
theorem bitIndices_sorted
  given: {n : Nat}
  statement: n.bitIndices.SortedLT
  proof: by
  induction n using binaryRec with
  | zero => simp [sortedLT_iff_pairwise]
  | bit b n hs =>
    suffices List.Pairwise (fun a b => a < b) n.bitIndices by
      cases b <;> simpa [sortedLT_iff_pairwise, bit_false, bit_true, List.pairwise_map]
    exact List.Pairwise.imp (by simp) hs.pairwise

中文:
定理 bitIndices_sorted
  条件: {n : 自然数}
  结论: n.bitIndices.SortedLT
  证明: by
  induction n using binaryRec with
  | zero => simp [sortedLT_iff_pairwise]
  | bit b n hs =>
    suffices List.Pairwise (fun a b => a < b) n.bitIndices by
      cases b <;> simpa [sortedLT_iff_pairwise, bit_false, bit_true, List.pairwise_map]
    exact List.Pairwise.imp (by simp) hs.pairwise
-/
@[simp] theorem bitIndices_sorted {n : Nat} : n.bitIndices.SortedLT := by
  induction n using binaryRec with
  | zero => simp [sortedLT_iff_pairwise]
  | bit b n hs =>
    suffices List.Pairwise (fun a b => a < b) n.bitIndices by
      cases b <;> simpa [sortedLT_iff_pairwise, bit_false, bit_true, List.pairwise_map]
    exact List.Pairwise.imp (by simp) hs.pairwise

/--
theorem `bitIndices_nodup` / 定理 `bitIndices_nodup`

English:
theorem bitIndices_nodup
  given: {n : Nat}
  statement: n.bitIndices.Nodup
  proof: bitIndices_sorted.pairwise.nodup

中文:
定理 bitIndices_nodup
  条件: {n : 自然数}
  结论: n.bitIndices.Nodup
  证明: bitIndices_sorted.pairwise.nodup
-/
@[simp] theorem bitIndices_nodup {n : Nat} : n.bitIndices.Nodup := bitIndices_sorted.pairwise.nodup

/--
theorem `bitIndices_two_pow_mul` / 定理 `bitIndices_two_pow_mul`

English:
theorem bitIndices_two_pow_mul
  given: (k n : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_comm]; rw [pow_add]; rw [pow_one]; rw [mul_assoc]; rw [bitIndices_two_mul]; rw [ih]; rw [List.map_map]; rw [comp_add_right]
    simp [add_comm (a := 1)]

中文:
定理 bitIndices_two_pow_mul
  条件: (k n : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_comm]; rw [pow_add]; rw [pow_one]; rw [mul_assoc]; rw [bitIndices_two_mul]; rw [ih]; rw [List.map_map]; rw [comp_add_right]
    simp [add_comm (a := 1)]
-/
@[simp] theorem bitIndices_two_pow_mul (k n : Nat) :
    bitIndices (2 ^ k * n) = (bitIndices n).map (· + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_comm]; rw [pow_add]; rw [pow_one]; rw [mul_assoc]; rw [bitIndices_two_mul]; rw [ih]; rw [List.map_map]; rw [comp_add_right]
    simp [add_comm (a := 1)]

/--
theorem `bitIndices_two_pow` / 定理 `bitIndices_two_pow`

English:
theorem bitIndices_two_pow
  given: (k : Nat)
  statement: bitIndices (2 ^ k) = [k]
  proof: by
  rw [← mul_one (a := 2 ^ k)]; rw [bitIndices_two_pow_mul]; simp

中文:
定理 bitIndices_two_pow
  条件: (k : 自然数)
  结论: bitIndices (2 ^ k) = [k]
  证明: by
  rw [← mul_one (a := 2 ^ k)]; rw [bitIndices_two_pow_mul]; simp
-/
@[simp] theorem bitIndices_two_pow (k : Nat) : bitIndices (2 ^ k) = [k] := by
  rw [← mul_one (a := 2 ^ k)]; rw [bitIndices_two_pow_mul]; simp

/--
theorem `sum_map_two_pow_bitIndices` / 定理 `sum_map_two_pow_bitIndices`

English:
theorem sum_map_two_pow_bitIndices
  given: (n : Nat)
  proof: by
  induction n using binaryRec with
  | zero => simp
  | bit b n hs =>
    have hrw : (fun i => 2 ^ i) ∘ (fun x => x + 1) = fun i => 2 * 2 ^ i := by
      ext i; simp [pow_add, mul_comm]
    cases b
    · simpa [hrw, List.sum_map_mul_left]
    simp [hrw, List.sum_map_mul_left, hs, add_comm (a := 1)]

@[deprecated (since := "2026-05-15")] alias twoPowSum_bitIndices := sum_map_two_pow_bitIndices

中文:
定理 sum_map_two_pow_bitIndices
  条件: (n : 自然数)
  证明: by
  induction n using binaryRec with
  | zero => simp
  | bit b n hs =>
    have hrw : (fun i => 2 ^ i) ∘ (fun x => x + 1) = fun i => 2 * 2 ^ i := by
      ext i; simp [pow_add, mul_comm]
    cases b
    · simpa [hrw, List.sum_map_mul_left]
    simp [hrw, List.sum_map_mul_left, hs, add_comm (a := 1)]

@[deprecated (since := "2026-05-15")] alias twoPowSum_bitIndices := sum_map_two_pow_bitIndices
-/
@[simp] theorem sum_map_two_pow_bitIndices (n : Nat) :
    (n.bitIndices.map (fun i => 2 ^ i)).sum = n := by
  induction n using binaryRec with
  | zero => simp
  | bit b n hs =>
    have hrw : (fun i => 2 ^ i) ∘ (fun x => x + 1) = fun i => 2 * 2 ^ i := by
      ext i; simp [pow_add, mul_comm]
    cases b
    · simpa [hrw, List.sum_map_mul_left]
    simp [hrw, List.sum_map_mul_left, hs, add_comm (a := 1)]

@[deprecated (since := "2026-05-15")] alias twoPowSum_bitIndices := sum_map_two_pow_bitIndices

/--
theorem `mem_bitIndices` / 定理 `mem_bitIndices`

English:
theorem mem_bitIndices
  given: {i n : Nat}
  statement: i in n.bitIndices ↔ n.testBit i
  proof: by
  induction n using Nat.binaryRec generalizing i with
  | zero => simp
  | bit b n ih => cases b <;> cases i <;> simp_all [Nat.testBit_add_one, Nat.mul_add_div]

中文:
定理 mem_bitIndices
  条件: {i n : 自然数}
  结论: i in n.bitIndices ↔ n.testBit i
  证明: by
  induction n using Nat.binaryRec generalizing i with
  | zero => simp
  | bit b n ih => cases b <;> cases i <;> simp_all [Nat.testBit_add_one, Nat.mul_add_div]
-/
@[simp] theorem mem_bitIndices {i n : Nat} : i in n.bitIndices ↔ n.testBit i := by
  induction n using Nat.binaryRec generalizing i with
  | zero => simp
  | bit b n ih => cases b <;> cases i <;> simp_all [Nat.testBit_add_one, Nat.mul_add_div]

/--
theorem `bitIndices_sum_map_two_pow` / 定理 `bitIndices_sum_map_two_pow`

English:
theorem bitIndices_sum_map_two_pow
  given: {L : List Nat} (hL : List.SortedLT L)
  proof: by
  cases L with | nil => simp | cons a L =>
  obtain ⟨haL, hL⟩ := pairwise_cons.1 hL.pairwise
  simp_rw [Nat.lt_iff_add_one_le] at haL
  have h' : exists (L₀ : List Nat), L₀.SortedLT ∧ L = L₀.map (· + a + 1) := by
    refine ⟨L.map (· - (a+1)), ?_, ?_⟩
    · rwa [sortedLT_iff_pairwise, pairwise_map, Pairwise.and_mem,
        Pairwise.iff (S := fun x y => x in L ∧ y in L ∧ x < y), ← Pairwise.and_mem]
      simp only [and_congr_right_iff]
      exact fun x y hx _ => by rw [tsub_lt_tsub_iff_right (haL _ hx)]
    have h' : forall x in L, ((fun x => x + a + 1) ∘ (fun x => x - (a + 1))) x = x := fun x hx => by
      simp only [add_assoc, Function.comp_apply]; rw [tsub_add_cancel_of_le (haL _ hx)]
    simp [List.map_congr_left h']
  obtain ⟨L₀, hL₀, rfl⟩ := h'
  have hrw : (2 ^ ·) ∘ (· + a + 1) = fun i => 2 ^ a * (2 * 2 ^ i) := by
    ext x; simp only [Function.comp_apply, pow_add, pow_one]; ac_rfl
  simp only [List.map_cons, List.map_map, List.sum_map_mul_left, List.sum_cons, hrw]
  nth_rw 1 [← mul_one (a := 2 ^ a)]
  rw [← mul_add]; rw [bitIndices_two_pow_mul]; rw [add_comm]; rw [bitIndices_two_mul_add_one]; rw [bitIndices_sum_map_two_pow hL₀]
  simp [add_comm (a := 1), add_assoc]
termination_by L.length

@[deprecated (since := "2026-05-15")] alias bitIndices_twoPowsum := bitIndices_sum_map_two_pow

中文:
定理 bitIndices_sum_map_two_pow
  条件: {L : 列表 自然数} (hL : 列表.SortedLT L)
  证明: by
  cases L with | nil => simp | cons a L =>
  obtain ⟨haL, hL⟩ := pairwise_cons.1 hL.pairwise
  simp_rw [Nat.lt_iff_add_one_le] at haL
  have h' : exists (L₀ : List Nat), L₀.SortedLT ∧ L = L₀.map (· + a + 1) := by
    refine ⟨L.map (· - (a+1)), ?_, ?_⟩
    · rwa [sortedLT_iff_pairwise, pairwise_map, Pairwise.and_mem,
        Pairwise.iff (S := fun x y => x in L ∧ y in L ∧ x < y), ← Pairwise.and_mem]
      simp only [and_congr_right_iff]
      exact fun x y hx _ => by rw [tsub_lt_tsub_iff_right (haL _ hx)]
    have h' : forall x in L, ((fun x => x + a + 1) ∘ (fun x => x - (a + 1))) x = x := fun x hx => by
      simp only [add_assoc, Function.comp_apply]; rw [tsub_add_cancel_of_le (haL _ hx)]
    simp [List.map_congr_left h']
  obtain ⟨L₀, hL₀, rfl⟩ := h'
  have hrw : (2 ^ ·) ∘ (· + a + 1) = fun i => 2 ^ a * (2 * 2 ^ i) := by
    ext x; simp only [Function.comp_apply, pow_add, pow_one]; ac_rfl
  simp only [List.map_cons, List.map_map, List.sum_map_mul_left, List.sum_cons, hrw]
  nth_rw 1 [← mul_one (a := 2 ^ a)]
  rw [← mul_add]; rw [bitIndices_two_pow_mul]; rw [add_comm]; rw [bitIndices_two_mul_add_one]; rw [bitIndices_sum_map_two_pow hL₀]
  simp [add_comm (a := 1), add_assoc]
termination_by L.length

@[deprecated (since := "2026-05-15")] alias bitIndices_twoPowsum := bitIndices_sum_map_two_pow

Depends on / 依赖: L.map, Nat.lt_iff_add_one_le, Pairwise, Pairwise.and_mem, Pairwise.iff, SortedLT, and_congr_right_iff, and_mem, hL.pairwise, lt_iff_add_one_le, pairwise, pairwise_cons, pairwise_map, simp_rw, sortedLT_iff_pairwise, tsub_lt_tsub_iff_right
-/
theorem bitIndices_sum_map_two_pow {L : List Nat} (hL : List.SortedLT L) :
    (L.map (fun i => 2 ^ i)).sum.bitIndices = L := by
  cases L with | nil => simp | cons a L =>
  obtain ⟨haL, hL⟩ := pairwise_cons.1 hL.pairwise
  simp_rw [Nat.lt_iff_add_one_le] at haL
  have h' : exists (L₀ : List Nat), L₀.SortedLT ∧ L = L₀.map (· + a + 1) := by
    refine ⟨L.map (· - (a+1)), ?_, ?_⟩
    · rwa [sortedLT_iff_pairwise, pairwise_map, Pairwise.and_mem,
        Pairwise.iff (S := fun x y => x in L ∧ y in L ∧ x < y), ← Pairwise.and_mem]
      simp only [and_congr_right_iff]
      exact fun x y hx _ => by rw [tsub_lt_tsub_iff_right (haL _ hx)]
    have h' : forall x in L, ((fun x => x + a + 1) ∘ (fun x => x - (a + 1))) x = x := fun x hx => by
      simp only [add_assoc, Function.comp_apply]; rw [tsub_add_cancel_of_le (haL _ hx)]
    simp [List.map_congr_left h']
  obtain ⟨L₀, hL₀, rfl⟩ := h'
  have hrw : (2 ^ ·) ∘ (· + a + 1) = fun i => 2 ^ a * (2 * 2 ^ i) := by
    ext x; simp only [Function.comp_apply, pow_add, pow_one]; ac_rfl
  simp only [List.map_cons, List.map_map, List.sum_map_mul_left, List.sum_cons, hrw]
  nth_rw 1 [← mul_one (a := 2 ^ a)]
  rw [← mul_add]; rw [bitIndices_two_pow_mul]; rw [add_comm]; rw [bitIndices_two_mul_add_one]; rw [bitIndices_sum_map_two_pow hL₀]
  simp [add_comm (a := 1), add_assoc]
termination_by L.length

@[deprecated (since := "2026-05-15")] alias bitIndices_twoPowsum := bitIndices_sum_map_two_pow

/--
theorem `two_pow_le_of_mem_bitIndices` / 定理 `two_pow_le_of_mem_bitIndices`

English:
theorem two_pow_le_of_mem_bitIndices
  given: (ha : a in n.bitIndices)
  statement: 2 ^ a <= n
  proof: ge_two_pow_of_testBit (by simpa using ha)

中文:
定理 two_pow_le_of_mem_bitIndices
  条件: (ha : a in n.bitIndices)
  结论: 2 ^ a <= n
  证明: ge_two_pow_of_testBit (by simpa using ha)

Depends on / 依赖: ge_two_pow_of_testBit
-/
theorem two_pow_le_of_mem_bitIndices (ha : a in n.bitIndices) : 2 ^ a <= n :=
  ge_two_pow_of_testBit (by simpa using ha)

/--
theorem `notMem_bitIndices_self` / 定理 `notMem_bitIndices_self`

English:
theorem notMem_bitIndices_self
  given: (n : Nat)
  statement: n ∉ n.bitIndices
  proof: fun h => n.lt_two_pow_self.not_ge two_pow_le_of_mem_bitIndices h

中文:
定理 notMem_bitIndices_self
  条件: (n : 自然数)
  结论: n ∉ n.bitIndices
  证明: fun h => n.lt_two_pow_self.not_ge two_pow_le_of_mem_bitIndices h

Depends on / 依赖: lt_two_pow_self, n.lt_two_pow_self.not_ge, not_ge, two_pow_le_of_mem_bitIndices
-/
theorem notMem_bitIndices_self (n : Nat) : n ∉ n.bitIndices :=
fun h => n.lt_two_pow_self.not_ge two_pow_le_of_mem_bitIndices h

end Nat
