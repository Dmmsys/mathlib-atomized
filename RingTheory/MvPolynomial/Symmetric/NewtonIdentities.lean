/-
Copyright (c) 2023 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fintype.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Newton's Identities

This file defines `MvPolynomial` power sums as a means of implementing Newton's identities. The
combinatorial proof, due to Zeilberger, defines for `k : ℕ` a subset `pairs` of
`(range k).powerset × range k` and a map `pairMap` such that `pairMap` is an involution on `pairs`,
and a map `weight` which identifies elements of `pairs` with the terms of the summation in Newton's
identities and which satisfies `weight ∘ pairMap = -weight`. The result therefore follows neatly
from an identity implemented in mathlib as `Finset.sum_involution`. Namely, we use
`Finset.sum_involution` to show that `∑ t ∈ pairs σ k, weight σ R k t = 0`. We then identify
`(-1) ^ k * k * esymm σ R k` with the terms of the weight sum for which `t.fst` has
cardinality `k`, and `(-1) ^ i * esymm σ R i * psum σ R (k - i)` with the terms of the weight sum
for which `t.fst` has cardinality `i` for `i < k`, and we thereby derive the main result
`(-1) ^ k * k * esymm σ R k + ∑ i ∈ range k, (-1) ^ i * esymm σ R i * psum σ R (k - i) = 0` (or
rather, two equivalent forms which provide direct definitions for `esymm` and `psum` in lower-degree
terms).

## Main declarations

* `MvPolynomial.mul_esymm_eq_sum`: a recurrence relation for the `k`th elementary
  symmetric polynomial in terms of lower-degree elementary symmetric polynomials and power sums.

* `MvPolynomial.psum_eq_mul_esymm_sub_sum`: a recurrence relation for the degree-`k` power sum
  in terms of lower-degree elementary symmetric polynomials and power sums.

## References

See [zeilberger1984] for the combinatorial proof of Newton's identities.
-/

public section

open Equiv (Perm)

open MvPolynomial

noncomputable section

namespace MvPolynomial

open Finset Nat

namespace NewtonIdentities

variable (σ : Type*) (R : Type*) [CommRing R]

section DecidableEq

variable [DecidableEq σ]

/--
Definition of `pairMap` / `pairMap` 的定义

English:
definition pairMap
  signature: (t : Finset σ × σ)
  body: if h : t.snd in t.fst then (t.fst.erase t.snd, t.snd) else (t.fst.cons t.snd h, t.snd)

中文:
定义 pairMap
  签名: (t : 有限集 σ × σ)
  定义体: if h : t.snd in t.fst then (t.fst.erase t.snd, t.snd) else (t.fst.cons t.snd h, t.snd)
-/
private def pairMap (t : Finset σ × σ) : Finset σ × σ :=
  if h : t.snd in t.fst then (t.fst.erase t.snd, t.snd) else (t.fst.cons t.snd h, t.snd)

/--
lemma `pairMap_ne_self` / 引理 `pairMap_ne_self`

English:
lemma pairMap_ne_self
  given: (t : Finset σ × σ)
  statement: pairMap σ t != t
  proof: by
  rw [pairMap]
  split_ifs with h1
  all_goals by_contra ht; rw [← ht] at h1; simp_all

中文:
引理 pairMap_ne_self
  条件: (t : 有限集 σ × σ)
  结论: pairMap σ t != t
  证明: by
  rw [pairMap]
  split_ifs with h1
  all_goals by_contra ht; rw [← ht] at h1; simp_all
-/
private lemma pairMap_ne_self (t : Finset σ × σ) : pairMap σ t != t := by
  rw [pairMap]
  split_ifs with h1
  all_goals by_contra ht; rw [← ht] at h1; simp_all

/--
lemma `pairMap_of_snd_mem_fst` / 引理 `pairMap_of_snd_mem_fst`

English:
lemma pairMap_of_snd_mem_fst
  given: {t : Finset σ × σ} (h : t.snd in t.fst)
  proof: by
  simp [pairMap, h]

中文:
引理 pairMap_of_snd_mem_fst
  条件: {t : 有限集 σ × σ} (h : t.snd in t.fst)
  证明: by
  simp [pairMap, h]
-/
private lemma pairMap_of_snd_mem_fst {t : Finset σ × σ} (h : t.snd in t.fst) :
    pairMap σ t = (t.fst.erase t.snd, t.snd) := by
  simp [pairMap, h]

/--
lemma `pairMap_of_snd_notMem_fst` / 引理 `pairMap_of_snd_notMem_fst`

English:
lemma pairMap_of_snd_notMem_fst
  given: {t : Finset σ × σ} (h : t.snd ∉ t.fst)
  proof: by
  simp [pairMap, h]

@[simp]

中文:
引理 pairMap_of_snd_notMem_fst
  条件: {t : 有限集 σ × σ} (h : t.snd ∉ t.fst)
  证明: by
  simp [pairMap, h]

@[simp]
-/
private lemma pairMap_of_snd_notMem_fst {t : Finset σ × σ} (h : t.snd ∉ t.fst) :
    pairMap σ t = (t.fst.cons t.snd h, t.snd) := by
  simp [pairMap, h]

@[simp]
/--
theorem `pairMap_involutive` / 定理 `pairMap_involutive`

English:
theorem pairMap_involutive
  statement: (pairMap σ).Involutive
  proof: by
  intro t
  rw [pairMap]; rw [pairMap]
  split_ifs with h1 h2 h3
  · simp at h2
  · simp [insert_erase h1]
  · simp_all
  · simp at h3

中文:
定理 pairMap_involutive
  结论: (pairMap σ).对合
  证明: by
  intro t
  rw [pairMap]; rw [pairMap]
  split_ifs with h1 h2 h3
  · simp at h2
  · simp [insert_erase h1]
  · simp_all
  · simp at h3
-/
private theorem pairMap_involutive : (pairMap σ).Involutive := by
  intro t
  rw [pairMap]; rw [pairMap]
  split_ifs with h1 h2 h3
  · simp at h2
  · simp [insert_erase h1]
  · simp_all
  · simp at h3

variable [Fintype σ]

/--
Definition of `pairs` / `pairs` 的定义

English:
definition pairs
  signature: (k : Nat)
  body: {t | #t.1 <= k ∧ (#t.1 = k -> t.snd in t.fst)}

@[simp]

中文:
定义 pairs
  签名: (k : 自然数)
  定义体: {t | #t.1 <= k ∧ (#t.1 = k -> t.snd in t.fst)}

@[simp]
-/
private def pairs (k : Nat) : Finset (Finset σ × σ) :=
  {t | #t.1 <= k ∧ (#t.1 = k -> t.snd in t.fst)}

@[simp]
/--
lemma `mem_pairs` / 引理 `mem_pairs`

English:
lemma mem_pairs
  given: (k : Nat) (t : Finset σ × σ)
  proof: by
  simp [pairs]

中文:
引理 mem_pairs
  条件: (k : 自然数) (t : 有限集 σ × σ)
  证明: by
  simp [pairs]
-/
private lemma mem_pairs (k : Nat) (t : Finset σ × σ) :
    t in pairs σ k ↔ #t.1 <= k ∧ (#t.1 = k -> t.snd in t.fst) := by
  simp [pairs]

/--
Definition of `weight` / `weight` 的定义

English:
definition weight
  signature: (k : Nat) (t : Finset σ × σ)
  body: (-1) ^ #t.1 * ((∏ a in t.fst, X a) * X t.snd ^ (k - #t.1))

中文:
定义 weight
  签名: (k : 自然数) (t : 有限集 σ × σ)
  定义体: (-1) ^ #t.1 * ((∏ a in t.fst, X a) * X t.snd ^ (k - #t.1))
-/
private def weight (k : Nat) (t : Finset σ × σ) : MvPolynomial σ R :=
  (-1) ^ #t.1 * ((∏ a in t.fst, X a) * X t.snd ^ (k - #t.1))

/--
theorem `pairMap_mem_pairs` / 定理 `pairMap_mem_pairs`

English:
theorem pairMap_mem_pairs
  given: {k : Nat} (t : Finset σ × σ) (h : t in pairs σ k)
  proof: by
  rw [mem_pairs] at h ⊢
  rcases (em (t.snd in t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [h1, implies_true, and_true] at h
    simp only [card_erase_of_mem h1, tsub_le_iff_right, mem_erase, ne_eq, h1]
    refine ⟨le_succ_of_le h, ?_⟩
    by_contra h2
    simp only [not_true_eq_false, and_true, not_forall, not_false_eq_true, exists_prop] at h2
    rw [← h2] at h
    exact not_le_of_gt (sub_lt (card_pos.mpr ⟨t.snd, h1⟩) zero_lt_one) h
  · rw [pairMap_of_snd_notMem_fst σ h1]
    simp only [h1] at h
    simp only [card_cons, mem_cons, true_or, implies_true, and_true]
    exact (le_iff_eq_or_lt.mp h.left).resolve_left h.right

中文:
定理 pairMap_mem_pairs
  条件: {k : 自然数} (t : 有限集 σ × σ) (h : t in pairs σ k)
  证明: by
  rw [mem_pairs] at h ⊢
  rcases (em (t.snd in t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [h1, implies_true, and_true] at h
    simp only [card_erase_of_mem h1, tsub_le_iff_right, mem_erase, ne_eq, h1]
    refine ⟨le_succ_of_le h, ?_⟩
    by_contra h2
    simp only [not_true_eq_false, and_true, not_forall, not_false_eq_true, exists_prop] at h2
    rw [← h2] at h
    exact not_le_of_gt (sub_lt (card_pos.mpr ⟨t.snd, h1⟩) zero_lt_one) h
  · rw [pairMap_of_snd_notMem_fst σ h1]
    simp only [h1] at h
    simp only [card_cons, mem_cons, true_or, implies_true, and_true]
    exact (le_iff_eq_or_lt.mp h.left).resolve_left h.right
-/
private theorem pairMap_mem_pairs {k : Nat} (t : Finset σ × σ) (h : t in pairs σ k) :
    pairMap σ t in pairs σ k := by
  rw [mem_pairs] at h ⊢
  rcases (em (t.snd in t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [h1, implies_true, and_true] at h
    simp only [card_erase_of_mem h1, tsub_le_iff_right, mem_erase, ne_eq, h1]
    refine ⟨le_succ_of_le h, ?_⟩
    by_contra h2
    simp only [not_true_eq_false, and_true, not_forall, not_false_eq_true, exists_prop] at h2
    rw [← h2] at h
    exact not_le_of_gt (sub_lt (card_pos.mpr ⟨t.snd, h1⟩) zero_lt_one) h
  · rw [pairMap_of_snd_notMem_fst σ h1]
    simp only [h1] at h
    simp only [card_cons, mem_cons, true_or, implies_true, and_true]
    exact (le_iff_eq_or_lt.mp h.left).resolve_left h.right

/--
theorem `weight_add_weight_pairMap` / 定理 `weight_add_weight_pairMap`

English:
theorem weight_add_weight_pairMap
  given: {k : Nat} (t : Finset σ × σ) (h : t in pairs σ k)
  proof: by
  rw [weight]; rw [weight]
  rw [mem_pairs] at h
  have h2 (n : Nat) : -(-1 : MvPolynomial σ R) ^ n = (-1) ^ (n + 1) := by
    rw [← neg_one_mul ((-1 : MvPolynomial σ R) ^ n)]; rw [pow_add]; rw [pow_one]; rw [mul_comm]
  rcases (em (t.snd in t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [← prod_erase_mul t.fst (fun j => (X j : MvPolynomial σ R)) h1,
      mul_assoc (∏ a in erase t.fst t.snd, X a), card_erase_of_mem h1]
    nth_rewrite 1 [← pow_one (X t.snd)]
    simp only [← pow_add, add_comm]
    have h3 : 1 <= #t.1 := lt_iff_add_one_le.mp (card_pos.mpr ⟨t.snd, h1⟩)
    rw [← tsub_tsub_assoc h.left h3]; rw [← neg_neg ((-1 : MvPolynomial σ R) ^ (#t.1 - 1))]; rw [h2 (#t.1 - 1)]; rw [Nat.sub_add_cancel h3]
    simp
  · rw [pairMap_of_snd_notMem_fst σ h1]
    simp only [mul_comm, mul_assoc (∏ a in t.fst, X a), card_cons, prod_cons]
    nth_rewrite 2 [← pow_one (X t.snd)]
    simp only [← pow_add, ← Nat.add_sub_assoc (Nat.lt_of_le_of_ne h.left (mt h.right h1)), add_comm,
      Nat.succ_eq_add_one, Nat.add_sub_add_right]
    rw [← neg_neg ((-1 : MvPolynomial σ R) ^ #t.1)]; rw [h2]
    simp

中文:
定理 weight_add_weight_pairMap
  条件: {k : 自然数} (t : 有限集 σ × σ) (h : t in pairs σ k)
  证明: by
  rw [weight]; rw [weight]
  rw [mem_pairs] at h
  have h2 (n : Nat) : -(-1 : MvPolynomial σ R) ^ n = (-1) ^ (n + 1) := by
    rw [← neg_one_mul ((-1 : MvPolynomial σ R) ^ n)]; rw [pow_add]; rw [pow_one]; rw [mul_comm]
  rcases (em (t.snd in t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [← prod_erase_mul t.fst (fun j => (X j : MvPolynomial σ R)) h1,
      mul_assoc (∏ a in erase t.fst t.snd, X a), card_erase_of_mem h1]
    nth_rewrite 1 [← pow_one (X t.snd)]
    simp only [← pow_add, add_comm]
    have h3 : 1 <= #t.1 := lt_iff_add_one_le.mp (card_pos.mpr ⟨t.snd, h1⟩)
    rw [← tsub_tsub_assoc h.left h3]; rw [← neg_neg ((-1 : MvPolynomial σ R) ^ (#t.1 - 1))]; rw [h2 (#t.1 - 1)]; rw [Nat.sub_add_cancel h3]
    simp
  · rw [pairMap_of_snd_notMem_fst σ h1]
    simp only [mul_comm, mul_assoc (∏ a in t.fst, X a), card_cons, prod_cons]
    nth_rewrite 2 [← pow_one (X t.snd)]
    simp only [← pow_add, ← Nat.add_sub_assoc (Nat.lt_of_le_of_ne h.left (mt h.right h1)), add_comm,
      Nat.succ_eq_add_one, Nat.add_sub_add_right]
    rw [← neg_neg ((-1 : MvPolynomial σ R) ^ #t.1)]; rw [h2]
    simp
-/
private theorem weight_add_weight_pairMap {k : Nat} (t : Finset σ × σ) (h : t in pairs σ k) :
    weight σ R k t + weight σ R k (pairMap σ t) = 0 := by
  rw [weight]; rw [weight]
  rw [mem_pairs] at h
  have h2 (n : Nat) : -(-1 : MvPolynomial σ R) ^ n = (-1) ^ (n + 1) := by
    rw [← neg_one_mul ((-1 : MvPolynomial σ R) ^ n)]; rw [pow_add]; rw [pow_one]; rw [mul_comm]
  rcases (em (t.snd in t.fst)) with h1 | h1
  · rw [pairMap_of_snd_mem_fst σ h1]
    simp only [← prod_erase_mul t.fst (fun j => (X j : MvPolynomial σ R)) h1,
      mul_assoc (∏ a in erase t.fst t.snd, X a), card_erase_of_mem h1]
    nth_rewrite 1 [← pow_one (X t.snd)]
    simp only [← pow_add, add_comm]
    have h3 : 1 <= #t.1 := lt_iff_add_one_le.mp (card_pos.mpr ⟨t.snd, h1⟩)
    rw [← tsub_tsub_assoc h.left h3]; rw [← neg_neg ((-1 : MvPolynomial σ R) ^ (#t.1 - 1))]; rw [h2 (#t.1 - 1)]; rw [Nat.sub_add_cancel h3]
    simp
  · rw [pairMap_of_snd_notMem_fst σ h1]
    simp only [mul_comm, mul_assoc (∏ a in t.fst, X a), card_cons, prod_cons]
    nth_rewrite 2 [← pow_one (X t.snd)]
    simp only [← pow_add, ← Nat.add_sub_assoc (Nat.lt_of_le_of_ne h.left (mt h.right h1)), add_comm,
      Nat.succ_eq_add_one, Nat.add_sub_add_right]
    rw [← neg_neg ((-1 : MvPolynomial σ R) ^ #t.1)]; rw [h2]
    simp

/--
theorem `weight_sum` / 定理 `weight_sum`

English:
theorem weight_sum
  given: (k : Nat)
  statement: ∑ t in pairs σ k, weight σ R k t = 0
  proof: sum_involution (fun t _ => pairMap σ t) (weight_add_weight_pairMap σ R)
    (fun t _ => (fun _ => pairMap_ne_self σ t)) (pairMap_mem_pairs σ)
    (fun t _ => pairMap_involutive σ t)

中文:
定理 weight_sum
  条件: (k : 自然数)
  结论: ∑ t in pairs σ k, weight σ R k t = 0
  证明: sum_involution (fun t _ => pairMap σ t) (weight_add_weight_pairMap σ R)
    (fun t _ => (fun _ => pairMap_ne_self σ t)) (pairMap_mem_pairs σ)
    (fun t _ => pairMap_involutive σ t)
-/
private theorem weight_sum (k : Nat) : ∑ t in pairs σ k, weight σ R k t = 0 :=
  sum_involution (fun t _ => pairMap σ t) (weight_add_weight_pairMap σ R)
    (fun t _ => (fun _ => pairMap_ne_self σ t)) (pairMap_mem_pairs σ)
    (fun t _ => pairMap_involutive σ t)

/--
theorem `sum_filter_pairs_eq_sum_powersetCard_sum` / 定理 `sum_filter_pairs_eq_sum_powersetCard_sum`

English:
theorem sum_filter_pairs_eq_sum_powersetCard_sum
  statement: (k : Nat)
  proof: by
  apply sum_finset_product
  aesop

中文:
定理 sum_filter_pairs_eq_sum_powersetCard_sum
  结论: (k : 自然数)
  证明: by
  apply sum_finset_product
  aesop
-/
private theorem sum_filter_pairs_eq_sum_powersetCard_sum (k : Nat)
    (f : Finset σ × σ -> MvPolynomial σ R) :
    ∑ t in pairs σ k with #t.1 = k, f t = ∑ A in powersetCard k univ, ∑ j in A, f (A, j) := by
  apply sum_finset_product
  aesop

/--
theorem `sum_filter_pairs_eq_sum_powersetCard_mem_filter_antidiagonal_sum` / 定理 `sum_filter_pairs_eq_sum_powersetCard_mem_filter_antidiagonal_sum`

English:
theorem sum_filter_pairs_eq_sum_powersetCard_mem_filter_antidiagonal_sum
  statement: (k : Nat) (a : Nat × Nat)
  proof: by
  apply sum_finset_product
  simp only [mem_filter, mem_powersetCard_univ, mem_univ, and_true, and_iff_right_iff_imp]
  rintro p hp
  have : #p.fst <= k := by apply le_of_lt; simp_all
  aesop

中文:
定理 sum_filter_pairs_eq_sum_powersetCard_mem_filter_antidiagonal_sum
  结论: (k : 自然数) (a : 自然数 × 自然数)
  证明: by
  apply sum_finset_product
  simp only [mem_filter, mem_powersetCard_univ, mem_univ, and_true, and_iff_right_iff_imp]
  rintro p hp
  have : #p.fst <= k := by apply le_of_lt; simp_all
  aesop
-/
private theorem sum_filter_pairs_eq_sum_powersetCard_mem_filter_antidiagonal_sum (k : Nat) (a : Nat × Nat)
    (ha : a in {a in antidiagonal k | a.fst < k}) (f : Finset σ × σ -> MvPolynomial σ R) :
    ∑ t in pairs σ k with #t.1 = a.1, f t = ∑ A in powersetCard a.1 univ, ∑ j, f (A, j) := by
  apply sum_finset_product
  simp only [mem_filter, mem_powersetCard_univ, mem_univ, and_true, and_iff_right_iff_imp]
  rintro p hp
  have : #p.fst <= k := by apply le_of_lt; simp_all
  aesop

set_option backward.isDefEq.respectTransparency false in
/--
lemma `filter_pairs_lt` / 引理 `filter_pairs_lt`

English:
lemma filter_pairs_lt
  given: (k : Nat)
  proof: by ext; aesop (add unsafe le_of_lt)

中文:
引理 filter_pairs_lt
  条件: (k : 自然数)
  证明: by ext; aesop (add unsafe le_of_lt)
-/
private lemma filter_pairs_lt (k : Nat) :
    (pairs σ k).filter (fun (s, _) => #s < k) =
      (range k).disjiUnion (powersetCard · univ) ((pairwise_disjoint_powersetCard _).set_pairwise _)
        ×ˢ univ := by ext; aesop (add unsafe le_of_lt)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum` / 定理 `sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum`

English:
theorem sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum
  statement: (k : Nat)
  proof: by
  rw [filter_pairs_lt]; rw [sum_product]; rw [sum_disjiUnion]
  refine sum_nbij' (fun n => (n, k - n)) Prod.fst ?_ ?_ ?_ ?_ ?_ <;>
    simp +contextual [@eq_comm _ _ k, le_of_lt]

中文:
定理 sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum
  结论: (k : 自然数)
  证明: by
  rw [filter_pairs_lt]; rw [sum_product]; rw [sum_disjiUnion]
  refine sum_nbij' (fun n => (n, k - n)) Prod.fst ?_ ?_ ?_ ?_ ?_ <;>
    simp +contextual [@eq_comm _ _ k, le_of_lt]
-/
private theorem sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum (k : Nat)
    (f : Finset σ × σ -> MvPolynomial σ R) :
    ∑ t in pairs σ k with #t.1 < k, f t =
      ∑ a in antidiagonal k with a.fst < k, ∑ A in powersetCard a.fst univ, ∑ j, f (A, j) := by
  rw [filter_pairs_lt]; rw [sum_product]; rw [sum_disjiUnion]
  refine sum_nbij' (fun n => (n, k - n)) Prod.fst ?_ ?_ ?_ ?_ ?_ <;>
    simp +contextual [@eq_comm _ _ k, le_of_lt]

/--
theorem `disjoint_filter_pairs_lt_filter_pairs_eq` / 定理 `disjoint_filter_pairs_lt_filter_pairs_eq`

English:
theorem disjoint_filter_pairs_lt_filter_pairs_eq
  given: (k : Nat)
  proof: by
  rw [disjoint_filter]
  exact fun _ _ h1 h2 => lt_irrefl _ (h2.symm.subst h1)

中文:
定理 disjoint_filter_pairs_lt_filter_pairs_eq
  条件: (k : 自然数)
  证明: by
  rw [disjoint_filter]
  exact fun _ _ h1 h2 => lt_irrefl _ (h2.symm.subst h1)
-/
private theorem disjoint_filter_pairs_lt_filter_pairs_eq (k : Nat) :
    Disjoint {t in pairs σ k | #t.1 < k} {t in pairs σ k | #t.1 = k} := by
  rw [disjoint_filter]
  exact fun _ _ h1 h2 => lt_irrefl _ (h2.symm.subst h1)

/--
theorem `disjUnion_filter_pairs_eq_pairs` / 定理 `disjUnion_filter_pairs_eq_pairs`

English:
theorem disjUnion_filter_pairs_eq_pairs
  given: (k : Nat)
  proof: by
  grind [MvPolynomial.NewtonIdentities.pairs]

中文:
定理 disjUnion_filter_pairs_eq_pairs
  条件: (k : 自然数)
  证明: by
  grind [MvPolynomial.NewtonIdentities.pairs]
-/
private theorem disjUnion_filter_pairs_eq_pairs (k : Nat) :
    disjUnion {t in pairs σ k | #t.1 < k} {t in pairs σ k | #t.1 = k}
      (disjoint_filter_pairs_lt_filter_pairs_eq σ k) = pairs σ k := by
  grind [MvPolynomial.NewtonIdentities.pairs]

end DecidableEq

variable [Fintype σ]

/--
theorem `esymm_summand_to_weight` / 定理 `esymm_summand_to_weight`

English:
theorem esymm_summand_to_weight
  given: (k : Nat) (A : Finset σ) (h : A in powersetCard k univ)
  proof: by
  simp [weight, mem_powersetCard_univ.mp h, mul_assoc]

中文:
定理 esymm_summand_to_weight
  条件: (k : 自然数) (A : 有限集 σ) (h : A in powersetCard k univ)
  证明: by
  simp [weight, mem_powersetCard_univ.mp h, mul_assoc]
-/
private theorem esymm_summand_to_weight (k : Nat) (A : Finset σ) (h : A in powersetCard k univ) :
    ∑ j in A, weight σ R k (A, j) = k * (-1) ^ k * (∏ i in A, X i : MvPolynomial σ R) := by
  simp [weight, mem_powersetCard_univ.mp h, mul_assoc]

/--
theorem `esymm_to_weight` / 定理 `esymm_to_weight`

English:
theorem esymm_to_weight
  given: [DecidableEq σ] (k : Nat)
  statement: k * esymm σ R k =
  proof: by
  rw [esymm]; rw [sum_filter_pairs_eq_sum_powersetCard_sum σ R k (fun t => weight σ R k t)]; rw [sum_congr rfl (esymm_summand_to_weight σ R k)]; rw [mul_comm (k : MvPolynomial σ R) ((-1) ^ k)]; rw [← mul_sum]; rw [← mul_assoc]; rw [← mul_assoc]; rw [← pow_add]; rw [Even.neg_one_pow ⟨k]; rw [rfl⟩]; rw [one_mul]

中文:
定理 esymm_to_weight
  条件: [DecidableEq σ] (k : 自然数)
  结论: k * esymm σ R k =
  证明: by
  rw [esymm]; rw [sum_filter_pairs_eq_sum_powersetCard_sum σ R k (fun t => weight σ R k t)]; rw [sum_congr rfl (esymm_summand_to_weight σ R k)]; rw [mul_comm (k : MvPolynomial σ R) ((-1) ^ k)]; rw [← mul_sum]; rw [← mul_assoc]; rw [← mul_assoc]; rw [← pow_add]; rw [Even.neg_one_pow ⟨k]; rw [rfl⟩]; rw [one_mul]
-/
private theorem esymm_to_weight [DecidableEq σ] (k : Nat) : k * esymm σ R k =
    (-1) ^ k * ∑ t in pairs σ k with #t.1 = k, weight σ R k t := by
  rw [esymm]; rw [sum_filter_pairs_eq_sum_powersetCard_sum σ R k (fun t => weight σ R k t)]; rw [sum_congr rfl (esymm_summand_to_weight σ R k)]; rw [mul_comm (k : MvPolynomial σ R) ((-1) ^ k)]; rw [← mul_sum]; rw [← mul_assoc]; rw [← mul_assoc]; rw [← pow_add]; rw [Even.neg_one_pow ⟨k]; rw [rfl⟩]; rw [one_mul]

/--
theorem `esymm_mul_psum_summand_to_weight` / 定理 `esymm_mul_psum_summand_to_weight`

English:
theorem esymm_mul_psum_summand_to_weight
  given: (k : Nat) (a : Nat × Nat) (ha : a in antidiagonal k)
  proof: by
  simp only [esymm, psum, weight, ← mul_assoc, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun s hs => ?_
  rw [mem_powersetCard_univ.mp hs]; rw [← mem_antidiagonal.mp ha]; rw [add_sub_self_left]

中文:
定理 esymm_mul_psum_summand_to_weight
  条件: (k : 自然数) (a : 自然数 × 自然数) (ha : a in antidiagonal k)
  证明: by
  simp only [esymm, psum, weight, ← mul_assoc, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun s hs => ?_
  rw [mem_powersetCard_univ.mp hs]; rw [← mem_antidiagonal.mp ha]; rw [add_sub_self_left]
-/
private theorem esymm_mul_psum_summand_to_weight (k : Nat) (a : Nat × Nat) (ha : a in antidiagonal k) :
    ∑ A in powersetCard a.fst univ, ∑ j, weight σ R k (A, j) =
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd := by
  simp only [esymm, psum, weight, ← mul_assoc, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun s hs => ?_
  rw [mem_powersetCard_univ.mp hs]; rw [← mem_antidiagonal.mp ha]; rw [add_sub_self_left]

/--
theorem `esymm_mul_psum_to_weight` / 定理 `esymm_mul_psum_to_weight`

English:
theorem esymm_mul_psum_to_weight
  given: [DecidableEq σ] (k : Nat)
  proof: by
  rw [← sum_congr rfl (fun a ha => esymm_mul_psum_summand_to_weight σ R k a (mem_filter.mp ha).left)]; rw [sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum σ R k]

中文:
定理 esymm_mul_psum_to_weight
  条件: [DecidableEq σ] (k : 自然数)
  证明: by
  rw [← sum_congr rfl (fun a ha => esymm_mul_psum_summand_to_weight σ R k a (mem_filter.mp ha).left)]; rw [sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum σ R k]
-/
private theorem esymm_mul_psum_to_weight [DecidableEq σ] (k : Nat) :
    ∑ a in antidiagonal k with a.fst < k, (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd =
      ∑ t in pairs σ k with #t.1 < k, weight σ R k t := by
  rw [← sum_congr rfl (fun a ha => esymm_mul_psum_summand_to_weight σ R k a (mem_filter.mp ha).left)]; rw [sum_filter_pairs_eq_sum_filter_antidiagonal_powersetCard_sum σ R k]

end NewtonIdentities

variable (σ : Type*) [Fintype σ] (R : Type*) [CommRing R]

/--
theorem `mul_esymm_eq_sum` / 定理 `mul_esymm_eq_sum`

English:
theorem mul_esymm_eq_sum
  given: (k : Nat)
  proof: by
  classical
  rw [NewtonIdentities.esymm_to_weight σ R k]; rw [NewtonIdentities.esymm_mul_psum_to_weight σ R k]; rw [eq_comm]; rw [← sub_eq_zero]; rw [sub_eq_add_neg]; rw [neg_mul_eq_neg_mul]; rw [neg_eq_neg_one_mul ((-1 : MvPolynomial σ R) ^ k)]
  nth_rw 2 [← pow_one (-1 : MvPolynomial σ R)]
  rw [← pow_add]; rw [add_comm 1 k]; rw [← left_distrib]; rw [← sum_disjUnion (NewtonIdentities.disjoint_filter_pairs_lt_filter_pairs_eq σ k)]; rw [NewtonIdentities.disjUnion_filter_pairs_eq_pairs σ k]; rw [NewtonIdentities.weight_sum σ R k]; rw [neg_one_pow_mul_eq_zero_iff.mpr rfl]

中文:
定理 mul_esymm_eq_sum
  条件: (k : 自然数)
  证明: by
  classical
  rw [NewtonIdentities.esymm_to_weight σ R k]; rw [NewtonIdentities.esymm_mul_psum_to_weight σ R k]; rw [eq_comm]; rw [← sub_eq_zero]; rw [sub_eq_add_neg]; rw [neg_mul_eq_neg_mul]; rw [neg_eq_neg_one_mul ((-1 : MvPolynomial σ R) ^ k)]
  nth_rw 2 [← pow_one (-1 : MvPolynomial σ R)]
  rw [← pow_add]; rw [add_comm 1 k]; rw [← left_distrib]; rw [← sum_disjUnion (NewtonIdentities.disjoint_filter_pairs_lt_filter_pairs_eq σ k)]; rw [NewtonIdentities.disjUnion_filter_pairs_eq_pairs σ k]; rw [NewtonIdentities.weight_sum σ R k]; rw [neg_one_pow_mul_eq_zero_iff.mpr rfl]

Depends on / 依赖: MvPolynomial, NewtonIdentities, NewtonIdentities.disjUnion_filter_pairs_eq_pairs, NewtonIdentities.disjoint_filter_pairs_lt_filter_pairs_eq, NewtonIdentities.esymm_mul_psum_to_weight, NewtonIdentities.esymm_to_weight, add_comm, classical, disjUnion_filter_pairs_eq_pairs, disjoint_filter_pairs_lt_filter_pairs_eq, eq_comm, esymm_mul_psum_to_weight, esymm_to_weight, left_distrib, neg_eq_neg_one_mul, neg_mul_eq_neg_mul, nth_rw, pow_add, pow_one, sub_eq_add_neg
-/
theorem mul_esymm_eq_sum (k : Nat) :
    k * esymm σ R k = (-1) ^ (k + 1) *
      ∑ a in antidiagonal k with a.1 < k, (-1) ^ a.1 * esymm σ R a.1 * psum σ R a.2 := by
  classical
  rw [NewtonIdentities.esymm_to_weight σ R k]; rw [NewtonIdentities.esymm_mul_psum_to_weight σ R k]; rw [eq_comm]; rw [← sub_eq_zero]; rw [sub_eq_add_neg]; rw [neg_mul_eq_neg_mul]; rw [neg_eq_neg_one_mul ((-1 : MvPolynomial σ R) ^ k)]
  nth_rw 2 [← pow_one (-1 : MvPolynomial σ R)]
  rw [← pow_add]; rw [add_comm 1 k]; rw [← left_distrib]; rw [← sum_disjUnion (NewtonIdentities.disjoint_filter_pairs_lt_filter_pairs_eq σ k)]; rw [NewtonIdentities.disjUnion_filter_pairs_eq_pairs σ k]; rw [NewtonIdentities.weight_sum σ R k]; rw [neg_one_pow_mul_eq_zero_iff.mpr rfl]

/--
theorem `sum_antidiagonal_card_esymm_psum_eq_zero` / 定理 `sum_antidiagonal_card_esymm_psum_eq_zero`

English:
theorem sum_antidiagonal_card_esymm_psum_eq_zero
  proof: by
  let k := Fintype.card σ
  suffices (-1 : MvPolynomial σ R) ^ (k + 1) *
      ∑ a in antidiagonal k, (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0 by
    simpa using this
  simp [k, ← sum_filter_add_sum_filter_not (antidiagonal k) (fun a => a.fst < k),
    ← mul_esymm_eq_sum, mul_add, ← mul_assoc, ← pow_add, mul_comm ↑k (esymm σ R k)]

中文:
定理 sum_antidiagonal_card_esymm_psum_eq_zero
  证明: by
  let k := Fintype.card σ
  suffices (-1 : MvPolynomial σ R) ^ (k + 1) *
      ∑ a in antidiagonal k, (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0 by
    simpa using this
  simp [k, ← sum_filter_add_sum_filter_not (antidiagonal k) (fun a => a.fst < k),
    ← mul_esymm_eq_sum, mul_add, ← mul_assoc, ← pow_add, mul_comm ↑k (esymm σ R k)]

Depends on / 依赖: Fintype, Fintype.card, MvPolynomial, a.fst, a.snd, antidiagonal, mul_add, mul_assoc, mul_comm, mul_esymm_eq_sum, pow_add, sum_filter_add_sum_filter_not
-/
theorem sum_antidiagonal_card_esymm_psum_eq_zero :
    ∑ a in antidiagonal (Fintype.card σ), (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0 := by
  let k := Fintype.card σ
  suffices (-1 : MvPolynomial σ R) ^ (k + 1) *
      ∑ a in antidiagonal k, (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd = 0 by
    simpa using this
  simp [k, ← sum_filter_add_sum_filter_not (antidiagonal k) (fun a => a.fst < k),
    ← mul_esymm_eq_sum, mul_add, ← mul_assoc, ← pow_add, mul_comm ↑k (esymm σ R k)]

/--
theorem `psum_eq_mul_esymm_sub_sum` / 定理 `psum_eq_mul_esymm_sub_sum`

English:
theorem psum_eq_mul_esymm_sub_sum
  given: (k : Nat) (h : 0 < k)
  proof: by
  simp only [Set.Ioo, Set.mem_ofPred_eq, and_comm]
  have hesymm := mul_esymm_eq_sum σ R k
  rw [← (sum_filter_add_sum_filter_not {a in antidiagonal k | a.fst < k}
    (fun a => 0 < a.fst) (fun a => (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd))] at hesymm
  have sub_both_sides := congrArg (· - (-1 : MvPolynomial σ R) ^ (k + 1) *
    ∑ a in {a in antidiagonal k | a.fst < k} with 0 < a.fst,
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd) hesymm
  simp only [left_distrib, add_sub_cancel_left] at sub_both_sides
  have sub_both_sides := congrArg ((-1 : MvPolynomial σ R) ^ (k + 1) * ·) sub_both_sides
  simp only [mul_sub_left_distrib, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩, one_mul,
    filter_filter (fun a : Nat × Nat => a.fst < k) (fun a => ¬0 < a.fst)]
    at sub_both_sides
  have : {a in antidiagonal k | a.fst < k ∧ ¬0 < a.fst} = {(0, k)} := by
    ext a
    rw [mem_filter]; rw [mem_antidiagonal]; rw [mem_singleton]
    refine ⟨?_, by rintro rfl; lia⟩
    rintro ⟨ha, ⟨_, ha0⟩⟩
    rw [← ha]; rw [Nat.eq_zero_of_not_pos ha0]; rw [zero_add]; rw [← Nat.eq_zero_of_not_pos ha0]
  rw [this]; rw [sum_singleton] at sub_both_sides
  simp only [_root_.pow_zero, esymm_zero, mul_one, one_mul, filter_filter] at sub_both_sides
  exact sub_both_sides.symm

中文:
定理 psum_eq_mul_esymm_sub_sum
  条件: (k : 自然数) (h : 0 < k)
  证明: by
  simp only [Set.Ioo, Set.mem_ofPred_eq, and_comm]
  have hesymm := mul_esymm_eq_sum σ R k
  rw [← (sum_filter_add_sum_filter_not {a in antidiagonal k | a.fst < k}
    (fun a => 0 < a.fst) (fun a => (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd))] at hesymm
  have sub_both_sides := congrArg (· - (-1 : MvPolynomial σ R) ^ (k + 1) *
    ∑ a in {a in antidiagonal k | a.fst < k} with 0 < a.fst,
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd) hesymm
  simp only [left_distrib, add_sub_cancel_left] at sub_both_sides
  have sub_both_sides := congrArg ((-1 : MvPolynomial σ R) ^ (k + 1) * ·) sub_both_sides
  simp only [mul_sub_left_distrib, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩, one_mul,
    filter_filter (fun a : Nat × Nat => a.fst < k) (fun a => ¬0 < a.fst)]
    at sub_both_sides
  have : {a in antidiagonal k | a.fst < k ∧ ¬0 < a.fst} = {(0, k)} := by
    ext a
    rw [mem_filter]; rw [mem_antidiagonal]; rw [mem_singleton]
    refine ⟨?_, by rintro rfl; lia⟩
    rintro ⟨ha, ⟨_, ha0⟩⟩
    rw [← ha]; rw [Nat.eq_zero_of_not_pos ha0]; rw [zero_add]; rw [← Nat.eq_zero_of_not_pos ha0]
  rw [this]; rw [sum_singleton] at sub_both_sides
  simp only [_root_.pow_zero, esymm_zero, mul_one, one_mul, filter_filter] at sub_both_sides
  exact sub_both_sides.symm

Depends on / 依赖: MvPolynomial, Set.Ioo, Set.mem_ofPred_eq, a.fst, a.snd, add_sub_cancel_left, and_comm, antidiagonal, hesymm, left_distrib, mem_ofPred_eq, mul_esymm_eq_sum, sub_both_sid, sub_both_sides, sum_filter_add_sum_filter_not
-/
theorem psum_eq_mul_esymm_sub_sum (k : Nat) (h : 0 < k) :
    psum σ R k = (-1) ^ (k + 1) * k * esymm σ R k -
    ∑ a in antidiagonal k with a.1 in Set.Ioo 0 k, (-1) ^ a.fst * esymm σ R a.1 * psum σ R a.2 := by
  simp only [Set.Ioo, Set.mem_ofPred_eq, and_comm]
  have hesymm := mul_esymm_eq_sum σ R k
  rw [← (sum_filter_add_sum_filter_not {a in antidiagonal k | a.fst < k}
    (fun a => 0 < a.fst) (fun a => (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd))] at hesymm
  have sub_both_sides := congrArg (· - (-1 : MvPolynomial σ R) ^ (k + 1) *
    ∑ a in {a in antidiagonal k | a.fst < k} with 0 < a.fst,
    (-1) ^ a.fst * esymm σ R a.fst * psum σ R a.snd) hesymm
  simp only [left_distrib, add_sub_cancel_left] at sub_both_sides
  have sub_both_sides := congrArg ((-1 : MvPolynomial σ R) ^ (k + 1) * ·) sub_both_sides
  simp only [mul_sub_left_distrib, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k + 1, rfl⟩, one_mul,
    filter_filter (fun a : Nat × Nat => a.fst < k) (fun a => ¬0 < a.fst)]
    at sub_both_sides
  have : {a in antidiagonal k | a.fst < k ∧ ¬0 < a.fst} = {(0, k)} := by
    ext a
    rw [mem_filter]; rw [mem_antidiagonal]; rw [mem_singleton]
    refine ⟨?_, by rintro rfl; lia⟩
    rintro ⟨ha, ⟨_, ha0⟩⟩
    rw [← ha]; rw [Nat.eq_zero_of_not_pos ha0]; rw [zero_add]; rw [← Nat.eq_zero_of_not_pos ha0]
  rw [this]; rw [sum_singleton] at sub_both_sides
  simp only [_root_.pow_zero, esymm_zero, mul_one, one_mul, filter_filter] at sub_both_sides
  exact sub_both_sides.symm

end MvPolynomial
