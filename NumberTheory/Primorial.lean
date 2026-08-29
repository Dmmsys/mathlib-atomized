/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Yury Kudryashov, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.PrimeCounting

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Squarefree

/-!
# Primorial

This file defines the primorial function (the product of primes less than or equal to some bound),
and proves that `primorial n ≤ 4 ^ n`.

## Notation

We use the local notation `n#` for the primorial of `n`: that is, the product of the primes less
than or equal to `n`.
-/

@[expose] public section


open Finset

open Nat

/--
Definition of `primorial` / `primorial` 的定义

English:
definition primorial
  signature: (n : Nat)
  body: ∏ p in range (n + 1) with p.Prime, p

local notation x "#" => primorial x

中文:
定义 primorial
  签名: (n : 自然数)
  定义体: ∏ p in range (n + 1) with p.Prime, p

local notation x "#" => primorial x

Depends on / 依赖: Finset, Finset.univ, filter_upwards, h.meas_biInter, meas_biInter, p.Prime
-/
def primorial (n : Nat) : Nat := ∏ p in range (n + 1) with p.Prime, p

local notation x "#" => primorial x

/--
lemma `primorial_eq_prod_primesLE` / 引理 `primorial_eq_prod_primesLE`

English:
lemma primorial_eq_prod_primesLE
  given: (n : Nat)
  statement: n # = ∏ p in primesLE n, p
  proof: rfl

中文:
引理 primorial_eq_prod_primesLE
  条件: (n : 自然数)
  结论: n # = ∏ p in primesLE n, p
  证明: rfl
-/
lemma primorial_eq_prod_primesLE (n : Nat) : n # = ∏ p in primesLE n, p := rfl

/--
lemma `primeFactors_primorial` / 引理 `primeFactors_primorial`

English:
lemma primeFactors_primorial
  given: (n : Nat)
  statement: primeFactors (n#) = primesLE n
  proof: by
  rw [primorial_eq_prod_primesLE]
  exact primeFactors_prod fun _ hp => prime_of_mem_primesLE hp

中文:
引理 primeFactors_primorial
  条件: (n : 自然数)
  结论: primeFactors (n#) = primesLE n
  证明: by
  rw [primorial_eq_prod_primesLE]
  exact primeFactors_prod fun _ hp => prime_of_mem_primesLE hp

Depends on / 依赖: primeFactors_prod, prime_of_mem_primesLE, primorial_eq_prod_primesLE
-/
lemma primeFactors_primorial (n : Nat) : primeFactors (n#) = primesLE n := by
  rw [primorial_eq_prod_primesLE]
  exact primeFactors_prod fun _ hp => prime_of_mem_primesLE hp

/--
theorem `primorial_zero` / 定理 `primorial_zero`

English:
theorem primorial_zero
  statement: 0 # = 1
  proof: by decide

中文:
定理 primorial_zero
  结论: 0 # = 1
  证明: by decide
-/
@[simp] theorem primorial_zero : 0 # = 1 := by decide

/--
theorem `primorial_one` / 定理 `primorial_one`

English:
theorem primorial_one
  statement: 1 # = 1
  proof: by decide

中文:
定理 primorial_one
  结论: 1 # = 1
  证明: by decide

Depends on / 依赖: Finset, Finset.univ, filter_upwards, h.meas_biInter, meas_biInter
-/
@[simp] theorem primorial_one : 1 # = 1 := by decide

/--
theorem `primorial_two` / 定理 `primorial_two`

English:
theorem primorial_two
  statement: 2 # = 2
  proof: by decide

中文:
定理 primorial_two
  结论: 2 # = 2
  证明: by decide

Depends on / 依赖: all_goals, eq_empty_or_singleton, subsingleton_of_subsingleton
-/
@[simp] theorem primorial_two : 2 # = 2 := by decide

/--
theorem `primorial_pos` / 定理 `primorial_pos`

English:
theorem primorial_pos
  given: (n : Nat)
  statement: 0 < n#
  proof: prod_pos fun _p hp => (mem_filter.1 hp).2.pos

中文:
定理 primorial_pos
  条件: (n : 自然数)
  结论: 0 < n#
  证明: prod_pos fun _p hp => (mem_filter.1 hp).2.pos

Depends on / 依赖: iIndep, mem_filter, prod_pos
-/
theorem primorial_pos (n : Nat) : 0 < n# :=
  prod_pos fun _p hp => (mem_filter.1 hp).2.pos

/--
lemma `primorial_ne_zero` / 引理 `primorial_ne_zero`

English:
lemma primorial_ne_zero
  given: (n : Nat)
  statement: n# != 0
  proof: (primorial_pos n).ne'

中文:
引理 primorial_ne_zero
  条件: (n : 自然数)
  结论: n# != 0
  证明: (primorial_pos n).ne'

Depends on / 依赖: Finset, Finset.forall_mem_image, Finset.prod_image, Finset.set_biInter_finset_image, Function, Function.extend, _apply, classical, extend, extend_apply, filter_upwards, forall_mem_image, hg.extend_apply, hg.injOn, primorial_pos, prod_image, s.image, set_biInter_finset_image, simp_rw
-/
lemma primorial_ne_zero (n : Nat) : n# != 0 := (primorial_pos n).ne'

/--
theorem `primorial_mono` / 定理 `primorial_mono`

English:
theorem primorial_mono
  given: {m n : Nat} (h : m <= n)
  statement: m# <= n#
  proof: prod_le_prod_of_subset_of_one_le' (by gcongr) (by grind)

中文:
定理 primorial_mono
  条件: {m n : 自然数} (h : m <= n)
  结论: m# <= n#
  证明: prod_le_prod_of_subset_of_one_le' (by gcongr) (by grind)

Depends on / 依赖: Function, Function.comp_assoc, Function.comp_id, comp_assoc, comp_eq_id, comp_id, convert, h.precomp, hasRightInverse, hg.hasRightInverse, injective, precomp, prod_le_prod_of_subset_of_one_le
-/
theorem primorial_mono {m n : Nat} (h : m <= n) : m# <= n# :=
  prod_le_prod_of_subset_of_one_le' (by gcongr) (by grind)

/--
theorem `primorial_monotone` / 定理 `primorial_monotone`

English:
theorem primorial_monotone
  statement: Monotone primorial
  proof: fun _ _ => primorial_mono

中文:
定理 primorial_monotone
  结论: 递增 primorial
  证明: fun _ _ => primorial_mono

Depends on / 依赖: primorial_mono
-/
theorem primorial_monotone : Monotone primorial := fun _ _ => primorial_mono

/--
theorem `primorial_dvd_primorial` / 定理 `primorial_dvd_primorial`

English:
theorem primorial_dvd_primorial
  given: {m n : Nat} (h : m <= n)
  statement: m# ∣ n#
  proof: prod_dvd_prod_of_subset _ _ _ (by gcongr)

中文:
定理 primorial_dvd_primorial
  条件: {m n : 自然数} (h : m <= n)
  结论: m# ∣ n#
  证明: prod_dvd_prod_of_subset _ _ _ (by gcongr)

Depends on / 依赖: iIndepSets, iIndepSets.precomp, precomp, prod_dvd_prod_of_subset
-/
theorem primorial_dvd_primorial {m n : Nat} (h : m <= n) : m# ∣ n# :=
  prod_dvd_prod_of_subset _ _ _ (by gcongr)

/--
theorem `primorial_succ` / 定理 `primorial_succ`

English:
theorem primorial_succ
  given: {n : Nat} (hn1 : n != 1) (hn : Odd n)
  statement: (n + 1)# = n#
  proof: by
  refine prod_congr ?_ fun _ _ => rfl
  rw [range_add_one]; rw [filter_insert]; rw [if_neg fun h => not_even_iff_odd.2 hn _]
exact fun h => h.even_sub_one mt succ.inj hn1

中文:
定理 primorial_succ
  条件: {n : 自然数} (hn1 : n != 1) (hn : Odd n)
  结论: (n + 1)# = n#
  证明: by
  refine prod_congr ?_ fun _ _ => rfl
  rw [range_add_one]; rw [filter_insert]; rw [if_neg fun h => not_even_iff_odd.2 hn _]
exact fun h => h.even_sub_one mt succ.inj hn1

Depends on / 依赖: even_sub_one, filter_insert, h.even_sub_one, iIndepSets, iIndepSets.of_precomp, if_neg, not_even_iff_odd, of_precomp, prod_congr, range_add_one, succ.inj
-/
theorem primorial_succ {n : Nat} (hn1 : n != 1) (hn : Odd n) : (n + 1)# = n# := by
  refine prod_congr ?_ fun _ _ => rfl
  rw [range_add_one]; rw [filter_insert]; rw [if_neg fun h => not_even_iff_odd.2 hn _]
exact fun h => h.even_sub_one mt succ.inj hn1

/--
theorem `primorial_add` / 定理 `primorial_add`

English:
theorem primorial_add
  given: (m n : Nat)
  proof: by
  simp_rw [primorial, ← Ico_zero_eq_range]
  rw [← prod_union]; rw [← filter_union]; rw [Ico_union_Ico_eq_Ico]
  exacts [Nat.zero_le _, by lia, disjoint_filter_filter <| Ico_disjoint_Ico_consecutive _ _ _]

中文:
定理 primorial_add
  条件: (m n : 自然数)
  证明: by
  simp_rw [primorial, ← Ico_zero_eq_range]
  rw [← prod_union]; rw [← filter_union]; rw [Ico_union_Ico_eq_Ico]
  exacts [Nat.zero_le _, by lia, disjoint_filter_filter <| Ico_disjoint_Ico_consecutive _ _ _]

Depends on / 依赖: Ico_disjoint_Ico_consecutive, Ico_union_Ico_eq_Ico, Ico_zero_eq_range, Nat.zero_le, disjoint_filter_filter, exacts, filter_union, primorial, prod_union, simp_rw, zero_le
-/
theorem primorial_add (m n : Nat) :
    (m + n)# = m# * ∏ p in Ico (m + 1) (m + n + 1) with p.Prime, p := by
  simp_rw [primorial, ← Ico_zero_eq_range]
  rw [← prod_union]; rw [← filter_union]; rw [Ico_union_Ico_eq_Ico]
  exacts [Nat.zero_le _, by lia, disjoint_filter_filter <| Ico_disjoint_Ico_consecutive _ _ _]

/--
theorem `primorial_add_dvd` / 定理 `primorial_add_dvd`

English:
theorem primorial_add_dvd
  given: {m n : Nat} (h : n <= m)
  statement: (m + n)# ∣ m# * choose (m + n) m
  proof: calc
    (m + n)# = m# * ∏ p in Ico (m + 1) (m + n + 1) with p.Prime, p := primorial_add _ _
    _ ∣ m# * choose (m + n) m :=
mul_dvd_mul_left _
        prod_primes_dvd _ (fun _ hk => (mem_filter.1 hk).2.prime) fun p hp => by
          rw [mem_filter]; rw [mem_Ico] at hp
          exact hp.2.dvd_choose_add hp.1.1 (h.trans_lt (m.lt_succ_self.trans_le hp.1.1))
              (Nat.lt_succ_iff.1 hp.1.2)

中文:
定理 primorial_add_dvd
  条件: {m n : 自然数} (h : n <= m)
  结论: (m + n)# ∣ m# * choose (m + n) m
  证明: calc
    (m + n)# = m# * ∏ p in Ico (m + 1) (m + n + 1) with p.Prime, p := primorial_add _ _
    _ ∣ m# * choose (m + n) m :=
mul_dvd_mul_left _
        prod_primes_dvd _ (fun _ hk => (mem_filter.1 hk).2.prime) fun p hp => by
          rw [mem_filter]; rw [mem_Ico] at hp
          exact hp.2.dvd_choose_add hp.1.1 (h.trans_lt (m.lt_succ_self.trans_le hp.1.1))
              (Nat.lt_succ_iff.1 hp.1.2)

Depends on / 依赖: Nat.lt_succ_iff, dvd_choose_add, h.trans_lt, iIndep, iIndep.precomp, lt_succ_iff, lt_succ_self, m.lt_succ_self.trans_le, mem_Ico, mem_filter, mul_dvd_mul_left, p.Prime, precomp, primorial_add, prod_primes_dvd, trans_le, trans_lt
-/
theorem primorial_add_dvd {m n : Nat} (h : n <= m) : (m + n)# ∣ m# * choose (m + n) m :=
  calc
    (m + n)# = m# * ∏ p in Ico (m + 1) (m + n + 1) with p.Prime, p := primorial_add _ _
    _ ∣ m# * choose (m + n) m :=
mul_dvd_mul_left _
        prod_primes_dvd _ (fun _ hk => (mem_filter.1 hk).2.prime) fun p hp => by
          rw [mem_filter]; rw [mem_Ico] at hp
          exact hp.2.dvd_choose_add hp.1.1 (h.trans_lt (m.lt_succ_self.trans_le hp.1.1))
              (Nat.lt_succ_iff.1 hp.1.2)

/--
theorem `primorial_add_le` / 定理 `primorial_add_le`

English:
theorem primorial_add_le
  given: {m n : Nat} (h : n <= m)
  statement: (m + n)# <= m# * choose (m + n) m
  proof: le_of_dvd (mul_pos (primorial_pos _) (choose_pos <| Nat.le_add_right _ _)) (primorial_add_dvd h)

中文:
定理 primorial_add_le
  条件: {m n : 自然数} (h : n <= m)
  结论: (m + n)# <= m# * choose (m + n) m
  证明: le_of_dvd (mul_pos (primorial_pos _) (choose_pos <| Nat.le_add_right _ _)) (primorial_add_dvd h)

Depends on / 依赖: Nat.le_add_right, choose_pos, iIndep, iIndep.of_precomp, le_add_right, le_of_dvd, mul_pos, of_precomp, primorial_add_dvd, primorial_pos
-/
theorem primorial_add_le {m n : Nat} (h : n <= m) : (m + n)# <= m# * choose (m + n) m :=
  le_of_dvd (mul_pos (primorial_pos _) (choose_pos <| Nat.le_add_right _ _)) (primorial_add_dvd h)

/--
lemma `Nat.Prime.dvd_primorial_iff` / 引理 `Nat.Prime.dvd_primorial_iff`

English:
lemma Nat.Prime.dvd_primorial_iff
  given: {p n : Nat} (hp : Prime p)
  statement: p ∣ n# ↔ p <= n
  proof: by
  refine ⟨?_, fun h => dvd_prod_of_mem _ (by grind)⟩
  intro h
  simp only [primorial, hp.prime.dvd_finsetProd_iff, mem_filter, mem_range_succ_iff] at h
  obtain ⟨q, ⟨hqn, hq⟩, hpq⟩ := h
  exact (Nat.le_of_dvd hq.pos hpq).trans hqn

中文:
引理 自然数.素.dvd_primorial_iff
  条件: {p n : 自然数} (hp : 素 p)
  结论: p ∣ n# ↔ p <= n
  证明: by
  refine ⟨?_, fun h => dvd_prod_of_mem _ (by grind)⟩
  intro h
  simp only [primorial, hp.prime.dvd_finsetProd_iff, mem_filter, mem_range_succ_iff] at h
  obtain ⟨q, ⟨hqn, hq⟩, hpq⟩ := h
  exact (Nat.le_of_dvd hq.pos hpq).trans hqn

Depends on / 依赖: Nat.le_of_dvd, dvd_finsetProd_iff, dvd_prod_of_mem, hp.prime.dvd_finsetProd_iff, hq.pos, le_of_dvd, mem_filter, mem_range_succ_iff, primorial
-/
lemma Nat.Prime.dvd_primorial_iff {p n : Nat} (hp : Prime p) : p ∣ n# ↔ p <= n := by
  refine ⟨?_, fun h => dvd_prod_of_mem _ (by grind)⟩
  intro h
  simp only [primorial, hp.prime.dvd_finsetProd_iff, mem_filter, mem_range_succ_iff] at h
  obtain ⟨q, ⟨hqn, hq⟩, hpq⟩ := h
  exact (Nat.le_of_dvd hq.pos hpq).trans hqn

/--
lemma `Nat.Prime.dvd_primorial` / 引理 `Nat.Prime.dvd_primorial`

English:
lemma Nat.Prime.dvd_primorial
  given: {p : Nat} (hp : Prime p)
  statement: p ∣ p#
  proof: hp.dvd_primorial_iff.2 le_rfl

中文:
引理 自然数.素.dvd_primorial
  条件: {p : 自然数} (hp : 素 p)
  结论: p ∣ p#
  证明: hp.dvd_primorial_iff.2 le_rfl

Depends on / 依赖: Set.inter_comm, dvd_primorial_iff, filter_upwards, hp.dvd_primorial_iff, inter_comm, le_rfl, mul_comm
-/
lemma Nat.Prime.dvd_primorial {p : Nat} (hp : Prime p) : p ∣ p# :=
  hp.dvd_primorial_iff.2 le_rfl

/--
lemma `Squarefree.dvd_primorial` / 引理 `Squarefree.dvd_primorial`

English:
lemma Squarefree.dvd_primorial
  given: {n : Nat} (hn : Squarefree n)
  statement: n ∣ n#
  proof: by
  have : (∏ p in n.primeFactors, p) ∣ (∏ p in range (n + 1) with p.Prime, p) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (by grind [le_of_dvd])
  rwa [Nat.prod_primeFactors_of_squarefree hn] at this

中文:
引理 Squarefree.dvd_primorial
  条件: {n : 自然数} (hn : Squarefree n)
  结论: n ∣ n#
  证明: by
  have : (∏ p in n.primeFactors, p) ∣ (∏ p in range (n + 1) with p.Prime, p) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (by grind [le_of_dvd])
  rwa [Nat.prod_primeFactors_of_squarefree hn] at this

Depends on / 依赖: Finset, Finset.prod_dvd_prod_of_subset, IndepSets, IndepSets.symm, Nat.prod_primeFactors_of_squarefree, le_of_dvd, n.primeFactors, p.Prime, primeFactors, prod_dvd_prod_of_subset, prod_primeFactors_of_squarefree
-/
lemma Squarefree.dvd_primorial {n : Nat} (hn : Squarefree n) : n ∣ n# := by
  have : (∏ p in n.primeFactors, p) ∣ (∏ p in range (n + 1) with p.Prime, p) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (by grind [le_of_dvd])
  rwa [Nat.prod_primeFactors_of_squarefree hn] at this

/--
lemma `lt_primorial_self` / 引理 `lt_primorial_self`

English:
lemma lt_primorial_self
  given: {n : Nat} (hn : 2 < n)
  statement: n < n#
  proof: by
  have : 3 <= n# := single_le_prod' (f := id) (by grind [-> Prime.pos]) (by grind [prime_three])
  let q := (n# - 1).minFac
  have : n < q := by
    by_contra! h1
    replace h1 : q ∣ n# := (minFac_prime (by lia)).dvd_primorial_iff.2 h1
    grind [minFac_eq_one_iff, dvd_one, dvd_sub_iff_right, minFac_dvd]
  grind [Nat.minFac_le]

中文:
引理 lt_primorial_self
  条件: {n : 自然数} (hn : 2 < n)
  结论: n < n#
  证明: by
  have : 3 <= n# := single_le_prod' (f := id) (by grind [-> Prime.pos]) (by grind [prime_three])
  let q := (n# - 1).minFac
  have : n < q := by
    by_contra! h1
    replace h1 : q ∣ n# := (minFac_prime (by lia)).dvd_primorial_iff.2 h1
    grind [minFac_eq_one_iff, dvd_one, dvd_sub_iff_right, minFac_dvd]
  grind [Nat.minFac_le]

Depends on / 依赖: Nat.minFac_le, Prime.pos, dvd_one, dvd_primorial_iff, dvd_sub_iff_right, minFac, minFac_dvd, minFac_eq_one_iff, minFac_le, minFac_prime, prime_three, replace, single_le_prod
-/
lemma lt_primorial_self {n : Nat} (hn : 2 < n) : n < n# := by
  have : 3 <= n# := single_le_prod' (f := id) (by grind [-> Prime.pos]) (by grind [prime_three])
  let q := (n# - 1).minFac
  have : n < q := by
    by_contra! h1
    replace h1 : q ∣ n# := (minFac_prime (by lia)).dvd_primorial_iff.2 h1
    grind [minFac_eq_one_iff, dvd_one, dvd_sub_iff_right, minFac_dvd]
  grind [Nat.minFac_le]

/--
lemma `le_primorial_self` / 引理 `le_primorial_self`

English:
lemma le_primorial_self
  given: {n : Nat}
  statement: n <= n#
  proof: by
  obtain hn | hn := le_or_gt n 2
  · decide +revert
  · exact (lt_primorial_self hn).le

中文:
引理 le_primorial_self
  条件: {n : 自然数}
  结论: n <= n#
  证明: by
  obtain hn | hn := le_or_gt n 2
  · decide +revert
  · exact (lt_primorial_self hn).le

Depends on / 依赖: le_or_gt, lt_primorial_self, revert
-/
lemma le_primorial_self {n : Nat} : n <= n# := by
  obtain hn | hn := le_or_gt n 2
  · decide +revert
  · exact (lt_primorial_self hn).le

/--
theorem `primorial_lt_four_pow` / 定理 `primorial_lt_four_pow`

English:
theorem primorial_lt_four_pow
  given: (n : Nat) (hn : n != 0)
  statement: n# < 4 ^ n
  proof: by
  induction n using Nat.strong_induction_on with | h n ihn =>
  rcases n with - | n; · grind
  rcases n.even_or_odd with ⟨m, rfl⟩ | ho
  · rcases m.eq_zero_or_pos with rfl | hm
    · decide
    calc
      (m + m + 1)# = (m + 1 + m)# := by rw [add_right_comm]
      _ <= (m + 1)# * choose (m + 1 + m) (m + 1) := primorial_add_le m.le_succ
      _ = (m + 1)# * choose (2 * m + 1) m := by rw [choose_symm_add, two_mul, add_right_comm]
      _ < 4 ^ (m + 1) * 4 ^ m :=
        Nat.mul_lt_mul_of_lt_of_le (ihn _ (by lia) (by lia)) (choose_middle_le_pow _) (by simp)
      _ <= 4 ^ (m + m + 1) := by rw [← pow_add, add_right_comm]
  · rcases Decidable.eq_or_ne n 1 with rfl | hn
    · decide
    · calc
        (n + 1)# = n# := primorial_succ hn ho
        _ < 4 ^ n := ihn n n.lt_succ_self (by grind)
        _ <= 4 ^ (n + 1) := Nat.pow_le_pow_right four_pos n.le_succ

中文:
定理 primorial_lt_four_pow
  条件: (n : 自然数) (hn : n != 0)
  结论: n# < 4 ^ n
  证明: by
  induction n using Nat.strong_induction_on with | h n ihn =>
  rcases n with - | n; · grind
  rcases n.even_or_odd with ⟨m, rfl⟩ | ho
  · rcases m.eq_zero_or_pos with rfl | hm
    · decide
    calc
      (m + m + 1)# = (m + 1 + m)# := by rw [add_right_comm]
      _ <= (m + 1)# * choose (m + 1 + m) (m + 1) := primorial_add_le m.le_succ
      _ = (m + 1)# * choose (2 * m + 1) m := by rw [choose_symm_add, two_mul, add_right_comm]
      _ < 4 ^ (m + 1) * 4 ^ m :=
        Nat.mul_lt_mul_of_lt_of_le (ihn _ (by lia) (by lia)) (choose_middle_le_pow _) (by simp)
      _ <= 4 ^ (m + m + 1) := by rw [← pow_add, add_right_comm]
  · rcases Decidable.eq_or_ne n 1 with rfl | hn
    · decide
    · calc
        (n + 1)# = n# := primorial_succ hn ho
        _ < 4 ^ n := ihn n n.lt_succ_self (by grind)
        _ <= 4 ^ (n + 1) := Nat.pow_le_pow_right four_pos n.le_succ

Depends on / 依赖: Nat.mul_lt_mul_of_lt_of_le, Nat.strong_induction_on, add_right_comm, choose_middle_le_p, choose_symm_add, eq_zero_or_pos, even_or_odd, le_succ, m.eq_zero_or_pos, m.le_succ, mul_lt_mul_of_lt_of_le, n.even_or_odd, primorial_add_le, strong_induction_on, two_mul
-/
theorem primorial_lt_four_pow (n : Nat) (hn : n != 0) : n# < 4 ^ n := by
  induction n using Nat.strong_induction_on with | h n ihn =>
  rcases n with - | n; · grind
  rcases n.even_or_odd with ⟨m, rfl⟩ | ho
  · rcases m.eq_zero_or_pos with rfl | hm
    · decide
    calc
      (m + m + 1)# = (m + 1 + m)# := by rw [add_right_comm]
      _ <= (m + 1)# * choose (m + 1 + m) (m + 1) := primorial_add_le m.le_succ
      _ = (m + 1)# * choose (2 * m + 1) m := by rw [choose_symm_add, two_mul, add_right_comm]
      _ < 4 ^ (m + 1) * 4 ^ m :=
        Nat.mul_lt_mul_of_lt_of_le (ihn _ (by lia) (by lia)) (choose_middle_le_pow _) (by simp)
      _ <= 4 ^ (m + m + 1) := by rw [← pow_add, add_right_comm]
  · rcases Decidable.eq_or_ne n 1 with rfl | hn
    · decide
    · calc
        (n + 1)# = n# := primorial_succ hn ho
        _ < 4 ^ n := ihn n n.lt_succ_self (by grind)
        _ <= 4 ^ (n + 1) := Nat.pow_le_pow_right four_pos n.le_succ

/--
theorem `primorial_le_four_pow` / 定理 `primorial_le_four_pow`

English:
theorem primorial_le_four_pow
  given: (n : Nat)
  statement: n# <= 4 ^ n
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · decide
  · exact (primorial_lt_four_pow n hn).le

@[deprecated (since := "2026-03-21")] alias primorial_le_4_pow := primorial_le_four_pow

中文:
定理 primorial_le_four_pow
  条件: (n : 自然数)
  结论: n# <= 4 ^ n
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · decide
  · exact (primorial_lt_four_pow n hn).le

@[deprecated (since := "2026-03-21")] alias primorial_le_4_pow := primorial_le_four_pow

Depends on / 依赖: eq_or_ne, primorial_lt_four_pow
-/
theorem primorial_le_four_pow (n : Nat) : n# <= 4 ^ n := by
  obtain rfl | hn := eq_or_ne n 0
  · decide
  · exact (primorial_lt_four_pow n hn).le

@[deprecated (since := "2026-03-21")] alias primorial_le_4_pow := primorial_le_four_pow

/--
lemma `squarefree_primorial` / 引理 `squarefree_primorial`

English:
lemma squarefree_primorial
  given: (n : Nat)
  statement: Squarefree (n#)
  proof: by
  rw [primorial_eq_prod_primesLE]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun _ hp _ hq hpq => ?_)
    fun _ hp => (prime_of_mem_primesLE hp).squarefree
  simp only [← coprime_iff_isRelPrime]
  exact (coprime_primes (prime_of_mem_primesLE hp) (prime_of_mem_primesLE hq)).mpr hpq

中文:
引理 squarefree_primorial
  条件: (n : 自然数)
  结论: Squarefree (n#)
  证明: by
  rw [primorial_eq_prod_primesLE]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun _ hp _ hq hpq => ?_)
    fun _ hp => (prime_of_mem_primesLE hp).squarefree
  simp only [← coprime_iff_isRelPrime]
  exact (coprime_primes (prime_of_mem_primesLE hp) (prime_of_mem_primesLE hq)).mpr hpq

Depends on / 依赖: Finset, Finset.squarefree_prod_of_pairwise_isCoprime, coprime_iff_isRelPrime, coprime_primes, prime_of_mem_primesLE, primorial_eq_prod_primesLE, squarefree, squarefree_prod_of_pairwise_isCoprime
-/
lemma squarefree_primorial (n : Nat) : Squarefree (n#) := by
  rw [primorial_eq_prod_primesLE]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun _ hp _ hq hpq => ?_)
    fun _ hp => (prime_of_mem_primesLE hp).squarefree
  simp only [← coprime_iff_isRelPrime]
  exact (coprime_primes (prime_of_mem_primesLE hp) (prime_of_mem_primesLE hq)).mpr hpq
