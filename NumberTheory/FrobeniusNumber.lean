/-
Copyright (c) 2021 Alex Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Zhao, Daniel Buth, Sebastian Meier, Junyan Xu
-/
module

public import Mathlib.RingTheory.Ideal.NatInt

/-!
# Frobenius Number

In this file we first define a predicate for Frobenius numbers, then solve the 2-variable variant
of this problem. We also show the Frobenius number exists for any set of coprime natural numbers
that doesn't contain 1. This is closely related to the fact that all ideals of ℕ are finitely
generated, which we also prove in this file.

## Theorem Statement

Given a finite set of relatively prime integers all greater than 1, their Frobenius number is the
largest positive integer that cannot be expressed as a sum of nonnegative multiples of these
integers. Here we show the Frobenius number of two relatively prime integers `m` and `n` greater
than 1 is `m * n - m - n`. This result is also known as the Chicken McNugget Theorem.

## Implementation Notes

First we define Frobenius numbers in general using `IsGreatest` and `AddSubmonoid.closure`. Then
we proceed to compute the Frobenius number of `m` and `n`.

For the upper bound, we begin with an auxiliary lemma showing `m * n` is not attainable, then show
`m * n - m - n` is not attainable. Then for the construction, we create a `k_1` which is `k mod n`
and `0 mod m`, then show it is at most `k`. Then `k_1` is a multiple of `m`, so `(k-k_1)`
is a multiple of n, and we're done.

## Tags

frobenius number, chicken mcnugget, chinese remainder theorem, AddSubmonoid.closure
-/

@[expose] public section


open Nat

/--
Definition of `FrobeniusNumber` / `FrobeniusNumber` 的定义

English:
definition FrobeniusNumber
  signature: (n : Nat) (s : Set Nat)
  body: IsGreatest { k | k ∉ AddSubmonoid.closure s } n

中文:
定义 FrobeniusNumber
  签名: (n : 自然数) (s : 集合 自然数)
  定义体: IsGreatest { k | k ∉ AddSubmonoid.closure s } n

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure, IsGreatest, closure
-/
def FrobeniusNumber (n : Nat) (s : Set Nat) : Prop :=
  IsGreatest { k | k ∉ AddSubmonoid.closure s } n

/--
theorem `frobeniusNumber_iff` / 定理 `frobeniusNumber_iff`

English:
theorem frobeniusNumber_iff
  given: {n : Nat} {s : Set Nat}
  proof: by
  simp_rw [FrobeniusNumber, IsGreatest, upperBounds, Set.mem_ofPred, not_imp_comm, not_le]

中文:
定理 frobeniusNumber_iff
  条件: {n : 自然数} {s : 集合 自然数}
  证明: by
  simp_rw [FrobeniusNumber, IsGreatest, upperBounds, Set.mem_ofPred, not_imp_comm, not_le]

Depends on / 依赖: FrobeniusNumber, IsGreatest, Set.mem_ofPred, mem_ofPred, not_imp_comm, not_le, simp_rw, upperBounds
-/
theorem frobeniusNumber_iff {n : Nat} {s : Set Nat} :
    FrobeniusNumber n s ↔ n ∉ AddSubmonoid.closure s ∧ forall k > n, k in AddSubmonoid.closure s := by
  simp_rw [FrobeniusNumber, IsGreatest, upperBounds, Set.mem_ofPred, not_imp_comm, not_le]

variable {m n : Nat}

/--
theorem `frobeniusNumber_pair` / 定理 `frobeniusNumber_pair`

English:
theorem frobeniusNumber_pair
  given: (cop : Coprime m n) (hm : 1 < m) (hn : 1 < n)
  proof: by
  simp_rw [FrobeniusNumber, AddSubmonoid.mem_closure_pair]
  have hmn : m + n <= m * n := add_le_mul hm hn
  constructor
  · push Not
    intro a b h
    apply cop.mul_add_mul_ne_mul (add_one_ne_zero a) (add_one_ne_zero b)
    simp only [Nat.sub_sub, smul_eq_mul] at h
    zify [hmn] at h ⊢
    rw

中文:
定理 frobeniusNumber_pair
  条件: (cop : Coprime m n) (hm : 1 < m) (hn : 1 < n)
  证明: by
  simp_rw [FrobeniusNumber, AddSubmonoid.mem_closure_pair]
  have hmn : m + n <= m * n := add_le_mul hm hn
  constructor
  · push Not
    intro a b h
    apply cop.mul_add_mul_ne_mul (add_one_ne_zero a) (add_one_ne_zero b)
    simp only [Nat.sub_sub, smul_eq_mul] at h
    zify [hmn] at h ⊢
    rw

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_closure_pair, FrobeniusNumber, Nat.sub_sub, add_le_mul, add_one_ne_zero, contrapose, cop.gcd_eq_one, cop.mul_add_mul_ne_mul, exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le, gcd_eq_one, mem_closure_pair, mul_add_mul_ne_mul, mul_pred, pred_eq_sub_one, pred_mul, simp_rw, smul_eq_mul, sub_eq_zero, sub_sub
-/
theorem frobeniusNumber_pair (cop : Coprime m n) (hm : 1 < m) (hn : 1 < n) :
    FrobeniusNumber (m * n - m - n) {m, n} := by
  simp_rw [FrobeniusNumber, AddSubmonoid.mem_closure_pair]
  have hmn : m + n <= m * n := add_le_mul hm hn
  constructor
  · push Not
    intro a b h
    apply cop.mul_add_mul_ne_mul (add_one_ne_zero a) (add_one_ne_zero b)
    simp only [Nat.sub_sub, smul_eq_mul] at h
    zify [hmn] at h ⊢
    rw [← sub_eq_zero] at h ⊢
    rw [← h]
    ring
  · intro k hk
    dsimp at hk
    contrapose! hk
    obtain ⟨a, b, h⟩ := exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le m n k
      (by simp [cop.gcd_eq_one]) (by grind [pred_mul, mul_pred, pred_eq_sub_one])
    exact ⟨a, b, succ_inj.mp (congrArg succ h)⟩

namespace Nat

open Submodule.IsPrincipal

/--
Definition of `setGcd` / `setGcd` 的定义

English:
definition setGcd
  signature: (s : Set Nat)
  body: (generator <| Ideal.span <| ((↑) : Nat -> Int) '' s).natAbs

中文:
定义 setGcd
  签名: (s : 集合 自然数)
  定义体: (generator <| Ideal.span <| ((↑) : Nat -> Int) '' s).natAbs

Depends on / 依赖: Ideal.span, generator, natAbs
-/
noncomputable def setGcd (s : Set Nat) : Nat :=
  (generator <| Ideal.span <| ((↑) : Nat -> Int) '' s).natAbs

variable {s t : Set Nat} {n : Nat}

/--
lemma `setGcd_dvd_of_mem` / 引理 `setGcd_dvd_of_mem`

English:
lemma setGcd_dvd_of_mem
  given: (h : n in s)
  statement: setGcd s ∣ n
  proof: by
  rw [setGcd]; rw [← Int.dvd_natCast]; rw [← mem_iff_generator_dvd]
  exact Ideal.subset_span ⟨n, h, rfl⟩

中文:
引理 setGcd_dvd_of_mem
  条件: (h : n in s)
  结论: setGcd s ∣ n
  证明: by
  rw [setGcd]; rw [← Int.dvd_natCast]; rw [← mem_iff_generator_dvd]
  exact Ideal.subset_span ⟨n, h, rfl⟩

Depends on / 依赖: Ideal.subset_span, Int.dvd_natCast, dvd_natCast, mem_iff_generator_dvd, setGcd, subset_span
-/
lemma setGcd_dvd_of_mem (h : n in s) : setGcd s ∣ n := by
  rw [setGcd]; rw [← Int.dvd_natCast]; rw [← mem_iff_generator_dvd]
  exact Ideal.subset_span ⟨n, h, rfl⟩

/--
lemma `setGcd_dvd_of_mem_closure` / 引理 `setGcd_dvd_of_mem_closure`

English:
lemma setGcd_dvd_of_mem_closure
  given: (h : n in AddSubmonoid.closure s)
  statement: setGcd s ∣ n
  proof: AddSubmonoid.closure_induction (fun _ => setGcd_dvd_of_mem) (dvd_zero _) (fun _ _ _ _ => dvd_add) h

中文:
引理 setGcd_dvd_of_mem_closure
  条件: (h : n in 加法子幺半群.closure s)
  结论: setGcd s ∣ n
  证明: AddSubmonoid.closure_induction (fun _ => setGcd_dvd_of_mem) (dvd_zero _) (fun _ _ _ _ => dvd_add) h

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure_induction, closure_induction, dvd_add, dvd_zero, setGcd_dvd_of_mem
-/
lemma setGcd_dvd_of_mem_closure (h : n in AddSubmonoid.closure s) : setGcd s ∣ n :=
  AddSubmonoid.closure_induction (fun _ => setGcd_dvd_of_mem) (dvd_zero _) (fun _ _ _ _ => dvd_add) h

/--
lemma `dvd_setGcd_iff` / 引理 `dvd_setGcd_iff`

English:
lemma dvd_setGcd_iff
  statement: n ∣ setGcd s ↔ forall m in s, n ∣ m
  proof: by
  simp_rw [setGcd, ← Int.natCast_dvd, dvd_generator_span_iff,
    Set.forall_mem_image, Int.natCast_dvd_natCast]

中文:
引理 dvd_setGcd_iff
  结论: n ∣ setGcd s ↔ 对任意 m in s, n ∣ m
  证明: by
  simp_rw [setGcd, ← Int.natCast_dvd, dvd_generator_span_iff,
    Set.forall_mem_image, Int.natCast_dvd_natCast]

Depends on / 依赖: Int.natCast_dvd, Int.natCast_dvd_natCast, Set.forall_mem_image, dvd_generator_span_iff, forall_mem_image, natCast_dvd, natCast_dvd_natCast, setGcd, simp_rw
-/
lemma dvd_setGcd_iff : n ∣ setGcd s ↔ forall m in s, n ∣ m := by
  simp_rw [setGcd, ← Int.natCast_dvd, dvd_generator_span_iff,
    Set.forall_mem_image, Int.natCast_dvd_natCast]

/--
lemma `setGcd_mono` / 引理 `setGcd_mono`

English:
lemma setGcd_mono
  given: (h : s subseteq t)
  statement: setGcd t ∣ setGcd s
  proof: dvd_setGcd_iff.mpr fun _m hm => setGcd_dvd_of_mem (h hm)

中文:
引理 setGcd_mono
  条件: (h : s subseteq t)
  结论: setGcd t ∣ setGcd s
  证明: dvd_setGcd_iff.mpr fun _m hm => setGcd_dvd_of_mem (h hm)

Depends on / 依赖: dvd_setGcd_iff, dvd_setGcd_iff.mpr, setGcd_dvd_of_mem
-/
lemma setGcd_mono (h : s subseteq t) : setGcd t ∣ setGcd s :=
  dvd_setGcd_iff.mpr fun _m hm => setGcd_dvd_of_mem (h hm)

/--
lemma `dvdNotUnit_setGcd_insert` / 引理 `dvdNotUnit_setGcd_insert`

English:
lemma dvdNotUnit_setGcd_insert
  given: (h : ¬ setGcd s ∣ n)
  proof: dvdNotUnit_of_dvd_of_not_dvd (setGcd_mono <| Set.subset_insert ..)
fun dvd => h dvd_setGcd_iff.mp dvd _ (Set.mem_insert ..)

中文:
引理 dvdNotUnit_setGcd_insert
  条件: (h : ¬ setGcd s ∣ n)
  证明: dvdNotUnit_of_dvd_of_not_dvd (setGcd_mono <| Set.subset_insert ..)
fun dvd => h dvd_setGcd_iff.mp dvd _ (Set.mem_insert ..)

Depends on / 依赖: Set.mem_insert, Set.subset_insert, dvdNotUnit_of_dvd_of_not_dvd, dvd_setGcd_iff, dvd_setGcd_iff.mp, mem_insert, setGcd_mono, subset_insert
-/
lemma dvdNotUnit_setGcd_insert (h : ¬ setGcd s ∣ n) :
    DvdNotUnit (setGcd (insert n s)) (setGcd s) :=
  dvdNotUnit_of_dvd_of_not_dvd (setGcd_mono <| Set.subset_insert ..)
fun dvd => h dvd_setGcd_iff.mp dvd _ (Set.mem_insert ..)

/--
lemma `setGcd_insert_of_dvd` / 引理 `setGcd_insert_of_dvd`

English:
lemma setGcd_insert_of_dvd
  given: (h : setGcd s ∣ n)
  statement: setGcd (insert n s) = setGcd s
  proof: (setGcd_mono <| Set.subset_insert ..).antisymm dvd_setGcd_iff.mpr
    fun m => by rintro (rfl | hm); exacts [h, setGcd_dvd_of_mem hm]

中文:
引理 setGcd_insert_of_dvd
  条件: (h : setGcd s ∣ n)
  结论: setGcd (insert n s) = setGcd s
  证明: (setGcd_mono <| Set.subset_insert ..).antisymm dvd_setGcd_iff.mpr
    fun m => by rintro (rfl | hm); exacts [h, setGcd_dvd_of_mem hm]

Depends on / 依赖: Set.subset_insert, antisymm, dvd_setGcd_iff, dvd_setGcd_iff.mpr, exacts, setGcd_dvd_of_mem, setGcd_mono, subset_insert
-/
lemma setGcd_insert_of_dvd (h : setGcd s ∣ n) : setGcd (insert n s) = setGcd s :=
(setGcd_mono <| Set.subset_insert ..).antisymm dvd_setGcd_iff.mpr
    fun m => by rintro (rfl | hm); exacts [h, setGcd_dvd_of_mem hm]

/--
lemma `setGcd_eq_zero_iff` / 引理 `setGcd_eq_zero_iff`

English:
lemma setGcd_eq_zero_iff
  statement: setGcd s = 0 ↔ s subseteq {0}
  proof: by
  simp_rw [setGcd, Int.natAbs_eq_zero, ← eq_bot_iff_generator_eq_zero, Ideal.span_eq_bot,
    Set.forall_mem_image, Int.natCast_eq_zero, Set.subset_def, Set.mem_singleton_iff]

中文:
引理 setGcd_eq_zero_iff
  结论: setGcd s = 0 ↔ s subseteq {0}
  证明: by
  simp_rw [setGcd, Int.natAbs_eq_zero, ← eq_bot_iff_generator_eq_zero, Ideal.span_eq_bot,
    Set.forall_mem_image, Int.natCast_eq_zero, Set.subset_def, Set.mem_singleton_iff]

Depends on / 依赖: Ideal.span_eq_bot, Int.natAbs_eq_zero, Int.natCast_eq_zero, Set.forall_mem_image, Set.mem_singleton_iff, Set.subset_def, eq_bot_iff_generator_eq_zero, forall_mem_image, mem_singleton_iff, natAbs_eq_zero, natCast_eq_zero, setGcd, simp_rw, span_eq_bot, subset_def
-/
lemma setGcd_eq_zero_iff : setGcd s = 0 ↔ s subseteq {0} := by
  simp_rw [setGcd, Int.natAbs_eq_zero, ← eq_bot_iff_generator_eq_zero, Ideal.span_eq_bot,
    Set.forall_mem_image, Int.natCast_eq_zero, Set.subset_def, Set.mem_singleton_iff]

/--
lemma `exists_ne_zero_of_setGcd_ne_zero` / 引理 `exists_ne_zero_of_setGcd_ne_zero`

English:
lemma exists_ne_zero_of_setGcd_ne_zero
  given: (hs : setGcd s != 0)
  statement: exists n in s, n != 0
  proof: by
  contrapose! hs
  exact setGcd_eq_zero_iff.mpr hs

中文:
引理 存在_ne_zero_of_setGcd_ne_zero
  条件: (hs : setGcd s != 0)
  结论: 存在 n in s, n != 0
  证明: by
  contrapose! hs
  exact setGcd_eq_zero_iff.mpr hs

Depends on / 依赖: contrapose, setGcd_eq_zero_iff, setGcd_eq_zero_iff.mpr
-/
lemma exists_ne_zero_of_setGcd_ne_zero (hs : setGcd s != 0) : exists n in s, n != 0 := by
  contrapose! hs
  exact setGcd_eq_zero_iff.mpr hs

variable (s)

/--
lemma `span_singleton_setGcd` / 引理 `span_singleton_setGcd`

English:
lemma span_singleton_setGcd
  statement: Ideal.span {(setGcd s : Int)} = Ideal.span (((↑) : Nat -> Int) '' s)
  proof: by
  rw [setGcd]; rw [← Ideal.span_singleton_eq_span_singleton.mpr (Int.associated_natAbs _)]; rw [Ideal.span]; rw [span_singleton_generator]

中文:
引理 span_singleton_setGcd
  结论: 理想.span {(setGcd s : 整数)} = 理想.span (((↑) : 自然数 -> 整数) '' s)
  证明: by
  rw [setGcd]; rw [← Ideal.span_singleton_eq_span_singleton.mpr (Int.associated_natAbs _)]; rw [Ideal.span]; rw [span_singleton_generator]

Depends on / 依赖: Ideal.span, Ideal.span_singleton_eq_span_singleton.mpr, Int.associated_natAbs, associated_natAbs, setGcd, span_singleton_eq_span_singleton, span_singleton_generator
-/
lemma span_singleton_setGcd : Ideal.span {(setGcd s : Int)} = Ideal.span (((↑) : Nat -> Int) '' s) := by
  rw [setGcd]; rw [← Ideal.span_singleton_eq_span_singleton.mpr (Int.associated_natAbs _)]; rw [Ideal.span]; rw [span_singleton_generator]

/--
lemma `subset_span_setGcd` / 引理 `subset_span_setGcd`

English:
lemma subset_span_setGcd
  statement: s subseteq Ideal.span {setGcd s}
  proof: fun _x hx => Ideal.mem_span_singleton.mpr (setGcd_dvd_of_mem hx)

中文:
引理 subset_span_setGcd
  结论: s subseteq 理想.span {setGcd s}
  证明: fun _x hx => Ideal.mem_span_singleton.mpr (setGcd_dvd_of_mem hx)

Depends on / 依赖: Ideal.mem_span_singleton.mpr, mem_span_singleton, setGcd_dvd_of_mem
-/
lemma subset_span_setGcd : s subseteq Ideal.span {setGcd s} :=
  fun _x hx => Ideal.mem_span_singleton.mpr (setGcd_dvd_of_mem hx)

open Ideal in
/--
theorem `exists_mem_span_nat_finset_of_ge` / 定理 `exists_mem_span_nat_finset_of_ge`

English:
theorem exists_mem_span_nat_finset_of_ge
  proof: by
  by_cases h0 : setGcd s = 0
  · refine ⟨∅, 0, by simp, fun _ _ dvd => by cases zero_dvd_iff.mp (h0 ▸ dvd); exact zero_mem _⟩
  -- Write the gcd of `s` as a ℤ-linear combination of a finite subset `t`.
  have ⟨t, hts, a, eq⟩ := (Submodule.mem_span_image_iff_exists_fun _).mp
    (span_singleton_se

中文:
定理 存在_mem_span_nat_finset_of_ge
  证明: by
  by_cases h0 : setGcd s = 0
  · refine ⟨∅, 0, by simp, fun _ _ dvd => by cases zero_dvd_iff.mp (h0 ▸ dvd); exact zero_mem _⟩
  -- Write the gcd of `s` as a ℤ-linear combination of a finite subset `t`.
  have ⟨t, hts, a, eq⟩ := (Submodule.mem_span_image_iff_exists_fun _).mp
    (span_singleton_se

Depends on / 依赖: setGcd, zero_dvd_iff, zero_dvd_iff.mp, zero_mem
-/
theorem exists_mem_span_nat_finset_of_ge :
    exists (t : Finset Nat) (n : Nat), ↑t subseteq s ∧ forall m >= n, setGcd s ∣ m -> m in Ideal.span t := by
  by_cases h0 : setGcd s = 0
  · refine ⟨∅, 0, by simp, fun _ _ dvd => by cases zero_dvd_iff.mp (h0 ▸ dvd); exact zero_mem _⟩
  -- Write the gcd of `s` as a ℤ-linear combination of a finite subset `t`.
  have ⟨t, hts, a, eq⟩ := (Submodule.mem_span_image_iff_exists_fun _).mp
    (span_singleton_setGcd s ▸ mem_span_singleton_self _)
  -- Let `x` be an arbitrary nonzero element in `s`.
  have ⟨x, hxs, hx⟩ := exists_ne_zero_of_setGcd_ne_zero h0
  let n := (x / setGcd s) * ∑ i, (-a i).toNat * i
  refine ⟨insert x t, n, by simpa [Set.insert_subset_iff] using ⟨hxs, hts⟩, fun m ge dvd => ?_⟩
  -- For `m ≥ n`, write `m = q * x + (r + n)` with 0 ≤ r < x.
  obtain ⟨c, rfl⟩ := exists_add_of_le ge
  rw [← c.div_add_mod' x]
  set q := c / x
  set r := c % x
  rw [add_comm]; rw [add_assoc]
  refine add_mem (mul_mem_left _ q (subset_span (Finset.mem_insert_self ..)))
    (Submodule.span_mono (s := t) (Finset.subset_insert ..) ?_)
  -- It suffices to show `r + n` lies in the ℕ-span of `t`.
obtain ⟨rx, hrx⟩ : setGcd s ∣ r := (dvd_mod_iff (setGcd_dvd_of_mem hxs)).mpr
    (Nat.dvd_add_right <| dvd_mul_of_dvd_right (Finset.dvd_sum fun i _ =>
      dvd_mul_of_dvd_right (setGcd_dvd_of_mem (hts i.2)) _) _).mp dvd
  convert!
    (sum_mem fun i _ => mul_mem_left _ _ (subset_span i.2) :
      -- an explicit ℕ-linear combination of elements of `t` that is equal to `r + n`
       ∑ i : t, (if 0 <= a i then rx else x / setGcd s - rx) * (a i).natAbs * i in span t)
  simp_rw [← Int.natCast_inj, hrx, n, Finset.mul_sum, mul_comm _ rx, cast_add, cast_sum, cast_mul,
    ← eq, Finset.mul_sum, smul_eq_mul, ← mul_assoc, ← Finset.sum_add_distrib, ← add_mul]
  congr! 2 with i
  split_ifs with hai
  · rw [Int.toNat_eq_zero.mpr (by lia), cast_zero, mul_zero, add_zero,
      Int.natCast_natAbs, abs_eq_self.mpr hai]
  · rw [cast_sub, Int.natCast_natAbs, abs_eq_neg_self.mpr (by lia), sub_mul,
      ← Int.eq_natCast_toNat.mpr (by lia), mul_neg (rx : Int), sub_neg_eq_add, add_comm]
    rw [← Nat.mul_le_mul_left_iff (pos_of_ne_zero h0)]; rw [← hrx]; rw [Nat.mul_div_cancel' (setGcd_dvd_of_mem hxs)]
    exact (c.mod_lt (pos_of_ne_zero hx)).le

/--
theorem `exists_mem_closure_of_ge` / 定理 `exists_mem_closure_of_ge`

English:
theorem exists_mem_closure_of_ge
  statement: exists n, forall m >= n, setGcd s ∣ m -> m in AddSubmonoid.closure s
  proof: have ⟨_t, n, hts, hn⟩ := exists_mem_span_nat_finset_of_ge s
  ⟨n, fun m ge dvd => (Submodule.span_nat_eq_addSubmonoidClosure s).le
    (Submodule.span_mono hts (hn m ge dvd))⟩

中文:
定理 存在_mem_closure_of_ge
  结论: 存在 n, 对任意 m >= n, setGcd s ∣ m -> m in 加法子幺半群.closure s
  证明: have ⟨_t, n, hts, hn⟩ := exists_mem_span_nat_finset_of_ge s
  ⟨n, fun m ge dvd => (Submodule.span_nat_eq_addSubmonoidClosure s).le
    (Submodule.span_mono hts (hn m ge dvd))⟩

Depends on / 依赖: Submodule, Submodule.span_mono, Submodule.span_nat_eq_addSubmonoidClosure, exists_mem_span_nat_finset_of_ge, span_mono, span_nat_eq_addSubmonoidClosure
-/
theorem exists_mem_closure_of_ge : exists n, forall m >= n, setGcd s ∣ m -> m in AddSubmonoid.closure s :=
  have ⟨_t, n, hts, hn⟩ := exists_mem_span_nat_finset_of_ge s
  ⟨n, fun m ge dvd => (Submodule.span_nat_eq_addSubmonoidClosure s).le
    (Submodule.span_mono hts (hn m ge dvd))⟩

/--
theorem `finite_setOfPred_setGcd_dvd_and_mem_span` / 定理 `finite_setOfPred_setGcd_dvd_and_mem_span`

English:
theorem finite_setOfPred_setGcd_dvd_and_mem_span
  proof: have ⟨n, hn⟩ := exists_mem_closure_of_ge s
(Finset.range n).finite_toSet.subset fun m h => Finset.mem_range.mpr
lt_of_not_ge fun ge => h.2 (Submodule.span_nat_eq_addSubmonoidClosure s).ge (hn m ge h.1)

@[deprecated (since := "2026-07-09")]
alias finite_setOf_setGcd_dvd_and_mem_span := finite_setOfP

中文:
定理 finite_setOfPred_setGcd_dvd_and_mem_span
  证明: have ⟨n, hn⟩ := exists_mem_closure_of_ge s
(Finset.range n).finite_toSet.subset fun m h => Finset.mem_range.mpr
lt_of_not_ge fun ge => h.2 (Submodule.span_nat_eq_addSubmonoidClosure s).ge (hn m ge h.1)

@[deprecated (since := "2026-07-09")]
alias finite_setOf_setGcd_dvd_and_mem_span := finite_setOfP

Depends on / 依赖: Finset, Finset.mem_range.mpr, Finset.range, Submodule, Submodule.span_nat_eq_addSubmonoidClosure, exists_mem_closure_of_ge, finite_toSet, finite_toSet.subset, lt_of_not_ge, mem_range, span_nat_eq_addSubmonoidClosure, subset
-/
theorem finite_setOfPred_setGcd_dvd_and_mem_span :
    {n | setGcd s ∣ n ∧ n ∉ Ideal.span s}.Finite :=
  have ⟨n, hn⟩ := exists_mem_closure_of_ge s
(Finset.range n).finite_toSet.subset fun m h => Finset.mem_range.mpr
lt_of_not_ge fun ge => h.2 (Submodule.span_nat_eq_addSubmonoidClosure s).ge (hn m ge h.1)

@[deprecated (since := "2026-07-09")]
alias finite_setOf_setGcd_dvd_and_mem_span := finite_setOfPred_setGcd_dvd_and_mem_span

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNoetherian Nat Nat
  body: by
    have ⟨t, n, hts, hn⟩ := exists_mem_span_nat_finset_of_ge s
    classical
    refine ⟨t union {m in Finset.range n | m in s}, (Submodule.span_le.mpr ?_).antisymm fun m hm => ?_⟩
    · simpa using ⟨hts, fun _ => And.right⟩
    obtain le | gt := le_or_gt n m
    · exact Submodule.span_mono (by s

中文:
实例 :
  签名: 是Noether 自然数 自然数
  定义体: by
    have ⟨t, n, hts, hn⟩ := exists_mem_span_nat_finset_of_ge s
    classical
    refine ⟨t union {m in Finset.range n | m in s}, (Submodule.span_le.mpr ?_).antisymm fun m hm => ?_⟩
    · simpa using ⟨hts, fun _ => And.right⟩
    obtain le | gt := le_or_gt n m
    · exact Submodule.span_mono (by s

Depends on / 依赖: And.right, Finset, Finset.range, Submodule, Submodule.span_le.mpr, Submodule.span_mono, Submodule.subset_span, antisymm, classical, exists_mem_span_nat_finset_of_ge, le_or_gt, setGcd_dvd_of_mem, span_le, span_mono, subset_span
-/
instance : IsNoetherian Nat Nat where
  noetherian s := by
    have ⟨t, n, hts, hn⟩ := exists_mem_span_nat_finset_of_ge s
    classical
    refine ⟨t union {m in Finset.range n | m in s}, (Submodule.span_le.mpr ?_).antisymm fun m hm => ?_⟩
    · simpa using ⟨hts, fun _ => And.right⟩
    obtain le | gt := le_or_gt n m
    · exact Submodule.span_mono (by simp) (hn m le (setGcd_dvd_of_mem hm))
    · exact Submodule.subset_span (by simpa using .inr ⟨gt, hm⟩)

/--
theorem `addSubmonoid_fg` / 定理 `addSubmonoid_fg`

English:
theorem addSubmonoid_fg
  given: (s : AddSubmonoid Nat)
  statement: s.FG
  proof: by
  rw [← s.toNatSubmodule_toAddSubmonoid]; rw [← Submodule.fg_iff_addSubmonoid_fg]
  apply IsNoetherian.noetherian

中文:
定理 addSubmonoid_fg
  条件: (s : 加法子幺半群 自然数)
  结论: s.FG
  证明: by
  rw [← s.toNatSubmodule_toAddSubmonoid]; rw [← Submodule.fg_iff_addSubmonoid_fg]
  apply IsNoetherian.noetherian

Depends on / 依赖: IsNoetherian, IsNoetherian.noetherian, Submodule, Submodule.fg_iff_addSubmonoid_fg, fg_iff_addSubmonoid_fg, noetherian, s.toNatSubmodule_toAddSubmonoid, toNatSubmodule_toAddSubmonoid
-/
theorem addSubmonoid_fg (s : AddSubmonoid Nat) : s.FG := by
  rw [← s.toNatSubmodule_toAddSubmonoid]; rw [← Submodule.fg_iff_addSubmonoid_fg]
  apply IsNoetherian.noetherian

end Nat

/--
theorem `exists_frobeniusNumber_iff` / 定理 `exists_frobeniusNumber_iff`

English:
theorem exists_frobeniusNumber_iff
  given: {s : Set Nat}
  proof: fun ⟨n, hn⟩ => by
    rw [frobeniusNumber_iff] at hn
exact ⟨dvd_one.mp Nat.dvd_add_iff_right (setGcd_dvd_of_mem_closure (hn.2 (n + 1)
      (by lia))) (n := 1) |>.mpr (setGcd_dvd_of_mem_closure (hn.2 (n + 2) (by lia))),
fun h => hn.1 AddSubmonoid.closure_mono (Set.singleton_subset_iff.mpr h)
       

中文:
定理 存在_frobeniusNumber_iff
  条件: {s : 集合 自然数}
  证明: fun ⟨n, hn⟩ => by
    rw [frobeniusNumber_iff] at hn
exact ⟨dvd_one.mp Nat.dvd_add_iff_right (setGcd_dvd_of_mem_closure (hn.2 (n + 1)
      (by lia))) (n := 1) |>.mpr (setGcd_dvd_of_mem_closure (hn.2 (n + 2) (by lia))),
fun h => hn.1 AddSubmonoid.closure_mono (Set.singleton_subset_iff.mpr h)
       

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure, AddSubmonoid.closure_mono, Nat.dvd_add_iff_right, Set.singleton_subset_iff.mpr, addSubmonoidClosure_one, addSubmonoidClosure_one.ge, classical, closure, closure_mono, dvd_add_iff_right, dvd_one, dvd_one.mp, exists_mem_closure_of_ge, findGreatest, frobeniusNum, frobeniusNumber_iff, one_mem_closure_iff, one_mem_closure_iff.mp, setGcd_dvd_of_mem_closure
-/
theorem exists_frobeniusNumber_iff {s : Set Nat} :
    (exists n, FrobeniusNumber n s) ↔ setGcd s = 1 ∧ 1 ∉ s where
  mp := fun ⟨n, hn⟩ => by
    rw [frobeniusNumber_iff] at hn
exact ⟨dvd_one.mp Nat.dvd_add_iff_right (setGcd_dvd_of_mem_closure (hn.2 (n + 1)
      (by lia))) (n := 1) |>.mpr (setGcd_dvd_of_mem_closure (hn.2 (n + 2) (by lia))),
fun h => hn.1 AddSubmonoid.closure_mono (Set.singleton_subset_iff.mpr h)
        (addSubmonoidClosure_one.ge ⟨⟩)⟩
  mpr h := by
    have ⟨n, hn⟩ := exists_mem_closure_of_ge s
    let P n := n ∉ AddSubmonoid.closure s
    have : P 1 := h.2 ∘ one_mem_closure_iff.mp
    classical
    refine ⟨findGreatest P n, frobeniusNumber_iff.mpr ⟨findGreatest_spec (P := P) (m := 1)
      (le_of_not_gt fun lt => this (hn _ lt.le h.1.dvd)) this, fun k gt => ?_⟩⟩
    obtain le | le := le_total k n
    · exact of_not_not (findGreatest_is_greatest gt le)
    · exact hn k le (h.1.dvd.trans <| one_dvd k)
