/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
module

public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Basic lemmas on prime factorizations
-/

public section

open Finset List Finsupp

namespace Nat
variable {a b m n p : Nat}

/-! ### Basic facts about factorization -/



/--
theorem `factorization_eq_zero_of_lt` / 定理 `factorization_eq_zero_of_lt`

English:
theorem factorization_eq_zero_of_lt
  given: {n p : Nat} (h : n < p)
  statement: n.factorization p = 0
  proof: Finsupp.notMem_support_iff.mp (mt le_of_mem_primeFactors (not_le_of_gt h))

中文:
定理 factorization_eq_zero_of_lt
  条件: {n p : 自然数} (h : n < p)
  结论: n.factorization p = 0
  证明: Finsupp.notMem_support_iff.mp (mt le_of_mem_primeFactors (not_le_of_gt h))

Depends on / 依赖: Finsupp, Finsupp.notMem_support_iff.mp, le_of_mem_primeFactors, notMem_support_iff, not_le_of_gt
-/
theorem factorization_eq_zero_of_lt {n p : Nat} (h : n < p) : n.factorization p = 0 :=
  Finsupp.notMem_support_iff.mp (mt le_of_mem_primeFactors (not_le_of_gt h))

/--
theorem `dvd_of_factorization_pos` / 定理 `dvd_of_factorization_pos`

English:
theorem dvd_of_factorization_pos
  given: {n p : Nat} (hn : n.factorization p != 0)
  statement: p ∣ n
  proof: dvd_of_mem_primeFactorsList mem_primeFactors_iff_mem_primeFactorsList.1 mem_support_iff.2 hn

中文:
定理 dvd_of_factorization_pos
  条件: {n p : 自然数} (hn : n.factorization p != 0)
  结论: p ∣ n
  证明: dvd_of_mem_primeFactorsList mem_primeFactors_iff_mem_primeFactorsList.1 mem_support_iff.2 hn

Depends on / 依赖: dvd_of_mem_primeFactorsList, mem_primeFactors_iff_mem_primeFactorsList, mem_support_iff
-/
theorem dvd_of_factorization_pos {n p : Nat} (hn : n.factorization p != 0) : p ∣ n :=
dvd_of_mem_primeFactorsList mem_primeFactors_iff_mem_primeFactorsList.1 mem_support_iff.2 hn

/--
theorem `factorization_eq_zero_iff_remainder` / 定理 `factorization_eq_zero_iff_remainder`

English:
theorem factorization_eq_zero_iff_remainder
  given: {p r : Nat} (i : Nat) (pp : p.Prime) (hr0 : r != 0)
  proof: by
  refine ⟨factorization_eq_zero_of_remainder i, fun h => ?_⟩
  rw [factorization_eq_zero_iff] at h
  contrapose! h
  refine ⟨pp, ?_, ?_⟩
  · rwa [← Nat.dvd_add_iff_right (dvd_mul_right p i)]
  · contrapose hr0
    exact (add_eq_zero.1 hr0).2

中文:
定理 factorization_eq_zero_iff_remainder
  条件: {p r : 自然数} (i : 自然数) (pp : p.素) (hr0 : r != 0)
  证明: by
  refine ⟨factorization_eq_zero_of_remainder i, fun h => ?_⟩
  rw [factorization_eq_zero_iff] at h
  contrapose! h
  refine ⟨pp, ?_, ?_⟩
  · rwa [← Nat.dvd_add_iff_right (dvd_mul_right p i)]
  · contrapose hr0
    exact (add_eq_zero.1 hr0).2

Depends on / 依赖: Nat.dvd_add_iff_right, add_eq_zero, contrapose, dvd_add_iff_right, dvd_mul_right, factorization_eq_zero_iff, factorization_eq_zero_of_remainder
-/
theorem factorization_eq_zero_iff_remainder {p r : Nat} (i : Nat) (pp : p.Prime) (hr0 : r != 0) :
    ¬p ∣ r ↔ (p * i + r).factorization p = 0 := by
  refine ⟨factorization_eq_zero_of_remainder i, fun h => ?_⟩
  rw [factorization_eq_zero_iff] at h
  contrapose! h
  refine ⟨pp, ?_, ?_⟩
  · rwa [← Nat.dvd_add_iff_right (dvd_mul_right p i)]
  · contrapose hr0
    exact (add_eq_zero.1 hr0).2

/--
theorem `factorization_eq_zero_iff'` / 定理 `factorization_eq_zero_iff'`

English:
theorem factorization_eq_zero_iff'
  given: (n : Nat)
  statement: n.factorization = 0 ↔ n = 0 ∨ n = 1
  proof: by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp [Multiset.coe_eq_zero]

中文:
定理 factorization_eq_zero_iff'
  条件: (n : 自然数)
  结论: n.factorization = 0 ↔ n = 0 ∨ n = 1
  证明: by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp [Multiset.coe_eq_zero]

Depends on / 依赖: Multiset, Multiset.coe_eq_zero, coe_eq_zero, factorization_eq_primeFactorsList_multiset
-/
theorem factorization_eq_zero_iff' (n : Nat) : n.factorization = 0 ↔ n = 0 ∨ n = 1 := by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp [Multiset.coe_eq_zero]

/-! ## Lemmas about factorizations of products and powers -/

/--
theorem `factorization_prod_apply` / 定理 `factorization_prod_apply`

English:
theorem factorization_prod_apply
  statement: {α : Type*} {p : Nat}
  proof: by
  rw [factorization_prod hS]; rw [finsetSum_apply]

中文:
定理 factorization_prod_apply
  结论: {α : 类型} {p : 自然数}
  证明: by
  rw [factorization_prod hS]; rw [finsetSum_apply]

Depends on / 依赖: factorization_prod, finsetSum_apply
-/
theorem factorization_prod_apply {α : Type*} {p : Nat}
    {S : Finset α} {g : α -> Nat} (hS : forall x in S, g x != 0) :
    (S.prod g).factorization p = S.sum fun x => (g x).factorization p := by
  rw [factorization_prod hS]; rw [finsetSum_apply]

/--
lemma `prod_factorization_eq_prod_primeFactors` / 引理 `prod_factorization_eq_prod_primeFactors`

English:
lemma prod_factorization_eq_prod_primeFactors
  given: {β : Type*} [CommMonoid β] (f : Nat -> Nat -> β)
  proof: rfl

中文:
引理 prod_factorization_eq_prod_primeFactors
  条件: {β : 类型} [交换幺半群 β] (f : 自然数 -> 自然数 -> β)
  证明: rfl
-/
lemma prod_factorization_eq_prod_primeFactors {β : Type*} [CommMonoid β] (f : Nat -> Nat -> β) :
    n.factorization.prod f = ∏ p in n.primeFactors, f p (n.factorization p) := rfl

/--
lemma `prod_primeFactors_prod_factorization` / 引理 `prod_primeFactors_prod_factorization`

English:
lemma prod_primeFactors_prod_factorization
  given: {β : Type*} [CommMonoid β] (f : Nat -> β)
  proof: rfl

中文:
引理 prod_primeFactors_prod_factorization
  条件: {β : 类型} [交换幺半群 β] (f : 自然数 -> β)
  证明: rfl
-/
lemma prod_primeFactors_prod_factorization {β : Type*} [CommMonoid β] (f : Nat -> β) :
    ∏ p in n.primeFactors, f p = n.factorization.prod (fun p _ => f p) := rfl

/-! ## Lemmas about factorizations of primes and prime powers -/

/--
theorem `Prime.factorization_self` / 定理 `Prime.factorization_self`

English:
theorem Prime.factorization_self
  given: {p : Nat} (hp : Prime p)
  statement: p.factorization p = 1
  proof: by simp [hp]

中文:
定理 素.factorization_self
  条件: {p : 自然数} (hp : 素 p)
  结论: p.factorization p = 1
  证明: by simp [hp]
-/
theorem Prime.factorization_self {p : Nat} (hp : Prime p) : p.factorization p = 1 := by simp [hp]

/--
theorem `factorization_pow_self` / 定理 `factorization_pow_self`

English:
theorem factorization_pow_self
  given: {p n : Nat} (hp : p.Prime)
  statement: (p ^ n).factorization p = n
  proof: by
  simp [factorization_pow, Prime.factorization_self hp]

中文:
定理 factorization_pow_self
  条件: {p n : 自然数} (hp : p.素)
  结论: (p ^ n).factorization p = n
  证明: by
  simp [factorization_pow, Prime.factorization_self hp]

Depends on / 依赖: Prime.factorization_self, factorization_pow, factorization_self
-/
theorem factorization_pow_self {p n : Nat} (hp : p.Prime) : (p ^ n).factorization p = n := by
  simp [factorization_pow, Prime.factorization_self hp]

/--
theorem `eq_pow_of_factorization_eq_single` / 定理 `eq_pow_of_factorization_eq_single`

English:
theorem eq_pow_of_factorization_eq_single
  statement: {n p k : Nat} (hn : n != 0)
  proof: by
  rw [← Nat.prod_factorization_pow_eq_self hn]; rw [h]
  simp

中文:
定理 eq_pow_of_factorization_eq_single
  结论: {n p k : 自然数} (hn : n != 0)
  证明: by
  rw [← Nat.prod_factorization_pow_eq_self hn]; rw [h]
  simp

Depends on / 依赖: Nat.prod_factorization_pow_eq_self, prod_factorization_pow_eq_self
-/
theorem eq_pow_of_factorization_eq_single {n p k : Nat} (hn : n != 0)
    (h : n.factorization = Finsupp.single p k) : n = p ^ k := by
  rw [← Nat.prod_factorization_pow_eq_self hn]; rw [h]
  simp

/--
theorem `Prime.eq_of_factorization_pos` / 定理 `Prime.eq_of_factorization_pos`

English:
theorem Prime.eq_of_factorization_pos
  given: {p q : Nat} (hp : Prime p) (h : p.factorization q != 0)
  proof: by simpa [hp.factorization, single_apply] using h

中文:
定理 素.eq_of_factorization_pos
  条件: {p q : 自然数} (hp : 素 p) (h : p.factorization q != 0)
  证明: by simpa [hp.factorization, single_apply] using h

Depends on / 依赖: factorization, hp.factorization, single_apply
-/
theorem Prime.eq_of_factorization_pos {p q : Nat} (hp : Prime p) (h : p.factorization q != 0) :
    p = q := by simpa [hp.factorization, single_apply] using h

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/


@[deprecated factorizationEquiv_symm_apply_coe (since := "2026-03-18")]
/--
theorem `factorizationEquiv_inv_apply` / 定理 `factorizationEquiv_inv_apply`

English:
theorem factorizationEquiv_inv_apply
  given: {f : Nat ->₀ Nat} (hf : forall p in f.support, Prime p)
  proof: factorizationEquiv_symm_apply_coe ⟨f, hf⟩

中文:
定理 factorizationEquiv_inv_apply
  条件: {f : 自然数 ->₀ 自然数} (hf : 对任意 p in f.support, 素 p)
  证明: factorizationEquiv_symm_apply_coe ⟨f, hf⟩

Depends on / 依赖: factorizationEquiv_symm_apply_coe
-/
theorem factorizationEquiv_inv_apply {f : Nat ->₀ Nat} (hf : forall p in f.support, Prime p) :
    (factorizationEquiv.symm ⟨f, hf⟩).1 = f.prod (· ^ ·) :=
  factorizationEquiv_symm_apply_coe ⟨f, hf⟩

/--
theorem `ordProj_of_not_prime` / 定理 `ordProj_of_not_prime`

English:
theorem ordProj_of_not_prime
  given: (n p : Nat) (hp : ¬p.Prime)
  statement: ordProj[p] n = 1
  proof: by
  simp [hp]

中文:
定理 ordProj_of_not_prime
  条件: (n p : 自然数) (hp : ¬p.素)
  结论: ordProj[p] n = 1
  证明: by
  simp [hp]
-/
theorem ordProj_of_not_prime (n p : Nat) (hp : ¬p.Prime) : ordProj[p] n = 1 := by
  simp [hp]

/--
theorem `ordCompl_of_not_prime` / 定理 `ordCompl_of_not_prime`

English:
theorem ordCompl_of_not_prime
  given: (n p : Nat) (hp : ¬p.Prime)
  statement: ordCompl[p] n = n
  proof: by
  simp [hp]

中文:
定理 ordCompl_of_not_prime
  条件: (n p : 自然数) (hp : ¬p.素)
  结论: ordCompl[p] n = n
  证明: by
  simp [hp]
-/
theorem ordCompl_of_not_prime (n p : Nat) (hp : ¬p.Prime) : ordCompl[p] n = n := by
  simp [hp]

/--
theorem `ordCompl_dvd` / 定理 `ordCompl_dvd`

English:
theorem ordCompl_dvd
  given: (n p : Nat)
  statement: ordCompl[p] n ∣ n
  proof: div_dvd_of_dvd (ordProj_dvd n p)

中文:
定理 ordCompl_dvd
  条件: (n p : 自然数)
  结论: ordCompl[p] n ∣ n
  证明: div_dvd_of_dvd (ordProj_dvd n p)

Depends on / 依赖: div_dvd_of_dvd, ordProj_dvd
-/
theorem ordCompl_dvd (n p : Nat) : ordCompl[p] n ∣ n :=
  div_dvd_of_dvd (ordProj_dvd n p)

/--
theorem `ordProj_pos` / 定理 `ordProj_pos`

English:
theorem ordProj_pos
  given: (n p : Nat)
  statement: 0 < ordProj[p] n
  proof: by
  if pp : p.Prime then simp [Nat.pow_pos pp.pos] else simp [pp]

中文:
定理 ordProj_pos
  条件: (n p : 自然数)
  结论: 0 < ordProj[p] n
  证明: by
  if pp : p.Prime then simp [Nat.pow_pos pp.pos] else simp [pp]

Depends on / 依赖: Nat.pow_pos, p.Prime, pow_pos, pp.pos
-/
theorem ordProj_pos (n p : Nat) : 0 < ordProj[p] n := by
  if pp : p.Prime then simp [Nat.pow_pos pp.pos] else simp [pp]

/--
theorem `ordProj_le` / 定理 `ordProj_le`

English:
theorem ordProj_le
  given: {n : Nat} (p : Nat) (hn : n != 0)
  statement: ordProj[p] n <= n
  proof: le_of_dvd hn.bot_lt (Nat.ordProj_dvd n p)

中文:
定理 ordProj_le
  条件: {n : 自然数} (p : 自然数) (hn : n != 0)
  结论: ordProj[p] n <= n
  证明: le_of_dvd hn.bot_lt (Nat.ordProj_dvd n p)

Depends on / 依赖: Nat.ordProj_dvd, bot_lt, hn.bot_lt, le_of_dvd, ordProj_dvd
-/
theorem ordProj_le {n : Nat} (p : Nat) (hn : n != 0) : ordProj[p] n <= n :=
  le_of_dvd hn.bot_lt (Nat.ordProj_dvd n p)

/--
theorem `ordCompl_pos` / 定理 `ordCompl_pos`

English:
theorem ordCompl_pos
  given: {n : Nat} (p : Nat) (hn : n != 0)
  statement: 0 < ordCompl[p] n
  proof: by
  if pp : p.Prime then
    exact Nat.div_pos (ordProj_le p hn) (ordProj_pos n p)
  else
    simpa [Nat.factorization_eq_zero_of_not_prime n pp] using hn.bot_lt

中文:
定理 ordCompl_pos
  条件: {n : 自然数} (p : 自然数) (hn : n != 0)
  结论: 0 < ordCompl[p] n
  证明: by
  if pp : p.Prime then
    exact Nat.div_pos (ordProj_le p hn) (ordProj_pos n p)
  else
    simpa [Nat.factorization_eq_zero_of_not_prime n pp] using hn.bot_lt

Depends on / 依赖: Nat.div_pos, Nat.factorization_eq_zero_of_not_prime, bot_lt, div_pos, factorization_eq_zero_of_not_prime, hn.bot_lt, ordProj_le, ordProj_pos, p.Prime
-/
theorem ordCompl_pos {n : Nat} (p : Nat) (hn : n != 0) : 0 < ordCompl[p] n := by
  if pp : p.Prime then
    exact Nat.div_pos (ordProj_le p hn) (ordProj_pos n p)
  else
    simpa [Nat.factorization_eq_zero_of_not_prime n pp] using hn.bot_lt

/--
theorem `ordCompl_le` / 定理 `ordCompl_le`

English:
theorem ordCompl_le
  given: (n p : Nat)
  statement: ordCompl[p] n <= n
  proof: Nat.div_le_self _ _

中文:
定理 ordCompl_le
  条件: (n p : 自然数)
  结论: ordCompl[p] n <= n
  证明: Nat.div_le_self _ _

Depends on / 依赖: Nat.div_le_self, div_le_self
-/
theorem ordCompl_le (n p : Nat) : ordCompl[p] n <= n :=
  Nat.div_le_self _ _

/--
theorem `ordProj_mul_ordCompl_eq_self` / 定理 `ordProj_mul_ordCompl_eq_self`

English:
theorem ordProj_mul_ordCompl_eq_self
  given: (n p : Nat)
  statement: ordProj[p] n * ordCompl[p] n = n
  proof: Nat.mul_div_cancel' (ordProj_dvd n p)

中文:
定理 ordProj_mul_ordCompl_eq_self
  条件: (n p : 自然数)
  结论: ordProj[p] n * ordCompl[p] n = n
  证明: Nat.mul_div_cancel' (ordProj_dvd n p)

Depends on / 依赖: Nat.mul_div_cancel, mul_div_cancel, ordProj_dvd
-/
theorem ordProj_mul_ordCompl_eq_self (n p : Nat) : ordProj[p] n * ordCompl[p] n = n :=
  Nat.mul_div_cancel' (ordProj_dvd n p)

/--
theorem `ordProj_mul` / 定理 `ordProj_mul`

English:
theorem ordProj_mul
  given: {a b : Nat} (p : Nat) (ha : a != 0) (hb : b != 0)
  proof: by
  simp [factorization_mul ha hb, pow_add]

中文:
定理 ordProj_mul
  条件: {a b : 自然数} (p : 自然数) (ha : a != 0) (hb : b != 0)
  证明: by
  simp [factorization_mul ha hb, pow_add]

Depends on / 依赖: factorization_mul, pow_add
-/
theorem ordProj_mul {a b : Nat} (p : Nat) (ha : a != 0) (hb : b != 0) :
    ordProj[p] (a * b) = ordProj[p] a * ordProj[p] b := by
  simp [factorization_mul ha hb, pow_add]

/--
theorem `ordCompl_mul` / 定理 `ordCompl_mul`

English:
theorem ordCompl_mul
  given: (a b p : Nat)
  statement: ordCompl[p] (a * b) = ordCompl[p] a * ordCompl[p] b
  proof: by
  if ha : a = 0 then simp [ha] else
  if hb : b = 0 then simp [hb] else
  simp only [ordProj_mul p ha hb]
  rw [div_mul_div_comm (ordProj_dvd a p) (ordProj_dvd b p)]

中文:
定理 ordCompl_mul
  条件: (a b p : 自然数)
  结论: ordCompl[p] (a * b) = ordCompl[p] a * ordCompl[p] b
  证明: by
  if ha : a = 0 then simp [ha] else
  if hb : b = 0 then simp [hb] else
  simp only [ordProj_mul p ha hb]
  rw [div_mul_div_comm (ordProj_dvd a p) (ordProj_dvd b p)]

Depends on / 依赖: div_mul_div_comm, ordProj_dvd, ordProj_mul
-/
theorem ordCompl_mul (a b p : Nat) : ordCompl[p] (a * b) = ordCompl[p] a * ordCompl[p] b := by
  if ha : a = 0 then simp [ha] else
  if hb : b = 0 then simp [hb] else
  simp only [ordProj_mul p ha hb]
  rw [div_mul_div_comm (ordProj_dvd a p) (ordProj_dvd b p)]

/-! ### Factorization and divisibility -/

/--
theorem `factorization_lt` / 定理 `factorization_lt`

English:
theorem factorization_lt
  given: {n : Nat} (p : Nat) (hn : n != 0)
  statement: n.factorization p < n
  proof: by
  by_cases pp : p.Prime
· exact (Nat.pow_lt_pow_iff_right pp.one_lt).1 (ordProj_le p hn).trans_lt
      Nat.lt_pow_self pp.one_lt
  · simpa only [factorization_eq_zero_of_not_prime n pp] using! hn.bot_lt

中文:
定理 factorization_lt
  条件: {n : 自然数} (p : 自然数) (hn : n != 0)
  结论: n.factorization p < n
  证明: by
  by_cases pp : p.Prime
· exact (Nat.pow_lt_pow_iff_right pp.one_lt).1 (ordProj_le p hn).trans_lt
      Nat.lt_pow_self pp.one_lt
  · simpa only [factorization_eq_zero_of_not_prime n pp] using! hn.bot_lt

Depends on / 依赖: Nat.lt_pow_self, Nat.pow_lt_pow_iff_right, bot_lt, factorization_eq_zero_of_not_prime, hn.bot_lt, lt_pow_self, one_lt, ordProj_le, p.Prime, pow_lt_pow_iff_right, pp.one_lt, trans_lt
-/
theorem factorization_lt {n : Nat} (p : Nat) (hn : n != 0) : n.factorization p < n := by
  by_cases pp : p.Prime
· exact (Nat.pow_lt_pow_iff_right pp.one_lt).1 (ordProj_le p hn).trans_lt
      Nat.lt_pow_self pp.one_lt
  · simpa only [factorization_eq_zero_of_not_prime n pp] using! hn.bot_lt

/--
theorem `factorization_le_of_le_pow` / 定理 `factorization_le_of_le_pow`

English:
theorem factorization_le_of_le_pow
  given: {n p b : Nat} (hb : n <= p ^ b)
  statement: n.factorization p <= b
  proof: by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then
    exact (Nat.pow_le_pow_iff_right pp.one_lt).1 ((ordProj_le p hn).trans hb)
  else
    simp [factorization_eq_zero_of_not_prime n pp]

中文:
定理 factorization_le_of_le_pow
  条件: {n p b : 自然数} (hb : n <= p ^ b)
  结论: n.factorization p <= b
  证明: by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then
    exact (Nat.pow_le_pow_iff_right pp.one_lt).1 ((ordProj_le p hn).trans hb)
  else
    simp [factorization_eq_zero_of_not_prime n pp]

Depends on / 依赖: Nat.pow_le_pow_iff_right, factorization_eq_zero_of_not_prime, one_lt, ordProj_le, p.Prime, pow_le_pow_iff_right, pp.one_lt
-/
theorem factorization_le_of_le_pow {n p b : Nat} (hb : n <= p ^ b) : n.factorization p <= b := by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then
    exact (Nat.pow_le_pow_iff_right pp.one_lt).1 ((ordProj_le p hn).trans hb)
  else
    simp [factorization_eq_zero_of_not_prime n pp]

/--
theorem `factorization_prime_le_iff_dvd` / 定理 `factorization_prime_le_iff_dvd`

English:
theorem factorization_prime_le_iff_dvd
  given: {d n : Nat} (hd : d != 0) (hn : n != 0)
  proof: by
  rw [← factorization_le_iff_dvd hd hn]
  refine ⟨fun h p => (em p.Prime).elim (h p) fun hp => ?_, fun h p _ => h p⟩
  simp_rw [factorization_eq_zero_of_not_prime _ hp]
  rfl

中文:
定理 factorization_prime_le_iff_dvd
  条件: {d n : 自然数} (hd : d != 0) (hn : n != 0)
  证明: by
  rw [← factorization_le_iff_dvd hd hn]
  refine ⟨fun h p => (em p.Prime).elim (h p) fun hp => ?_, fun h p _ => h p⟩
  simp_rw [factorization_eq_zero_of_not_prime _ hp]
  rfl

Depends on / 依赖: factorization_eq_zero_of_not_prime, factorization_le_iff_dvd, p.Prime, simp_rw
-/
theorem factorization_prime_le_iff_dvd {d n : Nat} (hd : d != 0) (hn : n != 0) :
    (forall p : Nat, p.Prime -> d.factorization p <= n.factorization p) ↔ d ∣ n := by
  rw [← factorization_le_iff_dvd hd hn]
  refine ⟨fun h p => (em p.Prime).elim (h p) fun hp => ?_, fun h p _ => h p⟩
  simp_rw [factorization_eq_zero_of_not_prime _ hp]
  rfl

/--
theorem `factorization_le_factorization_mul_left` / 定理 `factorization_le_factorization_mul_left`

English:
theorem factorization_le_factorization_mul_left
  given: {a b : Nat} (hb : b != 0)
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  rw [factorization_le_iff_dvd ha <| mul_ne_zero ha hb]
  exact Dvd.intro b rfl

中文:
定理 factorization_le_factorization_mul_left
  条件: {a b : 自然数} (hb : b != 0)
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  rw [factorization_le_iff_dvd ha <| mul_ne_zero ha hb]
  exact Dvd.intro b rfl

Depends on / 依赖: Dvd.intro, eq_or_ne, factorization_le_iff_dvd, mul_ne_zero
-/
theorem factorization_le_factorization_mul_left {a b : Nat} (hb : b != 0) :
    a.factorization <= (a * b).factorization := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  rw [factorization_le_iff_dvd ha <| mul_ne_zero ha hb]
  exact Dvd.intro b rfl

/--
theorem `factorization_le_factorization_mul_right` / 定理 `factorization_le_factorization_mul_right`

English:
theorem factorization_le_factorization_mul_right
  given: {a b : Nat} (ha : a != 0)
  proof: by
  rw [mul_comm]
  apply factorization_le_factorization_mul_left ha

中文:
定理 factorization_le_factorization_mul_right
  条件: {a b : 自然数} (ha : a != 0)
  证明: by
  rw [mul_comm]
  apply factorization_le_factorization_mul_left ha

Depends on / 依赖: factorization_le_factorization_mul_left, mul_comm
-/
theorem factorization_le_factorization_mul_right {a b : Nat} (ha : a != 0) :
    b.factorization <= (a * b).factorization := by
  rw [mul_comm]
  apply factorization_le_factorization_mul_left ha

/--
theorem `Prime.pow_dvd_iff_le_factorization` / 定理 `Prime.pow_dvd_iff_le_factorization`

English:
theorem Prime.pow_dvd_iff_le_factorization
  given: {p k n : Nat} (pp : Prime p) (hn : n != 0)
  proof: by
  rw [← factorization_le_iff_dvd (Nat.pow_pos pp.pos).ne' hn]; rw [pp.factorization_pow]; rw [single_le_iff]

中文:
定理 素.pow_dvd_iff_le_factorization
  条件: {p k n : 自然数} (pp : 素 p) (hn : n != 0)
  证明: by
  rw [← factorization_le_iff_dvd (Nat.pow_pos pp.pos).ne' hn]; rw [pp.factorization_pow]; rw [single_le_iff]

Depends on / 依赖: Nat.pow_pos, factorization_le_iff_dvd, factorization_pow, pow_pos, pp.factorization_pow, pp.pos, single_le_iff
-/
theorem Prime.pow_dvd_iff_le_factorization {p k n : Nat} (pp : Prime p) (hn : n != 0) :
    p ^ k ∣ n ↔ k <= n.factorization p := by
  rw [← factorization_le_iff_dvd (Nat.pow_pos pp.pos).ne' hn]; rw [pp.factorization_pow]; rw [single_le_iff]

/--
theorem `Prime.pow_dvd_iff_dvd_ordProj` / 定理 `Prime.pow_dvd_iff_dvd_ordProj`

English:
theorem Prime.pow_dvd_iff_dvd_ordProj
  given: {p k n : Nat} (pp : Prime p) (hn : n != 0)
  proof: by
  rw [pow_dvd_pow_iff_le_right pp.one_lt]; rw [pp.pow_dvd_iff_le_factorization hn]

中文:
定理 素.pow_dvd_iff_dvd_ordProj
  条件: {p k n : 自然数} (pp : 素 p) (hn : n != 0)
  证明: by
  rw [pow_dvd_pow_iff_le_right pp.one_lt]; rw [pp.pow_dvd_iff_le_factorization hn]

Depends on / 依赖: one_lt, pow_dvd_iff_le_factorization, pow_dvd_pow_iff_le_right, pp.one_lt, pp.pow_dvd_iff_le_factorization
-/
theorem Prime.pow_dvd_iff_dvd_ordProj {p k n : Nat} (pp : Prime p) (hn : n != 0) :
    p ^ k ∣ n ↔ p ^ k ∣ ordProj[p] n := by
  rw [pow_dvd_pow_iff_le_right pp.one_lt]; rw [pp.pow_dvd_iff_le_factorization hn]

/--
theorem `Prime.dvd_iff_one_le_factorization` / 定理 `Prime.dvd_iff_one_le_factorization`

English:
theorem Prime.dvd_iff_one_le_factorization
  given: {p n : Nat} (pp : Prime p) (hn : n != 0)
  proof: Iff.trans (by simp) (pp.pow_dvd_iff_le_factorization hn)

中文:
定理 素.dvd_iff_one_le_factorization
  条件: {p n : 自然数} (pp : 素 p) (hn : n != 0)
  证明: Iff.trans (by simp) (pp.pow_dvd_iff_le_factorization hn)

Depends on / 依赖: Iff.trans, pow_dvd_iff_le_factorization, pp.pow_dvd_iff_le_factorization
-/
theorem Prime.dvd_iff_one_le_factorization {p n : Nat} (pp : Prime p) (hn : n != 0) :
    p ∣ n ↔ 1 <= n.factorization p :=
  Iff.trans (by simp) (pp.pow_dvd_iff_le_factorization hn)

/--
theorem `exists_factorization_lt_of_lt` / 定理 `exists_factorization_lt_of_lt`

English:
theorem exists_factorization_lt_of_lt
  given: {a b : Nat} (ha : a != 0) (hab : a < b)
  proof: by
  have hb : b != 0 := (ha.bot_lt.trans hab).ne'
  contrapose! hab
  rw [← Finsupp.le_def]; rw [factorization_le_iff_dvd hb ha] at hab
  exact le_of_dvd ha.bot_lt hab

@[simp]

中文:
定理 存在_factorization_lt_of_lt
  条件: {a b : 自然数} (ha : a != 0) (hab : a < b)
  证明: by
  have hb : b != 0 := (ha.bot_lt.trans hab).ne'
  contrapose! hab
  rw [← Finsupp.le_def]; rw [factorization_le_iff_dvd hb ha] at hab
  exact le_of_dvd ha.bot_lt hab

@[simp]

Depends on / 依赖: Finsupp, Finsupp.le_def, bot_lt, contrapose, factorization_le_iff_dvd, ha.bot_lt, ha.bot_lt.trans, le_def, le_of_dvd
-/
theorem exists_factorization_lt_of_lt {a b : Nat} (ha : a != 0) (hab : a < b) :
    exists p : Nat, a.factorization p < b.factorization p := by
  have hb : b != 0 := (ha.bot_lt.trans hab).ne'
  contrapose! hab
  rw [← Finsupp.le_def]; rw [factorization_le_iff_dvd hb ha] at hab
  exact le_of_dvd ha.bot_lt hab

@[simp]
/--
theorem `factorization_div` / 定理 `factorization_div`

English:
theorem factorization_div
  given: {d n : Nat} (h : d ∣ n)
  proof: by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [zero_dvd_iff.mp h]
  rcases eq_or_ne n 0 with (rfl | hn); · simp [tsub_eq_zero_of_le]
  apply add_left_injective d.factorization
  simp only
  rw [tsub_add_cancel_of_le <| (Nat.factorization_le_iff_dvd hd hn).mpr h]; rw [←
    Nat.factorization_mul (

中文:
定理 factorization_div
  条件: {d n : 自然数} (h : d ∣ n)
  证明: by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [zero_dvd_iff.mp h]
  rcases eq_or_ne n 0 with (rfl | hn); · simp [tsub_eq_zero_of_le]
  apply add_left_injective d.factorization
  simp only
  rw [tsub_add_cancel_of_le <| (Nat.factorization_le_iff_dvd hd hn).mpr h]; rw [←
    Nat.factorization_mul (

Depends on / 依赖: Nat.div_mul_cancel, Nat.div_pos, Nat.factorization_le_iff_dvd, Nat.factorization_mul, Nat.le_of_dvd, add_left_injective, bot_lt, d.factorization, div_mul_cancel, div_pos, eq_or_ne, factorization, factorization_le_iff_dvd, factorization_mul, hd.bot_lt, hn.bot_lt, le_of_dvd, tsub_add_cancel_of_le, tsub_eq_zero_of_le, zero_dvd_iff
-/
theorem factorization_div {d n : Nat} (h : d ∣ n) :
    (n / d).factorization = n.factorization - d.factorization := by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [zero_dvd_iff.mp h]
  rcases eq_or_ne n 0 with (rfl | hn); · simp [tsub_eq_zero_of_le]
  apply add_left_injective d.factorization
  simp only
  rw [tsub_add_cancel_of_le <| (Nat.factorization_le_iff_dvd hd hn).mpr h]; rw [←
    Nat.factorization_mul (Nat.div_pos (Nat.le_of_dvd hn.bot_lt h) hd.bot_lt).ne' hd]; rw [Nat.div_mul_cancel h]

/--
theorem `dvd_ordProj_of_dvd` / 定理 `dvd_ordProj_of_dvd`

English:
theorem dvd_ordProj_of_dvd
  given: {n p : Nat} (hn : n != 0) (pp : p.Prime) (h : p ∣ n)
  statement: p ∣ ordProj[p] n
  proof: dvd_pow_self p (Prime.factorization_pos_of_dvd pp hn h).ne'

中文:
定理 dvd_ordProj_of_dvd
  条件: {n p : 自然数} (hn : n != 0) (pp : p.素) (h : p ∣ n)
  结论: p ∣ ordProj[p] n
  证明: dvd_pow_self p (Prime.factorization_pos_of_dvd pp hn h).ne'

Depends on / 依赖: Prime.factorization_pos_of_dvd, dvd_pow_self, factorization_pos_of_dvd
-/
theorem dvd_ordProj_of_dvd {n p : Nat} (hn : n != 0) (pp : p.Prime) (h : p ∣ n) : p ∣ ordProj[p] n :=
  dvd_pow_self p (Prime.factorization_pos_of_dvd pp hn h).ne'

/--
theorem `not_dvd_ordCompl` / 定理 `not_dvd_ordCompl`

English:
theorem not_dvd_ordCompl
  given: {n p : Nat} (hp : Prime p) (hn : n != 0)
  statement: ¬p ∣ ordCompl[p] n
  proof: by
  rw [Nat.Prime.dvd_iff_one_le_factorization hp (ordCompl_pos p hn).ne']
  rw [Nat.factorization_div (Nat.ordProj_dvd n p)]
  simp [hp.factorization]

中文:
定理 not_dvd_ordCompl
  条件: {n p : 自然数} (hp : 素 p) (hn : n != 0)
  结论: ¬p ∣ ordCompl[p] n
  证明: by
  rw [Nat.Prime.dvd_iff_one_le_factorization hp (ordCompl_pos p hn).ne']
  rw [Nat.factorization_div (Nat.ordProj_dvd n p)]
  simp [hp.factorization]

Depends on / 依赖: Nat.Prime.dvd_iff_one_le_factorization, Nat.factorization_div, Nat.ordProj_dvd, dvd_iff_one_le_factorization, factorization, factorization_div, hp.factorization, ordCompl_pos, ordProj_dvd
-/
theorem not_dvd_ordCompl {n p : Nat} (hp : Prime p) (hn : n != 0) : ¬p ∣ ordCompl[p] n := by
  rw [Nat.Prime.dvd_iff_one_le_factorization hp (ordCompl_pos p hn).ne']
  rw [Nat.factorization_div (Nat.ordProj_dvd n p)]
  simp [hp.factorization]

/--
theorem `coprime_ordCompl` / 定理 `coprime_ordCompl`

English:
theorem coprime_ordCompl
  given: {n p : Nat} (hp : Prime p) (hn : n != 0)
  statement: Coprime p (ordCompl[p] n)
  proof: (or_iff_left (not_dvd_ordCompl hp hn)).mp coprime_or_dvd_of_prime hp _

中文:
定理 coprime_ordCompl
  条件: {n p : 自然数} (hp : 素 p) (hn : n != 0)
  结论: Coprime p (ordCompl[p] n)
  证明: (or_iff_left (not_dvd_ordCompl hp hn)).mp coprime_or_dvd_of_prime hp _

Depends on / 依赖: coprime_or_dvd_of_prime, not_dvd_ordCompl, or_iff_left
-/
theorem coprime_ordCompl {n p : Nat} (hp : Prime p) (hn : n != 0) : Coprime p (ordCompl[p] n) :=
(or_iff_left (not_dvd_ordCompl hp hn)).mp coprime_or_dvd_of_prime hp _

/--
theorem `factorization_ordCompl` / 定理 `factorization_ordCompl`

English:
theorem factorization_ordCompl
  given: (n p : Nat)
  proof: by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then ?_ else
    simp [pp]
  ext q
  rcases eq_or_ne q p with (rfl | hqp)
  · simp only [Finsupp.erase_same, factorization_eq_zero_iff, not_dvd_ordCompl pp hn]
    simp
  · rw [Finsupp.erase_ne hqp, factorization_div (ordProj_dvd n p)]
    sim

中文:
定理 factorization_ordCompl
  条件: (n p : 自然数)
  证明: by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then ?_ else
    simp [pp]
  ext q
  rcases eq_or_ne q p with (rfl | hqp)
  · simp only [Finsupp.erase_same, factorization_eq_zero_iff, not_dvd_ordCompl pp hn]
    simp
  · rw [Finsupp.erase_ne hqp, factorization_div (ordProj_dvd n p)]
    sim

Depends on / 依赖: Finsupp, Finsupp.erase_ne, Finsupp.erase_same, eq_or_ne, erase_ne, erase_same, factorization, factorization_div, factorization_eq_zero_iff, hqp.symm, not_dvd_ordCompl, ordProj_dvd, p.Prime, pp.factorization
-/
theorem factorization_ordCompl (n p : Nat) :
    (ordCompl[p] n).factorization = n.factorization.erase p := by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then ?_ else
    simp [pp]
  ext q
  rcases eq_or_ne q p with (rfl | hqp)
  · simp only [Finsupp.erase_same, factorization_eq_zero_iff, not_dvd_ordCompl pp hn]
    simp
  · rw [Finsupp.erase_ne hqp, factorization_div (ordProj_dvd n p)]
    simp [pp.factorization, hqp.symm]

/--
theorem `ordProj_self_pow` / 定理 `ordProj_self_pow`

English:
theorem ordProj_self_pow
  given: {p k : Nat} (hp : Prime p)
  statement: ordProj[p] (p ^ k) = p ^ k
  proof: by
  simp [hp]

中文:
定理 ordProj_self_pow
  条件: {p k : 自然数} (hp : 素 p)
  结论: ordProj[p] (p ^ k) = p ^ k
  证明: by
  simp [hp]
-/
theorem ordProj_self_pow {p k : Nat} (hp : Prime p) : ordProj[p] (p ^ k) = p ^ k := by
  simp [hp]

/--
theorem `ordCompl_self_pow` / 定理 `ordCompl_self_pow`

English:
theorem ordCompl_self_pow
  given: {p k : Nat} (hp : Prime p)
  statement: ordCompl[p] (p ^ k) = 1
  proof: by
  apply Nat.eq_of_factorization_eq
  · exact pos_iff_ne_zero.mp (ordCompl_pos p (pow_ne_zero k hp.ne_zero))
  · exact one_ne_zero
  · simp [Prime.factorization_pow hp]

中文:
定理 ordCompl_self_pow
  条件: {p k : 自然数} (hp : 素 p)
  结论: ordCompl[p] (p ^ k) = 1
  证明: by
  apply Nat.eq_of_factorization_eq
  · exact pos_iff_ne_zero.mp (ordCompl_pos p (pow_ne_zero k hp.ne_zero))
  · exact one_ne_zero
  · simp [Prime.factorization_pow hp]

Depends on / 依赖: Nat.eq_of_factorization_eq, Prime.factorization_pow, eq_of_factorization_eq, factorization_pow, hp.ne_zero, ne_zero, one_ne_zero, ordCompl_pos, pos_iff_ne_zero, pos_iff_ne_zero.mp, pow_ne_zero
-/
theorem ordCompl_self_pow {p k : Nat} (hp : Prime p) : ordCompl[p] (p ^ k) = 1 := by
  apply Nat.eq_of_factorization_eq
  · exact pos_iff_ne_zero.mp (ordCompl_pos p (pow_ne_zero k hp.ne_zero))
  · exact one_ne_zero
  · simp [Prime.factorization_pow hp]

/--
theorem `ordCompl_self_pow_mul` / 定理 `ordCompl_self_pow_mul`

English:
theorem ordCompl_self_pow_mul
  given: (n k : Nat) {p : Nat} (hp : Prime p)
  proof: by
  rw [ordCompl_mul]; rw [ordCompl_self_pow hp]; rw [one_mul]

中文:
定理 ordCompl_self_pow_mul
  条件: (n k : 自然数) {p : 自然数} (hp : 素 p)
  证明: by
  rw [ordCompl_mul]; rw [ordCompl_self_pow hp]; rw [one_mul]

Depends on / 依赖: one_mul, ordCompl_mul, ordCompl_self_pow
-/
theorem ordCompl_self_pow_mul (n k : Nat) {p : Nat} (hp : Prime p) :
    ordCompl[p] (p ^ k * n) = ordCompl[p] n := by
  rw [ordCompl_mul]; rw [ordCompl_self_pow hp]; rw [one_mul]

/--
theorem `ordCompl_eq_self_iff_zero_or_not_dvd` / 定理 `ordCompl_eq_self_iff_zero_or_not_dvd`

English:
theorem ordCompl_eq_self_iff_zero_or_not_dvd
  given: (n : Nat) {p : Nat} (hp : Prime p)
  proof: by
  constructor
  · intro h
    by_cases n_zero : n = 0
    · simp [n_zero]
    · right
      rw [← h]
      exact not_dvd_ordCompl hp n_zero
  · rintro (n_eq_zero | not_dvd)
    · simp [n_eq_zero]
    · simp [Nat.factorization_eq_zero_of_not_dvd not_dvd]

中文:
定理 ordCompl_eq_self_iff_zero_or_not_dvd
  条件: (n : 自然数) {p : 自然数} (hp : 素 p)
  证明: by
  constructor
  · intro h
    by_cases n_zero : n = 0
    · simp [n_zero]
    · right
      rw [← h]
      exact not_dvd_ordCompl hp n_zero
  · rintro (n_eq_zero | not_dvd)
    · simp [n_eq_zero]
    · simp [Nat.factorization_eq_zero_of_not_dvd not_dvd]

Depends on / 依赖: Nat.factorization_eq_zero_of_not_dvd, factorization_eq_zero_of_not_dvd, n_eq_zero, n_zero, not_dvd, not_dvd_ordCompl
-/
theorem ordCompl_eq_self_iff_zero_or_not_dvd (n : Nat) {p : Nat} (hp : Prime p) :
    ordCompl[p] n = n ↔ n = 0 ∨ ¬p ∣ n := by
  constructor
  · intro h
    by_cases n_zero : n = 0
    · simp [n_zero]
    · right
      rw [← h]
      exact not_dvd_ordCompl hp n_zero
  · rintro (n_eq_zero | not_dvd)
    · simp [n_eq_zero]
    · simp [Nat.factorization_eq_zero_of_not_dvd not_dvd]

/--
theorem `ordCompl_pow_mul_of_not_dvd` / 定理 `ordCompl_pow_mul_of_not_dvd`

English:
theorem ordCompl_pow_mul_of_not_dvd
  given: {m : Nat} (k : Nat) {p : Nat} (hp : p.Prime) (hm : ¬p ∣ m)
  proof: by
  rw [ordCompl_self_pow_mul m k hp]
  exact (ordCompl_eq_self_iff_zero_or_not_dvd m hp).mpr (Or.inr hm)

中文:
定理 ordCompl_pow_mul_of_not_dvd
  条件: {m : 自然数} (k : 自然数) {p : 自然数} (hp : p.素) (hm : ¬p ∣ m)
  证明: by
  rw [ordCompl_self_pow_mul m k hp]
  exact (ordCompl_eq_self_iff_zero_or_not_dvd m hp).mpr (Or.inr hm)

Depends on / 依赖: Or.inr, ordCompl_eq_self_iff_zero_or_not_dvd, ordCompl_self_pow_mul
-/
theorem ordCompl_pow_mul_of_not_dvd {m : Nat} (k : Nat) {p : Nat} (hp : p.Prime) (hm : ¬p ∣ m) :
    ordCompl[p] (p ^ k * m) = m := by
  rw [ordCompl_self_pow_mul m k hp]
  exact (ordCompl_eq_self_iff_zero_or_not_dvd m hp).mpr (Or.inr hm)

/--
theorem `ordCompl_pow_mul_eq_self_iff` / 定理 `ordCompl_pow_mul_eq_self_iff`

English:
theorem ordCompl_pow_mul_eq_self_iff
  given: (k m : Nat) {p : Nat} (hp : p.Prime)
  proof: by
  rw [ordCompl_self_pow_mul m k hp]; rw [ordCompl_eq_self_iff_zero_or_not_dvd m hp]

中文:
定理 ordCompl_pow_mul_eq_self_iff
  条件: (k m : 自然数) {p : 自然数} (hp : p.素)
  证明: by
  rw [ordCompl_self_pow_mul m k hp]; rw [ordCompl_eq_self_iff_zero_or_not_dvd m hp]

Depends on / 依赖: ordCompl_eq_self_iff_zero_or_not_dvd, ordCompl_self_pow_mul
-/
theorem ordCompl_pow_mul_eq_self_iff (k m : Nat) {p : Nat} (hp : p.Prime) :
    ordCompl[p] (p ^ k * m) = m ↔ m = 0 ∨ ¬p ∣ m := by
  rw [ordCompl_self_pow_mul m k hp]; rw [ordCompl_eq_self_iff_zero_or_not_dvd m hp]

/--
theorem `ordCompl_div_pow_of_dvd` / 定理 `ordCompl_div_pow_of_dvd`

English:
theorem ordCompl_div_pow_of_dvd
  given: (k : Nat) {x p : Nat} (hp : p.Prime) (hx : p ^ k ∣ x)
  proof: by
  obtain ⟨m, rfl⟩ := hx
  rw [Nat.mul_div_cancel_left m (pow_pos hp.pos k)]; rw [← ordCompl_self_pow_mul m k hp]

中文:
定理 ordCompl_div_pow_of_dvd
  条件: (k : 自然数) {x p : 自然数} (hp : p.素) (hx : p ^ k ∣ x)
  证明: by
  obtain ⟨m, rfl⟩ := hx
  rw [Nat.mul_div_cancel_left m (pow_pos hp.pos k)]; rw [← ordCompl_self_pow_mul m k hp]

Depends on / 依赖: Nat.mul_div_cancel_left, hp.pos, mul_div_cancel_left, ordCompl_self_pow_mul, pow_pos
-/
theorem ordCompl_div_pow_of_dvd (k : Nat) {x p : Nat} (hp : p.Prime) (hx : p ^ k ∣ x) :
    ordCompl[p] (x / p ^ k) = ordCompl[p] x := by
  obtain ⟨m, rfl⟩ := hx
  rw [Nat.mul_div_cancel_left m (pow_pos hp.pos k)]; rw [← ordCompl_self_pow_mul m k hp]

/--
theorem `ordCompl_div_of_dvd` / 定理 `ordCompl_div_of_dvd`

English:
theorem ordCompl_div_of_dvd
  given: {x : Nat} {p : Nat} (hp : p.Prime) (hx : p ∣ x)
  proof: by
  simpa [pow_one] using ordCompl_div_pow_of_dvd 1 hp (show p ^ 1 ∣ x by simpa)

中文:
定理 ordCompl_div_of_dvd
  条件: {x : 自然数} {p : 自然数} (hp : p.素) (hx : p ∣ x)
  证明: by
  simpa [pow_one] using ordCompl_div_pow_of_dvd 1 hp (show p ^ 1 ∣ x by simpa)

Depends on / 依赖: ordCompl_div_pow_of_dvd, pow_one
-/
theorem ordCompl_div_of_dvd {x : Nat} {p : Nat} (hp : p.Prime) (hx : p ∣ x) :
    ordCompl[p] (x / p) = ordCompl[p] x := by
  simpa [pow_one] using ordCompl_div_pow_of_dvd 1 hp (show p ^ 1 ∣ x by simpa)

-- `ordCompl[p] n` is the largest divisor of `n` not divisible by `p`.
/--
theorem `dvd_ordCompl_of_dvd_not_dvd` / 定理 `dvd_ordCompl_of_dvd_not_dvd`

English:
theorem dvd_ordCompl_of_dvd_not_dvd
  given: {p d n : Nat} (hdn : d ∣ n) (hpd : ¬p ∣ d)
  proof: by
  if hn0 : n = 0 then simp [hn0] else
  if hd0 : d = 0 then simp [hd0] at hpd else
  rw [← factorization_le_iff_dvd hd0 (ordCompl_pos p hn0).ne']; rw [factorization_ordCompl]
  intro q
  if hqp : q = p then
    simp [factorization_eq_zero_iff, hqp, hpd]
  else
    simp [hqp, (factorization_le_iff

中文:
定理 dvd_ordCompl_of_dvd_not_dvd
  条件: {p d n : 自然数} (hdn : d ∣ n) (hpd : ¬p ∣ d)
  证明: by
  if hn0 : n = 0 then simp [hn0] else
  if hd0 : d = 0 then simp [hd0] at hpd else
  rw [← factorization_le_iff_dvd hd0 (ordCompl_pos p hn0).ne']; rw [factorization_ordCompl]
  intro q
  if hqp : q = p then
    simp [factorization_eq_zero_iff, hqp, hpd]
  else
    simp [hqp, (factorization_le_iff

Depends on / 依赖: factorization_eq_zero_iff, factorization_le_iff_dvd, factorization_ordCompl, ordCompl_pos
-/
theorem dvd_ordCompl_of_dvd_not_dvd {p d n : Nat} (hdn : d ∣ n) (hpd : ¬p ∣ d) :
    d ∣ ordCompl[p] n := by
  if hn0 : n = 0 then simp [hn0] else
  if hd0 : d = 0 then simp [hd0] at hpd else
  rw [← factorization_le_iff_dvd hd0 (ordCompl_pos p hn0).ne']; rw [factorization_ordCompl]
  intro q
  if hqp : q = p then
    simp [factorization_eq_zero_iff, hqp, hpd]
  else
    simp [hqp, (factorization_le_iff_dvd hd0 hn0).2 hdn q]

/--
theorem `exists_eq_pow_mul_and_not_dvd` / 定理 `exists_eq_pow_mul_and_not_dvd`

English:
theorem exists_eq_pow_mul_and_not_dvd
  given: {n : Nat} (hn : n != 0) (p : Nat) (hp : p != 1)
  proof: let ⟨a', h₁, h₂⟩ :=
    (Nat.finiteMultiplicity_iff.mpr ⟨hp, Nat.pos_of_ne_zero hn⟩).exists_eq_pow_mul_and_not_dvd
  ⟨_, a', h₂, h₁⟩

中文:
定理 存在_eq_pow_mul_and_not_dvd
  条件: {n : 自然数} (hn : n != 0) (p : 自然数) (hp : p != 1)
  证明: let ⟨a', h₁, h₂⟩ :=
    (Nat.finiteMultiplicity_iff.mpr ⟨hp, Nat.pos_of_ne_zero hn⟩).exists_eq_pow_mul_and_not_dvd
  ⟨_, a', h₂, h₁⟩

Depends on / 依赖: Nat.finiteMultiplicity_iff.mpr, Nat.pos_of_ne_zero, exists_eq_pow_mul_and_not_dvd, finiteMultiplicity_iff, pos_of_ne_zero
-/
theorem exists_eq_pow_mul_and_not_dvd {n : Nat} (hn : n != 0) (p : Nat) (hp : p != 1) :
    exists e n' : Nat, ¬p ∣ n' ∧ n = p ^ e * n' :=
  let ⟨a', h₁, h₂⟩ :=
    (Nat.finiteMultiplicity_iff.mpr ⟨hp, Nat.pos_of_ne_zero hn⟩).exists_eq_pow_mul_and_not_dvd
  ⟨_, a', h₂, h₁⟩

/--
theorem `exists_eq_two_pow_mul_odd` / 定理 `exists_eq_two_pow_mul_odd`

English:
theorem exists_eq_two_pow_mul_odd
  given: {n : Nat} (hn : n != 0)
  proof: let ⟨k, m, hm, hn⟩ := exists_eq_pow_mul_and_not_dvd hn 2 (succ_ne_self 1)
  ⟨k, m, not_even_iff_odd.1 (mt Even.two_dvd hm), hn⟩

中文:
定理 存在_eq_two_pow_mul_odd
  条件: {n : 自然数} (hn : n != 0)
  证明: let ⟨k, m, hm, hn⟩ := exists_eq_pow_mul_and_not_dvd hn 2 (succ_ne_self 1)
  ⟨k, m, not_even_iff_odd.1 (mt Even.two_dvd hm), hn⟩

Depends on / 依赖: Even.two_dvd, exists_eq_pow_mul_and_not_dvd, not_even_iff_odd, succ_ne_self, two_dvd
-/
theorem exists_eq_two_pow_mul_odd {n : Nat} (hn : n != 0) :
    exists k m : Nat, Odd m ∧ n = 2 ^ k * m :=
  let ⟨k, m, hm, hn⟩ := exists_eq_pow_mul_and_not_dvd hn 2 (succ_ne_self 1)
  ⟨k, m, not_even_iff_odd.1 (mt Even.two_dvd hm), hn⟩

/--
theorem `dvd_iff_div_factorization_eq_tsub` / 定理 `dvd_iff_div_factorization_eq_tsub`

English:
theorem dvd_iff_div_factorization_eq_tsub
  given: {d n : Nat} (hd : d != 0) (hdn : d <= n)
  proof: by
  refine ⟨factorization_div, ?_⟩
  rcases eq_or_lt_of_le hdn with (rfl | hd_lt_n); · simp
  have h1 : n / d != 0 := by simp [*]
  intro h
  rw [dvd_iff_le_div_mul n d]
  by_contra h2
  obtain ⟨p, hp⟩ := exists_factorization_lt_of_lt (mul_ne_zero h1 hd) (not_le.mp h2)
  rwa [factorization_mul h1 h

中文:
定理 dvd_iff_div_factorization_eq_tsub
  条件: {d n : 自然数} (hd : d != 0) (hdn : d <= n)
  证明: by
  refine ⟨factorization_div, ?_⟩
  rcases eq_or_lt_of_le hdn with (rfl | hd_lt_n); · simp
  have h1 : n / d != 0 := by simp [*]
  intro h
  rw [dvd_iff_le_div_mul n d]
  by_contra h2
  obtain ⟨p, hp⟩ := exists_factorization_lt_of_lt (mul_ne_zero h1 hd) (not_le.mp h2)
  rwa [factorization_mul h1 h

Depends on / 依赖: add_apply, dvd_iff_le_div_mul, eq_or_lt_of_le, exists_factorization_lt_of_lt, factorization_div, factorization_mul, hd_lt_n, lt_self_iff_false, lt_tsub_iff_right, mul_ne_zero, not_le, not_le.mp, tsub_apply
-/
theorem dvd_iff_div_factorization_eq_tsub {d n : Nat} (hd : d != 0) (hdn : d <= n) :
    d ∣ n ↔ (n / d).factorization = n.factorization - d.factorization := by
  refine ⟨factorization_div, ?_⟩
  rcases eq_or_lt_of_le hdn with (rfl | hd_lt_n); · simp
  have h1 : n / d != 0 := by simp [*]
  intro h
  rw [dvd_iff_le_div_mul n d]
  by_contra h2
  obtain ⟨p, hp⟩ := exists_factorization_lt_of_lt (mul_ne_zero h1 hd) (not_le.mp h2)
  rwa [factorization_mul h1 hd, add_apply, ← lt_tsub_iff_right, h, tsub_apply,
    lt_self_iff_false] at hp

/--
theorem `ordProj_dvd_ordProj_of_dvd` / 定理 `ordProj_dvd_ordProj_of_dvd`

English:
theorem ordProj_dvd_ordProj_of_dvd
  given: {a b : Nat} (hb0 : b != 0) (hab : a ∣ b) (p : Nat)
  proof: by
  rcases em' p.Prime with (pp | pp); · simp [pp]
  rcases eq_or_ne a 0 with (rfl | ha0); · simp
  rw [pow_dvd_pow_iff_le_right pp.one_lt]
  exact (factorization_le_iff_dvd ha0 hb0).2 hab p

中文:
定理 ordProj_dvd_ordProj_of_dvd
  条件: {a b : 自然数} (hb0 : b != 0) (hab : a ∣ b) (p : 自然数)
  证明: by
  rcases em' p.Prime with (pp | pp); · simp [pp]
  rcases eq_or_ne a 0 with (rfl | ha0); · simp
  rw [pow_dvd_pow_iff_le_right pp.one_lt]
  exact (factorization_le_iff_dvd ha0 hb0).2 hab p

Depends on / 依赖: eq_or_ne, factorization_le_iff_dvd, one_lt, p.Prime, pow_dvd_pow_iff_le_right, pp.one_lt
-/
theorem ordProj_dvd_ordProj_of_dvd {a b : Nat} (hb0 : b != 0) (hab : a ∣ b) (p : Nat) :
    ordProj[p] a ∣ ordProj[p] b := by
  rcases em' p.Prime with (pp | pp); · simp [pp]
  rcases eq_or_ne a 0 with (rfl | ha0); · simp
  rw [pow_dvd_pow_iff_le_right pp.one_lt]
  exact (factorization_le_iff_dvd ha0 hb0).2 hab p

/--
theorem `ordCompl_dvd_ordCompl_of_dvd` / 定理 `ordCompl_dvd_ordCompl_of_dvd`

English:
theorem ordCompl_dvd_ordCompl_of_dvd
  given: {a b : Nat} (hab : a ∣ b) (p : Nat)
  proof: by
  rcases em' p.Prime with (pp | pp)
  · simp [pp, hab]
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  rcases eq_or_ne a 0 with (rfl | ha0)
  · cases hb0 (zero_dvd_iff.1 hab)
  have ha := (Nat.div_pos (ordProj_le p ha0) (ordProj_pos a p)).ne'
  have hb := (Nat.div_pos (ordProj_le p hb0) (ordPro

中文:
定理 ordCompl_dvd_ordCompl_of_dvd
  条件: {a b : 自然数} (hab : a ∣ b) (p : 自然数)
  证明: by
  rcases em' p.Prime with (pp | pp)
  · simp [pp, hab]
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  rcases eq_or_ne a 0 with (rfl | ha0)
  · cases hb0 (zero_dvd_iff.1 hab)
  have ha := (Nat.div_pos (ordProj_le p ha0) (ordProj_pos a p)).ne'
  have hb := (Nat.div_pos (ordProj_le p hb0) (ordPro

Depends on / 依赖: Nat.div_pos, div_pos, eq_or_ne, erase_ne, factorization_, factorization_le_iff_dvd, factorization_ordCompl, ordProj_le, ordProj_pos, p.Prime, simp_rw, zero_dvd_iff
-/
theorem ordCompl_dvd_ordCompl_of_dvd {a b : Nat} (hab : a ∣ b) (p : Nat) :
    ordCompl[p] a ∣ ordCompl[p] b := by
  rcases em' p.Prime with (pp | pp)
  · simp [pp, hab]
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  rcases eq_or_ne a 0 with (rfl | ha0)
  · cases hb0 (zero_dvd_iff.1 hab)
  have ha := (Nat.div_pos (ordProj_le p ha0) (ordProj_pos a p)).ne'
  have hb := (Nat.div_pos (ordProj_le p hb0) (ordProj_pos b p)).ne'
  rw [← factorization_le_iff_dvd ha hb]; rw [factorization_ordCompl a p]; rw [factorization_ordCompl b p]
  intro q
  rcases eq_or_ne q p with (rfl | hqp)
  · simp
  simp_rw [erase_ne hqp]
  exact (factorization_le_iff_dvd ha0 hb0).2 hab q

/--
theorem `ordCompl_dvd_ordCompl_iff_dvd` / 定理 `ordCompl_dvd_ordCompl_iff_dvd`

English:
theorem ordCompl_dvd_ordCompl_iff_dvd
  given: (a b : Nat)
  proof: by
  refine ⟨fun h => ?_, fun hab p => ordCompl_dvd_ordCompl_of_dvd hab p⟩
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  if pa : a.Prime then ?_ else simpa [pa] using h a
  if pb : b.Prime then ?_ else simpa [pb] using h b
  rw [prime_dvd_prime_iff_eq pa pb]
  by_contra hab
  apply pa.ne_one
  r

中文:
定理 ordCompl_dvd_ordCompl_iff_dvd
  条件: (a b : 自然数)
  证明: by
  refine ⟨fun h => ?_, fun hab p => ordCompl_dvd_ordCompl_of_dvd hab p⟩
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  if pa : a.Prime then ?_ else simpa [pa] using h a
  if pb : b.Prime then ?_ else simpa [pb] using h b
  rw [prime_dvd_prime_iff_eq pa pb]
  by_contra hab
  apply pa.ne_one
  r

Depends on / 依赖: Nat.dvd_one, Nat.mul_dvd_mul_iff_left, Prime.factorization, Prime.factorization_self, a.Prime, b.Prime, bot_lt, dvd_one, eq_or_ne, factorization, factorization_self, hb0.bot_lt, mul_dvd_mul_iff_left, mul_one, ne_one, ordCompl_dvd_ordCompl_of_dvd, pa.ne_one, prime_dvd_prime_iff_eq
-/
theorem ordCompl_dvd_ordCompl_iff_dvd (a b : Nat) :
    (forall p : Nat, ordCompl[p] a ∣ ordCompl[p] b) ↔ a ∣ b := by
  refine ⟨fun h => ?_, fun hab p => ordCompl_dvd_ordCompl_of_dvd hab p⟩
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  if pa : a.Prime then ?_ else simpa [pa] using h a
  if pb : b.Prime then ?_ else simpa [pb] using h b
  rw [prime_dvd_prime_iff_eq pa pb]
  by_contra hab
  apply pa.ne_one
  rw [← Nat.dvd_one]; rw [← Nat.mul_dvd_mul_iff_left hb0.bot_lt]; rw [mul_one]
  simpa [Prime.factorization_self pb, Prime.factorization pa, hab] using h b

/--
theorem `dvd_iff_prime_pow_dvd_dvd` / 定理 `dvd_iff_prime_pow_dvd_dvd`

English:
theorem dvd_iff_prime_pow_dvd_dvd
  given: (n d : Nat)
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases eq_or_ne d 0 with (rfl | hd)
  · simp only [zero_dvd_iff, hn, false_iff, not_forall]
    exact ⟨2, n, prime_two, dvd_zero _, mt (le_of_dvd hn.bot_lt) (n.lt_two_pow_self).not_ge⟩
  refine ⟨fun h p k _ hpkd => dvd_trans hpkd h, ?_⟩
  rw [← fac

中文:
定理 dvd_iff_prime_pow_dvd_dvd
  条件: (n d : 自然数)
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases eq_or_ne d 0 with (rfl | hd)
  · simp only [zero_dvd_iff, hn, false_iff, not_forall]
    exact ⟨2, n, prime_two, dvd_zero _, mt (le_of_dvd hn.bot_lt) (n.lt_two_pow_self).not_ge⟩
  refine ⟨fun h p k _ hpkd => dvd_trans hpkd h, ?_⟩
  rw [← fac

Depends on / 依赖: bot_lt, dvd_trans, dvd_zero, eq_or_ne, factorization_prime_le_iff_dvd, false_iff, hn.bot_lt, le_of_dvd, lt_two_pow_self, n.lt_two_pow_self, not_forall, not_ge, ordProj_dvd, pow_dvd_iff_le_factorization, pp.pow_dvd_iff_le_factorization, prime_two, simp_rw, zero_dvd_iff
-/
theorem dvd_iff_prime_pow_dvd_dvd (n d : Nat) :
    d ∣ n ↔ forall p k : Nat, Prime p -> p ^ k ∣ d -> p ^ k ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases eq_or_ne d 0 with (rfl | hd)
  · simp only [zero_dvd_iff, hn, false_iff, not_forall]
    exact ⟨2, n, prime_two, dvd_zero _, mt (le_of_dvd hn.bot_lt) (n.lt_two_pow_self).not_ge⟩
  refine ⟨fun h p k _ hpkd => dvd_trans hpkd h, ?_⟩
  rw [← factorization_prime_le_iff_dvd hd hn]
  intro h p pp
  simp_rw [← pp.pow_dvd_iff_le_factorization hn]
  exact h p _ pp (ordProj_dvd _ _)

/--
theorem `prod_primeFactors_dvd` / 定理 `prod_primeFactors_dvd`

English:
theorem prod_primeFactors_dvd
  given: (n : Nat)
  statement: ∏ p in n.primeFactors, p ∣ n
  proof: by
  by_cases hn : n = 0
  · subst hn
    simp
  · simpa [prod_primeFactorsList hn] using (n.primeFactorsList : Multiset Nat).toFinset_prod_dvd_prod

中文:
定理 prod_primeFactors_dvd
  条件: (n : 自然数)
  结论: ∏ p in n.primeFactors, p ∣ n
  证明: by
  by_cases hn : n = 0
  · subst hn
    simp
  · simpa [prod_primeFactorsList hn] using (n.primeFactorsList : Multiset Nat).toFinset_prod_dvd_prod

Depends on / 依赖: Multiset, n.primeFactorsList, primeFactorsList, prod_primeFactorsList, toFinset_prod_dvd_prod
-/
theorem prod_primeFactors_dvd (n : Nat) : ∏ p in n.primeFactors, p ∣ n := by
  by_cases hn : n = 0
  · subst hn
    simp
  · simpa [prod_primeFactorsList hn] using (n.primeFactorsList : Multiset Nat).toFinset_prod_dvd_prod

/--
theorem `factorization_gcd` / 定理 `factorization_gcd`

English:
theorem factorization_gcd
  given: {a b : Nat} (ha_pos : a != 0) (hb_pos : b != 0)
  proof: by
  suffices (a.factorization ⊓ b.factorization).prod (· ^ ·) = gcd a b by
    rw [← this]; rw [factorization_prod_pow_eq_self_of_le_factorization inf_le_left]
  apply gcd_greatest
  · exact prod_pow_dvd_of_le_factorization inf_le_left
  · exact prod_pow_dvd_of_le_factorization inf_le_right
  · int

中文:
定理 factorization_gcd
  条件: {a b : 自然数} (ha_pos : a != 0) (hb_pos : b != 0)
  证明: by
  suffices (a.factorization ⊓ b.factorization).prod (· ^ ·) = gcd a b by
    rw [← this]; rw [factorization_prod_pow_eq_self_of_le_factorization inf_le_left]
  apply gcd_greatest
  · exact prod_pow_dvd_of_le_factorization inf_le_left
  · exact prod_pow_dvd_of_le_factorization inf_le_right
  · int

Depends on / 依赖: a.factorization, absurd, b.factorization, dvd_prod_pow_of_factorization_le, eq_or_ne, factorization, factorization_le_iff_dvd, factorization_prod_pow_eq_self_of_le_factorization, gcd_greatest, ha_pos, he_pos, inf_le_left, inf_le_right, prod_pow_dvd_of_le_factorization, zero_dvd_iff, zero_dvd_iff.mp
-/
theorem factorization_gcd {a b : Nat} (ha_pos : a != 0) (hb_pos : b != 0) :
    (gcd a b).factorization = a.factorization ⊓ b.factorization := by
  suffices (a.factorization ⊓ b.factorization).prod (· ^ ·) = gcd a b by
    rw [← this]; rw [factorization_prod_pow_eq_self_of_le_factorization inf_le_left]
  apply gcd_greatest
  · exact prod_pow_dvd_of_le_factorization inf_le_left
  · exact prod_pow_dvd_of_le_factorization inf_le_right
  · intro e hea heb
    rcases eq_or_ne e 0 with (rfl | he_pos)
    · exact absurd (zero_dvd_iff.mp hea) ha_pos
    apply dvd_prod_pow_of_factorization_le he_pos
    have hea' := (factorization_le_iff_dvd he_pos ha_pos).mpr hea
    have heb' := (factorization_le_iff_dvd he_pos hb_pos).mpr heb
    simp [hea', heb']

/--
theorem `factorization_lcm` / 定理 `factorization_lcm`

English:
theorem factorization_lcm
  given: {a b : Nat} (ha : a != 0) (hb : b != 0)
  proof: by
  rw [← add_right_inj (a.gcd b).factorization]; rw [←
    factorization_mul (mt gcd_eq_zero_iff.1 fun h => ha h.1) (lcm_ne_zero ha hb)]; rw [gcd_mul_lcm]; rw [factorization_gcd ha hb]; rw [factorization_mul ha hb]
  ext1
  exact (min_add_max _ _).symm

@[to_additive sum_primeFactors_gcd_add_sum_p

中文:
定理 factorization_lcm
  条件: {a b : 自然数} (ha : a != 0) (hb : b != 0)
  证明: by
  rw [← add_right_inj (a.gcd b).factorization]; rw [←
    factorization_mul (mt gcd_eq_zero_iff.1 fun h => ha h.1) (lcm_ne_zero ha hb)]; rw [gcd_mul_lcm]; rw [factorization_gcd ha hb]; rw [factorization_mul ha hb]
  ext1
  exact (min_add_max _ _).symm

@[to_additive sum_primeFactors_gcd_add_sum_p

Depends on / 依赖: a.gcd, add_right_inj, factorization, factorization_gcd, factorization_mul, gcd_eq_zero_iff, gcd_mul_lcm, lcm_ne_zero, min_add_max
-/
theorem factorization_lcm {a b : Nat} (ha : a != 0) (hb : b != 0) :
    (a.lcm b).factorization = a.factorization ⊔ b.factorization := by
  rw [← add_right_inj (a.gcd b).factorization]; rw [←
    factorization_mul (mt gcd_eq_zero_iff.1 fun h => ha h.1) (lcm_ne_zero ha hb)]; rw [gcd_mul_lcm]; rw [factorization_gcd ha hb]; rw [factorization_mul ha hb]
  ext1
  exact (min_add_max _ _).symm

@[to_additive sum_primeFactors_gcd_add_sum_primeFactors_mul]
/--
theorem `prod_primeFactors_gcd_mul_prod_primeFactors_mul` / 定理 `prod_primeFactors_gcd_mul_prod_primeFactors_mul`

English:
theorem prod_primeFactors_gcd_mul_prod_primeFactors_mul
  statement: {β : Type*} [CommMonoid β] (m n : Nat)
  proof: by
  obtain rfl | hm₀ := eq_or_ne m 0
  · simp
  obtain rfl | hn₀ := eq_or_ne n 0
  · simp
  · rw [primeFactors_mul hm₀ hn₀, primeFactors_gcd hm₀ hn₀, mul_comm, Finset.prod_union_inter]

中文:
定理 prod_primeFactors_gcd_mul_prod_primeFactors_mul
  结论: {β : 类型} [交换幺半群 β] (m n : 自然数)
  证明: by
  obtain rfl | hm₀ := eq_or_ne m 0
  · simp
  obtain rfl | hn₀ := eq_or_ne n 0
  · simp
  · rw [primeFactors_mul hm₀ hn₀, primeFactors_gcd hm₀ hn₀, mul_comm, Finset.prod_union_inter]

Depends on / 依赖: Finset, Finset.prod_union_inter, eq_or_ne, mul_comm, primeFactors_gcd, primeFactors_mul, prod_union_inter
-/
theorem prod_primeFactors_gcd_mul_prod_primeFactors_mul {β : Type*} [CommMonoid β] (m n : Nat)
    (f : Nat -> β) :
    (m.gcd n).primeFactors.prod f * (m * n).primeFactors.prod f =
      m.primeFactors.prod f * n.primeFactors.prod f := by
  obtain rfl | hm₀ := eq_or_ne m 0
  · simp
  obtain rfl | hn₀ := eq_or_ne n 0
  · simp
  · rw [primeFactors_mul hm₀ hn₀, primeFactors_gcd hm₀ hn₀, mul_comm, Finset.prod_union_inter]

/--
theorem `setOfPred_pow_dvd_eq_Icc_factorization` / 定理 `setOfPred_pow_dvd_eq_Icc_factorization`

English:
theorem setOfPred_pow_dvd_eq_Icc_factorization
  given: {n p : Nat} (pp : p.Prime) (hn : n != 0)
  proof: by
  ext
  simp [one_le_iff_ne_zero, pp.pow_dvd_iff_le_factorization hn]

@[deprecated (since := "2026-07-09")]
alias setOf_pow_dvd_eq_Icc_factorization := setOfPred_pow_dvd_eq_Icc_factorization

中文:
定理 setOfPred_pow_dvd_eq_Icc_factorization
  条件: {n p : 自然数} (pp : p.素) (hn : n != 0)
  证明: by
  ext
  simp [one_le_iff_ne_zero, pp.pow_dvd_iff_le_factorization hn]

@[deprecated (since := "2026-07-09")]
alias setOf_pow_dvd_eq_Icc_factorization := setOfPred_pow_dvd_eq_Icc_factorization

Depends on / 依赖: one_le_iff_ne_zero, pow_dvd_iff_le_factorization, pp.pow_dvd_iff_le_factorization
-/
theorem setOfPred_pow_dvd_eq_Icc_factorization {n p : Nat} (pp : p.Prime) (hn : n != 0) :
    { i : Nat | i != 0 ∧ p ^ i ∣ n } = Set.Icc 1 (n.factorization p) := by
  ext
  simp [one_le_iff_ne_zero, pp.pow_dvd_iff_le_factorization hn]

@[deprecated (since := "2026-07-09")]
alias setOf_pow_dvd_eq_Icc_factorization := setOfPred_pow_dvd_eq_Icc_factorization

/--
theorem `Icc_factorization_eq_pow_dvd` / 定理 `Icc_factorization_eq_pow_dvd`

English:
theorem Icc_factorization_eq_pow_dvd
  given: (n : Nat) {p : Nat} (pp : Prime p)
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  ext x
  simp only [mem_Icc, Finset.mem_filter, mem_Ico, and_assoc, and_congr_right_iff,
    pp.pow_dvd_iff_le_factorization hn, iff_and_self]
  exact fun _ H => lt_of_le_of_lt H (factorization_lt p hn)

中文:
定理 Icc_factorization_eq_pow_dvd
  条件: (n : 自然数) {p : 自然数} (pp : 素 p)
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  ext x
  simp only [mem_Icc, Finset.mem_filter, mem_Ico, and_assoc, and_congr_right_iff,
    pp.pow_dvd_iff_le_factorization hn, iff_and_self]
  exact fun _ H => lt_of_le_of_lt H (factorization_lt p hn)

Depends on / 依赖: Finset, Finset.mem_filter, and_assoc, and_congr_right_iff, eq_or_ne, factorization_lt, iff_and_self, lt_of_le_of_lt, mem_Icc, mem_Ico, mem_filter, pow_dvd_iff_le_factorization, pp.pow_dvd_iff_le_factorization
-/
theorem Icc_factorization_eq_pow_dvd (n : Nat) {p : Nat} (pp : Prime p) :
    Icc 1 (n.factorization p) = {i in Ico 1 n | p ^ i ∣ n} := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  ext x
  simp only [mem_Icc, Finset.mem_filter, mem_Ico, and_assoc, and_congr_right_iff,
    pp.pow_dvd_iff_le_factorization hn, iff_and_self]
  exact fun _ H => lt_of_le_of_lt H (factorization_lt p hn)

/--
theorem `factorization_eq_card_pow_dvd` / 定理 `factorization_eq_card_pow_dvd`

English:
theorem factorization_eq_card_pow_dvd
  given: (n : Nat) {p : Nat} (pp : p.Prime)
  proof: by
  simp [← Icc_factorization_eq_pow_dvd n pp]

中文:
定理 factorization_eq_card_pow_dvd
  条件: (n : 自然数) {p : 自然数} (pp : p.素)
  证明: by
  simp [← Icc_factorization_eq_pow_dvd n pp]

Depends on / 依赖: Icc_factorization_eq_pow_dvd
-/
theorem factorization_eq_card_pow_dvd (n : Nat) {p : Nat} (pp : p.Prime) :
    n.factorization p = #{i in Ico 1 n | p ^ i ∣ n} := by
  simp [← Icc_factorization_eq_pow_dvd n pp]

/--
theorem `Ico_filter_pow_dvd_eq` / 定理 `Ico_filter_pow_dvd_eq`

English:
theorem Ico_filter_pow_dvd_eq
  given: {n p b : Nat} (pp : p.Prime) (hn : n != 0) (hb : n <= p ^ b)
  proof: by
  ext x
  simp only [Finset.mem_filter, mem_Ico, mem_Icc, and_congr_left_iff, and_congr_right_iff]
  rintro h1 -
exact iff_of_true (lt_of_pow_dvd_right hn pp.two_le h1)
(Nat.pow_le_pow_iff_right pp.one_lt).1 (le_of_dvd hn.bot_lt h1).trans hb

中文:
定理 Ico_filter_pow_dvd_eq
  条件: {n p b : 自然数} (pp : p.素) (hn : n != 0) (hb : n <= p ^ b)
  证明: by
  ext x
  simp only [Finset.mem_filter, mem_Ico, mem_Icc, and_congr_left_iff, and_congr_right_iff]
  rintro h1 -
exact iff_of_true (lt_of_pow_dvd_right hn pp.two_le h1)
(Nat.pow_le_pow_iff_right pp.one_lt).1 (le_of_dvd hn.bot_lt h1).trans hb

Depends on / 依赖: Finset, Finset.mem_filter, Nat.pow_le_pow_iff_right, and_congr_left_iff, and_congr_right_iff, bot_lt, hn.bot_lt, iff_of_true, le_of_dvd, lt_of_pow_dvd_right, mem_Icc, mem_Ico, mem_filter, one_lt, pow_le_pow_iff_right, pp.one_lt, pp.two_le, two_le
-/
theorem Ico_filter_pow_dvd_eq {n p b : Nat} (pp : p.Prime) (hn : n != 0) (hb : n <= p ^ b) :
    {i in Ico 1 n | p ^ i ∣ n} = {i in Icc 1 b | p ^ i ∣ n} := by
  ext x
  simp only [Finset.mem_filter, mem_Ico, mem_Icc, and_congr_left_iff, and_congr_right_iff]
  rintro h1 -
exact iff_of_true (lt_of_pow_dvd_right hn pp.two_le h1)
(Nat.pow_le_pow_iff_right pp.one_lt).1 (le_of_dvd hn.bot_lt h1).trans hb

/--
theorem `Ico_pow_dvd_eq_Ico_of_lt` / 定理 `Ico_pow_dvd_eq_Ico_of_lt`

English:
theorem Ico_pow_dvd_eq_Ico_of_lt
  given: {n p b : Nat} (pp : p.Prime) (hn : n != 0) (hb : n < p ^ b)
  proof: by
  ext i
  simp only [Finset.mem_filter, mem_Ico, and_congr_left_iff, and_congr_right_iff]
  refine fun h1 h2 => ⟨fun h => ?_, fun h => lt_of_pow_dvd_right hn (Prime.one_lt pp) h1⟩
  rcases p with - | p
  · rw [zero_pow (by lia), zero_dvd_iff] at h1
    exact (hn h1).elim
  · rw [← Nat.pow_lt_pow_

中文:
定理 Ico_pow_dvd_eq_Ico_of_lt
  条件: {n p b : 自然数} (pp : p.素) (hn : n != 0) (hb : n < p ^ b)
  证明: by
  ext i
  simp only [Finset.mem_filter, mem_Ico, and_congr_left_iff, and_congr_right_iff]
  refine fun h1 h2 => ⟨fun h => ?_, fun h => lt_of_pow_dvd_right hn (Prime.one_lt pp) h1⟩
  rcases p with - | p
  · rw [zero_pow (by lia), zero_dvd_iff] at h1
    exact (hn h1).elim
  · rw [← Nat.pow_lt_pow_

Depends on / 依赖: Finset, Finset.mem_filter, Nat.pow_lt_pow_iff_right, Nat.zero_lt_of_ne_zero, Prime.one_lt, and_congr_left_iff, and_congr_right_iff, le_of_dvd, lt_of_le_of_lt, lt_of_pow_dvd_right, mem_Ico, mem_filter, one_lt, pow_lt_pow_iff_right, zero_dvd_iff, zero_lt_of_ne_zero, zero_pow
-/
theorem Ico_pow_dvd_eq_Ico_of_lt {n p b : Nat} (pp : p.Prime) (hn : n != 0) (hb : n < p ^ b) :
    {i in Ico 1 n | p ^ i ∣ n} = {i in Ico 1 b | p ^ i ∣ n} := by
  ext i
  simp only [Finset.mem_filter, mem_Ico, and_congr_left_iff, and_congr_right_iff]
  refine fun h1 h2 => ⟨fun h => ?_, fun h => lt_of_pow_dvd_right hn (Prime.one_lt pp) h1⟩
  rcases p with - | p
  · rw [zero_pow (by lia), zero_dvd_iff] at h1
    exact (hn h1).elim
  · rw [← Nat.pow_lt_pow_iff_right (Prime.one_lt pp)]
    apply lt_of_le_of_lt (le_of_dvd (Nat.zero_lt_of_ne_zero hn) h1) hb

/--
theorem `factorization_eq_card_pow_dvd_of_lt` / 定理 `factorization_eq_card_pow_dvd_of_lt`

English:
theorem factorization_eq_card_pow_dvd_of_lt
  given: (hm : m.Prime) (hn : 0 < n) (hb : n < m ^ b)
  proof: by
  rwa [factorization_eq_card_pow_dvd n hm, Ico_pow_dvd_eq_Ico_of_lt hm (by lia)]

中文:
定理 factorization_eq_card_pow_dvd_of_lt
  条件: (hm : m.素) (hn : 0 < n) (hb : n < m ^ b)
  证明: by
  rwa [factorization_eq_card_pow_dvd n hm, Ico_pow_dvd_eq_Ico_of_lt hm (by lia)]

Depends on / 依赖: Ico_pow_dvd_eq_Ico_of_lt, factorization_eq_card_pow_dvd
-/
theorem factorization_eq_card_pow_dvd_of_lt (hm : m.Prime) (hn : 0 < n) (hb : n < m ^ b) :
    n.factorization m = #{i in Ico 1 b | m ^ i ∣ n} := by
  rwa [factorization_eq_card_pow_dvd n hm, Ico_pow_dvd_eq_Ico_of_lt hm (by lia)]

/-! ### Factorization and coprimes -/


/--
theorem `factorization_eq_of_coprime_left` / 定理 `factorization_eq_of_coprime_left`

English:
theorem factorization_eq_of_coprime_left
  statement: {p a b : Nat} (hab : Coprime a b)
  proof: by
  rw [factorization_mul_apply_of_coprime hab]; rw [← primeFactorsList_count_eq]; rw [← primeFactorsList_count_eq]; rw [count_eq_zero_of_not_mem (coprime_primeFactorsList_disjoint hab hpa)]; rw [add_zero]

中文:
定理 factorization_eq_of_coprime_left
  结论: {p a b : 自然数} (hab : Coprime a b)
  证明: by
  rw [factorization_mul_apply_of_coprime hab]; rw [← primeFactorsList_count_eq]; rw [← primeFactorsList_count_eq]; rw [count_eq_zero_of_not_mem (coprime_primeFactorsList_disjoint hab hpa)]; rw [add_zero]

Depends on / 依赖: add_zero, coprime_primeFactorsList_disjoint, count_eq_zero_of_not_mem, factorization_mul_apply_of_coprime, primeFactorsList_count_eq
-/
theorem factorization_eq_of_coprime_left {p a b : Nat} (hab : Coprime a b)
    (hpa : p in a.primeFactorsList) : (a * b).factorization p = a.factorization p := by
  rw [factorization_mul_apply_of_coprime hab]; rw [← primeFactorsList_count_eq]; rw [← primeFactorsList_count_eq]; rw [count_eq_zero_of_not_mem (coprime_primeFactorsList_disjoint hab hpa)]; rw [add_zero]

/--
theorem `factorization_eq_of_coprime_right` / 定理 `factorization_eq_of_coprime_right`

English:
theorem factorization_eq_of_coprime_right
  statement: {p a b : Nat} (hab : Coprime a b)
  proof: by
  rw [mul_comm]
  exact factorization_eq_of_coprime_left (coprime_comm.mp hab) hpb

中文:
定理 factorization_eq_of_coprime_right
  结论: {p a b : 自然数} (hab : Coprime a b)
  证明: by
  rw [mul_comm]
  exact factorization_eq_of_coprime_left (coprime_comm.mp hab) hpb

Depends on / 依赖: coprime_comm, coprime_comm.mp, factorization_eq_of_coprime_left, mul_comm
-/
theorem factorization_eq_of_coprime_right {p a b : Nat} (hab : Coprime a b)
    (hpb : p in b.primeFactorsList) : (a * b).factorization p = b.factorization p := by
  rw [mul_comm]
  exact factorization_eq_of_coprime_left (coprime_comm.mp hab) hpb

/--
theorem `eq_iff_prime_padicValNat_eq` / 定理 `eq_iff_prime_padicValNat_eq`

English:
theorem eq_iff_prime_padicValNat_eq
  given: (a b : Nat) (ha : a != 0) (hb : b != 0)
  proof: by
  constructor
  · rintro rfl
    simp
  · intro h
    refine eq_of_factorization_eq ha hb fun p => ?_
    by_cases pp : p.Prime
    · simp [factorization_def, pp, h p pp]
    · simp [factorization_eq_zero_of_not_prime, pp]

中文:
定理 eq_iff_prime_padicVal自然数_eq
  条件: (a b : 自然数) (ha : a != 0) (hb : b != 0)
  证明: by
  constructor
  · rintro rfl
    simp
  · intro h
    refine eq_of_factorization_eq ha hb fun p => ?_
    by_cases pp : p.Prime
    · simp [factorization_def, pp, h p pp]
    · simp [factorization_eq_zero_of_not_prime, pp]

Depends on / 依赖: eq_of_factorization_eq, factorization_def, factorization_eq_zero_of_not_prime, p.Prime
-/
theorem eq_iff_prime_padicValNat_eq (a b : Nat) (ha : a != 0) (hb : b != 0) :
    a = b ↔ forall p : Nat, p.Prime -> padicValNat p a = padicValNat p b := by
  constructor
  · rintro rfl
    simp
  · intro h
    refine eq_of_factorization_eq ha hb fun p => ?_
    by_cases pp : p.Prime
    · simp [factorization_def, pp, h p pp]
    · simp [factorization_eq_zero_of_not_prime, pp]

/--
theorem `prod_pow_prime_padicValNat` / 定理 `prod_pow_prime_padicValNat`

English:
theorem prod_pow_prime_padicValNat
  given: (n : Nat) (hn : n != 0) (m : Nat) (pr : n < m)
  proof: by
  nth_rw 2 [← prod_factorization_pow_eq_self hn]
  rw [eq_comm]
  apply Finset.prod_subset_one_on_sdiff
· exact fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_range.2 pr.trans_le'
      le_of_mem_primeFactors hp, prime_of_mem_primeFactors hp⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sdif

中文:
定理 prod_pow_prime_padicVal自然数
  条件: (n : 自然数) (hn : n != 0) (m : 自然数) (pr : n < m)
  证明: by
  nth_rw 2 [← prod_factorization_pow_eq_self hn]
  rw [eq_comm]
  apply Finset.prod_subset_one_on_sdiff
· exact fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_range.2 pr.trans_le'
      le_of_mem_primeFactors hp, prime_of_mem_primeFactors hp⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sdif

Depends on / 依赖: Finset, Finset.mem_filter.mp, Finset.mem_filter.mpr, Finset.mem_range, Finset.mem_sdiff.mp, Finset.prod_subset_one_on_sdiff, Finsupp, Finsupp.notMem_support_iff.mp, eq_comm, factorization_def, le_of_mem_primeFactors, mem_filter, mem_range, mem_sdiff, notMem_support_iff, nth_rw, pr.trans_le, prime_of_mem_primeFactors, prod_factorization_pow_eq_self, prod_subset_one_on_sdiff
-/
theorem prod_pow_prime_padicValNat (n : Nat) (hn : n != 0) (m : Nat) (pr : n < m) :
    ∏ p in range m with p.Prime, p ^ padicValNat p n = n := by
  nth_rw 2 [← prod_factorization_pow_eq_self hn]
  rw [eq_comm]
  apply Finset.prod_subset_one_on_sdiff
· exact fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_range.2 pr.trans_le'
      le_of_mem_primeFactors hp, prime_of_mem_primeFactors hp⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
    rw [← factorization_def n (Finset.mem_filter.mp hp1).2]
    simp [Finsupp.notMem_support_iff.mp hp2]
  · intro p hp
    simp [factorization_def n (prime_of_mem_primeFactors hp)]

/--
theorem `prod_primeFactors_pow_factorization` / 定理 `prod_primeFactors_pow_factorization`

English:
theorem prod_primeFactors_pow_factorization
  given: (hn : n != 0)
  proof: .symm.trans prod_factorization_eq_prod_primeFactors _ prod_factorization_pow_eq_self hn

中文:
定理 prod_primeFactors_pow_factorization
  条件: (hn : n != 0)
  证明: .symm.trans prod_factorization_eq_prod_primeFactors _ prod_factorization_pow_eq_self hn

Depends on / 依赖: prod_factorization_eq_prod_primeFactors, prod_factorization_pow_eq_self, symm.trans
-/
theorem prod_primeFactors_pow_factorization (hn : n != 0) :
    n = ∏ p in n.primeFactors, p ^ n.factorization p :=
.symm.trans prod_factorization_eq_prod_primeFactors _ prod_factorization_pow_eq_self hn

/--
lemma `prod_primeFactors_coe_pow_factorization` / 引理 `prod_primeFactors_coe_pow_factorization`

English:
lemma prod_primeFactors_coe_pow_factorization
  given: (hn : n != 0)
  proof: by
  simpa using prod_primeFactors_pow_factorization hn

@[deprecated (since := "2026-06-24")]
alias prod_pow_primeFactors_factorization := prod_primeFactors_coe_pow_factorization

中文:
引理 prod_primeFactors_coe_pow_factorization
  条件: (hn : n != 0)
  证明: by
  simpa using prod_primeFactors_pow_factorization hn

@[deprecated (since := "2026-06-24")]
alias prod_pow_primeFactors_factorization := prod_primeFactors_coe_pow_factorization

Depends on / 依赖: prod_primeFactors_pow_factorization
-/
lemma prod_primeFactors_coe_pow_factorization (hn : n != 0) :
    n = ∏ (p : n.primeFactors), (p : Nat) ^ (n.factorization p) := by
  simpa using prod_primeFactors_pow_factorization hn

@[deprecated (since := "2026-06-24")]
alias prod_pow_primeFactors_factorization := prod_primeFactors_coe_pow_factorization

/--
lemma `pairwise_coprime_pow_primeFactors_factorization` / 引理 `pairwise_coprime_pow_primeFactors_factorization`

English:
lemma pairwise_coprime_pow_primeFactors_factorization
  proof: by
  intro p1 p2 hp
  refine Nat.Coprime.pow (n.factorization p1) (n.factorization p2) ?_
refine (Nat.coprime_primes ?_ ?_).mpr Subtype.coe_ne_coe.mpr hp
  · exact Nat.prime_of_mem_primeFactors p1.2
  · exact Nat.prime_of_mem_primeFactors p2.2

中文:
引理 pairwise_coprime_pow_primeFactors_factorization
  证明: by
  intro p1 p2 hp
  refine Nat.Coprime.pow (n.factorization p1) (n.factorization p2) ?_
refine (Nat.coprime_primes ?_ ?_).mpr Subtype.coe_ne_coe.mpr hp
  · exact Nat.prime_of_mem_primeFactors p1.2
  · exact Nat.prime_of_mem_primeFactors p2.2

Depends on / 依赖: Coprime, Nat.Coprime.pow, Nat.coprime_primes, Nat.prime_of_mem_primeFactors, Subtype, Subtype.coe_ne_coe.mpr, coe_ne_coe, coprime_primes, factorization, n.factorization, prime_of_mem_primeFactors
-/
lemma pairwise_coprime_pow_primeFactors_factorization :
    Pairwise (Function.onFun Nat.Coprime fun (p : n.primeFactors) => p ^ n.factorization p) := by
  intro p1 p2 hp
  refine Nat.Coprime.pow (n.factorization p1) (n.factorization p2) ?_
refine (Nat.coprime_primes ?_ ?_).mpr Subtype.coe_ne_coe.mpr hp
  · exact Nat.prime_of_mem_primeFactors p1.2
  · exact Nat.prime_of_mem_primeFactors p2.2

/--
theorem `dvd_prod_primeFactors_pow_self` / 定理 `dvd_prod_primeFactors_pow_self`

English:
theorem dvd_prod_primeFactors_pow_self
  given: {n : Nat} (hn : n != 0)
  proof: by
  nth_rw 1 [← Finset.prod_pow, prod_primeFactors_pow_factorization hn]
  refine prod_dvd_prod_of_dvd _ _ fun i hi => pow_dvd_pow i ?_
  grw [n.factorization_def <| prime_of_mem_primeFactors hi, padicValNat_le_self]

中文:
定理 dvd_prod_primeFactors_pow_self
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  nth_rw 1 [← Finset.prod_pow, prod_primeFactors_pow_factorization hn]
  refine prod_dvd_prod_of_dvd _ _ fun i hi => pow_dvd_pow i ?_
  grw [n.factorization_def <| prime_of_mem_primeFactors hi, padicValNat_le_self]

Depends on / 依赖: Finset, Finset.prod_pow, factorization_def, n.factorization_def, nth_rw, padicValNat_le_self, pow_dvd_pow, prime_of_mem_primeFactors, prod_dvd_prod_of_dvd, prod_pow, prod_primeFactors_pow_factorization
-/
theorem dvd_prod_primeFactors_pow_self {n : Nat} (hn : n != 0) :
    n ∣ (∏ p in n.primeFactors, p) ^ n := by
  nth_rw 1 [← Finset.prod_pow, prod_primeFactors_pow_factorization hn]
  refine prod_dvd_prod_of_dvd _ _ fun i hi => pow_dvd_pow i ?_
  grw [n.factorization_def <| prime_of_mem_primeFactors hi, padicValNat_le_self]

/--
theorem `dvd_pow_self_iff` / 定理 `dvd_pow_self_iff`

English:
theorem dvd_pow_self_iff
  given: {n k : Nat} (hn : n != 0) (hk : k != 0)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · grw [← Nat.primeFactors_pow k hn, Nat.primeFactors_mono h <| pow_ne_zero n hk]
  · grw [dvd_prod_primeFactors_pow_self hn, prod_dvd_prod_of_subset _ _ _ h, prod_primeFactors_dvd]

中文:
定理 dvd_pow_self_iff
  条件: {n k : 自然数} (hn : n != 0) (hk : k != 0)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · grw [← Nat.primeFactors_pow k hn, Nat.primeFactors_mono h <| pow_ne_zero n hk]
  · grw [dvd_prod_primeFactors_pow_self hn, prod_dvd_prod_of_subset _ _ _ h, prod_primeFactors_dvd]

Depends on / 依赖: Nat.primeFactors_mono, Nat.primeFactors_pow, dvd_prod_primeFactors_pow_self, pow_ne_zero, primeFactors_mono, primeFactors_pow, prod_dvd_prod_of_subset, prod_primeFactors_dvd
-/
theorem dvd_pow_self_iff {n k : Nat} (hn : n != 0) (hk : k != 0) :
    n ∣ k ^ n ↔ n.primeFactors subseteq k.primeFactors := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · grw [← Nat.primeFactors_pow k hn, Nat.primeFactors_mono h <| pow_ne_zero n hk]
  · grw [dvd_prod_primeFactors_pow_self hn, prod_dvd_prod_of_subset _ _ _ h, prod_primeFactors_dvd]

/--
theorem `exists_dvd_pow_iff` / 定理 `exists_dvd_pow_iff`

English:
theorem exists_dvd_pow_iff
  given: {n k : Nat} (hn : n != 0) (hk : k != 0)
  proof: by
.mpr h⟩⟩ refine ⟨fun ⟨m, h⟩ => ?_, fun h => ⟨n, dvd_pow_self_iff hn hk
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp_all
  rw [← Nat.primeFactors_pow k hm]
exact Nat.primeFactors_mono h pow_ne_zero m hk

中文:
定理 存在_dvd_pow_iff
  条件: {n k : 自然数} (hn : n != 0) (hk : k != 0)
  证明: by
.mpr h⟩⟩ refine ⟨fun ⟨m, h⟩ => ?_, fun h => ⟨n, dvd_pow_self_iff hn hk
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp_all
  rw [← Nat.primeFactors_pow k hm]
exact Nat.primeFactors_mono h pow_ne_zero m hk

Depends on / 依赖: Nat.primeFactors_mono, Nat.primeFactors_pow, dvd_pow_self_iff, eq_or_ne, pow_ne_zero, primeFactors_mono, primeFactors_pow
-/
theorem exists_dvd_pow_iff {n k : Nat} (hn : n != 0) (hk : k != 0) :
    (exists m, n ∣ k ^ m) ↔ n.primeFactors subseteq k.primeFactors := by
.mpr h⟩⟩ refine ⟨fun ⟨m, h⟩ => ?_, fun h => ⟨n, dvd_pow_self_iff hn hk
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp_all
  rw [← Nat.primeFactors_pow k hm]
exact Nat.primeFactors_mono h pow_ne_zero m hk

/-! ### Lemmas about factorizations of particular functions -/

/--
theorem `card_multiples` / 定理 `card_multiples`

English:
theorem card_multiples
  given: (n p : Nat)
  statement: #{e in range n | p ∣ e + 1} = n / p
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    simp [Nat.succ_div, add_ite, add_zero, Finset.range_add_one, filter_insert, apply_ite card,
      card_insert_of_notMem, hn]

中文:
定理 card_multiples
  条件: (n p : 自然数)
  结论: #{e in range n | p ∣ e + 1} = n / p
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    simp [Nat.succ_div, add_ite, add_zero, Finset.range_add_one, filter_insert, apply_ite card,
      card_insert_of_notMem, hn]

Depends on / 依赖: Finset, Finset.range_add_one, Nat.succ_div, add_ite, add_zero, apply_ite, card_insert_of_notMem, filter_insert, range_add_one, succ_div
-/
theorem card_multiples (n p : Nat) : #{e in range n | p ∣ e + 1} = n / p := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp [Nat.succ_div, add_ite, add_zero, Finset.range_add_one, filter_insert, apply_ite card,
      card_insert_of_notMem, hn]

/--
theorem `Ioc_filter_dvd_card_eq_div` / 定理 `Ioc_filter_dvd_card_eq_div`

English:
theorem Ioc_filter_dvd_card_eq_div
  given: (n p : Nat)
  statement: #{x in Ioc 0 n | p ∣ x} = n / p
  proof: by
  induction n <;> simp [Nat.succ_div, add_ite, ← insert_Ioc_right_eq_Ioc_add_one, filter_insert,
    apply_ite card, *]

中文:
定理 Ioc_filter_dvd_card_eq_div
  条件: (n p : 自然数)
  结论: #{x in 左开右闭区间 0 n | p ∣ x} = n / p
  证明: by
  induction n <;> simp [Nat.succ_div, add_ite, ← insert_Ioc_right_eq_Ioc_add_one, filter_insert,
    apply_ite card, *]

Depends on / 依赖: Nat.succ_div, add_ite, apply_ite, filter_insert, insert_Ioc_right_eq_Ioc_add_one, succ_div
-/
theorem Ioc_filter_dvd_card_eq_div (n p : Nat) : #{x in Ioc 0 n | p ∣ x} = n / p := by
  induction n <;> simp [Nat.succ_div, add_ite, ← insert_Ioc_right_eq_Ioc_add_one, filter_insert,
    apply_ite card, *]

/--
lemma `card_multiples'` / 引理 `card_multiples'`

English:
lemma card_multiples'
  given: (N n : Nat)
  statement: #{k in range N.succ | k != 0 ∧ n ∣ k} = N / n
  proof: by
  induction N with
  | zero => simp [Finset.filter_false_of_mem]
  | succ N ih =>
    rw [Finset.range_add_one]; rw [Finset.filter_insert]
    by_cases h : n ∣ N.succ
    · simp [h, succ_div_of_dvd, ih]
    · simp [h, succ_div_of_not_dvd, ih]

中文:
引理 card_multiples'
  条件: (N n : 自然数)
  结论: #{k in range N.succ | k != 0 ∧ n ∣ k} = N / n
  证明: by
  induction N with
  | zero => simp [Finset.filter_false_of_mem]
  | succ N ih =>
    rw [Finset.range_add_one]; rw [Finset.filter_insert]
    by_cases h : n ∣ N.succ
    · simp [h, succ_div_of_dvd, ih]
    · simp [h, succ_div_of_not_dvd, ih]

Depends on / 依赖: Finset, Finset.filter_false_of_mem, Finset.filter_insert, Finset.range_add_one, N.succ, filter_false_of_mem, filter_insert, range_add_one, succ_div_of_dvd, succ_div_of_not_dvd
-/
lemma card_multiples' (N n : Nat) : #{k in range N.succ | k != 0 ∧ n ∣ k} = N / n := by
  induction N with
  | zero => simp [Finset.filter_false_of_mem]
  | succ N ih =>
    rw [Finset.range_add_one]; rw [Finset.filter_insert]
    by_cases h : n ∣ N.succ
    · simp [h, succ_div_of_dvd, ih]
    · simp [h, succ_div_of_not_dvd, ih]

/--
theorem `exists_eq_pow_of_exponent_coprime_of_pow_eq_pow` / 定理 `exists_eq_pow_of_exponent_coprime_of_pow_eq_pow`

English:
theorem exists_eq_pow_of_exponent_coprime_of_pow_eq_pow
  proof: by
  by_cases ha0 : a = 0
  · symm at h
    by_cases hm0 : m = 0
    · simp_all
    · use 0
      simp_all
  by_cases hn0 : n = 0
  · use b
    simp_all
  let factors := a.factorization.mapRange (· / n) (Nat.zero_div n)
  set c := factors.prod (· ^ ·) with hc
  use c
  suffices ha : a = c ^ n by
   

中文:
定理 存在_eq_pow_of_exponent_coprime_of_pow_eq_pow
  证明: by
  by_cases ha0 : a = 0
  · symm at h
    by_cases hm0 : m = 0
    · simp_all
    · use 0
      simp_all
  by_cases hn0 : n = 0
  · use b
    simp_all
  let factors := a.factorization.mapRange (· / n) (Nat.zero_div n)
  set c := factors.prod (· ^ ·) with hc
  use c
  suffices ha : a = c ^ n by
   

Depends on / 依赖: Finsupp, Finsupp.supp, Nat.pow_left_injective, Nat.pow_right_comm, Nat.zero_div, a.factorization.mapRange, eq_of_factorization_eq, factorization, factors, factors.prod, factors.support, mapRange, pow_left_injective, pow_right_comm, prime_of_mem_primeFactors, support, zero_div
-/
theorem exists_eq_pow_of_exponent_coprime_of_pow_eq_pow
    {a b m n : Nat} (hmn : m.Coprime n) (h : a ^ m = b ^ n) :
    exists c, a = c ^ n ∧ b = c ^ m := by
  by_cases ha0 : a = 0
  · symm at h
    by_cases hm0 : m = 0
    · simp_all
    · use 0
      simp_all
  by_cases hn0 : n = 0
  · use b
    simp_all
  let factors := a.factorization.mapRange (· / n) (Nat.zero_div n)
  set c := factors.prod (· ^ ·) with hc
  use c
  suffices ha : a = c ^ n by
    refine ⟨ha, ?_⟩
    apply Nat.pow_left_injective hn0
    simp [← h, ha, Nat.pow_right_comm]
  apply eq_of_factorization_eq ha0 (by simp [c, factors])
  intro p
  have foo (p) (hp : p in factors.support) : Prime p :=
    prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  rw [factorization_pow]; rw [hc]; rw [prod_pow_factorization_eq_self foo]
  suffices n ∣ a.factorization p by
    simp [factors, Nat.mul_div_cancel' this]
  refine hmn.symm.dvd_of_dvd_mul_left ⟨b.factorization p, ?_⟩
  simpa using congr(factorization $h p)

/--
theorem `exists_eq_pow_of_pow_eq_pow` / 定理 `exists_eq_pow_of_pow_eq_pow`

English:
theorem exists_eq_pow_of_pow_eq_pow
  proof: gcd m n; exists c, a = c ^ (n / g) ∧ b = c ^ (m / g) := by
  set g := gcd m n
  let m' := m / gcd m n
  let n' := n / gcd m n
  have coprime : m'.Coprime n' := by
    rcases hmn with hm | hn
    · exact gcd_div_gcd_div_gcd_of_pos_left (zero_lt_of_ne_zero hm)
    · exact gcd_div_gcd_div_gcd_of_pos_ri

中文:
定理 存在_eq_pow_of_pow_eq_pow
  证明: gcd m n; exists c, a = c ^ (n / g) ∧ b = c ^ (m / g) := by
  set g := gcd m n
  let m' := m / gcd m n
  let n' := n / gcd m n
  have coprime : m'.Coprime n' := by
    rcases hmn with hm | hn
    · exact gcd_div_gcd_div_gcd_of_pos_left (zero_lt_of_ne_zero hm)
    · exact gcd_div_gcd_div_gcd_of_pos_ri

Depends on / 依赖: Coprime, Nat.div_mul_cancel, conv_lhs, conv_rhs, coprime, div_mul_cancel, gcd_d, gcd_div_gcd_div_gcd_of_pos_left, gcd_div_gcd_div_gcd_of_pos_right, gcd_dvd_left, pow_eq, zero_lt_of_ne_zero
-/
theorem exists_eq_pow_of_pow_eq_pow
    {a b m n : Nat} (hmn : m != 0 ∨ n != 0) (h : a ^ m = b ^ n) :
    letI g := gcd m n; exists c, a = c ^ (n / g) ∧ b = c ^ (m / g) := by
  set g := gcd m n
  let m' := m / gcd m n
  let n' := n / gcd m n
  have coprime : m'.Coprime n' := by
    rcases hmn with hm | hn
    · exact gcd_div_gcd_div_gcd_of_pos_left (zero_lt_of_ne_zero hm)
    · exact gcd_div_gcd_div_gcd_of_pos_right (zero_lt_of_ne_zero hn)
  have pow_eq : a ^ m' = b ^ n' := by
    conv_lhs at h => rw [show m = m' * g from (Nat.div_mul_cancel (gcd_dvd_left m n)).symm]
    conv_rhs at h => rw [show n = n' * g from (Nat.div_mul_cancel (gcd_dvd_right m n)).symm]
    rw [pow_mul]; rw [pow_mul] at h
    have : g != 0 := by
      rcases hmn with hm | hn
      · exact gcd_ne_zero_left hm
      · exact gcd_ne_zero_right hn
    exact Nat.pow_left_injective this h
  exact exists_eq_pow_of_exponent_coprime_of_pow_eq_pow coprime pow_eq

end Nat
