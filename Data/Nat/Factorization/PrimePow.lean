/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Pow
public import Mathlib.NumberTheory.Divisors

/-!
# Prime powers and factorizations

This file deals with factorizations of prime powers.
-/

@[expose] public section


/--
theorem `IsPrimePow.minFac_pow_factorization_eq` / 定理 `IsPrimePow.minFac_pow_factorization_eq`

English:
theorem IsPrimePow.minFac_pow_factorization_eq
  given: {n : Nat} (hn : IsPrimePow n)
  proof: by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  rw [← Nat.prime_iff] at hp
  rw [hp.pow_minFac hk.ne']; rw [hp.factorization_pow]; rw [Finsupp.single_eq_same]

中文:
定理 IsPrimePow.minFac_pow_factorization_eq
  条件: {n : 自然数} (hn : IsPrimePow n)
  证明: by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  rw [← Nat.prime_iff] at hp
  rw [hp.pow_minFac hk.ne']; rw [hp.factorization_pow]; rw [Finsupp.single_eq_same]

Depends on / 依赖: Finsupp, Finsupp.single_eq_same, Nat.prime_iff, factorization_pow, hk.ne, hp.factorization_pow, hp.pow_minFac, pow_minFac, prime_iff, single_eq_same
-/
theorem IsPrimePow.minFac_pow_factorization_eq {n : Nat} (hn : IsPrimePow n) :
    n.minFac ^ n.factorization n.minFac = n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  rw [← Nat.prime_iff] at hp
  rw [hp.pow_minFac hk.ne']; rw [hp.factorization_pow]; rw [Finsupp.single_eq_same]

/--
theorem `isPrimePow_of_minFac_pow_factorization_eq` / 定理 `isPrimePow_of_minFac_pow_factorization_eq`

English:
theorem isPrimePow_of_minFac_pow_factorization_eq
  statement: {n : Nat}
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp_all
  refine ⟨_, _, (Nat.minFac_prime hn).prime, ?_, h⟩
  simp [pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization, hn',
    Nat.minFac_prime hn, Nat.minFac_dvd]

中文:
定理 isPrimePow_of_minFac_pow_factorization_eq
  结论: {n : 自然数}
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp_all
  refine ⟨_, _, (Nat.minFac_prime hn).prime, ?_, h⟩
  simp [pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization, hn',
    Nat.minFac_prime hn, Nat.minFac_dvd]

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff, Nat.minFac_dvd, Nat.minFac_prime, Nat.support_factorization, eq_or_ne, mem_support_iff, minFac_dvd, minFac_prime, pos_iff_ne_zero, support_factorization
-/
theorem isPrimePow_of_minFac_pow_factorization_eq {n : Nat}
    (h : n.minFac ^ n.factorization n.minFac = n) (hn : n != 1) : IsPrimePow n := by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp_all
  refine ⟨_, _, (Nat.minFac_prime hn).prime, ?_, h⟩
  simp [pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization, hn',
    Nat.minFac_prime hn, Nat.minFac_dvd]

/--
theorem `isPrimePow_iff_minFac_pow_factorization_eq` / 定理 `isPrimePow_iff_minFac_pow_factorization_eq`

English:
theorem isPrimePow_iff_minFac_pow_factorization_eq
  given: {n : Nat} (hn : n != 1)
  proof: ⟨fun h => h.minFac_pow_factorization_eq, fun h => isPrimePow_of_minFac_pow_factorization_eq h hn⟩

中文:
定理 isPrimePow_iff_minFac_pow_factorization_eq
  条件: {n : 自然数} (hn : n != 1)
  证明: ⟨fun h => h.minFac_pow_factorization_eq, fun h => isPrimePow_of_minFac_pow_factorization_eq h hn⟩

Depends on / 依赖: h.minFac_pow_factorization_eq, isPrimePow_of_minFac_pow_factorization_eq, minFac_pow_factorization_eq
-/
theorem isPrimePow_iff_minFac_pow_factorization_eq {n : Nat} (hn : n != 1) :
    IsPrimePow n ↔ n.minFac ^ n.factorization n.minFac = n :=
  ⟨fun h => h.minFac_pow_factorization_eq, fun h => isPrimePow_of_minFac_pow_factorization_eq h hn⟩

/--
theorem `isPrimePow_iff_factorization_eq_single` / 定理 `isPrimePow_iff_factorization_eq_single`

English:
theorem isPrimePow_iff_factorization_eq_single
  given: {n : Nat}
  proof: by
  rw [isPrimePow_nat_iff]
  refine exists₂_congr fun p k => ?_
  constructor
  · rintro ⟨hp, hk, hn⟩
    exact ⟨hk, by rw [← hn, Nat.Prime.factorization_pow hp]⟩
  · rintro ⟨hk, hn⟩
    have hn0 : n != 0 := by
      rintro rfl
      simp_all only [Finsupp.single_eq_zero, eq_comm, Nat.factorization_zero, hk.ne']
    rw [Nat.eq_pow_of_factorization_eq_single hn0 hn]
exact ⟨Nat.prime_of_mem_primeFactors
      Finsupp.mem_support_iff.2 (by simp [hn, hk.ne'] : n.factorization p != 0), hk, rfl⟩

中文:
定理 isPrimePow_iff_factorization_eq_single
  条件: {n : 自然数}
  证明: by
  rw [isPrimePow_nat_iff]
  refine exists₂_congr fun p k => ?_
  constructor
  · rintro ⟨hp, hk, hn⟩
    exact ⟨hk, by rw [← hn, Nat.Prime.factorization_pow hp]⟩
  · rintro ⟨hk, hn⟩
    have hn0 : n != 0 := by
      rintro rfl
      simp_all only [Finsupp.single_eq_zero, eq_comm, Nat.factorization_zero, hk.ne']
    rw [Nat.eq_pow_of_factorization_eq_single hn0 hn]
exact ⟨Nat.prime_of_mem_primeFactors
      Finsupp.mem_support_iff.2 (by simp [hn, hk.ne'] : n.factorization p != 0), hk, rfl⟩

Depends on / 依赖: Finsupp, Finsupp.mem_support_iff, Finsupp.single_eq_zero, Nat.Prime.factorization_pow, Nat.eq_pow_of_factorization_eq_single, Nat.factorization_zero, Nat.prime_of_mem_primeFactors, eq_comm, eq_pow_of_factorization_eq_single, factorization, factorization_pow, factorization_zero, hk.ne, isPrimePow_nat_iff, mem_support_iff, n.factorization, prime_of_mem_primeFactors, single_eq_zero
-/
theorem isPrimePow_iff_factorization_eq_single {n : Nat} :
    IsPrimePow n ↔ exists p k : Nat, 0 < k ∧ n.factorization = Finsupp.single p k := by
  rw [isPrimePow_nat_iff]
  refine exists₂_congr fun p k => ?_
  constructor
  · rintro ⟨hp, hk, hn⟩
    exact ⟨hk, by rw [← hn, Nat.Prime.factorization_pow hp]⟩
  · rintro ⟨hk, hn⟩
    have hn0 : n != 0 := by
      rintro rfl
      simp_all only [Finsupp.single_eq_zero, eq_comm, Nat.factorization_zero, hk.ne']
    rw [Nat.eq_pow_of_factorization_eq_single hn0 hn]
exact ⟨Nat.prime_of_mem_primeFactors
      Finsupp.mem_support_iff.2 (by simp [hn, hk.ne'] : n.factorization p != 0), hk, rfl⟩

/--
theorem `isPrimePow_iff_card_primeFactors_eq_one` / 定理 `isPrimePow_iff_card_primeFactors_eq_one`

English:
theorem isPrimePow_iff_card_primeFactors_eq_one
  given: {n : Nat}
  proof: by
  simp_rw [isPrimePow_iff_factorization_eq_single, ← Nat.support_factorization,
    Finsupp.card_support_eq_one', pos_iff_ne_zero]

中文:
定理 isPrimePow_iff_card_primeFactors_eq_one
  条件: {n : 自然数}
  证明: by
  simp_rw [isPrimePow_iff_factorization_eq_single, ← Nat.support_factorization,
    Finsupp.card_support_eq_one', pos_iff_ne_zero]

Depends on / 依赖: Finsupp, Finsupp.card_support_eq_one, Nat.support_factorization, card_support_eq_one, isPrimePow_iff_factorization_eq_single, pos_iff_ne_zero, simp_rw, support_factorization
-/
theorem isPrimePow_iff_card_primeFactors_eq_one {n : Nat} :
    IsPrimePow n ↔ n.primeFactors.card = 1 := by
  simp_rw [isPrimePow_iff_factorization_eq_single, ← Nat.support_factorization,
    Finsupp.card_support_eq_one', pos_iff_ne_zero]

/--
theorem `Nat.not_isPrimePow_iff_nontrivial_of_two_le` / 定理 `Nat.not_isPrimePow_iff_nontrivial_of_two_le`

English:
theorem Nat.not_isPrimePow_iff_nontrivial_of_two_le
  given: {n : Nat} (hn : 2 <= n)
  proof: by
  rw [isPrimePow_iff_card_primeFactors_eq_one]; rw [← Finset.one_lt_card_iff_nontrivial]
  grind [primeFactors_eq_empty]

中文:
定理 自然数.not_isPrimePow_iff_nontrivial_of_two_le
  条件: {n : 自然数} (hn : 2 <= n)
  证明: by
  rw [isPrimePow_iff_card_primeFactors_eq_one]; rw [← Finset.one_lt_card_iff_nontrivial]
  grind [primeFactors_eq_empty]

Depends on / 依赖: Finset, Finset.one_lt_card_iff_nontrivial, isPrimePow_iff_card_primeFactors_eq_one, one_lt_card_iff_nontrivial, primeFactors_eq_empty
-/
theorem Nat.not_isPrimePow_iff_nontrivial_of_two_le {n : Nat} (hn : 2 <= n) :
    ¬ IsPrimePow n ↔ n.primeFactors.Nontrivial := by
  rw [isPrimePow_iff_card_primeFactors_eq_one]; rw [← Finset.one_lt_card_iff_nontrivial]
  grind [primeFactors_eq_empty]

/--
theorem `IsPrimePow.exists_ordCompl_eq_one` / 定理 `IsPrimePow.exists_ordCompl_eq_one`

English:
theorem IsPrimePow.exists_ordCompl_eq_one
  given: {n : Nat} (h : IsPrimePow n)
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn0); · cases not_isPrimePow_zero h
  rcases isPrimePow_iff_factorization_eq_single.mp h with ⟨p, k, hk0, h1⟩
  rcases em' p.Prime with (pp | pp)
  · refine absurd ?_ hk0.ne'
    simp [← Nat.factorization_eq_zero_of_not_prime n pp, h1]
  refine ⟨p, pp, ?_⟩
  refine Nat.eq_of_factorization_eq (Nat.ordCompl_pos p hn0).ne' (by simp) fun q => ?_
  rw [Nat.factorization_ordCompl n p]; rw [h1]
  simp

中文:
定理 IsPrimePow.存在_ordCompl_eq_one
  条件: {n : 自然数} (h : IsPrimePow n)
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn0); · cases not_isPrimePow_zero h
  rcases isPrimePow_iff_factorization_eq_single.mp h with ⟨p, k, hk0, h1⟩
  rcases em' p.Prime with (pp | pp)
  · refine absurd ?_ hk0.ne'
    simp [← Nat.factorization_eq_zero_of_not_prime n pp, h1]
  refine ⟨p, pp, ?_⟩
  refine Nat.eq_of_factorization_eq (Nat.ordCompl_pos p hn0).ne' (by simp) fun q => ?_
  rw [Nat.factorization_ordCompl n p]; rw [h1]
  simp

Depends on / 依赖: Nat.eq_of_factorization_eq, Nat.factorization_eq_zero_of_not_prime, Nat.factorization_ordCompl, Nat.ordCompl_pos, absurd, eq_of_factorization_eq, eq_or_ne, factorization_eq_zero_of_not_prime, factorization_ordCompl, hk0.ne, isPrimePow_iff_factorization_eq_single, isPrimePow_iff_factorization_eq_single.mp, not_isPrimePow_zero, ordCompl_pos, p.Prime
-/
theorem IsPrimePow.exists_ordCompl_eq_one {n : Nat} (h : IsPrimePow n) :
    exists p : Nat, p.Prime ∧ ordCompl[p] n = 1 := by
  rcases eq_or_ne n 0 with (rfl | hn0); · cases not_isPrimePow_zero h
  rcases isPrimePow_iff_factorization_eq_single.mp h with ⟨p, k, hk0, h1⟩
  rcases em' p.Prime with (pp | pp)
  · refine absurd ?_ hk0.ne'
    simp [← Nat.factorization_eq_zero_of_not_prime n pp, h1]
  refine ⟨p, pp, ?_⟩
  refine Nat.eq_of_factorization_eq (Nat.ordCompl_pos p hn0).ne' (by simp) fun q => ?_
  rw [Nat.factorization_ordCompl n p]; rw [h1]
  simp

/--
theorem `exists_ordCompl_eq_one_iff_isPrimePow` / 定理 `exists_ordCompl_eq_one_iff_isPrimePow`

English:
theorem exists_ordCompl_eq_one_iff_isPrimePow
  given: {n : Nat} (hn : n != 1)
  proof: by
  refine ⟨fun h => IsPrimePow.exists_ordCompl_eq_one h, fun h => ?_⟩
  rcases h with ⟨p, pp, h⟩
  rw [isPrimePow_nat_iff]
  rw [← Nat.eq_of_dvd_of_div_eq_one (Nat.ordProj_dvd n p) h] at hn ⊢
  refine ⟨p, n.factorization p, pp, ?_, by simp⟩
  contrapose! hn
  simp [Nat.le_zero.1 hn]

中文:
定理 存在_ordCompl_eq_one_iff_isPrimePow
  条件: {n : 自然数} (hn : n != 1)
  证明: by
  refine ⟨fun h => IsPrimePow.exists_ordCompl_eq_one h, fun h => ?_⟩
  rcases h with ⟨p, pp, h⟩
  rw [isPrimePow_nat_iff]
  rw [← Nat.eq_of_dvd_of_div_eq_one (Nat.ordProj_dvd n p) h] at hn ⊢
  refine ⟨p, n.factorization p, pp, ?_, by simp⟩
  contrapose! hn
  simp [Nat.le_zero.1 hn]

Depends on / 依赖: IsPrimePow, IsPrimePow.exists_ordCompl_eq_one, Nat.eq_of_dvd_of_div_eq_one, Nat.le_zero, Nat.ordProj_dvd, contrapose, eq_of_dvd_of_div_eq_one, exists_ordCompl_eq_one, factorization, isPrimePow_nat_iff, le_zero, n.factorization, ordProj_dvd
-/
theorem exists_ordCompl_eq_one_iff_isPrimePow {n : Nat} (hn : n != 1) :
    IsPrimePow n ↔ exists p : Nat, p.Prime ∧ ordCompl[p] n = 1 := by
  refine ⟨fun h => IsPrimePow.exists_ordCompl_eq_one h, fun h => ?_⟩
  rcases h with ⟨p, pp, h⟩
  rw [isPrimePow_nat_iff]
  rw [← Nat.eq_of_dvd_of_div_eq_one (Nat.ordProj_dvd n p) h] at hn ⊢
  refine ⟨p, n.factorization p, pp, ?_, by simp⟩
  contrapose! hn
  simp [Nat.le_zero.1 hn]

/--
theorem `isPrimePow_iff_unique_prime_dvd` / 定理 `isPrimePow_iff_unique_prime_dvd`

English:
theorem isPrimePow_iff_unique_prime_dvd
  given: {n : Nat}
  statement: IsPrimePow n ↔ exists! p : Nat, p.Prime ∧ p ∣ n
  proof: by
  rw [isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp, hk, rfl⟩
    refine ⟨p, ⟨hp, dvd_pow_self _ hk.ne'⟩, ?_⟩
    rintro q ⟨hq, hq'⟩
    exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hq')
  rintro ⟨p, ⟨hp, hn⟩, hq⟩
  rcases eq_or_ne n 0 with (rfl | hn₀)
  · cases (hq 2 ⟨Nat.prime_two, dvd_zero 2⟩).trans (hq 3 ⟨Nat.prime_three, dvd_zero 3⟩).symm
  refine ⟨p, n.factorization p, hp, hp.factorization_pos_of_dvd hn₀ hn, ?_⟩
  simp only [and_imp] at hq
  apply Nat.dvd_antisymm (Nat.ordProj_dvd _ _)
  -- We need to show n ∣ p ^ n.factorization p
  apply Nat.dvd_of_primeFactorsList_subperm hn₀
  rw [hp.primeFactorsList_pow]; rw [List.subperm_ext_iff]
  intro q hq'
  rw [Nat.mem_primeFactorsList hn₀] at hq'
  cases hq _ hq'.1 hq'.2
  simp

中文:
定理 isPrimePow_iff_unique_prime_dvd
  条件: {n : 自然数}
  结论: IsPrimePow n ↔ 存在! p : 自然数, p.素 ∧ p ∣ n
  证明: by
  rw [isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp, hk, rfl⟩
    refine ⟨p, ⟨hp, dvd_pow_self _ hk.ne'⟩, ?_⟩
    rintro q ⟨hq, hq'⟩
    exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hq')
  rintro ⟨p, ⟨hp, hn⟩, hq⟩
  rcases eq_or_ne n 0 with (rfl | hn₀)
  · cases (hq 2 ⟨Nat.prime_two, dvd_zero 2⟩).trans (hq 3 ⟨Nat.prime_three, dvd_zero 3⟩).symm
  refine ⟨p, n.factorization p, hp, hp.factorization_pos_of_dvd hn₀ hn, ?_⟩
  simp only [and_imp] at hq
  apply Nat.dvd_antisymm (Nat.ordProj_dvd _ _)
  -- We need to show n ∣ p ^ n.factorization p
  apply Nat.dvd_of_primeFactorsList_subperm hn₀
  rw [hp.primeFactorsList_pow]; rw [List.subperm_ext_iff]
  intro q hq'
  rw [Nat.mem_primeFactorsList hn₀] at hq'
  cases hq _ hq'.1 hq'.2
  simp

Depends on / 依赖: Nat.dvd_antisymm, Nat.ordProj_dvd, Nat.prime_dvd_prime_iff_eq, Nat.prime_three, Nat.prime_two, and_imp, dvd_antisymm, dvd_of_dvd_pow, dvd_pow_self, dvd_zero, eq_or_ne, factorization, factorization_pos_of_dvd, hk.ne, hp.factorization_pos_of_dvd, hq.dvd_of_dvd_pow, isPrimePow_nat_iff, n.factorization, ordProj_dvd, prime_dvd_prime_iff_eq
-/
theorem isPrimePow_iff_unique_prime_dvd {n : Nat} : IsPrimePow n ↔ exists! p : Nat, p.Prime ∧ p ∣ n := by
  rw [isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp, hk, rfl⟩
    refine ⟨p, ⟨hp, dvd_pow_self _ hk.ne'⟩, ?_⟩
    rintro q ⟨hq, hq'⟩
    exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hq')
  rintro ⟨p, ⟨hp, hn⟩, hq⟩
  rcases eq_or_ne n 0 with (rfl | hn₀)
  · cases (hq 2 ⟨Nat.prime_two, dvd_zero 2⟩).trans (hq 3 ⟨Nat.prime_three, dvd_zero 3⟩).symm
  refine ⟨p, n.factorization p, hp, hp.factorization_pos_of_dvd hn₀ hn, ?_⟩
  simp only [and_imp] at hq
  apply Nat.dvd_antisymm (Nat.ordProj_dvd _ _)
  -- We need to show n ∣ p ^ n.factorization p
  apply Nat.dvd_of_primeFactorsList_subperm hn₀
  rw [hp.primeFactorsList_pow]; rw [List.subperm_ext_iff]
  intro q hq'
  rw [Nat.mem_primeFactorsList hn₀] at hq'
  cases hq _ hq'.1 hq'.2
  simp

/--
theorem `isPrimePow_pow_iff` / 定理 `isPrimePow_pow_iff`

English:
theorem isPrimePow_pow_iff
  given: {n k : Nat} (hk : k != 0)
  statement: IsPrimePow (n ^ k) ↔ IsPrimePow n
  proof: by
  simp only [isPrimePow_iff_unique_prime_dvd]
  apply existsUnique_congr
  simp +contextual [Nat.prime_iff, Prime.dvd_pow_iff_dvd, hk]

中文:
定理 isPrimePow_pow_iff
  条件: {n k : 自然数} (hk : k != 0)
  结论: IsPrimePow (n ^ k) ↔ IsPrimePow n
  证明: by
  simp only [isPrimePow_iff_unique_prime_dvd]
  apply existsUnique_congr
  simp +contextual [Nat.prime_iff, Prime.dvd_pow_iff_dvd, hk]

Depends on / 依赖: Nat.prime_iff, Prime.dvd_pow_iff_dvd, contextual, dvd_pow_iff_dvd, existsUnique_congr, isPrimePow_iff_unique_prime_dvd, prime_iff
-/
theorem isPrimePow_pow_iff {n k : Nat} (hk : k != 0) : IsPrimePow (n ^ k) ↔ IsPrimePow n := by
  simp only [isPrimePow_iff_unique_prime_dvd]
  apply existsUnique_congr
  simp +contextual [Nat.prime_iff, Prime.dvd_pow_iff_dvd, hk]

/--
theorem `Nat.Coprime.isPrimePow_dvd_mul` / 定理 `Nat.Coprime.isPrimePow_dvd_mul`

English:
theorem Nat.Coprime.isPrimePow_dvd_mul
  given: {n a b : Nat} (hab : Nat.Coprime a b) (hn : IsPrimePow n)
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp
  refine
    ⟨?_, fun h =>
      Or.elim h (fun i => i.trans ((@dvd_mul_right a b a hab).mpr (dvd_refl a)))
          fun i => i.trans ((@dvd_mul_left a b b hab.symm).mpr (dvd_refl b))⟩
  obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  simp only [hp.pow_dvd_iff_le_factorization (mul_ne_zero ha hb), Nat.factorization_mul ha hb,
    hp.pow_dvd_iff_le_factorization ha, hp.pow_dvd_iff_le_factorization hb, Pi.add_apply,
    Finsupp.coe_add]
  have : a.factorization p = 0 ∨ b.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff]; rw [← Finsupp.notMem_support_iff]; rw [← not_and_or]; rw [←
      Finset.mem_inter]
    intro t
    simpa using hab.disjoint_primeFactors.le_bot t
  rcases this with h | h <;> simp [h, imp_or]

中文:
定理 自然数.Coprime.isPrimePow_dvd_mul
  条件: {n a b : 自然数} (hab : 自然数.Coprime a b) (hn : IsPrimePow n)
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp
  refine
    ⟨?_, fun h =>
      Or.elim h (fun i => i.trans ((@dvd_mul_right a b a hab).mpr (dvd_refl a)))
          fun i => i.trans ((@dvd_mul_left a b b hab.symm).mpr (dvd_refl b))⟩
  obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  simp only [hp.pow_dvd_iff_le_factorization (mul_ne_zero ha hb), Nat.factorization_mul ha hb,
    hp.pow_dvd_iff_le_factorization ha, hp.pow_dvd_iff_le_factorization hb, Pi.add_apply,
    Finsupp.coe_add]
  have : a.factorization p = 0 ∨ b.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff]; rw [← Finsupp.notMem_support_iff]; rw [← not_and_or]; rw [←
      Finset.mem_inter]
    intro t
    simpa using hab.disjoint_primeFactors.le_bot t
  rcases this with h | h <;> simp [h, imp_or]

Depends on / 依赖: Finsupp, Finsupp.coe, Nat.factorization_mul, Or.elim, Pi.add_apply, add_apply, dvd_mul_left, dvd_mul_right, dvd_refl, eq_or_ne, factorization_mul, hab.symm, hp.pow_dvd_iff_le_factorization, i.trans, isPrimePow_nat_iff, mul_ne_zero, pow_dvd_iff_le_factorization
-/
theorem Nat.Coprime.isPrimePow_dvd_mul {n a b : Nat} (hab : Nat.Coprime a b) (hn : IsPrimePow n) :
    n ∣ a * b ↔ n ∣ a ∨ n ∣ b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp
  refine
    ⟨?_, fun h =>
      Or.elim h (fun i => i.trans ((@dvd_mul_right a b a hab).mpr (dvd_refl a)))
          fun i => i.trans ((@dvd_mul_left a b b hab.symm).mpr (dvd_refl b))⟩
  obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  simp only [hp.pow_dvd_iff_le_factorization (mul_ne_zero ha hb), Nat.factorization_mul ha hb,
    hp.pow_dvd_iff_le_factorization ha, hp.pow_dvd_iff_le_factorization hb, Pi.add_apply,
    Finsupp.coe_add]
  have : a.factorization p = 0 ∨ b.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff]; rw [← Finsupp.notMem_support_iff]; rw [← not_and_or]; rw [←
      Finset.mem_inter]
    intro t
    simpa using hab.disjoint_primeFactors.le_bot t
  rcases this with h | h <;> simp [h, imp_or]

/--
theorem `Nat.mul_divisors_filter_prime_pow` / 定理 `Nat.mul_divisors_filter_prime_pow`

English:
theorem Nat.mul_divisors_filter_prime_pow
  given: {a b : Nat} (hab : a.Coprime b)
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Nat.coprime_zero_left] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp only [Nat.coprime_zero_right] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  ext n
  simp only [ha, hb, Finset.mem_union, Finset.mem_filter, Nat.mul_eq_zero, and_true, Ne,
    and_congr_left_iff, not_false_iff, Nat.mem_divisors, or_self_iff]
  apply hab.isPrimePow_dvd_mul

中文:
定理 自然数.mul_divisors_filter_prime_pow
  条件: {a b : 自然数} (hab : a.Coprime b)
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Nat.coprime_zero_left] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp only [Nat.coprime_zero_right] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  ext n
  simp only [ha, hb, Finset.mem_union, Finset.mem_filter, Nat.mul_eq_zero, and_true, Ne,
    and_congr_left_iff, not_false_iff, Nat.mem_divisors, or_self_iff]
  apply hab.isPrimePow_dvd_mul

Depends on / 依赖: Finset, Finset.filter_singleton, Finset.mem_filter, Finset.mem_union, Nat.coprime_zero_left, Nat.coprime_zero_right, Nat.mem_divisors, Nat.mul_eq_zero, and_congr_left_iff, and_true, coprime_zero_left, coprime_zero_right, eq_or_ne, filter_singleton, hab.isPrimePow_dvd_mul, isPrimePow_dvd_mul, mem_divisors, mem_filter, mem_union, mul_eq_zero
-/
theorem Nat.mul_divisors_filter_prime_pow {a b : Nat} (hab : a.Coprime b) :
    {d in (a * b).divisors | IsPrimePow d} = {d in a.divisors union b.divisors | IsPrimePow d} := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Nat.coprime_zero_left] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp only [Nat.coprime_zero_right] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  ext n
  simp only [ha, hb, Finset.mem_union, Finset.mem_filter, Nat.mul_eq_zero, and_true, Ne,
    and_congr_left_iff, not_false_iff, Nat.mem_divisors, or_self_iff]
  apply hab.isPrimePow_dvd_mul

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Nat.Primes.prodNatEquiv` / `Nat.Primes.prodNatEquiv` 的定义

English:
definition Nat.Primes.prodNatEquiv
  signature: : Nat.Primes × Nat ≃ {n : Nat // IsPrimePow n} where
  body: ⟨pk.1 ^ (pk.2 + 1), ⟨pk.1, pk.2 + 1, prime_iff.mp pk.1.prop, pk.2.add_one_pos, rfl⟩⟩
  invFun n :=
    (⟨n.val.minFac, minFac_prime n.prop.ne_one⟩, n.val.factorization n.val.minFac - 1)
  left_inv := fun (p, k) => by
    simp only [p.prop.pow_minFac k.add_one_ne_zero, Subtype.coe_eta, factorization_pow, p.prop,
      Prime.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_add,
      Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, add_tsub_cancel_right]
  right_inv n := by
    ext1
    dsimp only
    rw [sub_one_add_one (Nat.factorization_minFac_ne_zero n.prop.one_lt)]; rw [n.prop.minFac_pow_factorization_eq]

@[simp]

中文:
定义 自然数.Primes.prod自然数Equiv
  签名: : 自然数.Primes × 自然数 ≃ {n : 自然数 // IsPrimePow n} where
  定义体: ⟨pk.1 ^ (pk.2 + 1), ⟨pk.1, pk.2 + 1, prime_iff.mp pk.1.prop, pk.2.add_one_pos, rfl⟩⟩
  invFun n :=
    (⟨n.val.minFac, minFac_prime n.prop.ne_one⟩, n.val.factorization n.val.minFac - 1)
  left_inv := fun (p, k) => by
    simp only [p.prop.pow_minFac k.add_one_ne_zero, Subtype.coe_eta, factorization_pow, p.prop,
      Prime.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_add,
      Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, add_tsub_cancel_right]
  right_inv n := by
    ext1
    dsimp only
    rw [sub_one_add_one (Nat.factorization_minFac_ne_zero n.prop.one_lt)]; rw [n.prop.minFac_pow_factorization_eq]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.coe_add, Finsupp.single_add, Finsupp.single_eq_same, Finsupp.smul_single, Pi.add_apply, Prime.factorization, Subtype, Subtype.coe_eta, add_apply, add_one_ne_zero, add_one_pos, add_tsub_cancel_right, coe_add, coe_eta, factorization, factorization_pow, invFun, k.add_one_ne_zero, left_inv
-/
def Nat.Primes.prodNatEquiv : Nat.Primes × Nat ≃ {n : Nat // IsPrimePow n} where
  toFun pk :=
    ⟨pk.1 ^ (pk.2 + 1), ⟨pk.1, pk.2 + 1, prime_iff.mp pk.1.prop, pk.2.add_one_pos, rfl⟩⟩
  invFun n :=
    (⟨n.val.minFac, minFac_prime n.prop.ne_one⟩, n.val.factorization n.val.minFac - 1)
  left_inv := fun (p, k) => by
    simp only [p.prop.pow_minFac k.add_one_ne_zero, Subtype.coe_eta, factorization_pow, p.prop,
      Prime.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_add,
      Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, add_tsub_cancel_right]
  right_inv n := by
    ext1
    dsimp only
    rw [sub_one_add_one (Nat.factorization_minFac_ne_zero n.prop.one_lt)]; rw [n.prop.minFac_pow_factorization_eq]

@[simp]
/--
lemma `Nat.Primes.prodNatEquiv_apply` / 引理 `Nat.Primes.prodNatEquiv_apply`

English:
lemma Nat.Primes.prodNatEquiv_apply
  given: (p : Nat.Primes) (k : Nat)
  proof: by
  rfl

@[simp]

中文:
引理 自然数.Primes.prod自然数Equiv_apply
  条件: (p : 自然数.Primes) (k : 自然数)
  证明: by
  rfl

@[simp]
-/
lemma Nat.Primes.prodNatEquiv_apply (p : Nat.Primes) (k : Nat) :
    prodNatEquiv (p, k) = ⟨p ^ (k + 1), p, k + 1, prime_iff.mp p.prop, k.add_one_pos, rfl⟩ := by
  rfl

@[simp]
/--
lemma `Nat.Primes.coe_prodNatEquiv_apply` / 引理 `Nat.Primes.coe_prodNatEquiv_apply`

English:
lemma Nat.Primes.coe_prodNatEquiv_apply
  given: (p : Nat.Primes) (k : Nat)
  proof: rfl

@[simp]

中文:
引理 自然数.Primes.coe_prod自然数Equiv_apply
  条件: (p : 自然数.Primes) (k : 自然数)
  证明: rfl

@[simp]
-/
lemma Nat.Primes.coe_prodNatEquiv_apply (p : Nat.Primes) (k : Nat) :
    (prodNatEquiv (p, k) : Nat) = p ^ (k + 1) :=
  rfl

@[simp]
/--
lemma `Nat.Primes.prodNatEquiv_symm_apply` / 引理 `Nat.Primes.prodNatEquiv_symm_apply`

English:
lemma Nat.Primes.prodNatEquiv_symm_apply
  given: {n : Nat} (hn : IsPrimePow n)
  proof: rfl

中文:
引理 自然数.Primes.prod自然数Equiv_symm_apply
  条件: {n : 自然数} (hn : IsPrimePow n)
  证明: rfl
-/
lemma Nat.Primes.prodNatEquiv_symm_apply {n : Nat} (hn : IsPrimePow n) :
    prodNatEquiv.symm ⟨n, hn⟩ =
      (⟨n.minFac, minFac_prime hn.ne_one⟩, n.factorization n.minFac - 1) :=
  rfl

namespace Nat

section PrimePowEqPow
variable {p a m n : Nat} (hp : p.Prime) (hn : n != 0) (h : p ^ m = a ^ n)
include hp h

/--
theorem `exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow` / 定理 `exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow`

English:
theorem exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow
  proof: by
  have := congrArg Nat.factorization h
  rw [Nat.Prime.factorization_pow hp]; rw [Nat.factorization_pow] at this
  simpa using congr($this p)

中文:
定理 exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow
  证明: by
  have := congrArg Nat.factorization h
  rw [Nat.Prime.factorization_pow hp]; rw [Nat.factorization_pow] at this
  simpa using congr($this p)

Depends on / 依赖: Nat.Prime.factorization_pow, Nat.factorization, Nat.factorization_pow, factorization, factorization_pow
-/
theorem exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow :
    m = n * a.factorization p := by
  have := congrArg Nat.factorization h
  rw [Nat.Prime.factorization_pow hp]; rw [Nat.factorization_pow] at this
  simpa using congr($this p)

/--
theorem `exponent_dvd_of_prime_pow_eq_pow` / 定理 `exponent_dvd_of_prime_pow_eq_pow`

English:
theorem exponent_dvd_of_prime_pow_eq_pow
  statement: n ∣ m
  proof: Dvd.intro (a.factorization p)
    (exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow hp h).symm

include hn

中文:
定理 exponent_dvd_of_prime_pow_eq_pow
  结论: n ∣ m
  证明: Dvd.intro (a.factorization p)
    (exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow hp h).symm

include hn

Depends on / 依赖: Dvd.intro, a.factorization, exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow, factorization
-/
theorem exponent_dvd_of_prime_pow_eq_pow : n ∣ m :=
  Dvd.intro (a.factorization p)
    (exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow hp h).symm

include hn
/--
theorem `exists_base_eq_prime_pow_of_prime_pow_eq_base_pow` / 定理 `exists_base_eq_prime_pow_of_prime_pow_eq_base_pow`

English:
theorem exists_base_eq_prime_pow_of_prime_pow_eq_base_pow
  statement: exists k, a = p ^ k
  proof: by
  rcases exponent_dvd_of_prime_pow_eq_pow hp h with ⟨k, m_eq⟩
  rw [m_eq]; rw [pow_mul'] at h
  use k
  exact Nat.pow_left_injective hn h.symm

中文:
定理 存在_base_eq_prime_pow_of_prime_pow_eq_base_pow
  结论: 存在 k, a = p ^ k
  证明: by
  rcases exponent_dvd_of_prime_pow_eq_pow hp h with ⟨k, m_eq⟩
  rw [m_eq]; rw [pow_mul'] at h
  use k
  exact Nat.pow_left_injective hn h.symm

Depends on / 依赖: Nat.pow_left_injective, exponent_dvd_of_prime_pow_eq_pow, h.symm, m_eq, pow_left_injective, pow_mul
-/
theorem exists_base_eq_prime_pow_of_prime_pow_eq_base_pow : exists k, a = p ^ k := by
  rcases exponent_dvd_of_prime_pow_eq_pow hp h with ⟨k, m_eq⟩
  rw [m_eq]; rw [pow_mul'] at h
  use k
  exact Nat.pow_left_injective hn h.symm

end PrimePowEqPow

end Nat
