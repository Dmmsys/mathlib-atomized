/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Multiplicative maps on unique factorization domains

## Main results
* `UniqueFactorizationMonoid.induction_on_coprime`: if `P` holds for `0`, units and powers of
  primes, and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`, then `P` holds on all `a : α`.
* `UniqueFactorizationMonoid.multiplicative_of_coprime`: if `f` maps `p ^ i` to `(f p) ^ i` for
  primes `p`, and `f` is multiplicative on coprime elements, then `f` is multiplicative everywhere.
-/

public section

assert_not_exists Field

variable {α : Type*}

namespace UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

section Multiplicative

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
variable {β : Type*} [CommMonoidWithZero β]

/--
theorem `prime_pow_coprime_prod_of_coprime_insert` / 定理 `prime_pow_coprime_prod_of_coprime_insert`

English:
theorem prime_pow_coprime_prod_of_coprime_insert
  statement: [DecidableEq α] {s : Finset α} (i : α -> Nat) (p : α)
  proof: by
  have hp := is_prime _ (Finset.mem_insert_self _ _)
  refine (isRelPrime_iff_no_prime_factors <| pow_ne_zero _ hp.ne_zero).mpr ?_
  intro d hdp hdprod hd
  apply hps
  replace hdp := hd.dvd_of_dvd_pow hdp
  obtain ⟨q, q_mem', hdq⟩ := hd.exists_mem_multiset_dvd hdprod
  obtain ⟨q, q_mem, rfl⟩ := 

中文:
定理 prime_pow_coprime_prod_of_coprime_insert
  结论: [DecidableEq α] {s : Finset α} (i : α -> 自然数) (p : α)
  证明: by
  have hp := is_prime _ (Finset.mem_insert_self _ _)
  refine (isRelPrime_iff_no_prime_factors <| pow_ne_zero _ hp.ne_zero).mpr ?_
  intro d hdp hdprod hd
  apply hps
  replace hdp := hd.dvd_of_dvd_pow hdp
  obtain ⟨q, q_mem', hdq⟩ := hd.exists_mem_multiset_dvd hdprod
  obtain ⟨q, q_mem, rfl⟩ := 

Depends on / 依赖: Finset, Finset.mem_in, Finset.mem_insert_self, Finset.mem_val, Multiset, Multiset.mem_map.mp, convert, dvd_of_dvd_pow, dvd_symm, dvd_trans, exists_mem_multiset_dvd, hd.dvd_of_dvd_pow, hd.exists_mem_multiset_dvd, hd.irreducible.dvd_symm, hdprod, hp.irreducible, hp.ne_zero, irreducible, isRelPrime_iff_no_prime_factors, is_coprime
-/
theorem prime_pow_coprime_prod_of_coprime_insert [DecidableEq α] {s : Finset α} (i : α -> Nat) (p : α)
    (hps : p ∉ s) (is_prime : forall q in insert p s, Prime q)
    (is_coprime : forallᵉ (q in insert p s) (q' in insert p s), q ∣ q' -> q = q') :
    IsRelPrime (p ^ i p) (∏ p' in s, p' ^ i p') := by
  have hp := is_prime _ (Finset.mem_insert_self _ _)
  refine (isRelPrime_iff_no_prime_factors <| pow_ne_zero _ hp.ne_zero).mpr ?_
  intro d hdp hdprod hd
  apply hps
  replace hdp := hd.dvd_of_dvd_pow hdp
  obtain ⟨q, q_mem', hdq⟩ := hd.exists_mem_multiset_dvd hdprod
  obtain ⟨q, q_mem, rfl⟩ := Multiset.mem_map.mp q_mem'
  replace hdq := hd.dvd_of_dvd_pow hdq
  have : p ∣ q := dvd_trans (hd.irreducible.dvd_symm hp.irreducible hdp) hdq
  convert! q_mem using 0
  rw [Finset.mem_val]; rw [is_coprime _ (Finset.mem_insert_self p s) _ (Finset.mem_insert_of_mem q_mem) this]

/-- If `P` holds for units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on a product of powers of distinct primes. -/
@[elab_as_elim]
/--
theorem `induction_on_prime_power` / 定理 `induction_on_prime_power`

English:
theorem induction_on_prime_power
  statement: {P : α -> Prop} (s : Finset α) (i : α -> Nat)
  proof: by
  let := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simpa using h1 isUnit_one
  | insert p f' hpf' ih =>
    rw [Finset.prod_insert hpf']
    exact
      hcp (prime_pow_coprime_prod_of_coprime_insert i p hpf' is_prime is_coprime)
        (hpr (i p) (is_prime _ (Fi

中文:
定理 induction_on_prime_power
  结论: {P : α -> 命题} (s : Finset α) (i : α -> 自然数)
  证明: by
  let := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simpa using h1 isUnit_one
  | insert p f' hpf' ih =>
    rw [Finset.prod_insert hpf']
    exact
      hcp (prime_pow_coprime_prod_of_coprime_insert i p hpf' is_prime is_coprime)
        (hpr (i p) (is_prime _ (Fi

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.prod_insert, induction_on, insert, isUnit_one, is_coprime, is_prime, mem_insert_of_mem, mem_insert_self, prime_pow_coprime_prod_of_coprime_insert, prod_insert
-/
theorem induction_on_prime_power {P : α -> Prop} (s : Finset α) (i : α -> Nat)
    (is_prime : forall p in s, Prime p) (is_coprime : forallᵉ (p in s) (q in s), p ∣ q -> p = q)
    (h1 : forall {x}, IsUnit x -> P x) (hpr : forall {p} (i : Nat), Prime p -> P (p ^ i))
    (hcp : forall {x y}, IsRelPrime x y -> P x -> P y -> P (x * y)) :
    P (∏ p in s, p ^ i p) := by
  let := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simpa using h1 isUnit_one
  | insert p f' hpf' ih =>
    rw [Finset.prod_insert hpf']
    exact
      hcp (prime_pow_coprime_prod_of_coprime_insert i p hpf' is_prime is_coprime)
        (hpr (i p) (is_prime _ (Finset.mem_insert_self _ _)))
        (ih (fun q hq => is_prime _ (Finset.mem_insert_of_mem hq)) fun q hq q' hq' =>
          is_coprime _ (Finset.mem_insert_of_mem hq) _ (Finset.mem_insert_of_mem hq'))

/-- If `P` holds for `0`, units and powers of primes,
and `P x ∧ P y` for coprime `x, y` implies `P (x * y)`,
then `P` holds on all `a : α`. -/
@[elab_as_elim]
/--
theorem `induction_on_coprime` / 定理 `induction_on_coprime`

English:
theorem induction_on_coprime
  statement: {P : α -> Prop} (a : α) (h0 : P 0) (h1 : forall {x}, IsUnit x -> P x)
  proof: by
  let := Classical.decEq α
  have P_of_associated : forall {x y}, Associated x y -> P x -> P y := by
    rintro x y ⟨u, rfl⟩ hx
    exact hcp (fun p _ hpx => isUnit_of_dvd_unit hpx u.isUnit) hx (h1 u.isUnit)
  by_cases ha0 : a = 0
  · rwa [ha0]
  have : Nontrivial α := ⟨⟨_, _, ha0⟩⟩
  let : Stron

中文:
定理 induction_on_coprime
  结论: {P : α -> 命题} (a : α) (h0 : P 0) (h1 : 对任意 {x}, IsUnit x -> P x)
  证明: by
  let := Classical.decEq α
  have P_of_associated : forall {x y}, Associated x y -> P x -> P y := by
    rintro x y ⟨u, rfl⟩ hx
    exact hcp (fun p _ hpx => isUnit_of_dvd_unit hpx u.isUnit) hx (h1 u.isUnit)
  by_cases ha0 : a = 0
  · rwa [ha0]
  have : Nontrivial α := ⟨⟨_, _, ha0⟩⟩
  let : Stron

Depends on / 依赖: Associated, Classical, Classical.decEq, Finset, Finset.prod_multiset_map_count, Nontrivial, P_of_associated, StrongNormalizationMonoid, UniqueFactorizationMonoid, UniqueFactorizationMonoid.strongNormalizationMonoid, inducti, isUnit, isUnit_of_dvd_unit, map_id, normalizedFactors, prod_multiset_map_count, prod_normalizedFactors, strongNormalizationMonoid, u.isUnit
-/
theorem induction_on_coprime {P : α -> Prop} (a : α) (h0 : P 0) (h1 : forall {x}, IsUnit x -> P x)
    (hpr : forall {p} (i : Nat), Prime p -> P (p ^ i))
    (hcp : forall {x y}, IsRelPrime x y -> P x -> P y -> P (x * y)) : P a := by
  let := Classical.decEq α
  have P_of_associated : forall {x y}, Associated x y -> P x -> P y := by
    rintro x y ⟨u, rfl⟩ hx
    exact hcp (fun p _ hpx => isUnit_of_dvd_unit hpx u.isUnit) hx (h1 u.isUnit)
  by_cases ha0 : a = 0
  · rwa [ha0]
  have : Nontrivial α := ⟨⟨_, _, ha0⟩⟩
  let : StrongNormalizationMonoid α := UniqueFactorizationMonoid.strongNormalizationMonoid
  refine P_of_associated (prod_normalizedFactors ha0) ?_
  rw [← (normalizedFactors a).map_id]; rw [Finset.prod_multiset_map_count]
  refine induction_on_prime_power _ _ ?_ ?_ @h1 @hpr @hcp <;> simp only [Multiset.mem_toFinset]
  · apply prime_of_normalized_factor
  · apply normalizedFactors_eq_of_dvd

/--
theorem `multiplicative_prime_power` / 定理 `multiplicative_prime_power`

English:
theorem multiplicative_prime_power
  statement: {f : α -> β} (s : Finset α) (i j : α -> Nat)
  proof: by
  let := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simpa using h1 isUnit_one
  | insert p s hps ih =>
    have hpr_p := is_prime _ (Finset.mem_insert_self _ _)
    have hpr_s : forall p in s, Prime p := fun p hp => is_prime _ (Finset.mem_insert_of_mem hp)
    hav

中文:
定理 multiplicative_prime_power
  结论: {f : α -> β} (s : Finset α) (i j : α -> 自然数)
  证明: by
  let := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simpa using h1 isUnit_one
  | insert p s hps ih =>
    have hpr_p := is_prime _ (Finset.mem_insert_self _ _)
    have hpr_s : forall p in s, Prime p := fun p hp => is_prime _ (Finset.mem_insert_of_mem hp)
    hav

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.induction_on, Finset.mem, Finset.mem_insert_of_mem, Finset.mem_insert_self, hcp_p, hcp_s, hpr_p, hpr_s, induction_on, insert, isUnit_one, is_coprime, is_prime, mem_insert_of_mem, mem_insert_self, prime_pow_coprime_prod_of_coprime_insert
-/
theorem multiplicative_prime_power {f : α -> β} (s : Finset α) (i j : α -> Nat)
    (is_prime : forall p in s, Prime p) (is_coprime : forallᵉ (p in s) (q in s), p ∣ q -> p = q)
    (h1 : forall {x y}, IsUnit y -> f (x * y) = f x * f y)
    (hpr : forall {p} (i : Nat), Prime p -> f (p ^ i) = f p ^ i)
    (hcp : forall {x y}, IsRelPrime x y -> f (x * y) = f x * f y) :
    f (∏ p in s, p ^ (i p + j p)) = f (∏ p in s, p ^ i p) * f (∏ p in s, p ^ j p) := by
  let := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simpa using h1 isUnit_one
  | insert p s hps ih =>
    have hpr_p := is_prime _ (Finset.mem_insert_self _ _)
    have hpr_s : forall p in s, Prime p := fun p hp => is_prime _ (Finset.mem_insert_of_mem hp)
    have hcp_p := fun i => prime_pow_coprime_prod_of_coprime_insert i p hps is_prime is_coprime
    have hcp_s : forallᵉ (p in s) (q in s), p ∣ q -> p = q := fun p hp q hq =>
      is_coprime p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps]; rw [Finset.prod_insert hps]; rw [Finset.prod_insert hps]; rw [hcp (hcp_p _)]; rw [hpr _ hpr_p]; rw [hcp (hcp_p _)]; rw [hpr _ hpr_p]; rw [hcp (hcp_p (fun p => i p + j p))]; rw [hpr _ hpr_p]; rw [ih hpr_s hcp_s]; rw [pow_add]; rw [mul_assoc]; rw [mul_left_comm (f p ^ j p)]; rw [mul_assoc]

/--
theorem `multiplicative_of_coprime` / 定理 `multiplicative_of_coprime`

English:
theorem multiplicative_of_coprime
  statement: (f : α -> β) (a b : α) (h0 : f 0 = 0)
  proof: by
  let := Classical.decEq α
  by_cases ha0 : a = 0
  · rw [ha0, zero_mul, h0, zero_mul]
  by_cases hb0 : b = 0
  · rw [hb0, mul_zero, h0, mul_zero]
  by_cases hf1 : f 1 = 0
  · calc
      f (a * b) = f (a * b * 1) := by rw [mul_one]
      _ = 0 := by simp only [h1 isUnit_one, hf1, mul_zero]
      

中文:
定理 multiplicative_of_coprime
  结论: (f : α -> β) (a b : α) (h0 : f 0 = 0)
  证明: by
  let := Classical.decEq α
  by_cases ha0 : a = 0
  · rw [ha0, zero_mul, h0, zero_mul]
  by_cases hb0 : b = 0
  · rw [hb0, mul_zero, h0, mul_zero]
  by_cases hf1 : f 1 = 0
  · calc
      f (a * b) = f (a * b * 1) := by rw [mul_one]
      _ = 0 := by simp only [h1 isUnit_one, hf1, mul_zero]
      

Depends on / 依赖: Classical, Classical.decEq, Nontrivial, StrongNormalizationMonoid, UniqueFactorizationMonoid, UniqueFactorizationMonoid.strongNormalizationMonoid, isUnit_one, mul_one, mul_zero, strongNormalizationMonoid, suffic, zero_mul
-/
theorem multiplicative_of_coprime (f : α -> β) (a b : α) (h0 : f 0 = 0)
    (h1 : forall {x y}, IsUnit y -> f (x * y) = f x * f y)
    (hpr : forall {p} (i : Nat), Prime p -> f (p ^ i) = f p ^ i)
    (hcp : forall {x y}, IsRelPrime x y -> f (x * y) = f x * f y) :
    f (a * b) = f a * f b := by
  let := Classical.decEq α
  by_cases ha0 : a = 0
  · rw [ha0, zero_mul, h0, zero_mul]
  by_cases hb0 : b = 0
  · rw [hb0, mul_zero, h0, mul_zero]
  by_cases hf1 : f 1 = 0
  · calc
      f (a * b) = f (a * b * 1) := by rw [mul_one]
      _ = 0 := by simp only [h1 isUnit_one, hf1, mul_zero]
      _ = f a * f (b * 1) := by simp only [h1 isUnit_one, hf1, mul_zero]
      _ = f a * f b := by rw [mul_one]
  have : Nontrivial α := ⟨⟨_, _, ha0⟩⟩
  let : StrongNormalizationMonoid α := UniqueFactorizationMonoid.strongNormalizationMonoid
  suffices
      f (∏ p in (normalizedFactors a).toFinset union (normalizedFactors b).toFinset,
        p ^ ((normalizedFactors a).count p + (normalizedFactors b).count p)) =
      f (∏ p in (normalizedFactors a).toFinset union (normalizedFactors b).toFinset,
        p ^ (normalizedFactors a).count p) *
      f (∏ p in (normalizedFactors a).toFinset union (normalizedFactors b).toFinset,
        p ^ (normalizedFactors b).count p) by
    obtain ⟨ua, a_eq⟩ := prod_normalizedFactors ha0
    obtain ⟨ub, b_eq⟩ := prod_normalizedFactors hb0
    rw [← a_eq]; rw [← b_eq]; rw [mul_right_comm (Multiset.prod (normalizedFactors a)) ua
        (Multiset.prod (normalizedFactors b) * ub)]; rw [h1 ua.isUnit]; rw [h1 ub.isUnit]; rw [h1 ua.isUnit]; rw [←
      mul_assoc]; rw [h1 ub.isUnit]; rw [mul_right_comm _ (f ua)]; rw [← mul_assoc]
    congr
    rw [← (normalizedFactors a).map_id]; rw [← (normalizedFactors b).map_id]; rw [Finset.prod_multiset_map_count]; rw [Finset.prod_multiset_map_count]; rw [Finset.prod_subset (Finset.subset_union_left (s₂ := (normalizedFactors b).toFinset))]; rw [Finset.prod_subset (Finset.subset_union_right (s₂ := (normalizedFactors b).toFinset))]; rw [←
      Finset.prod_mul_distrib]
    · simp_rw [id, ← pow_add, this]
    all_goals simp only [Multiset.mem_toFinset]
    · intro p _ hpb
      simp [hpb]
    · intro p _ hpa
      simp [hpa]
  refine multiplicative_prime_power _ _ _ ?_ ?_ @h1 @hpr @hcp
  all_goals simp only [Multiset.mem_toFinset, Finset.mem_union]
  · rintro p (hpa | hpb) <;> apply prime_of_normalized_factor <;> assumption
  · rintro p (hp | hp) q (hq | hq) hdvd <;>
      rw [← normalize_normalized_factor _ hp]; rw [← normalize_normalized_factor _ hq] <;>
      exact
        normalize_eq_normalize hdvd
          ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
            (prime_of_normalized_factor _ hq).irreducible hdvd)

end Multiplicative

end UniqueFactorizationMonoid
