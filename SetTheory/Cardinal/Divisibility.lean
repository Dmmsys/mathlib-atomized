/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Tactic.WLOG

/-!
# Cardinal Divisibility

We show basic results about divisibility in the cardinal numbers. This relation can be characterised
in the following simple way: if `a` and `b` are both less than `ℵ₀`, then `a ∣ b` iff they are
divisible as natural numbers. If `b` is greater than `ℵ₀`, then `a ∣ b` iff `a ≤ b`. This
furthermore shows that all infinite cardinals are prime; recall that `a * b = max a b` if
`ℵ₀ ≤ a * b`; therefore `a ∣ b * c = a ∣ max b c` and therefore clearly either `a ∣ b` or `a ∣ c`.
Note furthermore that no infinite cardinal is irreducible
(`Cardinal.not_irreducible_of_aleph0_le`), showing that the cardinal numbers do not form a
cancellative `CommMonoidWithZero`.

## Main results

* `Cardinal.prime_of_aleph0_le`: a `Cardinal` is prime if it is infinite.
* `Cardinal.is_prime_iff`: a `Cardinal` is prime iff it is infinite or a prime natural number.
* `Cardinal.isPrimePow_iff`: a `Cardinal` is a prime power iff it is infinite or a natural number
  which is itself a prime power.

-/

public section


namespace Cardinal

universe u

variable {a b : Cardinal.{u}} {n m : Nat}

/--
theorem `isUnit_iff` / 定理 `isUnit_iff`

English:
theorem isUnit_iff
  statement: IsUnit a ↔ a = 1
  proof: by
  refine
    ⟨fun h => ?_, by
      rintro rfl
      exact isUnit_one⟩
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact (not_isUnit_zero h).elim
  rw [isUnit_iff_forall_dvd] at h
  obtain ⟨t, ht⟩ := h 1
  rw [eq_comm]; rw [mul_eq_one_iff_of_one_le] at ht
  · exact ht.1
  · exact Cardinal.one_le_if

中文:
定理 isUnit_iff
  结论: 是单位 a ↔ a = 1
  证明: by
  refine
    ⟨fun h => ?_, by
      rintro rfl
      exact isUnit_one⟩
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact (not_isUnit_zero h).elim
  rw [isUnit_iff_forall_dvd] at h
  obtain ⟨t, ht⟩ := h 1
  rw [eq_comm]; rw [mul_eq_one_iff_of_one_le] at ht
  · exact ht.1
  · exact Cardinal.one_le_if

Depends on / 依赖: Cardinal, Cardinal.one_le_iff_ne_zero.mpr, eq_comm, eq_or_ne, isUnit_iff_forall_dvd, isUnit_one, mul_eq_one_iff_of_one_le, mul_zero, not_isUnit_zero, one_le_iff_ne_zero, zero_ne_one
-/
theorem isUnit_iff : IsUnit a ↔ a = 1 := by
  refine
    ⟨fun h => ?_, by
      rintro rfl
      exact isUnit_one⟩
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact (not_isUnit_zero h).elim
  rw [isUnit_iff_forall_dvd] at h
  obtain ⟨t, ht⟩ := h 1
  rw [eq_comm]; rw [mul_eq_one_iff_of_one_le] at ht
  · exact ht.1
  · exact Cardinal.one_le_iff_ne_zero.mpr ha
  · apply Cardinal.one_le_iff_ne_zero.mpr
    intro h
    rw [h]; rw [mul_zero] at ht
    exact zero_ne_one ht

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique Cardinal.{u}ˣ
  body: 1
uniq a := Units.val_eq_one.mp isUnit_iff.mp a.isUnit

中文:
实例 :
  签名: 唯一 基数.{u}ˣ
  定义体: 1
uniq a := Units.val_eq_one.mp isUnit_iff.mp a.isUnit
-/
instance : Unique Cardinal.{u}ˣ where
  default := 1
uniq a := Units.val_eq_one.mp isUnit_iff.mp a.isUnit

/--
theorem `le_of_dvd` / 定理 `le_of_dvd`

English:
theorem le_of_dvd
  given: {a b : Cardinal} (hb : b != 0) (hdiv : a ∣ b)
  statement: a <= b
  proof: by
  obtain ⟨b, rfl⟩ := hdiv
  apply le_mul_right
  simp_all

中文:
定理 le_of_dvd
  条件: {a b : 基数} (hb : b != 0) (hdiv : a ∣ b)
  结论: a <= b
  证明: by
  obtain ⟨b, rfl⟩ := hdiv
  apply le_mul_right
  simp_all

Depends on / 依赖: le_mul_right
-/
theorem le_of_dvd {a b : Cardinal} (hb : b != 0) (hdiv : a ∣ b) : a <= b := by
  obtain ⟨b, rfl⟩ := hdiv
  apply le_mul_right
  simp_all

/--
theorem `dvd_of_le_of_aleph0_le` / 定理 `dvd_of_le_of_aleph0_le`

English:
theorem dvd_of_le_of_aleph0_le
  given: (ha : a != 0) (h : a <= b) (hb : ℵ₀ <= b)
  statement: a ∣ b
  proof: ⟨b, (mul_eq_right hb h ha).symm⟩

@[simp]

中文:
定理 dvd_of_le_of_aleph0_le
  条件: (ha : a != 0) (h : a <= b) (hb : ℵ₀ <= b)
  结论: a ∣ b
  证明: ⟨b, (mul_eq_right hb h ha).symm⟩

@[simp]

Depends on / 依赖: mul_eq_right
-/
theorem dvd_of_le_of_aleph0_le (ha : a != 0) (h : a <= b) (hb : ℵ₀ <= b) : a ∣ b :=
  ⟨b, (mul_eq_right hb h ha).symm⟩

@[simp]
/--
theorem `prime_of_aleph0_le` / 定理 `prime_of_aleph0_le`

English:
theorem prime_of_aleph0_le
  given: (ha : ℵ₀ <= a)
  statement: Prime a
  proof: by
  refine ⟨(aleph0_pos.trans_le ha).ne', ?_, fun b c hbc => ?_⟩
  · rw [isUnit_iff]
    exact (one_lt_aleph0.trans_le ha).ne'
  rcases eq_or_ne (b * c) 0 with hz | hz
  · rcases mul_eq_zero.mp hz with (rfl | rfl) <;> simp
  wlog h : c <= b
  · cases le_total c b <;> [solve_by_elim; rw [or_comm]]
 

中文:
定理 prime_of_aleph0_le
  条件: (ha : ℵ₀ <= a)
  结论: 素 a
  证明: by
  refine ⟨(aleph0_pos.trans_le ha).ne', ?_, fun b c hbc => ?_⟩
  · rw [isUnit_iff]
    exact (one_lt_aleph0.trans_le ha).ne'
  rcases eq_or_ne (b * c) 0 with hz | hz
  · rcases mul_eq_zero.mp hz with (rfl | rfl) <;> simp
  wlog h : c <= b
  · cases le_total c b <;> [solve_by_elim; rw [or_comm]]
 

Depends on / 依赖: aleph0_pos, aleph0_pos.trans_le, all_goals, apply_assumption, eq_or_ne, ha.trans, if_pos, isUnit_iff, le_of_dvd, le_total, max_def, mul_comm, mul_eq_max, mul_eq_zero, mul_eq_zero.mp, one_lt_aleph0, one_lt_aleph0.trans_le, or_comm, solve_by_elim, trans_le
-/
theorem prime_of_aleph0_le (ha : ℵ₀ <= a) : Prime a := by
  refine ⟨(aleph0_pos.trans_le ha).ne', ?_, fun b c hbc => ?_⟩
  · rw [isUnit_iff]
    exact (one_lt_aleph0.trans_le ha).ne'
  rcases eq_or_ne (b * c) 0 with hz | hz
  · rcases mul_eq_zero.mp hz with (rfl | rfl) <;> simp
  wlog h : c <= b
  · cases le_total c b <;> [solve_by_elim; rw [or_comm]]
    apply_assumption
    assumption'
    all_goals rwa [mul_comm]
  left
  have habc := le_of_dvd hz hbc
  rwa [mul_eq_max' <| ha.trans <| habc, max_def', if_pos h] at hbc

/--
theorem `not_irreducible_of_aleph0_le` / 定理 `not_irreducible_of_aleph0_le`

English:
theorem not_irreducible_of_aleph0_le
  given: (ha : ℵ₀ <= a)
  statement: ¬Irreducible a
  proof: by
  rw [irreducible_iff]; rw [not_and_or]
  refine Or.inr fun h => ?_
  simpa [mul_aleph0_eq ha, isUnit_iff, (one_lt_aleph0.trans_le ha).ne', one_lt_aleph0.ne'] using
    @h a ℵ₀

@[simp, norm_cast]

中文:
定理 not_irreducible_of_aleph0_le
  条件: (ha : ℵ₀ <= a)
  结论: ¬不可约 a
  证明: by
  rw [irreducible_iff]; rw [not_and_or]
  refine Or.inr fun h => ?_
  simpa [mul_aleph0_eq ha, isUnit_iff, (one_lt_aleph0.trans_le ha).ne', one_lt_aleph0.ne'] using
    @h a ℵ₀

@[simp, norm_cast]

Depends on / 依赖: Or.inr, irreducible_iff, isUnit_iff, mul_aleph0_eq, not_and_or, one_lt_aleph0, one_lt_aleph0.ne, one_lt_aleph0.trans_le, trans_le
-/
theorem not_irreducible_of_aleph0_le (ha : ℵ₀ <= a) : ¬Irreducible a := by
  rw [irreducible_iff]; rw [not_and_or]
  refine Or.inr fun h => ?_
  simpa [mul_aleph0_eq ha, isUnit_iff, (one_lt_aleph0.trans_le ha).ne', one_lt_aleph0.ne'] using
    @h a ℵ₀

@[simp, norm_cast]
/--
theorem `nat_coe_dvd_iff` / 定理 `nat_coe_dvd_iff`

English:
theorem nat_coe_dvd_iff
  statement: (n : Cardinal) ∣ m ↔ n ∣ m
  proof: by
  refine ⟨?_, fun ⟨h, ht⟩ => ⟨h, mod_cast ht⟩⟩
  rintro ⟨k, hk⟩
  have : ↑m < ℵ₀ := natCast_lt_aleph0
  rw [hk]; rw [mul_lt_aleph0_iff] at this
  rcases this with (h | h | ⟨-, hk'⟩)
  iterate 2 simp only [h, mul_zero, zero_mul, Nat.cast_eq_zero] at hk; simp [hk]
  lift k to Nat using hk'
  exact 

中文:
定理 nat_coe_dvd_iff
  结论: (n : 基数) ∣ m ↔ n ∣ m
  证明: by
  refine ⟨?_, fun ⟨h, ht⟩ => ⟨h, mod_cast ht⟩⟩
  rintro ⟨k, hk⟩
  have : ↑m < ℵ₀ := natCast_lt_aleph0
  rw [hk]; rw [mul_lt_aleph0_iff] at this
  rcases this with (h | h | ⟨-, hk'⟩)
  iterate 2 simp only [h, mul_zero, zero_mul, Nat.cast_eq_zero] at hk; simp [hk]
  lift k to Nat using hk'
  exact 

Depends on / 依赖: Nat.cast_eq_zero, cast_eq_zero, iterate, mod_cast, mul_lt_aleph0_iff, mul_zero, natCast_lt_aleph0, zero_mul
-/
theorem nat_coe_dvd_iff : (n : Cardinal) ∣ m ↔ n ∣ m := by
  refine ⟨?_, fun ⟨h, ht⟩ => ⟨h, mod_cast ht⟩⟩
  rintro ⟨k, hk⟩
  have : ↑m < ℵ₀ := natCast_lt_aleph0
  rw [hk]; rw [mul_lt_aleph0_iff] at this
  rcases this with (h | h | ⟨-, hk'⟩)
  iterate 2 simp only [h, mul_zero, zero_mul, Nat.cast_eq_zero] at hk; simp [hk]
  lift k to Nat using hk'
  exact ⟨k, mod_cast hk⟩

@[simp]
/--
theorem `nat_is_prime_iff` / 定理 `nat_is_prime_iff`

English:
theorem nat_is_prime_iff
  statement: Prime (n : Cardinal) ↔ n.Prime
  proof: by
  simp only [Prime, Nat.prime_iff]
  refine and_congr (by simp) (and_congr ?_ ⟨fun h b c hbc => ?_, fun h b c hbc => ?_⟩)
  · simp only [isUnit_iff, Nat.isUnit_iff]
    exact mod_cast Iff.rfl
  · exact mod_cast h b c (mod_cast hbc)
  rcases lt_or_ge (b * c) ℵ₀ with h' | h'
  · rcases mul_lt_aleph

中文:
定理 nat_is_prime_iff
  结论: 素 (n : 基数) ↔ n.素
  证明: by
  simp only [Prime, Nat.prime_iff]
  refine and_congr (by simp) (and_congr ?_ ⟨fun h b c hbc => ?_, fun h b c hbc => ?_⟩)
  · simp only [isUnit_iff, Nat.isUnit_iff]
    exact mod_cast Iff.rfl
  · exact mod_cast h b c (mod_cast hbc)
  rcases lt_or_ge (b * c) ℵ₀ with h' | h'
  · rcases mul_lt_aleph

Depends on / 依赖: Cardinal, Iff.rfl, Nat.isUnit_iff, Nat.prime_iff, aleph0_le_mul_iff, aleph0_le_mul_iff.mp, and_congr, isUnit_iff, lt_or_ge, mod_cast, mul_lt_aleph0_iff, mul_lt_aleph0_iff.mp, prime_iff
-/
theorem nat_is_prime_iff : Prime (n : Cardinal) ↔ n.Prime := by
  simp only [Prime, Nat.prime_iff]
  refine and_congr (by simp) (and_congr ?_ ⟨fun h b c hbc => ?_, fun h b c hbc => ?_⟩)
  · simp only [isUnit_iff, Nat.isUnit_iff]
    exact mod_cast Iff.rfl
  · exact mod_cast h b c (mod_cast hbc)
  rcases lt_or_ge (b * c) ℵ₀ with h' | h'
  · rcases mul_lt_aleph0_iff.mp h' with (rfl | rfl | ⟨hb, hc⟩)
    · simp
    · simp
    lift b to Nat using hb
    lift c to Nat using hc
    exact mod_cast h b c (mod_cast hbc)
  rcases aleph0_le_mul_iff.mp h' with ⟨hb, hc, hℵ₀⟩
  have hn : (n : Cardinal) != 0 := by
    intro h
    rw [h]; rw [zero_dvd_iff]; rw [mul_eq_zero] at hbc
    cases hbc <;> contradiction
  wlog hℵ₀b : ℵ₀ <= b
  apply (this h c b _ _ hc hb hℵ₀.symm hn (hℵ₀.resolve_left hℵ₀b)).symm <;> try assumption
  · rwa [mul_comm] at hbc
  · rwa [mul_comm] at h'
  · exact Or.inl (dvd_of_le_of_aleph0_le hn (natCast_lt_aleph0.le.trans hℵ₀b) hℵ₀b)

/--
theorem `is_prime_iff` / 定理 `is_prime_iff`

English:
theorem is_prime_iff
  given: {a : Cardinal}
  statement: Prime a ↔ ℵ₀ <= a ∨ exists p : Nat, a = p ∧ p.Prime
  proof: by
  rcases le_or_gt ℵ₀ a with h | h
  · simp [h]
  lift a to Nat using id h
  simp [not_le.mpr h]

中文:
定理 is_prime_iff
  条件: {a : 基数}
  结论: 素 a ↔ ℵ₀ <= a ∨ 存在 p : 自然数, a = p ∧ p.素
  证明: by
  rcases le_or_gt ℵ₀ a with h | h
  · simp [h]
  lift a to Nat using id h
  simp [not_le.mpr h]

Depends on / 依赖: le_or_gt, not_le, not_le.mpr
-/
theorem is_prime_iff {a : Cardinal} : Prime a ↔ ℵ₀ <= a ∨ exists p : Nat, a = p ∧ p.Prime := by
  rcases le_or_gt ℵ₀ a with h | h
  · simp [h]
  lift a to Nat using id h
  simp [not_le.mpr h]

/--
theorem `isPrimePow_iff` / 定理 `isPrimePow_iff`

English:
theorem isPrimePow_iff
  given: {a : Cardinal}
  statement: IsPrimePow a ↔ ℵ₀ <= a ∨ exists n : Nat, a = n ∧ IsPrimePow n
  proof: by
  by_cases h : ℵ₀ <= a
  · simp [h, (prime_of_aleph0_le h).isPrimePow]
  simp only [h, false_or, isPrimePow_nat_iff]
  lift a to Nat using not_le.mp h
  rw [isPrimePow_def]
  refine
    ⟨?_, fun ⟨n, han, p, k, hp, hk, h⟩ =>
          ⟨p, k, nat_is_prime_iff.2 hp, hk, by rw [han]; exact mod_cast h

中文:
定理 isPrimePow_iff
  条件: {a : 基数}
  结论: IsPrimePow a ↔ ℵ₀ <= a ∨ 存在 n : 自然数, a = n ∧ IsPrimePow n
  证明: by
  by_cases h : ℵ₀ <= a
  · simp [h, (prime_of_aleph0_le h).isPrimePow]
  simp only [h, false_or, isPrimePow_nat_iff]
  lift a to Nat using not_le.mp h
  rw [isPrimePow_def]
  refine
    ⟨?_, fun ⟨n, han, p, k, hp, hk, h⟩ =>
          ⟨p, k, nat_is_prime_iff.2 hp, hk, by rw [han]; exact mod_cast h

Depends on / 依赖: Cardinal, false_or, hp.ne_zero, isPrimePow, isPrimePow_def, isPrimePow_nat_iff, key.trans_lt, mod_cast, natCast_lt_aleph0, nat_is_prime_iff, ne_zero, not_le, not_le.mp, power_le_power_left, power_one, prime_of_aleph0_le, trans_lt
-/
theorem isPrimePow_iff {a : Cardinal} : IsPrimePow a ↔ ℵ₀ <= a ∨ exists n : Nat, a = n ∧ IsPrimePow n := by
  by_cases h : ℵ₀ <= a
  · simp [h, (prime_of_aleph0_le h).isPrimePow]
  simp only [h, false_or, isPrimePow_nat_iff]
  lift a to Nat using not_le.mp h
  rw [isPrimePow_def]
  refine
    ⟨?_, fun ⟨n, han, p, k, hp, hk, h⟩ =>
          ⟨p, k, nat_is_prime_iff.2 hp, hk, by rw [han]; exact mod_cast h⟩⟩
  rintro ⟨p, k, hp, hk, hpk⟩
  have key : p ^ (1 : Cardinal) <= ↑a := by
    rw [← hpk]; apply power_le_power_left hp.ne_zero; exact mod_cast hk
  rw [power_one] at key
  lift p to Nat using key.trans_lt natCast_lt_aleph0
  exact ⟨a, rfl, p, k, nat_is_prime_iff.mp hp, hk, mod_cast hpk⟩

end Cardinal
