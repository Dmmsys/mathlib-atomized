/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Data.Int.Basic

/-!
# Prime numbers in the naturals and the integers

TODO: This file can probably be merged with `Mathlib/Data/Int/NatPrime.lean`.
-/

public section


namespace Nat

/--
theorem `prime_iff_prime_int` / 定理 `prime_iff_prime_int`

English:
theorem prime_iff_prime_int
  given: {p : Nat}
  statement: p.Prime ↔ _root_.Prime (p : Int)
  proof: ⟨fun hp =>
    ⟨Int.natCast_ne_zero_iff_pos.2 hp.pos, mt Int.isUnit_iff_natAbs_eq.1 hp.ne_one, fun a b h => by
      rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast]; rw [Int.natAbs_mul]; rw [hp.dvd_mul] at h
      rwa [← Int.dvd_natAbs, Int.natCast_dvd_natCast, ← Int.dvd_natAbs, Int.natCast_dvd_

中文:
定理 prime_iff_prime_int
  条件: {p : 自然数}
  结论: p.素 ↔ _root_.素 (p : 整数)
  证明: ⟨fun hp =>
    ⟨Int.natCast_ne_zero_iff_pos.2 hp.pos, mt Int.isUnit_iff_natAbs_eq.1 hp.ne_one, fun a b h => by
      rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast]; rw [Int.natAbs_mul]; rw [hp.dvd_mul] at h
      rwa [← Int.dvd_natAbs, Int.natCast_dvd_natCast, ← Int.dvd_natAbs, Int.natCast_dvd_

Depends on / 依赖: Int.dvd_natAbs, Int.isUnit_iff_natAbs_eq, Int.natAbs_mul, Int.natCast_dvd_natCast, Int.natCast_mul, Int.natCast_ne_zero, Int.natCast_ne_zero_iff_pos, Nat.isUnit_iff, Nat.prime_iff, dvd_mul, dvd_natAbs, hp.dvd_mul, hp.ne_one, hp.pos, isUnit_iff, isUnit_iff_natAbs_eq, natAbs_mul, natCast_dvd_natCast, natCast_mul, natCast_ne_zero
-/
theorem prime_iff_prime_int {p : Nat} : p.Prime ↔ _root_.Prime (p : Int) :=
  ⟨fun hp =>
    ⟨Int.natCast_ne_zero_iff_pos.2 hp.pos, mt Int.isUnit_iff_natAbs_eq.1 hp.ne_one, fun a b h => by
      rw [← Int.dvd_natAbs]; rw [Int.natCast_dvd_natCast]; rw [Int.natAbs_mul]; rw [hp.dvd_mul] at h
      rwa [← Int.dvd_natAbs, Int.natCast_dvd_natCast, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]⟩,
    fun hp =>
    Nat.prime_iff.2
      ⟨Int.natCast_ne_zero.1 hp.1,
        (mt Nat.isUnit_iff.1) fun h => by simp [h] at hp, fun a b => by
        simpa only [Int.natCast_dvd_natCast, (Int.natCast_mul _ _).symm] using hp.2.2 a b⟩⟩

/--
lemma `Prime.pow_inj` / 引理 `Prime.pow_inj`

English:
lemma Prime.pow_inj
  statement: {p q m n : Nat} (hp : p.Prime) (hq : q.Prime)
  proof: by
  have H := dvd_antisymm (Prime.dvd_of_dvd_pow hp <| h ▸ dvd_pow_self p (succ_ne_zero m))
    (Prime.dvd_of_dvd_pow hq <| h.symm ▸ dvd_pow_self q (succ_ne_zero n))
exact ⟨H, succ_inj.mp Nat.pow_right_injective hq.two_le (H ▸ h)⟩

中文:
引理 素.pow_inj
  结论: {p q m n : 自然数} (hp : p.素) (hq : q.素)
  证明: by
  have H := dvd_antisymm (Prime.dvd_of_dvd_pow hp <| h ▸ dvd_pow_self p (succ_ne_zero m))
    (Prime.dvd_of_dvd_pow hq <| h.symm ▸ dvd_pow_self q (succ_ne_zero n))
exact ⟨H, succ_inj.mp Nat.pow_right_injective hq.two_le (H ▸ h)⟩

Depends on / 依赖: Nat.pow_right_injective, Prime.dvd_of_dvd_pow, dvd_antisymm, dvd_of_dvd_pow, dvd_pow_self, h.symm, hq.two_le, pow_right_injective, succ_inj, succ_inj.mp, succ_ne_zero, two_le
-/
lemma Prime.pow_inj {p q m n : Nat} (hp : p.Prime) (hq : q.Prime)
    (h : p ^ (m + 1) = q ^ (n + 1)) : p = q ∧ m = n := by
  have H := dvd_antisymm (Prime.dvd_of_dvd_pow hp <| h ▸ dvd_pow_self p (succ_ne_zero m))
    (Prime.dvd_of_dvd_pow hq <| h.symm ▸ dvd_pow_self q (succ_ne_zero n))
exact ⟨H, succ_inj.mp Nat.pow_right_injective hq.two_le (H ▸ h)⟩

/--
lemma `Prime.pow_inj'` / 引理 `Prime.pow_inj'`

English:
lemma Prime.pow_inj'
  proof: by
  obtain ⟨m, rfl⟩ := exists_eq_add_one_of_ne_zero hm
  obtain ⟨n, rfl⟩ := exists_eq_add_one_of_ne_zero hn
  simpa using hp.pow_inj hq h

中文:
引理 素.pow_inj'
  证明: by
  obtain ⟨m, rfl⟩ := exists_eq_add_one_of_ne_zero hm
  obtain ⟨n, rfl⟩ := exists_eq_add_one_of_ne_zero hn
  simpa using hp.pow_inj hq h

Depends on / 依赖: exists_eq_add_one_of_ne_zero, hp.pow_inj, pow_inj
-/
lemma Prime.pow_inj'
    {p q m n : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q) (hm : m != 0) (hn : n != 0)
    (h : p ^ m = q ^ n) : p = q ∧ m = n := by
  obtain ⟨m, rfl⟩ := exists_eq_add_one_of_ne_zero hm
  obtain ⟨n, rfl⟩ := exists_eq_add_one_of_ne_zero hn
  simpa using hp.pow_inj hq h

end Nat

namespace Int

@[simp]
/--
theorem `prime_ofNat_iff` / 定理 `prime_ofNat_iff`

English:
theorem prime_ofNat_iff
  given: {n : Nat}
  proof: Nat.prime_iff_prime_int.symm

中文:
定理 prime_of自然数_iff
  条件: {n : 自然数}
  证明: Nat.prime_iff_prime_int.symm

Depends on / 依赖: Nat.prime_iff_prime_int.symm, prime_iff_prime_int
-/
theorem prime_ofNat_iff {n : Nat} :
    Prime (ofNat(n) : Int) ↔ Nat.Prime (OfNat.ofNat n) :=
  Nat.prime_iff_prime_int.symm

/--
theorem `prime_two` / 定理 `prime_two`

English:
theorem prime_two
  statement: Prime (2 : Int)
  proof: prime_ofNat_iff.mpr Nat.prime_two

中文:
定理 prime_two
  结论: 素 (2 : 整数)
  证明: prime_ofNat_iff.mpr Nat.prime_two

Depends on / 依赖: Nat.prime_two, prime_ofNat_iff, prime_ofNat_iff.mpr, prime_two
-/
theorem prime_two : Prime (2 : Int) :=
  prime_ofNat_iff.mpr Nat.prime_two

/--
theorem `prime_three` / 定理 `prime_three`

English:
theorem prime_three
  statement: Prime (3 : Int)
  proof: prime_ofNat_iff.mpr Nat.prime_three

中文:
定理 prime_three
  结论: 素 (3 : 整数)
  证明: prime_ofNat_iff.mpr Nat.prime_three

Depends on / 依赖: Nat.prime_three, prime_ofNat_iff, prime_ofNat_iff.mpr, prime_three
-/
theorem prime_three : Prime (3 : Int) :=
  prime_ofNat_iff.mpr Nat.prime_three

end Int
