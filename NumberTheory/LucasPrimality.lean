/-
Copyright (c) 2020 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.IntegralDomain

/-!
# The Lucas test for primes

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number `a` witnesses that `n` is prime if `a` has order `n-1` in the
multiplicative group of integers mod `n`. This is checked by verifying that `a^(n-1) = 1 (mod n)`
and `a^d ≠ 1 (mod n)` for any divisor `d | n - 1`. This test is the basis of the Pratt primality
certificate.

## TODO
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate Pratt primality certificates into the `norm_num` primality verifier

## Implementation notes

Note that the proof for `lucas_primality` relies on analyzing the multiplicative group
modulo `p`. Despite this, the theorem still holds vacuously for `p = 0` and `p = 1`. In these
cases, we can take `q` to be any prime and see that `hd` does not hold, since `a^((p-1)/q)` reduces
to `1`.
-/

public section


/--
theorem `lucas_primality` / 定理 `lucas_primality`

English:
theorem lucas_primality
  statement: (p : Nat) (a : ZMod p) (ha : a ^ (p - 1) = 1)
  proof: by
  have h : p != 0 ∧ p != 1 := by
    constructor <;> rintro rfl <;> exact hd 2 Nat.prime_two (dvd_zero _) (pow_zero _)
  have hp1 : 1 < p := Nat.one_lt_iff_ne_zero_and_ne_one.2 h
  have : NeZero p := ⟨h.1⟩
  rw [Nat.prime_iff_card_units]
  apply (Nat.card_units_zmod_lt_sub_one hp1).antisymm
  let

中文:
定理 lucas_primality
  结论: (p : 自然数) (a : ZMod p) (ha : a ^ (p - 1) = 1)
  证明: by
  have h : p != 0 ∧ p != 1 := by
    constructor <;> rintro rfl <;> exact hd 2 Nat.prime_two (dvd_zero _) (pow_zero _)
  have hp1 : 1 < p := Nat.one_lt_iff_ne_zero_and_ne_one.2 h
  have : NeZero p := ⟨h.1⟩
  rw [Nat.prime_iff_card_units]
  apply (Nat.card_units_zmod_lt_sub_one hp1).antisymm
  let

Depends on / 依赖: Nat.card_units_zmod_lt_sub_one, Nat.one_lt_iff_ne_zero_and_ne_one, Nat.prime_iff_card_units, Nat.prime_two, NeZero, Units.mkOfMulEqOne, antisymm, card_units_zmod_lt_sub_one, dvd_zero, mkOfMulEqOne, one_lt_iff_ne_zero_and_ne_one, orderOf, orderOf_eq_of_pow_and_pow_div_prime, orderOf_inj, pow_succ, pow_zero, prime_iff_card_units, prime_two, tsub_add_eq_add_tsub, tsub_pos_of_lt
-/
theorem lucas_primality (p : Nat) (a : ZMod p) (ha : a ^ (p - 1) = 1)
    (hd : forall q : Nat, q.Prime -> q ∣ p - 1 -> a ^ ((p - 1) / q) != 1) : p.Prime := by
  have h : p != 0 ∧ p != 1 := by
    constructor <;> rintro rfl <;> exact hd 2 Nat.prime_two (dvd_zero _) (pow_zero _)
  have hp1 : 1 < p := Nat.one_lt_iff_ne_zero_and_ne_one.2 h
  have : NeZero p := ⟨h.1⟩
  rw [Nat.prime_iff_card_units]
  apply (Nat.card_units_zmod_lt_sub_one hp1).antisymm
  let a' : (ZMod p)ˣ := Units.mkOfMulEqOne a _ (by rwa [← pow_succ', tsub_add_eq_add_tsub hp1])
  calc p - 1 = orderOf a := (orderOf_eq_of_pow_and_pow_div_prime (tsub_pos_of_lt hp1) ha hd).symm
    _ = orderOf a' := orderOf_injective (Units.coeHom _) Units.val_injective a'
    _ <= Fintype.card (ZMod p)ˣ := orderOf_le_card_univ

/--
theorem `reverse_lucas_primality` / 定理 `reverse_lucas_primality`

English:
theorem reverse_lucas_primality
  given: (p : Nat) (hP : p.Prime)
  proof: by
  have : Fact p.Prime := ⟨hP⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have h1 : orderOf g = p - 1 := by
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ← Nat.prime_iff_card_units]
  have h2 := tsub_pos_iff_lt.2 hP.one_lt
  rw [← orderOf_

中文:
定理 reverse_lucas_primality
  条件: (p : 自然数) (hP : p.Prime)
  证明: by
  have : Fact p.Prime := ⟨hP⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have h1 : orderOf g = p - 1 := by
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ← Nat.prime_iff_card_units]
  have h2 := tsub_pos_iff_lt.2 hP.one_lt
  rw [← orderOf_

Depends on / 依赖: IsCyclic, IsCyclic.exists_generator, Nat.card_eq_fintype_card, Nat.div_lt_self, Nat.div_pos, Nat.le_of_dvd, Nat.prime_iff_card_units, Units.coeHom, Units.val_injective, card_eq_fintype_card, coeHom, div_lt_self, div_pos, exists_generator, hP.one_lt, hq.one_lt, le_of_dvd, one_lt, orderOf, orderOf_eq_card_of_forall_mem_zpowers
-/
theorem reverse_lucas_primality (p : Nat) (hP : p.Prime) :
    exists a : ZMod p, a ^ (p - 1) = 1 ∧ forall q : Nat, q.Prime -> q ∣ p - 1 -> a ^ ((p - 1) / q) != 1 := by
  have : Fact p.Prime := ⟨hP⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have h1 : orderOf g = p - 1 := by
    rwa [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ← Nat.prime_iff_card_units]
  have h2 := tsub_pos_iff_lt.2 hP.one_lt
  rw [← orderOf_injective (Units.coeHom _) Units.val_injective _]; rw [orderOf_eq_iff h2] at h1
  refine ⟨g, h1.1, fun q hq hqd => ?_⟩
  replace hq := hq.one_lt
  exact h1.2 _ (Nat.div_lt_self h2 hq) (Nat.div_pos (Nat.le_of_dvd h2 hqd) (zero_lt_one.trans hq))

/--
theorem `lucas_primality_iff` / 定理 `lucas_primality_iff`

English:
theorem lucas_primality_iff
  given: (p : Nat)
  statement: p.Prime ↔
  proof: ⟨reverse_lucas_primality p, fun ⟨a, ⟨ha, hb⟩⟩ => lucas_primality p a ha hb⟩

中文:
定理 lucas_primality_iff
  条件: (p : 自然数)
  结论: p.Prime ↔
  证明: ⟨reverse_lucas_primality p, fun ⟨a, ⟨ha, hb⟩⟩ => lucas_primality p a ha hb⟩

Depends on / 依赖: lucas_primality, reverse_lucas_primality
-/
theorem lucas_primality_iff (p : Nat) : p.Prime ↔
    exists a : ZMod p, a ^ (p - 1) = 1 ∧ forall q : Nat, q.Prime -> q ∣ p - 1 -> a ^ ((p - 1) / q) != 1 :=
  ⟨reverse_lucas_primality p, fun ⟨a, ⟨ha, hb⟩⟩ => lucas_primality p a ha hb⟩
