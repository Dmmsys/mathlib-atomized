/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Basic

/-!
# Prime numbers

This file deals with prime numbers: natural numbers `p ≥ 2` whose only divisors are `p` and `1`.

## Important declarations

- `Nat.Prime`: the predicate that expresses that a natural number `p` is prime
- `Nat.Primes`: the subtype of natural numbers that are prime
- `Nat.minFac n`: the minimal prime factor of a natural number `n ≠ 1`
- `Nat.prime_iff`: `Nat.Prime` coincides with the general definition of `Prime`
- `Nat.irreducible_iff_nat_prime`: a non-unit natural number is
                                  only divisible by `1` iff it is prime

-/

@[expose] public section

assert_not_exists Ring

namespace Nat

variable {n : Nat}

/-- `Nat.Prime p` means that `p` is a prime number, that is, a natural number
  at least 2 whose only divisors are `p` and `1`.
  The theorem `Nat.prime_def` witnesses this description of a prime number. -/
@[pp_nodot, wikidata Q49008]
/--
Definition of `Prime` / `Prime` 的定义

English:
definition Prime
  signature: (p : Nat)
  body: Irreducible p

中文:
定义 Prime
  签名: (p : 自然数)
  定义体: Irreducible p

Depends on / 依赖: Irreducible
-/
def Prime (p : Nat) :=
  Irreducible p

/--
theorem `irreducible_iff_nat_prime` / 定理 `irreducible_iff_nat_prime`

English:
theorem irreducible_iff_nat_prime
  given: (a : Nat)
  statement: Irreducible a ↔ Nat.Prime a
  proof: Iff.rfl

中文:
定理 irreducible_iff_nat_prime
  条件: (a : 自然数)
  结论: Irreducible a ↔ 自然数.Prime a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem irreducible_iff_nat_prime (a : Nat) : Irreducible a ↔ Nat.Prime a :=
  Iff.rfl

/--
theorem `not_prime_zero` / 定理 `not_prime_zero`

English:
theorem not_prime_zero
  statement: ¬ Prime 0

中文:
定理 not_prime_zero
  结论: ¬ Prime 0
-/
theorem not_prime_zero : ¬ Prime 0
  | h => h.ne_zero rfl

/--
theorem `prime_zero_false` / 定理 `prime_zero_false`

English:
theorem prime_zero_false
  statement: Prime 0 -> False
  proof: not_prime_zero

中文:
定理 prime_zero_false
  结论: Prime 0 -> False
  证明: not_prime_zero
-/
@[aesop safe destruct] theorem prime_zero_false : Prime 0 -> False :=
  not_prime_zero

/--
theorem `not_prime_one` / 定理 `not_prime_one`

English:
theorem not_prime_one
  statement: ¬ Prime 1

中文:
定理 not_prime_one
  结论: ¬ Prime 1
-/
theorem not_prime_one : ¬ Prime 1
  | h => h.ne_one rfl

/--
theorem `prime_one_false` / 定理 `prime_one_false`

English:
theorem prime_one_false
  statement: Prime 1 -> False
  proof: not_prime_one

中文:
定理 prime_one_false
  结论: Prime 1 -> False
  证明: not_prime_one
-/
@[aesop safe destruct] theorem prime_one_false : Prime 1 -> False :=
  not_prime_one

/--
theorem `Prime.ne_zero` / 定理 `Prime.ne_zero`

English:
theorem Prime.ne_zero
  given: {n : Nat} (h : Prime n)
  statement: n != 0
  proof: Irreducible.ne_zero h

中文:
定理 Prime.ne_zero
  条件: {n : 自然数} (h : Prime n)
  结论: n != 0
  证明: Irreducible.ne_zero h
-/
theorem Prime.ne_zero {n : Nat} (h : Prime n) : n != 0 :=
  Irreducible.ne_zero h

/--
theorem `Prime.pos` / 定理 `Prime.pos`

English:
theorem Prime.pos
  given: {p : Nat} (pp : Prime p)
  statement: 0 < p
  proof: Nat.pos_of_ne_zero pp.ne_zero

中文:
定理 Prime.pos
  条件: {p : 自然数} (pp : Prime p)
  结论: 0 < p
  证明: Nat.pos_of_ne_zero pp.ne_zero

Depends on / 依赖: Nat.pos_of_ne_zero, ne_zero, pos_of_ne_zero, pp.ne_zero
-/
theorem Prime.pos {p : Nat} (pp : Prime p) : 0 < p :=
  Nat.pos_of_ne_zero pp.ne_zero

/--
theorem `Prime.two_le` / 定理 `Prime.two_le`

English:
theorem Prime.two_le
  statement: forall {p : Nat}, Prime p -> 2 <= p

中文:
定理 Prime.two_le
  结论: 对任意 {p : 自然数}, Prime p -> 2 <= p
-/
theorem Prime.two_le : forall {p : Nat}, Prime p -> 2 <= p
  | 0, h => (not_prime_zero h).elim
  | 1, h => (not_prime_one h).elim
  | _ + 2, _ => le_add_left 2 _

/--
theorem `Prime.one_lt` / 定理 `Prime.one_lt`

English:
theorem Prime.one_lt
  given: {p : Nat}
  statement: Prime p -> 1 < p
  proof: Prime.two_le

中文:
定理 Prime.one_lt
  条件: {p : 自然数}
  结论: Prime p -> 1 < p
  证明: Prime.two_le

Depends on / 依赖: Prime.two_le, two_le
-/
theorem Prime.one_lt {p : Nat} : Prime p -> 1 < p :=
  Prime.two_le

/--
lemma `Prime.one_le` / 引理 `Prime.one_le`

English:
lemma Prime.one_le
  given: {p : Nat} (hp : p.Prime)
  statement: 1 <= p
  proof: hp.one_lt.le

中文:
引理 Prime.one_le
  条件: {p : 自然数} (hp : p.Prime)
  结论: 1 <= p
  证明: hp.one_lt.le

Depends on / 依赖: hp.one_lt.le, one_lt
-/
lemma Prime.one_le {p : Nat} (hp : p.Prime) : 1 <= p := hp.one_lt.le

/--
Instance `Prime.one_lt'` / 实例 `Prime.one_lt'`

English:
instance Prime.one_lt'
  signature: (p : Nat) [hp : Fact p.Prime]
  body: ⟨hp.1.one_lt⟩

中文:
实例 Prime.one_lt'
  签名: (p : 自然数) [hp : Fact p.Prime]
  定义体: ⟨hp.1.one_lt⟩

Depends on / 依赖: one_lt
-/
instance Prime.one_lt' (p : Nat) [hp : Fact p.Prime] : Fact (1 < p) :=
  ⟨hp.1.one_lt⟩

/--
theorem `Prime.ne_one` / 定理 `Prime.ne_one`

English:
theorem Prime.ne_one
  given: {p : Nat} (hp : p.Prime)
  statement: p != 1
  proof: hp.one_lt.ne'

中文:
定理 Prime.ne_one
  条件: {p : 自然数} (hp : p.Prime)
  结论: p != 1
  证明: hp.one_lt.ne'
-/
theorem Prime.ne_one {p : Nat} (hp : p.Prime) : p != 1 :=
  hp.one_lt.ne'

/--
theorem `Prime.eq_one_or_self_of_dvd` / 定理 `Prime.eq_one_or_self_of_dvd`

English:
theorem Prime.eq_one_or_self_of_dvd
  given: {p : Nat} (pp : p.Prime) (m : Nat) (hm : m ∣ p)
  proof: by
  obtain ⟨n, hn⟩ := hm
  have := pp.isUnit_or_isUnit hn
  rw [Nat.isUnit_iff]; rw [Nat.isUnit_iff] at this
  apply Or.imp_right _ this
  rintro rfl
  rw [hn]; rw [mul_one]

@[inherit_doc Nat.Prime]

中文:
定理 Prime.eq_one_or_self_of_dvd
  条件: {p : 自然数} (pp : p.Prime) (m : 自然数) (hm : m ∣ p)
  证明: by
  obtain ⟨n, hn⟩ := hm
  have := pp.isUnit_or_isUnit hn
  rw [Nat.isUnit_iff]; rw [Nat.isUnit_iff] at this
  apply Or.imp_right _ this
  rintro rfl
  rw [hn]; rw [mul_one]

@[inherit_doc Nat.Prime]

Depends on / 依赖: Nat.isUnit_iff, Or.imp_right, imp_right, isUnit_iff, isUnit_or_isUnit, mul_one, pp.isUnit_or_isUnit
-/
theorem Prime.eq_one_or_self_of_dvd {p : Nat} (pp : p.Prime) (m : Nat) (hm : m ∣ p) :
    m = 1 ∨ m = p := by
  obtain ⟨n, hn⟩ := hm
  have := pp.isUnit_or_isUnit hn
  rw [Nat.isUnit_iff]; rw [Nat.isUnit_iff] at this
  apply Or.imp_right _ this
  rintro rfl
  rw [hn]; rw [mul_one]

@[inherit_doc Nat.Prime]
/--
theorem `prime_def` / 定理 `prime_def`

English:
theorem prime_def
  given: {p : Nat}
  statement: Prime p ↔ 2 <= p ∧ forall m, m ∣ p -> m = 1 ∨ m = p
  proof: by
  refine ⟨fun h => ⟨h.two_le, h.eq_one_or_self_of_dvd⟩, fun h => ?_⟩
  have h1 := Nat.one_lt_two.trans_le h.1
  refine ⟨mt Nat.isUnit_iff.mp h1.ne', ?_⟩
  rintro a b rfl
  simp only [Nat.isUnit_iff]
  refine (h.2 a <| dvd_mul_right ..).imp_right fun hab => ?_
  rw [← mul_right_inj' (Nat.ne_zero_o

中文:
定理 prime_def
  条件: {p : 自然数}
  结论: Prime p ↔ 2 <= p ∧ 对任意 m, m ∣ p -> m = 1 ∨ m = p
  证明: by
  refine ⟨fun h => ⟨h.two_le, h.eq_one_or_self_of_dvd⟩, fun h => ?_⟩
  have h1 := Nat.one_lt_two.trans_le h.1
  refine ⟨mt Nat.isUnit_iff.mp h1.ne', ?_⟩
  rintro a b rfl
  simp only [Nat.isUnit_iff]
  refine (h.2 a <| dvd_mul_right ..).imp_right fun hab => ?_
  rw [← mul_right_inj' (Nat.ne_zero_o

Depends on / 依赖: Nat.isUnit_iff, Nat.isUnit_iff.mp, Nat.ne_zero_of_lt, Nat.one_lt_two.trans_le, dvd_mul_right, eq_one_or_self_of_dvd, h.eq_one_or_self_of_dvd, h.two_le, h1.ne, imp_right, isUnit_iff, mul_one, mul_right_inj, ne_zero_of_lt, one_lt_two, trans_le, two_le
-/
theorem prime_def {p : Nat} : Prime p ↔ 2 <= p ∧ forall m, m ∣ p -> m = 1 ∨ m = p := by
  refine ⟨fun h => ⟨h.two_le, h.eq_one_or_self_of_dvd⟩, fun h => ?_⟩
  have h1 := Nat.one_lt_two.trans_le h.1
  refine ⟨mt Nat.isUnit_iff.mp h1.ne', ?_⟩
  rintro a b rfl
  simp only [Nat.isUnit_iff]
  refine (h.2 a <| dvd_mul_right ..).imp_right fun hab => ?_
  rw [← mul_right_inj' (Nat.ne_zero_of_lt h1)]; rw [← hab]; rw [← hab]; rw [mul_one]

/--
theorem `prime_def_lt` / 定理 `prime_def_lt`

English:
theorem prime_def_lt
  given: {p : Nat}
  statement: Prime p ↔ 2 <= p ∧ forall m < p, m ∣ p -> m = 1
  proof: prime_def.trans
    and_congr_right fun p2 =>
      forall_congr' fun _ =>
        ⟨fun h l d => (h d).resolve_right (ne_of_lt l), fun h d =>
          (le_of_dvd (le_of_succ_le p2) d).lt_or_eq_dec.imp_left fun l => h l d⟩

中文:
定理 prime_def_lt
  条件: {p : 自然数}
  结论: Prime p ↔ 2 <= p ∧ 对任意 m < p, m ∣ p -> m = 1
  证明: prime_def.trans
    and_congr_right fun p2 =>
      forall_congr' fun _ =>
        ⟨fun h l d => (h d).resolve_right (ne_of_lt l), fun h d =>
          (le_of_dvd (le_of_succ_le p2) d).lt_or_eq_dec.imp_left fun l => h l d⟩

Depends on / 依赖: and_congr_right, forall_congr, imp_left, le_of_dvd, le_of_succ_le, lt_or_eq_dec, lt_or_eq_dec.imp_left, ne_of_lt, prime_def, prime_def.trans, resolve_right
-/
theorem prime_def_lt {p : Nat} : Prime p ↔ 2 <= p ∧ forall m < p, m ∣ p -> m = 1 :=
prime_def.trans
    and_congr_right fun p2 =>
      forall_congr' fun _ =>
        ⟨fun h l d => (h d).resolve_right (ne_of_lt l), fun h d =>
          (le_of_dvd (le_of_succ_le p2) d).lt_or_eq_dec.imp_left fun l => h l d⟩

/--
theorem `prime_def_lt'` / 定理 `prime_def_lt'`

English:
theorem prime_def_lt'
  given: {p : Nat}
  statement: Prime p ↔ 2 <= p ∧ forall m, 2 <= m -> m < p -> ¬m ∣ p
  proof: prime_def_lt.trans
    and_congr_right fun p2 =>
      forall_congr' fun m =>
        ⟨fun h m2 l d => not_lt_of_ge m2 ((h l d).symm ▸ by decide), fun h l d => by
          rcases m with (_ | _ | m)
          · omega
          · rfl
          · exact (h (le_add_left 2 m) l).elim d⟩

中文:
定理 prime_def_lt'
  条件: {p : 自然数}
  结论: Prime p ↔ 2 <= p ∧ 对任意 m, 2 <= m -> m < p -> ¬m ∣ p
  证明: prime_def_lt.trans
    and_congr_right fun p2 =>
      forall_congr' fun m =>
        ⟨fun h m2 l d => not_lt_of_ge m2 ((h l d).symm ▸ by decide), fun h l d => by
          rcases m with (_ | _ | m)
          · omega
          · rfl
          · exact (h (le_add_left 2 m) l).elim d⟩

Depends on / 依赖: and_congr_right, forall_congr, le_add_left, not_lt_of_ge, prime_def_lt, prime_def_lt.trans
-/
theorem prime_def_lt' {p : Nat} : Prime p ↔ 2 <= p ∧ forall m, 2 <= m -> m < p -> ¬m ∣ p :=
prime_def_lt.trans
    and_congr_right fun p2 =>
      forall_congr' fun m =>
        ⟨fun h m2 l d => not_lt_of_ge m2 ((h l d).symm ▸ by decide), fun h l d => by
          rcases m with (_ | _ | m)
          · omega
          · rfl
          · exact (h (le_add_left 2 m) l).elim d⟩

/--
theorem `prime_def_le_sqrt` / 定理 `prime_def_le_sqrt`

English:
theorem prime_def_le_sqrt
  given: {p : Nat}
  statement: Prime p ↔ 2 <= p ∧ forall m, 2 <= m -> m <= sqrt p -> ¬m ∣ p
  proof: prime_def_lt'.trans
    and_congr_right fun p2 =>
⟨fun a m m2 l => a m m2 lt_of_le_of_lt l sqrt_lt_self p2, fun a m m2 l mdvd@⟨k, e⟩ => by
        rcases le_sqrt_of_eq_mul e with hm | hk
        · exact a m m2 hm mdvd
        · rw [mul_comm] at e
          exact a k (Nat.lt_of_mul_lt_mul_right (a :=

中文:
定理 prime_def_le_sqrt
  条件: {p : 自然数}
  结论: Prime p ↔ 2 <= p ∧ 对任意 m, 2 <= m -> m <= sqrt p -> ¬m ∣ p
  证明: prime_def_lt'.trans
    and_congr_right fun p2 =>
⟨fun a m m2 l => a m m2 lt_of_le_of_lt l sqrt_lt_self p2, fun a m m2 l mdvd@⟨k, e⟩ => by
        rcases le_sqrt_of_eq_mul e with hm | hk
        · exact a m m2 hm mdvd
        · rw [mul_comm] at e
          exact a k (Nat.lt_of_mul_lt_mul_right (a :=

Depends on / 依赖: Nat.lt_of_mul_lt_mul_right, and_congr_right, le_sqrt_of_eq_mul, lt_of_le_of_lt, lt_of_mul_lt_mul_right, mul_comm, one_mul, prime_def_lt, sqrt_lt_self
-/
theorem prime_def_le_sqrt {p : Nat} : Prime p ↔ 2 <= p ∧ forall m, 2 <= m -> m <= sqrt p -> ¬m ∣ p :=
prime_def_lt'.trans
    and_congr_right fun p2 =>
⟨fun a m m2 l => a m m2 lt_of_le_of_lt l sqrt_lt_self p2, fun a m m2 l mdvd@⟨k, e⟩ => by
        rcases le_sqrt_of_eq_mul e with hm | hk
        · exact a m m2 hm mdvd
        · rw [mul_comm] at e
          exact a k (Nat.lt_of_mul_lt_mul_right (a := m) (by rwa [one_mul, ← e])) hk ⟨m, e⟩⟩

/--
theorem `prime_iff_not_exists_mul_eq` / 定理 `prime_iff_not_exists_mul_eq`

English:
theorem prime_iff_not_exists_mul_eq
  given: {p : Nat}
  proof: by
  push Not
  simp_rw [prime_def_lt, dvd_def, exists_imp]
  refine and_congr_right fun hp => forall_congr' fun m => (forall_congr' fun h => ?_).trans forall_comm
  simp_rw [Ne, forall_comm (β := _ = _), eq_comm, imp_false, not_lt]
  refine forall₂_congr fun n hp => ⟨by simp_all, fun hpn => ?_⟩
  h

中文:
定理 prime_iff_not_exists_mul_eq
  条件: {p : 自然数}
  证明: by
  push Not
  simp_rw [prime_def_lt, dvd_def, exists_imp]
  refine and_congr_right fun hp => forall_congr' fun m => (forall_congr' fun h => ?_).trans forall_comm
  simp_rw [Ne, forall_comm (β := _ = _), eq_comm, imp_false, not_lt]
  refine forall₂_congr fun n hp => ⟨by simp_all, fun hpn => ?_⟩
  h

Depends on / 依赖: Nat.le_mul_of_pos_left, Nat.mul_eq_right, and_congr_right, antisymm, dvd_def, eq_comm, exists_imp, forall_comm, forall_congr, hp.symm.trans, hpn.antisymm, imp_false, le_mul_of_pos_left, mul_eq_right, mul_ne_zero_iff, mul_ne_zero_iff.mp, not_lt, prime_def_lt, simp_rw
-/
theorem prime_iff_not_exists_mul_eq {p : Nat} :
    p.Prime ↔ 2 <= p ∧ ¬ exists m n, m < p ∧ n < p ∧ m * n = p := by
  push Not
  simp_rw [prime_def_lt, dvd_def, exists_imp]
  refine and_congr_right fun hp => forall_congr' fun m => (forall_congr' fun h => ?_).trans forall_comm
  simp_rw [Ne, forall_comm (β := _ = _), eq_comm, imp_false, not_lt]
  refine forall₂_congr fun n hp => ⟨by simp_all, fun hpn => ?_⟩
  have := mul_ne_zero_iff.mp (hp ▸ show p != 0 by lia)
  exact (Nat.mul_eq_right (by lia)).mp
    (hp.symm.trans (hpn.antisymm (hp ▸ Nat.le_mul_of_pos_left _ (by lia))))

/--
theorem `prime_of_coprime` / 定理 `prime_of_coprime`

English:
theorem prime_of_coprime
  given: (n : Nat) (h1 : 1 < n) (h : forall m < n, m != 0 -> n.Coprime m)
  statement: Prime n
  proof: by
  refine prime_def_lt.mpr ⟨h1, fun m mlt mdvd => ?_⟩
  have hm : m != 0 := by
    rintro rfl
    rw [zero_dvd_iff] at mdvd
    exact mlt.ne' mdvd
  exact (h m mlt hm).symm.eq_one_of_dvd mdvd

中文:
定理 prime_of_coprime
  条件: (n : 自然数) (h1 : 1 < n) (h : 对任意 m < n, m != 0 -> n.Coprime m)
  结论: Prime n
  证明: by
  refine prime_def_lt.mpr ⟨h1, fun m mlt mdvd => ?_⟩
  have hm : m != 0 := by
    rintro rfl
    rw [zero_dvd_iff] at mdvd
    exact mlt.ne' mdvd
  exact (h m mlt hm).symm.eq_one_of_dvd mdvd

Depends on / 依赖: eq_one_of_dvd, mlt.ne, prime_def_lt, prime_def_lt.mpr, symm.eq_one_of_dvd, zero_dvd_iff
-/
theorem prime_of_coprime (n : Nat) (h1 : 1 < n) (h : forall m < n, m != 0 -> n.Coprime m) : Prime n := by
  refine prime_def_lt.mpr ⟨h1, fun m mlt mdvd => ?_⟩
  have hm : m != 0 := by
    rintro rfl
    rw [zero_dvd_iff] at mdvd
    exact mlt.ne' mdvd
  exact (h m mlt hm).symm.eq_one_of_dvd mdvd

/--
Instance `decidablePrime` / 实例 `decidablePrime`

English:
instance decidablePrime
  signature: (p : Nat)
  body: decidable_of_iff' _ prime_def_lt'

中文:
实例 decidablePrime
  签名: (p : 自然数)
  定义体: decidable_of_iff' _ prime_def_lt'

Depends on / 依赖: decidable_of_iff, prime_def_lt
-/
instance decidablePrime (p : Nat) : Decidable (Prime p) :=
  decidable_of_iff' _ prime_def_lt'

/--
theorem `prime_two` / 定理 `prime_two`

English:
theorem prime_two
  statement: Prime 2
  proof: by decide

中文:
定理 prime_two
  结论: Prime 2
  证明: by decide
-/
theorem prime_two : Prime 2 := by decide

/--
theorem `prime_three` / 定理 `prime_three`

English:
theorem prime_three
  statement: Prime 3
  proof: by decide

中文:
定理 prime_three
  结论: Prime 3
  证明: by decide
-/
theorem prime_three : Prime 3 := by decide

/--
theorem `prime_five` / 定理 `prime_five`

English:
theorem prime_five
  statement: Prime 5
  proof: by decide

中文:
定理 prime_five
  结论: Prime 5
  证明: by decide
-/
theorem prime_five : Prime 5 := by decide

/--
theorem `prime_seven` / 定理 `prime_seven`

English:
theorem prime_seven
  statement: Prime 7
  proof: by decide

中文:
定理 prime_seven
  结论: Prime 7
  证明: by decide
-/
theorem prime_seven : Prime 7 := by decide

/--
theorem `prime_eleven` / 定理 `prime_eleven`

English:
theorem prime_eleven
  statement: Prime 11
  proof: by decide

中文:
定理 prime_eleven
  结论: Prime 11
  证明: by decide
-/
theorem prime_eleven : Prime 11 := by decide

/--
theorem `dvd_prime` / 定理 `dvd_prime`

English:
theorem dvd_prime
  given: {p m : Nat} (pp : Prime p)
  statement: m ∣ p ↔ m = 1 ∨ m = p
  proof: ⟨fun d => pp.eq_one_or_self_of_dvd m d, fun h =>
    h.elim (fun e => e.symm ▸ one_dvd _) fun e => e.symm ▸ dvd_rfl⟩

中文:
定理 dvd_prime
  条件: {p m : 自然数} (pp : Prime p)
  结论: m ∣ p ↔ m = 1 ∨ m = p
  证明: ⟨fun d => pp.eq_one_or_self_of_dvd m d, fun h =>
    h.elim (fun e => e.symm ▸ one_dvd _) fun e => e.symm ▸ dvd_rfl⟩

Depends on / 依赖: dvd_rfl, e.symm, eq_one_or_self_of_dvd, h.elim, one_dvd, pp.eq_one_or_self_of_dvd
-/
theorem dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m = p :=
  ⟨fun d => pp.eq_one_or_self_of_dvd m d, fun h =>
    h.elim (fun e => e.symm ▸ one_dvd _) fun e => e.symm ▸ dvd_rfl⟩

/--
theorem `dvd_prime_two_le` / 定理 `dvd_prime_two_le`

English:
theorem dvd_prime_two_le
  given: {p m : Nat} (pp : Prime p) (H : 2 <= m)
  statement: m ∣ p ↔ m = p
  proof: (dvd_prime pp).trans or_iff_right_of_imp Not.elim ne_of_gt H

中文:
定理 dvd_prime_two_le
  条件: {p m : 自然数} (pp : Prime p) (H : 2 <= m)
  结论: m ∣ p ↔ m = p
  证明: (dvd_prime pp).trans or_iff_right_of_imp Not.elim ne_of_gt H

Depends on / 依赖: Not.elim, dvd_prime, ne_of_gt, or_iff_right_of_imp
-/
theorem dvd_prime_two_le {p m : Nat} (pp : Prime p) (H : 2 <= m) : m ∣ p ↔ m = p :=
(dvd_prime pp).trans or_iff_right_of_imp Not.elim ne_of_gt H

/--
theorem `prime_dvd_prime_iff_eq` / 定理 `prime_dvd_prime_iff_eq`

English:
theorem prime_dvd_prime_iff_eq
  given: {p q : Nat} (pp : p.Prime) (qp : q.Prime)
  statement: p ∣ q ↔ p = q
  proof: dvd_prime_two_le qp (Prime.two_le pp)

中文:
定理 prime_dvd_prime_iff_eq
  条件: {p q : 自然数} (pp : p.Prime) (qp : q.Prime)
  结论: p ∣ q ↔ p = q
  证明: dvd_prime_two_le qp (Prime.two_le pp)

Depends on / 依赖: Prime.two_le, dvd_prime_two_le, two_le
-/
theorem prime_dvd_prime_iff_eq {p q : Nat} (pp : p.Prime) (qp : q.Prime) : p ∣ q ↔ p = q :=
  dvd_prime_two_le qp (Prime.two_le pp)

/--
theorem `Prime.not_dvd_one` / 定理 `Prime.not_dvd_one`

English:
theorem Prime.not_dvd_one
  given: {p : Nat} (pp : Prime p)
  statement: ¬p ∣ 1
  proof: Irreducible.not_dvd_one pp

中文:
定理 Prime.not_dvd_one
  条件: {p : 自然数} (pp : Prime p)
  结论: ¬p ∣ 1
  证明: Irreducible.not_dvd_one pp
-/
theorem Prime.not_dvd_one {p : Nat} (pp : Prime p) : ¬p ∣ 1 :=
  Irreducible.not_dvd_one pp

section MinFac

/--
theorem `minFac_lemma` / 定理 `minFac_lemma`

English:
theorem minFac_lemma
  given: (n k : Nat) (h : ¬n < k * k)
  statement: sqrt n - k < sqrt n + 2 - k
  proof: (Nat.sub_lt_sub_right <| le_sqrt.2 <| le_of_not_gt h) Nat.lt_add_of_pos_right (by decide)

中文:
定理 minFac_lemma
  条件: (n k : 自然数) (h : ¬n < k * k)
  结论: sqrt n - k < sqrt n + 2 - k
  证明: (Nat.sub_lt_sub_right <| le_sqrt.2 <| le_of_not_gt h) Nat.lt_add_of_pos_right (by decide)

Depends on / 依赖: Nat.lt_add_of_pos_right, Nat.sub_lt_sub_right, le_of_not_gt, le_sqrt, lt_add_of_pos_right, sub_lt_sub_right
-/
theorem minFac_lemma (n k : Nat) (h : ¬n < k * k) : sqrt n - k < sqrt n + 2 - k :=
(Nat.sub_lt_sub_right <| le_sqrt.2 <| le_of_not_gt h) Nat.lt_add_of_pos_right (by decide)

/--
Definition of `minFacAux` / `minFacAux` 的定义

English:
definition minFacAux
  signature: (n : Nat)

中文:
定义 minFacAux
  签名: (n : 自然数)
-/
def minFacAux (n : Nat) : Nat -> Nat
  | k =>
    if n < k * k then n
    else
      if k ∣ n then k
      else
        minFacAux n (k + 2)
termination_by k => sqrt n + 2 - k
decreasing_by simp_wf; apply minFac_lemma n k; assumption

/--
Definition of `minFac` / `minFac` 的定义

English:
definition minFac
  signature: (n : Nat)
  body: if 2 ∣ n then 2 else minFacAux n 3

@[simp]

中文:
定义 minFac
  签名: (n : 自然数)
  定义体: if 2 ∣ n then 2 else minFacAux n 3

@[simp]

Depends on / 依赖: minFacAux
-/
def minFac (n : Nat) : Nat :=
  if 2 ∣ n then 2 else minFacAux n 3

@[simp]
/--
theorem `minFac_zero` / 定理 `minFac_zero`

English:
theorem minFac_zero
  statement: minFac 0 = 2
  proof: rfl

@[simp]

中文:
定理 minFac_zero
  结论: minFac 0 = 2
  证明: rfl

@[simp]
-/
theorem minFac_zero : minFac 0 = 2 :=
  rfl

@[simp]
/--
theorem `minFac_one` / 定理 `minFac_one`

English:
theorem minFac_one
  statement: minFac 1 = 1
  proof: by
  simp [minFac, minFacAux]

@[simp]

中文:
定理 minFac_one
  结论: minFac 1 = 1
  证明: by
  simp [minFac, minFacAux]

@[simp]

Depends on / 依赖: minFac, minFacAux
-/
theorem minFac_one : minFac 1 = 1 := by
  simp [minFac, minFacAux]

@[simp]
/--
theorem `minFac_two` / 定理 `minFac_two`

English:
theorem minFac_two
  statement: minFac 2 = 2
  proof: by
  simp [minFac]

中文:
定理 minFac_two
  结论: minFac 2 = 2
  证明: by
  simp [minFac]

Depends on / 依赖: minFac
-/
theorem minFac_two : minFac 2 = 2 := by
  simp [minFac]

/--
theorem `minFac_eq` / 定理 `minFac_eq`

English:
theorem minFac_eq
  given: (n : Nat)
  statement: minFac n = if 2 ∣ n then 2 else minFacAux n 3
  proof: rfl

中文:
定理 minFac_eq
  条件: (n : 自然数)
  结论: minFac n = if 2 ∣ n then 2 else minFacAux n 3
  证明: rfl
-/
theorem minFac_eq (n : Nat) : minFac n = if 2 ∣ n then 2 else minFacAux n 3 := rfl

set_option backward.privateInPublic true in
/--
Definition of `minFacProp` / `minFacProp` 的定义

English:
definition minFacProp
  signature: (n k : Nat)
  body: 2 <= k ∧ k ∣ n ∧ forall m, 2 <= m -> m ∣ n -> k <= m

中文:
定义 minFacProp
  签名: (n k : 自然数)
  定义体: 2 <= k ∧ k ∣ n ∧ forall m, 2 <= m -> m ∣ n -> k <= m
-/
private def minFacProp (n k : Nat) :=
  2 <= k ∧ k ∣ n ∧ forall m, 2 <= m -> m ∣ n -> k <= m

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `minFacAux_has_prop` / 定理 `minFacAux_has_prop`

English:
theorem minFacAux_has_prop
  given: {n : Nat} (n2 : 2 <= n)
  proof: prime_def_le_sqrt.2
⟨n2, fun m m2 l d => not_lt_of_ge l lt_of_lt_of_le (sqrt_lt.2 h) (a m m2 d)⟩
      simpa only [k, h] using
        ⟨n2, dvd_rfl, fun m m2 d => le_of_eq ((dvd_prime_two_le pp m2).1 d).symm⟩
    have k2 : 2 <= k := by
      subst e
      apply Nat.le_add_left
    simp only [k, h, ↓

中文:
定理 minFacAux_has_prop
  条件: {n : 自然数} (n2 : 2 <= n)
  证明: prime_def_le_sqrt.2
⟨n2, fun m m2 l d => not_lt_of_ge l lt_of_lt_of_le (sqrt_lt.2 h) (a m m2 d)⟩
      simpa only [k, h] using
        ⟨n2, dvd_rfl, fun m m2 d => le_of_eq ((dvd_prime_two_le pp m2).1 d).symm⟩
    have k2 : 2 <= k := by
      subst e
      apply Nat.le_add_left
    simp only [k, h, ↓

Depends on / 依赖: Nat.le_add_left, Nat.left_distrib, add_right_comm, dvd_prime_two_le, dvd_rfl, le_add_left, le_of_eq, left_distrib, lt_of_lt_of_le, minFacAux_has_prop, minFac_lemma, not_lt_of_ge, prime_def_le_sqrt, reduceIte, sqrt_lt
-/
theorem minFacAux_has_prop {n : Nat} (n2 : 2 <= n) :
    forall k i, k = 2 * i + 3 -> (forall m, 2 <= m -> m ∣ n -> k <= m) -> minFacProp n (minFacAux n k)
  | k => fun i e a => by
    rw [minFacAux]
    by_cases h : n < k * k
    · have pp : Prime n :=
        prime_def_le_sqrt.2
⟨n2, fun m m2 l d => not_lt_of_ge l lt_of_lt_of_le (sqrt_lt.2 h) (a m m2 d)⟩
      simpa only [k, h] using
        ⟨n2, dvd_rfl, fun m m2 d => le_of_eq ((dvd_prime_two_le pp m2).1 d).symm⟩
    have k2 : 2 <= k := by
      subst e
      apply Nat.le_add_left
    simp only [k, h, ↓reduceIte]
    by_cases dk : k ∣ n <;> simp only [k, dk, ↓reduceIte]
    · exact ⟨k2, dk, a⟩
    · refine
        have := minFac_lemma n k h
        minFacAux_has_prop n2 (k + 2) (i + 1) (by simp [k, e, Nat.left_distrib, add_right_comm])
          fun m m2 d => ?_
      rcases Nat.eq_or_lt_of_le (a m m2 d) with rfl | ml
      · contradiction
      apply (Nat.eq_or_lt_of_le ml).resolve_left
      intro me
      rw [← me]; rw [e] at d
      have d' : 2 * (i + 2) ∣ n := d
      have := a _ le_rfl (dvd_of_mul_right_dvd d')
      rw [e] at this
      exact absurd this (by contradiction)
  termination_by k => sqrt n + 2 - k

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `minFac_has_prop` / 定理 `minFac_has_prop`

English:
theorem minFac_has_prop
  given: {n : Nat} (n1 : n != 1)
  statement: minFacProp n (minFac n)
  proof: by
  by_cases n0 : n = 0
  · simp [n0, minFacProp]
  have n2 : 2 <= n := by
    revert n0 n1
    rcases n with (_ | _ | _) <;> simp [succ_le_succ]
  simp only [minFac_eq]
  by_cases d2 : 2 ∣ n <;> simp only [d2, ↓reduceIte]
  · exact ⟨le_rfl, d2, fun k k2 _ => k2⟩
  · refine
      minFacAux_has_prop

中文:
定理 minFac_has_prop
  条件: {n : 自然数} (n1 : n != 1)
  结论: minFac命题 n (minFac n)
  证明: by
  by_cases n0 : n = 0
  · simp [n0, minFacProp]
  have n2 : 2 <= n := by
    revert n0 n1
    rcases n with (_ | _ | _) <;> simp [succ_le_succ]
  simp only [minFac_eq]
  by_cases d2 : 2 ∣ n <;> simp only [d2, ↓reduceIte]
  · exact ⟨le_rfl, d2, fun k k2 _ => k2⟩
  · refine
      minFacAux_has_prop

Depends on / 依赖: Nat.eq_or_lt_of_le, e.symm, eq_or_lt_of_le, le_rfl, minFacAux_has_prop, minFacProp, minFac_eq, reduceIte, resolve_left, revert, succ_le_succ
-/
theorem minFac_has_prop {n : Nat} (n1 : n != 1) : minFacProp n (minFac n) := by
  by_cases n0 : n = 0
  · simp [n0, minFacProp]
  have n2 : 2 <= n := by
    revert n0 n1
    rcases n with (_ | _ | _) <;> simp [succ_le_succ]
  simp only [minFac_eq]
  by_cases d2 : 2 ∣ n <;> simp only [d2, ↓reduceIte]
  · exact ⟨le_rfl, d2, fun k k2 _ => k2⟩
  · refine
      minFacAux_has_prop n2 3 0 rfl fun m m2 d => (Nat.eq_or_lt_of_le m2).resolve_left (mt ?_ d2)
    exact fun e => e.symm ▸ d

/--
theorem `minFac_dvd` / 定理 `minFac_dvd`

English:
theorem minFac_dvd
  given: (n : Nat)
  statement: minFac n ∣ n
  proof: if n1 : n = 1 then by simp [n1] else (minFac_has_prop n1).2.1

中文:
定理 minFac_dvd
  条件: (n : 自然数)
  结论: minFac n ∣ n
  证明: if n1 : n = 1 then by simp [n1] else (minFac_has_prop n1).2.1

Depends on / 依赖: minFac_has_prop
-/
theorem minFac_dvd (n : Nat) : minFac n ∣ n :=
  if n1 : n = 1 then by simp [n1] else (minFac_has_prop n1).2.1

/--
theorem `minFac_prime` / 定理 `minFac_prime`

English:
theorem minFac_prime
  given: {n : Nat} (n1 : n != 1)
  statement: Prime (minFac n)
  proof: let ⟨f2, fd, a⟩ := minFac_has_prop n1
  prime_def_lt'.2 ⟨f2, fun m m2 l d => not_le_of_gt l (a m m2 (d.trans fd))⟩

@[simp]

中文:
定理 minFac_prime
  条件: {n : 自然数} (n1 : n != 1)
  结论: Prime (minFac n)
  证明: let ⟨f2, fd, a⟩ := minFac_has_prop n1
  prime_def_lt'.2 ⟨f2, fun m m2 l d => not_le_of_gt l (a m m2 (d.trans fd))⟩

@[simp]

Depends on / 依赖: d.trans, minFac_has_prop, not_le_of_gt, prime_def_lt
-/
theorem minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n) :=
  let ⟨f2, fd, a⟩ := minFac_has_prop n1
  prime_def_lt'.2 ⟨f2, fun m m2 l d => not_le_of_gt l (a m m2 (d.trans fd))⟩

@[simp]
/--
theorem `minFac_prime_iff` / 定理 `minFac_prime_iff`

English:
theorem minFac_prime_iff
  given: {n : Nat}
  statement: Prime (minFac n) ↔ n != 1
  proof: by
  refine ⟨?_, minFac_prime⟩
  rintro h rfl
  simp only [minFac_one, not_prime_one] at h

中文:
定理 minFac_prime_iff
  条件: {n : 自然数}
  结论: Prime (minFac n) ↔ n != 1
  证明: by
  refine ⟨?_, minFac_prime⟩
  rintro h rfl
  simp only [minFac_one, not_prime_one] at h

Depends on / 依赖: minFac_one, minFac_prime, not_prime_one
-/
theorem minFac_prime_iff {n : Nat} : Prime (minFac n) ↔ n != 1 := by
  refine ⟨?_, minFac_prime⟩
  rintro h rfl
  simp only [minFac_one, not_prime_one] at h

/--
theorem `minFac_le_of_dvd` / 定理 `minFac_le_of_dvd`

English:
theorem minFac_le_of_dvd
  given: {n : Nat}
  statement: forall {m : Nat}, 2 <= m -> m ∣ n -> minFac n <= m
  proof: by
  by_cases n1 : n = 1
  · exact fun m2 _ => n1.symm ▸ le_trans (by simp) m2
  · apply (minFac_has_prop n1).2.2

中文:
定理 minFac_le_of_dvd
  条件: {n : 自然数}
  结论: 对任意 {m : 自然数}, 2 <= m -> m ∣ n -> minFac n <= m
  证明: by
  by_cases n1 : n = 1
  · exact fun m2 _ => n1.symm ▸ le_trans (by simp) m2
  · apply (minFac_has_prop n1).2.2

Depends on / 依赖: le_trans, minFac_has_prop, n1.symm
-/
theorem minFac_le_of_dvd {n : Nat} : forall {m : Nat}, 2 <= m -> m ∣ n -> minFac n <= m := by
  by_cases n1 : n = 1
  · exact fun m2 _ => n1.symm ▸ le_trans (by simp) m2
  · apply (minFac_has_prop n1).2.2

/--
theorem `minFac_pos` / 定理 `minFac_pos`

English:
theorem minFac_pos
  given: (n : Nat)
  statement: 0 < minFac n
  proof: by
  by_cases n1 : n = 1
  · simp [n1]
  · exact (minFac_prime n1).pos

中文:
定理 minFac_pos
  条件: (n : 自然数)
  结论: 0 < minFac n
  证明: by
  by_cases n1 : n = 1
  · simp [n1]
  · exact (minFac_prime n1).pos

Depends on / 依赖: minFac_prime
-/
theorem minFac_pos (n : Nat) : 0 < minFac n := by
  by_cases n1 : n = 1
  · simp [n1]
  · exact (minFac_prime n1).pos

/--
theorem `minFac_le` / 定理 `minFac_le`

English:
theorem minFac_le
  given: {n : Nat} (H : 0 < n)
  statement: minFac n <= n
  proof: le_of_dvd H (minFac_dvd n)

中文:
定理 minFac_le
  条件: {n : 自然数} (H : 0 < n)
  结论: minFac n <= n
  证明: le_of_dvd H (minFac_dvd n)

Depends on / 依赖: le_of_dvd, minFac_dvd
-/
theorem minFac_le {n : Nat} (H : 0 < n) : minFac n <= n :=
  le_of_dvd H (minFac_dvd n)

/--
theorem `le_minFac` / 定理 `le_minFac`

English:
theorem le_minFac
  given: {m n : Nat}
  statement: n = 1 ∨ m <= minFac n ↔ forall p, Prime p -> p ∣ n -> m <= p
  proof: ⟨fun h p pp d =>
    h.elim (by rintro rfl; cases pp.not_dvd_one d) fun h =>
le_trans h minFac_le_of_dvd pp.two_le d,
    fun H => or_iff_not_imp_left.2 fun n1 => H _ (minFac_prime n1) (minFac_dvd _)⟩

中文:
定理 le_minFac
  条件: {m n : 自然数}
  结论: n = 1 ∨ m <= minFac n ↔ 对任意 p, Prime p -> p ∣ n -> m <= p
  证明: ⟨fun h p pp d =>
    h.elim (by rintro rfl; cases pp.not_dvd_one d) fun h =>
le_trans h minFac_le_of_dvd pp.two_le d,
    fun H => or_iff_not_imp_left.2 fun n1 => H _ (minFac_prime n1) (minFac_dvd _)⟩

Depends on / 依赖: h.elim, le_trans, minFac_dvd, minFac_le_of_dvd, minFac_prime, not_dvd_one, or_iff_not_imp_left, pp.not_dvd_one, pp.two_le, two_le
-/
theorem le_minFac {m n : Nat} : n = 1 ∨ m <= minFac n ↔ forall p, Prime p -> p ∣ n -> m <= p :=
  ⟨fun h p pp d =>
    h.elim (by rintro rfl; cases pp.not_dvd_one d) fun h =>
le_trans h minFac_le_of_dvd pp.two_le d,
    fun H => or_iff_not_imp_left.2 fun n1 => H _ (minFac_prime n1) (minFac_dvd _)⟩

/--
theorem `le_minFac'` / 定理 `le_minFac'`

English:
theorem le_minFac'
  given: {m n : Nat}
  statement: n = 1 ∨ m <= minFac n ↔ forall p, 2 <= p -> p ∣ n -> m <= p
  proof: ⟨fun h p (pp : 1 < p) d =>
    h.elim (by rintro rfl; cases not_le_of_gt pp (le_of_dvd (by decide) d)) fun h =>
le_trans h minFac_le_of_dvd pp d,
    fun H => le_minFac.2 fun p pp d => H p pp.two_le d⟩

中文:
定理 le_minFac'
  条件: {m n : 自然数}
  结论: n = 1 ∨ m <= minFac n ↔ 对任意 p, 2 <= p -> p ∣ n -> m <= p
  证明: ⟨fun h p (pp : 1 < p) d =>
    h.elim (by rintro rfl; cases not_le_of_gt pp (le_of_dvd (by decide) d)) fun h =>
le_trans h minFac_le_of_dvd pp d,
    fun H => le_minFac.2 fun p pp d => H p pp.two_le d⟩

Depends on / 依赖: h.elim, le_minFac, le_of_dvd, le_trans, minFac_le_of_dvd, not_le_of_gt, pp.two_le, two_le
-/
theorem le_minFac' {m n : Nat} : n = 1 ∨ m <= minFac n ↔ forall p, 2 <= p -> p ∣ n -> m <= p :=
  ⟨fun h p (pp : 1 < p) d =>
    h.elim (by rintro rfl; cases not_le_of_gt pp (le_of_dvd (by decide) d)) fun h =>
le_trans h minFac_le_of_dvd pp d,
    fun H => le_minFac.2 fun p pp d => H p pp.two_le d⟩

/--
theorem `prime_def_minFac` / 定理 `prime_def_minFac`

English:
theorem prime_def_minFac
  given: {p : Nat}
  statement: Prime p ↔ 2 <= p ∧ minFac p = p
  proof: ⟨fun pp =>
    ⟨pp.two_le,
let ⟨f2, fd, _⟩ := minFac_has_prop ne_of_gt pp.one_lt
      ((dvd_prime pp).1 fd).resolve_left (ne_of_gt f2)⟩,
    fun ⟨p2, e⟩ => e ▸ minFac_prime (ne_of_gt p2)⟩

@[simp]

中文:
定理 prime_def_minFac
  条件: {p : 自然数}
  结论: Prime p ↔ 2 <= p ∧ minFac p = p
  证明: ⟨fun pp =>
    ⟨pp.two_le,
let ⟨f2, fd, _⟩ := minFac_has_prop ne_of_gt pp.one_lt
      ((dvd_prime pp).1 fd).resolve_left (ne_of_gt f2)⟩,
    fun ⟨p2, e⟩ => e ▸ minFac_prime (ne_of_gt p2)⟩

@[simp]

Depends on / 依赖: dvd_prime, minFac_has_prop, minFac_prime, ne_of_gt, one_lt, pp.one_lt, pp.two_le, resolve_left, two_le
-/
theorem prime_def_minFac {p : Nat} : Prime p ↔ 2 <= p ∧ minFac p = p :=
  ⟨fun pp =>
    ⟨pp.two_le,
let ⟨f2, fd, _⟩ := minFac_has_prop ne_of_gt pp.one_lt
      ((dvd_prime pp).1 fd).resolve_left (ne_of_gt f2)⟩,
    fun ⟨p2, e⟩ => e ▸ minFac_prime (ne_of_gt p2)⟩

@[simp]
/--
theorem `Prime.minFac_eq` / 定理 `Prime.minFac_eq`

English:
theorem Prime.minFac_eq
  given: {p : Nat} (hp : Prime p)
  statement: minFac p = p
  proof: (prime_def_minFac.1 hp).2

中文:
定理 Prime.minFac_eq
  条件: {p : 自然数} (hp : Prime p)
  结论: minFac p = p
  证明: (prime_def_minFac.1 hp).2

Depends on / 依赖: prime_def_minFac
-/
theorem Prime.minFac_eq {p : Nat} (hp : Prime p) : minFac p = p :=
  (prime_def_minFac.1 hp).2

/--
Definition of `decidablePrime'` / `decidablePrime'` 的定义

English:
definition decidablePrime'
  signature: (p : Nat)
  body: decidable_of_iff' _ prime_def_minFac

中文:
定义 decidablePrime'
  签名: (p : 自然数)
  定义体: decidable_of_iff' _ prime_def_minFac

Depends on / 依赖: decidable_of_iff, prime_def_minFac
-/
def decidablePrime' (p : Nat) : Decidable (Prime p) :=
  decidable_of_iff' _ prime_def_minFac

/--
theorem `decidablePrime_csimp` / 定理 `decidablePrime_csimp`

English:
theorem decidablePrime_csimp
  proof: by
  subsingleton

中文:
定理 decidablePrime_csimp
  证明: by
  subsingleton
-/
@[csimp] theorem decidablePrime_csimp :
    @decidablePrime = @decidablePrime' := by
  subsingleton

/--
theorem `not_prime_iff_minFac_lt` / 定理 `not_prime_iff_minFac_lt`

English:
theorem not_prime_iff_minFac_lt
  given: {n : Nat} (n2 : 2 <= n)
  statement: ¬Prime n ↔ minFac n < n
  proof: (not_congr <| prime_def_minFac.trans <| and_iff_right n2).trans
    (lt_iff_le_and_ne.trans <| and_iff_right <| minFac_le <| le_of_succ_le n2).symm

中文:
定理 not_prime_iff_minFac_lt
  条件: {n : 自然数} (n2 : 2 <= n)
  结论: ¬Prime n ↔ minFac n < n
  证明: (not_congr <| prime_def_minFac.trans <| and_iff_right n2).trans
    (lt_iff_le_and_ne.trans <| and_iff_right <| minFac_le <| le_of_succ_le n2).symm

Depends on / 依赖: and_iff_right, le_of_succ_le, lt_iff_le_and_ne, lt_iff_le_and_ne.trans, minFac_le, not_congr, prime_def_minFac, prime_def_minFac.trans
-/
theorem not_prime_iff_minFac_lt {n : Nat} (n2 : 2 <= n) : ¬Prime n ↔ minFac n < n :=
(not_congr <| prime_def_minFac.trans <| and_iff_right n2).trans
    (lt_iff_le_and_ne.trans <| and_iff_right <| minFac_le <| le_of_succ_le n2).symm

/--
theorem `minFac_le_div` / 定理 `minFac_le_div`

English:
theorem minFac_le_div
  given: {n : Nat} (pos : 0 < n) (np : ¬Prime n)
  statement: minFac n <= n / minFac n
  proof: match minFac_dvd n with
| ⟨0, h0⟩ => absurd pos by rw [h0, mul_zero]; decide
  | ⟨1, h1⟩ => by
    rw [mul_one] at h1
    rw [prime_def_minFac]; rw [not_and_or]; rw [← h1]; rw [eq_self_iff_true]; rw [_root_.not_true]; rw [_root_.or_false]; rw [not_le] at np
    rw [le_antisymm (le_of_lt_succ np) (su

中文:
定理 minFac_le_div
  条件: {n : 自然数} (pos : 0 < n) (np : ¬Prime n)
  结论: minFac n <= n / minFac n
  证明: match minFac_dvd n with
| ⟨0, h0⟩ => absurd pos by rw [h0, mul_zero]; decide
  | ⟨1, h1⟩ => by
    rw [mul_one] at h1
    rw [prime_def_minFac]; rw [not_and_or]; rw [← h1]; rw [eq_self_iff_true]; rw [_root_.not_true]; rw [_root_.or_false]; rw [not_le] at np
    rw [le_antisymm (le_of_lt_succ np) (su

Depends on / 依赖: Nat.div_one, Nat.mul_div_cancel_left, _root_, _root_.not_true, _root_.or_false, absurd, conv_rhs, div_one, eq_self_iff_true, le_add_left, le_antisymm, le_of_lt_succ, minFac, minFac_dvd, minFac_le_of_dvd, minFac_one, minFac_pos, mul_comm, mul_div_cancel_left, mul_one
-/
theorem minFac_le_div {n : Nat} (pos : 0 < n) (np : ¬Prime n) : minFac n <= n / minFac n :=
  match minFac_dvd n with
| ⟨0, h0⟩ => absurd pos by rw [h0, mul_zero]; decide
  | ⟨1, h1⟩ => by
    rw [mul_one] at h1
    rw [prime_def_minFac]; rw [not_and_or]; rw [← h1]; rw [eq_self_iff_true]; rw [_root_.not_true]; rw [_root_.or_false]; rw [not_le] at np
    rw [le_antisymm (le_of_lt_succ np) (succ_le_of_lt pos)]; rw [minFac_one]; rw [Nat.div_one]
  | ⟨x + 2, hx⟩ => by
    conv_rhs =>
      congr
      rw [hx]
    rw [Nat.mul_div_cancel_left _ (minFac_pos _)]
    exact minFac_le_of_dvd (le_add_left 2 x) ⟨minFac n, by rwa [mul_comm]⟩

/--
theorem `minFac_sq_le_self` / 定理 `minFac_sq_le_self`

English:
theorem minFac_sq_le_self
  given: {n : Nat} (w : 0 < n) (h : ¬Prime n)
  statement: minFac n ^ 2 <= n
  proof: have t : minFac n <= n / minFac n := minFac_le_div w h
  calc
    minFac n ^ 2 = minFac n * minFac n := sq (minFac n)
    _ <= n / minFac n * minFac n := Nat.mul_le_mul_right (minFac n) t
    _ <= n := div_mul_le_self n (minFac n)

@[simp]

中文:
定理 minFac_sq_le_self
  条件: {n : 自然数} (w : 0 < n) (h : ¬Prime n)
  结论: minFac n ^ 2 <= n
  证明: have t : minFac n <= n / minFac n := minFac_le_div w h
  calc
    minFac n ^ 2 = minFac n * minFac n := sq (minFac n)
    _ <= n / minFac n * minFac n := Nat.mul_le_mul_right (minFac n) t
    _ <= n := div_mul_le_self n (minFac n)

@[simp]

Depends on / 依赖: Nat.mul_le_mul_right, div_mul_le_self, minFac, minFac_le_div, mul_le_mul_right
-/
theorem minFac_sq_le_self {n : Nat} (w : 0 < n) (h : ¬Prime n) : minFac n ^ 2 <= n :=
  have t : minFac n <= n / minFac n := minFac_le_div w h
  calc
    minFac n ^ 2 = minFac n * minFac n := sq (minFac n)
    _ <= n / minFac n * minFac n := Nat.mul_le_mul_right (minFac n) t
    _ <= n := div_mul_le_self n (minFac n)

@[simp]
/--
theorem `minFac_eq_one_iff` / 定理 `minFac_eq_one_iff`

English:
theorem minFac_eq_one_iff
  given: {n : Nat}
  statement: minFac n = 1 ↔ n = 1
  proof: by
  constructor
  · intro h
    by_contra hn
    have := minFac_prime hn
    rw [h] at this
    exact not_prime_one this
  · rintro rfl
    simp [minFac, minFacAux]

@[simp]

中文:
定理 minFac_eq_one_iff
  条件: {n : 自然数}
  结论: minFac n = 1 ↔ n = 1
  证明: by
  constructor
  · intro h
    by_contra hn
    have := minFac_prime hn
    rw [h] at this
    exact not_prime_one this
  · rintro rfl
    simp [minFac, minFacAux]

@[simp]

Depends on / 依赖: minFac, minFacAux, minFac_prime, not_prime_one
-/
theorem minFac_eq_one_iff {n : Nat} : minFac n = 1 ↔ n = 1 := by
  constructor
  · intro h
    by_contra hn
    have := minFac_prime hn
    rw [h] at this
    exact not_prime_one this
  · rintro rfl
    simp [minFac, minFacAux]

@[simp]
/--
theorem `minFac_eq_two_iff` / 定理 `minFac_eq_two_iff`

English:
theorem minFac_eq_two_iff
  given: (n : Nat)
  statement: minFac n = 2 ↔ 2 ∣ n
  proof: by
  constructor
  · intro h
    rw [← h]
    exact minFac_dvd n
  · intro h
    have ub := minFac_le_of_dvd (le_refl 2) h
    have lb := minFac_pos n
    refine ub.eq_or_lt.resolve_right fun h' => ?_
    suffices n.minFac = 1 by simp_all
    exact (le_antisymm (Nat.succ_le_of_lt lb) (Nat.lt_succ_if

中文:
定理 minFac_eq_two_iff
  条件: (n : 自然数)
  结论: minFac n = 2 ↔ 2 ∣ n
  证明: by
  constructor
  · intro h
    rw [← h]
    exact minFac_dvd n
  · intro h
    have ub := minFac_le_of_dvd (le_refl 2) h
    have lb := minFac_pos n
    refine ub.eq_or_lt.resolve_right fun h' => ?_
    suffices n.minFac = 1 by simp_all
    exact (le_antisymm (Nat.succ_le_of_lt lb) (Nat.lt_succ_if

Depends on / 依赖: Nat.lt_succ_iff.mp, Nat.succ_le_of_lt, eq_or_lt, le_antisymm, le_refl, lt_succ_iff, minFac, minFac_dvd, minFac_le_of_dvd, minFac_pos, n.minFac, resolve_right, succ_le_of_lt, ub.eq_or_lt.resolve_right
-/
theorem minFac_eq_two_iff (n : Nat) : minFac n = 2 ↔ 2 ∣ n := by
  constructor
  · intro h
    rw [← h]
    exact minFac_dvd n
  · intro h
    have ub := minFac_le_of_dvd (le_refl 2) h
    have lb := minFac_pos n
    refine ub.eq_or_lt.resolve_right fun h' => ?_
    suffices n.minFac = 1 by simp_all
    exact (le_antisymm (Nat.succ_le_of_lt lb) (Nat.lt_succ_iff.mp h')).symm

/--
theorem `factors_lemma` / 定理 `factors_lemma`

English:
theorem factors_lemma
  given: {k}
  statement: (k + 2) / minFac (k + 2) < k + 2
  proof: div_lt_self (Nat.zero_lt_succ _) (minFac_prime (by
      apply Nat.ne_of_gt
      apply Nat.succ_lt_succ
      apply Nat.zero_lt_succ)).one_lt

中文:
定理 factors_lemma
  条件: {k}
  结论: (k + 2) / minFac (k + 2) < k + 2
  证明: div_lt_self (Nat.zero_lt_succ _) (minFac_prime (by
      apply Nat.ne_of_gt
      apply Nat.succ_lt_succ
      apply Nat.zero_lt_succ)).one_lt

Depends on / 依赖: Nat.ne_of_gt, Nat.succ_lt_succ, Nat.zero_lt_succ, div_lt_self, minFac_prime, ne_of_gt, one_lt, succ_lt_succ, zero_lt_succ
-/
theorem factors_lemma {k} : (k + 2) / minFac (k + 2) < k + 2 :=
  div_lt_self (Nat.zero_lt_succ _) (minFac_prime (by
      apply Nat.ne_of_gt
      apply Nat.succ_lt_succ
      apply Nat.zero_lt_succ)).one_lt

end MinFac

/--
theorem `exists_prime_and_dvd` / 定理 `exists_prime_and_dvd`

English:
theorem exists_prime_and_dvd
  given: {n : Nat} (hn : n != 1)
  statement: exists p, Prime p ∧ p ∣ n
  proof: ⟨minFac n, minFac_prime hn, minFac_dvd _⟩

中文:
定理 exists_prime_and_dvd
  条件: {n : 自然数} (hn : n != 1)
  结论: 存在 p, Prime p ∧ p ∣ n
  证明: ⟨minFac n, minFac_prime hn, minFac_dvd _⟩

Depends on / 依赖: minFac, minFac_dvd, minFac_prime
-/
theorem exists_prime_and_dvd {n : Nat} (hn : n != 1) : exists p, Prime p ∧ p ∣ n :=
  ⟨minFac n, minFac_prime hn, minFac_dvd _⟩

/--
theorem `coprime_of_dvd` / 定理 `coprime_of_dvd`

English:
theorem coprime_of_dvd
  given: {m n : Nat} (H : forall k, Prime k -> k ∣ m -> ¬k ∣ n)
  statement: Coprime m n
  proof: by
  rw [coprime_iff_gcd_eq_one]
  by_contra g2
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2
  apply H p hp <;> apply dvd_trans hpdvd
  · exact gcd_dvd_left _ _
  · exact gcd_dvd_right _ _

中文:
定理 coprime_of_dvd
  条件: {m n : 自然数} (H : 对任意 k, Prime k -> k ∣ m -> ¬k ∣ n)
  结论: Coprime m n
  证明: by
  rw [coprime_iff_gcd_eq_one]
  by_contra g2
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2
  apply H p hp <;> apply dvd_trans hpdvd
  · exact gcd_dvd_left _ _
  · exact gcd_dvd_right _ _

Depends on / 依赖: coprime_iff_gcd_eq_one, dvd_trans, exists_prime_and_dvd, gcd_dvd_left, gcd_dvd_right
-/
theorem coprime_of_dvd {m n : Nat} (H : forall k, Prime k -> k ∣ m -> ¬k ∣ n) : Coprime m n := by
  rw [coprime_iff_gcd_eq_one]
  by_contra g2
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2
  apply H p hp <;> apply dvd_trans hpdvd
  · exact gcd_dvd_left _ _
  · exact gcd_dvd_right _ _

/--
theorem `Prime.coprime_iff_not_dvd` / 定理 `Prime.coprime_iff_not_dvd`

English:
theorem Prime.coprime_iff_not_dvd
  given: {p n : Nat} (pp : Prime p)
  statement: Coprime p n ↔ ¬p ∣ n
  proof: ⟨fun co d => pp.not_dvd_one co.dvd_of_dvd_mul_left (by simp [d]), fun nd =>
    coprime_of_dvd fun _ m2 mp => ((prime_dvd_prime_iff_eq m2 pp).1 mp).symm ▸ nd⟩

中文:
定理 Prime.coprime_iff_not_dvd
  条件: {p n : 自然数} (pp : Prime p)
  结论: Coprime p n ↔ ¬p ∣ n
  证明: ⟨fun co d => pp.not_dvd_one co.dvd_of_dvd_mul_left (by simp [d]), fun nd =>
    coprime_of_dvd fun _ m2 mp => ((prime_dvd_prime_iff_eq m2 pp).1 mp).symm ▸ nd⟩

Depends on / 依赖: co.dvd_of_dvd_mul_left, coprime_of_dvd, dvd_of_dvd_mul_left, not_dvd_one, pp.not_dvd_one, prime_dvd_prime_iff_eq
-/
theorem Prime.coprime_iff_not_dvd {p n : Nat} (pp : Prime p) : Coprime p n ↔ ¬p ∣ n :=
⟨fun co d => pp.not_dvd_one co.dvd_of_dvd_mul_left (by simp [d]), fun nd =>
    coprime_of_dvd fun _ m2 mp => ((prime_dvd_prime_iff_eq m2 pp).1 mp).symm ▸ nd⟩

/--
theorem `Prime.dvd_mul` / 定理 `Prime.dvd_mul`

English:
theorem Prime.dvd_mul
  given: {p m n : Nat} (pp : Prime p)
  statement: p ∣ m * n ↔ p ∣ m ∨ p ∣ n
  proof: ⟨fun H => or_iff_not_imp_left.2 fun h => (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
    Or.rec (fun h : p ∣ m => h.mul_right _) fun h : p ∣ n => h.mul_left _⟩

alias ⟨Prime.dvd_or_dvd, _⟩ := Prime.dvd_mul

中文:
定理 Prime.dvd_mul
  条件: {p m n : 自然数} (pp : Prime p)
  结论: p ∣ m * n ↔ p ∣ m ∨ p ∣ n
  证明: ⟨fun H => or_iff_not_imp_left.2 fun h => (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
    Or.rec (fun h : p ∣ m => h.mul_right _) fun h : p ∣ n => h.mul_left _⟩

alias ⟨Prime.dvd_or_dvd, _⟩ := Prime.dvd_mul
-/
theorem Prime.dvd_mul {p m n : Nat} (pp : Prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=
  ⟨fun H => or_iff_not_imp_left.2 fun h => (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
    Or.rec (fun h : p ∣ m => h.mul_right _) fun h : p ∣ n => h.mul_left _⟩

alias ⟨Prime.dvd_or_dvd, _⟩ := Prime.dvd_mul

/--
theorem `prime_iff` / 定理 `prime_iff`

English:
theorem prime_iff
  given: {p : Nat}
  statement: p.Prime ↔ _root_.Prime p
  proof: ⟨fun h => ⟨h.ne_zero, h.not_isUnit, fun _ _ => h.dvd_mul.mp⟩, Prime.irreducible⟩

alias ⟨Prime.prime, _root_.Prime.nat_prime⟩ := prime_iff

中文:
定理 prime_iff
  条件: {p : 自然数}
  结论: p.Prime ↔ _root_.Prime p
  证明: ⟨fun h => ⟨h.ne_zero, h.not_isUnit, fun _ _ => h.dvd_mul.mp⟩, Prime.irreducible⟩

alias ⟨Prime.prime, _root_.Prime.nat_prime⟩ := prime_iff

Depends on / 依赖: Prime.irreducible, dvd_mul, h.dvd_mul.mp, h.ne_zero, h.not_isUnit, irreducible, ne_zero, not_isUnit
-/
theorem prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p :=
  ⟨fun h => ⟨h.ne_zero, h.not_isUnit, fun _ _ => h.dvd_mul.mp⟩, Prime.irreducible⟩

alias ⟨Prime.prime, _root_.Prime.nat_prime⟩ := prime_iff

/--
Instance `instDecidablePredPrime` / 实例 `instDecidablePredPrime`

English:
instance instDecidablePredPrime
  signature: : DecidablePred (_root_.Prime : Nat -> Prop)
  body: fun n =>
  decidable_of_iff (Nat.Prime n) Nat.prime_iff

中文:
实例 instDecidablePredPrime
  签名: : DecidablePred (_root_.Prime : 自然数 -> 命题)
  定义体: fun n =>
  decidable_of_iff (Nat.Prime n) Nat.prime_iff
-/
instance instDecidablePredPrime : DecidablePred (_root_.Prime : Nat -> Prop) := fun n =>
  decidable_of_iff (Nat.Prime n) Nat.prime_iff

/--
theorem `irreducible_iff_prime` / 定理 `irreducible_iff_prime`

English:
theorem irreducible_iff_prime
  given: {p : Nat}
  statement: Irreducible p ↔ _root_.Prime p
  proof: prime_iff

中文:
定理 irreducible_iff_prime
  条件: {p : 自然数}
  结论: Irreducible p ↔ _root_.Prime p
  证明: prime_iff

Depends on / 依赖: prime_iff
-/
theorem irreducible_iff_prime {p : Nat} : Irreducible p ↔ _root_.Prime p :=
  prime_iff

/--
Instance `instDecidablePredIrreducible` / 实例 `instDecidablePredIrreducible`

English:
instance instDecidablePredIrreducible
  signature: : DecidablePred (Irreducible : Nat -> Prop)
  body: decidablePrime

中文:
实例 instDecidablePredIrreducible
  签名: : DecidablePred (Irreducible : 自然数 -> 命题)
  定义体: decidablePrime

Depends on / 依赖: decidablePrime
-/
instance instDecidablePredIrreducible : DecidablePred (Irreducible : Nat -> Prop) :=
  decidablePrime

/--
Definition of `Primes` / `Primes` 的定义

English:
definition Primes
  body: { p : Nat // p.Prime }
  deriving DecidableEq

中文:
定义 Primes
  定义体: { p : Nat // p.Prime }
  deriving DecidableEq

Depends on / 依赖: p.Prime
-/
def Primes :=
  { p : Nat // p.Prime }
  deriving DecidableEq

namespace Primes

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Repr Nat.Primes
  body: ⟨fun p _ => repr p.val⟩

中文:
实例 :
  签名: Repr 自然数.Primes
  定义体: ⟨fun p _ => repr p.val⟩

Depends on / 依赖: p.val
-/
instance : Repr Nat.Primes :=
  ⟨fun p _ => repr p.val⟩

/--
Instance `inhabitedPrimes` / 实例 `inhabitedPrimes`

English:
instance inhabitedPrimes
  signature: : Inhabited Primes
  body: ⟨⟨2, prime_two⟩⟩

中文:
实例 inhabitedPrimes
  签名: : Inhabited Primes
  定义体: ⟨⟨2, prime_two⟩⟩

Depends on / 依赖: prime_two
-/
instance inhabitedPrimes : Inhabited Primes :=
  ⟨⟨2, prime_two⟩⟩

/--
Instance `coeNat` / 实例 `coeNat`

English:
instance coeNat
  signature: : Coe Nat.Primes Nat
  body: ⟨Subtype.val⟩

中文:
实例 coeNat
  签名: : Coe 自然数.Primes 自然数
  定义体: ⟨Subtype.val⟩

Depends on / 依赖: Subtype, Subtype.val
-/
instance coeNat : Coe Nat.Primes Nat :=
  ⟨Subtype.val⟩

/--
theorem `coe_nat_injective` / 定理 `coe_nat_injective`

English:
theorem coe_nat_injective
  statement: Function.Injective ((↑) : Nat.Primes -> Nat)
  proof: Subtype.coe_injective

中文:
定理 coe_nat_injective
  结论: Function.Injective ((↑) : 自然数.Primes -> 自然数)
  证明: Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem coe_nat_injective : Function.Injective ((↑) : Nat.Primes -> Nat) :=
  Subtype.coe_injective

/--
theorem `coe_nat_inj` / 定理 `coe_nat_inj`

English:
theorem coe_nat_inj
  given: (p q : Nat.Primes)
  statement: (p : Nat) = (q : Nat) ↔ p = q
  proof: Subtype.ext_iff.symm

中文:
定理 coe_nat_inj
  条件: (p q : 自然数.Primes)
  结论: (p : 自然数) = (q : 自然数) ↔ p = q
  证明: Subtype.ext_iff.symm

Depends on / 依赖: Subtype, Subtype.ext_iff.symm, ext_iff
-/
theorem coe_nat_inj (p q : Nat.Primes) : (p : Nat) = (q : Nat) ↔ p = q :=
  Subtype.ext_iff.symm

end Primes

/--
Instance `monoid.primePow` / 实例 `monoid.primePow`

English:
instance monoid.primePow
  signature: {α : Type*} [Monoid α]
  body: ⟨fun x p => x ^ (p : Nat)⟩

中文:
实例 monoid.primePow
  签名: {α : 类型} [Monoid α]
  定义体: ⟨fun x p => x ^ (p : Nat)⟩
-/
instance monoid.primePow {α : Type*} [Monoid α] : Pow α Primes :=
  ⟨fun x p => x ^ (p : Nat)⟩

/--
Instance `fact_prime_two` / 实例 `fact_prime_two`

English:
instance fact_prime_two
  signature: : Fact (Prime 2)
  body: ⟨prime_two⟩

中文:
实例 fact_prime_two
  签名: : Fact (Prime 2)
  定义体: ⟨prime_two⟩

Depends on / 依赖: prime_two
-/
instance fact_prime_two : Fact (Prime 2) :=
  ⟨prime_two⟩

/--
Instance `fact_prime_three` / 实例 `fact_prime_three`

English:
instance fact_prime_three
  signature: : Fact (Prime 3)
  body: ⟨prime_three⟩

中文:
实例 fact_prime_three
  签名: : Fact (Prime 3)
  定义体: ⟨prime_three⟩

Depends on / 依赖: prime_three
-/
instance fact_prime_three : Fact (Prime 3) :=
  ⟨prime_three⟩

end Nat
