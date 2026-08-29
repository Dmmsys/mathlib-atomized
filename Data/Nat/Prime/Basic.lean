/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Prime numbers

This file develops the theory of prime numbers: natural numbers `p ≥ 2` whose only divisors are
`p` and `1`.

-/

public section

namespace Nat
variable {n : Nat}

/--
theorem `prime_mul_iff` / 定理 `prime_mul_iff`

English:
theorem prime_mul_iff
  given: {a b : Nat}
  statement: Nat.Prime (a * b) ↔ a.Prime ∧ b = 1 ∨ b.Prime ∧ a = 1
  proof: by
  simp only [irreducible_mul_iff, ← irreducible_iff_nat_prime, Nat.isUnit_iff]

中文:
定理 prime_mul_iff
  条件: {a b : 自然数}
  结论: 自然数.Prime (a * b) ↔ a.Prime ∧ b = 1 ∨ b.Prime ∧ a = 1
  证明: by
  simp only [irreducible_mul_iff, ← irreducible_iff_nat_prime, Nat.isUnit_iff]

Depends on / 依赖: Nat.isUnit_iff, irreducible_iff_nat_prime, irreducible_mul_iff, isUnit_iff
-/
theorem prime_mul_iff {a b : Nat} : Nat.Prime (a * b) ↔ a.Prime ∧ b = 1 ∨ b.Prime ∧ a = 1 := by
  simp only [irreducible_mul_iff, ← irreducible_iff_nat_prime, Nat.isUnit_iff]

/--
theorem `not_prime_mul` / 定理 `not_prime_mul`

English:
theorem not_prime_mul
  given: {a b : Nat} (a1 : a != 1) (b1 : b != 1)
  statement: ¬Prime (a * b)
  proof: by
  simp [prime_mul_iff, *]

中文:
定理 not_prime_mul
  条件: {a b : 自然数} (a1 : a != 1) (b1 : b != 1)
  结论: ¬Prime (a * b)
  证明: by
  simp [prime_mul_iff, *]

Depends on / 依赖: prime_mul_iff
-/
theorem not_prime_mul {a b : Nat} (a1 : a != 1) (b1 : b != 1) : ¬Prime (a * b) := by
  simp [prime_mul_iff, *]

/--
theorem `not_prime_of_mul_eq` / 定理 `not_prime_of_mul_eq`

English:
theorem not_prime_of_mul_eq
  given: {a b n : Nat} (h : a * b = n) (h₁ : a != 1) (h₂ : b != 1)
  statement: ¬Prime n
  proof: h ▸ not_prime_mul h₁ h₂

中文:
定理 not_prime_of_mul_eq
  条件: {a b n : 自然数} (h : a * b = n) (h₁ : a != 1) (h₂ : b != 1)
  结论: ¬Prime n
  证明: h ▸ not_prime_mul h₁ h₂

Depends on / 依赖: not_prime_mul
-/
theorem not_prime_of_mul_eq {a b n : Nat} (h : a * b = n) (h₁ : a != 1) (h₂ : b != 1) : ¬Prime n :=
  h ▸ not_prime_mul h₁ h₂

/--
theorem `Prime.dvd_iff_eq` / 定理 `Prime.dvd_iff_eq`

English:
theorem Prime.dvd_iff_eq
  given: {p a : Nat} (hp : p.Prime) (a1 : a != 1)
  statement: a ∣ p ↔ p = a
  proof: by
  refine ⟨?_, by rintro rfl; rfl⟩
  rintro ⟨j, rfl⟩
  rcases prime_mul_iff.mp hp with (⟨_, rfl⟩ | ⟨_, rfl⟩)
  · exact mul_one _
  · exact (a1 rfl).elim

中文:
定理 Prime.dvd_iff_eq
  条件: {p a : 自然数} (hp : p.Prime) (a1 : a != 1)
  结论: a ∣ p ↔ p = a
  证明: by
  refine ⟨?_, by rintro rfl; rfl⟩
  rintro ⟨j, rfl⟩
  rcases prime_mul_iff.mp hp with (⟨_, rfl⟩ | ⟨_, rfl⟩)
  · exact mul_one _
  · exact (a1 rfl).elim

Depends on / 依赖: mul_one, prime_mul_iff, prime_mul_iff.mp
-/
theorem Prime.dvd_iff_eq {p a : Nat} (hp : p.Prime) (a1 : a != 1) : a ∣ p ↔ p = a := by
  refine ⟨?_, by rintro rfl; rfl⟩
  rintro ⟨j, rfl⟩
  rcases prime_mul_iff.mp hp with (⟨_, rfl⟩ | ⟨_, rfl⟩)
  · exact mul_one _
  · exact (a1 rfl).elim

/--
theorem `Prime.eq_two_or_odd` / 定理 `Prime.eq_two_or_odd`

English:
theorem Prime.eq_two_or_odd
  given: {p : Nat} (hp : Prime p)
  statement: p = 2 ∨ p % 2 = 1
  proof: p.mod_two_eq_zero_or_one.imp_left fun h =>
    ((hp.eq_one_or_self_of_dvd 2 (dvd_of_mod_eq_zero h)).resolve_left (by decide)).symm

中文:
定理 Prime.eq_two_or_odd
  条件: {p : 自然数} (hp : Prime p)
  结论: p = 2 ∨ p % 2 = 1
  证明: p.mod_two_eq_zero_or_one.imp_left fun h =>
    ((hp.eq_one_or_self_of_dvd 2 (dvd_of_mod_eq_zero h)).resolve_left (by decide)).symm

Depends on / 依赖: dvd_of_mod_eq_zero, eq_one_or_self_of_dvd, hp.eq_one_or_self_of_dvd, imp_left, mod_two_eq_zero_or_one, p.mod_two_eq_zero_or_one.imp_left, resolve_left
-/
theorem Prime.eq_two_or_odd {p : Nat} (hp : Prime p) : p = 2 ∨ p % 2 = 1 :=
  p.mod_two_eq_zero_or_one.imp_left fun h =>
    ((hp.eq_one_or_self_of_dvd 2 (dvd_of_mod_eq_zero h)).resolve_left (by decide)).symm

/--
theorem `Prime.eq_two_or_odd'` / 定理 `Prime.eq_two_or_odd'`

English:
theorem Prime.eq_two_or_odd'
  given: {p : Nat} (hp : Prime p)
  statement: p = 2 ∨ Odd p
  proof: Or.imp_right (fun h => ⟨p / 2, (div_add_mod p 2).symm.trans (congr_arg _ h)⟩) hp.eq_two_or_odd

中文:
定理 Prime.eq_two_or_odd'
  条件: {p : 自然数} (hp : Prime p)
  结论: p = 2 ∨ Odd p
  证明: Or.imp_right (fun h => ⟨p / 2, (div_add_mod p 2).symm.trans (congr_arg _ h)⟩) hp.eq_two_or_odd

Depends on / 依赖: Or.imp_right, congr_arg, div_add_mod, eq_two_or_odd, hp.eq_two_or_odd, imp_right, symm.trans
-/
theorem Prime.eq_two_or_odd' {p : Nat} (hp : Prime p) : p = 2 ∨ Odd p :=
  Or.imp_right (fun h => ⟨p / 2, (div_add_mod p 2).symm.trans (congr_arg _ h)⟩) hp.eq_two_or_odd

section

/--
theorem `Prime.five_le_of_ne_two_of_ne_three` / 定理 `Prime.five_le_of_ne_two_of_ne_three`

English:
theorem Prime.five_le_of_ne_two_of_ne_three
  statement: {p : Nat} (hp : p.Prime) (h_two : p != 2)
  proof: by
  by_contra! h
  revert h_two h_three hp
  decide +revert

中文:
定理 Prime.five_le_of_ne_two_of_ne_three
  结论: {p : 自然数} (hp : p.Prime) (h_two : p != 2)
  证明: by
  by_contra! h
  revert h_two h_three hp
  decide +revert

Depends on / 依赖: h_three, h_two, revert
-/
theorem Prime.five_le_of_ne_two_of_ne_three {p : Nat} (hp : p.Prime) (h_two : p != 2)
    (h_three : p != 3) : 5 <= p := by
  by_contra! h
  revert h_two h_three hp
  decide +revert

end

/--
theorem `Prime.pred_pos` / 定理 `Prime.pred_pos`

English:
theorem Prime.pred_pos
  given: {p : Nat} (pp : Prime p)
  statement: 0 < pred p
  proof: lt_pred_iff.2 pp.one_lt

中文:
定理 Prime.pred_pos
  条件: {p : 自然数} (pp : Prime p)
  结论: 0 < pred p
  证明: lt_pred_iff.2 pp.one_lt

Depends on / 依赖: lt_pred_iff, one_lt, pp.one_lt
-/
theorem Prime.pred_pos {p : Nat} (pp : Prime p) : 0 < pred p :=
  lt_pred_iff.2 pp.one_lt

/--
theorem `succ_pred_prime` / 定理 `succ_pred_prime`

English:
theorem succ_pred_prime
  given: {p : Nat} (pp : Prime p)
  statement: succ (pred p) = p
  proof: succ_pred_eq_of_pos pp.pos

中文:
定理 succ_pred_prime
  条件: {p : 自然数} (pp : Prime p)
  结论: succ (pred p) = p
  证明: succ_pred_eq_of_pos pp.pos

Depends on / 依赖: pp.pos, succ_pred_eq_of_pos
-/
theorem succ_pred_prime {p : Nat} (pp : Prime p) : succ (pred p) = p :=
  succ_pred_eq_of_pos pp.pos

/--
theorem `exists_dvd_of_not_prime` / 定理 `exists_dvd_of_not_prime`

English:
theorem exists_dvd_of_not_prime
  given: {n : Nat} (n2 : 2 <= n) (np : ¬Prime n)
  statement: exists m, m ∣ n ∧ m != 1 ∧ m != n
  proof: ⟨minFac n, minFac_dvd _, ne_of_gt (minFac_prime (ne_of_gt n2)).one_lt,
ne_of_lt (not_prime_iff_minFac_lt n2).1 np⟩

中文:
定理 exists_dvd_of_not_prime
  条件: {n : 自然数} (n2 : 2 <= n) (np : ¬Prime n)
  结论: 存在 m, m ∣ n ∧ m != 1 ∧ m != n
  证明: ⟨minFac n, minFac_dvd _, ne_of_gt (minFac_prime (ne_of_gt n2)).one_lt,
ne_of_lt (not_prime_iff_minFac_lt n2).1 np⟩

Depends on / 依赖: minFac, minFac_dvd, minFac_prime, ne_of_gt, ne_of_lt, not_prime_iff_minFac_lt, one_lt
-/
theorem exists_dvd_of_not_prime {n : Nat} (n2 : 2 <= n) (np : ¬Prime n) : exists m, m ∣ n ∧ m != 1 ∧ m != n :=
  ⟨minFac n, minFac_dvd _, ne_of_gt (minFac_prime (ne_of_gt n2)).one_lt,
ne_of_lt (not_prime_iff_minFac_lt n2).1 np⟩

/--
theorem `exists_dvd_of_not_prime2` / 定理 `exists_dvd_of_not_prime2`

English:
theorem exists_dvd_of_not_prime2
  given: {n : Nat} (n2 : 2 <= n) (np : ¬Prime n)
  proof: ⟨minFac n, minFac_dvd _, (minFac_prime (ne_of_gt n2)).two_le,
    (not_prime_iff_minFac_lt n2).1 np⟩

中文:
定理 exists_dvd_of_not_prime2
  条件: {n : 自然数} (n2 : 2 <= n) (np : ¬Prime n)
  证明: ⟨minFac n, minFac_dvd _, (minFac_prime (ne_of_gt n2)).two_le,
    (not_prime_iff_minFac_lt n2).1 np⟩

Depends on / 依赖: minFac, minFac_dvd, minFac_prime, ne_of_gt, not_prime_iff_minFac_lt, two_le
-/
theorem exists_dvd_of_not_prime2 {n : Nat} (n2 : 2 <= n) (np : ¬Prime n) :
    exists m, m ∣ n ∧ 2 <= m ∧ m < n :=
  ⟨minFac n, minFac_dvd _, (minFac_prime (ne_of_gt n2)).two_le,
    (not_prime_iff_minFac_lt n2).1 np⟩

/--
theorem `not_prime_of_dvd_of_ne` / 定理 `not_prime_of_dvd_of_ne`

English:
theorem not_prime_of_dvd_of_ne
  given: {m n : Nat} (h1 : m ∣ n) (h2 : m != 1) (h3 : m != n)
  statement: ¬Prime n
  proof: fun h => Or.elim (h.eq_one_or_self_of_dvd m h1) h2 h3

中文:
定理 not_prime_of_dvd_of_ne
  条件: {m n : 自然数} (h1 : m ∣ n) (h2 : m != 1) (h3 : m != n)
  结论: ¬Prime n
  证明: fun h => Or.elim (h.eq_one_or_self_of_dvd m h1) h2 h3

Depends on / 依赖: Or.elim, eq_one_or_self_of_dvd, h.eq_one_or_self_of_dvd
-/
theorem not_prime_of_dvd_of_ne {m n : Nat} (h1 : m ∣ n) (h2 : m != 1) (h3 : m != n) : ¬Prime n :=
  fun h => Or.elim (h.eq_one_or_self_of_dvd m h1) h2 h3

/--
theorem `not_prime_of_dvd_of_lt` / 定理 `not_prime_of_dvd_of_lt`

English:
theorem not_prime_of_dvd_of_lt
  given: {m n : Nat} (h1 : m ∣ n) (h2 : 2 <= m) (h3 : m < n)
  statement: ¬Prime n
  proof: not_prime_of_dvd_of_ne h1 (ne_of_gt h2) (ne_of_lt h3)

中文:
定理 not_prime_of_dvd_of_lt
  条件: {m n : 自然数} (h1 : m ∣ n) (h2 : 2 <= m) (h3 : m < n)
  结论: ¬Prime n
  证明: not_prime_of_dvd_of_ne h1 (ne_of_gt h2) (ne_of_lt h3)

Depends on / 依赖: ne_of_gt, ne_of_lt, not_prime_of_dvd_of_ne
-/
theorem not_prime_of_dvd_of_lt {m n : Nat} (h1 : m ∣ n) (h2 : 2 <= m) (h3 : m < n) : ¬Prime n :=
  not_prime_of_dvd_of_ne h1 (ne_of_gt h2) (ne_of_lt h3)

/--
theorem `not_prime_iff_exists_dvd_ne` / 定理 `not_prime_iff_exists_dvd_ne`

English:
theorem not_prime_iff_exists_dvd_ne
  given: {n : Nat} (h : 2 <= n)
  statement: (¬Prime n) ↔ exists m, m ∣ n ∧ m != 1 ∧ m != n
  proof: ⟨exists_dvd_of_not_prime h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_ne h1 h2 h3⟩

中文:
定理 not_prime_iff_exists_dvd_ne
  条件: {n : 自然数} (h : 2 <= n)
  结论: (¬Prime n) ↔ 存在 m, m ∣ n ∧ m != 1 ∧ m != n
  证明: ⟨exists_dvd_of_not_prime h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_ne h1 h2 h3⟩

Depends on / 依赖: exists_dvd_of_not_prime, not_prime_of_dvd_of_ne
-/
theorem not_prime_iff_exists_dvd_ne {n : Nat} (h : 2 <= n) : (¬Prime n) ↔ exists m, m ∣ n ∧ m != 1 ∧ m != n :=
  ⟨exists_dvd_of_not_prime h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_ne h1 h2 h3⟩

/--
theorem `not_prime_iff_exists_dvd_lt` / 定理 `not_prime_iff_exists_dvd_lt`

English:
theorem not_prime_iff_exists_dvd_lt
  given: {n : Nat} (h : 2 <= n)
  statement: (¬Prime n) ↔ exists m, m ∣ n ∧ 2 <= m ∧ m < n
  proof: ⟨exists_dvd_of_not_prime2 h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_lt h1 h2 h3⟩

中文:
定理 not_prime_iff_exists_dvd_lt
  条件: {n : 自然数} (h : 2 <= n)
  结论: (¬Prime n) ↔ 存在 m, m ∣ n ∧ 2 <= m ∧ m < n
  证明: ⟨exists_dvd_of_not_prime2 h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_lt h1 h2 h3⟩

Depends on / 依赖: exists_dvd_of_not_prime2, not_prime_of_dvd_of_lt
-/
theorem not_prime_iff_exists_dvd_lt {n : Nat} (h : 2 <= n) : (¬Prime n) ↔ exists m, m ∣ n ∧ 2 <= m ∧ m < n :=
  ⟨exists_dvd_of_not_prime2 h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_lt h1 h2 h3⟩

/--
theorem `not_prime_iff_exists_mul_eq` / 定理 `not_prime_iff_exists_mul_eq`

English:
theorem not_prime_iff_exists_mul_eq
  given: {n : Nat} (h : 2 <= n)
  proof: by
  rw [prime_iff_not_exists_mul_eq]; rw [and_iff_right h]; rw [Classical.not_not]

中文:
定理 not_prime_iff_exists_mul_eq
  条件: {n : 自然数} (h : 2 <= n)
  证明: by
  rw [prime_iff_not_exists_mul_eq]; rw [and_iff_right h]; rw [Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, and_iff_right, not_not, prime_iff_not_exists_mul_eq
-/
theorem not_prime_iff_exists_mul_eq {n : Nat} (h : 2 <= n) :
    (¬Prime n) ↔ exists a b, a < n ∧ b < n ∧ a * b = n := by
  rw [prime_iff_not_exists_mul_eq]; rw [and_iff_right h]; rw [Classical.not_not]

/--
theorem `dvd_of_forall_prime_mul_dvd` / 定理 `dvd_of_forall_prime_mul_dvd`

English:
theorem dvd_of_forall_prime_mul_dvd
  statement: {a b : Nat}
  proof: by
  obtain rfl | ha := eq_or_ne a 1
  · apply one_dvd
  obtain ⟨p, hp⟩ := exists_prime_and_dvd ha
  exact _root_.trans (dvd_mul_left a p) (hdvd p hp.1 hp.2)

中文:
定理 dvd_of_forall_prime_mul_dvd
  结论: {a b : 自然数}
  证明: by
  obtain rfl | ha := eq_or_ne a 1
  · apply one_dvd
  obtain ⟨p, hp⟩ := exists_prime_and_dvd ha
  exact _root_.trans (dvd_mul_left a p) (hdvd p hp.1 hp.2)

Depends on / 依赖: _root_, _root_.trans, dvd_mul_left, eq_or_ne, exists_prime_and_dvd, one_dvd
-/
theorem dvd_of_forall_prime_mul_dvd {a b : Nat}
    (hdvd : forall p : Nat, p.Prime -> p ∣ a -> p * a ∣ b) : a ∣ b := by
  obtain rfl | ha := eq_or_ne a 1
  · apply one_dvd
  obtain ⟨p, hp⟩ := exists_prime_and_dvd ha
  exact _root_.trans (dvd_mul_left a p) (hdvd p hp.1 hp.2)

/--
theorem `Prime.even_iff` / 定理 `Prime.even_iff`

English:
theorem Prime.even_iff
  given: {p : Nat} (hp : Prime p)
  statement: Even p ↔ p = 2
  proof: by
  rw [even_iff_two_dvd]; rw [prime_dvd_prime_iff_eq prime_two hp]; rw [eq_comm]

中文:
定理 Prime.even_iff
  条件: {p : 自然数} (hp : Prime p)
  结论: Even p ↔ p = 2
  证明: by
  rw [even_iff_two_dvd]; rw [prime_dvd_prime_iff_eq prime_two hp]; rw [eq_comm]

Depends on / 依赖: eq_comm, even_iff_two_dvd, prime_dvd_prime_iff_eq, prime_two
-/
theorem Prime.even_iff {p : Nat} (hp : Prime p) : Even p ↔ p = 2 := by
  rw [even_iff_two_dvd]; rw [prime_dvd_prime_iff_eq prime_two hp]; rw [eq_comm]

/--
theorem `Prime.odd_iff` / 定理 `Prime.odd_iff`

English:
theorem Prime.odd_iff
  given: {p : Nat} (hp : Prime p)
  statement: Odd p ↔ 3 <= p
  proof: by
  rw [← not_iff_not]; rw [not_odd_iff_even]; rw [hp.even_iff]; rw [not_le]
  grind [hp.two_le]

中文:
定理 Prime.odd_iff
  条件: {p : 自然数} (hp : Prime p)
  结论: Odd p ↔ 3 <= p
  证明: by
  rw [← not_iff_not]; rw [not_odd_iff_even]; rw [hp.even_iff]; rw [not_le]
  grind [hp.two_le]

Depends on / 依赖: even_iff, hp.even_iff, hp.two_le, not_iff_not, not_le, not_odd_iff_even, two_le
-/
theorem Prime.odd_iff {p : Nat} (hp : Prime p) : Odd p ↔ 3 <= p := by
  rw [← not_iff_not]; rw [not_odd_iff_even]; rw [hp.even_iff]; rw [not_le]
  grind [hp.two_le]

/--
theorem `Prime.odd_of_ne_two` / 定理 `Prime.odd_of_ne_two`

English:
theorem Prime.odd_of_ne_two
  given: {p : Nat} (hp : p.Prime) (h_two : p != 2)
  statement: Odd p
  proof: hp.eq_two_or_odd'.resolve_left h_two

中文:
定理 Prime.odd_of_ne_two
  条件: {p : 自然数} (hp : p.Prime) (h_two : p != 2)
  结论: Odd p
  证明: hp.eq_two_or_odd'.resolve_left h_two

Depends on / 依赖: eq_two_or_odd, h_two, hp.eq_two_or_odd, resolve_left
-/
theorem Prime.odd_of_ne_two {p : Nat} (hp : p.Prime) (h_two : p != 2) : Odd p :=
  hp.eq_two_or_odd'.resolve_left h_two

/--
theorem `Prime.even_sub_one` / 定理 `Prime.even_sub_one`

English:
theorem Prime.even_sub_one
  given: {p : Nat} (hp : p.Prime) (h2 : p != 2)
  statement: Even (p - 1)
  proof: let ⟨n, hn⟩ := hp.odd_of_ne_two h2; ⟨n, by rw [hn, Nat.add_sub_cancel, two_mul]⟩

中文:
定理 Prime.even_sub_one
  条件: {p : 自然数} (hp : p.Prime) (h2 : p != 2)
  结论: Even (p - 1)
  证明: let ⟨n, hn⟩ := hp.odd_of_ne_two h2; ⟨n, by rw [hn, Nat.add_sub_cancel, two_mul]⟩

Depends on / 依赖: Nat.add_sub_cancel, add_sub_cancel, hp.odd_of_ne_two, odd_of_ne_two, two_mul
-/
theorem Prime.even_sub_one {p : Nat} (hp : p.Prime) (h2 : p != 2) : Even (p - 1) :=
  let ⟨n, hn⟩ := hp.odd_of_ne_two h2; ⟨n, by rw [hn, Nat.add_sub_cancel, two_mul]⟩

/--
theorem `Prime.mod_two_eq_one_iff_ne_two` / 定理 `Prime.mod_two_eq_one_iff_ne_two`

English:
theorem Prime.mod_two_eq_one_iff_ne_two
  given: {p : Nat} (hp : p.Prime)
  statement: p % 2 = 1 ↔ p != 2
  proof: by
  refine ⟨fun h hf => ?_, hp.eq_two_or_odd.resolve_left⟩
  rw [hf] at h
  simp at h

中文:
定理 Prime.mod_two_eq_one_iff_ne_two
  条件: {p : 自然数} (hp : p.Prime)
  结论: p % 2 = 1 ↔ p != 2
  证明: by
  refine ⟨fun h hf => ?_, hp.eq_two_or_odd.resolve_left⟩
  rw [hf] at h
  simp at h

Depends on / 依赖: eq_two_or_odd, hp.eq_two_or_odd.resolve_left, resolve_left
-/
theorem Prime.mod_two_eq_one_iff_ne_two {p : Nat} (hp : p.Prime) : p % 2 = 1 ↔ p != 2 := by
  refine ⟨fun h hf => ?_, hp.eq_two_or_odd.resolve_left⟩
  rw [hf] at h
  simp at h

/--
theorem `coprime_of_dvd'` / 定理 `coprime_of_dvd'`

English:
theorem coprime_of_dvd'
  given: {m n : Nat} (H : forall k, Prime k -> k ∣ m -> k ∣ n -> k ∣ 1)
  statement: Coprime m n
  proof: coprime_of_dvd fun k kp km kn => not_le_of_gt kp.one_lt le_of_dvd Nat.one_pos H k kp km kn

中文:
定理 coprime_of_dvd'
  条件: {m n : 自然数} (H : 对任意 k, Prime k -> k ∣ m -> k ∣ n -> k ∣ 1)
  结论: Coprime m n
  证明: coprime_of_dvd fun k kp km kn => not_le_of_gt kp.one_lt le_of_dvd Nat.one_pos H k kp km kn

Depends on / 依赖: Nat.one_pos, coprime_of_dvd, kp.one_lt, le_of_dvd, not_le_of_gt, one_lt, one_pos
-/
theorem coprime_of_dvd' {m n : Nat} (H : forall k, Prime k -> k ∣ m -> k ∣ n -> k ∣ 1) : Coprime m n :=
coprime_of_dvd fun k kp km kn => not_le_of_gt kp.one_lt le_of_dvd Nat.one_pos H k kp km kn

/--
theorem `Prime.dvd_iff_not_coprime` / 定理 `Prime.dvd_iff_not_coprime`

English:
theorem Prime.dvd_iff_not_coprime
  given: {p n : Nat} (pp : Prime p)
  statement: p ∣ n ↔ ¬Coprime p n
  proof: iff_not_comm.2 pp.coprime_iff_not_dvd

中文:
定理 Prime.dvd_iff_not_coprime
  条件: {p n : 自然数} (pp : Prime p)
  结论: p ∣ n ↔ ¬Coprime p n
  证明: iff_not_comm.2 pp.coprime_iff_not_dvd

Depends on / 依赖: coprime_iff_not_dvd, iff_not_comm, pp.coprime_iff_not_dvd
-/
theorem Prime.dvd_iff_not_coprime {p n : Nat} (pp : Prime p) : p ∣ n ↔ ¬Coprime p n :=
  iff_not_comm.2 pp.coprime_iff_not_dvd

/--
theorem `Prime.not_coprime_iff_dvd` / 定理 `Prime.not_coprime_iff_dvd`

English:
theorem Prime.not_coprime_iff_dvd
  given: {m n : Nat}
  statement: ¬Coprime m n ↔ exists p, Prime p ∧ p ∣ m ∧ p ∣ n
  proof: by
  apply Iff.intro
  · intro h
    exact
      ⟨minFac (gcd m n), minFac_prime h, (minFac_dvd (gcd m n)).trans (gcd_dvd_left m n),
        (minFac_dvd (gcd m n)).trans (gcd_dvd_right m n)⟩
  · intro h
    obtain ⟨p, hp⟩ := h
    apply Nat.not_coprime_of_dvd_of_dvd (Prime.one_lt hp.1) hp.2.1 hp.2.2

中文:
定理 Prime.not_coprime_iff_dvd
  条件: {m n : 自然数}
  结论: ¬Coprime m n ↔ 存在 p, Prime p ∧ p ∣ m ∧ p ∣ n
  证明: by
  apply Iff.intro
  · intro h
    exact
      ⟨minFac (gcd m n), minFac_prime h, (minFac_dvd (gcd m n)).trans (gcd_dvd_left m n),
        (minFac_dvd (gcd m n)).trans (gcd_dvd_right m n)⟩
  · intro h
    obtain ⟨p, hp⟩ := h
    apply Nat.not_coprime_of_dvd_of_dvd (Prime.one_lt hp.1) hp.2.1 hp.2.2

Depends on / 依赖: Iff.intro, Nat.not_coprime_of_dvd_of_dvd, Prime.one_lt, gcd_dvd_left, gcd_dvd_right, minFac, minFac_dvd, minFac_prime, not_coprime_of_dvd_of_dvd, one_lt
-/
theorem Prime.not_coprime_iff_dvd {m n : Nat} : ¬Coprime m n ↔ exists p, Prime p ∧ p ∣ m ∧ p ∣ n := by
  apply Iff.intro
  · intro h
    exact
      ⟨minFac (gcd m n), minFac_prime h, (minFac_dvd (gcd m n)).trans (gcd_dvd_left m n),
        (minFac_dvd (gcd m n)).trans (gcd_dvd_right m n)⟩
  · intro h
    obtain ⟨p, hp⟩ := h
    apply Nat.not_coprime_of_dvd_of_dvd (Prime.one_lt hp.1) hp.2.1 hp.2.2

/--
lemma `coprime_of_lt_minFac` / 引理 `coprime_of_lt_minFac`

English:
lemma coprime_of_lt_minFac
  given: {n m : Nat} (h₀ : m != 0) (h : m < minFac n)
  statement: Coprime n m
  proof: by
  rw [← not_not (a := n.Coprime m)]; rw [Prime.not_coprime_iff_dvd]
  push Not
  exact fun p hp hn hm =>
    ((le_of_dvd (by lia) hm).trans_lt <| h.trans_le <| minFac_le_of_dvd hp.two_le hn).false

中文:
引理 coprime_of_lt_minFac
  条件: {n m : 自然数} (h₀ : m != 0) (h : m < minFac n)
  结论: Coprime n m
  证明: by
  rw [← not_not (a := n.Coprime m)]; rw [Prime.not_coprime_iff_dvd]
  push Not
  exact fun p hp hn hm =>
    ((le_of_dvd (by lia) hm).trans_lt <| h.trans_le <| minFac_le_of_dvd hp.two_le hn).false

Depends on / 依赖: Coprime, Prime.not_coprime_iff_dvd, h.trans_le, hp.two_le, le_of_dvd, minFac_le_of_dvd, n.Coprime, not_coprime_iff_dvd, not_not, trans_le, trans_lt, two_le
-/
lemma coprime_of_lt_minFac {n m : Nat} (h₀ : m != 0) (h : m < minFac n) : Coprime n m := by
  rw [← not_not (a := n.Coprime m)]; rw [Prime.not_coprime_iff_dvd]
  push Not
  exact fun p hp hn hm =>
    ((le_of_dvd (by lia) hm).trans_lt <| h.trans_le <| minFac_le_of_dvd hp.two_le hn).false

/--
lemma `gcd_eq_one_of_lt_minFac` / 引理 `gcd_eq_one_of_lt_minFac`

English:
lemma gcd_eq_one_of_lt_minFac
  given: {n m : Nat} (h₀ : m != 0) (h : m < minFac n)
  statement: n.gcd m = 1
  proof: coprime_iff_gcd_eq_one.mp coprime_of_lt_minFac h₀ h

中文:
引理 gcd_eq_one_of_lt_minFac
  条件: {n m : 自然数} (h₀ : m != 0) (h : m < minFac n)
  结论: n.gcd m = 1
  证明: coprime_iff_gcd_eq_one.mp coprime_of_lt_minFac h₀ h

Depends on / 依赖: coprime_iff_gcd_eq_one, coprime_iff_gcd_eq_one.mp, coprime_of_lt_minFac
-/
lemma gcd_eq_one_of_lt_minFac {n m : Nat} (h₀ : m != 0) (h : m < minFac n) : n.gcd m = 1 :=
coprime_iff_gcd_eq_one.mp coprime_of_lt_minFac h₀ h

/--
theorem `Prime.not_dvd_mul` / 定理 `Prime.not_dvd_mul`

English:
theorem Prime.not_dvd_mul
  given: {p m n : Nat} (pp : Prime p) (Hm : ¬p ∣ m) (Hn : ¬p ∣ n)
  statement: ¬p ∣ m * n
  proof: mt pp.dvd_mul.1 by simp [Hm, Hn]

中文:
定理 Prime.not_dvd_mul
  条件: {p m n : 自然数} (pp : Prime p) (Hm : ¬p ∣ m) (Hn : ¬p ∣ n)
  结论: ¬p ∣ m * n
  证明: mt pp.dvd_mul.1 by simp [Hm, Hn]
-/
theorem Prime.not_dvd_mul {p m n : Nat} (pp : Prime p) (Hm : ¬p ∣ m) (Hn : ¬p ∣ n) : ¬p ∣ m * n :=
mt pp.dvd_mul.1 by simp [Hm, Hn]

/--
lemma `coprime_two_left` / 引理 `coprime_two_left`

English:
lemma coprime_two_left
  statement: Coprime 2 n ↔ Odd n
  proof: by
  rw [prime_two.coprime_iff_not_dvd]; rw [← not_even_iff_odd]; rw [even_iff_two_dvd]

中文:
引理 coprime_two_left
  结论: Coprime 2 n ↔ Odd n
  证明: by
  rw [prime_two.coprime_iff_not_dvd]; rw [← not_even_iff_odd]; rw [even_iff_two_dvd]
-/
@[simp] lemma coprime_two_left : Coprime 2 n ↔ Odd n := by
  rw [prime_two.coprime_iff_not_dvd]; rw [← not_even_iff_odd]; rw [even_iff_two_dvd]

/--
lemma `coprime_two_right` / 引理 `coprime_two_right`

English:
lemma coprime_two_right
  statement: n.Coprime 2 ↔ Odd n
  proof: coprime_comm.trans coprime_two_left

protected alias ⟨Coprime.odd_of_left, _root_.Odd.coprime_two_left⟩ := coprime_two_left
protected alias ⟨Coprime.odd_of_right, _root_.Odd.coprime_two_right⟩ := coprime_two_right

中文:
引理 coprime_two_right
  结论: n.Coprime 2 ↔ Odd n
  证明: coprime_comm.trans coprime_two_left

protected alias ⟨Coprime.odd_of_left, _root_.Odd.coprime_two_left⟩ := coprime_two_left
protected alias ⟨Coprime.odd_of_right, _root_.Odd.coprime_two_right⟩ := coprime_two_right
-/
@[simp] lemma coprime_two_right : n.Coprime 2 ↔ Odd n := coprime_comm.trans coprime_two_left

protected alias ⟨Coprime.odd_of_left, _root_.Odd.coprime_two_left⟩ := coprime_two_left
protected alias ⟨Coprime.odd_of_right, _root_.Odd.coprime_two_right⟩ := coprime_two_right

/--
theorem `Prime.dvd_of_dvd_pow` / 定理 `Prime.dvd_of_dvd_pow`

English:
theorem Prime.dvd_of_dvd_pow
  given: {p m n : Nat} (pp : Prime p) (h : p ∣ m ^ n)
  statement: p ∣ m
  proof: pp.prime.dvd_of_dvd_pow h

中文:
定理 Prime.dvd_of_dvd_pow
  条件: {p m n : 自然数} (pp : Prime p) (h : p ∣ m ^ n)
  结论: p ∣ m
  证明: pp.prime.dvd_of_dvd_pow h
-/
theorem Prime.dvd_of_dvd_pow {p m n : Nat} (pp : Prime p) (h : p ∣ m ^ n) : p ∣ m :=
  pp.prime.dvd_of_dvd_pow h

/--
theorem `Prime.not_prime_pow'` / 定理 `Prime.not_prime_pow'`

English:
theorem Prime.not_prime_pow'
  given: {x n : Nat} (hn : n != 1)
  statement: ¬(x ^ n).Prime
  proof: not_irreducible_pow hn

中文:
定理 Prime.not_prime_pow'
  条件: {x n : 自然数} (hn : n != 1)
  结论: ¬(x ^ n).Prime
  证明: not_irreducible_pow hn

Depends on / 依赖: not_irreducible_pow
-/
theorem Prime.not_prime_pow' {x n : Nat} (hn : n != 1) : ¬(x ^ n).Prime :=
  not_irreducible_pow hn

/--
theorem `Prime.not_prime_pow` / 定理 `Prime.not_prime_pow`

English:
theorem Prime.not_prime_pow
  given: {x n : Nat} (hn : 2 <= n)
  statement: ¬(x ^ n).Prime
  proof: not_prime_pow' ((two_le_iff _).mp hn).2

中文:
定理 Prime.not_prime_pow
  条件: {x n : 自然数} (hn : 2 <= n)
  结论: ¬(x ^ n).Prime
  证明: not_prime_pow' ((two_le_iff _).mp hn).2

Depends on / 依赖: not_prime_pow, two_le_iff
-/
theorem Prime.not_prime_pow {x n : Nat} (hn : 2 <= n) : ¬(x ^ n).Prime :=
  not_prime_pow' ((two_le_iff _).mp hn).2

/--
theorem `Prime.eq_one_of_pow` / 定理 `Prime.eq_one_of_pow`

English:
theorem Prime.eq_one_of_pow
  given: {x n : Nat} (h : (x ^ n).Prime)
  statement: n = 1
  proof: not_imp_not.mp Prime.not_prime_pow' h

中文:
定理 Prime.eq_one_of_pow
  条件: {x n : 自然数} (h : (x ^ n).Prime)
  结论: n = 1
  证明: not_imp_not.mp Prime.not_prime_pow' h

Depends on / 依赖: Prime.not_prime_pow, not_imp_not, not_imp_not.mp, not_prime_pow
-/
theorem Prime.eq_one_of_pow {x n : Nat} (h : (x ^ n).Prime) : n = 1 :=
  not_imp_not.mp Prime.not_prime_pow' h

/--
theorem `Prime.pow_eq_iff` / 定理 `Prime.pow_eq_iff`

English:
theorem Prime.pow_eq_iff
  given: {p a k : Nat} (hp : p.Prime)
  statement: a ^ k = p ↔ a = p ∧ k = 1
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, pow_one]⟩
  rw [← h] at hp
  rw [← h]; rw [hp.eq_one_of_pow]; rw [eq_self_iff_true]; rw [_root_.and_true]; rw [pow_one]

中文:
定理 Prime.pow_eq_iff
  条件: {p a k : 自然数} (hp : p.Prime)
  结论: a ^ k = p ↔ a = p ∧ k = 1
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, pow_one]⟩
  rw [← h] at hp
  rw [← h]; rw [hp.eq_one_of_pow]; rw [eq_self_iff_true]; rw [_root_.and_true]; rw [pow_one]

Depends on / 依赖: _root_, _root_.and_true, and_true, eq_one_of_pow, eq_self_iff_true, hp.eq_one_of_pow, pow_one
-/
theorem Prime.pow_eq_iff {p a k : Nat} (hp : p.Prime) : a ^ k = p ↔ a = p ∧ k = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, pow_one]⟩
  rw [← h] at hp
  rw [← h]; rw [hp.eq_one_of_pow]; rw [eq_self_iff_true]; rw [_root_.and_true]; rw [pow_one]

/--
theorem `Prime.mul_eq_prime_sq_iff` / 定理 `Prime.mul_eq_prime_sq_iff`

English:
theorem Prime.mul_eq_prime_sq_iff
  given: {x y p : Nat} (hp : p.Prime) (hx : x != 1) (hy : y != 1)
  proof: by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => h₁.symm ▸ h₂.symm ▸ (sq _).symm⟩
  have pdvdxy : p ∣ x * y := by rw [h]; simp [sq]
  -- Could be `wlog := hp.dvd_mul.1 pdvdxy using x y`, but that imports more than we want.
  suffices forall x' y' : Nat, x' != 1 -> y' != 1 -> x' * y' = p ^ 2 -> p ∣ x' -> x'

中文:
定理 Prime.mul_eq_prime_sq_iff
  条件: {x y p : 自然数} (hp : p.Prime) (hx : x != 1) (hy : y != 1)
  证明: by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => h₁.symm ▸ h₂.symm ▸ (sq _).symm⟩
  have pdvdxy : p ∣ x * y := by rw [h]; simp [sq]
  -- Could be `wlog := hp.dvd_mul.1 pdvdxy using x y`, but that imports more than we want.
  suffices forall x' y' : Nat, x' != 1 -> y' != 1 -> x' * y' = p ^ 2 -> p ∣ x' -> x'

Depends on / 依赖: pdvdxy
-/
theorem Prime.mul_eq_prime_sq_iff {x y p : Nat} (hp : p.Prime) (hx : x != 1) (hy : y != 1) :
    x * y = p ^ 2 ↔ x = p ∧ y = p := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => h₁.symm ▸ h₂.symm ▸ (sq _).symm⟩
  have pdvdxy : p ∣ x * y := by rw [h]; simp [sq]
  -- Could be `wlog := hp.dvd_mul.1 pdvdxy using x y`, but that imports more than we want.
  suffices forall x' y' : Nat, x' != 1 -> y' != 1 -> x' * y' = p ^ 2 -> p ∣ x' -> x' = p ∧ y' = p by
    obtain hx | hy := hp.dvd_mul.1 pdvdxy <;>
      [skip; rw [And.comm]] <;>
      [skip; rw [mul_comm] at h pdvdxy] <;>
      apply this <;>
      assumption
  rintro x y hx hy h ⟨a, ha⟩
  have : a ∣ p := ⟨y, by rwa [ha, sq, mul_assoc, mul_right_inj' hp.ne_zero, eq_comm] at h⟩
  obtain rfl | hap := (Nat.dvd_prime hp).mp ‹a ∣ p›
  · rw [mul_one] at ha
    subst ha
    simp only [sq, mul_right_inj' hp.ne_zero] at h
    subst h
    exact ⟨rfl, rfl⟩
  · refine (hy ?_).elim
    subst hap
    subst ha
    rw [sq]; rw [Nat.mul_eq_left (Nat.mul_ne_zero hp.ne_zero hp.ne_zero)] at h
    exact h

/--
theorem `Prime.coprime_pow_of_not_dvd` / 定理 `Prime.coprime_pow_of_not_dvd`

English:
theorem Prime.coprime_pow_of_not_dvd
  given: {p m a : Nat} (pp : Prime p) (h : ¬p ∣ a)
  statement: Coprime a (p ^ m)
  proof: (pp.coprime_iff_not_dvd.2 h).symm.pow_right _

中文:
定理 Prime.coprime_pow_of_not_dvd
  条件: {p m a : 自然数} (pp : Prime p) (h : ¬p ∣ a)
  结论: Coprime a (p ^ m)
  证明: (pp.coprime_iff_not_dvd.2 h).symm.pow_right _

Depends on / 依赖: coprime_iff_not_dvd, pow_right, pp.coprime_iff_not_dvd, symm.pow_right
-/
theorem Prime.coprime_pow_of_not_dvd {p m a : Nat} (pp : Prime p) (h : ¬p ∣ a) : Coprime a (p ^ m) :=
  (pp.coprime_iff_not_dvd.2 h).symm.pow_right _

/--
theorem `coprime_primes` / 定理 `coprime_primes`

English:
theorem coprime_primes
  given: {p q : Nat} (pp : Prime p) (pq : Prime q)
  statement: Coprime p q ↔ p != q
  proof: pp.coprime_iff_not_dvd.trans not_congr dvd_prime_two_le pq pp.two_le

中文:
定理 coprime_primes
  条件: {p q : 自然数} (pp : Prime p) (pq : Prime q)
  结论: Coprime p q ↔ p != q
  证明: pp.coprime_iff_not_dvd.trans not_congr dvd_prime_two_le pq pp.two_le

Depends on / 依赖: coprime_iff_not_dvd, dvd_prime_two_le, not_congr, pp.coprime_iff_not_dvd.trans, pp.two_le, two_le
-/
theorem coprime_primes {p q : Nat} (pp : Prime p) (pq : Prime q) : Coprime p q ↔ p != q :=
pp.coprime_iff_not_dvd.trans not_congr dvd_prime_two_le pq pp.two_le

/--
theorem `coprime_pow_primes` / 定理 `coprime_pow_primes`

English:
theorem coprime_pow_primes
  given: {p q : Nat} (n m : Nat) (pp : Prime p) (pq : Prime q) (h : p != q)
  proof: ((coprime_primes pp pq).2 h).pow _ _

中文:
定理 coprime_pow_primes
  条件: {p q : 自然数} (n m : 自然数) (pp : Prime p) (pq : Prime q) (h : p != q)
  证明: ((coprime_primes pp pq).2 h).pow _ _

Depends on / 依赖: coprime_primes
-/
theorem coprime_pow_primes {p q : Nat} (n m : Nat) (pp : Prime p) (pq : Prime q) (h : p != q) :
    Coprime (p ^ n) (q ^ m) :=
  ((coprime_primes pp pq).2 h).pow _ _

/--
theorem `coprime_or_dvd_of_prime` / 定理 `coprime_or_dvd_of_prime`

English:
theorem coprime_or_dvd_of_prime
  given: {p} (pp : Prime p) (i : Nat)
  statement: Coprime p i ∨ p ∣ i
  proof: by
  rw [pp.dvd_iff_not_coprime]; apply em

中文:
定理 coprime_or_dvd_of_prime
  条件: {p} (pp : Prime p) (i : 自然数)
  结论: Coprime p i ∨ p ∣ i
  证明: by
  rw [pp.dvd_iff_not_coprime]; apply em

Depends on / 依赖: dvd_iff_not_coprime, pp.dvd_iff_not_coprime
-/
theorem coprime_or_dvd_of_prime {p} (pp : Prime p) (i : Nat) : Coprime p i ∨ p ∣ i := by
  rw [pp.dvd_iff_not_coprime]; apply em

/--
theorem `coprime_of_lt_prime` / 定理 `coprime_of_lt_prime`

English:
theorem coprime_of_lt_prime
  given: {n p} (ne_zero : n != 0) (hlt : n < p) (pp : Prime p)
  statement: Coprime p n
  proof: (coprime_or_dvd_of_prime pp n).resolve_right fun h => Nat.lt_le_asymm hlt
    (le_of_dvd (Nat.pos_of_ne_zero ne_zero) h)

中文:
定理 coprime_of_lt_prime
  条件: {n p} (ne_zero : n != 0) (hlt : n < p) (pp : Prime p)
  结论: Coprime p n
  证明: (coprime_or_dvd_of_prime pp n).resolve_right fun h => Nat.lt_le_asymm hlt
    (le_of_dvd (Nat.pos_of_ne_zero ne_zero) h)

Depends on / 依赖: Nat.lt_le_asymm, Nat.pos_of_ne_zero, coprime_or_dvd_of_prime, le_of_dvd, lt_le_asymm, ne_zero, pos_of_ne_zero, resolve_right
-/
theorem coprime_of_lt_prime {n p} (ne_zero : n != 0) (hlt : n < p) (pp : Prime p) : Coprime p n :=
  (coprime_or_dvd_of_prime pp n).resolve_right fun h => Nat.lt_le_asymm hlt
    (le_of_dvd (Nat.pos_of_ne_zero ne_zero) h)

/--
theorem `eq_or_coprime_of_le_prime` / 定理 `eq_or_coprime_of_le_prime`

English:
theorem eq_or_coprime_of_le_prime
  given: {n p} (ne_zero : n != 0) (hle : n <= p) (pp : Prime p)
  proof: hle.eq_or_lt.imp Eq.symm fun h => coprime_of_lt_prime ne_zero h pp

中文:
定理 eq_or_coprime_of_le_prime
  条件: {n p} (ne_zero : n != 0) (hle : n <= p) (pp : Prime p)
  证明: hle.eq_or_lt.imp Eq.symm fun h => coprime_of_lt_prime ne_zero h pp

Depends on / 依赖: Eq.symm, coprime_of_lt_prime, eq_or_lt, hle.eq_or_lt.imp, ne_zero
-/
theorem eq_or_coprime_of_le_prime {n p} (ne_zero : n != 0) (hle : n <= p) (pp : Prime p) :
    p = n ∨ Coprime p n :=
  hle.eq_or_lt.imp Eq.symm fun h => coprime_of_lt_prime ne_zero h pp

/--
theorem `prime_eq_prime_of_dvd_pow` / 定理 `prime_eq_prime_of_dvd_pow`

English:
theorem prime_eq_prime_of_dvd_pow
  given: {m p q} (pp : Prime p) (pq : Prime q) (h : p ∣ q ^ m)
  statement: p = q
  proof: (prime_dvd_prime_iff_eq pp pq).mp (pp.dvd_of_dvd_pow h)

中文:
定理 prime_eq_prime_of_dvd_pow
  条件: {m p q} (pp : Prime p) (pq : Prime q) (h : p ∣ q ^ m)
  结论: p = q
  证明: (prime_dvd_prime_iff_eq pp pq).mp (pp.dvd_of_dvd_pow h)

Depends on / 依赖: dvd_of_dvd_pow, pp.dvd_of_dvd_pow, prime_dvd_prime_iff_eq
-/
theorem prime_eq_prime_of_dvd_pow {m p q} (pp : Prime p) (pq : Prime q) (h : p ∣ q ^ m) : p = q :=
  (prime_dvd_prime_iff_eq pp pq).mp (pp.dvd_of_dvd_pow h)

/--
theorem `dvd_prime_pow` / 定理 `dvd_prime_pow`

English:
theorem dvd_prime_pow
  given: {p : Nat} (pp : Prime p) {m i : Nat}
  statement: i ∣ p ^ m ↔ exists k <= m, i = p ^ k
  proof: by
  simp_rw [_root_.dvd_prime_pow (prime_iff.mp pp) m, associated_eq_eq]

中文:
定理 dvd_prime_pow
  条件: {p : 自然数} (pp : Prime p) {m i : 自然数}
  结论: i ∣ p ^ m ↔ 存在 k <= m, i = p ^ k
  证明: by
  simp_rw [_root_.dvd_prime_pow (prime_iff.mp pp) m, associated_eq_eq]

Depends on / 依赖: _root_, _root_.dvd_prime_pow, associated_eq_eq, dvd_prime_pow, prime_iff, prime_iff.mp, simp_rw
-/
theorem dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : i ∣ p ^ m ↔ exists k <= m, i = p ^ k := by
  simp_rw [_root_.dvd_prime_pow (prime_iff.mp pp) m, associated_eq_eq]

/--
theorem `Prime.dvd_mul_of_dvd_ne` / 定理 `Prime.dvd_mul_of_dvd_ne`

English:
theorem Prime.dvd_mul_of_dvd_ne
  statement: {p1 p2 n : Nat} (h_ne : p1 != p2) (pp1 : Prime p1) (pp2 : Prime p2)
  proof: Coprime.mul_dvd_of_dvd_of_dvd ((coprime_primes pp1 pp2).mpr h_ne) h1 h2

中文:
定理 Prime.dvd_mul_of_dvd_ne
  结论: {p1 p2 n : 自然数} (h_ne : p1 != p2) (pp1 : Prime p1) (pp2 : Prime p2)
  证明: Coprime.mul_dvd_of_dvd_of_dvd ((coprime_primes pp1 pp2).mpr h_ne) h1 h2

Depends on / 依赖: Coprime, Coprime.mul_dvd_of_dvd_of_dvd, coprime_primes, h_ne, mul_dvd_of_dvd_of_dvd
-/
theorem Prime.dvd_mul_of_dvd_ne {p1 p2 n : Nat} (h_ne : p1 != p2) (pp1 : Prime p1) (pp2 : Prime p2)
    (h1 : p1 ∣ n) (h2 : p2 ∣ n) : p1 * p2 ∣ n :=
  Coprime.mul_dvd_of_dvd_of_dvd ((coprime_primes pp1 pp2).mpr h_ne) h1 h2

/--
theorem `eq_prime_pow_of_dvd_least_prime_pow` / 定理 `eq_prime_pow_of_dvd_least_prime_pow`

English:
theorem eq_prime_pow_of_dvd_least_prime_pow
  statement: {a p k : Nat} (pp : Prime p) (h₁ : ¬a ∣ p ^ k)
  proof: by
  obtain ⟨l, ⟨h, rfl⟩⟩ := (dvd_prime_pow pp).1 h₂
  congr
  exact le_antisymm h (not_le.1 ((not_congr (pow_dvd_pow_iff_le_right (Prime.one_lt pp))).1 h₁))

中文:
定理 eq_prime_pow_of_dvd_least_prime_pow
  结论: {a p k : 自然数} (pp : Prime p) (h₁ : ¬a ∣ p ^ k)
  证明: by
  obtain ⟨l, ⟨h, rfl⟩⟩ := (dvd_prime_pow pp).1 h₂
  congr
  exact le_antisymm h (not_le.1 ((not_congr (pow_dvd_pow_iff_le_right (Prime.one_lt pp))).1 h₁))

Depends on / 依赖: Prime.one_lt, dvd_prime_pow, le_antisymm, not_congr, not_le, one_lt, pow_dvd_pow_iff_le_right
-/
theorem eq_prime_pow_of_dvd_least_prime_pow {a p k : Nat} (pp : Prime p) (h₁ : ¬a ∣ p ^ k)
    (h₂ : a ∣ p ^ (k + 1)) : a = p ^ (k + 1) := by
  obtain ⟨l, ⟨h, rfl⟩⟩ := (dvd_prime_pow pp).1 h₂
  congr
  exact le_antisymm h (not_le.1 ((not_congr (pow_dvd_pow_iff_le_right (Prime.one_lt pp))).1 h₁))

/--
theorem `ne_one_iff_exists_prime_dvd` / 定理 `ne_one_iff_exists_prime_dvd`

English:
theorem ne_one_iff_exists_prime_dvd
  statement: forall {n}, n != 1 ↔ exists p : Nat, p.Prime ∧ p ∣ n
  proof: n + 2
    have ha : a != 1 := Nat.succ_succ_ne_one n
    simp only [a, true_iff, Ne, not_false_iff, ha]
    exact ⟨a.minFac, Nat.minFac_prime ha, a.minFac_dvd⟩

中文:
定理 ne_one_iff_exists_prime_dvd
  结论: 对任意 {n}, n != 1 ↔ 存在 p : 自然数, p.Prime ∧ p ∣ n
  证明: n + 2
    have ha : a != 1 := Nat.succ_succ_ne_one n
    simp only [a, true_iff, Ne, not_false_iff, ha]
    exact ⟨a.minFac, Nat.minFac_prime ha, a.minFac_dvd⟩
-/
theorem ne_one_iff_exists_prime_dvd : forall {n}, n != 1 ↔ exists p : Nat, p.Prime ∧ p ∣ n
  | 0 => by simpa using Exists.intro 2 Nat.prime_two
  | 1 => by simp [Nat.not_prime_one]
  | n + 2 => by
    let a := n + 2
    have ha : a != 1 := Nat.succ_succ_ne_one n
    simp only [a, true_iff, Ne, not_false_iff, ha]
    exact ⟨a.minFac, Nat.minFac_prime ha, a.minFac_dvd⟩

/--
theorem `eq_one_iff_not_exists_prime_dvd` / 定理 `eq_one_iff_not_exists_prime_dvd`

English:
theorem eq_one_iff_not_exists_prime_dvd
  given: {n : Nat}
  statement: n = 1 ↔ forall p : Nat, p.Prime -> ¬p ∣ n
  proof: by
  simpa using not_iff_not.mpr ne_one_iff_exists_prime_dvd

中文:
定理 eq_one_iff_not_exists_prime_dvd
  条件: {n : 自然数}
  结论: n = 1 ↔ 对任意 p : 自然数, p.Prime -> ¬p ∣ n
  证明: by
  simpa using not_iff_not.mpr ne_one_iff_exists_prime_dvd

Depends on / 依赖: ne_one_iff_exists_prime_dvd, not_iff_not, not_iff_not.mpr
-/
theorem eq_one_iff_not_exists_prime_dvd {n : Nat} : n = 1 ↔ forall p : Nat, p.Prime -> ¬p ∣ n := by
  simpa using not_iff_not.mpr ne_one_iff_exists_prime_dvd

/--
theorem `succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul` / 定理 `succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul`

English:
theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
  statement: {p : Nat} (p_prime : Prime p) {m n k l : Nat}
  proof: by
  have hpd : p ^ (k + l) * p ∣ m * n := by
      let hpmn' : p ^ (succ (k + l)) ∣ m * n := hpmn
      rwa [pow_succ'] at hpmn'
  have hpd2 : p ∣ m * n / p ^ (k + l) := dvd_div_of_mul_dvd hpd
  have hpd3 : p ∣ m * n / (p ^ k * p ^ l) := by simpa [pow_add] using hpd2
  have hpd4 : p ∣ m / p ^ k * (

中文:
定理 succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
  结论: {p : 自然数} (p_prime : Prime p) {m n k l : 自然数}
  证明: by
  have hpd : p ^ (k + l) * p ∣ m * n := by
      let hpmn' : p ^ (succ (k + l)) ∣ m * n := hpmn
      rwa [pow_succ'] at hpmn'
  have hpd2 : p ∣ m * n / p ^ (k + l) := dvd_div_of_mul_dvd hpd
  have hpd3 : p ∣ m * n / (p ^ k * p ^ l) := by simpa [pow_add] using hpd2
  have hpd4 : p ∣ m / p ^ k * (

Depends on / 依赖: Nat.div_mul_div_comm, Prime.dvd_mul, _root_, _root_.pow_succ, div_mul_div_comm, dvd_div_of_mul_dvd, dvd_mul, p_prime, pow_add, pow_succ
-/
theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : Nat} (p_prime : Prime p) {m n k l : Nat}
    (hpm : p ^ k ∣ m) (hpn : p ^ l ∣ n) (hpmn : p ^ (k + l + 1) ∣ m * n) :
    p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n := by
  have hpd : p ^ (k + l) * p ∣ m * n := by
      let hpmn' : p ^ (succ (k + l)) ∣ m * n := hpmn
      rwa [pow_succ'] at hpmn'
  have hpd2 : p ∣ m * n / p ^ (k + l) := dvd_div_of_mul_dvd hpd
  have hpd3 : p ∣ m * n / (p ^ k * p ^ l) := by simpa [pow_add] using hpd2
  have hpd4 : p ∣ m / p ^ k * (n / p ^ l) := by simpa [Nat.div_mul_div_comm hpm hpn] using hpd3
  have hpd5 : p ∣ m / p ^ k ∨ p ∣ n / p ^ l :=
    (Prime.dvd_mul p_prime).1 hpd4
  suffices p ^ k * p ∣ m ∨ p ^ l * p ∣ n by rwa [_root_.pow_succ, _root_.pow_succ]
  exact hpd5.elim (fun h : p ∣ m / p ^ k => Or.inl <| mul_dvd_of_dvd_div hpm h)
fun h : p ∣ n / p ^ l => Or.inr mul_dvd_of_dvd_div hpn h

end Nat
