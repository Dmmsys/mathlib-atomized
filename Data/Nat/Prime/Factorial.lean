/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Basic
/-!
# Prime natural numbers and the factorial operator

-/

public section

open Bool Subtype

open Nat

namespace Nat

/--
theorem `Prime.dvd_factorial` / 定理 `Prime.dvd_factorial`

English:
theorem Prime.dvd_factorial
  statement: forall {n p : Nat} (_ : Prime p), p ∣ n ! ↔ p <= n

中文:
定理 Prime.dvd_factorial
  结论: 对任意 {n p : 自然数} (_ : Prime p), p ∣ n ! ↔ p <= n
-/
theorem Prime.dvd_factorial : forall {n p : Nat} (_ : Prime p), p ∣ n ! ↔ p <= n
  | 0, _, hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
  | n + 1, p, hp => by
    rw [factorial_succ]; rw [hp.dvd_mul]; rw [Prime.dvd_factorial hp]
    exact
      ⟨fun h => h.elim (le_of_dvd (succ_pos _)) le_succ_of_le, fun h =>
(_root_.lt_or_eq_of_le h).elim (Or.inr ∘ le_of_lt_succ) fun h => Or.inl by rw [h]⟩

/--
theorem `coprime_factorial_iff` / 定理 `coprime_factorial_iff`

English:
theorem coprime_factorial_iff
  given: {m n : Nat} (hm : m != 1)
  proof: by
  rw [← not_le]; rw [iff_not_comm]; rw [Nat.Prime.not_coprime_iff_dvd]
  constructor
  · intro h
    exact ⟨m.minFac, minFac_prime hm, minFac_dvd m, Nat.dvd_factorial (minFac_pos m) h⟩
  · rintro ⟨p, hp, hdvd, hdvd'⟩
    exact le_trans (minFac_le_of_dvd hp.two_le hdvd) (hp.dvd_factorial.mp hdvd')

中文:
定理 coprime_factorial_iff
  条件: {m n : 自然数} (hm : m != 1)
  证明: by
  rw [← not_le]; rw [iff_not_comm]; rw [Nat.Prime.not_coprime_iff_dvd]
  constructor
  · intro h
    exact ⟨m.minFac, minFac_prime hm, minFac_dvd m, Nat.dvd_factorial (minFac_pos m) h⟩
  · rintro ⟨p, hp, hdvd, hdvd'⟩
    exact le_trans (minFac_le_of_dvd hp.two_le hdvd) (hp.dvd_factorial.mp hdvd')

Depends on / 依赖: Nat.Prime.not_coprime_iff_dvd, Nat.dvd_factorial, dvd_factorial, hp.dvd_factorial.mp, hp.two_le, iff_not_comm, le_trans, m.minFac, minFac, minFac_dvd, minFac_le_of_dvd, minFac_pos, minFac_prime, not_coprime_iff_dvd, not_le, two_le
-/
theorem coprime_factorial_iff {m n : Nat} (hm : m != 1) :
    m.Coprime n ! ↔ n < m.minFac := by
  rw [← not_le]; rw [iff_not_comm]; rw [Nat.Prime.not_coprime_iff_dvd]
  constructor
  · intro h
    exact ⟨m.minFac, minFac_prime hm, minFac_dvd m, Nat.dvd_factorial (minFac_pos m) h⟩
  · rintro ⟨p, hp, hdvd, hdvd'⟩
    exact le_trans (minFac_le_of_dvd hp.two_le hdvd) (hp.dvd_factorial.mp hdvd')

/--
lemma `Prime.coprime_factorial_of_lt` / 引理 `Prime.coprime_factorial_of_lt`

English:
lemma Prime.coprime_factorial_of_lt
  given: {p n : Nat} (hp : p.Prime) (hn : n < p)
  proof: by
  rwa [hp.coprime_iff_not_dvd, hp.dvd_factorial, not_le]

中文:
引理 Prime.coprime_factorial_of_lt
  条件: {p n : 自然数} (hp : p.Prime) (hn : n < p)
  证明: by
  rwa [hp.coprime_iff_not_dvd, hp.dvd_factorial, not_le]

Depends on / 依赖: coprime_iff_not_dvd, dvd_factorial, hp.coprime_iff_not_dvd, hp.dvd_factorial, not_le
-/
lemma Prime.coprime_factorial_of_lt {p n : Nat} (hp : p.Prime) (hn : n < p) :
    p.Coprime n.factorial := by
  rwa [hp.coprime_iff_not_dvd, hp.dvd_factorial, not_le]

/--
lemma `Prime.coprime_descFactorial_of_lt_of_le` / 引理 `Prime.coprime_descFactorial_of_lt_of_le`

English:
lemma Prime.coprime_descFactorial_of_lt_of_le
  given: {p n k : Nat} (hp : p.Prime) (hn : n < p) (hk : k <= n)
  proof: by
  rw [Nat.descFactorial_eq_div hk]
  refine (hp.coprime_factorial_of_lt hn).coprime_div_right ?_
  simp [Nat.factorial_dvd_factorial]

中文:
引理 Prime.coprime_descFactorial_of_lt_of_le
  条件: {p n k : 自然数} (hp : p.Prime) (hn : n < p) (hk : k <= n)
  证明: by
  rw [Nat.descFactorial_eq_div hk]
  refine (hp.coprime_factorial_of_lt hn).coprime_div_right ?_
  simp [Nat.factorial_dvd_factorial]

Depends on / 依赖: Nat.descFactorial_eq_div, Nat.factorial_dvd_factorial, coprime_div_right, coprime_factorial_of_lt, descFactorial_eq_div, factorial_dvd_factorial, hp.coprime_factorial_of_lt
-/
lemma Prime.coprime_descFactorial_of_lt_of_le {p n k : Nat} (hp : p.Prime) (hn : n < p) (hk : k <= n) :
    p.Coprime (n.descFactorial k) := by
  rw [Nat.descFactorial_eq_div hk]
  refine (hp.coprime_factorial_of_lt hn).coprime_div_right ?_
  simp [Nat.factorial_dvd_factorial]

end Nat
