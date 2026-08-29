/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yaël Dillies, Jineon Baek
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Statement of Fermat's Last Theorem

This file states Fermat's Last Theorem. We provide a statement over a general semiring with
specific exponent, along with the usual statement over the naturals.

## Main definitions

* `FermatLastTheoremWith R n`: The statement that only solutions to the Fermat
  equation `a^n + b^n = c^n` in the semiring `R` have `a = 0`, `b = 0` or `c = 0`.

  Note that this statement can certainly be false for certain values of `R` and `n`.
  For example `FermatLastTheoremWith ℝ 3` is false as `1^3 + 1^3 = (2^{1/3})^3`, and
  `FermatLastTheoremWith ℕ 2` is false, as 3^2 + 4^2 = 5^2.

* `FermatLastTheoremFor n` : The statement that the only solutions to `a^n + b^n = c^n` in `ℕ`
  have `a = 0`, `b = 0` or `c = 0`. Again, this statement is not always true, for
  example `FermatLastTheoremFor 1` is false because `2^1 + 2^1 = 4^1`.

* `FermatLastTheorem` : The statement of Fermat's Last Theorem, namely that the only solutions to
  `a^n + b^n = c^n` in `ℕ` when `n ≥ 3` have `a = 0`, `b = 0` or `c = 0`.

## History

Fermat's Last Theorem was an open problem in number theory for hundreds of years, until it was
finally solved by Andrew Wiles, assisted by Richard Taylor, in 1994 (see
[A. Wiles, *Modular elliptic curves and Fermat's last theorem*][Wiles-FLT] and
[R. Taylor and A. Wiles, *Ring-theoretic properties of certain Hecke algebras*][Taylor-Wiles-FLT]).
An ongoing Lean formalisation of the proof, using mathlib as a dependency, is taking place at
https://github.com/ImperialCollegeLondon/FLT .

-/

@[expose] public section

open List

/--
Definition of `FermatLastTheoremWith` / `FermatLastTheoremWith` 的定义

English:
definition FermatLastTheoremWith
  signature: (R : Type*) [Semiring R] (n : Nat)
  body: forall a b c : R, a != 0 -> b != 0 -> c != 0 -> a ^ n + b ^ n != c ^ n

中文:
定义 FermatLastTheoremWith
  签名: (R : 类型) [半环 R] (n : 自然数)
  定义体: forall a b c : R, a != 0 -> b != 0 -> c != 0 -> a ^ n + b ^ n != c ^ n
-/
def FermatLastTheoremWith (R : Type*) [Semiring R] (n : Nat) : Prop :=
  forall a b c : R, a != 0 -> b != 0 -> c != 0 -> a ^ n + b ^ n != c ^ n

/--
Definition of `FermatLastTheoremFor` / `FermatLastTheoremFor` 的定义

English:
definition FermatLastTheoremFor
  signature: (n : Nat)
  body: FermatLastTheoremWith Nat n

中文:
定义 FermatLastTheoremFor
  签名: (n : 自然数)
  定义体: FermatLastTheoremWith Nat n

Depends on / 依赖: FermatLastTheoremWith
-/
def FermatLastTheoremFor (n : Nat) : Prop := FermatLastTheoremWith Nat n

/--
Definition of `FermatLastTheorem` / `FermatLastTheorem` 的定义

English:
definition FermatLastTheorem
  signature: : Prop
  body: forall n >= 3, FermatLastTheoremFor n

中文:
定义 FermatLastTheorem
  签名: : 命题
  定义体: forall n >= 3, FermatLastTheoremFor n

Depends on / 依赖: FermatLastTheoremFor
-/
def FermatLastTheorem : Prop := forall n >= 3, FermatLastTheoremFor n

/--
lemma `fermatLastTheoremFor_zero` / 引理 `fermatLastTheoremFor_zero`

English:
lemma fermatLastTheoremFor_zero
  statement: FermatLastTheoremFor 0
  proof: fun _ _ _ _ _ _ => by simp

中文:
引理 fermatLastTheoremFor_zero
  结论: FermatLastTheoremFor 0
  证明: fun _ _ _ _ _ _ => by simp
-/
lemma fermatLastTheoremFor_zero : FermatLastTheoremFor 0 :=
  fun _ _ _ _ _ _ => by simp

/--
lemma `not_fermatLastTheoremFor_one` / 引理 `not_fermatLastTheoremFor_one`

English:
lemma not_fermatLastTheoremFor_one
  statement: ¬ FermatLastTheoremFor 1
  proof: fun h => h 1 1 2 (by simp) (by simp) (by simp) (by simp)

中文:
引理 not_fermatLastTheoremFor_one
  结论: ¬ FermatLastTheoremFor 1
  证明: fun h => h 1 1 2 (by simp) (by simp) (by simp) (by simp)
-/
lemma not_fermatLastTheoremFor_one : ¬ FermatLastTheoremFor 1 :=
  fun h => h 1 1 2 (by simp) (by simp) (by simp) (by simp)

/--
lemma `not_fermatLastTheoremFor_two` / 引理 `not_fermatLastTheoremFor_two`

English:
lemma not_fermatLastTheoremFor_two
  statement: ¬ FermatLastTheoremFor 2
  proof: fun h => h 3 4 5 (by simp) (by simp) (by simp) (by simp)

中文:
引理 not_fermatLastTheoremFor_two
  结论: ¬ FermatLastTheoremFor 2
  证明: fun h => h 3 4 5 (by simp) (by simp) (by simp) (by simp)
-/
lemma not_fermatLastTheoremFor_two : ¬ FermatLastTheoremFor 2 :=
  fun h => h 3 4 5 (by simp) (by simp) (by simp) (by simp)

variable {R : Type*} [Semiring R] [NoZeroDivisors R] {m n : Nat}

/--
lemma `FermatLastTheoremWith.mono` / 引理 `FermatLastTheoremWith.mono`

English:
lemma FermatLastTheoremWith.mono
  given: (hmn : m ∣ n) (hm : FermatLastTheoremWith R m)
  proof: by
  rintro a b c ha hb hc
  obtain ⟨k, rfl⟩ := hmn
  simp_rw [pow_mul']
  refine hm _ _ _ ?_ ?_ ?_ <;> exact pow_ne_zero _ ‹_›

中文:
引理 FermatLastTheoremWith.mono
  条件: (hmn : m ∣ n) (hm : FermatLastTheoremWith R m)
  证明: by
  rintro a b c ha hb hc
  obtain ⟨k, rfl⟩ := hmn
  simp_rw [pow_mul']
  refine hm _ _ _ ?_ ?_ ?_ <;> exact pow_ne_zero _ ‹_›

Depends on / 依赖: pow_mul, pow_ne_zero, simp_rw
-/
lemma FermatLastTheoremWith.mono (hmn : m ∣ n) (hm : FermatLastTheoremWith R m) :
    FermatLastTheoremWith R n := by
  rintro a b c ha hb hc
  obtain ⟨k, rfl⟩ := hmn
  simp_rw [pow_mul']
  refine hm _ _ _ ?_ ?_ ?_ <;> exact pow_ne_zero _ ‹_›

/--
lemma `FermatLastTheoremFor.mono` / 引理 `FermatLastTheoremFor.mono`

English:
lemma FermatLastTheoremFor.mono
  given: (hmn : m ∣ n) (hm : FermatLastTheoremFor m)
  proof: by
  exact FermatLastTheoremWith.mono hmn hm

中文:
引理 FermatLastTheoremFor.mono
  条件: (hmn : m ∣ n) (hm : FermatLastTheoremFor m)
  证明: by
  exact FermatLastTheoremWith.mono hmn hm

Depends on / 依赖: FermatLastTheoremWith, FermatLastTheoremWith.mono
-/
lemma FermatLastTheoremFor.mono (hmn : m ∣ n) (hm : FermatLastTheoremFor m) :
    FermatLastTheoremFor n := by
  exact FermatLastTheoremWith.mono hmn hm

/--
lemma `fermatLastTheoremWith_nat_int_rat_tfae` / 引理 `fermatLastTheoremWith_nat_int_rat_tfae`

English:
lemma fermatLastTheoremWith_nat_int_rat_tfae
  given: (n : Nat)
  proof: by
  tfae_have 1 -> 2
  | h, a, b, c, ha, hb, hc, habc => by
    obtain hn | hn := n.even_or_odd
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [hn.pow_abs, habc]
    obtain ha | ha := ha.lt_or_gt <;> obtain hb | hb := hb.lt_or_gt <;>
      obtain hc | hc := hc.lt_or_gt
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_neg, neg_pow a, neg_pow b, neg_pow c, ← mul_add, *]
· exact (by positivity : 0 < c ^ n).not_gt habc.symm.trans_lt add_neg (hn.pow_neg ha)
        hn.pow_neg hb
    · refine h b.natAbs c.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, add_neg_eq_iff_eq_add,
        eq_neg_add_iff_add_eq, *]
    · refine h a.natAbs c.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, neg_add_eq_iff_eq_add,
        *]
    · refine h c.natAbs a.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, neg_add_eq_iff_eq_add,
        eq_add_neg_iff_add_eq, *]
    · refine h c.natAbs b.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, add_neg_eq_iff_eq_add,
        *]
· exact (by positivity : 0 < a ^ n + b ^ n).not_gt habc.trans_lt hn.pow_neg hc
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, *]
  tfae_have 2 -> 3
  | h, a, b, c, ha, hb, hc, habc => by
    rw [← Rat.num_ne_zero] at ha hb hc
    refine h (a.num * b.den * c.den) (a.den * b.num * c.den) (a.den * b.den * c.num)
      (by positivity) (by positivity) (by positivity) ?_
    have : (a.den * b.den * c.den : Rat) ^ n != 0 := by positivity
refine Int.cast_injective (div_left_inj' this).1 ?_
    push_cast
    simp only [add_div, ← div_pow, mul_div_mul_comm, div_self (by positivity : (a.den : Rat) != 0),
      div_self (by positivity : (b.den : Rat) != 0), div_self (by positivity : (c.den : Rat) != 0),
      one_mul, mul_one, Rat.num_div_den, habc]
  tfae_have 3 -> 1
  | h, a, b, c => mod_cast h a b c
  tfae_finish

中文:
引理 fermatLastTheoremWith_nat_int_rat_tfae
  条件: (n : 自然数)
  证明: by
  tfae_have 1 -> 2
  | h, a, b, c, ha, hb, hc, habc => by
    obtain hn | hn := n.even_or_odd
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [hn.pow_abs, habc]
    obtain ha | ha := ha.lt_or_gt <;> obtain hb | hb := hb.lt_or_gt <;>
      obtain hc | hc := hc.lt_or_gt
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_neg, neg_pow a, neg_pow b, neg_pow c, ← mul_add, *]
· exact (by positivity : 0 < c ^ n).not_gt habc.symm.trans_lt add_neg (hn.pow_neg ha)
        hn.pow_neg hb
    · refine h b.natAbs c.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, add_neg_eq_iff_eq_add,
        eq_neg_add_iff_add_eq, *]
    · refine h a.natAbs c.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, neg_add_eq_iff_eq_add,
        *]
    · refine h c.natAbs a.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, neg_add_eq_iff_eq_add,
        eq_add_neg_iff_add_eq, *]
    · refine h c.natAbs b.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, add_neg_eq_iff_eq_add,
        *]
· exact (by positivity : 0 < a ^ n + b ^ n).not_gt habc.trans_lt hn.pow_neg hc
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, *]
  tfae_have 2 -> 3
  | h, a, b, c, ha, hb, hc, habc => by
    rw [← Rat.num_ne_zero] at ha hb hc
    refine h (a.num * b.den * c.den) (a.den * b.num * c.den) (a.den * b.den * c.num)
      (by positivity) (by positivity) (by positivity) ?_
    have : (a.den * b.den * c.den : Rat) ^ n != 0 := by positivity
refine Int.cast_injective (div_left_inj' this).1 ?_
    push_cast
    simp only [add_div, ← div_pow, mul_div_mul_comm, div_self (by positivity : (a.den : Rat) != 0),
      div_self (by positivity : (b.den : Rat) != 0), div_self (by positivity : (c.den : Rat) != 0),
      one_mul, mul_one, Rat.num_div_den, habc]
  tfae_have 3 -> 1
  | h, a, b, c => mod_cast h a b c
  tfae_finish

Depends on / 依赖: Int.natCast_inj, a.natAbs, abs_of_neg, b.natAbs, c.natAbs, even_or_odd, ha.lt_or_gt, hb.lt_or_gt, hc.lt_or_gt, hn.pow_abs, lt_or_gt, n.even_or_odd, natAbs, natCast_inj, neg_pow, pow_abs, tfae_have
-/
lemma fermatLastTheoremWith_nat_int_rat_tfae (n : Nat) :
    TFAE [FermatLastTheoremWith Nat n, FermatLastTheoremWith Int n, FermatLastTheoremWith Rat n] := by
  tfae_have 1 -> 2
  | h, a, b, c, ha, hb, hc, habc => by
    obtain hn | hn := n.even_or_odd
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [hn.pow_abs, habc]
    obtain ha | ha := ha.lt_or_gt <;> obtain hb | hb := hb.lt_or_gt <;>
      obtain hc | hc := hc.lt_or_gt
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_neg, neg_pow a, neg_pow b, neg_pow c, ← mul_add, *]
· exact (by positivity : 0 < c ^ n).not_gt habc.symm.trans_lt add_neg (hn.pow_neg ha)
        hn.pow_neg hb
    · refine h b.natAbs c.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, add_neg_eq_iff_eq_add,
        eq_neg_add_iff_add_eq, *]
    · refine h a.natAbs c.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, neg_add_eq_iff_eq_add,
        *]
    · refine h c.natAbs a.natAbs b.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, neg_add_eq_iff_eq_add,
        eq_add_neg_iff_add_eq, *]
    · refine h c.natAbs b.natAbs a.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, abs_of_neg, hn.neg_pow, add_neg_eq_iff_eq_add,
        *]
· exact (by positivity : 0 < a ^ n + b ^ n).not_gt habc.trans_lt hn.pow_neg hc
    · refine h a.natAbs b.natAbs c.natAbs (by positivity) (by positivity) (by positivity)
        (Int.natCast_inj.1 ?_)
      push_cast
      simp only [abs_of_pos, *]
  tfae_have 2 -> 3
  | h, a, b, c, ha, hb, hc, habc => by
    rw [← Rat.num_ne_zero] at ha hb hc
    refine h (a.num * b.den * c.den) (a.den * b.num * c.den) (a.den * b.den * c.num)
      (by positivity) (by positivity) (by positivity) ?_
    have : (a.den * b.den * c.den : Rat) ^ n != 0 := by positivity
refine Int.cast_injective (div_left_inj' this).1 ?_
    push_cast
    simp only [add_div, ← div_pow, mul_div_mul_comm, div_self (by positivity : (a.den : Rat) != 0),
      div_self (by positivity : (b.den : Rat) != 0), div_self (by positivity : (c.den : Rat) != 0),
      one_mul, mul_one, Rat.num_div_den, habc]
  tfae_have 3 -> 1
  | h, a, b, c => mod_cast h a b c
  tfae_finish

/--
lemma `fermatLastTheoremFor_iff_nat` / 引理 `fermatLastTheoremFor_iff_nat`

English:
lemma fermatLastTheoremFor_iff_nat
  given: {n : Nat}
  statement: FermatLastTheoremFor n ↔ FermatLastTheoremWith Nat n
  proof: Iff.rfl

中文:
引理 fermatLastTheoremFor_iff_nat
  条件: {n : 自然数}
  结论: FermatLastTheoremFor n ↔ FermatLastTheoremWith 自然数 n
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma fermatLastTheoremFor_iff_nat {n : Nat} : FermatLastTheoremFor n ↔ FermatLastTheoremWith Nat n :=
  Iff.rfl

/--
lemma `fermatLastTheoremFor_iff_int` / 引理 `fermatLastTheoremFor_iff_int`

English:
lemma fermatLastTheoremFor_iff_int
  given: {n : Nat}
  statement: FermatLastTheoremFor n ↔ FermatLastTheoremWith Int n
  proof: (fermatLastTheoremWith_nat_int_rat_tfae n).out 0 1

中文:
引理 fermatLastTheoremFor_iff_int
  条件: {n : 自然数}
  结论: FermatLastTheoremFor n ↔ FermatLastTheoremWith 整数 n
  证明: (fermatLastTheoremWith_nat_int_rat_tfae n).out 0 1

Depends on / 依赖: fermatLastTheoremWith_nat_int_rat_tfae
-/
lemma fermatLastTheoremFor_iff_int {n : Nat} : FermatLastTheoremFor n ↔ FermatLastTheoremWith Int n :=
  (fermatLastTheoremWith_nat_int_rat_tfae n).out 0 1

/--
lemma `fermatLastTheoremFor_iff_rat` / 引理 `fermatLastTheoremFor_iff_rat`

English:
lemma fermatLastTheoremFor_iff_rat
  given: {n : Nat}
  statement: FermatLastTheoremFor n ↔ FermatLastTheoremWith Rat n
  proof: (fermatLastTheoremWith_nat_int_rat_tfae n).out 0 2

中文:
引理 fermatLastTheoremFor_iff_rat
  条件: {n : 自然数}
  结论: FermatLastTheoremFor n ↔ FermatLastTheoremWith 有理数 n
  证明: (fermatLastTheoremWith_nat_int_rat_tfae n).out 0 2

Depends on / 依赖: fermatLastTheoremWith_nat_int_rat_tfae
-/
lemma fermatLastTheoremFor_iff_rat {n : Nat} : FermatLastTheoremFor n ↔ FermatLastTheoremWith Rat n :=
  (fermatLastTheoremWith_nat_int_rat_tfae n).out 0 2

/--
Definition of `FermatLastTheoremWith'` / `FermatLastTheoremWith'` 的定义

English:
definition FermatLastTheoremWith'
  signature: (R : Type*) [CommSemiring R] (n : Nat)
  body: forall a b c : R, a != 0 -> b != 0 -> c != 0 -> a ^ n + b ^ n = c ^ n ->
    exists d a' b' c', (a = a' * d ∧ b = b' * d ∧ c = c' * d) ∧ (IsUnit a' ∧ IsUnit b' ∧ IsUnit c')

中文:
定义 FermatLastTheoremWith'
  签名: (R : 类型) [交换半环 R] (n : 自然数)
  定义体: forall a b c : R, a != 0 -> b != 0 -> c != 0 -> a ^ n + b ^ n = c ^ n ->
    exists d a' b' c', (a = a' * d ∧ b = b' * d ∧ c = c' * d) ∧ (IsUnit a' ∧ IsUnit b' ∧ IsUnit c')

Depends on / 依赖: IsUnit
-/
def FermatLastTheoremWith' (R : Type*) [CommSemiring R] (n : Nat) : Prop :=
  forall a b c : R, a != 0 -> b != 0 -> c != 0 -> a ^ n + b ^ n = c ^ n ->
    exists d a' b' c', (a = a' * d ∧ b = b' * d ∧ c = c' * d) ∧ (IsUnit a' ∧ IsUnit b' ∧ IsUnit c')

/--
lemma `FermatLastTheoremWith.fermatLastTheoremWith'` / 引理 `FermatLastTheoremWith.fermatLastTheoremWith'`

English:
lemma FermatLastTheoremWith.fermatLastTheoremWith'
  statement: {R : Type*} [CommSemiring R] {n : Nat}
  proof: fun a b c _ _ _ _ => by exfalso; apply h a b c <;> assumption

中文:
引理 FermatLastTheoremWith.fermatLastTheoremWith'
  结论: {R : 类型} [交换半环 R] {n : 自然数}
  证明: fun a b c _ _ _ _ => by exfalso; apply h a b c <;> assumption
-/
lemma FermatLastTheoremWith.fermatLastTheoremWith' {R : Type*} [CommSemiring R] {n : Nat}
    (h : FermatLastTheoremWith R n) : FermatLastTheoremWith' R n :=
  fun a b c _ _ _ _ => by exfalso; apply h a b c <;> assumption

/--
lemma `fermatLastTheoremWith'_of_semifield` / 引理 `fermatLastTheoremWith'_of_semifield`

English:
lemma fermatLastTheoremWith'_of_semifield
  given: (𝕜 : Type*) [Semifield 𝕜] (n : Nat)
  proof: fun a b c ha hb hc _ =>
  ⟨1, a, b, c,
    ⟨(mul_one a).symm, (mul_one b).symm, (mul_one c).symm⟩,
    ⟨ha.isUnit, hb.isUnit, hc.isUnit⟩⟩

中文:
引理 fermatLastTheoremWith'_of_semifield
  条件: (𝕜 : 类型) [半域 𝕜] (n : 自然数)
  证明: fun a b c ha hb hc _ =>
  ⟨1, a, b, c,
    ⟨(mul_one a).symm, (mul_one b).symm, (mul_one c).symm⟩,
    ⟨ha.isUnit, hb.isUnit, hc.isUnit⟩⟩
-/
lemma fermatLastTheoremWith'_of_semifield (𝕜 : Type*) [Semifield 𝕜] (n : Nat) :
    FermatLastTheoremWith' 𝕜 n := fun a b c ha hb hc _ =>
  ⟨1, a, b, c,
    ⟨(mul_one a).symm, (mul_one b).symm, (mul_one c).symm⟩,
    ⟨ha.isUnit, hb.isUnit, hc.isUnit⟩⟩

/--
lemma `FermatLastTheoremWith'.fermatLastTheoremWith` / 引理 `FermatLastTheoremWith'.fermatLastTheoremWith`

English:
lemma FermatLastTheoremWith'.fermatLastTheoremWith
  statement: {R : Type*} [CommSemiring R] [IsDomain R]
  proof: by
  intro a b c ha hb hc heq
  rcases h a b c ha hb hc heq with ⟨d, a', b', c', ⟨rfl, rfl, rfl⟩, ⟨ua, ub, uc⟩⟩
  rw [mul_pow]; rw [mul_pow]; rw [mul_pow]; rw [← add_mul] at heq
exact hn _ _ _ ua ub uc mul_right_cancel₀ (pow_ne_zero _ (right_ne_zero_of_mul ha)) heq

中文:
引理 FermatLastTheoremWith'.fermatLastTheoremWith
  结论: {R : 类型} [交换半环 R] [是整环 R]
  证明: by
  intro a b c ha hb hc heq
  rcases h a b c ha hb hc heq with ⟨d, a', b', c', ⟨rfl, rfl, rfl⟩, ⟨ua, ub, uc⟩⟩
  rw [mul_pow]; rw [mul_pow]; rw [mul_pow]; rw [← add_mul] at heq
exact hn _ _ _ ua ub uc mul_right_cancel₀ (pow_ne_zero _ (right_ne_zero_of_mul ha)) heq
-/
lemma FermatLastTheoremWith'.fermatLastTheoremWith {R : Type*} [CommSemiring R] [IsDomain R]
    {n : Nat} (h : FermatLastTheoremWith' R n)
    (hn : forall a b c : R, IsUnit a -> IsUnit b -> IsUnit c -> a ^ n + b ^ n != c ^ n) :
    FermatLastTheoremWith R n := by
  intro a b c ha hb hc heq
  rcases h a b c ha hb hc heq with ⟨d, a', b', c', ⟨rfl, rfl, rfl⟩, ⟨ua, ub, uc⟩⟩
  rw [mul_pow]; rw [mul_pow]; rw [mul_pow]; rw [← add_mul] at heq
exact hn _ _ _ ua ub uc mul_right_cancel₀ (pow_ne_zero _ (right_ne_zero_of_mul ha)) heq

/--
lemma `fermatLastTheoremWith'_iff_fermatLastTheoremWith` / 引理 `fermatLastTheoremWith'_iff_fermatLastTheoremWith`

English:
lemma fermatLastTheoremWith'_iff_fermatLastTheoremWith
  statement: {R : Type*} [CommSemiring R] [IsDomain R]
  proof: Iff.intro (fun h => h.fermatLastTheoremWith hn) (fun h => h.fermatLastTheoremWith')

中文:
引理 fermatLastTheoremWith'_iff_fermatLastTheoremWith
  结论: {R : 类型} [交换半环 R] [是整环 R]
  证明: Iff.intro (fun h => h.fermatLastTheoremWith hn) (fun h => h.fermatLastTheoremWith')
-/
lemma fermatLastTheoremWith'_iff_fermatLastTheoremWith {R : Type*} [CommSemiring R] [IsDomain R]
    {n : Nat} (hn : forall a b c : R, IsUnit a -> IsUnit b -> IsUnit c -> a ^ n + b ^ n != c ^ n) :
    FermatLastTheoremWith' R n ↔ FermatLastTheoremWith R n :=
  Iff.intro (fun h => h.fermatLastTheoremWith hn) (fun h => h.fermatLastTheoremWith')

/--
lemma `fermatLastTheoremWith'_nat_int_tfae` / 引理 `fermatLastTheoremWith'_nat_int_tfae`

English:
lemma fermatLastTheoremWith'_nat_int_tfae
  given: (n : Nat)
  proof: by
  tfae_have 2 ↔ 1 := by
    apply fermatLastTheoremWith'_iff_fermatLastTheoremWith
    simp only [Nat.isUnit_iff]
    intro _ _ _ ha hb hc
    rw [ha]; rw [hb]; rw [hc]
    simp only [one_pow, Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
  tfae_have 3 ↔ 1 := by
    rw [fermatLastTheoremFor_iff_int]
    apply fermatLastTheoremWith'_iff_fermatLastTheoremWith
    intro a b c ha hb hc
    by_cases hn : n = 0
    · subst hn
      simp only [pow_zero, Int.reduceAdd, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
    · rw [← isUnit_pow_iff hn, Int.isUnit_iff] at ha hb hc
      -- case division
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
        rw [ha]; rw [hb]; rw [hc] <;> decide
  tfae_finish

中文:
引理 fermatLastTheoremWith'_nat_int_tfae
  条件: (n : 自然数)
  证明: by
  tfae_have 2 ↔ 1 := by
    apply fermatLastTheoremWith'_iff_fermatLastTheoremWith
    simp only [Nat.isUnit_iff]
    intro _ _ _ ha hb hc
    rw [ha]; rw [hb]; rw [hc]
    simp only [one_pow, Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
  tfae_have 3 ↔ 1 := by
    rw [fermatLastTheoremFor_iff_int]
    apply fermatLastTheoremWith'_iff_fermatLastTheoremWith
    intro a b c ha hb hc
    by_cases hn : n = 0
    · subst hn
      simp only [pow_zero, Int.reduceAdd, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
    · rw [← isUnit_pow_iff hn, Int.isUnit_iff] at ha hb hc
      -- case division
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
        rw [ha]; rw [hb]; rw [hc] <;> decide
  tfae_finish
-/
lemma fermatLastTheoremWith'_nat_int_tfae (n : Nat) :
    TFAE [FermatLastTheoremFor n, FermatLastTheoremWith' Nat n, FermatLastTheoremWith' Int n] := by
  tfae_have 2 ↔ 1 := by
    apply fermatLastTheoremWith'_iff_fermatLastTheoremWith
    simp only [Nat.isUnit_iff]
    intro _ _ _ ha hb hc
    rw [ha]; rw [hb]; rw [hc]
    simp only [one_pow, Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
  tfae_have 3 ↔ 1 := by
    rw [fermatLastTheoremFor_iff_int]
    apply fermatLastTheoremWith'_iff_fermatLastTheoremWith
    intro a b c ha hb hc
    by_cases hn : n = 0
    · subst hn
      simp only [pow_zero, Int.reduceAdd, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
    · rw [← isUnit_pow_iff hn, Int.isUnit_iff] at ha hb hc
      -- case division
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
        rw [ha]; rw [hb]; rw [hc] <;> decide
  tfae_finish

open Finset in
/--
lemma `fermatLastTheoremWith_of_fermatLastTheoremWith_coprime` / 引理 `fermatLastTheoremWith_of_fermatLastTheoremWith_coprime`

English:
lemma fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  statement: {n : Nat} {R : Type*} [CommSemiring R]
  proof: by
  intro a b c ha hb hc habc
  let s : Finset R := {a, b, c}; let d := s.gcd id
  obtain ⟨A, hA⟩ : d ∣ a := gcd_dvd (by simp [s])
  obtain ⟨B, hB⟩ : d ∣ b := gcd_dvd (by simp [s])
  obtain ⟨C, hC⟩ : d ∣ c := gcd_dvd (by simp [s])
  simp only [hA, hB, hC, mul_ne_zero_iff, mul_pow] at ha hb hc habc
  rw [← mul_add]; rw [mul_right_inj' (pow_ne_zero n ha.1)] at habc
  refine hn A B C ha.2 hb.2 hc.2 ?_ habc
  rw [← Finset.normalize_gcd]; rw [normalize_eq_one]
  refine isUnit_of_associated_mul ?_ ha.1
  grw [← Finset.gcd_mul_left', gcd_eq_gcd_image]
  refine .of_eq ?_; congr; simp [s, hA, hB, hC]

中文:
引理 fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  结论: {n : 自然数} {R : 类型} [交换半环 R]
  证明: by
  intro a b c ha hb hc habc
  let s : Finset R := {a, b, c}; let d := s.gcd id
  obtain ⟨A, hA⟩ : d ∣ a := gcd_dvd (by simp [s])
  obtain ⟨B, hB⟩ : d ∣ b := gcd_dvd (by simp [s])
  obtain ⟨C, hC⟩ : d ∣ c := gcd_dvd (by simp [s])
  simp only [hA, hB, hC, mul_ne_zero_iff, mul_pow] at ha hb hc habc
  rw [← mul_add]; rw [mul_right_inj' (pow_ne_zero n ha.1)] at habc
  refine hn A B C ha.2 hb.2 hc.2 ?_ habc
  rw [← Finset.normalize_gcd]; rw [normalize_eq_one]
  refine isUnit_of_associated_mul ?_ ha.1
  grw [← Finset.gcd_mul_left', gcd_eq_gcd_image]
  refine .of_eq ?_; congr; simp [s, hA, hB, hC]

Depends on / 依赖: Finset, Finset.gcd, Finset.normalize_gcd, gcd_dvd, isUnit_of_associated_mul, mul_add, mul_ne_zero_iff, mul_pow, mul_right_inj, normalize_eq_one, normalize_gcd, pow_ne_zero, s.gcd
-/
lemma fermatLastTheoremWith_of_fermatLastTheoremWith_coprime {n : Nat} {R : Type*} [CommSemiring R]
    [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R]
    (hn : forall a b c : R, a != 0 -> b != 0 -> c != 0 -> ({a, b, c} : Finset R).gcd id = 1 ->
      a ^ n + b ^ n != c ^ n) :
    FermatLastTheoremWith R n := by
  intro a b c ha hb hc habc
  let s : Finset R := {a, b, c}; let d := s.gcd id
  obtain ⟨A, hA⟩ : d ∣ a := gcd_dvd (by simp [s])
  obtain ⟨B, hB⟩ : d ∣ b := gcd_dvd (by simp [s])
  obtain ⟨C, hC⟩ : d ∣ c := gcd_dvd (by simp [s])
  simp only [hA, hB, hC, mul_ne_zero_iff, mul_pow] at ha hb hc habc
  rw [← mul_add]; rw [mul_right_inj' (pow_ne_zero n ha.1)] at habc
  refine hn A B C ha.2 hb.2 hc.2 ?_ habc
  rw [← Finset.normalize_gcd]; rw [normalize_eq_one]
  refine isUnit_of_associated_mul ?_ ha.1
  grw [← Finset.gcd_mul_left', gcd_eq_gcd_image]
  refine .of_eq ?_; congr; simp [s, hA, hB, hC]

/--
lemma `dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT` / 引理 `dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT`

English:
lemma dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT
  statement: {n : Nat} {p : Int} (hp : Prime p) {a b c : Int}
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp at HF
  refine hp.dvd_of_dvd_pow (n := n) (dvd_neg.1 ?_)
  rw [add_eq_zero_iff_eq_neg] at HF
  exact HF.symm ▸ dvd_add (dvd_pow hpa hn) (dvd_pow hpb hn)

中文:
引理 dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT
  结论: {n : 自然数} {p : 整数} (hp : 素 p) {a b c : 整数}
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp at HF
  refine hp.dvd_of_dvd_pow (n := n) (dvd_neg.1 ?_)
  rw [add_eq_zero_iff_eq_neg] at HF
  exact HF.symm ▸ dvd_add (dvd_pow hpa hn) (dvd_pow hpb hn)

Depends on / 依赖: HF.symm, add_eq_zero_iff_eq_neg, dvd_add, dvd_neg, dvd_of_dvd_pow, dvd_pow, eq_or_ne, hp.dvd_of_dvd_pow
-/
lemma dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT {n : Nat} {p : Int} (hp : Prime p) {a b c : Int}
    (hpa : p ∣ a) (hpb : p ∣ b) (HF : a ^ n + b ^ n + c ^ n = 0) : p ∣ c := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp at HF
  refine hp.dvd_of_dvd_pow (n := n) (dvd_neg.1 ?_)
  rw [add_eq_zero_iff_eq_neg] at HF
  exact HF.symm ▸ dvd_add (dvd_pow hpa hn) (dvd_pow hpb hn)

/--
lemma `isCoprime_of_gcd_eq_one_of_FLT` / 引理 `isCoprime_of_gcd_eq_one_of_FLT`

English:
lemma isCoprime_of_gcd_eq_one_of_FLT
  statement: {n : Nat} {a b c : Int} (Hgcd : Finset.gcd {a, b, c} id = 1)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [pow_zero, Int.reduceAdd, OfNat.ofNat_ne_zero] at HF
refine isCoprime_of_prime_dvd ?_ (fun p hp hpa hpb => hp.not_dvd_one ?_)
  · rintro ⟨rfl, rfl⟩
    simp only [ne_eq, hn, not_false_eq_true, zero_pow, add_zero, zero_add, pow_eq_zero_iff]
      at HF
    simp only [HF, Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.gcd_singleton, id_eq,
      normalize_zero, zero_ne_one] at Hgcd
  · rw [← Hgcd]
    refine Finset.dvd_gcd_iff.mpr fun x hx => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> simp only [id_eq, hx, hpa, hpb,
      dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT hp hpa hpb HF]

中文:
引理 isCoprime_of_gcd_eq_one_of_FLT
  结论: {n : 自然数} {a b c : 整数} (Hgcd : 有限集.最大公约数 {a, b, c} id = 1)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [pow_zero, Int.reduceAdd, OfNat.ofNat_ne_zero] at HF
refine isCoprime_of_prime_dvd ?_ (fun p hp hpa hpb => hp.not_dvd_one ?_)
  · rintro ⟨rfl, rfl⟩
    simp only [ne_eq, hn, not_false_eq_true, zero_pow, add_zero, zero_add, pow_eq_zero_iff]
      at HF
    simp only [HF, Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.gcd_singleton, id_eq,
      normalize_zero, zero_ne_one] at Hgcd
  · rw [← Hgcd]
    refine Finset.dvd_gcd_iff.mpr fun x hx => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> simp only [id_eq, hx, hpa, hpb,
      dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT hp hpa hpb HF]

Depends on / 依赖: Finset, Finset.dvd_gcd_iff.mpr, Finset.gcd_singleton, Finset.insert_eq_of_mem, Finset.mem_in, Finset.mem_singleton, Int.reduceAdd, OfNat.ofNat_ne_zero, add_zero, dvd_gcd_iff, eq_or_ne, gcd_singleton, hp.not_dvd_one, id_eq, insert_eq_of_mem, isCoprime_of_prime_dvd, mem_in, mem_singleton, ne_eq, normalize_zero
-/
lemma isCoprime_of_gcd_eq_one_of_FLT {n : Nat} {a b c : Int} (Hgcd : Finset.gcd {a, b, c} id = 1)
    (HF : a ^ n + b ^ n + c ^ n = 0) : IsCoprime a b := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [pow_zero, Int.reduceAdd, OfNat.ofNat_ne_zero] at HF
refine isCoprime_of_prime_dvd ?_ (fun p hp hpa hpb => hp.not_dvd_one ?_)
  · rintro ⟨rfl, rfl⟩
    simp only [ne_eq, hn, not_false_eq_true, zero_pow, add_zero, zero_add, pow_eq_zero_iff]
      at HF
    simp only [HF, Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.gcd_singleton, id_eq,
      normalize_zero, zero_ne_one] at Hgcd
  · rw [← Hgcd]
    refine Finset.dvd_gcd_iff.mpr fun x hx => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> simp only [id_eq, hx, hpa, hpb,
      dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT hp hpa hpb HF]
