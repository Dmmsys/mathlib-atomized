/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Prime.Pow
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime powers

This file deals with prime powers: numbers which are positive integer powers of a single prime.
-/

@[expose] public section
assert_not_exists Nat.divisors

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : Nat)

/-- `n` is a prime power if there is a prime `p` and a positive natural `k` such that `n` can be
written as `p^k`. -/
@[wikidata Q1667469]
/--
Definition of `IsPrimePow` / `IsPrimePow` 的定义

English:
definition IsPrimePow
  signature: : Prop
  body: exists (p : R) (k : Nat), Prime p ∧ 0 < k ∧ p ^ k = n

中文:
定义 IsPrimePow
  签名: : 命题
  定义体: exists (p : R) (k : Nat), Prime p ∧ 0 < k ∧ p ^ k = n
-/
def IsPrimePow : Prop :=
  exists (p : R) (k : Nat), Prime p ∧ 0 < k ∧ p ^ k = n

/--
theorem `isPrimePow_def` / 定理 `isPrimePow_def`

English:
theorem isPrimePow_def
  statement: IsPrimePow n ↔ exists (p : R) (k : Nat), Prime p ∧ 0 < k ∧ p ^ k = n
  proof: Iff.rfl

中文:
定理 isPrimePow_def
  结论: IsPrimePow n ↔ 存在 (p : R) (k : 自然数), Prime p ∧ 0 < k ∧ p ^ k = n
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isPrimePow_def : IsPrimePow n ↔ exists (p : R) (k : Nat), Prime p ∧ 0 < k ∧ p ^ k = n :=
  Iff.rfl

/--
theorem `isPrimePow_iff_pow_succ` / 定理 `isPrimePow_iff_pow_succ`

English:
theorem isPrimePow_iff_pow_succ
  statement: IsPrimePow n ↔ exists (p : R) (k : Nat), Prime p ∧ p ^ (k + 1) = n
  proof: (isPrimePow_def _).trans
    ⟨fun ⟨p, k, hp, hk, hn⟩ => ⟨p, k - 1, hp, by rwa [Nat.sub_add_cancel hk]⟩, fun ⟨_, _, hp, hn⟩ =>
      ⟨_, _, hp, Nat.succ_pos', hn⟩⟩

中文:
定理 isPrimePow_iff_pow_succ
  结论: IsPrimePow n ↔ 存在 (p : R) (k : 自然数), Prime p ∧ p ^ (k + 1) = n
  证明: (isPrimePow_def _).trans
    ⟨fun ⟨p, k, hp, hk, hn⟩ => ⟨p, k - 1, hp, by rwa [Nat.sub_add_cancel hk]⟩, fun ⟨_, _, hp, hn⟩ =>
      ⟨_, _, hp, Nat.succ_pos', hn⟩⟩

Depends on / 依赖: Nat.sub_add_cancel, Nat.succ_pos, isPrimePow_def, sub_add_cancel, succ_pos
-/
theorem isPrimePow_iff_pow_succ : IsPrimePow n ↔ exists (p : R) (k : Nat), Prime p ∧ p ^ (k + 1) = n :=
  (isPrimePow_def _).trans
    ⟨fun ⟨p, k, hp, hk, hn⟩ => ⟨p, k - 1, hp, by rwa [Nat.sub_add_cancel hk]⟩, fun ⟨_, _, hp, hn⟩ =>
      ⟨_, _, hp, Nat.succ_pos', hn⟩⟩

/--
theorem `not_isPrimePow_zero` / 定理 `not_isPrimePow_zero`

English:
theorem not_isPrimePow_zero
  given: [IsReduced R]
  statement: ¬IsPrimePow (0 : R)
  proof: by
  simp only [isPrimePow_def, not_exists, not_and', and_imp]
  intro x n _hn hx
  rw [eq_zero_of_pow_eq_zero hx]
  simp

中文:
定理 not_isPrimePow_zero
  条件: [IsReduced R]
  结论: ¬IsPrimePow (0 : R)
  证明: by
  simp only [isPrimePow_def, not_exists, not_and', and_imp]
  intro x n _hn hx
  rw [eq_zero_of_pow_eq_zero hx]
  simp

Depends on / 依赖: and_imp, eq_zero_of_pow_eq_zero, isPrimePow_def, not_and, not_exists
-/
theorem not_isPrimePow_zero [IsReduced R] : ¬IsPrimePow (0 : R) := by
  simp only [isPrimePow_def, not_exists, not_and', and_imp]
  intro x n _hn hx
  rw [eq_zero_of_pow_eq_zero hx]
  simp

/--
theorem `IsPrimePow.not_isUnit` / 定理 `IsPrimePow.not_isUnit`

English:
theorem IsPrimePow.not_isUnit
  given: {n : R} (h : IsPrimePow n)
  statement: ¬IsUnit n
  proof: let ⟨_p, _k, hp, hk, hn⟩ := h
  hn ▸ (isUnit_pow_iff hk.ne').not.mpr hp.not_isUnit

@[deprecated (since := "2026-08-02")]
alias IsPrimePow.not_unit := IsPrimePow.not_isUnit

中文:
定理 IsPrimePow.not_isUnit
  条件: {n : R} (h : IsPrimePow n)
  结论: ¬IsUnit n
  证明: let ⟨_p, _k, hp, hk, hn⟩ := h
  hn ▸ (isUnit_pow_iff hk.ne').not.mpr hp.not_isUnit

@[deprecated (since := "2026-08-02")]
alias IsPrimePow.not_unit := IsPrimePow.not_isUnit

Depends on / 依赖: hk.ne, hp.not_isUnit, isUnit_pow_iff, not.mpr, not_isUnit
-/
theorem IsPrimePow.not_isUnit {n : R} (h : IsPrimePow n) : ¬IsUnit n :=
  let ⟨_p, _k, hp, hk, hn⟩ := h
  hn ▸ (isUnit_pow_iff hk.ne').not.mpr hp.not_isUnit

@[deprecated (since := "2026-08-02")]
alias IsPrimePow.not_unit := IsPrimePow.not_isUnit

/--
theorem `IsUnit.not_isPrimePow` / 定理 `IsUnit.not_isPrimePow`

English:
theorem IsUnit.not_isPrimePow
  given: {n : R} (h : IsUnit n)
  statement: ¬IsPrimePow n
  proof: fun h' => h'.not_isUnit h

中文:
定理 IsUnit.not_isPrimePow
  条件: {n : R} (h : IsUnit n)
  结论: ¬IsPrimePow n
  证明: fun h' => h'.not_isUnit h

Depends on / 依赖: not_isUnit
-/
theorem IsUnit.not_isPrimePow {n : R} (h : IsUnit n) : ¬IsPrimePow n := fun h' => h'.not_isUnit h

/--
theorem `not_isPrimePow_one` / 定理 `not_isPrimePow_one`

English:
theorem not_isPrimePow_one
  statement: ¬IsPrimePow (1 : R)
  proof: isUnit_one.not_isPrimePow

中文:
定理 not_isPrimePow_one
  结论: ¬IsPrimePow (1 : R)
  证明: isUnit_one.not_isPrimePow

Depends on / 依赖: isUnit_one, isUnit_one.not_isPrimePow, not_isPrimePow
-/
theorem not_isPrimePow_one : ¬IsPrimePow (1 : R) :=
  isUnit_one.not_isPrimePow

/--
theorem `Prime.isPrimePow` / 定理 `Prime.isPrimePow`

English:
theorem Prime.isPrimePow
  given: {p : R} (hp : Prime p)
  statement: IsPrimePow p
  proof: ⟨p, 1, hp, zero_lt_one, by simp⟩

中文:
定理 Prime.isPrimePow
  条件: {p : R} (hp : Prime p)
  结论: IsPrimePow p
  证明: ⟨p, 1, hp, zero_lt_one, by simp⟩

Depends on / 依赖: zero_lt_one
-/
theorem Prime.isPrimePow {p : R} (hp : Prime p) : IsPrimePow p :=
  ⟨p, 1, hp, zero_lt_one, by simp⟩

/--
theorem `IsPrimePow.pow` / 定理 `IsPrimePow.pow`

English:
theorem IsPrimePow.pow
  given: {n : R} (hn : IsPrimePow n) {k : Nat} (hk : k != 0)
  statement: IsPrimePow (n ^ k)
  proof: let ⟨p, k', hp, hk', hn⟩ := hn
  ⟨p, k * k', hp, mul_pos hk.bot_lt hk', by rw [pow_mul', hn]⟩

中文:
定理 IsPrimePow.pow
  条件: {n : R} (hn : IsPrimePow n) {k : 自然数} (hk : k != 0)
  结论: IsPrimePow (n ^ k)
  证明: let ⟨p, k', hp, hk', hn⟩ := hn
  ⟨p, k * k', hp, mul_pos hk.bot_lt hk', by rw [pow_mul', hn]⟩

Depends on / 依赖: bot_lt, hk.bot_lt, mul_pos, pow_mul
-/
theorem IsPrimePow.pow {n : R} (hn : IsPrimePow n) {k : Nat} (hk : k != 0) : IsPrimePow (n ^ k) :=
  let ⟨p, k', hp, hk', hn⟩ := hn
  ⟨p, k * k', hp, mul_pos hk.bot_lt hk', by rw [pow_mul', hn]⟩

/--
theorem `IsPrimePow.ne_zero` / 定理 `IsPrimePow.ne_zero`

English:
theorem IsPrimePow.ne_zero
  given: [IsReduced R] {n : R} (h : IsPrimePow n)
  statement: n != 0
  proof: fun t =>
  not_isPrimePow_zero (t ▸ h)

中文:
定理 IsPrimePow.ne_zero
  条件: [IsReduced R] {n : R} (h : IsPrimePow n)
  结论: n != 0
  证明: fun t =>
  not_isPrimePow_zero (t ▸ h)
-/
theorem IsPrimePow.ne_zero [IsReduced R] {n : R} (h : IsPrimePow n) : n != 0 := fun t =>
  not_isPrimePow_zero (t ▸ h)

/--
theorem `IsPrimePow.ne_one` / 定理 `IsPrimePow.ne_one`

English:
theorem IsPrimePow.ne_one
  given: {n : R} (h : IsPrimePow n)
  statement: n != 1
  proof: fun t =>
  not_isPrimePow_one (t ▸ h)

中文:
定理 IsPrimePow.ne_one
  条件: {n : R} (h : IsPrimePow n)
  结论: n != 1
  证明: fun t =>
  not_isPrimePow_one (t ▸ h)
-/
theorem IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n != 1 := fun t =>
  not_isPrimePow_one (t ▸ h)

section Nat

/--
theorem `isPrimePow_nat_iff` / 定理 `isPrimePow_nat_iff`

English:
theorem isPrimePow_nat_iff
  given: (n : Nat)
  statement: IsPrimePow n ↔ exists p k : Nat, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
  proof: by
  simp only [isPrimePow_def, Nat.prime_iff]

中文:
定理 isPrimePow_nat_iff
  条件: (n : 自然数)
  结论: IsPrimePow n ↔ 存在 p k : 自然数, 自然数.Prime p ∧ 0 < k ∧ p ^ k = n
  证明: by
  simp only [isPrimePow_def, Nat.prime_iff]

Depends on / 依赖: Nat.prime_iff, isPrimePow_def, prime_iff
-/
theorem isPrimePow_nat_iff (n : Nat) : IsPrimePow n ↔ exists p k : Nat, Nat.Prime p ∧ 0 < k ∧ p ^ k = n := by
  simp only [isPrimePow_def, Nat.prime_iff]

/--
theorem `Nat.Prime.isPrimePow` / 定理 `Nat.Prime.isPrimePow`

English:
theorem Nat.Prime.isPrimePow
  given: {p : Nat} (hp : p.Prime)
  statement: IsPrimePow p
  proof: _root_.Prime.isPrimePow (prime_iff.mp hp)

中文:
定理 Nat.Prime.isPrimePow
  条件: {p : 自然数} (hp : p.Prime)
  结论: IsPrimePow p
  证明: _root_.Prime.isPrimePow (prime_iff.mp hp)

Depends on / 依赖: _root_, _root_.Prime.isPrimePow, isPrimePow, prime_iff, prime_iff.mp
-/
theorem Nat.Prime.isPrimePow {p : Nat} (hp : p.Prime) : IsPrimePow p :=
  _root_.Prime.isPrimePow (prime_iff.mp hp)

/--
theorem `isPrimePow_nat_iff_bounded` / 定理 `isPrimePow_nat_iff_bounded`

English:
theorem isPrimePow_nat_iff_bounded
  given: (n : Nat)
  proof: by
  rw [isPrimePow_nat_iff]
  refine Iff.symm ⟨fun ⟨p, _, k, _, hp, hk, hn⟩ => ⟨p, k, hp, hk, hn⟩, ?_⟩
  rintro ⟨p, k, hp, hk, rfl⟩
  refine ⟨p, ?_, k, (Nat.lt_pow_self hp.one_lt).le, hp, hk, rfl⟩
  conv => {lhs; rw [← (pow_one p)]}
  exact Nat.pow_le_pow_right hp.one_lt.le hk

中文:
定理 isPrimePow_nat_iff_bounded
  条件: (n : 自然数)
  证明: by
  rw [isPrimePow_nat_iff]
  refine Iff.symm ⟨fun ⟨p, _, k, _, hp, hk, hn⟩ => ⟨p, k, hp, hk, hn⟩, ?_⟩
  rintro ⟨p, k, hp, hk, rfl⟩
  refine ⟨p, ?_, k, (Nat.lt_pow_self hp.one_lt).le, hp, hk, rfl⟩
  conv => {lhs; rw [← (pow_one p)]}
  exact Nat.pow_le_pow_right hp.one_lt.le hk

Depends on / 依赖: Iff.symm, Nat.lt_pow_self, Nat.pow_le_pow_right, hp.one_lt, hp.one_lt.le, isPrimePow_nat_iff, lt_pow_self, one_lt, pow_le_pow_right, pow_one
-/
theorem isPrimePow_nat_iff_bounded (n : Nat) :
    IsPrimePow n ↔ exists p : Nat, p <= n ∧ exists k : Nat, k <= n ∧ p.Prime ∧ 0 < k ∧ p ^ k = n := by
  rw [isPrimePow_nat_iff]
  refine Iff.symm ⟨fun ⟨p, _, k, _, hp, hk, hn⟩ => ⟨p, k, hp, hk, hn⟩, ?_⟩
  rintro ⟨p, k, hp, hk, rfl⟩
  refine ⟨p, ?_, k, (Nat.lt_pow_self hp.one_lt).le, hp, hk, rfl⟩
  conv => {lhs; rw [← (pow_one p)]}
  exact Nat.pow_le_pow_right hp.one_lt.le hk

/--
theorem `isPrimePow_nat_iff_bounded_log` / 定理 `isPrimePow_nat_iff_bounded_log`

English:
theorem isPrimePow_nat_iff_bounded_log
  given: (n : Nat)
  proof: by
  rw [isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp', hk', rfl⟩
    refine ⟨k, ?_, hk', ⟨p, Nat.le_pow hk', rfl, hp'⟩⟩
    · calc
        k = Nat.log 2 (2 ^ k) := by simp
        _ <= Nat.log 2 (p ^ k) := Nat.log_mono Nat.one_lt_two Nat.AtLeastTwo.prop
                                   

中文:
定理 isPrimePow_nat_iff_bounded_log
  条件: (n : 自然数)
  证明: by
  rw [isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp', hk', rfl⟩
    refine ⟨k, ?_, hk', ⟨p, Nat.le_pow hk', rfl, hp'⟩⟩
    · calc
        k = Nat.log 2 (2 ^ k) := by simp
        _ <= Nat.log 2 (p ^ k) := Nat.log_mono Nat.one_lt_two Nat.AtLeastTwo.prop
                                   

Depends on / 依赖: AtLeastTwo, Nat.AtLeastTwo.prop, Nat.Prime.two_le, Nat.le_pow, Nat.log, Nat.log_mono, Nat.one_lt_two, Nat.pow_le_pow_left, isPrimePow_nat_iff, le_pow, log_mono, one_lt_two, pow_le_pow_left, two_le
-/
theorem isPrimePow_nat_iff_bounded_log (n : Nat) :
    IsPrimePow n
      ↔ exists k : Nat, k <= Nat.log 2 n ∧ 0 < k ∧ exists p : Nat, p <= n ∧ n = p ^ k ∧ p.Prime := by
  rw [isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp', hk', rfl⟩
    refine ⟨k, ?_, hk', ⟨p, Nat.le_pow hk', rfl, hp'⟩⟩
    · calc
        k = Nat.log 2 (2 ^ k) := by simp
        _ <= Nat.log 2 (p ^ k) := Nat.log_mono Nat.one_lt_two Nat.AtLeastTwo.prop
                                   (Nat.pow_le_pow_left (Nat.Prime.two_le hp') k)
  · rintro ⟨k, hk, hk', ⟨p, hp, rfl, hp'⟩⟩
    exact ⟨p, k, hp', hk', rfl⟩

/--
theorem `isPrimePow_nat_iff_bounded_log_minFac` / 定理 `isPrimePow_nat_iff_bounded_log_minFac`

English:
theorem isPrimePow_nat_iff_bounded_log_minFac
  given: (n : Nat)
  proof: by
  rw [isPrimePow_nat_iff_bounded_log]
  obtain rfl | h := eq_or_ne n 1
  · simp
  constructor
  · rintro ⟨k, hkle, hk_pos, p, hle, heq, hprime⟩
    refine ⟨k, hkle, hk_pos, ?_⟩
    rw [heq]; rw [hprime.pow_minFac hk_pos.ne']
  · rintro ⟨k, hkle, hk_pos, heq⟩
    refine ⟨k, hkle, hk_pos, n.minFac,

中文:
定理 isPrimePow_nat_iff_bounded_log_minFac
  条件: (n : 自然数)
  证明: by
  rw [isPrimePow_nat_iff_bounded_log]
  obtain rfl | h := eq_or_ne n 1
  · simp
  constructor
  · rintro ⟨k, hkle, hk_pos, p, hle, heq, hprime⟩
    refine ⟨k, hkle, hk_pos, ?_⟩
    rw [heq]; rw [hprime.pow_minFac hk_pos.ne']
  · rintro ⟨k, hkle, hk_pos, heq⟩
    refine ⟨k, hkle, hk_pos, n.minFac,

Depends on / 依赖: Nat.log_zero_right, Nat.minFac_le, Nat.minFac_prime_iff, eq_or_ne, hk_pos, hk_pos.ne, hprime, hprime.pow_minFac, isPrimePow_nat_iff_bounded_log, log_zero_right, lt_self_iff_false, minFac, minFac_le, minFac_prime_iff, n.minFac, nonpos_iff_eq_zero, pow_minFac
-/
theorem isPrimePow_nat_iff_bounded_log_minFac (n : Nat) :
    IsPrimePow n
      ↔ exists k : Nat, k <= Nat.log 2 n ∧ 0 < k ∧ n = n.minFac ^ k := by
  rw [isPrimePow_nat_iff_bounded_log]
  obtain rfl | h := eq_or_ne n 1
  · simp
  constructor
  · rintro ⟨k, hkle, hk_pos, p, hle, heq, hprime⟩
    refine ⟨k, hkle, hk_pos, ?_⟩
    rw [heq]; rw [hprime.pow_minFac hk_pos.ne']
  · rintro ⟨k, hkle, hk_pos, heq⟩
    refine ⟨k, hkle, hk_pos, n.minFac, Nat.minFac_le ?_, heq, ?_⟩
    · grind [Nat.minFac_prime_iff, nonpos_iff_eq_zero, Nat.log_zero_right, lt_self_iff_false]
    · grind [Nat.minFac_prime_iff]

instance {n : Nat} : Decidable (IsPrimePow n) :=
  decidable_of_iff' _ (isPrimePow_nat_iff_bounded_log_minFac n)

/--
theorem `IsPrimePow.dvd` / 定理 `IsPrimePow.dvd`

English:
theorem IsPrimePow.dvd
  given: {n m : Nat} (hn : IsPrimePow n) (hm : m ∣ n) (hm₁ : m != 1)
  statement: IsPrimePow m
  proof: by
  grind [isPrimePow_nat_iff, Nat.dvd_prime_pow, Nat.pow_eq_one]

中文:
定理 IsPrimePow.dvd
  条件: {n m : 自然数} (hn : IsPrimePow n) (hm : m ∣ n) (hm₁ : m != 1)
  结论: IsPrimePow m
  证明: by
  grind [isPrimePow_nat_iff, Nat.dvd_prime_pow, Nat.pow_eq_one]

Depends on / 依赖: Nat.dvd_prime_pow, Nat.pow_eq_one, dvd_prime_pow, isPrimePow_nat_iff, pow_eq_one
-/
theorem IsPrimePow.dvd {n m : Nat} (hn : IsPrimePow n) (hm : m ∣ n) (hm₁ : m != 1) : IsPrimePow m := by
  grind [isPrimePow_nat_iff, Nat.dvd_prime_pow, Nat.pow_eq_one]

/--
theorem `IsPrimePow.two_le` / 定理 `IsPrimePow.two_le`

English:
theorem IsPrimePow.two_le
  statement: forall {n : Nat}, IsPrimePow n -> 2 <= n

中文:
定理 IsPrimePow.two_le
  结论: 对任意 {n : 自然数}, IsPrimePow n -> 2 <= n
-/
theorem IsPrimePow.two_le : forall {n : Nat}, IsPrimePow n -> 2 <= n
  | 0, h => (not_isPrimePow_zero h).elim
  | 1, h => (not_isPrimePow_one h).elim
  | _n + 2, _ => le_add_self

/--
theorem `IsPrimePow.pos` / 定理 `IsPrimePow.pos`

English:
theorem IsPrimePow.pos
  given: {n : Nat} (hn : IsPrimePow n)
  statement: 0 < n
  proof: pos_of_gt hn.two_le

中文:
定理 IsPrimePow.pos
  条件: {n : 自然数} (hn : IsPrimePow n)
  结论: 0 < n
  证明: pos_of_gt hn.two_le

Depends on / 依赖: hn.two_le, pos_of_gt, two_le
-/
theorem IsPrimePow.pos {n : Nat} (hn : IsPrimePow n) : 0 < n :=
  pos_of_gt hn.two_le

/--
theorem `IsPrimePow.one_lt` / 定理 `IsPrimePow.one_lt`

English:
theorem IsPrimePow.one_lt
  given: {n : Nat} (h : IsPrimePow n)
  statement: 1 < n
  proof: h.two_le

中文:
定理 IsPrimePow.one_lt
  条件: {n : 自然数} (h : IsPrimePow n)
  结论: 1 < n
  证明: h.two_le

Depends on / 依赖: h.two_le, two_le
-/
theorem IsPrimePow.one_lt {n : Nat} (h : IsPrimePow n) : 1 < n :=
  h.two_le

end Nat
