/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# Prime elements

In this file we define the predicate `Prime p`
saying that an element of a commutative monoid with zero is prime.
Namely, `Prime p` means that `p` isn't zero, it isn't a unit,
and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`;

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Irreducible`
(see `irreducible_iff_prime`), however this is not true in general.

## Main definitions

* `Prime`: a prime element of a commutative monoid with zero

## Main results

* `irreducible_iff_prime`: the two definitions are equivalent in a decomposition monoid.
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Multiset

variable {M : Type*}

section Prime

variable [CommMonoidWithZero M]

/--
Definition of `Prime` / `Prime` 的定义

English:
definition Prime
  signature: (p : M)
  body: p != 0 ∧ ¬IsUnit p ∧ forall a b, p ∣ a * b -> p ∣ a ∨ p ∣ b

中文:
定义 Prime
  签名: (p : M)
  定义体: p != 0 ∧ ¬IsUnit p ∧ forall a b, p ∣ a * b -> p ∣ a ∨ p ∣ b

Depends on / 依赖: IsUnit
-/
def Prime (p : M) : Prop :=
  p != 0 ∧ ¬IsUnit p ∧ forall a b, p ∣ a * b -> p ∣ a ∨ p ∣ b

namespace Prime

variable {p : M} (hp : Prime p)
include hp

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  statement: p != 0
  proof: hp.1

中文:
定理 ne_zero
  结论: p != 0
  证明: hp.1
-/
theorem ne_zero : p != 0 :=
  hp.1

/--
theorem `not_isUnit` / 定理 `not_isUnit`

English:
theorem not_isUnit
  statement: ¬IsUnit p
  proof: hp.2.1

@[deprecated (since := "2026-08-02")]
alias not_unit := not_isUnit

中文:
定理 not_isUnit
  结论: ¬IsUnit p
  证明: hp.2.1

@[deprecated (since := "2026-08-02")]
alias not_unit := not_isUnit
-/
theorem not_isUnit : ¬IsUnit p :=
  hp.2.1

@[deprecated (since := "2026-08-02")]
alias not_unit := not_isUnit

/--
theorem `not_dvd_one` / 定理 `not_dvd_one`

English:
theorem not_dvd_one
  statement: ¬p ∣ 1
  proof: mt (isUnit_of_dvd_one ·) hp.not_isUnit

中文:
定理 not_dvd_one
  结论: ¬p ∣ 1
  证明: mt (isUnit_of_dvd_one ·) hp.not_isUnit

Depends on / 依赖: hp.not_isUnit, isUnit_of_dvd_one, not_isUnit
-/
theorem not_dvd_one : ¬p ∣ 1 :=
  mt (isUnit_of_dvd_one ·) hp.not_isUnit

/--
theorem `ne_one` / 定理 `ne_one`

English:
theorem ne_one
  statement: p != 1
  proof: fun h => hp.2.1 (h.symm ▸ isUnit_one)

中文:
定理 ne_one
  结论: p != 1
  证明: fun h => hp.2.1 (h.symm ▸ isUnit_one)

Depends on / 依赖: h.symm, isUnit_one
-/
theorem ne_one : p != 1 := fun h => hp.2.1 (h.symm ▸ isUnit_one)

/--
theorem `dvd_or_dvd` / 定理 `dvd_or_dvd`

English:
theorem dvd_or_dvd
  given: {a b : M} (h : p ∣ a * b)
  statement: p ∣ a ∨ p ∣ b
  proof: hp.2.2 a b h

中文:
定理 dvd_or_dvd
  条件: {a b : M} (h : p ∣ a * b)
  结论: p ∣ a ∨ p ∣ b
  证明: hp.2.2 a b h
-/
theorem dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  hp.2.2 a b h

/--
theorem `dvd_mul` / 定理 `dvd_mul`

English:
theorem dvd_mul
  given: {a b : M}
  statement: p ∣ a * b ↔ p ∣ a ∨ p ∣ b
  proof: ⟨hp.dvd_or_dvd, (Or.elim · (dvd_mul_of_dvd_left · _) (dvd_mul_of_dvd_right · _))⟩

中文:
定理 dvd_mul
  条件: {a b : M}
  结论: p ∣ a * b ↔ p ∣ a ∨ p ∣ b
  证明: ⟨hp.dvd_or_dvd, (Or.elim · (dvd_mul_of_dvd_left · _) (dvd_mul_of_dvd_right · _))⟩

Depends on / 依赖: Or.elim, dvd_mul_of_dvd_left, dvd_mul_of_dvd_right, dvd_or_dvd, hp.dvd_or_dvd
-/
theorem dvd_mul {a b : M} : p ∣ a * b ↔ p ∣ a ∨ p ∣ b :=
  ⟨hp.dvd_or_dvd, (Or.elim · (dvd_mul_of_dvd_left · _) (dvd_mul_of_dvd_right · _))⟩

/--
theorem `isPrimal` / 定理 `isPrimal`

English:
theorem isPrimal
  statement: IsPrimal p
  proof: fun _a _b dvd => (hp.dvd_or_dvd dvd).elim
  (fun h => ⟨p, 1, h, one_dvd _, (mul_one p).symm⟩) fun h => ⟨1, p, one_dvd _, h, (one_mul p).symm⟩

中文:
定理 isPrimal
  结论: IsPrimal p
  证明: fun _a _b dvd => (hp.dvd_or_dvd dvd).elim
  (fun h => ⟨p, 1, h, one_dvd _, (mul_one p).symm⟩) fun h => ⟨1, p, one_dvd _, h, (one_mul p).symm⟩

Depends on / 依赖: dvd_or_dvd, hp.dvd_or_dvd
-/
theorem isPrimal : IsPrimal p := fun _a _b dvd => (hp.dvd_or_dvd dvd).elim
  (fun h => ⟨p, 1, h, one_dvd _, (mul_one p).symm⟩) fun h => ⟨1, p, one_dvd _, h, (one_mul p).symm⟩

/--
theorem `not_dvd_mul` / 定理 `not_dvd_mul`

English:
theorem not_dvd_mul
  given: {a b : M} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
  statement: ¬ p ∣ a * b
  proof: hp.dvd_mul.not.mpr not_or.mpr ⟨ha, hb⟩

中文:
定理 not_dvd_mul
  条件: {a b : M} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
  结论: ¬ p ∣ a * b
  证明: hp.dvd_mul.not.mpr not_or.mpr ⟨ha, hb⟩

Depends on / 依赖: dvd_mul, hp.dvd_mul.not.mpr, not_or, not_or.mpr
-/
theorem not_dvd_mul {a b : M} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b :=
hp.dvd_mul.not.mpr not_or.mpr ⟨ha, hb⟩

/--
theorem `dvd_of_dvd_pow` / 定理 `dvd_of_dvd_pow`

English:
theorem dvd_of_dvd_pow
  given: {a : M} {n : Nat} (h : p ∣ a ^ n)
  statement: p ∣ a
  proof: by
  induction n with
  | zero =>
    rw [pow_zero] at h
    have := isUnit_of_dvd_one h
    have := not_isUnit hp
    contradiction
  | succ n ih =>
    rw [pow_succ'] at h
    rcases dvd_or_dvd hp h with dvd_a | dvd_pow
    · assumption
    · exact ih dvd_pow

中文:
定理 dvd_of_dvd_pow
  条件: {a : M} {n : 自然数} (h : p ∣ a ^ n)
  结论: p ∣ a
  证明: by
  induction n with
  | zero =>
    rw [pow_zero] at h
    have := isUnit_of_dvd_one h
    have := not_isUnit hp
    contradiction
  | succ n ih =>
    rw [pow_succ'] at h
    rcases dvd_or_dvd hp h with dvd_a | dvd_pow
    · assumption
    · exact ih dvd_pow

Depends on / 依赖: dvd_a, dvd_or_dvd, dvd_pow, isUnit_of_dvd_one, not_isUnit, pow_succ, pow_zero
-/
theorem dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) : p ∣ a := by
  induction n with
  | zero =>
    rw [pow_zero] at h
    have := isUnit_of_dvd_one h
    have := not_isUnit hp
    contradiction
  | succ n ih =>
    rw [pow_succ'] at h
    rcases dvd_or_dvd hp h with dvd_a | dvd_pow
    · assumption
    · exact ih dvd_pow

/--
theorem `dvd_pow_iff_dvd` / 定理 `dvd_pow_iff_dvd`

English:
theorem dvd_pow_iff_dvd
  given: {a : M} {n : Nat} (hn : n != 0)
  statement: p ∣ a ^ n ↔ p ∣ a
  proof: ⟨hp.dvd_of_dvd_pow, (dvd_pow · hn)⟩

中文:
定理 dvd_pow_iff_dvd
  条件: {a : M} {n : 自然数} (hn : n != 0)
  结论: p ∣ a ^ n ↔ p ∣ a
  证明: ⟨hp.dvd_of_dvd_pow, (dvd_pow · hn)⟩

Depends on / 依赖: dvd_of_dvd_pow, dvd_pow, hp.dvd_of_dvd_pow
-/
theorem dvd_pow_iff_dvd {a : M} {n : Nat} (hn : n != 0) : p ∣ a ^ n ↔ p ∣ a :=
  ⟨hp.dvd_of_dvd_pow, (dvd_pow · hn)⟩

end Prime

@[simp]
/--
theorem `not_prime_zero` / 定理 `not_prime_zero`

English:
theorem not_prime_zero
  statement: ¬Prime (0 : M)
  proof: fun h => h.ne_zero rfl

@[simp]

中文:
定理 not_prime_zero
  结论: ¬Prime (0 : M)
  证明: fun h => h.ne_zero rfl

@[simp]

Depends on / 依赖: h.ne_zero, ne_zero
-/
theorem not_prime_zero : ¬Prime (0 : M) := fun h => h.ne_zero rfl

@[simp]
/--
theorem `not_prime_one` / 定理 `not_prime_one`

English:
theorem not_prime_one
  statement: ¬Prime (1 : M)
  proof: fun h => h.not_isUnit isUnit_one

中文:
定理 not_prime_one
  结论: ¬Prime (1 : M)
  证明: fun h => h.not_isUnit isUnit_one

Depends on / 依赖: h.not_isUnit, isUnit_one, not_isUnit
-/
theorem not_prime_one : ¬Prime (1 : M) := fun h => h.not_isUnit isUnit_one

end Prime

/--
theorem `Irreducible.not_dvd_isUnit` / 定理 `Irreducible.not_dvd_isUnit`

English:
theorem Irreducible.not_dvd_isUnit
  given: [CommMonoid M] {p u : M} (hp : Irreducible p) (hu : IsUnit u)
  proof: mt (isUnit_of_dvd_unit · hu) hp.not_isUnit

中文:
定理 Irreducible.not_dvd_isUnit
  条件: [CommMonoid M] {p u : M} (hp : Irreducible p) (hu : IsUnit u)
  证明: mt (isUnit_of_dvd_unit · hu) hp.not_isUnit

Depends on / 依赖: hp.not_isUnit, isUnit_of_dvd_unit, not_isUnit
-/
theorem Irreducible.not_dvd_isUnit [CommMonoid M] {p u : M} (hp : Irreducible p) (hu : IsUnit u) :
    ¬p ∣ u :=
  mt (isUnit_of_dvd_unit · hu) hp.not_isUnit

/--
theorem `Irreducible.not_dvd_one` / 定理 `Irreducible.not_dvd_one`

English:
theorem Irreducible.not_dvd_one
  given: [CommMonoid M] {p : M} (hp : Irreducible p)
  statement: ¬p ∣ 1
  proof: hp.not_dvd_isUnit isUnit_one

中文:
定理 Irreducible.not_dvd_one
  条件: [CommMonoid M] {p : M} (hp : Irreducible p)
  结论: ¬p ∣ 1
  证明: hp.not_dvd_isUnit isUnit_one

Depends on / 依赖: hp.not_dvd_isUnit, isUnit_one, not_dvd_isUnit
-/
theorem Irreducible.not_dvd_one [CommMonoid M] {p : M} (hp : Irreducible p) : ¬p ∣ 1 :=
  hp.not_dvd_isUnit isUnit_one

/--
theorem `Irreducible.not_dvd_unit` / 定理 `Irreducible.not_dvd_unit`

English:
theorem Irreducible.not_dvd_unit
  given: [CommMonoid M] {p : M} (u : Mˣ) (hp : Irreducible p)
  proof: hp.not_dvd_isUnit u.isUnit

@[simp]

中文:
定理 Irreducible.not_dvd_unit
  条件: [CommMonoid M] {p : M} (u : Mˣ) (hp : Irreducible p)
  证明: hp.not_dvd_isUnit u.isUnit

@[simp]

Depends on / 依赖: hp.not_dvd_isUnit, isUnit, not_dvd_isUnit, u.isUnit
-/
theorem Irreducible.not_dvd_unit [CommMonoid M] {p : M} (u : Mˣ) (hp : Irreducible p) :
    ¬ p ∣ u :=
  hp.not_dvd_isUnit u.isUnit

@[simp]
/--
theorem `not_irreducible_zero` / 定理 `not_irreducible_zero`

English:
theorem not_irreducible_zero
  given: [MonoidWithZero M]
  statement: ¬Irreducible (0 : M)
  proof: h (mul_zero 0).symm
    this.elim hn0 hn0

中文:
定理 not_irreducible_zero
  条件: [MonoidWithZero M]
  结论: ¬Irreducible (0 : M)
  证明: h (mul_zero 0).symm
    this.elim hn0 hn0

Depends on / 依赖: mul_zero
-/
theorem not_irreducible_zero [MonoidWithZero M] : ¬Irreducible (0 : M)
  | ⟨hn0, h⟩ =>
    have : IsUnit (0 : M) ∨ IsUnit (0 : M) := h (mul_zero 0).symm
    this.elim hn0 hn0

/--
theorem `Irreducible.ne_zero` / 定理 `Irreducible.ne_zero`

English:
theorem Irreducible.ne_zero
  given: [MonoidWithZero M]
  statement: forall {p : M}, Irreducible p -> p != 0

中文:
定理 Irreducible.ne_zero
  条件: [MonoidWithZero M]
  结论: 对任意 {p : M}, Irreducible p -> p != 0
-/
theorem Irreducible.ne_zero [MonoidWithZero M] : forall {p : M}, Irreducible p -> p != 0
  | _, hp, rfl => not_irreducible_zero hp

/--
theorem `Irreducible.dvd_symm` / 定理 `Irreducible.dvd_symm`

English:
theorem Irreducible.dvd_symm
  given: [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q)
  proof: by
  rintro ⟨q', rfl⟩
  rw [IsUnit.mul_right_dvd (Or.resolve_left (of_irreducible_mul hq) hp.not_isUnit)]

中文:
定理 Irreducible.dvd_symm
  条件: [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q)
  证明: by
  rintro ⟨q', rfl⟩
  rw [IsUnit.mul_right_dvd (Or.resolve_left (of_irreducible_mul hq) hp.not_isUnit)]

Depends on / 依赖: IsUnit, IsUnit.mul_right_dvd, Or.resolve_left, hp.not_isUnit, mul_right_dvd, not_isUnit, of_irreducible_mul, resolve_left
-/
theorem Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q) :
    p ∣ q -> q ∣ p := by
  rintro ⟨q', rfl⟩
  rw [IsUnit.mul_right_dvd (Or.resolve_left (of_irreducible_mul hq) hp.not_isUnit)]

/--
theorem `Irreducible.dvd_comm` / 定理 `Irreducible.dvd_comm`

English:
theorem Irreducible.dvd_comm
  given: [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q)
  proof: ⟨hp.dvd_symm hq, hq.dvd_symm hp⟩

中文:
定理 Irreducible.dvd_comm
  条件: [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q)
  证明: ⟨hp.dvd_symm hq, hq.dvd_symm hp⟩

Depends on / 依赖: dvd_symm, hp.dvd_symm, hq.dvd_symm
-/
theorem Irreducible.dvd_comm [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q) :
    p ∣ q ↔ q ∣ p :=
  ⟨hp.dvd_symm hq, hq.dvd_symm hp⟩

section CommMonoidWithZero

variable [CommMonoidWithZero M]

/--
theorem `Irreducible.prime_of_isPrimal` / 定理 `Irreducible.prime_of_isPrimal`

English:
theorem Irreducible.prime_of_isPrimal
  statement: {a : M}
  proof: ⟨irr.ne_zero, irr.not_isUnit, fun a b dvd => by
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := primal dvd
    exact (of_irreducible_mul irr).symm.imp (·.mul_right_dvd.mpr h₁) (·.mul_left_dvd.mpr h₂)⟩

中文:
定理 Irreducible.prime_of_isPrimal
  结论: {a : M}
  证明: ⟨irr.ne_zero, irr.not_isUnit, fun a b dvd => by
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := primal dvd
    exact (of_irreducible_mul irr).symm.imp (·.mul_right_dvd.mpr h₁) (·.mul_left_dvd.mpr h₂)⟩

Depends on / 依赖: irr.ne_zero, irr.not_isUnit, mul_left_dvd, mul_left_dvd.mpr, mul_right_dvd, mul_right_dvd.mpr, ne_zero, not_isUnit, of_irreducible_mul, primal, symm.imp
-/
theorem Irreducible.prime_of_isPrimal {a : M}
    (irr : Irreducible a) (primal : IsPrimal a) : Prime a :=
  ⟨irr.ne_zero, irr.not_isUnit, fun a b dvd => by
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := primal dvd
    exact (of_irreducible_mul irr).symm.imp (·.mul_right_dvd.mpr h₁) (·.mul_left_dvd.mpr h₂)⟩

/--
theorem `Irreducible.prime` / 定理 `Irreducible.prime`

English:
theorem Irreducible.prime
  given: [DecompositionMonoid M] {a : M} (irr : Irreducible a)
  statement: Prime a
  proof: irr.prime_of_isPrimal (DecompositionMonoid.primal a)

中文:
定理 Irreducible.prime
  条件: [DecompositionMonoid M] {a : M} (irr : Irreducible a)
  结论: Prime a
  证明: irr.prime_of_isPrimal (DecompositionMonoid.primal a)

Depends on / 依赖: DecompositionMonoid, DecompositionMonoid.primal, irr.prime_of_isPrimal, primal, prime_of_isPrimal
-/
theorem Irreducible.prime [DecompositionMonoid M] {a : M} (irr : Irreducible a) : Prime a :=
  irr.prime_of_isPrimal (DecompositionMonoid.primal a)

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable [CommMonoidWithZero M] [IsCancelMulZero M] {p : M}

/--
theorem `Prime.irreducible` / 定理 `Prime.irreducible`

English:
theorem Prime.irreducible
  given: (hp : Prime p)
  statement: Irreducible p
  proof: ⟨hp.not_isUnit, fun a b => by
    rintro rfl
    exact (hp.dvd_or_dvd dvd_rfl).symm.imp
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_right <| right_ne_zero_of_mul hp.ne_zero).mp <|
        dvd_mul_of_dvd_right · _)
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_left <| left_ne_zero_of_mul hp.ne_zero).

中文:
定理 Prime.irreducible
  条件: (hp : Prime p)
  结论: Irreducible p
  证明: ⟨hp.not_isUnit, fun a b => by
    rintro rfl
    exact (hp.dvd_or_dvd dvd_rfl).symm.imp
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_right <| right_ne_zero_of_mul hp.ne_zero).mp <|
        dvd_mul_of_dvd_right · _)
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_left <| left_ne_zero_of_mul hp.ne_zero).
-/
protected theorem Prime.irreducible (hp : Prime p) : Irreducible p :=
  ⟨hp.not_isUnit, fun a b => by
    rintro rfl
    exact (hp.dvd_or_dvd dvd_rfl).symm.imp
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_right <| right_ne_zero_of_mul hp.ne_zero).mp <|
        dvd_mul_of_dvd_right · _)
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_left <| left_ne_zero_of_mul hp.ne_zero).mp <|
        dvd_mul_of_dvd_left · _)⟩

/--
theorem `irreducible_iff_prime` / 定理 `irreducible_iff_prime`

English:
theorem irreducible_iff_prime
  given: [DecompositionMonoid M] {a : M}
  statement: Irreducible a ↔ Prime a
  proof: ⟨Irreducible.prime, Prime.irreducible⟩

中文:
定理 irreducible_iff_prime
  条件: [DecompositionMonoid M] {a : M}
  结论: Irreducible a ↔ Prime a
  证明: ⟨Irreducible.prime, Prime.irreducible⟩

Depends on / 依赖: Irreducible, Irreducible.prime, Prime.irreducible, irreducible
-/
theorem irreducible_iff_prime [DecompositionMonoid M] {a : M} : Irreducible a ↔ Prime a :=
  ⟨Irreducible.prime, Prime.irreducible⟩

end CancelCommMonoidWithZero
