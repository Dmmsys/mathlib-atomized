/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Cast.Commute

/-!
# Invertibility of elements given a characteristic

This file includes some instances of `Invertible` for specific numbers in
characteristic zero. Some more cases are given as a `def`, to be included only
when needed. To construct instances for concrete numbers,
`invertibleOfNonzero` is a useful definition.
-/

@[expose] public section


variable {R K : Type*}

/-- When two is invertible, every element is `Even`. -/
@[simp]
/--
theorem `Even.all` / 定理 `Even.all`

English:
theorem Even.all
  given: [Semiring R] [Invertible (2 : R)] (a : R)
  statement: Even a
  proof: .of_isUnit_two (isUnit_of_invertible _) _

中文:
定理 Even.all
  条件: [Semiring R] [Invertible (2 : R)] (a : R)
  结论: Even a
  证明: .of_isUnit_two (isUnit_of_invertible _) _

Depends on / 依赖: isUnit_of_invertible, of_isUnit_two
-/
theorem Even.all [Semiring R] [Invertible (2 : R)] (a : R) : Even a :=
  .of_isUnit_two (isUnit_of_invertible _) _

/-- When two is invertible in a ring, every element is `Odd`. -/
@[simp low]
/--
theorem `Odd.all` / 定理 `Odd.all`

English:
theorem Odd.all
  given: [Ring R] [Invertible (2 : R)] (a : R)
  statement: Odd a
  proof: .of_isUnit_two (isUnit_of_invertible _) _

中文:
定理 Odd.all
  条件: [Ring R] [Invertible (2 : R)] (a : R)
  结论: Odd a
  证明: .of_isUnit_two (isUnit_of_invertible _) _

Depends on / 依赖: isUnit_of_invertible, of_isUnit_two
-/
theorem Odd.all [Ring R] [Invertible (2 : R)] (a : R) : Odd a :=
  .of_isUnit_two (isUnit_of_invertible _) _

section Ring
variable [Ring R] {p : Nat} [CharP R p]

/--
theorem `not_ringChar_dvd_of_invertible` / 定理 `not_ringChar_dvd_of_invertible`

English:
theorem not_ringChar_dvd_of_invertible
  given: {t : Nat} [Invertible (t : R)] [Nontrivial R]
  proof: by
  rw [← ringChar.spec]; rw [← Ne]
  exact Invertible.ne_zero (t : R)

中文:
定理 not_ringChar_dvd_of_invertible
  条件: {t : 自然数} [Invertible (t : R)] [Nontrivial R]
  证明: by
  rw [← ringChar.spec]; rw [← Ne]
  exact Invertible.ne_zero (t : R)

Depends on / 依赖: Invertible, Invertible.ne_zero, ne_zero, ringChar, ringChar.spec
-/
theorem not_ringChar_dvd_of_invertible {t : Nat} [Invertible (t : R)] [Nontrivial R] :
    ¬ringChar R ∣ t := by
  rw [← ringChar.spec]; rw [← Ne]
  exact Invertible.ne_zero (t : R)

/--
theorem `CharP.intCast_mul_natCast_gcdA_eq_gcd` / 定理 `CharP.intCast_mul_natCast_gcdA_eq_gcd`

English:
theorem CharP.intCast_mul_natCast_gcdA_eq_gcd
  given: (n : Nat)
  proof: by
  suffices ↑(n * n.gcdA p + p * n.gcdB p : Int) = ((n.gcd p : Int) : R) by simpa using this
  rw [← Nat.gcd_eq_gcd_ab]

中文:
定理 CharP.intCast_mul_natCast_gcdA_eq_gcd
  条件: (n : 自然数)
  证明: by
  suffices ↑(n * n.gcdA p + p * n.gcdB p : Int) = ((n.gcd p : Int) : R) by simpa using this
  rw [← Nat.gcd_eq_gcd_ab]

Depends on / 依赖: Nat.gcd_eq_gcd_ab, gcd_eq_gcd_ab, n.gcd, n.gcdA, n.gcdB
-/
theorem CharP.intCast_mul_natCast_gcdA_eq_gcd (n : Nat) :
    (n * n.gcdA p : R) = n.gcd p := by
  suffices ↑(n * n.gcdA p + p * n.gcdB p : Int) = ((n.gcd p : Int) : R) by simpa using this
  rw [← Nat.gcd_eq_gcd_ab]

/--
theorem `CharP.natCast_gcdA_mul_intCast_eq_gcd` / 定理 `CharP.natCast_gcdA_mul_intCast_eq_gcd`

English:
theorem CharP.natCast_gcdA_mul_intCast_eq_gcd
  given: (n : Nat)
  proof: .eq.trans CharP.intCast_mul_natCast_gcdA_eq_gcd n Nat.commute_cast _ _

中文:
定理 CharP.natCast_gcdA_mul_intCast_eq_gcd
  条件: (n : 自然数)
  证明: .eq.trans CharP.intCast_mul_natCast_gcdA_eq_gcd n Nat.commute_cast _ _

Depends on / 依赖: CharP.intCast_mul_natCast_gcdA_eq_gcd, Nat.commute_cast, commute_cast, eq.trans, intCast_mul_natCast_gcdA_eq_gcd
-/
theorem CharP.natCast_gcdA_mul_intCast_eq_gcd (n : Nat) :
    (n.gcdA p * n : R) = n.gcd p :=
.eq.trans CharP.intCast_mul_natCast_gcdA_eq_gcd n Nat.commute_cast _ _

/-- In a ring of characteristic `p`, `(n : R)` is invertible when `n` is coprime with `p`, with
inverse `n.gcdA p`. -/
@[instance_reducible]
/--
Definition of `invertibleOfCoprime` / `invertibleOfCoprime` 的定义

English:
definition invertibleOfCoprime
  signature: {n : Nat} (h : n.Coprime p)
  body: n.gcdA p
  invOf_mul_self := by rw [CharP.natCast_gcdA_mul_intCast_eq_gcd, h, Nat.cast_one]
  mul_invOf_self := by rw [CharP.intCast_mul_natCast_gcdA_eq_gcd, h, Nat.cast_one]

中文:
定义 invertibleOfCoprime
  签名: {n : 自然数} (h : n.Coprime p)
  定义体: n.gcdA p
  invOf_mul_self := by rw [CharP.natCast_gcdA_mul_intCast_eq_gcd, h, Nat.cast_one]
  mul_invOf_self := by rw [CharP.intCast_mul_natCast_gcdA_eq_gcd, h, Nat.cast_one]

Depends on / 依赖: n.gcdA
-/
def invertibleOfCoprime {n : Nat} (h : n.Coprime p) :
    Invertible (n : R) where
  invOf := n.gcdA p
  invOf_mul_self := by rw [CharP.natCast_gcdA_mul_intCast_eq_gcd, h, Nat.cast_one]
  mul_invOf_self := by rw [CharP.intCast_mul_natCast_gcdA_eq_gcd, h, Nat.cast_one]

/--
theorem `invOf_eq_of_coprime` / 定理 `invOf_eq_of_coprime`

English:
theorem invOf_eq_of_coprime
  given: {n : Nat} [Invertible (n : R)] (h : n.Coprime p)
  proof: by
  let : Invertible (n : R) := invertibleOfCoprime h
  convert! (rfl : ⅟(n : R) = _)

中文:
定理 invOf_eq_of_coprime
  条件: {n : 自然数} [Invertible (n : R)] (h : n.Coprime p)
  证明: by
  let : Invertible (n : R) := invertibleOfCoprime h
  convert! (rfl : ⅟(n : R) = _)

Depends on / 依赖: Invertible, convert, invertibleOfCoprime
-/
theorem invOf_eq_of_coprime {n : Nat} [Invertible (n : R)] (h : n.Coprime p) :
    ⅟(n : R) = n.gcdA p := by
  let : Invertible (n : R) := invertibleOfCoprime h
  convert! (rfl : ⅟(n : R) = _)

/--
theorem `CharP.isUnit_natCast_iff` / 定理 `CharP.isUnit_natCast_iff`

English:
theorem CharP.isUnit_natCast_iff
  given: {n : Nat} (hp : p.Prime)
  statement: IsUnit (n : R) ↔ ¬p ∣ n where
  proof: by
    have := CharP.nontrivial_of_char_ne_one (R := R) hp.ne_one
    rw [← CharP.cast_eq_zero_iff (R := R)]
    exact h.ne_zero
  mpr not_dvd :=
    letI := invertibleOfCoprime (R := R) (hp.coprime_iff_not_dvd.2 not_dvd).symm
    isUnit_of_invertible _

中文:
定理 CharP.isUnit_natCast_iff
  条件: {n : 自然数} (hp : p.Prime)
  结论: IsUnit (n : R) ↔ ¬p ∣ n where
  证明: by
    have := CharP.nontrivial_of_char_ne_one (R := R) hp.ne_one
    rw [← CharP.cast_eq_zero_iff (R := R)]
    exact h.ne_zero
  mpr not_dvd :=
    letI := invertibleOfCoprime (R := R) (hp.coprime_iff_not_dvd.2 not_dvd).symm
    isUnit_of_invertible _

Depends on / 依赖: CharP.cast_eq_zero_iff, CharP.nontrivial_of_char_ne_one, cast_eq_zero_iff, coprime_iff_not_dvd, h.ne_zero, hp.coprime_iff_not_dvd, hp.ne_one, invertibleOfCoprime, isUnit_of_invertible, ne_one, ne_zero, nontrivial_of_char_ne_one, not_dvd
-/
theorem CharP.isUnit_natCast_iff {n : Nat} (hp : p.Prime) : IsUnit (n : R) ↔ ¬p ∣ n where
  mp h := by
    have := CharP.nontrivial_of_char_ne_one (R := R) hp.ne_one
    rw [← CharP.cast_eq_zero_iff (R := R)]
    exact h.ne_zero
  mpr not_dvd :=
    letI := invertibleOfCoprime (R := R) (hp.coprime_iff_not_dvd.2 not_dvd).symm
    isUnit_of_invertible _

/--
theorem `CharP.isUnit_ofNat_iff` / 定理 `CharP.isUnit_ofNat_iff`

English:
theorem CharP.isUnit_ofNat_iff
  given: {n : Nat} [n.AtLeastTwo] (hp : p.Prime)
  proof: CharP.isUnit_natCast_iff hp

中文:
定理 CharP.isUnit_ofNat_iff
  条件: {n : 自然数} [n.AtLeastTwo] (hp : p.Prime)
  证明: CharP.isUnit_natCast_iff hp

Depends on / 依赖: CharP.isUnit_natCast_iff, isUnit_natCast_iff
-/
theorem CharP.isUnit_ofNat_iff {n : Nat} [n.AtLeastTwo] (hp : p.Prime) :
    IsUnit (ofNat(n) : R) ↔ ¬p ∣ ofNat(n) :=
  CharP.isUnit_natCast_iff hp

/--
theorem `CharP.isUnit_intCast_iff` / 定理 `CharP.isUnit_intCast_iff`

English:
theorem CharP.isUnit_intCast_iff
  given: {z : Int} (hp : p.Prime)
  statement: IsUnit (z : R) ↔ ¬↑p ∣ z
  proof: by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp [CharP.isUnit_natCast_iff hp, Int.ofNat_dvd]
  · simp [CharP.isUnit_natCast_iff hp, Int.dvd_neg, Int.ofNat_dvd]

中文:
定理 CharP.isUnit_intCast_iff
  条件: {z : 整数} (hp : p.Prime)
  结论: IsUnit (z : R) ↔ ¬↑p ∣ z
  证明: by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp [CharP.isUnit_natCast_iff hp, Int.ofNat_dvd]
  · simp [CharP.isUnit_natCast_iff hp, Int.dvd_neg, Int.ofNat_dvd]

Depends on / 依赖: CharP.isUnit_natCast_iff, Int.dvd_neg, Int.ofNat_dvd, dvd_neg, eq_nat_or_neg, isUnit_natCast_iff, ofNat_dvd, z.eq_nat_or_neg
-/
theorem CharP.isUnit_intCast_iff {z : Int} (hp : p.Prime) : IsUnit (z : R) ↔ ¬↑p ∣ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp [CharP.isUnit_natCast_iff hp, Int.ofNat_dvd]
  · simp [CharP.isUnit_natCast_iff hp, Int.dvd_neg, Int.ofNat_dvd]

end Ring

section Semifield
variable [Semifield K]

/-- A natural number `t` is invertible in a semifield `K` if the characteristic of `K` does not
divide `t`. -/
@[instance_reducible]
/--
Definition of `invertibleOfRingCharNotDvd` / `invertibleOfRingCharNotDvd` 的定义

English:
definition invertibleOfRingCharNotDvd
  signature: {t : Nat} (not_dvd : ¬ringChar K ∣ t)
  body: invertibleOfNonzero fun h => not_dvd ((ringChar.spec K t).mp h)

中文:
定义 invertibleOfRingCharNotDvd
  签名: {t : 自然数} (not_dvd : ¬ringChar K ∣ t)
  定义体: invertibleOfNonzero fun h => not_dvd ((ringChar.spec K t).mp h)

Depends on / 依赖: invertibleOfNonzero, not_dvd, ringChar, ringChar.spec
-/
def invertibleOfRingCharNotDvd {t : Nat} (not_dvd : ¬ringChar K ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((ringChar.spec K t).mp h)

/-- A natural number `t` is invertible in a semifield `K` of characteristic `p` if `p` does not
divide `t`. -/
@[instance_reducible]
/--
Definition of `invertibleOfCharPNotDvd` / `invertibleOfCharPNotDvd` 的定义

English:
definition invertibleOfCharPNotDvd
  signature: {p : Nat} [CharP K p] {t : Nat} (not_dvd : ¬p ∣ t)
  body: invertibleOfNonzero fun h => not_dvd ((CharP.cast_eq_zero_iff K p t).mp h)

中文:
定义 invertibleOfCharPNotDvd
  签名: {p : 自然数} [CharP K p] {t : 自然数} (not_dvd : ¬p ∣ t)
  定义体: invertibleOfNonzero fun h => not_dvd ((CharP.cast_eq_zero_iff K p t).mp h)

Depends on / 依赖: CharP.cast_eq_zero_iff, cast_eq_zero_iff, invertibleOfNonzero, not_dvd
-/
def invertibleOfCharPNotDvd {p : Nat} [CharP K p] {t : Nat} (not_dvd : ¬p ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((CharP.cast_eq_zero_iff K p t).mp h)

-- warning: this could potentially loop with `Invertible.ne_zero` - if there are weird type-class
-- loops, watch out for that.
/--
Instance `invertibleOfPos` / 实例 `invertibleOfPos`

English:
instance invertibleOfPos
  signature: [CharZero K] (n : Nat) [NeZero n]
  body: invertibleOfNonzero NeZero.out

中文:
实例 invertibleOfPos
  签名: [CharZero K] (n : 自然数) [NeZero n]
  定义体: invertibleOfNonzero NeZero.out

Depends on / 依赖: NeZero, NeZero.out, invertibleOfNonzero
-/
instance invertibleOfPos [CharZero K] (n : Nat) [NeZero n] : Invertible (n : K) :=
invertibleOfNonzero NeZero.out

end Semifield

section DivisionSemiring
variable [DivisionSemiring K] [CharZero K]

/--
Instance `invertibleSucc` / 实例 `invertibleSucc`

English:
instance invertibleSucc
  signature: (n : Nat)
  body: invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))

中文:
实例 invertibleSucc
  签名: (n : 自然数)
  定义体: invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))

Depends on / 依赖: Nat.cast_ne_zero.mpr, Nat.succ_ne_zero, cast_ne_zero, invertibleOfNonzero, succ_ne_zero
-/
instance invertibleSucc (n : Nat) : Invertible (n.succ : K) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))



/--
Instance `invertibleTwo` / 实例 `invertibleTwo`

English:
instance invertibleTwo
  signature: : Invertible (2 : K)
  body: invertibleOfNonzero (mod_cast (by decide : 2 != 0))

中文:
实例 invertibleTwo
  签名: : Invertible (2 : K)
  定义体: invertibleOfNonzero (mod_cast (by decide : 2 != 0))

Depends on / 依赖: invertibleOfNonzero, mod_cast
-/
instance invertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero (mod_cast (by decide : 2 != 0))

/--
Instance `invertibleThree` / 实例 `invertibleThree`

English:
instance invertibleThree
  signature: : Invertible (3 : K)
  body: invertibleOfNonzero (mod_cast (by decide : 3 != 0))

中文:
实例 invertibleThree
  签名: : Invertible (3 : K)
  定义体: invertibleOfNonzero (mod_cast (by decide : 3 != 0))

Depends on / 依赖: invertibleOfNonzero, mod_cast
-/
instance invertibleThree : Invertible (3 : K) :=
  invertibleOfNonzero (mod_cast (by decide : 3 != 0))

end DivisionSemiring
