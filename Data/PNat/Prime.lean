/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.PNat.Basic

/-!
# Primality and GCD on pnat

This file extends the theory of `ℕ+` with `gcd`, `lcm` and `Prime` functions, analogous to those on
`Nat`.
-/

@[expose] public section


namespace Nat.Primes

/--
Definition of `toPNat` / `toPNat` 的定义

English:
definition toPNat
  signature: : Nat.Primes -> Nat+
  body: fun p => ⟨(p : Nat), p.property.pos⟩

中文:
定义 toP自然数
  签名: : 自然数.Primes -> 自然数+
  定义体: fun p => ⟨(p : Nat), p.property.pos⟩
-/
@[coe] def toPNat : Nat.Primes -> Nat+ :=
  fun p => ⟨(p : Nat), p.property.pos⟩

/--
Instance `coePNat` / 实例 `coePNat`

English:
instance coePNat
  signature: : Coe Nat.Primes Nat+
  body: ⟨toPNat⟩

@[norm_cast]

中文:
实例 coeP自然数
  签名: : Coe 自然数.Primes 自然数+
  定义体: ⟨toPNat⟩

@[norm_cast]

Depends on / 依赖: toPNat
-/
instance coePNat : Coe Nat.Primes Nat+ :=
  ⟨toPNat⟩

@[norm_cast]
/--
theorem `coe_pnat_nat` / 定理 `coe_pnat_nat`

English:
theorem coe_pnat_nat
  given: (p : Nat.Primes)
  statement: ((p : Nat+) : Nat) = p
  proof: rfl

中文:
定理 coe_pnat_nat
  条件: (p : 自然数.Primes)
  结论: ((p : 自然数+) : 自然数) = p
  证明: rfl
-/
theorem coe_pnat_nat (p : Nat.Primes) : ((p : Nat+) : Nat) = p :=
  rfl

/--
theorem `coe_pnat_injective` / 定理 `coe_pnat_injective`

English:
theorem coe_pnat_injective
  statement: Function.Injective ((↑) : Nat.Primes -> Nat+)
  proof: fun p q h =>
  Subtype.ext (by injection h)

@[norm_cast]

中文:
定理 coe_pnat_injective
  结论: 函数.单射 ((↑) : 自然数.Primes -> 自然数+)
  证明: fun p q h =>
  Subtype.ext (by injection h)

@[norm_cast]
-/
theorem coe_pnat_injective : Function.Injective ((↑) : Nat.Primes -> Nat+) := fun p q h =>
  Subtype.ext (by injection h)

@[norm_cast]
/--
theorem `coe_pnat_inj` / 定理 `coe_pnat_inj`

English:
theorem coe_pnat_inj
  given: (p q : Nat.Primes)
  statement: (p : Nat+) = (q : Nat+) ↔ p = q
  proof: coe_pnat_injective.eq_iff

中文:
定理 coe_pnat_inj
  条件: (p q : 自然数.Primes)
  结论: (p : 自然数+) = (q : 自然数+) ↔ p = q
  证明: coe_pnat_injective.eq_iff

Depends on / 依赖: coe_pnat_injective, coe_pnat_injective.eq_iff, eq_iff
-/
theorem coe_pnat_inj (p q : Nat.Primes) : (p : Nat+) = (q : Nat+) ↔ p = q :=
  coe_pnat_injective.eq_iff

end Nat.Primes

namespace PNat

open Nat

/--
Definition of `gcd` / `gcd` 的定义

English:
definition gcd
  signature: (n m : Nat+)
  body: ⟨Nat.gcd (n : Nat) (m : Nat), Nat.gcd_pos_of_pos_left (m : Nat) n.pos⟩

中文:
定义 最大公约数
  签名: (n m : 自然数+)
  定义体: ⟨Nat.gcd (n : Nat) (m : Nat), Nat.gcd_pos_of_pos_left (m : Nat) n.pos⟩

Depends on / 依赖: Nat.gcd, Nat.gcd_pos_of_pos_left, gcd_pos_of_pos_left, n.pos
-/
def gcd (n m : Nat+) : Nat+ :=
  ⟨Nat.gcd (n : Nat) (m : Nat), Nat.gcd_pos_of_pos_left (m : Nat) n.pos⟩

/--
Definition of `lcm` / `lcm` 的定义

English:
definition lcm
  signature: (n m : Nat+)
  body: ⟨Nat.lcm (n : Nat) (m : Nat), by
    let h := mul_pos n.pos m.pos
    rw [← gcd_mul_lcm (n : Nat) (m : Nat)]; rw [mul_comm] at h
    exact pos_of_dvd_of_pos (Dvd.intro (Nat.gcd (n : Nat) (m : Nat)) rfl) h⟩

@[simp, norm_cast]

中文:
定义 最小公倍数
  签名: (n m : 自然数+)
  定义体: ⟨Nat.lcm (n : Nat) (m : Nat), by
    let h := mul_pos n.pos m.pos
    rw [← gcd_mul_lcm (n : Nat) (m : Nat)]; rw [mul_comm] at h
    exact pos_of_dvd_of_pos (Dvd.intro (Nat.gcd (n : Nat) (m : Nat)) rfl) h⟩

@[simp, norm_cast]

Depends on / 依赖: Dvd.intro, Nat.gcd, Nat.lcm, gcd_mul_lcm, m.pos, mul_comm, mul_pos, n.pos, pos_of_dvd_of_pos
-/
def lcm (n m : Nat+) : Nat+ :=
  ⟨Nat.lcm (n : Nat) (m : Nat), by
    let h := mul_pos n.pos m.pos
    rw [← gcd_mul_lcm (n : Nat) (m : Nat)]; rw [mul_comm] at h
    exact pos_of_dvd_of_pos (Dvd.intro (Nat.gcd (n : Nat) (m : Nat)) rfl) h⟩

@[simp, norm_cast]
/--
theorem `gcd_coe` / 定理 `gcd_coe`

English:
theorem gcd_coe
  given: (n m : Nat+)
  statement: (gcd n m : Nat) = Nat.gcd n m
  proof: rfl

@[simp, norm_cast]

中文:
定理 gcd_coe
  条件: (n m : 自然数+)
  结论: (最大公约数 n m : 自然数) = 自然数.最大公约数 n m
  证明: rfl

@[simp, norm_cast]
-/
theorem gcd_coe (n m : Nat+) : (gcd n m : Nat) = Nat.gcd n m :=
  rfl

@[simp, norm_cast]
/--
theorem `lcm_coe` / 定理 `lcm_coe`

English:
theorem lcm_coe
  given: (n m : Nat+)
  statement: (lcm n m : Nat) = Nat.lcm n m
  proof: rfl

中文:
定理 lcm_coe
  条件: (n m : 自然数+)
  结论: (最小公倍数 n m : 自然数) = 自然数.最小公倍数 n m
  证明: rfl
-/
theorem lcm_coe (n m : Nat+) : (lcm n m : Nat) = Nat.lcm n m :=
  rfl

/--
theorem `gcd_dvd_left` / 定理 `gcd_dvd_left`

English:
theorem gcd_dvd_left
  given: (n m : Nat+)
  statement: gcd n m ∣ n
  proof: dvd_iff.2 (Nat.gcd_dvd_left (n : Nat) (m : Nat))

中文:
定理 gcd_dvd_left
  条件: (n m : 自然数+)
  结论: 最大公约数 n m ∣ n
  证明: dvd_iff.2 (Nat.gcd_dvd_left (n : Nat) (m : Nat))

Depends on / 依赖: Nat.gcd_dvd_left, dvd_iff, gcd_dvd_left
-/
theorem gcd_dvd_left (n m : Nat+) : gcd n m ∣ n :=
  dvd_iff.2 (Nat.gcd_dvd_left (n : Nat) (m : Nat))

/--
theorem `gcd_dvd_right` / 定理 `gcd_dvd_right`

English:
theorem gcd_dvd_right
  given: (n m : Nat+)
  statement: gcd n m ∣ m
  proof: dvd_iff.2 (Nat.gcd_dvd_right (n : Nat) (m : Nat))

中文:
定理 gcd_dvd_right
  条件: (n m : 自然数+)
  结论: 最大公约数 n m ∣ m
  证明: dvd_iff.2 (Nat.gcd_dvd_right (n : Nat) (m : Nat))

Depends on / 依赖: Nat.gcd_dvd_right, dvd_iff, gcd_dvd_right
-/
theorem gcd_dvd_right (n m : Nat+) : gcd n m ∣ m :=
  dvd_iff.2 (Nat.gcd_dvd_right (n : Nat) (m : Nat))

/--
theorem `dvd_gcd` / 定理 `dvd_gcd`

English:
theorem dvd_gcd
  given: {m n k : Nat+} (hm : k ∣ m) (hn : k ∣ n)
  statement: k ∣ gcd m n
  proof: dvd_iff.2 (Nat.dvd_gcd (dvd_iff.1 hm) (dvd_iff.1 hn))

中文:
定理 dvd_gcd
  条件: {m n k : 自然数+} (hm : k ∣ m) (hn : k ∣ n)
  结论: k ∣ 最大公约数 m n
  证明: dvd_iff.2 (Nat.dvd_gcd (dvd_iff.1 hm) (dvd_iff.1 hn))

Depends on / 依赖: Nat.dvd_gcd, dvd_gcd, dvd_iff
-/
theorem dvd_gcd {m n k : Nat+} (hm : k ∣ m) (hn : k ∣ n) : k ∣ gcd m n :=
  dvd_iff.2 (Nat.dvd_gcd (dvd_iff.1 hm) (dvd_iff.1 hn))

/--
theorem `dvd_lcm_left` / 定理 `dvd_lcm_left`

English:
theorem dvd_lcm_left
  given: (n m : Nat+)
  statement: n ∣ lcm n m
  proof: dvd_iff.2 (Nat.dvd_lcm_left (n : Nat) (m : Nat))

中文:
定理 dvd_lcm_left
  条件: (n m : 自然数+)
  结论: n ∣ 最小公倍数 n m
  证明: dvd_iff.2 (Nat.dvd_lcm_left (n : Nat) (m : Nat))

Depends on / 依赖: Nat.dvd_lcm_left, dvd_iff, dvd_lcm_left
-/
theorem dvd_lcm_left (n m : Nat+) : n ∣ lcm n m :=
  dvd_iff.2 (Nat.dvd_lcm_left (n : Nat) (m : Nat))

/--
theorem `dvd_lcm_right` / 定理 `dvd_lcm_right`

English:
theorem dvd_lcm_right
  given: (n m : Nat+)
  statement: m ∣ lcm n m
  proof: dvd_iff.2 (Nat.dvd_lcm_right (n : Nat) (m : Nat))

中文:
定理 dvd_lcm_right
  条件: (n m : 自然数+)
  结论: m ∣ 最小公倍数 n m
  证明: dvd_iff.2 (Nat.dvd_lcm_right (n : Nat) (m : Nat))

Depends on / 依赖: Nat.dvd_lcm_right, dvd_iff, dvd_lcm_right
-/
theorem dvd_lcm_right (n m : Nat+) : m ∣ lcm n m :=
  dvd_iff.2 (Nat.dvd_lcm_right (n : Nat) (m : Nat))

/--
theorem `lcm_dvd` / 定理 `lcm_dvd`

English:
theorem lcm_dvd
  given: {m n k : Nat+} (hm : m ∣ k) (hn : n ∣ k)
  statement: lcm m n ∣ k
  proof: dvd_iff.2 (@Nat.lcm_dvd (m : Nat) (n : Nat) (k : Nat) (dvd_iff.1 hm) (dvd_iff.1 hn))

中文:
定理 lcm_dvd
  条件: {m n k : 自然数+} (hm : m ∣ k) (hn : n ∣ k)
  结论: 最小公倍数 m n ∣ k
  证明: dvd_iff.2 (@Nat.lcm_dvd (m : Nat) (n : Nat) (k : Nat) (dvd_iff.1 hm) (dvd_iff.1 hn))

Depends on / 依赖: Nat.lcm_dvd, dvd_iff, lcm_dvd
-/
theorem lcm_dvd {m n k : Nat+} (hm : m ∣ k) (hn : n ∣ k) : lcm m n ∣ k :=
  dvd_iff.2 (@Nat.lcm_dvd (m : Nat) (n : Nat) (k : Nat) (dvd_iff.1 hm) (dvd_iff.1 hn))

/--
theorem `gcd_mul_lcm` / 定理 `gcd_mul_lcm`

English:
theorem gcd_mul_lcm
  given: (n m : Nat+)
  statement: gcd n m * lcm n m = n * m
  proof: Subtype.ext (Nat.gcd_mul_lcm (n : Nat) (m : Nat))

中文:
定理 gcd_mul_lcm
  条件: (n m : 自然数+)
  结论: 最大公约数 n m * 最小公倍数 n m = n * m
  证明: Subtype.ext (Nat.gcd_mul_lcm (n : Nat) (m : Nat))

Depends on / 依赖: Nat.gcd_mul_lcm, Subtype, Subtype.ext, gcd_mul_lcm
-/
theorem gcd_mul_lcm (n m : Nat+) : gcd n m * lcm n m = n * m :=
  Subtype.ext (Nat.gcd_mul_lcm (n : Nat) (m : Nat))

-- TODO: this is an iff, and should be moved to an earlier file.
/--
theorem `eq_one_of_lt_two` / 定理 `eq_one_of_lt_two`

English:
theorem eq_one_of_lt_two
  given: {n : Nat+}
  statement: n < 2 -> n = 1
  proof: by
  change n < 1 + 1 -> _
  rw [lt_add_one_iff]; rw [le_one_iff_eq_one]
  exact id

中文:
定理 eq_one_of_lt_two
  条件: {n : 自然数+}
  结论: n < 2 -> n = 1
  证明: by
  change n < 1 + 1 -> _
  rw [lt_add_one_iff]; rw [le_one_iff_eq_one]
  exact id

Depends on / 依赖: le_one_iff_eq_one, lt_add_one_iff
-/
theorem eq_one_of_lt_two {n : Nat+} : n < 2 -> n = 1 := by
  change n < 1 + 1 -> _
  rw [lt_add_one_iff]; rw [le_one_iff_eq_one]
  exact id

section Prime

/-! ### Prime numbers -/


/--
Definition of `Prime` / `Prime` 的定义

English:
definition Prime
  signature: (p : Nat+)
  body: (p : Nat).Prime

中文:
定义 素
  签名: (p : 自然数+)
  定义体: (p : Nat).Prime
-/
def Prime (p : Nat+) : Prop :=
  (p : Nat).Prime

/--
theorem `Prime.one_lt` / 定理 `Prime.one_lt`

English:
theorem Prime.one_lt
  given: {p : Nat+}
  statement: p.Prime -> 1 < p
  proof: Nat.Prime.one_lt

中文:
定理 素.one_lt
  条件: {p : 自然数+}
  结论: p.素 -> 1 < p
  证明: Nat.Prime.one_lt
-/
theorem Prime.one_lt {p : Nat+} : p.Prime -> 1 < p :=
  Nat.Prime.one_lt

/--
theorem `prime_two` / 定理 `prime_two`

English:
theorem prime_two
  statement: (2 : Nat+).Prime
  proof: Nat.prime_two

中文:
定理 prime_two
  结论: (2 : 自然数+).素
  证明: Nat.prime_two

Depends on / 依赖: Nat.prime_two, prime_two
-/
theorem prime_two : (2 : Nat+).Prime :=
  Nat.prime_two

instance {p : Nat+} [h : Fact p.Prime] : Fact (p : Nat).Prime := h

/--
Instance `fact_prime_two` / 实例 `fact_prime_two`

English:
instance fact_prime_two
  signature: : Fact (2 : Nat+).Prime
  body: ⟨prime_two⟩

中文:
实例 fact_prime_two
  签名: : Fact (2 : 自然数+).素
  定义体: ⟨prime_two⟩

Depends on / 依赖: prime_two
-/
instance fact_prime_two : Fact (2 : Nat+).Prime :=
  ⟨prime_two⟩

/--
theorem `prime_three` / 定理 `prime_three`

English:
theorem prime_three
  statement: (3 : Nat+).Prime
  proof: Nat.prime_three

中文:
定理 prime_three
  结论: (3 : 自然数+).素
  证明: Nat.prime_three

Depends on / 依赖: Nat.prime_three, prime_three
-/
theorem prime_three : (3 : Nat+).Prime :=
  Nat.prime_three

/--
Instance `fact_prime_three` / 实例 `fact_prime_three`

English:
instance fact_prime_three
  signature: : Fact (3 : Nat+).Prime
  body: ⟨prime_three⟩

中文:
实例 fact_prime_three
  签名: : Fact (3 : 自然数+).素
  定义体: ⟨prime_three⟩

Depends on / 依赖: prime_three
-/
instance fact_prime_three : Fact (3 : Nat+).Prime :=
  ⟨prime_three⟩

/--
theorem `prime_five` / 定理 `prime_five`

English:
theorem prime_five
  statement: (5 : Nat+).Prime
  proof: Nat.prime_five

中文:
定理 prime_five
  结论: (5 : 自然数+).素
  证明: Nat.prime_five

Depends on / 依赖: Nat.prime_five, prime_five
-/
theorem prime_five : (5 : Nat+).Prime :=
  Nat.prime_five

/--
Instance `fact_prime_five` / 实例 `fact_prime_five`

English:
instance fact_prime_five
  signature: : Fact (5 : Nat+).Prime
  body: ⟨prime_five⟩

中文:
实例 fact_prime_five
  签名: : Fact (5 : 自然数+).素
  定义体: ⟨prime_five⟩

Depends on / 依赖: prime_five
-/
instance fact_prime_five : Fact (5 : Nat+).Prime :=
  ⟨prime_five⟩

/--
theorem `dvd_prime` / 定理 `dvd_prime`

English:
theorem dvd_prime
  given: {p m : Nat+} (pp : p.Prime)
  statement: m ∣ p ↔ m = 1 ∨ m = p
  proof: by
  rw [PNat.dvd_iff]
  rw [Nat.dvd_prime pp]
  simp

中文:
定理 dvd_prime
  条件: {p m : 自然数+} (pp : p.素)
  结论: m ∣ p ↔ m = 1 ∨ m = p
  证明: by
  rw [PNat.dvd_iff]
  rw [Nat.dvd_prime pp]
  simp

Depends on / 依赖: Nat.dvd_prime, PNat.dvd_iff, dvd_iff, dvd_prime
-/
theorem dvd_prime {p m : Nat+} (pp : p.Prime) : m ∣ p ↔ m = 1 ∨ m = p := by
  rw [PNat.dvd_iff]
  rw [Nat.dvd_prime pp]
  simp

/--
theorem `Prime.ne_one` / 定理 `Prime.ne_one`

English:
theorem Prime.ne_one
  given: {p : Nat+}
  statement: p.Prime -> p != 1
  proof: by
  intro pp contra
  apply Nat.Prime.ne_one pp
  rw [PNat.coe_eq_one_iff]
  apply contra

@[simp]

中文:
定理 素.ne_one
  条件: {p : 自然数+}
  结论: p.素 -> p != 1
  证明: by
  intro pp contra
  apply Nat.Prime.ne_one pp
  rw [PNat.coe_eq_one_iff]
  apply contra

@[simp]
-/
theorem Prime.ne_one {p : Nat+} : p.Prime -> p != 1 := by
  intro pp contra
  apply Nat.Prime.ne_one pp
  rw [PNat.coe_eq_one_iff]
  apply contra

@[simp]
/--
theorem `not_prime_one` / 定理 `not_prime_one`

English:
theorem not_prime_one
  statement: ¬(1 : Nat+).Prime
  proof: Nat.not_prime_one

中文:
定理 not_prime_one
  结论: ¬(1 : 自然数+).素
  证明: Nat.not_prime_one

Depends on / 依赖: Nat.not_prime_one, not_prime_one
-/
theorem not_prime_one : ¬(1 : Nat+).Prime :=
  Nat.not_prime_one

/--
theorem `Prime.not_dvd_one` / 定理 `Prime.not_dvd_one`

English:
theorem Prime.not_dvd_one
  given: {p : Nat+}
  statement: p.Prime -> ¬p ∣ 1
  proof: fun pp : p.Prime => by
  rw [dvd_iff]
  apply Nat.Prime.not_dvd_one pp

中文:
定理 素.not_dvd_one
  条件: {p : 自然数+}
  结论: p.素 -> ¬p ∣ 1
  证明: fun pp : p.Prime => by
  rw [dvd_iff]
  apply Nat.Prime.not_dvd_one pp
-/
theorem Prime.not_dvd_one {p : Nat+} : p.Prime -> ¬p ∣ 1 := fun pp : p.Prime => by
  rw [dvd_iff]
  apply Nat.Prime.not_dvd_one pp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_prime_and_dvd` / 定理 `exists_prime_and_dvd`

English:
theorem exists_prime_and_dvd
  given: {n : Nat+} (hn : n != 1)
  statement: exists p : Nat+, p.Prime ∧ p ∣ n
  proof: by
  obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (mt coe_eq_one_iff.mp hn)
  exists (⟨p, Nat.Prime.pos hp.left⟩ : Nat+); rw [dvd_iff]; apply hp

中文:
定理 存在_prime_and_dvd
  条件: {n : 自然数+} (hn : n != 1)
  结论: 存在 p : 自然数+, p.素 ∧ p ∣ n
  证明: by
  obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (mt coe_eq_one_iff.mp hn)
  exists (⟨p, Nat.Prime.pos hp.left⟩ : Nat+); rw [dvd_iff]; apply hp

Depends on / 依赖: Nat.Prime.pos, Nat.exists_prime_and_dvd, coe_eq_one_iff, coe_eq_one_iff.mp, dvd_iff, exists_prime_and_dvd, hp.left
-/
theorem exists_prime_and_dvd {n : Nat+} (hn : n != 1) : exists p : Nat+, p.Prime ∧ p ∣ n := by
  obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (mt coe_eq_one_iff.mp hn)
  exists (⟨p, Nat.Prime.pos hp.left⟩ : Nat+); rw [dvd_iff]; apply hp

end Prime

section Coprime

/-! ### Coprime numbers and gcd -/


/--
Definition of `Coprime` / `Coprime` 的定义

English:
definition Coprime
  signature: (m n : Nat+)
  body: m.gcd n = 1

@[simp, norm_cast]

中文:
定义 Coprime
  签名: (m n : 自然数+)
  定义体: m.gcd n = 1

@[simp, norm_cast]

Depends on / 依赖: m.gcd
-/
def Coprime (m n : Nat+) : Prop :=
  m.gcd n = 1

@[simp, norm_cast]
/--
theorem `coprime_coe` / 定理 `coprime_coe`

English:
theorem coprime_coe
  given: {m n : Nat+}
  statement: Nat.Coprime ↑m ↑n ↔ m.Coprime n
  proof: by
  unfold Nat.Coprime Coprime
  rw [← coe_inj]
  simp

中文:
定理 coprime_coe
  条件: {m n : 自然数+}
  结论: 自然数.Coprime ↑m ↑n ↔ m.Coprime n
  证明: by
  unfold Nat.Coprime Coprime
  rw [← coe_inj]
  simp

Depends on / 依赖: Coprime, Nat.Coprime, coe_inj
-/
theorem coprime_coe {m n : Nat+} : Nat.Coprime ↑m ↑n ↔ m.Coprime n := by
  unfold Nat.Coprime Coprime
  rw [← coe_inj]
  simp

/--
theorem `Coprime.mul` / 定理 `Coprime.mul`

English:
theorem Coprime.mul
  given: {k m n : Nat+}
  statement: m.Coprime k -> n.Coprime k -> (m * n).Coprime k
  proof: by
  repeat rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul_left

中文:
定理 Coprime.mul
  条件: {k m n : 自然数+}
  结论: m.Coprime k -> n.Coprime k -> (m * n).Coprime k
  证明: by
  repeat rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul_left

Depends on / 依赖: Coprime, Nat.Coprime.mul_left, coprime_coe, mul_coe, mul_left, repeat
-/
theorem Coprime.mul {k m n : Nat+} : m.Coprime k -> n.Coprime k -> (m * n).Coprime k := by
  repeat rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul_left

/--
theorem `Coprime.mul_right` / 定理 `Coprime.mul_right`

English:
theorem Coprime.mul_right
  given: {k m n : Nat+}
  statement: k.Coprime m -> k.Coprime n -> k.Coprime (m * n)
  proof: by
  repeat rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul_right

中文:
定理 Coprime.mul_right
  条件: {k m n : 自然数+}
  结论: k.Coprime m -> k.Coprime n -> k.Coprime (m * n)
  证明: by
  repeat rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul_right

Depends on / 依赖: Coprime, Nat.Coprime.mul_right, coprime_coe, mul_coe, mul_right, repeat
-/
theorem Coprime.mul_right {k m n : Nat+} : k.Coprime m -> k.Coprime n -> k.Coprime (m * n) := by
  repeat rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul_right

/--
theorem `gcd_comm` / 定理 `gcd_comm`

English:
theorem gcd_comm
  given: {m n : Nat+}
  statement: m.gcd n = n.gcd m
  proof: by
  apply eq
  simp only [gcd_coe]
  apply Nat.gcd_comm

中文:
定理 gcd_comm
  条件: {m n : 自然数+}
  结论: m.最大公约数 n = n.最大公约数 m
  证明: by
  apply eq
  simp only [gcd_coe]
  apply Nat.gcd_comm

Depends on / 依赖: Nat.gcd_comm, gcd_coe, gcd_comm
-/
theorem gcd_comm {m n : Nat+} : m.gcd n = n.gcd m := by
  apply eq
  simp only [gcd_coe]
  apply Nat.gcd_comm

/--
theorem `gcd_eq_left_iff_dvd` / 定理 `gcd_eq_left_iff_dvd`

English:
theorem gcd_eq_left_iff_dvd
  given: {m n : Nat+}
  statement: m.gcd n = m ↔ m ∣ n
  proof: by
  rw [dvd_iff]; rw [← Nat.gcd_eq_left_iff_dvd]; rw [← coe_inj]
  simp

中文:
定理 gcd_eq_left_iff_dvd
  条件: {m n : 自然数+}
  结论: m.最大公约数 n = m ↔ m ∣ n
  证明: by
  rw [dvd_iff]; rw [← Nat.gcd_eq_left_iff_dvd]; rw [← coe_inj]
  simp

Depends on / 依赖: Nat.gcd_eq_left_iff_dvd, coe_inj, dvd_iff, gcd_eq_left_iff_dvd
-/
theorem gcd_eq_left_iff_dvd {m n : Nat+} : m.gcd n = m ↔ m ∣ n := by
  rw [dvd_iff]; rw [← Nat.gcd_eq_left_iff_dvd]; rw [← coe_inj]
  simp

/--
theorem `gcd_eq_right_iff_dvd` / 定理 `gcd_eq_right_iff_dvd`

English:
theorem gcd_eq_right_iff_dvd
  given: {m n : Nat+}
  statement: n.gcd m = m ↔ m ∣ n
  proof: by
  rw [gcd_comm]
  apply gcd_eq_left_iff_dvd

中文:
定理 gcd_eq_right_iff_dvd
  条件: {m n : 自然数+}
  结论: n.最大公约数 m = m ↔ m ∣ n
  证明: by
  rw [gcd_comm]
  apply gcd_eq_left_iff_dvd

Depends on / 依赖: gcd_comm, gcd_eq_left_iff_dvd
-/
theorem gcd_eq_right_iff_dvd {m n : Nat+} : n.gcd m = m ↔ m ∣ n := by
  rw [gcd_comm]
  apply gcd_eq_left_iff_dvd

/--
theorem `Coprime.gcd_mul_left_cancel` / 定理 `Coprime.gcd_mul_left_cancel`

English:
theorem Coprime.gcd_mul_left_cancel
  given: (m : Nat+) {n k : Nat+}
  proof: by
  intro h; apply eq; simp only [gcd_coe, mul_coe]
  apply Nat.Coprime.gcd_mul_left_cancel; simpa

中文:
定理 Coprime.gcd_mul_left_cancel
  条件: (m : 自然数+) {n k : 自然数+}
  证明: by
  intro h; apply eq; simp only [gcd_coe, mul_coe]
  apply Nat.Coprime.gcd_mul_left_cancel; simpa

Depends on / 依赖: Coprime, Nat.Coprime.gcd_mul_left_cancel, gcd_coe, gcd_mul_left_cancel, mul_coe
-/
theorem Coprime.gcd_mul_left_cancel (m : Nat+) {n k : Nat+} :
    k.Coprime n -> (k * m).gcd n = m.gcd n := by
  intro h; apply eq; simp only [gcd_coe, mul_coe]
  apply Nat.Coprime.gcd_mul_left_cancel; simpa

/--
theorem `Coprime.gcd_mul_right_cancel` / 定理 `Coprime.gcd_mul_right_cancel`

English:
theorem Coprime.gcd_mul_right_cancel
  given: (m : Nat+) {n k : Nat+}
  proof: by rw [mul_comm]; apply Coprime.gcd_mul_left_cancel

中文:
定理 Coprime.gcd_mul_right_cancel
  条件: (m : 自然数+) {n k : 自然数+}
  证明: by rw [mul_comm]; apply Coprime.gcd_mul_left_cancel

Depends on / 依赖: Coprime, Coprime.gcd_mul_left_cancel, gcd_mul_left_cancel, mul_comm
-/
theorem Coprime.gcd_mul_right_cancel (m : Nat+) {n k : Nat+} :
    k.Coprime n -> (m * k).gcd n = m.gcd n := by rw [mul_comm]; apply Coprime.gcd_mul_left_cancel

/--
theorem `Coprime.gcd_mul_left_cancel_right` / 定理 `Coprime.gcd_mul_left_cancel_right`

English:
theorem Coprime.gcd_mul_left_cancel_right
  given: (m : Nat+) {n k : Nat+}
  proof: by
  intro h; iterate 2 rw [gcd_comm]; symm
  apply Coprime.gcd_mul_left_cancel _ h

中文:
定理 Coprime.gcd_mul_left_cancel_right
  条件: (m : 自然数+) {n k : 自然数+}
  证明: by
  intro h; iterate 2 rw [gcd_comm]; symm
  apply Coprime.gcd_mul_left_cancel _ h

Depends on / 依赖: Coprime, Coprime.gcd_mul_left_cancel, gcd_comm, gcd_mul_left_cancel, iterate
-/
theorem Coprime.gcd_mul_left_cancel_right (m : Nat+) {n k : Nat+} :
    k.Coprime m -> m.gcd (k * n) = m.gcd n := by
  intro h; iterate 2 rw [gcd_comm]; symm
  apply Coprime.gcd_mul_left_cancel _ h

/--
theorem `Coprime.gcd_mul_right_cancel_right` / 定理 `Coprime.gcd_mul_right_cancel_right`

English:
theorem Coprime.gcd_mul_right_cancel_right
  given: (m : Nat+) {n k : Nat+}
  proof: by
  rw [mul_comm]
  apply Coprime.gcd_mul_left_cancel_right

@[simp]

中文:
定理 Coprime.gcd_mul_right_cancel_right
  条件: (m : 自然数+) {n k : 自然数+}
  证明: by
  rw [mul_comm]
  apply Coprime.gcd_mul_left_cancel_right

@[simp]

Depends on / 依赖: Coprime, Coprime.gcd_mul_left_cancel_right, gcd_mul_left_cancel_right, mul_comm
-/
theorem Coprime.gcd_mul_right_cancel_right (m : Nat+) {n k : Nat+} :
    k.Coprime m -> m.gcd (n * k) = m.gcd n := by
  rw [mul_comm]
  apply Coprime.gcd_mul_left_cancel_right

@[simp]
/--
theorem `one_gcd` / 定理 `one_gcd`

English:
theorem one_gcd
  given: {n : Nat+}
  statement: gcd 1 n = 1
  proof: by
  rw [gcd_eq_left_iff_dvd]
  apply one_dvd

@[simp]

中文:
定理 one_gcd
  条件: {n : 自然数+}
  结论: 最大公约数 1 n = 1
  证明: by
  rw [gcd_eq_left_iff_dvd]
  apply one_dvd

@[simp]

Depends on / 依赖: gcd_eq_left_iff_dvd, one_dvd
-/
theorem one_gcd {n : Nat+} : gcd 1 n = 1 := by
  rw [gcd_eq_left_iff_dvd]
  apply one_dvd

@[simp]
/--
theorem `gcd_one` / 定理 `gcd_one`

English:
theorem gcd_one
  given: {n : Nat+}
  statement: gcd n 1 = 1
  proof: by
  rw [gcd_comm]
  apply one_gcd

@[symm]

中文:
定理 gcd_one
  条件: {n : 自然数+}
  结论: 最大公约数 n 1 = 1
  证明: by
  rw [gcd_comm]
  apply one_gcd

@[symm]

Depends on / 依赖: gcd_comm, one_gcd
-/
theorem gcd_one {n : Nat+} : gcd n 1 = 1 := by
  rw [gcd_comm]
  apply one_gcd

@[symm]
/--
theorem `Coprime.symm` / 定理 `Coprime.symm`

English:
theorem Coprime.symm
  given: {m n : Nat+}
  statement: m.Coprime n -> n.Coprime m
  proof: by
  unfold Coprime
  rw [gcd_comm]
  simp

@[simp]

中文:
定理 Coprime.symm
  条件: {m n : 自然数+}
  结论: m.Coprime n -> n.Coprime m
  证明: by
  unfold Coprime
  rw [gcd_comm]
  simp

@[simp]

Depends on / 依赖: Coprime, gcd_comm
-/
theorem Coprime.symm {m n : Nat+} : m.Coprime n -> n.Coprime m := by
  unfold Coprime
  rw [gcd_comm]
  simp

@[simp]
/--
theorem `one_coprime` / 定理 `one_coprime`

English:
theorem one_coprime
  given: {n : Nat+}
  statement: (1 : Nat+).Coprime n
  proof: one_gcd

@[simp]

中文:
定理 one_coprime
  条件: {n : 自然数+}
  结论: (1 : 自然数+).Coprime n
  证明: one_gcd

@[simp]

Depends on / 依赖: one_gcd
-/
theorem one_coprime {n : Nat+} : (1 : Nat+).Coprime n :=
  one_gcd

@[simp]
/--
theorem `coprime_one` / 定理 `coprime_one`

English:
theorem coprime_one
  given: {n : Nat+}
  statement: n.Coprime 1
  proof: Coprime.symm one_coprime

中文:
定理 coprime_one
  条件: {n : 自然数+}
  结论: n.Coprime 1
  证明: Coprime.symm one_coprime

Depends on / 依赖: Coprime, Coprime.symm, one_coprime
-/
theorem coprime_one {n : Nat+} : n.Coprime 1 :=
  Coprime.symm one_coprime

/--
theorem `Coprime.coprime_dvd_left` / 定理 `Coprime.coprime_dvd_left`

English:
theorem Coprime.coprime_dvd_left
  given: {m k n : Nat+}
  statement: m ∣ k -> k.Coprime n -> m.Coprime n
  proof: by
  rw [dvd_iff]
  repeat rw [← coprime_coe]
  apply Nat.Coprime.coprime_dvd_left

中文:
定理 Coprime.coprime_dvd_left
  条件: {m k n : 自然数+}
  结论: m ∣ k -> k.Coprime n -> m.Coprime n
  证明: by
  rw [dvd_iff]
  repeat rw [← coprime_coe]
  apply Nat.Coprime.coprime_dvd_left

Depends on / 依赖: Coprime, Nat.Coprime.coprime_dvd_left, coprime_coe, coprime_dvd_left, dvd_iff, repeat
-/
theorem Coprime.coprime_dvd_left {m k n : Nat+} : m ∣ k -> k.Coprime n -> m.Coprime n := by
  rw [dvd_iff]
  repeat rw [← coprime_coe]
  apply Nat.Coprime.coprime_dvd_left

/--
theorem `Coprime.factor_eq_gcd_left` / 定理 `Coprime.factor_eq_gcd_left`

English:
theorem Coprime.factor_eq_gcd_left
  given: {a b m n : Nat+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n)
  proof: by
  rw [← gcd_eq_left_iff_dvd] at am
  conv_lhs => rw [← am]
  rw [eq_comm]
  apply Coprime.gcd_mul_right_cancel a
  apply Coprime.coprime_dvd_left bn cop.symm

中文:
定理 Coprime.factor_eq_gcd_left
  条件: {a b m n : 自然数+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n)
  证明: by
  rw [← gcd_eq_left_iff_dvd] at am
  conv_lhs => rw [← am]
  rw [eq_comm]
  apply Coprime.gcd_mul_right_cancel a
  apply Coprime.coprime_dvd_left bn cop.symm

Depends on / 依赖: Coprime, Coprime.coprime_dvd_left, Coprime.gcd_mul_right_cancel, conv_lhs, cop.symm, coprime_dvd_left, eq_comm, gcd_eq_left_iff_dvd, gcd_mul_right_cancel
-/
theorem Coprime.factor_eq_gcd_left {a b m n : Nat+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n) :
    a = (a * b).gcd m := by
  rw [← gcd_eq_left_iff_dvd] at am
  conv_lhs => rw [← am]
  rw [eq_comm]
  apply Coprime.gcd_mul_right_cancel a
  apply Coprime.coprime_dvd_left bn cop.symm

/--
theorem `Coprime.factor_eq_gcd_right` / 定理 `Coprime.factor_eq_gcd_right`

English:
theorem Coprime.factor_eq_gcd_right
  given: {a b m n : Nat+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n)
  proof: by rw [mul_comm]; apply Coprime.factor_eq_gcd_left cop am bn

中文:
定理 Coprime.factor_eq_gcd_right
  条件: {a b m n : 自然数+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n)
  证明: by rw [mul_comm]; apply Coprime.factor_eq_gcd_left cop am bn

Depends on / 依赖: Coprime, Coprime.factor_eq_gcd_left, factor_eq_gcd_left, mul_comm
-/
theorem Coprime.factor_eq_gcd_right {a b m n : Nat+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n) :
    a = (b * a).gcd m := by rw [mul_comm]; apply Coprime.factor_eq_gcd_left cop am bn

/--
theorem `Coprime.factor_eq_gcd_left_right` / 定理 `Coprime.factor_eq_gcd_left_right`

English:
theorem Coprime.factor_eq_gcd_left_right
  statement: {a b m n : Nat+} (cop : m.Coprime n) (am : a ∣ m)
  proof: by rw [gcd_comm]; apply Coprime.factor_eq_gcd_left cop am bn

中文:
定理 Coprime.factor_eq_gcd_left_right
  结论: {a b m n : 自然数+} (cop : m.Coprime n) (am : a ∣ m)
  证明: by rw [gcd_comm]; apply Coprime.factor_eq_gcd_left cop am bn

Depends on / 依赖: Coprime, Coprime.factor_eq_gcd_left, factor_eq_gcd_left, gcd_comm
-/
theorem Coprime.factor_eq_gcd_left_right {a b m n : Nat+} (cop : m.Coprime n) (am : a ∣ m)
    (bn : b ∣ n) : a = m.gcd (a * b) := by rw [gcd_comm]; apply Coprime.factor_eq_gcd_left cop am bn

/--
theorem `Coprime.factor_eq_gcd_right_right` / 定理 `Coprime.factor_eq_gcd_right_right`

English:
theorem Coprime.factor_eq_gcd_right_right
  statement: {a b m n : Nat+} (cop : m.Coprime n) (am : a ∣ m)
  proof: by
  rw [gcd_comm]
  apply Coprime.factor_eq_gcd_right cop am bn

中文:
定理 Coprime.factor_eq_gcd_right_right
  结论: {a b m n : 自然数+} (cop : m.Coprime n) (am : a ∣ m)
  证明: by
  rw [gcd_comm]
  apply Coprime.factor_eq_gcd_right cop am bn

Depends on / 依赖: Coprime, Coprime.factor_eq_gcd_right, factor_eq_gcd_right, gcd_comm
-/
theorem Coprime.factor_eq_gcd_right_right {a b m n : Nat+} (cop : m.Coprime n) (am : a ∣ m)
    (bn : b ∣ n) : a = m.gcd (b * a) := by
  rw [gcd_comm]
  apply Coprime.factor_eq_gcd_right cop am bn

/--
theorem `Coprime.gcd_mul` / 定理 `Coprime.gcd_mul`

English:
theorem Coprime.gcd_mul
  given: (k : Nat+) {m n : Nat+} (h : m.Coprime n)
  proof: by
  rw [← coprime_coe] at h; apply eq
  simp only [gcd_coe, mul_coe]; apply Nat.Coprime.gcd_mul k h

中文:
定理 Coprime.gcd_mul
  条件: (k : 自然数+) {m n : 自然数+} (h : m.Coprime n)
  证明: by
  rw [← coprime_coe] at h; apply eq
  simp only [gcd_coe, mul_coe]; apply Nat.Coprime.gcd_mul k h

Depends on / 依赖: Coprime, Nat.Coprime.gcd_mul, coprime_coe, gcd_coe, gcd_mul, mul_coe
-/
theorem Coprime.gcd_mul (k : Nat+) {m n : Nat+} (h : m.Coprime n) :
    k.gcd (m * n) = k.gcd m * k.gcd n := by
  rw [← coprime_coe] at h; apply eq
  simp only [gcd_coe, mul_coe]; apply Nat.Coprime.gcd_mul k h

/--
theorem `Coprime.pow` / 定理 `Coprime.pow`

English:
theorem Coprime.pow
  given: {m n : Nat+} (k l : Nat) (h : m.Coprime n)
  statement: (m ^ k : Nat).Coprime (n ^ l)
  proof: by
  rw [← coprime_coe] at *; apply Nat.Coprime.pow; apply h

中文:
定理 Coprime.pow
  条件: {m n : 自然数+} (k l : 自然数) (h : m.Coprime n)
  结论: (m ^ k : 自然数).Coprime (n ^ l)
  证明: by
  rw [← coprime_coe] at *; apply Nat.Coprime.pow; apply h

Depends on / 依赖: Coprime, Nat.Coprime.pow, coprime_coe
-/
theorem Coprime.pow {m n : Nat+} (k l : Nat) (h : m.Coprime n) : (m ^ k : Nat).Coprime (n ^ l) := by
  rw [← coprime_coe] at *; apply Nat.Coprime.pow; apply h

end Coprime

end PNat
