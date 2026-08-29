/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality of continuum

In this file we define `Cardinal.continuum` (notation: `𝔠`, localized in `Cardinal`) to be `2 ^ ℵ₀`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `Cardinal.continuum` in scope `Cardinal`.
-/

@[expose] public section


namespace Cardinal

universe u v

open Cardinal

/--
Definition of `continuum` / `continuum` 的定义

English:
definition continuum
  signature: : Cardinal.{u}
  body: 2 ^ ℵ₀

@[inherit_doc] scoped notation "𝔠" => Cardinal.continuum

@[simp]

中文:
定义 continuum
  签名: : Cardinal.{u}
  定义体: 2 ^ ℵ₀

@[inherit_doc] scoped notation "𝔠" => Cardinal.continuum

@[simp]
-/
def continuum : Cardinal.{u} :=
  2 ^ ℵ₀

@[inherit_doc] scoped notation "𝔠" => Cardinal.continuum

@[simp]
/--
theorem `two_power_aleph0` / 定理 `two_power_aleph0`

English:
theorem two_power_aleph0
  statement: 2 ^ ℵ₀ = 𝔠
  proof: rfl

@[simp]

中文:
定理 two_power_aleph0
  结论: 2 ^ ℵ₀ = 𝔠
  证明: rfl

@[simp]
-/
theorem two_power_aleph0 : 2 ^ ℵ₀ = 𝔠 :=
  rfl

@[simp]
/--
theorem `lift_continuum` / 定理 `lift_continuum`

English:
theorem lift_continuum
  statement: lift.{v} 𝔠 = 𝔠
  proof: by
  rw [← two_power_aleph0]; rw [lift_two_power]; rw [lift_aleph0]; rw [two_power_aleph0]

@[simp]

中文:
定理 lift_continuum
  结论: lift.{v} 𝔠 = 𝔠
  证明: by
  rw [← two_power_aleph0]; rw [lift_two_power]; rw [lift_aleph0]; rw [two_power_aleph0]

@[simp]

Depends on / 依赖: lift_aleph0, lift_two_power, two_power_aleph0
-/
theorem lift_continuum : lift.{v} 𝔠 = 𝔠 := by
  rw [← two_power_aleph0]; rw [lift_two_power]; rw [lift_aleph0]; rw [two_power_aleph0]

@[simp]
/--
theorem `continuum_le_lift` / 定理 `continuum_le_lift`

English:
theorem continuum_le_lift
  given: {c : Cardinal.{u}}
  statement: 𝔠 <= lift.{v} c ↔ 𝔠 <= c
  proof: by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_le]

@[simp]

中文:
定理 continuum_le_lift
  条件: {c : Cardinal.{u}}
  结论: 𝔠 <= lift.{v} c ↔ 𝔠 <= c
  证明: by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_le]

@[simp]

Depends on / 依赖: lift_continuum, lift_le
-/
theorem continuum_le_lift {c : Cardinal.{u}} : 𝔠 <= lift.{v} c ↔ 𝔠 <= c := by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_le]

@[simp]
/--
theorem `lift_le_continuum` / 定理 `lift_le_continuum`

English:
theorem lift_le_continuum
  given: {c : Cardinal.{u}}
  statement: lift.{v} c <= 𝔠 ↔ c <= 𝔠
  proof: by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_le]

@[simp]

中文:
定理 lift_le_continuum
  条件: {c : Cardinal.{u}}
  结论: lift.{v} c <= 𝔠 ↔ c <= 𝔠
  证明: by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_le]

@[simp]

Depends on / 依赖: lift_continuum, lift_le
-/
theorem lift_le_continuum {c : Cardinal.{u}} : lift.{v} c <= 𝔠 ↔ c <= 𝔠 := by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_le]

@[simp]
/--
theorem `continuum_lt_lift` / 定理 `continuum_lt_lift`

English:
theorem continuum_lt_lift
  given: {c : Cardinal.{u}}
  statement: 𝔠 < lift.{v} c ↔ 𝔠 < c
  proof: by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_lt]

@[simp]

中文:
定理 continuum_lt_lift
  条件: {c : Cardinal.{u}}
  结论: 𝔠 < lift.{v} c ↔ 𝔠 < c
  证明: by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_lt]

@[simp]

Depends on / 依赖: lift_continuum, lift_lt
-/
theorem continuum_lt_lift {c : Cardinal.{u}} : 𝔠 < lift.{v} c ↔ 𝔠 < c := by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_lt]

@[simp]
/--
theorem `lift_lt_continuum` / 定理 `lift_lt_continuum`

English:
theorem lift_lt_continuum
  given: {c : Cardinal.{u}}
  statement: lift.{v} c < 𝔠 ↔ c < 𝔠
  proof: by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_lt]

中文:
定理 lift_lt_continuum
  条件: {c : Cardinal.{u}}
  结论: lift.{v} c < 𝔠 ↔ c < 𝔠
  证明: by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_lt]

Depends on / 依赖: lift_continuum, lift_lt
-/
theorem lift_lt_continuum {c : Cardinal.{u}} : lift.{v} c < 𝔠 ↔ c < 𝔠 := by
  rw [← lift_continuum.{v]; rw [u}]; rw [lift_lt]



/--
theorem `aleph0_lt_continuum` / 定理 `aleph0_lt_continuum`

English:
theorem aleph0_lt_continuum
  statement: ℵ₀ < 𝔠
  proof: cantor ℵ₀

中文:
定理 aleph0_lt_continuum
  结论: ℵ₀ < 𝔠
  证明: cantor ℵ₀

Depends on / 依赖: cantor
-/
theorem aleph0_lt_continuum : ℵ₀ < 𝔠 :=
  cantor ℵ₀

/--
theorem `aleph0_le_continuum` / 定理 `aleph0_le_continuum`

English:
theorem aleph0_le_continuum
  statement: ℵ₀ <= 𝔠
  proof: aleph0_lt_continuum.le

@[simp]

中文:
定理 aleph0_le_continuum
  结论: ℵ₀ <= 𝔠
  证明: aleph0_lt_continuum.le

@[simp]

Depends on / 依赖: aleph0_lt_continuum, aleph0_lt_continuum.le
-/
theorem aleph0_le_continuum : ℵ₀ <= 𝔠 :=
  aleph0_lt_continuum.le

@[simp]
/--
theorem `beth_one` / 定理 `beth_one`

English:
theorem beth_one
  statement: ℶ_ 1 = 𝔠
  proof: by simpa using beth_succ 0

中文:
定理 beth_one
  结论: ℶ_ 1 = 𝔠
  证明: by simpa using beth_succ 0

Depends on / 依赖: beth_succ
-/
theorem beth_one : ℶ_ 1 = 𝔠 := by simpa using beth_succ 0

/--
theorem `nat_lt_continuum` / 定理 `nat_lt_continuum`

English:
theorem nat_lt_continuum
  given: (n : Nat)
  statement: ↑n < 𝔠
  proof: natCast_lt_aleph0.trans aleph0_lt_continuum

中文:
定理 nat_lt_continuum
  条件: (n : 自然数)
  结论: ↑n < 𝔠
  证明: natCast_lt_aleph0.trans aleph0_lt_continuum

Depends on / 依赖: aleph0_lt_continuum, natCast_lt_aleph0, natCast_lt_aleph0.trans
-/
theorem nat_lt_continuum (n : Nat) : ↑n < 𝔠 :=
  natCast_lt_aleph0.trans aleph0_lt_continuum

/--
theorem `mk_set_nat` / 定理 `mk_set_nat`

English:
theorem mk_set_nat
  statement: #(Set Nat) = 𝔠
  proof: by simp

中文:
定理 mk_set_nat
  结论: #(Set 自然数) = 𝔠
  证明: by simp
-/
theorem mk_set_nat : #(Set Nat) = 𝔠 := by simp

/--
theorem `continuum_pos` / 定理 `continuum_pos`

English:
theorem continuum_pos
  statement: 0 < 𝔠
  proof: nat_lt_continuum 0

中文:
定理 continuum_pos
  结论: 0 < 𝔠
  证明: nat_lt_continuum 0

Depends on / 依赖: nat_lt_continuum
-/
theorem continuum_pos : 0 < 𝔠 :=
  nat_lt_continuum 0

/--
theorem `continuum_ne_zero` / 定理 `continuum_ne_zero`

English:
theorem continuum_ne_zero
  statement: 𝔠 != 0
  proof: continuum_pos.ne'

中文:
定理 continuum_ne_zero
  结论: 𝔠 != 0
  证明: continuum_pos.ne'

Depends on / 依赖: continuum_pos, continuum_pos.ne
-/
theorem continuum_ne_zero : 𝔠 != 0 :=
  continuum_pos.ne'

/--
theorem `aleph_one_le_continuum` / 定理 `aleph_one_le_continuum`

English:
theorem aleph_one_le_continuum
  statement: ℵ₁ <= 𝔠
  proof: by
  rw [← succ_aleph0]
  exact Order.succ_le_of_lt aleph0_lt_continuum

@[simp]

中文:
定理 aleph_one_le_continuum
  结论: ℵ₁ <= 𝔠
  证明: by
  rw [← succ_aleph0]
  exact Order.succ_le_of_lt aleph0_lt_continuum

@[simp]

Depends on / 依赖: Order.succ_le_of_lt, aleph0_lt_continuum, succ_aleph0, succ_le_of_lt
-/
theorem aleph_one_le_continuum : ℵ₁ <= 𝔠 := by
  rw [← succ_aleph0]
  exact Order.succ_le_of_lt aleph0_lt_continuum

@[simp]
/--
theorem `continuum_toNat` / 定理 `continuum_toNat`

English:
theorem continuum_toNat
  statement: toNat continuum = 0
  proof: toNat_apply_of_aleph0_le aleph0_le_continuum

@[simp]

中文:
定理 continuum_toNat
  结论: to自然数 continuum = 0
  证明: toNat_apply_of_aleph0_le aleph0_le_continuum

@[simp]

Depends on / 依赖: aleph0_le_continuum, toNat_apply_of_aleph0_le
-/
theorem continuum_toNat : toNat continuum = 0 :=
  toNat_apply_of_aleph0_le aleph0_le_continuum

@[simp]
/--
theorem `continuum_toENat` / 定理 `continuum_toENat`

English:
theorem continuum_toENat
  statement: toENat continuum = ⊤
  proof: (toENat_eq_top.2 aleph0_le_continuum)

中文:
定理 continuum_toENat
  结论: toE自然数 continuum = ⊤
  证明: (toENat_eq_top.2 aleph0_le_continuum)

Depends on / 依赖: aleph0_le_continuum, toENat_eq_top
-/
theorem continuum_toENat : toENat continuum = ⊤ :=
  (toENat_eq_top.2 aleph0_le_continuum)

/-!
### Addition
-/


@[simp]
/--
theorem `aleph0_add_continuum` / 定理 `aleph0_add_continuum`

English:
theorem aleph0_add_continuum
  statement: ℵ₀ + 𝔠 = 𝔠
  proof: add_eq_right aleph0_le_continuum aleph0_le_continuum

@[simp]

中文:
定理 aleph0_add_continuum
  结论: ℵ₀ + 𝔠 = 𝔠
  证明: add_eq_right aleph0_le_continuum aleph0_le_continuum

@[simp]

Depends on / 依赖: add_eq_right, aleph0_le_continuum
-/
theorem aleph0_add_continuum : ℵ₀ + 𝔠 = 𝔠 :=
  add_eq_right aleph0_le_continuum aleph0_le_continuum

@[simp]
/--
theorem `continuum_add_aleph0` / 定理 `continuum_add_aleph0`

English:
theorem continuum_add_aleph0
  statement: 𝔠 + ℵ₀ = 𝔠
  proof: (add_comm _ _).trans aleph0_add_continuum

@[simp]

中文:
定理 continuum_add_aleph0
  结论: 𝔠 + ℵ₀ = 𝔠
  证明: (add_comm _ _).trans aleph0_add_continuum

@[simp]

Depends on / 依赖: add_comm, aleph0_add_continuum
-/
theorem continuum_add_aleph0 : 𝔠 + ℵ₀ = 𝔠 :=
  (add_comm _ _).trans aleph0_add_continuum

@[simp]
/--
theorem `continuum_add_self` / 定理 `continuum_add_self`

English:
theorem continuum_add_self
  statement: 𝔠 + 𝔠 = 𝔠
  proof: add_eq_self aleph0_le_continuum

@[simp]

中文:
定理 continuum_add_self
  结论: 𝔠 + 𝔠 = 𝔠
  证明: add_eq_self aleph0_le_continuum

@[simp]

Depends on / 依赖: add_eq_self, aleph0_le_continuum
-/
theorem continuum_add_self : 𝔠 + 𝔠 = 𝔠 :=
  add_eq_self aleph0_le_continuum

@[simp]
/--
theorem `nat_add_continuum` / 定理 `nat_add_continuum`

English:
theorem nat_add_continuum
  given: (n : Nat)
  statement: ↑n + 𝔠 = 𝔠
  proof: nat_add_eq n aleph0_le_continuum

@[simp]

中文:
定理 nat_add_continuum
  条件: (n : 自然数)
  结论: ↑n + 𝔠 = 𝔠
  证明: nat_add_eq n aleph0_le_continuum

@[simp]

Depends on / 依赖: aleph0_le_continuum, nat_add_eq
-/
theorem nat_add_continuum (n : Nat) : ↑n + 𝔠 = 𝔠 :=
  nat_add_eq n aleph0_le_continuum

@[simp]
/--
theorem `continuum_add_nat` / 定理 `continuum_add_nat`

English:
theorem continuum_add_nat
  given: (n : Nat)
  statement: 𝔠 + n = 𝔠
  proof: (add_comm _ _).trans (nat_add_continuum n)

@[simp]

中文:
定理 continuum_add_nat
  条件: (n : 自然数)
  结论: 𝔠 + n = 𝔠
  证明: (add_comm _ _).trans (nat_add_continuum n)

@[simp]

Depends on / 依赖: add_comm, nat_add_continuum
-/
theorem continuum_add_nat (n : Nat) : 𝔠 + n = 𝔠 :=
  (add_comm _ _).trans (nat_add_continuum n)

@[simp]
/--
theorem `ofNat_add_continuum` / 定理 `ofNat_add_continuum`

English:
theorem ofNat_add_continuum
  given: {n : Nat} [Nat.AtLeastTwo n]
  statement: ofNat(n) + 𝔠 = 𝔠
  proof: nat_add_continuum n

@[simp]

中文:
定理 ofNat_add_continuum
  条件: {n : 自然数} [自然数.AtLeastTwo n]
  结论: of自然数(n) + 𝔠 = 𝔠
  证明: nat_add_continuum n

@[simp]

Depends on / 依赖: nat_add_continuum
-/
theorem ofNat_add_continuum {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) + 𝔠 = 𝔠 :=
  nat_add_continuum n

@[simp]
/--
theorem `continuum_add_ofNat` / 定理 `continuum_add_ofNat`

English:
theorem continuum_add_ofNat
  given: {n : Nat} [Nat.AtLeastTwo n]
  statement: 𝔠 + ofNat(n) = 𝔠
  proof: continuum_add_nat n

中文:
定理 continuum_add_ofNat
  条件: {n : 自然数} [自然数.AtLeastTwo n]
  结论: 𝔠 + of自然数(n) = 𝔠
  证明: continuum_add_nat n

Depends on / 依赖: continuum_add_nat
-/
theorem continuum_add_ofNat {n : Nat} [Nat.AtLeastTwo n] : 𝔠 + ofNat(n) = 𝔠 :=
  continuum_add_nat n

/-!
### Multiplication
-/


@[simp]
/--
theorem `continuum_mul_self` / 定理 `continuum_mul_self`

English:
theorem continuum_mul_self
  statement: 𝔠 * 𝔠 = 𝔠
  proof: mul_eq_left aleph0_le_continuum le_rfl continuum_ne_zero

@[simp]

中文:
定理 continuum_mul_self
  结论: 𝔠 * 𝔠 = 𝔠
  证明: mul_eq_left aleph0_le_continuum le_rfl continuum_ne_zero

@[simp]

Depends on / 依赖: aleph0_le_continuum, continuum_ne_zero, le_rfl, mul_eq_left
-/
theorem continuum_mul_self : 𝔠 * 𝔠 = 𝔠 :=
  mul_eq_left aleph0_le_continuum le_rfl continuum_ne_zero

@[simp]
/--
theorem `continuum_mul_aleph0` / 定理 `continuum_mul_aleph0`

English:
theorem continuum_mul_aleph0
  statement: 𝔠 * ℵ₀ = 𝔠
  proof: mul_eq_left aleph0_le_continuum aleph0_le_continuum aleph0_ne_zero

@[simp]

中文:
定理 continuum_mul_aleph0
  结论: 𝔠 * ℵ₀ = 𝔠
  证明: mul_eq_left aleph0_le_continuum aleph0_le_continuum aleph0_ne_zero

@[simp]

Depends on / 依赖: aleph0_le_continuum, aleph0_ne_zero, mul_eq_left
-/
theorem continuum_mul_aleph0 : 𝔠 * ℵ₀ = 𝔠 :=
  mul_eq_left aleph0_le_continuum aleph0_le_continuum aleph0_ne_zero

@[simp]
/--
theorem `aleph0_mul_continuum` / 定理 `aleph0_mul_continuum`

English:
theorem aleph0_mul_continuum
  statement: ℵ₀ * 𝔠 = 𝔠
  proof: (mul_comm _ _).trans continuum_mul_aleph0

@[simp]

中文:
定理 aleph0_mul_continuum
  结论: ℵ₀ * 𝔠 = 𝔠
  证明: (mul_comm _ _).trans continuum_mul_aleph0

@[simp]

Depends on / 依赖: continuum_mul_aleph0, mul_comm
-/
theorem aleph0_mul_continuum : ℵ₀ * 𝔠 = 𝔠 :=
  (mul_comm _ _).trans continuum_mul_aleph0

@[simp]
/--
theorem `nat_mul_continuum` / 定理 `nat_mul_continuum`

English:
theorem nat_mul_continuum
  given: {n : Nat} (hn : n != 0)
  statement: ↑n * 𝔠 = 𝔠
  proof: mul_eq_right aleph0_le_continuum (nat_lt_continuum n).le (Nat.cast_ne_zero.2 hn)

@[simp]

中文:
定理 nat_mul_continuum
  条件: {n : 自然数} (hn : n != 0)
  结论: ↑n * 𝔠 = 𝔠
  证明: mul_eq_right aleph0_le_continuum (nat_lt_continuum n).le (Nat.cast_ne_zero.2 hn)

@[simp]

Depends on / 依赖: Nat.cast_ne_zero, aleph0_le_continuum, cast_ne_zero, mul_eq_right, nat_lt_continuum
-/
theorem nat_mul_continuum {n : Nat} (hn : n != 0) : ↑n * 𝔠 = 𝔠 :=
  mul_eq_right aleph0_le_continuum (nat_lt_continuum n).le (Nat.cast_ne_zero.2 hn)

@[simp]
/--
theorem `continuum_mul_nat` / 定理 `continuum_mul_nat`

English:
theorem continuum_mul_nat
  given: {n : Nat} (hn : n != 0)
  statement: 𝔠 * n = 𝔠
  proof: (mul_comm _ _).trans (nat_mul_continuum hn)

@[simp]

中文:
定理 continuum_mul_nat
  条件: {n : 自然数} (hn : n != 0)
  结论: 𝔠 * n = 𝔠
  证明: (mul_comm _ _).trans (nat_mul_continuum hn)

@[simp]

Depends on / 依赖: mul_comm, nat_mul_continuum
-/
theorem continuum_mul_nat {n : Nat} (hn : n != 0) : 𝔠 * n = 𝔠 :=
  (mul_comm _ _).trans (nat_mul_continuum hn)

@[simp]
/--
theorem `ofNat_mul_continuum` / 定理 `ofNat_mul_continuum`

English:
theorem ofNat_mul_continuum
  given: {n : Nat} [Nat.AtLeastTwo n]
  statement: ofNat(n) * 𝔠 = 𝔠
  proof: nat_mul_continuum (OfNat.ofNat_ne_zero n)

@[simp]

中文:
定理 ofNat_mul_continuum
  条件: {n : 自然数} [自然数.AtLeastTwo n]
  结论: of自然数(n) * 𝔠 = 𝔠
  证明: nat_mul_continuum (OfNat.ofNat_ne_zero n)

@[simp]

Depends on / 依赖: OfNat.ofNat_ne_zero, nat_mul_continuum, ofNat_ne_zero
-/
theorem ofNat_mul_continuum {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) * 𝔠 = 𝔠 :=
  nat_mul_continuum (OfNat.ofNat_ne_zero n)

@[simp]
/--
theorem `continuum_mul_ofNat` / 定理 `continuum_mul_ofNat`

English:
theorem continuum_mul_ofNat
  given: {n : Nat} [Nat.AtLeastTwo n]
  statement: 𝔠 * ofNat(n) = 𝔠
  proof: continuum_mul_nat (OfNat.ofNat_ne_zero n)

中文:
定理 continuum_mul_ofNat
  条件: {n : 自然数} [自然数.AtLeastTwo n]
  结论: 𝔠 * of自然数(n) = 𝔠
  证明: continuum_mul_nat (OfNat.ofNat_ne_zero n)

Depends on / 依赖: OfNat.ofNat_ne_zero, continuum_mul_nat, ofNat_ne_zero
-/
theorem continuum_mul_ofNat {n : Nat} [Nat.AtLeastTwo n] : 𝔠 * ofNat(n) = 𝔠 :=
  continuum_mul_nat (OfNat.ofNat_ne_zero n)

/-!
### Power
-/


@[simp]
/--
theorem `aleph0_power_aleph0` / 定理 `aleph0_power_aleph0`

English:
theorem aleph0_power_aleph0
  statement: ℵ₀ ^ ℵ₀ = 𝔠
  proof: power_self_eq le_rfl

@[simp]

中文:
定理 aleph0_power_aleph0
  结论: ℵ₀ ^ ℵ₀ = 𝔠
  证明: power_self_eq le_rfl

@[simp]

Depends on / 依赖: le_rfl, power_self_eq
-/
theorem aleph0_power_aleph0 : ℵ₀ ^ ℵ₀ = 𝔠 :=
  power_self_eq le_rfl

@[simp]
/--
theorem `nat_power_aleph0` / 定理 `nat_power_aleph0`

English:
theorem nat_power_aleph0
  given: {n : Nat} (hn : 2 <= n)
  statement: n ^ ℵ₀ = 𝔠
  proof: nat_power_eq le_rfl hn

@[simp]

中文:
定理 nat_power_aleph0
  条件: {n : 自然数} (hn : 2 <= n)
  结论: n ^ ℵ₀ = 𝔠
  证明: nat_power_eq le_rfl hn

@[simp]

Depends on / 依赖: le_rfl, nat_power_eq
-/
theorem nat_power_aleph0 {n : Nat} (hn : 2 <= n) : n ^ ℵ₀ = 𝔠 :=
  nat_power_eq le_rfl hn

@[simp]
/--
theorem `continuum_power_aleph0` / 定理 `continuum_power_aleph0`

English:
theorem continuum_power_aleph0
  statement: 𝔠 ^ ℵ₀ = 𝔠
  proof: by
  rw [← two_power_aleph0]; rw [← power_mul]; rw [mul_eq_left le_rfl le_rfl aleph0_ne_zero]

中文:
定理 continuum_power_aleph0
  结论: 𝔠 ^ ℵ₀ = 𝔠
  证明: by
  rw [← two_power_aleph0]; rw [← power_mul]; rw [mul_eq_left le_rfl le_rfl aleph0_ne_zero]

Depends on / 依赖: aleph0_ne_zero, le_rfl, mul_eq_left, power_mul, two_power_aleph0
-/
theorem continuum_power_aleph0 : 𝔠 ^ ℵ₀ = 𝔠 := by
  rw [← two_power_aleph0]; rw [← power_mul]; rw [mul_eq_left le_rfl le_rfl aleph0_ne_zero]

/--
theorem `power_aleph0_of_le_continuum` / 定理 `power_aleph0_of_le_continuum`

English:
theorem power_aleph0_of_le_continuum
  given: {x : Cardinal} (h₁ : 2 <= x) (h₂ : x <= 𝔠)
  statement: x ^ ℵ₀ = 𝔠
  proof: by
  apply le_antisymm
  · rw [← continuum_power_aleph0]
    exact power_le_power_right h₂
  · rw [← two_power_aleph0]
    exact power_le_power_right h₁

中文:
定理 power_aleph0_of_le_continuum
  条件: {x : Cardinal} (h₁ : 2 <= x) (h₂ : x <= 𝔠)
  结论: x ^ ℵ₀ = 𝔠
  证明: by
  apply le_antisymm
  · rw [← continuum_power_aleph0]
    exact power_le_power_right h₂
  · rw [← two_power_aleph0]
    exact power_le_power_right h₁

Depends on / 依赖: continuum_power_aleph0, le_antisymm, power_le_power_right, two_power_aleph0
-/
theorem power_aleph0_of_le_continuum {x : Cardinal} (h₁ : 2 <= x) (h₂ : x <= 𝔠) : x ^ ℵ₀ = 𝔠 := by
  apply le_antisymm
  · rw [← continuum_power_aleph0]
    exact power_le_power_right h₂
  · rw [← two_power_aleph0]
    exact power_le_power_right h₁

end Cardinal
