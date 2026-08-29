/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Data.ZMod.Basic

/-!
# The power operator on `ℤˣ` by `ZMod 2`, `ℕ`, and `ℤ`

See also the related `negOnePow`.

## TODO

* Generalize this to `Pow G (Zmod n)` where `orderOf g = n`.

## Implementation notes

In future, we could consider a `LawfulPower M R` typeclass; but we can save ourselves a lot of work
by using `Module R (Additive M)` in its place, especially since this already has instances for
`R = ℕ` and `R = ℤ`.
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (ZMod 2) (Additive Intˣ)
  body: .ofMul au.toMul ^ z.val

中文:
实例 :
  签名: 标量乘法 (ZMod 2) (加性 整数ˣ)
  定义体: .ofMul au.toMul ^ z.val

Depends on / 依赖: au.toMul, z.val
-/
instance : SMul (ZMod 2) (Additive Intˣ) where
smul z au := .ofMul au.toMul ^ z.val

/--
lemma `ZMod.smul_units_def` / 引理 `ZMod.smul_units_def`

English:
lemma ZMod.smul_units_def
  given: (z : ZMod 2) (au : Additive Intˣ)
  proof: rfl

中文:
引理 ZMod.smul_units_def
  条件: (z : ZMod 2) (au : 加性 整数ˣ)
  证明: rfl
-/
lemma ZMod.smul_units_def (z : ZMod 2) (au : Additive Intˣ) :
    z • au = z.val • au := rfl

/--
lemma `ZMod.natCast_smul_units` / 引理 `ZMod.natCast_smul_units`

English:
lemma ZMod.natCast_smul_units
  given: (n : Nat) (au : Additive Intˣ)
  statement: (n : ZMod 2) • au = n • au
  proof: (Int.units_pow_eq_pow_mod_two au n).symm

中文:
引理 ZMod.natCast_smul_units
  条件: (n : 自然数) (au : 加性 整数ˣ)
  结论: (n : ZMod 2) • au = n • au
  证明: (Int.units_pow_eq_pow_mod_two au n).symm

Depends on / 依赖: Int.units_pow_eq_pow_mod_two, units_pow_eq_pow_mod_two
-/
lemma ZMod.natCast_smul_units (n : Nat) (au : Additive Intˣ) : (n : ZMod 2) • au = n • au :=
  (Int.units_pow_eq_pow_mod_two au n).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module (ZMod 2) (Additive Intˣ)
  body: .ofMul au.toMul ^ z.val
one_smul _ := Additive.toMul.injective pow_one _
mul_smul z₁ z₂ au := Additive.toMul.injective by
    dsimp only [ZMod.smul_units_def, toMul_nsmul]
    rw [← pow_mul]; rw [ZMod.val_mul]; rw [← Int.units_pow_eq_pow_mod_two]; rw [mul_comm]
smul_zero _ := Additive.toMul.injectiv

中文:
实例 :
  签名: 模 (ZMod 2) (加性 整数ˣ)
  定义体: .ofMul au.toMul ^ z.val
one_smul _ := Additive.toMul.injective pow_one _
mul_smul z₁ z₂ au := Additive.toMul.injective by
    dsimp only [ZMod.smul_units_def, toMul_nsmul]
    rw [← pow_mul]; rw [ZMod.val_mul]; rw [← Int.units_pow_eq_pow_mod_two]; rw [mul_comm]
smul_zero _ := Additive.toMul.injectiv

Depends on / 依赖: au.toMul, z.val
-/
instance : Module (ZMod 2) (Additive Intˣ) where
smul z au := .ofMul au.toMul ^ z.val
one_smul _ := Additive.toMul.injective pow_one _
mul_smul z₁ z₂ au := Additive.toMul.injective by
    dsimp only [ZMod.smul_units_def, toMul_nsmul]
    rw [← pow_mul]; rw [ZMod.val_mul]; rw [← Int.units_pow_eq_pow_mod_two]; rw [mul_comm]
smul_zero _ := Additive.toMul.injective one_pow _
smul_add _ _ _ := Additive.toMul.injective mul_pow _ _ _
add_smul z₁ z₂ au := Additive.toMul.injective by
    dsimp only [ZMod.smul_units_def, toMul_nsmul, toMul_add]
    rw [← pow_add]; rw [ZMod.val_add]; rw [← Int.units_pow_eq_pow_mod_two]
zero_smul au := Additive.toMul.injective pow_zero au.toMul

section CommSemiring
variable {R : Type*} [CommSemiring R] [Module R (Additive Intˣ)]

/--
Instance `Int.instUnitsPow` / 实例 `Int.instUnitsPow`

English:
instance Int.instUnitsPow
  signature: : Pow Intˣ R where
  body: (r • Additive.ofMul u).toMul

中文:
实例 整数.instUnitsPow
  签名: : 幂 整数ˣ R where
  定义体: (r • Additive.ofMul u).toMul

Depends on / 依赖: Additive, Additive.ofMul
-/
instance Int.instUnitsPow : Pow Intˣ R where
  pow u r := (r • Additive.ofMul u).toMul

-- The above instances form no typeclass diamonds with the standard power operators
example : Int.instUnitsPow = NPow.toPow := by with_implicit rfl
example : Int.instUnitsPow = ZPow.toPow := by with_implicit rfl

/--
lemma `ofMul_uzpow` / 引理 `ofMul_uzpow`

English:
lemma ofMul_uzpow
  given: (u : Intˣ) (r : R)
  statement: Additive.ofMul (u ^ r) = r • Additive.ofMul u
  proof: rfl

中文:
引理 ofMul_uzpow
  条件: (u : 整数ˣ) (r : R)
  结论: 加性.ofMul (u ^ r) = r • 加性.ofMul u
  证明: rfl
-/
@[simp] lemma ofMul_uzpow (u : Intˣ) (r : R) : Additive.ofMul (u ^ r) = r • Additive.ofMul u := rfl

/--
lemma `toMul_uzpow` / 引理 `toMul_uzpow`

English:
lemma toMul_uzpow
  given: (u : Additive Intˣ) (r : R)
  statement: (r • u).toMul = u.toMul ^ r
  proof: rfl

中文:
引理 toMul_uzpow
  条件: (u : 加性 整数ˣ) (r : R)
  结论: (r • u).toMul = u.toMul ^ r
  证明: rfl
-/
@[simp] lemma toMul_uzpow (u : Additive Intˣ) (r : R) : (r • u).toMul = u.toMul ^ r := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `uzpow_natCast` / 引理 `uzpow_natCast`

English:
lemma uzpow_natCast
  given: (u : Intˣ) (n : Nat)
  statement: u ^ (n : R) = u ^ n
  proof: by
  change ((n : R) • Additive.ofMul u).toMul = _
  rw [Nat.cast_smul_eq_nsmul]; rw [toMul_nsmul]; rw [toMul_ofMul]

中文:
引理 uzpow_natCast
  条件: (u : 整数ˣ) (n : 自然数)
  结论: u ^ (n : R) = u ^ n
  证明: by
  change ((n : R) • Additive.ofMul u).toMul = _
  rw [Nat.cast_smul_eq_nsmul]; rw [toMul_nsmul]; rw [toMul_ofMul]
-/
@[norm_cast] lemma uzpow_natCast (u : Intˣ) (n : Nat) : u ^ (n : R) = u ^ n := by
  change ((n : R) • Additive.ofMul u).toMul = _
  rw [Nat.cast_smul_eq_nsmul]; rw [toMul_nsmul]; rw [toMul_ofMul]

/--
lemma `uzpow_coe_nat` / 引理 `uzpow_coe_nat`

English:
lemma uzpow_coe_nat
  given: (s : Intˣ) (n : Nat) [n.AtLeastTwo]
  proof: uzpow_natCast _ _

中文:
引理 uzpow_coe_nat
  条件: (s : 整数ˣ) (n : 自然数) [n.AtLeastTwo]
  证明: uzpow_natCast _ _

Depends on / 依赖: uzpow_natCast
-/
lemma uzpow_coe_nat (s : Intˣ) (n : Nat) [n.AtLeastTwo] :
    s ^ (ofNat(n) : R) = s ^ (ofNat(n) : Nat) :=
  uzpow_natCast _ _

/--
lemma `one_uzpow` / 引理 `one_uzpow`

English:
lemma one_uzpow
  given: (x : R)
  statement: (1 : Intˣ) ^ x = 1
  proof: Additive.ofMul.injective smul_zero _

中文:
引理 one_uzpow
  条件: (x : R)
  结论: (1 : 整数ˣ) ^ x = 1
  证明: Additive.ofMul.injective smul_zero _
-/
@[simp] lemma one_uzpow (x : R) : (1 : Intˣ) ^ x = 1 :=
Additive.ofMul.injective smul_zero _

/--
lemma `mul_uzpow` / 引理 `mul_uzpow`

English:
lemma mul_uzpow
  given: (s₁ s₂ : Intˣ) (x : R)
  statement: (s₁ * s₂) ^ x = s₁ ^ x * s₂ ^ x
  proof: Additive.ofMul.injective smul_add x (Additive.ofMul s₁) (Additive.ofMul s₂)

中文:
引理 mul_uzpow
  条件: (s₁ s₂ : 整数ˣ) (x : R)
  结论: (s₁ * s₂) ^ x = s₁ ^ x * s₂ ^ x
  证明: Additive.ofMul.injective smul_add x (Additive.ofMul s₁) (Additive.ofMul s₂)

Depends on / 依赖: Additive, Additive.ofMul, Additive.ofMul.injective, injective, smul_add
-/
lemma mul_uzpow (s₁ s₂ : Intˣ) (x : R) : (s₁ * s₂) ^ x = s₁ ^ x * s₂ ^ x :=
Additive.ofMul.injective smul_add x (Additive.ofMul s₁) (Additive.ofMul s₂)

/--
lemma `uzpow_zero` / 引理 `uzpow_zero`

English:
lemma uzpow_zero
  given: (s : Intˣ)
  statement: (s ^ (0 : R) : Intˣ) = (1 : Intˣ)
  proof: Additive.ofMul.injective zero_smul R (Additive.ofMul s)

中文:
引理 uzpow_zero
  条件: (s : 整数ˣ)
  结论: (s ^ (0 : R) : 整数ˣ) = (1 : 整数ˣ)
  证明: Additive.ofMul.injective zero_smul R (Additive.ofMul s)
-/
@[simp] lemma uzpow_zero (s : Intˣ) : (s ^ (0 : R) : Intˣ) = (1 : Intˣ) :=
Additive.ofMul.injective zero_smul R (Additive.ofMul s)

/--
lemma `uzpow_one` / 引理 `uzpow_one`

English:
lemma uzpow_one
  given: (s : Intˣ)
  statement: (s ^ (1 : R) : Intˣ) = s
  proof: Additive.ofMul.injective one_smul R (Additive.ofMul s)

中文:
引理 uzpow_one
  条件: (s : 整数ˣ)
  结论: (s ^ (1 : R) : 整数ˣ) = s
  证明: Additive.ofMul.injective one_smul R (Additive.ofMul s)
-/
@[simp] lemma uzpow_one (s : Intˣ) : (s ^ (1 : R) : Intˣ) = s :=
Additive.ofMul.injective one_smul R (Additive.ofMul s)

/--
lemma `uzpow_mul` / 引理 `uzpow_mul`

English:
lemma uzpow_mul
  given: (s : Intˣ) (x y : R)
  statement: s ^ (x * y) = (s ^ x) ^ y
  proof: Additive.ofMul.injective mul_comm x y ▸ mul_smul y x (Additive.ofMul s)

中文:
引理 uzpow_mul
  条件: (s : 整数ˣ) (x y : R)
  结论: s ^ (x * y) = (s ^ x) ^ y
  证明: Additive.ofMul.injective mul_comm x y ▸ mul_smul y x (Additive.ofMul s)

Depends on / 依赖: Additive, Additive.ofMul, Additive.ofMul.injective, injective, mul_comm, mul_smul
-/
lemma uzpow_mul (s : Intˣ) (x y : R) : s ^ (x * y) = (s ^ x) ^ y :=
Additive.ofMul.injective mul_comm x y ▸ mul_smul y x (Additive.ofMul s)

/--
lemma `uzpow_add` / 引理 `uzpow_add`

English:
lemma uzpow_add
  given: (s : Intˣ) (x y : R)
  statement: s ^ (x + y) = s ^ x * s ^ y
  proof: Additive.ofMul.injective add_smul x y (Additive.ofMul s)

中文:
引理 uzpow_add
  条件: (s : 整数ˣ) (x y : R)
  结论: s ^ (x + y) = s ^ x * s ^ y
  证明: Additive.ofMul.injective add_smul x y (Additive.ofMul s)

Depends on / 依赖: Additive, Additive.ofMul, Additive.ofMul.injective, add_smul, injective
-/
lemma uzpow_add (s : Intˣ) (x y : R) : s ^ (x + y) = s ^ x * s ^ y :=
Additive.ofMul.injective add_smul x y (Additive.ofMul s)

end CommSemiring

section CommRing
variable {R : Type*} [CommRing R] [Module R (Additive Intˣ)]

/--
lemma `uzpow_sub` / 引理 `uzpow_sub`

English:
lemma uzpow_sub
  given: (s : Intˣ) (x y : R)
  statement: s ^ (x - y) = s ^ x / s ^ y
  proof: Additive.ofMul.injective sub_smul x y (Additive.ofMul s)

中文:
引理 uzpow_sub
  条件: (s : 整数ˣ) (x y : R)
  结论: s ^ (x - y) = s ^ x / s ^ y
  证明: Additive.ofMul.injective sub_smul x y (Additive.ofMul s)

Depends on / 依赖: Additive, Additive.ofMul, Additive.ofMul.injective, injective, sub_smul
-/
lemma uzpow_sub (s : Intˣ) (x y : R) : s ^ (x - y) = s ^ x / s ^ y :=
Additive.ofMul.injective sub_smul x y (Additive.ofMul s)

/--
lemma `uzpow_neg` / 引理 `uzpow_neg`

English:
lemma uzpow_neg
  given: (s : Intˣ) (x : R)
  statement: s ^ (-x) = (s ^ x)⁻¹
  proof: Additive.ofMul.injective neg_smul x (Additive.ofMul s)

中文:
引理 uzpow_neg
  条件: (s : 整数ˣ) (x : R)
  结论: s ^ (-x) = (s ^ x)⁻¹
  证明: Additive.ofMul.injective neg_smul x (Additive.ofMul s)

Depends on / 依赖: Additive, Additive.ofMul, Additive.ofMul.injective, injective, neg_smul
-/
lemma uzpow_neg (s : Intˣ) (x : R) : s ^ (-x) = (s ^ x)⁻¹ :=
Additive.ofMul.injective neg_smul x (Additive.ofMul s)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `uzpow_intCast` / 引理 `uzpow_intCast`

English:
lemma uzpow_intCast
  given: (u : Intˣ) (z : Int)
  statement: u ^ (z : R) = u ^ z
  proof: by
  change ((z : R) • Additive.ofMul u).toMul = _
  rw [Int.cast_smul_eq_zsmul]; rw [toMul_zsmul]; rw [toMul_ofMul]

中文:
引理 uzpow_intCast
  条件: (u : 整数ˣ) (z : 整数)
  结论: u ^ (z : R) = u ^ z
  证明: by
  change ((z : R) • Additive.ofMul u).toMul = _
  rw [Int.cast_smul_eq_zsmul]; rw [toMul_zsmul]; rw [toMul_ofMul]
-/
@[norm_cast] lemma uzpow_intCast (u : Intˣ) (z : Int) : u ^ (z : R) = u ^ z := by
  change ((z : R) • Additive.ofMul u).toMul = _
  rw [Int.cast_smul_eq_zsmul]; rw [toMul_zsmul]; rw [toMul_ofMul]

end CommRing
