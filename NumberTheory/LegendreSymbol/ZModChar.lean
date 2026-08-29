/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Int.Range
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.MulChar.Basic

/-!
# Quadratic characters on ℤ/nℤ

This file defines some quadratic characters on the rings ℤ/4ℤ and ℤ/8ℤ.

We set them up to be of type `MulChar (ZMod n) ℤ`, where `n` is `4` or `8`.

## Tags

quadratic character, zmod
-/

@[expose] public section


/-!
### Quadratic characters mod 4 and 8

We define the primitive quadratic characters `χ₄` on `ZMod 4`
and `χ₈`, `χ₈'` on `ZMod 8`.
-/


namespace ZMod

section QuadCharModP

/-- Define the nontrivial quadratic character on `ZMod 4`, `χ₄`.
It corresponds to the extension `ℚ(√-1)/ℚ`. -/
@[simps]
/--
Definition of `χ₄` / `χ₄` 的定义

English:
definition χ₄
  signature: : MulChar (ZMod 4) Int where
  body: match a with
    | 0 | 2 => 0
    | 1 => 1
    | 3 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

中文:
定义 χ₄
  签名: : 乘法特征 (ZMod 4) 整数 where
  定义体: match a with
    | 0 | 2 => 0
    | 1 => 1
    | 3 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

Depends on / 依赖: map_mul, map_nonunit, map_one
-/
def χ₄ : MulChar (ZMod 4) Int where
  toFun a :=
    match a with
    | 0 | 2 => 0
    | 1 => 1
    | 3 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/--
theorem `isQuadratic_χ₄` / 定理 `isQuadratic_χ₄`

English:
theorem isQuadratic_χ₄
  statement: χ₄.IsQuadratic
  proof: by
  unfold MulChar.IsQuadratic
  decide

中文:
定理 isQuadratic_χ₄
  结论: χ₄.IsQuadratic
  证明: by
  unfold MulChar.IsQuadratic
  decide

Depends on / 依赖: IsQuadratic, MulChar, MulChar.IsQuadratic
-/
theorem isQuadratic_χ₄ : χ₄.IsQuadratic := by
  unfold MulChar.IsQuadratic
  decide

/--
theorem `χ₄_nat_mod_four` / 定理 `χ₄_nat_mod_four`

English:
theorem χ₄_nat_mod_four
  given: (n : Nat)
  statement: χ₄ n = χ₄ (n % 4 : Nat)
  proof: by grind

中文:
定理 χ₄_nat_mod_four
  条件: (n : 自然数)
  结论: χ₄ n = χ₄ (n % 4 : 自然数)
  证明: by grind
-/
theorem χ₄_nat_mod_four (n : Nat) : χ₄ n = χ₄ (n % 4 : Nat) := by grind

/--
theorem `χ₄_int_mod_four` / 定理 `χ₄_int_mod_four`

English:
theorem χ₄_int_mod_four
  given: (n : Int)
  statement: χ₄ n = χ₄ (n % 4 : Int)
  proof: by
  rw [← ZMod.intCast_mod n 4]; rw [Nat.cast_ofNat]

中文:
定理 χ₄_int_mod_four
  条件: (n : 整数)
  结论: χ₄ n = χ₄ (n % 4 : 整数)
  证明: by
  rw [← ZMod.intCast_mod n 4]; rw [Nat.cast_ofNat]

Depends on / 依赖: Nat.cast_ofNat, ZMod.intCast_mod, cast_ofNat, intCast_mod
-/
theorem χ₄_int_mod_four (n : Int) : χ₄ n = χ₄ (n % 4 : Int) := by
  rw [← ZMod.intCast_mod n 4]; rw [Nat.cast_ofNat]

/--
theorem `χ₄_int_eq_if_mod_four` / 定理 `χ₄_int_eq_if_mod_four`

English:
theorem χ₄_int_eq_if_mod_four
  given: (n : Int)
  proof: by
  have help : forall m : Int, 0 <= m -> m < 4 -> χ₄ m = if m % 2 = 0 then 0 else if m = 1 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by lia : (2 : Int) ∣ 4)]; rw [← ZMod.intCast_mod n 4]
  exact help (n % 4) (Int.emod_nonneg n (by lia)) (Int.emod_lt_abs n (by lia))

中文:
定理 χ₄_int_eq_if_mod_four
  条件: (n : 整数)
  证明: by
  have help : forall m : Int, 0 <= m -> m < 4 -> χ₄ m = if m % 2 = 0 then 0 else if m = 1 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by lia : (2 : Int) ∣ 4)]; rw [← ZMod.intCast_mod n 4]
  exact help (n % 4) (Int.emod_nonneg n (by lia)) (Int.emod_lt_abs n (by lia))

Depends on / 依赖: Int.emod_emod_of_dvd, Int.emod_lt_abs, Int.emod_nonneg, ZMod.intCast_mod, emod_emod_of_dvd, emod_lt_abs, emod_nonneg, intCast_mod
-/
theorem χ₄_int_eq_if_mod_four (n : Int) :
    χ₄ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  have help : forall m : Int, 0 <= m -> m < 4 -> χ₄ m = if m % 2 = 0 then 0 else if m = 1 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by lia : (2 : Int) ∣ 4)]; rw [← ZMod.intCast_mod n 4]
  exact help (n % 4) (Int.emod_nonneg n (by lia)) (Int.emod_lt_abs n (by lia))

/--
theorem `χ₄_nat_eq_if_mod_four` / 定理 `χ₄_nat_eq_if_mod_four`

English:
theorem χ₄_nat_eq_if_mod_four
  given: (n : Nat)
  proof: mod_cast χ₄_int_eq_if_mod_four n

中文:
定理 χ₄_nat_eq_if_mod_four
  条件: (n : 自然数)
  证明: mod_cast χ₄_int_eq_if_mod_four n

Depends on / 依赖: mod_cast
-/
theorem χ₄_nat_eq_if_mod_four (n : Nat) :
    χ₄ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 :=
  mod_cast χ₄_int_eq_if_mod_four n

/--
theorem `χ₄_eq_neg_one_pow` / 定理 `χ₄_eq_neg_one_pow`

English:
theorem χ₄_eq_neg_one_pow
  given: {n : Nat} (hn : n % 2 = 1)
  statement: χ₄ n = (-1) ^ (n / 2)
  proof: by
  rw [χ₄_nat_eq_if_mod_four]
  simp only [hn, Nat.one_ne_zero, if_false]
  nth_rewrite 3 [← Nat.div_add_mod n 4]
  nth_rewrite 3 [show 4 = 2 * 2 by lia]
  rw [mul_assoc]; rw [add_comm]; rw [Nat.add_mul_div_left _ _ zero_lt_two]; rw [pow_add]; rw [pow_mul]; rw [neg_one_sq]; rw [one_pow]; rw [mul_o

中文:
定理 χ₄_eq_neg_one_pow
  条件: {n : 自然数} (hn : n % 2 = 1)
  结论: χ₄ n = (-1) ^ (n / 2)
  证明: by
  rw [χ₄_nat_eq_if_mod_four]
  simp only [hn, Nat.one_ne_zero, if_false]
  nth_rewrite 3 [← Nat.div_add_mod n 4]
  nth_rewrite 3 [show 4 = 2 * 2 by lia]
  rw [mul_assoc]; rw [add_comm]; rw [Nat.add_mul_div_left _ _ zero_lt_two]; rw [pow_add]; rw [pow_mul]; rw [neg_one_sq]; rw [one_pow]; rw [mul_o

Depends on / 依赖: Nat.add_mul_div_left, Nat.div_add_mod, Nat.mod_lt, Nat.mod_mod_of_dvd, Nat.one_ne_zero, add_comm, add_mul_div_left, div_add_mod, if_false, mod_lt, mod_mod_of_dvd, mul_assoc, mul_one, neg_one_sq, nth_rewrite, one_ne_zero, one_pow, pow_add, pow_mul, zero_lt_two
-/
theorem χ₄_eq_neg_one_pow {n : Nat} (hn : n % 2 = 1) : χ₄ n = (-1) ^ (n / 2) := by
  rw [χ₄_nat_eq_if_mod_four]
  simp only [hn, Nat.one_ne_zero, if_false]
  nth_rewrite 3 [← Nat.div_add_mod n 4]
  nth_rewrite 3 [show 4 = 2 * 2 by lia]
  rw [mul_assoc]; rw [add_comm]; rw [Nat.add_mul_div_left _ _ zero_lt_two]; rw [pow_add]; rw [pow_mul]; rw [neg_one_sq]; rw [one_pow]; rw [mul_one]
  have help : forall m : Nat, m < 4 -> m % 2 = 1 -> ite (m = 1) (1 : Int) (-1) = (-1) ^ (m / 2) := by decide
exact help _ (Nat.mod_lt n (by lia)) (Nat.mod_mod_of_dvd n (by lia : 2 ∣ 4)).trans hn

/--
theorem `χ₄_nat_one_mod_four` / 定理 `χ₄_nat_one_mod_four`

English:
theorem χ₄_nat_one_mod_four
  given: {n : Nat} (hn : n % 4 = 1)
  statement: χ₄ n = 1
  proof: by
  rw [χ₄_nat_mod_four]; rw [hn]
  rfl

中文:
定理 χ₄_nat_one_mod_four
  条件: {n : 自然数} (hn : n % 4 = 1)
  结论: χ₄ n = 1
  证明: by
  rw [χ₄_nat_mod_four]; rw [hn]
  rfl
-/
theorem χ₄_nat_one_mod_four {n : Nat} (hn : n % 4 = 1) : χ₄ n = 1 := by
  rw [χ₄_nat_mod_four]; rw [hn]
  rfl

/--
theorem `χ₄_nat_three_mod_four` / 定理 `χ₄_nat_three_mod_four`

English:
theorem χ₄_nat_three_mod_four
  given: {n : Nat} (hn : n % 4 = 3)
  statement: χ₄ n = -1
  proof: by
  rw [χ₄_nat_mod_four]; rw [hn]
  rfl

中文:
定理 χ₄_nat_three_mod_four
  条件: {n : 自然数} (hn : n % 4 = 3)
  结论: χ₄ n = -1
  证明: by
  rw [χ₄_nat_mod_four]; rw [hn]
  rfl
-/
theorem χ₄_nat_three_mod_four {n : Nat} (hn : n % 4 = 3) : χ₄ n = -1 := by
  rw [χ₄_nat_mod_four]; rw [hn]
  rfl

/--
theorem `χ₄_int_one_mod_four` / 定理 `χ₄_int_one_mod_four`

English:
theorem χ₄_int_one_mod_four
  given: {n : Int} (hn : n % 4 = 1)
  statement: χ₄ n = 1
  proof: by
  rw [χ₄_int_mod_four]; rw [hn]
  rfl

中文:
定理 χ₄_int_one_mod_four
  条件: {n : 整数} (hn : n % 4 = 1)
  结论: χ₄ n = 1
  证明: by
  rw [χ₄_int_mod_four]; rw [hn]
  rfl
-/
theorem χ₄_int_one_mod_four {n : Int} (hn : n % 4 = 1) : χ₄ n = 1 := by
  rw [χ₄_int_mod_four]; rw [hn]
  rfl

/--
theorem `χ₄_int_three_mod_four` / 定理 `χ₄_int_three_mod_four`

English:
theorem χ₄_int_three_mod_four
  given: {n : Int} (hn : n % 4 = 3)
  statement: χ₄ n = -1
  proof: by
  rw [χ₄_int_mod_four]; rw [hn]
  rfl

中文:
定理 χ₄_int_three_mod_four
  条件: {n : 整数} (hn : n % 4 = 3)
  结论: χ₄ n = -1
  证明: by
  rw [χ₄_int_mod_four]; rw [hn]
  rfl
-/
theorem χ₄_int_three_mod_four {n : Int} (hn : n % 4 = 3) : χ₄ n = -1 := by
  rw [χ₄_int_mod_four]; rw [hn]
  rfl

/--
theorem `neg_one_pow_div_two_of_one_mod_four` / 定理 `neg_one_pow_div_two_of_one_mod_four`

English:
theorem neg_one_pow_div_two_of_one_mod_four
  given: {n : Nat} (hn : n % 4 = 1)
  statement: (-1 : Int) ^ (n / 2) = 1
  proof: χ₄_eq_neg_one_pow (Nat.odd_of_mod_four_eq_one hn) ▸ χ₄_nat_one_mod_four hn

中文:
定理 neg_one_pow_div_two_of_one_mod_four
  条件: {n : 自然数} (hn : n % 4 = 1)
  结论: (-1 : 整数) ^ (n / 2) = 1
  证明: χ₄_eq_neg_one_pow (Nat.odd_of_mod_four_eq_one hn) ▸ χ₄_nat_one_mod_four hn

Depends on / 依赖: Nat.odd_of_mod_four_eq_one, odd_of_mod_four_eq_one
-/
theorem neg_one_pow_div_two_of_one_mod_four {n : Nat} (hn : n % 4 = 1) : (-1 : Int) ^ (n / 2) = 1 :=
  χ₄_eq_neg_one_pow (Nat.odd_of_mod_four_eq_one hn) ▸ χ₄_nat_one_mod_four hn

/--
theorem `neg_one_pow_div_two_of_three_mod_four` / 定理 `neg_one_pow_div_two_of_three_mod_four`

English:
theorem neg_one_pow_div_two_of_three_mod_four
  given: {n : Nat} (hn : n % 4 = 3)
  statement: (-1 : Int) ^ (n / 2) = -1
  proof: χ₄_eq_neg_one_pow (Nat.odd_of_mod_four_eq_three hn) ▸ χ₄_nat_three_mod_four hn

中文:
定理 neg_one_pow_div_two_of_three_mod_four
  条件: {n : 自然数} (hn : n % 4 = 3)
  结论: (-1 : 整数) ^ (n / 2) = -1
  证明: χ₄_eq_neg_one_pow (Nat.odd_of_mod_four_eq_three hn) ▸ χ₄_nat_three_mod_four hn

Depends on / 依赖: Nat.odd_of_mod_four_eq_three, odd_of_mod_four_eq_three
-/
theorem neg_one_pow_div_two_of_three_mod_four {n : Nat} (hn : n % 4 = 3) : (-1 : Int) ^ (n / 2) = -1 :=
  χ₄_eq_neg_one_pow (Nat.odd_of_mod_four_eq_three hn) ▸ χ₄_nat_three_mod_four hn

/-- Define the first primitive quadratic character on `ZMod 8`, `χ₈`.
It corresponds to the extension `ℚ(√2)/ℚ`. -/
@[simps]
/--
Definition of `χ₈` / `χ₈` 的定义

English:
definition χ₈
  signature: : MulChar (ZMod 8) Int where
  body: match a with
    | 0 | 2 | 4 | 6 => 0
    | 1 | 7 => 1
    | 3 | 5 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

中文:
定义 χ₈
  签名: : 乘法特征 (ZMod 8) 整数 where
  定义体: match a with
    | 0 | 2 | 4 | 6 => 0
    | 1 | 7 => 1
    | 3 | 5 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

Depends on / 依赖: map_mul, map_nonunit, map_one
-/
def χ₈ : MulChar (ZMod 8) Int where
  toFun a :=
    match a with
    | 0 | 2 | 4 | 6 => 0
    | 1 | 7 => 1
    | 3 | 5 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/--
theorem `isQuadratic_χ₈` / 定理 `isQuadratic_χ₈`

English:
theorem isQuadratic_χ₈
  statement: χ₈.IsQuadratic
  proof: by
  unfold MulChar.IsQuadratic
  decide

中文:
定理 isQuadratic_χ₈
  结论: χ₈.IsQuadratic
  证明: by
  unfold MulChar.IsQuadratic
  decide

Depends on / 依赖: IsQuadratic, MulChar, MulChar.IsQuadratic
-/
theorem isQuadratic_χ₈ : χ₈.IsQuadratic := by
  unfold MulChar.IsQuadratic
  decide

/--
theorem `χ₈_nat_mod_eight` / 定理 `χ₈_nat_mod_eight`

English:
theorem χ₈_nat_mod_eight
  given: (n : Nat)
  statement: χ₈ n = χ₈ (n % 8 : Nat)
  proof: by
  rw [← ZMod.natCast_mod n 8]

中文:
定理 χ₈_nat_mod_eight
  条件: (n : 自然数)
  结论: χ₈ n = χ₈ (n % 8 : 自然数)
  证明: by
  rw [← ZMod.natCast_mod n 8]

Depends on / 依赖: ZMod.natCast_mod, natCast_mod
-/
theorem χ₈_nat_mod_eight (n : Nat) : χ₈ n = χ₈ (n % 8 : Nat) := by
  rw [← ZMod.natCast_mod n 8]

/--
theorem `χ₈_int_mod_eight` / 定理 `χ₈_int_mod_eight`

English:
theorem χ₈_int_mod_eight
  given: (n : Int)
  statement: χ₈ n = χ₈ (n % 8 : Int)
  proof: by
  rw [← ZMod.intCast_mod n 8]; rw [Nat.cast_ofNat]

中文:
定理 χ₈_int_mod_eight
  条件: (n : 整数)
  结论: χ₈ n = χ₈ (n % 8 : 整数)
  证明: by
  rw [← ZMod.intCast_mod n 8]; rw [Nat.cast_ofNat]

Depends on / 依赖: Nat.cast_ofNat, ZMod.intCast_mod, cast_ofNat, intCast_mod
-/
theorem χ₈_int_mod_eight (n : Int) : χ₈ n = χ₈ (n % 8 : Int) := by
  rw [← ZMod.intCast_mod n 8]; rw [Nat.cast_ofNat]

/--
theorem `χ₈_int_eq_if_mod_eight` / 定理 `χ₈_int_eq_if_mod_eight`

English:
theorem χ₈_int_eq_if_mod_eight
  given: (n : Int)
  proof: by
  have help :
    forall m : Int, 0 <= m -> m < 8 -> χ₈ m = if m % 2 = 0 then 0 else if m = 1 ∨ m = 7 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by lia : (2 : Int) ∣ 8)]; rw [← ZMod.intCast_mod n 8]
  exact help (n % 8) (Int.emod_nonneg n (by lia)) (Int.emod_lt_abs n (by lia)

中文:
定理 χ₈_int_eq_if_mod_eight
  条件: (n : 整数)
  证明: by
  have help :
    forall m : Int, 0 <= m -> m < 8 -> χ₈ m = if m % 2 = 0 then 0 else if m = 1 ∨ m = 7 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by lia : (2 : Int) ∣ 8)]; rw [← ZMod.intCast_mod n 8]
  exact help (n % 8) (Int.emod_nonneg n (by lia)) (Int.emod_lt_abs n (by lia)

Depends on / 依赖: Int.emod_emod_of_dvd, Int.emod_lt_abs, Int.emod_nonneg, ZMod.intCast_mod, emod_emod_of_dvd, emod_lt_abs, emod_nonneg, intCast_mod
-/
theorem χ₈_int_eq_if_mod_eight (n : Int) :
    χ₈ n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 := by
  have help :
    forall m : Int, 0 <= m -> m < 8 -> χ₈ m = if m % 2 = 0 then 0 else if m = 1 ∨ m = 7 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by lia : (2 : Int) ∣ 8)]; rw [← ZMod.intCast_mod n 8]
  exact help (n % 8) (Int.emod_nonneg n (by lia)) (Int.emod_lt_abs n (by lia))

/--
theorem `χ₈_nat_eq_if_mod_eight` / 定理 `χ₈_nat_eq_if_mod_eight`

English:
theorem χ₈_nat_eq_if_mod_eight
  given: (n : Nat)
  proof: mod_cast χ₈_int_eq_if_mod_eight n

中文:
定理 χ₈_nat_eq_if_mod_eight
  条件: (n : 自然数)
  证明: mod_cast χ₈_int_eq_if_mod_eight n

Depends on / 依赖: mod_cast
-/
theorem χ₈_nat_eq_if_mod_eight (n : Nat) :
    χ₈ n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 :=
  mod_cast χ₈_int_eq_if_mod_eight n

/-- Define the second primitive quadratic character on `ZMod 8`, `χ₈'`.
It corresponds to the extension `ℚ(√-2)/ℚ`. -/
@[simps]
/--
Definition of `χ₈'` / `χ₈'` 的定义

English:
definition χ₈'
  signature: : MulChar (ZMod 8) Int where
  body: match a with
    | 0 | 2 | 4 | 6 => 0
    | 1 | 3 => 1
    | 5 | 7 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

中文:
定义 χ₈'
  签名: : 乘法特征 (ZMod 8) 整数 where
  定义体: match a with
    | 0 | 2 | 4 | 6 => 0
    | 1 | 3 => 1
    | 5 | 7 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

Depends on / 依赖: map_mul, map_nonunit, map_one
-/
def χ₈' : MulChar (ZMod 8) Int where
  toFun a :=
    match a with
    | 0 | 2 | 4 | 6 => 0
    | 1 | 3 => 1
    | 5 | 7 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/--
theorem `isQuadratic_χ₈'` / 定理 `isQuadratic_χ₈'`

English:
theorem isQuadratic_χ₈'
  statement: χ₈'.IsQuadratic
  proof: by
  unfold MulChar.IsQuadratic
  decide

中文:
定理 isQuadratic_χ₈'
  结论: χ₈'.IsQuadratic
  证明: by
  unfold MulChar.IsQuadratic
  decide

Depends on / 依赖: IsQuadratic, MulChar, MulChar.IsQuadratic
-/
theorem isQuadratic_χ₈' : χ₈'.IsQuadratic := by
  unfold MulChar.IsQuadratic
  decide

/--
theorem `χ₈'_int_eq_if_mod_eight` / 定理 `χ₈'_int_eq_if_mod_eight`

English:
theorem χ₈'_int_eq_if_mod_eight
  given: (n : Int)
  proof: by
  have help :
    forall m : Int, 0 <= m -> m < 8 -> χ₈' m = if m % 2 = 0 then 0 else if m = 1 ∨ m = 3 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by lia : (2 : Int) ∣ 8)]; rw [← ZMod.intCast_mod n 8]
  exact help (n % 8) (Int.emod_nonneg n (by lia)) (Int.emod_lt_abs n (by lia

中文:
定理 χ₈'_int_eq_if_mod_eight
  条件: (n : 整数)
  证明: by
  have help :
    forall m : Int, 0 <= m -> m < 8 -> χ₈' m = if m % 2 = 0 then 0 else if m = 1 ∨ m = 3 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by lia : (2 : Int) ∣ 8)]; rw [← ZMod.intCast_mod n 8]
  exact help (n % 8) (Int.emod_nonneg n (by lia)) (Int.emod_lt_abs n (by lia
-/
theorem χ₈'_int_eq_if_mod_eight (n : Int) :
    χ₈' n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 := by
  have help :
    forall m : Int, 0 <= m -> m < 8 -> χ₈' m = if m % 2 = 0 then 0 else if m = 1 ∨ m = 3 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by lia : (2 : Int) ∣ 8)]; rw [← ZMod.intCast_mod n 8]
  exact help (n % 8) (Int.emod_nonneg n (by lia)) (Int.emod_lt_abs n (by lia))

/--
theorem `χ₈'_nat_eq_if_mod_eight` / 定理 `χ₈'_nat_eq_if_mod_eight`

English:
theorem χ₈'_nat_eq_if_mod_eight
  given: (n : Nat)
  proof: mod_cast χ₈'_int_eq_if_mod_eight n

中文:
定理 χ₈'_nat_eq_if_mod_eight
  条件: (n : 自然数)
  证明: mod_cast χ₈'_int_eq_if_mod_eight n
-/
theorem χ₈'_nat_eq_if_mod_eight (n : Nat) :
    χ₈' n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 :=
  mod_cast χ₈'_int_eq_if_mod_eight n

/--
theorem `χ₈'_eq_χ₄_mul_χ₈` / 定理 `χ₈'_eq_χ₄_mul_χ₈`

English:
theorem χ₈'_eq_χ₄_mul_χ₈
  statement: forall a : ZMod 8, χ₈' a = χ₄ (cast a) * χ₈ a
  proof: by
  decide

中文:
定理 χ₈'_eq_χ₄_mul_χ₈
  结论: 对任意 a : ZMod 8, χ₈' a = χ₄ (cast a) * χ₈ a
  证明: by
  decide
-/
theorem χ₈'_eq_χ₄_mul_χ₈ : forall a : ZMod 8, χ₈' a = χ₄ (cast a) * χ₈ a := by
  decide

/--
theorem `χ₈'_int_eq_χ₄_mul_χ₈` / 定理 `χ₈'_int_eq_χ₄_mul_χ₈`

English:
theorem χ₈'_int_eq_χ₄_mul_χ₈
  given: (a : Int)
  statement: χ₈' a = χ₄ a * χ₈ a
  proof: by
  rw [← @cast_intCast 8 (ZMod 4) _ 4 _ (by lia) a]
  exact χ₈'_eq_χ₄_mul_χ₈ a

中文:
定理 χ₈'_int_eq_χ₄_mul_χ₈
  条件: (a : 整数)
  结论: χ₈' a = χ₄ a * χ₈ a
  证明: by
  rw [← @cast_intCast 8 (ZMod 4) _ 4 _ (by lia) a]
  exact χ₈'_eq_χ₄_mul_χ₈ a
-/
theorem χ₈'_int_eq_χ₄_mul_χ₈ (a : Int) : χ₈' a = χ₄ a * χ₈ a := by
  rw [← @cast_intCast 8 (ZMod 4) _ 4 _ (by lia) a]
  exact χ₈'_eq_χ₄_mul_χ₈ a

end QuadCharModP

end ZMod
