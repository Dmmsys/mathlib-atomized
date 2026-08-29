/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Fintype.Parity
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Quadratic characters of finite fields

This file defines the quadratic character on a finite field `F` and proves
some basic statements about it.

## Tags

quadratic character
-/

@[expose] public section


/-!
### Definition of the quadratic character

We define the quadratic character of a finite field `F` with values in ℤ.
-/


section Define

/--
Definition of `quadraticCharFun` / `quadraticCharFun` 的定义

English:
definition quadraticCharFun
  signature: (α : Type*) [MonoidWithZero α] [DecidableEq α]
  body: if a = 0 then 0 else if IsSquare a then 1 else -1

中文:
定义 quadraticCharFun
  签名: (α : 类型) [带零幺半群 α] [DecidableEq α]
  定义体: if a = 0 then 0 else if IsSquare a then 1 else -1

Depends on / 依赖: IsSquare
-/
def quadraticCharFun (α : Type*) [MonoidWithZero α] [DecidableEq α]
    [DecidablePred (IsSquare : α -> Prop)] (a : α) : Int :=
  if a = 0 then 0 else if IsSquare a then 1 else -1

end Define

/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/


section quadraticChar

open MulChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/--
theorem `quadraticCharFun_eq_zero_iff` / 定理 `quadraticCharFun_eq_zero_iff`

English:
theorem quadraticCharFun_eq_zero_iff
  given: {a : F}
  statement: quadraticCharFun F a = 0 ↔ a = 0
  proof: by
  simp only [quadraticCharFun]
  grind

@[simp]

中文:
定理 quadraticCharFun_eq_zero_iff
  条件: {a : F}
  结论: quadraticCharFun F a = 0 ↔ a = 0
  证明: by
  simp only [quadraticCharFun]
  grind

@[simp]

Depends on / 依赖: quadraticCharFun
-/
theorem quadraticCharFun_eq_zero_iff {a : F} : quadraticCharFun F a = 0 ↔ a = 0 := by
  simp only [quadraticCharFun]
  grind

@[simp]
/--
theorem `quadraticCharFun_zero` / 定理 `quadraticCharFun_zero`

English:
theorem quadraticCharFun_zero
  statement: quadraticCharFun F 0 = 0
  proof: by
  simp only [quadraticCharFun, if_true]

@[simp]

中文:
定理 quadraticCharFun_zero
  结论: quadraticCharFun F 0 = 0
  证明: by
  simp only [quadraticCharFun, if_true]

@[simp]

Depends on / 依赖: if_true, quadraticCharFun
-/
theorem quadraticCharFun_zero : quadraticCharFun F 0 = 0 := by
  simp only [quadraticCharFun, if_true]

@[simp]
/--
theorem `quadraticCharFun_one` / 定理 `quadraticCharFun_one`

English:
theorem quadraticCharFun_one
  statement: quadraticCharFun F 1 = 1
  proof: by
  simp only [quadraticCharFun, one_ne_zero, IsSquare.one, if_true, if_false]

中文:
定理 quadraticCharFun_one
  结论: quadraticCharFun F 1 = 1
  证明: by
  simp only [quadraticCharFun, one_ne_zero, IsSquare.one, if_true, if_false]

Depends on / 依赖: IsSquare, IsSquare.one, if_false, if_true, one_ne_zero, quadraticCharFun
-/
theorem quadraticCharFun_one : quadraticCharFun F 1 = 1 := by
  simp only [quadraticCharFun, one_ne_zero, IsSquare.one, if_true, if_false]

/--
theorem `quadraticCharFun_eq_one_of_char_two` / 定理 `quadraticCharFun_eq_one_of_char_two`

English:
theorem quadraticCharFun_eq_one_of_char_two
  given: (hF : ringChar F = 2) {a : F} (ha : a != 0)
  proof: by
  simp only [quadraticCharFun, ha, if_false, ite_eq_left_iff]
  exact fun h => (h (FiniteField.isSquare_of_char_two hF a)).elim

中文:
定理 quadraticCharFun_eq_one_of_char_two
  条件: (hF : ringChar F = 2) {a : F} (ha : a != 0)
  证明: by
  simp only [quadraticCharFun, ha, if_false, ite_eq_left_iff]
  exact fun h => (h (FiniteField.isSquare_of_char_two hF a)).elim

Depends on / 依赖: FiniteField, FiniteField.isSquare_of_char_two, if_false, isSquare_of_char_two, ite_eq_left_iff, quadraticCharFun
-/
theorem quadraticCharFun_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a != 0) :
    quadraticCharFun F a = 1 := by
  simp only [quadraticCharFun, ha, if_false, ite_eq_left_iff]
  exact fun h => (h (FiniteField.isSquare_of_char_two hF a)).elim

/--
theorem `quadraticCharFun_eq_pow_of_char_ne_two` / 定理 `quadraticCharFun_eq_pow_of_char_ne_two`

English:
theorem quadraticCharFun_eq_pow_of_char_ne_two
  given: (hF : ringChar F != 2) {a : F} (ha : a != 0)
  proof: by
  simp only [quadraticCharFun, ha, if_false]
  simp_rw [FiniteField.isSquare_iff hF ha]

中文:
定理 quadraticCharFun_eq_pow_of_char_ne_two
  条件: (hF : ringChar F != 2) {a : F} (ha : a != 0)
  证明: by
  simp only [quadraticCharFun, ha, if_false]
  simp_rw [FiniteField.isSquare_iff hF ha]

Depends on / 依赖: FiniteField, FiniteField.isSquare_iff, if_false, isSquare_iff, quadraticCharFun, simp_rw
-/
theorem quadraticCharFun_eq_pow_of_char_ne_two (hF : ringChar F != 2) {a : F} (ha : a != 0) :
    quadraticCharFun F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 := by
  simp only [quadraticCharFun, ha, if_false]
  simp_rw [FiniteField.isSquare_iff hF ha]

/--
theorem `quadraticCharFun_mul` / 定理 `quadraticCharFun_mul`

English:
theorem quadraticCharFun_mul
  given: (a b : F)
  proof: by
  by_cases ha : a = 0
  · rw [ha, zero_mul, quadraticCharFun_zero, zero_mul]
  -- now `a ≠ 0`
  by_cases hb : b = 0
  · rw [hb, mul_zero, quadraticCharFun_zero, mul_zero]
  -- now `a ≠ 0` and `b ≠ 0`
  have hab := mul_ne_zero ha hb
  by_cases hF : ringChar F = 2
  · -- case `ringChar F = 2`
    r

中文:
定理 quadraticCharFun_mul
  条件: (a b : F)
  证明: by
  by_cases ha : a = 0
  · rw [ha, zero_mul, quadraticCharFun_zero, zero_mul]
  -- now `a ≠ 0`
  by_cases hb : b = 0
  · rw [hb, mul_zero, quadraticCharFun_zero, mul_zero]
  -- now `a ≠ 0` and `b ≠ 0`
  have hab := mul_ne_zero ha hb
  by_cases hF : ringChar F = 2
  · -- case `ringChar F = 2`
    r

Depends on / 依赖: quadraticCharFun_zero, zero_mul
-/
theorem quadraticCharFun_mul (a b : F) :
    quadraticCharFun F (a * b) = quadraticCharFun F a * quadraticCharFun F b := by
  by_cases ha : a = 0
  · rw [ha, zero_mul, quadraticCharFun_zero, zero_mul]
  -- now `a ≠ 0`
  by_cases hb : b = 0
  · rw [hb, mul_zero, quadraticCharFun_zero, mul_zero]
  -- now `a ≠ 0` and `b ≠ 0`
  have hab := mul_ne_zero ha hb
  by_cases hF : ringChar F = 2
  · -- case `ringChar F = 2`
    rw [quadraticCharFun_eq_one_of_char_two hF ha]; rw [quadraticCharFun_eq_one_of_char_two hF hb]; rw [quadraticCharFun_eq_one_of_char_two hF hab]; rw [mul_one]
  · -- case of odd characteristic
    rw [quadraticCharFun_eq_pow_of_char_ne_two hF ha]; rw [quadraticCharFun_eq_pow_of_char_ne_two hF hb]; rw [quadraticCharFun_eq_pow_of_char_ne_two hF hab]; rw [mul_pow]
    rcases FiniteField.pow_dichotomy hF hb with hb' | hb'
    · simp only [hb', mul_one, if_true]
    · have h := Ring.neg_one_ne_one_of_char_ne_two hF
      -- `-1 ≠ 1`
      simp only [hb', mul_neg, mul_one, h, if_false]
      rcases FiniteField.pow_dichotomy hF ha with ha' | ha' <;>
        simp only [ha', h, neg_neg, if_true, if_false]

variable (F) in
/-- The quadratic character as a multiplicative character. -/
@[simps]
/--
Definition of `quadraticChar` / `quadraticChar` 的定义

English:
definition quadraticChar
  signature: : MulChar F Int where
  body: quadraticCharFun F
  map_one' := quadraticCharFun_one
  map_mul' := quadraticCharFun_mul
  map_nonunit' a ha := by rw [of_not_not (mt Ne.isUnit ha)]; exact quadraticCharFun_zero

中文:
定义 quadraticChar
  签名: : 乘法特征 F 整数 where
  定义体: quadraticCharFun F
  map_one' := quadraticCharFun_one
  map_mul' := quadraticCharFun_mul
  map_nonunit' a ha := by rw [of_not_not (mt Ne.isUnit ha)]; exact quadraticCharFun_zero

Depends on / 依赖: quadraticCharFun
-/
def quadraticChar : MulChar F Int where
  toFun := quadraticCharFun F
  map_one' := quadraticCharFun_one
  map_mul' := quadraticCharFun_mul
  map_nonunit' a ha := by rw [of_not_not (mt Ne.isUnit ha)]; exact quadraticCharFun_zero

/--
theorem `quadraticChar_eq_zero_iff` / 定理 `quadraticChar_eq_zero_iff`

English:
theorem quadraticChar_eq_zero_iff
  given: {a : F}
  statement: quadraticChar F a = 0 ↔ a = 0
  proof: quadraticCharFun_eq_zero_iff

中文:
定理 quadraticChar_eq_zero_iff
  条件: {a : F}
  结论: quadraticChar F a = 0 ↔ a = 0
  证明: quadraticCharFun_eq_zero_iff

Depends on / 依赖: quadraticCharFun_eq_zero_iff
-/
theorem quadraticChar_eq_zero_iff {a : F} : quadraticChar F a = 0 ↔ a = 0 :=
  quadraticCharFun_eq_zero_iff

/--
theorem `quadraticChar_zero` / 定理 `quadraticChar_zero`

English:
theorem quadraticChar_zero
  statement: quadraticChar F 0 = 0
  proof: by
  simp only [quadraticChar_apply, quadraticCharFun_zero]

中文:
定理 quadraticChar_zero
  结论: quadraticChar F 0 = 0
  证明: by
  simp only [quadraticChar_apply, quadraticCharFun_zero]

Depends on / 依赖: quadraticCharFun_zero, quadraticChar_apply
-/
theorem quadraticChar_zero : quadraticChar F 0 = 0 := by
  simp only [quadraticChar_apply, quadraticCharFun_zero]

/--
theorem `quadraticChar_one_iff_isSquare` / 定理 `quadraticChar_one_iff_isSquare`

English:
theorem quadraticChar_one_iff_isSquare
  given: {a : F} (ha : a != 0)
  proof: by
  simp only [quadraticChar_apply, quadraticCharFun, ha, if_false, ite_eq_left_iff,
    imp_false, not_not, reduceCtorEq]

中文:
定理 quadraticChar_one_iff_isSquare
  条件: {a : F} (ha : a != 0)
  证明: by
  simp only [quadraticChar_apply, quadraticCharFun, ha, if_false, ite_eq_left_iff,
    imp_false, not_not, reduceCtorEq]

Depends on / 依赖: if_false, imp_false, ite_eq_left_iff, not_not, quadraticCharFun, quadraticChar_apply, reduceCtorEq
-/
theorem quadraticChar_one_iff_isSquare {a : F} (ha : a != 0) :
    quadraticChar F a = 1 ↔ IsSquare a := by
  simp only [quadraticChar_apply, quadraticCharFun, ha, if_false, ite_eq_left_iff,
    imp_false, not_not, reduceCtorEq]

/--
theorem `quadraticChar_sq_one'` / 定理 `quadraticChar_sq_one'`

English:
theorem quadraticChar_sq_one'
  given: {a : F} (ha : a != 0)
  statement: quadraticChar F (a ^ 2) = 1
  proof: by
  simp only [quadraticChar_apply, quadraticCharFun, sq_eq_zero_iff, ha, IsSquare.sq, if_true,
    if_false]

中文:
定理 quadraticChar_sq_one'
  条件: {a : F} (ha : a != 0)
  结论: quadraticChar F (a ^ 2) = 1
  证明: by
  simp only [quadraticChar_apply, quadraticCharFun, sq_eq_zero_iff, ha, IsSquare.sq, if_true,
    if_false]

Depends on / 依赖: IsSquare, IsSquare.sq, if_false, if_true, quadraticCharFun, quadraticChar_apply, sq_eq_zero_iff
-/
theorem quadraticChar_sq_one' {a : F} (ha : a != 0) : quadraticChar F (a ^ 2) = 1 := by
  simp only [quadraticChar_apply, quadraticCharFun, sq_eq_zero_iff, ha, IsSquare.sq, if_true,
    if_false]

/--
theorem `quadraticChar_sq_one` / 定理 `quadraticChar_sq_one`

English:
theorem quadraticChar_sq_one
  given: {a : F} (ha : a != 0)
  statement: quadraticChar F a ^ 2 = 1
  proof: by
  rwa [pow_two, ← map_mul, ← pow_two, quadraticChar_sq_one']

中文:
定理 quadraticChar_sq_one
  条件: {a : F} (ha : a != 0)
  结论: quadraticChar F a ^ 2 = 1
  证明: by
  rwa [pow_two, ← map_mul, ← pow_two, quadraticChar_sq_one']

Depends on / 依赖: map_mul, pow_two, quadraticChar_sq_one
-/
theorem quadraticChar_sq_one {a : F} (ha : a != 0) : quadraticChar F a ^ 2 = 1 := by
  rwa [pow_two, ← map_mul, ← pow_two, quadraticChar_sq_one']

/--
theorem `quadraticChar_dichotomy` / 定理 `quadraticChar_dichotomy`

English:
theorem quadraticChar_dichotomy
  given: {a : F} (ha : a != 0)
  proof: sq_eq_one_iff.1 quadraticChar_sq_one ha

中文:
定理 quadraticChar_dichotomy
  条件: {a : F} (ha : a != 0)
  证明: sq_eq_one_iff.1 quadraticChar_sq_one ha

Depends on / 依赖: quadraticChar_sq_one, sq_eq_one_iff
-/
theorem quadraticChar_dichotomy {a : F} (ha : a != 0) :
    quadraticChar F a = 1 ∨ quadraticChar F a = -1 :=
sq_eq_one_iff.1 quadraticChar_sq_one ha

/--
theorem `quadraticChar_eq_neg_one_iff_not_one` / 定理 `quadraticChar_eq_neg_one_iff_not_one`

English:
theorem quadraticChar_eq_neg_one_iff_not_one
  given: {a : F} (ha : a != 0)
  proof: ⟨fun h => by rw [h]; lia, fun h₂ => (or_iff_right h₂).mp (quadraticChar_dichotomy ha)⟩

中文:
定理 quadraticChar_eq_neg_one_iff_not_one
  条件: {a : F} (ha : a != 0)
  证明: ⟨fun h => by rw [h]; lia, fun h₂ => (or_iff_right h₂).mp (quadraticChar_dichotomy ha)⟩

Depends on / 依赖: or_iff_right, quadraticChar_dichotomy
-/
theorem quadraticChar_eq_neg_one_iff_not_one {a : F} (ha : a != 0) :
    quadraticChar F a = -1 ↔ ¬quadraticChar F a = 1 :=
  ⟨fun h => by rw [h]; lia, fun h₂ => (or_iff_right h₂).mp (quadraticChar_dichotomy ha)⟩

/--
theorem `quadraticChar_neg_one_iff_not_isSquare` / 定理 `quadraticChar_neg_one_iff_not_isSquare`

English:
theorem quadraticChar_neg_one_iff_not_isSquare
  given: {a : F}
  statement: quadraticChar F a = -1 ↔ ¬IsSquare a
  proof: by
  by_cases ha : a = 0
  · simp only [ha, MulChar.map_zero, zero_eq_neg, one_ne_zero, IsSquare.zero, not_true]
  · rw [quadraticChar_eq_neg_one_iff_not_one ha, quadraticChar_one_iff_isSquare ha]

中文:
定理 quadraticChar_neg_one_iff_not_isSquare
  条件: {a : F}
  结论: quadraticChar F a = -1 ↔ ¬IsSquare a
  证明: by
  by_cases ha : a = 0
  · simp only [ha, MulChar.map_zero, zero_eq_neg, one_ne_zero, IsSquare.zero, not_true]
  · rw [quadraticChar_eq_neg_one_iff_not_one ha, quadraticChar_one_iff_isSquare ha]

Depends on / 依赖: IsSquare, IsSquare.zero, MulChar, MulChar.map_zero, map_zero, not_true, one_ne_zero, quadraticChar_eq_neg_one_iff_not_one, quadraticChar_one_iff_isSquare, zero_eq_neg
-/
theorem quadraticChar_neg_one_iff_not_isSquare {a : F} : quadraticChar F a = -1 ↔ ¬IsSquare a := by
  by_cases ha : a = 0
  · simp only [ha, MulChar.map_zero, zero_eq_neg, one_ne_zero, IsSquare.zero, not_true]
  · rw [quadraticChar_eq_neg_one_iff_not_one ha, quadraticChar_one_iff_isSquare ha]

/--
theorem `quadraticChar_exists_neg_one` / 定理 `quadraticChar_exists_neg_one`

English:
theorem quadraticChar_exists_neg_one
  given: (hF : ringChar F != 2)
  statement: exists a, quadraticChar F a = -1
  proof: (FiniteField.exists_nonsquare hF).imp fun _ h₁ => quadraticChar_neg_one_iff_not_isSquare.mpr h₁

中文:
定理 quadraticChar_存在_neg_one
  条件: (hF : ringChar F != 2)
  结论: 存在 a, quadraticChar F a = -1
  证明: (FiniteField.exists_nonsquare hF).imp fun _ h₁ => quadraticChar_neg_one_iff_not_isSquare.mpr h₁

Depends on / 依赖: FiniteField, FiniteField.exists_nonsquare, exists_nonsquare, quadraticChar_neg_one_iff_not_isSquare, quadraticChar_neg_one_iff_not_isSquare.mpr
-/
theorem quadraticChar_exists_neg_one (hF : ringChar F != 2) : exists a, quadraticChar F a = -1 :=
  (FiniteField.exists_nonsquare hF).imp fun _ h₁ => quadraticChar_neg_one_iff_not_isSquare.mpr h₁

/--
lemma `quadraticChar_exists_neg_one'` / 引理 `quadraticChar_exists_neg_one'`

English:
lemma quadraticChar_exists_neg_one'
  given: (hF : ringChar F != 2)
  statement: exists a : Fˣ, quadraticChar F a = -1
  proof: by
  refine (fun ⟨a, ha⟩ => ⟨IsUnit.unit ?_, ha⟩) (quadraticChar_exists_neg_one hF)
  contrapose ha
  exact ne_of_eq_of_ne ((quadraticChar F).map_nonunit ha) (mt zero_eq_neg.mp one_ne_zero)

中文:
引理 quadraticChar_存在_neg_one'
  条件: (hF : ringChar F != 2)
  结论: 存在 a : Fˣ, quadraticChar F a = -1
  证明: by
  refine (fun ⟨a, ha⟩ => ⟨IsUnit.unit ?_, ha⟩) (quadraticChar_exists_neg_one hF)
  contrapose ha
  exact ne_of_eq_of_ne ((quadraticChar F).map_nonunit ha) (mt zero_eq_neg.mp one_ne_zero)

Depends on / 依赖: IsUnit, IsUnit.unit, contrapose, map_nonunit, ne_of_eq_of_ne, one_ne_zero, quadraticChar, quadraticChar_exists_neg_one, zero_eq_neg, zero_eq_neg.mp
-/
lemma quadraticChar_exists_neg_one' (hF : ringChar F != 2) : exists a : Fˣ, quadraticChar F a = -1 := by
  refine (fun ⟨a, ha⟩ => ⟨IsUnit.unit ?_, ha⟩) (quadraticChar_exists_neg_one hF)
  contrapose ha
  exact ne_of_eq_of_ne ((quadraticChar F).map_nonunit ha) (mt zero_eq_neg.mp one_ne_zero)

/--
theorem `quadraticChar_eq_one_of_char_two` / 定理 `quadraticChar_eq_one_of_char_two`

English:
theorem quadraticChar_eq_one_of_char_two
  given: (hF : ringChar F = 2) {a : F} (ha : a != 0)
  proof: quadraticCharFun_eq_one_of_char_two hF ha

中文:
定理 quadraticChar_eq_one_of_char_two
  条件: (hF : ringChar F = 2) {a : F} (ha : a != 0)
  证明: quadraticCharFun_eq_one_of_char_two hF ha

Depends on / 依赖: quadraticCharFun_eq_one_of_char_two
-/
theorem quadraticChar_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a != 0) :
    quadraticChar F a = 1 :=
  quadraticCharFun_eq_one_of_char_two hF ha

/--
theorem `quadraticChar_eq_pow_of_char_ne_two` / 定理 `quadraticChar_eq_pow_of_char_ne_two`

English:
theorem quadraticChar_eq_pow_of_char_ne_two
  given: (hF : ringChar F != 2) {a : F} (ha : a != 0)
  proof: quadraticCharFun_eq_pow_of_char_ne_two hF ha

中文:
定理 quadraticChar_eq_pow_of_char_ne_two
  条件: (hF : ringChar F != 2) {a : F} (ha : a != 0)
  证明: quadraticCharFun_eq_pow_of_char_ne_two hF ha

Depends on / 依赖: quadraticCharFun_eq_pow_of_char_ne_two
-/
theorem quadraticChar_eq_pow_of_char_ne_two (hF : ringChar F != 2) {a : F} (ha : a != 0) :
    quadraticChar F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 :=
  quadraticCharFun_eq_pow_of_char_ne_two hF ha

/--
theorem `quadraticChar_eq_pow_of_char_ne_two'` / 定理 `quadraticChar_eq_pow_of_char_ne_two'`

English:
theorem quadraticChar_eq_pow_of_char_ne_two'
  given: (hF : ringChar F != 2) (a : F)
  proof: by
  by_cases ha : a = 0
  · have : 0 < Fintype.card F / 2 := Nat.div_pos Fintype.one_lt_card two_pos
    simp only [ha, quadraticChar_apply, quadraticCharFun_zero, Int.cast_zero, zero_pow this.ne']
  · rw [quadraticChar_eq_pow_of_char_ne_two hF ha]
    by_cases ha' : a ^ (Fintype.card F / 2) = 1
  

中文:
定理 quadraticChar_eq_pow_of_char_ne_two'
  条件: (hF : ringChar F != 2) (a : F)
  证明: by
  by_cases ha : a = 0
  · have : 0 < Fintype.card F / 2 := Nat.div_pos Fintype.one_lt_card two_pos
    simp only [ha, quadraticChar_apply, quadraticCharFun_zero, Int.cast_zero, zero_pow this.ne']
  · rw [quadraticChar_eq_pow_of_char_ne_two hF ha]
    by_cases ha' : a ^ (Fintype.card F / 2) = 1
  

Depends on / 依赖: Eq.symm, FiniteField, FiniteField.pow_dichotomy, Fintype, Fintype.card, Fintype.one_lt_card, Int.cast_ite, Int.cast_neg, Int.cast_one, Int.cast_zero, Nat.div_pos, Or.resolve_left, cast_ite, cast_neg, cast_one, cast_zero, div_pos, if_true, ite_eq_right_iff, one_lt_card
-/
theorem quadraticChar_eq_pow_of_char_ne_two' (hF : ringChar F != 2) (a : F) :
    (quadraticChar F a : F) = a ^ (Fintype.card F / 2) := by
  by_cases ha : a = 0
  · have : 0 < Fintype.card F / 2 := Nat.div_pos Fintype.one_lt_card two_pos
    simp only [ha, quadraticChar_apply, quadraticCharFun_zero, Int.cast_zero, zero_pow this.ne']
  · rw [quadraticChar_eq_pow_of_char_ne_two hF ha]
    by_cases ha' : a ^ (Fintype.card F / 2) = 1
    · simp only [ha', if_true, Int.cast_one]
    · have ha'' := Or.resolve_left (FiniteField.pow_dichotomy hF ha) ha'
      simp only [ha'', Int.cast_ite, Int.cast_one, Int.cast_neg, ite_eq_right_iff]
      exact Eq.symm

variable (F) in
/--
theorem `quadraticChar_isQuadratic` / 定理 `quadraticChar_isQuadratic`

English:
theorem quadraticChar_isQuadratic
  statement: (quadraticChar F).IsQuadratic
  proof: by
  intro a
  by_cases ha : a = 0
  · left; rw [ha]; exact quadraticChar_zero
  · right; exact quadraticChar_dichotomy ha

中文:
定理 quadraticChar_isQuadratic
  结论: (quadraticChar F).IsQuadratic
  证明: by
  intro a
  by_cases ha : a = 0
  · left; rw [ha]; exact quadraticChar_zero
  · right; exact quadraticChar_dichotomy ha

Depends on / 依赖: quadraticChar_dichotomy, quadraticChar_zero
-/
theorem quadraticChar_isQuadratic : (quadraticChar F).IsQuadratic := by
  intro a
  by_cases ha : a = 0
  · left; rw [ha]; exact quadraticChar_zero
  · right; exact quadraticChar_dichotomy ha

/--
theorem `quadraticChar_ne_one` / 定理 `quadraticChar_ne_one`

English:
theorem quadraticChar_ne_one
  given: (hF : ringChar F != 2)
  statement: quadraticChar F != 1
  proof: by
  rcases quadraticChar_exists_neg_one' hF with ⟨a, ha⟩
  intro hχ
  simp only [hχ, one_apply a.isUnit, reduceCtorEq] at ha

中文:
定理 quadraticChar_ne_one
  条件: (hF : ringChar F != 2)
  结论: quadraticChar F != 1
  证明: by
  rcases quadraticChar_exists_neg_one' hF with ⟨a, ha⟩
  intro hχ
  simp only [hχ, one_apply a.isUnit, reduceCtorEq] at ha

Depends on / 依赖: a.isUnit, isUnit, one_apply, quadraticChar_exists_neg_one, reduceCtorEq
-/
theorem quadraticChar_ne_one (hF : ringChar F != 2) : quadraticChar F != 1 := by
  rcases quadraticChar_exists_neg_one' hF with ⟨a, ha⟩
  intro hχ
  simp only [hχ, one_apply a.isUnit, reduceCtorEq] at ha

open Finset in
/--
theorem `quadraticChar_card_sqrts` / 定理 `quadraticChar_card_sqrts`

English:
theorem quadraticChar_card_sqrts
  given: (hF : ringChar F != 2) (a : F)
  proof: by
  -- we consider the cases `a = 0`, `a` is a nonzero square and `a` is a nonsquare in turn
  by_cases h₀ : a = 0
  · simp only [h₀, sq_eq_zero_iff, Set.ofPred_eq_eq_singleton, Set.toFinset_card,
    Set.card_singleton, Int.natCast_succ, Int.ofNat_zero, MulChar.map_zero]
  · set s := {x : F | x ^ 

中文:
定理 quadraticChar_card_sqrts
  条件: (hF : ringChar F != 2) (a : F)
  证明: by
  -- we consider the cases `a = 0`, `a` is a nonzero square and `a` is a nonsquare in turn
  by_cases h₀ : a = 0
  · simp only [h₀, sq_eq_zero_iff, Set.ofPred_eq_eq_singleton, Set.toFinset_card,
    Set.card_singleton, Int.natCast_succ, Int.ofNat_zero, MulChar.map_zero]
  · set s := {x : F | x ^ 
-/
theorem quadraticChar_card_sqrts (hF : ringChar F != 2) (a : F) :
    #{x : F | x ^ 2 = a}.toFinset = quadraticChar F a + 1 := by
  -- we consider the cases `a = 0`, `a` is a nonzero square and `a` is a nonsquare in turn
  by_cases h₀ : a = 0
  · simp only [h₀, sq_eq_zero_iff, Set.ofPred_eq_eq_singleton, Set.toFinset_card,
    Set.card_singleton, Int.natCast_succ, Int.ofNat_zero, MulChar.map_zero]
  · set s := {x : F | x ^ 2 = a}.toFinset
    by_cases h : IsSquare a
    · rw [(quadraticChar_one_iff_isSquare h₀).mpr h]
      rcases h with ⟨b, h⟩
      rw [h]; rw [mul_self_eq_zero] at h₀
      have h₁ : s = [b, -b].toFinset := by
        ext1
        rw [← pow_two] at h
        simp_rw [s, Set.toFinset_ofPred, mem_filter_univ, h, List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, mem_insert, mem_singleton]
        exact sq_eq_sq_iff_eq_or_eq_neg
      norm_cast
      rw [h₁]; rw [List.toFinset_cons]; rw [List.toFinset_cons]; rw [List.toFinset_nil]
      exact card_pair (Ne.symm (mt (Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h₀))
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr h]
      simp only [neg_add_cancel, Int.natCast_eq_zero, card_eq_zero, eq_empty_iff_forall_notMem]
      simpa [s, isSquare_iff_exists_sq, eq_comm] using h

/--
theorem `quadraticChar_sum_zero` / 定理 `quadraticChar_sum_zero`

English:
theorem quadraticChar_sum_zero
  given: (hF : ringChar F != 2)
  statement: ∑ a : F, quadraticChar F a = 0
  proof: sum_eq_zero_of_ne_one (quadraticChar_ne_one hF)

中文:
定理 quadraticChar_sum_zero
  条件: (hF : ringChar F != 2)
  结论: ∑ a : F, quadraticChar F a = 0
  证明: sum_eq_zero_of_ne_one (quadraticChar_ne_one hF)

Depends on / 依赖: quadraticChar_ne_one, sum_eq_zero_of_ne_one
-/
theorem quadraticChar_sum_zero (hF : ringChar F != 2) : ∑ a : F, quadraticChar F a = 0 :=
  sum_eq_zero_of_ne_one (quadraticChar_ne_one hF)

end quadraticChar

/-!
### Special values of the quadratic character

We express `quadraticChar F (-1)` in terms of `χ₄`.
-/


section SpecialValues

open ZMod MulChar

variable {F : Type*} [Field F] [Fintype F]

/--
theorem `quadraticChar_neg_one` / 定理 `quadraticChar_neg_one`

English:
theorem quadraticChar_neg_one
  given: [DecidableEq F] (hF : ringChar F != 2)
  proof: by
  have h := quadraticChar_eq_pow_of_char_ne_two hF (neg_ne_zero.mpr one_ne_zero)
  rw [h]; rw [χ₄_eq_neg_one_pow (FiniteField.odd_card_of_char_ne_two hF)]
  generalize Fintype.card F / 2 = n
  rcases Nat.even_or_odd n with h₂ | h₂
  · simp only [Even.neg_one_pow h₂, if_true]
  · simp only [Odd.ne

中文:
定理 quadraticChar_neg_one
  条件: [DecidableEq F] (hF : ringChar F != 2)
  证明: by
  have h := quadraticChar_eq_pow_of_char_ne_two hF (neg_ne_zero.mpr one_ne_zero)
  rw [h]; rw [χ₄_eq_neg_one_pow (FiniteField.odd_card_of_char_ne_two hF)]
  generalize Fintype.card F / 2 = n
  rcases Nat.even_or_odd n with h₂ | h₂
  · simp only [Even.neg_one_pow h₂, if_true]
  · simp only [Odd.ne

Depends on / 依赖: Even.neg_one_pow, FiniteField, FiniteField.odd_card_of_char_ne_two, Fintype, Fintype.card, Nat.even_or_odd, Odd.neg_one_pow, Ring.neg_one_ne_one_of_char_ne_two, even_or_odd, generalize, if_true, ite_false, neg_ne_zero, neg_ne_zero.mpr, neg_one_ne_one_of_char_ne_two, neg_one_pow, odd_card_of_char_ne_two, one_ne_zero, quadraticChar_eq_pow_of_char_ne_two
-/
theorem quadraticChar_neg_one [DecidableEq F] (hF : ringChar F != 2) :
    quadraticChar F (-1) = χ₄ (Fintype.card F) := by
  have h := quadraticChar_eq_pow_of_char_ne_two hF (neg_ne_zero.mpr one_ne_zero)
  rw [h]; rw [χ₄_eq_neg_one_pow (FiniteField.odd_card_of_char_ne_two hF)]
  generalize Fintype.card F / 2 = n
  rcases Nat.even_or_odd n with h₂ | h₂
  · simp only [Even.neg_one_pow h₂, if_true]
  · simp only [Odd.neg_one_pow h₂, Ring.neg_one_ne_one_of_char_ne_two hF, ite_false]

/--
theorem `FiniteField.isSquare_neg_one_iff` / 定理 `FiniteField.isSquare_neg_one_iff`

English:
theorem FiniteField.isSquare_neg_one_iff
  statement: IsSquare (-1 : F) ↔ Fintype.card F % 4 != 3
  proof: by
  classical -- suggested by the linter (instead of `[DecidableEq F]`)
  by_cases hF : ringChar F = 2
  · simp only [FiniteField.isSquare_of_char_two hF, Ne, true_iff]
    exact fun hf =>
one_ne_zero
(Nat.odd_of_mod_four_eq_three hf).symm.trans FiniteField.even_card_of_char_two hF
  · have h₁ := F

中文:
定理 FiniteField.isSquare_neg_one_iff
  结论: IsSquare (-1 : F) ↔ 有限类型.card F % 4 != 3
  证明: by
  classical -- suggested by the linter (instead of `[DecidableEq F]`)
  by_cases hF : ringChar F = 2
  · simp only [FiniteField.isSquare_of_char_two hF, Ne, true_iff]
    exact fun hf =>
one_ne_zero
(Nat.odd_of_mod_four_eq_three hf).symm.trans FiniteField.even_card_of_char_two hF
  · have h₁ := F

Depends on / 依赖: DecidableEq, FiniteField, FiniteField.even_card_of_char_two, FiniteField.isSquare_of_char_two, FiniteField.odd_card_of_char_ne_two, Nat.odd_of_mod_four_eq_three, classical, even_card_of_char_two, instead, isSquare_of_char_two, linter, neg_ne_zero, neg_ne_zero.mpr, odd_card_of_char_ne_two, odd_of_mod_four_eq_three, one_ne_zero, quadraticChar_neg_one, quadraticChar_one_iff_isSquare, ringChar, suggested
-/
theorem FiniteField.isSquare_neg_one_iff : IsSquare (-1 : F) ↔ Fintype.card F % 4 != 3 := by
  classical -- suggested by the linter (instead of `[DecidableEq F]`)
  by_cases hF : ringChar F = 2
  · simp only [FiniteField.isSquare_of_char_two hF, Ne, true_iff]
    exact fun hf =>
one_ne_zero
(Nat.odd_of_mod_four_eq_three hf).symm.trans FiniteField.even_card_of_char_two hF
  · have h₁ := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (one_ne_zero' F))]; rw [quadraticChar_neg_one hF]; rw [χ₄_nat_eq_if_mod_four]; rw [h₁]
    lia

end SpecialValues
