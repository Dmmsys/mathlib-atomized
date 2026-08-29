/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.Algebra.CharP.CharAndCard

import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Gauss sums

We define the Gauss sum associated to a multiplicative and an additive
character of a finite field and prove some results about them.

## Main definition

Let `R` be a finite commutative ring and let `R'` be another commutative ring.
If `χ` is a multiplicative character `R → R'` (type `MulChar R R'`) and `ψ`
is an additive character `R → R'` (type `AddChar R R'`, which abbreviates
`(Multiplicative R) →* R'`), then the *Gauss sum* of `χ` and `ψ` is `∑ a, χ a * ψ a`.

## Main results

Some important results are as follows.

* `gaussSum_mul_gaussSum_eq_card`: The product of the Gauss
  sums of `χ` and `ψ` and that of `χ⁻¹` and `ψ⁻¹` is the cardinality
  of the source ring `R` (if `χ` is nontrivial, `ψ` is primitive and `R` is a field).
* `gaussSum_sq`: The square of the Gauss sum is `χ(-1)` times
  the cardinality of `R` if in addition `χ` is a quadratic character.
* `MulChar.IsQuadratic.gaussSum_frob`: For a quadratic character `χ`, raising
  the Gauss sum to the `p`th power (where `p` is the characteristic of
  the target ring `R'`) multiplies it by `χ p`.
* `Char.card_pow_card`: When `F` and `F'` are finite fields and `χ : F → F'`
  is a nontrivial quadratic character, then `(χ (-1) * #F)^(#F'/2) = χ #F'`.
* `FiniteField.two_pow_card`: For every finite field `F` of odd characteristic,
  we have `2^(#F/2) = χ₈ #F` in `F`.

This machinery can be used to derive (a generalization of) the Law of
Quadratic Reciprocity.

## Tags

additive character, multiplicative character, Gauss sum
-/

@[expose] public section


universe u v

open AddChar MulChar

section GaussSumDef

-- `R` is the domain of the characters
variable {R : Type u} [CommRing R] [Fintype R]

-- `R'` is the target of the characters
variable {R' : Type v} [CommRing R']

/-!
### Definition and first properties
-/

/--
Definition of `gaussSum` / `gaussSum` 的定义

English:
definition gaussSum
  signature: (χ : MulChar R R') (ψ : AddChar R R')
  body: ∑ a, χ a * ψ a

中文:
定义 gaussSum
  签名: (χ : 乘法特征 R R') (ψ : 加法特征 R R')
  定义体: ∑ a, χ a * ψ a
-/
def gaussSum (χ : MulChar R R') (ψ : AddChar R R') : R' :=
  ∑ a, χ a * ψ a

/--
theorem `gaussSum_mulShift` / 定理 `gaussSum_mulShift`

English:
theorem gaussSum_mulShift
  given: (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ)
  proof: by
  simp only [gaussSum, mulShift_apply, Finset.mul_sum]
  simp_rw [← mul_assoc, ← map_mul]
  exact Fintype.sum_bijective _ a.mulLeft_bijective _ _ fun x => rfl

中文:
定理 gaussSum_mulShift
  条件: (χ : 乘法特征 R R') (ψ : 加法特征 R R') (a : Rˣ)
  证明: by
  simp only [gaussSum, mulShift_apply, Finset.mul_sum]
  simp_rw [← mul_assoc, ← map_mul]
  exact Fintype.sum_bijective _ a.mulLeft_bijective _ _ fun x => rfl

Depends on / 依赖: Finset, Finset.mul_sum, Fintype, Fintype.sum_bijective, a.mulLeft_bijective, gaussSum, map_mul, mulLeft_bijective, mulShift_apply, mul_assoc, mul_sum, simp_rw, sum_bijective
-/
theorem gaussSum_mulShift (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ) :
    χ a * gaussSum χ (mulShift ψ a) = gaussSum χ ψ := by
  simp only [gaussSum, mulShift_apply, Finset.mul_sum]
  simp_rw [← mul_assoc, ← map_mul]
  exact Fintype.sum_bijective _ a.mulLeft_bijective _ _ fun x => rfl

/--
theorem `gaussSum_mulShift_eq` / 定理 `gaussSum_mulShift_eq`

English:
theorem gaussSum_mulShift_eq
  given: (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ)
  proof: by
  rw [← gaussSum_mulShift χ ψ a]; rw [inv_apply_eq_inv]; rw [Ring.inverse_mul_cancel_left _ _ (a.isUnit.map χ)]

中文:
定理 gaussSum_mulShift_eq
  条件: (χ : 乘法特征 R R') (ψ : 加法特征 R R') (a : Rˣ)
  证明: by
  rw [← gaussSum_mulShift χ ψ a]; rw [inv_apply_eq_inv]; rw [Ring.inverse_mul_cancel_left _ _ (a.isUnit.map χ)]

Depends on / 依赖: Ring.inverse_mul_cancel_left, a.isUnit.map, gaussSum_mulShift, inv_apply_eq_inv, inverse_mul_cancel_left, isUnit
-/
theorem gaussSum_mulShift_eq (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  rw [← gaussSum_mulShift χ ψ a]; rw [inv_apply_eq_inv]; rw [Ring.inverse_mul_cancel_left _ _ (a.isUnit.map χ)]

/--
lemma `star_gaussSum_eq` / 引理 `star_gaussSum_eq`

English:
lemma star_gaussSum_eq
  given: (χ : MulChar R Complex) (ψ : AddChar R Complex)
  proof: calc
    _ = ∑ x, star (ψ x) * χ⁻¹ x := by simp [gaussSum, star_mul, MulChar.star_apply']
    _ = ∑ x, ψ⁻¹ x * χ⁻¹ x := by simp [← starRingEnd_apply, map_neg_eq_conj]
    _ = _ := by simp [mul_comm, gaussSum]

中文:
引理 star_gaussSum_eq
  条件: (χ : 乘法特征 R 复形) (ψ : 加法特征 R 复形)
  证明: calc
    _ = ∑ x, star (ψ x) * χ⁻¹ x := by simp [gaussSum, star_mul, MulChar.star_apply']
    _ = ∑ x, ψ⁻¹ x * χ⁻¹ x := by simp [← starRingEnd_apply, map_neg_eq_conj]
    _ = _ := by simp [mul_comm, gaussSum]

Depends on / 依赖: MulChar, MulChar.star_apply, gaussSum, map_neg_eq_conj, mul_comm, starRingEnd_apply, star_apply, star_mul
-/
lemma star_gaussSum_eq (χ : MulChar R Complex) (ψ : AddChar R Complex) :
    star (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ :=
  calc
    _ = ∑ x, star (ψ x) * χ⁻¹ x := by simp [gaussSum, star_mul, MulChar.star_apply']
    _ = ∑ x, ψ⁻¹ x * χ⁻¹ x := by simp [← starRingEnd_apply, map_neg_eq_conj]
    _ = _ := by simp [mul_comm, gaussSum]

end GaussSumDef

/-!
### Gauss sums of trivial characters
-/

section GaussSumTrivial

variable {R R' : Type*} [CommRing R] [Fintype R] [CommRing R']

/-- The Gauss sum of the two trivial characters is the cardinality of the unit group of `R`. -/
@[simp]
/--
theorem `gaussSum_one_one` / 定理 `gaussSum_one_one`

English:
theorem gaussSum_one_one
  statement: gaussSum (1 : MulChar R R') (1 : AddChar R R') = Nat.card Rˣ
  proof: by
  classical
  simp [gaussSum, MulChar.sum_one_eq_card_units]

中文:
定理 gaussSum_one_one
  结论: gaussSum (1 : 乘法特征 R R') (1 : 加法特征 R R') = 自然数.card Rˣ
  证明: by
  classical
  simp [gaussSum, MulChar.sum_one_eq_card_units]

Depends on / 依赖: MulChar, MulChar.sum_one_eq_card_units, classical, gaussSum, sum_one_eq_card_units
-/
theorem gaussSum_one_one : gaussSum (1 : MulChar R R') (1 : AddChar R R') = Nat.card Rˣ := by
  classical
  simp [gaussSum, MulChar.sum_one_eq_card_units]

/--
theorem `gaussSum_one_right` / 定理 `gaussSum_one_right`

English:
theorem gaussSum_one_right
  given: [IsDomain R'] {χ : MulChar R R'} (hχ : χ != 1)
  proof: by
  simpa [gaussSum] using MulChar.sum_eq_zero_of_ne_one hχ

中文:
定理 gaussSum_one_right
  条件: [是整环 R'] {χ : 乘法特征 R R'} (hχ : χ != 1)
  证明: by
  simpa [gaussSum] using MulChar.sum_eq_zero_of_ne_one hχ

Depends on / 依赖: MulChar, MulChar.sum_eq_zero_of_ne_one, gaussSum, sum_eq_zero_of_ne_one
-/
theorem gaussSum_one_right [IsDomain R'] {χ : MulChar R R'} (hχ : χ != 1) :
    gaussSum χ (1 : AddChar R R') = 0 := by
  simpa [gaussSum] using MulChar.sum_eq_zero_of_ne_one hχ

end GaussSumTrivial

section GaussSumTrivialField

variable {R R' : Type*} [Field R] [Fintype R] [CommRing R'] [IsDomain R']

/--
theorem `gaussSum_one_left` / 定理 `gaussSum_one_left`

English:
theorem gaussSum_one_left
  given: {ψ : AddChar R R'} (hψ : ψ != 1)
  proof: by
  classical
  simp only [gaussSum, ← add_eq_zero_iff_eq_neg]
  calc ∑ a, (1 : MulChar R R') a * ψ a + 1
  _ = ∑ a in {0}ᶜ, (1 : MulChar R R') a * ψ a + 1 := by
    simp [← ({0} : Finset R).sum_compl_add_sum]
  _ = ∑ a in {0}ᶜ, ψ a + ψ 0 := by
    congr! <;> aesop (add simp MulChar.one_apply)
  _ = 0 := by
    rw [← AddChar.sum_eq_zero_of_ne_one hψ]; rw [← Finset.sum_compl_add_sum (s := {0})]
    simp

中文:
定理 gaussSum_one_left
  条件: {ψ : 加法特征 R R'} (hψ : ψ != 1)
  证明: by
  classical
  simp only [gaussSum, ← add_eq_zero_iff_eq_neg]
  calc ∑ a, (1 : MulChar R R') a * ψ a + 1
  _ = ∑ a in {0}ᶜ, (1 : MulChar R R') a * ψ a + 1 := by
    simp [← ({0} : Finset R).sum_compl_add_sum]
  _ = ∑ a in {0}ᶜ, ψ a + ψ 0 := by
    congr! <;> aesop (add simp MulChar.one_apply)
  _ = 0 := by
    rw [← AddChar.sum_eq_zero_of_ne_one hψ]; rw [← Finset.sum_compl_add_sum (s := {0})]
    simp

Depends on / 依赖: AddChar, AddChar.sum_eq_zero_of_ne_one, Finset, Finset.sum_compl_add_sum, MulChar, MulChar.one_apply, add_eq_zero_iff_eq_neg, classical, gaussSum, one_apply, sum_compl_add_sum, sum_eq_zero_of_ne_one
-/
theorem gaussSum_one_left {ψ : AddChar R R'} (hψ : ψ != 1) :
    gaussSum (1 : MulChar R R') ψ = -1 := by
  classical
  simp only [gaussSum, ← add_eq_zero_iff_eq_neg]
  calc ∑ a, (1 : MulChar R R') a * ψ a + 1
  _ = ∑ a in {0}ᶜ, (1 : MulChar R R') a * ψ a + 1 := by
    simp [← ({0} : Finset R).sum_compl_add_sum]
  _ = ∑ a in {0}ᶜ, ψ a + ψ 0 := by
    congr! <;> aesop (add simp MulChar.one_apply)
  _ = 0 := by
    rw [← AddChar.sum_eq_zero_of_ne_one hψ]; rw [← Finset.sum_compl_add_sum (s := {0})]
    simp

end GaussSumTrivialField

/-!
### The product of two Gauss sums
-/

section GaussSumProd

open Finset in
/--
lemma `gaussSum_mul` / 引理 `gaussSum_mul`

English:
lemma gaussSum_mul
  statement: {R : Type u} [CommRing R] [Fintype R] {R' : Type v} [CommRing R']
  proof: by
  rw [gaussSum]; rw [gaussSum]; rw [sum_mul_sum]
  conv => enter [1, 2, x, 2, x_1]; rw [mul_mul_mul_comm]
  simp only [← ψ.map_add_eq_mul]
  have sum_eq x : ∑ y : R, χ x * φ y * ψ (x + y) = ∑ y : R, χ x * φ (y - x) * ψ y := by
    rw [sum_bij (fun a _ => a + x)]
    · simp only [mem_univ, forall_const]
    · simp only [mem_univ, add_left_inj, imp_self, forall_const]
    · exact fun b _ => ⟨b - x, mem_univ _, by rw [sub_add_cancel]⟩
    · exact fun a _ => by rw [add_sub_cancel_right, add_comm]
  rw [sum_congr rfl fun x _ => sum_eq x]; rw [sum_comm]

中文:
引理 gaussSum_mul
  结论: {R : 类型u} [交换环 R] [有限类型 R] {R' : 类型v} [交换环 R']
  证明: by
  rw [gaussSum]; rw [gaussSum]; rw [sum_mul_sum]
  conv => enter [1, 2, x, 2, x_1]; rw [mul_mul_mul_comm]
  simp only [← ψ.map_add_eq_mul]
  have sum_eq x : ∑ y : R, χ x * φ y * ψ (x + y) = ∑ y : R, χ x * φ (y - x) * ψ y := by
    rw [sum_bij (fun a _ => a + x)]
    · simp only [mem_univ, forall_const]
    · simp only [mem_univ, add_left_inj, imp_self, forall_const]
    · exact fun b _ => ⟨b - x, mem_univ _, by rw [sub_add_cancel]⟩
    · exact fun a _ => by rw [add_sub_cancel_right, add_comm]
  rw [sum_congr rfl fun x _ => sum_eq x]; rw [sum_comm]

Depends on / 依赖: add_comm, add_left_inj, add_sub_cancel_right, forall_const, gaussSum, imp_self, map_add_eq_mul, mem_univ, mul_mul_mul_comm, sub_add_cancel, sum_bij, sum_congr, sum_eq, sum_mul_sum
-/
lemma gaussSum_mul {R : Type u} [CommRing R] [Fintype R] {R' : Type v} [CommRing R']
    (χ φ : MulChar R R') (ψ : AddChar R R') :
    gaussSum χ ψ * gaussSum φ ψ = ∑ t : R, ∑ x : R, χ x * φ (t - x) * ψ t := by
  rw [gaussSum]; rw [gaussSum]; rw [sum_mul_sum]
  conv => enter [1, 2, x, 2, x_1]; rw [mul_mul_mul_comm]
  simp only [← ψ.map_add_eq_mul]
  have sum_eq x : ∑ y : R, χ x * φ y * ψ (x + y) = ∑ y : R, χ x * φ (y - x) * ψ y := by
    rw [sum_bij (fun a _ => a + x)]
    · simp only [mem_univ, forall_const]
    · simp only [mem_univ, add_left_inj, imp_self, forall_const]
    · exact fun b _ => ⟨b - x, mem_univ _, by rw [sub_add_cancel]⟩
    · exact fun a _ => by rw [add_sub_cancel_right, add_comm]
  rw [sum_congr rfl fun x _ => sum_eq x]; rw [sum_comm]

-- In the following, we need `R` to be a finite field.
variable {R : Type u} [Field R] [Fintype R] {R' : Type v} [CommRing R']

/--
lemma `mul_gaussSum_inv_eq_gaussSum` / 引理 `mul_gaussSum_inv_eq_gaussSum`

English:
lemma mul_gaussSum_inv_eq_gaussSum
  given: (χ : MulChar R R') (ψ : AddChar R R')
  proof: by
  rw [ψ.inv_mulShift]; rw [← Units.coe_neg_one]
  exact gaussSum_mulShift χ ψ (-1)

中文:
引理 mul_gaussSum_inv_eq_gaussSum
  条件: (χ : 乘法特征 R R') (ψ : 加法特征 R R')
  证明: by
  rw [ψ.inv_mulShift]; rw [← Units.coe_neg_one]
  exact gaussSum_mulShift χ ψ (-1)

Depends on / 依赖: Units.coe_neg_one, coe_neg_one, gaussSum_mulShift, inv_mulShift
-/
lemma mul_gaussSum_inv_eq_gaussSum (χ : MulChar R R') (ψ : AddChar R R') :
    χ (-1) * gaussSum χ ψ⁻¹ = gaussSum χ ψ := by
  rw [ψ.inv_mulShift]; rw [← Units.coe_neg_one]
  exact gaussSum_mulShift χ ψ (-1)

variable [IsDomain R'] -- From now on, `R'` needs to be a domain.

-- A helper lemma for `gaussSum_mul_gaussSum_eq_card` below
-- Is this useful enough in other contexts to be public?
/--
theorem `gaussSum_mul_aux` / 定理 `gaussSum_mul_aux`

English:
theorem gaussSum_mul_aux
  statement: {χ : MulChar R R'} (hχ : χ != 1) (ψ : AddChar R R')
  proof: by
  rcases eq_or_ne b 0 with hb | hb
  · -- case `b = 0`
    simp only [hb, inv_zero, mul_zero, MulChar.map_zero, zero_mul,
      Finset.sum_const_zero, map_zero_eq_one, mul_one, χ.sum_eq_zero_of_ne_one hχ]
  · -- case `b ≠ 0`
    refine (Fintype.sum_bijective _ (mulLeft_bijective₀ b hb) _ _ fun x => ?_).symm
    rw [mul_assoc]; rw [mul_comm x]; rw [← mul_assoc]; rw [mul_inv_cancel₀ hb]; rw [one_mul]; rw [mul_sub]; rw [mul_one]

中文:
定理 gaussSum_mul_aux
  结论: {χ : 乘法特征 R R'} (hχ : χ != 1) (ψ : 加法特征 R R')
  证明: by
  rcases eq_or_ne b 0 with hb | hb
  · -- case `b = 0`
    simp only [hb, inv_zero, mul_zero, MulChar.map_zero, zero_mul,
      Finset.sum_const_zero, map_zero_eq_one, mul_one, χ.sum_eq_zero_of_ne_one hχ]
  · -- case `b ≠ 0`
    refine (Fintype.sum_bijective _ (mulLeft_bijective₀ b hb) _ _ fun x => ?_).symm
    rw [mul_assoc]; rw [mul_comm x]; rw [← mul_assoc]; rw [mul_inv_cancel₀ hb]; rw [one_mul]; rw [mul_sub]; rw [mul_one]
-/
private theorem gaussSum_mul_aux {χ : MulChar R R'} (hχ : χ != 1) (ψ : AddChar R R')
    (b : R) :
    ∑ a, χ (a * b⁻¹) * ψ (a - b) = ∑ c, χ c * ψ (b * (c - 1)) := by
  rcases eq_or_ne b 0 with hb | hb
  · -- case `b = 0`
    simp only [hb, inv_zero, mul_zero, MulChar.map_zero, zero_mul,
      Finset.sum_const_zero, map_zero_eq_one, mul_one, χ.sum_eq_zero_of_ne_one hχ]
  · -- case `b ≠ 0`
    refine (Fintype.sum_bijective _ (mulLeft_bijective₀ b hb) _ _ fun x => ?_).symm
    rw [mul_assoc]; rw [mul_comm x]; rw [← mul_assoc]; rw [mul_inv_cancel₀ hb]; rw [one_mul]; rw [mul_sub]; rw [mul_one]

/--
theorem `gaussSum_mul_gaussSum_eq_card` / 定理 `gaussSum_mul_gaussSum_eq_card`

English:
theorem gaussSum_mul_gaussSum_eq_card
  statement: {χ : MulChar R R'} (hχ : χ != 1) {ψ : AddChar R R'}
  proof: by
  simp only [gaussSum, AddChar.inv_apply, Finset.sum_mul, Finset.mul_sum, MulChar.inv_apply']
  conv =>
    enter [1, 2, x, 2, y]
    rw [mul_mul_mul_comm]; rw [← map_mul]; rw [← map_add_eq_mul]; rw [← sub_eq_add_neg]

中文:
定理 gaussSum_mul_gaussSum_eq_card
  结论: {χ : 乘法特征 R R'} (hχ : χ != 1) {ψ : 加法特征 R R'}
  证明: by
  simp only [gaussSum, AddChar.inv_apply, Finset.sum_mul, Finset.mul_sum, MulChar.inv_apply']
  conv =>
    enter [1, 2, x, 2, y]
    rw [mul_mul_mul_comm]; rw [← map_mul]; rw [← map_add_eq_mul]; rw [← sub_eq_add_neg]

Depends on / 依赖: AddChar, AddChar.inv_apply, Finset, Finset.mul_sum, Finset.sum_mul, MulChar, MulChar.inv_apply, gaussSum, inv_apply, map_add_eq_mul, map_mul, mul_mul_mul_comm, mul_sum, sub_eq_add_neg, sum_mul
-/
theorem gaussSum_mul_gaussSum_eq_card {χ : MulChar R R'} (hχ : χ != 1) {ψ : AddChar R R'}
    (hψ : IsPrimitive ψ) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card R := by
  simp only [gaussSum, AddChar.inv_apply, Finset.sum_mul, Finset.mul_sum, MulChar.inv_apply']
  conv =>
    enter [1, 2, x, 2, y]
    rw [mul_mul_mul_comm]; rw [← map_mul]; rw [← map_add_eq_mul]; rw [← sub_eq_add_neg]
-- conv in _ * _ * (_ * _) => rw [mul_mul_mul_comm, ← map_mul, ← map_add_eq_mul, ← sub_eq_add_neg]
  simp_rw [gaussSum_mul_aux hχ ψ]
  rw [Finset.sum_comm]
  classical -- to get `[DecidableEq R]` for `sum_mulShift`
  simp_rw [← Finset.mul_sum, sum_mulShift _ hψ, sub_eq_zero, apply_ite, Nat.cast_zero, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (1 : R)]
  simp only [Finset.mem_univ, map_one, one_mul, if_true]

/--
lemma `gaussSum_mul_gaussSum_pow_orderOf_sub_one` / 引理 `gaussSum_mul_gaussSum_pow_orderOf_sub_one`

English:
lemma gaussSum_mul_gaussSum_pow_orderOf_sub_one
  statement: {χ : MulChar R R'} {ψ : AddChar R R'}
  proof: by
  have h : χ ^ (orderOf χ - 1) = χ⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos χ.orderOf_pos]; rw [pow_orderOf_eq_one]
  rw [h]; rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹]; rw [mul_left_comm]; rw [gaussSum_mul_gaussSum_eq_card hχ hψ]; rw [MulChar.inv_apply']; rw [inv_neg_one]

中文:
引理 gaussSum_mul_gaussSum_pow_orderOf_sub_one
  结论: {χ : 乘法特征 R R'} {ψ : 加法特征 R R'}
  证明: by
  have h : χ ^ (orderOf χ - 1) = χ⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos χ.orderOf_pos]; rw [pow_orderOf_eq_one]
  rw [h]; rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹]; rw [mul_left_comm]; rw [gaussSum_mul_gaussSum_eq_card hχ hψ]; rw [MulChar.inv_apply']; rw [inv_neg_one]

Depends on / 依赖: MulChar, MulChar.inv_apply, Nat.sub_one_add_one_eq_of_pos, gaussSum_mul_gaussSum_eq_card, inv_apply, inv_eq_of_mul_eq_one_right, inv_neg_one, mul_gaussSum_inv_eq_gaussSum, mul_left_comm, orderOf, orderOf_pos, pow_orderOf_eq_one, pow_succ, sub_one_add_one_eq_of_pos
-/
lemma gaussSum_mul_gaussSum_pow_orderOf_sub_one {χ : MulChar R R'} {ψ : AddChar R R'}
    (hχ : χ != 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ ^ (orderOf χ - 1)) ψ = χ (-1) * Fintype.card R := by
  have h : χ ^ (orderOf χ - 1) = χ⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ']; rw [Nat.sub_one_add_one_eq_of_pos χ.orderOf_pos]; rw [pow_orderOf_eq_one]
  rw [h]; rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹]; rw [mul_left_comm]; rw [gaussSum_mul_gaussSum_eq_card hχ hψ]; rw [MulChar.inv_apply']; rw [inv_neg_one]

/--
lemma `gaussSum_ne_zero_of_nontrivial` / 引理 `gaussSum_ne_zero_of_nontrivial`

English:
lemma gaussSum_ne_zero_of_nontrivial
  statement: (h : (Fintype.card R : R') != 0) {χ : MulChar R R'}
  proof: fun H => h.symm zero_mul (gaussSum χ⁻¹ _) ▸ H ▸ gaussSum_mul_gaussSum_eq_card hχ hψ

中文:
引理 gaussSum_ne_zero_of_nontrivial
  结论: (h : (有限类型.card R : R') != 0) {χ : 乘法特征 R R'}
  证明: fun H => h.symm zero_mul (gaussSum χ⁻¹ _) ▸ H ▸ gaussSum_mul_gaussSum_eq_card hχ hψ

Depends on / 依赖: gaussSum, gaussSum_mul_gaussSum_eq_card, h.symm, zero_mul
-/
lemma gaussSum_ne_zero_of_nontrivial (h : (Fintype.card R : R') != 0) {χ : MulChar R R'}
    (hχ : χ != 1) {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ != 0 :=
fun H => h.symm zero_mul (gaussSum χ⁻¹ _) ▸ H ▸ gaussSum_mul_gaussSum_eq_card hχ hψ

/--
theorem `gaussSum_sq` / 定理 `gaussSum_sq`

English:
theorem gaussSum_sq
  statement: {χ : MulChar R R'} (hχ₁ : χ != 1) (hχ₂ : IsQuadratic χ)
  proof: by
  rw [pow_two]; rw [← gaussSum_mul_gaussSum_eq_card hχ₁ hψ]; rw [hχ₂.inv]; rw [mul_rotate']
  congr
  rw [mul_comm]; rw [← gaussSum_mulShift _ _ (-1 : Rˣ)]; rw [inv_mulShift]
  rfl

中文:
定理 gaussSum_sq
  结论: {χ : 乘法特征 R R'} (hχ₁ : χ != 1) (hχ₂ : IsQuadratic χ)
  证明: by
  rw [pow_two]; rw [← gaussSum_mul_gaussSum_eq_card hχ₁ hψ]; rw [hχ₂.inv]; rw [mul_rotate']
  congr
  rw [mul_comm]; rw [← gaussSum_mulShift _ _ (-1 : Rˣ)]; rw [inv_mulShift]
  rfl

Depends on / 依赖: gaussSum_mulShift, gaussSum_mul_gaussSum_eq_card, inv_mulShift, mul_comm, mul_rotate, pow_two
-/
theorem gaussSum_sq {χ : MulChar R R'} (hχ₁ : χ != 1) (hχ₂ : IsQuadratic χ)
    {ψ : AddChar R R'} (hψ : IsPrimitive ψ) :
    gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R := by
  rw [pow_two]; rw [← gaussSum_mul_gaussSum_eq_card hχ₁ hψ]; rw [hχ₂.inv]; rw [mul_rotate']
  congr
  rw [mul_comm]; rw [← gaussSum_mulShift _ _ (-1 : Rˣ)]; rw [inv_mulShift]
  rfl

end GaussSumProd

/-!
### Gauss sums and Frobenius
-/

section gaussSum_frob

variable {R : Type u} [CommRing R] [Fintype R] {R' : Type v} [CommRing R']

-- We assume that the target ring `R'` has prime characteristic `p`.
variable (p : Nat) [fp : Fact p.Prime] [hch : CharP R' p]

/--
theorem `gaussSum_frob` / 定理 `gaussSum_frob`

English:
theorem gaussSum_frob
  given: (χ : MulChar R R') (ψ : AddChar R R')
  proof: by
  rw [← frobenius_def]; rw [gaussSum]; rw [gaussSum]; rw [map_sum]
  simp_rw [pow_apply' χ fp.1.ne_zero, map_mul, frobenius_def]
  rfl

中文:
定理 gaussSum_frob
  条件: (χ : 乘法特征 R R') (ψ : 加法特征 R R')
  证明: by
  rw [← frobenius_def]; rw [gaussSum]; rw [gaussSum]; rw [map_sum]
  simp_rw [pow_apply' χ fp.1.ne_zero, map_mul, frobenius_def]
  rfl

Depends on / 依赖: frobenius_def, gaussSum, map_mul, map_sum, ne_zero, pow_apply, simp_rw
-/
theorem gaussSum_frob (χ : MulChar R R') (ψ : AddChar R R') :
    gaussSum χ ψ ^ p = gaussSum (χ ^ p) (ψ ^ p) := by
  rw [← frobenius_def]; rw [gaussSum]; rw [gaussSum]; rw [map_sum]
  simp_rw [pow_apply' χ fp.1.ne_zero, map_mul, frobenius_def]
  rfl

/--
theorem `MulChar.IsQuadratic.gaussSum_frob` / 定理 `MulChar.IsQuadratic.gaussSum_frob`

English:
theorem MulChar.IsQuadratic.gaussSum_frob
  statement: (hp : IsUnit (p : R)) {χ : MulChar R R'}
  proof: by
  rw [_root_.gaussSum_frob]; rw [pow_mulShift]; rw [hχ.pow_char p]; rw [← gaussSum_mulShift χ ψ hp.unit]; rw [← mul_assoc]; rw [hp.unit_spec]; rw [← pow_two]; rw [← pow_apply' _ two_ne_zero]; rw [hχ.sq_eq_one]; rw [← hp.unit_spec]; rw [one_apply_coe]; rw [one_mul]

中文:
定理 乘法特征.IsQuadratic.gaussSum_frob
  结论: (hp : 是单位 (p : R)) {χ : 乘法特征 R R'}
  证明: by
  rw [_root_.gaussSum_frob]; rw [pow_mulShift]; rw [hχ.pow_char p]; rw [← gaussSum_mulShift χ ψ hp.unit]; rw [← mul_assoc]; rw [hp.unit_spec]; rw [← pow_two]; rw [← pow_apply' _ two_ne_zero]; rw [hχ.sq_eq_one]; rw [← hp.unit_spec]; rw [one_apply_coe]; rw [one_mul]

Depends on / 依赖: _root_, _root_.gaussSum_frob, gaussSum_frob, gaussSum_mulShift, hp.unit, hp.unit_spec, mul_assoc, one_apply_coe, one_mul, pow_apply, pow_char, pow_mulShift, pow_two, sq_eq_one, two_ne_zero, unit_spec
-/
theorem MulChar.IsQuadratic.gaussSum_frob (hp : IsUnit (p : R)) {χ : MulChar R R'}
    (hχ : IsQuadratic χ) (ψ : AddChar R R') :
    gaussSum χ ψ ^ p = χ p * gaussSum χ ψ := by
  rw [_root_.gaussSum_frob]; rw [pow_mulShift]; rw [hχ.pow_char p]; rw [← gaussSum_mulShift χ ψ hp.unit]; rw [← mul_assoc]; rw [hp.unit_spec]; rw [← pow_two]; rw [← pow_apply' _ two_ne_zero]; rw [hχ.sq_eq_one]; rw [← hp.unit_spec]; rw [one_apply_coe]; rw [one_mul]

/--
theorem `MulChar.IsQuadratic.gaussSum_frob_iter` / 定理 `MulChar.IsQuadratic.gaussSum_frob_iter`

English:
theorem MulChar.IsQuadratic.gaussSum_frob_iter
  statement: (n : Nat) (hp : IsUnit (p : R)) {χ : MulChar R R'}
  proof: by
  induction n with
  | zero => rw [pow_zero, pow_one, pow_zero, MulChar.map_one, one_mul]
  | succ n ih =>
    rw [pow_succ]; rw [pow_mul]; rw [ih]; rw [mul_pow]; rw [hχ.gaussSum_frob _ hp]; rw [← mul_assoc]; rw [pow_succ]; rw [map_mul]; rw [← pow_apply' χ fp.1.ne_zero ((p : R) ^ n)]; rw [hχ.pow_char p]

中文:
定理 乘法特征.IsQuadratic.gaussSum_frob_iter
  结论: (n : 自然数) (hp : 是单位 (p : R)) {χ : 乘法特征 R R'}
  证明: by
  induction n with
  | zero => rw [pow_zero, pow_one, pow_zero, MulChar.map_one, one_mul]
  | succ n ih =>
    rw [pow_succ]; rw [pow_mul]; rw [ih]; rw [mul_pow]; rw [hχ.gaussSum_frob _ hp]; rw [← mul_assoc]; rw [pow_succ]; rw [map_mul]; rw [← pow_apply' χ fp.1.ne_zero ((p : R) ^ n)]; rw [hχ.pow_char p]

Depends on / 依赖: MulChar, MulChar.map_one, gaussSum_frob, map_mul, map_one, mul_assoc, mul_pow, ne_zero, one_mul, pow_apply, pow_char, pow_mul, pow_one, pow_succ, pow_zero
-/
theorem MulChar.IsQuadratic.gaussSum_frob_iter (n : Nat) (hp : IsUnit (p : R)) {χ : MulChar R R'}
    (hχ : IsQuadratic χ) (ψ : AddChar R R') :
    gaussSum χ ψ ^ p ^ n = χ ((p : R) ^ n) * gaussSum χ ψ := by
  induction n with
  | zero => rw [pow_zero, pow_one, pow_zero, MulChar.map_one, one_mul]
  | succ n ih =>
    rw [pow_succ]; rw [pow_mul]; rw [ih]; rw [mul_pow]; rw [hχ.gaussSum_frob _ hp]; rw [← mul_assoc]; rw [pow_succ]; rw [map_mul]; rw [← pow_apply' χ fp.1.ne_zero ((p : R) ^ n)]; rw [hχ.pow_char p]

end gaussSum_frob

/-!
### Values of quadratic characters
-/

section GaussSumValues

variable {R : Type u} [CommRing R] [Fintype R] {R' : Type v} [CommRing R'] [IsDomain R']

/--
theorem `Char.card_pow_char_pow` / 定理 `Char.card_pow_char_pow`

English:
theorem Char.card_pow_char_pow
  statement: {χ : MulChar R R'} (hχ : IsQuadratic χ) (ψ : AddChar R R') (p n : Nat)
  proof: by
  have : gaussSum χ ψ != 0 := by
    intro hf
    rw [hf]; rw [zero_pow two_ne_zero]; rw [eq_comm]; rw [mul_eq_zero] at hg
    exact not_isUnit_prime_of_dvd_card
        ((CharP.cast_eq_zero_iff R' p _).mp <| hg.resolve_left (isUnit_one.neg.map χ).ne_zero) hp
  rw [← hg]
  apply mul_right_cancel₀ this
  rw [← hχ.gaussSum_frob_iter p n hp ψ]; rw [← pow_mul]; rw [← pow_succ]; rw [Nat.two_mul_div_two_add_one_of_odd (fp.1.eq_two_or_odd'.resolve_left hp').pow]

中文:
定理 Char.card_pow_char_pow
  结论: {χ : 乘法特征 R R'} (hχ : IsQuadratic χ) (ψ : 加法特征 R R') (p n : 自然数)
  证明: by
  have : gaussSum χ ψ != 0 := by
    intro hf
    rw [hf]; rw [zero_pow two_ne_zero]; rw [eq_comm]; rw [mul_eq_zero] at hg
    exact not_isUnit_prime_of_dvd_card
        ((CharP.cast_eq_zero_iff R' p _).mp <| hg.resolve_left (isUnit_one.neg.map χ).ne_zero) hp
  rw [← hg]
  apply mul_right_cancel₀ this
  rw [← hχ.gaussSum_frob_iter p n hp ψ]; rw [← pow_mul]; rw [← pow_succ]; rw [Nat.two_mul_div_two_add_one_of_odd (fp.1.eq_two_or_odd'.resolve_left hp').pow]

Depends on / 依赖: CharP.cast_eq_zero_iff, Nat.two_mul_div_two_add_one_of_odd, cast_eq_zero_iff, eq_comm, eq_two_or_odd, gaussSum, gaussSum_frob_iter, hg.resolve_left, isUnit_one, isUnit_one.neg.map, mul_eq_zero, ne_zero, not_isUnit_prime_of_dvd_card, pow_mul, pow_succ, resolve_left, two_mul_div_two_add_one_of_odd, two_ne_zero, zero_pow
-/
theorem Char.card_pow_char_pow {χ : MulChar R R'} (hχ : IsQuadratic χ) (ψ : AddChar R R') (p n : Nat)
    [fp : Fact p.Prime] [hch : CharP R' p] (hp : IsUnit (p : R)) (hp' : p != 2)
    (hg : gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R) :
    (χ (-1) * Fintype.card R) ^ (p ^ n / 2) = χ ((p : R) ^ n) := by
  have : gaussSum χ ψ != 0 := by
    intro hf
    rw [hf]; rw [zero_pow two_ne_zero]; rw [eq_comm]; rw [mul_eq_zero] at hg
    exact not_isUnit_prime_of_dvd_card
        ((CharP.cast_eq_zero_iff R' p _).mp <| hg.resolve_left (isUnit_one.neg.map χ).ne_zero) hp
  rw [← hg]
  apply mul_right_cancel₀ this
  rw [← hχ.gaussSum_frob_iter p n hp ψ]; rw [← pow_mul]; rw [← pow_succ]; rw [Nat.two_mul_div_two_add_one_of_odd (fp.1.eq_two_or_odd'.resolve_left hp').pow]

/--
theorem `Char.card_pow_card` / 定理 `Char.card_pow_card`

English:
theorem Char.card_pow_card
  statement: {F : Type*} [Field F] [Fintype F] {F' : Type*} [Field F'] [Fintype F']
  proof: by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  obtain ⟨n', hp', hc'⟩ := FiniteField.card F' (ringChar F')
  let ψ := FiniteField.primitiveChar F F' hch₁
  let FF' := CyclotomicField ψ.n F'
  have hchar := Algebra.ringChar_eq F' FF'
  apply (algebraMap F' FF').injective
  rw [map_pow]; rw [map_mul]; rw [map_natCast]; rw [hc']; rw [hchar]; rw [Nat.cast_pow]
  simp only [← MulChar.ringHomComp_apply]
  have := Fact.mk hp'
  have := Fact.mk (hchar.subst hp')
  rw [Ne]; rw [← Nat.prime_dvd_prime_iff_eq hp' hp]; rw [← isUnit_iff_not_dvd_char]; rw [hchar] at hch₁
  exact Char.card_pow_char_pow (hχ₂.comp _) ψ.char (ringChar FF') n' hch₁ (hchar ▸ hch₂)
       (gaussSum_sq ((ringHomComp_ne_one_iff (RingHom.injective _)).mpr hχ₁) (hχ₂.comp _) ψ.prim)

中文:
定理 Char.card_pow_card
  结论: {F : 类型} [域 F] [有限类型 F] {F' : 类型} [域 F'] [有限类型 F']
  证明: by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  obtain ⟨n', hp', hc'⟩ := FiniteField.card F' (ringChar F')
  let ψ := FiniteField.primitiveChar F F' hch₁
  let FF' := CyclotomicField ψ.n F'
  have hchar := Algebra.ringChar_eq F' FF'
  apply (algebraMap F' FF').injective
  rw [map_pow]; rw [map_mul]; rw [map_natCast]; rw [hc']; rw [hchar]; rw [Nat.cast_pow]
  simp only [← MulChar.ringHomComp_apply]
  have := Fact.mk hp'
  have := Fact.mk (hchar.subst hp')
  rw [Ne]; rw [← Nat.prime_dvd_prime_iff_eq hp' hp]; rw [← isUnit_iff_not_dvd_char]; rw [hchar] at hch₁
  exact Char.card_pow_char_pow (hχ₂.comp _) ψ.char (ringChar FF') n' hch₁ (hchar ▸ hch₂)
       (gaussSum_sq ((ringHomComp_ne_one_iff (RingHom.injective _)).mpr hχ₁) (hχ₂.comp _) ψ.prim)

Depends on / 依赖: Algebra, Algebra.ringChar_eq, CyclotomicField, Fact.mk, FiniteField, FiniteField.card, FiniteField.primitiveChar, MulChar, MulChar.ringHomComp_apply, Nat.cast_pow, Nat.prime_dvd_prime_iff_eq, algebraMap, cast_pow, hchar.subst, injective, map_mul, map_natCast, map_pow, prime_dvd_prime_iff_eq, primitiveChar
-/
theorem Char.card_pow_card {F : Type*} [Field F] [Fintype F] {F' : Type*} [Field F'] [Fintype F']
    {χ : MulChar F F'} (hχ₁ : χ != 1) (hχ₂ : IsQuadratic χ)
    (hch₁ : ringChar F' != ringChar F) (hch₂ : ringChar F' != 2) :
    (χ (-1) * Fintype.card F) ^ (Fintype.card F' / 2) = χ (Fintype.card F') := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  obtain ⟨n', hp', hc'⟩ := FiniteField.card F' (ringChar F')
  let ψ := FiniteField.primitiveChar F F' hch₁
  let FF' := CyclotomicField ψ.n F'
  have hchar := Algebra.ringChar_eq F' FF'
  apply (algebraMap F' FF').injective
  rw [map_pow]; rw [map_mul]; rw [map_natCast]; rw [hc']; rw [hchar]; rw [Nat.cast_pow]
  simp only [← MulChar.ringHomComp_apply]
  have := Fact.mk hp'
  have := Fact.mk (hchar.subst hp')
  rw [Ne]; rw [← Nat.prime_dvd_prime_iff_eq hp' hp]; rw [← isUnit_iff_not_dvd_char]; rw [hchar] at hch₁
  exact Char.card_pow_char_pow (hχ₂.comp _) ψ.char (ringChar FF') n' hch₁ (hchar ▸ hch₂)
       (gaussSum_sq ((ringHomComp_ne_one_iff (RingHom.injective _)).mpr hχ₁) (hχ₂.comp _) ψ.prim)

end GaussSumValues

section GaussSumTwo

/-!
### The quadratic character of 2

This section proves the following result.

For every finite field `F` of odd characteristic, we have `2^(#F/2) = χ₈#F` in `F`.
This can be used to show that the quadratic character of `F` takes the value
`χ₈#F` at `2`.

The proof uses the Gauss sum of `χ₈` and a primitive additive character on `ℤ/8ℤ`;
in this way, the result is reduced to `card_pow_char_pow`.
-/

open ZMod

set_option backward.isDefEq.respectTransparency false in
/--
theorem `FiniteField.two_pow_card` / 定理 `FiniteField.two_pow_card`

English:
theorem FiniteField.two_pow_card
  given: {F : Type*} [Fintype F] [Field F] (hF : ringChar F != 2)
  proof: by
  have hp2 (n : Nat) : (2 ^ n : F) != 0 := pow_ne_zero n (Ring.two_ne_zero hF)
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- we work in `FF`, the eighth cyclotomic field extension of `F`
  let FF := CyclotomicField 8 F
  have hchar := Algebra.ringChar_eq F FF
  have FFp := hchar.subst hp
  have := Fact.mk FFp
  have hFF := hchar ▸ hF -- `ringChar FF ≠ 2`
  have hu : IsUnit (ringChar FF : ZMod 8) := by
    rw [isUnit_iff_not_dvd_char]; rw [ringChar_zmod_n]
    rw [Ne]; rw [← Nat.prime_dvd_prime_iff_eq FFp Nat.prime_two] at hFF
    change ¬_ ∣ 2 ^ 3
    exact mt FFp.dvd_of_dvd_pow hFF
  -- there is a primitive additive character `ℤ/8ℤ → FF`, sending `a + 8ℤ ↦ τ^a`
  -- with a primitive eighth root of unity `τ`
  let ψ₈ := primitiveZModChar 8 F (by convert! hp2 3 using 1; norm_cast)
  -- We cast from `AddChar (ZMod (8 : ℕ+)) FF` to `AddChar (ZMod 8) FF`
  -- This is needed to make `simp_rw [← h₁]` below work.
  let ψ₈char : AddChar (ZMod 8) FF := ψ₈.char
  let τ : FF := ψ₈char 1
  have τ_spec : τ ^ 4 = -1 := by
    rw [show τ = ψ₈.char 1 from rfl] -- to make `rw [ψ₈.prim.zmod_char_eq_one_iff]` work
    refine (sq_eq_one_iff.1 ?_).resolve_left ?_
    · rw [← pow_mul, ← map_nsmul_eq_pow ψ₈.char, ψ₈.prim.zmod_char_eq_one_iff]
      decide
    · rw [← map_nsmul_eq_pow ψ₈.char, ψ₈.prim.zmod_char_eq_one_iff]
      decide
  -- we consider `χ₈` as a multiplicative character `ℤ/8ℤ → FF`
  let χ := χ₈.ringHomComp (Int.castRingHom FF)
  have hχ : χ (-1) = 1 := Int.cast_one
  have hq : IsQuadratic χ := isQuadratic_χ₈.comp _
  -- we now show that the Gauss sum of `χ` and `ψ₈` has the relevant property
  have h₁ : (fun (a : Fin 8) => ↑(χ₈ a) * τ ^ (a : Nat)) = fun a => χ a * ↑(ψ₈char a) := by
    ext1; congr; apply pow_one
  have hg₁ : gaussSum χ ψ₈char = 2 * (τ - τ ^ 3) := by
    rw [gaussSum]; rw [← h₁]; rw [Fin.sum_univ_eight]; rw [-- evaluate `χ₈`
      show χ₈ 0 = 0 from rfl]; rw [show χ₈ 1 = 1 from rfl]; rw [show χ₈ 2 = 0 from rfl]; rw [show χ₈ 3 = -1 from rfl]; rw [show χ₈ 4 = 0 from rfl]; rw [show χ₈ 5 = -1 from rfl]; rw [show χ₈ 6 = 0 from rfl]; rw [show χ₈ 7 = 1 from rfl]; rw [-- normalize exponents
      show ((3 : Fin 8) : Nat) = 3 from rfl]; rw [show ((5 : Fin 8) : Nat) = 5 from rfl]; rw [show ((7 : Fin 8) : Nat) = 7 from rfl]
    simp only [Int.cast_zero, zero_mul, Int.cast_one, Fin.val_one, pow_one, one_mul, zero_add,
      Fin.val_two, add_zero, Int.reduceNeg, Int.cast_neg]
    linear_combination (τ ^ 3 - τ) * τ_spec
  have hg : gaussSum χ ψ₈char ^ 2 = χ (-1) * Fintype.card (ZMod 8) := by
    rw [hχ]; rw [one_mul]; rw [ZMod.card]; rw [Nat.cast_ofNat]; rw [hg₁]
    linear_combination (4 * τ ^ 2 - 8) * τ_spec
  -- this allows us to apply `card_pow_char_pow` to our situation
  have h := Char.card_pow_char_pow (R := ZMod 8) hq ψ₈char (ringChar FF) n hu hFF hg
  rw [ZMod.card]; rw [← hchar]; rw [hχ]; rw [one_mul]; rw [← hc]; rw [← Nat.cast_pow (ringChar F)]; rw [← hc] at h
  -- finally, we change `2` to `8` on the left-hand side
  convert_to (8 : F) ^ (Fintype.card F / 2) = _
  · rw [(by norm_num : (8 : F) = 2 ^ 2 * 2), mul_pow,
      (FiniteField.isSquare_iff hF <| hp2 2).mp ⟨2, pow_two 2⟩, one_mul]
  apply (algebraMap F FF).injective
  simpa only [map_pow, map_ofNat, map_intCast, Nat.cast_ofNat] using! h

中文:
定理 FiniteField.two_pow_card
  条件: {F : 类型} [有限类型 F] [域 F] (hF : ringChar F != 2)
  证明: by
  have hp2 (n : Nat) : (2 ^ n : F) != 0 := pow_ne_zero n (Ring.two_ne_zero hF)
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- we work in `FF`, the eighth cyclotomic field extension of `F`
  let FF := CyclotomicField 8 F
  have hchar := Algebra.ringChar_eq F FF
  have FFp := hchar.subst hp
  have := Fact.mk FFp
  have hFF := hchar ▸ hF -- `ringChar FF ≠ 2`
  have hu : IsUnit (ringChar FF : ZMod 8) := by
    rw [isUnit_iff_not_dvd_char]; rw [ringChar_zmod_n]
    rw [Ne]; rw [← Nat.prime_dvd_prime_iff_eq FFp Nat.prime_two] at hFF
    change ¬_ ∣ 2 ^ 3
    exact mt FFp.dvd_of_dvd_pow hFF
  -- there is a primitive additive character `ℤ/8ℤ → FF`, sending `a + 8ℤ ↦ τ^a`
  -- with a primitive eighth root of unity `τ`
  let ψ₈ := primitiveZModChar 8 F (by convert! hp2 3 using 1; norm_cast)
  -- We cast from `AddChar (ZMod (8 : ℕ+)) FF` to `AddChar (ZMod 8) FF`
  -- This is needed to make `simp_rw [← h₁]` below work.
  let ψ₈char : AddChar (ZMod 8) FF := ψ₈.char
  let τ : FF := ψ₈char 1
  have τ_spec : τ ^ 4 = -1 := by
    rw [show τ = ψ₈.char 1 from rfl] -- to make `rw [ψ₈.prim.zmod_char_eq_one_iff]` work
    refine (sq_eq_one_iff.1 ?_).resolve_left ?_
    · rw [← pow_mul, ← map_nsmul_eq_pow ψ₈.char, ψ₈.prim.zmod_char_eq_one_iff]
      decide
    · rw [← map_nsmul_eq_pow ψ₈.char, ψ₈.prim.zmod_char_eq_one_iff]
      decide
  -- we consider `χ₈` as a multiplicative character `ℤ/8ℤ → FF`
  let χ := χ₈.ringHomComp (Int.castRingHom FF)
  have hχ : χ (-1) = 1 := Int.cast_one
  have hq : IsQuadratic χ := isQuadratic_χ₈.comp _
  -- we now show that the Gauss sum of `χ` and `ψ₈` has the relevant property
  have h₁ : (fun (a : Fin 8) => ↑(χ₈ a) * τ ^ (a : Nat)) = fun a => χ a * ↑(ψ₈char a) := by
    ext1; congr; apply pow_one
  have hg₁ : gaussSum χ ψ₈char = 2 * (τ - τ ^ 3) := by
    rw [gaussSum]; rw [← h₁]; rw [Fin.sum_univ_eight]; rw [-- evaluate `χ₈`
      show χ₈ 0 = 0 from rfl]; rw [show χ₈ 1 = 1 from rfl]; rw [show χ₈ 2 = 0 from rfl]; rw [show χ₈ 3 = -1 from rfl]; rw [show χ₈ 4 = 0 from rfl]; rw [show χ₈ 5 = -1 from rfl]; rw [show χ₈ 6 = 0 from rfl]; rw [show χ₈ 7 = 1 from rfl]; rw [-- normalize exponents
      show ((3 : Fin 8) : Nat) = 3 from rfl]; rw [show ((5 : Fin 8) : Nat) = 5 from rfl]; rw [show ((7 : Fin 8) : Nat) = 7 from rfl]
    simp only [Int.cast_zero, zero_mul, Int.cast_one, Fin.val_one, pow_one, one_mul, zero_add,
      Fin.val_two, add_zero, Int.reduceNeg, Int.cast_neg]
    linear_combination (τ ^ 3 - τ) * τ_spec
  have hg : gaussSum χ ψ₈char ^ 2 = χ (-1) * Fintype.card (ZMod 8) := by
    rw [hχ]; rw [one_mul]; rw [ZMod.card]; rw [Nat.cast_ofNat]; rw [hg₁]
    linear_combination (4 * τ ^ 2 - 8) * τ_spec
  -- this allows us to apply `card_pow_char_pow` to our situation
  have h := Char.card_pow_char_pow (R := ZMod 8) hq ψ₈char (ringChar FF) n hu hFF hg
  rw [ZMod.card]; rw [← hchar]; rw [hχ]; rw [one_mul]; rw [← hc]; rw [← Nat.cast_pow (ringChar F)]; rw [← hc] at h
  -- finally, we change `2` to `8` on the left-hand side
  convert_to (8 : F) ^ (Fintype.card F / 2) = _
  · rw [(by norm_num : (8 : F) = 2 ^ 2 * 2), mul_pow,
      (FiniteField.isSquare_iff hF <| hp2 2).mp ⟨2, pow_two 2⟩, one_mul]
  apply (algebraMap F FF).injective
  simpa only [map_pow, map_ofNat, map_intCast, Nat.cast_ofNat] using! h

Depends on / 依赖: FiniteField, FiniteField.card, Ring.two_ne_zero, pow_ne_zero, ringChar, two_ne_zero
-/
theorem FiniteField.two_pow_card {F : Type*} [Fintype F] [Field F] (hF : ringChar F != 2) :
    (2 : F) ^ (Fintype.card F / 2) = χ₈ (Fintype.card F) := by
  have hp2 (n : Nat) : (2 ^ n : F) != 0 := pow_ne_zero n (Ring.two_ne_zero hF)
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- we work in `FF`, the eighth cyclotomic field extension of `F`
  let FF := CyclotomicField 8 F
  have hchar := Algebra.ringChar_eq F FF
  have FFp := hchar.subst hp
  have := Fact.mk FFp
  have hFF := hchar ▸ hF -- `ringChar FF ≠ 2`
  have hu : IsUnit (ringChar FF : ZMod 8) := by
    rw [isUnit_iff_not_dvd_char]; rw [ringChar_zmod_n]
    rw [Ne]; rw [← Nat.prime_dvd_prime_iff_eq FFp Nat.prime_two] at hFF
    change ¬_ ∣ 2 ^ 3
    exact mt FFp.dvd_of_dvd_pow hFF
  -- there is a primitive additive character `ℤ/8ℤ → FF`, sending `a + 8ℤ ↦ τ^a`
  -- with a primitive eighth root of unity `τ`
  let ψ₈ := primitiveZModChar 8 F (by convert! hp2 3 using 1; norm_cast)
  -- We cast from `AddChar (ZMod (8 : ℕ+)) FF` to `AddChar (ZMod 8) FF`
  -- This is needed to make `simp_rw [← h₁]` below work.
  let ψ₈char : AddChar (ZMod 8) FF := ψ₈.char
  let τ : FF := ψ₈char 1
  have τ_spec : τ ^ 4 = -1 := by
    rw [show τ = ψ₈.char 1 from rfl] -- to make `rw [ψ₈.prim.zmod_char_eq_one_iff]` work
    refine (sq_eq_one_iff.1 ?_).resolve_left ?_
    · rw [← pow_mul, ← map_nsmul_eq_pow ψ₈.char, ψ₈.prim.zmod_char_eq_one_iff]
      decide
    · rw [← map_nsmul_eq_pow ψ₈.char, ψ₈.prim.zmod_char_eq_one_iff]
      decide
  -- we consider `χ₈` as a multiplicative character `ℤ/8ℤ → FF`
  let χ := χ₈.ringHomComp (Int.castRingHom FF)
  have hχ : χ (-1) = 1 := Int.cast_one
  have hq : IsQuadratic χ := isQuadratic_χ₈.comp _
  -- we now show that the Gauss sum of `χ` and `ψ₈` has the relevant property
  have h₁ : (fun (a : Fin 8) => ↑(χ₈ a) * τ ^ (a : Nat)) = fun a => χ a * ↑(ψ₈char a) := by
    ext1; congr; apply pow_one
  have hg₁ : gaussSum χ ψ₈char = 2 * (τ - τ ^ 3) := by
    rw [gaussSum]; rw [← h₁]; rw [Fin.sum_univ_eight]; rw [-- evaluate `χ₈`
      show χ₈ 0 = 0 from rfl]; rw [show χ₈ 1 = 1 from rfl]; rw [show χ₈ 2 = 0 from rfl]; rw [show χ₈ 3 = -1 from rfl]; rw [show χ₈ 4 = 0 from rfl]; rw [show χ₈ 5 = -1 from rfl]; rw [show χ₈ 6 = 0 from rfl]; rw [show χ₈ 7 = 1 from rfl]; rw [-- normalize exponents
      show ((3 : Fin 8) : Nat) = 3 from rfl]; rw [show ((5 : Fin 8) : Nat) = 5 from rfl]; rw [show ((7 : Fin 8) : Nat) = 7 from rfl]
    simp only [Int.cast_zero, zero_mul, Int.cast_one, Fin.val_one, pow_one, one_mul, zero_add,
      Fin.val_two, add_zero, Int.reduceNeg, Int.cast_neg]
    linear_combination (τ ^ 3 - τ) * τ_spec
  have hg : gaussSum χ ψ₈char ^ 2 = χ (-1) * Fintype.card (ZMod 8) := by
    rw [hχ]; rw [one_mul]; rw [ZMod.card]; rw [Nat.cast_ofNat]; rw [hg₁]
    linear_combination (4 * τ ^ 2 - 8) * τ_spec
  -- this allows us to apply `card_pow_char_pow` to our situation
  have h := Char.card_pow_char_pow (R := ZMod 8) hq ψ₈char (ringChar FF) n hu hFF hg
  rw [ZMod.card]; rw [← hchar]; rw [hχ]; rw [one_mul]; rw [← hc]; rw [← Nat.cast_pow (ringChar F)]; rw [← hc] at h
  -- finally, we change `2` to `8` on the left-hand side
  convert_to (8 : F) ^ (Fintype.card F / 2) = _
  · rw [(by norm_num : (8 : F) = 2 ^ 2 * 2), mul_pow,
      (FiniteField.isSquare_iff hF <| hp2 2).mp ⟨2, pow_two 2⟩, one_mul]
  apply (algebraMap F FF).injective
  simpa only [map_pow, map_ofNat, map_intCast, Nat.cast_ofNat] using! h

end GaussSumTwo
