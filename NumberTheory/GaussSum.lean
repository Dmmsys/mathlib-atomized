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

/-- Definition of the Gauss sum associated to a multiplicative and an additive character. -/
/-
**gaussSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：gaussSum (χ : MulChar R R') (ψ : AddChar R R') : R'
参数：χ : MulChar R R'；ψ : AddChar R R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of the Gauss sum associated to a multiplicative and an additive chara
cter.
-/
def gaussSum (χ : MulChar R R') (ψ : AddChar R R') : R' :=
  ∑ a, χ a * ψ a

/-- Replacing `ψ` by `mulShift ψ a` and multiplying the Gauss sum by `χ a` does not change it. -/
/-
**gaussSum_mulShift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaussSum_mulShift (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ) : χ a * g
aussSum χ (mulShift ψ a) = gaussSum χ ψ
参数：χ : MulChar R R'；ψ : AddChar R R'；a : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `Fintype.sum_bijective`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [i
nst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι → κ), 
Function.Bi…
· 使用定理 `Units.mulLeft_bijective`：mulLeft_bijective (a : Mˣ) : Function.Bijective
 ((a * ·) : M -> M)

--- 原说明 ---
Replacing `ψ` by `mulShift ψ a` and multiplying the Gauss sum by `χ a` does not 
change it.
-/
theorem gaussSum_mulShift (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ) :
    χ a * gaussSum χ (mulShift ψ a) = gaussSum χ ψ := by
  simp only [gaussSum, mulShift_apply, Finset.mul_sum]
  simp_rw [← mul_assoc, ← map_mul]
  exact Fintype.sum_bijective _ a.mulLeft_bijective _ _ fun x ↦ rfl

/-- Replacing `ψ` by `mulShift ψ a` multiplies the Gauss sum by `χ⁻¹ a`. -/
/-
**gaussSum_mulShift_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaussSum_mulShift_eq (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ) : gaus
sSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ
参数：χ : MulChar R R'；ψ : AddChar R R'；a : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gaussSum_mulShift`：gaussSum_mulShift (χ : MulChar R R') (ψ : AddChar R R
') (a : Rˣ) : χ a * gaussSum χ (mulShift ψ a) = gaussSum χ ψ
· 使用定理 `MulChar.inv_apply_eq_inv`：inv_apply_eq_inv (χ : MulChar R R') (a : R) : 
χ⁻¹ a = (χ a)⁻¹ʳ
· 使用定理 `Ring.inverse_mul_cancel_left`：inverse_mul_cancel_left (x y : M₀) (h : Is
Unit x) : x⁻¹ʳ * (x * y) = y
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u

--- 原说明 ---
Replacing `ψ` by `mulShift ψ a` multiplies the Gauss sum by `χ⁻¹ a`.
-/
theorem gaussSum_mulShift_eq (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  rw [← gaussSum_mulShift χ ψ a, inv_apply_eq_inv,
    Ring.inverse_mul_cancel_left _ _ (a.isUnit.map χ)]

/-- Taking complex conjugates of a Gauss sum inverts both characters. -/
/-
**star_gaussSum_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：star_gaussSum_eq (χ : MulChar R Complex) (ψ : AddChar R Complex) : star (g
aussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹
参数：χ : MulChar R Complex；ψ : AddChar R Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_sum`：star_sum [AddCommMonoid R] [StarAddMonoid R] {α : Type*} (s : 
Finset α) (f : α -> R) : star (∑ x in s, f x) = ∑ x in s, star (f x)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用引理 `MulChar.star_apply'`：star_apply' (χ : MulChar R Complex) (a : R) : star 
(χ a) = χ⁻¹ a
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AddChar.map_neg_eq_conj`：map_neg_eq_conj [AddCommGroup G] (ψ : AddChar G
 K) (x : G) : ψ (-x) = conj (ψ x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
Taking complex conjugates of a Gauss sum inverts both characters.
-/
lemma star_gaussSum_eq (χ : MulChar R ℂ) (ψ : AddChar R ℂ) :
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
/-
**gaussSum_one_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaussSum_one_one : gaussSum (1 : MulChar R R') (1 : AddChar R R') = Nat.ca
rd Rˣ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulChar.sum_one_eq_card_units`：sum_one_eq_card_units [DecidableEq R] : (
∑ a, (1 : MulChar R R') a) = Fintype.card Rˣ
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Gauss sum of the two trivial characters is the cardinality of the unit group
 of `R`.
-/
theorem gaussSum_one_one : gaussSum (1 : MulChar R R') (1 : AddChar R R') = Nat.card Rˣ := by
  classical
  simp [gaussSum, MulChar.sum_one_eq_card_units]

/-- The Gauss sum of a nontrivial multiplicative character and the trivial additive character
vanishes. -/
/-
**gaussSum_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaussSum_one_right [IsDomain R'] {χ : MulChar R R'} (hχ : χ != 1) : gaussS
um χ (1 : AddChar R R') = 0
参数：hχ : χ != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulChar.sum_eq_zero_of_ne_one`：sum_eq_zero_of_ne_one [IsDomain R'] {χ : 
MulChar R R'} (hχ : χ != 1) : ∑ a, χ a = 0

--- 原说明 ---
The Gauss sum of a nontrivial multiplicative character and the trivial additive 
character
vanishes.
-/
theorem gaussSum_one_right [IsDomain R'] {χ : MulChar R R'} (hχ : χ ≠ 1) :
    gaussSum χ (1 : AddChar R R') = 0 := by
  simpa [gaussSum] using MulChar.sum_eq_zero_of_ne_one hχ

end GaussSumTrivial

section GaussSumTrivialField

variable {R R' : Type*} [Field R] [Fintype R] [CommRing R'] [IsDomain R']

/-- The Gauss sum of the trivial multiplicative character and a nontrivial additive character,
over a finite field, is `-1`. -/
/-
**gaussSum_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaussSum_one_left {ψ : AddChar R R'} (hψ : ψ != 1) : gaussSum (1 : MulChar
 R R') ψ = -1
参数：hψ : ψ != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_compl_add_sum`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (s : Finset ι)   (f : ι
 → M), ∑ i ∈ s…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulCharClass.map_nonunit`：∀ {F : Type u_3} {R : outParam (Type u_4)} {R'
 : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZero R'}
 {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `MulChar.one_apply`：one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R'
) x = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AddChar.sum_eq_zero_of_ne_one`：sum_eq_zero_of_ne_one [IsDomain R'] {ψ : 
AddChar R R'} (hψ : ψ != 1) : ∑ a, ψ a = 0

--- 原说明 ---
The Gauss sum of the trivial multiplicative character and a nontrivial additive 
character,
over a finite field, is `-1`.
-/
theorem gaussSum_one_left {ψ : AddChar R R'} (hψ : ψ ≠ 1) :
    gaussSum (1 : MulChar R R') ψ = -1 := by
  classical
  simp only [gaussSum, ← add_eq_zero_iff_eq_neg]
  calc ∑ a, (1 : MulChar R R') a * ψ a + 1
  _ = ∑ a ∈ {0}ᶜ, (1 : MulChar R R') a * ψ a + 1 := by
    simp [← ({0} : Finset R).sum_compl_add_sum]
  _ = ∑ a ∈ {0}ᶜ, ψ a + ψ 0 := by
    congr! <;> aesop (add simp MulChar.one_apply)
  _ = 0 := by
    rw [← AddChar.sum_eq_zero_of_ne_one hψ, ← Finset.sum_compl_add_sum (s := {0})]
    simp

end GaussSumTrivialField

/-!
### The product of two Gauss sums
-/

section GaussSumProd

open Finset in
/-- A formula for the product of two Gauss sums with the same additive character. -/
/-
**gaussSum_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gaussSum_mul {R : Type u} [CommRing R] [Fintype R] {R' : Type v} [CommRing
 R'] (χ φ : MulChar R R') (ψ : AddChar R R') : gaussSum χ ψ * gaussSum φ ψ = ∑ t
 : R, ∑ x : R, χ x * φ (t - x) * ψ t
参数：χ φ : MulChar R R'；ψ : AddChar R R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gaussSum.eq_1`：∀ {R : Type u} [inst : CommRing R] [inst_1 : Fintype R] {
R' : Type v} [inst_2 : CommRing R'] (χ : MulChar R R')   (ψ : AddChar R R'), gau
ssS…
· 使用引理 `Finset.sum_mul_sum`：sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> 
R) (g : κ -> R) : (∑ i in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g 
j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y
· 使用定理 `Finset.sum_bij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a 
: ι)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…

--- 原说明 ---
A formula for the product of two Gauss sums with the same additive character.
-/
lemma gaussSum_mul {R : Type u} [CommRing R] [Fintype R] {R' : Type v} [CommRing R']
    (χ φ : MulChar R R') (ψ : AddChar R R') :
    gaussSum χ ψ * gaussSum φ ψ = ∑ t : R, ∑ x : R, χ x * φ (t - x) * ψ t := by
  rw [gaussSum, gaussSum, sum_mul_sum]
  conv => enter [1, 2, x, 2, x_1]; rw [mul_mul_mul_comm]
  simp only [← ψ.map_add_eq_mul]
  have sum_eq x : ∑ y : R, χ x * φ y * ψ (x + y) = ∑ y : R, χ x * φ (y - x) * ψ y := by
    rw [sum_bij (fun a _ ↦ a + x)]
    · simp only [mem_univ, forall_const]
    · simp only [mem_univ, add_left_inj, imp_self, forall_const]
    · exact fun b _ ↦ ⟨b - x, mem_univ _, by rw [sub_add_cancel]⟩
    · exact fun a _ ↦ by rw [add_sub_cancel_right, add_comm]
  rw [sum_congr rfl fun x _ ↦ sum_eq x, sum_comm]

-- In the following, we need `R` to be a finite field.
variable {R : Type u} [Field R] [Fintype R] {R' : Type v} [CommRing R']
/-
**mul_gaussSum_inv_eq_gaussSum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_gaussSum_inv_eq_gaussSum (χ : MulChar R R') (ψ : AddChar R R') : χ (-1
) * gaussSum χ ψ⁻¹ = gaussSum χ ψ
参数：χ : MulChar R R'；ψ : AddChar R R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddChar.inv_mulShift`：inv_mulShift (ψ : AddChar R M) : ψ⁻¹ = mulShift ψ 
(-1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.coe_neg_one`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistrib
Neg α], ↑(-1) = -1
· 使用定理 `gaussSum_mulShift`：gaussSum_mulShift (χ : MulChar R R') (ψ : AddChar R R
') (a : Rˣ) : χ a * gaussSum χ (mulShift ψ a) = gaussSum χ ψ
-/
lemma mul_gaussSum_inv_eq_gaussSum (χ : MulChar R R') (ψ : AddChar R R') :
    χ (-1) * gaussSum χ ψ⁻¹ = gaussSum χ ψ := by
  rw [ψ.inv_mulShift, ← Units.coe_neg_one]
  exact gaussSum_mulShift χ ψ (-1)

variable [IsDomain R'] --  From now on, `R'` needs to be a domain.

-- A helper lemma for `gaussSum_mul_gaussSum_eq_card` below
-- Is this useful enough in other contexts to be public?
/-
**gaussSum_mul_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem gaussSum_mul_aux {χ : MulChar R R'} (hχ : χ ≠ 1) (ψ : AddChar R R')
    (b : R) :
    ∑ a, χ (a * b⁻¹) * ψ (a - b) = ∑ c, χ c * ψ (b * (c - 1)) := by
  rcases eq_or_ne b 0 with hb | hb
  · -- case `b = 0`
    simp only [hb, inv_zero, mul_zero, MulChar.map_zero, zero_mul,
      Finset.sum_const_zero, map_zero_eq_one, mul_one, χ.sum_eq_zero_of_ne_one hχ]
  · -- case `b ≠ 0`
    refine (Fintype.sum_bijective _ (mulLeft_bijective₀ b hb) _ _ fun x ↦ ?_).symm
    rw [mul_assoc, mul_comm x, ← mul_assoc, mul_inv_cancel₀ hb, one_mul, mul_sub, mul_one]

/-- We have `gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card R`
when `χ` is nontrivial and `ψ` is primitive (and `R` is a field). -/
/-
**gaussSum_mul_gaussSum_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaussSum_mul_gaussSum_eq_card {χ : MulChar R R'} (hχ : χ != 1) {ψ : AddCha
r R R'} (hψ : IsPrimitive ψ) : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card R
参数：hχ : χ != 1；hψ : IsPrimitive ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulChar.inv_apply'`：inv_apply' {R : Type*} [CommGroupWithZero R] (χ : Mu
lChar R R') (a : R) : χ⁻¹ a = χ a⁻¹
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `_private.Mathlib.NumberTheory.GaussSum.0.gaussSum_mul_aux`：∀ {R : Type u
} [inst : Field R] [inst_1 : Fintype R] {R' : Type v} [inst_2 : CommRing R'] [Is
Domain R']   {χ : MulChar R R'}, χ ≠ 1 → ∀ (ψ :…
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `AddChar.sum_mulShift`：sum_mulShift {R : Type*} [CommRing R] [Fintype R] 
[DecidableEq R] {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar R R'} (b :
 R) (hψ : …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We have `gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card R`
when `χ` is nontrivial and `ψ` is primitive (and `R` is a field).
-/
theorem gaussSum_mul_gaussSum_eq_card {χ : MulChar R R'} (hχ : χ ≠ 1) {ψ : AddChar R R'}
    (hψ : IsPrimitive ψ) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card R := by
  simp only [gaussSum, AddChar.inv_apply, Finset.sum_mul, Finset.mul_sum, MulChar.inv_apply']
  conv =>
    enter [1, 2, x, 2, y]
    rw [mul_mul_mul_comm, ← map_mul, ← map_add_eq_mul, ← sub_eq_add_neg]
--  conv in _ * _ * (_ * _) => rw [mul_mul_mul_comm, ← map_mul, ← map_add_eq_mul, ← sub_eq_add_neg]
  simp_rw [gaussSum_mul_aux hχ ψ]
  rw [Finset.sum_comm]
  classical -- to get `[DecidableEq R]` for `sum_mulShift`
  simp_rw [← Finset.mul_sum, sum_mulShift _ hψ, sub_eq_zero, apply_ite, Nat.cast_zero, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (1 : R)]
  simp only [Finset.mem_univ, map_one, one_mul, if_true]

/-- If `χ` is a multiplicative character of order `n` on a finite field `F`,
then `g(χ) * g(χ^(n-1)) = χ(-1)*#F` -/
/-
**gaussSum_mul_gaussSum_pow_orderOf_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gaussSum_mul_gaussSum_pow_orderOf_sub_one {χ : MulChar R R'} {ψ : AddChar 
R R'} (hχ : χ != 1) (hψ : ψ.IsPrimitive) : gaussSum χ ψ * gaussSum (χ ^ (orderOf
 χ - 1)) ψ = χ (-1) * Fintype.card R
参数：hχ : χ != 1；hψ : ψ.IsPrimitive。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Nat.sub_one_add_one_eq_of_pos`：∀ {n : ℕ}, 0 < n → n - 1 + 1 = n
· 使用引理 `MulChar.orderOf_pos`：orderOf_pos [Finite Mˣ] (χ : MulChar M R) : 0 < ord
erOf χ
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用引理 `mul_gaussSum_inv_eq_gaussSum`：mul_gaussSum_inv_eq_gaussSum (χ : MulChar 
R R') (ψ : AddChar R R') : χ (-1) * gaussSum χ ψ⁻¹ = gaussSum χ ψ
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `gaussSum_mul_gaussSum_eq_card`：gaussSum_mul_gaussSum_eq_card {χ : MulCha
r R R'} (hχ : χ != 1) {ψ : AddChar R R'} (hψ : IsPrimitive ψ) : gaussSum χ ψ * g
aussSum χ⁻¹ ψ⁻¹ = F…
· 使用定理 `MulChar.inv_apply'`：inv_apply' {R : Type*} [CommGroupWithZero R] (χ : Mu
lChar R R') (a : R) : χ⁻¹ a = χ a⁻¹
· 使用引理 `inv_neg_one`：inv_neg_one : (-1 : R)⁻¹ = -1

--- 原说明 ---
If `χ` is a multiplicative character of order `n` on a finite field `F`,
then `g(χ) * g(χ^(n-1)) = χ(-1)*#F`
-/
lemma gaussSum_mul_gaussSum_pow_orderOf_sub_one {χ : MulChar R R'} {ψ : AddChar R R'}
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ ^ (orderOf χ - 1)) ψ = χ (-1) * Fintype.card R := by
  have h : χ ^ (orderOf χ - 1) = χ⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos χ.orderOf_pos, pow_orderOf_eq_one]
  rw [h, ← mul_gaussSum_inv_eq_gaussSum χ⁻¹, mul_left_comm, gaussSum_mul_gaussSum_eq_card hχ hψ,
    MulChar.inv_apply', inv_neg_one]

/-- The Gauss sum of a nontrivial character on a finite field does not vanish. -/
/-
**gaussSum_ne_zero_of_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gaussSum_ne_zero_of_nontrivial (h : (Fintype.card R : R') != 0) {χ : MulCh
ar R R'} (hχ : χ != 1) {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) : gaussSum χ ψ !=
 0
参数：h : (Fintype.card R : R') != 0；hχ : χ != 1；hψ : ψ.IsPrimitive。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `gaussSum_mul_gaussSum_eq_card`：gaussSum_mul_gaussSum_eq_card {χ : MulCha
r R R'} (hχ : χ != 1) {ψ : AddChar R R'} (hψ : IsPrimitive ψ) : gaussSum χ ψ * g
aussSum χ⁻¹ ψ⁻¹ = F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
The Gauss sum of a nontrivial character on a finite field does not vanish.
-/
lemma gaussSum_ne_zero_of_nontrivial (h : (Fintype.card R : R') ≠ 0) {χ : MulChar R R'}
    (hχ : χ ≠ 1) {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ≠ 0 :=
  fun H ↦ h.symm <| zero_mul (gaussSum χ⁻¹ _) ▸ H ▸ gaussSum_mul_gaussSum_eq_card hχ hψ

/-- When `χ` is a nontrivial quadratic character, then the square of `gaussSum χ ψ`
is `χ(-1)` times the cardinality of `R`. -/
/-
**gaussSum_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaussSum_sq {χ : MulChar R R'} (hχ₁ : χ != 1) (hχ₂ : IsQuadratic χ) {ψ : A
ddChar R R'} (hψ : IsPrimitive ψ) : gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R
参数：hχ₁ : χ != 1；hχ₂ : IsQuadratic χ；hψ : IsPrimitive ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gaussSum_mul_gaussSum_eq_card`：gaussSum_mul_gaussSum_eq_card {χ : MulCha
r R R'} (hχ : χ != 1) {ψ : AddChar R R'} (hψ : IsPrimitive ψ) : gaussSum χ ψ * g
aussSum χ⁻¹ ψ⁻¹ = F…
· 使用定理 `MulChar.IsQuadratic.inv`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Ty
pe u_2} [inst_1 : CommRing R'] {χ : MulChar R R'},   χ.IsQuadratic → χ⁻¹ = χ
· 使用定理 `mul_rotate'`：mul_rotate' (a b c : G) : a * (b * c) = b * (c * a)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `gaussSum_mulShift`：gaussSum_mulShift (χ : MulChar R R') (ψ : AddChar R R
') (a : Rˣ) : χ a * gaussSum χ (mulShift ψ a) = gaussSum χ ψ
· 使用定理 `AddChar.inv_mulShift`：inv_mulShift (ψ : AddChar R M) : ψ⁻¹ = mulShift ψ 
(-1)

--- 原说明 ---
When `χ` is a nontrivial quadratic character, then the square of `gaussSum χ ψ`
is `χ(-1)` times the cardinality of `R`.
-/
theorem gaussSum_sq {χ : MulChar R R'} (hχ₁ : χ ≠ 1) (hχ₂ : IsQuadratic χ)
    {ψ : AddChar R R'} (hψ : IsPrimitive ψ) :
    gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R := by
  rw [pow_two, ← gaussSum_mul_gaussSum_eq_card hχ₁ hψ, hχ₂.inv, mul_rotate']
  congr
  rw [mul_comm, ← gaussSum_mulShift _ _ (-1 : Rˣ), inv_mulShift]
  rfl

end GaussSumProd

/-!
### Gauss sums and Frobenius
-/

section gaussSum_frob

variable {R : Type u} [CommRing R] [Fintype R] {R' : Type v} [CommRing R']

-- We assume that the target ring `R'` has prime characteristic `p`.
variable (p : ℕ) [fp : Fact p.Prime] [hch : CharP R' p]

/-- When `R'` has prime characteristic `p`, then the `p`th power of the Gauss sum
of `χ` and `ψ` is the Gauss sum of `χ^p` and `ψ^p`. -/
/-
**gaussSum_frob** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaussSum_frob (χ : MulChar R R') (ψ : AddChar R R') : gaussSum χ ψ ^ p = g
aussSum (χ ^ p) (ψ ^ p)
参数：χ : MulChar R R'；ψ : AddChar R R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `frobenius_def`：frobenius_def : frobenius R p x = x ^ p
· 使用定理 `gaussSum.eq_1`：∀ {R : Type u} [inst : CommRing R] [inst_1 : Fintype R] {
R' : Type v} [inst_2 : CommRing R'] (χ : MulChar R R')   (ψ : AddChar R R'), gau
ssS…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulChar.pow_apply'`：pow_apply' (χ : MulChar R R') {n : Nat} (hn : n != 0
) (a : R) : (χ ^ n) a = χ a ^ n
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …

--- 原说明 ---
When `R'` has prime characteristic `p`, then the `p`th power of the Gauss sum
of `χ` and `ψ` is the Gauss sum of `χ^p` and `ψ^p`.
-/
theorem gaussSum_frob (χ : MulChar R R') (ψ : AddChar R R') :
    gaussSum χ ψ ^ p = gaussSum (χ ^ p) (ψ ^ p) := by
  rw [← frobenius_def, gaussSum, gaussSum, map_sum]
  simp_rw [pow_apply' χ fp.1.ne_zero, map_mul, frobenius_def]
  rfl

/-- For a quadratic character `χ` and when the characteristic `p` of the target ring
is a unit in the source ring, the `p`th power of the Gauss sum of `χ` and `ψ` is
`χ p` times the original Gauss sum. -/
/-
**MulChar.IsQuadratic.gaussSum_frob** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulChar.IsQuadratic.gaussSum_frob (hp : IsUnit (p : R)) {χ : MulChar R R'}
 (hχ : IsQuadratic χ) (ψ : AddChar R R') : gaussSum χ ψ ^ p = χ p * gaussSum χ ψ
参数：hp : IsUnit (p : R)；hχ : IsQuadratic χ；ψ : AddChar R R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gaussSum_frob`：gaussSum_frob (χ : MulChar R R') (ψ : AddChar R R') : gau
ssSum χ ψ ^ p = gaussSum (χ ^ p) (ψ ^ p)
· 使用定理 `AddChar.pow_mulShift`：pow_mulShift (ψ : AddChar R M) (n : Nat) : ψ ^ n =
 mulShift ψ n
· 使用定理 `MulChar.IsQuadratic.pow_char`：∀ {R : Type u_1} [inst : CommMonoid R] {R'
 : Type u_2} [inst_1 : CommRing R'] {χ : MulChar R R'},   χ.IsQuadratic → ∀ (p :
 ℕ) [hp : Fact (Na…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gaussSum_mulShift`：gaussSum_mulShift (χ : MulChar R R') (ψ : AddChar R R
') (a : Rˣ) : χ a * gaussSum χ (mulShift ψ a) = gaussSum χ ψ
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `MulChar.pow_apply'`：pow_apply' (χ : MulChar R R') {n : Nat} (hn : n != 0
) (a : R) : (χ ^ n) a = χ a ^ n
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MulChar.IsQuadratic.sq_eq_one`：∀ {R : Type u_1} [inst : CommMonoid R] {R
' : Type u_2} [inst_1 : CommRing R'] {χ : MulChar R R'},   χ.IsQuadratic → χ ^ 2
 = 1
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
For a quadratic character `χ` and when the characteristic `p` of the target ring
is a unit in the source ring, the `p`th power of the Gauss sum of `χ` and `ψ` is
`χ p` times the original Gauss sum.
-/
theorem MulChar.IsQuadratic.gaussSum_frob (hp : IsUnit (p : R)) {χ : MulChar R R'}
    (hχ : IsQuadratic χ) (ψ : AddChar R R') :
    gaussSum χ ψ ^ p = χ p * gaussSum χ ψ := by
  rw [_root_.gaussSum_frob, pow_mulShift, hχ.pow_char p, ← gaussSum_mulShift χ ψ hp.unit,
    ← mul_assoc, hp.unit_spec, ← pow_two, ← pow_apply' _ two_ne_zero, hχ.sq_eq_one, ← hp.unit_spec,
    one_apply_coe, one_mul]

/-- For a quadratic character `χ` and when the characteristic `p` of the target ring
is a unit in the source ring and `n` is a natural number, the `p^n`th power of the Gauss
sum of `χ` and `ψ` is `χ (p^n)` times the original Gauss sum. -/
/-
**MulChar.IsQuadratic.gaussSum_frob_iter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulChar.IsQuadratic.gaussSum_frob_iter (n : Nat) (hp : IsUnit (p : R)) {χ 
: MulChar R R'} (hχ : IsQuadratic χ) (ψ : AddChar R R') : gaussSum χ ψ ^ p ^ n =
 χ ((p : R) ^ n) * gaussSum χ ψ
参数：n : Nat；hp : IsUnit (p : R)；hχ : IsQuadratic χ；ψ : AddChar R R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `MulChar.map_one`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} 
[inst_1 : CommMonoidWithZero R'] (χ : MulChar R R'), χ 1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `MulChar.IsQuadratic.gaussSum_frob`：MulChar.IsQuadratic.gaussSum_frob (hp
 : IsUnit (p : R)) {χ : MulChar R R'} (hχ : IsQuadratic χ) (ψ : AddChar R R') : 
gaussSum χ ψ ^ p = χ p …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `MulChar.pow_apply'`：pow_apply' (χ : MulChar R R') {n : Nat} (hn : n != 0
) (a : R) : (χ ^ n) a = χ a ^ n
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `MulChar.IsQuadratic.pow_char`：∀ {R : Type u_1} [inst : CommMonoid R] {R'
 : Type u_2} [inst_1 : CommRing R'] {χ : MulChar R R'},   χ.IsQuadratic → ∀ (p :
 ℕ) [hp : Fact (Na…

--- 原说明 ---
For a quadratic character `χ` and when the characteristic `p` of the target ring
is a unit in the source ring and `n` is a natural number, the `p^n`th power of t
he Gauss
sum of `χ` and `ψ` is `χ (p^n)` times the original Gauss sum.
-/
theorem MulChar.IsQuadratic.gaussSum_frob_iter (n : ℕ) (hp : IsUnit (p : R)) {χ : MulChar R R'}
    (hχ : IsQuadratic χ) (ψ : AddChar R R') :
    gaussSum χ ψ ^ p ^ n = χ ((p : R) ^ n) * gaussSum χ ψ := by
  induction n with
  | zero => rw [pow_zero, pow_one, pow_zero, MulChar.map_one, one_mul]
  | succ n ih =>
    rw [pow_succ, pow_mul, ih, mul_pow, hχ.gaussSum_frob _ hp, ← mul_assoc, pow_succ, map_mul,
      ← pow_apply' χ fp.1.ne_zero ((p : R) ^ n), hχ.pow_char p]

end gaussSum_frob

/-!
### Values of quadratic characters
-/

section GaussSumValues

variable {R : Type u} [CommRing R] [Fintype R] {R' : Type v} [CommRing R'] [IsDomain R']

/-- If the square of the Gauss sum of a quadratic character is `χ(-1) * #R`,
then we get, for all `n : ℕ`, the relation `(χ(-1) * #R) ^ (p^n/2) = χ(p^n)`,
where `p` is the (odd) characteristic of the target ring `R'`.
This version can be used when `R` is not a field, e.g., `ℤ/8ℤ`. -/
/-
**Char.card_pow_char_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Char.card_pow_char_pow {χ : MulChar R R'} (hχ : IsQuadratic χ) (ψ : AddCha
r R R') (p n : Nat) [fp : Fact p.Prime] [hch : CharP R' p] (hp : IsUnit (p : R))
 (hp' : p != 2) (hg : gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R) : (χ (-1) * Fi
ntype.card R) ^ (p ^ n / 2) = χ ((p : R) ^ n)
参数：hχ : IsQuadratic χ；ψ : AddChar R R'；p n : Nat；hp : IsUnit (p : R)；hp' : p != 
2；hg : gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isUnit_prime_of_dvd_card`：not_isUnit_prime_of_dvd_card {R : Type*} [
CommRing R] [Fintype R] {p : Nat} [Fact p.Prime] (hp : p ∣ Fintype.card R) : ¬Is
Unit (p : R)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `IsUnit.neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg α] 
{a : α}, IsUnit a → IsUnit (-a)
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `MulChar.IsQuadratic.gaussSum_frob_iter`：MulChar.IsQuadratic.gaussSum_fro
b_iter (n : Nat) (hp : IsUnit (p : R)) {χ : MulChar R R'} (hχ : IsQuadratic χ) (
ψ : AddChar R R') : gaussSum…
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `Nat.two_mul_div_two_add_one_of_odd`：two_mul_div_two_add_one_of_odd (h : 
Odd n) : 2 * (n / 2) + 1 = n
· 使用引理 `Odd.pow`：Odd.pow {n : Nat} (ha : Odd a) : Odd (a ^ n)
· 使用定理 `Nat.Prime.eq_two_or_odd'`：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ Odd p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
If the square of the Gauss sum of a quadratic character is `χ(-1) * #R`,
then we get, for all `n : ℕ`, the relation `(χ(-1) * #R) ^ (p^n/2) = χ(p^n)`,
where `p` is the (odd) characteristic of the target ring `R'`.
This version can be used when `R` is not a field, e.g., `ℤ/8ℤ`.
-/
theorem Char.card_pow_char_pow {χ : MulChar R R'} (hχ : IsQuadratic χ) (ψ : AddChar R R') (p n : ℕ)
    [fp : Fact p.Prime] [hch : CharP R' p] (hp : IsUnit (p : R)) (hp' : p ≠ 2)
    (hg : gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R) :
    (χ (-1) * Fintype.card R) ^ (p ^ n / 2) = χ ((p : R) ^ n) := by
  have : gaussSum χ ψ ≠ 0 := by
    intro hf
    rw [hf, zero_pow two_ne_zero, eq_comm, mul_eq_zero] at hg
    exact not_isUnit_prime_of_dvd_card
        ((CharP.cast_eq_zero_iff R' p _).mp <| hg.resolve_left (isUnit_one.neg.map χ).ne_zero) hp
  rw [← hg]
  apply mul_right_cancel₀ this
  rw [← hχ.gaussSum_frob_iter p n hp ψ, ← pow_mul, ← pow_succ,
    Nat.two_mul_div_two_add_one_of_odd (fp.1.eq_two_or_odd'.resolve_left hp').pow]

/-- When `F` and `F'` are finite fields and `χ : F → F'` is a nontrivial quadratic character,
then `(χ(-1) * #F)^(#F'/2) = χ #F'`. -/
/-
**Char.card_pow_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Char.card_pow_card {F : Type*} [Field F] [Fintype F] {F' : Type*} [Field F
'] [Fintype F'] {χ : MulChar F F'} (hχ₁ : χ != 1) (hχ₂ : IsQuadratic χ) (hch₁ : 
ringChar F' != ringChar F) (hch₂ : ringChar F' != 2) : (χ (-1) * Fintype.card F)
 ^ (Fintype.card F' / 2) = χ (Fintype.card F')
参数：hχ₁ : χ != 1；hχ₂ : IsQuadratic χ；hch₁ : ringChar F' != ringChar F；hch₂ : ring
Char F' != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.ringChar_eq`：Algebra.ringChar_eq : ringChar K = ringChar L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Char.card_pow_char_pow`：Char.card_pow_char_pow {χ : MulChar R R'} (hχ : 
IsQuadratic χ) (ψ : AddChar R R') (p n : Nat) [fp : Fact p.Prime] [hch : CharP R
' p] (hp : I…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `MulChar.IsQuadratic.comp`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommRing R'] {R'' : Type u_3} [inst_2 : CommRing R'']   {χ : 
MulChar R R'},…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_iff_not_dvd_char`：isUnit_iff_not_dvd_char (R : Type*) [CommRing R
] (p : Nat) [Fact p.Prime] [Finite R] : IsUnit (p : R) ↔ ¬p ∣ ringChar R
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `gaussSum_sq`：gaussSum_sq {χ : MulChar R R'} (hχ₁ : χ != 1) (hχ₂ : IsQuad
ratic χ) {ψ : AddChar R R'} (hψ : IsPrimitive ψ) : gaussSum χ ψ ^ 2 = χ (-1) * F
i…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MulChar.ringHomComp_ne_one_iff`：ringHomComp_ne_one_iff {f : R' ->+* R''}
 (hf : Function.Injective f) {χ : MulChar R R'} : χ.ringHomComp f != 1 ↔ χ != 1
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
When `F` and `F'` are finite fields and `χ : F → F'` is a nontrivial quadratic c
haracter,
then `(χ(-1) * #F)^(#F'/2) = χ #F'`.
-/
theorem Char.card_pow_card {F : Type*} [Field F] [Fintype F] {F' : Type*} [Field F'] [Fintype F']
    {χ : MulChar F F'} (hχ₁ : χ ≠ 1) (hχ₂ : IsQuadratic χ)
    (hch₁ : ringChar F' ≠ ringChar F) (hch₂ : ringChar F' ≠ 2) :
    (χ (-1) * Fintype.card F) ^ (Fintype.card F' / 2) = χ (Fintype.card F') := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  obtain ⟨n', hp', hc'⟩ := FiniteField.card F' (ringChar F')
  let ψ := FiniteField.primitiveChar F F' hch₁
  let FF' := CyclotomicField ψ.n F'
  have hchar := Algebra.ringChar_eq F' FF'
  apply (algebraMap F' FF').injective
  rw [map_pow, map_mul, map_natCast, hc', hchar, Nat.cast_pow]
  simp only [← MulChar.ringHomComp_apply]
  have := Fact.mk hp'
  have := Fact.mk (hchar.subst hp')
  rw [Ne, ← Nat.prime_dvd_prime_iff_eq hp' hp, ← isUnit_iff_not_dvd_char, hchar] at hch₁
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
/-- For every finite field `F` of odd characteristic, we have `2^(#F/2) = χ₈ #F` in `F`. -/
/-
**FiniteField.two_pow_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteField.two_pow_card {F : Type*} [Fintype F] [Field F] (hF : ringChar 
F != 2) : (2 : F) ^ (Fintype.card F / 2) = χ₈ (Fintype.card F)
参数：hF : ringChar F != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Ring.two_ne_zero`：∀ {R : Type u_2} [inst : NonAssocSemiring R] [Nontrivi
al R], ringChar R ≠ 2 → 2 ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `Algebra.ringChar_eq`：Algebra.ringChar_eq : ringChar K = ringChar L
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUnit_iff_not_dvd_char`：isUnit_iff_not_dvd_char (R : Type*) [CommRing R
] (p : Nat) [Fact p.Prime] [Finite R] : IsUnit (p : R) ↔ ¬p ∣ ringChar R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ZMod.ringChar_zmod_n`：ringChar_zmod_n (n : Nat) : ringChar (ZMod n) = n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Nat.Prime.dvd_of_dvd_pow`：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ^ n → p ∣ m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sq_eq_one_iff`：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R]
, a ^ 2 = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `AddChar.map_nsmul_eq_pow`：map_nsmul_eq_pow (ψ : AddChar A M) (n : Nat) (
x : A) : ψ (n • x) = ψ x ^ n
· 使用定理 `AddChar.IsPrimitive.zmod_char_eq_one_iff`：∀ {C : Type v} [inst : CommMon
oid C] (n : ℕ) [NeZero n] {ψ : AddChar (ZMod n) C},   ψ.IsPrimitive → ∀ (a : ZMo
d n), ψ a = 1 ↔ a = 0
（共 124 条，此处仅展示前 30 条）

--- 原说明 ---
For every finite field `F` of odd characteristic, we have `2^(#F/2) = χ₈ #F` in 
`F`.
-/
theorem FiniteField.two_pow_card {F : Type*} [Fintype F] [Field F] (hF : ringChar F ≠ 2) :
    (2 : F) ^ (Fintype.card F / 2) = χ₈ (Fintype.card F) := by
  have hp2 (n : ℕ) : (2 ^ n : F) ≠ 0 := pow_ne_zero n (Ring.two_ne_zero hF)
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- we work in `FF`, the eighth cyclotomic field extension of `F`
  let FF := CyclotomicField 8 F
  have hchar := Algebra.ringChar_eq F FF
  have FFp := hchar.subst hp
  have := Fact.mk FFp
  have hFF := hchar ▸ hF -- `ringChar FF ≠ 2`
  have hu : IsUnit (ringChar FF : ZMod 8) := by
    rw [isUnit_iff_not_dvd_char, ringChar_zmod_n]
    rw [Ne, ← Nat.prime_dvd_prime_iff_eq FFp Nat.prime_two] at hFF
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
  have h₁ : (fun (a : Fin 8) ↦ ↑(χ₈ a) * τ ^ (a : ℕ)) = fun a ↦ χ a * ↑(ψ₈char a) := by
    ext1; congr; apply pow_one
  have hg₁ : gaussSum χ ψ₈char = 2 * (τ - τ ^ 3) := by
    rw [gaussSum, ← h₁, Fin.sum_univ_eight,
      -- evaluate `χ₈`
      show χ₈ 0 = 0 from rfl, show χ₈ 1 = 1 from rfl, show χ₈ 2 = 0 from rfl,
      show χ₈ 3 = -1 from rfl, show χ₈ 4 = 0 from rfl, show χ₈ 5 = -1 from rfl,
      show χ₈ 6 = 0 from rfl, show χ₈ 7 = 1 from rfl,
      -- normalize exponents
      show ((3 : Fin 8) : ℕ) = 3 from rfl, show ((5 : Fin 8) : ℕ) = 5 from rfl,
      show ((7 : Fin 8) : ℕ) = 7 from rfl]
    simp only [Int.cast_zero, zero_mul, Int.cast_one, Fin.val_one, pow_one, one_mul, zero_add,
      Fin.val_two, add_zero, Int.reduceNeg, Int.cast_neg]
    linear_combination (τ ^ 3 - τ) * τ_spec
  have hg : gaussSum χ ψ₈char ^ 2 = χ (-1) * Fintype.card (ZMod 8) := by
    rw [hχ, one_mul, ZMod.card, Nat.cast_ofNat, hg₁]
    linear_combination (4 * τ ^ 2 - 8) * τ_spec
  -- this allows us to apply `card_pow_char_pow` to our situation
  have h := Char.card_pow_char_pow (R := ZMod 8) hq ψ₈char (ringChar FF) n hu hFF hg
  rw [ZMod.card, ← hchar, hχ, one_mul, ← hc, ← Nat.cast_pow (ringChar F), ← hc] at h
  -- finally, we change `2` to `8` on the left-hand side
  convert_to (8 : F) ^ (Fintype.card F / 2) = _
  · rw [(by norm_num : (8 : F) = 2 ^ 2 * 2), mul_pow,
      (FiniteField.isSquare_iff hF <| hp2 2).mp ⟨2, pow_two 2⟩, one_mul]
  apply (algebraMap F FF).injective
  simpa only [map_pow, map_ofNat, map_intCast, Nat.cast_ofNat] using! h

end GaussSumTwo

