/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# `IsReduced` is a local property

In this file, we prove that `IsReduced` is a local property.

## Main results

Let `R` be a commutative ring, `M` be a submonoid of `R`.

* `isReduced_localizationPreserves` :  `M⁻¹R` is reduced if `R` is reduced.
* `isReduced_ofLocalizationMaximal` : `R` is reduced if `Rₘ` is reduced for all maximal ideal `m`.

-/

public section

/-- `M⁻¹R` is reduced if `R` is reduced. -/
/-
**isReduced_localizationPreserves** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isReduced_localizationPreserves : LocalizationPreserves fun R _ => IsReduc
ed R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsNilpotent.eq_zero`：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced
 R] (h : IsNilpotent x) : x = 0
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `IsLocalization.map_eq_zero_iff`：map_eq_zero_iff (r : R) : algebraMap R S
 r = 0 ↔ exists m : M, ↑m * r = 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
`M⁻¹R` is reduced if `R` is reduced.
-/
theorem isReduced_localizationPreserves : LocalizationPreserves fun R _ => IsReduced R := by
  introv R _ _
  constructor
  rintro x ⟨_ | n, e⟩
  · simpa using congr_arg (· * x) e
  obtain ⟨⟨y, m⟩, hx⟩ := IsLocalization.surj M x
  dsimp only at hx
  let hx' := congr_arg (· ^ n.succ) hx
  simp only [mul_pow, e, zero_mul, ← map_pow] at hx'
  rw [← (algebraMap R S).map_zero] at hx'
  obtain ⟨m', hm'⟩ := (IsLocalization.eq_iff_exists M S).mp hx'
  apply_fun (· * (m' : R) ^ n) at hm'
  simp only [mul_assoc, zero_mul, mul_zero] at hm'
  rw [← mul_left_comm, ← pow_succ', ← mul_pow] at hm'
  replace hm' := IsNilpotent.eq_zero ⟨_, hm'.symm⟩
  rw [← (IsLocalization.map_units S m).mul_left_inj, hx, zero_mul,
    IsLocalization.map_eq_zero_iff M]
  exact ⟨m', by rw [← hm', mul_comm]⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [CommRing R] (M : Submonoid R) [IsReduced R] : IsReduced (Localization M) :=
  isReduced_localizationPreserves M _ inferInstance

/-- `R` is reduced if `Rₘ` is reduced for all maximal ideal `m`. -/
/-
**isReduced_ofLocalizationMaximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isReduced_ofLocalizationMaximal : OfLocalizationMaximal fun R _ => IsReduc
ed R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_of_localization`：eq_zero_of_localization (r : R) (h : forall (J 
: Ideal R) (_ : J.IsMaximal), algebraMap R (Localization.AtPrime J) r = 0) : r =
 0
· 使用定理 `IsNilpotent.eq_zero`：IsNilpotent.eq_zero [Zero R] [Pow R Nat] [IsReduced
 R] (h : IsNilpotent x) : x = 0
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsNilpotent.map`：IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {
r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpot
ent r…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
`R` is reduced if `Rₘ` is reduced for all maximal ideal `m`.
-/
theorem isReduced_ofLocalizationMaximal : OfLocalizationMaximal fun R _ => IsReduced R := by
  introv R h
  constructor
  intro x hx
  apply eq_zero_of_localization
  intro J hJ
  specialize h J hJ
  exact (hx.map <| algebraMap R <| Localization.AtPrime J).eq_zero
