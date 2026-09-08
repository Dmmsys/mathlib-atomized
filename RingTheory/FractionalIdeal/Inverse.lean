/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# Inverse operator for fractional ideals

This file defines the notation `I⁻¹` where `I` is a not necessarily invertible fractional ideal.
Note that this is somewhat misleading notation in case `I` is not invertible.
The theorem that all nonzero fractional ideals are invertible in a Dedekind domain can be found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Main definitions

- `FractionalIdeal.instInv` defines `I⁻¹ := 1 / I`.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

fractional ideal, invertible ideal
-/

public section

assert_not_exists IsDedekindDomain

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

namespace FractionalIdeal

variable {R₁ : Type*} [CommRing R₁] [IsDomain R₁] [Algebra R₁ K] [IsFractionRing R₁ K]
variable {I J : FractionalIdeal R₁⁰ K}

/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inv (FractionalIdeal R₁⁰ K) := ⟨fun I => 1 / I⟩
/-
**FractionalIdeal.inv_eq** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：inv_eq : I⁻¹ = 1 / I
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_eq : I⁻¹ = 1 / I := rfl
/-
**FractionalIdeal.inv_zero'** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：inv_zero' : (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.div_zero`：div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 =
 0
-/
theorem inv_zero' : (0 : FractionalIdeal R₁⁰ K)⁻¹ = 0 := div_zero
/-
**FractionalIdeal.inv_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：inv_of_ne_zero {J : FractionalIdeal R₁⁰ K} (h : J != 0) : J⁻¹ = ⟨(1 : Frac
tionalIdeal R₁⁰ K) / J, isFractional_div_of_ne_zero h⟩
参数：h : J != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.div_of_ne_zero`：div_of_ne_zero {I J : FractionalIdeal R₁
⁰ K} (h : J != 0) : I / J = ⟨I / J, isFractional_div_of_ne_zero h⟩
-/
theorem inv_of_ne_zero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    J⁻¹ = ⟨(1 : FractionalIdeal R₁⁰ K) / J, isFractional_div_of_ne_zero h⟩ := div_of_ne_zero h
/-
**FractionalIdeal.coe_inv_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：coe_inv_of_ne_zero {J : FractionalIdeal R₁⁰ K} (h : J != 0) : (↑J⁻¹ : Subm
odule R₁ K) = IsLocalization.coeSubmodule K ⊤ / (J : Submodule R₁ K)
参数：h : J != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.isFractional_div_of_ne_zero`：isFractional_div_of_ne_zero
 {I J : FractionalIdeal R₁⁰ K} (h : J != 0) : IsFractional R₁⁰ (I / J : Submodul
e R₁ K)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.inv_of_ne_zero`：inv_of_ne_zero {J : FractionalIdeal R₁⁰ 
K} (h : J != 0) : J⁻¹ = ⟨(1 : FractionalIdeal R₁⁰ K) / J, isFractional_div_of_ne
_zero h⟩
· 使用定理 `FractionalIdeal.coe_one`：coe_one : (↑(1 : FractionalIdeal S P) : Submodu
le R P) = 1
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalization.coeSubmodule_top`：coeSubmodule_top : coeSubmodule S (⊤ : 
Ideal R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_inv_of_ne_zero {J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    (↑J⁻¹ : Submodule R₁ K) = IsLocalization.coeSubmodule K ⊤ / (J : Submodule R₁ K) := by
  simp_rw [inv_of_ne_zero _ h, coe_one, coe_mk, IsLocalization.coeSubmodule_top]

variable {K}
/-
**FractionalIdeal.mem_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：mem_inv_iff (hI : I != 0) {x : K} : x in I⁻¹ ↔ forall y in I, x * y in (1 
: FractionalIdeal R₁⁰ K)
参数：hI : I != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.mem_div_iff_of_ne_zero`：mem_div_iff_of_ne_zero {I J : Fr
actionalIdeal R₁⁰ K} (h : J != 0) {x} : x in I / J ↔ forall y in J, x * y in I
-/
theorem mem_inv_iff (hI : I ≠ 0) {x : K} : x ∈ I⁻¹ ↔ ∀ y ∈ I, x * y ∈ (1 : FractionalIdeal R₁⁰ K) :=
  mem_div_iff_of_ne_zero hI
/-
**FractionalIdeal.inv_anti_mono** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：inv_anti_mono (hI : I != 0) (hJ : J != 0) (hIJ : I <= J) : J⁻¹ <= I⁻¹
参数：hI : I != 0；hJ : J != 0；hIJ : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FractionalIdeal.mem_inv_iff`：mem_inv_iff (hI : I != 0) {x : K} : x in I⁻
¹ ↔ forall y in I, x * y in (1 : FractionalIdeal R₁⁰ K)
-/
theorem inv_anti_mono (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ≤ J) : J⁻¹ ≤ I⁻¹ := by
  intro x
  simp only [mem_inv_iff hJ, mem_inv_iff hI]
  exact fun h y hy => h y (hIJ hy)
/-
**FractionalIdeal.le_self_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：le_self_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I <= (1 : FractionalIdea
l R₁⁰ K)) : I <= I * I⁻¹
参数：hI : I <= (1 : FractionalIdeal R₁⁰ K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.le_self_mul_one_div`：le_self_mul_one_div {I : Fractional
Ideal R₁⁰ K} (hI : I <= (1 : FractionalIdeal R₁⁰ K)) : I <= I * (1 / I)
-/
theorem le_self_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) :
    I ≤ I * I⁻¹ :=
  le_self_mul_one_div hI

variable (K)
/-
**FractionalIdeal.coe_ideal_le_self_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Fractiona
lIdeal`。
形式化陈述：coe_ideal_le_self_mul_inv (I : Ideal R₁) : (I : FractionalIdeal R₁⁰ K) <= 
I * (I : FractionalIdeal R₁⁰ K)⁻¹
参数：I : Ideal R₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.le_self_mul_inv`：le_self_mul_inv {I : FractionalIdeal R₁
⁰ K} (hI : I <= (1 : FractionalIdeal R₁⁰ K)) : I <= I * I⁻¹
· 使用定理 `FractionalIdeal.coeIdeal_le_one`：coeIdeal_le_one {I : Ideal R} : (I : Fr
actionalIdeal S P) <= 1
-/
theorem coe_ideal_le_self_mul_inv (I : Ideal R₁) :
    (I : FractionalIdeal R₁⁰ K) ≤ I * (I : FractionalIdeal R₁⁰ K)⁻¹ :=
  le_self_mul_inv coeIdeal_le_one

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
/-
**FractionalIdeal.right_inverse_eq** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：right_inverse_eq (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = I⁻¹
参数：I J : FractionalIdeal R₁⁰ K；h : I * J = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.eq_one_div_of_mul_eq_one_right`：eq_one_div_of_mul_eq_one
_right (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = 1 / I

--- 原说明 ---
`I⁻¹` is the inverse of `I` if `I` has an inverse.
-/
theorem right_inverse_eq (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = I⁻¹ :=
  eq_one_div_of_mul_eq_one_right _ _ h
/-
**FractionalIdeal.mul_inv_cancel_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`
。
形式化陈述：mul_inv_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ exists J, I
 * J = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.right_inverse_eq`：right_inverse_eq (I J : FractionalIdea
l R₁⁰ K) (h : I * J = 1) : J = I⁻¹
-/
theorem mul_inv_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
  ⟨fun h => ⟨I⁻¹, h⟩, fun ⟨J, hJ⟩ => by rwa [← right_inverse_eq K I J hJ]⟩
/-
**FractionalIdeal.mul_inv_cancel_iff_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Fractiona
lIdeal`。
形式化陈述：mul_inv_cancel_iff_isUnit {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ IsUn
it I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `FractionalIdeal.mul_inv_cancel_iff`：mul_inv_cancel_iff {I : FractionalId
eal R₁⁰ K} : I * I⁻¹ = 1 ↔ exists J, I * J = 1
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
-/
theorem mul_inv_cancel_iff_isUnit {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ IsUnit I :=
  (mul_inv_cancel_iff K).trans isUnit_iff_exists_inv.symm

variable {K' : Type*} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

@[simp]
/-
**FractionalIdeal.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：∀ (K : Type u_3) [inst : Field K] {R₁ : Type u_4} [inst_1 : CommRing R₁] [
inst_2 : IsDomain R₁] [inst_3 : Algebra R₁ K]   [inst_4 : IsFractionRing R₁ K] {
K' : Type u_5} [inst_5 : Field K'] [inst_6 : Algebra R₁ K']   [inst_7 : IsFracti
onRing R₁ K'] (I : FractionalIdeal (nonZeroDivisors R₁) K) (h : K ≃ₐ[R₁] K'),   
FractionalIdeal.map (↑h) I⁻¹ = (FractionalIdeal.map (↑h) I)⁻¹
参数：K : Type u_3；I : FractionalIdeal (nonZeroDivisors R₁) K；h : K ≃ₐ[R₁] K'；↑h；Fr
actionalIdeal.map (↑h) I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.inv_eq`：inv_eq : I⁻¹ = 1 / I
· 使用定理 `FractionalIdeal.map_div`：∀ {R₁ : Type u_3} [inst : CommRing R₁] {K : Typ
e u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K]   [inst_3 : IsFractionRing R₁ 
K] [inst_4 : …
· 使用定理 `FractionalIdeal.map_one`：∀ {R : Type u_1} [inst : CommRing R] {S : Submo
noid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P]   {P' : Type
 u_3} [inst_3…
-/
protected theorem map_inv (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    I⁻¹.map (h : K →ₐ[R₁] K') = (I.map h)⁻¹ := by
  rw [inv_eq, FractionalIdeal.map_div, FractionalIdeal.map_one, inv_eq]

open Submodule Submodule.IsPrincipal

@[simp]
/-
**FractionalIdeal.spanSingleton_inv** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：spanSingleton_inv (x : K) : (spanSingleton R₁⁰ x)⁻¹ = spanSingleton _ x⁻¹
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.one_div_spanSingleton`：one_div_spanSingleton (x : K) : 1
 / spanSingleton R₁⁰ x = spanSingleton R₁⁰ x⁻¹
-/
theorem spanSingleton_inv (x : K) : (spanSingleton R₁⁰ x)⁻¹ = spanSingleton _ x⁻¹ :=
  one_div_spanSingleton x
/-
**FractionalIdeal.spanSingleton_div_spanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Fra
ctionalIdeal`。
形式化陈述：spanSingleton_div_spanSingleton (x y : K) : spanSingleton R₁⁰ x / spanSing
leton R₁⁰ y = spanSingleton R₁⁰ (x / y)
参数：x y : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.div_spanSingleton`：div_spanSingleton (J : FractionalIdea
l R₁⁰ K) (d : K) : J / spanSingleton R₁⁰ d = spanSingleton R₁⁰ d⁻¹ * J
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `FractionalIdeal.spanSingleton_mul_spanSingleton`：spanSingleton_mul_spanS
ingleton (x y : P) : spanSingleton S x * spanSingleton S y = spanSingleton S (x 
* y)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem spanSingleton_div_spanSingleton (x y : K) :
    spanSingleton R₁⁰ x / spanSingleton R₁⁰ y = spanSingleton R₁⁰ (x / y) := by
  rw [div_spanSingleton, mul_comm, spanSingleton_mul_spanSingleton, div_eq_mul_inv]
/-
**FractionalIdeal.spanSingleton_div_self** 是 Mathlib 中的一个定理，位于命名空间 `FractionalId
eal`。
形式化陈述：spanSingleton_div_self {x : K} (hx : x != 0) : spanSingleton R₁⁰ x / spanS
ingleton R₁⁰ x = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.spanSingleton_div_spanSingleton`：spanSingleton_div_spanS
ingleton (x y : K) : spanSingleton R₁⁰ x / spanSingleton R₁⁰ y = spanSingleton R
₁⁰ (x / y)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `FractionalIdeal.spanSingleton_one`：spanSingleton_one : spanSingleton S (
1 : P) = 1
-/
theorem spanSingleton_div_self {x : K} (hx : x ≠ 0) :
    spanSingleton R₁⁰ x / spanSingleton R₁⁰ x = 1 := by
  rw [spanSingleton_div_spanSingleton, div_self hx, spanSingleton_one]
/-
**FractionalIdeal.coe_ideal_span_singleton_div_self** 是 Mathlib 中的一个定理，位于命名空间 `F
ractionalIdeal`。
形式化陈述：coe_ideal_span_singleton_div_self {x : R₁} (hx : x != 0) : (Ideal.span ({x
} : Set R₁) : FractionalIdeal R₁⁰ K) / Ideal.span ({x} : Set R₁) = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coeIdeal_span_singleton`：coeIdeal_span_singleton (x : R)
 : (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebr
aMap R P x)
· 使用定理 `FractionalIdeal.spanSingleton_div_self`：spanSingleton_div_self {x : K} (
hx : x != 0) : spanSingleton R₁⁰ x / spanSingleton R₁⁰ x = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
-/
theorem coe_ideal_span_singleton_div_self {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K) / Ideal.span ({x} : Set R₁) = 1 := by
  rw [coeIdeal_span_singleton,
    spanSingleton_div_self K <|
      (map_ne_zero_iff _ <| FaithfulSMul.algebraMap_injective R₁ K).mpr hx]
/-
**FractionalIdeal.spanSingleton_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：spanSingleton_mul_inv {x : K} (hx : x != 0) : spanSingleton R₁⁰ x * (spanS
ingleton R₁⁰ x)⁻¹ = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.spanSingleton_inv`：spanSingleton_inv (x : K) : (spanSing
leton R₁⁰ x)⁻¹ = spanSingleton _ x⁻¹
· 使用定理 `FractionalIdeal.spanSingleton_mul_spanSingleton`：spanSingleton_mul_spanS
ingleton (x y : P) : spanSingleton S x * spanSingleton S y = spanSingleton S (x 
* y)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `FractionalIdeal.spanSingleton_one`：spanSingleton_one : spanSingleton S (
1 : P) = 1
-/
theorem spanSingleton_mul_inv {x : K} (hx : x ≠ 0) :
    spanSingleton R₁⁰ x * (spanSingleton R₁⁰ x)⁻¹ = 1 := by
  rw [spanSingleton_inv, spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hx, spanSingleton_one]
/-
**FractionalIdeal.coe_ideal_span_singleton_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Fr
actionalIdeal`。
形式化陈述：coe_ideal_span_singleton_mul_inv {x : R₁} (hx : x != 0) : (Ideal.span ({x}
 : Set R₁) : FractionalIdeal R₁⁰ K) * (Ideal.span ({x} : Set R₁) : FractionalIde
al R₁⁰ K)⁻¹ = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.coeIdeal_span_singleton`：coeIdeal_span_singleton (x : R)
 : (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebr
aMap R P x)
· 使用定理 `FractionalIdeal.spanSingleton_mul_inv`：spanSingleton_mul_inv {x : K} (hx
 : x != 0) : spanSingleton R₁⁰ x * (spanSingleton R₁⁰ x)⁻¹ = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
-/
theorem coe_ideal_span_singleton_mul_inv {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K) *
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K)⁻¹ = 1 := by
  rw [coeIdeal_span_singleton,
    spanSingleton_mul_inv K <|
      (map_ne_zero_iff _ <| FaithfulSMul.algebraMap_injective R₁ K).mpr hx]
/-
**FractionalIdeal.spanSingleton_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIde
al`。
形式化陈述：spanSingleton_inv_mul {x : K} (hx : x != 0) : (spanSingleton R₁⁰ x)⁻¹ * sp
anSingleton R₁⁰ x = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `FractionalIdeal.spanSingleton_mul_inv`：spanSingleton_mul_inv {x : K} (hx
 : x != 0) : spanSingleton R₁⁰ x * (spanSingleton R₁⁰ x)⁻¹ = 1
-/
theorem spanSingleton_inv_mul {x : K} (hx : x ≠ 0) :
    (spanSingleton R₁⁰ x)⁻¹ * spanSingleton R₁⁰ x = 1 := by
  rw [mul_comm, spanSingleton_mul_inv K hx]
/-
**FractionalIdeal.coe_ideal_span_singleton_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Fr
actionalIdeal`。
形式化陈述：coe_ideal_span_singleton_inv_mul {x : R₁} (hx : x != 0) : (Ideal.span ({x}
 : Set R₁) : FractionalIdeal R₁⁰ K)⁻¹ * Ideal.span ({x} : Set R₁) = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `FractionalIdeal.coe_ideal_span_singleton_mul_inv`：coe_ideal_span_singlet
on_mul_inv {x : R₁} (hx : x != 0) : (Ideal.span ({x} : Set R₁) : FractionalIdeal
 R₁⁰ K) * (Ideal.span ({x} : Set R₁) :…
-/
theorem coe_ideal_span_singleton_inv_mul {x : R₁} (hx : x ≠ 0) :
    (Ideal.span ({x} : Set R₁) : FractionalIdeal R₁⁰ K)⁻¹ * Ideal.span ({x} : Set R₁) = 1 := by
  rw [mul_comm, coe_ideal_span_singleton_mul_inv K hx]
/-
**FractionalIdeal.mul_generator_self_inv** 是 Mathlib 中的一个定理，位于命名空间 `FractionalId
eal`。
形式化陈述：mul_generator_self_inv {R₁ : Type*} [CommRing R₁] [Algebra R₁ K] [IsLocali
zation R₁⁰ K] (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule 
R₁ K)] (h : I != 0) : I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1
参数：I : FractionalIdeal R₁⁰ K；I : Submodule R₁ K；h : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.eq_spanSingleton_of_principal`：eq_spanSingleton_of_princ
ipal (I : FractionalIdeal S P) [IsPrincipal (I : Submodule R P)] : I = spanSingl
eton S (generator (I : Submodule R …
· 使用定理 `FractionalIdeal.spanSingleton_mul_spanSingleton`：spanSingleton_mul_spanS
ingleton (x y : P) : spanSingleton S x * spanSingleton S y = spanSingleton S (x 
* y)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `FractionalIdeal.spanSingleton_zero`：spanSingleton_zero : spanSingleton S
 (0 : P) = 0
· 使用定理 `FractionalIdeal.spanSingleton_one`：spanSingleton_one : spanSingleton S (
1 : P) = 1
-/
theorem mul_generator_self_inv {R₁ : Type*} [CommRing R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
    (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 := by
  -- Rewrite only the `I` that appears alone.
  conv_lhs => congr; rw [eq_spanSingleton_of_principal I]
  rw [spanSingleton_mul_spanSingleton, mul_inv_cancel₀, spanSingleton_one]
  intro generator_I_eq_zero
  apply h
  rw [eq_spanSingleton_of_principal I, generator_I_eq_zero, spanSingleton_zero]
/-
**FractionalIdeal.invertible_of_principal** 是 Mathlib 中的一个定理，位于命名空间 `FractionalI
deal`。
形式化陈述：invertible_of_principal (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal
 (I : Submodule R₁ K)] (h : I != 0) : I * I⁻¹ = 1
参数：I : FractionalIdeal R₁⁰ K；I : Submodule R₁ K；h : I != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.mul_div_self_cancel_iff`：mul_div_self_cancel_iff {I : Fr
actionalIdeal R₁⁰ K} : I * (1 / I) = 1 ↔ exists J, I * J = 1
· 使用定理 `FractionalIdeal.mul_generator_self_inv`：mul_generator_self_inv {R₁ : Typ
e*} [CommRing R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K] (I : FractionalIdeal R₁⁰
 K) [Submodule.IsPrincipal (…
-/
theorem invertible_of_principal (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) : I * I⁻¹ = 1 :=
  mul_div_self_cancel_iff.mpr
    ⟨spanSingleton _ (generator (I : Submodule R₁ K))⁻¹, mul_generator_self_inv _ I h⟩
/-
**FractionalIdeal.invertible_iff_generator_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Fr
actionalIdeal`。
形式化陈述：invertible_iff_generator_nonzero (I : FractionalIdeal R₁⁰ K) [Submodule.Is
Principal (I : Submodule R₁ K)] : I * I⁻¹ = 1 ↔ generator (I : Submodule R₁ K) !
= 0
参数：I : FractionalIdeal R₁⁰ K；I : Submodule R₁ K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FractionalIdeal.ne_zero_of_mul_eq_one`：ne_zero_of_mul_eq_one (I J : Frac
tionalIdeal R₁⁰ K) (h : I * J = 1) : I != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.eq_spanSingleton_of_principal`：eq_spanSingleton_of_princ
ipal (I : FractionalIdeal S P) [IsPrincipal (I : Submodule R P)] : I = spanSingl
eton S (generator (I : Submodule R …
· 使用定理 `FractionalIdeal.spanSingleton_zero`：spanSingleton_zero : spanSingleton S
 (0 : P) = 0
· 使用定理 `FractionalIdeal.invertible_of_principal`：invertible_of_principal (I : Fr
actionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I != 0) :
 I * I⁻¹ = 1
· 使用定理 `FractionalIdeal.mem_spanSingleton_self`：mem_spanSingleton_self (x : P) :
 x in spanSingleton S x
· 使用定理 `FractionalIdeal.mem_zero_iff`：mem_zero_iff {x : P} : x in (0 : Fractiona
lIdeal S P) ↔ x = 0
-/
theorem invertible_iff_generator_nonzero (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] :
    I * I⁻¹ = 1 ↔ generator (I : Submodule R₁ K) ≠ 0 := by
  constructor
  · intro hI hg
    apply ne_zero_of_mul_eq_one _ _ hI
    rw [eq_spanSingleton_of_principal I, hg, spanSingleton_zero]
  · intro hg
    apply invertible_of_principal
    rw [eq_spanSingleton_of_principal I]
    intro hI
    have := mem_spanSingleton_self R₁⁰ (generator (I : Submodule R₁ K))
    rw [hI, mem_zero_iff] at this
    contradiction
/-
**FractionalIdeal.isPrincipal_inv** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：isPrincipal_inv (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Su
bmodule R₁ K)] (h : I != 0) : Submodule.IsPrincipal I⁻¹.1
参数：I : FractionalIdeal R₁⁰ K；I : Submodule R₁ K；h : I != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.val_eq_coe`：val_eq_coe (I : FractionalIdeal S P) : I.val
 = I
· 使用定理 `FractionalIdeal.isPrincipal_iff`：isPrincipal_iff (I : FractionalIdeal S 
P) : IsPrincipal (I : Submodule R P) ↔ exists x, I = spanSingleton S x
· 使用定理 `FractionalIdeal.mul_generator_self_inv`：mul_generator_self_inv {R₁ : Typ
e*} [CommRing R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K] (I : FractionalIdeal R₁⁰
 K) [Submodule.IsPrincipal (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.right_inverse_eq`：right_inverse_eq (I J : FractionalIdea
l R₁⁰ K) (h : I * J = 1) : J = I⁻¹
-/
theorem isPrincipal_inv (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)]
    (h : I ≠ 0) : Submodule.IsPrincipal I⁻¹.1 := by
  rw [val_eq_coe, isPrincipal_iff]
  use (generator (I : Submodule R₁ K))⁻¹
  have hI : I * spanSingleton _ (generator (I : Submodule R₁ K))⁻¹ = 1 :=
    mul_generator_self_inv _ I h
  exact (right_inverse_eq _ I (spanSingleton _ (generator (I : Submodule R₁ K))⁻¹) hI).symm

variable {K}
/-
**FractionalIdeal.den_mem_inv** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：den_mem_inv {I : FractionalIdeal R₁⁰ K} (hI : I != ⊥) : algebraMap R₁ K (I
.den : R₁) in I⁻¹
参数：hI : I != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.mem_inv_iff`：mem_inv_iff (hI : I != 0) {x : K} : x in I⁻
¹ ↔ forall y in I, x * y in (1 : FractionalIdeal R₁⁰ K)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `FractionalIdeal.mem_coe`：mem_coe {I : FractionalIdeal S P} {x : P} : x i
n (I : Submodule R P) ↔ x in I
· 使用定理 `FractionalIdeal.coe_one`：coe_one : (↑(1 : FractionalIdeal S P) : Submodu
le R P) = 1
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.one_eq_range`：one_eq_range : (1 : Submodule R A) = LinearMap.r
ange (Algebra.linearMap R A)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Submodule.smul_mem_pointwise_smul`：smul_mem_pointwise_smul (m : M) (a : 
α) (S : Submodule R M) : m in S -> a • m in a • S
· 使用定理 `FractionalIdeal.den_mul_self_eq_num`：den_mul_self_eq_num (I : Fractional
Ideal S P) : I.den • (I : Submodule R P) = Submodule.map (Algebra.linearMap R P)
 I.num
-/
lemma den_mem_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≠ ⊥) :
    algebraMap R₁ K (I.den : R₁) ∈ I⁻¹ := by
  rw [mem_inv_iff hI]
  intro i hi
  rw [← Algebra.smul_def (I.den : R₁) i, ← mem_coe, coe_one]
  suffices Submodule.map (Algebra.linearMap R₁ K) I.num ≤ 1 from
    this <| (den_mul_self_eq_num I).symm ▸ smul_mem_pointwise_smul i I.den I.coeToSubmodule hi
  apply le_trans <| map_mono (show I.num ≤ 1 by simp only [Ideal.one_eq_top, le_top])
  rw [Ideal.one_eq_top, Submodule.map_top, one_eq_range]
/-
**FractionalIdeal.num_le_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：num_le_mul_inv (I : FractionalIdeal R₁⁰ K) : I.num <= I * I⁻¹
参数：I : FractionalIdeal R₁⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.num_zero_eq`：num_zero_eq (h_inj : Function.Injective (al
gebraMap R P)) : num (0 : FractionalIdeal S P) = 0
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Submodule.zero_eq_bot`：zero_eq_bot : (0 : Submodule R M) = ⊥
· 使用定理 `FractionalIdeal.coeIdeal_bot`：coeIdeal_bot : ((⊥ : Ideal R) : Fractional
Ideal S P) = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.den_mul_self_eq_num'`：den_mul_self_eq_num' (I : Fraction
alIdeal S P) : spanSingleton S (algebraMap R P I.den) * I = I.num
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `FractionalIdeal.instMulLeftMono`：∀ {R : Type u_1} [inst : CommRing R] {S
 : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P],   M
ulLeftMono (Fractiona…
· 使用定理 `FractionalIdeal.instMulRightMono`：∀ {R : Type u_1} [inst : CommRing R] {
S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra R P],   
MulRightMono (Fraction…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.spanSingleton_le_iff_mem`：spanSingleton_le_iff_mem {x : 
P} {I : FractionalIdeal S P} : spanSingleton S x <= I ↔ x in I
· 使用引理 `FractionalIdeal.den_mem_inv`：den_mem_inv {I : FractionalIdeal R₁⁰ K} (hI
 : I != ⊥) : algebraMap R₁ K (I.den : R₁) in I⁻¹
-/
lemma num_le_mul_inv (I : FractionalIdeal R₁⁰ K) : I.num ≤ I * I⁻¹ := by
  by_cases hI : I = 0
  · rw [hI, num_zero_eq <| FaithfulSMul.algebraMap_injective R₁ K, zero_mul, zero_eq_bot,
      coeIdeal_bot]
  · rw [mul_comm, ← den_mul_self_eq_num']
    gcongr
    exact spanSingleton_le_iff_mem.2 (den_mem_inv hI)
/-
**FractionalIdeal.bot_lt_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：bot_lt_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I != ⊥) : ⊥ < I * I⁻¹
参数：hI : I != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.coeIdeal_ne_zero`：coeIdeal_ne_zero {I : Ideal R} : (I : 
FractionalIdeal R⁰ K) != 0 ↔ I != ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.num_eq_zero_iff`：num_eq_zero_iff [IsDomain R] {I : Fract
ionalIdeal R⁰ K} : I.num = 0 ↔ I = 0 where mp h
· 使用引理 `FractionalIdeal.num_le_mul_inv`：num_le_mul_inv (I : FractionalIdeal R₁⁰ 
K) : I.num <= I * I⁻¹
-/
lemma bot_lt_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≠ ⊥) : ⊥ < I * I⁻¹ :=
  lt_of_lt_of_le (coeIdeal_ne_zero.2 (hI ∘ num_eq_zero_iff.1)).bot_lt I.num_le_mul_inv
/-
**FractionalIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `FractionalIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : InvOneClass (FractionalIdeal R₁⁰ K) := { inv_one := div_one }

end FractionalIdeal

