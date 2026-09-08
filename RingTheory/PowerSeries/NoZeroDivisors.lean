/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Power series over rings with no zero divisors

This file proves, using the properties of orders of power series,
that `R⟦X⟧` is an integral domain when `R` is.

We then state various results about `R⟦X⟧` with `R` an integral domain.

## Instance

If `R` has `NoZeroDivisors`, then so does `R⟦X⟧`.

-/

public section


variable {R : Type*}

namespace PowerSeries

section NoZeroDivisors

variable [Semiring R]

/-
**PowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoZeroDivisors R] : NoZeroDivisors R⟦X⟧ where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} h := by
    simp_rw [← order_eq_top, order_mul] at h ⊢
    exact WithTop.add_eq_top.mp h

end NoZeroDivisors

section IsDomain

/-
**PowerSeries.** 是 Mathlib 中的一个实例，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] [IsDomain R] : IsDomain R⟦X⟧ :=
  NoZeroDivisors.to_isDomain _

variable [CommRing R] [IsDomain R]

/-- The ideal spanned by the variable in the power series ring
over an integral domain is a prime ideal. -/
/-
**PowerSeries.span_X_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：span_X_isPrime : (Ideal.span ({X} : Set R⟦X⟧)).IsPrime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `PowerSeries.X_dvd_iff`：X_dvd_iff {φ : R⟦X⟧} : (X : R⟦X⟧) ∣ φ ↔ constantC
oeff φ = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `RingHom.ker_isPrime`：ker_isPrime {F : Type*} [Semiring R] [Semiring S] [
IsDomain S] [FunLike F R S] [RingHomClass F R S] (f : F) : (ker f).IsPrime

--- 原说明 ---
The ideal spanned by the variable in the power series ring
over an integral domain is a prime ideal.
-/
theorem span_X_isPrime : (Ideal.span ({X} : Set R⟦X⟧)).IsPrime := by
  suffices Ideal.span ({X} : Set R⟦X⟧) = RingHom.ker constantCoeff by
    rw [this]
    exact RingHom.ker_isPrime _
  apply Ideal.ext
  intro φ
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

/-- The variable of the power series ring over an integral domain is prime. -/
/-
**PowerSeries.X_prime** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_prime : Prime (X : R⟦X⟧)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PowerSeries.coeff_one_X`：coeff_one_X : coeff 1 (X : R⟦X⟧) = 1
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PowerSeries.span_X_isPrime`：span_X_isPrime : (Ideal.span ({X} : Set R⟦X⟧
)).IsPrime

--- 原说明 ---
The variable of the power series ring over an integral domain is prime.
-/
theorem X_prime : Prime (X : R⟦X⟧) := by
  rw [← Ideal.span_singleton_prime]
  · exact span_X_isPrime
  · intro h
    simpa [map_zero (coeff 1)] using congr_arg (coeff 1) h

/-- The variable of the power series ring over an integral domain is irreducible. -/
/-
**PowerSeries.X_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_irreducible : Irreducible (X : R⟦X⟧)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `PowerSeries.instIsDomain`：∀ {R : Type u_1} [inst : Ring R] [IsDomain R],
 IsDomain (PowerSeries R)
· 使用定理 `PowerSeries.X_prime`：X_prime : Prime (X : R⟦X⟧)

--- 原说明 ---
The variable of the power series ring over an integral domain is irreducible.
-/
theorem X_irreducible : Irreducible (X : R⟦X⟧) := X_prime.irreducible
/-
**PowerSeries.rescale_injective** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_injective {a : R} (ha : a != 0) : Function.Injective (rescale a)
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.ext_iff`：∀ {R : Type u_1} [inst : Semiring R] {φ ψ : PowerSe
ries R},   φ = ψ ↔ ∀ (n : ℕ), (PowerSeries.coeff n) φ = (PowerSeries.coeff n) ψ
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `PowerSeries.coeff_rescale`：coeff_rescale (f : R⟦X⟧) (a : R) (n : Nat) : 
coeff n (rescale a f) = a ^ n * coeff n f
-/
theorem rescale_injective {a : R} (ha : a ≠ 0) : Function.Injective (rescale a) := by
  intro p q h
  rw [PowerSeries.ext_iff] at *
  intro n
  specialize h n
  rwa [coeff_rescale, coeff_rescale, mul_right_inj' <| pow_ne_zero _ ha] at h

end IsDomain

end PowerSeries

