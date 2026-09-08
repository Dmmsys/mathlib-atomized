/-
Copyright (c) 2026 María Inés de Frutos-Fernández, Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Xavier Généreux
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuations on an algebra over a finite field.
-/

public section

namespace FiniteField

open Valuation

variable {Fq A Γ : Type*} [Field Fq] [Finite Fq] [Ring A] [Algebra Fq A]
  [LinearOrderedCommMonoidWithZero Γ] (v : Valuation A Γ)

@[grind =>]
/-
**FiniteField.valuation_algebraMap_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `FiniteField
`。
形式化陈述：valuation_algebraMap_eq_one (a : Fq) (ha : a != 0) : v (algebraMap Fq A a)
 = 1
参数：a : Fq；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `FiniteField.pow_card_sub_one_eq_one`：pow_card_sub_one_eq_one (a : K) (ha
 : a != 0) : a ^ (q - 1) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma valuation_algebraMap_eq_one (a : Fq) (ha : a ≠ 0) : v (algebraMap Fq A a) = 1 := by
  have : Fintype Fq := Fintype.ofFinite Fq
  have hpow : (v (algebraMap Fq A a)) ^ (Fintype.card Fq - 1) = 1 := by
    simp [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha]
  grind [pow_eq_one_iff, → IsPrimePow.two_le, FiniteField.isPrimePow_card]
/-
**FiniteField.valuation_algebraMap_le_one** 是 Mathlib 中的一个引理，位于命名空间 `FiniteField
`。
形式化陈述：valuation_algebraMap_le_one (v : Valuation A Γ) (a : Fq) : v (algebraMap F
q A a) <= 1
参数：v : Valuation A Γ；a : Fq。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma valuation_algebraMap_le_one (v : Valuation A Γ) (a : Fq) :
    v (algebraMap Fq A a) ≤ 1 := by by_cases a = 0 <;> grind [zero_le]
/-
**FiniteField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrivialOn Fq v where
  eq_one a ha := FiniteField.valuation_algebraMap_eq_one v a ha

end FiniteField

