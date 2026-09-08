/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Prime

/-!
# Localizations of modules at the complement of a prime ideal
-/

public section

/-- Given a prime ideal `P` and `f : M →ₗ[R] M'`, `IsLocalizedModule.AtPrime P f` states that `M'`
  is isomorphic to the localization of `M` at the complement of `P`. -/
/-
**IsLocalizedModule.AtPrime** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     {M' : Type u_3} →       [inst : Co
mmSemiring R] →         (P : Ideal R) →           [P.IsPrime] →             [ins
t_2 : AddCommMonoid M] →               [inst_3 : AddCommMonoid M'] →            
     [inst_4 : _root_.Module R M] → [inst_5 : _root_.Module R M'] → (M →ₗ[R] M')
 → Prop
参数：P : Ideal R；M →ₗ[R] M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a prime ideal `P` and `f : M →ₗ[R] M'`, `IsLocalizedModule.AtPrime P f` st
ates that `M'`
  is isomorphic to the localization of `M` at the complement of `P`.
-/
protected abbrev IsLocalizedModule.AtPrime {R M M' : Type*} [CommSemiring R] (P : Ideal R)
    [P.IsPrime] [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] (f : M →ₗ[R] M') :=
  IsLocalizedModule P.primeCompl f

/-- Given a prime ideal `P`, `LocalizedModule.AtPrime P M` is a localization of `M`
  at the complement of `P`. -/
/-
**LocalizedModule.AtPrime** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     (P : Ideal R) → [P.IsPrim
e] → (M : Type u_2) → [inst_2 : AddCommMonoid M] → [_root_.Module R M] → Type (m
ax u_1 u_2)
参数：P : Ideal R；M : Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a prime ideal `P`, `LocalizedModule.AtPrime P M` is a localization of `M`
  at the complement of `P`.
-/
protected abbrev LocalizedModule.AtPrime {R : Type*} [CommSemiring R] (P : Ideal R) [P.IsPrime]
    (M : Type*) [AddCommMonoid M] [Module R M] :=
  LocalizedModule P.primeCompl M
