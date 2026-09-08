/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Integral elements of ℂ

This file proves that `Complex.I` is integral over ℤ and ℚ.
-/

public section

open Polynomial

namespace Complex

/-
**Complex.isIntegral_int_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isIntegral_int_I : IsIntegral Int I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_X_pow_add_C`：monic_X_pow_add_C {n : Nat} (h : n != 0) :
 (X ^ n + C a).Monic
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_add`：eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.ev
al₂ f x
· 使用定理 `Polynomial.eval₂_X_pow`：eval₂_X_pow {n : Nat} : (X ^ n).eval₂ f x = x ^ 
n
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `Complex.I_sq`：I_sq : I ^ 2 = -1
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
-/
theorem isIntegral_int_I : IsIntegral ℤ I := by
  refine ⟨X ^ 2 + C 1, monic_X_pow_add_C _ two_ne_zero, ?_⟩
  rw [eval₂_add, eval₂_X_pow, eval₂_C, I_sq, eq_intCast, Int.cast_one, neg_add_cancel]
/-
**Complex.isIntegral_rat_I** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isIntegral_rat_I : IsIntegral Rat I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `Complex.isIntegral_int_I`：isIntegral_int_I : IsIntegral Int I
-/
theorem isIntegral_rat_I : IsIntegral ℚ I :=
  isIntegral_int_I.tower_top

end Complex

