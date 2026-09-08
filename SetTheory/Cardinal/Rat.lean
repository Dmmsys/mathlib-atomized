/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Floris Van Doorn
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Rat.Encodable
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinality of ℚ

This file proves that the Cardinality of ℚ is ℵ₀
-/

public section

assert_not_exists Module Field

open Cardinal

/-
**Cardinal.mkRat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Cardinal.mkRat : #Rat = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `CharZero.infinite`：∀ (M : Type u_1) [inst : AddMonoidWithOne M] [CharZer
o M], Infinite M
-/
theorem Cardinal.mkRat : #ℚ = ℵ₀ := mk_eq_aleph0 ℚ
