/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Lemmas about `Multiplicative ℤ`.
-/

public section


open Nat

namespace Int

section Multiplicative

open Multiplicative

/-
**Int.toAdd_pow** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：toAdd_pow (a : Multiplicative Int) (b : Nat) : (a ^ b).toAdd = a.toAdd * b
参数：a : Multiplicative Int；b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma toAdd_pow (a : Multiplicative ℤ) (b : ℕ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _
/-
**Int.toAdd_zpow** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：toAdd_zpow (a : Multiplicative Int) (b : Int) : (a ^ b).toAdd = a.toAdd * 
b
参数：a : Multiplicative Int；b : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma toAdd_zpow (a : Multiplicative ℤ) (b : ℤ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _
/-
**Int.ofAdd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (a b : ℤ), Multiplicative.ofAdd (a * b) = Multiplicative.ofAdd a ^ b
参数：a b : ℤ；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.toAdd_zpow`：toAdd_zpow (a : Multiplicative Int) (b : Int) : (a ^ b).
toAdd = a.toAdd * b
-/
@[simp] lemma ofAdd_mul (a b : ℤ) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_zpow ..).symm

end Multiplicative

end Int

