/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Lemmas about `Multiplicative ℕ`
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

open Multiplicative

namespace Nat

/-
**Nat.toAdd_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：toAdd_pow (a : Multiplicative Nat) (b : Nat) : (a ^ b).toAdd = a.toAdd * b
参数：a : Multiplicative Nat；b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma toAdd_pow (a : Multiplicative ℕ) (b : ℕ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _
/-
**Nat.ofAdd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a b : ℕ), Multiplicative.ofAdd (a * b) = Multiplicative.ofAdd a ^ b
参数：a b : ℕ；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.toAdd_pow`：toAdd_pow (a : Multiplicative Nat) (b : Nat) : (a ^ b).to
Add = a.toAdd * b
-/
@[simp] lemma ofAdd_mul (a b : ℕ) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_pow _ _).symm

end Nat

