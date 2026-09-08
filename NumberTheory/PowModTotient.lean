/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Modular exponentiation with the totient function

This file contains lemmas about modular exponentiation.
In particular, it contains lemmas showing that an exponent can be reduced modulo the totient
function when the base is coprime to the modulus.

## Main Results

* `pow_totient_mod`: If `x` is coprime to `n`, then the modular exponentiation
  `x ^ k % n` can be reduced to `x ^ (k % φ n) % n`.

## TODOs

- Extend to results in cases where the base is not coprime to the modulus.
- Write a tactic or simproc that can automatically reduce exponents
  or towers of exponents using these results.

-/

public section

namespace Nat

/-
**Nat.pow_totient_mod_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_totient_mod_eq_one {x n : Nat} (hn : 1 < n) (h : x.Coprime n) : (x ^ φ
 n) % n = 1
参数：hn : 1 < n；h : x.Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.mod_eq_of_modEq`：mod_eq_of_modEq {a b n} (h : a ≡ b [MOD n]) (hb : b
 < n) : a % n = b
· 使用定理 `Nat.ModEq.pow_totient`：Nat.ModEq.pow_totient {x n : Nat} (h : Nat.Coprim
e x n) : x ^ φ n ≡ 1 [MOD n]
-/
lemma pow_totient_mod_eq_one {x n : ℕ} (hn : 1 < n) (h : x.Coprime n) :
    (x ^ φ n) % n = 1 := by
  exact mod_eq_of_modEq (ModEq.pow_totient h) hn
/-
**Nat.pow_add_totient_mod_eq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_add_totient_mod_eq {x k n : Nat} (hn : 1 < n) (h : x.Coprime n) : (x ^
 (k + φ n)) % n = (x ^ k) % n
参数：hn : 1 < n；h : x.Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.mul_mod`：∀ (a b n : ℕ), a * b % n = a % n * (b % n) % n
· 使用引理 `Nat.pow_totient_mod_eq_one`：pow_totient_mod_eq_one {x n : Nat} (hn : 1 <
 n) (h : x.Coprime n) : (x ^ φ n) % n = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pow_add_totient_mod_eq {x k n : ℕ} (hn : 1 < n) (h : x.Coprime n) :
    (x ^ (k + φ n)) % n = (x ^ k) % n := by
  rw [pow_add, mul_mod, pow_totient_mod_eq_one hn h]
  simp only [mul_one, dvd_refl, mod_mod_of_dvd]
/-
**Nat.pow_add_mul_totient_mod_eq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_add_mul_totient_mod_eq {x k l n : Nat} (hn : 1 < n) (h : x.Coprime n) 
: (x ^ (k + l * φ n)) % n = (x ^ k) % n
参数：hn : 1 < n；h : x.Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用引理 `Nat.pow_add_totient_mod_eq`：pow_add_totient_mod_eq {x k n : Nat} (hn : 1
 < n) (h : x.Coprime n) : (x ^ (k + φ n)) % n = (x ^ k) % n
-/
lemma pow_add_mul_totient_mod_eq {x k l n : ℕ} (hn : 1 < n) (h : x.Coprime n) :
    (x ^ (k + l * φ n)) % n = (x ^ k) % n := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [add_mul, one_mul, ← add_assoc, pow_add_totient_mod_eq hn h, ih]
/-
**Nat.pow_totient_mod** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_totient_mod {x k n : Nat} (hn : 1 < n) (h : x.Coprime n) : x ^ k % n =
 x ^ (k % φ n) % n
参数：hn : 1 < n；h : x.Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_add_mod'`：∀ (a b : ℕ), a / b * b + a % b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Nat.pow_add_mul_totient_mod_eq`：pow_add_mul_totient_mod_eq {x k l n : Na
t} (hn : 1 < n) (h : x.Coprime n) : (x ^ (k + l * φ n)) % n = (x ^ k) % n
· 使用定理 `Nat.add_mul_mod_self_right`：∀ (x y z : ℕ), (x + y * z) % z = x % z
· 使用定理 `Nat.mod_mod`：∀ (a n : ℕ), a % n % n = a % n
-/
lemma pow_totient_mod {x k n : ℕ} (hn : 1 < n) (h : x.Coprime n) :
    x ^ k % n = x ^ (k % φ n) % n := by
  rw [← div_add_mod' k (φ n), add_comm, pow_add_mul_totient_mod_eq hn h, add_mul_mod_self_right,
    mod_mod k (φ n)]

end Nat

