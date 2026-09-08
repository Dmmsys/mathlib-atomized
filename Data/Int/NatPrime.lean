/-
Copyright (c) 2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Bryan Gin-ge Chen
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Int.Basic

/-!
# Lemmas about `Nat.Prime` using `Int`s
-/

public section


open Nat

namespace Int

/-
**Int.not_prime_of_int_mul** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：not_prime_of_int_mul {a b : Int} {c : Nat} (ha : a.natAbs != 1) (hb : b.na
tAbs != 1) (hc : a * b = (c : Int)) : ¬Nat.Prime c
参数：ha : a.natAbs != 1；hb : b.natAbs != 1；hc : a * b = (c : Int)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_of_mul_eq`：not_prime_of_mul_eq {a b n : Nat} (h : a * b = 
n) (h₁ : a != 1) (h₂ : b != 1) : ¬Prime n
· 使用定理 `Int.natAbs_mul_natAbs_eq`：∀ {a b : ℤ} {c : ℕ}, a * b = ↑c → a.natAbs * b
.natAbs = c
-/
theorem not_prime_of_int_mul {a b : ℤ} {c : ℕ} (ha : a.natAbs ≠ 1) (hb : b.natAbs ≠ 1)
    (hc : a * b = (c : ℤ)) : ¬Nat.Prime c :=
  not_prime_of_mul_eq (natAbs_mul_natAbs_eq hc) ha hb
/-
**Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : Nat} (p_prime : Nat.Prime p)
 {m n : Int} {k l : Nat} (hpm : ↑(p ^ k) ∣ m) (hpn : ↑(p ^ l) ∣ n) (hpmn : ↑(p ^
 (k + l + 1)) ∣ m * n) : ↑(p ^ (k + 1)) ∣ m ∨ ↑(p ^ (l + 1)) ∣ n
参数：p_prime : Nat.Prime p；hpm : ↑(p ^ k) ∣ m；hpn : ↑(p ^ l) ∣ n；hpmn : ↑(p ^ (k +
 l + 1)) ∣ m * n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.dvd_natAbs`：∀ {a b : ℤ}, a ∣ ↑b.natAbs ↔ a ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul`：succ_dvd_or_succ_dvd_of_su
cc_sum_dvd_mul {p : Nat} (p_prime : Prime p) {m n k l : Nat} (hpm : p ^ k ∣ m) (
hpn : p ^ l ∣ n) (hpmn : p ^ (k + …
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : Nat.Prime p) {m n : ℤ}
    {k l : ℕ} (hpm : ↑(p ^ k) ∣ m) (hpn : ↑(p ^ l) ∣ n) (hpmn : ↑(p ^ (k + l + 1)) ∣ m * n) :
    ↑(p ^ (k + 1)) ∣ m ∨ ↑(p ^ (l + 1)) ∣ n :=
  have hpm' : p ^ k ∣ m.natAbs := Int.natCast_dvd_natCast.1 <| Int.dvd_natAbs.2 hpm
  have hpn' : p ^ l ∣ n.natAbs := Int.natCast_dvd_natCast.1 <| Int.dvd_natAbs.2 hpn
  have hpmn' : p ^ (k + l + 1) ∣ m.natAbs * n.natAbs := by
    rw [← Int.natAbs_mul]; apply Int.natCast_dvd_natCast.1 <| Int.dvd_natAbs.2 hpmn
  let hsd := Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul p_prime hpm' hpn' hpmn'
  hsd.elim (fun hsd1 => Or.inl (by apply Int.dvd_natAbs.1; apply Int.natCast_dvd_natCast.2 hsd1))
    fun hsd2 => Or.inr (by apply Int.dvd_natAbs.1; apply Int.natCast_dvd_natCast.2 hsd2)
/-
**Int.Prime.dvd_natAbs_of_coe_dvd_sq** 是 Mathlib 中的一个定理，位于命名空间 `Int.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → ∀ (k : ℤ), ↑p ∣ k ^ 2 → p ∣ k.natAbs
参数：k : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.dvd_of_dvd_pow`：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ^ n → p ∣ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用引理 `Int.natCast_dvd`：natCast_dvd {m : Nat} : (m : Int) ∣ n ↔ m ∣ n.natAbs
-/
theorem Prime.dvd_natAbs_of_coe_dvd_sq {p : ℕ} (hp : p.Prime) (k : ℤ) (h : (p : ℤ) ∣ k ^ 2) :
    p ∣ k.natAbs := by
  apply @Nat.Prime.dvd_of_dvd_pow _ _ 2 hp
  rwa [sq, ← natAbs_mul, ← natCast_dvd, ← sq]

end Int

