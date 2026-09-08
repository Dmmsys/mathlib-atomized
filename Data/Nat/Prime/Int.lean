/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Data.Int.Basic

/-!
# Prime numbers in the naturals and the integers

TODO: This file can probably be merged with `Mathlib/Data/Int/NatPrime.lean`.
-/

public section


namespace Nat

/-
**Nat.prime_iff_prime_int** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root_.Prime (p : Int)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero_iff_pos`：∀ {n : ℕ}, ↑n ≠ 0 ↔ 0 < n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Int.isUnit_iff_natAbs_eq`：isUnit_iff_natAbs_eq : IsUnit u ↔ u.natAbs = 1
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.dvd_natAbs`：∀ {a b : ℤ}, a ∣ ↑b.natAbs ↔ a ∣ b
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Nat.Prime.dvd_mul`：∀ {p m n : ℕ}, Nat.Prime p → (p ∣ m * n ↔ p ∣ m ∨ p ∣
 n)
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.isUnit_iff`：∀ {n : ℕ}, IsUnit n ↔ n = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Int.natCast_mul`：∀ (n m : ℕ), ↑(n * m) = ↑n * ↑m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem prime_iff_prime_int {p : ℕ} : p.Prime ↔ _root_.Prime (p : ℤ) :=
  ⟨fun hp =>
    ⟨Int.natCast_ne_zero_iff_pos.2 hp.pos, mt Int.isUnit_iff_natAbs_eq.1 hp.ne_one, fun a b h => by
      rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast, Int.natAbs_mul, hp.dvd_mul] at h
      rwa [← Int.dvd_natAbs, Int.natCast_dvd_natCast, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]⟩,
    fun hp =>
    Nat.prime_iff.2
      ⟨Int.natCast_ne_zero.1 hp.1,
        (mt Nat.isUnit_iff.1) fun h => by simp [h] at hp, fun a b => by
        simpa only [Int.natCast_dvd_natCast, (Int.natCast_mul _ _).symm] using hp.2.2 a b⟩⟩

/-- Two prime powers with positive exponents are equal only when the primes and the
exponents are equal. -/
/-
**Nat.Prime.pow_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p q m n : ℕ}, Nat.Prime p → Nat.Prime q → p ^ (m + 1) = q ^ (n + 1) → p
 = q ∧ m = n
参数：m + 1；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.Prime.dvd_of_dvd_pow`：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ^ n → p ∣ m
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_inj`：∀ {a b : ℕ}, a.succ = b.succ ↔ a = b
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p

--- 原说明 ---
Two prime powers with positive exponents are equal only when the primes and the
exponents are equal.
-/
lemma Prime.pow_inj {p q m n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ^ (m + 1) = q ^ (n + 1)) : p = q ∧ m = n := by
  have H := dvd_antisymm (Prime.dvd_of_dvd_pow hp <| h ▸ dvd_pow_self p (succ_ne_zero m))
    (Prime.dvd_of_dvd_pow hq <| h.symm ▸ dvd_pow_self q (succ_ne_zero n))
  exact ⟨H, succ_inj.mp <| Nat.pow_right_injective hq.two_le (H ▸ h)⟩

/-- Version of `Nat.Prime.pow_inj` with an explicit nonzero assumption on the exponents. -/
/-
**Nat.Prime.pow_inj'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p q m n : ℕ}, Nat.Prime p → Nat.Prime q → m ≠ 0 → n ≠ 0 → p ^ m = q ^ n
 → p = q ∧ m = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_one_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.pow_inj`：∀ {p q m n : ℕ}, Nat.Prime p → Nat.Prime q → p ^ (m +
 1) = q ^ (n + 1) → p = q ∧ m = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Version of `Nat.Prime.pow_inj` with an explicit nonzero assumption on the expone
nts.
-/
lemma Prime.pow_inj'
    {p q m n : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hm : m ≠ 0) (hn : n ≠ 0)
    (h : p ^ m = q ^ n) : p = q ∧ m = n := by
  obtain ⟨m, rfl⟩ := exists_eq_add_one_of_ne_zero hm
  obtain ⟨n, rfl⟩ := exists_eq_add_one_of_ne_zero hn
  simpa using hp.pow_inj hq h

end Nat

namespace Int

@[simp]
/-
**Int.prime_ofNat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：prime_ofNat_iff {n : Nat} : Prime (ofNat(n) : Int) ↔ Nat.Prime (OfNat.ofNa
t n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
-/
theorem prime_ofNat_iff {n : ℕ} :
    Prime (ofNat(n) : ℤ) ↔ Nat.Prime (OfNat.ofNat n) :=
  Nat.prime_iff_prime_int.symm
/-
**Int.prime_two** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：prime_two : Prime (2 : Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.prime_ofNat_iff`：prime_ofNat_iff {n : Nat} : Prime (ofNat(n) : Int) 
↔ Nat.Prime (OfNat.ofNat n)
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
-/
theorem prime_two : Prime (2 : ℤ) :=
  prime_ofNat_iff.mpr Nat.prime_two
/-
**Int.prime_three** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：prime_three : Prime (3 : Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.prime_ofNat_iff`：prime_ofNat_iff {n : Nat} : Prime (ofNat(n) : Int) 
↔ Nat.Prime (OfNat.ofNat n)
· 使用定理 `Nat.prime_three`：prime_three : Prime 3
-/
theorem prime_three : Prime (3 : ℤ) :=
  prime_ofNat_iff.mpr Nat.prime_three

end Int

