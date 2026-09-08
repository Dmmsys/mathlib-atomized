/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.PNat.Basic

/-!
# Primality and GCD on pnat

This file extends the theory of `ℕ+` with `gcd`, `lcm` and `Prime` functions, analogous to those on
`Nat`.
-/

@[expose] public section


namespace Nat.Primes

/-- The canonical map from `Nat.Primes` to `ℕ+` -/
/-
**Nat.Primes.toPNat** 是 Mathlib 中的一个定义，位于命名空间 `Nat.Primes`。
形式化陈述：Nat.Primes → ℕ+
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `Nat.Primes` to `ℕ+`
-/
@[coe] def toPNat : Nat.Primes → ℕ+ :=
  fun p => ⟨(p : ℕ), p.property.pos⟩
/-
**Nat.Primes.coePNat** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Primes`。
形式化陈述：coePNat : Coe Nat.Primes Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coePNat : Coe Nat.Primes ℕ+ :=
  ⟨toPNat⟩

@[norm_cast]
/-
**Nat.Primes.coe_pnat_nat** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primes`。
形式化陈述：coe_pnat_nat (p : Nat.Primes) : ((p : Nat+) : Nat) = p
参数：p : Nat.Primes。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pnat_nat (p : Nat.Primes) : ((p : ℕ+) : ℕ) = p :=
  rfl
/-
**Nat.Primes.coe_pnat_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primes`。
形式化陈述：coe_pnat_injective : Function.Injective ((↑) : Nat.Primes -> Nat+)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem coe_pnat_injective : Function.Injective ((↑) : Nat.Primes → ℕ+) := fun p q h =>
  Subtype.ext (by injection h)

@[norm_cast]
/-
**Nat.Primes.coe_pnat_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primes`。
形式化陈述：coe_pnat_inj (p q : Nat.Primes) : (p : Nat+) = (q : Nat+) ↔ p = q
参数：p q : Nat.Primes。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Nat.Primes.coe_pnat_injective`：coe_pnat_injective : Function.Injective (
(↑) : Nat.Primes -> Nat+)
-/
theorem coe_pnat_inj (p q : Nat.Primes) : (p : ℕ+) = (q : ℕ+) ↔ p = q :=
  coe_pnat_injective.eq_iff

end Nat.Primes

namespace PNat

open Nat

/-- The greatest common divisor (gcd) of two positive natural numbers,
  viewed as positive natural number. -/
/-
**PNat.gcd** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：gcd (n m : Nat+) : Nat+
参数：n m : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The greatest common divisor (gcd) of two positive natural numbers,
  viewed as positive natural number.
-/
def gcd (n m : ℕ+) : ℕ+ :=
  ⟨Nat.gcd (n : ℕ) (m : ℕ), Nat.gcd_pos_of_pos_left (m : ℕ) n.pos⟩

/-- The least common multiple (lcm) of two positive natural numbers,
  viewed as positive natural number. -/
/-
**PNat.lcm** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：lcm (n m : Nat+) : Nat+
参数：n m : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The least common multiple (lcm) of two positive natural numbers,
  viewed as positive natural number.
-/
def lcm (n m : ℕ+) : ℕ+ :=
  ⟨Nat.lcm (n : ℕ) (m : ℕ), by
    let h := mul_pos n.pos m.pos
    rw [← gcd_mul_lcm (n : ℕ) (m : ℕ), mul_comm] at h
    exact pos_of_dvd_of_pos (Dvd.intro (Nat.gcd (n : ℕ) (m : ℕ)) rfl) h⟩

@[simp, norm_cast]
/-
**PNat.gcd_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_coe (n m : Nat+) : (gcd n m : Nat) = Nat.gcd n m
参数：n m : Nat+。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gcd_coe (n m : ℕ+) : (gcd n m : ℕ) = Nat.gcd n m :=
  rfl

@[simp, norm_cast]
/-
**PNat.lcm_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：lcm_coe (n m : Nat+) : (lcm n m : Nat) = Nat.lcm n m
参数：n m : Nat+。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcm_coe (n m : ℕ+) : (lcm n m : ℕ) = Nat.lcm n m :=
  rfl
/-
**PNat.gcd_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_dvd_left (n m : Nat+) : gcd n m ∣ n
参数：n m : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
-/
theorem gcd_dvd_left (n m : ℕ+) : gcd n m ∣ n :=
  dvd_iff.2 (Nat.gcd_dvd_left (n : ℕ) (m : ℕ))
/-
**PNat.gcd_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_dvd_right (n m : Nat+) : gcd n m ∣ m
参数：n m : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
-/
theorem gcd_dvd_right (n m : ℕ+) : gcd n m ∣ m :=
  dvd_iff.2 (Nat.gcd_dvd_right (n : ℕ) (m : ℕ))
/-
**PNat.dvd_gcd** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：dvd_gcd {m n k : Nat+} (hm : k ∣ m) (hn : k ∣ n) : k ∣ gcd m n
参数：hm : k ∣ m；hn : k ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Nat.dvd_gcd`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m.gcd n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem dvd_gcd {m n k : ℕ+} (hm : k ∣ m) (hn : k ∣ n) : k ∣ gcd m n :=
  dvd_iff.2 (Nat.dvd_gcd (dvd_iff.1 hm) (dvd_iff.1 hn))
/-
**PNat.dvd_lcm_left** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：dvd_lcm_left (n m : Nat+) : n ∣ lcm n m
参数：n m : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Nat.dvd_lcm_left`：∀ (m n : ℕ), m ∣ m.lcm n
-/
theorem dvd_lcm_left (n m : ℕ+) : n ∣ lcm n m :=
  dvd_iff.2 (Nat.dvd_lcm_left (n : ℕ) (m : ℕ))
/-
**PNat.dvd_lcm_right** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：dvd_lcm_right (n m : Nat+) : m ∣ lcm n m
参数：n m : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Nat.dvd_lcm_right`：∀ (m n : ℕ), n ∣ m.lcm n
-/
theorem dvd_lcm_right (n m : ℕ+) : m ∣ lcm n m :=
  dvd_iff.2 (Nat.dvd_lcm_right (n : ℕ) (m : ℕ))
/-
**PNat.lcm_dvd** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：lcm_dvd {m n k : Nat+} (hm : m ∣ k) (hn : n ∣ k) : lcm m n ∣ k
参数：hm : m ∣ k；hn : n ∣ k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Nat.lcm_dvd`：∀ {m n k : ℕ}, m ∣ k → n ∣ k → m.lcm n ∣ k
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem lcm_dvd {m n k : ℕ+} (hm : m ∣ k) (hn : n ∣ k) : lcm m n ∣ k :=
  dvd_iff.2 (@Nat.lcm_dvd (m : ℕ) (n : ℕ) (k : ℕ) (dvd_iff.1 hm) (dvd_iff.1 hn))
/-
**PNat.gcd_mul_lcm** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_mul_lcm (n m : Nat+) : gcd n m * lcm n m = n * m
参数：n m : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Nat.gcd_mul_lcm`：∀ (m n : ℕ), m.gcd n * m.lcm n = m * n
-/
theorem gcd_mul_lcm (n m : ℕ+) : gcd n m * lcm n m = n * m :=
  Subtype.ext (Nat.gcd_mul_lcm (n : ℕ) (m : ℕ))

-- TODO: this is an iff, and should be moved to an earlier file.
/-
**PNat.eq_one_of_lt_two** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：eq_one_of_lt_two {n : Nat+} : n < 2 -> n = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.lt_add_one_iff`：lt_add_one_iff : forall {a b : Nat+}, a < b + 1 ↔ a
 <= b
· 使用定理 `le_one_iff_eq_one`：le_one_iff_eq_one : a <= 1 ↔ a = 1
· 使用定理 `PNat.instIsBotOneClass`：IsBotOneClass ℕ+
-/
theorem eq_one_of_lt_two {n : ℕ+} : n < 2 → n = 1 := by
  change n < 1 + 1 → _
  rw [lt_add_one_iff, le_one_iff_eq_one]
  exact id

section Prime

/-! ### Prime numbers -/


/-- Primality predicate for `ℕ+`, defined in terms of `Nat.Prime`. -/
/-
**PNat.Prime** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：Prime (p : Nat+) : Prop
参数：p : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Primality predicate for `ℕ+`, defined in terms of `Nat.Prime`.
-/
def Prime (p : ℕ+) : Prop :=
  (p : ℕ).Prime
/-
**PNat.Prime.one_lt** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Prime`。
形式化陈述：∀ {p : ℕ+}, p.Prime → 1 < p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
-/
theorem Prime.one_lt {p : ℕ+} : p.Prime → 1 < p :=
  Nat.Prime.one_lt
/-
**PNat.prime_two** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：prime_two : (2 : Nat+).Prime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
-/
theorem prime_two : (2 : ℕ+).Prime :=
  Nat.prime_two
/-
**PNat.** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : ℕ+} [h : Fact p.Prime] : Fact (p : ℕ).Prime := h
/-
**PNat.fact_prime_two** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
形式化陈述：fact_prime_two : Fact (2 : Nat+).Prime
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PNat.prime_two`：prime_two : (2 : Nat+).Prime
-/
instance fact_prime_two : Fact (2 : ℕ+).Prime :=
  ⟨prime_two⟩
/-
**PNat.prime_three** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：prime_three : (3 : Nat+).Prime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_three`：prime_three : Prime 3
-/
theorem prime_three : (3 : ℕ+).Prime :=
  Nat.prime_three
/-
**PNat.fact_prime_three** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
形式化陈述：fact_prime_three : Fact (3 : Nat+).Prime
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PNat.prime_three`：prime_three : (3 : Nat+).Prime
-/
instance fact_prime_three : Fact (3 : ℕ+).Prime :=
  ⟨prime_three⟩
/-
**PNat.prime_five** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：prime_five : (5 : Nat+).Prime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_five`：prime_five : Prime 5
-/
theorem prime_five : (5 : ℕ+).Prime :=
  Nat.prime_five
/-
**PNat.fact_prime_five** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
形式化陈述：fact_prime_five : Fact (5 : Nat+).Prime
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PNat.prime_five`：prime_five : (5 : Nat+).Prime
-/
instance fact_prime_five : Fact (5 : ℕ+).Prime :=
  ⟨prime_five⟩
/-
**PNat.dvd_prime** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：dvd_prime {p m : Nat+} (pp : p.Prime) : m ∣ p ↔ m = 1 ∨ m = p
参数：pp : p.Prime。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dvd_prime {p m : ℕ+} (pp : p.Prime) : m ∣ p ↔ m = 1 ∨ m = p := by
  rw [PNat.dvd_iff]
  rw [Nat.dvd_prime pp]
  simp
/-
**PNat.Prime.ne_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Prime`。
形式化陈述：∀ {p : ℕ+}, p.Prime → p ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.coe_eq_one_iff`：coe_eq_one_iff {m : Nat+} : (m : Nat) = 1 ↔ m = 1
-/
theorem Prime.ne_one {p : ℕ+} : p.Prime → p ≠ 1 := by
  intro pp contra
  apply Nat.Prime.ne_one pp
  rw [PNat.coe_eq_one_iff]
  apply contra

@[simp]
/-
**PNat.not_prime_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：not_prime_one : ¬(1 : Nat+).Prime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_one`：¬Nat.Prime 1
-/
theorem not_prime_one : ¬(1 : ℕ+).Prime :=
  Nat.not_prime_one
/-
**PNat.Prime.not_dvd_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Prime`。
形式化陈述：∀ {p : ℕ+}, p.Prime → ¬p ∣ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
-/
theorem Prime.not_dvd_one {p : ℕ+} : p.Prime → ¬p ∣ 1 := fun pp : p.Prime => by
  rw [dvd_iff]
  apply Nat.Prime.not_dvd_one pp

set_option backward.isDefEq.respectTransparency false in
/-
**PNat.exists_prime_and_dvd** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：exists_prime_and_dvd {n : Nat+} (hn : n != 1) : exists p : Nat+, p.Prime ∧
 p ∣ n
参数：hn : n != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.exists_prime_and_dvd`：exists_prime_and_dvd {n : Nat} (hn : n != 1) :
 exists p, Prime p ∧ p ∣ n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PNat.coe_eq_one_iff`：coe_eq_one_iff {m : Nat+} : (m : Nat) = 1 ↔ m = 1
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
-/
theorem exists_prime_and_dvd {n : ℕ+} (hn : n ≠ 1) : ∃ p : ℕ+, p.Prime ∧ p ∣ n := by
  obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (mt coe_eq_one_iff.mp hn)
  exists (⟨p, Nat.Prime.pos hp.left⟩ : ℕ+); rw [dvd_iff]; apply hp

end Prime

section Coprime

/-! ### Coprime numbers and gcd -/


/-- Two pnats are coprime if their gcd is 1. -/
/-
**PNat.Coprime** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：Coprime (m n : Nat+) : Prop
参数：m n : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two pnats are coprime if their gcd is 1.
-/
def Coprime (m n : ℕ+) : Prop :=
  m.gcd n = 1

@[simp, norm_cast]
/-
**PNat.coprime_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：coprime_coe {m n : Nat+} : Nat.Coprime ↑m ↑n ↔ m.Coprime n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.coe_inj`：coe_inj {m n : Nat+} : (m : Nat) = n ↔ m = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coprime_coe {m n : ℕ+} : Nat.Coprime ↑m ↑n ↔ m.Coprime n := by
  unfold Nat.Coprime Coprime
  rw [← coe_inj]
  simp
/-
**PNat.Coprime.mul** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime`。
形式化陈述：∀ {k m n : ℕ+}, m.Coprime k → n.Coprime k → (m * n).Coprime k
参数：m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.coprime_coe`：coprime_coe {m n : Nat+} : Nat.Coprime ↑m ↑n ↔ m.Copri
me n
· 使用定理 `PNat.mul_coe`：mul_coe (m n : Nat+) : ((m * n : Nat+) : Nat) = m * n
· 使用定理 `Nat.Coprime.mul_left`：∀ {m k n : ℕ}, m.Coprime k → n.Coprime k → (m * n)
.Coprime k
-/
theorem Coprime.mul {k m n : ℕ+} : m.Coprime k → n.Coprime k → (m * n).Coprime k := by
  repeat rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul_left
/-
**PNat.Coprime.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime`。
形式化陈述：∀ {k m n : ℕ+}, k.Coprime m → k.Coprime n → k.Coprime (m * n)
参数：m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.coprime_coe`：coprime_coe {m n : Nat+} : Nat.Coprime ↑m ↑n ↔ m.Copri
me n
· 使用定理 `PNat.mul_coe`：mul_coe (m n : Nat+) : ((m * n : Nat+) : Nat) = m * n
· 使用定理 `Nat.Coprime.mul_right`：∀ {k m n : ℕ}, k.Coprime m → k.Coprime n → k.Copr
ime (m * n)
-/
theorem Coprime.mul_right {k m n : ℕ+} : k.Coprime m → k.Coprime n → k.Coprime (m * n) := by
  repeat rw [← coprime_coe]
  rw [mul_coe]
  apply Nat.Coprime.mul_right
/-
**PNat.gcd_comm** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_comm {m n : Nat+} : m.gcd n = n.gcd m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.eq`：eq {m n : Nat+} : (m : Nat) = n -> m = n
· 使用定理 `Nat.gcd_comm`：∀ (m n : ℕ), m.gcd n = n.gcd m
-/
theorem gcd_comm {m n : ℕ+} : m.gcd n = n.gcd m := by
  apply eq
  simp only [gcd_coe]
  apply Nat.gcd_comm
/-
**PNat.gcd_eq_left_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_eq_left_iff_dvd {m n : Nat+} : m.gcd n = m ↔ m ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_eq_left_iff_dvd`：∀ {m n : ℕ}, m.gcd n = m ↔ m ∣ n
· 使用定理 `PNat.coe_inj`：coe_inj {m n : Nat+} : (m : Nat) = n ↔ m = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem gcd_eq_left_iff_dvd {m n : ℕ+} : m.gcd n = m ↔ m ∣ n := by
  rw [dvd_iff, ← Nat.gcd_eq_left_iff_dvd, ← coe_inj]
  simp
/-
**PNat.gcd_eq_right_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_eq_right_iff_dvd {m n : Nat+} : n.gcd m = m ↔ m ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.gcd_comm`：gcd_comm {m n : Nat+} : m.gcd n = n.gcd m
· 使用定理 `PNat.gcd_eq_left_iff_dvd`：gcd_eq_left_iff_dvd {m n : Nat+} : m.gcd n = m
 ↔ m ∣ n
-/
theorem gcd_eq_right_iff_dvd {m n : ℕ+} : n.gcd m = m ↔ m ∣ n := by
  rw [gcd_comm]
  apply gcd_eq_left_iff_dvd
/-
**PNat.Coprime.gcd_mul_left_cancel** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime`。
形式化陈述：∀ (m : ℕ+) {n k : ℕ+}, k.Coprime n → (k * m).gcd n = m.gcd n
参数：m : ℕ+；k * m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.eq`：eq {m n : Nat+} : (m : Nat) = n -> m = n
· 使用定理 `Nat.Coprime.gcd_mul_left_cancel`：∀ {k n : ℕ} (m : ℕ), k.Coprime n → (k *
 m).gcd n = m.gcd n
-/
theorem Coprime.gcd_mul_left_cancel (m : ℕ+) {n k : ℕ+} :
    k.Coprime n → (k * m).gcd n = m.gcd n := by
  intro h; apply eq; simp only [gcd_coe, mul_coe]
  apply Nat.Coprime.gcd_mul_left_cancel; simpa
/-
**PNat.Coprime.gcd_mul_right_cancel** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime`。
形式化陈述：∀ (m : ℕ+) {n k : ℕ+}, k.Coprime n → (m * k).gcd n = m.gcd n
参数：m : ℕ+；m * k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PNat.Coprime.gcd_mul_left_cancel`：∀ (m : ℕ+) {n k : ℕ+}, k.Coprime n → (
k * m).gcd n = m.gcd n
-/
theorem Coprime.gcd_mul_right_cancel (m : ℕ+) {n k : ℕ+} :
    k.Coprime n → (m * k).gcd n = m.gcd n := by rw [mul_comm]; apply Coprime.gcd_mul_left_cancel
/-
**PNat.Coprime.gcd_mul_left_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime
`。
形式化陈述：∀ (m : ℕ+) {n k : ℕ+}, k.Coprime m → m.gcd (k * n) = m.gcd n
参数：m : ℕ+；k * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.gcd_comm`：gcd_comm {m n : Nat+} : m.gcd n = n.gcd m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.Coprime.gcd_mul_left_cancel`：∀ (m : ℕ+) {n k : ℕ+}, k.Coprime n → (
k * m).gcd n = m.gcd n
-/
theorem Coprime.gcd_mul_left_cancel_right (m : ℕ+) {n k : ℕ+} :
    k.Coprime m → m.gcd (k * n) = m.gcd n := by
  intro h; iterate 2 rw [gcd_comm]; symm
  apply Coprime.gcd_mul_left_cancel _ h
/-
**PNat.Coprime.gcd_mul_right_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprim
e`。
形式化陈述：∀ (m : ℕ+) {n k : ℕ+}, k.Coprime m → m.gcd (n * k) = m.gcd n
参数：m : ℕ+；n * k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PNat.Coprime.gcd_mul_left_cancel_right`：∀ (m : ℕ+) {n k : ℕ+}, k.Coprime
 m → m.gcd (k * n) = m.gcd n
-/
theorem Coprime.gcd_mul_right_cancel_right (m : ℕ+) {n k : ℕ+} :
    k.Coprime m → m.gcd (n * k) = m.gcd n := by
  rw [mul_comm]
  apply Coprime.gcd_mul_left_cancel_right

@[simp]
/-
**PNat.one_gcd** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：one_gcd {n : Nat+} : gcd 1 n = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.gcd_eq_left_iff_dvd`：gcd_eq_left_iff_dvd {m n : Nat+} : m.gcd n = m
 ↔ m ∣ n
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
theorem one_gcd {n : ℕ+} : gcd 1 n = 1 := by
  rw [gcd_eq_left_iff_dvd]
  apply one_dvd

@[simp]
/-
**PNat.gcd_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：gcd_one {n : Nat+} : gcd n 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.gcd_comm`：gcd_comm {m n : Nat+} : m.gcd n = n.gcd m
· 使用定理 `PNat.one_gcd`：one_gcd {n : Nat+} : gcd 1 n = 1
-/
theorem gcd_one {n : ℕ+} : gcd n 1 = 1 := by
  rw [gcd_comm]
  apply one_gcd

@[symm]
/-
**PNat.Coprime.symm** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime`。
形式化陈述：∀ {m n : ℕ+}, m.Coprime n → n.Coprime m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.gcd_comm`：gcd_comm {m n : Nat+} : m.gcd n = n.gcd m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem Coprime.symm {m n : ℕ+} : m.Coprime n → n.Coprime m := by
  unfold Coprime
  rw [gcd_comm]
  simp

@[simp]
/-
**PNat.one_coprime** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：one_coprime {n : Nat+} : (1 : Nat+).Coprime n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.one_gcd`：one_gcd {n : Nat+} : gcd 1 n = 1
-/
theorem one_coprime {n : ℕ+} : (1 : ℕ+).Coprime n :=
  one_gcd

@[simp]
/-
**PNat.coprime_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：coprime_one {n : Nat+} : n.Coprime 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.Coprime.symm`：∀ {m n : ℕ+}, m.Coprime n → n.Coprime m
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PNat.one_coprime`：one_coprime {n : Nat+} : (1 : Nat+).Coprime n
-/
theorem coprime_one {n : ℕ+} : n.Coprime 1 :=
  Coprime.symm one_coprime
/-
**PNat.Coprime.coprime_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime`。
形式化陈述：∀ {m k n : ℕ+}, m ∣ k → k.Coprime n → m.Coprime n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.coprime_coe`：coprime_coe {m n : Nat+} : Nat.Coprime ↑m ↑n ↔ m.Copri
me n
· 使用定理 `Nat.Coprime.coprime_dvd_left`：∀ {m k n : ℕ}, m ∣ k → k.Coprime n → m.Cop
rime n
-/
theorem Coprime.coprime_dvd_left {m k n : ℕ+} : m ∣ k → k.Coprime n → m.Coprime n := by
  rw [dvd_iff]
  repeat rw [← coprime_coe]
  apply Nat.Coprime.coprime_dvd_left
/-
**PNat.Coprime.factor_eq_gcd_left** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime`。
形式化陈述：∀ {a b m n : ℕ+}, m.Coprime n → a ∣ m → b ∣ n → a = (a * b).gcd m
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.gcd_eq_left_iff_dvd`：gcd_eq_left_iff_dvd {m n : Nat+} : m.gcd n = m
 ↔ m ∣ n
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `PNat.Coprime.gcd_mul_right_cancel`：∀ (m : ℕ+) {n k : ℕ+}, k.Coprime n → 
(m * k).gcd n = m.gcd n
· 使用定理 `PNat.Coprime.coprime_dvd_left`：∀ {m k n : ℕ+}, m ∣ k → k.Coprime n → m.C
oprime n
· 使用定理 `PNat.Coprime.symm`：∀ {m n : ℕ+}, m.Coprime n → n.Coprime m
-/
theorem Coprime.factor_eq_gcd_left {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n) :
    a = (a * b).gcd m := by
  rw [← gcd_eq_left_iff_dvd] at am
  conv_lhs => rw [← am]
  rw [eq_comm]
  apply Coprime.gcd_mul_right_cancel a
  apply Coprime.coprime_dvd_left bn cop.symm
/-
**PNat.Coprime.factor_eq_gcd_right** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime`。
形式化陈述：∀ {a b m n : ℕ+}, m.Coprime n → a ∣ m → b ∣ n → a = (b * a).gcd m
参数：b * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PNat.Coprime.factor_eq_gcd_left`：∀ {a b m n : ℕ+}, m.Coprime n → a ∣ m →
 b ∣ n → a = (a * b).gcd m
-/
theorem Coprime.factor_eq_gcd_right {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m) (bn : b ∣ n) :
    a = (b * a).gcd m := by rw [mul_comm]; apply Coprime.factor_eq_gcd_left cop am bn
/-
**PNat.Coprime.factor_eq_gcd_left_right** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime`
。
形式化陈述：∀ {a b m n : ℕ+}, m.Coprime n → a ∣ m → b ∣ n → a = m.gcd (a * b)
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.gcd_comm`：gcd_comm {m n : Nat+} : m.gcd n = n.gcd m
· 使用定理 `PNat.Coprime.factor_eq_gcd_left`：∀ {a b m n : ℕ+}, m.Coprime n → a ∣ m →
 b ∣ n → a = (a * b).gcd m
-/
theorem Coprime.factor_eq_gcd_left_right {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m)
    (bn : b ∣ n) : a = m.gcd (a * b) := by rw [gcd_comm]; apply Coprime.factor_eq_gcd_left cop am bn
/-
**PNat.Coprime.factor_eq_gcd_right_right** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime
`。
形式化陈述：∀ {a b m n : ℕ+}, m.Coprime n → a ∣ m → b ∣ n → a = m.gcd (b * a)
参数：b * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.gcd_comm`：gcd_comm {m n : Nat+} : m.gcd n = n.gcd m
· 使用定理 `PNat.Coprime.factor_eq_gcd_right`：∀ {a b m n : ℕ+}, m.Coprime n → a ∣ m 
→ b ∣ n → a = (b * a).gcd m
-/
theorem Coprime.factor_eq_gcd_right_right {a b m n : ℕ+} (cop : m.Coprime n) (am : a ∣ m)
    (bn : b ∣ n) : a = m.gcd (b * a) := by
  rw [gcd_comm]
  apply Coprime.factor_eq_gcd_right cop am bn
/-
**PNat.Coprime.gcd_mul** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime`。
形式化陈述：∀ (k : ℕ+) {m n : ℕ+}, m.Coprime n → k.gcd (m * n) = k.gcd m * k.gcd n
参数：k : ℕ+；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.eq`：eq {m n : Nat+} : (m : Nat) = n -> m = n
· 使用定理 `Nat.Coprime.gcd_mul`：∀ {m n : ℕ} (k : ℕ), m.Coprime n → k.gcd (m * n) = 
k.gcd m * k.gcd n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.coprime_coe`：coprime_coe {m n : Nat+} : Nat.Coprime ↑m ↑n ↔ m.Copri
me n
-/
theorem Coprime.gcd_mul (k : ℕ+) {m n : ℕ+} (h : m.Coprime n) :
    k.gcd (m * n) = k.gcd m * k.gcd n := by
  rw [← coprime_coe] at h; apply eq
  simp only [gcd_coe, mul_coe]; apply Nat.Coprime.gcd_mul k h
/-
**PNat.Coprime.pow** 是 Mathlib 中的一个定理，位于命名空间 `PNat.Coprime`。
形式化陈述：∀ {m n : ℕ+} (k l : ℕ), m.Coprime n → (↑m ^ k).Coprime (↑n ^ l)
参数：k l : ℕ；↑m ^ k；↑n ^ l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.pow`：∀ {k l : ℕ} (m n : ℕ), k.Coprime l → (k ^ m).Coprime (l
 ^ n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.coprime_coe`：coprime_coe {m n : Nat+} : Nat.Coprime ↑m ↑n ↔ m.Copri
me n
-/
theorem Coprime.pow {m n : ℕ+} (k l : ℕ) (h : m.Coprime n) : (m ^ k : ℕ).Coprime (n ^ l) := by
  rw [← coprime_coe] at *; apply Nat.Coprime.pow; apply h

end Coprime

end PNat

