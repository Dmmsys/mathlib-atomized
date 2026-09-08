/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Prime.Pow
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime powers

This file deals with prime powers: numbers which are positive integer powers of a single prime.
-/

@[expose] public section
assert_not_exists Nat.divisors

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

/-- `n` is a prime power if there is a prime `p` and a positive natural `k` such that `n` can be
written as `p^k`. -/
@[wikidata Q1667469]
/-
**IsPrimePow** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsPrimePow : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n` is a prime power if there is a prime `p` and a positive natural `k` such tha
t `n` can be
written as `p^k`.
-/
def IsPrimePow : Prop :=
  ∃ (p : R) (k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n
/-
**isPrimePow_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_def : IsPrimePow n ↔ exists (p : R) (k : Nat), Prime p ∧ 0 < k 
∧ p ^ k = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isPrimePow_def : IsPrimePow n ↔ ∃ (p : R) (k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n :=
  Iff.rfl

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a prime `p` and a
natural `k` such that `n` can be written as `p^(k+1)`. -/
/-
**isPrimePow_iff_pow_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_iff_pow_succ : IsPrimePow n ↔ exists (p : R) (k : Nat), Prime p
 ∧ p ^ (k + 1) = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isPrimePow_def`：isPrimePow_def : IsPrimePow n ↔ exists (p : R) (k : Nat)
, Prime p ∧ 0 < k ∧ p ^ k = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用引理 `Nat.succ_pos'`：succ_pos' : 0 < succ n

--- 原说明 ---
An equivalent definition for prime powers: `n` is a prime power iff there is a p
rime `p` and a
natural `k` such that `n` can be written as `p^(k+1)`.
-/
theorem isPrimePow_iff_pow_succ : IsPrimePow n ↔ ∃ (p : R) (k : ℕ), Prime p ∧ p ^ (k + 1) = n :=
  (isPrimePow_def _).trans
    ⟨fun ⟨p, k, hp, hk, hn⟩ => ⟨p, k - 1, hp, by rwa [Nat.sub_add_cancel hk]⟩, fun ⟨_, _, hp, hn⟩ =>
      ⟨_, _, hp, Nat.succ_pos', hn⟩⟩
/-
**not_isPrimePow_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isPrimePow_zero [IsReduced R] : ¬IsPrimePow (0 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_isPrimePow_zero [IsReduced R] : ¬IsPrimePow (0 : R) := by
  simp only [isPrimePow_def, not_exists, not_and', and_imp]
  intro x n _hn hx
  rw [eq_zero_of_pow_eq_zero hx]
  simp
/-
**IsPrimePow.not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimePow.not_isUnit {n : R} (h : IsPrimePow n) : ¬IsUnit n
参数：h : IsPrimePow n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `isUnit_pow_iff`：∀ {M : Type u_1} [inst : Monoid M] {n : ℕ} {a : M}, n ≠ 
0 → (IsUnit (a ^ n) ↔ IsUnit a)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
-/
theorem IsPrimePow.not_isUnit {n : R} (h : IsPrimePow n) : ¬IsUnit n :=
  let ⟨_p, _k, hp, hk, hn⟩ := h
  hn ▸ (isUnit_pow_iff hk.ne').not.mpr hp.not_isUnit

@[deprecated (since := "2026-08-02")]
alias IsPrimePow.not_unit := IsPrimePow.not_isUnit
/-
**IsUnit.not_isPrimePow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUnit.not_isPrimePow {n : R} (h : IsUnit n) : ¬IsPrimePow n
参数：h : IsUnit n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimePow.not_isUnit`：IsPrimePow.not_isUnit {n : R} (h : IsPrimePow n) 
: ¬IsUnit n
-/
theorem IsUnit.not_isPrimePow {n : R} (h : IsUnit n) : ¬IsPrimePow n := fun h' => h'.not_isUnit h
/-
**not_isPrimePow_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isPrimePow_one : ¬IsPrimePow (1 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.not_isPrimePow`：IsUnit.not_isPrimePow {n : R} (h : IsUnit n) : ¬I
sPrimePow n
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem not_isPrimePow_one : ¬IsPrimePow (1 : R) :=
  isUnit_one.not_isPrimePow
/-
**Prime.isPrimePow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.isPrimePow {p : R} (hp : Prime p) : IsPrimePow p
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Prime.isPrimePow {p : R} (hp : Prime p) : IsPrimePow p :=
  ⟨p, 1, hp, zero_lt_one, by simp⟩
/-
**IsPrimePow.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimePow.pow {n : R} (hn : IsPrimePow n) {k : Nat} (hk : k != 0) : IsPri
mePow (n ^ k)
参数：hn : IsPrimePow n；hk : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
-/
theorem IsPrimePow.pow {n : R} (hn : IsPrimePow n) {k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) :=
  let ⟨p, k', hp, hk', hn⟩ := hn
  ⟨p, k * k', hp, mul_pos hk.bot_lt hk', by rw [pow_mul', hn]⟩
/-
**IsPrimePow.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimePow.ne_zero [IsReduced R] {n : R} (h : IsPrimePow n) : n != 0
参数：h : IsPrimePow n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isPrimePow_zero`：not_isPrimePow_zero [IsReduced R] : ¬IsPrimePow (0 
: R)
-/
theorem IsPrimePow.ne_zero [IsReduced R] {n : R} (h : IsPrimePow n) : n ≠ 0 := fun t =>
  not_isPrimePow_zero (t ▸ h)
/-
**IsPrimePow.ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n != 1
参数：h : IsPrimePow n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isPrimePow_one`：not_isPrimePow_one : ¬IsPrimePow (1 : R)
-/
theorem IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n ≠ 1 := fun t =>
  not_isPrimePow_one (t ▸ h)

section Nat

/-
**isPrimePow_nat_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_nat_iff (n : Nat) : IsPrimePow n ↔ exists p k : Nat, Nat.Prime 
p ∧ 0 < k ∧ p ^ k = n
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPrimePow_nat_iff (n : ℕ) : IsPrimePow n ↔ ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p ^ k = n := by
  simp only [isPrimePow_def, Nat.prime_iff]
/-
**Nat.Prime.isPrimePow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Prime.isPrimePow {p : Nat} (hp : p.Prime) : IsPrimePow p
参数：hp : p.Prime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.isPrimePow`：Prime.isPrimePow {p : R} (hp : Prime p) : IsPrimePow p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
-/
theorem Nat.Prime.isPrimePow {p : ℕ} (hp : p.Prime) : IsPrimePow p :=
  _root_.Prime.isPrimePow (prime_iff.mp hp)
/-
**isPrimePow_nat_iff_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_nat_iff_bounded (n : Nat) : IsPrimePow n ↔ exists p : Nat, p <=
 n ∧ exists k : Nat, k <= n ∧ p.Prime ∧ 0 < k ∧ p ^ k = n
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPrimePow_nat_iff`：isPrimePow_nat_iff (n : Nat) : IsPrimePow n ↔ exists
 p k : Nat, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
-/
theorem isPrimePow_nat_iff_bounded (n : ℕ) :
    IsPrimePow n ↔ ∃ p : ℕ, p ≤ n ∧ ∃ k : ℕ, k ≤ n ∧ p.Prime ∧ 0 < k ∧ p ^ k = n := by
  rw [isPrimePow_nat_iff]
  refine Iff.symm ⟨fun ⟨p, _, k, _, hp, hk, hn⟩ => ⟨p, k, hp, hk, hn⟩, ?_⟩
  rintro ⟨p, k, hp, hk, rfl⟩
  refine ⟨p, ?_, k, (Nat.lt_pow_self hp.one_lt).le, hp, hk, rfl⟩
  conv => {lhs; rw [← (pow_one p)]}
  exact Nat.pow_le_pow_right hp.one_lt.le hk
/-
**isPrimePow_nat_iff_bounded_log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_nat_iff_bounded_log (n : Nat) : IsPrimePow n ↔ exists k : Nat, 
k <= Nat.log 2 n ∧ 0 < k ∧ exists p : Nat, p <= n ∧ n = p ^ k ∧ p.Prime
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPrimePow_nat_iff`：isPrimePow_nat_iff (n : Nat) : IsPrimePow n ↔ exists
 p k : Nat, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.log_pow`：log_pow {b : Nat} (hb : 1 < b) (x : Nat) : log b (b ^ x) = 
x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.log_mono`：log_mono {b c m n : Nat} (hc : 1 < c) (hb : c <= b) (hmn :
 m <= n) : log b m <= log c n
· 使用定理 `Nat.one_lt_two`：1 < 2
· 使用定理 `Nat.AtLeastTwo.prop`：∀ {n : ℕ} [self : n.AtLeastTwo], 2 ≤ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.pow_le_pow_left`：∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Nat.le_pow`：∀ {a b : ℕ}, 0 < b → a ≤ a ^ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isPrimePow_nat_iff_bounded_log (n : ℕ) :
    IsPrimePow n
      ↔ ∃ k : ℕ, k ≤ Nat.log 2 n ∧ 0 < k ∧ ∃ p : ℕ, p ≤ n ∧ n = p ^ k ∧ p.Prime := by
  rw [isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp', hk', rfl⟩
    refine ⟨k, ?_, hk', ⟨p, Nat.le_pow hk', rfl, hp'⟩⟩
    · calc
        k = Nat.log 2 (2 ^ k) := by simp
        _ ≤ Nat.log 2 (p ^ k) := Nat.log_mono Nat.one_lt_two Nat.AtLeastTwo.prop
                                   (Nat.pow_le_pow_left (Nat.Prime.two_le hp') k)
  · rintro ⟨k, hk, hk', ⟨p, hp, rfl, hp'⟩⟩
    exact ⟨p, k, hp', hk', rfl⟩
/-
**isPrimePow_nat_iff_bounded_log_minFac** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_nat_iff_bounded_log_minFac (n : Nat) : IsPrimePow n ↔ exists k 
: Nat, k <= Nat.log 2 n ∧ 0 < k ∧ n = n.minFac ^ k
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPrimePow_nat_iff_bounded_log`：isPrimePow_nat_iff_bounded_log (n : Nat)
 : IsPrimePow n ↔ exists k : Nat, k <= Nat.log 2 n ∧ 0 < k ∧ exists p : Nat, p <
= n ∧ n = p ^ k ∧ p.…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.log_one_right`：log_one_right (b : Nat) : log b 1 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Nat.minFac_one`：minFac_one : minFac 1 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.pow_minFac`：∀ {p k : ℕ}, Nat.Prime p → k ≠ 0 → (p ^ k).minFac 
= p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.minFac_le`：minFac_le {n : Nat} (H : 0 < n) : minFac n <= n
-/
theorem isPrimePow_nat_iff_bounded_log_minFac (n : ℕ) :
    IsPrimePow n
      ↔ ∃ k : ℕ, k ≤ Nat.log 2 n ∧ 0 < k ∧ n = n.minFac ^ k := by
  rw [isPrimePow_nat_iff_bounded_log]
  obtain rfl | h := eq_or_ne n 1
  · simp
  constructor
  · rintro ⟨k, hkle, hk_pos, p, hle, heq, hprime⟩
    refine ⟨k, hkle, hk_pos, ?_⟩
    rw [heq, hprime.pow_minFac hk_pos.ne']
  · rintro ⟨k, hkle, hk_pos, heq⟩
    refine ⟨k, hkle, hk_pos, n.minFac, Nat.minFac_le ?_, heq, ?_⟩
    · grind [Nat.minFac_prime_iff, nonpos_iff_eq_zero, Nat.log_zero_right, lt_self_iff_false]
    · grind [Nat.minFac_prime_iff]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} : Decidable (IsPrimePow n) :=
  decidable_of_iff' _ (isPrimePow_nat_iff_bounded_log_minFac n)
/-
**IsPrimePow.dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimePow.dvd {n m : Nat} (hn : IsPrimePow n) (hm : m ∣ n) (hm₁ : m != 1)
 : IsPrimePow m
参数：hn : IsPrimePow n；hm : m ∣ n；hm₁ : m != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsPrimePow.dvd {n m : ℕ} (hn : IsPrimePow n) (hm : m ∣ n) (hm₁ : m ≠ 1) : IsPrimePow m := by
  grind [isPrimePow_nat_iff, Nat.dvd_prime_pow, Nat.pow_eq_one]
/-
**IsPrimePow.two_le** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimePow`。
形式化陈述：∀ {n : ℕ}, IsPrimePow n → 2 ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isPrimePow_zero`：not_isPrimePow_zero [IsReduced R] : ¬IsPrimePow (0 
: R)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `not_isPrimePow_one`：not_isPrimePow_one : ¬IsPrimePow (1 : R)
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
-/
theorem IsPrimePow.two_le : ∀ {n : ℕ}, IsPrimePow n → 2 ≤ n
  | 0, h => (not_isPrimePow_zero h).elim
  | 1, h => (not_isPrimePow_one h).elim
  | _n + 2, _ => le_add_self
/-
**IsPrimePow.pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimePow.pos {n : Nat} (hn : IsPrimePow n) : 0 < n
参数：hn : IsPrimePow n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `IsPrimePow.two_le`：∀ {n : ℕ}, IsPrimePow n → 2 ≤ n
-/
theorem IsPrimePow.pos {n : ℕ} (hn : IsPrimePow n) : 0 < n :=
  pos_of_gt hn.two_le
/-
**IsPrimePow.one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimePow.one_lt {n : Nat} (h : IsPrimePow n) : 1 < n
参数：h : IsPrimePow n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimePow.two_le`：∀ {n : ℕ}, IsPrimePow n → 2 ≤ n
-/
theorem IsPrimePow.one_lt {n : ℕ} (h : IsPrimePow n) : 1 < n :=
  h.two_le

end Nat

