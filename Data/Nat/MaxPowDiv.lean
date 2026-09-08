/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard, Yury Kudryashov
-/
module

public import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Notation

/-!
# The maximal power of one natural number dividing another

Here we introduce `p.maxPowDvd n` which returns the maximal `k : ℕ` for
which `p ^ k ∣ n` with the convention that `maxPowDvd 1 n = 0` for all `n`.

We prove enough about `maxPowDvd` in this file to show equality with `Nat.padicValNat` in
`padicValNat.padicValNat_eq_maxPowDvd`.

The implementation of `maxPowDvd` improves on the speed of `padicValNat`.
-/

@[expose] public section

namespace Nat

/--
Find largest `k : ℕ` such that `p ^ k ∣ n` for any `p : ℕ`, as well as the ratio `n / p ^ k`.

The implementation recurses from `(p, n)` to `(p * p, n)`,
so the recursion depth is $$O(\log(\nu_p(n)))$$, thus it is $$O(\log(\log(n)))$$.
-/
/-
**Nat.maxPowDvdDiv** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv (p n : Nat) : Nat × Nat
参数：p n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Find largest `k : ℕ` such that `p ^ k ∣ n` for any `p : ℕ`, as well as the ratio
 `n / p ^ k`.

The implementation recurses from `(p, n)` to `(p * p, n)`,
so the recursion depth is $$O(\log(\nu_p(n)))$$, thus it is $$O(\log(\log(n)))$$
.
-/
def maxPowDvdDiv (p n : ℕ) : ℕ × ℕ :=
  if H : 1 < p ∧ n ≠ 0 then
    go p H
  else
    (0, n)
  where
  /-- Auxiliary definition for `Nat.maxPowDvdDiv`. -/
  go (p : ℕ) (hp : 1 < p ∧ n ≠ 0) :=
    if hmod : n % p = 0 then
      let (e, q) := go (p * p) <| by simp [Nat.one_lt_mul_iff, hp, Nat.lt_trans Nat.one_pos]
      if q % p = 0 then (2 * e + 1, q / p) else (2 * e, q)
    else
      (0, n)
  termination_by n / p
  decreasing_by
    rw [← Nat.dvd_iff_mod_eq_zero] at hmod
    rcases hmod with ⟨m, rfl⟩
    have hp₀ : 0 < p := Nat.lt_trans Nat.one_pos hp.1
    rw [Nat.mul_div_mul_left _ _ hp₀, Nat.mul_div_cancel_left _ hp₀]
    exact Nat.div_lt_self (by grind) hp.1

/-- For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural number `k` such
that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults to `0`. -/
/-
**Nat._root_.padicValNat** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `p ≠ 1`, the `p`-adic valuation of a natural `n ≠ 0` is the largest natural 
number `k` such
that `p^k` divides `n`. If `n = 0` or `p = 1`, then `padicValNat p n` defaults t
o `0`.
-/
def _root_.padicValNat (p n : ℕ) : ℕ := (maxPowDvdDiv p n).fst

/-- Divide `n` by the maximal power of `p` that divides `n`. -/
/-
**Nat.divMaxPow** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：divMaxPow (n p : Nat) : Nat
参数：n p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Divide `n` by the maximal power of `p` that divides `n`.
-/
def divMaxPow (n p : ℕ) : ℕ := (maxPowDvdDiv p n).snd
/-
**Nat.maxPowDvdDiv.go_spec** 是 Mathlib 中的一个定理，位于命名空间 `Nat.maxPowDvdDiv`。
形式化陈述：∀ {n p : ℕ} (hnp : 1 < p ∧ n ≠ 0),   (Nat.maxPowDvdDiv.go n p hnp).2 * p ^
 (Nat.maxPowDvdDiv.go n p hnp).1 = n ∧ ¬p ∣ (Nat.maxPowDvdDiv.go n p hnp).2
参数：hnp : 1 < p ∧ n ≠ 0；Nat.maxPowDvdDiv.go n p hnp；Nat.maxPowDvdDiv.go n p hnp；N
at.maxPowDvdDiv.go n p hnp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.maxPowDvdDiv.go.induct_unfolding`：∀ (n : ℕ) (motive : (p : ℕ) → 1 < 
p ∧ n ≠ 0 → ℕ × ℕ → Prop),   (∀ (p : ℕ) (hp : 1 < p ∧ n ≠ 0),       n % p = 0 → 
        ∀ (e q : ℕ),      …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_trans`：∀ {n m k : ℕ}, n < m → m < k → n < k
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.two_mul`：∀ (n : ℕ), 2 * n = n + n
· 使用定理 `Nat.pow_add'`：∀ (a m n : ℕ), a ^ (m + n) = a ^ n * a ^ m
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `Nat.mul_pow`：∀ (a b n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.pow_add`：∀ (a m n : ℕ), a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
-/
theorem maxPowDvdDiv.go_spec {n p : ℕ} (hnp) :
    (go n p hnp).2 * p ^ (go n p hnp).1 = n ∧ ¬p ∣ (go n p hnp).2 := by
  fun_induction go with
  | case1 p hp hmod e q heq hqp ih =>
    rw [heq] at ih
    rcases ih with ⟨rfl, hdvd⟩
    have hp₀ : 0 < p := Nat.lt_trans Nat.one_pos hp.1
    simp_all [← Nat.dvd_iff_mod_eq_zero, Nat.pow_add', ← Nat.mul_assoc, Nat.div_mul_cancel,
      Nat.two_mul, Nat.mul_pow]
  | case2 p hp hmod e q heq hqp ih =>
    rw [heq] at ih
    rcases ih with ⟨rfl, hdvd⟩
    simp_all [Nat.dvd_iff_mod_eq_zero, Nat.two_mul, Nat.mul_pow, Nat.pow_add]
  | case3 =>
    simp_all [Nat.dvd_iff_mod_eq_zero]
/-
**Nat.maxPowDvdDiv_of_base_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv_of_base_le_one {p : Nat} (hp : p <= 1) (n : Nat) : maxPowDvdD
iv p n = (0, n)
参数：hp : p <= 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.not_lt_of_ge`：∀ {a b : ℕ}, b ≥ a → ¬b < a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem maxPowDvdDiv_of_base_le_one {p : ℕ} (hp : p ≤ 1) (n : ℕ) : maxPowDvdDiv p n = (0, n) := by
  simp [maxPowDvdDiv, Nat.not_lt_of_ge hp]

@[simp]
/-
**Nat.maxPowDvdDiv_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv_zero_left (n : Nat) : maxPowDvdDiv 0 n = (0, n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.maxPowDvdDiv_of_base_le_one`：maxPowDvdDiv_of_base_le_one {p : Nat} (
hp : p <= 1) (n : Nat) : maxPowDvdDiv p n = (0, n)
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
theorem maxPowDvdDiv_zero_left (n : ℕ) : maxPowDvdDiv 0 n = (0, n) :=
  maxPowDvdDiv_of_base_le_one (Nat.zero_le _) _

@[simp]
/-
**Nat._root_.padicValNat_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.padicValNat_zero_left (n : ℕ) : padicValNat 0 n = 0 := by simp [padicValNat]

@[simp]
/-
**Nat.divMaxPow_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divMaxPow_zero_right (n : Nat) : divMaxPow n 0 = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.maxPowDvdDiv_zero_left`：maxPowDvdDiv_zero_left (n : Nat) : maxPowDvd
Div 0 n = (0, n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divMaxPow_zero_right (n : ℕ) : divMaxPow n 0 = n := by simp [divMaxPow]

@[simp]
/-
**Nat.maxPowDvdDiv_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv_one_left (n : Nat) : maxPowDvdDiv 1 n = (0, n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.maxPowDvdDiv_of_base_le_one`：maxPowDvdDiv_of_base_le_one {p : Nat} (
hp : p <= 1) (n : Nat) : maxPowDvdDiv p n = (0, n)
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
-/
theorem maxPowDvdDiv_one_left (n : ℕ) : maxPowDvdDiv 1 n = (0, n) :=
  maxPowDvdDiv_of_base_le_one (Nat.le_refl _) _

@[simp]
/-
**Nat._root_.padicValNat_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.padicValNat_one_left (n : ℕ) : padicValNat 1 n = 0 := by simp [padicValNat]

@[simp]
/-
**Nat.divMaxPow_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divMaxPow_one_right (n : Nat) : divMaxPow n 1 = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.maxPowDvdDiv_one_left`：maxPowDvdDiv_one_left (n : Nat) : maxPowDvdDi
v 1 n = (0, n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divMaxPow_one_right (n : ℕ) : divMaxPow n 1 = n := by simp [divMaxPow]

@[simp]
/-
**Nat.maxPowDvdDiv_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv_zero_right (p : Nat) : maxPowDvdDiv p 0 = (0, 0)
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem maxPowDvdDiv_zero_right (p : ℕ) : maxPowDvdDiv p 0 = (0, 0) := by simp [maxPowDvdDiv]

@[simp]
/-
**Nat._root_.padicValNat_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.padicValNat_zero_right (p : ℕ) : padicValNat p 0 = 0 := by simp [padicValNat]

@[simp]
/-
**Nat.divMaxPow_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divMaxPow_zero_left (p : Nat) : divMaxPow 0 p = 0
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.maxPowDvdDiv_zero_right`：maxPowDvdDiv_zero_right (p : Nat) : maxPowD
vdDiv p 0 = (0, 0)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divMaxPow_zero_left (p : ℕ) : divMaxPow 0 p = 0 := by simp [divMaxPow]
/-
**Nat.maxPowDvdDiv_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv_of_not_dvd {p n : Nat} (h : ¬p ∣ n) : maxPowDvdDiv p n = (0, 
n)
参数：h : ¬p ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Nat.maxPowDvdDiv.go.eq_1`：∀ (n p : ℕ) (hp : 1 < p ∧ n ≠ 0),   Nat.maxPow
DvdDiv.go n p hp =     if hmod : n % p = 0 then       match Nat.maxPowDvdDiv.go 
n (p * p) ⋯ wi…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem maxPowDvdDiv_of_not_dvd {p n : ℕ} (h : ¬p ∣ n) : maxPowDvdDiv p n = (0, n) := by
  cases n with
  | zero => simp at h
  | succ n => simp [maxPowDvdDiv, Nat.dvd_iff_mod_eq_zero.not.mp h, maxPowDvdDiv.go]

@[simp]
/-
**Nat.maxPowDvdDiv_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv_one_right (p : Nat) : maxPowDvdDiv p 1 = (0, 1)
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.maxPowDvdDiv_one_left`：maxPowDvdDiv_one_left (n : Nat) : maxPowDvdDi
v 1 n = (0, n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.maxPowDvdDiv_of_not_dvd`：maxPowDvdDiv_of_not_dvd {p n : Nat} (h : ¬p
 ∣ n) : maxPowDvdDiv p n = (0, n)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem maxPowDvdDiv_one_right (p : ℕ) : maxPowDvdDiv p 1 = (0, 1) := by
  rcases eq_or_ne p 1 with rfl | hp <;> simp [maxPowDvdDiv_of_not_dvd, *]

@[simp]
/-
**Nat._root_.padicValNat_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.padicValNat_one_right (p : ℕ) : padicValNat p 1 = 0 := by simp [padicValNat]

@[simp]
/-
**Nat.divMaxPow_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divMaxPow_one_left (p : Nat) : divMaxPow 1 p = 1
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.maxPowDvdDiv_one_right`：maxPowDvdDiv_one_right (p : Nat) : maxPowDvd
Div p 1 = (0, 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divMaxPow_one_left (p : ℕ) : divMaxPow 1 p = 1 := by simp [divMaxPow]

open maxPowDvdDiv in
@[simp]
/-
**Nat.divMaxPow_mul_pow_padicValNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divMaxPow_mul_pow_padicValNat (p n : Nat) : divMaxPow n p * p ^ padicValNa
t p n = n
参数：p n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.maxPowDvdDiv.fun_cases_unfolding`：∀ (p n : ℕ) (motive : ℕ × ℕ → Prop
),   (∀ (h : 1 < p ∧ n ≠ 0), motive (Nat.maxPowDvdDiv.go n p h)) →     (¬(1 < p 
∧ n ≠ 0) → motive (0, n)) …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.maxPowDvdDiv.go_spec`：∀ {n p : ℕ} (hnp : 1 < p ∧ n ≠ 0),   (Nat.maxP
owDvdDiv.go n p hnp).2 * p ^ (Nat.maxPowDvdDiv.go n p hnp).1 = n ∧ ¬p ∣ (Nat.max
PowDvdDiv.go n…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divMaxPow_mul_pow_padicValNat (p n : ℕ) : divMaxPow n p * p ^ padicValNat p n = n := by
  unfold divMaxPow padicValNat
  fun_cases maxPowDvdDiv with
  | case1 h => exact go_spec h |>.1
  | case2 h => simp

@[simp]
/-
**Nat.pow_padicValNat_mul_divMaxPow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_padicValNat_mul_divMaxPow (p n : Nat) : p ^ padicValNat p n * divMaxPo
w n p = n
参数：p n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.divMaxPow_mul_pow_padicValNat`：divMaxPow_mul_pow_padicValNat (p n : 
Nat) : divMaxPow n p * p ^ padicValNat p n = n
-/
theorem pow_padicValNat_mul_divMaxPow (p n : ℕ) : p ^ padicValNat p n * divMaxPow n p = n := by
  rw [Nat.mul_comm, divMaxPow_mul_pow_padicValNat]
/-
**Nat._root_.pow_padicValNat_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.pow_padicValNat_dvd {p n : ℕ} : p ^ padicValNat p n ∣ n :=
  ⟨divMaxPow n p, by simp⟩
/-
**Nat.padicValNat_lt_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：padicValNat_lt_self {p n : Nat} (hn : n != 0) : padicValNat p n < n
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_zero_left`：∀ (n : ℕ), padicValNat 0 n = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `padicValNat_one_left`：∀ (n : ℕ), padicValNat 1 n = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pow_lt_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n < a ^ m ↔ n < m)
· 使用定理 `Nat.lt_of_le_of_lt`：∀ {n m k : ℕ}, n ≤ m → m < k → n < k
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `pow_padicValNat_dvd`：∀ {p n : ℕ}, p ^ padicValNat p n ∣ n
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
-/
theorem padicValNat_lt_self {p n : ℕ} (hn : n ≠ 0) : padicValNat p n < n := by
  match p with
  | 0 | 1 => simp [Nat.pos_of_ne_zero hn]
  | p + 2 =>
    apply (p + 2 |>.pow_lt_pow_iff_right <| by lia).mp
    apply Nat.lt_of_le_of_lt ?_ <| Nat.lt_pow_self <| by lia
    exact le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd
/-
**Nat.padicValNat_le_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：padicValNat_le_self {p : Nat} (n : Nat) : padicValNat p n <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_zero_right`：∀ (p : ℕ), padicValNat p 0 = 0
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.padicValNat_lt_self`：padicValNat_lt_self {p n : Nat} (hn : n != 0) :
 padicValNat p n < n
-/
theorem padicValNat_le_self {p : ℕ} (n : ℕ) : padicValNat p n ≤ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · exact Nat.le_of_lt <| padicValNat_lt_self hn
/-
**Nat.not_dvd_divMaxPow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_dvd_divMaxPow {p n : Nat} (hp : 1 < p) (hn : n != 0) : ¬p ∣ divMaxPow 
n p
参数：hp : 1 < p；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
theorem not_dvd_divMaxPow {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) : ¬p ∣ divMaxPow n p := by
  simp [divMaxPow, maxPowDvdDiv, maxPowDvdDiv.go_spec, *]
/-
**Nat.pow_dvd_iff_le_of_spec** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem pow_dvd_iff_le_of_spec {p k n a b : ℕ} (hp : 1 < p) (hn : n ≠ 0)
    (hab : p ^ a * b = n) (hb : ¬p ∣ b) : p ^ k ∣ n ↔ k ≤ a := by
  subst hab
  cases Nat.lt_or_ge a k with
  | inl hlt =>
    refine iff_of_false (fun hdvd ↦ ?_) (Nat.not_le_of_lt hlt)
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [Nat.add_assoc, Nat.pow_add,
      Nat.mul_dvd_mul_iff_left (Nat.pow_pos (Nat.zero_lt_of_lt hp))] at hdvd
    exact hb <| Nat.dvd_of_pow_dvd (Nat.le_add_left 1 l) hdvd
  | inr hle =>
    refine iff_of_true (Nat.dvd_mul_right_of_dvd ?_ _) hle
    exact Nat.pow_dvd_pow p hle

/-- If `p > 1`, `n > 0`, then the first component of `maxPowDvdDiv` is the maximal power of `p`
that divides `n`. -/
/-
**Nat.pow_dvd_iff_le_padicValNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_dvd_iff_le_padicValNat {p k n : Nat} (hp : p != 1) (hn : n != 0) : p ^
 k ∣ n ↔ k <= padicValNat p n
参数：hp : p != 1；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_zero_left`：∀ (n : ℕ), padicValNat 0 n = 0
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_pow_of_pos`：∀ (n : ℕ), 0 < n → 0 ^ n = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `_private.Mathlib.Data.Nat.MaxPowDiv.0.Nat.pow_dvd_iff_le_of_spec`：∀ {p k
 n a b : ℕ}, 1 < p → n ≠ 0 → p ^ a * b = n → ¬p ∣ b → (p ^ k ∣ n ↔ k ≤ a)
· 使用定理 `Nat.pow_padicValNat_mul_divMaxPow`：pow_padicValNat_mul_divMaxPow (p n : 
Nat) : p ^ padicValNat p n * divMaxPow n p = n
· 使用定理 `Nat.not_dvd_divMaxPow`：not_dvd_divMaxPow {p n : Nat} (hp : 1 < p) (hn : 
n != 0) : ¬p ∣ divMaxPow n p

--- 原说明 ---
If `p > 1`, `n > 0`, then the first component of `maxPowDvdDiv` is the maximal p
ower of `p`
that divides `n`.
-/
theorem pow_dvd_iff_le_padicValNat {p k n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ padicValNat p n := by
  obtain rfl | hp₁ : p = 0 ∨ 1 < p := by grind
  · rcases k.eq_zero_or_pos with rfl | hk <;> simp [Nat.ne_of_gt, *]
  · exact pow_dvd_iff_le_of_spec hp₁ hn (pow_padicValNat_mul_divMaxPow p n)
      (not_dvd_divMaxPow hp₁ hn)
/-
**Nat.maxPowDvdDiv_of_pow_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv_of_pow_mul_eq {p n k l : Nat} (hn : n != 0) (h : p ^ k * l = 
n) (hl : ¬p ∣ l) : maxPowDvdDiv p n = (k, l)
参数：hn : n != 0；h : p ^ k * l = n；hl : ¬p ∣ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.maxPowDvdDiv_zero_left`：maxPowDvdDiv_zero_left (n : Nat) : maxPowDvd
Div 0 n = (0, n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.zero_pow_of_pos`：∀ (n : ℕ), 0 < n → 0 ^ n = 0
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.one_pow`：∀ (n : ℕ), 1 ^ n = 1
· 使用定理 `Nat.le_antisymm`：∀ {n m : ℕ}, n ≤ m → m ≤ n → n = m
· 使用定理 `padicValNat.eq_1`：∀ (p n : ℕ), padicValNat p n = (p.maxPowDvdDiv n).1
· 使用定理 `Nat.pow_dvd_iff_le_padicValNat`：pow_dvd_iff_le_padicValNat {p k n : Nat}
 (hp : p != 1) (hn : n != 0) : p ^ k ∣ n ↔ k <= padicValNat p n
· 使用定理 `Nat.ne_of_gt`：∀ {a b : ℕ}, b < a → a ≠ b
· 使用定理 `_private.Mathlib.Data.Nat.MaxPowDiv.0.Nat.pow_dvd_iff_le_of_spec`：∀ {p k
 n a b : ℕ}, 1 < p → n ≠ 0 → p ^ a * b = n → ¬p ∣ b → (p ^ k ∣ n ↔ k ≤ a)
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Nat.mul_left_cancel_iff`：∀ {n : ℕ}, 0 < n → ∀ {m k : ℕ}, n * m = n * k ↔
 m = k
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `Nat.pow_padicValNat_mul_divMaxPow`：pow_padicValNat_mul_divMaxPow (p n : 
Nat) : p ^ padicValNat p n * divMaxPow n p = n
-/
theorem maxPowDvdDiv_of_pow_mul_eq {p n k l : ℕ} (hn : n ≠ 0) (h : p ^ k * l = n)
    (hl : ¬p ∣ l) : maxPowDvdDiv p n = (k, l) := by
  obtain rfl | rfl | hp : p = 0 ∨ p = 1 ∨ 1 < p := by grind
  · cases k.eq_zero_or_pos <;> simp_all
  · simp_all
  · have hk : k = (p.maxPowDvdDiv n).1 := by
      · apply Nat.le_antisymm
        · rw [← padicValNat, ← pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp) hn,
            pow_dvd_iff_le_of_spec hp hn h hl]
          apply Nat.le_refl
        · rw [← pow_dvd_iff_le_of_spec hp hn h hl, pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp) hn]
          apply Nat.le_refl
    rw [← pow_padicValNat_mul_divMaxPow p n, hk, padicValNat, Nat.mul_left_cancel_iff] at h
    · exact Prod.ext hk.symm h.symm
    · exact Nat.pow_pos <| Nat.zero_lt_of_lt hp

@[simp]
/-
**Nat.maxPowDvdDiv_base_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv_base_pow_mul {p n : Nat} (hp : 1 < p) (hn : n != 0) (k : Nat)
 : p.maxPowDvdDiv (p ^ k * n) = (padicValNat p n + k, divMaxPow n p)
参数：hp : 1 < p；hn : n != 0；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.maxPowDvdDiv_of_pow_mul_eq`：maxPowDvdDiv_of_pow_mul_eq {p n k l : Na
t} (hn : n != 0) (h : p ^ k * l = n) (hl : ¬p ∣ l) : maxPowDvdDiv p n = (k, l)
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `Nat.ne_of_gt`：∀ {a b : ℕ}, b < a → a ≠ b
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_add`：∀ (a m n : ℕ), a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Nat.mul_assoc`：∀ (n m k : ℕ), n * m * k = n * (m * k)
· 使用定理 `Nat.mul_left_comm`：∀ (n m k : ℕ), n * (m * k) = m * (n * k)
· 使用定理 `Nat.pow_padicValNat_mul_divMaxPow`：pow_padicValNat_mul_divMaxPow (p n : 
Nat) : p ^ padicValNat p n * divMaxPow n p = n
· 使用定理 `Nat.not_dvd_divMaxPow`：not_dvd_divMaxPow {p n : Nat} (hp : 1 < p) (hn : 
n != 0) : ¬p ∣ divMaxPow n p
-/
theorem maxPowDvdDiv_base_pow_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) (k : ℕ) :
    p.maxPowDvdDiv (p ^ k * n) = (padicValNat p n + k, divMaxPow n p) := by
  apply maxPowDvdDiv_of_pow_mul_eq
  · exact Nat.mul_ne_zero (Nat.ne_of_gt <| Nat.pow_pos <| Nat.zero_lt_of_lt hp) hn
  · rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, pow_padicValNat_mul_divMaxPow]
  · exact not_dvd_divMaxPow hp hn

@[simp]
/-
**Nat._root_.padicValNat_base_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.padicValNat_base_pow_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) (k : ℕ) :
    padicValNat p (p ^ k * n) = padicValNat p n + k := by
  simp [padicValNat, *]

@[simp]
/-
**Nat.divMaxPow_base_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divMaxPow_base_pow_mul {p : Nat} (hp : p != 0) (n k : Nat) : (p ^ k * n).d
ivMaxPow p = n.divMaxPow p
参数：hp : p != 0；n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.one_pow`：∀ (n : ℕ), 1 ^ n = 1
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.divMaxPow_one_right`：divMaxPow_one_right (n : Nat) : divMaxPow n 1 =
 n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Nat.maxPowDvdDiv_zero_right`：maxPowDvdDiv_zero_right (p : Nat) : maxPowD
vdDiv p 0 = (0, 0)
· 使用定理 `Nat.maxPowDvdDiv_base_pow_mul`：maxPowDvdDiv_base_pow_mul {p n : Nat} (hp
 : 1 < p) (hn : n != 0) (k : Nat) : p.maxPowDvdDiv (p ^ k * n) = (padicValNat p 
n + k, divMaxPow n …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem divMaxPow_base_pow_mul {p : ℕ} (hp : p ≠ 0) (n k : ℕ) :
    (p ^ k * n).divMaxPow p = n.divMaxPow p := by
  obtain rfl | hp1 : p = 1 ∨ 1 < p := by grind
  · simp
  · rcases eq_or_ne n 0 with rfl | hn <;> simp [divMaxPow, *]

@[simp]
/-
**Nat.maxPowDvdDiv_base_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv_base_mul {p n : Nat} (hp : 1 < p) (hn : n != 0) : p.maxPowDvd
Div (p * n) = (padicValNat p n + 1, divMaxPow n p)
参数：hp : 1 < p；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
· 使用定理 `Nat.maxPowDvdDiv_base_pow_mul`：maxPowDvdDiv_base_pow_mul {p n : Nat} (hp
 : 1 < p) (hn : n != 0) (k : Nat) : p.maxPowDvdDiv (p ^ k * n) = (padicValNat p 
n + k, divMaxPow n …
-/
theorem maxPowDvdDiv_base_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    p.maxPowDvdDiv (p * n) = (padicValNat p n + 1, divMaxPow n p) := by
  simpa using maxPowDvdDiv_base_pow_mul hp hn 1

@[simp]
/-
**Nat._root_.padicValNat_base_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.padicValNat_base_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    padicValNat p (p * n) = padicValNat p n + 1 := by
  simp [padicValNat, *]

@[simp]
/-
**Nat.divMaxPow_base_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divMaxPow_base_mul {p : Nat} (hp : p != 0) (n : Nat) : (p * n).divMaxPow p
 = n.divMaxPow p
参数：hp : p != 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
· 使用定理 `Nat.divMaxPow_base_pow_mul`：divMaxPow_base_pow_mul {p : Nat} (hp : p != 
0) (n k : Nat) : (p ^ k * n).divMaxPow p = n.divMaxPow p
-/
theorem divMaxPow_base_mul {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    (p * n).divMaxPow p = n.divMaxPow p := by
  simpa using divMaxPow_base_pow_mul hp n 1

@[simp]
/-
**Nat.maxPowDvdDiv_base_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv_base_pow {p : Nat} (hp : 1 < p) (k : Nat) : p.maxPowDvdDiv (p
 ^ k) = (k, 1)
参数：hp : 1 < p；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `padicValNat_one_right`：∀ (p : ℕ), padicValNat p 1 = 0
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.divMaxPow_one_left`：divMaxPow_one_left (p : Nat) : divMaxPow 1 p = 1
· 使用定理 `Nat.maxPowDvdDiv_base_pow_mul`：maxPowDvdDiv_base_pow_mul {p n : Nat} (hp
 : 1 < p) (hn : n != 0) (k : Nat) : p.maxPowDvdDiv (p ^ k * n) = (padicValNat p 
n + k, divMaxPow n …
· 使用定理 `Nat.one_ne_zero`：1 ≠ 0
-/
theorem maxPowDvdDiv_base_pow {p : ℕ} (hp : 1 < p) (k : ℕ) : p.maxPowDvdDiv (p ^ k) = (k, 1) := by
  simpa using maxPowDvdDiv_base_pow_mul hp Nat.one_ne_zero k

@[simp]
/-
**Nat._root_.padicValNat_base_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.padicValNat_base_pow {p : ℕ} (hp : 1 < p) (k : ℕ) : padicValNat p (p ^ k) = k := by
  simp [padicValNat, hp]

@[simp]
/-
**Nat.divMaxPow_base_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divMaxPow_base_pow {p : Nat} (hp : p != 0) (k : Nat) : (p ^ k).divMaxPow p
 = 1
参数：hp : p != 0；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `Nat.divMaxPow_one_left`：divMaxPow_one_left (p : Nat) : divMaxPow 1 p = 1
· 使用定理 `Nat.divMaxPow_base_pow_mul`：divMaxPow_base_pow_mul {p : Nat} (hp : p != 
0) (n k : Nat) : (p ^ k * n).divMaxPow p = n.divMaxPow p
-/
theorem divMaxPow_base_pow {p : ℕ} (hp : p ≠ 0) (k : ℕ) : (p ^ k).divMaxPow p = 1 := by
  simpa using divMaxPow_base_pow_mul hp 1 k

@[simp]
/-
**Nat.maxPowDvdDiv_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：maxPowDvdDiv_self {p : Nat} (hp : 1 < p) : p.maxPowDvdDiv p = (1, 1)
参数：hp : 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
· 使用定理 `Nat.maxPowDvdDiv_base_pow`：maxPowDvdDiv_base_pow {p : Nat} (hp : 1 < p) 
(k : Nat) : p.maxPowDvdDiv (p ^ k) = (k, 1)
-/
theorem maxPowDvdDiv_self {p : ℕ} (hp : 1 < p) : p.maxPowDvdDiv p = (1, 1) := by
  simpa using maxPowDvdDiv_base_pow hp 1

@[simp]
/-
**Nat._root_.padicValNat_base** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.padicValNat_base {p : ℕ} (hp : 1 < p) : padicValNat p p = 1 := by
  simpa using padicValNat_base_pow hp 1

@[simp]
/-
**Nat.divMaxPow_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divMaxPow_self {p : Nat} (hp : p != 0) : p.divMaxPow p = 1
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
· 使用定理 `Nat.divMaxPow_base_pow`：divMaxPow_base_pow {p : Nat} (hp : p != 0) (k : 
Nat) : (p ^ k).divMaxPow p = 1
-/
theorem divMaxPow_self {p : ℕ} (hp : p ≠ 0) : p.divMaxPow p = 1 := by
  simpa using divMaxPow_base_pow hp 1

@[simp]
/-
**Nat.fst_maxPowDvdDiv** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：fst_maxPowDvdDiv (p n : Nat) : (p.maxPowDvdDiv n).1 = padicValNat p n
参数：p n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_maxPowDvdDiv (p n : ℕ) : (p.maxPowDvdDiv n).1 = padicValNat p n := rfl

@[simp]
/-
**Nat.snd_maxPowDvdDiv** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：snd_maxPowDvdDiv (p n : Nat) : (p.maxPowDvdDiv n).2 = n.divMaxPow p
参数：p n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_maxPowDvdDiv (p n : ℕ) : (p.maxPowDvdDiv n).2 = n.divMaxPow p := rfl

@[deprecated (since := "2026-03-15")]
alias maxPowDiv := padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_mul_eq_succ := padicValNat_base_mul

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_pow_mul := padicValNat_base_pow_mul

@[deprecated (since := "2026-03-15")]
alias ⟨_, maxPowDiv.le_of_dvd⟩ := pow_dvd_iff_le_padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.pow_dvd := pow_padicValNat_dvd

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.zero := padicValNat_zero_right

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.zero_base := padicValNat_zero_left

end Nat

