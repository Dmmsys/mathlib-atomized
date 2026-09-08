/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic.Attr.Register

/-!
# `IsSquare` and `Even` for natural numbers
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

namespace Nat

/-! #### Parity -/

variable {m n : ℕ}

@[grind =]
/-
**Nat.even_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：even_iff : Even n ↔ n % 2 = 0 where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma even_iff : Even n ↔ n % 2 = 0 where
  mp := fun ⟨m, hm⟩ ↦ by simp [← Nat.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidablePred (Even : ℕ → Prop) := fun _ ↦ decidable_of_iff _ even_iff.symm

/-- `IsSquare` can be decided on `ℕ` by checking against the square root. -/
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSquare` can be decided on `ℕ` by checking against the square root.
-/
instance : DecidablePred (IsSquare : ℕ → Prop) :=
  fun m ↦ decidable_of_iff' (Nat.sqrt m * Nat.sqrt m = m) <| by
    simp_rw [← Nat.exists_mul_self m, IsSquare, eq_comm]
/-
**Nat.not_even_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：not_even_iff : ¬ Even n ↔ n % 2 = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_even_iff : ¬ Even n ↔ n % 2 = 1 := by grind
/-
**Nat.two_dvd_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, ¬2 ∣ n ↔ n % 2 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 := by grind
/-
**Nat.not_even_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：¬Even 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma not_even_one : ¬Even 1 := by grind
/-
**Nat.even_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, Even (m + n) ↔ (Even m ↔ Even n)
参数：m + n；Even m ↔ Even n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps, grind =] lemma even_add : Even (m + n) ↔ (Even m ↔ Even n) := by grind
/-
**Nat.even_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, Even (n + 1) ↔ ¬Even n
参数：n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps] lemma even_add_one : Even (n + 1) ↔ ¬Even n := by grind
/-
**Nat.succ_mod_two_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：succ_mod_two_eq_zero_iff : (m + 1) % 2 = 0 ↔ m % 2 = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma succ_mod_two_eq_zero_iff : (m + 1) % 2 = 0 ↔ m % 2 = 1 := by lia
/-
**Nat.succ_mod_two_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：succ_mod_two_eq_one_iff : (m + 1) % 2 = 1 ↔ m % 2 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma succ_mod_two_eq_one_iff : (m + 1) % 2 = 1 ↔ m % 2 = 0 := by lia
/-
**Nat.two_not_dvd_two_mul_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_not_dvd_two_mul_add_one (n : Nat) : ¬2 ∣ 2 * n + 1
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma two_not_dvd_two_mul_add_one (n : ℕ) : ¬2 ∣ 2 * n + 1 := by lia
/-
**Nat.two_not_dvd_two_mul_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_not_dvd_two_mul_sub_one {n} : 0 < n -> ¬2 ∣ 2 * n - 1
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma two_not_dvd_two_mul_sub_one {n} : 0 < n → ¬2 ∣ 2 * n - 1 := by lia
/-
**Nat.even_sub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, n ≤ m → (Even (m - n) ↔ (Even m ↔ Even n))
参数：Even (m - n) ↔ (Even m ↔ Even n)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[parity_simps] lemma even_sub (h : n ≤ m) : Even (m - n) ↔ (Even m ↔ Even n) := by grind
/-
**Nat.even_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, Even (m * n) ↔ Even m ∨ Even n
参数：m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_two_eq_zero_or_one`：∀ (n : ℕ), n % 2 = 0 ∨ n % 2 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mul_mod`：∀ (a b n : ℕ), a * b % n = a % n * (b % n) % n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
-/
@[parity_simps, grind =] lemma even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  rcases mod_two_eq_zero_or_one m with h₁ | h₁ <;> rcases mod_two_eq_zero_or_one n with h₂ | h₂ <;>
    simp [even_iff, h₁, h₂, Nat.mul_mod]

/-- If `m` and `n` are natural numbers, then the natural number `m^n` is even
if and only if `m` is even and `n` is positive. -/
/-
**Nat.even_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, Even (m ^ n) ↔ Even m ∧ n ≠ 0
参数：m ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `m` and `n` are natural numbers, then the natural number `m^n` is even
if and only if `m` is even and `n` is positive.
-/
@[parity_simps, grind =] lemma even_pow : Even (m ^ n) ↔ Even m ∧ n ≠ 0 := by
  induction n with grind
/-
**Nat.even_pow'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：even_pow' (h : n != 0) : Even (m ^ n) ↔ Even m
参数：h : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_pow' (h : n ≠ 0) : Even (m ^ n) ↔ Even m := by grind
/-
**Nat.even_mul_succ_self** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：even_mul_succ_self (n : Nat) : Even (n * (n + 1))
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_mul_succ_self (n : ℕ) : Even (n * (n + 1)) := by grind
/-
**Nat.even_mul_pred_self** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：even_mul_pred_self (n : Nat) : Even (n * (n - 1))
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma even_mul_pred_self (n : ℕ) : Even (n * (n - 1)) := by grind
/-
**Nat.two_mul_div_two_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_mul_div_two_of_even : Even n -> 2 * (n / 2) = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_div_cancel_left'`：∀ {a b : ℕ}, a ∣ b → a * (b / a) = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `even_iff_exists_two_nsmul`：∀ {α : Type u_2} [inst : AddMonoid α] (a : α)
, Even a ↔ ∃ r, a = 2 • r
-/
lemma two_mul_div_two_of_even : Even n → 2 * (n / 2) = n := fun h ↦
  Nat.mul_div_cancel_left' ((even_iff_exists_two_nsmul _).1 h)
/-
**Nat.div_two_mul_two_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：div_two_mul_two_of_even : Even n -> n / 2 * 2 = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `even_iff_exists_two_nsmul`：∀ {α : Type u_2} [inst : AddMonoid α] (a : α)
, Even a ↔ ∃ r, a = 2 • r
-/
lemma div_two_mul_two_of_even : Even n → n / 2 * 2 = n :=
  fun h ↦ Nat.div_mul_cancel ((even_iff_exists_two_nsmul _).1 h)
/-
**Nat.one_lt_of_ne_zero_of_even** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：one_lt_of_ne_zero_of_even (h0 : n != 0) (hn : Even n) : 1 < n
参数：h0 : n != 0；hn : Even n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_lt_of_ne_zero_of_even (h0 : n ≠ 0) (hn : Even n) : 1 < n := by grind
/-
**Nat.add_one_lt_of_even** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_one_lt_of_even (hn : Even n) (hm : Even m) (hnm : n < m) : n + 1 < m
参数：hn : Even n；hm : Even m；hnm : n < m。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_one_lt_of_even (hn : Even n) (hm : Even m) (hnm : n < m) :
    n + 1 < m := by grind

-- Here are examples of how `parity_simps` can be used with `Nat`.
/-
**Nat.** 是 Mathlib 中的一个示例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (m n : ℕ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by simp [*, parity_simps]
/-
**Nat.** 是 Mathlib 中的一个示例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : ¬Even 25394535 := by decide

end Nat

