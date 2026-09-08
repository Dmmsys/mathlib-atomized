/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Stuart Presnell, Antoine Chambert-Loir,
  María-Inés de Frutos—Fernández
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Binomial coefficients

This file defines binomial coefficients and proves simple lemmas (i.e. those not
requiring more imports).
For the lemma that `n.choose k` counts the `k`-element-subsets of an `n`-element set,
see `Finset.card_powersetCard` in `Mathlib/Data/Finset/Powerset.lean`.

## Main definition and results

* `Nat.choose`: binomial coefficients, defined inductively
* `Nat.choose_eq_factorial_div_factorial`: a proof that `choose n k = n! / (k! * (n - k)!)`
* `Nat.choose_symm`: symmetry of binomial coefficients
* `Nat.choose_le_succ_of_lt_half_left`: `choose n k` is increasing for small values of `k`
* `Nat.choose_le_middle`: `choose n r` is maximised when `r` is `n/2`
* `Nat.descFactorial_eq_factorial_mul_choose`: Relates binomial coefficients to the descending
  factorial. This is used to prove `Nat.choose_le_pow` and variants. We provide similar statements
  for the ascending factorial.
* `Nat.multichoose`: whereas `choose` counts combinations, `multichoose` counts multicombinations.
  The fact that this is indeed the correct counting function for multisets is proved in
  `Sym.card_sym_eq_multichoose` in `Data.Sym.Card`.
* `Nat.multichoose_eq` : a proof that `multichoose n k = (n + k - 1).choose k`.
  This is central to the "stars and bars" technique in informal mathematics, where we switch between
  counting multisets of size `k` over an alphabet of size `n` to counting strings of `k` elements
  ("stars") separated by `n-1` dividers ("bars").  See `Data.Sym.Card` for more detail.

## Tags

binomial coefficient, combination, multicombination, stars and bars
-/

@[expose] public section

namespace Nat

/-- `choose n k` is the number of `k`-element subsets in an `n`-element set. Also known as binomial
coefficients. For the fact that this is the number of `k`-element-subsets of an `n`-element
set, see `Finset.card_powersetCard`. -/
/-
**Nat.choose** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`choose n k` is the number of `k`-element subsets in an `n`-element set. Also kn
own as binomial
coefficients. For the fact that this is the number of `k`-element-subsets of an 
`n`-element
set, see `Finset.card_powersetCard`.
-/
def choose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

@[simp, grind =]
/-
**Nat.choose_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_zero_right (n : Nat) : choose n 0 = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem choose_zero_right (n : ℕ) : choose n 0 = 1 := by cases n <;> rfl

@[simp, grind =]
/-
**Nat.choose_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_zero_succ (k : Nat) : choose 0 (succ k) = 0
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem choose_zero_succ (k : ℕ) : choose 0 (succ k) = 0 :=
  rfl

@[grind =]
/-
**Nat.choose_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_succ_succ (n k : Nat) : choose (succ n) (succ k) = choose n k + cho
ose n (succ k)
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem choose_succ_succ (n k : ℕ) : choose (succ n) (succ k) = choose n k + choose n (succ k) :=
  rfl
/-
**Nat.choose_succ_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_succ_succ' (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choo
se n (k + 1)
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem choose_succ_succ' (n k : ℕ) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) :=
  rfl
/-
**Nat.choose_succ_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_succ_left (n k : Nat) (hk : 0 < k) : choose (n + 1) k = choose n (k
 - 1) + choose n k
参数：n k : Nat；hk : 0 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem choose_succ_left (n k : ℕ) (hk : 0 < k) :
    choose (n + 1) k = choose n (k - 1) + choose n k := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl
/-
**Nat.choose_succ_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_succ_right (n k : Nat) (hn : 0 < n) : choose n (k + 1) = choose (n 
- 1) k + choose (n - 1) (k + 1)
参数：n k : Nat；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem choose_succ_right (n k : ℕ) (hn : 0 < n) :
    choose n (k + 1) = choose (n - 1) k + choose (n - 1) (k + 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, n = l + 1 := Nat.exists_eq_add_of_le' hn
  rfl
/-
**Nat.choose_eq_choose_pred_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_eq_choose_pred_add {n k : Nat} (hn : 0 < n) (hk : 0 < k) : choose n
 k = choose (n - 1) (k - 1) + choose (n - 1) k
参数：hn : 0 < n；hk : 0 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_succ_right`：choose_succ_right (n k : Nat) (hn : 0 < n) : choo
se n (k + 1) = choose (n - 1) k + choose (n - 1) (k + 1)
· 使用定理 `Nat.add_one_sub_one`：∀ (n : ℕ), n + 1 - 1 = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem choose_eq_choose_pred_add {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    choose n k = choose (n - 1) (k - 1) + choose (n - 1) k := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rw [choose_succ_right _ _ hn, Nat.add_one_sub_one]

@[grind <=]
/-
**Nat.choose_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_eq_zero_of_lt : forall {n k}, n < k -> choose n k = 0 | _, 0, hk =>
 absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choose_zero_succ _ | n + 1, k + 
1, hk => by have hnk : n < k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem choose_eq_zero_of_lt : ∀ {n k}, n < k → choose n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => choose_zero_succ _
  | n + 1, k + 1, hk => by
    have hnk : n < k := lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := lt_of_succ_lt hk
    rw [choose_succ_succ, choose_eq_zero_of_lt hnk, choose_eq_zero_of_lt hnk1]

@[simp]
/-
**Nat.choose_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_self (n : Nat) : choose n n = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem choose_self (n : ℕ) : choose n n = 1 := by
  induction n <;> grind

@[simp]
/-
**Nat.choose_succ_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_succ_self (n : Nat) : choose n (succ n) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem choose_succ_self (n : ℕ) : choose n (succ n) = 0 :=
  choose_eq_zero_of_lt (lt_succ_self _)

@[simp]
/-
**Nat.choose_one_right** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：choose_one_right (n : Nat) : choose n 1 = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
-/
lemma choose_one_right (n : ℕ) : choose n 1 = n := by induction n <;> simp [*, choose, Nat.add_comm]

-- The `n + 1`-st triangle number is `n` more than the `n`-th triangle number
/-
**Nat.triangle_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：triangle_succ (n : Nat) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_mul_div_left`：∀ (x z : ℕ) {y : ℕ}, 0 < y → (x + y * z) / y = x /
 y + z
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.mul_add`：∀ (n m k : ℕ), n * (m + k) = n * m + n * k
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
-/
theorem triangle_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  rw [← add_mul_div_left, Nat.mul_comm 2 n, ← Nat.mul_add, Nat.add_sub_cancel, Nat.mul_comm]
  cases n <;> rfl; apply zero_lt_succ

/-- `choose n 2` is the `n`-th triangle number. -/
/-
**Nat.choose_two_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_two_right (n : Nat) : choose n 2 = n * (n - 1) / 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.triangle_succ`：triangle_succ (n : Nat) : (n + 1) * (n + 1 - 1) / 2 =
 n * (n - 1) / 2 + n
· 使用定理 `Nat.choose.eq_3`：∀ (n k : ℕ), n.succ.choose k.succ = n.choose k + n.choo
se (k + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n

--- 原说明 ---
`choose n 2` is the `n`-th triangle number.
-/
theorem choose_two_right (n : ℕ) : choose n 2 = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [triangle_succ n, choose, ih]
    simp [Nat.add_comm]
/-
**Nat.choose_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem choose_pos : ∀ {n k}, k ≤ n → 0 < choose n k
  | 0, _, hk => by rw [Nat.eq_zero_of_le_zero hk]; decide
  | n + 1, 0, _ => by simp
  | _ + 1, _ + 1, hk => Nat.add_pos_left (choose_pos (le_of_succ_le_succ hk)) _
/-
**Nat.choose_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_eq_zero_iff {n k : Nat} : n.choose k = 0 ↔ n < k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
-/
theorem choose_eq_zero_iff {n k : ℕ} : n.choose k = 0 ↔ n < k :=
  ⟨fun h => lt_of_not_ge (mt Nat.choose_pos h.symm.not_lt), Nat.choose_eq_zero_of_lt⟩
/-
**Nat.choose_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_ne_zero_iff {n k : Nat} : n.choose k != 0 ↔ k <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem choose_ne_zero_iff {n k : ℕ} : n.choose k ≠ 0 ↔ k ≤ n :=
  not_iff_not.1 <| by simp [choose_eq_zero_iff]
/-
**Nat.choose_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：choose_ne_zero {n k : Nat} (h : k <= n) : n.choose k != 0
参数：h : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
-/
lemma choose_ne_zero {n k : ℕ} (h : k ≤ n) : n.choose k ≠ 0 :=
  (choose_pos h).ne'
/-
**Nat.add_one_mul_choose_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1)
参数：n k : ℕ；n + 1；n + 1；k + 1；k + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_one_mul_choose_eq : ∀ n k, (n + 1) * choose n k = choose (n + 1) (k + 1) * (k + 1)
  | 0, 0 => by decide
  | 0, k + 1 => by simp [choose]
  | n + 1, 0 => by simp [choose, mul_succ, Nat.add_comm]
  | n + 1, k + 1 => by
    rw [choose_succ_succ' (n + 1) (k + 1), Nat.add_mul _ _ (k + 1 + 1), ← add_one_mul_choose_eq n,
      mul_add_one, ← add_one_mul_choose_eq n, Nat.add_right_comm _ _ (_ * _), ← Nat.mul_add,
      ← choose_succ_succ', ← add_one_mul]
/-
**Nat.choose_mul_factorial_mul_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_mul_factorial_mul_factorial : forall {n k}, k <= n -> choose n k * 
k ! * (n - k)! = n ! | 0, _, hk => by simp [Nat.eq_zero_of_le_zero hk] | n + 1, 
0, _ => by simp | n + 1, succ k, hk => by rcases lt_or_eq_of_le hk with hk₁ | hk
₁ · have h : choose n k * k.succ ! * (n - k)! = (k + 1) * n !
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem choose_mul_factorial_mul_factorial : ∀ {n k}, k ≤ n → choose n k * k ! * (n - k)! = n !
  | 0, _, hk => by simp [Nat.eq_zero_of_le_zero hk]
  | n + 1, 0, _ => by simp
  | n + 1, succ k, hk => by
    rcases lt_or_eq_of_le hk with hk₁ | hk₁
    · have h : choose n k * k.succ ! * (n - k)! = (k + 1) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_succ_le_succ hk)]
        simp [factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h₁ : (n - k)! = (n - k) * (n - k.succ)! := by
        rw [← succ_sub_succ, succ_sub (le_of_lt_succ hk₁), factorial_succ]
      have h₂ : choose n (succ k) * k.succ ! * ((n - k) * (n - k.succ)!) = (n - k) * n ! := by
        rw [← choose_mul_factorial_mul_factorial (le_of_lt_succ hk₁)]
        simp [factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have h₃ : k * n ! ≤ n * n ! := Nat.mul_le_mul_right _ (le_of_succ_le_succ hk)
      rw [choose_succ_succ, Nat.add_mul, Nat.add_mul, succ_sub_succ, h, h₁, h₂, Nat.add_mul,
        Nat.mul_sub_right_distrib, factorial_succ, ← Nat.add_sub_assoc h₃, Nat.add_assoc,
        ← Nat.add_mul, Nat.add_sub_cancel_left, Nat.add_comm]
    · rw [hk₁]; simp [Nat.mul_comm, choose, Nat.sub_self]
/-
**Nat.choose_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_mul {n k s : Nat} (hsk : s <= k) : n.choose k * k.choose s = n.choo
se s * (n - s).choose (k - s)
参数：hsk : s <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Nat.mul_right_cancel`：∀ {n m k : ℕ}, 0 < m → n * m = k * m → n = k
-/
theorem choose_mul {n k s : ℕ} (hsk : s ≤ k) :
    n.choose k * k.choose s = n.choose s * (n - s).choose (k - s) := by
  obtain hnk | hkn := lt_or_ge n k
  · grind
  have h : 0 < (n - k)! * (k - s)! * s ! := by apply_rules [factorial_pos, Nat.mul_pos]
  apply Nat.mul_right_cancel h
  calc
    _ = n.choose s * s ! * ((n - s).choose (k - s) * (k - s)! * (n - s - (k - s))!) := by
      grind [choose_mul_factorial_mul_factorial]
    _ = n.choose s * (n - s).choose (k - s) * ((n - k)! * (k - s)! * s !) := by
      grind
/-
**Nat.choose_eq_factorial_div_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_eq_factorial_div_factorial {n k : Nat} (hk : k <= n) : choose n k =
 n ! / (k ! * (n - k)!)
参数：hk : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.choose_mul_factorial_mul_factorial`：choose_mul_factorial_mul_factori
al : forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n ! | 0, _, hk => by 
simp [Nat.eq_zero_of_le_zero…
· 使用定理 `Nat.mul_assoc`：∀ (n m k : ℕ), n * m * k = n * (m * k)
· 使用定理 `Nat.mul_div_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
-/
theorem choose_eq_factorial_div_factorial {n k : ℕ} (hk : k ≤ n) :
    choose n k = n ! / (k ! * (n - k)!) := by
  rw [← choose_mul_factorial_mul_factorial hk, Nat.mul_assoc]
  exact (mul_div_left _ (Nat.mul_pos (factorial_pos _) (factorial_pos _))).symm
/-
**Nat.add_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_choose (i j : Nat) : (i + j).choose j = (i + j)! / (i ! * j !)
参数：i j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_factorial_div_factorial`：choose_eq_factorial_div_factorial
 {n k : Nat} (hk : k <= n) : choose n k = n ! / (k ! * (n - k)!)
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
-/
theorem add_choose (i j : ℕ) : (i + j).choose j = (i + j)! / (i ! * j !) := by
  rw [choose_eq_factorial_div_factorial (Nat.le_add_left j i), Nat.add_sub_cancel_right,
    Nat.mul_comm]
/-
**Nat.add_choose_mul_factorial_mul_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_choose_mul_factorial_mul_factorial (i j : Nat) : (i + j).choose j * i 
! * j ! = (i + j)!
参数：i j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.choose_mul_factorial_mul_factorial`：choose_mul_factorial_mul_factori
al : forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n ! | 0, _, hk => by 
simp [Nat.eq_zero_of_le_zero…
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Nat.mul_right_comm`：∀ (n m k : ℕ), n * m * k = n * k * m
-/
theorem add_choose_mul_factorial_mul_factorial (i j : ℕ) :
    (i + j).choose j * i ! * j ! = (i + j)! := by
  rw [← choose_mul_factorial_mul_factorial (Nat.le_add_left _ _), Nat.add_sub_cancel_right,
    Nat.mul_right_comm]
/-
**Nat.factorial_mul_factorial_dvd_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_mul_factorial_dvd_factorial {n k : Nat} (hk : k <= n) : k ! * (n
 - k)! ∣ n !
参数：hk : k <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.choose_mul_factorial_mul_factorial`：choose_mul_factorial_mul_factori
al : forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n ! | 0, _, hk => by 
simp [Nat.eq_zero_of_le_zero…
· 使用定理 `Nat.mul_assoc`：∀ (n m k : ℕ), n * m * k = n * (m * k)
· 使用定理 `Nat.dvd_mul_left`：∀ (a b : ℕ), a ∣ b * a
-/
theorem factorial_mul_factorial_dvd_factorial {n k : ℕ} (hk : k ≤ n) : k ! * (n - k)! ∣ n ! := by
  rw [← choose_mul_factorial_mul_factorial hk, Nat.mul_assoc]; exact Nat.dvd_mul_left _ _
/-
**Nat.factorial_mul_factorial_dvd_factorial_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_mul_factorial_dvd_factorial_add (i j : Nat) : i ! * j ! ∣ (i + j
)!
参数：i j : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorial_mul_factorial_dvd_factorial`：factorial_mul_factorial_dvd_f
actorial {n k : Nat} (hk : k <= n) : k ! * (n - k)! ∣ n !
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
-/
theorem factorial_mul_factorial_dvd_factorial_add (i j : ℕ) : i ! * j ! ∣ (i + j)! := by
  suffices i ! * (i + j - i)! ∣ (i + j)! by
    rwa [Nat.add_sub_cancel_left i j] at this
  exact factorial_mul_factorial_dvd_factorial (Nat.le_add_right _ _)

@[simp]
/-
**Nat.choose_symm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_symm {n k : Nat} (hk : k <= n) : choose n (n - k) = choose n k
参数：hk : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_factorial_div_factorial`：choose_eq_factorial_div_factorial
 {n k : Nat} (hk : k <= n) : choose n k = n ! / (k ! * (n - k)!)
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `Nat.sub_sub_self`：∀ {n m : ℕ}, m ≤ n → n - (n - m) = m
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
-/
theorem choose_symm {n k : ℕ} (hk : k ≤ n) : choose n (n - k) = choose n k := by
  rw [choose_eq_factorial_div_factorial hk, choose_eq_factorial_div_factorial (Nat.sub_le _ _),
    Nat.sub_sub_self hk, Nat.mul_comm]
/-
**Nat.choose_symm_of_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_symm_of_eq_add {n a b : Nat} (h : n = a + b) : Nat.choose n a = Nat
.choose n b
参数：h : n = a + b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.choose_symm`：choose_symm {n k : Nat} (hk : k <= n) : choose n (n - k
) = choose n k
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
-/
theorem choose_symm_of_eq_add {n a b : ℕ} (h : n = a + b) : Nat.choose n a = Nat.choose n b := by
  suffices choose n (n - b) = choose n b by
    rw [h, Nat.add_sub_cancel_right] at this; rwa [h]
  exact choose_symm (h ▸ le_add_left _ _)
/-
**Nat.choose_symm_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_symm_add {a b : Nat} : choose (a + b) a = choose (a + b) b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.choose_symm_of_eq_add`：choose_symm_of_eq_add {n a b : Nat} (h : n = 
a + b) : Nat.choose n a = Nat.choose n b
-/
theorem choose_symm_add {a b : ℕ} : choose (a + b) a = choose (a + b) b :=
  choose_symm_of_eq_add rfl
/-
**Nat.choose_symm_half** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_symm_half (m : Nat) : choose (2 * m + 1) (m + 1) = choose (2 * m + 
1) m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.choose_symm_of_eq_add`：choose_symm_of_eq_add {n a b : Nat} (h : n = 
a + b) : Nat.choose n a = Nat.choose n b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Nat.two_mul`：∀ (n : ℕ), 2 * n = n + n
-/
theorem choose_symm_half (m : ℕ) : choose (2 * m + 1) (m + 1) = choose (2 * m + 1) m := by
  apply choose_symm_of_eq_add
  rw [Nat.add_comm m 1, Nat.add_assoc 1 m m, Nat.add_comm (2 * m) 1, Nat.two_mul m]
/-
**Nat.choose_succ_right_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_succ_right_eq (n k : Nat) : choose n (k + 1) * (k + 1) = choose n k
 * (n - k)
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_mul`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.choose_succ_succ`：choose_succ_succ (n k : Nat) : choose (succ n) (su
cc k) = choose n k + choose n (succ k)
· 使用定理 `Nat.add_one_mul_choose_eq`：∀ (n k : ℕ), (n + 1) * n.choose k = (n + 1).c
hoose (k + 1) * (k + 1)
· 使用定理 `Nat.sub_eq_of_eq_add`：∀ {a b c : ℕ}, a = c + b → a - b = c
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.mul_sub_left_distrib`：∀ (n m k : ℕ), n * (m - k) = n * m - n * k
· 使用定理 `Nat.add_sub_add_right`：∀ (n k m : ℕ), n + k - (m + k) = n - m
-/
theorem choose_succ_right_eq (n k : ℕ) : choose n (k + 1) * (k + 1) = choose n k * (n - k) := by
  have e : (n + 1) * choose n k = choose n (k + 1) * (k + 1) + choose n k * (k + 1) := by
    rw [← Nat.add_mul, Nat.add_comm (choose _ _), ← choose_succ_succ, add_one_mul_choose_eq]
  rw [← Nat.sub_eq_of_eq_add e, Nat.mul_comm, ← Nat.mul_sub_left_distrib, Nat.add_sub_add_right]

@[simp, grind =]
/-
**Nat.choose_succ_self_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (n + 1).choose n = n + 1
参数：n : ℕ；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem choose_succ_self_right : ∀ n : ℕ, (n + 1).choose n = n + 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_succ_self_right n, choose_self]
/-
**Nat.choose_mul_succ_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_mul_succ_eq (n k : Nat) : n.choose k * (n + 1) = (n + 1).choose k *
 (n + 1 - k)
参数：n k : Nat。
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
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Nat.choose_succ_succ`：choose_succ_succ (n k : Nat) : choose (succ n) (su
cc k) = choose n k + choose n (succ k)
· 使用定理 `Nat.add_mul`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
· 使用定理 `Nat.succ_sub_succ`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `Nat.choose_succ_right_eq`：choose_succ_right_eq (n k : Nat) : choose n (k
 + 1) * (k + 1) = choose n k * (n - k)
· 使用定理 `Nat.mul_sub_left_distrib`：∀ (n m k : ℕ), n * (m - k) = n * m - n * k
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
-/
theorem choose_mul_succ_eq (n k : ℕ) : n.choose k * (n + 1) = (n + 1).choose k * (n + 1 - k) := by
  cases k with
  | zero => simp
  | succ k =>
    obtain hk | hk := le_or_gt (k + 1) (n + 1)
    · rw [choose_succ_succ, Nat.add_mul, succ_sub_succ, ← choose_succ_right_eq, ← succ_sub_succ,
        Nat.mul_sub_left_distrib, Nat.add_sub_cancel' (Nat.mul_le_mul_left _ hk)]
    · rw [choose_eq_zero_of_lt hk, choose_eq_zero_of_lt (n.lt_succ_self.trans hk), Nat.zero_mul,
        Nat.zero_mul]
/-
**Nat.choose_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_mul_add {m n : Nat} (hn : n != 0) : (m * n + n).choose n = (m + 1) 
* (m * n + n - 1).choose (n - 1)
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_left_inj`：∀ {a b c : ℕ}, a ≠ 0 → (b * a = c * a ↔ b = c)
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Nat.succ_pred_eq_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → n.pred.succ = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.add_choose_mul_factorial_mul_factorial`：add_choose_mul_factorial_mul
_factorial (i j : Nat) : (i + j).choose j * i ! * j ! = (i + j)!
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
-/
theorem choose_mul_add {m n : ℕ} (hn : n ≠ 0) :
    (m * n + n).choose n = (m + 1) * (m * n + n - 1).choose (n - 1) := by
  rw [← Nat.mul_left_inj (Nat.mul_ne_zero (factorial_ne_zero (m * n)) (factorial_ne_zero n))]
  set p := n - 1
  have hp : n = p + 1 := (succ_pred_eq_of_ne_zero hn).symm
  simp only [hp, add_succ_sub_one]
  calc
    (m * (p + 1) + (p + 1)).choose (p + 1) * ((m * (p + 1))! * (p + 1)!)
      = (m * (p + 1) + (p + 1)).choose (p + 1) * (m * (p + 1))! * (p + 1)! := by lia
    _ = (m * (p + 1) + (p + 1))! := by rw [add_choose_mul_factorial_mul_factorial]
    _ = ((m * (p + 1) + p) + 1)! := by lia
    _ = ((m * (p + 1) + p) + 1) * (m * (p + 1) + p)! := by rw [factorial_succ]
    _ = (m * (p + 1) + p)! * ((p + 1) * (m + 1)) := by lia
    _ = ((m * (p + 1) + p).choose p * (m * (p + 1))! * (p)!) * ((p + 1) * (m + 1)) := by
      rw [add_choose_mul_factorial_mul_factorial]
    _ = (m * (p + 1) + p).choose p * (m * (p + 1))! * (((p + 1) * (p)!) * (m + 1)) := by lia
    _ = (m * (p + 1) + p).choose p * (m * (p + 1))! * ((p + 1)! * (m + 1)) := by rw [factorial_succ]
    _ = (m + 1) * (m * (p + 1) + p).choose p * ((m * (p + 1))! * (p + 1)!) := by lia
/-
**Nat.choose_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_mul_right {m n : Nat} (hn : n != 0) : (m * n).choose n = m * (m * n
 - 1).choose (n - 1)
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → n.pred.succ = n
· 使用定理 `Nat.add_mul`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.choose_mul_add`：choose_mul_add {m n : Nat} (hn : n != 0) : (m * n + 
n).choose n = (m + 1) * (m * n + n - 1).choose (n - 1)
-/
theorem choose_mul_right {m n : ℕ} (hn : n ≠ 0) :
    (m * n).choose n = m * (m * n - 1).choose (n - 1) := by
  by_cases hm : m = 0
  · simp only [hm, Nat.zero_mul, Nat.choose_eq_zero_iff]
    exact Nat.pos_of_ne_zero hn
  · set p := m - 1; have hp : m = p + 1 := (succ_pred_eq_of_ne_zero hm).symm
    simp only [hp]
    rw [Nat.add_mul, Nat.one_mul, choose_mul_add hn]
/-
**Nat.ascFactorial_eq_factorial_mul_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_eq_factorial_mul_choose (n k : Nat) : (n + 1).ascFactorial k 
= k ! * (n + k).choose k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.mul_right_cancel`：∀ {n m k : ℕ}, 0 < m → n * m = k * m → n = k
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Nat.choose_mul_factorial_mul_factorial`：choose_mul_factorial_mul_factori
al : forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n ! | 0, _, hk => by 
simp [Nat.eq_zero_of_le_zero…
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorial_mul_ascFactorial`：∀ (n k : ℕ), n.factorial * (n + 1).ascFa
ctorial k = (n + k).factorial
-/
theorem ascFactorial_eq_factorial_mul_choose (n k : ℕ) :
    (n + 1).ascFactorial k = k ! * (n + k).choose k := by
  rw [Nat.mul_comm]
  apply Nat.mul_right_cancel (n + k - k).factorial_pos
  rw [choose_mul_factorial_mul_factorial <| Nat.le_add_left k n, Nat.add_sub_cancel_right,
    ← factorial_mul_ascFactorial, Nat.mul_comm]
/-
**Nat.ascFactorial_eq_factorial_mul_choose'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_eq_factorial_mul_choose' (n k : Nat) : n.ascFactorial k = k !
 * (n + k - 1).choose k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ascFactorial_zero`：ascFactorial_zero (n : Nat) : n.ascFactorial 0 = 
1
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.factorial_zero`：Nat.factorial 0 = 1
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.zero_ascFactorial`：∀ (k : ℕ), Nat.ascFactorial 0 k.succ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `Nat.choose_succ_self`：choose_succ_self (n : Nat) : choose n (succ n) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.ascFactorial_eq_factorial_mul_choose`：ascFactorial_eq_factorial_mul_
choose (n k : Nat) : (n + 1).ascFactorial k = k ! * (n + k).choose k
· 使用定理 `Nat.succ_add_sub_one`：∀ (n m : ℕ), m.succ + n - 1 = m + n
-/
theorem ascFactorial_eq_factorial_mul_choose' (n k : ℕ) :
    n.ascFactorial k = k ! * (n + k - 1).choose k := by
  cases n
  · cases k
    · rw [ascFactorial_zero, choose_zero_right, factorial_zero, Nat.mul_one]
    · simp only [zero_ascFactorial, Nat.zero_add, succ_sub_succ_eq_sub,
        Nat.sub_zero, choose_succ_self, Nat.mul_zero]
  rw [ascFactorial_eq_factorial_mul_choose]
  simp only [succ_add_sub_one]
/-
**Nat.factorial_dvd_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_dvd_ascFactorial (n k : Nat) : k ! ∣ n.ascFactorial k
参数：n k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ascFactorial_eq_factorial_mul_choose'`：ascFactorial_eq_factorial_mul
_choose' (n k : Nat) : n.ascFactorial k = k ! * (n + k - 1).choose k
-/
theorem factorial_dvd_ascFactorial (n k : ℕ) : k ! ∣ n.ascFactorial k :=
  ⟨(n + k - 1).choose k, ascFactorial_eq_factorial_mul_choose' _ _⟩
/-
**Nat.choose_eq_asc_factorial_div_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_eq_asc_factorial_div_factorial (n k : Nat) : (n + k).choose k = (n 
+ 1).ascFactorial k / k !
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_left_cancel`：∀ {n m k : ℕ}, 0 < n → n * m = n * k → m = k
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ascFactorial_eq_factorial_mul_choose`：ascFactorial_eq_factorial_mul_
choose (n k : Nat) : (n + 1).ascFactorial k = k ! * (n + k).choose k
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Nat.factorial_dvd_ascFactorial`：factorial_dvd_ascFactorial (n k : Nat) :
 k ! ∣ n.ascFactorial k
-/
theorem choose_eq_asc_factorial_div_factorial (n k : ℕ) :
    (n + k).choose k = (n + 1).ascFactorial k / k ! := by
  apply Nat.mul_left_cancel k.factorial_pos
  rw [← ascFactorial_eq_factorial_mul_choose]
  exact (Nat.mul_div_cancel' <| factorial_dvd_ascFactorial _ _).symm
/-
**Nat.choose_eq_asc_factorial_div_factorial'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_eq_asc_factorial_div_factorial' (n k : Nat) : (n + k - 1).choose k 
= n.ascFactorial k / k !
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_div_of_mul_eq_right`：∀ {c a b : ℕ}, c ≠ 0 → c * a = b → a = b / c
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ascFactorial_eq_factorial_mul_choose'`：ascFactorial_eq_factorial_mul
_choose' (n k : Nat) : n.ascFactorial k = k ! * (n + k - 1).choose k
-/
theorem choose_eq_asc_factorial_div_factorial' (n k : ℕ) :
    (n + k - 1).choose k = n.ascFactorial k / k ! :=
  Nat.eq_div_of_mul_eq_right k.factorial_ne_zero (ascFactorial_eq_factorial_mul_choose' _ _).symm
/-
**Nat.descFactorial_eq_factorial_mul_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：descFactorial_eq_factorial_mul_choose (n k : Nat) : n.descFactorial k = k 
! * n.choose k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.descFactorial_eq_zero_iff_lt`：∀ {n k : ℕ}, n.descFactorial k = 0 ↔ n
 < k
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Nat.mul_zero`：∀ (n : ℕ), n * 0 = 0
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.mul_right_cancel`：∀ {n m k : ℕ}, 0 < m → n * m = k * m → n = k
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Nat.choose_mul_factorial_mul_factorial`：choose_mul_factorial_mul_factori
al : forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n ! | 0, _, hk => by 
simp [Nat.eq_zero_of_le_zero…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorial_mul_descFactorial`：∀ {n k : ℕ}, k ≤ n → (n - k).factorial 
* n.descFactorial k = n.factorial
-/
theorem descFactorial_eq_factorial_mul_choose (n k : ℕ) : n.descFactorial k = k ! * n.choose k := by
  obtain h | h := Nat.lt_or_ge n k
  · rw [descFactorial_eq_zero_iff_lt.2 h, choose_eq_zero_of_lt h, Nat.mul_zero]
  rw [Nat.mul_comm]
  apply Nat.mul_right_cancel (n - k).factorial_pos
  rw [choose_mul_factorial_mul_factorial h, ← factorial_mul_descFactorial h, Nat.mul_comm]
/-
**Nat.factorial_dvd_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_dvd_descFactorial (n k : Nat) : k ! ∣ n.descFactorial k
参数：n k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.descFactorial_eq_factorial_mul_choose`：descFactorial_eq_factorial_mu
l_choose (n k : Nat) : n.descFactorial k = k ! * n.choose k
-/
theorem factorial_dvd_descFactorial (n k : ℕ) : k ! ∣ n.descFactorial k :=
  ⟨n.choose k, descFactorial_eq_factorial_mul_choose _ _⟩
/-
**Nat.choose_eq_descFactorial_div_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_eq_descFactorial_div_factorial (n k : Nat) : n.choose k = n.descFac
torial k / k !
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_div_of_mul_eq_right`：∀ {c a b : ℕ}, c ≠ 0 → c * a = b → a = b / c
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.descFactorial_eq_factorial_mul_choose`：descFactorial_eq_factorial_mu
l_choose (n k : Nat) : n.descFactorial k = k ! * n.choose k
-/
theorem choose_eq_descFactorial_div_factorial (n k : ℕ) : n.choose k = n.descFactorial k / k ! :=
  Nat.eq_div_of_mul_eq_right k.factorial_ne_zero (descFactorial_eq_factorial_mul_choose _ _).symm

/-- A faster implementation of `choose`, to be used during bytecode evaluation
and in compiled code. -/
/-
**Nat.fast_choose** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：fast_choose n k
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A faster implementation of `choose`, to be used during bytecode evaluation
and in compiled code.
-/
def fast_choose n k := Nat.descFactorial n k / Nat.factorial k
/-
**Nat.choose_eq_fast_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.choose = Nat.fast_choose
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.choose_eq_descFactorial_div_factorial`：choose_eq_descFactorial_div_f
actorial (n k : Nat) : n.choose k = n.descFactorial k / k !
-/
@[csimp] lemma choose_eq_fast_choose : Nat.choose = fast_choose :=
  funext (fun _ => funext (Nat.choose_eq_descFactorial_div_factorial _))


/-! ### Inequalities -/


/-- Show that `Nat.choose` is increasing for small values of the right argument. -/
/-
**Nat.choose_le_succ_of_lt_half_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_le_succ_of_lt_half_left {r n : Nat} (h : r < n / 2) : choose n r <=
 choose n (r + 1)
参数：h : r < n / 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_mul_le_mul_right`：∀ {a b c : ℕ}, a * c ≤ b * c → 0 < c → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.choose_succ_right_eq`：choose_succ_right_eq (n k : Nat) : choose n (k
 + 1) * (k + 1) = choose n k * (n - k)
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Nat.lt_iff_add_one_le`：∀ {m n : ℕ}, m < n ↔ m + 1 ≤ n
· 使用定理 `Nat.lt_sub_iff_add_lt`：∀ {a b c : ℕ}, a < c - b ↔ a + b < c
· 使用定理 `Nat.mul_two`：∀ (n : ℕ), n * 2 = n + n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.mul_lt_mul_of_pos_right`：∀ {n m k : ℕ}, n < m → k > 0 → n * k < m * 
k
· 使用定理 `Nat.zero_lt_two`：0 < 2
· 使用定理 `Nat.div_mul_le_self`：∀ (m n : ℕ), m / n * n ≤ m
· 使用定理 `Nat.sub_pos_of_lt`：∀ {m n : ℕ}, m < n → 0 < n - m
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.div_le_self`：∀ (n k : ℕ), n / k ≤ n

--- 原说明 ---
Show that `Nat.choose` is increasing for small values of the right argument.
-/
theorem choose_le_succ_of_lt_half_left {r n : ℕ} (h : r < n / 2) :
    choose n r ≤ choose n (r + 1) := by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.sub_pos_of_lt (h.trans_le (n.div_le_self 2)))
  rw [← choose_succ_right_eq]
  apply Nat.mul_le_mul_left
  rw [← Nat.lt_iff_add_one_le, Nat.lt_sub_iff_add_lt, ← Nat.mul_two]
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h Nat.zero_lt_two) (n.div_mul_le_self 2)

/-- Show that for small values of the right argument, the middle value is largest. -/
/-
**Nat.choose_le_middle_of_le_half_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Show that for small values of the right argument, the middle value is largest.
-/
private theorem choose_le_middle_of_le_half_left {n r : ℕ} (hr : r ≤ n / 2) :
    choose n r ≤ choose n (n / 2) := by
  induction hr using decreasingInduction with
  | self => rfl
  | of_succ k hk ih => exact (choose_le_succ_of_lt_half_left hk).trans ih

/-- `choose n r` is maximised when `r` is `n/2`. -/
/-
**Nat.choose_le_middle** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_le_middle (r n : Nat) : choose n r <= choose n (n / 2)
参数：r n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `_private.Mathlib.Data.Nat.Choose.Basic.0.Nat.choose_le_middle_of_le_half
_left`：∀ {n r : ℕ}, r ≤ n / 2 → n.choose r ≤ n.choose (n / 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.choose_symm`：choose_symm {n k : Nat} (hk : k <= n) : choose n (n - k
) = choose n k
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n

--- 原说明 ---
`choose n r` is maximised when `r` is `n/2`.
-/
theorem choose_le_middle (r n : ℕ) : choose n r ≤ choose n (n / 2) := by
  rcases le_or_gt r n with b | b
  · rcases le_or_gt r (n / 2) with a | h
    · apply choose_le_middle_of_le_half_left a
    · rw [← choose_symm b]
      apply choose_le_middle_of_le_half_left
      lia
  · rw [choose_eq_zero_of_lt b]
    apply zero_le

/-! #### Inequalities about increasing the first argument -/


/-
**Nat.choose_le_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_le_succ (a c : Nat) : choose a c <= choose a.succ c
参数：a c : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
#### Inequalities about increasing the first argument
-/
theorem choose_le_succ (a c : ℕ) : choose a c ≤ choose a.succ c := by
  cases c <;> grind
/-
**Nat.choose_le_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_le_add (a b c : Nat) : choose a c <= choose (a + b) c
参数：a b c : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.choose_le_succ`：choose_le_succ (a c : Nat) : choose a c <= choose a.
succ c
-/
theorem choose_le_add (a b c : ℕ) : choose a c ≤ choose (a + b) c := by
  induction b with
  | zero => simp
  | succ b_n b_ih => exact b_ih.trans (choose_le_succ (a + b_n) c)

@[gcongr]
/-
**Nat.choose_le_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_le_choose {a b : Nat} (c : Nat) (h : a <= b) : choose a c <= choose
 b c
参数：c : Nat；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.choose_le_add`：choose_le_add (a b c : Nat) : choose a c <= choose (a
 + b) c
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
-/
theorem choose_le_choose {a b : ℕ} (c : ℕ) (h : a ≤ b) : choose a c ≤ choose b c :=
  Nat.add_sub_cancel' h ▸ choose_le_add a (b - a) c
/-
**Nat.choose_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_mono (b : Nat) : Monotone fun a => choose a b
参数：b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.choose_le_choose`：choose_le_choose {a b : Nat} (c : Nat) (h : a <= b
) : choose a c <= choose b c
-/
theorem choose_mono (b : ℕ) : Monotone fun a => choose a b := fun _ _ => choose_le_choose b
/-
**Nat.choose_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_eq_one_iff {n k : Nat} : n.choose k = 1 ↔ k = 0 ∨ n = k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem choose_eq_one_iff {n k : ℕ} : n.choose k = 1 ↔ k = 0 ∨ n = k := by
  rcases lt_trichotomy k n with hk | rfl | hk
  · grind [k.choose_mono hk]
  · simp
  · grind

/-! #### Multichoose

Whereas `choose n k` is the number of subsets of cardinality `k` from a type of cardinality `n`,
`multichoose n k` is the number of multisets of cardinality `k` from a type of cardinality `n`.

Alternatively, whereas `choose n k` counts the number of combinations,
i.e. ways to select `k` items (up to permutation) from `n` items without replacement,
`multichoose n k` counts the number of multicombinations,
i.e. ways to select `k` items (up to permutation) from `n` items with replacement.

Note that `multichoose` is *not* the multinomial coefficient, although it can be computed
in terms of multinomial coefficients. For details see https://mathworld.wolfram.com/Multichoose.html

-/

/--
`multichoose n k` is the number of multisets of cardinality `k` from a type of cardinality `n`. -/
/-
**Nat.multichoose** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`multichoose n k` is the number of multisets of cardinality `k` from a type of c
ardinality `n`.
-/
def multichoose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 =>
    multichoose n (k + 1) + multichoose (n + 1) k

@[simp]
/-
**Nat.multichoose_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multichoose_zero_right (n : Nat) : multichoose n 0 = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multichoose.eq_1`：∀ (x : ℕ), x.multichoose 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem multichoose_zero_right (n : ℕ) : multichoose n 0 = 1 := by cases n <;> simp [multichoose]

@[simp]
/-
**Nat.multichoose_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multichoose_zero_succ (k : Nat) : multichoose 0 (k + 1) = 0
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multichoose.eq_2`：∀ (n : ℕ), Nat.multichoose 0 n.succ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem multichoose_zero_succ (k : ℕ) : multichoose 0 (k + 1) = 0 := by simp [multichoose]
/-
**Nat.multichoose_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multichoose_succ_succ (n k : Nat) : multichoose (n + 1) (k + 1) = multicho
ose n (k + 1) + multichoose (n + 1) k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multichoose.eq_3`：∀ (n k : ℕ), n.succ.multichoose k.succ = n.multich
oose (k + 1) + (n + 1).multichoose k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem multichoose_succ_succ (n k : ℕ) :
    multichoose (n + 1) (k + 1) = multichoose n (k + 1) + multichoose (n + 1) k := by
  simp [multichoose]

@[simp]
/-
**Nat.multichoose_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multichoose_one (k : Nat) : multichoose 1 k = 1
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multichoose_zero_right`：multichoose_zero_right (n : Nat) : multichoo
se n 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.multichoose_succ_succ`：multichoose_succ_succ (n k : Nat) : multichoo
se (n + 1) (k + 1) = multichoose n (k + 1) + multichoose (n + 1) k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.multichoose_zero_succ`：multichoose_zero_succ (k : Nat) : multichoose
 0 (k + 1) = 0
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
-/
theorem multichoose_one (k : ℕ) : multichoose 1 k = 1 := by
  induction k with
  | zero => simp
  | succ k IH => simp [multichoose_succ_succ 0 k, IH]

@[simp]
/-
**Nat.multichoose_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multichoose_two (k : Nat) : multichoose 2 k = k + 1
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multichoose_zero_right`：multichoose_zero_right (n : Nat) : multichoo
se n 0 = 1
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.multichoose.eq_3`：∀ (n k : ℕ), n.succ.multichoose k.succ = n.multich
oose (k + 1) + (n + 1).multichoose k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.multichoose_one`：multichoose_one (k : Nat) : multichoose 1 k = 1
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
-/
theorem multichoose_two (k : ℕ) : multichoose 2 k = k + 1 := by
  induction k with
  | zero => simp
  | succ k IH => rw [multichoose, IH]; simp [Nat.add_comm]

@[simp]
/-
**Nat.multichoose_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multichoose_one_right (n : Nat) : multichoose n 1 = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multichoose_zero_succ`：multichoose_zero_succ (k : Nat) : multichoose
 0 (k + 1) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.multichoose_succ_succ`：multichoose_succ_succ (n k : Nat) : multichoo
se (n + 1) (k + 1) = multichoose n (k + 1) + multichoose (n + 1) k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.multichoose_zero_right`：multichoose_zero_right (n : Nat) : multichoo
se n 0 = 1
-/
theorem multichoose_one_right (n : ℕ) : multichoose n 1 = n := by
  induction n with
  | zero => simp
  | succ n IH => simp [multichoose_succ_succ n 0, IH]
/-
**Nat.multichoose_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multichoose_eq : forall n k : Nat, multichoose n k = (n + k - 1).choose k 
| _, 0 => by simp | 0, k + 1 => by simp | n + 1, k + 1 => by have : n + (k + 1) 
< (n + 1) + (k + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.multichoose_eq._unary`：∀ (_x : (_ : ℕ) ×' ℕ), _x.1.multichoose _x.2 
= (_x.1 + _x.2 - 1).choose _x.2
-/
theorem multichoose_eq : ∀ n k : ℕ, multichoose n k = (n + k - 1).choose k
  | _, 0 => by simp
  | 0, k + 1 => by simp
  | n + 1, k + 1 => by
    have : n + (k + 1) < (n + 1) + (k + 1) := Nat.add_lt_add_right (Nat.lt_succ_self _) _
    have : (n + 1) + k < (n + 1) + (k + 1) := Nat.add_lt_add_left (Nat.lt_succ_self _) _
    rw [multichoose_succ_succ, Nat.add_comm, Nat.succ_add_sub_one, ← Nat.add_assoc,
      Nat.choose_succ_succ]
    simp [multichoose_eq n (k + 1), multichoose_eq (n + 1) k]

end Nat

