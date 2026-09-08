/-
Copyright (c) 2025 Beibei Xiong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beibei Xiong, Yu Shao, Weijie Jiang, Zhengfeng Yang
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# Stirling Numbers

This file defines Stirling numbers of the first and second kinds, proves their fundamental
recurrence relations, and establishes some of their key properties and identities.

## The Stirling numbers of the first kind

The unsigned Stirling numbers of the first kind, represent the number of ways
to partition `n` distinct elements into `k` non-empty cycles.

## The Stirling numbers of the second kind

The Stirling numbers of the second kind, represent the number of ways to partition
`n` distinct elements into `k` non-empty subsets.

## Main definitions

* `Nat.stirlingFirst`: the number of ways to partition `n` distinct elements into `k` non-empty
  cycles, defined by the recursive relationship it satisfies.
* `Nat.stirlingSecond`: the number of ways to partition `n` distinct elements into `k` non-empty
  subsets, defined by the recursive relationship it satisfies.

## References

* [Knuth, *The Art of Computer Programming*, Volume 1, §1.2.6][knuth1997]
-/

@[expose] public section

open Nat

namespace Nat

/--
`Nat.stirlingFirst n k` is the (unsigned) Stirling number of the first kind,
counting the number of permutations of `n` elements with exactly `k` disjoint cycles.
-/
/-
**Nat.stirlingFirst** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nat.stirlingFirst n k` is the (unsigned) Stirling number of the first kind,
counting the number of permutations of `n` elements with exactly `k` disjoint cy
cles.
-/
def stirlingFirst : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * stirlingFirst n (k + 1) + stirlingFirst n k

@[simp]
/-
**Nat.stirlingFirst_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingFirst_zero : stirlingFirst 0 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stirlingFirst_zero : stirlingFirst 0 0 = 1 :=
  rfl

@[simp]
/-
**Nat.stirlingFirst_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingFirst_zero_succ (k : Nat) : stirlingFirst 0 (succ k) = 0
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stirlingFirst_zero_succ (k : ℕ) : stirlingFirst 0 (succ k) = 0 :=
  rfl

@[simp]
/-
**Nat.stirlingFirst_succ_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingFirst_succ_zero (n : Nat) : stirlingFirst (succ n) 0 = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stirlingFirst_succ_zero (n : ℕ) : stirlingFirst (succ n) 0 = 0 :=
  rfl
/-
**Nat.stirlingFirst_succ_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingFirst_succ_left (n k : Nat) (hk : k != 0) : stirlingFirst (n + 1) 
k = n * stirlingFirst n k + stirlingFirst n (k - 1)
参数：n k : Nat；hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem stirlingFirst_succ_left (n k : ℕ) (hk : k ≠ 0) :
    stirlingFirst (n + 1) k = n * stirlingFirst n k + stirlingFirst n (k - 1) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hk)
  rfl
/-
**Nat.stirlingFirst_succ_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingFirst_succ_right (n k : Nat) (hn : n != 0) : stirlingFirst n (k + 
1) = (n - 1) * stirlingFirst (n - 1) (k + 1) + stirlingFirst (n - 1) k
参数：n k : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem stirlingFirst_succ_right (n k : ℕ) (hn : n ≠ 0) :
    stirlingFirst n (k + 1) =
      (n - 1) * stirlingFirst (n - 1) (k + 1) + stirlingFirst (n - 1) k := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hn)
  rfl
/-
**Nat.stirlingFirst_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingFirst_succ_succ (n k : Nat) : stirlingFirst (n + 1) (k + 1) = n * 
stirlingFirst n (k + 1) + stirlingFirst n k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stirlingFirst_succ_succ (n k : ℕ) :
    stirlingFirst (n + 1) (k + 1) = n * stirlingFirst n (k + 1) + stirlingFirst n k := by
  rfl
/-
**Nat.stirlingFirst_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n k : ℕ}, n < k → n.stirlingFirst k = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stirlingFirst_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → stirlingFirst n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by rw [stirlingFirst]
  | n + 1, k + 1, hk => by
    rw [stirlingFirst_succ_succ, stirlingFirst_eq_zero_of_lt (Nat.lt_of_succ_lt_succ hk),
      stirlingFirst_eq_zero_of_lt (Nat.lt_of_succ_lt hk), mul_zero]
/-
**Nat.stirlingFirst_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingFirst_self (n : Nat) : stirlingFirst n n = 1
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
· 使用定理 `Nat.stirlingFirst_eq_zero_of_lt`：∀ {n k : ℕ}, n < k → n.stirlingFirst k 
= 0
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem stirlingFirst_self (n : ℕ) : stirlingFirst n n = 1 := by
  induction n <;> simp only [*, stirlingFirst, stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self _),
    mul_zero]
/-
**Nat.stirlingFirst_succ_self_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingFirst_succ_self_left (n : Nat) : stirlingFirst (n + 1) n = (n + 1)
.choose 2
参数：n : Nat。
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.choose_succ_self`：choose_succ_self (n : Nat) : choose n (succ n) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.stirlingFirst_succ_succ`：stirlingFirst_succ_succ (n k : Nat) : stirl
ingFirst (n + 1) (k + 1) = n * stirlingFirst n (k + 1) + stirlingFirst n k
· 使用定理 `Nat.stirlingFirst_self`：stirlingFirst_self (n : Nat) : stirlingFirst n n
 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.choose_succ_succ`：choose_succ_succ (n k : Nat) : choose (succ n) (su
cc k) = choose n k + choose n (succ k)
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
-/
theorem stirlingFirst_succ_self_left (n : ℕ) : stirlingFirst (n + 1) n = (n + 1).choose 2 := by
  induction n with
  | zero => simp only [zero_add, stirlingFirst_succ_zero, choose_succ_self]
  | succ n ih =>
    rw [stirlingFirst_succ_succ, ih, stirlingFirst_self, mul_one, Nat.choose_succ_succ (n + 1),
      Nat.choose_one_right]
/-
**Nat.stirlingFirst_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingFirst_one_right (n : Nat) : stirlingFirst (n + 1) 1 = n.factorial
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.stirlingFirst_succ_succ`：stirlingFirst_succ_succ (n k : Nat) : stirl
ingFirst (n + 1) (k + 1) = n * stirlingFirst n (k + 1) + stirlingFirst n k
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.stirlingFirst_succ_zero`：stirlingFirst_succ_zero (n : Nat) : stirlin
gFirst (succ n) 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stirlingFirst_one_right (n : ℕ) : stirlingFirst (n + 1) 1 = n.factorial := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [stirlingFirst_succ_succ, zero_add, hn, stirlingFirst_succ_zero]
    simp [Nat.factorial_succ]


/--
`Nat.stirlingSecond n k` is the Stirling number of the second kind,
counting the number of ways to partition a set of `n` elements into `k` nonempty subsets.
-/
/-
**Nat.stirlingSecond** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nat.stirlingSecond n k` is the Stirling number of the second kind,
counting the number of ways to partition a set of `n` elements into `k` nonempty
 subsets.
-/
def stirlingSecond : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
    (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k

@[simp]
/-
**Nat.stirlingSecond_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingSecond_zero : stirlingSecond 0 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stirlingSecond_zero : stirlingSecond 0 0 = 1 :=
  rfl

@[simp]
/-
**Nat.stirlingSecond_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingSecond_zero_succ (k : Nat) : stirlingSecond 0 (succ k) = 0
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stirlingSecond_zero_succ (k : ℕ) : stirlingSecond 0 (succ k) = 0 :=
  rfl

@[simp]
/-
**Nat.stirlingSecond_succ_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingSecond_succ_zero (n : Nat) : stirlingSecond (succ n) 0 = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stirlingSecond_succ_zero (n : ℕ) : stirlingSecond (succ n) 0 = 0 :=
  rfl
/-
**Nat.stirlingSecond_succ_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingSecond_succ_left (n k : Nat) (hk : k != 0) : stirlingSecond (n + 1
) k = k * stirlingSecond n k + stirlingSecond n (k - 1)
参数：n k : Nat；hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem stirlingSecond_succ_left (n k : ℕ) (hk : k ≠ 0) :
    stirlingSecond (n + 1) k = k * stirlingSecond n k + stirlingSecond n (k - 1) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hk)
  rfl
/-
**Nat.stirlingSecond_succ_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingSecond_succ_right (n k : Nat) (hn : n != 0) : stirlingSecond n (k 
+ 1) = (k + 1) * stirlingSecond (n - 1) (k + 1) + stirlingSecond (n - 1) k
参数：n k : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le'`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = k + m
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem stirlingSecond_succ_right (n k : ℕ) (hn : n ≠ 0) :
    stirlingSecond n (k + 1) =
      (k + 1) * stirlingSecond (n - 1) (k + 1) + stirlingSecond (n - 1) k := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.pos_of_ne_zero hn)
  rfl
/-
**Nat.stirlingSecond_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingSecond_succ_succ (n k : Nat) : stirlingSecond (n + 1) (k + 1) = (k
 + 1) * stirlingSecond n (k + 1) + stirlingSecond n k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stirlingSecond_succ_succ (n k : ℕ) :
    stirlingSecond (n + 1) (k + 1) =
      (k + 1) * stirlingSecond n (k + 1) + stirlingSecond n k := rfl
/-
**Nat.stirlingSecond_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n k : ℕ}, n < k → n.stirlingSecond k = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stirlingSecond_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → stirlingSecond n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, _ + 1, _ => by rw [stirlingSecond]
  | n + 1, k + 1, hk => by
    simp only [stirlingSecond_succ_succ, stirlingSecond_eq_zero_of_lt (Nat.lt_of_succ_lt_succ hk),
      stirlingSecond_eq_zero_of_lt (Nat.lt_of_succ_lt hk), mul_zero]
/-
**Nat.stirlingSecond_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingSecond_self (n : Nat) : stirlingSecond n n = 1
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
· 使用定理 `Nat.stirlingSecond_eq_zero_of_lt`：∀ {n k : ℕ}, n < k → n.stirlingSecond 
k = 0
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem stirlingSecond_self (n : ℕ) : stirlingSecond n n = 1 := by
  induction n <;> simp only [*, stirlingSecond, stirlingSecond_eq_zero_of_lt (lt_succ_self _),
    mul_zero]
/-
**Nat.stirlingSecond_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingSecond_one_right (n : Nat) : stirlingSecond (n + 1) 1 = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.stirlingSecond.eq_4`：∀ (n k : ℕ), n.succ.stirlingSecond k.succ = (k 
+ 1) * n.stirlingSecond (k + 1) + n.stirlingSecond k
· 使用定理 `Nat.stirlingSecond_succ_zero`：stirlingSecond_succ_zero (n : Nat) : stirl
ingSecond (succ n) 0 = 0
-/
theorem stirlingSecond_one_right (n : ℕ) : stirlingSecond (n + 1) 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stirlingSecond, stirlingSecond_succ_zero, ih]
/-
**Nat.stirlingSecond_succ_self_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：stirlingSecond_succ_self_left (n : Nat) : stirlingSecond (n + 1) n = (n + 
1).choose 2
参数：n : Nat。
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.choose_succ_self`：choose_succ_self (n : Nat) : choose n (succ n) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.stirlingSecond_succ_succ`：stirlingSecond_succ_succ (n k : Nat) : sti
rlingSecond (n + 1) (k + 1) = (k + 1) * stirlingSecond n (k + 1) + stirlingSecon
d n k
· 使用定理 `Nat.stirlingSecond_self`：stirlingSecond_self (n : Nat) : stirlingSecond 
n n = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.choose_succ_succ`：choose_succ_succ (n k : Nat) : choose (succ n) (su
cc k) = choose n k + choose n (succ k)
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
-/
theorem stirlingSecond_succ_self_left (n : ℕ) :
    stirlingSecond (n + 1) n = (n + 1).choose 2 := by
  induction n with
  | zero => simp only [zero_add, stirlingSecond_succ_zero, choose_succ_self]
  | succ n ih =>
    rw [stirlingSecond_succ_succ, ih, stirlingSecond_self, mul_one,
      Nat.choose_succ_succ (n + 1), Nat.choose_one_right]

end Nat

