/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Set.Lattice.Image

/-!
# Naturals pairing function

This file defines a pairing function for the naturals as follows:
```text
 0  1  4  9 16
 2  3  5 10 17
 6  7  8 11 18
12 13 14 15 19
20 21 22 23 24
```

It has the advantage of being monotone in both directions and sending `⟦0, n^2 - 1⟧` to
`⟦0, n - 1⟧²`.
-/

@[expose] public section

assert_not_exists Monoid

open Prod Decidable Function

namespace Nat

/-- Pairing function for the natural numbers. -/
@[pp_nodot]
/-
**Nat.pair** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：pair (a b : Nat) : Nat
参数：a b : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pairing function for the natural numbers.
-/
def pair (a b : ℕ) : ℕ :=
  if a < b then b * b + a else a * a + a + b

/-- Unpairing function for the natural numbers. -/
@[pp_nodot]
/-
**Nat.unpair** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：unpair (n : Nat) : Nat × Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unpairing function for the natural numbers.
-/
def unpair (n : ℕ) : ℕ × ℕ :=
  let s := sqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

@[simp]
/-
**Nat.pair_unpair** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `Nat.sqrt_le`：∀ (n : ℕ), n.sqrt * n.sqrt ≤ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.sub_le_iff_le_add`：∀ {a b c : ℕ}, a - b ≤ c ↔ a ≤ c + b
· 使用定理 `Nat.sub_le_iff_le_add'`：∀ {a b c : ℕ}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用引理 `Nat.sqrt_le_add`：sqrt_le_add (n : Nat) : n <= sqrt n * sqrt n + sqrt n +
 sqrt n
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
-/
theorem pair_unpair (n : ℕ) : pair (unpair n).1 (unpair n).2 = n := by
  dsimp only [unpair]; let s := sqrt n
  have sm : s * s + (n - s * s) = n := Nat.add_sub_cancel' (sqrt_le _)
  split_ifs with h
  · simp [s, pair, h, sm]
  · have hl : n - s * s - s ≤ s := Nat.sub_le_iff_le_add.2
      (Nat.sub_le_iff_le_add'.2 <| by rw [← Nat.add_assoc]; apply sqrt_le_add)
    simp [s, pair, hl.not_gt, Nat.add_assoc, Nat.add_sub_cancel' (le_of_not_gt h), sm]
/-
**Nat.pair_eq_of_unpair_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pair_eq_of_unpair_eq {n a b} (H : unpair n = (a, b)) : pair a b = n
参数：H : unpair n = (a, b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.pair_unpair`：pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 
= n
-/
theorem pair_eq_of_unpair_eq {n a b} (H : unpair n = (a, b)) : pair a b = n := by
  simpa [H] using pair_unpair n

@[simp]
/-
**Nat.unpair_pair** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `Nat.sqrt_add_eq`：sqrt_add_eq (n : Nat) (h : a <= n + n) : sqrt (n * n + 
a) = n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.add_le_add_left`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), k + n ≤ k + m
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
-/
theorem unpair_pair (a b : ℕ) : unpair (pair a b) = (a, b) := by
  dsimp only [pair]; split_ifs with h
  · show unpair (b * b + a) = (a, b)
    have be : sqrt (b * b + a) = b := sqrt_add_eq _ (le_trans (le_of_lt h) (Nat.le_add_left _ _))
    simp [unpair, be, Nat.add_sub_cancel_left, h]
  · show unpair (a * a + a + b) = (a, b)
    have ae : sqrt (a * a + (a + b)) = a := by
      rw [sqrt_add_eq]
      exact Nat.add_le_add_left (le_of_not_gt h) _
    simp [unpair, ae, Nat.add_assoc, Nat.add_sub_cancel_left]

/-- An equivalence between `ℕ × ℕ` and `ℕ`. -/
@[simps -fullyApplied]
/-
**Nat.pairEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：pairEquiv : Nat × Nat ≃ Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pair_unpair`：pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 
= n

--- 原说明 ---
An equivalence between `ℕ × ℕ` and `ℕ`.
-/
def pairEquiv : ℕ × ℕ ≃ ℕ :=
  ⟨uncurry pair, unpair, fun ⟨a, b⟩ => unpair_pair a b, pair_unpair⟩
/-
**Nat.surjective_unpair** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：surjective_unpair : Surjective unpair
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem surjective_unpair : Surjective unpair :=
  pairEquiv.symm.surjective

@[simp]
/-
**Nat.pair_eq_pair** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pair_eq_pair {a b c d : Nat} : pair a b = pair c d ↔ a = c ∧ b = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
-/
theorem pair_eq_pair {a b c d : ℕ} : pair a b = pair c d ↔ a = c ∧ b = d :=
  pairEquiv.injective.eq_iff.trans (@Prod.ext_iff ℕ ℕ (a, b) (c, d))
/-
**Nat.unpair_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：unpair_lt {n : Nat} (n1 : 1 <= n) : (unpair n).1 < n
参数：n1 : 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Nat.sqrt_le_self`：sqrt_le_self (n : Nat) : sqrt n <= n
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.sqrt_pos`：sqrt_pos : 0 < sqrt n ↔ 0 < n
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
-/
theorem unpair_lt {n : ℕ} (n1 : 1 ≤ n) : (unpair n).1 < n := by
  let s := sqrt n
  simp only [unpair]
  by_cases h : n - s * s < s <;> simp only [h, ↓reduceIte, gt_iff_lt, s]
  · exact lt_of_lt_of_le h (sqrt_le_self _)
  · simp only [not_lt] at h
    have s0 : 0 < s := sqrt_pos.2 n1
    exact lt_of_le_of_lt h (Nat.sub_lt n1 (Nat.mul_pos s0 s0))

@[simp]
/-
**Nat.unpair_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：unpair_zero : unpair 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.unpair.eq_1`：∀ (n : ℕ),   Nat.unpair n =     if n - n.sqrt * n.sqrt 
< n.sqrt then (n - n.sqrt * n.sqrt, n.sqrt) else (n.sqrt, n - n.sqrt * n.sqrt - 
n.sqr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.sqrt_zero`：Nat.sqrt 0 = 0
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem unpair_zero : unpair 0 = 0 := by
  rw [unpair]
  simp
/-
**Nat.unpair_left_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (Nat.unpair n).1 ≤ n
参数：n : ℕ；Nat.unpair n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.unpair_zero`：unpair_zero : unpair 0 = 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.unpair_lt`：unpair_lt {n : Nat} (n1 : 1 <= n) : (unpair n).1 < n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem unpair_left_le : ∀ n : ℕ, (unpair n).1 ≤ n
  | 0 => by simp
  | _ + 1 => le_of_lt (unpair_lt (Nat.succ_pos _))
/-
**Nat.left_le_pair** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：left_le_pair (a b : Nat) : a <= pair a b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Nat.unpair_left_le`：∀ (n : ℕ), (Nat.unpair n).1 ≤ n
-/
theorem left_le_pair (a b : ℕ) : a ≤ pair a b := by simpa using unpair_left_le (pair a b)
/-
**Nat.right_le_pair** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：right_le_pair (a b : Nat) : b <= pair a b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_mul_self`：∀ (n : ℕ), n ≤ n * n
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem right_le_pair (a b : ℕ) : b ≤ pair a b := by
  by_cases h : a < b
  · simpa [pair, h] using le_trans (le_mul_self _) (Nat.le_add_right _ _)
  · simp [pair, h]
/-
**Nat.unpair_right_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：unpair_right_le (n : Nat) : (unpair n).2 <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pair_unpair`：pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 
= n
· 使用定理 `Nat.right_le_pair`：right_le_pair (a b : Nat) : b <= pair a b
-/
theorem unpair_right_le (n : ℕ) : (unpair n).2 ≤ n := by
  simpa using right_le_pair n.unpair.1 n.unpair.2
/-
**Nat.pair_lt_pair_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pair_lt_pair_left {a₁ a₂} (b) (h : a₁ < a₂) : pair a₁ b < pair a₂ b
参数：b；h : a₁ < a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.add_lt_add_of_le_of_lt`：∀ {a b c d : ℕ}, a ≤ b → c < d → a + c < b +
 d
· 使用定理 `Nat.mul_self_le_mul_self`：∀ {m n : ℕ}, m ≤ n → m * m ≤ n * n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.lt_add_right`：∀ {a b : ℕ} (c : ℕ), a < b → a < b + c
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.add_lt_add`：∀ {a b c d : ℕ}, a < b → c < d → a + c < b + d
· 使用定理 `Nat.mul_self_lt_mul_self`：∀ {m n : ℕ}, m < n → m * m < n * n
· 使用定理 `Nat.add_lt_add_right`：∀ {n m : ℕ}, n < m → ∀ (k : ℕ), n + k < m + k
-/
theorem pair_lt_pair_left {a₁ a₂} (b) (h : a₁ < a₂) : pair a₁ b < pair a₂ b := by
  by_cases h₁ : a₁ < b <;> simp only [pair, h₁, ↓reduceIte, Nat.add_assoc]
  · by_cases h₂ : a₂ < b
    · simp [h₂, h]
    simp only [h₂, ↓reduceIte]
    apply Nat.add_lt_add_of_le_of_lt
    · exact Nat.mul_self_le_mul_self (not_lt.mp h₂)
    · exact Nat.lt_add_right _ h
  · simp at h₁
    simp only [not_lt_of_gt (lt_of_le_of_lt h₁ h), ite_false]
    apply add_lt_add
    · exact Nat.mul_self_lt_mul_self h
    · apply Nat.add_lt_add_right; assumption
/-
**Nat.pair_lt_pair_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pair_lt_pair_right (a) {b₁ b₂} (h : b₁ < b₂) : pair a b₁ < pair a b₂
参数：a；h : b₁ < b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Nat.mul_self_lt_mul_self`：∀ {m n : ℕ}, m < n → m * m < n * n
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.add_lt_add_iff_left`：∀ {k n m : ℕ}, k + n < k + m ↔ n < m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.sqrt_lt`：sqrt_lt : sqrt m < n ↔ m < n * n
· 使用引理 `Nat.sqrt_add_eq`：sqrt_add_eq (n : Nat) (h : a <= n + n) : sqrt (n * n + 
a) = n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem pair_lt_pair_right (a) {b₁ b₂} (h : b₁ < b₂) : pair a b₁ < pair a b₂ := by
  by_cases h₁ : a < b₁
  · simpa [pair, h₁, Nat.add_assoc, lt_trans h₁ h, h] using mul_self_lt_mul_self h
  · simp only [pair, h₁, ↓reduceIte, Nat.add_assoc]
    by_cases h₂ : a < b₂; swap; · simp [h₂, h]
    simp only [h₂, ↓reduceIte]
    rw [Nat.add_comm, Nat.add_comm _ a, Nat.add_assoc, Nat.add_lt_add_iff_left]
    rwa [Nat.add_comm, ← sqrt_lt, sqrt_add_eq]
    exact le_trans (not_lt.mp h₁) (Nat.le_add_left _ _)
/-
**Nat.pair_lt_max_add_one_sq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pair_lt_max_add_one_sq (m n : Nat) : pair m n < (max m n + 1) ^ 2
参数：m n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.pow_two`：∀ (a : ℕ), a ^ 2 = a * a
· 使用定理 `Nat.mul_add`：∀ (n m k : ℕ), n * (m + k) = n * m + n * k
· 使用定理 `Nat.add_mul`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem pair_lt_max_add_one_sq (m n : ℕ) : pair m n < (max m n + 1) ^ 2 := by
  simp only [pair, Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.add_assoc]
  split_ifs <;> simp [Nat.le_of_lt, not_lt.1, *] <;> lia
/-
**Nat.max_sq_add_min_le_pair** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：max_sq_add_min_le_pair (m n : Nat) : max m n ^ 2 + min m n <= pair m n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pair.eq_1`：∀ (a b : ℕ), Nat.pair a b = if a < b then b * b + a else 
a * a + a + b
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `Nat.pow_two`：∀ (a : ℕ), a ^ 2 = a * a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Nat.add_le_add_iff_left`：∀ {m k n : ℕ}, n + m ≤ n + k ↔ m ≤ k
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
-/
theorem max_sq_add_min_le_pair (m n : ℕ) : max m n ^ 2 + min m n ≤ pair m n := by
  rw [pair]
  rcases lt_or_ge m n with h | h
  · rw [if_pos h, max_eq_right h.le, min_eq_left h.le, Nat.pow_two]
  rw [if_neg h.not_gt, max_eq_left h, min_eq_right h, Nat.pow_two, Nat.add_assoc,
    Nat.add_le_add_iff_left]
  exact Nat.le_add_left _ _
/-
**Nat.add_le_pair** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_le_pair (m n : Nat) : m + n <= pair m n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.le_mul_self`：∀ (n : ℕ), n ≤ n * n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
-/
theorem add_le_pair (m n : ℕ) : m + n ≤ pair m n := by
  simp only [pair, Nat.add_assoc]
  split_ifs
  · have := le_mul_self n
    lia
  · exact Nat.le_add_left _ _
/-
**Nat.unpair_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：unpair_add_le (n : Nat) : (unpair n).1 + (unpair n).2 <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Nat.add_le_pair`：add_le_pair (m n : Nat) : m + n <= pair m n
· 使用定理 `Nat.pair_unpair`：pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 
= n
-/
theorem unpair_add_le (n : ℕ) : (unpair n).1 + (unpair n).2 ≤ n :=
  (add_le_pair _ _).trans_eq (pair_unpair _)

end Nat

open Nat

section CompleteLattice

@[to_dual]
/-
**iSup_unpair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_unpair {α} [CompleteLattice α] (f : Nat -> Nat -> α) : ⨆ n : Nat, f n
.unpair.1 n.unpair.2 = ⨆ (i : Nat) (j : Nat), f i j
参数：f : Nat -> Nat -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_prod`：iSup_prod {f : β × γ -> α} : ⨆ x, f x = ⨆ (i) (j), f (i, j)
· 使用定理 `Function.Surjective.iSup_comp`：Function.Surjective.iSup_comp {f : ι -> ι
'} (hf : Surjective f) (g : ι' -> α) : ⨆ x, g (f x) = ⨆ y, g y
· 使用定理 `Nat.surjective_unpair`：surjective_unpair : Surjective unpair
-/
theorem iSup_unpair {α} [CompleteLattice α] (f : ℕ → ℕ → α) :
    ⨆ n : ℕ, f n.unpair.1 n.unpair.2 = ⨆ (i : ℕ) (j : ℕ), f i j := by
  rw [← (iSup_prod : ⨆ i : ℕ × ℕ, f i.1 i.2 = _), ← Nat.surjective_unpair.iSup_comp]

end CompleteLattice

namespace Set

/-
**Set.iUnion_unpair_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_unpair_prod {α β} {s : Nat -> Set α} {t : Nat -> Set β} : ⋃ n : Nat
, s n.unpair.fst ×ˢ t n.unpair.snd = (⋃ n, s n) ×ˢ ⋃ n, t n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_prod`：iUnion_prod {ι ι' α β} (s : ι -> Set α) (t : ι' -> Set 
β) : ⋃ x : ι × ι', s x.1 ×ˢ t x.2 = (⋃ i : ι, s i) ×ˢ ⋃ i : ι', t i
· 使用定理 `Function.Surjective.iUnion_comp`：iUnion_comp {f : ι -> ι₂} (hf : Surject
ive f) (g : ι₂ -> Set α) : ⋃ x, g (f x) = ⋃ y, g y
· 使用定理 `Nat.surjective_unpair`：surjective_unpair : Surjective unpair
-/
theorem iUnion_unpair_prod {α β} {s : ℕ → Set α} {t : ℕ → Set β} :
    ⋃ n : ℕ, s n.unpair.fst ×ˢ t n.unpair.snd = (⋃ n, s n) ×ˢ ⋃ n, t n := by
  rw [← Set.iUnion_prod]
  exact surjective_unpair.iUnion_comp (fun x => s x.fst ×ˢ t x.snd)
/-
**Set.iUnion_unpair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_unpair {α} (f : Nat -> Nat -> Set α) : ⋃ n : Nat, f n.unpair.1 n.un
pair.2 = ⋃ (i : Nat) (j : Nat), f i j
参数：f : Nat -> Nat -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_unpair`：iSup_unpair {α} [CompleteLattice α] (f : Nat -> Nat -> α) :
 ⨆ n : Nat, f n.unpair.1 n.unpair.2 = ⨆ (i : Nat) (j : Nat), f i j
-/
theorem iUnion_unpair {α} (f : ℕ → ℕ → Set α) :
    ⋃ n : ℕ, f n.unpair.1 n.unpair.2 = ⋃ (i : ℕ) (j : ℕ), f i j :=
  iSup_unpair f
/-
**Set.iInter_unpair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iInter_unpair {α} (f : Nat -> Nat -> Set α) : ⋂ n : Nat, f n.unpair.1 n.un
pair.2 = ⋂ (i : Nat) (j : Nat), f i j
参数：f : Nat -> Nat -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_unpair`：∀ {α : Type u_1} [inst : CompleteLattice α] (f : ℕ → ℕ → α)
, ⨅ n, f (Nat.unpair n).1 (Nat.unpair n).2 = ⨅ i, ⨅ j, f i j
-/
theorem iInter_unpair {α} (f : ℕ → ℕ → Set α) :
    ⋂ n : ℕ, f n.unpair.1 n.unpair.2 = ⋂ (i : ℕ) (j : ℕ), f i j :=
  iInf_unpair f

end Set

