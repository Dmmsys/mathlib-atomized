/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Divisor Finsets

This file defines sets of divisors of a natural number. This is particularly useful as background
for defining Dirichlet convolution.

## Main Definitions
Let `n : ℕ`. All of the following definitions are in the `Nat` namespace:
* `divisors n` is the `Finset` of natural numbers that divide `n`.
* `properDivisors n` is the `Finset` of natural numbers that divide `n`, other than `n`.
* `divisorsAntidiagonal n` is the `Finset` of pairs `(x,y)` such that `x * y = n`.
* `Perfect n` is true when `n` is positive and the sum of `properDivisors n` is `n`.

## Conventions

Since `0` has infinitely many divisors, none of the definitions in this file make sense for it.
Therefore we adopt the convention that `Nat.divisors 0`, `Nat.properDivisors 0`,
`Nat.divisorsAntidiagonal 0` and `Int.divisorsAntidiag 0` are all `∅`.

## Tags
divisors, perfect numbers

-/

@[expose] public section

open Finset

namespace Nat

variable (n : ℕ)

/-- `divisors n` is the `Finset` of divisors of `n`. By convention, we set `divisors 0 = ∅`. -/
/-
**Nat.divisors** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：divisors : Finset Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`divisors n` is the `Finset` of divisors of `n`. By convention, we set `divisors
 0 = ∅`.
-/
def divisors : Finset ℕ := {d ∈ Ico 1 (n + 1) | d ∣ n}

/-- `properDivisors n` is the `Finset` of divisors of `n`, other than `n`.
By convention, we set `properDivisors 0 = ∅`. -/
/-
**Nat.properDivisors** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：properDivisors : Finset Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`properDivisors n` is the `Finset` of divisors of `n`, other than `n`.
By convention, we set `properDivisors 0 = ∅`.
-/
def properDivisors : Finset ℕ := {d ∈ Ico 1 n | d ∣ n}

/-- Pairs of divisors of a natural number as a finset.

`n.divisorsAntidiagonal` is the finset of pairs `(a, b) : ℕ × ℕ` such that `a * b = n`.
By convention, we set `Nat.divisorsAntidiagonal 0 = ∅`.

O(n). -/
/-
**Nat.divisorsAntidiagonal** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：divisorsAntidiagonal : Finset (Nat × Nat)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pairs of divisors of a natural number as a finset.

`n.divisorsAntidiagonal` is the finset of pairs `(a, b) : ℕ × ℕ` such that `a * 
b = n`.
By convention, we set `Nat.divisorsAntidiagonal 0 = ∅`.

O(n).
-/
def divisorsAntidiagonal : Finset (ℕ × ℕ) :=
  (Icc 1 n).filterMap (fun x ↦ let y := n / x; if x * y = n then some (x, y) else none)
    fun x₁ x₂ (x, y) hx₁ hx₂ ↦ by aesop

/-- Pairs of divisors of a natural number, as a list.

`n.divisorsAntidiagonalList` is the list of pairs `(a, b) : ℕ × ℕ` such that `a * b = n`, ordered
by increasing `a`. By convention, we set `Nat.divisorsAntidiagonalList 0 = []`.
-/
/-
**Nat.divisorsAntidiagonalList** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：divisorsAntidiagonalList (n : Nat) : List (Nat × Nat)
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a

--- 原说明 ---
Pairs of divisors of a natural number, as a list.

`n.divisorsAntidiagonalList` is the list of pairs `(a, b) : ℕ × ℕ` such that `a 
* b = n`, ordered
by increasing `a`. By convention, we set `Nat.divisorsAntidiagonalList 0 = []`.
-/
def divisorsAntidiagonalList (n : ℕ) : List (ℕ × ℕ) :=
  (List.range' 1 n).filterMap
    (fun x ↦ let y := n / x; if x * y = n then some (x, y) else none)

variable {n}

@[simp]
/-
**Nat.filter_dvd_eq_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：filter_dvd_eq_divisors (h : n != 0) : {d in range n.succ | d ∣ n} = n.divi
sors
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Nat.pos_of_dvd_of_pos`：∀ {m n : ℕ}, m ∣ n → 0 < n → 0 < m
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem filter_dvd_eq_divisors (h : n ≠ 0) : {d ∈ range n.succ | d ∣ n} = n.divisors := by
  ext
  simp only [divisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)

@[simp]
/-
**Nat.filter_dvd_eq_properDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：filter_dvd_eq_properDivisors (h : n != 0) : {d in range n | d ∣ n} = n.pro
perDivisors
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Nat.pos_of_dvd_of_pos`：∀ {m n : ℕ}, m ∣ n → 0 < n → 0 < m
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem filter_dvd_eq_properDivisors (h : n ≠ 0) : {d ∈ range n | d ∣ n} = n.properDivisors := by
  ext
  simp only [properDivisors, mem_filter, mem_range, mem_Ico, and_congr_left_iff, iff_and_self]
  exact fun ha _ => succ_le_iff.mpr (pos_of_dvd_of_pos ha h.bot_lt)
/-
**Nat.self_notMem_properDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：self_notMem_properDivisors : n ∉ properDivisors n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem self_notMem_properDivisors : n ∉ properDivisors n := by simp [properDivisors]

@[simp]
/-
**Nat.mem_properDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_properDivisors {m : Nat} : n in properDivisors m ↔ n ∣ m ∧ n < m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_true`：∀ {α : Type u_1} {h : DecidablePred fun x => True} (
s : Finset α), {x ∈ s | True} = s
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.filter_dvd_eq_properDivisors`：filter_dvd_eq_properDivisors (h : n !=
 0) : {d in range n | d ∣ n} = n.properDivisors
-/
theorem mem_properDivisors {m : ℕ} : n ∈ properDivisors m ↔ n ∣ m ∧ n < m := by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [properDivisors]
  simp only [and_comm, ← filter_dvd_eq_properDivisors hm, mem_filter, mem_range]
/-
**Nat.insert_self_properDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：insert_self_properDivisors (h : n != 0) : insert n (properDivisors n) = di
visors n
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.divisors.eq_1`：∀ (n : ℕ), n.divisors = {d ∈ Finset.Ico 1 (n + 1) | d
 ∣ n}
· 使用定理 `Nat.properDivisors.eq_1`：∀ (n : ℕ), n.properDivisors = {d ∈ Finset.Ico 1
 n | d ∣ n}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.insert_Ico_right_eq_Ico_add_one`：insert_Ico_right_eq_Ico_add_one 
(h : a <= b) : insert b (Ico a b) = Ico a (b + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem insert_self_properDivisors (h : n ≠ 0) : insert n (properDivisors n) = divisors n := by
  rw [divisors, properDivisors,
    ← Finset.insert_Ico_right_eq_Ico_add_one (one_le_iff_ne_zero.2 h),
    Finset.filter_insert, if_pos (dvd_refl n)]
/-
**Nat.cons_self_properDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cons_self_properDivisors (h : n != 0) : cons n (properDivisors n) self_not
Mem_properDivisors = divisors n
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Nat.insert_self_properDivisors`：insert_self_properDivisors (h : n != 0) 
: insert n (properDivisors n) = divisors n
-/
theorem cons_self_properDivisors (h : n ≠ 0) :
    cons n (properDivisors n) self_notMem_properDivisors = divisors n := by
  rw [cons_eq_insert, insert_self_properDivisors h]

@[simp, grind =]
/-
**Nat.mem_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_true`：∀ {α : Type u_1} {h : DecidablePred fun x => True} (
s : Finset α), {x ∈ s | True} = s
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.filter_dvd_eq_divisors`：filter_dvd_eq_divisors (h : n != 0) : {d in 
range n.succ | d ∣ n} = n.divisors
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem mem_divisors {m : ℕ} : n ∈ divisors m ↔ n ∣ m ∧ m ≠ 0 := by
  rcases eq_or_ne m 0 with (rfl | hm); · simp [divisors]
  simp only [hm, Ne, not_false_iff, and_true, ← filter_dvd_eq_divisors hm, mem_filter,
    mem_range, and_iff_right_iff_imp, Nat.lt_succ_iff]
  exact le_of_dvd hm.bot_lt
/-
**Nat.dvd_of_mem_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_of_mem_divisors {m : Nat} (h : n in divisors m) : n ∣ m
参数：h : n in divisors m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
-/
theorem dvd_of_mem_divisors {m : ℕ} (h : n ∈ divisors m) : n ∣ m := (mem_divisors.mp h).1
/-
**Nat.ne_zero_of_mem_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ne_zero_of_mem_divisors {m : Nat} (h : n in divisors m) : m != 0
参数：h : n in divisors m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
-/
theorem ne_zero_of_mem_divisors {m : ℕ} (h : n ∈ divisors m) : m ≠ 0 := (mem_divisors.mp h).2
/-
**Nat.one_mem_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：one_mem_divisors : 1 in divisors n ↔ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_mem_divisors : 1 ∈ divisors n ↔ n ≠ 0 := by simp
/-
**Nat.mem_divisors_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_divisors_self (n : Nat) (h : n != 0) : n in n.divisors
参数：n : Nat；h : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem mem_divisors_self (n : ℕ) (h : n ≠ 0) : n ∈ n.divisors :=
  mem_divisors.2 ⟨dvd_rfl, h⟩

@[simp]
/-
**Nat.mem_divisorsAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_divisorsAntidiagonal {x : Nat × Nat} : x in divisorsAntidiagonal n ↔ x
.fst * x.snd = n ∧ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.filterMap.congr_simp`：∀ {α : Type u_1} {β : Type u_2} (f f_1 : α 
→ Option β) (e_f : f = f_1) (s s_1 : Finset α),   s = s_1 →     ∀ (f_inj : ∀ (a 
a' : α), ∀ b ∈ f …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_divisorsAntidiagonal {x : ℕ × ℕ} :
    x ∈ divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n ≠ 0 := by
  obtain ⟨a, b⟩ := x
  simp only [divisorsAntidiagonal, mul_div_eq_iff_dvd, mem_filterMap, mem_Icc, one_le_iff_ne_zero,
    Option.ite_none_right_eq_some, Option.some.injEq, Prod.ext_iff, and_left_comm, exists_eq_left]
  constructor
  · rintro ⟨han, ⟨ha, han'⟩, rfl⟩
    simp [Nat.mul_div_eq_iff_dvd, han]
    lia
  · rintro ⟨rfl, hab⟩
    rw [mul_ne_zero_iff] at hab
    simpa [hab.1, hab.2] using Nat.le_mul_of_pos_right _ hab.2.bot_lt
/-
**Nat.divisorsAntidiagonalList_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.divisorsAntidiagonalList 0 = []
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma divisorsAntidiagonalList_zero : divisorsAntidiagonalList 0 = [] := rfl
/-
**Nat.divisorsAntidiagonalList_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.divisorsAntidiagonalList 1 = [(1, 1)]
参数：1, 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma divisorsAntidiagonalList_one : divisorsAntidiagonalList 1 = [(1, 1)] := rfl

@[simp]
/-
**Nat.toFinset_divisorsAntidiagonalList** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：toFinset_divisorsAntidiagonalList {n : Nat} : n.divisorsAntidiagonalList.t
oFinset = n.divisorsAntidiagonal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.divisorsAntidiagonalList.eq_1`：∀ (n : ℕ),   n.divisorsAntidiagonalLi
st =     List.filterMap       (fun x =>         have y := n / x;         if x * 
y = n then some (x, y) …
· 使用定理 `Nat.divisorsAntidiagonal.eq_1`：∀ (n : ℕ),   n.divisorsAntidiagonal =    
 Finset.filterMap       (fun x =>         have y := n / x;         if x * y = n 
then some (x, y) el…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.toFinset_filterMap`：∀ {α : Type u_1} {β : Type u_2} (f : α → Option
 β) [inst : DecidableEq α] [inst_1 : DecidableEq β]   (f_inj : ∀ (a a' : α) (b :
 β), f a = so…
· 使用定理 `List.toFinset_range'_1_1`：∀ (a : ℕ), (List.range' 1 a).toFinset = Finset
.Icc 1 a
-/
lemma toFinset_divisorsAntidiagonalList {n : ℕ} :
    n.divisorsAntidiagonalList.toFinset = n.divisorsAntidiagonal := by
  rw [divisorsAntidiagonalList, divisorsAntidiagonal, List.toFinset_filterMap
    (f_inj := by simp_all), List.toFinset_range'_1_1]
/-
**Nat.pairwise_divisorsAntidiagonalList_fst** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pairwise_divisorsAntidiagonalList_fst {n : Nat} : n.divisorsAntidiagonalLi
st.Pairwise (·.fst < ·.fst)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.filterMap`：∀ {β : Type u_1} {α : Type u_2} {R : α → α → Pr
op} {S : β → β → Prop} (f : α → Option β),   (∀ (a a' : α), R a a' → ∀ (b : β), 
f a = some b …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Option.ite_none_right_eq_some`：∀ {α : Type u_1} {a : α} {p : Prop} {x : 
Decidable p} {b : Option α}, (if p then b else none) = some a ↔ p ∧ b = some a
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `List.SortedLT.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLT → List.Pairwise (fun x1 x2 => x1 < x2) l
· 使用定理 `List.sortedLT_range'`：sortedLT_range' (a b) {s} (hs : s != 0) : (range' 
a b s).SortedLT
· 使用定理 `Nat.one_ne_zero`：1 ≠ 0
-/
lemma pairwise_divisorsAntidiagonalList_fst {n : ℕ} :
    n.divisorsAntidiagonalList.Pairwise (·.fst < ·.fst) := by
  refine (List.sortedLT_range' _ _ Nat.one_ne_zero).pairwise.filterMap _ fun a b c d h ha h' => ?_
  rw [Option.ite_none_right_eq_some, Option.some.injEq] at h h'
  simpa [← h.right, ← h'.right]
/-
**Nat.pairwise_divisorsAntidiagonalList_snd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pairwise_divisorsAntidiagonalList_snd {n : Nat} : n.divisorsAntidiagonalLi
st.Pairwise (·.snd > ·.snd)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Pairwise.filterMap`：∀ {β : Type u_1} {α : Type u_2} {R : α → α → Pr
op} {S : β → β → Prop} (f : α → Option β),   (∀ (a a' : α), R a a' → ∀ (b : β), 
f a = some b …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Nat.div_lt_div_left`：∀ {a b c : ℕ}, a ≠ 0 → b ∣ a → c ∣ a → (a / b < a /
 c ↔ c < b)
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `List.SortedLT.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLT → List.Pairwise (fun x1 x2 => x1 < x2) l
· 使用定理 `List.sortedLT_range'`：sortedLT_range' (a b) {s} (hs : s != 0) : (range' 
a b s).SortedLT
· 使用定理 `Nat.one_ne_zero`：1 ≠ 0
-/
lemma pairwise_divisorsAntidiagonalList_snd {n : ℕ} :
    n.divisorsAntidiagonalList.Pairwise (·.snd > ·.snd) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  refine (List.sortedLT_range' _ _ Nat.one_ne_zero).pairwise.filterMap _ ?_
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, gt_iff_lt,
    and_imp, Prod.forall, Prod.mk.injEq]
  rintro a b hab _ _ ha rfl rfl _ _ hb rfl rfl
  rwa [Nat.div_lt_div_left hn ⟨_, hb.symm⟩ ⟨_, ha.symm⟩]
/-
**Nat.sortedLT_map_fst_divisorsAntidiagonalList** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sortedLT_map_fst_divisorsAntidiagonalList {n : Nat} : (n.divisorsAntidiago
nalList.map Prod.fst).SortedLT
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sortedLT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 < x2) l → l.SortedLT
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.pairwise_map`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} {R : 
α_1 → α_1 → Prop} {l : List α},   List.Pairwise R (List.map f l) ↔ List.Pairwise
 (fun a…
· 使用引理 `Nat.pairwise_divisorsAntidiagonalList_fst`：pairwise_divisorsAntidiagonal
List_fst {n : Nat} : n.divisorsAntidiagonalList.Pairwise (·.fst < ·.fst)
-/
lemma sortedLT_map_fst_divisorsAntidiagonalList {n : ℕ} :
    (n.divisorsAntidiagonalList.map Prod.fst).SortedLT :=
  (List.pairwise_map.mpr <| pairwise_divisorsAntidiagonalList_fst).sortedLT
/-
**Nat.sortedGT_map_snd_divisorsAntidiagonalList** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sortedGT_map_snd_divisorsAntidiagonalList {n : Nat} : (n.divisorsAntidiago
nalList.map Prod.snd).SortedGT
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sortedGT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 > x2) l → l.SortedGT
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.pairwise_map`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} {R : 
α_1 → α_1 → Prop} {l : List α},   List.Pairwise R (List.map f l) ↔ List.Pairwise
 (fun a…
· 使用引理 `Nat.pairwise_divisorsAntidiagonalList_snd`：pairwise_divisorsAntidiagonal
List_snd {n : Nat} : n.divisorsAntidiagonalList.Pairwise (·.snd > ·.snd)
-/
lemma sortedGT_map_snd_divisorsAntidiagonalList {n : ℕ} :
    (n.divisorsAntidiagonalList.map Prod.snd).SortedGT :=
  (List.pairwise_map.mpr <| pairwise_divisorsAntidiagonalList_snd).sortedGT
/-
**Nat.nodup_divisorsAntidiagonalList** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nodup_divisorsAntidiagonalList {n : Nat} : n.divisorsAntidiagonalList.Nodu
p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.Pairwise.nodup`：∀ {α : Type u} {l : List α} {r : α → α → Prop} [Std
.Irrefl r], List.Pairwise r l → l.Nodup
· 使用引理 `Nat.pairwise_divisorsAntidiagonalList_fst`：pairwise_divisorsAntidiagonal
List_fst {n : Nat} : n.divisorsAntidiagonalList.Pairwise (·.fst < ·.fst)
-/
lemma nodup_divisorsAntidiagonalList {n : ℕ} : n.divisorsAntidiagonalList.Nodup :=
  have : @Std.Irrefl (ℕ × ℕ) (·.fst < ·.fst) := ⟨by simp⟩
  pairwise_divisorsAntidiagonalList_fst.nodup

/-- The `Finset` and `List` versions agree by definition. -/
@[simp]
/-
**Nat.val_divisorsAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：val_divisorsAntidiagonal (n : Nat) : (divisorsAntidiagonal n).val = diviso
rsAntidiagonalList n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Finset` and `List` versions agree by definition.
-/
theorem val_divisorsAntidiagonal (n : ℕ) :
    (divisorsAntidiagonal n).val = divisorsAntidiagonalList n :=
  rfl

@[simp]
/-
**Nat.mem_divisorsAntidiagonalList** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_divisorsAntidiagonalList {n : Nat} {a : Nat × Nat} : a in n.divisorsAn
tidiagonalList ↔ a.1 * a.2 = n ∧ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用引理 `Nat.toFinset_divisorsAntidiagonalList`：toFinset_divisorsAntidiagonalList
 {n : Nat} : n.divisorsAntidiagonalList.toFinset = n.divisorsAntidiagonal
· 使用定理 `Nat.mem_divisorsAntidiagonal`：mem_divisorsAntidiagonal {x : Nat × Nat} :
 x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_divisorsAntidiagonalList {n : ℕ} {a : ℕ × ℕ} :
    a ∈ n.divisorsAntidiagonalList ↔ a.1 * a.2 = n ∧ n ≠ 0 := by
  rw [← List.mem_toFinset, toFinset_divisorsAntidiagonalList, mem_divisorsAntidiagonal]

@[simp high]
/-
**Nat.swap_mem_divisorsAntidiagonalList** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：swap_mem_divisorsAntidiagonalList {a : Nat × Nat} : a.swap in n.divisorsAn
tidiagonalList ↔ a in n.divisorsAntidiagonalList
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma swap_mem_divisorsAntidiagonalList {a : ℕ × ℕ} :
    a.swap ∈ n.divisorsAntidiagonalList ↔ a ∈ n.divisorsAntidiagonalList := by simp [mul_comm]
/-
**Nat.reverse_divisorsAntidiagonalList** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：reverse_divisorsAntidiagonalList (n : Nat) : n.divisorsAntidiagonalList.re
verse = n.divisorsAntidiagonalList.map .swap
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_asymm`：lt_asymm (h : a < b) : ¬b < a
· 使用定理 `List.Perm.eq_of_pairwise'`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Anti
symm r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂
 → l₁ = l₂
· 使用定理 `Function.instAntisymmSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.
Antisymm r], Std.Antisymm (Function.swap r)
· 使用定理 `Std.instAntisymmOfAsymm`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asymm 
r], Std.Antisymm r
· 使用定理 `List.Pairwise.reverse`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
 List.Pairwise (fun a b => R b a) l → List.Pairwise R l.reverse
· 使用引理 `Nat.pairwise_divisorsAntidiagonalList_snd`：pairwise_divisorsAntidiagonal
List_snd {n : Nat} : n.divisorsAntidiagonalList.Pairwise (·.snd > ·.snd)
· 使用定理 `List.Pairwise.map`：∀ {β : Type u_1} {α : Type u_2} {R : α → α → Prop} {l
 : List α} {S : β → β → Prop} (f : α → β),   (∀ (a b : α), R a b → S (f a) (f b)
) → Lis…
· 使用引理 `Nat.pairwise_divisorsAntidiagonalList_fst`：pairwise_divisorsAntidiagonal
List_fst {n : Nat} : n.divisorsAntidiagonalList.Pairwise (·.fst < ·.fst)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.perm_ext_iff_of_nodup`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Nodup 
→ l₂.Nodup → (l₁.Perm l₂ ↔ ∀ (a : α), a ∈ l₁ ↔ a ∈ l₂)
· 使用引理 `Nat.nodup_divisorsAntidiagonalList`：nodup_divisorsAntidiagonalList {n : 
Nat} : n.divisorsAntidiagonalList.Nodup
· 使用定理 `List.Nodup.map`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β}, Fu
nction.Injective f → l.Nodup → (List.map f l).Nodup
· 使用定理 `Prod.swap_injective`：swap_injective : Function.Injective (@swap α β)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma reverse_divisorsAntidiagonalList (n : ℕ) :
    n.divisorsAntidiagonalList.reverse = n.divisorsAntidiagonalList.map .swap := by
  have : Std.Asymm (α := ℕ × ℕ) (·.snd < ·.snd) := ⟨fun _ _ ↦ lt_asymm⟩
  refine List.Perm.eq_of_pairwise' pairwise_divisorsAntidiagonalList_snd.reverse
    (pairwise_divisorsAntidiagonalList_fst.map _ fun _ _ ↦ id) ?_
  simp [List.reverse_perm', List.perm_ext_iff_of_nodup nodup_divisorsAntidiagonalList
    (nodup_divisorsAntidiagonalList.map Prod.swap_injective), mul_comm]
/-
**Nat.ne_zero_of_mem_divisorsAntidiagonal** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ne_zero_of_mem_divisorsAntidiagonal {p : Nat × Nat} (hp : p in n.divisorsA
ntidiagonal) : p.1 != 0 ∧ p.2 != 0
参数：hp : p in n.divisorsAntidiagonal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_divisorsAntidiagonal`：mem_divisorsAntidiagonal {x : Nat × Nat} :
 x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_zero_of_mem_divisorsAntidiagonal {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) :
    p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  obtain ⟨hp₁, hp₂⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  exact mul_ne_zero_iff.mp (hp₁.symm ▸ hp₂)
/-
**Nat.left_ne_zero_of_mem_divisorsAntidiagonal** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：left_ne_zero_of_mem_divisorsAntidiagonal {p : Nat × Nat} (hp : p in n.divi
sorsAntidiagonal) : p.1 != 0
参数：hp : p in n.divisorsAntidiagonal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Nat.ne_zero_of_mem_divisorsAntidiagonal`：ne_zero_of_mem_divisorsAntidiag
onal {p : Nat × Nat} (hp : p in n.divisorsAntidiagonal) : p.1 != 0 ∧ p.2 != 0
-/
lemma left_ne_zero_of_mem_divisorsAntidiagonal {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) :
    p.1 ≠ 0 :=
  (ne_zero_of_mem_divisorsAntidiagonal hp).1
/-
**Nat.right_ne_zero_of_mem_divisorsAntidiagonal** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：right_ne_zero_of_mem_divisorsAntidiagonal {p : Nat × Nat} (hp : p in n.div
isorsAntidiagonal) : p.2 != 0
参数：hp : p in n.divisorsAntidiagonal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Nat.ne_zero_of_mem_divisorsAntidiagonal`：ne_zero_of_mem_divisorsAntidiag
onal {p : Nat × Nat} (hp : p in n.divisorsAntidiagonal) : p.1 != 0 ∧ p.2 != 0
-/
lemma right_ne_zero_of_mem_divisorsAntidiagonal {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) :
    p.2 ≠ 0 :=
  (ne_zero_of_mem_divisorsAntidiagonal hp).2
/-
**Nat.divisor_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisor_le {m : Nat} : n in divisors m -> n <= m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem divisor_le {m : ℕ} : n ∈ divisors m → n ≤ m := by
  rcases m with - | m
  · simp
  · simp only [mem_divisors, Nat.succ_ne_zero m, and_true, Ne, not_false_iff]
    exact Nat.le_of_dvd (Nat.succ_pos m)

@[gcongr]
/-
**Nat.divisors_subset_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisors_subset_of_dvd {m : Nat} (hzero : n != 0) (h : m ∣ n) : divisors m
 subseteq divisors n
参数：hzero : n != 0；h : m ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.subset_iff`：subset_iff {s₁ s₂ : Finset α} : s₁ subseteq s₂ ↔ fora
ll ⦃x⦄, x in s₁ -> x in s₂
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem divisors_subset_of_dvd {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) : divisors m ⊆ divisors n :=
  Finset.subset_iff.2 fun _x hx => Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hx).1.trans h, hzero⟩
/-
**Nat.card_divisors_le_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_divisors_le_self (n : Nat) : #n.divisors <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_Ico`：∀ (a b : ℕ), (Finset.Ico a b).card = b - a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem card_divisors_le_self (n : ℕ) : #n.divisors ≤ n := calc
  _ ≤ #(Ico 1 (n + 1)) := by
    apply card_le_card
    simp only [divisors, filter_subset]
  _ = n := by rw [card_Ico, add_tsub_cancel_right]
/-
**Nat.divisors_subset_properDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisors_subset_properDivisors {m : Nat} (hzero : n != 0) (h : m ∣ n) (hdi
ff : m != n) : divisors m subseteq properDivisors n
参数：hzero : n != 0；h : m ∣ n；hdiff : m != n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.subset_iff`：subset_iff {s₁ s₂ : Finset α} : s₁ subseteq s₂ ↔ fora
ll ⦃x⦄, x in s₁ -> x in s₂
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.divisor_le`：divisor_le {m : Nat} : n in divisors m -> n <= m
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
-/
theorem divisors_subset_properDivisors {m : ℕ} (hzero : n ≠ 0) (h : m ∣ n) (hdiff : m ≠ n) :
    divisors m ⊆ properDivisors n := by
  apply Finset.subset_iff.2
  intro x hx
  exact
    Nat.mem_properDivisors.2
      ⟨(Nat.mem_divisors.1 hx).1.trans h,
        lt_of_le_of_lt (divisor_le hx)
          (lt_of_le_of_ne (divisor_le (Nat.mem_divisors.2 ⟨h, hzero⟩)) hdiff)⟩
/-
**Nat.divisors_filter_dvd_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：divisors_filter_dvd_of_dvd {n m : Nat} (hn : n != 0) (hm : m ∣ n) : {d in 
n.divisors | d ∣ m} = m.divisors
参数：hn : n != 0；hm : m ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
-/
lemma divisors_filter_dvd_of_dvd {n m : ℕ} (hn : n ≠ 0) (hm : m ∣ n) :
    {d ∈ n.divisors | d ∣ m} = m.divisors := by
  ext k
  simp_rw [mem_filter, mem_divisors]
  exact ⟨fun ⟨_, hkm⟩ ↦ ⟨hkm, ne_zero_of_dvd_ne_zero hn hm⟩, fun ⟨hk, _⟩ ↦ ⟨⟨hk.trans hm, hn⟩, hk⟩⟩

@[simp]
/-
**Nat.divisors_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisors_zero : divisors 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem divisors_zero : divisors 0 = ∅ := by
  ext
  simp

@[simp]
/-
**Nat.properDivisors_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：properDivisors_zero : properDivisors 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem properDivisors_zero : properDivisors 0 = ∅ := by
  ext
  simp

@[simp]
/-
**Nat.nonempty_divisors** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nonempty_divisors : (divisors n).Nonempty ↔ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.divisors_zero`：divisors_zero : divisors 0 = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_mem_divisors`：one_mem_divisors : 1 in divisors n ↔ n != 0
-/
lemma nonempty_divisors : (divisors n).Nonempty ↔ n ≠ 0 :=
  ⟨fun ⟨m, hm⟩ hn ↦ by simp [hn] at hm, fun hn ↦ ⟨1, one_mem_divisors.2 hn⟩⟩

@[simp]
/-
**Nat.divisors_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：divisors_eq_empty : divisors n = ∅ ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.nonempty_divisors`：nonempty_divisors : (divisors n).Nonempty ↔ n != 
0
-/
lemma divisors_eq_empty : divisors n = ∅ ↔ n = 0 := by
  contrapose!
  exact nonempty_divisors
/-
**Nat.properDivisors_subset_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：properDivisors_subset_divisors : properDivisors n subseteq divisors n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_subset_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : Dec
idablePred p] {s t : Finset α}, s ⊆ t → Finset.filter p s ⊆ Finset.filter p t
· 使用定理 `Finset.Ico_subset_Ico_right`：Ico_subset_Ico_right (h : b₁ <= b₂) : Ico a
 b₁ subseteq Ico a b₂
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem properDivisors_subset_divisors : properDivisors n ⊆ divisors n :=
  filter_subset_filter _ <| Ico_subset_Ico_right n.le_succ

@[simp]
/-
**Nat.divisors_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisors_one : divisors 1 = {1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem divisors_one : divisors 1 = {1} := by
  ext
  simp

@[simp]
/-
**Nat.properDivisors_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：properDivisors_one : properDivisors 1 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.properDivisors.eq_1`：∀ (n : ℕ), n.properDivisors = {d ∈ Finset.Ico 1
 n | d ∣ n}
· 使用定理 `Finset.Ico_self`：Ico_self : Ico a a = ∅
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
-/
theorem properDivisors_one : properDivisors 1 = ∅ := by rw [properDivisors, Ico_self, filter_empty]
/-
**Nat.pos_of_mem_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pos_of_mem_divisors {m : Nat} (h : m in n.divisors) : 0 < m
参数：h : m in n.divisors。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem pos_of_mem_divisors {m : ℕ} (h : m ∈ n.divisors) : 0 < m := by
  cases m
  · rw [mem_divisors, zero_dvd_iff (a := n)] at h
    cases h.2 h.1
  apply Nat.succ_pos
/-
**Nat.pos_of_mem_properDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pos_of_mem_properDivisors {m : Nat} (h : m in n.properDivisors) : 0 < m
参数：h : m in n.properDivisors。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_mem_divisors`：pos_of_mem_divisors {m : Nat} (h : m in n.divis
ors) : 0 < m
· 使用定理 `Nat.properDivisors_subset_divisors`：properDivisors_subset_divisors : pro
perDivisors n subseteq divisors n
-/
theorem pos_of_mem_properDivisors {m : ℕ} (h : m ∈ n.properDivisors) : 0 < m :=
  pos_of_mem_divisors (properDivisors_subset_divisors h)
/-
**Nat.one_mem_properDivisors_iff_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：one_mem_properDivisors_iff_one_lt : 1 in n.properDivisors ↔ 1 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_mem_properDivisors_iff_one_lt : 1 ∈ n.properDivisors ↔ 1 < n := by
  rw [mem_properDivisors, and_iff_right (one_dvd _)]

@[simp]
/-
**Nat.sup_divisors_id** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sup_divisors_id (n : Nat) : n.divisors.sup id = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Nat.divisor_le`：divisor_le {m : Nat} : n in divisors m -> n <= m
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Nat.mem_divisors_self`：mem_divisors_self (n : Nat) (h : n != 0) : n in n
.divisors
-/
lemma sup_divisors_id (n : ℕ) : n.divisors.sup id = n := by
  refine le_antisymm (Finset.sup_le fun _ ↦ divisor_le) ?_
  rcases Decidable.eq_or_ne n 0 with rfl | hn
  · apply zero_le
  · exact Finset.le_sup (f := id) <| mem_divisors_self n hn
/-
**Nat.one_lt_of_mem_properDivisors** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：one_lt_of_mem_properDivisors {m n : Nat} (h : m in n.properDivisors) : 1 <
 n
参数：h : m in n.properDivisors。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.pos_of_mem_properDivisors`：pos_of_mem_properDivisors {m : Nat} (h : 
m in n.properDivisors) : 0 < m
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
-/
lemma one_lt_of_mem_properDivisors {m n : ℕ} (h : m ∈ n.properDivisors) : 1 < n :=
  lt_of_le_of_lt (pos_of_mem_properDivisors h) (mem_properDivisors.1 h).2
/-
**Nat.one_lt_div_of_mem_properDivisors** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：one_lt_div_of_mem_properDivisors {m n : Nat} (h : m in n.properDivisors) :
 1 < n / m
参数：h : m in n.properDivisors。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_div_iff_mul_lt'`：∀ {d n : ℕ}, d ∣ n → ∀ (a : ℕ), a < n / d ↔ d * 
a < n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma one_lt_div_of_mem_properDivisors {m n : ℕ} (h : m ∈ n.properDivisors) :
    1 < n / m := by
  obtain ⟨h_dvd, h_lt⟩ := mem_properDivisors.mp h
  rwa [Nat.lt_div_iff_mul_lt' h_dvd, mul_one]

/-- See also `Nat.mem_properDivisors`. -/
/-
**Nat.mem_properDivisors_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_properDivisors_iff_exists {m n : Nat} (hn : n != 0) : m in n.properDiv
isors ↔ exists k > 1, n = m * k
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.one_lt_div_of_mem_properDivisors`：one_lt_div_of_mem_properDivisors {
m n : Nat} (h : m in n.properDivisors) : 1 < n / m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_mul_of_one_lt_right`：lt_mul_of_one_lt_right [PosMulStrictMono α] (ha 
: 0 < a) (h : 1 < b) : a < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ

--- 原说明 ---
See also `Nat.mem_properDivisors`.
-/
lemma mem_properDivisors_iff_exists {m n : ℕ} (hn : n ≠ 0) :
    m ∈ n.properDivisors ↔ ∃ k > 1, n = m * k := by
  refine ⟨fun h ↦ ⟨n / m, one_lt_div_of_mem_properDivisors h, ?_⟩, ?_⟩
  · exact (Nat.mul_div_cancel' (mem_properDivisors.mp h).1).symm
  · rintro ⟨k, hk, rfl⟩
    rw [mul_ne_zero_iff] at hn
    exact mem_properDivisors.mpr ⟨⟨k, rfl⟩, lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hn.1) hk⟩

@[simp]
/-
**Nat.nonempty_properDivisors** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nonempty_properDivisors : n.properDivisors.Nonempty ↔ 1 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.one_lt_of_mem_properDivisors`：one_lt_of_mem_properDivisors {m n : Na
t} (h : m in n.properDivisors) : 1 < n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_mem_properDivisors_iff_one_lt`：one_mem_properDivisors_iff_one_lt
 : 1 in n.properDivisors ↔ 1 < n
-/
lemma nonempty_properDivisors : n.properDivisors.Nonempty ↔ 1 < n :=
  ⟨fun ⟨_m, hm⟩ ↦ one_lt_of_mem_properDivisors hm, fun hn ↦
    ⟨1, one_mem_properDivisors_iff_one_lt.2 hn⟩⟩

@[simp]
/-
**Nat.properDivisors_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：properDivisors_eq_empty : n.properDivisors = ∅ ↔ n <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.nonempty_properDivisors`：nonempty_properDivisors : n.properDivisors.
Nonempty ↔ 1 < n
-/
lemma properDivisors_eq_empty : n.properDivisors = ∅ ↔ n ≤ 1 := by
  contrapose!
  exact nonempty_properDivisors

@[simp]
/-
**Nat.divisorsAntidiagonal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisorsAntidiagonal_zero : divisorsAntidiagonal 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem divisorsAntidiagonal_zero : divisorsAntidiagonal 0 = ∅ := by
  ext
  simp

@[simp]
/-
**Nat.divisorsAntidiagonal_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisorsAntidiagonal_one : divisorsAntidiagonal 1 = {(1, 1)}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem divisorsAntidiagonal_one : divisorsAntidiagonal 1 = {(1, 1)} := by
  ext
  simp [mul_eq_one, Prod.ext_iff]

@[simp high]
/-
**Nat.swap_mem_divisorsAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：swap_mem_divisorsAntidiagonal {x : Nat × Nat} : x.swap in divisorsAntidiag
onal n ↔ x in divisorsAntidiagonal n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_divisorsAntidiagonal`：mem_divisorsAntidiagonal {x : Nat × Nat} :
 x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Prod.swap.eq_1`：∀ {α : Type u_1} {β : Type u_2} (p : α × β), p.swap = (p
.2, p.1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem swap_mem_divisorsAntidiagonal {x : ℕ × ℕ} :
    x.swap ∈ divisorsAntidiagonal n ↔ x ∈ divisorsAntidiagonal n := by
  rw [mem_divisorsAntidiagonal, mem_divisorsAntidiagonal, mul_comm, Prod.swap]
/-
**Nat.prodMk_mem_divisorsAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prodMk_mem_divisorsAntidiag {x y : Nat} (hn : n != 0) : (x, y) in n.diviso
rsAntidiagonal ↔ x * y = n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma prodMk_mem_divisorsAntidiag {x y : ℕ} (hn : n ≠ 0) :
    (x, y) ∈ n.divisorsAntidiagonal ↔ x * y = n := by simp [hn]
/-
**Nat.fst_mem_divisors_of_mem_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：fst_mem_divisors_of_mem_antidiagonal {x : Nat × Nat} (h : x in divisorsAnt
idiagonal n) : x.fst in divisors n
参数：h : x in divisorsAntidiagonal n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.mem_divisorsAntidiagonal`：mem_divisorsAntidiagonal {x : Nat × Nat} :
 x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem fst_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisorsAntidiagonal n) :
    x.fst ∈ divisors n := by
  rw [mem_divisorsAntidiagonal] at h
  simp [Dvd.intro _ h.1, h.2]
/-
**Nat.snd_mem_divisors_of_mem_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：snd_mem_divisors_of_mem_antidiagonal {x : Nat × Nat} (h : x in divisorsAnt
idiagonal n) : x.snd in divisors n
参数：h : x in divisorsAntidiagonal n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.mem_divisorsAntidiagonal`：mem_divisorsAntidiagonal {x : Nat × Nat} :
 x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem snd_mem_divisors_of_mem_antidiagonal {x : ℕ × ℕ} (h : x ∈ divisorsAntidiagonal n) :
    x.snd ∈ divisors n := by
  rw [mem_divisorsAntidiagonal] at h
  simp [Dvd.intro_left _ h.1, h.2]

@[simp]
/-
**Nat.map_swap_divisorsAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：map_swap_divisorsAntidiagonal : (divisorsAntidiagonal n).map (Equiv.prodCo
mm _ _).toEmbedding = divisorsAntidiagonal n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Equiv.coe_toEmbedding`：coe_toEmbedding : (f.toEmbedding : α -> β) = f
· 使用定理 `Equiv.coe_prodComm`：coe_prodComm (α β) : (⇑(prodComm α β) : α × β -> β ×
 α) = Prod.swap
· 使用定理 `Set.image_swap_eq_preimage_swap`：image_swap_eq_preimage_swap : image (@P
rod.swap α β) = preimage Prod.swap
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nat.swap_mem_divisorsAntidiagonal`：swap_mem_divisorsAntidiagonal {x : Na
t × Nat} : x.swap in divisorsAntidiagonal n ↔ x in divisorsAntidiagonal n
-/
theorem map_swap_divisorsAntidiagonal :
    (divisorsAntidiagonal n).map (Equiv.prodComm _ _).toEmbedding = divisorsAntidiagonal n := by
  rw [← coe_inj, coe_map, Equiv.coe_toEmbedding, Equiv.coe_prodComm,
    Set.image_swap_eq_preimage_swap]
  ext
  exact swap_mem_divisorsAntidiagonal

@[simp]
/-
**Nat.image_fst_divisorsAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_fst_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.fst =
 divisors n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
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
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_fst_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.fst = divisors n := by
  ext
  simp [Dvd.dvd, @eq_comm _ n (_ * _)]

@[simp]
/-
**Nat.image_snd_divisorsAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_snd_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.snd =
 divisors n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.map_swap_divisorsAntidiagonal`：map_swap_divisorsAntidiagonal : (divi
sorsAntidiagonal n).map (Equiv.prodComm _ _).toEmbedding = divisorsAntidiagonal 
n
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
· 使用定理 `Nat.image_fst_divisorsAntidiagonal`：image_fst_divisorsAntidiagonal : (di
visorsAntidiagonal n).image Prod.fst = divisors n
-/
theorem image_snd_divisorsAntidiagonal : (divisorsAntidiagonal n).image Prod.snd = divisors n := by
  rw [← map_swap_divisorsAntidiagonal, map_eq_image, image_image]
  exact image_fst_divisorsAntidiagonal

set_option backward.isDefEq.respectTransparency false in
/-
**Nat.map_div_right_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：map_div_right_divisors : n.divisors.map ⟨fun d => (d, n / d), fun _ _ => c
ongr_arg Prod.fst⟩ = n.divisorsAntidiagonal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem map_div_right_divisors :
    n.divisors.map ⟨fun d => (d, n / d), fun _ _ => congr_arg Prod.fst⟩ =
      n.divisorsAntidiagonal := by
  ext ⟨d, nd⟩
  simp only [mem_map, mem_divisorsAntidiagonal, Function.Embedding.coeFn_mk, mem_divisors,
    Prod.ext_iff, and_left_comm, exists_eq_left]
  constructor
  · rintro ⟨⟨⟨k, rfl⟩, hn⟩, rfl⟩
    rw [Nat.mul_div_cancel_left _ (left_ne_zero_of_mul hn).bot_lt]
    exact ⟨rfl, hn⟩
  · rintro ⟨rfl, hn⟩
    exact ⟨⟨dvd_mul_right _ _, hn⟩, Nat.mul_div_cancel_left _ (left_ne_zero_of_mul hn).bot_lt⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Nat.map_div_left_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：map_div_left_divisors : n.divisors.map ⟨fun d => (n / d, d), fun _ _ => co
ngr_arg Prod.snd⟩ = n.divisorsAntidiagonal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.map_injective`：map_injective (f : α ↪ β) : Injective (map f)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.map_swap_divisorsAntidiagonal`：map_swap_divisorsAntidiagonal : (divi
sorsAntidiagonal n).map (Equiv.prodComm _ _).toEmbedding = divisorsAntidiagonal 
n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.map_div_right_divisors`：map_div_right_divisors : n.divisors.map ⟨fun
 d => (d, n / d), fun _ _ => congr_arg Prod.fst⟩ = n.divisorsAntidiagonal
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_div_left_divisors :
    n.divisors.map ⟨fun d => (n / d, d), fun _ _ => congr_arg Prod.snd⟩ =
      n.divisorsAntidiagonal := by
  apply Finset.map_injective (Equiv.prodComm _ _).toEmbedding
  ext
  rw [map_swap_divisorsAntidiagonal, ← map_div_right_divisors, Finset.map_map]
  simp
/-
**Nat.sum_divisors_eq_sum_properDivisors_add_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat
`。
形式化陈述：sum_divisors_eq_sum_properDivisors_add_self : ∑ i in divisors n, i = (∑ i 
in properDivisors n, i) + n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.divisors_zero`：divisors_zero : divisors 0 = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.properDivisors_zero`：properDivisors_zero : properDivisors 0 = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `Nat.cons_self_properDivisors`：cons_self_properDivisors (h : n != 0) : co
ns n (properDivisors n) self_notMem_properDivisors = divisors n
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem sum_divisors_eq_sum_properDivisors_add_self :
    ∑ i ∈ divisors n, i = (∑ i ∈ properDivisors n, i) + n := by
  rcases Decidable.eq_or_ne n 0 with (rfl | hn)
  · simp
  · rw [← cons_self_properDivisors hn, Finset.sum_cons, add_comm]

/-- `n : ℕ` is perfect if and only the sum of the proper divisors of `n` is `n` and `n`
  is positive. -/
/-
**Nat.Perfect** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：Perfect (n : Nat) : Prop
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n : ℕ` is perfect if and only the sum of the proper divisors of `n` is `n` and 
`n`
  is positive.
-/
def Perfect (n : ℕ) : Prop :=
  ∑ i ∈ properDivisors n, i = n ∧ 0 < n
/-
**Nat.perfect_iff_sum_properDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：perfect_iff_sum_properDivisors (h : 0 < n) : Perfect n ↔ ∑ i in properDivi
sors n, i = n
参数：h : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
-/
theorem perfect_iff_sum_properDivisors (h : 0 < n) : Perfect n ↔ ∑ i ∈ properDivisors n, i = n :=
  and_iff_left h
/-
**Nat.perfect_iff_sum_divisors_eq_two_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：perfect_iff_sum_divisors_eq_two_mul (h : 0 < n) : Perfect n ↔ ∑ i in divis
ors n, i = 2 * n
参数：h : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.perfect_iff_sum_properDivisors`：perfect_iff_sum_properDivisors (h : 
0 < n) : Perfect n ↔ ∑ i in properDivisors n, i = n
· 使用定理 `Nat.sum_divisors_eq_sum_properDivisors_add_self`：sum_divisors_eq_sum_pro
perDivisors_add_self : ∑ i in divisors n, i = (∑ i in properDivisors n, i) + n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem perfect_iff_sum_divisors_eq_two_mul (h : 0 < n) :
    Perfect n ↔ ∑ i ∈ divisors n, i = 2 * n := by
  rw [perfect_iff_sum_properDivisors h, sum_divisors_eq_sum_properDivisors_add_self, two_mul]
  constructor <;> intro h
  · rw [h]
  · apply add_right_cancel h
/-
**Nat.mem_divisors_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_divisors_prime_pow {p : Nat} (pp : p.Prime) (k : Nat) {x : Nat} : x in
 divisors (p ^ k) ↔ exists j <= k, x = p ^ j
参数：pp : p.Prime；k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `Nat.dvd_prime_pow`：dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : 
i ∣ p ^ m ↔ exists k <= m, i = p ^ k
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) {x : ℕ} :
    x ∈ divisors (p ^ k) ↔ ∃ j ≤ k, x = p ^ j := by
  rw [mem_divisors, Nat.dvd_prime_pow pp, and_iff_left (ne_of_gt (pow_pos pp.pos k))]
/-
**Nat.Prime.divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p.divisors = {1, p}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Prime.divisors {p : ℕ} (pp : p.Prime) : divisors p = {1, p} := by
  ext
  rw [mem_divisors, dvd_prime pp, and_iff_left pp.ne_zero, Finset.mem_insert, Finset.mem_singleton]
/-
**Nat.Prime.properDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p.properDivisors = {1}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `Nat.insert_self_properDivisors`：insert_self_properDivisors (h : n != 0) 
: insert n (properDivisors n) = divisors n
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Nat.Prime.divisors`：∀ {p : ℕ}, Nat.Prime p → p.divisors = {1, p}
· 使用定理 `Finset.pair_comm`：pair_comm (a b : α) : ({a, b} : Finset α) = {b, a}
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem Prime.properDivisors {p : ℕ} (pp : p.Prime) : properDivisors p = {1} := by
  rw [← erase_insert self_notMem_properDivisors, insert_self_properDivisors pp.ne_zero,
    pp.divisors, pair_comm, erase_insert fun con => pp.ne_one (mem_singleton.1 con)]
/-
**Nat.divisors_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisors_prime_pow {p : Nat} (pp : p.Prime) (k : Nat) : divisors (p ^ k) =
 (Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_injective pp.two_le⟩
参数：pp : p.Prime；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_divisors_prime_pow`：mem_divisors_prime_pow {p : Nat} (pp : p.Pri
me) (k : Nat) {x : Nat} : x in divisors (p ^ k) ↔ exists j <= k, x = p ^ j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem divisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) :
    divisors (p ^ k) = (Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_injective pp.two_le⟩ := by
  ext a
  rw [mem_divisors_prime_pow pp]
  simp [eq_comm]
/-
**Nat.divisors_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisors_injective : Function.Injective divisors
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用引理 `Nat.sup_divisors_id`：sup_divisors_id (n : Nat) : n.divisors.sup id = n
-/
theorem divisors_injective : Function.Injective divisors :=
  Function.LeftInverse.injective sup_divisors_id

@[simp]
/-
**Nat.divisors_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisors_inj {a b : Nat} : a.divisors = b.divisors ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Nat.divisors_injective`：divisors_injective : Function.Injective divisors
-/
theorem divisors_inj {a b : ℕ} : a.divisors = b.divisors ↔ a = b :=
  divisors_injective.eq_iff
/-
**Nat.eq_properDivisors_of_subset_of_sum_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_properDivisors_of_subset_of_sum_eq_sum {s : Finset Nat} (hsub : s subse
teq n.properDivisors) : ((∑ x in s, x) = ∑ x in n.properDivisors, x) -> s = n.pr
operDivisors
参数：hsub : s subseteq n.properDivisors。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.subset_empty`：∀ {α : Type u_1} {s : Finset α}, s ⊆ ∅ ↔ s = ∅
· 使用定理 `Nat.properDivisors_zero`：properDivisors_zero : properDivisors 0 = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   s₁ ⊆ s₂ → ∑ x ∈ s₂
 \ s₁,…
· 使用定理 `Finset.Subset.antisymm`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₁ → s₁ = s₂
· 使用定理 `Finset.sdiff_eq_empty_iff_subset`：sdiff_eq_empty_iff_subset : s \ t = ∅ 
↔ s subseteq t
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.sum_lt_sum_of_nonempty`：∀ {ι : Type u_1} {M : Type u_4} [inst : A
ddCommMonoid M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M]   {f g : ι → 
M} {s : Finset ι} […
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
（共 34 条，此处仅展示前 30 条）
-/
theorem eq_properDivisors_of_subset_of_sum_eq_sum {s : Finset ℕ} (hsub : s ⊆ n.properDivisors) :
    ((∑ x ∈ s, x) = ∑ x ∈ n.properDivisors, x) → s = n.properDivisors := by
  cases n
  · rw [properDivisors_zero, subset_empty] at hsub
    simp [hsub]
  classical
    rw [← sum_sdiff hsub]
    intro h
    apply Subset.antisymm hsub
    rw [← sdiff_eq_empty_iff_subset]
    contrapose! h
    apply ne_of_lt
    rw [← zero_add (∑ x ∈ s, x), ← add_assoc, add_zero]
    gcongr
    have hlt :=
      sum_lt_sum_of_nonempty h fun x hx => pos_of_mem_properDivisors (sdiff_subset hx)
    simp only [sum_const_zero] at hlt
    apply hlt
/-
**Nat.sum_properDivisors_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_properDivisors_dvd (h : (∑ x in n.properDivisors, x) ∣ n) : ∑ x in n.p
roperDivisors, x = 1 ∨ ∑ x in n.properDivisors, x = n
参数：h : (∑ x in n.properDivisors, x) ∣ n。
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.properDivisors_zero`：properDivisors_zero : properDivisors 0 = ∅
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.properDivisors_one`：properDivisors_one : properDivisors 1 = ∅
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Nat.eq_properDivisors_of_subset_of_sum_eq_sum`：eq_properDivisors_of_subs
et_of_sum_eq_sum {s : Finset Nat} (hsub : s subseteq n.properDivisors) : ((∑ x i
n s, x) = ∑ x in n.properDivisors, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
-/
theorem sum_properDivisors_dvd (h : (∑ x ∈ n.properDivisors, x) ∣ n) :
    ∑ x ∈ n.properDivisors, x = 1 ∨ ∑ x ∈ n.properDivisors, x = n := by
  rcases n with - | n
  · simp
  · rcases n with - | n
    · simp at h
    · rw [or_iff_not_imp_right]
      intro ne_n
      have hlt : ∑ x ∈ n.succ.succ.properDivisors, x < n.succ.succ :=
        lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h) ne_n
      symm
      rw [← mem_singleton, eq_properDivisors_of_subset_of_sum_eq_sum (singleton_subset_iff.2
        (mem_properDivisors.2 ⟨h, hlt⟩)) (sum_singleton _ _), mem_properDivisors]
      exact ⟨one_dvd _, Nat.succ_lt_succ (Nat.succ_pos _)⟩

@[to_additive (attr := simp)]
/-
**Nat.Prime.prod_properDivisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoid α] {p : ℕ} {f : ℕ → α}, Nat.Prime p → 
∏ x ∈ p.properDivisors, f x = f 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.Prime.properDivisors`：∀ {p : ℕ}, Nat.Prime p → p.properDivisors = {1
}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Prime.prod_properDivisors {α : Type*} [CommMonoid α] {p : ℕ} {f : ℕ → α} (h : p.Prime) :
    ∏ x ∈ p.properDivisors, f x = f 1 := by simp [h.properDivisors]

@[to_additive (attr := simp)]
/-
**Nat.Prime.prod_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {α : Type u_1} [inst : CommMonoid α] {p : ℕ} {f : ℕ → α}, Nat.Prime p → 
∏ x ∈ p.divisors, f x = f p * f 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cons_self_properDivisors`：cons_self_properDivisors (h : n != 0) : co
ns n (properDivisors n) self_notMem_properDivisors = divisors n
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Nat.Prime.prod_properDivisors`：∀ {α : Type u_1} [inst : CommMonoid α] {p
 : ℕ} {f : ℕ → α}, Nat.Prime p → ∏ x ∈ p.properDivisors, f x = f 1
-/
theorem Prime.prod_divisors {α : Type*} [CommMonoid α] {p : ℕ} {f : ℕ → α} (h : p.Prime) :
    ∏ x ∈ p.divisors, f x = f p * f 1 := by
  rw [← cons_self_properDivisors h.ne_zero, prod_cons, h.prod_properDivisors]
/-
**Nat.properDivisors_eq_singleton_one_iff_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：properDivisors_eq_singleton_one_iff_prime : n.properDivisors = {1} ↔ n.Pri
me
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prime_def_lt`：prime_def_lt {p : Nat} : Prime p ↔ 2 <= p ∧ forall m <
 p, m ∣ p -> m = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.one_mem_properDivisors_iff_one_lt`：one_mem_properDivisors_iff_one_lt
 : 1 in n.properDivisors ↔ 1 < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `Nat.Prime.properDivisors`：∀ {p : ℕ}, Nat.Prime p → p.properDivisors = {1
}
-/
theorem properDivisors_eq_singleton_one_iff_prime : n.properDivisors = {1} ↔ n.Prime := by
  refine ⟨fun h ↦ ?_, Prime.properDivisors⟩
  rw [Nat.prime_def_lt]
  refine ⟨Nat.succ_le_iff.mpr <| one_mem_properDivisors_iff_one_lt.mp (by simp [h]), ?_⟩
  intro m hm hdvd
  simpa [h] using mem_properDivisors.mpr ⟨hdvd, hm⟩
/-
**Nat.sum_properDivisors_eq_one_iff_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_properDivisors_eq_one_iff_prime : ∑ x in n.properDivisors, x = 1 ↔ n.P
rime
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.properDivisors_zero`：properDivisors_zero : properDivisors 0 = ∅
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.properDivisors_one`：properDivisors_one : properDivisors 1 = ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.properDivisors_eq_singleton_one_iff_prime`：properDivisors_eq_singlet
on_one_iff_prime : n.properDivisors = {1} ↔ n.Prime
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.eq_properDivisors_of_subset_of_sum_eq_sum`：eq_properDivisors_of_subs
et_of_sum_eq_sum {s : Finset Nat} (hsub : s subseteq n.properDivisors) : ((∑ x i
n s, x) = ∑ x in n.properDivisors, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Nat.one_mem_properDivisors_iff_one_lt`：one_mem_properDivisors_iff_one_lt
 : 1 in n.properDivisors ↔ 1 < n
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
-/
theorem sum_properDivisors_eq_one_iff_prime : ∑ x ∈ n.properDivisors, x = 1 ↔ n.Prime := by
  rcases n with - | n
  · simp [Nat.not_prime_zero]
  · cases n
    · simp [Nat.not_prime_one]
    · rw [← properDivisors_eq_singleton_one_iff_prime]
      refine ⟨fun h => ?_, fun h => h.symm ▸ sum_singleton _ _⟩
      rw [@eq_comm (Finset ℕ) _ _]
      apply
        eq_properDivisors_of_subset_of_sum_eq_sum
          (singleton_subset_iff.2
            (one_mem_properDivisors_iff_one_lt.2 (succ_lt_succ (Nat.succ_pos _))))
          ((sum_singleton _ _).trans h.symm)
/-
**Nat.mem_properDivisors_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_properDivisors_prime_pow {p : Nat} (pp : p.Prime) (k : Nat) {x : Nat} 
: x in properDivisors (p ^ k) ↔ exists (j : Nat) (_ : j < k), x = p ^ j
参数：pp : p.Prime；k : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_properDivisors`：mem_properDivisors {m : Nat} : n in properDiviso
rs m ↔ n ∣ m ∧ n < m
· 使用定理 `Nat.dvd_prime_pow`：dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : 
i ∣ p ^ m ↔ exists k <= m, i = p ^ k
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pow_lt_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n < a ^ m ↔ n < m)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.pow_lt_pow_of_lt`：∀ {a n m : ℕ}, 1 < a → n < m → a ^ n < a ^ m
-/
theorem mem_properDivisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) {x : ℕ} :
    x ∈ properDivisors (p ^ k) ↔ ∃ (j : ℕ) (_ : j < k), x = p ^ j := by
  rw [mem_properDivisors, Nat.dvd_prime_pow pp]
  constructor
  · rintro ⟨⟨j, hjk, rfl⟩, hlt⟩
    exact ⟨j, (Nat.pow_lt_pow_iff_right pp.one_lt).mp hlt, rfl⟩
  · rintro ⟨j, hjk, rfl⟩
    exact ⟨⟨j, le_of_lt hjk, rfl⟩, Nat.pow_lt_pow_of_lt pp.one_lt hjk⟩
/-
**Nat.properDivisors_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：properDivisors_prime_pow {p : Nat} (pp : p.Prime) (k : Nat) : properDiviso
rs (p ^ k) = (Finset.range k).map ⟨(p ^ ·), Nat.pow_right_injective pp.two_le⟩
参数：pp : p.Prime；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_properDivisors_prime_pow`：mem_properDivisors_prime_pow {p : Nat}
 (pp : p.Prime) (k : Nat) {x : Nat} : x in properDivisors (p ^ k) ↔ exists (j : 
Nat) (_ : j < k), x = …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem properDivisors_prime_pow {p : ℕ} (pp : p.Prime) (k : ℕ) :
    properDivisors (p ^ k) = (Finset.range k).map ⟨(p ^ ·), Nat.pow_right_injective pp.two_le⟩ := by
  ext a
  simp [mem_properDivisors_prime_pow pp, eq_comm]

@[to_additive (attr := simp)]
/-
**Nat.prod_properDivisors_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_properDivisors_prime_pow {α : Type*} [CommMonoid α] {k p : Nat} {f : 
Nat -> α} (h : p.Prime) : (∏ x in (p ^ k).properDivisors, f x) = ∏ x in range k,
 f (p ^ x)
参数：h : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.properDivisors_prime_pow`：properDivisors_prime_pow {p : Nat} (pp : p
.Prime) (k : Nat) : properDivisors (p ^ k) = (Finset.range k).map ⟨(p ^ ·), Nat.
pow_right_injectiv…
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_properDivisors_prime_pow {α : Type*} [CommMonoid α] {k p : ℕ} {f : ℕ → α}
    (h : p.Prime) : (∏ x ∈ (p ^ k).properDivisors, f x) = ∏ x ∈ range k, f (p ^ x) := by
  simp [h, properDivisors_prime_pow]

@[to_additive (attr := simp) sum_divisors_prime_pow]
/-
**Nat.prod_divisors_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_divisors_prime_pow {α : Type*} [CommMonoid α] {k p : Nat} {f : Nat ->
 α} (h : p.Prime) : (∏ x in (p ^ k).divisors, f x) = ∏ x in range (k + 1), f (p 
^ x)
参数：h : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.divisors_prime_pow`：divisors_prime_pow {p : Nat} (pp : p.Prime) (k :
 Nat) : divisors (p ^ k) = (Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_in
jective pp.t…
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_divisors_prime_pow {α : Type*} [CommMonoid α] {k p : ℕ} {f : ℕ → α} (h : p.Prime) :
    (∏ x ∈ (p ^ k).divisors, f x) = ∏ x ∈ range (k + 1), f (p ^ x) := by
  simp [h, divisors_prime_pow]

@[to_additive]
/-
**Nat.prod_divisorsAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_divisorsAntidiagonal {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M)
 {n : Nat} : ∏ i in n.divisorsAntidiagonal, f i.1 i.2 = ∏ i in n.divisors, f i (
n / i)
参数：f : Nat -> Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.map_div_right_divisors`：map_div_right_divisors : n.divisors.map ⟨fun
 d => (d, n / d), fun _ _ => congr_arg Prod.fst⟩ = n.divisorsAntidiagonal
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
-/
theorem prod_divisorsAntidiagonal {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) {n : ℕ} :
    ∏ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∏ i ∈ n.divisors, f i (n / i) := by
  rw [← map_div_right_divisors, Finset.prod_map]
  rfl

@[to_additive]
/-
**Nat.prod_divisorsAntidiagonal'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_divisorsAntidiagonal' {M : Type*} [CommMonoid M] (f : Nat -> Nat -> M
) {n : Nat} : ∏ i in n.divisorsAntidiagonal, f i.1 i.2 = ∏ i in n.divisors, f (n
 / i) i
参数：f : Nat -> Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.map_swap_divisorsAntidiagonal`：map_swap_divisorsAntidiagonal : (divi
sorsAntidiagonal n).map (Equiv.prodComm _ _).toEmbedding = divisorsAntidiagonal 
n
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Nat.prod_divisorsAntidiagonal`：prod_divisorsAntidiagonal {M : Type*} [Co
mmMonoid M] (f : Nat -> Nat -> M) {n : Nat} : ∏ i in n.divisorsAntidiagonal, f i
.1 i.2 = ∏ i in n.d…
-/
theorem prod_divisorsAntidiagonal' {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) {n : ℕ} :
    ∏ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∏ i ∈ n.divisors, f (n / i) i := by
  rw [← map_swap_divisorsAntidiagonal, Finset.prod_map]
  exact prod_divisorsAntidiagonal fun i j => f j i

/-- The factors of `n` are the prime divisors -/
/-
**Nat.primeFactors_eq_to_filter_divisors_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactors_eq_to_filter_divisors_prime (n : Nat) : n.primeFactors = {p i
n divisors n | p.Prime}
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The factors of `n` are the prime divisors
-/
theorem primeFactors_eq_to_filter_divisors_prime (n : ℕ) :
    n.primeFactors = {p ∈ divisors n | p.Prime} := by
  grind
/-
**Nat.primeFactors_filter_dvd_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeFactors_filter_dvd_of_dvd {m n : Nat} (hn : n != 0) (hmn : m ∣ n) : {
p in n.primeFactors | p ∣ m} = m.primeFactors
参数：hn : n != 0；hmn : m ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Nat.primeFactors_eq_to_filter_divisors_prime`：primeFactors_eq_to_filter_
divisors_prime (n : Nat) : n.primeFactors = {p in divisors n | p.Prime}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_comm`：∀ {α : Type u_1} (p q : α → Prop) [inst : DecidableP
red p] [inst_1 : DecidablePred q] (s : Finset α),   Finset.filter q (Finset.filt
er p s) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Nat.divisors_filter_dvd_of_dvd`：divisors_filter_dvd_of_dvd {n m : Nat} (
hn : n != 0) (hm : m ∣ n) : {d in n.divisors | d ∣ m} = m.divisors
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma primeFactors_filter_dvd_of_dvd {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) :
    {p ∈ n.primeFactors | p ∣ m} = m.primeFactors := by
  simp_rw [primeFactors_eq_to_filter_divisors_prime, filter_comm,
    divisors_filter_dvd_of_dvd hn hmn]

@[simp]
/-
**Nat.image_div_divisors_eq_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：image_div_divisors_eq_divisors (n : Nat) : image (fun x : Nat => n / x) n.
divisors = n.divisors
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.image_fst_divisorsAntidiagonal`：image_fst_divisorsAntidiagonal : (di
visorsAntidiagonal n).image Prod.fst = divisors n
· 使用定理 `Nat.map_div_left_divisors`：map_div_left_divisors : n.divisors.map ⟨fun d
 => (n / d, d), fun _ _ => congr_arg Prod.snd⟩ = n.divisorsAntidiagonal
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.image_image`：image_image [DecidableEq γ] {g : β -> γ} : (s.image 
f).image g = s.image (g ∘ f)
-/
theorem image_div_divisors_eq_divisors (n : ℕ) :
    image (fun x : ℕ => n / x) n.divisors = n.divisors := by
  conv_rhs =>
    rw [← image_fst_divisorsAntidiagonal, ← map_div_left_divisors, map_eq_image, image_image]
  rfl

@[to_additive (attr := simp) sum_div_divisors]
/-
**Nat.prod_div_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_div_divisors {α : Type*} [CommMonoid α] (n : Nat) (f : Nat -> α) : (∏
 d in n.divisors, f (n / d)) = n.divisors.prod f
参数：n : Nat；f : Nat -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.divisors_zero`：divisors_zero : divisors 0 = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.div_eq_iff_eq_of_dvd_dvd`：∀ {n a b : ℕ}, n ≠ 0 → a ∣ n → b ∣ n → (n 
/ a = n / b ↔ a = b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Nat.image_div_divisors_eq_divisors`：image_div_divisors_eq_divisors (n : 
Nat) : image (fun x : Nat => n / x) n.divisors = n.divisors
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_div_divisors {α : Type*} [CommMonoid α] (n : ℕ) (f : ℕ → α) :
    (∏ d ∈ n.divisors, f (n / d)) = n.divisors.prod f := by
  by_cases hn : n = 0; · simp [hn]
  rw [← prod_image]
  · exact prod_congr (image_div_divisors_eq_divisors n) (by simp)
  · intro x hx y hy h
    rw [mem_coe, mem_divisors] at hx hy
    exact (div_eq_iff_eq_of_dvd_dvd hn hx.1 hy.1).mp h
/-
**Nat.disjoint_divisors_filter_isPrimePow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：disjoint_divisors_filter_isPrimePow {a b : Nat} (hab : a.Coprime b) : Disj
oint (a.divisors.filter IsPrimePow) (b.divisors.filter IsPrimePow)
参数：hab : a.Coprime b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimePow.ne_one`：IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n != 1
· 使用定理 `Nat.eq_one_of_dvd_coprimes`：eq_one_of_dvd_coprimes {a b k : Nat} (h_ab_c
oprime : Coprime a b) (hka : k ∣ a) (hkb : k ∣ b) : k = 1
-/
theorem disjoint_divisors_filter_isPrimePow {a b : ℕ} (hab : a.Coprime b) :
    Disjoint (a.divisors.filter IsPrimePow) (b.divisors.filter IsPrimePow) := by
  simp only [Finset.disjoint_left, Finset.mem_filter, and_imp, Nat.mem_divisors, not_and]
  rintro n han _ha hn hbn _hb -
  exact hn.ne_one (Nat.eq_one_of_dvd_coprimes hab han hbn)

/-- Useful lemma for reordering sums. -/
/-
**Nat.divisorsAntidiagonal_eq_prod_filter_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：divisorsAntidiagonal_eq_prod_filter_of_le {n N : Nat} (n_ne_zero : n != 0)
 (hn : n <= N) : n.divisorsAntidiagonal = (Ioc 0 N ×ˢ Ioc 0 N).filter (fun x => 
x.1 * x.2 = n)
参数：n_ne_zero : n != 0；hn : n <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_divisorsAntidiagonal`：mem_divisorsAntidiagonal {x : Nat × Nat} :
 x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Mathlib.Tactic.GCongr.and_mono`：and_mono (h₁ : a -> c) (h₂ : a -> b -> d
) : (a ∧ b) -> c ∧ d
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
Useful lemma for reordering sums.
-/
lemma divisorsAntidiagonal_eq_prod_filter_of_le {n N : ℕ} (n_ne_zero : n ≠ 0) (hn : n ≤ N) :
    n.divisorsAntidiagonal = (Ioc 0 N ×ˢ Ioc 0 N).filter (fun x ↦ x.1 * x.2 = n) := by
  ext ⟨n1, n2⟩
  rw [Nat.mem_divisorsAntidiagonal]
  simp only [ne_eq, Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc]
  constructor
  · intro ⟨rfl, hn2⟩
    grw [← hn]
    simp (disch := lia) only [le_mul_iff_one_le_right, le_mul_iff_one_le_left, and_true]
    lia
  · intro ⟨⟨hn1, hn2⟩, hn3⟩
    exact ⟨hn3, n_ne_zero⟩

/-- `Finset.antidiagonal k` embeds as a subset of `Nat.divisorsAntidiagonal (q ^ k)`. -/
/-
**Nat.antidiagonal_map_subset_divisorsAntidiagonal_pow** 是 Mathlib 中的一个定理，位于命名空间
 `Nat`。
形式化陈述：antidiagonal_map_subset_divisorsAntidiagonal_pow {q : Nat} (hq : 1 < q) (k
 : Nat) : letI ι : Nat ↪ Nat
参数：hq : 1 < q；k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
`Finset.antidiagonal k` embeds as a subset of `Nat.divisorsAntidiagonal (q ^ k)`
.
-/
theorem antidiagonal_map_subset_divisorsAntidiagonal_pow {q : ℕ} (hq : 1 < q) (k : ℕ) :
    letI ι : ℕ ↪ ℕ := ⟨fun k ↦ q ^ k, Nat.pow_right_injective hq⟩
    (Finset.antidiagonal k).map (.prodMap ι ι) ⊆ (q ^ k).divisorsAntidiagonal := by
  intro k hk
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
  simp [Nat.mem_divisorsAntidiagonal, ← Finset.mem_antidiagonal.mp hi, pow_add, ne_zero_of_lt hq]

end Nat

namespace Int
variable {xy : ℤ × ℤ} {x y z : ℤ}

-- Local notation for the embeddings `n ↦ n, n ↦ -n : ℕ → ℤ`
local notation "natCast" => Nat.castEmbedding (R := ℤ)
local notation "negNatCast" =>
  Function.Embedding.trans Nat.castEmbedding (Equiv.toEmbedding (Equiv.neg ℤ))

/-- `divisors z` is the `Finset` of divisors of `z`. By convention, we set `divisors 0 = ∅`. -/
/-
**Int.divisors** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：divisors (z : Int) : Finset Int
参数：z : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`divisors z` is the `Finset` of divisors of `z`. By convention, we set `divisors
 0 = ∅`.
-/
def divisors (z : ℤ) : Finset ℤ :=
  letI s := z.natAbs.divisors
  (s.map natCast).disjUnion (s.map negNatCast) <| by
    simp +contextual [s, disjoint_left, Eq.comm, forall_comm (β := _ = _)]

/-- Pairs of divisors of an integer as a finset.

`z.divisorsAntidiag` is the finset of pairs `(a, b) : ℤ × ℤ` such that `a * b = z`.
By convention, we set `Int.divisorsAntidiag 0 = ∅`.

O(|z|). Computed from `Nat.divisorsAntidiagonal`. -/
/-
**Int.divisorsAntidiag** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：divisorsAntidiag : (z : Int) -> Finset (Int × Int) | (n : Nat) => let s : 
Finset (Nat × Nat)
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pairs of divisors of an integer as a finset.

`z.divisorsAntidiag` is the finset of pairs `(a, b) : ℤ × ℤ` such that `a * b = 
z`.
By convention, we set `Int.divisorsAntidiag 0 = ∅`.

O(|z|). Computed from `Nat.divisorsAntidiagonal`.
-/
def divisorsAntidiag : (z : ℤ) → Finset (ℤ × ℤ)
  | (n : ℕ) =>
    let s : Finset (ℕ × ℕ) := n.divisorsAntidiagonal
    (s.map <| .prodMap natCast natCast).disjUnion (s.map <| .prodMap negNatCast negNatCast) <| by
      simp +contextual [s, disjoint_left, eq_comm]
  | negSucc n =>
    let s : Finset (ℕ × ℕ) := (n + 1).divisorsAntidiagonal
    (s.map <| .prodMap natCast negNatCast).disjUnion (s.map <| .prodMap negNatCast natCast) <| by
      simp +contextual [s, disjoint_left, eq_comm, forall_comm (α := _ * _ = _)]
/-
**Int.mem_divisors_iff_natAbs_mem_divisors_natAbs** 是 Mathlib 中的一个定理，位于命名空间 `Int
`。
形式化陈述：mem_divisors_iff_natAbs_mem_divisors_natAbs : x in z.divisors ↔ x.natAbs i
n z.natAbs.divisors
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.disjUnion_eq_union`：disjUnion_eq_union (s t h) : @disjUnion α s t
 h = s union t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.castEmbedding_apply`：∀ {R : Type u_2} [inst : AddMonoidWithOne R] [i
nst_1 : CharZero R] (a : ℕ), Nat.castEmbedding a = ↑a
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_eq_right`：∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∃ a, p a ∧ a
 = a') ↔ p a'
-/
theorem mem_divisors_iff_natAbs_mem_divisors_natAbs :
    x ∈ z.divisors ↔ x.natAbs ∈ z.natAbs.divisors := calc
  _ ↔ ∃ y ∈ z.natAbs.divisors, ↑y = x ∨ -↑y = x := by
    simp [← exists_or, ← and_or_left, divisors]
  _ ↔ ∃ y ∈ z.natAbs.divisors, y = x.natAbs := congr(∃ y ∈ _, $(by grind))
  _ ↔ x.natAbs ∈ z.natAbs.divisors := exists_eq_right

@[simp, grind =]
/-
**Int.mem_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：mem_divisors : x in divisors z ↔ x ∣ z ∧ z != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_divisors : x ∈ divisors z ↔ x ∣ z ∧ z ≠ 0 := by
  simp [mem_divisors_iff_natAbs_mem_divisors_natAbs]
/-
**Int.dvd_of_mem_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：dvd_of_mem_divisors (h : x in divisors z) : x ∣ z
参数：h : x in divisors z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.mem_divisors`：mem_divisors : x in divisors z ↔ x ∣ z ∧ z != 0
-/
theorem dvd_of_mem_divisors (h : x ∈ divisors z) : x ∣ z := (mem_divisors.mp h).1
/-
**Int.ne_zero_of_mem_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：ne_zero_of_mem_divisors (h : x in divisors z) : z != 0
参数：h : x in divisors z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.mem_divisors`：mem_divisors : x in divisors z ↔ x ∣ z ∧ z != 0
-/
theorem ne_zero_of_mem_divisors (h : x ∈ divisors z) : z ≠ 0 := (mem_divisors.mp h).2
/-
**Int.one_mem_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：one_mem_divisors : 1 in divisors z ↔ z != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_mem_divisors : 1 ∈ divisors z ↔ z ≠ 0 := by simp
/-
**Int.neg_one_mem_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：neg_one_mem_divisors : -1 in divisors z ↔ z != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neg_one_mem_divisors : -1 ∈ divisors z ↔ z ≠ 0 := by simp

@[simp]
/-
**Int.divisors_zero** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：divisors_zero : divisors 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma divisors_zero : divisors 0 = ∅ := by
  ext
  simp

@[simp]
/-
**Int.nonempty_divisors** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：nonempty_divisors : (divisors z).Nonempty ↔ z != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.divisors_zero`：divisors_zero : divisors 0 = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.one_mem_divisors`：one_mem_divisors : 1 in divisors z ↔ z != 0
-/
lemma nonempty_divisors : (divisors z).Nonempty ↔ z ≠ 0 :=
  ⟨fun ⟨z, hz⟩ hx ↦ by simp [hx] at hz, fun hx ↦ ⟨1, one_mem_divisors.mpr hx⟩⟩

@[simp]
/-
**Int.divisors_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：divisors_eq_empty : divisors z = ∅ ↔ z = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.nonempty_divisors`：nonempty_divisors : (divisors z).Nonempty ↔ z != 
0
-/
lemma divisors_eq_empty : divisors z = ∅ ↔ z = 0 := by
  contrapose!
  exact nonempty_divisors

@[simp]
/-
**Int.divisors_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：divisors_one : divisors 1 = {1, -1}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem divisors_one : divisors 1 = {1, -1} := rfl
/-
**Int.mem_divisors_self** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：mem_divisors_self (hz : z != 0) : z in divisors z
参数：hz : z != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.mem_divisors`：mem_divisors : x in divisors z ↔ x ∣ z ∧ z != 0
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
lemma mem_divisors_self (hz : z ≠ 0) : z ∈ divisors z :=
  mem_divisors.mpr ⟨dvd_rfl, hz⟩
/-
**Int.divisors_neg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {z : ℤ}, (-z).divisors = z.divisors
参数：-z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem divisors_neg : divisors (-z) = divisors z := by
  ext
  simp

@[simp]
/-
**Int.mem_divisorsAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：mem_divisorsAntidiag : xy in divisorsAntidiag z ↔ xy.fst * xy.snd = z ∧ z 
!= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.disjUnion_eq_union`：disjUnion_eq_union (s t h) : @disjUnion α s t
 h = s union t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.castEmbedding_apply`：∀ {R : Type u_2} [inst : AddMonoidWithOne R] [i
nst_1 : CharZero R] (a : ℕ), Nat.castEmbedding a = ↑a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
（共 31 条，此处仅展示前 30 条）
-/
lemma mem_divisorsAntidiag : xy ∈ divisorsAntidiag z ↔ xy.fst * xy.snd = z ∧ z ≠ 0 := by
  rcases z, xy with ⟨_ | _, ⟨_ | _, _ | _⟩⟩
  -- splitting this case saves about 1770 heartbeats i.e. 12.5% faster
  case ofNat.negSucc.negSucc =>
    simp [divisorsAntidiag]
    grind [Nat.cast_inj]
  all_goals
    simp [divisorsAntidiag]
    grind
/-
**Int.image_fst_divisorsAntidiag** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：image_fst_divisorsAntidiag : z.divisorsAntidiag.image Prod.fst = z.divisor
s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
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
theorem image_fst_divisorsAntidiag : z.divisorsAntidiag.image Prod.fst = z.divisors := by
  ext
  simp [Eq.comm, dvd_def]
/-
**Int.image_snd_divisorsAntidiag** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：image_snd_divisorsAntidiag : z.divisorsAntidiag.image Prod.snd = z.divisor
s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
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
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_snd_divisorsAntidiag : z.divisorsAntidiag.image Prod.snd = z.divisors := by
  ext
  simp [Eq.comm, mul_comm, dvd_def]
/-
**Int.divisorsAntidiag_zero** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：Int.divisorsAntidiag 0 = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma divisorsAntidiag_zero : divisorsAntidiag 0 = ∅ := rfl

-- TODO Write a simproc instead of `divisorsAntidiagonal_one`, ..., `divisorsAntidiagonal_four` ...

@[simp]
/-
**Int.divisorsAntidiagonal_one** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：divisorsAntidiagonal_one : Int.divisorsAntidiag 1 = {(1, 1), (-1, -1)}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem divisorsAntidiagonal_one :
    Int.divisorsAntidiag 1 = {(1, 1), (-1, -1)} :=
  rfl

@[simp]
/-
**Int.divisorsAntidiagonal_two** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：divisorsAntidiagonal_two : Int.divisorsAntidiag 2 = {(1, 2), (2, 1), (-1, 
-2), (-2, -1)}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem divisorsAntidiagonal_two :
    Int.divisorsAntidiag 2 = {(1, 2), (2, 1), (-1, -2), (-2, -1)} :=
  rfl

@[simp]
/-
**Int.divisorsAntidiagonal_three** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：divisorsAntidiagonal_three : Int.divisorsAntidiag 3 = {(1, 3), (3, 1), (-1
, -3), (-3, -1)}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem divisorsAntidiagonal_three :
    Int.divisorsAntidiag 3 = {(1, 3), (3, 1), (-1, -3), (-3, -1)} :=
  rfl

@[simp]
/-
**Int.divisorsAntidiagonal_four** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：divisorsAntidiagonal_four : Int.divisorsAntidiag 4 = {(1, 4), (2, 2), (4, 
1), (-1, -4), (-2, -2), (-4, -1)}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem divisorsAntidiagonal_four :
    Int.divisorsAntidiag 4 = {(1, 4), (2, 2), (4, 1), (-1, -4), (-2, -2), (-4, -1)} :=
  rfl
/-
**Int.prodMk_mem_divisorsAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：prodMk_mem_divisorsAntidiag (hz : z != 0) : (x, y) in z.divisorsAntidiag ↔
 x * y = z
参数：hz : z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma prodMk_mem_divisorsAntidiag (hz : z ≠ 0) : (x, y) ∈ z.divisorsAntidiag ↔ x * y = z := by
  simp [hz]

@[simp high]
/-
**Int.swap_mem_divisorsAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：swap_mem_divisorsAntidiag : xy.swap in z.divisorsAntidiag ↔ xy in z.diviso
rsAntidiag
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma swap_mem_divisorsAntidiag : xy.swap ∈ z.divisorsAntidiag ↔ xy ∈ z.divisorsAntidiag := by
  simp [mul_comm]
/-
**Int.neg_mem_divisorsAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：neg_mem_divisorsAntidiag : -xy in z.divisorsAntidiag ↔ xy in z.divisorsAnt
idiag
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma neg_mem_divisorsAntidiag : -xy ∈ z.divisorsAntidiag ↔ xy ∈ z.divisorsAntidiag := by simp

@[simp]
/-
**Int.map_prodComm_divisorsAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：map_prodComm_divisorsAntidiag : z.divisorsAntidiag.map (Equiv.prodComm _ _
).toEmbedding = z.divisorsAntidiag
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_prodComm_divisorsAntidiag :
    z.divisorsAntidiag.map (Equiv.prodComm _ _).toEmbedding = z.divisorsAntidiag := by
  ext; simp [mem_divisorsAntidiag]

@[simp]
/-
**Int.map_neg_divisorsAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：map_neg_divisorsAntidiag : z.divisorsAntidiag.map (Equiv.neg _).toEmbeddin
g = z.divisorsAntidiag
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_neg_divisorsAntidiag :
    z.divisorsAntidiag.map (Equiv.neg _).toEmbedding = z.divisorsAntidiag := by
  ext; simp [mem_divisorsAntidiag, mul_comm]
/-
**Int.divisorsAntidiag_neg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：divisorsAntidiag_neg : (-z).divisorsAntidiag = z.divisorsAntidiag.map (.pr
odMap (.refl _) (Equiv.neg _).toEmbedding)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `Function.Embedding.refl_apply`：∀ (α : Sort u_1) (a : α), (Function.Embed
ding.refl α) a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma divisorsAntidiag_neg :
    (-z).divisorsAntidiag =
      z.divisorsAntidiag.map (.prodMap (.refl _) (Equiv.neg _).toEmbedding) := by
  ext; simp [mem_divisorsAntidiag, Prod.ext_iff, neg_eq_iff_eq_neg]
/-
**Int.divisorsAntidiag_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：divisorsAntidiag_natCast (n : Nat) : divisorsAntidiag n = (n.divisorsAntid
iagonal.map <| .prodMap natCast natCast).disjUnion (n.divisorsAntidiagonal.map <
| .prodMap negNatCast negNatCast) (by simp +contextual [disjoint_left, eq_comm])
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma divisorsAntidiag_natCast (n : ℕ) :
    divisorsAntidiag n =
      (n.divisorsAntidiagonal.map <| .prodMap natCast natCast).disjUnion
        (n.divisorsAntidiagonal.map <| .prodMap negNatCast negNatCast) (by
          simp +contextual [disjoint_left, eq_comm]) := rfl
/-
**Int.divisorsAntidiag_neg_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：divisorsAntidiag_neg_natCast (n : Nat) : divisorsAntidiag (-n) = (n.diviso
rsAntidiagonal.map <| .prodMap natCast negNatCast).disjUnion (n.divisorsAntidiag
onal.map <| .prodMap negNatCast natCast) (by simp +contextual [disjoint_left, eq
_comm])
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma divisorsAntidiag_neg_natCast (n : ℕ) :
    divisorsAntidiag (-n) =
      (n.divisorsAntidiagonal.map <| .prodMap natCast negNatCast).disjUnion
        (n.divisorsAntidiagonal.map <| .prodMap negNatCast natCast) (by
          simp +contextual [disjoint_left, eq_comm]) := by cases n <;> rfl
/-
**Int.divisorsAntidiag_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：divisorsAntidiag_ofNat (n : Nat) : divisorsAntidiag ofNat(n) = (n.divisors
Antidiagonal.map <| .prodMap natCast natCast).disjUnion (n.divisorsAntidiagonal.
map <| .prodMap negNatCast negNatCast) (by simp +contextual [disjoint_left, eq_c
omm])
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma divisorsAntidiag_ofNat (n : ℕ) :
    divisorsAntidiag ofNat(n) =
      (n.divisorsAntidiagonal.map <| .prodMap natCast natCast).disjUnion
        (n.divisorsAntidiagonal.map <| .prodMap negNatCast negNatCast) (by
          simp +contextual [disjoint_left, eq_comm]) := rfl

/-- This lemma justifies its existence from its utility in crystallographic root system theory. -/
/-
**Int.mul_mem_one_two_three_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：mul_mem_one_two_three_iff {a b : Int} : a * b in ({1, 2, 3} : Set Int) ↔ (
a, b) in ({ (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1)
, (-1, -3), (-3, -1)} : Set (Int × Int))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False

--- 原说明 ---
This lemma justifies its existence from its utility in crystallographic root sys
tem theory.
-/
lemma mul_mem_one_two_three_iff {a b : ℤ} :
    a * b ∈ ({1, 2, 3} : Set ℤ) ↔ (a, b) ∈ ({
      (1, 1), (-1, -1),
      (1, 2), (2, 1), (-1, -2), (-2, -1),
      (1, 3), (3, 1), (-1, -3), (-3, -1)} : Set (ℤ × ℤ)) := by
  simp only [← Int.prodMk_mem_divisorsAntidiag, Set.mem_insert_iff, Set.mem_singleton_iff, ne_eq,
    one_ne_zero, not_false_eq_true, OfNat.ofNat_ne_zero]
  aesop

/-- This lemma justifies its existence from its utility in crystallographic root system theory. -/
/-
**Int.mul_mem_zero_one_two_three_four_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：mul_mem_zero_one_two_three_four_iff {a b : Int} (h₀ : a = 0 ↔ b = 0) : a *
 b in ({0, 1, 2, 3, 4} : Set Int) ↔ (a, b) in ({ (0, 0), (1, 1), (-1, -1), (1, 2
), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1), (-1, -3), (-3, -1), (4, 1), (1, 4
), (-4, -1), (-1, -4), (2, 2), (-2, -2)} : Set (Int × Int))
参数：h₀ : a = 0 ↔ b = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False

--- 原说明 ---
This lemma justifies its existence from its utility in crystallographic root sys
tem theory.
-/
lemma mul_mem_zero_one_two_three_four_iff {a b : ℤ} (h₀ : a = 0 ↔ b = 0) :
    a * b ∈ ({0, 1, 2, 3, 4} : Set ℤ) ↔ (a, b) ∈ ({
      (0, 0),
      (1, 1), (-1, -1),
      (1, 2), (2, 1), (-1, -2), (-2, -1),
      (1, 3), (3, 1), (-1, -3), (-3, -1),
      (4, 1), (1, 4), (-4, -1), (-1, -4), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  simp only [← Int.prodMk_mem_divisorsAntidiag, Set.mem_insert_iff, Set.mem_singleton_iff, ne_eq,
    one_ne_zero, not_false_eq_true, OfNat.ofNat_ne_zero]
  aesop

end Int

