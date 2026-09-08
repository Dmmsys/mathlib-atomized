/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Basic
public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Tactic.GCongr.Core

/-!
# Basic operations on the natural numbers

This file builds on `Mathlib/Data/Nat/Init.lean` by adding basic lemmas on natural numbers
depending on Mathlib definitions.

See note [foundational algebra order theory].
-/

public section

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

open Function

namespace Nat
variable {a b c d m n k : ℕ} {p : ℕ → Prop}

-- TODO: Move the `LinearOrder ℕ` instance to `Order.Nat` (https://github.com/leanprover-community/mathlib4/pull/13092).
/-
**Nat.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instLinearOrder : LinearOrder Nat where le
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `Nat.lt_iff_le_and_not_ge`：∀ {m n : ℕ}, m < n ↔ m ≤ n ∧ ¬n ≤ m
· 使用定理 `Nat.le_antisymm`：∀ {n m : ℕ}, n ≤ m → m ≤ n → n = m
· 使用定理 `Nat.le_total`：∀ (m n : ℕ), m ≤ n ∨ n ≤ m
-/
instance instLinearOrder : LinearOrder ℕ where
  le := Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_ge := @Nat.lt_iff_le_and_not_ge
  toDecidableLT := inferInstance
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance

-- Shortcut instances
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder ℕ := inferInstance
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder ℕ := inferInstance
/-
**Nat.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instNontrivial : Nontrivial Nat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_ne_one`：0 ≠ 1
-/
instance instNontrivial : Nontrivial ℕ := ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

attribute [gcongr] Nat.succ_le_succ Nat.div_le_div_right Nat.div_le_div

/-! ### `succ`, `pred` -/

/-
**Nat.succ_injective** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：succ_injective : Injective Nat.succ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ.inj`：∀ {m n : ℕ}, m.succ = n.succ → m = n

--- 原说明 ---
### `succ`, `pred`
-/
lemma succ_injective : Injective Nat.succ := @succ.inj

/-! ### `div` -/

/-
**Nat.div_right_comm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (a b c : ℕ), a / b / c = a / c / b
参数：a b c : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_div_eq_div_mul`：∀ (m n k : ℕ), m / n / k = m / (n * k)
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
### `div`
-/
protected theorem div_right_comm (a b c : ℕ) : a / b / c = a / c / b := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

/-!
### `pow`
-/

/-
**Nat.pow_left_injective** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_left_injective (hn : n != 0) : Injective (fun a : Nat => a ^ n)
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_le_pow_iff_left`：∀ {a b n : ℕ}, n ≠ 0 → (a ^ n ≤ b ^ n ↔ a ≤ b)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
### `pow`
-/
lemma pow_left_injective (hn : n ≠ 0) : Injective (fun a : ℕ ↦ a ^ n) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_left hn]
/-
**Nat.pow_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => a ^ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_le_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n ≤ a ^ m ↔ n ≤ m)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma pow_right_injective (ha : 2 ≤ a) : Injective (a ^ ·) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_right ha]
/-
**Nat.pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {x a : ℕ}, x ≠ 0 → a ≠ 0 → x ^ (a - 1) = x ^ a / x
参数：a - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pow_div`：∀ {x m n : ℕ}, n ≤ m → 0 < x → x ^ m / x ^ n = x ^ (m - n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Nat.pow_one`：∀ (a : ℕ), a ^ 1 = a
-/
protected theorem pow_sub_one {x a : ℕ} (hx : x ≠ 0) (ha : a ≠ 0) :
    x ^ (a - 1) = x ^ a / x := by
  rw [← Nat.pow_div (one_le_iff_ne_zero.mpr ha) (Nat.pos_iff_ne_zero.mpr hx), Nat.pow_one]

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

/-
**Nat.leRecOn_injective** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRecOn_injective {C : Nat -> Sort*} {n m} (hnm : n <= m) (next : forall {
k}, C k -> C (k + 1)) (Hnext : forall n, Injective (@next n)) : Injective (@leRe
cOn C n m hnm next)
参数：hnm : n <= m；next : forall {k}, C k -> C (k + 1)；Hnext : forall n, Injective 
(@next n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.leRecOn_self`：leRecOn_self {C : Nat -> Sort*} {n} {next : forall {k}
, C k -> C (k + 1)} (x : C n) : (leRecOn n.le_refl next x : C n) = x
· 使用引理 `Nat.leRecOn_succ`：leRecOn_succ {C : Nat -> Sort*} {n m} (h1 : n <= m) {h
2 : n <= m + 1} {next} (x : C n) : (leRecOn h2 next x : C (m + 1)) = next (leRec
On h1 …

--- 原说明 ---
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the 
lemmas
proved above, and some of the results in later sections depend on the definition
s in this section.
-/
lemma leRecOn_injective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Injective (@next n)) : Injective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x y H
    rwa [leRecOn_self, leRecOn_self] at H
  | step hnm ih =>
    intro x y H
    rw [leRecOn_succ hnm, leRecOn_succ hnm] at H
    exact ih (Hnext _ H)
/-
**Nat.leRecOn_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：leRecOn_surjective {C : Nat -> Sort*} {n m} (hnm : n <= m) (next : forall 
{k}, C k -> C (k + 1)) (Hnext : forall n, Surjective (@next n)) : Surjective (@l
eRecOn C n m hnm next)
参数：hnm : n <= m；next : forall {k}, C k -> C (k + 1)；Hnext : forall n, Surjective
 (@next n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用引理 `Nat.leRecOn_self`：leRecOn_self {C : Nat -> Sort*} {n} {next : forall {k}
, C k -> C (k + 1)} (x : C n) : (leRecOn n.le_refl next x : C n) = x
· 使用引理 `Nat.leRecOn_succ`：leRecOn_succ {C : Nat -> Sort*} {n m} (h1 : n <= m) {h
2 : n <= m + 1} {next} (x : C n) : (leRecOn h2 next x : C (m + 1)) = next (leRec
On h1 …
-/
lemma leRecOn_surjective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Surjective (@next n)) : Surjective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x
    refine ⟨x, ?_⟩
    rw [leRecOn_self]
  | step hnm ih =>
    intro x
    obtain ⟨w, rfl⟩ := Hnext _ x
    obtain ⟨x, rfl⟩ := ih w
    refine ⟨x, ?_⟩
    rw [leRecOn_succ]


/-- A subset of `ℕ` containing `k : ℕ` and closed under `Nat.succ` contains every `n ≥ k`. -/
/-
**Nat.set_induction_bounded** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：set_induction_bounded {S : Set Nat} (hk : k in S) (h_ind : forall k : Nat,
 k in S -> k + 1 in S) (hnk : k <= n) : n in S
参数：hk : k in S；h_ind : forall k : Nat, k in S -> k + 1 in S；hnk : k <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of `ℕ` containing `k : ℕ` and closed under `Nat.succ` contains every `n
 ≥ k`.
-/
lemma set_induction_bounded {S : Set ℕ} (hk : k ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S)
    (hnk : k ≤ n) : n ∈ S :=
  @leRecOn (fun n => n ∈ S) k n hnk @h_ind hk

/-- A subset of `ℕ` containing zero and closed under `Nat.succ` contains all of `ℕ`. -/
/-
**Nat.set_induction** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：set_induction {S : Set Nat} (hb : 0 in S) (h_ind : forall k : Nat, k in S 
-> k + 1 in S) (n : Nat) : n in S
参数：hb : 0 in S；h_ind : forall k : Nat, k in S -> k + 1 in S；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.set_induction_bounded`：set_induction_bounded {S : Set Nat} (hk : k i
n S) (h_ind : forall k : Nat, k in S -> k + 1 in S) (hnk : k <= n) : n in S
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n

--- 原说明 ---
A subset of `ℕ` containing zero and closed under `Nat.succ` contains all of `ℕ`.
-/
lemma set_induction {S : Set ℕ} (hb : 0 ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S) (n : ℕ) :
    n ∈ S :=
  set_induction_bounded hb h_ind (zero_le n)

/-! ### `mod`, `dvd` -/

/-- `dvd` is injective in the left argument -/
/-
**Nat.dvd_left_injective** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：dvd_left_injective : Function.Injective ((· ∣ ·) : Nat -> Nat -> Prop)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.dvd_right_iff_eq`：dvd_right_iff_eq : (forall a : Nat, m ∣ a ↔ n ∣ a)
 ↔ m = n
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
`dvd` is injective in the left argument
-/
lemma dvd_left_injective : Function.Injective ((· ∣ ·) : ℕ → ℕ → Prop) := fun _ _ h =>
  dvd_right_iff_eq.mp fun a => iff_of_eq (congr_fun h a)

@[simp]
/-
**Nat.dvd_sub_self_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n m : ℕ}, n ∣ n - m ↔ m = 0 ∨ n ≤ m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Nat.not_dvd_of_pos_of_lt`：∀ {n m : ℕ}, 0 < n → n < m → ¬m ∣ n
-/
protected lemma dvd_sub_self_left {n m : ℕ} :
    n ∣ n - m ↔ m = 0 ∨ n ≤ m := by
  rcases le_or_gt n m with h | h
  · simp [h]
  · rcases eq_or_ne m 0 with rfl | hm
    · simp
    · simp only [hm, h.not_ge, or_self, iff_false]
      refine not_dvd_of_pos_of_lt ?_ ?_ <;>
      grind

@[simp]
/-
**Nat.dvd_sub_self_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n m : ℕ}, n ∣ m - n ↔ n ∣ m ∨ m ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.dvd_sub_iff_left`：∀ {m n k : ℕ}, k ≤ n → m ∣ k → (m ∣ n - k ↔ m ∣ n)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.dvd_refl`：∀ (a : ℕ), a ∣ a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
protected lemma dvd_sub_self_right {n m : ℕ} :
    n ∣ m - n ↔ n ∣ m ∨ m ≤ n := by
  rcases le_or_gt m n with h | h
  · simp [h]
  · simp [dvd_sub_iff_left (le_of_lt h) (Nat.dvd_refl _), h.not_ge]

/-! ### Miscellaneous -/

/-
**Nat.mul_le_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mul_le_pow {a : Nat} (ha : a != 1) (b : Nat) : a * b <= a ^ b
参数：ha : a != 1；b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `Nat.lt_of_le_of_ne`：∀ {n m : ℕ}, n ≤ m → ¬n = m → n < m
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n

--- 原说明 ---
### Miscellaneous
-/
lemma mul_le_pow {a : ℕ} (ha : a ≠ 1) (b : ℕ) :
    a * b ≤ a ^ b := by
  cases b with
  | zero => exact Nat.zero_le _
  | succ b =>
      obtain rfl | ha0 : a = 0 ∨ a > 0 := a.eq_zero_or_pos
      · rw [Nat.zero_mul]; exact Nat.zero_le _
      · have ha1 : a > 1 := Nat.lt_of_le_of_ne ha0 ha.symm
        rw [Nat.pow_succ']; exact Nat.mul_le_mul_left a (Nat.lt_pow_self ha1)
/-
**Nat.two_mul_sq_add_one_le_two_pow_two_mul** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_mul_sq_add_one_le_two_pow_two_mul (k : Nat) : 2 * k ^ 2 + 1 <= 2 ^ (2 
* k)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `Nat.two_pos`：0 < 2
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用定理 `Nat.lt_add_of_pos_left`：∀ {k n : ℕ}, 0 < k → n < k + n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_pow`：∀ (a b n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Nat.add_mul`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
· 使用定理 `Nat.pow_le_pow_left`：∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
· 使用引理 `Nat.mul_le_pow`：mul_le_pow {a : Nat} (ha : a != 1) (b : Nat) : a * b <= 
a ^ b
· 使用定理 `Nat.pow_mul'`：∀ (a m n : ℕ), a ^ (m * n) = (a ^ n) ^ m
-/
lemma two_mul_sq_add_one_le_two_pow_two_mul (k : ℕ) : 2 * k ^ 2 + 1 ≤ 2 ^ (2 * k) := by
  obtain rfl | hk : k = 0 ∨ k > 0 := k.eq_zero_or_pos
  · decide
  · have hk0 : 0 < 2 * k ^ 2 := Nat.mul_pos Nat.two_pos (Nat.pow_pos hk)
    calc 2 * k ^ 2
      _ < 2 * k ^ 2 + 2 * k ^ 2 := Nat.lt_add_of_pos_left hk0
      _ = (2 * k) ^ 2 := by rw [Nat.mul_pow, ← Nat.add_mul]
      _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_pow (by decide : 2 ≠ 1) _) 2
      _ = 2 ^ (2 * k) := (Nat.pow_mul' _ _ _).symm

end Nat

