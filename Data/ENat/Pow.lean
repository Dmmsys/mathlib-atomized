/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Data.ENat.Basic

/-!
# Powers of extended natural numbers

We define the power of an extended natural `x : ℕ∞` by another extended natural `y : ℕ∞`. The
definition is chosen such that `x ^ y` is the cardinality of `α → β`, when `β` has cardinality `x`
and `α` has cardinality `y`:

* When `y` is finite, it coincides with the exponentiation by natural numbers (e.g. `⊤ ^ 0 = 1`).
* We set `0 ^ ⊤ = 0`, `1 ^ ⊤ = 1` and `x ^ ⊤ = ⊤` for `x > 1`.

## Naming convention

The quantity `x ^ y` for `x`, `y : ℕ∞` is defined as a `Pow` instance. It is called `epow` in
lemmas' names.
-/

@[expose] public section

namespace ENat

variable {x y z : ℕ∞}

/-
**ENat.** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow ℕ∞ ℕ∞ where
  pow
    | x, some y => x ^ y
    | x, ⊤ => if x = 0 then 0 else if x = 1 then 1 else ⊤
/-
**ENat.epow_def** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_def {x y : Nat∞} : x ^ y = if y < ⊤ then x ^ y.toNat else if x = 0 th
en 0 else if x = 1 then 1 else ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
-/
lemma epow_def {x y : ℕ∞} :
    x ^ y = if y < ⊤ then x ^ y.toNat else if x = 0 then 0 else if x = 1 then 1 else ⊤ := by
  cases y with
  | top => simp only [lt_self_iff_false, ↓reduceIte]; rfl
  | coe n => simp only [natCast_lt_top, ↓reduceIte, toNat_natCast]; rfl

@[simp, norm_cast]
/-
**ENat.epow_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_natCast {y : Nat} : x ^ (y : Nat∞) = x ^ y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma epow_natCast {y : ℕ} : x ^ (y : ℕ∞) = x ^ y := rfl

@[simp]
/-
**ENat.zero_epow_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：zero_epow_top : (0 : Nat∞) ^ (⊤ : Nat∞) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_epow_top : (0 : ℕ∞) ^ (⊤ : ℕ∞) = 0 := rfl
/-
**ENat.zero_epow** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：zero_epow (h : y != 0) : (0 : Nat∞) ^ y = 0
参数：h : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.zero_epow_top`：zero_epow_top : (0 : Nat∞) ^ (⊤ : Nat∞) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.epow_natCast`：epow_natCast {y : Nat} : x ^ (y : Nat∞) = x ^ y
· 使用定理 `pow_eq_zero_iff'`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} 
{n : ℕ} [IsReduced M₀] [Nontrivial M₀], a ^ n = 0 ↔ a = 0 ∧ n ≠ 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `instNoZeroDivisorsENat`：NoZeroDivisors ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma zero_epow (h : y ≠ 0) : (0 : ℕ∞) ^ y = 0 := by
  induction y with
  | top => exact zero_epow_top
  | coe y => rwa [epow_natCast, pow_eq_zero_iff', eq_self 0, true_and, ← y.cast_ne_zero (R := ℕ∞)]

@[simp]
/-
**ENat.one_epow** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：one_epow : (1 : Nat∞) ^ y = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.epow_natCast`：epow_natCast {y : Nat} : x ^ (y : Nat∞) = x ^ y
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
lemma one_epow : (1 : ℕ∞) ^ y = 1 := by
  induction y with
  | top => rfl
  | coe y => rw [epow_natCast, one_pow]

@[simp]
/-
**ENat.top_epow_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：top_epow_top : (⊤ : Nat∞) ^ (⊤ : Nat∞) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma top_epow_top : (⊤ : ℕ∞) ^ (⊤ : ℕ∞) = ⊤ := rfl
/-
**ENat.top_epow** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：top_epow (h : y != 0) : (⊤ : Nat∞) ^ y = ⊤
参数：h : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.top_epow_top`：top_epow_top : (⊤ : Nat∞) ^ (⊤ : Nat∞) = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.epow_natCast`：epow_natCast {y : Nat} : x ^ (y : Nat∞) = x ^ y
· 使用定理 `ENat.pow_eq_top_iff`：∀ {a : ℕ∞} {n : ℕ}, a ^ n = ⊤ ↔ a = ⊤ ∧ n ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma top_epow (h : y ≠ 0) : (⊤ : ℕ∞) ^ y = ⊤ := by
  induction y with
  | top => exact top_epow_top
  | coe y => rwa [epow_natCast, pow_eq_top_iff, eq_self ⊤, true_and, ← y.cast_ne_zero (R := ℕ∞)]

@[simp]
/-
**ENat.epow_zero** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_zero : x ^ (0 : Nat∞) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_zero`：natCast_zero : ((0 : Nat) : Nat∞) = 0
· 使用引理 `ENat.epow_natCast`：epow_natCast {y : Nat} : x ^ (y : Nat∞) = x ^ y
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
lemma epow_zero : x ^ (0 : ℕ∞) = 1 := by
  rw [← natCast_zero, epow_natCast, pow_zero]

@[simp]
/-
**ENat.epow_one** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_one : x ^ (1 : Nat∞) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_one`：natCast_one : ((1 : Nat) : Nat∞) = 1
· 使用引理 `ENat.epow_natCast`：epow_natCast {y : Nat} : x ^ (y : Nat∞) = x ^ y
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma epow_one : x ^ (1 : ℕ∞) = x := by
  rw [← natCast_one, epow_natCast, pow_one]
/-
**ENat.epow_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_top (h : 1 < x) : x ^ (⊤ : Nat∞) = ⊤
参数：h : 1 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.epow_def`：epow_def {x y : Nat∞} : x ^ y = if y < ⊤ then x ^ y.toNat
 else if x = 0 then 0 else if x = 1 then 1 else ⊤
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma epow_top (h : 1 < x) : x ^ (⊤ : ℕ∞) = ⊤ := by
  have : (0 : ℕ∞) ≤ 1 := zero_le_one
  rw [epow_def, if_neg, if_neg, if_neg] <;> grind
/-
**ENat.epow_right_mono** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_right_mono (h : x != 0) : Monotone (fun y : Nat∞ => x ^ y)
参数：h : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ENat.one_epow`：one_epow : (1 : Nat∞) ^ y = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.epow_top`：epow_top (h : 1 < x) : x ^ (⊤ : Nat∞) = ⊤
· 使用引理 `pow_right_mono₀`：pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h 
: 1 <= a) : Monotone (a ^ ·)
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma epow_right_mono (h : x ≠ 0) : Monotone (fun y : ℕ∞ ↦ x ^ y) := by
  intro y z y_z
  induction y
  · rw [top_le_iff.1 y_z]
  induction z
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · exact (h (Order.lt_one_iff.1 x_0)).rec
    · simp only [one_epow, le_refl]
    · simp only [epow_top x_2, le_top]
  · exact pow_right_mono₀ (Order.one_le_iff_ne_zero.2 h) (Nat.cast_le.1 y_z)
/-
**ENat.one_le_epow** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：one_le_epow (h : x != 0) : 1 <= x ^ y
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.epow_zero`：epow_zero : x ^ (0 : Nat∞) = 1
· 使用引理 `ENat.epow_right_mono`：epow_right_mono (h : x != 0) : Monotone (fun y : N
at∞ => x ^ y)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
lemma one_le_epow (h : x ≠ 0) : 1 ≤ x ^ y := by
  simpa using epow_right_mono h zero_le
/-
**ENat.epow_pos** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_pos (h : x != 0) : 0 < x ^ y
参数：h : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用引理 `ENat.one_le_epow`：one_le_epow (h : x != 0) : 1 <= x ^ y
-/
lemma epow_pos (h : x ≠ 0) : 0 < x ^ y := by
  rw [← Order.one_le_iff_pos]; exact one_le_epow h
/-
**ENat.epow_left_mono** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_left_mono : Monotone (fun x : Nat∞ => x ^ y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用引理 `ENat.zero_epow_top`：zero_epow_top : (0 : Nat∞) ^ (⊤ : Nat∞) = 0
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用引理 `ENat.one_epow`：one_epow : (1 : Nat∞) ^ y = 1
· 使用引理 `ENat.one_le_epow`：one_le_epow (h : x != 0) : 1 <= x ^ y
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.epow_top`：epow_top (h : 1 < x) : x ^ (⊤ : Nat∞) = ⊤
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pow_left_mono`：pow_left_mono (n : Nat) : Monotone fun a : M => a ^ n
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
-/
lemma epow_left_mono : Monotone (fun x : ℕ∞ ↦ x ^ y) := by
  intro x z x_z
  simp only
  induction y
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · rw [Order.lt_one_iff.1 x_0, zero_epow_top]; exact bot_le
    · rw [one_epow]; exact one_le_epow (Order.one_le_iff_ne_zero.1 x_z)
    · rw [epow_top (x_2.trans_le x_z)]; exact le_top
  · simp only [epow_natCast, (pow_left_mono _) x_z]
/-
**ENat.epow_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_eq_zero_iff : x ^ y = 0 ↔ x = 0 ∧ y != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `ENat.epow_pos`：epow_pos (h : x != 0) : 0 < x ^ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.epow_zero`：epow_zero : x ^ (0 : Nat∞) = 1
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用引理 `ENat.zero_epow`：zero_epow (h : y != 0) : (0 : Nat∞) ^ y = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma epow_eq_zero_iff : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  refine ⟨fun h ↦ ⟨?_, fun y_0 ↦ ?_⟩, fun h ↦ h.1.symm ▸ zero_epow h.2⟩
  · contrapose! h
    exact (epow_pos h).ne'
  · rw [y_0, epow_zero] at h; contradiction
/-
**ENat.epow_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_eq_one_iff : x ^ y = 1 ↔ x = 1 ∨ y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENat.zero_epow`：zero_epow (h : y != 0) : (0 : Nat∞) ^ y = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.epow_right_mono`：epow_right_mono (h : x != 0) : Monotone (fun y : N
at∞ => x ^ y)
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ENat.epow_one`：epow_one : x ^ (1 : Nat∞) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENat.one_epow`：one_epow : (1 : Nat∞) ^ y = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ENat.epow_zero`：epow_zero : x ^ (0 : Nat∞) = 1
-/
lemma epow_eq_one_iff : x ^ y = 1 ↔ x = 1 ∨ y = 0 := by
  refine ⟨fun h ↦ or_iff_not_imp_right.2 fun y_0 ↦ ?_, fun h ↦ by rcases h with h | h <;> simp [h]⟩
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0, zero_epow y_0] at h; contradiction
  · rfl
  · have := epow_right_mono x_2.ne_zero (Order.one_le_iff_ne_zero.2 y_0)
    simp only [epow_one, h] at this
    exact (not_lt_of_ge this x_2).rec
/-
**ENat.epow_add** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_add : x ^ (y + z) = x ^ y * x ^ z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENat.epow_zero`：epow_zero : x ^ (0 : Nat∞) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.zero_epow`：zero_epow (h : y != 0) : (0 : Nat∞) ^ y = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用引理 `ENat.one_epow`：one_epow : (1 : Nat∞) ^ y = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用引理 `ENat.epow_top`：epow_top (h : 1 < x) : x ^ (⊤ : Nat∞) = ⊤
（共 37 条，此处仅展示前 30 条）
-/
lemma epow_add : x ^ (y + z) = x ^ y * x ^ z := by
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0]
    rcases eq_zero_or_pos y with rfl | y_0
    · simp only [zero_add, epow_zero, one_mul]
    · rw [zero_epow y_0.ne.symm, zero_mul]
      exact zero_epow (add_pos_of_pos_of_nonneg y_0 bot_le).ne.symm
  · simp only [one_epow, mul_one]
  · induction y
    · rw [top_add, epow_top x_2, top_mul]
      exact (epow_pos x_2.ne_zero).ne'
    induction z
    · rw [add_top, epow_top x_2, mul_top]
      exact (epow_pos x_2.ne_zero).ne'
    simp only [← Nat.cast_add, epow_natCast, pow_add x]
/-
**ENat.mul_epow** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：mul_epow : (x * y) ^ z = x ^ z * y ^ z
该定理/引理给出了一组等式。
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
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `ENat.one_epow`：one_epow : (1 : Nat∞) ^ y = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `ENat.epow_top`：epow_top (h : 1 < x) : x ^ (⊤ : Nat∞) = ⊤
· 使用定理 `ENat.mul_top`：∀ {m : ℕ∞}, m ≠ 0 → m * ⊤ = ⊤
· 使用定理 `ENat.top_ne_zero`：⊤ ≠ 0
· 使用定理 `one_lt_mul`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a b : M₀} [ZeroLEOneClass M₀] [MulPosMono M₀],   1 ≤ a → 1 < b → 1 < a 
…
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
-/
lemma mul_epow : (x * y) ^ z = x ^ z * y ^ z := by
  induction z
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · simp only [Order.lt_one_iff.1 x_0, zero_mul, zero_epow_top]
    · simp only [one_mul, one_epow]
    · rcases lt_trichotomy y 1 with y_0 | rfl | y_2
      · simp only [Order.lt_one_iff.1 y_0, mul_zero, zero_epow_top]
      · simp
      · rw [epow_top x_2, epow_top y_2, mul_top top_ne_zero]
        exact epow_top (one_lt_mul x_2.le y_2)
  · simp only [epow_natCast, mul_pow x y]
/-
**ENat.epow_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：epow_mul : x ^ (y * z) = (x ^ y) ^ z
该定理/引理给出了一组等式。
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `ENat.epow_zero`：epow_zero : x ^ (0 : Nat∞) = 1
· 使用引理 `ENat.one_epow`：one_epow : (1 : Nat∞) ^ y = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用引理 `ENat.zero_epow`：zero_epow (h : y != 0) : (0 : Nat∞) ^ y = 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `instNoZeroDivisorsENat`：NoZeroDivisors ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.top_mul`：∀ {m : ℕ∞}, m ≠ 0 → ⊤ * m = ⊤
· 使用引理 `ENat.epow_top`：epow_top (h : 1 < x) : x ^ (⊤ : Nat∞) = ⊤
· 使用引理 `ENat.top_epow`：top_epow (h : y != 0) : (⊤ : Nat∞) ^ y = ⊤
· 使用定理 `ENat.mul_top`：∀ {m : ℕ∞}, m ≠ 0 → m * ⊤ = ⊤
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用引理 `ENat.epow_right_mono`：epow_right_mono (h : x != 0) : Monotone (fun y : N
at∞ => x ^ y)
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
（共 33 条，此处仅展示前 30 条）
-/
lemma epow_mul : x ^ (y * z) = (x ^ y) ^ z := by
  rcases eq_or_ne y 0 with y_0 | y_0
  · simp [y_0]
  rcases eq_or_ne z 0 with z_0 | z_0
  · simp [z_0]
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0, zero_epow y_0, zero_epow z_0, zero_epow (mul_ne_zero y_0 z_0)]
  · simp only [one_epow]
  · induction y
    · rw [top_mul z_0, epow_top x_2, top_epow z_0]
    induction z
    · rw [mul_top y_0, epow_top x_2, epow_top]
      apply (epow_right_mono x_2.ne_zero (Order.one_le_iff_ne_zero.2 y_0)).trans_lt'
      simp [x_2]
    · simp only [← Nat.cast_mul, epow_natCast, pow_mul x]

end ENat

