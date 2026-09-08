/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Lemmas about the interaction of power operations with order in terms of `CovariantClass`
-/

public section

open Function

variable {β G M : Type*}

section Monoid

variable [Monoid M]

section Preorder

variable [Preorder M]

namespace Left

variable [MulLeftMono M] {a : M}

@[to_additive Left.nsmul_nonneg]
/-
**Left.one_le_pow_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Left`。
形式化陈述：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder M] [MulLeftMono M] {
a : M}, 1 ≤ a → ∀ (n : ℕ), 1 ≤ a ^ n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_le_pow_of_le (ha : 1 ≤ a) : ∀ n : ℕ, 1 ≤ a ^ n
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ]
    exact one_le_mul (one_le_pow_of_le ha k) ha

@[to_additive nsmul_nonpos]
/-
**Left.pow_le_one_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Left`。
形式化陈述：pow_le_one_of_le (ha : a <= 1) (n : Nat) : a ^ n <= 1
参数：ha : a <= 1；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Left.one_le_pow_of_le`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preo
rder M] [MulLeftMono M] {a : M}, 1 ≤ a → ∀ (n : ℕ), 1 ≤ a ^ n
-/
theorem pow_le_one_of_le (ha : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 := one_le_pow_of_le (M := Mᵒᵈ) ha n

@[to_additive nsmul_neg]
/-
**Left.pow_lt_one_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Left`。
形式化陈述：pow_lt_one_of_lt {a : M} {n : Nat} (h : a < 1) (hn : n != 0) : a ^ n < 1
参数：h : a < 1；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Left.mul_lt_one_of_lt_of_le`：Left.mul_lt_one_of_lt_of_le [MulLeftMono α]
 {a b : α} (ha : a < 1) (hb : b <= 1) : a * b < 1
· 使用定理 `Left.pow_le_one_of_le`：pow_le_one_of_le (ha : a <= 1) (n : Nat) : a ^ n 
<= 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pow_lt_one_of_lt {a : M} {n : ℕ} (h : a < 1) (hn : n ≠ 0) : a ^ n < 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
  rw [pow_succ']
  exact mul_lt_one_of_lt_of_le h (pow_le_one_of_le h.le _)

end Left

@[to_additive nsmul_nonneg] alias one_le_pow_of_one_le' := Left.one_le_pow_of_le
@[to_additive nsmul_nonpos] alias pow_le_one' := Left.pow_le_one_of_le
@[to_additive nsmul_neg] alias pow_lt_one' := Left.pow_lt_one_of_lt

section Left

variable [MulLeftMono M] {a : M} {n : ℕ}

@[to_additive nsmul_left_monotone]
/-
**pow_right_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_right_monotone (ha : 1 <= a) : Monotone fun n : Nat => a ^ n
参数：ha : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
-/
theorem pow_right_monotone (ha : 1 ≤ a) : Monotone fun n : ℕ ↦ a ^ n :=
  monotone_nat_of_le_succ fun n ↦ by rw [pow_succ]; exact le_mul_of_one_le_right' ha

-- `gcongr low` so that we prefer `Set.pow_subset_pow` and `Finset.pow_subset_pow`
@[to_additive (attr := gcongr low) nsmul_le_nsmul_left]
/-
**pow_le_pow_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_le_pow_right' {n m : Nat} (ha : 1 <= a) (h : n <= m) : a ^ n <= a ^ m
参数：ha : 1 <= a；h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_right_monotone`：pow_right_monotone (ha : 1 <= a) : Monotone fun n : 
Nat => a ^ n
-/
theorem pow_le_pow_right' {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
  pow_right_monotone ha h

@[to_additive nsmul_le_nsmul_left_of_nonpos]
/-
**pow_le_pow_right_of_le_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_le_pow_right_of_le_one' {n m : Nat} (ha : a <= 1) (h : n <= m) : a ^ m
 <= a ^ n
参数：ha : a <= 1；h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_right'`：pow_le_pow_right' {n m : Nat} (ha : 1 <= a) (h : n <=
 m) : a ^ n <= a ^ m
-/
theorem pow_le_pow_right_of_le_one' {n m : ℕ} (ha : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n :=
  pow_le_pow_right' (M := Mᵒᵈ) ha h

@[to_additive nsmul_pos]
/-
**one_lt_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_pow' (ha : 1 < a) {k : Nat} (hk : k != 0) : 1 < a ^ k
参数：ha : 1 < a；hk : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_lt_one'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder M] [M
ulLeftMono M] {a : M} {n : ℕ}, a < 1 → n ≠ 0 → a ^ n < 1
-/
theorem one_lt_pow' (ha : 1 < a) {k : ℕ} (hk : k ≠ 0) : 1 < a ^ k :=
  pow_lt_one' (M := Mᵒᵈ) ha hk

@[to_additive]
/-
**le_self_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_self_pow (ha : 1 <= a) (hn : n != 0) : a <= a ^ n
参数：ha : 1 <= a；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_le_pow_right'`：pow_le_pow_right' {n m : Nat} (ha : 1 <= a) (h : n <=
 m) : a ^ n <= a ^ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
lemma le_self_pow (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  simpa using pow_le_pow_right' ha (Nat.one_le_iff_ne_zero.2 hn)

end Left

section LeftLt

variable [MulLeftStrictMono M] {a : M} {n m : ℕ}

@[to_additive nsmul_left_strictMono]
/-
**pow_right_strictMono'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_right_strictMono' (ha : 1 < a) : StrictMono ((a ^ ·) : Nat -> M)
参数：ha : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `lt_mul_of_one_lt_right'`：lt_mul_of_one_lt_right' [MulLeftStrictMono α] (
a : α) {b : α} (h : 1 < b) : a < a * b
-/
theorem pow_right_strictMono' (ha : 1 < a) : StrictMono ((a ^ ·) : ℕ → M) :=
  strictMono_nat_of_lt_succ fun n ↦ by rw [pow_succ]; exact lt_mul_of_one_lt_right' (a ^ n) ha

@[to_additive (attr := gcongr) nsmul_lt_nsmul_left]
/-
**pow_lt_pow_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_lt_pow_right' (ha : 1 < a) (h : n < m) : a ^ n < a ^ m
参数：ha : 1 < a；h : n < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_right_strictMono'`：pow_right_strictMono' (ha : 1 < a) : StrictMono (
(a ^ ·) : Nat -> M)
-/
theorem pow_lt_pow_right' (ha : 1 < a) (h : n < m) : a ^ n < a ^ m :=
  pow_right_strictMono' ha h

end LeftLt

section Right

variable [MulRightMono M] {x : M}

@[to_additive Right.nsmul_nonneg]
/-
**Right.one_le_pow_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Right`。
形式化陈述：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder M] [MulRightMono M] 
{x : M}, 1 ≤ x → ∀ {n : ℕ}, 1 ≤ x ^ n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Right.one_le_pow_of_le (hx : 1 ≤ x) : ∀ {n : ℕ}, 1 ≤ x ^ n
  | 0 => (pow_zero _).ge
  | n + 1 => by
    rw [pow_succ]
    exact Right.one_le_mul (Right.one_le_pow_of_le hx) hx

@[to_additive Right.nsmul_nonpos]
/-
**Right.pow_le_one_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.pow_le_one_of_le (hx : x <= 1) {n : Nat} : x ^ n <= 1
参数：hx : x <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Right.one_le_pow_of_le`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Pre
order M] [MulRightMono M] {x : M}, 1 ≤ x → ∀ {n : ℕ}, 1 ≤ x ^ n
-/
theorem Right.pow_le_one_of_le (hx : x ≤ 1) {n : ℕ} : x ^ n ≤ 1 :=
  Right.one_le_pow_of_le (M := Mᵒᵈ) hx

@[to_additive Right.nsmul_neg]
/-
**Right.pow_lt_one_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.pow_lt_one_of_lt {n : Nat} {x : M} (hn : 0 < n) (h : x < 1) : x ^ n 
< 1
参数：hn : 0 < n；h : x < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Right.mul_lt_one_of_le_of_lt`：Right.mul_lt_one_of_le_of_lt [MulRightMono
 α] {a b : α} (ha : a <= 1) (hb : b < 1) : a * b < 1
· 使用定理 `Right.pow_le_one_of_le`：Right.pow_le_one_of_le (hx : x <= 1) {n : Nat} :
 x ^ n <= 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Right.pow_lt_one_of_lt {n : ℕ} {x : M} (hn : 0 < n) (h : x < 1) : x ^ n < 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨k, rfl⟩
  rw [pow_succ]
  exact mul_lt_one_of_le_of_lt (pow_le_one_of_le h.le) h

/-- This lemma is useful in non-cancellative monoids, like sets under pointwise operations. -/
@[to_additive
/-- This lemma is useful in non-cancellative monoids, like sets under pointwise operations. -/]
/-
**pow_le_pow_mul_of_sq_le_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_le_pow_mul_of_sq_le_mul [MulLeftMono M] {a b : M} (hab : a ^ 2 <= b * 
a) : forall {n}, n != 0 -> a ^ n <= b ^ (n - 1) * a | 1, _ => by simp | n + 2, _
 => by calc a ^ (n + 2) = a ^ (n + 1) * a
参数：hab : a ^ 2 <= b * a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pow_le_pow_mul_of_sq_le_mul [MulLeftMono M] {a b : M} (hab : a ^ 2 ≤ b * a) :
    ∀ {n}, n ≠ 0 → a ^ n ≤ b ^ (n - 1) * a
  | 1, _ => by simp
  | n + 2, _ => by
    calc
      a ^ (n + 2) = a ^ (n + 1) * a := by rw [pow_succ]
      _ ≤ b ^ n * a * a := by grw [pow_le_pow_mul_of_sq_le_mul hab (by lia)]; simp
      _ = b ^ n * a ^ 2 := by rw [mul_assoc, sq]
      _ ≤ b ^ n * (b * a) := by grw [hab]
      _ = b ^ (n + 1) * a := by rw [← mul_assoc, ← pow_succ]

end Right

section CovariantLTSwap

variable [Preorder β] [MulLeftStrictMono M] [MulRightStrictMono M] {f : β → M} {n : ℕ}

@[to_additive StrictMono.const_nsmul]
/-
**StrictMono.pow_const** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：∀ {β : Type u_1} {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder M] [i
nst_2 : Preorder β] [MulLeftStrictMono M]   [MulRightStrictMono M] {f : β → M}, 
StrictMono f → ∀ {n : ℕ}, n ≠ 0 → StrictMono fun x => f x ^ n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrictMono.pow_const (hf : StrictMono f) : ∀ {n : ℕ}, n ≠ 0 → StrictMono (f · ^ n)
  | 0, hn => (hn rfl).elim
  | 1, _ => by simpa
  | Nat.succ <| Nat.succ n, _ => by
    simpa only [pow_succ] using (hf.pow_const n.succ_ne_zero).mul' hf

/-- See also `pow_left_strictMonoOn₀`. -/
@[to_additive nsmul_right_strictMono]
/-
**pow_left_strictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_left_strictMono (hn : n != 0) : StrictMono (· ^ n : M -> M)
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.pow_const`：∀ {β : Type u_1} {M : Type u_3} [inst : Monoid M] 
[inst_1 : Preorder M] [inst_2 : Preorder β] [MulLeftStrictMono M]   [MulRightStr
ictMono M]…
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)

--- 原说明 ---
See also `pow_left_strictMonoOn₀`.
-/
theorem pow_left_strictMono (hn : n ≠ 0) : StrictMono (· ^ n : M → M) := strictMono_id.pow_const hn

@[to_additive (attr := mono, gcongr) nsmul_lt_nsmul_right]
/-
**pow_lt_pow_left'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_lt_pow_left' (hn : n != 0) {a b : M} (hab : a < b) : a ^ n < b ^ n
参数：hn : n != 0；hab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_left_strictMono`：pow_left_strictMono (hn : n != 0) : StrictMono (· ^
 n : M -> M)
-/
lemma pow_lt_pow_left' (hn : n ≠ 0) {a b : M} (hab : a < b) : a ^ n < b ^ n :=
  pow_left_strictMono hn hab

end CovariantLTSwap

section CovariantLESwap

variable [Preorder β] [MulLeftMono M] [MulRightMono M]

@[to_additive (attr := mono, gcongr) nsmul_le_nsmul_right]
/-
**pow_le_pow_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder M] [MulLeftMono M] [
MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ i
参数：i : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_le_pow_left' {a b : M} (hab : a ≤ b) : ∀ i : ℕ, a ^ i ≤ b ^ i
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_succ]
    exact mul_le_mul' (pow_le_pow_left' hab k) hab

@[to_additive Monotone.const_nsmul]
/-
**Monotone.pow_const** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {β : Type u_1} {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder M] [i
nst_2 : Preorder β] [MulLeftMono M]   [MulRightMono M] {f : β → M}, Monotone f →
 ∀ (n : ℕ), Monotone fun a => f a ^ n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monotone.pow_const {f : β → M} (hf : Monotone f) : ∀ n : ℕ, Monotone fun a => f a ^ n
  | 0 => by simpa using monotone_const
  | n + 1 => by
    simp_rw [pow_succ]
    exact (Monotone.pow_const hf _).mul' hf

@[to_additive nsmul_right_mono]
/-
**pow_left_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_left_mono (n : Nat) : Monotone fun a : M => a ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.pow_const`：∀ {β : Type u_1} {M : Type u_3} [inst : Monoid M] [i
nst_1 : Preorder M] [inst_2 : Preorder β] [MulLeftMono M]   [MulRightMono M] {f 
: β → M}…
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
-/
theorem pow_left_mono (n : ℕ) : Monotone fun a : M => a ^ n := monotone_id.pow_const _

-- `gcongr low` so that we prefer `Set.pow_subset_pow` and `Finset.pow_subset_pow`
@[to_additive (attr := gcongr low)]
/-
**pow_le_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_le_pow {a b : M} (hab : a <= b) (ht : 1 <= b) {m n : Nat} (hmn : m <= 
n) : a ^ m <= b ^ n
参数：hab : a <= b；ht : 1 <= b；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `pow_le_pow_right'`：pow_le_pow_right' {n m : Nat} (ha : 1 <= a) (h : n <=
 m) : a ^ n <= a ^ m
-/
lemma pow_le_pow {a b : M} (hab : a ≤ b) (ht : 1 ≤ b) {m n : ℕ} (hmn : m ≤ n) : a ^ m ≤ b ^ n :=
  (pow_le_pow_left' hab _).trans (pow_le_pow_right' ht hmn)

end CovariantLESwap

end Preorder

section SemilatticeSup
variable [SemilatticeSup M] [MulLeftMono M] [MulRightMono M] {a b : M} {n : ℕ}

/-
**le_pow_sup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_pow_sup : a ^ n ⊔ b ^ n <= (a ⊔ b) ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma le_pow_sup : a ^ n ⊔ b ^ n ≤ (a ⊔ b) ^ n :=
  sup_le (pow_le_pow_left' le_sup_left _) (pow_le_pow_left' le_sup_right _)

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf M] [MulLeftMono M] [MulRightMono M] {a b : M} {n : ℕ}

/-
**pow_inf_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_inf_le : (a ⊓ b) ^ n <= a ^ n ⊓ b ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma pow_inf_le : (a ⊓ b) ^ n ≤ a ^ n ⊓ b ^ n :=
  le_inf (pow_le_pow_left' inf_le_left _) (pow_le_pow_left' inf_le_right _)

end SemilatticeInf

section LinearOrder

variable [LinearOrder M]

section CovariantLE

variable [MulLeftMono M]

-- This generalises to lattices. See `pow_two_semiclosed`
@[to_additive nsmul_nonneg_iff]
/-
**one_le_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_pow_iff {x : M} {n : Nat} (hn : n != 0) : 1 <= x ^ n ↔ 1 <= x
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_lt_imp_lt`：le_imp_le_of_lt_imp_lt {α β} [Preorder α] [Linea
rOrder β] {a b : α} {c d : β} (H : d < c -> b < a) (h : a <= b) : c <= d
· 使用定理 `pow_lt_one'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder M] [M
ulLeftMono M] {a : M} {n : ℕ}, a < 1 → n ≠ 0 → a ^ n < 1
· 使用定理 `one_le_pow_of_one_le'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preo
rder M] [MulLeftMono M] {a : M}, 1 ≤ a → ∀ (n : ℕ), 1 ≤ a ^ n
-/
theorem one_le_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 ≤ x ^ n ↔ 1 ≤ x :=
  ⟨le_imp_le_of_lt_imp_lt fun h => pow_lt_one' h hn, fun h => one_le_pow_of_one_le' h n⟩

@[to_additive]
/-
**pow_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_le_one_iff {x : M} {n : Nat} (hn : n != 0) : x ^ n <= 1 ↔ x <= 1
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_le_pow_iff`：one_le_pow_iff {x : M} {n : Nat} (hn : n != 0) : 1 <= x 
^ n ↔ 1 <= x
-/
theorem pow_le_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n ≤ 1 ↔ x ≤ 1 :=
  one_le_pow_iff (M := Mᵒᵈ) hn

@[to_additive nsmul_pos_iff]
/-
**one_lt_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_pow_iff {x : M} {n : Nat} (hn : n != 0) : 1 < x ^ n ↔ 1 < x
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `pow_le_one_iff`：pow_le_one_iff {x : M} {n : Nat} (hn : n != 0) : x ^ n <
= 1 ↔ x <= 1
-/
theorem one_lt_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 < x ^ n ↔ 1 < x :=
  lt_iff_lt_of_le_iff_le (pow_le_one_iff hn)

@[to_additive]
/-
**pow_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_lt_one_iff {x : M} {n : Nat} (hn : n != 0) : x ^ n < 1 ↔ x < 1
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `one_le_pow_iff`：one_le_pow_iff {x : M} {n : Nat} (hn : n != 0) : 1 <= x 
^ n ↔ 1 <= x
-/
theorem pow_lt_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n < 1 ↔ x < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff hn)

end CovariantLE

section CovariantLT

variable [MulLeftStrictMono M] {a : M} {m n : ℕ}

@[to_additive nsmul_le_nsmul_iff_left]
/-
**pow_le_pow_iff_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_le_pow_iff_right' (ha : 1 < a) : a ^ m <= a ^ n ↔ m <= n
参数：ha : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `pow_right_strictMono'`：pow_right_strictMono' (ha : 1 < a) : StrictMono (
(a ^ ·) : Nat -> M)
-/
theorem pow_le_pow_iff_right' (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (pow_right_strictMono' ha).le_iff_le

@[to_additive nsmul_lt_nsmul_iff_left]
/-
**pow_lt_pow_iff_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_lt_pow_iff_right' (ha : 1 < a) : a ^ m < a ^ n ↔ m < n
参数：ha : 1 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `pow_right_strictMono'`：pow_right_strictMono' (ha : 1 < a) : StrictMono (
(a ^ ·) : Nat -> M)
-/
theorem pow_lt_pow_iff_right' (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (pow_right_strictMono' ha).lt_iff_lt

end CovariantLT

section CovariantLESwap

variable [MulLeftMono M] [MulRightMono M]

@[to_additive lt_of_nsmul_lt_nsmul_right]
/-
**lt_of_pow_lt_pow_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_pow_lt_pow_left' {a b : M} (n : Nat) : a ^ n < b ^ n -> a < b
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `pow_left_mono`：pow_left_mono (n : Nat) : Monotone fun a : M => a ^ n
-/
theorem lt_of_pow_lt_pow_left' {a b : M} (n : ℕ) : a ^ n < b ^ n → a < b :=
  (pow_left_mono _).reflect_lt

@[to_additive min_lt_of_add_lt_two_nsmul]
/-
**min_lt_of_mul_lt_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_lt_of_mul_lt_sq {a b c : M} (h : a * b < c ^ 2) : min a b < c
参数：h : a * b < c ^ 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `min_lt_max_of_mul_lt_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Line
arOrder α] {a b c d : α} [MulLeftMono α] [MulRightMono α],   a * b < c * d → min
 a b < max c d
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem min_lt_of_mul_lt_sq {a b c : M} (h : a * b < c ^ 2) : min a b < c := by
  simpa using min_lt_max_of_mul_lt_mul (h.trans_eq <| pow_two _)

@[to_additive lt_max_of_two_nsmul_lt_add]
/-
**lt_max_of_sq_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_max_of_sq_lt_mul {a b c : M} (h : a ^ 2 < b * c) : a < max b c
参数：h : a ^ 2 < b * c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `min_lt_max_of_mul_lt_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Line
arOrder α] {a b c d : α} [MulLeftMono α] [MulRightMono α],   a * b < c * d → min
 a b < max c d
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem lt_max_of_sq_lt_mul {a b c : M} (h : a ^ 2 < b * c) : a < max b c := by
  simpa using min_lt_max_of_mul_lt_mul ((pow_two _).symm.trans_lt h)

end CovariantLESwap

section CovariantLTSwap

variable [MulLeftStrictMono M] [MulRightStrictMono M]

@[to_additive nsmul_le_nsmul_iff_right]
/-
**pow_le_pow_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_le_pow_iff_left {a b : M} {n : Nat} (hn : n != 0) : a ^ n <= b ^ n ↔ a
 <= b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `pow_left_strictMono`：pow_left_strictMono (hn : n != 0) : StrictMono (· ^
 n : M -> M)
-/
theorem pow_le_pow_iff_left {a b : M} {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (pow_left_strictMono hn).le_iff_le

@[to_additive le_of_nsmul_le_nsmul_right]
alias ⟨le_of_pow_le_pow_left', _⟩ := pow_le_pow_iff_left

@[to_additive min_le_of_add_le_two_nsmul]
/-
**min_le_of_mul_le_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_le_of_mul_le_sq {a b c : M} (h : a * b <= c ^ 2) : min a b <= c
参数：h : a * b <= c ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `min_le_max_of_mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Line
arOrder α] {a b c d : α} [MulLeftStrictMono α] [MulRightStrictMono α],   a * b ≤
 c * d → min a…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem min_le_of_mul_le_sq {a b c : M} (h : a * b ≤ c ^ 2) : min a b ≤ c := by
  simpa using min_le_max_of_mul_le_mul (h.trans_eq <| pow_two _)

@[to_additive le_max_of_two_nsmul_le_add]
/-
**le_max_of_sq_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_max_of_sq_le_mul {a b c : M} (h : a ^ 2 <= b * c) : a <= max b c
参数：h : a ^ 2 <= b * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `min_le_max_of_mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Line
arOrder α] {a b c d : α} [MulLeftStrictMono α] [MulRightStrictMono α],   a * b ≤
 c * d → min a…
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem le_max_of_sq_le_mul {a b c : M} (h : a ^ 2 ≤ b * c) : a ≤ max b c := by
  simpa using min_le_max_of_mul_le_mul ((pow_two _).symm.trans_le h)

end CovariantLTSwap

@[to_additive Left.nsmul_neg_iff]
/-
**Left.pow_lt_one_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.pow_lt_one_iff' [MulLeftStrictMono M] {n : Nat} {x : M} (hn : 0 < n) 
: x ^ n < 1 ↔ x < 1
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_lt_one_iff`：pow_lt_one_iff {x : M} {n : Nat} (hn : n != 0) : x ^ n <
 1 ↔ x < 1
· 使用定理 `mulLeftMono_of_mulLeftStrictMono`：mulLeftMono_of_mulLeftStrictMono (M) [
Mul M] [PartialOrder M] [MulLeftStrictMono M] : MulLeftMono M
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem Left.pow_lt_one_iff' [MulLeftStrictMono M] {n : ℕ} {x : M} (hn : 0 < n) :
    x ^ n < 1 ↔ x < 1 :=
  haveI := mulLeftMono_of_mulLeftStrictMono M
  pow_lt_one_iff hn.ne'
/-
**Left.pow_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.pow_lt_one_iff [MulLeftStrictMono M] {n : Nat} {x : M} (hn : 0 < n) :
 x ^ n < 1 ↔ x < 1
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Left.pow_lt_one_iff'`：Left.pow_lt_one_iff' [MulLeftStrictMono M] {n : Na
t} {x : M} (hn : 0 < n) : x ^ n < 1 ↔ x < 1
-/
theorem Left.pow_lt_one_iff [MulLeftStrictMono M] {n : ℕ} {x : M} (hn : 0 < n) :
    x ^ n < 1 ↔ x < 1 := Left.pow_lt_one_iff' hn

@[to_additive]
/-
**Right.pow_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.pow_lt_one_iff [MulRightStrictMono M] {n : Nat} {x : M} (hn : 0 < n)
 : x ^ n < 1 ↔ x < 1
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Right.one_le_pow_of_le`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Pre
order M] [MulRightMono M] {x : M}, 1 ≤ x → ∀ {n : ℕ}, 1 ≤ x ^ n
· 使用定理 `mulRightMono_of_mulRightStrictMono`：mulRightMono_of_mulRightStrictMono (
M) [Mul M] [PartialOrder M] [MulRightStrictMono M] : MulRightMono M
· 使用定理 `Right.pow_lt_one_of_lt`：Right.pow_lt_one_of_lt {n : Nat} {x : M} (hn : 0
 < n) (h : x < 1) : x ^ n < 1
-/
theorem Right.pow_lt_one_iff [MulRightStrictMono M] {n : ℕ} {x : M}
    (hn : 0 < n) : x ^ n < 1 ↔ x < 1 :=
  haveI := mulRightMono_of_mulRightStrictMono M
  ⟨fun H => not_le.mp fun k => H.not_ge <| Right.one_le_pow_of_le k, Right.pow_lt_one_of_lt hn⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulLeftStrictMono M] [MulRightStrictMono M] : IsMulTorsionFree M where
  pow_left_injective _ hn := (pow_left_strictMono hn).injective

end LinearOrder

end Monoid

section DivInvMonoid

variable [DivInvMonoid G] [Preorder G] [MulLeftMono G]

@[to_additive zsmul_nonneg]
/-
**one_le_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_zpow {x : G} (H : 1 <= x) {n : Int} (hn : 0 <= n) : 1 <= x ^ n
参数：H : 1 <= x；hn : 0 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `one_le_pow_of_one_le'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preo
rder M] [MulLeftMono M] {a : M}, 1 ≤ a → ∀ (n : ℕ), 1 ≤ a ^ n
-/
theorem one_le_zpow {x : G} (H : 1 ≤ x) {n : ℤ} (hn : 0 ≤ n) : 1 ≤ x ^ n := by
  lift n to ℕ using hn
  rw [zpow_natCast]
  apply one_le_pow_of_one_le' H

@[to_additive zsmul_pos]
/-
**one_lt_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_lt_zpow {x : G} (hx : 1 < x) {n : Int} (hn : 0 < n) : 1 < x ^ n
参数：hx : 1 < x；hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `Int.le_of_lt`：∀ {a b : ℤ}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `one_lt_pow'`：one_lt_pow' (ha : 1 < a) {k : Nat} (hk : k != 0) : 1 < a ^ 
k
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
-/
lemma one_lt_zpow {x : G} (hx : 1 < x) {n : ℤ} (hn : 0 < n) : 1 < x ^ n := by
  lift n to ℕ using Int.le_of_lt hn
  rw [zpow_natCast]
  exact one_lt_pow' hx (Int.natCast_pos.mp hn).ne'

end DivInvMonoid

