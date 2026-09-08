/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The von Mangoldt Function

In this file we define the von Mangoldt function: the function on natural numbers that returns
`log p` if the input can be expressed as `p^k` for a prime `p`.

## Main Results

The main definition for this file is

- `ArithmeticFunction.vonMangoldt`: The von Mangoldt function `Λ`.

We then prove the classical summation property of the von Mangoldt function in
`ArithmeticFunction.vonMangoldt_sum`, that `∑ i ∈ n.divisors, Λ i = Real.log n`, and use this
to deduce alternative expressions for the von Mangoldt function via Möbius inversion, see
`ArithmeticFunction.sum_moebius_mul_log_eq`.

## Notation

We use the standard notation `Λ` to represent the von Mangoldt function.
It is accessible in the locales `ArithmeticFunction` (like the notations for other arithmetic
functions) and also in the scope `ArithmeticFunction.vonMangoldt`.

-/

@[expose] public section

namespace ArithmeticFunction

open Finset Nat

open scoped ArithmeticFunction

/-- `log` as an arithmetic function `ℕ → ℝ`. Note this is in the `ArithmeticFunction`
namespace to indicate that it is bundled as an `ArithmeticFunction` rather than being the usual
real logarithm. -/
/-
**ArithmeticFunction.log** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：ArithmeticFunction ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`log` as an arithmetic function `ℕ → ℝ`. Note this is in the `ArithmeticFunction
`
namespace to indicate that it is bundled as an `ArithmeticFunction` rather than 
being the usual
real logarithm.
-/
noncomputable def log : ArithmeticFunction ℝ :=
  ⟨fun n => Real.log n, by simp⟩

@[simp]
/-
**ArithmeticFunction.log_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：∀ {n : ℕ}, ArithmeticFunction.log n = Real.log ↑n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem log_apply {n : ℕ} : log n = Real.log n :=
  rfl

/--
The `vonMangoldt` function is the function on natural numbers that returns `log p` if the input can
be expressed as `p^k` for a prime `p`.
In the case when `n` is a prime power, `Nat.minFac` will give the appropriate prime, as it is the
smallest prime factor.

In the `ArithmeticFunction` locale, we have the notation `Λ` for this function.
This is also available in the `ArithmeticFunction.vonMangoldt` locale, allowing for selective
access to the notation.
-/
/-
**ArithmeticFunction.vonMangoldt** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：ArithmeticFunction ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `vonMangoldt` function is the function on natural numbers that returns `log 
p` if the input can
be expressed as `p^k` for a prime `p`.
In the case when `n` is a prime power, `Nat.minFac` will give the appropriate pr
ime, as it is the
smallest prime factor.

In the `ArithmeticFunction` locale, we have the notation `Λ` for this function.
This is also available in the `ArithmeticFunction.vonMangoldt` locale, allowing 
for selective
access to the notation.
-/
noncomputable def vonMangoldt : ArithmeticFunction ℝ :=
  ⟨fun n => if IsPrimePow n then Real.log (minFac n) else 0, if_neg not_isPrimePow_zero⟩

@[inherit_doc] scoped[ArithmeticFunction] notation "Λ" => ArithmeticFunction.vonMangoldt

@[inherit_doc] scoped[ArithmeticFunction.vonMangoldt] notation "Λ" =>
  ArithmeticFunction.vonMangoldt
/-
**ArithmeticFunction.vonMangoldt_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunc
tion`。
形式化陈述：∀ {n : ℕ}, ArithmeticFunction.vonMangoldt n = if IsPrimePow n then Real.lo
g ↑n.minFac else 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vonMangoldt_apply {n : ℕ} : Λ n = if IsPrimePow n then Real.log (minFac n) else 0 :=
  rfl

@[simp]
/-
**ArithmeticFunction.vonMangoldt_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `Arithmetic
Function`。
形式化陈述：ArithmeticFunction.vonMangoldt 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.minFac_one`：minFac_one : minFac 1 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vonMangoldt_apply_one : Λ 1 = 0 := by simp [vonMangoldt_apply]

@[simp]
/-
**ArithmeticFunction.vonMangoldt_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFun
ction`。
形式化陈述：∀ {n : ℕ}, 0 ≤ ArithmeticFunction.vonMangoldt n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.vonMangoldt_apply`：∀ {n : ℕ}, ArithmeticFunction.vonM
angoldt n = if IsPrimePow n then Real.log ↑n.minFac else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Real.log_nonneg`：log_nonneg (hx : 1 <= x) : 0 <= log x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_cast`：one_le_cast : 1 <= (n : α) ↔ 1 <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.minFac_pos`：minFac_pos (n : Nat) : 0 < minFac n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem vonMangoldt_nonneg {n : ℕ} : 0 ≤ Λ n := by
  rw [vonMangoldt_apply]
  split_ifs
  · exact Real.log_nonneg (one_le_cast.2 (Nat.minFac_pos n))
  rfl
/-
**ArithmeticFunction.vonMangoldt_apply_pow** 是 Mathlib 中的一个定理，位于命名空间 `Arithmetic
Function`。
形式化陈述：∀ {n k : ℕ}, k ≠ 0 → ArithmeticFunction.vonMangoldt (n ^ k) = ArithmeticFu
nction.vonMangoldt n
参数：n ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `isPrimePow_pow_iff`：isPrimePow_pow_iff {n k : Nat} (hk : k != 0) : IsPri
mePow (n ^ k) ↔ IsPrimePow n
· 使用定理 `Nat.pow_minFac`：pow_minFac {n k : Nat} (hk : k != 0) : (n ^ k).minFac = 
n.minFac
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vonMangoldt_apply_pow {n k : ℕ} (hk : k ≠ 0) : Λ (n ^ k) = Λ n := by
  simp only [vonMangoldt_apply, isPrimePow_pow_iff hk, pow_minFac hk]
/-
**ArithmeticFunction.vonMangoldt_apply_prime** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → ArithmeticFunction.vonMangoldt p = Real.log ↑p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.vonMangoldt_apply`：∀ {n : ℕ}, ArithmeticFunction.vonM
angoldt n = if IsPrimePow n then Real.log ↑n.minFac else 0
· 使用定理 `Nat.Prime.minFac_eq`：∀ {p : ℕ}, Nat.Prime p → p.minFac = p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Prime.isPrimePow`：Prime.isPrimePow {p : R} (hp : Prime p) : IsPrimePow p
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
-/
theorem vonMangoldt_apply_prime {p : ℕ} (hp : p.Prime) : Λ p = Real.log p := by
  rw [vonMangoldt_apply, Prime.minFac_eq hp, if_pos hp.prime.isPrimePow]
/-
**ArithmeticFunction.vonMangoldt_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：∀ {n : ℕ}, ArithmeticFunction.vonMangoldt n ≠ 0 ↔ IsPrimePow n
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
· 使用定理 `ArithmeticFunction.vonMangoldt_apply_one`：ArithmeticFunction.vonMangoldt
 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.ite_ne_right_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a
 b : α}, a ≠ b → ((if P then a else b) ≠ b ↔ P)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_cast`：one_lt_cast : 1 < (n : α) ↔ 1 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
-/
theorem vonMangoldt_ne_zero_iff {n : ℕ} : Λ n ≠ 0 ↔ IsPrimePow n := by
  rcases eq_or_ne n 1 with (rfl | hn); · simp [not_isPrimePow_one]
  exact (Real.log_pos (one_lt_cast.2 (minFac_prime hn).one_lt)).ne'.ite_ne_right_iff
/-
**ArithmeticFunction.vonMangoldt_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFu
nction`。
形式化陈述：∀ {n : ℕ}, 0 < ArithmeticFunction.vonMangoldt n ↔ IsPrimePow n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `ArithmeticFunction.vonMangoldt_nonneg`：∀ {n : ℕ}, 0 ≤ ArithmeticFunction
.vonMangoldt n
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `ArithmeticFunction.vonMangoldt_ne_zero_iff`：∀ {n : ℕ}, ArithmeticFunctio
n.vonMangoldt n ≠ 0 ↔ IsPrimePow n
-/
theorem vonMangoldt_pos_iff {n : ℕ} : 0 < Λ n ↔ IsPrimePow n :=
  vonMangoldt_nonneg.lt_iff_ne.trans (ne_comm.trans vonMangoldt_ne_zero_iff)
/-
**ArithmeticFunction.vonMangoldt_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Arithmet
icFunction`。
形式化陈述：∀ {n : ℕ}, ArithmeticFunction.vonMangoldt n = 0 ↔ ¬IsPrimePow n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用定理 `ArithmeticFunction.vonMangoldt_ne_zero_iff`：∀ {n : ℕ}, ArithmeticFunctio
n.vonMangoldt n ≠ 0 ↔ IsPrimePow n
-/
theorem vonMangoldt_eq_zero_iff {n : ℕ} : Λ n = 0 ↔ ¬IsPrimePow n :=
  vonMangoldt_ne_zero_iff.not_right
/-
**ArithmeticFunction.vonMangoldt_sum** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFuncti
on`。
形式化陈述：∀ {n : ℕ}, ∑ i ∈ n.divisors, ArithmeticFunction.vonMangoldt i = Real.log ↑
n
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.sum_divisors_prime_pow`：∀ {α : Type u_1} [inst : AddCommMonoid α] {k
 p : ℕ} {f : ℕ → α},   Nat.Prime p → ∑ x ∈ (p ^ k).divisors, f x = ∑ x ∈ Finset.
range (k + 1), f…
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Real.log_pow`：log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `Nat.pow_zero`：∀ (n : ℕ), n ^ 0 = 1
· 使用定理 `ArithmeticFunction.vonMangoldt_apply_one`：ArithmeticFunction.vonMangoldt
 1 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.vonMangoldt_apply_pow`：∀ {n k : ℕ}, k ≠ 0 → Arithmeti
cFunction.vonMangoldt (n ^ k) = ArithmeticFunction.vonMangoldt n
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `ArithmeticFunction.vonMangoldt_apply_prime`：∀ {p : ℕ}, Nat.Prime p → Ari
thmeticFunction.vonMangoldt p = Real.log ↑p
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.mul_divisors_filter_prime_pow`：Nat.mul_divisors_filter_prime_pow {a 
b : Nat} (hab : a.Coprime b) : {d in (a * b).divisors | IsPrimePow d} = {d in a.
divisors union b.diviso…
· 使用定理 `Finset.filter_union`：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).fil
ter p = s₁.filter p union s₂.filter p
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Nat.disjoint_divisors_filter_isPrimePow`：disjoint_divisors_filter_isPrim
ePow {a b : Nat} (hab : a.Coprime b) : Disjoint (a.divisors.filter IsPrimePow) (
b.divisors.filter IsPrimePow)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
（共 35 条，此处仅展示前 30 条）
-/
theorem vonMangoldt_sum {n : ℕ} : ∑ i ∈ n.divisors, Λ i = Real.log n := by
  refine recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p k hp
    rw [sum_divisors_prime_pow hp, cast_pow, Real.log_pow, Finset.sum_range_succ', Nat.pow_zero,
      vonMangoldt_apply_one]
    simp [vonMangoldt_apply_pow (Nat.succ_ne_zero _), vonMangoldt_apply_prime hp]
  intro a b ha' hb' hab ha hb
  simp only [vonMangoldt_apply, ← sum_filter] at ha hb ⊢
  rw [mul_divisors_filter_prime_pow hab, filter_union,
    sum_union (disjoint_divisors_filter_isPrimePow hab), ha, hb, Nat.cast_mul,
    Real.log_mul (cast_ne_zero.2 (pos_of_gt ha').ne') (cast_ne_zero.2 (pos_of_gt hb').ne')]

-- access notation `ζ` and `μ`
open scoped zeta Moebius

@[simp]
/-
**ArithmeticFunction.vonMangoldt_mul_zeta** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticF
unction`。
形式化陈述：ArithmeticFunction.vonMangoldt * ↑ArithmeticFunction.zeta = ArithmeticFunc
tion.log
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.coe_mul_zeta_apply`：coe_mul_zeta_apply [Semiring R] {
f : ArithmeticFunction R} {x : Nat} : (f * ζ) x = ∑ i in divisors x, f i
· 使用定理 `ArithmeticFunction.vonMangoldt_sum`：∀ {n : ℕ}, ∑ i ∈ n.divisors, Arithme
ticFunction.vonMangoldt i = Real.log ↑n
-/
theorem vonMangoldt_mul_zeta : Λ * ζ = log := by
  ext n; rw [coe_mul_zeta_apply, vonMangoldt_sum]; rfl

@[simp]
/-
**ArithmeticFunction.zeta_mul_vonMangoldt** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticF
unction`。
形式化陈述：↑ArithmeticFunction.zeta * ArithmeticFunction.vonMangoldt = ArithmeticFunc
tion.log
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.vonMangoldt_mul_zeta`：ArithmeticFunction.vonMangoldt 
* ↑ArithmeticFunction.zeta = ArithmeticFunction.log
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zeta_mul_vonMangoldt : (ζ : ArithmeticFunction ℝ) * Λ = log := by rw [mul_comm]; simp

@[simp]
/-
**ArithmeticFunction.log_mul_moebius_eq_vonMangoldt** 是 Mathlib 中的一个定理，位于命名空间 `A
rithmeticFunction`。
形式化陈述：ArithmeticFunction.log * ↑ArithmeticFunction.moebius = ArithmeticFunction.
vonMangoldt
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.vonMangoldt_mul_zeta`：ArithmeticFunction.vonMangoldt 
* ↑ArithmeticFunction.zeta = ArithmeticFunction.log
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ArithmeticFunction.coe_zeta_mul_coe_moebius`：coe_zeta_mul_coe_moebius [R
ing R] : (ζ * μ : ArithmeticFunction R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem log_mul_moebius_eq_vonMangoldt : log * μ = Λ := by
  rw [← vonMangoldt_mul_zeta, mul_assoc, coe_zeta_mul_coe_moebius, mul_one]

@[simp]
/-
**ArithmeticFunction.moebius_mul_log_eq_vonMangoldt** 是 Mathlib 中的一个定理，位于命名空间 `A
rithmeticFunction`。
形式化陈述：↑ArithmeticFunction.moebius * ArithmeticFunction.log = ArithmeticFunction.
vonMangoldt
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ArithmeticFunction.log_mul_moebius_eq_vonMangoldt`：ArithmeticFunction.lo
g * ↑ArithmeticFunction.moebius = ArithmeticFunction.vonMangoldt
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem moebius_mul_log_eq_vonMangoldt : (μ : ArithmeticFunction ℝ) * log = Λ := by
  rw [mul_comm]; simp
/-
**ArithmeticFunction.sum_moebius_mul_log_eq** 是 Mathlib 中的一个定理，位于命名空间 `Arithmeti
cFunction`。
形式化陈述：∀ {n : ℕ},   ∑ d ∈ n.divisors, ↑(ArithmeticFunction.moebius d) * Arithmeti
cFunction.log d = -ArithmeticFunction.vonMangoldt n
参数：ArithmeticFunction.moebius d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `Nat.sum_divisorsAntidiagonal`：∀ {M : Type u_1} [inst : AddCommMonoid M] 
(f : ℕ → ℕ → M) {n : ℕ},   ∑ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∑ i ∈ n.div
isors, f i (n / i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_div`：cast_div (hnm : n ∣ m) (hn : (n : K) != 0) : (↑(m / n) : K
) = m / n
· 使用定理 `Real.log_div`：log_div (hx : x != 0) (hy : y != 0) : log (x / y) = log x 
- log y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用引理 `Int.cast_sum`：cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι -> 
Int) : ↑(∑ x in s, f x : Int) = ∑ x in s, (f x : R)
· 使用定理 `ArithmeticFunction.coe_mul_zeta_apply`：coe_mul_zeta_apply [Semiring R] {
f : ArithmeticFunction R} {x : Nat} : (f * ζ) x = ∑ i in divisors x, f i
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_self`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = a ↔
 b = 0
· 使用定理 `ArithmeticFunction.moebius_mul_coe_zeta`：moebius_mul_coe_zeta : (μ * ζ :
 ArithmeticFunction Int) = 1
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_one`：map_one {f : ArithmeticFunc
tion R} (h : f.IsMultiplicative) : f 1 = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 38 条，此处仅展示前 30 条）
-/
theorem sum_moebius_mul_log_eq {n : ℕ} : (∑ d ∈ n.divisors, (μ d : ℝ) * log d) = -Λ n := by
  simp only [← log_mul_moebius_eq_vonMangoldt, mul_comm log, mul_apply, log_apply, intCoe_apply, ←
    Finset.sum_neg_distrib, neg_mul_eq_mul_neg]
  rw [sum_divisorsAntidiagonal fun i j => (μ i : ℝ) * -Real.log j]
  have : (∑ i ∈ n.divisors, (μ i : ℝ) * -Real.log (n / i : ℕ)) =
      ∑ i ∈ n.divisors, ((μ i : ℝ) * Real.log i - μ i * Real.log n) := by
    apply sum_congr rfl
    simp only [and_imp, Ne, mem_divisors]
    intro m mn hn
    have : (m : ℝ) ≠ 0 := by
      rw [cast_ne_zero]
      rintro rfl
      exact hn (by simpa using mn)
    rw [Nat.cast_div mn this, Real.log_div (cast_ne_zero.2 hn) this, neg_sub, mul_sub]
  rw [this, sum_sub_distrib, ← sum_mul, ← Int.cast_sum, ← coe_mul_zeta_apply, eq_comm, sub_eq_self,
    moebius_mul_coe_zeta]
  rcases eq_or_ne n 1 with (hn | hn) <;> simp [hn]
/-
**ArithmeticFunction.vonMangoldt_le_log** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFun
ction`。
形式化陈述：∀ {n : ℕ}, ArithmeticFunction.vonMangoldt n ≤ Real.log ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.vonMangoldt_sum`：∀ {n : ℕ}, ∑ i ∈ n.divisors, Arithme
ticFunction.vonMangoldt i = Real.log ↑n
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ArithmeticFunction.vonMangoldt_nonneg`：∀ {n : ℕ}, 0 ≤ ArithmeticFunction
.vonMangoldt n
· 使用定理 `Nat.mem_divisors_self`：mem_divisors_self (n : Nat) (h : n != 0) : n in n
.divisors
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
theorem vonMangoldt_le_log : ∀ {n : ℕ}, Λ n ≤ Real.log (n : ℝ)
  | 0 => by simp
  | n + 1 => by
    rw [← vonMangoldt_sum]
    exact single_le_sum (by exact fun _ _ => vonMangoldt_nonneg)
      (mem_divisors_self _ n.succ_ne_zero)

end ArithmeticFunction

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: the von Mangoldt function is nonnegative. -/
@[positivity ArithmeticFunction.vonMangoldt _]
meta def evalVonMangoldt : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@ArithmeticFunction.vonMangoldt $a) =>
    assertInstancesCommute
    pure (.nonnegative q(ArithmeticFunction.vonMangoldt_nonneg))
  | _, _, _ => throwError "not von Mangoldt"

end Mathlib.Meta.Positivity

