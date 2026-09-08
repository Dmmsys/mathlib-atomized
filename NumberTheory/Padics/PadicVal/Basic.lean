/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Matthew Robert Ballard
-/
module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.Nat.Prime.Int

/-!
# `p`-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in
`Mathlib/NumberTheory/Padics/PadicNorm.lean`.

## Notation

This file uses the local notation `/.` for `Rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## Calculations with `p`-adic valuations

* `padicValNat_factorial`: Legendre's Theorem. The `p`-adic valuation of `n!` is the sum of the
  quotients `n / p ^ i`. This sum is expressed over the finset `Ico 1 b` where `b` is any bound
  greater than `log p n`. See `Nat.Prime.multiplicity_factorial` for the same result but stated in
  the language of prime multiplicity.

* `sub_one_mul_padicValNat_factorial`: Legendre's Theorem.  Taking (`p - 1`) times
  the `p`-adic valuation of `n!` equals `n` minus the sum of base `p` digits of `n`.

* `padicValNat_choose`: Kummer's Theorem. The `p`-adic valuation of `n.choose k` is the number
  of carries when `k` and `n - k` are added in base `p`. This sum is expressed over the finset
  `Ico 1 b` where `b` is any bound greater than `log p n`. See `Nat.Prime.multiplicity_choose` for
  the same result but stated in the language of prime multiplicity.

* `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`: Kummer's Theorem. Taking (`p - 1`) times the
  `p`-adic valuation of the binomial `n` over `k` equals the sum of the digits of `k` plus the sum
  of the digits of `n - k` minus the sum of digits of `n`, all base `p`.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/

@[expose] public section


universe u

open Nat Rat
open scoped Finset

namespace padicValNat

variable {p : ℕ}

/-- If `p ≠ 0` and `p ≠ 1`, then `padicValNat p p` is `1`. -/
alias self := padicValNat_base

/-
**padicValNat.eq_zero_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：eq_zero_of_not_dvd {n : Nat} (h : ¬p ∣ n) : padicValNat p n = 0
参数：h : ¬p ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `padicValNat.eq_zero_iff`：eq_zero_iff {n : Nat} : padicValNat p n = 0 ↔ p
 = 1 ∨ n = 0 ∨ ¬p ∣ n
-/
theorem eq_zero_of_not_dvd {n : ℕ} (h : ¬p ∣ n) : padicValNat p n = 0 :=
  eq_zero_iff.2 <| Or.inr <| Or.inr h

end padicValNat

/-- For `p ≠ 1`, the `p`-adic valuation of an integer `z ≠ 0` is the largest natural number `k` such
that `p^k` divides `z`. If `x = 0` or `p = 1`, then `padicValInt p q` defaults to `0`. -/
/-
**padicValInt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：padicValInt (p : Nat) (z : Int) : Nat
参数：p : Nat；z : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `p ≠ 1`, the `p`-adic valuation of an integer `z ≠ 0` is the largest natural
 number `k` such
that `p^k` divides `z`. If `x = 0` or `p = 1`, then `padicValInt p q` defaults t
o `0`.
-/
def padicValInt (p : ℕ) (z : ℤ) : ℕ :=
  padicValNat p z.natAbs

namespace padicValInt

variable {p : ℕ}

/-
**padicValInt.of_ne_one_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `padicValInt`。
形式化陈述：of_ne_one_ne_zero {z : Int} (hp : p != 1) (hz : z != 0) : padicValInt p z 
= multiplicity (p : Int) z
参数：hp : p != 1；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValInt.eq_1`：∀ (p : ℕ) (z : ℤ), padicValInt p z = padicValNat p z.n
atAbs
· 使用定理 `padicValNat_def'`：padicValNat_def' {n : Nat} (hp : p != 1) (hn : n != 0)
 : padicValNat p n = multiplicity p n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natAbs_ne_zero`：∀ {a : ℤ}, a.natAbs ≠ 0 ↔ a ≠ 0
· 使用定理 `Int.multiplicity_natAbs`：Int.multiplicity_natAbs (a : Nat) (b : Int) : m
ultiplicity a b.natAbs = multiplicity (a : Int) b
-/
theorem of_ne_one_ne_zero {z : ℤ} (hp : p ≠ 1) (hz : z ≠ 0) :
    padicValInt p z = multiplicity (p : ℤ) z := by
  rw [padicValInt, padicValNat_def' hp (Int.natAbs_ne_zero.mpr hz)]
  apply Int.multiplicity_natAbs

/-- `padicValInt p 0` is `0` for any `p`. -/
@[simp]
/-
**padicValInt.zero** 是 Mathlib 中的一个定理，位于命名空间 `padicValInt`。
形式化陈述：∀ {p : ℕ}, padicValInt p 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_zero_right`：∀ (p : ℕ), padicValNat p 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`padicValInt p 0` is `0` for any `p`.
-/
protected theorem zero : padicValInt p 0 = 0 := by simp [padicValInt]

/-- `padicValInt p 1` is `0` for any `p`. -/
@[simp]
/-
**padicValInt.one** 是 Mathlib 中的一个定理，位于命名空间 `padicValInt`。
形式化陈述：∀ {p : ℕ}, padicValInt p 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_of_isUnit`：∀ {u : ℤ}, IsUnit u → u.natAbs = 1
· 使用定理 `padicValNat_one_right`：∀ (p : ℕ), padicValNat p 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`padicValInt p 1` is `0` for any `p`.
-/
protected theorem one : padicValInt p 1 = 0 := by simp [padicValInt]

/-- The `p`-adic value of a natural is its `p`-adic value as an integer. -/
@[simp]
/-
**padicValInt.of_nat** 是 Mathlib 中的一个定理，位于命名空间 `padicValInt`。
形式化陈述：of_nat {n : Nat} : padicValInt p n = padicValNat p n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `p`-adic value of a natural is its `p`-adic value as an integer.
-/
theorem of_nat {n : ℕ} : padicValInt p n = padicValNat p n := by simp [padicValInt]

/-- If `p ≠ 0` and `p ≠ 1`, then `padicValInt p p` is `1`. -/
/-
**padicValInt.self** 是 Mathlib 中的一个定理，位于命名空间 `padicValInt`。
形式化陈述：self (hp : 1 < p) : padicValInt p p = 1
参数：hp : 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValInt.of_nat`：of_nat {n : Nat} : padicValInt p n = padicValNat p n
· 使用定理 `padicValNat.self`：∀ {p : ℕ}, 1 < p → padicValNat p p = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `p ≠ 0` and `p ≠ 1`, then `padicValInt p p` is `1`.
-/
theorem self (hp : 1 < p) : padicValInt p p = 1 := by simp [padicValNat.self hp]

@[simp]
/-
**padicValInt.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `padicValInt`。
形式化陈述：eq_zero_iff {z : Int} : padicValInt p z = 0 ↔ p = 1 ∨ z = 0 ∨ ¬(p : Int) ∣
 z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValInt.eq_1`：∀ (p : ℕ) (z : ℤ), padicValInt p z = padicValNat p z.n
atAbs
· 使用定理 `padicValNat.eq_zero_iff`：eq_zero_iff {n : Nat} : padicValNat p n = 0 ↔ p
 = 1 ∨ n = 0 ∨ ¬p ∣ n
· 使用定理 `Int.natAbs_eq_zero`：∀ {a : ℤ}, a.natAbs = 0 ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_dvd_left`：∀ {n : ℕ} {z : ℤ}, ↑n ∣ z ↔ n ∣ z.natAbs
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_zero_iff {z : ℤ} : padicValInt p z = 0 ↔ p = 1 ∨ z = 0 ∨ ¬(p : ℤ) ∣ z := by
  rw [padicValInt, padicValNat.eq_zero_iff, Int.natAbs_eq_zero, ← Int.ofNat_dvd_left]
/-
**padicValInt.eq_zero_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `padicValInt`。
形式化陈述：eq_zero_of_not_dvd {z : Int} (h : ¬(p : Int) ∣ z) : padicValInt p z = 0
参数：h : ¬(p : Int) ∣ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem eq_zero_of_not_dvd {z : ℤ} (h : ¬(p : ℤ) ∣ z) : padicValInt p z = 0 := by
  simp [h]

end padicValInt

/-- `padicValRat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.den`. If `q = 0` or `p = 1`, then `padicValRat p q` defaults to `0`. -/
/-
**padicValRat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：padicValRat (p : Nat) (q : Rat) : Int
参数：p : Nat；q : Rat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`padicValRat` defines the valuation of a rational `q` to be the valuation of `q.
num` minus the
valuation of `q.den`. If `q = 0` or `p = 1`, then `padicValRat p q` defaults to 
`0`.
-/
def padicValRat (p : ℕ) (q : ℚ) : ℤ :=
  padicValInt p q.num - padicValNat p q.den
/-
**padicValRat_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：padicValRat_def (p : Nat) (q : Rat) : padicValRat p q = padicValInt p q.nu
m - padicValNat p q.den
参数：p : Nat；q : Rat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma padicValRat_def (p : ℕ) (q : ℚ) :
    padicValRat p q = padicValInt p q.num - padicValNat p q.den :=
  rfl

namespace padicValRat

variable {p : ℕ}

/-- `padicValRat p q` is symmetric in `q`. -/
@[simp]
/-
**padicValRat.neg** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：∀ {p : ℕ} (q : ℚ), padicValRat p (-q) = padicValRat p q
参数：q : ℚ；-q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`padicValRat p q` is symmetric in `q`.
-/
protected theorem neg (q : ℚ) : padicValRat p (-q) = padicValRat p q := by
  simp [padicValRat, padicValInt]

/-- `padicValRat p 0` is `0` for any `p`. -/
@[simp]
/-
**padicValRat.zero** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：∀ {p : ℕ}, padicValRat p 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `padicValInt.zero`：∀ {p : ℕ}, padicValInt p 0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `padicValNat_one_right`：∀ (p : ℕ), padicValNat p 1 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`padicValRat p 0` is `0` for any `p`.
-/
protected theorem zero : padicValRat p 0 = 0 := by simp [padicValRat]

/-- `padicValRat p 1` is `0` for any `p`. -/
@[simp]
/-
**padicValRat.one** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：∀ {p : ℕ}, padicValRat p 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `padicValInt.one`：∀ {p : ℕ}, padicValInt p 1 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `padicValNat_one_right`：∀ (p : ℕ), padicValNat p 1 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`padicValRat p 1` is `0` for any `p`.
-/
protected theorem one : padicValRat p 1 = 0 := by simp [padicValRat]

/-- The `p`-adic value of an integer `z ≠ 0` is its `p`-adic value as a rational. -/
@[simp]
/-
**padicValRat.of_int** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：of_int {z : Int} : padicValRat p z = padicValInt p z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_one_right`：∀ (p : ℕ), padicValNat p 1 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `p`-adic value of an integer `z ≠ 0` is its `p`-adic value as a rational.
-/
theorem of_int {z : ℤ} : padicValRat p z = padicValInt p z := by simp [padicValRat]

/-- The `p`-adic value of an integer `z ≠ 0` is the multiplicity of `p` in `z`. -/
/-
**padicValRat.of_int_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：of_int_multiplicity {z : Int} (hp : p != 1) (hz : z != 0) : padicValRat p 
(z : Rat) = multiplicity (p : Int) z
参数：hp : p != 1；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValRat.of_int`：of_int {z : Int} : padicValRat p z = padicValInt p z
· 使用定理 `padicValInt.of_ne_one_ne_zero`：of_ne_one_ne_zero {z : Int} (hp : p != 1)
 (hz : z != 0) : padicValInt p z = multiplicity (p : Int) z

--- 原说明 ---
The `p`-adic value of an integer `z ≠ 0` is the multiplicity of `p` in `z`.
-/
theorem of_int_multiplicity {z : ℤ} (hp : p ≠ 1) (hz : z ≠ 0) :
    padicValRat p (z : ℚ) = multiplicity (p : ℤ) z := by
  rw [of_int, padicValInt.of_ne_one_ne_zero hp hz]
/-
**padicValRat.multiplicity_sub_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 `padicValR
at`。
形式化陈述：multiplicity_sub_multiplicity {q : Rat} (hp : p != 1) (hq : q != 0) : padi
cValRat p q = multiplicity (p : Int) q.num - multiplicity p q.den
参数：hp : p != 1；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValRat.eq_1`：∀ (p : ℕ) (q : ℚ), padicValRat p q = ↑(padicValInt p q
.num) - ↑(padicValNat p q.den)
· 使用定理 `padicValInt.of_ne_one_ne_zero`：of_ne_one_ne_zero {z : Int} (hp : p != 1)
 (hz : z != 0) : padicValInt p z = multiplicity (p : Int) z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Rat.num_ne_zero`：num_ne_zero {q : Rat} : q.num != 0 ↔ q != 0
· 使用定理 `padicValNat_def'`：padicValNat_def' {n : Nat} (hp : p != 1) (hn : n != 0)
 : padicValNat p n = multiplicity p n
· 使用定理 `Rat.den_ne_zero`：∀ (q : ℚ), q.den ≠ 0
-/
theorem multiplicity_sub_multiplicity {q : ℚ} (hp : p ≠ 1) (hq : q ≠ 0) :
    padicValRat p q = multiplicity (p : ℤ) q.num - multiplicity p q.den := by
  rw [padicValRat, padicValInt.of_ne_one_ne_zero hp (Rat.num_ne_zero.2 hq),
    padicValNat_def' hp q.den_ne_zero]

/-- The `p`-adic value of an integer `z ≠ 0` is its `p`-adic value as a rational. -/
@[simp]
/-
**padicValRat.of_nat** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：of_nat {n : Nat} : padicValRat p n = padicValNat p n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `padicValInt.of_nat`：of_nat {n : Nat} : padicValInt p n = padicValNat p n
· 使用定理 `padicValNat_one_right`：∀ (p : ℕ), padicValNat p 1 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `p`-adic value of an integer `z ≠ 0` is its `p`-adic value as a rational.
-/
theorem of_nat {n : ℕ} : padicValRat p n = padicValNat p n := by simp [padicValRat]

/-- If `p ≠ 0` and `p ≠ 1`, then `padicValRat p p` is `1`. -/
/-
**padicValRat.self** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：self (hp : 1 < p) : padicValRat p p = 1
参数：hp : 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValRat.of_nat`：of_nat {n : Nat} : padicValRat p n = padicValNat p n
· 使用定理 `padicValNat_base`：∀ {p : ℕ}, 1 < p → padicValNat p p = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `p ≠ 0` and `p ≠ 1`, then `padicValRat p p` is `1`.
-/
theorem self (hp : 1 < p) : padicValRat p p = 1 := by simp [hp]

end padicValRat

section padicValNat

variable {p : ℕ}

/-
**zero_le_padicValRat_of_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_le_padicValRat_of_nat (n : Nat) : 0 <= padicValRat p n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValRat.of_nat`：of_nat {n : Nat} : padicValRat p n = padicValNat p n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem zero_le_padicValRat_of_nat (n : ℕ) : 0 ≤ padicValRat p n := by simp

/-- `padicValRat` coincides with `padicValNat`. -/
@[norm_cast]
/-
**padicValRat_of_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValRat_of_nat (n : Nat) : ↑(padicValNat p n) = padicValRat p n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValRat.of_nat`：of_nat {n : Nat} : padicValRat p n = padicValNat p n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`padicValRat` coincides with `padicValNat`.
-/
theorem padicValRat_of_nat (n : ℕ) : ↑(padicValNat p n) = padicValRat p n := by simp

@[simp]
/-
**padicValNat_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_self [Fact p.Prime] : padicValNat p p = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_def`：padicValNat_def [hp : Fact p.Prime] {n : Nat} (hn : n !
= 0) : padicValNat p n = multiplicity p n
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `multiplicity_self`：multiplicity_self {a : α} : multiplicity a a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem padicValNat_self [Fact p.Prime] : padicValNat p p = 1 := by
  rw [padicValNat_def (@Fact.out p.Prime).ne_zero]
  simp
/-
**one_le_padicValNat_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_padicValNat_of_dvd {n : Nat} [hp : Fact p.Prime] (hn : n != 0) (div
 : p ∣ n) : 1 <= padicValNat p n
参数：hn : n != 0；div : p ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `padicValNat_eq_emultiplicity`：padicValNat_eq_emultiplicity [hp : Fact p.
Prime] {n : Nat} (hn : n != 0) : padicValNat p n = emultiplicity p n
· 使用定理 `pow_dvd_iff_le_emultiplicity`：pow_dvd_iff_le_emultiplicity {k : Nat} : a
 ^ k ∣ b ↔ k <= emultiplicity a b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem one_le_padicValNat_of_dvd {n : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) (div : p ∣ n) :
    1 ≤ padicValNat p n := by
  rwa [← ENat.natCast_le_natCast, padicValNat_eq_emultiplicity hn,
    ← pow_dvd_iff_le_emultiplicity, pow_one]
/-
**dvd_iff_padicValNat_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_iff_padicValNat_ne_zero {p n : Nat} [Fact p.Prime] (hn0 : n != 0) : p 
∣ n ↔ padicValNat p n != 0
参数：hn0 : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `one_le_padicValNat_of_dvd`：one_le_padicValNat_of_dvd {n : Nat} [hp : Fac
t p.Prime] (hn : n != 0) (div : p ∣ n) : 1 <= padicValNat p n
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `padicValNat.eq_zero_of_not_dvd`：eq_zero_of_not_dvd {n : Nat} (h : ¬p ∣ n
) : padicValNat p n = 0
-/
theorem dvd_iff_padicValNat_ne_zero {p n : ℕ} [Fact p.Prime] (hn0 : n ≠ 0) :
    p ∣ n ↔ padicValNat p n ≠ 0 :=
  ⟨fun h => one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hn0 h), fun h =>
    Classical.not_not.1 (mt padicValNat.eq_zero_of_not_dvd h)⟩

end padicValNat

namespace padicValRat

variable {p : ℕ} [hp : Fact p.Prime]

/-- The multiplicity of `p : ℕ` in `a : ℤ` is finite exactly when `a ≠ 0`. -/
/-
**padicValRat.finite_int_prime_iff** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：finite_int_prime_iff {a : Int} : FiniteMultiplicity (p : Int) a ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The multiplicity of `p : ℕ` in `a : ℤ` is finite exactly when `a ≠ 0`.
-/
theorem finite_int_prime_iff {a : ℤ} : FiniteMultiplicity (p : ℤ) a ↔ a ≠ 0 := by
  simp [Int.finiteMultiplicity_iff, hp.1.ne_one]

/-- A rewrite lemma for `padicValRat p q` when `q` is expressed in terms of `Rat.mk`. -/
/-
**padicValRat.defn** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：∀ (p : ℕ) [hp : Fact (Nat.Prime p)] {q : ℚ} {n d : ℤ},   q ≠ 0 → q = Rat.d
ivInt n d → padicValRat p q = ↑(multiplicity (↑p) n) - ↑(multiplicity (↑p) d)
参数：p : ℕ；Nat.Prime p；multiplicity (↑p) n；multiplicity (↑p) d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.mk_denom_ne_zero_of_ne_zero`：mk_denom_ne_zero_of_ne_zero {q : Rat} {
n d : Int} (hq : q != 0) (hqnd : q = n /. d) : d != 0
· 使用定理 `Rat.num_den_mk`：num_den_mk {q : Rat} {n d : Int} (hd : d != 0) (qdf : q 
= n /. d) : exists c : Int, n = c * q.num ∧ d = c * q.den
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValRat.multiplicity_sub_multiplicity`：multiplicity_sub_multiplicity
 {q : Rat} (hp : p != 1) (hq : q != 0) : padicValRat p q = multiplicity (p : Int
) q.num - multiplicity p q.den
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `multiplicity_mul`：multiplicity_mul {p a b : α} (hp : Prime p) (hfin : Fi
niteMultiplicity p (a * b)) : multiplicity p (a * b) = multiplicity p a + multip
licity…
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Int.natCast_multiplicity`：Int.natCast_multiplicity (a b : Nat) : multipl
icity (a : Int) (b : Int) = multiplicity a b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
A rewrite lemma for `padicValRat p q` when `q` is expressed in terms of `Rat.mk`
.
-/
protected theorem defn (p : ℕ) [hp : Fact p.Prime] {q : ℚ} {n d : ℤ} (hqz : q ≠ 0)
    (qdf : q = n /. d) :
    padicValRat p q = multiplicity (p : ℤ) n - multiplicity (p : ℤ) d := by
  have hd : d ≠ 0 := Rat.mk_denom_ne_zero_of_ne_zero hqz qdf
  let ⟨c, hc1, hc2⟩ := Rat.num_den_mk hd qdf
  rw [padicValRat.multiplicity_sub_multiplicity hp.1.ne_one hqz]
  simp only [hc1, hc2]
  rw [multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1),
    multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1)]
  · rw [Nat.cast_add, Nat.cast_add]
    simp_rw [Int.natCast_multiplicity p q.den]
    ring
  · simpa [finite_int_prime_iff, hc2] using hd
  · simpa [finite_int_prime_iff, hqz, hc2] using hd

/-- A rewrite lemma for `padicValRat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
/-
**padicValRat.mul** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ}, q ≠ 0 → r ≠ 0 → padicValRat
 p (q * r) = padicValRat p q + padicValRat p r
参数：Nat.Prime p；q * r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.mul_eq_mkRat`：mul_eq_mkRat (q r : Rat) : q * r = mkRat (q.num * r.nu
m) (q.den * r.den)
· 使用引理 `Rat.mkRat_eq_divInt`：mkRat_eq_divInt (n d) : mkRat n d = n /. d
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `padicValRat.defn`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)] {q : ℚ} {n d : ℤ},
   q ≠ 0 → q = Rat.divInt n d → padicValRat p q = ↑(multiplicity (↑p) n) - ↑(mul
tiplic…
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `multiplicity_mul`：multiplicity_mul {p a b : α} (hp : Prime p) (hfin : Fi
niteMultiplicity p (a * b)) : multiplicity p (a * b) = multiplicity p a + multip
licity…
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
A rewrite lemma for `padicValRat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`.
-/
protected theorem mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q * r) = padicValRat p q + padicValRat p r := by
  have : q * r = (q.num * r.num) /. (q.den * r.den) := by
    rw [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt, Nat.cast_mul]
  have hq' : q.num /. q.den ≠ 0 := by rwa [Rat.num_divInt_den]
  have hr' : r.num /. r.den ≠ 0 := by rwa [Rat.num_divInt_den]
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.1
  rw [padicValRat.defn p (mul_ne_zero hq hr) this]
  conv_rhs =>
    rw [← q.num_divInt_den, padicValRat.defn p hq', ← r.num_divInt_den, padicValRat.defn p hr']
  rw [multiplicity_mul hp', multiplicity_mul hp', Nat.cast_add, Nat.cast_add]
  · ring
  · simp [finite_int_prime_iff]
  · simp [finite_int_prime_iff, hq, hr]

/-- A rewrite lemma for `padicValRat p (q^k)`. -/
@[simp]
/-
**padicValRat.pow** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ) {k : ℕ}, padicValRat p (q ^ k)
 = ↑k * padicValRat p q
参数：Nat.Prime p；q : ℚ；q ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `padicValRat.one`：∀ {p : ℕ}, padicValRat p 1 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `padicValRat.zero`：∀ {p : ℕ}, padicValRat p 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `padicValRat.mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ}, q ≠ 0 → 
r ≠ 0 → padicValRat p (q * r) = padicValRat p q + padicValRat p r
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
A rewrite lemma for `padicValRat p (q^k)`.
-/
protected theorem pow (q : ℚ) {k : ℕ} :
    padicValRat p (q ^ k) = k * padicValRat p q := by
  obtain rfl | hq := eq_or_ne q 0
  · cases k <;> simp
  induction k <;>
    simp [*, padicValRat.mul hq (pow_ne_zero _ hq), _root_.pow_succ', add_mul, add_comm]

/-- A rewrite lemma for `padicValRat p (q⁻¹)`. -/
@[simp]
/-
**padicValRat.inv** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ), padicValRat p q⁻¹ = -padicVal
Rat p q
参数：Nat.Prime p；q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `padicValRat.zero`：∀ {p : ℕ}, padicValRat p 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicValRat.mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ}, q ≠ 0 → 
r ≠ 0 → padicValRat p (q * r) = padicValRat p q + padicValRat p r
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `padicValRat.one`：∀ {p : ℕ}, padicValRat p 1 = 0

--- 原说明 ---
A rewrite lemma for `padicValRat p (q⁻¹)`.
-/
protected theorem inv (q : ℚ) : padicValRat p q⁻¹ = -padicValRat p q := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [eq_neg_iff_add_eq_zero, ← padicValRat.mul (inv_ne_zero hq) hq, inv_mul_cancel₀ hq,
      padicValRat.one]

@[simp]
/-
**padicValRat.zpow** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ) {k : ℤ}, padicValRat p (q ^ k)
 = k * padicValRat p q
参数：Nat.Prime p；q : ℚ；q ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `padicValRat.pow`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ) {k : ℕ}, pa
dicValRat p (q ^ k) = ↑k * padicValRat p q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `padicValRat.inv`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ), padicValRa
t p q⁻¹ = -padicValRat p q
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
protected theorem zpow (q : ℚ) {k : ℤ} :
    padicValRat p (q ^ k) = k * padicValRat p q := by
  induction k using Int.negInduction <;> simp

/-- A rewrite lemma for `padicValRat p (q / r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
/-
**padicValRat.div** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ}, q ≠ 0 → r ≠ 0 → padicValRat
 p (q / r) = padicValRat p q - padicValRat p r
参数：Nat.Prime p；q / r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `padicValRat.mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ}, q ≠ 0 → 
r ≠ 0 → padicValRat p (q * r) = padicValRat p q + padicValRat p r
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `padicValRat.inv`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ), padicValRa
t p q⁻¹ = -padicValRat p q
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b

--- 原说明 ---
A rewrite lemma for `padicValRat p (q / r)` with conditions `q ≠ 0`, `r ≠ 0`.
-/
protected theorem div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q / r) = padicValRat p q - padicValRat p r := by
  rw [div_eq_mul_inv, padicValRat.mul hq (inv_ne_zero hr), padicValRat.inv r, sub_eq_add_neg]

/-- A condition for `padicValRat p (n₁ / d₁) ≤ padicValRat p (n₂ / d₂)`, in terms of
divisibility by `p^n`. -/
/-
**padicValRat.padicValRat_le_padicValRat_iff** 是 Mathlib 中的一个定理，位于命名空间 `padicVal
Rat`。
形式化陈述：padicValRat_le_padicValRat_iff {n₁ n₂ d₁ d₂ : Int} (hn₁ : n₁ != 0) (hn₂ : 
n₂ != 0) (hd₁ : d₁ != 0) (hd₂ : d₂ != 0) : padicValRat p (n₁ /. d₁) <= padicValR
at p (n₂ /. d₂) ↔ forall n : Nat, (p : Int) ^ n ∣ n₁ * d₂ -> (p : Int) ^ n ∣ n₂ 
* d₁
参数：hn₁ : n₁ != 0；hn₂ : n₂ != 0；hd₁ : d₁ != 0；hd₂ : d₂ != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `padicValRat.finite_int_prime_iff`：finite_int_prime_iff {a : Int} : Finit
eMultiplicity (p : Int) a ↔ a != 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValRat.defn`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)] {q : ℚ} {n d : ℤ},
   q ≠ 0 → q = Rat.divInt n d → padicValRat p q = ↑(multiplicity (↑p) n) - ↑(mul
tiplic…
· 使用定理 `Rat.divInt_ne_zero_of_ne_zero`：divInt_ne_zero_of_ne_zero {n d : Int} (h 
: n != 0) (hd : d != 0) : n /. d != 0
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `le_sub_iff_add_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a ≤ c - b ↔ a + b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `multiplicity_mul`：multiplicity_mul {p a b : α} (hp : Prime p) (hfin : Fi
niteMultiplicity p (a * b)) : multiplicity p (a * b) = multiplicity p a + multip
licity…
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `FiniteMultiplicity.multiplicity_le_multiplicity_iff`：FiniteMultiplicity.
multiplicity_le_multiplicity_iff {c d : β} (hab : FiniteMultiplicity a b) (hcd :
 FiniteMultiplicity c d) : multiplicity a…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A condition for `padicValRat p (n₁ / d₁) ≤ padicValRat p (n₂ / d₂)`, in terms of
divisibility by `p^n`.
-/
theorem padicValRat_le_padicValRat_iff {n₁ n₂ d₁ d₂ : ℤ} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    padicValRat p (n₁ /. d₁) ≤ padicValRat p (n₂ /. d₂) ↔
      ∀ n : ℕ, (p : ℤ) ^ n ∣ n₁ * d₂ → (p : ℤ) ^ n ∣ n₂ * d₁ := by
  have hf1 : FiniteMultiplicity (p : ℤ) (n₁ * d₂) := finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂)
  have hf2 : FiniteMultiplicity (p : ℤ) (n₂ * d₁) := finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁)
  conv =>
    lhs
    rw [padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₁ hd₁) rfl,
      padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₂ hd₂) rfl, sub_le_iff_le_add', ←
      add_sub_assoc, le_sub_iff_add_le]
    norm_cast
    rw [← multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1) hf1, add_comm,
        ← multiplicity_mul (Nat.prime_iff_prime_int.1 hp.1) hf2,
        hf1.multiplicity_le_multiplicity_iff hf2]

/-- Sufficient conditions to show that the `p`-adic valuation of `q` is less than or equal to the
`p`-adic valuation of `q + r`. -/
/-
**padicValRat.le_padicValRat_add_of_le** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：le_padicValRat_add_of_le {q r : Rat} (hqr : q + r != 0) (h : padicValRat p
 q <= padicValRat p r) : padicValRat p q <= padicValRat p (q + r)
参数：hqr : q + r != 0；h : padicValRat p q <= padicValRat p r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `padicValRat.zero`：∀ {p : ℕ}, padicValRat p 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Rat.num_ne_zero`：num_ne_zero {q : Rat} : q.num != 0 ↔ q != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
· 使用定理 `Rat.add_num_den`：add_num_den (q r : Rat) : q + r = (q.num * r.den + q.de
n * r.num : Int) /. (↑q.den * ↑r.den : Int)
· 使用定理 `Rat.mk_num_ne_zero_of_ne_zero`：mk_num_ne_zero_of_ne_zero {q : Rat} {n d 
: Int} (hq : q != 0) (hqnd : q = n /. d) : n != 0
· 使用定理 `Rat.num_divInt_den`：∀ (a : ℚ), Rat.divInt a.num ↑a.den = a
· 使用定理 `padicValRat.padicValRat_le_padicValRat_iff`：padicValRat_le_padicValRat_i
ff {n₁ n₂ d₁ d₂ : Int} (hn₁ : n₁ != 0) (hn₂ : n₂ != 0) (hd₁ : d₁ != 0) (hd₂ : d₂
 != 0) : padicValRat p (n₁ /. d₁…
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `emultiplicity_le_emultiplicity_iff`：emultiplicity_le_emultiplicity_iff {
c d : β} : emultiplicity a b <= emultiplicity c d ↔ forall n : Nat, a ^ n ∣ b ->
 c ^ n ∣ d
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `emultiplicity_mul`：emultiplicity_mul {p a b : α} (hp : Prime p) : emulti
plicity p (a * b) = emultiplicity p a + emultiplicity p b
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
Sufficient conditions to show that the `p`-adic valuation of `q` is less than or
 equal to the
`p`-adic valuation of `q + r`.
-/
theorem le_padicValRat_add_of_le {q r : ℚ} (hqr : q + r ≠ 0)
    (h : padicValRat p q ≤ padicValRat p r) : padicValRat p q ≤ padicValRat p (q + r) :=
  if hq : q = 0 then by simpa [hq] using h
  else
    if hr : r = 0 then by simp [hr]
    else by
      have hqn : q.num ≠ 0 := Rat.num_ne_zero.2 hq
      have hqd : (q.den : ℤ) ≠ 0 := mod_cast Rat.den_nz _
      have hrn : r.num ≠ 0 := Rat.num_ne_zero.2 hr
      have hrd : (r.den : ℤ) ≠ 0 := mod_cast Rat.den_nz _
      have hqreq : q + r = (q.num * r.den + q.den * r.num) /. (q.den * r.den) := Rat.add_num_den _ _
      have hqrd : q.num * r.den + q.den * r.num ≠ 0 := Rat.mk_num_ne_zero_of_ne_zero hqr hqreq
      conv_lhs => rw [← q.num_divInt_den]
      rw [hqreq, padicValRat_le_padicValRat_iff hqn hqrd hqd (mul_ne_zero hqd hrd), ←
        emultiplicity_le_emultiplicity_iff, mul_left_comm,
        emultiplicity_mul (Nat.prime_iff_prime_int.1 hp.1), add_mul]
      rw [← q.num_divInt_den, ← r.num_divInt_den, padicValRat_le_padicValRat_iff hqn hrn hqd hrd, ←
        emultiplicity_le_emultiplicity_iff] at h
      calc
        _ ≤ min (emultiplicity ↑p (q.num * r.den * q.den))
                (emultiplicity ↑p (q.den * r.num * q.den)) :=
          le_min
            (by rw [emultiplicity_mul (a := _ * _) (Nat.prime_iff_prime_int.1 hp.1), add_comm])
            (by grw [mul_assoc, emultiplicity_mul (b := _ * _) (Nat.prime_iff_prime_int.1 hp.1), h])
        _ ≤ _ := min_le_emultiplicity_add

/-- The minimum of the valuations of `q` and `r` is at most the valuation of `q + r`. -/
/-
**padicValRat.min_le_padicValRat_add** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：min_le_padicValRat_add {q r : Rat} (hqr : q + r != 0) : min (padicValRat p
 q) (padicValRat p r) <= padicValRat p (q + r)
参数：hqr : q + r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `padicValRat.le_padicValRat_add_of_le`：le_padicValRat_add_of_le {q r : Ra
t} (hqr : q + r != 0) (h : padicValRat p q <= padicValRat p r) : padicValRat p q
 <= padicValRat p (q + r)
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
The minimum of the valuations of `q` and `r` is at most the valuation of `q + r`
.
-/
theorem min_le_padicValRat_add {q r : ℚ} (hqr : q + r ≠ 0) :
    min (padicValRat p q) (padicValRat p r) ≤ padicValRat p (q + r) :=
  (le_total (padicValRat p q) (padicValRat p r)).elim
  (fun h => by rw [min_eq_left h]; exact le_padicValRat_add_of_le hqr h)
  (fun h => by rw [min_eq_right h, add_comm]; exact le_padicValRat_add_of_le (by rwa [add_comm]) h)

/-- Ultrametric property of a p-adic valuation. -/
/-
**padicValRat.add_eq_min** 是 Mathlib 中的一个引理，位于命名空间 `padicValRat`。
形式化陈述：add_eq_min {q r : Rat} (hqr : q + r != 0) (hq : q != 0) (hr : r != 0) (hva
l : padicValRat p q != padicValRat p r) : padicValRat p (q + r) = min (padicValR
at p q) (padicValRat p r)
参数：hqr : q + r != 0；hq : q != 0；hr : r != 0；hval : padicValRat p q != padicValRa
t p r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicValRat.min_le_padicValRat_add`：min_le_padicValRat_add {q r : Rat} (
hqr : q + r != 0) : min (padicValRat p q) (padicValRat p r) <= padicValRat p (q 
+ r)
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValRat.neg`：∀ {p : ℕ} (q : ℚ), padicValRat p (-q) = padicValRat p q
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
Ultrametric property of a p-adic valuation.
-/
lemma add_eq_min {q r : ℚ} (hqr : q + r ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hval : padicValRat p q ≠ padicValRat p r) :
    padicValRat p (q + r) = min (padicValRat p q) (padicValRat p r) := by
  have h1 := min_le_padicValRat_add (p := p) hqr
  have h2 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right q r) hq)
  have h3 := min_le_padicValRat_add (p := p) (ne_of_eq_of_ne (add_neg_cancel_right r q) hr)
  rw [add_neg_cancel_right, padicValRat.neg] at h2 h3
  rw [add_comm] at h3
  omega
/-
**padicValRat.add_eq_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `padicValRat`。
形式化陈述：add_eq_of_lt {q r : Rat} (hqr : q + r != 0) (hq : q != 0) (hr : r != 0) (h
val : padicValRat p q < padicValRat p r) : padicValRat p (q + r) = padicValRat p
 q
参数：hqr : q + r != 0；hq : q != 0；hr : r != 0；hval : padicValRat p q < padicValRat
 p r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `padicValRat.add_eq_min`：add_eq_min {q r : Rat} (hqr : q + r != 0) (hq : 
q != 0) (hr : r != 0) (hval : padicValRat p q != padicValRat p r) : padicValRat 
p (q + r) = …
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma add_eq_of_lt {q r : ℚ} (hqr : q + r ≠ 0)
    (hq : q ≠ 0) (hr : r ≠ 0) (hval : padicValRat p q < padicValRat p r) :
    padicValRat p (q + r) = padicValRat p q := by
  rw [add_eq_min hqr hq hr (ne_of_lt hval), min_eq_left (le_of_lt hval)]
/-
**padicValRat.lt_add_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `padicValRat`。
形式化陈述：lt_add_of_lt {q r₁ r₂ : Rat} (hqr : r₁ + r₂ != 0) (hval₁ : padicValRat p q
 < padicValRat p r₁) (hval₂ : padicValRat p q < padicValRat p r₂) : padicValRat 
p q < padicValRat p (r₁ + r₂)
参数：hqr : r₁ + r₂ != 0；hval₁ : padicValRat p q < padicValRat p r₁；hval₂ : padicVa
lRat p q < padicValRat p r₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `padicValRat.min_le_padicValRat_add`：min_le_padicValRat_add {q r : Rat} (
hqr : q + r != 0) : min (padicValRat p q) (padicValRat p r) <= padicValRat p (q 
+ r)
-/
lemma lt_add_of_lt {q r₁ r₂ : ℚ} (hqr : r₁ + r₂ ≠ 0)
    (hval₁ : padicValRat p q < padicValRat p r₁) (hval₂ : padicValRat p q < padicValRat p r₂) :
    padicValRat p q < padicValRat p (r₁ + r₂) :=
  lt_of_lt_of_le (lt_min hval₁ hval₂) (padicValRat.min_le_padicValRat_add hqr)
/-
**padicValRat.self_pow_inv** 是 Mathlib 中的一个引理，位于命名空间 `padicValRat`。
形式化陈述：self_pow_inv (r : Nat) : padicValRat p ((p : Rat) ^ r)⁻¹ = -r
参数：r : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValRat.inv`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ), padicValRa
t p q⁻¹ = -padicValRat p q
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `padicValRat.pow`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ) {k : ℕ}, pa
dicValRat p (q ^ k) = ↑k * padicValRat p q
· 使用定理 `padicValRat.self`：self (hp : 1 < p) : padicValRat p p = 1
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma self_pow_inv (r : ℕ) : padicValRat p ((p : ℚ) ^ r)⁻¹ = -r := by
  rw [padicValRat.inv, neg_inj, padicValRat.pow p, padicValRat.self hp.elim.one_lt, mul_one]

/-- A finite sum of rationals with positive `p`-adic valuation has positive `p`-adic valuation
(if the sum is non-zero). -/
/-
**padicValRat.sum_pos_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：sum_pos_of_pos {n : Nat} {F : Nat -> Rat} (hF : forall i, i < n -> 0 < pad
icValRat p (F i)) (hn0 : ∑ i in Finset.range n, F i != 0) : 0 < padicValRat p (∑
 i in Finset.range n, F i)
参数：hF : forall i, i < n -> 0 < padicValRat p (F i)；hn0 : ∑ i in Finset.range n, 
F i != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `padicValRat.min_le_padicValRat_add`：min_le_padicValRat_add {q r : Rat} (
hqr : q + r != 0) : min (padicValRat p q) (padicValRat p r) <= padicValRat p (q 
+ r)

--- 原说明 ---
A finite sum of rationals with positive `p`-adic valuation has positive `p`-adic
 valuation
(if the sum is non-zero).
-/
theorem sum_pos_of_pos {n : ℕ} {F : ℕ → ℚ} (hF : ∀ i, i < n → 0 < padicValRat p (F i))
    (hn0 : ∑ i ∈ Finset.range n, F i ≠ 0) : 0 < padicValRat p (∑ i ∈ Finset.range n, F i) := by
  induction n with
  | zero => exact False.elim (hn0 rfl)
  | succ d hd =>
    rw [Finset.sum_range_succ] at hn0 ⊢
    by_cases h : ∑ x ∈ Finset.range d, F x = 0
    · rw [h, zero_add]
      exact hF d (lt_add_one _)
    · refine lt_of_lt_of_le ?_ (min_le_padicValRat_add hn0)
      refine lt_min (hd (fun i hi => ?_) h) (hF d (lt_add_one _))
      exact hF _ (lt_trans hi (lt_add_one _))

/-- If the p-adic valuation of a finite set of positive rationals is greater than a given rational
number, then the p-adic valuation of their sum is also greater than the same rational number. -/
/-
**padicValRat.lt_sum_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `padicValRat`。
形式化陈述：lt_sum_of_lt {p j : Nat} [hp : Fact (Nat.Prime p)] {F : Nat -> Rat} {S : F
inset Nat} (hS : S.Nonempty) (hF : forall i, i in S -> padicValRat p (F j) < pad
icValRat p (F i)) (hn1 : forall i : Nat, 0 < F i) : padicValRat p (F j) < padicV
alRat p (∑ i in S, F i)
参数：Nat.Prime p；hS : S.Nonempty；hF : forall i, i in S -> padicValRat p (F j) < pa
dicValRat p (F i)；hn1 : forall i : Nat, 0 < F i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用引理 `padicValRat.lt_add_of_lt`：lt_add_of_lt {q r₁ r₂ : Rat} (hqr : r₁ + r₂ !=
 0) (hval₁ : padicValRat p q < padicValRat p r₁) (hval₂ : padicValRat p q < padi
cValRat p r₂) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s

--- 原说明 ---
If the p-adic valuation of a finite set of positive rationals is greater than a 
given rational
number, then the p-adic valuation of their sum is also greater than the same rat
ional number.
-/
theorem lt_sum_of_lt {p j : ℕ} [hp : Fact (Nat.Prime p)] {F : ℕ → ℚ} {S : Finset ℕ}
    (hS : S.Nonempty) (hF : ∀ i, i ∈ S → padicValRat p (F j) < padicValRat p (F i))
    (hn1 : ∀ i : ℕ, 0 < F i) : padicValRat p (F j) < padicValRat p (∑ i ∈ S, F i) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton k =>
    rw [Finset.sum_singleton]
    exact hF k (by simp)
  | cons s S' Hnot Hne Hind =>
    rw [Finset.cons_eq_insert, Finset.sum_insert Hnot]
    exact padicValRat.lt_add_of_lt
      (ne_of_gt (add_pos (hn1 s) (Finset.sum_pos (fun i _ => hn1 i) Hne)))
      (hF _ (by simp [Finset.mem_insert, true_or]))
      (Hind (fun i hi => hF _ (by rw [Finset.cons_eq_insert, Finset.mem_insert]; exact Or.inr hi)))

end padicValRat

namespace padicValNat

variable {p a b : ℕ} [hp : Fact p.Prime]

/-- A rewrite lemma for `padicValNat p (a * b)` with conditions `a ≠ 0`, `b ≠ 0`. -/
/-
**padicValNat.mul** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 → padicValNat p (a 
* b) = padicValNat p a + padicValNat p b
参数：Nat.Prime p；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `padicValRat.mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ}, q ≠ 0 → 
r ≠ 0 → padicValRat p (q * r) = padicValRat p q + padicValRat p r

--- 原说明 ---
A rewrite lemma for `padicValNat p (a * b)` with conditions `a ≠ 0`, `b ≠ 0`.
-/
protected theorem mul : a ≠ 0 → b ≠ 0 → padicValNat p (a * b) = padicValNat p a + padicValNat p b :=
  mod_cast padicValRat.mul (p := p) (q := a) (r := b)
/-
**padicValNat.div_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], b ∣ a → padicValNat p (a / b) = p
adicValNat p a - padicValNat p b
参数：Nat.Prime p；a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `padicValNat_zero_right`：∀ (p : ℕ), padicValNat p 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.mul_div_cancel`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `padicValNat.mul`：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 
→ padicValNat p (a * b) = padicValNat p a + padicValNat p b
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
-/
protected theorem div_of_dvd (h : b ∣ a) :
    padicValNat p (a / b) = padicValNat p a - padicValNat p b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  obtain ⟨k, rfl⟩ := h
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha
  rw [mul_comm, k.mul_div_cancel hb.bot_lt, padicValNat.mul hk hb, Nat.add_sub_cancel]

/-- Dividing out by a prime factor reduces the `padicValNat` by `1`. -/
/-
**padicValNat.div** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：∀ {p b : ℕ} [hp : Fact (Nat.Prime p)], p ∣ b → padicValNat p (b / p) = pad
icValNat p b - 1
参数：Nat.Prime p；b / p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat.div_of_dvd`：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], b ∣ a →
 padicValNat p (a / b) = padicValNat p a - padicValNat p b
· 使用定理 `padicValNat_self`：padicValNat_self [Fact p.Prime] : padicValNat p p = 1

--- 原说明 ---
Dividing out by a prime factor reduces the `padicValNat` by `1`.
-/
protected theorem div (dvd : p ∣ b) : padicValNat p (b / p) = padicValNat p b - 1 := by
  rw [padicValNat.div_of_dvd dvd, padicValNat_self]

/-- A version of `padicValRat.pow` for `padicValNat`. -/
@[simp]
/-
**padicValNat.pow** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (a n : ℕ), padicValNat p (a ^ n) = n *
 padicValNat p a
参数：Nat.Prime p；a n : ℕ；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValRat_of_nat`：padicValRat_of_nat (n : Nat) : ↑(padicValNat p n) = 
padicValRat p n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `padicValRat.pow`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ) {k : ℕ}, pa
dicValRat p (q ^ k) = ↑k * padicValRat p q

--- 原说明 ---
A version of `padicValRat.pow` for `padicValNat`.
-/
protected theorem pow (a n : ℕ) : padicValNat p (a ^ n) = n * padicValNat p a := by
  simpa only [← @Nat.cast_inj ℤ, push_cast] using padicValRat.pow a
/-
**padicValNat.prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (n : ℕ), padicValNat p (p ^ n) = n
参数：Nat.Prime p；n : ℕ；p ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat.pow`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (a n : ℕ), padicVal
Nat p (a ^ n) = n * padicValNat p a
· 使用定理 `padicValNat_self`：padicValNat_self [Fact p.Prime] : padicValNat p p = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
protected theorem prime_pow (n : ℕ) : padicValNat p (p ^ n) = n := by
  rw [padicValNat.pow p, padicValNat_self, mul_one]
/-
**padicValNat.div_pow** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], p ^ a ∣ b → padicValNat p (b / p 
^ a) = padicValNat p b - a
参数：Nat.Prime p；b / p ^ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat.div_of_dvd`：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], b ∣ a →
 padicValNat p (a / b) = padicValNat p a - padicValNat p b
· 使用定理 `padicValNat.prime_pow`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (n : ℕ), padi
cValNat p (p ^ n) = n
-/
protected theorem div_pow (dvd : p ^ a ∣ b) : padicValNat p (b / p ^ a) = padicValNat p b - a := by
  rw [padicValNat.div_of_dvd dvd, padicValNat.prime_pow]
/-
**padicValNat.div'** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {m : ℕ}, p.Coprime m → ∀ {b : ℕ}, m ∣ 
b → padicValNat p (b / m) = padicValNat p b
参数：Nat.Prime p；b / m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat.div_of_dvd`：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], b ∣ a →
 padicValNat p (a / b) = padicValNat p a - padicValNat p b
· 使用定理 `padicValNat.eq_zero_of_not_dvd`：eq_zero_of_not_dvd {n : Nat} (h : ¬p ∣ n
) : padicValNat p n = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.sub_zero`：∀ (n : ℕ), n - 0 = n
-/
protected theorem div' {m : ℕ} (cpm : Coprime p m) {b : ℕ} (dvd : m ∣ b) :
    padicValNat p (b / m) = padicValNat p b := by
  rw [padicValNat.div_of_dvd dvd, eq_zero_of_not_dvd (hp.out.coprime_iff_not_dvd.mp cpm),
    Nat.sub_zero]

end padicValNat

section padicValNat

variable {p : ℕ}

/-
**dvd_of_one_le_padicValNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_of_one_le_padicValNat {n : Nat} (hp : 1 <= padicValNat p n) : p ∣ n
参数：hp : 1 <= padicValNat p n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat.eq_zero_of_not_dvd`：eq_zero_of_not_dvd {n : Nat} (h : ¬p ∣ n
) : padicValNat p n = 0
-/
theorem dvd_of_one_le_padicValNat {n : ℕ} (hp : 1 ≤ padicValNat p n) : p ∣ n := by
  by_contra h
  rw [padicValNat.eq_zero_of_not_dvd h] at hp
  exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp)
/-
**padicValNat_dvd_iff_le_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_dvd_iff_le_of_ne_one {p : Nat} (hp : p != 1) {a n : Nat} (ha :
 a != 0) : p ^ n ∣ a ↔ n <= padicValNat p a
参数：hp : p != 1；ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_dvd_iff_le_emultiplicity`：pow_dvd_iff_le_emultiplicity {k : Nat} : a
 ^ k ∣ b ↔ k <= emultiplicity a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicValNat_eq_emultiplicity_of_ne_one`：padicValNat_eq_emultiplicity_of_
ne_one (hp : p != 1) {n : Nat} (hn : n != 0) : padicValNat p n = emultiplicity p
 n
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem padicValNat_dvd_iff_le_of_ne_one {p : ℕ} (hp : p ≠ 1) {a n : ℕ} (ha : a ≠ 0) :
    p ^ n ∣ a ↔ n ≤ padicValNat p a := by
  rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity_of_ne_one hp ha, Nat.cast_le]
/-
**padicValNat_dvd_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_dvd_iff_le [hp : Fact p.Prime] {a n : Nat} (ha : a != 0) : p ^
 n ∣ a ↔ n <= padicValNat p a
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicValNat_dvd_iff_le_of_ne_one`：padicValNat_dvd_iff_le_of_ne_one {p : 
Nat} (hp : p != 1) {a n : Nat} (ha : a != 0) : p ^ n ∣ a ↔ n <= padicValNat p a
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem padicValNat_dvd_iff_le [hp : Fact p.Prime] {a n : ℕ} (ha : a ≠ 0) :
    p ^ n ∣ a ↔ n ≤ padicValNat p a :=
  padicValNat_dvd_iff_le_of_ne_one hp.out.ne_one ha
/-
**padicValNat_dvd_iff_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_dvd_iff_of_ne_one {p : Nat} (hp : p != 1) (n a : Nat) : p ^ n 
∣ a ↔ a = 0 ∨ n <= padicValNat p a
参数：hp : p != 1；n a : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_dvd_iff_le_of_ne_one`：padicValNat_dvd_iff_le_of_ne_one {p : 
Nat} (hp : p != 1) {a n : Nat} (ha : a != 0) : p ^ n ∣ a ↔ n <= padicValNat p a
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem padicValNat_dvd_iff_of_ne_one {p : ℕ} (hp : p ≠ 1) (n a : ℕ) :
    p ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact iff_of_true (dvd_zero _) (Or.inl rfl)
  · rw [padicValNat_dvd_iff_le_of_ne_one hp ha, or_iff_right ha]
/-
**padicValNat_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_dvd_iff (n : Nat) [hp : Fact p.Prime] (a : Nat) : p ^ n ∣ a ↔ 
a = 0 ∨ n <= padicValNat p a
参数：n : Nat；a : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicValNat_dvd_iff_of_ne_one`：padicValNat_dvd_iff_of_ne_one {p : Nat} (
hp : p != 1) (n a : Nat) : p ^ n ∣ a ↔ a = 0 ∨ n <= padicValNat p a
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem padicValNat_dvd_iff (n : ℕ) [hp : Fact p.Prime] (a : ℕ) :
    p ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a :=
  padicValNat_dvd_iff_of_ne_one hp.out.ne_one n a
/-
**pow_succ_padicValNat_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_succ_padicValNat_not_dvd {n : Nat} [hp : Fact p.Prime] (hn : n != 0) :
 ¬p ^ (padicValNat p n + 1) ∣ n
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_dvd_iff_le`：padicValNat_dvd_iff_le [hp : Fact p.Prime] {a n 
: Nat} (ha : a != 0) : p ^ n ∣ a ↔ n <= padicValNat p a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem pow_succ_padicValNat_not_dvd {n : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) :
    ¬p ^ (padicValNat p n + 1) ∣ n := by
  rw [padicValNat_dvd_iff_le hn, not_le]
  exact Nat.lt_succ_self _
/-
**padicValNat_primes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_primes {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Prime] (ne :
 p != q) : padicValNat p q = 0
参数：ne : p != q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicValNat.eq_zero_of_not_dvd`：eq_zero_of_not_dvd {n : Nat} (h : ¬p ∣ n
) : padicValNat p n = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem padicValNat_primes {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (ne : p ≠ q) :
    padicValNat p q = 0 :=
  @padicValNat.eq_zero_of_not_dvd p q <|
    (not_congr (Iff.symm (prime_dvd_prime_iff_eq hp.1 hq.1))).mp ne
/-
**padicValNat_prime_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_prime_prime_pow {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Pri
me] (n : Nat) (ne : p != q) : padicValNat p (q ^ n) = 0
参数：n : Nat；ne : p != q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat.pow`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (a n : ℕ), padicVal
Nat p (a ^ n) = n * padicValNat p a
· 使用定理 `padicValNat_primes`：padicValNat_primes {q : Nat} [hp : Fact p.Prime] [hq
 : Fact q.Prime] (ne : p != q) : padicValNat p q = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem padicValNat_prime_prime_pow {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n : ℕ) (ne : p ≠ q) : padicValNat p (q ^ n) = 0 := by
  rw [padicValNat.pow _, padicValNat_primes ne, mul_zero]
/-
**padicValNat_mul_pow_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_mul_pow_left {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Prime]
 (n m : Nat) (ne : p != q) : padicValNat p (p ^ n * q ^ m) = n
参数：n m : Nat；ne : p != q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat.mul`：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 
→ padicValNat p (a * b) = padicValNat p a + padicValNat p b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `NeZero.ne'`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], 0 ≠
 n
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `padicValNat.prime_pow`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (n : ℕ), padi
cValNat p (p ^ n) = n
· 使用定理 `padicValNat_prime_prime_pow`：padicValNat_prime_prime_pow {q : Nat} [hp :
 Fact p.Prime] [hq : Fact q.Prime] (n : Nat) (ne : p != q) : padicValNat p (q ^ 
n) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem padicValNat_mul_pow_left {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : ℕ) (ne : p ≠ q) : padicValNat p (p ^ n * q ^ m) = n := by
  rw [padicValNat.mul (NeZero.ne' (p ^ n)).symm (NeZero.ne' (q ^ m)).symm,
    padicValNat.prime_pow, padicValNat_prime_prime_pow m ne, add_zero]
/-
**padicValNat_mul_pow_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_mul_pow_right {q : Nat} [hp : Fact p.Prime] [hq : Fact q.Prime
] (n m : Nat) (ne : q != p) : padicValNat q (p ^ n * q ^ m) = m
参数：n m : Nat；ne : q != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `padicValNat_mul_pow_left`：padicValNat_mul_pow_left {q : Nat} [hp : Fact 
p.Prime] [hq : Fact q.Prime] (n m : Nat) (ne : p != q) : padicValNat p (p ^ n * 
q ^ m) = n
-/
theorem padicValNat_mul_pow_right {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : ℕ) (ne : q ≠ p) : padicValNat q (p ^ n * q ^ m) = m := by
  rw [mul_comm (p ^ n) (q ^ m)]
  exact padicValNat_mul_pow_left m n ne

/-- The p-adic valuation of `n` is less than or equal to its logarithm w.r.t. `p`. -/
/-
**padicValNat_le_nat_log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：padicValNat_le_nat_log (n : Nat) : padicValNat p n <= Nat.log p n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_zero_right`：∀ (p : ℕ), padicValNat p 0 = 0
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `padicValNat_zero_left`：∀ (n : ℕ), padicValNat 0 n = 0
· 使用定理 `Nat.log_zero_left`：∀ (n : ℕ), Nat.log 0 n = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `padicValNat_one_left`：∀ (n : ℕ), padicValNat 1 n = 0
· 使用定理 `Nat.log_one_left`：log_one_left : forall n, log 1 n = 0
· 使用定理 `Nat.le_log_of_pow_le`：le_log_of_pow_le {b x y : Nat} (hb : 1 < b) (h : b
 ^ x <= y) : x <= log b y
· 使用定理 `Nat.one_lt_succ_succ`：∀ (n : ℕ), 1 < n.succ.succ
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `pow_padicValNat_dvd`：∀ {p n : ℕ}, p ^ padicValNat p n ∣ n

--- 原说明 ---
The p-adic valuation of `n` is less than or equal to its logarithm w.r.t. `p`.
-/
lemma padicValNat_le_nat_log (n : ℕ) : padicValNat p n ≤ Nat.log p n := by
  rcases n with _ | n
  · simp
  rcases p with _ | _ | p
  · simp
  · simp
  exact Nat.le_log_of_pow_le p.one_lt_succ_succ (le_of_dvd n.succ_pos pow_padicValNat_dvd)
/-
**padicValNat_add_le_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：padicValNat_add_le_self {a : Nat} [hp : Fact p.Prime] (ha : p < a) : padic
ValNat p a + p <= a
参数：ha : p < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `padicValNat_le_nat_log`：padicValNat_le_nat_log (n : Nat) : padicValNat p
 n <= Nat.log p n
· 使用引理 `Nat.log_lt_self`：log_lt_self (b : Nat) {x : Nat} (hx : x != 0) : log b x
 < x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat.mul`：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 
→ padicValNat p (a * b) = padicValNat p a + padicValNat p b
· 使用定理 `padicValNat_self`：padicValNat_self [Fact p.Prime] : padicValNat p p = 1
· 使用定理 `Nat.add_le_mul`：∀ {a : ℕ}, 2 ≤ a → ∀ {b : ℕ}, 2 ≤ b → a + b ≤ a * b
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `padicValNat.eq_zero_of_not_dvd`：eq_zero_of_not_dvd {n : Nat} (h : ¬p ∣ n
) : padicValNat p n = 0
-/
lemma padicValNat_add_le_self {a : ℕ} [hp : Fact p.Prime] (ha : p < a) :
    padicValNat p a + p ≤ a := by
  by_cases dvd : p ∣ a
  · rcases dvd with ⟨k, hk⟩
    have : padicValNat p k < k := by calc
      _ ≤ log p k := padicValNat_le_nat_log k
      _ < _ := log_lt_self p (by lia)
    rw [hk, padicValNat.mul (by lia) (by lia), padicValNat_self]
    calc
      _ ≤ p + k := by lia
      _ ≤ _ := Nat.add_le_mul hp.out.two_le (by lia)
  · rw [padicValNat.eq_zero_of_not_dvd dvd]
    lia

/-- The p-adic valuation of `n` is equal to the logarithm w.r.t. `p` iff
`n` is less than `p` raised to one plus the p-adic valuation of `n`. -/
/-
**nat_log_eq_padicValNat_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nat_log_eq_padicValNat_iff {n : Nat} [hp : Fact (Nat.Prime p)] (hn : n != 
0) : Nat.log p n = padicValNat p n ↔ n < p ^ (padicValNat p n + 1)
参数：Nat.Prime p；hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_eq_iff`：log_eq_iff {b m n : Nat} (h : m != 0 ∨ 1 < b ∧ n != 0) :
 log b n = m ↔ b ^ m <= n ∧ n < b ^ (m + 1)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `and_iff_right_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ b) ↔ b → a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `pow_padicValNat_dvd`：∀ {p n : ℕ}, p ^ padicValNat p n ∣ n

--- 原说明 ---
The p-adic valuation of `n` is equal to the logarithm w.r.t. `p` iff
`n` is less than `p` raised to one plus the p-adic valuation of `n`.
-/
lemma nat_log_eq_padicValNat_iff {n : ℕ} [hp : Fact (Nat.Prime p)] (hn : n ≠ 0) :
    Nat.log p n = padicValNat p n ↔ n < p ^ (padicValNat p n + 1) := by
  rw [Nat.log_eq_iff (Or.inr ⟨(Nat.Prime.one_lt' p).out, by lia⟩), and_iff_right_iff_imp]
  exact fun _ => Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hn) pow_padicValNat_dvd

/-- This is false for prime numbers other than 2:
for `p = 3`, `n = 1`, one has `log 3 1 = padicValNat 3 2 = 0`. -/
/-
**Nat.log_ne_padicValNat_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.log_ne_padicValNat_succ {n : Nat} (hn : n != 0) : log 2 n != padicValN
at 2 (n + 1)
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Nat.log_eq_iff`：log_eq_iff {b m n : Nat} (h : m != 0 ∨ 1 < b ∧ n != 0) :
 log b n = m ↔ b ^ m <= n ∧ n < b ^ (m + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Nat.not_dvd_of_lt_of_lt_mul_succ`：∀ {n k m : ℕ}, n * k < m → m < n * (k 
+ 1) → ¬n ∣ m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Nat.pow_succ`：∀ (n m : ℕ), n ^ m.succ = n ^ m * n
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `pow_succ_padicValNat_not_dvd`：pow_succ_padicValNat_not_dvd {n : Nat} [hp
 : Fact p.Prime] (hn : n != 0) : ¬p ^ (padicValNat p n + 1) ∣ n
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `dvd_of_eq`：dvd_of_eq (h : a = b) : a ∣ b
· 使用定理 `pow_padicValNat_dvd`：∀ {p n : ℕ}, p ^ padicValNat p n ∣ n

--- 原说明 ---
This is false for prime numbers other than 2:
for `p = 3`, `n = 1`, one has `log 3 1 = padicValNat 3 2 = 0`.
-/
lemma Nat.log_ne_padicValNat_succ {n : ℕ} (hn : n ≠ 0) : log 2 n ≠ padicValNat 2 (n + 1) := by
  rw [Ne, log_eq_iff (by simp [hn])]
  rintro ⟨h1, h2⟩
  rw [← Nat.lt_add_one_iff, ← mul_one (2 ^ _)] at h1
  rw [← add_one_le_iff, Nat.pow_succ] at h2
  refine not_dvd_of_lt_of_lt_mul_succ h1 (lt_of_le_of_ne' h2 ?_) pow_padicValNat_dvd
  -- TODO(kmill): Why is this `p := 2` necessary?
  exact pow_succ_padicValNat_not_dvd (p := 2) n.succ_ne_zero ∘ dvd_of_eq
/-
**Nat.max_log_padicValNat_succ_eq_log_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.max_log_padicValNat_succ_eq_log_succ (n : Nat) [hp : Fact p.Prime] : m
ax (log p n) (padicValNat p (n + 1)) = log p (n + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Nat.le_log_of_pow_le`：le_log_of_pow_le {b x y : Nat} (hb : 1 < b) (h : b
 ^ x <= y) : x <= log b y
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.pow_log_le_add_one`：∀ (b x : ℕ), b ^ Nat.log b x ≤ x + 1
· 使用引理 `padicValNat_le_nat_log`：padicValNat_le_nat_log (n : Nat) : padicValNat p
 n <= Nat.log p n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `Nat.lt_pow_of_log_lt`：lt_pow_of_log_lt {b x y : Nat} (hb : 1 < b) : log 
b y < x -> y < b ^ x
· 使用定理 `Nat.pow_log_le_self`：pow_log_le_self (b : Nat) {x : Nat} (hx : x != 0) :
 b ^ log b x <= x
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `padicValNat.prime_pow`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (n : ℕ), padi
cValNat p (p ^ n) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma Nat.max_log_padicValNat_succ_eq_log_succ (n : ℕ) [hp : Fact p.Prime] :
    max (log p n) (padicValNat p (n + 1)) = log p (n + 1) := by
  apply le_antisymm (max_le (le_log_of_pow_le hp.out.one_lt (pow_log_le_add_one p n))
    (padicValNat_le_nat_log (n + 1)))
  rw [le_max_iff, or_iff_not_imp_left, not_le]
  intro h
  replace h := le_antisymm (add_one_le_iff.mpr (lt_pow_of_log_lt hp.out.one_lt h))
    (pow_log_le_self p n.succ_ne_zero)
  rw [h, padicValNat.prime_pow, ← h]
/-
**range_pow_padicValNat_subset_divisors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_pow_padicValNat_subset_divisors {n : Nat} (hn : n != 0) : (Finset.ra
nge (padicValNat p n + 1)).image (p ^ ·) subseteq n.divisors
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `pow_padicValNat_dvd`：∀ {p n : ℕ}, p ^ padicValNat p n ∣ n
-/
theorem range_pow_padicValNat_subset_divisors {n : ℕ} (hn : n ≠ 0) :
    (Finset.range (padicValNat p n + 1)).image (p ^ ·) ⊆ n.divisors := by
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Nat.mem_divisors]
  exact ⟨(pow_dvd_pow p <| by lia).trans pow_padicValNat_dvd, hn⟩
/-
**range_pow_padicValNat_subset_divisors'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_pow_padicValNat_subset_divisors' {n : Nat} [hp : Fact p.Prime] : ((F
inset.range (padicValNat p n)).image fun t => p ^ (t + 1)) subseteq n.divisors.e
rase 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_zero_right`：∀ (p : ℕ), padicValNat p 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.divisors_zero`：divisors_zero : divisors 0 = ∅
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.one_lt_pow`：∀ {n a : ℕ}, n ≠ 0 → 1 < a → 1 < a ^ n
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `pow_padicValNat_dvd`：∀ {p n : ℕ}, p ^ padicValNat p n ∣ n
-/
theorem range_pow_padicValNat_subset_divisors' {n : ℕ} [hp : Fact p.Prime] :
    ((Finset.range (padicValNat p n)).image fun t => p ^ (t + 1)) ⊆ n.divisors.erase 1 := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_erase, Nat.mem_divisors]
  refine ⟨?_, (pow_dvd_pow p <| succ_le_iff.2 hk).trans pow_padicValNat_dvd, hn⟩
  exact (Nat.one_lt_pow k.succ_ne_zero hp.out.one_lt).ne'

/-- The `p`-adic valuation of `(p * n)!` is `n` more than that of `n!`. -/
/-
**padicValNat_factorial_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_factorial_mul (n : Nat) [hp : Fact p.Prime] : padicValNat p (p
 * n)! = padicValNat p n ! + n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_eq_emultiplicity`：padicValNat_eq_emultiplicity [hp : Fact p.
Prime] {n : Nat} (hn : n != 0) : padicValNat p n = emultiplicity p n
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.Prime.emultiplicity_factorial_mul`：emultiplicity_factorial_mul {n p 
: Nat} (hp : p.Prime) : emultiplicity p (p * n)! = emultiplicity p n ! + n
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
The `p`-adic valuation of `(p * n)!` is `n` more than that of `n!`.
-/
theorem padicValNat_factorial_mul (n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * n)! = padicValNat p n ! + n := by
  apply Nat.cast_injective (R := ℕ∞)
  rw [padicValNat_eq_emultiplicity <| factorial_ne_zero (p * n), Nat.cast_add,
      padicValNat_eq_emultiplicity <| factorial_ne_zero n]
  exact Prime.emultiplicity_factorial_mul hp.out

/-- The `p`-adic valuation of `m` equals zero if it is between `p * k` and `p * (k + 1)` for
some `k`. -/
/-
**padicValNat_eq_zero_of_mem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_eq_zero_of_mem_Ioo {m k : Nat} (hm : m in Set.Ioo (p * k) (p *
 (k + 1))) : padicValNat p m = 0
参数：hm : m in Set.Ioo (p * k) (p * (k + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicValNat.eq_zero_of_not_dvd`：eq_zero_of_not_dvd {n : Nat} (h : ¬p ∣ n
) : padicValNat p n = 0
· 使用定理 `Nat.not_dvd_of_lt_of_lt_mul_succ`：∀ {n k m : ℕ}, n * k < m → m < n * (k 
+ 1) → ¬n ∣ m
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The `p`-adic valuation of `m` equals zero if it is between `p * k` and `p * (k +
 1)` for
some `k`.
-/
theorem padicValNat_eq_zero_of_mem_Ioo {m k : ℕ}
    (hm : m ∈ Set.Ioo (p * k) (p * (k + 1))) : padicValNat p m = 0 :=
  padicValNat.eq_zero_of_not_dvd <| not_dvd_of_lt_of_lt_mul_succ hm.1 hm.2
/-
**padicValNat_factorial_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_factorial_mul_add {n : Nat} (m : Nat) [hp : Fact p.Prime] (h :
 n < p) : padicValNat p (p * m + n)! = padicValNat p (p * m)!
参数：m : Nat；h : n < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.add_succ`：∀ (n m : ℕ), n + m.succ = (n + m).succ
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `padicValNat.mul`：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 
→ padicValNat p (a * b) = padicValNat p a + padicValNat p b
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Nat.lt_of_succ_lt`：∀ {n m : ℕ}, n.succ < m → n < m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicValNat_eq_zero_of_mem_Ioo`：padicValNat_eq_zero_of_mem_Ioo {m k : Na
t} (hm : m in Set.Ioo (p * k) (p * (k + 1))) : padicValNat p m = 0
· 使用定理 `Nat.lt_add_of_pos_right`：∀ {k n : ℕ}, 0 < k → n < n + k
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `add_lt_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [Ad
dLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b c : α},   a + b < a + c ↔ b <
 c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `Nat.mul_add`：∀ (n m k : ℕ), n * (m + k) = n * m + n * k
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem padicValNat_factorial_mul_add {n : ℕ} (m : ℕ) [hp : Fact p.Prime] (h : n < p) :
    padicValNat p (p * m + n)! = padicValNat p (p * m)! := by
  induction n with
  | zero => rw [add_zero]
  | succ n hn =>
    rw [add_succ, factorial_succ,
      padicValNat.mul (succ_ne_zero (p * m + n)) <| factorial_ne_zero (p * m + _),
      hn <| lt_of_succ_lt h, ← add_succ,
      padicValNat_eq_zero_of_mem_Ioo ⟨(Nat.lt_add_of_pos_right <| succ_pos n),
        (Nat.mul_add _ _ _▸ Nat.mul_one _ ▸ ((add_lt_add_iff_left (p * m)).mpr h))⟩,
      zero_add]

/-- The `p`-adic valuation of `n!` is equal to the `p`-adic valuation of the factorial of the
largest multiple of `p` below `n`, i.e. `(p * ⌊n / p⌋)!`. -/
/-
**padicValNat_mul_div_factorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {p : ℕ} (n : ℕ) [hp : Fact (Nat.Prime p)], padicValNat p (p * (n / p)).f
actorial = padicValNat p n.factorial
参数：n : ℕ；Nat.Prime p；p * (n / p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
· 使用定理 `padicValNat_factorial_mul_add`：padicValNat_factorial_mul_add {n : Nat} (
m : Nat) [hp : Fact p.Prime] (h : n < p) : padicValNat p (p * m + n)! = padicVal
Nat p (p * m)!
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
The `p`-adic valuation of `n!` is equal to the `p`-adic valuation of the factori
al of the
largest multiple of `p` below `n`, i.e. `(p * ⌊n / p⌋)!`.
-/
@[simp] theorem padicValNat_mul_div_factorial (n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * (n / p))! = padicValNat p n ! := by
  nth_rw 2 [← div_add_mod n p]
  exact (padicValNat_factorial_mul_add (n / p) <| mod_lt n hp.out.pos).symm

/-- **Legendre's Theorem**

The `p`-adic valuation of `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
/-
**padicValNat_factorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_factorial {n b : Nat} [hp : Fact p.Prime] (hnb : log p n < b) 
: padicValNat p (n !) = ∑ i in Finset.Ico 1 b, n / p ^ i
参数：hnb : log p n < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.Prime.emultiplicity_factorial`：emultiplicity_factorial {p : Nat} (hp
 : p.Prime) : forall {n b : Nat}, log p n < b -> emultiplicity p n ! = (∑ i in I
co 1 b, n / p ^ i : Nat…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicValNat_eq_emultiplicity`：padicValNat_eq_emultiplicity [hp : Fact p.
Prime] {n : Nat} (hn : n != 0) : padicValNat p n = emultiplicity p n
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0

--- 原说明 ---
**Legendre's Theorem**

The `p`-adic valuation of `n!` is the sum of the quotients `n / p ^ i`. This sum
 is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`.
-/
theorem padicValNat_factorial {n b : ℕ} [hp : Fact p.Prime] (hnb : log p n < b) :
    padicValNat p (n !) = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
  exact_mod_cast ((padicValNat_eq_emultiplicity (p := p) <| factorial_ne_zero _) ▸
      Prime.emultiplicity_factorial hp.out hnb)

/-- **Legendre's Theorem**

Taking (`p - 1`) times the `p`-adic valuation of `n!` equals `n` minus the sum of base `p` digits
of `n`. -/
/-
**sub_one_mul_padicValNat_factorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_one_mul_padicValNat_factorial [hp : Fact p.Prime] (n : Nat) : (p - 1) 
* padicValNat p (n !) = n - (p.digits n).sum
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_factorial`：padicValNat_factorial {n b : Nat} [hp : Fact p.Pr
ime] (hnb : log p n < b) : padicValNat p (n !) = ∑ i in Finset.Ico 1 b, n / p ^ 
i
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Finset.sum_Ico_add'`：∀ {α : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : AddCommMonoid α] [inst_2 : PartialOrder α]   [IsOrderedCancelAdd
Monoid α]…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits`：sub_one_mul_sum_log_d
iv_pow_eq_sub_sum_digits {p : Nat} (n : Nat) : (p - 1) * ∑ i in range (log p n).
succ, n / p ^ i.succ = n - (p.digits n)…

--- 原说明 ---
**Legendre's Theorem**

Taking (`p - 1`) times the `p`-adic valuation of `n!` equals `n` minus the sum o
f base `p` digits
of `n`.
-/
theorem sub_one_mul_padicValNat_factorial [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (n !) = n - (p.digits n).sum := by
  rw [padicValNat_factorial <| lt_succ_of_lt <| lt_add_one (log p n)]
  nth_rw 2 [← zero_add 1]
  rw [Nat.succ_eq_add_one, ← Finset.sum_Ico_add' _ 0 _ 1,
    Ico_zero_eq_range, ← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits, Nat.succ_eq_add_one]

variable (p)
/-
**sub_one_mul_padicValNat_factorial_lt_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_one_mul_padicValNat_factorial_lt_of_ne_zero [hp : Fact p.Prime] {n : N
at} (hn : n != 0) : (p - 1) * padicValNat p n.factorial < n
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_one_mul_padicValNat_factorial`：sub_one_mul_padicValNat_factorial [hp
 : Fact p.Prime] (n : Nat) : (p - 1) * padicValNat p (n !) = n - (p.digits n).su
m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.digits_ne_nil_iff_ne_zero`：digits_ne_nil_iff_ne_zero {b n : Nat} : d
igits b n != [] ↔ n != 0
· 使用定理 `List.sum_pos_iff_exists_pos_nat`：∀ {l : List ℕ}, 0 < l.sum ↔ ∃ x ∈ l, 0 
< x
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.getLast_digit_ne_zero`：getLast_digit_ne_zero (b : Nat) {m : Nat} (hm
 : m != 0) : (digits b m).getLast (digits_ne_nil_iff_ne_zero.mpr hm) != 0
· 使用定理 `Nat.digit_sum_le`：digit_sum_le (p n : Nat) : List.sum (digits p n) <= n
-/
theorem sub_one_mul_padicValNat_factorial_lt_of_ne_zero [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * padicValNat p n.factorial < n := by
  rw [sub_one_mul_padicValNat_factorial n]
  refine Nat.sub_lt_self ?_ (digit_sum_le p n)
  have hnil : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn)⟩
/-
**padicValNat_factorial_lt_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_factorial_lt_of_ne_zero [hp : Fact p.Prime] {n : Nat} (hn : n 
!= 0) : padicValNat p n.factorial < n
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`：sub_one_mul_padicValNat
_factorial_lt_of_ne_zero [hp : Fact p.Prime] {n : Nat} (hn : n != 0) : (p - 1) *
 padicValNat p n.factorial < n
-/
theorem padicValNat_factorial_lt_of_ne_zero [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n.factorial < n := by
  apply lt_of_le_of_lt _ (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn)
  conv_lhs => rw [← one_mul (padicValNat p n !)]
  gcongr
  exact le_sub_one_of_lt (Nat.Prime.one_lt hp.elim)
/-
**padicValNat_factorial_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_factorial_le [hp : Fact p.Prime] (n : Nat) : padicValNat p n.f
actorial <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValNat_one_right`：∀ (p : ℕ), padicValNat p 1 = 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `padicValNat_factorial_lt_of_ne_zero`：padicValNat_factorial_lt_of_ne_zero
 [hp : Fact p.Prime] {n : Nat} (hn : n != 0) : padicValNat p n.factorial < n
-/
theorem padicValNat_factorial_le [hp : Fact p.Prime] (n : ℕ) : padicValNat p n.factorial ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact le_of_lt (padicValNat_factorial_lt_of_ne_zero p hn)

variable {p}

/-- **Kummer's Theorem**

The `p`-adic valuation of `n.choose k` is the number of carries when `k` and `n - k` are added
in base `p`. This sum is expressed over the finset `Ico 1 b` where `b` is any bound greater than
`log p n`. -/
/-
**padicValNat_choose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_choose {n k b : Nat} [hp : Fact p.Prime] (hkn : k <= n) (hnb :
 log p n < b) : padicValNat p (choose n k) = #{i in Finset.Ico 1 b | p ^ i <= k 
% p ^ i + (n - k) % p ^ i}
参数：hkn : k <= n；hnb : log p n < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.Prime.emultiplicity_choose`：emultiplicity_choose {p n k b : Nat} (hp
 : p.Prime) (hkn : k <= n) (hnb : log p n < b) : emultiplicity p (choose n k) = 
#{i in Ico 1 b | p ^…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicValNat_eq_emultiplicity`：padicValNat_eq_emultiplicity [hp : Fact p.
Prime] {n : Nat} (hn : n != 0) : padicValNat p n = emultiplicity p n
· 使用引理 `Nat.choose_ne_zero`：choose_ne_zero {n k : Nat} (h : k <= n) : n.choose k
 != 0

--- 原说明 ---
**Kummer's Theorem**

The `p`-adic valuation of `n.choose k` is the number of carries when `k` and `n 
- k` are added
in base `p`. This sum is expressed over the finset `Ico 1 b` where `b` is any bo
und greater than
`log p n`.
-/
theorem padicValNat_choose {n k b : ℕ} [hp : Fact p.Prime] (hkn : k ≤ n) (hnb : log p n < b) :
    padicValNat p (choose n k) = #{i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| (choose_ne_zero hkn)) ▸
    Prime.emultiplicity_choose hp.out hkn hnb

/-- **Kummer's Theorem**

The `p`-adic valuation of `(n + k).choose k` is the number of carries when `k` and `n` are added
in base `p`. This sum is expressed over the finset `Ico 1 b` where `b` is any bound greater than
`log p (n + k)`. -/
/-
**padicValNat_choose'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_choose' {n k b : Nat} [hp : Fact p.Prime] (hnb : log p (n + k)
 < b) : padicValNat p (choose (n + k) k) = #{i in Finset.Ico 1 b | p ^ i <= k % 
p ^ i + n % p ^ i}
参数：hnb : log p (n + k) < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.Prime.emultiplicity_choose'`：emultiplicity_choose' {p n k b : Nat} (
hp : p.Prime) (hnb : log p (n + k) < b) : emultiplicity p (choose (n + k) k) = #
{i in Ico 1 b | p ^ i…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicValNat_eq_emultiplicity`：padicValNat_eq_emultiplicity [hp : Fact p.
Prime] {n : Nat} (hn : n != 0) : padicValNat p n = emultiplicity p n
· 使用引理 `Nat.choose_ne_zero`：choose_ne_zero {n k : Nat} (h : k <= n) : n.choose k
 != 0
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n

--- 原说明 ---
**Kummer's Theorem**

The `p`-adic valuation of `(n + k).choose k` is the number of carries when `k` a
nd `n` are added
in base `p`. This sum is expressed over the finset `Ico 1 b` where `b` is any bo
und greater than
`log p (n + k)`.
-/
theorem padicValNat_choose' {n k b : ℕ} [hp : Fact p.Prime] (hnb : log p (n + k) < b) :
    padicValNat p (choose (n + k) k) = #{i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| choose_ne_zero <|
    Nat.le_add_left k n) ▸ Prime.emultiplicity_choose' hp.out hnb

/-- **Kummer's Theorem**
Taking (`p - 1`) times the `p`-adic valuation of the binomial `n + k` over `k` equals the sum of the
digits of `k` plus the sum of the digits of `n` minus the sum of digits of `n + k`, all base `p`.
-/
/-
**sub_one_mul_padicValNat_choose_eq_sub_sum_digits'** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：sub_one_mul_padicValNat_choose_eq_sub_sum_digits' {k n : Nat} [hp : Fact p
.Prime] : (p - 1) * padicValNat p (choose (n + k) k) = (p.digits k).sum + (p.dig
its n).sum - (p.digits (n + k)).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_factorial_div_factorial`：choose_eq_factorial_div_factorial
 {n k : Nat} (hk : k <= n) : choose n k = n ! / (k ! * (n - k)!)
· 使用定理 `padicValNat.div_of_dvd`：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], b ∣ a →
 padicValNat p (a / b) = padicValNat p a - padicValNat p b
· 使用定理 `Nat.factorial_mul_factorial_dvd_factorial`：factorial_mul_factorial_dvd_f
actorial {n k : Nat} (hk : k <= n) : k ! * (n - k)! ∣ n !
· 使用定理 `Nat.mul_sub_left_distrib`：∀ (n m k : ℕ), n * (m - k) = n * m - n * k
· 使用定理 `padicValNat.mul`：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 
→ padicValNat p (a * b) = padicValNat p a + padicValNat p b
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Nat.mul_add`：∀ (n m k : ℕ), n * (m + k) = n * m + n * k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_one_mul_padicValNat_factorial`：sub_one_mul_padicValNat_factorial [hp
 : Fact p.Prime] (n : Nat) : (p - 1) * padicValNat p (n !) = n - (p.digits n).su
m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_comm`：∀ {n m k : ℕ}, k ≤ n → n + m - k = n - k + m
· 使用定理 `Nat.digit_sum_le`：digit_sum_le (p n : Nat) : List.sum (digits p n) <= n
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Nat.add_sub_assoc`：∀ {m k : ℕ}, k ≤ m → ∀ (n : ℕ), n + m - k = n + (m - 
k)
· 使用定理 `Nat.sub_sub`：∀ (n m k : ℕ), n - m - k = n - (m + k)
· 使用定理 `Nat.sub_right_comm`：∀ (m n k : ℕ), m - n - k = m - k - n
· 使用定理 `Nat.sub_add_eq`：∀ (a b c : ℕ), a - (b + c) = a - b - c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_tsub_assoc`：tsub_tsub_assoc (h₁ : b <= a) (h₂ : c <= b) : a - (b - 
c) = a - b + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `Nat.add_le_add`：∀ {a b c d : ℕ}, a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
**Kummer's Theorem**
Taking (`p - 1`) times the `p`-adic valuation of the binomial `n + k` over `k` e
quals the sum of the
digits of `k` plus the sum of the digits of `n` minus the sum of digits of `n + 
k`, all base `p`.
-/
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits' {k n : ℕ} [hp : Fact p.Prime] :
    (p - 1) * padicValNat p (choose (n + k) k) =
    (p.digits k).sum + (p.digits n).sum - (p.digits (n + k)).sum := by
  have h : k ≤ n + k := by exact Nat.le_add_left k n
  simp only [Nat.choose_eq_factorial_div_factorial h]
  rw [padicValNat.div_of_dvd <| factorial_mul_factorial_dvd_factorial h, Nat.mul_sub_left_distrib,
      padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _), Nat.mul_add]
  simp only [sub_one_mul_padicValNat_factorial]
  rw [← Nat.sub_add_comm <| digit_sum_le p k, Nat.add_sub_cancel n k, ← Nat.add_sub_assoc <|
      digit_sum_le p n, Nat.sub_sub (k + n), ← Nat.sub_right_comm, Nat.sub_sub, sub_add_eq,
      add_comm, tsub_tsub_assoc (Nat.le_refl (k + n)) <| (add_comm k n) ▸ (Nat.add_le_add
      (digit_sum_le p n) (digit_sum_le p k)), Nat.sub_self (k + n), zero_add, add_comm]

/-- **Kummer's Theorem**
Taking (`p - 1`) times the `p`-adic valuation of the binomial `n` over `k` equals the sum of the
digits of `k` plus the sum of the digits of `n - k` minus the sum of digits of `n`, all base `p`.
-/
/-
**sub_one_mul_padicValNat_choose_eq_sub_sum_digits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_one_mul_padicValNat_choose_eq_sub_sum_digits {k n : Nat} [hp : Fact p.
Prime] (h : k <= n) : (p - 1) * padicValNat p (choose n k) = (p.digits k).sum + 
(p.digits (n - k)).sum - (p.digits n).sum
参数：h : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'`：sub_one_mul_padicValN
at_choose_eq_sub_sum_digits' {k n : Nat} [hp : Fact p.Prime] : (p - 1) * padicVa
lNat p (choose (n + k) k) = (p.digits k…

--- 原说明 ---
**Kummer's Theorem**
Taking (`p - 1`) times the `p`-adic valuation of the binomial `n` over `k` equal
s the sum of the
digits of `k` plus the sum of the digits of `n - k` minus the sum of digits of `
n`, all base `p`.
-/
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits {k n : ℕ} [hp : Fact p.Prime]
    (h : k ≤ n) : (p - 1) * padicValNat p (choose n k) =
    (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum := by
  convert! @sub_one_mul_padicValNat_choose_eq_sub_sum_digits' _ _ _ ‹_›
  all_goals lia

end padicValNat

section padicValInt

variable {p : ℕ}

/-
**padicValInt_dvd_iff_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValInt_dvd_iff_of_ne_one (hp : p != 1) (n : Nat) (a : Int) : (p : Int
) ^ n ∣ a ↔ a = 0 ∨ n <= padicValInt p a
参数：hp : p != 1；n : Nat；a : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValInt.eq_1`：∀ (p : ℕ) (z : ℤ), padicValInt p z = padicValNat p z.n
atAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natAbs_eq_zero`：∀ {a : ℤ}, a.natAbs = 0 ↔ a = 0
· 使用定理 `padicValNat_dvd_iff_of_ne_one`：padicValNat_dvd_iff_of_ne_one {p : Nat} (
hp : p != 1) (n a : Nat) : p ^ n ∣ a ↔ a = 0 ∨ n <= padicValNat p a
· 使用引理 `Int.natCast_dvd`：natCast_dvd {m : Nat} : (m : Int) ∣ n ↔ m ∣ n.natAbs
· 使用定理 `Int.natCast_pow`：∀ (m n : ℕ), ↑(m ^ n) = ↑m ^ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem padicValInt_dvd_iff_of_ne_one (hp : p ≠ 1) (n : ℕ) (a : ℤ) :
    (p : ℤ) ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValInt p a := by
  rw [padicValInt, ← Int.natAbs_eq_zero, ← padicValNat_dvd_iff_of_ne_one hp, ← Int.natCast_dvd,
    Int.natCast_pow]
/-
**padicValInt_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValInt_dvd_iff [hp : Fact p.Prime] (n : Nat) (a : Int) : (p : Int) ^ 
n ∣ a ↔ a = 0 ∨ n <= padicValInt p a
参数：n : Nat；a : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicValInt_dvd_iff_of_ne_one`：padicValInt_dvd_iff_of_ne_one (hp : p != 
1) (n : Nat) (a : Int) : (p : Int) ^ n ∣ a ↔ a = 0 ∨ n <= padicValInt p a
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem padicValInt_dvd_iff [hp : Fact p.Prime] (n : ℕ) (a : ℤ) :
    (p : ℤ) ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValInt p a :=
  padicValInt_dvd_iff_of_ne_one hp.out.ne_one n a
/-
**padicValInt_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValInt_dvd (a : Int) : (p : Int) ^ padicValInt p a ∣ a
参数：a : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `padicValInt_dvd_iff_of_ne_one`：padicValInt_dvd_iff_of_ne_one (hp : p != 
1) (n : Nat) (a : Int) : (p : Int) ^ n ∣ a ↔ a = 0 ∨ n <= padicValInt p a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem padicValInt_dvd (a : ℤ) : (p : ℤ) ^ padicValInt p a ∣ a := by
  by_cases hp : p = 1
  · rw [hp, Nat.cast_one, one_pow]; exact one_dvd _
  rw [padicValInt_dvd_iff_of_ne_one hp]
  exact Or.inr le_rfl
/-
**padicValInt_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValInt_self [hp : Fact p.Prime] : padicValInt p p = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicValInt.self`：self (hp : 1 < p) : padicValInt p p = 1
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem padicValInt_self [hp : Fact p.Prime] : padicValInt p p = 1 :=
  padicValInt.self hp.out.one_lt
/-
**padicValInt.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValInt.mul [hp : Fact p.Prime] {a b : Int} (ha : a != 0) (hb : b != 0
) : padicValInt p (a * b) = padicValInt p a + padicValInt p b
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `padicValNat.mul`：∀ {p a b : ℕ} [hp : Fact (Nat.Prime p)], a ≠ 0 → b ≠ 0 
→ padicValNat p (a * b) = padicValNat p a + padicValNat p b
· 使用定理 `Int.natAbs_ne_zero`：∀ {a : ℤ}, a.natAbs ≠ 0 ↔ a ≠ 0
-/
theorem padicValInt.mul [hp : Fact p.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValInt p (a * b) = padicValInt p a + padicValInt p b := by
  simp_rw [padicValInt]
  rw [Int.natAbs_mul, padicValNat.mul] <;> rwa [Int.natAbs_ne_zero]
/-
**padicValInt_mul_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValInt_mul_eq_succ [hp : Fact p.Prime] (a : Int) (ha : a != 0) : padi
cValInt p (a * p) = padicValInt p a + 1
参数：a : Int；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicValInt.mul`：padicValInt.mul [hp : Fact p.Prime] {a b : Int} (ha : a
 != 0) (hb : b != 0) : padicValInt p (a * b) = padicValInt p a + padicValInt p b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `padicValInt.of_nat`：of_nat {n : Nat} : padicValInt p n = padicValNat p n
· 使用定理 `padicValNat_self`：padicValNat_self [Fact p.Prime] : padicValNat p p = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem padicValInt_mul_eq_succ [hp : Fact p.Prime] (a : ℤ) (ha : a ≠ 0) :
    padicValInt p (a * p) = padicValInt p a + 1 := by
  rw [padicValInt.mul ha (Int.natCast_ne_zero.mpr hp.out.ne_zero)]
  simp only [padicValInt.of_nat, padicValNat_self]

end padicValInt

