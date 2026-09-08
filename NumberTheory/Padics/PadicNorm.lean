/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-!
# p-adic norm

This file defines the `p`-adic norm on `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`.

The valuation induces a norm on `ℚ`. This norm is a nonarchimedean absolute value.
It takes values in `{0} ∪ {1/p^k | k ∈ ℤ}`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/

@[expose] public section


/-- If `q ≠ 0`, the `p`-adic norm of a rational `q` is `p ^ (-padicValRat p q)`.
If `q = 0`, the `p`-adic norm of `q` is `0`. -/
/-
**padicNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：padicNorm (p : Nat) (q : Rat) : Rat
参数：p : Nat；q : Rat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `q ≠ 0`, the `p`-adic norm of a rational `q` is `p ^ (-padicValRat p q)`.
If `q = 0`, the `p`-adic norm of `q` is `0`.
-/
def padicNorm (p : ℕ) (q : ℚ) : ℚ :=
  if q = 0 then 0 else (p : ℚ) ^ (-padicValRat p q)

namespace padicNorm

open padicValRat

variable {p : ℕ}

/-- Unfolds the definition of the `p`-adic norm of `q` when `q ≠ 0`. -/
@[simp]
/-
**padicNorm.eq_zpow_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ} {q : ℚ}, q ≠ 0 → padicNorm p q = ↑p ^ (-padicValRat p q)
参数：-padicValRat p q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Unfolds the definition of the `p`-adic norm of `q` when `q ≠ 0`.
-/
protected theorem eq_zpow_of_nonzero {q : ℚ} (hq : q ≠ 0) :
    padicNorm p q = (p : ℚ) ^ (-padicValRat p q) := by simp [hq, padicNorm]

/-- The `p`-adic norm is nonnegative. -/
/-
**padicNorm.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ} (q : ℚ), 0 ≤ padicNorm p q
参数：q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zpow_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Parti
alOrder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 ≤ a → ∀ (n : 
ℤ…
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n

--- 原说明 ---
The `p`-adic norm is nonnegative.
-/
protected theorem nonneg (q : ℚ) : 0 ≤ padicNorm p q :=
  if hq : q = 0 then by simp [hq, padicNorm]
  else by
    unfold padicNorm
    split_ifs
    apply zpow_nonneg
    exact mod_cast Nat.zero_le _

/-- The `p`-adic norm of `0` is `0`. -/
@[simp]
/-
**padicNorm.zero** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ}, padicNorm p 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `p`-adic norm of `0` is `0`.
-/
protected theorem zero : padicNorm p 0 = 0 := by simp [padicNorm]

/-- The `p`-adic norm of `1` is `1`. -/
/-
**padicNorm.one** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ}, padicNorm p 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `padicValRat.one`：∀ {p : ℕ}, padicValRat p 1 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `p`-adic norm of `1` is `1`.
-/
protected theorem one : padicNorm p 1 = 1 := by simp [padicNorm]

/-- The `p`-adic norm of `p` is `p⁻¹` if `p > 1`.

See also `padicNorm.padicNorm_p_of_prime` for a version assuming `p` is prime. -/
/-
**padicNorm.padicNorm_p** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：padicNorm_p (hp : 1 < p) : padicNorm p p = (p : Rat)⁻¹
参数：hp : 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `padicValRat.of_nat`：of_nat {n : Nat} : padicValRat p n = padicValNat p n
· 使用定理 `padicValNat.self`：∀ {p : ℕ}, 1 < p → padicValNat p p = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `p`-adic norm of `p` is `p⁻¹` if `p > 1`.

See also `padicNorm.padicNorm_p_of_prime` for a version assuming `p` is prime.
-/
theorem padicNorm_p (hp : 1 < p) : padicNorm p p = (p : ℚ)⁻¹ := by
  simp [padicNorm, (pos_of_gt hp).ne', padicValNat.self hp]

/-- The `p`-adic norm of `p` is `p⁻¹` if `p` is prime.

See also `padicNorm.padicNorm_p` for a version assuming `1 < p`. -/
@[simp]
/-
**padicNorm.padicNorm_p_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：padicNorm_p_of_prime [Fact p.Prime] : padicNorm p p = (p : Rat)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.padicNorm_p`：padicNorm_p (hp : 1 < p) : padicNorm p p = (p : R
at)⁻¹
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
The `p`-adic norm of `p` is `p⁻¹` if `p` is prime.

See also `padicNorm.padicNorm_p` for a version assuming `1 < p`.
-/
theorem padicNorm_p_of_prime [Fact p.Prime] : padicNorm p p = (p : ℚ)⁻¹ :=
  padicNorm_p <| Nat.Prime.one_lt Fact.out

/-- The `p`-adic norm of `q` is `1` if `q` is prime and not equal to `p`. -/
/-
**padicNorm.padicNorm_of_prime_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：padicNorm_of_prime_of_ne {q : Nat} [p_prime : Fact p.Prime] [q_prime : Fac
t q.Prime] (ne : p != q) : padicNorm p q = 1
参数：ne : p != q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `padicValNat_primes`：padicValNat_primes {q : Nat} [hp : Fact p.Prime] [hq
 : Fact q.Prime] (ne : p != q) : padicValNat p q = 0
· 使用定理 `padicNorm.eq_1`：∀ (p : ℕ) (q : ℚ), padicNorm p q = if q = 0 then 0 else 
↑p ^ (-padicValRat p q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `p`-adic norm of `q` is `1` if `q` is prime and not equal to `p`.
-/
theorem padicNorm_of_prime_of_ne {q : ℕ} [p_prime : Fact p.Prime] [q_prime : Fact q.Prime]
    (ne : p ≠ q) : padicNorm p q = 1 := by
  have p : padicValRat p q = 0 := mod_cast padicValNat_primes ne
  rw [padicNorm, p]
  simp [q_prime.1.ne_zero]

/-- The `p`-adic norm of `p` is less than `1` if `1 < p`.

See also `padicNorm.padicNorm_p_lt_one_of_prime` for a version assuming `p` is prime. -/
/-
**padicNorm.padicNorm_p_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：padicNorm_p_lt_one (hp : 1 < p) : padicNorm p p < 1
参数：hp : 1 < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicNorm.padicNorm_p`：padicNorm_p (hp : 1 < p) : padicNorm p p = (p : R
at)⁻¹
· 使用引理 `inv_lt_one_iff₀`：inv_lt_one_iff₀ : a⁻¹ < 1 ↔ a <= 0 ∨ 1 < a
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ

--- 原说明 ---
The `p`-adic norm of `p` is less than `1` if `1 < p`.

See also `padicNorm.padicNorm_p_lt_one_of_prime` for a version assuming `p` is p
rime.
-/
theorem padicNorm_p_lt_one (hp : 1 < p) : padicNorm p p < 1 := by
  rw [padicNorm_p hp, inv_lt_one_iff₀]
  exact mod_cast Or.inr hp

/-- The `p`-adic norm of `p` is less than `1` if `p` is prime.

See also `padicNorm.padicNorm_p_lt_one` for a version assuming `1 < p`. -/
/-
**padicNorm.padicNorm_p_lt_one_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：padicNorm_p_lt_one_of_prime [Fact p.Prime] : padicNorm p p < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.padicNorm_p_lt_one`：padicNorm_p_lt_one (hp : 1 < p) : padicNor
m p p < 1
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
The `p`-adic norm of `p` is less than `1` if `p` is prime.

See also `padicNorm.padicNorm_p_lt_one` for a version assuming `1 < p`.
-/
theorem padicNorm_p_lt_one_of_prime [Fact p.Prime] : padicNorm p p < 1 :=
  padicNorm_p_lt_one <| Nat.Prime.one_lt Fact.out

/-- `padicNorm p q` takes discrete values `p ^ -z` for `z : ℤ`. -/
/-
**padicNorm.values_discrete** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ} {q : ℚ}, q ≠ 0 → ∃ z, padicNorm p q = ↑p ^ (-z)
参数：-z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`padicNorm p q` takes discrete values `p ^ -z` for `z : ℤ`.
-/
protected theorem values_discrete {q : ℚ} (hq : q ≠ 0) : ∃ z : ℤ, padicNorm p q = (p : ℚ) ^ (-z) :=
  ⟨padicValRat p q, by simp [padicNorm, hq]⟩

/-- `padicNorm p` is symmetric. -/
@[simp]
/-
**padicNorm.neg** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ} (q : ℚ), padicNorm p (-q) = padicNorm p q
参数：q : ℚ；-q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `padicNorm.zero`：∀ {p : ℕ}, padicNorm p 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `padicValRat.neg`：∀ {p : ℕ} (q : ℚ), padicValRat p (-q) = padicValRat p q
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹

--- 原说明 ---
`padicNorm p` is symmetric.
-/
protected theorem neg (q : ℚ) : padicNorm p (-q) = padicNorm p q :=
  if hq : q = 0 then by simp [hq] else by simp [padicNorm, hq]

variable [hp : Fact p.Prime]

/-- If `q ≠ 0`, then `padicNorm p q ≠ 0`. -/
/-
**padicNorm.nonzero** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q : ℚ}, q ≠ 0 → padicNorm p q ≠ 0
参数：Nat.Prime p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicNorm.eq_zpow_of_nonzero`：∀ {p : ℕ} {q : ℚ}, q ≠ 0 → padicNorm p q =
 ↑p ^ (-padicValRat p q)
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
If `q ≠ 0`, then `padicNorm p q ≠ 0`.
-/
protected theorem nonzero {q : ℚ} (hq : q ≠ 0) : padicNorm p q ≠ 0 := by
  rw [padicNorm.eq_zpow_of_nonzero hq]
  apply zpow_ne_zero
  exact mod_cast ne_of_gt hp.1.pos

/-- If the `p`-adic norm of `q` is 0, then `q` is `0`. -/
/-
**padicNorm.zero_of_padicNorm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：zero_of_padicNorm_eq_zero {q : Rat} (h : padicNorm p q = 0) : q = 0
参数：h : padicNorm p q = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
If the `p`-adic norm of `q` is 0, then `q` is `0`.
-/
theorem zero_of_padicNorm_eq_zero {q : ℚ} (h : padicNorm p q = 0) : q = 0 := by
  apply by_contradiction; intro hq
  unfold padicNorm at h; rw [if_neg hq] at h
  apply absurd h
  apply zpow_ne_zero
  exact mod_cast hp.1.ne_zero

/-- The `p`-adic norm is multiplicative. -/
@[simp]
/-
**padicNorm.mul** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q r : ℚ), padicNorm p (q * r) = padic
Norm p q * padicNorm p r
参数：Nat.Prime p；q r : ℚ；q * r。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `padicNorm.zero`：∀ {p : ℕ}, padicNorm p 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `padicValRat.mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ}, q ≠ 0 → 
r ≠ 0 → padicValRat p (q * r) = padicValRat p q + padicValRat p r
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The `p`-adic norm is multiplicative.
-/
protected theorem mul (q r : ℚ) : padicNorm p (q * r) = padicNorm p q * padicNorm p r :=
  if hq : q = 0 then by simp [hq]
  else
    if hr : r = 0 then by simp [hr]
    else by
      have : (p : ℚ) ≠ 0 := by simp [hp.1.ne_zero]
      simp [padicNorm, *, padicValRat.mul, zpow_add₀ this, mul_comm]

/-- The `p`-adic norm respects division. -/
@[simp]
/-
**padicNorm.div** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q r : ℚ), padicNorm p (q / r) = padic
Norm p q / padicNorm p r
参数：Nat.Prime p；q r : ℚ；q / r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `padicNorm.zero`：∀ {p : ℕ}, padicNorm p 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `eq_div_of_mul_eq`：eq_div_of_mul_eq (hc : c != 0) : a * c = b -> a = b / 
c
· 使用定理 `padicNorm.nonzero`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q : ℚ}, q ≠ 0 → 
padicNorm p q ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicNorm.mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q r : ℚ), padicNorm 
p (q * r) = padicNorm p q * padicNorm p r
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a

--- 原说明 ---
The `p`-adic norm respects division.
-/
protected theorem div (q r : ℚ) : padicNorm p (q / r) = padicNorm p q / padicNorm p r :=
  if hr : r = 0 then by simp [hr]
  else eq_div_of_mul_eq (padicNorm.nonzero hr) (by rw [← padicNorm.mul, div_mul_cancel₀ _ hr])

/-- The `p`-adic norm of an integer is at most `1`. -/
/-
**padicNorm.of_int** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (z : ℤ), padicNorm p ↑z ≤ 1
参数：Nat.Prime p；z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `padicNorm.zero`：∀ {p : ℕ}, padicNorm p 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicNorm.eq_1`：∀ (p : ℕ) (q : ℚ), padicNorm p q = if q = 0 then 0 else 
↑p ^ (-padicValRat p q)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `zpow_le_one_of_nonpos₀`：zpow_le_one_of_nonpos₀ (ha : 1 <= a) (hn : n <= 
0) : a ^ n <= 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Nat.Prime.one_le`：∀ {p : ℕ}, Nat.Prime p → 1 ≤ p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `padicValRat.of_int`：of_int {z : Int} : padicValRat p z = padicValInt p z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
The `p`-adic norm of an integer is at most `1`.
-/
protected theorem of_int (z : ℤ) : padicNorm p z ≤ 1 := by
  obtain rfl | hz := eq_or_ne z 0
  · simp
  · rw [padicNorm, if_neg (mod_cast hz)]
    exact zpow_le_one_of_nonpos₀ (mod_cast hp.1.one_le) (by simp)
/-
**padicNorm.nonarchimedean_aux** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem nonarchimedean_aux {q r : ℚ} (h : padicValRat p q ≤ padicValRat p r) :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) :=
  have hnqp : padicNorm p q ≥ 0 := padicNorm.nonneg _
  have hnrp : padicNorm p r ≥ 0 := padicNorm.nonneg _
  if hq : q = 0 then by simp [hq, max_eq_right hnrp]
  else
    if hr : r = 0 then by simp [hr, max_eq_left hnqp]
    else
      if hqr : q + r = 0 then le_trans (by simpa [hqr] using hnqp) (le_max_left _ _)
      else by
        unfold padicNorm; split_ifs
        apply le_max_iff.2
        left
        apply zpow_le_zpow_right₀
        · exact mod_cast le_of_lt hp.1.one_lt
        · apply neg_le_neg
          have : padicValRat p q = min (padicValRat p q) (padicValRat p r) := (min_eq_left h).symm
          rw [this]
          exact min_le_padicValRat_add hqr

/-- The `p`-adic norm is nonarchimedean: the norm of `p + q` is at most the max of the norm of `p`
and the norm of `q`. -/
/-
**padicNorm.nonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ}, padicNorm p (q + r) ≤ max (
padicNorm p q) (padicNorm p r)
参数：Nat.Prime p；q + r；padicNorm p q；padicNorm p r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `_private.Mathlib.NumberTheory.Padics.PadicNorm.0.padicNorm.nonarchimedea
n_aux`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ},   padicValRat p q ≤ padicV
alRat p r → padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a

--- 原说明 ---
The `p`-adic norm is nonarchimedean: the norm of `p + q` is at most the max of t
he norm of `p`
and the norm of `q`.
-/
protected theorem nonarchimedean {q r : ℚ} :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) := by
  wlog hle : padicValRat p q ≤ padicValRat p r generalizing q r
  · rw [add_comm, max_comm]
    exact this (le_of_not_ge hle)
  exact nonarchimedean_aux hle

/-- The `p`-adic norm respects the triangle inequality: the norm of `p + q` is at most the norm of
`p` plus the norm of `q`. -/
/-
**padicNorm.triangle_ineq** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：triangle_ineq (q r : Rat) : padicNorm p (q + r) <= padicNorm p q + padicNo
rm p r
参数：q r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.nonarchimedean`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ},
 padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r)
· 使用定理 `max_le_add_of_nonneg`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : 
AddZeroClass α] [AddLeftMono α] [AddRightMono α] {a b : α},   0 ≤ a → 0 ≤ b → ma
x a b ≤ a …
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `padicNorm.nonneg`：∀ {p : ℕ} (q : ℚ), 0 ≤ padicNorm p q

--- 原说明 ---
The `p`-adic norm respects the triangle inequality: the norm of `p + q` is at mo
st the norm of
`p` plus the norm of `q`.
-/
theorem triangle_ineq (q r : ℚ) : padicNorm p (q + r) ≤ padicNorm p q + padicNorm p r :=
  calc
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) := padicNorm.nonarchimedean
    _ ≤ padicNorm p q + padicNorm p r :=
      max_le_add_of_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)

/-- The `p`-adic norm of a difference is at most the max of each component. Restates the archimedean
property of the `p`-adic norm. -/
/-
**padicNorm.sub** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ}, padicNorm p (q - r) ≤ max (
padicNorm p q) (padicNorm p r)
参数：Nat.Prime p；q - r；padicNorm p q；padicNorm p r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicNorm.neg`：∀ {p : ℕ} (q : ℚ), padicNorm p (-q) = padicNorm p q
· 使用定理 `padicNorm.nonarchimedean`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ},
 padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r)

--- 原说明 ---
The `p`-adic norm of a difference is at most the max of each component. Restates
 the archimedean
property of the `p`-adic norm.
-/
protected theorem sub {q r : ℚ} : padicNorm p (q - r) ≤ max (padicNorm p q) (padicNorm p r) := by
  rw [sub_eq_add_neg, ← padicNorm.neg r]
  exact padicNorm.nonarchimedean

/-- The `p`-adic norm is an absolute value: positive-definite and multiplicative, satisfying the
triangle inequality. -/
/-
**padicNorm.** 是 Mathlib 中的一个实例，位于命名空间 `padicNorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `p`-adic norm is an absolute value: positive-definite and multiplicative, sa
tisfying the
triangle inequality.
-/
instance : IsAbsoluteValue (padicNorm p) where
  abv_nonneg' := padicNorm.nonneg
  abv_eq_zero' := ⟨zero_of_padicNorm_eq_zero, fun hx ↦ by simp [hx]⟩
  abv_add' := padicNorm.triangle_ineq
  abv_mul' := padicNorm.mul

/-- If the `p`-adic norms of `q` and `r` are different, then the norm of `q + r` is equal to the max
of the norms of `q` and `r`. -/
/-
**padicNorm.add_eq_max_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：add_eq_max_of_ne {q r : Rat} (hne : padicNorm p q != padicNorm p r) : padi
cNorm p (q + r) = max (padicNorm p q) (padicNorm p r)
参数：hne : padicNorm p q != padicNorm p r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNonarchimedean.add_eq_max_of_ne`：add_eq_max_of_ne {F α : Type*} [AddGr
oup α] [FunLike F α R] [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchime
dean f) {x y : α} (hne …
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `padicNorm.nonarchimedean`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ},
 padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r)

--- 原说明 ---
If the `p`-adic norms of `q` and `r` are different, then the norm of `q + r` is 
equal to the max
of the norms of `q` and `r`.
-/
theorem add_eq_max_of_ne {q r : ℚ} (hne : padicNorm p q ≠ padicNorm p r) :
    padicNorm p (q + r) = max (padicNorm p q) (padicNorm p r) :=
  IsNonarchimedean.add_eq_max_of_ne (f := IsAbsoluteValue.toAbsoluteValue (padicNorm p))
    (fun _ _ ↦ padicNorm.nonarchimedean) hne
/-
**padicNorm.dvd_iff_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：dvd_iff_norm_le {n : Nat} {z : Int} : ↑(p ^ n) ∣ z ↔ padicNorm p z <= (p :
 Rat) ^ (-n : Int)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zpow_le_zpow_iff_right₀`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [in
st_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀} [ZeroLEOneClass G₀]   {m n
 : ℤ}, 1 < a …
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `padicValRat.of_int`：of_int {z : Int} : padicValRat p z = padicValInt p z
· 使用定理 `padicValInt.of_ne_one_ne_zero`：of_ne_one_ne_zero {z : Int} (hp : p != 1)
 (hz : z != 0) : padicValInt p z = multiplicity (p : Int) z
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `FiniteMultiplicity.pow_dvd_iff_le_multiplicity`：FiniteMultiplicity.pow_d
vd_iff_le_multiplicity (hf : FiniteMultiplicity a b) {k : Nat} : a ^ k ∣ b ↔ k <
= multiplicity a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 34 条，此处仅展示前 30 条）
-/
theorem dvd_iff_norm_le {n : ℕ} {z : ℤ} : ↑(p ^ n) ∣ z ↔ padicNorm p z ≤ (p : ℚ) ^ (-n : ℤ) := by
  unfold padicNorm; split_ifs with hz
  · norm_cast at hz
    simp [hz]
  · rw [zpow_le_zpow_iff_right₀, neg_le_neg_iff, padicValRat.of_int,
      padicValInt.of_ne_one_ne_zero hp.1.ne_one _]
    · norm_cast
      rw [← FiniteMultiplicity.pow_dvd_iff_le_multiplicity]
      · norm_cast
      · apply Int.finiteMultiplicity_iff.2 ⟨by simp [hp.out.ne_one], mod_cast hz⟩
    · exact_mod_cast hz
    · exact_mod_cast hp.out.one_lt

/-- The `p`-adic norm of an integer `m` is one iff `p` doesn't divide `m`. -/
/-
**padicNorm.int_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：int_eq_one_iff (m : Int) : padicNorm p m = 1 ↔ ¬(p : Int) ∣ m
参数：m : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用引理 `inv_lt_one₀`：inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `inv_lt_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Linea
rOrder G₀] {a : G₀} [PosMulMono G₀], a⁻¹ < 0 ↔ a < 0
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `Nat.not_lt_zero`：∀ (n : ℕ), ¬n < 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `zpow_neg_one`：zpow_neg_one (x : G) : x ^ (-1 : Int) = x⁻¹
· 使用定理 `zpow_lt_zpow_iff_right₀`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [in
st_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀} [ZeroLEOneClass G₀]   {m n
 : ℤ}, 1 < a …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `padicValRat.of_int`：of_int {z : Int} : padicValRat p z = padicValInt p z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `zpow_right_inj₀`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : L
inearOrder G₀] {a : G₀} {m n : ℤ} [PosMulStrictMono G₀]   [ZeroLEOneClass G₀], 0
 < a …
（共 70 条，此处仅展示前 30 条）

--- 原说明 ---
The `p`-adic norm of an integer `m` is one iff `p` doesn't divide `m`.
-/
theorem int_eq_one_iff (m : ℤ) : padicNorm p m = 1 ↔ ¬(p : ℤ) ∣ m := by
  nth_rw 2 [← pow_one p]
  simp only [dvd_iff_norm_le, Nat.cast_one, zpow_neg, zpow_one, not_le]
  constructor
  · intro h
    rw [h, inv_lt_one₀] <;> norm_cast
    · exact Nat.Prime.one_lt Fact.out
    · exact Nat.Prime.pos Fact.out
  · simp only [padicNorm]
    split_ifs
    · rw [inv_lt_zero, ← Nat.cast_zero, Nat.cast_lt]
      intro h
      exact (Nat.not_lt_zero p h).elim
    · have : 1 < (p : ℚ) := by norm_cast; exact Nat.Prime.one_lt (Fact.out : Nat.Prime p)
      rw [← zpow_neg_one, zpow_lt_zpow_iff_right₀ this]
      have : 0 ≤ padicValRat p m := by simp only [of_int, Nat.cast_nonneg]
      intro h
      rw [← zpow_zero (p : ℚ), zpow_right_inj₀] <;> linarith
/-
**padicNorm.int_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：int_lt_one_iff (m : Int) : padicNorm p m < 1 ↔ (p : Int) ∣ m
参数：m : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `padicNorm.int_eq_one_iff`：int_eq_one_iff (m : Int) : padicNorm p m = 1 ↔
 ¬(p : Int) ∣ m
· 使用定理 `eq_iff_le_not_lt`：eq_iff_le_not_lt : a = b ↔ a <= b ∧ ¬a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem int_lt_one_iff (m : ℤ) : padicNorm p m < 1 ↔ (p : ℤ) ∣ m := by
  rw [← not_iff_not, ← int_eq_one_iff, eq_iff_le_not_lt]
  simp only [padicNorm.of_int, true_and]
/-
**padicNorm.of_nat** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：of_nat (m : Nat) : padicNorm p m <= 1
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.of_int`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (z : ℤ), padicNorm
 p ↑z ≤ 1
-/
theorem of_nat (m : ℕ) : padicNorm p m ≤ 1 :=
  padicNorm.of_int (m : ℤ)

/-- The `p`-adic norm of a natural `m` is one iff `p` doesn't divide `m`. -/
/-
**padicNorm.nat_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：nat_eq_one_iff (m : Nat) : padicNorm p m = 1 ↔ ¬p ∣ m
参数：m : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `padicNorm.int_eq_one_iff`：int_eq_one_iff (m : Int) : padicNorm p m = 1 ↔
 ¬(p : Int) ∣ m
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `p`-adic norm of a natural `m` is one iff `p` doesn't divide `m`.
-/
theorem nat_eq_one_iff (m : ℕ) : padicNorm p m = 1 ↔ ¬p ∣ m := by
  rw [← Int.natCast_dvd_natCast, ← int_eq_one_iff, Int.cast_natCast]
/-
**padicNorm.nat_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：nat_lt_one_iff (m : Nat) : padicNorm p m < 1 ↔ p ∣ m
参数：m : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `padicNorm.int_lt_one_iff`：int_lt_one_iff (m : Int) : padicNorm p m < 1 ↔
 (p : Int) ∣ m
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nat_lt_one_iff (m : ℕ) : padicNorm p m < 1 ↔ p ∣ m := by
  rw [← Int.natCast_dvd_natCast, ← int_lt_one_iff, Int.cast_natCast]

/-- If a rational is not a p-adic integer, it is not an integer. -/
/-
**padicNorm.not_int_of_not_padic_int** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：not_int_of_not_padic_int (p : Nat) {a : Rat} [hp : Fact (Nat.Prime p)] (H 
: 1 < padicNorm p a) : ¬ a.isInt
参数：p : Nat；Nat.Prime p；H : 1 < padicNorm p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.eq_num_of_isInt`：eq_num_of_isInt {q : Rat} (h : q.isInt) : q = q.num
· 使用定理 `padicNorm.of_int`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (z : ℤ), padicNorm
 p ↑z ≤ 1

--- 原说明 ---
If a rational is not a p-adic integer, it is not an integer.
-/
theorem not_int_of_not_padic_int (p : ℕ) {a : ℚ} [hp : Fact (Nat.Prime p)]
    (H : 1 < padicNorm p a) : ¬ a.isInt := by
  contrapose! H
  rw [Rat.eq_num_of_isInt H]
  apply padicNorm.of_int
/-
**padicNorm.sum_lt** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：sum_lt {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α} (hs : s.Nonempt
y) (hF : forall i in s, padicNorm p (F i) < t) : padicNorm p (∑ i in s, F i) < t
参数：hs : s.Nonempty；hF : forall i in s, padicNorm p (F i) < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `IsNonarchimedean.apply_sum_le_sup`：apply_sum_le_sup {α β : Type*} [AddCo
mmMonoid α] {f : α -> R} (nonarch : IsNonarchimedean f) {s : Finset β} (hnonempt
y : s.Nonempty) {l : β …
· 使用定理 `padicNorm.nonarchimedean`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ},
 padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sup'_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder 
α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α},   s.sup' H f < a ↔ ∀ i ∈
 s, f i …
-/
theorem sum_lt {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α} (hs : s.Nonempty)
    (hF : ∀ i ∈ s, padicNorm p (F i) < t) : padicNorm p (∑ i ∈ s, F i) < t :=
  lt_of_le_of_lt (IsNonarchimedean.apply_sum_le_sup (fun _ _ ↦ padicNorm.nonarchimedean) hs) <|
    (Finset.sup'_lt_iff hs).2 hF
/-
**padicNorm.sum_le** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：sum_le {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α} (hs : s.Nonempt
y) (hF : forall i in s, padicNorm p (F i) <= t) : padicNorm p (∑ i in s, F i) <=
 t
参数：hs : s.Nonempty；hF : forall i in s, padicNorm p (F i) <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `IsNonarchimedean.apply_sum_le_sup`：apply_sum_le_sup {α β : Type*} [AddCo
mmMonoid α] {f : α -> R} (nonarch : IsNonarchimedean f) {s : Finset β} (hnonempt
y : s.Nonempty) {l : β …
· 使用定理 `padicNorm.nonarchimedean`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ},
 padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sup'_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   s.sup' H f ≤ a ↔ ∀ 
b ∈ s, f…
-/
theorem sum_le {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α} (hs : s.Nonempty)
    (hF : ∀ i ∈ s, padicNorm p (F i) ≤ t) : padicNorm p (∑ i ∈ s, F i) ≤ t :=
  (IsNonarchimedean.apply_sum_le_sup (fun _ _ ↦ padicNorm.nonarchimedean) hs).trans <|
    (Finset.sup'_le_iff hs (fun i ↦ padicNorm p (F i))).2 hF
/-
**padicNorm.sum_lt'** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：sum_lt' {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α} (hF : forall i
 in s, padicNorm p (F i) < t) (ht : 0 < t) : padicNorm p (∑ i in s, F i) < t
参数：hF : forall i in s, padicNorm p (F i) < t；ht : 0 < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicNorm.zero`：∀ {p : ℕ}, padicNorm p 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicNorm.sum_lt`：sum_lt {α : Type*} {F : α -> Rat} {t : Rat} {s : Finse
t α} (hs : s.Nonempty) (hF : forall i in s, padicNorm p (F i) < t) : padicNorm p
 (∑ i …
-/
theorem sum_lt' {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α}
    (hF : ∀ i ∈ s, padicNorm p (F i) < t) (ht : 0 < t) : padicNorm p (∑ i ∈ s, F i) < t := by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_lt hs hF
/-
**padicNorm.sum_le'** 是 Mathlib 中的一个定理，位于命名空间 `padicNorm`。
形式化陈述：sum_le' {α : Type*} {F : α -> Rat} {t : Rat} {s : Finset α} (hF : forall i
 in s, padicNorm p (F i) <= t) (ht : 0 <= t) : padicNorm p (∑ i in s, F i) <= t
参数：hF : forall i in s, padicNorm p (F i) <= t；ht : 0 <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicNorm.zero`：∀ {p : ℕ}, padicNorm p 0 = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicNorm.sum_le`：sum_le {α : Type*} {F : α -> Rat} {t : Rat} {s : Finse
t α} (hs : s.Nonempty) (hF : forall i in s, padicNorm p (F i) <= t) : padicNorm 
p (∑ i…
-/
theorem sum_le' {α : Type*} {F : α → ℚ} {t : ℚ} {s : Finset α}
    (hF : ∀ i ∈ s, padicNorm p (F i) ≤ t) (ht : 0 ≤ t) : padicNorm p (∑ i ∈ s, F i) ≤ t := by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_le hs hF

end padicNorm

