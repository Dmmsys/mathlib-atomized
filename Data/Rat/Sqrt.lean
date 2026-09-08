/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Int.Sqrt

/-!
# Square root on rational numbers

This file defines the square root function on rational numbers `Rat.sqrt`
and proves several theorems about it.

-/

@[expose] public section


namespace Rat

/-- Square root function on rational numbers, defined by taking the (integer) square root of the
numerator and the square root (on natural numbers) of the denominator. -/
@[pp_nodot]
/-
**Rat.sqrt** 是 Mathlib 中的一个定义，位于命名空间 `Rat`。
形式化陈述：sqrt (q : Rat) : Rat
参数：q : Rat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Square root function on rational numbers, defined by taking the (integer) square
 root of the
numerator and the square root (on natural numbers) of the denominator.
-/
def sqrt (q : ℚ) : ℚ := mkRat (Int.sqrt q.num) (Nat.sqrt q.den)
/-
**Rat.sqrt_eq** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：sqrt_eq (q : Rat) : Rat.sqrt (q * q) = |q|
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.sqrt.eq_1`：∀ (q : ℚ), Rat.sqrt q = mkRat (Int.sqrt q.num) q.den.sqrt
· 使用定理 `Rat.mul_self_num`：mul_self_num (q : Rat) : (q * q).num = q.num * q.num
· 使用定理 `Rat.mul_self_den`：mul_self_den (q : Rat) : (q * q).den = q.den * q.den
· 使用定理 `Int.sqrt_eq`：sqrt_eq (n : Int) : sqrt (n * n) = n.natAbs
· 使用引理 `Nat.sqrt_eq`：sqrt_eq (n : Nat) : sqrt (n * n) = n
· 使用定理 `Rat.abs_def`：abs_def (q : Rat) : |q| = q.num.natAbs /. q.den
· 使用定理 `Rat.divInt_ofNat`：∀ (num : ℤ) (den : ℕ), Rat.divInt num ↑den = mkRat num
 den
-/
theorem sqrt_eq (q : ℚ) : Rat.sqrt (q * q) = |q| := by
  rw [sqrt, mul_self_num, mul_self_den, Int.sqrt_eq, Nat.sqrt_eq, abs_def, divInt_ofNat]
/-
**Rat.exists_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：exists_mul_self (x : Rat) : (exists q, q * q = x) ↔ Rat.sqrt x * Rat.sqrt 
x = x
参数：x : Rat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.sqrt_eq`：sqrt_eq (q : Rat) : Rat.sqrt (q * q) = |q|
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
-/
theorem exists_mul_self (x : ℚ) : (∃ q, q * q = x) ↔ Rat.sqrt x * Rat.sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, abs_mul_abs_self], fun h => ⟨Rat.sqrt x, h⟩⟩
/-
**Rat.sqrt_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：sqrt_nonneg (q : Rat) : 0 <= Rat.sqrt q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.mkRat_nonneg`：∀ {a : ℤ}, 0 ≤ a → ∀ (b : ℕ), 0 ≤ mkRat a b
· 使用定理 `Int.sqrt_nonneg`：sqrt_nonneg (n : Int) : 0 <= sqrt n
-/
lemma sqrt_nonneg (q : ℚ) : 0 ≤ Rat.sqrt q := mkRat_nonneg (Int.sqrt_nonneg _) _

/-- `IsSquare` can be decided on `ℚ` by checking against the square root. -/
/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSquare` can be decided on `ℚ` by checking against the square root.
-/
instance : DecidablePred (IsSquare : ℚ → Prop) :=
  fun m => decidable_of_iff' (sqrt m * sqrt m = m) <| by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]

@[simp, norm_cast]
/-
**Rat.sqrt_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：sqrt_intCast (z : Int) : Rat.sqrt (z : Rat) = Int.sqrt z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sqrt_one`：Nat.sqrt 1 = 1
· 使用定理 `Rat.mkRat_one`：∀ (x : ℤ), mkRat x 1 = ↑x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sqrt_intCast (z : ℤ) : Rat.sqrt (z : ℚ) = Int.sqrt z := by
  simp only [sqrt, num_intCast, den_intCast, Nat.sqrt_one, mkRat_one]

@[simp, norm_cast]
/-
**Rat.sqrt_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：sqrt_natCast (n : Nat) : Rat.sqrt (n : Rat) = Nat.sqrt n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.sqrt_intCast`：sqrt_intCast (z : Int) : Rat.sqrt (z : Rat) = Int.sqrt
 z
· 使用定理 `Int.sqrt_natCast`：sqrt_natCast (n : Nat) : Int.sqrt (n : Int) = Nat.sqrt
 n
-/
theorem sqrt_natCast (n : ℕ) : Rat.sqrt (n : ℚ) = Nat.sqrt n := by
  rw [← Int.cast_natCast, sqrt_intCast, Int.sqrt_natCast, Int.cast_natCast]

@[simp]
/-
**Rat.sqrt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：sqrt_ofNat (n : Nat) : Rat.sqrt (ofNat(n) : Rat) = Nat.sqrt (OfNat.ofNat n
)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.sqrt_natCast`：sqrt_natCast (n : Nat) : Rat.sqrt (n : Rat) = Nat.sqrt
 n
-/
theorem sqrt_ofNat (n : ℕ) : Rat.sqrt (ofNat(n) : ℚ) = Nat.sqrt (OfNat.ofNat n) :=
  sqrt_natCast _

end Rat

