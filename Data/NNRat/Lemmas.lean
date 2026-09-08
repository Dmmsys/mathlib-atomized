/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.Zify

/-!
# Field and action structures on the nonnegative rationals

This file provides additional results about `NNRat` that cannot live in earlier files due to import
cycles.
-/

@[expose] public section

open Function
open scoped NNRat

namespace NNRat
variable {α : Type*} {q : ℚ≥0}

@[simp, norm_cast]
/-
**NNRat.coe_indicator** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：coe_indicator (s : Set α) (f : α -> Rat>=0) (a : α) : ((s.indicator f a : 
Rat>=0) : Rat) = s.indicator (fun x => ↑(f x)) a
参数：s : Set α；f : α -> Rat>=0；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_indicator`：∀ {α : Type u_1} {M : Type u_6} {N : Type u_7} {F : Type 
u_8} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass 
F M…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma coe_indicator (s : Set α) (f : α → ℚ≥0) (a : α) :
    ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (fun x ↦ ↑(f x)) a :=
  map_indicator coeHom _ _ _

end NNRat

open NNRat

namespace Rat

variable {p q : ℚ}

/-
**Rat.toNNRat_inv** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：toNNRat_inv (q : Rat) : toNNRat q⁻¹ = (toNNRat q)⁻¹
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.toNNRat_eq_zero`：toNNRat_eq_zero : toNNRat q = 0 ↔ q <= 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `inv_nonpos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Linear
Order G₀] {a : G₀} [PosMulMono G₀], a⁻¹ ≤ 0 ↔ a ≤ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.coe_toNNRat`：∀ (q : ℚ), 0 ≤ q → ↑q.toNNRat = q
· 使用定理 `NNRat.coe_inv`：∀ (q : ℚ≥0), ↑q⁻¹ = (↑q)⁻¹
· 使用定理 `NNRat.toNNRat_coe`：toNNRat_coe (q : Rat>=0) : toNNRat q = q
-/
lemma toNNRat_inv (q : ℚ) : toNNRat q⁻¹ = (toNNRat q)⁻¹ := by
  obtain hq | hq := le_total q 0
  · rw [toNNRat_eq_zero.mpr hq, inv_zero, toNNRat_eq_zero.mpr (inv_nonpos.mpr hq)]
  · nth_rw 1 [← Rat.coe_toNNRat q hq]
    rw [← coe_inv, toNNRat_coe]
/-
**Rat.toNNRat_div** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：toNNRat_div (hp : 0 <= p) : toNNRat (p / q) = toNNRat p / toNNRat q
参数：hp : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.toNNRat_inv`：toNNRat_inv (q : Rat) : toNNRat q⁻¹ = (toNNRat q)⁻¹
· 使用定理 `Rat.toNNRat_mul`：toNNRat_mul (hp : 0 <= p) : toNNRat (p * q) = toNNRat p
 * toNNRat q
-/
lemma toNNRat_div (hp : 0 ≤ p) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← toNNRat_inv, ← toNNRat_mul hp]
/-
**Rat.toNNRat_div'** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：toNNRat_div' (hq : 0 <= q) : toNNRat (p / q) = toNNRat p / toNNRat q
参数：hq : 0 <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Rat.toNNRat_mul`：toNNRat_mul (hp : 0 <= p) : toNNRat (p * q) = toNNRat p
 * toNNRat q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Rat.toNNRat_inv`：toNNRat_inv (q : Rat) : toNNRat q⁻¹ = (toNNRat q)⁻¹
-/
lemma toNNRat_div' (hq : 0 ≤ q) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_inv_mul, div_eq_inv_mul, toNNRat_mul (inv_nonneg.2 hq), toNNRat_inv]

end Rat

/-! ### Numerator and denominator -/

namespace NNRat

variable {q : ℚ≥0}

/-- A recursor for nonnegative rationals in terms of numerators and denominators. -/
/-
**NNRat.rec** 是 Mathlib 中的一个定义，位于命名空间 `NNRat`。
形式化陈述：{α : ℚ≥0 → Sort u_1} → ((m n : ℕ) → α (↑m / ↑n)) → (q : ℚ≥0) → α q
参数：(m n : ℕ) → α (↑m / ↑n)；q : ℚ≥0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for nonnegative rationals in terms of numerators and denominators.
-/
protected def rec {α : ℚ≥0 → Sort*} (h : ∀ m n : ℕ, α (m / n)) (q : ℚ≥0) : α q := by
  rw [← num_div_den q]; apply h
/-
**NNRat.mul_num** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：mul_num (q₁ q₂ : Rat>=0) : (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.n
um * q₂.num) (q₁.den * q₂.den)
参数：q₁ q₂ : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.mul_num`：mul_num (q₁ q₂ : Rat) : (q₁ * q₂).num = q₁.num * q₂.num / N
at.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den)
-/
theorem mul_num (q₁ q₂ : ℚ≥0) :
    (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.num * q₂.num) (q₁.den * q₂.den) := by
  zify
  convert! Rat.mul_num q₁ q₂ <;> norm_cast
/-
**NNRat.mul_den** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：mul_den (q₁ q₂ : Rat>=0) : (q₁ * q₂).den = q₁.den * q₂.den / Nat.gcd (q₁.n
um * q₂.num) (q₁.den * q₂.den)
参数：q₁ q₂ : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `Rat.mul_den`：mul_den (q₁ q₂ : Rat) : (q₁ * q₂).den = q₁.den * q₂.den / N
at.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den)
-/
theorem mul_den (q₁ q₂ : ℚ≥0) :
    (q₁ * q₂).den = q₁.den * q₂.den / Nat.gcd (q₁.num * q₂.num) (q₁.den * q₂.den) := by
  convert! Rat.mul_den q₁ q₂
  norm_cast

/-- A version of `NNRat.mul_den` without division. -/
/-
**NNRat.den_mul_den_eq_den_mul_gcd** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：den_mul_den_eq_den_mul_gcd (q₁ q₂ : Rat>=0) : q₁.den * q₂.den = (q₁ * q₂).
den * ((q₁.num * q₂.num).gcd (q₁.den * q₂.den))
参数：q₁ q₂ : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `Rat.den_mul_den_eq_den_mul_gcd`：den_mul_den_eq_den_mul_gcd (q₁ q₂ : Rat)
 : q₁.den * q₂.den = (q₁ * q₂).den * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.
den))

--- 原说明 ---
A version of `NNRat.mul_den` without division.
-/
theorem den_mul_den_eq_den_mul_gcd (q₁ q₂ : ℚ≥0) :
    q₁.den * q₂.den = (q₁ * q₂).den * ((q₁.num * q₂.num).gcd (q₁.den * q₂.den)) := by
  convert! Rat.den_mul_den_eq_den_mul_gcd q₁ q₂
  norm_cast

/-- A version of `NNRat.mul_num` without division. -/
/-
**NNRat.num_mul_num_eq_num_mul_gcd** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：num_mul_num_eq_num_mul_gcd (q₁ q₂ : Rat>=0) : q₁.num * q₂.num = (q₁ * q₂).
num * ((q₁.num * q₂.num).gcd (q₁.den * q₂.den))
参数：q₁ q₂ : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `Rat.num_mul_num_eq_num_mul_gcd`：num_mul_num_eq_num_mul_gcd (q₁ q₂ : Rat)
 : q₁.num * q₂.num = (q₁ * q₂).num * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.
den))

--- 原说明 ---
A version of `NNRat.mul_num` without division.
-/
theorem num_mul_num_eq_num_mul_gcd (q₁ q₂ : ℚ≥0) :
    q₁.num * q₂.num = (q₁ * q₂).num * ((q₁.num * q₂.num).gcd (q₁.den * q₂.den)) := by
  zify
  convert! Rat.num_mul_num_eq_num_mul_gcd q₁ q₂ <;> norm_cast

end NNRat

