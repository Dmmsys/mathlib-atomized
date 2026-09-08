/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Rat.NatSqrt.Defs

/-!
Comparisons between rational approximations to the square root of a natural number
and the real square root.
-/

public section

namespace Nat

/-
**Nat.ratSqrt_le_realSqrt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ratSqrt_le_realSqrt (x : Nat) {prec : Nat} (h : 0 < prec) : ratSqrt x prec
 <= √x
参数：x : Nat；h : 0 < prec。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ratSqrt_sq_le`：ratSqrt_sq_le (x : Nat) {prec : Nat} (h : 0 < prec) :
 (ratSqrt x prec) ^ 2 <= x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt_monotone`：sqrt_monotone : Monotone Real.sqrt
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `Nat.ratSqrt_nonneg`：ratSqrt_nonneg (x prec : Nat) : 0 <= ratSqrt x prec
-/
theorem ratSqrt_le_realSqrt (x : ℕ) {prec : ℕ} (h : 0 < prec) : ratSqrt x prec ≤ √x := by
  have := ratSqrt_sq_le (x := x) h
  have : (x.ratSqrt prec ^ 2 : ℝ) ≤ ↑x := by norm_cast
  have := Real.sqrt_monotone this
  rwa [Real.sqrt_sq] at this
  simpa only [Rat.cast_nonneg] using ratSqrt_nonneg _ _
/-
**Nat.realSqrt_lt_ratSqrt_add_inv_prec** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：realSqrt_lt_ratSqrt_add_inv_prec (x : Nat) {prec : Nat} (h : 0 < prec) : √
x < ratSqrt x prec + 1 / prec
参数：x : Nat；h : 0 < prec。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_ratSqrt_add_inv_prec_sq`：lt_ratSqrt_add_inv_prec_sq (x : Nat) {pr
ec : Nat} (h : 0 < prec) : x < (ratSqrt x prec + 1 / prec) ^ 2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.sqrt_lt_sqrt`：sqrt_lt_sqrt (hx : 0 <= x) (h : x < y) : √x < √y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.ratSqrt_nonneg`：ratSqrt_nonneg (x prec : Nat) : 0 <= ratSqrt x prec
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Rat.cast_pow`：cast_pow (p : Rat) (n : Nat) : ↑(p ^ n) = (p ^ n : α)
-/
theorem realSqrt_lt_ratSqrt_add_inv_prec (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    √x < ratSqrt x prec + 1 / prec := by
  have := lt_ratSqrt_add_inv_prec_sq (x := x) h
  have : (x : ℝ) < ↑((x.ratSqrt prec + 1 / prec) ^ 2 : ℚ) := by norm_cast
  have := Real.sqrt_lt_sqrt (by simp) this
  rw [Rat.cast_pow, Real.sqrt_sq] at this
  · push_cast at this
    exact this
  · push_cast
    exact add_nonneg (by simpa using ratSqrt_nonneg _ _) (by simp)
/-
**Nat.realSqrt_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：realSqrt_mem_Ico (x : Nat) {prec : Nat} (h : 0 < prec) : √x in Set.Ico (ra
tSqrt x prec : Real) (ratSqrt x prec + 1 / prec : Real)
参数：x : Nat；h : 0 < prec。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem realSqrt_mem_Ico (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    √x ∈ Set.Ico (ratSqrt x prec : ℝ) (ratSqrt x prec + 1 / prec : ℝ) := by
  grind [ratSqrt_le_realSqrt, realSqrt_lt_ratSqrt_add_inv_prec]

#adaptation_note
/--
nightly-2025-09-11
We're investigating changing the `grind` heuristics for selecting patterns.
Under one heuristic, the next proof would fail if we just passed `realSqrt_lt_ratSqrt_add_inv_prec`
to `grind` in the next proof.
So for robustness I'm explicitly setting the pattern here.
-/
local grind_pattern realSqrt_lt_ratSqrt_add_inv_prec => (x.ratSqrt prec : ℝ)

/-
**Nat.ratSqrt_mem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ratSqrt_mem_Ioc (x : Nat) {prec : Nat} (h : 0 < prec) : (ratSqrt x prec : 
Real) in Set.Ioc (√x - 1 / prec) √x
参数：x : Nat；h : 0 < prec。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ratSqrt_mem_Ioc (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    (ratSqrt x prec : ℝ) ∈ Set.Ioc (√x - 1 / prec) √x := by
  grind [ratSqrt_le_realSqrt]

end Nat

