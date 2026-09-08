/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The Wallis formula for Pi

This file establishes the Wallis product for `π` (`Real.tendsto_prod_pi_div_two`). Our proof is
largely about analyzing the behaviour of the sequence `∫ x in 0..π, sin x ^ n` as `n → ∞`.
See: https://en.wikipedia.org/wiki/Wallis_product

The proof can be broken down into two pieces. The first step (carried out in
`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`) is to use repeated integration by parts to
obtain an explicit formula for this integral, which is rational if `n` is odd and a rational
multiple of `π` if `n` is even.

The second step, carried out here, is to estimate the ratio
`∫ (x : ℝ) in 0..π, sin x ^ (2 * k + 1) / ∫ (x : ℝ) in 0..π, sin x ^ (2 * k)` and prove that
it converges to one using the squeeze theorem. The final product for `π` is obtained after some
algebraic manipulation.

## Main statements

* `Real.Wallis.W`: the product of the first `k` terms in Wallis' formula for `π`.
* `Real.Wallis.W_eq_integral_sin_pow_div_integral_sin_pow`: express `W n` as a ratio of integrals.
* `Real.Wallis.W_le` and `Real.Wallis.le_W`: upper and lower bounds for `W n`.
* `Real.tendsto_prod_pi_div_two`: the Wallis product formula.
-/

@[expose] public section


open scoped Real Topology Nat

open Filter Finset intervalIntegral

namespace Real

namespace Wallis


/-- The product of the first `k` terms in Wallis' formula for `π`. -/
/-
**Real.Wallis.W** 是 Mathlib 中的一个定义，位于命名空间 `Real.Wallis`。
形式化陈述：W (k : Nat) : Real
参数：k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of the first `k` terms in Wallis' formula for `π`.
-/
noncomputable def W (k : ℕ) : ℝ :=
  ∏ i ∈ range k, (2 * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))
/-
**Real.Wallis.W_succ** 是 Mathlib 中的一个定理，位于命名空间 `Real.Wallis`。
形式化陈述：W_succ (k : Nat) : W (k + 1) = W k * ((2 * k + 2) / (2 * k + 1) * ((2 * k 
+ 2) / (2 * k + 3)))
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
-/
theorem W_succ (k : ℕ) :
    W (k + 1) = W k * ((2 * k + 2) / (2 * k + 1) * ((2 * k + 2) / (2 * k + 3))) :=
  prod_range_succ _ _
/-
**Real.Wallis.W_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real.Wallis`。
形式化陈述：W_pos (k : Nat) : 0 < W k
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Wallis.W_succ`：W_succ (k : Nat) : W (k + 1) = W k * ((2 * k + 2) / 
(2 * k + 1) * ((2 * k + 2) / (2 * k + 3)))
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem W_pos (k : ℕ) : 0 < W k := by
  induction k with
  | zero => unfold W; simp
  | succ k hk =>
    rw [W_succ]
    refine mul_pos hk (mul_pos (div_pos ?_ ?_) (div_pos ?_ ?_)) <;> positivity
/-
**Real.Wallis.W_eq_factorial_ratio** 是 Mathlib 中的一个定理，位于命名空间 `Real.Wallis`。
形式化陈述：W_eq_factorial_ratio (n : Nat) : W n = 2 ^ (4 * n) * n ! ^ 4 / ((2 * n)! ^
 2 * (2 * n + 1))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_range_zero`：prod_range_zero (f : Nat -> M) : ∏ k in range 0,
 f k = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.one_natPow`：one_natPow : Nat.pow (nat_lit 1) b = na
t_lit 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_eq_div_iff`：div_eq_div_iff (hb : b != 0) (hd : d != 0) : a / b = c /
 d ↔ a * d = c * b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 83 条，此处仅展示前 30 条）
-/
theorem W_eq_factorial_ratio (n : ℕ) :
    W n = 2 ^ (4 * n) * n ! ^ 4 / ((2 * n)! ^ 2 * (2 * n + 1)) := by
  induction n with
  | zero =>
    simp only [W, prod_range_zero, Nat.factorial_zero, mul_zero, pow_zero]
    norm_num
  | succ n IH =>
    unfold W at IH ⊢
    rw [prod_range_succ, IH, _root_.div_mul_div_comm, _root_.div_mul_div_comm]
    refine (div_eq_div_iff ?_ ?_).mpr ?_
    any_goals exact ne_of_gt (by positivity)
    simp_rw [Nat.mul_succ, Nat.factorial_succ, pow_succ]
    push_cast
    ring_nf
/-
**Real.Wallis.W_eq_integral_sin_pow_div_integral_sin_pow** 是 Mathlib 中的一个定理，位于命名
空间 `Real.Wallis`。
形式化陈述：W_eq_integral_sin_pow_div_integral_sin_pow (k : Nat) : (π / 2)⁻¹ * W k = (
∫ x : Real in 0..π, sin x ^ (2 * k + 1)) / ∫ x : Real in 0..π, sin x ^ (2 * k)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `integral_sin_pow_even`：integral_sin_pow_even : (∫ x in 0..π, sin x ^ (2 
* n)) = π * ∏ i in range n, (2 * (i : Real) + 1) / (2 * i + 2)
· 使用定理 `integral_sin_pow_odd`：integral_sin_pow_odd : (∫ x in 0..π, sin x ^ (2 * 
n + 1)) = 2 * ∏ i in range n, (2 * (i : Real) + 2) / (2 * i + 3)
· 使用定理 `mul_div_mul_comm`：mul_div_mul_comm : a * b / (c * d) = a / c * (b / d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_div_distrib`：prod_div_distrib (f g : ι -> G) : ∏ x in s, f x
 / g x = (∏ x in s, f x) / ∏ x in s, g x
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `div_div_div_comm`：div_div_div_comm : a / b / (c / d) = a / c / (b / d)
· 使用定理 `div_div_eq_mul_div`：div_div_eq_mul_div : a / (b / c) = a * c / b
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
-/
theorem W_eq_integral_sin_pow_div_integral_sin_pow (k : ℕ) : (π / 2)⁻¹ * W k =
    (∫ x : ℝ in 0..π, sin x ^ (2 * k + 1)) / ∫ x : ℝ in 0..π, sin x ^ (2 * k) := by
  rw [integral_sin_pow_even, integral_sin_pow_odd, mul_div_mul_comm, ← prod_div_distrib, inv_div]
  simp_rw [div_div_div_comm, div_div_eq_mul_div, mul_div_assoc]
  rfl
/-
**Real.Wallis.W_le** 是 Mathlib 中的一个定理，位于命名空间 `Real.Wallis`。
形式化陈述：W_le (k : Nat) : W k <= π / 2
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_le_one`：div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.pi_div_two_pos`：pi_div_two_pos : 0 < π / 2
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Real.Wallis.W_eq_integral_sin_pow_div_integral_sin_pow`：W_eq_integral_si
n_pow_div_integral_sin_pow (k : Nat) : (π / 2)⁻¹ * W k = (∫ x : Real in 0..π, si
n x ^ (2 * k + 1)) / ∫ x : Real in 0..π, sin…
· 使用定理 `integral_sin_pow_pos`：integral_sin_pow_pos : 0 < ∫ x in 0..π, sin x ^ n
· 使用定理 `integral_sin_pow_succ_le`：integral_sin_pow_succ_le : (∫ x in 0..π, sin x
 ^ (n + 1)) <= ∫ x in 0..π, sin x ^ n
-/
theorem W_le (k : ℕ) : W k ≤ π / 2 := by
  rw [← div_le_one pi_div_two_pos, div_eq_inv_mul]
  rw [W_eq_integral_sin_pow_div_integral_sin_pow, div_le_one (integral_sin_pow_pos _)]
  apply integral_sin_pow_succ_le
/-
**Real.Wallis.le_W** 是 Mathlib 中的一个定理，位于命名空间 `Real.Wallis`。
形式化陈述：le_W (k : Nat) : ((2 : Real) * k + 1) / (2 * k + 2) * (π / 2) <= W k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.pi_div_two_pos`：pi_div_two_pos : 0 < π / 2
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Real.Wallis.W_eq_integral_sin_pow_div_integral_sin_pow`：W_eq_integral_si
n_pow_div_integral_sin_pow (k : Nat) : (π / 2)⁻¹ * W k = (∫ x : Real in 0..π, si
n x ^ (2 * k + 1)) / ∫ x : Real in 0..π, sin…
· 使用定理 `integral_sin_pow_pos`：integral_sin_pow_pos : 0 < ∫ x in 0..π, sin x ^ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `integral_sin_pow`：integral_sin_pow : (∫ x in a..b, sin x ^ (n + 2)) = (s
in a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b) / (n + 2) + (n + 1) / (n + 2) 
* ∫ x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.sin_pi`：sin_pi : sin π = 0
· 使用定理 `Real.cos_pi`：cos_pi : cos π = -1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
（共 37 条，此处仅展示前 30 条）
-/
theorem le_W (k : ℕ) : ((2 : ℝ) * k + 1) / (2 * k + 2) * (π / 2) ≤ W k := by
  rw [← le_div_iff₀ pi_div_two_pos, div_eq_inv_mul (W k) _]
  rw [W_eq_integral_sin_pow_div_integral_sin_pow, le_div_iff₀ (integral_sin_pow_pos _)]
  convert! integral_sin_pow_succ_le (2 * k + 1)
  rw [integral_sin_pow (2 * k)]
  simp
/-
**Real.Wallis.tendsto_W_nhds_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 `Real.Wallis`。
形式化陈述：tendsto_W_nhds_pi_div_two : Tendsto W atTop (𝓝 <| π / 2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `sub_div'`：sub_div' {a b c : K} (hc : c != 0) : b - a / c = (b * c - a) /
 c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftStrictMono α] {a b : α},   0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 66 条，此处仅展示前 30 条）
-/
theorem tendsto_W_nhds_pi_div_two : Tendsto W atTop (𝓝 <| π / 2) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds le_W W_le
  have : 𝓝 (π / 2) = 𝓝 ((1 - 0) * (π / 2)) := by rw [sub_zero, one_mul]
  rw [this]
  refine Tendsto.mul ?_ tendsto_const_nhds
  have h : ∀ n : ℕ, ((2 : ℝ) * n + 1) / (2 * n + 2) = 1 - 1 / (2 * n + 2) := by
    intro n
    rw [sub_div' (ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg
      (two_pos : 0 < (2 : ℝ)).le (Nat.cast_nonneg _)) two_pos)), one_mul]
    congr 1; ring
  simp_rw [h]
  refine (tendsto_const_nhds.div_atTop ?_).const_sub _
  refine Tendsto.atTop_add ?_ tendsto_const_nhds
  exact tendsto_natCast_atTop_atTop.const_mul_atTop two_pos

end Wallis

end Real

/-- Wallis' product formula for `π / 2`. -/
/-
**Real.tendsto_prod_pi_div_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.tendsto_prod_pi_div_two : Tendsto (fun k => ∏ i in range k, ((2 : Rea
l) * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))) atTop (𝓝 (π / 2))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.Wallis.tendsto_W_nhds_pi_div_two`：tendsto_W_nhds_pi_div_two : Tends
to W atTop (𝓝 <| π / 2)

--- 原说明 ---
Wallis' product formula for `π / 2`.
-/
theorem Real.tendsto_prod_pi_div_two :
    Tendsto (fun k => ∏ i ∈ range k, ((2 : ℝ) * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3)))
      atTop (𝓝 (π / 2)) :=
  Real.Wallis.tendsto_W_nhds_pi_div_two
