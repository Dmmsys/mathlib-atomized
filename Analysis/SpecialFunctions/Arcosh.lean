/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Inverse of the cosh function

In this file we define an inverse of cosh as a function from $[0, ∞)$ to $[1, ∞)$.

## Main definitions

- `Real.arcosh`: An inverse function of `Real.cosh` as a function from $[0, ∞)$ to $[1, ∞)$.

- `Real.coshPartialEquiv`: `Real.cosh` and `Real.arcosh` bundled as a `PartialEquiv`
  from $[0, ∞)$ to $[1, ∞)$.

- `Real.coshOpenPartialHomeomorph`: `Real.cosh` as an `OpenPartialHomeomorph` from $(0, ∞)$ to
  $(1, ∞)$.

## Main Results

- `Real.cosh_arcosh`, `Real.arcosh_cosh`: cosh and arcosh are inverse in the appropriate domains.

- `Real.cosh_bijOn`, `Real.cosh_injOn`, `Real.cosh_surjOn`: `Real.cosh` is bijective, injective and
  surjective as a function from $[0, ∞)$ to $[1, ∞)$

- `Real.arcosh_bijOn`, `Real.arcosh_injOn`, `Real.arcosh_surjOn`: `Real.arcosh` is bijective,
  injective and surjective as a function from $[1, ∞)$ to $[0, ∞)$

- `Real.continuousOn_arcosh`: arcosh is continuous on $[1, ∞)$

- `Real.differentiableOn_arcosh`, `Real.contDiffOn_arcosh`: `Real.arcosh` is
  differentiable, and continuously differentiable on $(1, ∞)$

## Tags

arcosh, arccosh, argcosh, acosh
-/

@[expose] public section


noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `arcosh` is defined using a logarithm, `arcosh x = log (x + √(x ^ 2 - 1))`. -/
@[pp_nodot]
/-
**Real.arcosh** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：arcosh (x : Real)
参数：x : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`arcosh` is defined using a logarithm, `arcosh x = log (x + √(x ^ 2 - 1))`.
-/
def arcosh (x : ℝ) :=
  log (x + √(x ^ 2 - 1))
/-
**Real.exp_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exp_arcosh {x : Real} (hx : 1 <= x) : exp (arcosh x) = x + √(x ^ 2 - 1)
参数：hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
-/
theorem exp_arcosh {x : ℝ} (hx : 1 ≤ x) : exp (arcosh x) = x + √(x ^ 2 - 1) := by
  apply exp_log
  positivity

@[simp]
/-
**Real.arcosh_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcosh_zero : arcosh 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem arcosh_zero : arcosh 1 = 0 := by simp [arcosh]
/-
**Real.add_sqrt_self_sq_sub_one_inv** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：add_sqrt_self_sq_sub_one_inv {x : Real} (hx : 1 <= x) : (x + √(x ^ 2 - 1))
⁻¹ = x - √(x ^ 2 - 1)
参数：hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two_sub_pow_two`：∀ {R : Type u} [inst : CommRing R] (a b : R), a ^ 2
 - b ^ 2 = (a + b) * (a - b)
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
lemma add_sqrt_self_sq_sub_one_inv {x : ℝ} (hx : 1 ≤ x) :
    (x + √(x ^ 2 - 1))⁻¹ = x - √(x ^ 2 - 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_two_sub_pow_two, sq_sqrt (sub_nonneg_of_le (one_le_pow₀ hx)), sub_sub_cancel]

/-- `arcosh` is the right inverse of `cosh` over $[1, ∞)$. -/
/-
**Real.cosh_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cosh_arcosh {x : Real} (hx : 1 <= x) : cosh (arcosh x) = x
参数：hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arcosh.eq_1`：∀ (x : ℝ), Real.arcosh x = Real.log (x + √(x ^ 2 - 1))
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.cosh_eq`：cosh_eq (x : Real) : cosh x = (exp x + exp (-x)) / 2
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用引理 `Real.add_sqrt_self_sq_sub_one_inv`：add_sqrt_self_sq_sub_one_inv {x : Rea
l} (hx : 1 <= x) : (x + √(x ^ 2 - 1))⁻¹ = x - √(x ^ 2 - 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
`arcosh` is the right inverse of `cosh` over $[1, ∞)$.
-/
theorem cosh_arcosh {x : ℝ} (hx : 1 ≤ x) : cosh (arcosh x) = x := by
  rw [arcosh, cosh_eq, exp_neg, exp_log (by positivity), add_sqrt_self_sq_sub_one_inv hx]
  ring
/-
**Real.arcosh_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcosh_eq_zero_iff {x : Real} (hx : 1 <= x) : arcosh x = 0 ↔ x = 1
参数：hx : 1 <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Real.exp_injective`：exp_injective : Function.Injective exp
· 使用定理 `Real.exp_arcosh`：exp_arcosh {x : Real} (hx : 1 <= x) : exp (arcosh x) = 
x + √(x ^ 2 - 1)
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
-/
theorem arcosh_eq_zero_iff {x : ℝ} (hx : 1 ≤ x) : arcosh x = 0 ↔ x = 1 := by
  rw [← exp_injective.eq_iff, exp_arcosh hx, exp_zero]
  grind
/-
**Real.sinh_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sinh_arcosh {x : Real} (hx : 1 <= x) : sinh (arcosh x) = √(x ^ 2 - 1)
参数：hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arcosh.eq_1`：∀ (x : ℝ), Real.arcosh x = Real.log (x + √(x ^ 2 - 1))
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.sinh_eq`：∀ (x : ℝ), Real.sinh x = (Real.exp x - Real.exp (-x)) / 2
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用引理 `Real.add_sqrt_self_sq_sub_one_inv`：add_sqrt_self_sq_sub_one_inv {x : Rea
l} (hx : 1 <= x) : (x + √(x ^ 2 - 1))⁻¹ = x - √(x ^ 2 - 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
（共 58 条，此处仅展示前 30 条）
-/
theorem sinh_arcosh {x : ℝ} (hx : 1 ≤ x) : sinh (arcosh x) = √(x ^ 2 - 1) := by
  rw [arcosh, sinh_eq, exp_neg, exp_log (by positivity), add_sqrt_self_sq_sub_one_inv hx]
  ring
/-
**Real.tanh_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tanh_arcosh {x : Real} (hx : 1 <= x) : tanh (arcosh x) = √(x ^ 2 - 1) / x
参数：hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.tanh_eq_sinh_div_cosh`：∀ (x : ℝ), Real.tanh x = Real.sinh x / Real.
cosh x
· 使用定理 `Real.sinh_arcosh`：sinh_arcosh {x : Real} (hx : 1 <= x) : sinh (arcosh x)
 = √(x ^ 2 - 1)
· 使用定理 `Real.cosh_arcosh`：cosh_arcosh {x : Real} (hx : 1 <= x) : cosh (arcosh x)
 = x
-/
theorem tanh_arcosh {x : ℝ} (hx : 1 ≤ x) : tanh (arcosh x) = √(x ^ 2 - 1) / x := by
  rw [tanh_eq_sinh_div_cosh, sinh_arcosh hx, cosh_arcosh hx]

/-- `arcosh` is the left inverse of `cosh` over $[0, ∞)$. -/
/-
**Real.arcosh_cosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcosh_cosh {x : Real} (hx : 0 <= x) : arcosh (cosh x) = x
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.arcosh.eq_1`：∀ (x : ℝ), Real.arcosh x = Real.log (x + √(x ^ 2 - 1))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_eq_exp`：exp_eq_exp {x y : Real} : exp x = exp y ↔ x = y
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.cosh_pos`：cosh_pos (x : Real) : 0 < Real.cosh x
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用定理 `Real.exp_sub_cosh`：exp_sub_cosh : exp x - cosh x = sinh x
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.sinh_nonneg_iff`：sinh_nonneg_iff : 0 <= sinh x ↔ 0 <= x
· 使用定理 `Real.sinh_sq`：∀ (x : ℝ), Real.sinh x ^ 2 = Real.cosh x ^ 2 - 1
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `pow_two_nonneg`：∀ {R : Type u} [inst : Semiring R] [inst_1 : LinearOrder
 R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a : R),   0 ≤ a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
`arcosh` is the left inverse of `cosh` over $[0, ∞)$.
-/
theorem arcosh_cosh {x : ℝ} (hx : 0 ≤ x) : arcosh (cosh x) = x := by
  rw [arcosh, ← exp_eq_exp, exp_log (by positivity), ← eq_sub_iff_add_eq', exp_sub_cosh,
    ← sq_eq_sq₀ (sqrt_nonneg _) (sinh_nonneg_iff.mpr hx), ← sinh_sq, sq_sqrt (pow_two_nonneg _)]
/-
**Real.arcosh_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcosh_nonneg {x : Real} (hx : 1 <= x) : 0 <= arcosh x
参数：hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.log_nonneg`：log_nonneg (hx : 1 <= x) : 0 <= log x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
-/
theorem arcosh_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ arcosh x := by
  apply log_nonneg
  calc
    1 ≤ x + 0 := by simpa
    _ ≤ x + √(x ^ 2 - 1) := by gcongr; positivity
/-
**Real.arcosh_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcosh_pos {x : Real} (hx : 1 < x) : 0 < arcosh x
参数：hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
-/
theorem arcosh_pos {x : ℝ} (hx : 1 < x) : 0 < arcosh x := by
  apply log_pos
  calc
    1 < x + 0 := by simpa
    _ ≤ x + √(x ^ 2 - 1) := by gcongr; positivity

/-- This holds for `Ioi 0` instead of only `Ici 1` due to junk values. -/
/-
**Real.strictMonoOn_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：strictMonoOn_arcosh : StrictMonoOn arcosh (Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.comp`：StrictMonoOn.comp (hg : StrictMonoOn g t) (hf : Stric
tMonoOn f s) (hs : Set.MapsTo f s t) : StrictMonoOn (g ∘ f) s
· 使用定理 `Real.strictMonoOn_log`：strictMonoOn_log : StrictMonoOn log (Set.Ioi 0)
· 使用定理 `StrictMonoOn.add_monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α
] [inst_1 : Preorder α] [inst_2 : Preorder β] {f g : β → α} {s : Set β}   [AddLe
ftMono α] [AddR…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `strictMonoOn_id`：strictMonoOn_id [Preorder α] {s : Set α} : StrictMonoOn
 id s
· 使用定理 `Real.sqrt_monotone`：sqrt_monotone : Monotone Real.sqrt
· 使用定理 `sub_le_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → ∀ (c : α), a - c ≤ b - c
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x

--- 原说明 ---
This holds for `Ioi 0` instead of only `Ici 1` due to junk values.
-/
theorem strictMonoOn_arcosh : StrictMonoOn arcosh (Ioi 0) := by
  refine strictMonoOn_log.comp ?_ fun x (hx : 0 < x) ↦ show 0 < x + √(x ^ 2 - 1) by positivity
  exact strictMonoOn_id.add_monotone fun x (hx : 0 < x) y (hy : 0 < y) hxy ↦ by gcongr

/-- This holds for `0 < x, y ≤ 1` due to junk values. -/
/-
**Real.arcosh_le_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcosh_le_arcosh {x y : Real} (hx : 0 < x) (hy : 0 < y) : arcosh x <= arco
sh y ↔ x <= y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.le_iff_le`：StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a <= f b ↔ a <= b
· 使用定理 `Real.strictMonoOn_arcosh`：strictMonoOn_arcosh : StrictMonoOn arcosh (Ioi
 0)

--- 原说明 ---
This holds for `0 < x, y ≤ 1` due to junk values.
-/
theorem arcosh_le_arcosh {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : arcosh x ≤ arcosh y ↔ x ≤ y :=
  strictMonoOn_arcosh.le_iff_le hx hy

/-- This holds for `0 < x, y ≤ 1` due to junk values. -/
/-
**Real.arcosh_lt_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcosh_lt_arcosh {x y : Real} (hx : 0 < x) (hy : 0 < y) : arcosh x < arcos
h y ↔ x < y
参数：hx : 0 < x；hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.lt_iff_lt`：StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a < f b ↔ a < b
· 使用定理 `Real.strictMonoOn_arcosh`：strictMonoOn_arcosh : StrictMonoOn arcosh (Ioi
 0)

--- 原说明 ---
This holds for `0 < x, y ≤ 1` due to junk values.
-/
theorem arcosh_lt_arcosh {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : arcosh x < arcosh y ↔ x < y :=
  strictMonoOn_arcosh.lt_iff_lt hx hy

/-- `Real.cosh` as a `PartialEquiv` from $[0, ∞)$ to $[1, ∞)$. -/
/-
**Real.coshPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：coshPartialEquiv : PartialEquiv Real Real where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.one_le_cosh`：one_le_cosh (x : Real) : 1 <= cosh x
· 使用定理 `Real.arcosh_nonneg`：arcosh_nonneg {x : Real} (hx : 1 <= x) : 0 <= arcosh
 x
· 使用定理 `Real.arcosh_cosh`：arcosh_cosh {x : Real} (hx : 0 <= x) : arcosh (cosh x)
 = x
· 使用定理 `Real.cosh_arcosh`：cosh_arcosh {x : Real} (hx : 1 <= x) : cosh (arcosh x)
 = x

--- 原说明 ---
`Real.cosh` as a `PartialEquiv` from $[0, ∞)$ to $[1, ∞)$.
-/
def coshPartialEquiv : PartialEquiv ℝ ℝ where
  toFun := cosh
  invFun := arcosh
  source := Ici 0
  target := Ici 1
  map_source' r _ := one_le_cosh r
  map_target' _ hr := arcosh_nonneg hr
  left_inv' _ hr := arcosh_cosh hr
  right_inv' _ hr := cosh_arcosh hr
/-
**Real.continuousOn_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousOn_arcosh : ContinuousOn arcosh (Ici 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_pos_of_pos_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, 0 < a → 0 ≤ b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Real.continuousOn_log`：continuousOn_log : ContinuousOn log {0}ᶜ
· 使用定理 `ContinuousOn.fun_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `ContinuousOn.sqrt`：ContinuousOn.sqrt (h : ContinuousOn f s) : Continuous
On (fun x => √(f x)) s
· 使用定理 `ContinuousOn.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `ContinuousOn.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] 
{f : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem continuousOn_arcosh : ContinuousOn arcosh (Ici 1) :=
  have {x : ℝ} (hx : x ∈ Ici 1) : 0 < x + √(x ^ 2 - 1) :=
    add_pos_of_pos_of_nonneg (show 0 < x by grind) (sqrt_nonneg _)
  continuousOn_log.comp (by fun_prop) (by grind [MapsTo])

/-- `Real.cosh` as an `OpenPartialHomeomorph` from $(0, ∞)$ to $(1, ∞)$. -/
/-
**Real.coshOpenPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：coshOpenPartialHomeomorph : OpenPartialHomeomorph Real Real where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Real.arcosh_pos`：arcosh_pos {x : Real} (hx : 1 < x) : 0 < arcosh x

--- 原说明 ---
`Real.cosh` as an `OpenPartialHomeomorph` from $(0, ∞)$ to $(1, ∞)$.
-/
def coshOpenPartialHomeomorph : OpenPartialHomeomorph ℝ ℝ where
  toFun := cosh
  invFun := arcosh
  source := Ioi 0
  target := Ioi 1
  map_source' _ hr := one_lt_cosh.mpr (ne_of_lt hr).symm
  map_target' _ hr := arcosh_pos hr
  left_inv' _ hr := arcosh_cosh (le_of_lt hr)
  right_inv' _ hr := cosh_arcosh (le_of_lt hr)
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := continuousOn_arcosh.mono Ioi_subset_Ici_self
/-
**Real.hasStrictDerivAt_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_arcosh {x : Real} (hx : x in Ioi 1) : HasStrictDerivAt ar
cosh (√(x ^ 2 - 1))⁻¹ x
参数：hx : x in Ioi 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sinh_arcosh`：sinh_arcosh {x : Real} (hx : 1 <= x) : sinh (arcosh x)
 = √(x ^ 2 - 1)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `OpenPartialHomeomorph.hasStrictDerivAt_symm`：OpenPartialHomeomorph.hasSt
rictDerivAt_symm (f : OpenPartialHomeomorph 𝕜 𝕜) {a f' : 𝕜} (ha : a in f.target)
 (hf' : f' != 0) (htff' : HasStri…
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Real.sinh_eq_zero`：∀ {x : ℝ}, Real.sinh x = 0 ↔ x = 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.arcosh_pos`：arcosh_pos {x : Real} (hx : 1 < x) : 0 < arcosh x
· 使用定理 `Real.hasStrictDerivAt_cosh`：hasStrictDerivAt_cosh (x : Real) : HasStrict
DerivAt cosh (sinh x) x
-/
theorem hasStrictDerivAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) :
    HasStrictDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x := by
  rw [← sinh_arcosh (le_of_lt hx)]
  refine coshOpenPartialHomeomorph.hasStrictDerivAt_symm hx ?_ (hasStrictDerivAt_cosh _)
  rw [ne_eq, sinh_eq_zero]
  exact ne_of_gt (arcosh_pos hx)
/-
**Real.hasDerivAt_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_arcosh {x : Real} (hx : x in Ioi 1) : HasDerivAt arcosh (√(x ^ 
2 - 1))⁻¹ x
参数：hx : x in Ioi 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Real.hasStrictDerivAt_arcosh`：hasStrictDerivAt_arcosh {x : Real} (hx : x
 in Ioi 1) : HasStrictDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x
-/
theorem hasDerivAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) : HasDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x :=
  (hasStrictDerivAt_arcosh hx).hasDerivAt
/-
**Real.differentiableAt_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_arcosh {x : Real} (hx : x in Ioi 1) : DifferentiableAt Re
al arcosh x
参数：hx : x in Ioi 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Real.hasDerivAt_arcosh`：hasDerivAt_arcosh {x : Real} (hx : x in Ioi 1) :
 HasDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x
-/
theorem differentiableAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) : DifferentiableAt ℝ arcosh x :=
  (hasDerivAt_arcosh hx).differentiableAt
/-
**Real.differentiableOn_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableOn_arcosh : DifferentiableOn Real arcosh (Ioi 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Real.differentiableAt_arcosh`：differentiableAt_arcosh {x : Real} (hx : x
 in Ioi 1) : DifferentiableAt Real arcosh x
-/
theorem differentiableOn_arcosh : DifferentiableOn ℝ arcosh (Ioi 1) := fun _ hx =>
  (differentiableAt_arcosh hx).differentiableWithinAt
/-
**Real.contDiffAt_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffAt_arcosh {n : WithTop Nat∞} {x : Real} (hx : x in Ioi 1) : ContDi
ffAt Real n arcosh x
参数：hx : x in Ioi 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.contDiffAt_symm_deriv`：OpenPartialHomeomorph.contD
iffAt_symm_deriv [CompleteSpace 𝕜] (f : OpenPartialHomeomorph 𝕜 𝕜) {f₀' a : 𝕜} (
h₀ : f₀' != 0) (ha : a in f.targe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Real.sinh_eq_zero`：∀ {x : ℝ}, Real.sinh x = 0 ↔ x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.arcosh_pos`：arcosh_pos {x : Real} (hx : 1 < x) : 0 < arcosh x
· 使用定理 `Real.hasDerivAt_cosh`：hasDerivAt_cosh (x : Real) : HasDerivAt cosh (sinh
 x) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `Real.contDiff_cosh`：contDiff_cosh {n} : ContDiff Real n cosh
-/
theorem contDiffAt_arcosh {n : WithTop ℕ∞} {x : ℝ} (hx : x ∈ Ioi 1) : ContDiffAt ℝ n arcosh x := by
  refine coshOpenPartialHomeomorph.contDiffAt_symm_deriv ?_ hx (hasDerivAt_cosh _)
    contDiff_cosh.contDiffAt
  rw [ne_eq, sinh_eq_zero]
  exact (arcosh_pos hx).ne'
/-
**Real.contDiffOn_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffOn_arcosh {n : WithTop Nat∞} : ContDiffOn Real n arcosh (Ioi 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Real.contDiffAt_arcosh`：contDiffAt_arcosh {n : WithTop Nat∞} {x : Real} 
(hx : x in Ioi 1) : ContDiffAt Real n arcosh x
-/
theorem contDiffOn_arcosh {n : WithTop ℕ∞} : ContDiffOn ℝ n arcosh (Ioi 1) := fun _ hx =>
  (contDiffAt_arcosh hx).contDiffWithinAt

/-- The function `Real.arcosh` is real analytic. -/
@[fun_prop]
/-
**Real.analyticAt_arcosh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticAt_arcosh {x : Real} (hx : x in Ioi 1) : AnalyticAt Real arcosh x
参数：hx : x in Ioi 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.analyticAt`：ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : 
AnalyticAt 𝕜 f x
· 使用定理 `Real.contDiffAt_arcosh`：contDiffAt_arcosh {n : WithTop Nat∞} {x : Real} 
(hx : x in Ioi 1) : ContDiffAt Real n arcosh x

--- 原说明 ---
The function `Real.arcosh` is real analytic.
-/
lemma analyticAt_arcosh {x : ℝ} (hx : x ∈ Ioi 1) : AnalyticAt ℝ arcosh x :=
  (contDiffAt_arcosh hx).analyticAt

/-- The function `Real.arcosh` is real analytic. -/
/-
**Real.analyticWithinAt_arcosh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticWithinAt_arcosh {s : Set Real} {x : Real} (hx : x in Ioi 1) : Anal
yticWithinAt Real arcosh s x
参数：hx : x in Ioi 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContDiffWithinAt.analyticWithinAt`：ContDiffWithinAt.analyticWithinAt (h 
: ContDiffWithinAt 𝕜 ω f s x) : AnalyticWithinAt 𝕜 f s x
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Real.contDiffAt_arcosh`：contDiffAt_arcosh {n : WithTop Nat∞} {x : Real} 
(hx : x in Ioi 1) : ContDiffAt Real n arcosh x

--- 原说明 ---
The function `Real.arcosh` is real analytic.
-/
lemma analyticWithinAt_arcosh {s : Set ℝ} {x : ℝ} (hx : x ∈ Ioi 1) :
    AnalyticWithinAt ℝ arcosh s x :=
  (contDiffAt_arcosh hx).contDiffWithinAt.analyticWithinAt

/-- The function `Real.arcosh` is real analytic. -/
/-
**Real.analyticOnNhd_arcosh** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：analyticOnNhd_arcosh {s : Set Real} (hs : s subseteq Ioi 1) : AnalyticOnNh
d Real arcosh s
参数：hs : s subseteq Ioi 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.analyticAt_arcosh`：analyticAt_arcosh {x : Real} (hx : x in Ioi 1) :
 AnalyticAt Real arcosh x

--- 原说明 ---
The function `Real.arcosh` is real analytic.
-/
theorem analyticOnNhd_arcosh {s : Set ℝ} (hs : s ⊆ Ioi 1) : AnalyticOnNhd ℝ arcosh s :=
  fun _ hx ↦ analyticAt_arcosh (hs hx)

/-- The function `Real.arcosh` is real analytic. -/
/-
**Real.analyticOn_arcosh** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：analyticOn_arcosh {s : Set Real} (hs : s subseteq Ioi 1) : AnalyticOn Real
 arcosh s
参数：hs : s subseteq Ioi 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOn.mono`：AnalyticOn.mono {f : E -> F} {s t : Set E} (h : Analyti
cOn 𝕜 f t) (hs : s subseteq t) : AnalyticOn 𝕜 f s
· 使用定理 `ContDiffOn.analyticOn`：ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : 
AnalyticOn 𝕜 f s
· 使用定理 `Real.contDiffOn_arcosh`：contDiffOn_arcosh {n : WithTop Nat∞} : ContDiffO
n Real n arcosh (Ioi 1)

--- 原说明 ---
The function `Real.arcosh` is real analytic.
-/
lemma analyticOn_arcosh {s : Set ℝ} (hs : s ⊆ Ioi 1) : AnalyticOn ℝ arcosh s :=
  contDiffOn_arcosh.analyticOn.mono hs
/-
**Real.cosh_bijOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cosh_bijOn : BijOn cosh (Ici 0) (Ici 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.bijOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.BijOn (↑e) e.source e.target
-/
theorem cosh_bijOn : BijOn cosh (Ici 0) (Ici 1) := coshPartialEquiv.bijOn
/-
**Real.cosh_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cosh_injOn : InjOn cosh (Ici 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.injOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.InjOn (↑e) e.source
-/
theorem cosh_injOn : InjOn cosh (Ici 0) := coshPartialEquiv.injOn
/-
**Real.cosh_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：cosh_surjOn : SurjOn cosh (Ici 0) (Ici 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.surjOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.SurjOn (↑e) e.source e.target
-/
theorem cosh_surjOn : SurjOn cosh (Ici 0) (Ici 1) := coshPartialEquiv.surjOn
/-
**Real.arcosh_bijOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcosh_bijOn : BijOn arcosh (Ici 1) (Ici 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.bijOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.BijOn (↑e) e.source e.target
-/
theorem arcosh_bijOn : BijOn arcosh (Ici 1) (Ici 0) := coshPartialEquiv.symm.bijOn
/-
**Real.arcosh_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcosh_injOn : InjOn arcosh (Ici 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.injOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.InjOn (↑e) e.source
-/
theorem arcosh_injOn : InjOn arcosh (Ici 1) := coshPartialEquiv.symm.injOn
/-
**Real.arcosh_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：arcosh_surjOn : SurjOn arcosh (Ici 1) (Ici 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.surjOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.SurjOn (↑e) e.source e.target
-/
theorem arcosh_surjOn : SurjOn arcosh (Ici 1) (Ici 0) := coshPartialEquiv.symm.surjOn

end Real

