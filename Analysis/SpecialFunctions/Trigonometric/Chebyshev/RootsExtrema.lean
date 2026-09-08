/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.Niven

/-!
# Chebyshev polynomials over the reals: roots and extrema

## Main statements

* `T_n(x) ∈ [-1, 1]` iff `x ∈ [-1, 1]`: `abs_eval_T_real_le_one_iff`
* Zeroes of `T` and `U`: `roots_T_real`, `roots_U_real`
* Local extrema of `T`: `isLocalExtr_T_real_iff`, `isExtrOn_T_real_iff`
* Irrationality of zeroes of `T` other than zero: `irrational_of_isRoot_T_real`
* `|T_n^{(k)} (x)| ≤ T_n^{(k)} (1)` for `x ∈ [-1, 1]`: `abs_iterate_derivative_T_real_le`

## TODO

Show that the bound on `T_n^{(k)} (x)` is achieved only at `x = ±1`
-/

public section

namespace Polynomial.Chebyshev

open Real

/-
**Polynomial.Chebyshev.eval_T_real_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Chebyshev`。
形式化陈述：eval_T_real_mem_Icc (n : Int) {x : Real} (hx : x in Set.Icc (-1) 1) : (T R
eal n).eval x in Set.Icc (-1) 1
参数：n : Int；hx : x in Set.Icc (-1) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.cos_arccos`：cos_arccos {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : 
cos (arccos x) = x
-/
theorem eval_T_real_mem_Icc (n : ℤ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    (T ℝ n).eval x ∈ Set.Icc (-1) 1 := by
  rw [← cos_arccos (x := x) (by grind) (by grind)]
  grind [T_real_cos, cos_mem_Icc]
/-
**Polynomial.Chebyshev.abs_eval_T_real_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Chebyshev`。
形式化陈述：abs_eval_T_real_le_one (n : Int) {x : Real} (hx : |x| <= 1) : |(T Real n).
eval x| <= 1
参数：n : Int；hx : |x| <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Chebyshev.eval_T_real_mem_Icc`：eval_T_real_mem_Icc (n : Int) 
{x : Real} (hx : x in Set.Icc (-1) 1) : (T Real n).eval x in Set.Icc (-1) 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
-/
theorem abs_eval_T_real_le_one (n : ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(T ℝ n).eval x| ≤ 1 := by
  #adaptation_note /-- Before nightly-2026-04-07, this was just
  `grind [eval_T_real_mem_Icc]`. `grind`'s e-matching now keeps the
  `Polynomial.eval` produced by the lemma (which uses `instCommSemiring.toSemiring`)
  and the `Polynomial.eval` propagated by abs unfolding (which uses `Real.semiring`)
  as distinct atoms, even though they are `rfl`-equal, so the contradiction is
  never found. -/
  have h := eval_T_real_mem_Icc n (Set.mem_Icc.mpr (abs_le.mp hx))
  exact abs_le.mpr (Set.mem_Icc.mp h)
/-
**Polynomial.Chebyshev.one_le_eval_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
Chebyshev`。
形式化陈述：one_le_eval_T_real (n : Int) {x : Real} (hx : 1 <= x) : 1 <= (T Real n).ev
al x
参数：n : Int；hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.cosh_arcosh`：cosh_arcosh {x : Real} (hx : 1 <= x) : cosh (arcosh x)
 = x
-/
theorem one_le_eval_T_real (n : ℤ) {x : ℝ} (hx : 1 ≤ x) : 1 ≤ (T ℝ n).eval x := by
  rw [← cosh_arcosh hx]
  grind [T_real_cosh, one_le_cosh]
/-
**Polynomial.Chebyshev.one_lt_eval_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
Chebyshev`。
形式化陈述：one_lt_eval_T_real {n : Int} (hn : n != 0) {x : Real} (hx : 1 < x) : 1 < (
T Real n).eval x
参数：hn : n != 0；hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.cosh_arcosh`：cosh_arcosh {x : Real} (hx : 1 <= x) : cosh (arcosh x)
 = x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Polynomial.Chebyshev.T_real_cosh`：T_real_cosh (n : Int) : (T Real n).eva
l (cosh θ) = cosh (n * θ)
· 使用定理 `Real.one_lt_cosh`：one_lt_cosh : 1 < cosh x ↔ x != 0
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem one_lt_eval_T_real {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : 1 < x) :
    1 < (T ℝ n).eval x := by
  have : arcosh x ≠ 0 := by grind [cosh_arcosh, cosh_zero]
  rw [← cosh_arcosh (le_of_lt hx), T_real_cosh, one_lt_cosh, mul_ne_zero_iff]
  exact ⟨by norm_cast, by assumption⟩
/-
**Polynomial.Chebyshev.one_le_negOnePow_mul_eval_T_real** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial.Chebyshev`。
形式化陈述：one_le_negOnePow_mul_eval_T_real (n : Int) {x : Real} (hx : x <= -1) : 1 <
= n.negOnePow * (T Real n).eval x
参数：n : Int；hx : x <= -1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Polynomial.Chebyshev.T_eval_neg`：T_eval_neg (n : Int) (x : R) : (T R n).
eval (-x) = n.negOnePow * (T R n).eval x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Int.cast_negOnePow`：cast_negOnePow (K : Type*) (n : Int) [DivisionRing K
] : n.negOnePow = (-1 : K) ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_zpow`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α) (n : 
ℤ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Chebyshev.one_le_eval_T_real`：one_le_eval_T_real (n : Int) {x
 : Real} (hx : 1 <= x) : 1 <= (T Real n).eval x
· 使用定理 `le_neg_of_le_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dLeftMono α] [AddRightMono α] {a b : α}, a ≤ -b → b ≤ -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem one_le_negOnePow_mul_eval_T_real (n : ℤ) {x : ℝ} (hx : x ≤ -1) :
    1 ≤ n.negOnePow * (T ℝ n).eval x := by
  rw [← neg_neg x, T_eval_neg]
  convert! one_le_eval_T_real n (le_neg_of_le_neg hx)
  rw [Int.cast_negOnePow, ← mul_assoc, ← mul_zpow]
  simp
/-
**Polynomial.Chebyshev.one_lt_negOnePow_mul_eval_T_real** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial.Chebyshev`。
形式化陈述：one_lt_negOnePow_mul_eval_T_real {n : Int} (hn : n != 0) {x : Real} (hx : 
x < -1) : 1 < n.negOnePow * (T Real n).eval x
参数：hn : n != 0；hx : x < -1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Polynomial.Chebyshev.T_eval_neg`：T_eval_neg (n : Int) (x : R) : (T R n).
eval (-x) = n.negOnePow * (T R n).eval x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Int.cast_negOnePow`：cast_negOnePow (K : Type*) (n : Int) [DivisionRing K
] : n.negOnePow = (-1 : K) ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_zpow`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α) (n : 
ℤ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Chebyshev.one_lt_eval_T_real`：one_lt_eval_T_real {n : Int} (h
n : n != 0) {x : Real} (hx : 1 < x) : 1 < (T Real n).eval x
· 使用定理 `lt_neg_of_lt_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Ad
dLeftStrictMono α] {a b : α} [AddRightStrictMono α],   a < -b → b < -a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
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
-/
theorem one_lt_negOnePow_mul_eval_T_real {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : x < -1) :
    1 < n.negOnePow * (T ℝ n).eval x := by
  rw [← neg_neg x, T_eval_neg]
  convert! one_lt_eval_T_real hn (lt_neg_of_lt_neg hx)
  rw [Int.cast_negOnePow, ← mul_assoc, ← mul_zpow]
  simp
/-
**Polynomial.Chebyshev.one_le_abs_eval_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Chebyshev`。
形式化陈述：one_le_abs_eval_T_real (n : Int) {x : Real} (hx : 1 <= |x|) : 1 <= |(T Rea
l n).eval x|
参数：n : Int；hx : 1 <= |x|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.Chebyshev.one_le_eval_T_real`：one_le_eval_T_real (n : Int) {x
 : Real} (hx : 1 <= x) : 1 <= (T Real n).eval x
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.Chebyshev.T_eval_neg`：T_eval_neg (n : Int) (x : R) : (T R n).
eval (-x) = n.negOnePow * (T R n).eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_le_abs_eval_T_real (n : ℤ) {x : ℝ} (hx : 1 ≤ |x|) :
    1 ≤ |(T ℝ n).eval x| := by
  wlog! h : 0 ≤ x
  · simpa [T_eval_neg, abs_mul, abs_unit_intCast] using @this n (-x) (by grind) (by grind)
  · exact one_le_eval_T_real n (abs_of_nonneg h ▸ hx) |>.trans <| le_abs_self _
/-
**Polynomial.Chebyshev.one_lt_abs_eval_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Chebyshev`。
形式化陈述：one_lt_abs_eval_T_real {n : Int} (hn : n != 0) {x : Real} (hx : 1 < |x|) :
 1 < |(T Real n).eval x|
参数：hn : n != 0；hx : 1 < |x|。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Polynomial.Chebyshev.one_lt_eval_T_real`：one_lt_eval_T_real {n : Int} (h
n : n != 0) {x : Real} (hx : 1 < x) : 1 < (T Real n).eval x
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.Chebyshev.T_eval_neg`：T_eval_neg (n : Int) (x : R) : (T R n).
eval (-x) = n.negOnePow * (T R n).eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.coe_negOnePow`：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.neg
OnePow : R) = (-1 : R) ^ n.natAbs
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_lt_abs_eval_T_real {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : 1 < |x|) :
    1 < |(T ℝ n).eval x| := by
  wlog! h : 0 ≤ x
  · simpa [T_eval_neg, abs_mul, abs_unit_intCast] using @this n hn (-x) (by grind) (by grind)
  · exact one_lt_eval_T_real hn (abs_of_nonneg h ▸ hx) |>.trans_le <| le_abs_self _
/-
**Polynomial.Chebyshev.abs_eval_T_real_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial.Chebyshev`。
形式化陈述：abs_eval_T_real_le_one_iff {n : Int} (hn : n != 0) (x : Real) : |x| <= 1 ↔
 |(T Real n).eval x| <= 1
参数：hn : n != 0；x : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Chebyshev.abs_eval_T_real_le_one`：abs_eval_T_real_le_one (n :
 Int) {x : Real} (hx : |x| <= 1) : |(T Real n).eval x| <= 1
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Polynomial.Chebyshev.one_lt_abs_eval_T_real`：one_lt_abs_eval_T_real {n :
 Int} (hn : n != 0) {x : Real} (hx : 1 < |x|) : 1 < |(T Real n).eval x|
-/
theorem abs_eval_T_real_le_one_iff {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
    |x| ≤ 1 ↔ |(T ℝ n).eval x| ≤ 1 :=
  ⟨abs_eval_T_real_le_one n, by simpa using mt <| one_lt_abs_eval_T_real hn⟩
/-
**Polynomial.Chebyshev.abs_eval_T_real_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial.Chebyshev`。
形式化陈述：abs_eval_T_real_eq_one_iff {n : Nat} (hn : n != 0) (x : Real) : |(T Real n
).eval x| = 1 ↔ exists k <= n, x = cos (k * π / n)
参数：hn : n != 0；x : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.Chebyshev.abs_eval_T_real_le_one_iff`：abs_eval_T_real_le_one_
iff {n : Int} (hn : n != 0) (x : Real) : |x| <= 1 ↔ |(T Real n).eval x| <= 1
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.abs_cos_eq_one_iff`：abs_cos_eq_one_iff {x : Real} : |cos x| = 1 ↔ e
xists k : Int, k * π = x
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Polynomial.Chebyshev.T_real_cos`：T_real_cos : (T Real n).eval (cos θ) = 
cos (n * θ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.cos_arccos`：cos_arccos {x : Real} (hx₁ : -1 <= x) (hx₂ : x <= 1) : 
cos (arccos x) = x
· 使用定理 `neg_le_of_abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Lin
earOrder G] [IsOrderedAddMonoid G] {a b : G}, |a| ≤ b → -b ≤ a
· 使用定理 `le_of_max_le_left`：le_of_max_le_left {a b c : α} (h : max a b <= c) : a 
<= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
（共 72 条，此处仅展示前 30 条）
-/
theorem abs_eval_T_real_eq_one_iff {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    |(T ℝ n).eval x| = 1 ↔ ∃ k ≤ n, x = cos (k * π / n) := by
  constructor
  · intro hTx
    have hx := (abs_eval_T_real_le_one_iff (Nat.cast_ne_zero.mpr hn) x).mpr (le_of_eq hTx)
    rw [← cos_arccos (neg_le_of_abs_le hx) (le_of_max_le_left hx), T_real_cos,
      Int.cast_natCast, abs_cos_eq_one_iff] at hTx
    obtain ⟨k, hk⟩ := hTx
    have hk' : k = n * (arccos x / π) := by simpa [field]
    lift k to ℕ using (by rw [← Int.cast_nonneg_iff (R := ℝ), hk']; positivity [arccos_nonneg x])
    simp only [Int.cast_natCast] at hk hk'
    have hkn : (k : ℝ) ≤ n := by
      rw [← mul_one (n : ℝ), hk']
      gcongr
      exact div_le_one_of_le₀ (arccos_le_pi x) (by positivity)
    refine ⟨k, by simpa using hkn, ?_⟩
    convert! congr(cos ($hk.symm / n))
    rw [mul_div_cancel_left₀ _ (by simpa), cos_arccos (by grind) (by grind)]
  · rintro ⟨k, hk, rfl⟩
    rw [T_real_cos, abs_cos_eq_one_iff]
    exact ⟨k, by simp [field]⟩
/-
**Polynomial.Chebyshev.eval_T_real_cos_int_mul_pi_div** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial.Chebyshev`。
形式化陈述：eval_T_real_cos_int_mul_pi_div {k : Nat} {n : Nat} (hn : n != 0) : (T Real
 n).eval (cos (k * π / n)) = (k : Int).negOnePow
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.T_real_cos`：T_real_cos : (T Real n).eval (cos θ) = 
cos (n * θ)
· 使用引理 `Int.cast_negOnePow`：cast_negOnePow (K : Type*) (n : Int) [DivisionRing K
] : n.negOnePow = (-1 : K) ^ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons_zero`：eval_mul_eval_cons_
zero [CommGroupWithZero M] {e : M} {L l l' l₀ : NF M} (h : L.eval * l.eval = l'.
eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 48 条，此处仅展示前 30 条）
-/
theorem eval_T_real_cos_int_mul_pi_div {k : ℕ} {n : ℕ} (hn : n ≠ 0) :
    (T ℝ n).eval (cos (k * π / n)) = (k : ℤ).negOnePow := by
  rw [T_real_cos, Int.cast_negOnePow]
  convert! Real.cos_int_mul_pi k using 2
  simp [field]
/-
**Polynomial.Chebyshev.eval_T_real_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Chebyshev`。
形式化陈述：eval_T_real_eq_one_iff {n : Nat} (hn : n != 0) (x : Real) : (T Real n).eva
l x = 1 ↔ exists k <= n, Even k ∧ x = cos (k * π / n)
参数：hn : n != 0；x : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Chebyshev.abs_eval_T_real_eq_one_iff`：abs_eval_T_real_eq_one_
iff {n : Nat} (hn : n != 0) (x : Real) : |(T Real n).eval x| = 1 ↔ exists k <= n
, x = cos (k * π / n)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] {a b : α}, |a| = |b| ↔ a = b ∨ a = -b
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用引理 `neg_one_pow_eq_one_iff_even`：neg_one_pow_eq_one_iff_even (h : (-1 : R) !
= 1) : (-1 : R) ^ n = 1 ↔ Even n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_negOnePow_natCast`：cast_negOnePow_natCast (R : Type*) [Ring R] 
(n : Nat) : negOnePow n = (-1 : R) ^ n
· 使用定理 `Polynomial.Chebyshev.eval_T_real_cos_int_mul_pi_div`：eval_T_real_cos_int
_mul_pi_div {k : Nat} {n : Nat} (hn : n != 0) : (T Real n).eval (cos (k * π / n)
) = (k : Int).negOnePow
· 使用引理 `Int.negOnePow_even`：negOnePow_even (n : Int) (hn : Even n) : n.negOnePow
 = 1
· 使用引理 `Int.even_coe_nat`：even_coe_nat (n : Nat) : Even (n : Int) ↔ Even n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem eval_T_real_eq_one_iff {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    (T ℝ n).eval x = 1 ↔ ∃ k ≤ n, Even k ∧ x = cos (k * π / n) := by
  constructor
  · intro hx
    obtain ⟨k, hk₁, hk₂⟩ := (abs_eval_T_real_eq_one_iff hn x).mp
      ((abs_eq_abs.mpr (.inl hx)).trans abs_one)
    use k
    refine ⟨hk₁, ?_, hk₂⟩
    rw [hk₂, eval_T_real_cos_int_mul_pi_div hn, Int.cast_negOnePow_natCast] at hx
    exact (neg_one_pow_eq_one_iff_even (by grind)).mp hx
  · rintro ⟨k, hk₁, hk₂, hx⟩
    rw [hx, eval_T_real_cos_int_mul_pi_div hn, Int.negOnePow_even k ((Int.even_coe_nat k).mpr hk₂)]
    norm_cast
/-
**Polynomial.Chebyshev.eval_T_real_eq_neg_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial.Chebyshev`。
形式化陈述：eval_T_real_eq_neg_one_iff {n : Nat} (hn : n != 0) (x : Real) : (T Real n)
.eval x = -1 ↔ exists k <= n, Odd k ∧ x = cos (k * π / n)
参数：hn : n != 0；x : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Chebyshev.abs_eval_T_real_eq_one_iff`：abs_eval_T_real_eq_one_
iff {n : Nat} (hn : n != 0) (x : Real) : |(T Real n).eval x| = 1 ↔ exists k <= n
, x = cos (k * π / n)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] {a b : α}, |a| = |b| ↔ a = b ∨ a = -b
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用引理 `neg_one_pow_eq_neg_one_iff_odd`：neg_one_pow_eq_neg_one_iff_odd (h : (-1 
: R) != 1) : (-1 : R) ^ n = -1 ↔ Odd n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_negOnePow_natCast`：cast_negOnePow_natCast (R : Type*) [Ring R] 
(n : Nat) : negOnePow n = (-1 : R) ^ n
· 使用定理 `Polynomial.Chebyshev.eval_T_real_cos_int_mul_pi_div`：eval_T_real_cos_int
_mul_pi_div {k : Nat} {n : Nat} (hn : n != 0) : (T Real n).eval (cos (k * π / n)
) = (k : Int).negOnePow
· 使用引理 `Int.negOnePow_odd`：negOnePow_odd (n : Int) (hn : Odd n) : n.negOnePow = 
-1
· 使用定理 `Int.odd_coe_nat`：∀ (n : ℕ), Odd ↑n ↔ Odd n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem eval_T_real_eq_neg_one_iff {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    (T ℝ n).eval x = -1 ↔ ∃ k ≤ n, Odd k ∧ x = cos (k * π / n) := by
  constructor
  · intro hx
    obtain ⟨k, hk₁, hk₂⟩ := (abs_eval_T_real_eq_one_iff hn x).mp
      ((abs_eq_abs.mpr (.inl hx)).trans ((abs_neg 1).trans abs_one))
    use k
    refine ⟨hk₁, ?_, hk₂⟩
    rw [hk₂, eval_T_real_cos_int_mul_pi_div hn, Int.cast_negOnePow_natCast] at hx
    exact (neg_one_pow_eq_neg_one_iff_odd (by grind)).mp hx
  · rintro ⟨k, hk₁, hk₂, hx⟩
    rw [hx, eval_T_real_cos_int_mul_pi_div hn, Int.negOnePow_odd k ((Int.odd_coe_nat k).mpr hk₂)]
    norm_cast
/-
**Polynomial.Chebyshev.roots_T_real_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
Chebyshev`。
形式化陈述：roots_T_real_nodup (n : Nat) : (Multiset.map (fun k : Nat => cos ((2 * k +
 1) * π / (2 * n))) (.range n)).Nodup
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.nodup_map_iff_injOn`：nodup_map_iff_injOn {f : α -> β} {s : Finset
 α} : (Multiset.map f s.val).Nodup ↔ Set.InjOn f s
· 使用定理 `Set.InjOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set 
α} {t : Set β} {f : α → β} {g : β → γ},   Set.InjOn g t → Set.InjOn f s → Set.Ma
psTo…
· 使用定理 `Real.injOn_cos`：injOn_cos : InjOn cos (Icc 0 π)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
（共 85 条，此处仅展示前 30 条）
-/
theorem roots_T_real_nodup (n : ℕ) :
    (Multiset.map (fun k : ℕ ↦ cos ((2 * k + 1) * π / (2 * n))) (.range n)).Nodup := by
  wlog! hn : n ≠ 0
  · simp [hn]
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  refine injOn_cos.comp (by aesop) fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
  field_simp
  norm_cast
  grind
/-
**Polynomial.Chebyshev.roots_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Chebys
hev`。
形式化陈述：roots_T_real (n : Nat) : (T Real n).roots = ((Finset.range n).image (fun (
k : Nat) => cos ((2 * k + 1) * π / (2 * n)))).val
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Polynomial.roots_eq_of_degree_eq_card`：roots_eq_of_degree_eq_card {S : F
inset R} (hS : forall x in S, p.eval x = 0) (hcard : S.card = p.degree) : p.root
s = S.val
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Chebyshev.T_real_cos`：T_real_cos : (T Real n).eval (cos θ) = 
cos (n * θ)
· 使用定理 `Real.cos_eq_zero_iff`：cos_eq_zero_iff {θ : Real} : cos θ = 0 ↔ exists k 
: Int, θ = (2 * k + 1) * π / 2
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
（共 79 条，此处仅展示前 30 条）
-/
theorem roots_T_real (n : ℕ) :
    (T ℝ n).roots =
    ((Finset.range n).image (fun (k : ℕ) => cos ((2 * k + 1) * π / (2 * n)))).val := by
  wlog! hn : n ≠ 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx ↦ ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    rw [← hx, T_real_cos, cos_eq_zero_iff]
    use k
    field_simp
    norm_cast
  · rw [Finset.card_image_of_injOn, Finset.card_range, degree_T, Int.natAbs_natCast]
    exact (Finset.range n).nodup_map_iff_injOn.mp (roots_T_real_nodup n)
/-
**Polynomial.Chebyshev.rootMultiplicity_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial.Chebyshev`。
形式化陈述：rootMultiplicity_T_real {n k : Nat} (hk : k < n) : (T Real n).rootMultipli
city (cos ((2 * k + 1) * π / (2 * n))) = 1
参数：hk : k < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Polynomial.Chebyshev.roots_T_real`：roots_T_real (n : Nat) : (T Real n).r
oots = ((Finset.range n).image (fun (k : Nat) => cos ((2 * k + 1) * π / (2 * n))
)).val
· 使用定理 `Multiset.count_eq_one_of_mem`：count_eq_one_of_mem [DecidableEq α] {a : α
} {s : Multiset α} (d : Nodup s) (h : a in s) : count a s = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem rootMultiplicity_T_real {n k : ℕ} (hk : k < n) :
    (T ℝ n).rootMultiplicity (cos ((2 * k + 1) * π / (2 * n))) = 1 := by
  rw [← count_roots, roots_T_real, Multiset.count_eq_one_of_mem (by simp)]
  grind
/-
**Polynomial.Chebyshev.roots_U_real_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
Chebyshev`。
形式化陈述：roots_U_real_nodup (n : Nat) : (Multiset.map (fun k : Nat => cos ((k + 1) 
* π / (n + 1))) (.range n)).Nodup
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.nodup_map_iff_injOn`：nodup_map_iff_injOn {f : α -> β} {s : Finset
 α} : (Multiset.map f s.val).Nodup ↔ Set.InjOn f s
· 使用定理 `Set.InjOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set 
α} {t : Set β} {f : α → β} {g : β → γ},   Set.InjOn g t → Set.InjOn f s → Set.Ma
psTo…
· 使用定理 `Real.injOn_cos`：injOn_cos : InjOn cos (Icc 0 π)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
（共 64 条，此处仅展示前 30 条）
-/
theorem roots_U_real_nodup (n : ℕ) :
    (Multiset.map (fun k : ℕ ↦ cos ((k + 1) * π / (n + 1))) (.range n)).Nodup := by
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  apply injOn_cos.comp
  · intro x hx y hy hxy
    field_simp at hxy
    aesop
  · refine fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
    field_simp
    norm_cast
    grind
/-
**Polynomial.Chebyshev.roots_U_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Chebys
hev`。
形式化陈述：roots_U_real (n : Nat) : (U Real n).roots = ((Finset.range n).image (fun (
k : Nat) => cos ((k + 1) * π / (n + 1)))).val
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Polynomial.roots_eq_of_degree_eq_card`：roots_eq_of_degree_eq_card {S : F
inset R} (hS : forall x in S, p.eval x = 0) (hcard : S.card = p.degree) : p.root
s = S.val
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Chebyshev.U_real_cos`：U_real_cos : (U Real n).eval (cos θ) * 
sin θ = sin ((n + 1) * θ)
· 使用定理 `Real.sin_eq_zero_iff`：sin_eq_zero_iff {x : Real} : sin x = 0 ↔ exists n 
: Int, (n : Real) * π = x
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
（共 102 条，此处仅展示前 30 条）
-/
theorem roots_U_real (n : ℕ) :
    (U ℝ n).roots =
    ((Finset.range n).image (fun (k : ℕ) => cos ((k + 1) * π / (n + 1)))).val := by
  wlog! hn : n ≠ 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx ↦ ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    suffices (U ℝ n).eval x * sin ((k + 1) * π / (n + 1)) = 0 by
      refine (mul_eq_zero_iff_right (ne_of_gt (sin_pos_of_pos_of_lt_pi (by positivity) ?_))).mp this
      field_simp
      norm_cast
      grind
    rw [← hx, U_real_cos, sin_eq_zero_iff]
    use k + 1
    field_simp
    norm_cast
    ring
  · rw [Finset.card_image_of_injOn, Finset.card_range, degree_U_natCast]
    exact (Finset.range n).nodup_map_iff_injOn.mp (roots_U_real_nodup n)
/-
**Polynomial.Chebyshev.rootMultiplicity_U_real** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial.Chebyshev`。
形式化陈述：rootMultiplicity_U_real {n k : Nat} (hk : k < n) : (U Real n).rootMultipli
city (cos ((k + 1) * π / (n + 1))) = 1
参数：hk : k < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.count_roots`：count_roots [DecidableEq R] (p : R[X]) : p.roots
.count a = rootMultiplicity a p
· 使用定理 `Polynomial.Chebyshev.roots_U_real`：roots_U_real (n : Nat) : (U Real n).r
oots = ((Finset.range n).image (fun (k : Nat) => cos ((k + 1) * π / (n + 1)))).v
al
· 使用定理 `Multiset.count_eq_one_of_mem`：count_eq_one_of_mem [DecidableEq α] {a : α
} {s : Multiset α} (d : Nodup s) (h : a in s) : count a s = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem rootMultiplicity_U_real {n k : ℕ} (hk : k < n) :
    (U ℝ n).rootMultiplicity (cos ((k + 1) * π / (n + 1))) = 1 := by
  rw [← count_roots, roots_U_real, Multiset.count_eq_one_of_mem (by simp)]
  grind
/-
**Polynomial.Chebyshev.isLocalMax_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.C
hebyshev`。
形式化陈述：isLocalMax_T_real {n k : Nat} (hn : n != 0) (hk₀ : 0 < k) (hk₁ : k < n) (h
k₂ : Even k) : IsLocalMax (T Real n).eval (cos (k * π / n))
参数：hn : n != 0；hk₀ : 0 < k；hk₁ : k < n；hk₂ : Even k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `div_lt_div_of_pos_right`：div_lt_div_of_pos_right (h : a < b) (hc : 0 < c
) : a / c < b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `Nat.strictMono_cast`：strictMono_cast : StrictMono (Nat.cast : Nat -> α)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.eval_T_real_eq_one_iff`：eval_T_real_eq_one_iff {n :
 Nat} (hn : n != 0) (x : Real) : (T Real n).eval x = 1 ↔ exists k <= n, Even k ∧
 x = cos (k * π / n)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Polynomial.Chebyshev.abs_eval_T_real_le_one`：abs_eval_T_real_le_one (n :
 Int) {x : Real} (hx : |x| <= 1) : |(T Real n).eval x| <= 1
（共 38 条，此处仅展示前 30 条）
-/
theorem isLocalMax_T_real {n k : ℕ} (hn : n ≠ 0) (hk₀ : 0 < k) (hk₁ : k < n) (hk₂ : Even k) :
    IsLocalMax (T ℝ n).eval (cos (k * π / n)) := by
  have zero_lt : 0 < k * π / n := by positivity
  have lt_pi : k * π / n < π := calc
    k * π / n < n * π / n := by gcongr
    _ = π := mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)
  refine eventually_nhds_iff.mpr ⟨Set.Ioo (-1) 1, ?_, isOpen_Ioo, ?_, ?_⟩
  · intro x hx
    dsimp
    rw [(eval_T_real_eq_one_iff hn _).mpr ⟨k, le_of_lt hk₁, hk₂, rfl⟩]
    exact (abs_le.mp (abs_eval_T_real_le_one n (by grind))).2
  · rw [← cos_pi]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_of_lt zero_lt) (le_refl π) lt_pi
  · rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (le_of_lt lt_pi) zero_lt
/-
**Polynomial.Chebyshev.isLocalMin_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.C
hebyshev`。
形式化陈述：isLocalMin_T_real {n k : Nat} (hn : n != 0) (hk₁ : k < n) (hk₂ : Odd k) : 
IsLocalMin (T Real n).eval (cos (k * π / n))
参数：hn : n != 0；hk₁ : k < n；hk₂ : Odd k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Odd.pos`：Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
 [Nontrivial R] {a : R} : Odd a -> 0 < a
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `div_lt_div_of_pos_right`：div_lt_div_of_pos_right (h : a < b) (hc : 0 < c
) : a / c < b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `Nat.strictMono_cast`：strictMono_cast : StrictMono (Nat.cast : Nat -> α)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.eval_T_real_eq_neg_one_iff`：eval_T_real_eq_neg_one_
iff {n : Nat} (hn : n != 0) (x : Real) : (T Real n).eval x = -1 ↔ exists k <= n,
 Odd k ∧ x = cos (k * π / n)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
（共 39 条，此处仅展示前 30 条）
-/
theorem isLocalMin_T_real {n k : ℕ} (hn : n ≠ 0) (hk₁ : k < n) (hk₂ : Odd k) :
    IsLocalMin (T ℝ n).eval (cos (k * π / n)) := by
  have k_pos : 0 < k := hk₂.pos
  have zero_lt : 0 < k * π / n := by positivity
  have lt_pi : k * π / n < π := calc
    k * π / n < n * π / n := by gcongr
    _ = π := mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)
  refine eventually_nhds_iff.mpr ⟨Set.Ioo (-1) 1, ?_, isOpen_Ioo, ?_, ?_⟩
  · intro x hx
    dsimp
    rw [(eval_T_real_eq_neg_one_iff hn _).mpr ⟨k, le_of_lt hk₁, hk₂, rfl⟩]
    refine (abs_le.mp (abs_eval_T_real_le_one n (by grind))).1
  · rw [← cos_pi]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_of_lt zero_lt) (le_refl π) lt_pi
  · rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (le_of_lt lt_pi) zero_lt
/-
**Polynomial.Chebyshev.isLocalExtr_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
Chebyshev`。
形式化陈述：isLocalExtr_T_real {n k : Nat} (hn : n != 0) (hk₀ : 0 < k) (hk₁ : k < n) :
 IsLocalExtr (T Real n).eval (cos (k * π / n))
参数：hn : n != 0；hk₀ : 0 < k；hk₁ : k < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `Polynomial.Chebyshev.isLocalMax_T_real`：isLocalMax_T_real {n k : Nat} (h
n : n != 0) (hk₀ : 0 < k) (hk₁ : k < n) (hk₂ : Even k) : IsLocalMax (T Real n).e
val (cos (k * π / n))
· 使用定理 `Polynomial.Chebyshev.isLocalMin_T_real`：isLocalMin_T_real {n k : Nat} (h
n : n != 0) (hk₁ : k < n) (hk₂ : Odd k) : IsLocalMin (T Real n).eval (cos (k * π
 / n))
-/
theorem isLocalExtr_T_real {n k : ℕ} (hn : n ≠ 0) (hk₀ : 0 < k) (hk₁ : k < n) :
    IsLocalExtr (T ℝ n).eval (cos (k * π / n)) := by
  cases k.even_or_odd
  case inl hk₂ => exact .inr (isLocalMax_T_real hn hk₀ hk₁ hk₂)
  case inr hk₂ => exact .inl (isLocalMin_T_real hn hk₁ hk₂)
/-
**Polynomial.Chebyshev.isLocalExtr_T_real_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Chebyshev`。
形式化陈述：isLocalExtr_T_real_iff {n : Nat} (hn : 2 <= n) (x : Real) : IsLocalExtr (T
 Real n).eval x ↔ exists k in Finset.Ioo 0 n, x = cos (k * π / n)
参数：hn : 2 <= n；x : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtr.deriv_eq_zero`：IsLocalExtr.deriv_eq_zero (h : IsLocalExtr f 
a) : deriv f a = 0
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_ne_bot`：degree_ne_bot : degree p != ⊥ ↔ p != 0
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `WithBot.natCast_ne_bot`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : 
ℕ), ↑n ≠ ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_zero_iff_left`：mul_eq_zero_iff_left (ha : a != 0) : a * b = 0 ↔ b
 = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.Chebyshev.T_derivative_eq_U`：T_derivative_eq_U (n : Int) : de
rivative (T R n) = n * U R (n - 1)
· 使用定理 `Polynomial.deriv`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {x :
 𝕜} (p : Polynomial 𝕜),   deriv (fun x => Polynomial.eval x p) x = Polynomial.ev
al x (…
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_val`：mem_val {a : α} {s : Finset α} : (a in s.1) = (a in s)
· 使用定理 `Polynomial.Chebyshev.roots_U_real`：roots_U_real (n : Nat) : (U Real n).r
oots = ((Finset.range n).image (fun (k : Nat) => cos ((k + 1) * π / (n + 1)))).v
al
· 使用定理 `Finset.mem_Ioo`：mem_Ioo : x in Ioo a b ↔ a < x ∧ x < b
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 36 条，此处仅展示前 30 条）
-/
theorem isLocalExtr_T_real_iff {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    IsLocalExtr (T ℝ n).eval x ↔ ∃ k ∈ Finset.Ioo 0 n, x = cos (k * π / n) := by
  constructor
  · intro hx
    replace hx := hx.deriv_eq_zero
    rw [Polynomial.deriv, T_derivative_eq_U, eval_mul, Int.cast_natCast, eval_natCast,
      mul_eq_zero_iff_left (by aesop)] at hx
    replace hx : x ∈ (U ℝ (n - 1)).roots :=
      (mem_roots (degree_ne_bot.mp (ne_of_eq_of_ne (by grind [degree_U_natCast])
        (WithBot.natCast_ne_bot (n - 1))))).mpr hx
    rw [show (n - 1 : ℤ) = (n - 1 : ℕ) by grind, roots_U_real, Finset.mem_val] at hx
    obtain ⟨k, hk₁, hx⟩ := Finset.mem_image.mp hx
    refine ⟨k + 1, Finset.mem_Ioo.mpr ⟨k.zero_lt_succ, by grind⟩, ?_⟩
    rw [← hx]
    congr <;> norm_cast
    exact Nat.sub_add_cancel (Nat.one_le_of_lt hn)
  · rintro ⟨k, hk, hx⟩
    rw [hx]
    exact isLocalExtr_T_real (Nat.ne_zero_of_lt hn)
      (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2
/-
**Polynomial.Chebyshev.isMaxOn_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Cheb
yshev`。
形式化陈述：isMaxOn_T_real {n k : Nat} (hn : n != 0) (hk₁ : k <= n) (hk₂ : Even k) : I
sMaxOn (T Real n).eval (Set.Icc (-1) 1) (cos (k * π / n))
参数：hn : n != 0；hk₁ : k <= n；hk₂ : Even k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isMaxOn_iff`：isMaxOn_iff : IsMaxOn f s a ↔ forall x in s, f x <= f a
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Polynomial.Chebyshev.abs_eval_T_real_le_one`：abs_eval_T_real_le_one (n :
 Int) {x : Real} (hx : |x| <= 1) : |(T Real n).eval x| <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Chebyshev.eval_T_real_eq_one_iff`：eval_T_real_eq_one_iff {n :
 Nat} (hn : n != 0) (x : Real) : (T Real n).eval x = 1 ↔ exists k <= n, Even k ∧
 x = cos (k * π / n)
-/
theorem isMaxOn_T_real {n k : ℕ} (hn : n ≠ 0) (hk₁ : k ≤ n) (hk₂ : Even k) :
    IsMaxOn (T ℝ n).eval (Set.Icc (-1) 1) (cos (k * π / n)) :=
  isMaxOn_iff.mpr (fun x hx => le_of_le_of_eq (abs_le.mp (abs_eval_T_real_le_one n (by grind))).2
    ((eval_T_real_eq_one_iff hn _).mpr ⟨k, hk₁, hk₂, rfl⟩).symm)
/-
**Polynomial.Chebyshev.isMinOn_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Cheb
yshev`。
形式化陈述：isMinOn_T_real {n k : Nat} (hn : n != 0) (hk₁ : k <= n) (hk₂ : Odd k) : Is
MinOn (T Real n).eval (Set.Icc (-1) 1) (cos (k * π / n))
参数：hn : n != 0；hk₁ : k <= n；hk₂ : Odd k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isMinOn_iff`：isMinOn_iff : IsMinOn f s a ↔ forall x in s, f a <= f x
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Polynomial.Chebyshev.eval_T_real_eq_neg_one_iff`：eval_T_real_eq_neg_one_
iff {n : Nat} (hn : n != 0) (x : Real) : (T Real n).eval x = -1 ↔ exists k <= n,
 Odd k ∧ x = cos (k * π / n)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Polynomial.Chebyshev.abs_eval_T_real_le_one`：abs_eval_T_real_le_one (n :
 Int) {x : Real} (hx : |x| <= 1) : |(T Real n).eval x| <= 1
-/
theorem isMinOn_T_real {n k : ℕ} (hn : n ≠ 0) (hk₁ : k ≤ n) (hk₂ : Odd k) :
    IsMinOn (T ℝ n).eval (Set.Icc (-1) 1) (cos (k * π / n)) :=
  isMinOn_iff.mpr (fun x hx => le_of_eq_of_le
    ((eval_T_real_eq_neg_one_iff hn _).mpr ⟨k, hk₁, hk₂, rfl⟩)
    (abs_le.mp (abs_eval_T_real_le_one n (by grind))).1)
/-
**Polynomial.Chebyshev.isExtrOn_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Che
byshev`。
形式化陈述：isExtrOn_T_real {n k : Nat} (hn : n != 0) (hk : k <= n) : IsExtrOn (T Real
 n).eval (Set.Icc (-1) 1) (cos (k * π / n))
参数：hn : n != 0；hk : k <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `Polynomial.Chebyshev.isMaxOn_T_real`：isMaxOn_T_real {n k : Nat} (hn : n 
!= 0) (hk₁ : k <= n) (hk₂ : Even k) : IsMaxOn (T Real n).eval (Set.Icc (-1) 1) (
cos (k * π / n))
· 使用定理 `Polynomial.Chebyshev.isMinOn_T_real`：isMinOn_T_real {n k : Nat} (hn : n 
!= 0) (hk₁ : k <= n) (hk₂ : Odd k) : IsMinOn (T Real n).eval (Set.Icc (-1) 1) (c
os (k * π / n))
-/
theorem isExtrOn_T_real {n k : ℕ} (hn : n ≠ 0) (hk : k ≤ n) :
    IsExtrOn (T ℝ n).eval (Set.Icc (-1) 1) (cos (k * π / n)) := by
  cases k.even_or_odd
  case inl hk₂ => exact .inr (isMaxOn_T_real hn hk hk₂)
  case inr hk₂ => exact .inl (isMinOn_T_real hn hk hk₂)
/-
**Polynomial.Chebyshev.isExtrOn_T_real_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Chebyshev`。
形式化陈述：isExtrOn_T_real_iff {n : Nat} (hn : n != 0) {x : Real} (hx : x in Set.Icc 
(-1) 1) : IsExtrOn (T Real n).eval (Set.Icc (-1) 1) x ↔ exists k <= n, x = cos (
k * π / n)
参数：hn : n != 0；hx : x in Set.Icc (-1) 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Chebyshev.abs_eval_T_real_eq_one_iff`：abs_eval_T_real_eq_one_
iff {n : Nat} (hn : n != 0) (x : Real) : |(T Real n).eval x| = 1 ↔ exists k <= n
, x = cos (k * π / n)
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Polynomial.Chebyshev.abs_eval_T_real_le_one`：abs_eval_T_real_le_one (n :
 Int) {x : Real} (hx : |x| <= 1) : |(T Real n).eval x| <= 1
· 使用定理 `IsExtrOn.elim`：IsExtrOn.elim {p : Prop} : IsExtrOn f s a -> (IsMinOn f s
 a -> p) -> (IsMaxOn f s a -> p) -> p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] {a
 b : α}, a ≤ |b| ↔ a ≤ b ∨ a ≤ -b
· 使用定理 `le_neg_of_le_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dLeftMono α] [AddRightMono α] {a b : α}, a ≤ -b → b ≤ -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `isMinOn_iff`：isMinOn_iff : IsMinOn f s a ↔ forall x in s, f a <= f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Chebyshev.eval_T_real_eq_neg_one_iff`：eval_T_real_eq_neg_one_
iff {n : Nat} (hn : n != 0) (x : Real) : (T Real n).eval x = -1 ↔ exists k <= n,
 Odd k ∧ x = cos (k * π / n)
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `isMaxOn_iff`：isMaxOn_iff : IsMaxOn f s a ↔ forall x in s, f x <= f a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `Polynomial.Chebyshev.eval_T_real_eq_one_iff`：eval_T_real_eq_one_iff {n :
 Nat} (hn : n != 0) (x : Real) : (T Real n).eval x = 1 ↔ exists k <= n, Even k ∧
 x = cos (k * π / n)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 31 条，此处仅展示前 30 条）
-/
theorem isExtrOn_T_real_iff {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    IsExtrOn (T ℝ n).eval (Set.Icc (-1) 1) x ↔
    ∃ k ≤ n, x = cos (k * π / n) := by
  constructor
  · intro h
    apply (abs_eval_T_real_eq_one_iff hn x).mp
    apply eq_of_le_of_ge (abs_eval_T_real_le_one n (by grind))
    refine h.elim (fun h => ?_) (fun h => ?_)
    · refine le_abs.mpr (.inr (le_neg_of_le_neg ?_))
      have := isMinOn_iff.mp h (cos (1 * π / n)) (by grind [abs_cos_le_one])
      rw [(eval_T_real_eq_neg_one_iff hn (cos (1 * π / n))).mpr ⟨1, Nat.one_le_iff_ne_zero.mpr hn,
        by simp⟩] at this
      assumption
    · refine le_abs.mpr (.inl ?_)
      have := isMaxOn_iff.mp h (cos (0 * π / n)) (by simp)
      rw [(eval_T_real_eq_one_iff hn _).mpr ⟨0, by simp, by simp⟩] at this
      assumption
  · rintro ⟨k, hk, hx⟩
    rw [hx]
    exact isExtrOn_T_real hn hk
/-
**Polynomial.Chebyshev.irrational_of_isRoot_T_real** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial.Chebyshev`。
形式化陈述：irrational_of_isRoot_T_real {n : Nat} {x : Real} (hroot : (T Real n).IsRoo
t x) (hnz : x != 0) : Irrational x
参数：hroot : (T Real n).IsRoot x；hnz : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_val`：mem_val {a : α} {s : Finset α} : (a in s.1) = (a in s)
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Polynomial.Chebyshev.roots_T_real`：roots_T_real (n : Nat) : (T Real n).r
oots = ((Finset.range n).image (fun (k : Nat) => cos ((2 * k + 1) * π / (2 * n))
)).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.Chebyshev.T_ne_zero`：T_ne_zero (n : Int) [IsDomain R] [NeZero
 (2 : R)] : T R n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `irrational_cos_rat_mul_pi`：irrational_cos_rat_mul_pi {r : Rat} (hr : 3 <
 r.den) : Irrational (cos (r * π))
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Rat.den_divInt`：∀ (a b : ℤ), (Rat.divInt a b).den = if b = 0 then 1 else
 b.natAbs / b.gcd a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.gcd_natCast_natCast`：∀ (a b : ℕ), (↑a).gcd ↑b = a.gcd b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
（共 98 条，此处仅展示前 30 条）
-/
theorem irrational_of_isRoot_T_real {n : ℕ} {x : ℝ} (hroot : (T ℝ n).IsRoot x) (hnz : x ≠ 0) :
    Irrational x := by
  rw [← mem_roots (T_ne_zero ℝ n), roots_T_real, Finset.mem_val] at hroot
  obtain ⟨k, hk₁, hk₂⟩ := Finset.mem_image.mp hroot
  have hn : n ≠ 0 := by grind
  suffices Irrational (cos ((Rat.divInt (2 * k + 1) (2 * n)) * π)) by
    rw [← hk₂]; convert! this using 2; push_cast; field_simp
  apply irrational_cos_rat_mul_pi
  contrapose! hnz
  have : (Rat.divInt (2 * k + 1) (2 * n)).den = 2 * (n / n.gcd (2 * k + 1)) := calc
    _ = 2 * n / (2 * n).gcd (2 * k + 1) := by rw [Rat.den_divInt]; norm_cast; simp [hn]
    _ = _ := by rw [Nat.Coprime.gcd_mul_left_cancel n (by simp),
      Nat.mul_div_assoc _ (Nat.gcd_dvd_left ..)]
  have hn : 2 * k + 1 = n := Nat.eq_of_dvd_of_lt_two_mul (by simp) (Nat.gcd_eq_left_iff_dvd.mp <|
    Nat.eq_of_dvd_of_div_eq_one (Nat.gcd_dvd_left ..) (by grind [Rat.den_pos])) (by grind)
  rw_mod_cast [← hk₂, hn]; convert! cos_pi_div_two using 2; push_cast; field_simp
/-
**Polynomial.Chebyshev.abs_iterate_derivative_T_real_le** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial.Chebyshev`。
形式化陈述：abs_iterate_derivative_T_real_le (n : Int) (k : Nat) {x : Real} (hx : |x| 
<= 1) : |(derivative^[k] (T Real n)).eval x| <= (derivative^[k] (T Real n)).eval
 1
参数：n : Int；k : Nat；hx : |x| <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `Polynomial.Chebyshev.T_iterate_derivative_mem_span_T`：T_iterate_derivati
ve_mem_span_T (n k : Nat) : derivative^[k] (T R n) in Submodule.span Nat ((fun m
 : Nat => T R m) '' Set.Icc 0 (n - k))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_set`：Submodule.mem_span_set {m : M} {s : Set M} : m i
n Submodule.span R s ↔ exists c : M ->₀ R, (c.support : Set M) subseteq s ∧ (c.s
um fun mi r …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_smul`：eval_smul [SMulZeroClass S R] [IsScalarTower S R R
] (s : S) (p : R[X]) (x : R) : (s • p).eval x = s • p.eval x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.abs_sum_le_sum_abs`：abs_sum_le_sum_abs {G : Type*} [AddCommGroup 
G] [LinearOrder G] [IsOrderedAddMonoid G] (f : ι -> G) (s : Finset ι) : |∑ i in 
s, f i| <= ∑ i …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `abs_nsmul`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrde
r G] [IsOrderedAddMonoid G] (n : ℕ) (a : G),   |n • a| = n • |a|
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `Polynomial.Chebyshev.abs_eval_T_real_le_one`：abs_eval_T_real_le_one (n :
 Int) {x : Real} (hx : |x| <= 1) : |(T Real n).eval x| <= 1
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.Chebyshev.T_eval_one`：T_eval_one (n : Int) : (T R n).eval 1 =
 1
（共 32 条，此处仅展示前 30 条）
-/
theorem abs_iterate_derivative_T_real_le (n : ℤ) (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(derivative^[k] (T ℝ n)).eval x| ≤ (derivative^[k] (T ℝ n)).eval 1 := by
  wlog hn : 0 ≤ n
  · convert! this (-n) k hx (by grind) using 1 <;> rw [T_neg]
  lift n to ℕ using hn
  have := T_iterate_derivative_mem_span_T (R := ℝ) n k
  obtain ⟨f, hfsupp, hfderiv⟩ := Submodule.mem_span_set.mp this
  replace hfderiv : ∑ p ∈ f.support, f p • p = derivative^[k] (T ℝ n) := by rw [← hfderiv]; rfl
  have hf (y : ℝ) :
      ∑ p ∈ f.support, f p • p.eval y = (derivative^[k] (T ℝ n)).eval y := by
    rw [← hfderiv, Polynomial.eval_finsetSum]
    simp_rw [Polynomial.eval_smul]
  rw [← hf x, ← hf 1]
  grw [Finset.abs_sum_le_sum_abs]
  refine Finset.sum_le_sum (fun i hi => ?_)
  obtain ⟨m, hm, hi⟩ := (Set.mem_image ..).mp (hfsupp hi)
  grw [abs_nsmul, ← hi, abs_eval_T_real_le_one m hx]
  simp

end Polynomial.Chebyshev

