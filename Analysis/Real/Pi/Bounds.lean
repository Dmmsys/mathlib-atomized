/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Pi

This file contains lemmas which establish bounds on `Real.pi`.
Notably, these include `pi_gt_sqrtTwoAddSeries` and `pi_lt_sqrtTwoAddSeries`,
which bound `π` using series;
numerical bounds on `π` such as `pi_gt_d2` and `pi_lt_d2` (more precise versions are given, too).

See also `Mathlib/Analysis/Real/Pi/Leibniz.lean` and `Mathlib/Analysis/Real/Pi/Wallis.lean` for
infinite formulas for `π`.
-/

public section

open scoped Real

namespace Real

/-
**Real.pi_gt_sqrtTwoAddSeries** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_gt_sqrtTwoAddSeries (n : Nat) : 2 ^ (n + 1) * √(2 - sqrtTwoAddSeries 0 
n) < π
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.sin_pi_over_two_pow_succ`：sin_pi_over_two_pow_succ (n : Nat) : sin 
(π / 2 ^ (n + 2)) = √(2 - sqrtTwoAddSeries 0 n) / 2
· 使用定理 `Real.sin_lt`：sin_lt (h : 0 < x) : sin x < x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem pi_gt_sqrtTwoAddSeries (n : ℕ) : 2 ^ (n + 1) * √(2 - sqrtTwoAddSeries 0 n) < π := by
  have : √(2 - sqrtTwoAddSeries 0 n) / 2 * 2 ^ (n + 2) < π := by
    rw [← lt_div_iff₀, ← sin_pi_over_two_pow_succ]
    focus
      apply sin_lt
      apply div_pos pi_pos
    all_goals apply pow_pos; norm_num
  refine lt_of_le_of_lt (le_of_eq ?_) this
  rw [pow_succ' _ (n + 1), ← mul_assoc, div_mul_cancel₀, mul_comm]; simp
/-
**Real.pi_lt_sqrtTwoAddSeries** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_lt_sqrtTwoAddSeries (n : Nat) : π < 2 ^ (n + 1) * √(2 - sqrtTwoAddSerie
s 0 n) + 1 / 4 ^ n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.sin_pi_over_two_pow_succ`：sin_pi_over_two_pow_succ (n : Nat) : sin 
(π / 2 ^ (n + 2)) = √(2 - sqrtTwoAddSeries 0 n) / 2
· 使用定理 `sub_lt_iff_lt_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, a - b < c ↔ a < b + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_lt_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] {a b c : α}, a - b < c ↔ a - c < b
· 使用定理 `Real.sin_gt_sub_cube`：sin_gt_sub_cube {x : Real} (hx : 0 < x) : x - x ^ 
3 / 6 < Real.sin x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `div_le_div₀`：div_le_div₀ (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb 
: d <= b) : a / b <= c / d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 111 条，此处仅展示前 30 条）
-/
theorem pi_lt_sqrtTwoAddSeries (n : ℕ) :
    π < 2 ^ (n + 1) * √(2 - sqrtTwoAddSeries 0 n) + 1 / 4 ^ n := by
  have : π < (√(2 - sqrtTwoAddSeries 0 n) / 2 + 1 / (2 ^ n) ^ 3 / 4) * (2 : ℝ) ^ (n + 2) := by
    rw [← div_lt_iff₀ (by simp), ← sin_pi_over_two_pow_succ, ← sub_lt_iff_lt_add']
    calc
      π / 2 ^ (n + 2) - sin (π / 2 ^ (n + 2)) < (π / 2 ^ (n + 2)) ^ 3 / 6 :=
        sub_lt_comm.1 <| sin_gt_sub_cube (by positivity)
      _ ≤ (4 / 2 ^ (n + 2)) ^ 3 / 4 := by gcongr; exacts [pi_le_four, by norm_num]
      _ = 1 / (2 ^ n) ^ 3 / 4 := by simp [add_comm n, pow_add, div_mul_eq_div_div]; norm_num
  refine lt_of_lt_of_le this (le_of_eq ?_); rw [add_mul]; congr 1
  · ring
  simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, div_div, ← pow_add]
  rw [one_div, one_div, inv_mul_eq_iff_eq_mul₀, eq_comm, mul_inv_eq_iff_eq_mul₀, ← pow_add]
  · rw [add_assoc, Nat.mul_succ, add_comm, add_comm n, add_assoc, mul_comm n]
  all_goals norm_num

/-- From an upper bound on `sqrtTwoAddSeries 0 n = 2 cos (π / 2 ^ (n+1))` of the form
`sqrtTwoAddSeries 0 n ≤ 2 - (a / 2 ^ (n + 1)) ^ 2)`, one can deduce the lower bound `a < π`
thanks to basic trigonometric inequalities as expressed in `pi_gt_sqrtTwoAddSeries`. -/
/-
**Real.pi_lower_bound_start** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_lower_bound_start (n : Nat) {a} (h : sqrtTwoAddSeries ((0 : Nat) / (1 :
 Nat)) n <= (2 : Real) - (a / (2 : Real) ^ (n + 1)) ^ 2) : a < π
参数：n : Nat；h : sqrtTwoAddSeries ((0 : Nat) / (1 : Nat)) n <= (2 : Real) - (a / (
2 : Real) ^ (n + 1)) ^ 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Real.le_sqrt_of_sq_le`：le_sqrt_of_sq_le (h : x ^ 2 <= y) : x <= √y
· 使用定理 `le_sub_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE α] [Add
LeftMono α] {a b c : α}, a ≤ b - c ↔ c ≤ b - a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.pi_gt_sqrtTwoAddSeries`：pi_gt_sqrtTwoAddSeries (n : Nat) : 2 ^ (n +
 1) * √(2 - sqrtTwoAddSeries 0 n) < π

--- 原说明 ---
From an upper bound on `sqrtTwoAddSeries 0 n = 2 cos (π / 2 ^ (n+1))` of the for
m
`sqrtTwoAddSeries 0 n ≤ 2 - (a / 2 ^ (n + 1)) ^ 2)`, one can deduce the lower bo
und `a < π`
thanks to basic trigonometric inequalities as expressed in `pi_gt_sqrtTwoAddSeri
es`.
-/
theorem pi_lower_bound_start (n : ℕ) {a}
    (h : sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤ (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
    a < π := by
  refine lt_of_le_of_lt ?_ (pi_gt_sqrtTwoAddSeries n); rw [mul_comm]
  refine (div_le_iff₀ (pow_pos (by simp) _)).mp (le_sqrt_of_sq_le ?_)
  rwa [le_sub_comm, show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by rw [Nat.cast_zero, zero_div]]
/-
**Real.sqrtTwoAddSeries_step_up** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrtTwoAddSeries_step_up (c d : Nat) {a b n : Nat} {z : Real} (hz : sqrtTw
oAddSeries (c / d) n <= z) (hb : 0 < b) (hd : 0 < d) (h : (2 * b + a) * d ^ 2 <=
 c ^ 2 * b) : sqrtTwoAddSeries (a / b) (n + 1) <= z
参数：c d : Nat；hz : sqrtTwoAddSeries (c / d) n <= z；hb : 0 < b；hd : 0 < d；h : (2 *
 b + a) * d ^ 2 <= c ^ 2 * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrtTwoAddSeries_succ`：∀ (x : ℝ) (n : ℕ), x.sqrtTwoAddSeries (n + 1
) = (√(2 + x)).sqrtTwoAddSeries n
· 使用定理 `Real.sqrtTwoAddSeries_monotone_left`：∀ {x y : ℝ}, x ≤ y → ∀ (n : ℕ), x.s
qrtTwoAddSeries n ≤ y.sqrtTwoAddSeries n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Real.sqrt_le_left`：sqrt_le_left (hy : 0 <= y) : √x <= y ↔ x <= y ^ 2
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `add_div_eq_mul_add_div`：add_div_eq_mul_add_div (a b : K) (hc : c != 0) :
 a + b / c = (a * c + b) / c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `div_le_div_iff₀`：div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b <= c 
/ d ↔ a * d <= c * b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem sqrtTwoAddSeries_step_up (c d : ℕ) {a b n : ℕ} {z : ℝ} (hz : sqrtTwoAddSeries (c / d) n ≤ z)
    (hb : 0 < b) (hd : 0 < d) (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
    sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
  refine le_trans ?_ hz; rw [sqrtTwoAddSeries_succ]; apply sqrtTwoAddSeries_monotone_left
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
  rw [sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg), div_pow,
    add_div_eq_mul_add_div _ _ (ne_of_gt hb'), div_le_div_iff₀ hb' (pow_pos hd' _)]
  exact mod_cast h

/-- From a lower bound on `sqrtTwoAddSeries 0 n = 2 cos (π / 2 ^ (n+1))` of the form
`2 - ((a - 1 / 4 ^ n) / 2 ^ (n + 1)) ^ 2 ≤ sqrtTwoAddSeries 0 n`, one can deduce the upper bound
`π < a` thanks to basic trigonometric formulas as expressed in `pi_lt_sqrtTwoAddSeries`. -/
/-
**Real.pi_upper_bound_start** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_upper_bound_start (n : Nat) {a} (h : (2 : Real) - ((a - 1 / (4 : Real) 
^ n) / (2 : Real) ^ (n + 1)) ^ 2 <= sqrtTwoAddSeries ((0 : Nat) / (1 : Nat)) n) 
(h₂ : (1 : Real) / (4 : Real) ^ n <= a) : π < a
参数：n : Nat；h : (2 : Real) - ((a - 1 / (4 : Real) ^ n) / (2 : Real) ^ (n + 1)) ^ 
2 <= sqrtTwoAddSeries ((0 : Nat) / (1 : Nat)) n；h₂ : (1 : Real) / (4 : Real) ^ n
 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Real.pi_lt_sqrtTwoAddSeries`：pi_lt_sqrtTwoAddSeries (n : Nat) : π < 2 ^ 
(n + 1) * √(2 - sqrtTwoAddSeries 0 n) + 1 / 4 ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_sub_iff_add_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a ≤ c - b ↔ a + b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.sqrt_le_left`：sqrt_le_left (hy : 0 <= y) : √x <= y ↔ x <= y ^ 2
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `sub_le_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE α] [Add
LeftMono α] {a b c : α}, a - b ≤ c ↔ a - c ≤ b
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0

--- 原说明 ---
From a lower bound on `sqrtTwoAddSeries 0 n = 2 cos (π / 2 ^ (n+1))` of the form
`2 - ((a - 1 / 4 ^ n) / 2 ^ (n + 1)) ^ 2 ≤ sqrtTwoAddSeries 0 n`, one can deduce
 the upper bound
`π < a` thanks to basic trigonometric formulas as expressed in `pi_lt_sqrtTwoAdd
Series`.
-/
theorem pi_upper_bound_start (n : ℕ) {a}
    (h : (2 : ℝ) - ((a - 1 / (4 : ℝ) ^ n) / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
        sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
    (h₂ : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) : π < a := by
  refine lt_of_lt_of_le (pi_lt_sqrtTwoAddSeries n) ?_
  rw [← le_sub_iff_add_le, ← le_div_iff₀', sqrt_le_left, sub_le_comm]
  · rwa [Nat.cast_zero, zero_div] at h
  · exact div_nonneg (sub_nonneg.2 h₂) (pow_nonneg (le_of_lt zero_lt_two) _)
  · exact pow_pos zero_lt_two _
/-
**Real.sqrtTwoAddSeries_step_down** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sqrtTwoAddSeries_step_down (a b : Nat) {c d n : Nat} {z : Real} (hz : z <=
 sqrtTwoAddSeries (a / b) n) (hb : 0 < b) (hd : 0 < d) (h : a ^ 2 * d <= (2 * d 
+ c) * b ^ 2) : z <= sqrtTwoAddSeries (c / d) (n + 1)
参数：a b : Nat；hz : z <= sqrtTwoAddSeries (a / b) n；hb : 0 < b；hd : 0 < d；h : a ^ 
2 * d <= (2 * d + c) * b ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrtTwoAddSeries_succ`：∀ (x : ℝ) (n : ℕ), x.sqrtTwoAddSeries (n + 1
) = (√(2 + x)).sqrtTwoAddSeries n
· 使用定理 `Real.sqrtTwoAddSeries_monotone_left`：∀ {x y : ℝ}, x ≤ y → ∀ (n : ℕ), x.s
qrtTwoAddSeries n ≤ y.sqrtTwoAddSeries n
· 使用定理 `Real.le_sqrt_of_sq_le`：le_sqrt_of_sq_le (h : x ^ 2 <= y) : x <= √y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `add_div_eq_mul_add_div`：add_div_eq_mul_add_div (a b : K) (hc : c != 0) :
 a + b / c = (a * c + b) / c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `div_le_div_iff₀`：div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b <= c 
/ d ↔ a * d <= c * b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem sqrtTwoAddSeries_step_down (a b : ℕ) {c d n : ℕ} {z : ℝ}
    (hz : z ≤ sqrtTwoAddSeries (a / b) n) (hb : 0 < b) (hd : 0 < d)
    (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) : z ≤ sqrtTwoAddSeries (c / d) (n + 1) := by
  apply le_trans hz; rw [sqrtTwoAddSeries_succ]; apply sqrtTwoAddSeries_monotone_left
  apply le_sqrt_of_sq_le
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
  rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'), div_le_div_iff₀ (pow_pos hb' _) hd']
  exact mod_cast h

section Tactic

open Lean Elab Tactic Qq

/-- Create a proof of `a < π` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `√2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`√(2 + r i) ≤ r(i+1)`, where `r 0 = 0` and `√(2 - r n) ≥ a/2^(n+1)`. -/
elab "pi_lower_bound " "[" l:term,* "]" : tactic => do
  have els := l.getElems
  let n := quote els.size
  evalTactic (← `(tactic| apply pi_lower_bound_start $n))
  for l in els do
    let {num, den, ..} ← unsafe Meta.evalExpr ℚ q(ℚ) (← Term.elabTermAndSynthesize l (some q(ℚ)))
    evalTactic (← `(tactic| apply sqrtTwoAddSeries_step_up $(quote num.toNat) $(quote den)))
  evalTactic (← `(tactic| simp [sqrtTwoAddSeries]))
  allGoals <| evalTactic (← `(tactic| norm_num1))

/-- Create a proof of `π < a` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `√2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`√(2 + r i) ≥ r(i+1)`, where `r 0 = 0` and `√(2 - r n) ≤ (a - 1/4^n) / 2^(n+1)`. -/
elab "pi_upper_bound " "[" l:term,* "]" : tactic => do
  have els := l.getElems
  let n := quote els.size
  evalTactic (← `(tactic| apply pi_upper_bound_start $n))
  for l in els do
    let {num, den, ..} ← unsafe Meta.evalExpr ℚ q(ℚ) (← Term.elabTermAndSynthesize l (some q(ℚ)))
    evalTactic (← `(tactic| apply sqrtTwoAddSeries_step_down $(quote num.toNat) $(quote den)))
  evalTactic (← `(tactic| simp [sqrtTwoAddSeries]))
  allGoals <| evalTactic (← `(tactic| norm_num1))

end Tactic

/-!
The below witnesses were generated using the following Mathematica script:
```mathematica
bound[a_, Iters -> n_, Rounding -> extra_, Precision -> prec_] := Module[{r0, r, r2, diff, sign},
  On[Assert];
  sign = If[a >= \[Pi], Print["upper"]; 1, Print["lower"]; -1];
  r0 = 2 - ((a - (sign + 1)/2/4^n)/2^(n + 1))^2;
  r = Log[2 - NestList[#^2 - 2 &, N[r0, prec], n - 1]];
  diff = (r[[-1]] - Log[2 - Sqrt[2]])/(Length[r] + 1);
  If[sign diff <= 0, Return["insufficient iterations"]];
  r2 = Log[Rationalize[Exp[#], extra (Exp[#] - Exp[# - sign diff])] &
    /@ (r - diff Range[1, Length[r]])];
  Assert[sign (2 - Exp@r2[[1]] - r0) >= 0];
  Assert[And @@ Table[
    sign (Sqrt@(4 - Exp@r2[[i + 1]]) - (2 - Exp@r2[[i]])) >= 0, {i, 1, Length[r2] - 1}]];
  Assert[sign (Exp@r2[[-1]] - (2 - Sqrt[2])) >= 0];
  With[{s1 = ToString@InputForm[2 - #], s2 = ToString@InputForm[#]},
    If[StringLength[s1] <= StringLength[s2] + 2, s1, "2-" <> s2]] & /@ Exp@Reverse@r2
];
```
-/

/-
**Real.pi_gt_three** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_gt_three : 3 < π
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_lower_bound_start`：pi_lower_bound_start (n : Nat) {a} (h : sqrtT
woAddSeries ((0 : Nat) / (1 : Nat)) n <= (2 : Real) - (a / (2 : Real) ^ (n + 1))
 ^ 2) : a < π
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.sqrtTwoAddSeries_step_up`：sqrtTwoAddSeries_step_up (c d : Nat) {a b
 n : Nat} {z : Real} (hz : sqrtTwoAddSeries (c / d) n <= z) (hb : 0 < b) (hd : 0
 < d) (h : (2 * b +…
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_pow`：isNNRat_pow {α} [Semiring α] {f : α ->
 Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat} : f = HPow.hPow -> IsNNRat a
 an ad -> IsNat b b' -…
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …

--- 原说明 ---
The below witnesses were generated using the following Mathematica script:
```mathematica
bound[a_, Iters -> n_, Rounding -> extra_, Precision -> prec_] := Module[{r0, r,
 r2, diff, sign},
  On[Assert];
  sign = If[a >= \[Pi], Print["upper"]; 1, Print["lower"]; -1];
  r0 = 2 - ((a - (sign + 1)/2/4^n)/2^(n + 1))^2;
  r = Log[2 - NestList[#^2 - 2 &, N[r0, prec], n - 1]];
  diff = (r[[-1]] - Log[2 - Sqrt[2]])/(Length[r] + 1);
  If[sign diff <= 0, Return["insufficient iterations"]];
  r2 = Log[Rationalize[Exp[#], extra (Exp[#] - Exp[# - sign diff])] &
    /@ (r - diff Range[1, Length[r]])];
  Assert[sign (2 - Exp@r2[[1]] - r0) >= 0];
  Assert[And @@ Table[
    sign (Sqrt@(4 - Exp@r2[[i + 1]]) - (2 - Exp@r2[[i]])) >= 0, {i, 1, Length[r2
] - 1}]];
  Assert[sign (Exp@r2[[-1]] - (2 - Sqrt[2])) >= 0];
  With[{s1 = ToString@InputForm[2 - #], s2 = ToString@InputForm[#]},
    If[StringLength[s1] <= StringLength[s2] + 2, s1, "2-" <> s2]] & /@ Exp@Rever
se@r2
];
```
-/
theorem pi_gt_three : 3 < π := by
  -- bound[3, Iters -> 1, Rounding -> 2, Precision -> 3]
  pi_lower_bound [23 / 16]
/-
**Real.pi_lt_four** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_lt_four : π < 4
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_upper_bound_start`：pi_upper_bound_start (n : Nat) {a} (h : (2 : 
Real) - ((a - 1 / (4 : Real) ^ n) / (2 : Real) ^ (n + 1)) ^ 2 <= sqrtTwoAddSerie
s ((0 : Nat) / …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.sqrtTwoAddSeries_step_down`：sqrtTwoAddSeries_step_down (a b : Nat) 
{c d n : Nat} {z : Real} (hz : z <= sqrtTwoAddSeries (a / b) n) (hb : 0 < b) (hd
 : 0 < d) (h : a ^ 2 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_pow`：isNNRat_pow {α} [Semiring α] {f : α ->
 Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat} : f = HPow.hPow -> IsNNRat a
 an ad -> IsNat b b' -…
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
（共 35 条，此处仅展示前 30 条）
-/
theorem pi_lt_four : π < 4 := by
  -- bound[4, Iters -> 1, Rounding -> 1, Precision -> 1]
  pi_upper_bound [4 / 3]
/-
**Real.pi_gt_d2** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_gt_d2 : 3.14 < π
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_lower_bound_start`：pi_lower_bound_start (n : Nat) {a} (h : sqrtT
woAddSeries ((0 : Nat) / (1 : Nat)) n <= (2 : Real) - (a / (2 : Real) ^ (n + 1))
 ^ 2) : a < π
· 使用定理 `Real.sqrtTwoAddSeries_step_up`：sqrtTwoAddSeries_step_up (c d : Nat) {a b
 n : Nat} {z : Real} (hz : sqrtTwoAddSeries (c / d) n <= z) (hb : 0 < b) (hd : 0
 < d) (h : (2 * b +…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_pow`：isNNRat_pow {α} [Semiring α] {f : α ->
 Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat} : f = HPow.hPow -> IsNNRat a
 an ad -> IsNat b b' -…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true`：∀ {α : Type u_1} [ins
t : DivisionSemiring α] {m e n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat (↑(NNRat.d
ivNat m (10 ^ e))) n d →     Mathlib.Me…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_nnratCast`：∀ {R : Type u_1} [inst : Divisio
nSemiring R] [CharZero R] {q : ℚ≥0} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat q 
n d → Mathlib.Meta.NormNum.I…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_divNat`：∀ {a na n b nb d : ℕ},   Mathlib.Me
ta.NormNum.IsNat a na →     Mathlib.Meta.NormNum.IsNat b nb →       Mathlib.Meta
.NormNum.IsNNRat (↑na / ↑…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.raw_refl`：∀ (n : ℕ), Mathlib.Meta.NormNum.IsN
at n n
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.trans`：∀ {a b c : ℕ} {p : Prop} {b' c' : 
ℕ},   Mathlib.Meta.NormNum.IsNatPowT p a b c →     Mathlib.Meta.NormNum.IsNatPow
T (a.pow b = c) a b' c' → …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit1`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b + 1) (c.mul (c.mul a))
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 31 条，此处仅展示前 30 条）
-/
theorem pi_gt_d2 : 3.14 < π := by
  -- bound[314*^-2, Iters -> 4, Rounding -> 1.5, Precision -> 8]
  pi_lower_bound [338 / 239, 704 / 381, 1940 / 989, 1447 / 727]
/-
**Real.pi_lt_d2** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_lt_d2 : π < 3.15
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_upper_bound_start`：pi_upper_bound_start (n : Nat) {a} (h : (2 : 
Real) - ((a - 1 / (4 : Real) ^ n) / (2 : Real) ^ (n + 1)) ^ 2 <= sqrtTwoAddSerie
s ((0 : Nat) / …
· 使用定理 `Real.sqrtTwoAddSeries_step_down`：sqrtTwoAddSeries_step_down (a b : Nat) 
{c d n : Nat} {z : Real} (hz : z <= sqrtTwoAddSeries (a / b) n) (hb : 0 < b) (hd
 : 0 < d) (h : a ^ 2 …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_pow`：isNNRat_pow {α} [Semiring α] {f : α ->
 Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat} : f = HPow.hPow -> IsNNRat a
 an ad -> IsNat b b' -…
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true`：∀ {α : Type u_1} [ins
t : DivisionSemiring α] {m e n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat (↑(NNRat.d
ivNat m (10 ^ e))) n d →     Mathlib.Me…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_nnratCast`：∀ {R : Type u_1} [inst : Divisio
nSemiring R] [CharZero R] {q : ℚ≥0} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat q 
n d → Mathlib.Meta.NormNum.I…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_divNat`：∀ {a na n b nb d : ℕ},   Mathlib.Me
ta.NormNum.IsNat a na →     Mathlib.Meta.NormNum.IsNat b nb →       Mathlib.Meta
.NormNum.IsNNRat (↑na / ↑…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.raw_refl`：∀ (n : ℕ), Mathlib.Meta.NormNum.IsN
at n n
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
（共 40 条，此处仅展示前 30 条）
-/
theorem pi_lt_d2 : π < 3.15 := by
  -- bound[315*^-2, Iters -> 4, Rounding -> 1.4, Precision -> 7]
  pi_upper_bound [41 / 29, 109 / 59, 865 / 441, 412 / 207]
/-
**Real.pi_gt_d4** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_gt_d4 : 3.1415 < π
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_lower_bound_start`：pi_lower_bound_start (n : Nat) {a} (h : sqrtT
woAddSeries ((0 : Nat) / (1 : Nat)) n <= (2 : Real) - (a / (2 : Real) ^ (n + 1))
 ^ 2) : a < π
· 使用定理 `Real.sqrtTwoAddSeries_step_up`：sqrtTwoAddSeries_step_up (c d : Nat) {a b
 n : Nat} {z : Real} (hz : sqrtTwoAddSeries (c / d) n <= z) (hb : 0 < b) (hd : 0
 < d) (h : (2 * b +…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_pow`：isNNRat_pow {α} [Semiring α] {f : α ->
 Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat} : f = HPow.hPow -> IsNNRat a
 an ad -> IsNat b b' -…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true`：∀ {α : Type u_1} [ins
t : DivisionSemiring α] {m e n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat (↑(NNRat.d
ivNat m (10 ^ e))) n d →     Mathlib.Me…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_nnratCast`：∀ {R : Type u_1} [inst : Divisio
nSemiring R] [CharZero R] {q : ℚ≥0} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat q 
n d → Mathlib.Meta.NormNum.I…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_divNat`：∀ {a na n b nb d : ℕ},   Mathlib.Me
ta.NormNum.IsNat a na →     Mathlib.Meta.NormNum.IsNat b nb →       Mathlib.Meta
.NormNum.IsNNRat (↑na / ↑…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.raw_refl`：∀ (n : ℕ), Mathlib.Meta.NormNum.IsN
at n n
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.trans`：∀ {a b c : ℕ} {p : Prop} {b' c' : 
ℕ},   Mathlib.Meta.NormNum.IsNatPowT p a b c →     Mathlib.Meta.NormNum.IsNatPow
T (a.pow b = c) a b' c' → …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit1`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b + 1) (c.mul (c.mul a))
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 31 条，此处仅展示前 30 条）
-/
theorem pi_gt_d4 : 3.1415 < π := by
  -- bound[31415*^-4, Iters -> 6, Rounding -> 1.1, Precision -> 10]
  pi_lower_bound [
    1970 / 1393, 3010 / 1629, 11689 / 5959, 10127 / 5088, 33997 / 17019, 23235 / 11621]
/-
**Real.pi_lt_d4** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_lt_d4 : π < 3.1416
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_upper_bound_start`：pi_upper_bound_start (n : Nat) {a} (h : (2 : 
Real) - ((a - 1 / (4 : Real) ^ n) / (2 : Real) ^ (n + 1)) ^ 2 <= sqrtTwoAddSerie
s ((0 : Nat) / …
· 使用定理 `Real.sqrtTwoAddSeries_step_down`：sqrtTwoAddSeries_step_down (a b : Nat) 
{c d n : Nat} {z : Real} (hz : z <= sqrtTwoAddSeries (a / b) n) (hb : 0 < b) (hd
 : 0 < d) (h : a ^ 2 …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_pow`：isNNRat_pow {α} [Semiring α] {f : α ->
 Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat} : f = HPow.hPow -> IsNNRat a
 an ad -> IsNat b b' -…
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true`：∀ {α : Type u_1} [ins
t : DivisionSemiring α] {m e n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat (↑(NNRat.d
ivNat m (10 ^ e))) n d →     Mathlib.Me…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_nnratCast`：∀ {R : Type u_1} [inst : Divisio
nSemiring R] [CharZero R] {q : ℚ≥0} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat q 
n d → Mathlib.Meta.NormNum.I…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_divNat`：∀ {a na n b nb d : ℕ},   Mathlib.Me
ta.NormNum.IsNat a na →     Mathlib.Meta.NormNum.IsNat b nb →       Mathlib.Meta
.NormNum.IsNNRat (↑na / ↑…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.raw_refl`：∀ (n : ℕ), Mathlib.Meta.NormNum.IsN
at n n
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
（共 40 条，此处仅展示前 30 条）
-/
theorem pi_lt_d4 : π < 3.1416 := by
  -- bound[31416*^-4, Iters -> 9, Rounding -> .9, Precision -> 16]
  pi_upper_bound [
    4756/3363, 14965/8099, 21183/10799, 49188/24713, 2-53/22000, 2-71/117869, 2-47/312092,
    2-17/451533, 2-4/424971]
/-
**Real.pi_gt_d6** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_gt_d6 : 3.141592 < π
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_lower_bound_start`：pi_lower_bound_start (n : Nat) {a} (h : sqrtT
woAddSeries ((0 : Nat) / (1 : Nat)) n <= (2 : Real) - (a / (2 : Real) ^ (n + 1))
 ^ 2) : a < π
· 使用定理 `Real.sqrtTwoAddSeries_step_up`：sqrtTwoAddSeries_step_up (c d : Nat) {a b
 n : Nat} {z : Real} (hz : sqrtTwoAddSeries (c / d) n <= z) (hb : 0 < b) (hd : 0
 < d) (h : (2 * b +…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_pow`：isNNRat_pow {α} [Semiring α] {f : α ->
 Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat} : f = HPow.hPow -> IsNNRat a
 an ad -> IsNat b b' -…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true`：∀ {α : Type u_1} [ins
t : DivisionSemiring α] {m e n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat (↑(NNRat.d
ivNat m (10 ^ e))) n d →     Mathlib.Me…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_nnratCast`：∀ {R : Type u_1} [inst : Divisio
nSemiring R] [CharZero R] {q : ℚ≥0} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat q 
n d → Mathlib.Meta.NormNum.I…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_divNat`：∀ {a na n b nb d : ℕ},   Mathlib.Me
ta.NormNum.IsNat a na →     Mathlib.Meta.NormNum.IsNat b nb →       Mathlib.Meta
.NormNum.IsNNRat (↑na / ↑…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.raw_refl`：∀ (n : ℕ), Mathlib.Meta.NormNum.IsN
at n n
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.trans`：∀ {a b c : ℕ} {p : Prop} {b' c' : 
ℕ},   Mathlib.Meta.NormNum.IsNatPowT p a b c →     Mathlib.Meta.NormNum.IsNatPow
T (a.pow b = c) a b' c' → …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit1`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b + 1) (c.mul (c.mul a))
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 31 条，此处仅展示前 30 条）
-/
theorem pi_gt_d6 : 3.141592 < π := by
  -- bound[3141592*^-6, Iters -> 10, Rounding -> .8, Precision -> 16]
  pi_lower_bound [
    11482/8119, 7792/4217, 54055/27557, 2-623/64690, 2-337/139887, 2-208/345307, 2-167/1108925,
    2-64/1699893, 2-31/3293535, 2-48/20398657]
/-
**Real.pi_lt_d6** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_lt_d6 : π < 3.141593
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_upper_bound_start`：pi_upper_bound_start (n : Nat) {a} (h : (2 : 
Real) - ((a - 1 / (4 : Real) ^ n) / (2 : Real) ^ (n + 1)) ^ 2 <= sqrtTwoAddSerie
s ((0 : Nat) / …
· 使用定理 `Real.sqrtTwoAddSeries_step_down`：sqrtTwoAddSeries_step_down (a b : Nat) 
{c d n : Nat} {z : Real} (hz : z <= sqrtTwoAddSeries (a / b) n) (hb : 0 < b) (hd
 : 0 < d) (h : a ^ 2 …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_pow`：isNNRat_pow {α} [Semiring α] {f : α ->
 Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat} : f = HPow.hPow -> IsNNRat a
 an ad -> IsNat b b' -…
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true`：∀ {α : Type u_1} [ins
t : DivisionSemiring α] {m e n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat (↑(NNRat.d
ivNat m (10 ^ e))) n d →     Mathlib.Me…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_nnratCast`：∀ {R : Type u_1} [inst : Divisio
nSemiring R] [CharZero R] {q : ℚ≥0} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat q 
n d → Mathlib.Meta.NormNum.I…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_divNat`：∀ {a na n b nb d : ℕ},   Mathlib.Me
ta.NormNum.IsNat a na →     Mathlib.Meta.NormNum.IsNat b nb →       Mathlib.Meta
.NormNum.IsNNRat (↑na / ↑…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.raw_refl`：∀ (n : ℕ), Mathlib.Meta.NormNum.IsN
at n n
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
（共 40 条，此处仅展示前 30 条）
-/
theorem pi_lt_d6 : π < 3.141593 := by
  -- bound[3141593*^-6, Iters -> 11, Rounding -> .5, Precision -> 17]
  pi_upper_bound [
    35839/25342, 49143/26596, 145729/74292, 294095/147759, 2-137/56868, 2-471/781921, 2-153/1015961,
    2-157/4170049, 2-28/2974805, 2-9/3824747, 2-7/11899211]
/-
**Real.pi_gt_d20** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_gt_d20 : 3.14159265358979323846 < π
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_lower_bound_start`：pi_lower_bound_start (n : Nat) {a} (h : sqrtT
woAddSeries ((0 : Nat) / (1 : Nat)) n <= (2 : Real) - (a / (2 : Real) ^ (n + 1))
 ^ 2) : a < π
· 使用定理 `Real.sqrtTwoAddSeries_step_up`：sqrtTwoAddSeries_step_up (c d : Nat) {a b
 n : Nat} {z : Real} (hz : sqrtTwoAddSeries (c / d) n <= z) (hb : 0 < b) (hd : 0
 < d) (h : (2 * b +…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_pow`：isNNRat_pow {α} [Semiring α] {f : α ->
 Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat} : f = HPow.hPow -> IsNNRat a
 an ad -> IsNat b b' -…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true`：∀ {α : Type u_1} [ins
t : DivisionSemiring α] {m e n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat (↑(NNRat.d
ivNat m (10 ^ e))) n d →     Mathlib.Me…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_nnratCast`：∀ {R : Type u_1} [inst : Divisio
nSemiring R] [CharZero R] {q : ℚ≥0} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat q 
n d → Mathlib.Meta.NormNum.I…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_divNat`：∀ {a na n b nb d : ℕ},   Mathlib.Me
ta.NormNum.IsNat a na →     Mathlib.Meta.NormNum.IsNat b nb →       Mathlib.Meta
.NormNum.IsNNRat (↑na / ↑…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.raw_refl`：∀ (n : ℕ), Mathlib.Meta.NormNum.IsN
at n n
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.trans`：∀ {a b c : ℕ} {p : Prop} {b' c' : 
ℕ},   Mathlib.Meta.NormNum.IsNatPowT p a b c →     Mathlib.Meta.NormNum.IsNatPow
T (a.pow b = c) a b' c' → …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit1`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b + 1) (c.mul (c.mul a))
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 31 条，此处仅展示前 30 条）
-/
theorem pi_gt_d20 : 3.14159265358979323846 < π := by
  -- bound[314159265358979323846*^-20, Iters -> 34, Rounding -> .6, Precision -> 46]
  pi_lower_bound [
    671574048197/474874563549, 58134718954/31462283181, 3090459598621/1575502640777,
    2-7143849599/741790664068, 8431536490061/4220852446654, 2-2725579171/4524814682468,
    2-2494895647/16566776788806, 2-608997841/16175484287402, 2-942567063/100141194694075,
    2-341084060/144951150987041, 2-213717653/363295959742218, 2-71906926/488934711121807,
    2-29337101/797916288104986, 2-45326311/4931175952730065, 2-7506877/3266776448781479,
    2-5854787/10191338039232571, 2-4538642/31601378399861717, 2-276149/7691013341581098,
    2-350197/39013283396653714, 2-442757/197299283738495963, 2-632505/1127415566199968707,
    2-1157/8249230030392285, 2-205461/5859619883403334178, 2-33721/3846807755987625852,
    2-11654/5317837263222296743, 2-8162/14897610345776687857, 2-731/5337002285107943372,
    2-1320/38549072592845336201, 2-707/82588467645883795866, 2-53/24764858756615791675,
    2-237/442963888703240952920, 2-128/956951523274512100791, 2-32/956951523274512100783,
    2-27/3229711391051478340136]
/-
**Real.pi_lt_d20** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：pi_lt_d20 : π < 3.14159265358979323847
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.pi_upper_bound_start`：pi_upper_bound_start (n : Nat) {a} (h : (2 : 
Real) - ((a - 1 / (4 : Real) ^ n) / (2 : Real) ^ (n + 1)) ^ 2 <= sqrtTwoAddSerie
s ((0 : Nat) / …
· 使用定理 `Real.sqrtTwoAddSeries_step_down`：sqrtTwoAddSeries_step_down (a b : Nat) 
{c d n : Nat} {z : Real} (hz : z <= sqrtTwoAddSeries (a / b) n) (hb : 0 < b) (hd
 : 0 < d) (h : a ^ 2 …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_pow`：isNNRat_pow {α} [Semiring α] {f : α ->
 Nat -> α} {a : α} {an cn : Nat} {ad b b' cd : Nat} : f = HPow.hPow -> IsNNRat a
 an ad -> IsNat b b' -…
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true`：∀ {α : Type u_1} [ins
t : DivisionSemiring α] {m e n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat (↑(NNRat.d
ivNat m (10 ^ e))) n d →     Mathlib.Me…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_nnratCast`：∀ {R : Type u_1} [inst : Divisio
nSemiring R] [CharZero R] {q : ℚ≥0} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat q 
n d → Mathlib.Meta.NormNum.I…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_divNat`：∀ {a na n b nb d : ℕ},   Mathlib.Me
ta.NormNum.IsNat a na →     Mathlib.Meta.NormNum.IsNat b nb →       Mathlib.Meta
.NormNum.IsNNRat (↑na / ↑…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.raw_refl`：∀ (n : ℕ), Mathlib.Meta.NormNum.IsN
at n n
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
（共 40 条，此处仅展示前 30 条）
-/
theorem pi_lt_d20 : π < 3.14159265358979323847 := by
  -- bound[314159265358979323847*^-20, Iters -> 34, Rounding -> .5, Precision -> 46]
  pi_upper_bound [
    215157040700/152139002499, 936715022285/506946517009, 1760670193473/897581880893,
    2-6049918861/628200981455, 2-8543385003/3546315642356, 2-2687504973/4461606579043,
    2-1443277808/9583752057175, 2-546886849/14525765179168, 2-650597193/69121426717657,
    2-199969519/84981432264454, 2-226282901/384655467333100, 2-60729699/412934601558121,
    2-25101251/682708800188252, 2-7156464/778571703825145, 2-7524725/3274543383827551,
    2-4663362/8117442793616861, 2-1913009/13319781840326041, 2-115805/3225279830894912,
    2-708749/78957345705688293, 2-131255/58489233342660393, 2-101921/181670219085488669,
    2-44784/319302953916238627, 2-82141/2342610212364552264, 2-4609/525783249231842696,
    2-4567/2083967975041722089, 2-2273/4148770928197796067, 2-563/4110440884426500846,
    2-784/22895812812720260289, 2-1717/200571992854289218531, 2-368/171952226838388893139,
    2-149/278487845640434185590, 2-207/1547570041545500037992, 2-20/598094702046570062987,
    2-7/837332582865198088180]
/-
**Real.floor_pi_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：floor_pi_eq_three : ⌊π⌋ = 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.floor_eq_iff`：floor_eq_iff : ⌊a⌋ = z ↔ ↑z <= a ∧ a < z + 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.pi_gt_three`：pi_gt_three : 3 < π
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Real.pi_lt_four`：pi_lt_four : π < 4
-/
theorem floor_pi_eq_three : ⌊π⌋ = 3 :=
  Int.floor_eq_iff.mpr ⟨pi_gt_three.le, by exact_mod_cast pi_lt_four⟩
/-
**Real.ceil_pi_eq_four** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：ceil_pi_eq_four : ⌈π⌉ = 4
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ceil_eq_iff`：ceil_eq_iff : ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a <= z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Real.pi_gt_three`：pi_gt_three : 3 < π
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.pi_lt_four`：pi_lt_four : π < 4
-/
theorem ceil_pi_eq_four : ⌈π⌉ = 4 :=
  Int.ceil_eq_iff.mpr ⟨by exact_mod_cast pi_gt_three, pi_lt_four.le⟩
/-
**Real.round_pi_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：round_pi_eq_three : round π = 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `round_eq`：round_eq (x : α) : round x = ⌊x + 1 / 2⌋
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.floor_eq_iff`：floor_eq_iff : ⌊a⌋ = z ↔ ↑z <= a ∧ a < z + 1
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.pi_lt_d2`：pi_lt_d2 : π < 3.15
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_ofScientific_of_true`：∀ {α : Type u_1} [ins
t : DivisionSemiring α] {m e n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat (↑(NNRat.d
ivNat m (10 ^ e))) n d →     Mathlib.Me…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_nnratCast`：∀ {R : Type u_1} [inst : Divisio
nSemiring R] [CharZero R] {q : ℚ≥0} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat q 
n d → Mathlib.Meta.NormNum.I…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_divNat`：∀ {a na n b nb d : ℕ},   Mathlib.Me
ta.NormNum.IsNat a na →     Mathlib.Meta.NormNum.IsNat b nb →       Mathlib.Meta
.NormNum.IsNNRat (↑na / ↑…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.raw_refl`：∀ (n : ℕ), Mathlib.Meta.NormNum.IsN
at n n
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
（共 37 条，此处仅展示前 30 条）
-/
theorem round_pi_eq_three : round π = 3 := by
  refine round_eq _ |>.trans <| Int.floor_eq_iff.mpr ⟨by grind [pi_gt_three], ?_⟩
  grw [pi_lt_d2]
  norm_num

end Real

