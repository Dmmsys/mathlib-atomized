/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
module

public import Mathlib.Analysis.Complex.Asymptotics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Complex and real exponential

In this file we prove continuity of `Complex.exp` and `Real.exp`. We also prove a few facts about
limits of `Real.exp` at infinity.

## Tags

exp
-/

@[expose] public section

noncomputable section

open Asymptotics Bornology Finset Filter Function Metric Set Topology

open scoped Nat

namespace Complex

variable {z y x : ℝ}

/-
**Complex.exp_bound_sq** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：exp_bound_sq (x z : Complex) (hz : ‖z‖ <= 1) : ‖exp (x + z) - exp x - z • 
exp x‖ <= ‖exp x‖ * ‖z‖ ^ 2
参数：x z : Complex；hz : ‖z‖ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 38 条，此处仅展示前 30 条）
-/
theorem exp_bound_sq (x z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖exp (x + z) - exp x - z • exp x‖ ≤ ‖exp x‖ * ‖z‖ ^ 2 :=
  calc
    ‖exp (x + z) - exp x - z * exp x‖ = ‖exp x * (exp z - 1 - z)‖ := by
      congr
      rw [exp_add]
      ring
    _ = ‖exp x‖ * ‖exp z - 1 - z‖ := norm_mul _ _
    _ ≤ ‖exp x‖ * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (norm_exp_sub_one_sub_id_le hz) (norm_nonneg _)
/-
**Complex.locally_lipschitz_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：locally_lipschitz_exp {r : Real} (hr_nonneg : 0 <= r) (hr_le : r <= 1) (x 
y : Complex) (hyx : ‖y - x‖ < r) : ‖exp y - exp x‖ <= (1 + r) * ‖exp x‖ * ‖y - x
‖
参数：hr_nonneg : 0 <= r；hr_le : r <= 1；x y : Complex；hyx : ‖y - x‖ < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.SpecialFunctions.Exp.0.Complex.locally_lipschi
tz_exp._abel_1_1`：∀ (x y : ℂ), y = x + (y - x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Complex.exp_bound_sq`：exp_bound_sq (x z : Complex) (hz : ‖z‖ <= 1) : ‖ex
p (x + z) - exp x - z • exp x‖ <= ‖exp x‖ * ‖z‖ ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_sub_norm_le`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), ‖a‖ - ‖b‖ ≤ ‖a - b‖
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 41 条，此处仅展示前 30 条）
-/
theorem locally_lipschitz_exp {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_le : r ≤ 1) (x y : ℂ)
    (hyx : ‖y - x‖ < r) : ‖exp y - exp x‖ ≤ (1 + r) * ‖exp x‖ * ‖y - x‖ := by
  have hy_eq : y = x + (y - x) := by abel
  have hyx_sq_le : ‖y - x‖ ^ 2 ≤ r * ‖y - x‖ := by
    rw [pow_two]
    exact mul_le_mul hyx.le le_rfl (norm_nonneg _) hr_nonneg
  have h_sq : ∀ z, ‖z‖ ≤ 1 → ‖exp (x + z) - exp x‖ ≤ ‖z‖ * ‖exp x‖ + ‖exp x‖ * ‖z‖ ^ 2 := by
    intro z hz
    have : ‖exp (x + z) - exp x - z • exp x‖ ≤ ‖exp x‖ * ‖z‖ ^ 2 := exp_bound_sq x z hz
    rw [← sub_le_iff_le_add', ← norm_smul z]
    exact (norm_sub_norm_le _ _).trans this
  calc
    ‖exp y - exp x‖ = ‖exp (x + (y - x)) - exp x‖ := by nth_rw 1 [hy_eq]
    _ ≤ ‖y - x‖ * ‖exp x‖ + ‖exp x‖ * ‖y - x‖ ^ 2 := h_sq (y - x) (hyx.le.trans hr_le)
    _ ≤ ‖y - x‖ * ‖exp x‖ + ‖exp x‖ * (r * ‖y - x‖) := by grw [hyx_sq_le]
    _ = (1 + r) * ‖exp x‖ * ‖y - x‖ := by ring

-- Porting note: proof by term mode `locally_lipschitz_exp zero_le_one le_rfl x`
-- doesn't work because `‖y - x‖` and `dist y x` don't unify
@[continuity]
/-
**Complex.continuous_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuous_exp : Continuous exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `continuousAt_of_locally_lipschitz`：continuousAt_of_locally_lipschitz {f 
: α -> β} {x : α} {r : Real} (hr : 0 < r) (K : Real) (h : forall y, dist y x < r
 -> dist (f y) (f x) <=…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Complex.locally_lipschitz_exp`：locally_lipschitz_exp {r : Real} (hr_nonn
eg : 0 <= r) (hr_le : r <= 1) (x y : Complex) (hyx : ‖y - x‖ < r) : ‖exp y - exp
 x‖ <= (1 + r) * ‖e…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem continuous_exp : Continuous exp :=
  continuous_iff_continuousAt.mpr fun x =>
    continuousAt_of_locally_lipschitz zero_lt_one (2 * ‖exp x‖)
      (fun y ↦ by
        simpa [dist_eq_norm, one_add_one_eq_two] using locally_lipschitz_exp zero_le_one le_rfl x y)
/-
**Complex.continuousOn_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：continuousOn_exp {s : Set Complex} : ContinuousOn exp s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Complex.continuous_exp`：continuous_exp : Continuous exp
-/
theorem continuousOn_exp {s : Set ℂ} : ContinuousOn exp s :=
  continuous_exp.continuousOn
/-
**Complex.exp_sub_sum_range_isBigO_pow** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：exp_sub_sum_range_isBigO_pow (n : Nat) : (fun x => exp x - ∑ i in Finset.r
ange n, x ^ i / i !) =O[𝓝 0] (· ^ n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousAt.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {a : α},   ContinuousAt f a →
 Contin…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `NormedAddGroup.nhds_zero_basis_norm_lt`：∀ {E : Type u_5} [inst : Seminor
medAddGroup E], (nhds 0).HasBasis (fun ε => 0 < ε) fun ε => {y | ‖y‖ < ε}
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
（共 72 条，此处仅展示前 30 条）
-/
lemma exp_sub_sum_range_isBigO_pow (n : ℕ) :
    (fun x ↦ exp x - ∑ i ∈ Finset.range n, x ^ i / i !) =O[𝓝 0] (· ^ n) := by
  rcases eq_zero_or_pos n with rfl | hn
  · simpa using continuous_exp.continuousAt.norm.isBoundedUnder_le
  · refine .of_bound (n.succ / (n ! * n)) ?_
    rw [NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff]
    refine ⟨1, one_pos, fun x hx ↦ ?_⟩
    convert! exp_bound hx.out.le hn using 1
    simp [field]
/-
**Complex.exp_sub_sum_range_succ_isLittleO_pow** 是 Mathlib 中的一个引理，位于命名空间 `Comple
x`。
形式化陈述：exp_sub_sum_range_succ_isLittleO_pow (n : Nat) : (fun x => exp x - ∑ i in 
Finset.range (n + 1), x ^ i / i !) =o[𝓝 0] (· ^ n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用引理 `Complex.exp_sub_sum_range_isBigO_pow`：exp_sub_sum_range_isBigO_pow (n : 
Nat) : (fun x => exp x - ∑ i in Finset.range n, x ^ i / i !) =O[𝓝 0] (· ^ n)
· 使用定理 `Asymptotics.isLittleO_pow_pow`：isLittleO_pow_pow {m n : Nat} (h : m < n)
 : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
lemma exp_sub_sum_range_succ_isLittleO_pow (n : ℕ) :
    (fun x ↦ exp x - ∑ i ∈ Finset.range (n + 1), x ^ i / i !) =o[𝓝 0] (· ^ n) :=
  (exp_sub_sum_range_isBigO_pow (n + 1)).trans_isLittleO <| isLittleO_pow_pow n.lt_succ_self

end Complex

section ComplexContinuousExpComp

variable {α : Type*}

open Complex

/-
**Filter.Tendsto.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.cexp {l : Filter α} {f : α -> Complex} {z : Complex} (hf : 
Tendsto f l (𝓝 z)) : Tendsto (fun x => exp (f x)) l (𝓝 (exp z))
参数：hf : Tendsto f l (𝓝 z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Complex.continuous_exp`：continuous_exp : Continuous exp
-/
theorem Filter.Tendsto.cexp {l : Filter α} {f : α → ℂ} {z : ℂ} (hf : Tendsto f l (𝓝 z)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.tendsto _).comp hf

variable [TopologicalSpace α] {f : α → ℂ} {s : Set α} {x : α}

nonrec
/-
**ContinuousWithinAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.cexp (h : ContinuousWithinAt f s x) : ContinuousWithinA
t (fun y => exp (f y)) s x
参数：h : ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.cexp`：Filter.Tendsto.cexp {l : Filter α} {f : α -> Comple
x} {z : Complex} (hf : Tendsto f l (𝓝 z)) : Tendsto (fun x => exp (f x)) l (𝓝 (e
xp z))
-/
theorem ContinuousWithinAt.cexp (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun y => exp (f y)) s x :=
  h.cexp

@[fun_prop]
nonrec
/-
**ContinuousAt.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.cexp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y
)) x
参数：h : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.cexp`：Filter.Tendsto.cexp {l : Filter α} {f : α -> Comple
x} {z : Complex} (hf : Tendsto f l (𝓝 z)) : Tendsto (fun x => exp (f x)) l (𝓝 (e
xp z))
-/
theorem ContinuousAt.cexp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y)) x :=
  h.cexp

@[fun_prop]
/-
**ContinuousOn.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.cexp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y
)) s
参数：h : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.cexp`：ContinuousWithinAt.cexp (h : ContinuousWithinAt
 f s x) : ContinuousWithinAt (fun y => exp (f y)) s x
-/
theorem ContinuousOn.cexp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y)) s :=
  fun x hx => (h x hx).cexp

@[fun_prop]
/-
**Continuous.cexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.cexp (h : Continuous f) : Continuous fun y => exp (f y)
参数：h : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.cexp`：ContinuousAt.cexp (h : ContinuousAt f x) : Continuous
At (fun y => exp (f y)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.cexp (h : Continuous f) : Continuous fun y => exp (f y) :=
  continuous_iff_continuousAt.2 fun _ => h.continuousAt.cexp

/-- The complex exponential function is uniformly continuous on left half planes. -/
/-
**UniformContinuousOn.cexp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformContinuousOn.cexp (a : Real) : UniformContinuousOn exp {x : Complex
 | x.re <= a}
参数：a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_one`：continuous_one [TopologicalSpace M] [One M] : Continuous
 (1 : X -> M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.uniformContinuousOn_iff`：uniformContinuousOn_iff [PseudoMetricSpa
ce β] {f : α -> β} {s : Set α} : UniformContinuousOn f s ↔ forall ε > 0, exists 
δ > 0, forall x in s…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_sub_eq_dist_add_right`：∀ {E : Type u_2} [inst : SeminormedAddCommGr
oup E] (a b c : E), dist a (b - c) = dist (a + c) b
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Metric.continuous_iff'`：continuous_iff' [TopologicalSpace β] {f : β -> α
} : Continuous f ↔ forall (a), forall ε > 0, forallᶠ x in 𝓝 a, dist (f x) (f a) 
< ε
· 使用定理 `Metric.eventually_nhds_iff`：eventually_nhds_iff {p : α -> Prop} : (foral
lᶠ y in 𝓝 x, p y) ↔ exists ε > 0, forall ⦃y⦄, dist y x < ε -> p y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 105 条，此处仅展示前 30 条）

--- 原说明 ---
The complex exponential function is uniformly continuous on left half planes.
-/
lemma UniformContinuousOn.cexp (a : ℝ) : UniformContinuousOn exp {x : ℂ | x.re ≤ a} := by
  have : Continuous (cexp - 1) := Continuous.sub (by fun_prop) continuous_one
  rw [Metric.uniformContinuousOn_iff, Metric.continuous_iff'] at *
  intro ε hε
  simp only [gt_iff_lt, Pi.sub_apply, Pi.one_apply, dist_sub_eq_dist_add_right,
    sub_add_cancel] at this
  have ha : 0 < ε / (2 * Real.exp a) := by positivity
  have H := this 0 (ε / (2 * Real.exp a)) ha
  rw [Metric.eventually_nhds_iff] at H
  obtain ⟨δ, hδ⟩ := H
  refine ⟨δ, hδ.1, ?_⟩
  intro x _ y hy hxy
  have h3 := hδ.2 (y := x - y) (by simpa only [dist_eq_norm, sub_zero] using hxy)
  rw [dist_eq_norm, exp_zero] at *
  have : cexp x - cexp y = cexp y * (cexp (x - y) - 1) := by
    rw [mul_sub_one, ← exp_add]
    ring_nf
  rw [this, mul_comm]
  have hya : ‖cexp y‖ ≤ Real.exp a := by simpa only [norm_exp, Real.exp_le_exp]
  simp only [gt_iff_lt, dist_zero_right, Set.mem_ofPred_eq, norm_mul, Complex.norm_exp] at *
  apply lt_of_le_of_lt (mul_le_mul h3.le hya (Real.exp_nonneg y.re) ha.le)
  simp [field]

end ComplexContinuousExpComp

namespace Real

@[continuity, fun_prop]
/-
**Real.continuous_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_exp : Continuous exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
-/
theorem continuous_exp : Continuous exp := by
  unfold Real.exp; fun_prop
/-
**Real.continuousOn_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuousOn_exp {s : Set Real} : ContinuousOn exp s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
-/
theorem continuousOn_exp {s : Set ℝ} : ContinuousOn exp s := by fun_prop
/-
**Real.exp_sub_sum_range_isBigO_pow** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：exp_sub_sum_range_isBigO_pow (n : Nat) : (fun x => exp x - ∑ i in Finset.r
ange n, x ^ i / i !) =O[𝓝 0] (· ^ n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用引理 `Complex.exp_sub_sum_range_isBigO_pow`：exp_sub_sum_range_isBigO_pow (n : 
Nat) : (fun x => exp x - ∑ i in Finset.range n, x ^ i / i !) =O[𝓝 0] (· ^ n)
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
lemma exp_sub_sum_range_isBigO_pow (n : ℕ) :
    (fun x ↦ exp x - ∑ i ∈ Finset.range n, x ^ i / i !) =O[𝓝 0] (· ^ n) := by
  have := (Complex.exp_sub_sum_range_isBigO_pow n).comp_tendsto
    (Complex.continuous_ofReal.tendsto' 0 0 rfl)
  simp only [Function.comp_def] at this
  norm_cast at this
/-
**Real.exp_sub_sum_range_succ_isLittleO_pow** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：exp_sub_sum_range_succ_isLittleO_pow (n : Nat) : (fun x => exp x - ∑ i in 
Finset.range (n + 1), x ^ i / i !) =o[𝓝 0] (· ^ n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用引理 `Real.exp_sub_sum_range_isBigO_pow`：exp_sub_sum_range_isBigO_pow (n : Nat
) : (fun x => exp x - ∑ i in Finset.range n, x ^ i / i !) =O[𝓝 0] (· ^ n)
· 使用定理 `Asymptotics.isLittleO_pow_pow`：isLittleO_pow_pow {m n : Nat} (h : m < n)
 : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
lemma exp_sub_sum_range_succ_isLittleO_pow (n : ℕ) :
    (fun x ↦ exp x - ∑ i ∈ Finset.range (n + 1), x ^ i / i !) =o[𝓝 0] (· ^ n) :=
  (exp_sub_sum_range_isBigO_pow (n + 1)).trans_isLittleO <| isLittleO_pow_pow n.lt_succ_self

end Real

section RealContinuousExpComp

variable {α : Type*}

open Real

/-
**Filter.Tendsto.rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.rexp {l : Filter α} {f : α -> Real} {z : Real} (hf : Tendst
o f l (𝓝 z)) : Tendsto (fun x => exp (f x)) l (𝓝 (exp z))
参数：hf : Tendsto f l (𝓝 z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
-/
theorem Filter.Tendsto.rexp {l : Filter α} {f : α → ℝ} {z : ℝ} (hf : Tendsto f l (𝓝 z)) :
    Tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.tendsto _).comp hf

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {x : α}

nonrec
/-
**ContinuousWithinAt.rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.rexp (h : ContinuousWithinAt f s x) : ContinuousWithinA
t (fun y => exp (f y)) s x
参数：h : ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.rexp`：Filter.Tendsto.rexp {l : Filter α} {f : α -> Real} 
{z : Real} (hf : Tendsto f l (𝓝 z)) : Tendsto (fun x => exp (f x)) l (𝓝 (exp z))
-/
theorem ContinuousWithinAt.rexp (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun y ↦ exp (f y)) s x :=
  h.rexp

@[fun_prop]
nonrec
/-
**ContinuousAt.rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.rexp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y
)) x
参数：h : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.rexp`：Filter.Tendsto.rexp {l : Filter α} {f : α -> Real} 
{z : Real} (hf : Tendsto f l (𝓝 z)) : Tendsto (fun x => exp (f x)) l (𝓝 (exp z))
-/
theorem ContinuousAt.rexp (h : ContinuousAt f x) : ContinuousAt (fun y ↦ exp (f y)) x :=
  h.rexp
@[fun_prop]
/-
**ContinuousOn.rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.rexp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y
)) s
参数：h : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.rexp`：ContinuousWithinAt.rexp (h : ContinuousWithinAt
 f s x) : ContinuousWithinAt (fun y => exp (f y)) s x
-/
theorem ContinuousOn.rexp (h : ContinuousOn f s) :
    ContinuousOn (fun y ↦ exp (f y)) s :=
  fun x hx ↦ (h x hx).rexp
@[fun_prop]
/-
**Continuous.rexp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.rexp (h : Continuous f) : Continuous fun y => exp (f y)
参数：h : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.rexp`：ContinuousAt.rexp (h : ContinuousAt f x) : Continuous
At (fun y => exp (f y)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.rexp (h : Continuous f) : Continuous fun y ↦ exp (f y) :=
  continuous_iff_continuousAt.2 fun _ ↦ h.continuousAt.rexp
end RealContinuousExpComp

namespace Real

variable {α : Type*} {x y z : ℝ} {l : Filter α}

/-
**Real.exp_half** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：exp_half (x : Real) : exp (x / 2) = √(exp x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Real.sqrt_eq_iff_eq_sq`：sqrt_eq_iff_eq_sq (hx : 0 <= x) (hy : 0 <= y) : 
√x = y ↔ x = y ^ 2
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem exp_half (x : ℝ) : exp (x / 2) = √(exp x) := by
  rw [eq_comm, sqrt_eq_iff_eq_sq, sq, ← exp_add, add_halves] <;> exact (exp_pos _).le

/-- The real exponential function tends to `+∞` at `+∞`. -/
/-
**Real.tendsto_exp_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_exp_atTop : Tendsto exp atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_add_const_right`：∀ {α : Type u_1} {G : Type u_2} [i
nst : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filt
er α)   {f : α → G} (C : G…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Real.add_one_le_exp`：add_one_le_exp (x : Real) : x + 1 <= Real.exp x
· 使用定理 `Filter.tendsto_atTop_mono'`：tendsto_atTop_mono' [Preorder β] (l : Filter
 α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l
 atTop

--- 原说明 ---
The real exponential function tends to `+∞` at `+∞`.
-/
theorem tendsto_exp_atTop : Tendsto exp atTop atTop := by
  have A : Tendsto (fun x : ℝ => x + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have B : ∀ᶠ x in atTop, x + 1 ≤ exp x := eventually_atTop.2 ⟨0, fun x _ => add_one_le_exp x⟩
  exact tendsto_atTop_mono' atTop B A

/-- The function `y ↦ y * exp (-y)` is bounded above by `exp (-1)`. -/
/-
**Real.mul_exp_neg_le_exp_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mul_exp_neg_le_exp_neg_one (y : Real) : y * exp (-y) <= exp (-1)
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Real.add_one_le_exp`：add_one_le_exp (x : Real) : x + 1 <= Real.exp x
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - b + c = a + c - b
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a

--- 原说明 ---
The function `y ↦ y * exp (-y)` is bounded above by `exp (-1)`.
-/
theorem mul_exp_neg_le_exp_neg_one (y : ℝ) : y * exp (-y) ≤ exp (-1) := by
  have h_le : y ≤ exp (y - 1) := by simpa using add_one_le_exp (y - 1)
  have h_mul_le : y * rexp (-y) ≤ rexp (y - 1) * rexp (-y) := by gcongr
  simpa [← exp_add, sub_add_eq_add_sub] using h_mul_le

/-- The real exponential function tends to `0` at `-∞` or, equivalently, `exp(-x)` tends to `0`
at `+∞` -/
/-
**Real.tendsto_exp_neg_atTop_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_exp_neg_atTop_nhds_zero : Tendsto (fun x => exp (-x)) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.tendsto_exp_atTop`：tendsto_exp_atTop : Tendsto exp atTop atTop

--- 原说明 ---
The real exponential function tends to `0` at `-∞` or, equivalently, `exp(-x)` t
ends to `0`
at `+∞`
-/
theorem tendsto_exp_neg_atTop_nhds_zero : Tendsto (fun x => exp (-x)) atTop (𝓝 0) :=
  (tendsto_inv_atTop_zero.comp tendsto_exp_atTop).congr fun x => (exp_neg x).symm

/-- The real exponential function tends to `1` at `0`. -/
/-
**Real.tendsto_exp_nhds_zero_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_exp_nhds_zero_nhds_one : Tendsto exp (𝓝 0) (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp

--- 原说明 ---
The real exponential function tends to `1` at `0`.
-/
theorem tendsto_exp_nhds_zero_nhds_one : Tendsto exp (𝓝 0) (𝓝 1) := by
  convert! continuous_exp.tendsto 0
  simp
/-
**Real.tendsto_exp_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_exp_atBot : Tendsto exp atBot (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_exp_neg_atTop_nhds_zero`：tendsto_exp_neg_atTop_nhds_zero : 
Tendsto (fun x => exp (-x)) atTop (𝓝 0)
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
-/
theorem tendsto_exp_atBot : Tendsto exp atBot (𝓝 0) :=
  (tendsto_exp_neg_atTop_nhds_zero.comp tendsto_neg_atBot_atTop).congr fun x =>
    congr_arg exp <| neg_neg x
/-
**Real.tendsto_exp_atBot_nhdsGT** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_exp_atBot_nhdsGT : Tendsto exp atBot (𝓝[>] 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Real.tendsto_exp_atBot`：tendsto_exp_atBot : Tendsto exp atBot (𝓝 0)
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
theorem tendsto_exp_atBot_nhdsGT : Tendsto exp atBot (𝓝[>] 0) :=
  tendsto_inf.2 ⟨tendsto_exp_atBot, tendsto_principal.2 <| Eventually.of_forall exp_pos⟩

@[simp]
/-
**Real.isBoundedUnder_ge_exp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isBoundedUnder_ge_exp_comp (l : Filter α) (f : α -> Real) : IsBoundedUnder
 (· >= ·) l fun x => exp (f x)
参数：l : Filter α；f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.isBoundedUnder_of`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {f : Filter β} {u : β → α},   (∃ b, ∀ (x : β), r (u x) b) → Filter.IsBounde
dUnder r f u
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
theorem isBoundedUnder_ge_exp_comp (l : Filter α) (f : α → ℝ) :
    IsBoundedUnder (· ≥ ·) l fun x => exp (f x) :=
  isBoundedUnder_of ⟨0, fun _ => (exp_pos _).le⟩

@[simp]
/-
**Real.isBoundedUnder_le_exp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isBoundedUnder_le_exp_comp {f : α -> Real} : (IsBoundedUnder (· <= ·) l fu
n x => exp (f x)) ↔ IsBoundedUnder (· <= ·) l f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.isBoundedUnder_le_comp_iff`：Monotone.isBoundedUnder_le_comp_iff
 [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ] {g : β -> γ} {f : α ->
 β} {l : Filter α} (hg : …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `Real.tendsto_exp_atTop`：tendsto_exp_atTop : Tendsto exp atTop atTop
-/
theorem isBoundedUnder_le_exp_comp {f : α → ℝ} :
    (IsBoundedUnder (· ≤ ·) l fun x => exp (f x)) ↔ IsBoundedUnder (· ≤ ·) l f :=
  exp_monotone.isBoundedUnder_le_comp_iff tendsto_exp_atTop

/-- The function `exp(x)/x^n` tends to `+∞` at `+∞`, for any natural number `n` -/
/-
**Real.tendsto_exp_div_pow_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_exp_div_pow_atTop (n : Nat) : Tendsto (fun x => exp x / x ^ n) atT
op atTop
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用引理 `Filter.atTop_basis_Ioi`：atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@
atTop α _).HasBasis (fun _ => True) Ioi
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.atTop_basis'`：atTop_basis' (a : α) : atTop.HasBasis (a <= ·) Ici
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `tendsto_pow_const_div_const_pow_of_one_lt`：tendsto_pow_const_div_const_p
ow_of_one_lt (k : Nat) {r : Real} (hr : 1 < r) : Tendsto (fun n => (n : Real) ^ 
k / r ^ n : Nat -> Real) atTop …
· 使用定理 `Real.one_lt_exp_iff`：one_lt_exp_iff {x : Real} : 1 < exp x ↔ 0 < x
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `trivial`：True
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
The function `exp(x)/x^n` tends to `+∞` at `+∞`, for any natural number `n`
-/
theorem tendsto_exp_div_pow_atTop (n : ℕ) : Tendsto (fun x => exp x / x ^ n) atTop atTop := by
  refine (atTop_basis_Ioi.tendsto_iff (atTop_basis' 1)).2 fun C hC₁ => ?_
  have hC₀ : 0 < C := zero_lt_one.trans_le hC₁
  have : 0 < (exp 1 * C)⁻¹ := inv_pos.2 (mul_pos (exp_pos _) hC₀)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ≥ N, (↑k : ℝ) ^ n / exp 1 ^ k < (exp 1 * C)⁻¹ :=
    eventually_atTop.1
      ((tendsto_pow_const_div_const_pow_of_one_lt n (one_lt_exp_iff.2 zero_lt_one)).eventually
        (gt_mem_nhds this))
  simp only [← exp_nat_mul, mul_one, div_lt_iff₀, exp_pos, ← div_eq_inv_mul] at hN
  refine ⟨N, trivial, fun x hx => ?_⟩
  rw [Set.mem_Ioi] at hx
  have hx₀ : 0 < x := (Nat.cast_nonneg N).trans_lt hx
  rw [Set.mem_Ici, le_div_iff₀ (pow_pos hx₀ _), ← le_div_iff₀' hC₀]
  calc
    x ^ n ≤ ⌈x⌉₊ ^ n := by gcongr; exact Nat.le_ceil _
    _ ≤ exp ⌈x⌉₊ / (exp 1 * C) := mod_cast (hN _ (Nat.lt_ceil.2 hx).le).le
    _ ≤ exp (x + 1) / (exp 1 * C) := by gcongr; exact (Nat.ceil_lt_add_one hx₀.le).le
    _ = exp x / C := by rw [add_comm, exp_add, mul_div_mul_left _ _ (exp_pos _).ne']

/-- The function `x^n * exp(-x)` tends to `0` at `+∞`, for any natural number `n`. -/
/-
**Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_pow_mul_exp_neg_atTop_nhds_zero (n : Nat) : Tendsto (fun x => x ^ 
n * exp (-x)) atTop (𝓝 0)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用定理 `div_div_eq_mul_div`：div_div_eq_mul_div : a / (b / c) = a * c / b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.tendsto_exp_div_pow_atTop`：tendsto_exp_div_pow_atTop (n : Nat) : Te
ndsto (fun x => exp x / x ^ n) atTop atTop

--- 原说明 ---
The function `x^n * exp(-x)` tends to `0` at `+∞`, for any natural number `n`.
-/
theorem tendsto_pow_mul_exp_neg_atTop_nhds_zero (n : ℕ) :
    Tendsto (fun x => x ^ n * exp (-x)) atTop (𝓝 0) :=
  (tendsto_inv_atTop_zero.comp (tendsto_exp_div_pow_atTop n)).congr fun x => by
    rw [comp_apply, inv_eq_one_div, div_div_eq_mul_div, one_mul, div_eq_mul_inv, exp_neg]

/-- The function `(b * exp x + c) / (x ^ n)` tends to `+∞` at `+∞`, for any natural number
`n` and any real numbers `b` and `c` such that `b` is positive. -/
/-
**Real.tendsto_mul_exp_add_div_pow_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_mul_exp_add_div_pow_atTop (b c : Real) (n : Nat) (hb : 0 < b) : Te
ndsto (fun x => (b * exp x + c) / x ^ n) atTop atTop
参数：b c : Real；n : Nat；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Filter.Tendsto.atTop_add`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : AddCommGroup α] [inst_2 : LinearOrder α]   [IsOrderedAdd
Monoid α] [Ord…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Real.tendsto_exp_atTop`：tendsto_exp_atTop : Tendsto exp atTop atTop
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `Real.tendsto_exp_div_pow_atTop`：tendsto_exp_div_pow_atTop (n : Nat) : Te
ndsto (fun x => exp x / x ^ n) atTop atTop
· 使用定理 `Filter.Tendsto.div_atTop`：Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto 
f l (𝓝 a)) (hg : Tendsto g l atTop) : Tendsto (fun x => f x / g x) l (𝓝 0)
· 使用定理 `Filter.tendsto_pow_atTop`：tendsto_pow_atTop {n : Nat} (hn : n != 0) : Te
ndsto (fun x : α => x ^ n) atTop atTop

--- 原说明 ---
The function `(b * exp x + c) / (x ^ n)` tends to `+∞` at `+∞`, for any natural 
number
`n` and any real numbers `b` and `c` such that `b` is positive.
-/
theorem tendsto_mul_exp_add_div_pow_atTop (b c : ℝ) (n : ℕ) (hb : 0 < b) :
    Tendsto (fun x => (b * exp x + c) / x ^ n) atTop atTop := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp only [pow_zero, div_one]
    exact (tendsto_exp_atTop.const_mul_atTop hb).atTop_add tendsto_const_nhds
  simp only [add_div, mul_div_assoc]
  exact
    ((tendsto_exp_div_pow_atTop n).const_mul_atTop hb).atTop_add
      (tendsto_const_nhds.div_atTop (tendsto_pow_atTop hn))

/-- The function `(x ^ n) / (b * exp x + c)` tends to `0` at `+∞`, for any natural number
`n` and any real numbers `b` and `c` such that `b` is nonzero. -/
/-
**Real.tendsto_div_pow_mul_exp_add_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_div_pow_mul_exp_add_atTop (b c : Real) (n : Nat) (hb : 0 != b) : T
endsto (fun x => x ^ n / (b * exp x + c)) atTop (𝓝 0)
参数：b c : Real；n : Nat；hb : 0 != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Real.tendsto_mul_exp_add_div_pow_atTop`：tendsto_mul_exp_add_div_pow_atTo
p (b c : Real) (n : Nat) (hb : 0 < b) : Tendsto (fun x => (b * exp x + c) / x ^ 
n) atTop atTop
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
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
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
The function `(x ^ n) / (b * exp x + c)` tends to `0` at `+∞`, for any natural n
umber
`n` and any real numbers `b` and `c` such that `b` is nonzero.
-/
theorem tendsto_div_pow_mul_exp_add_atTop (b c : ℝ) (n : ℕ) (hb : 0 ≠ b) :
    Tendsto (fun x => x ^ n / (b * exp x + c)) atTop (𝓝 0) := by
  have H : ∀ d e, 0 < d → Tendsto (fun x : ℝ => x ^ n / (d * exp x + e)) atTop (𝓝 0) := by
    intro b' c' h
    convert! (tendsto_mul_exp_add_div_pow_atTop b' c' n h).inv_tendsto_atTop using 1
    ext x
    simp
  rcases lt_or_gt_of_ne hb with h | h
  · exact H b c h
  · convert! (H (-b) (-c) (neg_pos.mpr h)).neg using 1
    · ext x
      field_simp
      rw [← neg_add (b * exp x) c, div_neg, neg_neg]
    · rw [neg_zero]

/-- `Real.exp` as an order isomorphism between `ℝ` and `(0, +∞)`. -/
/-
**Real.expOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：expOrderIso : Real ≃o Ioi (0 : Real)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Real.exp` as an order isomorphism between `ℝ` and `(0, +∞)`.
-/
def expOrderIso : ℝ ≃o Ioi (0 : ℝ) :=
  StrictMono.orderIsoOfSurjective _
    (exp_strictMono.codRestrict fun x ↦ Set.mem_Ioi.mpr (exp_pos x)) <|
    (continuous_exp.subtype_mk _).surjective
      (by rw [tendsto_Ioi_atTop]; simp only [tendsto_exp_atTop])
      (by simp [tendsto_exp_atBot_nhdsGT])

@[simp]
/-
**Real.coe_expOrderIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：coe_expOrderIso_apply (x : Real) : (expOrderIso x : Real) = exp x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_expOrderIso_apply (x : ℝ) : (expOrderIso x : ℝ) = exp x :=
  rfl

@[simp]
/-
**Real.coe_comp_expOrderIso** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：coe_comp_expOrderIso : (↑) ∘ expOrderIso = exp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp_expOrderIso : (↑) ∘ expOrderIso = exp :=
  rfl

@[simp]
/-
**Real.range_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：range_exp : range exp = Set.Ioi 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.coe_comp_expOrderIso`：coe_comp_expOrderIso : (↑) ∘ expOrderIso = ex
p
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `OrderIso.range_eq`：range_eq (e : α ≃o β) : Set.range e = Set.univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem range_exp : range exp = Set.Ioi 0 := by
  rw [← coe_comp_expOrderIso, range_comp, expOrderIso.range_eq, image_univ, Subtype.range_coe]

@[simp]
/-
**Real.image_exp_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_exp_Ioi (a : Real) : exp '' Ioi a = Ioi (exp a)
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_Ioi_of_strictMonoOn`：ContinuousOn.image_Ioi_of_strict
MonoOn (hf : ContinuousOn f (Ici a)) (hmono : StrictMonoOn f (Ici a)) (htop : Te
ndsto f atTop atTop) : f '' …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
· 使用定理 `Real.exp_strictMono`：exp_strictMono : StrictMono exp
· 使用定理 `Real.tendsto_exp_atTop`：tendsto_exp_atTop : Tendsto exp atTop atTop
-/
theorem image_exp_Ioi (a : ℝ) : exp '' Ioi a = Ioi (exp a) :=
  continuous_exp.continuousOn.image_Ioi_of_strictMonoOn (exp_strictMono.strictMonoOn _)
    tendsto_exp_atTop

@[simp]
/-
**Real.image_exp_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_exp_Ici (a : Real) : exp '' Ici a = Ici (exp a)
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_Ici_of_monotoneOn`：ContinuousOn.image_Ici_of_monotone
On (hf : ContinuousOn f (Ici a)) (hmono : MonotoneOn f (Ici a)) (htop : Tendsto 
f atTop atTop) : f '' Ici …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Real.exp_strictMono`：exp_strictMono : StrictMono exp
· 使用定理 `Real.tendsto_exp_atTop`：tendsto_exp_atTop : Tendsto exp atTop atTop
-/
theorem image_exp_Ici (a : ℝ) : exp '' Ici a = Ici (exp a) :=
  continuous_exp.continuousOn.image_Ici_of_monotoneOn (exp_strictMono.monotone.monotoneOn _)
    tendsto_exp_atTop

@[simp]
/-
**Real.image_exp_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_exp_Icc (a b : Real) : exp '' Icc a b = Icc (exp a) (exp b)
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.image_Icc_of_strictMono`：Continuous.image_Icc_of_strictMono (
hf_c : Continuous f) (hf : StrictMono f) : f '' Icc a b = Icc (f a) (f b)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `Real.exp_strictMono`：exp_strictMono : StrictMono exp
-/
theorem image_exp_Icc (a b : ℝ) : exp '' Icc a b = Icc (exp a) (exp b) :=
  continuous_exp.image_Icc_of_strictMono exp_strictMono

@[simp]
/-
**Real.image_exp_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_exp_Ico (a b : Real) : exp '' Ico a b = Ico (exp a) (exp b)
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.image_Ico_of_strictMono`：Continuous.image_Ico_of_strictMono (
hf_c : Continuous f) (hf : StrictMono f) : f '' Ico a b = Ico (f a) (f b)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `Real.exp_strictMono`：exp_strictMono : StrictMono exp
-/
theorem image_exp_Ico (a b : ℝ) : exp '' Ico a b = Ico (exp a) (exp b) :=
  continuous_exp.image_Ico_of_strictMono exp_strictMono

@[simp]
/-
**Real.image_exp_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_exp_Ioc (a b : Real) : exp '' Ioc a b = Ioc (exp a) (exp b)
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.image_Ioc_of_strictMono`：Continuous.image_Ioc_of_strictMono (
hf_c : Continuous f) (hf : StrictMono f) : f '' Ioc a b = Ioc (f a) (f b)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `Real.exp_strictMono`：exp_strictMono : StrictMono exp
-/
theorem image_exp_Ioc (a b : ℝ) : exp '' Ioc a b = Ioc (exp a) (exp b) :=
  continuous_exp.image_Ioc_of_strictMono exp_strictMono

@[simp]
/-
**Real.image_exp_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_exp_Ioo (a b : Real) : exp '' Ioo a b = Ioo (exp a) (exp b)
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.image_Ioo_of_strictMono`：Continuous.image_Ioo_of_strictMono (
hf_c : Continuous f) (hf : StrictMono f) : f '' Ioo a b = Ioo (f a) (f b)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `Real.exp_strictMono`：exp_strictMono : StrictMono exp
-/
theorem image_exp_Ioo (a b : ℝ) : exp '' Ioo a b = Ioo (exp a) (exp b) :=
  continuous_exp.image_Ioo_of_strictMono exp_strictMono

@[simp]
/-
**Real.image_exp_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_exp_uIcc (a b : Real) : exp '' uIcc a b = uIcc (exp a) (exp b)
参数：a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_uIcc_of_monotoneOn`：ContinuousOn.image_uIcc_of_monoto
neOn (hf : ContinuousOn f [[a, b]]) (hmono : MonotoneOn f [[a, b]]) : f '' [[a, 
b]] = [[f a, f b]]
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Real.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Real.exp_strictMono`：exp_strictMono : StrictMono exp
-/
theorem image_exp_uIcc (a b : ℝ) : exp '' uIcc a b = uIcc (exp a) (exp b) :=
  continuous_exp.continuousOn.image_uIcc_of_monotoneOn (exp_strictMono.monotone.monotoneOn _)

@[simp]
/-
**Real.image_exp_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_exp_Iio (a : Real) : exp '' Iio a = Ioo 0 (exp a)
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.coe_comp_expOrderIso`：coe_comp_expOrderIso : (↑) ∘ expOrderIso = ex
p
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `OrderIso.image_Iio`：image_Iio (e : α ≃o β) (a : α) : e '' Iio a = Iio (e
 a)
· 使用引理 `Set.image_subtype_val_Ioi_Iio`：image_subtype_val_Ioi_Iio {a : α} (b : Io
i a) : Subtype.val '' Iio b = Ioo a b
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem image_exp_Iio (a : ℝ) : exp '' Iio a = Ioo 0 (exp a) := by
  rw [← coe_comp_expOrderIso, image_comp, expOrderIso.image_Iio, image_subtype_val_Ioi_Iio,
    Function.comp_apply]

@[simp]
/-
**Real.image_exp_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：image_exp_Iic (a : Real) : exp '' Iic a = Ioc 0 (exp a)
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.coe_comp_expOrderIso`：coe_comp_expOrderIso : (↑) ∘ expOrderIso = ex
p
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `OrderIso.image_Iic`：image_Iic (e : α ≃o β) (a : α) : e '' Iic a = Iic (e
 a)
· 使用引理 `Set.image_subtype_val_Ioi_Iic`：image_subtype_val_Ioi_Iic {a : α} (b : Io
i a) : Subtype.val '' Iic b = Ioc a b
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem image_exp_Iic (a : ℝ) : exp '' Iic a = Ioc 0 (exp a) := by
  rw [← coe_comp_expOrderIso, image_comp, expOrderIso.image_Iic, image_subtype_val_Ioi_Iic,
    Function.comp_apply]

@[simp]
/-
**Real.map_exp_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：map_exp_atTop : map exp atTop = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.coe_comp_expOrderIso`：coe_comp_expOrderIso : (↑) ∘ expOrderIso = ex
p
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `OrderIso.map_atTop`：map_atTop (e : α ≃o β) : map (e : α -> β) atTop = at
Top
· 使用定理 `Filter.map_val_Ioi_atTop`：map_val_Ioi_atTop [Preorder α] [IsDirectedOrde
r α] [NoMaxOrder α] (a : α) : map ((↑) : Ioi a -> α) atTop = atTop
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
theorem map_exp_atTop : map exp atTop = atTop := by
  rw [← coe_comp_expOrderIso, ← Filter.map_map, OrderIso.map_atTop, map_val_Ioi_atTop]

@[simp]
/-
**Real.comap_exp_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：comap_exp_atTop : comap exp atTop = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.map_exp_atTop`：map_exp_atTop : map exp atTop = atTop
· 使用定理 `Filter.comap_map`：comap_map {f : Filter α} {m : α -> β} (h : Injective m
) : comap m (map m f) = f
· 使用定理 `Real.exp_injective`：exp_injective : Function.Injective exp
-/
theorem comap_exp_atTop : comap exp atTop = atTop := by
  rw [← map_exp_atTop, comap_map exp_injective, map_exp_atTop]

@[simp]
/-
**Real.tendsto_exp_comp_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_exp_comp_atTop {f : α -> Real} : Tendsto (fun x => exp (f x)) l at
Top ↔ Tendsto f l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.comap_exp_atTop`：comap_exp_atTop : comap exp atTop = atTop
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_exp_comp_atTop {f : α → ℝ} :
    Tendsto (fun x => exp (f x)) l atTop ↔ Tendsto f l atTop := by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_atTop]
/-
**Real.tendsto_comp_exp_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_comp_exp_atTop {f : Real -> α} : Tendsto (fun x => f (exp x)) atTo
p l ↔ Tendsto f atTop l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.map_exp_atTop`：map_exp_atTop : map exp atTop = atTop
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_comp_exp_atTop {f : ℝ → α} :
    Tendsto (fun x => f (exp x)) atTop l ↔ Tendsto f atTop l := by
  simp_rw [← comp_apply (g := exp), ← tendsto_map'_iff, map_exp_atTop]

@[simp]
/-
**Real.map_exp_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：map_exp_atBot : map exp atBot = 𝓝[>] 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.coe_comp_expOrderIso`：coe_comp_expOrderIso : (↑) ∘ expOrderIso = ex
p
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `OrderIso.map_atBot`：map_atBot (e : α ≃o β) : map (e : α -> β) atBot = at
Bot
· 使用定理 `map_coe_Ioi_atBot`：map_coe_Ioi_atBot (a : X) (ha : IsPredPrelimit a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Order.IsPredPrelimit.of_dense`：∀ {α : Type u_1} [inst : LT α] [DenselyOr
dered α] (a : α), Order.IsPredPrelimit a
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem map_exp_atBot : map exp atBot = 𝓝[>] 0 := by
  rw [← coe_comp_expOrderIso, ← Filter.map_map, expOrderIso.map_atBot, ← map_coe_Ioi_atBot]

@[simp]
/-
**Real.comap_exp_nhdsGT_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：comap_exp_nhdsGT_zero : comap exp (𝓝[>] 0) = atBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.map_exp_atBot`：map_exp_atBot : map exp atBot = 𝓝[>] 0
· 使用定理 `Filter.comap_map`：comap_map {f : Filter α} {m : α -> β} (h : Injective m
) : comap m (map m f) = f
· 使用定理 `Real.exp_injective`：exp_injective : Function.Injective exp
-/
theorem comap_exp_nhdsGT_zero : comap exp (𝓝[>] 0) = atBot := by
  rw [← map_exp_atBot, comap_map exp_injective]
/-
**Real.tendsto_comp_exp_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_comp_exp_atBot {f : Real -> α} : Tendsto (fun x => f (exp x)) atBo
t l ↔ Tendsto f (𝓝[>] 0) l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.map_exp_atBot`：map_exp_atBot : map exp atBot = 𝓝[>] 0
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_comp_exp_atBot {f : ℝ → α} :
    Tendsto (fun x => f (exp x)) atBot l ↔ Tendsto f (𝓝[>] 0) l := by
  rw [← map_exp_atBot, tendsto_map'_iff]
  rfl

@[simp]
/-
**Real.comap_exp_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：comap_exp_nhds_zero : comap exp (𝓝 0) = atBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_nhdsWithin_range`：∀ {α : Type u_5} {β : Type u_6} [inst : Topologi
calSpace β] (f : α → β) (y : β),   Filter.comap f (nhdsWithin y (Set.range f)) =
 Filter.coma…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.range_exp`：range_exp : range exp = Set.Ioi 0
· 使用定理 `Real.comap_exp_nhdsGT_zero`：comap_exp_nhdsGT_zero : comap exp (𝓝[>] 0) =
 atBot
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_exp_nhds_zero : comap exp (𝓝 0) = atBot :=
  (comap_nhdsWithin_range exp 0).symm.trans <| by simp

@[simp]
/-
**Real.tendsto_exp_comp_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_exp_comp_nhds_zero {f : α -> Real} : Tendsto (fun x => exp (f x)) 
l (𝓝 0) ↔ Tendsto f l atBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.comap_exp_nhds_zero`：comap_exp_nhds_zero : comap exp (𝓝 0) = atBot
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_exp_comp_nhds_zero {f : α → ℝ} :
    Tendsto (fun x => exp (f x)) l (𝓝 0) ↔ Tendsto f l atBot := by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_nhds_zero]

@[fun_prop]
/-
**Real.isOpenEmbedding_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isOpenEmbedding_exp : IsOpenEmbedding exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type
 u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologica
lSpace Y] [inst_2 :…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
-/
theorem isOpenEmbedding_exp : IsOpenEmbedding exp :=
  isOpen_Ioi.isOpenEmbedding_subtypeVal.comp expOrderIso.toHomeomorph.isOpenEmbedding

@[simp]
/-
**Real.map_exp_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：map_exp_nhds (x : Real) : map exp (𝓝 x) = 𝓝 (exp x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `Real.isOpenEmbedding_exp`：isOpenEmbedding_exp : IsOpenEmbedding exp
-/
theorem map_exp_nhds (x : ℝ) : map exp (𝓝 x) = 𝓝 (exp x) :=
  isOpenEmbedding_exp.map_nhds_eq x

@[simp]
/-
**Real.comap_exp_nhds_exp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：comap_exp_nhds_exp (x : Real) : comap exp (𝓝 (exp x)) = 𝓝 x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `Real.isOpenEmbedding_exp`：isOpenEmbedding_exp : IsOpenEmbedding exp
-/
theorem comap_exp_nhds_exp (x : ℝ) : comap exp (𝓝 (exp x)) = 𝓝 x :=
  (isOpenEmbedding_exp.nhds_eq_comap x).symm
/-
**Real.isLittleO_pow_exp_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isLittleO_pow_exp_atTop {n : Nat} : (fun x : Real => x ^ n) =o[atTop] Real
.exp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_iff_tendsto`：isLittleO_iff_tendsto {f g : α -> 𝕜} 
(hgf : forall x, g x = 0 -> f x = 0) : f =o[l] g ↔ Tendsto (fun x => f x / g x) 
l (𝓝 0)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Real.tendsto_div_pow_mul_exp_add_atTop`：tendsto_div_pow_mul_exp_add_atTo
p (b c : Real) (n : Nat) (hb : 0 != b) : Tendsto (fun x => x ^ n / (b * exp x + 
c)) atTop (𝓝 0)
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem isLittleO_pow_exp_atTop {n : ℕ} : (fun x : ℝ => x ^ n) =o[atTop] Real.exp := by
  simpa [isLittleO_iff_tendsto fun x hx => ((exp_pos x).ne' hx).elim] using
    tendsto_div_pow_mul_exp_add_atTop 1 0 n zero_ne_one

@[simp]
/-
**Real.isBigO_exp_comp_exp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isBigO_exp_comp_exp_comp {f g : α -> Real} : ((fun x => exp (f x)) =O[l] f
un x => exp (g x)) ↔ IsBoundedUnder (· <= ·) l (f - g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isBigO_iff_isBoundedUnder_le_div`：isBigO_iff_isBoundedUnder_
le_div (h : forallᶠ x in l, g'' x != 0) : f =O[l] g'' ↔ IsBoundedUnder (· <= ·) 
l fun x => ‖f x‖ / ‖g'' x‖
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Real.exp_ne_zero`：∀ (x : ℝ), Real.exp x ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.abs_exp`：abs_exp (x : Real) : |exp x| = exp x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigO_exp_comp_exp_comp {f g : α → ℝ} :
    ((fun x => exp (f x)) =O[l] fun x => exp (g x)) ↔ IsBoundedUnder (· ≤ ·) l (f - g) :=
  Iff.trans (isBigO_iff_isBoundedUnder_le_div <| Eventually.of_forall fun _ => exp_ne_zero _) <| by
    simp only [norm_eq_abs, abs_exp, ← exp_sub, isBoundedUnder_le_exp_comp, Pi.sub_def]

@[simp]
/-
**Real.isTheta_exp_comp_exp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isTheta_exp_comp_exp_comp {f g : α -> Real} : ((fun x => exp (f x)) =Θ[l] 
fun x => exp (g x)) ↔ IsBoundedUnder (· <= ·) l fun x => |f x - g x|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isTheta_exp_comp_exp_comp {f g : α → ℝ} :
    ((fun x => exp (f x)) =Θ[l] fun x => exp (g x)) ↔
      IsBoundedUnder (· ≤ ·) l fun x => |f x - g x| := by
  simp only [isBoundedUnder_le_abs, ← isBoundedUnder_le_neg, neg_sub, IsTheta,
    isBigO_exp_comp_exp_comp, Pi.sub_def]

@[simp]
/-
**Real.isLittleO_exp_comp_exp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isLittleO_exp_comp_exp_comp {f g : α -> Real} : ((fun x => exp (f x)) =o[l
] fun x => exp (g x)) ↔ Tendsto (fun x => g x - f x) l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLittleO_exp_comp_exp_comp {f g : α → ℝ} :
    ((fun x => exp (f x)) =o[l] fun x => exp (g x)) ↔ Tendsto (fun x => g x - f x) l atTop := by
  simp only [isLittleO_iff_tendsto, exp_ne_zero, ← exp_sub, ← tendsto_neg_atTop_iff, false_imp_iff,
    imp_true_iff, tendsto_exp_comp_nhds_zero, neg_sub]
/-
**Real.isLittleO_one_exp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isLittleO_one_exp_comp {f : α -> Real} : ((fun _ => 1 : α -> Real) =o[l] f
un x => exp (f x)) ↔ Tendsto f l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLittleO_one_exp_comp {f : α → ℝ} :
    ((fun _ => 1 : α → ℝ) =o[l] fun x => exp (f x)) ↔ Tendsto f l atTop := by
  simp only [← exp_zero, isLittleO_exp_comp_exp_comp, sub_zero]

/-- `Real.exp (f x)` is bounded away from zero along a filter if and only if this filter is bounded
from below under `f`. -/
@[simp]
/-
**Real.isBigO_one_exp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isBigO_one_exp_comp {f : α -> Real} : ((fun _ => 1 : α -> Real) =O[l] fun 
x => exp (f x)) ↔ IsBoundedUnder (· >= ·) l f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`Real.exp (f x)` is bounded away from zero along a filter if and only if this fi
lter is bounded
from below under `f`.
-/
theorem isBigO_one_exp_comp {f : α → ℝ} :
    ((fun _ => 1 : α → ℝ) =O[l] fun x => exp (f x)) ↔ IsBoundedUnder (· ≥ ·) l f := by
  simp only [← exp_zero, isBigO_exp_comp_exp_comp, Pi.sub_def, zero_sub, isBoundedUnder_le_neg]

/-- `Real.exp (f x)` is bounded away from zero along a filter if and only if this filter is bounded
from below under `f`. -/
/-
**Real.isBigO_exp_comp_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isBigO_exp_comp_one {f : α -> Real} : (fun x => exp (f x)) =O[l] (fun _ =>
 1 : α -> Real) ↔ IsBoundedUnder (· <= ·) l f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.abs_exp`：abs_exp (x : Real) : |exp x| = exp x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`Real.exp (f x)` is bounded away from zero along a filter if and only if this fi
lter is bounded
from below under `f`.
-/
theorem isBigO_exp_comp_one {f : α → ℝ} :
    (fun x => exp (f x)) =O[l] (fun _ => 1 : α → ℝ) ↔ IsBoundedUnder (· ≤ ·) l f := by
  simp only [isBigO_one_iff, norm_eq_abs, abs_exp, isBoundedUnder_le_exp_comp]

/-- `Real.exp (f x)` is bounded away from zero and infinity along a filter `l` if and only if
`|f x|` is bounded from above along this filter. -/
@[simp]
/-
**Real.isTheta_exp_comp_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：isTheta_exp_comp_one {f : α -> Real} : (fun x => exp (f x)) =Θ[l] (fun _ =
> 1 : α -> Real) ↔ IsBoundedUnder (· <= ·) l fun x => |f x|
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`Real.exp (f x)` is bounded away from zero and infinity along a filter `l` if an
d only if
`|f x|` is bounded from above along this filter.
-/
theorem isTheta_exp_comp_one {f : α → ℝ} :
    (fun x => exp (f x)) =Θ[l] (fun _ => 1 : α → ℝ) ↔ IsBoundedUnder (· ≤ ·) l fun x => |f x| := by
  simp only [← exp_zero, isTheta_exp_comp_exp_comp, sub_zero]
/-
**Real.summable_exp_nat_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：summable_exp_nat_mul_iff {a : Real} : Summable (fun n : Nat => exp (n * a)
) ↔ a < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.exp_nat_mul`：∀ (x : ℝ) (n : ℕ), Real.exp (↑n * x) = Real.exp x ^ n
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用引理 `Real.exp_nonneg`：exp_nonneg (x : Real) : 0 <= exp x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma summable_exp_nat_mul_iff {a : ℝ} :
    Summable (fun n : ℕ ↦ exp (n * a)) ↔ a < 0 := by
  simp only [exp_nat_mul, summable_geometric_iff_norm_lt_one, norm_of_nonneg (exp_nonneg _),
    exp_lt_one_iff]
/-
**Real.summable_exp_neg_nat** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：summable_exp_neg_nat : Summable fun n : Nat => exp (-n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_neg_one`：mul_neg_one (a : α) : a * -1 = -a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Real.summable_exp_nat_mul_iff`：summable_exp_nat_mul_iff {a : Real} : Sum
mable (fun n : Nat => exp (n * a)) ↔ a < 0
· 使用引理 `neg_one_lt_zero`：neg_one_lt_zero [ZeroLEOneClass R] [NeZero (1 : R)] [Ad
dLeftStrictMono R] : -1 < (0 : R)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma summable_exp_neg_nat : Summable fun n : ℕ ↦ exp (-n) := by
  simpa only [mul_neg_one] using summable_exp_nat_mul_iff.mpr neg_one_lt_zero
/-
**Real.summable_exp_nat_mul_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：summable_exp_nat_mul_of_ge {c : Real} (hc : c < 0) {f : Nat -> Real} (hf :
 forall i, i <= f i) : Summable fun i : Nat => exp (c * f i)
参数：hc : c < 0；hf : forall i, i <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_le_mul_of_nonpos_left`：mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [
PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0) 
: c * a <= c * …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Real.summable_exp_nat_mul_iff`：summable_exp_nat_mul_iff {a : Real} : Sum
mable (fun n : Nat => exp (n * a)) ↔ a < 0
-/
lemma summable_exp_nat_mul_of_ge {c : ℝ} (hc : c < 0) {f : ℕ → ℝ} (hf : ∀ i, i ≤ f i) :
    Summable fun i : ℕ ↦ exp (c * f i) := by
  refine (Real.summable_exp_nat_mul_iff.mpr hc).of_nonneg_of_le (fun _ ↦ by positivity) fun i ↦ ?_
  refine Real.exp_monotone ?_
  conv_rhs => rw [mul_comm]
  exact mul_le_mul_of_nonpos_left (hf i) hc.le
/-
**Real.summable_pow_mul_exp_neg_nat_mul** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：summable_pow_mul_exp_neg_nat_mul (k : Nat) {r : Real} (hr : 0 < r) : Summa
ble fun n : Nat => n ^ k * exp (-r * n)
参数：k : Nat；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.exp_nat_mul`：∀ (x : ℝ) (n : ℕ), Real.exp (↑n * x) = Real.exp x ^ n
· 使用定理 `summable_pow_mul_geometric_of_norm_lt_one`：summable_pow_mul_geometric_of
_norm_lt_one (k : Nat) {r : R} (hr : ‖r‖ < 1) : Summable (fun n => (n : R) ^ k *
 r ^ n : Nat -> R)
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用引理 `Real.exp_nonneg`：exp_nonneg (x : Real) : 0 <= exp x
· 使用定理 `Real.exp_lt_one_iff`：exp_lt_one_iff {x : Real} : exp x < 1 ↔ x < 0
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma summable_pow_mul_exp_neg_nat_mul (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ ↦ n ^ k * exp (-r * n) := by
  simp_rw [mul_comm (-r), exp_nat_mul]
  apply summable_pow_mul_geometric_of_norm_lt_one
  rwa [norm_of_nonneg (exp_nonneg _), exp_lt_one_iff, neg_lt_zero]

end Real

open Real in
/-- If `f` has sum `a`, then `exp ∘ f` has product `exp a`. -/
/-
**HasSum.rexp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasSum.rexp {ι} {f : ι -> Real} {a : Real} (h : HasSum f a) : HasProd (rex
p ∘ f) (rexp a)
参数：h : HasSum f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Real.exp_sum`：exp_sum {α : Type*} (s : Finset α) (f : α -> Real) : exp (
∑ x in s, f x) = ∏ x in s, exp (f x)
· 使用定理 `Filter.Tendsto.rexp`：Filter.Tendsto.rexp {l : Filter α} {f : α -> Real} 
{z : Real} (hf : Tendsto f l (𝓝 z)) : Tendsto (fun x => exp (f x)) l (𝓝 (exp z))

--- 原说明 ---
If `f` has sum `a`, then `exp ∘ f` has product `exp a`.
-/
lemma HasSum.rexp {ι} {f : ι → ℝ} {a : ℝ} (h : HasSum f a) : HasProd (rexp ∘ f) (rexp a) :=
  Tendsto.congr (fun s ↦ exp_sum s f) <| Tendsto.rexp h

namespace Complex

@[simp]
/-
**Complex.comap_exp_cobounded** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：comap_exp_cobounded : comap exp (cobounded Complex) = comap re atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.comap_exp_atTop`：comap_exp_atTop : comap exp atTop = atTop
-/
theorem comap_exp_cobounded : comap exp (cobounded ℂ) = comap re atTop :=
  calc
    comap exp (cobounded ℂ) = comap re (comap Real.exp atTop) := by
      simp only [← comap_norm_atTop, comap_comap, comp_def, norm_exp]
    _ = comap re atTop := by rw [Real.comap_exp_atTop]

@[simp]
/-
**Complex.comap_exp_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：comap_exp_nhds_zero : comap exp (𝓝 0) = comap re atBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_norm_nhds_zero`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Fi
lter.comap norm (nhds 0) = nhds 0
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.comap_exp_nhds_zero`：comap_exp_nhds_zero : comap exp (𝓝 0) = atBot
-/
theorem comap_exp_nhds_zero : comap exp (𝓝 0) = comap re atBot :=
  calc
    comap exp (𝓝 0) = comap re (comap Real.exp (𝓝 0)) := by
      rw [← comap_norm_nhds_zero, comap_comap, Function.comp_def]
      simp_rw [norm_exp, comap_comap, Function.comp_def]
    _ = comap re atBot := by rw [Real.comap_exp_nhds_zero]
/-
**Complex.comap_exp_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：comap_exp_nhdsNE : comap exp (𝓝[!=] 0) = comap re atBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.comap_exp_nhds_zero`：comap_exp_nhds_zero : comap exp (𝓝 0) = com
ap re atBot
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_exp_nhdsNE : comap exp (𝓝[≠] 0) = comap re atBot := by
  have : (exp ⁻¹' {0})ᶜ = Set.univ := eq_univ_of_forall exp_ne_zero
  simp [nhdsWithin, comap_exp_nhds_zero, this]
/-
**Complex.tendsto_exp_nhds_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：tendsto_exp_nhds_zero_iff {α : Type*} {l : Filter α} {f : α -> Complex} : 
Tendsto (fun x => exp (f x)) l (𝓝 0) ↔ Tendsto (fun x => re (f x)) l atBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Complex.comap_exp_nhds_zero`：comap_exp_nhds_zero : comap exp (𝓝 0) = com
ap re atBot
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_exp_nhds_zero_iff {α : Type*} {l : Filter α} {f : α → ℂ} :
    Tendsto (fun x => exp (f x)) l (𝓝 0) ↔ Tendsto (fun x => re (f x)) l atBot := by
  simp_rw [← comp_apply (f := exp), ← tendsto_comap_iff, comap_exp_nhds_zero, tendsto_comap_iff]
  rfl

/-- `‖Complex.exp z‖ → ∞` as `Complex.re z → ∞`. -/
/-
**Complex.tendsto_exp_comap_re_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：tendsto_exp_comap_re_atTop : Tendsto exp (comap re atTop) (cobounded Compl
ex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `Complex.comap_exp_cobounded`：comap_exp_cobounded : comap exp (cobounded 
Complex) = comap re atTop

--- 原说明 ---
`‖Complex.exp z‖ → ∞` as `Complex.re z → ∞`.
-/
theorem tendsto_exp_comap_re_atTop : Tendsto exp (comap re atTop) (cobounded ℂ) :=
  comap_exp_cobounded ▸ tendsto_comap

/-- `Complex.exp z → 0` as `Complex.re z → -∞`. -/
/-
**Complex.tendsto_exp_comap_re_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：tendsto_exp_comap_re_atBot : Tendsto exp (comap re atBot) (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `Complex.comap_exp_nhds_zero`：comap_exp_nhds_zero : comap exp (𝓝 0) = com
ap re atBot

--- 原说明 ---
`Complex.exp z → 0` as `Complex.re z → -∞`.
-/
theorem tendsto_exp_comap_re_atBot : Tendsto exp (comap re atBot) (𝓝 0) :=
  comap_exp_nhds_zero ▸ tendsto_comap
/-
**Complex.tendsto_exp_comap_re_atBot_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：tendsto_exp_comap_re_atBot_nhdsNE : Tendsto exp (comap re atBot) (𝓝[!=] 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `Complex.comap_exp_nhdsNE`：comap_exp_nhdsNE : comap exp (𝓝[!=] 0) = comap
 re atBot
-/
theorem tendsto_exp_comap_re_atBot_nhdsNE : Tendsto exp (comap re atBot) (𝓝[≠] 0) :=
  comap_exp_nhdsNE ▸ tendsto_comap

end Complex

open Complex in
/-- If `f` has sum `a`, then `exp ∘ f` has product `exp a`. -/
/-
**HasSum.cexp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasSum.cexp {ι : Type*} {f : ι -> Complex} {a : Complex} (h : HasSum f a) 
: HasProd (cexp ∘ f) (cexp a)
参数：h : HasSum f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Complex.exp_sum`：exp_sum {α : Type*} (s : Finset α) (f : α -> Complex) :
 exp (∑ x in s, f x) = ∏ x in s, exp (f x)
· 使用定理 `Filter.Tendsto.cexp`：Filter.Tendsto.cexp {l : Filter α} {f : α -> Comple
x} {z : Complex} (hf : Tendsto f l (𝓝 z)) : Tendsto (fun x => exp (f x)) l (𝓝 (e
xp z))

--- 原说明 ---
If `f` has sum `a`, then `exp ∘ f` has product `exp a`.
-/
lemma HasSum.cexp {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasSum f a) : HasProd (cexp ∘ f) (cexp a) :=
  Filter.Tendsto.congr (fun s ↦ exp_sum s f) <| Filter.Tendsto.cexp h
