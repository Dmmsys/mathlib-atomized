/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Lemmas about `NormedSpace.exp` on `Quaternion`s

This file contains results about `NormedSpace.exp` on `Quaternion ℝ`.

## Main results

* `Quaternion.exp_eq`: the general expansion of the quaternion exponential in terms of `Real.cos`
  and `Real.sin`.
* `Quaternion.exp_of_re_eq_zero`: the special case when the quaternion has a zero real part.
* `Quaternion.norm_exp`: the norm of the quaternion exponential is the norm of the exponential of
  the real part.

-/

public section

open scoped Quaternion Nat

open NormedSpace

namespace Quaternion

@[simp, norm_cast]
/-
**Quaternion.exp_coe** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：exp_coe (r : Real) : exp (r : ℍ[Real]) = ↑(exp r)
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedSpace.map_exp`：map_exp [Algebra Rat 𝔹] {F} [FunLike F 𝔸 𝔹] [RingHo
mClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) : f (exp x) = exp (f x)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem exp_coe (r : ℝ) : exp (r : ℍ[ℝ]) = ↑(exp r) :=
  (map_exp (algebraMap ℝ ℍ[ℝ]) (continuous_algebraMap _ _) _).symm

/-- The even terms of `expSeries` are real, and correspond to the series for $\cos ‖q‖$. -/
/-
**Quaternion.expSeries_even_of_imaginary** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：expSeries_even_of_imaginary {q : Quaternion Real} (hq : q.re = 0) (n : Nat
) : expSeries Real (Quaternion Real) (2 * n) (fun _ => q) = ↑((-1 : Real) ^ n * 
‖q‖ ^ (2 * n) / (2 * n)!)
参数：hq : q.re = 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.expSeries_apply_eq`：expSeries_apply_eq (x : 𝔸) (n : Nat) : (
expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quaternion.sq_eq_neg_normSq`：sq_eq_neg_normSq : a ^ 2 = -normSq a ↔ a.re
 = 0
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `neg_pow`：neg_pow (a : R) (n : Nat) : (-a) ^ n = (-1) ^ n * a ^ n
· 使用定理 `Quaternion.normSq_eq_norm_mul_self`：normSq_eq_norm_mul_self (a : ℍ) : no
rmSq a = ‖a‖ * ‖a‖
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Quaternion.coe_mul`：coe_mul : ((x * y : R) : ℍ[R]) = x * y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quaternion.coe_pow`：coe_pow (n : Nat) : (↑(x ^ n) : ℍ[R]) = (x : ℍ[R]) ^
 n
· 使用定理 `Quaternion.coe_neg`：coe_neg : ((-x : R) : ℍ[R]) = -x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quaternion.coe_mul_eq_smul`：coe_mul_eq_smul : ↑r * a = r • a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
The even terms of `expSeries` are real, and correspond to the series for $\cos ‖
q‖$.
-/
theorem expSeries_even_of_imaginary {q : Quaternion ℝ} (hq : q.re = 0) (n : ℕ) :
    expSeries ℝ (Quaternion ℝ) (2 * n) (fun _ => q) =
      ↑((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n) / (2 * n)!) := by
  rw [expSeries_apply_eq]
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  let k : ℝ := ↑(2 * n)!
  calc
    k⁻¹ • q ^ (2 * n) = k⁻¹ • (-normSq q) ^ n := by rw [pow_mul, hq2]
    _ = k⁻¹ • ↑((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n)) := ?_
    _ = ↑((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n) / k) := ?_
  · congr 1
    rw [neg_pow, normSq_eq_norm_mul_self, pow_mul, sq]
    push_cast
    rfl
  · rw [← coe_mul_eq_smul, div_eq_mul_inv]
    norm_cast
    ring_nf

/-- The odd terms of `expSeries` are real, and correspond to the series for
$\frac{q}{‖q‖} \sin ‖q‖$. -/
/-
**Quaternion.expSeries_odd_of_imaginary** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：expSeries_odd_of_imaginary {q : Quaternion Real} (hq : q.re = 0) (n : Nat)
 : expSeries Real (Quaternion Real) (2 * n + 1) (fun _ => q) = (((-1 : Real) ^ n
 * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) / ‖q‖) • q
参数：hq : q.re = 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.expSeries_apply_eq`：expSeries_apply_eq (x : 𝔸) (n : Nat) : (
expSeries 𝕂 𝔸 n fun _ => x) = (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quaternion.sq_eq_neg_normSq`：sq_eq_neg_normSq : a ^ 2 = -normSq a ↔ a.re
 = 0
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `neg_pow`：neg_pow (a : R) (n : Nat) : (-a) ^ n = (-1) ^ n * a ^ n
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
The odd terms of `expSeries` are real, and correspond to the series for
$\frac{q}{‖q‖} \sin ‖q‖$.
-/
theorem expSeries_odd_of_imaginary {q : Quaternion ℝ} (hq : q.re = 0) (n : ℕ) :
    expSeries ℝ (Quaternion ℝ) (2 * n + 1) (fun _ => q) =
      (((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) / ‖q‖) • q := by
  rw [expSeries_apply_eq]
  obtain rfl | hq0 := eq_or_ne q 0
  · simp
  have hq2 : q ^ 2 = -normSq q := sq_eq_neg_normSq.mpr hq
  have hqn := norm_ne_zero_iff.mpr hq0
  let k : ℝ := ↑(2 * n + 1)!
  calc
    k⁻¹ • q ^ (2 * n + 1) = k⁻¹ • ((-normSq q) ^ n * q) := by rw [pow_succ, pow_mul, hq2]
    _ = k⁻¹ • ((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n)) • q := ?_
    _ = ((-1 : ℝ) ^ n * ‖q‖ ^ (2 * n + 1) / k / ‖q‖) • q := ?_
  · congr 1
    rw [neg_pow, normSq_eq_norm_mul_self, pow_mul, sq, ← coe_mul_eq_smul]
    norm_cast
  · rw [smul_smul]
    congr 1
    simp_rw [pow_succ, mul_div_assoc, div_div_cancel_left' hqn]
    ring

/-- Auxiliary result; if the power series corresponding to `Real.cos` and `Real.sin` evaluated
at `‖q‖` tend to `c` and `s`, then the exponential series tends to `c + (s / ‖q‖)`. -/
/-
**Quaternion.hasSum_expSeries_of_imaginary** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion
`。
形式化陈述：hasSum_expSeries_of_imaginary {q : Quaternion Real} (hq : q.re = 0) {c s :
 Real} (hc : HasSum (fun n => (-1 : Real) ^ n * ‖q‖ ^ (2 * n) / (2 * n)!) c) (hs
 : HasSum (fun n => (-1 : Real) ^ n * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) s) : Has
Sum (fun n => expSeries Real (Quaternion Real) n fun _ => q) (↑c + (s / ‖q‖) • q
)
参数：hq : q.re = 0；hc : HasSum (fun n => (-1 : Real) ^ n * ‖q‖ ^ (2 * n) / (2 * n)
!) c；hs : HasSum (fun n => (-1 : Real) ^ n * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quaternion.hasSum_coe`：hasSum_coe {f : α -> Real} {r : Real} : HasSum (f
un a => (f a : ℍ)) (↑r : ℍ) L ↔ HasSum f r L
· 使用定理 `HasSum.smul_const`：HasSum.smul_const {r : R} (hf : HasSum f r L) (a : M)
 : HasSum (fun z => f z • a) (r • a) L
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasSum.div_const`：HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (
fun i => f i / b) (a / b) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasSum.even_add_odd`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_1 :
 TopologicalSpace M] {m m' : M} [ContinuousAdd M] {f : ℕ → M},   HasSum (fun k =
> f (2 * …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.expSeries_even_of_imaginary`：expSeries_even_of_imaginary {q :
 Quaternion Real} (hq : q.re = 0) (n : Nat) : expSeries Real (Quaternion Real) (
2 * n) (fun _ => q) = ↑((-1 …
· 使用定理 `Quaternion.expSeries_odd_of_imaginary`：expSeries_odd_of_imaginary {q : Q
uaternion Real} (hq : q.re = 0) (n : Nat) : expSeries Real (Quaternion Real) (2 
* n + 1) (fun _ => q) = (((…

--- 原说明 ---
Auxiliary result; if the power series corresponding to `Real.cos` and `Real.sin`
 evaluated
at `‖q‖` tend to `c` and `s`, then the exponential series tends to `c + (s / ‖q‖
)`.
-/
theorem hasSum_expSeries_of_imaginary {q : Quaternion ℝ} (hq : q.re = 0) {c s : ℝ}
    (hc : HasSum (fun n => (-1 : ℝ) ^ n * ‖q‖ ^ (2 * n) / (2 * n)!) c)
    (hs : HasSum (fun n => (-1 : ℝ) ^ n * ‖q‖ ^ (2 * n + 1) / (2 * n + 1)!) s) :
    HasSum (fun n => expSeries ℝ (Quaternion ℝ) n fun _ => q) (↑c + (s / ‖q‖) • q) := by
  replace hc := hasSum_coe.mpr hc
  replace hs := (hs.div_const ‖q‖).smul_const q
  refine HasSum.even_add_odd ?_ ?_
  · convert! hc using 1
    ext n : 1
    rw [expSeries_even_of_imaginary hq]
  · convert! hs using 1
    ext n : 1
    rw [expSeries_odd_of_imaginary hq]

set_option backward.isDefEq.respectTransparency false in -- This is needed or we get errors in later declarations.
/-- The closed form for the quaternion exponential on imaginary quaternions. -/
/-
**Quaternion.exp_of_re_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：exp_of_re_eq_zero (q : Quaternion Real) (hq : q.re = 0) : exp q = ↑(Real.c
os ‖q‖) + (Real.sin ‖q‖ / ‖q‖) • q
参数：q : Quaternion Real；hq : q.re = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp_eq_tsum`：exp_eq_tsum [CharZero 𝕂] : exp = fun x : 𝔸 => ∑
' n : Nat, (n !⁻¹ : 𝕂) • x ^ n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quaternion.hasSum_expSeries_of_imaginary`：hasSum_expSeries_of_imaginary 
{q : Quaternion Real} (hq : q.re = 0) {c s : Real} (hc : HasSum (fun n => (-1 : 
Real) ^ n * ‖q‖ ^ (2 * n) / (2…
· 使用定理 `Real.hasSum_cos`：Real.hasSum_cos (r : Real) : HasSum (fun n : Nat => (-1
) ^ n * r ^ (2 * n) / ↑(2 * n)!) (Real.cos r)
· 使用定理 `Real.hasSum_sin`：Real.hasSum_sin (r : Real) : HasSum (fun n : Nat => (-1
) ^ n * r ^ (2 * n + 1) / ↑(2 * n + 1)!) (Real.sin r)

--- 原说明 ---
The closed form for the quaternion exponential on imaginary quaternions.
-/
theorem exp_of_re_eq_zero (q : Quaternion ℝ) (hq : q.re = 0) :
    exp q = ↑(Real.cos ‖q‖) + (Real.sin ‖q‖ / ‖q‖) • q := by
  rw [exp_eq_tsum ℝ]
  refine HasSum.tsum_eq ?_
  simp_rw [← expSeries_apply_eq]
  exact hasSum_expSeries_of_imaginary hq (Real.hasSum_cos _) (Real.hasSum_sin _)

set_option backward.isDefEq.respectTransparency false in -- This is needed or we get errors in later declarations.
/-- The closed form for the quaternion exponential on arbitrary quaternions. -/
/-
**Quaternion.exp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：exp_eq (q : Quaternion Real) : exp q = exp q.re • (↑(Real.cos ‖q.im‖) + (R
eal.sin ‖q.im‖ / ‖q.im‖) • q.im)
参数：q : Quaternion Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quaternion.exp_of_re_eq_zero`：exp_of_re_eq_zero (q : Quaternion Real) (h
q : q.re = 0) : exp q = ↑(Real.cos ‖q‖) + (Real.sin ‖q‖ / ‖q‖) • q
· 使用定理 `Quaternion.re_im`：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion R
), a.im.re = 0
· 使用定理 `Quaternion.coe_mul_eq_smul`：coe_mul_eq_smul : ↑r * a = r • a
· 使用定理 `Quaternion.exp_coe`：exp_coe (r : Real) : exp (r : ℍ[Real]) = ↑(exp r)
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedSpace.exp_add_of_commute`：exp_add_of_commute {x y : 𝔸} (hxy : Comm
ute x y) : exp (x + y) = exp x * exp y
· 使用定理 `Quaternion.instCompleteSpaceReal`：CompleteSpace (Quaternion ℝ)
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `Quaternion.re_add_im`：∀ {R : Type u_3} [inst : CommRing R] (a : Quaterni
on R), ↑a.re + a.im = a

--- 原说明 ---
The closed form for the quaternion exponential on arbitrary quaternions.
-/
theorem exp_eq (q : Quaternion ℝ) :
    exp q = exp q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
  let +nondep : NormedAlgebra ℚ ℍ := .restrictScalars ℚ ℝ ℍ
  rw [← exp_of_re_eq_zero q.im q.re_im, ← coe_mul_eq_smul, ← exp_coe, ← exp_add_of_commute,
    re_add_im]
  exact Algebra.commutes q.re (_ : ℍ[ℝ])
/-
**Quaternion.re_exp** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：re_exp (q : ℍ[Real]) : (exp q).re = exp q.re * Real.cos ‖q - q.re‖
参数：q : ℍ[Real]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.exp_eq`：exp_eq (q : Quaternion Real) : exp q = exp q.re • (↑(
Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Quaternion.sub_re_self`：∀ {R : Type u_3} [inst : CommRing R] (a : Quater
nion R), a - ↑a.re = a.im
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem re_exp (q : ℍ[ℝ]) : (exp q).re = exp q.re * Real.cos ‖q - q.re‖ := by simp [exp_eq]
/-
**Quaternion.im_exp** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：im_exp (q : ℍ[Real]) : (exp q).im = (exp q.re * (Real.sin ‖q.im‖ / ‖q.im‖)
) • q.im
参数：q : ℍ[Real]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.exp_eq`：exp_eq (q : Quaternion Real) : exp q = exp q.re • (↑(
Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Quaternion.im_add`：∀ {R : Type u_3} [inst : CommRing R] (a b : Quaternio
n R), (a + b).im = a.im + b.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Quaternion.im_smul`：im_smul [SMulZeroClass S R] (s : S) : (s • a).im = s
 • a.im
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem im_exp (q : ℍ[ℝ]) : (exp q).im = (exp q.re * (Real.sin ‖q.im‖ / ‖q.im‖)) • q.im := by
  simp [exp_eq, smul_smul]
/-
**Quaternion.normSq_exp** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：normSq_exp (q : ℍ[Real]) : normSq (exp q) = exp q.re ^ 2
参数：q : ℍ[Real]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quaternion.exp_eq`：exp_eq (q : Quaternion Real) : exp q = exp q.re • (↑(
Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im)
· 使用定理 `Quaternion.normSq_smul`：normSq_smul (r : R) (q : ℍ[R]) : normSq (r • q) 
= r ^ 2 * normSq q
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Quaternion.normSq_add`：normSq_add (a b : ℍ[R]) : normSq (a + b) = normSq
 a + normSq b + 2 * (a * star b).re
· 使用定理 `Quaternion.star_smul`：star_smul [Monoid S] [DistribMulAction S R] (s : S
) (a : ℍ[R]) : star (s • a) = s • star a
· 使用定理 `Quaternion.coe_mul_eq_smul`：coe_mul_eq_smul : ↑r * a = r • a
· 使用定理 `Quaternion.re_smul`：re_smul [SMul S R] (s : S) : (s • a).re = s • a.re
· 使用定理 `Quaternion.re_star`：∀ {R : Type u_3} [inst : CommRing R] (a : Quaternion
 R), (star a).re = a.re
（共 44 条，此处仅展示前 30 条）
-/
theorem normSq_exp (q : ℍ[ℝ]) : normSq (exp q) = exp q.re ^ 2 :=
  calc
    normSq (exp q) =
        normSq (exp q.re • (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im)) := by
      rw [exp_eq]
    _ = exp q.re ^ 2 * normSq (↑(Real.cos ‖q.im‖) + (Real.sin ‖q.im‖ / ‖q.im‖) • q.im) := by
      rw [normSq_smul]
    _ = exp q.re ^ 2 * (Real.cos ‖q.im‖ ^ 2 + Real.sin ‖q.im‖ ^ 2) := by
      congr 1
      obtain hv | hv := eq_or_ne ‖q.im‖ 0
      · simp [hv]
      rw [normSq_add, normSq_smul, star_smul, coe_mul_eq_smul, re_smul, re_smul, re_star, re_im,
        smul_zero, smul_zero, mul_zero, add_zero, div_pow, normSq_coe,
        normSq_eq_norm_mul_self, ← sq, div_mul_cancel₀ _ (pow_ne_zero _ hv)]
    _ = exp q.re ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]

/-- Note that this implies that exponentials of pure imaginary quaternions are unit quaternions
since in that case the RHS is `1` via `NormedSpace.exp_zero` and `norm_one`. -/
@[simp]
/-
**Quaternion.norm_exp** 是 Mathlib 中的一个定理，位于命名空间 `Quaternion`。
形式化陈述：norm_exp (q : ℍ[Real]) : ‖exp q‖ = ‖exp q.re‖
参数：q : ℍ[Real]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_sqrt_real_inner`：norm_eq_sqrt_real_inner (x : F) : ‖x‖ = √⟪x, x⟫
_Real
· 使用定理 `Quaternion.inner_self`：inner_self (a : ℍ) : ⟪a, a⟫ = normSq a
· 使用定理 `Quaternion.normSq_exp`：normSq_exp (q : ℍ[Real]) : normSq (exp q) = exp q
.re ^ 2
· 使用定理 `Real.sqrt_sq_eq_abs`：sqrt_sq_eq_abs (x : Real) : √(x ^ 2) = |x|
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|

--- 原说明 ---
Note that this implies that exponentials of pure imaginary quaternions are unit 
quaternions
since in that case the RHS is `1` via `NormedSpace.exp_zero` and `norm_one`.
-/
theorem norm_exp (q : ℍ[ℝ]) : ‖exp q‖ = ‖exp q.re‖ := by
  rw [norm_eq_sqrt_real_inner (exp q), inner_self, normSq_exp, Real.sqrt_sq_eq_abs,
    Real.norm_eq_abs]

end Quaternion

