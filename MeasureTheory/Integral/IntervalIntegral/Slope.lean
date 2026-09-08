/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Some properties of the interval integral of `fun x ↦ slope f x (x + c)`, given a constant `c : ℝ`

This file proves that:
* `IntervalIntegrable.intervalIntegrable_slope`: If `f` is interval integrable on `a..(b + c)`
  where `a ≤ b` and `0 ≤ c`, then `fun x ↦ slope f x (x + c)` is interval integrable on `a..b`.
* `MonotoneOn.intervalIntegrable_slope`: If `f` is monotone on `a..(b + c)`
  where `a ≤ b` and `0 ≤ c`, then `fun x ↦ slope f x (x + c)` is interval integrable on `a..b`.
* `MonotoneOn.intervalIntegral_slope_le`:  If `f` is monotone on `a..(b + c)`
  where `a ≤ b` and `0 ≤ c`, then the interval integral of `fun x ↦ slope f x (x + c)` on `a..b` is
  at most `f (b + c) - f a`.

## Tags
interval integrable, interval integral, monotone, slope
-/

public section

open MeasureTheory Set

/-- If `f` is interval integrable on `a..(b + c)` where `a ≤ b` and `0 ≤ c`, then
`fun x ↦ slope f x (x + c)` is interval integrable on `a..b`. -/
/-
**IntervalIntegrable.intervalIntegrable_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntervalIntegrable.intervalIntegrable_slope {f : Real -> Real} {a b c : Re
al} (hf : IntervalIntegrable f volume a (b + c)) (hab : a <= b) (hc : 0 <= c) : 
IntervalIntegrable (fun x => slope f x (x + c)) volume a b
参数：hf : IntervalIntegrable f volume a (b + c)；hab : a <= b；hc : 0 <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `IntervalIntegrable.const_mul`：const_mul {f : Real -> A} (hf : IntervalIn
tegrable f μ a b) (c : A) : IntervalIntegrable (fun x => c * f x) μ a b
· 使用定理 `IntervalIntegrable.sub`：sub {f g : Real -> E} (hf : IntervalIntegrable f
 μ a b) (hg : IntervalIntegrable g μ a b) : IntervalIntegrable (fun x => f x - g
 x) μ a b
· 使用定理 `IntervalIntegrable.mono_set`：mono_set (hf : IntervalIntegrable f μ a b) 
(h : [[c, d]] subseteq [[a, b]]) : IntervalIntegrable f μ c d
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IntervalIntegrable.comp_add_right`：comp_add_right (hf : IntervalIntegrab
le f volume a b) (c : Real) (h : ‖f (min a b)‖ₑ != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞

--- 原说明 ---
If `f` is interval integrable on `a..(b + c)` where `a ≤ b` and `0 ≤ c`, then
`fun x ↦ slope f x (x + c)` is interval integrable on `a..b`.
-/
theorem IntervalIntegrable.intervalIntegrable_slope {f : ℝ → ℝ} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a (b + c)) (hab : a ≤ b) (hc : 0 ≤ c) :
    IntervalIntegrable (fun x ↦ slope f x (x + c)) volume a b := by
  simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
  exact hf.comp_add_right c |>.mono_set (by grind [uIcc]) |>.sub (hf.mono_set (by grind [uIcc]))
    |>.const_mul (c := c⁻¹)

/-- If `f` is monotone on `a..(b + c)` where `a ≤ b` and `0 ≤ c`, then
`fun x ↦ slope f x (x + c)` is interval integrable on `a..b`. -/
/-
**MonotoneOn.intervalIntegrable_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.intervalIntegrable_slope {f : Real -> Real} {a b c : Real} (hf 
: MonotoneOn f (Icc a (b + c))) (hab : a <= b) (hc : 0 <= c) : IntervalIntegrabl
e (fun x => slope f x (x + c)) volume a b
参数：hf : MonotoneOn f (Icc a (b + c))；hab : a <= b；hc : 0 <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntervalIntegrable.intervalIntegrable_slope`：IntervalIntegrable.interval
Integrable_slope {f : Real -> Real} {a b c : Real} (hf : IntervalIntegrable f vo
lume a (b + c)) (hab : a <= b) (h…
· 使用定理 `MonotoneOn.intervalIntegrable`：MonotoneOn.intervalIntegrable {u : Real -
> E} {a b : Real} (hu : MonotoneOn u (uIcc a b)) : IntervalIntegrable u μ a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is monotone on `a..(b + c)` where `a ≤ b` and `0 ≤ c`, then
`fun x ↦ slope f x (x + c)` is interval integrable on `a..b`.
-/
theorem MonotoneOn.intervalIntegrable_slope {f : ℝ → ℝ} {a b c : ℝ}
    (hf : MonotoneOn f (Icc a (b + c))) (hab : a ≤ b) (hc : 0 ≤ c) :
    IntervalIntegrable (fun x ↦ slope f x (x + c)) volume a b :=
  uIcc_of_le (show a ≤ b + c by linarith) ▸ hf |>.intervalIntegrable.intervalIntegrable_slope hab hc

/-- If `f` is monotone on `a..(b + c)` where `a ≤ b` and `0 ≤ c`, then the interval integral of
`fun x ↦ slope f x (x + c)` on `a..b` is at most `f (b + c) - f a`. -/
/-
**MonotoneOn.intervalIntegral_slope_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.intervalIntegral_slope_le {f : Real -> Real} {a b c : Real} (hf
 : MonotoneOn f (Icc a (b + c))) (hab : a <= b) (hc : 0 <= c) : ∫ x in a..b, slo
pe f x (x + c) <= f (b + c) - f a
参数：hf : MonotoneOn f (Icc a (b + c))；hab : a <= b；hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `slope_same`：slope_same (f : k -> PE) (a : k) : (slope f a a : E) = 0
· 使用定理 `intervalIntegral.integral_zero`：integral_zero : (∫ _ in a..b, (0 : E) ∂μ
) = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MonotoneOn.intervalIntegrable`：MonotoneOn.intervalIntegrable {u : Real -
> E} {a b : Real} (hu : MonotoneOn u (uIcc a b)) : IntervalIntegrable u μ a b
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is monotone on `a..(b + c)` where `a ≤ b` and `0 ≤ c`, then the interval 
integral of
`fun x ↦ slope f x (x + c)` on `a..b` is at most `f (b + c) - f a`.
-/
theorem MonotoneOn.intervalIntegral_slope_le {f : ℝ → ℝ} {a b c : ℝ}
    (hf : MonotoneOn f (Icc a (b + c))) (hab : a ≤ b) (hc : 0 ≤ c) :
    ∫ x in a..b, slope f x (x + c) ≤ f (b + c) - f a := by
  rcases eq_or_lt_of_le hc with hc | hc
  · simp only [← hc, add_zero, slope_same, intervalIntegral.integral_zero, sub_nonneg]
    apply hf <;> grind
  rw [← uIcc_of_le (by linarith)] at hf
  have hf' := hf.intervalIntegrable (μ := volume)
  simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub
        (hf'.comp_add_right c |>.mono_set (by grind [uIcc]))
        (hf'.mono_set (by grind [uIcc])),
      intervalIntegral.integral_comp_add_right,
      intervalIntegral.integral_interval_sub_interval_comm'
        (hf'.mono_set (by grind [uIcc]))
        (hf'.mono_set (by grind [uIcc]))
        (hf'.mono_set (by grind [uIcc]))]
  have fU : ∫ (x : ℝ) in b..b + c, f x ≤ c * f (b + c) := by
    grw [intervalIntegral.integral_mono_on (g := fun _ ↦ f (b + c))
          (by linarith)
          (hf'.mono_set (by grind [uIcc]))
          (by simp)
          (by intros; apply hf <;> grind [uIcc])]
    simp
  have fL : c * f a ≤ ∫ (x : ℝ) in a..a + c, f x := by
    grw [← intervalIntegral.integral_mono_on (f := fun _ ↦ f a)
            (by linarith)
            (by simp)
            (hf'.mono_set (by grind [uIcc]))
            (by intros; apply hf <;> grind [uIcc])]
    simp
  grw [fU, ← fL]
  field_simp; rfl
