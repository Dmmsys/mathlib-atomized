/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Mean value inequalities for integrals

In this file we prove several inequalities on integrals, notably the Hölder inequality and
the Minkowski inequality. The versions for finite sums are in `Analysis.MeanInequalities`.

## Main results

Hölder's inequality for the Lebesgue integral of `ℝ≥0∞` and `ℝ≥0` functions: we prove
`∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q` conjugate real exponents
and `α → (E)NNReal` functions in two cases,
* `ENNReal.lintegral_mul_le_Lp_mul_Lq` : ℝ≥0∞ functions,
* `NNReal.lintegral_mul_le_Lp_mul_Lq`  : ℝ≥0 functions.

`ENNReal.lintegral_mul_norm_pow_le` is a variant where the exponents are not reciprocals:
`∫ (f ^ p * g ^ q) ∂μ ≤ (∫ f ∂μ) ^ p * (∫ g ∂μ) ^ q` where `p, q ≥ 0` and `p + q = 1`.
`ENNReal.lintegral_prod_norm_pow_le` generalizes this to a finite family of functions:
`∫ (∏ i, f i ^ p i) ∂μ ≤ ∏ i, (∫ f i ∂μ) ^ p i` when the `p` is a collection
of nonnegative weights with sum 1.

Minkowski's inequality for the Lebesgue integral of measurable functions with `ℝ≥0∞` values:
we prove `(∫ (f + g)^p ∂μ) ^ (1/p) ≤ (∫ f^p ∂μ) ^ (1/p) + (∫ g^p ∂μ) ^ (1/p)` for `1 ≤ p`.
-/

@[expose] public section


section LIntegral

/-!
### Hölder's inequality for the Lebesgue integral of ℝ≥0∞ and ℝ≥0 functions

We prove `∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q`
conjugate real exponents and `α → (E)NNReal` functions in several cases, the first two being useful
only to prove the more general results:
* `ENNReal.lintegral_mul_le_one_of_lintegral_rpow_eq_one` : ℝ≥0∞ functions for which the
    integrals on the right are equal to 1,
* `ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top` : ℝ≥0∞ functions for which the
    integrals on the right are neither ⊤ nor 0,
* `ENNReal.lintegral_mul_le_Lp_mul_Lq` : ℝ≥0∞ functions,
* `NNReal.lintegral_mul_le_Lp_mul_Lq`  : ℝ≥0 functions.
-/


noncomputable section

open NNReal ENNReal MeasureTheory Finset


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace ENNReal

/-
**ENNReal.lintegral_mul_le_one_of_lintegral_rpow_eq_one** 是 Mathlib 中的一个定理，位于命名空
间 `ENNReal`。
形式化陈述：lintegral_mul_le_one_of_lintegral_rpow_eq_one {p q : Real} (hpq : p.Holder
Conjugate q) {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf_norm : ∫⁻ a, f a 
^ p ∂μ = 1) (hg_norm : ∫⁻ a, g a ^ q ∂μ = 1) : (∫⁻ a, (f * g) a ∂μ) <= 1
参数：hpq : p.HolderConjugate q；hf : AEMeasurable f μ；hf_norm : ∫⁻ a, f a ^ p ∂μ = 
1；hg_norm : ∫⁻ a, g a ^ q ∂μ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `ENNReal.young_inequality`：young_inequality (a b : Real>=0∞) {p q : Real}
 (hpq : p.HolderConjugate q) : a * b <= a ^ p / ENNReal.ofReal p + b ^ q / ENNRe
al.ofReal q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MeasureTheory.lintegral_add_left'`：lintegral_add_left' {f : α -> Real>=0
∞} (hf : AEMeasurable f μ) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a 
∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `AEMeasurable.mul_const`：AEMeasurable.mul_const [MeasurableMul M] (hf : A
EMeasurable f μ) (c : M) : AEMeasurable (fun x => f x * c) μ
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `MeasureTheory.lintegral_mul_const''`：lintegral_mul_const'' (r : Real>=0∞
) {f : α -> Real>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ
) * r
· 使用定理 `MeasureTheory.lintegral_mul_const'`：lintegral_mul_const' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.HolderConjugate.inv_add_inv_ennreal`：inv_add_inv_ennreal : (ENNReal
.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1
-/
theorem lintegral_mul_le_one_of_lintegral_rpow_eq_one {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_norm : ∫⁻ a, f a ^ p ∂μ = 1)
    (hg_norm : ∫⁻ a, g a ^ q ∂μ = 1) : (∫⁻ a, (f * g) a ∂μ) ≤ 1 := by
  calc
    (∫⁻ a : α, (f * g) a ∂μ) ≤
        ∫⁻ a : α, f a ^ p / ENNReal.ofReal p + g a ^ q / ENNReal.ofReal q ∂μ :=
      lintegral_mono fun a => young_inequality (f a) (g a) hpq
    _ = 1 := by
      simp only [div_eq_mul_inv]
      rw [lintegral_add_left']
      · rw [lintegral_mul_const'' _ (hf.pow_const p), lintegral_mul_const', hf_norm, hg_norm,
          one_mul, one_mul, hpq.inv_add_inv_ennreal]
        simp [hpq.symm.pos]
      · exact (hf.pow_const _).mul_const _

/-- Function multiplied by the inverse of its p-seminorm `(∫⁻ f^p ∂μ) ^ 1/p` -/
/-
**ENNReal.funMulInvSnorm** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：funMulInvSnorm (f : α -> Real>=0∞) (p : Real) (μ : Measure α) : α -> Real>
=0∞
参数：f : α -> Real>=0∞；p : Real；μ : Measure α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function multiplied by the inverse of its p-seminorm `(∫⁻ f^p ∂μ) ^ 1/p`
-/
def funMulInvSnorm (f : α → ℝ≥0∞) (p : ℝ) (μ : Measure α) : α → ℝ≥0∞ := fun a =>
  f a * ((∫⁻ c, f c ^ p ∂μ) ^ (1 / p))⁻¹
/-
**ENNReal.fun_eq_funMulInvSnorm_mul_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：fun_eq_funMulInvSnorm_mul_eLpNorm {p : Real} (f : α -> Real>=0∞) (hf_nonze
ro : (∫⁻ a, f a ^ p ∂μ) != 0) (hf_top : (∫⁻ a, f a ^ p ∂μ) != ⊤) {a : α} : f a =
 funMulInvSnorm f p μ a * (∫⁻ c, f c ^ p ∂μ) ^ (1 / p)
参数：f : α -> Real>=0∞；hf_nonzero : (∫⁻ a, f a ^ p ∂μ) != 0；hf_top : (∫⁻ a, f a ^ 
p ∂μ) != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fun_eq_funMulInvSnorm_mul_eLpNorm {p : ℝ} (f : α → ℝ≥0∞)
    (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) {a : α} :
    f a = funMulInvSnorm f p μ a * (∫⁻ c, f c ^ p ∂μ) ^ (1 / p) := by
  simp [funMulInvSnorm, mul_assoc, ENNReal.inv_mul_cancel, hf_nonzero, hf_top]
/-
**ENNReal.funMulInvSnorm_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：funMulInvSnorm_rpow {p : Real} (hp0 : 0 < p) {f : α -> Real>=0∞} {a : α} :
 funMulInvSnorm f p μ a ^ p = f a ^ p * (∫⁻ c, f c ^ p ∂μ)⁻¹
参数：hp0 : 0 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.funMulInvSnorm.eq_1`：∀ {α : Type u_1} [inst : MeasurableSpace α]
 (f : α → ENNReal) (p : ℝ) (μ : MeasureTheory.Measure α) (a : α),   ENNReal.funM
ulInvSnorm f p μ …
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENNReal.inv_rpow`：inv_rpow (x : Real>=0∞) (y : Real) : x⁻¹ ^ y = (x ^ y)
⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用引理 `one_div_mul_cancel`：one_div_mul_cancel (h : a != 0) : 1 / a * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
-/
theorem funMulInvSnorm_rpow {p : ℝ} (hp0 : 0 < p) {f : α → ℝ≥0∞} {a : α} :
    funMulInvSnorm f p μ a ^ p = f a ^ p * (∫⁻ c, f c ^ p ∂μ)⁻¹ := by
  rw [funMulInvSnorm, mul_rpow_of_nonneg _ _ (le_of_lt hp0)]
  suffices h_inv_rpow : ((∫⁻ c : α, f c ^ p ∂μ) ^ (1 / p))⁻¹ ^ p = (∫⁻ c : α, f c ^ p ∂μ)⁻¹ by
    rw [h_inv_rpow]
  rw [inv_rpow, ← rpow_mul, one_div_mul_cancel hp0.ne', rpow_one]
/-
**ENNReal.lintegral_rpow_funMulInvSnorm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNRea
l`。
形式化陈述：lintegral_rpow_funMulInvSnorm_eq_one {p : Real} (hp0_lt : 0 < p) {f : α ->
 Real>=0∞} (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) != 0) (hf_top : (∫⁻ a, f a ^ p ∂μ) !
= ⊤) : ∫⁻ c, funMulInvSnorm f p μ c ^ p ∂μ = 1
参数：hp0_lt : 0 < p；hf_nonzero : (∫⁻ a, f a ^ p ∂μ) != 0；hf_top : (∫⁻ a, f a ^ p ∂
μ) != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.funMulInvSnorm_rpow`：funMulInvSnorm_rpow {p : Real} (hp0 : 0 < p
) {f : α -> Real>=0∞} {a : α} : funMulInvSnorm f p μ a ^ p = f a ^ p * (∫⁻ c, f 
c ^ p ∂μ)⁻¹
· 使用定理 `MeasureTheory.lintegral_mul_const'`：lintegral_mul_const' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
-/
theorem lintegral_rpow_funMulInvSnorm_eq_one {p : ℝ} (hp0_lt : 0 < p) {f : α → ℝ≥0∞}
    (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) :
    ∫⁻ c, funMulInvSnorm f p μ c ^ p ∂μ = 1 := by
  simp_rw [funMulInvSnorm_rpow hp0_lt]
  rw [lintegral_mul_const', ENNReal.mul_inv_cancel hf_nonzero hf_top]
  rwa [inv_ne_top]

/-- Hölder's inequality in case of finite non-zero integrals -/
/-
**ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top** 是 Mathlib 中的一个定理，位于命
名空间 `ENNReal`。
形式化陈述：lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top {p q : Real} (hpq : p.Hold
erConjugate q) {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf_nontop : (∫⁻ a,
 f a ^ p ∂μ) != ⊤) (hg_nontop : (∫⁻ a, g a ^ q ∂μ) != ⊤) (hf_nonzero : (∫⁻ a, f 
a ^ p ∂μ) != 0) (hg_nonzero : (∫⁻ a, g a ^ q ∂μ) != 0) : (∫⁻ a, (f * g) a ∂μ) <=
 (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q)
参数：hpq : p.HolderConjugate q；hf : AEMeasurable f μ；hf_nontop : (∫⁻ a, f a ^ p ∂μ
) != ⊤；hg_nontop : (∫⁻ a, g a ^ q ∂μ) != ⊤；hf_nonzero : (∫⁻ a, f a ^ p ∂μ) != 0；
hg_nonzero : (∫⁻ a, g a ^ q ∂μ) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_congr`：lintegral_congr {f g : α -> Real>=0∞} (h 
: forall a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `ENNReal.fun_eq_funMulInvSnorm_mul_eLpNorm`：fun_eq_funMulInvSnorm_mul_eLp
Norm {p : Real} (f : α -> Real>=0∞) (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) != 0) (hf_t
op : (∫⁻ a, f a ^ p ∂μ) != ⊤) {…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
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
· 使用定理 `MeasureTheory.lintegral_mul_const'`：lintegral_mul_const' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Hölder's inequality in case of finite non-zero integrals
-/
theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_nontop : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤)
    (hg_nontop : (∫⁻ a, g a ^ q ∂μ) ≠ ⊤) (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0)
    (hg_nonzero : (∫⁻ a, g a ^ q ∂μ) ≠ 0) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  let npf := (∫⁻ c : α, f c ^ p ∂μ) ^ (1 / p)
  let nqg := (∫⁻ c : α, g c ^ q ∂μ) ^ (1 / q)
  calc
    (∫⁻ a : α, (f * g) a ∂μ) =
        ∫⁻ a : α, (funMulInvSnorm f p μ * funMulInvSnorm g q μ) a * (npf * nqg) ∂μ := by
      refine lintegral_congr fun a => ?_
      rw [Pi.mul_apply, fun_eq_funMulInvSnorm_mul_eLpNorm f hf_nonzero hf_nontop,
        fun_eq_funMulInvSnorm_mul_eLpNorm g hg_nonzero hg_nontop, Pi.mul_apply]
      ring
    _ ≤ npf * nqg := by
      rw [lintegral_mul_const' (npf * nqg) _
          (by simp [npf, nqg, hf_nontop, hg_nontop, hf_nonzero, hg_nonzero, ENNReal.mul_eq_top])]
      refine mul_le_of_le_one_left' ?_
      have hf1 := lintegral_rpow_funMulInvSnorm_eq_one hpq.pos hf_nonzero hf_nontop
      have hg1 := lintegral_rpow_funMulInvSnorm_eq_one hpq.symm.pos hg_nonzero hg_nontop
      exact lintegral_mul_le_one_of_lintegral_rpow_eq_one hpq (hf.mul_const _) hf1 hg1
/-
**ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNRea
l`。
形式化陈述：ae_eq_zero_of_lintegral_rpow_eq_zero {p : Real} (hp0 : 0 <= p) {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) (hf_zero : ∫⁻ a, f a ^ p ∂μ = 0) : f =ᵐ[μ] 0
参数：hp0 : 0 <= p；hf : AEMeasurable f μ；hf_zero : ∫⁻ a, f a ^ p ∂μ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.rpow_pos_of_nonneg`：rpow_pos_of_nonneg {p : Real} {x : Real>=0∞}
 (hx_pos : 0 < x) (hp_nonneg : 0 <= p) : 0 < x ^ p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem ae_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0 : 0 ≤ p) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_zero : ∫⁻ a, f a ^ p ∂μ = 0) : f =ᵐ[μ] 0 := by
  rw [lintegral_eq_zero_iff' (hf.pow_const p)] at hf_zero
  filter_upwards [hf_zero] with x
  rw [Pi.zero_apply, ← not_imp_not]
  exact fun hx => (rpow_pos_of_nonneg (pos_iff_ne_zero.2 hx) hp0).ne'
/-
**ENNReal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero** 是 Mathlib 中的一个定理，位于命
名空间 `ENNReal`。
形式化陈述：lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero {p : Real} (hp0 : 0 <= p) 
{f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf_zero : ∫⁻ a, f a ^ p ∂μ = 0) :
 (∫⁻ a, (f * g) a ∂μ) = 0
参数：hp0 : 0 <= p；hf : AEMeasurable f μ；hf_zero : ∫⁻ a, f a ^ p ∂μ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_zero_fun`：lintegral_zero_fun : lintegral μ (0 : 
α -> Real>=0∞) = 0
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero`：ae_eq_zero_of_lintegral_rp
ow_eq_zero {p : Real} (hp0 : 0 <= p) {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
 (hf_zero : ∫⁻ a, f a ^ p ∂μ = 0) …
· 使用定理 `Filter.EventuallyEq.mul`：∀ {α : Type u} {β : Type v} [inst : Mul β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f * f' =ᶠ[l] g * g'
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0 : 0 ≤ p) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_zero : ∫⁻ a, f a ^ p ∂μ = 0) : (∫⁻ a, (f * g) a ∂μ) = 0 := by
  rw [← @lintegral_zero_fun α _ μ]
  refine lintegral_congr_ae ?_
  suffices h_mul_zero : f * g =ᵐ[μ] 0 * g by rwa [zero_mul] at h_mul_zero
  have hf_eq_zero : f =ᵐ[μ] 0 := ae_eq_zero_of_lintegral_rpow_eq_zero hp0 hf hf_zero
  exact hf_eq_zero.mul (ae_eq_refl g)
/-
**ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top** 是 Mathlib 中的一个定理，位于命
名空间 `ENNReal`。
形式化陈述：lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top {p q : Real} (hp0_lt : 0 <
 p) (hq0 : 0 <= q) {f g : α -> Real>=0∞} (hf_top : ∫⁻ a, f a ^ p ∂μ = ⊤) (hg_non
zero : (∫⁻ a, g a ^ q ∂μ) != 0) : (∫⁻ a, (f * g) a ∂μ) <= (∫⁻ a, f a ^ p ∂μ) ^ (
1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q)
参数：hp0_lt : 0 < p；hq0 : 0 <= q；hf_top : ∫⁻ a, f a ^ p ∂μ = ⊤；hg_nonzero : (∫⁻ a,
 g a ^ q ∂μ) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top {p q : ℝ} (hp0_lt : 0 < p) (hq0 : 0 ≤ q)
    {f g : α → ℝ≥0∞} (hf_top : ∫⁻ a, f a ^ p ∂μ = ⊤) (hg_nonzero : (∫⁻ a, g a ^ q ∂μ) ≠ 0) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  simp [*]

/-- Hölder's inequality for functions `α → ℝ≥0∞`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
/-
**ENNReal.lintegral_mul_le_Lp_mul_Lq** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lintegral_mul_le_Lp_mul_Lq (μ : Measure α) {p q : Real} (hpq : p.HolderCon
jugate q) {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) 
: (∫⁻ a, (f * g) a ∂μ) <= (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1
 / q)
参数：μ : Measure α；hpq : p.HolderConjugate q；hf : AEMeasurable f μ；hg : AEMeasurab
le g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `ENNReal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero`：lintegral_mul_e
q_zero_of_lintegral_rpow_eq_zero {p : Real} (hp0 : 0 <= p) {f g : α -> Real>=0∞}
 (hf : AEMeasurable f μ) (hf_zero : ∫⁻ a, f a…
· 使用定理 `Real.HolderTriple.nonneg`：nonneg : 0 <= p
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top`：lintegral_mul_l
e_Lp_mul_Lq_of_ne_zero_of_eq_top {p q : Real} (hp0_lt : 0 < p) (hq0 : 0 <= q) {f
 g : α -> Real>=0∞} (hf_top : ∫⁻ a, f a ^ p ∂…
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top`：lintegral_mul_l
e_Lp_mul_Lq_of_ne_zero_of_ne_top {p q : Real} (hpq : p.HolderConjugate q) {f g :
 α -> Real>=0∞} (hf : AEMeasurable f μ) (hf_n…

--- 原说明 ---
Hölder's inequality for functions `α → ℝ≥0∞`. The integral of the product of two
 functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are 
conjugate
exponents.
-/
theorem lintegral_mul_le_Lp_mul_Lq (μ : Measure α) {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  by_cases hf_zero : ∫⁻ a, f a ^ p ∂μ = 0
  · refine Eq.trans_le ?_ zero_le
    exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.nonneg hf hf_zero
  by_cases hg_zero : ∫⁻ a, g a ^ q ∂μ = 0
  · refine Eq.trans_le ?_ zero_le
    rw [mul_comm]
    exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.symm.nonneg hg hg_zero
  by_cases hf_top : ∫⁻ a, f a ^ p ∂μ = ⊤
  · exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.pos hpq.symm.nonneg hf_top hg_zero
  by_cases hg_top : ∫⁻ a, g a ^ q ∂μ = ⊤
  · rw [mul_comm, mul_comm ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p))]
    exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.symm.pos hpq.nonneg hg_top hf_zero
  -- non-⊤ non-zero case
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top hpq hf hf_top hg_top hf_zero hg_zero

/-- A different formulation of Hölder's inequality for two functions, with two exponents that sum to
1, instead of reciprocals of -/
/-
**ENNReal.lintegral_mul_norm_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lintegral_mul_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α} {f g : α
 -> Real>=0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) {p q : Real} (hp :
 0 <= p) (hq : 0 <= q) (hpq : p + q = 1) : ∫⁻ a, f a ^ p * g a ^ q ∂μ <= (∫⁻ a, 
f a ∂μ) ^ p * (∫⁻ a, g a ∂μ) ^ q
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ；hp : 0 <= p；hq : 0 <= q；hpq : p +
 q = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `one_lt_inv₀`：one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
A different formulation of Hölder's inequality for two functions, with two expon
ents that sum to
1, instead of reciprocals of
-/
theorem lintegral_mul_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    ∫⁻ a, f a ^ p * g a ^ q ∂μ ≤ (∫⁻ a, f a ∂μ) ^ p * (∫⁻ a, g a ∂μ) ^ q := by
  rcases hp.eq_or_lt with rfl | hp
  · rw [zero_add] at hpq
    simp [hpq]
  rcases hq.eq_or_lt with rfl | hq
  · rw [add_zero] at hpq
    simp [hpq]
  have h2p : 1 < 1 / p := by
    rw [one_div, one_lt_inv₀ hp]
    linarith
  have h2pq : (1 / p)⁻¹ + (1 / q)⁻¹ = 1 := by simp [hpq]
  have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.holderConjugate_iff.mpr ⟨h2p, h2pq⟩)
    (hf.pow_const p) (hg.pow_const q)
  simpa [← ENNReal.rpow_mul, hp.ne', hq.ne'] using this

/-- A version of Hölder with multiple arguments -/
/-
**ENNReal.lintegral_prod_norm_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lintegral_prod_norm_pow_le {α ι : Type*} [MeasurableSpace α] {μ : Measure 
α} (s : Finset ι) {f : ι -> α -> Real>=0∞} (hf : forall i in s, AEMeasurable (f 
i) μ) {p : ι -> Real} (hp : ∑ i in s, p i = 1) (h2p : forall i in s, 0 <= p i) :
 ∫⁻ a, ∏ i in s, f i a ^ p i ∂μ <= ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i
参数：s : Finset ι；hf : forall i in s, AEMeasurable (f i) μ；hp : ∑ i in s, p i = 1；
h2p : forall i in s, 0 <= p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
A version of Hölder with multiple arguments
-/
theorem lintegral_prod_norm_pow_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    {p : ι → ℝ} (hp : ∑ i ∈ s, p i = 1) (h2p : ∀ i ∈ s, 0 ≤ p i) :
    ∫⁻ a, ∏ i ∈ s, f i a ^ p i ∂μ ≤ ∏ i ∈ s, (∫⁻ a, f i a ∂μ) ^ p i := by
  classical
  induction s using Finset.induction generalizing p with
  | empty =>
    simp at hp
  | insert i₀ s hi₀ ih =>
    rcases eq_or_ne (p i₀) 1 with h2i₀ | h2i₀
    · simp only [hi₀, not_false_eq_true, prod_insert]
      have h2p : ∀ i ∈ s, p i = 0 := by
        simpa [hi₀, h2i₀, sum_eq_zero_iff_of_nonneg (fun i hi ↦ h2p i <| mem_insert_of_mem hi)]
          using hp
      calc ∫⁻ a, f i₀ a ^ p i₀ * ∏ i ∈ s, f i a ^ p i ∂μ
          = ∫⁻ a, f i₀ a ^ p i₀ * ∏ i ∈ s, 1 ∂μ := by
            congr! 3 with x
            apply prod_congr rfl fun i hi ↦ by rw [h2p i hi, ENNReal.rpow_zero]
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i ∈ s, 1 := by simp [h2i₀]
        _ = (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i ∈ s, (∫⁻ a, f i a ∂μ) ^ p i := by
            congr 1
            apply prod_congr rfl fun i hi ↦ by rw [h2p i hi, ENNReal.rpow_zero]
    · have hpi₀ : 0 ≤ 1 - p i₀ := by
        simp_rw [sub_nonneg, ← hp, single_le_sum h2p (mem_insert_self ..)]
      have h2pi₀ : 1 - p i₀ ≠ 0 := by
        rwa [sub_ne_zero, ne_comm]
      let q := fun i ↦ p i / (1 - p i₀)
      have hq : ∑ i ∈ s, q i = 1 := by
        rw [← Finset.sum_div, ← sum_insert_sub hi₀, hp, div_self h2pi₀]
      have h2q : ∀ i ∈ s, 0 ≤ q i :=
        fun i hi ↦ div_nonneg (h2p i <| mem_insert_of_mem hi) hpi₀
      calc ∫⁻ a, ∏ i ∈ insert i₀ s, f i a ^ p i ∂μ
          = ∫⁻ a, f i₀ a ^ p i₀ * ∏ i ∈ s, f i a ^ p i ∂μ := by simp [hi₀]
        _ = ∫⁻ a, f i₀ a ^ p i₀ * (∏ i ∈ s, f i a ^ q i) ^ (1 - p i₀) ∂μ := by
            simp [q, ← ENNReal.prod_rpow_of_nonneg hpi₀, ← ENNReal.rpow_mul,
              div_mul_cancel₀ (h := h2pi₀)]
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * (∫⁻ a, ∏ i ∈ s, f i a ^ q i ∂μ) ^ (1 - p i₀) := by
            apply ENNReal.lintegral_mul_norm_pow_le
            · exact hf i₀ <| mem_insert_self ..
            · exact s.aemeasurable_fun_prod fun i hi ↦ (hf i <| mem_insert_of_mem hi).pow_const _
            · exact h2p i₀ <| mem_insert_self ..
            · exact hpi₀
            · apply add_sub_cancel
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * (∏ i ∈ s, (∫⁻ a, f i a ∂μ) ^ q i) ^ (1 - p i₀) := by
            gcongr -- behavior of gcongr is heartbeat-dependent, which makes code really fragile...
            exact ih (fun i hi ↦ hf i <| mem_insert_of_mem hi) hq h2q
        _ = (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i ∈ s, (∫⁻ a, f i a ∂μ) ^ p i := by
            simp [q, ← ENNReal.prod_rpow_of_nonneg hpi₀, ← ENNReal.rpow_mul,
              div_mul_cancel₀ (h := h2pi₀)]
        _ = ∏ i ∈ insert i₀ s, (∫⁻ a, f i a ∂μ) ^ p i := by simp [hi₀]

/-- A version of Hölder with multiple arguments, one of which plays a distinguished role. -/
/-
**ENNReal.lintegral_mul_prod_norm_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lintegral_mul_prod_norm_pow_le {α ι : Type*} [MeasurableSpace α] {μ : Meas
ure α} (s : Finset ι) {g : α -> Real>=0∞} {f : ι -> α -> Real>=0∞} (hg : AEMeasu
rable g μ) (hf : forall i in s, AEMeasurable (f i) μ) (q : Real) {p : ι -> Real}
 (hpq : q + ∑ i in s, p i = 1) (hq : 0 <= q) (hp : forall i in s, 0 <= p i) : ∫⁻
 a, g a ^ q * ∏ i in s, f i a ^ p i ∂μ <= (∫⁻ a, g a ∂μ) ^ q * ∏ i in s, (∫⁻ a, 
f i a ∂μ) ^ p i
参数：s : Finset ι；hg : AEMeasurable g μ；hf : forall i in s, AEMeasurable (f i) μ；q
 : Real；hpq : q + ∑ i in s, p i = 1；hq : 0 <= q；hp : forall i in s, 0 <= p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.lintegral_prod_norm_pow_le`：lintegral_prod_norm_pow_le {α ι : Ty
pe*} [MeasurableSpace α] {μ : Measure α} (s : Finset ι) {f : ι -> α -> Real>=0∞}
 (hf : forall i in s, AE…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insertNone`：∀ {α : Type u_1} {M : Type u_2} [inst : AddCommMo
noid M] (f : Option α → M) (s : Finset α),   ∑ x ∈ Finset.insertNone s, f x = f 
none + ∑ x …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_insertNone`：prod_insertNone (f : Option α -> M) (s : Finset 
α) : ∏ x in insertNone s, f x = f none * ∏ x in s, f (some x)

--- 原说明 ---
A version of Hölder with multiple arguments, one of which plays a distinguished 
role.
-/
theorem lintegral_mul_prod_norm_pow_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {g : α → ℝ≥0∞} {f : ι → α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) (q : ℝ) {p : ι → ℝ} (hpq : q + ∑ i ∈ s, p i = 1)
    (hq : 0 ≤ q) (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∫⁻ a, g a ^ q * ∏ i ∈ s, f i a ^ p i ∂μ ≤
      (∫⁻ a, g a ∂μ) ^ q * ∏ i ∈ s, (∫⁻ a, f i a ∂μ) ^ p i := by
  suffices
    ∫⁻ t, ∏ j ∈ insertNone s, Option.elim j (g t) (fun j ↦ f j t) ^ Option.elim j q p ∂μ
    ≤ ∏ j ∈ insertNone s, (∫⁻ t, Option.elim j (g t) (fun j ↦ f j t) ∂μ) ^ Option.elim j q p by
    simpa using this
  refine ENNReal.lintegral_prod_norm_pow_le _ ?_ ?_ ?_
  · rintro (_ | i) hi
    · exact hg
    · refine hf i ?_
      simpa using hi
  · simp_rw [sum_insertNone, Option.elim]
    exact hpq
  · rintro (_ | i) hi
    · exact hq
    · refine hp i ?_
      simpa using hi
/-
**ENNReal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top** 是 Mathlib 中的一个定理，
位于命名空间 `ENNReal`。
形式化陈述：lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top {p : Real} {f g : α -> 
Real>=0∞} (hf : AEMeasurable f μ) (hf_top : (∫⁻ a, f a ^ p ∂μ) < ⊤) (hg_top : (∫
⁻ a, g a ^ p ∂μ) < ⊤) (hp1 : 1 <= p) : (∫⁻ a, (f + g) a ^ p ∂μ) < ⊤
参数：hf : AEMeasurable f μ；hf_top : (∫⁻ a, f a ^ p ∂μ) < ⊤；hg_top : (∫⁻ a, g a ^ p
 ∂μ) < ⊤；hp1 : 1 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `ENNReal.rpow_add_le_mul_rpow_add_rpow`：rpow_add_le_mul_rpow_add_rpow (z₁
 z₂ : Real>=0∞) {p : Real} (hp : 1 <= p) : (z₁ + z₂) ^ p <= (2 : Real>=0∞) ^ (p 
- 1) * (z₁ ^ p + z₂ ^ p)
· 使用定理 `MeasureTheory.lintegral_add_left'`：lintegral_add_left' {f : α -> Real>=0
∞} (hf : AEMeasurable f μ) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a 
∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `AEMeasurable.const_mul`：AEMeasurable.const_mul [MeasurableMul M] (hf : A
EMeasurable f μ) (c : M) : AEMeasurable (fun x => c * f x) μ
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `MeasureTheory.lintegral_const_mul''`：lintegral_const_mul'' (r : Real>=0∞
) {f : α -> Real>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a
 ∂μ
· 使用定理 `MeasureTheory.lintegral_const_mul'`：lintegral_const_mul' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `ENNReal.rpow_ne_top_of_nonneg'`：rpow_ne_top_of_nonneg' {y : Real} {x : R
eal>=0∞} (hx : 0 < x) (hx' : x != ⊤) : x ^ y != ⊤
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.rpow_ne_top_of_ne_zero`：rpow_ne_top_of_ne_zero {x : Real>=0∞} {y
 : Real} (hx : x != 0) (hx' : x != ⊤) : x ^ y != ⊤
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
-/
theorem lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top {p : ℝ} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_top : (∫⁻ a, f a ^ p ∂μ) < ⊤) (hg_top : (∫⁻ a, g a ^ p ∂μ) < ⊤)
    (hp1 : 1 ≤ p) : (∫⁻ a, (f + g) a ^ p ∂μ) < ⊤ := by
  calc
    (∫⁻ a : α, (f a + g a) ^ p ∂μ) ≤
        ∫⁻ a, (2 : ℝ≥0∞) ^ (p - 1) * f a ^ p + (2 : ℝ≥0∞) ^ (p - 1) * g a ^ p ∂μ := by
      refine lintegral_mono fun a => ?_
      simpa [mul_add] using ENNReal.rpow_add_le_mul_rpow_add_rpow (f a) (g a) hp1
    _ < ⊤ := by
      rw [lintegral_add_left', lintegral_const_mul'' _ (hf.pow_const p),
        lintegral_const_mul' _ _ (by finiteness), ENNReal.add_lt_top]
      · constructor <;> finiteness
      · fun_prop
/-
**ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lintegral_Lp_mul_le_Lq_mul_Lr {α} [MeasurableSpace α] {p q r : Real} (hp0_
lt : 0 < p) (hpq : p < q) (hpqr : 1 / p = 1 / q + 1 / r) (μ : Measure α) {f g : 
α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : (∫⁻ a, (f * g) 
a ^ p ∂μ) ^ (1 / p) <= (∫⁻ a, f a ^ q ∂μ) ^ (1 / q) * (∫⁻ a, g a ^ r ∂μ) ^ (1 / 
r)
参数：hp0_lt : 0 < p；hpq : p < q；hpqr : 1 / p = 1 / q + 1 / r；μ : Measure α；hf : AE
Measurable f μ；hg : AEMeasurable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.HolderConjugate.conjExponent`：∀ {p : ℝ}, 1 < p → p.HolderConjugate 
p.conjExponent
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `ENNReal.lintegral_mul_le_Lp_mul_Lq`：lintegral_mul_le_Lp_mul_Lq (μ : Meas
ure α) {p q : Real} (hpq : p.HolderConjugate q) {f g : α -> Real>=0∞} (hf : AEMe
asurable f μ) (hg : AEMe…
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 69 条，此处仅展示前 30 条）
-/
theorem lintegral_Lp_mul_le_Lq_mul_Lr {α} [MeasurableSpace α] {p q r : ℝ} (hp0_lt : 0 < p)
    (hpq : p < q) (hpqr : 1 / p = 1 / q + 1 / r) (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, (f * g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ q ∂μ) ^ (1 / q) * (∫⁻ a, g a ^ r ∂μ) ^ (1 / r) := by
  have hp0_ne : p ≠ 0 := (ne_of_lt hp0_lt).symm
  have hp0 : 0 ≤ p := le_of_lt hp0_lt
  have hq0_lt : 0 < q := lt_of_le_of_lt hp0 hpq
  have hq0_ne : q ≠ 0 := (ne_of_lt hq0_lt).symm
  have h_one_div_r : 1 / r = 1 / p - 1 / q := by rw [hpqr]; simp
  let p2 := q / p
  let q2 := p2.conjExponent
  have hp2q2 : p2.HolderConjugate q2 :=
    .conjExponent (by simp [p2, _root_.lt_div_iff₀, hpq, hp0_lt])
  calc
    (∫⁻ a : α, (f * g) a ^ p ∂μ) ^ (1 / p) = (∫⁻ a : α, f a ^ p * g a ^ p ∂μ) ^ (1 / p) := by
      simp_rw [Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ hp0]
    _ ≤ ((∫⁻ a, f a ^ (p * p2) ∂μ) ^ (1 / p2) *
        (∫⁻ a, g a ^ (p * q2) ∂μ) ^ (1 / q2)) ^ (1 / p) := by
      gcongr
      simp_rw [ENNReal.rpow_mul]
      exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp2q2 (hf.pow_const _) (hg.pow_const _)
    _ = (∫⁻ a : α, f a ^ q ∂μ) ^ (1 / q) * (∫⁻ a : α, g a ^ r ∂μ) ^ (1 / r) := by
      rw [@ENNReal.mul_rpow_of_nonneg _ _ (1 / p) (by simp [hp0]), ← ENNReal.rpow_mul, ←
        ENNReal.rpow_mul]
      have hpp2 : p * p2 = q := by
        symm
        rw [mul_comm, ← div_eq_iff hp0_ne]
      have hpq2 : p * q2 = r := by
        rw [← inv_inv r, ← one_div, ← one_div, h_one_div_r]
        simp [field, p2, q2, Real.conjExponent]
      simp_rw [div_mul_div_comm, mul_one, mul_comm p2, mul_comm q2, hpp2, hpq2]
/-
**ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow** 是 Mathlib 中的
一个定理，位于命名空间 `ENNReal`。
形式化陈述：lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow {p q : Real} (hpq 
: p.HolderConjugate q) {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : AEMea
surable g μ) : ∫⁻ a, f a * g a ^ (p - 1) ∂μ <= (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫
⁻ a, g a ^ p ∂μ) ^ (1 / q)
参数：hpq : p.HolderConjugate q；hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `ENNReal.lintegral_mul_le_Lp_mul_Lq`：lintegral_mul_le_Lp_mul_Lq (μ : Meas
ure α) {p q : Real} (hpq : p.HolderConjugate q) {f g : α -> Real>=0∞} (hf : AEMe
asurable f μ) (hg : AEMe…
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.HolderConjugate.sub_one_mul_conj`：sub_one_mul_conj : (p - 1) * q = 
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow {p q : ℝ}
    (hpq : p.HolderConjugate q) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a * g a ^ (p - 1) ∂μ ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ p ∂μ) ^ (1 / q) := by
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf (hg.pow_const _)).trans_eq ?_
  simp [← ENNReal.rpow_mul, hpq.sub_one_mul_conj]
/-
**ENNReal.lintegral_rpow_add_le_add_eLpNorm_mul_lintegral_rpow_add** 是 Mathlib 中
的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lintegral_rpow_add_le_add_eLpNorm_mul_lintegral_rpow_add {p q : Real} (hpq
 : p.HolderConjugate q) {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : AEMe
asurable g μ) : ∫⁻ a, (f + g) a ^ p ∂μ <= ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a,
 g a ^ p ∂μ) ^ (1 / p)) * (∫⁻ a, (f a + g a) ^ p ∂μ) ^ (1 / q)
参数：hpq : p.HolderConjugate q；hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `Real.HolderConjugate.sub_one_pos`：sub_one_pos : 0 < p - 1
· 使用定理 `ENNReal.top_mul_top`：top_mul_top : ∞ * ∞ = ∞
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `ENNReal.rpow_add`：rpow_add {x : Real>=0∞} (y z : Real) (hx : x != 0) (h'
x : x != ⊤) : x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `AEMeasurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpac
e M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTheory
.Measu…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `MeasureTheory.lintegral_add_left'`：lintegral_add_left' {f : α -> Real>=0
∞} (hf : AEMeasurable f μ) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a 
∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `AEMeasurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTh
eory.Measu…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 33 条，此处仅展示前 30 条）
-/
theorem lintegral_rpow_add_le_add_eLpNorm_mul_lintegral_rpow_add {p q : ℝ}
    (hpq : p.HolderConjugate q) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, (f + g) a ^ p ∂μ ≤
      ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) *
        (∫⁻ a, (f a + g a) ^ p ∂μ) ^ (1 / q) := by
  calc
    (∫⁻ a, (f + g) a ^ p ∂μ) ≤ ∫⁻ a, (f + g) a * (f + g) a ^ (p - 1) ∂μ := by
      gcongr with a
      by_cases h_zero : (f + g) a = 0
      · rw [h_zero, ENNReal.zero_rpow_of_pos hpq.pos]
        exact zero_le
      by_cases h_top : (f + g) a = ⊤
      · rw [h_top, ENNReal.top_rpow_of_pos hpq.sub_one_pos, ENNReal.top_mul_top]
        exact le_top
      refine le_of_eq ?_
      nth_rw 2 [← ENNReal.rpow_one ((f + g) a)]
      rw [← ENNReal.rpow_add _ _ h_zero h_top, add_sub_cancel]
    _ = (∫⁻ a : α, f a * (f + g) a ^ (p - 1) ∂μ) + ∫⁻ a : α, g a * (f + g) a ^ (p - 1) ∂μ := by
      have h_add_m : AEMeasurable (fun a : α => (f + g) a ^ (p - 1 : ℝ)) μ :=
        (hf.add hg).pow_const _
      have h_add_apply :
        (∫⁻ a : α, (f + g) a * (f + g) a ^ (p - 1) ∂μ) =
          ∫⁻ a : α, (f a + g a) * (f + g) a ^ (p - 1) ∂μ :=
        rfl
      simp_rw [h_add_apply, add_mul]
      rw [lintegral_add_left' (hf.fun_mul h_add_m)]
    _ ≤
        ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) *
          (∫⁻ a, (f a + g a) ^ p ∂μ) ^ (1 / q) := by
      rw [add_mul]
      gcongr
      · exact lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hf (hf.add hg)
      · exact lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hg (hf.add hg)
/-
**ENNReal.lintegral_Lp_add_le_aux** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem lintegral_Lp_add_le_aux {p q : ℝ} (hpq : p.HolderConjugate q) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (h_add_zero : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ 0)
    (h_add_top : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) := by
  have h0_rpow : (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≠ 0 := by
    simp [h_add_zero, h_add_top, -Pi.add_apply]
  suffices h :
    1 ≤
      (∫⁻ a : α, (f + g) a ^ p ∂μ) ^ (-(1 / p)) *
        ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a : α, g a ^ p ∂μ) ^ (1 / p)) by
    rwa [← ENNReal.mul_le_mul_iff_right h0_rpow (by finiteness),
      ← mul_assoc, ← rpow_add _ _ h_add_zero h_add_top, ←
      sub_eq_add_neg, _root_.sub_self, rpow_zero, one_mul, mul_one] at h
  have h :
    (∫⁻ a : α, (f + g) a ^ p ∂μ) ≤
      ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a : α, g a ^ p ∂μ) ^ (1 / p)) *
        (∫⁻ a : α, (f + g) a ^ p ∂μ) ^ (1 / q) :=
    lintegral_rpow_add_le_add_eLpNorm_mul_lintegral_rpow_add hpq hf hg
  have h_one_div_q : 1 / q = 1 - 1 / p := by
    nth_rw 2 [← hpq.inv_add_inv_eq_one]
    ring
  simp_rw [h_one_div_q, sub_eq_add_neg 1 (1 / p), ENNReal.rpow_add _ _ h_add_zero h_add_top,
    rpow_one] at h
  conv_rhs at h => enter [2]; rw [mul_comm]
  conv_lhs at h => rw [← one_mul (∫⁻ a : α, (f + g) a ^ p ∂μ)]
  rwa [← mul_assoc, ENNReal.mul_le_mul_iff_left h_add_zero h_add_top, mul_comm] at h

/-- **Minkowski's inequality for functions** `α → ℝ≥0∞`: the `ℒp` seminorm of the sum of two
functions is bounded by the sum of their `ℒp` seminorms. -/
/-
**ENNReal.lintegral_Lp_add_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lintegral_Lp_add_le {p : Real} {f g : α -> Real>=0∞} (hf : AEMeasurable f 
μ) (hg : AEMeasurable g μ) (hp1 : 1 <= p) : (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) <
= (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ；hp1 : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div_one`：one_div_one : (1 : G) / 1 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `MeasureTheory.lintegral_add_left'`：lintegral_add_left' {f : α -> Real>=0
∞} (hf : AEMeasurable f μ) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a 
∂μ + ∫⁻ a, g a ∂μ
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Real.HolderConjugate.conjExponent`：∀ {p : ℝ}, 1 < p → p.HolderConjugate 
p.conjExponent
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.MeanInequalities.0.ENNReal.linte
gral_Lp_add_le_aux`：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheo
ry.Measure α} {p q : ℝ},   p.HolderConjugate q →     ∀ {f g : α → ENNReal},     
…
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
**Minkowski's inequality for functions** `α → ℝ≥0∞`: the `ℒp` seminorm of the su
m of two
functions is bounded by the sum of their `ℒp` seminorms.
-/
theorem lintegral_Lp_add_le {p : ℝ} {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hp1 : 1 ≤ p) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  obtain hf_top | hf_top := eq_top_or_lt_top (∫⁻ a, f a ^ p ∂μ)
  · simp [hf_top, hp_pos]
  obtain hg_top | hg_top := eq_top_or_lt_top (∫⁻ a, g a ^ p ∂μ)
  · simp [hg_top, hp_pos]
  by_cases h1 : p = 1
  · refine le_of_eq ?_
    simp_rw [h1, one_div_one, ENNReal.rpow_one]
    exact lintegral_add_left' hf _
  have hp1_lt : 1 < p := by
    refine lt_of_le_of_ne hp1 ?_
    symm
    exact h1
  have hpq := Real.HolderConjugate.conjExponent hp1_lt
  by_cases h0 : (∫⁻ a, (f + g) a ^ p ∂μ) = 0
  · rw [h0, @ENNReal.zero_rpow_of_pos (1 / p) (by simp [lt_of_lt_of_le zero_lt_one hp1])]
    exact zero_le
  exact lintegral_Lp_add_le_aux hpq hf hg h0
    (lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top hf hf_top hg_top hp1).ne

/-- Variant of Minkowski's inequality for functions `α → ℝ≥0∞` in `ℒp` with `p ≤ 1`: the `ℒp`
seminorm of the sum of two functions is bounded by a constant multiple of the sum
of their `ℒp` seminorms. -/
/-
**ENNReal.lintegral_Lp_add_le_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lintegral_Lp_add_le_of_le_one {p : Real} {f g : α -> Real>=0∞} (hf : AEMea
surable f μ) (hp0 : 0 <= p) (hp1 : p <= 1) : (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) 
<= (2 : Real>=0∞) ^ (1 / p - 1) * ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p
 ∂μ) ^ (1 / p))
参数：hf : AEMeasurable f μ；hp0 : 0 <= p；hp1 : p <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `MeasureTheory.lintegral_one`：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ
 univ
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENNReal.rpow_neg`：rpow_neg (x : Real>=0∞) (y : Real) : x ^ (-y) = (x ^ y
)⁻¹
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_add_left'`：lintegral_add_left' {f : α -> Real>=0
∞} (hf : AEMeasurable f μ) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a 
∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `ENNReal.rpow_add_le_add_rpow`：rpow_add_le_add_rpow {p : Real} (a b : Rea
l>=0∞) (hp : 0 <= p) (hp1 : p <= 1) : (a + b) ^ p <= a ^ p + b ^ p
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Variant of Minkowski's inequality for functions `α → ℝ≥0∞` in `ℒp` with `p ≤ 1`:
 the `ℒp`
seminorm of the sum of two functions is bounded by a constant multiple of the su
m
of their `ℒp` seminorms.
-/
theorem lintegral_Lp_add_le_of_le_one {p : ℝ} {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (2 : ℝ≥0∞) ^ (1 / p - 1) * ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) := by
  rcases eq_or_lt_of_le hp0 with (rfl | hp)
  · simp only [Pi.add_apply, rpow_zero, lintegral_one, _root_.div_zero, zero_sub]
    norm_num
    rw [rpow_neg, rpow_one, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top]
  calc
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤ ((∫⁻ a, f a ^ p ∂μ) + ∫⁻ a, g a ^ p ∂μ) ^ (1 / p) := by
      rw [← lintegral_add_left' (hf.pow_const p)]
      gcongr with a
      exact rpow_add_le_add_rpow _ _ hp0 hp1
    _ ≤ (2 : ℝ≥0∞) ^ (1 / p - 1) * ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) :=
      rpow_add_le_mul_rpow_add_rpow _ _ ((one_le_div hp).2 hp1)

end ENNReal

/-- Hölder's inequality for functions `α → ℝ≥0`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
/-
**NNReal.lintegral_mul_le_Lp_mul_Lq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNReal.lintegral_mul_le_Lp_mul_Lq {p q : Real} (hpq : p.HolderConjugate q)
 {f g : α -> Real>=0} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : (∫⁻ a, (
f * g) a ∂μ) <= (∫⁻ a, (f a : Real>=0∞) ^ p ∂μ) ^ (1 / p) * (∫⁻ a, (g a : Real>=
0∞) ^ q ∂μ) ^ (1 / q)
参数：hpq : p.HolderConjugate q；hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.lintegral_mul_le_Lp_mul_Lq`：lintegral_mul_le_Lp_mul_Lq (μ : Meas
ure α) {p q : Real} (hpq : p.HolderConjugate q) {f g : α -> Real>=0∞} (hf : AEMe
asurable f μ) (hg : AEMe…
· 使用定理 `AEMeasurable.coe_nnreal_ennreal`：AEMeasurable.coe_nnreal_ennreal {f : α 
-> Real>=0} {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => (f 
x : Real>=0∞)) μ

--- 原说明 ---
Hölder's inequality for functions `α → ℝ≥0`. The integral of the product of two 
functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are 
conjugate
exponents.
-/
theorem NNReal.lintegral_mul_le_Lp_mul_Lq {p q : ℝ} (hpq : p.HolderConjugate q) {f g : α → ℝ≥0}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, (f * g) a ∂μ) ≤
      (∫⁻ a, (f a : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) * (∫⁻ a, (g a : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) := by
  simp_rw [Pi.mul_apply, ENNReal.coe_mul]
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.coe_nnreal_ennreal hg.coe_nnreal_ennreal

end

end LIntegral

