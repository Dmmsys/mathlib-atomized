/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.Positivity.Finset

/-!
# Real-valued Lᵖ norm

This file proves theorems about `MeasureTheory.lpNorm`,
a real-valued version of `MeasureTheory.eLpNorm`.
-/

open Filter
open scoped BigOperators ComplexConjugate ENNReal NNReal

public section

namespace MeasureTheory
variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] {f g h : α → E}

/-
**MeasureTheory.toReal_eLpNorm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：toReal_eLpNorm (hf : AEStronglyMeasurable f μ) : (eLpNorm f p μ).toReal = 
lpNorm f p μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lpNorm.eq_1`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measura
bleSpace α} [inst : NormedAddCommGroup E] (f : α → E) (p : ENNReal)   (μ : Measu
reTheory.Measur…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma toReal_eLpNorm (hf : AEStronglyMeasurable f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ := by
  rw [lpNorm, if_pos hf]
/-
**MeasureTheory.ofReal_lpNorm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ofReal_lpNorm (hf : MemLp f p μ) : .ofReal (lpNorm f p μ) = eLpNorm f p μ
参数：hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.toReal_eLpNorm`：toReal_eLpNorm (hf : AEStronglyMeasurable 
f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
-/
lemma ofReal_lpNorm (hf : MemLp f p μ) : .ofReal (lpNorm f p μ) = eLpNorm f p μ := by
  rw [← toReal_eLpNorm hf.aestronglyMeasurable, ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

@[simp]
/-
**MeasureTheory.lpNorm_of_not_aestronglyMeasurable** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory`。
形式化陈述：lpNorm_of_not_aestronglyMeasurable (hf : ¬ AEStronglyMeasurable f μ) : lpN
orm f p μ = 0
参数：hf : ¬ AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma lpNorm_of_not_aestronglyMeasurable (hf : ¬ AEStronglyMeasurable f μ) : lpNorm f p μ = 0 :=
  if_neg hf

@[simp]
/-
**MeasureTheory.lpNorm_of_not_memLp** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_of_not_memLp (hf' : ¬ MemLp f p μ) : lpNorm f p μ = 0
参数：hf' : ¬ MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma lpNorm_of_not_memLp (hf' : ¬ MemLp f p μ) : lpNorm f p μ = 0 := by simp_all [MemLp, lpNorm]
/-
**MeasureTheory.lpNorm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E] {f : α → E}, 0 ≤ Measu
reTheory.lpNorm f p μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
@[simp] lemma lpNorm_nonneg : 0 ≤ lpNorm f p μ := by simp [lpNorm, apply_ite]
/-
**MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：lpNorm_eq_integral_norm_rpow_toReal (hp₀ : p != 0) (hp : p != ∞) (hf : AES
tronglyMeasurable f μ) : lpNorm f p μ = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹
参数：hp₀ : p != 0；hp : p != ∞；hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.toReal_eLpNorm`：toReal_eLpNorm (hf : AEStronglyMeasurable 
f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用定理 `ENNReal.toReal_rpow`：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ 
z = (x ^ z).toReal
· 使用定理 `MeasureTheory.integral_toReal`：integral_toReal {f : α -> Real>=0∞} (hfm 
: AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a,
 f a ∂μ).toReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用引理 `AEMeasurable.ennreal_ofReal`：AEMeasurable.ennreal_ofReal {f : α -> Real}
 {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal
 (f x)) μ
· 使用定理 `AEMeasurable.norm`：AEMeasurable.norm {f : β -> α} {μ : Measure β} (hf : 
AEMeasurable f μ) : AEMeasurable (fun a => norm (f a)) μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lpNorm_eq_integral_norm_rpow_toReal (hp₀ : p ≠ 0) (hp : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) :
    lpNorm f p μ = (∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
  rw [← toReal_eLpNorm hf, eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp, ← ENNReal.toReal_rpow,
    ← integral_toReal]
  · simp [← ENNReal.toReal_rpow]
  · simp_rw [← ofReal_norm]
    borelize E
    fun_prop
  · exact .of_forall fun x ↦ ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)
/-
**MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：lpNorm_nnreal_eq_integral_norm_rpow {p : Real>=0} (hp : p != 0) (hf : AESt
ronglyMeasurable f μ) : lpNorm f p μ = (∫ x, ‖f x‖ ^ (p : Real) ∂μ) ^ (p⁻¹ : Rea
l)
参数：hp : p != 0；hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal`：lpNorm_eq_integral_no
rm_rpow_toReal (hp₀ : p != 0) (hp : p != ∞) (hf : AEStronglyMeasurable f μ) : lp
Norm f p μ = (∫ x, ‖f x‖ ^ p.toReal ∂μ)…
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lpNorm_nnreal_eq_integral_norm_rpow {p : ℝ≥0} (hp : p ≠ 0) (hf : AEStronglyMeasurable f μ) :
    lpNorm f p μ = (∫ x, ‖f x‖ ^ (p : ℝ) ∂μ) ^ (p⁻¹ : ℝ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp) hf]; simp
/-
**MeasureTheory.lpNorm_one_eq_integral_norm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：lpNorm_one_eq_integral_norm (hf : AEStronglyMeasurable f μ) : lpNorm f 1 μ
 = ∫ x, ‖f x‖ ∂μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal`：lpNorm_eq_integral_no
rm_rpow_toReal (hp₀ : p != 0) (hp : p != ∞) (hf : AEStronglyMeasurable f μ) : lp
Norm f p μ = (∫ x, ‖f x‖ ^ p.toReal ∂μ)…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lpNorm_one_eq_integral_norm (hf : AEStronglyMeasurable f μ) :
    lpNorm f 1 μ = ∫ x, ‖f x‖ ∂μ := by
  simp [lpNorm_eq_integral_norm_rpow_toReal one_ne_zero ENNReal.coe_ne_top hf]
/-
**MeasureTheory.lpNorm_exponent_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup E]   (f : α → E), MeasureTheory.lpNorm f 
0 μ = 0
参数：f : α → E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lpNorm_exponent_zero (f : α → E) : lpNorm f 0 μ = 0 := by simp [lpNorm]
/-
**MeasureTheory.lpNorm_measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} {p : ENNReal} [ins
t : NormedAddCommGroup E] (f : α → E),   MeasureTheory.lpNorm f p 0 = 0
参数：f : α → E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `MeasureTheory.eLpNorm_measure_zero`：eLpNorm_measure_zero {f : α -> ε} : 
eLpNorm f p (0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lpNorm_measure_zero (f : α → E) : lpNorm f p (0 : Measure α) = 0 := by simp [lpNorm]
/-
**MeasureTheory.ae_le_lpNorm_exponent_top** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：ae_le_lpNorm_exponent_top (hf : MemLp f ∞ μ) : forallᵐ x ∂μ, ‖f x‖ <= lpNo
rm f ∞ μ
参数：hf : MemLp f ∞ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.toReal_eLpNorm`：toReal_eLpNorm (hf : AEStronglyMeasurable 
f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `ENNReal.ofReal_le_iff_le_toReal`：ofReal_le_iff_le_toReal {a : Real} {b :
 Real>=0∞} (hb : b != ∞) : ENNReal.ofReal a <= b ↔ a <= ENNReal.toReal b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `MeasureTheory.ae_le_eLpNormEssSup`：ae_le_eLpNormEssSup {f : α -> ε} : fo
rallᵐ y ∂μ, ‖f y‖ₑ <= eLpNormEssSup f μ
-/
lemma ae_le_lpNorm_exponent_top (hf : MemLp f ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ lpNorm f ∞ μ := by
  simpa only [← toReal_eLpNorm hf.aestronglyMeasurable, ← ENNReal.ofReal_le_iff_le_toReal hf.2.ne,
    ofReal_norm] using! ae_le_eLpNormEssSup
/-
**MeasureTheory.lpNorm_exponent_top_eq_essSup** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：lpNorm_exponent_top_eq_essSup (hf : MemLp f ∞ μ) : lpNorm f ∞ μ = essSup (
‖f ·‖) μ
参数：hf : MemLp f ∞ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.toReal_eLpNorm`：toReal_eLpNorm (hf : AEStronglyMeasurable 
f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用引理 `ENNReal.toReal_essSup`：toReal_essSup {f : α -> Real>=0∞} (h₁ : forallᵐ a
 ∂μ, f a != ⊤) (h₂ : IsBoundedUnder (· <= ·) (ae μ) fun i => (f i).toReal) : (es
sSup f μ).t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用引理 `MeasureTheory.ae_le_lpNorm_exponent_top`：ae_le_lpNorm_exponent_top (hf :
 MemLp f ∞ μ) : forallᵐ x ∂μ, ‖f x‖ <= lpNorm f ∞ μ
-/
lemma lpNorm_exponent_top_eq_essSup (hf : MemLp f ∞ μ) : lpNorm f ∞ μ = essSup (‖f ·‖) μ := by
  simp only [← toReal_eLpNorm hf.aestronglyMeasurable, eLpNorm_exponent_top, eLpNormEssSup]
  refine ENNReal.toReal_essSup (by simp) ⟨lpNorm f ∞ μ, ?_⟩
  simpa [-toReal_enorm, lpNorm] using! ae_le_lpNorm_exponent_top hf

@[simp]
/-
**MeasureTheory.lpNorm_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_zero (p : Real>=0∞) (μ : Measure α) : lpNorm (0 : α -> E) p μ = 0
参数：p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lpNorm_zero (p : ℝ≥0∞) (μ : Measure α) : lpNorm (0 : α → E) p μ = 0 := by simp [lpNorm]

@[simp]
/-
**MeasureTheory.lpNorm_fun_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_fun_zero (p : Real>=0∞) (μ : Measure α) : lpNorm (fun _ => 0 : α ->
 E) p μ = 0
参数：p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `MeasureTheory.eLpNorm_zero'`：eLpNorm_zero' : eLpNorm (fun _ : α => (0 : 
ε)) p μ = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lpNorm_fun_zero (p : ℝ≥0∞) (μ : Measure α) : lpNorm (fun _ ↦ 0 : α → E) p μ = 0 := by
  simp [lpNorm]

@[simp]
/-
**MeasureTheory.lpNorm_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_eq_zero (hf : MemLp f p μ) (hp : p != 0) : lpNorm f p μ = 0 ↔ f =ᵐ[
μ] 0
参数：hf : MemLp f p μ；hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.toReal_eLpNorm`：toReal_eLpNorm (hf : AEStronglyMeasurable 
f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.eLpNorm_eq_zero_iff`：eLpNorm_eq_zero_iff {f : α -> ε} (hf 
: AEStronglyMeasurable f μ) (h0 : p != 0) : eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lpNorm_eq_zero (hf : MemLp f p μ) (hp : p ≠ 0) : lpNorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp [← toReal_eLpNorm hf.aestronglyMeasurable, ENNReal.toReal_eq_zero_iff, hf.eLpNorm_ne_top,
    eLpNorm_eq_zero_iff hf.1 hp]
/-
**MeasureTheory.lpNorm_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup E]   [IsEmpty α] (f : α → E) (p : ENNReal
), MeasureTheory.lpNorm f p μ = 0
参数：f : α → E；p : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `MeasureTheory.lpNorm_zero`：lpNorm_zero (p : Real>=0∞) (μ : Measure α) : 
lpNorm (0 : α -> E) p μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : lpNorm f p μ = 0 := by
  simp [Subsingleton.elim f 0]
/-
**MeasureTheory.lpNorm_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} [inst : NormedAddC
ommGroup E] (f : α → E) (p : ENNReal)   (μ : MeasureTheory.Measure α), MeasureTh
eory.lpNorm (-f) p μ = MeasureTheory.lpNorm f p μ
参数：f : α → E；p : ENNReal；μ : MeasureTheory.Measure α；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEStronglyMeasurable.neg`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.lpNorm_of_not_aestronglyMeasurable`：lpNorm_of_not_aestrong
lyMeasurable (hf : ¬ AEStronglyMeasurable f μ) : lpNorm f p μ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
@[simp] lemma lpNorm_neg (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (-f) p μ = lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.neg]
  · rw [lpNorm_of_not_aestronglyMeasurable hf,
      lpNorm_of_not_aestronglyMeasurable fun h ↦ hf <| by simpa using h.neg]
/-
**MeasureTheory.lpNorm_fun_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} [inst : NormedAddC
ommGroup E] (f : α → E) (p : ENNReal)   (μ : MeasureTheory.Measure α), MeasureTh
eory.lpNorm (fun x => -f x) p μ = MeasureTheory.lpNorm f p μ
参数：f : α → E；p : ENNReal；μ : MeasureTheory.Measure α；fun x => -f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lpNorm_neg`：∀ {α : Type u_1} {E : Type u_2} {m : Measurabl
eSpace α} [inst : NormedAddCommGroup E] (f : α → E) (p : ENNReal)   (μ : Measure
Theory.Measure…
-/
@[simp] lemma lpNorm_fun_neg (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (fun x ↦ -f x) p μ = lpNorm f p μ := lpNorm_neg ..
/-
**MeasureTheory.lpNorm_sub_comm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_sub_comm (f g : α -> E) (p : Real>=0∞) (μ : Measure α) : lpNorm (f 
- g) p μ = lpNorm (g - f) p μ
参数：f g : α -> E；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lpNorm_neg`：∀ {α : Type u_1} {E : Type u_2} {m : Measurabl
eSpace α} [inst : NormedAddCommGroup E] (f : α → E) (p : ENNReal)   (μ : Measure
Theory.Measure…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (f - g) p μ = lpNorm (g - f) p μ := by rw [← lpNorm_neg]; simp
/-
**MeasureTheory.lpNorm_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : NormedAddCommGroup E]   {f : α → E},   MeasureTheory.AEStron
glyMeasurable f μ →     ∀ (p : ENNReal), MeasureTheory.lpNorm (fun x => ‖f x‖) p
 μ = MeasureTheory.lpNorm f p μ
参数：p : ENNReal；fun x => ‖f x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.toReal_eLpNorm`：toReal_eLpNorm (hf : AEStronglyMeasurable 
f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.eLpNorm_norm`：eLpNorm_norm (f : α -> F) : eLpNorm (fun x =
> ‖f x‖) p μ = eLpNorm f p μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lpNorm_norm (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    lpNorm (fun x ↦ ‖f x‖) p μ = lpNorm f p μ := by
  rw [← toReal_eLpNorm hf, ← toReal_eLpNorm (by fun_prop)]; simp
/-
**MeasureTheory.lpNorm_abs** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   MeasureTheory.AEStronglyMeasurable f μ → ∀ (p : ENNReal), MeasureThe
ory.lpNorm |f| p μ = MeasureTheory.lpNorm f p μ
参数：p : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lpNorm_norm`：∀ {α : Type u_1} {E : Type u_2} {m : Measurab
leSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup E]   {f : α 
→ E},   Measure…
-/
@[simp] lemma lpNorm_abs {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    lpNorm (|f|) p μ = lpNorm f p μ := lpNorm_norm hf p
/-
**MeasureTheory.lpNorm_fun_abs** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f 
: α → ℝ},   MeasureTheory.AEStronglyMeasurable f μ →     ∀ (p : ENNReal), Measur
eTheory.lpNorm (fun x => |f x|) p μ = MeasureTheory.lpNorm f p μ
参数：p : ENNReal；fun x => |f x|。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lpNorm_abs`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : 
MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.AEStronglyMeasurable f μ →
 ∀ (p : ENNRea…
-/
@[simp] lemma lpNorm_fun_abs {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    lpNorm (fun x ↦ |f x|) p μ = lpNorm f p μ := lpNorm_abs hf _
/-
**MeasureTheory.lpNorm_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E],   p ≠ 0 → μ ≠ 0 → ∀ (
c : E), MeasureTheory.lpNorm (fun _x => c) p μ = ‖c‖ * μ.real Set.univ ^ p.toRea
l⁻¹
参数：c : E；fun _x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `MeasureTheory.eLpNorm_const`：eLpNorm_const (c : ε) (h0 : p != 0) (hμ : μ
 != 0) : eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal 
p)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `ENNReal.toReal_rpow`：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ 
z = (x ^ z).toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lpNorm_const (hp : p ≠ 0) (hμ : μ ≠ 0) (c : E) :
    lpNorm (fun _x ↦ c) p μ = ‖c‖ * μ.real .univ ^ p.toReal⁻¹ := by
  simp [lpNorm, eLpNorm_const c hp hμ, Measure.real, ENNReal.toReal_rpow,
    aestronglyMeasurable_const]
/-
**MeasureTheory.lpNorm_const'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} {p : ENNReal} {μ :
 MeasureTheory.Measure α}   [inst : NormedAddCommGroup E],   p ≠ 0 → p ≠ ⊤ → ∀ (
c : E), MeasureTheory.lpNorm (fun _x => c) p μ = ‖c‖ * μ.real Set.univ ^ p.toRea
l⁻¹
参数：c : E；fun _x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `MeasureTheory.eLpNorm_const'`：eLpNorm_const' (c : ε) (h0 : p != 0) (h_to
p : p != ∞) : eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.to
Real p)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `ENNReal.toReal_rpow`：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ 
z = (x ^ z).toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lpNorm_const' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (c : E) :
    lpNorm (fun _x ↦ c) p μ = ‖c‖ * μ.real .univ ^ p.toReal⁻¹ := by
  simp [lpNorm, eLpNorm_const' c hp₀ hp, Measure.real, ENNReal.toReal_rpow,
    aestronglyMeasurable_const]

section NormedField
variable {𝕜 : Type*} [NormedField 𝕜]

/-
**MeasureTheory.lpNorm_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.
Measure α} {𝕜 : Type u_3}   [inst : NormedField 𝕜], p ≠ 0 → μ ≠ 0 → MeasureTheor
y.lpNorm 1 p μ = μ.real Set.univ ^ p.toReal⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lpNorm_const`：∀ {α : Type u_1} {E : Type u_2} {m : Measura
bleSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommG
roup E],   p ≠ 0…
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `ENNReal.toReal_rpow`：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ 
z = (x ^ z).toReal
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lpNorm_one (hp : p ≠ 0) (hμ : μ ≠ 0) :
    lpNorm (1 : α → 𝕜) p μ = μ.real .univ ^ (p.toReal⁻¹ : ℝ) := by
  simp [Pi.one_def, lpNorm_const hp hμ, Measure.real, ENNReal.toReal_rpow]
/-
**MeasureTheory.lpNorm_one'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p : ENNReal} {𝕜 : Type u_3} [ins
t : NormedField 𝕜],   p ≠ 0 → p ≠ ⊤ → ∀ (μ : MeasureTheory.Measure α), MeasureTh
eory.lpNorm 1 p μ = μ.real Set.univ ^ p.toReal⁻¹
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lpNorm_const'`：∀ {α : Type u_1} {E : Type u_2} {m : Measur
ableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddComm
Group E],   p ≠ 0…
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `ENNReal.toReal_rpow`：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ 
z = (x ^ z).toReal
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lpNorm_one' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (μ : Measure α) :
    lpNorm (1 : α → 𝕜) p μ = μ.real .univ ^ (p.toReal⁻¹ : ℝ) := by
  simp [Pi.one_def, lpNorm_const' hp₀ hp, Measure.real, ENNReal.toReal_rpow]
/-
**MeasureTheory.lpNorm_const_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α -> E) (μ
 : Measure α) : lpNorm (c • f) p μ = ‖c‖₊ * lpNorm f p μ
参数：c : 𝕜；f : α -> E；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} {𝕜 : Type…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.eLpNorm_const_smul`：eLpNorm_const_smul (c : 𝕜) (f : α -> F
) (p : Real>=0∞) (μ : Measure α) : eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `MeasureTheory.lpNorm_zero`：lpNorm_zero (p : Real>=0∞) (μ : Measure α) : 
lpNorm (0 : α -> E) p μ = 0
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.lpNorm_of_not_aestronglyMeasurable`：lpNorm_of_not_aestrong
lyMeasurable (hf : ¬ AEStronglyMeasurable f μ) : lpNorm f p μ = 0
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma lpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α → E) (μ : Measure α) :
    lpNorm (c • f) p μ = ‖c‖₊ * lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [lpNorm, eLpNorm_const_smul, hf, hf.const_smul]
  obtain rfl | hc := eq_or_ne c 0
  · simp
  rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h ↦ hf <| by
    simpa [hc] using h.const_smul c⁻¹]
  simp
/-
**MeasureTheory.lpNorm_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_nsmul [NormedSpace Real E] (n : Nat) (f : α -> E) (μ : Measure α) :
 lpNorm (n • f) p μ = n • lpNorm f p μ
参数：n : Nat；f : α -> E；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.nnnorm_natCast`：∀ (n : ℕ), ‖↑n‖₊ = ↑n
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用引理 `MeasureTheory.lpNorm_const_smul`：lpNorm_const_smul [Module 𝕜 E] [NormSMu
lClass 𝕜 E] (c : 𝕜) (f : α -> E) (μ : Measure α) : lpNorm (c • f) p μ = ‖c‖₊ * l
pNorm f p μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
-/
lemma lpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (μ : Measure α) :
    lpNorm (n • f) p μ = n • lpNorm f p μ := by
  simpa [Nat.cast_smul_eq_nsmul] using lpNorm_const_smul (n : ℝ) f μ (p := p)

variable [NormedSpace ℝ 𝕜]
/-
**MeasureTheory.lpNorm_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_natCast_mul (n : Nat) (f : α -> 𝕜) (p : Real>=0∞) (μ : Measure α) :
 lpNorm ((n : α -> 𝕜) * f) p μ = n * lpNorm f p μ
参数：n : Nat；f : α -> 𝕜；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用引理 `MeasureTheory.lpNorm_nsmul`：lpNorm_nsmul [NormedSpace Real E] (n : Nat) 
(f : α -> E) (μ : Measure α) : lpNorm (n • f) p μ = n • lpNorm f p μ
-/
lemma lpNorm_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm ((n : α → 𝕜) * f) p μ = n * lpNorm f p μ := by
  simpa only [nsmul_eq_mul] using lpNorm_nsmul n f μ
/-
**MeasureTheory.lpNorm_fun_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：lpNorm_fun_natCast_mul (n : Nat) (f : α -> 𝕜) (p : Real>=0∞) (μ : Measure 
α) : lpNorm (n * f ·) p μ = n * lpNorm f p μ
参数：n : Nat；f : α -> 𝕜；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.lpNorm_natCast_mul`：lpNorm_natCast_mul (n : Nat) (f : α ->
 𝕜) (p : Real>=0∞) (μ : Measure α) : lpNorm ((n : α -> 𝕜) * f) p μ = n * lpNorm 
f p μ
-/
lemma lpNorm_fun_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (n * f ·) p μ = n * lpNorm f p μ := lpNorm_natCast_mul ..
/-
**MeasureTheory.lpNorm_mul_natCast** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_mul_natCast (f : α -> 𝕜) (n : Nat) (p : Real>=0∞) (μ : Measure α) :
 lpNorm (f * (n : α -> 𝕜)) p μ = lpNorm f p μ * n
参数：f : α -> 𝕜；n : Nat；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `MeasureTheory.lpNorm_natCast_mul`：lpNorm_natCast_mul (n : Nat) (f : α ->
 𝕜) (p : Real>=0∞) (μ : Measure α) : lpNorm ((n : α -> 𝕜) * f) p μ = n * lpNorm 
f p μ
-/
lemma lpNorm_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (f * (n : α → 𝕜)) p μ = lpNorm f p μ * n := by
  simpa only [mul_comm] using lpNorm_natCast_mul n f p μ
/-
**MeasureTheory.lpNorm_fun_mul_natCast** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：lpNorm_fun_mul_natCast (f : α -> 𝕜) (n : Nat) (p : Real>=0∞) (μ : Measure 
α) : lpNorm (f · * n) p μ = lpNorm f p μ * n
参数：f : α -> 𝕜；n : Nat；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.lpNorm_mul_natCast`：lpNorm_mul_natCast (f : α -> 𝕜) (n : N
at) (p : Real>=0∞) (μ : Measure α) : lpNorm (f * (n : α -> 𝕜)) p μ = lpNorm f p 
μ * n
-/
lemma lpNorm_fun_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (f · * n) p μ = lpNorm f p μ * n := lpNorm_mul_natCast ..
/-
**MeasureTheory.lpNorm_div_natCast** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_div_natCast [CharZero 𝕜] {n : Nat} (hn : n != 0) (f : α -> 𝕜) (p : 
Real>=0∞) (μ : Measure α) : lpNorm (f / (n : α -> 𝕜)) p μ = lpNorm f p μ / n
参数：hn : n != 0；f : α -> 𝕜；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.lpNorm_mul_natCast`：lpNorm_mul_natCast (f : α -> 𝕜) (n : N
at) (p : Real>=0∞) (μ : Measure α) : lpNorm (f * (n : α -> 𝕜)) p μ = lpNorm f p 
μ * n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lpNorm_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞)
    (μ : Measure α) : lpNorm (f / (n : α → 𝕜)) p μ = lpNorm f p μ / n := by
  rw [eq_div_iff (by positivity), ← lpNorm_mul_natCast]; simp [Pi.mul_def, hn]
/-
**MeasureTheory.lpNorm_fun_div_natCast** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：lpNorm_fun_div_natCast [CharZero 𝕜] {n : Nat} (hn : n != 0) (f : α -> 𝕜) (
p : Real>=0∞) (μ : Measure α) : lpNorm (f · / n) p μ = lpNorm f p μ / n
参数：hn : n != 0；f : α -> 𝕜；p : Real>=0∞；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.lpNorm_div_natCast`：lpNorm_div_natCast [CharZero 𝕜] {n : N
at} (hn : n != 0) (f : α -> 𝕜) (p : Real>=0∞) (μ : Measure α) : lpNorm (f / (n :
 α -> 𝕜)) p μ = lpNorm…
-/
lemma lpNorm_fun_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞)
    (μ : Measure α) : lpNorm (f · / n) p μ = lpNorm f p μ / n := lpNorm_div_natCast hn ..

end NormedField

/-
**MeasureTheory.lpNorm_add_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_add_le (hf : MemLp f p μ) (hp : 1 <= p) : lpNorm (f + g) p μ <= lpN
orm f p μ + lpNorm g p μ
参数：hf : MemLp f p μ；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.toReal_eLpNorm`：toReal_eLpNorm (hf : AEStronglyMeasurable 
f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用定理 `MeasureTheory.eLpNorm_add_le`：eLpNorm_add_le (hf : AEStronglyMeasurable 
f μ) (hg : AEStronglyMeasurable g μ) (hp1 : 1 <= p) : eLpNorm (f + g) p μ <= eLp
Norm f p μ + eLpNo…
· 使用引理 `MeasureTheory.lpNorm_of_not_memLp`：lpNorm_of_not_memLp (hf' : ¬ MemLp f 
p μ) : lpNorm f p μ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma lpNorm_add_le (hf : MemLp f p μ) (hp : 1 ≤ p) :
    lpNorm (f + g) p μ ≤ lpNorm f p μ + lpNorm g p μ := by
  by_cases hg : MemLp g p μ
  · rw [← toReal_eLpNorm (hf.add hg).aestronglyMeasurable,
      ← toReal_eLpNorm hf.aestronglyMeasurable, ← toReal_eLpNorm hg.aestronglyMeasurable,
      ← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
    gcongr
    exacts [ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩,
      eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable hp]
  · rw [lpNorm_of_not_memLp fun hfg ↦ hg <| by simpa using hfg.sub hf, lpNorm_of_not_memLp hg]
    simp
/-
**MeasureTheory.lpNorm_add_le'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_add_le' (hg : MemLp g p μ) (hp : 1 <= p) : lpNorm (f + g) p μ <= lp
Norm f p μ + lpNorm g p μ
参数：hg : MemLp g p μ；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `MeasureTheory.lpNorm_add_le`：lpNorm_add_le (hf : MemLp f p μ) (hp : 1 <=
 p) : lpNorm (f + g) p μ <= lpNorm f p μ + lpNorm g p μ
-/
lemma lpNorm_add_le' (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm (f + g) p μ ≤ lpNorm f p μ + lpNorm g p μ := by
  simpa [add_comm] using lpNorm_add_le hg (g := f) hp
/-
**MeasureTheory.lpNorm_sub_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_sub_le (hf : MemLp f p μ) (hp : 1 <= p) : lpNorm (f - g) p μ <= lpN
orm f p μ + lpNorm g p μ
参数：hf : MemLp f p μ；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.lpNorm_neg`：∀ {α : Type u_1} {E : Type u_2} {m : Measurabl
eSpace α} [inst : NormedAddCommGroup E] (f : α → E) (p : ENNReal)   (μ : Measure
Theory.Measure…
· 使用引理 `MeasureTheory.lpNorm_add_le`：lpNorm_add_le (hf : MemLp f p μ) (hp : 1 <=
 p) : lpNorm (f + g) p μ <= lpNorm f p μ + lpNorm g p μ
-/
lemma lpNorm_sub_le (hf : MemLp f p μ) (hp : 1 ≤ p) :
    lpNorm (f - g) p μ ≤ lpNorm f p μ + lpNorm g p μ := by
  simpa [sub_eq_add_neg] using lpNorm_add_le hf (g := -g) hp
/-
**MeasureTheory.lpNorm_le_lpNorm_add_lpNorm_sub'** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：lpNorm_le_lpNorm_add_lpNorm_sub' (hg : MemLp g p μ) (hp : 1 <= p) : lpNorm
 f p μ <= lpNorm g p μ + lpNorm (f - g) p μ
参数：hg : MemLp g p μ；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用引理 `MeasureTheory.lpNorm_add_le`：lpNorm_add_le (hf : MemLp f p μ) (hp : 1 <=
 p) : lpNorm (f + g) p μ <= lpNorm f p μ + lpNorm g p μ
-/
lemma lpNorm_le_lpNorm_add_lpNorm_sub' (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm f p μ ≤ lpNorm g p μ + lpNorm (f - g) p μ := by
  simpa using lpNorm_add_le hg (g := f - g) hp
/-
**MeasureTheory.lpNorm_le_lpNorm_add_lpNorm_sub** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：lpNorm_le_lpNorm_add_lpNorm_sub (hg : MemLp g p μ) (hp : 1 <= p) : lpNorm 
f p μ <= lpNorm g p μ + lpNorm (g - f) p μ
参数：hg : MemLp g p μ；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `MeasureTheory.lpNorm_neg`：∀ {α : Type u_1} {E : Type u_2} {m : Measurabl
eSpace α} [inst : NormedAddCommGroup E] (f : α → E) (p : ENNReal)   (μ : Measure
Theory.Measure…
· 使用引理 `MeasureTheory.lpNorm_add_le`：lpNorm_add_le (hf : MemLp f p μ) (hp : 1 <=
 p) : lpNorm (f + g) p μ <= lpNorm f p μ + lpNorm g p μ
· 使用定理 `MeasureTheory.MemLp.neg`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f : α …
-/
lemma lpNorm_le_lpNorm_add_lpNorm_sub (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm f p μ ≤ lpNorm g p μ + lpNorm (g - f) p μ := by
  simpa [neg_add_eq_sub] using lpNorm_add_le hg.neg (g := g - f) hp
/-
**MeasureTheory.lpNorm_le_add_lpNorm_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：lpNorm_le_add_lpNorm_add (hg : MemLp g p μ) (hp : 1 <= p) : lpNorm f p μ <
= lpNorm (f + g) p μ + lpNorm g p μ
参数：hg : MemLp g p μ；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `MeasureTheory.lpNorm_neg`：∀ {α : Type u_1} {E : Type u_2} {m : Measurabl
eSpace α} [inst : NormedAddCommGroup E] (f : α → E) (p : ENNReal)   (μ : Measure
Theory.Measure…
· 使用引理 `MeasureTheory.lpNorm_add_le'`：lpNorm_add_le' (hg : MemLp g p μ) (hp : 1 
<= p) : lpNorm (f + g) p μ <= lpNorm f p μ + lpNorm g p μ
· 使用定理 `MeasureTheory.MemLp.neg`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f : α …
-/
lemma lpNorm_le_add_lpNorm_add (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm f p μ ≤ lpNorm (f + g) p μ + lpNorm g p μ := by
  simpa using lpNorm_add_le' (f := f + g) hg.neg hp
/-
**MeasureTheory.lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (hf : MemLp f p μ) (hg : MemLp g p
 μ) (hp : 1 <= p) : lpNorm (f - h) p μ <= lpNorm (f - g) p μ + lpNorm (g - h) p 
μ
参数：hf : MemLp f p μ；hg : MemLp g p μ；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用引理 `MeasureTheory.lpNorm_add_le`：lpNorm_add_le (hf : MemLp f p μ) (hp : 1 <=
 p) : lpNorm (f + g) p μ <= lpNorm f p μ + lpNorm g p μ
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…
-/
lemma lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub (hf : MemLp f p μ) (hg : MemLp g p μ) (hp : 1 ≤ p) :
    lpNorm (f - h) p μ ≤ lpNorm (f - g) p μ + lpNorm (g - h) p μ := by
  simpa using lpNorm_add_le (hf.sub hg) (g := g - h) hp
/-
**MeasureTheory.lpNorm_sum_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι -> α -> E} (hf : forall i 
in s, MemLp (f i) p μ) (hp : 1 <= p) : lpNorm (∑ i in s, f i) p μ <= ∑ i in s, l
pNorm (f i) p μ
参数：hf : forall i in s, MemLp (f i) p μ；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `MeasureTheory.toReal_eLpNorm`：toReal_eLpNorm (hf : AEStronglyMeasurable 
f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `ENNReal.toReal_sum`：toReal_sum {s : Finset α} {f : α -> Real>=0∞} (hf : 
forall a in s, f a != ∞) : ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.to
Real (f …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.aestronglyMeasurable_sum`：∀ {α : Type u_1} {m₀ : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {M : Type u_5} [inst : AddCommMonoid M]   [inst
_1 : TopologicalSpace…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.eLpNorm_sum_le`：eLpNorm_sum_le [ContinuousAdd ε'] {ι} {f :
 ι -> α -> ε'} {s : Finset ι} (hfs : forall i, i in s -> AEStronglyMeasurable (f
 i) μ) (hp1 : 1 <=…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma lpNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι → α → E} (hf : ∀ i ∈ s, MemLp (f i) p μ)
    (hp : 1 ≤ p) : lpNorm (∑ i ∈ s, f i) p μ ≤ ∑ i ∈ s, lpNorm (f i) p μ := by
  rw [← Finset.sum_congr rfl fun i hi ↦ toReal_eLpNorm (hf i hi).aestronglyMeasurable,
    ← ENNReal.toReal_sum fun i hi ↦ (hf i hi).2.ne,
    ← toReal_eLpNorm (Finset.aestronglyMeasurable_sum _ fun i hi ↦ (hf i hi).aestronglyMeasurable)]
  grw [eLpNorm_sum_le (fun i hi ↦ (hf _ hi).aestronglyMeasurable) hp]
  simpa using fun i hi ↦ (hf i hi).2.ne

-- TODO: Golf using `eLpNorm_expect_le` once it exists
/-
**MeasureTheory.lpNorm_expect_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_expect_le [Module Rat>=0 E] [NormedSpace Real E] {ι : Type*} {s : F
inset ι} {f : ι -> α -> E} (hf : forall i in s, MemLp (f i) p μ) (hp : 1 <= p) :
 lpNorm (𝔼 i in s, f i) p μ <= 𝔼 i in s, lpNorm (f i) p μ
参数：hf : forall i in s, MemLp (f i) p μ；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.expect_empty`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] (f : ι → M),   (∅.expect fun i => f i) = 0
· 使用引理 `MeasureTheory.lpNorm_zero`：lpNorm_zero (p : Real>=0∞) (μ : Measure α) : 
lpNorm (0 : α -> E) p μ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_inv_smul_iff_of_pos`：le_inv_smul_iff_of_pos [PosSMulMono α β] [PosSMu
lReflectLE α β] (ha : 0 < a) : b₁ <= a⁻¹ • b₂ ↔ a • b₁ <= b₂
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `MeasureTheory.lpNorm_nsmul`：lpNorm_nsmul [NormedSpace Real E] (n : Nat) 
(f : α -> E) (μ : Measure α) : lpNorm (n • f) p μ = n • lpNorm f p μ
· 使用引理 `Finset.card_smul_expect`：card_smul_expect (s : Finset ι) (f : ι -> M) : 
#s • 𝔼 i in s, f i = ∑ i in s, f i
· 使用引理 `MeasureTheory.lpNorm_sum_le`：lpNorm_sum_le {ι : Type*} {s : Finset ι} {f
 : ι -> α -> E} (hf : forall i in s, MemLp (f i) p μ) (hp : 1 <= p) : lpNorm (∑ 
i in s, f i) p μ …
-/
lemma lpNorm_expect_le [Module ℚ≥0 E] [NormedSpace ℝ E] {ι : Type*} {s : Finset ι}
    {f : ι → α → E} (hf : ∀ i ∈ s, MemLp (f i) p μ) (hp : 1 ≤ p) :
    lpNorm (𝔼 i ∈ s, f i) p μ ≤ 𝔼 i ∈ s, lpNorm (f i) p μ := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  refine (le_inv_smul_iff_of_pos <| by positivity).2 ?_
  rw [Nat.cast_smul_eq_nsmul, ← lpNorm_nsmul, Finset.card_smul_expect]
  exact lpNorm_sum_le hf hp
/-
**MeasureTheory.lpNorm_mono_real** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lpNorm_mono_real {g : α -> Real} (hg : MemLp g p μ) (h : forall x, ‖f x‖ <
= g x) : lpNorm f p μ <= lpNorm g p μ
参数：hg : MemLp g p μ；h : forall x, ‖f x‖ <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.toReal_eLpNorm`：toReal_eLpNorm (hf : AEStronglyMeasurable 
f μ) : (eLpNorm f p μ).toReal = lpNorm f p μ
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `ENNReal.toNNReal_mono`：toNNReal_mono (hb : b != ∞) (h : a <= b) : a.toNN
Real <= b.toNNReal
· 使用定理 `MeasureTheory.MemLp.eLpNorm_ne_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
· 使用定理 `MeasureTheory.eLpNorm_mono_real`：eLpNorm_mono_real {f : α -> F} {g : α -
> Real} (h : forall x, ‖f x‖ <= g x) : eLpNorm f p μ <= eLpNorm g p μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.lpNorm_of_not_aestronglyMeasurable`：lpNorm_of_not_aestrong
lyMeasurable (hf : ¬ AEStronglyMeasurable f μ) : lpNorm f p μ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma lpNorm_mono_real {g : α → ℝ} (hg : MemLp g p μ) (h : ∀ x, ‖f x‖ ≤ g x) :
    lpNorm f p μ ≤ lpNorm g p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hg.aestronglyMeasurable]
    exact ENNReal.toNNReal_mono (hg.eLpNorm_ne_top) (eLpNorm_mono_real h)
  · simp [hf]
/-
**MeasureTheory.lpNorm_smul_measure_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：lpNorm_smul_measure_of_ne_zero {f : α -> E} {c : Real>=0} (hc : c != 0) : 
lpNorm f p (c • μ) = c ^ p.toReal⁻¹ • lpNorm f p μ
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul_measure`：smul_measure {R : Type*
} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : AEStronglyMeasurabl
e f μ) (c : R) : AEStronglyMeasurable…
· 使用引理 `MeasureTheory.eLpNorm_smul_measure_of_ne_zero'`：eLpNorm_smul_measure_of_
ne_zero' {c : Real>=0} (hc : c != 0) (f : α -> ε) (p : Real>=0∞) (μ : Measure α)
 : eLpNorm f p (c • μ) = c ^ p.toRea…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.lpNorm_of_not_aestronglyMeasurable`：lpNorm_of_not_aestrong
lyMeasurable (hf : ¬ AEStronglyMeasurable f μ) : lpNorm f p μ = 0
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma lpNorm_smul_measure_of_ne_zero {f : α → E} {c : ℝ≥0} (hc : c ≠ 0) :
    lpNorm f p (c • μ) = c ^ p.toReal⁻¹ • lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.smul_measure, eLpNorm_smul_measure_of_ne_zero' hc f p μ]
    simp [ENNReal.smul_def, NNReal.smul_def]
  · rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h ↦ hf <| by
      simpa [hc] using h.smul_measure c⁻¹]
    simp
/-
**MeasureTheory.lpNorm_smul_measure_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：lpNorm_smul_measure_of_ne_top (hp : p != ∞) {f : α -> E} (c : Real>=0) : l
pNorm f p (c • μ) = c ^ p.toReal⁻¹ • lpNorm f p μ
参数：hp : p != ∞；c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.AEStronglyMeasurable.smul_measure`：smul_measure {R : Type*
} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : AEStronglyMeasurabl
e f μ) (c : R) : AEStronglyMeasurable…
· 使用引理 `MeasureTheory.eLpNorm_smul_measure_of_ne_top'`：eLpNorm_smul_measure_of_n
e_top' (hp : p != ∞) (c : Real>=0) (f : α -> ε) : eLpNorm f p (c • μ) = c ^ p.to
Real⁻¹ • eLpNorm f p μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MeasureTheory.lpNorm_exponent_zero`：∀ {α : Type u_1} {E : Type u_2} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup E] 
  (f : α → E), MeasureTh…
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.lpNorm_measure_zero`：∀ {α : Type u_1} {E : Type u_2} {m : 
MeasurableSpace α} {p : ENNReal} [inst : NormedAddCommGroup E] (f : α → E),   Me
asureTheory.lpNorm f p …
· 使用引理 `MeasureTheory.lpNorm_of_not_aestronglyMeasurable`：lpNorm_of_not_aestrong
lyMeasurable (hf : ¬ AEStronglyMeasurable f μ) : lpNorm f p μ = 0
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
lemma lpNorm_smul_measure_of_ne_top (hp : p ≠ ∞) {f : α → E} (c : ℝ≥0) :
    lpNorm f p (c • μ) = c ^ p.toReal⁻¹ • lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · simp [← toReal_eLpNorm, hf, hf.smul_measure, eLpNorm_smul_measure_of_ne_top' hp]
    simp [ENNReal.smul_def, NNReal.smul_def]
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain rfl | hc := eq_or_ne c 0
  · rw [NNReal.zero_rpow (by simp [ENNReal.toReal_eq_zero_iff, *])]
    simp
  rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h ↦ hf <| by
    simpa [hc] using h.smul_measure c⁻¹]
  simp
/-
**MeasureTheory.lpNorm_conj** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {K : Type u_3} [inst : RCLike K] 
(f : α → K) (p : ENNReal)   (μ : MeasureTheory.Measure α), MeasureTheory.lpNorm 
((starRingEnd (α → K)) f) p μ = MeasureTheory.lpNorm f p μ
参数：f : α → K；p : ENNReal；μ : MeasureTheory.Measure α；(starRingEnd (α → K)) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lpNorm_norm`：∀ {α : Type u_1} {E : Type u_2} {m : Measurab
leSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup E]   {f : α 
→ E},   Measure…
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `RCLike.borelSpace`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜], BorelSpace 𝕜
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.lpNorm_of_not_aestronglyMeasurable`：lpNorm_of_not_aestrong
lyMeasurable (hf : ¬ AEStronglyMeasurable f μ) : lpNorm f p μ = 0
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
-/
@[simp] lemma lpNorm_conj {K : Type*} [RCLike K] (f : α → K) (p : ℝ≥0∞) (μ : Measure α) :
    lpNorm (conj f) p μ = lpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← lpNorm_norm hf, ← lpNorm_norm]
    · simp
    · exact (continuous_star.measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  · rw [lpNorm_of_not_aestronglyMeasurable hf, lpNorm_of_not_aestronglyMeasurable fun h ↦ hf ?_]
    simpa [Function.comp_def]
      using (continuous_star.measurable.comp_aemeasurable h.aemeasurable).aestronglyMeasurable

end MeasureTheory

