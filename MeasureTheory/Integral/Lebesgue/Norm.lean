/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Interactions between the Lebesgue integral and norms
-/

public section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-
**MeasureTheory.lintegral_ofReal_le_lintegral_enorm** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：lintegral_ofReal_le_lintegral_enorm (f : α -> Real) : ∫⁻ x, ENNReal.ofReal
 (f x) ∂μ <= ∫⁻ x, ‖f x‖ₑ ∂μ
参数：f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
-/
theorem lintegral_ofReal_le_lintegral_enorm (f : α → ℝ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
  simp_rw [← ofReal_norm]
  refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs]
  exact le_abs_self (f x)
/-
**MeasureTheory.lintegral_enorm_of_ae_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：lintegral_enorm_of_ae_nonneg {f : α -> Real} (h_nonneg : 0 <=ᵐ[μ] f) : ∫⁻ 
x, ‖f x‖ₑ ∂μ = ∫⁻ x, .ofReal (f x) ∂μ
参数：h_nonneg : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
-/
theorem lintegral_enorm_of_ae_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ᵐ[μ] f) :
    ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, .ofReal (f x) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [h_nonneg] with x hx
  rw [Real.enorm_eq_ofReal hx]
/-
**MeasureTheory.lintegral_enorm_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：lintegral_enorm_of_nonneg {f : α -> Real} (h_nonneg : 0 <= f) : ∫⁻ x, ‖f x
‖ₑ ∂μ = ∫⁻ x, .ofReal (f x) ∂μ
参数：h_nonneg : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_enorm_of_ae_nonneg`：lintegral_enorm_of_ae_nonneg
 {f : α -> Real} (h_nonneg : 0 <=ᵐ[μ] f) : ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, .ofReal (f x)
 ∂μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem lintegral_enorm_of_nonneg {f : α → ℝ} (h_nonneg : 0 ≤ f) :
    ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, .ofReal (f x) ∂μ :=
  lintegral_enorm_of_ae_nonneg <| .of_forall h_nonneg

end MeasureTheory

