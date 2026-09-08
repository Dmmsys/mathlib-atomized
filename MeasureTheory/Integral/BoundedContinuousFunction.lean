/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Integration of bounded continuous functions

In this file, some results are collected about integrals of bounded continuous functions. They are
mostly specializations of results in general integration theory, but they are used directly in this
specialized form in some other files, in particular in those related to the topology of weak
convergence of probability measures and finite measures.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

namespace BoundedContinuousFunction

section NNRealValued

variable {X : Type*} [TopologicalSpace X]

/-
**BoundedContinuousFunction.apply_le_nndist_zero** 是 Mathlib 中的一个引理，位于命名空间 `Boun
dedContinuousFunction`。
形式化陈述：apply_le_nndist_zero (f : X ->ᵇ Real>=0) (x : X) : f x <= nndist 0 f
参数：f : X ->ᵇ Real>=0；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.nndist_zero_eq_val`：NNReal.nndist_zero_eq_val (z : Real>=0) : nnd
ist 0 z = z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `BoundedContinuousFunction.nndist_coe_le_nndist`：nndist_coe_le_nndist (x 
: α) : nndist (f x) (g x) <= nndist f g
-/
lemma apply_le_nndist_zero (f : X →ᵇ ℝ≥0) (x : X) :
    f x ≤ nndist 0 f := by
  convert! nndist_coe_le_nndist x
  simp only [coe_zero, Pi.zero_apply, NNReal.nndist_zero_eq_val]
/-
**BoundedContinuousFunction.apply_le_edist_zero** 是 Mathlib 中的一个引理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：apply_le_edist_zero (f : X ->ᵇ Real>=0) (x : X) : f x <= edist 0 f
参数：f : X ->ᵇ Real>=0；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coe_nnreal_ennreal_nndist`：coe_nnreal_ennreal_nndist (x y : α) : ↑(nndis
t x y) = edist x y
· 使用引理 `BoundedContinuousFunction.apply_le_nndist_zero`：apply_le_nndist_zero (f 
: X ->ᵇ Real>=0) (x : X) : f x <= nndist 0 f
-/
lemma apply_le_edist_zero (f : X →ᵇ ℝ≥0) (x : X) :
    f x ≤ edist 0 f := by
  simpa [← ENNReal.coe_le_coe] using f.apply_le_nndist_zero x

variable [MeasurableSpace X]
/-
**BoundedContinuousFunction.lintegral_le_edist_mul** 是 Mathlib 中的一个引理，位于命名空间 `Bo
undedContinuousFunction`。
形式化陈述：lintegral_le_edist_mul (f : X ->ᵇ Real>=0) (μ : Measure X) : (∫⁻ x, f x ∂μ
) <= edist 0 f * (μ Set.univ)
参数：f : X ->ᵇ Real>=0；μ : Measure X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用引理 `BoundedContinuousFunction.apply_le_nndist_zero`：apply_le_nndist_zero (f 
: X ->ᵇ Real>=0) (x : X) : f x <= nndist 0 f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `coe_nnreal_ennreal_nndist`：coe_nnreal_ennreal_nndist (x y : α) : ↑(nndis
t x y) = edist x y
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
-/
lemma lintegral_le_edist_mul (f : X →ᵇ ℝ≥0) (μ : Measure X) :
    (∫⁻ x, f x ∂μ) ≤ edist 0 f * (μ Set.univ) :=
  le_trans (lintegral_mono (fun x ↦ ENNReal.coe_le_coe.mpr (f.apply_le_nndist_zero x))) (by simp)
/-
**BoundedContinuousFunction.measurable_coe_ennreal_comp** 是 Mathlib 中的一个定理，位于命名空
间 `BoundedContinuousFunction`。
形式化陈述：measurable_coe_ennreal_comp [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0) :
 Measurable fun x => (f x : Real>=0∞)
参数：f : X ->ᵇ Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_coe_nnreal_ennreal`：measurable_coe_nnreal_ennreal : Measurabl
e ((↑) : Real>=0 -> Real>=0∞)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
-/
theorem measurable_coe_ennreal_comp [OpensMeasurableSpace X] (f : X →ᵇ ℝ≥0) :
    Measurable fun x ↦ (f x : ℝ≥0∞) :=
  measurable_coe_nnreal_ennreal.comp f.continuous.measurable

variable (μ : Measure X) [IsFiniteMeasure μ]
/-
**BoundedContinuousFunction.lintegral_lt_top_of_nnreal** 是 Mathlib 中的一个定理，位于命名空间
 `BoundedContinuousFunction`。
形式化陈述：lintegral_lt_top_of_nnreal (f : X ->ᵇ Real>=0) : ∫⁻ x, f x ∂μ < ∞
参数：f : X ->ᵇ Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] (μ : MeasureTheory.Measure α) [MeasureTheory.IsFinit
eMeasure μ]   {f : α → ENNReal}, (∃ c, ∀ (x …
· 使用定理 `BoundedContinuousFunction.NNReal.upper_bound`：∀ {α : Type u_2} [inst : T
opologicalSpace α] (f : BoundedContinuousFunction α NNReal) (x : α), f x ≤ nndis
t f 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
-/
theorem lintegral_lt_top_of_nnreal (f : X →ᵇ ℝ≥0) : ∫⁻ x, f x ∂μ < ∞ := by
  apply IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
  refine ⟨nndist f 0, fun x ↦ ?_⟩
  have key := BoundedContinuousFunction.NNReal.upper_bound f x
  rwa [ENNReal.coe_le_coe]
/-
**BoundedContinuousFunction.integrable_of_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `Boun
dedContinuousFunction`。
形式化陈述：integrable_of_nnreal [OpensMeasurableSpace X] (f : X ->ᵇ Real>=0) : Integr
able (((↑) : Real>=0 -> Real) ∘ ⇑f) μ
参数：f : X ->ᵇ Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.enorm_eq`：∀ (x : NNReal), ‖↑x‖ₑ = ↑x
· 使用定理 `BoundedContinuousFunction.lintegral_lt_top_of_nnreal`：lintegral_lt_top_o
f_nnreal (f : X ->ᵇ Real>=0) : ∫⁻ x, f x ∂μ < ∞
-/
theorem integrable_of_nnreal [OpensMeasurableSpace X] (f : X →ᵇ ℝ≥0) :
    Integrable (((↑) : ℝ≥0 → ℝ) ∘ ⇑f) μ := by
  refine ⟨(NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable, ?_⟩
  simp only [hasFiniteIntegral_iff_enorm, Function.comp_apply, NNReal.enorm_eq]
  exact lintegral_lt_top_of_nnreal _ f
/-
**BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub** 是 Mathlib 中的一个
定理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：integral_eq_integral_nnrealPart_sub [OpensMeasurableSpace X] (f : X ->ᵇ Re
al) : ∫ x, f x ∂μ = (∫ x, (f.nnrealPart x : Real) ∂μ) - ∫ x, ((-f).nnrealPart x 
: Real) ∂μ
参数：f : X ->ᵇ Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `BoundedContinuousFunction.self_eq_nnrealPart_sub_nnrealPart_neg`：self_eq
_nnrealPart_sub_nnrealPart_neg (f : α ->ᵇ Real) : ⇑f = (↑) ∘ f.nnrealPart - (↑) 
∘ (-f).nnrealPart
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq_integral_nnrealPart_sub [OpensMeasurableSpace X] (f : X →ᵇ ℝ) :
    ∫ x, f x ∂μ = (∫ x, (f.nnrealPart x : ℝ) ∂μ) - ∫ x, ((-f).nnrealPart x : ℝ) ∂μ := by
  simp only [f.self_eq_nnrealPart_sub_nnrealPart_neg, Pi.sub_apply, integral_sub,
             integrable_of_nnreal]
  simp only [Function.comp_apply]
/-
**BoundedContinuousFunction.lintegral_of_real_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `
BoundedContinuousFunction`。
形式化陈述：lintegral_of_real_lt_top (f : X ->ᵇ Real) : ∫⁻ x, ENNReal.ofReal (f x) ∂μ 
< ∞
参数：f : X ->ᵇ Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.lintegral_lt_top_of_nnreal`：lintegral_lt_top_o
f_nnreal (f : X ->ᵇ Real>=0) : ∫⁻ x, f x ∂μ < ∞
-/
theorem lintegral_of_real_lt_top (f : X →ᵇ ℝ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ∞ := lintegral_lt_top_of_nnreal _ f.nnrealPart
/-
**BoundedContinuousFunction.toReal_lintegral_coe_eq_integral** 是 Mathlib 中的一个定理，
位于命名空间 `BoundedContinuousFunction`。
形式化陈述：toReal_lintegral_coe_eq_integral [OpensMeasurableSpace X] (f : X ->ᵇ Real>
=0) (μ : Measure X) : (∫⁻ x, (f x : Real>=0∞) ∂μ).toReal = ∫ x, (f x : Real) ∂μ
参数：f : X ->ᵇ Real>=0；μ : Measure X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toReal_lintegral_coe_eq_integral [OpensMeasurableSpace X] (f : X →ᵇ ℝ≥0) (μ : Measure X) :
    (∫⁻ x, (f x : ℝ≥0∞) ∂μ).toReal = ∫ x, (f x : ℝ) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae _ (by simpa [Function.comp_apply] using!
        (NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable)]
  · simp only [ENNReal.ofReal_coe_nnreal]
  · exact Eventually.of_forall (by simp)

end NNRealValued

section BochnerIntegral

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable (μ : Measure X)
variable {E : Type*} [NormedAddCommGroup E]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**BoundedContinuousFunction.lintegral_nnnorm_le** 是 Mathlib 中的一个引理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：lintegral_nnnorm_le (f : X ->ᵇ E) : ∫⁻ x, ‖f x‖₊ ∂μ <= ‖f‖₊ * (μ Set.univ)
参数：f : X ->ᵇ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.coe_le_coe._gcongr_2`：∀ {r q : NNReal}, r ≤ q → ↑r ≤ ↑q
· 使用定理 `BoundedContinuousFunction.nnnorm_coe_le_nnnorm`：nnnorm_coe_le_nnnorm (x 
: α) : ‖f x‖₊ <= ‖f‖₊
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
-/
lemma lintegral_nnnorm_le (f : X →ᵇ E) :
    ∫⁻ x, ‖f x‖₊ ∂μ ≤ ‖f‖₊ * (μ Set.univ) := by
  calc  ∫⁻ x, ‖f x‖₊ ∂μ
    _ ≤ ∫⁻ _, ‖f‖₊ ∂μ       := by gcongr; apply nnnorm_coe_le_nnnorm
    _ = ‖f‖₊ * (μ Set.univ) := by rw [lintegral_const]

variable [OpensMeasurableSpace X] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**BoundedContinuousFunction.integrable** 是 Mathlib 中的一个引理，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：integrable [IsFiniteMeasure μ] (f : X ->ᵇ E) : Integrable f μ
参数：f : X ->ᵇ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.hasFiniteIntegral_def`：hasFiniteIntegral_def {_ : Measurab
leSpace α} (f : α -> ε) (μ : Measure α) : HasFiniteIntegral f μ ↔ (∫⁻ a, ‖f a‖ₑ 
∂μ < ∞)
· 使用引理 `BoundedContinuousFunction.lintegral_nnnorm_le`：lintegral_nnnorm_le (f : 
X ->ᵇ E) : ∫⁻ x, ‖f x‖₊ ∂μ <= ‖f‖₊ * (μ Set.univ)
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
-/
lemma integrable [IsFiniteMeasure μ] (f : X →ᵇ E) :
    Integrable f μ := by
  refine ⟨f.continuous.measurable.aestronglyMeasurable, (hasFiniteIntegral_def _ _).mp ?_⟩
  calc  ∫⁻ x, ‖f x‖₊ ∂μ
    _ ≤ ‖f‖₊ * (μ Set.univ) := f.lintegral_nnnorm_le μ
    _ < ∞                   := ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ Set.univ)

variable [NormedSpace ℝ E]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**BoundedContinuousFunction.norm_integral_le_mul_norm** 是 Mathlib 中的一个引理，位于命名空间 
`BoundedContinuousFunction`。
形式化陈述：norm_integral_le_mul_norm [IsFiniteMeasure μ] (f : X ->ᵇ E) : ‖∫ x, f x ∂μ
‖ <= μ.real Set.univ * ‖f‖
参数：f : X ->ᵇ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
· 使用引理 `MeasureTheory.integral_mono`：integral_mono {f g : α -> E} (hf : Integrab
le f μ) (hg : Integrable g μ) (h : f <= g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_norm_iff`：integrable_norm_iff {f : α -> β} (hf 
: AEStronglyMeasurable f μ) : Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用引理 `BoundedContinuousFunction.integrable`：integrable [IsFiniteMeasure μ] (f 
: X ->ᵇ E) : Integrable f μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
-/
lemma norm_integral_le_mul_norm [IsFiniteMeasure μ] (f : X →ᵇ E) :
    ‖∫ x, f x ∂μ‖ ≤ μ.real Set.univ * ‖f‖ := by
  calc  ‖∫ x, f x ∂μ‖
    _ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _, ‖f‖ ∂μ := ?_
    _ = μ.real Set.univ • ‖f‖ := by rw [integral_const]
  apply integral_mono _ (integrable_const ‖f‖) (fun x ↦ f.norm_coe_le_norm x) -- NOTE: `gcongr`?
  exact (integrable_norm_iff f.continuous.measurable.aestronglyMeasurable).mpr (f.integrable μ)
/-
**BoundedContinuousFunction.norm_integral_le_norm** 是 Mathlib 中的一个引理，位于命名空间 `Bou
ndedContinuousFunction`。
形式化陈述：norm_integral_le_norm [IsProbabilityMeasure μ] (f : X ->ᵇ E) : ‖∫ x, f x ∂
μ‖ <= ‖f‖
参数：f : X ->ᵇ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `BoundedContinuousFunction.norm_integral_le_mul_norm`：norm_integral_le_mu
l_norm [IsFiniteMeasure μ] (f : X ->ᵇ E) : ‖∫ x, f x ∂μ‖ <= μ.real Set.univ * ‖f
‖
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
-/
lemma norm_integral_le_norm [IsProbabilityMeasure μ] (f : X →ᵇ E) :
    ‖∫ x, f x ∂μ‖ ≤ ‖f‖ := by
  convert! f.norm_integral_le_mul_norm μ
  simp
/-
**BoundedContinuousFunction.isBounded_range_integral** 是 Mathlib 中的一个引理，位于命名空间 `
BoundedContinuousFunction`。
形式化陈述：isBounded_range_integral {ι : Type*} (μs : ι -> Measure X) [forall i, IsPr
obabilityMeasure (μs i)] (f : X ->ᵇ E) : Bornology.IsBounded (Set.range (fun i =
> ∫ x, f x ∂(μs i)))
参数：μs : ι -> Measure X；μs i；f : X ->ᵇ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `BoundedContinuousFunction.norm_integral_le_norm`：norm_integral_le_norm [
IsProbabilityMeasure μ] (f : X ->ᵇ E) : ‖∫ x, f x ∂μ‖ <= ‖f‖
-/
lemma isBounded_range_integral
    {ι : Type*} (μs : ι → Measure X) [∀ i, IsProbabilityMeasure (μs i)] (f : X →ᵇ E) :
    Bornology.IsBounded (Set.range (fun i ↦ ∫ x, f x ∂(μs i))) := by
  apply isBounded_iff_forall_norm_le.mpr ⟨‖f‖, fun v hv ↦ ?_⟩
  obtain ⟨i, hi⟩ := hv
  rw [← hi]
  apply f.norm_integral_le_norm (μs i)

end BochnerIntegral

section RealValued

variable {X : Type*} [TopologicalSpace X]
variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-
**BoundedContinuousFunction.integral_add_const** 是 Mathlib 中的一个引理，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：integral_add_const (f : X ->ᵇ Real) (c : Real) : ∫ x, (f + const X c) x ∂μ
 = ∫ x, f x ∂μ + μ.real Set.univ • c
参数：f : X ->ᵇ Real；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `BoundedContinuousFunction.const_apply`：∀ (α : Type u) {β : Type v} [inst
 : TopologicalSpace α] [inst_1 : PseudoMetricSpace β] (b : β),   ⇑(BoundedContin
uousFunction.const α b) = f…
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用引理 `BoundedContinuousFunction.integrable`：integrable [IsFiniteMeasure μ] (f 
: X ->ᵇ E) : Integrable f μ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_add_const (f : X →ᵇ ℝ) (c : ℝ) :
    ∫ x, (f + const X c) x ∂μ = ∫ x, f x ∂μ + μ.real Set.univ • c := by
  simp [integral_add (f.integrable _) (integrable_const c)]
/-
**BoundedContinuousFunction.integral_const_sub** 是 Mathlib 中的一个引理，位于命名空间 `Bounde
dContinuousFunction`。
形式化陈述：integral_const_sub (f : X ->ᵇ Real) (c : Real) : ∫ x, (const X c - f) x ∂μ
 = μ.real Set.univ • c - ∫ x, f x ∂μ
参数：f : X ->ᵇ Real；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instBoundedSub`：∀ {R : Type u_1} [inst : SeminormedAddCommGroup R], Boun
dedSub R
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `BoundedContinuousFunction.const_apply`：∀ (α : Type u) {β : Type v} [inst
 : TopologicalSpace α] [inst_1 : PseudoMetricSpace β] (b : β),   ⇑(BoundedContin
uousFunction.const α b) = f…
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用引理 `BoundedContinuousFunction.integrable`：integrable [IsFiniteMeasure μ] (f 
: X ->ᵇ E) : Integrable f μ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_const_sub (f : X →ᵇ ℝ) (c : ℝ) :
    ∫ x, (const X c - f) x ∂μ = μ.real Set.univ • c - ∫ x, f x ∂μ := by
  simp [integral_sub (integrable_const c) (f.integrable _)]

end RealValued

section tendsto_integral

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-
**BoundedContinuousFunction.tendsto_integral_of_forall_limsup_integral_le_integr
al** 是 Mathlib 中的一个引理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：tendsto_integral_of_forall_limsup_integral_le_integral {ι : Type*} {L : Fi
lter ι} {μ : Measure X} [IsProbabilityMeasure μ] {μs : ι -> Measure X} [forall i
, IsProbabilityMeasure (μs i)] (h : forall f : X ->ᵇ Real, 0 <= f -> L.limsup (f
un i => ∫ x, f x ∂(μs i)) <= ∫ x, f x ∂μ) (f : X ->ᵇ Real) : Tendsto (fun i => ∫
 x, f x ∂(μs i)) L (𝓝 (∫ x, f x ∂μ))
参数：μs i；h : forall f : X ->ᵇ Real, 0 <= f -> L.limsup (fun i => ∫ x, f x ∂(μs i)
) <= ∫ x, f x ∂μ；f : X ->ᵇ Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `BoundedContinuousFunction.isBounded_range_integral`：isBounded_range_inte
gral {ι : Type*} (μs : ι -> Measure X) [forall i, IsProbabilityMeasure (μs i)] (
f : X ->ᵇ E) : Bornology.IsBounded (Set.…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BddAbove.isBoundedUnder`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorde
r α] {f : Filter β} {u : β → α} {s : Set β},   s ∈ f → BddAbove (u '' s) → Filte
r.IsBoundedUn…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Bornology.IsBounded.bddAbove`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dAbove s
· 使用定理 `BddBelow.isBoundedUnder`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorde
r α] {f : Filter β} {u : β → α} {s : Set β},   s ∈ f → BddBelow (u '' s) → Filte
r.IsBoundedUn…
· 使用定理 `Bornology.IsBounded.bddBelow`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dBelow s
· 使用定理 `tendsto_of_le_liminf_of_limsup_le`：tendsto_of_le_liminf_of_limsup_le {f 
: Filter β} {u : β -> α} {a : α} (hinf : a <= liminf u f) (hsup : limsup u f <= 
a) (h : f.IsBoundedUnde…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instBoundedSub`：∀ {R : Type u_1} [inst : SeminormedAddCommGroup R], Boun
dedSub R
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用引理 `BoundedContinuousFunction.norm_sub_nonneg`：norm_sub_nonneg (f : α ->ᵇ Re
al) : 0 <= const _ ‖f‖ - f
· 使用引理 `limsup_const_sub`：limsup_const_sub (F : Filter ι) [AddCommSemigroup R] [
Sub R] [ContinuousSub R] [OrderedSub R] [AddLeftMono R] (f : ι -> R) (c : R) (co
bdd : …
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Filter.IsBounded.isCobounded_ge`：∀ {α : Type u_1} {f : Filter α} [inst :
 Preorder α] [f.NeBot],   Filter.IsBounded (fun x1 x2 => x1 ≤ x2) f → Filter.IsC
obounded (fun x1 x2 =…
· 使用定理 `sub_le_sub_iff_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] [AddRightMono α] {b c : α} (a : α),   a - b ≤ a - c ↔ c ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 49 条，此处仅展示前 30 条）
-/
lemma tendsto_integral_of_forall_limsup_integral_le_integral {ι : Type*} {L : Filter ι}
    {μ : Measure X} [IsProbabilityMeasure μ] {μs : ι → Measure X} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ f : X →ᵇ ℝ, 0 ≤ f → L.limsup (fun i ↦ ∫ x, f x ∂(μs i)) ≤ ∫ x, f x ∂μ)
    (f : X →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, f x ∂(μs i)) L (𝓝 (∫ x, f x ∂μ)) := by
  rcases eq_or_neBot L with rfl | hL
  · simp only [tendsto_bot]
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above := BddAbove.isBoundedUnder L.univ_mem (by simpa using obs.bddAbove)
  have bdd_below := BddBelow.isBoundedUnder L.univ_mem (by simpa using obs.bddBelow)
  apply tendsto_of_le_liminf_of_limsup_le _ _ bdd_above bdd_below
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := limsup_const_sub L (fun i ↦ ∫ x, f x ∂(μs i)) ‖f‖ bdd_above.isCobounded_ge bdd_below
    rwa [this, _root_.sub_le_sub_iff_left ‖f‖] at key
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := limsup_add_const L (fun i ↦ ∫ x, f x ∂(μs i)) ‖f‖ bdd_above bdd_below.isCobounded_le
    rwa [this, add_le_add_iff_right] at key
/-
**BoundedContinuousFunction.tendsto_integral_of_forall_integral_le_liminf_integr
al** 是 Mathlib 中的一个引理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：tendsto_integral_of_forall_integral_le_liminf_integral {ι : Type*} {L : Fi
lter ι} {μ : Measure X} [IsProbabilityMeasure μ] {μs : ι -> Measure X} [forall i
, IsProbabilityMeasure (μs i)] (h : forall f : X ->ᵇ Real, 0 <= f -> ∫ x, f x ∂μ
 <= L.liminf (fun i => ∫ x, f x ∂(μs i))) (f : X ->ᵇ Real) : Tendsto (fun i => ∫
 x, f x ∂(μs i)) L (𝓝 (∫ x, f x ∂μ))
参数：μs i；h : forall f : X ->ᵇ Real, 0 <= f -> ∫ x, f x ∂μ <= L.liminf (fun i => ∫
 x, f x ∂(μs i))；f : X ->ᵇ Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `BoundedContinuousFunction.isBounded_range_integral`：isBounded_range_inte
gral {ι : Type*} (μs : ι -> Measure X) [forall i, IsProbabilityMeasure (μs i)] (
f : X ->ᵇ E) : Bornology.IsBounded (Set.…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BddAbove.isBoundedUnder`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorde
r α] {f : Filter β} {u : β → α} {s : Set β},   s ∈ f → BddAbove (u '' s) → Filte
r.IsBoundedUn…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Bornology.IsBounded.bddAbove`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dAbove s
· 使用定理 `BddBelow.isBoundedUnder`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorde
r α] {f : Filter β} {u : β → α} {s : Set β},   s ∈ f → BddBelow (u '' s) → Filte
r.IsBoundedUn…
· 使用定理 `Bornology.IsBounded.bddBelow`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dBelow s
· 使用定理 `tendsto_of_le_liminf_of_limsup_le`：tendsto_of_le_liminf_of_limsup_le {f 
: Filter β} {u : β -> α} {a : α} (hinf : a <= liminf u f) (hsup : limsup u f <= 
a) (h : f.IsBoundedUnde…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
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
· 使用引理 `BoundedContinuousFunction.add_norm_nonneg`：add_norm_nonneg (f : α ->ᵇ Re
al) : 0 <= f + const _ ‖f‖
· 使用引理 `liminf_add_const`：liminf_add_const (F : Filter ι) [NeBot F] [Add R] [Con
tinuousAdd R] [AddRightMono R] (f : ι -> R) (c : R) (cobdd : F.IsCoboundedUnder 
(· >= …
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Filter.IsBounded.isCobounded_ge`：∀ {α : Type u_1} {f : Filter α} [inst :
 Preorder α] [f.NeBot],   Filter.IsBounded (fun x1 x2 => x1 ≤ x2) f → Filter.IsC
obounded (fun x1 x2 =…
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
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
（共 49 条，此处仅展示前 30 条）
-/
lemma tendsto_integral_of_forall_integral_le_liminf_integral {ι : Type*} {L : Filter ι}
    {μ : Measure X} [IsProbabilityMeasure μ] {μs : ι → Measure X} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ f : X →ᵇ ℝ, 0 ≤ f → ∫ x, f x ∂μ ≤ L.liminf (fun i ↦ ∫ x, f x ∂(μs i)))
    (f : X →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, f x ∂(μs i)) L (𝓝 (∫ x, f x ∂μ)) := by
  rcases eq_or_neBot L with rfl | hL
  · simp only [tendsto_bot]
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above := BddAbove.isBoundedUnder L.univ_mem (by simpa using obs.bddAbove)
  have bdd_below := BddBelow.isBoundedUnder L.univ_mem (by simpa using obs.bddBelow)
  apply @tendsto_of_le_liminf_of_limsup_le ℝ ι _ _ _ L (fun i ↦ ∫ x, f x ∂(μs i)) (∫ x, f x ∂μ)
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := liminf_add_const L (fun i ↦ ∫ x, f x ∂(μs i)) ‖f‖ bdd_above.isCobounded_ge bdd_below
    rwa [this, add_le_add_iff_right] at key
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [probReal_univ, smul_eq_mul, one_mul] at key
    have := liminf_const_sub L (fun i ↦ ∫ x, f x ∂(μs i)) ‖f‖ bdd_above bdd_below.isCobounded_le
    rwa [this, sub_le_sub_iff_left] at key
  · exact bdd_above
  · exact bdd_below

end tendsto_integral --section

end BoundedContinuousFunction

