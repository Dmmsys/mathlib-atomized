/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Probability.Independence.Basic

/-!
# Probability density function

This file defines the probability density function of random variables, by which we mean
measurable functions taking values in a Borel space. The probability density function is defined
as the Radon–Nikodym derivative of the law of `X`. In particular, a measurable function `f`
is said to the probability density function of a random variable `X` if for all measurable
sets `S`, `ℙ(X ∈ S) = ∫ x in S, f x dx`. Probability density functions are one way of describing
the distribution of a random variable, and are useful for calculating probabilities and
finding moments (although the latter is better achieved with moment-generating functions).

This file also defines the continuous uniform distribution and proves some properties about
random variables with this distribution.

## Main definitions

* `MeasureTheory.HasPDF` : A random variable `X : Ω → E` is said to `HasPDF` with
  respect to the measure `ℙ` on `Ω` and `μ` on `E` if the push-forward measure of `ℙ` along `X`
  is absolutely continuous with respect to `μ` and they `HaveLebesgueDecomposition`.
* `MeasureTheory.pdf` : If `X` is a random variable that `HasPDF X ℙ μ`, then `pdf X`
  is the Radon–Nikodym derivative of the push-forward measure of `ℙ` along `X` with respect to `μ`.
* `MeasureTheory.pdf.IsUniform` : A random variable `X` is said to follow the uniform
  distribution if it has a constant probability density function with a compact, non-null support.

## Main results

* `MeasureTheory.pdf.integral_pdf_smul` : Law of the unconscious statistician,
  i.e. if a random variable `X : Ω → E` has pdf `f`, then `𝔼(g(X)) = ∫ x, f x • g x dx` for
  all measurable `g : E → F`.
* `MeasureTheory.pdf.integral_mul_eq_integral` : A real-valued random variable `X` with
  pdf `f` has expectation `∫ x, x * f x dx`.
* `MeasureTheory.pdf.IsUniform.integral_eq` : If `X` follows the uniform distribution with
  its pdf having support `s`, then `X` has expectation `(λ s)⁻¹ * ∫ x in s, x dx` where `λ`
  is the Lebesgue measure.
-/

@[expose] public section


open scoped MeasureTheory NNReal ENNReal

open TopologicalSpace MeasureTheory Measure ProbabilityTheory

noncomputable section

namespace MeasureTheory

variable {Ω E : Type*} [MeasurableSpace E]

/-- A random variable `X : Ω → E` is said to have a probability density function (`HasPDF`)
with respect to the measure `ℙ` on `Ω` and `μ` on `E`
if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `μ`
and they have a Lebesgue decomposition (`HaveLebesgueDecomposition`). -/
/-
**MeasureTheory.HasPDF** 是 Mathlib 中的一个类，位于命名空间 `MeasureTheory`。
形式化陈述：HasPDF {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E
参数：X : Ω -> E；ℙ : Measure Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A random variable `X : Ω → E` is said to have a probability density function (`H
asPDF`)
with respect to the measure `ℙ` on `Ω` and `μ` on `E`
if the push-forward measure of `ℙ` along `X` is absolutely continuous with respe
ct to `μ`
and they have a Lebesgue decomposition (`HaveLebesgueDecomposition`).
-/
class HasPDF {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :
    Prop where
  protected aemeasurable' : AEMeasurable X ℙ
  protected haveLebesgueDecomposition' : (map X ℙ).HaveLebesgueDecomposition μ
  protected absolutelyContinuous' : map X ℙ ≪ μ

section HasPDF

variable {_ : MeasurableSpace Ω} {X Y : Ω → E} {ℙ : Measure Ω} {μ : Measure E}

/-
**MeasureTheory.hasPDF_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hasPDF_iff : HasPDF X ℙ μ ↔ AEMeasurable X ℙ ∧ (map X ℙ).HaveLebesgueDecom
position μ ∧ map X ℙ ≪ μ
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hasPDF_iff :
    HasPDF X ℙ μ ↔ AEMeasurable X ℙ ∧ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ :=
  ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩
/-
**MeasureTheory.hasPDF_iff_of_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：hasPDF_iff_of_aemeasurable (hX : AEMeasurable X ℙ) : HasPDF X ℙ μ ↔ (map X
 ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ
参数：hX : AEMeasurable X ℙ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasPDF_iff`：hasPDF_iff : HasPDF X ℙ μ ↔ AEMeasurable X ℙ ∧
 (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasPDF_iff_of_aemeasurable (hX : AEMeasurable X ℙ) :
    HasPDF X ℙ μ ↔ (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ := by
  rw [hasPDF_iff]
  simp only [hX, true_and]

variable (X ℙ μ) in
/-
**MeasureTheory.HasPDF.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Has
PDF`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} [inst : MeasurableSpace E] {x : Measurable
Space Ω} (X : Ω → E)   (ℙ : MeasureTheory.Measure Ω) (μ : MeasureTheory.Measure 
E) [MeasureTheory.HasPDF X ℙ μ], AEMeasurable X ℙ
参数：X : Ω → E；ℙ : MeasureTheory.Measure Ω；μ : MeasureTheory.Measure E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasPDF.aemeasurable'`：∀ {Ω : Type u_1} {E : Type u_2} {ins
t : MeasurableSpace E} {m : MeasurableSpace Ω} {X : Ω → E}   {ℙ : MeasureTheory.
Measure Ω} (μ : autoPara…
-/
theorem HasPDF.aemeasurable [HasPDF X ℙ μ] : AEMeasurable X ℙ := HasPDF.aemeasurable' μ
/-
**MeasureTheory.HasPDF.haveLebesgueDecomposition** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.HasPDF`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} [inst : MeasurableSpace E] {x : Measurable
Space Ω} {X : Ω → E}   {ℙ : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure 
E} [MeasureTheory.HasPDF X ℙ μ],   (MeasureTheory.Measure.map X ℙ).HaveLebesgueD
ecomposition μ
参数：MeasureTheory.Measure.map X ℙ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasPDF.haveLebesgueDecomposition'`：∀ {Ω : Type u_1} {E : T
ype u_2} {inst : MeasurableSpace E} {m : MeasurableSpace Ω} {X : Ω → E}   {ℙ : M
easureTheory.Measure Ω} {μ : autoPara…
-/
instance HasPDF.haveLebesgueDecomposition [HasPDF X ℙ μ] : (map X ℙ).HaveLebesgueDecomposition μ :=
  HasPDF.haveLebesgueDecomposition'
/-
**MeasureTheory.HasPDF.absolutelyContinuous** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.HasPDF`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} [inst : MeasurableSpace E] {x : Measurable
Space Ω} {X : Ω → E}   {ℙ : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measure 
E} [MeasureTheory.HasPDF X ℙ μ],   (MeasureTheory.Measure.map X ℙ).AbsolutelyCon
tinuous μ
参数：MeasureTheory.Measure.map X ℙ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasPDF.absolutelyContinuous'`：∀ {Ω : Type u_1} {E : Type u
_2} {inst : MeasurableSpace E} {m : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Measur
eTheory.Measure Ω} {μ : autoPara…
-/
theorem HasPDF.absolutelyContinuous [HasPDF X ℙ μ] : map X ℙ ≪ μ := HasPDF.absolutelyContinuous'

/-- A random variable that `HasPDF` is quasi-measure-preserving. -/
/-
**MeasureTheory.HasPDF.quasiMeasurePreserving_of_measurable** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.HasPDF`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} [inst : MeasurableSpace E] {x : Measurable
Space Ω} (X : Ω → E)   (ℙ : MeasureTheory.Measure Ω) (μ : MeasureTheory.Measure 
E) [MeasureTheory.HasPDF X ℙ μ],   Measurable X → MeasureTheory.Measure.QuasiMea
surePreserving X ℙ μ
参数：X : Ω → E；ℙ : MeasureTheory.Measure Ω；μ : MeasureTheory.Measure E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasPDF.absolutelyContinuous`：∀ {Ω : Type u_1} {E : Type u_
2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Measure
Theory.Measure Ω} {μ : MeasureT…

--- 原说明 ---
A random variable that `HasPDF` is quasi-measure-preserving.
-/
theorem HasPDF.quasiMeasurePreserving_of_measurable (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E)
    [HasPDF X ℙ μ] (h : Measurable X) : QuasiMeasurePreserving X ℙ μ :=
  { measurable := h
    absolutelyContinuous := HasPDF.absolutelyContinuous .. }
/-
**MeasureTheory.HasPDF.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.HasPDF`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} [inst : MeasurableSpace E] {x : Measurable
Space Ω} {X Y : Ω → E}   {ℙ : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measur
e E},   X =ᵐ[ℙ] Y → ∀ [hX : MeasureTheory.HasPDF X ℙ μ], MeasureTheory.HasPDF Y 
ℙ μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.congr`：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMe
asurable g μ
· 使用定理 `MeasureTheory.HasPDF.aemeasurable`：∀ {Ω : Type u_1} {E : Type u_2} [inst
 : MeasurableSpace E] {x : MeasurableSpace Ω} (X : Ω → E)   (ℙ : MeasureTheory.M
easure Ω) (μ : MeasureT…
· 使用定理 `MeasureTheory.HasPDF.haveLebesgueDecomposition`：∀ {Ω : Type u_1} {E : Ty
pe u_2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Me
asureTheory.Measure Ω} {μ : MeasureT…
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `MeasureTheory.HasPDF.absolutelyContinuous`：∀ {Ω : Type u_1} {E : Type u_
2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Measure
Theory.Measure Ω} {μ : MeasureT…
-/
theorem HasPDF.congr (hXY : X =ᵐ[ℙ] Y) [hX : HasPDF X ℙ μ] : HasPDF Y ℙ μ :=
  ⟨(HasPDF.aemeasurable X ℙ μ).congr hXY, ℙ.map_congr hXY ▸ hX.haveLebesgueDecomposition,
    ℙ.map_congr hXY ▸ hX.absolutelyContinuous⟩
/-
**MeasureTheory.HasPDF.congr_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.HasPDF
`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} [inst : MeasurableSpace E] {x : Measurable
Space Ω} {X Y : Ω → E}   {ℙ : MeasureTheory.Measure Ω} {μ : MeasureTheory.Measur
e E},   X =ᵐ[ℙ] Y → (MeasureTheory.HasPDF X ℙ μ ↔ MeasureTheory.HasPDF Y ℙ μ)
参数：MeasureTheory.HasPDF X ℙ μ ↔ MeasureTheory.HasPDF Y ℙ μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.HasPDF.congr`：∀ {Ω : Type u_1} {E : Type u_2} [inst : Meas
urableSpace E] {x : MeasurableSpace Ω} {X Y : Ω → E}   {ℙ : MeasureTheory.Measur
e Ω} {μ : Measur…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem HasPDF.congr_iff (hXY : X =ᵐ[ℙ] Y) : HasPDF X ℙ μ ↔ HasPDF Y ℙ μ :=
  ⟨fun _ ↦ HasPDF.congr hXY, fun _ ↦ HasPDF.congr hXY.symm⟩

/-- X `HasPDF` if there is a pdf `f` such that `map X ℙ = μ.withDensity f`. -/
/-
**MeasureTheory.hasPDF_of_map_eq_withDensity** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：hasPDF_of_map_eq_withDensity (hX : AEMeasurable X ℙ) (f : E -> Real>=0∞) (
hf : AEMeasurable f μ) (h : map X ℙ = μ.withDensity f) : HasPDF X ℙ μ
参数：hX : AEMeasurable X ℙ；f : E -> Real>=0∞；hf : AEMeasurable f μ；h : map X ℙ = μ
.withDensity f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_congr_ae`：withDensity_congr_ae {f g : α -> Rea
l>=0∞} (h : f =ᵐ[μ] g) : μ.withDensity f = μ.withDensity g
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_withDensity`：haveLebesgu
eDecomposition_withDensity (μ : Measure α) {f : α -> Real>=0∞} (hf : Measurable 
f) : (μ.withDensity f).HaveLebesgueDecomposition …
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ

--- 原说明 ---
X `HasPDF` if there is a pdf `f` such that `map X ℙ = μ.withDensity f`.
-/
theorem hasPDF_of_map_eq_withDensity (hX : AEMeasurable X ℙ) (f : E → ℝ≥0∞) (hf : AEMeasurable f μ)
    (h : map X ℙ = μ.withDensity f) : HasPDF X ℙ μ := by
  refine ⟨hX, ?_, ?_⟩ <;> rw [h]
  · rw [withDensity_congr_ae hf.ae_eq_mk]
    exact haveLebesgueDecomposition_withDensity μ hf.measurable_mk
  · exact withDensity_absolutelyContinuous μ f

end HasPDF

/-- If `X` is a random variable, then `pdf X ℙ μ`
is the Radon–Nikodym derivative of the push-forward measure of `ℙ` along `X` with respect to `μ`. -/
/-
**MeasureTheory.pdf** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：pdf {_ : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E
参数：X : Ω -> E；ℙ : Measure Ω。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a random variable, then `pdf X ℙ μ`
is the Radon–Nikodym derivative of the push-forward measure of `ℙ` along `X` wit
h respect to `μ`.
-/
def pdf {_ : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :
    E → ℝ≥0∞ :=
  (map X ℙ).rnDeriv μ
/-
**MeasureTheory.pdf_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：pdf_def {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω -> 
E} : pdf X ℙ μ = (map X ℙ).rnDeriv μ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pdf_def {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω → E} :
    pdf X ℙ μ = (map X ℙ).rnDeriv μ := rfl
/-
**MeasureTheory.pdf_of_not_aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：pdf_of_not_aemeasurable {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measu
re E} {X : Ω -> E} (hX : ¬AEMeasurable X ℙ) : pdf X ℙ μ =ᵐ[μ] 0
参数：hX : ¬AEMeasurable X ℙ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.pdf_def`：pdf_def {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {
μ : Measure E} {X : Ω -> E} : pdf X ℙ μ = (map X ℙ).rnDeriv μ
· 使用定理 `MeasureTheory.Measure.map_of_not_aemeasurable`：map_of_not_aemeasurable {
f : α -> β} {μ : Measure α} (hf : ¬AEMeasurable f μ) : μ.map f = 0
· 使用引理 `MeasureTheory.Measure.rnDeriv_zero`：rnDeriv_zero (ν : Measure α) : (0 : 
Measure α).rnDeriv ν =ᵐ[ν] 0
-/
theorem pdf_of_not_aemeasurable {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
    {X : Ω → E} (hX : ¬AEMeasurable X ℙ) : pdf X ℙ μ =ᵐ[μ] 0 := by
  rw [pdf_def, map_of_not_aemeasurable hX]
  exact rnDeriv_zero μ
/-
**MeasureTheory.pdf_of_not_haveLebesgueDecomposition** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：pdf_of_not_haveLebesgueDecomposition {_ : MeasurableSpace Ω} {ℙ : Measure 
Ω} {μ : Measure E} {X : Ω -> E} (h : ¬(map X ℙ).HaveLebesgueDecomposition μ) : p
df X ℙ μ = 0
参数：h : ¬(map X ℙ).HaveLebesgueDecomposition μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.rnDeriv_of_not_haveLebesgueDecomposition`：rnDeriv_
of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) : μ.rnDer
iv ν = 0
-/
theorem pdf_of_not_haveLebesgueDecomposition {_ : MeasurableSpace Ω} {ℙ : Measure Ω}
    {μ : Measure E} {X : Ω → E} (h : ¬(map X ℙ).HaveLebesgueDecomposition μ) : pdf X ℙ μ = 0 :=
  rnDeriv_of_not_haveLebesgueDecomposition h
/-
**MeasureTheory.aemeasurable_of_pdf_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：aemeasurable_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : M
easure E} (X : Ω -> E) (h : ¬pdf X ℙ μ =ᵐ[μ] 0) : AEMeasurable X ℙ
参数：X : Ω -> E；h : ¬pdf X ℙ μ =ᵐ[μ] 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `MeasureTheory.pdf_of_not_aemeasurable`：pdf_of_not_aemeasurable {_ : Meas
urableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω -> E} (hX : ¬AEMeasurable 
X ℙ) : pdf X ℙ μ =ᵐ[μ] 0
-/
theorem aemeasurable_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}
    (X : Ω → E) (h : ¬pdf X ℙ μ =ᵐ[μ] 0) : AEMeasurable X ℙ := by
  contrapose h
  exact pdf_of_not_aemeasurable h
/-
**MeasureTheory.hasPDF_of_pdf_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：hasPDF_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure
 E} {X : Ω -> E} (hac : map X ℙ ≪ μ) (hpdf : ¬pdf X ℙ μ =ᵐ[μ] 0) : HasPDF X ℙ μ
参数：hac : map X ℙ ≪ μ；hpdf : ¬pdf X ℙ μ =ᵐ[μ] 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.aemeasurable_of_pdf_ne_zero`：aemeasurable_of_pdf_ne_zero {
m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} (X : Ω -> E) (h : ¬pdf X 
ℙ μ =ᵐ[μ] 0) : AEMeasurable X ℙ
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `MeasureTheory.pdf_of_not_haveLebesgueDecomposition`：pdf_of_not_haveLebes
gueDecomposition {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω 
-> E} (h : ¬(map X ℙ).HaveLebesgueDecomp…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem hasPDF_of_pdf_ne_zero {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω → E}
    (hac : map X ℙ ≪ μ) (hpdf : ¬pdf X ℙ μ =ᵐ[μ] 0) : HasPDF X ℙ μ := by
  refine ⟨?_, ?_, hac⟩
  · exact aemeasurable_of_pdf_ne_zero X hpdf
  · contrapose hpdf
    have := pdf_of_not_haveLebesgueDecomposition hpdf
    filter_upwards using congrFun this

@[fun_prop]
/-
**MeasureTheory.measurable_pdf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measurable_pdf {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : M
easure E
参数：X : Ω -> E；ℙ : Measure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
-/
theorem measurable_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) : Measurable (pdf X ℙ μ) := by
  exact measurable_rnDeriv _ _
/-
**MeasureTheory.withDensity_pdf_le_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：withDensity_pdf_le_map {_ : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω
) (μ : Measure E
参数：X : Ω -> E；ℙ : Measure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_le`：withDensity_rnDeriv_le (μ 
ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ
-/
theorem withDensity_pdf_le_map {_ : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) : μ.withDensity (pdf X ℙ μ) ≤ map X ℙ :=
  withDensity_rnDeriv_le _ _
/-
**MeasureTheory.setLIntegral_pdf_le_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：setLIntegral_pdf_le_map {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure 
Ω) (μ : Measure E
参数：X : Ω -> E；ℙ : Measure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.withDensity_apply_le`：withDensity_apply_le (f : α -> Real>
=0∞) (s : Set α) : ∫⁻ a in s, f a ∂μ <= μ.withDensity f s
· 使用定理 `MeasureTheory.withDensity_pdf_le_map`：withDensity_pdf_le_map {_ : Measur
ableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E
-/
theorem setLIntegral_pdf_le_map {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) (s : Set E) :
    ∫⁻ x in s, pdf X ℙ μ x ∂μ ≤ map X ℙ s := by
  apply (withDensity_apply_le _ s).trans
  exact withDensity_pdf_le_map _ _ _ s
/-
**MeasureTheory.map_eq_withDensity_pdf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：map_eq_withDensity_pdf {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω
) (μ : Measure E
参数：X : Ω -> E；ℙ : Measure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.pdf_def`：pdf_def {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {
μ : Measure E} {X : Ω -> E} : pdf X ℙ μ = (map X ℙ).rnDeriv μ
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.HasPDF.haveLebesgueDecomposition`：∀ {Ω : Type u_1} {E : Ty
pe u_2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Me
asureTheory.Measure Ω} {μ : MeasureT…
· 使用定理 `MeasureTheory.HasPDF.absolutelyContinuous`：∀ {Ω : Type u_1} {E : Type u_
2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Measure
Theory.Measure Ω} {μ : MeasureT…
-/
theorem map_eq_withDensity_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) [hX : HasPDF X ℙ μ] :
    map X ℙ = μ.withDensity (pdf X ℙ μ) := by
  rw [pdf_def, withDensity_rnDeriv_eq _ _ hX.absolutelyContinuous]
/-
**MeasureTheory.map_eq_setLIntegral_pdf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：map_eq_setLIntegral_pdf {m : MeasurableSpace Ω} (X : Ω -> E) (ℙ : Measure 
Ω) (μ : Measure E
参数：X : Ω -> E；ℙ : Measure Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.map_eq_withDensity_pdf`：map_eq_withDensity_pdf {m : Measur
ableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E
-/
theorem map_eq_setLIntegral_pdf {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω)
    (μ : Measure E := by volume_tac) [hX : HasPDF X ℙ μ] {s : Set E}
    (hs : MeasurableSet s) : map X ℙ s = ∫⁻ x in s, pdf X ℙ μ x ∂μ := by
  rw [← withDensity_apply _ hs, map_eq_withDensity_pdf X ℙ μ]

namespace pdf

variable {m : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E}

/-
**MeasureTheory.pdf.congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.pdf`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} [inst : MeasurableSpace E] {m : Measurable
Space Ω} {ℙ : MeasureTheory.Measure Ω}   {μ : MeasureTheory.Measure E} {X Y : Ω 
→ E}, X =ᵐ[ℙ] Y → MeasureTheory.pdf X ℙ μ = MeasureTheory.pdf Y ℙ μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.pdf_def`：pdf_def {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {
μ : Measure E} {X : Ω -> E} : pdf X ℙ μ = (map X ℙ).rnDeriv μ
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
-/
protected theorem congr {X Y : Ω → E} (hXY : X =ᵐ[ℙ] Y) : pdf X ℙ μ = pdf Y ℙ μ := by
  rw [pdf_def, pdf_def, map_congr hXY]
/-
**MeasureTheory.pdf.lintegral_eq_measure_univ** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.pdf`。
形式化陈述：lintegral_eq_measure_univ {X : Ω -> E} [HasPDF X ℙ μ] : ∫⁻ x, pdf X ℙ μ x 
∂μ = ℙ Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.map_eq_setLIntegral_pdf`：map_eq_setLIntegral_pdf {m : Meas
urableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.Measure.map_apply_of_aemeasurable`：map_apply_of_aemeasurab
le (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f
 ⁻¹' s)
· 使用定理 `MeasureTheory.HasPDF.aemeasurable`：∀ {Ω : Type u_1} {E : Type u_2} [inst
 : MeasurableSpace E] {x : MeasurableSpace Ω} (X : Ω → E)   (ℙ : MeasureTheory.M
easure Ω) (μ : MeasureT…
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
theorem lintegral_eq_measure_univ {X : Ω → E} [HasPDF X ℙ μ] :
    ∫⁻ x, pdf X ℙ μ x ∂μ = ℙ Set.univ := by
  rw [← setLIntegral_univ, ← map_eq_setLIntegral_pdf X ℙ μ MeasurableSet.univ,
    map_apply_of_aemeasurable (HasPDF.aemeasurable X ℙ μ) MeasurableSet.univ, Set.preimage_univ]
/-
**MeasureTheory.pdf.eq_of_map_eq_withDensity** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.pdf`。
形式化陈述：eq_of_map_eq_withDensity [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] (
f : E -> Real>=0∞) (hmf : AEMeasurable f μ) : map X ℙ = μ.withDensity f ↔ pdf X 
ℙ μ =ᵐ[μ] f
参数：f : E -> Real>=0∞；hmf : AEMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.map_eq_withDensity_pdf`：map_eq_withDensity_pdf {m : Measur
ableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E
· 使用定理 `MeasureTheory.withDensity_eq_iff`：withDensity_eq_iff {f g : α -> Real>=0
∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ != ∞) : μ
.withDensity f = μ.wit…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.measurable_pdf`：measurable_pdf {m : MeasurableSpace Ω} (X 
: Ω -> E) (ℙ : Measure Ω) (μ : Measure E
· 使用定理 `MeasureTheory.pdf.lintegral_eq_measure_univ`：lintegral_eq_measure_univ {
X : Ω -> E} [HasPDF X ℙ μ] : ∫⁻ x, pdf X ℙ μ x ∂μ = ℙ Set.univ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem eq_of_map_eq_withDensity [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] (f : E → ℝ≥0∞)
    (hmf : AEMeasurable f μ) : map X ℙ = μ.withDensity f ↔ pdf X ℙ μ =ᵐ[μ] f := by
  rw [map_eq_withDensity_pdf X ℙ μ]
  apply withDensity_eq_iff (measurable_pdf X ℙ μ).aemeasurable hmf
  rw [lintegral_eq_measure_univ]
  exact measure_ne_top _ _
/-
**MeasureTheory.pdf.eq_of_map_eq_withDensity'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.pdf`。
形式化陈述：eq_of_map_eq_withDensity' [SigmaFinite μ] {X : Ω -> E} [HasPDF X ℙ μ] (f :
 E -> Real>=0∞) (hmf : AEMeasurable f μ) : map X ℙ = μ.withDensity f ↔ pdf X ℙ μ
 =ᵐ[μ] f
参数：f : E -> Real>=0∞；hmf : AEMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.withDensity_eq_iff_of_sigmaFinite`：withDensity_eq_iff_of_s
igmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : A
EMeasurable g μ) : μ.withDensity f = …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.measurable_pdf`：measurable_pdf {m : MeasurableSpace Ω} (X 
: Ω -> E) (ℙ : Measure Ω) (μ : Measure E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.map_eq_withDensity_pdf`：map_eq_withDensity_pdf {m : Measur
ableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E
-/
theorem eq_of_map_eq_withDensity' [SigmaFinite μ] {X : Ω → E} [HasPDF X ℙ μ] (f : E → ℝ≥0∞)
    (hmf : AEMeasurable f μ) : map X ℙ = μ.withDensity f ↔ pdf X ℙ μ =ᵐ[μ] f :=
  map_eq_withDensity_pdf X ℙ μ ▸
    withDensity_eq_iff_of_sigmaFinite (measurable_pdf X ℙ μ).aemeasurable hmf

nonrec theorem ae_lt_top [IsFiniteMeasure ℙ] {μ : Measure E} {X : Ω → E} :
    ∀ᵐ x ∂μ, pdf X ℙ μ x < ∞ :=
  rnDeriv_lt_top (map X ℙ) μ

nonrec theorem ofReal_toReal_ae_eq [IsFiniteMeasure ℙ] {X : Ω → E} :
    (fun x => ENNReal.ofReal (pdf X ℙ μ x).toReal) =ᵐ[μ] pdf X ℙ μ :=
  ofReal_toReal_ae_eq ae_lt_top

section IntegralPDFMul

/-- **The Law of the Unconscious Statistician** for nonnegative random variables. -/
/-
**MeasureTheory.pdf.lintegral_pdf_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.p
df`。
形式化陈述：lintegral_pdf_mul {X : Ω -> E} [HasPDF X ℙ μ] {f : E -> Real>=0∞} (hf : AE
Measurable f μ) : ∫⁻ x, pdf X ℙ μ x * f x ∂μ = ∫⁻ x, f (X x) ∂ℙ
参数：hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.pdf_def`：pdf_def {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {
μ : Measure E} {X : Ω -> E} : pdf X ℙ μ = (map X ℙ).rnDeriv μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_map'`：lintegral_map' {f : β -> Real>=0∞} {g : α 
-> β} (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f 
a ∂Measure.map g μ…
· 使用引理 `AEMeasurable.mono_ac`：mono_ac (hf : AEMeasurable f ν) (hμν : μ ≪ ν) : AE
Measurable f μ
· 使用定理 `MeasureTheory.HasPDF.absolutelyContinuous`：∀ {Ω : Type u_1} {E : Type u_
2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Measure
Theory.Measure Ω} {μ : MeasureT…
· 使用定理 `MeasureTheory.HasPDF.aemeasurable`：∀ {Ω : Type u_1} {E : Type u_2} [inst
 : MeasurableSpace E] {x : MeasurableSpace Ω} (X : Ω → E)   (ℙ : MeasureTheory.M
easure Ω) (μ : MeasureT…
· 使用定理 `MeasureTheory.lintegral_rnDeriv_mul`：lintegral_rnDeriv_mul [HaveLebesgue
Decomposition μ ν] (hμν : μ ≪ ν) {f : α -> Real>=0∞} (hf : AEMeasurable f ν) : ∫
⁻ x, μ.rnDeriv ν x * f x …
· 使用定理 `MeasureTheory.HasPDF.haveLebesgueDecomposition`：∀ {Ω : Type u_1} {E : Ty
pe u_2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Me
asureTheory.Measure Ω} {μ : MeasureT…

--- 原说明 ---
**The Law of the Unconscious Statistician** for nonnegative random variables.
-/
theorem lintegral_pdf_mul {X : Ω → E} [HasPDF X ℙ μ] {f : E → ℝ≥0∞}
    (hf : AEMeasurable f μ) : ∫⁻ x, pdf X ℙ μ x * f x ∂μ = ∫⁻ x, f (X x) ∂ℙ := by
  rw [pdf_def,
    ← lintegral_map' (hf.mono_ac HasPDF.absolutelyContinuous) (HasPDF.aemeasurable X ℙ μ),
    lintegral_rnDeriv_mul HasPDF.absolutelyContinuous hf]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-
**MeasureTheory.pdf.integrable_pdf_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.pdf`。
形式化陈述：integrable_pdf_smul_iff [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] {f
 : E -> F} (hf : AEStronglyMeasurable f μ) : Integrable (fun x => (pdf X ℙ μ x).
toReal • f x) μ ↔ Integrable (fun x => f (X x)) ℙ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用定理 `MeasureTheory.HasPDF.absolutelyContinuous`：∀ {Ω : Type u_1} {E : Type u_
2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Measure
Theory.Measure Ω} {μ : MeasureT…
· 使用定理 `MeasureTheory.HasPDF.aemeasurable`：∀ {Ω : Type u_1} {E : Type u_2} [inst
 : MeasurableSpace E] {x : MeasurableSpace Ω} (X : Ω → E)   (ℙ : MeasureTheory.M
easure Ω) (μ : MeasureT…
· 使用定理 `MeasureTheory.map_eq_withDensity_pdf`：map_eq_withDensity_pdf {m : Measur
ableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E
· 使用定理 `MeasureTheory.pdf_def`：pdf_def {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {
μ : Measure E} {X : Ω -> E} : pdf X ℙ μ = (map X ℙ).rnDeriv μ
· 使用定理 `MeasureTheory.integrable_rnDeriv_smul_iff`：integrable_rnDeriv_smul_iff (
hμν : μ ≪ ν) : Integrable (fun x => (μ.rnDeriv ν x).toReal • f x) ν ↔ Integrable
 f μ
· 使用定理 `MeasureTheory.HasPDF.haveLebesgueDecomposition`：∀ {Ω : Type u_1} {E : Ty
pe u_2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Me
asureTheory.Measure Ω} {μ : MeasureT…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrable_pdf_smul_iff [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] {f : E → F}
    (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => (pdf X ℙ μ x).toReal • f x) μ ↔ Integrable (fun x => f (X x)) ℙ := by
  rw [← Function.comp_def,
    ← integrable_map_measure (hf.mono_ac HasPDF.absolutelyContinuous) (HasPDF.aemeasurable X ℙ μ),
    map_eq_withDensity_pdf X ℙ μ, pdf_def, integrable_rnDeriv_smul_iff HasPDF.absolutelyContinuous]
  rw [withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuous]

/-- **The Law of the Unconscious Statistician**: Given a random variable `X` and a measurable
function `f`, `f ∘ X` is a random variable with expectation `∫ x, pdf X x • f x ∂μ`
where `μ` is a measure on the codomain of `X`. -/
/-
**MeasureTheory.pdf.integral_pdf_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.p
df`。
形式化陈述：integral_pdf_smul [IsFiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] {f : E -
> F} (hf : AEStronglyMeasurable f μ) : ∫ x, (pdf X ℙ μ x).toReal • f x ∂μ = ∫ x,
 f (X x) ∂ℙ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `MeasureTheory.HasPDF.aemeasurable`：∀ {Ω : Type u_1} {E : Type u_2} [inst
 : MeasurableSpace E] {x : MeasurableSpace Ω} (X : Ω → E)   (ℙ : MeasureTheory.M
easure Ω) (μ : MeasureT…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用定理 `MeasureTheory.HasPDF.absolutelyContinuous`：∀ {Ω : Type u_1} {E : Type u_
2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Measure
Theory.Measure Ω} {μ : MeasureT…
· 使用定理 `MeasureTheory.map_eq_withDensity_pdf`：map_eq_withDensity_pdf {m : Measur
ableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E
· 使用定理 `MeasureTheory.pdf_def`：pdf_def {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {
μ : Measure E} {X : Ω -> E} : pdf X ℙ μ = (map X ℙ).rnDeriv μ
· 使用定理 `MeasureTheory.integral_rnDeriv_smul`：integral_rnDeriv_smul (hμν : μ ≪ ν)
 : ∫ x, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.HasPDF.haveLebesgueDecomposition`：∀ {Ω : Type u_1} {E : Ty
pe u_2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Me
asureTheory.Measure Ω} {μ : MeasureT…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ

--- 原说明 ---
**The Law of the Unconscious Statistician**: Given a random variable `X` and a m
easurable
function `f`, `f ∘ X` is a random variable with expectation `∫ x, pdf X x • f x 
∂μ`
where `μ` is a measure on the codomain of `X`.
-/
theorem integral_pdf_smul [IsFiniteMeasure ℙ] {X : Ω → E} [HasPDF X ℙ μ] {f : E → F}
    (hf : AEStronglyMeasurable f μ) : ∫ x, (pdf X ℙ μ x).toReal • f x ∂μ = ∫ x, f (X x) ∂ℙ := by
  rw [← integral_map (HasPDF.aemeasurable X ℙ μ) (hf.mono_ac HasPDF.absolutelyContinuous),
    map_eq_withDensity_pdf X ℙ μ, pdf_def, integral_rnDeriv_smul HasPDF.absolutelyContinuous,
    withDensity_rnDeriv_eq _ _ HasPDF.absolutelyContinuous]

end IntegralPDFMul

section

variable {F : Type*} [MeasurableSpace F] {ν : Measure F} (X : Ω → E) [HasPDF X ℙ μ] {g : E → F}

/-- A random variable that `HasPDF` transformed under a `QuasiMeasurePreserving`
map also `HasPDF` if `(map g (map X ℙ)).HaveLebesgueDecomposition μ`.

`quasiMeasurePreserving_hasPDF` is more useful in the case we are working with a
probability measure and a real-valued random variable. -/
/-
**MeasureTheory.pdf.quasiMeasurePreserving_hasPDF** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.pdf`。
形式化陈述：quasiMeasurePreserving_hasPDF (hg : QuasiMeasurePreserving g μ ν) (hmap : 
(map g (map X ℙ)).HaveLebesgueDecomposition ν) : HasPDF (g ∘ X) ℙ ν
参数：hg : QuasiMeasurePreserving g μ ν；hmap : (map g (map X ℙ)).HaveLebesgueDecomp
osition ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AEMeasurable.mono_ac`：mono_ac (hf : AEMeasurable f ν) (hμν : μ ≪ ν) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : Measu
reTheory.Measure α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.HasPDF.absolutelyContinuous`：∀ {Ω : Type u_1} {E : Type u_
2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Measure
Theory.Measure Ω} {μ : MeasureT…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasPDF_iff`：hasPDF_iff : HasPDF X ℙ μ ↔ AEMeasurable X ℙ ∧
 (map X ℙ).HaveLebesgueDecomposition μ ∧ map X ℙ ≪ μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `MeasureTheory.HasPDF.aemeasurable`：∀ {Ω : Type u_1} {E : Type u_2} [inst
 : MeasurableSpace E] {x : MeasurableSpace Ω} (X : Ω → E)   (ℙ : MeasureTheory.M
easure Ω) (μ : MeasureT…
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.measurable`：∀ {α : Type u_1
} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f : α → β}  
 {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.map`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureTheory.M
easure α},   μ.AbsolutelyContinuous …
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…

--- 原说明 ---
A random variable that `HasPDF` transformed under a `QuasiMeasurePreserving`
map also `HasPDF` if `(map g (map X ℙ)).HaveLebesgueDecomposition μ`.

`quasiMeasurePreserving_hasPDF` is more useful in the case we are working with a
probability measure and a real-valued random variable.
-/
theorem quasiMeasurePreserving_hasPDF (hg : QuasiMeasurePreserving g μ ν)
    (hmap : (map g (map X ℙ)).HaveLebesgueDecomposition ν) : HasPDF (g ∘ X) ℙ ν := by
  have hgm : AEMeasurable g (map X ℙ) := hg.aemeasurable.mono_ac HasPDF.absolutelyContinuous
  rw [hasPDF_iff, ← AEMeasurable.map_map_of_aemeasurable hgm (HasPDF.aemeasurable X ℙ μ)]
  refine ⟨hg.measurable.comp_aemeasurable (HasPDF.aemeasurable _ _ μ), hmap, ?_⟩
  exact (HasPDF.absolutelyContinuous.map hg.1).trans hg.2
/-
**MeasureTheory.pdf.quasiMeasurePreserving_hasPDF'** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.pdf`。
形式化陈述：quasiMeasurePreserving_hasPDF' [SFinite ℙ] [SigmaFinite ν] (hg : QuasiMeas
urePreserving g μ ν) : HasPDF (g ∘ X) ℙ ν
参数：hg : QuasiMeasurePreserving g μ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.pdf.quasiMeasurePreserving_hasPDF`：quasiMeasurePreserving_
hasPDF (hg : QuasiMeasurePreserving g μ ν) (hmap : (map g (map X ℙ)).HaveLebesgu
eDecomposition ν) : HasPDF (g ∘ X) ℙ …
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
-/
theorem quasiMeasurePreserving_hasPDF' [SFinite ℙ] [SigmaFinite ν]
    (hg : QuasiMeasurePreserving g μ ν) : HasPDF (g ∘ X) ℙ ν :=
  quasiMeasurePreserving_hasPDF X hg inferInstance

end

section Real

variable {X : Ω → ℝ}

nonrec theorem _root_.Real.hasPDF_iff [SFinite ℙ] :
    HasPDF X ℙ ↔ AEMeasurable X ℙ ∧ map X ℙ ≪ volume := by
  rw [hasPDF_iff, and_iff_right (inferInstance : HaveLebesgueDecomposition _ _)]

/-- A real-valued random variable `X` `HasPDF X ℙ λ` (where `λ` is the Lebesgue measure) if and
only if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `λ`. -/
nonrec theorem _root_.Real.hasPDF_iff_of_aemeasurable [SFinite ℙ] (hX : AEMeasurable X ℙ) :
    HasPDF X ℙ ↔ map X ℙ ≪ volume := by
  rw [Real.hasPDF_iff, and_iff_right hX]

variable [IsFiniteMeasure ℙ]

/-- If `X` is a real-valued random variable that has pdf `f`, then the expectation of `X` equals
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure. -/
/-
**MeasureTheory.pdf.integral_mul_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.pdf`。
形式化陈述：integral_mul_eq_integral [HasPDF X ℙ] : ∫ x, x * (pdf X ℙ volume x).toReal
 = ∫ x, X x ∂ℙ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.pdf.integral_pdf_smul`：integral_pdf_smul [IsFiniteMeasure 
ℙ] {X : Ω -> E} [HasPDF X ℙ μ] {f : E -> F} (hf : AEStronglyMeasurable f μ) : ∫ 
x, (pdf X ℙ μ x).toReal •…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)

--- 原说明 ---
If `X` is a real-valued random variable that has pdf `f`, then the expectation o
f `X` equals
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure.
-/
theorem integral_mul_eq_integral [HasPDF X ℙ] : ∫ x, x * (pdf X ℙ volume x).toReal = ∫ x, X x ∂ℙ :=
  calc
    _ = ∫ x, (pdf X ℙ volume x).toReal * x := by congr with x; exact mul_comm _ _
    _ = _ := integral_pdf_smul measurable_id.aestronglyMeasurable
/-
**MeasureTheory.pdf.hasFiniteIntegral_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.pdf`。
形式化陈述：hasFiniteIntegral_mul {f : Real -> Real} {g : Real -> Real>=0∞} (hg : pdf 
X ℙ =ᵐ[volume] g) (hgi : ∫⁻ x, ‖f x‖ₑ * g x != ∞) : HasFiniteIntegral fun x => f
 x * (pdf X ℙ volume x).toReal
参数：hg : pdf X ℙ =ᵐ[volume] g；hgi : ∫⁻ x, ‖f x‖ₑ * g x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_enorm`：hasFiniteIntegral_iff_enorm {
f : α -> ε} : HasFiniteIntegral f μ ↔ ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
· 使用定理 `MeasureTheory.ae_eq_trans`：ae_eq_trans {f g h : α -> β} (h₁ : f =ᵐ[μ] g)
 (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h
· 使用定理 `Filter.EventuallyEq.fun_mul`：∀ {α : Type u} {β : Type v} [inst : Mul β] 
{f f' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → (fun i => f i * 
f' i) =ᶠ[l] fun i…
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.pdf.ofReal_toReal_ae_eq`：∀ {Ω : Type u_1} {E : Type u_2} [
inst : MeasurableSpace E] {m : MeasurableSpace Ω} {ℙ : MeasureTheory.Measure Ω} 
  {μ : MeasureTheory.Measur…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `enorm_smul`：enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α 
β] (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
· 使用定理 `instENormSMulClass`：∀ {α : Type u_1} {β : Type u_2} [inst : SeminormedRi
ng α] [inst_1 : SeminormedAddGroup β] [inst_2 : SMul α β]   [NormSMulClass α β],
 ENormSM…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.enorm_eq_ofReal`：enorm_eq_ofReal (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
-/
theorem hasFiniteIntegral_mul {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞} (hg : pdf X ℙ =ᵐ[volume] g)
    (hgi : ∫⁻ x, ‖f x‖ₑ * g x ≠ ∞) :
    HasFiniteIntegral fun x => f x * (pdf X ℙ volume x).toReal := by
  rw [hasFiniteIntegral_iff_enorm]
  have : (fun x => ‖f x‖ₑ * g x) =ᵐ[volume] fun x => ‖f x * (pdf X ℙ volume x).toReal‖ₑ := by
    refine ae_eq_trans ((ae_eq_refl _).fun_mul (ae_eq_trans hg.symm ofReal_toReal_ae_eq.symm)) ?_
    simp_rw [← smul_eq_mul, enorm_smul, smul_eq_mul]
    refine .fun_mul (ae_eq_refl _) ?_
    simp only [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ae_eq_refl]
  rwa [lt_top_iff_ne_top, ← lintegral_congr_ae this]

end Real

section TwoVariables

variable {F : Type*} [MeasurableSpace F] {ν : Measure F} {X : Ω → E} {Y : Ω → F}

/-- Random variables are independent iff their joint density is a product of marginal densities. -/
/-
**MeasureTheory.pdf.indepFun_iff_pdf_prod_eq_pdf_mul_pdf** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.pdf`。
形式化陈述：indepFun_iff_pdf_prod_eq_pdf_mul_pdf [IsFiniteMeasure ℙ] [SigmaFinite μ] [
SigmaFinite ν] [HasPDF (fun ω => (X ω, Y ω)) ℙ (μ.prod ν)] : IndepFun X Y ℙ ↔ pd
f (fun ω => (X ω, Y ω)) ℙ (μ.prod ν) =ᵐ[μ.prod ν] fun z => pdf X ℙ μ z.1 * pdf Y
 ℙ ν z.2
参数：fun ω => (X ω, Y ω)；μ.prod ν。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.pdf.quasiMeasurePreserving_hasPDF'`：quasiMeasurePreserving
_hasPDF' [SFinite ℙ] [SigmaFinite ν] (hg : QuasiMeasurePreserving g μ ν) : HasPD
F (g ∘ X) ℙ ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_snd`：quasiMeasurePreserving
_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
· 使用定理 `MeasureTheory.lintegral_prod_mul`：lintegral_prod_mul {f : α -> Real>=0∞}
 {g : β -> Real>=0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) : ∫⁻ z, f z
.1 * g z.2 ∂μ.prod ν =…
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.measurable_pdf`：measurable_pdf {m : MeasurableSpace Ω} (X 
: Ω -> E) (ℙ : Measure Ω) (μ : Measure E
· 使用定理 `MeasureTheory.map_eq_setLIntegral_pdf`：map_eq_setLIntegral_pdf {m : Meas
urableSpace Ω} (X : Ω -> E) (ℙ : Measure Ω) (μ : Measure E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`：indepFun_iff_ma
p_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsFi
niteMeasure μ] (hf : AEMeasurable f μ) (hg : …
· 使用定理 `MeasureTheory.HasPDF.aemeasurable`：∀ {Ω : Type u_1} {E : Type u_2} [inst
 : MeasurableSpace E] {x : MeasurableSpace Ω} (X : Ω → E)   (ℙ : MeasureTheory.M
easure Ω) (μ : MeasureT…
· 使用定理 `MeasureTheory.pdf.eq_of_map_eq_withDensity`：eq_of_map_eq_withDensity [Is
FiniteMeasure ℙ] {X : Ω -> E} [HasPDF X ℙ μ] (f : E -> Real>=0∞) (hmf : AEMeasur
able f μ) : map X ℙ = μ.withDens…
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Random variables are independent iff their joint density is a product of margina
l densities.
-/
theorem indepFun_iff_pdf_prod_eq_pdf_mul_pdf
    [IsFiniteMeasure ℙ] [SigmaFinite μ] [SigmaFinite ν] [HasPDF (fun ω ↦ (X ω, Y ω)) ℙ (μ.prod ν)] :
    IndepFun X Y ℙ ↔
      pdf (fun ω ↦ (X ω, Y ω)) ℙ (μ.prod ν) =ᵐ[μ.prod ν] fun z ↦ pdf X ℙ μ z.1 * pdf Y ℙ ν z.2 := by
  have : HasPDF X ℙ μ := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (fun ω ↦ (X ω, Y ω))
    quasiMeasurePreserving_fst
  have : HasPDF Y ℙ ν := quasiMeasurePreserving_hasPDF' (μ := μ.prod ν) (fun ω ↦ (X ω, Y ω))
    quasiMeasurePreserving_snd
  have h₀ : (ℙ.map X).prod (ℙ.map Y) =
      (μ.prod ν).withDensity fun z ↦ pdf X ℙ μ z.1 * pdf Y ℙ ν z.2 :=
    prod_eq fun s t hs ht ↦ by rw [withDensity_apply _ (hs.prod ht), ← prod_restrict,
      lintegral_prod_mul (measurable_pdf X ℙ μ).aemeasurable (measurable_pdf Y ℙ ν).aemeasurable,
      map_eq_setLIntegral_pdf X ℙ μ hs, map_eq_setLIntegral_pdf Y ℙ ν ht]
  rw [indepFun_iff_map_prod_eq_prod_map_map (HasPDF.aemeasurable X ℙ μ) (HasPDF.aemeasurable Y ℙ ν),
    ← eq_of_map_eq_withDensity, h₀]
  exact (((measurable_pdf X ℙ μ).comp measurable_fst).mul
    ((measurable_pdf Y ℙ ν).comp measurable_snd)).aemeasurable

end TwoVariables

end pdf

end MeasureTheory

section Group

namespace ProbabilityTheory

variable {Ω G : Type*} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [Group G] {mG : MeasurableSpace G}
  [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G} [IsMulLeftInvariant μ] {X Y : Ω → G}

@[to_additive]
/-
**ProbabilityTheory.IndepFun.mul_hasPDF'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {G : Type u_2} {mΩ : MeasurableSpace Ω} {ℙ : MeasureTheor
y.Measure Ω} [inst : Group G]   {mG : MeasurableSpace G} [MeasurableMul₂ G] [Mea
surableInv G] {μ : MeasureTheory.Measure G} [μ.IsMulLeftInvariant]   {X Y : Ω → 
G} [MeasureTheory.SFinite μ] [MeasureTheory.HasPDF X ℙ μ] [MeasureTheory.HasPDF 
Y ℙ μ],   MeasureTheory.SigmaFinite (MeasureTheory.Measure.map X ℙ) →     Measur
eTheory.SigmaFinite (MeasureTheory.Measure.map Y ℙ) →       ProbabilityTheory.In
depFun X Y ℙ → MeasureTheory.HasPDF (X * Y) ℙ μ
参数：MeasureTheory.Measure.map X ℙ；MeasureTheory.Measure.map Y ℙ；X * Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasPDF.aemeasurable'`：∀ {Ω : Type u_1} {E : Type u_2} {ins
t : MeasurableSpace E} {m : MeasurableSpace Ω} {X : Ω → E}   {ℙ : MeasureTheory.
Measure Ω} (μ : autoPara…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.hasPDF_iff_of_aemeasurable`：hasPDF_iff_of_aemeasurable (hX
 : AEMeasurable X ℙ) : HasPDF X ℙ μ ↔ (map X ℙ).HaveLebesgueDecomposition μ ∧ ma
p X ℙ ≪ μ
· 使用定理 `AEMeasurable.mul`：AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (f * g) μ
· 使用定理 `ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map₀'`：∀ {Ω : Type u_7} 
{mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M : Type u_10} [inst : M
onoid M]   [inst_1 : MeasurableSpace M] [Me…
· 使用定理 `MeasureTheory.HaveLebesgueDecomposition.mconv`：∀ {G : Type u_3} [inst : 
Group G] {mG : MeasurableSpace G} [MeasurableMul₂ G] [MeasurableInv G]   {μ : Me
asureTheory.Measure G} [μ.IsMulLeft…
· 使用定理 `MeasureTheory.HasPDF.haveLebesgueDecomposition`：∀ {Ω : Type u_1} {E : Ty
pe u_2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Me
asureTheory.Measure Ω} {μ : MeasureT…
· 使用定理 `MeasureTheory.HasPDF.absolutelyContinuous`：∀ {Ω : Type u_1} {E : Type u_
2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Measure
Theory.Measure Ω} {μ : MeasureT…
· 使用定理 `MeasureTheory.Measure.mconv_absolutelyContinuous`：mconv_absolutelyContin
uous [MeasurableMul₂ M] {μ ν ρ : Measure M} [IsMulLeftInvariant ρ] [SFinite ν] (
hν : ν ≪ ρ) : μ ∗ₘ ν ≪ ρ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
-/
theorem IndepFun.mul_hasPDF' [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    (σX : SigmaFinite (ℙ.map X)) (σY : SigmaFinite (ℙ.map Y)) (hXY : IndepFun X Y ℙ) :
    HasPDF (X * Y) ℙ μ := by
  have : AEMeasurable X ℙ := HasPDF.aemeasurable' μ
  have : AEMeasurable Y ℙ := HasPDF.aemeasurable' μ
  rw [hasPDF_iff_of_aemeasurable (by fun_prop),
    hXY.map_mul_eq_map_mconv_map₀' (by fun_prop) (by fun_prop) σX σY]
  refine ⟨?_, mconv_absolutelyContinuous HasPDF.absolutelyContinuous⟩
  apply HaveLebesgueDecomposition.mconv <;> exact HasPDF.absolutelyContinuous

@[to_additive]
/-
**ProbabilityTheory.IndepFun.mul_hasPDF** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {G : Type u_2} {mΩ : MeasurableSpace Ω} {ℙ : MeasureTheor
y.Measure Ω} [inst : Group G]   {mG : MeasurableSpace G} [MeasurableMul₂ G] [Mea
surableInv G] {μ : MeasureTheory.Measure G} [μ.IsMulLeftInvariant]   {X Y : Ω → 
G} [MeasureTheory.SFinite μ] [MeasureTheory.HasPDF X ℙ μ] [MeasureTheory.HasPDF 
Y ℙ μ]   [MeasureTheory.IsFiniteMeasure ℙ], ProbabilityTheory.IndepFun X Y ℙ → M
easureTheory.HasPDF (X * Y) ℙ μ
参数：X * Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IndepFun.mul_hasPDF'`：∀ {Ω : Type u_1} {G : Type u_2} 
{mΩ : MeasurableSpace Ω} {ℙ : MeasureTheory.Measure Ω} [inst : Group G]   {mG : 
MeasurableSpace G} [Measurab…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
-/
theorem IndepFun.mul_hasPDF [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ] [IsFiniteMeasure ℙ]
  (hXY : IndepFun X Y ℙ) : HasPDF (X * Y) ℙ μ := by
  apply hXY.mul_hasPDF' <;> apply IsFiniteMeasure.toSigmaFinite

@[to_additive]
/-
**ProbabilityTheory.IndepFun.pdf_mul_eq_mlconvolution_pdf'** 是 Mathlib 中的一个定理，位于
命名空间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {G : Type u_2} {mΩ : MeasurableSpace Ω} {ℙ : MeasureTheor
y.Measure Ω} [inst : Group G]   {mG : MeasurableSpace G} [MeasurableMul₂ G] [Mea
surableInv G] {μ : MeasureTheory.Measure G} [μ.IsMulLeftInvariant]   {X Y : Ω → 
G} [MeasureTheory.SigmaFinite μ] [MeasureTheory.HasPDF X ℙ μ] [MeasureTheory.Has
PDF Y ℙ μ],   MeasureTheory.SigmaFinite (MeasureTheory.Measure.map X ℙ) →     Me
asureTheory.SigmaFinite (MeasureTheory.Measure.map Y ℙ) →       ProbabilityTheor
y.IndepFun X Y ℙ →         MeasureTheory.pdf (X * Y) ℙ μ =ᵐ[μ]           Measure
Theory.mlconvolution (MeasureTheory.pdf X ℙ μ) (MeasureTheory.pdf Y ℙ μ) μ
参数：MeasureTheory.Measure.map X ℙ；MeasureTheory.Measure.map Y ℙ；X * Y；MeasureTheo
ry.pdf X ℙ μ；MeasureTheory.pdf Y ℙ μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.pdf.eq_1`：∀ {Ω : Type u_1} {E : Type u_2} [inst : Measurab
leSpace E] {x : MeasurableSpace Ω} (X : Ω → E)   (ℙ : MeasureTheory.Measure Ω) (
μ : MeasureT…
· 使用定理 `ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map₀'`：∀ {Ω : Type u_7} 
{mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M : Type u_10} [inst : M
onoid M]   [inst_1 : MeasurableSpace M] [Me…
· 使用定理 `MeasureTheory.HasPDF.aemeasurable'`：∀ {Ω : Type u_1} {E : Type u_2} {ins
t : MeasurableSpace E} {m : MeasurableSpace Ω} {X : Ω → E}   {ℙ : MeasureTheory.
Measure Ω} (μ : autoPara…
· 使用定理 `MeasureTheory.rnDeriv_mconv'`：rnDeriv_mconv' [SigmaFinite μ] {ν₁ ν₂ : Me
asure G} [SigmaFinite ν₁] [SigmaFinite ν₂] (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) : (ν₁ ∗
ₘ ν₂).rnDeriv μ =ᵐ…
· 使用定理 `MeasureTheory.HasPDF.absolutelyContinuous`：∀ {Ω : Type u_1} {E : Type u_
2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Measure
Theory.Measure Ω} {μ : MeasureT…
-/
theorem IndepFun.pdf_mul_eq_mlconvolution_pdf' [SigmaFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    (σX : SigmaFinite (ℙ.map X)) (σY : SigmaFinite (ℙ.map Y)) (hXY : IndepFun X Y ℙ) :
    pdf (X * Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₘₗ[μ] pdf Y ℙ μ := by
  rw [pdf, hXY.map_mul_eq_map_mconv_map₀' (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ) σX σY]
  apply rnDeriv_mconv' <;> exact HasPDF.absolutelyContinuous

@[to_additive]
/-
**ProbabilityTheory.IndepFun.pdf_mul_eq_mlconvolution_pdf** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {G : Type u_2} {mΩ : MeasurableSpace Ω} {ℙ : MeasureTheor
y.Measure Ω} [inst : Group G]   {mG : MeasurableSpace G} [MeasurableMul₂ G] [Mea
surableInv G] {μ : MeasureTheory.Measure G} [μ.IsMulLeftInvariant]   {X Y : Ω → 
G} [MeasureTheory.SFinite μ] [MeasureTheory.HasPDF X ℙ μ] [MeasureTheory.HasPDF 
Y ℙ μ]   [MeasureTheory.IsFiniteMeasure ℙ],   ProbabilityTheory.IndepFun X Y ℙ →
     MeasureTheory.pdf (X * Y) ℙ μ =ᵐ[μ]       MeasureTheory.mlconvolution (Meas
ureTheory.pdf X ℙ μ) (MeasureTheory.pdf Y ℙ μ) μ
参数：X * Y；MeasureTheory.pdf X ℙ μ；MeasureTheory.pdf Y ℙ μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.pdf.eq_1`：∀ {Ω : Type u_1} {E : Type u_2} [inst : Measurab
leSpace E] {x : MeasurableSpace Ω} (X : Ω → E)   (ℙ : MeasureTheory.Measure Ω) (
μ : MeasureT…
· 使用定理 `ProbabilityTheory.IndepFun.map_mul_eq_map_mconv_map₀`：∀ {Ω : Type u_7} {
mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {M : Type u_10} [inst : Mo
noid M]   [inst_1 : MeasurableSpace M] [Me…
· 使用定理 `MeasureTheory.HasPDF.aemeasurable'`：∀ {Ω : Type u_1} {E : Type u_2} {ins
t : MeasurableSpace E} {m : MeasurableSpace Ω} {X : Ω → E}   {ℙ : MeasureTheory.
Measure Ω} (μ : autoPara…
· 使用定理 `MeasureTheory.rnDeriv_mconv`：rnDeriv_mconv [SFinite μ] {ν₁ ν₂ : Measure 
G} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] [ν₁.HaveLebesgueDecomposition μ] [ν
₂.HaveLebesgueDec…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.HasPDF.haveLebesgueDecomposition`：∀ {Ω : Type u_1} {E : Ty
pe u_2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Me
asureTheory.Measure Ω} {μ : MeasureT…
· 使用定理 `MeasureTheory.HasPDF.absolutelyContinuous`：∀ {Ω : Type u_1} {E : Type u_
2} [inst : MeasurableSpace E] {x : MeasurableSpace Ω} {X : Ω → E}   {ℙ : Measure
Theory.Measure Ω} {μ : MeasureT…
-/
theorem IndepFun.pdf_mul_eq_mlconvolution_pdf [SFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ]
    [IsFiniteMeasure ℙ] (hXY : IndepFun X Y ℙ) :
    pdf (X * Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₘₗ[μ] pdf Y ℙ μ := by
  rw [pdf, hXY.map_mul_eq_map_mconv_map₀ (HasPDF.aemeasurable' μ) (HasPDF.aemeasurable' μ)]
  apply rnDeriv_mconv <;> exact HasPDF.absolutelyContinuous

end ProbabilityTheory

end Group

