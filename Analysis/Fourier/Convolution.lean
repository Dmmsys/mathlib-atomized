/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # The Fourier transform of the convolution

In this file we calculate the Fourier transform of a convolution.

## Main definitions
* `SchwartzMap.convolution`: The convolution on Schwartz functions is defined via the Fourier
  transform.

## Main statements
* `Real.fourier_bilin_convolution_eq`: The Fourier transform of a convolution is the bilinear map
  applied to the Fourier transform of the functions.
* `Real.fourier_smul_convolution_eq`: Variant for scalar multiplication.
* `Real.fourier_mul_convolution_eq`: Variant for multiplication.
* `SchwartzMap.fourier_convolution`: The Fourier transform of the Schwartz convolution is given by
  the pairing of the Fourier transformed Schwartz functions.
* `SchwartzMap.convolution_apply`: The Schwartz function convolution coincides with the convolution
  for functions.

-/

@[expose] public section

variable {𝕜 R E F F₁ F₂ F₃ : Type*}

namespace Real

open MeasureTheory Convolution

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F₁] [NormedAddCommGroup F₂] [NormedAddCommGroup F₃]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace 𝕜 F₁] [NormedSpace 𝕜 F₂] [NormedSpace 𝕜 F₃]

/-- The norm of the integrand of the convolution is integrable if the functions are integrable. -/
/-
**Real.integrable_prod_sub** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：integrable_prod_sub (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {f₁ : E -> F₁} {f₂ : E ->
 F₂} (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) : Integrable (fun (p : E × E) =
> ‖B‖ * (‖f₁ (p.1 - p.2)‖ * ‖f₂ p.2‖)) (volume.prod volume)
参数：B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃；hf₁ : Integrable f₁；hf₂ : Integrable f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.convolution_integrand`：∀ {𝕜 : Type u𝕜} {G : Typ
e uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E] 
  [inst_1 : NormedAddCommGroup E'] […
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `MeasureTheory.IsAddLeftInvariant.isAddRightInvariant`：∀ {G : Type u_1} [
inst : MeasurableSpace G] [inst_1 : AddCommSemigroup G] {μ : MeasureTheory.Measu
re G}   [μ.IsAddLeftInvariant], μ.IsAddRig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…

--- 原说明 ---
The norm of the integrand of the convolution is integrable if the functions are 
integrable.
-/
theorem integrable_prod_sub (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {f₁ : E → F₁} {f₂ : E → F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) :
    Integrable (fun (p : E × E) ↦ ‖B‖ * (‖f₁ (p.1 - p.2)‖ * ‖f₂ p.2‖)) (volume.prod volume) := by
  simpa [mul_comm] using (hf₂.norm.convolution_integrand (.mul ℝ ℝ) hf₁.norm).const_mul ‖B‖

open FourierTransform

variable [NormedSpace ℂ F₃]

/-- Calculate the Fourier transform of the convolution as a symmetric integral. -/
/-
**Real.fourier_bilin_convolution_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_bilin_convolution_eq_integral (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {f₁ : E
 -> F₁} {f₂ : E -> F₂} (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) : 𝓕 (
f₁ ⋆[B] f₂) ξ = ∫ y, ∫ x, 𝐞 (-inner Real (y + x) ξ) • B (f₁ x) (f₂ y)
参数：B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃；hf₁ : Integrable f₁；hf₂ : Integrable f₂；ξ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.convolution_flip`：convolution_flip : g ⋆[L.flip, μ] f = f 
⋆[L, μ] g
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular`：∀
 {G : Type u_1} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopolog
icalAddGroup G]   [inst_3 : MeasurableSpace G] [BorelSpace …
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaComp
actSpaceOfBorelSpaceOfSigmaFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] 
[TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]   [inst_3 : Mea
surableSpace X]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_integral_swap`：integral_integral_swap ⦃f : α -> β
 -> E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫
 x, f x y ∂μ ∂ν
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
Calculate the Fourier transform of the convolution as a symmetric integral.
-/
theorem fourier_bilin_convolution_eq_integral (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {f₁ : E → F₁} {f₂ : E → F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[B] f₂) ξ = ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) := calc
  _ = 𝓕 (f₂ ⋆[B.flip] f₁) ξ := by
    rw [convolution_flip]
  _ = ∫ x, 𝐞 (-inner ℝ x ξ) • ∫ y, B (f₁ (x - y)) (f₂ y) := by rfl
  _ = ∫ x, ∫ y, 𝐞 (-inner ℝ x ξ) • B (f₁ (x - y)) (f₂ y) := by
    congr
    ext x
    simp_rw [Circle.smul_def, integral_smul]
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ x ξ) • B (f₁ (x - y)) (f₂ y) := by
    refine integral_integral_swap ?_
    have hB := hf₂.convolution_integrand B.flip hf₁
    refine hB.mono ?_ ?_
    · exact continuous_fourierChar.comp (by fun_prop) |>.aestronglyMeasurable.smul
        hB.aestronglyMeasurable
    · filter_upwards with ⟨x, y⟩ using by simp
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) := by
    congr
    ext y
    -- Linear change of variables
    convert! integral_sub_right_eq_self _ y (μ := volume)
    congr
    simp

variable [CompleteSpace F₁] [CompleteSpace F₂] [CompleteSpace F₃]
  [NormedSpace ℂ F₁] [NormedSpace ℂ F₂]

open ContinuousLinearMap

/-- The Fourier transform of the convolution is given by the bilinear map applied to the Fourier
transform of the individual functions. -/
/-
**Real.fourier_bilin_convolution_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_bilin_convolution_eq (B : F₁ ->L[Complex] F₂ ->L[Complex] F₃) {f₁ 
: E -> F₁} {f₂ : E -> F₂} (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) : 
𝓕 (f₁ ⋆[B] f₂) ξ = B (𝓕 f₁ ξ) (𝓕 f₂ ξ)
参数：B : F₁ ->L[Complex] F₂ ->L[Complex] F₃；hf₁ : Integrable f₁；hf₂ : Integrable f
₂；ξ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Real.fourier_bilin_convolution_eq_integral`：fourier_bilin_convolution_eq
_integral (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂} (hf₁ : Inte
grable f₁) (hf₂ : Integrable f₂)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inner_add_left`：inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z
⟫
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.fourierIntegral_convergent_iff`：∀ {V : Type u_1} {E : Type u_3} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] [inst_2 : NormedAddCommGro
up V]   [inst_3 : InnerPr…
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The Fourier transform of the convolution is given by the bilinear map applied to
 the Fourier
transform of the individual functions.
-/
theorem fourier_bilin_convolution_eq (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) {f₁ : E → F₁} {f₂ : E → F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[B] f₂) ξ = B (𝓕 f₁ ξ) (𝓕 f₂ ξ) := calc
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) :=
    fourier_bilin_convolution_eq_integral B hf₁ hf₂ _
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ y ξ) • 𝐞 (-inner ℝ x ξ) • B (f₁ x) (f₂ y) := by
    simp_rw [inner_add_left, neg_add, AddChar.map_add_eq_mul, smul_smul]
  _ = ∫ y, (∫ x, B (𝐞 (-inner ℝ x ξ) • f₁ x)) (𝐞 (-inner ℝ y ξ) • f₂ y) := by
    congr with y
    have : Integrable (fun x ↦ (𝐞 (-inner ℝ x ξ) : ℂ) • B (f₁ x)) volume := by
      simpa [Circle.smul_def] using
        (Real.fourierIntegral_convergent_iff ξ).2 (B.integrable_comp hf₁)
    simp [Circle.smul_def, MeasureTheory.integral_smul, integral_apply this (f₂ y)]
  _ = B (∫ x, 𝐞 (-inner ℝ x ξ) • f₁ x) (∫ y, 𝐞 (-inner ℝ y ξ) • f₂ y) := by
    rw [← integral_comp_comm _ (by simpa using hf₂), ← integral_comp_comm _ (by simpa using hf₁)]

/-- The Fourier transform of the convolution is given by the multiplication of the Fourier transform
of the individual functions.

Version for scalar multiplication. -/
/-
**Real.fourier_smul_convolution_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_smul_convolution_eq {f₁ : E -> Complex} {f₂ : E -> F₁} (hf₁ : Inte
grable f₁) (hf₂ : Integrable f₂) (ξ : E) : 𝓕 (f₁ ⋆[lsmul Complex Complex] f₂) ξ 
= (𝓕 f₁ ξ) • (𝓕 f₂ ξ)
参数：hf₁ : Integrable f₁；hf₂ : Integrable f₂；ξ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.fourier_bilin_convolution_eq`：fourier_bilin_convolution_eq (B : F₁ 
->L[Complex] F₂ ->L[Complex] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂} (hf₁ : Integrable
 f₁) (hf₂ : Integrable …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
The Fourier transform of the convolution is given by the multiplication of the F
ourier transform
of the individual functions.

Version for scalar multiplication.
-/
theorem fourier_smul_convolution_eq {f₁ : E → ℂ} {f₂ : E → F₁}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[lsmul ℂ ℂ] f₂) ξ = (𝓕 f₁ ξ) • (𝓕 f₂ ξ) :=
  fourier_bilin_convolution_eq (lsmul ℂ ℂ) hf₁ hf₂ ξ

variable [NormedRing R] [NormedSpace ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
  [CompleteSpace R]

/-- The Fourier transform of the convolution is given by the multiplication of the Fourier transform
of the individual functions.

Version for multiplication. -/
/-
**Real.fourier_mul_convolution_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：fourier_mul_convolution_eq {f₁ : E -> R} {f₂ : E -> R} (hf₁ : Integrable f
₁) (hf₂ : Integrable f₂) (ξ : E) : 𝓕 (f₁ ⋆[mul Complex R] f₂) ξ = (𝓕 f₁ ξ) * (𝓕 
f₂ ξ)
参数：hf₁ : Integrable f₁；hf₂ : Integrable f₂；ξ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.fourier_bilin_convolution_eq`：fourier_bilin_convolution_eq (B : F₁ 
->L[Complex] F₂ ->L[Complex] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂} (hf₁ : Integrable
 f₁) (hf₂ : Integrable …

--- 原说明 ---
The Fourier transform of the convolution is given by the multiplication of the F
ourier transform
of the individual functions.

Version for multiplication.
-/
theorem fourier_mul_convolution_eq {f₁ : E → R} {f₂ : E → R}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[mul ℂ R] f₂) ξ = (𝓕 f₁ ξ) * (𝓕 f₂ ξ) :=
  fourier_bilin_convolution_eq (mul ℂ R) hf₁ hf₂ ξ

end Real

namespace SchwartzMap

variable [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedSpace 𝕜 F₁] [SMulCommClass ℂ 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [NormedSpace 𝕜 F₂] [SMulCommClass ℂ 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℂ F₃] [NormedSpace 𝕜 F₃] [SMulCommClass ℂ 𝕜 F₃]

open FourierTransform Convolution

/-- The bilinear convolution of Schwartz functions.

The continuity in the left argument is provided in `SchwartzMap.convolution_continuous_left`. -/
noncomputable
/-
**SchwartzMap.convolution** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：convolution (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) : 𝓢(E, F₁) ->ₗ[𝕜] 𝓢(E, F₂) ->L[𝕜]
 𝓢(E, F₃) where toFun f
参数：B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def convolution (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) : 𝓢(E, F₁) →ₗ[𝕜] 𝓢(E, F₂) →L[𝕜] 𝓢(E, F₃) where
  toFun f := fourierInvCLM 𝕜 𝓢(E, F₃) ∘L pairing B (𝓕 f) ∘L fourierCLM 𝕜 𝓢(E, F₂)
  map_add' := by simp [FourierTransform.fourier_add]
  map_smul' := by simp [FourierTransform.fourier_smul]

@[simp]
/-
**SchwartzMap.convolution_flip** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：convolution_flip (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)
) : convolution B.flip g f = convolution B f g
参数：B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃；f : 𝓢(E, F₁)；g : 𝓢(E, F₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
theorem convolution_flip (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) :
    convolution B.flip g f = convolution B f g := rfl

/-- The convolution is continuous in the left argument.

Note that since `𝓢(E, F)` is not a normed space, uncurried and curried continuity do not
coincide. -/
@[fun_prop]
/-
**SchwartzMap.convolution_continuous_left** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap
`。
形式化陈述：convolution_continuous_left (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (g : 𝓢(E, F₂)) : 
Continuous (convolution B · g)
参数：B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃；g : 𝓢(E, F₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…

--- 原说明 ---
The convolution is continuous in the left argument.

Note that since `𝓢(E, F)` is not a normed space, uncurried and curried continuit
y do not
coincide.
-/
theorem convolution_continuous_left (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (g : 𝓢(E, F₂)) :
    Continuous (convolution B · g) := (convolution B.flip g).continuous

variable [CompleteSpace F₃]
/-
**SchwartzMap.fourier_convolution** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：fourier_convolution (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, 
F₂)) : 𝓕 (convolution B f g) = pairing B (𝓕 f) (𝓕 g)
参数：B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃；f : 𝓢(E, F₁)；g : 𝓢(E, F₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourier_convolution (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) :
    𝓕 (convolution B f g) = pairing B (𝓕 f) (𝓕 g) := by simp [convolution]

variable [CompleteSpace F₁] [CompleteSpace F₂]

open MeasureTheory
/-
**SchwartzMap.fourier_convolution_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：fourier_convolution_apply (B : F₁ ->L[Complex] F₂ ->L[Complex] F₃) (f : 𝓢(
E, F₁)) (g : 𝓢(E, F₂)) (x : E) : 𝓕 (convolution B f g) x = 𝓕 (f ⋆[B] g) x
参数：B : F₁ ->L[Complex] F₂ ->L[Complex] F₃；f : 𝓢(E, F₁)；g : 𝓢(E, F₂)；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SchwartzMap.fourier_convolution`：fourier_convolution (B : F₁ ->L[𝕜] F₂ -
>L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) : 𝓕 (convolution B f g) = pairing B (𝓕 f
) (𝓕 g)
· 使用定理 `Real.fourier_bilin_convolution_eq`：fourier_bilin_convolution_eq (B : F₁ 
->L[Complex] F₂ ->L[Complex] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂} (hf₁ : Integrable
 f₁) (hf₂ : Integrable …
· 使用引理 `SchwartzMap.integrable`：integrable (f : 𝓢(D, V)) : Integrable f μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourier_convolution_apply (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (x : E) :
    𝓕 (convolution B f g) x = 𝓕 (f ⋆[B] g) x := by
  simp [fourier_convolution, fourier_coe,
    Real.fourier_bilin_convolution_eq B f.integrable g.integrable]

/-- The convolution on Schwartz functions is equal to the convolution on functions. -/
/-
**SchwartzMap.convolution_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：convolution_apply (B : F₁ ->L[Complex] F₂ ->L[Complex] F₃) (f : 𝓢(E, F₁)) 
(g : 𝓢(E, F₂)) (x : E) : convolution B f g x = (f ⋆[B] g) x
参数：B : F₁ ->L[Complex] F₂ ->L[Complex] F₃；f : 𝓢(E, F₁)；g : 𝓢(E, F₂)；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FourierPair.fourierInv_fourier_eq`：∀ {E : Type u_5} {F : Type u_6} {inst
 : FourierTransform E F} {inst_1 : FourierTransformInv F E}   [self : FourierPai
r E F] (f : E), Fourier…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `SchwartzMap.fourierInv_coe`：fourierInv_coe (f : 𝓢(V, E)) : 𝓕⁻ f = 𝓕⁻ (f 
: V -> E)
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SchwartzMap.fourier_convolution_apply`：fourier_convolution_apply (B : F₁
 ->L[Complex] F₂ ->L[Complex] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (x : E) : 𝓕 (con
volution B f g) x = 𝓕 (f ⋆[…
· 使用定理 `Continuous.fourierInv_fourier_eq`：Continuous.fourierInv_fourier_eq (h : 
Continuous f) (hf : Integrable f) (h'f : Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) = f
· 使用定理 `BddAbove.continuous_convolution_right_of_integrable`：∀ {𝕜 : Type u𝕜} {G 
: Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGrou
p E]   [inst_1 : NormedAddCommGroup E'] […
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `SchwartzMap.norm_le_seminorm`：norm_le_seminorm (f : 𝓢(E, F)) (x₀ : E) : 
‖f x₀‖ <= (SchwartzMap.seminorm 𝕜 0 0) f
· 使用引理 `SchwartzMap.integrable`：integrable (f : 𝓢(D, V)) : Integrable f μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SchwartzMap.continuous`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst
_3 : NormedS…
· 使用定理 `MeasureTheory.Integrable.integrable_convolution`：∀ {𝕜 : Type u𝕜} {G : Ty
pe uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]
   [inst_1 : NormedAddCommGroup E'] […
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
The convolution on Schwartz functions is equal to the convolution on functions.
-/
theorem convolution_apply (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (x : E) :
    convolution B f g x = (f ⋆[B] g) x := calc
  _ = 𝓕⁻ (𝓕 (convolution B f g)) x := by simp
  _ = 𝓕⁻ (fun y ↦ 𝓕 (f ⋆[B] g) y) x := by
    rw [fourierInv_coe]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [fourier_convolution_apply]
  _ = _ := by
    rw [Continuous.fourierInv_fourier_eq]
    · refine BddAbove.continuous_convolution_right_of_integrable B ?_ f.integrable g.continuous
      exact ⟨SchwartzMap.seminorm ℝ 0 0 g, fun x ⟨y, hy⟩ ↦ hy ▸ norm_le_seminorm ℝ g y⟩
    · exact f.integrable.integrable_convolution B g.integrable
    · have : Integrable (fun ξ ↦ B (𝓕 f ξ) (𝓕 g ξ)) volume := (pairing B (𝓕 f) (𝓕 g)).integrable
      convert! this
      rw [← fourier_convolution_apply B f g, fourier_convolution, pairing_apply_apply]


end SchwartzMap

