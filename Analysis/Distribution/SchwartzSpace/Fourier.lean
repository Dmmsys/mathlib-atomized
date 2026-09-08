/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier transform on Schwartz functions

This file constructs the Fourier transform as a continuous linear map acting on Schwartz
functions, in `fourierTransformCLM`. It is also given as a continuous linear equiv, in
`fourierTransformCLE`.

## Main statements
* `SchwartzMap.fderivCLM_fourier_eq`: The derivative of the Fourier transform is given by the
  Fourier transform of the multiplication with `-(2 * π * Complex.I) • innerSL ℝ`.
* `SchwartzMap.lineDerivOp_fourier_eq`: The line derivative of the Fourier transform is given by the
  Fourier transform of the multiplication with `-(2 * π * Complex.I) • (inner ℝ · m)`.
* `SchwartzMap.integral_bilin_fourier_eq`: The Fourier transform is self-adjoint.
* `SchwartzMap.integral_inner_fourier_fourier`: Plancherel's theorem for Schwartz functions.

-/

@[expose] public section

open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace

noncomputable section

namespace SchwartzMap

variable
  (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section definition

/-- The Fourier transform on a real inner product space, as a continuous linear map on the
Schwartz space.

This definition is only to define the Fourier transform, use `FourierTransform.fourierCLM` instead.
-/
/-
**SchwartzMap.fourierTransformCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：fourierTransformCLM : 𝓢(V, E) ->L[𝕜] 𝓢(V, E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Fourier transform on a real inner product space, as a continuous linear map 
on the
Schwartz space.

This definition is only to define the Fourier transform, use `FourierTransform.f
ourierCLM` instead.
-/
def fourierTransformCLM : 𝓢(V, E) →L[𝕜] 𝓢(V, E) := by
  refine mkCLM ((𝓕 : (V → E) → (V → E)) ·) ?_ ?_ ?_ ?_
  · intro f g
    simp [fourier_eq, integral_add ((fourierIntegral_convergent_iff _).mpr f.integrable)
      ((fourierIntegral_convergent_iff _).mpr g.integrable)]
  · simp [fourier_eq, smul_comm, integral_smul]
  · exact fun f ↦ contDiff_fourier (fun n _ ↦ integrable_pow_mul volume f n)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1),
      (2 * π) ^ n * (2 * n + 2) ^ k * (Finset.range (n + 1) ×ˢ Finset.range (k + 1)).card *
        2 ^ integrablePower (volume : Measure V) *
        (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : ℝ)) * 2, by positivity,
      fun f x ↦ ?_⟩
    apply (pow_mul_norm_iteratedFDeriv_fourier_le (f.smooth ⊤)
      (fun k n _hk _hn ↦ integrable_pow_mul_iteratedFDeriv _ f k n) le_top le_top x).trans
    simp only [mul_assoc]
    gcongr
    calc
    _ ≤ ∑ _ ∈ Finset.range (n + 1) ×ˢ Finset.range (k + 1),
        2 ^ integrablePower (volume : Measure V) *
          (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : ℝ)) * 2 *
          (Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1)).sup
          (schwartzSeminormFamily 𝕜 V E) f := by
      gcongr with p
      apply (f.integral_pow_mul_iteratedFDeriv_le 𝕜 ..).trans
      simp only [mul_assoc, two_mul]
      gcongr
      · have : (0, p.2) ∈ Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ
            Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p ↦ SchwartzMap.seminorm 𝕜 p.1 p.2) this)
      · have : (p.1 + integrablePower (volume : Measure V), p.2) ∈ Finset.range
            (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p ↦ SchwartzMap.seminorm 𝕜 p.1 p.2) this)
    _ = _ := by simp [mul_assoc]
/-
**SchwartzMap.instFourierTransform** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instFourierTransform : FourierTransform 𝓢(V, E) 𝓢(V, E) where fourier f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFourierTransform : FourierTransform 𝓢(V, E) 𝓢(V, E) where
  fourier f := fourierTransformCLM ℂ f
/-
**SchwartzMap.instFourierAdd** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instFourierAdd : FourierAdd 𝓢(V, E) 𝓢(V, E) where fourier_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
-/
instance instFourierAdd : FourierAdd 𝓢(V, E) 𝓢(V, E) where
  fourier_add := ContinuousLinearMap.map_add _
/-
**SchwartzMap.instFourierSMul** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instFourierSMul : FourierSMul 𝕜 𝓢(V, E) 𝓢(V, E) where fourier_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
-/
instance instFourierSMul : FourierSMul 𝕜 𝓢(V, E) 𝓢(V, E) where
  fourier_smul := (fourierTransformCLM 𝕜).map_smul
/-
**SchwartzMap.instContinuousFourier** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instContinuousFourier : ContinuousFourier 𝓢(V, E) 𝓢(V, E) where continuous
_fourier
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
instance instContinuousFourier : ContinuousFourier 𝓢(V, E) 𝓢(V, E) where
  continuous_fourier := ContinuousLinearMap.continuous _
/-
**SchwartzMap.fourier_coe** 是 Mathlib 中的一个引理，位于命名空间 `SchwartzMap`。
形式化陈述：fourier_coe (f : 𝓢(V, E)) : 𝓕 f = 𝓕 (f : V -> E)
参数：f : 𝓢(V, E)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fourier_coe (f : 𝓢(V, E)) : 𝓕 f = 𝓕 (f : V → E) := rfl

@[simp]
/-
**SchwartzMap.fourierTransformCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：fourierTransformCLM_apply (f : 𝓢(V, E)) : fourierTransformCLM 𝕜 f = 𝓕 f
参数：f : 𝓢(V, E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
-/
theorem fourierTransformCLM_apply (f : 𝓢(V, E)) :
    fourierTransformCLM 𝕜 f = 𝓕 f := rfl
/-
**SchwartzMap.instFourierTransformInv** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instFourierTransformInv : FourierTransformInv 𝓢(V, E) 𝓢(V, E) where fourie
rInv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFourierTransformInv : FourierTransformInv 𝓢(V, E) 𝓢(V, E) where
  fourierInv := (compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := V)))
      ∘L (fourierTransformCLM ℂ)
/-
**SchwartzMap.instFourierInvAdd** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instFourierInvAdd : FourierInvAdd 𝓢(V, E) 𝓢(V, E) where fourierInv_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
-/
instance instFourierInvAdd : FourierInvAdd 𝓢(V, E) 𝓢(V, E) where
  fourierInv_add := ContinuousLinearMap.map_add _
/-
**SchwartzMap.instFourierInvSMul** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instFourierInvSMul : FourierInvSMul 𝕜 𝓢(V, E) 𝓢(V, E) where fourierInv_smu
l
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
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
-/
instance instFourierInvSMul : FourierInvSMul 𝕜 𝓢(V, E) 𝓢(V, E) where
  fourierInv_smul := ((compCLMOfContinuousLinearEquiv 𝕜 (D := V) (E := V) (F := E)
    (LinearIsometryEquiv.neg ℝ (E := V))) ∘L (fourierTransformCLM 𝕜)).map_smul
/-
**SchwartzMap.instContinuousFourierInv** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instContinuousFourierInv : ContinuousFourierInv 𝓢(V, E) 𝓢(V, E) where cont
inuous_fourierInv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
instance instContinuousFourierInv : ContinuousFourierInv 𝓢(V, E) 𝓢(V, E) where
  continuous_fourierInv := ContinuousLinearMap.continuous _
/-
**SchwartzMap.fourierInv_coe** 是 Mathlib 中的一个引理，位于命名空间 `SchwartzMap`。
形式化陈述：fourierInv_coe (f : 𝓢(V, E)) : 𝓕⁻ f = 𝓕⁻ (f : V -> E)
参数：f : 𝓢(V, E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.fourierInv_eq_fourier_neg`：fourierInv_eq_fourier_neg (f : V -> E) (
w : V) : 𝓕⁻ f w = 𝓕 f (-w)
-/
lemma fourierInv_coe (f : 𝓢(V, E)) : 𝓕⁻ f = 𝓕⁻ (f : V → E) := by
  ext x
  exact (fourierInv_eq_fourier_neg f x).symm
/-
**SchwartzMap.fourierInv_apply_eq** 是 Mathlib 中的一个引理，位于命名空间 `SchwartzMap`。
形式化陈述：fourierInv_apply_eq (f : 𝓢(V, E)) : 𝓕⁻ f = (compCLMOfContinuousLinearEquiv
 Complex (LinearIsometryEquiv.neg Real (E
参数：f : 𝓢(V, E)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fourierInv_apply_eq (f : 𝓢(V, E)) :
    𝓕⁻ f = (compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := V))) (𝓕 f) := by
  rfl

variable [CompleteSpace E]
/-
**SchwartzMap.instFourierPair** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instFourierPair : FourierPair 𝓢(V, E) 𝓢(V, E) where fourierInv_fourier_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SchwartzMap.fourierInv_coe`：fourierInv_coe (f : 𝓢(V, E)) : 𝓕⁻ f = 𝓕⁻ (f 
: V -> E)
· 使用引理 `SchwartzMap.fourier_coe`：fourier_coe (f : 𝓢(V, E)) : 𝓕 f = 𝓕 (f : V -> E
)
· 使用定理 `Continuous.fourierInv_fourier_eq`：Continuous.fourierInv_fourier_eq (h : 
Continuous f) (hf : Integrable f) (h'f : Integrable (𝓕 f)) : 𝓕⁻ (𝓕 f) = f
· 使用定理 `SchwartzMap.continuous`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst
_3 : NormedS…
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
-/
instance instFourierPair : FourierPair 𝓢(V, E) 𝓢(V, E) where
  fourierInv_fourier_eq := by
    intro f
    ext x
    rw [fourierInv_coe, fourier_coe, f.continuous.fourierInv_fourier_eq f.integrable
      (𝓕 f).integrable]
/-
**SchwartzMap.instFourierInvPair** 是 Mathlib 中的一个实例，位于命名空间 `SchwartzMap`。
形式化陈述：instFourierInvPair : FourierInvPair 𝓢(V, E) 𝓢(V, E) where fourier_fourierI
nv_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SchwartzMap.fourier_coe`：fourier_coe (f : 𝓢(V, E)) : 𝓕 f = 𝓕 (f : V -> E
)
· 使用引理 `SchwartzMap.fourierInv_coe`：fourierInv_coe (f : 𝓢(V, E)) : 𝓕⁻ f = 𝓕⁻ (f 
: V -> E)
· 使用定理 `Continuous.fourier_fourierInv_eq`：Continuous.fourier_fourierInv_eq (h : 
Continuous f) (hf : Integrable f) (h'f : Integrable (𝓕 f)) : 𝓕 (𝓕⁻ f) = f
· 使用定理 `SchwartzMap.continuous`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst
_3 : NormedS…
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
-/
instance instFourierInvPair : FourierInvPair 𝓢(V, E) 𝓢(V, E) where
  fourier_fourierInv_eq := by
    intro f
    ext x
    rw [fourier_coe, fourierInv_coe, f.continuous.fourier_fourierInv_eq f.integrable
      (𝓕 f).integrable]

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE := FourierTransform.fourierCLE

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE_apply := FourierTransform.fourierCLE_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE_symm_apply := FourierTransform.fourierCLE_symm_apply

end definition

section eval

variable {𝕜' : Type*} [NormedField 𝕜']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace 𝕜' G] [SMulCommClass ℝ 𝕜' G]

variable (𝕜') in
/-
**SchwartzMap.fourier_evalCLM_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：fourier_evalCLM_eq (f : 𝓢(V, F ->L[Real] G)) (m : F) : 𝓕 (SchwartzMap.eval
CLM 𝕜' V G m f) = SchwartzMap.evalCLM 𝕜' V G m (𝓕 f)
参数：f : 𝓢(V, F ->L[Real] G)；m : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.fourier_continuousLinearMap_apply`：fourier_continuousLinearMap_appl
y {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] {f : V -> (F ->L[Real]
 E)} {a : F} {v : V} (hf : I…
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
-/
theorem fourier_evalCLM_eq (f : 𝓢(V, F →L[ℝ] G)) (m : F) :
    𝓕 (SchwartzMap.evalCLM 𝕜' V G m f) = SchwartzMap.evalCLM 𝕜' V G m (𝓕 f) := by
  ext x
  exact (fourier_continuousLinearMap_apply f.integrable).symm

end eval

section deriv

/-- The derivative of the Fourier transform is given by the Fourier transform of the multiplication
with `-(2 * π * Complex.I) • innerSL ℝ`. -/
/-
**SchwartzMap.fderivCLM_fourier_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：fderivCLM_fourier_eq (f : 𝓢(V, E)) : fderivCLM 𝕜 V E (𝓕 f) = 𝓕 (-(2 * π * 
Complex.I) • smulRightCLM Complex E (innerSL Real) f)
参数：f : 𝓢(V, E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.fderiv_fourier`：fderiv_fourier (hf_int : Integrable f) (hvf_int : I
ntegrable (fun v => ‖v‖ * ‖f v‖)) : fderiv Real (𝓕 f) = 𝓕 (fourierSMulRight (inn
erSL Real…
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `SchwartzMap.integrable_pow_mul`：integrable_pow_mul (f : 𝓢(D, V)) (k : Na
t) : Integrable (fun x => ‖x‖ ^ k * ‖f x‖) μ

--- 原说明 ---
The derivative of the Fourier transform is given by the Fourier transform of the
 multiplication
with `-(2 * π * Complex.I) • innerSL ℝ`.
-/
theorem fderivCLM_fourier_eq (f : 𝓢(V, E)) :
    fderivCLM 𝕜 V E (𝓕 f) = 𝓕 (-(2 * π * Complex.I) • smulRightCLM ℂ E (innerSL ℝ) f) := by
  ext1 x
  change fderiv ℝ (𝓕 ⇑f) x = 𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) f) x
  rw [fderiv_fourier f.integrable]
  simpa using f.integrable_pow_mul volume 1

set_option backward.isDefEq.respectTransparency false in
/-- The Fourier transform of the derivative is given by multiplication of
`(2 * π * Complex.I) • innerSL ℝ` with the Fourier transform. -/
/-
**SchwartzMap.fourier_fderivCLM_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：fourier_fderivCLM_eq (f : 𝓢(V, E)) : 𝓕 (fderivCLM 𝕜 V E f) = (2 * π * Comp
lex.I) • smulRightCLM Complex E (innerSL Real) (𝓕 f)
参数：f : 𝓢(V, E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Real.fourier_fderiv`：fourier_fderiv (hf : Integrable f) (h'f : Different
iable Real f) (hf' : Integrable (fderiv Real f)) : 𝓕 (fderiv Real f) = fourierSM
ulRight (…
· 使用引理 `SchwartzMap.integrable`：integrable (f : 𝓢(D, V)) : Integrable f μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
The Fourier transform of the derivative is given by multiplication of
`(2 * π * Complex.I) • innerSL ℝ` with the Fourier transform.
-/
theorem fourier_fderivCLM_eq (f : 𝓢(V, E)) :
    𝓕 (fderivCLM 𝕜 V E f) = (2 * π * Complex.I) • smulRightCLM ℂ E (innerSL ℝ) (𝓕 f) := by
  ext x m
  change 𝓕 (fderiv ℝ ⇑f) x m = _
  simp [fourier_fderiv f.integrable f.differentiable (fderivCLM ℝ V E f).integrable,
    innerSL_apply_apply ℝ, fourier_coe]

open LineDeriv

set_option backward.isDefEq.respectTransparency false in
/-- The line derivative in direction `m` of the Fourier transform is given by the Fourier transform
of the multiplication with `-(2 * π * Complex.I) • (inner ℝ · m)`. -/
/-
**SchwartzMap.lineDerivOp_fourier_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：lineDerivOp_fourier_eq (f : 𝓢(V, E)) (m : V) : ∂_{m} (𝓕 f) = 𝓕 (-(2 * π * 
Complex.I) • smulLeftCLM E (inner Real · m) f)
参数：f : 𝓢(V, E)；m : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `SchwartzMap.fderivCLM_fourier_eq`：fderivCLM_fourier_eq (f : 𝓢(V, E)) : f
derivCLM 𝕜 V E (𝓕 f) = 𝓕 (-(2 * π * Complex.I) • smulRightCLM Complex E (innerSL
 Real) f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SchwartzMap.fourier_evalCLM_eq`：fourier_evalCLM_eq (f : 𝓢(V, F ->L[Real]
 G)) (m : F) : 𝓕 (SchwartzMap.evalCLM 𝕜' V G m f) = SchwartzMap.evalCLM 𝕜' V G m
 (𝓕 f)
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `ContinuousLinearMap.hasTemperateGrowth`：∀ {E : Type u_5} {F : Type u_6} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
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
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `instCStarRingReal`：CStarRing ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
The line derivative in direction `m` of the Fourier transform is given by the Fo
urier transform
of the multiplication with `-(2 * π * Complex.I) • (inner ℝ · m)`.
-/
theorem lineDerivOp_fourier_eq (f : 𝓢(V, E)) (m : V) :
    ∂_{m} (𝓕 f) = 𝓕 (-(2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) f) := by
  change SchwartzMap.evalCLM ℝ V E m (fderivCLM ℝ V E (𝓕 f)) = _
  rw [fderivCLM_fourier_eq, ← fourier_evalCLM_eq]
  congr
  ext
  have : (inner ℝ · m).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  simp [this, innerSL_apply_apply ℝ]

set_option backward.isDefEq.respectTransparency false in
/-- The Fourier transform of line derivative in direction `m` is given by multiplication of
`(2 * π * Complex.I) • (inner ℝ · m)` with the Fourier transform. -/
/-
**SchwartzMap.fourier_lineDerivOp_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：fourier_lineDerivOp_eq (f : 𝓢(V, E)) (m : V) : 𝓕 (∂_{m} f) = (2 * π * Comp
lex.I) • smulLeftCLM E (inner Real · m) (𝓕 f)
参数：f : 𝓢(V, E)；m : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `ContinuousLinearMap.hasTemperateGrowth`：∀ {E : Type u_5} {F : Type u_6} 
[inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddComm
Group F]   [inst_3 : NormedS…
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
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `instCStarRingReal`：CStarRing ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.fourier_evalCLM_eq`：fourier_evalCLM_eq (f : 𝓢(V, F ->L[Real]
 G)) (m : F) : 𝓕 (SchwartzMap.evalCLM 𝕜' V G m f) = SchwartzMap.evalCLM 𝕜' V G m
 (𝓕 f)
· 使用定理 `SchwartzMap.fourier_fderivCLM_eq`：fourier_fderivCLM_eq (f : 𝓢(V, E)) : 𝓕
 (fderivCLM 𝕜 V E f) = (2 * π * Complex.I) • smulRightCLM Complex E (innerSL Rea
l) (𝓕 f)
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The Fourier transform of line derivative in direction `m` is given by multiplica
tion of
`(2 * π * Complex.I) • (inner ℝ · m)` with the Fourier transform.
-/
theorem fourier_lineDerivOp_eq (f : 𝓢(V, E)) (m : V) :
    𝓕 (∂_{m} f) = (2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) (𝓕 f) := by
  change 𝓕 (SchwartzMap.evalCLM ℝ V E m (fderivCLM ℝ V E f)) = _
  ext
  have : (inner ℝ · m).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  simp [fourier_evalCLM_eq ℝ, fourier_fderivCLM_eq, this, innerSL_apply_apply ℝ]

/-- The line derivative in direction `m` of the inverse Fourier transform is given by the inverse
Fourier transform of the multiplication with `(2 * π * Complex.I) • (inner ℝ · m)`. -/
/-
**SchwartzMap.lineDerivOp_fourierInv_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：lineDerivOp_fourierInv_eq (f : 𝓢(V, E)) (m : V) : ∂_{m} (𝓕⁻ f) = 𝓕⁻ ((2 * 
π * Complex.I) • smulLeftCLM E (inner Real · m) f)
参数：f : 𝓢(V, E)；m : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SchwartzMap.fourierInv_apply_eq`：fourierInv_apply_eq (f : 𝓢(V, E)) : 𝓕⁻ 
f = (compCLMOfContinuousLinearEquiv Complex (LinearIsometryEquiv.neg Real (E
· 使用定理 `SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv`：lineDerivOp_comp
CLMOfContinuousLinearEquiv (m : D) (g : D ≃L[Real] E) (f : 𝓢(E, F)) : ∂_{m} (com
pCLMOfContinuousLinearEquiv 𝕜 g f) = compCLM…
· 使用定理 `LineDeriv.lineDerivOp_left_neg`：lineDerivOp_left_neg (v : V) (x : E) : ∂
_{-v} x = - ∂_{v} x
· 使用定理 `SchwartzMap.instLineDerivAdd`：∀ {E : Type u_5} {F : Type u_8} [inst : No
rmedAddCommGroup E] [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSpace ℝ F]  
 [inst_3 : NormedS…
· 使用定理 `SchwartzMap.lineDerivOp_fourier_eq`：lineDerivOp_fourier_eq (f : 𝓢(V, E))
 (m : V) : ∂_{m} (𝓕 f) = 𝓕 (-(2 * π * Complex.I) • smulLeftCLM E (inner Real · m
) f)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `FourierTransform.fourier_neg`：fourier_neg (f : E) : 𝓕 (-f) = - 𝓕 f
· 使用定理 `FourierSMul.fourier_smul`：∀ {R : Type u_5} {E : Type u_6} {F : outParam 
(Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTransform E
 F} [self : Fo…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `FourierInvSMul.fourierInv_smul`：∀ {R : Type u_5} {E : Type u_6} {F : out
Param (Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTrans
formInv E F} [self :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The line derivative in direction `m` of the inverse Fourier transform is given b
y the inverse
Fourier transform of the multiplication with `(2 * π * Complex.I) • (inner ℝ · m
)`.
-/
theorem lineDerivOp_fourierInv_eq (f : 𝓢(V, E)) (m : V) :
    ∂_{m} (𝓕⁻ f) = 𝓕⁻ ((2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) f) := by
  simp [fourierInv_apply_eq, lineDerivOp_compCLMOfContinuousLinearEquiv, lineDerivOp_fourier_eq]

/-- The inverse Fourier transform of line derivative in direction `m` is given by multiplication of
`-(2 * π * Complex.I) • (inner ℝ · m)` with the inverse Fourier transform. -/
/-
**SchwartzMap.fourierInv_lineDerivOp_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：fourierInv_lineDerivOp_eq (f : 𝓢(V, E)) (m : V) : 𝓕⁻ (∂_{m} f) = -(2 * π *
 Complex.I) • smulLeftCLM E (inner Real · m) (𝓕⁻ f)
参数：f : 𝓢(V, E)；m : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.hasTemperateGrowth_inner_left`：hasTemperateGrowth_inner_left (c
 : H) : (inner Real · c).HasTemperateGrowth
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SchwartzMap.fourierInv_apply_eq`：fourierInv_apply_eq (f : 𝓢(V, E)) : 𝓕⁻ 
f = (compCLMOfContinuousLinearEquiv Complex (LinearIsometryEquiv.neg Real (E
· 使用定理 `SchwartzMap.fourier_lineDerivOp_eq`：fourier_lineDerivOp_eq (f : 𝓢(V, E))
 (m : V) : 𝓕 (∂_{m} f) = (2 * π * Complex.I) • smulLeftCLM E (inner Real · m) (𝓕
 f)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `SchwartzMap.smulLeftCLM_compCLMOfContinuousLinearEquiv`：smulLeftCLM_comp
CLMOfContinuousLinearEquiv {u : D -> 𝕜'} (hu : u.HasTemperateGrowth) (g : D ≃L[R
eal] E) (f : 𝓢(E, F)) : smulLeftCLM F u (com…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `SchwartzMap.smulLeftCLM_fun_neg`：smulLeftCLM_fun_neg {g : E -> 𝕜} (hg : 
g.HasTemperateGrowth) : smulLeftCLM F (fun x => -g x) = -smulLeftCLM F g
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The inverse Fourier transform of line derivative in direction `m` is given by mu
ltiplication of
`-(2 * π * Complex.I) • (inner ℝ · m)` with the inverse Fourier transform.
-/
theorem fourierInv_lineDerivOp_eq (f : 𝓢(V, E)) (m : V) :
    𝓕⁻ (∂_{m} f) = -(2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) (𝓕⁻ f) := by
  have : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp [fourierInv_apply_eq, fourier_lineDerivOp_eq,
    smulLeftCLM_compCLMOfContinuousLinearEquiv ℂ this, Function.comp_def, smulLeftCLM_fun_neg this]

end deriv

section fubini

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

variable [CompleteSpace E] [CompleteSpace F]

/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint.

Version where the multiplication is replaced by a general bilinear form `M`. -/
/-
**SchwartzMap.integral_bilin_fourier_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：integral_bilin_fourier_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L[Complex] 
F ->L[Complex] G) : ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕 g x)
参数：f : 𝓢(V, E)；g : 𝓢(V, F)；M : E ->L[Complex] F ->L[Complex] G。
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `flip_innerₗ`：∀ (F : Type u_3) [inst : SeminormedAddCommGroup F] [inst_1 
: InnerProductSpace ℝ F], (innerₗ F).flip = innerₗ F
· 使用定理 `VectorFourier.integral_bilin_fourierIntegral_eq_flip`：integral_bilin_fou
rierIntegral_eq_flip {f : V -> E} {g : W -> F} (M : E ->L[Complex] F ->L[Complex
] G) (he : Continuous e) (hL : Continuous …
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
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
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `Real.continuous_fourierChar`：continuous_fourierChar : Continuous 𝐞
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用引理 `SchwartzMap.integrable`：integrable (f : 𝓢(D, V)) : Integrable f μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…

--- 原说明 ---
The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoin
t.

Version where the multiplication is replaced by a general bilinear form `M`.
-/
theorem integral_bilin_fourier_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕 g x) := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip M (L := innerₗ V)
    continuous_fourierChar continuous_inner f.integrable g.integrable

/-- The Fourier transform satisfies `∫ 𝓕 f • g = ∫ f • 𝓕 g`, i.e., it is self-adjoint. -/
/-
**SchwartzMap.integral_fourier_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：integral_fourier_smul_eq (f : 𝓢(V, Complex)) (g : 𝓢(V, F)) : ∫ ξ, 𝓕 f ξ • 
g ξ = ∫ x, f x • 𝓕 g x
参数：f : 𝓢(V, Complex)；g : 𝓢(V, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.integral_bilin_fourier_eq`：integral_bilin_fourier_eq (f : 𝓢(
V, E)) (g : 𝓢(V, F)) (M : E ->L[Complex] F ->L[Complex] G) : ∫ ξ, M (𝓕 f ξ) (g ξ
) = ∫ x, M (f x) (𝓕 g x)
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
The Fourier transform satisfies `∫ 𝓕 f • g = ∫ f • 𝓕 g`, i.e., it is self-adjoin
t.
-/
theorem integral_fourier_smul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, F)) :
    ∫ ξ, 𝓕 f ξ • g ξ = ∫ x, f x • 𝓕 g x :=
  integral_bilin_fourier_eq f g (.lsmul ℂ ℂ)

/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint. -/
/-
**SchwartzMap.integral_fourier_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：integral_fourier_mul_eq (f : 𝓢(V, Complex)) (g : 𝓢(V, Complex)) : ∫ ξ, 𝓕 f
 ξ * g ξ = ∫ x, f x * 𝓕 g x
参数：f : 𝓢(V, Complex)；g : 𝓢(V, Complex)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.integral_bilin_fourier_eq`：integral_bilin_fourier_eq (f : 𝓢(
V, E)) (g : 𝓢(V, F)) (M : E ->L[Complex] F ->L[Complex] G) : ∫ ξ, M (𝓕 f ξ) (g ξ
) = ∫ x, M (f x) (𝓕 g x)
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoin
t.
-/
theorem integral_fourier_mul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, ℂ)) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x :=
  integral_bilin_fourier_eq f g (.mul ℂ ℂ)

/-- The inverse Fourier transform satisfies `∫ 𝓕⁻ f * g = ∫ f * 𝓕⁻ g`, i.e., it is self-adjoint.

Version where the multiplication is replaced by a general bilinear form `M`. -/
/-
**SchwartzMap.integral_bilin_fourierInv_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMa
p`。
形式化陈述：integral_bilin_fourierInv_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L[Comple
x] F ->L[Complex] G) : ∫ ξ, M (𝓕⁻ f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x)
参数：f : 𝓢(V, E)；g : 𝓢(V, F)；M : E ->L[Complex] F ->L[Complex] G。
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…
· 使用定理 `SchwartzMap.integral_bilin_fourier_eq`：integral_bilin_fourier_eq (f : 𝓢(
V, E)) (g : 𝓢(V, F)) (M : E ->L[Complex] F ->L[Complex] G) : ∫ ξ, M (𝓕 f ξ) (g ξ
) = ∫ x, M (f x) (𝓕 g x)

--- 原说明 ---
The inverse Fourier transform satisfies `∫ 𝓕⁻ f * g = ∫ f * 𝓕⁻ g`, i.e., it is s
elf-adjoint.

Version where the multiplication is replaced by a general bilinear form `M`.
-/
theorem integral_bilin_fourierInv_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕⁻ f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x) := by
  convert! (integral_bilin_fourier_eq (𝓕⁻ f) (𝓕⁻ g) M).symm
  · exact (FourierTransform.fourier_fourierInv_eq g).symm
  · exact (FourierTransform.fourier_fourierInv_eq f).symm

/-- The inverse Fourier transform satisfies `∫ 𝓕⁻ f • g = ∫ f • 𝓕⁻ g`, i.e., it is self-adjoint. -/
/-
**SchwartzMap.integral_fourierInv_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap
`。
形式化陈述：integral_fourierInv_smul_eq (f : 𝓢(V, Complex)) (g : 𝓢(V, F)) : ∫ ξ, 𝓕⁻ f 
ξ • g ξ = ∫ x, f x • 𝓕⁻ g x
参数：f : 𝓢(V, Complex)；g : 𝓢(V, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.integral_bilin_fourierInv_eq`：integral_bilin_fourierInv_eq (
f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L[Complex] F ->L[Complex] G) : ∫ ξ, M (𝓕⁻ f 
ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ

--- 原说明 ---
The inverse Fourier transform satisfies `∫ 𝓕⁻ f • g = ∫ f • 𝓕⁻ g`, i.e., it is s
elf-adjoint.
-/
theorem integral_fourierInv_smul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, F)) :
    ∫ ξ, 𝓕⁻ f ξ • g ξ = ∫ x, f x • 𝓕⁻ g x :=
  integral_bilin_fourierInv_eq f g (.lsmul ℂ ℂ)

/-- The inverse Fourier transform satisfies `∫ 𝓕⁻ f * g = ∫ f * 𝓕⁻ g`, i.e., it is self-adjoint. -/
/-
**SchwartzMap.integral_fourierInv_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`
。
形式化陈述：integral_fourierInv_mul_eq (f : 𝓢(V, Complex)) (g : 𝓢(V, Complex)) : ∫ ξ, 
𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x
参数：f : 𝓢(V, Complex)；g : 𝓢(V, Complex)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.integral_bilin_fourierInv_eq`：integral_bilin_fourierInv_eq (
f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L[Complex] F ->L[Complex] G) : ∫ ξ, M (𝓕⁻ f 
ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
The inverse Fourier transform satisfies `∫ 𝓕⁻ f * g = ∫ f * 𝓕⁻ g`, i.e., it is s
elf-adjoint.
-/
theorem integral_fourierInv_mul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, ℂ)) :
    ∫ ξ, 𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x :=
  integral_bilin_fourierInv_eq f g (.mul ℂ ℂ)
/-
**SchwartzMap.integral_sesq_fourier_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：integral_sesq_fourier_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L⋆[Complex] 
F ->L[Complex] G) : ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x)
参数：f : 𝓢(V, E)；g : 𝓢(V, F)；M : E ->L⋆[Complex] F ->L[Complex] G。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `SchwartzMap.fourierInv_coe`：fourierInv_coe (f : 𝓢(V, E)) : 𝓕⁻ f = 𝓕⁻ (f 
: V -> E)
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `flip_innerₗ`：∀ (F : Type u_3) [inst : SeminormedAddCommGroup F] [inst_1 
: InnerProductSpace ℝ F], (innerₗ F).flip = innerₗ F
· 使用定理 `VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip`：integral_sesq_f
ourierIntegral_eq_neg_flip {f : V -> E} {g : W -> F} (M : E ->L⋆[Complex] F ->L[
Complex] G) (he : Continuous e) (hL : Continu…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
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
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `Real.continuous_fourierChar`：continuous_fourierChar : Continuous 𝐞
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用引理 `SchwartzMap.integrable`：integrable (f : 𝓢(D, V)) : Integrable f μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
-/
theorem integral_sesq_fourier_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L⋆[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x) := by
  simpa [fourierInv_coe] using! VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip M
    (L := innerₗ V) continuous_fourierChar continuous_inner f.integrable g.integrable

/-- Plancherel's theorem for Schwartz functions.

Version where the inner product is replaced by a general sesquilinear form `M`. -/
/-
**SchwartzMap.integral_sesq_fourier_fourier** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzM
ap`。
形式化陈述：integral_sesq_fourier_fourier (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L⋆[Comp
lex] F ->L[Complex] G) : ∫ ξ, M (𝓕 f ξ) (𝓕 g ξ) = ∫ x, M (f x) (g x)
参数：f : 𝓢(V, E)；g : 𝓢(V, F)；M : E ->L⋆[Complex] F ->L[Complex] G。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FourierPair.fourierInv_fourier_eq`：∀ {E : Type u_5} {F : Type u_6} {inst
 : FourierTransform E F} {inst_1 : FourierTransformInv F E}   [self : FourierPai
r E F] (f : E), Fourier…
· 使用定理 `SchwartzMap.integral_sesq_fourier_eq`：integral_sesq_fourier_eq (f : 𝓢(V,
 E)) (g : 𝓢(V, F)) (M : E ->L⋆[Complex] F ->L[Complex] G) : ∫ ξ, M (𝓕 f ξ) (g ξ)
 = ∫ x, M (f x) (𝓕⁻ g x)

--- 原说明 ---
Plancherel's theorem for Schwartz functions.

Version where the inner product is replaced by a general sesquilinear form `M`.
-/
theorem integral_sesq_fourier_fourier (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L⋆[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (𝓕 g ξ) = ∫ x, M (f x) (g x) := by
  simpa using integral_sesq_fourier_eq f (𝓕 g) M

end fubini

section L1

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-
**SchwartzMap.norm_fourier_apply_le_toLp_one** 是 Mathlib 中的一个定理，位于命名空间 `Schwartz
Map`。
形式化陈述：norm_fourier_apply_le_toLp_one (f : 𝓢(V, F)) (x : V) : ‖𝓕 f x‖ <= ‖f.toLp 
1‖
参数：f : 𝓢(V, F)；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SchwartzMap.fourier_coe`：fourier_coe (f : 𝓢(V, E)) : 𝓕 f = 𝓕 (f : V -> E
)
· 使用引理 `Real.fourier_eq`：fourier_eq (f : V -> E) (w : V) : 𝓕 f w = ∫ v, 𝐞 (-⟪v, 
w⟫) • f v
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Circle.norm_smul`：∀ {E : Type u_4} [inst : SeminormedAddCommGroup E] [in
st_1 : NormedSpace ℂ E] (u : Circle) (v : E), ‖u • v‖ = ‖v‖
· 使用定理 `SchwartzMap.norm_toLp_one`：norm_toLp_one {f : 𝓢(E, F)} {μ : Measure E} [
hμ : μ.HasTemperateGrowth] : ‖f.toLp 1 μ‖ = ∫ x, ‖f x‖ ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_fourier_apply_le_toLp_one (f : 𝓢(V, F)) (x : V) :
    ‖𝓕 f x‖ ≤ ‖f.toLp 1‖ := calc
  _ = ‖∫ (v : V), 𝐞 (-inner ℝ v x) • f v‖ := by rw [fourier_coe, Real.fourier_eq]
  _ ≤ ∫ (v : V), ‖𝐞 (-inner ℝ v x) • f v‖ := norm_integral_le_integral_norm _
  _ = _ := by simp [norm_toLp_one]
/-
**SchwartzMap.norm_fourier_toBoundedContinuousFunction_le_toLp_one** 是 Mathlib 中
的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：norm_fourier_toBoundedContinuousFunction_le_toLp_one (f : 𝓢(V, F)) : ‖(𝓕 f
).toBoundedContinuousFunction‖ <= ‖f.toLp 1‖
参数：f : 𝓢(V, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `SchwartzMap.norm_fourier_apply_le_toLp_one`：norm_fourier_apply_le_toLp_o
ne (f : 𝓢(V, F)) (x : V) : ‖𝓕 f x‖ <= ‖f.toLp 1‖
-/
theorem norm_fourier_toBoundedContinuousFunction_le_toLp_one (f : 𝓢(V, F)) :
    ‖(𝓕 f).toBoundedContinuousFunction‖ ≤ ‖f.toLp 1‖ := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  simpa using norm_fourier_apply_le_toLp_one f
/-
**SchwartzMap.norm_fourier_Lp_top_leq_toLp_one** 是 Mathlib 中的一个定理，位于命名空间 `Schwar
tzMap`。
形式化陈述：norm_fourier_Lp_top_leq_toLp_one (f : 𝓢(V, F)) : ‖(𝓕 f).toLp ⊤‖ <= ‖f.toLp
 1‖
参数：f : 𝓢(V, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SchwartzMap.norm_toLp_top_le`：norm_toLp_top_le {f : 𝓢(E, F)} {μ : Measur
e E} [hμ : μ.HasTemperateGrowth] : ‖f.toLp ⊤ μ‖ <= SchwartzMap.seminorm Real 0 0
 f
· 使用定理 `SchwartzMap.seminorm_le_bound`：seminorm_le_bound (k n : Nat) (f : 𝓢(E, F
)) {M : Real} (hMp : 0 <= M) (hM : forall x, ‖x‖ ^ k * ‖iteratedFDeriv Real n f 
x‖ <= M) : Schwartz…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `norm_iteratedFDeriv_zero`：norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0
 f x‖ = ‖f x‖
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `SchwartzMap.norm_fourier_apply_le_toLp_one`：norm_fourier_apply_le_toLp_o
ne (f : 𝓢(V, F)) (x : V) : ‖𝓕 f x‖ <= ‖f.toLp 1‖
-/
theorem norm_fourier_Lp_top_leq_toLp_one (f : 𝓢(V, F)) :
    ‖(𝓕 f).toLp ⊤‖ ≤ ‖f.toLp 1‖ :=
  norm_toLp_top_le.trans (seminorm_le_bound ℝ 0 0 _ (by positivity)
    (by simpa using norm_fourier_apply_le_toLp_one f))

end L1

section L2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Plancherel's theorem for Schwartz functions. -/
/-
**SchwartzMap.integral_inner_fourier_fourier** 是 Mathlib 中的一个定理，位于命名空间 `Schwartz
Map`。
形式化陈述：∀ {V : Type u_3} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace
 ℝ V] [inst_2 : FiniteDimensional ℝ V]   [inst_3 : MeasurableSpace V] [inst_4 : 
BorelSpace V] {H : Type u_4} [inst_5 : NormedAddCommGroup H]   [inst_6 : InnerPr
oductSpace ℂ H] [CompleteSpace H] (f g : SchwartzMap V H),   ∫ (ξ : V), inner ℂ 
((FourierTransform.fourier f) ξ) ((FourierTransform.fourier g) ξ) = ∫ (x : V), i
nner ℂ (f x) (g x)
参数：f g : SchwartzMap V H；ξ : V；(FourierTransform.fourier f) ξ；(FourierTransform.
fourier g) ξ；x : V；f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SchwartzMap.integral_sesq_fourier_fourier`：integral_sesq_fourier_fourier
 (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L⋆[Complex] F ->L[Complex] G) : ∫ ξ, M (𝓕 
f ξ) (𝓕 g ξ) = ∫ x, M (f x) (g …

--- 原说明 ---
Plancherel's theorem for Schwartz functions.
-/
@[simp] theorem integral_inner_fourier_fourier (f g : 𝓢(V, H)) :
    ∫ ξ, ⟪𝓕 f ξ, 𝓕 g ξ⟫ = ∫ x, ⟪f x, g x⟫ :=
  integral_sesq_fourier_fourier f g (innerSL ℂ)
/-
**SchwartzMap.integral_norm_sq_fourier** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：integral_norm_sq_fourier (f : 𝓢(V, H)) : ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2
参数：f : 𝓢(V, H)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E₂ : Type u_
6} {F : Type u_9} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* R₂} 
[inst_2 : Semi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `SchwartzMap.integral_inner_fourier_fourier`：∀ {V : Type u_3} [inst : Nor
medAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : FiniteDimensional 
ℝ V]   [inst_3 : MeasurableSpace…
-/
theorem integral_norm_sq_fourier (f : 𝓢(V, H)) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    integral_inner_fourier_fourier f f
/-
**SchwartzMap.inner_fourier_toL2_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：inner_fourier_toL2_eq (f g : 𝓢(V, H)) : ⟪(𝓕 f).toLp 2, (𝓕 g).toLp 2⟫ = ⟪f.
toLp 2, g.toLp 2⟫
参数：f g : 𝓢(V, H)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.inner_toL2_toL2_eq`：inner_toL2_toL2_eq (f g : 𝓢(H, V)) (μ : 
Measure H
· 使用定理 `SchwartzMap.integral_inner_fourier_fourier`：∀ {V : Type u_3} [inst : Nor
medAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : FiniteDimensional 
ℝ V]   [inst_3 : MeasurableSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_fourier_toL2_eq (f g : 𝓢(V, H)) :
    ⟪(𝓕 f).toLp 2, (𝓕 g).toLp 2⟫ = ⟪f.toLp 2, g.toLp 2⟫ := by simp
/-
**SchwartzMap.norm_fourier_toL2_eq** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：∀ {V : Type u_3} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace
 ℝ V] [inst_2 : FiniteDimensional ℝ V]   [inst_3 : MeasurableSpace V] [inst_4 : 
BorelSpace V] {H : Type u_4} [inst_5 : NormedAddCommGroup H]   [inst_6 : InnerPr
oductSpace ℂ H] [CompleteSpace H] (f : SchwartzMap V H),   ‖(FourierTransform.fo
urier f).toLp 2 MeasureTheory.volume‖ = ‖f.toLp 2 MeasureTheory.volume‖
参数：f : SchwartzMap V H；FourierTransform.fourier f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth`：∀ {E : Ty
pe u_5} [inst : NormedAddCommGroup E] [inst_1 : MeasurableSpace E] [inst_2 : Nor
medSpace ℝ E]   [FiniteDimensional ℝ E] [BorelSpace…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_sqrt_re_inner`：norm_eq_sqrt_re_inner (x : E) : ‖x‖ = √(re ⟪x, x⟫
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.inner_fourier_toL2_eq`：inner_fourier_toL2_eq (f g : 𝓢(V, H))
 : ⟪(𝓕 f).toLp 2, (𝓕 g).toLp 2⟫ = ⟪f.toLp 2, g.toLp 2⟫
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem norm_fourier_toL2_eq (f : 𝓢(V, H)) :
    ‖(𝓕 f).toLp 2‖ = ‖f.toLp 2‖ := by
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_fourier_toL2_eq]

end L2

end SchwartzMap

