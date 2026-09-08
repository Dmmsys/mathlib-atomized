/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-! # Fourier multiplier on Schwartz functions and tempered distributions

We define a Fourier multiplier as continuous linear maps on Schwartz functions and tempered
distributions. The multiplier function is throughout assumed to have temperate growth.

## Main definitions
* `SchwartzMap.fourierMultiplierCLM`: Fourier multiplier on Schwartz functions
* `TemperedDistribution.fourierMultiplierCLM`: Fourier multiplier on tempered distribution

## Main statements
* `SchwartzMap.lineDeriv_eq_fourierMultiplierCLM`: the directional derivative is equal to the
  Fourier multiplier with `inner ℝ . m`.
* `SchwartzMap.laplacian_eq_fourierMultiplierCLM`: the Laplacian is equal to the Fourier multiplier
  with `‖·‖`.
* `TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM`: the distributional directional
  derivative is equal to the Fourier multiplier with `inner ℝ . m`.
* `TemperedDistribution.laplacian_eq_fourierMultiplierCLM`: the distributional Laplacian is equal to
  the Fourier multiplier with `‖·‖`.

-/

@[expose] public noncomputable section

variable {ι 𝕜 E F F₁ F₂ : Type*}

namespace SchwartzMap

/-! ## Schwartz functions -/

open scoped SchwartzMap

variable [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

variable (F) in
/-- Fourier multiplier on Schwartz functions. -/
/-
**SchwartzMap.fourierMultiplierCLM** 是 Mathlib 中的一个定义，位于命名空间 `SchwartzMap`。
形式化陈述：fourierMultiplierCLM (g : E -> 𝕜) : 𝓢(E, F) ->L[𝕜] 𝓢(E, F)
参数：g : E -> 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fourier multiplier on Schwartz functions.
-/
def fourierMultiplierCLM (g : E → 𝕜) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  fourierInvCLM 𝕜 𝓢(E, F) ∘L (smulLeftCLM F g) ∘L fourierCLM 𝕜 𝓢(E, F)
/-
**SchwartzMap.fourierMultiplierCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`
。
形式化陈述：fourierMultiplierCLM_apply (g : E -> 𝕜) (f : 𝓢(E, F)) : fourierMultiplierC
LM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f))
参数：g : E -> 𝕜；f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
-/
theorem fourierMultiplierCLM_apply (g : E → 𝕜) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f)) := by
  rfl

variable (𝕜) in
/-
**SchwartzMap.fourierMultiplierCLM_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap
`。
形式化陈述：fourierMultiplierCLM_ofReal {g : E -> Real} (hg : g.HasTemperateGrowth) (f
 : 𝓢(E, F)) : fourierMultiplierCLM F (fun x => RCLike.ofReal (K
参数：hg : g.HasTemperateGrowth；f : 𝓢(E, F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.fourierMultiplierCLM_apply`：fourierMultiplierCLM_apply (g : 
E -> 𝕜) (f : 𝓢(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f))
· 使用定理 `SchwartzMap.smulLeftCLM_ofReal`：smulLeftCLM_ofReal {g : E -> Real} (hg :
 g.HasTemperateGrowth) (f : 𝓢(E, F)) : smulLeftCLM F (fun x => RCLike.ofReal (K
-/
theorem fourierMultiplierCLM_ofReal {g : E → ℝ} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F (fun x ↦ RCLike.ofReal (K := 𝕜) (g x)) f =
    fourierMultiplierCLM F g f := by
  simp_rw [fourierMultiplierCLM_apply]
  congr 1
  exact smulLeftCLM_ofReal 𝕜 hg (𝓕 f)
/-
**SchwartzMap.fourierMultiplierCLM_smul** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：fourierMultiplierCLM_smul {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜)
 : fourierMultiplierCLM F (c • g) = c • fourierMultiplierCLM F g
参数：hg : g.HasTemperateGrowth；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.fourierMultiplierCLM_apply`：fourierMultiplierCLM_apply (g : 
E -> 𝕜) (f : 𝓢(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_smul`：smulLeftCLM_smul {g : E -> 𝕜} (hg : g.HasT
emperateGrowth) (c : 𝕜) : smulLeftCLM F (c • g) = c • smulLeftCLM F g
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `FourierInvSMul.fourierInv_smul`：∀ {R : Type u_5} {E : Type u_6} {F : out
Param (Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTrans
formInv E F} [self :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierMultiplierCLM_smul {g : E → 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜) :
    fourierMultiplierCLM F (c • g) = c • fourierMultiplierCLM F g := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smul hg]

variable (F) in
/-
**SchwartzMap.fourierMultiplierCLM_sum** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`。
形式化陈述：fourierMultiplierCLM_sum {g : ι -> E -> 𝕜} {s : Finset ι} (hg : forall i i
n s, (g i).HasTemperateGrowth) : fourierMultiplierCLM F (∑ i in s, g i ·) = ∑ i 
in s, fourierMultiplierCLM F (g i)
参数：hg : forall i in s, (g i).HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.fourierMultiplierCLM_apply`：fourierMultiplierCLM_apply (g : 
E -> 𝕜) (f : 𝓢(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_sum`：smulLeftCLM_sum {g : ι -> E -> 𝕜} {s : Fins
et ι} (hg : forall i in s, (g i).HasTemperateGrowth) : smulLeftCLM F (fun x => ∑
 i in s, g i x) =…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `FourierTransform.fourierInv_sum`：fourierInv_sum (f : ι -> E) (s : Finset
 ι) : 𝓕⁻ (∑ i in s, f i) = ∑ i in s, 𝓕⁻ (f i)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierMultiplierCLM_sum {g : ι → E → 𝕜} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) :
    fourierMultiplierCLM F (∑ i ∈ s, g i ·) = ∑ i ∈ s, fourierMultiplierCLM F (g i) := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_sum hg]

variable [CompleteSpace F]

@[simp]
/-
**SchwartzMap.fourierMultiplierCLM_const** 是 Mathlib 中的一个定理，位于命名空间 `SchwartzMap`
。
形式化陈述：fourierMultiplierCLM_const (c : 𝕜) : fourierMultiplierCLM F (fun (_ : E) =
> c) = c • ContinuousLinearMap.id _ _
参数：c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `SchwartzMap.fourierMultiplierCLM_apply`：fourierMultiplierCLM_apply (g : 
E -> 𝕜) (f : 𝓢(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f))
· 使用定理 `SchwartzMap.smulLeftCLM_const`：smulLeftCLM_const (c : 𝕜) : smulLeftCLM F
 (fun (_ : E) => c) = c • ContinuousLinearMap.id 𝕜 _
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `FourierInvSMul.fourierInv_smul`：∀ {R : Type u_5} {E : Type u_6} {F : out
Param (Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTrans
formInv E F} [self :…
· 使用定理 `FourierPair.fourierInv_fourier_eq`：∀ {E : Type u_5} {F : Type u_6} {inst
 : FourierTransform E F} {inst_1 : FourierTransformInv F E}   [self : FourierPai
r E F] (f : E), Fourier…
· 使用定理 `SchwartzMap.instIsSMulApply`：∀ {𝕜 : Type u_2} {E : Type u_5} {F : Type u
_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedA
ddCommGroup F] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierMultiplierCLM_const (c : 𝕜) :
    fourierMultiplierCLM F (fun (_ : E) ↦ c) = c • ContinuousLinearMap.id _ _ := by
  ext f x
  simp [fourierMultiplierCLM_apply]
/-
**SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply** 是 Mathlib 中的一个定理
，位于命名空间 `SchwartzMap`。
形式化陈述：fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E -> 𝕜} (hg₁ : g₁
.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) : fourierMultip
lierCLM F g₁ (fourierMultiplierCLM F g₂ f) = fourierMultiplierCLM F (g₁ * g₂) f
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth；f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.fourierMultiplierCLM_apply`：fourierMultiplierCLM_apply (g : 
E -> 𝕜) (f : 𝓢(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f))
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…
· 使用定理 `SchwartzMap.smulLeftCLM_smulLeftCLM_apply`：smulLeftCLM_smulLeftCLM_apply
 {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f
 : 𝓢(E, F)) : smulLeftCLM F g₁ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E → 𝕜}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g₁ (fourierMultiplierCLM F g₂ f) =
    fourierMultiplierCLM F (g₁ * g₂) f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]
/-
**SchwartzMap.fourierMultiplierCLM_compL_fourierMultiplierCLM** 是 Mathlib 中的一个定理
，位于命名空间 `SchwartzMap`。
形式化陈述：fourierMultiplierCLM_compL_fourierMultiplierCLM {g₁ g₂ : E -> 𝕜} (hg₁ : g₁
.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) : fourierMultiplierCLM F g₁ ∘
L fourierMultiplierCLM F g₂ = fourierMultiplierCLM F (g₁ * g₂)
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply`：fourierMult
iplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E -> 𝕜} (hg₁ : g₁.HasTemperateGrow
th) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierMultiplierCLM_compL_fourierMultiplierCLM {g₁ g₂ : E → 𝕜}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F g₁ ∘L fourierMultiplierCLM F g₂ =
    fourierMultiplierCLM F (g₁ * g₂) := by
  ext1 f
  simp [fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ hg₂]

open LineDeriv Real
/-
**SchwartzMap.lineDeriv_eq_fourierMultiplierCLM** 是 Mathlib 中的一个定理，位于命名空间 `Schwa
rtzMap`。
形式化陈述：lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢(E, F)) : ∂_{m} f = (2 * π
 * Complex.I) • fourierMultiplierCLM F (inner Real · m) f
参数：m : E；f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
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
· 使用定理 `SchwartzMap.fourierMultiplierCLM_apply`：fourierMultiplierCLM_apply (g : 
E -> 𝕜) (f : 𝓢(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FourierInvSMul.fourierInv_smul`：∀ {R : Type u_5} {E : Type u_6} {F : out
Param (Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTrans
formInv E F} [self :…
· 使用定理 `SchwartzMap.fourier_lineDerivOp_eq`：fourier_lineDerivOp_eq (f : 𝓢(V, E))
 (m : V) : 𝓕 (∂_{m} f) = (2 * π * Complex.I) • smulLeftCLM E (inner Real · m) (𝓕
 f)
· 使用定理 `FourierPair.fourierInv_fourier_eq`：∀ {E : Type u_5} {F : Type u_6} {inst
 : FourierTransform E F} {inst_1 : FourierTransformInv F E}   [self : FourierPai
r E F] (f : E), Fourier…
-/
theorem lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢(E, F)) :
    ∂_{m} f = (2 * π * Complex.I) • fourierMultiplierCLM F (inner ℝ · m) f := by
  rw [fourierMultiplierCLM_apply, ← FourierTransform.fourierInv_smul, ← fourier_lineDerivOp_eq,
    FourierTransform.fourierInv_fourier_eq]

open Laplacian
/-
**SchwartzMap.laplacian_eq_fourierMultiplierCLM** 是 Mathlib 中的一个定理，位于命名空间 `Schwa
rtzMap`。
形式化陈述：laplacian_eq_fourierMultiplierCLM (f : 𝓢(E, F)) : Δ f = -(2 * π) ^ 2 • fou
rierMultiplierCLM F (‖·‖ ^ 2) f
参数：f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasTemperateGrowth.fun_pow`：∀ {R : Type u_3} {E : Type u_5} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedRing R]   
[inst_3 : NormedAlgebra ℝ…
· 使用定理 `Function.hasTemperateGrowth_inner_left`：hasTemperateGrowth_inner_left (c
 : H) : (inner Real · c).HasTemperateGrowth
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SchwartzMap.laplacian_eq_sum`：laplacian_eq_sum [Fintype ι] (b : Orthonor
malBasis ι Real E) (f : 𝓢(E, F)) : Δ f = ∑ i, ∂_{b i} (∂_{b i} f)
· 使用定理 `SchwartzMap.fourierMultiplierCLM.congr_simp`：∀ {𝕜 : Type u_2} {E : Type 
u_3} (F : Type u_4) [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 
: NormedAddCommGroup F] [inst_3 :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.sum_sq_inner_left`：sum_sq_inner_left {ι E : Type*} [Nor
medAddCommGroup E] [InnerProductSpace Real E] [Fintype ι] (b : OrthonormalBasis 
ι Real E) (x : E) : ∑ i …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SchwartzMap.fourierMultiplierCLM_sum`：fourierMultiplierCLM_sum {g : ι ->
 E -> 𝕜} {s : Finset ι} (hg : forall i in s, (g i).HasTemperateGrowth) : fourier
MultiplierCLM F (∑ i in s,…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `SchwartzMap.ext`：ext {f g : 𝓢(E, F)} (h : forall x, (f : E -> F) x = g x
) : f = g
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `SchwartzMap.instIsSMulApply`：∀ {𝕜 : Type u_2} {E : Type u_5} {F : Type u
_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedA
ddCommGroup F] [i…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SchwartzMap.lineDeriv_eq_fourierMultiplierCLM`：lineDeriv_eq_fourierMulti
plierCLM (m : E) (f : 𝓢(E, F)) : ∂_{m} f = (2 * π * Complex.I) • fourierMultipli
erCLM F (inner Real · m) f
· 使用定理 `SchwartzMap.fourierMultiplierCLM_ofReal`：fourierMultiplierCLM_ofReal {g 
: E -> Real} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) : fourierMultiplierCLM F 
(fun x => RCLike.ofReal (K
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `RingHom.map_zero'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemir
ing α] [inst_1 : NonAssocSemiring β] (self : α →+* β),   (↑↑self).toFun 0 = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 78 条，此处仅展示前 30 条）
-/
theorem laplacian_eq_fourierMultiplierCLM (f : 𝓢(E, F)) :
    Δ f = -(2 * π) ^ 2 • fourierMultiplierCLM F (‖·‖ ^ 2) f := by
  let ι := Fin (Module.finrank ℝ E)
  let b := stdOrthonormalBasis ℝ E
  have : ∀ i (hi : i ∈ Finset.univ), (inner ℝ · (b i) ^ 2).HasTemperateGrowth := by
    fun_prop
  simp_rw [laplacian_eq_sum b, ← b.sum_sq_inner_left, fourierMultiplierCLM_sum F this,
    _root_.sum_apply, Finset.smul_sum]
  congr 1
  ext i x
  simp_rw [smul_apply, lineDeriv_eq_fourierMultiplierCLM]
  rw [← fourierMultiplierCLM_ofReal ℂ (by fun_prop)]
  simp_rw [map_smul, smul_apply, smul_smul]
  congr 1
  · ring_nf
    simp
  · rw [fourierMultiplierCLM_ofReal ℂ (by fun_prop),
      fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
    simp [sq, Pi.mul_def]

end SchwartzMap

namespace TemperedDistribution

/-! ## Tempered distributions -/

open scoped SchwartzMap

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

variable (F) in
/-- Fourier multiplier on tempered distributions. -/
/-
**TemperedDistribution.fourierMultiplierCLM** 是 Mathlib 中的一个定义，位于命名空间 `TemperedD
istribution`。
形式化陈述：fourierMultiplierCLM (g : E -> Complex) : 𝓢'(E, F) ->L[Complex] 𝓢'(E, F)
参数：g : E -> Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fourier multiplier on tempered distributions.
-/
def fourierMultiplierCLM (g : E → ℂ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierInvCLM ℂ 𝓢'(E, F) ∘L (smulLeftCLM F g) ∘L fourierCLM ℂ 𝓢'(E, F)
/-
**TemperedDistribution.fourierMultiplierCLM_apply** 是 Mathlib 中的一个定理，位于命名空间 `Tem
peredDistribution`。
形式化陈述：fourierMultiplierCLM_apply (g : E -> Complex) (f : 𝓢'(E, F)) : fourierMult
iplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f))
参数：g : E -> Complex；f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem fourierMultiplierCLM_apply (g : E → ℂ) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f)) := by
  rfl

@[simp]
/-
**TemperedDistribution.fourierMultiplierCLM_apply_apply** 是 Mathlib 中的一个定理，位于命名空
间 `TemperedDistribution`。
形式化陈述：fourierMultiplierCLM_apply_apply (g : E -> Complex) (f : 𝓢'(E, F)) (u : 𝓢(
E, Complex)) : fourierMultiplierCLM F g f u = f (𝓕 (SchwartzMap.smulLeftCLM Comp
lex g (𝓕⁻ u)))
参数：g : E -> Complex；f : 𝓢'(E, F)；u : 𝓢(E, Complex)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem fourierMultiplierCLM_apply_apply (g : E → ℂ) (f : 𝓢'(E, F)) (u : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F g f u = f (𝓕 (SchwartzMap.smulLeftCLM ℂ g (𝓕⁻ u))) := by
  rfl

@[simp]
/-
**TemperedDistribution.fourierMultiplierCLM_const** 是 Mathlib 中的一个定理，位于命名空间 `Tem
peredDistribution`。
形式化陈述：fourierMultiplierCLM_const (c : Complex) : fourierMultiplierCLM F (fun (_ 
: E) => c) = c • ContinuousLinearMap.id _ _
参数：c : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_apply_apply`：fourierMultiplier
CLM_apply_apply (g : E -> Complex) (f : 𝓢'(E, F)) (u : 𝓢(E, Complex)) : fourierM
ultiplierCLM F g f u = f (𝓕 (SchwartzMap.sm…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_const`：smulLeftCLM_const (c : 𝕜) : smulLeftCLM F
 (fun (_ : E) => c) = c • ContinuousLinearMap.id 𝕜 _
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `FourierSMul.fourier_smul`：∀ {R : Type u_5} {E : Type u_6} {F : outParam 
(Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTransform E
 F} [self : Fo…
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `UniformConvergenceCLM.instIsSMulApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierMultiplierCLM_const (c : ℂ) :
    fourierMultiplierCLM F (fun (_ : E) ↦ c) = c • ContinuousLinearMap.id _ _ := by
  ext
  simp
/-
**TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply** 是 Mathl
ib 中的一个定理，位于命名空间 `TemperedDistribution`。
形式化陈述：fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E -> Complex} (hg
₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) : fourie
rMultiplierCLM F g₂ (fourierMultiplierCLM F g₁ f) = fourierMultiplierCLM F (g₁ *
 g₂) f
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth；f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_apply`：fourierMultiplierCLM_ap
ply (g : E -> Complex) (f : 𝓢'(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLef
tCLM F g (𝓕 f))
· 使用定理 `FourierInvPair.fourier_fourierInv_eq`：∀ {E : Type u_5} {F : Type u_6} {i
nst : FourierTransform F E} {inst_1 : FourierTransformInv E F}   [self : Fourier
InvPair E F] (f : E), Four…
· 使用定理 `TemperedDistribution.smulLeftCLM_smulLeftCLM_apply`：smulLeftCLM_smulLeft
CLM_apply {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemp
erateGrowth) (f : 𝓢'(E, F)) : smulLeftCL…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E → ℂ}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F g₂ (fourierMultiplierCLM F g₁ f) =
    fourierMultiplierCLM F (g₁ * g₂) f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]
/-
**TemperedDistribution.fourierMultiplierCLM_compL_fourierMultiplierCLM** 是 Mathl
ib 中的一个定理，位于命名空间 `TemperedDistribution`。
形式化陈述：fourierMultiplierCLM_compL_fourierMultiplierCLM {g₁ g₂ : E -> Complex} (hg
₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) : fourierMultiplierCLM 
F g₂ ∘L fourierMultiplierCLM F g₁ = fourierMultiplierCLM F (g₁ * g₂)
参数：hg₁ : g₁.HasTemperateGrowth；hg₂ : g₂.HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply`：fo
urierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E -> Complex} (hg₁ : g₁.H
asTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierMultiplierCLM_compL_fourierMultiplierCLM {g₁ g₂ : E → ℂ}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F g₂ ∘L fourierMultiplierCLM F g₁ =
    fourierMultiplierCLM F (g₁ * g₂) := by
  ext1 f
  simp [fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ hg₂]
/-
**TemperedDistribution.fourierMultiplierCLM_smul** 是 Mathlib 中的一个定理，位于命名空间 `Temp
eredDistribution`。
形式化陈述：fourierMultiplierCLM_smul {g : E -> Complex} (hg : g.HasTemperateGrowth) (
c : Complex) : fourierMultiplierCLM F (c • g) = c • fourierMultiplierCLM F g
参数：hg : g.HasTemperateGrowth；c : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_apply`：fourierMultiplierCLM_ap
ply (g : E -> Complex) (f : 𝓢'(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLef
tCLM F g (𝓕 f))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TemperedDistribution.smulLeftCLM_smul`：smulLeftCLM_smul {g : E -> Comple
x} (hg : g.HasTemperateGrowth) (c : Complex) : smulLeftCLM F (c • g) = c • smulL
eftCLM F g
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `FourierInvSMul.fourierInv_smul`：∀ {R : Type u_5} {E : Type u_6} {F : out
Param (Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTrans
formInv E F} [self :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierMultiplierCLM_smul {g : E → ℂ} (hg : g.HasTemperateGrowth) (c : ℂ) :
    fourierMultiplierCLM F (c • g) = c • fourierMultiplierCLM F g := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smul hg]

variable (F) in
/-
**TemperedDistribution.fourierMultiplierCLM_sum** 是 Mathlib 中的一个定理，位于命名空间 `Tempe
redDistribution`。
形式化陈述：fourierMultiplierCLM_sum {g : ι -> E -> Complex} {s : Finset ι} (hg : fora
ll i in s, (g i).HasTemperateGrowth) : fourierMultiplierCLM F (∑ i in s, g i ·) 
= ∑ i in s, fourierMultiplierCLM F (g i)
参数：hg : forall i in s, (g i).HasTemperateGrowth。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_apply_apply`：fourierMultiplier
CLM_apply_apply (g : E -> Complex) (f : 𝓢'(E, F)) (u : 𝓢(E, Complex)) : fourierM
ultiplierCLM F g f u = f (𝓕 (SchwartzMap.sm…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_sum`：smulLeftCLM_sum {g : ι -> E -> 𝕜} {s : Fins
et ι} (hg : forall i in s, (g i).HasTemperateGrowth) : smulLeftCLM F (fun x => ∑
 i in s, g i x) =…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `FourierTransform.fourier_sum`：fourier_sum (f : ι -> E) (s : Finset ι) : 
𝓕 (∑ i in s, f i) = ∑ i in s, 𝓕 (f i)
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `UniformConvergenceCLM.instIsZeroApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2}
 [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3
}   (F : Type u_4) [inst_2 …
· 使用定理 `UniformConvergenceCLM.instIsAddApply`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2} 
[inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] (σ : 𝕜₁ →+* 𝕜₂) {E : Type u_3}
   (F : Type u_4) [inst_2 …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierMultiplierCLM_sum {g : ι → E → ℂ} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) :
    fourierMultiplierCLM F (∑ i ∈ s, g i ·) = ∑ i ∈ s, fourierMultiplierCLM F (g i) := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sum hg]

section embedding

variable [CompleteSpace F]

/-
**TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq** 是 Mat
hlib 中的一个定理，位于命名空间 `TemperedDistribution`。
形式化陈述：fourierMultiplierCLM_toTemperedDistributionCLM_eq {g : E -> Complex} (hg :
 g.HasTemperateGrowth) (f : 𝓢(E, F)) : fourierMultiplierCLM F g (f : 𝓢'(E, F)) =
 SchwartzMap.fourierMultiplierCLM F g f
参数：hg : g.HasTemperateGrowth；f : 𝓢(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
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
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_apply_apply`：fourierMultiplier
CLM_apply_apply (g : E -> Complex) (f : 𝓢'(E, F)) (u : 𝓢(E, Complex)) : fourierM
ultiplierCLM F g f u = f (𝓕 (SchwartzMap.sm…
· 使用定理 `SchwartzMap.toTemperedDistributionCLM_apply_apply`：toTemperedDistributio
nCLM_apply_apply (μ : Measure E
· 使用定理 `SchwartzMap.integral_fourier_smul_eq`：integral_fourier_smul_eq (f : 𝓢(V,
 Complex)) (g : 𝓢(V, F)) : ∫ ξ, 𝓕 f ξ • g ξ = ∫ x, f x • 𝓕 g x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SchwartzMap.smulLeftCLM_apply_apply`：smulLeftCLM_apply_apply {g : E -> 𝕜
} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) : smulLeftCLM F g f x = g x 
• f x
· 使用定理 `SchwartzMap.fourierMultiplierCLM_apply`：fourierMultiplierCLM_apply (g : 
E -> 𝕜) (f : 𝓢(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f))
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fourierMultiplierCLM_toTemperedDistributionCLM_eq {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g (f : 𝓢'(E, F)) = SchwartzMap.fourierMultiplierCLM F g f := by
  ext u
  simp [SchwartzMap.integral_fourier_smul_eq, SchwartzMap.fourierMultiplierCLM_apply g f,
    ← SchwartzMap.integral_fourierInv_smul_eq, hg, smul_smul, mul_comm]

end embedding

open LineDeriv Real

/-
**TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM** 是 Mathlib 中的一个定理，位于命名
空间 `TemperedDistribution`。
形式化陈述：lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢'(E, F)) : ∂_{m} f = (2 * 
π * Complex.I) • fourierMultiplierCLM F (inner Real · m) f
参数：m : E；f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_apply`：fourierMultiplierCLM_ap
ply (g : E -> Complex) (f : 𝓢'(E, F)) : fourierMultiplierCLM F g f = 𝓕⁻ (smulLef
tCLM F g (𝓕 f))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FourierInvSMul.fourierInv_smul`：∀ {R : Type u_5} {E : Type u_6} {F : out
Param (Type u_7)} {inst : SMul R E} {inst_1 : SMul R F}   {inst_2 : FourierTrans
formInv E F} [self :…
· 使用定理 `TemperedDistribution.fourier_lineDerivOp_eq`：fourier_lineDerivOp_eq (f :
 𝓢'(E, F)) (m : E) : 𝓕 (∂_{m} f) = (2 * π * Complex.I) • smulLeftCLM F (inner Re
al · m) (𝓕 f)
· 使用定理 `FourierPair.fourierInv_fourier_eq`：∀ {E : Type u_5} {F : Type u_6} {inst
 : FourierTransform E F} {inst_1 : FourierTransformInv F E}   [self : FourierPai
r E F] (f : E), Fourier…
-/
theorem lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢'(E, F)) :
    ∂_{m} f = (2 * π * Complex.I) • fourierMultiplierCLM F (inner ℝ · m) f := by
  rw [fourierMultiplierCLM_apply, ← FourierTransform.fourierInv_smul, ← fourier_lineDerivOp_eq,
    FourierTransform.fourierInv_fourier_eq]

open Laplacian
/-
**TemperedDistribution.laplacian_eq_fourierMultiplierCLM** 是 Mathlib 中的一个定理，位于命名
空间 `TemperedDistribution`。
形式化陈述：laplacian_eq_fourierMultiplierCLM (f : 𝓢'(E, F)) : Δ f = -(2 * π) ^ 2 • fo
urierMultiplierCLM F (fun x => Complex.ofReal (‖x‖ ^ 2)) f
参数：f : 𝓢'(E, F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasTemperateGrowth.fun_pow`：∀ {R : Type u_3} {E : Type u_5} [in
st : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedRing R]   
[inst_3 : NormedAlgebra ℝ…
· 使用定理 `Function.HasTemperateGrowth.comp`：∀ {D : Type u_4} {E : Type u_5} {F : T
ype u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : No
rmedAddCommGroup F] [i…
· 使用定理 `Function.Complex.hasTemperateGrowth_ofReal`：Function.HasTemperateGrowth 
Complex.ofReal
· 使用定理 `Function.hasTemperateGrowth_inner_left`：hasTemperateGrowth_inner_left (c
 : H) : (inner Real · c).HasTemperateGrowth
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TemperedDistribution.laplacian_eq_sum`：laplacian_eq_sum [Fintype ι] (b :
 OrthonormalBasis ι Real E) (f : 𝓢'(E, F)) : Δ f = ∑ i, ∂_{b i} (∂_{b i} f)
· 使用定理 `TemperedDistribution.fourierMultiplierCLM.congr_simp`：∀ {E : Type u_3} (
F : Type u_4) [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup F]   [i
nst_2 : InnerProductSpace ℝ E] [inst_3 : N…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.sum_sq_inner_left`：sum_sq_inner_left {ι E : Type*} [Nor
medAddCommGroup E] [InnerProductSpace Real E] [Fintype ι] (b : OrthonormalBasis 
ι Real E) (x : E) : ∑ i …
· 使用定理 `Complex.ofReal_sum`：ofReal_sum (f : α -> Real) : ((∑ i in s, f i : Real)
 : Complex) = ∑ i in s, (f i : Complex)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `TemperedDistribution.fourierMultiplierCLM_sum`：fourierMultiplierCLM_sum 
{g : ι -> E -> Complex} {s : Finset ι} (hg : forall i in s, (g i).HasTemperateGr
owth) : fourierMultiplierCLM F (∑ i…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `UniformConvergenceCLM.ext`：ext [TopologicalSpace F] {𝔖 : Set (Set E)} {f
 g : E ->SLᵤ[σ, 𝔖] F} (h : forall x, f x = g x) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM`：lineDeriv_eq_fou
rierMultiplierCLM (m : E) (f : 𝓢'(E, F)) : ∂_{m} f = (2 * π * Complex.I) • fouri
erMultiplierCLM F (inner Real · m) f
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
（共 81 条，此处仅展示前 30 条）
-/
theorem laplacian_eq_fourierMultiplierCLM (f : 𝓢'(E, F)) :
    Δ f = -(2 * π) ^ 2 • fourierMultiplierCLM F (fun x ↦ Complex.ofReal (‖x‖ ^ 2)) f := by
  let ι := Fin (Module.finrank ℝ E)
  let b := stdOrthonormalBasis ℝ E
  have : ∀ i (hi : i ∈ Finset.univ),
      (fun x ↦ Complex.ofReal (inner ℝ x (b i)) ^ 2).HasTemperateGrowth := by
    fun_prop
  simp_rw [laplacian_eq_sum b, ← b.sum_sq_inner_left, Complex.ofReal_sum, Complex.ofReal_pow,
    fourierMultiplierCLM_sum F this, sum_apply, Finset.smul_sum]
  congr 1
  ext i x
  simp_rw [lineDeriv_eq_fourierMultiplierCLM, map_smul, smul_smul]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop),
    ← Complex.coe_smul (-(2 * π) ^ 2)]
  congr 4
  · ring_nf
    simp
  · simp [sq, Pi.mul_def]

end TemperedDistribution

