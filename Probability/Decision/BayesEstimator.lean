/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Decision.Risk.Defs
public import Mathlib.Probability.Kernel.Posterior

import Mathlib.Probability.Decision.Risk.Basic

/-!
# Bayes estimator

Let `Θ` be a parameter space, `𝓧` a data space, `𝓨` a prediction space, `P : Kernel Θ 𝓧` a
data generating kernel, `π` a prior on the parameter space, and `ℓ : Θ → 𝓨 → ℝ≥0∞` a loss function.

An estimator (a `Kernel 𝓧 𝓨`) is said to be a Bayes estimator if it attains the Bayes risk for
the estimation problem.
It can be written as a measurable function `x ↦ argmin_y P†π(x)[θ ↦ ℓ θ y]`
for `(P ∘ₘ π)`-almost every `x`, where `P†π` is the posterior kernel, whenever we can select
the argmin in a measurable way.

## Main definitions

* `IsBayesEstimator`: an estimator is a Bayes estimator if it attains the Bayes risk for the prior.
* `IsArgminEstimator`: a measurable function `f : 𝓧 → 𝓨` is an argmin estimator
  if for `(P ∘ₘ π)`-almost every `x` the value `f x` belongs to `argmin_y P†π(x)[θ ↦ ℓ θ y]`.
* `HasArgminEstimator`: the estimation problem admits an argmin estimator.
  That is, we can choose the argmin of the posterior expected loss in a measurable way.

## Main statements

* `lintegral_iInf_posterior_le_bayesRisk`: the Bayes risk with respect to a prior is bounded
  from below by the integral over the data (with distribution `P ∘ₘ π`) of the infimum over the
  possible predictions `y` of the posterior loss `∫⁻ θ, ℓ θ y ∂((P†π) x)`:
  `∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) ≤ bayesRisk ℓ P π`
* `IsArgminEstimator.isBayesEstimator`: an argmin Bayes estimator is a Bayes estimator.
  That is, it minimizes the Bayesian risk.
* `bayesRisk_eq_of_hasArgminEstimator`: if the estimation problem admits an argmin estimator,
  then the Bayesian risk attains the risk lower bound `∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂(P ∘ₘ π)`.

## TODO

Once Mathlib has measurable selection theorems, we will be able to prove `HasArgminEstimator` under
general conditions on the measurable spaces `𝓧` and/or `𝓨`.

-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

section Posterior

variable [StandardBorelSpace Θ] [Nonempty Θ]

/-- The average risk of an estimator `κ` with respect to a prior `π` can be expressed as
an integral in the following way: `R_π(κ) = ((P†π × κ) ∘ P ∘ π)[(θ, y) ↦ ℓ θ y]`. -/
/-
**ProbabilityTheory.avgRisk_eq_lintegral_posterior_prod** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：avgRisk_eq_lintegral_posterior_prod (hl : Measurable (Function.uncurry ℓ))
 (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : M
easure Θ) [IsFiniteMeasure π] : avgRisk ℓ P κ π = ∫⁻ θy, ℓ θy.1 θy.2 ∂(((P†π) ×ₖ
 κ) ∘ₘ (P ∘ₘ π))
参数：hl : Measurable (Function.uncurry ℓ)；P : Kernel Θ 𝓧；κ : Kernel 𝓧 𝓨；π : Measur
e Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.avgRisk.eq_1`：∀ {Θ : Type u_1} {𝓧 : Type u_2} {𝓨 : Typ
e u_3} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace
 𝓨} (ℓ : Θ → 𝓨 → ENN…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.lintegral_compProd`：lintegral_compProd [SFinite μ]
 [IsSFiniteKernel κ] {f : α × β -> Real>=0∞} (hf : Measurable f) : ∫⁻ x, f x ∂(μ
 otimesₘ κ) = ∫⁻ a, ∫⁻ b, f (a…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.comp`：∀ {α : Type u_1} {β : Typ
e u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {mγ : 
MeasurableSpace γ} (η : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `MeasureTheory.Measure.parallelComp_comp_compProd`：parallelComp_comp_comp
Prod [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η] : (Kernel.id ∥ₖ η)
 ∘ₘ (μ otimesₘ κ) = μ otimesₘ (η ∘ₖ κ)
· 使用引理 `ProbabilityTheory.posterior_prod_id_comp`：posterior_prod_id_comp : (κ†μ 
×ₖ Kernel.id) ∘ₘ κ ∘ₘ μ = μ otimesₘ κ
· 使用引理 `MeasureTheory.Measure.comp_assoc`：comp_assoc {η : Kernel β γ} : η ∘ₘ (κ 
∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_comp_prod`：parallelComp_comp_prod 
[IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η] {κ' : Kernel X Y'} [IsS
FiniteKernel κ'] {η' : Kernel Y' Z'} …
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `ProbabilityTheory.Kernel.id_comp`：∀ {α : Type u_1} {β : Type u_2} {mα : 
MeasurableSpace α} {mβ : MeasurableSpace β} (κ : ProbabilityTheory.Kernel α β), 
  ProbabilityTheory.Ke…
· 使用定理 `ProbabilityTheory.Kernel.comp_id`：∀ {β : Type u_2} {γ : Type u_3} {mβ : 
MeasurableSpace β} {mγ : MeasurableSpace γ} (κ : ProbabilityTheory.Kernel β γ), 
  κ.comp ProbabilityTh…

--- 原说明 ---
The average risk of an estimator `κ` with respect to a prior `π` can be expresse
d as
an integral in the following way: `R_π(κ) = ((P†π × κ) ∘ P ∘ π)[(θ, y) ↦ ℓ θ y]`
.
-/
lemma avgRisk_eq_lintegral_posterior_prod
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π] :
    avgRisk ℓ P κ π = ∫⁻ θy, ℓ θy.1 θy.2 ∂(((P†π) ×ₖ κ) ∘ₘ (P ∘ₘ π)) := by
  rw [avgRisk, ← Measure.lintegral_compProd (f := fun θy ↦ ℓ θy.1 θy.2) (by fun_prop)]
  congr
  calc π ⊗ₘ (κ ∘ₖ P) = (Kernel.id ∥ₖ κ) ∘ₘ (π ⊗ₘ P) := Measure.parallelComp_comp_compProd.symm
  _ = (Kernel.id ∥ₖ κ) ∘ₘ ((P†π) ×ₖ Kernel.id) ∘ₘ P ∘ₘ π := by rw [posterior_prod_id_comp]
  _ = ((P†π) ×ₖ κ) ∘ₘ P ∘ₘ π := by
      rw [Measure.comp_assoc, Kernel.parallelComp_comp_prod, Kernel.id_comp, Kernel.comp_id]
/-
**ProbabilityTheory.avgRisk_eq_lintegral_lintegral_lintegral** 是 Mathlib 中的一个引理，
位于命名空间 `ProbabilityTheory`。
形式化陈述：avgRisk_eq_lintegral_lintegral_lintegral (hl : Measurable (Function.uncurr
y ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (
π : Measure Θ) [IsFiniteMeasure π] : avgRisk ℓ P κ π = ∫⁻ x, ∫⁻ y, ∫⁻ θ, ℓ θ y ∂
(P†π) x ∂κ x ∂(P ∘ₘ π)
参数：hl : Measurable (Function.uncurry ℓ)；P : Kernel Θ 𝓧；κ : Kernel 𝓧 𝓨；π : Measur
e Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.avgRisk_eq_lintegral_posterior_prod`：avgRisk_eq_linteg
ral_posterior_prod (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFi
niteKernel P] (κ : Kernel 𝓧 𝓨) [IsSFiniteKe…
· 使用定理 `MeasureTheory.Measure.lintegral_bind`：lintegral_bind {m : Measure α} {μ 
: α -> Measure β} {f : β -> Real>=0∞} (hμ : AEMeasurable μ m) (hf : AEMeasurable
 f (bind m μ)) : ∫⁻ x, f x…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `ProbabilityTheory.Kernel.measurable`：measurable (κ : Kernel α β) : Measu
rable κ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.Kernel.prod_apply`：prod_apply (κ : Kernel α β) [IsSFin
iteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] (a : α) : (κ ×ₖ η) a = (κ a).p
rod (η a)
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用定理 `MeasureTheory.lintegral_prod_symm'`：lintegral_prod_symm' [SFinite μ] (f 
: α × β -> Real>=0∞) (hf : Measurable f) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (
x, y) ∂μ ∂ν
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
-/
lemma avgRisk_eq_lintegral_lintegral_lintegral
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π] :
    avgRisk ℓ P κ π = ∫⁻ x, ∫⁻ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂κ x ∂(P ∘ₘ π) := by
  rw [avgRisk_eq_lintegral_posterior_prod hl, Measure.lintegral_bind (by fun_prop) (by fun_prop)]
  congr with x
  rw [Kernel.prod_apply, lintegral_prod_symm' _ (by fun_prop)]
/-
**ProbabilityTheory.lintegral_iInf_posterior_le_avgRisk** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：lintegral_iInf_posterior_le_avgRisk (hl : Measurable (Function.uncurry ℓ))
 (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (π : Me
asure Θ) [IsFiniteMeasure π] : ∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) <
= avgRisk ℓ P κ π
参数：hl : Measurable (Function.uncurry ℓ)；P : Kernel Θ 𝓧；κ : Kernel 𝓧 𝓨；π : Measur
e Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.avgRisk_eq_lintegral_lintegral_lintegral`：avgRisk_eq_l
integral_lintegral_lintegral (hl : Measurable (Function.uncurry ℓ)) (P : Kernel 
Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsSFin…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `MeasureTheory.iInf_le_lintegral`：iInf_le_lintegral [IsProbabilityMeasure
 μ] (f : α -> Real>=0∞) : ⨅ x, f x <= ∫⁻ x, f x ∂μ
· 使用定理 `ProbabilityTheory.IsMarkovKernel.is_probability_measure'`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabi
lityTheory.Kernel α β}   [ProbabilityTheory.Is…
-/
lemma lintegral_iInf_posterior_le_avgRisk
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (π : Measure Θ) [IsFiniteMeasure π] :
    ∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) ≤ avgRisk ℓ P κ π := by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl]
  gcongr with x
  exact iInf_le_lintegral _
/-
**ProbabilityTheory.lintegral_iInf_posterior_le_bayesRisk** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：lintegral_iInf_posterior_le_bayesRisk (hl : Measurable (Function.uncurry ℓ
)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] : ∫⁻ 
x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) <= bayesRisk ℓ P π
参数：hl : Measurable (Function.uncurry ℓ)；P : Kernel Θ 𝓧；π : Measure Θ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用引理 `ProbabilityTheory.lintegral_iInf_posterior_le_avgRisk`：lintegral_iInf_po
sterior_le_avgRisk (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFi
niteKernel P] (κ : Kernel 𝓧 𝓨) [IsMarkovKer…
-/
lemma lintegral_iInf_posterior_le_bayesRisk
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] :
    ∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) ≤ bayesRisk ℓ P π :=
  le_iInf₂ fun κ _ ↦ lintegral_iInf_posterior_le_avgRisk hl P κ π

end Posterior

/-- An estimator is a Bayes estimator for a prior `π` if it attains the Bayes risk for `π`. -/
/-
**ProbabilityTheory.IsBayesEstimator** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：IsBayesEstimator (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨
) (π : Measure Θ) : Prop
参数：ℓ : Θ -> 𝓨 -> Real>=0∞；P : Kernel Θ 𝓧；κ : Kernel 𝓧 𝓨；π : Measure Θ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An estimator is a Bayes estimator for a prior `π` if it attains the Bayes risk f
or `π`.
-/
def IsBayesEstimator (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) : Prop :=
  avgRisk ℓ P κ π = bayesRisk ℓ P π

variable [StandardBorelSpace Θ] [Nonempty Θ] {f : 𝓧 → 𝓨} [IsFiniteKernel P] [IsFiniteMeasure π]

/-- We say that a measurable function `f : 𝓧 → 𝓨` is an argmin estimator
with respect to the prior `π` if for `(P ∘ₘ π)`-almost every `x` it is of
the form `x ↦ argmin_y P†π(x)[θ ↦ ℓ θ y]`. -/
/-
**ProbabilityTheory.IsArgminEstimator** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：{Θ : Type u_1} →   {𝓧 : Type u_2} →     {mΘ : MeasurableSpace Θ} →       {
m𝓧 : MeasurableSpace 𝓧} →         [StandardBorelSpace Θ] →           [Nonempty Θ
] →             {𝓨 : Type u_4} →               [MeasurableSpace 𝓨] →            
     (Θ → 𝓨 → ENNReal) →                   (P : ProbabilityTheory.Kernel Θ 𝓧) → 
                    [ProbabilityTheory.IsFiniteKernel P] →                      
 (π : MeasureTheory.Measure Θ) → [MeasureTheory.IsFiniteMeasure π] → (𝓧 → 𝓨) → P
rop
参数：Θ → 𝓨 → ENNReal；P : ProbabilityTheory.Kernel Θ 𝓧；π : MeasureTheory.Measure Θ；
𝓧 → 𝓨。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a measurable function `f : 𝓧 → 𝓨` is an argmin estimator
with respect to the prior `π` if for `(P ∘ₘ π)`-almost every `x` it is of
the form `x ↦ argmin_y P†π(x)[θ ↦ ℓ θ y]`.
-/
structure IsArgminEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] (f : 𝓧 → 𝓨) : Prop where
  measurable : Measurable f
  property : ∀ᵐ x ∂(P ∘ₘ π), ∫⁻ θ, ℓ θ (f x) ∂(P†π) x = ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x

/-- Given an argmin estimator `f`, we can define a deterministic kernel. -/
protected noncomputable
/-
**ProbabilityTheory.IsArgminEstimator.kernel** 是 Mathlib 中的一个定义，位于命名空间 `Probabil
ityTheory.IsArgminEstimator`。
形式化陈述：{Θ : Type u_1} →   {𝓧 : Type u_2} →     {𝓨 : Type u_3} →       {mΘ : Measu
rableSpace Θ} →         {m𝓧 : MeasurableSpace 𝓧} →           {m𝓨 : MeasurableSpa
ce 𝓨} →             {ℓ : Θ → 𝓨 → ENNReal} →               {P : ProbabilityTheory
.Kernel Θ 𝓧} →                 {π : MeasureTheory.Measure Θ} →                  
 [inst : StandardBorelSpace Θ] →                     [inst_1 : Nonempty Θ] →    
                   {f : 𝓧 → 𝓨} →                         [inst_2 : ProbabilityTh
eory.IsFiniteKernel P] →                           [inst_3 : MeasureTheory.IsFin
iteMeasure π] →                             ProbabilityTheory.IsArgminEstimator 
ℓ P π f → ProbabilityTheory.Kernel 𝓧 𝓨
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsArgminEstimator.measurable`：∀ {Θ : Type u_1} {𝓧 : Ty
pe u_2} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧} [inst : StandardBorelS
pace Θ]   [inst_1 : Nonempty Θ] {𝓨 :…
-/
abbrev IsArgminEstimator.kernel (h : IsArgminEstimator ℓ P π f) : Kernel 𝓧 𝓨 :=
  Kernel.deterministic f h.measurable

/-- The risk of an argmin estimator is the risk lower bound
`∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂(P†π) x ∂(P ∘ₘ π)`. -/
/-
**ProbabilityTheory.IsArgminEstimator.avgRisk_eq_lintegral_iInf** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.IsArgminEstimator`。
形式化陈述：∀ {Θ : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {mΘ : MeasurableSpace Θ} {m
𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ENNReal} {P : Pro
babilityTheory.Kernel Θ 𝓧} {π : MeasureTheory.Measure Θ}   [inst : StandardBorel
Space Θ] [inst_1 : Nonempty Θ] {f : 𝓧 → 𝓨} [inst_2 : ProbabilityTheory.IsFiniteK
ernel P]   [inst_3 : MeasureTheory.IsFiniteMeasure π] (hf : ProbabilityTheory.Is
ArgminEstimator ℓ P π f),   Measurable (Function.uncurry ℓ) →     ProbabilityThe
ory.avgRisk ℓ P hf.kernel π =       ∫⁻ (x : 𝓧), ⨅ y, ∫⁻ (θ : Θ), ℓ θ y ∂(Probabi
lityTheory.posterior P π) x ∂π.bind ⇑P
参数：hf : ProbabilityTheory.IsArgminEstimator ℓ P π f；Function.uncurry ℓ；x : 𝓧；θ :
 Θ；ProbabilityTheory.posterior P π。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.avgRisk_eq_lintegral_lintegral_lintegral`：avgRisk_eq_l
integral_lintegral_lintegral (hl : Measurable (Function.uncurry ℓ)) (P : Kernel 
Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsSFin…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsArgminEstimator.measurable`：∀ {Θ : Type u_1} {𝓧 : Ty
pe u_2} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧} [inst : StandardBorelS
pace Θ]   [inst_1 : Nonempty Θ] {𝓨 :…
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.IsArgminEstimator.property`：∀ {Θ : Type u_1} {𝓧 : Type
 u_2} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧} [inst : StandardBorelSpa
ce Θ]   [inst_1 : Nonempty Θ] {𝓨 :…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ProbabilityTheory.Kernel.lintegral_deterministic'`：lintegral_determinist
ic' {f : β -> Real>=0∞} {g : α -> β} {a : α} (hg : Measurable g) (hf : Measurabl
e f) : ∫⁻ x, f x ∂deterministic g hg a …
· 使用定理 `Measurable.lintegral_prod_right`：Measurable.lintegral_prod_right [SFinit
e ν] {f : α -> β -> Real>=0∞} (hf : Measurable (uncurry f)) : Measurable fun x =
> ∫⁻ y, f x y ∂ν
· 使用定理 `ProbabilityTheory.IsSFiniteKernel.sFinite`：∀ {α : Type u_1} {β : Type u_
2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kern
el α β}   [ProbabilityTheory.Is…
· 使用定理 `ProbabilityTheory.instIsMarkovKernelPosterior`：∀ {Ω : Type u_1} {𝓧 : Typ
e u_2} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {κ : ProbabilityTheory.
Kernel Ω 𝓧}   {μ : MeasureTheory.Me…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1

--- 原说明 ---
The risk of an argmin estimator is the risk lower bound
`∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂(P†π) x ∂(P ∘ₘ π)`.
-/
lemma IsArgminEstimator.avgRisk_eq_lintegral_iInf (hf : IsArgminEstimator ℓ P π f)
    (hl : Measurable (Function.uncurry ℓ)) :
    avgRisk ℓ P hf.kernel π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂(P ∘ₘ π) := by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl]
  refine lintegral_congr_ae ?_
  filter_upwards [hf.property] with x hx
  rwa [Kernel.lintegral_deterministic' _ (by fun_prop)]

/-- An argmin estimator is a Bayes estimator: that is, it minimizes the Bayesian risk. -/
/-
**ProbabilityTheory.IsArgminEstimator.isBayesEstimator** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.IsArgminEstimator`。
形式化陈述：∀ {Θ : Type u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {mΘ : MeasurableSpace Θ} {m
𝓧 : MeasurableSpace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ENNReal} {P : Pro
babilityTheory.Kernel Θ 𝓧} {π : MeasureTheory.Measure Θ}   [inst : StandardBorel
Space Θ] [inst_1 : Nonempty Θ] {f : 𝓧 → 𝓨} [inst_2 : ProbabilityTheory.IsFiniteK
ernel P]   [inst_3 : MeasureTheory.IsFiniteMeasure π] (hf : ProbabilityTheory.Is
ArgminEstimator ℓ P π f),   Measurable (Function.uncurry ℓ) → ProbabilityTheory.
IsBayesEstimator ℓ P hf.kernel π
参数：hf : ProbabilityTheory.IsArgminEstimator ℓ P π f；Function.uncurry ℓ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsArgminEstimator.avgRisk_eq_lintegral_iInf`：∀ {Θ : Ty
pe u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableS
pace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ENN…
· 使用引理 `ProbabilityTheory.lintegral_iInf_posterior_le_bayesRisk`：lintegral_iInf_
posterior_le_bayesRisk (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [
IsFiniteKernel P] (π : Measure Θ) [IsFiniteMe…
· 使用引理 `ProbabilityTheory.bayesRisk_le_avgRisk`：bayesRisk_le_avgRisk (ℓ : Θ -> 𝓨
 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) [hκ : IsMarkovKe
rnel κ] : bayesRisk ℓ P π <=…
· 使用定理 `ProbabilityTheory.IsArgminEstimator.measurable`：∀ {Θ : Type u_1} {𝓧 : Ty
pe u_2} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧} [inst : StandardBorelS
pace Θ]   [inst_1 : Nonempty Θ] {𝓨 :…

--- 原说明 ---
An argmin estimator is a Bayes estimator: that is, it minimizes the Bayesian ris
k.
-/
lemma IsArgminEstimator.isBayesEstimator (hf : IsArgminEstimator ℓ P π f)
    (hl : Measurable (Function.uncurry ℓ)) :
    IsBayesEstimator ℓ P hf.kernel π := by
  refine le_antisymm ?_ (bayesRisk_le_avgRisk _ _ _ _)
  rw [hf.avgRisk_eq_lintegral_iInf hl]
  exact lintegral_iInf_posterior_le_bayesRisk hl _ _

/-- The estimation problem admits an argmin estimator with respect to the prior `π`.
That is, we can choose the argmin of the posterior expected loss in a measurable way. -/
/-
**ProbabilityTheory.HasArgminEstimator** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProbabilityT
heory`。
形式化陈述：{Θ : Type u_1} →   {𝓧 : Type u_2} →     {mΘ : MeasurableSpace Θ} →       {
m𝓧 : MeasurableSpace 𝓧} →         [StandardBorelSpace Θ] →           [Nonempty Θ
] →             {𝓨 : Type u_4} →               [MeasurableSpace 𝓨] →            
     (Θ → 𝓨 → ENNReal) →                   (P : ProbabilityTheory.Kernel Θ 𝓧) → 
                    [ProbabilityTheory.IsFiniteKernel P] →                      
 (π : MeasureTheory.Measure Θ) → [MeasureTheory.IsFiniteMeasure π] → Prop
参数：Θ → 𝓨 → ENNReal；P : ProbabilityTheory.Kernel Θ 𝓧；π : MeasureTheory.Measure Θ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The estimation problem admits an argmin estimator with respect to the prior `π`.
That is, we can choose the argmin of the posterior expected loss in a measurable
 way.
-/
structure HasArgminEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    Prop where
  exists_isArgminEstimator : ∃ f : 𝓧 → 𝓨, IsArgminEstimator ℓ P π f

namespace HasArgminEstimator

/-- An estimator for an estimation problem that for `(P ∘ₘ π)`-almost every `x` is of
the form `x ↦ argmin_y P†π(x)[θ ↦ ℓ θ y]`. -/
noncomputable
/-
**ProbabilityTheory.HasArgminEstimator.argminEstimator** 是 Mathlib 中的一个定义，位于命名空间
 `ProbabilityTheory.HasArgminEstimator`。
形式化陈述：argminEstimator (h : HasArgminEstimator ℓ P π) : 𝓧 -> 𝓨
参数：h : HasArgminEstimator ℓ P π。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasArgminEstimator.exists_isArgminEstimator`：∀ {Θ : Ty
pe u_1} {𝓧 : Type u_2} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧} [inst :
 StandardBorelSpace Θ]   [inst_1 : Nonempty Θ] {𝓨 :…
-/
def argminEstimator (h : HasArgminEstimator ℓ P π) : 𝓧 → 𝓨 :=
  h.exists_isArgminEstimator.choose
/-
**ProbabilityTheory.HasArgminEstimator.isArgminEstimator_argminEstimator** 是 Mat
hlib 中的一个引理，位于命名空间 `ProbabilityTheory.HasArgminEstimator`。
形式化陈述：isArgminEstimator_argminEstimator (h : HasArgminEstimator ℓ P π) : IsArgmi
nEstimator ℓ P π h.argminEstimator
参数：h : HasArgminEstimator ℓ P π。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `ProbabilityTheory.HasArgminEstimator.exists_isArgminEstimator`：∀ {Θ : Ty
pe u_1} {𝓧 : Type u_2} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧} [inst :
 StandardBorelSpace Θ]   [inst_1 : Nonempty Θ] {𝓨 :…
-/
lemma isArgminEstimator_argminEstimator (h : HasArgminEstimator ℓ P π) :
    IsArgminEstimator ℓ P π h.argminEstimator :=
  h.exists_isArgminEstimator.choose_spec

/-- If the estimation problem admits an argmin estimator, then the Bayesian risk
attains the risk lower bound `∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π)`. -/
/-
**ProbabilityTheory.HasArgminEstimator.bayesRisk_eq** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory.HasArgminEstimator`。
形式化陈述：bayesRisk_eq (hl : Measurable (Function.uncurry ℓ)) (h : HasArgminEstimato
r ℓ P π) : bayesRisk ℓ P π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π)
参数：hl : Measurable (Function.uncurry ℓ)；h : HasArgminEstimator ℓ P π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasArgminEstimator.isArgminEstimator_argminEstimator`：
isArgminEstimator_argminEstimator (h : HasArgminEstimator ℓ P π) : IsArgminEstim
ator ℓ P π h.argminEstimator
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IsArgminEstimator.isBayesEstimator`：∀ {Θ : Type u_1} {
𝓧 : Type u_2} {𝓨 : Type u_3} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}  
 {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ENN…
· 使用定理 `ProbabilityTheory.IsArgminEstimator.avgRisk_eq_lintegral_iInf`：∀ {Θ : Ty
pe u_1} {𝓧 : Type u_2} {𝓨 : Type u_3} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableS
pace 𝓧}   {m𝓨 : MeasurableSpace 𝓨} {ℓ : Θ → 𝓨 → ENN…

--- 原说明 ---
If the estimation problem admits an argmin estimator, then the Bayesian risk
attains the risk lower bound `∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π)`.
-/
lemma bayesRisk_eq (hl : Measurable (Function.uncurry ℓ)) (h : HasArgminEstimator ℓ P π) :
    bayesRisk ℓ P π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) := by
  rw [← h.isArgminEstimator_argminEstimator.isBayesEstimator hl,
    h.isArgminEstimator_argminEstimator.avgRisk_eq_lintegral_iInf hl]

end HasArgminEstimator

end ProbabilityTheory

