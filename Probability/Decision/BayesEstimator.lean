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
  {ℓ : Θ -> 𝓨 -> Real>=0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

section Posterior

variable [StandardBorelSpace Θ] [Nonempty Θ]

/--
lemma `avgRisk_eq_lintegral_posterior_prod` / 引理 `avgRisk_eq_lintegral_posterior_prod`

English:
lemma avgRisk_eq_lintegral_posterior_prod
  proof: by
  rw [avgRisk]; rw [← Measure.lintegral_compProd (f := fun θy => ℓ θy.1 θy.2) (by fun_prop)]
  congr
  calc π otimesₘ (κ ∘ₖ P) = (Kernel.id ∥ₖ κ) ∘ₘ (π otimesₘ P) := Measure.parallelComp_comp_compProd.symm
  _ = (Kernel.id ∥ₖ κ) ∘ₘ ((P†π) ×ₖ Kernel.id) ∘ₘ P ∘ₘ π := by rw [posterior_prod_id_comp]


中文:
引理 avgRisk_eq_lintegral_posterior_prod
  证明: by
  rw [avgRisk]; rw [← Measure.lintegral_compProd (f := fun θy => ℓ θy.1 θy.2) (by fun_prop)]
  congr
  calc π otimesₘ (κ ∘ₖ P) = (Kernel.id ∥ₖ κ) ∘ₘ (π otimesₘ P) := Measure.parallelComp_comp_compProd.symm
  _ = (Kernel.id ∥ₖ κ) ∘ₘ ((P†π) ×ₖ Kernel.id) ∘ₘ P ∘ₘ π := by rw [posterior_prod_id_comp]


Depends on / 依赖: Kernel, Kernel.comp_id, Kernel.id, Kernel.id_comp, Kernel.parallelComp_comp_prod, Measure, Measure.comp_assoc, Measure.lintegral_compProd, Measure.parallelComp_comp_compProd.symm, avgRisk, comp_assoc, comp_id, fun_prop, id_comp, lintegral_compProd, parallelComp_comp_compProd, parallelComp_comp_prod, posterior_prod_id_comp
-/
lemma avgRisk_eq_lintegral_posterior_prod
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π] :
    avgRisk ℓ P κ π = ∫⁻ θy, ℓ θy.1 θy.2 ∂(((P†π) ×ₖ κ) ∘ₘ (P ∘ₘ π)) := by
  rw [avgRisk]; rw [← Measure.lintegral_compProd (f := fun θy => ℓ θy.1 θy.2) (by fun_prop)]
  congr
  calc π otimesₘ (κ ∘ₖ P) = (Kernel.id ∥ₖ κ) ∘ₘ (π otimesₘ P) := Measure.parallelComp_comp_compProd.symm
  _ = (Kernel.id ∥ₖ κ) ∘ₘ ((P†π) ×ₖ Kernel.id) ∘ₘ P ∘ₘ π := by rw [posterior_prod_id_comp]
  _ = ((P†π) ×ₖ κ) ∘ₘ P ∘ₘ π := by
      rw [Measure.comp_assoc]; rw [Kernel.parallelComp_comp_prod]; rw [Kernel.id_comp]; rw [Kernel.comp_id]

/--
lemma `avgRisk_eq_lintegral_lintegral_lintegral` / 引理 `avgRisk_eq_lintegral_lintegral_lintegral`

English:
lemma avgRisk_eq_lintegral_lintegral_lintegral
  proof: by
  rw [avgRisk_eq_lintegral_posterior_prod hl]; rw [Measure.lintegral_bind (by fun_prop) (by fun_prop)]
  congr with x
  rw [Kernel.prod_apply]; rw [lintegral_prod_symm' _ (by fun_prop)]

中文:
引理 avgRisk_eq_lintegral_lintegral_lintegral
  证明: by
  rw [avgRisk_eq_lintegral_posterior_prod hl]; rw [Measure.lintegral_bind (by fun_prop) (by fun_prop)]
  congr with x
  rw [Kernel.prod_apply]; rw [lintegral_prod_symm' _ (by fun_prop)]

Depends on / 依赖: Kernel, Kernel.prod_apply, Measure, Measure.lintegral_bind, avgRisk_eq_lintegral_posterior_prod, fun_prop, lintegral_bind, lintegral_prod_symm, prod_apply
-/
lemma avgRisk_eq_lintegral_lintegral_lintegral
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π] :
    avgRisk ℓ P κ π = ∫⁻ x, ∫⁻ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂κ x ∂(P ∘ₘ π) := by
  rw [avgRisk_eq_lintegral_posterior_prod hl]; rw [Measure.lintegral_bind (by fun_prop) (by fun_prop)]
  congr with x
  rw [Kernel.prod_apply]; rw [lintegral_prod_symm' _ (by fun_prop)]

/--
lemma `lintegral_iInf_posterior_le_avgRisk` / 引理 `lintegral_iInf_posterior_le_avgRisk`

English:
lemma lintegral_iInf_posterior_le_avgRisk
  proof: by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl]
  gcongr with x
  exact iInf_le_lintegral _

中文:
引理 lintegral_iInf_posterior_le_avgRisk
  证明: by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl]
  gcongr with x
  exact iInf_le_lintegral _

Depends on / 依赖: avgRisk_eq_lintegral_lintegral_lintegral, iInf_le_lintegral
-/
lemma lintegral_iInf_posterior_le_avgRisk
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] (π : Measure Θ) [IsFiniteMeasure π] :
    ∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) <= avgRisk ℓ P κ π := by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl]
  gcongr with x
  exact iInf_le_lintegral _

/--
lemma `lintegral_iInf_posterior_le_bayesRisk` / 引理 `lintegral_iInf_posterior_le_bayesRisk`

English:
lemma lintegral_iInf_posterior_le_bayesRisk
  proof: le_iInf₂ fun κ _ => lintegral_iInf_posterior_le_avgRisk hl P κ π

中文:
引理 lintegral_iInf_posterior_le_bayesRisk
  证明: le_iInf₂ fun κ _ => lintegral_iInf_posterior_le_avgRisk hl P κ π

Depends on / 依赖: lintegral_iInf_posterior_le_avgRisk
-/
lemma lintegral_iInf_posterior_le_bayesRisk
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] :
    ∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) <= bayesRisk ℓ P π :=
  le_iInf₂ fun κ _ => lintegral_iInf_posterior_le_avgRisk hl P κ π

end Posterior

/--
Definition of `IsBayesEstimator` / `IsBayesEstimator` 的定义

English:
definition IsBayesEstimator
  signature: (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ)
  body: avgRisk ℓ P κ π = bayesRisk ℓ P π

中文:
定义 IsBayesEstimator
  签名: (ℓ : Θ -> 𝓨 -> 实数>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ)
  定义体: avgRisk ℓ P κ π = bayesRisk ℓ P π

Depends on / 依赖: avgRisk, bayesRisk
-/
def IsBayesEstimator (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) : Prop :=
  avgRisk ℓ P κ π = bayesRisk ℓ P π

variable [StandardBorelSpace Θ] [Nonempty Θ] {f : 𝓧 -> 𝓨} [IsFiniteKernel P] [IsFiniteMeasure π]

/--
Definition of `IsArgminEstimator` / `IsArgminEstimator` 的定义

English:
structure IsArgminEstimator
  parameters: {𝓨 : Type*} [MeasurableSpace 𝓨]
  axioms and operations (2):
    - measurable : Measurable f
    - property : forallᵐ x ∂(P ∘ₘ π), ∫⁻ θ, ℓ θ (f x) ∂(P†π) x = ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x

中文:
结构 IsArgminEstimator
  参数: {𝓨 : 类型} [MeasurableSpace 𝓨]
  公理与运算 (2 个):
    - measurable : Measurable f
    - property : 对任意ᵐ x ∂(P ∘ₘ π), ∫⁻ θ, ℓ θ (f x) ∂(P†π) x = ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x
-/
structure IsArgminEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] (f : 𝓧 -> 𝓨) : Prop where
  measurable : Measurable f
  property : forallᵐ x ∂(P ∘ₘ π), ∫⁻ θ, ℓ θ (f x) ∂(P†π) x = ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x

/-- Given an argmin estimator `f`, we can define a deterministic kernel. -/
protected noncomputable
/--
Definition of `IsArgminEstimator.kernel` / `IsArgminEstimator.kernel` 的定义

English:
abbreviation IsArgminEstimator.kernel
  signature: (h : IsArgminEstimator ℓ P π f)
  body: Kernel.deterministic f h.measurable

中文:
缩写 IsArgminEstimator.kernel
  签名: (h : IsArgminEstimator ℓ P π f)
  定义体: Kernel.deterministic f h.measurable

Depends on / 依赖: Kernel, Kernel.deterministic, deterministic, h.measurable, measurable
-/
abbrev IsArgminEstimator.kernel (h : IsArgminEstimator ℓ P π f) : Kernel 𝓧 𝓨 :=
  Kernel.deterministic f h.measurable

/--
lemma `IsArgminEstimator.avgRisk_eq_lintegral_iInf` / 引理 `IsArgminEstimator.avgRisk_eq_lintegral_iInf`

English:
lemma IsArgminEstimator.avgRisk_eq_lintegral_iInf
  statement: (hf : IsArgminEstimator ℓ P π f)
  proof: by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl]
  refine lintegral_congr_ae ?_
  filter_upwards [hf.property] with x hx
  rwa [Kernel.lintegral_deterministic' _ (by fun_prop)]

中文:
引理 IsArgminEstimator.avgRisk_eq_lintegral_iInf
  结论: (hf : IsArgminEstimator ℓ P π f)
  证明: by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl]
  refine lintegral_congr_ae ?_
  filter_upwards [hf.property] with x hx
  rwa [Kernel.lintegral_deterministic' _ (by fun_prop)]

Depends on / 依赖: Kernel, Kernel.lintegral_deterministic, avgRisk_eq_lintegral_lintegral_lintegral, filter_upwards, fun_prop, hf.property, lintegral_congr_ae, lintegral_deterministic, property
-/
lemma IsArgminEstimator.avgRisk_eq_lintegral_iInf (hf : IsArgminEstimator ℓ P π f)
    (hl : Measurable (Function.uncurry ℓ)) :
    avgRisk ℓ P hf.kernel π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂(P ∘ₘ π) := by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl]
  refine lintegral_congr_ae ?_
  filter_upwards [hf.property] with x hx
  rwa [Kernel.lintegral_deterministic' _ (by fun_prop)]

/--
lemma `IsArgminEstimator.isBayesEstimator` / 引理 `IsArgminEstimator.isBayesEstimator`

English:
lemma IsArgminEstimator.isBayesEstimator
  statement: (hf : IsArgminEstimator ℓ P π f)
  proof: by
  refine le_antisymm ?_ (bayesRisk_le_avgRisk _ _ _ _)
  rw [hf.avgRisk_eq_lintegral_iInf hl]
  exact lintegral_iInf_posterior_le_bayesRisk hl _ _

中文:
引理 IsArgminEstimator.isBayesEstimator
  结论: (hf : IsArgminEstimator ℓ P π f)
  证明: by
  refine le_antisymm ?_ (bayesRisk_le_avgRisk _ _ _ _)
  rw [hf.avgRisk_eq_lintegral_iInf hl]
  exact lintegral_iInf_posterior_le_bayesRisk hl _ _

Depends on / 依赖: avgRisk_eq_lintegral_iInf, bayesRisk_le_avgRisk, hf.avgRisk_eq_lintegral_iInf, le_antisymm, lintegral_iInf_posterior_le_bayesRisk
-/
lemma IsArgminEstimator.isBayesEstimator (hf : IsArgminEstimator ℓ P π f)
    (hl : Measurable (Function.uncurry ℓ)) :
    IsBayesEstimator ℓ P hf.kernel π := by
  refine le_antisymm ?_ (bayesRisk_le_avgRisk _ _ _ _)
  rw [hf.avgRisk_eq_lintegral_iInf hl]
  exact lintegral_iInf_posterior_le_bayesRisk hl _ _

/--
Definition of `HasArgminEstimator` / `HasArgminEstimator` 的定义

English:
structure HasArgminEstimator
  parameters: {𝓨 : Type*} [MeasurableSpace 𝓨]
  axioms and operations (1):
    - exists_isArgminEstimator : exists f : 𝓧 -> 𝓨, IsArgminEstimator ℓ P π f

中文:
结构 HasArgminEstimator
  参数: {𝓨 : 类型} [MeasurableSpace 𝓨]
  公理与运算 (1 个):
    - exists_isArgminEstimator : 存在 f : 𝓧 -> 𝓨, IsArgminEstimator ℓ P π f
-/
structure HasArgminEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ -> 𝓨 -> Real>=0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    Prop where
  exists_isArgminEstimator : exists f : 𝓧 -> 𝓨, IsArgminEstimator ℓ P π f

namespace HasArgminEstimator

/-- An estimator for an estimation problem that for `(P ∘ₘ π)`-almost every `x` is of
the form `x ↦ argmin_y P†π(x)[θ ↦ ℓ θ y]`. -/
noncomputable
/--
Definition of `argminEstimator` / `argminEstimator` 的定义

English:
definition argminEstimator
  signature: (h : HasArgminEstimator ℓ P π)
  body: h.exists_isArgminEstimator.choose

中文:
定义 argminEstimator
  签名: (h : HasArgminEstimator ℓ P π)
  定义体: h.exists_isArgminEstimator.choose

Depends on / 依赖: exists_isArgminEstimator, h.exists_isArgminEstimator.choose
-/
def argminEstimator (h : HasArgminEstimator ℓ P π) : 𝓧 -> 𝓨 :=
  h.exists_isArgminEstimator.choose

/--
lemma `isArgminEstimator_argminEstimator` / 引理 `isArgminEstimator_argminEstimator`

English:
lemma isArgminEstimator_argminEstimator
  given: (h : HasArgminEstimator ℓ P π)
  proof: h.exists_isArgminEstimator.choose_spec

中文:
引理 isArgminEstimator_argminEstimator
  条件: (h : HasArgminEstimator ℓ P π)
  证明: h.exists_isArgminEstimator.choose_spec

Depends on / 依赖: choose_spec, exists_isArgminEstimator, h.exists_isArgminEstimator.choose_spec
-/
lemma isArgminEstimator_argminEstimator (h : HasArgminEstimator ℓ P π) :
    IsArgminEstimator ℓ P π h.argminEstimator :=
  h.exists_isArgminEstimator.choose_spec

/--
lemma `bayesRisk_eq` / 引理 `bayesRisk_eq`

English:
lemma bayesRisk_eq
  given: (hl : Measurable (Function.uncurry ℓ)) (h : HasArgminEstimator ℓ P π)
  proof: by
  rw [← h.isArgminEstimator_argminEstimator.isBayesEstimator hl]; rw [h.isArgminEstimator_argminEstimator.avgRisk_eq_lintegral_iInf hl]

中文:
引理 bayesRisk_eq
  条件: (hl : Measurable (Function.uncurry ℓ)) (h : HasArgminEstimator ℓ P π)
  证明: by
  rw [← h.isArgminEstimator_argminEstimator.isBayesEstimator hl]; rw [h.isArgminEstimator_argminEstimator.avgRisk_eq_lintegral_iInf hl]

Depends on / 依赖: avgRisk_eq_lintegral_iInf, h.isArgminEstimator_argminEstimator.avgRisk_eq_lintegral_iInf, h.isArgminEstimator_argminEstimator.isBayesEstimator, isArgminEstimator_argminEstimator, isBayesEstimator
-/
lemma bayesRisk_eq (hl : Measurable (Function.uncurry ℓ)) (h : HasArgminEstimator ℓ P π) :
    bayesRisk ℓ P π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) := by
  rw [← h.isArgminEstimator_argminEstimator.isBayesEstimator hl]; rw [h.isArgminEstimator_argminEstimator.avgRisk_eq_lintegral_iInf hl]

end HasArgminEstimator

end ProbabilityTheory
