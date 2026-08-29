/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Decision.Risk.Defs

import Mathlib.Probability.Decision.Risk.Basic

/-!
# Risk in countable spaces

In countable spaces, we can write integrals as sums, hence we can write the average or Bayes risk
with sums instead of integrals.

-/

public section

open MeasureTheory Function
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ Θ' 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {mΘ' : MeasurableSpace Θ'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ -> 𝓨 -> Real>=0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

/--
lemma `avgRisk_countable` / 引理 `avgRisk_countable`

English:
lemma avgRisk_countable
  given: [Countable Θ] [MeasurableSingletonClass Θ]
  proof: by
  simp [avgRisk, lintegral_countable']

中文:
引理 avgRisk_countable
  条件: [可数 Θ] [MeasurableSingleton类 Θ]
  证明: by
  simp [avgRisk, lintegral_countable']

Depends on / 依赖: avgRisk, lintegral_countable
-/
lemma avgRisk_countable [Countable Θ] [MeasurableSingletonClass Θ] :
    avgRisk ℓ P κ π = ∑' θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [avgRisk, lintegral_countable']

/--
lemma `avgRisk_fintype` / 引理 `avgRisk_fintype`

English:
lemma avgRisk_fintype
  given: [Fintype Θ] [MeasurableSingletonClass Θ]
  proof: by
  simp [avgRisk, lintegral_fintype]

中文:
引理 avgRisk_fintype
  条件: [有限类型 Θ] [MeasurableSingleton类 Θ]
  证明: by
  simp [avgRisk, lintegral_fintype]

Depends on / 依赖: avgRisk, lintegral_fintype
-/
lemma avgRisk_fintype [Fintype Θ] [MeasurableSingletonClass Θ] :
    avgRisk ℓ P κ π = ∑ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [avgRisk, lintegral_fintype]

/--
lemma `avgRisk_countable'` / 引理 `avgRisk_countable'`

English:
lemma avgRisk_countable'
  given: [Countable 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ)
  proof: by
  simp only [avgRisk, lintegral_countable']
  rw [lintegral_tsum]
  · rfl
  · refine fun y => Measurable.aemeasurable ?_
    exact Measurable.mul (by fun_prop) ((κ ∘ₖ P).measurable_coe (measurableSet_singleton y))

中文:
引理 avgRisk_countable'
  条件: [可数 𝓨] [MeasurableSingleton类 𝓨] (hℓ : 可测 ℓ)
  证明: by
  simp only [avgRisk, lintegral_countable']
  rw [lintegral_tsum]
  · rfl
  · refine fun y => Measurable.aemeasurable ?_
    exact Measurable.mul (by fun_prop) ((κ ∘ₖ P).measurable_coe (measurableSet_singleton y))

Depends on / 依赖: Measurable, Measurable.aemeasurable, Measurable.mul, aemeasurable, avgRisk, fun_prop, lintegral_countable, lintegral_tsum, measurableSet_singleton, measurable_coe
-/
lemma avgRisk_countable' [Countable 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ) :
    avgRisk ℓ P κ π = ∑' y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  simp only [avgRisk, lintegral_countable']
  rw [lintegral_tsum]
  · rfl
  · refine fun y => Measurable.aemeasurable ?_
    exact Measurable.mul (by fun_prop) ((κ ∘ₖ P).measurable_coe (measurableSet_singleton y))

/--
lemma `avgRisk_fintype'` / 引理 `avgRisk_fintype'`

English:
lemma avgRisk_fintype'
  given: [Fintype 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ)
  proof: by
  rw [avgRisk_countable' hℓ]; rw [tsum_fintype]

中文:
引理 avgRisk_fintype'
  条件: [有限类型 𝓨] [MeasurableSingleton类 𝓨] (hℓ : 可测 ℓ)
  证明: by
  rw [avgRisk_countable' hℓ]; rw [tsum_fintype]

Depends on / 依赖: avgRisk_countable, tsum_fintype
-/
lemma avgRisk_fintype' [Fintype 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ) :
    avgRisk ℓ P κ π = ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  rw [avgRisk_countable' hℓ]; rw [tsum_fintype]

/--
lemma `bayesRisk_countable` / 引理 `bayesRisk_countable`

English:
lemma bayesRisk_countable
  given: [Countable Θ] [MeasurableSingletonClass Θ]
  proof: by
  simp [bayesRisk, avgRisk_countable]

中文:
引理 bayesRisk_countable
  条件: [可数 Θ] [MeasurableSingleton类 Θ]
  证明: by
  simp [bayesRisk, avgRisk_countable]

Depends on / 依赖: avgRisk_countable, bayesRisk
-/
lemma bayesRisk_countable [Countable Θ] [MeasurableSingletonClass Θ] :
    bayesRisk ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑' θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [bayesRisk, avgRisk_countable]

/--
lemma `bayesRisk_fintype` / 引理 `bayesRisk_fintype`

English:
lemma bayesRisk_fintype
  given: [Fintype Θ] [MeasurableSingletonClass Θ]
  proof: by
  simp [bayesRisk, avgRisk_fintype]

中文:
引理 bayesRisk_fintype
  条件: [有限类型 Θ] [MeasurableSingleton类 Θ]
  证明: by
  simp [bayesRisk, avgRisk_fintype]

Depends on / 依赖: avgRisk_fintype, bayesRisk
-/
lemma bayesRisk_fintype [Fintype Θ] [MeasurableSingletonClass Θ] :
    bayesRisk ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [bayesRisk, avgRisk_fintype]

/--
lemma `bayesRisk_countable'` / 引理 `bayesRisk_countable'`

English:
lemma bayesRisk_countable'
  given: [Countable 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ)
  proof: by
  simp [bayesRisk, avgRisk_countable' hℓ]

中文:
引理 bayesRisk_countable'
  条件: [可数 𝓨] [MeasurableSingleton类 𝓨] (hℓ : 可测 ℓ)
  证明: by
  simp [bayesRisk, avgRisk_countable' hℓ]

Depends on / 依赖: avgRisk_countable, bayesRisk
-/
lemma bayesRisk_countable' [Countable 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ) :
    bayesRisk ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑' y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  simp [bayesRisk, avgRisk_countable' hℓ]

/--
lemma `bayesRisk_fintype'` / 引理 `bayesRisk_fintype'`

English:
lemma bayesRisk_fintype'
  given: [Fintype 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ)
  proof: by
  simp [bayesRisk, avgRisk_fintype' hℓ]

中文:
引理 bayesRisk_fintype'
  条件: [有限类型 𝓨] [MeasurableSingleton类 𝓨] (hℓ : 可测 ℓ)
  证明: by
  simp [bayesRisk, avgRisk_fintype' hℓ]

Depends on / 依赖: avgRisk_fintype, bayesRisk
-/
lemma bayesRisk_fintype' [Fintype 𝓨] [MeasurableSingletonClass 𝓨] (hℓ : Measurable ℓ) :
    bayesRisk ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  simp [bayesRisk, avgRisk_fintype' hℓ]

section Const

/--
lemma `avgRisk_const_of_countable` / 引理 `avgRisk_const_of_countable`

English:
lemma avgRisk_const_of_countable
  statement: [Countable 𝓨] [MeasurableSingletonClass 𝓨]
  proof: by
  simp [avgRisk_countable' hℓ]

中文:
引理 avgRisk_const_of_countable
  结论: [可数 𝓨] [MeasurableSingleton类 𝓨]
  证明: by
  simp [avgRisk_countable' hℓ]

Depends on / 依赖: avgRisk_countable
-/
lemma avgRisk_const_of_countable [Countable 𝓨] [MeasurableSingletonClass 𝓨]
    (hℓ : Measurable ℓ) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∑' y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ μ) {y} ∂π := by
  simp [avgRisk_countable' hℓ]

/--
lemma `avgRisk_const_of_fintype` / 引理 `avgRisk_const_of_fintype`

English:
lemma avgRisk_const_of_fintype
  statement: [Fintype 𝓨] [MeasurableSingletonClass 𝓨]
  proof: by
  simp [avgRisk_fintype' hℓ]

中文:
引理 avgRisk_const_of_fintype
  结论: [有限类型 𝓨] [MeasurableSingleton类 𝓨]
  证明: by
  simp [avgRisk_fintype' hℓ]

Depends on / 依赖: avgRisk_fintype
-/
lemma avgRisk_const_of_fintype [Fintype 𝓨] [MeasurableSingletonClass 𝓨]
    (hℓ : Measurable ℓ) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ μ) {y} ∂π := by
  simp [avgRisk_fintype' hℓ]

end Const

end ProbabilityTheory
