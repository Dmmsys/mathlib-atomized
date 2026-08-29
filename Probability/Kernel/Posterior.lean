/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Deterministic

/-!

# Posterior kernel

For `μ : Measure Ω` (called prior measure), seen as a measure on a parameter, and a kernel
`κ : Kernel Ω 𝓧` that gives the conditional distribution of "data" in `𝓧` given the prior parameter,
we can get the distribution of the data with `κ ∘ₘ μ`, and the joint distribution of parameter and
data with `μ ⊗ₘ κ : Measure (Ω × 𝓧)`.

The posterior distribution of the parameter given the data is a Markov kernel `κ†μ : Kernel 𝓧 Ω`
such that `(κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap`. That is, the joint distribution of parameter
and data can be recovered from the distribution of the data and the posterior.

## Main definitions

* `posterior κ μ`: posterior of a kernel `κ` for a prior measure `μ`.

## Main statements

* `compProd_posterior_eq_map_swap`: the main property of the posterior,
  `(κ ∘ₘ μ) ⊗ₘ κ†μ = (μ ⊗ₘ κ).map Prod.swap`.
* `ae_eq_posterior_of_compProd_eq`
* `posterior_comp_self`: `κ†μ ∘ₘ κ ∘ₘ μ = μ`
* `posterior_posterior`: `(κ†μ)†(κ ∘ₘ μ) =ᵐ[μ] κ`
* `posterior_comp`: `(η ∘ₖ κ)†μ =ᵐ[η ∘ₘ κ ∘ₘ μ] κ†μ ∘ₖ η†(κ ∘ₘ μ)`

* `posterior_eq_withDensity`: If `κ ω ≪ κ ∘ₘ μ` for `μ`-almost every `ω`,
  then for `κ ∘ₘ μ`-almost every `x`,
  `κ†μ x = μ.withDensity (fun ω ↦ κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x)`.
  The condition is true for countable `Ω`: see `absolutelyContinuous_comp_of_countable`.

## Notation

`κ†μ` denotes the posterior of `κ` with respect to `μ`, `posterior κ μ`.
`†` can be typed as `\dag` or `\dagger`.

This notation emphasizes that the posterior is a kind of inverse of `κ`, which we would want to
denote `κ†`, but we have to also specify the measure `μ`.

-/

@[expose] public section

open scoped ENNReal

open MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}
    {κ : Kernel Ω 𝓧} {μ : Measure Ω} [IsFiniteMeasure μ] [IsFiniteKernel κ]

variable [StandardBorelSpace Ω] [Nonempty Ω]

/-- Posterior of the kernel `κ` with respect to the measure `μ`. -/
noncomputable
/--
Definition of `posterior` / `posterior` 的定义

English:
definition posterior
  signature: (κ : Kernel Ω 𝓧) (μ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteKernel κ]
  body: ((μ otimesₘ κ).map Prod.swap).condKernel

中文:
定义 posterior
  签名: (κ : 核 Ω 𝓧) (μ : 测度 Ω) [是有限测度 μ] [是FiniteKernel κ]
  定义体: ((μ otimesₘ κ).map Prod.swap).condKernel

Depends on / 依赖: Prod.swap, condKernel
-/
def posterior (κ : Kernel Ω 𝓧) (μ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    Kernel 𝓧 Ω :=
  ((μ otimesₘ κ).map Prod.swap).condKernel

/-- Posterior of the kernel `κ` with respect to the measure `μ`. -/
scoped[ProbabilityTheory] infix:arg "†" => ProbabilityTheory.posterior

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMarkovKernel κ†μ
  body: by rw [posterior]; infer_instance

中文:
实例 :
  签名: 是MarkovKernel κ†μ
  定义体: by rw [posterior]; infer_instance

Depends on / 依赖: infer_instance, posterior
-/
instance : IsMarkovKernel κ†μ := by rw [posterior]; infer_instance

/--
lemma `compProd_posterior_eq_map_swap` / 引理 `compProd_posterior_eq_map_swap`

English:
lemma compProd_posterior_eq_map_swap
  statement: (κ ∘ₘ μ) otimesₘ κ†μ = (μ otimesₘ κ).map Prod.swap
  proof: by
  simpa using! ((μ otimesₘ κ).map Prod.swap).disintegrate ((μ otimesₘ κ).map Prod.swap).condKernel

中文:
引理 compProd_posterior_eq_map_swap
  结论: (κ ∘ₘ μ) otimesₘ κ†μ = (μ otimesₘ κ).map 积类型.swap
  证明: by
  simpa using! ((μ otimesₘ κ).map Prod.swap).disintegrate ((μ otimesₘ κ).map Prod.swap).condKernel

Depends on / 依赖: Prod.swap, condKernel, disintegrate
-/
lemma compProd_posterior_eq_map_swap : (κ ∘ₘ μ) otimesₘ κ†μ = (μ otimesₘ κ).map Prod.swap := by
  simpa using! ((μ otimesₘ κ).map Prod.swap).disintegrate ((μ otimesₘ κ).map Prod.swap).condKernel

/--
lemma `compProd_posterior_eq_swap_comp` / 引理 `compProd_posterior_eq_swap_comp`

English:
lemma compProd_posterior_eq_swap_comp
  statement: (κ ∘ₘ μ) otimesₘ κ†μ = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ
  proof: by
  rw [compProd_posterior_eq_map_swap]; rw [Measure.swap_comp]

中文:
引理 compProd_posterior_eq_swap_comp
  结论: (κ ∘ₘ μ) otimesₘ κ†μ = 核.swap Ω 𝓧 ∘ₘ μ otimesₘ κ
  证明: by
  rw [compProd_posterior_eq_map_swap]; rw [Measure.swap_comp]

Depends on / 依赖: Measure, Measure.swap_comp, compProd_posterior_eq_map_swap, swap_comp
-/
lemma compProd_posterior_eq_swap_comp : (κ ∘ₘ μ) otimesₘ κ†μ = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ := by
  rw [compProd_posterior_eq_map_swap]; rw [Measure.swap_comp]

/--
lemma `swap_compProd_posterior` / 引理 `swap_compProd_posterior`

English:
lemma swap_compProd_posterior
  statement: Kernel.swap 𝓧 Ω ∘ₘ (κ ∘ₘ μ) otimesₘ κ†μ = μ otimesₘ κ
  proof: by
  rw [compProd_posterior_eq_swap_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_swap]; rw [Measure.id_comp]

中文:
引理 swap_compProd_posterior
  结论: 核.swap 𝓧 Ω ∘ₘ (κ ∘ₘ μ) otimesₘ κ†μ = μ otimesₘ κ
  证明: by
  rw [compProd_posterior_eq_swap_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_swap]; rw [Measure.id_comp]

Depends on / 依赖: Kernel, Kernel.swap_swap, Measure, Measure.comp_assoc, Measure.id_comp, compProd_posterior_eq_swap_comp, comp_assoc, id_comp, swap_swap
-/
lemma swap_compProd_posterior : Kernel.swap 𝓧 Ω ∘ₘ (κ ∘ₘ μ) otimesₘ κ†μ = μ otimesₘ κ := by
  rw [compProd_posterior_eq_swap_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_swap]; rw [Measure.id_comp]

/--
lemma `parallelProd_posterior_comp_copy_comp` / 引理 `parallelProd_posterior_comp_copy_comp`

English:
lemma parallelProd_posterior_comp_copy_comp
  proof: by
  calc (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ
  _ = (κ ∘ₘ μ) otimesₘ κ†μ := by rw [← Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = Kernel.swap _ _ ∘ₘ (μ otimesₘ κ) := by rw [compProd_posterior_eq_swap_comp]
  _ = Kernel.swap _ _ ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.comp_assoc]; rw [Kernel.swap_parallelComp]; rw [Measure.comp_assoc]; rw [Kernel.comp_assoc]; rw [Kernel.swap_copy]; rw [Measure.comp_assoc]

中文:
引理 parallelProd_posterior_comp_copy_comp
  证明: by
  calc (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ
  _ = (κ ∘ₘ μ) otimesₘ κ†μ := by rw [← Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = Kernel.swap _ _ ∘ₘ (μ otimesₘ κ) := by rw [compProd_posterior_eq_swap_comp]
  _ = Kernel.swap _ _ ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.comp_assoc]; rw [Kernel.swap_parallelComp]; rw [Measure.comp_assoc]; rw [Kernel.comp_assoc]; rw [Kernel.swap_copy]; rw [Measure.comp_assoc]

Depends on / 依赖: Kernel, Kernel.comp_assoc, Kernel.copy, Kernel.id, Kernel.swap, Kernel.swap_parallelComp, Measure, Measure.compProd_eq_parallelComp_comp_copy_comp, Measure.comp_assoc, compProd_eq_parallelComp_comp_copy_comp, compProd_posterior_eq_swap_comp, comp_assoc, swap_parallelComp
-/
lemma parallelProd_posterior_comp_copy_comp :
    (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ
      = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
  calc (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ
  _ = (κ ∘ₘ μ) otimesₘ κ†μ := by rw [← Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = Kernel.swap _ _ ∘ₘ (μ otimesₘ κ) := by rw [compProd_posterior_eq_swap_comp]
  _ = Kernel.swap _ _ ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.compProd_eq_parallelComp_comp_copy_comp]
  _ = (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.comp_assoc]; rw [Kernel.swap_parallelComp]; rw [Measure.comp_assoc]; rw [Kernel.comp_assoc]; rw [Kernel.swap_copy]; rw [Measure.comp_assoc]

/--
lemma `posterior_prod_id_comp` / 引理 `posterior_prod_id_comp`

English:
lemma posterior_prod_id_comp
  statement: (κ†μ ×ₖ Kernel.id) ∘ₘ κ ∘ₘ μ = μ otimesₘ κ
  proof: by
  rw [← Kernel.swap_prod]; rw [← Measure.comp_assoc]; rw [← Measure.compProd_eq_comp_prod]; rw [compProd_posterior_eq_swap_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_swap]; rw [Measure.id_comp]

中文:
引理 posterior_prod_id_comp
  结论: (κ†μ ×ₖ 核.id) ∘ₘ κ ∘ₘ μ = μ otimesₘ κ
  证明: by
  rw [← Kernel.swap_prod]; rw [← Measure.comp_assoc]; rw [← Measure.compProd_eq_comp_prod]; rw [compProd_posterior_eq_swap_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_swap]; rw [Measure.id_comp]

Depends on / 依赖: Kernel, Kernel.swap_prod, Kernel.swap_swap, Measure, Measure.compProd_eq_comp_prod, Measure.comp_assoc, Measure.id_comp, compProd_eq_comp_prod, compProd_posterior_eq_swap_comp, comp_assoc, id_comp, swap_prod, swap_swap
-/
lemma posterior_prod_id_comp : (κ†μ ×ₖ Kernel.id) ∘ₘ κ ∘ₘ μ = μ otimesₘ κ := by
  rw [← Kernel.swap_prod]; rw [← Measure.comp_assoc]; rw [← Measure.compProd_eq_comp_prod]; rw [compProd_posterior_eq_swap_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_swap]; rw [Measure.id_comp]

/--
lemma `ae_eq_posterior_of_compProd_eq` / 引理 `ae_eq_posterior_of_compProd_eq`

English:
lemma ae_eq_posterior_of_compProd_eq
  statement: {η : Kernel 𝓧 Ω} [IsFiniteKernel η]
  proof: (Kernel.ae_eq_of_compProd_eq (compProd_posterior_eq_map_swap.trans h.symm)).symm

中文:
引理 ae_eq_posterior_of_compProd_eq
  结论: {η : 核 𝓧 Ω} [是FiniteKernel η]
  证明: (Kernel.ae_eq_of_compProd_eq (compProd_posterior_eq_map_swap.trans h.symm)).symm

Depends on / 依赖: Kernel, Kernel.ae_eq_of_compProd_eq, ae_eq_of_compProd_eq, compProd_posterior_eq_map_swap, compProd_posterior_eq_map_swap.trans, h.symm
-/
lemma ae_eq_posterior_of_compProd_eq {η : Kernel 𝓧 Ω} [IsFiniteKernel η]
    (h : (κ ∘ₘ μ) otimesₘ η = (μ otimesₘ κ).map Prod.swap) :
    η =ᵐ[κ ∘ₘ μ] κ†μ :=
  (Kernel.ae_eq_of_compProd_eq (compProd_posterior_eq_map_swap.trans h.symm)).symm

/--
lemma `ae_eq_posterior_of_compProd_eq_swap_comp` / 引理 `ae_eq_posterior_of_compProd_eq_swap_comp`

English:
lemma ae_eq_posterior_of_compProd_eq_swap_comp
  statement: (η : Kernel 𝓧 Ω) [IsFiniteKernel η]
  proof: ae_eq_posterior_of_compProd_eq by rw [h, Measure.swap_comp]

@[simp]

中文:
引理 ae_eq_posterior_of_compProd_eq_swap_comp
  结论: (η : 核 𝓧 Ω) [是FiniteKernel η]
  证明: ae_eq_posterior_of_compProd_eq by rw [h, Measure.swap_comp]

@[simp]

Depends on / 依赖: Measure, Measure.swap_comp, ae_eq_posterior_of_compProd_eq, swap_comp
-/
lemma ae_eq_posterior_of_compProd_eq_swap_comp (η : Kernel 𝓧 Ω) [IsFiniteKernel η]
    (h : ((κ ∘ₘ μ) otimesₘ η) = Kernel.swap Ω 𝓧 ∘ₘ μ otimesₘ κ) :
    η =ᵐ[κ ∘ₘ μ] κ†μ :=
ae_eq_posterior_of_compProd_eq by rw [h, Measure.swap_comp]

@[simp]
/--
lemma `posterior_comp_self` / 引理 `posterior_comp_self`

English:
lemma posterior_comp_self
  given: [IsMarkovKernel κ]
  statement: κ†μ ∘ₘ κ ∘ₘ μ = μ
  proof: by
  rw [← Measure.snd_compProd]; rw [compProd_posterior_eq_map_swap]; rw [Measure.snd_map_swap]; rw [Measure.fst_compProd]

中文:
引理 posterior_comp_self
  条件: [是MarkovKernel κ]
  结论: κ†μ ∘ₘ κ ∘ₘ μ = μ
  证明: by
  rw [← Measure.snd_compProd]; rw [compProd_posterior_eq_map_swap]; rw [Measure.snd_map_swap]; rw [Measure.fst_compProd]

Depends on / 依赖: Measure, Measure.fst_compProd, Measure.snd_compProd, Measure.snd_map_swap, compProd_posterior_eq_map_swap, fst_compProd, snd_compProd, snd_map_swap
-/
lemma posterior_comp_self [IsMarkovKernel κ] : κ†μ ∘ₘ κ ∘ₘ μ = μ := by
  rw [← Measure.snd_compProd]; rw [compProd_posterior_eq_map_swap]; rw [Measure.snd_map_swap]; rw [Measure.fst_compProd]

/--
lemma `posterior_id` / 引理 `posterior_id`

English:
lemma posterior_id
  given: (μ : Measure Ω) [IsFiniteMeasure μ]
  statement: Kernel.id†μ =ᵐ[μ] Kernel.id
  proof: by
  suffices Kernel.id =ᵐ[Kernel.id ∘ₘ μ] (Kernel.id : Kernel Ω Ω)†μ by
    rw [Measure.id_comp] at this
    filter_upwards [this] with a ha using ha.symm
  refine ae_eq_posterior_of_compProd_eq_swap_comp Kernel.id ?_
  rw [Measure.id_comp]; rw [Measure.compProd_id_eq_copy_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_copy]

中文:
引理 posterior_id
  条件: (μ : 测度 Ω) [是有限测度 μ]
  结论: 核.id†μ =ᵐ[μ] 核.id
  证明: by
  suffices Kernel.id =ᵐ[Kernel.id ∘ₘ μ] (Kernel.id : Kernel Ω Ω)†μ by
    rw [Measure.id_comp] at this
    filter_upwards [this] with a ha using ha.symm
  refine ae_eq_posterior_of_compProd_eq_swap_comp Kernel.id ?_
  rw [Measure.id_comp]; rw [Measure.compProd_id_eq_copy_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_copy]

Depends on / 依赖: Kernel, Kernel.id, Kernel.swap_copy, Measure, Measure.compProd_id_eq_copy_comp, Measure.comp_assoc, Measure.id_comp, ae_eq_posterior_of_compProd_eq_swap_comp, compProd_id_eq_copy_comp, comp_assoc, filter_upwards, ha.symm, id_comp, swap_copy
-/
lemma posterior_id (μ : Measure Ω) [IsFiniteMeasure μ] : Kernel.id†μ =ᵐ[μ] Kernel.id := by
  suffices Kernel.id =ᵐ[Kernel.id ∘ₘ μ] (Kernel.id : Kernel Ω Ω)†μ by
    rw [Measure.id_comp] at this
    filter_upwards [this] with a ha using ha.symm
  refine ae_eq_posterior_of_compProd_eq_swap_comp Kernel.id ?_
  rw [Measure.id_comp]; rw [Measure.compProd_id_eq_copy_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_copy]

/--
lemma `deterministic_comp_posterior` / 引理 `deterministic_comp_posterior`

English:
lemma deterministic_comp_posterior
  statement: [MeasurableSpace.CountablyGenerated 𝓧]
  proof: by
  refine Kernel.ae_eq_of_compProd_eq ?_
  calc μ.map f otimesₘ (Kernel.deterministic f hf ∘ₖ (Kernel.deterministic f hf)†μ)
  _ = (Kernel.deterministic f hf ∘ₘ μ)
      otimesₘ (Kernel.deterministic f hf ∘ₖ (Kernel.deterministic f hf)†μ) := by
    rw [Measure.deterministic_comp_eq_map]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ∥ₖ (Kernel.deterministic f hf)†μ) ∘ₘ
      Kernel.copy 𝓧 ∘ₘ Kernel.deterministic f hf ∘ₘ μ := by
    rw [Measure.compProd_eq_parallelComp_comp_copy_comp]; rw [← Kernel.parallelComp_id_left_comp_parallelComp]; rw [← Measure.comp_assoc]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.deterministic f hf ∥ₖ Kernel.id) ∘ₘ
      Kernel.copy Ω ∘ₘ μ := by rw [parallelProd_posterior_comp_copy_comp]
  _ = (Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.comp_assoc]; rw [Kernel.parallelComp_comp_parallelComp]; rw [Kernel.id_comp]; rw [Kernel.comp_id]
  _ = (Kernel.copy 𝓧 ∘ₖ Kernel.deterministic f hf) ∘ₘ μ := by -- `deterministic` is used here
    rw [Measure.comp_assoc]; rw [Kernel.parallelComp_self_comp_copy]
  _ = μ.map f otimesₘ Kernel.id := by
    rw [Measure.compProd_id_eq_copy_comp]; rw [← Measure.comp_assoc]; rw [Measure.deterministic_comp_eq_map]

中文:
引理 deterministic_comp_posterior
  结论: [可测空间.余untablyGenerated 𝓧]
  证明: by
  refine Kernel.ae_eq_of_compProd_eq ?_
  calc μ.map f otimesₘ (Kernel.deterministic f hf ∘ₖ (Kernel.deterministic f hf)†μ)
  _ = (Kernel.deterministic f hf ∘ₘ μ)
      otimesₘ (Kernel.deterministic f hf ∘ₖ (Kernel.deterministic f hf)†μ) := by
    rw [Measure.deterministic_comp_eq_map]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ∥ₖ (Kernel.deterministic f hf)†μ) ∘ₘ
      Kernel.copy 𝓧 ∘ₘ Kernel.deterministic f hf ∘ₘ μ := by
    rw [Measure.compProd_eq_parallelComp_comp_copy_comp]; rw [← Kernel.parallelComp_id_left_comp_parallelComp]; rw [← Measure.comp_assoc]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.deterministic f hf ∥ₖ Kernel.id) ∘ₘ
      Kernel.copy Ω ∘ₘ μ := by rw [parallelProd_posterior_comp_copy_comp]
  _ = (Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.comp_assoc]; rw [Kernel.parallelComp_comp_parallelComp]; rw [Kernel.id_comp]; rw [Kernel.comp_id]
  _ = (Kernel.copy 𝓧 ∘ₖ Kernel.deterministic f hf) ∘ₘ μ := by -- `deterministic` is used here
    rw [Measure.comp_assoc]; rw [Kernel.parallelComp_self_comp_copy]
  _ = μ.map f otimesₘ Kernel.id := by
    rw [Measure.compProd_id_eq_copy_comp]; rw [← Measure.comp_assoc]; rw [Measure.deterministic_comp_eq_map]

Depends on / 依赖: Kernel, Kernel.ae_eq_of_compProd_eq, Kernel.copy, Kernel.deterministic, Kernel.id, Kernel.parallelC, Measure, Measure.compProd_eq_parallelComp_comp_copy_comp, Measure.deterministic_comp_eq_map, ae_eq_of_compProd_eq, compProd_eq_parallelComp_comp_copy_comp, deterministic, deterministic_comp_eq_map, parallelC
-/
lemma deterministic_comp_posterior [MeasurableSpace.CountablyGenerated 𝓧]
    {f : Ω -> 𝓧} (hf : Measurable f) :
    Kernel.deterministic f hf ∘ₖ (Kernel.deterministic f hf)†μ =ᵐ[μ.map f] Kernel.id := by
  refine Kernel.ae_eq_of_compProd_eq ?_
  calc μ.map f otimesₘ (Kernel.deterministic f hf ∘ₖ (Kernel.deterministic f hf)†μ)
  _ = (Kernel.deterministic f hf ∘ₘ μ)
      otimesₘ (Kernel.deterministic f hf ∘ₖ (Kernel.deterministic f hf)†μ) := by
    rw [Measure.deterministic_comp_eq_map]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ∥ₖ (Kernel.deterministic f hf)†μ) ∘ₘ
      Kernel.copy 𝓧 ∘ₘ Kernel.deterministic f hf ∘ₘ μ := by
    rw [Measure.compProd_eq_parallelComp_comp_copy_comp]; rw [← Kernel.parallelComp_id_left_comp_parallelComp]; rw [← Measure.comp_assoc]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.deterministic f hf ∥ₖ Kernel.id) ∘ₘ
      Kernel.copy Ω ∘ₘ μ := by rw [parallelProd_posterior_comp_copy_comp]
  _ = (Kernel.deterministic f hf ∥ₖ Kernel.deterministic f hf) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [Measure.comp_assoc]; rw [Kernel.parallelComp_comp_parallelComp]; rw [Kernel.id_comp]; rw [Kernel.comp_id]
  _ = (Kernel.copy 𝓧 ∘ₖ Kernel.deterministic f hf) ∘ₘ μ := by -- `deterministic` is used here
    rw [Measure.comp_assoc]; rw [Kernel.parallelComp_self_comp_copy]
  _ = μ.map f otimesₘ Kernel.id := by
    rw [Measure.compProd_id_eq_copy_comp]; rw [← Measure.comp_assoc]; rw [Measure.deterministic_comp_eq_map]

/--
lemma `absolutelyContinuous_posterior` / 引理 `absolutelyContinuous_posterior`

English:
lemma absolutelyContinuous_posterior
  given: {ν : Measure 𝓧} [SFinite ν] (h_ac : forallᵐ ω ∂μ, κ ω ≪ ν)
  proof: by
  suffices (κ ∘ₘ μ) otimesₘ (κ†μ) ≪ ν.prod μ by
    rw [← Measure.compProd_const] at this
    simpa using this.kernel_of_compProd
  suffices μ otimesₘ κ ≪ μ.prod ν by
    rw [compProd_posterior_eq_map_swap]; rw [← Measure.prod_swap]
    exact this.map measurable_swap
  rw [← Measure.compProd_const]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  simpa

中文:
引理 absolutelyContinuous_posterior
  条件: {ν : 测度 𝓧} [SFinite ν] (h_ac : 对任意ᵐ ω ∂μ, κ ω ≪ ν)
  证明: by
  suffices (κ ∘ₘ μ) otimesₘ (κ†μ) ≪ ν.prod μ by
    rw [← Measure.compProd_const] at this
    simpa using this.kernel_of_compProd
  suffices μ otimesₘ κ ≪ μ.prod ν by
    rw [compProd_posterior_eq_map_swap]; rw [← Measure.prod_swap]
    exact this.map measurable_swap
  rw [← Measure.compProd_const]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  simpa

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.compProd_right, Measure.compProd_const, Measure.prod_swap, compProd_const, compProd_posterior_eq_map_swap, compProd_right, kernel_of_compProd, measurable_swap, prod_swap, this.kernel_of_compProd, this.map
-/
lemma absolutelyContinuous_posterior {ν : Measure 𝓧} [SFinite ν] (h_ac : forallᵐ ω ∂μ, κ ω ≪ ν) :
    forallᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ := by
  suffices (κ ∘ₘ μ) otimesₘ (κ†μ) ≪ ν.prod μ by
    rw [← Measure.compProd_const] at this
    simpa using this.kernel_of_compProd
  suffices μ otimesₘ κ ≪ μ.prod ν by
    rw [compProd_posterior_eq_map_swap]; rw [← Measure.prod_swap]
    exact this.map measurable_swap
  rw [← Measure.compProd_const]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  simpa

section StandardBorelSpace

variable [StandardBorelSpace 𝓧] [Nonempty 𝓧]

/--
lemma `posterior_posterior` / 引理 `posterior_posterior`

English:
lemma posterior_posterior
  given: [IsMarkovKernel κ]
  statement: (κ†μ)†(κ ∘ₘ μ) =ᵐ[μ] κ
  proof: by
  suffices κ =ᵐ[κ†μ ∘ₘ κ ∘ₘ μ] (κ†μ)†(κ ∘ₘ μ) by
    rw [posterior_comp_self] at this
    filter_upwards [this] with a h using h.symm
  refine ae_eq_posterior_of_compProd_eq_swap_comp κ ?_
  rw [posterior_comp_self]; rw [compProd_posterior_eq_swap_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_swap]; rw [Measure.id_comp]

中文:
引理 posterior_posterior
  条件: [是MarkovKernel κ]
  结论: (κ†μ)†(κ ∘ₘ μ) =ᵐ[μ] κ
  证明: by
  suffices κ =ᵐ[κ†μ ∘ₘ κ ∘ₘ μ] (κ†μ)†(κ ∘ₘ μ) by
    rw [posterior_comp_self] at this
    filter_upwards [this] with a h using h.symm
  refine ae_eq_posterior_of_compProd_eq_swap_comp κ ?_
  rw [posterior_comp_self]; rw [compProd_posterior_eq_swap_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_swap]; rw [Measure.id_comp]

Depends on / 依赖: Kernel, Kernel.swap_swap, Measure, Measure.comp_assoc, Measure.id_comp, ae_eq_posterior_of_compProd_eq_swap_comp, compProd_posterior_eq_swap_comp, comp_assoc, filter_upwards, h.symm, id_comp, posterior_comp_self, swap_swap
-/
lemma posterior_posterior [IsMarkovKernel κ] : (κ†μ)†(κ ∘ₘ μ) =ᵐ[μ] κ := by
  suffices κ =ᵐ[κ†μ ∘ₘ κ ∘ₘ μ] (κ†μ)†(κ ∘ₘ μ) by
    rw [posterior_comp_self] at this
    filter_upwards [this] with a h using h.symm
  refine ae_eq_posterior_of_compProd_eq_swap_comp κ ?_
  rw [posterior_comp_self]; rw [compProd_posterior_eq_swap_comp]; rw [Measure.comp_assoc]; rw [Kernel.swap_swap]; rw [Measure.id_comp]

/--
lemma `posterior_comp` / 引理 `posterior_comp`

English:
lemma posterior_comp
  given: {η : Kernel 𝓧 𝓨} [IsFiniteKernel η]
  proof: by
  rw [Measure.comp_assoc]
  refine (ae_eq_posterior_of_compProd_eq_swap_comp ((κ†μ) ∘ₖ η†(κ ∘ₘ μ)) ?_).symm
  simp_rw [Measure.compProd_eq_comp_prod, ← Kernel.parallelComp_comp_copy,
    ← Kernel.parallelComp_id_left_comp_parallelComp, ← Measure.comp_assoc]
  calc (Kernel.id ∥ₖ κ†μ) ∘ₘ (Kernel.id ∥ₖ η†(κ ∘ₘ μ)) ∘ₘ (Kernel.copy 𝓨) ∘ₘ η ∘ₘ κ ∘ₘ μ
  _ = (Kernel.id ∥ₖ κ†μ) ∘ₘ (η ∥ₖ Kernel.id) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp]
  _ = (η ∥ₖ Kernel.id) ∘ₘ (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := by
    rw [Measure.comp_assoc]; rw [Kernel.parallelComp_comm]; rw [← Measure.comp_assoc]
  _ = (η ∥ₖ Kernel.id) ∘ₘ (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp]
  _ = (Kernel.swap _ _) ∘ₘ (Kernel.id ∥ₖ η) ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    simp_rw [Measure.comp_assoc]
    conv_rhs => rw [← Kernel.comp_assoc]
    rw [Kernel.swap_parallelComp]; rw [Kernel.comp_assoc]; rw [← Kernel.comp_assoc (Kernel.swap Ω 𝓧)]; rw [Kernel.swap_parallelComp]; rw [Kernel.comp_assoc]; rw [Kernel.swap_copy]

中文:
引理 posterior_comp
  条件: {η : 核 𝓧 𝓨} [是FiniteKernel η]
  证明: by
  rw [Measure.comp_assoc]
  refine (ae_eq_posterior_of_compProd_eq_swap_comp ((κ†μ) ∘ₖ η†(κ ∘ₘ μ)) ?_).symm
  simp_rw [Measure.compProd_eq_comp_prod, ← Kernel.parallelComp_comp_copy,
    ← Kernel.parallelComp_id_left_comp_parallelComp, ← Measure.comp_assoc]
  calc (Kernel.id ∥ₖ κ†μ) ∘ₘ (Kernel.id ∥ₖ η†(κ ∘ₘ μ)) ∘ₘ (Kernel.copy 𝓨) ∘ₘ η ∘ₘ κ ∘ₘ μ
  _ = (Kernel.id ∥ₖ κ†μ) ∘ₘ (η ∥ₖ Kernel.id) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp]
  _ = (η ∥ₖ Kernel.id) ∘ₘ (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := by
    rw [Measure.comp_assoc]; rw [Kernel.parallelComp_comm]; rw [← Measure.comp_assoc]
  _ = (η ∥ₖ Kernel.id) ∘ₘ (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp]
  _ = (Kernel.swap _ _) ∘ₘ (Kernel.id ∥ₖ η) ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    simp_rw [Measure.comp_assoc]
    conv_rhs => rw [← Kernel.comp_assoc]
    rw [Kernel.swap_parallelComp]; rw [Kernel.comp_assoc]; rw [← Kernel.comp_assoc (Kernel.swap Ω 𝓧)]; rw [Kernel.swap_parallelComp]; rw [Kernel.comp_assoc]; rw [Kernel.swap_copy]

Depends on / 依赖: Kernel, Kernel.copy, Kernel.id, Kernel.parallelComp_comp_copy, Kernel.parallelComp_id_left_comp_parallelComp, Measure, Measure.compProd_eq_comp_prod, Measure.comp_assoc, ae_eq_posterior_of_compProd_eq_swap_comp, compProd_eq_comp_prod, comp_assoc, parallelComp_comp_copy, parallelComp_id_left_comp_parallelComp, parallelProd_posterior_comp_copy_comp, simp_rw
-/
lemma posterior_comp {η : Kernel 𝓧 𝓨} [IsFiniteKernel η] :
    (η ∘ₖ κ)†μ =ᵐ[η ∘ₘ κ ∘ₘ μ] κ†μ ∘ₖ η†(κ ∘ₘ μ) := by
  rw [Measure.comp_assoc]
  refine (ae_eq_posterior_of_compProd_eq_swap_comp ((κ†μ) ∘ₖ η†(κ ∘ₘ μ)) ?_).symm
  simp_rw [Measure.compProd_eq_comp_prod, ← Kernel.parallelComp_comp_copy,
    ← Kernel.parallelComp_id_left_comp_parallelComp, ← Measure.comp_assoc]
  calc (Kernel.id ∥ₖ κ†μ) ∘ₘ (Kernel.id ∥ₖ η†(κ ∘ₘ μ)) ∘ₘ (Kernel.copy 𝓨) ∘ₘ η ∘ₘ κ ∘ₘ μ
  _ = (Kernel.id ∥ₖ κ†μ) ∘ₘ (η ∥ₖ Kernel.id) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp]
  _ = (η ∥ₖ Kernel.id) ∘ₘ (Kernel.id ∥ₖ κ†μ) ∘ₘ Kernel.copy 𝓧 ∘ₘ κ ∘ₘ μ := by
    rw [Measure.comp_assoc]; rw [Kernel.parallelComp_comm]; rw [← Measure.comp_assoc]
  _ = (η ∥ₖ Kernel.id) ∘ₘ (κ ∥ₖ Kernel.id) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    rw [parallelProd_posterior_comp_copy_comp]
  _ = (Kernel.swap _ _) ∘ₘ (Kernel.id ∥ₖ η) ∘ₘ (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy Ω ∘ₘ μ := by
    simp_rw [Measure.comp_assoc]
    conv_rhs => rw [← Kernel.comp_assoc]
    rw [Kernel.swap_parallelComp]; rw [Kernel.comp_assoc]; rw [← Kernel.comp_assoc (Kernel.swap Ω 𝓧)]; rw [Kernel.swap_parallelComp]; rw [Kernel.comp_assoc]; rw [Kernel.swap_copy]

end StandardBorelSpace


section CountableOrCountablyGenerated

variable [MeasurableSpace.CountableOrCountablyGenerated Ω 𝓧]

/--
lemma `absolutelyContinuous_of_posterior` / 引理 `absolutelyContinuous_of_posterior`

English:
lemma absolutelyContinuous_of_posterior
  given: (h_ac : forallᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ)
  proof: by
  suffices μ otimesₘ κ ≪ μ.prod (κ ∘ₘ μ) by
    rw [← Measure.compProd_const] at this
    simpa using this.kernel_of_compProd
  suffices (κ ∘ₘ μ) otimesₘ κ†μ ≪ (κ ∘ₘ μ).prod μ by
    rw [← swap_compProd_posterior]; rw [← Measure.prod_swap]; rw [Measure.swap_comp]
    exact this.map measurable_swap
  rw [← Measure.compProd_const]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  simpa

中文:
引理 absolutelyContinuous_of_posterior
  条件: (h_ac : 对任意ᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ)
  证明: by
  suffices μ otimesₘ κ ≪ μ.prod (κ ∘ₘ μ) by
    rw [← Measure.compProd_const] at this
    simpa using this.kernel_of_compProd
  suffices (κ ∘ₘ μ) otimesₘ κ†μ ≪ (κ ∘ₘ μ).prod μ by
    rw [← swap_compProd_posterior]; rw [← Measure.prod_swap]; rw [Measure.swap_comp]
    exact this.map measurable_swap
  rw [← Measure.compProd_const]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  simpa

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.compProd_right, Measure.compProd_const, Measure.prod_swap, Measure.swap_comp, compProd_const, compProd_right, kernel_of_compProd, measurable_swap, prod_swap, swap_comp, swap_compProd_posterior, this.kernel_of_compProd, this.map
-/
lemma absolutelyContinuous_of_posterior (h_ac : forallᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ) :
    forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ := by
  suffices μ otimesₘ κ ≪ μ.prod (κ ∘ₘ μ) by
    rw [← Measure.compProd_const] at this
    simpa using this.kernel_of_compProd
  suffices (κ ∘ₘ μ) otimesₘ κ†μ ≪ (κ ∘ₘ μ).prod μ by
    rw [← swap_compProd_posterior]; rw [← Measure.prod_swap]; rw [Measure.swap_comp]
    exact this.map measurable_swap
  rw [← Measure.compProd_const]
  refine Measure.AbsolutelyContinuous.compProd_right ?_
  simpa

/--
lemma `absolutelyContinuous_posterior_iff` / 引理 `absolutelyContinuous_posterior_iff`

English:
lemma absolutelyContinuous_posterior_iff
  statement: (forallᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ) ↔ forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ
  proof: ⟨absolutelyContinuous_of_posterior, absolutelyContinuous_posterior⟩

中文:
引理 absolutelyContinuous_posterior_iff
  结论: (对任意ᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ) ↔ 对任意ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ
  证明: ⟨absolutelyContinuous_of_posterior, absolutelyContinuous_posterior⟩

Depends on / 依赖: absolutelyContinuous_of_posterior, absolutelyContinuous_posterior
-/
lemma absolutelyContinuous_posterior_iff : (forallᵐ b ∂(κ ∘ₘ μ), (κ†μ) b ≪ μ) ↔ forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ :=
  ⟨absolutelyContinuous_of_posterior, absolutelyContinuous_posterior⟩

/--
lemma `Kernel.absolutelyContinuous_comp_of_absolutelyContinuous` / 引理 `Kernel.absolutelyContinuous_comp_of_absolutelyContinuous`

English:
lemma Kernel.absolutelyContinuous_comp_of_absolutelyContinuous
  statement: {ν : Measure 𝓧} [SFinite ν]
  proof: by
  rw [← absolutelyContinuous_posterior_iff]
  exact absolutelyContinuous_posterior h_ac

中文:
引理 核.absolutelyContinuous_comp_of_absolutelyContinuous
  结论: {ν : 测度 𝓧} [SFinite ν]
  证明: by
  rw [← absolutelyContinuous_posterior_iff]
  exact absolutelyContinuous_posterior h_ac

Depends on / 依赖: absolutelyContinuous_posterior, absolutelyContinuous_posterior_iff, h_ac
-/
lemma Kernel.absolutelyContinuous_comp_of_absolutelyContinuous {ν : Measure 𝓧} [SFinite ν]
    (h_ac : forallᵐ ω ∂μ, κ ω ≪ ν) :
    forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ := by
  rw [← absolutelyContinuous_posterior_iff]
  exact absolutelyContinuous_posterior h_ac

/--
lemma `rnDeriv_posterior_ae_prod` / 引理 `rnDeriv_posterior_ae_prod`

English:
lemma rnDeriv_posterior_ae_prod
  given: (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ)
  proof: by
  -- We prove the a.e. equality by showing that integrals on the π-system of rectangles are equal.
  -- First, the integral of the left-hand side on `s ×ˢ t` is `(μ ⊗ₘ κ) (s ×ˢ t)`, which we prove
  -- by showing that it's equal to `((κ ∘ₘ μ) ⊗ κ†μ) (t ×ˢ s)` and using the main property of the
  -- posterior.
  have h1 {s : Set Ω} {t : Set 𝓧} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      ∫⁻ x in s ×ˢ t, (κ†μ).rnDeriv (Kernel.const _ μ) x.2 x.1 ∂μ.prod (⇑κ ∘ₘ μ)
        = (μ otimesₘ κ) (s ×ˢ t) := by
    rw [setLIntegral_prod_symm _ (by fun_prop)]; rw [← swap_compProd_posterior]; rw [Measure.swap_comp]; rw [Measure.map_apply measurable_swap (hs.prod ht)]; rw [Set.preimage_swap_prod]; rw [Measure.compProd_apply_prod ht hs]
refine lintegral_congr_ae ae_restrict_of_ae ?_
    filter_upwards [absolutelyContinuous_posterior h_ac] with x h_ac'
    change ∫⁻ ω in s, (κ†μ).rnDeriv (Kernel.const 𝓧 μ) x ω ∂(Kernel.const 𝓧 μ x) = _
    rw [Kernel.setLIntegral_rnDeriv h_ac' hs]
  have h2 {s : Set Ω} {t : Set 𝓧} (hs : MeasurableSet s) (ht : MeasurableSet t) :
  -- Second, the integral of the right-hand side on `s ×ˢ t` is `(μ ⊗ₘ κ) (s ×ˢ t)`.
      ∫⁻ x in s ×ˢ t, κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) x.1 x.2 ∂μ.prod (⇑κ ∘ₘ μ)
        = (μ otimesₘ κ) (s ×ˢ t) := by
    rw [setLIntegral_prod _ (by fun_prop)]; rw [Measure.compProd_apply_prod hs ht]
refine lintegral_congr_ae ae_restrict_of_ae ?_
    filter_upwards [h_ac] with ω h_ac
    change ∫⁻ x in t, κ.rnDeriv (Kernel.const Ω (κ ∘ₘ μ)) ω x ∂(Kernel.const Ω (κ ∘ₘ μ) ω) = _
    rw [Kernel.setLIntegral_rnDeriv h_ac ht]
  -- We extend from the π-system to the σ-algebra.
  refine ae_eq_of_setLIntegral_prod_eq (by fun_prop) (by fun_prop) ?_ ?_
  · refine ne_of_lt ?_
    calc ∫⁻ x, (κ†μ).rnDeriv (Kernel.const _ μ) x.2 x.1 ∂μ.prod (κ ∘ₘ μ)
    _ = (μ otimesₘ κ) Set.univ := by rw [← setLIntegral_univ, ← Set.univ_prod_univ, h1 .univ .univ]
    _ < ⊤ := measure_lt_top _ _
  · intro s hs t ht
    rw [h1 hs ht]; rw [h2 hs ht]

中文:
引理 rnDeriv_posterior_ae_prod
  条件: (h_ac : 对任意ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ)
  证明: by
  -- We prove the a.e. equality by showing that integrals on the π-system of rectangles are equal.
  -- First, the integral of the left-hand side on `s ×ˢ t` is `(μ ⊗ₘ κ) (s ×ˢ t)`, which we prove
  -- by showing that it's equal to `((κ ∘ₘ μ) ⊗ κ†μ) (t ×ˢ s)` and using the main property of the
  -- posterior.
  have h1 {s : Set Ω} {t : Set 𝓧} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      ∫⁻ x in s ×ˢ t, (κ†μ).rnDeriv (Kernel.const _ μ) x.2 x.1 ∂μ.prod (⇑κ ∘ₘ μ)
        = (μ otimesₘ κ) (s ×ˢ t) := by
    rw [setLIntegral_prod_symm _ (by fun_prop)]; rw [← swap_compProd_posterior]; rw [Measure.swap_comp]; rw [Measure.map_apply measurable_swap (hs.prod ht)]; rw [Set.preimage_swap_prod]; rw [Measure.compProd_apply_prod ht hs]
refine lintegral_congr_ae ae_restrict_of_ae ?_
    filter_upwards [absolutelyContinuous_posterior h_ac] with x h_ac'
    change ∫⁻ ω in s, (κ†μ).rnDeriv (Kernel.const 𝓧 μ) x ω ∂(Kernel.const 𝓧 μ x) = _
    rw [Kernel.setLIntegral_rnDeriv h_ac' hs]
  have h2 {s : Set Ω} {t : Set 𝓧} (hs : MeasurableSet s) (ht : MeasurableSet t) :
  -- Second, the integral of the right-hand side on `s ×ˢ t` is `(μ ⊗ₘ κ) (s ×ˢ t)`.
      ∫⁻ x in s ×ˢ t, κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) x.1 x.2 ∂μ.prod (⇑κ ∘ₘ μ)
        = (μ otimesₘ κ) (s ×ˢ t) := by
    rw [setLIntegral_prod _ (by fun_prop)]; rw [Measure.compProd_apply_prod hs ht]
refine lintegral_congr_ae ae_restrict_of_ae ?_
    filter_upwards [h_ac] with ω h_ac
    change ∫⁻ x in t, κ.rnDeriv (Kernel.const Ω (κ ∘ₘ μ)) ω x ∂(Kernel.const Ω (κ ∘ₘ μ) ω) = _
    rw [Kernel.setLIntegral_rnDeriv h_ac ht]
  -- We extend from the π-system to the σ-algebra.
  refine ae_eq_of_setLIntegral_prod_eq (by fun_prop) (by fun_prop) ?_ ?_
  · refine ne_of_lt ?_
    calc ∫⁻ x, (κ†μ).rnDeriv (Kernel.const _ μ) x.2 x.1 ∂μ.prod (κ ∘ₘ μ)
    _ = (μ otimesₘ κ) Set.univ := by rw [← setLIntegral_univ, ← Set.univ_prod_univ, h1 .univ .univ]
    _ < ⊤ := measure_lt_top _ _
  · intro s hs t ht
    rw [h1 hs ht]; rw [h2 hs ht]
-/
lemma rnDeriv_posterior_ae_prod (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    forallᵐ p ∂(μ.prod (κ ∘ₘ μ)),
      (κ†μ).rnDeriv (Kernel.const _ μ) p.2 p.1 = κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) p.1 p.2 := by
  -- We prove the a.e. equality by showing that integrals on the π-system of rectangles are equal.
  -- First, the integral of the left-hand side on `s ×ˢ t` is `(μ ⊗ₘ κ) (s ×ˢ t)`, which we prove
  -- by showing that it's equal to `((κ ∘ₘ μ) ⊗ κ†μ) (t ×ˢ s)` and using the main property of the
  -- posterior.
  have h1 {s : Set Ω} {t : Set 𝓧} (hs : MeasurableSet s) (ht : MeasurableSet t) :
      ∫⁻ x in s ×ˢ t, (κ†μ).rnDeriv (Kernel.const _ μ) x.2 x.1 ∂μ.prod (⇑κ ∘ₘ μ)
        = (μ otimesₘ κ) (s ×ˢ t) := by
    rw [setLIntegral_prod_symm _ (by fun_prop)]; rw [← swap_compProd_posterior]; rw [Measure.swap_comp]; rw [Measure.map_apply measurable_swap (hs.prod ht)]; rw [Set.preimage_swap_prod]; rw [Measure.compProd_apply_prod ht hs]
refine lintegral_congr_ae ae_restrict_of_ae ?_
    filter_upwards [absolutelyContinuous_posterior h_ac] with x h_ac'
    change ∫⁻ ω in s, (κ†μ).rnDeriv (Kernel.const 𝓧 μ) x ω ∂(Kernel.const 𝓧 μ x) = _
    rw [Kernel.setLIntegral_rnDeriv h_ac' hs]
  have h2 {s : Set Ω} {t : Set 𝓧} (hs : MeasurableSet s) (ht : MeasurableSet t) :
  -- Second, the integral of the right-hand side on `s ×ˢ t` is `(μ ⊗ₘ κ) (s ×ˢ t)`.
      ∫⁻ x in s ×ˢ t, κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) x.1 x.2 ∂μ.prod (⇑κ ∘ₘ μ)
        = (μ otimesₘ κ) (s ×ˢ t) := by
    rw [setLIntegral_prod _ (by fun_prop)]; rw [Measure.compProd_apply_prod hs ht]
refine lintegral_congr_ae ae_restrict_of_ae ?_
    filter_upwards [h_ac] with ω h_ac
    change ∫⁻ x in t, κ.rnDeriv (Kernel.const Ω (κ ∘ₘ μ)) ω x ∂(Kernel.const Ω (κ ∘ₘ μ) ω) = _
    rw [Kernel.setLIntegral_rnDeriv h_ac ht]
  -- We extend from the π-system to the σ-algebra.
  refine ae_eq_of_setLIntegral_prod_eq (by fun_prop) (by fun_prop) ?_ ?_
  · refine ne_of_lt ?_
    calc ∫⁻ x, (κ†μ).rnDeriv (Kernel.const _ μ) x.2 x.1 ∂μ.prod (κ ∘ₘ μ)
    _ = (μ otimesₘ κ) Set.univ := by rw [← setLIntegral_univ, ← Set.univ_prod_univ, h1 .univ .univ]
    _ < ⊤ := measure_lt_top _ _
  · intro s hs t ht
    rw [h1 hs ht]; rw [h2 hs ht]

/--
lemma `rnDeriv_posterior` / 引理 `rnDeriv_posterior`

English:
lemma rnDeriv_posterior
  given: (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ)
  proof: by
  convert!
    Measure.ae_ae_of_ae_prod
      (rnDeriv_posterior_ae_prod h_ac) -- much faster than `exact`
         -- much faster than `exact`

中文:
引理 rnDeriv_posterior
  条件: (h_ac : 对任意ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ)
  证明: by
  convert!
    Measure.ae_ae_of_ae_prod
      (rnDeriv_posterior_ae_prod h_ac) -- much faster than `exact`
         -- much faster than `exact`

Depends on / 依赖: Measure, Measure.ae_ae_of_ae_prod, ae_ae_of_ae_prod, convert, faster, h_ac, rnDeriv_posterior_ae_prod
-/
lemma rnDeriv_posterior (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    forallᵐ ω ∂μ, forallᵐ x ∂(κ ∘ₘ μ),
      (κ†μ).rnDeriv (Kernel.const _ μ) x ω = κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x := by
  convert!
    Measure.ae_ae_of_ae_prod
      (rnDeriv_posterior_ae_prod h_ac) -- much faster than `exact`
         -- much faster than `exact`

/--
lemma `rnDeriv_posterior_symm` / 引理 `rnDeriv_posterior_symm`

English:
lemma rnDeriv_posterior_symm
  given: (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ)
  proof: by
  rw [Measure.ae_ae_comm]
  · exact rnDeriv_posterior h_ac
  · measurability

中文:
引理 rnDeriv_posterior_symm
  条件: (h_ac : 对任意ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ)
  证明: by
  rw [Measure.ae_ae_comm]
  · exact rnDeriv_posterior h_ac
  · measurability

Depends on / 依赖: Measure, Measure.ae_ae_comm, ae_ae_comm, h_ac, measurability, rnDeriv_posterior
-/
lemma rnDeriv_posterior_symm (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    forallᵐ x ∂(κ ∘ₘ μ), forallᵐ ω ∂μ,
      (κ†μ).rnDeriv (Kernel.const _ μ) x ω = κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x := by
  rw [Measure.ae_ae_comm]
  · exact rnDeriv_posterior h_ac
  · measurability

/--
lemma `posterior_eq_withDensity` / 引理 `posterior_eq_withDensity`

English:
lemma posterior_eq_withDensity
  given: (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ)
  proof: by
  filter_upwards [rnDeriv_posterior_symm h_ac, absolutelyContinuous_posterior h_ac] with x h h_ac'
  ext s hs
  rw [← Measure.setLIntegral_rnDeriv h_ac']; rw [withDensity_apply _ hs]
  refine setLIntegral_congr_fun_ae hs ?_
  filter_upwards [h, Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ†μ) (η := Kernel.const 𝓧 μ) (a := x)]
    with ω h h_eq hωs
  rw [← h]; rw [h_eq]; rw [Kernel.const_apply]

中文:
引理 posterior_eq_withDensity
  条件: (h_ac : 对任意ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ)
  证明: by
  filter_upwards [rnDeriv_posterior_symm h_ac, absolutelyContinuous_posterior h_ac] with x h h_ac'
  ext s hs
  rw [← Measure.setLIntegral_rnDeriv h_ac']; rw [withDensity_apply _ hs]
  refine setLIntegral_congr_fun_ae hs ?_
  filter_upwards [h, Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ†μ) (η := Kernel.const 𝓧 μ) (a := x)]
    with ω h h_eq hωs
  rw [← h]; rw [h_eq]; rw [Kernel.const_apply]

Depends on / 依赖: Kernel, Kernel.const, Kernel.const_apply, Kernel.rnDeriv_eq_rnDeriv_measure, Measure, Measure.setLIntegral_rnDeriv, absolutelyContinuous_posterior, const_apply, filter_upwards, h_ac, h_eq, rnDeriv_eq_rnDeriv_measure, rnDeriv_posterior_symm, setLIntegral_congr_fun_ae, setLIntegral_rnDeriv, withDensity_apply
-/
lemma posterior_eq_withDensity (h_ac : forallᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ) :
    forallᵐ x ∂(κ ∘ₘ μ), (κ†μ) x = μ.withDensity (fun ω => κ.rnDeriv (Kernel.const _ (κ ∘ₘ μ)) ω x) := by
  filter_upwards [rnDeriv_posterior_symm h_ac, absolutelyContinuous_posterior h_ac] with x h h_ac'
  ext s hs
  rw [← Measure.setLIntegral_rnDeriv h_ac']; rw [withDensity_apply _ hs]
  refine setLIntegral_congr_fun_ae hs ?_
  filter_upwards [h, Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ†μ) (η := Kernel.const 𝓧 μ) (a := x)]
    with ω h h_eq hωs
  rw [← h]; rw [h_eq]; rw [Kernel.const_apply]

/--
lemma `posterior_eq_withDensity_of_countable` / 引理 `posterior_eq_withDensity_of_countable`

English:
lemma posterior_eq_withDensity_of_countable
  statement: {Ω : Type*} [Countable Ω] [MeasurableSpace Ω]
  proof: by
  have h_rnDeriv ω := Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := Kernel.const Ω (κ ∘ₘ μ))
    (a := ω)
  simp only [Filter.EventuallyEq, Kernel.const_apply] at h_rnDeriv
  rw [← ae_all_iff] at h_rnDeriv
  filter_upwards [posterior_eq_withDensity Measure.absolutelyContinuous_comp_of_countable,
    h_rnDeriv] with x hx hx_all
  simp_rw [hx, hx_all]

中文:
引理 posterior_eq_withDensity_of_countable
  结论: {Ω : 类型} [可数 Ω] [可测空间 Ω]
  证明: by
  have h_rnDeriv ω := Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := Kernel.const Ω (κ ∘ₘ μ))
    (a := ω)
  simp only [Filter.EventuallyEq, Kernel.const_apply] at h_rnDeriv
  rw [← ae_all_iff] at h_rnDeriv
  filter_upwards [posterior_eq_withDensity Measure.absolutelyContinuous_comp_of_countable,
    h_rnDeriv] with x hx hx_all
  simp_rw [hx, hx_all]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Kernel, Kernel.const, Kernel.const_apply, Kernel.rnDeriv_eq_rnDeriv_measure, Measure, Measure.absolutelyContinuous_comp_of_countable, absolutelyContinuous_comp_of_countable, ae_all_iff, const_apply, filter_upwards, h_rnDeriv, hx_all, posterior_eq_withDensity, rnDeriv_eq_rnDeriv_measure, simp_rw
-/
lemma posterior_eq_withDensity_of_countable {Ω : Type*} [Countable Ω] [MeasurableSpace Ω]
    [Nonempty Ω] [StandardBorelSpace Ω] (κ : Kernel Ω 𝓧) [IsFiniteKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    forallᵐ x ∂(κ ∘ₘ μ), (κ†μ) x = μ.withDensity (fun ω => (κ ω).rnDeriv (κ ∘ₘ μ) x) := by
  have h_rnDeriv ω := Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := Kernel.const Ω (κ ∘ₘ μ))
    (a := ω)
  simp only [Filter.EventuallyEq, Kernel.const_apply] at h_rnDeriv
  rw [← ae_all_iff] at h_rnDeriv
  filter_upwards [posterior_eq_withDensity Measure.absolutelyContinuous_comp_of_countable,
    h_rnDeriv] with x hx hx_all
  simp_rw [hx, hx_all]

end CountableOrCountablyGenerated

section Bool

/--
lemma `posterior_boolKernel_apply_false` / 引理 `posterior_boolKernel_apply_false`

English:
lemma posterior_boolKernel_apply_false
  statement: (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  proof: by
  filter_upwards [posterior_eq_withDensity_of_countable (Kernel.boolKernel μ ν) π] with x hx
  rw [hx]
  simp

中文:
引理 posterior_boolKernel_apply_false
  结论: (μ ν : 测度 𝓧) [是有限测度 μ] [是有限测度 ν]
  证明: by
  filter_upwards [posterior_eq_withDensity_of_countable (Kernel.boolKernel μ ν) π] with x hx
  rw [hx]
  simp

Depends on / 依赖: Kernel, Kernel.boolKernel, boolKernel, filter_upwards, posterior_eq_withDensity_of_countable
-/
lemma posterior_boolKernel_apply_false (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    forallᵐ x ∂Kernel.boolKernel μ ν ∘ₘ π, ((Kernel.boolKernel μ ν)†π) x {false}
      = π {false} * μ.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x := by
  filter_upwards [posterior_eq_withDensity_of_countable (Kernel.boolKernel μ ν) π] with x hx
  rw [hx]
  simp

/--
lemma `posterior_boolKernel_apply_true` / 引理 `posterior_boolKernel_apply_true`

English:
lemma posterior_boolKernel_apply_true
  statement: (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  proof: by
  filter_upwards [posterior_eq_withDensity_of_countable (Kernel.boolKernel μ ν) π] with x hx
  rw [hx]
  simp

中文:
引理 posterior_boolKernel_apply_true
  结论: (μ ν : 测度 𝓧) [是有限测度 μ] [是有限测度 ν]
  证明: by
  filter_upwards [posterior_eq_withDensity_of_countable (Kernel.boolKernel μ ν) π] with x hx
  rw [hx]
  simp

Depends on / 依赖: Kernel, Kernel.boolKernel, boolKernel, filter_upwards, posterior_eq_withDensity_of_countable
-/
lemma posterior_boolKernel_apply_true (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (π : Measure Bool) [IsFiniteMeasure π] :
    forallᵐ x ∂Kernel.boolKernel μ ν ∘ₘ π, ((Kernel.boolKernel μ ν)†π) x {true}
      = π {true} * ν.rnDeriv (Kernel.boolKernel μ ν ∘ₘ π) x := by
  filter_upwards [posterior_eq_withDensity_of_countable (Kernel.boolKernel μ ν) π] with x hx
  rw [hx]
  simp

end Bool

end ProbabilityTheory
