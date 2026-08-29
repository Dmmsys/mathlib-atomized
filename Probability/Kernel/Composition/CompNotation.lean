/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Basic

/-!
# Notation for the composition of a measure and a kernel

This operation, for which we introduce the notation `∘ₘ`, takes `μ : Measure α` and
`κ : Kernel α β` and creates `κ ∘ₘ μ : Measure β`. The integral of a function against `κ ∘ₘ μ` is
`∫⁻ x, f x ∂(κ ∘ₘ μ) = ∫⁻ a, ∫⁻ b, f b ∂(κ a) ∂μ`.

This file does not define composition but only introduces notation for
`MeasureTheory.Measure.bind μ κ`.

## Notation

* `κ ∘ₘ μ = MeasureTheory.Measure.bind μ κ`, for `κ` a kernel.
-/

public section

/- This file is only for lemmas that are direct specializations of `Measure.bind` to kernels,
anything more involved should go elsewhere (for example the `MeasureComp` file). -/
assert_not_exists ProbabilityTheory.Kernel.compProd

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ : Kernel α β}

/-- Composition of a measure and a kernel.

Notation for `MeasureTheory.Measure.bind` -/
scoped[ProbabilityTheory] notation:100 κ:101 " ∘ₘ " μ:100 => MeasureTheory.Measure.bind μ κ

@[simp]
/--
lemma `comp_apply_univ` / 引理 `comp_apply_univ`

English:
lemma comp_apply_univ
  given: [IsMarkovKernel κ]
  statement: (κ ∘ₘ μ) Set.univ = μ Set.univ
  proof: by
  simp [bind_apply .univ κ.aemeasurable]

中文:
引理 comp_apply_univ
  条件: [IsMarkovKernel κ]
  结论: (κ ∘ₘ μ) Set.univ = μ Set.univ
  证明: by
  simp [bind_apply .univ κ.aemeasurable]

Depends on / 依赖: aemeasurable, bind_apply
-/
lemma comp_apply_univ [IsMarkovKernel κ] : (κ ∘ₘ μ) Set.univ = μ Set.univ := by
  simp [bind_apply .univ κ.aemeasurable]

/--
lemma `deterministic_comp_eq_map` / 引理 `deterministic_comp_eq_map`

English:
lemma deterministic_comp_eq_map
  given: {f : α -> β} (hf : Measurable f)
  proof: Measure.bind_dirac_eq_map μ hf

@[simp]

中文:
引理 deterministic_comp_eq_map
  条件: {f : α -> β} (hf : Measurable f)
  证明: Measure.bind_dirac_eq_map μ hf

@[simp]

Depends on / 依赖: Measure, Measure.bind_dirac_eq_map, bind_dirac_eq_map
-/
lemma deterministic_comp_eq_map {f : α -> β} (hf : Measurable f) :
    Kernel.deterministic f hf ∘ₘ μ = μ.map f :=
  Measure.bind_dirac_eq_map μ hf

@[simp]
/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  statement: Kernel.id ∘ₘ μ = μ
  proof: by rw [Kernel.id, deterministic_comp_eq_map, Measure.map_id]

中文:
引理 id_comp
  结论: Kernel.id ∘ₘ μ = μ
  证明: by rw [Kernel.id, deterministic_comp_eq_map, Measure.map_id]

Depends on / 依赖: Kernel, Kernel.id, Measure, Measure.map_id, deterministic_comp_eq_map, map_id
-/
lemma id_comp : Kernel.id ∘ₘ μ = μ := by rw [Kernel.id, deterministic_comp_eq_map, Measure.map_id]

/--
lemma `swap_comp` / 引理 `swap_comp`

English:
lemma swap_comp
  given: {μ : Measure (α × β)}
  statement: (Kernel.swap α β) ∘ₘ μ = μ.map Prod.swap
  proof: deterministic_comp_eq_map measurable_swap

@[simp]

中文:
引理 swap_comp
  条件: {μ : Measure (α × β)}
  结论: (Kernel.swap α β) ∘ₘ μ = μ.map Prod.swap
  证明: deterministic_comp_eq_map measurable_swap

@[simp]

Depends on / 依赖: deterministic_comp_eq_map, measurable_swap
-/
lemma swap_comp {μ : Measure (α × β)} : (Kernel.swap α β) ∘ₘ μ = μ.map Prod.swap :=
  deterministic_comp_eq_map measurable_swap

@[simp]
/--
lemma `const_comp` / 引理 `const_comp`

English:
lemma const_comp
  given: {ν : Measure β}
  statement: (Kernel.const α ν) ∘ₘ μ = μ Set.univ • ν
  proof: μ.bind_const

中文:
引理 const_comp
  条件: {ν : Measure β}
  结论: (Kernel.const α ν) ∘ₘ μ = μ Set.univ • ν
  证明: μ.bind_const

Depends on / 依赖: bind_const
-/
lemma const_comp {ν : Measure β} : (Kernel.const α ν) ∘ₘ μ = μ Set.univ • ν := μ.bind_const

end MeasureTheory.Measure
