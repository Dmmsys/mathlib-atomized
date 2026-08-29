/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Lemmas relating different ways to compose kernels

This file contains lemmas about the composition of kernels that involve several types of
compositions/products.

## Main statements

* `comp_eq_snd_compProd`: `η ∘ₖ κ = snd (κ ⊗ₖ prodMkLeft X η)`
* `parallelComp_comp_parallelComp`: `(η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ')`

-/

public section


open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {X Y Z T : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  {mZ : MeasurableSpace Z} {mT : MeasurableSpace T}
  {μ : Measure X} {ν : Measure Y} {κ : Kernel X Y} {η : Kernel Z T}

namespace ProbabilityTheory.Kernel

/--
theorem `comp_eq_snd_compProd` / 定理 `comp_eq_snd_compProd`

English:
theorem comp_eq_snd_compProd
  statement: (η : Kernel Y Z) [IsSFiniteKernel η] (κ : Kernel X Y)
  proof: by
  ext a s hs
  rw [comp_apply' _ _ _ hs]; rw [snd_apply' _ _ hs]; rw [compProd_apply (measurable_snd hs)]
  simp [← Set.preimage_comp]

中文:
定理 comp_eq_snd_compProd
  结论: (η : 核 Y Z) [是SFiniteKernel η] (κ : 核 X Y)
  证明: by
  ext a s hs
  rw [comp_apply' _ _ _ hs]; rw [snd_apply' _ _ hs]; rw [compProd_apply (measurable_snd hs)]
  simp [← Set.preimage_comp]

Depends on / 依赖: Set.preimage_comp, compProd_apply, comp_apply, measurable_snd, preimage_comp, snd_apply
-/
theorem comp_eq_snd_compProd (η : Kernel Y Z) [IsSFiniteKernel η] (κ : Kernel X Y)
    [IsSFiniteKernel κ] : η ∘ₖ κ = snd (κ otimesₖ prodMkLeft X η) := by
  ext a s hs
  rw [comp_apply' _ _ _ hs]; rw [snd_apply' _ _ hs]; rw [compProd_apply (measurable_snd hs)]
  simp [← Set.preimage_comp]

/--
lemma `snd_compProd_prodMkLeft` / 引理 `snd_compProd_prodMkLeft`

English:
lemma snd_compProd_prodMkLeft
  proof: (comp_eq_snd_compProd η κ).symm

中文:
引理 snd_compProd_prodMkLeft
  证明: (comp_eq_snd_compProd η κ).symm
-/
@[simp] lemma snd_compProd_prodMkLeft
    (κ : Kernel X Y) (η : Kernel Y Z) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    snd (κ otimesₖ prodMkLeft X η) = η ∘ₖ κ := (comp_eq_snd_compProd η κ).symm

/--
lemma `compProd_prodMkLeft_eq_comp` / 引理 `compProd_prodMkLeft_eq_comp`

English:
lemma compProd_prodMkLeft_eq_comp
  proof: by
  ext a s hs
  rw [comp_eq_snd_compProd]; rw [compProd_apply hs]; rw [snd_apply' _ _ hs]; rw [compProd_apply]
  swap; · exact measurable_snd hs
  simp only [prodMkLeft_apply, ← Set.preimage_comp, Prod.snd_comp_mk, Set.preimage_id_eq, id_eq,
    prod_apply' _ _ _ hs, id_apply]
  congr with b
  rw [lintegral_dirac']
  exact measurable_measure_prodMk_left hs

中文:
引理 compProd_prodMkLeft_eq_comp
  证明: by
  ext a s hs
  rw [comp_eq_snd_compProd]; rw [compProd_apply hs]; rw [snd_apply' _ _ hs]; rw [compProd_apply]
  swap; · exact measurable_snd hs
  simp only [prodMkLeft_apply, ← Set.preimage_comp, Prod.snd_comp_mk, Set.preimage_id_eq, id_eq,
    prod_apply' _ _ _ hs, id_apply]
  congr with b
  rw [lintegral_dirac']
  exact measurable_measure_prodMk_left hs

Depends on / 依赖: Prod.snd_comp_mk, Set.preimage_comp, Set.preimage_id_eq, compProd_apply, comp_eq_snd_compProd, id_apply, id_eq, lintegral_dirac, measurable_measure_prodMk_left, measurable_snd, preimage_comp, preimage_id_eq, prodMkLeft_apply, prod_apply, snd_apply, snd_comp_mk
-/
lemma compProd_prodMkLeft_eq_comp
    (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z) [IsSFiniteKernel η] :
    κ otimesₖ (prodMkLeft X η) = (Kernel.id ×ₖ η) ∘ₖ κ := by
  ext a s hs
  rw [comp_eq_snd_compProd]; rw [compProd_apply hs]; rw [snd_apply' _ _ hs]; rw [compProd_apply]
  swap; · exact measurable_snd hs
  simp only [prodMkLeft_apply, ← Set.preimage_comp, Prod.snd_comp_mk, Set.preimage_id_eq, id_eq,
    prod_apply' _ _ _ hs, id_apply]
  congr with b
  rw [lintegral_dirac']
  exact measurable_measure_prodMk_left hs

/--
lemma `swap_parallelComp` / 引理 `swap_parallelComp`

English:
lemma swap_parallelComp
  statement: swap Y T ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap X Z
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  ext ac s hs
  simp_rw [comp_apply, parallelComp_apply, Measure.bind_apply hs (Kernel.aemeasurable _),
    swap_apply, lintegral_dirac' _ (Kernel.measurable_coe _ hs), parallelComp_apply' hs,
    Prod.fst_swap, Prod.snd_swap]
  rw [MeasureTheory.lintegral_prod_symm]
  swap; · exact ((Kernel.id.measurable_coe hs).comp measurable_swap).aemeasurable
  congr with d
  simp_rw [Prod.swap_prod_mk, Measure.dirac_apply' _ hs, ← Set.indicator_comp_right,
    lintegral_indicator (measurable_prodMk_left hs)]
  simp

中文:
引理 swap_parallelComp
  结论: swap Y T ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap X Z
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  ext ac s hs
  simp_rw [comp_apply, parallelComp_apply, Measure.bind_apply hs (Kernel.aemeasurable _),
    swap_apply, lintegral_dirac' _ (Kernel.measurable_coe _ hs), parallelComp_apply' hs,
    Prod.fst_swap, Prod.snd_swap]
  rw [MeasureTheory.lintegral_prod_symm]
  swap; · exact ((Kernel.id.measurable_coe hs).comp measurable_swap).aemeasurable
  congr with d
  simp_rw [Prod.swap_prod_mk, Measure.dirac_apply' _ hs, ← Set.indicator_comp_right,
    lintegral_indicator (measurable_prodMk_left hs)]
  simp

Depends on / 依赖: IsSFiniteKernel, Kernel, Kernel.aemeasurable, Kernel.id.measurable_coe, Kernel.measurable_coe, Measure, Measure.bind_apply, Measure.dirac_apply, MeasureTheory, MeasureTheory.lintegral_prod_symm, Prod.fst_swap, Prod.snd_swap, Prod.swap_prod_mk, aemeasurable, bind_apply, comp_apply, dirac_apply, fst_swap, lintegral_dirac, lintegral_prod_symm
-/
lemma swap_parallelComp : swap Y T ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap X Z := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  ext ac s hs
  simp_rw [comp_apply, parallelComp_apply, Measure.bind_apply hs (Kernel.aemeasurable _),
    swap_apply, lintegral_dirac' _ (Kernel.measurable_coe _ hs), parallelComp_apply' hs,
    Prod.fst_swap, Prod.snd_swap]
  rw [MeasureTheory.lintegral_prod_symm]
  swap; · exact ((Kernel.id.measurable_coe hs).comp measurable_swap).aemeasurable
  congr with d
  simp_rw [Prod.swap_prod_mk, Measure.dirac_apply' _ hs, ← Set.indicator_comp_right,
    lintegral_indicator (measurable_prodMk_left hs)]
  simp

section ParallelComp

variable {X' Y' Z' : Type*} {mX' : MeasurableSpace X'} {mY' : MeasurableSpace Y'}
  {mZ' : MeasurableSpace Z'}

/--
lemma `parallelComp_id_left_comp_parallelComp` / 引理 `parallelComp_id_left_comp_parallelComp`

English:
lemma parallelComp_id_left_comp_parallelComp
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  ext a s hs
  rw [comp_apply' _ _ _ hs]; rw [parallelComp_apply]; rw [MeasureTheory.lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]
  rw [parallelComp_apply]; rw [Measure.prod_apply hs]
  congr with x
  rw [comp_apply' _ _ _ (measurable_prodMk_left hs)]
  congr with y
  rw [parallelComp_apply' hs]; rw [Kernel.id_apply]; rw [lintegral_dirac' _ (measurable_measure_prodMk_left hs)]

中文:
引理 parallelComp_id_left_comp_parallelComp
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  ext a s hs
  rw [comp_apply' _ _ _ hs]; rw [parallelComp_apply]; rw [MeasureTheory.lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]
  rw [parallelComp_apply]; rw [Measure.prod_apply hs]
  congr with x
  rw [comp_apply' _ _ _ (measurable_prodMk_left hs)]
  congr with y
  rw [parallelComp_apply' hs]; rw [Kernel.id_apply]; rw [lintegral_dirac' _ (measurable_measure_prodMk_left hs)]

Depends on / 依赖: IsSFiniteKernel, Kernel, Kernel.id_apply, Kernel.measurable_coe, Measure, Measure.prod_apply, MeasureTheory, MeasureTheory.lintegral_prod, aemeasurable, comp_apply, id_apply, lintegral_dirac, lintegral_prod, measurable_coe, measurable_measure_prodMk_left, measurable_prodMk_left, parallelComp_apply, prod_apply
-/
lemma parallelComp_id_left_comp_parallelComp
    {η : Kernel X' Z} [IsSFiniteKernel η] {ξ : Kernel Z T} [IsSFiniteKernel ξ] :
    (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  ext a s hs
  rw [comp_apply' _ _ _ hs]; rw [parallelComp_apply]; rw [MeasureTheory.lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]
  rw [parallelComp_apply]; rw [Measure.prod_apply hs]
  congr with x
  rw [comp_apply' _ _ _ (measurable_prodMk_left hs)]
  congr with y
  rw [parallelComp_apply' hs]; rw [Kernel.id_apply]; rw [lintegral_dirac' _ (measurable_measure_prodMk_left hs)]

/--
lemma `parallelComp_id_right_comp_parallelComp` / 引理 `parallelComp_id_right_comp_parallelComp`

English:
lemma parallelComp_id_right_comp_parallelComp
  statement: {η : Kernel X' Z} [IsSFiniteKernel η]
  proof: by
  suffices swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ) by
    calc ξ ∥ₖ Kernel.id ∘ₖ (η ∥ₖ κ)
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ)) := by
      simp_rw [← comp_assoc, swap_swap, id_comp]
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ)) := by rw [this]
    _ = ξ ∘ₖ η ∥ₖ κ := by simp_rw [← comp_assoc, swap_swap, id_comp]
  simp_rw [swap_parallelComp, comp_assoc, swap_parallelComp, ← comp_assoc,
    parallelComp_id_left_comp_parallelComp]

中文:
引理 parallelComp_id_right_comp_parallelComp
  结论: {η : 核 X' Z} [是SFiniteKernel η]
  证明: by
  suffices swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ) by
    calc ξ ∥ₖ Kernel.id ∘ₖ (η ∥ₖ κ)
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ)) := by
      simp_rw [← comp_assoc, swap_swap, id_comp]
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ)) := by rw [this]
    _ = ξ ∘ₖ η ∥ₖ κ := by simp_rw [← comp_assoc, swap_swap, id_comp]
  simp_rw [swap_parallelComp, comp_assoc, swap_parallelComp, ← comp_assoc,
    parallelComp_id_left_comp_parallelComp]

Depends on / 依赖: Kernel, Kernel.id, comp_assoc, id_comp, parallelComp_id_left_comp_parallelComp, simp_rw, swap_parallelComp, swap_swap
-/
lemma parallelComp_id_right_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel η]
    {ξ : Kernel Z T} [IsSFiniteKernel ξ] :
    (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ η) ∥ₖ κ := by
  suffices swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ) by
    calc ξ ∥ₖ Kernel.id ∘ₖ (η ∥ₖ κ)
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ)) := by
      simp_rw [← comp_assoc, swap_swap, id_comp]
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ)) := by rw [this]
    _ = ξ ∘ₖ η ∥ₖ κ := by simp_rw [← comp_assoc, swap_swap, id_comp]
  simp_rw [swap_parallelComp, comp_assoc, swap_parallelComp, ← comp_assoc,
    parallelComp_id_left_comp_parallelComp]

/--
lemma `parallelComp_comp_parallelComp` / 引理 `parallelComp_comp_parallelComp`

English:
lemma parallelComp_comp_parallelComp
  statement: [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η]
  proof: by
  rw [← parallelComp_id_left_comp_parallelComp]; rw [← parallelComp_id_right_comp_parallelComp]; rw [← comp_assoc]; rw [parallelComp_id_left_comp_parallelComp]; rw [comp_id]

中文:
引理 parallelComp_comp_parallelComp
  结论: [是SFiniteKernel κ] {η : 核 Y Z} [是SFiniteKernel η]
  证明: by
  rw [← parallelComp_id_left_comp_parallelComp]; rw [← parallelComp_id_right_comp_parallelComp]; rw [← comp_assoc]; rw [parallelComp_id_left_comp_parallelComp]; rw [comp_id]

Depends on / 依赖: comp_assoc, comp_id, parallelComp_id_left_comp_parallelComp, parallelComp_id_right_comp_parallelComp
-/
lemma parallelComp_comp_parallelComp [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η]
    {κ' : Kernel X' Y'} [IsSFiniteKernel κ'] {η' : Kernel Y' Z'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  rw [← parallelComp_id_left_comp_parallelComp]; rw [← parallelComp_id_right_comp_parallelComp]; rw [← comp_assoc]; rw [parallelComp_id_left_comp_parallelComp]; rw [comp_id]

/--
lemma `parallelComp_comp_prod` / 引理 `parallelComp_comp_prod`

English:
lemma parallelComp_comp_prod
  statement: [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η]
  proof: by
  rw [← parallelComp_comp_copy]; rw [← comp_assoc]; rw [parallelComp_comp_parallelComp]; rw [← parallelComp_comp_copy]

中文:
引理 parallelComp_comp_prod
  结论: [是SFiniteKernel κ] {η : 核 Y Z} [是SFiniteKernel η]
  证明: by
  rw [← parallelComp_comp_copy]; rw [← comp_assoc]; rw [parallelComp_comp_parallelComp]; rw [← parallelComp_comp_copy]

Depends on / 依赖: comp_assoc, parallelComp_comp_copy, parallelComp_comp_parallelComp
-/
lemma parallelComp_comp_prod [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η]
    {κ' : Kernel X Y'} [IsSFiniteKernel κ'] {η' : Kernel Y' Z'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  rw [← parallelComp_comp_copy]; rw [← comp_assoc]; rw [parallelComp_comp_parallelComp]; rw [← parallelComp_comp_copy]

/--
lemma `parallelComp_comm` / 引理 `parallelComp_comm`

English:
lemma parallelComp_comm
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  rw [parallelComp_id_left_comp_parallelComp]; rw [parallelComp_id_right_comp_parallelComp]; rw [comp_id]; rw [comp_id]

中文:
引理 parallelComp_comm
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  rw [parallelComp_id_left_comp_parallelComp]; rw [parallelComp_id_right_comp_parallelComp]; rw [comp_id]; rw [comp_id]

Depends on / 依赖: IsSFiniteKernel, comp_id, parallelComp_id_left_comp_parallelComp, parallelComp_id_right_comp_parallelComp
-/
lemma parallelComp_comm :
    (Kernel.id ∥ₖ κ) ∘ₖ (η ∥ₖ Kernel.id) = (η ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ κ) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  rw [parallelComp_id_left_comp_parallelComp]; rw [parallelComp_id_right_comp_parallelComp]; rw [comp_id]; rw [comp_id]

/--
lemma `id_parallelComp_comp_parallelComp_id` / 引理 `id_parallelComp_comp_parallelComp_id`

English:
lemma id_parallelComp_comp_parallelComp_id
  given: [IsSFiniteKernel κ]
  proof: by
  rw [parallelComp_id_left_comp_parallelComp]
  congr
  exact comp_id κ

中文:
引理 id_parallelComp_comp_parallelComp_id
  条件: [是SFiniteKernel κ]
  证明: by
  rw [parallelComp_id_left_comp_parallelComp]
  congr
  exact comp_id κ

Depends on / 依赖: comp_id, parallelComp_id_left_comp_parallelComp
-/
lemma id_parallelComp_comp_parallelComp_id [IsSFiniteKernel κ] :
    Kernel.id ∥ₖ κ ∘ₖ (η ∥ₖ Kernel.id) = η ∥ₖ κ := by
  rw [parallelComp_id_left_comp_parallelComp]
  congr
  exact comp_id κ

end ParallelComp

end ProbabilityTheory.Kernel
