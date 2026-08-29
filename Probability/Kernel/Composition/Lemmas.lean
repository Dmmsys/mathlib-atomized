/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Lemmas relating different ways to compose measures and kernels

This file contains lemmas about the composition of measures and kernels that do not fit in any of
the other files in this directory, because they involve several types of compositions/products.

-/

public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {μ : Measure α} {ν : Measure β} {κ : Kernel α β}

namespace ProbabilityTheory.Kernel

/--
lemma `prod_prodMkLeft_comp_prod_deterministic` / 引理 `prod_prodMkLeft_comp_prod_deterministic`

English:
lemma prod_prodMkLeft_comp_prod_deterministic
  statement: {β' ε : Type*}
  proof: by
  ext ω s hs
  rw [prod_apply' _ _ _ hs]; rw [comp_apply' _ _ _ hs]; rw [lintegral_prod_deterministic]; rw [lintegral_comp]; rw [lintegral_prod_deterministic]
  · congr with b
    rw [prod_apply' _ _ _ hs]; rw [prodMkLeft_apply]; rw [comp_deterministic_eq_comap]; rw [comap_apply]
  · exact (measurable_measure_prodMk_left hs).lintegral_kernel
  · exact measurable_measure_prodMk_left hs
  · exact Kernel.measurable_coe _ hs

中文:
引理 prod_prodMkLeft_comp_prod_deterministic
  结论: {β' ε : 类型}
  证明: by
  ext ω s hs
  rw [prod_apply' _ _ _ hs]; rw [comp_apply' _ _ _ hs]; rw [lintegral_prod_deterministic]; rw [lintegral_comp]; rw [lintegral_prod_deterministic]
  · congr with b
    rw [prod_apply' _ _ _ hs]; rw [prodMkLeft_apply]; rw [comp_deterministic_eq_comap]; rw [comap_apply]
  · exact (measurable_measure_prodMk_left hs).lintegral_kernel
  · exact measurable_measure_prodMk_left hs
  · exact Kernel.measurable_coe _ hs

Depends on / 依赖: Kernel, Kernel.measurable_coe, comap_apply, comp_apply, comp_deterministic_eq_comap, lintegral_comp, lintegral_kernel, lintegral_prod_deterministic, measurable_coe, measurable_measure_prodMk_left, prodMkLeft_apply, prod_apply
-/
lemma prod_prodMkLeft_comp_prod_deterministic {β' ε : Type*}
    {mβ' : MeasurableSpace β'} {mε : MeasurableSpace ε}
    (κ : Kernel γ β) [IsSFiniteKernel κ] (η : Kernel ε β') [IsSFiniteKernel η]
    (ξ : Kernel (β × ε) δ) [IsSFiniteKernel ξ] {f : γ -> ε} (hf : Measurable f) :
    (ξ ×ₖ η.prodMkLeft β) ∘ₖ (κ ×ₖ deterministic f hf)
      = (ξ ∘ₖ (κ ×ₖ deterministic f hf)) ×ₖ (η ∘ₖ deterministic f hf) := by
  ext ω s hs
  rw [prod_apply' _ _ _ hs]; rw [comp_apply' _ _ _ hs]; rw [lintegral_prod_deterministic]; rw [lintegral_comp]; rw [lintegral_prod_deterministic]
  · congr with b
    rw [prod_apply' _ _ _ hs]; rw [prodMkLeft_apply]; rw [comp_deterministic_eq_comap]; rw [comap_apply]
  · exact (measurable_measure_prodMk_left hs).lintegral_kernel
  · exact measurable_measure_prodMk_left hs
  · exact Kernel.measurable_coe _ hs

/--
lemma `prod_prodMkRight_comp_deterministic_prod` / 引理 `prod_prodMkRight_comp_deterministic_prod`

English:
lemma prod_prodMkRight_comp_deterministic_prod
  statement: {β' ε : Type*}
  proof: by
  ext ω s hs
  rw [prod_apply' _ _ _ hs]; rw [comp_apply' _ _ _ hs]; rw [lintegral_deterministic_prod]; rw [lintegral_comp]; rw [lintegral_deterministic_prod]
  · congr with b
    rw [prod_apply' _ _ _ hs]; rw [prodMkRight_apply]; rw [comp_deterministic_eq_comap]; rw [comap_apply]
  · exact (measurable_measure_prodMk_left hs).lintegral_kernel
  · exact measurable_measure_prodMk_left hs
  · exact Kernel.measurable_coe _ hs

中文:
引理 prod_prodMkRight_comp_deterministic_prod
  结论: {β' ε : 类型}
  证明: by
  ext ω s hs
  rw [prod_apply' _ _ _ hs]; rw [comp_apply' _ _ _ hs]; rw [lintegral_deterministic_prod]; rw [lintegral_comp]; rw [lintegral_deterministic_prod]
  · congr with b
    rw [prod_apply' _ _ _ hs]; rw [prodMkRight_apply]; rw [comp_deterministic_eq_comap]; rw [comap_apply]
  · exact (measurable_measure_prodMk_left hs).lintegral_kernel
  · exact measurable_measure_prodMk_left hs
  · exact Kernel.measurable_coe _ hs

Depends on / 依赖: Kernel, Kernel.measurable_coe, comap_apply, comp_apply, comp_deterministic_eq_comap, lintegral_comp, lintegral_deterministic_prod, lintegral_kernel, measurable_coe, measurable_measure_prodMk_left, prodMkRight_apply, prod_apply
-/
lemma prod_prodMkRight_comp_deterministic_prod {β' ε : Type*}
    {mβ' : MeasurableSpace β'} {mε : MeasurableSpace ε}
    (κ : Kernel γ β) [IsSFiniteKernel κ] (η : Kernel ε β') [IsSFiniteKernel η]
    (ξ : Kernel (ε × β) δ) [IsSFiniteKernel ξ] {f : γ -> ε} (hf : Measurable f) :
    (ξ ×ₖ η.prodMkRight β) ∘ₖ (deterministic f hf ×ₖ κ)
      = (ξ ∘ₖ (deterministic f hf ×ₖ κ)) ×ₖ (η ∘ₖ deterministic f hf) := by
  ext ω s hs
  rw [prod_apply' _ _ _ hs]; rw [comp_apply' _ _ _ hs]; rw [lintegral_deterministic_prod]; rw [lintegral_comp]; rw [lintegral_deterministic_prod]
  · congr with b
    rw [prod_apply' _ _ _ hs]; rw [prodMkRight_apply]; rw [comp_deterministic_eq_comap]; rw [comap_apply]
  · exact (measurable_measure_prodMk_left hs).lintegral_kernel
  · exact measurable_measure_prodMk_left hs
  · exact Kernel.measurable_coe _ hs

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

/--
lemma `compProd_eq_parallelComp_comp_copy_comp` / 引理 `compProd_eq_parallelComp_comp_copy_comp`

English:
lemma compProd_eq_parallelComp_comp_copy_comp
  given: [SFinite μ]
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [FunLike.coe_zero, hκ]
  rw [compProd_eq_comp_prod]; rw [← Kernel.parallelComp_comp_copy]; rw [Measure.comp_assoc]

中文:
引理 compProd_eq_parallelComp_comp_copy_comp
  条件: [SFinite μ]
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [FunLike.coe_zero, hκ]
  rw [compProd_eq_comp_prod]; rw [← Kernel.parallelComp_comp_copy]; rw [Measure.comp_assoc]

Depends on / 依赖: FunLike, FunLike.coe_zero, IsSFiniteKernel, Kernel, Kernel.parallelComp_comp_copy, Measure, Measure.comp_assoc, coe_zero, compProd_eq_comp_prod, comp_assoc, parallelComp_comp_copy
-/
lemma compProd_eq_parallelComp_comp_copy_comp [SFinite μ] :
    μ otimesₘ κ = (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy α ∘ₘ μ := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [FunLike.coe_zero, hκ]
  rw [compProd_eq_comp_prod]; rw [← Kernel.parallelComp_comp_copy]; rw [Measure.comp_assoc]

/--
lemma `prod_comp_right` / 引理 `prod_comp_right`

English:
lemma prod_comp_right
  given: [SFinite ν] {κ : Kernel β γ} [IsSFiniteKernel κ]
  proof: by
  ext s hs
  rw [Measure.prod_apply hs]; rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Measure.bind_apply (measurable_prodMk_left hs) (Kernel.aemeasurable _)]
  rw [MeasureTheory.lintegral_prod]
  swap; · exact (Kernel.measurable_coe _ hs).aemeasurable
  congr with a
  congr with b
  rw [Kernel.parallelComp_apply]; rw [Kernel.id_apply]; rw [Measure.prod_apply hs]; rw [lintegral_dirac']
  exact measurable_measure_prodMk_left hs

中文:
引理 prod_comp_right
  条件: [SFinite ν] {κ : 核 β γ} [是SFiniteKernel κ]
  证明: by
  ext s hs
  rw [Measure.prod_apply hs]; rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Measure.bind_apply (measurable_prodMk_left hs) (Kernel.aemeasurable _)]
  rw [MeasureTheory.lintegral_prod]
  swap; · exact (Kernel.measurable_coe _ hs).aemeasurable
  congr with a
  congr with b
  rw [Kernel.parallelComp_apply]; rw [Kernel.id_apply]; rw [Measure.prod_apply hs]; rw [lintegral_dirac']
  exact measurable_measure_prodMk_left hs

Depends on / 依赖: Kernel, Kernel.aemeasurable, Kernel.id_apply, Kernel.measurable_coe, Kernel.parallelComp_apply, Measure, Measure.bind_apply, Measure.prod_apply, MeasureTheory, MeasureTheory.lintegral_prod, aemeasurable, bind_apply, id_apply, lintegral_dirac, lintegral_prod, measurable_coe, measurable_measure_prodMk_left, measurable_prodMk_left, parallelComp_apply, prod_apply
-/
lemma prod_comp_right [SFinite ν] {κ : Kernel β γ} [IsSFiniteKernel κ] :
    μ.prod (κ ∘ₘ ν) = (Kernel.id ∥ₖ κ) ∘ₘ (μ.prod ν) := by
  ext s hs
  rw [Measure.prod_apply hs]; rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Measure.bind_apply (measurable_prodMk_left hs) (Kernel.aemeasurable _)]
  rw [MeasureTheory.lintegral_prod]
  swap; · exact (Kernel.measurable_coe _ hs).aemeasurable
  congr with a
  congr with b
  rw [Kernel.parallelComp_apply]; rw [Kernel.id_apply]; rw [Measure.prod_apply hs]; rw [lintegral_dirac']
  exact measurable_measure_prodMk_left hs

/--
lemma `prod_comp_left` / 引理 `prod_comp_left`

English:
lemma prod_comp_left
  given: [SFinite μ] [SFinite ν] {κ : Kernel α γ} [IsSFiniteKernel κ]
  proof: by
  have h1 : (κ ∘ₘ μ).prod ν = (ν.prod (κ ∘ₘ μ)).map Prod.swap := by rw [Measure.prod_swap]
  have h2 : (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
    calc (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν)
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((ν.prod μ).map Prod.swap) := by rw [Measure.prod_swap]
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((Kernel.swap _ _) ∘ₘ (ν.prod μ)) := by
      rw [Kernel.swap]; rw [Measure.deterministic_comp_eq_map]
    _ = (Kernel.swap _ _) ∘ₘ ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)) := by
      rw [Measure.comp_assoc]; rw [Measure.comp_assoc]; rw [Kernel.swap_parallelComp]
    _ = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
      rw [Kernel.swap]; rw [Measure.deterministic_comp_eq_map]
  rw [← Measure.prod_comp_right]; rw [← h1] at h2
  exact h2.symm

中文:
引理 prod_comp_left
  条件: [SFinite μ] [SFinite ν] {κ : 核 α γ} [是SFiniteKernel κ]
  证明: by
  have h1 : (κ ∘ₘ μ).prod ν = (ν.prod (κ ∘ₘ μ)).map Prod.swap := by rw [Measure.prod_swap]
  have h2 : (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
    calc (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν)
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((ν.prod μ).map Prod.swap) := by rw [Measure.prod_swap]
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((Kernel.swap _ _) ∘ₘ (ν.prod μ)) := by
      rw [Kernel.swap]; rw [Measure.deterministic_comp_eq_map]
    _ = (Kernel.swap _ _) ∘ₘ ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)) := by
      rw [Measure.comp_assoc]; rw [Measure.comp_assoc]; rw [Kernel.swap_parallelComp]
    _ = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
      rw [Kernel.swap]; rw [Measure.deterministic_comp_eq_map]
  rw [← Measure.prod_comp_right]; rw [← h1] at h2
  exact h2.symm

Depends on / 依赖: Kernel, Kernel.id, Kernel.swap, Measure, Measure.deterministic_comp_eq_map, Measure.prod_swap, Prod.swap, deterministic_comp_eq_map, prod_swap
-/
lemma prod_comp_left [SFinite μ] [SFinite ν] {κ : Kernel α γ} [IsSFiniteKernel κ] :
    (κ ∘ₘ μ).prod ν = (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) := by
  have h1 : (κ ∘ₘ μ).prod ν = (ν.prod (κ ∘ₘ μ)).map Prod.swap := by rw [Measure.prod_swap]
  have h2 : (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
    calc (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν)
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((ν.prod μ).map Prod.swap) := by rw [Measure.prod_swap]
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((Kernel.swap _ _) ∘ₘ (ν.prod μ)) := by
      rw [Kernel.swap]; rw [Measure.deterministic_comp_eq_map]
    _ = (Kernel.swap _ _) ∘ₘ ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)) := by
      rw [Measure.comp_assoc]; rw [Measure.comp_assoc]; rw [Kernel.swap_parallelComp]
    _ = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
      rw [Kernel.swap]; rw [Measure.deterministic_comp_eq_map]
  rw [← Measure.prod_comp_right]; rw [← h1] at h2
  exact h2.symm

/--
lemma `parallelComp_comp_compProd` / 引理 `parallelComp_comp_compProd`

English:
lemma parallelComp_comp_compProd
  given: [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η]
  proof: by
  by_cases hμ : SFinite μ
  swap; · simp [hμ]
  rw [Measure.compProd_eq_comp_prod]; rw [Measure.compProd_eq_comp_prod]; rw [Measure.comp_assoc]; rw [Kernel.parallelComp_comp_prod]; rw [Kernel.id_comp]

中文:
引理 parallelComp_comp_compProd
  条件: [是SFiniteKernel κ] {η : 核 β γ} [是SFiniteKernel η]
  证明: by
  by_cases hμ : SFinite μ
  swap; · simp [hμ]
  rw [Measure.compProd_eq_comp_prod]; rw [Measure.compProd_eq_comp_prod]; rw [Measure.comp_assoc]; rw [Kernel.parallelComp_comp_prod]; rw [Kernel.id_comp]

Depends on / 依赖: Kernel, Kernel.id_comp, Kernel.parallelComp_comp_prod, Measure, Measure.compProd_eq_comp_prod, Measure.comp_assoc, SFinite, compProd_eq_comp_prod, comp_assoc, id_comp, parallelComp_comp_prod
-/
lemma parallelComp_comp_compProd [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ η) ∘ₘ (μ otimesₘ κ) = μ otimesₘ (η ∘ₖ κ) := by
  by_cases hμ : SFinite μ
  swap; · simp [hμ]
  rw [Measure.compProd_eq_comp_prod]; rw [Measure.compProd_eq_comp_prod]; rw [Measure.comp_assoc]; rw [Kernel.parallelComp_comp_prod]; rw [Kernel.id_comp]

/--
lemma `compProd_map` / 引理 `compProd_map`

English:
lemma compProd_map
  given: [SFinite μ] [IsSFiniteKernel κ] {f : β -> γ} (hf : Measurable f)
  proof: by
  calc μ otimesₘ (κ.map f)
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ×ₖ κ) ∘ₘ μ := by
    rw [comp_assoc]; rw [Kernel.parallelComp_comp_prod]; rw [compProd_eq_comp_prod]; rw [Kernel.id_comp]; rw [Kernel.deterministic_comp_eq_map]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (μ otimesₘ κ) := by rw [compProd_eq_comp_prod]
  _ = (μ otimesₘ κ).map (Prod.map id f) := by
    rw [Kernel.id]; rw [Kernel.deterministic_parallelComp_deterministic]; rw [deterministic_comp_eq_map]

中文:
引理 compProd_map
  条件: [SFinite μ] [是SFiniteKernel κ] {f : β -> γ} (hf : 可测 f)
  证明: by
  calc μ otimesₘ (κ.map f)
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ×ₖ κ) ∘ₘ μ := by
    rw [comp_assoc]; rw [Kernel.parallelComp_comp_prod]; rw [compProd_eq_comp_prod]; rw [Kernel.id_comp]; rw [Kernel.deterministic_comp_eq_map]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (μ otimesₘ κ) := by rw [compProd_eq_comp_prod]
  _ = (μ otimesₘ κ).map (Prod.map id f) := by
    rw [Kernel.id]; rw [Kernel.deterministic_parallelComp_deterministic]; rw [deterministic_comp_eq_map]

Depends on / 依赖: Kernel, Kernel.deterministic, Kernel.deterministic_comp_eq_map, Kernel.deterministic_parallelComp_deterministic, Kernel.id, Kernel.id_comp, Kernel.parallelComp_comp_prod, Prod.map, compProd_eq_comp_prod, comp_assoc, deterministic, deterministic_comp_eq_map, deterministic_parallelComp_deterministic, id_comp, parallelComp_comp_prod
-/
lemma compProd_map [SFinite μ] [IsSFiniteKernel κ] {f : β -> γ} (hf : Measurable f) :
    μ otimesₘ (κ.map f) = (μ otimesₘ κ).map (Prod.map id f) := by
  calc μ otimesₘ (κ.map f)
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ×ₖ κ) ∘ₘ μ := by
    rw [comp_assoc]; rw [Kernel.parallelComp_comp_prod]; rw [compProd_eq_comp_prod]; rw [Kernel.id_comp]; rw [Kernel.deterministic_comp_eq_map]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (μ otimesₘ κ) := by rw [compProd_eq_comp_prod]
  _ = (μ otimesₘ κ).map (Prod.map id f) := by
    rw [Kernel.id]; rw [Kernel.deterministic_parallelComp_deterministic]; rw [deterministic_comp_eq_map]

end MeasureTheory.Measure
