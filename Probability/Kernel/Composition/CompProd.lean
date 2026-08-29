/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Composition-product of kernels

We define the composition-product `κ ⊗ₖ η` of two s-finite kernels `κ : Kernel α β` and
`η : Kernel (α × β) γ`, a kernel from `α` to `β × γ`.

A note on names:
The composition-product `Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)` is named composition in
[kallenberg2021] and product on the wikipedia article on transition kernels.
Most papers studying categories of kernels call composition the map we call composition. We adopt
that convention because it fits better with the use of the name `comp` elsewhere in mathlib.

## Main definitions

* `compProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ)`: composition-product of 2
  s-finite kernels. We define a notation `κ ⊗ₖ η = compProd κ η`.
  `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`

## Main statements

* `lintegral_compProd`: Lebesgue integral of a function against a composition-product of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by composition-product.

## Notation

* `κ ⊗ₖ η = ProbabilityTheory.Kernel.compProd κ η`

-/

@[expose] public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

section CompositionProduct

/-!
### Composition-Product of kernels

We define a kernel composition-product
`compProd : Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)`.
-/

variable {s : Set (β × γ)}

/-- Composition-Product of kernels. For s-finite kernels, it satisfies
`∫⁻ bc, f bc ∂(compProd κ η a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`
(see `ProbabilityTheory.Kernel.lintegral_compProd`).
If either of the kernels is not s-finite, `compProd` is given the junk value 0. -/
noncomputable irreducible_def compProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ) :=
  swap γ β ∘ₖ (η ∥ₖ Kernel.id)
    ∘ₖ deterministic MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _)
    ∘ₖ (Kernel.id ∥ₖ copy β) ∘ₖ (Kernel.id ∥ₖ κ) ∘ₖ copy α

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " otimesₖ " => ProbabilityTheory.Kernel.compProd

@[simp]
/--
theorem `compProd_of_not_isSFiniteKernel_left` / 定理 `compProd_of_not_isSFiniteKernel_left`

English:
theorem compProd_of_not_isSFiniteKernel_left
  statement: (κ : Kernel α β) (η : Kernel (α × β) γ)
  proof: by
  simp [compProd, h]

@[simp]

中文:
定理 compProd_of_not_isSFiniteKernel_left
  结论: (κ : 核 α β) (η : 核 (α × β) γ)
  证明: by
  simp [compProd, h]

@[simp]

Depends on / 依赖: compProd
-/
theorem compProd_of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ)
    (h : ¬ IsSFiniteKernel κ) :
    κ otimesₖ η = 0 := by
  simp [compProd, h]

@[simp]
/--
theorem `compProd_of_not_isSFiniteKernel_right` / 定理 `compProd_of_not_isSFiniteKernel_right`

English:
theorem compProd_of_not_isSFiniteKernel_right
  statement: (κ : Kernel α β) (η : Kernel (α × β) γ)
  proof: by
  simp [compProd, h]

中文:
定理 compProd_of_not_isSFiniteKernel_right
  结论: (κ : 核 α β) (η : 核 (α × β) γ)
  证明: by
  simp [compProd, h]

Depends on / 依赖: compProd
-/
theorem compProd_of_not_isSFiniteKernel_right (κ : Kernel α β) (η : Kernel (α × β) γ)
    (h : ¬ IsSFiniteKernel η) :
    κ otimesₖ η = 0 := by
  simp [compProd, h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `compProd_apply` / 定理 `compProd_apply`

English:
theorem compProd_apply
  statement: (hs : MeasurableSet s) (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  rw [compProd]; rw [comp_apply]; rw [copy_apply]; rw [Measure.dirac_bind (by fun_prop)]; rw [comp_apply]; rw [parallelComp_apply]; rw [Kernel.id_apply]; rw [Measure.bind_apply hs (by fun_prop)]; rw [lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]; rw [lintegral_dirac']
  swap
  · suffices Measurable fun p : α × β =>
      (swap γ β ∘ₖ (η ∥ₖ Kernel.id)
        ∘ₖ deterministic MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _)
        ∘ₖ (Kernel.id ∥ₖ copy β)) p s by fun_prop
    exact Kernel.measurable_coe _ hs
  congr with b
  rw [comp_apply]; rw [parallelComp_apply]; rw [Kernel.id_apply]; rw [copy_apply]; rw [Measure.dirac_prod_dirac]; rw [Measure.dirac_bind (by fun_prop)]; rw [comp_apply]; rw [deterministic_apply (by fun_prop)]; rw [Measure.dirac_bind (by fun_prop)]; rw [comp_apply]
  simp only [MeasurableEquiv.prodAssoc, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
    Equiv.prodAssoc_symm_apply]
  rw [parallelComp_apply]; rw [Kernel.id_apply]; rw [Measure.bind_apply hs (by fun_prop)]; rw [lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]
  classical
  have h_int x : ∫⁻ y, swap γ β (x, y) s ∂Measure.dirac b = (Prod.mk b ⁻¹' s).indicator 1 x := by
    rw [lintegral_dirac']
    · simp [swap_apply' _ hs, Set.indicator_apply]
    · simpa [swap_apply' _ hs, Prod.swap_prod_mk] using!
        measurable_const.indicator (measurable_prodMk_right hs)
  simp_rw [h_int]
  rw [lintegral_indicator_one]
  exact measurable_prodMk_left hs

中文:
定理 compProd_apply
  结论: (hs : 可测集 s) (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  rw [compProd]; rw [comp_apply]; rw [copy_apply]; rw [Measure.dirac_bind (by fun_prop)]; rw [comp_apply]; rw [parallelComp_apply]; rw [Kernel.id_apply]; rw [Measure.bind_apply hs (by fun_prop)]; rw [lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]; rw [lintegral_dirac']
  swap
  · suffices Measurable fun p : α × β =>
      (swap γ β ∘ₖ (η ∥ₖ Kernel.id)
        ∘ₖ deterministic MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _)
        ∘ₖ (Kernel.id ∥ₖ copy β)) p s by fun_prop
    exact Kernel.measurable_coe _ hs
  congr with b
  rw [comp_apply]; rw [parallelComp_apply]; rw [Kernel.id_apply]; rw [copy_apply]; rw [Measure.dirac_prod_dirac]; rw [Measure.dirac_bind (by fun_prop)]; rw [comp_apply]; rw [deterministic_apply (by fun_prop)]; rw [Measure.dirac_bind (by fun_prop)]; rw [comp_apply]
  simp only [MeasurableEquiv.prodAssoc, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
    Equiv.prodAssoc_symm_apply]
  rw [parallelComp_apply]; rw [Kernel.id_apply]; rw [Measure.bind_apply hs (by fun_prop)]; rw [lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]
  classical
  have h_int x : ∫⁻ y, swap γ β (x, y) s ∂Measure.dirac b = (Prod.mk b ⁻¹' s).indicator 1 x := by
    rw [lintegral_dirac']
    · simp [swap_apply' _ hs, Set.indicator_apply]
    · simpa [swap_apply' _ hs, Prod.swap_prod_mk] using!
        measurable_const.indicator (measurable_prodMk_right hs)
  simp_rw [h_int]
  rw [lintegral_indicator_one]
  exact measurable_prodMk_left hs

Depends on / 依赖: Kernel, Kernel.id, Kernel.id_apply, Kernel.measurab, Kernel.measurable_coe, Measurable, MeasurableEquiv, MeasurableEquiv.measurable, MeasurableEquiv.prodAssoc.symm, Measure, Measure.bind_apply, Measure.dirac_bind, aemeasurable, bind_apply, compProd, comp_apply, copy_apply, deterministic, dirac_bind, fun_prop
-/
theorem compProd_apply (hs : MeasurableSet s) (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) :
    (κ otimesₖ η) a s = ∫⁻ b, η (a, b) (Prod.mk b ⁻¹' s) ∂κ a := by
  rw [compProd]; rw [comp_apply]; rw [copy_apply]; rw [Measure.dirac_bind (by fun_prop)]; rw [comp_apply]; rw [parallelComp_apply]; rw [Kernel.id_apply]; rw [Measure.bind_apply hs (by fun_prop)]; rw [lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]; rw [lintegral_dirac']
  swap
  · suffices Measurable fun p : α × β =>
      (swap γ β ∘ₖ (η ∥ₖ Kernel.id)
        ∘ₖ deterministic MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _)
        ∘ₖ (Kernel.id ∥ₖ copy β)) p s by fun_prop
    exact Kernel.measurable_coe _ hs
  congr with b
  rw [comp_apply]; rw [parallelComp_apply]; rw [Kernel.id_apply]; rw [copy_apply]; rw [Measure.dirac_prod_dirac]; rw [Measure.dirac_bind (by fun_prop)]; rw [comp_apply]; rw [deterministic_apply (by fun_prop)]; rw [Measure.dirac_bind (by fun_prop)]; rw [comp_apply]
  simp only [MeasurableEquiv.prodAssoc, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
    Equiv.prodAssoc_symm_apply]
  rw [parallelComp_apply]; rw [Kernel.id_apply]; rw [Measure.bind_apply hs (by fun_prop)]; rw [lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]
  classical
  have h_int x : ∫⁻ y, swap γ β (x, y) s ∂Measure.dirac b = (Prod.mk b ⁻¹' s).indicator 1 x := by
    rw [lintegral_dirac']
    · simp [swap_apply' _ hs, Set.indicator_apply]
    · simpa [swap_apply' _ hs, Prod.swap_prod_mk] using!
        measurable_const.indicator (measurable_prodMk_right hs)
  simp_rw [h_int]
  rw [lintegral_indicator_one]
  exact measurable_prodMk_left hs

/--
theorem `le_compProd_apply` / 定理 `le_compProd_apply`

English:
theorem le_compProd_apply
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
  proof: calc
    ∫⁻ b, η (a, b) {c | (b, c) in s} ∂κ a <=
        ∫⁻ b, η (a, b) {c | (b, c) in toMeasurable ((κ otimesₖ η) a) s} ∂κ a :=
      lintegral_mono fun _ => measure_mono fun _ h_mem => subset_toMeasurable _ _ h_mem
    _ = (κ otimesₖ η) a (toMeasurable ((κ otimesₖ η) a) s) :=
      (compProd_apply (measurableSet_toMeasurable _ _) κ η a).symm
    _ = (κ otimesₖ η) a s := measure_toMeasurable s

@[simp]

中文:
定理 le_compProd_apply
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 (α × β) γ)
  证明: calc
    ∫⁻ b, η (a, b) {c | (b, c) in s} ∂κ a <=
        ∫⁻ b, η (a, b) {c | (b, c) in toMeasurable ((κ otimesₖ η) a) s} ∂κ a :=
      lintegral_mono fun _ => measure_mono fun _ h_mem => subset_toMeasurable _ _ h_mem
    _ = (κ otimesₖ η) a (toMeasurable ((κ otimesₖ η) a) s) :=
      (compProd_apply (measurableSet_toMeasurable _ _) κ η a).symm
    _ = (κ otimesₖ η) a s := measure_toMeasurable s

@[simp]

Depends on / 依赖: compProd_apply, h_mem, lintegral_mono, measurableSet_toMeasurable, measure_mono, measure_toMeasurable, subset_toMeasurable, toMeasurable
-/
theorem le_compProd_apply (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (s : Set (β × γ)) :
    ∫⁻ b, η (a, b) {c | (b, c) in s} ∂κ a <= (κ otimesₖ η) a s :=
  calc
    ∫⁻ b, η (a, b) {c | (b, c) in s} ∂κ a <=
        ∫⁻ b, η (a, b) {c | (b, c) in toMeasurable ((κ otimesₖ η) a) s} ∂κ a :=
      lintegral_mono fun _ => measure_mono fun _ h_mem => subset_toMeasurable _ _ h_mem
    _ = (κ otimesₖ η) a (toMeasurable ((κ otimesₖ η) a) s) :=
      (compProd_apply (measurableSet_toMeasurable _ _) κ η a).symm
    _ = (κ otimesₖ η) a s := measure_toMeasurable s

@[simp]
/--
lemma `compProd_apply_univ` / 引理 `compProd_apply_univ`

English:
lemma compProd_apply_univ
  statement: {κ : Kernel α β} {η : Kernel (α × β) γ}
  proof: by
  rw [compProd_apply MeasurableSet.univ]
  simp

中文:
引理 compProd_apply_univ
  结论: {κ : 核 α β} {η : 核 (α × β) γ}
  证明: by
  rw [compProd_apply MeasurableSet.univ]
  simp

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, compProd_apply
-/
lemma compProd_apply_univ {κ : Kernel α β} {η : Kernel (α × β) γ}
    [IsSFiniteKernel κ] [IsMarkovKernel η] {a : α} :
    (κ otimesₖ η) a Set.univ = κ a Set.univ := by
  rw [compProd_apply MeasurableSet.univ]
  simp

/--
lemma `compProd_apply_prod` / 引理 `compProd_apply_prod`

English:
lemma compProd_apply_prod
  statement: {κ : Kernel α β} {η : Kernel (α × β) γ}
  proof: by
  rw [compProd_apply (hs.prod ht)]; rw [← lintegral_indicator hs]
  congr with a
  by_cases ha : a in s <;> simp [ha]

中文:
引理 compProd_apply_prod
  结论: {κ : 核 α β} {η : 核 (α × β) γ}
  证明: by
  rw [compProd_apply (hs.prod ht)]; rw [← lintegral_indicator hs]
  congr with a
  by_cases ha : a in s <;> simp [ha]

Depends on / 依赖: compProd_apply, hs.prod, lintegral_indicator
-/
lemma compProd_apply_prod {κ : Kernel α β} {η : Kernel (α × β) γ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] {a : α}
    {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (κ otimesₖ η) a (s ×ˢ t) = ∫⁻ b in s, η (a, b) t ∂(κ a) := by
  rw [compProd_apply (hs.prod ht)]; rw [← lintegral_indicator hs]
  congr with a
  by_cases ha : a in s <;> simp [ha]

/--
lemma `compProd_congr` / 引理 `compProd_congr`

English:
lemma compProd_congr
  statement: {κ : Kernel α β} {η η' : Kernel (α × β) γ}
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp_rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
  ext a s hs
  rw [compProd_apply hs]; rw [compProd_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [h a] with b hb using by rw [hb]

@[simp]

中文:
引理 compProd_congr
  结论: {κ : 核 α β} {η η' : 核 (α × β) γ}
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp_rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
  ext a s hs
  rw [compProd_apply hs]; rw [compProd_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [h a] with b hb using by rw [hb]

@[simp]

Depends on / 依赖: IsSFiniteKernel, compProd_apply, compProd_of_not_isSFiniteKernel_left, filter_upwards, lintegral_congr_ae, simp_rw
-/
lemma compProd_congr {κ : Kernel α β} {η η' : Kernel (α × β) γ}
    [IsSFiniteKernel η] [IsSFiniteKernel η'] (h : forall a, forallᵐ b ∂(κ a), η (a, b) = η' (a, b)) :
    κ otimesₖ η = κ otimesₖ η' := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp_rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
  ext a s hs
  rw [compProd_apply hs]; rw [compProd_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [h a] with b hb using by rw [hb]

@[simp]
/--
lemma `compProd_zero_left` / 引理 `compProd_zero_left`

English:
lemma compProd_zero_left
  given: (κ : Kernel (α × β) γ)
  proof: by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [Kernel.compProd_apply hs]
    simp
  · rw [Kernel.compProd_of_not_isSFiniteKernel_right _ _ h]

@[simp]

中文:
引理 compProd_zero_left
  条件: (κ : 核 (α × β) γ)
  证明: by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [Kernel.compProd_apply hs]
    simp
  · rw [Kernel.compProd_of_not_isSFiniteKernel_right _ _ h]

@[simp]

Depends on / 依赖: IsSFiniteKernel, Kernel, Kernel.compProd_apply, Kernel.compProd_of_not_isSFiniteKernel_right, compProd_apply, compProd_of_not_isSFiniteKernel_right
-/
lemma compProd_zero_left (κ : Kernel (α × β) γ) :
    (0 : Kernel α β) otimesₖ κ = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [Kernel.compProd_apply hs]
    simp
  · rw [Kernel.compProd_of_not_isSFiniteKernel_right _ _ h]

@[simp]
/--
lemma `compProd_zero_right` / 引理 `compProd_zero_right`

English:
lemma compProd_zero_right
  given: (κ : Kernel α β) (γ : Type*) {mγ : MeasurableSpace γ}
  proof: by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [Kernel.compProd_apply hs]
    simp
  · rw [Kernel.compProd_of_not_isSFiniteKernel_left _ _ h]

中文:
引理 compProd_zero_right
  条件: (κ : 核 α β) (γ : 类型) {mγ : 可测空间 γ}
  证明: by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [Kernel.compProd_apply hs]
    simp
  · rw [Kernel.compProd_of_not_isSFiniteKernel_left _ _ h]

Depends on / 依赖: Algebra, CommSemiring, IsSFiniteKernel, Kernel, Kernel.compProd_apply, Kernel.compProd_of_not_isSFiniteKernel_left, algebraPolynomial, compProd_apply, compProd_of_not_isSFiniteKernel_left
-/
lemma compProd_zero_right (κ : Kernel α β) (γ : Type*) {mγ : MeasurableSpace γ} :
    κ otimesₖ (0 : Kernel (α × β) γ) = 0 := by
  by_cases h : IsSFiniteKernel κ
  · ext a s hs
    rw [Kernel.compProd_apply hs]
    simp
  · rw [Kernel.compProd_of_not_isSFiniteKernel_left _ _ h]

/--
lemma `compProd_eq_zero_iff` / 引理 `compProd_eq_zero_iff`

English:
lemma compProd_eq_zero_iff
  statement: {κ : Kernel α β} {η : Kernel (α × β) γ}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp_rw [← Measure.measure_univ_eq_zero]
    refine fun a => (lintegral_eq_zero_iff ?_).mp ?_
    · exact (η.measurable_coe .univ).comp measurable_prodMk_left
    · rw [← setLIntegral_univ, ← Kernel.compProd_apply_prod .univ .univ, h]
      simp
  · rw [← Kernel.compProd_zero_right κ]
    exact Kernel.compProd_congr h

中文:
引理 compProd_eq_zero_iff
  结论: {κ : 核 α β} {η : 核 (α × β) γ}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp_rw [← Measure.measure_univ_eq_zero]
    refine fun a => (lintegral_eq_zero_iff ?_).mp ?_
    · exact (η.measurable_coe .univ).comp measurable_prodMk_left
    · rw [← setLIntegral_univ, ← Kernel.compProd_apply_prod .univ .univ, h]
      simp
  · rw [← Kernel.compProd_zero_right κ]
    exact Kernel.compProd_congr h

Depends on / 依赖: Kernel, Kernel.compProd_apply_prod, Kernel.compProd_congr, Kernel.compProd_zero_right, Measure, Measure.measure_univ_eq_zero, compProd_apply_prod, compProd_congr, compProd_zero_right, lintegral_eq_zero_iff, measurable_coe, measurable_prodMk_left, measure_univ_eq_zero, setLIntegral_univ, simp_rw
-/
lemma compProd_eq_zero_iff {κ : Kernel α β} {η : Kernel (α × β) γ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ otimesₖ η = 0 ↔ forall a, forallᵐ b ∂(κ a), η (a, b) = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp_rw [← Measure.measure_univ_eq_zero]
    refine fun a => (lintegral_eq_zero_iff ?_).mp ?_
    · exact (η.measurable_coe .univ).comp measurable_prodMk_left
    · rw [← setLIntegral_univ, ← Kernel.compProd_apply_prod .univ .univ, h]
      simp
  · rw [← Kernel.compProd_zero_right κ]
    exact Kernel.compProd_congr h

/--
lemma `compProd_preimage_fst` / 引理 `compProd_preimage_fst`

English:
lemma compProd_preimage_fst
  statement: {s : Set β} (hs : MeasurableSet s) (κ : Kernel α β)
  proof: by
  simp_rw [compProd_apply (measurable_fst hs), ← Set.preimage_comp, Prod.fst_comp_mk, Set.preimage,
    Function.const_apply]
  have : forall b : β, η (x, b) {_c | b in s} = s.indicator (fun _ => 1) b := by
    intro b
    by_cases hb : b in s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator_const hs]; rw [one_mul]

中文:
引理 compProd_preimage_fst
  结论: {s : 集合 β} (hs : 可测集 s) (κ : 核 α β)
  证明: by
  simp_rw [compProd_apply (measurable_fst hs), ← Set.preimage_comp, Prod.fst_comp_mk, Set.preimage,
    Function.const_apply]
  have : forall b : β, η (x, b) {_c | b in s} = s.indicator (fun _ => 1) b := by
    intro b
    by_cases hb : b in s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator_const hs]; rw [one_mul]

Depends on / 依赖: Function, Function.const_apply, Prod.fst_comp_mk, Set.preimage, Set.preimage_comp, compProd_apply, const_apply, fst_comp_mk, indicator, lintegral_indicator_const, measurable_fst, one_mul, preimage, preimage_comp, s.indicator, simp_rw
-/
lemma compProd_preimage_fst {s : Set β} (hs : MeasurableSet s) (κ : Kernel α β)
    (η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] (x : α) :
    (κ otimesₖ η) x (Prod.fst ⁻¹' s) = κ x s := by
  simp_rw [compProd_apply (measurable_fst hs), ← Set.preimage_comp, Prod.fst_comp_mk, Set.preimage,
    Function.const_apply]
  have : forall b : β, η (x, b) {_c | b in s} = s.indicator (fun _ => 1) b := by
    intro b
    by_cases hb : b in s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator_const hs]; rw [one_mul]

/--
lemma `compProd_deterministic_apply` / 引理 `compProd_deterministic_apply`

English:
lemma compProd_deterministic_apply
  statement: [MeasurableSingletonClass γ] {f : α × β -> γ} (hf : Measurable f)
  proof: by
  classical
  simp only [deterministic_apply, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, compProd_apply hs]
  let t := {b | (b, f (x, b)) in s}
  have ht : MeasurableSet t := (measurable_id.prodMk (hf.comp measurable_prodMk_left)) hs
  rw [← lintegral_add_compl _ ht]
  convert! add_zero _
  · suffices forall b in tᶜ, (if f (x, b) in Prod.mk b ⁻¹' s then (1 : Real>=0∞) else 0) = 0 by
      rw [setLIntegral_congr_fun ht.compl this]; rw [lintegral_zero]
    intro b hb
    simp only [t, Set.mem_compl_iff, Set.mem_ofPred_eq] at hb
    simp [hb]
  · suffices forall b in t, (if f (x, b) in Prod.mk b ⁻¹' s then (1 : Real>=0∞) else 0) = 1 by
      rw [setLIntegral_congr_fun ht this]; rw [setLIntegral_one]
    intro b hb
    simp only [t, Set.mem_ofPred_eq] at hb
    simp [hb]

中文:
引理 compProd_deterministic_apply
  结论: [MeasurableSingleton类 γ] {f : α × β -> γ} (hf : 可测 f)
  证明: by
  classical
  simp only [deterministic_apply, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, compProd_apply hs]
  let t := {b | (b, f (x, b)) in s}
  have ht : MeasurableSet t := (measurable_id.prodMk (hf.comp measurable_prodMk_left)) hs
  rw [← lintegral_add_compl _ ht]
  convert! add_zero _
  · suffices forall b in tᶜ, (if f (x, b) in Prod.mk b ⁻¹' s then (1 : Real>=0∞) else 0) = 0 by
      rw [setLIntegral_congr_fun ht.compl this]; rw [lintegral_zero]
    intro b hb
    simp only [t, Set.mem_compl_iff, Set.mem_ofPred_eq] at hb
    simp [hb]
  · suffices forall b in t, (if f (x, b) in Prod.mk b ⁻¹' s then (1 : Real>=0∞) else 0) = 1 by
      rw [setLIntegral_congr_fun ht this]; rw [setLIntegral_one]
    intro b hb
    simp only [t, Set.mem_ofPred_eq] at hb
    simp [hb]

Depends on / 依赖: MeasurableSet, Measure, Measure.dirac_apply, Pi.one_apply, Prod.mk, Set.indicator_apply, Set.m, Set.mem_compl_iff, add_zero, classical, compProd_apply, convert, deterministic_apply, dirac_apply, hf.comp, ht.compl, indicator_apply, lintegral_add_compl, lintegral_zero, measurable_id
-/
lemma compProd_deterministic_apply [MeasurableSingletonClass γ] {f : α × β -> γ} (hf : Measurable f)
    {s : Set (β × γ)} (hs : MeasurableSet s) (κ : Kernel α β) [IsSFiniteKernel κ] (x : α) :
    (κ otimesₖ deterministic f hf) x s = κ x {b | (b, f (x, b)) in s} := by
  classical
  simp only [deterministic_apply, Measure.dirac_apply,
    Set.indicator_apply, Pi.one_apply, compProd_apply hs]
  let t := {b | (b, f (x, b)) in s}
  have ht : MeasurableSet t := (measurable_id.prodMk (hf.comp measurable_prodMk_left)) hs
  rw [← lintegral_add_compl _ ht]
  convert! add_zero _
  · suffices forall b in tᶜ, (if f (x, b) in Prod.mk b ⁻¹' s then (1 : Real>=0∞) else 0) = 0 by
      rw [setLIntegral_congr_fun ht.compl this]; rw [lintegral_zero]
    intro b hb
    simp only [t, Set.mem_compl_iff, Set.mem_ofPred_eq] at hb
    simp [hb]
  · suffices forall b in t, (if f (x, b) in Prod.mk b ⁻¹' s then (1 : Real>=0∞) else 0) = 1 by
      rw [setLIntegral_congr_fun ht this]; rw [setLIntegral_one]
    intro b hb
    simp only [t, Set.mem_ofPred_eq] at hb
    simp [hb]

section Ae

/-! ### `ae` filter of the composition-product -/


variable {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η] {a : α}

/--
theorem `ae_kernel_lt_top` / 定理 `ae_kernel_lt_top`

English:
theorem ae_kernel_lt_top
  given: (a : α) (h2s : (κ otimesₖ η) a s != ∞)
  proof: by
  let t := toMeasurable ((κ otimesₖ η) a) s
  have : forall b : β, η (a, b) (Prod.mk b ⁻¹' s) <= η (a, b) (Prod.mk b ⁻¹' t) := fun b =>
    measure_mono (Set.preimage_mono (subset_toMeasurable _ _))
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have h2t : (κ otimesₖ η) a t != ∞ := by rwa [measure_toMeasurable]
  have ht_lt_top : forallᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' t) < ∞ := by
    rw [Kernel.compProd_apply ht] at h2t
    exact ae_lt_top (Kernel.measurable_kernel_prodMk_left' ht a) h2t
  filter_upwards [ht_lt_top] with b hb
  exact (this b).trans_lt hb

中文:
定理 ae_kernel_lt_top
  条件: (a : α) (h2s : (κ otimesₖ η) a s != ∞)
  证明: by
  let t := toMeasurable ((κ otimesₖ η) a) s
  have : forall b : β, η (a, b) (Prod.mk b ⁻¹' s) <= η (a, b) (Prod.mk b ⁻¹' t) := fun b =>
    measure_mono (Set.preimage_mono (subset_toMeasurable _ _))
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have h2t : (κ otimesₖ η) a t != ∞ := by rwa [measure_toMeasurable]
  have ht_lt_top : forallᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' t) < ∞ := by
    rw [Kernel.compProd_apply ht] at h2t
    exact ae_lt_top (Kernel.measurable_kernel_prodMk_left' ht a) h2t
  filter_upwards [ht_lt_top] with b hb
  exact (this b).trans_lt hb

Depends on / 依赖: Kernel, Kernel.compProd_apply, Kernel.measurable_kernel_prodMk_left, MeasurableSet, Prod.mk, Set.preimage_mono, ae_lt_top, compProd_apply, filter_, ht_lt_top, measurableSet_toMeasurable, measurable_kernel_prodMk_left, measure_mono, measure_toMeasurable, preimage_mono, subset_toMeasurable, toMeasurable
-/
theorem ae_kernel_lt_top (a : α) (h2s : (κ otimesₖ η) a s != ∞) :
    forallᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' s) < ∞ := by
  let t := toMeasurable ((κ otimesₖ η) a) s
  have : forall b : β, η (a, b) (Prod.mk b ⁻¹' s) <= η (a, b) (Prod.mk b ⁻¹' t) := fun b =>
    measure_mono (Set.preimage_mono (subset_toMeasurable _ _))
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have h2t : (κ otimesₖ η) a t != ∞ := by rwa [measure_toMeasurable]
  have ht_lt_top : forallᵐ b ∂κ a, η (a, b) (Prod.mk b ⁻¹' t) < ∞ := by
    rw [Kernel.compProd_apply ht] at h2t
    exact ae_lt_top (Kernel.measurable_kernel_prodMk_left' ht a) h2t
  filter_upwards [ht_lt_top] with b hb
  exact (this b).trans_lt hb

/--
theorem `compProd_null` / 定理 `compProd_null`

English:
theorem compProd_null
  given: (a : α) (hs : MeasurableSet s)
  proof: by
  rw [Kernel.compProd_apply hs]; rw [lintegral_eq_zero_iff]
  exact Kernel.measurable_kernel_prodMk_left' hs a

中文:
定理 compProd_null
  条件: (a : α) (hs : 可测集 s)
  证明: by
  rw [Kernel.compProd_apply hs]; rw [lintegral_eq_zero_iff]
  exact Kernel.measurable_kernel_prodMk_left' hs a

Depends on / 依赖: Kernel, Kernel.compProd_apply, Kernel.measurable_kernel_prodMk_left, compProd_apply, lintegral_eq_zero_iff, measurable_kernel_prodMk_left
-/
theorem compProd_null (a : α) (hs : MeasurableSet s) :
    (κ otimesₖ η) a s = 0 ↔ (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  rw [Kernel.compProd_apply hs]; rw [lintegral_eq_zero_iff]
  exact Kernel.measurable_kernel_prodMk_left' hs a

/--
theorem `ae_null_of_compProd_null` / 定理 `ae_null_of_compProd_null`

English:
theorem ae_null_of_compProd_null
  given: (h : (κ otimesₖ η) a s = 0)
  proof: by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [compProd_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact
    ⟨Filter.EventuallyLE.trans_eq
        (Filter.Eventually.of_forall fun x => measure_mono (Set.preimage_mono hst)) ht,
      Filter.Eventually.of_forall fun x => zero_le⟩

中文:
定理 ae_null_of_compProd_null
  条件: (h : (κ otimesₖ η) a s = 0)
  证明: by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [compProd_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact
    ⟨Filter.EventuallyLE.trans_eq
        (Filter.Eventually.of_forall fun x => measure_mono (Set.preimage_mono hst)) ht,
      Filter.Eventually.of_forall fun x => zero_le⟩

Depends on / 依赖: Eventually, EventuallyLE, Filter, Filter.Eventually.of_forall, Filter.EventuallyLE.trans_eq, Filter.eventuallyLE_antisymm_iff, Set.preimage_mono, compProd_null, eventuallyLE_antisymm_iff, exists_measurable_superset_of_null, measure_mono, of_forall, preimage_mono, simp_rw, trans_eq, zero_le
-/
theorem ae_null_of_compProd_null (h : (κ otimesₖ η) a s = 0) :
    (fun b => η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  simp_rw [compProd_null a mt] at ht
  rw [Filter.eventuallyLE_antisymm_iff]
  exact
    ⟨Filter.EventuallyLE.trans_eq
        (Filter.Eventually.of_forall fun x => measure_mono (Set.preimage_mono hst)) ht,
      Filter.Eventually.of_forall fun x => zero_le⟩

/--
theorem `ae_ae_of_ae_compProd` / 定理 `ae_ae_of_ae_compProd`

English:
theorem ae_ae_of_ae_compProd
  given: {p : β × γ -> Prop} (h : forallᵐ bc ∂(κ otimesₖ η) a, p bc)
  proof: ae_null_of_compProd_null h

中文:
定理 ae_ae_of_ae_compProd
  条件: {p : β × γ -> 命题} (h : 对任意ᵐ bc ∂(κ otimesₖ η) a, p bc)
  证明: ae_null_of_compProd_null h

Depends on / 依赖: ae_null_of_compProd_null
-/
theorem ae_ae_of_ae_compProd {p : β × γ -> Prop} (h : forallᵐ bc ∂(κ otimesₖ η) a, p bc) :
    forallᵐ b ∂κ a, forallᵐ c ∂η (a, b), p (b, c) :=
  ae_null_of_compProd_null h

/--
lemma `ae_compProd_of_ae_ae` / 引理 `ae_compProd_of_ae_ae`

English:
lemma ae_compProd_of_ae_ae
  statement: {κ : Kernel α β} {η : Kernel (α × β) γ}
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [compProd_of_not_isSFiniteKernel_right _ _ hη]
  simp_rw [ae_iff] at h ⊢
  rw [compProd_null]
  · exact h
  · exact hp.compl

中文:
引理 ae_compProd_of_ae_ae
  结论: {κ : 核 α β} {η : 核 (α × β) γ}
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [compProd_of_not_isSFiniteKernel_right _ _ hη]
  simp_rw [ae_iff] at h ⊢
  rw [compProd_null]
  · exact h
  · exact hp.compl

Depends on / 依赖: IsSFiniteKernel, ae_iff, compProd_null, compProd_of_not_isSFiniteKernel_left, compProd_of_not_isSFiniteKernel_right, hp.compl, simp_rw
-/
lemma ae_compProd_of_ae_ae {κ : Kernel α β} {η : Kernel (α × β) γ}
    {p : β × γ -> Prop} (hp : MeasurableSet {x | p x})
    (h : forallᵐ b ∂κ a, forallᵐ c ∂η (a, b), p (b, c)) :
    forallᵐ bc ∂(κ otimesₖ η) a, p bc := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [compProd_of_not_isSFiniteKernel_right _ _ hη]
  simp_rw [ae_iff] at h ⊢
  rw [compProd_null]
  · exact h
  · exact hp.compl

/--
lemma `ae_compProd_iff` / 引理 `ae_compProd_iff`

English:
lemma ae_compProd_iff
  given: {p : β × γ -> Prop} (hp : MeasurableSet {x | p x})
  proof: ⟨fun h => ae_ae_of_ae_compProd h, fun h => ae_compProd_of_ae_ae hp h⟩

中文:
引理 ae_compProd_iff
  条件: {p : β × γ -> 命题} (hp : 可测集 {x | p x})
  证明: ⟨fun h => ae_ae_of_ae_compProd h, fun h => ae_compProd_of_ae_ae hp h⟩

Depends on / 依赖: ae_ae_of_ae_compProd, ae_compProd_of_ae_ae
-/
lemma ae_compProd_iff {p : β × γ -> Prop} (hp : MeasurableSet {x | p x}) :
    (forallᵐ bc ∂(κ otimesₖ η) a, p bc) ↔ forallᵐ b ∂κ a, forallᵐ c ∂η (a, b), p (b, c) :=
  ⟨fun h => ae_ae_of_ae_compProd h, fun h => ae_compProd_of_ae_ae hp h⟩

end Ae

section Restrict

variable {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η]

/--
theorem `compProd_restrict` / 定理 `compProd_restrict`

English:
theorem compProd_restrict
  given: {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  ext a u hu
  rw [compProd_apply hu]; rw [restrict_apply' _ _ _ hu]; rw [compProd_apply (hu.inter (hs.prod ht))]
  simp only [restrict_apply, Set.preimage, Measure.restrict_apply' ht, Set.mem_inter_iff,
    Set.mem_prod]
  have (b : _) : η (a, b) {c : γ | (b, c) in u ∧ b in s ∧ c in t} =
      s.indicator (fun b => η (a, b) ({c : γ | (b, c) in u} inter t)) b := by
    classical
    rw [Set.indicator_apply]
    split_ifs with h
    · simp only [h, true_and, Set.inter_def, Set.mem_ofPred]
    · simp only [h, false_and, and_false, Set.ofPred_false, measure_empty]
  simp_rw [this]
  rw [lintegral_indicator hs]

中文:
定理 compProd_restrict
  条件: {s : 集合 β} {t : 集合 γ} (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  ext a u hu
  rw [compProd_apply hu]; rw [restrict_apply' _ _ _ hu]; rw [compProd_apply (hu.inter (hs.prod ht))]
  simp only [restrict_apply, Set.preimage, Measure.restrict_apply' ht, Set.mem_inter_iff,
    Set.mem_prod]
  have (b : _) : η (a, b) {c : γ | (b, c) in u ∧ b in s ∧ c in t} =
      s.indicator (fun b => η (a, b) ({c : γ | (b, c) in u} inter t)) b := by
    classical
    rw [Set.indicator_apply]
    split_ifs with h
    · simp only [h, true_and, Set.inter_def, Set.mem_ofPred]
    · simp only [h, false_and, and_false, Set.ofPred_false, measure_empty]
  simp_rw [this]
  rw [lintegral_indicator hs]

Depends on / 依赖: Measure, Measure.restrict_apply, Set.indicator_apply, Set.inter_def, Set.mem_inter_iff, Set.mem_ofPred, Set.mem_prod, Set.preimage, and_false, classical, compProd_apply, false_and, hs.prod, hu.inter, indicator, indicator_apply, inter_def, mem_inter_iff, mem_ofPred, mem_prod
-/
theorem compProd_restrict {s : Set β} {t : Set γ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Kernel.restrict κ hs otimesₖ Kernel.restrict η ht = Kernel.restrict (κ otimesₖ η) (hs.prod ht) := by
  ext a u hu
  rw [compProd_apply hu]; rw [restrict_apply' _ _ _ hu]; rw [compProd_apply (hu.inter (hs.prod ht))]
  simp only [restrict_apply, Set.preimage, Measure.restrict_apply' ht, Set.mem_inter_iff,
    Set.mem_prod]
  have (b : _) : η (a, b) {c : γ | (b, c) in u ∧ b in s ∧ c in t} =
      s.indicator (fun b => η (a, b) ({c : γ | (b, c) in u} inter t)) b := by
    classical
    rw [Set.indicator_apply]
    split_ifs with h
    · simp only [h, true_and, Set.inter_def, Set.mem_ofPred]
    · simp only [h, false_and, and_false, Set.ofPred_false, measure_empty]
  simp_rw [this]
  rw [lintegral_indicator hs]

/--
theorem `compProd_restrict_left` / 定理 `compProd_restrict_left`

English:
theorem compProd_restrict_left
  given: {s : Set β} (hs : MeasurableSet s)
  proof: by
  rw [← compProd_restrict hs MeasurableSet.univ]
  congr; exact Kernel.restrict_univ.symm

中文:
定理 compProd_restrict_left
  条件: {s : 集合 β} (hs : 可测集 s)
  证明: by
  rw [← compProd_restrict hs MeasurableSet.univ]
  congr; exact Kernel.restrict_univ.symm

Depends on / 依赖: Kernel, Kernel.restrict_univ.symm, MeasurableSet, MeasurableSet.univ, compProd_restrict, restrict_univ
-/
theorem compProd_restrict_left {s : Set β} (hs : MeasurableSet s) :
    Kernel.restrict κ hs otimesₖ η = Kernel.restrict (κ otimesₖ η) (hs.prod MeasurableSet.univ) := by
  rw [← compProd_restrict hs MeasurableSet.univ]
  congr; exact Kernel.restrict_univ.symm

/--
theorem `compProd_restrict_right` / 定理 `compProd_restrict_right`

English:
theorem compProd_restrict_right
  given: {t : Set γ} (ht : MeasurableSet t)
  proof: by
  rw [← compProd_restrict MeasurableSet.univ ht]
  congr; exact Kernel.restrict_univ.symm

中文:
定理 compProd_restrict_right
  条件: {t : 集合 γ} (ht : 可测集 t)
  证明: by
  rw [← compProd_restrict MeasurableSet.univ ht]
  congr; exact Kernel.restrict_univ.symm

Depends on / 依赖: Kernel, Kernel.restrict_univ.symm, MeasurableSet, MeasurableSet.univ, compProd_restrict, restrict_univ
-/
theorem compProd_restrict_right {t : Set γ} (ht : MeasurableSet t) :
    κ otimesₖ Kernel.restrict η ht = Kernel.restrict (κ otimesₖ η) (MeasurableSet.univ.prod ht) := by
  rw [← compProd_restrict MeasurableSet.univ ht]
  congr; exact Kernel.restrict_univ.symm

end Restrict

section Lintegral

/-! ### Lebesgue integral -/


/--
theorem `lintegral_compProd'` / 定理 `lintegral_compProd'`

English:
theorem lintegral_compProd'
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
  proof: by
  let F : Nat -> SimpleFunc (β × γ) Real>=0∞ := SimpleFunc.eapprox (Function.uncurry f)
  have h : forall a, ⨆ n, F n a = Function.uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, Function.uncurry_apply_pair] at h
  simp_rw [← h]
  have h_mono : Monotone F := fun i j hij b =>
    SimpleFunc.monotone_eapprox (Function.uncurry f) hij _
  rw [lintegral_iSup (fun n => (F n).measurable) h_mono]
  have : forall b, ∫⁻ c, ⨆ n, F n (b, c) ∂η (a, b) = ⨆ n, ∫⁻ c, F n (b, c) ∂η (a, b) := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => h_mono hij _
  simp_rw [this]
  have h_some_meas_integral :
    forall f' : SimpleFunc (β × γ) Real>=0∞, Measurable fun b => ∫⁻ c, f' (b, c) ∂η (a, b) := by
    intro f'
    have :
      (fun b => ∫⁻ c, f' (b, c) ∂η (a, b)) =
        (fun ab => ∫⁻ c, f' (ab.2, c) ∂η ab) ∘ fun b => (a, b) := by
      ext1 ab; rfl
    rw [this]
    fun_prop
  rw [lintegral_iSup]
  rotate_left
  · exact fun n => h_some_meas_integral (F n)
  · exact fun i j hij b => lintegral_mono fun c => h_mono hij _
  congr
  ext1 n
  refine SimpleFunc.induction ?_ ?_ (F n)
  · intro c s hs
    simp +unfoldPartialApp only [SimpleFunc.const_zero,
      SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.coe_zero,
      Set.piecewise_eq_indicator, Function.const, lintegral_indicator_const hs]
    rw [compProd_apply hs]; rw [← lintegral_const_mul c _]
    swap
    · exact (measurable_kernel_prodMk_left ((measurable_fst.snd.prodMk measurable_snd) hs)).comp
        measurable_prodMk_left
    congr
    ext1 b
    rw [lintegral_indicator_const_comp measurable_prodMk_left hs]
  · intro f f' _ hf_eq hf'_eq
    simp_rw [SimpleFunc.coe_add, Pi.add_apply]
    change
      ∫⁻ x, (f : β × γ -> Real>=0∞) x + f' x ∂(κ otimesₖ η) a =
        ∫⁻ b, ∫⁻ c : γ, f (b, c) + f' (b, c) ∂η (a, b) ∂κ a
    rw [lintegral_add_left (SimpleFunc.measurable _)]; rw [hf_eq]; rw [hf'_eq]; rw [← lintegral_add_left]
    swap
    · exact h_some_meas_integral f
    congr with b
    rw [lintegral_add_left]
    exact (SimpleFunc.measurable _).comp measurable_prodMk_left

中文:
定理 lintegral_compProd'
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 (α × β) γ)
  证明: by
  let F : Nat -> SimpleFunc (β × γ) Real>=0∞ := SimpleFunc.eapprox (Function.uncurry f)
  have h : forall a, ⨆ n, F n a = Function.uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, Function.uncurry_apply_pair] at h
  simp_rw [← h]
  have h_mono : Monotone F := fun i j hij b =>
    SimpleFunc.monotone_eapprox (Function.uncurry f) hij _
  rw [lintegral_iSup (fun n => (F n).measurable) h_mono]
  have : forall b, ∫⁻ c, ⨆ n, F n (b, c) ∂η (a, b) = ⨆ n, ∫⁻ c, F n (b, c) ∂η (a, b) := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => h_mono hij _
  simp_rw [this]
  have h_some_meas_integral :
    forall f' : SimpleFunc (β × γ) Real>=0∞, Measurable fun b => ∫⁻ c, f' (b, c) ∂η (a, b) := by
    intro f'
    have :
      (fun b => ∫⁻ c, f' (b, c) ∂η (a, b)) =
        (fun ab => ∫⁻ c, f' (ab.2, c) ∂η ab) ∘ fun b => (a, b) := by
      ext1 ab; rfl
    rw [this]
    fun_prop
  rw [lintegral_iSup]
  rotate_left
  · exact fun n => h_some_meas_integral (F n)
  · exact fun i j hij b => lintegral_mono fun c => h_mono hij _
  congr
  ext1 n
  refine SimpleFunc.induction ?_ ?_ (F n)
  · intro c s hs
    simp +unfoldPartialApp only [SimpleFunc.const_zero,
      SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.coe_zero,
      Set.piecewise_eq_indicator, Function.const, lintegral_indicator_const hs]
    rw [compProd_apply hs]; rw [← lintegral_const_mul c _]
    swap
    · exact (measurable_kernel_prodMk_left ((measurable_fst.snd.prodMk measurable_snd) hs)).comp
        measurable_prodMk_left
    congr
    ext1 b
    rw [lintegral_indicator_const_comp measurable_prodMk_left hs]
  · intro f f' _ hf_eq hf'_eq
    simp_rw [SimpleFunc.coe_add, Pi.add_apply]
    change
      ∫⁻ x, (f : β × γ -> Real>=0∞) x + f' x ∂(κ otimesₖ η) a =
        ∫⁻ b, ∫⁻ c : γ, f (b, c) + f' (b, c) ∂η (a, b) ∂κ a
    rw [lintegral_add_left (SimpleFunc.measurable _)]; rw [hf_eq]; rw [hf'_eq]; rw [← lintegral_add_left]
    swap
    · exact h_some_meas_integral f
    congr with b
    rw [lintegral_add_left]
    exact (SimpleFunc.measurable _).comp measurable_prodMk_left

Depends on / 依赖: Function, Function.uncurry, Function.uncurry_apply_pair, Monotone, Prod.forall, SimpleFunc, SimpleFunc.eapprox, SimpleFunc.iSup_eapprox_apply, SimpleFunc.monotone_eapprox, eapprox, h_mono, iSup_eapprox_apply, lintegral_iSup, measurable, monotone_eapprox, simp_rw, uncurry, uncurry_apply_pair
-/
theorem lintegral_compProd' (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β -> γ -> Real>=0∞} (hf : Measurable (Function.uncurry f)) :
    ∫⁻ bc, f bc.1 bc.2 ∂(κ otimesₖ η) a = ∫⁻ b, ∫⁻ c, f b c ∂η (a, b) ∂κ a := by
  let F : Nat -> SimpleFunc (β × γ) Real>=0∞ := SimpleFunc.eapprox (Function.uncurry f)
  have h : forall a, ⨆ n, F n a = Function.uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, Function.uncurry_apply_pair] at h
  simp_rw [← h]
  have h_mono : Monotone F := fun i j hij b =>
    SimpleFunc.monotone_eapprox (Function.uncurry f) hij _
  rw [lintegral_iSup (fun n => (F n).measurable) h_mono]
  have : forall b, ∫⁻ c, ⨆ n, F n (b, c) ∂η (a, b) = ⨆ n, ∫⁻ c, F n (b, c) ∂η (a, b) := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => h_mono hij _
  simp_rw [this]
  have h_some_meas_integral :
    forall f' : SimpleFunc (β × γ) Real>=0∞, Measurable fun b => ∫⁻ c, f' (b, c) ∂η (a, b) := by
    intro f'
    have :
      (fun b => ∫⁻ c, f' (b, c) ∂η (a, b)) =
        (fun ab => ∫⁻ c, f' (ab.2, c) ∂η ab) ∘ fun b => (a, b) := by
      ext1 ab; rfl
    rw [this]
    fun_prop
  rw [lintegral_iSup]
  rotate_left
  · exact fun n => h_some_meas_integral (F n)
  · exact fun i j hij b => lintegral_mono fun c => h_mono hij _
  congr
  ext1 n
  refine SimpleFunc.induction ?_ ?_ (F n)
  · intro c s hs
    simp +unfoldPartialApp only [SimpleFunc.const_zero,
      SimpleFunc.coe_piecewise, SimpleFunc.coe_const, SimpleFunc.coe_zero,
      Set.piecewise_eq_indicator, Function.const, lintegral_indicator_const hs]
    rw [compProd_apply hs]; rw [← lintegral_const_mul c _]
    swap
    · exact (measurable_kernel_prodMk_left ((measurable_fst.snd.prodMk measurable_snd) hs)).comp
        measurable_prodMk_left
    congr
    ext1 b
    rw [lintegral_indicator_const_comp measurable_prodMk_left hs]
  · intro f f' _ hf_eq hf'_eq
    simp_rw [SimpleFunc.coe_add, Pi.add_apply]
    change
      ∫⁻ x, (f : β × γ -> Real>=0∞) x + f' x ∂(κ otimesₖ η) a =
        ∫⁻ b, ∫⁻ c : γ, f (b, c) + f' (b, c) ∂η (a, b) ∂κ a
    rw [lintegral_add_left (SimpleFunc.measurable _)]; rw [hf_eq]; rw [hf'_eq]; rw [← lintegral_add_left]
    swap
    · exact h_some_meas_integral f
    congr with b
    rw [lintegral_add_left]
    exact (SimpleFunc.measurable _).comp measurable_prodMk_left

/--
theorem `lintegral_compProd` / 定理 `lintegral_compProd`

English:
theorem lintegral_compProd
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
  proof: by
  let g := Function.curry f
  change ∫⁻ bc, f bc ∂(κ otimesₖ η) a = ∫⁻ b, ∫⁻ c, g b c ∂η (a, b) ∂κ a
  rw [← lintegral_compProd']
  · simp_rw [g, Function.curry_apply]
  · simp_rw [g, Function.uncurry_curry]; exact hf

中文:
定理 lintegral_compProd
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 (α × β) γ)
  证明: by
  let g := Function.curry f
  change ∫⁻ bc, f bc ∂(κ otimesₖ η) a = ∫⁻ b, ∫⁻ c, g b c ∂η (a, b) ∂κ a
  rw [← lintegral_compProd']
  · simp_rw [g, Function.curry_apply]
  · simp_rw [g, Function.uncurry_curry]; exact hf

Depends on / 依赖: Function, Function.curry, Function.curry_apply, Function.uncurry_curry, curry_apply, lintegral_compProd, simp_rw, uncurry_curry
-/
theorem lintegral_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ -> Real>=0∞} (hf : Measurable f) :
    ∫⁻ bc, f bc ∂(κ otimesₖ η) a = ∫⁻ b, ∫⁻ c, f (b, c) ∂η (a, b) ∂κ a := by
  let g := Function.curry f
  change ∫⁻ bc, f bc ∂(κ otimesₖ η) a = ∫⁻ b, ∫⁻ c, g b c ∂η (a, b) ∂κ a
  rw [← lintegral_compProd']
  · simp_rw [g, Function.curry_apply]
  · simp_rw [g, Function.uncurry_curry]; exact hf

/--
theorem `lintegral_compProd₀` / 定理 `lintegral_compProd₀`

English:
theorem lintegral_compProd₀
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
  proof: by
  have A : ∫⁻ z, f z ∂(κ otimesₖ η) a = ∫⁻ z, hf.mk f z ∂(κ otimesₖ η) a := lintegral_congr_ae hf.ae_eq_mk
  have B : ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a = ∫⁻ x, ∫⁻ y, hf.mk f (x, y) ∂η (a, x) ∂κ a := by
    apply lintegral_congr_ae
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ ha using lintegral_congr_ae ha
  rw [A]; rw [B]; rw [lintegral_compProd]
  exact hf.measurable_mk

中文:
定理 lintegral_compProd₀
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 (α × β) γ)
  证明: by
  have A : ∫⁻ z, f z ∂(κ otimesₖ η) a = ∫⁻ z, hf.mk f z ∂(κ otimesₖ η) a := lintegral_congr_ae hf.ae_eq_mk
  have B : ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a = ∫⁻ x, ∫⁻ y, hf.mk f (x, y) ∂η (a, x) ∂κ a := by
    apply lintegral_congr_ae
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ ha using lintegral_congr_ae ha
  rw [A]; rw [B]; rw [lintegral_compProd]
  exact hf.measurable_mk

Depends on / 依赖: ae_ae_of_ae_compProd, ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.measurable_mk, hf.mk, lintegral_compProd, lintegral_congr_ae, measurable_mk
-/
theorem lintegral_compProd₀ (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ -> Real>=0∞} (hf : AEMeasurable f ((κ otimesₖ η) a)) :
    ∫⁻ z, f z ∂(κ otimesₖ η) a = ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a := by
  have A : ∫⁻ z, f z ∂(κ otimesₖ η) a = ∫⁻ z, hf.mk f z ∂(κ otimesₖ η) a := lintegral_congr_ae hf.ae_eq_mk
  have B : ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a = ∫⁻ x, ∫⁻ y, hf.mk f (x, y) ∂η (a, x) ∂κ a := by
    apply lintegral_congr_ae
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ ha using lintegral_congr_ae ha
  rw [A]; rw [B]; rw [lintegral_compProd]
  exact hf.measurable_mk

/--
theorem `setLIntegral_compProd` / 定理 `setLIntegral_compProd`

English:
theorem setLIntegral_compProd
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
  proof: by
  simp_rw [← Kernel.restrict_apply (κ otimesₖ η) (hs.prod ht), ← compProd_restrict hs ht,
    lintegral_compProd _ _ _ hf, Kernel.restrict_apply]

中文:
定理 setL整数egral_compProd
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 (α × β) γ)
  证明: by
  simp_rw [← Kernel.restrict_apply (κ otimesₖ η) (hs.prod ht), ← compProd_restrict hs ht,
    lintegral_compProd _ _ _ hf, Kernel.restrict_apply]

Depends on / 依赖: Kernel, Kernel.restrict_apply, compProd_restrict, hs.prod, lintegral_compProd, restrict_apply, simp_rw
-/
theorem setLIntegral_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ -> Real>=0∞} (hf : Measurable f) {s : Set β} {t : Set γ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ z in s ×ˢ t, f z ∂(κ otimesₖ η) a = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [← Kernel.restrict_apply (κ otimesₖ η) (hs.prod ht), ← compProd_restrict hs ht,
    lintegral_compProd _ _ _ hf, Kernel.restrict_apply]

/--
theorem `setLIntegral_compProd_univ_right` / 定理 `setLIntegral_compProd_univ_right`

English:
theorem setLIntegral_compProd_univ_right
  statement: (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  simp_rw [setLIntegral_compProd κ η a hf hs MeasurableSet.univ, Measure.restrict_univ]

中文:
定理 setL整数egral_compProd_univ_right
  结论: (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  simp_rw [setLIntegral_compProd κ η a hf hs MeasurableSet.univ, Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setLIntegral_compProd, simp_rw
-/
theorem setLIntegral_compProd_univ_right (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) {f : β × γ -> Real>=0∞} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ z in s ×ˢ Set.univ, f z ∂(κ otimesₖ η) a = ∫⁻ x in s, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setLIntegral_compProd κ η a hf hs MeasurableSet.univ, Measure.restrict_univ]

/--
theorem `setLIntegral_compProd_univ_left` / 定理 `setLIntegral_compProd_univ_left`

English:
theorem setLIntegral_compProd_univ_left
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
  proof: by
  simp_rw [setLIntegral_compProd κ η a hf MeasurableSet.univ ht, Measure.restrict_univ]

中文:
定理 setL整数egral_compProd_univ_left
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 (α × β) γ)
  证明: by
  simp_rw [setLIntegral_compProd κ η a hf MeasurableSet.univ ht, Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setLIntegral_compProd, simp_rw
-/
theorem setLIntegral_compProd_univ_left (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) {f : β × γ -> Real>=0∞} (hf : Measurable f) {t : Set γ}
    (ht : MeasurableSet t) :
    ∫⁻ z in Set.univ ×ˢ t, f z ∂(κ otimesₖ η) a = ∫⁻ x, ∫⁻ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setLIntegral_compProd κ η a hf MeasurableSet.univ ht, Measure.restrict_univ]

end Lintegral

/--
theorem `compProd_eq_sum_compProd_left` / 定理 `compProd_eq_sum_compProd_left`

English:
theorem compProd_eq_sum_compProd_left
  given: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
  proof: by
  simp_rw [compProd_def]
  rw [← comp_sum_left]; rw [← comp_sum_right]; rw [← parallelComp_sum_right]; rw [kernel_sum_seq]

中文:
定理 compProd_eq_sum_compProd_left
  条件: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 (α × β) γ)
  证明: by
  simp_rw [compProd_def]
  rw [← comp_sum_left]; rw [← comp_sum_right]; rw [← parallelComp_sum_right]; rw [kernel_sum_seq]

Depends on / 依赖: compProd_def, comp_sum_left, comp_sum_right, kernel_sum_seq, parallelComp_sum_right, simp_rw
-/
theorem compProd_eq_sum_compProd_left (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) :
    κ otimesₖ η = Kernel.sum fun n => seq κ n otimesₖ η := by
  simp_rw [compProd_def]
  rw [← comp_sum_left]; rw [← comp_sum_right]; rw [← parallelComp_sum_right]; rw [kernel_sum_seq]

/--
theorem `compProd_eq_sum_compProd_right` / 定理 `compProd_eq_sum_compProd_right`

English:
theorem compProd_eq_sum_compProd_right
  statement: (κ : Kernel α β) (η : Kernel (α × β) γ)
  proof: by
  simp_rw [compProd_def]
  rw [← comp_sum_left]; rw [← comp_sum_left]; rw [← comp_sum_left]; rw [← comp_sum_left]; rw [← comp_sum_right]; rw [← parallelComp_sum_left]; rw [kernel_sum_seq]

中文:
定理 compProd_eq_sum_compProd_right
  结论: (κ : 核 α β) (η : 核 (α × β) γ)
  证明: by
  simp_rw [compProd_def]
  rw [← comp_sum_left]; rw [← comp_sum_left]; rw [← comp_sum_left]; rw [← comp_sum_left]; rw [← comp_sum_right]; rw [← parallelComp_sum_left]; rw [kernel_sum_seq]

Depends on / 依赖: compProd_def, comp_sum_left, comp_sum_right, kernel_sum_seq, parallelComp_sum_left, simp_rw
-/
theorem compProd_eq_sum_compProd_right (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] : κ otimesₖ η = Kernel.sum fun n => κ otimesₖ seq η n := by
  simp_rw [compProd_def]
  rw [← comp_sum_left]; rw [← comp_sum_left]; rw [← comp_sum_left]; rw [← comp_sum_left]; rw [← comp_sum_right]; rw [← parallelComp_sum_left]; rw [kernel_sum_seq]

/--
theorem `compProd_eq_sum_compProd` / 定理 `compProd_eq_sum_compProd`

English:
theorem compProd_eq_sum_compProd
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
  proof: by
  simp_rw [← compProd_eq_sum_compProd_right, ← compProd_eq_sum_compProd_left]

中文:
定理 compProd_eq_sum_compProd
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 (α × β) γ)
  证明: by
  simp_rw [← compProd_eq_sum_compProd_right, ← compProd_eq_sum_compProd_left]

Depends on / 依赖: compProd_eq_sum_compProd_left, compProd_eq_sum_compProd_right, simp_rw
-/
theorem compProd_eq_sum_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] : κ otimesₖ η = Kernel.sum fun n => Kernel.sum fun m => seq κ n otimesₖ seq η m := by
  simp_rw [← compProd_eq_sum_compProd_right, ← compProd_eq_sum_compProd_left]

/--
theorem `compProd_eq_tsum_compProd` / 定理 `compProd_eq_tsum_compProd`

English:
theorem compProd_eq_tsum_compProd
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
  proof: by
  rw [compProd_eq_sum_compProd]
  simp_rw [sum_apply' _ _ hs]

中文:
定理 compProd_eq_tsum_compProd
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 (α × β) γ)
  证明: by
  rw [compProd_eq_sum_compProd]
  simp_rw [sum_apply' _ _ hs]

Depends on / 依赖: compProd_eq_sum_compProd, simp_rw, sum_apply
-/
theorem compProd_eq_tsum_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] (a : α) (hs : MeasurableSet s) :
    (κ otimesₖ η) a s = ∑' (n : Nat) (m : Nat), (seq κ n otimesₖ seq η m) a s := by
  rw [compProd_eq_sum_compProd]
  simp_rw [sum_apply' _ _ hs]

/--
Instance `IsMarkovKernel.compProd` / 实例 `IsMarkovKernel.compProd`

English:
instance IsMarkovKernel.compProd
  signature: (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel (α × β) γ)
  body: ⟨by simp [compProd_apply]⟩

中文:
实例 是MarkovKernel.compProd
  签名: (κ : 核 α β) [是MarkovKernel κ] (η : 核 (α × β) γ)
  定义体: ⟨by simp [compProd_apply]⟩

Depends on / 依赖: compProd_apply
-/
instance IsMarkovKernel.compProd (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel (α × β) γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ otimesₖ η) where
  isProbabilityMeasure a := ⟨by simp [compProd_apply]⟩

/--
Instance `IsZeroOrMarkovKernel.compProd` / 实例 `IsZeroOrMarkovKernel.compProd`

English:
instance IsZeroOrMarkovKernel.compProd
  signature: (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
  body: by
  rw [compProd_def]
  infer_instance

中文:
实例 是ZeroOrMarkovKernel.compProd
  签名: (κ : 核 α β) [是ZeroOrMarkovKernel κ]
  定义体: by
  rw [compProd_def]
  infer_instance

Depends on / 依赖: compProd_def, infer_instance
-/
instance IsZeroOrMarkovKernel.compProd (κ : Kernel α β) [IsZeroOrMarkovKernel κ]
    (η : Kernel (α × β) γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ otimesₖ η) := by
  rw [compProd_def]
  infer_instance

/--
theorem `compProd_apply_univ_le` / 定理 `compProd_apply_univ_le`

English:
theorem compProd_apply_univ_le
  given: (κ : Kernel α β) (η : Kernel (α × β) γ) [IsFiniteKernel η] (a : α)
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
    simp
  rw [compProd_apply .univ]
  let Cη := η.bound
  calc
    ∫⁻ b, η (a, b) Set.univ ∂κ a <= ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η (a, b) Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _

中文:
定理 compProd_apply_univ_le
  条件: (κ : 核 α β) (η : 核 (α × β) γ) [是FiniteKernel η] (a : α)
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
    simp
  rw [compProd_apply .univ]
  let Cη := η.bound
  calc
    ∫⁻ b, η (a, b) Set.univ ∂κ a <= ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η (a, b) Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _

Depends on / 依赖: IsSFiniteKernel, MeasureTheory, MeasureTheory.lintegral_const, Set.univ, compProd_apply, compProd_of_not_isSFiniteKernel_left, lintegral_const, lintegral_mono, measure_le_bound, mul_comm
-/
theorem compProd_apply_univ_le (κ : Kernel α β) (η : Kernel (α × β) γ) [IsFiniteKernel η] (a : α) :
    (κ otimesₖ η) a Set.univ <= κ a Set.univ * η.bound := by
  by_cases hκ : IsSFiniteKernel κ
  swap
  · rw [compProd_of_not_isSFiniteKernel_left _ _ hκ]
    simp
  rw [compProd_apply .univ]
  let Cη := η.bound
  calc
    ∫⁻ b, η (a, b) Set.univ ∂κ a <= ∫⁻ _, Cη ∂κ a :=
      lintegral_mono fun b => measure_le_bound η (a, b) Set.univ
    _ = Cη * κ a Set.univ := MeasureTheory.lintegral_const Cη
    _ = κ a Set.univ * Cη := mul_comm _ _

/--
Instance `IsFiniteKernel.compProd` / 实例 `IsFiniteKernel.compProd`

English:
instance IsFiniteKernel.compProd
  signature: (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel (α × β) γ)
  body: by
  rw [compProd_def]
  infer_instance

中文:
实例 是FiniteKernel.compProd
  签名: (κ : 核 α β) [是FiniteKernel κ] (η : 核 (α × β) γ)
  定义体: by
  rw [compProd_def]
  infer_instance

Depends on / 依赖: compProd_def, infer_instance
-/
instance IsFiniteKernel.compProd (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ otimesₖ η) := by
  rw [compProd_def]
  infer_instance

/--
Instance `IsSFiniteKernel.compProd` / 实例 `IsSFiniteKernel.compProd`

English:
instance IsSFiniteKernel.compProd
  signature: (κ : Kernel α β) (η : Kernel (α × β) γ)
  body: by
  rw [compProd_def]
  infer_instance

中文:
实例 是SFiniteKernel.compProd
  签名: (κ : 核 α β) (η : 核 (α × β) γ)
  定义体: by
  rw [compProd_def]
  infer_instance

Depends on / 依赖: compProd_def, infer_instance
-/
instance IsSFiniteKernel.compProd (κ : Kernel α β) (η : Kernel (α × β) γ) :
    IsSFiniteKernel (κ otimesₖ η) := by
  rw [compProd_def]
  infer_instance

/--
lemma `compProd_assoc` / 引理 `compProd_assoc`

English:
lemma compProd_assoc
  statement: {δ : Type*} {mδ : MeasurableSpace δ}
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  by_cases hξ : IsSFiniteKernel ξ
  swap
  · have : ¬ IsSFiniteKernel
        (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)) := by
      refine fun h_sfin => hξ ?_
      have : ξ = (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)).comap
          MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _) := by
        simp [← comap_comp_right]
      rw [this]
      infer_instance
    simp [hξ, this]
  ext a s hs
  rw [compProd_apply hs]; rw [map_apply' _ (by fun_prop) _ hs]; rw [compProd_apply (hs.preimage (by fun_prop))]; rw [lintegral_compProd]
  swap; · exact measurable_kernel_prodMk_left' hs a
  congr with b
  rw [compProd_apply]
  · congr
  · exact hs.preimage (by fun_prop)

中文:
引理 compProd_assoc
  结论: {δ : 类型} {mδ : 可测空间 δ}
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  by_cases hξ : IsSFiniteKernel ξ
  swap
  · have : ¬ IsSFiniteKernel
        (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)) := by
      refine fun h_sfin => hξ ?_
      have : ξ = (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)).comap
          MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _) := by
        simp [← comap_comp_right]
      rw [this]
      infer_instance
    simp [hξ, this]
  ext a s hs
  rw [compProd_apply hs]; rw [map_apply' _ (by fun_prop) _ hs]; rw [compProd_apply (hs.preimage (by fun_prop))]; rw [lintegral_compProd]
  swap; · exact measurable_kernel_prodMk_left' hs a
  congr with b
  rw [compProd_apply]
  · congr
  · exact hs.preimage (by fun_prop)

Depends on / 依赖: IsSFiniteKernel, MeasurableEquiv, MeasurableEquiv.measurable, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodAssoc.symm, comap_comp_right, h_sfin, infer_instance, measurable, prodAssoc
-/
lemma compProd_assoc {δ : Type*} {mδ : MeasurableSpace δ}
    {κ : Kernel α β} {η : Kernel (α × β) γ} {ξ : Kernel (α × β × γ) δ} :
    (κ otimesₖ (η otimesₖ (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)))).map
        MeasurableEquiv.prodAssoc.symm
      = κ otimesₖ η otimesₖ ξ := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  by_cases hξ : IsSFiniteKernel ξ
  swap
  · have : ¬ IsSFiniteKernel
        (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)) := by
      refine fun h_sfin => hξ ?_
      have : ξ = (ξ.comap MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _)).comap
          MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.measurable _) := by
        simp [← comap_comp_right]
      rw [this]
      infer_instance
    simp [hξ, this]
  ext a s hs
  rw [compProd_apply hs]; rw [map_apply' _ (by fun_prop) _ hs]; rw [compProd_apply (hs.preimage (by fun_prop))]; rw [lintegral_compProd]
  swap; · exact measurable_kernel_prodMk_left' hs a
  congr with b
  rw [compProd_apply]
  · congr
  · exact hs.preimage (by fun_prop)

/--
lemma `compProd_add_left` / 引理 `compProd_add_left`

English:
lemma compProd_add_left
  statement: (μ κ : Kernel α β) (η : Kernel (α × β) γ)
  proof: by
  by_cases hη : IsSFiniteKernel η
  · ext _ _ hs
    simp [compProd_apply hs]
  · simp [hη]

中文:
引理 compProd_add_left
  结论: (μ κ : 核 α β) (η : 核 (α × β) γ)
  证明: by
  by_cases hη : IsSFiniteKernel η
  · ext _ _ hs
    simp [compProd_apply hs]
  · simp [hη]

Depends on / 依赖: IsSFiniteKernel, compProd_apply
-/
lemma compProd_add_left (μ κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel μ] [IsSFiniteKernel κ] :
    (μ + κ) otimesₖ η = μ otimesₖ η + κ otimesₖ η := by
  by_cases hη : IsSFiniteKernel η
  · ext _ _ hs
    simp [compProd_apply hs]
  · simp [hη]

/--
lemma `compProd_add_right` / 引理 `compProd_add_right`

English:
lemma compProd_add_right
  statement: (μ : Kernel α β) (κ η : Kernel (α × β) γ)
  proof: by
  by_cases hμ : IsSFiniteKernel μ
  swap; · simp [hμ]
  ext a s hs
  simp only [compProd_apply hs, FunLike.coe_add, Pi.add_apply, Measure.coe_add]
  rw [lintegral_add_left]
  exact measurable_kernel_prodMk_left' hs a

中文:
引理 compProd_add_right
  结论: (μ : 核 α β) (κ η : 核 (α × β) γ)
  证明: by
  by_cases hμ : IsSFiniteKernel μ
  swap; · simp [hμ]
  ext a s hs
  simp only [compProd_apply hs, FunLike.coe_add, Pi.add_apply, Measure.coe_add]
  rw [lintegral_add_left]
  exact measurable_kernel_prodMk_left' hs a

Depends on / 依赖: FunLike, FunLike.coe_add, IsSFiniteKernel, Measure, Measure.coe_add, Pi.add_apply, add_apply, coe_add, compProd_apply, lintegral_add_left, measurable_kernel_prodMk_left
-/
lemma compProd_add_right (μ : Kernel α β) (κ η : Kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ otimesₖ (κ + η) = μ otimesₖ κ + μ otimesₖ η := by
  by_cases hμ : IsSFiniteKernel μ
  swap; · simp [hμ]
  ext a s hs
  simp only [compProd_apply hs, FunLike.coe_add, Pi.add_apply, Measure.coe_add]
  rw [lintegral_add_left]
  exact measurable_kernel_prodMk_left' hs a

/--
lemma `compProd_sum_left` / 引理 `compProd_sum_left`

English:
lemma compProd_sum_left
  statement: {ι : Type*} [Countable ι]
  proof: by
  by_cases hη : IsSFiniteKernel η
  · ext a s hs
    simp_rw [sum_apply, compProd_apply hs, sum_apply, lintegral_sum_measure, Measure.sum_apply _ hs,
    compProd_apply hs]
  · simp [hη]

中文:
引理 compProd_sum_left
  结论: {ι : 类型} [可数 ι]
  证明: by
  by_cases hη : IsSFiniteKernel η
  · ext a s hs
    simp_rw [sum_apply, compProd_apply hs, sum_apply, lintegral_sum_measure, Measure.sum_apply _ hs,
    compProd_apply hs]
  · simp [hη]

Depends on / 依赖: IsSFiniteKernel, Measure, Measure.sum_apply, compProd_apply, lintegral_sum_measure, simp_rw, sum_apply
-/
lemma compProd_sum_left {ι : Type*} [Countable ι]
    {κ : ι -> Kernel α β} {η : Kernel (α × β) γ} [forall i, IsSFiniteKernel (κ i)] :
    Kernel.sum κ otimesₖ η = Kernel.sum (fun i => (κ i) otimesₖ η) := by
  by_cases hη : IsSFiniteKernel η
  · ext a s hs
    simp_rw [sum_apply, compProd_apply hs, sum_apply, lintegral_sum_measure, Measure.sum_apply _ hs,
    compProd_apply hs]
  · simp [hη]

/--
lemma `compProd_sum_right` / 引理 `compProd_sum_right`

English:
lemma compProd_sum_right
  statement: {ι : Type*} [Countable ι]
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  ext a s hs
  simp_rw [sum_apply, compProd_apply hs, Measure.sum_apply _ hs, sum_apply, compProd_apply hs]
  rw [← lintegral_tsum]
  · congr with i
    rw [Measure.sum_apply]
    exact measurable_prodMk_left hs
  · exact fun _ => (measurable_kernel_prodMk_left' hs a).aemeasurable

中文:
引理 compProd_sum_right
  结论: {ι : 类型} [可数 ι]
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  ext a s hs
  simp_rw [sum_apply, compProd_apply hs, Measure.sum_apply _ hs, sum_apply, compProd_apply hs]
  rw [← lintegral_tsum]
  · congr with i
    rw [Measure.sum_apply]
    exact measurable_prodMk_left hs
  · exact fun _ => (measurable_kernel_prodMk_left' hs a).aemeasurable

Depends on / 依赖: IsSFiniteKernel, Measure, Measure.sum_apply, aemeasurable, compProd_apply, lintegral_tsum, measurable_kernel_prodMk_left, measurable_prodMk_left, simp_rw, sum_apply
-/
lemma compProd_sum_right {ι : Type*} [Countable ι]
    {κ : Kernel α β} {η : ι -> Kernel (α × β) γ} [forall i, IsSFiniteKernel (η i)] :
    κ otimesₖ Kernel.sum η = Kernel.sum (fun i => κ otimesₖ (η i)) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  ext a s hs
  simp_rw [sum_apply, compProd_apply hs, Measure.sum_apply _ hs, sum_apply, compProd_apply hs]
  rw [← lintegral_tsum]
  · congr with i
    rw [Measure.sum_apply]
    exact measurable_prodMk_left hs
  · exact fun _ => (measurable_kernel_prodMk_left' hs a).aemeasurable

/--
lemma `comapRight_compProd_id_prod` / 引理 `comapRight_compProd_id_prod`

English:
lemma comapRight_compProd_id_prod
  statement: {δ : Type*} {mδ : MeasurableSpace δ}
  proof: by
  ext a t ht
  rw [comapRight_apply' _ _ _ ht]; rw [compProd_apply]; rw [compProd_apply ht]
  · refine lintegral_congr fun b => ?_
    rw [comapRight_apply']
    · congr with x
      grind
    · exact measurable_prodMk_left ht
  · exact (MeasurableEmbedding.id.prodMap hf).measurableSet_image.mpr ht

中文:
引理 comapRight_compProd_id_prod
  结论: {δ : 类型} {mδ : 可测空间 δ}
  证明: by
  ext a t ht
  rw [comapRight_apply' _ _ _ ht]; rw [compProd_apply]; rw [compProd_apply ht]
  · refine lintegral_congr fun b => ?_
    rw [comapRight_apply']
    · congr with x
      grind
    · exact measurable_prodMk_left ht
  · exact (MeasurableEmbedding.id.prodMap hf).measurableSet_image.mpr ht

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.id.prodMap, comapRight_apply, compProd_apply, lintegral_congr, measurableSet_image, measurableSet_image.mpr, measurable_prodMk_left, prodMap
-/
lemma comapRight_compProd_id_prod {δ : Type*} {mδ : MeasurableSpace δ}
    (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η]
    {f : δ -> γ} (hf : MeasurableEmbedding f) :
    comapRight (κ otimesₖ η) (MeasurableEmbedding.id.prodMap hf) = κ otimesₖ (comapRight η hf) := by
  ext a t ht
  rw [comapRight_apply' _ _ _ ht]; rw [compProd_apply]; rw [compProd_apply ht]
  · refine lintegral_congr fun b => ?_
    rw [comapRight_apply']
    · congr with x
      grind
    · exact measurable_prodMk_left ht
  · exact (MeasurableEmbedding.id.prodMap hf).measurableSet_image.mpr ht

end CompositionProduct

open scoped ProbabilityTheory

section FstSnd

variable {δ : Type*} {mδ : MeasurableSpace δ}

/--
lemma `fst_compProd_apply` / 引理 `fst_compProd_apply`

English:
lemma fst_compProd_apply
  statement: (κ : Kernel α β) (η : Kernel (α × β) γ)
  proof: by
  rw [Kernel.fst_apply' _ _ hs]; rw [Kernel.compProd_apply]
  swap; · exact measurable_fst hs
  have h_eq b : η (x, b) {c | b in s} = s.indicator (fun b => η (x, b) Set.univ) b := by
    by_cases hb : b in s <;> simp [hb]
  simp_rw [Set.preimage, Set.mem_ofPred_eq, h_eq]

@[simp]

中文:
引理 fst_compProd_apply
  结论: (κ : 核 α β) (η : 核 (α × β) γ)
  证明: by
  rw [Kernel.fst_apply' _ _ hs]; rw [Kernel.compProd_apply]
  swap; · exact measurable_fst hs
  have h_eq b : η (x, b) {c | b in s} = s.indicator (fun b => η (x, b) Set.univ) b := by
    by_cases hb : b in s <;> simp [hb]
  simp_rw [Set.preimage, Set.mem_ofPred_eq, h_eq]

@[simp]

Depends on / 依赖: Kernel, Kernel.compProd_apply, Kernel.fst_apply, Set.mem_ofPred_eq, Set.preimage, Set.univ, compProd_apply, fst_apply, h_eq, indicator, measurable_fst, mem_ofPred_eq, preimage, s.indicator, simp_rw
-/
lemma fst_compProd_apply (κ : Kernel α β) (η : Kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (x : α) {s : Set β} (hs : MeasurableSet s) :
    (κ otimesₖ η).fst x s = ∫⁻ b, s.indicator (fun b => η (x, b) Set.univ) b ∂(κ x) := by
  rw [Kernel.fst_apply' _ _ hs]; rw [Kernel.compProd_apply]
  swap; · exact measurable_fst hs
  have h_eq b : η (x, b) {c | b in s} = s.indicator (fun b => η (x, b) Set.univ) b := by
    by_cases hb : b in s <;> simp [hb]
  simp_rw [Set.preimage, Set.mem_ofPred_eq, h_eq]

@[simp]
/--
lemma `fst_compProd` / 引理 `fst_compProd`

English:
lemma fst_compProd
  given: (κ : Kernel α β) (η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η]
  proof: by
  ext x s hs; simp [fst_compProd_apply, hs]

中文:
引理 fst_compProd
  条件: (κ : 核 α β) (η : 核 (α × β) γ) [是SFiniteKernel κ] [是MarkovKernel η]
  证明: by
  ext x s hs; simp [fst_compProd_apply, hs]

Depends on / 依赖: fst_compProd_apply
-/
lemma fst_compProd (κ : Kernel α β) (η : Kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] :
    fst (κ otimesₖ η) = κ := by
  ext x s hs; simp [fst_compProd_apply, hs]

end FstSnd

end Kernel
end ProbabilityTheory
