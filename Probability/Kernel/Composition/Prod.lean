/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.CompMap
public import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Product and composition of kernels

We define the product `κ ×ₖ η` of s-finite kernels `κ : Kernel α β` and `η : Kernel α γ`, which is
a kernel from `α` to `β × γ`.

## Main definitions

* `prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ)`: product of 2 s-finite kernels.
  `∫⁻ bc, f bc ∂((κ ×ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η a) ∂(κ a)`

## Main statements

* `lintegral_prod`: Lebesgue integral of a function against a product of kernels.
* Instances stating that `IsMarkovKernel`, `IsZeroOrMarkovKernel`, `IsFiniteKernel` and
  `IsSFiniteKernel` are stable by product.

## Notation

* `κ ×ₖ η = ProbabilityTheory.Kernel.prod κ η`

-/

@[expose] public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (κ : Kernel α β) (η : Kernel α γ)
  body: (κ ∥ₖ η) ∘ₖ copy α

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ×ₖ " => ProbabilityTheory.Kernel.prod

中文:
定义 乘积
  签名: (κ : 核 α β) (η : 核 α γ)
  定义体: (κ ∥ₖ η) ∘ₖ copy α

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ×ₖ " => ProbabilityTheory.Kernel.prod
-/
noncomputable def prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ) :=
  (κ ∥ₖ η) ∘ₖ copy α

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ×ₖ " => ProbabilityTheory.Kernel.prod

/--
lemma `parallelComp_comp_copy` / 引理 `parallelComp_comp_copy`

English:
lemma parallelComp_comp_copy
  given: (κ : Kernel α β) (η : Kernel α γ)
  proof: rfl

@[simp]

中文:
引理 parallelComp_comp_copy
  条件: (κ : 核 α β) (η : 核 α γ)
  证明: rfl

@[simp]
-/
lemma parallelComp_comp_copy (κ : Kernel α β) (η : Kernel α γ) :
    (κ ∥ₖ η) ∘ₖ copy α = κ ×ₖ η := rfl

@[simp]
/--
lemma `zero_prod` / 引理 `zero_prod`

English:
lemma zero_prod
  given: (η : Kernel α γ)
  statement: (0 : Kernel α β) ×ₖ η = 0
  proof: by simp [prod]

@[simp]

中文:
引理 zero_prod
  条件: (η : 核 α γ)
  结论: (0 : 核 α β) ×ₖ η = 0
  证明: by simp [prod]

@[simp]
-/
lemma zero_prod (η : Kernel α γ) : (0 : Kernel α β) ×ₖ η = 0 := by simp [prod]

@[simp]
/--
lemma `prod_zero` / 引理 `prod_zero`

English:
lemma prod_zero
  given: (κ : Kernel α β)
  statement: κ ×ₖ (0 : Kernel α γ) = 0
  proof: by simp [prod]

@[simp]

中文:
引理 prod_zero
  条件: (κ : 核 α β)
  结论: κ ×ₖ (0 : 核 α γ) = 0
  证明: by simp [prod]

@[simp]
-/
lemma prod_zero (κ : Kernel α β) : κ ×ₖ (0 : Kernel α γ) = 0 := by simp [prod]

@[simp]
/--
lemma `prod_of_not_isSFiniteKernel_left` / 引理 `prod_of_not_isSFiniteKernel_left`

English:
lemma prod_of_not_isSFiniteKernel_left
  given: {κ : Kernel α β} (η : Kernel α γ) (h : ¬ IsSFiniteKernel κ)
  proof: by
  simp [prod, h]

@[simp]

中文:
引理 prod_of_not_isSFiniteKernel_left
  条件: {κ : 核 α β} (η : 核 α γ) (h : ¬ 是SFiniteKernel κ)
  证明: by
  simp [prod, h]

@[simp]
-/
lemma prod_of_not_isSFiniteKernel_left {κ : Kernel α β} (η : Kernel α γ) (h : ¬ IsSFiniteKernel κ) :
    κ ×ₖ η = 0 := by
  simp [prod, h]

@[simp]
/--
lemma `prod_of_not_isSFiniteKernel_right` / 引理 `prod_of_not_isSFiniteKernel_right`

English:
lemma prod_of_not_isSFiniteKernel_right
  statement: (κ : Kernel α β) {η : Kernel α γ}
  proof: by
  simp [prod, h]

中文:
引理 prod_of_not_isSFiniteKernel_right
  结论: (κ : 核 α β) {η : 核 α γ}
  证明: by
  simp [prod, h]
-/
lemma prod_of_not_isSFiniteKernel_right (κ : Kernel α β) {η : Kernel α γ}
    (h : ¬ IsSFiniteKernel η) :
    κ ×ₖ η = 0 := by
  simp [prod, h]

/--
theorem `prod_apply'` / 定理 `prod_apply'`

English:
theorem prod_apply'
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
  proof: by
  simp_rw [prod, comp_apply, copy_apply, Measure.dirac_bind (Kernel.measurable _) (a, a),
    parallelComp_apply, Measure.prod_apply hs]

中文:
定理 prod_apply'
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 α γ) [是SFiniteKernel η]
  证明: by
  simp_rw [prod, comp_apply, copy_apply, Measure.dirac_bind (Kernel.measurable _) (a, a),
    parallelComp_apply, Measure.prod_apply hs]

Depends on / 依赖: Kernel, Kernel.measurable, Measure, Measure.dirac_bind, Measure.prod_apply, comp_apply, copy_apply, dirac_bind, measurable, parallelComp_apply, prod_apply, simp_rw
-/
theorem prod_apply' (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (a : α) {s : Set (β × γ)} (hs : MeasurableSet s) :
    (κ ×ₖ η) a s = ∫⁻ b : β, (η a) (Prod.mk b ⁻¹' s) ∂κ a := by
  simp_rw [prod, comp_apply, copy_apply, Measure.dirac_bind (Kernel.measurable _) (a, a),
    parallelComp_apply, Measure.prod_apply hs]

/--
lemma `prod_apply` / 引理 `prod_apply`

English:
lemma prod_apply
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
  proof: by
  ext s hs
  rw [prod_apply' _ _ _ hs]; rw [Measure.prod_apply hs]

中文:
引理 prod_apply
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 α γ) [是SFiniteKernel η]
  证明: by
  ext s hs
  rw [prod_apply' _ _ _ hs]; rw [Measure.prod_apply hs]

Depends on / 依赖: Measure, Measure.prod_apply, prod_apply
-/
lemma prod_apply (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (a : α) :
    (κ ×ₖ η) a = (κ a).prod (η a) := by
  ext s hs
  rw [prod_apply' _ _ _ hs]; rw [Measure.prod_apply hs]

/--
lemma `prod_apply_prod` / 引理 `prod_apply_prod`

English:
lemma prod_apply_prod
  statement: {κ : Kernel α β} {η : Kernel α γ}
  proof: by
  rw [prod_apply]; rw [Measure.prod_prod]

中文:
引理 prod_apply_prod
  结论: {κ : 核 α β} {η : 核 α γ}
  证明: by
  rw [prod_apply]; rw [Measure.prod_prod]

Depends on / 依赖: Measure, Measure.prod_prod, prod_apply, prod_prod
-/
lemma prod_apply_prod {κ : Kernel α β} {η : Kernel α γ}
    [IsSFiniteKernel κ] [IsSFiniteKernel η] {s : Set β} {t : Set γ} {a : α} :
    (κ ×ₖ η) a (s ×ˢ t) = (κ a s) * (η a t) := by
  rw [prod_apply]; rw [Measure.prod_prod]

/--
lemma `prod_const` / 引理 `prod_const`

English:
lemma prod_const
  given: (μ : Measure β) [SFinite μ] (ν : Measure γ) [SFinite ν]
  proof: by
  ext x
  rw [const_apply]; rw [prod_apply]; rw [const_apply]; rw [const_apply]

中文:
引理 prod_const
  条件: (μ : 测度 β) [SFinite μ] (ν : 测度 γ) [SFinite ν]
  证明: by
  ext x
  rw [const_apply]; rw [prod_apply]; rw [const_apply]; rw [const_apply]

Depends on / 依赖: const_apply, prod_apply
-/
lemma prod_const (μ : Measure β) [SFinite μ] (ν : Measure γ) [SFinite ν] :
    const α μ ×ₖ const α ν = const α (μ.prod ν) := by
  ext x
  rw [const_apply]; rw [prod_apply]; rw [const_apply]; rw [const_apply]

/--
theorem `lintegral_prod` / 定理 `lintegral_prod`

English:
theorem lintegral_prod
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
  proof: by
  simp_rw [prod, lintegral_comp _ _ _ hg, copy_apply]
  rw [lintegral_dirac' _ (by fun_prop)]
  simp_rw [parallelComp_apply, MeasureTheory.lintegral_prod _ hg.aemeasurable]

中文:
定理 lintegral_prod
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 α γ) [是SFiniteKernel η]
  证明: by
  simp_rw [prod, lintegral_comp _ _ _ hg, copy_apply]
  rw [lintegral_dirac' _ (by fun_prop)]
  simp_rw [parallelComp_apply, MeasureTheory.lintegral_prod _ hg.aemeasurable]

Depends on / 依赖: IsNilpotent_substAlgHom, MeasureTheory, MeasureTheory.lintegral_prod, MvPowerSeries, MvPowerSeries.IsNilpotent_substAlgHom, aemeasurable, copy_apply, fun_prop, hb.const, hg.aemeasurable, lintegral_comp, lintegral_dirac, lintegral_prod, parallelComp_apply, simp_rw
-/
theorem lintegral_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (a : α) {g : β × γ -> Real>=0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂(κ ×ₖ η) a = ∫⁻ b, ∫⁻ c, g (b, c) ∂η a ∂κ a := by
  simp_rw [prod, lintegral_comp _ _ _ hg, copy_apply]
  rw [lintegral_dirac' _ (by fun_prop)]
  simp_rw [parallelComp_apply, MeasureTheory.lintegral_prod _ hg.aemeasurable]

/--
theorem `lintegral_prod_symm` / 定理 `lintegral_prod_symm`

English:
theorem lintegral_prod_symm
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ)
  proof: by
  rw [prod_apply]; rw [MeasureTheory.lintegral_prod_symm _ hg.aemeasurable]

中文:
定理 lintegral_prod_symm
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 α γ)
  证明: by
  rw [prod_apply]; rw [MeasureTheory.lintegral_prod_symm _ hg.aemeasurable]

Depends on / 依赖: MeasureTheory, MeasureTheory.lintegral_prod_symm, aemeasurable, hg.aemeasurable, lintegral_prod_symm, prod_apply
-/
theorem lintegral_prod_symm (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ)
    [IsSFiniteKernel η] (a : α) {g : β × γ -> Real>=0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂(κ ×ₖ η) a = ∫⁻ c, ∫⁻ b, g (b, c) ∂κ a ∂η a := by
  rw [prod_apply]; rw [MeasureTheory.lintegral_prod_symm _ hg.aemeasurable]

/--
theorem `lintegral_deterministic_prod` / 定理 `lintegral_deterministic_prod`

English:
theorem lintegral_deterministic_prod
  statement: {f : α -> β} (hf : Measurable f) (κ : Kernel α γ)
  proof: by
  rw [lintegral_prod _ _ _ hg]; rw [lintegral_deterministic' _ hg.lintegral_prod_right']

中文:
定理 lintegral_deterministic_prod
  结论: {f : α -> β} (hf : 可测 f) (κ : 核 α γ)
  证明: by
  rw [lintegral_prod _ _ _ hg]; rw [lintegral_deterministic' _ hg.lintegral_prod_right']

Depends on / 依赖: hg.lintegral_prod_right, lintegral_deterministic, lintegral_prod, lintegral_prod_right
-/
theorem lintegral_deterministic_prod {f : α -> β} (hf : Measurable f) (κ : Kernel α γ)
    [IsSFiniteKernel κ] (a : α) {g : (β × γ) -> Real>=0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂((deterministic f hf) ×ₖ κ) a = ∫⁻ c, g (f a, c) ∂κ a := by
  rw [lintegral_prod _ _ _ hg]; rw [lintegral_deterministic' _ hg.lintegral_prod_right']

/--
theorem `lintegral_prod_deterministic` / 定理 `lintegral_prod_deterministic`

English:
theorem lintegral_prod_deterministic
  statement: {f : α -> γ} (hf : Measurable f) (κ : Kernel α β)
  proof: by
  rw [lintegral_prod_symm _ _ _ hg]; rw [lintegral_deterministic' _ hg.lintegral_prod_left']

中文:
定理 lintegral_prod_deterministic
  结论: {f : α -> γ} (hf : 可测 f) (κ : 核 α β)
  证明: by
  rw [lintegral_prod_symm _ _ _ hg]; rw [lintegral_deterministic' _ hg.lintegral_prod_left']

Depends on / 依赖: hg.lintegral_prod_left, lintegral_deterministic, lintegral_prod_left, lintegral_prod_symm
-/
theorem lintegral_prod_deterministic {f : α -> γ} (hf : Measurable f) (κ : Kernel α β)
    [IsSFiniteKernel κ] (a : α) {g : (β × γ) -> Real>=0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂(κ ×ₖ (deterministic f hf)) a = ∫⁻ b, g (b, f a) ∂κ a := by
  rw [lintegral_prod_symm _ _ _ hg]; rw [lintegral_deterministic' _ hg.lintegral_prod_left']

/--
theorem `lintegral_id_prod` / 定理 `lintegral_id_prod`

English:
theorem lintegral_id_prod
  statement: {f : (α × β) -> Real>=0∞} (hf : Measurable f) (κ : Kernel α β)
  proof: by
  rw [Kernel.id]; rw [lintegral_deterministic_prod _ _ _ hf]; rw [id_eq]

中文:
定理 lintegral_id_prod
  结论: {f : (α × β) -> 实数>=0∞} (hf : 可测 f) (κ : 核 α β)
  证明: by
  rw [Kernel.id]; rw [lintegral_deterministic_prod _ _ _ hf]; rw [id_eq]

Depends on / 依赖: Kernel, Kernel.id, id_eq, lintegral_deterministic_prod
-/
theorem lintegral_id_prod {f : (α × β) -> Real>=0∞} (hf : Measurable f) (κ : Kernel α β)
    [IsSFiniteKernel κ] (a : α) :
    ∫⁻ p, f p ∂(Kernel.id ×ₖ κ) a = ∫⁻ b, f (a, b) ∂κ a := by
  rw [Kernel.id]; rw [lintegral_deterministic_prod _ _ _ hf]; rw [id_eq]

/--
theorem `lintegral_prod_id` / 定理 `lintegral_prod_id`

English:
theorem lintegral_prod_id
  statement: {f : (α × β) -> Real>=0∞} (hf : Measurable f) (κ : Kernel β α)
  proof: by
  rw [Kernel.id]; rw [lintegral_prod_deterministic _ _ _ hf]; rw [id_eq]

中文:
定理 lintegral_prod_id
  结论: {f : (α × β) -> 实数>=0∞} (hf : 可测 f) (κ : 核 β α)
  证明: by
  rw [Kernel.id]; rw [lintegral_prod_deterministic _ _ _ hf]; rw [id_eq]

Depends on / 依赖: Kernel, Kernel.id, id_eq, lintegral_prod_deterministic
-/
theorem lintegral_prod_id {f : (α × β) -> Real>=0∞} (hf : Measurable f) (κ : Kernel β α)
    [IsSFiniteKernel κ] (b : β) :
    ∫⁻ p, f p ∂(κ ×ₖ Kernel.id) b = ∫⁻ a, f (a, b) ∂κ b := by
  rw [Kernel.id]; rw [lintegral_prod_deterministic _ _ _ hf]; rw [id_eq]

/--
theorem `deterministic_prod_apply'` / 定理 `deterministic_prod_apply'`

English:
theorem deterministic_prod_apply'
  statement: {f : α -> β} (mf : Measurable f) (κ : Kernel α γ)
  proof: by
  rw [prod_apply' _ _ _ hs]; rw [lintegral_deterministic']
  exact measurable_measure_prodMk_left hs

中文:
定理 deterministic_prod_apply'
  结论: {f : α -> β} (mf : 可测 f) (κ : 核 α γ)
  证明: by
  rw [prod_apply' _ _ _ hs]; rw [lintegral_deterministic']
  exact measurable_measure_prodMk_left hs

Depends on / 依赖: lintegral_deterministic, measurable_measure_prodMk_left, prod_apply
-/
theorem deterministic_prod_apply' {f : α -> β} (mf : Measurable f) (κ : Kernel α γ)
    [IsSFiniteKernel κ] (a : α) {s : Set (β × γ)} (hs : MeasurableSet s) :
    ((Kernel.deterministic f mf) ×ₖ κ) a s = κ a (Prod.mk (f a) ⁻¹' s) := by
  rw [prod_apply' _ _ _ hs]; rw [lintegral_deterministic']
  exact measurable_measure_prodMk_left hs

/--
theorem `id_prod_apply'` / 定理 `id_prod_apply'`

English:
theorem id_prod_apply'
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (a : α) {s : Set (α × β)}
  proof: by
  rw [Kernel.id]; rw [deterministic_prod_apply' _ _ _ hs]; rw [id_eq]

中文:
定理 id_prod_apply'
  结论: (κ : 核 α β) [是SFiniteKernel κ] (a : α) {s : 集合 (α × β)}
  证明: by
  rw [Kernel.id]; rw [deterministic_prod_apply' _ _ _ hs]; rw [id_eq]

Depends on / 依赖: Kernel, Kernel.id, deterministic_prod_apply, id_eq
-/
theorem id_prod_apply' (κ : Kernel α β) [IsSFiniteKernel κ] (a : α) {s : Set (α × β)}
    (hs : MeasurableSet s) : (Kernel.id ×ₖ κ) a s = κ a (Prod.mk a ⁻¹' s) := by
  rw [Kernel.id]; rw [deterministic_prod_apply' _ _ _ hs]; rw [id_eq]

/--
Instance `IsMarkovKernel.prod` / 实例 `IsMarkovKernel.prod`

English:
instance IsMarkovKernel.prod
  signature: (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel α γ)
  body: by rw [Kernel.prod]; infer_instance

nonrec instance IsZeroOrMarkovKernel.prod (κ : Kernel α β) [h : IsZeroOrMarkovKernel κ]
    (η : Kernel α γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ×ₖ η) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp only [prod]; infer_instance
  rc

中文:
实例 是MarkovKernel.乘积
  签名: (κ : 核 α β) [是MarkovKernel κ] (η : 核 α γ)
  定义体: by rw [Kernel.prod]; infer_instance

nonrec instance IsZeroOrMarkovKernel.prod (κ : Kernel α β) [h : IsZeroOrMarkovKernel κ]
    (η : Kernel α γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ×ₖ η) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp only [prod]; infer_instance
  rc

Depends on / 依赖: Kernel, Kernel.prod, infer_instance
-/
instance IsMarkovKernel.prod (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel α γ)
    [IsMarkovKernel η] : IsMarkovKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance

nonrec instance IsZeroOrMarkovKernel.prod (κ : Kernel α β) [h : IsZeroOrMarkovKernel κ]
    (η : Kernel α γ) [IsZeroOrMarkovKernel η] : IsZeroOrMarkovKernel (κ ×ₖ η) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp only [prod]; infer_instance
  rcases eq_zero_or_isMarkovKernel η with rfl | h'
  · simp only [prod]; infer_instance
  infer_instance

/--
Instance `IsFiniteKernel.prod` / 实例 `IsFiniteKernel.prod`

English:
instance IsFiniteKernel.prod
  signature: (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel α γ)
  body: by rw [Kernel.prod]; infer_instance

中文:
实例 是FiniteKernel.乘积
  签名: (κ : 核 α β) [是FiniteKernel κ] (η : 核 α γ)
  定义体: by rw [Kernel.prod]; infer_instance

Depends on / 依赖: Kernel, Kernel.prod, infer_instance
-/
instance IsFiniteKernel.prod (κ : Kernel α β) [IsFiniteKernel κ] (η : Kernel α γ)
    [IsFiniteKernel η] : IsFiniteKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance

/--
Instance `IsSFiniteKernel.prod` / 实例 `IsSFiniteKernel.prod`

English:
instance IsSFiniteKernel.prod
  signature: (κ : Kernel α β) (η : Kernel α γ)
  body: by rw [Kernel.prod]; infer_instance

中文:
实例 是SFiniteKernel.乘积
  签名: (κ : 核 α β) (η : 核 α γ)
  定义体: by rw [Kernel.prod]; infer_instance

Depends on / 依赖: Kernel, Kernel.prod, infer_instance
-/
instance IsSFiniteKernel.prod (κ : Kernel α β) (η : Kernel α γ) :
    IsSFiniteKernel (κ ×ₖ η) := by rw [Kernel.prod]; infer_instance

/--
lemma `fst_prod` / 引理 `fst_prod`

English:
lemma fst_prod
  given: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsMarkovKernel η]
  proof: by
  rw [prod]; rw [fst_comp]
  ext a : 1
  rw [comp_apply]; rw [copy_apply]; rw [Measure.dirac_bind (by fun_prop)]; rw [fst_apply]; rw [parallelComp_apply]
  simp

中文:
引理 fst_prod
  条件: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 α γ) [是MarkovKernel η]
  证明: by
  rw [prod]; rw [fst_comp]
  ext a : 1
  rw [comp_apply]; rw [copy_apply]; rw [Measure.dirac_bind (by fun_prop)]; rw [fst_apply]; rw [parallelComp_apply]
  simp
-/
@[simp] lemma fst_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsMarkovKernel η] :
    fst (κ ×ₖ η) = κ := by
  rw [prod]; rw [fst_comp]
  ext a : 1
  rw [comp_apply]; rw [copy_apply]; rw [Measure.dirac_bind (by fun_prop)]; rw [fst_apply]; rw [parallelComp_apply]
  simp

/--
lemma `snd_prod` / 引理 `snd_prod`

English:
lemma snd_prod
  given: (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
  proof: by
  ext x; simp [snd_apply, prod_apply]

中文:
引理 snd_prod
  条件: (κ : 核 α β) [是MarkovKernel κ] (η : 核 α γ) [是SFiniteKernel η]
  证明: by
  ext x; simp [snd_apply, prod_apply]
-/
@[simp] lemma snd_prod (κ : Kernel α β) [IsMarkovKernel κ] (η : Kernel α γ) [IsSFiniteKernel η] :
    snd (κ ×ₖ η) = η := by
  ext x; simp [snd_apply, prod_apply]

/--
lemma `comap_prod` / 引理 `comap_prod`

English:
lemma comap_prod
  statement: (κ : Kernel β γ) [IsSFiniteKernel κ] (η : Kernel β δ) [IsSFiniteKernel η]
  proof: by
  ext1 x
  rw [comap_apply]; rw [prod_apply]; rw [prod_apply]; rw [comap_apply]; rw [comap_apply]

中文:
引理 comap_prod
  结论: (κ : 核 β γ) [是SFiniteKernel κ] (η : 核 β δ) [是SFiniteKernel η]
  证明: by
  ext1 x
  rw [comap_apply]; rw [prod_apply]; rw [prod_apply]; rw [comap_apply]; rw [comap_apply]

Depends on / 依赖: comap_apply, prod_apply
-/
lemma comap_prod (κ : Kernel β γ) [IsSFiniteKernel κ] (η : Kernel β δ) [IsSFiniteKernel η]
    {f : α -> β} (hf : Measurable f) :
    (κ ×ₖ η).comap f hf = (κ.comap f hf) ×ₖ (η.comap f hf) := by
  ext1 x
  rw [comap_apply]; rw [prod_apply]; rw [prod_apply]; rw [comap_apply]; rw [comap_apply]

/--
lemma `map_prod_map` / 引理 `map_prod_map`

English:
lemma map_prod_map
  statement: {ε} {mε : MeasurableSpace ε} (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  ext1 x
  rw [map_apply _ (hf.prodMap hg)]; rw [prod_apply κ]; rw [← Measure.map_prod_map _ _ hf hg]; rw [prod_apply]; rw [map_apply _ hf]; rw [map_apply _ hg]

中文:
引理 map_prod_map
  结论: {ε} {mε : 可测空间 ε} (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  ext1 x
  rw [map_apply _ (hf.prodMap hg)]; rw [prod_apply κ]; rw [← Measure.map_prod_map _ _ hf hg]; rw [prod_apply]; rw [map_apply _ hf]; rw [map_apply _ hg]

Depends on / 依赖: Measure, Measure.map_prod_map, hf.prodMap, map_apply, map_prod_map, prodMap, prod_apply
-/
lemma map_prod_map {ε} {mε : MeasurableSpace ε} (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α δ) [IsSFiniteKernel η] {f : β -> γ} (hf : Measurable f) {g : δ -> ε}
    (hg : Measurable g) : (κ.map f) ×ₖ (η.map g) = (κ ×ₖ η).map (Prod.map f g) := by
  ext1 x
  rw [map_apply _ (hf.prodMap hg)]; rw [prod_apply κ]; rw [← Measure.map_prod_map _ _ hf hg]; rw [prod_apply]; rw [map_apply _ hf]; rw [map_apply _ hg]

/--
lemma `map_prod_eq` / 引理 `map_prod_eq`

English:
lemma map_prod_eq
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
  proof: by
  rw [← map_prod_map _ _ hf measurable_id]; rw [map_id]

中文:
引理 map_prod_eq
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 α γ) [是SFiniteKernel η]
  证明: by
  rw [← map_prod_map _ _ hf measurable_id]; rw [map_id]

Depends on / 依赖: map_id, map_prod_map, measurable_id
-/
lemma map_prod_eq (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    {f : β -> δ} (hf : Measurable f) : (κ.map f) ×ₖ η = (κ ×ₖ η).map (Prod.map f id) := by
  rw [← map_prod_map _ _ hf measurable_id]; rw [map_id]

/--
lemma `comap_prod_swap` / 引理 `comap_prod_swap`

English:
lemma comap_prod_swap
  given: (κ : Kernel α β) (η : Kernel γ δ) [IsSFiniteKernel κ] [IsSFiniteKernel η]
  proof: by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_comap]; rw [lintegral_map _ measurable_swap _ hf]; rw [lintegral_prod _ _ _ hf]; rw [lintegral_prod]
  swap; · fun_prop
  simp only [prodMkRight_apply, Prod.fst_swap, Prod.swap_prod_mk, lintegral_prodMkLeft,
    Prod.snd_swap]
  refine (lintegral_

中文:
引理 comap_prod_swap
  条件: (κ : 核 α β) (η : 核 γ δ) [是SFiniteKernel κ] [是SFiniteKernel η]
  证明: by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_comap]; rw [lintegral_map _ measurable_swap _ hf]; rw [lintegral_prod _ _ _ hf]; rw [lintegral_prod]
  swap; · fun_prop
  simp only [prodMkRight_apply, Prod.fst_swap, Prod.swap_prod_mk, lintegral_prodMkLeft,
    Prod.snd_swap]
  refine (lintegral_

Depends on / 依赖: Prod.fst_swap, Prod.snd_swap, Prod.swap_prod_mk, ext_fun_iff, fst_swap, fun_prop, lintegral_comap, lintegral_lintegral_swap, lintegral_map, lintegral_prod, lintegral_prodMkLeft, measurable_swap, prodMkRight_apply, snd_swap, swap_prod_mk
-/
lemma comap_prod_swap (κ : Kernel α β) (η : Kernel γ δ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    comap (prodMkRight α η ×ₖ prodMkLeft γ κ) Prod.swap measurable_swap
      = map (prodMkRight γ κ ×ₖ prodMkLeft α η) Prod.swap := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_comap]; rw [lintegral_map _ measurable_swap _ hf]; rw [lintegral_prod _ _ _ hf]; rw [lintegral_prod]
  swap; · fun_prop
  simp only [prodMkRight_apply, Prod.fst_swap, Prod.swap_prod_mk, lintegral_prodMkLeft,
    Prod.snd_swap]
  refine (lintegral_lintegral_swap ?_).symm
  fun_prop

/--
lemma `map_prod_swap` / 引理 `map_prod_swap`

English:
lemma map_prod_swap
  given: (κ : Kernel α β) (η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η]
  proof: by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_map _ measurable_swap _ hf]; rw [lintegral_prod]; rw [lintegral_prod _ _ _ hf]
  swap; · fun_prop
  refine (lintegral_lintegral_swap ?_).symm
  fun_prop

中文:
引理 map_prod_swap
  条件: (κ : 核 α β) (η : 核 α γ) [是SFiniteKernel κ] [是SFiniteKernel η]
  证明: by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_map _ measurable_swap _ hf]; rw [lintegral_prod]; rw [lintegral_prod _ _ _ hf]
  swap; · fun_prop
  refine (lintegral_lintegral_swap ?_).symm
  fun_prop

Depends on / 依赖: ext_fun_iff, fun_prop, lintegral_lintegral_swap, lintegral_map, lintegral_prod, measurable_swap
-/
lemma map_prod_swap (κ : Kernel α β) (η : Kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    map (κ ×ₖ η) Prod.swap = η ×ₖ κ := by
  rw [ext_fun_iff]
  intro x f hf
  rw [lintegral_map _ measurable_swap _ hf]; rw [lintegral_prod]; rw [lintegral_prod _ _ _ hf]
  swap; · fun_prop
  refine (lintegral_lintegral_swap ?_).symm
  fun_prop

/--
lemma `prodComm_prod` / 引理 `prodComm_prod`

English:
lemma prodComm_prod
  given: {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel α γ} [IsSFiniteKernel η]
  proof: map_prod_swap κ η

@[simp]

中文:
引理 prodComm_prod
  条件: {κ : 核 α β} [是SFiniteKernel κ] {η : 核 α γ} [是SFiniteKernel η]
  证明: map_prod_swap κ η

@[simp]

Depends on / 依赖: map_prod_swap
-/
lemma prodComm_prod {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel α γ} [IsSFiniteKernel η] :
    (κ ×ₖ η).map MeasurableEquiv.prodComm = η ×ₖ κ :=
  map_prod_swap κ η

@[simp]
/--
lemma `swap_prod` / 引理 `swap_prod`

English:
lemma swap_prod
  given: {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel α γ} [IsSFiniteKernel η]
  proof: by
  rw [swap_comp_eq_map]; rw [map_prod_swap]

中文:
引理 swap_prod
  条件: {κ : 核 α β} [是SFiniteKernel κ] {η : 核 α γ} [是SFiniteKernel η]
  证明: by
  rw [swap_comp_eq_map]; rw [map_prod_swap]

Depends on / 依赖: map_prod_swap, swap_comp_eq_map
-/
lemma swap_prod {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel α γ} [IsSFiniteKernel η] :
    (swap β γ) ∘ₖ (κ ×ₖ η) = (η ×ₖ κ) := by
  rw [swap_comp_eq_map]; rw [map_prod_swap]

/--
lemma `deterministic_prod_deterministic` / 引理 `deterministic_prod_deterministic`

English:
lemma deterministic_prod_deterministic
  statement: {f : α -> β} {g : α -> γ}
  proof: by
  ext; simp_rw [prod_apply, deterministic_apply, Measure.dirac_prod_dirac]

中文:
引理 deterministic_prod_deterministic
  结论: {f : α -> β} {g : α -> γ}
  证明: by
  ext; simp_rw [prod_apply, deterministic_apply, Measure.dirac_prod_dirac]

Depends on / 依赖: Measure, Measure.dirac_prod_dirac, deterministic_apply, dirac_prod_dirac, prod_apply, simp_rw
-/
lemma deterministic_prod_deterministic {f : α -> β} {g : α -> γ}
    (hf : Measurable f) (hg : Measurable g) :
    deterministic f hf ×ₖ deterministic g hg
      = deterministic (fun a => (f a, g a)) (hf.prodMk hg) := by
  ext; simp_rw [prod_apply, deterministic_apply, Measure.dirac_prod_dirac]

/--
lemma `id_prod_eq` / 引理 `id_prod_eq`

English:
lemma id_prod_eq
  statement: @Kernel.id (α × β) inferInstance =
  proof: by
  rw [deterministic_prod_deterministic]
  rfl

中文:
引理 id_prod_eq
  结论: @核.id (α × β) inferInstance =
  证明: by
  rw [deterministic_prod_deterministic]
  rfl

Depends on / 依赖: deterministic_prod_deterministic
-/
lemma id_prod_eq : @Kernel.id (α × β) inferInstance =
    (deterministic Prod.fst measurable_fst) ×ₖ (deterministic Prod.snd measurable_snd) := by
  rw [deterministic_prod_deterministic]
  rfl

/--
lemma `prodAssoc_prod` / 引理 `prodAssoc_prod`

English:
lemma prodAssoc_prod
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
  proof: by
  ext1 a
  rw [map_apply _ (by fun_prop)]; rw [prod_apply]; rw [prod_apply]; rw [Measure.prodAssoc_prod]; rw [prod_apply]; rw [prod_apply]

中文:
引理 prodAssoc_prod
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 α γ) [是SFiniteKernel η]
  证明: by
  ext1 a
  rw [map_apply _ (by fun_prop)]; rw [prod_apply]; rw [prod_apply]; rw [Measure.prodAssoc_prod]; rw [prod_apply]; rw [prod_apply]

Depends on / 依赖: Measure, Measure.prodAssoc_prod, fun_prop, map_apply, prodAssoc_prod, prod_apply
-/
lemma prodAssoc_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (ξ : Kernel α δ) [IsSFiniteKernel ξ] :
    ((κ ×ₖ ξ) ×ₖ η).map MeasurableEquiv.prodAssoc = κ ×ₖ (ξ ×ₖ η) := by
  ext1 a
  rw [map_apply _ (by fun_prop)]; rw [prod_apply]; rw [prod_apply]; rw [Measure.prodAssoc_prod]; rw [prod_apply]; rw [prod_apply]

/--
lemma `prodAssoc_symm_prod` / 引理 `prodAssoc_symm_prod`

English:
lemma prodAssoc_symm_prod
  statement: (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
  proof: by
  rw [← prodAssoc_prod]; rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
  simp

中文:
引理 prodAssoc_symm_prod
  结论: (κ : 核 α β) [是SFiniteKernel κ] (η : 核 α γ) [是SFiniteKernel η]
  证明: by
  rw [← prodAssoc_prod]; rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
  simp

Depends on / 依赖: Kernel, Kernel.map_comp_right, fun_prop, map_comp_right, prodAssoc_prod
-/
lemma prodAssoc_symm_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ) [IsSFiniteKernel η]
    (ξ : Kernel α δ) [IsSFiniteKernel ξ] :
    (κ ×ₖ (ξ ×ₖ η)).map MeasurableEquiv.prodAssoc.symm = (κ ×ₖ ξ) ×ₖ η := by
  rw [← prodAssoc_prod]; rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
  simp

/--
lemma `prod_const_comp` / 引理 `prod_const_comp`

English:
lemma prod_const_comp
  statement: {δ} {mδ : MeasurableSpace δ} (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply' _ _ _ ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_left ms)]

中文:
引理 prod_const_comp
  结论: {δ} {mδ : 可测空间 δ} (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply' _ _ _ ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_left ms)]

Depends on / 依赖: comp_apply, const_apply, lintegral_comp, measurable_measure_prodMk_left, prod_apply, simp_rw
-/
lemma prod_const_comp {δ} {mδ : MeasurableSpace δ} (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel β γ) [IsSFiniteKernel η] (μ : Measure δ) [SFinite μ] :
    (η ×ₖ (const β μ)) ∘ₖ κ = (η ∘ₖ κ) ×ₖ (const α μ) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply' _ _ _ ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_left ms)]

/--
lemma `const_prod_comp` / 引理 `const_prod_comp`

English:
lemma const_prod_comp
  statement: {δ} {mδ : MeasurableSpace δ} (κ : Kernel α β) [IsSFiniteKernel κ]
  proof: by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply, Measure.prod_apply_symm ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_right ms)]

中文:
引理 const_prod_comp
  结论: {δ} {mδ : 可测空间 δ} (κ : 核 α β) [是SFiniteKernel κ]
  证明: by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply, Measure.prod_apply_symm ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_right ms)]

Depends on / 依赖: Measure, Measure.prod_apply_symm, comp_apply, const_apply, lintegral_comp, measurable_measure_prodMk_right, prod_apply, prod_apply_symm, simp_rw
-/
lemma const_prod_comp {δ} {mδ : MeasurableSpace δ} (κ : Kernel α β) [IsSFiniteKernel κ]
    (μ : Measure γ) [SFinite μ] (η : Kernel β δ) [IsSFiniteKernel η] :
    ((const β μ) ×ₖ η) ∘ₖ κ = (const α μ) ×ₖ (η ∘ₖ κ) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, prod_apply, Measure.prod_apply_symm ms, const_apply,
  lintegral_comp _ _ _ (measurable_measure_prodMk_right ms)]

end Kernel
end ProbabilityTheory
